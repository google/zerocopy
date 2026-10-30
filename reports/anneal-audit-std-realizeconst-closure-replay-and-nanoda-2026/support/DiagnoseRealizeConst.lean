-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
# Diagnostic Probe: `realizeConst` Duplicate Constants Across `Init` and `Std`

Loads the full `Init` and `Std` module graph in Lean `v4.34.1` at
`level := .private` (`1,138` modules) or `level := .exported` (`1,020` modules)
and inventories every constant name that appears in `ModuleData.constants` of
more than one module.

For each duplicate constant `c`, this probe classifies:

1. Its `ConstantInfo` kind (`thm`, `defn`, `induct`, `ctor`, `rec`, `axiom`,
   `opaque`, or `quot`) and realized theorem suffix (`.eq_def`, `.eq_<n>`,
   `.congr_simp`, `.induct_unfolding`, `.fun_cases_unfolding`, `.congr_eq_<n>`).
2. Whether all occurrences share identical `(type, levelParams, kind, all)` and
   whether `value? (allowOpaque := true)` is identical or differs across
   defining modules.
3. Which module index `env.getModuleIdxFor? c` retains (`const2ModIdx`, which
   uses `insertIfNew` and retains the first module) versus which `ConstantInfo`
   `env.checked.get.find? c` retains (`privateConstantMap`, which overwrites the
   stored entry with the last module whenever `subsumesInfo` holds).
4. For every duplicate with differing `value? true`, the exact set of private
   helper constants (`_private.<Module>.0.<helper>`) that account for the proof
   term difference.
-/

open Lean

/-- Return a short label for a `ConstantInfo` variant. -/
def kindStr (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "defn"
  | .thmInfo _    => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

/-- Classify a constant name by its realized theorem suffix. -/
def suffixCategory (n : Name) : String :=
  match n with
  | .str _ s =>
    if s == "eq_def" then ".eq_def"
    else if s == "eq_unfold" then ".eq_unfold"
    else if s.startsWith "eq_" then ".eq_<n>"
    else if s == "congr_simp" then ".congr_simp"
    else if s == "induct" then ".induct"
    else if s == "fun_cases" then ".fun_cases"
    else if s == "elim" then ".elim"
    else if s.startsWith "_eq_" then "._eq_<n>"
    else if s == "_sunfold" then "._sunfold"
    else if s.startsWith "_cstage" then "._cstage*"
    else s!"other(.str:{s})"
  | _ => "other(non-str)"

/-- Entry point for the `Init` + `Std` duplicate-constant inventory. -/
def main : IO Unit := do
  let sysroot ← findSysroot
  initSearchPath sysroot

  let env ← unsafe importModules
    #[{ module := `Std, importAll := true }]
    {} (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let env := env.setExporting false

  let numMods := env.header.modules.size
  IO.println s!"=== 1. Loaded `Init` + `Std` Environment ==="
  IO.println s!"Total modules loaded: {numMods}"

  -- Collect all occurrences of each constant across every module's
  -- `data.constants` array.
  let mut allOccurrences : Std.HashMap Name (Array (Name × ConstantInfo)) := {}
  let mut totalDataConstants := 0
  for m in env.header.modules, data in env.header.moduleData do
    totalDataConstants := totalDataConstants + data.constants.size
    for ci in data.constants do
      let prev := allOccurrences.getD ci.name #[]
      allOccurrences := allOccurrences.insert ci.name (prev.push (m.module, ci))

  IO.println s!"Total entries across all `data.constants`: {totalDataConstants}"
  IO.println s!"Unique constant names across `data.constants`: {allOccurrences.size}"
  let checkedCount :=
    env.checked.get.constants.fold (init := 0) (fun acc _ _ => acc + 1)
  IO.println s!"Total constants in `env.checked.get.constants`: {checkedCount}"

  let mut dupNames : Array Name := #[]
  for (c, occs) in allOccurrences do
    if occs.size > 1 then
      dupNames := dupNames.push c
  dupNames := dupNames.qsort (fun a b => a.toString < b.toString)

  IO.println s!"Duplicate constant names (`allOccurrences[c].size > 1`): {dupNames.size}"

  let mut identicalTypeAndVal : Array Name := #[]
  let mut identicalTypeDiffVal : Array Name := #[]
  let mut diffTypeOrMeta : Array Name := #[]
  let mut byKind : Std.HashMap String Nat := {}
  let mut bySuffix : Std.HashMap String Nat := {}

  for c in dupNames do
    let occs := allOccurrences[c]!
    let (_, ci0) := occs[0]!
    let kStr := kindStr ci0
    byKind := byKind.insert kStr (byKind.getD kStr 0 + 1)
    let sCat := suffixCategory c
    bySuffix := bySuffix.insert sCat (bySuffix.getD sCat 0 + 1)

    let mut sameTypeAndMeta := true
    let mut sameVal := true
    for i in [1:occs.size] do
      let (_, cii) := occs[i]!
      if cii.type != ci0.type || cii.levelParams != ci0.levelParams ||
          kindStr cii != kStr || cii.all != ci0.all then
        sameTypeAndMeta := false
      if cii.value? true != ci0.value? true then
        sameVal := false
    if !sameTypeAndMeta then
      diffTypeOrMeta := diffTypeOrMeta.push c
    else if sameVal then
      identicalTypeAndVal := identicalTypeAndVal.push c
    else
      identicalTypeDiffVal := identicalTypeDiffVal.push c

  IO.println s!"\n=== 2. Classification of Duplicate Constants ({dupNames.size} total) ==="
  IO.println s!"- Identical `type`, `levelParams`, `kind`, `all`, AND `value? true`: {identicalTypeAndVal.size}"
  IO.println s!"- Identical `type`, `levelParams`, `kind`, `all`, but DIFFERING `value? true`: {identicalTypeDiffVal.size}"
  IO.println s!"- Differing `type`, `levelParams`, `kind`, or `all`: {diffTypeOrMeta.size}"

  IO.println s!"\nBreakdown by ConstantInfo kind:"
  for (k, cnt) in byKind.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"  {k}: {cnt}"

  IO.println s!"\nBreakdown by realized constant suffix:"
  for (s, cnt) in bySuffix.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"  {s}: {cnt}"

  -- Compare the module retained in `const2ModIdx` (`env.getModuleIdxFor?`)
  -- against the `ConstantInfo` retained in `env.checked`.
  let mut checkedMatchesFirst := 0
  let mut checkedMatchesLast := 0
  let mut checkedMatchesOther := 0
  let mut originMatchesFirst := 0
  for c in dupNames do
    let occs := allOccurrences[c]!
    let some stored := env.checked.get.find? c
      | throw <| IO.userError s!"missing {c}"
    let (firstMod, firstCi) := occs[0]!
    let (_, lastCi) := occs.back!
    let some origIdx := env.getModuleIdxFor? c
      | throw <| IO.userError s!"missing idx {c}"
    let origMod := env.header.modules[origIdx]!.module
    if origMod == firstMod then
      originMatchesFirst := originMatchesFirst + 1
    if stored.value? true == lastCi.value? true &&
        stored.value? true != firstCi.value? true then
      checkedMatchesLast := checkedMatchesLast + 1
    else if stored.value? true == firstCi.value? true &&
        stored.value? true != lastCi.value? true then
      checkedMatchesFirst := checkedMatchesFirst + 1
    else
      checkedMatchesOther := checkedMatchesOther + 1

  IO.println s!"\n=== 3. `env.checked` & `const2ModIdx` Retention Behavior ==="
  IO.println s!"- `env.getModuleIdxFor? c` equals FIRST module in `env.header.modules`: {originMatchesFirst} / {dupNames.size}"
  IO.println s!"- Among differing-value duplicates ({identicalTypeDiffVal.size}):"
  IO.println s!"  `env.checked` stores LAST module's `ConstantInfo`: {checkedMatchesLast}"
  IO.println s!"  `env.checked` stores FIRST module's `ConstantInfo`: {checkedMatchesFirst}"

  IO.println s!"\n=== 4. Complete List of Duplicate Constants with Differing `value? true` ({identicalTypeDiffVal.size}) ==="
  for idx in [:identicalTypeDiffVal.size] do
    let c := identicalTypeDiffVal[idx]!
    let occs := allOccurrences[c]!
    let mods := occs.map (·.1)
    let (_, ci0) := occs[0]!
    let (_, ciLast) := occs.back!
    let v0 := ci0.value? true |>.get!
    let vLast := ciLast.value? true |>.get!
    let consts0 := v0.getUsedConstants
    let constsLast := vLast.getUsedConstants
    let priv0 := consts0.filter isPrivateName
    let privLast := constsLast.filter isPrivateName
    let onlyIn0 := consts0.filter (!constsLast.contains ·)
    let onlyInLast := constsLast.filter (!consts0.contains ·)
    IO.println s!"  [{idx + 1}] {c} (kind={kindStr ci0}, occurrences={occs.size}, modules={mods.toList})"
    IO.println s!"      onlyInFirstUsedConsts={onlyIn0.toList}"
    IO.println s!"      onlyInLastUsedConsts={onlyInLast.toList}"
    IO.println s!"      privInFirst={priv0.toList}, privInLast={privLast.toList}"
    if onlyIn0.isEmpty && onlyInLast.isEmpty then
      IO.println s!"      (Same used constants; v0.depth={v0.approxDepth}, vLast.depth={vLast.approxDepth})"
      IO.println s!"      v0    = {v0}"
      IO.println s!"      vLast = {vLast}"

  IO.println s!"\n=== 5. Complete List of Duplicate Constants with Identical `value? true` ({identicalTypeAndVal.size}) ==="
  for idx in [:identicalTypeAndVal.size] do
    let c := identicalTypeAndVal[idx]!
    let occs := allOccurrences[c]!
    let mods := occs.map (·.1)
    let (_, ci0) := occs[0]!
    IO.println s!"  [{idx + 1}] {c} (kind={kindStr ci0}, occurrences={occs.size}, modules={mods.toList})"

  -- Also check `data.extraConstNames` duplicates across modules.
  let mut extraOccs : Std.HashMap Name (Array Name) := {}
  for m in env.header.modules, data in env.header.moduleData do
    for n in data.extraConstNames do
      let prev := extraOccs.getD n #[]
      extraOccs := extraOccs.insert n (prev.push m.module)
  let mut dupExtras : Array (Name × Array Name) := #[]
  for (n, ms) in extraOccs do
    if ms.size > 1 then
      dupExtras := dupExtras.push (n, ms)
  dupExtras := dupExtras.qsort (fun a b => a.1.toString < b.1.toString)
  IO.println s!"\n=== 6. Duplicate `data.extraConstNames` Across Modules ({dupExtras.size}) ==="
  for (n, ms) in dupExtras do
    IO.println s!"  {n}: {ms.toList}"
