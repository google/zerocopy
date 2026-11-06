-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean
import Lean.Replay

/-!
# Diagnostic Probe: Total Recursion vs. `partial def` in `.olean` `ModuleData`

Compares the `ConstantInfo` entries emitted into `ModuleData.constants` and
`env.checked` in Lean `v4.34.1` for seven declaration patterns:

1. A structurally recursive total `def` (`totalStruct`).
2. A well-founded recursive total `def` (`totalWF`).
3. A mutual well-founded recursive total `def` (`mutualEven` / `mutualOdd`).
4. A private structurally recursive total `def` (`privRec`).
5. A nested `where` structurally recursive total `def` (`withWhere.loop`).
6. A user-written `partial def` (`userPartial`).
7. A user-written `opaque` (`userOpaque`).

Both total computable recursive definitions (1–5) and user-written `partial def`
declarations (6) invoke `Lean.Elab.PreDefinition.addAndCompilePartialRec` and
therefore emit a `<base>._unsafe_rec` companion with `ci.isPartial == true`
(`DefinitionSafety.partial`). However, their `<base>` constants in
`env.checked` are disjoint: total recursive definitions elaborate `<base>` as
`.defnInfo` with `safety == .safe`, whereas `partial def` elaborates `<base>`
as `.opaqueInfo` (`isUnsafe == false`).
-/

/-- Structurally recursive total definition. -/
def totalStruct : Nat → Nat
  | 0 => 0
  | n + 1 => totalStruct n + 1

/-- Well-founded recursive total definition. -/
def totalWF (n : Nat) : Nat :=
  if h : n == 0 then 0 else totalWF (n / 2) + 1
termination_by n
decreasing_by
  have hne : n ≠ 0 := by
    intro heq
    subst heq
    contradiction
  omega

mutual
/-- Mutually recursive well-founded total definition (even branch). -/
def mutualEven (n : Nat) : Bool :=
  if h : n == 0 then true else mutualOdd (n - 1)
termination_by n
decreasing_by
  have hne : n ≠ 0 := by intro heq; subst heq; contradiction
  omega

/-- Mutually recursive well-founded total definition (odd branch). -/
def mutualOdd (n : Nat) : Bool :=
  if h : n == 0 then false else mutualEven (n - 1)
termination_by n
decreasing_by
  have hne : n ≠ 0 := by intro heq; subst heq; contradiction
  omega
end

/-- User-written partial definition (`<base>` is `.opaqueInfo`). -/
partial def userPartial (n : Nat) : Nat :=
  if n == 0 then 0 else userPartial (n - 1) + 1

/-- Private structurally recursive total definition. -/
private def privRec : Nat → Nat
  | 0 => 0
  | n + 1 => privRec n + 1

/-- Definition with a nested structurally recursive `where` helper. -/
def withWhere (n : Nat) : Nat :=
  loop n
where
  loop : Nat → Nat
    | 0 => 0
    | k + 1 => loop k + 1

/-- User-written opaque constant (`<base>` is `.opaqueInfo`, with no
    `._unsafe_rec` companion). -/
opaque userOpaque : Nat := 42

/-- Mirror of the private `ConstantInfo.isCEnv` predicate in
    `src/lean/Lean/Replay.lean:161-162`. -/
def Lean.ConstantInfo.isCEnv (ci : Lean.ConstantInfo) : Bool :=
  !ci.isUnsafe && !ci.isPartial

open Lean in
/-- Format the `ConstantInfo` constructor and safety metadata of `ci`. -/
def kindOf : ConstantInfo → String
  | .axiomInfo _  => "axiomInfo"
  | .defnInfo v   => s!"defnInfo(safety={repr v.safety})"
  | .thmInfo _    => "thmInfo"
  | .opaqueInfo v => s!"opaqueInfo(isUnsafe={v.isUnsafe})"
  | .quotInfo _   => "quotInfo"
  | .inductInfo _ => "inductInfo"
  | .ctorInfo _   => "ctorInfo"
  | .recInfo _    => "recInfo"

open Lean in
#eval show MetaM Unit from do
  let env ← getEnv
  let mut entries : Array (Name × ConstantInfo) := #[]
  for (c, ci) in env.checked.get.constants.map₂.toList do
    if c != `kindOf && c != `Lean.ConstantInfo.isCEnv && !(`kindOf).isPrefixOf c then
      entries := entries.push (c, ci)
  entries := entries.qsort (fun a b => a.1.toString < b.1.toString)
  IO.println "=== ALL STAGE-2 CONSTANTS IN env.checked ==="
  for (c, ci) in entries do
    let unsafeRecBase := Compiler.isUnsafeRecName? c
    IO.println s!"  {c}:"
    IO.println s!"    kind               = {kindOf ci}"
    IO.println s!"    isUnsafe           = {ci.isUnsafe}"
    IO.println s!"    isPartial          = {ci.isPartial}"
    IO.println s!"    isCEnv             = {ci.isCEnv}"
    IO.println s!"    isUnsafeRecName?   = {repr unsafeRecBase}"
    if let some v := ci.value? true then
      IO.println s!"    usedConstants      = {v.getUsedConstants}"
    if let some base := unsafeRecBase then
      if let some baseCi := env.checked.get.find? base then
        IO.println s!"    base ({base}) kind = {kindOf baseCi}"
  let md ← mkModuleData env
  IO.println s!"\n=== mkModuleData extraConstNames ({md.extraConstNames.size}) ==="
  for n in md.extraConstNames do
    let inConstants := md.constants.any (·.name == n)
    let inChecked := (env.checked.get.find? n).isSome
    IO.println s!"  {n}: inConstants={inConstants}, inChecked={inChecked}"
