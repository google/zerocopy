-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

/-!
# Runnable Probe: Two-Stage Boundary Audit (`preaudit` + `theory-lock.json` + `runtime-audit`)

This probe prototypes and validates the two-stage boundary audit split on
Lean `v4.34.1`:
1. **Stage 1 (`preaudit`, compile-time / CI):**
   - Verifies `Trusted.*` and `Anneal.*` sources and `.olean`s on top of
     `foundation-lock.json`.
   - Enforces two-color `@[vetted]` / `@[candidate <feat>]` non-contamination
     in `Trusted.*`.
   - Replays all `Trusted.*` and `Anneal.*` kernel constants from scratch in
     `foundation.toKernelEnv.replay`.
   - Precomputes for every constant `c` in `Trusted.*` and `Anneal.*`:
     * `axioms`: transitive foundation axioms reachable from `c`;
     * `directFeats`: candidate features unconditionally activated by reaching
       `c`;
     * `guardedFeats`: for each valid candidate feature `f`, the set of
       additional candidate features unlocked inside `@[vetted]` definitions
       reachable from `c` when `f` becomes active.
   - Emits a deterministic `theory-lock.json` with SHA-256 digests of all
     `Trusted.*` and `Anneal.*` `.lean` and `.olean` files alongside the
     per-constant summaries.
2. **Stage 2 (`runtime-audit`, `cargo anneal verify`):**
   - Verifies `foundation-lock.json` and `theory-lock.json` SHA-256 digests.
   - Parses **only** `Mir.lean` and `Proof.lean` during preflight.
   - Treats `baseModules := foundation ++ trusted ++ theory` as the pre-audited
     Stage-1 base (`base.toKernelEnv`, Stage-1 `map₁`).
   - Collects `crateLocals` from `#[Mir, Proof]`, including cross-stage
     `realizeConst` theorems (such as `Anneal.evalHelper.eq_1` realized when
     `Proof.lean` calls `simp [Anneal.evalHelper]` on a definition from
     `Anneal` in `base`).
   - Computes `(axioms, activeCandidateFeatures)` in $O(|crateLocals|)$ using
     `theory-lock.json` summaries and verifies bit-for-bit equality with the
     baseline single-stage full-graph traversal.
   - Replays **only** `crateLocals` in `base.toKernelEnv.replay crateLocals`.
-/

open Lean

namespace ProbeTwoStagePreAudit

def fail (msg : String) : IO α := throw <| IO.userError msg

def validCandidateFeatures : List String :=
  ["refinement", "step_result", "memory", "mir_ast", "mir_semantics", "rustc_capture"]

structure ConstantSummary where
  name : String
  originModule : String
  kind : String
  trustStatus : String
  axioms : Array String
  directFeats : Array String
  /-- Pairs `(guardFeat, unlockedFeats)` for monotonic fixed-point propagation
      across `@[vetted]` `Trusted.candidate` guards. -/
  guardedFeats : Array (String × Array String)
  deriving ToJson, FromJson, Repr

structure ModuleLockEntry where
  name : String
  role : String
  leanSha256 : String
  oleanSha256 : String
  deriving ToJson, FromJson, Repr

structure TheoryLock where
  schemaVersion : Nat := 1
  foundationLockSha256 : String
  modules : Array ModuleLockEntry
  trustDeclarations : Array (String × String)
  constants : Array ConstantSummary
  replayedDeclarationCount : Nat
  deriving ToJson, FromJson, Repr

structure AuditOutput where
  mode : String
  replayedCount : Nat
  visitedCount : Nat
  axioms : Array String
  activeCandidateFeatures : Array String
  crossStageRealizedConsts : Array String
  replayMs : Nat
  totalAuditMs : Nat
  deriving ToJson, FromJson, Repr

partial def exprEdges (splitCandidateGuards : Bool) (e : Expr)
    (allowLooseBVarsInSubexpr : Bool := false) :
    IO (NameSet × Array (String × Expr)) := do
  if e.hasFVar || e.hasMVar || (!allowLooseBVarsInSubexpr && e.hasLooseBVars) then
    fail "open expression in stored declaration"
  let mut result : NameSet := {}
  let mut guarded : Array (String × Expr) := #[]
  let mut pending := [e]
  let mut seen : Std.HashSet Expr := {}
  while !pending.isEmpty do
    let x := pending.head!
    pending := pending.tail!
    if !seen.contains x then
      seen := seen.insert x
      if splitCandidateGuards && x.getAppFn.isConstOf `Trusted.candidate then
        let args := x.getAppArgs
        if args.size < 3 then
          fail "partially applied Trusted.candidate is unsupported"
        let .lit (.strVal feat) := args[0]!
          | fail "Trusted.candidate feature argument must be a string literal"
        unless validCandidateFeatures.contains feat do
          fail s!"unknown candidate feature {feat} in Trusted.candidate"
        result := result.insert `Trusted.candidate
        result := result.insert `String
        pending := args[1]! :: (args.extract 3 args.size).toList ++ pending
        guarded := guarded.push (feat, args[2]!)
      else
        match x with
        | .const n _ => result := result.insert n
        | .lit (.natVal _) => result := result.insert `Nat
        | .lit (.strVal _) => result := result.insert `String
        | .app a b => pending := a :: b :: pending
        | .forallE _ a b _ | .lam _ a b _ => pending := a :: b :: pending
        | .letE _ t v b _ => pending := t :: v :: b :: pending
        | .proj s _ b =>
          result := result.insert s
          pending := b :: pending
        | .mdata _ b => pending := b :: pending
        | _ => pure ()
  return (result, guarded)

def expressionEdges (e : Expr) (allowLooseBVarsInSubexpr : Bool := false) : IO NameSet := do
  return (← exprEdges false e allowLooseBVarsInSubexpr).1

def declarationEdges (ci : ConstantInfo) : IO NameSet := do
  let mut result ← expressionEdges ci.type
  if let some value := ci.value? (allowOpaque := true) then
    result := result ++ (← expressionEdges value)
  match ci with
  | .defnInfo v => result := result ++ .ofList v.all
  | .thmInfo v => result := result ++ .ofList v.all
  | .opaqueInfo v => result := result ++ .ofList v.all
  | .inductInfo v => result := result ++ .ofList (v.all ++ v.ctors)
  | .ctorInfo v => result := result.insert v.induct
  | .recInfo v =>
    result := result ++ .ofList v.all
    for rule in v.rules do
      result := (result.insert rule.ctor) ++ (← expressionEdges rule.rhs)
  | _ => pure ()
  return result

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom" | .defnInfo _ => "definition" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quotient" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]? | fail s!"invalid module index: {n}"
  return mod.module

def sameRealizedThmHeader (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo ta, .thmInfo tb =>
    ta.name == tb.name &&
    ta.type == tb.type &&
    ta.levelParams == tb.levelParams &&
    ta.all == tb.all
  | .thmInfo ta, .axiomInfo ab =>
    ta.name == ab.name &&
    ta.type == ab.type &&
    ta.levelParams == ab.levelParams &&
    ta.all == [ab.name] &&
    !ab.isUnsafe
  | .axiomInfo aa, .thmInfo tb =>
    aa.name == tb.name &&
    aa.type == tb.type &&
    aa.levelParams == tb.levelParams &&
    tb.all == [aa.name] &&
    !aa.isUnsafe
  | _, _ => false

partial def realizedRootPrefix? (n : Name) : Option Name :=
  match n with
  | .str p s =>
    if s == "eq_def" || s == "eq_unfold" || s == "congr_simp" ||
       s == "induct_unfolding" || s.startsWith "eq_" ||
       s.startsWith "proof_" || s.startsWith "match_" ||
       s.startsWith "_eq_" || s.startsWith "_proof_" || s.startsWith "_sunfold" then
      some ( extractRoot p )
    else if s == "splitter" || s == "elim" || s == "casesOn" || s == "recOn" || s == "brecOn" || s == "below" || s == "ibelow" then
      some ( extractRoot p )
    else
      none
  | _ => none
where
  extractRoot (p : Name) : Name :=
    let up := (privateToUserName? p).getD p
    match up with
    | .str q s =>
      if s.startsWith "match_" || s.startsWith "proof_" || s.startsWith "eq_" then
        extractRoot q
      else
        up
    | _ => up

def classifyTrustedConstant (declMap : Std.HashMap Name String)
    (cName : Name) : IO (String × Name) := do
  let userName := (privateToUserName? cName).getD cName
  let mut cur := userName
  while !cur.isAnonymous do
    if let some status := declMap.get? cur then
      return (status, cur)
    cur := cur.getPrefix
  fail s!"unclassified Trusted constant {cName}"

/-- Full single-stage candidate feature collector (from `TrustedBoundary.lean`),
    enhanced with `initialActiveFeats` so we can also query what features a
    constant `c` unlocks when a given guard feature `f` is already active. -/
def collectActiveCandidateFeaturesWithInit
    (lookup : Name → IO ConstantInfo)
    (provenance : Name → IO Name)
    (trusted : Array Name)
    (statusMap : Std.HashMap Name String)
    (ownerMap : Std.HashMap Name Name)
    (roots : Array Name)
    (initialActiveFeats : Array String := #[]) : IO (Array String) := do
  let trustedSet : NameSet := .ofList trusted.toList
  let mut pending := roots.toList
  let mut visited : NameSet := {}
  let mut activeFeats : Std.HashSet String := .ofArray initialActiveFeats
  let mut deferred : Std.HashMap String (Array Expr) := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      let orig ← provenance n
      let ci ← lookup n
      if trustedSet.contains orig then
        let status := statusMap.getD n "vetted"
        if status.startsWith "candidate:" then
          let feat := (status.drop 10).toString
          if !activeFeats.contains feat then
            activeFeats := activeFeats.insert feat
            if let some bodies := deferred.get? feat then
              deferred := deferred.erase feat
              for b in bodies do
                pending := (← expressionEdges b true).toList ++ pending
          pending := (← declarationEdges ci).toList ++ pending
        else
          let userName := (privateToUserName? n).getD n
          let owner := ownerMap.getD n userName
          let isTopLevelDef :=
            userName == owner &&
            (match ci with
             | .inductInfo _ | .recInfo _ | .ctorInfo _ => false
             | _ => true)
          if isTopLevelDef then
            pending := (← expressionEdges ci.type).toList ++ pending
            if let some val := ci.value? (allowOpaque := true) then
              let (unguarded, guarded) ← exprEdges true val
              pending := unguarded.toList ++ pending
              for (feat, body) in guarded do
                if activeFeats.contains feat then
                  pending := (← expressionEdges body true).toList ++ pending
                else
                  let prev := deferred.getD feat #[]
                  deferred := deferred.insert feat (prev.push body)
          else
            for dep in (← declarationEdges ci) do
              if (statusMap.getD dep "vetted") == "vetted" then
                pending := dep :: pending
      else
        pending := (← declarationEdges ci).toList ++ pending
  return activeFeats.toArray.qsort (· < ·)

def closure (lookup : Name → IO ConstantInfo) (provenance : Name → IO Name)
    (axioms : Array (String × String)) (roots : Array Name) : IO (Array Name × Nat) := do
  let mut pending := roots.toList
  let mut visited : NameSet := {}
  let mut reachedAxioms : NameSet := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !visited.contains n then
      visited := visited.insert n
      let m ← provenance n
      let ci ← lookup n
      if ci.isAxiom then
        unless axioms.contains (n.toString, m.toString) do
          fail s!"unapproved axiom {n} from {m}"
        reachedAxioms := reachedAxioms.insert n
      pending := (← declarationEdges ci).toList ++ pending
  return (reachedAxioms.toArray.qsort Name.lt, visited.size)

def collectLocalClosure (locals : Std.HashMap Name ConstantInfo)
    (roots : Array Name) : IO (Std.HashMap Name ConstantInfo) := do
  let mut pending := roots.toList
  let mut result : Std.HashMap Name ConstantInfo := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if !result.contains n then
      if let some ci := locals.get? n then
        result := result.insert n ci
        for dep in (← declarationEdges ci) do
          if !result.contains dep && locals.contains dep then
            pending := dep :: pending
  return result

/-- Verify and collect stage-2 local declarations over `env`, given `baseMods`
    as the Stage-1 base modules. Works identically whether `baseMods` is
    `foundation` (in Stage-1 `preaudit` or single-stage baseline) or
    `foundation ++ trusted ++ theory` (in Stage-2 `runtime-audit`). -/
def verifyAndCollectStageLocals (env : Environment) (baseMods : Array Name)
    (trusted : Array Name) (allowedAll : Array Name) :
    IO (Std.HashMap Name ConstantInfo × Array String) := do
  let loadedMods : NameSet := .ofList (env.header.modules.toList.map (·.module))
  for reqMod in allowedAll do
    unless loadedMods.contains reqMod do fail s!"missing required module {reqMod}"
  let baseSet : NameSet := .ofList baseMods.toList
  let mut locals : Std.HashMap Name ConstantInfo := {}
  let mut partialCompanions : NameSet := {}
  let mut pendingPartials : Array (Name × Name × Bool) := #[]
  let mut crossStageRealized : Array String := #[]
  for m in env.header.modules, data in env.header.moduleData do
    unless data.constNames == data.constants.map ConstantInfo.name do
      fail s!"invalid inventory {m.module}"
    unless allowedAll.contains m.module do fail s!"foreign module {m.module}"
    for ci in data.constants do
      let orig ← origin env ci.name
      let some stored := env.checked.get.find? ci.name
        | fail s!"missing stored declaration {ci.name}"
      let exactValueMatch :=
        stored.type == ci.type && stored.value? true == ci.value? true
      let isRealizedThmDup := sameRealizedThmHeader stored ci
      unless exactValueMatch || isRealizedThmDup do
        fail s!"stored declaration differs from inventory {ci.name}"
      if baseSet.contains m.module then
        unless baseSet.contains orig do
          fail s!"inventory origin mismatch {ci.name}"
      else
        let isTrusted := trusted.contains m.module
        if ci.isUnsafe then
          fail s!"unsafe/partial declaration {ci.name} in {m.module}"
        if ci.isAxiom then
          fail s!"strict axiom declaration {ci.name} in {m.module}"
        if ci.isPartial then
          partialCompanions := partialCompanions.insert ci.name
          pendingPartials := pendingPartials.push (ci.name, m.module, isTrusted)
        else
          if ci.hasValue true && (ci.value? true).isNone then
            fail s!"missing stored body {ci.name}"
          if let some rootName := realizedRootPrefix? ci.name then
            if let some rootIdx := env.getModuleIdxFor? rootName then
              if let some rootMod := env.header.modules[rootIdx.toNat]? then
                if baseSet.contains rootMod.module && !baseSet.contains orig then
                  crossStageRealized := crossStageRealized.push s!"{ci.name} (in {m.module}, root {rootName} in {rootMod.module})"
          if baseSet.contains orig then
            unless isRealizedThmDup do
              fail s!"inventory origin mismatch {ci.name}"
          else if orig != m.module || locals.contains ci.name then
            unless isRealizedThmDup do
              if locals.contains ci.name then
                fail s!"duplicate declaration {ci.name}"
              else
                fail s!"inventory origin mismatch {ci.name}"
            locals := locals.insert ci.name stored
          else
            locals := locals.insert ci.name stored
  for (cName, modName, _) in pendingPartials do
    let errMsg := s!"unsafe/partial declaration {cName} in {modName}"
    let some baseName := Compiler.isUnsafeRecName? cName | fail errMsg
    let some (.defnInfo baseVal) := locals.get? baseName | fail errMsg
    unless baseVal.safety == .safe && (← origin env baseName) == modName do
      fail errMsg
  for (n, _) in env.checked.get.constants do
    if !baseSet.contains (← origin env n) &&
        !locals.contains n && !partialCompanions.contains n then
      fail s!"uninventoried constant {n}"
  return (locals, crossStageRealized.qsort (· < ·))

/-- Stage 1 (`preaudit`): Audit `Trusted.*` and `Anneal.*` on top of
    `foundation`, replay all `Trusted.*` and `Anneal.*` constants in
    `foundation.toKernelEnv`, and build `TheoryLock`. -/
def runPreAudit (foundation : Array Name) (trusted : Array Name)
    (theory : Array Name) (axioms : Array (String × String))
    (trustDecls : Array (String × String)) : IO (TheoryLock × Nat) := do
  let t0 ← IO.monoMsNow
  let allMods := foundation ++ trusted ++ theory
  let env ← importModules (allMods.map ({ module := · })) Options.empty 0
  let (locals, _) ← verifyAndCollectStageLocals env foundation trusted allMods
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci | none => fail s!"missing dependency declaration {n}"
  let mut declMap : Std.HashMap Name String := {}
  for (n, st) in trustDecls do
    declMap := declMap.insert n.toName st
  let mut statusMap : Std.HashMap Name String := {}
  let mut ownerMap : Std.HashMap Name Name := {}
  for (cName, _) in locals do
    let orig ← origin env cName
    if trusted.contains orig then
      let (st, owner) ← classifyTrustedConstant declMap cName
      statusMap := statusMap.insert cName st
      ownerMap := ownerMap.insert cName owner
  -- Replay all `Trusted.*` and `Anneal.*` constants on `foundation.toKernelEnv`.
  let base ← importModules (foundation.map ({ module := · })) Options.empty 0
  let _ ← base.toKernelEnv.replay locals
  -- Precompute per-constant `(axioms, directFeats, guardedFeats)` summaries
  -- for every constant in `Trusted.*` and `Anneal.*`.
  let sortedNames := locals.toArray.map (·.1) |>.qsort Name.lt
  let mut summaries : Array ConstantSummary := #[]
  for cName in sortedNames do
    let ci := locals.getD cName default
    let orig ← origin env cName
    let st := statusMap.getD cName "theory"
    let (cAxioms, _) ← closure lookup (origin env) axioms #[cName]
    let directFeats ←
      collectActiveCandidateFeaturesWithInit lookup (origin env) trusted statusMap ownerMap #[cName] #[]
    let mut guardedPairs : Array (String × Array String) := #[]
    for gFeat in validCandidateFeatures do
      let withGuard ←
        collectActiveCandidateFeaturesWithInit lookup (origin env) trusted statusMap ownerMap #[cName] #[gFeat]
      let unlocked := withGuard.filter fun f => f != gFeat && !directFeats.contains f
      if !unlocked.isEmpty then
        guardedPairs := guardedPairs.push (gFeat, unlocked)
    summaries := summaries.push {
      name := cName.toString
      originModule := orig.toString
      kind := kind ci
      trustStatus := st
      axioms := cAxioms.map toString
      directFeats := directFeats
      guardedFeats := guardedPairs
    }
  let elapsed := (← IO.monoMsNow) - t0
  let lock : TheoryLock := {
    schemaVersion := 1
    foundationLockSha256 := "probe-foundation-sha256"
    modules := #[]
    trustDeclarations := trustDecls
    constants := summaries
    replayedDeclarationCount := locals.size
  }
  return (lock, elapsed)

/-- Stage 2 (`runtime-audit`): Given pre-verified `TheoryLock`, audit and
    replay ONLY `crateModules` (`#[Mir, Proof]`) on top of
    `baseModules := foundation ++ trusted ++ theory`. -/
def runRuntimeAudit (foundation : Array Name) (trusted : Array Name)
    (theory : Array Name) (axioms : Array (String × String))
    (lock : TheoryLock) (mirMod : Name) (proofMod : Name) : IO AuditOutput := do
  let t0 ← IO.monoMsNow
  let baseMods := foundation ++ trusted ++ theory
  let crateMods := #[mirMod, proofMod]
  let allMods := baseMods ++ crateMods
  let env ← importModules (allMods.map ({ module := · })) Options.empty 0
  let (crateLocals, crossStageRealized) ←
    verifyAndCollectStageLocals env baseMods trusted allMods
  let verifyCrateName := proofMod ++ `verify_crate
  let some _ := env.checked.get.find? verifyCrateName
    | fail s!"missing {verifyCrateName}"
  -- Build O(1) lookup table from `TheoryLock`.
  let mut summaryMap : Std.HashMap Name ConstantSummary := {}
  for s in lock.constants do
    summaryMap := summaryMap.insert s.name.toName s
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci | none => fail s!"missing dependency declaration {n}"
  -- Traverse ONLY `crateLocals` starting from `verifyCrateName`; whenever an
  -- edge hits a constant in `summaryMap` (`Trusted.*` or `Anneal.*`), merge its
  -- pre-verified summary in O(1) without descending into `Trusted`/`Anneal`!
  let mut pending : List Name := [verifyCrateName]
  let mut visitedCrate : NameSet := {}
  let mut reachedTheorySummaries : Array ConstantSummary := #[]
  let mut reachedSummaryNames : NameSet := {}
  let mut reachedAxioms : Std.HashSet String := {}
  let mut activeFeats : Std.HashSet String := {}
  while !pending.isEmpty do
    let n := pending.head!
    pending := pending.tail!
    if let some s := summaryMap.get? n then
      if !reachedSummaryNames.contains n then
        reachedSummaryNames := reachedSummaryNames.insert n
        reachedTheorySummaries := reachedTheorySummaries.push s
        for ax in s.axioms do
          reachedAxioms := reachedAxioms.insert ax
        for df in s.directFeats do
          activeFeats := activeFeats.insert df
    else if !visitedCrate.contains n then
      visitedCrate := visitedCrate.insert n
      let m ← origin env n
      let ci ← lookup n
      if ci.isAxiom then
        unless axioms.contains (n.toString, m.toString) do
          fail s!"unapproved axiom {n} from {m}"
        reachedAxioms := reachedAxioms.insert n.toString
      pending := (← declarationEdges ci).toList ++ pending
  -- Monotonic least fixed point over the 6 candidate features using the
  -- precomputed `guardedFeats` transitions on reached `Trusted`/`Anneal`
  -- constants.
  let mut changed := true
  while changed do
    changed := false
    for s in reachedTheorySummaries do
      for (gFeat, unlocked) in s.guardedFeats do
        if activeFeats.contains gFeat then
          for u in unlocked do
            if !activeFeats.contains u then
              activeFeats := activeFeats.insert u
              changed := true
  -- Replay ONLY the reachable `crateLocals` on `base.toKernelEnv`
  -- (`foundation ++ trusted ++ theory` in Stage-1 `map₁`)!
  let replayLocals ← collectLocalClosure crateLocals #[verifyCrateName]
  let base ← importModules (baseMods.map ({ module := · })) Options.empty 0
  let tReplay0 ← IO.monoMsNow
  let _ ← base.toKernelEnv.replay replayLocals
  let replayMs := (← IO.monoMsNow) - tReplay0
  let totalMs := (← IO.monoMsNow) - t0
  return {
    mode := "runtime-audit"
    replayedCount := replayLocals.size
    visitedCount := visitedCrate.size + reachedSummaryNames.size
    axioms := reachedAxioms.toArray.qsort (· < ·)
    activeCandidateFeatures := activeFeats.toArray.qsort (· < ·)
    crossStageRealizedConsts := crossStageRealized
    replayMs := replayMs
    totalAuditMs := totalMs
  }

/-- Baseline single-stage audit (`single-stage`): Replays and traverses
    `Trusted ++ Anneal ++ Mir ++ Proof` from scratch on `foundation`. -/
def runSingleStageAudit (foundation : Array Name) (trusted : Array Name)
    (theory : Array Name) (axioms : Array (String × String))
    (trustDecls : Array (String × String)) (mirMod : Name) (proofMod : Name) :
    IO AuditOutput := do
  let t0 ← IO.monoMsNow
  let allMods := foundation ++ trusted ++ theory ++ #[mirMod, proofMod]
  let env ← importModules (allMods.map ({ module := · })) Options.empty 0
  let (locals, crossStageRealized) ←
    verifyAndCollectStageLocals env foundation trusted allMods
  let lookup n := match env.checked.get.find? n with
    | some ci => pure ci | none => fail s!"missing dependency declaration {n}"
  let mut declMap : Std.HashMap Name String := {}
  for (n, st) in trustDecls do
    declMap := declMap.insert n.toName st
  let mut statusMap : Std.HashMap Name String := {}
  let mut ownerMap : Std.HashMap Name Name := {}
  for (cName, _) in locals do
    let orig ← origin env cName
    if trusted.contains orig then
      let (st, owner) ← classifyTrustedConstant declMap cName
      statusMap := statusMap.insert cName st
      ownerMap := ownerMap.insert cName owner
  let verifyCrateName := proofMod ++ `verify_crate
  let (crateAxioms, crateVisited) ←
    closure lookup (origin env) axioms #[verifyCrateName]
  let activeFeats ←
    collectActiveCandidateFeaturesWithInit lookup (origin env) trusted statusMap ownerMap #[verifyCrateName] #[]
  let replayLocals ← collectLocalClosure locals #[verifyCrateName]
  let base ← importModules (foundation.map ({ module := · })) Options.empty 0
  let tReplay0 ← IO.monoMsNow
  let _ ← base.toKernelEnv.replay replayLocals
  let replayMs := (← IO.monoMsNow) - tReplay0
  let totalMs := (← IO.monoMsNow) - t0
  return {
    mode := "single-stage"
    replayedCount := replayLocals.size
    visitedCount := crateVisited
    axioms := crateAxioms.map toString
    activeCandidateFeatures := activeFeats
    crossStageRealizedConsts := crossStageRealized
    replayMs := replayMs
    totalAuditMs := totalMs
  }

end ProbeTwoStagePreAudit

open ProbeTwoStagePreAudit

def main (args : List String) : IO UInt32 := do
  let workDir := System.FilePath.mk (args.headD ".")
  let foundationLockPath := System.FilePath.mk (args.getD 1 (toString (workDir / "foundation-lock.json")))
  initSearchPath (← findSysroot) [workDir]
  let foundationJson ← IO.FS.readFile foundationLockPath
  let .ok j := Json.parse foundationJson | fail "invalid foundation-lock.json"
  let .ok (.obj modsObj) := j.getObjVal? "modules"
    | fail "missing modules object"
  let .ok (axioms : Array (String × String)) := j.getObjValAs? (Array (String × String)) "axioms"
    | fail "missing axioms array"
  let foundation := modsObj.toArray.map (·.1.toName)
  let trusted := #[`Trusted.Attributes, `Trusted.Base, `Trusted]
  let theory := #[`Anneal.Theory, `Anneal]
  let trustDecls : Array (String × String) := #[
    ("Trusted.candidate", "vetted"),
    ("Trusted.Crate", "vetted"),
    ("Trusted.Crate.mk", "vetted"),
    ("Trusted.CrateTheorem", "vetted"),
    ("Trusted.GateInput", "vetted"),
    ("Trusted.GateInput.base", "vetted"),
    ("Trusted.GateInput.ext", "candidate:mir_ast"),
    ("Trusted.evalOp", "vetted"),
    ("Trusted.mir_ast_flag", "candidate:mir_ast"),
    ("Trusted.mir_sem_step", "candidate:mir_semantics"),
    ("Trusted.chainedGate", "vetted")
  ]

  -- 1. Run Stage-1 `preaudit` once and write `theory-lock.json`.
  let (theoryLock, preauditMs) ← runPreAudit foundation trusted theory axioms trustDecls
  let lockPath := workDir / "theory-lock.json"
  IO.FS.writeFile lockPath (toJson theoryLock).pretty
  IO.println s!"[preaudit] verified {theoryLock.replayedDeclarationCount} Trusted+Anneal declarations in {preauditMs} ms -> wrote {lockPath}"

  -- 2. Compare Single-Stage vs Runtime-Audit on Case A: Vetted-only crate
  --    with cross-stage `realizeConst` (`simp [Anneal.evalHelper]` in `ProofVetted`).
  let singleA ← runSingleStageAudit foundation trusted theory axioms trustDecls `MirVetted `ProofVetted
  let runtimeA ← runRuntimeAudit foundation trusted theory axioms theoryLock `MirVetted `ProofVetted
  IO.println s!"[Case A: Vetted + Cross-Stage realizeConst]"
  IO.println s!"  single-stage:  replayed={singleA.replayedCount}, axioms={singleA.axioms}, activeFeats={singleA.activeCandidateFeatures}"
  IO.println s!"  runtime-audit: replayed={runtimeA.replayedCount}, axioms={runtimeA.axioms}, activeFeats={runtimeA.activeCandidateFeatures}, crossStageRealized={runtimeA.crossStageRealizedConsts}"
  unless singleA.axioms == runtimeA.axioms do
    fail s!"Case A axiom mismatch: {singleA.axioms} != {runtimeA.axioms}"
  unless singleA.activeCandidateFeatures == runtimeA.activeCandidateFeatures do
    fail s!"Case A candidate feature mismatch: {singleA.activeCandidateFeatures} != {runtimeA.activeCandidateFeatures}"
  unless !runtimeA.crossStageRealizedConsts.isEmpty do
    fail "Case A expected non-empty crossStageRealizedConsts for Anneal.evalHelper.eq_1"

  -- 3. Compare Single-Stage vs Runtime-Audit on Case B: Candidate-activating
  --    crate with chained `@[vetted]` `Trusted.candidate` guard (`mir_ast`
  --    activated in `ProofCand`, unlocking `Trusted.chainedGate`'s guarded
  --    branch in `Anneal.Theory`, which in turn activates `mir_semantics`!).
  let singleB ← runSingleStageAudit foundation trusted theory axioms trustDecls `MirCand `ProofCand
  let runtimeB ← runRuntimeAudit foundation trusted theory axioms theoryLock `MirCand `ProofCand
  IO.println s!"[Case B: Chained Guarded Candidate Features + Axiom Propagation]"
  IO.println s!"  single-stage:  replayed={singleB.replayedCount}, axioms={singleB.axioms}, activeFeats={singleB.activeCandidateFeatures}"
  IO.println s!"  runtime-audit: replayed={runtimeB.replayedCount}, axioms={runtimeB.axioms}, activeFeats={runtimeB.activeCandidateFeatures}"
  unless singleB.axioms == runtimeB.axioms do
    fail s!"Case B axiom mismatch: {singleB.axioms} != {runtimeB.axioms}"
  unless singleB.activeCandidateFeatures == runtimeB.activeCandidateFeatures do
    fail s!"Case B candidate feature mismatch: {singleB.activeCandidateFeatures} != {runtimeB.activeCandidateFeatures}"
  unless runtimeB.activeCandidateFeatures == #["mir_ast", "mir_semantics"] do
    fail s!"Case B expected #[\"mir_ast\", \"mir_semantics\"], got {runtimeB.activeCandidateFeatures}"

  IO.println "[PASS] All Two-Stage Pre-Audit & Cross-Stage realizeConst assertions succeeded bit-for-bit."
  return 0
