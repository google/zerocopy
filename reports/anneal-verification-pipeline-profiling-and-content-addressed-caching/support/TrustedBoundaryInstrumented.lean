-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean.Elab.Import
import Lean.Parser.Tactic
import Lean.Replay
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr

open Lean

namespace TrustedBoundary

def validCandidateFeatures : List Name :=
  [`refinement, `step_result, `memory, `mir_ast, `mir_semantics, `rustc_capture, `mvp]

inductive TrustTier where
  | vetted
  | candidate (feature : Name)
  deriving BEq, DecidableEq

namespace TrustTier

def render : TrustTier → String
  | .vetted => "vetted"
  | .candidate feat => s!"candidate:{feat}"

def parse? (raw : String) : Option TrustTier :=
  if raw == "vetted" then
    some .vetted
  else if let some rest := raw.dropPrefix? "candidate:" then
    let feat := rest.toString.toName
    if validCandidateFeatures.contains feat then
      some (.candidate feat)
    else
      none
  else
    none

end TrustTier

inductive SourceRole where
  | trusted (tier : TrustTier)
  | theory
  deriving BEq, DecidableEq

inductive ModuleRole where
  | foundation
  | library
  | trusted (tier : TrustTier)
  | theory
  deriving BEq, DecidableEq

def fail (message : String) : IO α :=
  throw <| IO.userError s!"policy:{message}"

def field [FromJson α] (j : Json) (key : String) : IO α :=
  IO.ofExcept <| j.getObjValAs? α key

def names (j : Json) (key : String) : IO (Array Name) := do
  return (← field (α := Array String) j key).map String.toName

def artifacts (j : Json) : IO (NameMap ImportArtifacts) := do
  let entries ← field (α := Array (String × Array (Array String))) j "artifacts"
  entries.foldlM (init := {}) fun acc (n, parts) => do
    let modName := n.toName
    if (acc.find? modName).isSome then
      fail s!"duplicate artifact module {n}"
    return acc.insert modName
      (.ofArrays (parts.map (·.map System.FilePath.mk)))

def graph (env : Environment) : Json :=
  Json.mkObj <|
    (env.header.modules.zip env.header.moduleData).toList.map fun (m, d) =>
      (m.module.toString, toJson d.imports)

def importEnvWithArts (arts : NameMap ImportArtifacts) (roots : Array Name)
    (extensions := false) : IO Environment := do
  if extensions then unsafe enableInitializersExecution
  let env ← importModules (roots.map fun n => { module := n }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := extensions)
    (level := .private) (arts := arts)
  unless env.header.modules.size == env.header.moduleData.size do
    throw <| IO.userError "module/data array alignment failure"
  return env.setExporting false

def importEnv (j : Json) (roots : Array Name)
    (extensions := false) : IO Environment := do
  let arts ← artifacts j
  importEnvWithArts arts roots extensions

def validateGraph (j : Json) (env : Environment) : IO Unit := do
  let expected ← field (α := Json) j "graph"
  unless graph env == expected do
    fail "compiled module/import DAG differs from admitted DAG"

partial def collectExprConsts (pending : List Expr)
    (seen : Std.HashSet Expr := {}) (acc : NameSet := {}) : NameSet :=
  match pending with
  | [] => acc
  | x :: rest =>
    if seen.contains x then
      collectExprConsts rest seen acc
    else
      let seen := seen.insert x
      match x with
      | .const n _ => collectExprConsts rest seen (acc.insert n)
      | .lit (.natVal _) => collectExprConsts rest seen (acc.insert `Nat)
      | .lit (.strVal _) => collectExprConsts rest seen (acc.insert `String)
      | .app a b | .forallE _ a b _ | .lam _ a b _ =>
        collectExprConsts (a :: b :: rest) seen acc
      | .letE _ t v b _ =>
        collectExprConsts (t :: v :: b :: rest) seen acc
      | .proj s _ b =>
        collectExprConsts (b :: rest) seen (acc.insert s)
      | .mdata _ b =>
        collectExprConsts (b :: rest) seen acc
      | .bvar _ | .fvar _ | .mvar _ | .sort _ =>
        collectExprConsts rest seen acc

def expressionEdges (e : Expr) : IO NameSet := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then
    fail "open expression in stored declaration"
  return collectExprConsts [e]

def declarationEdges (ci : ConstantInfo) : IO NameSet := do
  let typeEdges ← expressionEdges ci.type
  let valEdges ← match ci.value? (allowOpaque := true) with
    | some value => expressionEdges value
    | none => pure {}
  let baseEdges := typeEdges ++ valEdges ++ .ofList ci.all
  match ci with
  | .inductInfo v => return baseEdges ++ .ofList v.ctors
  | .ctorInfo v => return baseEdges.insert v.induct
  | .recInfo v =>
    v.rules.foldlM (init := baseEdges ++ .ofList v.all) fun acc rule => do
      return (acc.insert rule.ctor) ++ (← expressionEdges rule.rhs)
  | .axiomInfo _ | .defnInfo _ | .thmInfo _ | .opaqueInfo _ | .quotInfo _ =>
    return baseEdges

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def origin (env : Environment) (n : Name) : IO Name := do
  let some idx := env.getModuleIdxFor? n
    | fail s!"unknown declaration origin: {n}"
  let some mod := env.header.modules[idx]?
    | fail s!"invalid module index: {n}"
  return mod.module

partial def closure (lookup : Name → IO ConstantInfo)
    (provenance : Name → IO Name) (axioms : Array (String × String))
    (pending : List Name) (visited : NameSet := {})
    (reachedAxioms : NameSet := {}) : IO (Array Name × NameSet) := do
  match pending with
  | [] => return (reachedAxioms.toArray.qsort Name.lt, visited)
  | n :: rest =>
    if visited.contains n then
      closure lookup provenance axioms rest visited reachedAxioms
    else
      let visited := visited.insert n
      let m ← provenance n
      let ci ← lookup n
      let reachedAxioms ← if ci.isAxiom then do
        unless axioms.contains (n.toString, m.toString) do
          fail s!"unapproved axiom {n} from {m}"
        pure (reachedAxioms.insert n)
      else
        pure reachedAxioms
      let deps ← declarationEdges ci
      closure lookup provenance axioms (deps.toList ++ rest) visited
        reachedAxioms

inductive TargetRole where
  | model | specification | capture | expected | proof
  deriving BEq

def targetRole (raw : String) : IO TargetRole :=
  match raw with
  | "model" => pure .model
  | "specification" => pure .specification
  | "capture" => pure .capture
  | "expected" => pure .expected
  | "proof" => pure .proof
  | _ => fail s!"unknown target role {raw}"

def TargetRole.allows (role dep : TargetRole) : Bool :=
  match role with
  | .model => dep == .model
  | .specification => dep == .model || dep == .specification
  | .capture => dep == .model || dep == .capture
  | .expected => dep != .proof
  | .proof => true

inductive TargetOrigin where
  | foundation | library | source (role : TargetRole)

/-! ## Instrumented Kernel Replay (`replayDetailed`) -/

namespace InstrumentedReplay

structure DeclTiming where
  name : Name
  kind : String
  elapsedNs : Nat

structure Context where
  newConstants : Std.HashMap Name ConstantInfo

structure State where
  env : Kernel.Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  declTimings : Array DeclTiming := #[]

abbrev M := ReaderT Context <| StateRefT State IO

def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false

def throwKernelException (ex : Kernel.Exception) : M Unit := do
  throw <| .userError <| (← ex.toMessageData {} |>.toString)

def addDeclTimed (declName : Name) (declKind : String) (d : Declaration) : M Unit := do
  let t0 ← IO.monoNanosNow
  let res := (← get).env.addDeclCore 0 0 d (cancelTk? := none)
  let t1 ← IO.monoNanosNow
  match res with
  | .ok env =>
    modify fun s => {
      s with
      env := env
      declTimings := s.declTimings.push { name := declName, kind := declKind, elapsedNs := t1 - t0 }
    }
  | .error ex => throwKernelException ex

mutual
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    replayConstants ci.getUsedConstantsAsSet
    if (← get).pending.contains name then
      try
        match ci with
        | .defnInfo info =>
          addDeclTimed name "definition" (Declaration.defnDecl info)
        | .thmInfo info =>
          if let some (.thmInfo info') := (← get).env.find? ci.name then
            if info.name == info'.name &&
              info.type == info'.type &&
              info.levelParams == info'.levelParams &&
              info.all == info'.all
            then
              modify fun s => { s with pending := s.pending.erase name }
              return
          addDeclTimed name "theorem" (Declaration.thmDecl info)
        | .axiomInfo info =>
          addDeclTimed name "axiom" (Declaration.axiomDecl info)
        | .opaqueInfo info =>
          addDeclTimed name "opaque" (Declaration.opaqueDecl info)
        | .inductInfo info =>
          let lparams := info.levelParams
          let nparams := info.numParams
          let all ← info.all.mapM fun n => do pure <| ((← read).newConstants[n]!)
          for o in all do
            modify fun s =>
              { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
          let ctorInfo ← all.mapM fun ci => do
            pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
              pure ((← read).newConstants[n]!))
          for (_, ctors) in ctorInfo do
            for ctor in ctors do
              replayConstants ctor.getUsedConstantsAsSet
          let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
            { name := ci.name
              type := ci.type
              ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
          addDeclTimed name "inductive" (Declaration.inductDecl lparams nparams types false)
        | .ctorInfo info =>
          modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
        | .recInfo info =>
          modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
        | .quotInfo _ =>
          replayConstant `Eq
          addDeclTimed name "quotient" Declaration.quotDecl
        modify fun s => { s with pending := s.pending.erase name }
      catch ex =>
        throw <| .userError s!"while replaying declaration '{name}':\n{ex}"

partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n
end

def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      if ! (info == info') then throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

def replay (newConstants : Std.HashMap Name ConstantInfo) (env : Kernel.Environment) :
    IO (Kernel.Environment × Array DeclTiming × Nat) := do
  let mut remaining : NameSet := ∅
  for (n, ci) in newConstants.toList do
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := { newConstants }) do
      for n in remaining do
        replayConstant n
      let tc0 ← IO.monoNanosNow
      checkPostponedConstructors
      checkPostponedRecursors
      let tc1 ← IO.monoNanosNow
      return (tc1 - tc0)
  return (s.env, s.declTimings, 0)

end InstrumentedReplay

def mvpPreverifiedModules : Array Name :=
  #[`Trusted, `Trusted.Mvp, `Trusted.Mvp.Semantics, `Trusted.Mvp.Syntax,
    `Anneal, `Anneal.Mvp.Canaries, `Anneal.Mvp.Execution]

def targetAuditInstrumented (j : Json) (foundation : Array Name) : IO (Json × Json) := do
  let tStart ← IO.monoNanosNow
  let baseMode := (j.getObjValAs? String "baseMode").toOption.getD "foundation"
  let skipMetadataReload := (j.getObjValAs? Bool "skipRedundantMetadataImport").toOption.getD false
  let target ← field (α := Json) j "target"
  let libraries ← names j "libraries"
  let modules ← field (α := Array Json) target "modules"
  let mut roles : Std.HashMap Name TargetOrigin := {}
  for m in foundation do roles := roles.insert m .foundation
  for m in libraries do
    if roles.contains m then fail s!"overlapping target module {m}"
    roles := roles.insert m .library
  let mut roots := foundation ++ libraries
  for item in modules do
    let m := (← field (α := String) item "module").toName
    let role ← targetRole (← field item "role")
    if roles.contains m then fail s!"overlapping target module {m}"
    roles := roles.insert m (.source role)
    roots := roots.push m

  let tBeforeArts ← IO.monoNanosNow
  let arts ← artifacts j
  let tAfterArts ← IO.monoNanosNow

  let env ← importEnvWithArts arts roots false
  let tAfterImportEnv ← IO.monoNanosNow

  validateGraph j env
  let tAfterValidateGraph ← IO.monoNanosNow

  let provenance n := do
    let m ← origin env n
    let some role := roles.get? m | fail s!"foreign target module {m}"
    return (m, role)
  let lookup n := do
    let some ci := env.checked.get.find? n
      | fail s!"missing target dependency {n}"
    return ci

  let mut sourceInventory : NameSet := {}
  for m in env.header.modules, data in env.header.moduleData do
    let some role := roles.get? m.module | fail s!"foreign target module {m.module}"
    if let .source _ := role then
      unless data.constNames == data.constants.map ConstantInfo.name do
        fail s!"invalid target inventory {m.module}"
      for ci in data.constants do
        if sourceInventory.contains ci.name then
          fail s!"duplicate target declaration {ci.name}"
        unless (← origin env ci.name) == m.module do
          fail s!"target inventory origin mismatch {ci.name}"
        let stored ← lookup ci.name
        unless stored.type == ci.type && stored.value? true == ci.value? true do
          fail s!"stored target declaration differs {ci.name}"
        sourceInventory := sourceInventory.insert ci.name
  let tAfterInventory ← IO.monoNanosNow

  let theoremName := (← field (α := String) target "theoremName").toName
  let theoremModule := (← field (α := String) target "theoremModule").toName
  let expectedName := (← field (α := String) target "expectedDeclaration").toName
  let expectedModule := (← field (α := String) target "expectedModule").toName
  match roles.get? theoremModule, roles.get? expectedModule with
  | some (.source .proof), some (.source .expected) => pure ()
  | _, _ => fail "incorrect target/expected authority roles"
  let theoremInfo ← lookup theoremName
  let expectedInfo ← lookup expectedName
  unless (← origin env theoremName) == theoremModule &&
      (← origin env expectedName) == expectedModule do
    fail "incorrect target/expected declaration origin"
  unless theoremInfo matches .thmInfo _ do fail "target root must be a theorem"
  unless expectedInfo matches .defnInfo _ do fail "Expected must be a definition"
  unless theoremInfo.levelParams.isEmpty && expectedInfo.levelParams.isEmpty do
    fail "target and Expected must have no universe parameters"
  unless expectedInfo.type == .sort .zero do fail "Expected must have type Prop"
  let canonicalRoot := (← field (α := String) target "canonicalRoot").toName
  let subjectName := (← field (α := String) target "subjectDeclaration").toName
  let specName := (← field (α := String) target "specificationDeclaration").toName
  for (n, requiredRole) in [(canonicalRoot, TargetRole.model),
      (subjectName, TargetRole.capture), (specName, TargetRole.specification)] do
    let (_, role) ← provenance n
    match role with
    | .source actual =>
      unless actual == requiredRole do fail s!"incorrect canonical input origin {n}"
    | _ => fail s!"incorrect canonical input origin {n}"
    unless (← lookup n).levelParams.isEmpty do
      fail s!"canonical input has universe parameters {n}"
  let canonical := mkApp2 (mkConst canonicalRoot) (mkConst subjectName) (mkConst specName)
  let axiomPolicy ← field (α := Array (String × String)) j "axioms"
  unless axiomPolicy == #[("Classical.choice", "Init.Prelude"),
      ("Quot.sound", "Init.Prelude"), ("propext", "Init.Core")] do
    fail "target axiom policy differs from the original foundation"

  let tBeforeClosure ← IO.monoNanosNow
  let (axioms, reached) ← closure lookup (origin env) axiomPolicy
    [theoremName, expectedName, canonicalRoot, subjectName, specName]
  let (_, expectedReached) ← closure lookup (origin env) axiomPolicy
    [canonicalRoot, subjectName, specName]
  let tAfterClosure ← IO.monoNanosNow

  -- Determine which modules belong to `base` under `baseMode`
  let baseRoots : Array Name :=
    match baseMode with
    | "foundation+trusted_mvp" => foundation ++ #[`Trusted, `Trusted.Mvp, `Trusted.Mvp.Semantics, `Trusted.Mvp.Syntax]
    | "foundation+mvp" => foundation ++ mvpPreverifiedModules
    | "foundation+libraries" => foundation ++ libraries
    | "foundation+libraries+mvp" => foundation ++ libraries ++ mvpPreverifiedModules
    | _ => foundation

  let tBeforeImportBase ← IO.monoNanosNow
  let base ← importEnvWithArts arts baseRoots false
  let tAfterImportBase ← IO.monoNanosNow
  let baseModSet : NameSet := .ofList (base.header.modules.toList.map (·.module))

  let mut replayMap : Std.HashMap Name ConstantInfo := {}
  let mut modelRoots : List Name := []
  let mut specRoots : List Name := []
  for n in reached do
    let ci ← lookup n
    let (origMod, role) ← provenance n
    match role with
    | .foundation => pure ()
    | .library | .source _ =>
      if ci.isUnsafe || ci.isPartial then
        fail s!"unsafe/partial logical dependency {n}"
      if ci matches .quotInfo _ then fail s!"unexpected quotient primitive {n}"
      if ci.hasValue true && (ci.value? true).isNone then
        fail s!"missing stored body {n}"
      if let .source _ := role then
        unless sourceInventory.contains n do
          fail s!"uninventoried target dependency {n}"
      for dep in ← declarationEdges ci do
        let (_, depRole) ← provenance dep
        match role, depRole with
        | .source r, .source d =>
          unless r.allows d do fail s!"target authority violation {n} references {dep}"
        | .library, .source _ =>
          fail s!"installed library {n} references target source {dep}"
        | _, _ => pure ()
      unless baseModSet.contains origMod do
        replayMap := replayMap.insert n ci
    if expectedReached.contains n then
      match role with
      | .source .model => modelRoots := n :: modelRoots
      | .source .specification => specRoots := n :: specRoots
      | _ => pure ()
  let tAfterPolicyLoop ← IO.monoNanosNow

  let (replayed, declTimings, _) ← try InstrumentedReplay.replay replayMap base.toKernelEnv
    catch error => fail s!"kernel replay rejected target dependency: {error}"
  let tAfterReplay ← IO.monoNanosNow

  let checkedEnv := Environment.ofKernelEnv replayed
  unless (Kernel.check checkedEnv {} canonical).toOption == some (.sort .zero) do
    fail "canonical root application must have type Prop"
  let some expectedBody := expectedInfo.value? true
    | fail "Expected has no stored body"
  unless Kernel.isDefEqGuarded checkedEnv {} expectedBody canonical do
    fail "compiled Expected body differs from the canonical root"
  match Kernel.isDefEq checkedEnv {} theoremInfo.type canonical with
  | .ok true => pure ()
  | .ok false => fail "target theorem type differs from Expected"
  | .error _ => fail "kernel could not compare target theorem type"
  let tAfterDefEq ← IO.monoNanosNow

  let mut tAfterFixedMeta := tAfterDefEq
  let mut tAfterTargetMeta := tAfterDefEq
  let mut tAfterCompilerOverrides := tAfterDefEq
  if !skipMetadataReload then
    let fixedMetadata ← importEnvWithArts arts (foundation ++ libraries) true
    tAfterFixedMeta ← IO.monoNanosNow
    let targetMetadata ← importEnvWithArts arts roots true
    tAfterTargetMeta ← IO.monoNanosNow
    for n in reached do
      unless Compiler.getImplementedBy? fixedMetadata n ==
          Compiler.getImplementedBy? targetMetadata n &&
          getExternAttrData? fixedMetadata n == getExternAttrData? targetMetadata n do
        fail s!"unchecked compiler override on logical dependency {n}"
      let replacement (metadata : Environment) :=
        (Compiler.CSimp.ext.getState metadata).map.find? n |>.map fun e =>
          (e.toDeclName, e.thmName)
      unless replacement fixedMetadata == replacement targetMetadata do
        fail s!"authored compiler replacement on logical dependency {n}"
    tAfterCompilerOverrides ← IO.monoNanosNow

  let (_, modelClosure) ← closure lookup (origin env) axiomPolicy modelRoots
  let (_, specClosure) ← closure lookup (origin env) axiomPolicy specRoots
  let describe (nodes : NameSet) := nodes.toArray.qsort Name.lt |>.mapM fun n => do
    return Json.mkObj [("name", toJson n), ("module", toJson (← origin env n))]
  let modelClosureJson ← describe modelClosure
  let specClosureJson ← describe specClosure
  let tAfterModelSpecClosure ← IO.monoNanosNow

  -- Aggregate replay declaration timings by module and find top-30 declarations
  let mut modNanos : Std.HashMap String (Nat × Nat) := {}
  let mut totalAddDeclNs : Nat := 0
  for dt in declTimings do
    totalAddDeclNs := totalAddDeclNs + dt.elapsedNs
    let origMod := (← origin env dt.name).toString
    let (cnt, sumNs) := modNanos.getD origMod (0, 0)
    modNanos := modNanos.insert origMod (cnt + 1, sumNs + dt.elapsedNs)

  let modRows := modNanos.toArray.qsort (fun a b => a.2.2 > b.2.2) |>.map fun (m, (cnt, ns)) =>
    Json.mkObj [
      ("module", toJson m),
      ("declarations", toJson cnt),
      ("addDeclNs", toJson ns),
      ("addDeclMs", toJson (ns.toFloat / 1000000.0))
    ]

  let sortedDecls := declTimings.qsort (fun a b => a.elapsedNs > b.elapsedNs)
  let topDecls ← (sortedDecls.extract 0 (Nat.min 30 sortedDecls.size)).mapM fun dt => do
    let origMod := (← origin env dt.name).toString
    return Json.mkObj [
      ("name", toJson dt.name.toString),
      ("module", toJson origMod),
      ("kind", toJson dt.kind),
      ("elapsedNs", toJson dt.elapsedNs),
      ("elapsedMs", toJson (dt.elapsedNs.toFloat / 1000000.0))
    ]

  let nsToMs (ns : Nat) : Json := toJson (ns.toFloat / 1000000.0)
  let breakdown := Json.mkObj [
    ("baseMode", toJson baseMode),
    ("reachedCount", toJson reached.size),
    ("replayMapSize", toJson replayMap.size),
    ("replayedAddDeclCount", toJson declTimings.size),
    ("phasesMs", Json.mkObj [
      ("parseRequestFieldsAndArtifacts", nsToMs (tAfterArts - tStart)),
      ("importTargetEnvNoExts", nsToMs (tAfterImportEnv - tAfterArts)),
      ("validateGraph", nsToMs (tAfterValidateGraph - tAfterImportEnv)),
      ("verifySourceInventory", nsToMs (tAfterInventory - tAfterValidateGraph)),
      ("reachabilityClosures", nsToMs (tAfterClosure - tAfterInventory)),
      ("importBaseEnvNoExts", nsToMs (tAfterImportBase - tBeforeImportBase)),
      ("roleAndEdgePolicyCheck", nsToMs (tAfterPolicyLoop - tAfterImportBase)),
      ("kernelReplayTotal", nsToMs (tAfterReplay - tAfterPolicyLoop)),
      ("kernelReplayAddDeclCoreSum", nsToMs totalAddDeclNs),
      ("kernelReplayOverhead", nsToMs ((tAfterReplay - tAfterPolicyLoop) - totalAddDeclNs)),
      ("postReplayDefEqChecks", nsToMs (tAfterDefEq - tAfterReplay)),
      ("importFixedMetadataWithExts", nsToMs (tAfterFixedMeta - tAfterDefEq)),
      ("importTargetMetadataWithExts", nsToMs (tAfterTargetMeta - tAfterFixedMeta)),
      ("compilerOverrideChecks", nsToMs (tAfterCompilerOverrides - tAfterTargetMeta)),
      ("modelAndSpecClosures", nsToMs (tAfterModelSpecClosure - tAfterCompilerOverrides)),
      ("totalTargetAudit", nsToMs (tAfterModelSpecClosure - tStart))
    ]),
    ("replayByModule", .arr modRows),
    ("top30SlowestDeclarations", .arr topDecls)
  ]

  let res := Json.mkObj [
    ("theorem", toJson theoremName),
    ("canonicalRoot", toJson canonicalRoot), ("subject", toJson subjectName),
    ("specification", toJson specName), ("graph", graph env),
    ("expected", toJson expectedName), ("axioms", toJson axioms),
    ("replay", toJson true), ("exactType", toJson true),
    ("replayedDeclarations", toJson replayMap.size),
    ("modelClosure", .arr modelClosureJson),
    ("specificationClosure", .arr specClosureJson)]
  return (res, breakdown)

def runInstrumented (j : Json) : IO (Json × Json) := do
  initSearchPath (← field (α := String) j "sysroot")
  let foundation ← names j "foundation"
  targetAuditInstrumented j foundation

end TrustedBoundary

def main (args : List String) : IO UInt32 := do
  let [request, output] := args
    | IO.eprintln "expected request and result files"; return 2
  try
    let t0 ← IO.monoNanosNow
    let rawText ← IO.FS.readFile request
    let t1 ← IO.monoNanosNow
    let j ← IO.ofExcept <| Json.parse rawText
    let t2 ← IO.monoNanosNow
    let (result, breakdown) ← TrustedBoundary.runInstrumented j
    let t3 ← IO.monoNanosNow
    let outStr := (Json.mkObj [("ok", toJson true), ("result", result)]).pretty
    IO.FS.writeFile output outStr
    let t4 ← IO.monoNanosNow
    let fullBreakdown := Json.mkObj [
      ("readFileMs", toJson ((t1 - t0).toFloat / 1000000.0)),
      ("jsonParseMs", toJson ((t2 - t1).toFloat / 1000000.0)),
      ("runTargetAuditMs", toJson ((t3 - t2).toFloat / 1000000.0)),
      ("jsonSerializeAndWriteMs", toJson ((t4 - t3).toFloat / 1000000.0)),
      ("totalMainMs", toJson ((t4 - t0).toFloat / 1000000.0)),
      ("auditBreakdown", breakdown)
    ]
    IO.FS.writeFile (output ++ ".timings.json") fullBreakdown.pretty
    return 0
  catch error =>
    let message := error.toString
    let category :=
      if message.startsWith "policy:" then "policy" else "operational"
    IO.FS.writeFile output <|
      (Json.mkObj [
        ("ok", toJson false), ("category", toJson category),
        ("message", toJson message)]).pretty
    IO.eprintln message
    return if category == "policy" then 1 else 2
