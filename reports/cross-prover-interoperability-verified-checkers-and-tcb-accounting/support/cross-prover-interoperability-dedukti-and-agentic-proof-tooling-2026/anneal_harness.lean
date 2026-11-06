/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

import Lean.Elab.Frontend
import Lean.Elab.Tactic.Basic

/-!
# Zero-Dependency Environment Search and Goal-State Harness for Lean v4.34.1

This standalone script provides two programmatic capabilities for Anneal agents
using only the Lean `v4.34.1` standard library and compiler (`Lean` package):

1. `search`: A lightweight local Loogle engine that searches loaded modules
   (`Init.*`, `Std.*`, `Trusted.*`, `Anneal.*`, or declarations elaborated from
   a local file or snippet) by type shape (`?a -> ?b`, subterm matching, or
   conclusion matching up to hypothesis permutation), referenced constants,
   declaration-name substrings, and module prefixes.
2. `goals`: A Frontend and InfoTree elaborator that compiles a Lean snippet or
   file, extracts structured JSON for all tactic steps, unsolved goals (with
   full local context hypotheses, let-bindings, metavariable coupling across
   goals, and 1-indexed source spans), and diagnostics, and optionally tests a
   candidate tactic against the first unsolved goal state.
-/

open Lean Core Meta Elab Term Command Frontend

namespace AnnealHarness

/-!
## JSON and Source Span Utilities
-/

/-- Converts a `FileMap` and byte position into a 1-indexed `(line, column)`
pair matching LSP/editor conventions. -/
def posToLineCol (fileMap : FileMap) (pos : String.Pos.Raw) : Nat × Nat :=
  let p := fileMap.toPosition pos
  (p.line, p.column + 1)

/-- Extracts a JSON span object from a `Syntax` node's source range. -/
def syntaxSpanJson (fileMap : FileMap) (stx : Syntax) : Json :=
  let startPos := stx.getPos? (canonicalOnly := false) |>.getD 0
  let endPos := stx.getTailPos? (canonicalOnly := false) |>.getD startPos
  let (startLine, startCol) := posToLineCol fileMap startPos
  let (endLine, endCol) := posToLineCol fileMap endPos
  Json.mkObj [
    ("startLine", .num startLine),
    ("startCol", .num startCol),
    ("endLine", .num endLine),
    ("endCol", .num endCol)
  ]

/-- Classifies a `ConstantInfo` into its declaration kind string. -/
def constantKind : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "inductive"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "recursor"

/-- Resolves the defining module name for `declName` in `env`. Returns
`"(local)"` for declarations elaborated in the current snippet. -/
def getDeclModuleName (env : Environment) (declName : Name) : String :=
  match env.getModuleIdxFor? declName with
  | some modIdx =>
    match env.header.moduleNames[modIdx.toNat]? with
    | some modName => modName.toString
    | none => "(unknown)"
  | none => "(local)"

/-- Filters internal compiler-generated auxiliary declarations so search results
surface user-facing theorems and definitions. -/
def isInternalOrBlacklisted (name : Name) : Bool :=
  name.isInternalDetail ||
  match name with
  | .str _ s =>
    s.startsWith "_" || s.startsWith "eq_" || s.startsWith "congr_" ||
    s == "recOn" || s == "casesOn" || s == "brecOn" || s == "below" ||
    s == "ibelow" || s == "noConfusion" || s == "noConfusionType" ||
    s == "sizeOf_spec" || s == "inj" || s == "injEq"
  | _ => true

/-!
## Part 1: Lightweight Local Loogle Type-Shape and Substring Search

Adapted from Joachim Breitner's `Loogle.Find` architecture:
- Pattern expressions such as `(?a -> ?b) -> List ?a -> List ?b` are elaborated
  with `ignoreTCFailures := true` and `errToSorry := false`, and resumed with
  `withoutPostponing` so numeric/relation patterns do not default to `Nat`.
- Pattern metavariables are abstracted into an `AbstractMVarsResult` template
  that can be freshly instantiated in a temporary `withNewMCtxDepth` scope for
  each candidate constant.
- `matchUpToHyps` opens the candidate's `forallTelescope` and the pattern's
  `forallMetaTelescope`, checks fast `HeadIndex` compatibility on conclusions,
  unifies conclusions via `isDefEq`, and matches pattern hypotheses against
  candidate hypotheses up to permutation (`matchHyps`).
- `matchAnywhere` traverses subexpressions via `Meta.forEachExpr'`, pruning
  branches whose used constants do not contain all constants in the pattern.
-/

/-- Checks whether two `HeadIndex` values can unify. Metavariable heads can
match any head constructor. -/
def canMatchHead : HeadIndex → HeadIndex → Bool
  | .mvar _, _ => true
  | _, .mvar _ => true
  | hi₁, hi₂   => hi₁ == hi₂

/-- Matches pattern hypotheses `ps` against candidate hypotheses `newHyps` up
to reordering, backtracking across candidate hypotheses as needed. -/
partial def matchHyps : List Expr → List Expr → List Expr → MetaM Bool
  | p :: ps, oldHyps, h :: newHyps => do
    let pt ← inferType p
    let t ← inferType h
    let matched ← checkpointDefEq (mayPostpone := false) do
      if ← isDefEq pt t then
        matchHyps ps [] (oldHyps ++ newHyps)
      else
        pure false
    if matched then
      return true
    else
      matchHyps (p :: ps) (h :: oldHyps) newHyps
  | [], _, _      => pure true
  | _ :: _, _, [] => pure false

/-- Checks whether `e` matches the abstracted pattern `pat` up to hypothesis
reordering. Wrapped in `withNewMCtxDepth` so metavariable assignments do not
leak across subterm or declaration checks. -/
def matchUpToHyps (pat : AbstractMVarsResult) (head : HeadIndex) (e : Expr) :
    MetaM Bool :=
  withNewMCtxDepth do
    forallTelescopeReducing e fun eParams eConcl => do
      if canMatchHead head eConcl.toHeadIndex then
        let (_, _, patExpr) ← openAbstractMVarsResult pat
        let (patParams, _, patConcl) ← forallMetaTelescopeReducing patExpr
        if ← isDefEq eConcl patConcl then
          matchHyps patParams.toList [] eParams.toList
        else
          pure false
      else
        pure false

/-- Checks whether every constant in `requiredConsts` occurs in `e`, used to
prune subexpression traversal early. -/
def hasAllConsts (requiredConsts : NameSet) (e : Expr) : Bool := Id.run do
  let used := e.getUsedConstantsAsSet
  for c in requiredConsts do
    if !used.contains c then
      return false
  return true

/-- Compiles a conclusion pattern (`|- T`) into a `ConstantInfo` predicate. -/
def mkConclusionMatcher (patExpr : Expr) : MetaM (ConstantInfo → MetaM Bool) :=
  withReducible do
    let patConsts := patExpr.getUsedConstantsAsSet
    let head := (← forallMetaTelescopeReducing patExpr).2.2.toHeadIndex
    let pat ← abstractMVars (← instantiateMVars patExpr)
    return fun (ci : ConstantInfo) => withReducible do
      if !hasAllConsts patConsts ci.type then
        return false
      let cTy := ci.instantiateTypeLevelParams (← mkFreshLevelMVars ci.numLevelParams)
      matchUpToHyps pat head cTy

/-- Compiles a subexpression pattern into a predicate on `ConstantInfo` that
succeeds if any subexpression of the declaration's type matches `patExpr`. -/
def mkSubtermMatcher (patExpr : Expr) : MetaM (ConstantInfo → MetaM Bool) :=
  withReducible do
    let patConsts := patExpr.getUsedConstantsAsSet
    let head := (← forallMetaTelescopeReducing patExpr).2.2.toHeadIndex
    let pat ← abstractMVars (← instantiateMVars patExpr)
    return fun (ci : ConstantInfo) => withReducible do
      if !hasAllConsts patConsts ci.type then
        return false
      let cTy := ci.instantiateTypeLevelParams (← mkFreshLevelMVars ci.numLevelParams)
      let found ← IO.mkRef false
      Meta.forEachExpr' cTy fun subExpr => do
        if ← found.get then
          return false
        if !hasAllConsts patConsts subExpr then
          return false
        if ← matchUpToHyps pat head subExpr then
          found.set true
          return false
        return true
      found.get

/-- Parses and elaborates a user pattern string into a `MetaM` expression while
preserving unassigned pattern metavariables (`?a`, `?b`, `_`). -/
def elabPatternString (patStr : String) (isConclusion : Bool) :
    TermElabM Expr := do
  let env ← getEnv
  match Parser.runParserCategory env `term patStr "<pattern>" with
  | .error err => throwError s!"Failed to parse pattern '{patStr}': {err}"
  | .ok stx =>
    withTheReader Term.Context
        ({ · with ignoreTCFailures := true, errToSorry := false }) do
      let expected? ←
        if isConclusion then
          pure (some (mkSort (← mkFreshLevelMVar)))
        else
          pure none
      let e ← Term.elabTerm stx expected?
      Term.withoutPostponing <|
        Term.synthesizeSyntheticMVars (postpone := .yes) (ignoreStuckTC := true)
      instantiateMVars e

/-- Pretty-prints a constant's type signature on a single line. -/
def ppConstantType (ci : ConstantInfo) : MetaM String := do
  try
    let fmt ← Meta.ppExpr ci.type
    return fmt.pretty (width := 10000)
  catch _ =>
    return toString ci.type

/-- Computes the AST size of an expression to rank concise lemmas first. -/
def exprSize : Expr → Nat
  | .forallE _ d b _ => 1 + exprSize d + exprSize b
  | .lam _ d b _     => 1 + exprSize d + exprSize b
  | .letE _ t v b _  => 1 + exprSize t + exprSize v + exprSize b
  | .app f a         => 1 + exprSize f + exprSize a
  | .mdata _ b       => 1 + exprSize b
  | .proj _ _ b      => 1 + exprSize b
  | _                => 1

/-- Configuration for the `search` subcommand. -/
structure SearchConfig where
  modules     : Array Name := #[`Init, `Std]
  extraFiles  : Array String := #[]
  extraCode   : Option String := none
  nameSubstrs : Array String := #[]
  modPrefixes : Array String := #[]
  reqConsts   : Array Name := #[]
  subPats     : Array String := #[]
  conclPats   : Array String := #[]
  maxResults  : Nat := 25
  includeDoc  : Bool := false

/-!
## Part 2: Frontend Elaboration and Structured Goal / InfoTree Extraction

Adapted from `Pantograph/Frontend/Basic.lean`, `Pantograph/Goal.lean`, and
`Pantograph/Delab.lean`:
- Runs `Lean.Elab.Frontend` with `infoState.enabled := true` to collect all
  `InfoTree`s and diagnostics.
- Extracts `TacticInfo` nodes and `TermInfo` nodes (for `sorry` terms),
  serializing each goal's local context (`LocalDecl`), target type, and
  shared/dependent metavariables (`Meta.getMVars`) so callers can detect
  existential metavariable coupling across goals.
-/

/-- Serializes a single goal `mvarId` inside its `MetavarContext` into a
structured JSON object containing hypotheses, target type, and coupled mvars. -/
def serializeGoal (mctx : MetavarContext) (mvarId : MVarId) : MetaM Json :=
  withMCtx mctx do
    let some mvarDecl := mctx.findDecl? mvarId
      | return Json.mkObj [
          ("mvarId", .str mvarId.name.toString),
          ("error", .str "unregistered mvarId")
        ]
    mvarId.withContext do
      let mut hyps : Array Json := #[]
      let mut coupledMVars : NameSet := {}
      for localDecl in mvarDecl.lctx do
        if !localDecl.isImplementationDetail then
          let ty ← instantiateMVars localDecl.type
          for mv in (← Meta.getMVars ty) do
            coupledMVars := coupledMVars.insert mv.name
          let tyStr := (← Meta.ppExpr ty).pretty (width := 10000)
          match localDecl with
          | .cdecl _ fvarId userName _ _ _ =>
            hyps := hyps.push <| Json.mkObj [
              ("name", .str userName.toString),
              ("fvarId", .str fvarId.name.toString),
              ("type", .str tyStr),
              ("isLet", .bool false)
            ]
          | .ldecl _ fvarId userName _ val _ _ =>
            let val' ← instantiateMVars val
            for mv in (← Meta.getMVars val') do
              coupledMVars := coupledMVars.insert mv.name
            let valStr := (← Meta.ppExpr val').pretty (width := 10000)
            hyps := hyps.push <| Json.mkObj [
              ("name", .str userName.toString),
              ("fvarId", .str fvarId.name.toString),
              ("type", .str tyStr),
              ("value", .str valStr),
              ("isLet", .bool true)
            ]
      let target ← instantiateMVars mvarDecl.type
      for mv in (← Meta.getMVars target) do
        coupledMVars := coupledMVars.insert mv.name
      let targetStr := (← Meta.ppExpr target).pretty (width := 10000)
      let prettyGoal := (← Meta.ppGoal mvarId).pretty
      let depMVarArr := coupledMVars.toList.toArray.map (Json.str ∘ Name.toString)
      return Json.mkObj [
        ("mvarId", .str mvarId.name.toString),
        ("userName", if mvarDecl.userName.isAnonymous then .null
                     else .str mvarDecl.userName.toString),
        ("target", .str targetStr),
        ("hypotheses", .arr hyps),
        ("dependentMVars", .arr depMVarArr),
        ("pretty", .str prettyGoal)
      ]

/-- Record of a tactic step or `sorry` hole discovered in the `InfoTree`. -/
structure ExtractedStep where
  kind        : String
  syntaxText  : String
  span        : Json
  startPos    : Nat
  endPos      : Nat
  ctxInfo     : ContextInfo
  tacticInfo? : Option TacticInfo
  goalsBefore : Array Json
  goalsAfter  : Array Json

/-- Traverses an `InfoTree` to collect tactic steps and `sorry` term holes. -/
partial def collectInfoTreeSteps (fileMap : FileMap) (tree : InfoTree) :
    IO (Array ExtractedStep) := do
  let resultsRef ← IO.mkRef (#[] : Array ExtractedStep)
  let _ ← tree.visitM (m := IO)
    (preNode := fun _ _ _ => pure true)
    (postNode := fun ctx info _ _ => do
      match info with
      | .ofTacticInfo ti =>
        let some startPos := ti.stx.getPos? (canonicalOnly := false)
          | return ()
        let some endPos := ti.stx.getTailPos? (canonicalOnly := false)
          | return ()
        let stxText := String.Pos.Raw.extract fileMap.source startPos endPos
        let span := syntaxSpanJson fileMap ti.stx
        let ctxBefore := { ctx with mctx := ti.mctxBefore }
        let goalsBefore ← ctxBefore.runMetaM {} do
          ti.goalsBefore.toArray.mapM (serializeGoal ti.mctxBefore)
        let ctxAfter := { ctx with mctx := ti.mctxAfter }
        let goalsAfter ← ctxAfter.runMetaM {} do
          ti.goalsAfter.toArray.mapM (serializeGoal ti.mctxAfter)
        resultsRef.modify fun arr => arr.push {
          kind        := toString ti.stx.getKind
          syntaxText  := stxText.trimAscii.toString
          span        := span
          startPos    := startPos.byteIdx
          endPos      := endPos.byteIdx
          ctxInfo     := ctx
          tacticInfo? := some ti
          goalsBefore := goalsBefore
          goalsAfter  := goalsAfter
        }
      | .ofTermInfo termInfo =>
        if termInfo.expr.isSorry then
          let some startPos := termInfo.stx.getPos? (canonicalOnly := false)
            | return ()
          let some endPos := termInfo.stx.getTailPos? (canonicalOnly := false)
            | return ()
          let stxText := String.Pos.Raw.extract fileMap.source startPos endPos
          if stxText.trimAscii.toString == "sorry" then
            let span := syntaxSpanJson fileMap termInfo.stx
            let sorryGoalJson ← ctx.runMetaM termInfo.lctx do
              let ty ← match termInfo.expectedType? with
                | some t => instantiateMVars t
                | none   => instantiateMVars (← Meta.inferType termInfo.expr)
              let mvar ← Meta.mkFreshExprSyntheticOpaqueMVar ty
              serializeGoal (← getMCtx) mvar.mvarId!
            resultsRef.modify fun arr => arr.push {
              kind        := "sorryTerm"
              syntaxText  := "sorry"
              span        := span
              startPos    := startPos.byteIdx
              endPos      := endPos.byteIdx
              ctxInfo     := ctx
              tacticInfo? := none
              goalsBefore := #[sorryGoalJson]
              goalsAfter  := #[]
            }
      | _ => pure ())
  resultsRef.get

/-- Elaborates a complete Lean source string (including `import` headers) using
`Lean.Elab.Frontend`, returning the final `Environment`, `FileMap`,
`MessageLog`, and `InfoTree` array. -/
unsafe def elaborateSource (source : String) (fileName : String := "<input>")
    (extraImports : Array Name := #[]) :
    IO (Environment × FileMap × MessageLog × PersistentArray InfoTree) := do
  let inputCtx := Parser.mkInputContext source fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let headerImports := Elab.headerToImports header
  let extraImportSpecs := extraImports.map fun m => { module := m : Import }
  enableInitializersExecution
  let (env, messages) ←
    if headerImports.isEmpty && extraImportSpecs.isEmpty then
      let env ← importModules #[{ module := `Init : Import }] {}
        (trustLevel := 0) (loadExts := true)
      pure (env, messages)
    else if !extraImportSpecs.isEmpty then
      let base := if headerImports.isEmpty then #[{ module := `Init : Import }]
                  else headerImports
      let env ← importModules (base ++ extraImportSpecs) {}
        (trustLevel := 0) (loadExts := true)
      pure (env, messages)
    else
      processHeader
        (header := header)
        (opts := {})
        (messages := messages)
        (inputCtx := inputCtx)
        (trustLevel := 0)
        (plugins := #[])
        (leakEnv := false)
  let commandState := {
    Command.mkState env messages {} with
    infoState.enabled := true
  }
  let frontendState ← IO.processCommands inputCtx parserState commandState
  return (
    frontendState.commandState.env,
    inputCtx.fileMap,
    frontendState.commandState.messages,
    frontendState.commandState.infoState.trees
  )

/-- Executes a candidate tactic string `tacticStr` on the `goalsBefore` state of
an `ExtractedStep` and returns a JSON report of the resulting goals or error. -/
def runCandidateTactic (step : ExtractedStep) (tacticStr : String) :
    IO Json := do
  let some ti := step.tacticInfo?
    | return Json.mkObj [("error", .str "Step has no TacticInfo state")]
  let some mainGoal := ti.goalsBefore.head?
    | return Json.mkObj [("error", .str "No open goals in TacticInfo state")]
  let ctxBefore := { step.ctxInfo with mctx := ti.mctxBefore }
  try
    let lctx := (ti.mctxBefore.findDecl? mainGoal).map (·.lctx) |>.getD {}
    ctxBefore.runMetaM lctx do
      let env ← getEnv
      let stx ← match Parser.runParserCategory env `tactic tacticStr "<tactic>" with
        | .ok s    => pure s
        | .error e => throwError s!"Parse error: {e}"
      let termCtx : Term.Context := {
        declName? := step.ctxInfo.parentDecl?
        errToSorry := false
      }
      Core.resetMessageLog
      let tacticState : Elab.Tactic.State := { goals := ti.goalsBefore }
      let (_, newTacticState) ←
        (Elab.Tactic.evalTactic stx |>.run { elaborator := .anonymous }
          |>.run tacticState)
          |>.run' termCtx
      let msgs ← (← Core.getMessageLog).toList.mapM fun m => do
        pure (m.severity, (← m.data.toString).trimAscii.toString)
      let errMsgs := msgs.filterMap fun (sev, txt) =>
        if sev == .error then some txt else none
      let mctxAfter ← getMCtx
      let rootExpr := (instantiateMVarsCore mctxAfter (.mvar mainGoal)).1
      if !errMsgs.isEmpty || rootExpr.hasSorry then
        let errStr := if !errMsgs.isEmpty then
          "\n".intercalate errMsgs
        else
          "Tactic failed (generated sorry)"
        return Json.mkObj [
          ("tactic", .str tacticStr),
          ("success", .bool false),
          ("error", .str errStr)
        ]
      let unsolved ← newTacticState.goals.filterM fun g =>
        return !(mctxAfter.eAssignment.contains g ||
                 mctxAfter.dAssignment.contains g)
      let serialized ← unsolved.toArray.mapM (serializeGoal mctxAfter)
      return Json.mkObj [
        ("tactic", .str tacticStr),
        ("success", .bool true),
        ("goalsSolved", .bool unsolved.isEmpty),
        ("remainingGoals", .arr serialized)
      ]
  catch ex =>
    return Json.mkObj [
      ("tactic", .str tacticStr),
      ("success", .bool false),
      ("error", .str ex.toString)
    ]

/-!
## Execution Entry Points for `search` and `goals`
-/

/-- Runs the `search` subcommand and prints structured JSON to stdout. -/
unsafe def runSearch (cfg : SearchConfig) : IO UInt32 := do
  enableInitializersExecution
  let mut env ← importModules
    (imports := cfg.modules.map ({ module := · }))
    (opts := {})
    (trustLevel := 0)
    (loadExts := true)
  for filePath in cfg.extraFiles do
    let content ← IO.FS.readFile filePath
    let (env', _, _, _) ← elaborateSource content filePath cfg.modules
    env := env'
  if let some code := cfg.extraCode then
    let (env', _, _, _) ← elaborateSource code "<search-snippet>" cfg.modules
    env := env'

  let coreCtx : Core.Context := {
    fileName := "<search>"
    fileMap := FileMap.ofString ""
    maxHeartbeats := 0
  }
  let coreState : Core.State := { env := env }

  let jsonOut ← (do
    -- 1. Elaborate conclusion and subterm patterns in `TermElabM`
    let conclExprs ← TermElabM.run' <|
      cfg.conclPats.mapM (elabPatternString · true)
    let subExprs ← TermElabM.run' <|
      cfg.subPats.mapM (elabPatternString · false)

    -- 2. Compile pattern matchers
    let conclMatchers ← conclExprs.mapM mkConclusionMatcher
    let subMatchers ← subExprs.mapM mkSubtermMatcher
    let allMatchers := conclMatchers ++ subMatchers

    -- 3. Collect all required constants from `--const` and pattern expressions
    let mut reqConsts : NameSet := cfg.reqConsts.foldl NameSet.insert {}
    for e in conclExprs ++ subExprs do
      reqConsts := e.foldConsts reqConsts (flip NameSet.insert)

    let lowerSubstrs := cfg.nameSubstrs.map String.toLower

    -- 4. Scan environment constants (`map₁` imported + `map₂` local)
    let mut candidates : Array (ConstantInfo × String × Nat) := #[]
    let checkConst (name : Name) (ci : ConstantInfo) :
        MetaM (Option (ConstantInfo × String × Nat)) := do
      if isInternalOrBlacklisted name then
        return none
      let modName := getDeclModuleName env name
      if !cfg.modPrefixes.isEmpty then
        unless cfg.modPrefixes.any (fun p => modName.startsWith p) do
          return none
      if !lowerSubstrs.isEmpty then
        let lowerName := name.toString.toLower
        unless lowerSubstrs.all (fun sub => (lowerName.find? sub).isSome) do
          return none
      if !hasAllConsts reqConsts ci.type then
        return none
      for m in allMatchers do
        unless ← m ci do
          return none
      return some (ci, modName, exprSize ci.type)

    for (name, ci) in env.constants.map₁.toList do
      if let some hit ← checkConst name ci then
        candidates := candidates.push hit
    for (name, ci) in env.constants.map₂.toList do
      if let some hit ← checkConst name ci then
        candidates := candidates.push hit

    -- 5. Sort by expression size (concise lemmas first), then by name
    let sorted := candidates.qsort fun (c₁, _, sz₁) (c₂, _, sz₂) =>
      if sz₁ != sz₂ then sz₁ < sz₂ else Name.lt c₁.name c₂.name

    let totalCount := sorted.size
    let sliced := sorted.extract 0 cfg.maxResults
    let mut hitsJson : Array Json := #[]
    for (ci, modName, _) in sliced do
      let tyStr ← ppConstantType ci
      let mut fields : List (String × Json) := [
        ("name", .str ci.name.toString),
        ("module", .str modName),
        ("kind", .str (constantKind ci)),
        ("type", .str tyStr)
      ]
      if cfg.includeDoc then
        let doc? ← findDocString? env ci.name
        let docJson : Json := match doc? with
          | some d => Json.str d.trimAscii.toString
          | none   => Json.null
        fields := fields ++ [("doc", docJson)]
      hitsJson := hitsJson.push (Json.mkObj fields)

    return Json.mkObj [
      ("count", .num totalCount),
      ("shown", .num hitsJson.size),
      ("hits", .arr hitsJson)
    ]
  ).run' |>.toIO coreCtx coreState

  IO.println (jsonOut.1.pretty)
  return 0

/-- Configuration for the `goals` subcommand. -/
structure GoalsConfig where
  code?      : Option String := none
  file?      : Option String := none
  readStdin  : Bool := false
  modules    : Array Name := #[]
  allTactics : Bool := false
  tryTactics : Array String := #[]

/-- Runs the `goals` subcommand and prints structured JSON to stdout. -/
unsafe def runGoals (cfg : GoalsConfig) : IO UInt32 := do
  let (source, fileName) ←
    if let some code := cfg.code? then
      pure (code, "<snippet>")
    else if let some path := cfg.file? then
      pure (← IO.FS.readFile path, path)
    else if cfg.readStdin then
      pure (← (← IO.getStdin).readToEnd, "<stdin>")
    else
      throw <| IO.userError
        "goals requires one of `--code <snippet>`, `--file <path>`, or `--stdin`"

  let (_, fileMap, messages, trees) ← elaborateSource source fileName cfg.modules

  -- 1. Extract all diagnostics from `MessageLog`
  let mut diagsJson : Array Json := #[]
  let mut hasErrors := false
  for msg in messages.toList do
    let sev := match msg.severity with
      | .error       => "error"
      | .warning     => "warning"
      | .information => "info"
    if msg.severity == .error then
      hasErrors := true
    let startLine := msg.pos.line
    let startCol := msg.pos.column + 1
    let (endLine, endCol) := match msg.endPos with
      | some ep => (ep.line, ep.column + 1)
      | none    => (startLine, startCol)
    let text ← msg.data.toString
    diagsJson := diagsJson.push <| Json.mkObj [
      ("severity", .str sev),
      ("startLine", .num startLine),
      ("startCol", .num startCol),
      ("endLine", .num endLine),
      ("endCol", .num endCol),
      ("message", .str text.trimAscii.toString)
    ]

  -- 2. Traverse InfoTrees to collect tactic steps and `sorry` holes
  let mut allSteps : Array ExtractedStep := #[]
  for tree in trees do
    let steps ← collectInfoTreeSteps fileMap tree
    allSteps := allSteps ++ steps

  -- 3. Identify unsolved proof obligations:
  --    (a) Outer `tacticSorry` holes (preferring `Parser.Tactic.tacticSorry`
  --        over macro-expanded child nodes at the same span so `mctxBefore`
  --        captures the pre-sorry tactic goal and metavariable coupling),
  --    (b) Other tactic `sorry` holes,
  --    (c) Standalone term-mode `sorry` holes outside tactic blocks, and
  --    (d) Incomplete `by` blocks whose `goalsAfter` remain non-empty.
  let mut unsolvedSites : Array ExtractedStep := #[]
  for step in allSteps do
    if step.kind == "Lean.Parser.Tactic.tacticSorry" &&
        !step.goalsBefore.isEmpty then
      unless unsolvedSites.any (fun s =>
          s.startPos == step.startPos && s.endPos == step.endPos) do
        unsolvedSites := unsolvedSites.push step

  for step in allSteps do
    if step.tacticInfo?.isSome && step.syntaxText == "sorry" &&
        !step.goalsBefore.isEmpty then
      unless unsolvedSites.any (fun s =>
          s.startPos == step.startPos && s.endPos == step.endPos) do
        unsolvedSites := unsolvedSites.push step

  for step in allSteps do
    if step.tacticInfo?.isNone && step.syntaxText == "sorry" &&
        !step.goalsBefore.isEmpty then
      unless unsolvedSites.any (fun s =>
          s.startPos == step.startPos && s.endPos == step.endPos) do
        unsolvedSites := unsolvedSites.push step

  for step in allSteps do
    if step.kind == "Lean.Parser.Term.byTactic" && !step.goalsAfter.isEmpty then
      unless unsolvedSites.any (fun s =>
          s.startPos == step.startPos && s.endPos == step.endPos) do
        unsolvedSites := unsolvedSites.push step

  let serializeStep (s : ExtractedStep) : Json :=
    Json.mkObj [
      ("kind", .str s.kind),
      ("syntax", .str s.syntaxText),
      ("span", s.span),
      ("goalsBefore", .arr s.goalsBefore),
      ("goalsAfter", .arr s.goalsAfter)
    ]

  -- 4. Optionally run `--try-tactic` candidates on the first unsolved site
  let mut tacticTrials : Array Json := #[]
  if !cfg.tryTactics.isEmpty then
    if let some firstSite := unsolvedSites[0]? then
      for tac in cfg.tryTactics do
        let res ← runCandidateTactic firstSite tac
        tacticTrials := tacticTrials.push res

  let mut fields : List (String × Json) := [
    ("file", .str fileName),
    ("hasErrors", .bool hasErrors),
    ("unsolvedSiteCount", .num unsolvedSites.size),
    ("unsolvedSites", .arr (unsolvedSites.map serializeStep)),
    ("diagnostics", .arr diagsJson)
  ]
  if cfg.allTactics then
    fields := fields ++ [("allTacticSteps", .arr (allSteps.map serializeStep))]
  if !tacticTrials.isEmpty then
    fields := fields ++ [("tacticTrials", .arr tacticTrials)]

  IO.println (Json.mkObj fields).pretty
  return 0

/-!
## CLI Argument Parsing
-/

def usage : String :=
"Usage:
  lean --run anneal_harness.lean search [OPTIONS]
  lean --run anneal_harness.lean goals  [OPTIONS]

Subcommand `search`:
  --module <Mod>        Import module (repeatable; defaults to Init, Std)
  --path <Dir>          Add directory to LEAN_PATH for .olean lookup
  --file <Path>         Elaborate local .lean file before searching
  --code <Snippet>      Elaborate inline Lean snippet before searching
  --name <Substr>       Case-insensitive declaration name substring filter
  --mod-prefix <Pref>   Filter by defining module prefix (e.g. Init.Data.BitVec)
  --const <Name>        Require constant <Name> to appear in declaration type
  --pat <Pattern>       Match type pattern anywhere in type (e.g. '?a -> ?b')
  --concl <Pattern>     Match conclusion pattern up to hyp permutation
  --max <N>             Maximum results to return (default: 25)
  --doc                 Include docstrings in JSON output

Subcommand `goals`:
  --code <Snippet>      Inline Lean 4 code snippet to elaborate
  --file <Path>         Path to Lean 4 file to elaborate
  --stdin               Read Lean 4 code from stdin
  --module <Mod>        Additional module to import
  --path <Dir>          Add directory to LEAN_PATH for .olean lookup
  --all-tactics         Include every intermediate InfoTree tactic step
  --try-tactic <Tac>    Try <Tac> on the first unsolved goal site (repeatable)"

partial def parseSearchArgs (args : List String) (cfg : SearchConfig)
    (customMods : Bool) (extraPaths : List System.FilePath) :
    IO (SearchConfig × List System.FilePath) := do
  match args with
  | [] => pure (cfg, extraPaths.reverse)
  | "--module" :: m :: rest =>
    let mods := if customMods then cfg.modules.push m.toName else #[m.toName]
    parseSearchArgs rest { cfg with modules := mods } true extraPaths
  | "--path" :: p :: rest =>
    parseSearchArgs rest cfg customMods (System.FilePath.mk p :: extraPaths)
  | "--file" :: f :: rest =>
    parseSearchArgs rest { cfg with extraFiles := cfg.extraFiles.push f }
      customMods extraPaths
  | "--code" :: c :: rest =>
    parseSearchArgs rest { cfg with extraCode := some c } customMods extraPaths
  | "--name" :: s :: rest =>
    parseSearchArgs rest { cfg with nameSubstrs := cfg.nameSubstrs.push s }
      customMods extraPaths
  | "--mod-prefix" :: p :: rest =>
    parseSearchArgs rest { cfg with modPrefixes := cfg.modPrefixes.push p }
      customMods extraPaths
  | "--const" :: c :: rest =>
    parseSearchArgs rest { cfg with reqConsts := cfg.reqConsts.push c.toName }
      customMods extraPaths
  | "--pat" :: p :: rest =>
    parseSearchArgs rest { cfg with subPats := cfg.subPats.push p }
      customMods extraPaths
  | "--concl" :: p :: rest =>
    parseSearchArgs rest { cfg with conclPats := cfg.conclPats.push p }
      customMods extraPaths
  | "--max" :: n :: rest =>
    let maxN := n.toNat?.getD 25
    parseSearchArgs rest { cfg with maxResults := maxN } customMods extraPaths
  | "--doc" :: rest =>
    parseSearchArgs rest { cfg with includeDoc := true } customMods extraPaths
  | flag :: _ =>
    throw <| IO.userError s!"Unknown or incomplete search option: {flag}\n\n{usage}"

partial def parseGoalsArgs (args : List String) (cfg : GoalsConfig)
    (extraPaths : List System.FilePath) :
    IO (GoalsConfig × List System.FilePath) := do
  match args with
  | [] => pure (cfg, extraPaths.reverse)
  | "--code" :: c :: rest =>
    parseGoalsArgs rest { cfg with code? := some c } extraPaths
  | "--file" :: f :: rest =>
    parseGoalsArgs rest { cfg with file? := some f } extraPaths
  | "--stdin" :: rest =>
    parseGoalsArgs rest { cfg with readStdin := true } extraPaths
  | "--module" :: m :: rest =>
    parseGoalsArgs rest { cfg with modules := cfg.modules.push m.toName }
      extraPaths
  | "--path" :: p :: rest =>
    parseGoalsArgs rest cfg (System.FilePath.mk p :: extraPaths)
  | "--all-tactics" :: rest =>
    parseGoalsArgs rest { cfg with allTactics := true } extraPaths
  | "--try-tactic" :: t :: rest =>
    parseGoalsArgs rest { cfg with tryTactics := cfg.tryTactics.push t }
      extraPaths
  | flag :: _ =>
    throw <| IO.userError s!"Unknown or incomplete goals option: {flag}\n\n{usage}"

/-- Configures Lean's `.olean` search path from the running `lean` binary's
sysroot, `LEAN_PATH`, and any explicit `--path` flags. -/
def setupSearchPath (extraPaths : List System.FilePath) : IO Unit := do
  let appPath ← IO.appPath
  let sysroot ← Lean.findSysroot appPath.toString
  Lean.initSearchPath sysroot extraPaths

/-!
## Part 3: Kernel-Checked Specifications of Pure Harness Primitives
-/

/-- A metavariable `HeadIndex` on the left matches every candidate head. -/
theorem canMatchHead_mvar_left (m : MVarId) (hi : HeadIndex) :
    canMatchHead (.mvar m) hi = true := by
  rfl

/-- A metavariable `HeadIndex` on the right matches every pattern head. -/
theorem canMatchHead_mvar_right (hi : HeadIndex) (m : MVarId) :
    canMatchHead hi (.mvar m) = true := by
  cases hi <;> rfl

/-- `canMatchHead` is reflexive on structural `HeadIndex` constructors
(`.sort`, `.lam`, `.forallE`) and distinguishes distinct structural heads. -/
theorem canMatchHead_structural :
    canMatchHead .sort .sort = true ∧
    canMatchHead .lam .lam = true ∧
    canMatchHead .forallE .forallE = true ∧
    canMatchHead .sort .lam = false := by
  decide

/-- Every `Expr` has a strictly positive AST size (`0 < exprSize e`). -/
theorem exprSize_pos (e : Expr) : 0 < exprSize e := by
  cases e <;> simp [exprSize] <;> omega

/-- `exprSize` is strictly additive (+1) on applications. -/
theorem exprSize_app (f a : Expr) :
    exprSize (.app f a) = 1 + exprSize f + exprSize a := by
  rfl

/-- `exprSize` is strictly additive (+1) on dependent arrows (`forallE`). -/
theorem exprSize_forallE (n : Name) (d b : Expr) (bi : BinderInfo) :
    exprSize (.forallE n d b bi) = 1 + exprSize d + exprSize b := by
  rfl

/-- Compiler-generated `.recOn` recursors are filtered out by
`isInternalOrBlacklisted`. -/
theorem isInternalOrBlacklisted_recOn (p : Name) :
    isInternalOrBlacklisted (.str p "recOn") = true := by
  simp [isInternalOrBlacklisted]

/-- Compiler-generated `.brecOn` course-of-values recursors are filtered out by
`isInternalOrBlacklisted`. -/
theorem isInternalOrBlacklisted_brecOn (p : Name) :
    isInternalOrBlacklisted (.str p "brecOn") = true := by
  simp [isInternalOrBlacklisted]

/-- Anonymous declaration names are filtered out by
`isInternalOrBlacklisted`. -/
theorem isInternalOrBlacklisted_anonymous :
    isInternalOrBlacklisted .anonymous = true := by
  rfl

end AnnealHarness

unsafe def main (args : List String) : IO UInt32 := do
  try
    match args with
    | [] | ["--help"] | ["-h"] | ["help"] =>
      IO.println AnnealHarness.usage
      return 0
    | "search" :: rest =>
      let (cfg, extraPaths) ← AnnealHarness.parseSearchArgs rest {} false []
      AnnealHarness.setupSearchPath extraPaths
      AnnealHarness.runSearch cfg
    | "goals" :: rest =>
      let (cfg, extraPaths) ← AnnealHarness.parseGoalsArgs rest {} []
      AnnealHarness.setupSearchPath extraPaths
      AnnealHarness.runGoals cfg
    | cmd :: _ =>
      IO.eprintln s!"Unknown subcommand: {cmd}\n\n{AnnealHarness.usage}"
      return 1
  catch ex =>
    let errJson := Lean.Json.mkObj [("error", .str ex.toString)]
    IO.eprintln errJson.pretty
    return 1
