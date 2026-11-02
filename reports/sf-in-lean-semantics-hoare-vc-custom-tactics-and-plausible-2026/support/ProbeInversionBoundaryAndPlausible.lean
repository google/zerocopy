-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Lean

set_option Elab.async false

/-!
# Custom Tactic Elaboration, `TrustedBoundary` Audit, and `Plausible` Canaries

This self-contained Lean `v4.34.1` executable probe (`lean --run`) mechanizes
and verifies:

1. **Part 1 (`InversionAndAutomationProbe`):**
   - Ports `LF/CustomTactics.lean`'s `inversion` and `apply ... at ...`,
   - Demonstrates why built-in `cases` fails on computed index expressions
     (`ShiftStep (evalShift raw) out`) while `inversion` succeeds via
     `observing?` around `unifyEq?`,
   - Reproduces both failure modes of `sf-in-lean` Issue #447 and PR #449
     (`0f74845c`): right-aligned backwards `renameInaccessibles` binding
     trailing equations (`eq✝`, `heq✝`) instead of constructor fields, and
     pre-unification `givenNames` consumed by unified-away implicit fields in
     `NoStutter`,
   - Verifies `inversion_fixed` (left-aligned post-`unifyCasesEqs` renaming over
     surviving `.fvar` entries in `CasesSubgoal.fields`), and
   - Measures `Expr.numObjs` and `Kernel.check` times against `generalize +
     cases`, `apply_rules`, `solve_by_elim`, `omega`, `lia`, and `grind`.

2. **Part 2 (`BoundaryAuditProbe`):**
   - Replicates `trusted/audit/TrustedBoundary.lean` source-syntax preflight
     (`commandKinds`, `allowedAttributeNames`, `inspectSyntax`) and tests 14
     tactic/command patterns under `Init.NotationExtra` vs.
     `+Init.Omega/Grind/RCases`, including the bare `by decide` `optConfig` AST
     inspection bug (`s[1].getArgs.isEmpty` vs. `s[1][0].getArgs.isEmpty`).

3. **Part 3 (`PlausibleCanaryProbe`):**
   - Embeds the core `Plausible` (`v4.34.0`, commit
     `118aa17ee84656b8bd727fef7c458ee8c833385c`) testing engine (`Gen`,
     `Arbitrary`, `Shrinkable`, `SampleableExt`, `Testable`, `decGuardTestable`,
     `subtypeVarTestable` at priority `2000`, and `UInt8.Arbitrary`'s
     `min (← getSize) UInt8.size`), and
   - Runs 8 negative-canary and pre-proof specification-falsification benchmarks
     on Anneal-style MIR semantics (`MirBinOp.shlUnchecked`,
     `MirBinOp.subChecked`, `ValidFrame`, and `alignUpBitwise`).
-/

namespace Lean.Parser
open _root_.Lean.Parser.Tactic

syntax (name := inversion)
  "inversion " optConfig ident
  (" with " (tacticSeq)? (colGe inductionAlt)*)? : tactic

syntax (name := inversionFixed)
  "inversion_fixed " optConfig ident
  (" with " (tacticSeq)? (colGe inductionAlt)*)? : tactic

end Lean.Parser

namespace ProbeInversionBoundaryAndPlausible

/-!
## Part 1: `LF/CustomTactics.lean` (`inversion`, `inversion_fixed`, `apply`)
-/

namespace CustomTactics

open Lean Meta Elab Tactic Term
open Lean.Parser.Tactic (inductionAlt optConfig)

def _root_.Lean.MVarId.getUserName (mvarId : MVarId) : MetaM Name := do
  let decl ← mvarId.getDecl
  return decl.userName

def _root_.Lean.Name.getSuffix : Name → Name
  | .anonymous => .anonymous
  | .str _ s => .str .anonymous s
  | .num n _ => n.getSuffix

/-- Peels one `∀` binder at a time from `e` until the last peeled parameter's
    type unifies (`isDefEq`) with hypothesis type `t`. -/
def forallMetaTelescopeReducingUntilDefEq
    (e t : Expr) (kind : MetavarKind := MetavarKind.natural) :
    MetaM (Array Expr × Array BinderInfo × Expr) := do
  let (ms, bs, tp) ← forallMetaTelescopeReducing e (some 1) kind
  unless ms.size == 1 do
    if ms.size == 0 then
      throwError m!"Failed: {← ppExpr e} is not the type of a function."
    else
      throwError m!"Failed"
  let mut mvs := ms
  let mut bis := bs
  let mut out : Expr := tp
  while !(← isDefEq (← inferType mvs.toList.getLast!) t) do
    let (ms, bs, tp) ← forallMetaTelescopeReducing out (some 1) kind
    unless ms.size == 1 do
      throwError
        m!"Failed to find {← ppExpr t} as the type of a parameter of {← ppExpr e}."
    mvs := mvs ++ ms
    bis := bis ++ bs
    out := tp
  return (mvs, bis, out)

/-- Replicates `Lean.Meta.Cases` context setup (`Lean/Meta/Tactic/Cases.lean`
    L160–277) so `MVarId.inversion` runs self-contained in a single file. -/
structure LocalCasesContext where
  inductiveVal     : InductiveVal
  nminors          : Nat := inductiveVal.ctors.length
  majorDecl        : LocalDecl
  majorTypeFn      : Expr
  majorTypeArgs    : Array Expr
  majorTypeIndices : Array Expr :=
    majorTypeArgs.extract
      (majorTypeArgs.size - inductiveVal.numIndices)
      majorTypeArgs.size

def mkCasesContextLocal? (majorFVarId : FVarId) :
    MetaM (Option LocalCasesContext) := do
  let env ← getEnv
  if !env.contains `Eq || !env.contains `HEq then
    pure none
  else
    let majorDecl ← majorFVarId.getDecl
    let majorType ← whnf majorDecl.type
    majorType.withApp fun f args =>
      matchConstInduct f (fun _ => pure none) fun ival _ =>
        if args.size != ival.numIndices + ival.numParams then pure none
        else if !env.contains (Name.mkStr ival.name "casesOn") then pure none
        else return some {
          inductiveVal  := ival
          majorDecl     := majorDecl
          majorTypeFn   := f
          majorTypeArgs := args
        }

def hasIndepIndicesLocal (ctx : LocalCasesContext) : MetaM Bool := do
  if ctx.majorTypeIndices.isEmpty then
    return true
  else if ctx.majorTypeIndices.any fun idx => !idx.isFVar then
    return false
  else if ctx.majorTypeIndices.size.any fun i _ =>
      i.any fun j _ => ctx.majorTypeIndices[i] == ctx.majorTypeIndices[j] then
    return false
  else
    (← getLCtx).allM fun decl =>
      pure (decl.fvarId == ctx.majorDecl.fvarId) <||>
      pure (ctx.majorTypeIndices.any fun index =>
        decl.fvarId == index.fvarId!) <||>
      findLocalDeclDependsOn decl fun fvarId =>
        ctx.majorTypeIndices.all fun idx => idx.fvarId! != fvarId

def elimAuxIndicesLocal (s₁ : GeneralizeIndicesSubgoal)
    (s₂ : Array CasesSubgoal) : MetaM (Array CasesSubgoal) :=
  let indicesFVarIds := s₁.indicesFVarIds
  s₂.mapM fun s => do
    indicesFVarIds.foldlM (init := s) fun s indexFVarId =>
      match s.subst.get indexFVarId with
      | Expr.fvar indexFVarId' =>
        (do
          let mvarId ← s.mvarId.clear indexFVarId'
          pure { s with mvarId := mvarId, subst := s.subst.erase indexFVarId })
        <|> pure s
      | _ => pure s

def toCasesSubgoalsLocal (s : Array InductionSubgoal) (ctorNames : Array Name)
    (majorFVarId : FVarId) (us : List Level) (params : Array Expr) :
    Array CasesSubgoal :=
  s.mapIdx fun i s =>
    if _ : i < ctorNames.size then
      let ctorName := ctorNames[i]
      let ctorApp  := mkAppN (mkAppN (mkConst ctorName us) params) s.fields
      let subst := s.subst.erase majorFVarId |>.insert majorFVarId ctorApp
      { s with ctorName := ctorName, subst := subst }
    else
      { s with ctorName := none }

def inductionCasesOnLocal (mvarId : MVarId) (majorFVarId : FVarId)
    (givenNames : Array AltVarNames) (ctx : LocalCasesContext) :
    MetaM (Array CasesSubgoal) := mvarId.withContext do
  let majorType ← inferType (mkFVar majorFVarId)
  let (us, params) ← getInductiveUniverseAndParams majorType
  let casesOn := mkCasesOnName ctx.inductiveVal.name
  let ctors := ctx.inductiveVal.ctors.toArray
  let s ← mvarId.induction majorFVarId casesOn givenNames
  return toCasesSubgoalsLocal s ctors majorFVarId us params

/-- `LF/CustomTactics.lean` L92–103: wraps `unifyEq?` in `observing?` so
    unsolvable index equations (such as `evalShift raw = 0`) are retained in the
    local context rather than aborting dependent elimination. -/
partial def unifyEqs (eqs : List FVarId) (mvarId : MVarId) (subst : FVarSubst)
    (caseName? : Option Name) : MetaM (MVarId × FVarSubst) :=
  withIncRecDepth do
    match eqs with
    | [] => return (mvarId, subst)
    | eq :: eqs =>
      let some { mvarId, subst, numNewEqs } ←
          Option.join <$>
            (observing? $ unifyEq? mvarId eq subst MVarId.acyclic caseName?)
        | unifyEqs eqs mvarId subst caseName?
      let (newEqs, mvarId) ← mvarId.introN numNewEqs
      let eqs := eqs.map (Expr.fvarId! ∘ subst.get)
      unifyEqs (newEqs.toList ++ eqs) mvarId subst caseName?

def unifyCasesEqs (eqs : List FVarId) (subgoals : Array CasesSubgoal) :
    MetaM (Array CasesSubgoal) :=
  subgoals.filterMapM fun s => do
    let eqs := eqs.filterMap (Expr.fvarId? ∘ s.subst.get)
    let (mvarId, subst) ← unifyEqs eqs s.mvarId s.subst s.ctorName
    if (← mvarId.isAssignedOrDelayedAssigned) then
      return none
    else
      return some { s with
        mvarId := mvarId
        subst  := subst
        fields := s.fields.map (subst.apply ·)
      }

def casesClearMany (subgoals : Array CasesSubgoal) (fvarIds : Array FVarId) :
    MetaM (Array CasesSubgoal) :=
  subgoals.mapM fun s => do
    let fvarIds := fvarIds.filterMap (Expr.fvarId? ∘ s.subst.get)
    let mvarId ← s.mvarId.tryClearMany fvarIds
    return { s with mvarId }

/-- `LF/CustomTactics.lean` L134–160: Rocq-style forward reasoning
    `apply f at h`. -/
elab "apply " t:term " at " i:ident : tactic =>
  withSynthesize <| withMainContext do
    let f ← elabTermForApply t
    let some ldecl := (← getLCtx).findFromUserName? i.getId
      | throwErrorAt i m!"Identifier {i} not found"
    let (mvs, bis, _) ←
      forallMetaTelescopeReducingUntilDefEq (← inferType f) ldecl.type
    for (m, b) in mvs.zip bis do
      if b.isInstImplicit && !(← m.mvarId!.isAssigned) then
        try m.mvarId!.inferInstance
        catch _ => continue
    let (_, mainGoal) ← (← getMainGoal).note ldecl.userName
      (← mkAppOptM' f (mvs.pop.push ldecl.toExpr |>.map some))
    let mainGoal ← mainGoal.tryClear ldecl.fvarId
    let sideGoals ← mvs.pop.toList.filterM fun m =>
      not <$> m.mvarId!.isAssigned
    replaceMainGoal <| [mainGoal] ++ sideGoals.map (·.mvarId!)

structure InversionConfig where
  clear : Bool := false

declare_config_elab elabInversionConfig InversionConfig

def _root_.Lean.MVarId.inversion (goal : MVarId) (h : FVarId)
    (config : InversionConfig) (givenNames : Array AltVarNames := #[]) :
    TacticM (Array CasesSubgoal) := goal.withContext do
  let some ctx ← mkCasesContextLocal? h
    | throwTacticEx `inversion goal
        m!"Target {Expr.fvar h} does not belong to an inductive type"
  if ← hasIndepIndicesLocal ctx then
    let subgoals ← inductionCasesOnLocal goal h givenNames ctx
    if config.clear then
      casesClearMany subgoals #[h]
    else
      pure subgoals
  else
    let gis@⟨newGoal, _, newTarget, numEqs⟩ ← generalizeIndices goal h
    let (newEqs, newGoal) ← newGoal.introN numEqs
    let some targetEq := newEqs.back?
      | throwTacticEx `inversion newGoal "Failed to generalize target"
    let subgoals ← inductionCasesOnLocal newGoal newTarget givenNames ctx
    let subgoals ← elimAuxIndicesLocal gis subgoals
    let subgoals ← unifyCasesEqs newEqs.toList subgoals
    if config.clear then
      casesClearMany subgoals #[h, targetEq]
    else
      pure subgoals

def evalInvAlt (goals : List MVarId) (alt : TSyntax ``inductionAlt) :
    TacticM (List MVarId) :=
  match alt with
  | `(inductionAlt| | $tag:ident $vars* => $tactics:tacticSeq) => do
    if let some goal ←
        goals.findM? (matchTag tag.getId <$> ·.getUserName) then
      return [← trySolveGoal alt vars tactics goal]
    else
      throwError m!"Invalid alternative name `{tag.getId}`"
  | `(inductionAlt| | _ $vars* => $tactics:tacticSeq) => do
    if !goals.isEmpty then
      goals.mapM (trySolveGoal alt vars tactics)
    else
      throwErrorAt alt "Invalid wildcard alternative"
  | _ => throwErrorAt alt "Could not parse inversion alternative"
where
  matchTag tag name : Bool :=
    tag == name || tag.isPrefixOf name || tag.isSuffixOf name
  trySolveGoal alt vars tactics goal : TacticM MVarId := do
    let vars := vars.map fun var => ⟨mkNode ``binderIdent #[var.raw]⟩
    let renamedGoal ← withRef alt.raw[1][0] $ renameInaccessibles goal vars
    let savedGoals ← getGoals
    try
      setGoals [renamedGoal]
      withTacticInfoContext (mkNullNode #[alt.raw[0], alt.raw[1][0]]) do
        evalTactic tactics
        let goals ← getUnsolvedGoals
        unless goals.isEmpty do
          reportUnsolvedGoals goals
      return goal
    finally
      setGoals savedGoals

elab_rules : tactic
  | `(tactic| inversion $config $h:ident $[with $[$tactics?:tacticSeq]? $[$alts?:inductionAlt]*]?) => do
    let casesSubgoals ←
      (← getMainGoal).inversion (← getFVarId h) (← elabInversionConfig config)
    let mut goals ← casesSubgoals.toList.mapM fun subgoal => do
      if let some name := subgoal.ctorName then
        subgoal.mvarId.setUserName name.getSuffix
      return subgoal.mvarId
    if let some tactics := tactics?.join then
      let subgoals ← goals.mapM (evalTacticAt tactics)
      goals ← subgoals.flatten.filterM (not <$> ·.isAssignedOrDelayedAssigned)
    if let some alts := alts? then
      let expandedAlts ← Array.flatten <$> alts.mapM fun (alt : TSyntax ``inductionAlt) =>
        match alt with
        | `(inductionAlt| $lhs* => $_:tacticSeq) =>
          pure <| lhs.map fun lhs => ⟨alt.raw.setArg 0 (mkNullNode #[lhs.raw])⟩
        | stx => throwErrorAt stx "Could not parse inversion alternatives"
      for alt in expandedAlts do
        let solvedGoals ← evalInvAlt goals alt
        goals := goals.removeAll solvedGoals
      unless goals.isEmpty do
        reportUnsolvedGoals goals
    replaceMainGoal goals

/-- Left-aligned post-`unifyCasesEqs` renamer that fixes both `sf-in-lean` Issue
    #447 and the unified-away-implicits bug in PR #449 (`0f74845c`):
    1. Supports both `| tag vars* =>` and `| @tag vars* =>`.
    2. Instead of calling `renameInaccessibles` (which walks `lctx.decls`
       backwards from the end and binds user names to trailing `heq✝`/`eq✝`
       equations when `vars.size < total_inaccessibles`), and instead of passing
       `givenNames` to `inductionCasesOn` before `unifyCasesEqs` (which consumes
       user names on implicit constructor fields that are substituted away by
       `unifyCasesEqs`), it collects inaccessible hypotheses starting from the
       first surviving constructor `.fvar` in `CasesSubgoal.fields` in forward
       order. -/
def renameInversionFieldsForward (subgoal : CasesSubgoal) (explicit : Bool)
    (hs : TSyntaxArray ``binderIdent) : TacticM MVarId := do
  if hs.isEmpty then return subgoal.mvarId
  let mvarDecl ← subgoal.mvarId.getDecl
  let mut lctx := mvarDecl.lctx
  let survivingFieldFVars := subgoal.fields.filterMap (·.fvarId?)
  let ctorImplicitFVars : Std.HashSet FVarId ← do
    if explicit then pure {}
    else
      let env ← getEnv
      match subgoal.ctorName.bind env.find? with
      | some (.ctorInfo cinfo) =>
        let (_, bis, _) ← forallMetaTelescopeReducing cinfo.type
        let fieldBis := bis.extract cinfo.numParams bis.size
        let mut set : Std.HashSet FVarId := {}
        for (fExpr, bi) in subgoal.fields.zip fieldBis do
          if !bi.isExplicit then
            if let some fid := fExpr.fvarId? then
              set := set.insert fid
        pure set
      | _ => pure {}
  let firstIdx? :=
    survivingFieldFVars.filterMap (fun fid => (lctx.find? fid).map (·.index))
      |>.min?
  let mut candidateFVars : Array FVarId := #[]
  for decl in lctx.decls do
    if let some decl := decl then
      let afterStart := match firstIdx? with
        | some startIdx => decl.index >= startIdx
        | none => true
      if afterStart && decl.userName.hasMacroScopes &&
          !ctorImplicitFVars.contains decl.fvarId then
        candidateFVars := candidateFVars.push decl.fvarId
  let mut idx := 0
  for h in hs do
    if h1 : idx < candidateFVars.size then
      let fvarId := candidateFVars[idx]
      if let `(binderIdent| $name:ident) := h then
        lctx := lctx.setUserName fvarId name.getId
    idx := idx + 1
  let mvarNew ←
    mkFreshExprMVarAt lctx mvarDecl.localInstances mvarDecl.type
      .syntheticOpaque mvarDecl.userName
  subgoal.mvarId.assign mvarNew
  return mvarNew.mvarId!

def evalInvAltFixed (subgoals : List CasesSubgoal)
    (alt : TSyntax ``inductionAlt) : TacticM (List MVarId) := do
  let (explicit, tagOpt, vars, tactics) ← match alt with
    | `(inductionAlt| | $tag:ident $vars* => $tactics:tacticSeq) =>
      pure (false, some tag.getId, vars, tactics)
    | `(inductionAlt| | @$tag:ident $vars* => $tactics:tacticSeq) =>
      pure (true, some tag.getId, vars, tactics)
    | `(inductionAlt| | _ $vars* => $tactics:tacticSeq) =>
      pure (false, none, vars, tactics)
    | _ => throwErrorAt alt "Could not parse inversion alternative"
  match tagOpt with
  | some tagId =>
    if let some sg ←
        subgoals.findM? (fun s => matchTag tagId <$> s.mvarId.getUserName) then
      return [← trySolveSubgoal alt explicit vars tactics sg]
    else
      throwError m!"Invalid alternative name `{tagId}`"
  | none =>
    subgoals.mapM (trySolveSubgoal alt explicit vars tactics)
where
  matchTag tag name : Bool :=
    tag == name || tag.isPrefixOf name || tag.isSuffixOf name
  trySolveSubgoal alt explicit vars tactics sg : TacticM MVarId := do
    let vars := vars.map fun var => ⟨mkNode ``binderIdent #[var.raw]⟩
    let renamedGoal ← renameInversionFieldsForward sg explicit vars
    let savedGoals ← getGoals
    try
      setGoals [renamedGoal]
      withTacticInfoContext (mkNullNode #[alt.raw[0], alt.raw[1][0]]) do
        evalTactic tactics
        let goals ← getUnsolvedGoals
        unless goals.isEmpty do
          reportUnsolvedGoals goals
      return sg.mvarId
    finally
      setGoals savedGoals

elab_rules : tactic
  | `(tactic| inversion_fixed $config $h:ident $[with $[$tactics?:tacticSeq]? $[$alts?:inductionAlt]*]?) => do
    let casesSubgoals ←
      (← getMainGoal).inversion (← getFVarId h) (← elabInversionConfig config)
    let subgoals := casesSubgoals.toList
    for sg in subgoals do
      if let some name := sg.ctorName then
        sg.mvarId.setUserName name.getSuffix
    let mut goals := subgoals.map (·.mvarId)
    if let some alts := alts? then
      let expandedAlts ← Array.flatten <$> alts.mapM fun (alt : TSyntax ``inductionAlt) =>
        match alt with
        | `(inductionAlt| $lhs* => $_:tacticSeq) =>
          pure <| lhs.map fun lhs => ⟨alt.raw.setArg 0 (mkNullNode #[lhs.raw])⟩
        | stx => throwErrorAt stx "Could not parse inversion alternatives"
      for alt in expandedAlts do
        let activeSubgoals := subgoals.filter fun s => goals.contains s.mvarId
        let solvedGoals ← evalInvAltFixed activeSubgoals alt
        goals := goals.removeAll solvedGoals
      unless goals.isEmpty do
        reportUnsolvedGoals goals
    replaceMainGoal goals

end CustomTactics

namespace InversionProbe

open Lean CustomTactics

/-- Indexed operational semantics step relation where the input index is matched
    against constructor shapes `0` and `k + 1`. -/
inductive ShiftStep : Nat → Nat → Prop where
  | zeroShift (x : Nat) : ShiftStep 0 x
  | nonZeroShift {k : Nat} (hk : 0 < k) (x : Nat) : ShiftStep (k + 1) (x * 2)

/- 1. Built-in `cases h` fails when the index is a computed expression
   `evalShift raw` and the constructor indices are `0` and `k + 1`:
   `Lean.Meta.Cases.unifyEqs` throws `"Dependent elimination failed"`. -/
/--
error: Dependent elimination failed: Failed to solve equation
  evalShift raw = 0
-/
#guard_msgs in
theorem shiftStep_cases_fails (evalShift : Nat → Nat) (raw out : Nat)
    (h : ShiftStep (evalShift raw) out)
    (hpos : evalShift raw = 0 → False) : ∃ y, out = y * 2 := by
  cases h

/-- 2. `LF/CustomTactics.lean`'s `inversion` succeeds on the exact same goal
    because `unifyEqs` wraps `unifyEq?` in `observing?`, retaining the unsolved
    index equation `evalShift raw = 0` in the `zeroShift` branch. -/
theorem shiftStep_inversion_succeeds (evalShift : Nat → Nat) (raw out : Nat)
    (h : ShiftStep (evalShift raw) out)
    (hpos : evalShift raw = 0 → False) : ∃ y, out = y * 2 := by
  inversion +clear h with
  | zeroShift heq =>
    exfalso
    exact hpos heq
  | nonZeroShift k hk x heq =>
    exact ⟨x, rfl⟩

/-- 3. Standard Lean 4 workaround accepted by `TrustedBoundary.lean`:
    `generalize hexp : evalShift raw = idx at h` followed by `cases h`. -/
theorem shiftStep_cases_generalize_succeeds (evalShift : Nat → Nat)
    (raw out : Nat) (h : ShiftStep (evalShift raw) out)
    (hpos : evalShift raw = 0 → False) : ∃ y, out = y * 2 := by
  generalize hexp : evalShift raw = idx at h
  cases h with
  | zeroShift =>
    exfalso
    exact hpos hexp
  | nonZeroShift hk x =>
    exact ⟨x, rfl⟩

/-- Inductive family with implicit parameters (`{x y : Nat}`, `{l : List Nat}`)
    matching `NoStutter` from `LF/IndProp.lean` and PR #449. -/
inductive NoStutter : List Nat → Prop where
  | nil : NoStutter []
  | singleton (x : Nat) : NoStutter [x]
  | cons {x y : Nat} {l : List Nat} (hneq : x ≠ y) (h : NoStutter (y :: l)) :
      NoStutter (x :: y :: l)

/-- Indexed inductive with an un-unified implicit parameter `{m : Nat}` and a
    function application index `f m`, matching `Wec` in
    `LF/CustomTactics.lean:396`. -/
inductive IndexedWec (α : Type) : Nat → Type where
  | nil : IndexedWec α 0
  | cons {m : Nat} (f : Nat → Nat) (hd : α) (tl : IndexedWec α m) :
      IndexedWec α (f m)

/- Anomaly 1 (`sf-in-lean` `main` `13e9425b`):
   `| @cons ...` is rejected because `evalInvAlt` only matches
   `| $tag:ident $vars* =>`. -/
/--
error: Could not parse inversion alternative
-/
#guard_msgs in
theorem issue447_at_syntax_rejected (h : NoStutter [3, 1, 1, 4]) : False := by
  inversion +clear h with
  | @cons x y l hneq h => contradiction

/-- Anomaly 2 (`sf-in-lean` `main` `13e9425b`):
    Because `renameInaccessibles` walks `lctx.decls` backwards from the end,
    when unsolved trailing equations (`eq✝ : n + 1 = f✝ m✝`, `heq✝ : w ≍ ...`)
    remain at the end of `lctx` and the user supplies only 2 names
    `| cons a b =>`, `a` and `b` bind to the trailing equations instead of the
    first 2 constructor fields. -/
theorem issue447_reverse_renaming_binds_trailing_eqs
    (n : Nat) (w : IndexedWec Bool (n + 1)) : True := by
  inversion w with
  | cons a b =>
    guard_hyp a : w ≍ IndexedWec.cons _ _ _
    guard_hyp b : n + 1 = _
    trivial

/-- Verification of `inversion_fixed`:
    1. Forward post-`unifyCasesEqs` renaming on `NoStutter [3, 1, 1, 4]` binds
       `hneq` and `h1` to the surviving explicit fields without consuming names
       on unified-away `{x y l}`.
    2. `| cons f hd =>` and `| @cons m f hd tl =>` on `IndexedWec` bind
       left-to-right to constructor fields rather than trailing equations. -/
theorem issue447_fixed_noStutter (h : NoStutter [3, 1, 1, 4]) : False := by
  inversion_fixed +clear h with
  | cons hneq h1 =>
    inversion_fixed +clear h1 with
    | @cons hneq2 h2 =>
      exact hneq2 rfl

theorem issue447_fixed_indexedWec_forward_binding
    (n : Nat) (w : IndexedWec Bool (n + 1)) : True := by
  inversion_fixed w with
  | cons f hd =>
    guard_hyp f : Nat → Nat
    guard_hyp hd : Bool
    trivial

theorem issue447_fixed_indexedWec_at_syntax
    (n : Nat) (w : IndexedWec Bool (n + 1)) : True := by
  inversion_fixed w with
  | @cons m f hd tl =>
    guard_hyp m : Nat
    guard_hyp f : Nat → Nat
    guard_hyp hd : Bool
    guard_hyp tl : IndexedWec Bool m
    trivial

/-- Forward reasoning via `apply ... at ...`
    (`LF/CustomTactics.lean:134–160`). -/
theorem apply_at_demo (P Q R : Nat → Prop)
    (hstep : ∀ n, Q n → P n → R n) (hp : P 7) (hq : Q 7) : R 7 := by
  apply hstep at hp
  · exact hp
  · exact hq

inductive EvenInd : Nat → Prop where
  | zero : EvenInd 0
  | addTwo {n : Nat} : EvenInd n → EvenInd (n + 2)

theorem even_zero : EvenInd 0 := EvenInd.zero
theorem even_addTwo {n : Nat} (h : EvenInd n) : EvenInd (n + 2) :=
  EvenInd.addTwo h

theorem even_8_apply_rules : EvenInd 8 := by
  apply_rules [even_zero, even_addTwo]

theorem even_8_solve_by_elim : EvenInd 8 := by
  solve_by_elim [even_zero, even_addTwo]

theorem arith_bound_omega (a b : Nat) (h1 : a < 100) (h2 : b < 100) :
    a + b < 200 := by
  omega

theorem arith_bound_lia (a b : Nat) (h1 : a < 100) (h2 : b < 100) :
    a + b < 200 := by
  lia

theorem arith_bound_grind (a b : Nat) (h1 : a < 100) (h2 : b < 100) :
    a + b < 200 := by
  grind

def measureProofLine (env : Environment) (declName : Name) : IO String := do
  let some (.thmInfo info) := env.find? declName
    | throw <| IO.userError s!"theorem {declName} not found"
  let dagNodes ← (ShareCommon.shareCommon info.value).numObjs
  let t0 ← IO.monoNanosNow
  let lctx : LocalContext := {}
  match Kernel.check env lctx info.value with
  | .ok _ => pure ()
  | .error _ => throw <| IO.userError s!"kernel check failed on {declName}"
  let t1 ← IO.monoNanosNow
  return s!"  {declName}: dagNodes={dagNodes}, kernelCheckNs={t1 - t0}"

end InversionProbe

/-!
## Part 2: `TrustedBoundary.lean` Preflight & Foundation Elaboration
-/

namespace BoundaryAuditProbe

open Lean Elab

def commandKinds : List SyntaxNodeKind :=
  [ ``Parser.Command.declaration, ``Parser.Command.namespace,
    ``Parser.Command.section, ``Parser.Command.end,
    ``Parser.Command.universe, ``Parser.Command.variable,
    ``Parser.Command.open, ``Parser.Command.export,
    ``Parser.Command.mutual, ``Parser.Command.in,
    ``Parser.Command.attribute, ``Parser.Command.moduleDoc ]

def openOnlyKinds : List SyntaxNodeKind :=
  [ ``Parser.Command.openOnly, ``Parser.Command.openSimple,
    ``Parser.Command.openHiding, ``Parser.Command.openRenaming ]

def allowedAttributeNames : List Name :=
  [`simp, `instance, `reducible, `semireducible, `irreducible]

partial def inspectSyntax (fixDecideOptConfig : Bool) (moduleName : Name)
    (stx : Syntax) : Except String Unit := do
  match stx with
  | .atom _ val =>
    if ["set_option", "rfl'", "unhygienic", "decide!", "bv_decide",
        "native_decide", "include_str", "by_elab", "run_tac",
        "with_decl_name%", "private_decl%", "decl_name%", "partial_fixpoint",
        "coinductive_fixpoint", "inductive_fixpoint"].contains val then
      throw s!"forbidden keyword '{val}' in {moduleName}"
  | .ident _ _ val _ =>
    if val == `Lean.ofReduceBool || val == `Lean.ofReduceNat then
      throw s!"forbidden kernel reduction primitive {val} in {moduleName}"
  | .node _ kind args =>
    if [ `Lean.Parser.Command.set_option, `Lean.Parser.Term.set_option,
         `Lean.Parser.Tactic.set_option, `Lean.Parser.Tactic.Grind.set_option,
         `Lean.byElab, `Lean.includeStr, `Lean.Parser.Tactic.runTac,
         `Lean.Parser.Tactic.nativeDecide, `Lean.Parser.Tactic.decideBang,
         `Lean.Parser.Tactic.bvDecide, `Lean.Parser.Tactic.rfl',
         `Lean.Parser.Tactic.unhygienic, `Lean.Parser.Term.sleep,
         `Lean.Parser.Term.dbgTrace, `Lean.Parser.Term.idbg,
         `Lean.Parser.Term.doIdbg, `Lean.Parser.Term.doDbgTrace,
         `Lean.Parser.Term.withDeclName, `Lean.Parser.Term.privateDecl,
         `Lean.Parser.Term.declName, `Lean.Parser.Command.partialFixpoint,
         `Lean.Parser.Command.coinductiveFixpoint,
         `Lean.Parser.Command.inductiveFixpoint ].contains kind then
      throw s!"forbidden syntax kind {kind} in {moduleName}"
    if kind == ``Parser.Tactic.decide then
      let cfg := args.getD 1 .missing
      let hasCfg :=
        if fixDecideOptConfig then !cfg[0].getArgs.isEmpty
        else !cfg.getArgs.isEmpty
      if hasCfg then
        throw
          s!"forbidden decide configuration '{cfg.reprint.getD ""}' in {moduleName}"
    for arg in args do
      inspectSyntax fixDecideOptConfig moduleName arg
  | .missing => pure ()

def atomWithin (s : Syntax) (value : String) : Bool :=
  (s.find? fun x => x.isAtom && x.getAtomVal == value).isSome

def inspectAttrInstance (moduleName : Name) (elem : Syntax) :
    Except String Unit := do
  if elem.getKind != `Lean.Parser.Term.attrInstance then
    throw s!"unsupported attribute syntax {elem.getKind} in {moduleName}"
  let attrKind := elem.getArg 0
  if atomWithin attrKind "scoped" || atomWithin attrKind "local" then
    throw s!"scoped or local attribute modifier is not allowed in {moduleName}"
  let attr := elem.getArg 1
  let k := attr.getKind
  if k == `Lean.Parser.Attr.simple then
    let attrName := (attr.getArg 0).getId
    let attrArgs := attr.getArg 1
    if allowedAttributeNames.contains attrName then
      if !attrArgs.isNone && !attrArgs.getArgs.isEmpty then
        throw s!"arguments on attribute {attrName} are not allowed in {moduleName}"
    else
      throw s!"unsupported attribute {attrName} in {moduleName}"
  else
    throw s!"unsupported attribute kind {k} in {moduleName}"

def inspectDeclModifiers (moduleName : Name) (mods : Syntax) :
    Except String Unit := do
  let attrsNode := mods.getArg 1
  if let some inner := attrsNode.getArgs[0]? then
    for elem in (inner.getArg 1).getArgs do
      if elem.getKind == `Lean.Parser.Term.attrInstance then
        inspectAttrInstance moduleName elem
  for idx in [2, 3, 4, 5] do
    let m := mods.getArg idx
    if !m.isNone then
      throw s!"forbidden declaration modifier '{m.reprint.getD ""}' in {moduleName}"

partial def inspectCommand (fixDecideOptConfig : Bool) (moduleName : Name)
    (stx : Syntax) : Except String Unit := do
  let kind := stx.getKind
  if !commandKinds.contains kind then
    throw s!"unsupported command {kind} in {moduleName}"
  inspectSyntax fixDecideOptConfig moduleName stx
  if kind == ``Parser.Command.open then
    let directive := stx.getArg 1
    if !openOnlyKinds.contains directive.getKind then
      throw s!"forbidden open directive {directive.getKind} in {moduleName}"
  else if kind == ``Parser.Command.attribute then
    for idx in [0, 1] do
      let mod := stx.getArg idx
      if !mod.isNone then
        throw s!"unsupported attribute command modifier in {moduleName}"
    for elem in (stx.getArg 3).getArgs do
      if elem.getKind == `Lean.Parser.Term.attrInstance then
        inspectAttrInstance moduleName elem
  else if kind == ``Parser.Command.in then
    inspectCommand fixDecideOptConfig moduleName (stx.getArg 0)
    inspectCommand fixDecideOptConfig moduleName (stx.getArg 2)
  else if kind == ``Parser.Command.mutual then
    for elem in (stx.getArg 1).getArgs do
      inspectCommand fixDecideOptConfig moduleName elem
  else if kind == ``Parser.Command.declaration then
    let mods := stx.getArg 0
    let decl := stx.getArg 1
    inspectDeclModifiers moduleName mods
    let declKind := decl.getKind
    if ![ ``Parser.Command.abbrev, ``Parser.Command.definition,
          ``Parser.Command.theorem, ``Parser.Command.opaque,
          ``Parser.Command.instance, ``Parser.Command.inductive,
          ``Parser.Command.classInductive,
          ``Parser.Command.structure ].contains declKind then
      throw s!"forbidden declaration kind {declKind} in {moduleName}"

def checkPreflightSnippet (fixDecideOptConfig : Bool) (parserEnv : Environment)
    (moduleName : Name) (source : String) : IO (Except String Unit) := do
  let ictx := Parser.mkInputContext source "<snippet>"
  let (header, pstate, messages) ← Parser.parseHeader ictx
  if messages.hasErrors then
    let errs ← messages.toList.mapM (·.toString)
    return .error s!"header parser error: {String.intercalate "; " errs}"
  let headerStx := header.raw
  if headerStx.getKind != ``Parser.Module.header ||
      (headerStx.getArg 1).isNone then
    return .error "missing `prelude` in module header"
  let pmctx : Parser.ParserModuleContext := { env := parserEnv, options := {} }
  let mut pstate := pstate
  let mut messages := messages
  while !ictx.atEnd pstate.pos do
    let (stx, pstate', messages') :=
      Parser.parseCommand ictx pmctx pstate messages
    pstate := pstate'
    messages := messages'
    if messages.hasErrors then
      let errs ← messages.toList.mapM (·.toString)
      return .error s!"command parser error: {String.intercalate "; " errs}"
    if Parser.isTerminalCommand stx then break
    match inspectCommand fixDecideOptConfig moduleName stx with
    | .ok () => pure ()
    | .error e => return .error e
  return .ok ()

def checkElaboration (baseEnv : Environment) (source : String) :
    IO (Except String Unit) := do
  let ictx := Parser.mkInputContext source "<snippet>"
  let (_, pstate, messages) ← Parser.parseHeader ictx
  if messages.hasErrors then
    let errs ← messages.toList.mapM (·.toString)
    return .error s!"header error: {String.intercalate "; " errs}"
  let commandState := Command.mkState baseEnv messages {}
  let s ← IO.processCommands ictx pstate commandState
  if s.commandState.messages.hasErrors then
    let errs ←
      s.commandState.messages.toList.filter (·.severity == .error)
        |>.mapM (·.toString)
    return .error (String.intercalate "; " errs |>.trimAscii.toString)
  return .ok ()

structure SnippetCase where
  label : String
  source : String

def testCases : Array SnippetCase := #[
  { label := "1. Custom `syntax` + `elab` (`inversion` / `apply ... at ...` in `Anneal.*`)"
    source := "prelude\nimport Init.NotationExtra\nsyntax \"my_inv\" ident : tactic\n" },
  { label := "2. Custom `macro` / `macro_rules` in `Anneal.*`"
    source := "prelude\nimport Init.NotationExtra\nmacro \"my_tac\" : tactic => `(tactic| trivial)\n" },
  { label := "3. `register_label_attr` (`TS/AttributeDecls.lean` style)"
    source := "prelude\nimport Init.NotationExtra\nregister_label_attr SimpleArith\n" },
  { label := "4. Custom `@[SimpleArith]` attribute on theorem in `Anneal.*`"
    source := "prelude\nimport Init.NotationExtra\n@[SimpleArith] theorem foo : True := trivial\n" },
  { label := "5. `by_elab` / `run_tac` metaprogramming escape inside `by ...`"
    source := "prelude\nimport Init.NotationExtra\ntheorem foo : True := by run_tac pure ()\n" },
  { label := "6a. `native_decide` / `decide +kernel` inside `by ...`"
    source := "prelude\nimport Init.NotationExtra\ntheorem foo : 1 + 1 = 2 := by decide +kernel\n" },
  { label := "6b. Bare `decide` tactic inside `by ...` (`s[1].getArgs.isEmpty` bug in `TrustedBoundary.lean:366`)"
    source := "prelude\nimport Init.NotationExtra\ntheorem foo : 1 + 1 = 2 := by decide\n" },
  { label := "7. `cases` + `generalize` + `injections` + `subst_vars` inside `by ...`"
    source := "prelude\nimport Init.NotationExtra\ninductive Step : Nat → Nat → Prop\n| zero (x : Nat) : Step 0 x\ntheorem inv_step (f : Nat → Nat) (n out : Nat) (h : Step (f n) out) : f n = 0 := by\n  generalize hexp : f n = idx at h\n  cases h with\n  | zero x => rfl\n" },
  { label := "8. `apply_rules [lem1, lem2]` (explicit lemma list, no `register_label_attr`)"
    source := "prelude\nimport Init.NotationExtra\ninductive EvenP : Nat → Prop\n| zero : EvenP 0\n| step {n : Nat} : EvenP n → EvenP (n + 2)\ntheorem ev4 : EvenP 4 := by apply_rules [EvenP.zero, EvenP.step]\n" },
  { label := "9. `solve_by_elim [lem1, lem2]` (explicit lemma list, no `register_label_attr`)"
    source := "prelude\nimport Init.NotationExtra\ninductive EvenP : Nat → Prop\n| zero : EvenP 0\n| step {n : Nat} : EvenP n → EvenP (n + 2)\ntheorem ev4 : EvenP 4 := by solve_by_elim [EvenP.zero, EvenP.step]\n" },
  { label := "10. `fun_induction` inside `by ...` under `Init.NotationExtra`"
    source := "prelude\nimport Init.NotationExtra\ndef addOne (n : Nat) : Nat := match n with | 0 => 1 | k + 1 => addOne k + 1\ntheorem addOne_pos (n : Nat) : 0 < addOne n := by\n  fun_induction addOne n with\n  | case1 => exact Nat.zero_lt_succ 0\n  | case2 k ih => exact Nat.zero_lt_succ _\n" },
  { label := "11. `omega` inside `by ...` under `Init.NotationExtra` vs `Init.Omega`"
    source := "prelude\nimport Init.NotationExtra\ntheorem omega_test (a b : Nat) (h : a < b) : a ≤ b := by omega\n" },
  { label := "12. `lia` / `grind` inside `by ...` under `Init.NotationExtra` vs `Init.Grind`"
    source := "prelude\nimport Init.NotationExtra\ntheorem grind_test (a b : Nat) (h : a = b) : b = a := by grind\n" },
  { label := "13. `rcases` / `obtain` inside `by ...` under `Init.NotationExtra` vs `Init.RCases`"
    source := "prelude\nimport Init.NotationExtra\ntheorem obtain_test (h : ∃ n : Nat, n = 0) : True := by\n  obtain ⟨n, hn⟩ := h\n  trivial\n" }
]

unsafe def runBoundaryAuditLines : IO (Array String) := do
  let mut lines : Array String := #[]
  lines := lines.push
    "\n=== [2] `TrustedBoundary.lean` Preflight & `Init.NotationExtra` Elaboration Probe ==="
  let sysroot := (← IO.appDir).parent.getD (← findSysroot)
  initSearchPath sysroot
  enableInitializersExecution
  let foundationEnv ← importModules #[{ module := `Init.NotationExtra }] {}
    (loadExts := true)
  enableInitializersExecution
  let extendedInitEnv ← importModules #[
    { module := `Init.NotationExtra },
    { module := `Init.Omega },
    { module := `Init.Grind },
    { module := `Init.RCases }
  ] {} (loadExts := true)
  let fmt (r : Except String Unit) : String :=
    match r with
    | .ok () => "PASS"
    | .error e => s!"FAIL ({e.take 110})"
  for tc in testCases do
    let preflightStock ←
      checkPreflightSnippet false foundationEnv `Anneal.Probe tc.source
    let preflightFixed ←
      checkPreflightSnippet true foundationEnv `Anneal.Probe tc.source
    let elabFoundationRes ← checkElaboration foundationEnv tc.source
    let elabExtendedRes ← checkElaboration extendedInitEnv tc.source
    lines := lines.push s!"  * {tc.label}"
    lines := lines.push
      s!"      - TrustedBoundary preflight stock (`s[1].getArgs.isEmpty`):    {fmt preflightStock}"
    if fmt preflightStock != fmt preflightFixed then
      lines := lines.push
        s!"      - TrustedBoundary preflight fixed (`s[1][0].getArgs.isEmpty`): {fmt preflightFixed}"
    lines := lines.push
      s!"      - Elaboration (Init.NotationExtra only):                       {fmt elabFoundationRes}"
    lines := lines.push
      s!"      - Elaboration (+Init.Omega/Grind/RCases):                      {fmt elabExtendedRes}"
  return lines

end BoundaryAuditProbe

/-!
## Part 3: `Plausible` (`v4.34.0`) Negative-Canary & Spec Falsification Harness
-/

namespace PlausibleCanaryProbe

/-!
Self-contained port of `Plausible` (`v4.34.0`, commit `118aa17ee84656`) core
types (`Gen`, `Arbitrary`, `Shrinkable`, `SampleableExt`, `TestResult`,
`Configuration`, `Testable`, `decGuardTestable`, `subtypeVarTestable` at
`@[instance 2000]`, and `UInt8.Arbitrary`'s `min (← getSize) UInt8.size`) so
the probe executes via standalone `lean --run`.
-/
namespace MiniPlausible

set_option warn.classDefReducibility false

inductive GenError where
  | genError (msg : String)
  deriving Repr

structure GenState where
  size : Nat
  gen  : StdGen

abbrev Gen (α : Type) := StateT GenState (Except GenError) α

def Gen.getSize : Gen Nat := do
  return (← get).size

def Gen.resize (f : Nat → Nat) (g : Gen α) : Gen α := do
  let st ← get
  set { st with size := f st.size }
  let res ← g
  let st' ← get
  set { st' with size := st.size }
  return res

def Gen.chooseNat (lo hi : Nat) : Gen Nat := do
  let st ← get
  let (n, gen') := randNat st.gen lo hi
  set { st with gen := gen' }
  return n

class Arbitrary (α : Type) where
  arbitrary : Gen α

class Shrinkable (α : Type) where
  shrink : α → List α := fun _ => []

class SampleableExt (α : Type) where
  proxy : Type
  interp : proxy → α
  [repr : Repr proxy]
  [arb : Arbitrary proxy]
  [shrink : Shrinkable proxy]

attribute [instance] SampleableExt.repr SampleableExt.arb SampleableExt.shrink

def SampleableExt.mkSelfContained [Repr α] [Arbitrary α] [Shrinkable α] :
    SampleableExt α where
  proxy := α
  interp := id

instance (priority := 50) [Repr α] [Arbitrary α] [Shrinkable α] :
    SampleableExt α :=
  SampleableExt.mkSelfContained

instance : Arbitrary Nat where
  arbitrary := do
    Gen.chooseNat 0 (← Gen.getSize)

instance : Shrinkable Nat where
  shrink n :=
    if n == 0 then []
    else
      let half := n / 2
      if half == 0 then [0] else [0, half, n - 1]

/-- Exact replica of `Plausible/Arbitrary.lean` L94–97:
    `choose Nat 0 (min (← getSize) UInt8.size)`, which caps `UInt8` generation
    at `getSize` (default `maxSize = 100`, or `50` in `defaultCfg`)! -/
instance : Arbitrary UInt8 where
  arbitrary := do
    let n ← Gen.chooseNat 0 (min (← Gen.getSize) UInt8.size)
    return UInt8.ofNat n

instance : Shrinkable UInt8 where
  shrink x := (Shrinkable.shrink x.toNat).map UInt8.ofNat

/-- Boundary-weighted `UInt8` wrapper that samples corner values (`0`, `1`,
    `127`, `128`, `254`, `255`) and uniform full-range `0..255` regardless of
    `maxSize`. -/
structure FullRangeUInt8 where
  val : UInt8
  deriving Repr, DecidableEq

instance : Arbitrary FullRangeUInt8 where
  arbitrary := do
    let mode ← Gen.chooseNat 0 3
    if mode == 0 then
      let corners : Array UInt8 := #[0, 1, 127, 128, 254, 255]
      let idx ← Gen.chooseNat 0 (corners.size - 1)
      return ⟨corners[idx]!⟩
    else
      let n ← Gen.chooseNat 0 255
      return ⟨UInt8.ofNat n⟩

instance : Shrinkable FullRangeUInt8 where
  shrink x := (Shrinkable.shrink x.val).map FullRangeUInt8.mk

structure Configuration where
  numInst : Nat := 100
  maxSize : Nat := 100
  numRetries : Nat := 10
  randomSeed : Option Nat := none

inductive TestResult where
  | success
  | gaveUp (n : Nat)
  | failure (msg : String) (xs : List String) (shrinks : Nat)

def TestResult.isFailure : TestResult → Bool
  | .failure _ _ _ => true
  | _ => false

def addShrinks (k : Nat) : TestResult → TestResult
  | .failure msg xs n => .failure msg xs (n + k)
  | r => r

def addVarInfo [Repr α] (var : String) (x : α) : TestResult → TestResult
  | .failure msg xs n => .failure msg (s!"{var} := {repr x}" :: xs) n
  | r => r

class Testable (p : Prop) where
  run : Configuration → Bool → Gen TestResult

instance (priority := low) decidableTestable (p : Prop) [Decidable p] :
    Testable p where
  run _ _ :=
    if decide p then
      return .success
    else
      return .failure "property falsified" [] 0

/-- `Plausible/Testable.lean` L396: `decGuardTestable` tests `p → q` by
    evaluating `decide p` and returning `.gaveUp 1` when `p` is `false`. -/
instance (priority := 500) decGuardTestable (p q : Prop) [Decidable p]
    [Testable q] : Testable (p → q) where
  run cfg min :=
    if decide p then
      Testable.run q cfg min
    else
      return .gaveUp 1

partial def minimizeAux [SampleableExt α] (β : α → Prop)
    [∀ x, Testable (β x)] (cfg : Configuration)
    (x : SampleableExt.proxy α) (n : Nat) :
    Gen (Option (SampleableExt.proxy α × TestResult)) := do
  for cand in SampleableExt.shrink.shrink x do
    let res ← Testable.run (β (SampleableExt.interp cand)) cfg true
    if res.isFailure then
      let next? ← minimizeAux β cfg cand (n + 1)
      match next? with
      | some final => return some final
      | none => return some (cand, addShrinks (n + 1) res)
  return none

partial def retryGen (cmd : Gen TestResult) : Nat → Gen TestResult
  | 0 => return .gaveUp 1
  | k + 1 => do
    match ← cmd with
    | .gaveUp _ => retryGen cmd k
    | r => return r

instance (priority := 1000) varTestable [SampleableExt α] (β : α → Prop)
    [∀ x, Testable (β x)] : Testable (∀ x : α, β x) where
  run cfg min :=
    retryGen (do
      let x ← SampleableExt.arb.arbitrary
      let r ← Testable.run (β (SampleableExt.interp x)) cfg min
      if r.isFailure then
        if min then
          match ← minimizeAux β cfg x 0 with
          | some (x', r') => return addVarInfo "arg" x' r'
          | none => return addVarInfo "arg" x r
        else
          return addVarInfo "arg" x r
      else
        return r) cfg.numRetries

/-- `Plausible/Testable.lean` L448: `@[instance 2000] subtypeVarTestable`
    intercepts `∀ x : α, p x → β x` whenever `[SampleableExt { x : α // p x }]`
    is available, sampling valid `{ x // p x }` values directly with zero
    precondition rejections. -/
instance (priority := 2000) subtypeVarTestable {α : Type} (p : α → Prop)
    (β : α → Prop) [SampleableExt { x : α // p x }] [∀ x, Testable (β x)] :
    Testable (∀ x : α, p x → β x) where
  run cfg min :=
    let subProp (s : { x : α // p x }) : Prop := β s.val
    have : ∀ s : { x : α // p x }, Testable (subProp s) := fun s => inferInstanceAs (Testable (β s.val))
    @Testable.run (∀ s : { x : α // p x }, subProp s)
      (varTestable subProp) cfg min

instance [Repr α] [Shrinkable α] {p : α → Prop} [Arbitrary { x : α // p x }] :
    SampleableExt { x : α // p x } where
  proxy := { x : α // p x }
  interp := id
  repr := ⟨fun s n => Repr.reprPrec s.val n⟩
  arb := inferInstance
  shrink := ⟨fun _ => []⟩

def checkIO (p : Prop) [Testable p] (cfg : Configuration) :
    IO TestResult := do
  let seed := cfg.randomSeed.getD 42
  let mut st : GenState := { size := 0, gen := mkStdGen seed }
  let mut discarded := 0
  let mut succeeded := 0
  for i in [0:cfg.numInst] do
    let sz := (i * cfg.maxSize) / (max 1 cfg.numInst)
    st := { st with size := sz }
    match StateT.run (Testable.run p cfg true) st with
    | .error _ =>
      discarded := discarded + 1
    | .ok (res, st') =>
      st := st'
      match res with
      | .success =>
        succeeded := succeeded + 1
      | .gaveUp n =>
        discarded := discarded + n
      | .failure msg xs n =>
        return .failure msg xs n
  if succeeded == 0 && discarded > 0 then
    return .gaveUp (discarded * cfg.numRetries)
  return .success

end MiniPlausible

open MiniPlausible

inductive MirBinOp where
  | addChecked
  | subChecked
  | shlChecked
  | shlUnchecked
  deriving Repr, DecidableEq

instance : Arbitrary MirBinOp where
  arbitrary := do
    match ← Gen.chooseNat 0 3 with
    | 0 => return .addChecked
    | 1 => return .subChecked
    | 2 => return .shlChecked
    | _ => return .shlUnchecked

instance : Shrinkable MirBinOp where
  shrink _ := []

inductive MirOutcome (α : Type) where
  | val (v : α)
  | panic
  | ub
  deriving Repr, DecidableEq

def evalMirBinOpRef (op : MirBinOp) (lhs rhs : UInt8) :
    MirOutcome (UInt8 × Bool) :=
  match op with
  | .addChecked =>
    let sum := lhs.toNat + rhs.toNat
    .val (lhs + rhs, decide (sum ≥ 256))
  | .subChecked =>
    .val (lhs - rhs, decide (lhs.toNat < rhs.toNat))
  | .shlChecked =>
    let shift := rhs &&& 7
    .val (lhs <<< shift, decide (rhs.toNat ≥ 8))
  | .shlUnchecked =>
    if rhs.toNat ≥ 8 then .ub
    else .val (lhs <<< rhs, false)

/-- Mutant 1: `shlUnchecked` omits the `rhs >= 8` UB guard. -/
def evalMirBinOpMutant_MissingUbGuard (op : MirBinOp) (lhs rhs : UInt8) :
    MirOutcome (UInt8 × Bool) :=
  match op with
  | .shlUnchecked =>
    .val (lhs <<< (rhs &&& 7), false)
  | _ => evalMirBinOpRef op lhs rhs

/-- Mutant 2: `subChecked` uses `lhs <= rhs` instead of `lhs < rhs`. -/
def evalMirBinOpMutant_SubOffByOne (op : MirBinOp) (lhs rhs : UInt8) :
    MirOutcome (UInt8 × Bool) :=
  match op with
  | .subChecked =>
    .val (lhs - rhs, decide (lhs.toNat ≤ rhs.toNat))
  | _ => evalMirBinOpRef op lhs rhs

structure MirFrame where
  allocSize : Nat
  alignExp  : Nat
  offset    : Nat
  accessLen : Nat
  deriving Repr, DecidableEq

instance : Arbitrary MirFrame where
  arbitrary := do
    return {
      allocSize := ← Arbitrary.arbitrary
      alignExp  := ← Arbitrary.arbitrary
      offset    := ← Arbitrary.arbitrary
      accessLen := ← Arbitrary.arbitrary
    }

instance : Shrinkable MirFrame where
  shrink f :=
    (Shrinkable.shrink f.allocSize).map fun s => { f with allocSize := s }

def ValidFrame (f : MirFrame) : Prop :=
  f.alignExp ≤ 4 ∧
  f.offset % (2 ^ f.alignExp) = 0 ∧
  0 < f.accessLen ∧
  f.offset + f.accessLen ≤ f.allocSize ∧
  f.allocSize ≤ 64

instance (f : MirFrame) : Decidable (ValidFrame f) := by
  unfold ValidFrame
  infer_instance

def ValidFrameUnconstrained (f : MirFrame) : Prop :=
  ValidFrame f ∧ f.offset + f.accessLen = f.allocSize ∧
    f.alignExp = 4 ∧ 0 < f.offset

instance (f : MirFrame) : Decidable (ValidFrameUnconstrained f) := by
  unfold ValidFrameUnconstrained
  infer_instance

/-- Constrained generator for `{ f : MirFrame // ValidFrame f }` picked up
    automatically by `subtypeVarTestable` at priority `2000`. -/
instance : Arbitrary { f : MirFrame // ValidFrame f } where
  arbitrary := do
    let alignExp ← Gen.chooseNat 0 4
    let k ← Gen.chooseNat 0 2
    let accessLen ← Gen.chooseNat 1 8
    let slack ← Gen.chooseNat 0 3
    let align := 2 ^ alignExp
    let offset := k * align
    let allocSize := offset + accessLen + slack
    let f : MirFrame := {
      allocSize := allocSize
      alignExp  := alignExp
      offset    := offset
      accessLen := accessLen
    }
    if h : ValidFrame f then
      return ⟨f, h⟩
    else
      throw (.genError "Generated frame did not satisfy ValidFrame")

def checkDerefRef (f : MirFrame) : Bool :=
  decide (f.offset + f.accessLen ≤ f.allocSize)

def checkDerefMutant_OffByOne (f : MirFrame) : Bool :=
  decide (f.offset + f.accessLen < f.allocSize)

def alignUpBitwise (addr align : UInt8) : UInt8 :=
  (addr + (align - 1)) &&& ~~~(align - 1)

def isPowerOfTwoU8 (x : UInt8) : Bool :=
  x != 0 && (x &&& (x - 1)) == 0

def formatTestResult (res : TestResult) : String :=
  match res with
  | .success => "SUCCESS (no counterexample found)"
  | .gaveUp n => s!"GAVE UP after {n} discarded precondition failures"
  | .failure _ xs n =>
    let vars := String.intercalate ", " xs
    s!"FAILURE (shrunk {n} steps): [{vars}]"

def defaultCfg : Configuration :=
  { numInst := 200, maxSize := 50, randomSeed := some 42 }

def runTimedCheckLines (label : String) (p : Prop) [Testable p]
    (cfg : Configuration := defaultCfg) : IO (Array String) := do
  let t0 ← IO.monoNanosNow
  let res ← checkIO p cfg
  let t1 ← IO.monoNanosNow
  let elapsedUs := (t1 - t0) / 1000
  return #[
    s!"  * {label}",
    s!"      - Time:   {elapsedUs} us ({elapsedUs / 1000} ms)",
    s!"      - Result: {formatTestResult res}"
  ]

def runPlausibleCanaryLines : IO (Array String) := do
  let mut lines : Array String := #[]
  lines := lines.push
    "\n=== [3] `Plausible` (`v4.34.0`) Negative-Canary & Spec Falsification Probe ==="
  lines := lines ++ (← runTimedCheckLines
    "Canary 1a: Mutated `MirBinOp.shlUnchecked` (missing `rhs >= 8` UB guard)"
    (∀ (op : MirBinOp) (lhs rhs : UInt8),
      evalMirBinOpMutant_MissingUbGuard op lhs rhs = evalMirBinOpRef op lhs rhs))
  lines := lines ++ (← runTimedCheckLines
    "Canary 1b: Mutated `MirBinOp.subChecked` (off-by-one `lhs <= rhs` underflow flag)"
    (∀ (op : MirBinOp) (lhs rhs : UInt8),
      evalMirBinOpMutant_SubOffByOne op lhs rhs = evalMirBinOpRef op lhs rhs))
  lines := lines ++ (← runTimedCheckLines
    "Canary 2a (Naive Rejection Sampling via `decGuardTestable` on sparse `ValidFrameUnconstrained`)"
    (∀ (f : MirFrame), ValidFrameUnconstrained f →
      checkDerefMutant_OffByOne f = checkDerefRef f)
    (cfg := { numInst := 100, maxSize := 100, numRetries := 5, randomSeed := some 42 }))
  lines := lines ++ (← runTimedCheckLines
    "Canary 2b (Constrained Generator via `subtypeVarTestable` on `{ f : MirFrame // ValidFrame f }`)"
    (∀ (f : MirFrame), ValidFrame f →
      checkDerefMutant_OffByOne f = checkDerefRef f))
  lines := lines ++ (← runTimedCheckLines
    "Spec Falsification 3a: `alignUpBitwise addr align % align = 0` without `isPowerOfTwoU8 align`"
    (∀ (addr align : UInt8), align > 0 →
      (alignUpBitwise addr align) % align = 0))
  lines := lines ++ (← runTimedCheckLines
    "Spec Falsification 3b-default (`maxSize := 50`): Blind to `UInt8` overflow (`min size 256` cap in `UInt8.Arbitrary`)"
    (∀ (addr align : UInt8), isPowerOfTwoU8 align = true →
      alignUpBitwise addr align ≥ addr)
    (cfg := { numInst := 200, maxSize := 50, randomSeed := some 42 }))
  lines := lines ++ (← runTimedCheckLines
    "Spec Falsification 3b-full (`maxSize := 256` & `FullRangeUInt8`): Catches `UInt8` overflow on `alignUpBitwise`"
    (∀ (addr align : FullRangeUInt8), isPowerOfTwoU8 align.val = true →
      alignUpBitwise addr.val align.val ≥ addr.val)
    (cfg := { numInst := 200, maxSize := 256, randomSeed := some 42 }))
  lines := lines ++ (← runTimedCheckLines
    "Spec Verification 3c: Corrected `alignUpBitwise` spec with `FullRangeUInt8` (passes 200/200 tests)"
    (∀ (addr align : FullRangeUInt8),
      isPowerOfTwoU8 align.val = true →
      addr.val.toNat + align.val.toNat - 1 < 256 →
      alignUpBitwise addr.val align.val ≥ addr.val ∧
        (alignUpBitwise addr.val align.val) % align.val = 0)
    (cfg := { numInst := 200, maxSize := 256, randomSeed := some 42 }))
  return lines

end PlausibleCanaryProbe

/-!
## Part 4: Compile-Time Proof Metrics Capture + Runtime Execution
-/

namespace ProbeRunner

open Lean Elab Command

elab "#capture_inversion_metrics" : command => do
  let env := (← getEnv).setExporting false
  let out ← liftIO do
    let mut lines : Array String := #[]
    lines := lines.push
      "=== [1] Proof-Term DAG Size (`Expr.numObjs`) & Kernel Typecheck Cost ==="
    let decls := #[
      ``InversionProbe.shiftStep_inversion_succeeds,
      ``InversionProbe.shiftStep_cases_generalize_succeeds,
      ``InversionProbe.issue447_fixed_noStutter,
      ``InversionProbe.issue447_fixed_indexedWec_forward_binding,
      ``InversionProbe.issue447_fixed_indexedWec_at_syntax,
      ``InversionProbe.apply_at_demo,
      ``InversionProbe.even_8_apply_rules,
      ``InversionProbe.even_8_solve_by_elim,
      ``InversionProbe.arith_bound_omega,
      ``InversionProbe.arith_bound_lia,
      ``InversionProbe.arith_bound_grind
    ]
    for d in decls do
      lines := lines.push (← InversionProbe.measureProofLine env d)
    return String.intercalate "\n" lines.toList
  let id := mkIdent `inversionMetricsReport
  elabCommand (← `(def $id : String := $(Syntax.mkStrLit out)))

#capture_inversion_metrics

end ProbeRunner

end ProbeInversionBoundaryAndPlausible

unsafe def main : IO Unit := do
  IO.println ProbeInversionBoundaryAndPlausible.ProbeRunner.inversionMetricsReport
  let auditLines ←
    ProbeInversionBoundaryAndPlausible.BoundaryAuditProbe.runBoundaryAuditLines
  for l in auditLines do
    IO.println l
  let plausibleLines ←
    ProbeInversionBoundaryAndPlausible.PlausibleCanaryProbe.runPlausibleCanaryLines
  for l in plausibleLines do
    IO.println l
