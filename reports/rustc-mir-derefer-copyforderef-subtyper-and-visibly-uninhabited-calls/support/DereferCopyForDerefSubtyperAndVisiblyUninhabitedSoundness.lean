/-
  DereferCopyForDerefSubtyperAndVisiblyUninhabitedSoundness.lean

  Kernel-checked Lean 4 (v4.34.1) mechanization of three required rustc MIR
  phase-transition desugarings:
    Part I:   `Derefer` (`deref_separator.rs`) projection-chain normal form
              (`projection[1..]` deref-free, `VarDebugInfo` exclusion) and
              `EraseDerefTemps` (`erase_deref_temps.rs`) `CopyForDeref` ->
              `Rvalue::Use(Operand::Copy(_), WithRetag::No)` Tree Borrows and
              Stacked Borrows equivalence, plus concrete `WithRetag::Yes` UB
              counterexamples under both aliasing models.
    Part II:  `Subtyper` (`add_subtyping_projections.rs`) region-erased and
              anonymized higher-ranked binder (HRTB) `CastKind::Subtype`
              insertion soundness, strict runtime assignment typing, `TypeId`
              distinction preservation, and operational value-preservation.
    Part III: `LintAndRemoveUninhabited` (`lint_and_remove_uninhabited.rs`,
              `inhabitedness/mod.rs`, `inhabited_predicate.rs`) three-tier
              inhabitedness implication chain (`!isInhabitedFrom` ->
              `isPrivatelyUninhabited` -> `!isOpsemInhabited`), strict
              reference separation (`&!`), call-return pruning operational
              soundness, definite-initialization (`E0381`) gate, SemVer
              monotonicity across module boundaries, and enclosing-uninhabited
              lint suppression.

  Purity guarantees:
    - Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
      zero `native_decide`, zero `partial def`, zero `._unsafe_rec` helpers.
    - Every equality/predicate over inductive types with `List`/`Option` fields
      is defined by explicit total structural recursion (no `deriving` on such
      types).
-/

namespace RustcMirPhaseTransitions

/-! ==========================================================================
    PART 0: Constructive Arithmetic Helpers (Zero `omega`)
    ========================================================================== -/

private theorem nat_beq_refl (n : Nat) : (n == n) = true :=
  decide_eq_true rfl

private theorem nat_beq_eq_true_iff (a b : Nat) : (a == b) = true ↔ a = b :=
  ⟨of_decide_eq_true, decide_eq_true⟩

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  cases hEq : (a == b) with
  | false => rfl
  | true => exact False.elim (h ((nat_beq_eq_true_iff a b).mp hEq))

/-! ==========================================================================
    PART I: `Derefer` Projection-Chain Normal Form & `EraseDerefTemps`
            `WithRetag::No` Tree Borrows / Stacked Borrows Preservation
    ========================================================================== -/

namespace DereferEraseDerefTemps

/-- MIR place projection element (`ProjectionElem::Deref` or `ProjectionElem::Field`). -/
inductive ProjElem where
  | deref
  | field (idx : Nat)

/-- Explicit total equality on `ProjElem`. -/
def ProjElem.beq : ProjElem → ProjElem → Bool
  | .deref, .deref => true
  | .field i, .field j => i == j
  | _, _ => false

/-- MIR place: base local plus left-to-right projection chain. -/
structure Place where
  localId : Nat
  proj : List ProjElem

/-- Place context distinguishing `PlaceContext::NonUse(VarDebugInfo)`. -/
inductive PlaceCtx where
  | runtimeUse
  | varDebugInfo

/-- `LocalInfo` distinction relevant to `Derefer` and `EraseDerefTemps`. -/
inductive LocalInfo where
  | boring
  | derefTemp

/-- `rustc_middle::mir::WithRetag` (`syntax.rs:490`). -/
inductive WithRetag where
  | yes
  | no

/-- Subset of MIR rvalues needed for nested dereference desugaring and raw split. -/
inductive Rvalue where
  | useCopy (p : Place) (retag : WithRetag)
  | copyForDeref (p : Place)
  | rawMut (p : Place)
  | constU32 (v : Nat)
  | addLocals (lhs rhs : Nat)

/-- MIR statement in our phase-transition calculus. -/
inductive Stmt where
  | assign (dst : Place) (rv : Rvalue)
  | varDebug (nameId : Nat) (p : Place)

/-- A projection list contains no `ProjectionElem::Deref` (written via `List.foldr`
    so Lean emits zero compiler `_unsafe_rec` helpers). -/
def projHasNoDeref (xs : List ProjElem) : Bool :=
  xs.foldr (fun elem ih =>
    match elem with
    | .deref => false
    | .field _ => ih) true

/-- `validate.rs:956-965` invariant: `Deref` may only occur at `projection[0]`. -/
def derefOnlyFirst (p : Place) : Bool :=
  match p.proj with
  | [] => true
  | _ :: tail => projHasNoDeref tail

/-- True iff `projection[1..]` contains at least one `ProjectionElem::Deref`
    (`deref_separator.rs:26`). -/
def hasNestedDeref (p : Place) : Bool :=
  !(derefOnlyFirst p)

/-- Prefix/tail decomposition of a deref-chain split step matching
    `DerefChecker::visit_place` (`deref_separator.rs:23-81`), written via
    `List.foldr` to emit zero `_unsafe_rec` helpers. -/
def splitAfterFirstAux
    (nextTmp : Nat) (curLocal : Nat) (acc : List ProjElem)
    (addMeta : Bool) (rem : List ProjElem) : List (Nat × LocalInfo × Stmt) × Place × Nat :=
  rem.foldr
    (fun elem ih nTmp cLoc curAcc =>
      match elem with
      | .field f => ih nTmp cLoc (curAcc ++ [.field f])
      | .deref =>
        let srcPlace : Place := { localId := cLoc, proj := curAcc }
        let info : LocalInfo := if addMeta then .derefTemp else .boring
        let rv : Rvalue :=
          if addMeta then .copyForDeref srcPlace else .useCopy srcPlace .no
        let emitStmt : Stmt := .assign { localId := nTmp, proj := [] } rv
        let (moreStmts, finalPlace, finalTmp) := ih (nTmp + 1) nTmp [.deref]
        ((nTmp, info, emitStmt) :: moreStmts, finalPlace, finalTmp))
    (fun nTmp cLoc curAcc => ([], { localId := cLoc, proj := curAcc }, nTmp))
    nextTmp curLocal acc

/-- `Derefer::visit_place` (`deref_separator.rs:23-81`) on a single place.
    Skips `PlaceCtx.varDebugInfo` (`deref_separator.rs:25`) and places that
    already satisfy `derefOnlyFirst`. -/
def dereferPlace (nextTmp : Nat) (ctx : PlaceCtx) (addMeta : Bool) (p : Place) :
    List (Nat × LocalInfo × Stmt) × Place × Nat :=
  match ctx with
  | .varDebugInfo => ([], p, nextTmp)
  | .runtimeUse =>
    if derefOnlyFirst p then
      ([], p, nextTmp)
    else
      match p.proj with
      | [] => ([], p, nextTmp)
      | first :: rest => splitAfterFirstAux nextTmp p.localId [first] addMeta rest

def rvalueDerefOnlyFirst : Rvalue → Bool
  | .useCopy p _ => derefOnlyFirst p
  | .copyForDeref p => derefOnlyFirst p
  | .rawMut p => derefOnlyFirst p
  | .constU32 _ => true
  | .addLocals _ _ => true

def stmtDerefOnlyFirst : Stmt → Bool
  | .assign dst rv => derefOnlyFirst dst && rvalueDerefOnlyFirst rv
  | .varDebug _ _ => true

private theorem projHasNoDeref_nil : projHasNoDeref [] = true := rfl
private theorem projHasNoDeref_cons_deref (rest : List ProjElem) :
    projHasNoDeref (.deref :: rest) = false := rfl
private theorem projHasNoDeref_cons_field (f : Nat) (rest : List ProjElem) :
    projHasNoDeref (.field f :: rest) = projHasNoDeref rest := rfl

private theorem projHasNoDeref_append (xs ys : List ProjElem) :
    projHasNoDeref (xs ++ ys) = (projHasNoDeref xs && projHasNoDeref ys) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    cases x with
    | deref => rfl
    | field f =>
      rw [List.cons_append, projHasNoDeref_cons_field, projHasNoDeref_cons_field]
      exact ih

private theorem derefOnlyFirst_snoc_field (l : Nat) (acc : List ProjElem) (f : Nat)
    (h : derefOnlyFirst { localId := l, proj := acc } = true) :
    derefOnlyFirst { localId := l, proj := acc ++ [.field f] } = true := by
  cases acc with
  | nil => rfl
  | cons e tail =>
    simp only [derefOnlyFirst, List.cons_append] at h ⊢
    rw [projHasNoDeref_append, h, projHasNoDeref_cons_field, projHasNoDeref_nil]
    rfl

private theorem splitAfterFirstAux_nil (nextTmp curLocal : Nat) (acc : List ProjElem) (addMeta : Bool) :
    splitAfterFirstAux nextTmp curLocal acc addMeta [] =
      ([], { localId := curLocal, proj := acc }, nextTmp) := rfl

private theorem splitAfterFirstAux_cons_field
    (nextTmp curLocal : Nat) (acc : List ProjElem) (addMeta : Bool) (f : Nat) (rest : List ProjElem) :
    splitAfterFirstAux nextTmp curLocal acc addMeta (.field f :: rest) =
      splitAfterFirstAux nextTmp curLocal (acc ++ [.field f]) addMeta rest := rfl

private theorem splitAfterFirstAux_cons_deref
    (nextTmp curLocal : Nat) (acc : List ProjElem) (addMeta : Bool) (rest : List ProjElem) :
    splitAfterFirstAux nextTmp curLocal acc addMeta (.deref :: rest) =
      let srcPlace : Place := { localId := curLocal, proj := acc }
      let info : LocalInfo := if addMeta then .derefTemp else .boring
      let rv : Rvalue :=
        if addMeta then .copyForDeref srcPlace else .useCopy srcPlace .no
      let emitStmt : Stmt := .assign { localId := nextTmp, proj := [] } rv
      let (moreStmts, finalPlace, finalTmp) :=
        splitAfterFirstAux (nextTmp + 1) nextTmp [.deref] addMeta rest
      ((nextTmp, info, emitStmt) :: moreStmts, finalPlace, finalTmp) := rfl

/-- Core structural induction proving `splitAfterFirstAux` emits only
    `derefOnlyFirst` statements (with `DerefTemp` + `CopyForDeref` when
    `addMeta = true`) and yields a `derefOnlyFirst` final place. -/
theorem splitAfterFirstAux_normalForm
    (rem : List ProjElem) (nextTmp curLocal : Nat) (acc : List ProjElem) (addMeta : Bool)
    (hAcc : derefOnlyFirst { localId := curLocal, proj := acc } = true) :
    let res := splitAfterFirstAux nextTmp curLocal acc addMeta rem
    res.1.all (fun entry => stmtDerefOnlyFirst entry.2.2) = true ∧
    derefOnlyFirst res.2.1 = true ∧
    (addMeta = true →
      res.1.all (fun entry =>
        match entry.2.1, entry.2.2 with
        | .derefTemp, .assign { localId := _, proj := [] } (.copyForDeref _) => true
        | _, _ => false) = true) := by
  induction rem generalizing nextTmp curLocal acc with
  | nil =>
    refine ⟨rfl, hAcc, fun _ => rfl⟩
  | cons elem rest ih =>
    cases elem with
    | field f =>
      rw [splitAfterFirstAux_cons_field]
      exact ih nextTmp curLocal (acc ++ [.field f])
        (derefOnlyFirst_snoc_field curLocal acc f hAcc)
    | deref =>
      have hSingle : derefOnlyFirst { localId := nextTmp, proj := [.deref] } = true := rfl
      have hRest := ih (nextTmp + 1) nextTmp [.deref] hSingle
      rcases hRest with ⟨hStmts, hFinal, hMeta⟩
      rw [splitAfterFirstAux_cons_deref]
      refine ⟨?_, hFinal, ?_⟩
      · simp only [List.all]
        have hCurStmt :
            stmtDerefOnlyFirst
              (.assign { localId := nextTmp, proj := [] }
                (if addMeta then .copyForDeref { localId := curLocal, proj := acc }
                 else .useCopy { localId := curLocal, proj := acc } .no)) = true := by
          cases addMeta <;> (
            simp only [ite_true, Bool.false_eq_true, ite_false, stmtDerefOnlyFirst, rvalueDerefOnlyFirst]
            rw [hAcc]
            rfl
          )
        rw [hCurStmt, hStmts]
        rfl
      · intro hAdd
        subst hAdd
        simp only [List.all, ite_true]
        rw [hMeta rfl]
        rfl

/-- **Theorem 1 (`Derefer` Projection-Chain Normal Form):**
    `dereferPlace` produces exclusively `derefOnlyFirst` temporary assignments
    and a `derefOnlyFirst` rewritten place for arbitrary projection chains. -/
theorem dereferPlace_normalForm
    (nextTmp : Nat) (ctx : PlaceCtx) (addMeta : Bool) (p : Place) :
    let res := dereferPlace nextTmp ctx addMeta p
    res.1.all (fun entry => stmtDerefOnlyFirst entry.2.2) = true ∧
    (ctx = .runtimeUse → derefOnlyFirst res.2.1 = true) := by
  cases ctx with
  | varDebugInfo =>
    refine ⟨rfl, fun h => PlaceCtx.noConfusion h⟩
  | runtimeUse =>
    simp only [dereferPlace]
    cases hOk : derefOnlyFirst p with
    | true =>
      exact ⟨rfl, fun _ => hOk⟩
    | false =>
      cases hp : p.proj with
      | nil =>
        simp [derefOnlyFirst, hp] at hOk
      | cons first rest =>
        have h1 : derefOnlyFirst { localId := p.localId, proj := [first] } = true := rfl
        have hRes := splitAfterFirstAux_normalForm rest nextTmp p.localId [first] addMeta h1
        exact ⟨hRes.1, fun _ => hRes.2.1⟩

/-- **Theorem 2 (`VarDebugInfo` Preservation, `deref_separator.rs:25`):**
    `Derefer` never rewrites `VarDebugInfo` places and emits zero temporaries for them. -/
theorem dereferPlace_skips_varDebugInfo (nextTmp : Nat) (addMeta : Bool) (p : Place) :
    dereferPlace nextTmp .varDebugInfo addMeta p = ([], p, nextTmp) := rfl

/-- `EraseDerefTemps` (`erase_deref_temps.rs:19-33`) parameterized by `WithRetag`. -/
def eraseDerefTempsRvalue (retag : WithRetag) : Rvalue → Rvalue
  | .copyForDeref p => .useCopy p retag
  | other => other

def eraseDerefTempsStmt (retag : WithRetag) : Stmt → Stmt
  | .assign dst rv => .assign dst (eraseDerefTempsRvalue retag rv)
  | .varDebug n p => .varDebug n p

def eraseDerefTempsLocal : LocalInfo → LocalInfo
  | .derefTemp => .boring
  | .boring => .boring

def stmtHasNoCopyForDeref : Stmt → Bool
  | .assign _ (.copyForDeref _) => false
  | _ => true

def localIsNotDerefTemp : LocalInfo → Bool
  | .derefTemp => false
  | .boring => true

/-- **Theorem 3 (`EraseDerefTemps` Postconditions, `validate.rs:1028-1031, 1669-1673`):**
    `EraseDerefTemps` eliminates every `CopyForDeref` and `DerefTemp` while
    strictly preserving the `derefOnlyFirst` normal form. -/
theorem eraseDerefTemps_eliminates_and_preserves (retag : WithRetag) (s : Stmt) (info : LocalInfo)
    (hNorm : stmtDerefOnlyFirst s = true) :
    stmtHasNoCopyForDeref (eraseDerefTempsStmt retag s) = true ∧
    stmtDerefOnlyFirst (eraseDerefTempsStmt retag s) = true ∧
    localIsNotDerefTemp (eraseDerefTempsLocal info) = true := by
  have hLoc : localIsNotDerefTemp (eraseDerefTempsLocal info) = true := by
    cases info <;> rfl
  cases s with
  | varDebug n p =>
    exact ⟨rfl, rfl, hLoc⟩
  | assign dst rv =>
    cases rv with
    | copyForDeref p =>
      simp [eraseDerefTempsStmt, eraseDerefTempsRvalue, stmtHasNoCopyForDeref,
            stmtDerefOnlyFirst, rvalueDerefOnlyFirst] at hNorm ⊢
      exact ⟨hNorm, hLoc⟩
    | useCopy p r =>
      exact ⟨rfl, hNorm, hLoc⟩
    | rawMut p =>
      exact ⟨rfl, hNorm, hLoc⟩
    | constU32 v =>
      exact ⟨rfl, hNorm, hLoc⟩
    | addLocals a b =>
      exact ⟨rfl, hNorm, hLoc⟩

/-! ### Tree Borrows & Stacked Borrows Operational Semantics for Deref Chains -/

/-- Tree Borrows per-tag, per-field permission state. -/
inductive TBPerm where
  | reserved
  | active
  | frozen
  | disabled

/-- Tree Borrows child write transition (matches Miri `tree_borrows/perms.rs`). -/
def tbChildWrite : TBPerm → Option TBPerm
  | .reserved => some .active
  | .active => some .active
  | .frozen => none
  | .disabled => none

/-- Tree Borrows child read transition. -/
def tbChildRead : TBPerm → Option TBPerm
  | .reserved => some .reserved
  | .active => some .active
  | .frozen => some .frozen
  | .disabled => none

/-- Tree Borrows foreign read transition (triggered by sibling reborrow retag). -/
def tbForeignRead : TBPerm → TBPerm
  | .reserved => .reserved
  | .active => .frozen
  | .frozen => .frozen
  | .disabled => .disabled

/-- Tree Borrows foreign write transition. -/
def tbForeignWrite : TBPerm → TBPerm
  | .reserved => .disabled
  | .active => .disabled
  | .frozen => .disabled
  | .disabled => .disabled

/-- Runtime pointer value with allocation ID, field offset path, and provenance tag. -/
structure PtrVal where
  allocId : Nat
  fieldPath : List Nat
  tag : Nat

/-- Runtime value stored in a local or heap cell. -/
inductive Val where
  | u32 (n : Nat)
  | ptr (p : PtrVal)

/-- Explicit aliasing UB reasons matching live Miri diagnostics. -/
inductive AliasUb where
  | frozenWriteForbidden (tag : Nat) (fieldIdx : Nat)
  | disabledAccessForbidden (tag : Nat) (fieldIdx : Nat)
  | tagMissingFromStack (tag : Nat) (fieldIdx : Nat)
  | missingLocation

/-- Outcome of executing a step or program under an aliasing model. -/
inductive ExecRes (α : Type) where
  | ok (v : α)
  | ub (err : AliasUb)

/-- Minimal Tree Borrows machine state over arbitrary dereference chains. -/
structure TBState where
  locals : Nat → Option Val
  heap : Nat → List Nat → Option Val
  perms : Nat → Nat → TBPerm
  parentOf : Nat → Option Nat
  nextTag : Nat

def TBState.setLocal (s : TBState) (l : Nat) (v : Val) : TBState :=
  { s with locals := fun k => if k == l then some v else s.locals k }

/-- Resolve a projection list starting from an already-evaluated `Val` (a pointer)
    in `TBState` without performing any retag (written via `List.foldr`). -/
def evalProjChain (heap : Nat → List Nat → Option Val) (v : Val)
    (projs : List ProjElem) : Option Val :=
  projs.foldr
    (fun elem ih curV =>
      match elem with
      | .deref =>
        match curV with
        | .ptr p =>
          match heap p.allocId p.fieldPath with
          | some inner => ih inner
          | none => none
        | .u32 _ => none
      | .field f =>
        match curV with
        | .ptr p => ih (.ptr { p with fieldPath := p.fieldPath ++ [f] })
        | .u32 _ => none)
    (fun curV => some curV)
    v

/-- Evaluate a `Place` to its resolved pointer/value without retagging. -/
def evalPlaceNoRetag (s : TBState) (p : Place) : Option Val :=
  match s.locals p.localId with
  | none => none
  | some baseVal => evalProjChain s.heap baseVal p.proj

private theorem evalProjChain_cons_deref (heap : Nat → List Nat → Option Val)
    (p : PtrVal) (rest : List ProjElem) :
    evalProjChain heap (.ptr p) (.deref :: rest) =
      match heap p.allocId p.fieldPath with
      | some inner => evalProjChain heap inner rest
      | none => none := rfl

private theorem evalProjChain_cons_field (heap : Nat → List Nat → Option Val)
    (p : PtrVal) (f : Nat) (rest : List ProjElem) :
    evalProjChain heap (.ptr p) (.field f :: rest) =
      evalProjChain heap (.ptr { p with fieldPath := p.fieldPath ++ [f] }) rest := rfl

private theorem evalProjChain_append (heap : Nat → List Nat → Option Val)
    (v : Val) (xs ys : List ProjElem) :
    evalProjChain heap v (xs ++ ys) =
      match evalProjChain heap v xs with
      | some v' => evalProjChain heap v' ys
      | none => none := by
  induction xs generalizing v with
  | nil => rfl
  | cons e rest ih =>
    cases e with
    | deref =>
      cases v with
      | u32 _ => rfl
      | ptr p =>
        rw [List.cons_append, evalProjChain_cons_deref, evalProjChain_cons_deref]
        cases heap p.allocId p.fieldPath with
        | none => rfl
        | some inner => exact ih inner
    | field f =>
      cases v with
      | u32 _ => rfl
      | ptr p =>
        rw [List.cons_append, evalProjChain_cons_field, evalProjChain_cons_field]
        exact ih (.ptr { p with fieldPath := p.fieldPath ++ [f] })

/-- Execute a list of `WithRetag::No` temp-copy assignments emitted by
    `Derefer` + `EraseDerefTemps`, strictly preserving `s.heap`, `s.perms`,
    `s.parentOf`, and `s.nextTag` (written via `List.foldr`). -/
def execNoRetagStmts (s : TBState) (stmts : List Stmt) : Option TBState :=
  stmts.foldr
    (fun stmt ih curS =>
      match stmt with
      | .assign { localId := dst, proj := [] } (.useCopy src .no) =>
        match evalPlaceNoRetag curS src with
        | some v => ih (curS.setLocal dst v)
        | none => none
      | _ => none)
    (fun curS => some curS)
    s

private theorem execNoRetagStmts_cons_noRetag (s : TBState) (dst : Nat) (src : Place) (rest : List Stmt) :
    execNoRetagStmts s (.assign { localId := dst, proj := [] } (.useCopy src .no) :: rest) =
      match evalPlaceNoRetag s src with
      | some v => execNoRetagStmts (s.setLocal dst v) rest
      | none => none := rfl

/-- **Theorem 4 (`splitAfterFirstAux_noRetag_equiv_and_preserves_tb`):**
    For any projection chain of arbitrary depth `rem`, executing the `Derefer`
    temp chain lowered with `EraseDerefTemps(WithRetag::No)` evaluates to the
    exact same resolved value/pointer+tag as direct place evaluation, and leaves
    `heap`, `perms` (the entire Tree Borrows state), `parentOf`, and `nextTag`
    strictly unchanged. -/
theorem splitAfterFirstAux_noRetag_equiv_and_preserves_tb
    (rem : List ProjElem) (nextTmp curLocal : Nat) (acc : List ProjElem)
    (s : TBState) (vCur vFinal : Val)
    (hCur : s.locals curLocal = some vCur)
    (hEval : evalProjChain s.heap vCur (acc ++ rem) = some vFinal) :
    let raw := splitAfterFirstAux nextTmp curLocal acc true rem
    let erasedStmts := raw.1.map (fun e => eraseDerefTempsStmt .no e.2.2)
    ∃ s',
      execNoRetagStmts s erasedStmts = some s' ∧
      evalPlaceNoRetag s' raw.2.1 = some vFinal ∧
      s'.heap = s.heap ∧ s'.perms = s.perms ∧
      s'.parentOf = s.parentOf ∧ s'.nextTag = s.nextTag := by
  induction rem generalizing nextTmp curLocal acc s vCur with
  | nil =>
    refine ⟨s, rfl, ?_, rfl, rfl, rfl, rfl⟩
    rw [splitAfterFirstAux_nil]
    simp only [evalPlaceNoRetag, hCur]
    simpa [List.append_nil] using hEval
  | cons elem rest ih =>
    cases elem with
    | field f =>
      have hAssoc : (acc ++ [.field f]) ++ rest = acc ++ (.field f :: rest) := by
        simp [List.append_assoc]
      rw [← hAssoc] at hEval
      rw [splitAfterFirstAux_cons_field]
      exact ih nextTmp curLocal (acc ++ [.field f]) s vCur hCur hEval
    | deref =>
      rw [evalProjChain_append] at hEval
      cases hAccVal : evalProjChain s.heap vCur acc with
      | none =>
        rw [hAccVal] at hEval
        cases hEval
      | some midVal =>
        rw [hAccVal] at hEval
        have hSrcEval : evalPlaceNoRetag s { localId := curLocal, proj := acc } = some midVal := by
          simp only [evalPlaceNoRetag, hCur, hAccVal]
        let s1 := s.setLocal nextTmp midVal
        have hS1Loc : s1.locals nextTmp = some midVal := by
          simp only [s1, TBState.setLocal, nat_beq_refl, ite_true]
        have hRestEval : evalProjChain s1.heap midVal ([.deref] ++ rest) = some vFinal := hEval
        rcases ih (nextTmp + 1) nextTmp [.deref] s1 midVal hS1Loc hRestEval with
          ⟨s', hExecRest, hFinalPlace, hHeap, hPerms, hParent, hNext⟩
        rw [splitAfterFirstAux_cons_deref]
        refine ⟨s', ?_, hFinalPlace, hHeap, hPerms, hParent, hNext⟩
        change execNoRetagStmts s
            (.assign { localId := nextTmp, proj := [] } (.useCopy { localId := curLocal, proj := acc } .no) ::
              (splitAfterFirstAux (nextTmp + 1) nextTmp [.deref] true rest).1.map
                (fun e => eraseDerefTempsStmt .no e.2.2)) = some s'
        rw [execNoRetagStmts_cons_noRetag, hSrcEval]
        exact hExecRest

/-- **Theorem 5 (`derefer_then_eraseNoRetag_preserves_tree_borrows`):**
    End-to-end corollary for `dereferPlace` + `EraseDerefTemps(WithRetag::No)`
    on any runtime place `p`: identical resolved value/provenance tag,
    `derefOnlyFirst` normal form, and zero Tree Borrows state perturbation. -/
theorem derefer_then_eraseNoRetag_preserves_tree_borrows
    (nextTmp : Nat) (p : Place) (s : TBState) (vFinal : Val)
    (hEval : evalPlaceNoRetag s p = some vFinal) :
    let raw := dereferPlace nextTmp .runtimeUse true p
    let erasedStmts := raw.1.map (fun e => eraseDerefTempsStmt .no e.2.2)
    derefOnlyFirst raw.2.1 = true ∧
    ∃ s',
      execNoRetagStmts s erasedStmts = some s' ∧
      evalPlaceNoRetag s' raw.2.1 = some vFinal ∧
      s'.heap = s.heap ∧ s'.perms = s.perms ∧
      s'.parentOf = s.parentOf ∧ s'.nextTag = s.nextTag := by
  have hNf := (dereferPlace_normalForm nextTmp .runtimeUse true p).2 rfl
  refine ⟨hNf, ?_⟩
  simp only [dereferPlace]
  cases hOk : derefOnlyFirst p with
  | true =>
    exact ⟨s, rfl, hEval, rfl, rfl, rfl, rfl⟩
  | false =>
    cases hp : p.proj with
    | nil =>
      simp [derefOnlyFirst, hp] at hOk
    | cons first rest =>
      simp only [evalPlaceNoRetag, hp] at hEval
      cases hLoc : s.locals p.localId with
      | none =>
        rw [hLoc] at hEval
        cases hEval
      | some vCur =>
        rw [hLoc] at hEval
        exact splitAfterFirstAux_noRetag_equiv_and_preserves_tb
          rest nextTmp p.localId [first] s vCur vFinal hLoc hEval

/-! ### Concrete `WithRetag::Yes` UB Counterexamples (Tree Borrows & Stacked Borrows)
    Mirrors `nested_mut_raw_split` vs `custom_with_retag_yes` from live Miri probe. -/

structure TupleTBState where
  f0 : Nat
  f1 : Nat
  perms : Nat → Nat → TBPerm
  isChild : Nat → Bool
  nextTag : Nat

def initTupleTBState : TupleTBState :=
  { f0 := 1
    f1 := 2
    perms := fun t _ => if t == 0 then .active else .disabled
    isChild := fun _ => false
    nextTag := 1 }

/-- Copy `&mut (u32, u32)` from `*pp` (root tag `0`) under `retag : WithRetag`:
    - `WithRetag.no`: returns tag `0` unchanged, zero Tree Borrows transitions.
    - `WithRetag.yes`: allocates fresh child tag `newT` in `.reserved` across
      both fields `0` and `1`, and performs a foreign read (`tbForeignRead`)
      on every existing child tag across both fields `0` and `1`. -/
def tbCopyMutRef (st : TupleTBState) (retag : WithRetag) : Nat × TupleTBState :=
  match retag with
  | .no => (0, st)
  | .yes =>
    let newT := st.nextTag
    let perms' : Nat → Nat → TBPerm := fun t idx =>
      if t == newT then .reserved
      else if st.isChild t then tbForeignRead (st.perms t idx)
      else st.perms t idx
    let isChild' : Nat → Bool := fun t => if t == newT then true else st.isChild t
    (newT, { st with perms := perms', isChild := isChild', nextTag := newT + 1 })

def tbReadField (st : TupleTBState) (tag : Nat) (idx : Nat) : ExecRes (Nat × TupleTBState) :=
  match tbChildRead (st.perms tag idx) with
  | none => .ub (.disabledAccessForbidden tag idx)
  | some p' =>
    let perms' : Nat → Nat → TBPerm := fun t i =>
      if i == idx then
        if t == tag then p'
        else if t == 0 then st.perms t i
        else tbForeignRead (st.perms t i)
      else st.perms t i
    let val := if idx == 0 then st.f0 else st.f1
    .ok (val, { st with perms := perms' })

def tbWriteField (st : TupleTBState) (tag : Nat) (idx : Nat) (val : Nat) : ExecRes TupleTBState :=
  match tbChildWrite (st.perms tag idx) with
  | none =>
    match st.perms tag idx with
    | .frozen => .ub (.frozenWriteForbidden tag idx)
    | _ => .ub (.disabledAccessForbidden tag idx)
  | some p' =>
    let perms' : Nat → Nat → TBPerm := fun t i =>
      if i == idx then
        if t == tag then p'
        else if t == 0 then st.perms t i
        else tbForeignWrite (st.perms t i)
      else st.perms t i
    let st' :=
      if idx == 0 then { st with f0 := val, perms := perms' }
      else { st with f1 := val, perms := perms' }
    .ok st'

def runSplitRawTB (retag : WithRetag) : ExecRes (Nat × Nat) :=
  let (t1, st1) := tbCopyMutRef initTupleTBState retag
  match tbWriteField st1 t1 0 11 with
  | .ub e => .ub e
  | .ok st2 =>
    let (t2, st3) := tbCopyMutRef st2 retag
    match tbWriteField st3 t2 1 22 with
    | .ub e => .ub e
    | .ok st4 =>
      match tbReadField st4 t1 0 with
      | .ub e => .ub e
      | .ok (v0, st5) =>
        match tbReadField st5 t2 1 with
        | .ub e => .ub e
        | .ok (v1, st6) =>
          match tbWriteField st6 t1 0 (v0 + v1) with
          | .ub e => .ub e
          | .ok st7 => .ok (st7.f0, st7.f1)

/-- **Theorem 6 (`withRetagNo_succeeds_and_withRetagYes_causes_tree_borrows_ub`):**
    On the split-field `&mut &mut (u32, u32)` program:
    - `WithRetag.no` (`EraseDerefTemps`) succeeds with `(33, 22)`.
    - `WithRetag.yes` triggers Tree Borrows UB (`.frozenWriteForbidden 1 0`)
      at the final write `*p0 = v0 + v1` because the second deref-temp retag
      performs a foreign read across both fields `[0, 1]`, freezing tag `1`. -/
theorem withRetagNo_succeeds_and_withRetagYes_causes_tree_borrows_ub :
    runSplitRawTB .no = .ok (33, 22) ∧
    runSplitRawTB .yes = .ub (.frozenWriteForbidden 1 0) :=
  ⟨rfl, rfl⟩

/-! ### Analogous Stacked Borrows Counterexample -/

inductive SBItem where
  | unique (tag : Nat)
  | srw (tag : Nat)

def sbHasTag (tag : Nat) (stk : List SBItem) : Bool :=
  stk.foldr
    (fun item ih =>
      match item with
      | .unique t => (t == tag) || ih
      | .srw t => (t == tag) || ih)
    false

def sbPopAbove (parentTag : Nat) (stk : List SBItem) : List SBItem :=
  (stk.foldr
    (fun item (acc : List SBItem × List SBItem) =>
      let full := item :: acc.1
      let popped :=
        match item with
        | .unique t => if t == parentTag then full else acc.2
        | .srw t => if t == parentTag then full else acc.2
      (full, popped))
    ([], [])).2

structure TupleSBState where
  f0 : Nat
  f1 : Nat
  stack0 : List SBItem
  stack1 : List SBItem
  nextTag : Nat

def initTupleSBState : TupleSBState :=
  { f0 := 1, f1 := 2, stack0 := [.unique 0], stack1 := [.unique 0], nextTag := 1 }

def sbCopyMutRef (st : TupleSBState) (retag : WithRetag) : Nat × TupleSBState :=
  match retag with
  | .no => (0, st)
  | .yes =>
    let newT := st.nextTag
    (newT,
      { st with
        stack0 := .unique newT :: sbPopAbove 0 st.stack0
        stack1 := .unique newT :: sbPopAbove 0 st.stack1
        nextTag := newT + 1 })

def sbDeriveRaw (st : TupleSBState) (parentTag : Nat) (idx : Nat) : Nat × TupleSBState :=
  let rawT := st.nextTag
  if idx == 0 then
    (rawT, { st with stack0 := .srw rawT :: sbPopAbove parentTag st.stack0, nextTag := rawT + 1 })
  else
    (rawT, { st with stack1 := .srw rawT :: sbPopAbove parentTag st.stack1, nextTag := rawT + 1 })

def sbReadField (st : TupleSBState) (tag : Nat) (idx : Nat) : ExecRes Nat :=
  let stk := if idx == 0 then st.stack0 else st.stack1
  if sbHasTag tag stk then .ok (if idx == 0 then st.f0 else st.f1)
  else .ub (.tagMissingFromStack tag idx)

def sbWriteField (st : TupleSBState) (tag : Nat) (idx : Nat) (val : Nat) : ExecRes TupleSBState :=
  let stk := if idx == 0 then st.stack0 else st.stack1
  if sbHasTag tag stk then
    if idx == 0 then .ok { st with f0 := val, stack0 := sbPopAbove tag st.stack0 }
    else .ok { st with f1 := val, stack1 := sbPopAbove tag st.stack1 }
  else .ub (.tagMissingFromStack tag idx)

def runSplitRawSB (retag : WithRetag) : ExecRes (Nat × Nat) :=
  let (t1, st1) := sbCopyMutRef initTupleSBState retag
  let (p0, st2) := sbDeriveRaw st1 t1 0
  match sbWriteField st2 p0 0 11 with
  | .ub e => .ub e
  | .ok st3 =>
    let (t2, st4) := sbCopyMutRef st3 retag
    let (p1, st5) := sbDeriveRaw st4 t2 1
    match sbWriteField st5 p1 1 22 with
    | .ub e => .ub e
    | .ok st6 =>
      match sbReadField st6 p0 0 with
      | .ub e => .ub e
      | .ok v0 =>
        match sbReadField st6 p1 1 with
        | .ub e => .ub e
        | .ok v1 =>
          match sbWriteField st6 p0 0 (v0 + v1) with
          | .ub e => .ub e
          | .ok st7 => .ok (st7.f0, st7.f1)

/-- **Theorem 7 (`withRetagNo_succeeds_and_withRetagYes_causes_stacked_borrows_ub`):**
    Under Stacked Borrows, `WithRetag.no` succeeds with `(33, 22)`, whereas
    `WithRetag.yes` fails already at the read `*p0` (`.tagMissingFromStack 2 0`),
    matching the exact live Miri SB vs TB divergence (`read` UB vs `write` UB). -/
theorem withRetagNo_succeeds_and_withRetagYes_causes_stacked_borrows_ub :
    runSplitRawSB .no = .ok (33, 22) ∧
    runSplitRawSB .yes = .ub (.tagMissingFromStack 2 0) :=
  ⟨rfl, rfl⟩

end DereferEraseDerefTemps

/-! ==========================================================================
    PART II: `Subtyper` (`add_subtyping_projections.rs`)
             Region-Erased HRTB Coercion Insertion Soundness
    ========================================================================== -/

namespace SubtyperSoundness

/-- Region representation distinguishing free/static regions from higher-ranked
    De Bruijn bound regions and erased regions. -/
inductive Region where
  | free (id : Nat)
  | staticR
  | bound (idx : Nat)
  | erased

def Region.beq : Region → Region → Bool
  | .free a, .free b => a == b
  | .staticR, .staticR => true
  | .bound a, .bound b => a == b
  | .erased, .erased => true
  | _, _ => false

theorem Region.beq_refl (r : Region) : Region.beq r r = true := by
  cases r with
  | free a => exact nat_beq_refl a
  | staticR => rfl
  | bound a => exact nat_beq_refl a
  | erased => rfl

theorem Region.beq_eq_true_iff (a b : Region) : Region.beq a b = true ↔ a = b := by
  cases a <;> cases b <;>
    first
    | exact ⟨fun _ => rfl, fun _ => rfl⟩
    | exact ⟨fun h => Bool.noConfusion h, fun h => Region.noConfusion h⟩
    | (constructor
       · intro h; exact congrArg _ ((nat_beq_eq_true_iff _ _).mp h)
       · intro h; injection h with h'; exact (nat_beq_eq_true_iff _ _).mpr h')

/-- MIR type subset capturing scalars, references, 1-arg and 2-arg (possibly
    higher-ranked) function pointers, and tuples. -/
inductive Ty where
  | u8
  | u32
  | refR (r : Region) (inner : Ty)
  | fn1 (boundCount : Nat) (argR retR : Region)
  | fn2 (boundCount : Nat) (arg1R arg2R retR : Region)
  | pair (a b : Ty)

noncomputable def Ty.beq (t1 t2 : Ty) : Bool :=
  @Ty.rec (fun _ => Ty → Bool)
    (fun t => match t with | .u8 => true | _ => false)
    (fun t => match t with | .u32 => true | _ => false)
    (fun r1 _ ih t => match t with | .refR r2 t2 => Region.beq r1 r2 && ih t2 | _ => false)
    (fun k1 a1 r1 t =>
      match t with | .fn1 k2 a2 r2 => (k1 == k2) && Region.beq a1 a2 && Region.beq r1 r2 | _ => false)
    (fun k1 a1 b1 r1 t =>
      match t with
      | .fn2 k2 a2 b2 r2 => (k1 == k2) && Region.beq a1 a2 && Region.beq b1 b2 && Region.beq r1 r2
      | _ => false)
    (fun _ _ iha ihb t => match t with | .pair a2 b2 => iha a2 && ihb b2 | _ => false)
    t1 t2

private theorem Ty.beq_refR (r1 r2 : Region) (t1 t2 : Ty) :
    Ty.beq (.refR r1 t1) (.refR r2 t2) = (Region.beq r1 r2 && Ty.beq t1 t2) := rfl
private theorem Ty.beq_fn1 (k1 k2 : Nat) (a1 a2 r1 r2 : Region) :
    Ty.beq (.fn1 k1 a1 r1) (.fn1 k2 a2 r2) = ((k1 == k2) && Region.beq a1 a2 && Region.beq r1 r2) := rfl
private theorem Ty.beq_fn2 (k1 k2 : Nat) (a1 a2 b1 b2 r1 r2 : Region) :
    Ty.beq (.fn2 k1 a1 b1 r1) (.fn2 k2 a2 b2 r2) =
      ((k1 == k2) && Region.beq a1 a2 && Region.beq b1 b2 && Region.beq r1 r2) := rfl
private theorem Ty.beq_pair (a1 a2 b1 b2 : Ty) :
    Ty.beq (.pair a1 b1) (.pair a2 b2) = (Ty.beq a1 a2 && Ty.beq b1 b2) := rfl

theorem Ty.beq_refl (t : Ty) : Ty.beq t t = true := by
  induction t with
  | u8 => rfl
  | u32 => rfl
  | refR r inner ih => rw [Ty.beq_refR, Region.beq_refl, ih]; rfl
  | fn1 k a r => rw [Ty.beq_fn1, nat_beq_refl, Region.beq_refl, Region.beq_refl]; rfl
  | fn2 k a b r => rw [Ty.beq_fn2, nat_beq_refl, Region.beq_refl, Region.beq_refl, Region.beq_refl]; rfl
  | pair a b iha ihb => rw [Ty.beq_pair, iha, ihb]; rfl

theorem Ty.beq_eq_true_iff (t1 t2 : Ty) : Ty.beq t1 t2 = true ↔ t1 = t2 := by
  induction t1 generalizing t2 with
  | u8 =>
    cases t2 <;>
      first | exact ⟨fun _ => rfl, fun _ => rfl⟩ | exact ⟨fun h => Bool.noConfusion h, fun h => Ty.noConfusion h⟩
  | u32 =>
    cases t2 <;>
      first | exact ⟨fun _ => rfl, fun _ => rfl⟩ | exact ⟨fun h => Bool.noConfusion h, fun h => Ty.noConfusion h⟩
  | refR r1 i1 ih =>
    cases t2 with
    | refR r2 i2 =>
      rw [Ty.beq_refR, Bool.and_eq_true]
      constructor
      · intro ⟨hr, hi⟩
        rw [(Region.beq_eq_true_iff r1 r2).mp hr, (ih i2).mp hi]
      · intro h
        injection h with hr hi
        exact ⟨(Region.beq_eq_true_iff r1 r2).mpr hr, (ih i2).mpr hi⟩
    | _ => exact ⟨fun h => Bool.noConfusion h, fun h => Ty.noConfusion h⟩
  | fn1 k1 a1 r1 =>
    cases t2 with
    | fn1 k2 a2 r2 =>
      rw [Ty.beq_fn1, Bool.and_eq_true, Bool.and_eq_true]
      constructor
      · intro ⟨⟨hk, ha⟩, hr⟩
        rw [(nat_beq_eq_true_iff k1 k2).mp hk,
            (Region.beq_eq_true_iff a1 a2).mp ha,
            (Region.beq_eq_true_iff r1 r2).mp hr]
      · intro h
        injection h with hk ha hr
        exact ⟨⟨(nat_beq_eq_true_iff k1 k2).mpr hk,
                (Region.beq_eq_true_iff a1 a2).mpr ha⟩,
               (Region.beq_eq_true_iff r1 r2).mpr hr⟩
    | _ => exact ⟨fun h => Bool.noConfusion h, fun h => Ty.noConfusion h⟩
  | fn2 k1 a1 b1 r1 =>
    cases t2 with
    | fn2 k2 a2 b2 r2 =>
      rw [Ty.beq_fn2, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
      constructor
      · intro ⟨⟨⟨hk, ha⟩, hb⟩, hr⟩
        rw [(nat_beq_eq_true_iff k1 k2).mp hk,
            (Region.beq_eq_true_iff a1 a2).mp ha,
            (Region.beq_eq_true_iff b1 b2).mp hb,
            (Region.beq_eq_true_iff r1 r2).mp hr]
      · intro h
        injection h with hk ha hb hr
        exact ⟨⟨⟨(nat_beq_eq_true_iff k1 k2).mpr hk,
                 (Region.beq_eq_true_iff a1 a2).mpr ha⟩,
                (Region.beq_eq_true_iff b1 b2).mpr hb⟩,
               (Region.beq_eq_true_iff r1 r2).mpr hr⟩
    | _ => exact ⟨fun h => Bool.noConfusion h, fun h => Ty.noConfusion h⟩
  | pair a1 b1 iha ihb =>
    cases t2 with
    | pair a2 b2 =>
      rw [Ty.beq_pair, Bool.and_eq_true]
      constructor
      · intro ⟨ha, hb⟩
        rw [(iha a2).mp ha, (ihb b2).mp hb]
      · intro h
        injection h with ha hb
        exact ⟨(iha a2).mpr ha, (ihb b2).mpr hb⟩
    | _ => exact ⟨fun h => Bool.noConfusion h, fun h => Ty.noConfusion h⟩

/-- Model of `tcx.erase_and_anonymize_regions` (`add_subtyping_projections.rs:39-40`):
    erases all free and `'static` regions to `.erased` while preserving
    higher-ranked binder counts and `.bound idx` variables. -/
def eraseRegion : Region → Region
  | .free _ => .erased
  | .staticR => .erased
  | .bound idx => .bound idx
  | .erased => .erased

noncomputable def eraseAndAnonymize (t : Ty) : Ty :=
  @Ty.rec (fun _ => Ty)
    .u8
    .u32
    (fun r _ ih => .refR (eraseRegion r) ih)
    (fun k a r => .fn1 k (eraseRegion a) (eraseRegion r))
    (fun k a b r => .fn2 k (eraseRegion a) (eraseRegion b) (eraseRegion r))
    (fun _ _ iha ihb => .pair iha ihb)
    t

private theorem eraseAndAnonymize_refR (r : Region) (t : Ty) :
    eraseAndAnonymize (.refR r t) = .refR (eraseRegion r) (eraseAndAnonymize t) := rfl
private theorem eraseAndAnonymize_fn1 (k : Nat) (a r : Region) :
    eraseAndAnonymize (.fn1 k a r) = .fn1 k (eraseRegion a) (eraseRegion r) := rfl
private theorem eraseAndAnonymize_fn2 (k : Nat) (a b r : Region) :
    eraseAndAnonymize (.fn2 k a b r) = .fn2 k (eraseRegion a) (eraseRegion b) (eraseRegion r) := rfl
private theorem eraseAndAnonymize_pair (a b : Ty) :
    eraseAndAnonymize (.pair a b) = .pair (eraseAndAnonymize a) (eraseAndAnonymize b) := rfl

theorem eraseRegion_idempotent (r : Region) : eraseRegion (eraseRegion r) = eraseRegion r := by
  cases r <;> rfl

/-- **Theorem 8 (`eraseAndAnonymize_idempotent`):**
    Region erasure and anonymization is strictly idempotent. -/
theorem eraseAndAnonymize_idempotent (t : Ty) :
    eraseAndAnonymize (eraseAndAnonymize t) = eraseAndAnonymize t := by
  induction t with
  | u8 => rfl
  | u32 => rfl
  | refR r inner ih =>
    rw [eraseAndAnonymize_refR, eraseAndAnonymize_refR, eraseRegion_idempotent, ih]
  | fn1 k a r =>
    rw [eraseAndAnonymize_fn1, eraseAndAnonymize_fn1, eraseRegion_idempotent, eraseRegion_idempotent]
  | fn2 k a b r =>
    rw [eraseAndAnonymize_fn2, eraseAndAnonymize_fn2,
        eraseRegion_idempotent, eraseRegion_idempotent, eraseRegion_idempotent]
  | pair a b iha ihb =>
    rw [eraseAndAnonymize_pair, eraseAndAnonymize_pair, iha, ihb]

/-- Declarative Rust subtyping relation (`rust-lang/reference` `r[subtype.kinds]`
    and `r[subtype.higher-ranked]`). -/
inductive IsSubtype : Ty → Ty → Prop where
  | refl (t : Ty) : IsSubtype t t
  | refStatic (r : Region) (t1 t2 : Ty) (hNotBound : eraseRegion r = .erased) :
      IsSubtype t1 t2 → IsSubtype (.refR .staticR t1) (.refR r t2)
  | refSame (r : Region) (t1 t2 : Ty) :
      IsSubtype t1 t2 → IsSubtype (.refR r t1) (.refR r t2)
  | fn1Inst (r : Region) :
      IsSubtype (.fn1 1 (.bound 0) (.bound 0)) (.fn1 0 r r)
  | fn2Collapse :
      IsSubtype (.fn2 2 (.bound 0) (.bound 1) (.bound 0))
                (.fn2 1 (.bound 0) (.bound 0) (.bound 0))
  | pairCong {a1 a2 b1 b2 : Ty} :
      IsSubtype a1 a2 → IsSubtype b1 b2 → IsSubtype (.pair a1 b1) (.pair a2 b2)

/-- **Theorem 9 (`isSubtype_eraseAndAnonymize`):**
    Region erasure and anonymization preserves the subtyping judgment. -/
theorem isSubtype_eraseAndAnonymize {s t : Ty} (h : IsSubtype s t) :
    IsSubtype (eraseAndAnonymize s) (eraseAndAnonymize t) := by
  induction h with
  | refl t => exact .refl (eraseAndAnonymize t)
  | refStatic r t1 t2 hNb _ ih =>
    simp only [eraseAndAnonymize, hNb]
    exact .refSame .erased _ _ ih
  | refSame r t1 t2 _ ih =>
    exact .refSame (eraseRegion r) _ _ ih
  | fn1Inst r =>
    exact .fn1Inst (eraseRegion r)
  | fn2Collapse =>
    exact .fn2Collapse
  | pairCong _ _ iha ihb =>
    exact .pairCong iha ihb

/-- Runtime value representation (erased of lifetimes; `CastKind::Subtype` is a
    representation-preserving identity on runtime values per `interpret/cast.rs:192-200`). -/
inductive RtVal where
  | scalar (n : Nat)
  | fnAddr (symId : Nat)
  | pairVal (a b : RtVal)

/-- Rvalue calculus for `Subtyper`. -/
inductive SubRvalue where
  | useLocal (l : Nat)
  | makePair (l1 l2 : Nat)
  | genericReborrow (l : Nat)
  | castSubtype (srcLocal : Nat) (targetTy : Ty)

/-- Assignment statement annotated with `isDerefTemp` on its destination local
    (`add_subtyping_projections.rs:27-34`). -/
structure AssignStmt where
  dstLocal : Nat
  dstIsDerefTemp : Bool
  rvalue : SubRvalue

abbrev TyEnv := Nat → Ty
abbrev RtStore := Nat → RtVal

def updateTyEnv (env : TyEnv) (l : Nat) (t : Ty) : TyEnv :=
  fun k => if k == l then t else env k

def updateRtStore (st : RtStore) (l : Nat) (v : RtVal) : RtStore :=
  fun k => if k == l then v else st k

def rvalueTy (env : TyEnv) : SubRvalue → Ty
  | .useLocal l => env l
  | .makePair l1 l2 => .pair (env l1) (env l2)
  | .genericReborrow l => env l
  | .castSubtype _ targetTy => targetTy

def evalSubRvalue (st : RtStore) : SubRvalue → RtVal
  | .useLocal l => st l
  | .makePair l1 l2 => .pairVal (st l1) (st l2)
  | .genericReborrow l => st l
  | .castSubtype srcLocal _ => st srcLocal

def execAssignList (st : RtStore) (stmts : List AssignStmt) : RtStore :=
  stmts.foldr
    (fun s ih curSt => ih (updateRtStore curSt s.dstLocal (evalSubRvalue curSt s.rvalue)))
    (fun curSt => curSt)
    st

private theorem execAssignList_nil (st : RtStore) : execAssignList st [] = st := rfl
private theorem execAssignList_cons (st : RtStore) (s : AssignStmt) (rest : List AssignStmt) :
    execAssignList st (s :: rest) =
      execAssignList (updateRtStore st s.dstLocal (evalSubRvalue st s.rvalue)) rest := rfl

/-- Exact model of `SubTypeChecker::visit_assign` (`add_subtyping_projections.rs:21-49`). -/
noncomputable def subtyperAssign (tmpLocal : Nat) (env : TyEnv) (s : AssignStmt) :
    TyEnv × List AssignStmt :=
  match s.rvalue with
  | .genericReborrow _ => (env, [s])
  | _ =>
    if s.dstIsDerefTemp then
      (env, [s])
    else
      let placeTy := eraseAndAnonymize (env s.dstLocal)
      let rvalTy := eraseAndAnonymize (rvalueTy env s.rvalue)
      if Ty.beq placeTy rvalTy then
        (env, [s])
      else
        let env' := updateTyEnv env tmpLocal rvalTy
        let s1 : AssignStmt :=
          { dstLocal := tmpLocal, dstIsDerefTemp := false, rvalue := s.rvalue }
        let s2 : AssignStmt :=
          { dstLocal := s.dstLocal
            dstIsDerefTemp := false
            rvalue := .castSubtype tmpLocal placeTy }
        (env', [s1, s2])

/-- Analysis-phase assignment well-typedness precondition (matches `validate.rs`
    in `Analysis(PostCleanup)` before `Subtyper`: `IsSubtype rval_ty place_ty`,
    plus any existing `CastKind::Subtype` satisfies `IsSubtype`, and `DerefTemp`
    only receives `CopyForDeref` / never `CastKind::Subtype` per `validate.rs:1501-1507`). -/
def AnalysisAssignWellTyped (env : TyEnv) (s : AssignStmt) : Prop :=
  IsSubtype (rvalueTy env s.rvalue) (env s.dstLocal) ∧
  match s.rvalue with
  | .castSubtype src targetTy =>
    s.dstIsDerefTemp = false ∧ IsSubtype (env src) targetTy
  | _ => True

/-- Strict `Runtime` MIR assignment well-typedness postcondition:
    - Non-`genericReborrow`, non-`DerefTemp` assignments satisfy exact erased-type
      equality `eraseAndAnonymize (env dst) = eraseAndAnonymize (rvalueTy env rv)`.
    - Every `CastKind::Subtype` additionally satisfies `IsSubtype` (`validate.rs:1446-1453`). -/
def RuntimeAssignWellTyped (env : TyEnv) (s : AssignStmt) : Prop :=
  match s.rvalue with
  | .genericReborrow _ => True
  | .castSubtype src targetTy =>
    eraseAndAnonymize (env s.dstLocal) = eraseAndAnonymize targetTy ∧
    IsSubtype (eraseAndAnonymize (env src)) (eraseAndAnonymize targetTy)
  | rv =>
    s.dstIsDerefTemp = true ∨
    eraseAndAnonymize (env s.dstLocal) = eraseAndAnonymize (rvalueTy env rv)

def freshForStmt (tmp : Nat) (s : AssignStmt) : Prop :=
  tmp ≠ s.dstLocal ∧
  match s.rvalue with
  | .useLocal l => tmp ≠ l
  | .makePair l1 l2 => tmp ≠ l1 ∧ tmp ≠ l2
  | .genericReborrow l => tmp ≠ l
  | .castSubtype l _ => tmp ≠ l

private theorem rvalueTy_update_fresh (env : TyEnv) (tmp : Nat) (t : Ty) (s : AssignStmt)
    (hFresh : freshForStmt tmp s) :
    rvalueTy (updateTyEnv env tmp t) s.rvalue = rvalueTy env s.rvalue := by
  rcases hFresh with ⟨_, hRv⟩
  cases hR : s.rvalue with
  | useLocal l =>
    rw [hR] at hRv
    simp [rvalueTy, updateTyEnv, nat_beq_false_of_ne (Ne.symm hRv)]
  | makePair l1 l2 =>
    rw [hR] at hRv
    simp [rvalueTy, updateTyEnv,
          nat_beq_false_of_ne (Ne.symm hRv.1),
          nat_beq_false_of_ne (Ne.symm hRv.2)]
  | genericReborrow l =>
    rw [hR] at hRv
    simp [rvalueTy, updateTyEnv, nat_beq_false_of_ne (Ne.symm hRv)]
  | castSubtype l ty =>
    rfl

/-- **Theorem 10 (`subtyper_explicit_cast_typing_and_eval_equiv`):**
    For any analysis-well-typed assignment `s` and fresh temporary `tmp`,
    `Subtyper` outputs statements ALL satisfying strict `RuntimeAssignWellTyped`
    (exact erased-type equality on every `Assign`, plus valid `IsSubtype` on every
    `CastKind::Subtype`) AND preserving exact runtime store semantics at every
    original local `k ≠ tmp`. -/
theorem subtyper_explicit_cast_typing_and_eval_equiv
    (tmp : Nat) (env : TyEnv) (st : RtStore) (s : AssignStmt)
    (hFresh : freshForStmt tmp s)
    (hWf : AnalysisAssignWellTyped env s) :
    let (env', outStmts) := subtyperAssign tmp env s
    (∀ stmt ∈ outStmts, RuntimeAssignWellTyped env' stmt) ∧
    (∀ k, k ≠ tmp → execAssignList st outStmts k = execAssignList st [s] k) := by
  cases s with
  | mk dstLocal dstIsDerefTemp rvalue =>
    rcases hWf with ⟨hSub, hCastWf⟩
    cases rvalue with
    | genericReborrow l =>
      simp only [subtyperAssign]
      refine ⟨?_, fun _ _ => trivial⟩
      intro stmt hMem
      simp only [List.mem_singleton] at hMem
      subst hMem
      trivial
    | useLocal l =>
      cases dstIsDerefTemp with
      | true =>
        simp only [subtyperAssign, ite_true]
        refine ⟨?_, fun _ _ => trivial⟩
        intro stmt hMem
        simp only [List.mem_singleton] at hMem
        subst hMem
        exact Or.inl rfl
      | false =>
        simp only [subtyperAssign, Bool.false_eq_true, ite_false]
        cases hEq : Ty.beq (eraseAndAnonymize (env dstLocal)) (eraseAndAnonymize (rvalueTy env (.useLocal l))) with
        | true =>
          have hTyEq : eraseAndAnonymize (env dstLocal) = eraseAndAnonymize (env l) :=
            (Ty.beq_eq_true_iff _ _).mp hEq
          simp only [ite_true]
          refine ⟨?_, fun _ _ => trivial⟩
          intro stmt hMem
          simp only [List.mem_singleton] at hMem
          subst hMem
          exact Or.inr hTyEq
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have hSubErased : IsSubtype (eraseAndAnonymize (env l)) (eraseAndAnonymize (env dstLocal)) :=
            isSubtype_eraseAndAnonymize hSub
          have hLNe : (l == tmp) = false := nat_beq_false_of_ne (Ne.symm hFresh.2)
          have hDstNe : (dstLocal == tmp) = false := nat_beq_false_of_ne (Ne.symm hFresh.1)
          refine ⟨?_, ?_⟩
          · intro stmt hMem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
            rcases hMem with rfl | rfl
            · right
              simp only [updateTyEnv, rvalueTy, nat_beq_refl, ite_true, hLNe, Bool.false_eq_true,
                         ite_false, eraseAndAnonymize_idempotent]
            · refine ⟨?_, ?_⟩
              · simp only [updateTyEnv, hDstNe, Bool.false_eq_true, ite_false, eraseAndAnonymize_idempotent]
              · simp only [updateTyEnv, rvalueTy, nat_beq_refl, ite_true, eraseAndAnonymize_idempotent]
                exact hSubErased
          · intro k hNe
            rw [execAssignList_cons, execAssignList_cons, execAssignList_nil,
                execAssignList_cons, execAssignList_nil]
            simp only [evalSubRvalue, updateRtStore, nat_beq_refl, ite_true]
            have hK : (k == tmp) = false := nat_beq_false_of_ne hNe
            cases hKD : (k == dstLocal) with
            | true => rfl
            | false => simp only [Bool.false_eq_true, ite_false, hK]
    | makePair l1 l2 =>
      cases dstIsDerefTemp with
      | true =>
        simp only [subtyperAssign, ite_true]
        refine ⟨?_, fun _ _ => trivial⟩
        intro stmt hMem
        simp only [List.mem_singleton] at hMem
        subst hMem
        exact Or.inl rfl
      | false =>
        simp only [subtyperAssign, Bool.false_eq_true, ite_false]
        cases hEq : Ty.beq (eraseAndAnonymize (env dstLocal)) (eraseAndAnonymize (rvalueTy env (.makePair l1 l2))) with
        | true =>
          have hTyEq : eraseAndAnonymize (env dstLocal) = eraseAndAnonymize (.pair (env l1) (env l2)) :=
            (Ty.beq_eq_true_iff _ _).mp hEq
          simp only [ite_true]
          refine ⟨?_, fun _ _ => trivial⟩
          intro stmt hMem
          simp only [List.mem_singleton] at hMem
          subst hMem
          exact Or.inr hTyEq
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have hSubErased :
              IsSubtype (eraseAndAnonymize (.pair (env l1) (env l2))) (eraseAndAnonymize (env dstLocal)) :=
            isSubtype_eraseAndAnonymize hSub
          have hL1Ne : (l1 == tmp) = false := nat_beq_false_of_ne (Ne.symm hFresh.2.1)
          have hL2Ne : (l2 == tmp) = false := nat_beq_false_of_ne (Ne.symm hFresh.2.2)
          have hDstNe : (dstLocal == tmp) = false := nat_beq_false_of_ne (Ne.symm hFresh.1)
          refine ⟨?_, ?_⟩
          · intro stmt hMem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
            rcases hMem with rfl | rfl
            · right
              simp only [updateTyEnv, rvalueTy, nat_beq_refl, ite_true, hL1Ne, hL2Ne,
                         Bool.false_eq_true, ite_false, eraseAndAnonymize_idempotent]
            · refine ⟨?_, ?_⟩
              · simp only [updateTyEnv, hDstNe, Bool.false_eq_true, ite_false, eraseAndAnonymize_idempotent]
              · simp only [updateTyEnv, rvalueTy, nat_beq_refl, ite_true, eraseAndAnonymize_idempotent]
                exact hSubErased
          · intro k hNe
            rw [execAssignList_cons, execAssignList_cons, execAssignList_nil,
                execAssignList_cons, execAssignList_nil]
            simp only [evalSubRvalue, updateRtStore, nat_beq_refl, ite_true]
            have hK : (k == tmp) = false := nat_beq_false_of_ne hNe
            cases hKD : (k == dstLocal) with
            | true => rfl
            | false => simp only [Bool.false_eq_true, ite_false, hK]
    | castSubtype src targetTy =>
      cases dstIsDerefTemp with
      | true =>
        exact Bool.noConfusion hCastWf.1
      | false =>
        simp only [subtyperAssign, Bool.false_eq_true, ite_false]
        cases hEq : Ty.beq (eraseAndAnonymize (env dstLocal)) (eraseAndAnonymize (rvalueTy env (.castSubtype src targetTy))) with
        | true =>
          have hTyEq : eraseAndAnonymize (env dstLocal) = eraseAndAnonymize targetTy :=
            (Ty.beq_eq_true_iff _ _).mp hEq
          simp only [ite_true]
          refine ⟨?_, fun _ _ => trivial⟩
          intro stmt hMem
          simp only [List.mem_singleton] at hMem
          subst hMem
          exact ⟨hTyEq, isSubtype_eraseAndAnonymize hCastWf.2⟩
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          have hSubErased : IsSubtype (eraseAndAnonymize targetTy) (eraseAndAnonymize (env dstLocal)) :=
            isSubtype_eraseAndAnonymize hSub
          have hSrcNe : (src == tmp) = false := nat_beq_false_of_ne (Ne.symm hFresh.2)
          have hDstNe : (dstLocal == tmp) = false := nat_beq_false_of_ne (Ne.symm hFresh.1)
          refine ⟨?_, ?_⟩
          · intro stmt hMem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hMem
            rcases hMem with rfl | rfl
            · refine ⟨?_, ?_⟩
              · simp only [updateTyEnv, rvalueTy, nat_beq_refl, ite_true, eraseAndAnonymize_idempotent]
              · simp only [updateTyEnv, hSrcNe, Bool.false_eq_true, ite_false]
                exact isSubtype_eraseAndAnonymize hCastWf.2
            · refine ⟨?_, ?_⟩
              · simp only [updateTyEnv, hDstNe, Bool.false_eq_true, ite_false, eraseAndAnonymize_idempotent]
              · simp only [updateTyEnv, rvalueTy, nat_beq_refl, ite_true, eraseAndAnonymize_idempotent]
                exact hSubErased
          · intro k hNe
            rw [execAssignList_cons, execAssignList_cons, execAssignList_nil,
                execAssignList_cons, execAssignList_nil]
            simp only [evalSubRvalue, updateRtStore, nat_beq_refl, ite_true]
            have hK : (k == tmp) = false := nat_beq_false_of_ne hNe
            cases hKD : (k == dstLocal) with
            | true => rfl
            | false => simp only [Bool.false_eq_true, ite_false, hK]

/-- **Theorem 11 (`subtyper_plain_region_variance_no_cast`):**
    Free-region variance (`&'static u8` -> `&'a u8`) equates under
    `eraseAndAnonymize`, so `Subtyper` inserts zero `CastKind::Subtype` casts. -/
theorem subtyper_plain_region_variance_no_cast :
    let env : TyEnv := fun l => if l == 1 then .refR .staticR .u8 else .refR (.free 0) .u8
    let s : AssignStmt := { dstLocal := 2, dstIsDerefTemp := false, rvalue := .useLocal 1 }
    (subtyperAssign 10 env s).2 = [s] := rfl

/-- **Theorem 12 (`subtyper_hrtb_tuple_and_binder_collapse_insert_casts`):**
    Both `(for<'a> fn(&'a u8) -> &'a u8, u32) -> (fn(&'static u8) -> &'static u8, u32)`
    and `for<'a,'b> fn(&'a u8, &'b u8) -> &'a u8 -> for<'c> fn(&'c u8, &'c u8) -> &'c u8`
    remain distinct after `eraseAndAnonymize` and receive explicit `CastKind::Subtype`
    coercions (matching live `Subtyper.after.mir` and `TYPEID_DIFF=true`). -/
theorem subtyper_hrtb_tuple_and_binder_collapse_insert_casts :
    let hrtbFn : Ty := .fn1 1 (.bound 0) (.bound 0)
    let staticFn : Ty := .fn1 0 .staticR .staticR
    let envTuple : TyEnv := fun l =>
      if l == 1 then hrtbFn else if l == 2 then .u32 else .pair staticFn .u32
    let sTuple : AssignStmt := { dstLocal := 3, dstIsDerefTemp := false, rvalue := .makePair 1 2 }
    let envCollapse : TyEnv := fun l =>
      if l == 1 then .fn2 2 (.bound 0) (.bound 1) (.bound 0)
      else .fn2 1 (.bound 0) (.bound 0) (.bound 0)
    let sCollapse : AssignStmt := { dstLocal := 2, dstIsDerefTemp := false, rvalue := .useLocal 1 }
    (eraseAndAnonymize hrtbFn ≠ eraseAndAnonymize staticFn) ∧
    (subtyperAssign 10 envTuple sTuple).2 =
      [ { dstLocal := 10, dstIsDerefTemp := false, rvalue := .makePair 1 2 },
        { dstLocal := 3, dstIsDerefTemp := false,
          rvalue := .castSubtype 10 (.pair (.fn1 0 .erased .erased) .u32) } ] ∧
    (subtyperAssign 10 envCollapse sCollapse).2 =
      [ { dstLocal := 10, dstIsDerefTemp := false, rvalue := .useLocal 1 },
        { dstLocal := 2, dstIsDerefTemp := false,
          rvalue := .castSubtype 10 (.fn2 1 (.bound 0) (.bound 0) (.bound 0)) } ] := by
  refine ⟨?_, rfl, rfl⟩
  intro hEq
  cases hEq

end SubtyperSoundness

/-! ==========================================================================
    PART III: `LintAndRemoveUninhabited` (`lint_and_remove_uninhabited.rs`,
              `inhabitedness/mod.rs`, `inhabited_predicate.rs`)
              Module-Scoped `isInhabitedFrom`, Call-Target Pruning Soundness,
              and Definite-Initialization (`E0381`) SemVer Monotonicity
    ========================================================================== -/

namespace VisiblyUninhabitedCalls

/-- Module identifier. -/
abbrev ModId := Nat

/-- Field visibility (`rustc_middle::ty::Visibility`). -/
inductive Vis where
  | pubVis
  | restricted (defMod : ModId)

/-- Mirror of `rustc_middle::ty::inhabitedness::InhabitedPredicate`
    (`inhabitedness/mod.rs:124`, `inhabited_predicate.rs:91-98`). -/
inductive InhabPred where
  | pTrue
  | pFalse
  | notInMod (m : ModId)
  | pAnd (a b : InhabPred)
  | pOr (a b : InhabPred)

/-- `InhabitedPredicate::apply` (`inhabited_predicate.rs:39-98`): evaluates
    visibility-scoped inhabitedness from `callerMod`. -/
noncomputable def evalPred (inMod : ModId → ModId → Bool) (callerMod : ModId) (p : InhabPred) : Bool :=
  @InhabPred.rec (fun _ => Bool)
    true
    false
    (fun m => !(inMod callerMod m))
    (fun _ _ iha ihb => iha && ihb)
    (fun _ _ iha ihb => iha || ihb)
    p

/-- `InhabitedPredicate::apply_ignore_module` (`inhabited_predicate.rs:74-80`):
    treats every `in_module` query as `true` (so `NotInModule _` evaluates to `false`). -/
noncomputable def evalPredIgnoreMod (p : InhabPred) : Bool :=
  @InhabPred.rec (fun _ => Bool)
    true
    false
    (fun _ => false)
    (fun _ _ iha ihb => iha && ihb)
    (fun _ _ iha ihb => iha || ihb)
    p

/-- **Theorem 13 (`evalPred_false_implies_ignoreMod_false`):**
    If an `InhabPred` evaluates to `false` in some module `callerMod`, it MUST
    evaluate to `false` when module visibility guards are ignored (i.e.,
    visibly uninhabited implies privately uninhabited). -/
theorem evalPred_false_implies_ignoreMod_false
    (inMod : ModId → ModId → Bool) (callerMod : ModId) (p : InhabPred)
    (h : evalPred inMod callerMod p = false) :
    evalPredIgnoreMod p = false := by
  induction p with
  | pTrue => exact Bool.noConfusion h
  | pFalse => rfl
  | notInMod _ => rfl
  | pAnd a b iha ihb =>
    simp only [evalPred, Bool.and_eq_false_iff] at h
    simp only [evalPredIgnoreMod, Bool.and_eq_false_iff]
    cases h with
    | inl ha => exact Or.inl (iha ha)
    | inr hb => exact Or.inr (ihb hb)
  | pOr a b iha ihb =>
    simp only [evalPred, Bool.or_eq_false_iff] at h
    simp only [evalPredIgnoreMod, Bool.or_eq_false_iff]
    exact ⟨iha h.1, ihb h.2⟩

/-- Type algebra covering `!`, scalars, references (`&T`), enums (0, 1, or 2
    variants — enum variant fields are always visible per `inhabitedness/mod.rs:119-121`),
    and structs with visibility-annotated fields (`mod.rs:122-125`). -/
inductive AdtTy where
  | never
  | u32Ty
  | refTy (pointee : AdtTy)
  | emptyEnum
  | enum1 (v0 : AdtTy)
  | enum2 (v0 v1 : AdtTy)
  | struct1 (vis : Vis) (f0 : AdtTy)
  | struct2 (vis0 : Vis) (f0 : AdtTy) (vis1 : Vis) (f1 : AdtTy)

/-- `Ty::inhabited_predicate` (`inhabitedness/mod.rs:106-168`):
    notice `refTy _` returns `pTrue` (`mod.rs:166`), and `struct` restricted
    fields guard with `notInMod from || pred` (`mod.rs:124`). -/
def fieldPred (vis : Vis) (p : InhabPred) : InhabPred :=
  match vis with
  | .pubVis => p
  | .restricted m => .pOr (.notInMod m) p

noncomputable def inhabPred (ty : AdtTy) : InhabPred :=
  @AdtTy.rec (fun _ => InhabPred)
    .pFalse
    .pTrue
    (fun _ _ => .pTrue)
    .pFalse
    (fun _ ih => ih)
    (fun _ _ ih0 ih1 => .pOr ih0 ih1)
    (fun vis _ ih => fieldPred vis ih)
    (fun vis0 _ vis1 _ ih0 ih1 => .pAnd (fieldPred vis0 ih0) (fieldPred vis1 ih1))
    ty

/-- Tier 1: `Ty::is_inhabited_from` (`inhabitedness/mod.rs:209-216`). -/
noncomputable def isInhabitedFrom (inMod : ModId → ModId → Bool) (callerMod : ModId) (ty : AdtTy) : Bool :=
  evalPred inMod callerMod (inhabPred ty)

/-- Tier 2: `Ty::is_privately_uninhabited` (`inhabitedness/mod.rs:222-228`). -/
noncomputable def isPrivatelyUninhabited (ty : AdtTy) : Bool :=
  !(evalPredIgnoreMod (inhabPred ty))

/-- Tier 3: `Ty::is_opsem_inhabited` (`inhabitedness/mod.rs:238-398`),
    recursing through references (`mod.rs:300-308`) and ignoring visibility. -/
noncomputable def isOpsemInhabited (ty : AdtTy) : Bool :=
  @AdtTy.rec (fun _ => Bool)
    false
    true
    (fun _ ih => ih)
    false
    (fun _ ih => ih)
    (fun _ _ ih0 ih1 => ih0 || ih1)
    (fun _ _ ih => ih)
    (fun _ _ _ _ ih0 ih1 => ih0 && ih1)
    ty

/-- **Theorem 14 (`privatelyUninhabited_implies_opsemUninhabited`):**
    If a type is privately uninhabited (`evalPredIgnoreMod (inhabPred ty) = false`),
    it MUST be opsem-uninhabited (`isOpsemInhabited ty = false`). -/
private theorem isOpsemInhabited_enum2 (v0 v1 : AdtTy) :
    isOpsemInhabited (.enum2 v0 v1) = (isOpsemInhabited v0 || isOpsemInhabited v1) := rfl
private theorem isOpsemInhabited_struct2 (vis0 vis1 : Vis) (f0 f1 : AdtTy) :
    isOpsemInhabited (.struct2 vis0 f0 vis1 f1) = (isOpsemInhabited f0 && isOpsemInhabited f1) := rfl
private theorem evalPredIgnoreMod_pOr (a b : InhabPred) :
    evalPredIgnoreMod (.pOr a b) = (evalPredIgnoreMod a || evalPredIgnoreMod b) := rfl
private theorem evalPredIgnoreMod_pAnd (a b : InhabPred) :
    evalPredIgnoreMod (.pAnd a b) = (evalPredIgnoreMod a && evalPredIgnoreMod b) := rfl
private theorem evalPredIgnoreMod_notInMod (m : ModId) :
    evalPredIgnoreMod (.notInMod m) = false := rfl

theorem privatelyUninhabited_implies_opsemUninhabited (ty : AdtTy)
    (h : evalPredIgnoreMod (inhabPred ty) = false) :
    isOpsemInhabited ty = false := by
  induction ty with
  | never => rfl
  | u32Ty => exact Bool.noConfusion h
  | refTy _ _ => exact Bool.noConfusion h
  | emptyEnum => rfl
  | enum1 v0 ih => exact ih h
  | enum2 v0 v1 ih0 ih1 =>
    rw [show inhabPred (.enum2 v0 v1) = .pOr (inhabPred v0) (inhabPred v1) from rfl,
        evalPredIgnoreMod_pOr, Bool.or_eq_false_iff] at h
    rw [isOpsemInhabited_enum2, Bool.or_eq_false_iff]
    exact ⟨ih0 h.1, ih1 h.2⟩
  | struct1 vis f0 ih =>
    cases vis with
    | pubVis => exact ih h
    | restricted m =>
      rw [show inhabPred (.struct1 (.restricted m) f0) = .pOr (.notInMod m) (inhabPred f0) from rfl,
          evalPredIgnoreMod_pOr, evalPredIgnoreMod_notInMod, Bool.false_or] at h
      exact ih h
  | struct2 vis0 f0 vis1 f1 ih0 ih1 =>
    rw [show inhabPred (.struct2 vis0 f0 vis1 f1) =
          .pAnd (fieldPred vis0 (inhabPred f0)) (fieldPred vis1 (inhabPred f1)) from rfl,
        evalPredIgnoreMod_pAnd, Bool.and_eq_false_iff] at h
    rw [isOpsemInhabited_struct2, Bool.and_eq_false_iff]
    cases h with
    | inl h0 =>
      cases vis0 with
      | pubVis => exact Or.inl (ih0 h0)
      | restricted m =>
        rw [show fieldPred (.restricted m) (inhabPred f0) = .pOr (.notInMod m) (inhabPred f0) from rfl,
            evalPredIgnoreMod_pOr, evalPredIgnoreMod_notInMod, Bool.false_or] at h0
        exact Or.inl (ih0 h0)
    | inr h1 =>
      cases vis1 with
      | pubVis => exact Or.inr (ih1 h1)
      | restricted m =>
        rw [show fieldPred (.restricted m) (inhabPred f1) = .pOr (.notInMod m) (inhabPred f1) from rfl,
            evalPredIgnoreMod_pOr, evalPredIgnoreMod_notInMod, Bool.false_or] at h1
        exact Or.inr (ih1 h1)

/-- **Theorem 15 (`visiblyUninhabited_implies_opsemUninhabited`):**
    Full three-tier implication chain:
      `isInhabitedFrom inMod m ty = false`
      `→ isPrivatelyUninhabited ty = true`
      `→ isOpsemInhabited ty = false`. -/
theorem visiblyUninhabited_implies_opsemUninhabited
    (inMod : ModId → ModId → Bool) (callerMod : ModId) (ty : AdtTy)
    (hVis : isInhabitedFrom inMod callerMod ty = false) :
    isPrivatelyUninhabited ty = true ∧ isOpsemInhabited ty = false := by
  have hIgn := evalPred_false_implies_ignoreMod_false inMod callerMod (inhabPred ty) hVis
  exact ⟨by simp [isPrivatelyUninhabited, hIgn],
         privatelyUninhabited_implies_opsemUninhabited ty hIgn⟩

/-- **Theorem 16 (`refNever_opsemUninhab_but_visiblyInhab`):**
    Strict separation witness matching our live `ref_void.rs` probe:
    `&'static !` (and `&'static PublicVoid`) is opsem-uninhabited
    (`isOpsemInhabited = false`), yet `isInhabitedFrom = true` for EVERY module
    hierarchy and caller module! -/
theorem refNever_opsemUninhab_but_visiblyInhab
    (inMod : ModId → ModId → Bool) (callerMod : ModId) :
    isOpsemInhabited (.refTy .never) = false ∧
    isInhabitedFrom inMod callerMod (.refTy .never) = true ∧
    isOpsemInhabited (.refTy .emptyEnum) = false ∧
    isInhabitedFrom inMod callerMod (.refTy .emptyEnum) = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Operational Semantics of Valid Return Values & Call-Target Pruning -/

/-- Valid operational values inhabiting `AdtTy`. There is NO constructor for
    `.never` or `.emptyEnum`, and `.refTy pointee` requires a valid pointee
    value (matching `is_opsem_inhabited` / Rust reference validity invariant). -/
inductive ValidVal : AdtTy → Type where
  | mkU32 (n : Nat) : ValidVal .u32Ty
  | mkRef {p : AdtTy} (v : ValidVal p) : ValidVal (.refTy p)
  | mkEnum1 {v0 : AdtTy} (v : ValidVal v0) : ValidVal (.enum1 v0)
  | mkEnum2L {v0 v1 : AdtTy} (v : ValidVal v0) : ValidVal (.enum2 v0 v1)
  | mkEnum2R {v0 v1 : AdtTy} (v : ValidVal v1) : ValidVal (.enum2 v0 v1)
  | mkStruct1 {vis : Vis} {f0 : AdtTy} (v : ValidVal f0) : ValidVal (.struct1 vis f0)
  | mkStruct2 {vis0 vis1 : Vis} {f0 f1 : AdtTy} (v0 : ValidVal f0) (v1 : ValidVal f1) :
      ValidVal (.struct2 vis0 f0 vis1 f1)

/-- Any type inhabited by a `ValidVal` MUST have `isOpsemInhabited = true`. -/
theorem validVal_implies_opsemInhabited {ty : AdtTy} (v : ValidVal ty) :
    isOpsemInhabited ty = true := by
  induction v with
  | mkU32 _ => rfl
  | mkRef _ ih => exact ih
  | mkEnum1 _ ih => exact ih
  | mkEnum2L _ ih => rw [isOpsemInhabited_enum2, ih]; rfl
  | mkEnum2R _ ih => rw [isOpsemInhabited_enum2, ih, Bool.or_true]
  | mkStruct1 _ ih => exact ih
  | mkStruct2 _ _ ih0 ih1 => rw [isOpsemInhabited_struct2, ih0, ih1]; rfl

/-- Callee execution outcome: either diverges/unwinds or returns a valid value
    of its declared return type `ty`. -/
inductive CalleeOutcome (ty : AdtTy) where
  | diverges
  | returned (v : ValidVal ty)

/-- MIR `TerminatorKind::Call` return-edge metadata. -/
structure CallTerm where
  retTy : AdtTy
  target : Option Nat

/-- Outcome of evaluating a `CallTerm` continuation (`eval_context.rs:525-531`):
    returning when `target = none` raises `UB(Unreachable)`. -/
inductive CallContOutcome where
  | diverges
  | jumpTo (bb : Nat)
  | ubUnreachable

def evalCallCont {ty : AdtTy} (target : Option Nat) (out : CalleeOutcome ty) : CallContOutcome :=
  match out with
  | .diverges => .diverges
  | .returned _ =>
    match target with
    | some bb => .jumpTo bb
    | none => .ubUnreachable

/-- Exact model of `LintAndRemoveUninhabited` (`lint_and_remove_uninhabited.rs:24-56`):
    - Prunes `target` to `none` iff `!isInhabitedFrom inMod callerMod term.retTy`.
    - Emits `UnreachableDueToUninhabited` lint iff pruned, `retTy ≠ .never`, and
      `isInhabitedFrom inMod callerMod enclosingRetTy = true` (issue #149571). -/
def isNeverTy : AdtTy → Bool
  | .never => true
  | _ => false

noncomputable def lintAndRemoveCall
    (inMod : ModId → ModId → Bool) (callerMod : ModId)
    (enclosingRetTy : AdtTy) (term : CallTerm) : CallTerm × Bool :=
  match term.target with
  | none => (term, false)
  | some _ =>
    if !(isInhabitedFrom inMod callerMod term.retTy) then
      let emitLint :=
        !(isNeverTy term.retTy) && isInhabitedFrom inMod callerMod enclosingRetTy
      ({ term with target := none }, emitLint)
    else
      (term, false)

/-- Definite-initialization (`E0381`) gate on the 2-block pattern
    `let x: u32; callee(); x`:
    `bb1` (the use of uninitialized `x`) is reachable iff `term.target.isSome`.
    Thus borrowck accepts the function iff `term.target.isNone`. -/
def passesDefiniteInit (term : CallTerm) : Bool :=
  term.target.isNone

/-- **Theorem 17 (`visiblyUninhabited_call_prune_opsem_sound`):**
    For EVERY module hierarchy, caller module, enclosing return type, call
    terminator, and valid callee outcome, `lintAndRemoveCall` is **100%
    operationally equivalent** (`evalCallCont pruned.target out = evalCallCont orig.target out`)
    — it NEVER introduces `ubUnreachable` on any valid execution! -/
theorem visiblyUninhabited_call_prune_opsem_sound
    (inMod : ModId → ModId → Bool) (callerMod : ModId)
    (enclosingRetTy : AdtTy) (term : CallTerm)
    (out : CalleeOutcome term.retTy) :
    evalCallCont (lintAndRemoveCall inMod callerMod enclosingRetTy term).1.target out =
      evalCallCont term.target out := by
  cases out with
  | diverges => rfl
  | returned v =>
    have hOpsem : isOpsemInhabited term.retTy = true := validVal_implies_opsemInhabited v
    cases term with
    | mk retTy target =>
      cases target with
      | none => rfl
      | some bb =>
        simp only [lintAndRemoveCall]
        cases hVis : isInhabitedFrom inMod callerMod retTy with
        | true => rfl
        | false =>
          have hContrad := (visiblyUninhabited_implies_opsemUninhabited inMod callerMod retTy hVis).2
          rw [hOpsem] at hContrad
          exact Bool.noConfusion hContrad

/-- **Theorem 18 (`visiblyUninhabited_call_prune_sound_and_semver_monotone`):**
    Master theorem combining all four core guarantees of `LintAndRemoveUninhabited`:
    1. **Operational soundness:** pruning never changes valid execution outcomes.
    2. **Publicly uninhabited (`PublicVoid`):** `target` is pruned (`none`),
       definite-init accepts (`passesDefiniteInit = true`, `rc = 0`), and the
       `UnreachableDueToUninhabited` lint fires when enclosing return is `u32`.
    3. **Privately uninhabited visibility split (`OpaqueUninhabited(PrivateVoid)`):**
       - Outside defining module `defMod` (`inMod outer defMod = false`):
         `target` is KEPT (`some bb`), so definite-init REJECTS (`E0381`, `rc = 1`).
       - Inside `defMod` or any child module `child` (`inMod child defMod = true`):
         `target` IS PRUNED (`none`), so definite-init ACCEPTS (`rc = 0`).
    4. **SemVer monotonicity:** replacing the private field of
       `struct1 (.restricted defMod) oldField` with ANY `newField` (e.g., turning
       `PrivateVoid` into `u32`) leaves `isInhabitedFrom`, `lintAndRemoveCall`,
       and `passesDefiniteInit` **identically invariant** for every external
       caller `outer` (`inMod outer defMod = false`)! -/
theorem visiblyUninhabited_call_prune_sound_and_semver_monotone
    (inMod : ModId → ModId → Bool)
    (defMod outerMod childMod : ModId)
    (hOuter : inMod outerMod defMod = false)
    (hChild : inMod childMod defMod = true)
    (bb : Nat) (oldField newField : AdtTy) :
    let pubVoidTerm : CallTerm := { retTy := .emptyEnum, target := some bb }
    let privOldTerm : CallTerm :=
      { retTy := .struct1 (.restricted defMod) oldField, target := some bb }
    let privNewTerm : CallTerm :=
      { retTy := .struct1 (.restricted defMod) newField, target := some bb }
    let privVoidTerm : CallTerm :=
      { retTy := .struct1 (.restricted defMod) .emptyEnum, target := some bb }
    -- (1) PublicVoid pruned + passes definite-init + emits lint
    (lintAndRemoveCall inMod outerMod .u32Ty pubVoidTerm =
      ({ retTy := .emptyEnum, target := none }, true) ∧
     passesDefiniteInit (lintAndRemoveCall inMod outerMod .u32Ty pubVoidTerm).1 = true) ∧
    -- (2) OpaqueUninhabited outside defMod: target kept + fails definite-init (E0381)
    (lintAndRemoveCall inMod outerMod .u32Ty privVoidTerm = (privVoidTerm, false) ∧
     passesDefiniteInit (lintAndRemoveCall inMod outerMod .u32Ty privVoidTerm).1 = false) ∧
    -- (3) OpaqueUninhabited inside childMod (or defMod): target pruned + passes definite-init
    (lintAndRemoveCall inMod childMod .u32Ty privVoidTerm =
      ({ retTy := .struct1 (.restricted defMod) .emptyEnum, target := none }, true) ∧
     passesDefiniteInit (lintAndRemoveCall inMod childMod .u32Ty privVoidTerm).1 = true) ∧
    -- (4) SemVer monotonicity: arbitrary private-field evolution is invisible externally
    (isInhabitedFrom inMod outerMod privOldTerm.retTy = true ∧
     isInhabitedFrom inMod outerMod privNewTerm.retTy = true ∧
     passesDefiniteInit (lintAndRemoveCall inMod outerMod .u32Ty privOldTerm).1 =
       passesDefiniteInit (lintAndRemoveCall inMod outerMod .u32Ty privNewTerm).1) := by
  refine ⟨⟨rfl, rfl⟩, ?_, ?_, ?_⟩
  · have hInhab : isInhabitedFrom inMod outerMod (.struct1 (.restricted defMod) .emptyEnum) = true := by
      simp [isInhabitedFrom, inhabPred, fieldPred, evalPred, hOuter]
    simp [lintAndRemoveCall, passesDefiniteInit, hInhab]
  · have hUninhab : isInhabitedFrom inMod childMod (.struct1 (.restricted defMod) .emptyEnum) = false := by
      simp [isInhabitedFrom, inhabPred, fieldPred, evalPred, hChild]
    have hRetInhab : isInhabitedFrom inMod childMod .u32Ty = true := rfl
    simp [lintAndRemoveCall, passesDefiniteInit, isNeverTy, hUninhab, hRetInhab]
  · have hOld : isInhabitedFrom inMod outerMod (.struct1 (.restricted defMod) oldField) = true := by
      simp [isInhabitedFrom, inhabPred, fieldPred, evalPred, hOuter]
    have hNew : isInhabitedFrom inMod outerMod (.struct1 (.restricted defMod) newField) = true := by
      simp [isInhabitedFrom, inhabPred, fieldPred, evalPred, hOuter]
    refine ⟨hOld, hNew, ?_⟩
    simp [lintAndRemoveCall, passesDefiniteInit, hOld, hNew]

/-- **Theorem 19 (`enclosingUninhabited_suppresses_lint_preserves_pruning`):**
    Models rust-lang/rust#149571 (`lint_and_remove_uninhabited.rs:24-25, 47`):
    when the enclosing function's return type is visibly uninhabited
    (`PublicVoid`), `lintAndRemoveCall` STILL prunes `target := none` (so
    definite-init accepts) while suppressing `UnreachableDueToUninhabited`
    (`emitLint = false`). -/
theorem enclosingUninhabited_suppresses_lint_preserves_pruning
    (inMod : ModId → ModId → Bool) (callerMod : ModId) (bb : Nat) :
    let term : CallTerm := { retTy := .emptyEnum, target := some bb }
    lintAndRemoveCall inMod callerMod .emptyEnum term =
      ({ retTy := .emptyEnum, target := none }, false) ∧
    passesDefiniteInit (lintAndRemoveCall inMod callerMod .emptyEnum term).1 = true :=
  ⟨rfl, rfl⟩

end VisiblyUninhabitedCalls

/-! ==========================================================================
    PART IV: End-to-End Phase-Transition Summary & Axiom Audit
    ========================================================================== -/

/-- Combined capstone theorem packaging the three required MIR phase-transition
    contracts (`Derefer`+`EraseDerefTemps`, `Subtyper`, `LintAndRemoveUninhabited`). -/
theorem phase_transition_required_desugarings_capstone :
    -- I. WithRetag::No succeeds under TB and SB while WithRetag::Yes triggers UB in both
    (DereferEraseDerefTemps.runSplitRawTB .no = .ok (33, 22) ∧
     DereferEraseDerefTemps.runSplitRawTB .yes = .ub (.frozenWriteForbidden 1 0) ∧
     DereferEraseDerefTemps.runSplitRawSB .no = .ok (33, 22) ∧
     DereferEraseDerefTemps.runSplitRawSB .yes = .ub (.tagMissingFromStack 2 0)) ∧
    -- II. Subtyper distinguishes HRTB after region erasure and omits cast on plain region variance
    (SubtyperSoundness.eraseAndAnonymize (.fn1 1 (.bound 0) (.bound 0)) ≠
     SubtyperSoundness.eraseAndAnonymize (.fn1 0 .staticR .staticR)) ∧
    -- III. Opsem-uninhabited `&!` remains visibility-inhabited
    (VisiblyUninhabitedCalls.isOpsemInhabited (.refTy .never) = false ∧
     VisiblyUninhabitedCalls.isInhabitedFrom (fun _ _ => false) 0 (.refTy .never) = true) := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_, ⟨rfl, rfl⟩⟩
  intro h
  cases h

#print axioms DereferEraseDerefTemps.dereferPlace_normalForm
#print axioms DereferEraseDerefTemps.dereferPlace_skips_varDebugInfo
#print axioms DereferEraseDerefTemps.eraseDerefTemps_eliminates_and_preserves
#print axioms DereferEraseDerefTemps.derefer_then_eraseNoRetag_preserves_tree_borrows
#print axioms DereferEraseDerefTemps.withRetagNo_succeeds_and_withRetagYes_causes_tree_borrows_ub
#print axioms DereferEraseDerefTemps.withRetagNo_succeeds_and_withRetagYes_causes_stacked_borrows_ub
#print axioms SubtyperSoundness.eraseAndAnonymize_idempotent
#print axioms SubtyperSoundness.isSubtype_eraseAndAnonymize
#print axioms SubtyperSoundness.subtyper_explicit_cast_typing_and_eval_equiv
#print axioms SubtyperSoundness.subtyper_plain_region_variance_no_cast
#print axioms SubtyperSoundness.subtyper_hrtb_tuple_and_binder_collapse_insert_casts
#print axioms VisiblyUninhabitedCalls.visiblyUninhabited_implies_opsemUninhabited
#print axioms VisiblyUninhabitedCalls.refNever_opsemUninhab_but_visiblyInhab
#print axioms VisiblyUninhabitedCalls.visiblyUninhabited_call_prune_opsem_sound
#print axioms VisiblyUninhabitedCalls.visiblyUninhabited_call_prune_sound_and_semver_monotone
#print axioms VisiblyUninhabitedCalls.enclosingUninhabited_suppresses_lint_preserves_pruning
#print axioms phase_transition_required_desugarings_capstone

end RustcMirPhaseTransitions
