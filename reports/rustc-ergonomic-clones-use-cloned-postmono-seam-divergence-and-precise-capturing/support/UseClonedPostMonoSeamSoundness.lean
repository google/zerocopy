/-!
# Operational Seam Soundness for `rustc` `ergonomic_clones` (`UseCloned` / `CallSource::Use`)
  and Edition 2024 `use<...>` Precise Capturing

This standalone Lean `v4.34.1` module formalizes:
1. The post-monomorphization `CallSource::Use` MIR-to-codegen rewrite
   (`rustc_codegen_ssa::mir::optimize_use_clone`) relative to
   `Runtime(PostCleanup)` / Miri MIR execution, proving that `optimize_use_clone`
   refines `PostCleanup` MIR semantics on `Copy ∩ UseCloned` types if and only if
   the type's `Clone` implementation satisfies observational `PureBitwiseClone`
   (`optimize_use_clone_refines_postcleanup_iff_pure_bitwise_clone`), together
   with multi-block CFG preservation (`optimize_use_clone_preserves_cfg`).
2. A relational nondeterministic `PostCleanup` `CallSource::Use` seam envelope
   (`NondetStep` / `NondetEval`) that provably envelops both Miri
   (`postCleanupEval`) and native `rustc_codegen_ssa` binaries (`codegenEval`)
   across arbitrary multi-block CFGs and arbitrary (including unlawful or
   panicking) safe-Rust `Clone` implementations
   (`nondet_call_source_use_envelops_both_miri_and_codegen`), plus the safe-code
   `UnwindAction::Unreachable` UB divergence theorem
   (`unwind_unreachable_safe_code_ub_divergence`).
3. Edition 2021 vs. Edition 2024 RPIT lifetime-capture defaults, opaque variance
   (`Variance.invariant` vs. `Variance.bivariant`), `check_opaque_precise_captures`
   well-formedness (`precise_capture_well_formed_iff_all_ty_params_retained`),
   and hidden-type substitution safety.
4. Constructive sharpness counterexamples:
   - `ce1_safe_sneaky_copy_refutes_deterministic_postcleanup_mir_seam`
   - `ce2_omitted_ty_param_in_use_breaks_hidden_type_subst_e0792`

Design invariants:
- Zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`,
  zero `native_decide`, zero `partial def`, zero `._unsafe_rec`.
- All recursive definitions on inductive types are marked `noncomputable def`
  so Lean does not synthesize `partial` `._unsafe_rec` codegen helpers, and
  all equality decision procedures are written explicitly rather than via
  `deriving DecidableEq` on recursive inductives.
-/

namespace UseClonedPostMonoSeamSoundness

/-! ## Part 1: MIR Operational Model for `CallSource::Use` and `optimize_use_clone` -/

/-- Source of a `TerminatorKind::Call` in `rustc_middle::mir::CallSource`. -/
inductive CallSource where
  | overloadedOperator
  | matchCmp
  | misc
  | use_
  | normal

/-- Unwind action on a `TerminatorKind::Call` (`rustc_middle::mir::UnwindAction`). -/
inductive UnwindAction where
  | continue_
  | unreachable
  | terminate
  | cleanup (bb : Nat)

/-- Concrete monomorphized type tags modeled in our operational seam. -/
inductive TyTag where
  | sneakyCopy
  | lawfulCopy
  | panicCopy
  | panicNonCopy
  | rcHandle
  | ownedString

/-- Manual structural equality on `TyTag`. -/
noncomputable def TyTag.beq : TyTag → TyTag → Bool
  | .sneakyCopy, .sneakyCopy => true
  | .lawfulCopy, .lawfulCopy => true
  | .panicCopy, .panicCopy => true
  | .panicNonCopy, .panicNonCopy => true
  | .rcHandle, .rcHandle => true
  | .ownedString, .ownedString => true
  | _, _ => false

theorem TyTag.beq_eq_true_iff (a b : TyTag) : TyTag.beq a b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

/-- Explicit `DecidableEq` on `TyTag` without `deriving`. -/
noncomputable def decEqTyTag (a b : TyTag) : Decidable (a = b) :=
  match a, b with
  | .sneakyCopy, .sneakyCopy => isTrue rfl
  | .lawfulCopy, .lawfulCopy => isTrue rfl
  | .panicCopy, .panicCopy => isTrue rfl
  | .panicNonCopy, .panicNonCopy => isTrue rfl
  | .rcHandle, .rcHandle => isTrue rfl
  | .ownedString, .ownedString => isTrue rfl
  | .sneakyCopy, .lawfulCopy | .sneakyCopy, .panicCopy | .sneakyCopy, .panicNonCopy
  | .sneakyCopy, .rcHandle | .sneakyCopy, .ownedString
  | .lawfulCopy, .sneakyCopy | .lawfulCopy, .panicCopy | .lawfulCopy, .panicNonCopy
  | .lawfulCopy, .rcHandle | .lawfulCopy, .ownedString
  | .panicCopy, .sneakyCopy | .panicCopy, .lawfulCopy | .panicCopy, .panicNonCopy
  | .panicCopy, .rcHandle | .panicCopy, .ownedString
  | .panicNonCopy, .sneakyCopy | .panicNonCopy, .lawfulCopy | .panicNonCopy, .panicCopy
  | .panicNonCopy, .rcHandle | .panicNonCopy, .ownedString
  | .rcHandle, .sneakyCopy | .rcHandle, .lawfulCopy | .rcHandle, .panicCopy
  | .rcHandle, .panicNonCopy | .rcHandle, .ownedString
  | .ownedString, .sneakyCopy | .ownedString, .lawfulCopy | .ownedString, .panicCopy
  | .ownedString, .panicNonCopy | .ownedString, .rcHandle =>
    isFalse (fun h => by cases h)

/-- Runtime values (scalars and pairs) carried in MIR local slots. -/
inductive Val where
  | scalar (n : Nat)
  | pair (a b : Nat)
  | uninit

/-- Operational effect of `<T as Clone>::clone(&x)` for a monomorphized type. -/
inductive CloneBehavior where
  /-- Pure bitwise copy: returns identical value, zero observable counter delta, never panics. -/
  | pureBitwise
  /-- Custom `Clone`: adds `valueDelta` to scalar payload and increments `cloneCalls` by `callDelta`. -/
  | custom (valueDelta : Nat) (callDelta : Nat)
  /-- Panicking `Clone::clone` (triggers stack unwinding). -/
  | panics

/-- Trait and `Clone` metadata for a concrete monomorphized type. -/
structure TypeInfo where
  isCopy : Bool
  isUseCloned : Bool
  cloneBehavior : CloneBehavior

/-- Type environment mapping each concrete monomorphized type to its `Copy`,
    `UseCloned`, and `Clone` behavior. -/
abbrev TypeTable := TyTag → TypeInfo

/-- MIR statements modeled inside a basic block. -/
inductive MirStmt where
  /-- Direct bitwise copy `dst := copy src` (emitted by `optimize_use_clone` or concrete `Copy` lowering). -/
  | assignCopy (dst src : Nat)
  /-- Build a pair `(src1, src2)` into `dst` (models `_0 = (move _2, move _4)`). -/
  | assignPair (dst src1 src2 : Nat)

/-- MIR basic-block terminators. -/
inductive MirTerm where
  /-- Function call terminator carrying `call_source` and `unwind` action. -/
  | call (source : CallSource) (argTy : TyTag) (src dst : Nat)
      (target : Nat) (unwind : UnwindAction)
  /-- Unconditional control-flow transfer. -/
  | goto (target : Nat)
  /-- Return value stored in local `0`. -/
  | return_

/-- A MIR basic block (`statements` followed by `terminator`). -/
structure BasicBlock where
  stmts : List MirStmt
  term : MirTerm

/-- A MIR function body is a list of basic blocks indexed from `0`. -/
abbrev MirBody := List BasicBlock

/-- Machine state: current basic-block index, local slot map, and observable
    atomic clone-call counter (`CLONE_CALLS`). -/
structure MachineState where
  bb : Nat
  locals : Nat → Val
  cloneCalls : Nat

/-- Update one local slot in a local environment. -/
noncomputable def updateLocal (locals : Nat → Val) (idx : Nat) (v : Val) : Nat → Val :=
  fun k => if Nat.beq k idx then v else locals k

/-- Terminal or intermediate execution outcome. -/
inductive Outcome where
  | returned (val : Val) (cloneCalls : Nat)
  | panicked (cloneCalls : Nat)
  | ubUnwindPastUnreachable (cloneCalls : Nat)
  | outOfFuel
  | stuck

/-- Structural list indexing (avoids any partial helper). -/
noncomputable def getBlock? : List BasicBlock → Nat → Option BasicBlock
  | [], _ => none
  | b :: _, 0 => some b
  | _ :: bs, n + 1 => getBlock? bs n

/-- Execute a single MIR statement on a local store. -/
noncomputable def execStmt (locals : Nat → Val) : MirStmt → Option (Nat → Val)
  | .assignCopy dst src =>
    match locals src with
    | .uninit => none
    | v => some (updateLocal locals dst v)
  | .assignPair dst src1 src2 =>
    match locals src1, locals src2 with
    | .scalar a, .scalar b => some (updateLocal locals dst (.pair a b))
    | _, _ => none

/-- Execute a list of MIR statements sequentially. -/
noncomputable def execStmts : List MirStmt → (Nat → Val) → Option (Nat → Val)
  | [], locals => some locals
  | s :: ss, locals =>
    match execStmt locals s with
    | none => none
    | some locals' => execStmts ss locals'

theorem execStmts_append (xs ys : List MirStmt) (locals : Nat → Val) :
    execStmts (xs ++ ys) locals =
      match execStmts xs locals with
      | none => none
      | some locals' => execStmts ys locals' := by
  induction xs generalizing locals with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.cons_append, execStmts]
    cases execStmt locals s with
    | none => rfl
    | some locals' => exact ih locals'

/-- Apply a type's `Clone::clone` semantics to value `v` and global counter `calls`. -/
inductive CloneStepResult where
  | ok (val : Val) (newCalls : Nat)
  | unwound

noncomputable def evalCloneBehavior (beh : CloneBehavior) (v : Val) (calls : Nat) :
    Option CloneStepResult :=
  match v with
  | .uninit => none
  | .scalar x =>
    match beh with
    | .pureBitwise => some (.ok (.scalar x) calls)
    | .custom dv dc => some (.ok (.scalar (x + dv)) (calls + dc))
    | .panics => some .unwound
  | .pair a b =>
    match beh with
    | .pureBitwise => some (.ok (.pair a b) calls)
    | .custom dv dc => some (.ok (.pair (a + dv) b) (calls + dc))
    | .panics => some .unwound

/-- Single-block step result in deterministic `Runtime(PostCleanup)` / Miri semantics. -/
inductive StepOutcome where
  | next (st : MachineState)
  | done (out : Outcome)

/-- Execute one basic block under deterministic `Runtime(PostCleanup)` / Miri semantics:
    matches `rustc_const_eval/src/interpret/step.rs:543-567` (ignores `call_source`)
    and `eval_context.rs:555-561` (`UnwindAction::Unreachable` triggers UB). -/
noncomputable def postCleanupStepBlock (tbl : TypeTable) (blk : BasicBlock)
    (st : MachineState) : StepOutcome :=
  match execStmts blk.stmts st.locals with
  | none => .done .stuck
  | some locals' =>
    match blk.term with
    | .goto target => .next { bb := target, locals := locals', cloneCalls := st.cloneCalls }
    | .return_ =>
      match locals' 0 with
      | .uninit => .done .stuck
      | v => .done (.returned v st.cloneCalls)
    | .call _source argTy src dst target unwind =>
      match evalCloneBehavior (tbl argTy).cloneBehavior (locals' src) st.cloneCalls with
      | none => .done .stuck
      | some (.ok v' calls') =>
        .next {
          bb := target
          locals := updateLocal locals' dst v'
          cloneCalls := calls'
        }
      | some .unwound =>
        match unwind with
        | .unreachable => .done (.ubUnwindPastUnreachable st.cloneCalls)
        | .continue_ => .done (.panicked st.cloneCalls)
        | .terminate => .done (.panicked st.cloneCalls)
        | .cleanup cbb => .next { bb := cbb, locals := locals', cloneCalls := st.cloneCalls }

/-- Deterministic `Runtime(PostCleanup)` / Miri single-block step. -/
noncomputable def postCleanupStep (tbl : TypeTable) (body : MirBody)
    (st : MachineState) : StepOutcome :=
  match getBlock? body st.bb with
  | none => .done .stuck
  | some blk => postCleanupStepBlock tbl blk st

/-- Fuel-bounded execution of `postCleanupStep` (Miri operational semantics). -/
noncomputable def postCleanupEval (tbl : TypeTable) (body : MirBody) :
    Nat → MachineState → Outcome
  | 0, _ => .outOfFuel
  | fuel + 1, st =>
    match postCleanupStep tbl body st with
    | .done out => out
    | .next st' => postCleanupEval tbl body fuel st'

/-- Exact post-monomorphization MIR rewrite modeling
    `rustc_codegen_ssa::mir::optimize_use_clone`
    (`compiler/rustc_codegen_ssa/src/mir/mod.rs:352-407` at `14210df0e2` /
    `390-445` at `342d74463a`):
    unconditionally rewrites `TerminatorKind::Call { call_source: CallSource::Use, .. }`
    whose inner argument type satisfies `type_is_copy_modulo_regions` into
    `StatementKind::Assign(dst = Copy(src))` + `TerminatorKind::Goto(target)`. -/
noncomputable def optimizeUseCloneBlock (tbl : TypeTable) : BasicBlock → BasicBlock
  | ⟨stmts, .call .use_ argTy src dst target unwind⟩ =>
    if (tbl argTy).isCopy then
      ⟨stmts ++ [.assignCopy dst src], .goto target⟩
    else
      ⟨stmts, .call .use_ argTy src dst target unwind⟩
  | blk => blk

noncomputable def optimizeUseClone (tbl : TypeTable) : MirBody → MirBody
  | [] => []
  | b :: bs => optimizeUseCloneBlock tbl b :: optimizeUseClone tbl bs

theorem getBlock?_optimizeUseClone (tbl : TypeTable) (body : MirBody) (idx : Nat) :
    getBlock? (optimizeUseClone tbl body) idx =
      Option.map (optimizeUseCloneBlock tbl) (getBlock? body idx) := by
  induction body generalizing idx with
  | nil => cases idx <;> rfl
  | cons b bs ih =>
    cases idx with
    | zero => rfl
    | succ n => exact ih n

/-- Native `-C opt-level=0` / `-O` codegen operational semantics:
    runs `optimizeUseClone` post-monomorphization before executing MIR. -/
noncomputable def codegenEval (tbl : TypeTable) (body : MirBody)
    (fuel : Nat) (st : MachineState) : Outcome :=
  postCleanupEval tbl (optimizeUseClone tbl body) fuel st

/-- Observational bitwise-copy law for `Copy ∩ UseCloned` types:
    a type's `Clone::clone` behaves identically to a bitwise copy (no value delta,
    no observable side-effect calls, no panic/unwind). -/
def PureBitwiseClone (tbl : TypeTable) (ty : TyTag) : Prop :=
  (tbl ty).isCopy = true → (tbl ty).isUseCloned = true →
    match (tbl ty).cloneBehavior with
    | .pureBitwise => True
    | .custom dv dc => dv = 0 ∧ dc = 0
    | .panics => False

/-- All `Copy ∩ UseCloned` types in `tbl` satisfy `PureBitwiseClone`. -/
def TableLawful (tbl : TypeTable) : Prop :=
  ∀ ty : TyTag, PureBitwiseClone tbl ty

/-- Every `CallSource::Use` call on a `Copy` type in `body` targets a `UseCloned` type
    (enforced statically by `rustc_mir_build::builder::expr::into`, which emits
    `CallSource::Use` only in the `type_is_use_cloned_modulo_regions` branch). -/
def BodyUseCallsWellTyped (tbl : TypeTable) (body : MirBody) : Prop :=
  ∀ idx blk argTy src dst target unwind,
    getBlock? body idx = some blk →
    blk.term = .call .use_ argTy src dst target unwind →
    (tbl argTy).isUseCloned = true

theorem evalCloneBehavior_eq_copy_of_pure (tbl : TypeTable) (ty : TyTag)
    (hCopy : (tbl ty).isCopy = true) (hUse : (tbl ty).isUseCloned = true)
    (hPure : PureBitwiseClone tbl ty) (v : Val) (calls : Nat) :
    evalCloneBehavior (tbl ty).cloneBehavior v calls =
      match v with
      | .uninit => none
      | v' => some (.ok v' calls) := by
  have hBeh := hPure hCopy hUse
  cases hcb : (tbl ty).cloneBehavior with
  | pureBitwise =>
    cases v <;> simp [evalCloneBehavior]
  | custom dv dc =>
    rw [hcb] at hBeh
    rcases hBeh with ⟨hdv, hdc⟩
    subst hdv; subst hdc
    cases v <;> simp [evalCloneBehavior]
  | panics =>
    rw [hcb] at hBeh
    cases hBeh

/-- Multi-block CFG single-step agreement when `TableLawful` holds. -/
theorem optimize_use_clone_step_eq_of_lawful (tbl : TypeTable) (body : MirBody)
    (hLawful : TableLawful tbl) (hWT : BodyUseCallsWellTyped tbl body)
    (st : MachineState) :
    postCleanupStep tbl (optimizeUseClone tbl body) st = postCleanupStep tbl body st := by
  unfold postCleanupStep
  rw [getBlock?_optimizeUseClone]
  cases hBlk : getBlock? body st.bb with
  | none => rfl
  | some blk =>
    rcases blk with ⟨stmts, term⟩
    simp only [Option.map]
    cases term with
    | goto target => rfl
    | return_ => rfl
    | call source argTy src dst target unwind =>
      cases source with
      | overloadedOperator => rfl
      | matchCmp => rfl
      | misc => rfl
      | normal => rfl
      | use_ =>
        unfold optimizeUseCloneBlock
        cases hCopy : (tbl argTy).isCopy with
        | false => simp [hCopy]
        | true =>
          simp only [hCopy, ↓reduceIte, postCleanupStepBlock]
          rw [execStmts_append]
          cases hStmts : execStmts stmts st.locals with
          | none => rfl
          | some locals' =>
            simp only [execStmts, execStmt]
            have hUse : (tbl argTy).isUseCloned = true :=
              hWT st.bb ⟨stmts, .call .use_ argTy src dst target unwind⟩
                argTy src dst target unwind hBlk rfl
            rw [evalCloneBehavior_eq_copy_of_pure tbl argTy hCopy hUse (hLawful argTy)]
            cases locals' src with
            | uninit => rfl
            | scalar n => rfl
            | pair a b => rfl

/-- Multi-block CFG preservation: if every `Copy ∩ UseCloned` type satisfies
    `PureBitwiseClone`, then `codegenEval` (`optimize_use_clone`) agrees with
    `postCleanupEval` (Miri) on every fuel bound and initial state. -/
theorem optimize_use_clone_preserves_cfg (tbl : TypeTable) (body : MirBody)
    (hLawful : TableLawful tbl) (hWT : BodyUseCallsWellTyped tbl body)
    (fuel : Nat) (st : MachineState) :
    codegenEval tbl body fuel st = postCleanupEval tbl body fuel st := by
  induction fuel generalizing st with
  | zero => rfl
  | succ f ih =>
    unfold codegenEval postCleanupEval
    rw [optimize_use_clone_step_eq_of_lawful tbl body hLawful hWT st]
    cases postCleanupStep tbl body st with
    | done out => rfl
    | next st' => exact ih st'

/-- Canonical generic `fn generic_dup<T: UseCloned>(x: T) -> (T, T) { (x.use, x) }`
    MIR body monomorphized at `ty`:
    - `bb0`: `_2 = <ty as Clone>::clone(&_1) -> [return: bb1, unwind unreachable]`
      with `CallSource::Use`
    - `bb1`: `_0 = (_2, _1); return` -/
noncomputable def genericDupBody (ty : TyTag) : MirBody :=
  [
    { stmts := [], term := .call .use_ ty 1 2 1 .unreachable },
    { stmts := [.assignPair 0 2 1], term := .return_ }
  ]

/-- Initial state for `generic_dup(scalar x)` with global counter `calls`. -/
noncomputable def mkDupInitState (x : Nat) (calls : Nat) : MachineState :=
  { bb := 0, locals := updateLocal (fun _ => .uninit) 1 (.scalar x), cloneCalls := calls }

theorem genericDupBody_wellTyped (tbl : TypeTable) (ty : TyTag)
    (hUse : (tbl ty).isUseCloned = true) :
    BodyUseCallsWellTyped tbl (genericDupBody ty) := by
  intro idx blk argTy src dst target unwind hBlk hTerm
  cases idx with
  | zero =>
    simp only [genericDupBody, getBlock?] at hBlk
    cases hBlk
    simp only at hTerm
    cases hTerm
    exact hUse
  | succ idx' =>
    cases idx' with
    | zero =>
      simp only [genericDupBody, getBlock?] at hBlk
      cases hBlk
      simp only at hTerm
      cases hTerm
    | succ _ =>
      simp only [genericDupBody, getBlock?] at hBlk
      cases hBlk

/-- **Theorem 1 (Post-Mono `CallSource::Use` Refinement Iff `PureBitwiseClone`):**
    For any type `ty` implementing both `Copy` and `UseCloned`, native codegen
    (`codegenEval` after `optimize_use_clone`) produces the same observable
    outcome as `Runtime(PostCleanup)` MIR (`postCleanupEval` / Miri) on
    `generic_dup::<ty>(x)` across all inputs `x` and initial counter states
    `calls` **if and only if** `PureBitwiseClone tbl ty` holds. -/
theorem optimize_use_clone_refines_postcleanup_iff_pure_bitwise_clone
    (tbl : TypeTable) (ty : TyTag)
    (hCopy : (tbl ty).isCopy = true)
    (hUse : (tbl ty).isUseCloned = true) :
    (∀ x calls,
        codegenEval tbl (genericDupBody ty) 3 (mkDupInitState x calls) =
        postCleanupEval tbl (genericDupBody ty) 3 (mkDupInitState x calls))
      ↔ PureBitwiseClone tbl ty := by
  constructor
  · intro hAgree
    unfold PureBitwiseClone
    intro _ _
    have h0 := hAgree 7 0
    cases hcb : (tbl ty).cloneBehavior with
    | pureBitwise => trivial
    | custom dv dc =>
      simp only [codegenEval, optimizeUseClone, optimizeUseCloneBlock, genericDupBody,
        hCopy, ↓reduceIte, Bool.false_eq_true, List.nil_append, postCleanupEval,
        postCleanupStep, postCleanupStepBlock, getBlock?, execStmts, execStmt,
        mkDupInitState, updateLocal, Nat.beq, evalCloneBehavior, hcb] at h0
      injection h0 with hVal hCalls
      injection hVal with hFirst _
      have hdv : dv = 0 := Nat.add_left_cancel (show 7 + dv = 7 + 0 from hFirst.symm)
      have hdc : dc = 0 := by
        simpa [Nat.zero_add] using hCalls.symm
      exact ⟨hdv, hdc⟩
    | panics =>
      simp only [codegenEval, optimizeUseClone, optimizeUseCloneBlock, genericDupBody,
        hCopy, ↓reduceIte, Bool.false_eq_true, List.nil_append, postCleanupEval,
        postCleanupStep, postCleanupStepBlock, getBlock?, execStmts, execStmt,
        mkDupInitState, updateLocal, Nat.beq, evalCloneBehavior, hcb] at h0
      cases h0
  · intro hPure x calls
    have hBeh := hPure hCopy hUse
    cases hcb : (tbl ty).cloneBehavior with
    | pureBitwise =>
      simp only [codegenEval, optimizeUseClone, optimizeUseCloneBlock, genericDupBody,
        hCopy, ↓reduceIte, Bool.false_eq_true, List.nil_append, postCleanupEval,
        postCleanupStep, postCleanupStepBlock, getBlock?, execStmts, execStmt,
        mkDupInitState, updateLocal, Nat.beq, evalCloneBehavior, hcb]
    | custom dv dc =>
      rw [hcb] at hBeh
      rcases hBeh with ⟨hdv, hdc⟩
      subst hdv; subst hdc
      simp only [codegenEval, optimizeUseClone, optimizeUseCloneBlock, genericDupBody,
        hCopy, ↓reduceIte, Bool.false_eq_true, List.nil_append, postCleanupEval,
        postCleanupStep, postCleanupStepBlock, getBlock?, execStmts, execStmt,
        mkDupInitState, updateLocal, Nat.beq, evalCloneBehavior, hcb, Nat.add_zero]
    | panics =>
      rw [hcb] at hBeh
      cases hBeh

/-! ## Part 2: Nondeterministic `PostCleanup` `CallSource::Use` Seam Envelope -/

/-- Relational single-block transition for the hardened `PostCleanup` MIR seam:
    on `TerminatorKind::Call { call_source: CallSource::Use, .. }` with a `Copy`
    argument type, the semantics nondeterministically permits **either**
    (a) executing the `Clone::clone` call (`postCleanupStep`, matching Miri), or
    (b) eliding the call via direct bitwise copy + `goto target` (matching
        `rustc_codegen_ssa::mir::optimize_use_clone`). -/
inductive NondetStep (tbl : TypeTable) (body : MirBody) :
    MachineState → StepOutcome → Prop where
  | miriBranch (st : MachineState) :
      NondetStep tbl body st (postCleanupStep tbl body st)
  | codegenElideUseBranch (st : MachineState) (blk : BasicBlock)
      (argTy : TyTag) (src dst target : Nat) (unwind : UnwindAction)
      (locals' : Nat → Val) (v : Val) :
      getBlock? body st.bb = some blk →
      execStmts blk.stmts st.locals = some locals' →
      blk.term = .call .use_ argTy src dst target unwind →
      (tbl argTy).isCopy = true →
      locals' src = v →
      v ≠ .uninit →
      NondetStep tbl body st
        (.next { bb := target, locals := updateLocal locals' dst v, cloneCalls := st.cloneCalls })
  | codegenElideUseStuck (st : MachineState) (blk : BasicBlock)
      (argTy : TyTag) (src dst target : Nat) (unwind : UnwindAction)
      (locals' : Nat → Val) :
      getBlock? body st.bb = some blk →
      execStmts blk.stmts st.locals = some locals' →
      blk.term = .call .use_ argTy src dst target unwind →
      (tbl argTy).isCopy = true →
      locals' src = .uninit →
      NondetStep tbl body st (.done .stuck)

/-- Relational fuel-bounded evaluation over `NondetStep`. -/
inductive NondetEval (tbl : TypeTable) (body : MirBody) :
    Nat → MachineState → Outcome → Prop where
  | zero (st : MachineState) :
      NondetEval tbl body 0 st .outOfFuel
  | done (fuel : Nat) (st : MachineState) (out : Outcome) :
      NondetStep tbl body st (.done out) →
      NondetEval tbl body (fuel + 1) st out
  | step (fuel : Nat) (st st' : MachineState) (out : Outcome) :
      NondetStep tbl body st (.next st') →
      NondetEval tbl body fuel st' out →
      NondetEval tbl body (fuel + 1) st out

theorem codegenStep_in_nondetStep (tbl : TypeTable) (body : MirBody) (st : MachineState) :
    NondetStep tbl body st (postCleanupStep tbl (optimizeUseClone tbl body) st) := by
  unfold postCleanupStep
  rw [getBlock?_optimizeUseClone]
  cases hBlk : getBlock? body st.bb with
  | none =>
    have hEq : postCleanupStep tbl body st = .done .stuck := by
      simp [postCleanupStep, hBlk]
    rw [← hEq]
    exact NondetStep.miriBranch st
  | some blk =>
    rcases blk with ⟨stmts, term⟩
    simp only [Option.map]
    cases term with
    | goto target =>
      have hEq : postCleanupStep tbl body st =
          postCleanupStepBlock tbl (optimizeUseCloneBlock tbl ⟨stmts, .goto target⟩) st := by
        simp [postCleanupStep, optimizeUseCloneBlock, hBlk]
      rw [← hEq]
      exact NondetStep.miriBranch st
    | return_ =>
      have hEq : postCleanupStep tbl body st =
          postCleanupStepBlock tbl (optimizeUseCloneBlock tbl ⟨stmts, .return_⟩) st := by
        simp [postCleanupStep, optimizeUseCloneBlock, hBlk]
      rw [← hEq]
      exact NondetStep.miriBranch st
    | call source argTy src dst target unwind =>
      cases source with
      | overloadedOperator =>
        have hEq : postCleanupStep tbl body st =
            postCleanupStepBlock tbl
              (optimizeUseCloneBlock tbl ⟨stmts, .call .overloadedOperator argTy src dst target unwind⟩) st := by
          simp [postCleanupStep, optimizeUseCloneBlock, hBlk]
        rw [← hEq]
        exact NondetStep.miriBranch st
      | matchCmp =>
        have hEq : postCleanupStep tbl body st =
            postCleanupStepBlock tbl
              (optimizeUseCloneBlock tbl ⟨stmts, .call .matchCmp argTy src dst target unwind⟩) st := by
          simp [postCleanupStep, optimizeUseCloneBlock, hBlk]
        rw [← hEq]
        exact NondetStep.miriBranch st
      | misc =>
        have hEq : postCleanupStep tbl body st =
            postCleanupStepBlock tbl
              (optimizeUseCloneBlock tbl ⟨stmts, .call .misc argTy src dst target unwind⟩) st := by
          simp [postCleanupStep, optimizeUseCloneBlock, hBlk]
        rw [← hEq]
        exact NondetStep.miriBranch st
      | normal =>
        have hEq : postCleanupStep tbl body st =
            postCleanupStepBlock tbl
              (optimizeUseCloneBlock tbl ⟨stmts, .call .normal argTy src dst target unwind⟩) st := by
          simp [postCleanupStep, optimizeUseCloneBlock, hBlk]
        rw [← hEq]
        exact NondetStep.miriBranch st
      | use_ =>
        unfold optimizeUseCloneBlock
        cases hCopy : (tbl argTy).isCopy with
        | false =>
          simp only [hCopy, Bool.false_eq_true, ↓reduceIte]
          have hEq : postCleanupStep tbl body st =
              postCleanupStepBlock tbl ⟨stmts, .call .use_ argTy src dst target unwind⟩ st := by
            simp [postCleanupStep, hBlk]
          rw [← hEq]
          exact NondetStep.miriBranch st
        | true =>
          simp only [hCopy, ↓reduceIte, postCleanupStepBlock]
          rw [execStmts_append]
          cases hStmts : execStmts stmts st.locals with
          | none =>
            have hEq : postCleanupStep tbl body st = .done .stuck := by
              simp [postCleanupStep, postCleanupStepBlock, hBlk, hStmts]
            rw [← hEq]
            exact NondetStep.miriBranch st
          | some locals' =>
            simp only [execStmts, execStmt]
            cases hVal : locals' src with
            | uninit =>
              exact NondetStep.codegenElideUseStuck st
                ⟨stmts, .call .use_ argTy src dst target unwind⟩
                argTy src dst target unwind locals'
                hBlk hStmts rfl hCopy hVal
            | scalar n =>
              exact NondetStep.codegenElideUseBranch st
                ⟨stmts, .call .use_ argTy src dst target unwind⟩
                argTy src dst target unwind locals'
                (.scalar n) hBlk hStmts rfl hCopy hVal (fun h => by cases h)
            | pair a b =>
              exact NondetStep.codegenElideUseBranch st
                ⟨stmts, .call .use_ argTy src dst target unwind⟩
                argTy src dst target unwind locals'
                (.pair a b) hBlk hStmts rfl hCopy hVal (fun h => by cases h)

/-- **Theorem 2 (Nondeterministic `PostCleanup` `CallSource::Use` Seam Envelope Soundness):**
    For EVERY MIR body (arbitrary multi-block CFG), EVERY `TypeTable` (including
    unlawful `SneakyCopy` and panicking `PanicCopy`), EVERY fuel bound, and EVERY
    initial state, the nondeterministic seam relation `NondetEval` envelops BOTH
    `Runtime(PostCleanup)` / Miri (`postCleanupEval`) AND native `rustc_codegen_ssa`
    (`codegenEval`). -/
theorem nondet_call_source_use_envelops_both_miri_and_codegen
    (tbl : TypeTable) (body : MirBody) (fuel : Nat) (st : MachineState) :
    NondetEval tbl body fuel st (postCleanupEval tbl body fuel st) ∧
    NondetEval tbl body fuel st (codegenEval tbl body fuel st) := by
  constructor
  · induction fuel generalizing st with
    | zero => exact NondetEval.zero st
    | succ f ih =>
      unfold postCleanupEval
      cases hStep : postCleanupStep tbl body st with
      | done out =>
        apply NondetEval.done
        rw [← hStep]
        exact NondetStep.miriBranch st
      | next st' =>
        apply NondetEval.step f st st'
        · rw [← hStep]
          exact NondetStep.miriBranch st
        · exact ih st'
  · induction fuel generalizing st with
    | zero => exact NondetEval.zero st
    | succ f ih =>
      unfold codegenEval postCleanupEval
      cases hStep : postCleanupStep tbl (optimizeUseClone tbl body) st with
      | done out =>
        apply NondetEval.done
        rw [← hStep]
        exact codegenStep_in_nondetStep tbl body st
      | next st' =>
        apply NondetEval.step f st st'
        · rw [← hStep]
          exact codegenStep_in_nondetStep tbl body st
        · exact ih st'

/-- Corollary: any postcondition proved over the nondeterministic seam `NondetEval`
    is sound simultaneously for Miri AND for native `rustc_codegen_ssa` binaries. -/
theorem nondet_postcondition_sound_for_miri_and_codegen
    (tbl : TypeTable) (body : MirBody) (fuel : Nat) (st : MachineState)
    (post : Outcome → Prop)
    (hVerified : ∀ out, NondetEval tbl body fuel st out → post out) :
    post (postCleanupEval tbl body fuel st) ∧ post (codegenEval tbl body fuel st) := by
  have hEnv := nondet_call_source_use_envelops_both_miri_and_codegen tbl body fuel st
  exact ⟨hVerified _ hEnv.1, hVerified _ hEnv.2⟩

/-! ## Part 3: Edition 2024 `use<...>` Precise Capturing, Variance, and Hidden-Type Substitution -/

/-- Rust editions relevant to RPIT lifetime-capture defaults. -/
inductive Edition where
  | ed2021
  | ed2024

/-- Generic parameter category (`rustc_middle::ty::GenericParamDefKind`). -/
inductive ParamKind where
  | lifetime
  | tyParam
  | constParam

/-- Variance lattice slice for opaque type parameters (`rustc_middle::ty::Variance`). -/
inductive Variance where
  | invariant
  | bivariant

/-- Identifier of a generic parameter in scope. -/
abbrev ParamId := Nat

/-- Generic parameter declaration in scope of an RPIT opaque type. -/
structure GenericParam where
  id : ParamId
  kind : ParamKind

/-- Manual membership predicate on `List ParamId`. -/
noncomputable def memNat (x : ParamId) : List ParamId → Bool
  | [] => false
  | y :: ys => if Nat.beq x y then true else memNat x ys

/-- Manual duplicate-free check on `List ParamId`. -/
noncomputable def noDupNat : List ParamId → Bool
  | [] => true
  | x :: xs => (!memNat x xs) && noDupNat xs

/-- Lookup a generic parameter's kind in scope. -/
noncomputable def lookupParamKind (id : ParamId) : List GenericParam → Option ParamKind
  | [] => none
  | p :: ps => if Nat.beq p.id id then some p.kind else lookupParamKind id ps

/-- `LifetimesMustBeFirst` syntactic ordering predicate on `use<...>` arguments
    (`compiler/rustc_hir_analysis/src/check/check.rs:593-605`). -/
noncomputable def lifetimesFirstAux (inScope : List GenericParam) : Bool → List ParamId → Bool
  | _, [] => true
  | seenNonLt, id :: rest =>
    match lookupParamKind id inScope with
    | none => false
    | some .lifetime =>
      if seenNonLt then false else lifetimesFirstAux inScope false rest
    | some .tyParam => lifetimesFirstAux inScope true rest
    | some .constParam => lifetimesFirstAux inScope true rest

/-- Whether an RPIT captures parameter `p` under the edition default or explicit `use<...>`.
    Matches `opaque_captures_all_in_scope_lifetimes`
    (`compiler/rustc_hir_analysis/src/collect/resolve_bound_vars.rs:323-332`):
    - Type and const parameters are always captured by RPIT opaques.
    - Without `use<...>`: Edition 2021 captures lifetimes only if mentioned in bounds;
      Edition 2024 captures ALL in-scope lifetimes.
    - With `use<args>`: captures lifetimes listed in `args` or mentioned in bounds. -/
noncomputable def rpitCapturesParam (ed : Edition) (boundMentioned : List ParamId)
    (useList : Option (List ParamId)) (p : GenericParam) : Bool :=
  match p.kind with
  | .tyParam | .constParam => true
  | .lifetime =>
    match useList with
    | some args => memNat p.id args || memNat p.id boundMentioned
    | none =>
      match ed with
      | .ed2021 => memNat p.id boundMentioned
      | .ed2024 => true

/-- Opaque parameter variance (`compiler/rustc_hir_analysis/src/variance/mod.rs:155-231`):
    every captured parameter is `Variance.invariant`; uncaptured parent lifetimes
    are `Variance.bivariant`. -/
noncomputable def opaqueParamVariance (ed : Edition) (boundMentioned : List ParamId)
    (useList : Option (List ParamId)) (p : GenericParam) : Variance :=
  if rpitCapturesParam ed boundMentioned useList p then .invariant else .bivariant

/-- Structural prerequisites on a `use<...>` argument list independent of
    type/const completeness:
    1. Every listed argument resolves to a parameter in scope and lifetimes precede
       non-lifetimes (`LifetimesMustBeFirst`).
    2. No parameter is listed twice (`DuplicatePreciseCapture`).
    3. Every lifetime mentioned in the opaque's explicit bounds is listed
       (`LifetimeNotCaptured`). -/
def PreciseCapturePreconditions (inScope : List GenericParam)
    (boundMentioned : List ParamId) (args : List ParamId) : Prop :=
  lifetimesFirstAux inScope false args = true ∧
  noDupNat args = true ∧
  (∀ p, p ∈ inScope → p.kind = .lifetime → memNat p.id boundMentioned = true →
    memNat p.id args = true)

/-- Type- and const-parameter completeness check enforced by
    `check_opaque_precise_captures`
    (`compiler/rustc_hir_analysis/src/check/check.rs:702-726`):
    every in-scope `tyParam` and `constParam` must appear in `use<...>`. -/
def AllNonLifetimeParamsRetained (inScope : List GenericParam) (args : List ParamId) : Prop :=
  ∀ p, p ∈ inScope →
    (p.kind = .tyParam ∨ p.kind = .constParam) →
    memNat p.id args = true

/-- Complete `check_opaque_precise_captures` acceptance judgment
    (`compiler/rustc_hir_analysis/src/check/check.rs:572-729`):
    combines syntactic prerequisites, invariance assertion for every listed param,
    bound-lifetime coverage, and all-type/const-parameter retention. -/
def PreciseCaptureWellFormed (ed : Edition) (inScope : List GenericParam)
    (boundMentioned : List ParamId) (args : List ParamId) : Prop :=
  PreciseCapturePreconditions inScope boundMentioned args ∧
  (∀ p, p ∈ inScope → memNat p.id args = true →
    opaqueParamVariance ed boundMentioned (some args) p = .invariant) ∧
  AllNonLifetimeParamsRetained inScope args

/-- Every parameter explicitly named in `use<args>` automatically receives
    `Variance.invariant` (matching the `assert_eq!(variances[param], ty::Invariant)`
    in `check_opaque_precise_captures` at `check.rs:651-655`). -/
theorem listed_param_is_invariant (ed : Edition) (boundMentioned args : List ParamId)
    (p : GenericParam) (hMem : memNat p.id args = true) :
    opaqueParamVariance ed boundMentioned (some args) p = .invariant := by
  unfold opaqueParamVariance rpitCapturesParam
  cases p.kind with
  | lifetime => simp [hMem]
  | tyParam => rfl
  | constParam => rfl

/-- Any in-scope lifetime NOT mentioned in bounds and NOT listed in `use<args>`
    receives `Variance.bivariant` (allowing detachment past local drops and
    unification across distinct lifetimes). -/
theorem omitted_unmentioned_lifetime_is_bivariant (ed : Edition)
    (boundMentioned args : List ParamId) (p : GenericParam)
    (hLt : p.kind = .lifetime)
    (hNotBound : memNat p.id boundMentioned = false)
    (hNotArgs : memNat p.id args = false) :
    opaqueParamVariance ed boundMentioned (some args) p = .bivariant := by
  unfold opaqueParamVariance rpitCapturesParam
  rw [hLt]
  simp [hNotBound, hNotArgs]

/-- **Theorem 3 (Edition 2024 `use<...>` Capture Variance & Type-Parameter Completeness):**
    Given syntactic ordering, uniqueness, and bound-lifetime coverage
    (`PreciseCapturePreconditions`), an RPIT `use<args>` bound passes
    `check_opaque_precise_captures` **if and only if** every in-scope type and
    const parameter is retained in `args` (and every retained parameter is
    invariant, while omitted unmentioned lifetimes are bivariant). -/
theorem precise_capture_well_formed_iff_all_ty_params_retained
    (ed : Edition) (inScope : List GenericParam)
    (boundMentioned args : List ParamId)
    (hPre : PreciseCapturePreconditions inScope boundMentioned args) :
    PreciseCaptureWellFormed ed inScope boundMentioned args ↔
      AllNonLifetimeParamsRetained inScope args := by
  constructor
  · intro hWF
    exact hWF.2.2
  · intro hAll
    refine ⟨hPre, ?_, hAll⟩
    intro p _ hMem
    exact listed_param_is_invariant ed boundMentioned args p hMem

/-- Edition 2021 vs. Edition 2024 default lifetime capture divergence and
    `use<...>` opt-out restoration. -/
theorem edition_2024_vs_2021_default_lifetime_capture_split
    (boundMentioned : List ParamId) (p : GenericParam)
    (hLt : p.kind = .lifetime)
    (hNotBound : memNat p.id boundMentioned = false) :
    opaqueParamVariance .ed2021 boundMentioned none p = .bivariant ∧
    opaqueParamVariance .ed2024 boundMentioned none p = .invariant ∧
    opaqueParamVariance .ed2024 boundMentioned (some []) p = .bivariant := by
  refine ⟨?_, ?_, ?_⟩
  · unfold opaqueParamVariance rpitCapturesParam
    rw [hLt]; simp [hNotBound]
  · unfold opaqueParamVariance rpitCapturesParam
    rw [hLt]; rfl
  · exact omitted_unmentioned_lifetime_is_bivariant .ed2024 boundMentioned [] p hLt hNotBound rfl

/-! ### Recursive Type Expressions and Opaque Hidden-Type Substitution -/

/-- Recursive type AST modeling concrete types, generic type parameters,
    references, pairs, and opaque type applications.
    Note: NO `deriving DecidableEq, Repr` on this recursive inductive; all
    recursive operations below are `noncomputable def` so zero `._unsafe_rec`
    helpers are synthesized. -/
inductive TyExpr where
  | u32Ty
  | boolTy
  | tyVar (id : ParamId)
  | refTy (lt : ParamId) (inner : TyExpr)
  | pairTy (a b : TyExpr)
  | opaqueApp (opaqueId : Nat) (args : List TyExpr)

/- Structural equality on `TyExpr` and `List TyExpr` (explicit `noncomputable def`,
   avoiding `._unsafe_rec`). -/
mutual
  /-- Structural equality on `TyExpr`. -/
  noncomputable def TyExpr.beq : TyExpr → TyExpr → Bool
    | .u32Ty, .u32Ty => true
    | .boolTy, .boolTy => true
    | .tyVar i, .tyVar j => Nat.beq i j
    | .refTy l1 t1, .refTy l2 t2 => Nat.beq l1 l2 && TyExpr.beq t1 t2
    | .pairTy a1 b1, .pairTy a2 b2 => TyExpr.beq a1 a2 && TyExpr.beq b1 b2
    | .opaqueApp id1 xs, .opaqueApp id2 ys => Nat.beq id1 id2 && TyExpr.beqList xs ys
    | _, _ => false

  /-- Elementwise structural equality on `List TyExpr`. -/
  noncomputable def TyExpr.beqList : List TyExpr → List TyExpr → Bool
    | [], [] => true
    | x :: xs, y :: ys => TyExpr.beq x y && TyExpr.beqList xs ys
    | _, _ => false
end

/- Check whether every free `tyVar` in a hidden type expression `t` is contained
   in the captured parameter list `captured`. -/
mutual
  /-- Coverage predicate for `TyExpr`. -/
  noncomputable def tyVarsCovered (captured : List ParamId) : TyExpr → Bool
    | .u32Ty => true
    | .boolTy => true
    | .tyVar id => memNat id captured
    | .refTy _ inner => tyVarsCovered captured inner
    | .pairTy a b => tyVarsCovered captured a && tyVarsCovered captured b
    | .opaqueApp _ args => tyVarsCoveredList captured args

  /-- Coverage predicate for `List TyExpr`. -/
  noncomputable def tyVarsCoveredList (captured : List ParamId) : List TyExpr → Bool
    | [] => true
    | t :: ts => tyVarsCovered captured t && tyVarsCoveredList captured ts
end

/-- Lookup a substitution binding in an association list `(ParamId × TyExpr)`. -/
noncomputable def lookupSubst (id : ParamId) : List (ParamId × TyExpr) → Option TyExpr
  | [] => none
  | (k, v) :: rest => if Nat.beq k id then some v else lookupSubst id rest

/- Apply a substitution map to a `TyExpr`. -/
mutual
  /-- Substitute type variables inside `TyExpr`. -/
  noncomputable def substTy (env : List (ParamId × TyExpr)) : TyExpr → TyExpr
    | .u32Ty => .u32Ty
    | .boolTy => .boolTy
    | .tyVar id =>
      match lookupSubst id env with
      | some t => t
      | none => .tyVar id
    | .refTy l inner => .refTy l (substTy env inner)
    | .pairTy a b => .pairTy (substTy env a) (substTy env b)
    | .opaqueApp oid args => .opaqueApp oid (substTyList env args)

  /-- Substitute type variables inside `List TyExpr`. -/
  noncomputable def substTyList (env : List (ParamId × TyExpr)) : List TyExpr → List TyExpr
    | [] => []
    | t :: ts => substTy env t :: substTyList env ts
end

/-- Defining-use generic-parameter injectivity check corresponding to `E0792`
    (`NonGenericOpaqueTypeParam` in `compiler/rustc_trait_selection/src/errors.rs:2052`):
    every argument at an opaque defining site must be a distinct generic `tyVar`. -/
noncomputable def definingUseArgsGenericAux (seen : List ParamId) : List TyExpr → Bool
  | [] => true
  | .tyVar id :: rest => (!memNat id seen) && definingUseArgsGenericAux (id :: seen) rest
  | _ :: _ => false

noncomputable def definingUseArgsGeneric (args : List TyExpr) : Bool :=
  definingUseArgsGenericAux [] args

/- Structural `DecidableEq` on the recursive inductive `TyExpr` and `List TyExpr`,
   written manually without `deriving` so Lean synthesizes zero `._unsafe_rec`
   helpers. -/
mutual
  /-- Explicit structural decidable equality on `TyExpr`. -/
  noncomputable def decEqTyExpr : (a b : TyExpr) → Decidable (a = b)
    | .u32Ty, .u32Ty => isTrue rfl
    | .boolTy, .boolTy => isTrue rfl
    | .tyVar i, .tyVar j =>
      match decEq i j with
      | isTrue h => isTrue (h ▸ rfl)
      | isFalse h => isFalse (fun heq => by cases heq; exact h rfl)
    | .refTy l1 t1, .refTy l2 t2 =>
      match decEq l1 l2, decEqTyExpr t1 t2 with
      | isTrue hl, isTrue ht => isTrue (hl ▸ ht ▸ rfl)
      | isFalse hl, _ => isFalse (fun heq => by cases heq; exact hl rfl)
      | _, isFalse ht => isFalse (fun heq => by cases heq; exact ht rfl)
    | .pairTy a1 b1, .pairTy a2 b2 =>
      match decEqTyExpr a1 a2, decEqTyExpr b1 b2 with
      | isTrue ha, isTrue hb => isTrue (ha ▸ hb ▸ rfl)
      | isFalse ha, _ => isFalse (fun heq => by cases heq; exact ha rfl)
      | _, isFalse hb => isFalse (fun heq => by cases heq; exact hb rfl)
    | .opaqueApp id1 xs, .opaqueApp id2 ys =>
      match decEq id1 id2, decEqTyExprList xs ys with
      | isTrue hi, isTrue hl => isTrue (hi ▸ hl ▸ rfl)
      | isFalse hi, _ => isFalse (fun heq => by cases heq; exact hi rfl)
      | _, isFalse hl => isFalse (fun heq => by cases heq; exact hl rfl)
    | .u32Ty, .boolTy | .u32Ty, .tyVar _ | .u32Ty, .refTy _ _ | .u32Ty, .pairTy _ _ | .u32Ty, .opaqueApp _ _
    | .boolTy, .u32Ty | .boolTy, .tyVar _ | .boolTy, .refTy _ _ | .boolTy, .pairTy _ _ | .boolTy, .opaqueApp _ _
    | .tyVar _, .u32Ty | .tyVar _, .boolTy | .tyVar _, .refTy _ _ | .tyVar _, .pairTy _ _ | .tyVar _, .opaqueApp _ _
    | .refTy _ _, .u32Ty | .refTy _ _, .boolTy | .refTy _ _, .tyVar _ | .refTy _ _, .pairTy _ _ | .refTy _ _, .opaqueApp _ _
    | .pairTy _ _, .u32Ty | .pairTy _ _, .boolTy | .pairTy _ _, .tyVar _ | .pairTy _ _, .refTy _ _ | .pairTy _ _, .opaqueApp _ _
    | .opaqueApp _ _, .u32Ty | .opaqueApp _ _, .boolTy | .opaqueApp _ _, .tyVar _ | .opaqueApp _ _, .refTy _ _ | .opaqueApp _ _, .pairTy _ _ =>
      isFalse (fun h => by cases h)

  noncomputable def decEqTyExprList : (xs ys : List TyExpr) → Decidable (xs = ys)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (fun h => by cases h)
    | _ :: _, [] => isFalse (fun h => by cases h)
    | x :: xs, y :: ys =>
      match decEqTyExpr x y, decEqTyExprList xs ys with
      | isTrue hx, isTrue hxs => isTrue (hx ▸ hxs ▸ rfl)
      | isFalse hx, _ => isFalse (fun heq => by cases heq; exact hx rfl)
      | _, isFalse hxs => isFalse (fun heq => by cases heq; exact hxs rfl)
end

/- Hidden-type substitution determinism: if every free type variable of hidden
   type `t` is covered by `captured`, then any two substitutions `env1` and
   `env2` that agree on all captured parameters produce the exact same
   instantiated hidden type. -/
mutual
  /-- Substitution determinism on `TyExpr`. -/
  theorem substTy_eq_of_covered_agree (captured : List ParamId)
      (env1 env2 : List (ParamId × TyExpr))
      (hAgree : ∀ id, memNat id captured = true → lookupSubst id env1 = lookupSubst id env2) :
      ∀ t : TyExpr, tyVarsCovered captured t = true → substTy env1 t = substTy env2 t
    | .u32Ty, _ => rfl
    | .boolTy, _ => rfl
    | .tyVar id, hCov => by
      simp only [tyVarsCovered] at hCov
      simp only [substTy, hAgree id hCov]
    | .refTy l inner, hCov => by
      simp only [tyVarsCovered] at hCov
      simp only [substTy, substTy_eq_of_covered_agree captured env1 env2 hAgree inner hCov]
    | .pairTy a b, hCov => by
      simp only [tyVarsCovered, Bool.and_eq_true] at hCov
      simp only [substTy,
        substTy_eq_of_covered_agree captured env1 env2 hAgree a hCov.1,
        substTy_eq_of_covered_agree captured env1 env2 hAgree b hCov.2]
    | .opaqueApp oid args, hCov => by
      simp only [tyVarsCovered] at hCov
      simp only [substTy, substTyList_eq_of_covered_agree captured env1 env2 hAgree args hCov]

  theorem substTyList_eq_of_covered_agree (captured : List ParamId)
      (env1 env2 : List (ParamId × TyExpr))
      (hAgree : ∀ id, memNat id captured = true → lookupSubst id env1 = lookupSubst id env2) :
      ∀ ts : List TyExpr, tyVarsCoveredList captured ts = true →
        substTyList env1 ts = substTyList env2 ts
    | [], _ => rfl
    | t :: ts, hCov => by
      simp only [tyVarsCoveredList, Bool.and_eq_true] at hCov
      simp only [substTyList,
        substTy_eq_of_covered_agree captured env1 env2 hAgree t hCov.1,
        substTyList_eq_of_covered_agree captured env1 env2 hAgree ts hCov.2]
end

/-! ## Part 4: Constructive Sharpness Counterexamples & Secondary Hazard Theorem -/

/-- Concrete type table matching our empirical probe (`SneakyCopy`, `LawfulCopy`,
    `PanicCopy`, `PanicNonCopy`, `Rc<u32>`, `String`). -/
noncomputable def probeTypeTable : TypeTable
  | .sneakyCopy   => { isCopy := true,  isUseCloned := true,  cloneBehavior := .custom 100 1 }
  | .lawfulCopy   => { isCopy := true,  isUseCloned := true,  cloneBehavior := .pureBitwise }
  | .panicCopy    => { isCopy := true,  isUseCloned := true,  cloneBehavior := .panics }
  | .panicNonCopy => { isCopy := false, isUseCloned := true,  cloneBehavior := .panics }
  | .rcHandle     => { isCopy := false, isUseCloned := true,  cloneBehavior := .custom 0 1 }
  | .ownedString  => { isCopy := false, isUseCloned := false, cloneBehavior := .custom 0 1 }

/-- **Counterexample 1 (`ce1_safe_sneaky_copy_refutes_deterministic_postcleanup_mir_seam`):**
    In `#![forbid(unsafe_code)]` Rust with `#![feature(ergonomic_clones)]`,
    `generic_dup::<SneakyCopy>(SneakyCopy(7))` evaluates to `(107, 7)` with
    `CLONE_CALLS = 1` in `Runtime(PostCleanup)` MIR (Miri Stacked & Tree Borrows),
    yet evaluates to `(7, 7)` with `CLONE_CALLS = 0` in native `-C opt-level=0`
    binaries (`rustc_codegen_ssa::mir::optimize_use_clone`).
    Hence `postCleanupEval ≠ codegenEval`, refuting any deterministic
    `PostCleanup` MIR verification seam. -/
theorem ce1_safe_sneaky_copy_refutes_deterministic_postcleanup_mir_seam :
    postCleanupEval probeTypeTable (genericDupBody .sneakyCopy) 3 (mkDupInitState 7 0) =
      .returned (.pair 107 7) 1 ∧
    codegenEval probeTypeTable (genericDupBody .sneakyCopy) 3 (mkDupInitState 7 0) =
      .returned (.pair 7 7) 0 ∧
    postCleanupEval probeTypeTable (genericDupBody .sneakyCopy) 3 (mkDupInitState 7 0) ≠
      codegenEval probeTypeTable (genericDupBody .sneakyCopy) 3 (mkDupInitState 7 0) ∧
    ¬ PureBitwiseClone probeTypeTable .sneakyCopy := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro h
    cases h
  · intro hPure
    have hBeh := hPure rfl rfl
    simp [probeTypeTable] at hBeh

/-- **Secondary Safe-Code Unwind Hazard (`unwind_unreachable_safe_code_ub_divergence`):**
    Because `rustc_mir_build` lowers `x.use` on `UseCloned` to
    `TerminatorKind::Call { unwind: UnwindAction::Unreachable, call_source: CallSource::Use }`,
    a safe `Copy + UseCloned` type whose `Clone::clone` panics triggers immediate
    `ubUnwindPastUnreachable` in `Runtime(PostCleanup)` MIR (Miri), yet returns
    cleanly with `(7, 7)` and zero panics in native `-C opt-level=0` binaries
    after `optimize_use_clone` elides the call. -/
theorem unwind_unreachable_safe_code_ub_divergence :
    postCleanupEval probeTypeTable (genericDupBody .panicCopy) 3 (mkDupInitState 7 0) =
      .ubUnwindPastUnreachable 0 ∧
    codegenEval probeTypeTable (genericDupBody .panicCopy) 3 (mkDupInitState 7 0) =
      .returned (.pair 7 7) 0 ∧
    postCleanupEval probeTypeTable (genericDupBody .panicNonCopy) 3 (mkDupInitState 7 0) =
      .ubUnwindPastUnreachable 0 := by
  exact ⟨rfl, rfl, rfl⟩

/-- **Counterexample 2 (`ce2_omitted_ty_param_in_use_breaks_hidden_type_subst_e0792`):**
    1. Omitting an in-scope type parameter `T` (id `1`) from `use<'a>` (id `0`)
       in `fn<'a, T>(_: &'a u32, _: T) -> impl Sized + use<'a>` violates
       `PreciseCaptureWellFormed` (`ParamNotCaptured`), even though all syntactic
       ordering and uniqueness preconditions hold.
    2. Leaving `T` uncaptured means `tyVarsCovered [0] (.tyVar 1) = false`:
       substituting `T = u32` vs. `T = bool` yields distinct hidden types
       (`.u32Ty ≠ .boolTy`) behind the SAME opaque key `[]` (no non-lifetime
       key slot), refuting functional hidden-type determinism.
    3. At an opaque defining site (TAIT `type Opaque<T> = impl Sized;`), passing
       a concrete type `Opaque<u32>` fails `definingUseArgsGeneric` (`E0792`),
       whereas a generic defining site `Opaque<T>` passes. -/
theorem ce2_omitted_ty_param_in_use_breaks_hidden_type_subst_e0792 :
    let inScope : List GenericParam := [{ id := 0, kind := .lifetime }, { id := 1, kind := .tyParam }]
    PreciseCapturePreconditions inScope [] [0] ∧
    ¬ PreciseCaptureWellFormed .ed2024 inScope [] [0] ∧
    tyVarsCovered [0] (.tyVar 1) = false ∧
    substTy [(1, .u32Ty)] (.tyVar 1) ≠ substTy [(1, .boolTy)] (.tyVar 1) ∧
    definingUseArgsGeneric [.u32Ty] = false ∧
    definingUseArgsGeneric [.tyVar 1] = true := by
  refine ⟨⟨rfl, rfl, ?_⟩, ?_, rfl, ?_, rfl, rfl⟩
  · intro p _ _ hBound
    cases hBound
  · intro hWF
    have hRet := hWF.2.2 { id := 1, kind := .tyParam }
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) (Or.inl rfl)
    cases hRet
  · intro hEq
    cases hEq

end UseClonedPostMonoSeamSoundness
