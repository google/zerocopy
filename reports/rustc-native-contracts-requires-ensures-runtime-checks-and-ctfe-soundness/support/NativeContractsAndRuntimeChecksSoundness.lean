/-
Kernel-checked operational semantics and soundness formalization for Rust
native contracts (`#[feature(contracts)]`, `core::contracts::{requires, ensures}`),
defining-crate vs. caller-crate `-Z contract-checks` flag scoping,
`const_eval_select!` CTFE bypass, multi-exit `ensures` interception,
tautological postcondition folding / return-range narrowing (`range(1, 101)` +
`nuw nsw`), and static-verification erasure equivalence.

Axiom & construct discipline:
  - 0 `sorry`
  - 0 `Classical.choice`
  - 0 `omega`, `bv_decide`, `native_decide`
  - 0 `partial def`, `._unsafe_rec`
-/

namespace NativeContractsSoundness

/-- Evaluation mode mirroring `const_eval_select!` in
    `library/core/src/intrinsics/mod.rs` (`contract_check_requires` and
    `contract_check_ensures`). -/
inductive EvalMode where
  | runtime
  | ctfe
  deriving DecidableEq, Repr

/-- Lowering strategy for contract check guards in `rustc`:
    - `hirBaked`: `compiler/rustc_ast_lowering/src/contract.rs` lowers contract
      guards to `bool` literals evaluated against the defining crate's
      `Session::contract_checks()` (`-Z contract-checks=yes|no`).
    - `deferredRuntimeCheck`: `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)`
      (`compiler/rustc_mir_transform/src/lower_intrinsics.rs`,
      `compiler/rustc_codegen_ssa/src/mir/operand.rs`), evaluated against the
      monomorphizing/caller crate's `Session::contract_checks()` at codegen. -/
inductive LoweringMode where
  | hirBaked
  | deferredRuntimeCheck
  deriving DecidableEq, Repr

/-- Cross-crate `-Z contract-checks` build flags for a callee defined in one
    crate and invoked (or inlined/monomorphized) in a downstream crate. -/
structure CrateBuildFlags where
  defContractChecks : Bool
  callerContractChecks : Bool
  deriving DecidableEq, Repr

/-- Effective contract-check predicate under `lmode` and `flags`. -/
def contractChecksEnabled (lmode : LoweringMode) (flags : CrateBuildFlags) : Bool :=
  match lmode with
  | .hirBaked => flags.defContractChecks
  | .deferredRuntimeCheck => flags.callerContractChecks

/-- Observable outcome of executing a contract-annotated function. -/
inductive Outcome (Ret : Type) where
  | ok (val : Ret)
  | unwind (code : Nat)
  | abortRequires
  | abortEnsures
  deriving DecidableEq, Repr

/-- Structured multi-exit function body modeling:
    - implicit tail return (`tail`),
    - explicit early `return` (`earlyReturn`),
    - `?` / `do yeet` residual early return (`tryResidual`),
    - unwinding panic (`panicUnwind`),
    - explicit tail call `become` (`tailCallBecome`), which bypasses
      `LoweringContext::checked_return` in `compiler/rustc_ast_lowering/src/expr.rs`,
    - conditional control flow (`branch`). -/
inductive BodyExpr (Ret : Type) where
  | tail (v : Ret)
  | earlyReturn (v : Ret)
  | tryResidual (v : Ret)
  | panicUnwind (code : Nat)
  | tailCallBecome (v : Ret)
  | branch (cond : Bool) (thenBranch : BodyExpr Ret) (elseBranch : BodyExpr Ret)

/-- Classification of the control-flow exit taken by a body execution. -/
inductive ExitKind where
  | tail
  | earlyReturn
  | tryResidual
  | unwind
  | becomeTailCall
  deriving DecidableEq, Repr

/-- Whether `rustc_ast_lowering` wraps this exit kind with `contract_check_ensures`. -/
def ExitKind.isCheckedNormalExit : ExitKind → Bool
  | .tail => true
  | .earlyReturn => true
  | .tryResidual => true
  | .unwind => false
  | .becomeTailCall => false

/-- Predicate asserting a function body contains no `become` explicit tail-call
    exit (which bypasses `checked_return` in `rustc_ast_lowering/src/expr.rs`). -/
def NoBecomeBypass {Ret : Type} : BodyExpr Ret → Prop
  | .tail _ => True
  | .earlyReturn _ => True
  | .tryResidual _ => True
  | .panicUnwind _ => True
  | .tailCallBecome _ => False
  | .branch _ t e => NoBecomeBypass t ∧ NoBecomeBypass e

/-- Raw exit classification and uninstrumented outcome of a `BodyExpr`. -/
def evalBodyRaw {Ret : Type} : BodyExpr Ret → ExitKind × Outcome Ret
  | .tail v => (.tail, .ok v)
  | .earlyReturn v => (.earlyReturn, .ok v)
  | .tryResidual v => (.tryResidual, .ok v)
  | .panicUnwind code => (.unwind, .unwind code)
  | .tailCallBecome v => (.becomeTailCall, .ok v)
  | .branch c t e =>
      match c with
      | true => evalBodyRaw t
      | false => evalBodyRaw e

/-- Uninstrumented body evaluation (erased contracts). -/
def evalBodyNoCheck {Ret : Type} (b : BodyExpr Ret) : Outcome Ret :=
  (evalBodyRaw b).2

/-- Postcondition-instrumented body evaluation mirroring
    `wrap_body_with_contract_check`, `checked_return`, and `inject_ensures_check`
    in `compiler/rustc_ast_lowering/src/contract.rs`. -/
def evalBodyWithEnsures {Ret : Type} (ens : Ret → Bool) : BodyExpr Ret → Outcome Ret
  | .tail v =>
      match ens v with
      | true => .ok v
      | false => .abortEnsures
  | .earlyReturn v =>
      match ens v with
      | true => .ok v
      | false => .abortEnsures
  | .tryResidual v =>
      match ens v with
      | true => .ok v
      | false => .abortEnsures
  | .panicUnwind code => .unwind code
  | .tailCallBecome v => .ok v
  | .branch c t e =>
      match c with
      | true => evalBodyWithEnsures ens t
      | false => evalBodyWithEnsures ens e

/-- Apply the `ensures` check rule to a raw `(ExitKind, Outcome)` pair. -/
def applyEnsuresDispatch {Ret : Type} (ens : Ret → Bool) :
    ExitKind × Outcome Ret → Outcome Ret
  | (k, .ok v) =>
      match k.isCheckedNormalExit with
      | true =>
          match ens v with
          | true => .ok v
          | false => .abortEnsures
      | false => .ok v
  | (_, out) => out

/-- A function annotated with `#[requires]` and `#[ensures]`, capturing input
    arguments by value (`move |ret| ...`). -/
structure ContractFn (Arg Ret : Type) where
  req : Arg → Bool
  ens : Arg → Ret → Bool
  body : Arg → BodyExpr Ret

/-- Uninstrumented execution of `f` (zero-overhead erased semantics). -/
def evalUninstrumented {Arg Ret : Type} (f : ContractFn Arg Ret) (x : Arg) : Outcome Ret :=
  evalBodyNoCheck (f.body x)

/-- Instrumented execution of `f` under evaluation mode `mode`, lowering mode
    `lmode`, and cross-crate build flags `flags`.
    In `EvalMode.ctfe`, `const_eval_select!` makes both `contract_check_requires`
    and `contract_check_ensures` no-ops even when `contractChecksEnabled = true`. -/
def evalInstrumented {Arg Ret : Type}
    (mode : EvalMode) (lmode : LoweringMode) (flags : CrateBuildFlags)
    (f : ContractFn Arg Ret) (x : Arg) : Outcome Ret :=
  match mode with
  | .ctfe => evalBodyNoCheck (f.body x)
  | .runtime =>
      match contractChecksEnabled lmode flags with
      | true =>
          match f.req x with
          | true => evalBodyWithEnsures (f.ens x) (f.body x)
          | false => .abortRequires
      | false => evalBodyNoCheck (f.body x)

/-- Static verification obligation corresponding to Anneal-style proof discharge:
    for every input satisfying `req`, the uninstrumented body returns normally
    with a value satisfying `ens`. -/
def StaticContractVerified {Arg Ret : Type} (f : ContractFn Arg Ret) : Prop :=
  ∀ x : Arg, f.req x = true →
    ∃ r : Ret, evalUninstrumented f x = .ok r ∧ f.ens x r = true

/-! ### Structural Lemmas for Multi-Exit Instrumentation -/

theorem evalBodyWithEnsures_eq_raw_dispatch {Ret : Type} (ens : Ret → Bool)
    (b : BodyExpr Ret) :
    evalBodyWithEnsures ens b = applyEnsuresDispatch ens (evalBodyRaw b) := by
  induction b with
  | tail v => rfl
  | earlyReturn v => rfl
  | tryResidual v => rfl
  | panicUnwind code => rfl
  | tailCallBecome v => rfl
  | branch c t e iht ihe =>
      cases c with
      | false => exact ihe
      | true => exact iht

theorem noBecomeBypass_raw_ok_is_checked {Ret : Type} (b : BodyExpr Ret)
    (hNo : NoBecomeBypass b) (k : ExitKind) (v : Ret)
    (hRaw : evalBodyRaw b = (k, .ok v)) :
    k.isCheckedNormalExit = true := by
  induction b with
  | tail w =>
      cases hRaw
      rfl
  | earlyReturn w =>
      cases hRaw
      rfl
  | tryResidual w =>
      cases hRaw
      rfl
  | panicUnwind code =>
      cases hRaw
  | tailCallBecome w =>
      exact False.elim hNo
  | branch c t e iht ihe =>
      cases hNo with
      | intro ht he =>
          cases c with
          | false => exact ihe he hRaw
          | true => exact iht ht hRaw

theorem evalBodyWithEnsures_preserves_verified_ok {Ret : Type}
    (ens : Ret → Bool) (b : BodyExpr Ret) (r : Ret)
    (hEval : evalBodyNoCheck b = .ok r) (hEns : ens r = true) :
    evalBodyWithEnsures ens b = .ok r := by
  rw [evalBodyWithEnsures_eq_raw_dispatch]
  unfold evalBodyNoCheck at hEval
  cases hPair : evalBodyRaw b with
  | mk k out =>
      rw [hPair] at hEval
      dsimp at hEval
      subst hEval
      dsimp [applyEnsuresDispatch]
      cases hChk : k.isCheckedNormalExit with
      | false => rfl
      | true =>
          rw [hEns]

/-! ### Core Soundness & Equivalence Theorems -/

/-- **Theorem 1 (Static-Verification Erasure Soundness)**:
    If `f` satisfies its static proof obligation `StaticContractVerified f`, then
    for every precondition-admitted input `x`, executing `f` with runtime or
    CTFE contract instrumentation (under any lowering mode and build flags)
    produces the exact same `Outcome` as zero-overhead erased execution. -/
theorem verified_contract_erasure_preserves_behavior {Arg Ret : Type}
    (f : ContractFn Arg Ret) (hVer : StaticContractVerified f)
    (mode : EvalMode) (lmode : LoweringMode) (flags : CrateBuildFlags)
    (x : Arg) (hReq : f.req x = true) :
    evalInstrumented mode lmode flags f x = evalUninstrumented f x := by
  cases mode with
  | ctfe => rfl
  | runtime =>
      unfold evalInstrumented evalUninstrumented
      cases hEn : contractChecksEnabled lmode flags with
      | false => rfl
      | true =>
          rw [hReq]
          rcases hVer x hReq with ⟨r, hEval, hEns⟩
          unfold evalUninstrumented at hEval
          rw [hEval]
          exact evalBodyWithEnsures_preserves_verified_ok (f.ens x) (f.body x) r hEval hEns

/-- **Theorem 1b (Converse: Erasure Equivalence Characterizes Static Verification)**:
    For any `become`-free function that returns normally on precondition-admitted
    inputs, `StaticContractVerified f` is logically equivalent to zero-overhead
    erasure preserving behavior under runtime `hirBaked` contract checks. -/
theorem static_verification_iff_erasure_preserves_behavior {Arg Ret : Type}
    (f : ContractFn Arg Ret)
    (hNoBecome : ∀ x, f.req x = true → NoBecomeBypass (f.body x))
    (hTotal : ∀ x, f.req x = true → ∃ r, evalUninstrumented f x = .ok r)
    (callerFlag : Bool) :
    StaticContractVerified f ↔
      (∀ x, f.req x = true →
        evalInstrumented .runtime .hirBaked ⟨true, callerFlag⟩ f x =
          evalUninstrumented f x) := by
  constructor
  · intro hVer x hReq
    exact verified_contract_erasure_preserves_behavior f hVer .runtime .hirBaked
      ⟨true, callerFlag⟩ x hReq
  · intro hEq x hReq
    rcases hTotal x hReq with ⟨r, hEval⟩
    refine ⟨r, hEval, ?_⟩
    have hInst := hEq x hReq
    unfold evalInstrumented contractChecksEnabled at hInst
    rw [hReq] at hInst
    rw [hEval] at hInst
    rw [evalBodyWithEnsures_eq_raw_dispatch] at hInst
    unfold evalUninstrumented evalBodyNoCheck at hEval
    cases hPair : evalBodyRaw (f.body x) with
    | mk k out =>
        rw [hPair] at hEval hInst
        dsimp at hEval
        subst hEval
        dsimp [applyEnsuresDispatch] at hInst
        have hChk : k.isCheckedNormalExit = true :=
          noBecomeBypass_raw_ok_is_checked (f.body x) (hNoBecome x hReq) k r hPair
        rw [hChk] at hInst
        cases hEnsVal : f.ens x r with
        | false =>
            rw [hEnsVal] at hInst
            cases hInst
        | true => rfl

/-- **Theorem 2 (Early-Return `ensures` Interception Completeness)**:
    When runtime contract checks are active and `req x = true`, every checked
    normal exit (`tail`, `earlyReturn`, or `tryResidual`) returning `r` is
    intercepted by `contract_check_ensures`: it yields `.ok r` if `ens x r = true`
    and aborts with `.abortEnsures` if `ens x r = false`. -/
theorem ensures_checks_every_normal_exit {Arg Ret : Type}
    (f : ContractFn Arg Ret) (lmode : LoweringMode) (flags : CrateBuildFlags)
    (hEn : contractChecksEnabled lmode flags = true)
    (x : Arg) (hReq : f.req x = true)
    (k : ExitKind) (r : Ret)
    (hRaw : evalBodyRaw (f.body x) = (k, .ok r))
    (hChecked : k.isCheckedNormalExit = true) :
    (f.ens x r = true → evalInstrumented .runtime lmode flags f x = .ok r) ∧
    (f.ens x r = false → evalInstrumented .runtime lmode flags f x = .abortEnsures) := by
  have hBase :
      evalInstrumented .runtime lmode flags f x =
        match f.ens x r with
        | true => .ok r
        | false => .abortEnsures := by
    unfold evalInstrumented
    rw [hEn, hReq, evalBodyWithEnsures_eq_raw_dispatch, hRaw]
    dsimp [applyEnsuresDispatch]
    rw [hChecked]
  constructor
  · intro hT
    rw [hBase, hT]
  · intro hF
    rw [hBase, hF]

/-- Corollary: for any `become`-free body, observing a normal return `.ok r`
    under active runtime contract checks implies both `f.req x = true` and
    `f.ens x r = true`. -/
theorem runtime_ok_implies_req_and_ens {Arg Ret : Type}
    (f : ContractFn Arg Ret) (lmode : LoweringMode) (flags : CrateBuildFlags)
    (hEn : contractChecksEnabled lmode flags = true)
    (x : Arg) (hNoBecome : NoBecomeBypass (f.body x)) (r : Ret)
    (hOk : evalInstrumented .runtime lmode flags f x = .ok r) :
    f.req x = true ∧ f.ens x r = true := by
  unfold evalInstrumented at hOk
  rw [hEn] at hOk
  cases hReq : f.req x with
  | false =>
      rw [hReq] at hOk
      cases hOk
  | true =>
      rw [hReq] at hOk
      rw [evalBodyWithEnsures_eq_raw_dispatch] at hOk
      cases hPair : evalBodyRaw (f.body x) with
      | mk k out =>
          rw [hPair] at hOk
          cases out with
          | ok v =>
              dsimp [applyEnsuresDispatch] at hOk
              have hChk : k.isCheckedNormalExit = true :=
                noBecomeBypass_raw_ok_is_checked (f.body x) hNoBecome k v hPair
              rw [hChk] at hOk
              cases hEnsVal : f.ens x v with
              | false =>
                  rw [hEnsVal] at hOk
                  cases hOk
              | true =>
                  rw [hEnsVal] at hOk
                  cases hOk
                  exact ⟨rfl, hEnsVal⟩
          | unwind _ => cases hOk
          | abortRequires => cases hOk
          | abortEnsures => cases hOk

/-- **Theorem 3 (Defining-Crate Flag Determinism vs. Caller-Crate Invariance)**:
    Under `rustc`'s HIR-baked contract lowering (`rustc_ast_lowering/src/contract.rs`),
    evaluation is completely invariant to the downstream caller crate's
    `-Z contract-checks` flag; only the defining crate's flag governs checking. -/
theorem contract_check_determined_by_defining_crate_flag {Arg Ret : Type}
    (mode : EvalMode) (f : ContractFn Arg Ret) (x : Arg)
    (defFlag callerFlag₁ callerFlag₂ : Bool) :
    evalInstrumented mode .hirBaked ⟨defFlag, callerFlag₁⟩ f x =
    evalInstrumented mode .hirBaked ⟨defFlag, callerFlag₂⟩ f x := by
  cases mode <;> rfl

/-- Dual scoping theorem for `Operand::RuntimeChecks(RuntimeChecks::ContractChecks)`:
    if a guard is lowered via `deferredRuntimeCheck`, evaluation is invariant to
    the defining crate's flag and governed exclusively by the caller/codegen crate. -/
theorem deferred_runtime_check_tracks_caller_crate_flag {Arg Ret : Type}
    (mode : EvalMode) (f : ContractFn Arg Ret) (x : Arg)
    (defFlag₁ defFlag₂ callerFlag : Bool) :
    evalInstrumented mode .deferredRuntimeCheck ⟨defFlag₁, callerFlag⟩ f x =
    evalInstrumented mode .deferredRuntimeCheck ⟨defFlag₂, callerFlag⟩ f x := by
  cases mode <;> rfl

/-! ### Return-Range Narrowing (`range(i32 1, 101)`) & Overflow Freedom (`nuw nsw`) -/

def u32Mod : Nat := 4294967296
def i32Max : Nat := 2147483647

def u32Add (a b : Nat) : Nat := (a + b) % u32Mod

/-- Concrete model of the probed `inc_bounded(x: u32) -> u32` function:
    `#[requires(x < 100)]`
    `#[ensures(move |ret| *ret == x + 1 && *ret > 0 && *ret <= 100)]` -/
def incBounded : ContractFn Nat Nat where
  req := fun x => decide (x < 100)
  ens := fun x r => decide (r = u32Add x 1 ∧ 0 < r ∧ r ≤ 100)
  body := fun x => .tail (u32Add x 1)

private theorem lt_100_succ_lt_101 {x : Nat} (h : x < 100) : x + 1 < 101 :=
  Nat.succ_lt_succ h

private theorem lt_101_le_100 {y : Nat} (h : y < 101) : y ≤ 100 :=
  Nat.le_of_lt_succ h

private theorem lt_100_succ_lt_u32Mod {x : Nat} (h : x < 100) : x + 1 < u32Mod :=
  Nat.lt_trans (Nat.succ_lt_succ h) (by decide : 101 < u32Mod)

private theorem lt_100_succ_le_i32Max {x : Nat} (h : x < 100) : x + 1 ≤ i32Max :=
  Nat.le_trans (Nat.le_of_lt_succ (Nat.succ_lt_succ h)) (by decide : 100 ≤ i32Max)

/-- Guarded `x < 100` implies `x + 1` has neither unsigned overflow (`nuw`) nor
    signed 32-bit overflow (`nsw`). -/
theorem incBounded_add_nuw_nsw {x : Nat} (h : x < 100) :
    x + 1 < u32Mod ∧ x + 1 ≤ i32Max ∧ u32Add x 1 = x + 1 := by
  have hNuw : x + 1 < u32Mod := lt_100_succ_lt_u32Mod h
  have hNsw : x + 1 ≤ i32Max := lt_100_succ_le_i32Max h
  exact ⟨hNuw, hNsw, Nat.mod_eq_of_lt hNuw⟩

/-- Guarded `x < 100` narrows the return value of `incBounded` to the half-open
    LLVM interval `range(i32 1, 101)` (`1 ≤ r < 101`). -/
theorem incBounded_return_in_llvm_range {x : Nat} (h : x < 100) :
    1 ≤ u32Add x 1 ∧ u32Add x 1 < 101 := by
  have hEq : u32Add x 1 = x + 1 := (incBounded_add_nuw_nsw h).2.2
  rw [hEq]
  exact ⟨Nat.succ_le_succ (Nat.zero_le x), lt_100_succ_lt_101 h⟩

/-- Under the precondition `x < 100`, the `#[ensures]` clause of `incBounded` is
    a tautology, justifying LLVM's complete elimination of the postcondition
    check and `"failed ensures check"` panic call. -/
theorem incBounded_ensures_tautological {x : Nat} (h : x < 100) :
    incBounded.ens x (u32Add x 1) = true := by
  have hRange := incBounded_return_in_llvm_range h
  have hPos : 0 < u32Add x 1 := hRange.1
  have hLe : u32Add x 1 ≤ 100 := lt_101_le_100 hRange.2
  exact decide_eq_true ⟨rfl, hPos, hLe⟩

/-- `incBounded` satisfies its static contract obligation. -/
theorem incBounded_static_verified : StaticContractVerified incBounded := by
  intro x hReq
  have hLt : x < 100 := of_decide_eq_true hReq
  exact ⟨u32Add x 1, rfl, incBounded_ensures_tautological hLt⟩

/-- Soundness of LLVM's `noundef range(i32 1, 101)` return-attribute deduction
    when runtime contract checks guard `incBounded`. -/
theorem incBounded_runtime_guarded_return_range (callerFlag : Bool) (x r : Nat)
    (hOk : evalInstrumented .runtime .hirBaked ⟨true, callerFlag⟩ incBounded x = .ok r) :
    1 ≤ r ∧ r < 101 := by
  unfold evalInstrumented contractChecksEnabled at hOk
  dsimp at hOk
  cases hReq : incBounded.req x with
  | false =>
      rw [hReq] at hOk
      cases hOk
  | true =>
      have hLt : x < 100 := of_decide_eq_true hReq
      have hEns : incBounded.ens x (u32Add x 1) = true :=
        incBounded_ensures_tautological hLt
      rw [hReq] at hOk
      change (match incBounded.ens x (u32Add x 1) with
              | true => Outcome.ok (u32Add x 1)
              | false => Outcome.abortEnsures) = Outcome.ok r at hOk
      rw [hEns] at hOk
      cases hOk
      exact incBounded_return_in_llvm_range hLt

/-- Tautological postcondition folding soundness: replacing `incBounded.ens`
    with `fun _ _ => true` preserves runtime behavior for ALL inputs `x : Nat`
    (both valid and precondition-violating!). -/
def incBoundedFoldedEnsures : ContractFn Nat Nat where
  req := incBounded.req
  ens := fun _ _ => true
  body := incBounded.body

theorem incBounded_tautological_ensures_folding_sound (callerFlag : Bool) (x : Nat) :
    evalInstrumented .runtime .hirBaked ⟨true, callerFlag⟩ incBounded x =
    evalInstrumented .runtime .hirBaked ⟨true, callerFlag⟩ incBoundedFoldedEnsures x := by
  unfold evalInstrumented contractChecksEnabled
  dsimp [incBoundedFoldedEnsures]
  cases hReq : incBounded.req x with
  | false => rfl
  | true =>
      have hLt : x < 100 := of_decide_eq_true hReq
      have hEns : incBounded.ens x (u32Add x 1) = true :=
        incBounded_ensures_tautological hLt
      change (match incBounded.ens x (u32Add x 1) with
              | true => Outcome.ok (u32Add x 1)
              | false => Outcome.abortEnsures) = Outcome.ok (u32Add x 1)
      rw [hEns]

/-! ### Constructive Counterexamples -/

/-- **Counterexample 1**: Without static verification of the caller's argument,
    erasing contract checks (`defContractChecks = false`) allows the
    precondition-violating call `incBounded(200)` to return `.ok 201` (matching
    empirical `REQ=201`), whereas checked execution aborts with `.abortRequires`
    (`SIGABRT`, `rc = -6`). -/
theorem ce1_unverified_erasure_misses_precondition_violation :
    incBounded.req 200 = false ∧
    evalInstrumented .runtime .hirBaked ⟨true, false⟩ incBounded 200 = .abortRequires ∧
    evalInstrumented .runtime .hirBaked ⟨false, false⟩ incBounded 200 = .ok 201 ∧
    evalInstrumented .runtime .hirBaked ⟨false, false⟩ incBounded 200 ≠
      evalInstrumented .runtime .hirBaked ⟨true, false⟩ incBounded 200 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  cases h

/-- Concrete model of `#[requires(x > 0)] #[ensures(|r| *r > 0)] const fn pos(x: u32) -> u32 { x }`. -/
def posConstFn : ContractFn Nat Nat where
  req := fun x => decide (0 < x)
  ens := fun _ r => decide (0 < r)
  body := fun x => .tail x

/-- **Counterexample 2**: Even when `-Z contract-checks=yes` is active in both
    crates, `const_eval_select!` turns `contract_check_requires` and
    `contract_check_ensures` into no-ops in CTFE, so `pub const BAD: u32 = pos(0)`
    evaluates to `.ok 0` (violating both `req 0` and `ens 0 0`), diverging from
    runtime execution which aborts with `.abortRequires`. -/
theorem ce2_ctfe_skipping_requires_evaluates_invalid_const :
    posConstFn.req 0 = false ∧
    posConstFn.ens 0 0 = false ∧
    evalInstrumented .ctfe .hirBaked ⟨true, true⟩ posConstFn 0 = .ok 0 ∧
    evalInstrumented .runtime .hirBaked ⟨true, true⟩ posConstFn 0 = .abortRequires ∧
    evalInstrumented .ctfe .hirBaked ⟨true, true⟩ posConstFn 0 ≠
      evalInstrumented .runtime .hirBaked ⟨true, true⟩ posConstFn 0 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro h
  cases h

/-- Concrete model of the upstream `#[inline] #[requires(x < 10)] pub fn inline_inc(x: u32) -> u32`. -/
def upstreamInlineInc : ContractFn Nat Nat where
  req := fun x => decide (x < 10)
  ens := fun x r => decide (r = u32Add x 1)
  body := fun x => .tail (u32Add x 1)

/-- **Counterexample 3**: A downstream crate compiled with `-Z contract-checks=yes`
    invoking an upstream `#[inline]` function compiled with `-Z contract-checks=no`
    (`⟨false, true⟩`) silently misses the violated precondition `50 < 10` and
    returns `.ok 51` under `hirBaked` lowering, whereas `deferredRuntimeCheck`
    would have caught it with `.abortRequires`. -/
theorem ce3_unchecked_downstream_caller_relying_on_uninstrumented_upstream_misses_contract :
    upstreamInlineInc.req 50 = false ∧
    evalInstrumented .runtime .hirBaked ⟨false, true⟩ upstreamInlineInc 50 = .ok 51 ∧
    evalInstrumented .runtime .hirBaked ⟨true, false⟩ upstreamInlineInc 50 = .abortRequires ∧
    evalInstrumented .runtime .deferredRuntimeCheck ⟨false, true⟩ upstreamInlineInc 50 =
      .abortRequires := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Concrete model of `buggy_early_return(flag: bool) -> u32` (`if flag { return 0; } 42`). -/
def buggyEarlyReturn : ContractFn Bool Nat where
  req := fun _ => true
  ens := fun _ r => decide (0 < r)
  body := fun flag => .branch flag (.earlyReturn 0) (.tail 42)

/-- Concrete model of `tail_bypass() -> u32 { become helper() }` where `helper()` returns `0`. -/
def tailBecomeBypass : ContractFn Unit Nat where
  req := fun _ => true
  ens := fun _ r => decide (0 < r)
  body := fun _ => .tailCallBecome 0

/-- Concrete model of `panics_before_return() -> u32 { panic!(...) }` with `#[ensures(|_| false)]`. -/
def panicsBeforeReturn : ContractFn Unit Nat where
  req := fun _ => true
  ens := fun _ _ => false
  body := fun _ => .panicUnwind 1

/-- **Counterexample 4 (Early Return Caught vs. Explicit Tail Call `become` & Unwind Bypass)**:
    Under `-Z contract-checks=yes`, `buggy_early_return(true)` is intercepted and
    aborts with `.abortEnsures`, whereas `become helper()` returns `.ok 0`
    without checking `ens` (matching `rustc_ast_lowering/src/expr.rs:488-490`),
    and an unwinding panic returns `.unwind 1` without checking `ens`. -/
theorem ce4_early_return_caught_vs_become_and_unwind_bypass :
    evalInstrumented .runtime .hirBaked ⟨true, true⟩ buggyEarlyReturn false = .ok 42 ∧
    evalInstrumented .runtime .hirBaked ⟨true, true⟩ buggyEarlyReturn true = .abortEnsures ∧
    tailBecomeBypass.ens () 0 = false ∧
    evalInstrumented .runtime .hirBaked ⟨true, true⟩ tailBecomeBypass () = .ok 0 ∧
    evalInstrumented .runtime .hirBaked ⟨true, true⟩ panicsBeforeReturn () = .unwind 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end NativeContractsSoundness

#print axioms NativeContractsSoundness.verified_contract_erasure_preserves_behavior
#print axioms NativeContractsSoundness.static_verification_iff_erasure_preserves_behavior
#print axioms NativeContractsSoundness.ensures_checks_every_normal_exit
#print axioms NativeContractsSoundness.runtime_ok_implies_req_and_ens
#print axioms NativeContractsSoundness.contract_check_determined_by_defining_crate_flag
#print axioms NativeContractsSoundness.deferred_runtime_check_tracks_caller_crate_flag
#print axioms NativeContractsSoundness.incBounded_runtime_guarded_return_range
#print axioms NativeContractsSoundness.incBounded_tautological_ensures_folding_sound
#print axioms NativeContractsSoundness.ce1_unverified_erasure_misses_precondition_violation
#print axioms NativeContractsSoundness.ce2_ctfe_skipping_requires_evaluates_invalid_const
#print axioms NativeContractsSoundness.ce3_unchecked_downstream_caller_relying_on_uninstrumented_upstream_misses_contract
#print axioms NativeContractsSoundness.ce4_early_return_caught_vs_become_and_unwind_bypass
