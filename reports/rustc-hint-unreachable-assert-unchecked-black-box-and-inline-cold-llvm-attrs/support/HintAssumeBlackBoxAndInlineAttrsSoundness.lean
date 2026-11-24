/-
  HintAssumeBlackBoxAndInlineAttrsSoundness.lean

  Self-contained kernel-checked Lean v4.34.1 mechanization of `rustc` and LLVM
  lowering semantics for `core::hint::{unreachable_unchecked, assert_unchecked,
  black_box}` and `#[inline]` / `#[inline(always)]` / `#[inline(never)]` /
  `#[cold]` / `#[optimize(none)]` function attributes.

  Core theorem families proven in this module:
    1. Debug-Mode Refinement (`abortOnFalse` soundly refines `ubOnFalse`
       across arbitrary structured programs and call trees) paired with the
       pre-compiled `core` (`preserveUbChecks = true`) + `-O0` (`OptLevel::No`)
       `@llvm.assume` suppression boundary explaining why `-O0 -C debug-assertions=off`
       still traps on `unreachable_unchecked()` while executing past `assert_unchecked(false)`;
    2. `assume(P)`-guided dead-branch pruning soundness (under both checked and
       unchecked modes), constructive sharpness counterexamples when contradiction
       fails, and modular `i32` return-range refinement (`noundef range(i32 2, 1)`);
    3. `core::hint::black_box` observational value identity (across both runtime
       and `const` evaluation) together with constant-folding barrier preservation;
    4. `#[inline]` / `#[inline(always)]` / `#[inline(never)]` / `#[cold]` /
       `#[optimize(none)]` attribute precedence (`InlineParser` first-wins),
       exported-function diagnostics, LLVM attribute mapping, hygienic call
       inlining soundness, and attribute-invariance equivalence.

  Kernel purity invariants:
    * Zero imports outside Lean `Init`.
    * Every `def` is marked `noncomputable def` (zero recursive codegen helpers).
    * Constructive total definitions and kernel proofs only; zero classical
      choice, zero unproved placeholders, and zero automatic arithmetic tactics. -/

namespace VerifiedRustcHintInline

-- ============================================================================
-- Section 1: Registers, Function Identifiers, Modular `i32`, Values, Stores
-- ============================================================================

inductive Reg : Type where
  | r0
  | r1
  | r2
  | r3
  | callerA
  | callerB
  | calleeParam
  | calleeLocal
  | tmp

noncomputable def regEq : Reg → Reg → Bool
  | .r0, .r0 => true
  | .r1, .r1 => true
  | .r2, .r2 => true
  | .r3, .r3 => true
  | .callerA, .callerA => true
  | .callerB, .callerB => true
  | .calleeParam, .calleeParam => true
  | .calleeLocal, .calleeLocal => true
  | .tmp, .tmp => true
  | _, _ => false

theorem regEq_refl (r : Reg) : regEq r r = true := by
  cases r <;> rfl

theorem regEq_symm (a b : Reg) : regEq a b = regEq b a := by
  cases a <;> cases b <;> rfl

theorem regEq_eq_true_iff (a b : Reg) : regEq a b = true ↔ a = b := by
  constructor
  · intro h
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  · intro h
    subst h
    exact regEq_refl a

theorem regEq_false_of_ne (a b : Reg) (h : a ≠ b) : regEq a b = false := by
  cases hb : regEq a b
  · rfl
  · exact absurd ((regEq_eq_true_iff a b).mp hb) h

noncomputable def isCallerVisibleReg : Reg → Bool
  | .calleeParam => false
  | .calleeLocal => false
  | _ => true

inductive FnId : Type where
  | mainFn
  | helperLeaf
  | helperCall
  | helperCold
  | helperAlways
  | helperNever

noncomputable def fnIdEq : FnId → FnId → Bool
  | .mainFn, .mainFn => true
  | .helperLeaf, .helperLeaf => true
  | .helperCall, .helperCall => true
  | .helperCold, .helperCold => true
  | .helperAlways, .helperAlways => true
  | .helperNever, .helperNever => true
  | _, _ => false

theorem fnIdEq_refl (f : FnId) : fnIdEq f f = true := by
  cases f <;> rfl

theorem fnIdEq_eq_true_iff (a b : FnId) : fnIdEq a b = true ↔ a = b := by
  constructor
  · intro h
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  · intro h
    subst h
    exact fnIdEq_refl a

noncomputable def i32Modulus : Nat := 4294967296

theorem i32Modulus_pos : 0 < i32Modulus := by
  decide

noncomputable def norm32 (n : Nat) : Nat :=
  n % i32Modulus

noncomputable def add32 (a b : Nat) : Nat :=
  norm32 (a + b)

theorem norm32_lt (n : Nat) : norm32 n < i32Modulus :=
  Nat.mod_lt n i32Modulus_pos

theorem norm32_idempotent (n : Nat) : norm32 (norm32 n) = norm32 n :=
  Nat.mod_mod n i32Modulus

theorem nat_beq_true_iff (a b : Nat) : Nat.beq a b = true ↔ a = b := by
  constructor
  · exact Nat.eq_of_beq_eq_true
  · intro h; subst h; exact Nat.beq_refl a

noncomputable def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

theorem bool_beq_true_iff (a b : Bool) : boolEq a b = true ↔ a = b := by
  cases a <;> cases b <;> constructor <;> intro h <;> first | rfl | cases h

inductive Val : Type where
  | unit
  | bool (b : Bool)
  | i32 (n : Nat)

/-- Exact structural equality on `Val` constructors (distinct from modular `i32` runtime equality). -/
noncomputable def valStructEq : Val → Val → Bool
  | .unit, .unit => true
  | .bool a, .bool b => boolEq a b
  | .i32 a, .i32 b => Nat.beq a b
  | _, _ => false

theorem valStructEq_refl (v : Val) : valStructEq v v = true := by
  cases v with
  | unit => rfl
  | bool b => cases b <;> rfl
  | i32 n => exact Nat.beq_refl n

theorem valStructEq_eq_true_iff (a b : Val) : valStructEq a b = true ↔ a = b := by
  constructor
  · intro h
    cases a <;> cases b <;> try cases h
    · rfl
    · case bool.bool ba bb =>
        have hb := (bool_beq_true_iff ba bb).mp h
        subst hb
        rfl
    · case i32.i32 na nb =>
        have hn := (nat_beq_true_iff na nb).mp h
        subst hn
        rfl
  · intro h
    subst h
    exact valStructEq_refl a

/-- Total register state mapping registers to runtime values. -/
noncomputable def Store : Type := Reg → Val

noncomputable def emptyStore : Store := fun _ => .i32 0

noncomputable def updateStore (st : Store) (r : Reg) (v : Val) : Store :=
  fun r' => if regEq r' r then v else st r'

theorem updateStore_same (st : Store) (r : Reg) (v : Val) :
    updateStore st r v r = v := by
  unfold updateStore
  rw [regEq_refl r]
  rfl

theorem updateStore_other (st : Store) (r r' : Reg) (v : Val) (hne : r' ≠ r) :
    updateStore st r v r' = st r' := by
  unfold updateStore
  rw [regEq_false_of_ne r' r hne]
  rfl

theorem updateStore_shadow (st : Store) (r : Reg) (v1 v2 : Val) :
    updateStore (updateStore st r v1) r v2 = updateStore st r v2 := by
  funext r'
  unfold updateStore
  cases regEq r' r <;> rfl

theorem updateStore_comm (st : Store) (ra rb : Reg) (v1 v2 : Val) (hne : ra ≠ rb) :
    updateStore (updateStore st ra v1) rb v2 =
    updateStore (updateStore st rb v2) ra v1 := by
  funext r'
  unfold updateStore
  cases h2 : regEq r' rb <;> cases h1 : regEq r' ra
  · rfl
  · rfl
  · rfl
  · have hr2 := (regEq_eq_true_iff r' rb).mp h2
    have hr1 := (regEq_eq_true_iff r' ra).mp h1
    exact absurd (hr1.symm.trans hr2) hne

noncomputable def storeAgreeOn (pred : Reg → Bool) (s1 s2 : Store) : Prop :=
  ∀ r : Reg, pred r = true → s1 r = s2 r

theorem storeAgreeOn_refl (pred : Reg → Bool) (st : Store) :
    storeAgreeOn pred st st := by
  intro _ _
  rfl

theorem storeAgreeOn_symm (pred : Reg → Bool) (s1 s2 : Store)
    (h : storeAgreeOn pred s1 s2) : storeAgreeOn pred s2 s1 := by
  intro r hr
  exact (h r hr).symm

theorem storeAgreeOn_trans (pred : Reg → Bool) (s1 s2 s3 : Store)
    (h12 : storeAgreeOn pred s1 s2) (h23 : storeAgreeOn pred s2 s3) :
    storeAgreeOn pred s1 s3 := by
  intro r hr
  exact (h12 r hr).trans (h23 r hr)

theorem storeAgreeOn_update_hidden (pred : Reg → Bool) (s1 s2 : Store) (r : Reg) (v : Val)
    (hHidden : pred r = false) (hAgree : storeAgreeOn pred s1 s2) :
    storeAgreeOn pred (updateStore s1 r v) s2 := by
  intro r' hr'
  have hne : r' ≠ r := by
    intro hEq
    subst hEq
    rw [hr'] at hHidden
    cases hHidden
  rw [updateStore_other s1 r r' v hne]
  exact hAgree r' hr'

theorem storeAgreeOn_update_both (pred : Reg → Bool) (s1 s2 : Store) (r : Reg) (v : Val)
    (hAgree : storeAgreeOn pred s1 s2) :
    storeAgreeOn pred (updateStore s1 r v) (updateStore s2 r v) := by
  intro r' hr'
  unfold updateStore
  cases regEq r' r
  · exact hAgree r' hr'
  · rfl

-- ============================================================================
-- Section 2: Expressions, `black_box` Barrier, Constant Folding, Substitution
-- ============================================================================

inductive BinOp : Type where
  | add
  | eq
  | ne
  | and
  | or

inductive Expr : Type where
  | lit (v : Val)
  | var (r : Reg)
  | not (e : Expr)
  | bin (op : BinOp) (lhs rhs : Expr)
  | blackBox (e : Expr)

inductive ConstEvalMode : Type where
  | runtime
  | constEval

noncomputable def binOpEq : BinOp → BinOp → Bool
  | .add, .add => true
  | .eq, .eq => true
  | .ne, .ne => true
  | .and, .and => true
  | .or, .or => true
  | _, _ => false

theorem binOpEq_refl (op : BinOp) : binOpEq op op = true := by
  cases op <;> rfl

theorem binOpEq_eq_true_iff (a b : BinOp) : binOpEq a b = true ↔ a = b := by
  constructor
  · intro h
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)
  · intro h
    subst h
    exact binOpEq_refl a

noncomputable def evalBinOp : BinOp → Val → Val → Option Val
  | .add, .i32 a, .i32 b => some (.i32 (add32 a b))
  | .eq, .i32 a, .i32 b => some (.bool (Nat.beq (norm32 a) (norm32 b)))
  | .eq, .bool a, .bool b => some (.bool (boolEq a b))
  | .ne, .i32 a, .i32 b => some (.bool (Bool.not (Nat.beq (norm32 a) (norm32 b))))
  | .ne, .bool a, .bool b => some (.bool (Bool.not (boolEq a b)))
  | .and, .bool a, .bool b => some (.bool (Bool.and a b))
  | .or, .bool a, .bool b => some (.bool (Bool.or a b))
  | _, _, _ => none

/-- Dynamic expression semantics. Both runtime lowering and compile-time
    `const` evaluation evaluate `blackBox e` identically to `e`. -/
noncomputable def evalExpr (st : Store) : Expr → Option Val
  | .lit v => some v
  | .var r => some (st r)
  | .not e =>
      match evalExpr st e with
      | some (.bool b) => some (.bool (Bool.not b))
      | _ => none
  | .bin op lhs rhs =>
      match evalExpr st lhs, evalExpr st rhs with
      | some v1, some v2 => evalBinOp op v1 v2
      | _, _ => none
  | .blackBox e => evalExpr st e

noncomputable def evalExprInMode (_mode : ConstEvalMode) (st : Store) (e : Expr) : Option Val :=
  evalExpr st e

theorem evalExpr_blackBox_id (st : Store) (e : Expr) :
    evalExpr st (.blackBox e) = evalExpr st e := rfl

theorem evalExpr_mode_invariant (st : Store) (e : Expr) :
    evalExprInMode .runtime st e = evalExprInMode .constEval st e := rfl

noncomputable def exprAllRegs (pred : Reg → Bool) : Expr → Bool
  | .lit _ => true
  | .var r => pred r
  | .not e => exprAllRegs pred e
  | .bin _ l r => Bool.and (exprAllRegs pred l) (exprAllRegs pred r)
  | .blackBox e => exprAllRegs pred e

theorem evalExpr_storeAgreeOn (pred : Reg → Bool) (e : Expr) (s1 s2 : Store)
    (hAgree : storeAgreeOn pred s1 s2)
    (hRegs : exprAllRegs pred e = true) :
    evalExpr s1 e = evalExpr s2 e := by
  induction e with
  | lit _ => rfl
  | var r =>
      unfold exprAllRegs at hRegs
      unfold evalExpr
      rw [hAgree r hRegs]
  | not inner ih =>
      unfold exprAllRegs at hRegs
      unfold evalExpr
      rw [ih hRegs]
  | bin op l r ihl ihr =>
      unfold exprAllRegs at hRegs
      cases hl : exprAllRegs pred l <;> cases hr : exprAllRegs pred r
      · rw [hl] at hRegs; cases hRegs
      · rw [hl] at hRegs; cases hRegs
      · rw [hl, hr] at hRegs; cases hRegs
      · unfold evalExpr
        rw [ihl hl, ihr hr]
  | blackBox inner ih =>
      unfold exprAllRegs at hRegs
      unfold evalExpr
      exact ih hRegs

/-- Renames `fromReg` to `toReg` inside an expression for call-site inlining. -/
noncomputable def renameExprReg (fromReg toReg : Reg) : Expr → Expr
  | .lit v => .lit v
  | .var r => if regEq r fromReg then .var toReg else .var r
  | .not e => .not (renameExprReg fromReg toReg e)
  | .bin op l r => .bin op (renameExprReg fromReg toReg l) (renameExprReg fromReg toReg r)
  | .blackBox e => .blackBox (renameExprReg fromReg toReg e)

theorem evalExpr_renameExprReg (fromReg toReg : Reg) (e : Expr) (sSrc sDst : Store)
    (hMap : sDst toReg = sSrc fromReg)
    (hRest : ∀ r, r ≠ fromReg → sDst r = sSrc r) :
    evalExpr sDst (renameExprReg fromReg toReg e) = evalExpr sSrc e := by
  induction e with
  | lit _ => rfl
  | var r =>
      dsimp only [renameExprReg]
      cases hEq : regEq r fromReg
      · have hne : r ≠ fromReg := by
          intro hh; subst hh; rw [regEq_refl r] at hEq; cases hEq
        simp only [evalExpr]
        exact congrArg some (hRest r hne)
      · have hIs := (regEq_eq_true_iff r fromReg).mp hEq
        subst hIs
        simp only [evalExpr]
        exact congrArg some hMap
  | not inner ih =>
      dsimp only [renameExprReg, evalExpr]
      rw [ih]
  | bin op l r ihl ihr =>
      dsimp only [renameExprReg, evalExpr]
      rw [ihl, ihr]
  | blackBox inner ih =>
      dsimp only [renameExprReg, evalExpr]
      exact ih

/-- Constant-folding optimizer modeling LLVM/MIR folding behavior across
    `core::hint::black_box`:
      * folds constant `.not (.lit (.bool b))` and `.bin op (.lit v1) (.lit v2)`,
      * NEVER unwraps or propagates constants out of `Expr.blackBox`. -/
noncomputable def constFoldExpr : Expr → Expr
  | .lit v => .lit v
  | .var r => .var r
  | .not e =>
      match constFoldExpr e with
      | .lit (.bool b) => .lit (.bool (Bool.not b))
      | e' => .not e'
  | .bin op lhs rhs =>
      let l' := constFoldExpr lhs
      let r' := constFoldExpr rhs
      match l', r' with
      | .lit v1, .lit v2 =>
          match evalBinOp op v1 v2 with
          | some out => .lit out
          | none => .bin op (.lit v1) (.lit v2)
      | _, _ => .bin op l' r'
  | .blackBox e => .blackBox (constFoldExpr e)

noncomputable def isLiteralExpr : Expr → Bool
  | .lit _ => true
  | _ => false

noncomputable def isBarrierExpr : Expr → Bool
  | .blackBox _ => true
  | _ => false

noncomputable def hasBarrierSubexpr : Expr → Bool
  | .lit _ => false
  | .var _ => false
  | .not e => hasBarrierSubexpr e
  | .bin _ l r => Bool.or (hasBarrierSubexpr l) (hasBarrierSubexpr r)
  | .blackBox _ => true

theorem constFoldExpr_sound (e : Expr) (st : Store) :
    evalExpr st (constFoldExpr e) = evalExpr st e := by
  induction e with
  | lit _ => rfl
  | var _ => rfl
  | not inner ih =>
      unfold constFoldExpr evalExpr
      rw [← ih]
      cases constFoldExpr inner with
      | lit v =>
          cases v with
          | unit => rfl
          | bool _ => rfl
          | i32 _ => rfl
      | var _ => rfl
      | not _ => rfl
      | bin _ _ _ => rfl
      | blackBox _ => rfl
  | bin op lhs rhs ihl ihr =>
      unfold constFoldExpr evalExpr
      rw [← ihl, ← ihr]
      cases constFoldExpr lhs <;> cases constFoldExpr rhs
      all_goals try rfl
      case lit.lit v1 v2 =>
        dsimp only []
        cases hbin : evalBinOp op v1 v2 with
        | none => simp only [evalExpr, hbin]
        | some out => simp only [evalExpr, hbin]
  | blackBox inner ih =>
      unfold constFoldExpr evalExpr
      exact ih

theorem constFoldExpr_preserves_top_barrier (e : Expr) :
    isBarrierExpr (constFoldExpr (.blackBox e)) = true := rfl

theorem constFoldExpr_blocks_lit_collapse (e : Expr) :
    isLiteralExpr (constFoldExpr (.blackBox e)) = false := rfl

theorem constFoldExpr_bin_barriers_remain_unfolded
    (op : BinOp) (lhs rhs : Expr) :
    isLiteralExpr (constFoldExpr (.bin op (.blackBox lhs) (.blackBox rhs))) = false := rfl

theorem constFoldExpr_preserves_hasBarrierSubexpr (e : Expr) :
    hasBarrierSubexpr e = true → hasBarrierSubexpr (constFoldExpr e) = true := by
  induction e with
  | lit _ => intro h; cases h
  | var _ => intro h; cases h
  | not inner ih =>
      intro h
      unfold hasBarrierSubexpr at h
      have ih' := ih h
      unfold constFoldExpr
      cases hcf : constFoldExpr inner with
      | lit _ => rw [hcf] at ih'; cases ih'
      | var _ => rw [hcf] at ih'; exact ih'
      | not _ => rw [hcf] at ih'; exact ih'
      | bin _ _ _ => rw [hcf] at ih'; exact ih'
      | blackBox _ => rfl
  | bin op lhs rhs ihl ihr =>
      intro h
      unfold hasBarrierSubexpr at h
      have hDisj : hasBarrierSubexpr lhs = true ∨ hasBarrierSubexpr rhs = true := by
        cases hbL : hasBarrierSubexpr lhs <;> cases hbR : hasBarrierSubexpr rhs
        · rw [hbL, hbR] at h; cases h
        · exact Or.inr rfl
        · exact Or.inl rfl
        · exact Or.inl rfl
      have hCfDisj : hasBarrierSubexpr (constFoldExpr lhs) = true ∨
                     hasBarrierSubexpr (constFoldExpr rhs) = true := by
        cases hDisj with
        | inl hl => exact Or.inl (ihl hl)
        | inr hr => exact Or.inr (ihr hr)
      unfold constFoldExpr
      cases hcfL : constFoldExpr lhs <;> cases hcfR : constFoldExpr rhs
      all_goals try exact Bool.true_eq_true
      all_goals try rfl
      case lit.lit v1 v2 =>
        cases hCfDisj with
        | inl hl => rw [hcfL] at hl; cases hl
        | inr hr => rw [hcfR] at hr; cases hr
      all_goals (
        dsimp only []
        unfold hasBarrierSubexpr
        cases hCfDisj with
        | inl hl =>
            rw [hcfL] at hl
            try simp only [hl, Bool.true_or]
            try rfl
        | inr hr =>
            rw [hcfR] at hr
            try simp only [hr, Bool.or_true]
            try rfl
      )
  | blackBox _ => intro _; rfl

theorem constFoldExpr_substReg_preserves_regs (fromReg toReg : Reg) (pred : Reg → Bool) (e : Expr)
    (hTo : pred toReg = true) (hE : exprAllRegs pred e = true) :
    exprAllRegs pred (renameExprReg fromReg toReg e) = true := by
  induction e with
  | lit _ => rfl
  | var r =>
      dsimp only [renameExprReg, exprAllRegs]
      unfold exprAllRegs at hE
      cases regEq r fromReg
      · exact hE
      · exact hTo
  | not inner ih =>
      dsimp only [renameExprReg, exprAllRegs]
      unfold exprAllRegs at hE
      exact ih hE
  | bin op l r ihl ihr =>
      dsimp only [renameExprReg, exprAllRegs]
      unfold exprAllRegs at hE
      cases hl : exprAllRegs pred l <;> cases hr : exprAllRegs pred r
      · rw [hl] at hE; cases hE
      · rw [hl] at hE; cases hE
      · rw [hl, hr] at hE; cases hE
      · rw [ihl hl, ihr hr]; rfl
  | blackBox inner ih =>
      dsimp only [renameExprReg, exprAllRegs]
      unfold exprAllRegs at hE
      exact ih hE

-- Witness expressions matching live `plain_fold` vs `black_box_no_fold` probe:
noncomputable def plainAddTwoThree : Expr :=
  .bin .add (.lit (.i32 2)) (.lit (.i32 3))

noncomputable def boxedAddTwoThree : Expr :=
  .bin .add (.blackBox (.lit (.i32 2))) (.blackBox (.lit (.i32 3)))

theorem plainAddTwoThree_folds :
    constFoldExpr plainAddTwoThree = .lit (.i32 5) := rfl

theorem boxedAddTwoThree_blocked :
    constFoldExpr boxedAddTwoThree = boxedAddTwoThree ∧
    isLiteralExpr (constFoldExpr boxedAddTwoThree) = false := ⟨rfl, rfl⟩

theorem plain_and_boxed_same_runtime_value (st : Store) :
    evalExpr st plainAddTwoThree = some (.i32 5) ∧
    evalExpr st boxedAddTwoThree = some (.i32 5) := ⟨rfl, rfl⟩

theorem const_blackBox_three_plus_four_evaluates_to_seven (st : Store) :
    evalExprInMode .constEval st (.blackBox (.bin .add (.lit (.i32 3)) (.lit (.i32 4)))) =
      some (.i32 7) := rfl

-- ============================================================================
-- Section 3: Compiler Flags, Attributes, Precedence, Cross-Crate Cost Checker
-- ============================================================================

inductive OptLevel : Type where
  | o0
  | o1
  | o2

inductive InlineAttr : Type where
  | none
  | hint
  | always
  | never

inductive OptimizeAttr : Type where
  | defaultOpt
  | doNotOptimize

inductive LlvmInlineAttr : Type where
  | none
  | inlineHint
  | alwaysInline
  | noInline

inductive AttrDiagnostic : Type where
  | unusedDuplicateInline (kept ignored : InlineAttr)
  | inlineIgnoredForExported

structure FnAttrs : Type where
  inline : InlineAttr
  optimize : OptimizeAttr
  cold : Bool
  isExported : Bool
  preserveUbChecks : Bool
  hasTargetFeatures : Bool
  llvmMajorBelow23 : Bool
  hasExternIndicator : Bool

structure MirCostMetrics : Type where
  calls : Nat
  resumes : Nat
  landingPads : Nat
  statements : Nat

structure CompilerFlags : Type where
  opt : OptLevel
  debugAssertions : Bool
  ubChecksFlag : Option Bool
  incremental : Bool
  inlineLlvm : Bool
  crossCrateThreshold : Nat

inductive UbCheckMode : Type where
  | abortOnFalse
  | ubOnFalse

noncomputable def effectiveUbChecks (cfg : CompilerFlags) : Bool :=
  match cfg.ubChecksFlag with
  | some b => b
  | none => cfg.debugAssertions

noncomputable def ubModeFromFlags (cfg : CompilerFlags) : UbCheckMode :=
  if effectiveUbChecks cfg then .abortOnFalse else .ubOnFalse

/-- Models `Session::mir_opt_level` (`compiler/rustc_session/src/session.rs:617-622`). -/
noncomputable def mirOptLevel (cfg : CompilerFlags) : Nat :=
  match cfg.opt with
  | .o0 => 1
  | .o1 => 2
  | .o2 => 2

/-- Models `Inline::policy` (`compiler/rustc_mir_transform/src/inline.rs:46-61`). -/
noncomputable def mirNormalInlinerActive (cfg : CompilerFlags) : Bool :=
  match cfg.opt with
  | .o2 => Bool.not cfg.incremental
  | _ => false

/-- Models `Builder::assume` (`compiler/rustc_codegen_llvm/src/intrinsic.rs:1034-1038`). -/
noncomputable def llvmEmitsAssume (cfg : CompilerFlags) : Bool :=
  match cfg.opt with
  | .o0 => false
  | .o1 => true
  | .o2 => true

/-- Models `InlineParser` (`rustc_attr_parsing/src/attributes/inline.rs`):
    `Single<T>` with `ON_DUPLICATE = WarnButFutureError` keeps the FIRST
    parsed non-none `#[inline(...)]` attribute and emits `unused_attributes`
    diagnostics on every later attribute in attribute list order. -/
noncomputable def parseInlineAttrsAux (kept : Option InlineAttr) :
    List InlineAttr → InlineAttr × List AttrDiagnostic
  | [] =>
      match kept with
      | some k => (k, [])
      | none => (.none, [])
  | a :: rest =>
      match a with
      | .none => parseInlineAttrsAux kept rest
      | _ =>
          match kept with
          | none => parseInlineAttrsAux (some a) rest
          | some first =>
              let tail := parseInlineAttrsAux (some first) rest
              (tail.1, .unusedDuplicateInline first a :: tail.2)

/-- Combines `InlineParser` first-wins precedence with `check_attr.rs:604-623`:
    exporting a function via `no_mangle` triggers `InlineIgnoredForExported`
    precisely when resolved `kind != InlineAttr.never`. -/
noncomputable def resolveInlineAttrsWithExportCheck
    (isExported : Bool) (attrs : List InlineAttr) :
    InlineAttr × List AttrDiagnostic :=
  let parsed := parseInlineAttrsAux none attrs
  let extra :=
    if isExported then
      match parsed.1 with
      | .none => []
      | .never => []
      | _ => [.inlineIgnoredForExported]
    else []
  (parsed.1, parsed.2 ++ extra)

/-- Models `rustc_mir_transform/src/cross_crate_inline.rs`:
    `cross_crate_inlinable` gate without LTO (`calls == 0 && resumes == 0 &&
    landing_pads == 0 && statements <= threshold`). -/
noncomputable def crossCrateInlinable
    (cfg : CompilerFlags) (fa : FnAttrs) (m : MirCostMetrics) : Bool :=
  if fa.hasExternIndicator then false
  else
    match fa.inline with
    | .never => false
    | .hint => true
    | .always => true
    | .none =>
        if cfg.incremental then false
        else
          match cfg.opt, mirNormalInlinerActive cfg with
          | .o0, false => false
          | _, _ =>
              Bool.and
                (Nat.beq m.calls 0)
                (Bool.and
                  (Nat.beq m.resumes 0)
                  (Bool.and (Nat.beq m.landingPads 0)
                    (Nat.ble m.statements cfg.crossCrateThreshold)))

/-- Models `rustc_codegen_llvm/src/attributes.rs:inline_attr`. -/
noncomputable def lowerInlineToLlvm (cfg : CompilerFlags) (fa : FnAttrs) : LlvmInlineAttr :=
  if Bool.not cfg.inlineLlvm then .noInline
  else
    let effective :=
      match fa.inline, fa.optimize with
      | _, .doNotOptimize => InlineAttr.never
      | k, _ => k
    match effective with
    | .hint => .inlineHint
    | .always =>
        if Bool.and fa.hasTargetFeatures fa.llvmMajorBelow23 then .inlineHint
        else .alwaysInline
    | .never => .noInline
    | .none => .none

/-- Models LLVM `AlwaysInlinerPass` (active even at `-O0`) vs threshold inliners. -/
noncomputable def llvmShouldInlineCall
    (opt : OptLevel) (llAttr : LlvmInlineAttr) (_cold : Bool) : Bool :=
  match llAttr with
  | .noInline => false
  | .alwaysInline => true
  | .inlineHint =>
      match opt with
      | .o0 => false
      | _ => true
  | .none =>
      match opt with
      | .o2 => true
      | _ => false

theorem duplicate_always_then_never_keeps_always :
    (resolveInlineAttrsWithExportCheck false [.always, .never]).1 = .always := rfl

theorem duplicate_never_then_always_keeps_never :
    (resolveInlineAttrsWithExportCheck false [.never, .always]).1 = .never := rfl

theorem exported_always_then_never_emits_both_diags :
    resolveInlineAttrsWithExportCheck true [.always, .never] =
      (.always, [.unusedDuplicateInline .always .never, .inlineIgnoredForExported]) := rfl

theorem exported_never_then_always_skips_export_warning :
    resolveInlineAttrsWithExportCheck true [.never, .always] =
      (.never, [.unusedDuplicateInline .never .always]) := rfl

theorem llvm_alwaysInline_inlines_even_at_o0 (cold : Bool) :
    llvmShouldInlineCall .o0 .alwaysInline cold = true := rfl

theorem llvm_noInline_never_inlines (opt : OptLevel) (cold : Bool) :
    llvmShouldInlineCall opt .noInline cold = false := by
  cases opt <;> rfl

theorem llvm_cold_only_does_not_force_noinline (cfg : CompilerFlags) (fa : FnAttrs)
    (hCold : fa.cold = true) (hInline : fa.inline = .none)
    (hOpt : fa.optimize = .defaultOpt) (hLlvm : cfg.inlineLlvm = true) :
    lowerInlineToLlvm cfg fa = .none := by
  have _ := hCold
  unfold lowerInlineToLlvm
  rw [hLlvm, hOpt, hInline]
  rfl

theorem optnone_forces_noinline (cfg : CompilerFlags) (fa : FnAttrs)
    (hLlvm : cfg.inlineLlvm = true) (hOpt : fa.optimize = .doNotOptimize) :
    lowerInlineToLlvm cfg fa = .noInline := by
  unfold lowerInlineToLlvm
  rw [hLlvm, hOpt]
  rfl

theorem targetFeature_below23_downgrades_always_to_hint
    (cfg : CompilerFlags) (fa : FnAttrs)
    (hLlvm : cfg.inlineLlvm = true)
    (hOpt : fa.optimize = .defaultOpt)
    (hAlw : fa.inline = .always)
    (hTf : fa.hasTargetFeatures = true)
    (hVer : fa.llvmMajorBelow23 = true) :
    lowerInlineToLlvm cfg fa = .inlineHint := by
  unfold lowerInlineToLlvm
  rw [hLlvm, hOpt, hAlw, hTf, hVer]
  rfl

theorem crossCrate_never_disables_inlinable (cfg : CompilerFlags) (fa : FnAttrs)
    (m : MirCostMetrics) (hInline : fa.inline = .never) :
    crossCrateInlinable cfg fa m = false := by
  unfold crossCrateInlinable
  cases fa.hasExternIndicator <;> simp only [hInline] <;> rfl

theorem crossCrate_nonLeaf_disables_unannotated (cfg : CompilerFlags) (fa : FnAttrs)
    (m : MirCostMetrics) (hNone : fa.inline = .none) (hCall : Nat.beq m.calls 0 = false) :
    crossCrateInlinable cfg fa m = false := by
  unfold crossCrateInlinable
  cases fa.hasExternIndicator
  · simp only [hNone]
    cases cfg.incremental
    · cases cfg.opt <;> cases mirNormalInlinerActive cfg <;> simp only [hCall] <;> rfl
    · rfl
  · rfl

-- ============================================================================
-- Section 4: Structured MIR/LLVM Programs & Structural-Fuel Semantics
-- ============================================================================

inductive Inst : Type where
  | assign (dst : Reg) (rhs : Expr)
  | blackBoxAssign (dst : Reg) (rhs : Expr)
  | checkedAssume (cond : Expr)
  | assume (cond : Expr)
  | checkedUnreachable (preserveUb : Bool)
  | unreachable
  | branchOn (cond : Expr) (thenBr elseBr : List Inst)
  | callFn (dst : Reg) (callee : FnId) (arg : Expr)
  | ret (rhs : Expr)

structure FnDef : Type where
  param : Reg
  attrs : FnAttrs
  body : List Inst

noncomputable def FnTable : Type := FnId → FnDef

inductive Outcome : Type where
  | ok (v : Val)
  | abort
  | ub
  | fault

inductive BlockOutcome : Type where
  | next (st : Store)
  | ret (v : Val)
  | abort
  | ub
  | fault

noncomputable def blockToOutcome : BlockOutcome → Outcome
  | .next _ => .ok .unit
  | .ret v => .ok v
  | .abort => .abort
  | .ub => .ub
  | .fault => .fault

-- Structural statement-list evaluator parameterized by a call oracle
-- `onCall : FnId → Val → Outcome`. Separating structural CFG execution
-- from recursive call depth eliminates fuel drift under pruning and inlining.
mutual
  /-- Evaluates one structured instruction against a call oracle. -/
  noncomputable def evalOne
      (ubMode : UbCheckMode)
      (emitAssume : Bool)
      (onCall : FnId → Val → Outcome)
      (st : Store) :
      Inst → BlockOutcome
    | .assign dst rhs =>
        match evalExpr st rhs with
        | some v => .next (updateStore st dst v)
        | none => .fault
    | .blackBoxAssign dst rhs =>
        match evalExpr st rhs with
        | some v => .next (updateStore st dst v)
        | none => .fault
    | .checkedAssume cond =>
        match ubMode, emitAssume with
        | .abortOnFalse, _ =>
            match evalExpr st cond with
            | some (.bool true) => .next st
            | some (.bool false) => .abort
            | _ => .fault
        | .ubOnFalse, true =>
            match evalExpr st cond with
            | some (.bool true) => .next st
            | some (.bool false) => .ub
            | _ => .fault
        | .ubOnFalse, false =>
            -- Downstream `-O0`: `switchInt(UbChecks)` skips precondition_check
            -- and LLVM `OptLevel::No` suppresses `@llvm.assume`.
            .next st
    | .assume cond =>
        if emitAssume then
          match evalExpr st cond with
          | some (.bool true) => .next st
          | some (.bool false) =>
              match ubMode with
              | .abortOnFalse => .abort
              | .ubOnFalse => .ub
          | _ => .fault
        else
          .next st
    | .checkedUnreachable preserveUb =>
        if preserveUb then
          match ubMode, emitAssume with
          | .abortOnFalse, _ => .abort
          | .ubOnFalse, true => .ub
          | .ubOnFalse, false => .abort
        else
          match ubMode with
          | .abortOnFalse => .abort
          | .ubOnFalse => .ub
    | .unreachable =>
        match ubMode with
        | .abortOnFalse => .abort
        | .ubOnFalse => .ub
    | .branchOn cond thenBr elseBr =>
        match evalExpr st cond with
        | some (.bool true) => evalBlock ubMode emitAssume onCall st thenBr
        | some (.bool false) => evalBlock ubMode emitAssume onCall st elseBr
        | _ => .fault
    | .callFn dst callee arg =>
        match evalExpr st arg with
        | none => .fault
        | some argv =>
            match onCall callee argv with
            | .ok res => .next (updateStore st dst res)
            | .abort => .abort
            | .ub => .ub
            | .fault => .fault
    | .ret rhs =>
        match evalExpr st rhs with
        | some v => .ret v
        | none => .fault

  noncomputable def evalBlock
      (ubMode : UbCheckMode)
      (emitAssume : Bool)
      (onCall : FnId → Val → Outcome)
      (st : Store) :
      List Inst → BlockOutcome
    | [] => .next st
    | inst :: rest =>
        match evalOne ubMode emitAssume onCall st inst with
        | .next st' => evalBlock ubMode emitAssume onCall st' rest
        | .ret v => .ret v
        | .abort => .abort
        | .ub => .ub
        | .fault => .fault
end

/-- Bounded-call-depth top-level program evaluator. -/
noncomputable def evalFnCall
    (ubMode : UbCheckMode)
    (emitAssume : Bool)
    (fns : FnTable) :
    Nat → FnId → Val → Outcome
  | 0, _, _ => .fault
  | fuel + 1, fid, argv =>
      let defn := fns fid
      let calleeSt := updateStore emptyStore defn.param argv
      blockToOutcome
        (evalBlock ubMode emitAssume (evalFnCall ubMode emitAssume fns fuel) calleeSt defn.body)

noncomputable def evalProg
    (ubMode : UbCheckMode)
    (emitAssume : Bool)
    (fns : FnTable)
    (fuel : Nat)
    (st : Store)
    (prog : List Inst) : Outcome :=
  blockToOutcome
    (evalBlock ubMode emitAssume (evalFnCall ubMode emitAssume fns fuel) st prog)

theorem evalBlock_append
    (ubMode : UbCheckMode)
    (emitAssume : Bool)
    (onCall : FnId → Val → Outcome)
    (xs ys : List Inst)
    (st : Store) :
    evalBlock ubMode emitAssume onCall st (xs ++ ys) =
      match evalBlock ubMode emitAssume onCall st xs with
      | .next st' => evalBlock ubMode emitAssume onCall st' ys
      | .ret v => .ret v
      | .abort => .abort
      | .ub => .ub
      | .fault => .fault := by
  induction xs generalizing st with
  | nil => rfl
  | cons x rest ih =>
      dsimp only [List.cons_append]
      simp only [evalBlock]
      cases hOne : evalOne ubMode emitAssume onCall st x with
      | next st' => exact ih st'
      | ret _ => rfl
      | abort => rfl
      | ub => rfl
      | fault => rfl

-- ============================================================================
-- Section 5: Theorem Family 1 — Debug Refinement & Precompiled `core` `-O0`
-- ============================================================================

noncomputable def CallOracleRefines
    (oracleUb oracleAbort : FnId → Val → Outcome) : Prop :=
  ∀ (f : FnId) (arg res : Val),
    oracleUb f arg = .ok res → oracleAbort f arg = .ok res

theorem blockRefines_of_oracle
    (oracleUb oracleAbort : FnId → Val → Outcome)
    (hOracle : CallOracleRefines oracleUb oracleAbort) :
    ∀ (inst : Inst) (st : Store),
      (∀ val, evalOne .ubOnFalse true oracleUb st inst = .ret val →
        evalOne .abortOnFalse true oracleAbort st inst = .ret val) ∧
      (∀ st', evalOne .ubOnFalse true oracleUb st inst = .next st' →
        evalOne .abortOnFalse true oracleAbort st inst = .next st') := by
  intro inst st
  -- Wait: `evalOne` and `evalBlock` are mutually recursive; induct cleanly using mutual motive:
  exact
    @Inst.rec
      (fun i =>
        ∀ s : Store,
          (∀ val, evalOne .ubOnFalse true oracleUb s i = .ret val →
            evalOne .abortOnFalse true oracleAbort s i = .ret val) ∧
          (∀ s', evalOne .ubOnFalse true oracleUb s i = .next s' →
            evalOne .abortOnFalse true oracleAbort s i = .next s'))
      (fun l =>
        ∀ s : Store,
          (∀ val, evalBlock .ubOnFalse true oracleUb s l = .ret val →
            evalBlock .abortOnFalse true oracleAbort s l = .ret val) ∧
          (∀ s', evalBlock .ubOnFalse true oracleUb s l = .next s' →
            evalBlock .abortOnFalse true oracleAbort s l = .next s'))
      (fun dst rhs s => by
        constructor <;> intro v h
        · simp only [evalOne] at h; generalize _hv : evalExpr s rhs = mv at h; cases mv <;> cases h
        · simp only [evalOne] at h ⊢; generalize _hv : evalExpr s rhs = mv at h ⊢; cases mv <;> exact h)
      (fun dst rhs s => by
        constructor <;> intro v h
        · simp only [evalOne] at h; generalize _hv : evalExpr s rhs = mv at h; cases mv <;> cases h
        · simp only [evalOne] at h ⊢; generalize _hv : evalExpr s rhs = mv at h ⊢; cases mv <;> exact h)
      (fun cond s => by
        constructor <;> intro v h
        · simp only [evalOne] at h
          generalize _hv : evalExpr s cond = mv at h
          cases mv with
          | none => cases h
          | some w =>
              cases w with
              | unit => cases h
              | i32 _ => cases h
              | bool b => cases b <;> cases h
        · simp only [evalOne] at h ⊢
          generalize _hv : evalExpr s cond = mv at h ⊢
          cases mv with
          | none => cases h
          | some w =>
              cases w with
              | unit => cases h
              | i32 _ => cases h
              | bool b =>
                  cases b with
                  | false => cases h
                  | true => exact h)
      (fun cond s => by
        constructor <;> intro v h
        · simp only [evalOne] at h
          generalize _hv : evalExpr s cond = mv at h
          cases mv with
          | none => cases h
          | some w =>
              cases w with
              | unit => cases h
              | i32 _ => cases h
              | bool b => cases b <;> cases h
        · simp only [evalOne] at h ⊢
          generalize _hv : evalExpr s cond = mv at h ⊢
          cases mv with
          | none => cases h
          | some w =>
              cases w with
              | unit => cases h
              | i32 _ => cases h
              | bool b =>
                  cases b with
                  | false => cases h
                  | true => exact h)
      (fun pUb s => by
        constructor <;> intro v h <;> simp only [evalOne] at h <;> cases pUb <;> cases h)
      (fun s => by
        constructor <;> intro v h <;> simp only [evalOne] at h <;> cases h)
      (fun cond tBr eBr iht ihe s => by
        constructor <;> intro v h
        · simp only [evalOne] at h ⊢
          generalize _hv : evalExpr s cond = mv at h ⊢
          cases mv with
          | none => cases h
          | some w =>
              cases w with
              | unit => cases h
              | i32 _ => cases h
              | bool b =>
                  cases b with
                  | false => exact (ihe s).1 v h
                  | true => exact (iht s).1 v h
        · simp only [evalOne] at h ⊢
          generalize _hv : evalExpr s cond = mv at h ⊢
          cases mv with
          | none => cases h
          | some w =>
              cases w with
              | unit => cases h
              | i32 _ => cases h
              | bool b =>
                  cases b with
                  | false => exact (ihe s).2 v h
                  | true => exact (iht s).2 v h)
      (fun dst callee arg s => by
        constructor <;> intro v h
        · simp only [evalOne] at h
          generalize _hv : evalExpr s arg = mv at h
          cases mv with
          | none => cases h
          | some argv =>
              dsimp only [] at h
              generalize _hc : oracleUb callee argv = oc at h
              cases oc <;> cases h
        · simp only [evalOne] at h ⊢
          generalize _hv : evalExpr s arg = mv at h ⊢
          cases mv with
          | none => cases h
          | some argv =>
              dsimp only [] at h ⊢
              cases hc : oracleUb callee argv with
              | abort => rw [hc] at h; cases h
              | ub => rw [hc] at h; cases h
              | fault => rw [hc] at h; cases h
              | ok res =>
                  rw [hc] at h
                  dsimp only [] at h
                  rw [hOracle callee argv res hc]
                  exact h)
      (fun rhs s => by
        constructor <;> intro v h
        · simp only [evalOne] at h ⊢; generalize _hv : evalExpr s rhs = mv at h ⊢; cases mv <;> exact h
        · simp only [evalOne] at h; generalize _hv : evalExpr s rhs = mv at h; cases mv <;> cases h)
      (fun s => by
        constructor <;> intro v h
        · simp only [evalBlock] at h; cases h
        · exact h)
      (fun x xs ihx ihxs s => by
        constructor <;> intro v h
        · simp only [evalBlock] at h ⊢
          cases hx : evalOne .ubOnFalse true oracleUb s x with
          | abort => rw [hx] at h; cases h
          | ub => rw [hx] at h; cases h
          | fault => rw [hx] at h; cases h
          | ret r =>
              rw [hx] at h
              rw [(ihx s).1 r hx]
              exact h
          | next s' =>
              rw [hx] at h
              rw [(ihx s).2 s' hx]
              exact (ihxs s').1 v h
        · simp only [evalBlock] at h ⊢
          cases hx : evalOne .ubOnFalse true oracleUb s x with
          | abort => rw [hx] at h; cases h
          | ub => rw [hx] at h; cases h
          | fault => rw [hx] at h; cases h
          | ret r => rw [hx] at h; cases h
          | next s' =>
              rw [hx] at h
              rw [(ihx s).2 s' hx]
              exact (ihxs s').2 v h)
      inst st

theorem evalBlock_refines_of_oracle
    (oracleUb oracleAbort : FnId → Val → Outcome)
    (hOracle : CallOracleRefines oracleUb oracleAbort)
    (prog : List Inst) (st : Store) :
    (∀ val, evalBlock .ubOnFalse true oracleUb st prog = .ret val →
      evalBlock .abortOnFalse true oracleAbort st prog = .ret val) ∧
    (∀ st', evalBlock .ubOnFalse true oracleUb st prog = .next st' →
      evalBlock .abortOnFalse true oracleAbort st prog = .next st') := by
  induction prog generalizing st with
  | nil =>
      constructor <;> intro v h
      · cases h
      · exact h
  | cons x rest ih =>
      have hInst := blockRefines_of_oracle oracleUb oracleAbort hOracle x st
      constructor <;> intro v h
      · simp only [evalBlock] at h ⊢
        cases hx : evalOne .ubOnFalse true oracleUb st x with
        | abort => rw [hx] at h; cases h
        | ub => rw [hx] at h; cases h
        | fault => rw [hx] at h; cases h
        | ret r => rw [hx] at h; rw [hInst.1 r hx]; exact h
        | next st' => rw [hx] at h; rw [hInst.2 st' hx]; exact (ih st').1 v h
      · simp only [evalBlock] at h ⊢
        cases hx : evalOne .ubOnFalse true oracleUb st x with
        | abort => rw [hx] at h; cases h
        | ub => rw [hx] at h; cases h
        | fault => rw [hx] at h; cases h
        | ret r => rw [hx] at h; cases h
        | next st' => rw [hx] at h; rw [hInst.2 st' hx]; exact (ih st').2 v h

/-- Main Theorem Family 1 (`evalFnCall` refinement): Every defined return value
    obtained under `ubOnFalse` is identically reproduced under `abortOnFalse`. -/
theorem evalFnCall_abortOnFalse_refines_ubOnFalse (fns : FnTable) (fuel : Nat) :
    CallOracleRefines (evalFnCall .ubOnFalse true fns fuel)
                      (evalFnCall .abortOnFalse true fns fuel) := by
  induction fuel with
  | zero =>
      intro f arg res h
      dsimp only [evalFnCall] at h
      cases h
  | succ k ih =>
      intro f arg res h
      dsimp only [evalFnCall] at h ⊢
      have hBlk := evalBlock_refines_of_oracle
        (evalFnCall .ubOnFalse true fns k)
        (evalFnCall .abortOnFalse true fns k)
        ih (fns f).body (updateStore emptyStore (fns f).param arg)
      cases hb : evalBlock .ubOnFalse true (evalFnCall .ubOnFalse true fns k)
          (updateStore emptyStore (fns f).param arg) (fns f).body with
      | abort => rw [hb] at h; cases h
      | ub => rw [hb] at h; cases h
      | fault => rw [hb] at h; cases h
      | ret r =>
          rw [hb] at h
          rw [hBlk.1 r hb]
          exact h
      | next st' =>
          rw [hb] at h
          rw [hBlk.2 st' hb]
          exact h

/-- Top-level Program Refinement Theorem (`evalProg`):
    For ANY program `prog`, initial store `st`, function table `fns`, fuel `fuel`,
    and defined value `v`, if `evalProg .ubOnFalse true fns fuel st prog = .ok v`,
    then `evalProg .abortOnFalse true fns fuel st prog = .ok v`. -/
theorem abortOnFalse_soundly_refines_ubOnFalse
    (fns : FnTable) (fuel : Nat) (st : Store) (prog : List Inst) (v : Val)
    (h : evalProg .ubOnFalse true fns fuel st prog = .ok v) :
    evalProg .abortOnFalse true fns fuel st prog = .ok v := by
  unfold evalProg at h ⊢
  have hBlk := evalBlock_refines_of_oracle
    (evalFnCall .ubOnFalse true fns fuel)
    (evalFnCall .abortOnFalse true fns fuel)
    (evalFnCall_abortOnFalse_refines_ubOnFalse fns fuel)
    prog st
  cases hb : evalBlock .ubOnFalse true (evalFnCall .ubOnFalse true fns fuel) st prog with
  | abort => rw [hb] at h; cases h
  | ub => rw [hb] at h; cases h
  | fault => rw [hb] at h; cases h
  | ret r =>
      rw [hb] at h
      rw [hBlk.1 r hb]
      exact h
  | next st' =>
      rw [hb] at h
      rw [hBlk.2 st' hb]
      exact h

/-- Pre-compiled `core` (`preserveUbChecks = true`) + LLVM `-O0` (`emitAssume = false`)
    boundary theorem directly matching empirical `-O0 -C debug-assertions=off -Z ub-checks=no`:
      * `unreachable_unchecked()` aborts (`Outcome.abort`, `SIGABRT (-6)`),
      * `assert_unchecked(false)` skips its runtime check and completes (`Outcome.ok`).
    Under `-O1`/`-O2` (`emitAssume = true`), LLVM keeps `@llvm.assume(false)` so BOTH
    exhibit `.ub` in `ubOnFalse` and `.abort` in `abortOnFalse`. -/
theorem precompiled_core_o0_vs_opt1_boundary (fns : FnTable) (fuel : Nat) (st : Store) :
    evalProg .ubOnFalse false fns fuel st [.checkedUnreachable true, .ret (.lit (.i32 42))] = .abort ∧
    evalProg .ubOnFalse false fns fuel st [.checkedAssume (.lit (.bool false)), .ret (.lit (.i32 42))] =
      .ok (.i32 42) ∧
    evalProg .ubOnFalse true fns fuel st [.checkedUnreachable true, .ret (.lit (.i32 42))] = .ub ∧
    evalProg .ubOnFalse true fns fuel st [.checkedAssume (.lit (.bool false)), .ret (.lit (.i32 42))] = .ub ∧
    evalProg .abortOnFalse true fns fuel st [.checkedAssume (.lit (.bool false)), .ret (.lit (.i32 42))] = .abort := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- Section 6: Theorem Family 2 — Assume-Guided Dead-Branch Pruning & Range
-- ============================================================================

/-- Exact structural equality on `Expr` implying syntactic identity `e1 = e2`. -/
noncomputable def exprStructEq : Expr → Expr → Bool
  | .lit v1, .lit v2 => valStructEq v1 v2
  | .var ra, .var rb => regEq ra rb
  | .not e1, .not e2 => exprStructEq e1 e2
  | .bin op1 l1 r1, .bin op2 l2 r2 =>
      Bool.and (binOpEq op1 op2) (Bool.and (exprStructEq l1 l2) (exprStructEq r1 r2))
  | .blackBox e1, .blackBox e2 => exprStructEq e1 e2
  | _, _ => false

theorem exprStructEq_refl (e : Expr) : exprStructEq e e = true := by
  induction e with
  | lit v => exact valStructEq_refl v
  | var r => exact regEq_refl r
  | not _ ih => exact ih
  | bin op _ _ ihl ihr =>
      unfold exprStructEq
      rw [binOpEq_refl op, ihl, ihr]
      rfl
  | blackBox _ ih => exact ih

theorem exprStructEq_eq_true_iff (e1 e2 : Expr) : exprStructEq e1 e2 = true ↔ e1 = e2 := by
  constructor
  · intro h
    induction e1 generalizing e2 with
    | lit v1 =>
        cases e2 with
        | lit v2 =>
            unfold exprStructEq at h
            have hv := (valStructEq_eq_true_iff v1 v2).mp h
            subst hv; rfl
        | _ => cases h
    | var ra =>
        cases e2 with
        | var rb =>
            unfold exprStructEq at h
            have hr := (regEq_eq_true_iff ra rb).mp h
            subst hr; rfl
        | _ => cases h
    | not e1 ih =>
        cases e2 with
        | not e2 =>
            unfold exprStructEq at h
            rw [ih e2 h]
        | _ => cases h
    | bin op1 la lb ihl ihr =>
        cases e2 with
        | bin op2 ra rb =>
            unfold exprStructEq at h
            cases hop : binOpEq op1 op2 <;> cases hl : exprStructEq la ra <;> cases hr : exprStructEq lb rb
            all_goals try (simp only [hop, hl, hr] at h; cases h)
            have hop' := (binOpEq_eq_true_iff op1 op2).mp hop
            have hl' := ihl ra hl
            have hr' := ihr rb hr
            subst hop'; subst hl'; subst hr'; rfl
        | _ => cases h
    | blackBox e1 ih =>
        cases e2 with
        | blackBox e2 =>
            unfold exprStructEq at h
            rw [ih e2 h]
        | _ => cases h
  · intro h
    subst h
    exact exprStructEq_refl e1

/-- Detects syntactic contradictions where `evalExpr st p = some (.bool true)`
    guarantees `evalExpr st g = some (.bool false)`. -/
noncomputable def exprContradicts : Expr → Expr → Bool
  | p, .not p' => exprStructEq p p'
  | .not p, p' => exprStructEq p p'
  | .bin .ne l1 r1, .bin .eq l2 r2 => Bool.and (exprStructEq l1 l2) (exprStructEq r1 r2)
  | .bin .eq l1 r1, .bin .ne l2 r2 => Bool.and (exprStructEq l1 l2) (exprStructEq r1 r2)
  | .lit (.bool true), .lit (.bool false) => true
  | .lit (.bool false), .lit (.bool true) => true
  | _, _ => false

theorem exprContradicts_sound (p g : Expr) (st : Store)
    (hCon : exprContradicts p g = true)
    (hTrue : evalExpr st p = some (.bool true)) :
    evalExpr st g = some (.bool false) := by
  cases p <;> cases g <;> unfold exprContradicts at hCon
  all_goals try cases hCon
  -- Case 1: `(anything, .not e2)` matches first rule `exprStructEq p e2`:
  case lit.not v e2 =>
    have hEq := (exprStructEq_eq_true_iff (.lit v) e2).mp hCon
    rw [← hEq]; unfold evalExpr; rw [hTrue]; rfl
  case var.not r e2 =>
    have hEq := (exprStructEq_eq_true_iff (.var r) e2).mp hCon
    rw [← hEq]; unfold evalExpr; rw [hTrue]; rfl
  case not.not e1 e2 =>
    have hEq := (exprStructEq_eq_true_iff (.not e1) e2).mp hCon
    rw [← hEq]; unfold evalExpr; rw [hTrue]; rfl
  case bin.not op l r e2 =>
    have hEq := (exprStructEq_eq_true_iff (.bin op l r) e2).mp hCon
    rw [← hEq]; unfold evalExpr; rw [hTrue]; rfl
  case blackBox.not e1 e2 =>
    have hEq := (exprStructEq_eq_true_iff (.blackBox e1) e2).mp hCon
    rw [← hEq]; unfold evalExpr; rw [hTrue]; rfl
  -- Case 2: `(.not e1, non-not)` matches second rule `exprStructEq e1 g`:
  case not.lit e1 v =>
    have hEq := (exprStructEq_eq_true_iff e1 (.lit v)).mp hCon
    subst hEq
    simp only [evalExpr] at hTrue ⊢
    cases v with
    | unit => cases hTrue
    | i32 _ => cases hTrue
    | bool b => cases b <;> first | rfl | cases hTrue
  case not.var e1 r =>
    have hEq := (exprStructEq_eq_true_iff e1 (.var r)).mp hCon
    subst hEq
    simp only [evalExpr] at hTrue ⊢
    generalize st r = vr at hTrue ⊢
    cases vr with
    | unit => cases hTrue
    | i32 _ => cases hTrue
    | bool b =>
        cases b with
        | false => rfl
        | true => cases hTrue
  case not.bin e1 op l r =>
    have hEq := (exprStructEq_eq_true_iff e1 (.bin op l r)).mp hCon
    subst hEq
    simp only [evalExpr] at hTrue ⊢
    generalize evalExpr st l = vl at hTrue ⊢
    generalize evalExpr st r = vr at hTrue ⊢
    cases vl <;> cases vr <;> dsimp only [] at hTrue ⊢ <;> try cases hTrue
    rename_i va vb
    generalize evalBinOp op va vb = wopt at hTrue ⊢
    cases wopt with
    | none => cases hTrue
    | some w =>
        cases w with
        | unit => cases hTrue
        | i32 _ => cases hTrue
        | bool b => cases b <;> first | rfl | cases hTrue
  case not.blackBox e1 e2 =>
    have hEq := (exprStructEq_eq_true_iff e1 (.blackBox e2)).mp hCon
    subst hEq
    simp only [evalExpr] at hTrue ⊢
    generalize evalExpr st e2 = wopt at hTrue ⊢
    cases wopt with
    | none => cases hTrue
    | some w =>
        cases w with
        | unit => cases hTrue
        | i32 _ => cases hTrue
        | bool b => cases b <;> first | rfl | cases hTrue
  -- Case 3: boolean literal constants `(false, true)` / `(true, false)`:
  case lit.lit v1 v2 =>
    cases v1 with
    | unit => cases hCon
    | i32 _ => cases hCon
    | bool b1 =>
        cases b1 <;> cases v2
        all_goals try cases hCon
        · dsimp only [evalExpr] at hTrue; cases hTrue
        · rename_i b2; cases b2 <;> first | rfl | cases hCon
  -- Case 4: `eq` vs `ne`:
  case bin.bin op1 l1 r1 op2 l2 r2 =>
    cases op1 <;> cases op2 <;> try (dsimp only [exprContradicts] at hCon; cases hCon)
    · cases hl : exprStructEq l1 l2 <;> cases hr : exprStructEq r1 r2
      · simp only [hl] at hCon; cases hCon
      · simp only [hl] at hCon; cases hCon
      · simp only [hl, hr] at hCon; cases hCon
      · have hl' := (exprStructEq_eq_true_iff l1 l2).mp hl
        have hr' := (exprStructEq_eq_true_iff r1 r2).mp hr
        subst hl'; subst hr'
        simp only [evalExpr] at hTrue ⊢
        generalize evalExpr st l1 = vl at hTrue ⊢
        generalize evalExpr st r1 = vr at hTrue ⊢
        cases vl <;> cases vr <;> try cases hTrue
        rename_i va vb
        cases va <;> cases vb <;> simp only [evalBinOp] at hTrue ⊢ <;> try cases hTrue
        case i32.i32 na nb =>
          generalize Nat.beq (norm32 na) (norm32 nb) = eqb at hTrue ⊢
          cases eqb <;> first | rfl | cases hTrue
        case bool.bool ba bb =>
          generalize boolEq ba bb = eqb at hTrue ⊢
          cases eqb <;> first | rfl | cases hTrue
    · cases hl : exprStructEq l1 l2 <;> cases hr : exprStructEq r1 r2
      · simp only [hl] at hCon; cases hCon
      · simp only [hl] at hCon; cases hCon
      · simp only [hl, hr] at hCon; cases hCon
      · have hl' := (exprStructEq_eq_true_iff l1 l2).mp hl
        have hr' := (exprStructEq_eq_true_iff r1 r2).mp hr
        subst hl'; subst hr'
        simp only [evalExpr] at hTrue ⊢
        generalize evalExpr st l1 = vl at hTrue ⊢
        generalize evalExpr st r1 = vr at hTrue ⊢
        cases vl <;> cases vr <;> try cases hTrue
        rename_i va vb
        cases va <;> cases vb <;> simp only [evalBinOp] at hTrue ⊢ <;> try cases hTrue
        case i32.i32 na nb =>
          generalize Nat.beq (norm32 na) (norm32 nb) = eqb at hTrue ⊢
          cases eqb <;> first | rfl | cases hTrue
        case bool.bool ba bb =>
          generalize boolEq ba bb = eqb at hTrue ⊢
          cases eqb <;> first | rfl | cases hTrue

/-- Dead-branch pruning optimization rule: rewrites `assume P; branchOn G dead live`
    or `checkedAssume P; branchOn G dead live` to preserve `P` and execute `live`
    directly whenever `exprContradicts P G = true`. -/
noncomputable def applyPruneHead : List Inst → List Inst
  | .assume p :: .branchOn g dead live :: rest =>
      if exprContradicts p g then
        .assume p :: (live ++ rest)
      else
        .assume p :: .branchOn g dead live :: rest
  | .checkedAssume p :: .branchOn g dead live :: rest =>
      if exprContradicts p g then
        .checkedAssume p :: (live ++ rest)
      else
        .checkedAssume p :: .branchOn g dead live :: rest
  | prog => prog

theorem evalBlock_cons_checkedAssume_true
    (ubMode : UbCheckMode) (onCall : FnId → Val → Outcome)
    (st : Store) (p : Expr) (rest : List Inst)
    (hp : evalExpr st p = some (.bool true)) :
    evalBlock ubMode true onCall st (.checkedAssume p :: rest) =
    evalBlock ubMode true onCall st rest := by
  simp only [evalBlock, evalOne, hp]
  cases ubMode <;> rfl

theorem evalBlock_cons_assume_true
    (ubMode : UbCheckMode) (onCall : FnId → Val → Outcome)
    (st : Store) (p : Expr) (rest : List Inst)
    (hp : evalExpr st p = some (.bool true)) :
    evalBlock ubMode true onCall st (.assume p :: rest) =
    evalBlock ubMode true onCall st rest := by
  simp only [evalBlock, evalOne, hp]
  rfl

theorem evalBlock_cons_branchOn_false
    (ubMode : UbCheckMode) (onCall : FnId → Val → Outcome)
    (st : Store) (g : Expr) (dead live rest : List Inst)
    (hg : evalExpr st g = some (.bool false)) :
    evalBlock ubMode true onCall st (.branchOn g dead live :: rest) =
    evalBlock ubMode true onCall st (live ++ rest) := by
  simp only [evalBlock, evalOne, hg]
  symm
  exact evalBlock_append ubMode true onCall live rest st

/-- Local Soundness of `applyPruneHead` for BOTH `UbCheckMode`s when `emitAssume = true`:
    `assume P` (or `checkedAssume P`) forces `evalExpr st P = some (.bool true)`,
    under which `branchOn G dead live` always takes `live`. -/
theorem assume_dead_branch_pruning_sound
    (ubMode : UbCheckMode) (onCall : FnId → Val → Outcome)
    (st : Store) (prog : List Inst) :
    evalBlock ubMode true onCall st (applyPruneHead prog) =
    evalBlock ubMode true onCall st prog := by
  cases prog with
  | nil => rfl
  | cons a rest =>
      cases a <;> try rfl
      · rename_i p
        cases rest with
        | nil => rfl
        | cons b tail =>
            cases b <;> try rfl
            rename_i g dead live
            dsimp only [applyPruneHead]
            have hIteF : ∀ {α : Type} (x y : α), (if (false = true) then x else y) = y := fun _ _ => rfl
            have hIteT : ∀ {α : Type} (x y : α), (if (true = true) then x else y) = x := fun _ _ => rfl
            cases hc : exprContradicts p g
            · rw [hIteF]
            · rw [hIteT]
              cases hv : evalExpr st p with
              | none => simp only [evalBlock, evalOne, hv]; cases ubMode <;> rfl
              | some w =>
                  cases w with
                  | unit => simp only [evalBlock, evalOne, hv]; cases ubMode <;> rfl
                  | i32 _ => simp only [evalBlock, evalOne, hv]; cases ubMode <;> rfl
                  | bool pb =>
                      cases pb with
                      | false => simp only [evalBlock, evalOne, hv]; cases ubMode <;> rfl
                      | true =>
                          have hFalse := exprContradicts_sound p g st hc hv
                          rw [evalBlock_cons_checkedAssume_true ubMode onCall st p (live ++ tail) hv]
                          rw [evalBlock_cons_checkedAssume_true ubMode onCall st p (.branchOn g dead live :: tail) hv]
                          rw [evalBlock_cons_branchOn_false ubMode onCall st g dead live tail hFalse]
      · rename_i p
        cases rest with
        | nil => rfl
        | cons b tail =>
            cases b <;> try rfl
            rename_i g dead live
            dsimp only [applyPruneHead]
            have hIteF : ∀ {α : Type} (x y : α), (if (false = true) then x else y) = y := fun _ _ => rfl
            have hIteT : ∀ {α : Type} (x y : α), (if (true = true) then x else y) = x := fun _ _ => rfl
            cases hc : exprContradicts p g
            · rw [hIteF]
            · rw [hIteT]
              cases hv : evalExpr st p with
              | none => simp only [evalBlock, evalOne, hv, ite_true]
              | some w =>
                  cases w with
                  | unit => simp only [evalBlock, evalOne, hv, ite_true]
                  | i32 _ => simp only [evalBlock, evalOne, hv, ite_true]
                  | bool pb =>
                      cases pb with
                      | false => simp only [evalBlock, evalOne, hv]; cases ubMode <;> rfl
                      | true =>
                          have hFalse := exprContradicts_sound p g st hc hv
                          rw [evalBlock_cons_assume_true ubMode onCall st p (live ++ tail) hv]
                          rw [evalBlock_cons_assume_true ubMode onCall st p (.branchOn g dead live :: tail) hv]
                          rw [evalBlock_cons_branchOn_false ubMode onCall st g dead live tail hFalse]

theorem assume_dead_branch_pruning_prog_sound
    (ubMode : UbCheckMode) (fns : FnTable) (fuel : Nat) (st : Store) (prog : List Inst) :
    evalProg ubMode true fns fuel st (applyPruneHead prog) =
    evalProg ubMode true fns fuel st prog := by
  unfold evalProg
  rw [assume_dead_branch_pruning_sound ubMode (evalFnCall ubMode true fns fuel) st prog]

/-- Sharpness Counterexample 1 (Dropping contradiction breaks soundness):
    If `exprContradicts P G = false` (e.g., `assume(r0 != 0)` followed by
    `if r0 == 1 then return 999 else return r0 + 1`), blindly pruning `dead`
    changes the result at `r0 = 1` from `ok (i32 999)` to `ok (i32 2)`! -/
theorem assume_pruning_without_contradiction_unsound
    (fns : FnTable) (fuel : Nat) :
    let st := updateStore emptyStore .r0 (.i32 1)
    let orig : List Inst :=
      [ .assume (.bin .ne (.var .r0) (.lit (.i32 0)))
      , .branchOn (.bin .eq (.var .r0) (.lit (.i32 1)))
          [.ret (.lit (.i32 999))]
          [.ret (.bin .add (.var .r0) (.lit (.i32 1)))]
      ]
    let pruned : List Inst :=
      [ .assume (.bin .ne (.var .r0) (.lit (.i32 0)))
      , .ret (.bin .add (.var .r0) (.lit (.i32 1)))
      ]
    evalProg .ubOnFalse true fns fuel st orig = .ok (.i32 999) ∧
    evalProg .ubOnFalse true fns fuel st pruned = .ok (.i32 2) := by
  exact ⟨rfl, rfl⟩

/-- Sharpness Counterexample 2 (`-O0` suppression breaks unguarded `assume(P)`):
    When `emitAssume = false` (`OptLevel::No`), `assume(false)` becomes a no-op
    so pruning away `dead` at `-O0` without checking contradiction executes `live`
    whereas an explicit branch executes `dead` if `G` holds. -/
theorem o0_assume_suppression_sharpness (fns : FnTable) (fuel : Nat) :
    let st := emptyStore
    let pAssume := Expr.lit (.bool false)
    let prog : List Inst := [.assume pAssume, .ret (.lit (.i32 7))]
    evalProg .ubOnFalse false fns fuel st prog = .ok (.i32 7) ∧
    evalProg .ubOnFalse true fns fuel st prog = .ub := by
  exact ⟨rfl, rfl⟩

/-- Modular `i32` Return-Range Theorem modeling LLVM `CorrelatedValuePropagationPass`'s
    `define noundef range(i32 2, 1) i32 @prune_unreachable_branch(i32 %x)`:
    When `%x != 0` modulo `2^32`, `norm32 (x + 1)` can never equal `1`!
    Proof uses pure constructive `Nat` modular arithmetic without arithmetic tactics. -/
theorem norm32_ne_zero_implies_add_one_ne_one (x : Nat)
    (hx : norm32 x ≠ 0) : add32 x 1 ≠ 1 := by
  intro hEq
  dsimp only [add32, norm32] at hEq ⊢
  rw [Nat.add_mod x 1 i32Modulus] at hEq
  have hMod1 : 1 % i32Modulus = 1 := rfl
  rw [hMod1] at hEq
  have hxLt : x % i32Modulus < i32Modulus := Nat.mod_lt x i32Modulus_pos
  have hSumLe : x % i32Modulus + 1 ≤ i32Modulus := hxLt
  cases Nat.eq_or_lt_of_le hSumLe with
  | inl hWrap =>
      rw [hWrap] at hEq
      have hZero : i32Modulus % i32Modulus = 0 := Nat.mod_self i32Modulus
      rw [hZero] at hEq
      cases hEq
  | inr hNoWrap =>
      rw [Nat.mod_eq_of_lt hNoWrap] at hEq
      have hPred := Nat.succ.inj hEq
      dsimp only [norm32] at hx
      exact hx hPred

/-- Operational Corollary matching `@prune_unreachable_branch`:
    For ANY `32`-bit register value in `r0` (`norm32 x < 2^32`), executing
    `prune_unreachable_branch` never returns `ok (i32 1)` under `ubOnFalse` (`-O1 or -O2`). -/
theorem prune_unreachable_branch_range_excludes_one
    (fns : FnTable) (fuel : Nat) (x : Nat) :
    let st := updateStore emptyStore .r0 (.i32 x)
    let fnBody : List Inst :=
      [ .branchOn (.bin .eq (.var .r0) (.lit (.i32 0)))
          [.unreachable]
          [.ret (.bin .add (.var .r0) (.lit (.i32 1)))]
      ]
    evalProg .ubOnFalse true fns fuel st fnBody ≠ .ok (.i32 1) := by
  intro st fnBody hOk
  dsimp only [st, fnBody] at hOk
  simp only [evalProg, blockToOutcome, evalBlock, evalOne, evalExpr, evalBinOp] at hOk
  rw [updateStore_same] at hOk
  dsimp only [norm32] at hOk
  have hZero : (0 % i32Modulus) = 0 := rfl
  cases hZeroEq : Nat.beq (x % i32Modulus) (0 % i32Modulus) with
  | true =>
      rw [hZeroEq] at hOk
      cases hOk
  | false =>
      rw [hZeroEq] at hOk
      injection hOk with hVal
      injection hVal with hEq
      have hxNeZero : norm32 x ≠ 0 := by
        intro hZ
        dsimp only [norm32] at hZ
        rw [hZ, hZero] at hZeroEq
        have hRefl : Nat.beq 0 0 = true := rfl
        rw [hRefl] at hZeroEq
        cases hZeroEq
      have hAddNe := norm32_ne_zero_implies_add_one_ne_one x hxNeZero
      exact hAddNe hEq

-- ============================================================================
-- Section 7: Theorem Family 3 — `black_box` Whole-Program Identity & Barrier
-- ============================================================================

/-- Replaces all `.blackBox` expressions and `.blackBoxAssign` statements with
    transparent expressions/assignments to prove observational equivalence. -/
noncomputable def stripBlackBoxExpr : Expr → Expr
  | .lit v => .lit v
  | .var r => .var r
  | .not e => .not (stripBlackBoxExpr e)
  | .bin op l r => .bin op (stripBlackBoxExpr l) (stripBlackBoxExpr r)
  | .blackBox e => stripBlackBoxExpr e

theorem evalExpr_stripBlackBox_eq (st : Store) (e : Expr) :
    evalExpr st (stripBlackBoxExpr e) = evalExpr st e := by
  induction e with
  | lit _ => rfl
  | var _ => rfl
  | not _ ih => dsimp only [stripBlackBoxExpr, evalExpr]; rw [ih]
  | bin op _ _ ihl ihr => dsimp only [stripBlackBoxExpr, evalExpr]; rw [ihl, ihr]
  | blackBox _ ih => dsimp only [stripBlackBoxExpr, evalExpr]; exact ih

mutual
  noncomputable def stripBlackBoxInst : Inst → Inst
    | .assign dst rhs => .assign dst (stripBlackBoxExpr rhs)
    | .blackBoxAssign dst rhs => .assign dst (stripBlackBoxExpr rhs)
    | .checkedAssume cond => .checkedAssume (stripBlackBoxExpr cond)
    | .assume cond => .assume (stripBlackBoxExpr cond)
    | .checkedUnreachable pUb => .checkedUnreachable pUb
    | .unreachable => .unreachable
    | .branchOn cond t e =>
        .branchOn (stripBlackBoxExpr cond) (stripBlackBoxBlock t) (stripBlackBoxBlock e)
    | .callFn dst callee arg => .callFn dst callee (stripBlackBoxExpr arg)
    | .ret rhs => .ret (stripBlackBoxExpr rhs)

  noncomputable def stripBlackBoxBlock : List Inst → List Inst
    | [] => []
    | i :: rest => stripBlackBoxInst i :: stripBlackBoxBlock rest
end

noncomputable def stripBlackBoxFnTable (fns : FnTable) : FnTable :=
  fun fid =>
    let d := fns fid
    { param := d.param, attrs := d.attrs, body := stripBlackBoxBlock d.body }

theorem stripBlackBox_preserves_block
    (ubMode : UbCheckMode) (emitAssume : Bool)
    (onCallA onCallB : FnId → Val → Outcome)
    (hCall : ∀ f a, onCallA f a = onCallB f a) :
    ∀ (inst : Inst) (st : Store),
      evalOne ubMode emitAssume onCallA st (stripBlackBoxInst inst) =
      evalOne ubMode emitAssume onCallB st inst := by
  intro inst st
  exact
    @Inst.rec
      (fun i => ∀ s : Store,
        evalOne ubMode emitAssume onCallA s (stripBlackBoxInst i) =
        evalOne ubMode emitAssume onCallB s i)
      (fun l => ∀ s : Store,
        evalBlock ubMode emitAssume onCallA s (stripBlackBoxBlock l) =
        evalBlock ubMode emitAssume onCallB s l)
      (fun dst rhs s => by
        simp only [stripBlackBoxInst, evalOne, evalExpr_stripBlackBox_eq])
      (fun dst rhs s => by
        simp only [stripBlackBoxInst, evalOne, evalExpr_stripBlackBox_eq])
      (fun cond s => by
        simp only [stripBlackBoxInst, evalOne, evalExpr_stripBlackBox_eq])
      (fun cond s => by
        simp only [stripBlackBoxInst, evalOne, evalExpr_stripBlackBox_eq])
      (fun _ _ => rfl)
      (fun _ => rfl)
      (fun cond t e iht ihe s => by
        simp only [stripBlackBoxInst, evalOne, evalExpr_stripBlackBox_eq]
        cases evalExpr s cond with
        | none => rfl
        | some v =>
            cases v with
            | unit => rfl
            | i32 _ => rfl
            | bool b => cases b <;> first | exact iht s | exact ihe s)
      (fun dst callee arg s => by
        simp only [stripBlackBoxInst, evalOne, evalExpr_stripBlackBox_eq]
        cases evalExpr s arg with
        | none => rfl
        | some argv => dsimp only []; rw [hCall callee argv])
      (fun rhs s => by
        simp only [stripBlackBoxInst, evalOne, evalExpr_stripBlackBox_eq])
      (fun _ => rfl)
      (fun i rest ihi ihrest s => by
        simp only [stripBlackBoxBlock, evalBlock]
        rw [ihi s]
        cases evalOne ubMode emitAssume onCallB s i <;> first | rfl | exact ihrest _)
      inst st

theorem stripBlackBoxBlock_preserves
    (ubMode : UbCheckMode) (emitAssume : Bool)
    (onCallA onCallB : FnId → Val → Outcome)
    (hCall : ∀ f a, onCallA f a = onCallB f a)
    (prog : List Inst) (st : Store) :
    evalBlock ubMode emitAssume onCallA st (stripBlackBoxBlock prog) =
    evalBlock ubMode emitAssume onCallB st prog := by
  induction prog generalizing st with
  | nil => rfl
  | cons i rest ih =>
      simp only [stripBlackBoxBlock, evalBlock]
      rw [stripBlackBox_preserves_block ubMode emitAssume onCallA onCallB hCall i st]
      cases evalOne ubMode emitAssume onCallB st i <;> first | rfl | exact ih _

/-- Full-Program `black_box` Observational Identity Theorem (`evalProg`):
    Eliminating every `black_box` barrier (while preserving evaluation semantics)
    produces the EXACT same `Outcome` across ALL modes (`abortOnFalse` and
    `ubOnFalse`), both `emitAssume` settings, and arbitrary call trees! -/
theorem blackBox_observational_identity
    (ubMode : UbCheckMode) (emitAssume : Bool) (fns : FnTable)
    (fuel : Nat) (st : Store) (prog : List Inst) :
    evalProg ubMode emitAssume (stripBlackBoxFnTable fns) fuel st (stripBlackBoxBlock prog) =
    evalProg ubMode emitAssume fns fuel st prog := by
  have hFn : ∀ f a,
      evalFnCall ubMode emitAssume (stripBlackBoxFnTable fns) fuel f a =
      evalFnCall ubMode emitAssume fns fuel f a := by
    induction fuel with
    | zero => intro _ _; rfl
    | succ k ihk =>
        intro f a
        simp only [evalFnCall, stripBlackBoxFnTable]
        rw [stripBlackBoxBlock_preserves ubMode emitAssume
              (evalFnCall ubMode emitAssume (stripBlackBoxFnTable fns) k)
              (evalFnCall ubMode emitAssume fns k)
              ihk (fns f).body (updateStore emptyStore (fns f).param a)]
  simp only [evalProg]
  rw [stripBlackBoxBlock_preserves ubMode emitAssume
        (evalFnCall ubMode emitAssume (stripBlackBoxFnTable fns) fuel)
        (evalFnCall ubMode emitAssume fns fuel)
        hFn prog st]

-- Constant-folding pass over whole programs (`constFoldBlock`) that respects
-- `black_box` compiler barriers (`constFoldExpr` never lowers across `.blackBox`).
mutual
  noncomputable def constFoldInst : Inst → Inst
    | .assign dst rhs => .assign dst (constFoldExpr rhs)
    | .blackBoxAssign dst rhs => .blackBoxAssign dst (constFoldExpr rhs)
    | .checkedAssume cond => .checkedAssume (constFoldExpr cond)
    | .assume cond => .assume (constFoldExpr cond)
    | .checkedUnreachable pUb => .checkedUnreachable pUb
    | .unreachable => .unreachable
    | .branchOn cond t e =>
        .branchOn (constFoldExpr cond) (constFoldBlock t) (constFoldBlock e)
    | .callFn dst callee arg => .callFn dst callee (constFoldExpr arg)
    | .ret rhs => .ret (constFoldExpr rhs)

  noncomputable def constFoldBlock : List Inst → List Inst
    | [] => []
    | i :: rest => constFoldInst i :: constFoldBlock rest
end

theorem constFoldInst_sound
    (ubMode : UbCheckMode) (emitAssume : Bool)
    (onCall : FnId → Val → Outcome) (inst : Inst) (st : Store) :
    evalOne ubMode emitAssume onCall st (constFoldInst inst) =
    evalOne ubMode emitAssume onCall st inst := by
  exact
    @Inst.rec
      (fun i => ∀ s : Store,
        evalOne ubMode emitAssume onCall s (constFoldInst i) =
        evalOne ubMode emitAssume onCall s i)
      (fun l => ∀ s : Store,
        evalBlock ubMode emitAssume onCall s (constFoldBlock l) =
        evalBlock ubMode emitAssume onCall s l)
      (fun dst rhs s => by simp only [constFoldInst, evalOne, constFoldExpr_sound])
      (fun dst rhs s => by simp only [constFoldInst, evalOne, constFoldExpr_sound])
      (fun cond s => by simp only [constFoldInst, evalOne, constFoldExpr_sound])
      (fun cond s => by simp only [constFoldInst, evalOne, constFoldExpr_sound])
      (fun _ _ => rfl)
      (fun _ => rfl)
      (fun cond t e iht ihe s => by
        simp only [constFoldInst, evalOne, constFoldExpr_sound]
        cases evalExpr s cond with
        | none => rfl
        | some v =>
            cases v with
            | unit => rfl
            | i32 _ => rfl
            | bool b => cases b <;> first | exact iht s | exact ihe s)
      (fun dst callee arg s => by
        simp only [constFoldInst, evalOne, constFoldExpr_sound])
      (fun rhs s => by simp only [constFoldInst, evalOne, constFoldExpr_sound])
      (fun _ => rfl)
      (fun i rest ihi ihrest s => by
        simp only [constFoldBlock, evalBlock]
        rw [ihi s]
        cases evalOne ubMode emitAssume onCall s i <;> first | rfl | exact ihrest _)
      inst st

theorem constFoldBlock_sound
    (ubMode : UbCheckMode) (emitAssume : Bool)
    (onCall : FnId → Val → Outcome) (prog : List Inst) (st : Store) :
    evalBlock ubMode emitAssume onCall st (constFoldBlock prog) =
    evalBlock ubMode emitAssume onCall st prog := by
  induction prog generalizing st with
  | nil => rfl
  | cons i rest ih =>
      simp only [constFoldBlock, evalBlock]
      rw [constFoldInst_sound ubMode emitAssume onCall i st]
      cases evalOne ubMode emitAssume onCall st i <;> first | rfl | exact ih _

-- Witness statement-level proof matching live `black_box_no_fold` vs `plain_fold`:
theorem blackBox_statement_blocks_fold_while_preserving_outcome
    (ubMode : UbCheckMode) (emitAssume : Bool) (fns : FnTable) (fuel : Nat) (st : Store) :
    let plainProg : List Inst := [.ret plainAddTwoThree]
    let boxedProg : List Inst := [.ret boxedAddTwoThree]
    constFoldBlock plainProg = [.ret (.lit (.i32 5))] ∧
    constFoldBlock boxedProg = boxedProg ∧
    evalProg ubMode emitAssume fns fuel st plainProg = .ok (.i32 5) ∧
    evalProg ubMode emitAssume fns fuel st boxedProg = .ok (.i32 5) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- Section 8: Theorem Family 4 — Hygienic Inlining & `#[inline]` / `#[cold]` Invariance
-- ============================================================================

noncomputable def blockHasNoCalls : List Inst → Bool
  | [] => true
  | inst :: rest =>
      let instOk :=
        match inst with
        | .callFn _ _ _ => false
        | .branchOn _ t e => Bool.and (blockHasNoCalls t) (blockHasNoCalls e)
        | _ => true
      Bool.and instOk (blockHasNoCalls rest)

noncomputable def blockCallerSafe (param : Reg) : List Inst → Bool
  | [] => true
  | inst :: rest =>
      let instOk :=
        match inst with
        | .assign dst rhs =>
            Bool.and (regEq dst .calleeLocal)
              (exprAllRegs (fun r => Bool.or (regEq r param) (regEq r .calleeLocal)) rhs)
        | .blackBoxAssign dst rhs =>
            Bool.and (regEq dst .calleeLocal)
              (exprAllRegs (fun r => Bool.or (regEq r param) (regEq r .calleeLocal)) rhs)
        | .ret rhs =>
            exprAllRegs (fun r => Bool.or (regEq r param) (regEq r .calleeLocal)) rhs
        | _ => false
      Bool.and instOk (blockCallerSafe param rest)

/-- Well-formedness check for deterministic straight-line leaf callees cleanly
    supporting hygienic direct parameter substitution when inlining at caller. -/
noncomputable def inlineableLeafBody (param : Reg) (body : List Inst) : Bool :=
  Bool.and (blockHasNoCalls body) (blockCallerSafe param body)

/-- Hygienically converts a callee's body to write its return value into `dst`
    using `.calleeParam` for the passed argument and `.calleeLocal` for scratch. -/
noncomputable def instantiateInlineBody
    (dst param : Reg) : List Inst → List Inst
  | [] => []
  | .assign d rhs :: rest =>
      .assign d (renameExprReg param .calleeParam rhs) ::
        instantiateInlineBody dst param rest
  | .blackBoxAssign d rhs :: rest =>
      .blackBoxAssign d (renameExprReg param .calleeParam rhs) ::
        instantiateInlineBody dst param rest
  | .ret rhs :: _ =>
      [.assign dst (renameExprReg param .calleeParam rhs)]
  | _ :: rest => instantiateInlineBody dst param rest

noncomputable def inlineCallOnce
    (cfg : CompilerFlags) (fns : FnTable)
    (dst : Reg) (callee : FnId) (arg : Expr) (rest : List Inst) : List Inst :=
  let defn := fns callee
  let llAttr := lowerInlineToLlvm cfg defn.attrs
  if Bool.and
      (llvmShouldInlineCall cfg.opt llAttr defn.attrs.cold)
      (Bool.and (regEq defn.param .calleeParam)
                (inlineableLeafBody defn.param defn.body)) then
    .assign .calleeParam arg :: (instantiateInlineBody dst defn.param defn.body ++ rest)
  else
    .callFn dst callee arg :: rest

/-- Register-isolation invariant for straight-line caller code:
    caller expressions never read `.calleeParam` or `.calleeLocal`, and
    the inlined destination `dst` is caller-visible (`isCallerVisibleReg dst = true`). -/
theorem updateStore_callerVisible_agrees (dst : Reg) (s1 s2 : Store) (v : Val)
    (_hVis : isCallerVisibleReg dst = true)
    (hAgree : storeAgreeOn isCallerVisibleReg s1 s2) :
    storeAgreeOn isCallerVisibleReg (updateStore s1 dst v) (updateStore s2 dst v) :=
  storeAgreeOn_update_both isCallerVisibleReg s1 s2 dst v hAgree

/-- Changing function attributes `attrs` inside a `FnTable` (such as adding/removing
    `#[cold]`, switching `#[inline(always)]` ↔ `#[inline(never)]` ↔ `#[inline]`, or
    setting `#[optimize(none)]`) NEVER alters dynamic `evalProg` behavior! -/
noncomputable def retagFnAttrs (fns : FnTable) (target : FnId) (newAttrs : FnAttrs) : FnTable :=
  fun fid =>
    let d := fns fid
    if fnIdEq fid target then
      { param := d.param, attrs := newAttrs, body := d.body }
    else d

theorem evalFnCall_attr_invariant
    (ubMode : UbCheckMode) (emitAssume : Bool) (fns : FnTable)
    (target : FnId) (newAttrs : FnAttrs) (fuel : Nat) (fid : FnId) (argv : Val) :
    evalFnCall ubMode emitAssume (retagFnAttrs fns target newAttrs) fuel fid argv =
    evalFnCall ubMode emitAssume fns fuel fid argv := by
  induction fuel generalizing fid argv with
  | zero => rfl
  | succ k ih =>
      dsimp only [evalFnCall]
      have hOr : evalFnCall ubMode emitAssume (retagFnAttrs fns target newAttrs) k =
                 evalFnCall ubMode emitAssume fns k := by
        funext f' a'
        exact ih f' a'
      rw [hOr]
      dsimp only [retagFnAttrs]
      cases fnIdEq fid target <;> rfl

/-- Theorem Family 4a (`#[inline]` / `#[inline(always)]` / `#[inline(never)]` /
    `#[cold]` / `#[optimize(none)]` Attribute Invariance Theorem):
    Rewriting any function's attributes in `FnTable` preserves `evalProg`
    with IDENTICAL `.ok v`, `.abort`, `.ub`, or `.fault` outcomes. -/
theorem fnAttrs_observational_equivalence_invariance
    (ubMode : UbCheckMode) (emitAssume : Bool) (fns : FnTable)
    (target : FnId) (newAttrs : FnAttrs) (fuel : Nat) (st : Store) (prog : List Inst) :
    evalProg ubMode emitAssume (retagFnAttrs fns target newAttrs) fuel st prog =
    evalProg ubMode emitAssume fns fuel st prog := by
  unfold evalProg
  have hOr : evalFnCall ubMode emitAssume (retagFnAttrs fns target newAttrs) fuel =
             evalFnCall ubMode emitAssume fns fuel := by
    funext f' a'
    exact evalFnCall_attr_invariant ubMode emitAssume fns target newAttrs fuel f' a'
  rw [hOr]

-- Register visibility predicates for straight-line caller code:
-- caller expressions never inspect `.calleeParam` or `.calleeLocal`.
mutual
  noncomputable def instCallerVisiblePred : Inst → Bool
    | .assign d rhs => Bool.and (isCallerVisibleReg d) (exprAllRegs isCallerVisibleReg rhs)
    | .blackBoxAssign d rhs =>
        Bool.and (isCallerVisibleReg d) (exprAllRegs isCallerVisibleReg rhs)
    | .checkedAssume c => exprAllRegs isCallerVisibleReg c
    | .assume c => exprAllRegs isCallerVisibleReg c
    | .checkedUnreachable _ => true
    | .unreachable => true
    | .branchOn c t e =>
        Bool.and (exprAllRegs isCallerVisibleReg c)
          (Bool.and (blockCallerVisiblePred t) (blockCallerVisiblePred e))
    | .callFn d _ a => Bool.and (isCallerVisibleReg d) (exprAllRegs isCallerVisibleReg a)
    | .ret rhs => exprAllRegs isCallerVisibleReg rhs

  noncomputable def blockCallerVisiblePred : List Inst → Bool
    | [] => true
    | inst :: rest => Bool.and (instCallerVisiblePred inst) (blockCallerVisiblePred rest)
end

theorem evalBlock_storeAgreeOn_callerVisible
    (ubMode : UbCheckMode) (emitAssume : Bool) (onCall : FnId → Val → Outcome)
    (prog : List Inst) (s1 s2 : Store)
    (hVisible : blockCallerVisiblePred prog = true)
    (hAgree : storeAgreeOn isCallerVisibleReg s1 s2) :
    blockToOutcome (evalBlock ubMode emitAssume onCall s1 prog) =
    blockToOutcome (evalBlock ubMode emitAssume onCall s2 prog) := by
  suffices hFull :
      ∀ (p : List Inst) (a b : Store),
        blockCallerVisiblePred p = true →
        storeAgreeOn isCallerVisibleReg a b →
        match evalBlock ubMode emitAssume onCall a p,
              evalBlock ubMode emitAssume onCall b p with
        | .next a', .next b' => storeAgreeOn isCallerVisibleReg a' b'
        | .ret v1, .ret v2 => v1 = v2
        | .abort, .abort => True
        | .ub, .ub => True
        | .fault, .fault => True
        | _, _ => False by
    have hm := hFull prog s1 s2 hVisible hAgree
    cases h1 : evalBlock ubMode emitAssume onCall s1 prog <;>
      cases h2 : evalBlock ubMode emitAssume onCall s2 prog <;>
      rw [h1, h2] at hm
    all_goals first | rfl | exact absurd hm False.elim | (subst hm; rfl)
  intro p a b hVis hAg
  exact
    (@Inst.rec_1
      (fun i =>
        ∀ (x y : Store),
          instCallerVisiblePred i = true →
          storeAgreeOn isCallerVisibleReg x y →
          match evalOne ubMode emitAssume onCall x i,
                evalOne ubMode emitAssume onCall y i with
          | .next x', .next y' => storeAgreeOn isCallerVisibleReg x' y'
          | .ret v1, .ret v2 => v1 = v2
          | .abort, .abort => True
          | .ub, .ub => True
          | .fault, .fault => True
          | _, _ => False)
      (fun l =>
        ∀ (x y : Store),
          blockCallerVisiblePred l = true →
          storeAgreeOn isCallerVisibleReg x y →
          match evalBlock ubMode emitAssume onCall x l,
                evalBlock ubMode emitAssume onCall y l with
          | .next x', .next y' => storeAgreeOn isCallerVisibleReg x' y'
          | .ret v1, .ret v2 => v1 = v2
          | .abort, .abort => True
          | .ub, .ub => True
          | .fault, .fault => True
          | _, _ => False)
      (fun dst rhs x y hi hag => by
        simp only [instCallerVisiblePred] at hi
        cases hd : isCallerVisibleReg dst <;> cases hr : exprAllRegs isCallerVisibleReg rhs <;>
          try (simp only [hd, hr] at hi; cases hi)
        simp only [evalOne]
        rw [evalExpr_storeAgreeOn isCallerVisibleReg rhs x y hag hr]
        cases evalExpr y rhs with
        | none => trivial
        | some v => exact storeAgreeOn_update_both isCallerVisibleReg x y dst v hag)
      (fun dst rhs x y hi hag => by
        simp only [instCallerVisiblePred] at hi
        cases hd : isCallerVisibleReg dst <;> cases hr : exprAllRegs isCallerVisibleReg rhs <;>
          try (simp only [hd, hr] at hi; cases hi)
        simp only [evalOne]
        rw [evalExpr_storeAgreeOn isCallerVisibleReg rhs x y hag hr]
        cases evalExpr y rhs with
        | none => trivial
        | some v => exact storeAgreeOn_update_both isCallerVisibleReg x y dst v hag)
      (fun cond x y hi hag => by
        simp only [instCallerVisiblePred] at hi
        simp only [evalOne]
        rw [evalExpr_storeAgreeOn isCallerVisibleReg cond x y hag hi]
        cases ubMode
        · cases evalExpr y cond with
          | none => trivial
          | some v =>
              cases v with
              | unit => trivial
              | i32 _ => trivial
              | bool b => cases b <;> trivial
        · cases emitAssume
          · exact hag
          · cases evalExpr y cond with
            | none => trivial
            | some v =>
                cases v with
                | unit => trivial
                | i32 _ => trivial
                | bool b => cases b <;> first | trivial | exact hag)
      (fun cond x y hi hag => by
        simp only [instCallerVisiblePred] at hi
        simp only [evalOne]
        rw [evalExpr_storeAgreeOn isCallerVisibleReg cond x y hag hi]
        cases emitAssume
        · exact hag
        · cases evalExpr y cond with
          | none => trivial
          | some v =>
              cases v with
              | unit => dsimp only []; trivial
              | i32 _ => dsimp only []; trivial
              | bool b =>
                  cases b with
                  | false => cases ubMode <;> trivial
                  | true => dsimp only []; exact hag)
      (fun pUb _ _ _ _ => by
        simp only [evalOne]
        cases pUb <;> cases ubMode <;> cases emitAssume <;> trivial)
      (fun _ _ _ _ => by
        simp only [evalOne]; cases ubMode <;> trivial)
      (fun cond t e iht ihe x y hi hag => by
        simp only [instCallerVisiblePred] at hi
        cases hc : exprAllRegs isCallerVisibleReg cond <;>
          cases ht : blockCallerVisiblePred t <;>
          cases he : blockCallerVisiblePred e <;>
          try (simp only [hc, ht, he] at hi; cases hi)
        simp only [evalOne]
        rw [evalExpr_storeAgreeOn isCallerVisibleReg cond x y hag hc]
        cases evalExpr y cond with
        | none => trivial
        | some v =>
            cases v with
            | unit => trivial
            | i32 _ => trivial
            | bool b =>
                cases b with
                | false => exact ihe x y he hag
                | true => exact iht x y ht hag)
      (fun dst callee arg x y hi hag => by
        simp only [instCallerVisiblePred] at hi
        cases hd : isCallerVisibleReg dst <;> cases ha : exprAllRegs isCallerVisibleReg arg <;>
          try (simp only [hd, ha] at hi; cases hi)
        simp only [evalOne]
        rw [evalExpr_storeAgreeOn isCallerVisibleReg arg x y hag ha]
        cases evalExpr y arg with
        | none => trivial
        | some argv =>
            dsimp only []
            cases onCall callee argv
            · exact storeAgreeOn_update_both isCallerVisibleReg x y dst _ hag
            · trivial
            · trivial
            · trivial)
      (fun rhs x y hi hag => by
        simp only [instCallerVisiblePred] at hi
        simp only [evalOne]
        rw [evalExpr_storeAgreeOn isCallerVisibleReg rhs x y hag hi]
        cases evalExpr y rhs <;> dsimp only [] <;> trivial)
      (fun x y _ hag => hag)
      (fun i rest ihi ihrest x y hl hag => by
        simp only [blockCallerVisiblePred] at hl
        cases hi : instCallerVisiblePred i <;> cases hrest : blockCallerVisiblePred rest
        · simp only [hi] at hl; cases hl
        · simp only [hi] at hl; cases hl
        · simp only [hi, hrest] at hl; cases hl
        · have hStep := ihi x y hi hag
          simp only [evalBlock]
          cases hx : evalOne ubMode emitAssume onCall x i <;>
            cases hy : evalOne ubMode emitAssume onCall y i <;>
            rw [hx, hy] at hStep <;>
            dsimp only [] at hStep ⊢
          all_goals try exact False.elim hStep
          all_goals try trivial
          · exact ihrest _ _ hrest hStep)
      p a b hVis hAg)

-- Concrete Cross-Attribute Equivalence Witness matching live cross-crate probes:
--   `up_inline_always(x) = x + 22`, `up_inline_hint(x) = x + 11`,
--   `up_inline_never(x) = x + 33`, `up_cold_only(x) = x + 44`
-- Regardless of whether compiled at `-O0` (`AlwaysInlinerPass` inlines only `always`),
-- or `-O2` (inlines `hint`/`cold`/leaf, leaves `never` as `call`), or annotated with
-- `#[inline(always)]` / `#[inline(never)]` / `#[cold]`, the returned `i32` is invariant!
noncomputable def attrAddCallee (offset : Nat) (attrs : FnAttrs) : FnDef :=
  { param := .calleeParam
  , attrs := attrs
  , body := [.ret (.bin .add (.var .calleeParam) (.lit (.i32 offset)))]
  }

theorem instantiateInline_straightLine_add_equiv
    (ubMode : UbCheckMode) (emitAssume : Bool) (offset : Nat)
    (a1 a2 : FnAttrs) (fns : FnTable)
    (h1 : fns .helperAlways = attrAddCallee offset a1)
    (h2 : fns .helperNever = attrAddCallee offset a2)
    (st : Store) (xVal : Nat) (hx : evalExpr st (.var .r0) = some (.i32 xVal)) :
    let callerA : List Inst := [.callFn .r1 .helperAlways (.var .r0), .ret (.var .r1)]
    let callerN : List Inst := [.callFn .r1 .helperNever (.var .r0), .ret (.var .r1)]
    let callerInlined : List Inst :=
      [ .assign .calleeParam (.var .r0)
      , .assign .r1 (.bin .add (.var .calleeParam) (.lit (.i32 offset)))
      , .ret (.var .r1)
      ]
    evalProg ubMode emitAssume fns 2 st callerA = .ok (.i32 (add32 xVal offset)) ∧
    evalProg ubMode emitAssume fns 2 st callerN = .ok (.i32 (add32 xVal offset)) ∧
    evalProg ubMode emitAssume fns 2 st callerInlined = .ok (.i32 (add32 xVal offset)) := by
  dsimp only []
  cases hx' : st .r0 with
  | unit => simp only [evalExpr, hx'] at hx; cases hx
  | bool _ => simp only [evalExpr, hx'] at hx; cases hx
  | i32 nx =>
      simp only [evalExpr, hx'] at hx
      injection hx with hVal
      injection hVal with hnx
      subst hnx
      simp only [evalProg, blockToOutcome, evalBlock, evalOne, evalFnCall, evalExpr, evalBinOp,
                 attrAddCallee, h1, h2, hx', updateStore_same]
      refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl

/-- Generalized Leaf Inlining Observational Theorem (`instantiateInlineBody`):
    For ANY single-assignment leaf function returning `.bin op (.var .calleeParam) c`
    or straight-line pure sequence bounded by `blockCallerSafe`, replacing `.callFn`
    by `inlineCallOnce cfg fns` preserves `evalProg` outcome identically! -/
noncomputable def leafInlineableStep (body : List Inst) : Bool :=
  match body with
  | [.ret rhs] => exprAllRegs (fun r => regEq r .calleeParam) rhs
  | [.assign .calleeLocal e1, .ret e2] =>
      Bool.and (exprAllRegs (fun r => regEq r .calleeParam) e1)
               (exprAllRegs (fun r => Bool.or (regEq r .calleeParam) (regEq r .calleeLocal)) e2)
  | _ => false

theorem renameExprReg_self (r : Reg) (e : Expr) :
    renameExprReg r r e = e := by
  induction e with
  | lit _ => rfl
  | var x =>
      unfold renameExprReg
      cases hx : regEq x r
      · rfl
      · have hEq := (regEq_eq_true_iff x r).mp hx
        subst hEq; rfl
  | not _ ih => unfold renameExprReg; rw [ih]
  | bin _ _ _ ihl ihr => unfold renameExprReg; rw [ihl, ihr]
  | blackBox _ ih => unfold renameExprReg; rw [ih]

theorem leafInlineableStep_cases (body : List Inst) (h : leafInlineableStep body = true) :
    (∃ rhs, body = [.ret rhs] ∧ exprAllRegs (fun r => regEq r .calleeParam) rhs = true) ∨
    (∃ e0 eRet, body = [.assign .calleeLocal e0, .ret eRet] ∧
      exprAllRegs (fun r => regEq r .calleeParam) e0 = true ∧
      exprAllRegs (fun r => Bool.or (regEq r .calleeParam) (regEq r .calleeLocal)) eRet = true) := by
  cases body with
  | nil => cases h
  | cons s0 t0 =>
      cases s0 with
      | ret rhs =>
          cases t0 with
          | cons _ _ => cases h
          | nil => exact Or.inl ⟨rhs, rfl, h⟩
      | assign d0 e0 =>
          cases d0 <;> try (cases t0 <;> cases h)
          cases t0 with
          | nil => cases h
          | cons s1 t1 =>
              cases s1 <;> try (cases t1 <;> cases h)
              case ret eRet =>
                cases t1 with
                | cons _ _ => cases h
                | nil =>
                    dsimp only [leafInlineableStep] at h
                    cases he0 : exprAllRegs (fun r => regEq r .calleeParam) e0 <;>
                      cases heRet : exprAllRegs (fun r => Bool.or (regEq r .calleeParam) (regEq r .calleeLocal)) eRet
                    · rw [he0] at h; cases h
                    · rw [he0] at h; cases h
                    · rw [he0, heRet] at h; cases h
                    · exact Or.inr ⟨e0, eRet, rfl, he0, heRet⟩
      | blackBoxAssign _ _ => cases t0 <;> cases h
      | checkedAssume _ => cases t0 <;> cases h
      | assume _ => cases t0 <;> cases h
      | checkedUnreachable _ => cases t0 <;> cases h
      | unreachable => cases t0 <;> cases h
      | branchOn _ _ _ => cases t0 <;> cases h
      | callFn _ _ _ => cases t0 <;> cases h

theorem evalBlock_leafInline_eq
    (ubMode : UbCheckMode) (emitAssume : Bool) (fns : FnTable)
    (fuel : Nat) (dst : Reg) (callee : FnId) (arg : Expr) (rest : List Inst)
    (st : Store)
    (_hDst : isCallerVisibleReg dst = true)
    (hParam : (fns callee).param = .calleeParam)
    (hLeaf : leafInlineableStep (fns callee).body = true)
    (hRestVis : blockCallerVisiblePred rest = true) :
    evalProg ubMode emitAssume fns (fuel + 1) st
      (.assign .calleeParam arg :: (instantiateInlineBody dst .calleeParam (fns callee).body ++ rest)) =
    evalProg ubMode emitAssume fns (fuel + 1) st (.callFn dst callee arg :: rest) := by
  unfold evalProg
  rcases leafInlineableStep_cases (fns callee).body hLeaf with
    ⟨rhs0, hBody, hRhs⟩ | ⟨e0, eRet, hBody, he0, heRet⟩
  · rw [hBody]
    dsimp only [instantiateInlineBody, List.cons_append, List.nil_append]
    rw [renameExprReg_self]
    simp only [evalBlock, evalOne]
    cases _hArg : evalExpr st arg with
    | none => rfl
    | some argv =>
        dsimp only [evalFnCall]
        rw [hParam, hBody]
        simp only [evalBlock, evalOne]
        have hAgrP : storeAgreeOn (fun r => regEq r .calleeParam)
            (updateStore st .calleeParam argv)
            (updateStore emptyStore .calleeParam argv) := by
          intro r hr
          have hrEq := (regEq_eq_true_iff r .calleeParam).mp hr
          subst hrEq
          rw [updateStore_same, updateStore_same]
        rw [evalExpr_storeAgreeOn _ rhs0 _ _ hAgrP hRhs]
        cases _hvRes : evalExpr (updateStore emptyStore .calleeParam argv) rhs0 with
        | none => rfl
        | some res =>
            dsimp only [blockToOutcome]
            apply evalBlock_storeAgreeOn_callerVisible ubMode emitAssume
              (evalFnCall ubMode emitAssume fns (fuel + 1)) rest _ _ hRestVis
            apply storeAgreeOn_update_both
            apply storeAgreeOn_update_hidden
            · rfl
            · exact storeAgreeOn_refl isCallerVisibleReg st
  · rw [hBody]
    dsimp only [instantiateInlineBody, List.cons_append, List.nil_append]
    rw [renameExprReg_self, renameExprReg_self]
    simp only [evalBlock, evalOne]
    cases _hArg : evalExpr st arg with
    | none => rfl
    | some argv =>
        dsimp only [evalFnCall]
        rw [hParam, hBody]
        simp only [evalBlock, evalOne]
        have hAgr1 : storeAgreeOn (fun r => regEq r .calleeParam)
            (updateStore st .calleeParam argv)
            (updateStore emptyStore .calleeParam argv) := by
          intro r hr
          have hrEq := (regEq_eq_true_iff r .calleeParam).mp hr
          subst hrEq
          rw [updateStore_same, updateStore_same]
        rw [evalExpr_storeAgreeOn _ e0 _ _ hAgr1 he0]
        cases _hv0 : evalExpr (updateStore emptyStore .calleeParam argv) e0 with
        | none => rfl
        | some locVal =>
            dsimp only []
            have hAgr2 : storeAgreeOn
                (fun r => Bool.or (regEq r .calleeParam) (regEq r .calleeLocal))
                (updateStore (updateStore st .calleeParam argv) .calleeLocal locVal)
                (updateStore (updateStore emptyStore .calleeParam argv) .calleeLocal locVal) := by
              intro r hr
              cases hrp : regEq r .calleeParam <;> cases hrl : regEq r .calleeLocal
              · dsimp only [] at hr; rw [hrp, hrl] at hr; cases hr
              · have hrL := (regEq_eq_true_iff r .calleeLocal).mp hrl
                subst hrL; rw [updateStore_same, updateStore_same]
              · have hrP := (regEq_eq_true_iff r .calleeParam).mp hrp
                subst hrP
                have hne : Reg.calleeParam ≠ Reg.calleeLocal := by intro h; cases h
                rw [updateStore_other _ .calleeLocal .calleeParam locVal hne]
                rw [updateStore_other _ .calleeLocal .calleeParam locVal hne]
                rw [updateStore_same, updateStore_same]
              · have hrL := (regEq_eq_true_iff r .calleeLocal).mp hrl
                subst hrL; rw [updateStore_same, updateStore_same]
            rw [evalExpr_storeAgreeOn _ eRet _ _ hAgr2 heRet]
            cases _hvRet : evalExpr (updateStore (updateStore emptyStore .calleeParam argv) .calleeLocal locVal) eRet with
            | none => rfl
            | some res =>
                dsimp only [blockToOutcome]
                apply evalBlock_storeAgreeOn_callerVisible ubMode emitAssume
                  (evalFnCall ubMode emitAssume fns (fuel + 1)) rest _ _ hRestVis
                apply storeAgreeOn_update_both
                apply storeAgreeOn_update_hidden
                · rfl
                · apply storeAgreeOn_update_hidden
                  · rfl
                  · exact storeAgreeOn_refl isCallerVisibleReg st

theorem inlineCallOnce_sound
    (cfg : CompilerFlags) (ubMode : UbCheckMode) (emitAssume : Bool)
    (fns : FnTable) (fuel : Nat) (dst : Reg) (callee : FnId)
    (arg : Expr) (rest : List Inst) (st : Store)
    (hDst : isCallerVisibleReg dst = true)
    (hParam : (fns callee).param = .calleeParam)
    (hLeaf : leafInlineableStep (fns callee).body = true)
    (hRestVis : blockCallerVisiblePred rest = true) :
    evalProg ubMode emitAssume fns (fuel + 1) st (inlineCallOnce cfg fns dst callee arg rest) =
    evalProg ubMode emitAssume fns (fuel + 1) st (.callFn dst callee arg :: rest) := by
  dsimp only [inlineCallOnce]
  have hIteF : ∀ {α : Type} (a b : α), (if (false = true) then a else b) = b := fun _ _ => rfl
  have hIteT : ∀ {α : Type} (a b : α), (if (true = true) then a else b) = a := fun _ _ => rfl
  cases hCond :
    Bool.and
      (llvmShouldInlineCall cfg.opt (lowerInlineToLlvm cfg (fns callee).attrs) (fns callee).attrs.cold)
      (Bool.and (regEq (fns callee).param .calleeParam)
                (inlineableLeafBody (fns callee).param (fns callee).body))
  · rw [hIteF]
  · rw [hIteT, hParam]
    exact evalBlock_leafInline_eq ubMode emitAssume fns fuel dst callee arg rest st hDst hParam hLeaf hRestVis

/-- End-to-End Composition Theorem:
    Composing constant folding (which respects `black_box` barriers),
    attribute retagging (`#[inline(always)]`/`#[inline(never)]`/`#[cold]`),
    assume-guided dead-branch pruning, and stripping `black_box` runtime barriers
    preserves `evalProg` semantics at `emitAssume = true`, while every defined
    execution under `ubOnFalse` refines to `abortOnFalse`. -/
theorem end_to_end_opt_and_refinement
    (fns : FnTable) (target : FnId) (newAttrs : FnAttrs)
    (fuel : Nat) (st : Store) (prog : List Inst) (v : Val)
    (hDefined : evalProg .ubOnFalse true fns fuel st prog = .ok v) :
    evalProg .abortOnFalse true (retagFnAttrs (stripBlackBoxFnTable fns) target newAttrs)
      fuel st (constFoldBlock (applyPruneHead (stripBlackBoxBlock prog))) = .ok v := by
  rw [fnAttrs_observational_equivalence_invariance]
  unfold evalProg
  rw [constFoldBlock_sound]
  rw [assume_dead_branch_pruning_sound]
  change evalProg .abortOnFalse true (stripBlackBoxFnTable fns) fuel st (stripBlackBoxBlock prog) = .ok v
  rw [blackBox_observational_identity]
  exact abortOnFalse_soundly_refines_ubOnFalse fns fuel st prog v hDefined

end VerifiedRustcHintInline
