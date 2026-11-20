/-!
# Core Language, Semantics, and Noninterference Definitions

This module defines a small deterministic imperative language with a two-point
confidentiality lattice (`low ≤ high`), total integer expressions, big-step
operational semantics, low-equivalence of stores, and the core security
properties (`TINI`, `CoTerminates`, `TSNI`).
-/

namespace Toy.IFC

/-- Two-point security lattice modeling public (`low`) and secret (`high`)
    confidentiality levels, following Denning & Denning (1977) and
    Volpano, Irvine & Smith (1996). -/
inductive Level where
  | low
  | high
  deriving DecidableEq, Repr

namespace Level

/-- Security ordering on `Level`: `low ≤ low`, `low ≤ high`, `high ≤ high`,
    and `¬ (high ≤ low)`. Models permitted direction of information flow. -/
def le : Level → Level → Prop
  | .low, _ => True
  | .high, .high => True
  | .high, .low => False

instance : LE Level := ⟨Level.le⟩

instance : DecidableRel (· ≤ · : Level → Level → Prop)
  | .low, _ => isTrue trivial
  | .high, .high => isTrue trivial
  | .high, .low => isFalse id

/-- Least upper bound (join) in the two-point security lattice `{low, high}`.
    Models combining information from two sources. -/
def join : Level → Level → Level
  | .low, l => l
  | .high, _ => .high

@[simp] theorem le_refl (l : Level) : l ≤ l := by
  cases l <;> trivial

theorem le_trans {a b c : Level} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [LE.le, Level.le]

theorem le_antisymm {a b : Level} (hab : a ≤ b) (hba : b ≤ a) : a = b := by
  cases a <;> cases b <;> simp_all [LE.le, Level.le]

@[simp] theorem low_le (l : Level) : Level.low ≤ l := trivial

@[simp] theorem le_high (l : Level) : l ≤ Level.high := by
  cases l <;> trivial

theorem eq_low_of_le_low {l : Level} (h : l ≤ Level.low) : l = Level.low := by
  cases l
  · rfl
  · cases h

theorem eq_high_of_high_le {l : Level} (h : Level.high ≤ l) : l = Level.high := by
  cases l
  · cases h
  · rfl

@[simp] theorem join_low_left (l : Level) : join .low l = l := rfl

@[simp] theorem join_low_right (l : Level) : join l .low = l := by
  cases l <;> rfl

@[simp] theorem join_high_left (l : Level) : join .high l = .high := rfl

@[simp] theorem join_high_right (l : Level) : join l .high = .high := by
  cases l <;> rfl

theorem le_join_left (a b : Level) : a ≤ join a b := by
  cases a <;> cases b <;> trivial

theorem le_join_right (a b : Level) : b ≤ join a b := by
  cases a <;> cases b <;> trivial

theorem join_le {a b c : Level} (ha : a ≤ c) (hb : b ≤ c) : join a b ≤ c := by
  cases a <;> cases b <;> cases c <;> simp_all [LE.le, Level.le, join]

theorem join_mono {a₁ a₂ b₁ b₂ : Level} (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    join a₁ b₁ ≤ join a₂ b₂ :=
  join_le (le_trans ha (le_join_left a₂ b₂)) (le_trans hb (le_join_right a₂ b₂))

theorem join_eq_low_iff {a b : Level} : join a b = .low ↔ a = .low ∧ b = .low := by
  cases a <;> cases b <;> simp [join]

end Level

infixl:65 " ⊔ " => Level.join

/-- A program store mapping variables to integer values. -/
abbrev Store (Var : Type) := Var → Int

/-- Functional store update: sets `x` to `v` and leaves all other variables unchanged. -/
def Store.update {Var : Type} [DecidableEq Var]
    (σ : Store Var) (x : Var) (v : Int) : Store Var :=
  fun y => if y = x then v else σ y

@[simp] theorem Store.update_eq {Var : Type} [DecidableEq Var]
    (σ : Store Var) (x : Var) (v : Int) :
    Store.update σ x v x = v := by
  simp [Store.update]

@[simp] theorem Store.update_ne {Var : Type} [DecidableEq Var]
    (σ : Store Var) {x y : Var} (v : Int) (hne : y ≠ x) :
    Store.update σ x v y = σ y := by
  simp [Store.update, hne]

/-- The everywhere-zero store, useful for constructing concrete executions. -/
def zeroStore {Var : Type} : Store Var := fun _ => 0

/-- Low-equivalence of two stores under security labeling `Γ`: `σ₁` and `σ₂`
    agree on every `low`-labeled variable and may differ arbitrarily on
    `high`-labeled variables. Models attacker indistinguishability of program states. -/
def LowEq {Var : Type} (Γ : Var → Level) (σ₁ σ₂ : Store Var) : Prop :=
  ∀ x, Γ x = .low → σ₁ x = σ₂ x

theorem LowEq.refl {Var : Type} (Γ : Var → Level) (σ : Store Var) : LowEq Γ σ σ :=
  fun _ _ => rfl

theorem LowEq.symm {Var : Type} {Γ : Var → Level} {σ₁ σ₂ : Store Var}
    (h : LowEq Γ σ₁ σ₂) : LowEq Γ σ₂ σ₁ :=
  fun x hx => (h x hx).symm

theorem LowEq.trans {Var : Type} {Γ : Var → Level} {σ₁ σ₂ σ₃ : Store Var}
    (h₁ : LowEq Γ σ₁ σ₂) (h₂ : LowEq Γ σ₂ σ₃) : LowEq Γ σ₁ σ₃ :=
  fun x hx => (h₁ x hx).trans (h₂ x hx)

/-- Derivable separation lemma: any `low`-labeled variable is distinct from any
    `high`-labeled variable, so `l ≠ h` need not be assumed separately. -/
theorem low_ne_high_var {Var : Type} {Γ : Var → Level} {l h : Var}
    (hLow : Γ l = .low) (hHigh : Γ h = .high) : l ≠ h := by
  intro heq
  subst heq
  rw [hLow] at hHigh
  cases hHigh

theorem LowEq.update_high {Var : Type} [DecidableEq Var]
    {Γ : Var → Level} {σ : Store Var} {h : Var} (v : Int) (hHigh : Γ h = .high) :
    LowEq Γ σ (Store.update σ h v) := by
  intro x hx
  have hne : x ≠ h := low_ne_high_var hx hHigh
  simp [Store.update, hne]

/-- Expressions of the toy imperative language. Every expression is total and
    evaluates to an integer; in control-flow guards (`if`, `while`), `0` represents
    false and any nonzero integer represents true. -/
inductive Expr (Var : Type) where
  | lit (n : Int)
  | var (x : Var)
  | add (e₁ e₂ : Expr Var)
  | sub (e₁ e₂ : Expr Var)
  | eq (e₁ e₂ : Expr Var)
  | lt (e₁ e₂ : Expr Var)
  | not (e : Expr Var)
  deriving DecidableEq, Repr

/-- Total big-step evaluation of expressions in a store. Partial operations
    (such as division) are intentionally excluded so expression evaluation
    cannot introduce error or exception channels. -/
def eval {Var : Type} (σ : Store Var) : Expr Var → Int
  | .lit n => n
  | .var x => σ x
  | .add e₁ e₂ => eval σ e₁ + eval σ e₂
  | .sub e₁ e₂ => eval σ e₁ - eval σ e₂
  | .eq e₁ e₂ => if eval σ e₁ = eval σ e₂ then 1 else 0
  | .lt e₁ e₂ => if eval σ e₁ < eval σ e₂ then 1 else 0
  | .not e => if eval σ e = 0 then 1 else 0

/-- Syntactic security level of an expression: the join of the security levels
    of all variables occurring in `e` (`low` for variable-free expressions).
    Captures the conservative static upper bound on what secrets an expression reads. -/
def exprLevel {Var : Type} (Γ : Var → Level) : Expr Var → Level
  | .lit _ => .low
  | .var x => Γ x
  | .add e₁ e₂ => exprLevel Γ e₁ ⊔ exprLevel Γ e₂
  | .sub e₁ e₂ => exprLevel Γ e₁ ⊔ exprLevel Γ e₂
  | .eq e₁ e₂ => exprLevel Γ e₁ ⊔ exprLevel Γ e₂
  | .lt e₁ e₂ => exprLevel Γ e₁ ⊔ exprLevel Γ e₂
  | .not e => exprLevel Γ e

/-- Low-expression agreement lemma: an expression with syntactic level `low`
    evaluates identically on any two low-equivalent stores. -/
theorem exprLevel_low_agrees {Var : Type} {Γ : Var → Level}
    {σ₁ σ₂ : Store Var} {e : Expr Var}
    (hLow : LowEq Γ σ₁ σ₂) (hLvl : exprLevel Γ e = .low) :
    eval σ₁ e = eval σ₂ e := by
  induction e with
  | lit n => rfl
  | var x => exact hLow x hLvl
  | add e₁ e₂ ih₁ ih₂ =>
    simp only [exprLevel, Level.join_eq_low_iff] at hLvl
    simp only [eval, ih₁ hLvl.1, ih₂ hLvl.2]
  | sub e₁ e₂ ih₁ ih₂ =>
    simp only [exprLevel, Level.join_eq_low_iff] at hLvl
    simp only [eval, ih₁ hLvl.1, ih₂ hLvl.2]
  | eq e₁ e₂ ih₁ ih₂ =>
    simp only [exprLevel, Level.join_eq_low_iff] at hLvl
    simp only [eval, ih₁ hLvl.1, ih₂ hLvl.2]
  | lt e₁ e₂ ih₁ ih₂ =>
    simp only [exprLevel, Level.join_eq_low_iff] at hLvl
    simp only [eval, ih₁ hLvl.1, ih₂ hLvl.2]
  | not e ih =>
    simp only [exprLevel] at hLvl
    simp only [eval, ih hLvl]

/-- Commands of the toy imperative language: no-op, variable assignment,
    sequential composition, conditional branching, and while-loops. -/
inductive Cmd (Var : Type) where
  | skip
  | assign (x : Var) (e : Expr Var)
  | seq (c₁ c₂ : Cmd Var)
  | ite (e : Expr Var) (c₁ c₂ : Cmd Var)
  | whileLoop (e : Expr Var) (c : Cmd Var)
  deriving DecidableEq, Repr

/-- Inductive big-step operational semantics: `Eval c σ σ'` holds when executing
    command `c` from initial store `σ` terminates in final store `σ'`.
    Non-terminating executions have no derivation, and execution time / intermediate
    states are not modeled. -/
inductive Eval {Var : Type} [DecidableEq Var] : Cmd Var → Store Var → Store Var → Prop where
  | skip {σ} :
      Eval .skip σ σ
  | assign {x e σ} :
      Eval (.assign x e) σ (Store.update σ x (eval σ e))
  | seq {c₁ c₂ σ σm σ'} :
      Eval c₁ σ σm →
      Eval c₂ σm σ' →
      Eval (.seq c₁ c₂) σ σ'
  | iteTrue {e c₁ c₂ σ σ'} :
      eval σ e ≠ 0 →
      Eval c₁ σ σ' →
      Eval (.ite e c₁ c₂) σ σ'
  | iteFalse {e c₁ c₂ σ σ'} :
      eval σ e = 0 →
      Eval c₂ σ σ' →
      Eval (.ite e c₁ c₂) σ σ'
  | whileFalse {e c σ} :
      eval σ e = 0 →
      Eval (.whileLoop e c) σ σ
  | whileTrue {e c σ σm σ'} :
      eval σ e ≠ 0 →
      Eval c σ σm →
      Eval (.whileLoop e c) σm σ' →
      Eval (.whileLoop e c) σ σ'

/-- Big-step evaluation is deterministic: from a given command and initial store,
    at most one final store is reachable. -/
theorem eval_deterministic {Var : Type} [DecidableEq Var]
    {c : Cmd Var} {σ σ₁ σ₂ : Store Var}
    (h₁ : Eval c σ σ₁) (h₂ : Eval c σ σ₂) : σ₁ = σ₂ := by
  induction h₁ generalizing σ₂ with
  | skip =>
    cases h₂
    rfl
  | assign =>
    cases h₂
    rfl
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₂a h₂b =>
      have hm := ih₁ h₂a
      subst hm
      exact ih₂ h₂b
  | iteTrue hne _ ih =>
    cases h₂ with
    | iteTrue _ h₂' => exact ih h₂'
    | iteFalse heq _ => exact absurd heq hne
  | iteFalse heq _ ih =>
    cases h₂ with
    | iteTrue hne _ => exact absurd heq hne
    | iteFalse _ h₂' => exact ih h₂'
  | whileFalse heq =>
    cases h₂ with
    | whileFalse _ => rfl
    | whileTrue hne _ _ => exact absurd heq hne
  | whileTrue hne _ _ ihBody ihLoop =>
    cases h₂ with
    | whileFalse heq => exact absurd heq hne
    | whileTrue _ h₂Body h₂Loop =>
      have hm := ihBody h₂Body
      subst hm
      exact ihLoop h₂Loop

/-- Termination predicate: command `c` terminates from initial store `σ` iff
    the big-step semantics relates `(c, σ)` to some final store `σ'`. -/
def Terminates {Var : Type} [DecidableEq Var] (c : Cmd Var) (σ : Store Var) : Prop :=
  ∃ σ', Eval c σ σ'

/-- General divergence helper: a `while e do skip` loop never terminates from
    any store where `eval σ e ≠ 0`, because `.skip` leaves the store unchanged. -/
theorem while_skip_no_eval {Var : Type} [DecidableEq Var]
    {e : Expr Var} {σ σ' : Store Var}
    (hEval : Eval (.whileLoop e .skip) σ σ') (hne : eval σ e ≠ 0) : False := by
  suffices ∀ {c s s'}, Eval c s s' → c = .whileLoop e .skip → eval s e ≠ 0 → False from
    this hEval rfl hne
  intro c s s' h
  induction h with
  | whileFalse heq =>
    intro hc hne'
    cases hc
    exact hne' heq
  | whileTrue _ hBody _ _ ihLoop =>
    intro hc hne'
    cases hc
    cases hBody
    exact ihLoop rfl hne'
  | _ =>
    intro hc _
    cases hc

/-- Termination-insensitive noninterference (TINI) for command `c` under security
    labeling `Γ`: whenever two low-equivalent initial stores both lead to
    terminating executions, their final stores are low-equivalent.
    Models confidentiality against a batch-job low observer who observes final
    low outputs only when execution terminates. -/
def TINI {Var : Type} [DecidableEq Var] (Γ : Var → Level) (c : Cmd Var) : Prop :=
  ∀ σ₁ σ₂ σ₁' σ₂',
    LowEq Γ σ₁ σ₂ →
    Eval c σ₁ σ₁' →
    Eval c σ₂ σ₂' →
    LowEq Γ σ₁' σ₂'

/-- Co-termination on low-equivalent inputs: from any two low-equivalent initial
    stores, command `c` terminates on one iff it terminates on the other.
    Models absence of a termination covert channel. -/
def CoTerminates {Var : Type} [DecidableEq Var] (Γ : Var → Level) (c : Cmd Var) : Prop :=
  ∀ σ₁ σ₂, LowEq Γ σ₁ σ₂ → (Terminates c σ₁ ↔ Terminates c σ₂)

/-- Termination-sensitive noninterference (TSNI) for command `c` under security
    labeling `Γ`: whenever `c` terminates from `σ₁` in `σ₁'` and `σ₂` is
    low-equivalent to `σ₁`, `c` also terminates from `σ₂` in a final store `σ₂'`
    that is low-equivalent to `σ₁'`.
    Models confidentiality against a batch-job low observer who can observe both
    whether a program terminates and its final low outputs (though not step counts
    or wall-clock timing). -/
def TSNI {Var : Type} [DecidableEq Var] (Γ : Var → Level) (c : Cmd Var) : Prop :=
  ∀ σ₁ σ₂ σ₁',
    LowEq Γ σ₁ σ₂ →
    Eval c σ₁ σ₁' →
    ∃ σ₂', Eval c σ₂ σ₂' ∧ LowEq Γ σ₁' σ₂'

/-! ### Minimal Two-Variable Test Harness & Definition Examples -/

/-- A minimal two-variable domain with one public variable `l` and one secret
    variable `h`, used for concrete positive/negative definition examples and
    non-vacuity witnesses. -/
inductive TwoVar where
  | l
  | h
  deriving DecidableEq, Repr

/-- Standard labeling on `TwoVar`: `l` is `low` and `h` is `high`. -/
def twoVarEnv : TwoVar → Level
  | .l => .low
  | .h => .high

/-- Concrete store with `l = 0, h = 0`. -/
def storeZero : Store TwoVar := zeroStore

/-- Concrete store with `l = 0, h = 1` (low-equivalent to `storeZero`). -/
def storeHighOne : Store TwoVar := Store.update storeZero .h 1

/-- Concrete store with `l = 1, h = 0` (not low-equivalent to `storeZero`). -/
def storeLowOne : Store TwoVar := Store.update storeZero .l 1

/-- Direct explicit-flow program `l := h`. -/
def explicitFlowProg {Var : Type} (l h : Var) : Cmd Var :=
  .assign l (.var h)

/-- Classic implicit-flow program `if h then l := 1 else l := 0`. -/
def implicitFlowProg {Var : Type} (l h : Var) : Cmd Var :=
  .ite (.var h) (.assign l (.lit 1)) (.assign l (.lit 0))

/-- Classic termination-channel program `while h do skip`. -/
def termChannelProg {Var : Type} (h : Var) : Cmd Var :=
  .whileLoop (.var h) .skip

/-- Low-guarded infinite loop nested under a high conditional:
    `if h then (while 1 do skip) else skip`. -/
def highIfLowWhileProg {Var : Type} (h : Var) : Cmd Var :=
  .ite (.var h) (.whileLoop (.lit 1) .skip) .skip

/-- Implicit flow through a high-guarded while loop:
    `while h do (l := 1; h := 0)`. Terminates in at most one iteration and copies
    whether `h ≠ 0` into `l`. -/
def whileLeakProg {Var : Type} (l h : Var) : Cmd Var :=
  .whileLoop (.var h) (.seq (.assign l (.lit 1)) (.assign h (.lit 0)))

/-- Repeated-run termination probe `while l < h do skip`: accepted by `CmdTyped`
    at every `pc`, and its termination behavior as a function of low input `l`
    determines the secret `h` exactly. -/
def probeProg {Var : Type} (l h : Var) : Cmd Var :=
  .whileLoop (.lt (.var l) (.var h)) .skip

/-- Terminating high-guarded loop `while h do h := 0`: satisfies `TSNI` yet is
    rejected by `TsTyped` at every `pc`, witnessing that `TsTyped` is sufficient
    but not necessary for `TSNI`. -/
def whileHZero : Cmd TwoVar :=
  .whileLoop (.var .h) (.assign .h (.lit 0))

-- Positive & negative examples for `Level.le`

/-- Positive example for `Level.le`: `low ≤ high`. -/
theorem level_le_pos_low_high : Level.low ≤ Level.high := trivial

/-- Negative example for `Level.le`: `¬ (high ≤ low)`. -/
theorem level_le_neg_high_low : ¬ (Level.high ≤ Level.low) := id

-- Positive & negative examples for `LowEq`

/-- Positive example for `LowEq`: stores differing only on `h` are low-equivalent. -/
theorem lowEq_pos_high_diff : LowEq twoVarEnv storeZero storeHighOne := by
  intro x hx
  cases x with
  | l => rfl
  | h => cases hx

/-- Negative example for `LowEq`: stores differing on `l` are not low-equivalent. -/
theorem lowEq_neg_low_diff : ¬ LowEq twoVarEnv storeZero storeLowOne := by
  intro h
  have hl := h .l rfl
  simp [storeZero, storeLowOne, zeroStore, Store.update] at hl

-- Positive & negative examples for `Eval`

/-- Positive example for `Eval`: a loop decrementing `l` from `1` to `0` terminates
    in `storeZero` (exercising both `whileTrue` and `whileFalse`). -/
theorem eval_pos_while_decrement :
    Eval (.whileLoop (.var .l) (.assign .l (.sub (.var .l) (.lit 1)))) storeLowOne storeZero := by
  refine Eval.whileTrue (σm := Store.update storeLowOne .l (eval storeLowOne (.sub (.var .l) (.lit 1)))) ?_ ?_ ?_
  · simp [eval, storeLowOne, Store.update]
  · exact Eval.assign
  · have hEq : Store.update storeLowOne .l (eval storeLowOne (.sub (.var .l) (.lit 1))) = storeZero := by
      funext x
      cases x <;> simp [eval, storeLowOne, storeZero, zeroStore, Store.update]
    rw [hEq]
    exact Eval.whileFalse (by simp [eval, storeZero, zeroStore])

/-- Negative example for `Eval`: `l := 1` from `storeZero` does not yield `storeZero`. -/
theorem eval_neg_wrong_final :
    ¬ Eval (.assign .l (.lit 1)) storeZero storeZero := by
  intro h
  have hDet := eval_deterministic h (Eval.assign (x := .l) (e := .lit 1) (σ := storeZero))
  have hAt := congrFun hDet .l
  simp [eval, storeZero, zeroStore, Store.update] at hAt

-- Positive & negative examples for `Terminates`

/-- Positive example for `Terminates`: an assignment terminates from `storeZero`. -/
theorem terminates_pos_assign :
    Terminates (.assign .l (.lit 1)) storeZero :=
  ⟨Store.update storeZero .l 1, Eval.assign⟩

/-- Negative example for `Terminates`: `while 1 do skip` diverges from `storeZero`. -/
theorem terminates_neg_while_one :
    ¬ Terminates (.whileLoop (.lit 1) .skip) storeZero := by
  rintro ⟨σ', hEval⟩
  exact while_skip_no_eval hEval (by simp [eval])

-- Positive & negative examples for `TINI`

/-- Positive example for `TINI`: branching on `h` to assign to `h` satisfies `TINI`. -/
theorem tini_pos_high_branch_high_write :
    TINI twoVarEnv (.ite (.var .h) (.assign .h (.lit 1)) (.assign .h (.lit 0))) := by
  intro σ₁ σ₂ σ₁' σ₂' hLow h₁ h₂
  have hPres₁ : LowEq twoVarEnv σ₁ σ₁' := by
    cases h₁ with
    | iteTrue _ hb =>
      cases hb
      exact LowEq.update_high 1 rfl
    | iteFalse _ hb =>
      cases hb
      exact LowEq.update_high 0 rfl
  have hPres₂ : LowEq twoVarEnv σ₂ σ₂' := by
    cases h₂ with
    | iteTrue _ hb =>
      cases hb
      exact LowEq.update_high 1 rfl
    | iteFalse _ hb =>
      cases hb
      exact LowEq.update_high 0 rfl
  exact hPres₁.symm.trans (hLow.trans hPres₂)

/-- Negative example for `TINI`: direct assignment `l := h` violates `TINI`. -/
theorem tini_neg_explicit_flow :
    ¬ TINI twoVarEnv (explicitFlowProg .l .h) := by
  intro hTini
  have hRes := hTini storeZero storeHighOne
    (Store.update storeZero .l (eval storeZero (.var .h)))
    (Store.update storeHighOne .l (eval storeHighOne (.var .h)))
    lowEq_pos_high_diff Eval.assign Eval.assign
  have hl := hRes .l rfl
  simp [eval, storeZero, storeHighOne, zeroStore, Store.update] at hl

-- Positive & negative examples for `CoTerminates`

/-- Positive example for `CoTerminates`: `skip` terminates on every store. -/
theorem coTerminates_pos_skip : CoTerminates twoVarEnv .skip := by
  intro σ₁ σ₂ _
  exact ⟨fun _ => ⟨σ₂, Eval.skip⟩, fun _ => ⟨σ₁, Eval.skip⟩⟩

/-- Non-trivial positive example for `CoTerminates`: `while l do skip`
    co-terminates on all low-equivalent stores even though it diverges on stores
    where `l ≠ 0` (so termination genuinely varies, but only with `low` data). -/
theorem coTerminates_pos_while_l :
    CoTerminates twoVarEnv (termChannelProg TwoVar.l) ∧
    ¬ ∀ σ, Terminates (termChannelProg TwoVar.l) σ := by
  constructor
  · intro σ₁ σ₂ hLow
    have hl : σ₁ TwoVar.l = σ₂ TwoVar.l := hLow TwoVar.l rfl
    constructor
    · rintro ⟨σ₁', hEval⟩
      match hEval with
      | .whileFalse heq =>
        exact ⟨σ₂, Eval.whileFalse (by simpa [eval, hl] using heq)⟩
      | hEval@(.whileTrue hne _ _) =>
        exact False.elim (while_skip_no_eval hEval hne)
    · rintro ⟨σ₂', hEval⟩
      match hEval with
      | .whileFalse heq =>
        exact ⟨σ₁, Eval.whileFalse (by simpa [eval, hl] using heq)⟩
      | hEval@(.whileTrue hne _ _) =>
        exact False.elim (while_skip_no_eval hEval hne)
  · intro hAll
    rcases hAll storeLowOne with ⟨σ', hEval⟩
    exact while_skip_no_eval hEval (by simp [eval, storeLowOne, Store.update])

/-- Negative example for `CoTerminates`: `while h do skip` terminates on `storeZero`
    but diverges on low-equivalent `storeHighOne`. -/
theorem coTerminates_neg_while_h : ¬ CoTerminates twoVarEnv (termChannelProg .h) := by
  intro hCo
  have hTerm₀ : Terminates (termChannelProg .h) storeZero :=
    ⟨storeZero, Eval.whileFalse (by simp [eval, storeZero, zeroStore])⟩
  rcases (hCo storeZero storeHighOne lowEq_pos_high_diff).mp hTerm₀ with ⟨σ', hEval⟩
  exact while_skip_no_eval hEval (by simp [eval, storeHighOne, Store.update])

-- Positive & negative examples for `TSNI`

/-- Positive example for `TSNI`: incrementing `l` satisfies `TSNI`. -/
theorem tsni_pos_low_inc : TSNI twoVarEnv (.assign .l (.add (.var .l) (.lit 1))) := by
  intro σ₁ σ₂ σ₁' hLow h₁
  cases h₁
  refine ⟨Store.update σ₂ .l (eval σ₂ (.add (.var .l) (.lit 1))), Eval.assign, ?_⟩
  intro x hx
  cases x with
  | l =>
    have hl := hLow .l rfl
    simp [eval, Store.update, hl]
  | h => cases hx

/-- Negative example for `TSNI`: `while h do skip` violates `TSNI`. -/
theorem tsni_neg_while_h : ¬ TSNI twoVarEnv (termChannelProg .h) := by
  intro hTsni
  have hEval₀ : Eval (termChannelProg .h) storeZero storeZero :=
    Eval.whileFalse (by simp [eval, storeZero, zeroStore])
  rcases hTsni storeZero storeHighOne storeZero lowEq_pos_high_diff hEval₀ with ⟨σ', hEval₁, _⟩
  exact while_skip_no_eval hEval₁ (by simp [eval, storeHighOne, Store.update])

end Toy.IFC
