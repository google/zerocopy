import Toy.Render.Defs

/-!
# Concrete instances and definition examples (`Toy.Render`)

A fixed signature `S₀` with variables `a b : Nat`, `z : Int`, abbreviations
`P := (a = b)`, `Q := (z = 0)`, `PQ := P ∧ Q`, the terms used throughout the package,
and, for each core definition, proved positive and negative examples.
-/

namespace Toy.Render

/-! ## The running signature and terms -/

/-- `a : Nat` (variable 0). -/
def vA : Tm := .var 0 .nat
/-- `b : Nat` (variable 1). -/
def vB : Tm := .var 1 .nat
/-- `z : Int` (variable 2). -/
def vZ : Tm := .var 2 .int

/-- The running signature. Context: `a b : Nat`, `z : Int`. Definitions (telescope,
outermost first): `PQ := P ∧ Q` (name 2), `P := (a = b)` at `Nat` (name 0),
`Q := (z = 0)` at `Int` (name 1). -/
def S₀ : Sig where
  ctx := [(0, .nat), (1, .nat), (2, .int)]
  defs := [⟨2, .prop, .and (.const 0) (.const 1)⟩,
           ⟨0, .prop, .eq .nat vA vB⟩,
           ⟨1, .prop, .eq .int vZ (.lit .int 0)⟩]

/-- `(2 : Nat) - 3 = 0` (true: subtraction truncates). -/
def tNatSub : Tm := .eq .nat (.sub .nat (.lit .nat 2) (.lit .nat 3)) (.lit .nat 0)

/-- `(2 : Int) - 3 = 0` (false). -/
def tIntSub : Tm := .eq .int (.sub .int (.lit .int 2) (.lit .int 3)) (.lit .int 0)

/-- `↑(a - b) = ↑a - ↑b` at `Int` (false when `a < b`). -/
def tTrunc : Tm := .eq .int (.coe (.sub .nat vA vB)) (.sub .int (.coe vA) (.coe vB))

/-- `a - b = a - b` at `Nat` (a tautology): how the default text of `tTrunc` reads back. -/
def tReread : Tm := .eq .nat (.sub .nat vA vB) (.sub .nat vA vB)

/-- `↑(a - b) = z` at `Int`: default text `a - b = z`. -/
def tZ : Tm := .eq .int (.coe (.sub .nat vA vB)) vZ

/-- `↑a - ↑b = z` at `Int`: the leaf-coercion reading of `a - b = z`. -/
def tZLeaves : Tm := .eq .int (.sub .int (.coe vA) (.coe vB)) vZ

/-- `↑(a + b) = z` at `Int`. -/
def tAddOp : Tm := .eq .int (.coe (.add .nat vA vB)) vZ

/-- `↑a + ↑b = z` at `Int`. -/
def tAddLeaves : Tm := .eq .int (.add .int (.coe vA) (.coe vB)) vZ

/-- A fully annotated text `@eq Int (2 : Int) z`. -/
def sTwoEqZ : Stx := .eq (some .int) (.asc (.num 2) .int) (.var 2)

/-- An ill-typed term: the variable `a : Nat` annotated as `Int`. -/
def tIll : Tm := .var 0 .int

/-- An ill-typed proposition `a ↔ a` (with `a : Nat`); its default text does not elaborate. -/
def tIffNat : Tm := .iff vA vA

/-- The environment `a = 0`, `b = 1`, `z = 0`. -/
def ρ₀ : Env where
  nat := fun x => if x = 1 then 1 else 0
  int := fun _ => 0
  prop := fun _ => false

/-! ## Examples: types and hints -/

example : Ty.isNum .int = true := rfl
example : Ty.isNum .prop = false := rfl
example : joinH (some .nat) (some .int) = some .int := rfl
example : joinH none none = none := rfl
example : numOnly (some .prop) = none := rfl
example : numOnly (some .int) = some .int := rfl

/-! ## Examples: typing -/

/-- Positive: `↑(a - b) = ↑a - ↑b` is well typed. -/
theorem wellTyped_tTrunc : WellTyped S₀ tTrunc := by decide
/-- Negative: a coercion applied to an `Int` is rejected. -/
theorem not_wellTyped_coe_int : ¬ WellTyped S₀ (.coe vZ) := by decide
/-- Negative: a variable annotated with a type other than its context type is rejected. -/
theorem not_wellTyped_tIll : ¬ WellTyped S₀ tIll := by decide

/-! ## Examples: semantics -/

/-- Positive: `(2 : Nat) - 3 = 0` is valid. -/
theorem valid_tNatSub : Valid S₀ tNatSub := fun _ => rfl
/-- Negative: `(2 : Int) - 3 = 0` is not valid (it is false everywhere). -/
theorem not_denote_tIntSub (ρ : Env) : ¬ Denote S₀ tIntSub ρ := by
  simp [Denote, eval, evalD, evalWith, tIntSub, S₀, Val.toInt, Val.toBool]
theorem not_valid_tIntSub : ¬ Valid S₀ tIntSub := fun h => not_denote_tIntSub ρ₀ (h ρ₀)
/-- Positive: the abbreviation `P` means `a = b`. -/
example : eval S₀ ρ₀ (.const 0) = eval S₀ ρ₀ (.eq .nat vA vB) := by decide
/-- Negative: an undefined name has the default value. -/
example : eval S₀ ρ₀ (.const 9) = undefVal := by decide

/-! ## Examples: δ-unfolding -/

/-- Positive: `PQ` unfolds to `(a = b) ∧ (z = 0)`. -/
example : deltaNF S₀ (.const 2) = .and (.eq .nat vA vB) (.eq .int vZ (.lit .int 0)) := by decide
/-- Negative: an undefined name is left alone. -/
example : deltaNF S₀ (.const 9) = .const 9 := by decide

/-! ## Examples: elaboration -/

example : hint S₀ (.num 2) = none := rfl
example : hint S₀ (.add none (.var 0) (.num 2)) = some .nat := by decide
example : opType cfg0 (some .nat) (some .int) = .nat := rfl
example : opType cfgLeaves (some .nat) (some .int) = .int := rfl
example : coerceTo (some .int) (vA, .nat) = some (.coe vA, .int) := by decide
/-- Negative: there is no `Int ↝ Nat` coercion. -/
example : coerceTo (some .nat) (vZ, .int) = none := by decide

/-- Positive: the system elaborator reads `a - b = z` as `↑(a - b) = z`. -/
theorem elabSys_ppDefault_tZ : elabSys S₀ (ppDefault tZ) = some tZ := by decide
/-- Negative: `a ↔ a` with `a : Nat` does not elaborate. -/
theorem elabSys_ppDefault_tIffNat : elabSys S₀ (ppDefault tIffNat) = none := by decide
/-- Positive: an unconstrained numeral defaults to `Nat` under `cfg0`. -/
example : elabSys S₀ (.num 2) = some (.lit .nat 2) := by decide
/-- Negative: under `cfgIntNumerals` the same numeral is read at `Int`. -/
example : elabWith cfgIntNumerals S₀ (.num 2) ≠ some (.lit .nat 2) := by decide

/-- Positive: the explicit rendering of `tTrunc` is faithful. -/
theorem faithful_ppExplicit_tTrunc : Faithful cfg0 S₀ (ppExplicit tTrunc) tTrunc := by decide
/-- Negative: the default rendering of `tTrunc` is not faithful. -/
theorem not_faithful_ppDefault_tTrunc : ¬ Faithful cfg0 S₀ (ppDefault tTrunc) tTrunc := by decide

/-! ## Examples: printers -/

/-- Positive: the default text of `tTrunc` is `a - b = a - b`. -/
theorem ppDefault_tTrunc :
    ppDefault tTrunc = .eq none (.sub none (.var 0) (.var 1)) (.sub none (.var 0) (.var 1)) := by
  decide
/-- Positive: the explicit text of `tTrunc` is `@eq Int ↑(@sub Nat a b) (@sub Int ↑a ↑b)`. -/
theorem ppExplicit_tTrunc :
    ppExplicit tTrunc = .eq (some .int) (.coe (.sub (some .nat) (.var 0) (.var 1)))
      (.sub (some .int) (.coe (.var 0)) (.coe (.var 1))) := by
  decide
/-- Negative: the default printer does not show a coercion. -/
example : ppDefault (.coe vA) ≠ .coe (.var 0) := by decide
/-- Positive: an intermediate printer shows numeral types only. -/
example : ppNumericTypes tIntSub =
    .eq none (.sub none (.asc (.num 2) .int) (.asc (.num 3) .int)) (.asc (.num 0) .int) := by decide
/-- Negative: the numeral-type printer does not show coercions. -/
example : ppNumericTypes (.coe vA) = .var 0 := by decide
example : annPos [] tZ = [([], .typeArg), ([0], .coercion), ([0, 0], .typeArg)] := by decide
/-- Negative: a variable has no annotation position. -/
example : annPos [] vA = [] := rfl
example : maskOf [([], .typeArg)] [] .typeArg = true := by decide
example : maskOf [([], .typeArg)] [] .coercion = false := by decide

/-- Positive: the deletion-greedy rendering of `tTrunc` under `cfg0` is
`a - b = a - ↑b` (one explicit coercion). -/
theorem ppMin_tTrunc :
    ppMin cfg0 S₀ tTrunc =
      .eq none (.sub none (.var 0) (.var 1)) (.sub none (.var 0) (.coe (.var 1))) := by
  decide
/-- Negative: it is not the default rendering. -/
example : ppMin cfg0 S₀ tTrunc ≠ ppDefault tTrunc := by decide

/-- Positive: the deletion-greedy rendering of `(2 : Int) - 3 = 0` under `cfg0` is
`2 - 3 = (0 : Int)` (one ascription). -/
theorem ppMin_tIntSub :
    ppMin cfg0 S₀ tIntSub = .eq none (.sub none (.num 2) (.num 3)) (.asc (.num 0) .int) := by
  decide

example : (ppExplicit tTrunc).annCount = 6 := by decide
example : (ppDefault tTrunc).annCount = 0 := by decide
example : (ppExplicit tTrunc).erase = ppDefault tTrunc := by decide
/-- Positive / negative: explicit text is fully annotated, default text is not. -/
example : (ppExplicit tTrunc).fullyAnnotated = true := by decide
example : (ppDefault tTrunc).fullyAnnotated = false := by decide
example : (ppDefault tAddOp).subFree = true := by decide
example : (ppDefault tZ).subFree = false := by decide

/-! ## Examples: default recoverability -/

example : dh S₀ (.coe (.sub .nat vA vB)) = some .nat := by decide
/-- Positive: every annotation `ppDefault` elides from `tZ` is recoverable. -/
theorem defaultRecoverable_tZ : DefaultRecoverable S₀ tZ := by decide
/-- Negative: the coercion of `↑(a - b) = ↑a - ↑b` is not recoverable. -/
theorem not_defaultRecoverable_tTrunc : ¬ DefaultRecoverable S₀ tTrunc := by decide

/-! ## Examples: declarative elaboration -/

/-- Positive: `a - b = z` admits the operator-coercion elaboration. -/
theorem elabs_ppDefault_tZ_tZ : Elabs S₀ (ppDefault tZ) .prop tZ :=
  .eq (τ := .int) rfl (.inl rfl)
    (.coeIns (.sub rfl (.inl rfl) (.var rfl) (.var rfl)))
    (.var rfl)

/-- Positive: `a - b = z` also admits the leaf-coercion elaboration. -/
theorem elabs_ppDefault_tZ_tZLeaves : Elabs S₀ (ppDefault tZ) .prop tZLeaves :=
  .eq (τ := .int) rfl (.inl rfl)
    (.sub rfl (.inl rfl) (.coeIns (.var rfl)) (.coeIns (.var rfl)))
    (.var rfl)

/-- Negative: an `Int` variable never elaborates at `Nat` (no `Int ↝ Nat` coercion). -/
theorem not_elabs_int_var_at_nat (t : Tm) : ¬ Elabs S₀ (.var 2) .nat t := by
  intro h
  cases h with
  | var h => simp [Sig.varTy, ctxLookup, S₀] at h

/-! ## Examples: agreeing readers -/

/-- Positive: the system elaborator agrees with itself. -/
theorem agreeOnFull_refl : AgreeOnFull elabSys elabSys := fun _ _ _ => rfl
/-- Negative: the reader that never answers does not agree with it. -/
theorem not_agreeOnFull_none : ¬ AgreeOnFull elabSys (fun _ _ => none) := by
  intro h
  have := h S₀ (ppExplicit tTrunc) (by decide)
  revert this
  decide

/-! ## Examples: subtraction-annotated syntax -/

/-- Positive: explicit text annotates every subtraction. -/
example : (ppExplicit tTrunc).subAnnotated = true := by decide
/-- Positive: a text with an annotated `-` but an unannotated `=` and `+`. -/
example : (Stx.eq none (.add none (.sub (some .nat) (.var 0) (.var 1)) (.var 0)) (.var 2)).subAnnotated
    = true := by decide
/-- Negative: the default text `a - b = z` has an unannotated `-`. -/
example : (ppDefault tZ).subAnnotated = false := by decide

/-! ## Examples: the coercion-showing printer -/

/-- Positive: `ppCoercions` shows a coercion. -/
example : ppCoercions (.coe vA) = .coe (.var 0) := by decide
/-- Negative: `ppCoercions` does not show numeral types. -/
example : ppCoercions (.lit .int 2) = .num 2 := by decide

/-! ## Examples: a degenerate configuration -/

/-- A configuration whose numeral default is `Prop` (allowed by `ElabCfg`). -/
def cfgPropNumerals : ElabCfg := { numDefault := .prop, rule := .atOperator }

/-- Negative: under `cfgPropNumerals` an unconstrained numeral does not elaborate. -/
example : elabWith cfgPropNumerals S₀ (.num 2) = none := by decide
/-- Positive: an ascribed numeral still elaborates under `cfgPropNumerals`. -/
example : elabWith cfgPropNumerals S₀ (.asc (.num 2) .int) = some (.lit .int 2) := by decide

/-! ## Examples: what `DefaultRecoverable` rejects and admits -/

/-- `↑(2 : Nat) = z` at `Int`. -/
def tCoeTwoEqZ : Tm := .eq .int (.coe (.lit .nat 2)) vZ
/-- `↑((2 : Nat) - 3) = z` at `Int`. -/
def tCoeNumSub : Tm := .eq .int (.coe (.sub .nat (.lit .nat 2) (.lit .nat 3))) vZ
/-- `(2 : Int) + 3 = z` at `Int`. -/
def tAddIntNumEqZ : Tm := .eq .int (.add .int (.lit .int 2) (.lit .int 3)) vZ

/-- Negative: a coerced numeral is not default-recoverable, although the coerced
subterm has type `Nat` and meets an expected `Int`; its default text `2 = z` reads
back as `(2 : Int) = z`. -/
theorem not_defaultRecoverable_tCoeTwoEqZ :
    WellTyped S₀ tCoeTwoEqZ ∧ tyOf S₀ (.lit .nat 2) = some .nat ∧
      ¬ DefaultRecoverable S₀ tCoeTwoEqZ ∧
      elabSys S₀ (ppDefault tCoeTwoEqZ) = some (.eq .int (.lit .int 2) vZ) := by
  decide

/-- Negative: a coerced unannotated numeral subtraction is not default-recoverable;
its default text `2 - 3 = z` reads back as `(2 : Int) - 3 = z`, which differs in truth
at `ρ₀`. -/
theorem not_defaultRecoverable_tCoeNumSub :
    WellTyped S₀ tCoeNumSub ∧ tyOf S₀ (.sub .nat (.lit .nat 2) (.lit .nat 3)) = some .nat ∧
      ¬ DefaultRecoverable S₀ tCoeNumSub ∧
      elabSys S₀ (ppDefault tCoeNumSub) =
        some (.eq .int (.sub .int (.lit .int 2) (.lit .int 3)) vZ) ∧
      Denote S₀ tCoeNumSub ρ₀ ∧ ¬ Denote S₀ (.eq .int (.sub .int (.lit .int 2) (.lit .int 3)) vZ) ρ₀ := by
  decide

/-- Positive: an operator whose operand hints are both `none` takes the expected
type (`Int`, from the other side of `=`). -/
theorem defaultRecoverable_tAddIntNumEqZ :
    joinH (dh S₀ (.lit .int 2)) (dh S₀ (.lit .int 3)) = none ∧
      DefaultRecoverable S₀ tAddIntNumEqZ ∧
      elabSys S₀ (ppDefault tAddIntNumEqZ) = some tAddIntNumEqZ := by
  decide

end Toy.Render
