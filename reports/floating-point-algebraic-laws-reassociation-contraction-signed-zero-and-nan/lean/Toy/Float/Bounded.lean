/-
Toy.Float.Bounded
=================

Bounded instances of three general statements of `Toy.Float.Statements`
(`fma_nearest_of_fma_finite` and the two double-rounding statements), fully
proved by kernel evaluation (`decide +kernel`, no native code). They are
independent cross-checks in small formats; the general statements are proved
separately in `Toy.Float.Statements`. Each theorem states the exact format(s)
and operand range it covers (every operand of the named format).

* `fma_nearest_of_fma_finite_F22`: format `(2,2)` (15 values), all quadruples
  `(a, b, c, r)`.
* `addVia_eq_add_F33_W37`, `addVia_eq_add_F33_W38`: narrow format `(3,3)`
  (59 values), all pairs; wide formats `(3,7)` (`p' = 2p + 1`) and `(3,8)`
  (`p' = 2p + 2`).
* `mulVia_eq_mul_F33_W46`, `mulVia_eq_mul_F33_W38`: narrow `(3,3)`, all pairs;
  wide `(4,6)` (`p' = 2p`) and `(3,8)` (`p' = 2p + 2`).
* `mulVia_eq_mul_F34_W58`: narrow `(3,4)` (115 values), all pairs; wide
  `(5,8)` (`p' = 2p`).

Each exhaustive check is split into one kernel evaluation per biased exponent
of the first operand (`allAtExp`) plus one for its special values, so that no
single evaluation is large; `forall_of_allAtExp` recombines them.
-/
import Toy.Float.Check
import Toy.Float.Instances

namespace Toy.Float

/-! ### Contraction and accuracy -/

/-- Per-first-operand check for `fma_nearest_of_fma_finite_F22`. -/
def chkFmaNearestF22 (x : FP F22) : Bool :=
  (FP.list F22).all fun b => (FP.list F22).all fun c => (FP.list F22).all fun r =>
    (!(fma x b c).isFinite || decide (ErrLe (errOf (fma x b c) (exactMulAdd x b c)) (errOf r (exactMulAdd x b c))))

theorem chkFmaNearestF22_special :
    chkFmaNearestF22 .nan = true ∧ chkFmaNearestF22 (.inf false) = true ∧ chkFmaNearestF22 (.inf true) = true := by
  decide +kernel

theorem chkFmaNearestF22_E0 : allAtExp F22 ⟨0, by decide⟩ chkFmaNearestF22 = true := by
  decide +kernel

theorem chkFmaNearestF22_E1 : allAtExp F22 ⟨1, by decide⟩ chkFmaNearestF22 = true := by
  decide +kernel

theorem chkFmaNearestF22_E2 : allAtExp F22 ⟨2, by decide⟩ chkFmaNearestF22 = true := by
  decide +kernel

theorem chkFmaNearestF22_all : ∀ x : FP F22, chkFmaNearestF22 x = true :=
  forall_of_allAtExp chkFmaNearestF22 chkFmaNearestF22_special fun E =>
    match E with
    | ⟨0, _⟩ => chkFmaNearestF22_E0
    | ⟨1, _⟩ => chkFmaNearestF22_E1
    | ⟨2, _⟩ => chkFmaNearestF22_E2
    | ⟨n + 3, h⟩ => absurd h (by simp [F22, Fmt.expCount])

/-- [bounded: format F22 = (2,2), every `a`, `b`, `c`, `r`] -/
theorem fma_nearest_of_fma_finite_F22 :
    ∀ a b c : FP F22, (fma a b c).isFinite = true → ∀ r : FP F22,
      ErrLe (errOf (fma a b c) (exactMulAdd a b c)) (errOf r (exactMulAdd a b c)) := by
  intro a b c h r
  have h1 := (all_FP_list_iff _).mp (chkFmaNearestF22_all a) b
  have h2 := (all_FP_list_iff _).mp h1 c
  have h3 := (all_FP_list_iff _).mp h2 r
  simp only [h, Bool.not_true, Bool.false_or] at h3
  exact of_decide_eq_true h3

/-! ### Double rounding -/

/-- Per-first-operand check for `addVia_eq_add_F33_W37`. -/
def chk_addVia_eq_add_F33_W37 (x : FP F33) : Bool :=
  (FP.list F33).all fun y => decide (addVia W37 x y = add x y)

theorem chk_addVia_eq_add_F33_W37_special :
    chk_addVia_eq_add_F33_W37 .nan = true ∧ chk_addVia_eq_add_F33_W37 (.inf false) = true ∧ chk_addVia_eq_add_F33_W37 (.inf true) = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W37_E0 : allAtExp F33 ⟨0, by decide⟩ chk_addVia_eq_add_F33_W37 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W37_E1 : allAtExp F33 ⟨1, by decide⟩ chk_addVia_eq_add_F33_W37 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W37_E2 : allAtExp F33 ⟨2, by decide⟩ chk_addVia_eq_add_F33_W37 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W37_E3 : allAtExp F33 ⟨3, by decide⟩ chk_addVia_eq_add_F33_W37 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W37_E4 : allAtExp F33 ⟨4, by decide⟩ chk_addVia_eq_add_F33_W37 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W37_E5 : allAtExp F33 ⟨5, by decide⟩ chk_addVia_eq_add_F33_W37 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W37_E6 : allAtExp F33 ⟨6, by decide⟩ chk_addVia_eq_add_F33_W37 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W37_all : ∀ x : FP F33, chk_addVia_eq_add_F33_W37 x = true :=
  forall_of_allAtExp chk_addVia_eq_add_F33_W37 chk_addVia_eq_add_F33_W37_special fun E =>
    match E with
    | ⟨0, _⟩ => chk_addVia_eq_add_F33_W37_E0
    | ⟨1, _⟩ => chk_addVia_eq_add_F33_W37_E1
    | ⟨2, _⟩ => chk_addVia_eq_add_F33_W37_E2
    | ⟨3, _⟩ => chk_addVia_eq_add_F33_W37_E3
    | ⟨4, _⟩ => chk_addVia_eq_add_F33_W37_E4
    | ⟨5, _⟩ => chk_addVia_eq_add_F33_W37_E5
    | ⟨6, _⟩ => chk_addVia_eq_add_F33_W37_E6
    | ⟨n + 7, h⟩ => absurd h (by simp [F33, Fmt.expCount])

/-- [bounded: narrow F33 = (3,3), wide W37 = (3,7) (p' = 2p + 1), every pair] -/
theorem addVia_eq_add_F33_W37 :
    ∀ x y : FP F33, addVia W37 x y = add x y := by
  intro x y
  exact of_decide_eq_true ((all_FP_list_iff _).mp (chk_addVia_eq_add_F33_W37_all x) y)

/-- Per-first-operand check for `addVia_eq_add_F33_W38`. -/
def chk_addVia_eq_add_F33_W38 (x : FP F33) : Bool :=
  (FP.list F33).all fun y => decide (addVia W38 x y = add x y)

theorem chk_addVia_eq_add_F33_W38_special :
    chk_addVia_eq_add_F33_W38 .nan = true ∧ chk_addVia_eq_add_F33_W38 (.inf false) = true ∧ chk_addVia_eq_add_F33_W38 (.inf true) = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W38_E0 : allAtExp F33 ⟨0, by decide⟩ chk_addVia_eq_add_F33_W38 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W38_E1 : allAtExp F33 ⟨1, by decide⟩ chk_addVia_eq_add_F33_W38 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W38_E2 : allAtExp F33 ⟨2, by decide⟩ chk_addVia_eq_add_F33_W38 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W38_E3 : allAtExp F33 ⟨3, by decide⟩ chk_addVia_eq_add_F33_W38 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W38_E4 : allAtExp F33 ⟨4, by decide⟩ chk_addVia_eq_add_F33_W38 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W38_E5 : allAtExp F33 ⟨5, by decide⟩ chk_addVia_eq_add_F33_W38 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W38_E6 : allAtExp F33 ⟨6, by decide⟩ chk_addVia_eq_add_F33_W38 = true := by
  decide +kernel

theorem chk_addVia_eq_add_F33_W38_all : ∀ x : FP F33, chk_addVia_eq_add_F33_W38 x = true :=
  forall_of_allAtExp chk_addVia_eq_add_F33_W38 chk_addVia_eq_add_F33_W38_special fun E =>
    match E with
    | ⟨0, _⟩ => chk_addVia_eq_add_F33_W38_E0
    | ⟨1, _⟩ => chk_addVia_eq_add_F33_W38_E1
    | ⟨2, _⟩ => chk_addVia_eq_add_F33_W38_E2
    | ⟨3, _⟩ => chk_addVia_eq_add_F33_W38_E3
    | ⟨4, _⟩ => chk_addVia_eq_add_F33_W38_E4
    | ⟨5, _⟩ => chk_addVia_eq_add_F33_W38_E5
    | ⟨6, _⟩ => chk_addVia_eq_add_F33_W38_E6
    | ⟨n + 7, h⟩ => absurd h (by simp [F33, Fmt.expCount])

/-- [bounded: narrow F33 = (3,3), wide W38 = (3,8) (p' = 2p + 2), every pair] -/
theorem addVia_eq_add_F33_W38 :
    ∀ x y : FP F33, addVia W38 x y = add x y := by
  intro x y
  exact of_decide_eq_true ((all_FP_list_iff _).mp (chk_addVia_eq_add_F33_W38_all x) y)

/-- Per-first-operand check for `mulVia_eq_mul_F33_W46`. -/
def chk_mulVia_eq_mul_F33_W46 (x : FP F33) : Bool :=
  (FP.list F33).all fun y => decide (mulVia W46 x y = mul x y)

theorem chk_mulVia_eq_mul_F33_W46_special :
    chk_mulVia_eq_mul_F33_W46 .nan = true ∧ chk_mulVia_eq_mul_F33_W46 (.inf false) = true ∧ chk_mulVia_eq_mul_F33_W46 (.inf true) = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W46_E0 : allAtExp F33 ⟨0, by decide⟩ chk_mulVia_eq_mul_F33_W46 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W46_E1 : allAtExp F33 ⟨1, by decide⟩ chk_mulVia_eq_mul_F33_W46 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W46_E2 : allAtExp F33 ⟨2, by decide⟩ chk_mulVia_eq_mul_F33_W46 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W46_E3 : allAtExp F33 ⟨3, by decide⟩ chk_mulVia_eq_mul_F33_W46 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W46_E4 : allAtExp F33 ⟨4, by decide⟩ chk_mulVia_eq_mul_F33_W46 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W46_E5 : allAtExp F33 ⟨5, by decide⟩ chk_mulVia_eq_mul_F33_W46 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W46_E6 : allAtExp F33 ⟨6, by decide⟩ chk_mulVia_eq_mul_F33_W46 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W46_all : ∀ x : FP F33, chk_mulVia_eq_mul_F33_W46 x = true :=
  forall_of_allAtExp chk_mulVia_eq_mul_F33_W46 chk_mulVia_eq_mul_F33_W46_special fun E =>
    match E with
    | ⟨0, _⟩ => chk_mulVia_eq_mul_F33_W46_E0
    | ⟨1, _⟩ => chk_mulVia_eq_mul_F33_W46_E1
    | ⟨2, _⟩ => chk_mulVia_eq_mul_F33_W46_E2
    | ⟨3, _⟩ => chk_mulVia_eq_mul_F33_W46_E3
    | ⟨4, _⟩ => chk_mulVia_eq_mul_F33_W46_E4
    | ⟨5, _⟩ => chk_mulVia_eq_mul_F33_W46_E5
    | ⟨6, _⟩ => chk_mulVia_eq_mul_F33_W46_E6
    | ⟨n + 7, h⟩ => absurd h (by simp [F33, Fmt.expCount])

/-- [bounded: narrow F33 = (3,3), wide W46 = (4,6) (p' = 2p), every pair] -/
theorem mulVia_eq_mul_F33_W46 :
    ∀ x y : FP F33, mulVia W46 x y = mul x y := by
  intro x y
  exact of_decide_eq_true ((all_FP_list_iff _).mp (chk_mulVia_eq_mul_F33_W46_all x) y)

/-- Per-first-operand check for `mulVia_eq_mul_F33_W38`. -/
def chk_mulVia_eq_mul_F33_W38 (x : FP F33) : Bool :=
  (FP.list F33).all fun y => decide (mulVia W38 x y = mul x y)

theorem chk_mulVia_eq_mul_F33_W38_special :
    chk_mulVia_eq_mul_F33_W38 .nan = true ∧ chk_mulVia_eq_mul_F33_W38 (.inf false) = true ∧ chk_mulVia_eq_mul_F33_W38 (.inf true) = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W38_E0 : allAtExp F33 ⟨0, by decide⟩ chk_mulVia_eq_mul_F33_W38 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W38_E1 : allAtExp F33 ⟨1, by decide⟩ chk_mulVia_eq_mul_F33_W38 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W38_E2 : allAtExp F33 ⟨2, by decide⟩ chk_mulVia_eq_mul_F33_W38 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W38_E3 : allAtExp F33 ⟨3, by decide⟩ chk_mulVia_eq_mul_F33_W38 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W38_E4 : allAtExp F33 ⟨4, by decide⟩ chk_mulVia_eq_mul_F33_W38 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W38_E5 : allAtExp F33 ⟨5, by decide⟩ chk_mulVia_eq_mul_F33_W38 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W38_E6 : allAtExp F33 ⟨6, by decide⟩ chk_mulVia_eq_mul_F33_W38 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F33_W38_all : ∀ x : FP F33, chk_mulVia_eq_mul_F33_W38 x = true :=
  forall_of_allAtExp chk_mulVia_eq_mul_F33_W38 chk_mulVia_eq_mul_F33_W38_special fun E =>
    match E with
    | ⟨0, _⟩ => chk_mulVia_eq_mul_F33_W38_E0
    | ⟨1, _⟩ => chk_mulVia_eq_mul_F33_W38_E1
    | ⟨2, _⟩ => chk_mulVia_eq_mul_F33_W38_E2
    | ⟨3, _⟩ => chk_mulVia_eq_mul_F33_W38_E3
    | ⟨4, _⟩ => chk_mulVia_eq_mul_F33_W38_E4
    | ⟨5, _⟩ => chk_mulVia_eq_mul_F33_W38_E5
    | ⟨6, _⟩ => chk_mulVia_eq_mul_F33_W38_E6
    | ⟨n + 7, h⟩ => absurd h (by simp [F33, Fmt.expCount])

/-- [bounded: narrow F33 = (3,3), wide W38 = (3,8) (p' = 2p + 2), every pair] -/
theorem mulVia_eq_mul_F33_W38 :
    ∀ x y : FP F33, mulVia W38 x y = mul x y := by
  intro x y
  exact of_decide_eq_true ((all_FP_list_iff _).mp (chk_mulVia_eq_mul_F33_W38_all x) y)

/-- Per-first-operand check for `mulVia_eq_mul_F34_W58`. -/
def chk_mulVia_eq_mul_F34_W58 (x : FP F34) : Bool :=
  (FP.list F34).all fun y => decide (mulVia W58 x y = mul x y)

theorem chk_mulVia_eq_mul_F34_W58_special :
    chk_mulVia_eq_mul_F34_W58 .nan = true ∧ chk_mulVia_eq_mul_F34_W58 (.inf false) = true ∧ chk_mulVia_eq_mul_F34_W58 (.inf true) = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F34_W58_E0 : allAtExp F34 ⟨0, by decide⟩ chk_mulVia_eq_mul_F34_W58 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F34_W58_E1 : allAtExp F34 ⟨1, by decide⟩ chk_mulVia_eq_mul_F34_W58 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F34_W58_E2 : allAtExp F34 ⟨2, by decide⟩ chk_mulVia_eq_mul_F34_W58 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F34_W58_E3 : allAtExp F34 ⟨3, by decide⟩ chk_mulVia_eq_mul_F34_W58 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F34_W58_E4 : allAtExp F34 ⟨4, by decide⟩ chk_mulVia_eq_mul_F34_W58 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F34_W58_E5 : allAtExp F34 ⟨5, by decide⟩ chk_mulVia_eq_mul_F34_W58 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F34_W58_E6 : allAtExp F34 ⟨6, by decide⟩ chk_mulVia_eq_mul_F34_W58 = true := by
  decide +kernel

theorem chk_mulVia_eq_mul_F34_W58_all : ∀ x : FP F34, chk_mulVia_eq_mul_F34_W58 x = true :=
  forall_of_allAtExp chk_mulVia_eq_mul_F34_W58 chk_mulVia_eq_mul_F34_W58_special fun E =>
    match E with
    | ⟨0, _⟩ => chk_mulVia_eq_mul_F34_W58_E0
    | ⟨1, _⟩ => chk_mulVia_eq_mul_F34_W58_E1
    | ⟨2, _⟩ => chk_mulVia_eq_mul_F34_W58_E2
    | ⟨3, _⟩ => chk_mulVia_eq_mul_F34_W58_E3
    | ⟨4, _⟩ => chk_mulVia_eq_mul_F34_W58_E4
    | ⟨5, _⟩ => chk_mulVia_eq_mul_F34_W58_E5
    | ⟨6, _⟩ => chk_mulVia_eq_mul_F34_W58_E6
    | ⟨n + 7, h⟩ => absurd h (by simp [F34, Fmt.expCount])

/-- [bounded: narrow F34 = (3,4), wide W58 = (5,8) (p' = 2p), every pair] -/
theorem mulVia_eq_mul_F34_W58 :
    ∀ x y : FP F34, mulVia W58 x y = mul x y := by
  intro x y
  exact of_decide_eq_true ((all_FP_list_iff _).mp (chk_mulVia_eq_mul_F34_W58_all x) y)

end Toy.Float
