/-
Toy.AbsInt.Fixpoint
===================

Least fixpoints of concrete transformers (Knaster–Tarski on sets), transfer of
abstract post-fixpoints to concrete fixpoints, and termination of Kleene
iteration under the ascending chain condition or a height bound (cards
`R4-lfp-fix`, `R4-lfp-least`, `R4-transfer`, `R4-transfer-lfp`, `R4-kleene-acc`,
`R4-kleene-height`, `R4-kleene-bound`, `R4-height-acc`),
with definition examples, tightness counterexamples, non-vacuity witnesses and
boundary examples.

Terminology: for a map `h` on an ordered set, a *post-fixpoint* is a `z` with
`h z ≤ z`, on the concrete and on the abstract side alike (the convention of
Cousot & Cousot).  Several texts, e.g. Nipkow & Klein (Concrete Semantics,
Ch. 13), call the same condition a *pre-fixpoint*.
-/
import Toy.AbsInt.Transformer

namespace Toy.AbsInt

/-! ## Definitions -/

/-- The intersection (greatest lower bound) of all concrete post-fixpoints
`{x | f x ⊆ x}` of a transformer `f`, defined impredicatively.  The name reflects
the monotone case: for monotone `f` this is the least fixpoint and the least
post-fixpoint (Knaster 1928, Tarski 1955; card `R4-lfp-fix`).  For arbitrary `f`
it is still below every post-fixpoint (`lfp_le_of_le`), but it need not itself be
a post-fixpoint (`lfp_not_postFixpoint_of_not_monotone`) or a fixpoint
(`lfpEq_tight_monotone`), and it can be disjoint from the unique fixpoint of `f`
(`lfp_nonMonoUniqueFix_eq_empty`). -/
def lfp {σ : Type} (f : Pred σ → Pred σ) : Pred σ := fun s => ∀ x : Pred σ, f x ≤ x → x s

/-- `a` is a post-fixpoint of `fs`: `fs a ≤ a` (Cousot & Cousot's terminology;
Nipkow & Klein and several order-theory texts call the same condition a
pre-fixpoint).  In program-analysis terms, `a` is an inductive invariant.  Used
for abstract transformers; on `Pred σ` it is the condition `f x ⊆ x` that `lfp`
intersects over. -/
def PostFixpoint {A : Type} [LE A] (fs : A → A) (a : A) : Prop := fs a ≤ a

instance PostFixpoint.instDecidable {A : Type} [LE A] [∀ a b : A, Decidable (a ≤ b)]
    (fs : A → A) (a : A) : Decidable (PostFixpoint fs a) :=
  inferInstanceAs (Decidable (fs a ≤ a))

/-- Kleene iteration of `fs` from `a₀`: `a₀, fs a₀, fs (fs a₀), …`. -/
def kleene {A : Type} (fs : A → A) (a₀ : A) : Nat → A
  | 0 => a₀
  | n + 1 => fs (kleene fs a₀ n)

/-- `x` is the least fixpoint of the concrete transformer `f`: a fixpoint that is
included in every fixpoint.  Independent of the definition of `lfp`. -/
def IsLeastFixpoint {σ : Type} (f : Pred σ → Pred σ) (x : Pred σ) : Prop :=
  f x = x ∧ ∀ y, f y = y → x ≤ y

/-! ## Main results -/

section Main

/-- **Knaster–Tarski on predicates** (card `R4-lfp-fix`).  For a monotone
concrete transformer `f`, `lfp f` is a fixpoint: `f (lfp f) = lfp f`. -/
theorem lfp_eq_of_monotone {σ : Type} {f : Pred σ → Pred σ} (hf : Monotone f) :
    f (lfp f) = lfp f := by
  have hle : f (lfp f) ≤ lfp f := fun s hs x hx =>
    hx s (hf (lfp f) x (fun _ ht => ht x hx) s hs)
  have hge : lfp f ≤ f (lfp f) := fun _ hs => hs (f (lfp f)) (hf (f (lfp f)) (lfp f) hle)
  funext s
  exact propext ⟨hle s, hge s⟩

/-- **`lfp` is below every post-fixpoint** (card `R4-lfp-least`, a definitional
reference point).  For any `f` (monotonicity not needed) and any concrete
post-fixpoint `x` (`f x ⊆ x`), `lfp f ⊆ x`. -/
theorem lfp_le_of_le {σ : Type} (f : Pred σ → Pred σ) (x : Pred σ) (hx : f x ≤ x) :
    lfp f ≤ x :=
  fun _ hs => hs x hx

/-- **Transfer to the intersection of concrete post-fixpoints** (card
`R4-transfer`).  If `γ` is monotone and `fs` is `γ`-sound for `f`
(`f ∘ γ ⊆ γ ∘ fs`), then for every abstract post-fixpoint `a` (`fs a ≤ a`),
`lfp f ⊆ γ a` (the proof shows that `γ a` is a concrete post-fixpoint; that
intermediate fact is not part of the statement).  No abstraction
function, Galois connection, order law on `A`, or monotonicity of `f` or `fs` is
assumed.  `lfp f` is the intersection of all concrete post-fixpoints; it is
guaranteed to be the least fixpoint of `f` only when `f` is monotone (without
monotonicity it need not be a fixpoint; card `R4-transfer-lfp`).  For
non-monotone `f`, `γ a` can miss the unique fixpoint of `f`
(`transfer_misses_leastFixpoint_of_not_monotone`). -/
theorem lfp_le_gamma_of_monotone_gamma_of_sound_of_postFixpoint
    {σ A : Type} [LE A] {γ : A → Pred σ} {f : Pred σ → Pred σ} {fs : A → A}
    (hγ : Monotone γ) (hs : Sound γ f fs) {a : A} (ha : PostFixpoint fs a) :
    lfp f ≤ γ a :=
  fun _ h => h (γ a) (Pred.le_trans (hs a) (hγ _ _ ha))

/-- **Transfer to the concrete least fixpoint** (card `R4-transfer-lfp`).  If the
concrete transformer `f` is monotone, `γ` is monotone, `fs` is `γ`-sound for `f`,
and `a` is an abstract post-fixpoint, then `lfp f` is the least fixpoint of `f`,
and every least fixpoint of `f` is included in `γ a`.  Monotonicity of `f` cannot
be dropped (`lfpFixGamma_tight_monotone`). -/
theorem isLeastFixpoint_lfp_and_le_gamma_of_monotone_of_monotone_gamma_of_sound_of_postFixpoint
    {σ A : Type} [LE A] {γ : A → Pred σ} {f : Pred σ → Pred σ} {fs : A → A}
    (hf : Monotone f) (hγ : Monotone γ) (hs : Sound γ f fs) {a : A} (ha : PostFixpoint fs a) :
    IsLeastFixpoint f (lfp f) ∧ ∀ x, IsLeastFixpoint f x → x ≤ γ a := by
  have hfix : f (lfp f) = lfp f := lfp_eq_of_monotone hf
  have hleast : ∀ y, f y = y → lfp f ≤ y := fun y hy =>
    lfp_le_of_le f y (by rw [hy]; exact Pred.le_refl y)
  have htr : lfp f ≤ γ a := lfp_le_gamma_of_monotone_gamma_of_sound_of_postFixpoint hγ hs ha
  exact ⟨⟨hfix, hleast⟩, fun x hx => Pred.le_trans (hx.2 _ hfix) htr⟩

/-- **Kleene iteration under the ascending chain condition** (card
`R4-kleene-acc`).  If `fs` is monotone, the abstract order has no infinite
sequence of consecutive strict steps (`ACC`), and the start `a₀` satisfies
`a₀ ≤ fs a₀` (for instance, `a₀` is a least element), then some Kleene iterate
`kleene fs a₀ n` is a post-fixpoint of `fs`.  No reflexivity or transitivity of
the order is assumed. -/
theorem exists_kleene_postFixpoint_of_monotone_of_acc_of_le_apply
    {A : Type} [LE A] {fs : A → A} (hmono : Monotone fs) (hacc : ACC A)
    (a₀ : A) (hstart : a₀ ≤ fs a₀) :
    ∃ n, PostFixpoint fs (kleene fs a₀ n) := by
  have hasc : ∀ n, kleene fs a₀ n ≤ kleene fs a₀ (n + 1) := by
    intro n; induction n with
    | zero => exact hstart
    | succ _ ih => exact hmono _ _ ih
  exact Classical.byContradiction fun hne =>
    hacc ⟨kleene fs a₀, fun n => ⟨hasc n, fun hp => hne ⟨n, hp⟩⟩⟩

/-- **Kleene iteration under a height bound** (card `R4-kleene-height`).  If `fs`
is monotone, the abstract order has height at most `h`, and `a₀ ≤ fs a₀`, then
some Kleene iterate `kleene fs a₀ n` with `n ≤ h` is a post-fixpoint of `fs`. -/
theorem exists_kleene_postFixpoint_le_of_monotone_of_heightLE_of_le_apply
    {A : Type} [LE A] {fs : A → A} (hmono : Monotone fs) (h : Nat) (hh : HeightLE A h)
    (a₀ : A) (hstart : a₀ ≤ fs a₀) :
    ∃ n, n ≤ h ∧ PostFixpoint fs (kleene fs a₀ n) := by
  have hasc : ∀ n, kleene fs a₀ n ≤ kleene fs a₀ (n + 1) := by
    intro n; induction n with
    | zero => exact hstart
    | succ _ ih => exact hmono _ _ ih
  exact Classical.byContradiction fun hne =>
    Nat.not_succ_le_self h (hh (kleene fs a₀) (h + 1) fun i hi =>
      ⟨hasc i, fun hp => hne ⟨i, Nat.le_of_lt_succ hi, hp⟩⟩)

/-- **Finite height implies the ascending chain condition** (card
`R4-height-acc`, an auxiliary bridge: it lets `R4-kleene-acc` and
`widenTerminates_of_acc` be applied to domains of finite height). -/
theorem acc_of_heightLE {A : Type} [LE A] (h : Nat) (hh : HeightLE A h) : ACC A :=
  fun ⟨c, hc⟩ => Nat.not_succ_le_self h (hh c (h + 1) fun i _ => hc i)

end Main

/-! ## Fixtures -/

/-- Concrete transformer of the loop `x := 0; while * do x := x + 1` on a
natural-number variable: `f x = {0} ∪ {m + 1 | m ∈ x}`.  Its least fixpoint is
the set of all naturals. -/
def counterStep (x : Pred Nat) : Pred Nat := fun n => n = 0 ∨ ∃ m, x m ∧ n = m + 1

theorem counterStep_monotone : Monotone counterStep := by
  intro x y hxy n hn
  rcases hn with h | ⟨m, hm, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, hxy m hm, he⟩

/-- Every natural number is in `lfp counterStep` (proved from the definition). -/
theorem lfp_counterStep (k : Nat) : lfp counterStep k := by
  intro x hx
  induction k with
  | zero => exact hx 0 (Or.inl rfl)
  | succ k ih => exact hx (k + 1) (Or.inr ⟨k, ih, rfl⟩)

/-- Abstract transformer of the counter loop body on `UB`. -/
def ubIncr : UB → UB
  | .bot => .atMost 0
  | .atMost n => .atMost (n + 1)
  | .top => .top

theorem ubIncr_monotone : Monotone ubIncr := by
  intro a b hab
  cases a <;> cases b <;> simp_all [ubIncr]

theorem ubIncr_sound : Sound ubGamma counterStep ubIncr := by
  intro a n hn
  cases a with
  | bot =>
    rcases hn with h | ⟨m, hm, _⟩
    · show n ≤ 0; omega
    · exact hm.elim
  | atMost k =>
    rcases hn with h | ⟨m, hm, he⟩
    · show n ≤ k + 1; omega
    · have : m ≤ k := hm
      show n ≤ k + 1; omega
  | top => trivial

theorem kleene_ubIncr_succ (n : Nat) : kleene ubIncr UB.bot (n + 1) = UB.atMost n := by
  induction n with
  | zero => rfl
  | succ n ih => show ubIncr (kleene ubIncr UB.bot (n + 1)) = _; rw [ih]; rfl

theorem kleene_ubIncr_not_postFixpoint (n : Nat) :
    ¬ PostFixpoint ubIncr (kleene ubIncr UB.bot n) := by
  cases n with
  | zero => exact UB.not_atMost_le_bot 0
  | succ n =>
    rw [kleene_ubIncr_succ]
    show ¬ (UB.atMost (n + 1) ≤ UB.atMost n)
    simp

theorem UB.not_heightLE (h : Nat) : ¬ HeightLE UB h := by
  intro hh
  have := hh (fun i => UB.atMost i) (h + 1) (fun i _ => by simp [StrictLt])
  omega

/-- A Kleene-iteration fixture on `V3`: `bot ↦ x ↦ y ↦ x`, not monotone, with
no post-fixpoint at all. -/
def v3Step : V3 → V3
  | .bot => .x
  | .x => .y
  | .y => .x

theorem v3Step_no_postFixpoint (a : V3) : ¬ PostFixpoint v3Step a := by
  cases a <;> decide

/-- The swap on the discrete `Dis2`: monotone, with no post-fixpoint. -/
def dis2Swap : Dis2 → Dis2
  | .a => .b
  | .b => .a

theorem dis2Swap_monotone : Monotone dis2Swap := by
  intro x y hxy; cases x <;> cases y <;> first | decide | exact absurd hxy (by decide)

theorem dis2Swap_no_postFixpoint (x : Dis2) : ¬ PostFixpoint dis2Swap x := by
  cases x <;> decide

/-- A monotone abstract transformer on `Sign`: the loop `x := 0; while * do
x := x + 1` abstracted as `bot ↦ zero`, everything else `↦ top`. -/
def signLoop : Sign → Sign
  | .bot => .zero
  | _ => .top

theorem signLoop_monotone : Monotone signLoop := by
  intro a b hab; cases a <;> cases b <;> first | decide | exact absurd hab (by decide)

/-- A capped successor on `Fin (h + 1)` (the chain `0 < 1 < … < h`). -/
def capSucc (h : Nat) (i : Fin (h + 1)) : Fin (h + 1) :=
  ⟨min (i.val + 1) h, by omega⟩

def capZero (h : Nat) : Fin (h + 1) := ⟨0, by omega⟩

theorem kleene_capSucc_val (h n : Nat) : (kleene (capSucc h) (capZero h) n).val = min n h := by
  induction n with
  | zero => show 0 = min 0 h; omega
  | succ n ih =>
    show min ((kleene (capSucc h) (capZero h) n).val + 1) h = min (n + 1) h
    rw [ih]; omega

/-- Concrete transformer of the loop `x := 1; while * do x := x + 1` on an integer
variable: `f x = {1} ∪ {m + 1 | m ∈ x}`.  Its least fixpoint is the set of
positive integers. -/
def posLoop (x : Pred Int) : Pred Int := fun n => n = 1 ∨ ∃ m, x m ∧ n = m + 1

theorem posLoop_monotone : Monotone posLoop := by
  intro x y hxy n hn
  rcases hn with h | ⟨m, hm, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨m, hxy m hm, he⟩

/-- Abstract transformer of that loop on `Sign`: `bot ↦ pos`, `pos ↦ pos`,
everything else `↦ top`. -/
def signPosLoop : Sign → Sign
  | .bot => .pos
  | .pos => .pos
  | _ => .top

theorem signPosLoop_sound : Sound signGamma posLoop signPosLoop := by
  intro a n hn
  cases a with
  | bot =>
    rcases hn with rfl | ⟨_, hm, _⟩
    · show (0 : Int) < 1; omega
    · exact hm.elim
  | pos =>
    rcases hn with rfl | ⟨m, hm, rfl⟩
    · show (0 : Int) < 1; omega
    · have : (0 : Int) < m := hm
      show (0 : Int) < m + 1; omega
  | neg => trivial
  | zero => trivial
  | top => trivial

/-- The predicates `{true}` and `{false}` on `Bool`. -/
def pTrue : Pred Bool := fun b => b = true
def pFalse : Pred Bool := fun b => b = false

/-- A non-monotone transformer on `Pred Bool`: `∅ ↦ univ`, `{false} ↦ ∅`,
`{true} ↦ {true}`, `univ ↦ ∅`.  Its unique fixpoint is `{true}`. -/
def nonMonoUniqueFix (x : Pred Bool) : Pred Bool :=
  fun b => (x true ∧ ¬ x false ∧ b = true) ∨ (¬ x false ∧ ¬ x true)

theorem nonMonoUniqueFix_empty : nonMonoUniqueFix (Pred.empty Bool) = Pred.univ Bool := by
  funext b; exact propext ⟨fun _ => trivial, fun _ => Or.inr ⟨fun h => h, fun h => h⟩⟩

theorem nonMonoUniqueFix_pFalse : nonMonoUniqueFix pFalse = Pred.empty Bool := by
  funext b
  refine propext ⟨fun h => ?_, fun h => h.elim⟩
  rcases h with ⟨_, hnf, _⟩ | ⟨hnf, _⟩ <;> exact hnf rfl

theorem nonMonoUniqueFix_pTrue : nonMonoUniqueFix pTrue = pTrue := by
  funext b
  refine propext ⟨fun h => ?_, fun hb => Or.inl ⟨rfl, Bool.noConfusion, hb⟩⟩
  rcases h with ⟨_, _, hb⟩ | ⟨_, hnt⟩
  · exact hb
  · exact (hnt rfl).elim

theorem nonMonoUniqueFix_not_monotone : ¬ Monotone nonMonoUniqueFix := by
  intro h
  have h1 := h _ _ (E_le pFalse) true (Or.inr ⟨fun c => c, fun c => c⟩)
  rw [nonMonoUniqueFix_pFalse] at h1
  exact h1

/-- `{true}` is the unique fixpoint of `nonMonoUniqueFix`. -/
theorem nonMonoUniqueFix_unique_fixpoint (x : Pred Bool) :
    nonMonoUniqueFix x = x ↔ x = pTrue := by
  constructor
  · intro hfix
    have hfx : ∀ b, nonMonoUniqueFix x b ↔ x b := fun b => by rw [hfix]
    by_cases hf : x false
    · have hbad : nonMonoUniqueFix x false := (hfx false).mpr hf
      rcases hbad with ⟨_, hnf, _⟩ | ⟨hnf, _⟩ <;> exact (hnf hf).elim
    · by_cases ht : x true
      · funext b
        cases b
        · exact propext ⟨fun h => (hf h).elim, Bool.noConfusion⟩
        · exact propext ⟨fun _ => rfl, fun _ => ht⟩
      · have hbad : x false := (hfx false).mp (Or.inr ⟨hf, ht⟩)
        exact (hf hbad).elim
  · intro hx; rw [hx]; exact nonMonoUniqueFix_pTrue

theorem isLeastFixpoint_nonMonoUniqueFix_pTrue : IsLeastFixpoint nonMonoUniqueFix pTrue :=
  ⟨nonMonoUniqueFix_pTrue, fun y hy => by
    rw [(nonMonoUniqueFix_unique_fixpoint y).mp hy]; exact Pred.le_refl _⟩

/-- `lfp nonMonoUniqueFix = ∅`, although `{true}` is the unique fixpoint. -/
theorem lfp_nonMonoUniqueFix_eq_empty : lfp nonMonoUniqueFix = Pred.empty Bool := by
  funext b
  refine propext ⟨fun h => ?_, fun h => h.elim⟩
  have hF : nonMonoUniqueFix pFalse ≤ pFalse := by
    rw [nonMonoUniqueFix_pFalse]; exact E_le pFalse
  have hT : nonMonoUniqueFix pTrue ≤ pTrue := by
    rw [nonMonoUniqueFix_pTrue]; exact Pred.le_refl pTrue
  have hbF : pFalse b := h pFalse hF
  have hbT : pTrue b := h pTrue hT
  cases b
  · exact Bool.noConfusion hbT
  · exact Bool.noConfusion hbF

/-- The constant-full transformer on `Pred Unit` has `{()}` as its least fixpoint. -/
theorem isLeastFixpoint_constU : IsLeastFixpoint (fun _ : Pred Unit => U) U :=
  ⟨rfl, fun y hy => by
    have h : U = y := hy
    rw [← h]; exact Pred.le_refl U⟩

/-- A strict cycle on `Cyc3`: `c0, c1, c2, c0, …`. -/
def cyc3Chain : Nat → Cyc3
  | 0 => .c0
  | n + 1 => (cyc3Chain n).next

/-- The sequence `(0, false), (0, true), (1, false), (1, true), …` in `NB`. -/
def nbChain (n : Nat) : NB := NB.mk (n / 2) (n % 2 == 1)

/-! ## Definition examples (proved) -/

theorem lfp_example_pos : ∀ k, lfp counterStep k := lfp_counterStep

/-- Negative example: the least fixpoint of the constant-`∅` transformer
contains nothing (`∅` is a post-fixpoint). -/
theorem lfp_example_neg : ¬ lfp (fun _ => Pred.empty Nat) 0 :=
  fun h => h (Pred.empty Nat) (fun _ h => h)

theorem postFixpoint_example_pos : PostFixpoint ubIncr UB.top := UB.le_top _

theorem postFixpoint_example_neg : ¬ PostFixpoint ubIncr (UB.atMost 0) := by
  show ¬ (UB.atMost 1 ≤ UB.atMost 0); simp

theorem kleene_example_pos : kleene ubIncr UB.bot 3 = UB.atMost 2 := rfl

theorem kleene_example_neg : kleene ubIncr UB.bot 3 ≠ UB.top := by decide

theorem acc_example_pos : ACC Sign := Sign.acc
theorem acc_example_neg : ¬ ACC UB := UB.not_acc

theorem heightLE_example_pos : HeightLE Sign 2 := Sign.heightLE

/-- Negative example: the sign domain does not have height `≤ 1`
(`bot < neg < top`). -/
theorem heightLE_example_neg : ¬ HeightLE Sign 1 := by
  intro hh
  have := hh (fun | 0 => .bot | 1 => .neg | _ => .top) 2 (by
    intro i hi
    match i, hi with
    | 0, _ => decide
    | 1, _ => decide)
  omega

theorem isBot_example_pos : IsBot Sign.bot := fun a => by cases a <;> decide
theorem isBot_example_neg : ¬ IsBot Sign.neg := fun h => absurd (h .zero) (by decide)

theorem strictLt_example_pos : StrictLt Sign.bot Sign.neg := by decide
theorem strictLt_example_neg : ¬ StrictLt Sign.neg Sign.zero := by decide

theorem isAntisymm_example_pos : IsAntisymm Sign := Sign.isAntisymm

/-- Negative example: the two-element total preorder `E2` (reflexive and
transitive) is not antisymmetric. -/
theorem isAntisymm_example_neg : IsRefl E2 ∧ IsTrans E2 ∧ ¬ IsAntisymm E2 :=
  ⟨E2.isRefl, E2.isTrans, E2.not_isAntisymm⟩

/-- A further negative example on a relation that is not transitive either. -/
theorem isAntisymm_example_neg_nonTrans : ¬ IsAntisymm NT4w :=
  fun h => absurd (h .bot .u (by decide) (by decide)) (by decide)

theorem posLoop_example_pos : posLoop (Pred.empty Int) 1 := Or.inl rfl

/-- Negative example: from the empty set, one step of the loop reaches only `1`. -/
theorem posLoop_example_neg : ¬ posLoop (Pred.empty Int) 2 := by
  intro h
  rcases h with h | ⟨_, hm, _⟩
  · omega
  · exact hm

theorem signPosLoop_example_pos : PostFixpoint signPosLoop Sign.pos := by decide

/-- Negative example: `zero` is not a post-fixpoint of `signPosLoop`. -/
theorem signPosLoop_example_neg : ¬ PostFixpoint signPosLoop Sign.zero := by decide

theorem isLeastFixpoint_example_pos : IsLeastFixpoint (fun _ : Pred Unit => U) U :=
  isLeastFixpoint_constU

/-- Negative example: `{()}` is a fixpoint of the identity but not its least
fixpoint (`∅` is a smaller one). -/
theorem isLeastFixpoint_example_neg : ¬ IsLeastFixpoint (id : Pred Unit → Pred Unit) U :=
  fun ⟨_, h⟩ => not_U_le_E (h E rfl)

/-! ## Non-vacuity witnesses (proved) -/

theorem lfpEq_nonvacuous : Monotone counterStep := counterStep_monotone

theorem lfpLe_nonvacuous : counterStep (Pred.univ Nat) ≤ Pred.univ Nat := le_U _

/-- Non-vacuity for `R4-transfer`: the sign domain with the loop
`x := 1; while * do x := x + 1` and the post-fixpoint `pos`, whose
concretization is not the full set (it excludes `0`). -/
theorem lfpGamma_nonvacuous :
    Monotone signGamma ∧ Sound signGamma posLoop signPosLoop ∧
      PostFixpoint signPosLoop Sign.pos ∧ ¬ signGamma Sign.pos 0 :=
  ⟨signGamma_monotone, signPosLoop_sound, by decide, by show ¬ (0 : Int) < 0; omega⟩

/-- Non-vacuity for `R4-transfer-lfp`: the same instance, with the monotone
concrete transformer `posLoop`. -/
theorem lfpFixGamma_nonvacuous :
    Monotone posLoop ∧ Monotone signGamma ∧ Sound signGamma posLoop signPosLoop ∧
      PostFixpoint signPosLoop Sign.pos ∧ ¬ signGamma Sign.pos 0 :=
  ⟨posLoop_monotone, signGamma_monotone, signPosLoop_sound, by decide,
    by show ¬ (0 : Int) < 0; omega⟩

theorem kleeneAcc_nonvacuous :
    Monotone signLoop ∧ ACC Sign ∧ Sign.bot ≤ signLoop Sign.bot :=
  ⟨signLoop_monotone, Sign.acc, by decide⟩

theorem kleeneHeight_nonvacuous :
    Monotone signLoop ∧ HeightLE Sign 2 ∧ Sign.bot ≤ signLoop Sign.bot :=
  ⟨signLoop_monotone, Sign.heightLE, by decide⟩

theorem accOfHeight_nonvacuous : HeightLE Sign 2 := Sign.heightLE

/-! ## Tightness counterexamples (proved) -/

/-- `R4-lfp-fix` needs monotonicity: for the complement on `Pred Unit`, `lfp` is the
full set but its image is empty, so it is not a fixpoint. -/
theorem lfpEq_tight_monotone :
    ¬ Monotone (@compl Unit) ∧ ¬ (@compl Unit (lfp (@compl Unit)) = lfp (@compl Unit)) := by
  have hl : lfp (@compl Unit) () := by
    intro x hx
    exact Classical.byContradiction fun hn => hn (hx () hn)
  refine ⟨fun h => h E U (le_U E) () (fun h' => h') trivial, ?_⟩
  intro heq
  have h2 : @compl Unit (lfp (@compl Unit)) () := by rw [heq]; exact hl
  exact h2 hl

/-- `R4-lfp-least` needs the post-fixpoint hypothesis: `∅` is not a post-fixpoint
of `counterStep`, and `lfp counterStep` is not contained in it. -/
theorem lfpLe_tight_postFixpoint :
    ¬ (counterStep (Pred.empty Nat) ≤ Pred.empty Nat) ∧ ¬ (lfp counterStep ≤ Pred.empty Nat) :=
  ⟨fun h => h 0 (Or.inl rfl), fun h => h 0 (lfp_counterStep 0)⟩

/-- `R4-transfer` needs monotone `γ`: with the order-reversing `b2GammaRev`, the
constant-full transformer, the constant-`lo` abstract transformer (sound) and
the post-fixpoint `hi`. -/
theorem lfpGamma_tight_monoGamma :
    Sound b2GammaRev (fun _ => U) (fun _ => B2.lo) ∧ PostFixpoint (fun _ : B2 => B2.lo) B2.hi ∧
      ¬ Monotone b2GammaRev ∧ ¬ (lfp (fun _ : Pred Unit => U) ≤ b2GammaRev B2.hi) :=
  ⟨fun _ => Pred.le_refl _, by decide, b2GammaRev_not_monotone,
    fun h => h () (fun x hx => hx () trivial)⟩

/-- `R4-transfer` needs soundness: with the monotone `b2Gamma`, the constant-full
transformer and the (unsound) identity abstract transformer, `lo` is a
post-fixpoint but `lfp ⊄ γ lo = ∅`. -/
theorem lfpGamma_tight_sound :
    Monotone b2Gamma ∧ PostFixpoint (id : B2 → B2) B2.lo ∧
      ¬ Sound b2Gamma (fun _ => U) id ∧ ¬ (lfp (fun _ : Pred Unit => U) ≤ b2Gamma B2.lo) :=
  ⟨b2Gamma_monotone, by decide, fun h => not_U_le_E (h B2.lo),
    fun h => h () (fun x hx => hx () trivial)⟩

/-- `R4-transfer` needs the post-fixpoint hypothesis: `lo` is not a post-fixpoint
of the (sound) constant-`hi` transformer, and `lfp ⊄ γ lo`. -/
theorem lfpGamma_tight_postFixpoint :
    Monotone b2Gamma ∧ Sound b2Gamma (fun _ => U) (fun _ => B2.hi) ∧
      ¬ PostFixpoint (fun _ : B2 => B2.hi) B2.lo ∧
      ¬ (lfp (fun _ : Pred Unit => U) ≤ b2Gamma B2.lo) :=
  ⟨b2Gamma_monotone, fun _ => Pred.le_refl _, by decide,
    fun h => h () (fun x hx => hx () trivial)⟩

/-- `R4-kleene-acc` needs monotone `fs`: `v3Step` on the finite `V3`. -/
theorem kleeneAcc_tight_monotone :
    ACC V3 ∧ V3.bot ≤ v3Step V3.bot ∧ ¬ Monotone v3Step ∧
      ∀ n, ¬ PostFixpoint v3Step (kleene v3Step V3.bot n) :=
  ⟨V3.acc, by decide, fun h => absurd (h .bot .x (by decide)) (by decide),
    fun n => v3Step_no_postFixpoint _⟩

/-- `R4-kleene-acc` needs the ascending chain condition: on `UB`, Kleene
iteration of the monotone `ubIncr` from `bot` never reaches a post-fixpoint
(although `top` is one). -/
theorem kleeneAcc_tight_acc :
    Monotone ubIncr ∧ UB.bot ≤ ubIncr UB.bot ∧ ¬ ACC UB ∧ PostFixpoint ubIncr UB.top ∧
      ∀ n, ¬ PostFixpoint ubIncr (kleene ubIncr UB.bot n) :=
  ⟨ubIncr_monotone, UB.bot_le _, UB.not_acc, UB.le_top _, kleene_ubIncr_not_postFixpoint⟩

/-- `R4-kleene-acc` needs `a₀ ≤ fs a₀`: the swap on the discrete `Dis2`. -/
theorem kleeneAcc_tight_start :
    Monotone dis2Swap ∧ ACC Dis2 ∧ ¬ (Dis2.a ≤ dis2Swap Dis2.a) ∧
      ∀ n, ¬ PostFixpoint dis2Swap (kleene dis2Swap Dis2.a n) :=
  ⟨dis2Swap_monotone, Dis2.acc, by decide, fun n => dis2Swap_no_postFixpoint _⟩

/-- `R4-kleene-height` needs monotone `fs` (`V3` has height `1`). -/
theorem kleeneHeight_tight_monotone :
    HeightLE V3 1 ∧ V3.bot ≤ v3Step V3.bot ∧ ¬ Monotone v3Step ∧
      ¬ ∃ n, n ≤ 1 ∧ PostFixpoint v3Step (kleene v3Step V3.bot n) :=
  ⟨V3.heightLE, by decide, kleeneAcc_tight_monotone.2.2.1,
    fun ⟨_, _, hp⟩ => v3Step_no_postFixpoint _ hp⟩

/-- `R4-kleene-height` needs `a₀ ≤ fs a₀` (`Dis2` has height `0`). -/
theorem kleeneHeight_tight_start :
    Monotone dis2Swap ∧ HeightLE Dis2 0 ∧ ¬ (Dis2.a ≤ dis2Swap Dis2.a) ∧
      ¬ ∃ n, n ≤ 0 ∧ PostFixpoint dis2Swap (kleene dis2Swap Dis2.a n) :=
  ⟨dis2Swap_monotone, Dis2.heightLE, by decide,
    fun ⟨_, _, hp⟩ => dis2Swap_no_postFixpoint _ hp⟩

/-- `R4-kleene-height` needs a height bound: on `UB` (no height bound), for every
`h` no Kleene iterate with index `≤ h` is a post-fixpoint. -/
theorem kleeneHeight_tight_height :
    Monotone ubIncr ∧ UB.bot ≤ ubIncr UB.bot ∧
      ∀ h, ¬ HeightLE UB h ∧ ¬ ∃ n, n ≤ h ∧ PostFixpoint ubIncr (kleene ubIncr UB.bot n) :=
  ⟨ubIncr_monotone, UB.bot_le _,
    fun h => ⟨UB.not_heightLE h, fun ⟨n, _, hp⟩ => kleene_ubIncr_not_postFixpoint n hp⟩⟩

/-- **The height bound is attained** (card `R4-kleene-bound`).  The bound `n ≤ h`
of `R4-kleene-height` is attained: on the chain
`Fin (h + 1)` (height `h`) with the capped successor, every hypothesis holds,
the `h`-th iterate is a post-fixpoint, and no earlier iterate is. -/
theorem kleeneHeight_bound_attained (h : Nat) :
    HeightLE (Fin (h + 1)) h ∧ Monotone (capSucc h) ∧ capZero h ≤ capSucc h (capZero h) ∧
      PostFixpoint (capSucc h) (kleene (capSucc h) (capZero h) h) ∧
      ∀ n, n < h → ¬ PostFixpoint (capSucc h) (kleene (capSucc h) (capZero h) n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine heightLE_of_rank (fun i => i.val) h ?_ (fun i => by have := i.isLt; omega)
    intro a b hab
    have h1 : a.val ≤ b.val := hab.1
    have h2 : ¬ b.val ≤ a.val := hab.2
    omega
  · intro a b hab
    have : a.val ≤ b.val := hab
    show min (a.val + 1) h ≤ min (b.val + 1) h
    omega
  · show 0 ≤ min (0 + 1) h; omega
  · show (capSucc h (kleene (capSucc h) (capZero h) h)).val ≤ (kleene (capSucc h) (capZero h) h).val
    show min ((kleene (capSucc h) (capZero h) h).val + 1) h ≤ _
    rw [kleene_capSucc_val]; omega
  · intro n hn hp
    have : (capSucc h (kleene (capSucc h) (capZero h) n)).val ≤
        (kleene (capSucc h) (capZero h) n).val := hp
    change min ((kleene (capSucc h) (capZero h) n).val + 1) h ≤ _ at this
    rw [kleene_capSucc_val] at this
    omega

/-- The top element `h` of the chain `Fin (h + 1)`. -/
def capTop (h : Nat) : Fin (h + 1) := ⟨h, by omega⟩

/-- **Positive control for `R4-kleene-bound`.**  On the same chain `Fin (h + 1)`
with the same capped successor, but starting from the top element `h` instead of
`0`, every hypothesis of `R4-kleene-height` still holds, and for `h ≥ 1` an iterate
with index `n < h` (namely `n = 0`) is already a post-fixpoint: the worst case of
`h` iterations depends on the start. -/
theorem kleeneHeight_bound_not_attained_from_top (h : Nat) (hpos : 0 < h) :
    HeightLE (Fin (h + 1)) h ∧ Monotone (capSucc h) ∧ capTop h ≤ capSucc h (capTop h) ∧
      ∃ n, n < h ∧ PostFixpoint (capSucc h) (kleene (capSucc h) (capTop h) n) := by
  refine ⟨(kleeneHeight_bound_attained h).1, (kleeneHeight_bound_attained h).2.1, ?_,
    ⟨0, hpos, ?_⟩⟩
  · show h ≤ min (h + 1) h; omega
  · show min (h + 1) h ≤ h; omega

/-- `R4-height-acc`: its premise cannot be dropped — `UB` has no height bound and
violates the ascending chain condition. -/
theorem accOfHeight_tight : ¬ ACC UB ∧ ∀ h, ¬ HeightLE UB h :=
  ⟨UB.not_acc, UB.not_heightLE⟩

/-- `R4-transfer-lfp` needs monotone `f`: with the exact abstraction `γ = id` on
`Pred Bool` and the non-monotone `nonMonoUniqueFix`, every other hypothesis holds
at `a = {false}`, but `{true}` is the least (indeed unique) fixpoint and is not
included in `γ a`; moreover `lfp f = ∅` is not a fixpoint. -/
theorem lfpFixGamma_tight_monotone :
    ¬ Monotone nonMonoUniqueFix ∧ Monotone (id : Pred Bool → Pred Bool) ∧
      Sound (id : Pred Bool → Pred Bool) nonMonoUniqueFix nonMonoUniqueFix ∧
      PostFixpoint nonMonoUniqueFix pFalse ∧
      ¬ (IsLeastFixpoint nonMonoUniqueFix (lfp nonMonoUniqueFix) ∧
          ∀ x, IsLeastFixpoint nonMonoUniqueFix x → x ≤ id pFalse) ∧
      IsLeastFixpoint nonMonoUniqueFix pTrue ∧ ¬ (pTrue ≤ id pFalse) ∧
      ¬ IsLeastFixpoint nonMonoUniqueFix (lfp nonMonoUniqueFix) := by
  have hpf : PostFixpoint nonMonoUniqueFix pFalse := by
    show nonMonoUniqueFix pFalse ≤ pFalse
    rw [nonMonoUniqueFix_pFalse]; exact E_le pFalse
  have hmiss : ¬ (pTrue ≤ id pFalse) := fun h => Bool.noConfusion (h true rfl)
  have hnotfix : ¬ IsLeastFixpoint nonMonoUniqueFix (lfp nonMonoUniqueFix) := by
    intro ⟨hfix, _⟩
    rw [lfp_nonMonoUniqueFix_eq_empty, nonMonoUniqueFix_empty] at hfix
    have : Pred.univ Bool true := trivial
    rw [hfix] at this
    exact this
  refine ⟨nonMonoUniqueFix_not_monotone, fun _ _ h => h, fun _ => Pred.le_refl _, hpf,
    fun ⟨_, h⟩ => hmiss (h pTrue isLeastFixpoint_nonMonoUniqueFix_pTrue),
    isLeastFixpoint_nonMonoUniqueFix_pTrue, hmiss, hnotfix⟩

/-- `R4-transfer-lfp` needs monotone `γ` (instance of `lfpGamma_tight_monoGamma`). -/
theorem lfpFixGamma_tight_monoGamma :
    Monotone (fun _ : Pred Unit => U) ∧ ¬ Monotone b2GammaRev ∧
      Sound b2GammaRev (fun _ => U) (fun _ => B2.lo) ∧ PostFixpoint (fun _ : B2 => B2.lo) B2.hi ∧
      ¬ (IsLeastFixpoint (fun _ : Pred Unit => U) (lfp (fun _ : Pred Unit => U)) ∧
          ∀ x, IsLeastFixpoint (fun _ : Pred Unit => U) x → x ≤ b2GammaRev B2.hi) :=
  ⟨fun _ _ _ => Pred.le_refl _, b2GammaRev_not_monotone, fun _ => Pred.le_refl _, by decide,
    fun ⟨_, h⟩ => not_U_le_E (h U isLeastFixpoint_constU)⟩

/-- `R4-transfer-lfp` needs soundness (instance of `lfpGamma_tight_sound`). -/
theorem lfpFixGamma_tight_sound :
    Monotone (fun _ : Pred Unit => U) ∧ Monotone b2Gamma ∧ PostFixpoint (id : B2 → B2) B2.lo ∧
      ¬ Sound b2Gamma (fun _ => U) id ∧
      ¬ (IsLeastFixpoint (fun _ : Pred Unit => U) (lfp (fun _ : Pred Unit => U)) ∧
          ∀ x, IsLeastFixpoint (fun _ : Pred Unit => U) x → x ≤ b2Gamma B2.lo) :=
  ⟨fun _ _ _ => Pred.le_refl _, b2Gamma_monotone, by decide, fun h => not_U_le_E (h B2.lo),
    fun ⟨_, h⟩ => not_U_le_E (h U isLeastFixpoint_constU)⟩

/-- `R4-transfer-lfp` needs the post-fixpoint hypothesis (instance of
`lfpGamma_tight_postFixpoint`). -/
theorem lfpFixGamma_tight_postFixpoint :
    Monotone (fun _ : Pred Unit => U) ∧ Monotone b2Gamma ∧
      Sound b2Gamma (fun _ => U) (fun _ => B2.hi) ∧ ¬ PostFixpoint (fun _ : B2 => B2.hi) B2.lo ∧
      ¬ (IsLeastFixpoint (fun _ : Pred Unit => U) (lfp (fun _ : Pred Unit => U)) ∧
          ∀ x, IsLeastFixpoint (fun _ : Pred Unit => U) x → x ≤ b2Gamma B2.lo) :=
  ⟨fun _ _ _ => Pred.le_refl _, b2Gamma_monotone, fun _ => Pred.le_refl _, by decide,
    fun ⟨_, h⟩ => not_U_le_E (h U isLeastFixpoint_constU)⟩

/-! ## Boundary examples (proved) -/

/-- For a non-monotone `f`, `lfp f` need not be a post-fixpoint of `f`. -/
theorem lfp_not_postFixpoint_of_not_monotone :
    ¬ Monotone nonMonoUniqueFix ∧
      ¬ (nonMonoUniqueFix (lfp nonMonoUniqueFix) ≤ lfp nonMonoUniqueFix) := by
  refine ⟨nonMonoUniqueFix_not_monotone, ?_⟩
  rw [lfp_nonMonoUniqueFix_eq_empty, nonMonoUniqueFix_empty]
  intro h
  exact h true trivial

/-- Without monotone `f`, `R4-transfer` says nothing about fixpoints of `f`: all
its hypotheses hold (with an exact Galois connection `id`, `id` on the poset
`Pred Bool`) at `a = {false}`, `{true}` is the unique fixpoint of `f`, and
`γ a = {false}` does not contain it. -/
theorem transfer_misses_leastFixpoint_of_not_monotone :
    IsRefl (Pred Bool) ∧ IsTrans (Pred Bool) ∧ IsAntisymm (Pred Bool) ∧
      GaloisConnection (id : Pred Bool → Pred Bool) id ∧
      Monotone (id : Pred Bool → Pred Bool) ∧
      Sound (id : Pred Bool → Pred Bool) nonMonoUniqueFix nonMonoUniqueFix ∧
      PostFixpoint nonMonoUniqueFix pFalse ∧
      (∀ x, nonMonoUniqueFix x = x ↔ x = pTrue) ∧
      ¬ (pTrue ≤ id pFalse) := by
  refine ⟨Pred.le_refl, fun _ _ _ => Pred.le_trans, ?_, fun _ _ => Iff.rfl,
    fun _ _ h => h, fun _ => Pred.le_refl _, lfpFixGamma_tight_monotone.2.2.2.1,
    nonMonoUniqueFix_unique_fixpoint, lfpFixGamma_tight_monotone.2.2.2.2.2.2.1⟩
  intro x y hxy hyx
  funext b
  exact propext ⟨hxy b, hyx b⟩

/-- A finite reflexive relation with a strict cycle violates the ascending chain
condition. -/
theorem cyc3_not_acc : IsRefl Cyc3 ∧ ¬ IsTrans Cyc3 ∧ ¬ ACC Cyc3 :=
  ⟨Cyc3.isRefl, Cyc3.not_isTrans, fun h => h ⟨cyc3Chain, fun _ => Cyc3.strict_next _⟩⟩

/-- The same finite relation has no height bound. -/
theorem cyc3_not_heightLE (h : Nat) : ¬ HeightLE Cyc3 h := by
  intro hh
  have := hh cyc3Chain (h + 1) (fun _ _ => Cyc3.strict_next _)
  omega

/-- On a non-transitive relation, height `1` (hence the ascending chain condition)
does not make ascending sequences stabilize, not even up to `≤`: `nbChain` is
ascending, yet for every `N` some later element is not `≤ nbChain N`. -/
theorem nb_heightLE_one_ascending_not_stabilizing :
    IsRefl NB ∧ ¬ IsTrans NB ∧ HeightLE NB 1 ∧ ACC NB ∧
      (∀ n, nbChain n ≤ nbChain (n + 1)) ∧
      ¬ ∃ N, ∀ m, N ≤ m → nbChain m ≤ nbChain N := by
  refine ⟨NB.isRefl, NB.not_isTrans, NB.heightLE, ?_, ?_, ?_⟩
  · intro ⟨c, hc⟩
    have := NB.heightLE c 2 (fun i _ => hc i)
    omega
  · intro n
    show NB.mk (n / 2) (n % 2 == 1) ≤ NB.mk ((n + 1) / 2) ((n + 1) % 2 == 1)
    rw [NB.le_iff]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · exact Or.inl (by omega)
    · have h' : (n + 1) % 2 = 0 := by omega
      exact Or.inr ⟨by simp [h], by simp [h'], by omega⟩
  · intro ⟨N, hN⟩
    have := hN (N + 2) (by omega)
    simp only [nbChain] at this
    rw [NB.le_iff] at this
    rcases this with h | ⟨_, _, h⟩ <;> omega

end Toy.AbsInt
