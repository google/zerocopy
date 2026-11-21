import ToyDataflow.MopMfp
import ToyDataflow.Diamond

/-!
# Gen/kill (bit-vector) frameworks

The powerset of `Fin k`, represented as bit vectors `Fin k → Bool`, ordered by
inclusion, with union as join. A gen/kill transfer is `f a = (a \ kill) ∪ gen`.
These model classic bit-vector *may* analyses such as reaching definitions and
live variables (the latter after reversing the CFG).

The orientation matters for strictness. In `bvLat k` (inclusion, union, bottom
`∅`) a gen/kill transfer is strict iff `gen = ∅` (`genKill_strict_iff`). In the
dual *must* orientation `bvMustLat k` (reverse inclusion, intersection, bottom the
full set), used for analyses such as available expressions, it is strict iff
`kill ⊆ gen` (`genKill_strict_must_iff`).
-/

namespace Toy.Dataflow

/-- The bit-vector (powerset) lattice over `Fin k`: inclusion, union, empty set. -/
def bvLat (k : Nat) : Lat (Fin k → Bool) where
  le a b := ∀ i, a i = true → b i = true
  join a b := fun i => a i || b i
  bot := fun _ => false

instance bvLat_le_dec (k : Nat) (a b : Fin k → Bool) : Decidable ((bvLat k).le a b) :=
  inferInstanceAs (Decidable (∀ i, a i = true → b i = true))

/-- Positive example: `bvLat k` satisfies every lattice law. -/
theorem bvLat_isJSL (k : Nat) : (bvLat k).IsJSL where
  refl := fun _ _ h => h
  trans := fun _ _ _ hab hbc i hi => hbc i (hab i hi)
  antisymm := by
    intro a b hab hba
    funext i
    have h1 := hab i
    have h2 := hba i
    cases ha : a i <;> cases hb : b i <;> simp_all
  join_le_iff := by
    intro a b c
    simp only [bvLat, Bool.or_eq_true]
    constructor
    · intro h
      exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
    · rintro ⟨h1, h2⟩ i (hi | hi)
      · exact h1 i hi
      · exact h2 i hi
  bot_le := fun _ _ h => absurd h (by simp [bvLat])

/-- Number of set bits. -/
def popcount {k : Nat} (a : Fin k → Bool) : Nat := (List.finRange k).countP (fun i => a i)

theorem countP_le_of_imp {β : Type} (l : List β) (p q : β → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) : l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have h1 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have ha := h a (List.mem_cons_self ..)
    by_cases hp : p a = true
    · simp [hp, ha hp]; omega
    · simp [hp]; split <;> omega

theorem countP_lt_of_imp {β : Type} (l : List β) (p q : β → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) (hx : ∃ x ∈ l, q x = true ∧ p x = false) :
    l.countP p < l.countP q := by
  induction l with
  | nil => obtain ⟨x, hx, _⟩ := hx; simp at hx
  | cons a l ih =>
    simp only [List.countP_cons]
    have hle := countP_le_of_imp l p q (fun x hx => h x (List.mem_cons_of_mem _ hx))
    obtain ⟨x, hxl, hqx, hpx⟩ := hx
    rcases List.mem_cons.1 hxl with rfl | hxl
    · simp [hqx, hpx]; omega
    · have hlt := ih (fun y hy => h y (List.mem_cons_of_mem _ hy)) ⟨x, hxl, hqx, hpx⟩
      have ha := h a (List.mem_cons_self ..)
      by_cases hp : p a = true
      · simp [hp, ha hp]; omega
      · simp [hp]; split <;> omega

theorem popcount_lt {k : Nat} {a b : Fin k → Bool} (h : (bvLat k).lt a b) :
    popcount a < popcount b := by
  obtain ⟨hle, hne⟩ := h
  apply countP_lt_of_imp _ _ _ (fun i _ hi => hle i hi)
  have : ∃ i, a i ≠ b i := by
    apply Classical.byContradiction
    intro hc
    exact hne (funext fun i => Classical.byContradiction fun hi => hc ⟨i, hi⟩)
  obtain ⟨i, hi⟩ := this
  refine ⟨i, List.mem_finRange i, ?_⟩
  have := hle i
  cases ha : a i <;> cases hb : b i <;> simp_all

theorem popcount_le {k : Nat} (a : Fin k → Bool) : popcount a ≤ k := by
  have := @List.countP_le_length _ (fun i => a i) (List.finRange k)
  simpa [popcount, List.length_finRange] using this

/-- Positive example: `bvLat k` has height at most `k`. -/
theorem bvLat_heightLe (k : Nat) : (bvLat k).HeightLe k :=
  Lat.heightLe_of_rank popcount (fun _ _ h => popcount_lt h) k popcount_le

theorem bvLat_acc (k : Nat) : (bvLat k).AscendingChainCondition :=
  Lat.acc_of_heightLe (bvLat_heightLe k)

/-- A gen/kill transfer function: `f a = (a \ kill) ∪ gen`. -/
def genKill {k : Nat} (gen kill : Fin k → Bool) (a : Fin k → Bool) : Fin k → Bool :=
  fun i => (a i && !kill i) || gen i

/-- Gen/kill transfer functions distribute over union. -/
theorem genKill_distributive {k : Nat} (gen kill : Fin k → Bool) :
    Distributive (bvLat k) (genKill gen kill) := by
  intro a b
  funext i
  simp only [genKill, bvLat]
  cases a i <;> cases b i <;> cases kill i <;> cases gen i <;> rfl

/-- A gen/kill transfer function is strict exactly when its gen set is empty. -/
theorem genKill_strict_iff {k : Nat} (gen kill : Fin k → Bool) :
    Strict (bvLat k) (genKill gen kill) ↔ gen = fun _ => false := by
  exact Iff.rfl

/-- Gen/kill exactness: if every transfer function of a CFG over `bvLat k` has
gen/kill form, and every node unreachable from the entry has an empty gen set,
then the least solution equals MOP at every node. -/
theorem genKill_isMOPAt_of_isLeastSolution_of_unreachable_gen_empty {n k : Nat}
    (G : CFG n (Fin k → Bool)) (gen kill : Fin n → Fin k → Bool)
    (hG : ∀ u, G.f u = genKill (gen u) (kill u))
    (hgen : ∀ u, ¬ Reachable G u → gen u = fun _ => false)
    {x : Fin n → Fin k → Bool} (hx : IsLeastSolution (bvLat k) G x) (v : Fin n) :
    IsMOPAt (bvLat k) G v (x v) := by
  apply isMOPAt_of_isLeastSolution_of_distributive_of_unreachableStrict (bvLat k) G
    (bvLat_isJSL k) (bvLat_acc k) (fun u => hG u ▸ genKill_distributive _ _) _ hx v
  intro u hu
  rw [hG u]
  exact (genKill_strict_iff _ _).2 (hgen u hu)

/-- Gen/kill exactness with existence: under the same hypotheses a least solution
exists, and it equals MOP at every node. -/
theorem genKill_exists_isLeastSolution_and_isMOPAt_of_unreachable_gen_empty {n k : Nat}
    (G : CFG n (Fin k → Bool)) (gen kill : Fin n → Fin k → Bool)
    (hG : ∀ u, G.f u = genKill (gen u) (kill u))
    (hgen : ∀ u, ¬ Reachable G u → gen u = fun _ => false) :
    ∃ x : Fin n → Fin k → Bool, IsLeastSolution (bvLat k) G x ∧
      ∀ v, IsMOPAt (bvLat k) G v (x v) := by
  apply exists_isLeastSolution_and_isMOPAt_of_distributive_of_unreachableStrict
    (bvLat k) G (bvLat_isJSL k) (bvLat_acc k) (fun u => hG u ▸ genKill_distributive _ _)
  intro u hu
  rw [hG u]
  exact (genKill_strict_iff _ _).2 (hgen u hu)

/-! ## The dual (must-analysis) orientation -/

/-- Bit vectors ordered by reverse inclusion, with intersection as join and the full
set as bottom: the orientation of must analyses such as available expressions. -/
def bvMustLat (k : Nat) : Lat (Fin k → Bool) where
  le a b := ∀ i, b i = true → a i = true
  join a b := fun i => a i && b i
  bot := fun _ => true

/-- Positive example: `bvMustLat k` satisfies every lattice law. -/
theorem bvMustLat_isJSL (k : Nat) : (bvMustLat k).IsJSL where
  refl := fun _ _ h => h
  trans := fun _ _ _ hab hbc i hi => hab i (hbc i hi)
  antisymm := by
    intro a b hab hba
    funext i
    have h1 := hab i
    have h2 := hba i
    cases ha : a i <;> cases hb : b i <;> simp_all
  join_le_iff := by
    intro a b c
    simp only [bvMustLat, Bool.and_eq_true]
    constructor
    · intro h
      exact ⟨fun i hi => (h i hi).1, fun i hi => (h i hi).2⟩
    · rintro ⟨h1, h2⟩ i hi
      exact ⟨h1 i hi, h2 i hi⟩
  bot_le := fun _ _ _ => rfl

/-- Gen/kill transfer functions distribute over intersection as well. -/
theorem genKill_distributive_must {k : Nat} (gen kill : Fin k → Bool) :
    Distributive (bvMustLat k) (genKill gen kill) := by
  intro a b
  funext i
  simp only [genKill, bvMustLat]
  cases a i <;> cases b i <;> cases kill i <;> cases gen i <;> rfl

/-- In the must orientation a gen/kill transfer is strict (maps the full set to the
full set) exactly when every killed bit is also generated (`kill ⊆ gen`). -/
theorem genKill_strict_must_iff {k : Nat} (gen kill : Fin k → Bool) :
    Strict (bvMustLat k) (genKill gen kill) ↔ ∀ i, kill i = true → gen i = true := by
  constructor
  · intro h i hk
    have := congrFun h i
    simpa [genKill, bvMustLat, hk] using this
  · intro h
    funext i
    simp only [genKill, bvMustLat]
    cases hk : kill i <;> cases hg : gen i <;> simp_all

/-- Negative example: a kill-only transfer is strict in the may orientation but not
in the must orientation. -/
theorem genKill_killOnly_strict_may_not_must :
    Strict (bvLat 1) (genKill (fun _ => false) (fun _ => true)) ∧
      ¬ Strict (bvMustLat 1) (genKill (fun _ => false) (fun _ => true)) := by
  refine ⟨(genKill_strict_iff _ _).2 rfl, fun h => ?_⟩
  have := (genKill_strict_must_iff _ _).1 h 0 rfl
  simp at this

/-! ## Examples on `bvLat 2` -/

/-- Copy bit 0 into both bits: distributive, but not of gen/kill form. -/
def copyBit0 (a : Fin 2 → Bool) : Fin 2 → Bool := fun _ => a 0

theorem copyBit0_distributive : Distributive (bvLat 2) copyBit0 := fun _ _ => rfl

/-- Negative example for `genKill`: `copyBit0` is not a gen/kill function (so the
gen/kill form is sufficient, not necessary, for distributivity). -/
theorem copyBit0_not_genKill : ¬ ∃ gen kill, ∀ a, copyBit0 a = genKill gen kill a := by
  rintro ⟨gen, kill, h⟩
  have h0 := congrFun (h (fun _ => false)) 1
  have h1 := congrFun (h (fun i => decide (i = 0))) 1
  simp [copyBit0, genKill] at h0 h1
  simp [h0] at h1

/-- "Both bits set", broadcast to both bits: monotone but not distributive. -/
def bothBits (a : Fin 2 → Bool) : Fin 2 → Bool := fun _ => a 0 && a 1

theorem bothBits_monotone : Monotone (bvLat 2) bothBits := by
  intro a b hab i hi
  simp only [bothBits, Bool.and_eq_true] at hi ⊢
  exact ⟨hab 0 hi.1, hab 1 hi.2⟩

/-- Negative example for `Distributive`: `bothBits` on `{0} ∪ {1}`. -/
theorem bothBits_not_distributive : ¬ Distributive (bvLat 2) bothBits := by
  intro h
  have := congrFun (h (fun i => decide (i = 0)) (fun i => decide (i = 1))) 0
  simp [bothBits, bvLat] at this

/-- Positive example for `Distributive`/`Strict`: a kill-only gen/kill function. -/
theorem genKill_killOnly_strict (kill : Fin 2 → Bool) :
    Distributive (bvLat 2) (genKill (fun _ => false) kill) ∧
      Strict (bvLat 2) (genKill (fun _ => false) kill) :=
  ⟨genKill_distributive _ _, (genKill_strict_iff _ _).2 rfl⟩

/-- Negative example for `Strict`: a gen/kill function with non-empty gen set. -/
theorem genKill_gen_not_strict :
    ¬ Strict (bvLat 2) (genKill (fun _ => true) (fun _ => false)) := by
  rw [genKill_strict_iff]
  intro h
  simpa using congrFun h 0

end Toy.Dataflow
