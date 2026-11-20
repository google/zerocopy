import ToyFarkas.Checker

/-!
# Motzkin's transposition theorem for scaled points, by Fourier–Motzkin elimination

This module proves the converse of `checkFarkas_sound_scaled` (used by
`farkas_complete_scaled` in `ToyFarkas.Completeness`). The proof works with *homogeneous*
constraints `a · y ≤ 0` / `a · y < 0` over integer points `y : Nat → Int`:

1. A system `S` is homogenized by a fresh coordinate `y 0` standing for the denominator `d`
   (the variables of `S` are shifted by one), plus the strict constraint `-y 0 < 0`.
2. Fourier–Motzkin elimination removes the largest variable: every pair of a constraint with a
   positive and one with a negative coefficient is combined with positive integer weights.
   If the eliminated system has an integer solution, the original one has an integer solution
   (obtained by scaling the solution and choosing the eliminated coordinate between the
   tightest lower and upper bound; homogeneity makes the scaling harmless).
3. With no variables left, an unsatisfiable system contains a strict constraint `0 < 0`.
4. The derivation of that constraint is a non-negative integer combination of the original
   constraints, which is read back as a certificate accepted by `checkFarkas`.

No rational number type is used; all multipliers are integers.
-/

namespace Toy.Farkas
namespace Motzkin

/-! ## Homogeneous constraints and derivations -/

/-- A homogeneous constraint `a · y ≤ 0` (`s = false`) or `a · y < 0` (`s = true`). -/
structure HC where
  a : SparseVec
  s : Bool

/-- Satisfaction of a homogeneous constraint at an integer point. -/
def HC.Holds (h : HC) (y : Nat → Int) : Prop :=
  SparseVec.eval h.a y ≤ 0 ∧ (h.s = true → SparseVec.eval h.a y < 0)

/-- Satisfaction of a finite homogeneous system. -/
def HSat (H : List HC) (y : Nat → Int) : Prop := ∀ h ∈ H, h.Holds y

/-- Constraints derivable from `H` by non-negative combination: members, sums (strict if either
summand is strict), and positive integer multiples. -/
inductive Deriv (H : List HC) : HC → Prop
  | mem {h : HC} : h ∈ H → Deriv H h
  | add {h g : HC} : Deriv H h → Deriv H g → Deriv H ⟨h.a ++ g.a, h.s || g.s⟩
  | smul {h : HC} {c : Int} : 0 < c → Deriv H h → Deriv H ⟨SparseVec.smul c h.a, h.s⟩

theorem Deriv.trans {H H' : List HC} (hH : ∀ g ∈ H', Deriv H g) {x : HC} (hx : Deriv H' x) :
    Deriv H x := by
  induction hx with
  | mem hm => exact hH _ hm
  | add _ _ ih1 ih2 => exact Deriv.add ih1 ih2
  | smul hc _ ih => exact Deriv.smul hc ih

/-! ## Evaluation lemmas -/

theorem eval_update (v : SparseVec) (n : Nat) (t : Int) (f : Nat → Int) :
    SparseVec.eval v (fun i => if i = n then t else f i) =
      SparseVec.eval v f + SparseVec.coeff v n * (t - f n) := by
  induction v with
  | nil => simp
  | cons a v ih =>
    rw [SparseVec.eval_cons, SparseVec.eval_cons, SparseVec.coeff_cons, ih]
    by_cases h : a.1 = n
    · subst h; simp only [ite_true]; grind
    · simp only [h, ite_false]; grind

theorem eval_scale_point (v : SparseVec) (M : Int) (f : Nat → Int) :
    SparseVec.eval v (fun i => M * f i) = M * SparseVec.eval v f := by
  induction v with
  | nil => simp
  | cons a v ih => rw [SparseVec.eval_cons, SparseVec.eval_cons, ih]; grind

theorem eval_eq_zero_of_coeff (v : SparseVec) (h : ∀ i, SparseVec.coeff v i = 0)
    (y : Nat → Int) : SparseVec.eval v y = 0 :=
  SparseVec.eval_eq_zero_of_isZero v ((SparseVec.isZero_iff_coeff_eq_zero v).mpr h) y

/-! ## Fourier–Motzkin elimination of one variable -/

/-- Combination of `p` (positive coefficient at `n`) and `q` (negative coefficient at `n`)
cancelling variable `n`. -/
def comb (n : Nat) (p q : HC) : HC :=
  ⟨SparseVec.smul (-SparseVec.coeff q.a n) p.a ++ SparseVec.smul (SparseVec.coeff p.a n) q.a,
    p.s || q.s⟩

/-- One Fourier–Motzkin step eliminating variable `n`. -/
def elim (n : Nat) (H : List HC) : List HC :=
  H.filter (fun h => decide (SparseVec.coeff h.a n = 0)) ++
  (H.filter (fun h => decide (0 < SparseVec.coeff h.a n))).flatMap (fun p =>
    (H.filter (fun h => decide (SparseVec.coeff h.a n < 0))).map (fun q => comb n p q))

theorem mem_elim {n : Nat} {H : List HC} {g : HC} :
    g ∈ elim n H ↔ (g ∈ H ∧ SparseVec.coeff g.a n = 0) ∨
      ∃ p ∈ H, 0 < SparseVec.coeff p.a n ∧ ∃ q ∈ H, SparseVec.coeff q.a n < 0 ∧ g = comb n p q := by
  simp only [elim, List.mem_append, List.mem_filter, List.mem_flatMap, List.mem_map,
    decide_eq_true_eq]
  constructor
  · rintro (h | ⟨p, ⟨hp, hpn⟩, q, ⟨hq, hqn⟩, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, hpn, q, hq, hqn, rfl⟩
  · rintro (h | ⟨p, hp, hpn, q, hq, hqn, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, ⟨hp, hpn⟩, q, ⟨hq, hqn⟩, rfl⟩

theorem coeff_comb (n : Nat) (p q : HC) (i : Nat) :
    SparseVec.coeff (comb n p q).a i =
      -SparseVec.coeff q.a n * SparseVec.coeff p.a i + SparseVec.coeff p.a n * SparseVec.coeff q.a i := by
  simp only [comb, SparseVec.coeff_append, SparseVec.coeff_smul]

theorem eval_comb (n : Nat) (p q : HC) (y : Nat → Int) :
    SparseVec.eval (comb n p q).a y =
      -SparseVec.coeff q.a n * SparseVec.eval p.a y + SparseVec.coeff p.a n * SparseVec.eval q.a y := by
  simp only [comb, SparseVec.eval_append, SparseVec.eval_smul]

theorem elim_support (n : Nat) (H : List HC)
    (hH : ∀ h ∈ H, ∀ i, n + 1 ≤ i → SparseVec.coeff h.a i = 0) :
    ∀ g ∈ elim n H, ∀ i, n ≤ i → SparseVec.coeff g.a i = 0 := by
  intro g hg i hi
  rcases mem_elim.mp hg with ⟨hgH, hgn⟩ | ⟨p, hp, _, q, hq, _, rfl⟩
  · rcases Nat.lt_or_eq_of_le hi with h | h
    · exact hH g hgH i h
    · subst h; exact hgn
  · rw [coeff_comb]
    rcases Nat.lt_or_eq_of_le hi with h | h
    · rw [hH p hp i h, hH q hq i h]; simp
    · subst h; grind

theorem deriv_of_mem_elim (n : Nat) (H : List HC) : ∀ g ∈ elim n H, Deriv H g := by
  intro g hg
  rcases mem_elim.mp hg with ⟨hgH, _⟩ | ⟨p, hp, hpn, q, hq, hqn, rfl⟩
  · exact Deriv.mem hgH
  · exact Deriv.add (Deriv.smul (by omega) (Deriv.mem hp)) (Deriv.smul hpn (Deriv.mem hq))

/-! ## Extending a solution of the eliminated system -/

/-- A transitive, total (on the list) relation has a least element on a non-empty list. -/
theorem exists_min_on {α : Type} (r : α → α → Prop) : ∀ (L : List α),
    (∀ a ∈ L, ∀ b ∈ L, r a b ∨ r b a) →
    (∀ a ∈ L, ∀ b ∈ L, ∀ c ∈ L, r a b → r b c → r a c) →
    L ≠ [] → ∃ m ∈ L, ∀ x ∈ L, r m x
  | [], _, _, h => absurd rfl h
  | [a], htot, _, _ => by
    refine ⟨a, List.mem_singleton_self a, ?_⟩
    intro x hx
    rw [List.mem_singleton] at hx
    subst hx
    rcases htot x (List.mem_singleton_self x) x (List.mem_singleton_self x) with h | h <;> exact h
  | a :: b :: L, htot, htrans, _ => by
    obtain ⟨m, hm, hmin⟩ := exists_min_on r (b :: L)
      (fun x hx y hy => htot x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
      (fun x hx y hy z hz => htrans x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
        z (List.mem_cons_of_mem _ hz))
      (List.cons_ne_nil _ _)
    rcases htot a (List.mem_cons_self ..) m (List.mem_cons_of_mem _ hm) with h | h
    · refine ⟨a, List.mem_cons_self .., ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases htot x (List.mem_cons_self ..) x (List.mem_cons_self ..) with h' | h' <;> exact h'
      · exact htrans a (List.mem_cons_self ..) m (List.mem_cons_of_mem _ hm) x
          (List.mem_cons_of_mem _ hx) h (hmin x hx)
    · refine ⟨m, List.mem_cons_of_mem _ hm, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h
      · exact hmin x hx

/-- Transitivity of `x₂ / d₂ ≤ x₁ / d₁` (written without division) for positive `dᵢ`. -/
theorem frac_trans {x1 x2 x3 d1 d2 d3 : Int} (h1 : 0 < d1) (h2 : 0 < d2) (h3 : 0 < d3)
    (ha : x2 * d1 ≤ x1 * d2) (hb : x3 * d2 ≤ x2 * d3) : x3 * d1 ≤ x1 * d3 := by
  have e1 := Int.mul_le_mul_of_nonneg_right ha (Int.le_of_lt h3)
  have e2 := Int.mul_le_mul_of_nonneg_right hb (Int.le_of_lt h1)
  have e3 : d2 * (x3 * d1) ≤ d2 * (x1 * d3) := by grind
  exact Int.le_of_mul_le_mul_left e3 h2

/-- Arithmetic for an upper-bound constraint when both bound kinds exist. -/
theorem arith_upper_both {P0 Q0 pn R Rp Rq : Int} (hP0 : 0 < P0) (hQ0 : 0 < Q0)
    (hB : R * P0 ≤ Rp * pn) {X : Int} (hX : X = Q0 * R + pn * Rq) :
    (X ≤ 0 → 2 * P0 * Q0 * R + pn * (Rq * P0 - Rp * Q0) ≤ 0) ∧
    (X < 0 → 2 * P0 * Q0 * R + pn * (Rq * P0 - Rp * Q0) < 0) := by
  have h2 : Q0 * (R * P0 - Rp * pn) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hQ0) (by omega)
  constructor
  · intro hA
    have h1 : P0 * X ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hP0) hA
    subst hX; grind
  · intro hA
    have h1 : P0 * X < 0 := Int.mul_neg_of_pos_of_neg hP0 hA
    subst hX; grind

/-- Arithmetic for a lower-bound constraint when both bound kinds exist. -/
theorem arith_lower_both {P0 Q0 qn R Rp Rq : Int} (hP0 : 0 < P0) (hQ0 : 0 < Q0)
    (hB : R * Q0 ≤ Rq * -qn) {X : Int} (hX : X = -qn * Rp + P0 * R) :
    (X ≤ 0 → 2 * P0 * Q0 * R + qn * (Rq * P0 - Rp * Q0) ≤ 0) ∧
    (X < 0 → 2 * P0 * Q0 * R + qn * (Rq * P0 - Rp * Q0) < 0) := by
  have h2 : P0 * (R * Q0 - Rq * -qn) ≤ 0 :=
    Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hP0) (by omega)
  constructor
  · intro hA
    have h1 : Q0 * X ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hQ0) hA
    subst hX; grind
  · intro hA
    have h1 : Q0 * X < 0 := Int.mul_neg_of_pos_of_neg hQ0 hA
    subst hX; grind

/-- Arithmetic for an upper-bound constraint when no lower bound exists. -/
theorem arith_upper_only {P0 pn R Rp : Int} (hpn : 0 < pn) (hB : R * P0 ≤ Rp * pn) :
    P0 * R + pn * (-Rp - 1) < 0 := by grind

/-- Arithmetic for a lower-bound constraint when no upper bound exists. -/
theorem arith_lower_only {Q0 qn R Rq : Int} (hqn : qn < 0) (hB : R * Q0 ≤ Rq * -qn) :
    Q0 * R + qn * (Rq + 1) < 0 := by grind

/-- The value of a constraint at `y` with the contribution of variable `n` removed. -/
def rest (n : Nat) (y : Nat → Int) (h : HC) : Int :=
  SparseVec.eval h.a y - SparseVec.coeff h.a n * y n

/-- Among the constraints with `0 < d h`, one maximizes `rest h / d h`. -/
theorem exists_best_in (n : Nat) (y : Nat → Int) (H : List HC) (d : HC → Int)
    (hex : ∃ h ∈ H, 0 < d h) :
    ∃ m ∈ H, 0 < d m ∧ ∀ x ∈ H, 0 < d x → rest n y x * d m ≤ rest n y m * d x := by
  obtain ⟨m, hm, hmin⟩ := exists_min_on (fun m x => rest n y x * d m ≤ rest n y m * d x)
    (H.filter (fun h => decide (0 < d h)))
    (fun a _ b _ => Int.le_total _ _)
    (fun a ha b hb c hc hab hbc =>
      frac_trans (by simpa using (List.mem_filter.mp ha).2) (by simpa using (List.mem_filter.mp hb).2)
        (by simpa using (List.mem_filter.mp hc).2) hab hbc)
    (by
      obtain ⟨h, hh, hd⟩ := hex
      exact List.ne_nil_of_mem (List.mem_filter.mpr ⟨hh, by simpa using hd⟩))
  have hm' := List.mem_filter.mp hm
  exact ⟨m, hm'.1, by simpa using hm'.2,
    fun x hx hdx => hmin x (List.mem_filter.mpr ⟨hx, by simpa using hdx⟩)⟩

/-- A scaled point with the eliminated coordinate replaced satisfies `H` once the upper- and
lower-bound constraints hold. -/
theorem extend_of_bounds (n : Nat) (H : List HC) (y' : Nat → Int)
    (hZ : ∀ h ∈ H, SparseVec.coeff h.a n = 0 → h.Holds y')
    (M t : Int) (hM : 0 < M)
    (hP : ∀ p ∈ H, 0 < SparseVec.coeff p.a n →
      M * rest n y' p + SparseVec.coeff p.a n * t ≤ 0 ∧
      (p.s = true → M * rest n y' p + SparseVec.coeff p.a n * t < 0))
    (hN : ∀ q ∈ H, SparseVec.coeff q.a n < 0 →
      M * rest n y' q + SparseVec.coeff q.a n * t ≤ 0 ∧
      (q.s = true → M * rest n y' q + SparseVec.coeff q.a n * t < 0)) :
    HSat H (fun i => if i = n then t else M * y' i) := by
  intro h hh
  have he : SparseVec.eval h.a (fun i => if i = n then t else M * y' i) =
      M * rest n y' h + SparseVec.coeff h.a n * t := by
    rw [eval_update h.a n t (fun i => M * y' i), eval_scale_point]
    simp only [rest]
    grind
  unfold HC.Holds
  rw [he]
  rcases Int.lt_trichotomy (SparseVec.coeff h.a n) 0 with hc | hc | hc
  · exact hN h hh hc
  · have hz := hZ h hh hc
    unfold HC.Holds at hz
    simp only [rest, hc, Int.zero_mul, Int.sub_zero, Int.add_zero]
    exact ⟨Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hM) hz.1,
      fun hs => Int.mul_neg_of_pos_of_neg hM (hz.2 hs)⟩
  · exact hP h hh hc

/-- **Fourier–Motzkin extension.** An integer solution of the eliminated system yields an integer
solution of the original system. -/
theorem elim_extend (n : Nat) (H : List HC) (y' : Nat → Int) (hy : HSat (elim n H) y') :
    ∃ y, HSat H y := by
  have hZ : ∀ h ∈ H, SparseVec.coeff h.a n = 0 → h.Holds y' :=
    fun h hh hc => hy h (mem_elim.mpr (Or.inl ⟨hh, hc⟩))
  have hPair : ∀ p ∈ H, 0 < SparseVec.coeff p.a n → ∀ q ∈ H, SparseVec.coeff q.a n < 0 →
      (comb n p q).Holds y' :=
    fun p hp hpn q hq hqn => hy _ (mem_elim.mpr (Or.inr ⟨p, hp, hpn, q, hq, hqn, rfl⟩))
  have hVal : ∀ p q : HC, SparseVec.eval (comb n p q).a y' =
      -SparseVec.coeff q.a n * rest n y' p + SparseVec.coeff p.a n * rest n y' q := by
    intro p q
    rw [eval_comb]
    simp only [rest]
    grind
  by_cases hPe : ∃ p ∈ H, 0 < SparseVec.coeff p.a n
  · obtain ⟨ps, hps, hP0, hpmin⟩ := exists_best_in n y' H (fun h => SparseVec.coeff h.a n) hPe
    by_cases hNe : ∃ q ∈ H, 0 < -SparseVec.coeff q.a n
    · -- both kinds of bounds: take the midpoint of the tightest pair
      obtain ⟨qs, hqs, hQ0, hqmin⟩ := exists_best_in n y' H (fun h => -SparseVec.coeff h.a n) hNe
      refine ⟨_, extend_of_bounds n H y' hZ
        (2 * SparseVec.coeff ps.a n * -SparseVec.coeff qs.a n)
        (rest n y' qs * SparseVec.coeff ps.a n - rest n y' ps * -SparseVec.coeff qs.a n)
        (by have := Int.mul_pos hP0 hQ0; grind) ?_ ?_⟩
      · intro p hp hpn
        have hc := hPair p hp hpn qs hqs (by simp at hQ0; omega)
        have hB := hpmin p hp hpn
        have A := arith_upper_both (Rq := rest n y' qs) hP0 hQ0 hB (hVal p qs)
        unfold HC.Holds at hc
        exact ⟨A.1 hc.1, fun hs => A.2 (hc.2 (by simp [comb, hs]))⟩
      · intro q hq hqn
        have hc := hPair ps hps hP0 q hq hqn
        have hB := hqmin q hq (by omega)
        have A := arith_lower_both (Rp := rest n y' ps) hP0 hQ0 hB (hVal ps q)
        unfold HC.Holds at hc
        exact ⟨A.1 hc.1, fun hs => A.2 (hc.2 (by simp [comb, hs]))⟩
    · -- upper bounds only
      refine ⟨_, extend_of_bounds n H y' hZ (SparseVec.coeff ps.a n) (-rest n y' ps - 1) hP0 ?_ ?_⟩
      · intro p hp hpn
        have A := arith_upper_only (Rp := rest n y' ps) hpn (hpmin p hp hpn)
        exact ⟨Int.le_of_lt A, fun _ => A⟩
      · intro q hq hqn
        exact absurd ⟨q, hq, by omega⟩ hNe
  · by_cases hNe : ∃ q ∈ H, 0 < -SparseVec.coeff q.a n
    · -- lower bounds only
      obtain ⟨qs, hqs, hQ0, hqmin⟩ := exists_best_in n y' H (fun h => -SparseVec.coeff h.a n) hNe
      refine ⟨_, extend_of_bounds n H y' hZ (-SparseVec.coeff qs.a n) (rest n y' qs + 1) hQ0 ?_ ?_⟩
      · intro p hp hpn
        exact absurd ⟨p, hp, hpn⟩ hPe
      · intro q hq hqn
        have A := arith_lower_only (Rq := rest n y' qs) hqn (hqmin q hq (by omega))
        exact ⟨Int.le_of_lt A, fun _ => A⟩
    · -- no bounds on variable `n`
      refine ⟨_, extend_of_bounds n H y' hZ 1 0 (by decide) ?_ ?_⟩
      · intro p hp hpn
        exact absurd ⟨p, hp, hpn⟩ hPe
      · intro q hq hqn
        exact absurd ⟨q, hq, by omega⟩ hNe

/-- **Homogeneous Motzkin by Fourier–Motzkin elimination.** If every constraint of `H` only
mentions variables `< n` and `H` has no integer solution, then a strict constraint with the zero
form is derivable from `H`. -/
theorem fm_main : ∀ (n : Nat) (H : List HC),
    (∀ h ∈ H, ∀ i, n ≤ i → SparseVec.coeff h.a i = 0) →
    (∀ y, ¬ HSat H y) → ∃ g, Deriv H g ∧ g.s = true ∧ ∀ i, SparseVec.coeff g.a i = 0
  | 0, H, hsupp, hns => by
    have hz : ∀ h ∈ H, ∀ y, SparseVec.eval h.a y = 0 := fun h hh y =>
      eval_eq_zero_of_coeff h.a (fun i => hsupp h hh i (Nat.zero_le i)) y
    have hn := hns (fun _ => 0)
    have ⟨h, hh, hnh⟩ : ∃ h ∈ H, ¬ h.Holds (fun _ => 0) := by
      refine Classical.byContradiction fun hc => hn ?_
      intro h hh
      exact Classical.byContradiction fun hnh => hc ⟨h, hh, hnh⟩
    refine ⟨h, Deriv.mem hh, ?_, fun i => hsupp h hh i (Nat.zero_le i)⟩
    unfold HC.Holds at hnh
    rw [hz h hh] at hnh
    cases hs : h.s
    · exact absurd ⟨Int.le_refl 0, fun hf => by simp [hs] at hf⟩ hnh
    · rfl
  | n + 1, H, hsupp, hns => by
    have hns' : ∀ y, ¬ HSat (elim n H) y := fun y hy => by
      obtain ⟨y0, hy0⟩ := elim_extend n H y hy
      exact hns y0 hy0
    obtain ⟨g, hg, hgs, hgz⟩ := fm_main n (elim n H) (elim_support n H hsupp) hns'
    exact ⟨g, Deriv.trans (deriv_of_mem_elim n H) hg, hgs, hgz⟩

/-! ## Reading a derivation as integer multipliers -/

/-- Coefficient of variable `i` in the combination `Σₖ μₖ · Hₖ`. -/
def lincomb (μ : List Int) (H : List HC) (i : Nat) : Int :=
  (List.zipWith (fun l h => l * SparseVec.coeff h.a i) μ H).sum

/-- Some strict constraint of `H` has a positive multiplier in `μ`. -/
def strictPos (μ : List Int) (H : List HC) : Bool :=
  (List.zipWith (fun l h => decide (0 < l) && h.s) μ H).any id

/-- `μ` is a multiplier vector over `H` that produces `g`. -/
structure IsMult (H : List HC) (g : HC) (μ : List Int) : Prop where
  len : μ.length = H.length
  nonneg : ∀ l ∈ μ, 0 ≤ l
  coeff : ∀ i, SparseVec.coeff g.a i = lincomb μ H i
  strict : g.s = true → strictPos μ H = true

theorem lincomb_cons (l : Int) (μ : List Int) (h : HC) (H : List HC) (i : Nat) :
    lincomb (l :: μ) (h :: H) i = l * SparseVec.coeff h.a i + lincomb μ H i := by
  simp [lincomb]

theorem strictPos_cons (l : Int) (μ : List Int) (h : HC) (H : List HC) :
    strictPos (l :: μ) (h :: H) = ((decide (0 < l) && h.s) || strictPos μ H) := by
  simp [strictPos]

theorem lincomb_replicate_zero (H : List HC) (i : Nat) :
    lincomb (List.replicate H.length 0) H i = 0 := by
  induction H with
  | nil => rfl
  | cons h H ih => rw [List.length_cons, List.replicate_succ, lincomb_cons, ih]; simp

theorem lincomb_add : ∀ (μ ν : List Int) (H : List HC), μ.length = H.length →
    ν.length = H.length → ∀ i,
    lincomb (List.zipWith (· + ·) μ ν) H i = lincomb μ H i + lincomb ν H i
  | [], [], [], _, _, _ => rfl
  | l :: μ, m :: ν, h :: H, h1, h2, i => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
    rw [List.zipWith_cons_cons, lincomb_cons, lincomb_cons, lincomb_cons,
      lincomb_add μ ν H h1 h2 i]
    grind
  | [], _ :: _, _, h1, h2, _ => by simp at h1 h2; omega
  | _ :: _, [], _, h1, h2, _ => by simp at h1 h2; omega
  | [], [], _ :: _, h1, _, _ => by simp at h1
  | _ :: _, _ :: _, [], h1, _, _ => by simp at h1

theorem strictPos_add_left : ∀ (μ ν : List Int) (H : List HC), μ.length = ν.length →
    (∀ l ∈ ν, 0 ≤ l) →
    strictPos μ H = true → strictPos (List.zipWith (· + ·) μ ν) H = true
  | [], _, _, _, _, h => by simp [strictPos] at h
  | _ :: _, [], _, hl, _, _ => by simp at hl
  | _ :: _, _ :: _, [], _, _, h => by simp [strictPos] at h
  | l :: μ, m :: ν, g :: H, hlen, hν, h => by
    rw [List.zipWith_cons_cons, strictPos_cons]
    rw [strictPos_cons] at h
    have hm : 0 ≤ m := hν m (List.mem_cons_self ..)
    rcases Bool.or_eq_true_iff.mp h with h | h
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact Or.inl ⟨by omega, h.2⟩
    · simp only [Bool.or_eq_true]
      exact Or.inr (strictPos_add_left μ ν H (by simpa using hlen)
        (fun l hl => hν l (List.mem_cons_of_mem _ hl)) h)

theorem zipWith_add_comm (μ ν : List Int) :
    List.zipWith (· + ·) μ ν = List.zipWith (· + ·) ν μ := by
  induction μ generalizing ν with
  | nil => cases ν <;> rfl
  | cons l μ ih =>
    cases ν with
    | nil => rfl
    | cons m ν => rw [List.zipWith_cons_cons, List.zipWith_cons_cons, ih, Int.add_comm]

theorem nonneg_zipWith_add : ∀ (μ ν : List Int), (∀ l ∈ μ, 0 ≤ l) → (∀ l ∈ ν, 0 ≤ l) →
    ∀ l ∈ List.zipWith (· + ·) μ ν, 0 ≤ l
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: μ, b :: ν, h1, h2 => by
    rw [List.zipWith_cons_cons]
    intro l hl
    rcases List.mem_cons.mp hl with rfl | hl
    · have := h1 a (List.mem_cons_self ..); have := h2 b (List.mem_cons_self ..); omega
    · exact nonneg_zipWith_add μ ν (fun l h => h1 l (List.mem_cons_of_mem _ h))
        (fun l h => h2 l (List.mem_cons_of_mem _ h)) l hl

theorem lincomb_smul (c : Int) : ∀ (μ : List Int) (H : List HC) (i : Nat),
    lincomb (μ.map (c * ·)) H i = c * lincomb μ H i
  | [], _, _ => by simp [lincomb]
  | _ :: _, [], _ => by simp [lincomb]
  | l :: μ, h :: H, i => by
    rw [List.map_cons, lincomb_cons, lincomb_cons, lincomb_smul c μ H i]
    grind

theorem strictPos_smul {c : Int} (hc : 0 < c) : ∀ (μ : List Int) (H : List HC),
    strictPos (μ.map (c * ·)) H = strictPos μ H
  | [], _ => by simp [strictPos]
  | _ :: _, [] => by simp [strictPos]
  | l :: μ, h :: H => by
    rw [List.map_cons, strictPos_cons, strictPos_cons, strictPos_smul hc μ H]
    have : decide (0 < c * l) = decide (0 < l) := by
      by_cases hl : 0 < l
      · simp [hl, Int.mul_pos hc hl]
      · have : c * l ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt hc) (by omega)
        simp [hl]; omega
    rw [this]

theorem isMult_mem : ∀ (H : List HC) {h : HC}, h ∈ H → ∃ μ, IsMult H h μ
  | [], _, hm => absurd hm (List.not_mem_nil)
  | g :: H, h, hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · refine ⟨1 :: List.replicate H.length 0, ⟨by simp, ?_, ?_, ?_⟩⟩
      · intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · decide
        · rw [(List.mem_replicate.mp hl).2]; exact Int.le_refl 0
      · intro i; rw [lincomb_cons, lincomb_replicate_zero]; simp
      · intro hs; rw [strictPos_cons]; simp [hs]
    · obtain ⟨μ, hμ⟩ := isMult_mem H hm
      refine ⟨0 :: μ, ⟨by simp [hμ.len], ?_, ?_, ?_⟩⟩
      · intro l hl
        rcases List.mem_cons.mp hl with rfl | hl
        · exact Int.le_refl 0
        · exact hμ.nonneg l hl
      · intro i; rw [lincomb_cons, ← hμ.coeff i]; simp
      · intro hs; rw [strictPos_cons, hμ.strict hs]; simp

theorem isMult_of_deriv {H : List HC} {g : HC} (hd : Deriv H g) : ∃ μ, IsMult H g μ := by
  induction hd with
  | mem hm => exact isMult_mem H hm
  | @add h g _ _ ih1 ih2 =>
    obtain ⟨μ, hμ⟩ := ih1
    obtain ⟨ν, hν⟩ := ih2
    refine ⟨List.zipWith (· + ·) μ ν, ⟨?_, nonneg_zipWith_add μ ν hμ.nonneg hν.nonneg, ?_, ?_⟩⟩
    · simp [hμ.len, hν.len]
    · intro i
      rw [lincomb_add μ ν H hμ.len hν.len i, ← hμ.coeff i, ← hν.coeff i]
      exact SparseVec.coeff_append h.a g.a i
    · intro hs
      rcases Bool.or_eq_true_iff.mp hs with hs | hs
      · exact strictPos_add_left μ ν H (by rw [hμ.len, hν.len]) hν.nonneg (hμ.strict hs)
      · rw [zipWith_add_comm]
        exact strictPos_add_left ν μ H (by rw [hμ.len, hν.len]) hμ.nonneg (hν.strict hs)
  | @smul h c hc _ ih =>
    obtain ⟨μ, hμ⟩ := ih
    refine ⟨μ.map (c * ·), ⟨by simp [hμ.len], ?_, ?_, ?_⟩⟩
    · intro l hl
      obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hl
      exact Int.mul_nonneg (Int.le_of_lt hc) (hμ.nonneg l' hl')
    · intro i
      rw [lincomb_smul, ← hμ.coeff i]
      exact SparseVec.coeff_smul c h.a i
    · intro hs; rw [strictPos_smul hc]; exact hμ.strict hs

/-! ## Homogenization of a constraint system -/

/-- Shift every variable index up by one (index `0` is reserved for the denominator). -/
def shift (v : SparseVec) : SparseVec := v.map (fun e => (e.1 + 1, e.2))

/-- The homogeneous form `lhs · p - rhs · d ⋈ 0` of a constraint, with `d = y 0` and
`p i = y (i + 1)`. -/
def homC (c : Constraint) : HC := ⟨(0, -c.rhs) :: shift c.lhs, c.isStrict⟩

/-- The constraint `-d < 0`, i.e. `d > 0`. -/
def hden : HC := ⟨[(0, -1)], true⟩

/-- The homogenized system of `S`. -/
def homSys (S : List Constraint) : List HC := hden :: S.map homC

theorem coeff_shift_zero (v : SparseVec) : SparseVec.coeff (shift v) 0 = 0 := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [shift, List.map_cons, SparseVec.coeff_cons] at ih ⊢; simp [ih]

theorem coeff_shift_succ (v : SparseVec) (i : Nat) :
    SparseVec.coeff (shift v) (i + 1) = SparseVec.coeff v i := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    simp only [shift, List.map_cons, SparseVec.coeff_cons] at ih ⊢
    rw [ih]; simp

theorem eval_shift (v : SparseVec) (y : Nat → Int) :
    SparseVec.eval (shift v) y = SparseVec.eval v (fun i => y (i + 1)) := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [shift, List.map_cons, SparseVec.eval_cons] at ih ⊢; rw [ih]

theorem homSys_sat (S : List Constraint) (y : Nat → Int) (h : HSat (homSys S) y) :
    0 < y 0 ∧ SatScaled S (y 0) (fun i => y (i + 1)) := by
  constructor
  · have hd := (h hden (List.mem_cons_self ..)).2 rfl
    simp [hden] at hd
    omega
  · intro c hc
    have hh := h (homC c) (List.mem_cons_of_mem _ (List.mem_map_of_mem hc))
    unfold HC.Holds at hh
    simp only [homC, SparseVec.eval_cons, eval_shift] at hh
    unfold Constraint.HoldsScaled
    cases hr : c.rel with
    | le => simp only [Rel.Sat]; have := hh.1; grind
    | lt =>
      simp only [Rel.Sat]
      have := hh.2 (by simp [Constraint.isStrict, hr])
      grind

/-- Every variable index mentioned in `homSys S` is below `homBound S`. -/
def homBound (S : List Constraint) : Nat := (S.map (fun c => c.lhs.bound)).sum + 1

theorem le_sum_of_mem {L : List Nat} {x : Nat} (h : x ∈ L) : x ≤ L.sum := by
  induction L with
  | nil => simp at h
  | cons a L ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem homSys_support (S : List Constraint) :
    ∀ h ∈ homSys S, ∀ i, homBound S ≤ i → SparseVec.coeff h.a i = 0 := by
  intro h hh i hi
  rcases List.mem_cons.mp hh with rfl | hh
  · simp [hden, homBound] at hi ⊢; omega
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hh
    have hb : c.lhs.bound ≤ (S.map (fun c => c.lhs.bound)).sum :=
      le_sum_of_mem (List.mem_map_of_mem hc)
    simp only [homC, SparseVec.coeff_cons]
    have h0 : (0 : Nat) ≠ i := by simp [homBound] at hi; omega
    rw [ite_eq_right h0, Int.zero_add]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [coeff_shift_succ]
    apply SparseVec.coeff_eq_zero_of_not_mem
    intro p hp hpj
    have := SparseVec.lt_bound c.lhs p hp
    simp [homBound] at hi
    omega

/-! ## From a derivation to a `checkFarkas` certificate -/

theorem zipWith_map_right_sum {β : Type} (f : Int → HC → Int) (g : β → HC) :
    ∀ (μ : List Int) (S : List β),
    (List.zipWith f μ (S.map g)).sum = (List.zipWith (fun l c => f l (g c)) μ S).sum
  | [], _ => by simp
  | _ :: _, [] => by simp
  | l :: μ, c :: S => by
    rw [List.map_cons, List.zipWith_cons_cons, List.zipWith_cons_cons, List.sum_cons,
      List.sum_cons, zipWith_map_right_sum f g μ S]

theorem combineRhs_neg : ∀ (μ : List Int) (S : List Constraint),
    (List.zipWith (fun l c => l * -c.rhs) μ S).sum = -combineRhs S μ
  | [], _ => by simp [combineRhs]
  | _ :: _, [] => by simp [combineRhs]
  | l :: μ, c :: S => by
    have ih := combineRhs_neg μ S
    simp only [combineRhs, List.zipWith_cons_cons, List.sum_cons] at ih ⊢
    rw [ih]; grind

theorem strictPos_homC : ∀ (μ : List Int) (S : List Constraint),
    strictPos μ (S.map homC) = combineStrict S μ
  | [], _ => by simp [strictPos, combineStrict]
  | _ :: _, [] => by simp [strictPos, combineStrict]
  | l :: μ, c :: S => by
    rw [List.map_cons, strictPos_cons, strictPos_homC μ S]
    simp [combineStrict, homC]

/-- **Completeness of `checkFarkas` for scaled points** (Motzkin's transposition theorem with
integer multipliers). -/
theorem complete (S : List Constraint)
    (h : ∀ (d : Int) (p : Nat → Int), 0 < d → ¬ SatScaled S d p) :
    ∃ cert : List Int, checkFarkas S cert = true := by
  have hns : ∀ y, ¬ HSat (homSys S) y := by
    intro y hy
    obtain ⟨hd, hs⟩ := homSys_sat S y hy
    exact h _ _ hd hs
  obtain ⟨g, hg, hgs, hgz⟩ := fm_main (homBound S) (homSys S) (homSys_support S) hns
  obtain ⟨μ, hμ⟩ := isMult_of_deriv hg
  match μ, hμ with
  | [], hμ => exact absurd hμ.len (by simp [homSys])
  | μd :: cert, hμ =>
    refine ⟨cert, ?_⟩
    have hnn : ∀ l ∈ cert, 0 ≤ l := fun l hl => hμ.nonneg l (List.mem_cons_of_mem _ hl)
    have hμd : 0 ≤ μd := hμ.nonneg μd (List.mem_cons_self ..)
    -- coefficient of variable `i + 1`: the combined left-hand side vanishes
    have hlhs : ∀ i, SparseVec.coeff (combineLhs S cert) i = 0 := by
      intro i
      have := hμ.coeff (i + 1)
      rw [hgz, homSys, lincomb_cons] at this
      simp only [lincomb] at this
      rw [zipWith_map_right_sum] at this
      rw [combineLhs_coeff]
      have e : (fun l c => l * SparseVec.coeff (homC c).a (i + 1)) =
          (fun (l : Int) (c : Constraint) => l * SparseVec.coeff c.lhs i) := by
        funext l c
        simp only [homC, SparseVec.coeff_cons, coeff_shift_succ]
        simp
      rw [e] at this
      simp [hden] at this
      omega
    -- coefficient of the denominator variable `0`: the combined right-hand side is `-μd`
    have hrhs : combineRhs S cert = -μd := by
      have := hμ.coeff 0
      rw [hgz, homSys, lincomb_cons] at this
      simp only [lincomb] at this
      rw [zipWith_map_right_sum] at this
      have e : (fun l c => l * SparseVec.coeff (homC c).a 0) =
          (fun (l : Int) (c : Constraint) => l * -c.rhs) := by
        funext l c
        simp only [homC, SparseVec.coeff_cons, coeff_shift_zero]
        simp
      rw [e, combineRhs_neg] at this
      simp [hden] at this
      omega
    have hstr := hμ.strict hgs
    rw [homSys, strictPos_cons, strictPos_homC] at hstr
    simp only [checkFarkas, Bool.and_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact List.all_eq_true.mpr (fun l hl => decide_eq_true (hnn l hl))
    · exact (SparseVec.isZero_iff_coeff_eq_zero _).mpr hlhs
    · unfold rhsContradicts
      rw [hrhs]
      cases hcs : combineStrict S cert
      · rw [hcs] at hstr
        simp [hden] at hstr
        simp; omega
      · simp; omega

end Motzkin
end Toy.Farkas
