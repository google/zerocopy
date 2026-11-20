/-
Toy.SCT.Infinite
================

The finiteness of the function set (`Fin nf`) and of the parameter set (`Fin k`) is built into
`SCG nf k`. This module shows that both are needed, in a generalized model `SCGInf F K` with
arbitrary function type `F` and parameter type `K`, whose composition (`SCGInf.comp`, relational:
strict if some intermediate parameter gives a strict thread step, else nonstrict if some gives a
present one) agrees with `SCG.comp` on finite types (`SCG.toInf_comp`).

* infinitely many functions: the criterion holds vacuously but there is an infinite consistent run
  (`infinite_functions_counterexample`);
* infinitely many parameters: the criterion holds vacuously but there is an infinite consistent run
  (`infinite_params_soundness_counterexample`), and an idempotent loop without self-arcs coexists
  with size-change termination and with the absence of consistent runs
  (`infinite_params_converse_exactness_counterexample`);
* model-level forms of the two soundness counterexamples, for semantic call relations
  (`infinite_functions_model_counterexample`, `infinite_params_model_counterexample`).

On finite types the generalized model agrees with the package's model
(`inClosure_iff_inClosureInf`, `closureCriterion_iff_closureCriterionInf`,
`sizeChangeTerminating_iff_sizeChangeTerminatingInf`, `consistentRunIn_nat_iff_consistentRunInf`,
`stepRespects_iff_stepRespectsInf`).
-/
import Toy.SCT.Examples
import Toy.SCT.Threads

namespace Toy.SCT

/-- Size-change graphs over an arbitrary function type `F` and parameter type `K`. -/
structure SCGInf (F K : Type) where
  src : F
  dst : F
  lab : K → K → Label

theorem SCGInf.ext {F K : Type} {G H : SCGInf F K}
    (hs : G.src = H.src) (hd : G.dst = H.dst) (hl : ∀ i j, G.lab i j = H.lab i j) : G = H := by
  cases G; cases H; simp only at hs hd hl
  subst hs; subst hd
  have : _ = _ := funext fun i => funext fun j => hl i j
  subst this; rfl

/-- Relational composition: strict if some intermediate parameter gives a strict thread step; else
nonstrict if some intermediate parameter gives a present one; else absent. -/
noncomputable def SCGInf.comp {F K : Type} (G H : SCGInf F K) : SCGInf F K :=
  open Classical in
  { src := G.src
    dst := H.dst
    lab := fun i j =>
      if ∃ m, Label.seq (G.lab i m) (H.lab m j) = .strict then .strict
      else if ∃ m, Label.seq (G.lab i m) (H.lab m j) = .nonstrict then .nonstrict
      else .absent }

/-- The embedding of `SCG nf k` into the generalized model. -/
def SCG.toInf {nf k : Nat} (G : SCG nf k) : SCGInf (Fin nf) (Fin k) := ⟨G.src, G.dst, G.lab⟩

/-- On finite types the relational composition is the package's composition. -/
theorem SCG.toInf_comp {nf k : Nat} (G H : SCG nf k) : (G.comp H).toInf = G.toInf.comp H.toInf := by
  refine SCGInf.ext rfl rfl fun i j => ?_
  show (G.compWith Label.seq H).lab i j = (G.toInf.comp H.toInf).lab i j
  simp only [SCGInf.comp]
  split
  · next hA =>
    obtain ⟨m, hm⟩ := hA
    exact (SCG.comp_lab_eq_strict G H i j).mpr ⟨m, (Label.seq_eq_strict _ _).mp hm⟩
  · next hA =>
    have hns : (G.compWith Label.seq H).lab i j ≠ .strict := fun h => by
      obtain ⟨m, hm⟩ := (SCG.comp_lab_eq_strict G H i j).mp h
      exact hA ⟨m, (Label.seq_eq_strict _ _).mpr hm⟩
    split
    · next hB =>
      obtain ⟨m, hm⟩ := hB
      have hm' : Label.seq (G.lab i m) (H.lab m j) = .nonstrict := hm
      have hpres : (G.compWith Label.seq H).lab i j ≠ .absent :=
        (SCG.comp_lab_ne_absent G H i j).mpr ⟨m, (Label.seq_ne_absent _ _).mp (by rw [hm']; decide)⟩
      revert hns hpres
      cases (G.compWith Label.seq H).lab i j <;> decide
    · next hB =>
      refine Classical.byContradiction fun h => ?_
      obtain ⟨m, hm⟩ := (SCG.comp_lab_ne_absent G H i j).mp (fun h' => h h')
      have hne := (Label.seq_ne_absent _ _).mpr hm
      have hA' : ¬ Label.seq (G.lab i m) (H.lab m j) = .strict := fun e => hA ⟨m, e⟩
      have hB' : ¬ Label.seq (G.lab i m) (H.lab m j) = .nonstrict := fun e => hB ⟨m, e⟩
      revert hne hA' hB'
      cases Label.seq (G.lab i m) (H.lab m j) <;> simp

inductive InClosureInf {F K : Type} (calls : SCGInf F K → Prop) : SCGInf F K → Prop where
  | gen {G} : calls G → InClosureInf calls G
  | comp {G H} : InClosureInf calls G → InClosureInf calls H → G.dst = H.src →
      InClosureInf calls (G.comp H)

/-- The closure criterion in the generalized model. -/
def ClosureCriterionInf {F K : Type} (calls : SCGInf F K → Prop) : Prop :=
  ∀ G, InClosureInf calls G → G.src = G.dst → G.comp G = G → ∃ i : K, G.lab i i = .strict

def RespectsInf {F K : Type} (G : SCGInf F K) (u v : K → Nat) : Prop :=
  ∀ i j, (G.lab i j = .strict → v j < u i) ∧ (G.lab i j = .nonstrict → v j ≤ u i)

/-- An infinite consistent run over `Nat` in the generalized model. -/
def ConsistentRunInf {F K : Type} (calls : SCGInf F K → Prop) : Prop :=
  ∃ (fs : Nat → F) (vs : Nat → K → Nat) (Gs : Nat → SCGInf F K),
    ∀ n, calls (Gs n) ∧ (Gs n).src = fs n ∧ (Gs n).dst = fs (n + 1) ∧
      RespectsInf (Gs n) (vs n) (vs (n + 1))

/-- Size-change termination in the generalized model. -/
def SizeChangeTerminatingInf {F K : Type} (calls : SCGInf F K → Prop) : Prop :=
  ∀ Gs : Nat → SCGInf F K,
    (∀ n, calls (Gs n) ∧ (Gs n).dst = (Gs (n + 1)).src) →
    ∃ (n0 : Nat) (p : Nat → K),
      (∀ n, n0 ≤ n → (Gs n).lab (p n) (p (n + 1)) ≠ .absent) ∧
      (∀ N, ∃ n, N ≤ n ∧ n0 ≤ n ∧ (Gs n).lab (p n) (p (n + 1)) = .strict)

/-! ### Infinitely many functions -/

/-- `f_n` calls `f_{n+1}`, with no size information. -/
def infFnCalls : SCGInf Nat (Fin 1) → Prop :=
  fun G => G.dst = G.src + 1 ∧ G.lab = fun _ _ => .absent

/-- With infinitely many functions (`F = Nat`) and one parameter, every closure graph goes from
`f_m` to some `f_n` with `m < n`, so there are no loops and the criterion holds vacuously; yet the
program is not size-change terminating and has an infinite consistent run. -/
theorem infinite_functions_counterexample :
    ClosureCriterionInf infFnCalls ∧ ¬ SizeChangeTerminatingInf infFnCalls ∧
    ConsistentRunInf infFnCalls := by
  have hlt : ∀ G, InClosureInf infFnCalls G → G.src < G.dst := by
    intro G hG
    induction hG with
    | gen h => have := h.1; omega
    | comp _ _ hdst ihG ihH => simp [SCGInf.comp]; omega
  refine ⟨fun G hG hloop => absurd hloop (Nat.ne_of_lt (hlt G hG)), ?_, ?_⟩
  · intro hsct
    let Gs : Nat → SCGInf Nat (Fin 1) := fun n => ⟨n, n + 1, fun _ _ => .absent⟩
    obtain ⟨n0, p, hpres, _⟩ := hsct Gs (fun n => ⟨⟨rfl, rfl⟩, rfl⟩)
    exact hpres n0 (Nat.le_refl _) rfl
  · exact ⟨fun n => n, fun _ _ => 0, fun n => ⟨n, n + 1, fun _ _ => .absent⟩,
      fun n => ⟨⟨rfl, rfl⟩, rfl, rfl, fun _ _ => ⟨by simp, by simp⟩⟩⟩

/-! ### Infinitely many parameters: soundness -/

/-- The shift graph: parameter `i` is passed, unchanged or smaller, to position `i + d`. -/
def shiftG (d : Nat) : SCGInf (Fin 1) Nat :=
  ⟨f0, f0, fun i j => if j = i + d then .nonstrict else .absent⟩

def shiftCalls : SCGInf (Fin 1) Nat → Prop := fun G => G = shiftG 1

theorem shiftG_comp (d1 d2 : Nat) : (shiftG d1).comp (shiftG d2) = shiftG (d1 + d2) := by
  refine SCGInf.ext rfl rfl fun i j => ?_
  dsimp only [SCGInf.comp]
  split
  · next hstr =>
    obtain ⟨m, hm⟩ := hstr
    simp only [shiftG] at hm
    split at hm <;> split at hm <;> simp [Label.seq] at hm
  · split
    · next hns =>
      obtain ⟨m, hm⟩ := hns
      simp only [shiftG] at hm ⊢
      by_cases h1 : m = i + d1
      · by_cases h2 : j = m + d2
        · have hij : j = i + (d1 + d2) := by omega
          simp [hij]
        · simp [h2] at hm; simp [h1, Label.seq] at hm
      · simp [h1, Label.seq] at hm
    · next hno =>
      simp only [shiftG]
      by_cases hij : j = i + (d1 + d2)
      · exfalso
        apply hno
        refine ⟨i + d1, ?_⟩
        simp [shiftG, hij, Nat.add_assoc, Label.seq]
      · simp [hij]

/-- With one function and infinitely many parameters (`K = Nat`), the single call passing each
parameter to the next position has a closure of shifts by `d ≥ 1`, none idempotent, so the
criterion holds vacuously; yet the program is not size-change terminating and has an infinite
consistent run. -/
theorem infinite_params_soundness_counterexample :
    ClosureCriterionInf shiftCalls ∧ ¬ SizeChangeTerminatingInf shiftCalls ∧
    ConsistentRunInf shiftCalls := by
  have hcl : ∀ G, InClosureInf shiftCalls G → ∃ d ≥ 1, G = shiftG d := by
    intro G hG
    induction hG with
    | gen h => exact ⟨1, Nat.le_refl _, h⟩
    | comp _ _ _ ihG ihH =>
      obtain ⟨d1, hd1, rfl⟩ := ihG
      obtain ⟨d2, hd2, rfl⟩ := ihH
      exact ⟨d1 + d2, by omega, shiftG_comp d1 d2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro G hG _ hidem
    obtain ⟨d, hd, rfl⟩ := hcl G hG
    rw [shiftG_comp] at hidem
    have h0 := congrFun (congrFun (congrArg SCGInf.lab hidem) 0) d
    dsimp only [shiftG] at h0
    have hne : ¬ (d = d + d) := by omega
    simp only [Nat.zero_add, hne, ite_false, ite_true] at h0
    cases h0
  · intro hsct
    obtain ⟨n0, p, _, hstr⟩ := hsct (fun _ => shiftG 1) (fun _ => ⟨rfl, rfl⟩)
    obtain ⟨n, _, _, hl⟩ := hstr 0
    simp only [shiftG] at hl
    split at hl <;> cases hl
  · refine ⟨fun _ => f0, fun _ _ => 0, fun _ => shiftG 1,
      fun _ => ⟨rfl, rfl, rfl, fun i j => ?_⟩⟩
    simp only [shiftG]
    split <;> exact ⟨by simp, by simp⟩

/-! ### Infinitely many parameters: converse and exactness -/

/-- The order of nonnegative rationals `a / (b + 1)` on pairs `(a, b)`. -/
def ratLt (p q : Nat × Nat) : Prop := p.1 * (q.2 + 1) < q.1 * (p.2 + 1)

instance (p q : Nat × Nat) : Decidable (ratLt p q) :=
  inferInstanceAs (Decidable (p.1 * (q.2 + 1) < q.1 * (p.2 + 1)))

theorem ratLt_trans {p q r : Nat × Nat} (h1 : ratLt p q) (h2 : ratLt q r) : ratLt p r := by
  unfold ratLt at *
  have h1' : p.1 * (q.2 + 1) * (r.2 + 1) < q.1 * (p.2 + 1) * (r.2 + 1) :=
    Nat.mul_lt_mul_of_pos_right h1 (Nat.succ_pos _)
  have h2' : q.1 * (r.2 + 1) * (p.2 + 1) < r.1 * (q.2 + 1) * (p.2 + 1) :=
    Nat.mul_lt_mul_of_pos_right h2 (Nat.succ_pos _)
  have hmul : p.1 * (r.2 + 1) * (q.2 + 1) < r.1 * (p.2 + 1) * (q.2 + 1) := by
    have e1 : p.1 * (r.2 + 1) * (q.2 + 1) = p.1 * (q.2 + 1) * (r.2 + 1) := by
      rw [Nat.mul_right_comm]
    have e2 : q.1 * (p.2 + 1) * (r.2 + 1) = q.1 * (r.2 + 1) * (p.2 + 1) := by
      rw [Nat.mul_right_comm]
    have e3 : r.1 * (q.2 + 1) * (p.2 + 1) = r.1 * (p.2 + 1) * (q.2 + 1) := by
      rw [Nat.mul_right_comm]
    rw [e1, ← e3]
    exact Nat.lt_trans h1' (e2 ▸ h2')
  exact Nat.lt_of_mul_lt_mul_right hmul

theorem ratLt_dense {p r : Nat × Nat} (h : ratLt p r) :
    ∃ q : Nat × Nat, ratLt p q ∧ ratLt q r := by
  refine ⟨(p.1 * (r.2 + 1) + r.1 * (p.2 + 1), 2 * (p.2 + 1) * (r.2 + 1) - 1), ?_, ?_⟩
  · unfold ratLt at *
    have hsub : 2 * (p.2 + 1) * (r.2 + 1) - 1 + 1 = 2 * (p.2 + 1) * (r.2 + 1) := by
      have : 0 < 2 * (p.2 + 1) * (r.2 + 1) :=
        Nat.mul_pos (Nat.mul_pos (by omega) (Nat.succ_pos _)) (Nat.succ_pos _)
      omega
    rw [hsub]
    have h1 : p.1 * (2 * (p.2 + 1) * (r.2 + 1)) =
        p.1 * (r.2 + 1) * (p.2 + 1) + p.1 * (r.2 + 1) * (p.2 + 1) := by
      have : p.1 * (2 * (p.2 + 1) * (r.2 + 1)) = 2 * (p.1 * (r.2 + 1) * (p.2 + 1)) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [this, Nat.two_mul]
    have h2 : (p.1 * (r.2 + 1) + r.1 * (p.2 + 1)) * (p.2 + 1) =
        p.1 * (r.2 + 1) * (p.2 + 1) + r.1 * (p.2 + 1) * (p.2 + 1) := by
      rw [Nat.add_mul]
    rw [h1, h2]
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos _)) _
  · unfold ratLt at *
    have hsub : 2 * (p.2 + 1) * (r.2 + 1) - 1 + 1 = 2 * (p.2 + 1) * (r.2 + 1) := by
      have : 0 < 2 * (p.2 + 1) * (r.2 + 1) :=
        Nat.mul_pos (Nat.mul_pos (by omega) (Nat.succ_pos _)) (Nat.succ_pos _)
      omega
    rw [hsub]
    have h1 : (p.1 * (r.2 + 1) + r.1 * (p.2 + 1)) * (r.2 + 1) =
        p.1 * (r.2 + 1) * (r.2 + 1) + r.1 * (p.2 + 1) * (r.2 + 1) := by
      rw [Nat.add_mul]
    have h2 : r.1 * (2 * (p.2 + 1) * (r.2 + 1)) =
        r.1 * (p.2 + 1) * (r.2 + 1) + r.1 * (p.2 + 1) * (r.2 + 1) := by
      have : r.1 * (2 * (p.2 + 1) * (r.2 + 1)) = 2 * (r.1 * (p.2 + 1) * (r.2 + 1)) := by
        simp only [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      rw [this, Nat.two_mul]
    rw [h1, h2]
    exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right h (Nat.succ_pos _)) _

/-- One loop graph over parameters `Nat × Nat`, with a strict arc `p → q` exactly when
`p < q` as rationals (a dense strict order). -/
def denseG : SCGInf (Fin 1) (Nat × Nat) :=
  ⟨f0, f0, fun p q => if ratLt p q then .strict else .absent⟩

def denseCalls : SCGInf (Fin 1) (Nat × Nat) → Prop := fun G => G = denseG

theorem denseG_idem : denseG.comp denseG = denseG := by
  refine SCGInf.ext rfl rfl fun p q => ?_
  dsimp only [SCGInf.comp]
  split
  · next hstr =>
    obtain ⟨m, hm⟩ := hstr
    simp only [denseG] at hm ⊢
    by_cases h1 : ratLt p m
    · by_cases h2 : ratLt m q
      · simp [ratLt_trans h1 h2]
      · simp [h1, h2, Label.seq] at hm
    · simp [h1, Label.seq] at hm
  · split
    · next hns =>
      obtain ⟨m, hm⟩ := hns
      simp only [denseG] at hm
      split at hm <;> split at hm <;> simp [Label.seq] at hm
    · next hno _ =>
      dsimp only [denseG]
      by_cases hpq : ratLt p q
      · exfalso
        apply hno
        obtain ⟨m, hm1, hm2⟩ := ratLt_dense hpq
        exact ⟨m, by simp [denseG, hm1, hm2, Label.seq]⟩
      · simp [hpq]

/-- With infinitely many parameters, an idempotent loop graph without any self-arc (so the
criterion fails) coexists with size-change termination and with the absence of infinite
consistent runs over `Nat`: both the converse of the characterization and exactness need finitely
many parameters. -/
theorem infinite_params_converse_exactness_counterexample :
    ¬ ClosureCriterionInf denseCalls ∧ SizeChangeTerminatingInf denseCalls ∧
    ¬ ConsistentRunInf denseCalls := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    obtain ⟨p, hp⟩ := h denseG (.gen rfl) rfl denseG_idem
    simp only [denseG, ratLt, Nat.lt_irrefl, ite_false] at hp
    cases hp
  · intro Gs hpath
    have hG : ∀ n, Gs n = denseG := fun n => (hpath n).1
    refine ⟨0, fun n => (n, 0), fun n _ => ?_, fun N => ⟨N, Nat.le_refl _, Nat.zero_le _, ?_⟩⟩
    · rw [hG n]; simp [denseG, ratLt]
    · rw [hG N]; simp [denseG, ratLt]
  · rintro ⟨fs, vs, Gs, hrun⟩
    apply nat_no_infinite_descent (fun n => vs n (n, 0))
    intro n
    obtain ⟨hG, -, -, hr⟩ := hrun n
    rw [hG] at hr
    have hlt : denseG.lab (n, 0) (n + 1, 0) = .strict := by simp [denseG, ratLt]
    exact (hr (n, 0) (n + 1, 0)).1 hlt

/-! ### The generalized model restricted to finite types

On `Fin nf` functions and `Fin k` parameters the generalized model is the package's model: closure
membership, the closure criterion, size-change termination and consistent runs over `Nat` all
agree with their `SCG nf k` counterparts. So the counterexamples above vary only the finiteness of
the function and parameter types. -/

/-- The inverse of `SCG.toInf`. -/
def SCGInf.toSCG {nf k : Nat} (G : SCGInf (Fin nf) (Fin k)) : SCG nf k := ⟨G.src, G.dst, G.lab⟩

theorem SCGInf.toSCG_toInf {nf k : Nat} (G : SCG nf k) : G.toInf.toSCG = G := by
  cases G; rfl

theorem SCGInf.toInf_toSCG {nf k : Nat} (G : SCGInf (Fin nf) (Fin k)) : G.toSCG.toInf = G := by
  cases G; rfl

theorem SCG.toInf_injective {nf k : Nat} {G H : SCG nf k} (h : G.toInf = H.toInf) : G = H := by
  have := congrArg SCGInf.toSCG h
  rwa [SCGInf.toSCG_toInf, SCGInf.toSCG_toInf] at this

theorem SCGInf.toSCG_comp {nf k : Nat} (G H : SCGInf (Fin nf) (Fin k)) :
    (G.comp H).toSCG = G.toSCG.comp H.toSCG := by
  apply SCG.toInf_injective
  rw [SCGInf.toInf_toSCG, SCG.toInf_comp, SCGInf.toInf_toSCG, SCGInf.toInf_toSCG]

/-- The call-site predicate of a program, in the generalized model. -/
def progCallsInf {nf k : Nat} (P : Prog nf k) : SCGInf (Fin nf) (Fin k) → Prop :=
  fun G => G.toSCG ∈ P.calls

theorem inClosure_iff_inClosureInf {nf k : Nat} (P : Prog nf k) (G : SCG nf k) :
    InClosure P G ↔ InClosureInf (progCallsInf P) G.toInf := by
  constructor
  · intro h
    induction h with
    | gen hm =>
      exact .gen (by simpa [progCallsInf, SCGInf.toSCG_toInf] using hm)
    | comp _ _ hdst ihG ihH =>
      change InClosureInf (progCallsInf P) (SCG.comp _ _).toInf
      rw [SCG.toInf_comp]
      exact .comp ihG ihH hdst
  · intro h
    have key : ∀ X, InClosureInf (progCallsInf P) X → InClosure P X.toSCG := by
      intro X hX
      induction hX with
      | gen hm => exact .gen hm
      | comp _ _ hdst ihG ihH =>
        rw [SCGInf.toSCG_comp]
        exact .comp ihG ihH hdst
    simpa [SCGInf.toSCG_toInf] using key G.toInf h

theorem closureCriterion_iff_closureCriterionInf {nf k : Nat} (P : Prog nf k) :
    ClosureCriterion P ↔ ClosureCriterionInf (progCallsInf P) := by
  constructor
  · intro h G hG hloop hidem
    have hG' : InClosure P G.toSCG := by
      rw [inClosure_iff_inClosureInf, SCGInf.toInf_toSCG]
      exact hG
    have hidem' : G.toSCG.comp G.toSCG = G.toSCG := by
      rw [← SCGInf.toSCG_comp, hidem]
    exact h G.toSCG hG' hloop hidem'
  · intro h G hG hloop hidem
    have hG' : InClosureInf (progCallsInf P) G.toInf := (inClosure_iff_inClosureInf P G).mp hG
    have hidem' : G.toInf.comp G.toInf = G.toInf := by
      rw [← SCG.toInf_comp]
      exact congrArg SCG.toInf hidem
    exact h G.toInf hG' hloop hidem'

theorem sizeChangeTerminating_iff_sizeChangeTerminatingInf {nf k : Nat} (P : Prog nf k) :
    SizeChangeTerminating P ↔ SizeChangeTerminatingInf (progCallsInf P) := by
  constructor
  · intro h Gs hpath
    have hpath' : IsCallPath P (fun n => (Gs n).toSCG) :=
      fun n => ⟨(hpath n).1, (hpath n).2⟩
    exact h _ hpath'
  · intro h Gs hpath
    have hpath' : ∀ n, progCallsInf P (Gs n).toInf ∧ (Gs n).toInf.dst = (Gs (n + 1)).toInf.src :=
      fun n => ⟨by simpa [progCallsInf, SCGInf.toSCG_toInf] using (hpath n).1, (hpath n).2⟩
    exact h _ hpath'

theorem consistentRunIn_nat_iff_consistentRunInf {nf k : Nat} (P : Prog nf k) :
    ConsistentRunIn Nat P ↔ ConsistentRunInf (progCallsInf P) := by
  constructor
  · rintro ⟨fs, vs, Gs, hrun⟩
    refine ⟨fs, vs, fun n => (Gs n).toInf, fun n => ?_⟩
    obtain ⟨hm, hs, hd, hr⟩ := hrun n
    exact ⟨by simpa [progCallsInf, SCGInf.toSCG_toInf] using hm, hs, hd, hr⟩
  · rintro ⟨fs, vs, Gs, hrun⟩
    refine ⟨fs, vs, fun n => (Gs n).toSCG, fun n => ?_⟩
    obtain ⟨hm, hs, hd, hr⟩ := hrun n
    exact ⟨hm, hs, hd, hr⟩

/-! ### Semantic models in the generalized model -/

/-- `StepRespects` in the generalized model: every call of `step` (on states made of a function
and a `Nat`-valued argument vector indexed by `K`) is justified by some call-site graph with
matching endpoints that the call respects. -/
def StepRespectsInf {F K : Type} (calls : SCGInf F K → Prop)
    (step : (F × (K → Nat)) → (F × (K → Nat)) → Prop) : Prop :=
  ∀ s t, step s t → ∃ G, calls G ∧ G.src = s.1 ∧ G.dst = t.1 ∧ RespectsInf G s.2 t.2

/-- The most permissive semantic model of a generalized program. -/
def runStepInf {F K : Type} (calls : SCGInf F K → Prop) :
    (F × (K → Nat)) → (F × (K → Nat)) → Prop :=
  fun s t => ∃ G, calls G ∧ G.src = s.1 ∧ G.dst = t.1 ∧ RespectsInf G s.2 t.2

theorem stepRespects_iff_stepRespectsInf {nf k : Nat} (P : Prog nf k)
    (step : State nf k → State nf k → Prop) :
    StepRespects P step ↔ StepRespectsInf (progCallsInf P) step := by
  constructor
  · intro h s t hst
    obtain ⟨G, hG, hs, hd, hr⟩ := h s t hst
    exact ⟨G.toInf, by simpa [progCallsInf, SCGInf.toSCG_toInf] using hG, hs, hd, hr⟩
  · intro h s t hst
    obtain ⟨G, hG, hs, hd, hr⟩ := h s t hst
    exact ⟨G.toSCG, hG, hs, hd, hr⟩

/-- Model-level form of `infinite_functions_counterexample` (finiteness of the function set in
`terminates_of_stepRespects_of_closureCriterion`): with infinitely many functions, the most
permissive model respects the graphs and the criterion holds, yet the model does not terminate. -/
theorem infinite_functions_model_counterexample :
    StepRespectsInf infFnCalls (runStepInf infFnCalls) ∧
    ClosureCriterionInf infFnCalls ∧
    ¬ Terminates (runStepInf infFnCalls) := by
  refine ⟨fun _ _ h => h, infinite_functions_counterexample.1, ?_⟩
  intro hT
  obtain ⟨fs, vs, Gs, hrun⟩ := infinite_functions_counterexample.2.2
  exact hT ⟨fun n => (fs n, vs n), fun n => ⟨Gs n, hrun n⟩⟩

/-- Model-level form of `infinite_params_soundness_counterexample` (finiteness of the parameter
slots in `terminates_of_stepRespects_of_closureCriterion`): with infinitely many parameters, the
most permissive model respects the graphs and the criterion holds, yet the model does not
terminate. -/
theorem infinite_params_model_counterexample :
    StepRespectsInf shiftCalls (runStepInf shiftCalls) ∧
    ClosureCriterionInf shiftCalls ∧
    ¬ Terminates (runStepInf shiftCalls) := by
  refine ⟨fun _ _ h => h, infinite_params_soundness_counterexample.1, ?_⟩
  intro hT
  obtain ⟨fs, vs, Gs, hrun⟩ := infinite_params_soundness_counterexample.2.2
  exact hT ⟨fun n => (fs n, vs n), fun n => ⟨Gs n, hrun n⟩⟩

end Toy.SCT
