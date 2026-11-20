import ToyFuelWP.Defs

/-!
# Main statements

The results of this module are stated over an arbitrary `System σ` and an
arbitrary postcondition `Q : σ → Prop`. Every statement is fully proved;
the corollaries in this module are derived from the main theorems by short
term-mode proofs. Examples, counterexamples, non-vacuity
witnesses, positive controls and boundary results live in
`ToyFuelWP.Examples`, `ToyFuelWP.Divergence`, `ToyFuelWP.Counterexamples`,
`ToyFuelWP.Boundaries` and `ToyFuelWP.Constructivity`, which do not import this
module and are fully proved.
-/

namespace Toy.FuelWP

universe u

variable {σ : Type u}

/-! ## Partial correctness: every fuel ⇔ greatest fixpoint (no branching assumption) -/

/-- **Greatest fixpoint implies every fuel.** If `s` satisfies the
greatest-fixpoint partial-correctness WP for `Q`, then `s` satisfies the
partial-correctness fuel WP for `Q` at every fuel `n`. No assumption on the
system. -/
theorem wpFuel_of_wpGfp (S : System σ) (Q : σ → Prop) (s : σ) (h : wpGfp S Q s) (n : Nat) :
    wpFuel S n Q s := by
  induction n generalizing s with
  | zero => trivial
  | succ n ih => exact wpStep_mono (fun t ht => ih t ht) ((wpGfp_unfold S Q s).mp h)

/-- **Every fuel implies greatest fixpoint.** If `s` satisfies the
partial-correctness fuel WP for `Q` at *every* fuel, then it satisfies the
greatest-fixpoint WP. No finite-branching or determinism assumption. -/
theorem wpGfp_of_forall_wpFuel (S : System σ) (Q : σ → Prop) (s : σ)
    (h : ∀ n, wpFuel S n Q s) : wpGfp S Q s :=
  ⟨fun t => ∀ n, wpFuel S n Q t,
    fun _ ht => ⟨(ht 1).1, fun hnt => ⟨((ht 1).2 hnt).1, fun u hu n => ((ht (n + 1)).2 hnt).2 u hu⟩⟩,
    h⟩

/-- **Partial correctness: fuel = gfp.** For every system, postcondition and
state, `(∀ n, wpFuel S n Q s) ↔ wpGfp S Q s`. (Corollary of the two
directions above.) -/
theorem forall_wpFuel_iff_wpGfp (S : System σ) (Q : σ → Prop) (s : σ) :
    (∀ n, wpFuel S n Q s) ↔ wpGfp S Q s :=
  ⟨wpGfp_of_forall_wpFuel S Q s, fun h n => wpFuel_of_wpGfp S Q s h n⟩

/-! ## Fuel monotonicity and the precise meaning of "verified at fuel `n`" -/

/-- **Partial-correctness fuel WP is antitone in fuel.** More fuel is a
stronger statement: if `n ≤ m` and `wpFuel S m Q s` then `wpFuel S n Q s`. -/
theorem wpFuel_antitone (S : System σ) (Q : σ → Prop) (s : σ) {n m : Nat} (hnm : n ≤ m)
    (h : wpFuel S m Q s) : wpFuel S n Q s := by
  induction n generalizing m s with
  | zero => trivial
  | succ n ih =>
    cases m with
    | zero => exact absurd hnm (Nat.not_succ_le_zero n)
    | succ m => exact wpStep_mono (fun t ht => ih t (Nat.le_of_succ_le_succ hnm) ht) h

/-- **Total-correctness fuel WP is monotone in fuel.** More fuel is a weaker
statement: if `n ≤ m` and `wpFuelTotal S n Q s` then `wpFuelTotal S m Q s`. -/
theorem wpFuelTotal_monotone (S : System σ) (Q : σ → Prop) (s : σ) {n m : Nat} (hnm : n ≤ m)
    (h : wpFuelTotal S n Q s) : wpFuelTotal S m Q s := by
  induction n generalizing m s with
  | zero => exact h.elim
  | succ n ih =>
    cases m with
    | zero => exact absurd hnm (Nat.not_succ_le_zero n)
    | succ m => exact wpStep_mono (fun t ht => ih t (Nat.le_of_succ_le_succ hnm) ht) h

/-- **What partial "verified at fuel `n`" means.** `wpFuel S n Q s` holds iff
every run prefix from `s` of fewer than `n` steps ends in a state that
satisfies `Q` if terminal and has a successor if not (`RunEndOk`). Nothing is
said about run prefixes of `n` or more steps. -/
theorem wpFuel_iff_forall_reach_lt (S : System σ) (n : Nat) (Q : σ → Prop) (s : σ) :
    wpFuel S n Q s ↔ ∀ k t, k < n → Reach S s k t → RunEndOk S Q t := by
  induction n generalizing s with
  | zero => exact ⟨fun _ _ _ hk => absurd hk (Nat.not_lt_zero _), fun _ => trivial⟩
  | succ n ih =>
    constructor
    · intro h k t hk hr
      cases hr with
      | refl _ => exact ⟨h.1, fun hnt => (h.2 hnt).1⟩
      | step hnt hst hr' =>
        exact (ih _).mp ((h.2 hnt).2 _ hst) _ _ (Nat.lt_of_succ_lt_succ hk) hr'
    · intro h
      have h0 := h 0 s (Nat.succ_pos n) (Reach.refl s)
      exact ⟨h0.1, fun hnt => ⟨h0.2 hnt, fun t hst => (ih t).mpr (fun k u hk hr =>
        h (k + 1) u (Nat.succ_lt_succ hk) (Reach.step hnt hst hr))⟩⟩

/-- **What total "verified at fuel `n`" means.** `wpFuelTotal S n Q s` holds
iff `wpFuel S n Q s` holds and no run prefix from `s` has exactly `n` steps
(nothing satisfies fuel `0`). -/
theorem wpFuelTotal_iff_wpFuel_and_no_reach (S : System σ) (n : Nat) (Q : σ → Prop) (s : σ) :
    wpFuelTotal S n Q s ↔ wpFuel S n Q s ∧ ∀ t, ¬ Reach S s n t := by
  induction n generalizing s with
  | zero => exact ⟨fun h => h.elim, fun ⟨_, hnr⟩ => hnr s (Reach.refl s)⟩
  | succ n ih =>
    constructor
    · intro h
      refine ⟨wpStep_mono (fun t ht => ((ih t).mp ht).1) h, fun u hr => ?_⟩
      cases hr with
      | step hnt hst hr' => exact ((ih _).mp ((h.2 hnt).2 _ hst)).2 u hr'
    · intro ⟨h1, h2⟩
      refine ⟨h1.1, fun hnt => ⟨(h1.2 hnt).1, fun t hst => (ih t).mpr ?_⟩⟩
      exact ⟨(h1.2 hnt).2 t hst, fun u hr => h2 u (Reach.step hnt hst hr)⟩

/-! ## Total correctness: fuel versus least fixpoint -/

/-- **Bounded fuel is sound for total correctness.** If `wpFuelTotal S n Q s`
for some `n`, then `wpLfp S Q s`. No assumption on the system. -/
theorem wpLfp_of_exists_wpFuelTotal (S : System σ) (Q : σ → Prop) (s : σ)
    (h : ∃ n, wpFuelTotal S n Q s) : wpLfp S Q s := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing s with
  | zero => exact hn.elim
  | succ n ih => exact wpLfp_preFixed S Q s (wpStep_mono (fun t ht => ih t ht) hn)

/-- **Total at some fuel implies partial (gfp).** If `wpFuelTotal S n Q s`
for some `n`, then `wpGfp S Q s`. (Corollary: `wpLfp S Q` is a fixed point,
hence a post-fixed point, of `wpStep S Q`.) -/
theorem wpGfp_of_wpFuelTotal (S : System σ) (n : Nat) (Q : σ → Prop) (s : σ)
    (h : wpFuelTotal S n Q s) : wpGfp S Q s :=
  ⟨wpLfp S Q, fun t ht => (wpLfp_unfold S Q t).mp ht, wpLfp_of_exists_wpFuelTotal S Q s ⟨n, h⟩⟩

/-- Helper: a finite list of successors that each have some total fuel bound
admits a common bound (the maximum). Used only in the proof of
`exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom`. -/
private theorem list_max_fuel {S : System σ} {Q : σ → Prop} {s : σ} (l : List σ)
    (hall : ∀ u, u ∈ l → S.step s u → ∃ n, wpFuelTotal S n Q u) :
    ∃ M, ∀ u, u ∈ l → S.step s u → wpFuelTotal S M Q u := by
  induction l with
  | nil => exact ⟨0, fun _ h => nomatch h⟩
  | cons a l ih =>
    obtain ⟨M, hM⟩ := ih (fun u hu => hall u (List.mem_cons_of_mem a hu))
    by_cases ha : S.step s a
    · obtain ⟨na, hna⟩ := hall a (List.mem_cons_self ..) ha
      refine ⟨max na M, fun u hu hsu => ?_⟩
      cases List.mem_cons.mp hu with
      | inl hEq =>
        subst hEq
        exact wpFuelTotal_monotone S Q u (Nat.le_max_left na M) hna
      | inr hMem =>
        exact wpFuelTotal_monotone S Q u (Nat.le_max_right na M) (hM u hMem hsu)
    · refine ⟨M, fun u hu hsu => ?_⟩
      cases List.mem_cons.mp hu with
      | inl hEq => subst hEq; exact absurd hsu ha
      | inr hMem => exact hM u hMem hsu

/-- **Bounded fuel is complete for total correctness under finite branching.**
If every non-terminal state reachable from `s` has finitely many successors,
then `wpLfp S Q s` implies `wpFuelTotal S n Q s` for some `n` (which depends
on `s`). -/
theorem exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom (S : System σ) (Q : σ → Prop)
    (s : σ) (hfb : FinitelyBranchingFrom S s) (h : wpLfp S Q s) :
    ∃ n, wpFuelTotal S n Q s := by
  have key : PreFixed S Q (fun t => FinitelyBranchingFrom S t → ∃ n, wpFuelTotal S n Q t) := by
    intro t ht hfb_t
    by_cases hterm : S.terminal t
    · exact ⟨1, fun _ => ht.1 hterm, fun hnt => absurd hterm hnt⟩
    · obtain ⟨l, hl⟩ := hfb_t.here hterm
      obtain ⟨M, hM⟩ := list_max_fuel (S := S) (Q := Q) (s := t) l (fun u _ htu =>
        (ht.2 hterm).2 u htu (hfb_t.succ hterm htu))
      refine ⟨M + 1, fun h => absurd h hterm, fun _ => ⟨(ht.2 hterm).1, fun u htu => ?_⟩⟩
      exact hM u (hl u htu) htu
  exact wpLfp_induction key h hfb

/-- Corollary (global finite branching): for a system in which every
non-terminal state is finitely branching, `(∃ n, wpFuelTotal S n Q s) ↔
wpLfp S Q s`. -/
theorem exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching (S : System σ) (Q : σ → Prop)
    (hfb : FinitelyBranching S) (s : σ) : (∃ n, wpFuelTotal S n Q s) ↔ wpLfp S Q s :=
  ⟨wpLfp_of_exists_wpFuelTotal S Q s,
    exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom S Q s
      (finitelyBranchingFrom_of_finitelyBranching hfb s)⟩

/-- Corollary (deterministic systems: every non-terminal state has at most one
successor): `(∃ n, wpFuelTotal S n Q s) ↔ wpLfp S Q s`. -/
theorem exists_wpFuelTotal_iff_wpLfp_of_deterministic (S : System σ) (Q : σ → Prop)
    (hdet : Deterministic S) (s : σ) : (∃ n, wpFuelTotal S n Q s) ↔ wpLfp S Q s :=
  exists_wpFuelTotal_iff_wpLfp_of_finitelyBranching S Q
    (finitelyBranching_of_deterministic hdet) s

/-- Corollary (interpreter step functions): for the system `ofStepFn next
halted` induced by a partial step function `next : σ → Option σ`,
`(∃ n, wpFuelTotal (ofStepFn next halted) n Q s) ↔ wpLfp (ofStepFn next halted) Q s`. -/
theorem exists_wpFuelTotal_iff_wpLfp_ofStepFn (next : σ → Option σ) (halted : σ → Prop)
    (Q : σ → Prop) (s : σ) :
    (∃ n, wpFuelTotal (ofStepFn next halted) n Q s) ↔ wpLfp (ofStepFn next halted) Q s :=
  exists_wpFuelTotal_iff_wpLfp_of_deterministic _ Q (ofStepFn_deterministic next halted) s

/-- **Total correctness decomposes as partial correctness plus termination.**
`wpLfp S Q s ↔ wpGfp S Q s ∧ ¬ HasInfiniteRun S s`. No branching
assumption. -/
theorem wpLfp_iff_wpGfp_and_not_hasInfiniteRun (S : System σ) (Q : σ → Prop) (s : σ) :
    wpLfp S Q s ↔ wpGfp S Q s ∧ ¬ HasInfiniteRun S s := by
  constructor
  · intro h
    refine ⟨⟨wpLfp S Q, fun t ht => (wpLfp_unfold S Q t).mp ht, h⟩, fun hinf => ?_⟩
    have key : PreFixed S Q (fun t => ¬ HasInfiniteRun S t) := by
      intro u hu ⟨f, hf0, hf⟩
      subst hf0
      exact (hu.2 (hf 0).1).2 (f 1) (hf 0).2 ⟨fun i => f (i + 1), rfl, fun i => hf (i + 1)⟩
    exact wpLfp_induction key h hinf
  · rintro ⟨hgfp, hnoinf⟩
    apply Classical.byContradiction
    intro hnotlfp
    let Bad (t : σ) : Prop := wpGfp S Q t ∧ ¬ wpLfp S Q t
    have hnotTerm : ∀ t, Bad t → ¬ S.terminal t := fun t ⟨hg, hnl⟩ hterm =>
      hnl (wpLfp_preFixed S Q t ⟨fun _ => ((wpGfp_unfold S Q t).mp hg).1 hterm,
        fun hnt => absurd hterm hnt⟩)
    have hnext : ∀ d : {t : σ // Bad t}, ∃ e : {t : σ // Bad t}, S.step d.1 e.1 := by
      intro ⟨t, hg, hnl⟩
      have hnt := hnotTerm t ⟨hg, hnl⟩
      have hunf := ((wpGfp_unfold S Q t).mp hg).2 hnt
      apply Classical.byContradiction
      intro hno
      apply hnl
      apply wpLfp_preFixed S Q t
      refine ⟨fun ht => absurd ht hnt, fun _ => ⟨hunf.1, fun u htu => ?_⟩⟩
      apply Classical.byContradiction
      intro hnu
      exact hno ⟨⟨u, hunf.2 u htu, hnu⟩, htu⟩
    let nx : {t : σ // Bad t} → {t : σ // Bad t} := fun d => Classical.choose (hnext d)
    let g : Nat → {t : σ // Bad t} := fun i =>
      Nat.rec (motive := fun _ => {t : σ // Bad t}) ⟨s, hgfp, hnotlfp⟩ (fun _ d => nx d) i
    exact hnoinf ⟨fun i => (g i).1, rfl, fun i =>
      ⟨hnotTerm (g i).1 (g i).2, Classical.choose_spec (hnext (g i))⟩⟩

/-- **König form.** If every non-terminal state reachable from `s` is finitely
branching, `s` satisfies the partial-correctness WP for `Q`, and no run from
`s` is infinite, then a single fuel bound `n` gives `wpFuelTotal S n Q s`.
(Corollary of `wpLfp_iff_wpGfp_and_not_hasInfiniteRun` and
`exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom`.) -/
theorem exists_wpFuelTotal_of_wpGfp_of_not_hasInfiniteRun_of_finitelyBranchingFrom
    (S : System σ) (Q : σ → Prop) (s : σ) (hfb : FinitelyBranchingFrom S s)
    (hsafe : wpGfp S Q s) (hfin : ¬ HasInfiniteRun S s) : ∃ n, wpFuelTotal S n Q s :=
  exists_wpFuelTotal_of_wpLfp_of_finitelyBranchingFrom S Q s hfb
    ((wpLfp_iff_wpGfp_and_not_hasInfiniteRun S Q s).mpr ⟨hsafe, hfin⟩)

/-! ## Adequacy of the greatest-fixpoint WP -/

/-- **Adequacy.** If `wpGfp S Q s`, then every finite run prefix from `s`
ends in a state that, if terminal, satisfies `Q`, and, if not terminal, has a
successor (the run is extendable). In particular no stuck state is reachable. -/
theorem wpGfp_adequacy (S : System σ) (Q : σ → Prop) (s : σ) (h : wpGfp S Q s) :
    ∀ k t, Reach S s k t → RunEndOk S Q t := by
  intro k t hr
  obtain ⟨X, hX, hs⟩ := h
  have ht := hX t (hX.reach hs hr)
  exact ⟨ht.1, fun hn => (ht.2 hn).1⟩

/-- **Converse of adequacy.** If every finite run prefix from `s` ends in a
state satisfying `RunEndOk S Q`, then `wpGfp S Q s`. -/
theorem wpGfp_of_forall_reach_runEndOk (S : System σ) (Q : σ → Prop) (s : σ)
    (h : ∀ k t, Reach S s k t → RunEndOk S Q t) : wpGfp S Q s :=
  ⟨fun u => ∀ k t, Reach S u k t → RunEndOk S Q t,
    fun u hu => ⟨(hu 0 u (Reach.refl u)).1, fun hnt =>
      ⟨(hu 0 u (Reach.refl u)).2 hnt, fun _v huv k t hr => hu (k + 1) t (Reach.step hnt huv hr)⟩⟩,
    h⟩

/-- Corollary: `wpGfp S Q s` is exactly "every finite run prefix from `s` is
acceptable" — partial correctness is a property of finite run prefixes only. -/
theorem wpGfp_iff_forall_reach_runEndOk (S : System σ) (Q : σ → Prop) (s : σ) :
    wpGfp S Q s ↔ ∀ k t, Reach S s k t → RunEndOk S Q t :=
  ⟨wpGfp_adequacy S Q s, wpGfp_of_forall_reach_runEndOk S Q s⟩

end Toy.FuelWP
