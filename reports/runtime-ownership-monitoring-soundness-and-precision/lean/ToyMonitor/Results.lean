import ToyMonitor.Lemmas

/-!
# Results: soundness, completeness, and the assumptions of a run-time ownership monitor

Main results, the counterexamples showing their hypotheses necessary, non-vacuity
witnesses (all hypotheses of a result hold in a concrete instance), and positive controls
for the impossibility result.
-/

namespace Toy.Monitor

open Assn

/-! ## Concrete programs used by the counterexamples and witnesses -/

/-- A callee given `owned 0` that, through an unannotated helper, stores `5` at byte `0`
and returns `pointsTo 0 5`. -/
def progNV : Prog := .call (owned 0) (pointsTo 0 5) (.unannot (.write 0 5))

/-- A callee whose precondition is the precise disjunction `pointsTo 0 0 ∨ pointsTo 0 1`. -/
def progOr : Prog := .call (.or (pointsTo 0 0) (pointsTo 0 1)) (pointsTo 0 1) (.write 0 1)

/-- A callee whose precondition `pointsTo 0 1` is false in `hOne` (byte `0` holds `0`). -/
def runBad : Prog := .call (pointsTo 0 1) (owned 0) .skip

/-- A callee given `owned 0` that returns only `emp` (it leaks byte `0`). -/
def runLeak : Prog := .call (owned 0) .emp .skip

/-- A leaking callee followed by a sibling callee, given only `owned 1`, that reads byte `0`. -/
def runStale : Prog := .seq (.call (owned 0) .emp .skip) (.call (owned 1) (owned 1) (.read 0))

/-- A callee given `owned 0` that calls an unannotated helper storing `7` at byte `1`,
a byte its caller kept. -/
def runTrusted : Prog := .call (owned 0) (owned 0) (.unannot (.write 1 7))

/-- A callee given `owned 0` whose unannotated helper stores `5` at byte `0` (inside the
callee's footprint) and then calls an annotated function that is given `owned 0`, reads
byte `0`, and returns `pointsTo 0 5`. Exercises both instrumentation modes. -/
def progMixed : Prog :=
  .call (owned 0) (owned 0)
    (.unannot (.seq (.write 0 5) (.call (owned 0) (pointsTo 0 5) (.read 0))))

/-! ## Helper facts for the concrete instances -/

theorem frag_initOwn_hTwo : frag hTwo (initOwn [0, 1]) 0 = hTwo.restrict [0, 1] := by
  funext a
  simp only [frag, initOwn, Heap.restrict]
  by_cases h : a ∈ [0, 1] <;> simp [h]

theorem frag_initOwn_hOne : frag hOne (initOwn [0]) 0 = hOne.restrict [0] := by
  funext a
  simp only [frag, initOwn, Heap.restrict]
  by_cases h : a ∈ [0] <;> simp [h]

/-- Shape of any fragment satisfying `C'`: exactly the two cells `0` and `1`. -/
theorem sat_C'_shape (g : Heap) (h : sat C' g) :
    (g 0).isSome = true ∧ (g 1).isSome = true ∧ ∀ a, a ≠ 0 → a ≠ 1 → g a = none := by
  obtain ⟨g₁, g₂, hdisj, hunion, hor, h₂⟩ := h
  obtain ⟨h₂1, h₂r⟩ := (sat_owned_iff 1 g₂).1 h₂
  rcases hor with hl | hr
  · -- left disjunct: g₁ contains byte 1, as does g₂: impossible
    exfalso
    obtain ⟨u₁, u₂, -, hu, hu₁, hu₂⟩ := hl
    obtain ⟨-, hu₁r⟩ := (sat_owned_iff 0 u₁).1 hu₁
    obtain ⟨hu₂1, -⟩ := (sat_owned_iff 1 u₂).1 hu₂
    have hg₁1 : (g₁ 1).isSome = true := by
      rw [hu 1]; simp [hu₁r 1 (by decide), hu₂1]
    rcases hdisj 1 with e | e
    · simp [e] at hg₁1
    · simp [e] at h₂1
  · obtain ⟨hg₁0, hg₁r⟩ := (sat_owned_iff 0 g₁).1 hr
    refine ⟨?_, ?_, ?_⟩
    · rw [hunion 0]
      cases e : g₁ 0 with
      | none => simp [e] at hg₁0
      | some v => simp [e]
    · rw [hunion 1]; simp [hg₁r 1 (by decide), h₂1]
    · intro a h0 h1
      rw [hunion a]; simp [hg₁r a h0, h₂r a h1]

/-- Any two-cell fragment on `{0, 1}` satisfies `C'`. -/
theorem sat_C'_of_shape (g : Heap) (h0 : (g 0).isSome = true) (h1 : (g 1).isSome = true)
    (hr : ∀ a, a ≠ 0 → a ≠ 1 → g a = none) : sat C' g := by
  refine ⟨g.restrict [0], g.restrict [1], ?_, ?_, Or.inr ?_, ?_⟩
  · intro a
    by_cases ha : a = 0
    · subst ha; right; simp
    · left; simp [ha]
  · intro a
    by_cases ha0 : a = 0
    · subst ha0
      cases e : g 0 with
      | none => simp [e] at h0
      | some v => simp [e]
    · by_cases ha1 : a = 1
      · subst ha1; simp
      · simp [ha0, ha1, hr a ha0 ha1]
  · exact (sat_owned_iff 0 _).2 ⟨by simpa using h0, fun a ha => by simp [ha]⟩
  · exact (sat_owned_iff 1 _).2 ⟨by simpa using h1, fun a ha => by simp [ha]⟩

/-- `C'` is precise. -/
theorem precise_C' : Precise C' := by
  intro g g₁ g₂ hs₁ hs₂ h₁ h₂
  obtain ⟨a0, a1, ar⟩ := sat_C'_shape g₁ h₁
  obtain ⟨b0, b1, br⟩ := sat_C'_shape g₂ h₂
  have agree : ∀ x, (g₁ x).isSome = true → (g₂ x).isSome = true → g₁ x = g₂ x := by
    intro x hx hy
    cases e₁ : g₁ x with
    | none => simp [e₁] at hx
    | some v =>
      cases e₂ : g₂ x with
      | none => simp [e₂] at hy
      | some w => rw [← hs₁ x v e₁, ← hs₂ x w e₂]
  funext x
  by_cases hx0 : x = 0
  · subst hx0; exact agree 0 a0 b0
  · by_cases hx1 : x = 1
    · subst hx1; exact agree 1 a1 b1
    · rw [ar x hx0 hx1, br x hx0 hx1]

/-! ## Result 1: monitor soundness (a computational interpretation of the contracts)

The monitor is generic in the footprint strategy. Soundness holds for every *sound*
strategy, for the whole assertion language including imprecise disjunction —
precision plays no role in soundness. -/

/-- **R1a.** Every footprint the greedy strategy returns is a genuine footprint. -/
theorem fpGreedy_strategySound : StrategySound fpGreedy := by
  intro A
  induction A with
  | cell p P =>
    intro g F hF
    simp only [fpGreedy] at hF
    cases e : g p with
    | none => simp [e] at hF
    | some v =>
      simp only [e] at hF
      split at hF
      · rename_i hP
        cases hF
        exact ⟨by simp [e], v, by simp [e], hP, fun a ha => by simp [ha]⟩
      · contradiction
  | pure b =>
    intro g F hF
    simp only [fpGreedy] at hF
    split at hF
    · rename_i hb
      cases hF
      exact ⟨by simp, hb, fun a => by simp⟩
    · contradiction
  | sep A B ihA ihB =>
    intro g F hF
    simp only [fpGreedy] at hF
    cases e₁ : fpGreedy A g with
    | none => simp [e₁] at hF
    | some F₁ =>
      simp only [e₁] at hF
      cases e₂ : fpGreedy B (g.remove F₁) with
      | none => simp [e₂] at hF
      | some F₂ =>
        simp only [e₂, Option.some.injEq] at hF
        subst hF
        exact isFootprint_sep_append (ihA g F₁ e₁) (ihB (g.remove F₁) F₂ e₂)
  | or A B ihA ihB =>
    intro g F hF
    simp only [fpGreedy] at hF
    cases e₁ : fpGreedy A g with
    | some F₁ =>
      simp only [e₁, Option.some.injEq] at hF
      subst hF
      have h := ihA g F₁ e₁
      exact ⟨h.1, Or.inl h.2⟩
    | none =>
      simp only [e₁] at hF
      have h := ihB g F hF
      exact ⟨h.1, Or.inr h.2⟩

/-- The right-biased greedy strategy is sound as well. -/
theorem fpGreedyR_strategySound : StrategySound fpGreedyR := by
  intro A
  induction A with
  | cell p P =>
    intro g F hF
    simp only [fpGreedyR] at hF
    cases e : g p with
    | none => simp [e] at hF
    | some v =>
      simp only [e] at hF
      split at hF
      · rename_i hP
        cases hF
        exact ⟨by simp [e], v, by simp [e], hP, fun a ha => by simp [ha]⟩
      · contradiction
  | pure b =>
    intro g F hF
    simp only [fpGreedyR] at hF
    split at hF
    · rename_i hb
      cases hF
      exact ⟨by simp, hb, fun a => by simp⟩
    · contradiction
  | sep A B ihA ihB =>
    intro g F hF
    simp only [fpGreedyR] at hF
    cases e₁ : fpGreedyR A g with
    | none => simp [e₁] at hF
    | some F₁ =>
      simp only [e₁] at hF
      cases e₂ : fpGreedyR B (g.remove F₁) with
      | none => simp [e₂] at hF
      | some F₂ =>
        simp only [e₂, Option.some.injEq] at hF
        subst hF
        exact isFootprint_sep_append (ihA g F₁ e₁) (ihB (g.remove F₁) F₂ e₂)
  | or A B ihA ihB =>
    intro g F hF
    simp only [fpGreedyR] at hF
    cases e₁ : fpGreedyR B g with
    | some F₁ =>
      simp only [e₁, Option.some.injEq] at hF
      subst hF
      have h := ihB g F₁ e₁
      exact ⟨h.1, Or.inr h.2⟩
    | none =>
      simp only [e₁] at hF
      have h := ihA g F hF
      exact ⟨h.1, Or.inl h.2⟩

/-- **R1b.** Every footprint the backtracking strategy returns is a genuine footprint. -/
theorem fpSearch_strategySound : StrategySound fpSearch := by
  intro A g F hF
  simp only [fpSearch] at hF
  cases e : fpAll A g with
  | nil => simp [e] at hF
  | cons hd tl =>
    simp only [e, List.head?_cons, Option.some.injEq] at hF
    subst hF
    exact fpAll_sound A g hd (by simp [e])

/-- **R1-trusted (soundness under either policy for unannotated callees, assuming
confinement when they are trusted).** If the strategy is sound and the monitor performs
the leak check, then a run accepted by the monitor satisfies every contract with the
monitor's own footprints as witnesses, provided that — when unannotated callees are
trusted (`cfg.checkUnannot = false`) — every read and write executed by an unannotated
callee targets an allocated byte of the frame it runs in (`UnannotConfined`). Annotated
callees called from unannotated code are monitored in both policies. -/
theorem accepts_imp_satisfiesBy_of_unannotConfined
    (s : Strategy) (hs : StrategySound s) (cfg : MonCfg) (hleak : cfg.leakCheck = true)
    (p : Prog) (h : Heap) (O : List Addr) (hacc : Accepts cfg s p h O)
    (hconf : cfg.checkUnannot = false → UnannotConfined s p h O) : SatisfiesBy s p h O := by
  obtain ⟨o', hmon⟩ := Option.isSome_iff_exists.1 hacc
  exact (monitorAux_sound s hs cfg hleak p true h (initOwn O) o' 0 O (ownInv_initOwn O) hmon
    (fun h0 => absurd h0 (by decide)) hconf).2

/-- **R1 (monitor soundness).** If the strategy is sound, the monitor performs the leak
check, and unannotated callees are checked as inlined, then a run accepted by the
monitor satisfies every contract, with the monitor's own footprints as witnesses: at
each call the strategy's footprint satisfies the precondition inside the caller's
fragment, the callee's accesses stay within it, and at return the strategy's footprint
has the same members and satisfies the postcondition. (The `cfg.checkUnannot = true`
instance of R1-trusted, in which the confinement assumption is vacuous.) -/
theorem accepts_imp_satisfiesBy_of_strategySound
    (s : Strategy) (hs : StrategySound s) (cfg : MonCfg)
    (hleak : cfg.leakCheck = true) (hun : cfg.checkUnannot = true)
    (p : Prog) (h : Heap) (O : List Addr) (hacc : Accepts cfg s p h O) :
    SatisfiesBy s p h O :=
  accepts_imp_satisfiesBy_of_unannotConfined s hs cfg hleak p h O hacc
    (fun hc => absurd (hun.symm.trans hc) (by decide))

/-- **R1′ (no false alarms relative to the monitor's own footprints).** Under any
configuration and any strategy, a run that satisfies its contracts with the strategy's
footprints is accepted. -/
theorem satisfiesBy_imp_accepts (s : Strategy) (cfg : MonCfg)
    (p : Prog) (h : Heap) (O : List Addr) (hsat : SatisfiesBy s p h O) :
    Accepts cfg s p h O := by
  simp [Accepts, monitor,
    monitorAux_of_satisfiesBy s cfg p true h (initOwn O) 0 O (ownInv_initOwn O) hsat]

/-- Satisfaction with the strategy's footprints implies satisfaction (angelic footprints). -/
theorem satisfiesBy_imp_satisfies (s : Strategy) :
    ∀ (p : Prog) (h : Heap) (O : List Addr), SatisfiesBy s p h O → Satisfies p h O := by
  intro p
  induction p with
  | skip => intro h O hs; exact hs
  | read a => intro h O hs; exact hs
  | write a v => intro h O hs; exact hs
  | seq p q ihp ihq =>
    intro h O hs
    exact ⟨ihp h O hs.1, ihq (exec p h) O hs.2⟩
  | call P Q body ih =>
    intro h O hs
    obtain ⟨F, -, hpre, hbody, F', -, hmem, hpost⟩ := hs
    refine ⟨F, hpre, ih h F hbody, ?_, ?_⟩
    · intro a ha
      exact hpost.1 a ((hmem a).2 ha)
    · have : ((exec body h).restrict F).restrict F = ((exec body h).restrict F).restrict F' := by
        funext a
        simp only [Heap.restrict_apply]
        by_cases ha : a ∈ F
        · simp [ha, (hmem a).2 ha]
        · have : a ∉ F' := fun h' => ha ((hmem a).1 h')
          simp [ha, this]
      rw [this]; exact hpost.2
  | unannot body ih => intro h O hs; exact ih h O hs

/-- **Frame property.** If a run satisfies its contracts in a frame owning `O`, the run
changes no byte outside `O`. In particular (applied to a callee) bytes not transferred
to a callee are unchanged when it returns. -/
theorem satisfies_frame :
    ∀ (p : Prog) (h : Heap) (O : List Addr), Satisfies p h O → ∀ a, a ∉ O → exec p h a = h a := by
  intro p
  induction p with
  | skip => intro h O _ a _; rfl
  | read b => intro h O _ a _; rfl
  | write b v =>
    intro h O hs a ha
    have hab : a ≠ b := fun e => ha (e ▸ hs.1)
    simp [exec, Heap.write, hab]
  | seq p q ihp ihq =>
    intro h O hs a ha
    simp only [exec]
    rw [ihq (exec p h) O hs.2 a ha, ihp h O hs.1 a ha]
  | call P Q body ih =>
    intro h O hs a ha
    obtain ⟨F, hpre, hbody, -⟩ := hs
    have haF : a ∉ F := by
      intro haF
      have := hpre.1 a haF
      simp [ha] at this
    exact ih h F hbody a haF
  | unannot body ih => intro h O hs a ha; exact ih h O hs a ha

/-- **Footprints witness the separating conjunction.** If the restriction of `g` to `F`
satisfies `A`, then `g` satisfies `A ∗ R` where `R` holds of exactly the frame
`g.remove F`, with the split exposed: the `A`-part is `g.restrict F` and the frame part
is `g.remove F`. (Applied to the caller's fragment and the monitor's footprint `F`, which
R1 shows satisfies the precondition there, this is the witness for `pre ∗ frame`.) -/
theorem restrict_witnesses_sep (A : Assn) (g : Heap) (F : List Addr)
    (hA : sat A (g.restrict F)) :
    SepP (fun g₁ => g₁ = g.restrict F ∧ sat A g₁) (fun g₂ => g₂ = g.remove F) g := by
  refine ⟨g.restrict F, g.remove F, ?_, ?_, ⟨rfl, hA⟩, rfl⟩
  · intro a
    by_cases ha : a ∈ F
    · right; simp [ha]
    · left; simp [ha]
  · intro a
    by_cases ha : a ∈ F
    · cases e : g a with
      | none => simp [ha, e]
      | some v => simp [ha, e]
    · simp [ha]

/-- **Counterexample (hypothesis of `restrict_witnesses_sep`).** `[0, 1]` does not carve
an `owned 0` fragment out of `hTwo`, and the split it induces is not a witness. -/
theorem restrict_witnesses_sep_needs_sat :
    ¬ sat (owned 0) (hTwo.restrict [0, 1]) ∧
      ¬ SepP (fun g₁ => g₁ = hTwo.restrict [0, 1] ∧ sat (owned 0) g₁)
          (fun g₂ => g₂ = hTwo.remove [0, 1]) hTwo := by
  have h : ¬ sat (owned 0) (hTwo.restrict [0, 1]) := by
    intro h
    have := ((sat_owned_iff 0 _).1 h).2 1 (by decide)
    simp at this
  refine ⟨h, ?_⟩
  rintro ⟨g₁, g₂, -, -, ⟨rfl, h₁⟩, -⟩
  exact h h₁

/-- **Counterexample (hypothesis of the frame property).** A store to a byte outside
the frame changes that byte, and the run does not satisfy its contracts. -/
theorem write_outside_frame_changes_byte :
    ¬ Satisfies (.write 1 7) hTwo [0] ∧ (1 : Addr) ∉ [0] ∧
      exec (.write 1 7) hTwo 1 ≠ hTwo 1 := by
  refine ⟨?_, by decide, by decide⟩
  rintro ⟨h, -⟩
  simp at h

/-! ## Result 2: precision and completeness -/

/-- Disjunction-precise contracts are precise (precision is closed under `∗`). -/
theorem precise_of_disjPrecise (A : Assn) (hA : DisjPrecise A) : Precise A := by
  induction A with
  | cell p P => exact precise_cell p P
  | pure b => exact precise_pure b
  | or B C _ _ => exact hA.1
  | sep B C ihB ihC =>
    intro g g₁ g₂ hs₁ hs₂ ⟨u₁, v₁, hd₁, hu₁, hB₁, hC₁⟩ ⟨u₂, v₂, hd₂, hu₂, hB₂, hC₂⟩
    have hg₁ : g₁ = Heap.union u₁ v₁ := funext hu₁
    have hg₂ : g₂ = Heap.union u₂ v₂ := funext hu₂
    subst hg₁ hg₂
    have eu : u₁ = u₂ :=
      ihB hA.1 g u₁ u₂ (sub_trans sub_union_left hs₁) (sub_trans sub_union_left hs₂) hB₁ hB₂
    have ev : v₁ = v₂ :=
      ihC hA.2 g v₁ v₂ (sub_trans (sub_union_right hd₁) hs₁)
        (sub_trans (sub_union_right hd₂) hs₂) hC₁ hC₂
    rw [eu, ev]

/-- **R2a.** The greedy strategy recovers every witness of every disjunction-precise
contract: whenever a sub-fragment of `g` satisfies `A`, the greedy footprint carves out
exactly that sub-fragment. -/
theorem fpGreedy_recoversEveryWitness_of_disjPrecise (A : Assn) (hA : DisjPrecise A) :
    RecoversEveryWitness fpGreedy A := by
  induction A with
  | cell p P =>
    intro g g' hs ⟨v, hv, hP, hr⟩
    have hgp := hs p v hv
    refine ⟨[p], by simp [fpGreedy, hgp, hP], by simp [hgp], ?_⟩
    funext a
    by_cases ha : a = p
    · subst ha; simp [hgp, hv]
    · simp [ha, hr a ha]
  | pure b =>
    intro g g' _ ⟨hb, hr⟩
    refine ⟨[], by simp [fpGreedy, hb], by simp, ?_⟩
    funext a; simp [hr a]
  | sep B C ihB ihC =>
    intro g g' hs ⟨g₁, g₂, hd, hu, hB, hC⟩
    have hs₁ : Heap.Sub g₁ g := fun a v hv => hs a v (by rw [hu a]; simp [hv])
    have hs₂ : Heap.Sub g₂ g := fun a v hv => hs a v (by
      rw [hu a]
      rcases hd a with e | e
      · simp [e, hv]
      · rw [hv] at e; contradiction)
    obtain ⟨F₁, hm₁, ha₁, hr₁⟩ := ihB hA.1 g g₁ hs₁ hB
    obtain ⟨F₂, hm₂, ha₂, hr₂⟩ := ihC hA.2 (g.remove F₁) g₂ (sub_remove_of_disjoint hs₂ hd ha₁ hr₁) hC
    refine ⟨F₁ ++ F₂, by simp [fpGreedy, hm₁, hm₂], ?_, restrict_append_eq_union hu ha₁ hr₁ hr₂⟩
    intro a ha
    rcases List.mem_append.1 ha with h1 | h2
    · exact ha₁ a h1
    · have := ha₂ a h2
      by_cases h1 : a ∈ F₁
      · exact ha₁ a h1
      · simpa [h1] using this
  | or B C ihB ihC =>
    obtain ⟨hPrec, hB, hC⟩ := hA
    intro g g' hs hsat
    rcases hsat with hsB | hsC
    · obtain ⟨F, hm, ha, hr⟩ := ihB hB g g' hs hsB
      exact ⟨F, by simp [fpGreedy, hm], ha, hr⟩
    · cases e : fpGreedy B g with
      | none =>
        obtain ⟨F, hm, ha, hr⟩ := ihC hC g g' hs hsC
        exact ⟨F, by simp [fpGreedy, e, hm], ha, hr⟩
      | some F =>
        have hfp := fpGreedy_strategySound B g F e
        exact ⟨F, by simp [fpGreedy, e], hfp.1,
          hPrec g (g.restrict F) g' (sub_restrict g F) hs (Or.inl hfp.2) (Or.inr hsC)⟩

/-- **R2b.** The backtracking strategy recovers every witness of every precise
contract. -/
theorem fpSearch_recoversEveryWitness_of_precise (A : Assn) (hA : Precise A) :
    RecoversEveryWitness fpSearch A := by
  intro g g' hs hsat
  obtain ⟨F₀, hm₀, _, _⟩ := fpAll_complete_raw A g g' hs hsat
  cases e : fpAll A g with
  | nil => rw [e] at hm₀; simp at hm₀
  | cons F tl =>
    have hsound := fpSearch_strategySound A g F (by simp [fpSearch, e])
    exact ⟨F, by simp [fpSearch, e], hsound.1,
      hA g (g.restrict F) g' (sub_restrict g F) hs hsound.2 hsat⟩

/-- **R2c.** If the strategy recovers every witness of every contract of the program, a run that
satisfies its contracts (angelic footprints) satisfies them with the strategy's
footprints. -/
theorem satisfies_imp_satisfiesBy_of_recoversEveryWitness (s : Strategy)
    (p : Prog) (h : Heap) (O : List Addr)
    (hc : ∀ A ∈ p.contracts, RecoversEveryWitness s A) (hsat : Satisfies p h O) :
    SatisfiesBy s p h O := by
  induction p generalizing h O with
  | skip => trivial
  | read a => exact hsat
  | write a v => exact hsat
  | seq p q ihp ihq =>
    exact ⟨ihp h O (fun A m => hc A (List.mem_append_left _ m)) hsat.1,
           ihq (exec p h) O (fun A m => hc A (List.mem_append_right _ m)) hsat.2⟩
  | unannot body ih => exact ih h O hc hsat
  | call P Q body ih =>
    obtain ⟨F₀, hpre₀, hbody₀, hpost₀⟩ := hsat
    have hcP : RecoversEveryWitness s P := hc P (by simp [Prog.contracts])
    have hcQ : RecoversEveryWitness s Q := hc Q (by simp [Prog.contracts])
    have hcB : ∀ A ∈ body.contracts, RecoversEveryWitness s A :=
      fun A m => hc A (by simp [Prog.contracts, m])
    obtain ⟨F, hsF, haF, hrF⟩ :=
      hcP (h.restrict O) ((h.restrict O).restrict F₀) (sub_restrict _ _) hpre₀.2
    have hmemF : ∀ a, a ∈ F ↔ a ∈ F₀ := by
      intro a
      constructor
      · intro hm
        have his := haF a hm
        have eqa := congrFun hrF a
        simp only [Heap.restrict_apply, hm, ↓reduceIte] at eqa
        by_cases hm₀ : a ∈ F₀
        · exact hm₀
        · simp only [hm₀, ↓reduceIte] at eqa
          simp only [Heap.restrict_apply, eqa] at his; simp at his
      · intro hm₀
        have his := hpre₀.1 a hm₀
        have eqa := congrFun hrF a
        simp only [Heap.restrict_apply, hm₀, ↓reduceIte] at eqa
        by_cases hm : a ∈ F
        · exact hm
        · simp only [hm, ↓reduceIte] at eqa
          simp only [Heap.restrict_apply, ← eqa] at his; simp at his
    have hpreF : IsFootprint P (h.restrict O) F := ⟨haF, hrF.symm ▸ hpre₀.2⟩
    have hbodyF : Satisfies body h F := satisfies_congr_mem (fun a => (hmemF a).symm) hbody₀
    have hbodyBy : SatisfiesBy s body h F := ih h F hcB hbodyF
    have hrestExec : (exec body h).restrict F = (exec body h).restrict F₀ := by
      funext a; simp [hmemF a]
    have hpostF_sat : sat Q (((exec body h).restrict F).restrict F) := by
      have : ((exec body h).restrict F).restrict F = ((exec body h).restrict F₀).restrict F₀ := by
        funext a; simp [hmemF a]
      rw [this]; exact hpost₀.2
    obtain ⟨F', hsF', haF', hrF'⟩ :=
      hcQ ((exec body h).restrict F) (((exec body h).restrict F).restrict F)
        (sub_restrict _ _) hpostF_sat
    have hmemF' : ∀ a, a ∈ F' ↔ a ∈ F := by
      intro a
      constructor
      · intro hm'
        have his := haF' a hm'
        by_cases hm : a ∈ F
        · exact hm
        · simp [hm] at his
      · intro hm
        have his₀ := hpost₀.1 a ((hmemF a).1 hm)
        rw [← hrestExec] at his₀
        have eqa := congrFun hrF' a
        simp only [Heap.restrict_apply, hm, ↓reduceIte] at eqa
        by_cases hm' : a ∈ F'
        · exact hm'
        · simp only [hm', ↓reduceIte] at eqa
          simp only [Heap.restrict_apply, hm, ↓reduceIte, ← eqa] at his₀
          simp at his₀
    exact ⟨F, hsF, hpreF, hbodyBy, F', hsF', hmemF', haF', hrF'.symm ▸ hpostF_sat⟩

/-- **R2 (greedy completeness).** If every contract of the program is
disjunction-precise, the greedy monitor (under any configuration) accepts every run that
satisfies its contracts. -/
theorem accepts_fpGreedy_of_satisfies_of_disjPrecise (cfg : MonCfg)
    (p : Prog) (h : Heap) (O : List Addr)
    (hdp : ∀ A ∈ p.contracts, DisjPrecise A) (hsat : Satisfies p h O) :
    Accepts cfg fpGreedy p h O :=
  satisfiesBy_imp_accepts fpGreedy cfg p h O
    (satisfies_imp_satisfiesBy_of_recoversEveryWitness fpGreedy p h O
      (fun A hA => fpGreedy_recoversEveryWitness_of_disjPrecise A (hdp A hA)) hsat)

/-- **R2 (search completeness).** If every contract of the program is precise, the
backtracking monitor (under any configuration) accepts every run that satisfies its
contracts. -/
theorem accepts_fpSearch_of_satisfies_of_precise (cfg : MonCfg)
    (p : Prog) (h : Heap) (O : List Addr)
    (hp : ∀ A ∈ p.contracts, Precise A) (hsat : Satisfies p h O) :
    Accepts cfg fpSearch p h O :=
  satisfiesBy_imp_accepts fpSearch cfg p h O
    (satisfies_imp_satisfiesBy_of_recoversEveryWitness fpSearch p h O
      (fun A hA => fpSearch_recoversEveryWitness_of_precise A (hp A hA)) hsat)

/-- **R2 (characterization, greedy).** For programs whose contracts are all
disjunction-precise, the strict greedy monitor accepts a run iff the run satisfies its
contracts. -/
theorem accepts_strict_fpGreedy_iff_satisfies_of_disjPrecise
    (p : Prog) (h : Heap) (O : List Addr) (hdp : ∀ A ∈ p.contracts, DisjPrecise A) :
    Accepts MonCfg.strict fpGreedy p h O ↔ Satisfies p h O :=
  ⟨fun hacc => satisfiesBy_imp_satisfies fpGreedy p h O
      (accepts_imp_satisfiesBy_of_strategySound fpGreedy fpGreedy_strategySound
        MonCfg.strict rfl rfl p h O hacc),
   accepts_fpGreedy_of_satisfies_of_disjPrecise MonCfg.strict p h O hdp⟩

/-- **R2 (characterization, search).** For programs whose contracts are all precise,
the strict backtracking monitor accepts a run iff the run satisfies its contracts. -/
theorem accepts_strict_fpSearch_iff_satisfies_of_precise
    (p : Prog) (h : Heap) (O : List Addr) (hp : ∀ A ∈ p.contracts, Precise A) :
    Accepts MonCfg.strict fpSearch p h O ↔ Satisfies p h O :=
  ⟨fun hacc => satisfiesBy_imp_satisfies fpSearch p h O
      (accepts_imp_satisfiesBy_of_strategySound fpSearch fpSearch_strategySound
        MonCfg.strict rfl rfl p h O hacc),
   accepts_fpSearch_of_satisfies_of_precise MonCfg.strict p h O hp⟩

/-! ### Imprecise contracts: no online strategy is complete -/

theorem satisfies_runL : Satisfies runL hTwo [0, 1] := by
  refine ⟨[0], ⟨by decide, Or.inl ((sat_owned_iff 0 _).2 ⟨by decide, fun a ha => by simp [ha]⟩)⟩,
    ⟨by simp, by decide⟩, ⟨by decide, Or.inl ((sat_owned_iff 0 _).2 ⟨by decide, fun a ha => by simp [ha]⟩)⟩⟩

theorem satisfies_runR : Satisfies runR hTwo [0, 1] := by
  refine ⟨[1], ⟨by decide, Or.inr ((sat_owned_iff 1 _).2 ⟨by decide, fun a ha => by simp [ha]⟩)⟩,
    ⟨by simp, by decide⟩, ⟨by decide, Or.inr ((sat_owned_iff 1 _).2 ⟨by decide, fun a ha => by simp [ha]⟩)⟩⟩

/-- **R2 (impossibility).** For the imprecise contract `owned 0 ∨ owned 1`: the run
whose callee reads byte `0` and the run whose callee reads byte `1` both satisfy their
contracts (from the same heap and ownership), yet no sound strategy — under any monitor
configuration — gets both accepted. The strategy must choose the footprint at call time,
before the callee's accesses are seen. -/
theorem owned0_or_owned1_no_sound_strategy_accepts_both :
    Satisfies runL hTwo [0, 1] ∧ Satisfies runR hTwo [0, 1] ∧
      ∀ (cfg : MonCfg) (s : Strategy), StrategySound s →
        ¬ (Accepts cfg s runL hTwo [0, 1] ∧ Accepts cfg s runR hTwo [0, 1]) := by
  refine ⟨satisfies_runL, satisfies_runR, ?_⟩
  rintro cfg s hs ⟨hL, hR⟩
  simp only [Accepts, runL, runR, monitor, monitorAux, frag_initOwn_hTwo] at hL hR
  cases hF : s C (hTwo.restrict [0, 1]) with
  | none => simp [hF] at hL
  | some F =>
    have hfp := hs _ _ _ hF
    simp only [hF] at hL hR
    rcases hfp.2 with h0 | h1
    · have h1F : 1 ∉ F := not_mem_one_of_isFootprint_owned0 F ⟨hfp.1, h0⟩
      split at hR
      · simp [transfer, h1F, initOwn] at hR
      · simp at hR
    · have h0F : 0 ∉ F := not_mem_zero_of_isFootprint_owned1 F ⟨hfp.1, h1⟩
      split at hL
      · simp [transfer, h0F, initOwn] at hL
      · simp at hL

/-- **Positive control for the impossibility.** Swapping the quantifiers makes the
conclusion fail: each of the two runs is accepted by some *sound* strategy (whose choices
on that run are genuine footprints) — the left-biased greedy strategy accepts the first,
the right-biased one the second. So the impossibility is about making one choice before
the callee runs, not about either run being unmonitorable by a sound strategy. -/
theorem owned0_or_owned1_each_run_accepted_by_some_strategy :
    StrategySound fpGreedy ∧ StrategySound fpGreedyR ∧
      Accepts MonCfg.strict fpGreedy runL hTwo [0, 1] ∧ SatisfiesBy fpGreedy runL hTwo [0, 1] ∧
      Accepts MonCfg.strict fpGreedyR runR hTwo [0, 1] ∧
      SatisfiesBy fpGreedyR runR hTwo [0, 1] := by
  refine ⟨fpGreedy_strategySound, fpGreedyR_strategySound, by decide, ?_, by decide, ?_⟩
  · refine ⟨[0], by decide,
      ⟨by decide, Or.inl ((sat_owned_iff 0 _).2 ⟨by decide, fun a ha => by simp [ha]⟩)⟩,
      ⟨by simp, by decide⟩, [0], by decide, fun a => Iff.rfl,
      ⟨by decide, Or.inl ((sat_owned_iff 0 _).2 ⟨by decide, fun a ha => by simp [ha]⟩)⟩⟩
  · refine ⟨[1], by decide,
      ⟨by decide, Or.inr ((sat_owned_iff 1 _).2 ⟨by decide, fun a ha => by simp [ha]⟩)⟩,
      ⟨by simp, by decide⟩, [1], by decide, fun a => Iff.rfl,
      ⟨by decide, Or.inr ((sat_owned_iff 1 _).2 ⟨by decide, fun a ha => by simp [ha]⟩)⟩⟩

/-- **Tightness of `StrategySound` in the impossibility.** An unsound strategy that
always transfers both bytes gets both runs accepted. -/
theorem owned0_or_owned1_unsound_strategy_accepts_both :
    ¬ StrategySound sAll ∧ Accepts MonCfg.strict sAll runL hTwo [0, 1] ∧
      Accepts MonCfg.strict sAll runR hTwo [0, 1] := by
  refine ⟨fun h => not_isFootprint_owned0_hTwo_01 (h (owned 0) hTwo [0, 1] rfl), by decide, by decide⟩

/-! ### Counterexamples for the completeness hypotheses -/

/-- **Counterexample (imprecise contract, greedy).** `owned 0 ∨ owned 1` is not
disjunction-precise and greedy does not recover every witness of it; the run `runR` satisfies its
contracts, but the greedy footprint (byte `0`) is not the one the callee uses, and the
greedy monitor rejects the run. -/
theorem fpGreedy_rejects_satisfying_run_imprecise_contract :
    ¬ DisjPrecise C ∧ ¬ RecoversEveryWitness fpGreedy C ∧ Satisfies runR hTwo [0, 1] ∧
      ¬ SatisfiesBy fpGreedy runR hTwo [0, 1] ∧
      ¬ Accepts MonCfg.strict fpGreedy runR hTwo [0, 1] :=
  ⟨not_disjPrecise_C, not_recoversEveryWitness_fpGreedy_C, satisfies_runR,
    not_satisfiesBy_fpGreedy_runR, by decide⟩

/-- **Counterexample (imprecise contract, search).** `owned 0 ∨ owned 1` is not precise;
`runR` satisfies its contracts but the backtracking monitor (first footprint found:
byte `0`) rejects it. -/
theorem fpSearch_rejects_satisfying_run_imprecise_contract :
    ¬ Precise C ∧ Satisfies runR hTwo [0, 1] ∧
      ¬ Accepts MonCfg.strict fpSearch runR hTwo [0, 1] :=
  ⟨not_precise_C, satisfies_runR, by decide⟩

theorem satisfies_runP : Satisfies runP hTwo [0, 1] := by
  refine ⟨[0, 1], ⟨by decide, sat_C'_of_shape _ (by decide) (by decide) ?_⟩, trivial,
    ⟨by decide, sat_C'_of_shape _ (by decide) (by decide) ?_⟩⟩
  · intro a h0 h1; simp [h0, h1]
  · intro a h0 h1; simp [h0, h1]

/-- **Counterexample (precise but not disjunction-precise, greedy).** `C'` is precise but
has an imprecise inner disjunction. Greedy does not recover every witness of it, and the greedy monitor
rejects a run that satisfies its contracts, while the backtracking monitor accepts it.
So `DisjPrecise` in the greedy results cannot be weakened to `Precise`. -/
theorem fpGreedy_rejects_satisfying_run_precise_not_disjPrecise :
    Precise C' ∧ ¬ DisjPrecise C' ∧ ¬ RecoversEveryWitness fpGreedy C' ∧
      Satisfies runP hTwo [0, 1] ∧ ¬ Accepts MonCfg.strict fpGreedy runP hTwo [0, 1] ∧
      Accepts MonCfg.strict fpSearch runP hTwo [0, 1] := by
  refine ⟨precise_C', not_disjPrecise_C', ?_, satisfies_runP, by decide, by decide⟩
  intro hc
  obtain ⟨F, hF, -⟩ := hc hTwo hTwo (fun _ _ h => h)
    (sat_C'_of_shape hTwo (by decide) (by decide) (fun a h0 h1 => hTwo_of_ne a h0 h1))
  have : fpGreedy C' hTwo = none := by decide
  rw [this] at hF
  cases hF

/-! ### Witness recovery versus weaker notions of completeness -/

/-- The backtracking strategy is existentially footprint-complete for *every* assertion,
precise or not: whenever a satisfying sub-fragment exists, it returns some genuine
footprint (not necessarily the intended one). -/
theorem fpSearch_existsFootprintComplete (A : Assn) : ExistsFootprintComplete fpSearch A := by
  intro g g' hs hsat
  obtain ⟨F₀, hm₀, _, _⟩ := fpAll_complete_raw A g g' hs hsat
  cases e : fpAll A g with
  | nil => rw [e] at hm₀; simp at hm₀
  | cons F tl =>
    exact ⟨F, by simp [fpSearch, e], fpSearch_strategySound A g F (by simp [fpSearch, e])⟩

/-- Existential footprint completeness does not imply precision (unlike witness
recovery, `precise_of_recoversEveryWitness`). -/
theorem existsFootprintComplete_not_imp_precise :
    ExistsFootprintComplete fpSearch C ∧ ¬ Precise C :=
  ⟨fpSearch_existsFootprintComplete C, not_precise_C⟩

/-- Whole-program completeness of a monitor for one fixed program does not require
precise contracts: the greedy monitor (under every configuration) accepts every
satisfying run of `call C C skip`, whose contracts are both the imprecise `C`, because
the callee does not distinguish the two witnesses. -/
theorem accepts_fpGreedy_call_C_C_skip_of_satisfies :
    (∀ A ∈ (Prog.call C C .skip).contracts, ¬ Precise A) ∧
      ∀ (cfg : MonCfg) (h : Heap) (O : List Addr),
        Satisfies (.call C C .skip) h O → Accepts cfg fpGreedy (.call C C .skip) h O := by
  refine ⟨?_, ?_⟩
  · intro A hA
    simp only [Prog.contracts, List.mem_cons, List.mem_nil_iff, or_false] at hA
    rcases hA with rfl | rfl <;> exact not_precise_C
  · intro cfg h O ⟨F₀, hpre₀, _, _⟩
    apply satisfiesBy_imp_accepts
    cases e0 : (h.restrict O) 0 with
    | some v0 =>
      have h0O : 0 ∈ O := by by_cases hm : 0 ∈ O; exact hm; simp [hm] at e0
      have hv0 : h 0 = some v0 := by simpa [h0O] using e0
      refine ⟨[0], by simp [fpGreedy, C, owned, h0O, hv0],
        ⟨by simp [h0O, hv0], Or.inl ((sat_owned_iff 0 _).2 ⟨by simp [h0O, hv0], fun a ha => by simp [ha]⟩)⟩,
        trivial, [0], by simp [fpGreedy, C, owned, exec, hv0], fun _ => Iff.rfl,
        ⟨by simp [exec, hv0], Or.inl ((sat_owned_iff 0 _).2 ⟨by simp [exec, hv0], fun a ha => by simp [ha]⟩)⟩⟩
    | none =>
      rcases hpre₀.2 with h0 | h1
      · have his0 := ((sat_owned_iff 0 _).1 h0).1
        by_cases hm0 : 0 ∈ F₀
        · simp only [Heap.restrict_apply, hm0, ↓reduceIte] at his0
          rw [Heap.restrict_apply] at e0
          rw [e0] at his0; simp at his0
        · simp [hm0] at his0
      · have his1 := ((sat_owned_iff 1 _).1 h1).1
        have h1F₀ : 1 ∈ F₀ := by by_cases hm : 1 ∈ F₀; exact hm; simp [hm] at his1
        simp only [Heap.restrict_apply, h1F₀, ↓reduceIte] at his1
        cases e1 : (h.restrict O) 1 with
        | none =>
          rw [Heap.restrict_apply] at e1
          rw [e1] at his1; simp at his1
        | some v1 =>
          have h1O : 1 ∈ O := by by_cases hm : 1 ∈ O; exact hm; simp [hm] at e1
          have hv1 : h 1 = some v1 := by simpa [h1O] using e1
          have h0none : (if 0 ∈ O then h 0 else none) = none := by simpa using e0
          refine ⟨[1], by simp [fpGreedy, C, owned, h0none, h1O, hv1],
            ⟨by simp [h1O, hv1], Or.inr ((sat_owned_iff 1 _).2 ⟨by simp [h1O, hv1], fun a ha => by simp [ha]⟩)⟩,
            trivial, [1], by simp [fpGreedy, C, owned, exec, hv1], fun _ => Iff.rfl,
            ⟨by simp [exec, hv1],
              Or.inr ((sat_owned_iff 1 _).2 ⟨by simp [exec, hv1], fun a ha => by simp [ha]⟩)⟩⟩

/-! ## Result 1 hypotheses: counterexamples -/

/-- **Counterexample (unsound strategy).** With a strategy that transfers byte `0`
without checking the precondition `pointsTo 0 1`, the strict monitor accepts a run
whose precondition is false. All other hypotheses of R1 and R1-trusted hold. -/
theorem unsound_strategy_accepts_contract_violating_run :
    ¬ StrategySound sBad ∧ MonCfg.strict.leakCheck = true ∧ MonCfg.strict.checkUnannot = true ∧
      Accepts MonCfg.strict sBad runBad hOne [0] ∧
      UnannotConfined sBad runBad hOne [0] ∧
      ¬ SatisfiesBy sBad runBad hOne [0] ∧ ¬ Satisfies runBad hOne [0] := by
  refine ⟨not_strategySound_sBad, rfl, rfl, by decide, fun _ _ => trivial, ?_, ?_⟩
  · rintro ⟨F, -, hpre, -⟩
    have := ((sat_pointsTo_iff 0 1 _).1 hpre.2).1
    by_cases h0 : 0 ∈ F <;> simp [h0, hOne] at this
  · rintro ⟨F, hpre, -⟩
    have := ((sat_pointsTo_iff 0 1 _).1 hpre.2).1
    by_cases h0 : 0 ∈ F <;> simp [h0, hOne] at this

/-- **Counterexample (no leak check: exactness).** Without the leak check, the monitor
accepts a callee that receives `owned 0` and returns only `emp`, although the
postcondition does not describe the callee's final fragment. All other hypotheses of R1
and R1-trusted hold. -/
theorem noLeakCheck_accepts_leaky_post :
    StrategySound fpAtom ∧ (⟨false, true⟩ : MonCfg).checkUnannot = true ∧
      Accepts ⟨false, true⟩ fpAtom runLeak hOne [0] ∧
      UnannotConfined fpAtom runLeak hOne [0] ∧
      ¬ SatisfiesBy fpAtom runLeak hOne [0] ∧ ¬ Satisfies runLeak hOne [0] :=
  ⟨fpAtom_strategySound, rfl, by decide, fun _ _ => trivial,
   fun hs => not_satisfies_leaky_post (satisfiesBy_imp_satisfies fpAtom _ _ _ hs),
   not_satisfies_leaky_post⟩

/-- **Counterexample (no leak check: stale depth-indexed ownership).** Without the leak
check, a byte leaked by one callee stays attributed to call depth 1, and a later sibling
callee at depth 1 — given only `owned 1` — reads byte `0` and is accepted. The second
call does not satisfy its contract even judged on its own, and the strict monitor rejects
the run. -/
theorem noLeakCheck_later_callee_inherits_leaked_byte :
    StrategySound fpAtom ∧ Accepts ⟨false, true⟩ fpAtom runStale hTwo [0, 1] ∧
      ¬ Satisfies (.call (owned 1) (owned 1) (.read 0))
          (exec (.call (owned 0) .emp .skip) hTwo) [0, 1] ∧
      ¬ Satisfies runStale hTwo [0, 1] ∧ ¬ SatisfiesBy fpAtom runStale hTwo [0, 1] ∧
      UnannotConfined fpAtom runStale hTwo [0, 1] ∧
      ¬ Accepts MonCfg.strict fpAtom runStale hTwo [0, 1] := by
  have h2 : ¬ Satisfies (.call (owned 1) (owned 1) (.read 0))
      (exec (.call (owned 0) .emp .skip) hTwo) [0, 1] := by
    rintro ⟨F, hF, ⟨h0, -⟩, -⟩
    exact not_mem_zero_of_isFootprint_owned1 F hF h0
  exact ⟨fpAtom_strategySound, by decide, h2, fun hs => h2 hs.2,
    fun hs => h2 (satisfiesBy_imp_satisfies fpAtom _ _ _ hs).2,
    ⟨fun _ _ => trivial, fun _ _ h => absurd h (by decide)⟩, by decide⟩

/-- **Result 3 (counterexample: trusted unannotated callees).** If unannotated callees
are trusted (not checked), the monitor — with a sound strategy and the leak check —
accepts a run in which an unannotated helper of a callee given only `owned 0` stores to
byte `1`, which the caller kept: the contracts are violated (byte `1` changes across a
call whose footprint is `[0]`), the confinement assumption `UnannotConfined` fails, and
the inline-checking (strict) monitor rejects the run. -/
theorem trusted_unannot_write_outside_footprint_accepted :
    StrategySound fpAtom ∧ (⟨true, false⟩ : MonCfg).leakCheck = true ∧
      Accepts ⟨true, false⟩ fpAtom runTrusted hTwo [0, 1] ∧
      ((⟨true, false⟩ : MonCfg).checkUnannot = false ∧
        ¬ UnannotConfined fpAtom runTrusted hTwo [0, 1]) ∧
      ¬ SatisfiesBy fpAtom runTrusted hTwo [0, 1] ∧ ¬ Satisfies runTrusted hTwo [0, 1] ∧
      (fpAtom (owned 0) (hTwo.restrict [0, 1]) = some [0] ∧ (1 : Addr) ∉ [0] ∧
        exec runTrusted hTwo 1 ≠ hTwo 1) ∧
      ¬ Accepts MonCfg.strict fpAtom runTrusted hTwo [0, 1] := by
  have hns : ¬ Satisfies runTrusted hTwo [0, 1] := by
    rintro ⟨F, hF, ⟨h1, -⟩, -⟩
    exact not_mem_one_of_isFootprint_owned0 F hF h1
  exact ⟨fpAtom_strategySound, rfl, accepts_trusted_unannot_store,
    ⟨rfl, not_unannotConfined_outside⟩,
    fun hs => hns (satisfiesBy_imp_satisfies fpAtom _ _ _ hs), hns,
    ⟨by decide, by decide, by decide⟩, by decide⟩

/-- **Trusted policy still monitors annotated callees.** An unannotated helper that
performs no access at all but calls an annotated function whose precondition
`pointsTo 0 1` is false: the run violates its contracts, the confinement assumption
holds (there is no uninstrumented access), and the monitor with unannotated callees
trusted rejects the run — consistent with R1-trusted. -/
theorem trusted_monitor_checks_nested_annotated_call :
    UnannotConfined fpAtom pCallback hOne [0] ∧ ¬ Satisfies pCallback hOne [0] ∧
      ¬ Accepts ⟨true, false⟩ fpAtom pCallback hOne [0] := by
  refine ⟨?_, ?_, not_accepts_trusted_nested_annotated_call⟩
  · intro F hF G hG
    have : fpAtom (pointsTo 0 1) (hOne.restrict F) = none := by
      have hF0 : F = [0] := by
        have h : fpAtom (owned 0) (hOne.restrict [0]) = some [0] := by decide
        rw [h] at hF; cases hF; rfl
      subst hF0; decide
    rw [this] at hG; cases hG
  · rintro ⟨F, _, ⟨G, hpreG, _, _⟩, _⟩
    have := ((sat_pointsTo_iff 0 1 _).1 hpreG.2).1
    by_cases hG : 0 ∈ G
    · by_cases hF : 0 ∈ F <;> simp [hG, hF, hOne] at this
    · simp [hG] at this

/-- **Counterexample (acceptance / satisfaction premises).** Reading a byte the frame
does not own is accepted by no monitor and satisfies no contract, while every other
hypothesis of the soundness and completeness results holds: the confinement assumption
holds (the read is not unannotated code), and the program has no contracts (so every
contract-wise hypothesis holds vacuously). -/
theorem read_unowned_rejected_and_unsatisfied :
    (∀ (cfg : MonCfg) (s : Strategy), ¬ Accepts cfg s (.read 1) hTwo [0]) ∧
      (∀ s : Strategy, ¬ SatisfiesBy s (.read 1) hTwo [0] ∧ UnannotConfined s (.read 1) hTwo [0]) ∧
      ¬ Satisfies (.read 1) hTwo [0] ∧
      (∀ (s : Strategy), ∀ A ∈ (Prog.read 1).contracts,
        DisjPrecise A ∧ Precise A ∧ RecoversEveryWitness s A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro cfg s
    simp [Accepts, monitor, monitorAux, initOwn]
  · intro s
    refine ⟨?_, fun h => absurd h (by decide)⟩
    rintro ⟨h, -⟩; simp at h
  · rintro ⟨h, -⟩; simp at h
  · intro s A hA; simp [Prog.contracts] at hA

/-- **Counterexample (`a ∉ O` in the frame property).** A run satisfying its contracts
in frame `[0]` changes byte `0`, which is in the frame. -/
theorem satisfies_frame_needs_not_mem :
    Satisfies (.write 0 5) hOne [0] ∧ ¬ ((0 : Addr) ∉ [0]) ∧
      exec (.write 0 5) hOne 0 ≠ hOne 0 :=
  ⟨⟨by simp, by decide⟩, by simp, by decide⟩

/-! ## Non-vacuity witnesses -/

/-- Non-vacuity for R1a: greedy computes a footprint for a contract mixing `∨` and `∗`. -/
theorem fpGreedy_strategySound_nonvacuous :
    fpGreedy (.sep C (owned 1)) hTwo = some [0, 1] := by decide

/-- Non-vacuity for R1b: search computes a footprint for `C'`. -/
theorem fpSearch_strategySound_nonvacuous : fpSearch C' hTwo = some [0, 1] := by decide

/-- Non-vacuity for R1: all hypotheses hold for `fpAtom`, the strict configuration, and
`progNV` (which contains a call and an unannotated helper). -/
theorem accepts_imp_satisfiesBy_of_strategySound_nonvacuous :
    StrategySound fpAtom ∧ MonCfg.strict.leakCheck = true ∧
      MonCfg.strict.checkUnannot = true ∧ Accepts MonCfg.strict fpAtom progNV hOne [0] :=
  ⟨fpAtom_strategySound, rfl, rfl, by decide⟩

theorem satisfiesBy_fpAtom_progNV : SatisfiesBy fpAtom progNV hOne [0] := by
  refine ⟨[0], by decide, ⟨by decide, (sat_owned_iff 0 _).2 ⟨by decide, fun a ha => by simp [ha]⟩⟩,
    ⟨by simp, by decide⟩, [0], by decide, fun a => Iff.rfl,
    ⟨by decide, (sat_pointsTo_iff 0 5 _).2 ⟨by decide, fun a ha => by simp [ha]⟩⟩⟩

/-- Non-vacuity for R1′. -/
theorem satisfiesBy_imp_accepts_nonvacuous : SatisfiesBy fpAtom progNV hOne [0] :=
  satisfiesBy_fpAtom_progNV

/-- Non-vacuity for R1-trusted: all hypotheses hold with unannotated callees trusted, for
`progMixed`, whose unannotated helper both performs an (unchecked, confined) store and
calls an annotated function (monitored). -/
theorem accepts_imp_satisfiesBy_of_unannotConfined_nonvacuous :
    StrategySound fpAtom ∧ (⟨true, false⟩ : MonCfg).leakCheck = true ∧
      Accepts ⟨true, false⟩ fpAtom progMixed hOne [0] ∧
      ((⟨true, false⟩ : MonCfg).checkUnannot = false →
        UnannotConfined fpAtom progMixed hOne [0]) := by
  refine ⟨fpAtom_strategySound, rfl, by decide, fun _ => ?_⟩
  intro F hF
  have : F = [0] := by
    have h : fpAtom (owned 0) (hOne.restrict [0]) = some [0] := by decide
    rw [h] at hF; cases hF; rfl
  subst this
  exact ⟨fun _ => ⟨by simp, by decide⟩, fun _ _ h => absurd h (by decide)⟩

/-- Non-vacuity for the frame property: the run satisfies its contracts and byte `1` is
outside the frame `[0]`. -/
theorem satisfies_frame_nonvacuous : Satisfies progNV hOne [0] ∧ (1 : Addr) ∉ [0] :=
  ⟨satisfiesBy_imp_satisfies fpAtom _ _ _ satisfiesBy_fpAtom_progNV, by decide⟩

/-- Non-vacuity for `restrict_witnesses_sep`. -/
theorem restrict_witnesses_sep_nonvacuous : sat (owned 0) (hTwo.restrict [0]) :=
  isFootprint_owned0_hTwo.2

/-- Non-vacuity for `precise_of_recoversEveryWitness`. -/
theorem precise_of_recoversEveryWitness_nonvacuous : RecoversEveryWitness fpAtom (owned 0) :=
  fpAtom_recoversEveryWitness_cell _ _

/-- Non-vacuity for `precise_of_disjPrecise`: a disjunctive disjunction-precise contract. -/
theorem precise_of_disjPrecise_nonvacuous : DisjPrecise (.or (pointsTo 0 0) (pointsTo 0 1)) :=
  disjPrecise_pointsTo00_or_pointsTo01

/-- Non-vacuity for R2a: all hypotheses (of the theorem and of the witness-recovery
clause) hold for a disjunctive contract. -/
theorem fpGreedy_recoversEveryWitness_of_disjPrecise_nonvacuous :
    DisjPrecise (.or (pointsTo 0 0) (pointsTo 0 1)) ∧ Heap.Sub hOne hOne ∧
      sat (.or (pointsTo 0 0) (pointsTo 0 1)) hOne :=
  ⟨disjPrecise_pointsTo00_or_pointsTo01, fun _ _ h => h,
   Or.inl ((sat_pointsTo_iff 0 0 _).2 ⟨rfl, fun a ha => by simp [hOne, ha]⟩)⟩

/-- Non-vacuity for R2b: all hypotheses hold for the precise, not disjunction-precise `C'`. -/
theorem fpSearch_recoversEveryWitness_of_precise_nonvacuous :
    Precise C' ∧ Heap.Sub hTwo hTwo ∧ sat C' hTwo :=
  ⟨precise_C', fun _ _ h => h,
   sat_C'_of_shape hTwo (by decide) (by decide) (fun a h0 h1 => hTwo_of_ne a h0 h1)⟩

/-- Non-vacuity for R2c. -/
theorem satisfies_imp_satisfiesBy_of_recoversEveryWitness_nonvacuous :
    (∀ A ∈ progNV.contracts, RecoversEveryWitness fpAtom A) ∧ Satisfies progNV hOne [0] := by
  refine ⟨?_, satisfies_frame_nonvacuous.1⟩
  intro A hA
  simp only [progNV, Prog.contracts, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl
  · exact fpAtom_recoversEveryWitness_cell _ _
  · exact fpAtom_recoversEveryWitness_cell _ _

theorem satisfies_progOr : Satisfies progOr hOne [0] := by
  refine ⟨[0], ⟨by decide, Or.inl ((sat_pointsTo_iff 0 0 _).2 ⟨by decide, fun a ha => by simp [ha]⟩)⟩,
    ⟨by simp, by decide⟩, ⟨by decide, (sat_pointsTo_iff 0 1 _).2 ⟨by decide, fun a ha => by simp [ha]⟩⟩⟩

theorem disjPrecise_progOr : ∀ A ∈ progOr.contracts, DisjPrecise A := by
  intro A hA
  simp only [progOr, Prog.contracts, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl
  · exact disjPrecise_pointsTo00_or_pointsTo01
  · trivial

/-- Non-vacuity for the greedy completeness and characterization theorems: a program
whose precondition is a (precise) disjunction. -/
theorem accepts_fpGreedy_of_satisfies_of_disjPrecise_nonvacuous :
    (∀ A ∈ progOr.contracts, DisjPrecise A) ∧ Satisfies progOr hOne [0] :=
  ⟨disjPrecise_progOr, satisfies_progOr⟩

/-- Non-vacuity for the search completeness and characterization theorems. -/
theorem accepts_fpSearch_of_satisfies_of_precise_nonvacuous :
    (∀ A ∈ runP.contracts, Precise A) ∧ Satisfies runP hTwo [0, 1] := by
  refine ⟨?_, satisfies_runP⟩
  intro A hA
  simp only [runP, Prog.contracts, List.mem_cons, List.mem_nil_iff, or_false] at hA
  rcases hA with rfl | rfl <;> exact precise_C'

/-- Non-vacuity for the impossibility: a sound strategy that handles disjunction exists
(so the hypothesis `StrategySound s` is satisfiable by a strategy that is not trivially
rejecting `∨`), and both runs satisfy their contracts. -/
theorem owned0_or_owned1_no_sound_strategy_accepts_both_nonvacuous :
    StrategySound fpGreedy ∧ fpGreedy C (hTwo.restrict [0, 1]) = some [0] ∧
      Satisfies runL hTwo [0, 1] ∧ Satisfies runR hTwo [0, 1] :=
  ⟨fpGreedy_strategySound, by decide, satisfies_runL, satisfies_runR⟩

/-! ## Boundary examples for the non-claims

These closed statements support non-claims stated for the results above: `DisjPrecise` is sufficient but
not necessary for greedy witness recovery; a fixed program can be characterized by the
search monitor although its contracts are imprecise; an out-of-frame *read* by trusted
unannotated code leaves the heap unchanged yet violates the contracts; and
`restrict_witnesses_sep` allows unallocated addresses in `F`. -/

/-- `C'` with its inner disjuncts swapped: `(owned 0 ∨ (owned 0 ∗ owned 1)) ∗ owned 1`. -/
def CFlip : Assn := .sep (.or (owned 0) (.sep (owned 0) (owned 1))) (owned 1)

/-- Every fragment satisfying `CFlip` is allocated at exactly the addresses `0` and `1`. -/
theorem sat_CFlip_shape (g : Heap) (h : sat CFlip g) :
    (g 0).isSome = true ∧ (g 1).isSome = true ∧ ∀ a, a ≠ 0 → a ≠ 1 → g a = none := by
  obtain ⟨g₁, g₂, hdisj, hunion, hor, h₂⟩ := h
  obtain ⟨h₂1, h₂r⟩ := (sat_owned_iff 1 g₂).1 h₂
  rcases hor with hl | hr
  · obtain ⟨hg₁0, hg₁r⟩ := (sat_owned_iff 0 g₁).1 hl
    refine ⟨?_, ?_, ?_⟩
    · rw [hunion 0]
      cases e : g₁ 0 with
      | none => simp [e] at hg₁0
      | some v => simp [e]
    · rw [hunion 1]; simp [hg₁r 1 (by decide), h₂1]
    · intro a h0 h1
      rw [hunion a]; simp [hg₁r a h0, h₂r a h1]
  · exfalso
    obtain ⟨u₁, u₂, -, hu, hu₁, hu₂⟩ := hr
    obtain ⟨-, hu₁r⟩ := (sat_owned_iff 0 u₁).1 hu₁
    obtain ⟨hu₂1, -⟩ := (sat_owned_iff 1 u₂).1 hu₂
    have hg₁1 : (g₁ 1).isSome = true := by
      rw [hu 1]; simp [hu₁r 1 (by decide), hu₂1]
    rcases hdisj 1 with e | e
    · simp [e] at hg₁1
    · simp [e] at h₂1

/-- **`DisjPrecise` is not necessary for greedy witness recovery.** `CFlip` is
satisfiable and precise but not `DisjPrecise`, and the left-biased `fpGreedy` still
recovers every witness of it, while the right-biased `fpGreedyR` does not. -/
theorem fpGreedy_recoversEveryWitness_CFlip_not_disjPrecise :
    Precise CFlip ∧
    ¬ DisjPrecise CFlip ∧
    sat CFlip hTwo ∧
    RecoversEveryWitness fpGreedy CFlip ∧
    ¬ RecoversEveryWitness fpGreedyR CFlip := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g g₁ g₂ hs₁ hs₂ h₁ h₂
    obtain ⟨a0, a1, ar⟩ := sat_CFlip_shape g₁ h₁
    obtain ⟨b0, b1, br⟩ := sat_CFlip_shape g₂ h₂
    have agree : ∀ x, (g₁ x).isSome = true → (g₂ x).isSome = true → g₁ x = g₂ x := by
      intro x hx hy
      cases e₁ : g₁ x with
      | none => simp [e₁] at hx
      | some v =>
        cases e₂ : g₂ x with
        | none => simp [e₂] at hy
        | some w => rw [← hs₁ x v e₁, ← hs₂ x w e₂]
    funext x
    by_cases hx0 : x = 0
    · subst hx0; exact agree 0 a0 b0
    · by_cases hx1 : x = 1
      · subst hx1; exact agree 1 a1 b1
      · rw [ar x hx0 hx1, br x hx0 hx1]
  · intro hdp
    have hp := hdp.1.1
    have := hp hTwo (Heap.single 0 0) hTwo sub_single0_hTwo (fun _ _ h => h)
      (Or.inl ((sat_owned_iff 0 _).2 ⟨rfl, fun a ha => by simp [ha]⟩))
      (Or.inr sat_owned0_sep_owned1_hTwo)
    have := congrFun this 1
    simp at this
  · refine ⟨Heap.single 0 0, Heap.single 1 0, ?_, ?_,
      Or.inl ((sat_owned_iff 0 _).2 ⟨rfl, fun a ha => by simp [ha]⟩),
      (sat_owned_iff 1 _).2 ⟨rfl, fun a ha => by simp [ha]⟩⟩
    · intro a; by_cases h : a = 0 <;> simp [h]
    · intro a
      by_cases h0 : a = 0
      · subst h0; rfl
      · by_cases h1 : a = 1
        · subst h1; rfl
        · simp [h0, h1, hTwo_of_ne a h0 h1]
  · intro g g' hs hsat
    obtain ⟨h0, h1, hr⟩ := sat_CFlip_shape g' hsat
    cases e0 : g' 0 with
    | none => simp [e0] at h0
    | some v0 =>
      cases e1 : g' 1 with
      | none => simp [e1] at h1
      | some v1 =>
        have hg0 : g 0 = some v0 := hs 0 v0 e0
        have hg1 : g 1 = some v1 := hs 1 v1 e1
        refine ⟨[0, 1], ?_, ?_, ?_⟩
        · simp [CFlip, fpGreedy, owned, hg0, hg1]
        · intro a ha
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl <;> simp [hg0, hg1]
        · funext a
          by_cases ha0 : a = 0
          · subst ha0; simp [hg0, e0]
          · by_cases ha1 : a = 1
            · subst ha1; simp [hg1, e1]
            · simp [ha0, ha1, hr a ha0 ha1]
  · intro hrec
    have hsat : sat CFlip hTwo := by
      refine ⟨Heap.single 0 0, Heap.single 1 0, ?_, ?_,
        Or.inl ((sat_owned_iff 0 _).2 ⟨rfl, fun a ha => by simp [ha]⟩),
        (sat_owned_iff 1 _).2 ⟨rfl, fun a ha => by simp [ha]⟩⟩
      · intro a; by_cases h : a = 0 <;> simp [h]
      · intro a
        by_cases h0 : a = 0
        · subst h0; rfl
        · by_cases h1 : a = 1
          · subst h1; rfl
          · simp [h0, h1, hTwo_of_ne a h0 h1]
    obtain ⟨F, hF, -⟩ := hrec hTwo hTwo (fun _ _ h => h) hsat
    have : fpGreedyR CFlip hTwo = none := by decide
    rw [this] at hF
    cases hF

/-- **A fixed program can be characterized despite imprecise contracts.** For
`call C C skip`, whose contracts are all imprecise, the strict search monitor accepts a
run if and only if the run satisfies its contracts. -/
theorem accepts_strict_fpSearch_iff_satisfies_call_C_C_skip :
    (∀ A ∈ (Prog.call C C .skip).contracts, ¬ Precise A) ∧
    ∀ (h : Heap) (O : List Addr),
      Accepts MonCfg.strict fpSearch (.call C C .skip) h O ↔
        Satisfies (.call C C .skip) h O := by
  refine ⟨accepts_fpGreedy_call_C_C_skip_of_satisfies.1, ?_⟩
  intro h O
  constructor
  · intro hacc
    exact satisfiesBy_imp_satisfies fpSearch _ h O
      (accepts_imp_satisfiesBy_of_strategySound fpSearch fpSearch_strategySound
        MonCfg.strict rfl rfl _ h O hacc)
  · intro ⟨F₀, hpre₀, _, _⟩
    apply satisfiesBy_imp_accepts
    cases e0 : (h.restrict O) 0 with
    | some v0 =>
      have h0O : 0 ∈ O := by by_cases hm : 0 ∈ O; exact hm; simp [hm] at e0
      have hv0 : h 0 = some v0 := by simpa [h0O] using e0
      refine ⟨[0], by simp [fpSearch, fpAll, C, owned, h0O, hv0],
        ⟨by simp [h0O, hv0], Or.inl ((sat_owned_iff 0 _).2 ⟨by simp [h0O, hv0], fun a ha => by simp [ha]⟩)⟩,
        trivial, [0], by simp [fpSearch, fpAll, C, owned, exec, hv0], fun _ => Iff.rfl,
        ⟨by simp [exec, hv0], Or.inl ((sat_owned_iff 0 _).2 ⟨by simp [exec, hv0], fun a ha => by simp [ha]⟩)⟩⟩
    | none =>
      rcases hpre₀.2 with h0 | h1
      · have his0 := ((sat_owned_iff 0 _).1 h0).1
        by_cases hm0 : 0 ∈ F₀
        · simp only [Heap.restrict_apply, hm0, ↓reduceIte] at his0
          rw [Heap.restrict_apply] at e0
          rw [e0] at his0; simp at his0
        · simp [hm0] at his0
      · have his1 := ((sat_owned_iff 1 _).1 h1).1
        have h1F₀ : 1 ∈ F₀ := by by_cases hm : 1 ∈ F₀; exact hm; simp [hm] at his1
        simp only [Heap.restrict_apply, h1F₀, ↓reduceIte] at his1
        cases e1 : (h.restrict O) 1 with
        | none =>
          rw [Heap.restrict_apply] at e1
          rw [e1] at his1; simp at his1
        | some v1 =>
          have h1O : 1 ∈ O := by by_cases hm : 1 ∈ O; exact hm; simp [hm] at e1
          have hv1 : h 1 = some v1 := by simpa [h1O] using e1
          have h0none : (if 0 ∈ O then h 0 else none) = none := by simpa using e0
          refine ⟨[1], by simp [fpSearch, fpAll, C, owned, h0none, h1O, hv1],
            ⟨by simp [h1O, hv1], Or.inr ((sat_owned_iff 1 _).2 ⟨by simp [h1O, hv1], fun a ha => by simp [ha]⟩)⟩,
            trivial, [1], by simp [fpSearch, fpAll, C, owned, exec, hv1], fun _ => Iff.rfl,
            ⟨by simp [exec, hv1],
              Or.inr ((sat_owned_iff 1 _).2 ⟨by simp [exec, hv1], fun a ha => by simp [ha]⟩)⟩⟩

/-- An annotated call whose unannotated body reads byte 1, outside the callee's
footprint `[0]`. -/
def pUnannotRead : Prog := .call (owned 0) (owned 0) (.unannot (.read 1))

/-- **Out-of-frame reads.** The unannotated helper of `pUnannotRead` reads a byte
outside its frame: the heap is unchanged (so a check that only compares the heap before
and after the call would pass), the monitor that trusts unannotated callees accepts the
run, yet the run violates `UnannotConfined` and its contracts, and the strict monitor
rejects it. -/
theorem trusted_unannot_read_outside_footprint_accepted_heap_unchanged :
    StrategySound fpAtom ∧
    (⟨true, false⟩ : MonCfg).leakCheck = true ∧
    Accepts ⟨true, false⟩ fpAtom pUnannotRead hTwo [0, 1] ∧
    exec pUnannotRead hTwo = hTwo ∧
    ¬ UnannotConfined fpAtom pUnannotRead hTwo [0, 1] ∧
    ¬ Satisfies pUnannotRead hTwo [0, 1] ∧
    ¬ Accepts MonCfg.strict fpAtom pUnannotRead hTwo [0, 1] := by
  refine ⟨fpAtom_strategySound, rfl, by decide, rfl, ?_, ?_, by decide⟩
  · intro h
    have := h [0] (by decide) rfl
    simp at this
  · rintro ⟨F, hF, ⟨h1, -⟩, -⟩
    exact not_mem_one_of_isFootprint_owned0 F hF h1

/-- `restrict_witnesses_sep` requires only `sat A (g.restrict F)`, which permits
unallocated addresses in `F` (here `99`), unlike `IsFootprint`. -/
theorem restrict_witnesses_sep_allows_unallocated_addrs :
    sat (owned 0) (hTwo.restrict [0, 99]) ∧
    SepP (fun g₁ => g₁ = hTwo.restrict [0, 99] ∧ sat (owned 0) g₁)
         (fun g₂ => g₂ = hTwo.remove [0, 99]) hTwo ∧
    ¬ IsFootprint (owned 0) hTwo [0, 99] := by
  have hsat : sat (owned 0) (hTwo.restrict [0, 99]) := by
    refine (sat_owned_iff 0 _).2 ⟨by decide, ?_⟩
    intro a ha
    by_cases h99 : a = 99
    · subst h99; simp [hTwo_of_ne 99 (by decide) (by decide)]
    · simp [ha, h99]
  refine ⟨hsat, restrict_witnesses_sep (owned 0) hTwo [0, 99] hsat, ?_⟩
  rintro ⟨hall, -⟩
  have := hall 99 (by simp)
  simp [hTwo_of_ne 99 (by decide) (by decide)] at this

end Toy.Monitor
