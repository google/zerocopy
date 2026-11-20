import ToyMonitor.Examples

/-!
# Proof infrastructure

Auxiliary lemmas about heaps, footprints, the footprint strategies, and the
ownership-depth invariant of the monitor, used by the proofs in `ToyMonitor.Results`.
-/

namespace Toy.Monitor

open Assn

theorem sub_trans {g₁ g₂ g₃ : Heap} (h₁ : Heap.Sub g₁ g₂) (h₂ : Heap.Sub g₂ g₃) :
    Heap.Sub g₁ g₃ :=
  fun a v h => h₂ a v (h₁ a v h)

theorem sub_restrict (g : Heap) (F : List Addr) : Heap.Sub (g.restrict F) g := by
  intro a v h
  simp only [Heap.restrict] at h
  split at h
  · exact h
  · contradiction

theorem sub_union_left {g₁ g₂ : Heap} : Heap.Sub g₁ (Heap.union g₁ g₂) := by
  intro a v h
  simp [Heap.union, h]

theorem sub_union_right {g₁ g₂ : Heap} (hd : Heap.Disjoint g₁ g₂) :
    Heap.Sub g₂ (Heap.union g₁ g₂) := by
  intro a v h
  rcases hd a with h1 | h2
  · simp [Heap.union, h1, h]
  · rw [h] at h2; contradiction

theorem precise_cell (p : Addr) (P : Val → Bool) : Precise (.cell p P) := by
  intro g g₁ g₂ hs₁ hs₂ ⟨v₁, hv₁, _, hr₁⟩ ⟨v₂, hv₂, _, hr₂⟩
  funext a
  by_cases ha : a = p
  · subst ha
    have := (hs₁ a v₁ hv₁).symm.trans (hs₂ a v₂ hv₂)
    cases this
    rw [hv₁, hv₂]
  · rw [hr₁ a ha, hr₂ a ha]

theorem precise_pure (b : Bool) : Precise (.pure b) := by
  intro _ g₁ g₂ _ _ ⟨_, hr₁⟩ ⟨_, hr₂⟩
  funext a; rw [hr₁ a, hr₂ a]

theorem isFootprint_sep_append {A B : Assn} {g : Heap} {F₁ F₂ : List Addr}
    (h₁ : IsFootprint A g F₁) (h₂ : IsFootprint B (g.remove F₁) F₂) :
    IsFootprint (.sep A B) g (F₁ ++ F₂) := by
  have hdisjF : ∀ a, a ∈ F₂ → a ∉ F₁ := by
    intro a ha₂ ha₁
    have := h₂.1 a ha₂
    simp [ha₁] at this
  refine ⟨?_, g.restrict F₁, g.restrict F₂, ?_, ?_, h₁.2, ?_⟩
  · intro a ha
    rcases List.mem_append.1 ha with ha₁ | ha₂
    · exact h₁.1 a ha₁
    · have := h₂.1 a ha₂
      simp [hdisjF a ha₂] at this
      exact this
  · intro a
    by_cases ha₁ : a ∈ F₁
    · right
      have : a ∉ F₂ := fun ha₂ => hdisjF a ha₂ ha₁
      simp [this]
    · left; simp [ha₁]
  · intro a
    by_cases ha₁ : a ∈ F₁
    · have hg : (g a).isSome = true := h₁.1 a ha₁
      cases e : g a with
      | none => simp [e] at hg
      | some v => simp [ha₁, e]
    · simp [ha₁]
  · have heq : (g.remove F₁).restrict F₂ = g.restrict F₂ := by
      funext a
      by_cases ha₂ : a ∈ F₂
      · simp [ha₂, hdisjF a ha₂]
      · simp [ha₂]
    rw [← heq]
    exact h₂.2

theorem fpAll_sound (A : Assn) (g : Heap) (F : List Addr) (hF : F ∈ fpAll A g) :
    IsFootprint A g F := by
  induction A generalizing g F with
  | cell p P =>
    simp only [fpAll] at hF
    cases e : g p with
    | none => simp [e] at hF
    | some v =>
      simp only [e] at hF
      split at hF
      · rename_i hP
        simp at hF; subst hF
        exact ⟨by simp [e], v, by simp [e], hP, fun a ha => by simp [ha]⟩
      · simp at hF
  | pure b =>
    simp only [fpAll] at hF
    split at hF
    · rename_i hb
      simp at hF; subst hF
      exact ⟨by simp, hb, fun a => by simp⟩
    · simp at hF
  | sep A B ihA ihB =>
    simp only [fpAll, List.mem_flatMap, List.mem_map] at hF
    obtain ⟨F₁, hF₁, F₂, hF₂, rfl⟩ := hF
    exact isFootprint_sep_append (ihA g F₁ hF₁) (ihB (g.remove F₁) F₂ hF₂)
  | or A B ihA ihB =>
    simp only [fpAll, List.mem_append] at hF
    rcases hF with hF | hF
    · exact ⟨(ihA g F hF).1, Or.inl (ihA g F hF).2⟩
    · exact ⟨(ihB g F hF).1, Or.inr (ihB g F hF).2⟩

theorem sub_remove_of_disjoint {g g₁ g₂ : Heap} {F₁ : List Addr}
    (hs₂ : Heap.Sub g₂ g) (hd : Heap.Disjoint g₁ g₂)
    (hF₁ : ∀ a ∈ F₁, (g a).isSome = true) (hr₁ : g.restrict F₁ = g₁) :
    Heap.Sub g₂ (g.remove F₁) := by
  intro a v hv
  have hg₁a : g₁ a = none := by
    rcases hd a with h | h
    · exact h
    · rw [hv] at h; contradiction
  have haF₁ : a ∉ F₁ := by
    intro hm
    have his := hF₁ a hm
    have : g.restrict F₁ a = g a := by simp [hm]
    rw [hr₁, hg₁a] at this
    simp [← this] at his
  simp [haF₁, hs₂ a v hv]

theorem restrict_append_eq_union {g g' g₁ g₂ : Heap} {F₁ F₂ : List Addr}
    (hu : ∀ a, g' a = Heap.union g₁ g₂ a)
    (hF₁ : ∀ a ∈ F₁, (g a).isSome = true) (hr₁ : g.restrict F₁ = g₁)
    (hr₂ : (g.remove F₁).restrict F₂ = g₂) :
    g.restrict (F₁ ++ F₂) = g' := by
  funext a
  rw [hu a]
  by_cases ha₁ : a ∈ F₁
  · have his := hF₁ a ha₁
    have hg₁ : g₁ a = g a := by rw [← hr₁]; simp [ha₁]
    cases e : g a with
    | none => simp [e] at his
    | some v => simp [ha₁, hg₁, e]
  · have hg₁ : g₁ a = none := by rw [← hr₁]; simp [ha₁]
    have hg₂ : g₂ a = if a ∈ F₂ then g a else none := by
      rw [← hr₂]
      by_cases ha₂ : a ∈ F₂ <;> simp [ha₂, ha₁]
    simp [ha₁, hg₁, hg₂]

theorem fpAll_complete_raw (A : Assn) :
    ∀ g g', Heap.Sub g' g → sat A g' →
      ∃ F ∈ fpAll A g, (∀ a ∈ F, (g a).isSome = true) ∧ g.restrict F = g' := by
  induction A with
  | cell p P =>
    intro g g' hs ⟨v, hv, hP, hr⟩
    have hgp := hs p v hv
    refine ⟨[p], by simp [fpAll, hgp, hP], by simp [hgp], ?_⟩
    funext a
    by_cases ha : a = p
    · subst ha; simp [hgp, hv]
    · simp [ha, hr a ha]
  | pure b =>
    intro g g' _ ⟨hb, hr⟩
    refine ⟨[], by simp [fpAll, hb], by simp, ?_⟩
    funext a; simp [hr a]
  | or B C ihB ihC =>
    intro g g' hs hsat
    rcases hsat with hB | hC
    · obtain ⟨F, hF, ha, hr⟩ := ihB g g' hs hB
      exact ⟨F, List.mem_append_left _ hF, ha, hr⟩
    · obtain ⟨F, hF, ha, hr⟩ := ihC g g' hs hC
      exact ⟨F, List.mem_append_right _ hF, ha, hr⟩
  | sep B C ihB ihC =>
    intro g g' hs ⟨g₁, g₂, hd, hu, hB, hC⟩
    have hs₁ : Heap.Sub g₁ g := fun a v hv => hs a v (by rw [hu a]; simp [hv])
    have hs₂ : Heap.Sub g₂ g := fun a v hv => hs a v (by
      rw [hu a]
      rcases hd a with e | e
      · simp [e, hv]
      · rw [hv] at e; contradiction)
    obtain ⟨F₁, hm₁, ha₁, hr₁⟩ := ihB g g₁ hs₁ hB
    obtain ⟨F₂, hm₂, ha₂, hr₂⟩ := ihC (g.remove F₁) g₂ (sub_remove_of_disjoint hs₂ hd ha₁ hr₁) hC
    refine ⟨F₁ ++ F₂, ?_, ?_, restrict_append_eq_union hu ha₁ hr₁ hr₂⟩
    · simp only [fpAll, List.mem_flatMap, List.mem_map]
      exact ⟨F₁, hm₁, F₂, hm₂, rfl⟩
    · intro a ha
      rcases List.mem_append.1 ha with h1 | h2
      · exact ha₁ a h1
      · have := ha₂ a h2
        by_cases h1 : a ∈ F₁
        · exact ha₁ a h1
        · simpa [h1] using this

theorem satisfies_congr_mem {p : Prog} {h : Heap} {O₁ O₂ : List Addr}
    (heq : ∀ a, a ∈ O₁ ↔ a ∈ O₂) (hs : Satisfies p h O₁) : Satisfies p h O₂ := by
  induction p generalizing h O₁ O₂ with
  | skip => trivial
  | read a => exact ⟨(heq a).1 hs.1, hs.2⟩
  | write a v => exact ⟨(heq a).1 hs.1, hs.2⟩
  | seq p q ihp ihq => exact ⟨ihp heq hs.1, ihq heq hs.2⟩
  | unannot body ih => exact ih heq hs
  | call P Q body _ =>
    obtain ⟨F, hpre, hbody, hpost⟩ := hs
    have hrest : h.restrict O₁ = h.restrict O₂ := by
      funext a; simp [heq a]
    exact ⟨F, hrest ▸ hpre, hbody, hpost⟩

/-- Ownership-depth invariant of the monitor in frame `d`: frame `d` owns exactly the
addresses in `O`, and no byte is owned by a deeper frame. -/
def OwnInv (o : Own) (d : Nat) (O : List Addr) : Prop :=
  (∀ a, o a = some d ↔ a ∈ O) ∧ (∀ a d', d < d' → o a ≠ some d')

theorem frag_eq_restrict {h : Heap} {o : Own} {d : Nat} {O : List Addr}
    (hinv : OwnInv o d O) : frag h o d = h.restrict O := by
  funext a
  simp only [frag, Heap.restrict]
  by_cases ha : a ∈ O
  · simp [ha, (hinv.1 a).2 ha]
  · have : o a ≠ some d := fun ho => ha ((hinv.1 a).1 ho)
    simp [ha, this]

theorem ownInv_initOwn (O : List Addr) : OwnInv (initOwn O) 0 O := by
  refine ⟨fun a => ?_, fun a d' hd => ?_⟩
  · simp [initOwn]
  · simp only [initOwn]
    split
    · intro h; injection h with h; omega
    · intro h; contradiction

theorem ownInv_transfer_down {o : Own} {d : Nat} {O F : List Addr}
    (hinv : OwnInv o d O) (hsub : ∀ a ∈ F, a ∈ O) :
    OwnInv (transfer F d (d + 1) o) (d + 1) F := by
  refine ⟨fun a => ?_, fun a d' hd => ?_⟩
  · simp only [transfer]
    by_cases ha : a ∈ F
    · simp [ha, (hinv.1 a).2 (hsub a ha)]
    · have hne : o a ≠ some (d + 1) := hinv.2 a (d + 1) (by omega)
      simp [ha, hne]
  · simp only [transfer]
    split
    · intro h; injection h with h; omega
    · exact hinv.2 a d' (by omega)

theorem transfer_roundtrip {o : Own} {d : Nat} {O F F' : List Addr}
    (hinv : OwnInv o d O) (hsub : ∀ a ∈ F, a ∈ O) (hmem : ∀ a, a ∈ F' ↔ a ∈ F) :
    transfer F' (d + 1) d (transfer F d (d + 1) o) = o := by
  funext a
  simp only [transfer]
  by_cases ha : a ∈ F
  · have ha' : a ∈ F' := (hmem a).2 ha
    have hod : o a = some d := (hinv.1 a).2 (hsub a ha)
    simp [ha, ha', hod]
  · have ha' : a ∉ F' := fun h => ha ((hmem a).1 h)
    simp [ha, ha']

/-- A run satisfying its contracts with the strategy's footprints is accepted by the
monitor in either instrumentation mode, and ownership is restored. -/
theorem monitorAux_of_satisfiesBy (s : Strategy) (cfg : MonCfg)
    (p : Prog) (chk : Bool) (h : Heap) (o : Own) (d : Nat) (O : List Addr)
    (hinv : OwnInv o d O) (hsat : SatisfiesBy s p h O) :
    monitorAux cfg s chk p h o d = some o := by
  induction p generalizing chk h o d O with
  | skip => rfl
  | read a => cases chk <;> simp [monitorAux, (hinv.1 a).2 hsat.1, hsat.2]
  | write a _ => cases chk <;> simp [monitorAux, (hinv.1 a).2 hsat.1, hsat.2]
  | seq p q ihp ihq =>
    simp [monitorAux, ihp chk h o d O hinv hsat.1, ihq chk (exec p h) o d O hinv hsat.2]
  | unannot body ih =>
    simp only [monitorAux]
    exact ih _ h o d O hinv hsat
  | call P Q body ih =>
    obtain ⟨F, hsP, hpre, hbody, F', hsQ, hmem, _⟩ := hsat
    have hsub : ∀ a ∈ F, a ∈ O := by
      intro a ha
      have := hpre.1 a ha
      by_cases hO : a ∈ O
      · exact hO
      · simp [hO] at this
    have hallF : (F.all fun a => decide (o a = some d)) = true := by
      rw [List.all_eq_true]
      intro a ha
      simp [(hinv.1 a).2 (hsub a ha)]
    have hinv₁ := ownInv_transfer_down hinv hsub
    have hmonB := ih true h (transfer F d (d + 1) o) (d + 1) F hinv₁ hbody
    have hallF' : (F'.all fun a => decide (transfer F d (d + 1) o a = some (d + 1))) = true := by
      rw [List.all_eq_true]
      intro a ha'
      simp [(hinv₁.1 a).2 ((hmem a).1 ha')]
    have hrt := transfer_roundtrip hinv hsub hmem
    have hnoLeak : (F.any fun a => decide (o a = some (d + 1))) = false := by
      rw [List.any_eq_false]
      intro a _
      simp [hinv.2 a (d + 1) (by omega)]
    simp [monitorAux, frag_eq_restrict hinv, hsP, hallF, hmonB,
      frag_eq_restrict hinv₁, hsQ, hallF', hrt, hnoLeak]

/-- Soundness of the monitor in both instrumentation modes. If the strategy is sound and
the leak check is on, an accepted run (from a state satisfying the ownership-depth
invariant) satisfies its contracts with the strategy's footprints and restores the
ownership map, provided that uninstrumented code (reachable only when
`cfg.checkUnannot = false`) is confined to its frame. -/
theorem monitorAux_sound (s : Strategy) (hs : StrategySound s) (cfg : MonCfg)
    (hleak : cfg.leakCheck = true)
    (p : Prog) (chk : Bool) (h : Heap) (o o' : Own) (d : Nat) (O : List Addr)
    (hinv : OwnInv o d O)
    (hmon : monitorAux cfg s chk p h o d = some o')
    (hchk : chk = false → cfg.checkUnannot = false)
    (hconf : cfg.checkUnannot = false → UnannotConfinedAux s (!chk) p h O) :
    o' = o ∧ SatisfiesBy s p h O := by
  induction p generalizing chk h o o' d O with
  | skip =>
    simp only [monitorAux, Option.some.injEq] at hmon
    exact ⟨hmon.symm, trivial⟩
  | read a =>
    cases chk with
    | true =>
      simp only [monitorAux, ↓reduceIte] at hmon
      split at hmon
      · rename_i hc
        simp only [Option.some.injEq] at hmon
        exact ⟨hmon.symm, (hinv.1 a).1 hc.1, hc.2⟩
      · contradiction
    | false =>
      simp only [monitorAux, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hmon
      exact ⟨hmon.symm, hconf (hchk rfl) rfl⟩
  | write a _ =>
    cases chk with
    | true =>
      simp only [monitorAux, ↓reduceIte] at hmon
      split at hmon
      · rename_i hc
        simp only [Option.some.injEq] at hmon
        exact ⟨hmon.symm, (hinv.1 a).1 hc.1, hc.2⟩
      · contradiction
    | false =>
      simp only [monitorAux, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hmon
      exact ⟨hmon.symm, hconf (hchk rfl) rfl⟩
  | seq p q ihp ihq =>
    simp only [monitorAux] at hmon
    cases e₁ : monitorAux cfg s chk p h o d with
    | none => simp [e₁] at hmon
    | some o₁ =>
      simp only [e₁] at hmon
      obtain ⟨ho₁, hsat₁⟩ := ihp chk h o o₁ d O hinv e₁ hchk (fun hc => (hconf hc).1)
      subst o₁
      obtain ⟨ho', hsat₂⟩ := ihq chk (exec p h) o o' d O hinv hmon hchk (fun hc => (hconf hc).2)
      exact ⟨ho', hsat₁, hsat₂⟩
  | unannot body ih =>
    simp only [monitorAux] at hmon
    refine ih (chk && cfg.checkUnannot) h o o' d O hinv hmon ?_ ?_
    · intro h0
      cases hc : cfg.checkUnannot
      · rfl
      · rw [hc, Bool.and_true] at h0
        have := hchk h0
        rw [hc] at this
        exact this
    · intro hc
      have := hconf hc
      rw [hc, Bool.and_false]
      exact this
  | call P Q body ih =>
    simp only [monitorAux, frag_eq_restrict hinv] at hmon
    cases hsP : s P (h.restrict O) with
    | none => simp [hsP] at hmon
    | some F =>
      simp only [hsP] at hmon
      split at hmon
      · rename_i hallF
        rw [List.all_eq_true] at hallF
        have hsub : ∀ a ∈ F, a ∈ O := fun a ha => (hinv.1 a).1 (of_decide_eq_true (hallF a ha))
        have hinv₁ := ownInv_transfer_down hinv hsub
        cases eB : monitorAux cfg s true body h (transfer F d (d + 1) o) (d + 1) with
        | none => simp [eB] at hmon
        | some o₂ =>
          simp only [eB] at hmon
          obtain ⟨ho₂, hbody⟩ := ih true h (transfer F d (d + 1) o) o₂ (d + 1) F hinv₁ eB
            (fun h0 => absurd h0 (by decide)) (fun hc => hconf hc F hsP)
          subst ho₂
          rw [frag_eq_restrict hinv₁] at hmon
          cases hsQ : s Q ((exec body h).restrict F) with
          | none => simp [hsQ] at hmon
          | some F' =>
            simp only [hsQ] at hmon
            split at hmon
            · rename_i hallF'
              rw [List.all_eq_true] at hallF'
              have hF'_sub : ∀ a ∈ F', a ∈ F :=
                fun a ha' => (hinv₁.1 a).1 (of_decide_eq_true (hallF' a ha'))
              split at hmon
              · contradiction
              · rename_i hnoLeak
                simp only [hleak, Bool.true_and, Bool.not_eq_true] at hnoLeak
                rw [List.any_eq_false] at hnoLeak
                have hF_sub : ∀ a ∈ F, a ∈ F' := by
                  intro a ha
                  have hnot := hnoLeak a ha
                  by_cases ha' : a ∈ F'
                  · exact ha'
                  · exfalso
                    apply hnot
                    have hod : o a = some d := (hinv.1 a).2 (hsub a ha)
                    simp [transfer, ha', ha, hod]
                have hmem : ∀ a, a ∈ F' ↔ a ∈ F :=
                  fun a => ⟨hF'_sub a, hF_sub a⟩
                simp only [Option.some.injEq] at hmon
                rw [transfer_roundtrip hinv hsub hmem] at hmon
                exact ⟨hmon.symm, F, hsP, hs P (h.restrict O) F hsP, hbody,
                  F', hsQ, hmem, hs Q ((exec body h).restrict F) F' hsQ⟩
            · contradiction
      · contradiction

end Toy.Monitor
