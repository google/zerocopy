import Implicature.Reader

/-!
# General lemmas

Unfolding lemmas for the semantics, the finite maximality argument behind innocent exclusion
(a world whose set of falsified alternatives is inclusion-maximal exists above every world
satisfying the prejacent), and small lemmas about readings and blockers. Everything here is
proved; the main results in `Results.lean` are assembled from these lemmas.
-/

namespace Toy.Implicature

/-! ## Unfolding -/

theorem holds_and_eq (S : Space) (w : S.World) (c d : Claim) :
    S.holds w (.and c d) = (S.holds w c && S.holds w d) := rfl

theorem holds_not_eq (S : Space) (w : S.World) (c : Claim) :
    S.holds w (.not c) = !S.holds w c := rfl

theorem holds_all_eq (S : Space) (w : S.World) (c : Claim) :
    S.holds w (.all c) = S.params.all fun y => S.evalAt w y c := rfl

theorem holds_exh (S : Space) (A : List Claim) (σ : Claim) (w : S.World) :
    S.holds w (exh S A σ) = (S.holds w σ && (ieList S σ A).all fun a => !S.holds w a) := by
  unfold exh
  rw [holds_conjList, List.all_cons, List.all_map]
  rfl

theorem holds_naiveExh (S : Space) (A : List Claim) (σ : Claim) (w : S.World) :
    S.holds w (naiveExh S A σ) =
      (S.holds w σ && (naiveExcl S σ A).all fun a => !S.holds w a) := by
  unfold naiveExh
  rw [holds_conjList, List.all_cons, List.all_map]
  rfl

theorem sat_singleton_iff {S : Space} {c : Claim} :
    Sat S [c] ↔ ∃ w ∈ S.worlds, S.holds w c = true := by
  simp [Sat]

theorem sat_pair_iff {S : Space} {c d : Claim} :
    Sat S [c, d] ↔ ∃ w ∈ S.worlds, S.holds w c = true ∧ S.holds w d = true := by
  simp [Sat]

theorem entails_singleton_iff {S : Space} {c d : Claim} :
    Entails S [c] d ↔ ∀ w ∈ S.worlds, S.holds w c = true → S.holds w d = true := by
  simp [Entails]

/-- A satisfiable report does not entail both a claim and its negation. -/
theorem not_entails_and_not_of_sat {S : Space} {E : List Claim} {c : Claim} (hE : Sat S E)
    (h1 : Entails S E c) (h2 : Entails S E (.not c)) : False := by
  obtain ⟨w, hw, hEw⟩ := hE
  have a := h1 w hw hEw
  have b := h2 w hw hEw
  rw [holds_not_eq, a] at b
  cases b

/-! ## Counting falsified alternatives -/

theorem countP_le_of_imp {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = true → q a = true) → l.countP p ≤ l.countP q
  | [], _ => by simp
  | x :: xs, h => by
    have ih := countP_le_of_imp p q xs (fun a ha => h a (List.mem_cons_of_mem x ha))
    simp only [List.countP_cons]
    by_cases hp : p x = true
    · have hq : q x = true := h x List.mem_cons_self hp
      simp [hp, hq]
      omega
    · have hpf : p x = false := by simpa using hp
      cases hq : q x <;> simp [hpf] <;> omega

theorem imp_of_countP_le {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, p a = true → q a = true) → l.countP q ≤ l.countP p →
      ∀ a ∈ l, q a = true → p a = true
  | [], _, _ => by simp
  | x :: xs, h, hc => by
    have hxs : ∀ a ∈ xs, p a = true → q a = true := fun a ha => h a (List.mem_cons_of_mem x ha)
    have hle := countP_le_of_imp p q xs hxs
    intro a ha hqa
    simp only [List.countP_cons] at hc
    by_cases hp : p x = true
    · have hq : q x = true := h x List.mem_cons_self hp
      simp [hp, hq] at hc
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hp
      · exact imp_of_countP_le p q xs hxs hc a ha' hqa
    · by_cases hq : q x = true
      · simp [hp, hq] at hc
        omega
      · simp [hp, hq] at hc
        rcases List.mem_cons.mp ha with rfl | ha'
        · exact absurd hqa hq
        · exact imp_of_countP_le p q xs hxs hc a ha' hqa

theorem exists_max_of_mem {α : Type} (f : α → Nat) :
    ∀ (l : List α) (x0 : α), x0 ∈ l → ∃ x ∈ l, ∀ y ∈ l, f y ≤ f x
  | [], _, h => absurd h List.not_mem_nil
  | x :: xs, _, _ => by
    by_cases hxs : xs = []
    · subst hxs
      exact ⟨x, List.mem_singleton_self x, by simp⟩
    · obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil xs hxs
      obtain ⟨m, hm, hmax⟩ := exists_max_of_mem f xs z hz
      by_cases hle : f m ≤ f x
      · refine ⟨x, List.mem_cons_self, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_refl _
        · exact Nat.le_trans (hmax y hy) hle
      · refine ⟨m, List.mem_cons_of_mem x hm, fun y hy => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · exact hmax y hy

/-- Number of alternatives of `A` that are false at `w`. -/
def fcount (S : Space) (A : List Claim) (w : S.World) : Nat :=
  A.countP fun a => !S.holds w a

theorem falsSub_iff {S : Space} {A : List Claim} {w v : S.World} :
    falsSub S A w v = true ↔ ∀ a ∈ A, S.holds w a = false → S.holds v a = false := by
  unfold falsSub
  rw [List.all_eq_true]
  apply forall_congr'
  intro a
  apply imp_congr_right
  intro _
  cases S.holds w a <;> cases S.holds v a <;> simp

theorem falsSub_refl (S : Space) (A : List Claim) (w : S.World) : falsSub S A w w = true :=
  falsSub_iff.mpr fun _ _ h => h

theorem falsSub_trans {S : Space} {A : List Claim} {u v w : S.World}
    (h1 : falsSub S A u v = true) (h2 : falsSub S A v w = true) : falsSub S A u w = true :=
  falsSub_iff.mpr fun a ha hu => falsSub_iff.mp h2 a ha (falsSub_iff.mp h1 a ha hu)

theorem fcount_le_of_falsSub {S : Space} {A : List Claim} {w v : S.World}
    (h : falsSub S A w v = true) : fcount S A w ≤ fcount S A v := by
  apply countP_le_of_imp
  intro a ha hw
  have := falsSub_iff.mp h a ha (by simpa using hw)
  simp [this]

theorem falsSub_of_fcount_le {S : Space} {A : List Claim} {w v : S.World}
    (h : falsSub S A w v = true) (hc : fcount S A v ≤ fcount S A w) :
    falsSub S A v w = true := by
  refine falsSub_iff.mpr fun a ha hv => ?_
  have key := imp_of_countP_le (fun a => !S.holds w a) (fun a => !S.holds v a) A
    (fun b hb hw => by
      have := falsSub_iff.mp h b hb (by simpa using hw)
      simp [this]) hc a ha (by simp [hv])
  simpa using key

theorem maxFals_iff {S : Space} {σ : Claim} {A : List Claim} {w : S.World} :
    maxFals S σ A w = true ↔
      S.holds w σ = true ∧
        ∀ v ∈ S.worlds, S.holds v σ = true → falsSub S A w v = true → falsSub S A v w = true := by
  unfold maxFals
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v hv hvσ hwv => ?_⟩
    rcases h2 v hv with h | h
    · simp [hvσ, hwv] at h
    · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun v hv => ?_⟩
    by_cases hc : (S.holds v σ && falsSub S A w v) = true
    · simp only [Bool.and_eq_true] at hc
      exact Or.inr (h2 v hv hc.1 hc.2)
    · exact Or.inl (by simpa using hc)

theorem ieB_iff {S : Space} {σ : Claim} {A : List Claim} {a : Claim} :
    ieB S σ A a = true ↔ ∀ w ∈ S.worlds, maxFals S σ A w = true → S.holds w a = false := by
  unfold ieB
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  constructor
  · intro h w hw hm
    rcases h w hw with h | h
    · rw [hm] at h; cases h
    · exact h
  · intro h w hw
    cases hm : maxFals S σ A w
    · exact Or.inl rfl
    · exact Or.inr (h w hw hm)

theorem mem_ieList_iff_ieB {S : Space} {σ : Claim} {A : List Claim} {a : Claim} :
    a ∈ ieList S σ A ↔ a ∈ A ∧ ieB S σ A a = true :=
  List.mem_filter

/-- Above every world satisfying `σ` there is a `σ`-world whose set of falsified alternatives
is inclusion-maximal among the `σ`-worlds of the space. -/
theorem exists_maxFals_above (S : Space) (σ : Claim) (A : List Claim) {w0 : S.World}
    (hw0 : w0 ∈ S.worlds) (hσ : S.holds w0 σ = true) :
    ∃ w ∈ S.worlds, falsSub S A w0 w = true ∧ maxFals S σ A w = true := by
  let L := S.worlds.filter fun v => S.holds v σ && falsSub S A w0 v
  have h0 : w0 ∈ L := List.mem_filter.mpr ⟨hw0, by simp [hσ, falsSub_refl]⟩
  obtain ⟨w, hwL, hmax⟩ := exists_max_of_mem (fcount S A) L w0 h0
  obtain ⟨hw, hwc⟩ := List.mem_filter.mp hwL
  simp only [Bool.and_eq_true] at hwc
  refine ⟨w, hw, hwc.2, maxFals_iff.mpr ⟨hwc.1, fun v hv hvσ hwv => ?_⟩⟩
  have hvL : v ∈ L := List.mem_filter.mpr ⟨hv, by simp [hvσ, falsSub_trans hwc.2 hwv]⟩
  exact falsSub_of_fcount_le hwv (hmax v hvL)

/-- Every innocently excludable alternative (computed list) is false at every `maxFals` world. -/
theorem holds_false_of_mem_ieList {S : Space} {σ : Claim} {A : List Claim} {a : Claim}
    {w : S.World} (ha : a ∈ ieList S σ A) (hw : w ∈ S.worlds) (hm : maxFals S σ A w = true) :
    S.holds w a = false :=
  ieB_iff.mp (mem_ieList_iff_ieB.mp ha).2 w hw hm

/-- `exh` holds at every `maxFals` world. -/
theorem holds_exh_of_maxFals {S : Space} {σ : Claim} {A : List Claim} {w : S.World}
    (hw : w ∈ S.worlds) (hm : maxFals S σ A w = true) : S.holds w (exh S A σ) = true := by
  rw [holds_exh, (maxFals_iff.mp hm).1, Bool.true_and, List.all_eq_true]
  intro a ha
  simp [holds_false_of_mem_ieList ha hw hm]

/-- `exh S A σ` entails `σ`. -/
theorem holds_of_holds_exh {S : Space} {σ : Claim} {A : List Claim} {w : S.World}
    (h : S.holds w (exh S A σ) = true) : S.holds w σ = true := by
  rw [holds_exh, Bool.and_eq_true] at h
  exact h.1

/-- At a world satisfying `exh S A σ`, every computed innocently excludable alternative fails. -/
theorem holds_false_of_holds_exh {S : Space} {σ : Claim} {A : List Claim} {w : S.World} {a : Claim}
    (h : S.holds w (exh S A σ) = true) (ha : a ∈ ieList S σ A) : S.holds w a = false := by
  rw [holds_exh, Bool.and_eq_true, List.all_eq_true] at h
  simpa using h.2 a ha

/-! ## Innocent exclusion: consistency, adequacy, comparison with naive exclusion -/

/-- Innocent exhaustification of a satisfiable prejacent is satisfiable. -/
theorem exh_sat_of_sat {S : Space} {A : List Claim} {σ : Claim} (hσ : Sat S [σ]) :
    Sat S [exh S A σ] := by
  obtain ⟨w0, hw0, h0⟩ := sat_singleton_iff.mp hσ
  obtain ⟨w, hw, _, hm⟩ := exists_maxFals_above S σ A hw0 h0
  exact sat_singleton_iff.mpr ⟨w, hw, holds_exh_of_maxFals hw hm⟩

/-- The computed list agrees with the textbook definition of innocent excludability. -/
theorem mem_ieList_iff_innocentlyExcludable_aux (S : Space) (σ : Claim) (A : List Claim)
    (a : Claim) : a ∈ ieList S σ A ↔ InnocentlyExcludable S σ A a := by
  constructor
  · intro ha
    obtain ⟨haA, hie⟩ := mem_ieList_iff_ieB.mp ha
    refine ⟨haA, fun X hX => ?_⟩
    obtain ⟨⟨hXA, w0, hw0, hσ0, hX0⟩, hmaxX⟩ := hX
    let L := S.worlds.filter fun v => S.holds v σ && X.all fun x => !S.holds v x
    have h0 : w0 ∈ L := by
      refine List.mem_filter.mpr ⟨hw0, ?_⟩
      simp only [Bool.and_eq_true, List.all_eq_true]
      exact ⟨hσ0, fun x hx => by simp [hX0 x hx]⟩
    obtain ⟨w, hwL, hmax⟩ := exists_max_of_mem (fcount S A) L w0 h0
    obtain ⟨hw, hwc⟩ := List.mem_filter.mp hwL
    simp only [Bool.and_eq_true, List.all_eq_true] at hwc
    have hXw : ∀ x ∈ X, S.holds w x = false := fun x hx => by simpa using hwc.2 x hx
    have hmf : maxFals S σ A w = true := by
      refine maxFals_iff.mpr ⟨hwc.1, fun v hv hvσ hwv => ?_⟩
      have hvL : v ∈ L := by
        refine List.mem_filter.mpr ⟨hv, ?_⟩
        simp only [Bool.and_eq_true, List.all_eq_true]
        exact ⟨hvσ, fun x hx => by simp [falsSub_iff.mp hwv x (hXA x hx) (hXw x hx)]⟩
      exact falsSub_of_fcount_le hwv (hmax v hvL)
    have haw : S.holds w a = false := ieB_iff.mp hie w hw hmf
    have hY : ConsistentExclusion S σ A (A.filter fun b => !S.holds w b) :=
      ⟨fun b hb => (List.mem_filter.mp hb).1, w, hw, hwc.1,
        fun b hb => by simpa using (List.mem_filter.mp hb).2⟩
    have hXY : ∀ x ∈ X, x ∈ A.filter fun b => !S.holds w b :=
      fun x hx => List.mem_filter.mpr ⟨hXA x hx, by simp [hXw x hx]⟩
    exact hmaxX _ hY hXY a (List.mem_filter.mpr ⟨haA, by simp [haw]⟩)
  · rintro ⟨haA, hall⟩
    refine mem_ieList_iff_ieB.mpr ⟨haA, ieB_iff.mpr fun w hw hm => ?_⟩
    have hX : MaximalExclusion S σ A (A.filter fun b => !S.holds w b) := by
      refine ⟨⟨fun b hb => (List.mem_filter.mp hb).1, w, hw, (maxFals_iff.mp hm).1,
        fun b hb => by simpa using (List.mem_filter.mp hb).2⟩, ?_⟩
      rintro Y ⟨hYA, v, hv, hvσ, hYv⟩ hXY b hb
      have hwv : falsSub S A w v = true := falsSub_iff.mpr fun c hc hwc =>
        hYv c (hXY c (List.mem_filter.mpr ⟨hc, by simp [hwc]⟩))
      have hvw := (maxFals_iff.mp hm).2 v hv hvσ hwv
      exact List.mem_filter.mpr ⟨hYA b hb, by simp [falsSub_iff.mp hvw b (hYA b hb) (hYv b hb)]⟩
    simpa using (List.mem_filter.mp (hall _ hX)).2

/-- Naive exhaustification entails innocent exhaustification. -/
theorem naiveExh_entails_exh (S : Space) (A : List Claim) (σ : Claim) :
    Entails S [naiveExh S A σ] (exh S A σ) := by
  intro w hw hE
  have hn : S.holds w (naiveExh S A σ) = true := hE _ (by simp)
  rw [holds_naiveExh, Bool.and_eq_true, List.all_eq_true] at hn
  rw [holds_exh, hn.1, Bool.true_and, List.all_eq_true]
  intro a ha
  obtain ⟨haA, hie⟩ := mem_ieList_iff_ieB.mp ha
  cases hent : entailsB S [σ] a
  · exact hn.2 a (List.mem_filter.mpr ⟨haA, by simp [hent]⟩)
  · exfalso
    obtain ⟨w', hw', _, hm⟩ := exists_maxFals_above S σ A hw hn.1
    have h1 := ieB_iff.mp hie w' hw' hm
    have h2 := (entailsB_iff.mp hent) w' hw' (by simp [(maxFals_iff.mp hm).1])
    rw [h1] at h2
    cases h2

/-- For a satisfiable prejacent, innocent and naive exhaustification are equivalent iff the
naive one is satisfiable. -/
theorem exh_equiv_naiveExh_iff_sat (S : Space) (A : List Claim) (σ : Claim) (hσ : Sat S [σ]) :
    Equiv S (exh S A σ) (naiveExh S A σ) ↔ Sat S [naiveExh S A σ] := by
  constructor
  · rintro ⟨h1, _⟩
    obtain ⟨w, hw, hwE⟩ := sat_singleton_iff.mp (exh_sat_of_sat (A := A) hσ)
    exact sat_singleton_iff.mpr ⟨w, hw, h1 w hw (by simp [hwE])⟩
  · intro h0
    obtain ⟨w0, hw0, hn0⟩ := sat_singleton_iff.mp h0
    rw [holds_naiveExh, Bool.and_eq_true, List.all_eq_true] at hn0
    have hsub : ∀ a ∈ naiveExcl S σ A, a ∈ ieList S σ A := by
      intro a ha
      obtain ⟨haA, _⟩ := List.mem_filter.mp ha
      refine mem_ieList_iff_ieB.mpr ⟨haA, ieB_iff.mpr fun w hw hm => ?_⟩
      have hww0 : falsSub S A w w0 = true := by
        refine falsSub_iff.mpr fun b hb hwb => ?_
        cases hent : entailsB S [σ] b
        · simpa using hn0.2 b (List.mem_filter.mpr ⟨hb, by simp [hent]⟩)
        · have := (entailsB_iff.mp hent) w hw (by simp [(maxFals_iff.mp hm).1])
          rw [hwb] at this
          cases this
      have hw0w := (maxFals_iff.mp hm).2 w0 hw0 hn0.1 hww0
      exact falsSub_iff.mp hw0w a haA (by simpa using hn0.2 a ha)
    refine ⟨?_, naiveExh_entails_exh S A σ⟩
    intro w hw hE
    have he : S.holds w (exh S A σ) = true := hE _ (by simp)
    rw [holds_naiveExh, holds_of_holds_exh he, Bool.true_and, List.all_eq_true]
    intro a ha
    simp [holds_false_of_holds_exh he (hsub a ha)]

/-- For an unsatisfiable prejacent every alternative is in the computed list. -/
theorem ieList_eq_self_of_not_sat {S : Space} {σ : Claim} (A : List Claim) (hσ : ¬ Sat S [σ]) :
    ieList S σ A = A := by
  unfold ieList
  apply List.filter_eq_self.mpr
  intro a _
  refine ieB_iff.mpr fun w hw hm => absurd (sat_singleton_iff.mpr ⟨w, hw, (maxFals_iff.mp hm).1⟩) hσ

/-- For an unsatisfiable prejacent every alternative is innocently excludable (no consistent
exclusion exists, so no maximal one does). -/
theorem innocentlyExcludable_of_not_sat {S : Space} {σ : Claim} {A : List Claim} {a : Claim}
    (hσ : ¬ Sat S [σ]) (ha : a ∈ A) : InnocentlyExcludable S σ A a :=
  ⟨ha, fun _ ⟨⟨_, w, hw, hwσ, _⟩, _⟩ => absurd (sat_singleton_iff.mpr ⟨w, hw, hwσ⟩) hσ⟩

/-! ## Readings and blockers -/

theorem mem_readings_iff {S : Space} {alt : Claim → List Claim} {F : List Rule} {σ ρ : Claim} :
    ρ ∈ readings S alt F σ ↔ ρ = σ ∨ ∃ r, r ∉ F ∧ ρ ∈ ruleReadings S alt r σ := by
  simp only [readings, List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (h | ⟨r, ⟨_, hr⟩, hρ⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, hr, hρ⟩
  · rintro (h | ⟨r, hr, hρ⟩)
    · exact Or.inl h
    · exact Or.inr ⟨r, ⟨by cases r <;> decide, hr⟩, hρ⟩

theorem mem_blockers_iff {S : Space} {alt : Claim → List Claim} {E : List Claim} {σ : Claim}
    {r : Rule} : r ∈ blockers S alt E σ ↔ ∃ ρ ∈ ruleReadings S alt r σ, ¬ Entails S E ρ := by
  simp only [blockers, List.mem_filter, List.any_eq_true, Bool.not_eq_true']
  constructor
  · rintro ⟨_, ρ, hρ, hn⟩
    exact ⟨ρ, hρ, fun h => by rw [entailsB_iff.mpr h] at hn; cases hn⟩
  · rintro ⟨ρ, hρ, hn⟩
    refine ⟨by cases r <;> decide, ρ, hρ, ?_⟩
    cases hb : entailsB S E ρ
    · rfl
    · exact absurd (entailsB_iff.mp hb) hn

theorem blockers_sound_aux (S : Space) (alt : Claim → List Claim) (E : List Claim) (σ : Claim)
    (hlit : LiterallySafe S E σ) : StrengtheningSafe S alt (blockers S alt E σ) E σ := by
  intro ρ hρ
  rcases mem_readings_iff.mp hρ with rfl | ⟨r, hr, hρr⟩
  · exact hlit
  · exact Classical.byContradiction fun hn => hr (mem_blockers_iff.mpr ⟨ρ, hρr, hn⟩)

theorem blockers_subset_aux (S : Space) (alt : Claim → List Claim) (E : List Claim) (σ : Claim)
    (F : List Rule) (hsafe : StrengtheningSafe S alt F E σ) : ∀ r ∈ blockers S alt E σ, r ∈ F := by
  intro r hr
  obtain ⟨ρ, hρ, hn⟩ := mem_blockers_iff.mp hr
  exact Classical.byContradiction fun hrF => hn (hsafe ρ (mem_readings_iff.mpr (Or.inr ⟨r, hrF, hρ⟩)))

theorem strengtheningSafe_iff_aux (S : Space) (alt : Claim → List Claim) (E : List Claim)
    (σ : Claim) (F : List Rule) (hlit : LiterallySafe S E σ) :
    StrengtheningSafe S alt F E σ ↔ ∀ r ∈ blockers S alt E σ, r ∈ F := by
  refine ⟨blockers_subset_aux S alt E σ F, fun hsub ρ hρ => ?_⟩
  apply blockers_sound_aux S alt E σ hlit ρ
  rcases mem_readings_iff.mp hρ with h | ⟨r, hr, hρr⟩
  · exact mem_readings_iff.mpr (Or.inl h)
  · exact mem_readings_iff.mpr (Or.inr ⟨r, mt (hsub r) hr, hρr⟩)

/-- The literal reading is always drawn, so strengthening safety implies literal safety. -/
theorem literallySafe_of_strengtheningSafe {S : Space} {alt : Claim → List Claim} {F : List Rule}
    {E : List Claim} {σ : Claim} (h : StrengtheningSafe S alt F E σ) : LiterallySafe S E σ :=
  h σ (mem_readings_iff.mpr (Or.inl rfl))

/-- With every rule flagged, the composing reader draws only the literal reading. -/
theorem strengtheningSafeStar_allRules_of_literallySafe {S : Space} {alt : Claim → List Claim}
    {E : List Claim} {σ : Claim} (hlit : LiterallySafe S E σ) :
    StrengtheningSafeStar S alt allRules E σ := by
  intro ρ hρ
  have hfil : (allRules.filter fun r => decide (r ∉ allRules)) = [] := by decide
  simp only [readingsStar, hfil, composeReadings, List.mem_cons, List.mem_filter,
    List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | ⟨rfl, _⟩ <;> exact hlit

/-! ## Normal forms -/

theorem evalAt_conjList (S : Space) (w : S.World) (y : Nat) :
    ∀ cs : List Claim, S.evalAt w y (conjList cs) = cs.all (S.evalAt w y)
  | [] => rfl
  | [c] => by simp [conjList]
  | c :: d :: cs => by
      have ih := evalAt_conjList S w y (d :: cs)
      show (S.evalAt w y c && S.evalAt w y (conjList (d :: cs))) = _
      rw [ih]
      rfl

theorem holds_nf (S : Space) (w : S.World) (H : Claim) (Cs : List Claim) :
    S.holds w (nf H Cs) = Cs.all fun c => S.holds w (.all (.rel H c)) := by
  unfold nf
  rw [holds_conjList, List.all_map]
  rfl

theorem holds_renderComp (S : Space) (w : S.World) (comp : List (Claim × List Claim)) :
    S.holds w (renderComp comp) = comp.all fun p => S.holds w (nfOf p) := by
  unfold renderComp
  rw [holds_conjList, List.all_map]
  rfl

theorem nf_conclusion_drop (S : Space) (E : List Claim) (H : Claim) (Cs Cs' : List Claim)
    (hE : LiterallySafe S E (nf H Cs)) (hsub : ∀ c ∈ Cs', c ∈ Cs) :
    LiterallySafe S E (nf H Cs') := by
  intro w hw hEw
  have h := hE w hw hEw
  rw [holds_nf, List.all_eq_true] at h ⊢
  exact fun c hc => h c (hsub c hc)

theorem renderComp_literallySafe_of_conclusionDropping (S : Space) (E : List Claim)
    (R comp : List (Claim × List Claim)) (hR : ∀ q ∈ R, LiterallySafe S E (nfOf q))
    (hcomp : ConclusionDropping R comp) : LiterallySafe S E (renderComp comp) := by
  intro w hw hEw
  rw [holds_renderComp, List.all_eq_true]
  intro p hp
  obtain ⟨q, hq, hEq, hSub⟩ := hcomp p hp
  have hqSafe : LiterallySafe S E (nf p.1 q.2) := hEq ▸ hR q hq
  exact nf_conclusion_drop S E p.1 q.2 p.2 hqSafe hSub w hw hEw

theorem holds_rel_all (S : Space) (w : S.World) (H c : Claim) :
    S.holds w (.all (.rel H c)) = S.params.all fun y => !S.evalAt w y H || S.evalAt w y c := rfl

/-! ## Universal conditionals under the standard alternatives -/

theorem stdAlt_forall_imp (S : Space) (a b : Claim) :
    stdAlt S (.all (.imp a b)) = [.all (.imp b a), .all (.iff a b)] := rfl

theorem step_perfection_forall_imp (S : Space) (alt : Claim → List Claim) (a b : Claim) :
    step S alt .perfection (.all (.imp a b)) = [.all (.iff a b)] := rfl

theorem step_qualifierDrop_forall_imp (S : Space) (alt : Claim → List Claim) (a b : Claim) :
    step S alt .qualifierDrop (.all (.imp a b)) = [] := rfl

theorem step_exhaustification_eq (S : Space) (alt : Claim → List Claim) (σ : Claim) :
    step S alt .exhaustification σ = [exh S (alt σ) σ] := rfl

theorem holds_conv_of_holds_iff {S : Space} {w : S.World} {a b : Claim}
    (h : S.holds w (.all (.iff a b)) = true) : S.holds w (.all (.imp b a)) = true := by
  rw [holds_all_eq, List.all_eq_true] at h ⊢
  intro y hy
  have := h y hy
  simp only [Space.evalAt] at this ⊢
  cases ha : S.evalAt w y a <;> cases hb : S.evalAt w y b <;> simp_all

theorem holds_iff_of_holds_imp_conv {S : Space} {w : S.World} {a b : Claim}
    (h1 : S.holds w (.all (.imp a b)) = true) (h2 : S.holds w (.all (.imp b a)) = true) :
    S.holds w (.all (.iff a b)) = true := by
  rw [holds_all_eq, List.all_eq_true] at h1 h2 ⊢
  intro y hy
  have e1 := h1 y hy
  have e2 := h2 y hy
  simp only [Space.evalAt] at e1 e2 ⊢
  cases ha : S.evalAt w y a <;> cases hb : S.evalAt w y b <;> simp_all

/-- If `∀x, a → b` is consistent with the failure of its converse, the converse is in the
computed innocent-exclusion list of the standard alternatives. -/
theorem conv_mem_ieList_of_converseExcludable {S : Space} {a b : Claim}
    (hconv : ConverseExcludable S a b) :
    Claim.all (.imp b a) ∈ ieList S (.all (.imp a b)) (stdAlt S (.all (.imp a b))) := by
  obtain ⟨v, hv, hvσ, hvc⟩ := sat_pair_iff.mp hconv
  rw [holds_not_eq, Bool.not_eq_true'] at hvc
  have hvi : S.holds v (.all (.iff a b)) = false := by
    cases h : S.holds v (.all (.iff a b))
    · rfl
    · rw [holds_conv_of_holds_iff h] at hvc; cases hvc
  rw [stdAlt_forall_imp]
  refine mem_ieList_iff_ieB.mpr ⟨by simp, ieB_iff.mpr fun w hw hm => ?_⟩
  have hwv : falsSub S [.all (.imp b a), .all (.iff a b)] w v = true := by
    refine falsSub_iff.mpr fun c hc _ => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact hvc
    · exact hvi
  have hvw := (maxFals_iff.mp hm).2 v hv hvσ hwv
  exact falsSub_iff.mp hvw _ (by simp) hvc

/-- Under the standard alternatives, the converse of `∀x, a → b` is innocently excludable or
entailed by `∀x, a → b`. -/
theorem conv_mem_ieList_or_entailed (S : Space) (a b : Claim) :
    Claim.all (.imp b a) ∈ ieList S (.all (.imp a b)) (stdAlt S (.all (.imp a b))) ∨
      Entails S [.all (.imp a b)] (.all (.imp b a)) := by
  by_cases hconv : ConverseExcludable S a b
  · exact Or.inl (conv_mem_ieList_of_converseExcludable hconv)
  · refine Or.inr (entails_singleton_iff.mpr fun w hw hσ => ?_)
    cases h : S.holds w (.all (.imp b a))
    · exact absurd (sat_pair_iff.mpr ⟨w, hw, hσ, by simp [holds_not_eq, h]⟩) hconv
    · rfl

set_option linter.unusedSimpArgs false in
/-- The computed blocker set of `∀x, a → b` under the standard alternatives, unfolded:
qualifier dropping never applies; perfection is a blocker iff its reading `∀x, a ↔ b` survives
cancellation and is not entailed; exhaustification is a blocker iff its reading survives
cancellation and is not entailed. -/
theorem blockers_forall_imp (S : Space) (E : List Claim) (a b : Claim) :
    blockers S (stdAlt S) E (.all (.imp a b)) =
      (if (satB S [.all (.imp a b), .all (.iff a b)] &&
          !entailsB S E (.all (.iff a b))) = true then [Rule.perfection] else []) ++
      (if (satB S [.all (.imp a b), exh S (stdAlt S (.all (.imp a b))) (.all (.imp a b))] &&
          !entailsB S E (exh S (stdAlt S (.all (.imp a b))) (.all (.imp a b)))) = true
        then [Rule.exhaustification] else []) := by
  unfold blockers allRules ruleReadings
  simp only [List.filter_cons, List.filter_nil, step_perfection_forall_imp,
    step_qualifierDrop_forall_imp, step_exhaustification_eq]
  cases h1 : satB S [.all (.imp a b), .all (.iff a b)] <;>
    cases h2 : entailsB S E (.all (.iff a b)) <;>
    cases h3 : satB S [.all (.imp a b), exh S (stdAlt S (.all (.imp a b))) (.all (.imp a b))] <;>
    cases h4 : entailsB S E (exh S (stdAlt S (.all (.imp a b))) (.all (.imp a b))) <;>
    simp [List.filter, h1, h2, h3, h4]

/-! ## Single-world spaces -/

theorem interp_never_open (ps : List Nat) (val : Nat → Nat → Bool) (E : List Claim) (c : Claim) :
    ¬ Open (Space.interp ps val) E c := by
  intro ⟨h1, h2⟩
  cases hc : (Space.interp ps val).holds () c
  · apply h2
    intro w hw _
    cases hw with
    | head => simp only [Space.holds, Space.evalAt, Bool.not_eq_true']; exact hc
    | tail _ hnil => cases hnil
  · apply h1
    intro w hw _
    cases hw with
    | head => exact hc
    | tail _ hnil => cases hnil

theorem interp_literallySafe_strengtheningSafe_unblocked (ps : List Nat)
    (val : Nat → Nat → Bool) (alt : Claim → List Claim) (E : List Claim) (σ : Claim)
    (hlit : LiterallySafe (Space.interp ps val) E σ) :
    StrengtheningSafe (Space.interp ps val) alt [] E σ := by
  intro ρ hρ w hw hE
  cases hw with
  | tail _ hnil => cases hnil
  | head =>
    rcases mem_readings_iff.mp hρ with rfl | ⟨r, _, hρr⟩
    · exact hlit () (List.mem_singleton.mpr rfl) hE
    · obtain ⟨_, hs⟩ := List.mem_filter.mp hρr
      obtain ⟨u, hu, hhold⟩ := sat_pair_iff.mp (satB_iff.mp hs)
      cases hu with
      | head => exact hhold.2
      | tail _ hnil => cases hnil

/-! ## Blocker sets of a universal conditional, by what the report says about the converse -/

private theorem satB_perf {S : Space} {a b : Claim} (hperf : PerfectionConsistent S a b) :
    satB S [.all (.imp a b), .all (.iff a b)] = true :=
  satB_iff.mpr hperf

private theorem satB_exh_forall_imp {S : Space} {a b : Claim}
    (hσ : Sat S [.all (.imp a b)]) :
    satB S [.all (.imp a b), exh S (stdAlt S (.all (.imp a b))) (.all (.imp a b))] = true := by
  obtain ⟨w, hw, hwx⟩ :=
    sat_singleton_iff.mp (exh_sat_of_sat (A := stdAlt S (.all (.imp a b))) hσ)
  exact satB_iff.mpr (sat_pair_iff.mpr ⟨w, hw, holds_of_holds_exh hwx, hwx⟩)

private theorem sat_of_perf {S : Space} {a b : Claim} (hperf : PerfectionConsistent S a b) :
    Sat S [.all (.imp a b)] := by
  obtain ⟨w, hw, h1, _⟩ := sat_pair_iff.mp hperf
  exact sat_singleton_iff.mpr ⟨w, hw, h1⟩

private theorem entailsB_iff_false_of_not_conv {S : Space} {E : List Claim} {a b : Claim}
    (h : ¬ Entails S E (.all (.imp b a))) : entailsB S E (.all (.iff a b)) = false := by
  cases hb : entailsB S E (.all (.iff a b))
  · rfl
  · exact absurd (fun w hw hEw => holds_conv_of_holds_iff (entailsB_iff.mp hb w hw hEw)) h

theorem forall_conditional_blockers_aux (S : Space) (E : List Claim) (a b : Claim)
    (hE : Sat S E) (hlit : LiterallySafe S E (.all (.imp a b)))
    (hperf : PerfectionConsistent S a b) (hconv : ConverseExcludable S a b) :
    blockers S (stdAlt S) E (.all (.imp a b)) =
      if Entails S E (.not (.all (.imp b a))) then [.perfection]
      else if Entails S E (.all (.imp b a)) then [.exhaustification]
      else [.perfection, .exhaustification] := by
  have hP := satB_perf hperf
  have hX := satB_exh_forall_imp (sat_of_perf hperf)
  have hmem := conv_mem_ieList_of_converseExcludable hconv
  rw [blockers_forall_imp]
  by_cases hr : Entails S E (.not (.all (.imp b a)))
  · simp only [hr, ↓reduceIte]
    have hi : entailsB S E (.all (.iff a b)) = false :=
      entailsB_iff_false_of_not_conv fun hc => not_entails_and_not_of_sat hE hc hr
    have hx : entailsB S E (exh S (stdAlt S (.all (.imp a b))) (.all (.imp a b))) = true := by
      apply entailsB_iff.mpr
      intro w hw hEw
      have hσ := hlit w hw hEw
      have hc : S.holds w (.all (.imp b a)) = false := by
        have := hr w hw hEw
        rw [holds_not_eq] at this
        simpa using this
      have hi' : S.holds w (.all (.iff a b)) = false := by
        cases h : S.holds w (.all (.iff a b))
        · rfl
        · rw [holds_conv_of_holds_iff h] at hc; cases hc
      rw [holds_exh, hσ, Bool.true_and, List.all_eq_true]
      intro c hc'
      have hcA := (mem_ieList_iff_ieB.mp hc').1
      rw [stdAlt_forall_imp] at hcA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcA
      rcases hcA with rfl | rfl <;> simp [hc, hi']
    simp [hP, hi, hX, hx]
  · simp only [hr, ↓reduceIte]
    have hxf : entailsB S E (exh S (stdAlt S (.all (.imp a b))) (.all (.imp a b))) = false := by
      cases h : entailsB S E (exh S (stdAlt S (.all (.imp a b))) (.all (.imp a b)))
      · rfl
      · exfalso
        apply hr
        intro w hw hEw
        rw [holds_not_eq, holds_false_of_holds_exh (entailsB_iff.mp h w hw hEw) hmem]
        rfl
    by_cases hp : Entails S E (.all (.imp b a))
    · simp only [hp, ↓reduceIte]
      have hi : entailsB S E (.all (.iff a b)) = true :=
        entailsB_iff.mpr fun w hw hEw => holds_iff_of_holds_imp_conv (hlit w hw hEw) (hp w hw hEw)
      simp [hP, hi, hX, hxf]
    · simp only [hp, ↓reduceIte]
      simp [hP, entailsB_iff_false_of_not_conv hp, hX, hxf]

theorem forall_conditional_blockers_of_open_aux (S : Space) (E : List Claim) (a b : Claim)
    (hperf : PerfectionConsistent S a b) (hopen : Open S E (.all (.imp b a))) :
    blockers S (stdAlt S) E (.all (.imp a b)) = [.perfection, .exhaustification] := by
  have hP := satB_perf hperf
  have hX := satB_exh_forall_imp (sat_of_perf hperf)
  have hxf : entailsB S E (exh S (stdAlt S (.all (.imp a b))) (.all (.imp a b))) = false := by
    cases h : entailsB S E (exh S (stdAlt S (.all (.imp a b))) (.all (.imp a b)))
    · rfl
    · exfalso
      have hEX := entailsB_iff.mp h
      rcases conv_mem_ieList_or_entailed S a b with hmem | hent
      · apply hopen.2
        intro w hw hEw
        rw [holds_not_eq, holds_false_of_holds_exh (hEX w hw hEw) hmem]
        rfl
      · apply hopen.1
        intro w hw hEw
        exact entails_singleton_iff.mp hent w hw (holds_of_holds_exh (hEX w hw hEw))
  rw [blockers_forall_imp]
  simp [hP, entailsB_iff_false_of_not_conv hopen.1, hX, hxf]

theorem forall_conditional_unblocked_unsafe_aux (S : Space) (E : List Claim) (a b : Claim)
    (hE : Sat S E) (hperf : PerfectionConsistent S a b) (hconv : ConverseExcludable S a b) :
    ¬ StrengtheningSafe S (stdAlt S) [] E (.all (.imp a b)) := by
  intro hs
  have hsub := blockers_subset_aux _ _ _ _ _ hs
  rw [forall_conditional_blockers_aux S E a b hE (literallySafe_of_strengtheningSafe hs) hperf
    hconv] at hsub
  by_cases hr : Entails S E (.not (.all (.imp b a)))
  · simp only [hr, ↓reduceIte] at hsub
    exact absurd (hsub _ (List.mem_singleton_self _)) List.not_mem_nil
  · by_cases hp : Entails S E (.all (.imp b a))
    · simp only [hr, hp, ↓reduceIte] at hsub
      exact absurd (hsub _ (List.mem_singleton_self _)) List.not_mem_nil
    · simp only [hr, hp, ↓reduceIte] at hsub
      exact absurd (hsub _ List.mem_cons_self) List.not_mem_nil

theorem forall_conditional_open_converse_safe_iff_aux (S : Space) (E : List Claim) (a b : Claim)
    (F : List Rule) (hlit : LiterallySafe S E (.all (.imp a b)))
    (hperf : PerfectionConsistent S a b) (hopen : Open S E (.all (.imp b a))) :
    StrengtheningSafe S (stdAlt S) F E (.all (.imp a b)) ↔
      Rule.perfection ∈ F ∧ Rule.exhaustification ∈ F := by
  rw [strengtheningSafe_iff_aux _ _ _ _ _ hlit,
    forall_conditional_blockers_of_open_aux S E a b hperf hopen]
  simp

end Toy.Implicature
