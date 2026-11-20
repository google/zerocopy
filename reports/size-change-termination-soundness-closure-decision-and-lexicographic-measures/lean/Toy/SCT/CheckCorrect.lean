/-
Toy.SCT.CheckCorrect
====================

Correctness of the checker `checkSCT`. Soundness: a fixpoint of the closure iteration contains
the call-site graphs and is closed under composition, so it contains the whole closure.
Completeness: every list the iteration produces is duplicate-free and consists of closure graphs;
each iteration step that is not a fixpoint adds a new graph; and a duplicate-free list of graphs has at most
`nf * nf * 3 ^ (k * k)` elements, so the fuel `closureFuel nf k` suffices.
-/
import Toy.SCT.Check
import Toy.SCT.Enum

namespace Toy.SCT

variable {nf k : Nat}

theorem foldl_preserves {α β : Type} (f : α → β → α) (I : α → Prop) (Q : β → Prop)
    (hf : ∀ a x, I a → Q x → I (f a x)) :
    ∀ (xs : List β) (acc : α), I acc → (∀ x ∈ xs, Q x) → I (xs.foldl f acc)
  | [], _, h, _ => h
  | x :: xs, acc, h, hxs =>
    foldl_preserves f I Q hf xs (f acc x) (hf acc x h (hxs x (by simp)))
      (fun y hy => hxs y (by simp [hy]))

theorem mem_addNew_iff {α : Type} [DecidableEq α] (x y : α) (l : List α) :
    y ∈ addNew x l ↔ y ∈ l ∨ y = x := by
  unfold addNew
  split <;> simp_all [or_comm]

theorem addNew_nodup {α : Type} [DecidableEq α] (x : α) (l : List α) (h : l.Nodup) :
    (addNew x l).Nodup := by
  unfold addNew
  split
  · exact h
  · next hx =>
    rw [List.nodup_append]
    refine ⟨h, by simp, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb
    subst hb
    exact fun e => hx (e ▸ ha)

theorem addNew_extends {α : Type} [DecidableEq α] (x : α) (l : List α) :
    ∃ E, addNew x l = l ++ E := by
  unfold addNew
  split
  · exact ⟨[], by simp⟩
  · exact ⟨[x], rfl⟩

/-- The invariant of one iteration step of closure computation on `S`. -/
def StepInv (S acc : List (SCG nf k)) : Prop :=
  (∃ E, acc = S ++ E) ∧ acc.Nodup ∧
    ∀ X ∈ acc, X ∈ S ∨ ∃ G ∈ S, ∃ H ∈ S, G.dst = H.src ∧ X = G.comp H

theorem closureStep_inv (S : List (SCG nf k)) (hS : S.Nodup) : StepInv S (closureStep S) := by
  unfold closureStep
  refine foldl_preserves _ (StepInv S) (· ∈ S) ?_ S S
    ⟨⟨[], by simp⟩, hS, fun X hX => Or.inl hX⟩ (fun _ h => h)
  intro acc G hacc hG
  refine foldl_preserves _ (StepInv S) (· ∈ S) ?_ S acc hacc (fun _ h => h)
  intro acc' H hacc' hH
  split
  · next hdst =>
    obtain ⟨⟨E, hE⟩, hnd, hmem⟩ := hacc'
    obtain ⟨E', hE'⟩ := addNew_extends (G.comp H) acc'
    refine ⟨⟨E ++ E', by rw [hE', hE, List.append_assoc]⟩, addNew_nodup _ _ hnd, fun X hX => ?_⟩
    rcases (mem_addNew_iff _ _ _).mp hX with hX | rfl
    · exact hmem X hX
    · exact Or.inr ⟨G, hG, H, hH, hdst, rfl⟩
  · exact hacc'

theorem mem_closureStep_of_mem (S : List (SCG nf k)) (hS : S.Nodup) {X : SCG nf k}
    (hX : X ∈ S) : X ∈ closureStep S := by
  obtain ⟨⟨E, hE⟩, -, -⟩ := closureStep_inv S hS
  rw [hE]
  exact List.mem_append_left _ hX

/-- Every list the closure iteration produces from a duplicate-free list of closure graphs
consists of closure graphs; and the iteration succeeds once the fuel exceeds the number of graphs
that can still be added. -/
theorem closureIter_complete (P : Prog nf k) :
    ∀ (n : Nat) (S : List (SCG nf k)), S.Nodup → (∀ G ∈ S, InClosure P G) →
      (allSCG nf k).length < S.length + n →
      ∃ T, closureIter n S = some T ∧ ∀ G ∈ T, InClosure P G
  | 0, S, hnd, _, hlen => by
    have := List.Nodup.length_le_of_subset hnd (fun G _ => mem_allSCG G)
    omega
  | n + 1, S, hnd, hcl, hlen => by
    simp only [closureIter]
    split
    · exact ⟨S, rfl, hcl⟩
    · next hfix =>
      obtain ⟨⟨E, hE⟩, hnd', hmem⟩ := closureStep_inv S hnd
      have ⟨X, hX, hXS⟩ : ∃ X ∈ closureStep S, X ∉ S := by
        refine Classical.byContradiction fun hne => hfix ?_
        refine List.all_eq_true.mpr fun X hX => decide_eq_true ?_
        exact Classical.byContradiction fun hXS => hne ⟨X, hX, hXS⟩
      have hEne : E ≠ [] := by
        intro he
        rw [hE, he, List.append_nil] at hX
        exact hXS hX
      have hlen' : S.length < (closureStep S).length := by
        rw [hE, List.length_append]
        cases E with
        | nil => exact absurd rfl hEne
        | cons _ _ => simp
      refine closureIter_complete P n (closureStep S) hnd' (fun G hG => ?_) (by omega)
      rcases hmem G hG with h | ⟨G1, h1, H1, h2, hdst, rfl⟩
      · exact hcl G h
      · exact .comp (hcl G1 h1) (hcl H1 h2) hdst

theorem dedupGraphs_spec (l : List (SCG nf k)) :
    (dedupGraphs l).Nodup ∧ ∀ G ∈ dedupGraphs l, G ∈ l := by
  unfold dedupGraphs
  refine foldl_preserves _ (fun acc => acc.Nodup ∧ ∀ G ∈ acc, G ∈ l) (· ∈ l) ?_ l []
    ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩ (fun _ h => h)
  intro acc x ⟨hnd, hmem⟩ hx
  refine ⟨addNew_nodup _ _ hnd, fun G hG => ?_⟩
  rcases (mem_addNew_iff _ _ _).mp hG with h | rfl
  · exact hmem G h
  · exact hx

/-- **Completeness of the checker.** -/
theorem checkSCT_eq_true_of_closureCriterion_proof (P : Prog nf k) (h : ClosureCriterion P) :
    checkSCT P = true := by
  obtain ⟨hnd, hsub⟩ := dedupGraphs_spec P.calls
  obtain ⟨T, hT, hcl⟩ := closureIter_complete P (closureFuel nf k) (dedupGraphs P.calls) hnd
    (fun G hG => .gen (hsub G hG))
    (by rw [length_allSCG]; unfold closureFuel; omega)
  unfold checkSCT
  rw [hT]
  refine List.all_eq_true.mpr fun G hG => ?_
  unfold idemTest
  by_cases hc : G.src = G.dst ∧ G.comp G = G
  · have := h G (hcl G hG) hc.1 hc.2
    simp [this]
  · have : (decide (G.src = G.dst) && decide (G.comp G = G)) = false := by
      by_cases h1 : G.src = G.dst
      · have h2 : ¬ G.comp G = G := fun h2 => hc ⟨h1, h2⟩
        simp [h1, h2]
      · simp [h1]
    simp [this]

/-! ### Soundness of the checker -/

theorem closureStep_comp_mem (S : List (SCG nf k)) {G H : SCG nf k}
    (hG : G ∈ S) (hH : H ∈ S) (hdst : G.dst = H.src) : G.comp H ∈ closureStep S := by
  -- the inner fold for `G` adds `G.comp H`; later folds only append
  have keep : ∀ (T : List (SCG nf k)) (G' : SCG nf k) (acc : List (SCG nf k)) (X : SCG nf k),
      X ∈ acc →
        X ∈ T.foldl (fun acc' H' => if G'.dst = H'.src then addNew (G'.comp H') acc' else acc')
          acc := by
    intro T G' acc X hX
    refine foldl_preserves _ (fun a => X ∈ a) (fun _ => True) ?_ T acc hX (fun _ _ => trivial)
    intro a x ha _
    split
    · exact (mem_addNew_iff _ _ _).mpr (Or.inl ha)
    · exact ha
  have keepOuter : ∀ (T : List (SCG nf k)) (acc : List (SCG nf k)) (X : SCG nf k), X ∈ acc →
      X ∈ T.foldl (fun acc G' => S.foldl
        (fun acc' H' => if G'.dst = H'.src then addNew (G'.comp H') acc' else acc') acc) acc := by
    intro T acc X hX
    refine foldl_preserves _ (fun a => X ∈ a) (fun _ => True) ?_ T acc hX (fun _ _ => trivial)
    intro a G' ha _
    exact keep S G' a X ha
  have inner : ∀ (T : List (SCG nf k)) (acc : List (SCG nf k)), H ∈ T →
      G.comp H ∈ T.foldl (fun acc' H' => if G.dst = H'.src then addNew (G.comp H') acc' else acc')
        acc := by
    intro T
    induction T with
    | nil => intro _ h; exact absurd h List.not_mem_nil
    | cons H' T ih =>
      intro acc hT
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hT with rfl | hT
      · apply keep
        rw [ite_eq_left hdst]
        exact (mem_addNew_iff _ _ _).mpr (Or.inr rfl)
      · exact ih _ hT
  have outer : ∀ (T : List (SCG nf k)) (acc : List (SCG nf k)), G ∈ T →
      G.comp H ∈ T.foldl (fun acc G' => S.foldl
        (fun acc' H' => if G'.dst = H'.src then addNew (G'.comp H') acc' else acc') acc) acc := by
    intro T
    induction T with
    | nil => intro _ h; exact absurd h List.not_mem_nil
    | cons G' T ih =>
      intro acc hT
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hT with rfl | hT
      · exact keepOuter T _ _ (inner S acc hH)
      · exact ih _ hT
  exact outer S S hG

theorem closureStep_sub (S : List (SCG nf k)) {X : SCG nf k} (hX : X ∈ S) :
    X ∈ closureStep S := by
  unfold closureStep
  refine foldl_preserves _ (fun a => X ∈ a) (fun _ => True) ?_ S S hX (fun _ _ => trivial)
  intro a G ha _
  refine foldl_preserves _ (fun a => X ∈ a) (fun _ => True) ?_ S a ha (fun _ _ => trivial)
  intro a' H ha' _
  split
  · exact (mem_addNew_iff _ _ _).mpr (Or.inl ha')
  · exact ha'

theorem closureIter_some_spec :
    ∀ (fuel : Nat) (S0 S : List (SCG nf k)), closureIter fuel S0 = some S →
      (∀ G ∈ S0, G ∈ S) ∧ (∀ G ∈ S, ∀ H ∈ S, G.dst = H.src → G.comp H ∈ S)
  | 0, _, _, h => by simp [closureIter] at h
  | n + 1, S0, S, h => by
    simp only [closureIter] at h
    split at h
    · next hfix =>
      cases h
      refine ⟨fun _ hG => hG, fun G hG H hH hdst => ?_⟩
      have hmem := closureStep_comp_mem S0 hG hH hdst
      exact of_decide_eq_true (List.all_eq_true.mp hfix (G.comp H) hmem)
    · obtain ⟨hsub, hcl⟩ := closureIter_some_spec n (closureStep S0) S h
      exact ⟨fun G hG => hsub G (closureStep_sub S0 hG), hcl⟩

/-- **Soundness of the checker.** -/
theorem closureCriterion_of_checkSCT_eq_true_proof (P : Prog nf k) (h : checkSCT P = true) :
    ClosureCriterion P := by
  unfold checkSCT at h
  cases hiter : closureIter (closureFuel nf k) (dedupGraphs P.calls) with
  | none => simp [hiter] at h
  | some S =>
    simp only [hiter] at h
    obtain ⟨hsub, hcl⟩ := closureIter_some_spec _ _ _ hiter
    have hgen : ∀ G ∈ P.calls, G ∈ S := by
      intro G hG
      refine hsub G ?_
      unfold dedupGraphs
      have : ∀ (l acc : List (SCG nf k)), G ∈ l ∨ G ∈ acc → G ∈ l.foldl (fun a x => addNew x a) acc := by
        intro l
        induction l with
        | nil => intro acc h; rcases h with h | h; exact absurd h List.not_mem_nil; exact h
        | cons x xs ih =>
          intro acc h
          apply ih
          rcases h with h | h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr ((mem_addNew_iff _ _ _).mpr (Or.inr rfl))
            · exact Or.inl h
          · exact Or.inr ((mem_addNew_iff _ _ _).mpr (Or.inl h))
      exact this _ _ (Or.inl hG)
    refine criterionWith_of_closed S hgen hcl ?_
    intro G hG hloop hidem
    have htest := List.all_eq_true.mp h G hG
    unfold idemTest at htest
    have hidem' : G.comp G = G := hidem
    simp [hloop, hidem'] at htest
    exact htest

end Toy.SCT
