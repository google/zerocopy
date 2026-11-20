import Toy.Sep.NonLocal
import Toy.Sep.Precision
import Toy.Sep.HeapLocal
import Toy.Sep.Frame
import Toy.Sep.FrameQuantified

/-!
# Definition examples (all proved)

For every core definition: at least one intended positive instance and at least
one intended negative instance. Every command is additionally illustrated by at
least one admitted transition `c h o` and at least one excluded transition
`¬ c h o` (except `diverge`, which by definition admits no transition).
-/

namespace Toy.Sep

open SepStruct

/-! ## Algebraic laws -/

/-- A separation structure on `Nat` with asymmetric disjointness `a < b`. -/
@[reducible] def ltSepStruct : SepStruct Nat := ⟨fun a b => a < b, fun a b => a + b⟩

/-- A separation structure on `Nat` whose union is the left projection. -/
@[reducible] def leftProjSepStruct : SepStruct Nat := ⟨fun _ _ => True, fun a _ => a⟩

/-- A separation structure on `Nat` whose union is truncated subtraction. -/
@[reducible] def subSepStruct : SepStruct Nat := ⟨fun _ _ => True, fun a b => a - b⟩

example : DisjSymm (Heap Nat) := heap_disjSymm Nat

theorem ltSepStruct_not_disjSymm : ¬ @DisjSymm Nat ltSepStruct := by
  intro h
  have h01 := h 0 1 (show (0 : Nat) < 1 by decide)
  exact (show ¬ (1 : Nat) < 0 by decide) h01

example : UnionComm (Heap Nat) := heap_unionComm Nat

theorem leftProjSepStruct_not_unionComm : ¬ @UnionComm Nat leftProjSepStruct := by
  intro h
  have h01 : (0 : Nat) = 1 := h 0 1 trivial
  cases h01

example : UnionAssoc (Heap Nat) := heap_unionAssoc Nat

theorem subSepStruct_not_unionAssoc : ¬ @UnionAssoc Nat subSepStruct := by
  intro h
  have h111 : (1 - 1 - 1 : Nat) = 1 - (1 - 1) := (h 1 1 1 trivial trivial).2.2
  cases h111

example : UnitLaw (Heap.emp : Heap Nat) := heap_unitLaw Nat

theorem pt_not_unitLaw : ¬ UnitLaw (Heap.pt 0 1 : Heap Nat) := by
  intro h
  rcases (h (Heap.pt 0 1)).1 0 with h1 | h1 <;> simp at h1

example : RightCancel (Heap Nat) := heap_rightCancel Nat
example : ¬ RightCancel OrAlg := orAlg_not_rightCancel
example : LeftCancel (Heap Nat) := heap_leftCancel Nat
example : ¬ LeftCancel Fork := fork_not_leftCancel

example : IsSepAlgebra (Heap Nat) Heap.emp := heap_isSepAlgebra Nat
example : IsSepAlgebra OrAlg OrAlg.unit := orAlg_isSepAlgebra
example : IsSepAlgebra Fork Fork.e := fork_isSepAlgebra

theorem leftProjSepStruct_not_isSepAlgebra : ¬ @IsSepAlgebra Nat leftProjSepStruct 0 :=
  fun h => leftProjSepStruct_not_unionComm (@IsSepAlgebra.comm Nat leftProjSepStruct 0 h)

/-! ## Heaps -/

/-- The everywhere-allocated map is not a finite heap. -/
theorem everywhere_allocated_not_finite :
    ¬ ∃ n, ∀ k, n ≤ k → (fun _ => some 0 : Nat → Option Nat) k = none := by
  rintro ⟨n, hn⟩
  cases hn n (Nat.le_refl n)

example : (Heap.pt 3 4 : Heap Nat).val 3 = some 4 := by simp

example : disj (Heap.pt 0 1 : Heap Nat) (Heap.pt 1 2) := pt01_disj_pt12

theorem pt0_not_disj_pt0 : ¬ disj (Heap.pt 0 1 : Heap Nat) (Heap.pt 0 2) := by
  intro h
  rcases h 0 with h1 | h1 <;> simp at h1

example : (union (Heap.pt 0 1 : Heap Nat) (Heap.pt 1 2)).val 1 = some 2 := by simp

/-- Union of overlapping heaps is left-biased and not commutative: it is only
meaningful on disjoint arguments. -/
theorem union_overlapping_not_comm :
    union (Heap.pt 0 1 : Heap Nat) (Heap.pt 0 2) ≠ union (Heap.pt 0 2) (Heap.pt 0 1) := by
  intro h
  have := congrArg (fun x : Heap Nat => x.val 0) h
  simp at this

/-! ## Separating conjunction -/

example : sep (sing (Heap.pt 0 1)) (sing (Heap.pt 1 2))
    (union (Heap.pt 0 1 : Heap Nat) (Heap.pt 1 2)) :=
  ⟨_, _, pt01_disj_pt12, rfl, rfl, rfl⟩

/-- Overlapping cells cannot be separated: `(0 ↦ 1) * (0 ↦ 2)` is unsatisfiable. -/
theorem sep_overlap_unsat (h : Heap Nat) :
    ¬ sep (sing (Heap.pt 0 1)) (sing (Heap.pt 0 2)) h := by
  rintro ⟨a, b, hd, _, ha, hb⟩
  have ha : a = Heap.pt 0 1 := ha
  have hb : b = Heap.pt 0 2 := hb
  subst ha; subst hb
  exact pt0_not_disj_pt0 hd

/-! ## Safety, strongest postconditions, triples -/

example : Safe (mutate 0 (5 : Nat)) (Heap.pt 0 1) :=
  (safe_mutate_iff _ _ _).2 (by simp)

theorem mutate_not_safe_emp : ¬ Safe (mutate 0 (5 : Nat)) Heap.emp := by
  rw [safe_mutate_iff]; simp

theorem mutate_pt_eq : (Heap.pt 0 1 : Heap Nat).set 0 (some 5) = Heap.pt 0 5 := by
  apply Heap.ext; intro j; by_cases hj : j = 0 <;> simp [hj]

example : post (mutate 0 (5 : Nat)) (Heap.pt 0 1) (Heap.pt 0 5) :=
  Or.inr ⟨by simp, by rw [mutate_pt_eq]⟩

theorem post_mutate_excludes_old : ¬ post (mutate 0 (5 : Nat)) (Heap.pt 0 1) (Heap.pt 0 1) := by
  rintro (⟨_, hf⟩ | ⟨_, he⟩)
  · cases hf
  · injection he with he
    rw [mutate_pt_eq] at he
    have := congrArg (fun x : Heap Nat => x.val 0) he
    simp at this

/-- Small axiom for mutation: `{0 ↦ 1} [0] := 5 {0 ↦ 5}`. -/
theorem triple_mutate : Triple (sing (Heap.pt 0 1)) (mutate 0 (5 : Nat)) (sing (Heap.pt 0 5)) := by
  intro h hh
  have hh : h = Heap.pt 0 1 := hh
  subst hh
  refine ⟨(safe_mutate_iff _ _ _).2 (by simp), ?_⟩
  rintro h' (⟨_, hf⟩ | ⟨_, he⟩)
  · cases hf
  · injection he with he
    rw [he, mutate_pt_eq]
    rfl

/-- Fault avoidance: `{emp} [0] := 5 {true}` does not hold. -/
theorem not_triple_mutate_emp :
    ¬ Triple (sing Heap.emp) (mutate 0 (5 : Nat)) (fun _ => True) := by
  intro ht
  exact mutate_not_safe_emp (ht Heap.emp rfl).1

/-- Partial correctness: a diverging command satisfies every triple. -/
theorem triple_diverge {S : Type _} (P Q : Assn S) : Triple P (diverge : Cmd S) Q :=
  fun _ _ => ⟨fun hf => hf, fun _ hf => hf.elim⟩

/-- Small axiom for deallocation: `{0 ↦ 1} free 0 {emp}`. -/
theorem triple_free : Triple (sing (Heap.pt 0 1)) (free (V := Nat) 0) (sing Heap.emp) := by
  intro h hh
  have hh : h = Heap.pt 0 1 := hh
  subst hh
  refine ⟨?_, ?_⟩
  · rintro (⟨h1, _⟩ | ⟨_, hf⟩)
    · simp at h1
    · cases hf
  · rintro h' (⟨_, hf⟩ | ⟨_, he⟩)
    · cases hf
    · injection he with he
      rw [he]
      apply Heap.ext; intro j; by_cases hj : j = 0 <;> simp [hj]

/-- Small axiom for allocation: `{emp} alloc 1 {∃ k. k ↦ 1}`. -/
theorem triple_alloc :
    Triple (sing Heap.emp) (alloc (1 : Nat)) (fun h => ∃ k, h = Heap.pt k 1) := by
  intro h hh
  have hh : h = Heap.emp := hh
  subst hh
  refine ⟨?_, ?_⟩
  · rintro ⟨_, _, hf⟩
    cases hf
  rintro h' ⟨k, _, he⟩
  injection he with he
  exact ⟨k, he⟩

example : WeakTriple (sing Heap.emp) (mutate 0 (5 : Nat)) (fun _ => False) := by
  intro h hh h' hr
  have hh : h = Heap.emp := hh
  subst hh
  rcases hr with ⟨_, hf⟩ | ⟨hne, _⟩
  · cases hf
  · exact hne rfl

theorem not_weakTriple_mutate :
    ¬ WeakTriple (sing (Heap.pt 0 1)) (mutate 0 (5 : Nat)) (sing (Heap.pt 0 1)) := by
  intro ht
  have hrun : mutate 0 (5 : Nat) (Heap.pt 0 1) (.ok (Heap.pt 0 5)) :=
    Or.inr ⟨by simp, by rw [mutate_pt_eq]⟩
  have h := ht _ rfl _ hrun
  have h' : Heap.pt 0 5 = (Heap.pt 0 1 : Heap Nat) := h
  have := congrArg (fun x : Heap Nat => x.val 0) h'
  simp at this

/-! ## Locality properties -/

example : SafetyMono (assertAlloc (V := Nat) 0) := assertAlloc_safetyMono 0
example : ¬ SafetyMono (allocAt 0 (1 : Nat)) := allocAt_not_safetyMono 0 1
example : FrameProp (assertAlloc (V := Nat) 0) := assertAlloc_frameProp 0
example : ¬ FrameProp (allocLeast (1 : Nat)) := allocLeast_not_frameProp 1
example : ¬ FrameProp (isAllocTest 1 0) := isAllocTest_not_frameProp (by decide)

theorem skip_local {S : Type _} [SepStruct S] : Local (skip : Cmd S) :=
  ⟨skip_safetyMono, skip_frameProp⟩

theorem diverge_local {S : Type _} [SepStruct S] : Local (diverge : Cmd S) :=
  ⟨fun _ _ _ _ hf => hf, fun _ _ _ _ _ hf => hf.elim⟩

theorem allocAt_not_local : ¬ Local (allocAt 0 (1 : Nat)) :=
  fun h => allocAt_not_safetyMono 0 1 h.1

/-- The frame rule holds for `skip` (proved directly, without the general
theorem). -/
theorem skip_frameRuleSound {S : Type _} [SepStruct S] : FrameRuleSound (skip : Cmd S) := by
  intro P Q R ht h ⟨h₁, h₂, hd, he, hP, hR⟩
  refine ⟨safe_skip h, fun h' hr => ?_⟩
  have hr : h' = h := by injection hr
  subst hr
  exact ⟨h₁, h₂, hd, he, (ht h₁ hP).2 h₁ rfl, hR⟩

theorem allocAt_not_frameRuleSound : ¬ FrameRuleSound (allocAt 0 (1 : Nat)) := by
  intro H
  obtain ⟨_, ht, hnot⟩ := allocAt_frameProp_and_framed_triple_fails
  exact hnot (H _ _ _ ht)

theorem skip_frameRuleAtSingletons {S : Type _} [SepStruct S] :
    FrameRuleAtSingletons (skip : Cmd S) :=
  fun _ _ ht => skip_frameRuleSound _ _ _ ht

theorem allocLeast_not_frameRuleAtSingletons :
    ¬ FrameRuleAtSingletons (allocLeast (1 : Nat)) := by
  intro H
  have ht : Triple (sing Heap.emp) (allocLeast (1 : Nat)) (post (allocLeast 1) Heap.emp) := by
    intro h hh
    have hh : h = Heap.emp := hh
    subst hh
    exact ⟨safe_allocLeast 1 _, fun _ hr => hr⟩
  have hF := H Heap.emp (Heap.pt 0 2) ht
  have hpre : sep (sing Heap.emp) (sing (Heap.pt 0 2))
      (union (Heap.emp : Heap Nat) (Heap.pt 0 2)) :=
    ⟨_, _, fun _ => Or.inl rfl, rfl, rfl, rfl⟩
  have hrun : allocLeast 1 (union (Heap.emp : Heap Nat) (Heap.pt 0 2))
      (.ok ((union (Heap.emp : Heap Nat) (Heap.pt 0 2)).set 1 (some 1))) := by
    refine ⟨1, by simp, ?_, rfl⟩
    intro j hj
    have : j = 0 := by omega
    subst this
    simp
  obtain ⟨q, r', hd, _, ⟨k, _, hlt, he⟩, hr'⟩ := (hF _ hpre).2 _ hrun
  have hr' : r' = Heap.pt 0 2 := hr'
  subst hr'
  have hk0 : k = 0 := by
    cases k with
    | zero => rfl
    | succ k => exact absurd rfl (hlt 0 (by omega))
  subst hk0
  injection he with he
  subst he
  rcases hd 0 with h1 | h1 <;> simp at h1

/-- Every singleton assertion is precise (in any separation structure). -/
theorem sing_precise {S : Type _} [SepStruct S] (x : S) : Precise (sing x) := by
  intro _ r₁ _ r₂ _ _ _ h1 h2
  exact (h1 : r₁ = x).trans (h2 : r₂ = x).symm

theorem skip_frameRuleForPreciseFrames {S : Type _} [SepStruct S] :
    FrameRuleForPreciseFrames (skip : Cmd S) :=
  fun P Q R _ ht => skip_frameRuleSound P Q R ht

theorem allocAt_not_frameRuleForPreciseFrames :
    ¬ FrameRuleForPreciseFrames (allocAt 0 (1 : Nat)) := by
  intro H
  obtain ⟨_, ht, hnot⟩ := allocAt_frameProp_and_framed_triple_fails
  exact hnot (H _ _ _ (sing_precise _) ht)

/-! ## Precision, unique frames, distribution -/

/-- `k ↦ -`: cell `k` is the only allocated cell, with any value. -/
def ptAny (k : Nat) : Assn (Heap Nat) := fun h => ∃ v, h = Heap.pt k v

theorem ptAny_part_eq {k : Nat} {f₁ f₂ : Heap Nat} {v₁ v₂ : Nat}
    (d₁ : disj f₁ (Heap.pt k v₁)) (d₂ : disj f₂ (Heap.pt k v₂))
    (he : union f₁ (Heap.pt k v₁) = union f₂ (Heap.pt k v₂)) : v₁ = v₂ := by
  have hk := congrArg (fun x : Heap Nat => x.val k) he
  have e1 : f₁.val k = none := by rcases d₁ k with h | h <;> simp_all
  have e2 : f₂.val k = none := by rcases d₂ k with h | h <;> simp_all
  simp [e1, e2] at hk
  exact hk

theorem ptAny_precise (k : Nat) : Precise (ptAny k) := by
  rintro f₁ _ f₂ _ d₁ d₂ he ⟨v₁, rfl⟩ ⟨v₂, rfl⟩
  rw [ptAny_part_eq d₁ d₂ he]

theorem ptAny_uniqueFrame (k : Nat) : UniqueFrame (ptAny k) := by
  rintro f₁ _ f₂ _ d₁ d₂ he ⟨v₁, rfl⟩ ⟨v₂, rfl⟩
  have hv := ptAny_part_eq d₁ d₂ he
  subst hv
  exact heap_rightCancel Nat _ _ _ d₁ d₂ he

theorem ptAny_conjDistrib (k : Nat) : ConjDistrib (ptAny k) := by
  intro P Q h ⟨f₁, r₁, d₁, e₁, hP, hR₁⟩ ⟨f₂, r₂, d₂, e₂, hQ, hR₂⟩
  have hf : f₁ = f₂ := ptAny_uniqueFrame k f₁ r₁ f₂ r₂ d₁ d₂ (e₁.symm.trans e₂) hR₁ hR₂
  subst hf
  exact ⟨f₁, r₁, d₁, e₁, ⟨hP, hQ⟩, hR₁⟩

theorem emp_conjDistrib : ConjDistrib (sing (Heap.emp : Heap Nat)) := by
  intro P Q h ⟨f₁, r₁, _, e₁, hP, hR₁⟩ ⟨f₂, r₂, _, e₂, hQ, hR₂⟩
  have hR₁ : r₁ = Heap.emp := hR₁
  have hR₂ : r₂ = Heap.emp := hR₂
  subst hR₁; subst hR₂
  have h1 : h = f₁ := by rw [e₁]; exact Heap.join_emp f₁
  have h2 : h = f₂ := by rw [e₂]; exact Heap.join_emp f₂
  subst h1; subst h2
  exact ⟨h, Heap.emp, fun _ => Or.inr rfl, (Heap.join_emp h).symm, ⟨hP, hQ⟩, rfl⟩

theorem true_not_precise : ¬ Precise (fun _ : Heap Nat => True) := by
  intro hp
  have := hp Heap.emp (Heap.pt 0 1) (Heap.pt 0 1) Heap.emp (fun _ => Or.inl rfl)
    (fun _ => Or.inr rfl) (by rw [Heap.union_eq, Heap.union_eq, Heap.emp_join, Heap.join_emp])
    trivial trivial
  have := congrArg (fun x : Heap Nat => x.val 0) this
  simp at this

theorem oneCell_not_uniqueFrame : ¬ UniqueFrame oneCell := by
  intro hu
  have := hu (Heap.pt 0 1) (Heap.pt 1 2) (Heap.pt 1 2) (Heap.pt 0 1)
    pt01_disj_pt12 pt12_disj_pt01 pt01_union_pt12_comm ⟨1, 2, rfl⟩ ⟨0, 1, rfl⟩
  exact pt01_ne_pt12 this

example : oneCell (Heap.pt 3 4) := ⟨3, 4, rfl⟩

theorem oneCell_not_emp : ¬ oneCell Heap.emp := by
  rintro ⟨k, v, h⟩
  have := congrArg (fun x : Heap Nat => x.val k) h
  simp at this

theorem oneCell_not_two : ¬ oneCell (union (Heap.pt 0 1) (Heap.pt 1 2)) := by
  rintro ⟨k, v, h⟩
  have h0 := congrArg (fun x : Heap Nat => x.val 0) h
  have h1 := congrArg (fun x : Heap Nat => x.val 1) h
  simp at h0 h1
  by_cases hk : k = 0
  · subst hk; simp at h1
  · simp [Ne.symm hk] at h0

example : someCellAllocated (Heap.pt 3 4) := ⟨3, by simp⟩

theorem someCellAllocated_not_emp : ¬ someCellAllocated Heap.emp := by
  rintro ⟨k, h⟩
  exact h rfl

/-! ## Further laws and heap notions -/

example : UnionAssocRev (Heap Nat) := heap_unionAssocRev Nat
example : UnionAssocRev AssocGap := assocGap_unionAssocRev_and_fqTriple_frame_fails.1
example : ¬ UnionAssocRev OneWayAssoc := oneWayAssoc_unionAssoc_and_fqTriple_frame_fails.2.1

example : RightUnitLaw (Heap.emp : Heap Nat) := heap_rightUnitLaw Nat

theorem pt_not_rightUnitLaw : ¬ RightUnitLaw (Heap.pt 0 1 : Heap Nat) := by
  intro h
  rcases (h (Heap.pt 0 1)).1 0 with h1 | h1 <;> simp at h1

example : Heap.Sub (Heap.pt 0 1 : Heap Nat) (union (Heap.pt 0 1) (Heap.pt 1 2)) := by
  intro k hk
  by_cases h0 : k = 0
  · subst h0; simp
  · simp [h0] at hk

theorem pt02_not_sub_pt01 : ¬ Heap.Sub (Heap.pt 0 2 : Heap Nat) (Heap.pt 0 1) := by
  intro h
  have := h 0 (by simp)
  simp at this

/-! ## Frame-quantified triples -/

example : FQTriple (sing (Heap.pt 0 1 : Heap Nat)) skip (sing (Heap.pt 0 1)) := skip_fqTriple
example : FQTriple (sing Heap.emp) (allocLeast (1 : Nat)) (fun h => ∃ k, h = Heap.pt k 1) :=
  allocLeast_fqTriple_someCell
example : ¬ FQTriple (sing Heap.emp) (allocLeast (1 : Nat)) (sing (Heap.pt 0 1)) :=
  allocLeast_triple_and_not_fqTriple.2

/-! ## Predictable allocation -/

example : AlwaysAllocatesAt (detAlloc (fun _ => 0) (1 : Nat)) Heap.emp 0 :=
  not_frameProp_of_alwaysAllocatesAt_nonvacuous.2.2.1
example : ¬ AlwaysAllocatesAt (alloc (1 : Nat)) Heap.emp 0 :=
  alloc_not_alwaysAllocatesAt_and_frameProp.2.2.1
example : RunsWhenOccupied (detAlloc (fun _ => 0) (1 : Nat)) Heap.emp 0 1 :=
  not_frameProp_of_alwaysAllocatesAt_nonvacuous.2.2.2
example : ¬ RunsWhenOccupied (detAllocOnEmp (1 : Nat)) Heap.emp 0 1 :=
  detAllocOnEmp_not_runsWhenOccupied_and_frameProp.2.2.2.1

/-! ## Command transitions -/

example : (skip : Cmd (Heap Nat)) (Heap.pt 0 1) (.ok (Heap.pt 0 1)) := rfl
example : ¬ (skip : Cmd (Heap Nat)) (Heap.pt 0 1) .fault := by intro h; cases h
example : ¬ (skip : Cmd (Heap Nat)) (Heap.pt 0 1) (.ok Heap.emp) := by
  intro h
  injection h with h
  have := congrArg (fun x : Heap Nat => x.val 0) h
  simp at this

example : ¬ (diverge : Cmd (Heap Nat)) Heap.emp (.ok Heap.emp) := fun h => h
example : ¬ (diverge : Cmd (Heap Nat)) Heap.emp .fault := fun h => h

example : (abort : Cmd (Heap Nat)) Heap.emp .fault := rfl
example : ¬ (abort : Cmd (Heap Nat)) Heap.emp (.ok Heap.emp) := by intro h; cases h

example : assertAlloc (V := Nat) 0 (Heap.pt 0 1) (.ok (Heap.pt 0 1)) := Or.inr ⟨by simp, rfl⟩
example : ¬ assertAlloc (V := Nat) 0 (Heap.pt 0 1) .fault := by
  rintro (⟨h, _⟩ | ⟨_, h⟩) <;> first | simp at h | cases h

example : lookup 0 1 (union (Heap.pt 0 5 : Heap Nat) (Heap.pt 1 0))
    (.ok ((union (Heap.pt 0 5 : Heap Nat) (Heap.pt 1 0)).set 1 (some 5))) :=
  Or.inr ⟨by simp, by simp, by simp⟩
example : lookup (V := Nat) 0 1 (Heap.pt 0 5) .fault := Or.inl ⟨Or.inr (by simp), rfl⟩
example : ¬ lookup (V := Nat) 0 1 (union (Heap.pt 0 5) (Heap.pt 1 0)) .fault :=
  (safe_lookup_iff 0 1 _).2 ⟨by simp, by simp⟩
example : ¬ lookup 0 1 (union (Heap.pt 0 5 : Heap Nat) (Heap.pt 1 0))
    (.ok (union (Heap.pt 0 5 : Heap Nat) (Heap.pt 1 0))) := by
  rintro (⟨_, hf⟩ | ⟨_, _, he⟩)
  · cases hf
  · injection he with he
    have hv := congrArg (fun x : Heap Nat => x.val 1) he
    simp at hv

example : mutate 0 (5 : Nat) (Heap.pt 0 1) (.ok (Heap.pt 0 5)) := Or.inr ⟨by simp, by rw [mutate_pt_eq]⟩
example : mutate 0 (5 : Nat) Heap.emp .fault := Or.inl ⟨rfl, rfl⟩
example : ¬ mutate 0 (5 : Nat) (Heap.pt 0 1) .fault := (safe_mutate_iff 0 5 _).2 (by simp)

example : alloc (1 : Nat) Heap.emp (.ok (Heap.pt 7 1)) := ⟨7, rfl, rfl⟩
example : ¬ alloc (1 : Nat) (Heap.pt 0 1) (.ok (Heap.pt 0 1)) := by
  rintro ⟨k, hk, he⟩
  injection he with he
  have h0 := congrArg (fun x : Heap Nat => x.val k) he
  by_cases hk0 : k = 0
  · subst hk0; simp at hk
  · simp [hk0] at h0
example : ¬ alloc (1 : Nat) Heap.emp .fault := safe_alloc 1 _

example : allocInto 0 9 (Heap.pt 0 0) (.ok (((Heap.pt 0 0).set 3 (some 9)).set 0 (some 3))) :=
  Or.inr ⟨by simp, 3, by simp, rfl⟩
example : allocInto 0 9 Heap.emp .fault := Or.inl ⟨rfl, rfl⟩
example : ¬ allocInto 0 9 (Heap.pt 0 0) .fault := (safe_allocInto_iff 0 9 _).2 (by simp)
example : ¬ allocInto 0 7 (Heap.pt 0 0) (.ok (Heap.pt 0 0)) := by
  rintro (⟨_, hf⟩ | ⟨_, k, hk, he⟩)
  · cases hf
  · injection he with he
    have hv0 := congrArg (fun x : Heap Nat => x.val 0) he
    simp at hv0
    subst hv0
    simp at hk

example : free (V := Nat) 0 (Heap.pt 0 1) (.ok ((Heap.pt 0 1).set 0 none)) := Or.inr ⟨by simp, rfl⟩
example : free (V := Nat) 0 Heap.emp .fault := Or.inl ⟨rfl, rfl⟩
example : ¬ free (V := Nat) 0 (Heap.pt 0 1) .fault := (safe_free_iff 0 _).2 (by simp)

example : allocAt 0 (1 : Nat) Heap.emp (.ok (Heap.pt 0 1)) := Or.inr ⟨rfl, rfl⟩
example : allocAt 0 (1 : Nat) (Heap.pt 0 2) .fault := Or.inl ⟨by simp, rfl⟩
example : ¬ allocAt 0 (1 : Nat) Heap.emp .fault := (safe_allocAt_iff 0 1 _).2 rfl

example : allocAtBlock 0 (1 : Nat) Heap.emp (.ok (Heap.pt 0 1)) := ⟨rfl, rfl⟩
example : ¬ allocAtBlock 0 (1 : Nat) (Heap.pt 0 2) (.ok (Heap.pt 0 1)) :=
  fun h => allocAtBlock_local_and_blocks_when_taken.2 ⟨_, h⟩

example : allocLeast (1 : Nat) Heap.emp (.ok (Heap.pt 0 1)) :=
  ⟨0, rfl, fun _ h => absurd h (Nat.not_lt_zero _), rfl⟩
example : ¬ allocLeast (1 : Nat) Heap.emp (.ok (Heap.pt 7 1)) := by
  rintro ⟨k, _, hlt, he⟩
  cases k with
  | zero =>
    injection he with he
    have := congrArg (fun x : Heap Nat => x.val 0) he
    simp at this
  | succ k => exact hlt 0 (by omega) rfl

example : isAllocTest 1 0 (Heap.pt 0 0) (.ok ((Heap.pt 0 0).set 0 (some 0))) :=
  Or.inr (Or.inr ⟨by simp, by simp, rfl⟩)
example : isAllocTest 1 0 Heap.emp .fault := Or.inl ⟨rfl, rfl⟩
example : ¬ isAllocTest 1 0 (Heap.pt 0 0) .fault := (safe_isAllocTest_iff 1 0 _).2 (by simp)
example : ¬ isAllocTest 1 0 (Heap.pt 0 0) (.ok ((Heap.pt 0 0).set 0 (some 1))) := by
  rintro (⟨_, hf⟩ | ⟨_, hk, _⟩ | ⟨_, _, he⟩)
  · cases hf
  · simp at hk
  · injection he with he
    have := congrArg (fun x : Heap Nat => x.val 0) he
    simp at this

example : detAlloc (fun _ => 0) (1 : Nat) Heap.emp (.ok (Heap.pt 0 1)) := rfl
example : ¬ detAlloc (fun _ => 0) (1 : Nat) Heap.emp .fault := safe_detAlloc _ _ _
example : ¬ detAlloc (fun _ : Heap Nat => 0) 1 Heap.emp (.ok Heap.emp) := by
  intro he
  injection he with he
  have hv := congrArg (fun x : Heap Nat => x.val 0) he
  simp at hv

example : detAllocInto (fun _ => 3) 0 9 (Heap.pt 0 0)
    (.ok (((Heap.pt 0 0).set 3 (some 9)).set 0 (some 3))) := Or.inr ⟨by simp, rfl⟩
example : detAllocInto (fun _ => 3) 0 9 Heap.emp .fault := Or.inl ⟨rfl, rfl⟩
example : ¬ detAllocInto (fun _ => 3) 0 9 (Heap.pt 0 0) .fault :=
  (safe_detAllocInto_iff _ 0 9 _).2 (by simp)

example : detAllocOnEmp (1 : Nat) Heap.emp (.ok (Heap.pt 0 1)) := ⟨rfl, rfl⟩
example : ¬ detAllocOnEmp (1 : Nat) (Heap.pt 0 1) (.ok (Heap.pt 0 1)) := by
  rintro ⟨he, _⟩
  have hv := congrArg (fun x : Heap Nat => x.val 0) he
  simp at hv

example : faultOrSet0 (1 : Nat) Heap.emp .fault := Or.inl rfl
example : ¬ faultOrSet0 (1 : Nat) Heap.emp (.ok Heap.emp) := by
  rintro (hf | he)
  · cases hf
  · injection he with he
    have hv := congrArg (fun x : Heap Nat => x.val 0) he
    simp at hv

end Toy.Sep
