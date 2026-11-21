import Toy.WrapNiche.ProofLemmas

/-!
# Main results

Group 1. Wrapping membership by one subtraction; fixed-origin comparison tests.
Group 2. The affine decoder: equality with the imported lookup layout, lawfulness, the
         four-way classification of field values, and lawfulness with dead slots.
Group 3. Contiguous capacity versus the unconstrained niche count.
Group 4. Declaration-order dependence and the rotated encoding.
Group 5. Nested `Option` by adjacent reservation.
Group 6. Discriminant write order: operational versus erased `SetDiscriminant`.

Model–system relation: none proved. These are statements about the toy model; they neither
establish nor refute the corresponding claims about rustc's layout computation, its generated
code, or its interpreter.
-/

namespace Toy.WrapNiche

open Imported

/-! ## Group 1: wrapping membership -/

/-- Membership in a wrapping interval `[s, e]` is the single-subtraction test
`(x - s) mod M ≤ (e - s) mod M`, for every `M`, interval and value (no hypothesis). -/
theorem mem_iff_offset_le_offset {M : Nat} (I : WrapInterval M) (x : Fin M) :
    I.Mem x ↔ offset I.s x ≤ offset I.s I.e := by
  unfold WrapInterval.Mem
  rw [offset_eq I.s x, offset_eq I.s I.e]
  have hs := I.s.isLt; have he := I.e.isLt; have hx := x.isLt
  simp only [Fin.le_def]
  split <;> split <;> omega

/-- For a non-full wrapping interval (`size < M`), the interval `[e + 1, s - 1]` (wrapping)
contains exactly the non-members. -/
theorem compl_mem_iff_not_mem_of_size_lt {M : Nat} (I : WrapInterval M) (hI : I.size < M)
    (x : Fin M) : I.compl.Mem x ↔ ¬ I.Mem x := by
  rw [mem_iff_offset_le_offset, mem_iff_offset_le_offset]
  unfold WrapInterval.compl WrapInterval.size at *
  have hM : 2 ≤ M := by omega
  have hse := offset_lt I.s I.e
  have hsx := offset_lt I.s x
  have he1 : offset I.s (wrapAdd I.e 1) = offset I.s I.e + 1 := by
    have : wrapAdd I.e 1 = wrapAdd I.s (offset I.s I.e + 1) := by
      rw [← wrapAdd_add, wrapAdd_offset]
    rw [this, offset_wrapAdd_of_lt I.s hI]
  have hs1 : offset I.s (wrapSub I.s 1) = M - 1 := offset_wrapSub_one I.s hM
  have h1 := offset_shift I.s (wrapAdd I.e 1) x
  have h2 := offset_shift I.s (wrapAdd I.e 1) (wrapSub I.s 1)
  rw [he1] at h1 h2
  rw [hs1] at h2
  have h2' : offset (wrapAdd I.e 1) (wrapSub I.s 1) = M - (offset I.s I.e + 2) := by
    rw [h2, show M - 1 + (M - (offset I.s I.e + 1)) = (M - (offset I.s I.e + 2)) + M by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  rw [h1, h2']
  by_cases hle : offset I.s x ≤ offset I.s I.e
  · rw [Nat.mod_eq_of_lt (by omega)]; omega
  · rw [show offset I.s x + (M - (offset I.s I.e + 1)) =
        (offset I.s x - (offset I.s I.e + 1)) + M by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega

/-- A fixed-origin comparison test (origin `o`) is exact for the interval `I` iff `I` does not
wrap past `o`, i.e. `(s - o) mod M ≤ (e - o) mod M`. -/
theorem originTest_exactFor_iff_offset_le {M : Nat} (o : Fin M) (I : WrapInterval M) :
    ExactFor (originTest o) I ↔ offset o I.s ≤ offset o I.e := by
  unfold ExactFor originTest
  have hos := offset_lt o I.s
  have hoe := offset_lt o I.e
  constructor
  · intro hex
    have hm : I.Mem I.s :=
      (mem_iff_offset_le_offset I I.s).mpr (by rw [offset_self]; exact Nat.zero_le _)
    exact (hex I.s).mp hm |>.2
  · intro hle x
    rw [mem_iff_offset_le_offset]
    have hox := offset_lt o x
    rw [offset_shift o I.s x, offset_shift o I.s I.e]
    have he' : (offset o I.e + (M - offset o I.s)) % M = offset o I.e - offset o I.s := by
      rw [show offset o I.e + (M - offset o I.s) = (offset o I.e - offset o I.s) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [he']
    by_cases hx : offset o I.s ≤ offset o x
    · rw [show offset o x + (M - offset o I.s) = (offset o x - offset o I.s) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
    · rw [Nat.mod_eq_of_lt (by omega)]; omega

/-- For `M ≥ 2`, no fixed origin `o` gives a comparison test that is exact for every interval:
it fails on the two-element interval `[o - 1, o]` (wrapping). -/
theorem not_exactFor_originTest_wrapSub_one_of_two_le {M : Nat} (hM : 2 ≤ M) (o : Fin M) :
    ¬ ExactFor (originTest o) ⟨wrapSub o 1, o⟩ := by
  rw [originTest_exactFor_iff_offset_le, offset_wrapSub_one o hM, offset_self]; omega

/-! ## Group 2: the affine decoder -/

/-- The single-subtraction layout of the dead-slot-free enum is the imported lookup layout
`nicheLayoutK V (affineTags A)`, for every validity set and every encoding (no hypothesis;
both decoders pick the least relative index whose tag matches). -/
theorem affineLayout_eq_nicheLayoutK_affineTags {n : Nat} (V : Validity n)
    (A : AffineNiche (256 ^ n)) : affineLayout V A = nicheLayoutK V (affineTags A) := by
  apply Layout.ext
  · funext y; cases y <;> rfl
  · funext x
    simp only [affineLayout, nicheLayoutK]
    have hlt := offset_lt A.nicheStart x
    by_cases h : offset A.nicheStart x ≤ A.span
    · have hfind : (List.finRange (A.span + 1)).find? (fun i => affineTags A i == x) =
          some ⟨offset A.nicheStart x, Nat.lt_succ_of_le h⟩ := by
        rw [List.find?_eq_some_iff_getElem]
        refine ⟨by simp [affineTags, AffineNiche.tagOf, wrapAdd_offset],
                offset A.nicheStart x, by simp; omega, by simp, fun j hj => ?_⟩
        simp only [List.getElem_finRange, affineTags, AffineNiche.tagOf, Bool.not_eq_true',
          beq_eq_false_iff_ne, ne_eq]
        intro heq
        have h1 := congrArg (offset A.nicheStart) heq
        change offset A.nicheStart (wrapAdd A.nicheStart j) = offset A.nicheStart x at h1
        rw [offset_wrapAdd_of_lt A.nicheStart (by omega)] at h1
        omega
      simp [h, hfind]
    · have hfind : (List.finRange (A.span + 1)).find? (fun i => affineTags A i == x) = none := by
        rw [List.find?_eq_none]
        intro i _
        simp only [affineTags, AffineNiche.tagOf]
        intro hbeq
        have heq : wrapAdd A.nicheStart i.val = x := beq_iff_eq.mp hbeq
        have h1 := congrArg (offset A.nicheStart) heq
        rw [offset_wrapAdd] at h1
        have hmod : i.val % 256 ^ n ≤ i.val := Nat.mod_le _ _
        have hi := i.isLt
        omega
      simp [h, hfind]

/-- The single-subtraction layout of the dead-slot-free enum is lawful iff the span fits the
field (`span < 256 ^ n`) and every tag is invalid for the payload. -/
theorem affineLayout_lawful_iff_span_lt_and_tagsDisjoint {n : Nat} (V : Validity n)
    (A : AffineNiche (256 ^ n)) :
    Lawful (affineLayout V A) ↔ (A.span < 256 ^ n ∧ TagsDisjoint V A.nicheStart A.span) := by
  rw [affineLayout_eq_nicheLayoutK_affineTags, nicheLayoutK_lawful_iff_injective_and_isNiche]
  constructor
  · rintro ⟨hinj, hniche⟩
    refine ⟨?_, fun r hr => hniche ⟨r, Nat.lt_succ_of_le hr⟩⟩
    rcases Nat.lt_or_ge A.span (256 ^ n) with hlt | hge
    · exact hlt
    · exfalso
      have h0 : (⟨0, Nat.zero_lt_succ _⟩ : Fin (A.span + 1)) ≠ ⟨256 ^ n, by omega⟩ := by
        intro h
        have hv : (0 : Nat) = 256 ^ n := congrArg Fin.val h
        have hpos := pat_card_pos n
        omega
      have heq : affineTags A ⟨0, Nat.zero_lt_succ _⟩ = affineTags A ⟨256 ^ n, by omega⟩ := by
        apply Fin.ext; unfold affineTags AffineNiche.tagOf wrapAdd; simp
      exact h0 (hinj heq)
  · rintro ⟨hspan, hdisj⟩
    refine ⟨fun i j hij => ?_, fun i => hdisj i.val (Nat.lt_succ_iff.mp i.isLt)⟩
    have := congrArg (offset A.nicheStart) hij
    simp only [affineTags, AffineNiche.tagOf] at this
    rw [offset_wrapAdd_of_lt A.nicheStart (by omega),
        offset_wrapAdd_of_lt A.nicheStart (by omega)] at this
    exact Fin.ext this

/-- Four-way classification under an affine encoding with `span < M` and every tag invalid:
a value is classified `valid` exactly when it is valid for the payload; the decoder `decodeIdx`
returns `u` on `valid` and `unusedNiche` values; it returns `first + r` on the tag of relative
index `r ≤ span`, which lies in the tag interval; and every value classified `liveTag` or
`deadTag` is such a tag. -/
theorem classify_valid_iff_and_decodeIdx_of_span_lt_of_tagsDisjoint {M : Nat} (E : EnumSpec)
    (A : AffineNiche M) (V : Fin M → Bool) (hspan : A.span < M)
    (hdisj : TagsDisjoint V A.nicheStart A.span) (x : Fin M) :
    (classify E A V x = .valid ↔ V x = true) ∧
    (classify E A V x = .valid → decodeIdx E.u A x = E.u) ∧
    (classify E A V x = .unusedNiche → decodeIdx E.u A x = E.u) ∧
    (∀ r, r ≤ A.span → x = A.tagOf r →
      decodeIdx E.u A x = A.first + r ∧ A.tagInterval.Mem x) ∧
    (classify E A V x = .liveTag ∨ classify E A V x = .deadTag →
      ∃ r, r ≤ A.span ∧ x = A.tagOf r ∧ decodeIdx E.u A x = A.first + r) := by
  have hmem : A.tagInterval.Mem x ↔ offset A.nicheStart x ≤ A.span := by
    rw [mem_iff_offset_le_offset]; unfold AffineNiche.tagInterval
    rw [offset_wrapAdd_of_lt A.nicheStart hspan]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold classify
    by_cases hm : A.tagInterval.Mem x
    · have hle := hmem.mp hm
      have hv : V x = false := by
        have := hdisj _ hle; rwa [wrapAdd_offset] at this
      simp only [hm, ↓reduceIte, hv, Bool.false_eq_true, iff_false]
      split <;> decide
    · simp only [hm, ↓reduceIte]
      cases hv : V x <;> simp
  · unfold classify decodeIdx
    by_cases hm : A.tagInterval.Mem x
    · simp only [hm, ↓reduceIte]; split <;> intro h <;> cases h
    · intro _; have hnot : ¬ offset A.nicheStart x ≤ A.span := fun h => hm (hmem.mpr h)
      simp [hnot]
  · unfold classify decodeIdx
    by_cases hm : A.tagInterval.Mem x
    · simp only [hm, ↓reduceIte]; split <;> intro h <;> cases h
    · intro _; have hnot : ¬ offset A.nicheStart x ≤ A.span := fun h => hm (hmem.mpr h)
      simp [hnot]
  · intro r hr hx
    subst hx
    have hoff : offset A.nicheStart (A.tagOf r) = r := offset_wrapAdd_of_lt A.nicheStart (by omega)
    refine ⟨by unfold decodeIdx; simp [hoff, hr], hmem.mpr (by rw [hoff]; exact hr)⟩
  · intro hc
    have hm : A.tagInterval.Mem x := by
      by_cases hm : A.tagInterval.Mem x
      · exact hm
      · exfalso
        unfold classify at hc
        simp only [hm, ↓reduceIte] at hc
        cases hv : V x <;> simp [hv] at hc
    have hle := hmem.mp hm
    refine ⟨offset A.nicheStart x, hle, (wrapAdd_offset _ _).symm, ?_⟩
    unfold decodeIdx; simp [hle]

/-- With `span < 256 ^ n`, the checked decoder of the general enum accepts a field value iff it
is classified `valid` or `liveTag`; `deadTag` and `unusedNiche` values are rejected. -/
theorem genLayout_dec_isSome_iff_classify_of_span_lt {n : Nat} (E : EnumSpec)
    (A : AffineNiche (256 ^ n)) (V : Validity n) (hspan : A.span < 256 ^ n) (x : Pat n) :
    ((genLayout E A V).dec x).isSome = true ↔
      (classify E A V x = .valid ∨ classify E A V x = .liveTag) := by
  have hmem : A.tagInterval.Mem x ↔ offset A.nicheStart x ≤ A.span := by
    rw [mem_iff_offset_le_offset]; unfold AffineNiche.tagInterval
    rw [offset_wrapAdd_of_lt A.nicheStart hspan]
  unfold genLayout classify
  by_cases hle : offset A.nicheStart x ≤ A.span
  · have hm : A.tagInterval.Mem x := hmem.mpr hle
    simp only [hle, hm, ↓reduceIte]
    by_cases hl : E.Live (A.first + offset A.nicheStart x) <;> simp [hl]
  · have hm : ¬ A.tagInterval.Mem x := fun h => hle (hmem.mp h)
    simp only [hle, hm, ↓reduceIte]
    by_cases hv : V x = true <;> simp [hv]

/-- If the span fits the field, every tag in the range is invalid for the payload, and every live
variant lies in the range, then the affine layout of the general enum is lawful (dead slots
allowed: the niche range may contain `u` and uninhabited variants). -/
theorem genLayout_lawful_of_span_lt_of_tagsDisjoint_of_liveInRange {n : Nat} (E : EnumSpec)
    (A : AffineNiche (256 ^ n)) (V : Validity n) (hspan : A.span < 256 ^ n)
    (hdisj : TagsDisjoint V A.nicheStart A.span) (hlive : LiveInRange E A) :
    Lawful (genLayout E A V) := by
  refine ⟨?_, genLayout_canonical E A V⟩
  intro y
  cases y with
  | inl i =>
    have hrange := hlive i.val i.2.1 i.2.2.1 i.2.2.2
    have hr : i.val - A.first ≤ A.span := by omega
    have hoff : offset A.nicheStart (A.tagOf (i.val - A.first)) = i.val - A.first :=
      offset_wrapAdd_of_lt A.nicheStart (by omega)
    have hadd : A.first + (i.val - A.first) = i.val := by omega
    simp only [genLayout, hoff, hr, ↓reduceIte, hadd, i.2, ↓reduceDIte]
  | inr v =>
    have hnot : ¬ offset A.nicheStart v.val ≤ A.span := by
      intro hle
      have hfalse := hdisj _ hle
      rw [wrapAdd_offset, v.2] at hfalse
      cases hfalse
    simp only [genLayout, hnot, ↓reduceIte, v.2, ↓reduceDIte]

/-! ## Group 3: contiguous capacity -/

/-- For a payload with at least one valid value and an interval hull `H` of its validity set,
`span + 1` contiguous tags (wrapping) can all be placed on invalid values iff
`span + 1 ≤ M - H.size` (`H.size ≤ M`, so the subtraction does not truncate). -/
theorem exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull {M : Nat}
    (V : Fin M → Bool) (H : WrapInterval M) (hne : ∃ x, V x = true) (hH : IsHull V H)
    (span : Nat) :
    (∃ ns : Fin M, TagsDisjoint V ns span) ↔ span + 1 ≤ M - H.size := by
  have hHsz : H.size ≤ M := Nat.succ_le_of_lt (offset_lt H.s H.e)
  constructor
  · rintro ⟨ns, hdisj⟩
    obtain ⟨v0, hv0⟩ := hne
    have hspan_lt : span + 1 < M := by
      rcases Nat.lt_or_ge (span + 1) M with hlt | hge
      · exact hlt
      · exfalso
        have hlt : offset ns v0 ≤ span := by have := offset_lt ns v0; omega
        have hf := hdisj _ hlt
        rw [wrapAdd_offset, hv0] at hf
        cases hf
    let T : WrapInterval M := ⟨ns, wrapAdd ns span⟩
    have hTsz : T.size = span + 1 := by
      unfold WrapInterval.size; dsimp [T]; rw [offset_wrapAdd_of_lt ns (by omega)]
    have hTlt : T.size < M := by omega
    have hcov : Covers T.compl V := by
      intro x hx
      rw [compl_mem_iff_not_mem_of_size_lt T hTlt x, mem_iff_offset_le_offset]
      dsimp [T]
      rw [offset_wrapAdd_of_lt ns (by omega)]
      intro hle
      have hf := hdisj _ hle
      rw [wrapAdd_offset, hx] at hf
      cases hf
    have hmin : H.size ≤ T.compl.size := hH.2 T.compl hcov
    have hcsz : T.compl.size = M - T.size := by
      have hM : 2 ≤ M := by omega
      have hTlt' : offset T.s T.e + 1 < M := hTlt
      unfold WrapInterval.size WrapInterval.compl
      have he1 : offset T.s (wrapAdd T.e 1) = offset T.s T.e + 1 := by
        have : wrapAdd T.e 1 = wrapAdd T.s (offset T.s T.e + 1) := by
          rw [← wrapAdd_add, wrapAdd_offset]
        rw [this, offset_wrapAdd_of_lt T.s hTlt']
      have hs1 : offset T.s (wrapSub T.s 1) = M - 1 := offset_wrapSub_one T.s hM
      have hsh := offset_shift T.s (wrapAdd T.e 1) (wrapSub T.s 1)
      rw [he1, hs1] at hsh
      rw [hsh, show M - 1 + (M - (offset T.s T.e + 1)) = (M - (offset T.s T.e + 2)) + M by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    omega
  · intro hle
    have hHlt : H.size < M := by omega
    have hHlt' : offset H.s H.e + 1 < M := hHlt
    have hM : 2 ≤ M := by unfold WrapInterval.size at hHlt; omega
    refine ⟨wrapAdd H.e 1, fun r hr => ?_⟩
    cases hv : V (wrapAdd (wrapAdd H.e 1) r) with
    | false => rfl
    | true =>
      exfalso
      have hm := hH.1 _ hv
      have hnot : ¬ H.Mem (wrapAdd (wrapAdd H.e 1) r) := by
        rw [← compl_mem_iff_not_mem_of_size_lt H hHlt]
        rw [mem_iff_offset_le_offset]
        unfold WrapInterval.compl
        have he1 : offset H.s (wrapAdd H.e 1) = offset H.s H.e + 1 := by
          have : wrapAdd H.e 1 = wrapAdd H.s (offset H.s H.e + 1) := by
            rw [← wrapAdd_add, wrapAdd_offset]
          rw [this, offset_wrapAdd_of_lt H.s hHlt']
        have hs1 : offset H.s (wrapSub H.s 1) = M - 1 := offset_wrapSub_one H.s hM
        have hsh := offset_shift H.s (wrapAdd H.e 1) (wrapSub H.s 1)
        rw [he1, hs1] at hsh
        rw [offset_wrapAdd_of_lt _ (by omega), hsh,
            show M - 1 + (M - (offset H.s H.e + 1)) = (M - (offset H.s H.e + 2)) + M by omega,
            Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        unfold WrapInterval.size at hle; omega
      exact hnot hm

/-- A wrapping interval of size `I.size` has `M - I.size` non-members. -/
theorem nichesCount_intervalV {M : Nat} (I : WrapInterval M) :
    nichesCount (intervalV I) = M - I.size := by
  have hpart : ∀ l : List (Fin M),
      (l.filter (fun p => intervalV I p)).length +
      (l.filter (fun p => !intervalV I p)).length = l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih => cases h : intervalV I a <;> simp [h] <;> omega
  have hmem : ((List.finRange M).filter (fun p => intervalV I p)).length = I.size := by
    have heq : (fun p : Fin M => intervalV I p) =
        (fun p => decide (offset I.s p ≤ offset I.s I.e)) := by
      funext p
      unfold intervalV
      exact decide_eq_decide.mpr (mem_iff_offset_le_offset I p)
    rw [heq, list_count_offset I.s (offset I.s I.e) (offset_lt I.s I.e)]
    rfl
  have hsum := hpart (List.finRange M)
  rw [hmem, List.length_finRange] at hsum
  unfold nichesCount
  omega

/-- For every interval `H` that covers the valid values of `V`, the number `M - H.size` of
values outside `H` is at most the niche count of `V`, with equality iff every member of `H` is
valid. -/
theorem sub_size_le_nichesCount_and_eq_iff_of_covers {M : Nat} (V : Fin M → Bool)
    (H : WrapInterval M) (hcov : Covers H V) :
    M - H.size ≤ nichesCount V ∧ (M - H.size = nichesCount V ↔ ∀ x, H.Mem x → V x = true) := by
  let l1 := (List.finRange M).filter (fun p => !intervalV H p)
  let l2 := (List.finRange M).filter (fun p => !V p)
  have hnd1 : l1.Nodup := List.Pairwise.filter _ (List.nodup_finRange _)
  have hsub : ∀ x ∈ l1, x ∈ l2 := by
    intro x hx
    simp only [l1, l2, List.mem_filter, List.mem_finRange, true_and, Bool.not_eq_true'] at hx ⊢
    cases hv : V x with
    | false => rfl
    | true =>
      have hm := hcov x hv
      unfold intervalV at hx
      simp [hm] at hx
  have hl1 : l1.length = M - H.size := nichesCount_intervalV H
  have hle : M - H.size ≤ nichesCount V := hl1 ▸ Counting.nodup_length_le_of_subset hnd1 hsub
  refine ⟨hle, ⟨?_, ?_⟩⟩
  · intro heq x hx
    cases hv : V x with
    | true => rfl
    | false =>
      have hx2 : x ∈ l2 := by simp [l2, hv]
      have hlen : l2.length ≤ l1.length := by rw [hl1]; exact Nat.le_of_eq heq.symm
      have hx1 : x ∈ l1 := Counting.mem_of_nodup_of_length_ge hnd1 hsub hlen x hx2
      simp only [l1, List.mem_filter, List.mem_finRange, true_and, Bool.not_eq_true', intervalV,
        decide_eq_false_iff_not] at hx1
      exact absurd hx hx1
  · intro hall
    have hnd2 : l2.Nodup := List.Pairwise.filter _ (List.nodup_finRange _)
    have hsub2 : ∀ x ∈ l2, x ∈ l1 := by
      intro x hx
      simp only [l1, l2, List.mem_filter, List.mem_finRange, true_and, Bool.not_eq_true',
        intervalV, decide_eq_false_iff_not] at hx ⊢
      intro hm
      have := hall x hm
      rw [hx] at this
      cases this
    have hge : nichesCount V ≤ M - H.size := hl1 ▸ Counting.nodup_length_le_of_subset hnd2 hsub2
    omega

/-! ## Group 4: declaration order and the rotated encoding -/

/-- For a payload with at least one valid value, an interval hull `H`, `k ≥ 2`, and exactly
`k - 1` values outside `H` (`M - H.size = k - 1`; under `2 ≤ k` the subtraction `k - 1` does not
truncate): for every natural number `u`, some start `ns` makes the `naturalSpan k u + 1`
contiguous tags `ns, …, ns + naturalSpan k u` all invalid iff `u = 0` or `u = k - 1`. -/
theorem exists_tagsDisjoint_naturalSpan_iff_untagged_first_or_last_of_nonempty_of_isHull_of_sub_size_eq
    {M : Nat} (V : Fin M → Bool) (H : WrapInterval M) (hne : ∃ x, V x = true) (hH : IsHull V H)
    (k u : Nat) (hk : 2 ≤ k) (hcap : M - H.size = k - 1) :
    (∃ ns : Fin M, TagsDisjoint V ns (naturalSpan k u)) ↔ (u = 0 ∨ u = k - 1) := by
  rw [exists_tagsDisjoint_iff_span_succ_le_sub_size_of_nonempty_of_isHull V H hne hH, hcap,
    naturalSpan_eq k u hk]
  split <;> omega

/-- The rotated decoder is exact: for `u < k`, `k ≤ M + 1`, and all `k - 1` rotated tags invalid
(`RotTagsInvalid V k ns`), it recovers every variant `i ≠ u` (`i < k`) from its rotated tag and
decodes every valid value to `u`. -/
theorem rotDecodeIdx_exact_of_lt_of_le_succ_of_rotTagsInvalid {M : Nat} (V : Fin M → Bool)
    (k u : Nat) (ns : Fin M) (hu : u < k) (hkM : k ≤ M + 1) (hdisj : RotTagsInvalid V k ns) :
    (∀ i, i < k → i ≠ u → rotDecodeIdx k u ns (rotTag k u ns i) = i) ∧
    (∀ x, V x = true → rotDecodeIdx k u ns x = u) := by
  refine ⟨fun i hi hne => ?_, fun x hx => ?_⟩
  · have hk2 : 2 ≤ k := by omega
    have hrot_lt : rotIdx k u i + 1 < k := by
      unfold rotIdx
      by_cases hu1 : u + 1 < k
      · rw [Nat.mod_eq_of_lt hu1]
        by_cases hiu : u < i
        · have : i + k - (u + 1) = (i - (u + 1)) + k := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]; omega
        · rw [Nat.mod_eq_of_lt (by omega)]; omega
      · have hueq : u + 1 = k := by omega
        rw [hueq, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hi]; omega
    unfold rotDecodeIdx rotTag
    rw [offset_wrapAdd_of_lt ns (by omega)]
    simp only [hrot_lt, ↓reduceIte]
    unfold rotIdx
    by_cases hu1 : u + 1 < k
    · rw [Nat.mod_eq_of_lt hu1]
      by_cases hiu : u < i
      · have h1 : i + k - (u + 1) = (i - (u + 1)) + k := by omega
        have h2 : i - (u + 1) < k := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt h2,
            show i - (u + 1) + u + 1 = i by omega, Nat.mod_eq_of_lt hi]
      · have h2 : i + k - (u + 1) < k := by omega
        rw [Nat.mod_eq_of_lt h2,
            show i + k - (u + 1) + u + 1 = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
    · have hueq : u + 1 = k := by omega
      rw [hueq, Nat.mod_self, Nat.sub_zero, Nat.add_mod_right, Nat.mod_eq_of_lt hi,
          show i + u + 1 = i + k by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hi]
  · unfold rotDecodeIdx
    have hnot : ¬ offset ns x + 1 < k := by
      intro hlt
      have hf := hdisj _ hlt
      rw [wrapAdd_offset, hx] at hf
      cases hf
    simp [hnot]

/-! ## Group 5: nested `Option` -/

/-- For a non-full interval (`size < M`), the adjacent value on either side is a non-member,
the extended interval contains exactly the old members and that value, and its size is one
more. -/
theorem extend_spec_of_size_lt {M : Nat} (I : WrapInterval M) (d : Side) (hI : I.size < M) :
    ¬ I.Mem (adjNiche I d) ∧ (∀ x, (extend I d).Mem x ↔ (I.Mem x ∨ x = adjNiche I d)) ∧
      (extend I d).size = I.size + 1 := by
  unfold WrapInterval.size at hI ⊢
  have hM : 2 ≤ M := by omega
  have hse := offset_lt I.s I.e
  cases d with
  | high =>
    have he1 : wrapAdd I.e 1 = wrapAdd I.s (offset I.s I.e + 1) := by
      rw [← wrapAdd_add, wrapAdd_offset]
    have hoff : offset I.s (wrapAdd I.e 1) = offset I.s I.e + 1 := by
      rw [he1, offset_wrapAdd_of_lt I.s hI]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_iff_offset_le_offset]; unfold adjNiche; rw [hoff]; omega
    · intro x
      rw [mem_iff_offset_le_offset, mem_iff_offset_le_offset]
      unfold extend adjNiche; dsimp; rw [hoff]
      constructor
      · intro hle
        by_cases h : offset I.s x ≤ offset I.s I.e
        · exact Or.inl h
        · right
          have hxe : offset I.s x = offset I.s I.e + 1 := by omega
          rw [← wrapAdd_offset I.s x, hxe, ← he1]
      · rintro (h | rfl)
        · omega
        · rw [hoff]; exact Nat.le_refl _
    · unfold extend; dsimp; rw [hoff]
  | low =>
    have hs1 : offset I.s (wrapSub I.s 1) = M - 1 := offset_wrapSub_one I.s hM
    have hshift : ∀ y : Fin M, offset (wrapSub I.s 1) y = (offset I.s y + 1) % M := by
      intro y
      rw [offset_shift I.s (wrapSub I.s 1) y, hs1, show M - (M - 1) = 1 by omega]
    have hse1 : offset (wrapSub I.s 1) I.e = offset I.s I.e + 1 := by
      rw [hshift, Nat.mod_eq_of_lt hI]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_iff_offset_le_offset]; unfold adjNiche; rw [hs1]; omega
    · intro x
      rw [mem_iff_offset_le_offset, mem_iff_offset_le_offset]
      unfold extend adjNiche; dsimp; rw [hse1, hshift]
      have hsx := offset_lt I.s x
      by_cases hx : offset I.s x = M - 1
      · have hxeq : x = wrapSub I.s 1 := by
          rw [← wrapAdd_offset I.s x, hx, ← hs1, wrapAdd_offset]
        rw [hx, show M - 1 + 1 = M by omega, Nat.mod_self]
        exact ⟨fun _ => Or.inr hxeq, fun _ => Nat.zero_le _⟩
      · rw [Nat.mod_eq_of_lt (by omega)]
        constructor
        · intro hle; exact Or.inl (by omega)
        · rintro (h | rfl)
          · omega
          · rw [hs1] at hx; exact absurd rfl hx
    · unfold extend; dsimp; rw [hse1]

/-- For a non-full valid interval `I` in `n` bytes, one `Option` level that reserves the
adjacent value has a lawful niche-filled layout, and the values it accepts are exactly the
members of `extend I d`. -/
theorem nicheLayout_adjNiche_lawful_and_accepts_extend_of_size_lt {n : Nat}
    (I : WrapInterval (256 ^ n)) (d : Side) (hI : I.size < 256 ^ n) :
    Lawful (nicheLayout (intervalV I) (adjNiche I d)) ∧
      ∀ p, ((nicheLayout (intervalV I) (adjNiche I d)).dec p).isSome = intervalV (extend I d) p := by
  have ⟨hnot, hmem, _⟩ := extend_spec_of_size_lt I d hI
  refine ⟨(nicheLayout_lawful_iff_isNiche _ _).mpr (by unfold IsNiche intervalV; simp [hnot]),
    fun p => ?_⟩
  simp only [nicheLayout, intervalV]
  by_cases hp : p = adjNiche I d
  · subst hp; simp [(hmem _).mpr (Or.inr rfl)]
  · by_cases hm : I.Mem p
    · simp [hp, hm, (hmem p).mpr (Or.inl hm)]
    · have hnot' : ¬ (extend I d).Mem p := fun h => by
        rcases (hmem p).mp h with h1 | h2
        · exact hm h1
        · exact hp h2
      simp [hp, hm, hnot']

/-- Adjacent reservation over `sides.length` levels reserves a niche at every level iff
`sides.length ≤ M - R₀.size`, whatever the side chosen at each level; in that case the final
valid interval has size `R₀.size + sides.length`. -/
theorem levelsReserveNiches_iff_length_le_and_nest_size {M : Nat} (R₀ : WrapInterval M)
    (sides : List Side) :
    (LevelsReserveNiches R₀ sides ↔ sides.length ≤ M - R₀.size) ∧
      (sides.length ≤ M - R₀.size → (nest R₀ sides).size = R₀.size + sides.length) := by
  induction sides generalizing R₀ with
  | nil =>
    refine ⟨⟨fun _ => Nat.zero_le _, fun _ j hj => by cases hj⟩, fun _ => rfl⟩
  | cons d ds ih =>
    have hRsz : R₀.size ≤ M := Nat.succ_le_of_lt (offset_lt R₀.s R₀.e)
    have hstep0 : ¬ R₀.Mem (adjNiche R₀ d) ↔ R₀.size < M := by
      constructor
      · intro hnot
        rcases Nat.lt_or_ge R₀.size M with hlt | hge
        · exact hlt
        · exfalso
          have hfull : offset R₀.s R₀.e = M - 1 := by unfold WrapInterval.size at hRsz hge; omega
          exact hnot ((mem_iff_offset_le_offset R₀ _).mpr
            (by have := offset_lt R₀.s (adjNiche R₀ d); omega))
      · exact fun hlt => (extend_spec_of_size_lt R₀ d hlt).1
    have hsplit : LevelsReserveNiches R₀ (d :: ds) ↔
        ¬ R₀.Mem (adjNiche R₀ d) ∧ LevelsReserveNiches (extend R₀ d) ds := by
      unfold LevelsReserveNiches
      constructor
      · intro h
        exact ⟨h 0 (Nat.zero_lt_succ _), fun j hj => h (j + 1) (Nat.succ_lt_succ hj)⟩
      · rintro ⟨h0, htail⟩ j hj
        cases j with
        | zero => exact h0
        | succ j' => exact htail j' (Nat.lt_of_succ_lt_succ hj)
    refine ⟨?_, ?_⟩
    · rw [hsplit, hstep0]
      constructor
      · rintro ⟨hlt, htail⟩
        have hsz := (extend_spec_of_size_lt R₀ d hlt).2.2
        have hlen := (ih (extend R₀ d)).1.mp htail
        simp only [List.length_cons] at *; omega
      · intro hle
        simp only [List.length_cons] at hle
        have hlt : R₀.size < M := by omega
        have hsz := (extend_spec_of_size_lt R₀ d hlt).2.2
        exact ⟨hlt, (ih (extend R₀ d)).1.mpr (by omega)⟩
    · intro hle
      simp only [List.length_cons, nest] at hle ⊢
      have hlt : R₀.size < M := by omega
      have hsz := (extend_spec_of_size_lt R₀ d hlt).2.2
      rw [(ih (extend R₀ d)).2 (by omega), hsz]; omega

/-- `j` dataless variants over a payload whose valid values are the interval `R₀` have a lawful
layout in the payload's `n` bytes (any layout, not only adjacent reservation) iff
`j ≤ 256 ^ n - R₀.size`. -/
theorem exists_lawful_extEnum_intervalV_iff_le_sub_size {n : Nat} (R₀ : WrapInterval (256 ^ n))
    (j : Nat) :
    (∃ L : Layout (ExtEnum j (intervalV R₀)) n, Lawful L) ↔ j ≤ 256 ^ n - R₀.size := by
  rw [← (le_numInvalid_iff_exists_lawful_layout_iff_lawful_nicheLayoutK_firstNiches
    (intervalV R₀) j).1, ← nichesCount_eq_numInvalid, nichesCount_intervalV]

/-! ## Group 6: discriminant write order -/

/-- If every tag is invalid for the payload: operational `SetDiscriminant u` is defined iff the
niche field lies inside the place (for `nw ≥ 1`), is initialized and holds a valid value; and if
the niche field lies inside the place, after writing `x` into it, it is defined iff `x` is valid. -/
theorem setDisc_operational_untagged_isSome_iff_of_tagsDisjoint (L : OpLayout)
    (hdisj : TagsDisjoint L.V L.A.nicheStart L.A.span) :
    (∀ p, (setDisc .operational L L.E.u p).isSome = true ↔
      ∃ x, L.readNiche p = some x ∧ L.V x = true) ∧
    (∀ p (x : Pat L.nw), L.no + L.nw ≤ p.length →
      ((setDisc .operational L L.E.u (L.writeNiche p x)).isSome = true ↔ L.V x = true)) := by
  have h1 : ∀ p, (setDisc .operational L L.E.u p).isSome = true ↔
      ∃ x, L.readNiche p = some x ∧ L.V x = true := by
    intro p
    unfold setDisc
    simp only [↓reduceIte]
    have his : (if L.readDisc p = some L.E.u then some p else none).isSome = true ↔
        L.readDisc p = some L.E.u := by
      split <;> simp [*]
    rw [his]
    unfold OpLayout.readDisc
    cases hr : L.readNiche p with
    | none => simp
    | some x =>
      simp only [Option.some.injEq, exists_eq_left']
      unfold genLayout
      by_cases hle : offset L.A.nicheStart x ≤ L.A.span
      · have hvf : L.V x = false := by
          have := hdisj _ hle; rwa [wrapAdd_offset] at this
        simp only [hle, ↓reduceIte, hvf, Bool.false_eq_true, iff_false]
        split
        · rename_i hl
          simp only [Option.map_some, Option.some.injEq]
          exact hl.2.1
        · simp
      · simp only [hle, ↓reduceIte]
        by_cases hv : L.V x = true <;> simp [hv]
  refine ⟨h1, fun p x hfit => ?_⟩
  rw [h1, readNiche_writeNiche L p x hfit]
  simp

/-- The erased semantics refines the operational one: whenever a program runs without
undefined behaviour under the operational semantics, it produces the same place and output
under the erased semantics (no hypothesis). -/
theorem run_erased_eq_some_of_run_operational_eq_some (L : OpLayout) (prog : List Op)
    (s r : Bytes × List Nat) :
    run .operational L prog s = some r → run .erased L prog s = some r := by
  induction prog generalizing s with
  | nil => intro h; exact h
  | cons o os ih =>
    intro h
    simp only [run, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨s', hs', hrest⟩ := h
    refine ⟨s', ?_, ih s' hrest⟩
    cases o with
    | write off bs => exact hs'
    | readDisc => exact hs'
    | setDisc v =>
      rcases s with ⟨p, out⟩
      simp only [stepOp, Option.map_eq_some_iff] at hs' ⊢
      obtain ⟨p', hp', rfl⟩ := hs'
      refine ⟨p', ?_, rfl⟩
      unfold setDisc at hp' ⊢
      by_cases hvu : v = L.E.u
      · simp only [hvu, ↓reduceIte] at hp' ⊢
        split at hp'
        · exact hp'
        · cases hp'
      · simp only [hvu, ↓reduceIte] at hp' ⊢
        exact hp'

/-- A `write` operation whose byte range does not overlap the niche field commutes with
`SetDiscriminant v`, for every variant `v` (including `u`), both semantics and every state:
the two orders give the same result, undefined behaviour included (an out-of-bounds write is
undefined behaviour in both orders). -/
theorem run_write_setDisc_comm_of_disjointFromNiche (sem : Sem) (L : OpLayout) (v off : Nat)
    (bs : List (Fin 256)) (hdis : L.DisjointFromNiche off bs.length) (s : Bytes × List Nat) :
    run sem L [.write off bs, .setDisc v] s = run sem L [.setDisc v, .write off bs] s := by
  obtain ⟨p, out⟩ := s
  have hc := setDisc_writeBytes_comm_of_disjointFromNiche sem L v off bs hdis p
  simp only [run, stepOp]
  by_cases hfit : off + bs.length ≤ p.length
  · simp only [hfit, ↓reduceIte, Option.bind_some]
    rw [← hc]
    cases h : setDisc sem L v p with
    | none => simp
    | some q =>
      have hq := setDisc_length h
      have hfit' : off + bs.length ≤ q.length := by rw [hq]; exact hfit
      simp [hfit']
  · simp only [hfit, ↓reduceIte, Option.bind_none]
    cases h : setDisc sem L v p with
    | none => simp
    | some q =>
      have hq := setDisc_length h
      have hfit' : ¬ off + bs.length ≤ q.length := by rw [hq]; exact hfit
      simp [hfit']

/-- Fields first, then `SetDiscriminant`: if the niche field lies inside the place, the span
fits the field, every tag is invalid, and the field writes lie inside the place, are pairwise
disjoint and do not overlap the niche field, then (both semantics) for every encodable variant
`v` the program "field writes; `SetDiscriminant v`; read discriminant" is defined, reads `v`,
leaves `v`'s tag in the niche field and every field write in `ws` readable as written; and for
every valid niche value `x` the program "field writes; write `x` to the niche field;
`SetDiscriminant u`; read discriminant" is defined, reads `u`, leaves `x` in the niche field
and every field write in `ws` readable as written. -/
theorem run_fields_then_setDisc_readDisc_of_disjoint (sem : Sem) (L : OpLayout) (p : Bytes)
    (ws : List (Nat × List (Fin 256))) (hfit : L.no + L.nw ≤ p.length)
    (hspan : L.A.span < 256 ^ L.nw) (hdisj : TagsDisjoint L.V L.A.nicheStart L.A.span)
    (hin : ∀ w ∈ ws, w.1 + w.2.length ≤ p.length)
    (hpw : ws.Pairwise (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1))
    (hws : ∀ w ∈ ws, L.DisjointFromNiche w.1 w.2.length) :
    (∀ v, L.Encodable v → ∃ q,
      run sem L (writesOf ws ++ [.setDisc v, .readDisc]) (p, []) = some (q, [v]) ∧
        L.readNiche q = some (L.A.tagOf (v - L.A.first)) ∧
        ∀ w ∈ ws, readBytes q w.1 w.2.length = some w.2) ∧
    (∀ x : Pat L.nw, L.V x = true → ∃ q,
      run sem L (writesOf ws ++ [.write L.no (leBytes L.nw x.val), .setDisc L.E.u, .readDisc])
        (p, []) = some (q, [L.E.u]) ∧
        L.readNiche q = some x ∧
        ∀ w ∈ ws, readBytes q w.1 w.2.length = some w.2) := by
  obtain ⟨q0, hrun0, hq0len, hreads0⟩ := run_writesOf sem L ws p [] hin hpw
  have hfit0 : L.no + L.nw ≤ q0.length := by rw [hq0len]; exact hfit
  refine ⟨fun v hv => ?_, fun x hx => ?_⟩
  · let t := L.A.tagOf (v - L.A.first)
    let q := L.writeNiche q0 t
    have hvu : v ≠ L.E.u := hv.1.2.1
    have hrn : L.readNiche q = some t := readNiche_writeNiche L q0 t hfit0
    have hrd : L.readDisc q = some v := by
      unfold OpLayout.readDisc
      rw [hrn]
      have hr : v - L.A.first ≤ L.A.span := by have := hv.2.1; have := hv.2.2; omega
      have hoff : offset L.A.nicheStart t = v - L.A.first :=
        offset_wrapAdd_of_lt L.A.nicheStart (by omega)
      have hadd : L.A.first + (v - L.A.first) = v := by have := hv.2.1; omega
      simp only [genLayout, hoff, hr, ↓reduceIte, hadd, hv.1, ↓reduceDIte, Option.map_some]
    have hsd : setDisc sem L v q0 = some q := by
      unfold setDisc
      simp only [hvu, ↓reduceIte, hv, hfit0]
      rfl
    refine ⟨q, ?_, hrn, fun w hw => ?_⟩
    · rw [run_append, hrun0]
      simp only [Option.bind_some, run, stepOp, hsd, Option.map_some, hrd, List.nil_append]
    · have hdis : L.no + (leBytes L.nw t.val).length ≤ w.1 ∨ w.1 + w.2.length ≤ L.no := by
        rw [leBytes_length]; exact (hws w hw).symm
      change readBytes (writeBytes q0 L.no (leBytes L.nw t.val)) w.1 w.2.length = some w.2
      rw [readBytes_writeBytes_disjoint q0 w.1 w.2.length L.no _ hdis]
      exact hreads0 w hw
  · let q := L.writeNiche q0 x
    have hrn : L.readNiche q = some x := readNiche_writeNiche L q0 x hfit0
    have hrd : L.readDisc q = some L.E.u := by
      unfold OpLayout.readDisc
      rw [hrn]
      have hnot : ¬ offset L.A.nicheStart x ≤ L.A.span := by
        intro hle; have hf := hdisj _ hle; rw [wrapAdd_offset, hx] at hf; cases hf
      simp [genLayout, hnot, hx]
    have hsd : setDisc sem L L.E.u q = some q := by
      unfold setDisc; simp only [↓reduceIte]
      cases sem with
      | erased => rfl
      | operational => simp [hrd]
    have hwfit : L.no + (leBytes L.nw x.val).length ≤ q0.length := by
      rw [leBytes_length]; exact hfit0
    refine ⟨q, ?_, hrn, fun w hw => ?_⟩
    · rw [run_append, hrun0]
      simp only [Option.bind_some, run, stepOp, hwfit, ↓reduceIte]
      change (((setDisc sem L L.E.u q).map (fun p' => (p', []))).bind
        (fun s => ((L.readDisc s.1).map (fun i => (s.1, s.2 ++ [i]))).bind some)) = some (q, [L.E.u])
      rw [hsd, Option.map_some, Option.bind_some, hrd]; rfl
    · have hdis : L.no + (leBytes L.nw x.val).length ≤ w.1 ∨ w.1 + w.2.length ≤ L.no := by
        rw [leBytes_length]; exact (hws w hw).symm
      change readBytes (writeBytes q0 L.no (leBytes L.nw x.val)) w.1 w.2.length = some w.2
      rw [readBytes_writeBytes_disjoint q0 w.1 w.2.length L.no _ hdis]
      exact hreads0 w hw

end Toy.WrapNiche
