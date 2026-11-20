import Toy.ByteSL.Commands
import Toy.ByteSL.Transmute

/-!
# Positive and negative examples for every definition of this package

The copied byte-representation vocabulary (`AByte`, `Bytes`, `Rep`, the three laws, `IntoBytes`,
`FromBytes`, `transmute`, …) has its examples in `Toy.ByteSL.ReprExamples` (copied with it).
This module covers the definitions introduced or copied for the separation-logic layer.
-/

namespace Toy.ByteSL

open SepStruct

/-! ## A deliberately lawless separation structure (for negative examples of the laws) -/

/-- A wrapper around `Nat` with `disj a b := a ≤ b` and `union a b := a`; it violates symmetry,
commutativity, associativity and the unit law for `0`. -/
structure Lawless where
  /-- The underlying number. -/
  val : Nat

instance : SepStruct Lawless where
  disj a b := a.val ≤ b.val
  union a _ := a

/-! ## Laws of separation structures -/

theorem ex_disjSymm_pos : DisjSymm (BHeap Byte) := (byteHeap_isSepAlgebra Byte).disjSymm
theorem ex_disjSymm_neg : ¬ DisjSymm Lawless := fun h =>
  absurd (h ⟨0⟩ ⟨1⟩ (by decide : (0 : Nat) ≤ 1)) (by decide : ¬ (1 : Nat) ≤ 0)

theorem ex_unionComm_pos : UnionComm (BHeap Byte) := (byteHeap_isSepAlgebra Byte).comm
theorem ex_unionComm_neg : ¬ UnionComm Lawless := fun h => by
  have := congrArg Lawless.val (h ⟨0⟩ ⟨1⟩ (by decide : (0 : Nat) ≤ 1))
  exact absurd this (by decide)

theorem ex_unionAssoc_pos : UnionAssoc (BHeap Byte) := (byteHeap_isSepAlgebra Byte).assoc
theorem ex_unionAssoc_neg : ¬ UnionAssoc Lawless := fun h =>
  absurd (h ⟨0⟩ ⟨5⟩ ⟨1⟩ (by decide : (0 : Nat) ≤ 5) (by decide : (0 : Nat) ≤ 1)).1
    (by decide : ¬ (5 : Nat) ≤ 1)

theorem ex_unitLaw_pos : UnitLaw (Heap.emp : BHeap Byte) := (byteHeap_isSepAlgebra Byte).unit
theorem ex_unitLaw_neg : ¬ UnitLaw (⟨0⟩ : Lawless) := fun h => by
  have := congrArg Lawless.val (h ⟨1⟩).2
  exact absurd this (by decide)

theorem ex_rightCancel_pos : RightCancel Lawless := fun _ _ _ _ _ he => he
theorem ex_rightCancel_neg : ¬ RightCancel (BHeap Byte) :=
  (byteHeap_isSepAlgebra_and_not_rightCancel Byte).2.1

theorem ex_isSepAlgebra_pos : IsSepAlgebra (BHeap Byte) Heap.emp := byteHeap_isSepAlgebra Byte
theorem ex_isSepAlgebra_neg : ¬ IsSepAlgebra Lawless ⟨0⟩ := fun h => ex_disjSymm_neg h.disjSymm

/-! ## Heaps, cells, disjointness, union -/

theorem ex_heap_set_pos :
    ((Heap.emp : BHeap Byte).set 3 (some ⟨.full, .init 1⟩)).val 3 = some ⟨.full, .init 1⟩ := rfl
theorem ex_heap_set_neg :
    ((Heap.emp : BHeap Byte).set 3 (some ⟨.full, .init 1⟩)).val 2 = none := rfl

theorem ex_disj_pos :
    disj (Heap.block .ro 0 (#v[.init 1] : Bytes Byte 1)) (Heap.block .ro 0 #v[.init 1]) ∧
      disj (Heap.block .full 0 (#v[.init 1] : Bytes Byte 1)) (Heap.block .full 1 #v[.init 2]) := by
  refine ⟨disj_block_ro_self 0 _, disj_of_forall_none fun k => ?_⟩
  rcases k with _ | k
  · right; decide
  · left; exact Heap.block_val_of_ge _ _ _ (by omega)

theorem ex_disj_neg :
    ¬ disj (Heap.block .full 0 (#v[.init 1] : Bytes Byte 1)) (Heap.block .ro 0 #v[.init 1]) ∧
      ¬ disj (Heap.block .ro 0 (#v[.init 1] : Bytes Byte 1)) (Heap.block .ro 0 #v[.init 2]) := by
  constructor
  · intro h
    exact absurd (h 0 ⟨.full, .init 1⟩ ⟨.ro, .init 1⟩ (by decide) (by decide)).1 (by decide)
  · intro h
    exact absurd (h 0 ⟨.ro, .init 1⟩ ⟨.ro, .init 2⟩ (by decide) (by decide)).2 (by decide)

theorem ex_join_pos :
    (union (Heap.block .full 0 (#v[.init 1] : Bytes Byte 1))
      (Heap.block .full 1 (#v[.init 2] : Bytes Byte 1))).val 1 = some ⟨.full, .init 2⟩ := by
  decide

/-- Union is left-biased off its intended domain (it is only meaningful on disjoint heaps). -/
theorem ex_join_neg :
    union (Heap.block .full 0 (#v[.init 1] : Bytes Byte 1)) (Heap.block .full 0 #v[.init 2]) ≠
      Heap.block .full 0 #v[.init 2] := fun h => by
  have := congrArg (fun h : BHeap Byte => h.val 0) h
  exact absurd this (by decide)

/-! ## Blocks, byte points-to, the heap byte-definedness order, byte-definedness upward closure -/

theorem ex_block_pos :
    (Heap.block .full 4 (#v[.init 1, .uninit] : Bytes Byte 2)).val 5 = some ⟨.full, .uninit⟩ := by
  decide
theorem ex_block_neg :
    (Heap.block .full 4 (#v[.init 1, .uninit] : Bytes Byte 2)).val 6 = none := by decide

theorem ex_blockOn_pos :
    (Heap.blockOn .full 0 (#v[.init 1, .init 9, .init 2, .init 3] : Bytes Byte 4)
      layoutS.isPad).val 1 = some ⟨.full, .init 9⟩ := by decide
theorem ex_blockOn_neg :
    (Heap.blockOn .full 0 (#v[.init 1, .init 9, .init 2, .init 3] : Bytes Byte 4)
      layoutS.isPad).val 0 = none := by decide

theorem ex_ptsB_pos : ptsB .full 0 (#v[.init 1] : Bytes Byte 1) (Heap.block .full 0 #v[.init 1]) :=
  rfl
theorem ex_ptsB_neg :
    ¬ ptsB .full 0 (#v[.init 1] : Bytes Byte 1) (Heap.block .ro 0 #v[.init 1]) ∧
      ¬ ptsB .full 0 (#v[.init 1] : Bytes Byte 1) Heap.emp := by
  constructor
  · intro h
    exact absurd (Heap.block_perm_inj (by decide) h) (by decide)
  · intro h
    have := congrArg (fun h : BHeap Byte => h.val 0) h
    exact absurd this (by decide)

theorem ex_heapByteLe_pos :
    HeapByteLe (Heap.block .full 0 (#v[.uninit] : Bytes Byte 1)) (Heap.block .full 0 #v[.init 1]) :=
  heapByteLe_block_of_le .full 0 (Bytes.le_one trivial)

theorem ex_heapByteLe_neg :
    ¬ HeapByteLe (Heap.block .full 0 (#v[.init 1] : Bytes Byte 1)) (Heap.block .full 0 #v[.uninit]) ∧
      ¬ HeapByteLe (Heap.block .full 0 (#v[.uninit] : Bytes Byte 1)) (Heap.block .ro 0 #v[.uninit]) ∧
      ¬ HeapByteLe (Heap.emp : BHeap Byte) (Heap.block .full 0 #v[.uninit]) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · exact absurd (le_of_heapByteLe_block h (i := 0) (by decide)) (by decide)
  · exact absurd ((h 0).2 ⟨.full, .uninit⟩ ⟨.ro, .uninit⟩ (by decide) (by decide)).1 (by decide)
  · exact absurd ((h 0).1.mp rfl) (by decide)

theorem ex_byteUpClose_pos :
    byteUpClose (ptsEnc .full u8PadRep 0 5)
      (Heap.block .full 0 (#v[.init 5, .init 7] : Bytes Byte 2)) :=
  ptsDec_eq_byteUpClose_nonvacuous.2.2.2.1

theorem ex_byteUpClose_neg :
    ¬ byteUpClose (ptsEnc .full u8PadRep 0 5)
      (Heap.block .full 0 (#v[.init 6, .init 7] : Bytes Byte 2)) := by
  rintro ⟨h₀, hh₀, hle⟩
  have hh₀' : h₀ = Heap.block .full 0 (u8PadRep.encode 5) := hh₀
  subst hh₀'
  exact absurd (le_of_heapByteLe_block hle (i := 0) (by decide)) (by decide)

/-! ## Typed points-to -/

theorem ex_ptsEnc_pos :
    ptsEnc .full u8PadRep 0 5 (Heap.block .full 0 (#v[.init 5, .uninit] : Bytes Byte 2)) := rfl
theorem ex_ptsEnc_neg :
    ¬ ptsEnc .full u8PadRep 0 5 (Heap.block .full 0 (#v[.init 5, .init 7] : Bytes Byte 2)) :=
  u8PadRep_laws_and_ptsDec_not_ptsEnc_of_init_padding.2.2.2.2

theorem ex_ptsDec_pos :
    ptsDec .full u8PadRep 0 5 (Heap.block .full 0 (#v[.init 5, .init 7] : Bytes Byte 2)) :=
  ⟨_, rfl, rfl⟩
theorem ex_ptsDec_neg :
    ¬ ptsDec .full u8PadRep 0 5 (Heap.block .full 0 (#v[.uninit, .init 5] : Bytes Byte 2)) := by
  rintro ⟨x, hx, hd⟩
  have hx' := Heap.block_inj hx
  subst hx'
  cases hd

/-! ## Struct layout, struct representation, padding assertions -/

theorem ex_layout2_pos : layoutS.size = 4 ∧ layoutS.off₂ = 2 := ⟨rfl, rfl⟩
/-- No layout places field 2 beyond the end of the struct. -/
theorem ex_layout2_neg : ¬ ∃ L : Layout2, L.size = 4 ∧ L.off₂ = 3 ∧ L.size₂ = 2 := by
  rintro ⟨L, h1, h2, h3⟩
  have := L.fits
  omega

theorem ex_nonOverlap_pos : layoutS.NonOverlap := layoutS_nonOverlap
/-- The union-like layout `layoutU` (both fields at offset 0) is overlapping. -/
theorem ex_nonOverlap_neg : ¬ layoutU.NonOverlap := ptsDec_struct_split_tight_hL.1

theorem ex_isPad_pos : layoutS.isPad 1 = true := by decide
theorem ex_isPad_neg : layoutS.isPad 0 = false ∧ layoutS.isPad 2 = false ∧ layoutS.isPad 3 = false ∧
    layoutS.isPad 4 = false ∧ layoutS.isPad 100 = false := by
  decide

theorem ex_slice_pos :
    (Bytes.slice (#v[.init 1, .init 9, .init 2, .init 3] : Bytes Byte 4) 2 2 (by decide)) =
      #v[.init 2, .init 3] := by decide
theorem ex_slice_neg :
    (Bytes.slice (#v[.init 1, .init 9, .init 2, .init 3] : Bytes Byte 4) 2 2 (by decide)) ≠
      #v[.init 9, .init 2] := by decide

theorem ex_structEncode_pos :
    structS.encode (1, (2, 3)) = #v[.init 1, .uninit, .init 2, .init 3] := by decide
theorem ex_structEncode_neg :
    structS.encode (1, (2, 3)) ≠ #v[.init 1, .init 0, .init 2, .init 3] := by decide

theorem ex_structDecode_pos :
    structS.decode #v[.init 1, .init 9, .init 2, .init 3] = some (1, (2, 3)) := by decide
theorem ex_structDecode_neg :
    structS.decode #v[.init 1, .init 9, .uninit, .init 3] = none := by decide

theorem ex_padAny_pos :
    padAny .full layoutS 0 (Heap.blockOn .full 0
      (#v[.init 1, .init 9, .init 2, .init 3] : Bytes Byte 4) layoutS.isPad) := ⟨_, rfl⟩
theorem ex_padAny_neg :
    ¬ padAny .full layoutS 0 (Heap.block .full 0 (#v[.init 1] : Bytes Byte 1)) := by
  rintro ⟨y, hy⟩
  have e := congrArg (fun h : BHeap Byte => h.val 0) hy
  have r : (Heap.blockOn .full 0 y layoutS.isPad).val 0 = none := by
    rw [Heap.blockOn_val]
    simp [Layout2.isPad]
  rw [r] at e
  exact absurd e (by decide)

theorem ex_padUninit_pos :
    padUninit .full layoutS 0 (Heap.blockOn .full 0
      (#v[.init 1, .uninit, .init 2, .init 3] : Bytes Byte 4) layoutS.isPad) := by
  apply Heap.ext
  intro k
  rcases k with _ | _ | _ | _ | k
  · decide
  · decide
  · decide
  · decide
  · rw [Heap.blockOn_val_of_ge _ _ _ _ (show 0 + layoutS.size ≤ k + 1 + 1 + 1 + 1 by
        show 0 + 4 ≤ _; omega), Heap.blockOn_val_of_ge _ _ _ _ (show 0 + 4 ≤ k + 1 + 1 + 1 + 1 by omega)]
theorem ex_padUninit_neg :
    ¬ padUninit .full layoutS 0 (Heap.blockOn .full 0
      (#v[.init 1, .init 9, .init 2, .init 3] : Bytes Byte 4) layoutS.isPad) := by
  intro h
  have := congrArg (fun h : BHeap Byte => h.val 1) h
  exact absurd this (by decide)

/-! ## The non-monotone `FromBytes` representation used as a view-change target -/

theorem ex_nonMonoBoolRep_pos :
    nonMonoBoolRep.decode #v[.uninit] = some false ∧ nonMonoBoolRep.decode #v[.init 7] = some true ∧
      nonMonoBoolRep.FromBytes :=
  ⟨rfl, rfl, nonMonoBoolRep_fromBytes⟩
/-- `nonMonoBoolRep` is not `DecodeMono`, and its encoding of `false` does not decode back to
`false`. -/
theorem ex_nonMonoBoolRep_neg :
    ¬ nonMonoBoolRep.DecodeMono ∧ nonMonoBoolRep.decode (nonMonoBoolRep.encode false) ≠ some false :=
  ⟨nonMonoBoolRep_not_decodeMono, by decide⟩

/-! ## Reading and writing cells -/

theorem ex_readBytes_pos : readBytes hSrc5 0 1 = some #v[.init 5] := by decide
theorem ex_readBytes_neg : readBytes hSrc5 0 2 = none := by decide

theorem ex_readLoose_pos : readLoose hSrc5 0 2 = #v[.init 5, .uninit] := by decide
theorem ex_readLoose_neg : readLoose hSrc5 0 2 ≠ #v[.init 5, .init 0] := by decide

theorem ex_ownsFull_pos : OwnsFull hDst 1 1 := ownsFull_hDst
theorem ex_ownsFull_neg : ¬ OwnsFull hRO1 0 1 := fun h => by
  obtain ⟨b, hb⟩ := h 0 (by decide)
  have : hRO1.val 0 = some ⟨.ro, .init 1⟩ := by decide
  rw [this] at hb
  injection hb with hb
  injection hb with hb
  cases hb

theorem ex_writeBytes_pos :
    (writeBytes hDst 1 (#v[.init 7] : Bytes Byte 1)).val 1 = some ⟨.full, .init 7⟩ := by decide
theorem ex_writeBytes_neg :
    (writeBytes hDst 1 (#v[.init 7] : Bytes Byte 1)).val 0 = none := by decide

/-! ## Commands: admitted and excluded transitions -/

theorem ex_skip_pos : (skip : Cmd (BHeap Byte)) hDst (.ok hDst) := rfl
theorem ex_skip_neg : ¬ (skip : Cmd (BHeap Byte)) hDst .fault := fun h => by cases h

theorem ex_bstore_pos : bstore (D := Byte) 1 (.init 7) hDst (.ok (writeBytes hDst 1 #v[.init 7])) :=
  byte_and_typed_commands_nonvacuous.1
/-- A byte store faults on a read-only cell. -/
theorem ex_bstore_neg : bstore (D := Byte) 0 (.init 7) hRO1 .fault :=
  Or.inl ⟨ex_ownsFull_neg, rfl⟩

theorem ex_bcopy_pos : bcopy (D := Byte) 0 1 (union hDst hSrc5)
    (.ok (writeBytes (union hDst hSrc5) 1 #v[.init 5])) := byte_and_typed_commands_nonvacuous.2.1
/-- A byte copy faults when the source is not owned. -/
theorem ex_bcopy_neg : bcopy (D := Byte) 0 1 hDst .fault :=
  Or.inl ⟨Or.inl (by decide), rfl⟩

theorem ex_tstore_pos : tstore u8Rep 1 (7 : Byte) hDst (.ok (writeBytes hDst 1 #v[.init 7])) :=
  byte_and_typed_commands_nonvacuous.2.2.1
theorem ex_tstore_neg : tstore u8Rep 0 (7 : Byte) hRO1 .fault := Or.inl ⟨ex_ownsFull_neg, rfl⟩

theorem ex_tcopy_pos : tcopy u8Rep 0 1 (union hDst hSrc5)
    (.ok (writeBytes (union hDst hSrc5) 1 (u8Rep.encode 5))) :=
  byte_and_typed_commands_nonvacuous.2.2.2.1
/-- A typed copy at `bool` faults when the source byte is a niche value. -/
theorem ex_tcopy_neg :
    tcopy boolRep 0 1 (union hDst (Heap.block .full 0 (#v[.init 2] : Bytes Byte 1))) .fault := by
  refine Or.inl ⟨Or.inl ?_, rfl⟩
  rintro ⟨x, v, hx, hv⟩
  have : readBytes (union hDst (Heap.block .full 0 (#v[.init 2] : Bytes Byte 1))) 0 1 =
      some #v[.init 2] := by decide
  rw [this] at hx
  cases hx
  revert hv
  cases v <;> decide

theorem ex_tload_pos : tload u8Rep 0 hSrc5 (.ok hSrc5) := byte_and_typed_commands_nonvacuous.2.2.2.2
theorem ex_tload_neg : tload u8Rep 1 hSrc5 .fault := by
  refine Or.inl ⟨?_, rfl⟩
  rintro ⟨x, v, hx, _⟩
  have : readBytes hSrc5 1 1 = none := by decide
  rw [this] at hx
  cases hx

theorem ex_bcopyLoose_pos : bcopyLoose (D := Byte) 0 1 hDst
    (.ok (writeBytes hDst 1 (readLoose hDst 0 1))) := Or.inr ⟨ownsFull_hDst, rfl⟩
theorem ex_bcopyLoose_neg : bcopyLoose (D := Byte) 0 0 hRO1 .fault :=
  Or.inl ⟨ex_ownsFull_neg, rfl⟩

theorem ex_tcopyLoose_pos :
    tcopyLoose u8PadRep 0 2
      (union (Heap.block .full 0 (#v[.init 5] : Bytes Byte 1))
        (Heap.block .full 2 (#v[.uninit, .uninit] : Bytes Byte 2)))
      (.ok (writeBytes (union (Heap.block .full 0 (#v[.init 5] : Bytes Byte 1))
        (Heap.block .full 2 (#v[.uninit, .uninit] : Bytes Byte 2))) 2 (u8PadRep.encode 5))) :=
  tcopyLoose_local_nonvacuous.2
/-- The loose typed copy still faults when the bytes it reads do not decode. -/
theorem ex_tcopyLoose_neg : tcopyLoose u8Rep 0 1 hDst .fault := by
  refine Or.inl ⟨Or.inl ?_, rfl⟩
  rintro ⟨v, hv⟩
  have : readLoose hDst 0 1 = #v[.uninit] := by decide
  rw [this] at hv
  cases hv

theorem ex_bstoreShared_pos :
    bstoreShared (D := Byte) 0 (.init 2) hRO1 (.ok (hRO1.set 0 (some ⟨.ro, .init 2⟩))) :=
  Or.inr ⟨⟨.ro, .init 1⟩, by decide, rfl⟩
theorem ex_bstoreShared_neg : bstoreShared (D := Byte) 1 (.init 2) hRO1 .fault :=
  Or.inl ⟨by decide, rfl⟩

/-! ## Separating conjunction, safety, triples, locality -/

theorem ex_sep_pos :
    sep (ptsB .full 1 (#v[.uninit] : Bytes Byte 1)) (ptsB .full 0 (#v[.init 5] : Bytes Byte 1))
      (union hDst hSrc5) :=
  ⟨hDst, hSrc5, hDst_hSrc5_disj, rfl, rfl, rfl⟩
theorem ex_sep_neg :
    ¬ sep (ptsB .full 0 (#v[.init 5] : Bytes Byte 1)) (ptsB .full 0 (#v[.init 5] : Bytes Byte 1))
      hSrc5 := by
  rintro ⟨h₁, h₂, hd, -, hp1, hp2⟩
  have hp1' : h₁ = hSrc5 := hp1
  have hp2' : h₂ = hSrc5 := hp2
  subst hp1' hp2'
  exact absurd (hd 0 ⟨.full, .init 5⟩ ⟨.full, .init 5⟩ (by decide) (by decide)).1 (by decide)

theorem ex_safe_pos : Safe (bstore (D := Byte) 1 (.init 7)) hDst := by
  rintro (⟨hf, _⟩ | ⟨_, ho⟩)
  · exact hf ownsFull_hDst
  · cases ho
theorem ex_safe_neg : ¬ Safe (bstore (D := Byte) 0 (.init 7)) hRO1 := fun h => h ex_bstore_neg

theorem ex_triple_pos :
    Triple (ptsB .full 0 (#v[.uninit] : Bytes Byte 1)) (bstore (D := Byte) 0 (.init 1))
      (ptsB .full 0 (#v[.init 1] : Bytes Byte 1)) := byteHeap_frameRule_nonvacuous
theorem ex_triple_neg :
    ¬ Triple (ptsB .ro 0 (#v[.init 1] : Bytes Byte 1)) (bstore (D := Byte) 0 (.init 7))
      (fun _ => True) := fun h => (h hRO1 rfl).1 ex_bstore_neg

theorem skip_local {S : Type} [SepStruct S] : Local (skip : Cmd S) := by
  refine ⟨fun h h' _ _ hf => (by cases hf), fun h h' h'' hd _ hr => ?_⟩
  cases hr
  exact ⟨h, rfl, hd, rfl⟩

theorem ex_safetyMono_pos : SafetyMono (skip : Cmd (BHeap Byte)) := skip_local.1
theorem ex_safetyMono_neg : ¬ SafetyMono (tcopyLoose exactUnitRep 0 1) :=
  tcopyLoose_exactUnitRep_not_safetyMono

theorem ex_frameProp_pos : FrameProp (skip : Cmd (BHeap Byte)) := skip_local.2
theorem ex_frameProp_neg : ¬ FrameProp (bcopyLoose (D := Byte) 0 1) :=
  bcopyLoose_safetyMono_and_not_frameProp.2.1

theorem ex_local_pos : Local (skip : Cmd (BHeap Byte)) := skip_local
theorem ex_local_neg : ¬ Local (bstoreShared (D := Byte) 0 (.init 2)) := fun h =>
  bstoreShared_safetyMono_and_not_frameProp.2.1 h.2

theorem skip_frameRuleSound {S : Type} [SepStruct S] : FrameRuleSound (skip : Cmd S) := by
  intro P Q R ht h ⟨h₁, h₂, hd, he, hP, hR⟩
  refine ⟨fun hf => (by cases hf), fun h' hr => ?_⟩
  cases hr
  obtain ⟨_, hq⟩ := ht h₁ hP
  exact ⟨h₁, h₂, hd, he, hq h₁ rfl, hR⟩

theorem ex_frameRuleSound_pos : FrameRuleSound (skip : Cmd (BHeap Byte)) := skip_frameRuleSound
theorem ex_frameRuleSound_neg : ¬ FrameRuleSound (bcopyLoose (D := Byte) 0 1) :=
  bcopyLoose_safetyMono_and_not_frameProp.2.2.2.2

end Toy.ByteSL
