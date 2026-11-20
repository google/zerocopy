import ToyTransmute.Tools

/-!
# Positive and negative examples for every definition (all fully proved)

Each core definition is tested on an instance it is meant to admit and an instance it is
meant to reject. The fixtures `boolV`, `boolV'`, `byteV`, `neverV`, `zeroV`, `twoV` are
one-byte types over `Fin 256`.
-/

namespace Toy.Transmute

/-! ## Fixture facts -/

theorem boolV_byteSeq_zero : boolV (byteSeq 0) := Or.inl rfl

theorem boolV_byteSeq_one : boolV (byteSeq 1) := Or.inr rfl

/-- `2` is not a valid `bool` byte. -/
theorem not_boolV_byteSeq_two : ¬ boolV (byteSeq 2) := by
  unfold boolV byteSeq; decide

theorem boolV'_byteSeq_one : boolV' (byteSeq 1) := by
  unfold boolV' byteSeq; decide

theorem not_boolV'_byteSeq_two : ¬ boolV' (byteSeq 2) := by
  unfold boolV' byteSeq; decide

/-- Every byte sequence is a valid raw byte (intended totality; `byteV` has no negative
example by design). -/
theorem byteV_total (m : Bytes (Fin 256) 1) : byteV m := trivial

/-- No byte sequence is valid for `neverV` (intended emptiness; `neverV` has no positive
example by design). -/
theorem neverV_empty (m : Bytes (Fin 256) 1) : ¬ neverV m := id

theorem zeroV_byteSeq_zero : zeroV (byteSeq 0) := rfl

theorem not_zeroV_byteSeq_one : ¬ zeroV (byteSeq 1) := by
  unfold zeroV byteSeq; decide

theorem twoV_byteSeq_two : twoV (byteSeq 2) := rfl

theorem not_twoV_byteSeq_zero : ¬ twoV (byteSeq 0) := by
  unfold twoV byteSeq; decide

/-! ## `Includes` -/

/-- Positive: every `bool` bit pattern is a byte bit pattern. -/
theorem includes_boolV_byteV : Includes boolV byteV := fun _ _ => trivial

/-- Negative: the byte `2` is not a `bool` bit pattern. -/
theorem not_includes_byteV_boolV : ¬ Includes byteV boolV :=
  fun h => not_boolV_byteSeq_two (h _ trivial)

/-! ## `ValidityEq` -/

/-- Positive: `boolV` and `boolV'` are written differently but accept the same bytes. -/
theorem validityEq_boolV_boolV' : ValidityEq boolV boolV' := by
  intro m
  unfold boolV boolV'
  constructor
  · rintro (h | h) <;> simp [h]
  · intro h
    have : (m 0).val = 0 ∨ (m 0).val = 1 := by omega
    rcases this with h0 | h1
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h1)

/-- Negative: `bool` and raw byte validity differ (on the byte `2`). -/
theorem not_validityEq_boolV_byteV : ¬ ValidityEq boolV byteV :=
  fun h => not_boolV_byteSeq_two ((h _).2 trivial)

/-! ## `Satisfiable` -/

/-- Positive: `bool` is inhabited. -/
theorem satisfiable_boolV : Satisfiable boolV := ⟨_, boolV_byteSeq_zero⟩

/-- Negative: the empty type is not inhabited. -/
theorem not_satisfiable_neverV : ¬ Satisfiable neverV := fun ⟨_, h⟩ => h

/-! ## `Side.ty` -/

/-- Positive: the destination view is typed at the destination type. -/
theorem side_ty_dst_example : Side.ty boolV byteV .dst = byteV := rfl

/-- Negative: the source view is not typed at the destination type here. -/
theorem side_ty_src_ne_example : Side.ty boolV byteV .src ≠ byteV := by
  intro h
  have h2 : Side.ty boolV byteV .src (byteSeq 2) = byteV (byteSeq 2) := congrFun h (byteSeq 2)
  have h3 : boolV (byteSeq 2) = True := h2
  exact not_boolV_byteSeq_two (h3 ▸ trivial)

/-! ## `Op.WellTyped` -/

/-- Positive: writing the byte `2` through a raw-byte view is well typed. -/
theorem wellTyped_write_dst_two : (Op.write .dst (byteSeq 2)).WellTyped boolV byteV :=
  trivial

/-- Negative: writing the byte `2` through a `bool` view is not well typed. -/
theorem not_wellTyped_write_src_two : ¬ (Op.write .src (byteSeq 2)).WellTyped boolV byteV :=
  not_boolV_byteSeq_two

/-! ## `NoInvalidRead` -/

/-- Positive: reading a `bool` `1` through both views observes valid bytes. -/
theorem noInvalidRead_example :
    NoInvalidRead boolV byteV (byteSeq 1) [.read .src, .read .dst] :=
  ⟨boolV_byteSeq_one, trivial, trivial⟩

/-- Negative: writing `2` through the byte view, then reading through the `bool` view,
observes an invalid `bool`. -/
theorem not_noInvalidRead_example :
    ¬ NoInvalidRead boolV byteV (byteSeq 1) [.write .dst (byteSeq 2), .read .src] :=
  fun h => not_boolV_byteSeq_two h.1

/-! ## The disciplines -/

/-- Positive: the destination of a value transmute may read and write. -/
theorem valueProtocol_example :
    (valueProtocol : Protocol (Fin 256) 1)
      [.read .dst, .write .dst (byteSeq 2), .read .dst] := by
  intro op hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;> rfl

/-- Negative: the moved-from source may not act during a value transmute. -/
theorem not_valueProtocol_example :
    ¬ (valueProtocol : Protocol (Fin 256) 1) [.read .src] := by
  intro h
  have := h (.read .src) (by simp)
  simp [Op.side] at this

/-- Positive: interleaved reads through both views are a shared-cast run. -/
theorem sharedProtocol_example :
    (sharedProtocol : Protocol (Fin 256) 1) [.read .src, .read .dst, .read .src] := by
  intro op hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;> trivial

/-- Negative: no write is permitted under a shared cast without interior mutability. -/
theorem not_sharedProtocol_example :
    ¬ (sharedProtocol : Protocol (Fin 256) 1) [.write .src (byteSeq 0)] := by
  intro h
  exact h (.write .src (byteSeq 0)) (by simp)

/-- Positive: an exclusive period through the cast view (read, write), then the owner's period
(read, write). -/
theorem mutProtocol_example :
    (mutProtocol : Protocol (Fin 256) 1)
      [.read .dst, .write .dst (byteSeq 2), .read .src, .write .src (byteSeq 0)] := by
  refine ⟨[.read .dst, .write .dst (byteSeq 2)], [.read .src, .write .src (byteSeq 0)],
    rfl, ?_, ?_⟩
  · intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> rfl
  · intro op hop
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with rfl | rfl <;> rfl

/-- Negative: the owner may not act while the mutable cast reference is still to be used.
A run starts when the cast reference is created, so the owner's read here happens before a
later use of the cast view. (Reads by the owner *before* the cast are not part of any run;
they are summarised by the initial contents.) -/
theorem not_mutProtocol_example :
    ¬ (mutProtocol : Protocol (Fin 256) 1) [.read .src, .read .dst] := by
  rintro ⟨d, a, h, hd, ha⟩
  cases d with
  | nil =>
    simp only [List.nil_append] at h
    have := ha (.read .dst) (by simp [← h])
    simp [Op.side] at this
  | cons x d =>
    simp only [List.cons_append, List.cons.injEq] at h
    have := hd x (by simp)
    rw [← h.1] at this
    simp [Op.side] at this

/-- Positive: with both write flags set, both views may write, interleaved with reads. -/
theorem sharedIMProtocol_example :
    (sharedIMProtocol true true : Protocol (Fin 256) 1)
      [.write .src (byteSeq 1), .write .dst (byteSeq 2), .read .src] := by
  intro op hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl <;> trivial

/-- Negative: with only the source side writable, a write through the cast view is not
permitted. -/
theorem not_sharedIMProtocol_example :
    ¬ (sharedIMProtocol true false : Protocol (Fin 256) 1) [.write .dst (byteSeq 2)] := by
  intro h
  have := h (.write .dst (byteSeq 2)) (by simp)
  simp [Op.PermittedIM] at this

/-- Positive: `Op.PermittedIM` permits a source write when the source flag is set. -/
theorem permittedIM_example : (Op.write .src (byteSeq 0) : Op (Fin 256) 1).PermittedIM true false :=
  rfl

/-- Negative: `Op.PermittedIM` rejects a source write when the source flag is unset. -/
theorem not_permittedIM_example :
    ¬ (Op.write .src (byteSeq 0) : Op (Fin 256) 1).PermittedIM false true := by
  simp [Op.PermittedIM]

/-! ## Soundness notions on fixtures -/

/-- `bool → byte` by value is sound (invariant: any bytes). -/
theorem valueSound_boolV_byteV : ValueSound boolV byteV :=
  valueSound_of_invariant byteV (fun _ _ => trivial) (fun _ h => h) (fun _ h => h)

/-- `byte → bool` by value is unsound: transmuting the byte `2`. -/
theorem not_valueSound_byteV_boolV : ¬ ValueSound byteV boolV :=
  not_sound_of_read_dst valueProtocol_readDst (m := byteSeq 2) trivial not_boolV_byteSeq_two

/-- `&bool → &byte` is sound (invariant: `bool`). -/
theorem sharedSound_boolV_byteV : SharedSound boolV byteV :=
  sharedSound_of_invariant boolV (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)

/-- `&byte → &bool` is unsound: reading the byte `2` as a `bool`. -/
theorem not_sharedSound_byteV_boolV : ¬ SharedSound byteV boolV :=
  not_sound_of_read_dst sharedProtocol_readDst (m := byteSeq 2) trivial not_boolV_byteSeq_two

/-- `&mut bool → &mut bool'` (same validity, different definition) is sound. -/
theorem mutSound_boolV_boolV' : MutSound boolV boolV' :=
  sound_of_validityEq _ validityEq_boolV_boolV'

/-- `&mut bool' → &mut bool` is sound. -/
theorem mutSound_boolV'_boolV : MutSound boolV' boolV :=
  sound_of_validityEq _ (fun m => (validityEq_boolV_boolV' m).symm)

/-- `&mut bool → &mut byte` is unsound: write `2` through the byte view, then read the
`bool`. -/
theorem not_mutSound_boolV_byteV : ¬ MutSound boolV byteV :=
  not_sound_of_write_dst_read_src (mutProtocol_writeDstReadSrc (byteSeq 2)) (m := byteSeq 0)
    boolV_byteSeq_zero trivial not_boolV_byteSeq_two

/-- `&mut byte → &mut bool` is unsound: read the byte `2` through the `bool` view. -/
theorem not_mutSound_byteV_boolV : ¬ MutSound byteV boolV :=
  not_sound_of_read_dst mutProtocol_readDst (m := byteSeq 2) trivial not_boolV_byteSeq_two

/-- With both sides writable, `bool ↔ bool'` is sound. -/
theorem sharedIMSound_boolV_boolV' (srcWrites dstWrites : Bool) :
    SharedIMSound srcWrites dstWrites boolV boolV' :=
  sound_of_validityEq _ validityEq_boolV_boolV'

/-- With only the source side writable, `bool → byte` is sound (invariant: `bool`). -/
theorem sharedIMSound_true_false_boolV_byteV : SharedIMSound true false boolV byteV :=
  sharedIMSound_of_invariant boolV (fun _ h => h) (fun _ h => h) (fun _ _ => trivial)
    (fun _ _ h => h) (fun h => absurd h (by decide))

/-- With the destination side writable, `bool → byte` is unsound: write `2` through the byte
view, then read the `bool`. -/
theorem not_sharedIMSound_dst_boolV_byteV (srcWrites : Bool) :
    ¬ SharedIMSound srcWrites true boolV byteV :=
  not_sound_of_write_dst_read_src (sharedIMProtocol_writeDstReadSrc srcWrites (byteSeq 2))
    (m := byteSeq 0) boolV_byteSeq_zero trivial not_boolV_byteSeq_two

/-- `Sound`, positive: the shared discipline is sound for `bool → byte`. -/
theorem sound_positive_example : Sound sharedProtocol boolV byteV := sharedSound_boolV_byteV

/-- `Sound`, negative: the mutable discipline is unsound for `bool → byte`. -/
theorem sound_negative_example : ¬ Sound mutProtocol boolV byteV := not_mutSound_boolV_byteV

/-! ## `Validity.meet` and `Validity.join` -/

/-- Positive: the byte `2` is valid for "either `bool` or the byte `2`". -/
theorem join_boolV_twoV_two : (boolV.join twoV) (byteSeq 2) := Or.inr rfl

/-- Negative: the byte `3` is valid for neither. -/
theorem not_join_boolV_twoV_three : ¬ (boolV.join twoV) (byteSeq 3) := by
  unfold Validity.join boolV twoV byteSeq; decide

/-- Positive: the byte `0` is valid for both `bool` and the zero-only type. -/
theorem meet_boolV_zeroV_zero : (boolV.meet zeroV) (byteSeq 0) := ⟨Or.inl rfl, rfl⟩

/-- Negative: the byte `1` is a `bool` but not valid for the zero-only type. -/
theorem not_meet_boolV_zeroV_one : ¬ (boolV.meet zeroV) (byteSeq 1) :=
  fun h => not_zeroV_byteSeq_one h.2

/-- Negative (interleaving): the owner may not act between two uses of the mutable cast
reference. -/
theorem not_mutProtocol_interleaved_example :
    ¬ (mutProtocol : Protocol (Fin 256) 1) [.read .dst, .read .src, .read .dst] := by
  rintro ⟨d, a, h, hd, ha⟩
  match d, h with
  | [], h =>
    simp only [List.nil_append] at h
    have := ha (.read .dst) (by rw [← h]; simp)
    simp [Op.side] at this
  | [x], h =>
    simp only [List.singleton_append, List.cons.injEq] at h
    have := ha (.read .dst) (by rw [← h.2]; simp)
    simp [Op.side] at this
  | x :: y :: d', h =>
    simp only [List.cons_append, List.cons.injEq] at h
    have := hd y (by simp)
    rw [← h.2.1] at this
    simp [Op.side] at this

/-! ## `Op.side`, `Op.IsRead`, `Op.Preserves` -/

/-- Positive: a read through the cast view goes through the destination view. -/
theorem op_side_read_dst_example : (Op.read .dst : Op (Fin 256) 1).side = .dst := rfl

/-- Negative: a write through the original view does not go through the destination view. -/
theorem op_side_write_src_ne_dst_example :
    (Op.write .src (byteSeq 0) : Op (Fin 256) 1).side ≠ .dst := by
  simp [Op.side]

/-- Positive: a read is a read. -/
theorem op_isRead_read_example : (Op.read .src : Op (Fin 256) 1).IsRead := trivial

/-- Negative: a write is not a read. -/
theorem not_op_isRead_write_example :
    ¬ (Op.write .src (byteSeq 0) : Op (Fin 256) 1).IsRead := id

/-- Positive: the region invariant `bool` is compatible with a read through a raw-byte view. -/
theorem op_preserves_read_dst_example :
    (Op.read .dst : Op (Fin 256) 1).Preserves boolV byteV boolV :=
  fun _ _ => trivial

/-- Negative: the region invariant `bool` is not re-established by writing the byte `2`
through the raw-byte view. -/
theorem not_op_preserves_write_dst_example :
    ¬ (Op.write .dst (byteSeq 2) : Op (Fin 256) 1).Preserves boolV byteV boolV :=
  fun h => not_boolV_byteSeq_two (h trivial)

/-! ## Reads are where validity is checked -/

/-- From the byte `2` (not a valid `bool`), the empty run and a run that overwrites before
reading observe no invalid bytes at `bool`, while the run that reads immediately does. This is
why value-transmute soundness is defined by quantifying over all permitted runs. -/
theorem noInvalidRead_unchecked_until_read :
    (valueProtocol : Protocol (Fin 256) 1) [] ∧ ¬ boolV (byteSeq 2) ∧
      NoInvalidRead byteV boolV (byteSeq 2) [] ∧
      NoInvalidRead byteV boolV (byteSeq 2) [.write .dst (byteSeq 0), .read .dst] ∧
      ¬ NoInvalidRead byteV boolV (byteSeq 2) readDst := by
  refine ⟨?_, not_boolV_byteSeq_two, trivial, ⟨boolV_byteSeq_zero, trivial⟩, ?_⟩
  · intro op hop; simp at hop
  · exact fun h => not_boolV_byteSeq_two h.1

/-! ## `CheckedSound` -/

/-- Positive: a checked `&mut byte → &mut bool` cast (check once that the byte is `0` or `1`,
then hand out an ordinary `&mut bool`) is sound: every value written through the `bool` view
is a valid byte. -/
theorem checkedSound_mut_byteV_boolV : CheckedSound mutProtocol byteV boolV :=
  checkedSound_mut_of_invariants boolV byteV (fun _ _ h => h) (fun _ _ => trivial)
    (fun _ h => h) (fun _ h => h) (fun _ _ => trivial) (fun _ _ => trivial)

/-- Negative: a check at cast time does not rescue `&mut bool → &mut byte`: write `2` through
the byte view, then read the `bool`. -/
theorem not_checkedSound_mut_boolV_byteV : ¬ CheckedSound mutProtocol boolV byteV :=
  not_checkedSound_of_write_dst_read_src (mutProtocol_writeDstReadSrc (byteSeq 2))
    (m := byteSeq 0) boolV_byteSeq_zero trivial trivial not_boolV_byteSeq_two

end Toy.Transmute
