/- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -/

module
public import ModelPrelude
import all RustModel
import all ModelPrelude
@[expose] public section

/-!
These laws concern fixed-size numeric abstract-machine bytes and the retained
physical and mathematical decoders. They establish representation admission,
not Rust provenance, ownership, destruction, or an ABI correspondence. In
particular, zero initialization need not preserve input padding in a raw value.
-/

open Aeneas.Std Rust.Storage
namespace AeneasSpecs

/-- Mapping a complete integer representation to an Aeneas scalar retains every
bit pattern. The mathematical provider observes that same scalar. -/
theorem completeUScalar (ty : UScalarTy) :
    RustModel.completeRepresentation (UScalar ty) := by
  intro bytes width initialized
  obtain ⟨word, physical⟩ := integerDecoder_complete (ty.numBits / 8) .little bytes width initialized
  refine ⟨⟨word.cast (AeneasAdapter.unsigned_byte_width ty)⟩, _, ?_, rfl⟩
  change ((integerDecoder (ty.numBits / 8) .little).map _).run bytes = _
  rw [BitDecoder.run_map, physical]
  rfl

theorem completeIScalar (ty : IScalarTy) :
    RustModel.completeRepresentation (IScalar ty) := by
  intro bytes width initialized
  obtain ⟨word, physical⟩ := integerDecoder_complete (ty.numBits / 8) .little bytes width initialized
  refine ⟨⟨word.cast (AeneasAdapter.signed_byte_width ty)⟩, _, ?_, rfl⟩
  change ((integerDecoder (ty.numBits / 8) .little).map _).run bytes = _
  rw [BitDecoder.run_map, physical]
  rfl

theorem zeroUScalar (ty : UScalarTy) : RustModel.zeroRepresentation (UScalar ty) :=
  RustModel.completeRepresentation_zeroRepresentation _ (completeUScalar ty)

theorem zeroIScalar (ty : IScalarTy) : RustModel.zeroRepresentation (IScalar ty) :=
  RustModel.completeRepresentation_zeroRepresentation _ (completeIScalar ty)

theorem completeUnit : RustModel.completeRepresentation Unit := by
  intro bytes width _
  exact ⟨(), (), emptyDecoder_complete () bytes width, rfl⟩

theorem zeroUnit : RustModel.zeroRepresentation Unit :=
  RustModel.completeRepresentation_zeroRepresentation _ completeUnit

/-- Boolean zero admission does not assert that every byte is a boolean. -/
theorem zeroBool : RustModel.zeroRepresentation Bool :=
  ⟨false, false, boolDecoder_run_zero, rfl⟩

/-- Count elements rather than dividing by their width. The same argument
therefore handles empty arrays and zero-sized elements. Each accepted element
also retains the witness from the supplied mathematical decoder. -/
private theorem arrayDecode_model_complete {Raw Model : Type u}
    (element : BitDecoder Raw) (decode : Raw → Option Model) (allowed : AMByte → Prop)
    (complete : ∀ bytes, bytes.length = element.byteSize →
      (∀ byte ∈ bytes, allowed byte) →
      ∃ raw value, element.run bytes = some raw ∧ decode raw = some value)
    (n : Nat) (bytes : List AMByte) (width : bytes.length = n * element.byteSize)
    (all : ∀ byte ∈ bytes, allowed byte) :
    ∃ (raw : { values : List Raw // values.length = n }) (values : List Model),
      arrayDecode element n bytes = some raw ∧ decodeList decode raw.val = some values := by
  induction n generalizing bytes with
  | zero =>
    have empty : bytes = [] := List.length_eq_zero_iff.mp (by simpa using width)
    subst bytes
    exact ⟨⟨[], rfl⟩, [], rfl, rfl⟩
  | succ n ih =>
    have sizeBound : element.byteSize ≤ bytes.length := by
      rw [Nat.succ_mul] at width
      omega
    have headWidth : (bytes.take element.byteSize).length = element.byteSize := by
      simp [List.length_take, Nat.min_eq_left sizeBound]
    have tailWidth : (bytes.drop element.byteSize).length = n * element.byteSize := by
      simp only [List.length_drop]
      rw [Nat.succ_mul] at width
      omega
    obtain ⟨head, value, acceptedHead, decodedHead⟩ := complete _ headWidth
      (fun byte member => all byte (List.mem_of_mem_take member))
    obtain ⟨tail, values, acceptedTail, decodedTail⟩ := ih _ tailWidth
      (fun byte member => all byte (List.mem_of_mem_drop member))
    refine ⟨⟨head :: tail.val, by simp [tail.property]⟩, value :: values, ?_, ?_⟩
    · simp only [arrayDecode, acceptedHead, acceptedTail]
      rfl
    · simp [decodeList, decodedHead, decodedTail]

/-- Array completeness uses exactly the element provider supplied to the
canonical array provider, including its mathematical admission check. -/
theorem RustModel.complete_array (α : Type u) [ma : RustModel α] (n : Usize)
    (element : RustModel.completeRepresentation α) :
    @RustModel.completeRepresentation (Aeneas.Std.Array α n) (@modelArray α n ma) := by
  cases available : ma.representation with
  | none => simp [RustModel.completeRepresentation, available] at element
  | some decoder =>
    simp only [RustModel.completeRepresentation, available] at element
    unfold RustModel.completeRepresentation
    rw [show (@modelArray α n ma).representation = ma.representation.map (fun element =>
      (arrayDecoder element n.val).map
        (fun values => Aeneas.Std.Array.from values.val values.property)) from rfl]
    rw [available]
    simp only [Option.map_some]
    change ∀ bytes, bytes.length = n.val * decoder.byteSize → Initialized bytes → _
    intro bytes width initialized
    obtain ⟨raw, values, physical, decoded⟩ := arrayDecode_model_complete decoder ma.decode
      (fun byte => ∃ value, byte = AMByte.init value) element n.val bytes width initialized
    refine ⟨Aeneas.Std.Array.from raw.val raw.property,
      ⟨values, (decodeList_length ma.decode decoded).trans raw.property⟩, ?_, ?_⟩
    · rw [BitDecoder.run_map]
      simp [BitDecoder.run, arrayDecoder, width, physical]
    · have modelDecoded : decodeList ma.decode
          (Aeneas.Std.Array.from raw.val raw.property).val = some values := by
        simpa only [Aeneas.Std.Array.from_val] using decoded
      dsimp only [RustModel.decode]
      split
      · rename_i rejected
        rw [modelDecoded] at rejected
        contradiction
      · rename_i output accepted
        have same := Option.some.inj (accepted.symm.trans modelDecoded)
        cases same
        rfl

private theorem allzero_eq_replicate (bytes : List AMByte)
    (all : ∀ byte ∈ bytes, byte = AMByte.init 0) :
    bytes = List.replicate bytes.length (AMByte.init 0) := by
  induction bytes with
  | nil => rfl
  | cons byte rest ih =>
    have head := all byte (by simp)
    have tail := ih (fun value member => all value (by simp [member]))
    rw [List.length_cons, List.replicate_succ, head]
    exact congrArg (AMByte.init 0 :: ·) tail

/-- Zero arrays need only the element zero law. They do not require complete
admission of all initialized element patterns. -/
theorem RustModel.zero_array (α : Type u) [ma : RustModel α] (n : Usize)
    (element : RustModel.zeroRepresentation α) :
    @RustModel.zeroRepresentation (Aeneas.Std.Array α n) (@modelArray α n ma) := by
  cases available : ma.representation with
  | none => simp [RustModel.zeroRepresentation, available] at element
  | some decoder =>
    simp only [RustModel.zeroRepresentation, available] at element
    have zeroComplete : ∀ bytes, bytes.length = decoder.byteSize →
        (∀ byte ∈ bytes, byte = AMByte.init 0) →
        ∃ raw value, decoder.run bytes = some raw ∧ ma.decode raw = some value := by
      intro bytes width all
      have same := allzero_eq_replicate bytes all
      rw [width] at same
      simpa only [same] using element
    obtain ⟨raw, values, physical, decoded⟩ := arrayDecode_model_complete decoder ma.decode
      (fun byte => byte = AMByte.init 0) zeroComplete n.val
      (List.replicate (n.val * decoder.byteSize) (AMByte.init 0)) (by simp) (by simp)
    unfold RustModel.zeroRepresentation
    rw [show (@modelArray α n ma).representation = ma.representation.map (fun element =>
      (arrayDecoder element n.val).map
        (fun values => Aeneas.Std.Array.from values.val values.property)) from rfl]
    rw [available]
    simp only [Option.map_some]
    refine ⟨Aeneas.Std.Array.from raw.val raw.property,
      ⟨values, (decodeList_length ma.decode decoded).trans raw.property⟩, ?_, ?_⟩
    · change ((arrayDecoder decoder n.val).map _).run
        (List.replicate (n.val * decoder.byteSize) (AMByte.init 0)) = _
      rw [BitDecoder.run_map]
      simp only [BitDecoder.run, arrayDecoder, List.length_replicate, ↓reduceIte, physical,
        Option.map_some]
    · have modelDecoded : decodeList ma.decode
          (Aeneas.Std.Array.from raw.val raw.property).val = some values := by
        simpa only [Aeneas.Std.Array.from_val] using decoded
      dsimp only [RustModel.decode]
      split
      · rename_i rejected
        rw [modelDecoded] at rejected
        contradiction
      · rename_i output accepted
        have same := Option.some.inj (accepted.symm.trans modelDecoded)
        cases same
        rfl

end AeneasSpecs
