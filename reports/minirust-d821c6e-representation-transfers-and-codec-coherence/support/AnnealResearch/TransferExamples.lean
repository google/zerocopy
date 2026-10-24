import AnnealResearch.Representation
import AnnealResearch.ByteMemory
import AnnealResearch.PartialTransfers
import AnnealResearch.Transfers

/-!
Concrete command instances connecting representation and access. The retagging
policy is an abstract experiment, not a claim of legal Rust reference creation.
Resolution and decoder failures below remain owned-model results, not Rust UB
or runtime/CTFE adequacy judgments.
-/
namespace AnnealResearch.TransferExamples
open Representation Transfers PartialTransfers

theorem padded_read_ready : ByteMemory.ReadReady paddedInitial (src 0) paddedLayout4.extent := by
  simp [ByteMemory.ReadReady, ByteMemory.Fits, paddedInitial, memoryFrom, src]

theorem padded_write_ready : ByteMemory.WriteReady
    (ByteMemory.afterRead .stable paddedInitial (src 0) paddedLayout4.extent)
    (dst 0) paddedLayout4.extent := by
  simp [ByteMemory.WriteReady, ByteMemory.Fits, ByteMemory.afterRead,
    ByteMemory.revoke, paddedInitial, memoryFrom, dst]

theorem padded_source_decodes :
    decodeAggregate target4LE paddedLayout4 (memoryRep paddedInitial (src 0)) =
      some exampleAggregate4 := by
  rw [decodeAggregate_congr target4LE paddedLayout4 paddedLayout4_admissible
    (memoryRep paddedInitial (src 0)) paddedInput4
    (by intro i hi; simp [Transfers.memoryRep, paddedInitial, memoryFrom, src, ByteMemory.Ptr.locAt])]
  exact paddedInput4_decodes

/-- Both actual operations decode successfully; their byte-one padding differs. -/
theorem concrete_raw_and_typed_padding :
    ∃ raw typed,
      runRawCopy .stable paddedInitial (src 0) (dst 0) paddedLayout4.extent = .success raw ∧
      typedCopyAggregate target4LE paddedLayout4 .stable identityPolicy
        paddedInitial (src 0) (dst 0) = .success typed ∧
      memoryRep raw (dst 0) 1 = .init ⟨99, by decide⟩ none ∧
      memoryRep typed (dst 0) 1 = .uninit ∧
      decodeAggregate target4LE paddedLayout4 (memoryRep raw (dst 0)) = some exampleAggregate4 ∧
      decodeAggregate target4LE paddedLayout4 (memoryRep typed (dst 0)) = some exampleAggregate4 := by
  obtain ⟨raw, typed, copied, moved, paddingRaw, paddingTyped, _⟩ := raw_and_typed_padding
    target4LE paddedLayout4 paddedLayout4_admissible .stable paddedInitial (src 0) (dst 0)
    exampleAggregate4 padded_read_ready padded_write_ready padded_source_decodes
    ⟨1, by decide⟩ (by decide) (by decide)
  obtain ⟨otherTyped, otherMoved, typedDecoded, _, _⟩ := typedCopyAggregate_supported
    target4LE paddedLayout4 paddedLayout4_admissible .stable identityPolicy paddedInitial
    (src 0) (dst 0) exampleAggregate4 padded_read_ready padded_write_ready padded_source_decodes
  have sameTyped : typed = otherTyped := StoreResult.success.inj (moved.symm.trans otherMoved)
  have sameRaw : raw = paddedResult := CopyResult.success.inj
    (copied.symm.trans (runRawCopy_success .stable paddedInitial paddedResult
      (src 0) (dst 0) paddedLayout4.extent padded_full_copy))
  refine ⟨raw, typed, copied, moved, paddingRaw, paddingTyped, ?_, ?_⟩
  · rw [sameRaw]
    rw [decodeAggregate_congr target4LE paddedLayout4 paddedLayout4_admissible
      (memoryRep paddedResult (dst 0)) (image paddedResult 1)
      (by intro i hi; simp [Transfers.memoryRep, image, dst, ByteMemory.Ptr.locAt])]
    exact padded_copy_decodes
  · rw [sameTyped]
    simpa using typedDecoded

def retagged : Aggregate target4LE := reborrowAggregate (withTag 19) exampleAggregate4

theorem concrete_reborrow_copy :
    ∃ out, typedCopyAggregate target4LE paddedLayout4 .stable (withTag 19)
        paddedInitial (src 0) (dst 0) = .success out ∧
      decodeAggregate target4LE paddedLayout4 (memoryRep out (dst 0)) = some retagged ∧
      retagged.pointer.address = exampleAggregate4.pointer.address ∧
      retagged.pointer.provenance = some ⟨11, 3, 19⟩ ∧ PreservesOrigin (withTag 19) := by
  obtain ⟨out, copied, decoded, _, _⟩ := typedCopyAggregate_supported
    target4LE paddedLayout4 paddedLayout4_admissible .stable (withTag 19) paddedInitial
    (src 0) (dst 0) exampleAggregate4 padded_read_ready padded_write_ready padded_source_decodes
  exact ⟨out, copied, decoded, rfl, rfl, withTag_preserves_origin 19⟩

/-- Allocation zero stores the pointer; allocation eleven stores its pointee. -/
def derefInitial : ByteMemory.State Cell where
  cells := fun l => if l.allocation = 0 then encodePtr target4LE (examplePtr target4LE) l.offset
    else if l.allocation = 11 then .init ⟨77, by decide⟩ none else .uninit
  live := fun a => decide (a = 0 ∨ a = 11)
  size := fun a => if a = 0 then 4 else 1
  readGrant := fun _ => true
  writeGrant := fun _ => true

def currentSpace : AddressSpace where
  base := fun a => if a = 11 then addressNumber target4LE (examplePtr target4LE) else 64
  generation := fun _ => 3

def staleSpace : AddressSpace := { currentSpace with generation := fun _ => 4 }
def pointee : ByteMemory.Ptr := ⟨11, 0, 7⟩
def postLoad : ByteMemory.State Cell := ByteMemory.afterRead .stable derefInitial (src 0) 4

/-- The two live allocations in this concrete witness have nonzero disjoint
    address ranges, and pointer storage has its configured four-byte alignment.
    This is a witness, not a generic allocation-coherence theorem. -/
theorem concrete_address_geometry :
    0 < currentSpace.base 0 ∧ currentSpace.base 0 % 4 = 0 ∧
    currentSpace.base 0 + 4 ≤ currentSpace.base 11 ∧
    currentSpace.base 11 + 1 ≤ 256 ^ target4LE.width := by
  decide

theorem pointer_storage_ready : ByteMemory.ReadReady derefInitial (src 0) target4LE.width := by
  simp [ByteMemory.ReadReady, ByteMemory.Fits, derefInitial, src, target4LE]

theorem pointer_storage_decodes :
    decodePtr target4LE (memoryRep derefInitial (src 0)) = some (examplePtr target4LE) := by
  rw [decodePtr_congr target4LE _ (encodePtr target4LE (examplePtr target4LE))
    (by intro i; simp [memoryRep, derefInitial, src, ByteMemory.Ptr.locAt])]
  exact decodePtr_encodePtr _ _

theorem pointer_resolvable :
    Resolvable target4LE currentSpace postLoad (examplePtr target4LE) exampleProvenance 1 := by
  have hb := addressNumber_bound target4LE (examplePtr target4LE)
  have hbound : addressNumber target4LE (examplePtr target4LE) + 1 ≤ 256 ^ target4LE.width := by omega
  simpa [Resolvable, currentSpace, postLoad, ByteMemory.afterRead, derefInitial,
    exampleProvenance] using hbound

theorem pointee_ready : ByteMemory.ReadReady postLoad pointee 1 := by
  simp [ByteMemory.ReadReady, ByteMemory.Fits, postLoad, ByteMemory.afterRead,
    ByteMemory.revoke, derefInitial, pointee]

theorem pointer_load_then_read :
    loadAndRead target4LE currentSpace .stable derefInitial (src 0) 1 =
      .success (ByteMemory.getWindow postLoad pointee 1)
        (ByteMemory.afterRead .stable postLoad pointee 1) := by
  have ready : ByteMemory.ReadReady postLoad
      ⟨exampleProvenance.allocation,
        addressNumber target4LE (examplePtr target4LE) - currentSpace.base exampleProvenance.allocation,
        exampleProvenance.tag⟩ 1 := by
    simpa [currentSpace, pointee, exampleProvenance] using pointee_ready
  simpa [postLoad, currentSpace, pointee, exampleProvenance, target4LE] using
    (loadAndRead_supported target4LE currentSpace .stable derefInitial (src 0)
      (examplePtr target4LE) exampleProvenance 1 pointer_storage_ready pointer_storage_decodes
      rfl pointer_resolvable ready)

theorem pointee_data :
    (ByteMemory.getWindow postLoad pointee 1) ⟨0, by decide⟩ = .init ⟨77, by decide⟩ none := rfl

/-- The stored pointer and source memory are identical; only the current
    allocation generation changes between the successful and rejected access. -/
theorem same_bits_stale_generation_rejected :
    loadAndRead target4LE staleSpace .stable derefInitial (src 0) 1 =
      .failure (.resolution .rejected) postLoad := by
  exact decoded_stale_pointer_cannot_read target4LE staleSpace .stable derefInitial (src 0)
    (examplePtr target4LE) exampleProvenance 1 pointer_storage_ready pointer_storage_decodes
    rfl (by decide)

def numericPointer : Ptr target4LE := { examplePtr target4LE with provenance := none }

/-- Provenance-free pointer formation is supported; this restricted ordinary
    allocation resolver still rejects using it for a nonzero access. -/
theorem provenance_free_formation_without_access :
    decodePtr target4LE (encodePtr target4LE numericPointer) = some numericPointer ∧
    resolve target4LE currentSpace derefInitial numericPointer 1 = .error .noProvenance := by
  exact ⟨decodePtr_encodePtr _ _, no_provenance_resolution _ _ _ _ _ rfl⟩

/-- Rejection of a provenance-bearing u8 tag is this decoder's unsupported
    case; the const-only integer rule is not a runtime UB justification. -/
theorem provenance_bearing_tag_unsupported :
    decodeAggregate target4LE paddedLayout4
      (fun i => if i = 0 then .init 42 (some ⟨exampleProvenance, 0⟩)
        else paddedInput4 i) = none := by
  simp [decodeAggregate, paddedLayout4_admissible]

#print axioms concrete_raw_and_typed_padding
#print axioms concrete_reborrow_copy
#print axioms pointer_load_then_read
#print axioms pointee_data
#print axioms same_bits_stale_generation_rejected
#print axioms concrete_address_geometry
#print axioms provenance_free_formation_without_access
#print axioms provenance_bearing_tag_unsupported

end AnnealResearch.TransferExamples
