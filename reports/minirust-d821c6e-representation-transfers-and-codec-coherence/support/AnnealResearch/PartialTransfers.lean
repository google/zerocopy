import AnnealResearch.Representation
import AnnealResearch.ByteMemory

/-!
Actual memory commands over complete representation cells. Two high bytes are
copied before two low bytes; no typed read occurs between the raw operations.
The intermediate decoder rejection and final reconstruction are properties of
this owned codec. They neither classify Rust UB nor supply a runtime/CTFE rule.
-/
namespace AnnealResearch.PartialTransfers
open Representation

def src (offset : Nat) : ByteMemory.Ptr := ⟨0, offset, 0⟩
def dst (offset : Nat) : ByteMemory.Ptr := ⟨1, offset, 0⟩
def image (s : ByteMemory.State Cell) (allocation : Nat) : Representation :=
  fun i => s.cells ⟨allocation, i⟩

def memoryFrom (r : Representation) (extent : Nat) : ByteMemory.State Cell where
  cells := fun l => if l.allocation = 0 then r l.offset else .uninit
  live := fun a => decide (a = 0 ∨ a = 1)
  size := fun _ => extent
  readGrant := fun _ => true
  writeGrant := fun _ => true

def initial : ByteMemory.State Cell :=
  memoryFrom (encodePtr target4LE (examplePtr target4LE)) 4

/-- Candidate result of the concrete read-then-write commands; `stage_ok`
    separately proves that their dynamic checks actually accept it. -/
def stage (s : ByteMemory.State Cell) (p q : ByteMemory.Ptr) (n : Nat) :
    ByteMemory.State Cell :=
  ByteMemory.afterWrite .stable (ByteMemory.afterRead .stable s p n) q n
    (ByteMemory.getWindow s p n)

theorem stage_ok (s : ByteMemory.State Cell) (p q : ByteMemory.Ptr) (n : Nat)
    (hr : ByteMemory.ReadReady s p n)
    (hw : ByteMemory.WriteReady (ByteMemory.afterRead .stable s p n) q n) :
    ByteMemory.rawCopy .stable s p q n = .ok (stage s p q n) := by
  rw [ByteMemory.rawCopy_eq_write .stable s p q n hr]
  exact ByteMemory.writeBlock_ok .stable _ q n _ hw

theorem stage_at (s : ByteMemory.State Cell) (p q : ByteMemory.Ptr) (n : Nat)
    (i : Fin n) : (stage s p q n).cells (q.locAt i.val) = s.cells (p.locAt i.val) :=
  ByteMemory.afterWrite_storage .stable _ q n (ByteMemory.getWindow s p n) i

theorem stage_frame (s : ByteMemory.State Cell) (p q : ByteMemory.Ptr) (n : Nat)
    (l : ByteMemory.Loc) (h : ¬ ByteMemory.Span q n l) :
    (stage s p q n).cells l = s.cells l :=
  ByteMemory.afterWrite_frame .stable _ q n (ByteMemory.getWindow s p n) l h

def highState : ByteMemory.State Cell := stage initial (src 2) (dst 2) 2
def assembledState : ByteMemory.State Cell := stage highState (src 0) (dst 0) 2

theorem high_copy :
    ByteMemory.rawCopy .stable initial (src 2) (dst 2) 2 = .ok highState := by
  apply stage_ok <;>
    simp [ByteMemory.ReadReady, ByteMemory.WriteReady, ByteMemory.Fits,
      ByteMemory.afterRead, ByteMemory.revoke, initial, memoryFrom, src, dst]

theorem high_only_decode_rejected : decodePtr target4LE (image highState 1) = none := by
  apply decodePtr_reject_uninit target4LE _ ⟨0, by decide⟩
  change highState.cells ⟨1, 0⟩ = .uninit
  calc
    _ = initial.cells ⟨1, 0⟩ := stage_frame initial (src 2) (dst 2) 2 _
      (by simp [ByteMemory.Span, dst])
    _ = .uninit := rfl

theorem low_copy_after_high :
    ByteMemory.rawCopy .stable highState (src 0) (dst 0) 2 = .ok assembledState := by
  apply stage_ok <;>
    simp [ByteMemory.ReadReady, ByteMemory.WriteReady, ByteMemory.Fits,
      ByteMemory.afterRead, ByteMemory.afterWrite, ByteMemory.revoke,
      highState, stage, initial, memoryFrom, src, dst]

/-- Complete cell equality retains byte values, initialization, provenance,
    generation, tag, and significance index together. -/
theorem assembled_window_exact (i : Fin target4LE.width) :
    image assembledState 1 i.val = encodePtr target4LE (examplePtr target4LE) i.val := by
  have hi : i.val < 4 := i.isLt
  by_cases hlo : i.val < 2
  · have hc : assembledState.cells ⟨1, i.val⟩ = highState.cells ⟨0, i.val⟩ := by
      simpa [assembledState, ByteMemory.Ptr.locAt, src, dst] using
        (stage_at highState (src 0) (dst 0) 2 ⟨i.val, hlo⟩)
    change assembledState.cells ⟨1, i.val⟩ = _
    rw [hc]
    change (stage initial (src 2) (dst 2) 2).cells ⟨0, i.val⟩ = _
    rw [stage_frame initial (src 2) (dst 2) 2 ⟨0, i.val⟩
      (by simp [ByteMemory.Span, dst])]
    rfl
  · have hge : 2 ≤ i.val := by omega
    have hj : i.val - 2 < 2 := by omega
    have hoff : 2 + (i.val - 2) = i.val := by omega
    change (stage highState (src 0) (dst 0) 2).cells ⟨1, i.val⟩ = _
    rw [stage_frame highState (src 0) (dst 0) 2 ⟨1, i.val⟩
      (by simp [ByteMemory.Span, dst]; omega)]
    have hc := stage_at initial (src 2) (dst 2) 2 ⟨i.val - 2, hj⟩
    simpa [highState, ByteMemory.Ptr.locAt, src, dst, hoff, initial, memoryFrom] using hc

theorem assembled_decode :
    decodePtr target4LE (image assembledState 1) = some (examplePtr target4LE) := by
  rw [decodePtr_congr target4LE (image assembledState 1)
    (encodePtr target4LE (examplePtr target4LE)) assembled_window_exact]
  exact decodePtr_encodePtr _ _

theorem assembled_source_preserved (i : Nat) :
    assembledState.cells ⟨0, i⟩ = initial.cells ⟨0, i⟩ := by
  change (stage highState (src 0) (dst 0) 2).cells ⟨0, i⟩ = _
  rw [stage_frame highState (src 0) (dst 0) 2 ⟨0, i⟩
    (by simp [ByteMemory.Span, dst])]
  change (stage initial (src 2) (dst 2) 2).cells ⟨0, i⟩ = _
  rw [stage_frame initial (src 2) (dst 2) 2 ⟨0, i⟩
    (by simp [ByteMemory.Span, dst])]

def misplacedState : ByteMemory.State Cell := stage initial (src 2) (dst 0) 2

theorem misplaced_copy :
    ByteMemory.rawCopy .stable initial (src 2) (dst 0) 2 = .ok misplacedState := by
  apply stage_ok <;>
    simp [ByteMemory.ReadReady, ByteMemory.WriteReady, ByteMemory.Fits,
      ByteMemory.afterRead, ByteMemory.revoke, initial, memoryFrom, src, dst]

theorem misplaced_fragments_rejected : decodePtr target4LE (image misplacedState 1) = none := by
  apply decodePtr_reject_wrong_index target4LE _ ⟨0, by decide⟩
    ⟨2, by decide⟩ ⟨exampleProvenance, 2⟩
  · have hc := stage_at initial (src 2) (dst 0) 2 ⟨0, by decide⟩
    exact hc.trans rfl
  · decide

def mixedInitial : ByteMemory.State Cell := memoryFrom mixed4 4
def mixedResult : ByteMemory.State Cell := stage mixedInitial (src 0) (dst 0) 4

theorem mixed_copy :
    ByteMemory.rawCopy .stable mixedInitial (src 0) (dst 0) 4 = .ok mixedResult := by
  apply stage_ok <;>
    simp [ByteMemory.ReadReady, ByteMemory.WriteReady, ByteMemory.Fits,
      ByteMemory.afterRead, ByteMemory.revoke, mixedInitial, memoryFrom, src, dst]

theorem mixed_window_exact (i : Fin target4LE.width) :
    image mixedResult 1 i.val = mixed4 i.val := by
  have hc := stage_at mixedInitial (src 0) (dst 0) 4 i
  simpa [image, mixedResult, ByteMemory.Ptr.locAt, src, dst, mixedInitial, memoryFrom] using hc

theorem mixed_same_address_bits (i : Fin target4LE.width) :
    (image mixedResult 1 i.val).byteValue =
      (encodePtr target4LE (examplePtr target4LE) i.val).byteValue := by
  rw [mixed_window_exact i]
  by_cases h : i.val = 1
  · have he : i = ⟨1, by decide⟩ := Fin.ext h
    subst i
    rfl
  · simp only [mixed4, ite_eq_right h]
    rw [assembled4_coherent i, encodePtr_cell]

/-- A decoder's unsupported representation result, with equal address bytes;
    no undefined-behavior judgment is derived from this result. -/
theorem mixed_copy_rejected : decodePtr target4LE (image mixedResult 1) = none := by
  rw [decodePtr_congr target4LE (image mixedResult 1) mixed4 mixed_window_exact]
  exact mixed_fragments_rejected

def paddedInitial : ByteMemory.State Cell := memoryFrom paddedInput4 paddedLayout4.extent
def paddedResult : ByteMemory.State Cell :=
  stage paddedInitial (src 0) (dst 0) paddedLayout4.extent

theorem padded_full_copy :
    ByteMemory.rawCopy .stable paddedInitial (src 0) (dst 0) paddedLayout4.extent =
      .ok paddedResult := by
  apply stage_ok <;>
    simp [ByteMemory.ReadReady, ByteMemory.WriteReady, ByteMemory.Fits,
      ByteMemory.afterRead, ByteMemory.revoke, paddedInitial, memoryFrom, src, dst]

theorem padded_window_exact (i : Nat) (hi : i < paddedLayout4.extent) :
    image paddedResult 1 i = paddedInput4 i := by
  have hc := stage_at paddedInitial (src 0) (dst 0) paddedLayout4.extent ⟨i, hi⟩
  simpa [image, paddedResult, ByteMemory.Ptr.locAt, src, dst, paddedInitial, memoryFrom] using hc

theorem padded_copy_decodes :
    decodeAggregate target4LE paddedLayout4 (image paddedResult 1) = some exampleAggregate4 := by
  rw [decodeAggregate_congr target4LE paddedLayout4 paddedLayout4_admissible
    (image paddedResult 1) paddedInput4 padded_window_exact]
  exact paddedInput4_decodes

theorem raw_copy_retains_initialized_padding :
    paddedResult.cells ⟨1, 1⟩ = .init ⟨99, by decide⟩ none := by
  exact (stage_at paddedInitial (src 0) (dst 0) paddedLayout4.extent ⟨1, by decide⟩).trans rfl

#print axioms high_copy
#print axioms high_only_decode_rejected
#print axioms low_copy_after_high
#print axioms assembled_window_exact
#print axioms assembled_decode
#print axioms assembled_source_preserved
#print axioms misplaced_copy
#print axioms misplaced_fragments_rejected
#print axioms mixed_copy
#print axioms mixed_same_address_bits
#print axioms mixed_copy_rejected
#print axioms padded_full_copy
#print axioms padded_copy_decodes
#print axioms raw_copy_retains_initialized_padding

end AnnealResearch.PartialTransfers
