import Rust.Layout

/- An original consumer specimen. The imported PR theorem is unchanged.
   Observations identify five numerical facts, not Rust type meaning or access
   authority. The record below is a mathematical aggregate, not an observed
   concrete Rust packet record. -/
namespace LayoutBridge

inductive ABI where | native64 | wasm32 deriving DecidableEq, Repr
def wordBytes : ABI → Nat | .native64 => 8 | .wasm32 => 4
theorem wordAlignment (abi : ABI) : Rust.IsAlignment (wordBytes abi) := by
  cases abi
  · exact ⟨by decide, 3, by decide⟩
  · exact ⟨by decide, 2, by decide⟩

-- These are independently declared mathematical primitive representations.
-- Their agreement with Bool / [bool;4] / U16<LE> is an external premise.
def boolLayout : Rust.Layout := ⟨1, 1, Rust.alignment_one, by decide⟩
def byteSequence : Rust.SliceDstLayout := ⟨0, boolLayout.size, 1, Rust.alignment_one⟩
def flagsSize (count : Nat) : Nat := Rust.reprCSliceDstSize byteSequence count
def headerSize : Nat := Rust.reprCSliceDstSize byteSequence 2

-- Abstract repr(C)-style order: one word, four one-byte flags, two header bytes.
-- Assume primitive word alignment equals word size; this is not observed by
-- the existing five-field probe. The trailing two-byte field has stride two.
def recordInfo (abi : ABI) : Rust.SliceDstLayout :=
  ⟨wordBytes abi + flagsSize 4, headerSize, wordBytes abi, wordAlignment abi⟩
def recordSize (abi : ABI) : Nat := Rust.reprCSliceDstSize (recordInfo abi) 1
def recordLayout (abi : ABI) : Rust.Layout where
  size := recordSize abi
  align := wordBytes abi
  isAlignment := wordAlignment abi
  sizeAligned := Rust.reprCSliceDstSize_aligned (recordInfo abi) 1

def expectedVector (abi : ABI) (count : Nat) : List Nat :=
  [wordBytes abi, flagsSize count, byteSequence.align, headerSize, byteSequence.align]
def nativeObserved : List Nat := [8,4,1,2,1]
def wasmObserved : List Nat := [4,4,1,2,1]

-- Exact full-length checking, no accepted trailing or missing fields.
def admit (abi : ABI) (count : Nat) (observed : List Nat) : Bool :=
  observed == expectedVector abi count
theorem admission_exact (abi : ABI) (count : Nat) (observed : List Nat) :
    admit abi count observed = true ↔ observed = expectedVector abi count := by
  simp [admit]

-- This is the imported, reusable mathematical content, not just rfl on a list.
theorem flags_aligned (n : Nat) : byteSequence.align ∣ flagsSize n :=
  Rust.reprCSliceDstSize_aligned byteSequence n
theorem record_aligned (abi : ABI) : wordBytes abi ∣ recordSize abi :=
  Rust.reprCSliceDstSize_aligned (recordInfo abi) 1
theorem record_not_smaller (abi : ABI) :
    wordBytes abi + flagsSize 4 + headerSize ≤ recordSize abi := by
  have h := Rust.roundUpToAlign_ge
    ((recordInfo abi).trailingOffset + 1 * (recordInfo abi).elementSize)
    (recordInfo abi).align (wordAlignment abi).1
  simpa [recordSize, Rust.reprCSliceDstSize, recordInfo] using h

-- A consumed observation becomes the field facts used by the shared theorem.
-- No Rust compiler/representation fact is manufactured by this implication.
def ObservedGeometry (abi : ABI) (observed : List Nat) : Prop :=
  observed = expectedVector abi 4 ∧
  (observed[0]?.getD 0) ∣ recordSize abi ∧
  (observed[2]?.getD 0) ∣ flagsSize 4 ∧
  wordBytes abi + flagsSize 4 + headerSize ≤ recordSize abi
theorem admitted_geometry (abi : ABI) (observed : List Nat)
    (accepted : admit abi 4 observed = true) : ObservedGeometry abi observed := by
  have eq := (admission_exact abi 4 observed).mp accepted
  refine ⟨eq, ?_, ?_, record_not_smaller abi⟩
  · simpa [eq, expectedVector] using record_aligned abi
  · simpa [eq, expectedVector] using flags_aligned 4

theorem native_accepted : admit .native64 4 nativeObserved = true := by decide
theorem wasm_accepted : admit .wasm32 4 wasmObserved = true := by decide
theorem native_geometry : ObservedGeometry .native64 nativeObserved :=
  admitted_geometry .native64 nativeObserved native_accepted
theorem wasm_geometry : ObservedGeometry .wasm32 wasmObserved :=
  admitted_geometry .wasm32 wasmObserved wasm_accepted
theorem native_record_size : recordSize .native64 = 16 := by decide
theorem wasm_record_size : recordSize .wasm32 = 12 := by decide
theorem bool_size_one : boolLayout.size = 1 := by decide
theorem flags_four : flagsSize 4 = 4 := by decide
theorem header_two : headerSize = 2 := by decide

theorem wrong_abi : admit .wasm32 4 nativeObserved = false := by decide
theorem wrong_array_length : admit .native64 3 nativeObserved = false := by decide
theorem missing_field : admit .native64 4 [8,4,1,2] = false := by decide
theorem extra_field : admit .native64 4 [8,4,1,2,1,99] = false := by decide
-- Four-byte LE header rather than the independently selected two-byte header.
theorem wrong_header_type : admit .native64 4 [8,4,1,4,1] = false := by decide
-- A wrong field length can have the same padded aggregate size. The full
-- field observation check above rejects it even though total size would not.
theorem different_count_same_aggregate_size :
    Rust.reprCSliceDstSize
      ⟨wordBytes .native64 + flagsSize 3, headerSize, 8, wordAlignment .native64⟩ 1 =
    recordSize .native64 := by decide
-- Geometry cannot distinguish [u8;4] from [bool;4]. This is an explicit limit.
theorem same_layout_type_not_distinguished : admit .native64 4 [8,4,1,2,1] = true := by decide

-- A later actual Rust repr(C) aggregate probe observes this independently
-- declared vector: record size/alignment, two offsets, then primitive facts.
def expectedAggregate (abi : ABI) : List Nat :=
  [recordSize abi, wordBytes abi, wordBytes abi, wordBytes abi + flagsSize 4,
   boolLayout.size, boolLayout.align, flagsSize 4, byteSequence.align,
   headerSize, byteSequence.align, wordBytes abi, wordBytes abi]
def admitAggregate (abi : ABI) (observed : List Nat) : Bool :=
  observed == expectedAggregate abi
def AggregateGeometry (abi : ABI) (observed : List Nat) : Prop :=
  observed = expectedAggregate abi ∧
  (observed[1]?.getD 0) ∣ (observed[0]?.getD 0) ∧
  (observed[3]?.getD 0) + (observed[8]?.getD 0) ≤ (observed[0]?.getD 0)
theorem admitted_aggregate_geometry (abi : ABI) (observed : List Nat)
    (accepted : admitAggregate abi observed = true) : AggregateGeometry abi observed := by
  have eq : observed = expectedAggregate abi := by simpa [admitAggregate] using accepted
  refine ⟨eq, ?_, ?_⟩
  · simpa [eq, expectedAggregate] using record_aligned abi
  · simpa [eq, expectedAggregate] using record_not_smaller abi

#print axioms admitted_aggregate_geometry

#print axioms recordLayout
#print axioms flags_aligned
#print axioms record_aligned
#print axioms record_not_smaller
#print axioms admitted_geometry
#print axioms native_geometry
#print axioms wasm_geometry
#print axioms wrong_abi
#print axioms wrong_array_length
#print axioms wrong_header_type
end LayoutBridge
