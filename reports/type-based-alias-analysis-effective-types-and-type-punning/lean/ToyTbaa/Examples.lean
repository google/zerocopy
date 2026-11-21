import ToyTbaa.Semantics

/-!
# Definition adequacy: positive and negative examples (all fully proved)

Each core definition gets at least one intended instance it admits and one it rejects.
-/

namespace Toy.Tbaa
namespace Examples

/-- Four bytes of value `1` (a well-sized `u32`/`f32` value). -/
def ones4 : Val := [1, 1, 1, 1]

/-! ### Layouts and validity -/

/-- Positive: a `pair` occupies eight bytes, the first four of leaf type `u32`. -/
theorem pair_layout : Ty.pair.size = 8 ∧ Ty.pair.leafAt 0 = .u32 ∧ Ty.u8.size = 1 := by decide

/-- Negative: the fifth byte of a `pair` is not a `u32` byte (it belongs to the `f32` field). -/
theorem pair_byte4_not_u32 : Ty.pair.leafAt 4 ≠ .u32 := by decide

/-- Positive: every 4-byte list is a valid `f32` (all bit patterns valid). -/
theorem f32_valid_any_pattern : Ty.f32.Valid [255, 0, 7, 9] := by decide

/-- Negative: a 2-byte list is not a valid `u32`. -/
theorem u32_invalid_short : ¬ Ty.u32.Valid [1, 2] := by decide

/-! ### Compatibility disciplines -/

/-- Positive: the standard discipline admits a byte read of a `u32` byte, a `u32` read of a
`u32` byte, and any read of a byte with no effective type. -/
theorem stdCompat_admits :
    stdCompat (some .u32) .u8 = true ∧ stdCompat (some .u32) .u32 = true ∧
    stdCompat none .f32 = true := by decide

/-- Negative: the standard discipline rejects an `f32` access to a `u32` byte. -/
theorem stdCompat_rejects : stdCompat (some .u32) .f32 = false := by decide

/-- Positive: the strict discipline admits same-type access. -/
theorem strictCompat_admits : strictCompat (some .u32) .u32 = true := by decide

/-- Negative: the strict discipline (no character exemption) rejects a byte read of a `u32`
byte. -/
theorem strictCompat_rejects_byte : strictCompat (some .u32) .u8 = false := by decide

/-! ### `NoCommonLeaf`, `RangesDisjoint`, `DeclaredOn` -/

/-- Positive: `u32` and `f32` share no leaf; so do `u8` and `u32` (the character exemption is
a separate hypothesis wherever it matters); so do the struct `pair` and `u16`. -/
theorem noCommonLeaf_admits :
    NoCommonLeaf .u32 .f32 ∧ NoCommonLeaf .u8 .u32 ∧ NoCommonLeaf .pair .u16 := by decide

/-- The complete table of `NoCommonLeaf` on the toy universe (both orders). -/
theorem noCommonLeaf_table (T U : Ty) :
    NoCommonLeaf T U ↔
      (T ≠ .u8 ∧ U = .u8) ∨ (T = .u8 ∧ U ≠ .u8) ∨
      (T = .u32 ∧ U = .f32) ∨ (T = .f32 ∧ U = .u32) ∨
      (T = .u16 ∧ U ≠ .u16 ∧ U ≠ .u8) ∨ (T ≠ .u16 ∧ T ≠ .u8 ∧ U = .u16) := by
  cases T <;> cases U <;> decide

/-- With the character type excluded, `NoCommonLeaf` admits struct instances: a `pair` access
and a `u16` access (in either order). -/
theorem noCommonLeaf_non_u8_struct_instances :
    Ty.pair ≠ .u8 ∧ Ty.u16 ≠ .u8 ∧ NoCommonLeaf .pair .u16 ∧ NoCommonLeaf .u16 .pair := by decide

/-- Negative: a `pair` and a `u32` share the leaf `u32` (the struct contains a `u32` member),
and a type always shares leaves with itself. -/
theorem noCommonLeaf_rejects : ¬ NoCommonLeaf .pair .u32 ∧ ¬ NoCommonLeaf .f32 .f32 := by decide

/-- Positive: `[0,4)` and `[4,8)` are disjoint. -/
theorem rangesDisjoint_admits : RangesDisjoint 0 4 4 4 := by decide

/-- Negative: `[0,4)` and `[3,4)` overlap. -/
theorem rangesDisjoint_rejects : ¬ RangesDisjoint 0 4 3 1 := by decide

/-- Positive: a declared object is declared storage. -/
theorem declaredOn_admits : DeclaredOn (declSt .u32 4 ones4) 0 4 := by decide

/-- Negative: allocated storage is not declared storage. -/
theorem declaredOn_rejects : ¬ DeclaredOn (freshAt 0 16 ones4) 0 4 := by decide

/-- Positive: allocated storage is allocated storage. -/
theorem allocatedOn_admits : AllocatedOn (freshAt 0 16 ones4) 0 4 := by decide

/-- Negative: a declared object is not allocated storage. -/
theorem allocatedOn_rejects : ¬ AllocatedOn (declSt .u32 4 ones4) 0 4 := by decide

/-! ### `ReadableAt`, `ReceivesAt`, `MemcpyLoadOk`, `valsAt` -/

/-- Positive: the `u32` object of `objSt .u32` is readable at `u32`, and also bytewise. -/
theorem readableAt_admits :
    ReadableAt stdCompat (objSt .u32) .u32 0 ∧ ReadableAt stdCompat (objSt .u32) .u8 1 := by decide

/-- Negative: it is not readable at `f32`, nor beyond allocated memory. -/
theorem readableAt_rejects :
    ¬ ReadableAt stdCompat (objSt .u32) .f32 0 ∧ ¬ ReadableAt stdCompat (objSt .u32) .u8 16 := by
  decide

/-- Positive: allocated storage and a declared `u32` object can receive a `u32`. -/
theorem receivesAt_admits :
    ReceivesAt (objSt .u32) .u32 8 ∧ ReceivesAt (declSt .u32 4 ones4) .u32 0 := by decide

/-- Negative: a declared `f32` object cannot receive a `u32`; unallocated memory receives
nothing. -/
theorem receivesAt_rejects :
    ¬ ReceivesAt (declSt .f32 4 ones4) .u32 0 ∧ ¬ ReceivesAt (objSt .u32) .u32 16 := by decide

/-- State with an `f32` object (value bytes `1`) at `0..3` in allocated storage and a declared
`u32` object at `8..11`. -/
def punIntoDeclSt : St :=
  ⟨fun a => if a < 4 then some ⟨1, .alloc (some .f32)⟩
            else if 8 ≤ a ∧ a < 12 then some ⟨0, .decl .u32⟩ else none,
   fun _ => ones4⟩

/-- Positive: `MemcpyLoadOk` admits copying a `u32` object into allocated storage and
`memcpy` punning of an `f32` object into a declared `u32` object. -/
theorem memcpyLoadOk_admits :
    MemcpyLoadOk (objSt .u32) .u32 0 8 ∧ MemcpyLoadOk punIntoDeclSt .u32 0 8 := by decide

/-- Negative: it rejects copying an `f32` object into allocated storage and loading the copy
at `u32`, and a destination that is not allocated. -/
theorem memcpyLoadOk_rejects :
    ¬ MemcpyLoadOk (objSt .f32) .u32 0 8 ∧ ¬ MemcpyLoadOk (objSt .u32) .u32 0 14 := by decide

theorem valsAt_example : valsAt (objSt .u32) 0 4 = [0, 0, 0, 0] := by decide

/-! ### The effective-type semantics `stepE stdCfg` -/

/-- Positive: store then load at the same type is defined and returns the stored bytes. -/
theorem stepE_same_type_defined :
    exec (stepE stdCfg) [.store .u32 0 0, .load 1 .u32 0, .out 1] (freshAt 0 16 ones4) =
      .done [ones4] := by decide

/-- Negative: store at `u32` then load at `f32` (type punning) is undefined. -/
theorem stepE_punning_ub :
    exec (stepE stdCfg) [.store .u32 0 0, .load 1 .f32 0, .out 1] (freshAt 0 16 ones4) =
      .ub [] := by decide

/-- Positive (character exemption): a byte read of a `u32` object is defined. -/
theorem stepE_byte_read_defined :
    exec (stepE stdCfg) [.store .u32 0 0, .load 1 .u8 0, .out 1] (freshAt 0 16 ones4) =
      .done [[1]] := by decide

/-- Positive (allocated storage is re-typed by stores): storing `u32` then `f32` to the same
allocated bytes, then loading `f32`, is defined. -/
theorem stepE_allocated_retype_defined :
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 0 0, .load 1 .f32 0, .out 1]
      (freshAt 0 16 ones4) = .done [ones4] := by decide

/-- Negative (declared storage is not re-typed): a `f32` store into a declared `u32` object
is undefined. -/
theorem stepE_declared_store_mismatch_ub :
    exec (stepE stdCfg) [.store .f32 0 0] (declSt .u32 4 ones4) = .ub [] := by decide

/-- Positive: `memcpy` copies the effective type into allocated storage, so a typed load of
the copy at the source's type is defined. -/
theorem stepE_memcpy_copies_type_defined :
    exec (stepE stdCfg) [.store .f32 0 0, .memcpy 8 0 4, .load 1 .f32 8, .out 1]
      (freshAt 0 16 ones4) = .done [ones4] := by decide

/-- Negative: after that copy, loading the copy at `u32` is undefined (the copy is an `f32`
object). -/
theorem stepE_memcpy_copy_punning_ub :
    exec (stepE stdCfg) [.store .f32 0 0, .memcpy 8 0 4, .load 1 .u32 8, .out 1]
      (freshAt 0 16 ones4) = .ub [] := by decide

/-- Positive: memcpy into a declared `u32` object keeps its declared type, so copying `f32`
bytes into it and loading at `u32` is defined (the sanctioned punning route). -/
theorem stepE_memcpy_into_declared_defined :
    exec (stepE stdCfg) [.store .f32 0 0, .memcpy 8 0 4, .load 1 .u32 8, .out 1]
      (⟨fun a => if a < 4 then some ⟨0, .alloc none⟩
                 else if 8 ≤ a ∧ a < 12 then some ⟨0, .decl .u32⟩ else none,
        fun _ => ones4⟩ : St) = .done [ones4] := by decide

/-- Positive: a `u32` member of a `pair` object can be accessed at `u32`. Negative: the `f32`
member cannot. -/
theorem stepE_pair_member_access :
    exec (stepE stdCfg) [.store .pair 0 0, .load 1 .u32 0, .out 1]
        (freshAt 0 16 (List.replicate 8 1)) = .done [ones4] ∧
    exec (stepE stdCfg) [.store .pair 0 0, .load 1 .u32 4, .out 1]
        (freshAt 0 16 (List.replicate 8 1)) = .ub [] := by decide

/-- Positive (per-byte tags carry no object boundaries): a `pair` load of eight bytes that
were written by a `u32` store and a separate `f32` store is defined. -/
theorem stepE_pair_load_from_member_stores_defined :
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 4 0, .load 1 .pair 0, .out 1]
      (freshAt 0 16 ones4) = .done [[1, 1, 1, 1, 1, 1, 1, 1]] := by decide

/-- Negative (the character exemption alone does not transfer effective types): copying a
`u32` object byte by byte through a register (`u8` loads and `u8` stores) onto allocated
storage that holds an `f32` object leaves the destination an `f32` object, so a `u32` load of
it is undefined; `memcpy` of the same bytes transfers the `u32` tags and the load is defined. -/
theorem byte_loop_copy_does_not_transfer_effective_type :
    exec (stepE stdCfg)
      [.load 2 .u8 0, .store .u8 8 2, .load 2 .u8 1, .store .u8 9 2,
       .load 2 .u8 2, .store .u8 10 2, .load 2 .u8 3, .store .u8 11 2,
       .load 1 .u32 8, .out 1]
      (⟨fun a => if a < 4 then some ⟨1, .alloc (some .u32)⟩
                 else if 8 ≤ a ∧ a < 12 then some ⟨0, .alloc (some .f32)⟩ else none,
        fun _ => []⟩ : St) = .ub [] ∧
    exec (stepE stdCfg) [.memcpy 8 0 4, .load 1 .u32 8, .out 1]
      (⟨fun a => if a < 4 then some ⟨1, .alloc (some .u32)⟩
                 else if 8 ≤ a ∧ a < 12 then some ⟨0, .alloc (some .f32)⟩ else none,
        fun _ => []⟩ : St) = .done [[1, 1, 1, 1]] := by decide

/-- Negative: reading unallocated memory is undefined (a base fault). -/
theorem stepE_unallocated_ub :
    exec (stepE stdCfg) [.load 1 .u8 100, .out 1] (freshAt 0 16 ones4) = .ub [] := by decide

/-! ### The untyped semantics `stepU` -/

/-- Positive: the punning program is defined under (U) and reinterprets the stored bytes. -/
theorem stepU_punning_defined :
    exec stepU [.store .u32 0 0, .load 1 .f32 0, .out 1] (erase (freshAt 0 16 ones4)) =
      .done [ones4] := by decide

/-- Negative: reading unallocated memory is undefined under (U) too. -/
theorem stepU_unallocated_ub :
    exec stepU [.load 1 .u8 100, .out 1] (erase (freshAt 0 16 ones4)) = .ub [] := by decide

theorem erase_example :
    (erase (freshAt 0 16 ones4)).mem 2 = some 0 ∧ (erase (freshAt 0 16 ones4)).mem 16 = none := by
  decide

/-! ### `TypeFaults`, `UDefined` -/

/-- Positive: an `f32` load of `u32`-typed bytes type-faults; so does a mismatched store into a
declared object (a program without any load). -/
theorem typeFaults_admits :
    TypeFaults stdCfg [.store .u32 0 0, .load 1 .f32 0] (freshAt 0 16 ones4) ∧
    TypeFaults stdCfg [.store .f32 0 0] (declSt .u32 4 ones4) := by decide

/-- Negative: same-type access, byte access to a typed object, and `memcpy` punning into a
declared object followed by a load at the declared type do not type-fault; nor does a program
whose first fault is a base fault. -/
theorem typeFaults_rejects :
    ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .u32 0] (freshAt 0 16 ones4) ∧
    ¬ TypeFaults stdCfg [.store .u32 0 0, .load 1 .u8 2] (freshAt 0 16 ones4) ∧
    ¬ TypeFaults stdCfg [.memcpy 8 0 4, .load 1 .u32 8] punIntoDeclSt ∧
    ¬ TypeFaults stdCfg [.load 1 .u8 100, .load 1 .f32 0] (objSt .u32) := by decide

/-- For a nonstandard configuration whose discipline rejects every tagged access, even a
same-type store-then-load type-faults (so `TypeFaults` depends on the configuration). -/
theorem typeFaults_same_type_nonstandard_cfg :
    TypeFaults ⟨fun _ _ => false, true⟩ [.store .u32 0 0, .load 1 .u32 0] (freshAt 0 16 ones4) := by
  decide

theorem uDefined_admits : UDefined [.store .u32 0 0, .load 1 .f32 0] (erase (freshAt 0 16 ones4)) := by
  decide

theorem uDefined_rejects : ¬ UDefined [.load 1 .u8 100] (erase (freshAt 0 16 ones4)) := by decide

/-! ### Behaviours and refinement -/

/-- Positive: UB with empty trace allows every behaviour; a run allows itself. -/
theorem refines_admits :
    Refines (Allows (.done [[5]])) (Allows (.ub [])) ∧ Refines (Allows (.done [[5]])) (Allows (.done [[5]])) :=
  ⟨(refines_allows_iff _ _).2 (by decide), (refines_allows_iff _ _).2 (by decide)⟩

/-- Negative: different traces do not refine; UB does not retract an already-emitted event. -/
theorem refines_rejects :
    ¬ Refines (Allows (.done [[0]])) (Allows (.done [[1]])) ∧
    ¬ Refines (Allows (.done [[2]])) (Allows (.ub [[1]])) := by
  constructor
  · rw [refines_allows_iff]; decide
  · rw [refines_allows_iff]; decide

/-- Positive example for `ReorderSound`: every block may be replaced by itself. -/
theorem reorderSound_admits : ReorderSound (stepE stdCfg) [.store .u32 0 0] [.store .u32 0 0] :=
  reorderSound_refl _ _

/-- Negative example for `ReorderSound`: swapping two stores of different values to the same
`u32` bytes is not sound. -/
theorem reorderSound_rejects :
    ¬ ReorderSound (stepE stdCfg) [.store .u32 0 0, .store .u32 0 1] [.store .u32 0 1, .store .u32 0 0] :=
  not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2] ((freshAt 0 16 []).withRegs (regs2 ones4 [2, 2, 2, 2]))
    trivial (by decide)

end Examples
end Toy.Tbaa
