import ToyTbaa.Results

/-!
# Companion statements (all fully proved)

These theorems state, in their types, the concrete witnesses that the proofs of
`Results.sink_load_below_store_not_sound_E` (R1b), `Results.store_store_reorder_not_sound_E`
(R1c) and `Results.store_swap_scheme_sound_on_declared_not_on_allocated` (R5c) use internally,
and give an example of the `valsAt` fallback on a range that is not entirely allocated. No other
declaration depends on them.
-/

namespace Toy.Tbaa
namespace Companions

open Results

/-- `valsAt` returns the empty list when the range is not entirely allocated: for `[16, 20)`,
where no byte of `objSt .u32` is allocated, and for `[14, 18)`, where bytes 14 and 15 are
allocated and bytes 16 and 17 are not. -/
theorem valsAt_unallocated_example :
    valsAt (objSt .u32) 16 4 = [] ∧ valsAt (objSt .u32) 14 4 = [] := by decide

/-- The witness inside the proof of R1b. From `freshAt 0 16 ones4` (bytes `0..15` allocated
storage with no effective type, every register holding `ones4`), with the empty prefix and the
suffix `[out 1]`: the source (the `u32` load, then the `f32` store) terminates normally and
prints the four loaded zero bytes; the target (the `f32` store, then the `u32` load) stops at a
`type` fault before any output; and the source outcome does not allow the target outcome. -/
theorem sink_load_below_store_witness_runs :
    exec (stepE stdCfg) [.load 1 .u32 0, .store .f32 0 0, .out 1] (freshAt 0 16 ones4) =
      .done [[0, 0, 0, 0]] ∧
    exec (stepE stdCfg) [.store .f32 0 0, .load 1 .u32 0, .out 1] (freshAt 0 16 ones4) =
      .ub [] ∧
    TypeFaults stdCfg [.store .f32 0 0, .load 1 .u32 0, .out 1] (freshAt 0 16 ones4) ∧
    ¬ Allows (exec (stepE stdCfg) [.load 1 .u32 0, .store .f32 0 0, .out 1] (freshAt 0 16 ones4))
      (exec (stepE stdCfg) [.store .f32 0 0, .load 1 .u32 0, .out 1] (freshAt 0 16 ones4)) := by
  decide

/-- The witness inside the proof of R1c, and a second suffix. From
`(freshAt 0 16 []).withRegs (regs2 ones4 twos4)` (bytes `0..15` allocated storage with no
effective type, register `0` holding `ones4` and every other register `twos4`), with the empty
prefix: with the suffix `[load 2 u8 0, out 2]` the source (the `u32` store of register `0`, then
the `f32` store of register `1`) prints `[2]` and the target (the two stores swapped) prints
`[1]`; with the suffix `[load 2 f32 0, out 2]` the source prints `twos4`, while the target stops
at a `type` fault before any output. -/
theorem store_store_swap_witness_runs :
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 0 1, .load 2 .u8 0, .out 2]
        ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) = .done [[2]] ∧
    exec (stepE stdCfg) [.store .f32 0 1, .store .u32 0 0, .load 2 .u8 0, .out 2]
        ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) = .done [[1]] ∧
    exec (stepE stdCfg) [.store .u32 0 0, .store .f32 0 1, .load 2 .f32 0, .out 2]
        ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) = .done [twos4] ∧
    exec (stepE stdCfg) [.store .f32 0 1, .store .u32 0 0, .load 2 .f32 0, .out 2]
        ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) = .ub [] ∧
    TypeFaults stdCfg [.store .f32 0 1, .store .u32 0 0, .load 2 .f32 0, .out 2]
        ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) := by
  decide

/-- The site at which part (2) of R5c fails, stated in the type: it is not the case that, at
`p = q = 0`, the swap is a refinement in every context from every initial state in which every
allocated byte of `[0, 4)` is allocated storage; the proof's witness state meets that condition. -/
theorem store_swap_scheme_fails_at_zero :
    AllocatedOn ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) 0 4 ∧
    ¬ ReorderSoundFrom (fun σ => AllocatedOn σ 0 4) (stepE stdCfg)
        [.store .u32 0 0, .store .f32 0 1] [.store .f32 0 1, .store .u32 0 0] :=
  ⟨by decide,
   not_reorderSoundFrom_of [] [.load 2 .u8 0, .out 2]
     ((freshAt 0 16 []).withRegs (regs2 ones4 twos4)) (by decide) (by decide)⟩

end Companions
end Toy.Tbaa
