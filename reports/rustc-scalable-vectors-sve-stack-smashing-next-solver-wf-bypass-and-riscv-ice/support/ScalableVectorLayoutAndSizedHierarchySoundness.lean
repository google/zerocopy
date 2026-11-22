/-
Kernel-checked Lean v4.34.1 formalization of:
  1. Symbolic vscale >= 1 runtime byte layouts vs. rustc's vscale = 1 static
     layout assumption (`BackendRepr::SimdScalableVector` marked `is_unsized() == false`)
     and `PlaceRef::alloca` transparent-wrapper peeling.
  2. Pre-monomorphization generic WF bypass (`wfcheck.rs`), unconditional array
     WF bypass (`wf.rs`), and `-Znext-solver=globally` `DUMMY_SP` tuple WF
     regression (`delegate.rs` + `wf.rs`).
  3. Mechanized proofs of the AArch64 SVE-128 (uncorrupted), SVE-256 (silent
     canary overwrite inside 32-byte alloca), SVE-512 (stack-frame buffer
     overflow smashing saved x29/x30), array element overlap, heap layout
     under-allocation, RISC-V RVV debuginfo capability gap, and 1-field
     scalable container validation/layout mismatch.
  4. Sound 4-tier `SizedHierarchy` (`PointeeSized` >= `MetaSized` >=
     `RuntimeSized` >= `ConstSized`) substitution-stable discipline proving
     that separating `RuntimeSized` from `ConstSized` and removing
     `!span.is_dummy()` restores vscale-invariance, substitution stability,
     field/array disjointness, and exact alloca bounds across all `vscale >= 1`.

Constructive Lean v4.34.1 kernel-checked formalization: all definitions are
total, all theorems depend at most on `propext`, and zero auxiliary unsafe
recursor helpers are synthesized.
-/

namespace ScalableVectorSoundness

/-! ## Section 1: Alignment Arithmetic and Byte Ranges -/

/-- Round `size` up to the next multiple of `align` (if `align = 0`, returns `size`). -/
noncomputable def alignUp (size align : Nat) : Nat :=
  if align = 0 then size
  else if size % align = 0 then size
  else size + (align - size % align)

theorem alignUp_ge (size align : Nat) : size ≤ alignUp size align := by
  unfold alignUp
  split
  · exact Nat.le_refl size
  · split
    · exact Nat.le_refl size
    · exact Nat.le_add_right size (align - size % align)

/-- Half-open byte interval `[base, base + len)`. -/
structure ByteRange where
  base : Nat
  len : Nat

/-- Two half-open byte intervals overlap iff they share at least one byte address. -/
def ByteRange.overlaps (r1 r2 : ByteRange) : Prop :=
  r1.base < r2.base + r2.len ∧ r2.base < r1.base + r1.len

/-- Two half-open byte intervals are disjoint when `r1` ends at or before `r2` starts,
or `r2` ends at or before `r1` starts. -/
def ByteRange.disjoint (r1 r2 : ByteRange) : Prop :=
  r1.base + r1.len ≤ r2.base ∨ r2.base + r2.len ≤ r1.base

/-- `r2` is entirely contained inside `r1`. -/
def ByteRange.contains (r1 r2 : ByteRange) : Prop :=
  r1.base ≤ r2.base ∧ r2.base + r2.len ≤ r1.base + r1.len

/-- `r` stays within `[0, frameBytes)`. -/
def ByteRange.withinFrame (r : ByteRange) (frameBytes : Nat) : Prop :=
  r.base + r.len ≤ frameBytes

theorem ByteRange.disjoint_not_overlaps {r1 r2 : ByteRange}
    (h : ByteRange.disjoint r1 r2) : ¬ ByteRange.overlaps r1 r2 := by
  intro hov
  cases h with
  | inl h1 => exact Nat.not_lt.mpr h1 hov.2
  | inr h2 => exact Nat.not_lt.mpr h2 hov.1

/-! ## Section 2: Type Syntax, Monomorphization Substitution, and vscale Layouts -/

/-- Core type language capturing scalars, scalable vectors/containers, generic
type parameters, non-transparent aggregates (`struct2`, `tuple2`, `arr`), and
`#[repr(transparent)]` wrappers. -/
inductive Ty where
  | scalar (bytes align : Nat)
  | sv (lanes elemBytes numVecs : Nat)
  | param (id : Nat)
  | struct2 (f0 f1 : Ty)
  | tuple2 (f0 f1 : Ty)
  | arr (elem : Ty) (len : Nat)
  | transparent (inner : Ty)

/-- Generic monomorphization substitution replacing each `Ty.param id` by `env id`. -/
noncomputable def subst (env : Nat → Ty) : Ty → Ty
  | .scalar b a => .scalar b a
  | .sv l eb nv => .sv l eb nv
  | .param id => env id
  | .struct2 f0 f1 => .struct2 (subst env f0) (subst env f1)
  | .tuple2 f0 f1 => .tuple2 (subst env f0) (subst env f1)
  | .arr elem len => .arr (subst env elem) len
  | .transparent inner => .transparent (subst env inner)

/-- Maximum of two `Nat`s (explicit constructive helper). -/
noncomputable def maxNat (a b : Nat) : Nat :=
  if a ≤ b then b else a

/-- Alignment of a monomorphic type (independent of `vscale` for SVE/RVV vectors,
matching `dl.rust_vector_align(elt.size * count)` in `rustc_abi/src/layout.rs:1005`). -/
noncomputable def runtimeAlign : Ty → Nat
  | .scalar _ a => a
  | .sv lanes elemBytes _ => lanes * elemBytes
  | .param _ => 1
  | .struct2 f0 f1 => maxNat (runtimeAlign f0) (runtimeAlign f1)
  | .tuple2 f0 f1 => maxNat (runtimeAlign f0) (runtimeAlign f1)
  | .arr elem _ => runtimeAlign elem
  | .transparent inner => runtimeAlign inner

/-- True hardware byte size parameterized by runtime `vscale >= 1`.
For `sv lanes elemBytes numVecs`, each hardware register occupies
`vscale * lanes * elemBytes` bytes (`16 * vscale` for `SvU32 = sv 4 4 1`). -/
noncomputable def runtimeSize (vscale : Nat) : Ty → Nat
  | .scalar b a => alignUp b a
  | .sv lanes elemBytes numVecs =>
      alignUp (vscale * (lanes * elemBytes) * numVecs) (lanes * elemBytes)
  | .param _ => 0
  | .struct2 f0 f1 =>
      alignUp
        (alignUp (runtimeSize vscale f0) (runtimeAlign f1) + runtimeSize vscale f1)
        (maxNat (runtimeAlign f0) (runtimeAlign f1))
  | .tuple2 f0 f1 =>
      alignUp
        (alignUp (runtimeSize vscale f0) (runtimeAlign f1) + runtimeSize vscale f1)
        (maxNat (runtimeAlign f0) (runtimeAlign f1))
  | .arr elem len => len * runtimeSize vscale elem
  | .transparent inner => runtimeSize vscale inner

/-- `rustc`'s buggy compile-time size (`vscale = 1` lower bound treated as exact
because `BackendRepr::SimdScalableVector` sets `is_unsized() == false`). -/
noncomputable def staticSizeBuggy (t : Ty) : Nat :=
  runtimeSize 1 t

/-- `rustc`'s buggy fixed byte offset of field 1 inside a 2-field aggregate
(`struct2 f0 f1` or `tuple2 f0 f1`). -/
noncomputable def staticField1OffsetBuggy (f0 f1 : Ty) : Nat :=
  alignUp (staticSizeBuggy f0) (runtimeAlign f1)

/-- Peel `#[repr(transparent)]` wrappers, matching
`layout.peel_transparent_wrappers_from_non_1zst(bx)` in
`compiler/rustc_codegen_ssa/src/mir/place.rs:117`. -/
noncomputable def peelTransparent : Ty → Ty
  | .transparent inner => peelTransparent inner
  | t => t

/-- Exact predicate `Ty::is_scalable_vector` in `compiler/rustc_middle/src/ty/sty.rs:1259`. -/
noncomputable def isScalableVector : Ty → Bool
  | .sv _ _ _ => true
  | _ => false

/-- Exact model of `PlaceRef::alloca` (`compiler/rustc_codegen_ssa/src/mir/place.rs:111-122`):
emits a scalable stack allocation (`runtimeSize vscale t`, via `LLVMBuildAlloca`)
ONLY when the outermost type after peeling transparent wrappers is a scalable vector;
otherwise emits a fixed-size byte array `alloca [staticSizeBuggy t x i8]`. -/
noncomputable def allocaBytesBuggy (vscale : Nat) (t : Ty) : Nat :=
  if isScalableVector (peelTransparent t) then
    runtimeSize vscale t
  else
    staticSizeBuggy t

/-! ## Section 3: Model of `rustc`'s Buggy WF Checks and Memory-Write Geometry -/

/-- Check valid `NumScalableVectors` count for layout calculation
(`compiler/rustc_abi/src/lib.rs:1807-1818`): `1` for element vector, `2..=8` for container. -/
noncomputable def validSvShape (lanes elemBytes numVecs : Nat) : Bool :=
  decide (0 < lanes) && decide (0 < elemBytes) &&
    (decide (numVecs = 1) || (decide (2 ≤ numVecs) && decide (numVecs ≤ 8)))

/-- Exact model of `rustc`'s buggy well-formedness check combining:
- `compiler/rustc_hir_analysis/src/check/wfcheck.rs:1039-1051` (checks only
  pre-monomorphization `isScalableVector` on concrete struct fields, returning `false`
  on `Ty.param`),
- `compiler/rustc_trait_selection/src/traits/wf.rs:812-827` (arrays only require
  `Sized`, which scalable vectors satisfy -> no scalable-vector rejection),
- `compiler/rustc_trait_selection/src/traits/wf.rs:834-856` (tuples check
  `is_scalable_vector() && !self.span.is_dummy()`, disabled when `isDummySpan = true`
  under `-Znext-solver=globally` via `delegate.rs:372-385`). -/
noncomputable def wfCheckBuggy (isDummySpan : Bool) : Ty → Bool
  | .scalar b a => decide (0 < b) && decide (0 < a)
  | .sv l eb nv => validSvShape l eb nv
  | .param _ => true
  | .struct2 f0 f1 =>
      !(isScalableVector f0) && !(isScalableVector f1) &&
      wfCheckBuggy isDummySpan f0 && wfCheckBuggy isDummySpan f1
  | .tuple2 f0 f1 =>
      !(if isDummySpan then false else isScalableVector f0 || isScalableVector f1) &&
      wfCheckBuggy isDummySpan f0 && wfCheckBuggy isDummySpan f1
  | .arr elem _ =>
      -- `wf.rs:813` only checks `require_sized(subty)`; scalable vectors are `Sized`.
      wfCheckBuggy isDummySpan elem
  | .transparent inner => wfCheckBuggy isDummySpan inner

/-- Runtime byte range overwritten by `store <vscale x ...>` into field 0 at offset 0. -/
noncomputable def field0WriteRange (vscale : Nat) (f0 : Ty) : ByteRange :=
  { base := 0, len := runtimeSize vscale f0 }

/-- Byte range occupied by field 1 under `rustc`'s static layout (`vscale = 1`). -/
noncomputable def field1SlotBuggy (f0 f1 : Ty) : ByteRange :=
  { base := staticField1OffsetBuggy f0 f1, len := staticSizeBuggy f1 }

/-- Byte range of saved AArch64 `x29`/`x30` pair placed immediately above a local
aggregate of size `localBytes` (as observed in `run_test`: `sub sp, sp, #48`,
`stp x29, x30, [sp, #32]`). -/
noncomputable def savedFpLrSlot (localBytes : Nat) : ByteRange :=
  { base := localBytes, len := 16 }

/-- Runtime byte range written to array element `idx` under `rustc`'s buggy fixed
`staticSizeBuggy elem` element stride. -/
noncomputable def arrayElemWriteBuggy (vscale : Nat) (elem : Ty) (idx : Nat) : ByteRange :=
  { base := idx * staticSizeBuggy elem, len := runtimeSize vscale elem }

/-! ## Section 4: Concrete SVE-128 / SVE-256 / SVE-512 & `DUMMY_SP` Counterexample Theorems -/

/-- `u64` scalar type (`size = 8`, `align = 8`). -/
noncomputable def u64Ty : Ty := .scalar 8 8

/-- `#[rustc_scalable_vector(4)] struct SvU32(u32)` (`4 * 4 = 16 B` at `vscale = 1`). -/
noncomputable def svU32 : Ty := .sv 4 4 1

/-- `struct GenericPair<T> { first: T, canary: u64 }`. -/
noncomputable def genericPairTy : Ty := .struct2 (.param 0) u64Ty

/-- Monomorphized `GenericPair<SvU32>`. -/
noncomputable def concretePairTy : Ty := subst (fun _ => svU32) genericPairTy

/-- Direct monomorphic tuple `(SvU32, u64)`. -/
noncomputable def directTupleTy : Ty := .tuple2 svU32 u64Ty

/-- Direct monomorphic array `[SvU32; 2]`. -/
noncomputable def directArrayTy : Ty := .arr svU32 2

theorem alignUp_mul_self (k m : Nat) (hm : 0 < m) : alignUp (k * m) m = k * m := by
  unfold alignUp
  have hne : m ≠ 0 := Nat.ne_of_gt hm
  have hmod : (k * m) % m = 0 := Nat.mul_mod_left k m
  simp [hne, hmod]

theorem runtimeSize_svU32 (vscale : Nat) : runtimeSize vscale svU32 = vscale * 16 := by
  dsimp only [svU32, runtimeSize]
  have h1 : vscale * (4 * 4) * 1 = vscale * 16 := Nat.mul_one (vscale * 16)
  rw [h1]
  exact alignUp_mul_self vscale 16 (by decide)

theorem staticSizeBuggy_svU32 : staticSizeBuggy svU32 = 16 := by
  dsimp only [staticSizeBuggy]
  rw [runtimeSize_svU32 1]

theorem runtimeAlign_svU32 : runtimeAlign svU32 = 16 := rfl

theorem runtimeAlign_u64Ty : runtimeAlign u64Ty = 8 := rfl

theorem staticSizeBuggy_u64Ty : staticSizeBuggy u64Ty = 8 := by
  dsimp only [staticSizeBuggy, runtimeSize, u64Ty, alignUp]
  decide

theorem staticField1OffsetBuggy_pair : staticField1OffsetBuggy svU32 u64Ty = 16 := by
  dsimp only [staticField1OffsetBuggy]
  rw [staticSizeBuggy_svU32, runtimeAlign_u64Ty]
  dsimp only [alignUp]
  decide

theorem staticSizeBuggy_concretePair : staticSizeBuggy concretePairTy = 32 := by
  dsimp only [concretePairTy, genericPairTy, subst, staticSizeBuggy, runtimeSize]
  rw [runtimeSize_svU32 1]
  dsimp only [u64Ty, svU32, runtimeAlign, maxNat, alignUp]
  decide

theorem allocaBytesBuggy_concretePair (vscale : Nat) :
    allocaBytesBuggy vscale concretePairTy = 32 := by
  dsimp only [allocaBytesBuggy, peelTransparent, isScalableVector, concretePairTy, genericPairTy, subst]
  exact staticSizeBuggy_concretePair

/-- **Theorem 4.1 (Generic Struct WF Bypass):** `GenericPair<T>` passes `wfCheckBuggy`
under BOTH solvers (`isDummySpan = false` and `true`), even though monomorphizing
`T := SvU32` yields `concretePairTy` whose direct non-generic counterpart is rejected. -/
theorem generic_pair_wf_bypass_both_solvers (isDummySpan : Bool) :
    wfCheckBuggy isDummySpan genericPairTy = true ∧
    wfCheckBuggy isDummySpan concretePairTy = false := by
  cases isDummySpan <;>
    exact ⟨by dsimp only [genericPairTy, wfCheckBuggy, isScalableVector, u64Ty]; decide,
           by dsimp only [concretePairTy, genericPairTy, subst, wfCheckBuggy, isScalableVector, svU32, u64Ty]; decide⟩

/-- **Theorem 4.2 (`-Znext-solver=globally` `DUMMY_SP` Tuple WF Regression):**
Direct monomorphic `(SvU32, u64)` is rejected when `isDummySpan = false`
(`-Znext-solver=no`), yet silently accepted when `isDummySpan = true`
(`-Znext-solver=globally` via `SolverDelegate::well_formed_goals(..., DUMMY_SP, ...)`). -/
theorem direct_tuple_dummysp_next_solver_bypass :
    wfCheckBuggy false directTupleTy = false ∧
    wfCheckBuggy true directTupleTy = true := by
  constructor
  · dsimp only [directTupleTy, wfCheckBuggy, isScalableVector, svU32, u64Ty, validSvShape]
    decide
  · dsimp only [directTupleTy, wfCheckBuggy, isScalableVector, svU32, u64Ty, validSvShape]
    decide

/-- **Theorem 4.3 (Unconditional Direct Array WF Bypass):** Even direct non-generic
`[SvU32; 2]` passes `wfCheckBuggy` under BOTH solvers because `wf.rs:812-827` checks
only `require_sized`. -/
theorem direct_array_unconditional_bypass (isDummySpan : Bool) :
    wfCheckBuggy isDummySpan directArrayTy = true := by
  cases isDummySpan <;>
    (dsimp only [directArrayTy, wfCheckBuggy, svU32, validSvShape]; decide)

/-- **Theorem 4.4 (SVE-128 / `vscale = 1` Baseline):** At `vscale = 1` (`16 B` vector),
writing `pair.first` writes `[0, 16)`, remaining disjoint from `canary` `[16, 24)` and
inside the `32 B` `alloca`. -/
theorem sve128_no_corruption :
    ByteRange.disjoint (field0WriteRange 1 svU32) (field1SlotBuggy svU32 u64Ty) ∧
    ByteRange.withinFrame (field0WriteRange 1 svU32) (allocaBytesBuggy 1 concretePairTy) := by
  rw [allocaBytesBuggy_concretePair 1]
  dsimp only [field0WriteRange, field1SlotBuggy, ByteRange.disjoint, ByteRange.withinFrame]
  rw [runtimeSize_svU32 1, staticField1OffsetBuggy_pair, staticSizeBuggy_u64Ty]
  exact ⟨Or.inl (by decide), by decide⟩

/-- **Theorem 4.5 (SVE-256 / `vscale = 2` Silent Field-Aliasing Corruption):**
At `vscale = 2` (`32 B` vector, e.g. Graviton3/Neoverse V1), storing `pair.first`
writes `[0, 32)`:
  1. It completely contains and overwrites `pair.canary` at `[16, 24)` (`exit 42`),
  2. It stays within the `32 B` local `alloca` and remains strictly disjoint from
     saved `x29`/`x30` at `[32, 48)` — producing silent data corruption with no crash. -/
theorem sve256_silent_canary_overwrite :
    ByteRange.contains (field0WriteRange 2 svU32) (field1SlotBuggy svU32 u64Ty) ∧
    ByteRange.overlaps (field0WriteRange 2 svU32) (field1SlotBuggy svU32 u64Ty) ∧
    ByteRange.withinFrame (field0WriteRange 2 svU32) (allocaBytesBuggy 2 concretePairTy) ∧
    ByteRange.disjoint (field0WriteRange 2 svU32) (savedFpLrSlot 32) := by
  rw [allocaBytesBuggy_concretePair 2]
  dsimp only [field0WriteRange, field1SlotBuggy, savedFpLrSlot,
    ByteRange.contains, ByteRange.overlaps, ByteRange.withinFrame, ByteRange.disjoint]
  rw [runtimeSize_svU32 2, staticField1OffsetBuggy_pair, staticSizeBuggy_u64Ty]
  exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, Or.inl (by decide)⟩

/-- **Theorem 4.6 (SVE-512 / `vscale = 4` Stack-Frame Buffer Overflow & LR Smash):**
At `vscale = 4` (`64 B` vector, e.g. Fujitsu A64FX), storing `pair.first` writes `[0, 64)`:
  1. It exceeds the `32 B` local `alloca` by exactly `32 B` (`¬ withinFrame ... 32`),
  2. It overflows the entire `48 B` function stack frame (`¬ withinFrame ... 48`),
  3. It completely overwrites saved `x29`/`x30` at `[32, 48)` (`SIGSEGV` on `ret`). -/
theorem sve512_stack_frame_overflow_and_lr_smash :
    (field0WriteRange 4 svU32).len = allocaBytesBuggy 4 concretePairTy + 32 ∧
    ¬ ByteRange.withinFrame (field0WriteRange 4 svU32) (allocaBytesBuggy 4 concretePairTy) ∧
    ¬ ByteRange.withinFrame (field0WriteRange 4 svU32) 48 ∧
    ByteRange.contains (field0WriteRange 4 svU32) (savedFpLrSlot 32) := by
  rw [allocaBytesBuggy_concretePair 4]
  dsimp only [field0WriteRange, savedFpLrSlot, ByteRange.withinFrame, ByteRange.contains]
  rw [runtimeSize_svU32 4]
  exact ⟨by decide, by decide, by decide, ⟨by decide, by decide⟩⟩

/-- **Theorem 4.7 (Universal Canary Corruption for All `vscale >= 2`):**
Every hardware vector length with `vscale >= 2` (`>= 256` bits) corrupts `pair.canary`. -/
theorem buggy_canary_corrupted_for_all_vscale_ge_2 (vscale : Nat) (hv : 2 ≤ vscale) :
    ByteRange.contains (field0WriteRange vscale svU32) (field1SlotBuggy svU32 u64Ty) ∧
    ByteRange.overlaps (field0WriteRange vscale svU32) (field1SlotBuggy svU32 u64Ty) := by
  dsimp only [field0WriteRange, field1SlotBuggy, ByteRange.contains, ByteRange.overlaps]
  rw [runtimeSize_svU32 vscale, staticField1OffsetBuggy_pair, staticSizeBuggy_u64Ty]
  have h32 : 32 ≤ vscale * 16 := Nat.mul_le_mul_right 16 hv
  have h24 : 24 ≤ vscale * 16 := Nat.le_trans (by decide : 24 ≤ 32) h32
  have h16lt : 16 < 0 + vscale * 16 := by
    rw [Nat.zero_add]
    exact Nat.lt_of_lt_of_le (by decide : 16 < 32) h32
  refine ⟨⟨Nat.zero_le 16, ?_⟩, ⟨by decide, h16lt⟩⟩
  rw [Nat.zero_add]
  exact h24

/-- **Theorem 4.8 (Universal Local Alloca Overflow for All `vscale >= 3`):**
Every hardware vector length with `vscale >= 3` (`>= 384` bits) overflows the `32 B`
`alloca [32 x i8]` of `GenericPair<SvU32>`. -/
theorem buggy_alloca_overflows_for_all_vscale_ge_3 (vscale : Nat) (hv : 3 ≤ vscale) :
    ¬ ByteRange.withinFrame (field0WriteRange vscale svU32) (allocaBytesBuggy vscale concretePairTy) := by
  rw [allocaBytesBuggy_concretePair vscale]
  dsimp only [field0WriteRange, ByteRange.withinFrame]
  rw [runtimeSize_svU32 vscale, Nat.zero_add]
  have h48 : 48 ≤ vscale * 16 := Nat.mul_le_mul_right 16 hv
  exact Nat.not_le.mpr (Nat.lt_of_lt_of_le (by decide : 32 < 48) h48)

/-- **Theorem 4.9 (Universal Array Element Overlap and Overflow for `[SvU32; 2]` at `vscale >= 2`):**
Writing element 0 of `[SvU32; 2]` overlaps element 1's slot at offset `16`, and writing
element 1 overflows the `32 B` `alloca`, for EVERY `vscale >= 2`. -/
theorem buggy_array_elem_overlap_for_all_vscale_ge_2 (vscale : Nat) (hv : 2 ≤ vscale) :
    ByteRange.overlaps (arrayElemWriteBuggy vscale svU32 0) (arrayElemWriteBuggy vscale svU32 1) ∧
    ¬ ByteRange.withinFrame (arrayElemWriteBuggy vscale svU32 1) (allocaBytesBuggy vscale directArrayTy) := by
  have halloca : allocaBytesBuggy vscale directArrayTy = 32 := by
    dsimp only [allocaBytesBuggy, peelTransparent, isScalableVector, directArrayTy, staticSizeBuggy, runtimeSize]
    rw [runtimeSize_svU32 1]
    rfl
  rw [halloca]
  dsimp only [arrayElemWriteBuggy, ByteRange.overlaps, ByteRange.withinFrame]
  rw [staticSizeBuggy_svU32, runtimeSize_svU32 vscale, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
  have h32 : 32 ≤ vscale * 16 := Nat.mul_le_mul_right 16 hv
  have h16lt : 16 < vscale * 16 := Nat.lt_of_lt_of_le (by decide : 16 < 32) h32
  have hpos : 0 < 16 + vscale * 16 := Nat.lt_of_lt_of_le (by decide : 0 < 16) (Nat.le_add_right 16 _)
  have hgt32 : 32 < 16 + vscale * 16 :=
    Nat.lt_of_lt_of_le (by decide : 32 < 16 + 32) (Nat.add_le_add_left h32 16)
  exact ⟨⟨hpos, h16lt⟩, Nat.not_le.mpr hgt32⟩

/-- **Theorem 4.10 (Universal Heap Layout Under-Allocation for `Layout::new::<SvU32>()`):**
Because `core::alloc::Layout::new::<SvU32>().size() == staticSizeBuggy svU32 == 16`,
safe heap allocation (`Box::new(sv)` / `Vec::push(sv)`) under-allocates by
`(vscale - 1) * 16 > 0` bytes for EVERY `vscale >= 2`. -/
theorem buggy_heap_layout_overflow_for_all_vscale_ge_2 (vscale : Nat) (hv : 2 ≤ vscale) :
    staticSizeBuggy svU32 < runtimeSize vscale svU32 := by
  rw [staticSizeBuggy_svU32, runtimeSize_svU32 vscale]
  have h32 : 32 ≤ vscale * 16 := Nat.mul_le_mul_right 16 hv
  exact Nat.lt_of_lt_of_le (by decide : 16 < 32) h32

/-! ## Section 5: Architecture Debuginfo Capability Gap & Container Arity Mismatch -/

inductive TargetArch where
  | aarch64
  | riscv32
  | riscv64
  | x86_64

/-- `Arch::supports_scalable_vectors` (`compiler/rustc_target/src/spec/mod.rs:1835-1845`). -/
noncomputable def supportsScalableVectors : TargetArch → Bool
  | .aarch64 | .riscv32 | .riscv64 => true
  | .x86_64 => false

/-- `build_scalable_vector_di_node` assertion (`compiler/rustc_codegen_llvm/src/debuginfo/metadata.rs:1214`). -/
noncomputable def debuginfoSupportsScalableVectors : TargetArch → Bool
  | .aarch64 => true
  | .riscv32 | .riscv64 | .x86_64 => false

/-- **Theorem 5.1 (RISC-V RVV Debuginfo Capability Mismatch / ICE):**
Both `riscv64` and `riscv32` are admitted by AST validation (`supportsScalableVectors = true`)
yet rejected by `build_scalable_vector_di_node`'s `assert_matches!(..., Arch::AArch64)`. -/
theorem riscv_debuginfo_capability_gap :
    (supportsScalableVectors .riscv64 = true ∧ debuginfoSupportsScalableVectors .riscv64 = false) ∧
    (supportsScalableVectors .riscv32 = true ∧ debuginfoSupportsScalableVectors .riscv32 = false) := by
  exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

/-- `check_scalable_vector` (`compiler/rustc_hir_analysis/src/check/check.rs:1585-1600`)
allows `1 <= n <= 8` container fields, whereas `NumScalableVectors::from_field_count`
(`compiler/rustc_abi/src/lib.rs:1814-1818`) admits only `2 <= n <= 8`. -/
noncomputable def checkScalableContainerArity (n : Nat) : Bool :=
  decide (1 ≤ n) && decide (n ≤ 8)

noncomputable def layoutContainerArity (n : Nat) : Bool :=
  decide (2 ≤ n) && decide (n ≤ 8)

/-- **Theorem 5.2 (1-Field Container Validation-vs-Layout ICE Gap):** -/
theorem container_x1_check_vs_layout_gap :
    checkScalableContainerArity 1 = true ∧ layoutContainerArity 1 = false := by
  dsimp only [checkScalableContainerArity, layoutContainerArity]
  exact ⟨by decide, by decide⟩

/-! ## Section 6: Sound `SizedHierarchy` (`ConstSized` vs `RuntimeSized`) Discipline -/

/-- Four-tier sizedness hierarchy separating compile-time fixed-size types (`constSized`,
safe in aggregates/arrays/tuples/fixed allocas/heap `Layout::new`) from runtime-known
scalable register/stack types (`runtimeSized`, permitted only in locals, parameters,
returns, scalable containers, and transparent wrappers). -/
inductive SizedTier where
  | constSized
  | runtimeSized
  | metaSized
  | pointeeSized

/-- `tierLe a b = true` means tier `a` is a subtrait (strictly stronger guarantee) of `b`:
`ConstSized <: RuntimeSized <: MetaSized <: PointeeSized`. -/
noncomputable def tierLe : SizedTier → SizedTier → Bool
  | .constSized, _ => true
  | .runtimeSized, .runtimeSized => true
  | .runtimeSized, .metaSized => true
  | .runtimeSized, .pointeeSized => true
  | .metaSized, .metaSized => true
  | .metaSized, .pointeeSized => true
  | .pointeeSized, .pointeeSized => true
  | _, _ => false

/-- Ground typing context mapping every generic parameter to `constSized` (used on
closed monomorphized types). -/
noncomputable def closedCtx : Nat → SizedTier := fun _ => .constSized

/-- True iff `t` contains no free `Ty.param` variables. -/
noncomputable def isClosed : Ty → Bool
  | .scalar _ _ => true
  | .sv _ _ _ => true
  | .param _ => false
  | .struct2 f0 f1 => isClosed f0 && isClosed f1
  | .tuple2 f0 f1 => isClosed f0 && isClosed f1
  | .arr elem _ => isClosed elem
  | .transparent inner => isClosed inner

/-- Sound compile-time `ConstSized` predicate under generic-parameter bounds `Γ`.
Crucially: `.sv` is NEVER `ConstSized`! Non-transparent aggregates (`struct2`, `tuple2`,
`arr`) require `ConstSized` constituents unconditionally (no `Span` parameter!). -/
noncomputable def isConstSized (Γ : Nat → SizedTier) : Ty → Bool
  | .scalar b a => decide (0 < b) && decide (0 < a)
  | .sv _ _ _ => false
  | .param id => tierLe (Γ id) .constSized
  | .struct2 f0 f1 => isConstSized Γ f0 && isConstSized Γ f1
  | .tuple2 f0 f1 => isConstSized Γ f0 && isConstSized Γ f1
  | .arr elem _ => isConstSized Γ elem
  | .transparent inner => isConstSized Γ inner

/-- Sound `RuntimeSized` predicate under `Γ`: includes all `ConstSized` types PLUS
valid scalable vectors `.sv` and transparent wrappers around `RuntimeSized` types. -/
noncomputable def isRuntimeSized (Γ : Nat → SizedTier) : Ty → Bool
  | .scalar b a => decide (0 < b) && decide (0 < a)
  | .sv l eb nv => validSvShape l eb nv
  | .param id => tierLe (Γ id) .runtimeSized
  | .struct2 f0 f1 => isConstSized Γ f0 && isConstSized Γ f1
  | .tuple2 f0 f1 => isConstSized Γ f0 && isConstSized Γ f1
  | .arr elem _ => isConstSized Γ elem
  | .transparent inner => isRuntimeSized Γ inner

/-- Sound span-independent well-formedness check (`wfSound`):
Every type admitted for local variables, aggregates, tuples, arrays, or transparent
wrappers must be `RuntimeSized`, and every constituent of a non-transparent aggregate
must be `ConstSized` regardless of `Span` (eliminating both the pre-monomorphization
generic bypass and the `-Znext-solver=globally` `DUMMY_SP` regression). -/
noncomputable def wfSound (Γ : Nat → SizedTier) (t : Ty) : Bool :=
  isRuntimeSized Γ t

/-- A ground instantiation `env : Nat → Ty` respects generic-parameter bounds `Γ`
when every `env i` is closed and satisfies the tier bound `Γ i`. -/
def EnvRespects (Γ : Nat → SizedTier) (env : Nat → Ty) : Prop :=
  ∀ i, isClosed (env i) = true ∧
    (tierLe (Γ i) .constSized = true → isConstSized closedCtx (env i) = true) ∧
    (tierLe (Γ i) .runtimeSized = true → isRuntimeSized closedCtx (env i) = true)

theorem bool_and_eq_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem tierLe_const_implies_runtime (t : SizedTier) :
    tierLe t .constSized = true → tierLe t .runtimeSized = true := by
  cases t <;> decide

theorem isConstSized_implies_isRuntimeSized (Γ : Nat → SizedTier) (t : Ty) :
    isConstSized Γ t = true → isRuntimeSized Γ t = true := by
  induction t with
  | scalar b a => intro h; exact h
  | sv l eb nv => intro h; cases h
  | param id => exact tierLe_const_implies_runtime (Γ id)
  | struct2 f0 f1 _ _ => intro h; exact h
  | tuple2 f0 f1 _ _ => intro h; exact h
  | arr elem len _ => intro h; exact h
  | transparent inner ih => exact ih

/-- **Theorem 6.1 (Substitution Stability of `isConstSized`):**
If `t` is `ConstSized` under `Γ` and `env` satisfies `Γ`, then `subst env t` is
`ConstSized` in the closed context. -/
theorem isConstSized_subst_stable {Γ : Nat → SizedTier} {env : Nat → Ty}
    (henv : EnvRespects Γ env) (t : Ty) :
    isConstSized Γ t = true → isConstSized closedCtx (subst env t) = true := by
  induction t with
  | scalar b a => intro h; exact h
  | sv l eb nv => intro h; cases h
  | param id =>
      intro h
      exact (henv id).2.1 h
  | struct2 f0 f1 ih0 ih1 =>
      intro h
      dsimp only [isConstSized] at h
      rw [bool_and_eq_true_iff] at h
      dsimp only [subst, isConstSized]
      rw [bool_and_eq_true_iff]
      exact ⟨ih0 h.1, ih1 h.2⟩
  | tuple2 f0 f1 ih0 ih1 =>
      intro h
      dsimp only [isConstSized] at h
      rw [bool_and_eq_true_iff] at h
      dsimp only [subst, isConstSized]
      rw [bool_and_eq_true_iff]
      exact ⟨ih0 h.1, ih1 h.2⟩
  | arr elem len ih =>
      intro h
      exact ih h
  | transparent inner ih =>
      intro h
      exact ih h

/-- **Theorem 6.2 (Substitution Stability of `wfSound` / `isRuntimeSized`):**
Generic well-formedness is preserved under arbitrary bound-respecting monomorphization. -/
theorem wfSound_subst_stable {Γ : Nat → SizedTier} {env : Nat → Ty}
    (henv : EnvRespects Γ env) (t : Ty) :
    wfSound Γ t = true → wfSound closedCtx (subst env t) = true := by
  dsimp only [wfSound]
  induction t with
  | scalar b a => intro h; exact h
  | sv l eb nv => intro h; exact h
  | param id =>
      intro h
      exact (henv id).2.2 h
  | struct2 f0 f1 _ _ =>
      intro h
      dsimp only [isRuntimeSized] at h
      rw [bool_and_eq_true_iff] at h
      dsimp only [subst, isRuntimeSized]
      rw [bool_and_eq_true_iff]
      exact ⟨isConstSized_subst_stable henv f0 h.1, isConstSized_subst_stable henv f1 h.2⟩
  | tuple2 f0 f1 _ _ =>
      intro h
      dsimp only [isRuntimeSized] at h
      rw [bool_and_eq_true_iff] at h
      dsimp only [subst, isRuntimeSized]
      rw [bool_and_eq_true_iff]
      exact ⟨isConstSized_subst_stable henv f0 h.1, isConstSized_subst_stable henv f1 h.2⟩
  | arr elem len _ =>
      intro h
      exact isConstSized_subst_stable henv elem h
  | transparent inner ih =>
      intro h
      exact ih h

/-- `subst env t` is closed whenever `env` maps every parameter to a closed type. -/
theorem subst_isClosed {Γ : Nat → SizedTier} {env : Nat → Ty}
    (henv : EnvRespects Γ env) (t : Ty) :
    isClosed (subst env t) = true := by
  induction t with
  | scalar _ _ => rfl
  | sv _ _ _ => rfl
  | param id => exact (henv id).1
  | struct2 f0 f1 ih0 ih1 =>
      dsimp only [subst, isClosed]
      rw [bool_and_eq_true_iff]
      exact ⟨ih0, ih1⟩
  | tuple2 f0 f1 ih0 ih1 =>
      dsimp only [subst, isClosed]
      rw [bool_and_eq_true_iff]
      exact ⟨ih0, ih1⟩
  | arr elem _ ih => exact ih
  | transparent inner ih => exact ih

/-- **Theorem 6.3 (`vscale`-Invariance of `ConstSized` Types):**
Every closed `ConstSized` type has identical runtime size across ALL hardware
`vscale : Nat` values (`runtimeSize vscale t = staticSizeBuggy t`). -/
theorem isConstSized_vscale_invariant (t : Ty)
    (hcl : isClosed t = true) (hcs : isConstSized closedCtx t = true) (vscale : Nat) :
    runtimeSize vscale t = staticSizeBuggy t := by
  dsimp only [staticSizeBuggy]
  induction t with
  | scalar b a => rfl
  | sv l eb nv => cases hcs
  | param id => cases hcl
  | struct2 f0 f1 ih0 ih1 =>
      dsimp only [isClosed] at hcl
      rw [bool_and_eq_true_iff] at hcl
      dsimp only [isConstSized] at hcs
      rw [bool_and_eq_true_iff] at hcs
      dsimp only [runtimeSize]
      rw [ih0 hcl.1 hcs.1, ih1 hcl.2 hcs.2]
  | tuple2 f0 f1 ih0 ih1 =>
      dsimp only [isClosed] at hcl
      rw [bool_and_eq_true_iff] at hcl
      dsimp only [isConstSized] at hcs
      rw [bool_and_eq_true_iff] at hcs
      dsimp only [runtimeSize]
      rw [ih0 hcl.1 hcs.1, ih1 hcl.2 hcs.2]
  | arr elem len ih =>
      dsimp only [runtimeSize]
      rw [ih hcl hcs]
  | transparent inner ih =>
      dsimp only [runtimeSize]
      exact ih hcl hcs

/-- Every closed `ConstSized` type is non-scalable even after peeling transparent wrappers. -/
theorem isConstSized_not_scalable_peeled (t : Ty)
    (hcl : isClosed t = true) (hcs : isConstSized closedCtx t = true) :
    isScalableVector (peelTransparent t) = false := by
  induction t with
  | scalar _ _ => rfl
  | sv _ _ _ => cases hcs
  | param _ => cases hcl
  | struct2 _ _ _ _ => rfl
  | tuple2 _ _ _ _ => rfl
  | arr _ _ _ => rfl
  | transparent inner ih =>
      dsimp only [peelTransparent]
      exact ih hcl hcs

/-- **Theorem 6.4 (Exact Alloca Soundness for ALL `RuntimeSized` Types):**
Under the sound `SizedHierarchy`, `PlaceRef::alloca`'s `peelTransparent` check
is **100% EXACT** for EVERY `wfSound` type (both `ConstSized` aggregates AND
`RuntimeSized` scalable vectors / transparent wrappers) across ALL `vscale : Nat`! -/
theorem sound_runtimeSized_alloca_exact {Γ : Nat → SizedTier} {env : Nat → Ty}
    (henv : EnvRespects Γ env) (t : Ty) (hwf : wfSound Γ t = true) (vscale : Nat) :
    allocaBytesBuggy vscale (subst env t) = runtimeSize vscale (subst env t) := by
  have hcl : isClosed (subst env t) = true := subst_isClosed henv t
  have hrt : isRuntimeSized closedCtx (subst env t) = true := wfSound_subst_stable henv t hwf
  generalize subst env t = m at hcl hrt ⊢
  induction m with
  | scalar b a =>
      dsimp only [allocaBytesBuggy, peelTransparent, isScalableVector, staticSizeBuggy, runtimeSize]
      rfl
  | sv l eb nv =>
      dsimp only [allocaBytesBuggy, peelTransparent, isScalableVector]
      rfl
  | param id => cases hcl
  | struct2 f0 f1 _ _ =>
      have hcs : isConstSized closedCtx (.struct2 f0 f1) = true := hrt
      dsimp only [allocaBytesBuggy, peelTransparent, isScalableVector]
      exact (isConstSized_vscale_invariant (.struct2 f0 f1) hcl hcs vscale).symm
  | tuple2 f0 f1 _ _ =>
      have hcs : isConstSized closedCtx (.tuple2 f0 f1) = true := hrt
      dsimp only [allocaBytesBuggy, peelTransparent, isScalableVector]
      exact (isConstSized_vscale_invariant (.tuple2 f0 f1) hcl hcs vscale).symm
  | arr elem len _ =>
      have hcs : isConstSized closedCtx (.arr elem len) = true := hrt
      dsimp only [allocaBytesBuggy, peelTransparent, isScalableVector]
      exact (isConstSized_vscale_invariant (.arr elem len) hcl hcs vscale).symm
  | transparent inner ih =>
      dsimp only [allocaBytesBuggy, peelTransparent, staticSizeBuggy, runtimeSize]
      exact ih hcl hrt

/-- **Theorem 6.5 (Sound Aggregate Disjointness & Frame Bounds Across All `vscale` and Instantiations):**
For ANY `wfSound` 2-field struct `struct2 f0 f1` (and identically `tuple2 f0 f1`),
ANY bound-respecting monomorphization `env`, and ANY hardware `vscale : Nat`:
  1. Field 0's runtime write is strictly disjoint from field 1's slot (ZERO silent corruption),
  2. Field 0's runtime write lies strictly within `allocaBytesBuggy`,
  3. Field 1's slot lies strictly within `allocaBytesBuggy`,
  4. The aggregate's runtime size equals its compile-time `staticSizeBuggy` (ZERO overflow). -/
theorem sound_struct2_disjoint_and_in_bounds {Γ : Nat → SizedTier} {env : Nat → Ty}
    (henv : EnvRespects Γ env) (f0 f1 : Ty)
    (hwf : wfSound Γ (.struct2 f0 f1) = true) (vscale : Nat) :
    let m0 := subst env f0
    let m1 := subst env f1
    let frame := allocaBytesBuggy vscale (subst env (.struct2 f0 f1))
    ByteRange.disjoint (field0WriteRange vscale m0) (field1SlotBuggy m0 m1) ∧
    ByteRange.withinFrame (field0WriteRange vscale m0) frame ∧
    ByteRange.withinFrame (field1SlotBuggy m0 m1) frame ∧
    runtimeSize vscale (subst env (.struct2 f0 f1)) = staticSizeBuggy (subst env (.struct2 f0 f1)) := by
  have hwf' : isConstSized Γ f0 = true ∧ isConstSized Γ f1 = true := by
    dsimp only [wfSound, isRuntimeSized] at hwf
    exact (bool_and_eq_true_iff _ _).mp hwf
  have hcl0 : isClosed (subst env f0) = true := subst_isClosed henv f0
  have hcl1 : isClosed (subst env f1) = true := subst_isClosed henv f1
  have hcs0 : isConstSized closedCtx (subst env f0) = true :=
    isConstSized_subst_stable henv f0 hwf'.1
  have hcs1 : isConstSized closedCtx (subst env f1) = true :=
    isConstSized_subst_stable henv f1 hwf'.2
  have heq0 : runtimeSize vscale (subst env f0) = staticSizeBuggy (subst env f0) :=
    isConstSized_vscale_invariant (subst env f0) hcl0 hcs0 vscale
  have hframe :
      allocaBytesBuggy vscale (subst env (.struct2 f0 f1)) =
      staticSizeBuggy (.struct2 (subst env f0) (subst env f1)) := by
    dsimp only [subst, allocaBytesBuggy, peelTransparent, isScalableVector]
    rfl
  have htot :
      staticField1OffsetBuggy (subst env f0) (subst env f1) + staticSizeBuggy (subst env f1) ≤
      staticSizeBuggy (.struct2 (subst env f0) (subst env f1)) := by
    dsimp only [staticSizeBuggy, staticField1OffsetBuggy, runtimeSize]
    exact alignUp_ge _ _
  have hoff : staticSizeBuggy (subst env f0) ≤ staticField1OffsetBuggy (subst env f0) (subst env f1) := by
    dsimp only [staticField1OffsetBuggy]
    exact alignUp_ge _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [field0WriteRange, field1SlotBuggy, ByteRange.disjoint]
    rw [Nat.zero_add, heq0]
    exact Or.inl hoff
  · rw [hframe]
    dsimp only [field0WriteRange, ByteRange.withinFrame]
    rw [Nat.zero_add, heq0]
    exact Nat.le_trans hoff (Nat.le_trans (Nat.le_add_right _ _) htot)
  · rw [hframe]
    dsimp only [field1SlotBuggy, ByteRange.withinFrame]
    exact htot
  · have hclPair : isClosed (subst env (.struct2 f0 f1)) = true :=
      subst_isClosed henv (.struct2 f0 f1)
    have hcsPair : isConstSized closedCtx (subst env (.struct2 f0 f1)) = true :=
      isConstSized_subst_stable henv (.struct2 f0 f1) hwf
    exact isConstSized_vscale_invariant _ hclPair hcsPair vscale

/-- **Theorem 6.6 (Sound Tuple Disjointness & Immunity to `DUMMY_SP`):**
Identical guarantee for `tuple2 f0 f1`, with zero dependence on `Span`. -/
theorem sound_tuple2_disjoint_and_in_bounds {Γ : Nat → SizedTier} {env : Nat → Ty}
    (henv : EnvRespects Γ env) (f0 f1 : Ty)
    (hwf : wfSound Γ (.tuple2 f0 f1) = true) (vscale : Nat) :
    let m0 := subst env f0
    let m1 := subst env f1
    let frame := allocaBytesBuggy vscale (subst env (.tuple2 f0 f1))
    ByteRange.disjoint (field0WriteRange vscale m0) (field1SlotBuggy m0 m1) ∧
    ByteRange.withinFrame (field0WriteRange vscale m0) frame ∧
    ByteRange.withinFrame (field1SlotBuggy m0 m1) frame := by
  have hwf' : isConstSized Γ f0 = true ∧ isConstSized Γ f1 = true := by
    dsimp only [wfSound, isRuntimeSized] at hwf
    exact (bool_and_eq_true_iff _ _).mp hwf
  have hcl0 : isClosed (subst env f0) = true := subst_isClosed henv f0
  have hcs0 : isConstSized closedCtx (subst env f0) = true :=
    isConstSized_subst_stable henv f0 hwf'.1
  have heq0 : runtimeSize vscale (subst env f0) = staticSizeBuggy (subst env f0) :=
    isConstSized_vscale_invariant (subst env f0) hcl0 hcs0 vscale
  have hframe :
      allocaBytesBuggy vscale (subst env (.tuple2 f0 f1)) =
      staticSizeBuggy (.tuple2 (subst env f0) (subst env f1)) := by
    dsimp only [subst, allocaBytesBuggy, peelTransparent, isScalableVector]
    rfl
  have htot :
      staticField1OffsetBuggy (subst env f0) (subst env f1) + staticSizeBuggy (subst env f1) ≤
      staticSizeBuggy (.tuple2 (subst env f0) (subst env f1)) := by
    dsimp only [staticSizeBuggy, staticField1OffsetBuggy, runtimeSize]
    exact alignUp_ge _ _
  have hoff : staticSizeBuggy (subst env f0) ≤ staticField1OffsetBuggy (subst env f0) (subst env f1) := by
    dsimp only [staticField1OffsetBuggy]
    exact alignUp_ge _ _
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [field0WriteRange, field1SlotBuggy, ByteRange.disjoint]
    rw [Nat.zero_add, heq0]
    exact Or.inl hoff
  · rw [hframe]
    dsimp only [field0WriteRange, ByteRange.withinFrame]
    rw [Nat.zero_add, heq0]
    exact Nat.le_trans hoff (Nat.le_trans (Nat.le_add_right _ _) htot)
  · rw [hframe]
    dsimp only [field1SlotBuggy, ByteRange.withinFrame]
    exact htot

/-- **Theorem 6.7 (Sound Array Element Disjointness & Frame Bounds):**
For ANY `wfSound` array `[elem; len]`, ANY bound-respecting monomorphization `env`,
ANY `vscale : Nat`, and ANY distinct in-bounds indices `i < j < len`:
element `i` and element `j` have strictly disjoint runtime write ranges, and both
stay within `allocaBytesBuggy vscale (subst env (.arr elem len))`. -/
theorem sound_array_disjoint_and_in_bounds {Γ : Nat → SizedTier} {env : Nat → Ty}
    (henv : EnvRespects Γ env) (elem : Ty) (len : Nat)
    (hwf : wfSound Γ (.arr elem len) = true) (vscale : Nat)
    (i j : Nat) (hij : i < j) (hj : j < len) :
    let me := subst env elem
    let frame := allocaBytesBuggy vscale (subst env (.arr elem len))
    ByteRange.disjoint (arrayElemWriteBuggy vscale me i) (arrayElemWriteBuggy vscale me j) ∧
    ByteRange.withinFrame (arrayElemWriteBuggy vscale me i) frame ∧
    ByteRange.withinFrame (arrayElemWriteBuggy vscale me j) frame := by
  have hcl : isClosed (subst env elem) = true := subst_isClosed henv elem
  have hcs : isConstSized closedCtx (subst env elem) = true :=
    isConstSized_subst_stable henv elem hwf
  have heq : runtimeSize vscale (subst env elem) = staticSizeBuggy (subst env elem) :=
    isConstSized_vscale_invariant (subst env elem) hcl hcs vscale
  have hframe :
      allocaBytesBuggy vscale (subst env (.arr elem len)) =
      len * staticSizeBuggy (subst env elem) := by
    dsimp only [subst, allocaBytesBuggy, peelTransparent, isScalableVector, staticSizeBuggy, runtimeSize]
    rfl
  let s := staticSizeBuggy (subst env elem)
  have hstep : ∀ k, k * s + s = (k + 1) * s := fun k => (Nat.succ_mul k s).symm
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [arrayElemWriteBuggy, ByteRange.disjoint]
    rw [heq]
    left
    change i * s + s ≤ j * s
    rw [hstep i]
    exact Nat.mul_le_mul_right s hij
  · rw [hframe]
    dsimp only [arrayElemWriteBuggy, ByteRange.withinFrame]
    rw [heq]
    change i * s + s ≤ len * s
    rw [hstep i]
    exact Nat.mul_le_mul_right s (Nat.le_trans hij (Nat.le_of_lt hj))
  · rw [hframe]
    dsimp only [arrayElemWriteBuggy, ByteRange.withinFrame]
    rw [heq]
    change j * s + s ≤ len * s
    rw [hstep j]
    exact Nat.mul_le_mul_right s hj

/-- **Theorem 6.8 (Sound Rejection of Unsound Generic Instantiations):**
Under `wfSound`:
  1. `GenericPair<T>` requires `Γ 0 = .constSized` (cannot be defined with `T: RuntimeSized`),
  2. Instantiating `T := SvU32` violates `EnvRespects` whenever `Γ 0 = .constSized`
     (since `isConstSized closedCtx svU32 = false`),
  3. Direct `(SvU32, u64)` and `[SvU32; 2]` are unconditionally rejected,
  4. Valid standalone `SvU32` and `#[repr(transparent)]` wrappers around `SvU32`
     ARE accepted by `wfSound`. -/
theorem sound_discipline_classifies_all_cases :
    wfSound (fun _ => .runtimeSized) genericPairTy = false ∧
    wfSound (fun _ => .constSized) genericPairTy = true ∧
    isConstSized closedCtx svU32 = false ∧
    wfSound closedCtx directTupleTy = false ∧
    wfSound closedCtx directArrayTy = false ∧
    wfSound closedCtx svU32 = true ∧
    wfSound closedCtx (.transparent svU32) = true := by
  dsimp only [wfSound, isRuntimeSized, isConstSized, genericPairTy, directTupleTy, directArrayTy,
    svU32, u64Ty, closedCtx, tierLe, validSvShape]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end ScalableVectorSoundness
