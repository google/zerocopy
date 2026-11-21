-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Div.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Int.Basic
import Init.Data.Int.DivMod.Basic
import Init.Data.List.Basic
import Init.Tactics
import Init.Omega

/-!
# Write-Side SIMD Masked-Store Fault Asymmetry, Tree Borrows RMW Unsoundness, and the Overlapping Tail-Store Trichotomy

Pass-1 `Init.*`-only Lean `v4.34.1` formalization covering:
1. Hardware write-side masked-store fault suppression vs. unconditional fault
   probing (`VPMASKMOVD`/`Q` and EVEX `VMOVDQU8`/`16`/`VMOVDQA32 {k1}` vs.
   SSE2 `MASKMOVDQU` / VEX `VMASKMOVDQU` and `VMOVNTDQ`), Rust/LLVM
   `simd_masked_store` alignment UB refinement asymmetry, and `rustc +avx2`
   scalarized `LeakTrace` 2-safety violation.
2. Categorical unsoundness of write-side aligned RMW slack-writeback across
   `Tree Borrows` (`ForeignAccess` `.write` vs. read-only `DemonicGranuleLoad`),
   concurrent atomic lost updates, and 16-byte Armv8.5-A MTE tag granules.
3. Exact 3-way soundness and refutation trichotomy for overlapping unaligned
   tail stores `[len - W .. len)` (`disjoint`, `in-place unbuffered`, and
   `in-place preloaded`), including the exact biconditional characterization
   (`sound ∀ len ≥ W ↔ ∀ b, F (F b) = F b`) and `len = 32` masking vs. minimal
   `len = 33` refutation.
-/

namespace MutatingSimdTheory

abbrev Mem := Nat → Nat

def writeByte (mem : Mem) (addr val : Nat) : Mem :=
  fun q => match Nat.beq q addr with
    | true  => val
    | false => mem q

theorem writeByte_same (mem : Mem) (addr val : Nat) :
    writeByte mem addr val addr = val := by
  unfold writeByte
  have h : Nat.beq addr addr = true := Nat.beq_refl addr
  rw [h]

theorem writeByte_other (mem : Mem) (addr val q : Nat) (hne : q ≠ addr) :
    writeByte mem addr val q = mem q := by
  unfold writeByte
  cases h : Nat.beq q addr with
  | false => rfl
  | true  => exact False.elim (hne (Nat.eq_of_beq_eq_true h))

-- ============================================================================
-- Section 1: Write-Side Hardware Masked-Store Fault Asymmetry & LeakTrace
-- ============================================================================

inductive AddrPerm where
  | readWrite
  | readOnly
  | protNone
  | unmapped
  | nonCanonical
  deriving DecidableEq

inductive FaultKind where
  | segvAccErr
  | segvMapErr
  | gpZero
  | alignUb
  | maskInvalidUb
  deriving DecidableEq

inductive StoreOutcome where
  | ok (mem : Mem)
  | trap (kind : FaultKind) (faultAddr : Nat)

def permFault (p : AddrPerm) : Option FaultKind :=
  match p with
  | .readWrite    => none
  | .readOnly     => some .segvAccErr
  | .protNone     => some .segvAccErr
  | .unmapped     => some .segvMapErr
  | .nonCanonical => some .gpZero

def checkByteRangeWritable (perm : Nat → AddrPerm) (base n0 : Nat) : Option (FaultKind × Nat) :=
  @Nat.rec (fun _ => Option (FaultKind × Nat))
    none
    (fun n ih =>
      match ih with
      | some err => some err
      | none =>
        match permFault (perm (base + n)) with
        | none    => none
        | some fk => some (fk, base + n))
    n0

def writeByteSpan (mem : Mem) (base : Nat) (valFn : Nat → Nat) (n0 : Nat) : Mem :=
  @Nat.rec (fun _ => Mem)
    mem
    (fun n ih => writeByte ih (base + n) (valFn n))
    n0

theorem checkByteRangeWritable_succ (perm : Nat → AddrPerm) (base n : Nat) :
    checkByteRangeWritable perm base (n + 1) =
      match checkByteRangeWritable perm base n with
      | some err => some err
      | none =>
        match permFault (perm (base + n)) with
        | none    => none
        | some fk => some (fk, base + n) := rfl

theorem writeByteSpan_succ (mem : Mem) (base : Nat) (valFn : Nat → Nat) (n : Nat) :
    writeByteSpan mem base valFn (n + 1) =
      writeByte (writeByteSpan mem base valFn n) (base + n) (valFn n) := rfl

theorem checkByteRangeWritable_all_rw (perm : Nat → AddrPerm) (base : Nat) :
    ∀ (n : Nat), (∀ i, i < n → perm (base + i) = .readWrite) →
      checkByteRangeWritable perm base n = none
  | 0, _ => rfl
  | n + 1, hrw => by
    rw [checkByteRangeWritable_succ]
    have ih := checkByteRangeWritable_all_rw perm base n (fun i hi => hrw i (by omega))
    rw [ih]
    have hn : perm (base + n) = .readWrite := hrw n (by omega)
    rw [hn]
    rfl

theorem writeByteSpan_in (mem : Mem) (base : Nat) (valFn : Nat → Nat) :
    ∀ (n q : Nat), base ≤ q → q < base + n →
      writeByteSpan mem base valFn n q = valFn (q - base)
  | 0, _, hlo, hhi => by omega
  | n + 1, q, hlo, hhi => by
    rw [writeByteSpan_succ]
    exact if hq : q = base + n then by
      subst hq
      rw [writeByte_same]
      have hsub : (base + n) - base = n := by omega
      rw [hsub]
    else by
      rw [writeByte_other _ _ _ _ hq]
      exact writeByteSpan_in mem base valFn n q hlo (by omega)

theorem writeByteSpan_out (mem : Mem) (base : Nat) (valFn : Nat → Nat) :
    ∀ (n q : Nat), (q < base ∨ base + n ≤ q) →
      writeByteSpan mem base valFn n q = mem q
  | 0, _, _ => rfl
  | n + 1, q, hout => by
    rw [writeByteSpan_succ]
    have hne : q ≠ base + n := by omega
    rw [writeByte_other _ _ _ _ hne]
    exact writeByteSpan_out mem base valFn n q (by omega)

/-- MSB extraction on unsigned `w`-bit lane value (`w ≥ 1`). -/
def msbActive (laneBits val : Nat) : Bool :=
  Nat.ble (Nat.shiftLeft 1 (laneBits - 1)) (val % (Nat.shiftLeft 1 laneBits))

def execFaultSuppressingLanes
    (perm : Nat → AddrPerm) (ptr laneBytes : Nat)
    (activeFn : Nat → Bool) (laneByteFn : Nat → Nat → Nat)
    (mem0 : Mem) (n0 : Nat) : StoreOutcome :=
  @Nat.rec (fun _ => StoreOutcome)
    (.ok mem0)
    (fun i ih =>
      match ih with
      | .trap fk fa => .trap fk fa
      | .ok memCur =>
        let laneAddr := ptr + laneBytes * i
        match activeFn i with
        | false => .ok memCur
        | true  =>
          match checkByteRangeWritable perm laneAddr laneBytes with
          | some (fk, fa) => .trap fk fa
          | none => .ok (writeByteSpan memCur laneAddr (laneByteFn i) laneBytes))
    n0

/-- `VPMASKMOVD` (`laneBytes = 4`) / `VPMASKMOVQ` (`laneBytes = 8`):
    checks MSB of each mask lane; suppresses `#PF` and `#GP` on `MSB == 0`. -/
def vpMaskStore
    (perm : Nat → AddrPerm) (ptr laneBytes numLanes : Nat)
    (maskLane : Nat → Nat) (valByte : Nat → Nat → Nat) (mem0 : Mem) : StoreOutcome :=
  let laneBits := 8 * laneBytes
  execFaultSuppressingLanes perm ptr laneBytes
    (fun i => msbActive laneBits (maskLane i)) valByte mem0 numLanes

/-- EVEX masked store (`VMOVDQU8`/`16` with `reqAlign = 1`, `VMOVDQA32` with `reqAlign = 32`):
    checks alignment `#GP(0)` ONLY when at least one mask bit is active (`kMask != 0` on lanes). -/
def anyLaneActive (activeFn : Nat → Bool) (n0 : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    false
    (fun n ih => ih || activeFn n)
    n0

def kBitActive (kMask i : Nat) : Bool :=
  !Nat.beq (Nat.land (Nat.shiftRight kMask i) 1) 0

def evexMaskStore
    (perm : Nat → AddrPerm) (reqAlign ptr laneBytes numLanes kMask : Nat)
    (valByte : Nat → Nat → Nat) (mem0 : Mem) : StoreOutcome :=
  let activeFn := fun i => kBitActive kMask i
  match anyLaneActive activeFn numLanes with
  | false => .ok mem0
  | true =>
    match Nat.beq (ptr % reqAlign) 0 with
    | false => .trap .gpZero 0
    | true  => execFaultSuppressingLanes perm ptr laneBytes activeFn valByte mem0 numLanes

/-- Rust / Miri / LLVM `simd_masked_store`:
    1. Checks `ptr % reqAlign == 0` UNCONDITIONALLY before inspecting any mask lane.
    2. Validates every mask lane `∈ {0, 2^w - 1}` (`allOnes = 2^w - 1`).
    3. Dereferences strictly active (`allOnes`) lanes. -/
def validSimdMaskLanes (laneBits : Nat) (maskLane : Nat → Nat) (n0 : Nat) : Bool :=
  @Nat.rec (fun _ => Bool)
    true
    (fun i ih =>
      let allOnes := (Nat.shiftLeft 1 laneBits) - 1
      let v := maskLane i
      ih && (Nat.beq v 0 || Nat.beq v allOnes))
    n0

def rustSimdMaskedStore
    (perm : Nat → AddrPerm) (reqAlign ptr laneBytes numLanes : Nat)
    (maskLane : Nat → Nat) (valByte : Nat → Nat → Nat) (mem0 : Mem) : StoreOutcome :=
  let laneBits := 8 * laneBytes
  let allOnes := (Nat.shiftLeft 1 laneBits) - 1
  match Nat.beq (ptr % reqAlign) 0 with
  | false => .trap .alignUb ptr
  | true =>
    match validSimdMaskLanes laneBits maskLane numLanes with
    | false => .trap .maskInvalidUb ptr
    | true =>
      execFaultSuppressingLanes perm ptr laneBytes
        (fun i => Nat.beq (maskLane i) allOnes) valByte mem0 numLanes

/-- SSE2 `MASKMOVDQU` (`66 0F F7`, implicit `[RDI]`) and VEX `VMASKMOVDQU`:
    probes write permission across ALL 16 bytes `[rdi .. rdi + 16)` BEFORE applying mask! -/
def applyMaskMovBytes
    (rdi : Nat) (maskByte valByte : Nat → Nat) (mem0 : Mem) (n0 : Nat) : Mem :=
  @Nat.rec (fun _ => Mem)
    mem0
    (fun j prev =>
      match msbActive 8 (maskByte j) with
      | false => prev
      | true  => writeByte prev (rdi + j) (valByte j))
    n0

def sse2MaskMovDqu
    (perm : Nat → AddrPerm) (rdi : Nat)
    (maskByte valByte : Nat → Nat) (mem0 : Mem) : StoreOutcome :=
  match checkByteRangeWritable perm rdi 16 with
  | some (fk, fa) => .trap fk fa
  | none => .ok (applyMaskMovBytes rdi maskByte valByte mem0 16)

/-- Non-temporal 32-byte aligned `VMOVNTDQ` (`_mm256_stream_si256`):
    unmasked, traps with `#GP(0)` if `ptr % 32 != 0` and checks all 32 bytes. -/
def vmovntdqStore
    (perm : Nat → AddrPerm) (ptr : Nat) (valByte : Nat → Nat) (mem0 : Mem) : StoreOutcome :=
  match Nat.beq (ptr % 32) 0 with
  | false => .trap .gpZero 0
  | true =>
    match checkByteRangeWritable perm ptr 32 with
    | some (fk, fa) => .trap fk fa
    | none => .ok (writeByteSpan mem0 ptr valByte 32)

theorem execFaultSuppressing_succ
    (perm : Nat → AddrPerm) (ptr laneBytes : Nat) (activeFn : Nat → Bool)
    (laneByteFn : Nat → Nat → Nat) (mem0 : Mem) (n : Nat) :
    execFaultSuppressingLanes perm ptr laneBytes activeFn laneByteFn mem0 (n + 1) =
      match execFaultSuppressingLanes perm ptr laneBytes activeFn laneByteFn mem0 n with
      | .trap fk fa => .trap fk fa
      | .ok memCur =>
        let laneAddr := ptr + laneBytes * n
        match activeFn n with
        | false => .ok memCur
        | true  =>
          match checkByteRangeWritable perm laneAddr laneBytes with
          | some (fk, fa) => .trap fk fa
          | none => .ok (writeByteSpan memCur laneAddr (laneByteFn n) laneBytes) := rfl

theorem execFaultSuppressing_inactive
    (perm : Nat → AddrPerm) (ptr laneBytes : Nat) (activeFn : Nat → Bool)
    (hInactive : ∀ i, activeFn i = false)
    (laneByteFn : Nat → Nat → Nat) (mem0 : Mem) :
    ∀ n, execFaultSuppressingLanes perm ptr laneBytes activeFn laneByteFn mem0 n = .ok mem0
  | 0 => rfl
  | n + 1 => by
    rw [execFaultSuppressing_succ]
    rw [execFaultSuppressing_inactive perm ptr laneBytes activeFn hInactive laneByteFn mem0 n]
    rw [hInactive n]

theorem one_le_shiftLeft_one : ∀ m, 1 ≤ Nat.shiftLeft 1 m
  | 0 => by decide
  | m + 1 => by
    have ih := one_le_shiftLeft_one m
    have hstep : Nat.shiftLeft 1 (m + 1) = 2 * Nat.shiftLeft 1 m := by
      change Nat.shiftLeft (Nat.shiftLeft 1 1) m = 2 * Nat.shiftLeft 1 m
      simp [Nat.shiftLeft_eq]
    omega

/-- Theorem 1.1: `VPMASKMOVD`/`Q` with zero mask suppresses `#PF` (`PROT_READ`,
    `PROT_NONE`, `munmap`) and `#GP(0)` (`0xdead_0000_0000_0000` non-canonical). -/
theorem vpmaskmov_zero_mask_suppresses_all_faults
    (perm : Nat → AddrPerm) (ptr laneBytes numLanes : Nat) (_hLB : laneBytes ≥ 1)
    (valByte : Nat → Nat → Nat) (mem0 : Mem) :
    vpMaskStore perm ptr laneBytes numLanes (fun _ => 0) valByte mem0 = .ok mem0 := by
  dsimp only [vpMaskStore]
  apply execFaultSuppressing_inactive
  intro i
  unfold msbActive
  rw [Nat.zero_mod]
  have hpos : 1 ≤ Nat.shiftLeft 1 (8 * laneBytes - 1) := one_le_shiftLeft_one _
  cases h : Nat.ble (Nat.shiftLeft 1 (8 * laneBytes - 1)) 0 with
  | false => rfl
  | true =>
    have hle := Nat.le_of_ble_eq_true h
    omega

/-- Theorem 1.2: `VPMASKMOVD` (`laneBytes = 4`) treats lane mask `1` (`LSB = 1, MSB = 0`)
    as inactive (silent no-op on `PROT_NONE`), whereas `rustSimdMaskedStore` flags `maskInvalidUb`. -/
theorem vpmaskmov_lsb1_msb0_silent_noop_vs_rust_ub
    (ptr : Nat) (hAlign : ptr % 32 = 0) (valByte : Nat → Nat → Nat) (mem0 : Mem) :
    vpMaskStore (fun _ => .protNone) ptr 4 8 (fun _ => 1) valByte mem0 = .ok mem0 ∧
    rustSimdMaskedStore (fun _ => .readWrite) 32 ptr 4 8 (fun _ => 1) valByte mem0 =
      .trap .maskInvalidUb ptr := by
  refine ⟨?_, ?_⟩
  · dsimp only [vpMaskStore]
    exact execFaultSuppressing_inactive _ ptr 4 _ (fun _ => rfl) valByte mem0 8
  · dsimp only [rustSimdMaskedStore]
    rw [hAlign]
    rfl

theorem zero_shiftRight_eq : ∀ n, Nat.shiftRight 0 n = 0
  | 0 => rfl
  | n + 1 => by
    change (Nat.shiftRight 0 n) / 2 = 0
    rw [zero_shiftRight_eq n]

theorem anyLaneActive_succ (activeFn : Nat → Bool) (n : Nat) :
    anyLaneActive activeFn (n + 1) = (anyLaneActive activeFn n || activeFn n) := rfl

theorem anyLaneActive_zero : ∀ n, anyLaneActive (fun i => kBitActive 0 i) n = false
  | 0 => rfl
  | n + 1 => by
    rw [anyLaneActive_succ, anyLaneActive_zero n]
    unfold kBitActive
    rw [zero_shiftRight_eq n]
    rfl

/-- Theorem 1.3: Hardware EVEX `VMOVDQA32`/`VMOVDQU8 {k1}` with `k1 = 0` suppresses
    ALL faults—including `#GP(0)` on misaligned `ptr` and non-canonical addresses. -/
theorem evex_k0_suppresses_all_faults_including_misaligned
    (perm : Nat → AddrPerm) (reqAlign ptr laneBytes numLanes : Nat)
    (valByte : Nat → Nat → Nat) (mem0 : Mem) :
    evexMaskStore perm reqAlign ptr laneBytes numLanes 0 valByte mem0 = .ok mem0 := by
  dsimp only [evexMaskStore]
  rw [anyLaneActive_zero numLanes]

/-- Theorem 1.4: ISA-vs-Rust/LLVM Refinement Asymmetry on `k1 = 0` + misaligned `ptr`.
    `rustSimdMaskedStore` (`SimdAlign::Vector = 32`) traps with `alignUb` at `ptr = 1, mask = 0`,
    whereas hardware `evexMaskStore` (`VMOVDQA32 [ptr] {k1=0}`) succeeds as a no-op. -/
theorem rust_simd_masked_store_vs_evex_k0_asymmetry
    (valByte : Nat → Nat → Nat) (mem0 : Mem) :
    rustSimdMaskedStore (fun _ => .readWrite) 32 1 4 8 (fun _ => 0) valByte mem0 =
      .trap .alignUb 1 ∧
    evexMaskStore (fun _ => .nonCanonical) 32 1 4 8 0 valByte mem0 = .ok mem0 := by
  refine ⟨rfl, ?_⟩
  exact evex_k0_suppresses_all_faults_including_misaligned _ 32 1 4 8 valByte mem0

/-- Theorem 1.5: SSE2 `MASKMOVDQU` / VEX `VMASKMOVDQU` traps even when `mask == 0`
    on `PROT_READ`, `PROT_NONE`, `unmapped`, and `nonCanonical` pages. -/
theorem maskmovdqu_zero_mask_traps_on_nonwritable
    (rdi : Nat) (valByte : Nat → Nat) (mem0 : Mem) :
    sse2MaskMovDqu (fun _ => .readOnly) rdi (fun _ => 0) valByte mem0 = .trap .segvAccErr rdi ∧
    sse2MaskMovDqu (fun _ => .protNone) rdi (fun _ => 0) valByte mem0 = .trap .segvAccErr rdi ∧
    sse2MaskMovDqu (fun _ => .unmapped) rdi (fun _ => 0) valByte mem0 = .trap .segvMapErr rdi ∧
    sse2MaskMovDqu (fun _ => .nonCanonical) rdi (fun _ => 0) valByte mem0 = .trap .gpZero rdi :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Theorem 1.6: Page-boundary straddle trap (`[4088..4096)` RW, `[4096..4104)` `PROT_READ`
    or `PROT_NONE`, active mask only on `0..8` (`0x00FF`)).
    EVEX `VMOVDQU8 {k1=0x00FF}` succeeds and writes `[4088..4096)`, whereas `MASKMOVDQU`
    traps at `4096` despite `maskByte j = 0` for all `j ∈ 8..16`! -/
def straddlePagePerm (roNext : Bool) (addr : Nat) : AddrPerm :=
  match Nat.blt addr 4096 with
  | true  => .readWrite
  | false => match roNext with | true => .readOnly | false => .protNone

theorem maskmovdqu_straddle_traps_where_evex_succeeds
    (roNext : Bool) (valByte : Nat → Nat) (mem0 : Mem) :
    sse2MaskMovDqu (straddlePagePerm roNext) 4088
      (fun j => if j < 8 then 0x80 else 0) valByte mem0 =
      .trap .segvAccErr 4096 ∧
    (∃ mem', evexMaskStore (straddlePagePerm roNext) 1 4088 1 16 0x00ff
      (fun j _ => valByte j) mem0 = .ok mem') := by
  cases roNext <;> exact ⟨rfl, ⟨_, rfl⟩⟩

/-- Theorem 1.7: Unsoundness of implementing `llvm.x86.sse2.maskmov.dqu` in Miri / `lean-miri`
    by delegating to `rustSimdMaskedStore` (`reqAlign = 1`): on a read-only static with `mask = 0`,
    `rustSimdMaskedStore` returns `.ok mem0` while real x86-64 `MASKMOVDQU` raises `SIGSEGV`. -/
theorem naive_maskmovdqu_miri_shim_unsound (rdi : Nat) (valByte : Nat → Nat) (mem0 : Mem) :
    rustSimdMaskedStore (fun _ => .readOnly) 1 rdi 1 16 (fun _ => 0) (fun j _ => valByte j) mem0 =
      .ok mem0 ∧
    sse2MaskMovDqu (fun _ => .readOnly) rdi (fun _ => 0) valByte mem0 =
      .trap .segvAccErr rdi := by
  refine ⟨?_, rfl⟩
  dsimp only [rustSimdMaskedStore]
  rw [Nat.mod_one]
  change (match validSimdMaskLanes 8 (fun _ => 0) 16 with
    | false => StoreOutcome.trap .maskInvalidUb rdi
    | true => execFaultSuppressingLanes (fun _ => .readOnly) rdi 1
                (fun _ => Nat.beq 0 255) (fun j _ => valByte j) mem0 16) = StoreOutcome.ok mem0
  have hv : validSimdMaskLanes 8 (fun _ => 0) 16 = true := rfl
  rw [hv]
  exact execFaultSuppressing_inactive _ rdi 1 _ (fun _ => rfl) (fun j _ => valByte j) mem0 16

/-- 2-Safety `LeakTrace` model comparing `rustc +avx2` scalarized `simd_masked_store`
    (`vpmovmskb` + per-lane conditional branch + `vpextrb`) against EVEX `vmovdqu8 {k1}`. -/
inductive LeakEvent where
  | branch (taken : Bool)
  | scalarStore (off : Nat)
  | maskedVecStore (ptr width : Nat)
  deriving DecidableEq

def avx2ScalarizedStoreStep
    (ptr : Nat) (kMask : Nat) (valByte : Nat → Nat) (n0 : Nat) (mem0 : Mem) (tr0 : List LeakEvent)
    : Mem × List LeakEvent :=
  @Nat.rec (fun _ => Mem × List LeakEvent)
    (mem0, tr0)
    (fun i prev =>
      let (mem1, tr1) := prev
      match kBitActive kMask i with
      | false => (mem1, tr1 ++ [.branch false])
      | true  => (writeByte mem1 (ptr + i) (valByte i), tr1 ++ [.branch true, .scalarStore i]))
    n0

def evexMaskedVecStoreStep
    (ptr width kMask : Nat) (valByte : Nat → Nat) (n0 : Nat) (mem0 : Mem) : Mem :=
  @Nat.rec (fun _ => Mem)
    mem0
    (fun i mem1 =>
      let _ := width
      match kBitActive kMask i with
      | false => mem1
      | true  => writeByte mem1 (ptr + i) (valByte i))
    n0

def evexMaskedVecStoreWithTrace
    (ptr width kMask : Nat) (valByte : Nat → Nat) (mem0 : Mem) : Mem × List LeakEvent :=
  (evexMaskedVecStoreStep ptr width kMask valByte width mem0, [.maskedVecStore ptr width])

theorem avx2ScalarizedStoreStep_succ
    (ptr kMask : Nat) (valByte : Nat → Nat) (i : Nat) (mem0 : Mem) (tr0 : List LeakEvent) :
    avx2ScalarizedStoreStep ptr kMask valByte (i + 1) mem0 tr0 =
      let (mem1, tr1) := avx2ScalarizedStoreStep ptr kMask valByte i mem0 tr0
      match kBitActive kMask i with
      | false => (mem1, tr1 ++ [.branch false])
      | true  => (writeByte mem1 (ptr + i) (valByte i), tr1 ++ [.branch true, .scalarStore i]) := rfl

theorem evexMaskedVecStoreStep_succ
    (ptr width kMask : Nat) (valByte : Nat → Nat) (i : Nat) (mem0 : Mem) :
    evexMaskedVecStoreStep ptr width kMask valByte (i + 1) mem0 =
      let mem1 := evexMaskedVecStoreStep ptr width kMask valByte i mem0
      match kBitActive kMask i with
      | false => mem1
      | true  => writeByte mem1 (ptr + i) (valByte i) := rfl

theorem avx2_vs_evex_1safety_mem_eq
    (ptr width kMask : Nat) (valByte : Nat → Nat) (mem0 : Mem) :
    ∀ n, (avx2ScalarizedStoreStep ptr kMask valByte n mem0 []).1 =
         evexMaskedVecStoreStep ptr width kMask valByte n mem0
  | 0 => rfl
  | n + 1 => by
    rw [avx2ScalarizedStoreStep_succ, evexMaskedVecStoreStep_succ]
    dsimp only []
    rw [← avx2_vs_evex_1safety_mem_eq ptr width kMask valByte mem0 n]
    cases kBitActive kMask n <;> rfl

/-- Theorem 1.8: `rustc +avx2` byte `simd_masked_store` is 1-safety memory-equivalent to
    EVEX `vmovdqu8 {k1}`, yet violates constant-time 2-safety `LeakTrace` on secret masks
    (`kMask = 0` vs. `kMask = 1`), whereas EVEX `vmovdqu8 {k1}` has mask-independent trace! -/
theorem avx2_scalarized_masked_store_1safety_vs_2safety
    (ptr : Nat) (valByte : Nat → Nat) (mem0 : Mem) :
    (∀ kMask, (avx2ScalarizedStoreStep ptr kMask valByte 16 mem0 []).1 =
              (evexMaskedVecStoreWithTrace ptr 16 kMask valByte mem0).1) ∧
    (avx2ScalarizedStoreStep ptr 0 valByte 16 mem0 []).2 ≠
      (avx2ScalarizedStoreStep ptr 1 valByte 16 mem0 []).2 ∧
    (∀ k1 k2, (evexMaskedVecStoreWithTrace ptr 16 k1 valByte mem0).2 =
              (evexMaskedVecStoreWithTrace ptr 16 k2 valByte mem0).2) := by
  refine ⟨fun kMask => avx2_vs_evex_1safety_mem_eq ptr 16 kMask valByte mem0 16, ?_, fun _ _ => rfl⟩
  intro hEq
  injection hEq with hHead _
  cases hHead

-- ============================================================================
-- Section 2: Categorical Unsoundness of Write-Side Aligned RMW Slack-Writeback
-- ============================================================================

/-- Exact Tree Borrows per-location permission & transition model matching
    `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`
    (`Miri/TreeBorrows/{Permissions,LocationState}.lean`). -/
inductive TbPerm where
  | cell
  | reservedFrz (conflicted : Bool)
  | reservedIM
  | unique
  | frozen
  | disabled
  deriving DecidableEq

inductive TbAccessKind where
  | read
  | write
  deriving DecidableEq

inductive TbRel where
  | localAcc
  | foreignAcc
  deriving DecidableEq

structure TbLocState where
  perm        : TbPerm
  accessed    : Bool
  isProtected : Bool
  deriving DecidableEq

inductive TbError where
  | childForbidden (p : TbPerm)
  | protectedDisabled (p : TbPerm)
  deriving DecidableEq

inductive TbResult where
  | ok (next : TbLocState)
  | ub (err : TbError)
  deriving DecidableEq

def tbStepPerm (kind : TbAccessKind) (rel : TbRel) (p : TbPerm) (prot : Bool) : Option TbPerm :=
  match kind, rel with
  | .read, .localAcc =>
    match p with
    | .disabled => none
    | okP       => some okP
  | .write, .localAcc =>
    match p with
    | .cell              => some .cell
    | .reservedFrz true  => if prot then none else some .unique
    | .reservedFrz false => some .unique
    | .reservedIM        => some .unique
    | .unique            => some .unique
    | .frozen            => none
    | .disabled          => none
  | .read, .foreignAcc =>
    match p with
    | .cell          => some .cell
    | .frozen        => some .frozen
    | .disabled      => some .disabled
    | .reservedFrz c => some (.reservedFrz (c || prot))
    | .reservedIM    => some .reservedIM
    | .unique        => some (if prot then .disabled else .frozen)
  | .write, .foreignAcc =>
    match p with
    | .cell       => some .cell
    | .reservedIM => some .reservedIM
    | _           => some .disabled

def tbPerformAccess (st : TbLocState) (kind : TbAccessKind) (rel : TbRel) : TbResult :=
  match tbStepPerm kind rel st.perm st.isProtected with
  | none => .ub (.childForbidden st.perm)
  | some nextP =>
    let nextAcc := st.accessed || (match rel with | .localAcc => true | .foreignAcc => false)
    let becameDisabled := (!Nat.beq (match st.perm with | .disabled => 1 | _ => 0) 1) &&
                          (match nextP with | .disabled => true | _ => false)
    if st.isProtected && nextAcc && becameDisabled then
      .ub (.protectedDisabled st.perm)
    else
      .ok { st with perm := nextP, accessed := nextAcc }

/-- Theorem 2.1 (Read-vs-Write Granule Asymmetry under Tree Borrows):
    For an accessed sibling reference `right : &[u8; 16]` (`perm = .frozen, accessed = true`):
    1. Read-only `DemonicGranuleLoad` (`foreignAcc`, `.read`) preserves `.frozen` even under
       an active `FnEntry` `StrongProtector` (`isProtected = true`).
    2. Write-side aligned RMW slack-writeback (`foreignAcc`, `.write`) triggers IMMEDIATE
       `.protectedDisabled .frozen` UB under `isProtected = true`, and transitions an
       unprotected sibling (`isProtected = false`) to `.disabled` so its next read triggers
       `.childForbidden .disabled` UB! -/
theorem read_overread_sound_but_rmw_writeback_ub_under_tree_borrows :
    (∀ prot, tbPerformAccess ⟨.frozen, true, prot⟩ .read .foreignAcc =
             .ok ⟨.frozen, true, prot⟩) ∧
    tbPerformAccess ⟨.frozen, true, true⟩ .write .foreignAcc =
      .ub (.protectedDisabled .frozen) ∧
    (match tbPerformAccess ⟨.frozen, true, false⟩ .write .foreignAcc with
     | .ok poisoned => tbPerformAccess poisoned .read .localAcc = .ub (.childForbidden .disabled)
     | .ub _ => False) ∧
    tbPerformAccess ⟨.reservedFrz false, false, false⟩ .write .localAcc =
      .ok ⟨.unique, true, false⟩ := by
  refine ⟨?_, rfl, rfl, rfl⟩
  intro prot
  cases prot <;> rfl

/-- Concurrent non-atomic RMW slack-writeback schedule tearing an adjacent atomic counter. -/
def thread1RmwLoad32 (algn : Nat) (mem : Mem) : Nat → Nat :=
  fun lane => mem (algn + lane)

def thread1RmwBlendStore32
    (algn sliceLen : Nat) (snap : Nat → Nat) (newVal : Nat → Nat) (mem : Mem) : Mem :=
  writeByteSpan mem algn (fun lane => if lane < sliceLen then newVal lane else snap lane) 32

def thread2AtomicFetchAdd (siblingAddr delta : Nat) (mem : Mem) : Mem :=
  writeByte mem siblingAddr (mem siblingAddr + delta)

/-- Theorem 2.2: Even when `sliceLen = 16` and `thread1RmwBlendStore32` writes back the
    exact bytes `snap lane` read on `[16..32)`, interleaving `thread2AtomicFetchAdd` at
    `algn + 16` between `Load32` and `Store32` loses `thread2`'s committed atomic update! -/
theorem rmw_slack_writeback_causes_concurrent_lost_update
    (algn : Nat) (newVal : Nat → Nat) (mem0 : Mem) :
    let snap := thread1RmwLoad32 algn mem0
    let memAfterT2 := thread2AtomicFetchAdd (algn + 16) 1 mem0
    let memFinal := thread1RmwBlendStore32 algn 16 snap newVal memAfterT2
    memAfterT2 (algn + 16) = mem0 (algn + 16) + 1 ∧
    memFinal (algn + 16) = mem0 (algn + 16) ∧
    memFinal (algn + 16) ≠ memAfterT2 (algn + 16) := by
  dsimp only []
  have ht2 : thread2AtomicFetchAdd (algn + 16) 1 mem0 (algn + 16) = mem0 (algn + 16) + 1 := by
    unfold thread2AtomicFetchAdd
    exact writeByte_same mem0 (algn + 16) (mem0 (algn + 16) + 1)
  have hfin : thread1RmwBlendStore32 algn 16 (thread1RmwLoad32 algn mem0) newVal
      (thread2AtomicFetchAdd (algn + 16) 1 mem0) (algn + 16) = mem0 (algn + 16) := by
    unfold thread1RmwBlendStore32
    rw [writeByteSpan_in _ algn _ 32 (algn + 16) (by omega) (by omega)]
    have hsub : (algn + 16) - algn = 16 := by omega
    rw [hsub]
    have hnlt : ¬ (16 < 16) := by omega
    simp [hnlt, thread1RmwLoad32]
  refine ⟨ht2, hfin, ?_⟩
  rw [ht2, hfin]
  omega

/-- Armv8.5-A 16-byte MTE granule store check (`stp q0, q1` = 32 B across 16 B tag granules). -/
def checkMteStoreSpan (memTag : Nat → Nat) (ptrTag base n0 : Nat) : Option Nat :=
  @Nat.rec (fun _ => Option Nat)
    none
    (fun n ih =>
      match ih with
      | some fa => some fa
      | none =>
        let granIdx := (base + n) / 16
        match Nat.beq (memTag granIdx) ptrTag with
        | true  => none
        | false => some (base + n))
    n0

/-- Theorem 2.3: On 32-byte aligned `base = 0` where `[0..16)` has MTE tag `1` and sibling
    `[16..32)` has MTE tag `2`, 16-byte NEON `str q0` (`n = 16`) succeeds while 32-byte RMW
    `stp q0, q1` (`n = 32`) faults synchronously (`SEGV_MTESERR`) at offset `16`! -/
theorem rmw_slack_writeback_faults_on_mte_16b_granule :
    let tags := fun g => if g = 0 then 1 else 2
    checkMteStoreSpan tags 1 0 16 = none ∧
    checkMteStoreSpan tags 1 0 32 = some 16 :=
  ⟨rfl, rfl⟩

-- ============================================================================
-- Section 3: The Overlapping Unaligned Tail-Store (`[len - W .. len)`) Trichotomy
-- ============================================================================

def specDisjointMap (F : Nat → Nat) (dst src len : Nat) (mem0 : Mem) : Mem :=
  fun q =>
    if dst ≤ q ∧ q < dst + len then
      F (mem0 (src + (q - dst)))
    else
      mem0 q

def specInplaceMap (F : Nat → Nat) (buf len : Nat) (mem0 : Mem) : Mem :=
  specDisjointMap F buf buf len mem0

theorem specInplaceMap_in (F : Nat → Nat) (buf len : Nat) (mem0 : Mem) (q : Nat)
    (hlo : buf ≤ q) (hhi : q < buf + len) :
    specInplaceMap F buf len mem0 q = F (mem0 q) := by
  unfold specInplaceMap specDisjointMap
  simp [hlo, hhi, show buf + (q - buf) = q by omega]

theorem specInplaceMap_out (F : Nat → Nat) (buf len : Nat) (mem0 : Mem) (q : Nat)
    (hout : q < buf ∨ buf + len ≤ q) :
    specInplaceMap F buf len mem0 q = mem0 q := by
  unfold specInplaceMap specDisjointMap
  have hnot : ¬ (buf ≤ q ∧ q < buf + len) := by omega
  simp [hnot]

/-- Snapshot `W` bytes starting at `srcOff` before writing `W` transformed bytes at `dstOff`
    (models loading a `W`-byte SIMD register `ymm := vmovdqu [srcOff]`, transforming each lane
    via `F`, and storing `vmovdqu [dstOff], ymm`). -/
def simdChunkTransform (W : Nat) (F : Nat → Nat) (dstOff srcOff : Nat) (mem : Mem) : Mem :=
  writeByteSpan mem dstOff (fun lane => F (mem (srcOff + lane))) W

theorem simdChunkTransform_in (W : Nat) (F : Nat → Nat) (dstOff srcOff : Nat) (mem : Mem) (q : Nat)
    (hlo : dstOff ≤ q) (hhi : q < dstOff + W) :
    simdChunkTransform W F dstOff srcOff mem q = F (mem (srcOff + (q - dstOff))) := by
  unfold simdChunkTransform
  exact writeByteSpan_in mem dstOff (fun lane => F (mem (srcOff + lane))) W q hlo hhi

theorem simdChunkTransform_out (W : Nat) (F : Nat → Nat) (dstOff srcOff : Nat) (mem : Mem) (q : Nat)
    (hout : q < dstOff ∨ dstOff + W ≤ q) :
    simdChunkTransform W F dstOff srcOff mem q = mem q := by
  unfold simdChunkTransform
  exact writeByteSpan_out mem dstOff (fun lane => F (mem (srcOff + lane))) W q hout

/-- Main `W`-stride loop executing `steps` chunks at offsets `0, W, ..., (steps - 1) * W`. -/
def runMainChunks (W : Nat) (F : Nat → Nat) (dst src : Nat) (mem0 : Mem) (steps : Nat) : Mem :=
  @Nat.rec (fun _ => Mem)
    mem0
    (fun k memK => simdChunkTransform W F (dst + W * k) (src + W * k) memK)
    steps

theorem runMainChunks_zero (W : Nat) (F : Nat → Nat) (dst src : Nat) (mem0 : Mem) :
    runMainChunks W F dst src mem0 0 = mem0 := rfl

theorem runMainChunks_succ (W : Nat) (F : Nat → Nat) (dst src : Nat) (mem0 : Mem) (k : Nat) :
    runMainChunks W F dst src mem0 (k + 1) =
      simdChunkTransform W F (dst + W * k) (src + W * k) (runMainChunks W F dst src mem0 k) := rfl

/-- Number of strict main-loop steps (`while off + W < len`):
    for `len ≥ W` (`W > 0`), `strictSteps W len = (len - 1) / W`, so the main loop covers
    `[0 .. W * ((len - 1) / W))` with `len - W ≤ W * ((len - 1) / W) < len`, followed by ONE
    unconditional branchless tail chunk at `len - W`! -/
def strictSteps (W len : Nat) : Nat :=
  (len - 1) / W

/-- Branchless overlapping-tail kernel for disjoint `(dst, src)` (`len ≥ W`). -/
def disjointOverlapTail (W : Nat) (F : Nat → Nat) (dst src len : Nat) (mem0 : Mem) : Mem :=
  let k := strictSteps W len
  let memLoop := runMainChunks W F dst src mem0 k
  let tailOff := len - W
  simdChunkTransform W F (dst + tailOff) (src + tailOff) memLoop

/-- Branchless overlapping-tail kernel for in-place `buf` WITHOUT tail register preloading:
    reads `buf[len - W .. len)` *after* the main loop has already mutated `[0 .. W * k)`. -/
def inplaceUnbufferedOverlapTail (W : Nat) (F : Nat → Nat) (buf len : Nat) (mem0 : Mem) : Mem :=
  disjointOverlapTail W F buf buf len mem0

/-- Branchless overlapping-tail kernel for in-place `buf` WITH hoisted tail preload:
    reads `tail_in := load(buf[len - W .. len])` from `mem0` before the overlapping main store,
    runs the main loop, and stores `F(tail_in)` to `buf[len - W .. len)`. -/
def inplacePreloadedOverlapTail (W : Nat) (F : Nat → Nat) (buf len : Nat) (mem0 : Mem) : Mem :=
  let k := strictSteps W len
  let tailOff := len - W
  let memLoop := runMainChunks W F buf buf mem0 k
  writeByteSpan memLoop (buf + tailOff) (fun lane => F (mem0 (buf + tailOff + lane))) W

def DisjointSlices (dst src len : Nat) : Prop :=
  dst + len ≤ src ∨ src + len ≤ dst

/-- Key inductive invariant of `runMainChunks` for disjoint `(dst, src)`:
    - `written_prefix`: `dst ≤ q < dst + W * k → memK q = F (mem0 (src + (q - dst)))`
    - `frame_outside`:  `q < dst ∨ dst + W * k ≤ q → memK q = mem0 q` -/
theorem runMainChunks_disjoint_inv
    (W : Nat) (F : Nat → Nat) (dst src len : Nat) (mem0 : Mem)
    (hDisj : DisjointSlices dst src len) :
    ∀ (k : Nat), W * k ≤ len → ∀ (q : Nat),
      (dst ≤ q ∧ q < dst + W * k → runMainChunks W F dst src mem0 k q = F (mem0 (src + (q - dst)))) ∧
      ((q < dst ∨ dst + W * k ≤ q) → runMainChunks W F dst src mem0 k q = mem0 q)
  | 0, _, _ => by
    rw [runMainChunks_zero]
    refine ⟨fun ⟨_, _⟩ => by omega, fun _ => rfl⟩
  | k + 1, hbound, q => by
    have hWk : W * k + W = W * (k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    have ih := runMainChunks_disjoint_inv W F dst src len mem0 hDisj k (by omega)
    refine ⟨?_, ?_⟩
    · intro ⟨hlo, hhi⟩
      rw [runMainChunks_succ]
      exact if hstep : dst + W * k ≤ q then by
        have hhi_step : q < (dst + W * k) + W := by omega
        rw [simdChunkTransform_in W F (dst + W * k) (src + W * k)
              (runMainChunks W F dst src mem0 k) q hstep hhi_step]
        have hsrc_addr : (src + W * k) + (q - (dst + W * k)) = src + (q - dst) := by omega
        rw [hsrc_addr]
        have hsrc_out : src + (q - dst) < dst ∨ dst + W * k ≤ src + (q - dst) := by
          cases hDisj with
          | inl hd => exact Or.inr (by omega)
          | inr hd => exact Or.inl (by omega)
        rw [(ih (src + (q - dst))).2 hsrc_out]
      else by
        have hout_step : q < dst + W * k ∨ (dst + W * k) + W ≤ q := by omega
        rw [simdChunkTransform_out W F (dst + W * k) (src + W * k)
              (runMainChunks W F dst src mem0 k) q hout_step]
        exact (ih q).1 ⟨hlo, by omega⟩
    · intro hout
      rw [runMainChunks_succ]
      have hout_step : q < dst + W * k ∨ (dst + W * k) + W ≤ q := by omega
      rw [simdChunkTransform_out W F (dst + W * k) (src + W * k)
            (runMainChunks W F dst src mem0 k) q hout_step]
      exact (ih q).2 (by omega)

/-- Key inductive 3-region Skolem invariant of `runMainChunks` for IN-PLACE `buf`:
    1. `written_prefix`:           `buf ≤ q < buf + W * k → memK q = F (mem0 q)`
    2. `unwritten_inplace_suffix`: `buf + W * k ≤ q < buf + len → memK q = mem0 q`
    3. `frame_outside`:            `q < buf ∨ buf + len ≤ q → memK q = mem0 q` -/
theorem runMainChunks_inplace_skolem_inv
    (W : Nat) (F : Nat → Nat) (buf len : Nat) (mem0 : Mem) :
    ∀ (k : Nat), W * k ≤ len → ∀ (q : Nat),
      (buf ≤ q ∧ q < buf + W * k → runMainChunks W F buf buf mem0 k q = F (mem0 q)) ∧
      ((q < buf ∨ buf + W * k ≤ q) → runMainChunks W F buf buf mem0 k q = mem0 q)
  | 0, _, _ => by
    rw [runMainChunks_zero]
    refine ⟨fun ⟨_, _⟩ => by omega, fun _ => rfl⟩
  | k + 1, hbound, q => by
    have hWk : W * k + W = W * (k + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    have ih := runMainChunks_inplace_skolem_inv W F buf len mem0 k (by omega)
    refine ⟨?_, ?_⟩
    · intro ⟨hlo, hhi⟩
      rw [runMainChunks_succ]
      exact if hstep : buf + W * k ≤ q then by
        have hhi_step : q < (buf + W * k) + W := by omega
        rw [simdChunkTransform_in W F (buf + W * k) (buf + W * k)
              (runMainChunks W F buf buf mem0 k) q hstep hhi_step]
        have haddr : (buf + W * k) + (q - (buf + W * k)) = q := by omega
        rw [haddr]
        rw [(ih q).2 (Or.inr hstep)]
      else by
        have hout_step : q < buf + W * k ∨ (buf + W * k) + W ≤ q := by omega
        rw [simdChunkTransform_out W F (buf + W * k) (buf + W * k)
              (runMainChunks W F buf buf mem0 k) q hout_step]
        exact (ih q).1 ⟨hlo, by omega⟩
    · intro hout
      rw [runMainChunks_succ]
      have hout_step : q < buf + W * k ∨ (buf + W * k) + W ≤ q := by omega
      rw [simdChunkTransform_out W F (buf + W * k) (buf + W * k)
            (runMainChunks W F buf buf mem0 k) q hout_step]
      exact (ih q).2 (by omega)

theorem strictSteps_bounds (W len : Nat) (hW : W > 0) (hlen : W ≤ len) :
    len - W ≤ W * strictSteps W len ∧ W * strictSteps W len < len := by
  unfold strictSteps
  have hdiv := Nat.div_add_mod (len - 1) W
  have hmod : (len - 1) % W < W := Nat.mod_lt (len - 1) hW
  omega

/-- TRICHOTOMY PART 1 (`disjoint_overlap_tail_universal_soundness`):
    For disjoint `(dst, src)` (`DisjointSlices dst src len`), the branchless overlapping
    tail store `[len - W .. len)` is universally sound for EVERY pure lane function `F`
    (whether idempotent or non-idempotent) across all `W > 0`, `len ≥ W`, and `q : Nat`. -/
theorem disjoint_overlap_tail_universal_soundness
    (W : Nat) (hW : W > 0) (F : Nat → Nat)
    (dst src len : Nat) (hlen : W ≤ len) (hDisj : DisjointSlices dst src len)
    (mem0 : Mem) (q : Nat) :
    disjointOverlapTail W F dst src len mem0 q = specDisjointMap F dst src len mem0 q := by
  dsimp only [disjointOverlapTail]
  unfold specDisjointMap
  have ⟨hTailLo, hLoopHi⟩ := strictSteps_bounds W len hW hlen
  have hInv := runMainChunks_disjoint_inv W F dst src len mem0 hDisj
    (strictSteps W len) (by omega)
  exact if hInSlice : dst ≤ q ∧ q < dst + len then by
    rcases hInSlice with ⟨hqLo, hqHi⟩
    simp [hqLo, hqHi]
    exact if hInTail : dst + (len - W) ≤ q then by
      rw [simdChunkTransform_in W F (dst + (len - W)) (src + (len - W))
            (runMainChunks W F dst src mem0 (strictSteps W len)) q hInTail (by omega)]
      have hsrcAddr : (src + (len - W)) + (q - (dst + (len - W))) = src + (q - dst) := by omega
      rw [hsrcAddr]
      have hSrcOut : src + (q - dst) < dst ∨ dst + W * strictSteps W len ≤ src + (q - dst) := by
        cases hDisj with
        | inl hd => exact Or.inr (by omega)
        | inr hd => exact Or.inl (by omega)
      rw [(hInv (src + (q - dst))).2 hSrcOut]
    else by
      rw [simdChunkTransform_out W F (dst + (len - W)) (src + (len - W))
            (runMainChunks W F dst src mem0 (strictSteps W len)) q (Or.inl (by omega))]
      exact (hInv q).1 ⟨hqLo, by omega⟩
  else by
    simp [hInSlice]
    have hOutTail : q < dst + (len - W) ∨ (dst + (len - W)) + W ≤ q := by omega
    rw [simdChunkTransform_out W F (dst + (len - W)) (src + (len - W))
          (runMainChunks W F dst src mem0 (strictSteps W len)) q hOutTail]
    exact (hInv q).2 (by omega)

/-- TRICHOTOMY PART 2A (`inplace_unbuffered_overlap_tail_sound_of_idempotent`):
    For in-place `buf` WITHOUT tail register preloading, if `F` is idempotent
    (`∀ b, F (F b) = F b`), then `inplaceUnbufferedOverlapTail` is universally sound! -/
theorem inplace_unbuffered_overlap_tail_sound_of_idempotent
    (W : Nat) (hW : W > 0) (F : Nat → Nat) (hIdem : ∀ b, F (F b) = F b)
    (buf len : Nat) (hlen : W ≤ len) (mem0 : Mem) (q : Nat) :
    inplaceUnbufferedOverlapTail W F buf len mem0 q = specInplaceMap F buf len mem0 q := by
  dsimp only [inplaceUnbufferedOverlapTail, disjointOverlapTail]
  have ⟨hTailLo, hLoopHi⟩ := strictSteps_bounds W len hW hlen
  have hInv := runMainChunks_inplace_skolem_inv W F buf len mem0
    (strictSteps W len) (by omega)
  exact if hInSlice : buf ≤ q ∧ q < buf + len then by
    rcases hInSlice with ⟨hqLo, hqHi⟩
    rw [specInplaceMap_in F buf len mem0 q hqLo hqHi]
    exact if hInTail : buf + (len - W) ≤ q then by
      rw [simdChunkTransform_in W F (buf + (len - W)) (buf + (len - W))
            (runMainChunks W F buf buf mem0 (strictSteps W len)) q hInTail (by omega)]
      have hqAddr : (buf + (len - W)) + (q - (buf + (len - W))) = q := by omega
      rw [hqAddr]
      exact if hInOverlap : q < buf + W * strictSteps W len then by
        rw [(hInv q).1 ⟨hqLo, hInOverlap⟩]
        exact hIdem (mem0 q)
      else by
        rw [(hInv q).2 (Or.inr (by omega))]
    else by
      rw [simdChunkTransform_out W F (buf + (len - W)) (buf + (len - W))
            (runMainChunks W F buf buf mem0 (strictSteps W len)) q (Or.inl (by omega))]
      exact (hInv q).1 ⟨hqLo, by omega⟩
  else by
    have hOut : q < buf ∨ buf + len ≤ q := by omega
    rw [specInplaceMap_out F buf len mem0 q hOut]
    have hOutTail : q < buf + (len - W) ∨ (buf + (len - W)) + W ≤ q := by omega
    rw [simdChunkTransform_out W F (buf + (len - W)) (buf + (len - W))
          (runMainChunks W F buf buf mem0 (strictSteps W len)) q hOutTail]
    exact (hInv q).2 (by omega)

/-- Concrete idempotent SIMD byte operations: `asciiTolower`, `clampRange`, `bitmaskClear`. -/
def asciiTolowerByte (b : Nat) : Nat :=
  let u := b % 256
  if 65 ≤ u ∧ u ≤ 90 then u + 32 else u

def clampByte (lo hi b : Nat) : Nat :=
  let u := b % 256
  if u < lo then lo else if hi < u then hi else u

def bitmaskClearByte (clearMask b : Nat) : Nat :=
  Nat.land (b % 256) (clearMask % 256)

theorem asciiTolowerByte_idempotent (b : Nat) :
    asciiTolowerByte (asciiTolowerByte b) = asciiTolowerByte b := by
  unfold asciiTolowerByte
  dsimp only []
  split <;> split <;> omega

theorem clampByte_idempotent (lo hi b : Nat) (hRange : lo ≤ hi ∧ hi < 256) :
    clampByte lo hi (clampByte lo hi b) = clampByte lo hi b := by
  unfold clampByte
  dsimp only []
  (try split) <;> (try split) <;> (try split) <;> (try split) <;> omega

/-- Exact masking at `len = W` (`len = 32` for AVX2): even when `F` is NON-idempotent,
    `len = W` executes `strictSteps W W = 0` main-loop iterations (`(W - 1) / W = 0`),
    so `len = W` NEVER overlaps and silently passes power-of-two unit tests! -/
theorem len_eq_W_hides_nonidempotent_bug
    (W : Nat) (hW : W > 0) (F : Nat → Nat) (buf : Nat) (mem0 : Mem) (q : Nat) :
    inplaceUnbufferedOverlapTail W F buf W mem0 q = specInplaceMap F buf W mem0 q := by
  dsimp only [inplaceUnbufferedOverlapTail, disjointOverlapTail]
  unfold strictSteps
  have hdiv : (W - 1) / W = 0 := Nat.div_eq_of_lt (by omega)
  have hsub : W - W = 0 := Nat.sub_self W
  rw [hdiv, hsub, Nat.add_zero, runMainChunks_zero]
  exact if hin : buf ≤ q ∧ q < buf + W then by
    rw [simdChunkTransform_in W F buf buf mem0 q hin.1 hin.2]
    rw [specInplaceMap_in F buf W mem0 q hin.1 hin.2]
    have hq : buf + (q - buf) = q := by omega
    rw [hq]
  else by
    have hout : q < buf ∨ buf + W ≤ q := by omega
    rw [simdChunkTransform_out W F buf buf mem0 q hout]
    rw [specInplaceMap_out F buf W mem0 q hout]

/-- TRICHOTOMY PART 2B (`len_W_plus_1_minimal_counterexample_nonidempotent`):
    Whenever `F (F b0) ≠ F b0` and `W ≥ 2`, `len = W + 1` (`len = 33` for `W = 32`) is the
    minimal counterexample length: EVERY overlap byte `q ∈ [buf + 1, buf + W)` receives
    `F (F b0)` instead of `F b0`! -/
theorem len_W_plus_1_minimal_counterexample_nonidempotent
    (W : Nat) (hW2 : 2 ≤ W) (F : Nat → Nat) (b0 : Nat) (hNonIdem : F (F b0) ≠ F b0)
    (buf q : Nat) (hqLo : buf + 1 ≤ q) (hqHi : q < buf + W) :
    let mem0 : Mem := fun _ => b0
    inplaceUnbufferedOverlapTail W F buf (W + 1) mem0 q = F (F b0) ∧
    specInplaceMap F buf (W + 1) mem0 q = F b0 ∧
    inplaceUnbufferedOverlapTail W F buf (W + 1) mem0 q ≠
      specInplaceMap F buf (W + 1) mem0 q := by
  dsimp only []
  have hsteps : strictSteps W (W + 1) = 1 := by
    unfold strictSteps
    have : (W + 1) - 1 = W := by omega
    rw [this]
    exact Nat.div_self (by omega)
  have hsub : (W + 1) - W = 1 := by omega
  have hval : inplaceUnbufferedOverlapTail W F buf (W + 1) (fun _ => b0) q = F (F b0) := by
    dsimp only [inplaceUnbufferedOverlapTail, disjointOverlapTail]
    rw [hsteps, hsub, runMainChunks_succ, runMainChunks_zero]
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [simdChunkTransform_in W F (buf + 1) (buf + 1)
          (simdChunkTransform W F buf buf (fun _ => b0)) q hqLo (by omega)]
    have hqAddr : (buf + 1) + (q - (buf + 1)) = q := by omega
    rw [hqAddr]
    rw [simdChunkTransform_in W F buf buf (fun _ => b0) q (by omega) hqHi]
  have hspec : specInplaceMap F buf (W + 1) (fun _ => b0) q = F b0 :=
    specInplaceMap_in F buf (W + 1) (fun _ => b0) q (by omega) (by omega)
  exact ⟨hval, hspec, by rw [hval, hspec]; exact hNonIdem⟩

/-- Exact Necessary & Sufficient Biconditional Characterization (`W ≥ 2`):
    Unbuffered in-place overlapping tail `[len - W .. len)` is sound for all `len ≥ W`
    IF AND ONLY IF `F` is byte-idempotent (`∀ b, F (F b) = F b`). -/
theorem inplace_unbuffered_overlap_tail_sound_iff_idempotent
    (W : Nat) (hW2 : 2 ≤ W) (F : Nat → Nat) (buf : Nat) :
    (∀ len, W ≤ len → ∀ mem0 q,
      inplaceUnbufferedOverlapTail W F buf len mem0 q = specInplaceMap F buf len mem0 q) ↔
    (∀ b, F (F b) = F b) := by
  refine ⟨?_, ?_⟩
  · intro hAll b
    exact if hEq : F (F b) = F b then
      hEq
    else by
      exfalso
      have ⟨_, _, hNe⟩ :=
        len_W_plus_1_minimal_counterexample_nonidempotent W hW2 F b hEq buf (buf + 1)
          (by omega) (by omega)
      exact hNe (hAll (W + 1) (by omega) (fun _ => b) (buf + 1))
  · intro hIdem len hlen mem0 q
    exact inplace_unbuffered_overlap_tail_sound_of_idempotent W (by omega) F hIdem buf len hlen mem0 q

/-- Concrete AVX2 `W = 32` instantiation on `xorByte key` (`key = 1`):
    passes at `len = 32`, fails at minimal `len = 33` on `buf + 1` (`0 ^ 1 ^ 1 = 0 ≠ 1`). -/
def xorByte (key b : Nat) : Nat := Nat.xor (b % 256) (key % 256)

theorem avx2_xor_inplace_unbuffered_len32_ok_len33_fails (buf : Nat) :
    (∀ mem0 q, inplaceUnbufferedOverlapTail 32 (xorByte 1) buf 32 mem0 q =
               specInplaceMap (xorByte 1) buf 32 mem0 q) ∧
    inplaceUnbufferedOverlapTail 32 (xorByte 1) buf 33 (fun _ => 0) (buf + 1) = 0 ∧
    specInplaceMap (xorByte 1) buf 33 (fun _ => 0) (buf + 1) = 1 := by
  refine ⟨fun mem0 q => len_eq_W_hides_nonidempotent_bug 32 (by omega) (xorByte 1) buf mem0 q, ?_⟩
  have hNonIdem : xorByte 1 (xorByte 1 0) ≠ xorByte 1 0 := by decide
  have ⟨hGot, hExp, _⟩ :=
    len_W_plus_1_minimal_counterexample_nonidempotent 32 (by omega) (xorByte 1) 0 hNonIdem
      buf (buf + 1) (by omega) (by omega)
  have h0 : xorByte 1 (xorByte 1 0) = 0 := rfl
  have h1 : xorByte 1 0 = 1 := rfl
  rw [h0] at hGot
  rw [h1] at hExp
  exact ⟨hGot, hExp⟩

/-- TRICHOTOMY PART 3 (`inplace_preloaded_overlap_tail_universal_soundness`):
    Hoisting the unaligned tail load `tail_in := load(buf[len - W .. len])` into a SIMD
    register BEFORE the overlapping loop store makes in-place overlapping tail stores
    universally sound for EVERY `F : Nat → Nat` (including non-idempotent XOR, byte-swap,
    nibble-LUT remap, and wrapping add)! -/
theorem inplace_preloaded_overlap_tail_universal_soundness
    (W : Nat) (hW : W > 0) (F : Nat → Nat)
    (buf len : Nat) (hlen : W ≤ len) (mem0 : Mem) (q : Nat) :
    inplacePreloadedOverlapTail W F buf len mem0 q = specInplaceMap F buf len mem0 q := by
  dsimp only [inplacePreloadedOverlapTail]
  have ⟨hTailLo, hLoopHi⟩ := strictSteps_bounds W len hW hlen
  have hInv := runMainChunks_inplace_skolem_inv W F buf len mem0
    (strictSteps W len) (by omega)
  exact if hInSlice : buf ≤ q ∧ q < buf + len then by
    rcases hInSlice with ⟨hqLo, hqHi⟩
    rw [specInplaceMap_in F buf len mem0 q hqLo hqHi]
    exact if hInTail : buf + (len - W) ≤ q then by
      rw [writeByteSpan_in (runMainChunks W F buf buf mem0 (strictSteps W len)) (buf + (len - W))
            (fun lane => F (mem0 (buf + (len - W) + lane))) W q hInTail (by omega)]
      have hqAddr : buf + (len - W) + (q - (buf + (len - W))) = q := by omega
      rw [hqAddr]
    else by
      rw [writeByteSpan_out (runMainChunks W F buf buf mem0 (strictSteps W len))
            (buf + (len - W)) _ W q (Or.inl (by omega))]
      exact (hInv q).1 ⟨hqLo, by omega⟩
  else by
    have hOut : q < buf ∨ buf + len ≤ q := by omega
    rw [specInplaceMap_out F buf len mem0 q hOut]
    have hOutTail : q < buf + (len - W) ∨ (buf + (len - W)) + W ≤ q := by omega
    rw [writeByteSpan_out (runMainChunks W F buf buf mem0 (strictSteps W len))
          (buf + (len - W)) _ W q hOutTail]
    exact (hInv q).2 (by omega)

end MutatingSimdTheory
