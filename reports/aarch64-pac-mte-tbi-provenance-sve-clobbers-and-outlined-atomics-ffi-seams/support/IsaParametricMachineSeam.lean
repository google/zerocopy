-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.Nat.Bitwise.Basic
import Init.Data.List.Basic
import Init.Data.List.Notation

/-!
# ISA-Parametric MIR-to-ISA Machine Seam (`x86_64` vs. `AArch64`)

Pass-1 Lean 4 (`v4.34.1`) mechanization of three hardware seams where `x86_64`
assumptions fail on `AArch64`:

1. **Upper-Bit Pointer Tagging (`TaggedAddrPolicy`) vs. Kripke Address Valuation:**
   Covers `x86_64` 48-bit canonical sign-extension and Linux `LAM_U57` (`[62:57]`)
   alongside `AArch64` EL0 `TBI0` (`[63:56]`), `MTE` 4-bit allocation tags
   (`[59:56]`), and `PAC` pointer authentication (`[54:vaBits]`) across
   `FEAT_FPAC` synchronous faulting vs. pre-FPAC `FEAT_EPAC` XOR poisoning and
   unauthenticated `XPAC*` stripping hazards.
2. **Bit-Slice Callee-Save and Flag Preservation (`RegSaveContract`):**
   Captures `x86_64` SysV vs. Win64 (`xmm6..15` low 128 bits), `AArch64` Base PCS
   (`v8..15` low 64-bit `d8..15` only, architecturally zeroing `[VL-1:64]` upon
   `ldr d8`) vs. `AArch64` SVE PCS (`z8..23` full `[VL-1:0]`), and the gap
   between normative Rust `options(preserves_flags)` (`NZCV` + `FPSR`) and
   `rustc`'s AArch64 `~{cc}` (`NZCV`-only) LLVM constraint lowering.
3. **Nondeterministic `ExclusiveMonitor` (`LDXR`/`STXR`) and Outlined Atomics:**
   Refutes fixed-step execution bounds under adversarial exclusive-monitor clears,
   proves partial safety under arbitrary spurious-clear schedules and total RMW
   refinement under fair schedules, proves observational equivalence between LSE
   and LL/SC paths of `__aarch64_*` outlined atomics, and proves that nested
   outlined CAS calls invalidate outer `LDXR` reservations.

Conforms strictly to Pass-1 `prelude` + `Init.*` rules: zero `sorry`, zero custom
`axiom`, zero `deriving`/`partial`/`unsafe`/`._unsafe_rec`, and zero
`omega`/`bv_decide`/`native_decide`/`Lean.ofReduceBool`.
-/

namespace IsaParametricSeam

/-! ## Elementary Structural `Nat` Equality Helpers -/

def natEq : Nat → Nat → Bool
  | 0, 0 => true
  | a + 1, b + 1 => natEq a b
  | _, _ => false

theorem natEq_refl (n : Nat) : natEq n n = true := by
  induction n with
  | zero => rfl
  | succ k ih => exact ih

theorem natLt_succ_or_eq {j k : Nat} (h : j < k + 1) : j < k ∨ j = k := by
  cases Nat.le_of_lt_succ h with
  | refl => exact Or.inr rfl
  | step hLe => exact Or.inl (Nat.lt_succ_of_le hLe)

/-! ## Section 1: Upper-Bit Pointer Tagging, PAC, MTE, and Kripke Valuation -/

/-- Cryptographic key selector for Armv8.3+ Pointer Authentication. -/
inductive PacKey where
  | ia | ib | da | db

/-- Hardware fault behavior on failed `AUT*` authentication. -/
inductive FpacMode where
  /-- Armv8.6+ `FEAT_FPAC`: `AUT*` faults synchronously (`SIGILL`) on mismatch. -/
  | fpacSync
  /-- Pre-FPAC `FEAT_EPAC` (`neoverse-v1`): `AUT*` XORs MAC without faulting,
      leaving a non-canonical poisoned upper field unless stripped by `XPAC*`. -/
  | preFpacXor

/-- Structured decomposition of a 64-bit pointer register across `x86_64` and
    `AArch64` `VA48` hardware bit partitions:
    - `va48`: virtual address bits `[47:0]`
    - `pacBits`: bits `[54:48]` (`PAC` signature on `AArch64` `VA48` + `TBI0`;
      sign-extension on `x86_64` 4-level paging)
    - `bit55`: `TTBR0`/`TTBR1` selector on `AArch64` (`false` = EL0 user)
    - `mteTag`: bits `[59:56]` (`MTE` 4-bit logical tag on `AArch64`; part of
      `LAM_U57` `[62:57]` / canonical sign-ext on `x86_64`)
    - `swTop`: bits `[63:60]` (`TBI0` free software nibble on `AArch64`; bit 63
      must remain `0` for user addresses under Linux `x86_64` `LAM_U57`) -/
structure PtrWord64 where
  va48    : Nat
  pacBits : Nat
  bit55   : Bool
  mteTag  : Nat
  swTop   : Nat

/-- Target-parametric upper-bit address translation and tag-enforcement policy. -/
inductive TaggedAddrPolicy where
  /-- Standard `x86_64` 4-level user-mode canonical addressing (`[63:47] == 0`). -/
  | x86_64_canonical48
  /-- Linux `x86_64` `LAM_U57` user-mode addressing (tags in `[62:57]`, bit 63 = 0). -/
  | x86_64_lam_u57
  /-- `AArch64` Linux EL0 `VA48` with `TBI0 = 1`, optional synchronous `MTE`
      (`PR_MTE_TCF_SYNC`), and `PAC` (`GENMASK_ULL(54, 48)`). -/
  | aarch64_tbi0_mte_pac (mteSyncEnabled : Bool) (fpacMode : FpacMode)

/-- Extract the translated 48-bit virtual address (`canonicalizeAddr`), stripping
    hardware-ignored upper tag bytes (`TBI0` `[63:56]` or `LAM_U57` `[62:57]`). -/
def canonicalizeAddr (pol : TaggedAddrPolicy) (w : PtrWord64) : Nat :=
  match pol with
  | .x86_64_canonical48 => w.va48
  | .x86_64_lam_u57 => w.va48
  | .aarch64_tbi0_mte_pac _ _ => w.va48

/-- Whether `w` satisfies the target's user-mode canonical / translation-fault
    invariants at memory dereference (`LDR`/`STR`/`MOV`).
    On `AArch64` `TBI0 = 1`, `[63:56]` (`mteTag`, `swTop`) are ignored by MMU
    translation, whereas non-zero `pacBits` (`[54:48]`) or `bit55 = true`
    trigger an immediate translation fault. -/
def isTranslationCanonical (pol : TaggedAddrPolicy) (w : PtrWord64) : Bool :=
  match pol with
  | .x86_64_canonical48 =>
      Nat.ble (w.va48 + 1) (2 ^ 47) &&
      natEq w.pacBits 0 && (!w.bit55) && natEq w.mteTag 0 && natEq w.swTop 0
  | .x86_64_lam_u57 =>
      Nat.ble (w.va48 + 1) (2 ^ 47) &&
      natEq w.pacBits 0 && (!w.bit55) && natEq (w.mteTag % 2) 0 && Nat.ble (w.swTop + 1) 8
  | .aarch64_tbi0_mte_pac _ _ =>
      Nat.ble (w.va48 + 1) (2 ^ 48) &&
      natEq w.pacBits 0 && (!w.bit55)

/-- Hardware allocation-tag check (`MTE` compares `w.mteTag` `[59:56]` against the
    16-byte granule's physical allocation tag when `mteSyncEnabled = true`). -/
def hardwareTagMatches (pol : TaggedAddrPolicy) (w : PtrWord64) (granuleTag : Nat) : Bool :=
  match pol with
  | .x86_64_canonical48 => true
  | .x86_64_lam_u57 => true
  | .aarch64_tbi0_mte_pac false _ => true
  | .aarch64_tbi0_mte_pac true _ => natEq w.mteTag granuleTag

/-- First-order Kripke address map `α` resolving canonical virtual addresses to
    `(allocId, byteOffset)` together with per-granule MTE tag and byte storage. -/
structure TaggedFlatMem where
  resolveAddr : Nat → Option (Nat × Nat)
  granuleTag  : Nat → Nat → Nat
  readByte    : Nat → Nat → Nat

inductive DerefOutcome where
  | ok (byte : Nat)
  | nonCanonicalFault
  | mteTagFault
  | pacAuthFault

/-- ISA-parametric load semantics over a `PtrWord64`. -/
def isaLoadByte (pol : TaggedAddrPolicy) (mem : TaggedFlatMem) (w : PtrWord64) : DerefOutcome :=
  match isTranslationCanonical pol w with
  | false => .nonCanonicalFault
  | true =>
      match mem.resolveAddr (canonicalizeAddr pol w) with
      | none => .nonCanonicalFault
      | some (allocId, off) =>
          match hardwareTagMatches pol w (mem.granuleTag allocId off) with
          | false => .mteTagFault
          | true => .ok (mem.readByte allocId off)

/-- Abstract non-zero 7-bit PAC MAC oracle `computePac(key, modifier, va48)`. -/
abbrev PacMacOracle := PacKey → Nat → Nat → Nat

/-- `PACDA` / `PACIA` under `FEAT_EPAC`: XORs computed MAC into `pacBits` `[54:48]`,
    preserving `TBI0` bits `[63:56]` (`mteTag` and `swTop`). -/
def pacSign (mac : PacMacOracle) (k : PacKey) (modifier : Nat) (w : PtrWord64) : PtrWord64 :=
  { w with pacBits := Nat.xor w.pacBits (mac k modifier w.va48) }

/-- Unauthenticated `XPACD` / `XPACI`: strips `pacBits` `[54:48]` to `0` WITHOUT
    verifying the key or modifier! -/
def xpacStrip (w : PtrWord64) : PtrWord64 :=
  { w with pacBits := 0 }

/-- Authenticated `AUTDA` / `AUTIA`:
    - Under `FEAT_FPAC` (`fpacSync`), a wrong signature faults immediately (`none`).
    - Under pre-FPAC `FEAT_EPAC` (`preFpacXor`), `AUT*` XORs the MAC without
      faulting, returning residual `Nat.xor w.pacBits expected`. -/
def autAuthenticate
    (mode : FpacMode) (mac : PacMacOracle) (k : PacKey) (modifier : Nat) (w : PtrWord64)
    : Option PtrWord64 :=
  let expected := mac k modifier w.va48
  match mode with
  | .fpacSync =>
      match natEq w.pacBits expected with
      | true => some { w with pacBits := 0 }
      | false => none
  | .preFpacXor =>
      some { w with pacBits := Nat.xor w.pacBits expected }

def tbiWitnessPol : TaggedAddrPolicy := .aarch64_tbi0_mte_pac false .fpacSync

def tbiWitnessMem : TaggedFlatMem where
  resolveAddr := fun a => match natEq a 16 with | true => some (1, 0) | false => none
  granuleTag  := fun _ _ => 0
  readByte    := fun _ _ => 0x42

def tbiPtrRaw : PtrWord64 :=
  { va48 := 16, pacBits := 0, bit55 := false, mteTag := 0, swTop := 0 }

def tbiPtrTagged0xA5 : PtrWord64 :=
  { va48 := 16, pacBits := 0, bit55 := false, mteTag := 5, swTop := 10 }

/-- **Theorem 1 (`naive_raw_word_eq_refuted_by_aarch64_tbi0`):**
    On AArch64 `TBI0 = 1`, equating a 64-bit pointer register `w` syntactically to
    the untagged Kripke address word is false: `tbiPtrTagged0xA5` (`0xA5` in
    `[63:56]`) and `tbiPtrRaw` (`0x00` in `[63:56]`) satisfy `tbiPtrRaw ≠ tbiPtrTagged0xA5`,
    yet `isaLoadByte` resolves both to the exact same Kripke allocation byte!
    Meanwhile, on `x86_64_canonical48`, `tbiPtrTagged0xA5` faults immediately
    (`.nonCanonicalFault`). -/
theorem naive_raw_word_eq_refuted_by_aarch64_tbi0 :
    tbiPtrRaw ≠ tbiPtrTagged0xA5 ∧
    isaLoadByte tbiWitnessPol tbiWitnessMem tbiPtrRaw = .ok 0x42 ∧
    isaLoadByte tbiWitnessPol tbiWitnessMem tbiPtrTagged0xA5 = .ok 0x42 ∧
    isaLoadByte .x86_64_canonical48 tbiWitnessMem tbiPtrTagged0xA5 = .nonCanonicalFault :=
  And.intro
    (fun hEq => PtrWord64.noConfusion hEq (fun _ _ _ hMte _ => Nat.noConfusion hMte))
    (And.intro rfl (And.intro rfl rfl))

def mteWitnessPol : TaggedAddrPolicy := .aarch64_tbi0_mte_pac true .fpacSync

def mteWitnessMem : TaggedFlatMem where
  resolveAddr := fun a => match natEq a 32 with | true => some (7, 0) | false => none
  granuleTag  := fun _ _ => 5
  readByte    := fun _ _ => 0xAA

def mtePtrTag5 : PtrWord64 :=
  { va48 := 32, pacBits := 0, bit55 := false, mteTag := 5, swTop := 0 }

def mtePtrUntagged : PtrWord64 :=
  { va48 := 32, pacBits := 0, bit55 := false, mteTag := 0, swTop := 0 }

/-- **Theorem 2 (`canonical_addr_alone_unsound_for_mte`):**
    Under synchronous `MTE` (`PR_MTE_TCF_SYNC`), stripping upper bits via
    `canonicalizeAddr` alone is insufficient for memory safety: `mtePtrTag5` and
    `mtePtrUntagged` share the *exact same* canonical address `32`, yet
    `mtePtrTag5` loads `.ok 0xAA` while `mtePtrUntagged` faults with `.mteTagFault`. -/
theorem canonical_addr_alone_unsound_for_mte :
    canonicalizeAddr mteWitnessPol mtePtrTag5 = canonicalizeAddr mteWitnessPol mtePtrUntagged ∧
    isaLoadByte mteWitnessPol mteWitnessMem mtePtrTag5 = .ok 0xAA ∧
    isaLoadByte mteWitnessPol mteWitnessMem mtePtrUntagged = .mteTagFault :=
  And.intro rfl (And.intro rfl rfl)

def pacWitnessMac : PacMacOracle := fun _ _ _ => 0x1D

/-- **Theorem 3 (`pre_fpac_xpac_gadget_bypasses_corrupted_pac_vs_fpac_blocks`):**
    Formalizes the exact empirical split observed between `-cpu neoverse-v1`
    (`FEAT_EPAC` without `FEAT_FPAC`) and `-cpu max` (`FEAT_FPAC`):
    Given a signed pointer whose PAC bits are corrupted (`0x1D -> 0x1F`):
    1. Under `FEAT_FPAC` (`fpacSync`), `autAuthenticate` immediately rejects the
       forged pointer (`= none`), preventing any subsequent `XPAC*` gadget.
    2. Under pre-FPAC (`preFpacXor`), `autAuthenticate` returns `some poisoned`
       (`pacBits = 2`), which faults if dereferenced directly (`.nonCanonicalFault`),
       **but** applying `xpacStrip` (`XPACD`) to `poisoned` silently recovers a
       valid pointer that loads `.ok 0x42`! -/
theorem pre_fpac_xpac_gadget_bypasses_corrupted_pac_vs_fpac_blocks :
    let signed := pacSign pacWitnessMac .da 0x1111 tbiPtrRaw
    let forged := { signed with pacBits := 0x1F }
    let poisoned : PtrWord64 := { va48 := 16, pacBits := 2, bit55 := false, mteTag := 0, swTop := 0 }
    autAuthenticate .fpacSync pacWitnessMac .da 0x1111 forged = none ∧
    autAuthenticate .preFpacXor pacWitnessMac .da 0x1111 forged = some poisoned ∧
    isaLoadByte (.aarch64_tbi0_mte_pac false .preFpacXor) tbiWitnessMem poisoned = .nonCanonicalFault ∧
    isaLoadByte (.aarch64_tbi0_mte_pac false .preFpacXor) tbiWitnessMem (xpacStrip poisoned) = .ok 0x42 :=
  And.intro rfl (And.intro rfl (And.intro rfl rfl))

/-- **Theorem 4 (`valid_aut_restores_tbi_tagged_ptr`):**
    Valid `PACDA` + `AUTDA` round-trips cleanly under both `fpacSync` and
    `preFpacXor` while preserving `TBI0` upper-byte tags (`mteTag` and `swTop`). -/
theorem valid_aut_restores_tbi_tagged_ptr :
    let signed := pacSign pacWitnessMac .da 0x77 tbiPtrTagged0xA5
    autAuthenticate .fpacSync pacWitnessMac .da 0x77 signed = some tbiPtrTagged0xA5 ∧
    autAuthenticate .preFpacXor pacWitnessMac .da 0x77 signed = some tbiPtrTagged0xA5 :=
  And.intro rfl rfl

/-- ISA-parametric pointer-validity predicate connecting `PtrWord64` to Kripke `(allocId, off)`. -/
def ValidIsaPtr
    (pol : TaggedAddrPolicy) (mem : TaggedFlatMem) (w : PtrWord64) (allocId off : Nat) : Prop :=
  isTranslationCanonical pol w = true ∧
  mem.resolveAddr (canonicalizeAddr pol w) = some (allocId, off) ∧
  hardwareTagMatches pol w (mem.granuleTag allocId off) = true

/-- **Theorem 5 (`isa_parametric_load_sound`):**
    Across all `TaggedAddrPolicy` instances (`x86_64` canonical, `x86_64` `LAM_U57`,
    and `AArch64` `TBI0` + `MTE` + `PAC`), `ValidIsaPtr` guarantees fault-free
    access to the exact Kripke byte `(allocId, off)`. -/
theorem isa_parametric_load_sound
    (pol : TaggedAddrPolicy) (mem : TaggedFlatMem) (w : PtrWord64) (allocId off : Nat)
    (hValid : ValidIsaPtr pol mem w allocId off) :
    isaLoadByte pol mem w = .ok (mem.readByte allocId off) := by
  cases hValid with
  | intro hCan hRest =>
    cases hRest with
    | intro hRes hTag =>
      unfold isaLoadByte
      rw [hCan]
      dsimp only
      rw [hRes]
      dsimp only
      rw [hTag]

/-! ## Section 2: Bit-Slice Callee-Save & Status-Register Preservation (`RegSaveMask`) -/

/-- Sub-register bit-slice preservation width for vector / general-purpose registers. -/
inductive SliceMask where
  | volatile        -- 0 bits preserved
  | low64           -- bits [63:0] preserved (`d8..d15` on AArch64 Base PCS; 64-bit GPRs)
  | low128          -- bits [127:0] preserved (`xmm6..xmm15` on Windows x64)
  | fullVec         -- full vector width [VL-1:0] preserved (`z8..z23` on AArch64 SVE PCS)

/-- Scalable vector register state decomposing `[63:0]`, `[127:64]`, and
    scalable upper lanes `[VL-1:128]` so partial-register clobbers are exact. -/
structure VecRegVal where
  lo64     : Nat
  hi64_128 : Nat
  sveUpper : List Nat

/-- Architectural AArch64 `LDR Dn` / `FMOV Dn` write rule (`ARM DDI 0487`):
    writing the 64-bit `D` view of a vector register sets `[63:0]` AND
    **unconditionally zeroes bits `[VL-1:64]`** (`hi64_128 := 0`, `sveUpper := 0s`)! -/
def writeNeonDReg (old : VecRegVal) (val64 : Nat) : VecRegVal :=
  { lo64 := val64, hi64_128 := 0, sveUpper := old.sveUpper.map (fun _ => 0) }

/-- Whether `post` preserves the required `SliceMask` of `pre`. -/
def slicePreserved (m : SliceMask) (pre post : VecRegVal) : Prop :=
  match m with
  | .volatile => True
  | .low64    => post.lo64 = pre.lo64
  | .low128   => post.lo64 = pre.lo64 ∧ post.hi64_128 = pre.hi64_128
  | .fullVec  => post = pre

theorem slicePreserved_trans (m : SliceMask) (a b d : VecRegVal)
    (h1 : slicePreserved m a b) (h2 : slicePreserved m b d) :
    slicePreserved m a d := by
  cases m with
  | volatile => trivial
  | low64 => exact Eq.trans h2 h1
  | low128 => exact And.intro (Eq.trans h2.1 h1.1) (Eq.trans h2.2 h1.2)
  | fullVec => exact Eq.trans h2 h1

/-- Relevant machine register and status-flag state across a call or `asm!` seam. -/
structure MachineRegState where
  gprCalleeSaved : Nat → Nat
  vecReg         : Nat → VecRegVal
  svePredReg     : Nat → Nat
  nzcv           : Nat
  fpsrSticky     : Nat
  fpcrControl    : Nat

/-- Parametric ABI / `asm!` preservation contract across ISAs and PCS variants. -/
structure RegSaveContract where
  gprSaved      : Nat → Bool
  vecMask       : Nat → SliceMask
  predSaved     : Nat → Bool
  preserveNzcv  : Bool
  preserveFpsr  : Bool
  preserveFpcr  : Bool

def SatisfiesRegContract (c : RegSaveContract) (pre post : MachineRegState) : Prop :=
  (∀ r, c.gprSaved r = true → post.gprCalleeSaved r = pre.gprCalleeSaved r) ∧
  (∀ v, slicePreserved (c.vecMask v) (pre.vecReg v) (post.vecReg v)) ∧
  (∀ p, c.predSaved p = true → post.svePredReg p = pre.svePredReg p) ∧
  (c.preserveNzcv = true → post.nzcv = pre.nzcv) ∧
  (c.preserveFpsr = true → post.fpsrSticky = pre.fpsrSticky) ∧
  (c.preserveFpcr = true → post.fpcrControl = pre.fpcrControl)

/-- AAPCS64 Base Procedure Call Standard: `v8..v15` preserve **only `low64` (`d8..d15`)**. -/
def aapcs64BaseContract : RegSaveContract where
  gprSaved     := fun r => Nat.ble 19 r && Nat.ble r 29
  vecMask      := fun v => match Nat.ble 8 v && Nat.ble v 15 with | true => .low64 | false => .volatile
  predSaved    := fun _ => false
  preserveNzcv := false
  preserveFpsr := false
  preserveFpcr := true

/-- AAPCS64 SVE Procedure Call Standard: `z8..z23` preserve **full `[VL-1:0]`** (`.fullVec`). -/
def aapcs64SveContract : RegSaveContract where
  gprSaved     := fun r => Nat.ble 19 r && Nat.ble r 29
  vecMask      := fun v => match Nat.ble 8 v && Nat.ble v 23 with | true => .fullVec | false => .volatile
  predSaved    := fun p => Nat.ble 4 p && Nat.ble p 15
  preserveNzcv := false
  preserveFpsr := false
  preserveFpcr := true

/-- Normative Rust Reference contract for `asm!(..., options(preserves_flags))` on AArch64:
    requires preserving `NZCV`, `FPSR`, AND `FPCR`. -/
def aarch64RustNormativePreservesFlags : RegSaveContract where
  gprSaved     := fun _ => false
  vecMask      := fun _ => .volatile
  predSaved    := fun _ => false
  preserveNzcv := true
  preserveFpsr := true
  preserveFpcr := true

/-- What `rustc_codegen_llvm/src/asm.rs:260-262` actually tracks in LLVM IR on AArch64
    when `options(preserves_flags)` is set: `NZCV` (`~{cc}` omitted), with NO `~{fpsr}`! -/
def aarch64LlvmLoweredPreservesFlags : RegSaveContract where
  gprSaved     := fun _ => false
  vecMask      := fun _ => .volatile
  predSaved    := fun _ => false
  preserveNzcv := true
  preserveFpsr := false
  preserveFpcr := false

/-- **Theorem 6 (`reg_contract_transitive`):**
    `SatisfiesRegContract c` composes transitively across sequential calls / blocks. -/
theorem reg_contract_transitive
    (c : RegSaveContract) (s0 s1 s2 : MachineRegState)
    (h01 : SatisfiesRegContract c s0 s1)
    (h12 : SatisfiesRegContract c s1 s2) :
    SatisfiesRegContract c s0 s2 :=
  And.intro
    (fun r hr => Eq.trans (h12.1 r hr) (h01.1 r hr))
    (And.intro
      (fun v => slicePreserved_trans (c.vecMask v) (s0.vecReg v) (s1.vecReg v) (s2.vecReg v)
        (h01.2.1 v) (h12.2.1 v))
      (And.intro
        (fun p hp => Eq.trans (h12.2.2.1 p hp) (h01.2.2.1 p hp))
        (And.intro
          (fun h => Eq.trans (h12.2.2.2.1 h) (h01.2.2.2.1 h))
          (And.intro
            (fun h => Eq.trans (h12.2.2.2.2.1 h) (h01.2.2.2.2.1 h))
            (fun h => Eq.trans (h12.2.2.2.2.2 h) (h01.2.2.2.2.2 h))))))

def sveWitnessV8Init : VecRegVal :=
  { lo64 := 0x1110, hi64_128 := 0x2221, sveUpper := [0x3332, 0x4443] }

def sveWitnessZeroVec : VecRegVal :=
  { lo64 := 0, hi64_128 := 0, sveUpper := [0, 0] }

def sveWitnessPre : MachineRegState where
  gprCalleeSaved := fun _ => 0
  vecReg         := fun v => match natEq v 8 with | true => sveWitnessV8Init | false => sveWitnessZeroVec
  svePredReg     := fun _ => 0
  nzcv           := 0
  fpsrSticky     := 0
  fpcrControl    := 0

def sveWitnessPost : MachineRegState :=
  { sveWitnessPre with
    vecReg := fun v =>
      match natEq v 8 with
      | true  => writeNeonDReg sveWitnessV8Init sveWitnessV8Init.lo64
      | false => sveWitnessZeroVec }

/-- **Theorem 7 (`base_pcs_d8_save_restore_corrupts_sve_pcs_upper_lanes`):**
    A callee that saves `d8 = v8.lo64`, clobbers `z8`, and restores `d8` via `ldr d8`
    (`writeNeonDReg`) **satisfies `aapcs64BaseContract`** yet **violates
    `aapcs64SveContract`** whenever `v8`'s `[127:64]` or upper SVE lanes are non-zero! -/
theorem base_pcs_d8_save_restore_corrupts_sve_pcs_upper_lanes :
    sveWitnessPost.vecReg 8 = writeNeonDReg (sveWitnessPre.vecReg 8) (sveWitnessPre.vecReg 8).lo64 ∧
    SatisfiesRegContract aapcs64BaseContract sveWitnessPre sveWitnessPost ∧
    ¬ SatisfiesRegContract aapcs64SveContract sveWitnessPre sveWitnessPost :=
  And.intro rfl
    (And.intro
      (And.intro
        (fun _ _ => rfl)
        (And.intro
          (fun v => by
            unfold aapcs64BaseContract
            dsimp only
            cases Nat.ble 8 v && Nat.ble v 15 with
            | false => trivial
            | true =>
                dsimp only [slicePreserved, sveWitnessPre, sveWitnessPost]
                cases natEq v 8 with
                | true => rfl
                | false => rfl)
          (And.intro
            (fun _ h => Bool.noConfusion h)
            (And.intro
              (fun h => Bool.noConfusion h)
              (And.intro (fun h => Bool.noConfusion h) (fun _ => rfl))))))
      (fun hSve =>
        VecRegVal.noConfusion (hSve.2.1 8) (fun _ hHi _ => Nat.noConfusion hHi)))

def fpsrWitnessPre : MachineRegState := sveWitnessPre

def fpsrWitnessPost : MachineRegState :=
  { sveWitnessPre with fpsrSticky := 0x08000000 }

/-- **Theorem 8 (`llvm_cc_only_lowering_misses_fpsr_qc_violation`):**
    Executing saturating NEON `uqadd` (`fpsrSticky := 0x0800_0000`) inside
    `options(preserves_flags)` satisfies LLVM's lowered `~{cc}` check
    (`aarch64LlvmLoweredPreservesFlags`) while violating the normative Rust
    `aarch64RustNormativePreservesFlags` contract! -/
theorem llvm_cc_only_lowering_misses_fpsr_qc_violation :
    SatisfiesRegContract aarch64LlvmLoweredPreservesFlags fpsrWitnessPre fpsrWitnessPost ∧
    ¬ SatisfiesRegContract aarch64RustNormativePreservesFlags fpsrWitnessPre fpsrWitnessPost :=
  And.intro
    (And.intro
      (fun _ h => Bool.noConfusion h)
      (And.intro
        (fun _ => trivial)
        (And.intro
          (fun _ h => Bool.noConfusion h)
          (And.intro
            (fun _ => rfl)
            (And.intro (fun h => Bool.noConfusion h) (fun h => Bool.noConfusion h))))))
    (fun hNorm => Nat.noConfusion (hNorm.2.2.2.2.1 rfl))

/-! ## Section 3: Nondeterministic `ExclusiveMonitor` (`LDXR`/`STXR`) & Outlined Atomics -/

/-- Hardware per-PE local exclusive monitor + flat atomic word memory. -/
structure ExclusiveState where
  mem         : Nat → Nat
  reservation : Option Nat

def writeWord (m : Nat → Nat) (addr val : Nat) : Nat → Nat :=
  fun a => match natEq a addr with | true => val | false => m a

/-- `LDXR` / `LDAXR` at `addr`: reads `mem addr` and arms `reservation := some addr`. -/
def stepLdxr (s : ExclusiveState) (addr : Nat) : Nat × ExclusiveState :=
  (s.mem addr, { s with reservation := some addr })

/-- `CLREX` (or asynchronous interrupt / cache-line eviction): clears reservation. -/
def stepClrex (s : ExclusiveState) : ExclusiveState :=
  { s with reservation := none }

/-- `STXR` / `STLXR` at `addr` with `envSpuriousClear : Bool`:
    Succeeds (`status = 0`, writes `val`) iff `reservation = some rAddr`,
    `natEq rAddr addr = true`, and `envSpuriousClear = false`; otherwise fails
    (`status = 1`) with **memory unchanged**. Always clears `reservation := none`. -/
def stepStxr (s : ExclusiveState) (addr val : Nat) (envSpuriousClear : Bool)
    : Nat × ExclusiveState :=
  match s.reservation with
  | some rAddr =>
      match natEq rAddr addr && (!envSpuriousClear) with
      | true  => (0, { mem := writeWord s.mem addr val, reservation := none })
      | false => (1, { s with reservation := none })
  | none =>
      (1, { s with reservation := none })

inductive RmwLoopOut where
  | committed (oldVal : Nat) (post : ExclusiveState)
  | retryExhausted (post : ExclusiveState)

/-- Fuel-indexed `LDXR`/`STXR` RMW retry loop (`__aarch64_ldadd*` / `swp*` / `ldset*`
    fallback path) under an arbitrary environment spurious-clear schedule
    `clearSched : Nat → Bool`. -/
def runLlscRmw
    (op : Nat → Nat) (addr : Nat) (fuel : Nat) (clearSched : Nat → Bool) (s : ExclusiveState)
    : RmwLoopOut :=
  match fuel with
  | 0 => .retryExhausted s
  | k + 1 =>
      let (oldVal, s1) := stepLdxr s addr
      let newVal := op oldVal
      let (status, s2) := stepStxr s1 addr newVal (clearSched k)
      match natEq status 0 with
      | true  => .committed oldVal s2
      | false => runLlscRmw op addr k clearSched s2

/-- Abstract single-step MIR `AtomicRmw` specification. -/
def AbstractRmwSpec (op : Nat → Nat) (addr : Nat) (pre : ExclusiveState)
    (oldVal : Nat) (post : ExclusiveState) : Prop :=
  oldVal = pre.mem addr ∧
  post.mem = writeWord pre.mem addr (op oldVal) ∧
  post.reservation = none

/-- **Theorem 9 (`fixed_step_rmw_bound_refuted_by_spurious_clear`):**
    No fixed step bound `K` can guarantee completion of an AArch64 `LDXR`/`STXR`
    loop: under the legal hardware spurious-clear schedule `fun _ => true`,
    `runLlscRmw` at fuel `K` returns `.retryExhausted` with memory unmutated. -/
theorem fixed_step_rmw_bound_refuted_by_spurious_clear
    (op : Nat → Nat) (addr : Nat) (K : Nat) (s : ExclusiveState) :
    Exists fun post =>
      runLlscRmw op addr K (fun _ => true) s = .retryExhausted post ∧
      post.mem = s.mem := by
  induction K generalizing s with
  | zero =>
      exact Exists.intro s (And.intro rfl rfl)
  | succ k ih =>
      unfold runLlscRmw stepLdxr stepStxr
      dsimp only
      rw [natEq_refl addr]
      exact ih { mem := s.mem, reservation := none }

/-- **Theorem 10 (`llsc_rmw_partial_safety_any_schedule`):**
    Under **every** fuel bound `fuel` and **every** adversarial spurious-clear
    schedule `clearSched`, `runLlscRmw` is unconditionally safe:
    - If `.committed oldVal post`, then `AbstractRmwSpec op addr s oldVal post` holds;
    - If `.retryExhausted post`, then `post.mem = s.mem` (zero partial or torn writes!). -/
theorem llsc_rmw_partial_safety_any_schedule
    (op : Nat → Nat) (addr : Nat) (fuel : Nat) (clearSched : Nat → Bool) (s : ExclusiveState) :
    match runLlscRmw op addr fuel clearSched s with
    | .committed oldVal post => AbstractRmwSpec op addr s oldVal post
    | .retryExhausted post   => post.mem = s.mem := by
  induction fuel generalizing s with
  | zero =>
      rfl
  | succ k ih =>
      unfold runLlscRmw stepLdxr stepStxr
      dsimp only
      rw [natEq_refl addr]
      cases hClr : clearSched k with
      | false =>
          exact And.intro rfl (And.intro rfl rfl)
      | true =>
          exact ih { mem := s.mem, reservation := none }

/-- **Theorem 11 (`llsc_rmw_total_liveness_under_fair_window`):**
    Whenever the environment grants at least one uninterrupted reservation window
    (`Exists fun j => j < fuel ∧ clearSched j = false`), `runLlscRmw` deterministically
    terminates in `.committed` satisfying `AbstractRmwSpec`! -/
theorem llsc_rmw_total_liveness_under_fair_window
    (op : Nat → Nat) (addr : Nat) (fuel : Nat) (clearSched : Nat → Bool) (s : ExclusiveState)
    (hFair : Exists fun j => j < fuel ∧ clearSched j = false) :
    Exists fun (res : Nat × ExclusiveState) =>
      runLlscRmw op addr fuel clearSched s = .committed res.1 res.2 ∧
      AbstractRmwSpec op addr s res.1 res.2 := by
  induction fuel generalizing s with
  | zero =>
      cases hFair with
      | intro j hj => exact False.elim (Nat.not_lt_zero j hj.1)
  | succ k ih =>
      unfold runLlscRmw stepLdxr stepStxr
      dsimp only
      rw [natEq_refl addr]
      cases hClr : clearSched k with
      | false =>
          exact Exists.intro
            (s.mem addr, { mem := writeWord s.mem addr (op (s.mem addr)), reservation := none })
            (And.intro rfl (And.intro rfl (And.intro rfl rfl)))
      | true =>
          cases hFair with
          | intro j hj =>
            cases natLt_succ_or_eq hj.1 with
            | inl hjSub =>
                exact ih { mem := s.mem, reservation := none } (Exists.intro j (And.intro hjSub hj.2))
            | inr hjEq =>
                subst hjEq
                rw [hClr] at hj
                exact Bool.noConfusion hj.2

/-- Outlined atomic RMW helper (`__aarch64_ldadd*`, `__aarch64_swp*`, etc.)
    branching dynamically on `haveLse` (`__aarch64_have_lse_atomics != 0`). -/
def runOutlinedRmw
    (haveLse : Bool) (op : Nat → Nat) (addr : Nat)
    (fuel : Nat) (clearSched : Nat → Bool) (s : ExclusiveState) : RmwLoopOut :=
  match haveLse with
  | true =>
      let oldVal := s.mem addr
      .committed oldVal { mem := writeWord s.mem addr (op oldVal), reservation := none }
  | false =>
      runLlscRmw op addr fuel clearSched s

/-- **Theorem 12 (`outlined_rmw_lse_and_llsc_both_refine_abstract_spec`):**
    Both runtime arms of `+outline-atomics` (`haveLse = true` LSE fast path and
    `haveLse = false` LL/SC fallback path under any fair schedule) satisfy the
    exact same `AbstractRmwSpec`! -/
theorem outlined_rmw_lse_and_llsc_both_refine_abstract_spec
    (haveLse : Bool) (op : Nat → Nat) (addr : Nat)
    (fuel : Nat) (clearSched : Nat → Bool) (s : ExclusiveState)
    (hFair : haveLse = false → Exists fun j => j < fuel ∧ clearSched j = false) :
    Exists fun (res : Nat × ExclusiveState) =>
      runOutlinedRmw haveLse op addr fuel clearSched s = .committed res.1 res.2 ∧
      AbstractRmwSpec op addr s res.1 res.2 := by
  cases haveLse with
  | true =>
      exact Exists.intro
        (s.mem addr, { mem := writeWord s.mem addr (op (s.mem addr)), reservation := none })
        (And.intro rfl (And.intro rfl (And.intro rfl rfl)))
  | false =>
      exact llsc_rmw_total_liveness_under_fair_window op addr fuel clearSched s (hFair rfl)

/-- Outlined `__aarch64_cas8_acq_rel` LL/SC fallback (`lse.S` / `compiler_builtins`):
    On mismatch (`oldVal != expected`), `b.ne` exits directly via `ret` *without*
    executing `clrex`, leaving `reservation := some casAddr`. -/
def runOutlinedCasFallback
    (expected desired casAddr : Nat) (s : ExclusiveState) : Nat × ExclusiveState :=
  let (oldVal, s1) := stepLdxr s casAddr
  match natEq oldVal expected with
  | true =>
      let (_, s2) := stepStxr s1 casAddr desired false
      (oldVal, s2)
  | false =>
      (oldVal, s1)

/-- **Theorem 13 (`nested_failing_outlined_cas_breaks_outer_ldxr_reservation`):**
    Even when an inner `__aarch64_cas8_acq_rel` on `addrY` (`natEq addrY addrX = false`)
    *fails* comparison without writing memory, its `LDXR` overwrites the single per-PE
    `ExclusiveMonitor` reservation (`some addrX -> some addrY`), causing the caller's
    subsequent `STXR` on `addrX` to fail (`status = 1`)! -/
theorem nested_failing_outlined_cas_breaks_outer_ldxr_reservation
    (s : ExclusiveState) (addrX addrY : Nat) (hNe : natEq addrY addrX = false)
    (hMismatch : natEq (s.mem addrY) 0xDEAD = false) :
    let (_, sAfterOuterLdxr) := stepLdxr s addrX
    let (_, sAfterInnerCas)  := runOutlinedCasFallback 0xDEAD 0xBEEF addrY sAfterOuterLdxr
    let (outerStatus, sFinal) := stepStxr sAfterInnerCas addrX 0x777 false
    outerStatus = 1 ∧ sFinal.mem = s.mem := by
  dsimp only [stepLdxr, runOutlinedCasFallback]
  rw [hMismatch]
  dsimp only [stepStxr]
  rw [hNe]
  exact And.intro rfl rfl

end IsaParametricSeam
