-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.NotationExtra
import Init.Data.BitVec.BasicAux
import Init.Data.Nat.Div.Basic
import Init.Control.Except

namespace VrustcFormal.F1_3

/-!
# `F1-3`: Release-Fingerprinted Multi-Target Rust `FnAbi` Bit-Exact Lowering,
Linker-Symbol Compatibility, and Physical-Frame Adapter-Shim Refinement

## Relation to General Foundations (`leanlib`) and Empirical Ground Truth (`E2-6`)

General layout algebra (`repr-c-layout-algebra-dst-tails-and-enum-tags`), enum
niche validity (`enum-niche-layout-guarantees-and-validity-invariants`), codec
round-trip laws (`codec-round-trip-laws-and-partial-isomorphisms`), parallel-move
sequentialization (`parallel-move-sequentialization-and-sub-register-lane-framing`,
`google/zerocopy@a02bab389d`), and modular contextual refinement
(`modular-verification-contextual-refinement-and-separate-compilation`) belong
to the general Lean Results Library (`leanlib`).

This module formalizes the strictly **Rust-compiler-specific** multi-target,
multi-release `FnAbi` classification, bit-exact physical call-boundary
marshaling (with byte/word-serialized indirect memory and caller-allocated
disjoint `sret` buffers), `.o` linker-symbol decoration fingerprinting, and
static `AbiVal`-free physical-frame adapter-shim refinement grounded in the
empirical 9-target x 3-release (`rustc 1.99.1`, `1.100.0`, `1.102.0-nightly`)
ABI drift matrix (`E2-6`, `google/zerocopy@120889696d`):

- **Drift Class `D1` (`rust-lang/rust@429c1c18ca61`):** `x86_64` AND `i686`
  `extern "Rust"` `#[repr(simd)]` (`F32x4`) shifted from `Indirect + sret`
  (`1.99.1`) to `Direct(Vector)` (`1.100.0` / `1.102.0`); `extern "C"` SIMD
  remains `Direct(Vector)` across all three releases on all targets.
- **Drift Class `D2` (`rust-lang/rust@a654a2404565`):** `aarch64` `extern "Rust"`
  `#[repr(simd)]` NEON (`F32x4`) stayed `Indirect + sret` (with AAPCS64 `sret`
  in dedicated register `x8`, leaving `x0..x7` intact!) through `1.99.1` and
  `1.100.0`, then shifted to `Direct(Vector)` in `1.102.0-nightly`.
- **Drift Class `D3` (`rust-lang/rust@916dda0c26e7`):** On `win64Msvc`
  `extern "C"`, BOTH `reprC = false` (`()`, `ZstStruct`) and `reprC = true`
  (`#[repr(C)]` ZST) were passed `Indirect` (`ptr align 1`, consuming a
  positional register slot!) in `1.99.1` and `1.100.0`; `1.102.0-nightly`
  restricted indirect ZST passing to `reprC = true`, flipping `reprC = false`
  to `Ignore` (`void`) while leaving `reprC = true` stable (`Indirect`).
- **Drift Class `D4` (`rust-lang/rust@d11b3f4d61c5`):** On `x86_64`
  `extern "vectorcall"`, `abi_vec_hfa4(HfaF32x4, f32) -> HfaF32x4` lowers to
  `void (ptr sret, ptr, float)` identically in IR across all 3 releases, yet
  its `.o` linker symbol shifted from `@@16` (`1.99.1`/`1.100.0`, post-lowering
  LLVM MC sum `sizeof(ptr)=8 + next_multiple_of(4,8)=8`) to `@@24`
  (`1.102.0-nightly`, pre-lowering `rustc` `FnAbi` layout sum
  `next_multiple_of(16,8)=16 + next_multiple_of(4,8)=8`), proving IR-only ABI
  fingerprints miss genuine `.o` linker breaks.
- **IEEE-754 x87 NaN Quietening Hazard (`i686SysV`):** On `i686`, `extern "C"`
  returns `f32`/`f64` through x87 `st(0)` (`fld`/`fstp`), which hardware-quietens
  every signaling NaN (setting bit 22 on `f32` / bit 51 on `f64`), whereas
  `extern "Rust"` returns `<4/8 x i8>` via GPRs and preserves ALL IEEE-754 bits.

## Honest Scope & Explicit Non-Claims

1. **Abstract `FnAbi` / `PhysFrame` Model — Not End-to-End Machine Code:**
   Models an abstract register/stack/word-memory machine corresponding to
   `rustc_target::callconv::FnAbi` and `declare_rust_fn` symbol decoration; does
   NOT verify LLVM `SelectionDAG`/`GlobalISel` lowering, ELF/PE/Mach-O encoding,
   or linker execution.
2. **Pinned 3-Release Epoch Table Only:** Models `{1.99.1, 1.100.0, 1.102.0}`
   as recorded in `E2-6`; makes zero claims about unprobed `rustc` commits.
3. **Explicitly Unmodeled ABI Dimensions:** Callee-saved register preservation,
   16-byte stack alignment, Win64 32-byte shadow space, SysV64 128-byte red
   zone, `i686` 32-bit GPR / 4-byte stack-slot granularity (e.g. `eax:edx`
   64-bit returns abstracted as single 64-bit `gpr0`), `i686-pc-windows-msvc`
   8-byte `eax:edx` struct returns, per-convention GPR caps (`sysv64`
   `vectorcall` 4-GPR cap and `i686` `vectorcall` `ecx`/`edx` 2-GPR fast-pass,
   which do not alter `@@N` decoration), `u128`/`i128` and AAPCS64 odd-register
   `u128` alignment, `stdcall`/`fastcall` callee stack cleanup,
   `#[target_feature]` wide AVX/AVX-512 vectors, struct padding bytes
   (`undef`/`poison`), invalid niche discriminants, `#[repr(C, packed)]`,
   C-variadics (`...`), `#[track_caller]`, `extern "efiapi"`, `f16`/`f128`, and
   `riscv64` `signext`/softfloat (both `f16`/`f128` and `riscv64` are explicitly
   `not examined` in `E2-6`; Win64 `#[repr(C)]` ZST retention in `1.102.0` is
   `source`-verified in `E2-6` Boundary #2 and live-confirmed via `rustc +nightly`).
4. **Anneal `TrustedBoundary.lean` Discipline:** Closed locked `Init.*` imports
   only, prefix `Nat.pow`/`Nat.div`/`Nat.mod` (zero banned `^`/`/`/`%` syntax),
   `noncomputable` on recursive/dependent value defs (zero `._unsafe_rec`),
   zero redundant `noncomputable` on `: Prop`, constructive axioms only
   (`0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`).
-/

/-! ## Part I: Targets, Releases, Calling Conventions, Types, and Values -/

/-- Supported ABI target profiles covering the empirical drift matrix. -/
inductive AbiTarget where
  | sysv64
  | win64Msvc
  | aapcs64
  | i686SysV

/-- Exact `rustc` release points pinned in the 9-target x 3-release matrix. -/
inductive RustcRelease where
  | r1_99_1
  | r1_100_0
  | r1_102_0

/-- Calling conventions exercised across Rust/C/vectorcall ABI boundaries. -/
inductive CallConv where
  | rust
  | c
  | vectorcall

/-- Rust ABI-relevant value types modeled at the call boundary. -/
inductive AbiTy where
  /-- Zero-sized type, parameterized by `LayoutData.repr_c` (Win64 `D3` split). -/
  | zst (reprC : Bool)
  /-- Fixed scalar integer of `bytes` in `{1, 2, 4, 8}`. -/
  | intScalar (bytes : Nat)
  /-- 32-bit IEEE-754 float (exact 32-bit payload). -/
  | float32
  /-- 64-bit IEEE-754 float (exact 64-bit payload). -/
  | float64
  /-- `Option<NonNull<u8>>`: 8-byte scalar with niche `0 = None`. -/
  | nicheNonNull
  /-- `#[repr(C)] struct { a: f64, b: f64 }` (16-byte 2-SSE HFA). -/
  | hfa2F64
  /-- `#[repr(C)] struct { a..d: f32 }` (16-byte 4-float HFA; `D4` vectorcall). -/
  | hfa4F32
  /-- `#[repr(simd)] struct F32x4([f32; 4])` (128-bit SIMD vector; `D1`/`D2`). -/
  | simd4F32
  /-- Large `#[repr(C)]` aggregate (`wordCount > 2`, i.e. `>= 24` bytes, indirect). -/
  | bigStruct (wordCount : Nat)

/-- Function signature at the MIR-to-machine call boundary. -/
structure FnSig where
  conv : CallConv
  args : List AbiTy
  ret : AbiTy

/-- Runtime bit-exact Rust values corresponding to `AbiTy`. -/
inductive AbiVal where
  | zst
  | intScalar (bytes : Nat) (bits : BitVec 64)
  | float32 (bits : BitVec 32)
  | float64 (bits : BitVec 64)
  | nicheNonNull (ptrBits : BitVec 64)
  | hfa2F64 (a b : BitVec 64)
  | hfa4F32 (a b c d : BitVec 32)
  | simd4F32 (bits : BitVec 128)
  | bigStruct (words : List (BitVec 64))

/-- Well-typedness predicate matching `AbiVal` to `AbiTy` (including exact
low-bit bounds for sub-64-bit integers and `wordCount > 2` for `bigStruct`). -/
def valHasTy : AbiVal → AbiTy → Prop
  | .zst, .zst _ => True
  | .intScalar b bits, .intScalar b' =>
      b = b' ∧ (b = 1 ∨ b = 2 ∨ b = 4 ∨ b = 8) ∧
      (b < 8 → bits.toNat < Nat.pow 2 (b * 8))
  | .float32 _, .float32 => True
  | .float64 _, .float64 => True
  | .nicheNonNull _, .nicheNonNull => True
  | .hfa2F64 _ _, .hfa2F64 => True
  | .hfa4F32 _ _ _ _, .hfa4F32 => True
  | .simd4F32 _, .simd4F32 => True
  | .bigStruct ws, .bigStruct n => ws.length = n ∧ 2 < n
  | _, _ => False

/-- List-level well-typedness of argument lists against parameter types.
Defined inductively so Lean `v4.34.1` emits zero `isPartial` `._unsafe_rec`
auxiliaries (required by Anneal `TrustedBoundary.lean` `"audit"`). -/
inductive valsHaveTys : List AbiVal → List AbiTy → Prop where
  | nil : valsHaveTys [] []
  | cons {v t vs ts} : valHasTy v t → valsHaveTys vs ts → valsHaveTys (v :: vs) (t :: ts)

/-- Decidable runtime well-typedness check enforcing `expectedTy` on both
marshaling and indirect word decoding. -/
noncomputable def checkValHasTy : AbiVal → AbiTy → Bool
  | .zst, .zst _ => true
  | .intScalar b bits, .intScalar b' =>
      Nat.beq b b' &&
      (Nat.beq b 1 || Nat.beq b 2 || Nat.beq b 4 || Nat.beq b 8) &&
      (if Nat.blt b 8 then Nat.blt bits.toNat (Nat.pow 2 (b * 8)) else true)
  | .float32 _, .float32 => true
  | .float64 _, .float64 => true
  | .nicheNonNull _, .nicheNonNull => true
  | .hfa2F64 _ _, .hfa2F64 => true
  | .hfa4F32 _ _ _ _, .hfa4F32 => true
  | .simd4F32 _, .simd4F32 => true
  | .bigStruct ws, .bigStruct n => Nat.beq ws.length n && Nat.blt 2 n
  | _, _ => false

/-! ## Part II: IEEE-754 x87 Signaling-NaN Hardware Quietening Model -/

/-- True iff `bits : BitVec 32` is an IEEE-754 binary32 signaling NaN:
exponent bits `[30:23]` are all 1 (`0xFF`), quiet bit `22` is `0`, and mantissa
bits `[21:0]` are nonzero. Uses prefix `Nat.div`/`Nat.mod` per `TrustedBoundary`. -/
noncomputable def isF32SignalingNaN (bits : BitVec 32) : Bool :=
  let exp := Nat.mod (Nat.div bits.toNat 8388608) 256
  let quietBit := Nat.mod (Nat.div bits.toNat 4194304) 2
  let payload := Nat.mod bits.toNat 4194304
  Nat.beq exp 255 && Nat.beq quietBit 0 && !Nat.beq payload 0

/-- True iff `bits : BitVec 64` is an IEEE-754 binary64 signaling NaN:
exponent bits `[62:52]` are all 1 (`0x7FF`), quiet bit `51` is `0`, and mantissa
bits `[50:0]` are nonzero. -/
noncomputable def isF64SignalingNaN (bits : BitVec 64) : Bool :=
  let exp := Nat.mod (Nat.div bits.toNat 4503599627370496) 2048
  let quietBit := Nat.mod (Nat.div bits.toNat 2251799813685248) 2
  let payload := Nat.mod bits.toNat 2251799813685248
  Nat.beq exp 2047 && Nat.beq quietBit 0 && !Nat.beq payload 0

/-- Hardware x87 `fld`+`fstp` transfer on `f32`: quietens signaling NaNs by
setting bit 22 (`+ 0x00400000 = 4194304`); preserves all other bit patterns. -/
noncomputable def x87TransferF32 (bits : BitVec 32) : BitVec 32 :=
  if isF32SignalingNaN bits then
    BitVec.ofNat 32 (bits.toNat + 4194304)
  else
    bits

/-- Hardware x87 `fld`+`fstp` transfer on `f64`: quietens signaling NaNs by
setting bit 51 (`+ 0x0008000000000000 = 2251799813685248`). -/
noncomputable def x87TransferF64 (bits : BitVec 64) : BitVec 64 :=
  if isF64SignalingNaN bits then
    BitVec.ofNat 64 (bits.toNat + 2251799813685248)
  else
    bits

/-- Predicate stating a return value is unaffected by x87 sNaN quietening. -/
def isNonSignalingRet : AbiVal → Prop
  | .float32 b => isF32SignalingNaN b = false
  | .float64 b => isF64SignalingNaN b = false
  | _ => True

/-! ## Part III: Concrete `FnAbi` Classification & Linker-Symbol Fingerprinting -/

/-- Physical passing mode for one argument in `FnAbi`. -/
inductive ArgPassMode where
  | ignore
  | directGpr (regIdx : Nat) (bytes : Nat)
  | directF32 (regIdx : Nat)
  | directF64 (regIdx : Nat)
  | directPairF64 (r0 : Nat)
  | directQuadF32 (r0 : Nat)
  | directVec128 (regIdx : Nat)
  | indirectGpr (regIdx : Nat) (expectedTy : AbiTy)
  | indirectStack (slotIdx : Nat) (byval : Bool) (expectedTy : AbiTy)
  | directStack (slotIdx : Nat) (expectedTy : AbiTy)

/-- Dedicated location where the caller passes the hidden `sret` buffer pointer
(distinguishing SysV64/Win64 `gpr0` (`rdi`/`rcx`), AAPCS64 dedicated `gpr8`
(`x8`), and i686 SysV `stack0`). -/
inductive SretLoc where
  | none
  | gpr0
  | gpr8
  | stack0

/-- Physical return passing mode in `FnAbi`. -/
inductive RetPassMode where
  | ignore
  | directGpr0 (bytes : Nat)
  | directXmm0F32
  | directXmm0F64
  | directX87F32
  | directX87F64
  | directPairXmm01F64
  | directQuadXmm03F32
  | directXmm0Vec128
  | indirectSret (loc : SretLoc) (expectedTy : AbiTy)

/-- Explicit `.o` linker-symbol decoration rule, preventing sentinel collisions
between undecorated `extern "C"` symbols (`foo`) and zero-byte `vectorcall`
symbols (`foo@@0`). -/
inductive LinkerSymbolRule where
  | undecorated
  | vectorcallAtAt (bytes : Nat)

/-- Computed ABI lowering plan for one function signature. -/
structure ComputedFnAbi where
  target : AbiTarget
  conv : CallConv
  argModes : List ArgPassMode
  retMode : RetPassMode
  sretLoc : SretLoc
  symbolRule : LinkerSymbolRule

/-- True iff `retMode` transfers a floating-point value through x87 `st(0)`. -/
noncomputable def isX87RetMode : RetPassMode → Bool
  | .directX87F32 => true
  | .directX87F64 => true
  | _ => false

/-- Equality helpers (`noncomputable` to avoid `._unsafe_rec`). -/
noncomputable def targetEq : AbiTarget → AbiTarget → Bool
  | .sysv64, .sysv64 => true
  | .win64Msvc, .win64Msvc => true
  | .aapcs64, .aapcs64 => true
  | .i686SysV, .i686SysV => true
  | _, _ => false

noncomputable def convEq : CallConv → CallConv → Bool
  | .rust, .rust => true
  | .c, .c => true
  | .vectorcall, .vectorcall => true
  | _, _ => false

noncomputable def boolEq : Bool → Bool → Bool
  | true, true => true
  | false, false => true
  | _, _ => false

noncomputable def abiTyEq : AbiTy → AbiTy → Bool
  | .zst a, .zst b => boolEq a b
  | .intScalar a, .intScalar b => Nat.beq a b
  | .float32, .float32 => true
  | .float64, .float64 => true
  | .nicheNonNull, .nicheNonNull => true
  | .hfa2F64, .hfa2F64 => true
  | .hfa4F32, .hfa4F32 => true
  | .simd4F32, .simd4F32 => true
  | .bigStruct a, .bigStruct b => Nat.beq a b
  | _, _ => false

noncomputable def sretLocEq : SretLoc → SretLoc → Bool
  | .none, .none => true
  | .gpr0, .gpr0 => true
  | .gpr8, .gpr8 => true
  | .stack0, .stack0 => true
  | _, _ => false

noncomputable def argModeEq : ArgPassMode → ArgPassMode → Bool
  | .ignore, .ignore => true
  | .directGpr r1 b1, .directGpr r2 b2 => Nat.beq r1 r2 && Nat.beq b1 b2
  | .directF32 r1, .directF32 r2 => Nat.beq r1 r2
  | .directF64 r1, .directF64 r2 => Nat.beq r1 r2
  | .directPairF64 r1, .directPairF64 r2 => Nat.beq r1 r2
  | .directQuadF32 r1, .directQuadF32 r2 => Nat.beq r1 r2
  | .directVec128 r1, .directVec128 r2 => Nat.beq r1 r2
  | .indirectGpr r1 t1, .indirectGpr r2 t2 => Nat.beq r1 r2 && abiTyEq t1 t2
  | .indirectStack s1 bv1 t1, .indirectStack s2 bv2 t2 =>
      Nat.beq s1 s2 && boolEq bv1 bv2 && abiTyEq t1 t2
  | .directStack s1 t1, .directStack s2 t2 => Nat.beq s1 s2 && abiTyEq t1 t2
  | _, _ => false

noncomputable def retModeEq : RetPassMode → RetPassMode → Bool
  | .ignore, .ignore => true
  | .directGpr0 b1, .directGpr0 b2 => Nat.beq b1 b2
  | .directXmm0F32, .directXmm0F32 => true
  | .directXmm0F64, .directXmm0F64 => true
  | .directX87F32, .directX87F32 => true
  | .directX87F64, .directX87F64 => true
  | .directPairXmm01F64, .directPairXmm01F64 => true
  | .directQuadXmm03F32, .directQuadXmm03F32 => true
  | .directXmm0Vec128, .directXmm0Vec128 => true
  | .indirectSret l1 t1, .indirectSret l2 t2 => sretLocEq l1 l2 && abiTyEq t1 t2
  | _, _ => false

noncomputable def argModeListEq : List ArgPassMode → List ArgPassMode → Bool
  | [], [] => true
  | a :: as, b :: bs => argModeEq a b && argModeListEq as bs
  | _, _ => false

noncomputable def symbolRuleEq : LinkerSymbolRule → LinkerSymbolRule → Bool
  | .undecorated, .undecorated => true
  | .vectorcallAtAt a, .vectorcallAtAt b => Nat.beq a b
  | _, _ => false

/-- Maximum integer, scalar-float XMM, and SIMD-vector XMM argument register
counts by `(target, conv)`. On `i686SysV`, scalar floats pass on the stack
(`maxFloatXmmArgs = 0`), while SSE2 128-bit vectors pass in `xmm0..xmm2`
(`maxVecXmmArgs = 3`). On `x86_64` `vectorcall`, 6 XMM registers (`xmm0..xmm5`)
are available. -/
noncomputable def maxGprArgs : AbiTarget → Nat
  | .sysv64 => 6
  | .win64Msvc => 4
  | .aapcs64 => 8
  | .i686SysV => 0

noncomputable def maxFloatXmmArgs (t : AbiTarget) (cc : CallConv) : Nat :=
  match t, cc with
  | .sysv64, .vectorcall => 6
  | .win64Msvc, .vectorcall => 6
  | .sysv64, _ => 8
  | .win64Msvc, _ => 4
  | .aapcs64, _ => 8
  | .i686SysV, .vectorcall => 6
  | .i686SysV, _ => 0

noncomputable def maxVecXmmArgs (t : AbiTarget) (cc : CallConv) : Nat :=
  match t, cc with
  | .sysv64, .vectorcall => 6
  | .win64Msvc, .vectorcall => 6
  | .sysv64, _ => 8
  | .win64Msvc, _ => 4
  | .aapcs64, _ => 8
  | .i686SysV, .vectorcall => 6
  | .i686SysV, _ => 3

/-- Whether `rustc` passes `#[repr(simd)] F32x4` directly in a vector register
for `(target, release, conv)`, faithfully matching `E2-6` drifts `D1` & `D2`:
- `D1` (`429c1c18ca61`): ALL `x86_64` AND `i686` `extern "Rust"` flip `false`
  (`1.99.1`) -> `true` (`1.100.0` / `1.102.0`).
- `D2` (`a654a2404565`): `aapcs64` `extern "Rust"` flips `false`
  (`1.99.1` / `1.100.0`) -> `true` (`1.102.0`).
- `extern "C"` and `extern "vectorcall"` pass `F32x4` directly on all 4 targets
  across all 3 releases. -/
noncomputable def simdDirectEnabled (t : AbiTarget) (rel : RustcRelease)
    (cc : CallConv) : Bool :=
  match t, cc, rel with
  | .sysv64, .rust, .r1_99_1 => false
  | .sysv64, .rust, _ => true
  | .win64Msvc, .rust, .r1_99_1 => false
  | .win64Msvc, .rust, _ => true
  | .i686SysV, .rust, .r1_99_1 => false
  | .i686SysV, .rust, _ => true
  | .aapcs64, .rust, .r1_99_1 => false
  | .aapcs64, .rust, .r1_100_0 => false
  | .aapcs64, .rust, .r1_102_0 => true
  | _, .c, _ => true
  | _, .vectorcall, _ => true

/-- Whether `win64` (`win64Msvc` `extern "C"` OR `x86_64` `extern "vectorcall"`,
which dispatches through `x86_win64::compute_abi_info`) passes a ZST indirectly
via `ptr align 1`, faithfully matching `E2-6` drift `D3` (`rust-lang/rust@916dda0c26e7`):
- In `1.99.1` and `1.100.0`, ALL `x86_win64` ZSTs (`reprC = false` and
  `reprC = true`) are passed `Indirect`.
- In `1.102.0-nightly`, `reprC = true` remains `Indirect` while `reprC = false`
  (`()`, `ZstStruct`) flips to `Ignore` (`void`). -/
noncomputable def win64ZstIndirect (t : AbiTarget) (rel : RustcRelease)
    (cc : CallConv) (reprC : Bool) : Bool :=
  match t, cc, rel, reprC with
  | .win64Msvc, .c, .r1_99_1, _ => true
  | .win64Msvc, .c, .r1_100_0, _ => true
  | .win64Msvc, .c, .r1_102_0, true => true
  | .win64Msvc, .vectorcall, .r1_99_1, _ => true
  | .win64Msvc, .vectorcall, .r1_100_0, _ => true
  | .win64Msvc, .vectorcall, .r1_102_0, true => true
  | .sysv64, .vectorcall, .r1_99_1, _ => true
  | .sysv64, .vectorcall, .r1_100_0, _ => true
  | .sysv64, .vectorcall, .r1_102_0, true => true
  | _, _, _, _ => false

/-- Whether target uses Win64 synchronized positional register slots
(`rcx/xmm0`, `rdx/xmm1`, `r8/xmm2`, `r9/xmm3`) for non-vectorcall conventions. -/
noncomputable def usesWin64PositionalSlots (t : AbiTarget) (cc : CallConv) : Bool :=
  match t, cc with
  | .win64Msvc, .vectorcall => false
  | .win64Msvc, _ => true
  | _, _ => false

/-- Classify one argument and advance register/stack cursors `(gIdx, xIdx, stkIdx)`. -/
noncomputable def classifyOneArg (t : AbiTarget) (rel : RustcRelease) (cc : CallConv)
    (ty : AbiTy) (gIdx xIdx stkIdx : Nat) : ArgPassMode × Nat × Nat × Nat :=
  let maxG := maxGprArgs t
  let maxFX := maxFloatXmmArgs t cc
  let maxVX := maxVecXmmArgs t cc
  let syncWin := usesWin64PositionalSlots t cc
  match ty with
  | .zst reprC =>
    if win64ZstIndirect t rel cc reprC then
      if Nat.blt gIdx maxG then
        (.indirectGpr gIdx (.zst reprC), gIdx + 1, if syncWin then xIdx + 1 else xIdx, stkIdx)
      else
        (.indirectStack stkIdx false (.zst reprC), gIdx, xIdx, stkIdx + 1)
    else
      (.ignore, gIdx, xIdx, stkIdx)
  | .intScalar bytes =>
    if Nat.blt gIdx maxG then
      (.directGpr gIdx bytes, gIdx + 1, if syncWin then xIdx + 1 else xIdx, stkIdx)
    else
      (.directStack stkIdx (.intScalar bytes), gIdx, xIdx, stkIdx + 1)
  | .nicheNonNull =>
    if Nat.blt gIdx maxG then
      (.directGpr gIdx 8, gIdx + 1, if syncWin then xIdx + 1 else xIdx, stkIdx)
    else
      (.directStack stkIdx .nicheNonNull, gIdx, xIdx, stkIdx + 1)
  | .float32 =>
    if Nat.blt xIdx maxFX then
      (.directF32 xIdx, if syncWin then gIdx + 1 else gIdx, xIdx + 1, stkIdx)
    else
      (.directStack stkIdx .float32, gIdx, xIdx, stkIdx + 1)
  | .float64 =>
    if Nat.blt xIdx maxFX then
      (.directF64 xIdx, if syncWin then gIdx + 1 else gIdx, xIdx + 1, stkIdx)
    else
      (.directStack stkIdx .float64, gIdx, xIdx, stkIdx + 1)
  | .hfa2F64 =>
    match t, cc with
    | .sysv64, .rust | .sysv64, .c | .aapcs64, _ =>
      if Nat.blt (xIdx + 1) maxFX then
        (.directPairF64 xIdx, gIdx, xIdx + 2, stkIdx)
      else
        (.directStack stkIdx .hfa2F64, gIdx, xIdx, stkIdx + 2)
    | .win64Msvc, .rust =>
      -- `E2-6`: Win64 `extern "Rust"` passes 2-f64 struct as ScalarPair(f64, f64)
      if Nat.blt (xIdx + 1) maxFX then
        (.directPairF64 xIdx, if syncWin then gIdx + 2 else gIdx, xIdx + 2, stkIdx)
      else
        (.directStack stkIdx .hfa2F64, gIdx, xIdx, stkIdx + 2)
    | .win64Msvc, _ | .sysv64, .vectorcall =>
      if Nat.blt gIdx maxG then
        (.indirectGpr gIdx .hfa2F64, gIdx + 1, if syncWin then xIdx + 1 else xIdx, stkIdx)
      else
        (.indirectStack stkIdx false .hfa2F64, gIdx, xIdx, stkIdx + 1)
    | .i686SysV, _ =>
      (.directStack stkIdx .hfa2F64, gIdx, xIdx, stkIdx + 2)
  | .hfa4F32 =>
    -- `E2-6` ground truth:
    -- 1. `extern "Rust"` `HfaF32x4` lowers to universal `sret + indirect ptr` on ALL targets.
    -- 2. `extern "vectorcall"` `HfaF32x4` lowers to `sret + indirect ptr` on `x86_64` (`D4`!)
    --    and `byval` on stack on `i686`.
    -- 3. `extern "C"` `HfaF32x4` splits 4 ways: AAPCS64 `[4 x float]`, SysV64 `{double, double}`,
    --    Win64 `indirect ptr`, i686 stack (`byval`).
    match t, cc with
    | .aapcs64, .c =>
      if Nat.blt (xIdx + 3) maxFX then
        (.directQuadF32 xIdx, gIdx, xIdx + 4, stkIdx)
      else
        (.directStack stkIdx .hfa4F32, gIdx, xIdx, stkIdx + 2)
    | .sysv64, .c =>
      if Nat.blt (xIdx + 1) maxFX then
        (.directPairF64 xIdx, gIdx, xIdx + 2, stkIdx)
      else
        (.directStack stkIdx .hfa4F32, gIdx, xIdx, stkIdx + 2)
    | .i686SysV, .c | .i686SysV, .vectorcall =>
      (.directStack stkIdx .hfa4F32, gIdx, xIdx, stkIdx + 2)
    | _, _ =>
      if Nat.blt gIdx maxG then
        (.indirectGpr gIdx .hfa4F32, gIdx + 1, if syncWin then xIdx + 1 else xIdx, stkIdx)
      else
        (.indirectStack stkIdx false .hfa4F32, gIdx, xIdx, stkIdx + 1)
  | .simd4F32 =>
    if simdDirectEnabled t rel cc then
      if Nat.blt xIdx maxVX then
        (.directVec128 xIdx, if syncWin then gIdx + 1 else gIdx, xIdx + 1, stkIdx)
      else
        (.directStack stkIdx .simd4F32, gIdx, xIdx, stkIdx + 2)
    else if Nat.blt gIdx maxG then
      (.indirectGpr gIdx .simd4F32, gIdx + 1, if syncWin then xIdx + 1 else xIdx, stkIdx)
    else
      (.indirectStack stkIdx false .simd4F32, gIdx, xIdx, stkIdx + 1)
  | .bigStruct n =>
    let isByval := match t, cc with
      | .i686SysV, .c | .i686SysV, .vectorcall => true
      | _, _ => false
    if Nat.blt gIdx maxG then
      (.indirectGpr gIdx (.bigStruct n), gIdx + 1, if syncWin then xIdx + 1 else xIdx, stkIdx)
    else
      (.indirectStack stkIdx isByval (.bigStruct n), gIdx, xIdx, stkIdx + 1)

/-- Classify a list of argument types sequentially. -/
noncomputable def classifyArgsLoop (t : AbiTarget) (rel : RustcRelease) (cc : CallConv)
    (gIdx xIdx stkIdx : Nat) : List AbiTy → List ArgPassMode
  | [] => []
  | ty :: rest =>
    let (m, g', x', s') := classifyOneArg t rel cc ty gIdx xIdx stkIdx
    m :: classifyArgsLoop t rel cc g' x' s' rest

/-- Target-specific hidden `sret` pointer register/stack slot (`aapcs64` uses
dedicated `x8`, leaving `x0..x7` untouched; `sysv64`/`win64Msvc` use `gpr0`;
`i686SysV` uses `stack0`). -/
noncomputable def targetSretLoc : AbiTarget → SretLoc
  | .sysv64 => .gpr0
  | .win64Msvc => .gpr0
  | .aapcs64 => .gpr8
  | .i686SysV => .stack0

/-- Classify return type for `(target, release, conv)`. -/
noncomputable def classifyRet (t : AbiTarget) (rel : RustcRelease) (cc : CallConv)
    (ty : AbiTy) : RetPassMode :=
  let sLoc := targetSretLoc t
  match ty with
  | .zst _ => .ignore
  | .intScalar bytes => .directGpr0 bytes
  | .nicheNonNull => .directGpr0 8
  | .float32 =>
    match t, cc with
    | .i686SysV, .c => .directX87F32
    | .i686SysV, .rust => .directGpr0 4
    | _, _ => .directXmm0F32
  | .float64 =>
    match t, cc with
    | .i686SysV, .c => .directX87F64
    | .i686SysV, .rust => .directGpr0 8
    | _, _ => .directXmm0F64
  | .hfa2F64 =>
    match t, cc with
    | .sysv64, .rust | .sysv64, .c | .aapcs64, _ => .directPairXmm01F64
    | .win64Msvc, .rust => .directPairXmm01F64
    | _, _ => .indirectSret sLoc .hfa2F64
  | .hfa4F32 =>
    match t, cc with
    | .aapcs64, .c => .directQuadXmm03F32
    | .sysv64, .c => .directPairXmm01F64
    | _, _ => .indirectSret sLoc .hfa4F32
  | .simd4F32 =>
    if simdDirectEnabled t rel cc then
      .directXmm0Vec128
    else
      .indirectSret sLoc .simd4F32
  | .bigStruct n => .indirectSret sLoc (.bigStruct n)

/-- Pre-lowering Rust ABI layout size in bytes for `AbiTy`. -/
noncomputable def tyByteSize : AbiTy → Nat
  | .zst _ => 0
  | .intScalar b => b
  | .float32 => 4
  | .float64 => 8
  | .nicheNonNull => 8
  | .hfa2F64 => 16
  | .hfa4F32 => 16
  | .simd4F32 => 16
  | .bigStruct n => n * 8

/-- Pointer word width in bytes (`8` on 64-bit targets, `4` on `i686SysV`). -/
noncomputable def targetPtrBytes : AbiTarget → Nat
  | .i686SysV => 4
  | _ => 8

/-- `next_multiple_of n align` using `Nat.div`/`Nat.mod` only (`align > 0`). -/
noncomputable def nextMultipleOf (n align : Nat) : Nat :=
  let rem := Nat.mod n align
  if Nat.beq rem 0 then n else n + (align - rem)

/-- Exact two-mode `E2-6` (`rust-lang/rust@d11b3f4d61c5`) `vectorcall` `@@N`
argument byte contribution for one `(ty, mode)` pair:
- Pre-`1.102.0` (`1.99.1`/`1.100.0`, LLVM MC post-lowering sum): `ignore` = `0`,
  `indirectGpr`/`indirectStack` = `ptrBytes` (`8` on `x86_64`), direct/byval =
  `nextMultipleOf (tyByteSize ty) ptrBytes`.
- `1.102.0-nightly` (`rustc` pre-lowering `FnAbi` layout sum): `ignore` = `0`,
  all other args = `nextMultipleOf (tyByteSize ty) ptrBytes`.
Reproduces `abi_vec_hfa4(HfaF32x4, f32)` `8+8 = 16 -> 16+8 = 24` on `x86_64`,
`16+4 = 20` on `i686` (`byval`), and `bigStruct 3` `8 -> 24` on `x86_64` with
zero hardcoded magic constants! -/
noncomputable def vectorcallArgDecorBytes (ptrBytes : Nat) (rel : RustcRelease)
    (ty : AbiTy) (mode : ArgPassMode) : Nat :=
  match mode with
  | .ignore => 0
  | .indirectStack _ true _ => nextMultipleOf (tyByteSize ty) ptrBytes
  | .indirectGpr _ _ | .indirectStack _ false _ =>
    match rel with
    | .r1_102_0 => nextMultipleOf (tyByteSize ty) ptrBytes
    | _ => ptrBytes
  | _ => nextMultipleOf (tyByteSize ty) ptrBytes

noncomputable def sumVectorcallDecorBytes (ptrBytes : Nat) (rel : RustcRelease) :
    List AbiTy → List ArgPassMode → Nat
  | ty :: ts, m :: ms =>
    vectorcallArgDecorBytes ptrBytes rel ty m + sumVectorcallDecorBytes ptrBytes rel ts ms
  | _, _ => 0

noncomputable def computeSymbolRule (t : AbiTarget) (rel : RustcRelease)
    (cc : CallConv) (tys : List AbiTy) (modes : List ArgPassMode) : LinkerSymbolRule :=
  match t, cc with
  | .sysv64, .vectorcall => .vectorcallAtAt (sumVectorcallDecorBytes (targetPtrBytes t) rel tys modes)
  | .win64Msvc, .vectorcall => .vectorcallAtAt (sumVectorcallDecorBytes (targetPtrBytes t) rel tys modes)
  | .i686SysV, .vectorcall => .vectorcallAtAt (sumVectorcallDecorBytes (targetPtrBytes t) rel tys modes)
  | _, _ => .undecorated

/-- Full release-fingerprinted `FnAbi` classifier. -/
noncomputable def classifyFnAbi (t : AbiTarget) (rel : RustcRelease)
    (sig : FnSig) : ComputedFnAbi :=
  let retM := classifyRet t rel sig.conv sig.ret
  let sLoc := match retM with
    | .indirectSret l _ => l
    | _ => .none
  let initGpr := match sLoc with
    | .gpr0 => 1
    | _ => 0
  let initXmm := match sLoc, usesWin64PositionalSlots t sig.conv with
    | .gpr0, true => 1
    | _, _ => 0
  let initStk := match sLoc with
    | .stack0 => 1
    | _ => 0
  let argMs := classifyArgsLoop t rel sig.conv initGpr initXmm initStk sig.args
  {
    target := t
    conv := sig.conv
    argModes := argMs
    retMode := retM
    sretLoc := sLoc
    symbolRule := computeSymbolRule t rel sig.conv sig.args argMs
  }

/-- **IR-only compatibility predicate** (checks target, pass modes, and `sret`
location, intentionally omitting `.o` `symbolRule` and `conv` decoration —
proven insufficient by Theorem 4 & Witness `D4`). -/
noncomputable def irOnlyCompatible (a b : ComputedFnAbi) : Bool :=
  targetEq a.target b.target &&
    argModeListEq a.argModes b.argModes &&
    retModeEq a.retMode b.retMode &&
    sretLocEq a.sretLoc b.sretLoc

/-- **Full release-fingerprinted ABI compatibility predicate** (checks target,
calling convention, canonical pass modes, `sret` location, AND `.o` linker
`symbolRule`). Note: by structural reflection `fullAbiCompatible a b = true ↔ a = b`
over the modeled 6-tuple; unmodeled ABI attributes are documented in Honest Scope. -/
noncomputable def fullAbiCompatible (a b : ComputedFnAbi) : Bool :=
  irOnlyCompatible a b && convEq a.conv b.conv && symbolRuleEq a.symbolRule b.symbolRule

/-! ## Part IV: Physical Machine State, Word-Serialized Memory & Marshaling -/

/-- Error kinds raised by physical call-boundary marshaling/unmarshaling. -/
inductive AbiError where
  | arityMismatch
  | typeMismatch
  | missingReg
  | missingStackSlot
  | missingIndirectSlot
  | missingSretPtr
  | wordLengthMismatch
  | modeMismatch

/-- Abstract physical machine state at a call or return boundary.
Crucially, `mem` stores raw `List (BitVec 64)` words (NEVER unserialized
`AbiVal` ASTs), and `sretTok` tracks the caller-allocated indirect return
buffer token when `sretLoc ≠ .none`. -/
structure PhysFrame where
  gprs : List (Nat × BitVec 64)
  xmms : List (Nat × BitVec 128)
  stack : List (Nat × BitVec 64)
  mem : List (Nat × List (BitVec 64))
  nextTok : Nat
  x87F32 : Option (BitVec 32)
  x87F64 : Option (BitVec 64)

noncomputable def emptyFrame : PhysFrame :=
  { gprs := [], xmms := [], stack := [], mem := [],
    nextTok := 1, x87F32 := none, x87F64 := none }

noncomputable def assocLookup {α : Type} (k : Nat) : List (Nat × α) → Option α
  | [] => none
  | (k', v) :: rest => if Nat.beq k k' then some v else assocLookup k rest

noncomputable def putGpr (f : PhysFrame) (r : Nat) (v : BitVec 64) : PhysFrame :=
  { f with gprs := (r, v) :: f.gprs }

noncomputable def putXmm (f : PhysFrame) (r : Nat) (v : BitVec 128) : PhysFrame :=
  { f with xmms := (r, v) :: f.xmms }

noncomputable def putStack (f : PhysFrame) (s : Nat) (v : BitVec 64) : PhysFrame :=
  { f with stack := (s, v) :: f.stack }

noncomputable def allocMemWords (f : PhysFrame) (ws : List (BitVec 64)) : Nat × PhysFrame :=
  let tok := f.nextTok
  (tok, { f with
    mem := (tok, ws) :: f.mem
    nextTok := tok + 1 })

noncomputable def writeMemWords (f : PhysFrame) (tok : Nat) (ws : List (BitVec 64)) : PhysFrame :=
  { f with mem := (tok, ws) :: f.mem }

/-- Bit-packing helpers using prefix `Nat.div`/`Nat.mod` only (`TrustedBoundary`). -/
noncomputable def pack2x32 (lo hi : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 (lo.toNat + hi.toNat * 4294967296)

noncomputable def unpackLo32 (w : BitVec 64) : BitVec 32 :=
  BitVec.ofNat 32 (Nat.mod w.toNat 4294967296)

noncomputable def unpackHi32 (w : BitVec 64) : BitVec 32 :=
  BitVec.ofNat 32 (Nat.div w.toNat 4294967296)

noncomputable def pack2x64 (lo hi : BitVec 64) : BitVec 128 :=
  BitVec.ofNat 128 (lo.toNat + hi.toNat * 18446744073709551616)

noncomputable def zext64To128 (w : BitVec 64) : BitVec 128 :=
  BitVec.ofNat 128 w.toNat

noncomputable def trunc128To64 (v : BitVec 128) : BitVec 64 :=
  BitVec.ofNat 64 (Nat.mod v.toNat 18446744073709551616)

noncomputable def hi64Of128 (v : BitVec 128) : BitVec 64 :=
  BitVec.ofNat 64 (Nat.div v.toNat 18446744073709551616)

noncomputable def zext32To64 (w : BitVec 32) : BitVec 64 :=
  BitVec.ofNat 64 w.toNat

noncomputable def trunc64To32 (w : BitVec 64) : BitVec 32 :=
  BitVec.ofNat 32 (Nat.mod w.toNat 4294967296)

noncomputable def zext32To128 (w : BitVec 32) : BitVec 128 :=
  BitVec.ofNat 128 w.toNat

noncomputable def trunc128To32 (v : BitVec 128) : BitVec 32 :=
  BitVec.ofNat 32 (Nat.mod v.toNat 4294967296)

/-- Bit-exact serialization of `AbiVal` to flat 64-bit memory words (used for
all indirect argument and `sret` return buffers — zero `AbiVal` smuggling). -/
noncomputable def encodeValWords : AbiVal → List (BitVec 64)
  | .zst => []
  | .intScalar _ bits => [bits]
  | .float32 bits => [zext32To64 bits]
  | .float64 bits => [bits]
  | .nicheNonNull bits => [bits]
  | .hfa2F64 a b => [a, b]
  | .hfa4F32 a b c d => [pack2x32 a b, pack2x32 c d]
  | .simd4F32 bits => [trunc128To64 bits, hi64Of128 bits]
  | .bigStruct ws => ws

/-- Bit-exact deserialization of flat 64-bit memory words back to `AbiVal`
guided strictly by `expectedTy`. -/
noncomputable def decodeValWords (ty : AbiTy) (ws : List (BitVec 64)) :
    Except AbiError AbiVal :=
  match ty, ws with
  | .zst _, [] => .ok .zst
  | .intScalar b, [bits] =>
    if (Nat.beq b 1 || Nat.beq b 2 || Nat.beq b 4 || Nat.beq b 8) &&
       (if Nat.blt b 8 then Nat.blt bits.toNat (Nat.pow 2 (b * 8)) else true) then
      .ok (.intScalar b bits)
    else .error .typeMismatch
  | .float32, [w] => .ok (.float32 (trunc64To32 w))
  | .float64, [w] => .ok (.float64 w)
  | .nicheNonNull, [w] => .ok (.nicheNonNull w)
  | .hfa2F64, [a, b] => .ok (.hfa2F64 a b)
  | .hfa4F32, [w0, w1] =>
    .ok (.hfa4F32 (unpackLo32 w0) (unpackHi32 w0) (unpackLo32 w1) (unpackHi32 w1))
  | .simd4F32, [lo, hi] => .ok (.simd4F32 (pack2x64 lo hi))
  | .bigStruct n, ws =>
    if Nat.beq ws.length n && Nat.blt 2 n then .ok (.bigStruct ws)
    else .error .wordLengthMismatch
  | _, _ => .error .wordLengthMismatch

/-- Write/read the caller-allocated `sret` buffer pointer according to `SretLoc`. -/
noncomputable def initSretBuffer (sLoc : SretLoc) (f : PhysFrame) : PhysFrame :=
  match sLoc with
  | .none => f
  | .gpr0 =>
    let (tok, f') := allocMemWords f []
    putGpr f' 0 (BitVec.ofNat 64 tok)
  | .gpr8 =>
    let (tok, f') := allocMemWords f []
    putGpr f' 8 (BitVec.ofNat 64 tok)
  | .stack0 =>
    let (tok, f') := allocMemWords f []
    putStack f' 0 (BitVec.ofNat 64 tok)

noncomputable def readSretTok (sLoc : SretLoc) (f : PhysFrame) : Option Nat :=
  match sLoc with
  | .none => none
  | .gpr0 => match assocLookup 0 f.gprs with | some w => some w.toNat | none => none
  | .gpr8 => match assocLookup 8 f.gprs with | some w => some w.toNat | none => none
  | .stack0 => match assocLookup 0 f.stack with | some w => some w.toNat | none => none

/-- Marshal one argument value into `PhysFrame` according to `ArgPassMode`,
enforcing `checkValHasTy` on indirect modes as well as direct modes. -/
noncomputable def marshalOneArg (f : PhysFrame) (mode : ArgPassMode)
    (v : AbiVal) : Except AbiError PhysFrame :=
  match mode, v with
  | .ignore, .zst => .ok f
  | .directGpr r b, .intScalar b' bits =>
    if checkValHasTy (.intScalar b' bits) (.intScalar b) then
      .ok (putGpr f r bits)
    else .error .typeMismatch
  | .directGpr r 8, .nicheNonNull bits => .ok (putGpr f r bits)
  | .directF32 r, .float32 bits => .ok (putXmm f r (zext32To128 bits))
  | .directF64 r, .float64 bits => .ok (putXmm f r (zext64To128 bits))
  | .directPairF64 r0, .hfa2F64 a b =>
    .ok (putXmm (putXmm f r0 (zext64To128 a)) (r0 + 1) (zext64To128 b))
  | .directPairF64 r0, .hfa4F32 a b c d =>
    .ok (putXmm (putXmm f r0 (zext64To128 (pack2x32 a b)))
                (r0 + 1) (zext64To128 (pack2x32 c d)))
  | .directQuadF32 r0, .hfa4F32 a b c d =>
    let f1 := putXmm f r0 (zext32To128 a)
    let f2 := putXmm f1 (r0 + 1) (zext32To128 b)
    let f3 := putXmm f2 (r0 + 2) (zext32To128 c)
    .ok (putXmm f3 (r0 + 3) (zext32To128 d))
  | .directVec128 r, .simd4F32 bits => .ok (putXmm f r bits)
  | .indirectGpr r expTy, v =>
    if checkValHasTy v expTy then
      let (tok, f') := allocMemWords f (encodeValWords v)
      .ok (putGpr f' r (BitVec.ofNat 64 tok))
    else .error .typeMismatch
  | .indirectStack s _ expTy, v =>
    if checkValHasTy v expTy then
      let (tok, f') := allocMemWords f (encodeValWords v)
      .ok (putStack f' s (BitVec.ofNat 64 tok))
    else .error .typeMismatch
  | .directStack s (.intScalar b), .intScalar b' bits =>
    if checkValHasTy (.intScalar b' bits) (.intScalar b) then
      .ok (putStack f s bits)
    else .error .typeMismatch
  | .directStack s .nicheNonNull, .nicheNonNull bits => .ok (putStack f s bits)
  | .directStack s .float32, .float32 bits => .ok (putStack f s (zext32To64 bits))
  | .directStack s .float64, .float64 bits => .ok (putStack f s bits)
  | .directStack s .hfa2F64, .hfa2F64 a b =>
    .ok (putStack (putStack f s a) (s + 1) b)
  | .directStack s .hfa4F32, .hfa4F32 a b c d =>
    .ok (putStack (putStack f s (pack2x32 a b)) (s + 1) (pack2x32 c d))
  | .directStack s .simd4F32, .simd4F32 bits =>
    .ok (putStack (putStack f s (trunc128To64 bits)) (s + 1) (hi64Of128 bits))
  | _, _ => .error .modeMismatch

/-- Unmarshal one argument value from `PhysFrame` according to `(mode, ty)`. -/
noncomputable def unmarshalOneArg (f : PhysFrame) (mode : ArgPassMode)
    (ty : AbiTy) : Except AbiError AbiVal :=
  match mode, ty with
  | .ignore, .zst _ => .ok .zst
  | .directGpr r b, .intScalar b' =>
    if Nat.beq b b' then
      match assocLookup r f.gprs with
      | some bits =>
        if checkValHasTy (.intScalar b bits) (.intScalar b) then .ok (.intScalar b bits)
        else .error .typeMismatch
      | none => .error .missingReg
    else .error .typeMismatch
  | .directGpr r 8, .nicheNonNull =>
    match assocLookup r f.gprs with
    | some bits => .ok (.nicheNonNull bits)
    | none => .error .missingReg
  | .directF32 r, .float32 =>
    match assocLookup r f.xmms with
    | some v => .ok (.float32 (trunc128To32 v))
    | none => .error .missingReg
  | .directF64 r, .float64 =>
    match assocLookup r f.xmms with
    | some v => .ok (.float64 (trunc128To64 v))
    | none => .error .missingReg
  | .directPairF64 r0, .hfa2F64 =>
    match assocLookup r0 f.xmms, assocLookup (r0 + 1) f.xmms with
    | some v0, some v1 => .ok (.hfa2F64 (trunc128To64 v0) (trunc128To64 v1))
    | _, _ => .error .missingReg
  | .directPairF64 r0, .hfa4F32 =>
    match assocLookup r0 f.xmms, assocLookup (r0 + 1) f.xmms with
    | some v0, some v1 =>
      let w0 := trunc128To64 v0
      let w1 := trunc128To64 v1
      .ok (.hfa4F32 (unpackLo32 w0) (unpackHi32 w0) (unpackLo32 w1) (unpackHi32 w1))
    | _, _ => .error .missingReg
  | .directQuadF32 r0, .hfa4F32 =>
    match assocLookup r0 f.xmms, assocLookup (r0 + 1) f.xmms,
          assocLookup (r0 + 2) f.xmms, assocLookup (r0 + 3) f.xmms with
    | some v0, some v1, some v2, some v3 =>
      .ok (.hfa4F32 (trunc128To32 v0) (trunc128To32 v1)
                    (trunc128To32 v2) (trunc128To32 v3))
    | _, _, _, _ => .error .missingReg
  | .directVec128 r, .simd4F32 =>
    match assocLookup r f.xmms with
    | some v => .ok (.simd4F32 v)
    | none => .error .missingReg
  | .indirectGpr r expTy, ty =>
    if abiTyEq expTy ty then
      match assocLookup r f.gprs with
      | none => .error .missingReg
      | some tokBits =>
        match assocLookup tokBits.toNat f.mem with
        | some ws => decodeValWords ty ws
        | none => .error .missingIndirectSlot
    else .error .typeMismatch
  | .indirectStack s _ expTy, ty =>
    if abiTyEq expTy ty then
      match assocLookup s f.stack with
      | none => .error .missingStackSlot
      | some tokBits =>
        match assocLookup tokBits.toNat f.mem with
        | some ws => decodeValWords ty ws
        | none => .error .missingIndirectSlot
    else .error .typeMismatch
  | .directStack s (.intScalar b), .intScalar b' =>
    if Nat.beq b b' then
      match assocLookup s f.stack with
      | some bits =>
        if checkValHasTy (.intScalar b bits) (.intScalar b) then .ok (.intScalar b bits)
        else .error .typeMismatch
      | none => .error .missingStackSlot
    else .error .typeMismatch
  | .directStack s .nicheNonNull, .nicheNonNull =>
    match assocLookup s f.stack with
    | some bits => .ok (.nicheNonNull bits)
    | none => .error .missingStackSlot
  | .directStack s .float32, .float32 =>
    match assocLookup s f.stack with
    | some w => .ok (.float32 (trunc64To32 w))
    | none => .error .missingStackSlot
  | .directStack s .float64, .float64 =>
    match assocLookup s f.stack with
    | some w => .ok (.float64 w)
    | none => .error .missingStackSlot
  | .directStack s .hfa2F64, .hfa2F64 =>
    match assocLookup s f.stack, assocLookup (s + 1) f.stack with
    | some a, some b => .ok (.hfa2F64 a b)
    | _, _ => .error .missingStackSlot
  | .directStack s .hfa4F32, .hfa4F32 =>
    match assocLookup s f.stack, assocLookup (s + 1) f.stack with
    | some w0, some w1 =>
      .ok (.hfa4F32 (unpackLo32 w0) (unpackHi32 w0) (unpackLo32 w1) (unpackHi32 w1))
    | _, _ => .error .missingStackSlot
  | .directStack s .simd4F32, .simd4F32 =>
    match assocLookup s f.stack, assocLookup (s + 1) f.stack with
    | some lo, some hi => .ok (.simd4F32 (pack2x64 lo hi))
    | _, _ => .error .missingStackSlot
  | _, _ => .error .modeMismatch

noncomputable def marshalArgsLoop (f : PhysFrame) :
    List ArgPassMode → List AbiVal → Except AbiError PhysFrame
  | [], [] => .ok f
  | m :: ms, v :: vs =>
    match marshalOneArg f m v with
    | .error e => .error e
    | .ok f' => marshalArgsLoop f' ms vs
  | _, _ => .error .arityMismatch

/-- Marshal call entry: allocates caller's disjoint `sret` buffer first (at
token `1` in `abi.sretLoc`, if any), then marshals all arguments (allocating
argument indirect buffers at tokens `>= 2`). -/
noncomputable def marshalArgs (abi : ComputedFnAbi) (vals : List AbiVal) :
    Except AbiError PhysFrame :=
  let f0 := initSretBuffer abi.sretLoc emptyFrame
  marshalArgsLoop f0 abi.argModes vals

noncomputable def unmarshalArgsLoop (f : PhysFrame) :
    List ArgPassMode → List AbiTy → Except AbiError (List AbiVal)
  | [], [] => .ok []
  | m :: ms, t :: ts =>
    match unmarshalOneArg f m t with
    | .error e => .error e
    | .ok v =>
      match unmarshalArgsLoop f ms ts with
      | .error e => .error e
      | .ok vs => .ok (v :: vs)
  | _, _ => .error .arityMismatch

noncomputable def unmarshalArgs (abi : ComputedFnAbi) (tys : List AbiTy)
    (f : PhysFrame) : Except AbiError (List AbiVal) :=
  unmarshalArgsLoop f abi.argModes tys

/-- Marshal return value into the threaded call-entry `PhysFrame` `fCall`:
for `.indirectSret sLoc expTy`, reads the caller-allocated `sretTok` from `fCall`
at `sLoc`, verifies `checkValHasTy v expTy`, and writes serialized words into
that caller buffer (preserving all caller argument buffers disjointly!). -/
noncomputable def marshalRet (fCall : PhysFrame) (mode : RetPassMode)
    (v : AbiVal) : Except AbiError PhysFrame :=
  match mode, v with
  | .ignore, .zst => .ok fCall
  | .directGpr0 b, .intScalar b' bits =>
    if checkValHasTy (.intScalar b' bits) (.intScalar b) then
      .ok (putGpr fCall 0 bits)
    else .error .typeMismatch
  | .directGpr0 8, .nicheNonNull bits => .ok (putGpr fCall 0 bits)
  | .directGpr0 4, .float32 bits => .ok (putGpr fCall 0 (zext32To64 bits))
  | .directGpr0 8, .float64 bits => .ok (putGpr fCall 0 bits)
  | .directXmm0F32, .float32 bits => .ok (putXmm fCall 0 (zext32To128 bits))
  | .directXmm0F64, .float64 bits => .ok (putXmm fCall 0 (zext64To128 bits))
  | .directX87F32, .float32 bits =>
    .ok { fCall with x87F32 := some (x87TransferF32 bits) }
  | .directX87F64, .float64 bits =>
    .ok { fCall with x87F64 := some (x87TransferF64 bits) }
  | .directPairXmm01F64, .hfa2F64 a b =>
    .ok (putXmm (putXmm fCall 0 (zext64To128 a)) 1 (zext64To128 b))
  | .directPairXmm01F64, .hfa4F32 a b c d =>
    .ok (putXmm (putXmm fCall 0 (zext64To128 (pack2x32 a b)))
                1 (zext64To128 (pack2x32 c d)))
  | .directQuadXmm03F32, .hfa4F32 a b c d =>
    let f1 := putXmm fCall 0 (zext32To128 a)
    let f2 := putXmm f1 1 (zext32To128 b)
    let f3 := putXmm f2 2 (zext32To128 c)
    .ok (putXmm f3 3 (zext32To128 d))
  | .directXmm0Vec128, .simd4F32 bits => .ok (putXmm fCall 0 bits)
  | .indirectSret sLoc expTy, v =>
    if checkValHasTy v expTy then
      match readSretTok sLoc fCall with
      | some tok => .ok (writeMemWords fCall tok (encodeValWords v))
      | none => .error .missingSretPtr
    else .error .typeMismatch
  | _, _ => .error .modeMismatch

/-- Unmarshal return value from `PhysFrame` according to `(mode, ty)`. -/
noncomputable def unmarshalRet (mode : RetPassMode) (ty : AbiTy)
    (f : PhysFrame) : Except AbiError AbiVal :=
  match mode, ty with
  | .ignore, .zst _ => .ok .zst
  | .directGpr0 b, .intScalar b' =>
    if Nat.beq b b' then
      match assocLookup 0 f.gprs with
      | some bits =>
        if checkValHasTy (.intScalar b bits) (.intScalar b) then .ok (.intScalar b bits)
        else .error .typeMismatch
      | none => .error .missingReg
    else .error .typeMismatch
  | .directGpr0 8, .nicheNonNull =>
    match assocLookup 0 f.gprs with
    | some bits => .ok (.nicheNonNull bits)
    | none => .error .missingReg
  | .directGpr0 4, .float32 =>
    match assocLookup 0 f.gprs with
    | some w => .ok (.float32 (trunc64To32 w))
    | none => .error .missingReg
  | .directGpr0 8, .float64 =>
    match assocLookup 0 f.gprs with
    | some w => .ok (.float64 w)
    | none => .error .missingReg
  | .directXmm0F32, .float32 =>
    match assocLookup 0 f.xmms with
    | some v => .ok (.float32 (trunc128To32 v))
    | none => .error .missingReg
  | .directXmm0F64, .float64 =>
    match assocLookup 0 f.xmms with
    | some v => .ok (.float64 (trunc128To64 v))
    | none => .error .missingReg
  | .directX87F32, .float32 =>
    match f.x87F32 with
    | some bits => .ok (.float32 bits)
    | none => .error .missingReg
  | .directX87F64, .float64 =>
    match f.x87F64 with
    | some bits => .ok (.float64 bits)
    | none => .error .missingReg
  | .directPairXmm01F64, .hfa2F64 =>
    match assocLookup 0 f.xmms, assocLookup 1 f.xmms with
    | some v0, some v1 => .ok (.hfa2F64 (trunc128To64 v0) (trunc128To64 v1))
    | _, _ => .error .missingReg
  | .directPairXmm01F64, .hfa4F32 =>
    match assocLookup 0 f.xmms, assocLookup 1 f.xmms with
    | some v0, some v1 =>
      let w0 := trunc128To64 v0
      let w1 := trunc128To64 v1
      .ok (.hfa4F32 (unpackLo32 w0) (unpackHi32 w0) (unpackLo32 w1) (unpackHi32 w1))
    | _, _ => .error .missingReg
  | .directQuadXmm03F32, .hfa4F32 =>
    match assocLookup 0 f.xmms, assocLookup 1 f.xmms,
          assocLookup 2 f.xmms, assocLookup 3 f.xmms with
    | some v0, some v1, some v2, some v3 =>
      .ok (.hfa4F32 (trunc128To32 v0) (trunc128To32 v1)
                    (trunc128To32 v2) (trunc128To32 v3))
    | _, _, _, _ => .error .missingReg
  | .directXmm0Vec128, .simd4F32 =>
    match assocLookup 0 f.xmms with
    | some v => .ok (.simd4F32 v)
    | none => .error .missingReg
  | .indirectSret sLoc expTy, ty =>
    if abiTyEq expTy ty then
      match readSretTok sLoc f with
      | none => .error .missingSretPtr
      | some tok =>
        match assocLookup tok f.mem with
        | some ws => decodeValWords ty ws
        | none => .error .missingIndirectSlot
    else .error .typeMismatch
  | _, _ => .error .modeMismatch

/-! ## Part V: Static `AbiVal`-Free Physical-Frame Adapter Shim IR (`PhysShim`) -/

/-- Low-level physical read operation transferring raw `BitVec 64` words from a
caller's `PhysFrame` registers/stack/memory into an untyped word buffer — ZERO
mention of `AbiVal`, `unmarshalArgs`, or `marshalArgs`! -/
inductive PhysReadOp where
  | constEmpty
  | readGpr64 (r : Nat)
  | readXmmLo32 (r : Nat)
  | readXmmLo64 (r : Nat)
  | readXmmPair64 (r0 : Nat)
  | readXmmQuad32 (r0 : Nat)
  | readXmm128 (r : Nat)
  | readIndirectGpr (r : Nat)
  | readIndirectStack (s : Nat)
  | readStack1 (s : Nat)
  | readStack2 (s : Nat)

/-- Low-level physical write operation committing a raw `List (BitVec 64)`
scratch word buffer into a callee's physical register, stack slot, or newly
allocated indirect memory buffer. Two-phase read-to-scratch then write-from-
scratch guarantees clobber-freedom (no register-cycle hazards, matching the
scratch-buffered parallel-move discipline of `leanlib` `a02bab389d`). -/
inductive PhysWriteOp where
  | dropWords
  | writeGpr64 (r : Nat)
  | writeXmmLo32 (r : Nat)
  | writeXmmLo64 (r : Nat)
  | writeXmmPair64 (r0 : Nat)
  | writeXmmQuad32 (r0 : Nat)
  | writeXmm128 (r : Nat)
  | writeIndirectGpr (r : Nat)
  | writeIndirectStack (s : Nat)
  | writeStack1 (s : Nat)
  | writeStack2 (s : Nat)

/-- Physical read/write ops for return-boundary adapter shims. -/
inductive PhysRetReadOp where
  | constEmpty
  | readGpr0
  | readXmm0Lo32
  | readXmm0Lo64
  | readX87F32
  | readX87F64
  | readXmm01Pair64
  | readXmm03Quad32
  | readXmm0Vec128
  | readIndirectSret (loc : SretLoc)

inductive PhysRetWriteOp where
  | dropWords
  | writeGpr0
  | writeXmm0Lo32
  | writeXmm0Lo64
  | writeX87F32
  | writeX87F64
  | writeXmm01Pair64
  | writeXmm03Quad32
  | writeXmm0Vec128
  | writeIndirectSret (loc : SretLoc)

/-- Complete statically compiled cross-release call-boundary shim plan:
separates register/stack/memory `argReads`/`argWrites` and `retRead`/`retWrite`
from explicit linker-symbol aliasing (`needsLinkerAlias` for `D4` `@@16 <-> @@24`). -/
structure CompiledShimPlan where
  argReads : List PhysReadOp
  argWrites : List PhysWriteOp
  calleeSretLoc : SretLoc
  retRead : PhysRetReadOp
  retWrite : PhysRetWriteOp
  callerSymbolRule : LinkerSymbolRule
  calleeSymbolRule : LinkerSymbolRule
  needsLinkerAlias : Bool

noncomputable def compileArgReadOp : ArgPassMode → AbiTy → PhysReadOp
  | .ignore, _ => .constEmpty
  | .directGpr r _, _ => .readGpr64 r
  | .directF32 r, _ => .readXmmLo32 r
  | .directF64 r, _ => .readXmmLo64 r
  | .directPairF64 r0, _ => .readXmmPair64 r0
  | .directQuadF32 r0, _ => .readXmmQuad32 r0
  | .directVec128 r, _ => .readXmm128 r
  | .indirectGpr r _, _ => .readIndirectGpr r
  | .indirectStack s _ _, _ => .readIndirectStack s
  | .directStack s .hfa2F64, _ => .readStack2 s
  | .directStack s .hfa4F32, _ => .readStack2 s
  | .directStack s .simd4F32, _ => .readStack2 s
  | .directStack s _, _ => .readStack1 s

noncomputable def compileArgWriteOp : ArgPassMode → AbiTy → PhysWriteOp
  | .ignore, _ => .dropWords
  | .directGpr r _, _ => .writeGpr64 r
  | .directF32 r, _ => .writeXmmLo32 r
  | .directF64 r, _ => .writeXmmLo64 r
  | .directPairF64 r0, _ => .writeXmmPair64 r0
  | .directQuadF32 r0, _ => .writeXmmQuad32 r0
  | .directVec128 r, _ => .writeXmm128 r
  | .indirectGpr r _, _ => .writeIndirectGpr r
  | .indirectStack s _ _, _ => .writeIndirectStack s
  | .directStack s .hfa2F64, _ => .writeStack2 s
  | .directStack s .hfa4F32, _ => .writeStack2 s
  | .directStack s .simd4F32, _ => .writeStack2 s
  | .directStack s _, _ => .writeStack1 s

noncomputable def compileArgReads : List ArgPassMode → List AbiTy → List PhysReadOp
  | m :: ms, t :: ts => compileArgReadOp m t :: compileArgReads ms ts
  | _, _ => []

noncomputable def compileArgWrites : List ArgPassMode → List AbiTy → List PhysWriteOp
  | m :: ms, t :: ts => compileArgWriteOp m t :: compileArgWrites ms ts
  | _, _ => []

noncomputable def compileRetReadOp : RetPassMode → PhysRetReadOp
  | .ignore => .constEmpty
  | .directGpr0 _ => .readGpr0
  | .directXmm0F32 => .readXmm0Lo32
  | .directXmm0F64 => .readXmm0Lo64
  | .directX87F32 => .readX87F32
  | .directX87F64 => .readX87F64
  | .directPairXmm01F64 => .readXmm01Pair64
  | .directQuadXmm03F32 => .readXmm03Quad32
  | .directXmm0Vec128 => .readXmm0Vec128
  | .indirectSret loc _ => .readIndirectSret loc

noncomputable def compileRetWriteOp : RetPassMode → PhysRetWriteOp
  | .ignore => .dropWords
  | .directGpr0 _ => .writeGpr0
  | .directXmm0F32 => .writeXmm0Lo32
  | .directXmm0F64 => .writeXmm0Lo64
  | .directX87F32 => .writeX87F32
  | .directX87F64 => .writeX87F64
  | .directPairXmm01F64 => .writeXmm01Pair64
  | .directQuadXmm03F32 => .writeXmm03Quad32
  | .directXmm0Vec128 => .writeXmm0Vec128
  | .indirectSret loc _ => .writeIndirectSret loc

/-- Static compiler from `(abiCaller, abiCallee, sig)` to a physical-frame
`CompiledShimPlan` (purely on ABI metadata, zero runtime `AbiVal` access). -/
noncomputable def compileShimPlan (abiCaller abiCallee : ComputedFnAbi)
    (sig : FnSig) : CompiledShimPlan :=
  {
    argReads := compileArgReads abiCaller.argModes sig.args
    argWrites := compileArgWrites abiCallee.argModes sig.args
    calleeSretLoc := abiCallee.sretLoc
    retRead := compileRetReadOp abiCallee.retMode
    retWrite := compileRetWriteOp abiCaller.retMode
    callerSymbolRule := abiCaller.symbolRule
    calleeSymbolRule := abiCallee.symbolRule
    needsLinkerAlias := !symbolRuleEq abiCaller.symbolRule abiCallee.symbolRule
  }

/-- Execute one physical read op into canonical flat `BitVec 64` words. -/
noncomputable def execPhysRead (f : PhysFrame) :
    PhysReadOp → Except AbiError (List (BitVec 64))
  | .constEmpty => .ok []
  | .readGpr64 r =>
    match assocLookup r f.gprs with | some w => .ok [w] | none => .error .missingReg
  | .readXmmLo32 r =>
    match assocLookup r f.xmms with
    | some v => .ok [zext32To64 (trunc128To32 v)]
    | none => .error .missingReg
  | .readXmmLo64 r =>
    match assocLookup r f.xmms with
    | some v => .ok [trunc128To64 v]
    | none => .error .missingReg
  | .readXmmPair64 r0 =>
    match assocLookup r0 f.xmms, assocLookup (r0 + 1) f.xmms with
    | some v0, some v1 => .ok [trunc128To64 v0, trunc128To64 v1]
    | _, _ => .error .missingReg
  | .readXmmQuad32 r0 =>
    match assocLookup r0 f.xmms, assocLookup (r0 + 1) f.xmms,
          assocLookup (r0 + 2) f.xmms, assocLookup (r0 + 3) f.xmms with
    | some v0, some v1, some v2, some v3 =>
      .ok [pack2x32 (trunc128To32 v0) (trunc128To32 v1),
           pack2x32 (trunc128To32 v2) (trunc128To32 v3)]
    | _, _, _, _ => .error .missingReg
  | .readXmm128 r =>
    match assocLookup r f.xmms with
    | some v => .ok [trunc128To64 v, hi64Of128 v]
    | none => .error .missingReg
  | .readIndirectGpr r =>
    match assocLookup r f.gprs with
    | none => .error .missingReg
    | some tok =>
      match assocLookup tok.toNat f.mem with
      | some ws => .ok ws
      | none => .error .missingIndirectSlot
  | .readIndirectStack s =>
    match assocLookup s f.stack with
    | none => .error .missingStackSlot
    | some tok =>
      match assocLookup tok.toNat f.mem with
      | some ws => .ok ws
      | none => .error .missingIndirectSlot
  | .readStack1 s =>
    match assocLookup s f.stack with | some w => .ok [w] | none => .error .missingStackSlot
  | .readStack2 s =>
    match assocLookup s f.stack, assocLookup (s + 1) f.stack with
    | some w0, some w1 => .ok [w0, w1]
    | _, _ => .error .missingStackSlot

/-- Execute one physical write op from raw `BitVec 64` words into `f`. -/
noncomputable def execPhysWrite (f : PhysFrame) (op : PhysWriteOp)
    (ws : List (BitVec 64)) : Except AbiError PhysFrame :=
  match op, ws with
  | .dropWords, [] => .ok f
  | .writeGpr64 r, [w] => .ok (putGpr f r w)
  | .writeXmmLo32 r, [w] => .ok (putXmm f r (zext32To128 (trunc64To32 w)))
  | .writeXmmLo64 r, [w] => .ok (putXmm f r (zext64To128 w))
  | .writeXmmPair64 r0, [w0, w1] =>
    .ok (putXmm (putXmm f r0 (zext64To128 w0)) (r0 + 1) (zext64To128 w1))
  | .writeXmmQuad32 r0, [w0, w1] =>
    let f1 := putXmm f r0 (zext32To128 (unpackLo32 w0))
    let f2 := putXmm f1 (r0 + 1) (zext32To128 (unpackHi32 w0))
    let f3 := putXmm f2 (r0 + 2) (zext32To128 (unpackLo32 w1))
    .ok (putXmm f3 (r0 + 3) (zext32To128 (unpackHi32 w1)))
  | .writeXmm128 r, [lo, hi] => .ok (putXmm f r (pack2x64 lo hi))
  | .writeIndirectGpr r, ws =>
    let (tok, f') := allocMemWords f ws
    .ok (putGpr f' r (BitVec.ofNat 64 tok))
  | .writeIndirectStack s, ws =>
    let (tok, f') := allocMemWords f ws
    .ok (putStack f' s (BitVec.ofNat 64 tok))
  | .writeStack1 s, [w] => .ok (putStack f s w)
  | .writeStack2 s, [w0, w1] => .ok (putStack (putStack f s w0) (s + 1) w1)
  | _, _ => .error .wordLengthMismatch

noncomputable def execPhysReads (f : PhysFrame) :
    List PhysReadOp → Except AbiError (List (List (BitVec 64)))
  | [] => .ok []
  | op :: ops =>
    match execPhysRead f op with
    | .error e => .error e
    | .ok ws =>
      match execPhysReads f ops with
      | .error e => .error e
      | .ok rest => .ok (ws :: rest)

noncomputable def execPhysWrites (f : PhysFrame) :
    List PhysWriteOp → List (List (BitVec 64)) → Except AbiError PhysFrame
  | [], [] => .ok f
  | op :: ops, ws :: wss =>
    match execPhysWrite f op ws with
    | .error e => .error e
    | .ok f' => execPhysWrites f' ops wss
  | _, _ => .error .arityMismatch

/-- Execute compiled physical argument shim: phase 1 reads all caller slots
into disjoint raw word buffers (zero clobber hazards!); phase 2 allocates a
fresh disjoint callee `sret` buffer (if needed) and commits every scratch buffer
into the callee's physical frame. -/
noncomputable def execArgShim (plan : CompiledShimPlan) (fCaller : PhysFrame) :
    Except AbiError PhysFrame :=
  match execPhysReads fCaller plan.argReads with
  | .error e => .error e
  | .ok scratch =>
    let fCallee0 := initSretBuffer plan.calleeSretLoc emptyFrame
    execPhysWrites fCallee0 plan.argWrites scratch

/-- Execute compiled physical return shim bridging callee's return frame
`fCalleeOut` into caller's original call-entry frame `fCallerIn` (writing into
caller's `sret` buffer when caller expects `indirectSret`, or into caller's
return register/x87 slot otherwise). -/
noncomputable def execRetRead (f : PhysFrame) :
    PhysRetReadOp → Except AbiError (List (BitVec 64))
  | .constEmpty => .ok []
  | .readGpr0 =>
    match assocLookup 0 f.gprs with | some w => .ok [w] | none => .error .missingReg
  | .readXmm0Lo32 =>
    match assocLookup 0 f.xmms with
    | some v => .ok [zext32To64 (trunc128To32 v)]
    | none => .error .missingReg
  | .readXmm0Lo64 =>
    match assocLookup 0 f.xmms with
    | some v => .ok [trunc128To64 v]
    | none => .error .missingReg
  | .readX87F32 =>
    match f.x87F32 with | some b => .ok [zext32To64 b] | none => .error .missingReg
  | .readX87F64 =>
    match f.x87F64 with | some b => .ok [b] | none => .error .missingReg
  | .readXmm01Pair64 =>
    match assocLookup 0 f.xmms, assocLookup 1 f.xmms with
    | some v0, some v1 => .ok [trunc128To64 v0, trunc128To64 v1]
    | _, _ => .error .missingReg
  | .readXmm03Quad32 =>
    match assocLookup 0 f.xmms, assocLookup 1 f.xmms,
          assocLookup 2 f.xmms, assocLookup 3 f.xmms with
    | some v0, some v1, some v2, some v3 =>
      .ok [pack2x32 (trunc128To32 v0) (trunc128To32 v1),
           pack2x32 (trunc128To32 v2) (trunc128To32 v3)]
    | _, _, _, _ => .error .missingReg
  | .readXmm0Vec128 =>
    match assocLookup 0 f.xmms with
    | some v => .ok [trunc128To64 v, hi64Of128 v]
    | none => .error .missingReg
  | .readIndirectSret loc =>
    match readSretTok loc f with
    | none => .error .missingSretPtr
    | some tok =>
      match assocLookup tok f.mem with
      | some ws => .ok ws
      | none => .error .missingIndirectSlot

noncomputable def execRetWrite (fCallerIn : PhysFrame) (op : PhysRetWriteOp)
    (ws : List (BitVec 64)) : Except AbiError PhysFrame :=
  match op, ws with
  | .dropWords, [] => .ok fCallerIn
  | .writeGpr0, [w] => .ok (putGpr fCallerIn 0 w)
  | .writeXmm0Lo32, [w] => .ok (putXmm fCallerIn 0 (zext32To128 (trunc64To32 w)))
  | .writeXmm0Lo64, [w] => .ok (putXmm fCallerIn 0 (zext64To128 w))
  | .writeX87F32, [w] => .ok { fCallerIn with x87F32 := some (x87TransferF32 (trunc64To32 w)) }
  | .writeX87F64, [w] => .ok { fCallerIn with x87F64 := some (x87TransferF64 w) }
  | .writeXmm01Pair64, [w0, w1] =>
    .ok (putXmm (putXmm fCallerIn 0 (zext64To128 w0)) 1 (zext64To128 w1))
  | .writeXmm03Quad32, [w0, w1] =>
    let f1 := putXmm fCallerIn 0 (zext32To128 (unpackLo32 w0))
    let f2 := putXmm f1 1 (zext32To128 (unpackHi32 w0))
    let f3 := putXmm f2 2 (zext32To128 (unpackLo32 w1))
    .ok (putXmm f3 3 (zext32To128 (unpackHi32 w1)))
  | .writeXmm0Vec128, [lo, hi] => .ok (putXmm fCallerIn 0 (pack2x64 lo hi))
  | .writeIndirectSret loc, ws =>
    match readSretTok loc fCallerIn with
    | some tok => .ok (writeMemWords fCallerIn tok ws)
    | none => .error .missingSretPtr
  | _, _ => .error .wordLengthMismatch

noncomputable def execRetShim (plan : CompiledShimPlan)
    (fCallerIn fCalleeOut : PhysFrame) : Except AbiError PhysFrame :=
  match execRetRead fCalleeOut plan.retRead with
  | .error e => .error e
  | .ok ws => execRetWrite fCallerIn plan.retWrite ws


/-! ## Stage 4 Constructive Proof Helpers (`private`, 0 `Classical.choice`, 0 `omega`) -/

section Stage4ProofHelpers

private theorem nat_beq_refl : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | Nat.succ n => nat_beq_refl n

private theorem nat_eq_of_beq_aux : ∀ (a b : Nat), Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | Nat.succ a, Nat.succ b, h => congrArg Nat.succ (nat_eq_of_beq_aux a b h)

private theorem nat_eq_of_beq {a b : Nat} (h : Nat.beq a b = true) : a = b :=
  nat_eq_of_beq_aux a b h

private theorem nat_beq_false_of_ne_aux : ∀ (a b : Nat), a ≠ b → Nat.beq a b = false
  | 0, 0, h => False.elim (h rfl)
  | 0, Nat.succ _, _ => rfl
  | Nat.succ _, 0, _ => rfl
  | Nat.succ a, Nat.succ b, h =>
      nat_beq_false_of_ne_aux a b (fun heq => h (congrArg Nat.succ heq))

private theorem nat_beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  nat_beq_false_of_ne_aux a b h

private theorem nat_ble_of_le_aux : ∀ (a b : Nat), a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | Nat.succ _, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | Nat.succ a, Nat.succ b, h => nat_ble_of_le_aux a b (Nat.le_of_succ_le_succ h)

private theorem nat_ble_of_le {a b : Nat} (h : a ≤ b) : Nat.ble a b = true :=
  nat_ble_of_le_aux a b h

private theorem nat_le_of_ble_aux : ∀ (a b : Nat), Nat.ble a b = true → a ≤ b
  | 0, _, _ => Nat.zero_le _
  | Nat.succ a, Nat.succ b, h => Nat.succ_le_succ (nat_le_of_ble_aux a b h)

private theorem nat_le_of_ble {a b : Nat} (h : Nat.ble a b = true) : a ≤ b :=
  nat_le_of_ble_aux a b h

private theorem nat_blt_of_lt {a b : Nat} (h : a < b) : Nat.blt a b = true :=
  nat_ble_of_le h

private theorem nat_lt_of_blt {a b : Nat} (h : Nat.blt a b = true) : a < b :=
  nat_le_of_ble h

private theorem nat_mod_eq_of_lt {a b : Nat} (h : a < b) : Nat.mod a b = a :=
  Nat.mod_eq_of_lt h

private theorem nat_mod_eq_sub_mod {a b : Nat} (h : b ≤ a) : Nat.mod a b = Nat.mod (a - b) b :=
  Nat.mod_eq_sub_mod h

private theorem nat_div_add_mod (m n : Nat) : n * Nat.div m n + Nat.mod m n = m :=
  Nat.div_add_mod m n

private theorem nat_mod_add_div (m k : Nat) : Nat.mod m k + k * Nat.div m k = m :=
  Nat.mod_add_div m k

private theorem nat_add_mul_div_right (x y : Nat) {z : Nat} (hz : 0 < z) :
    Nat.div (x + y * z) z = Nat.div x z + y :=
  Nat.add_mul_div_right x y hz

private theorem nat_div_eq_of_lt {a b : Nat} (h : a < b) : Nat.div a b = 0 :=
  Nat.div_eq_of_lt h

private theorem nat_div_lt_iff_lt_mul {x y k : Nat} (hk : 0 < k) :
    Nat.div x k < y ↔ x < y * k :=
  Nat.div_lt_iff_lt_mul hk

private theorem nat_mod_lt (x : Nat) {y : Nat} (hy : 0 < y) : Nat.mod x y < y :=
  Nat.mod_lt x hy

private theorem bool_and_true_iff {a b : Bool} : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp

private theorem bv_eq_of_toNat {w : Nat} {x y : BitVec w} (h : x.toNat = y.toNat) : x = y := by
  cases x
  cases y
  exact congrArg BitVec.ofFin (Fin.eq_of_val_eq h)

private theorem bv_toNat_ofNat (w n : Nat) :
    (BitVec.ofNat w n).toNat = Nat.mod n (Nat.pow 2 w) := rfl

private theorem bv_toNat_ofNat_of_lt {w n : Nat} (h : n < Nat.pow 2 w) :
    (BitVec.ofNat w n).toNat = n :=
  nat_mod_eq_of_lt h

private theorem nat_mod_add_mul_right (a k : Nat) :
    ∀ b : Nat, Nat.mod (a + b * k) k = Nat.mod a k
  | 0 => by simp
  | b + 1 => by
    have h1 : a + (b + 1) * k = (a + b * k) + k := by
      rw [Nat.succ_mul, Nat.add_assoc]
    rw [h1]
    have hk : k ≤ a + b * k + k := Nat.le_add_left k (a + b * k)
    have hsub : Nat.mod (a + b * k + k) k = Nat.mod (a + b * k + k - k) k :=
      nat_mod_eq_sub_mod hk
    rw [hsub, Nat.add_sub_cancel]
    exact nat_mod_add_mul_right a k b

private theorem pow2_32_eq : Nat.pow 2 32 = 4294967296 := rfl
private theorem pow2_64_eq : Nat.pow 2 64 = 18446744073709551616 := rfl
private theorem pow2_128_eq : Nat.pow 2 128 = 18446744073709551616 * 18446744073709551616 := rfl
private theorem pow2_64_mul_eq : 4294967296 * 4294967296 = 18446744073709551616 := rfl

private theorem bv32_lt_pow64 (w : BitVec 32) : w.toNat < Nat.pow 2 64 :=
  Nat.lt_trans w.isLt (by decide)

private theorem bv32_lt_pow128 (w : BitVec 32) : w.toNat < Nat.pow 2 128 :=
  Nat.lt_trans w.isLt (by decide)

private theorem bv64_lt_pow128 (w : BitVec 64) : w.toNat < Nat.pow 2 128 :=
  Nat.lt_trans w.isLt (by decide)

private theorem trunc64To32_zext32To64 (w : BitVec 32) :
    trunc64To32 (zext32To64 w) = w := by
  apply bv_eq_of_toNat
  unfold trunc64To32 zext32To64
  rw [bv_toNat_ofNat_of_lt (bv32_lt_pow64 w)]
  rw [bv_toNat_ofNat]
  rw [← pow2_32_eq]
  rw [nat_mod_eq_of_lt w.isLt, nat_mod_eq_of_lt w.isLt]

private theorem trunc128To32_zext32To128 (w : BitVec 32) :
    trunc128To32 (zext32To128 w) = w := by
  apply bv_eq_of_toNat
  unfold trunc128To32 zext32To128
  rw [bv_toNat_ofNat_of_lt (bv32_lt_pow128 w)]
  rw [bv_toNat_ofNat]
  rw [← pow2_32_eq]
  rw [nat_mod_eq_of_lt w.isLt, nat_mod_eq_of_lt w.isLt]

private theorem trunc128To64_zext64To128 (w : BitVec 64) :
    trunc128To64 (zext64To128 w) = w := by
  apply bv_eq_of_toNat
  unfold trunc128To64 zext64To128
  rw [bv_toNat_ofNat_of_lt (bv64_lt_pow128 w)]
  rw [bv_toNat_ofNat]
  rw [← pow2_64_eq]
  rw [nat_mod_eq_of_lt w.isLt, nat_mod_eq_of_lt w.isLt]

private theorem pack2x32_bound (lo hi : BitVec 32) :
    lo.toNat + hi.toNat * 4294967296 < Nat.pow 2 64 := by
  have hlo : lo.toNat < 4294967296 := lo.isLt
  have hhi : hi.toNat < 4294967296 := hi.isLt
  have h1 : hi.toNat + 1 ≤ 4294967296 := Nat.succ_le_of_lt hhi
  have h2 : lo.toNat + hi.toNat * 4294967296 < 4294967296 + hi.toNat * 4294967296 :=
    Nat.add_lt_add_right hlo _
  have h3 : 4294967296 + hi.toNat * 4294967296 = (hi.toNat + 1) * 4294967296 := by
    rw [Nat.succ_mul, Nat.add_comm]
  have h4 : (hi.toNat + 1) * 4294967296 ≤ 4294967296 * 4294967296 :=
    Nat.mul_le_mul_right 4294967296 h1
  rw [pow2_64_eq, ← pow2_64_mul_eq]
  rw [h3] at h2
  exact Nat.lt_of_lt_of_le h2 h4

private theorem unpackLo32_pack2x32 (lo hi : BitVec 32) :
    unpackLo32 (pack2x32 lo hi) = lo := by
  apply bv_eq_of_toNat
  unfold unpackLo32 pack2x32
  rw [bv_toNat_ofNat_of_lt (pack2x32_bound lo hi)]
  rw [nat_mod_add_mul_right]
  rw [bv_toNat_ofNat, ← pow2_32_eq]
  rw [nat_mod_eq_of_lt lo.isLt, nat_mod_eq_of_lt lo.isLt]

private theorem unpackHi32_pack2x32 (lo hi : BitVec 32) :
    unpackHi32 (pack2x32 lo hi) = hi := by
  apply bv_eq_of_toNat
  unfold unpackHi32 pack2x32
  rw [bv_toNat_ofNat_of_lt (pack2x32_bound lo hi)]
  have hpos : 0 < 4294967296 := by decide
  rw [nat_add_mul_div_right lo.toNat hi.toNat hpos]
  have hzero : Nat.div lo.toNat 4294967296 = 0 := nat_div_eq_of_lt lo.isLt
  rw [hzero, Nat.zero_add]
  rw [bv_toNat_ofNat, nat_mod_eq_of_lt hi.isLt]

private theorem pack2x64_bound (lo hi : BitVec 64) :
    lo.toNat + hi.toNat * 18446744073709551616 < Nat.pow 2 128 := by
  have hlo : lo.toNat < 18446744073709551616 := lo.isLt
  have hhi : hi.toNat < 18446744073709551616 := hi.isLt
  have h1 : hi.toNat + 1 ≤ 18446744073709551616 := Nat.succ_le_of_lt hhi
  have h2 : lo.toNat + hi.toNat * 18446744073709551616 <
      18446744073709551616 + hi.toNat * 18446744073709551616 :=
    Nat.add_lt_add_right hlo _
  have h3 : 18446744073709551616 + hi.toNat * 18446744073709551616 =
      (hi.toNat + 1) * 18446744073709551616 := by
    rw [Nat.succ_mul, Nat.add_comm]
  have h4 : (hi.toNat + 1) * 18446744073709551616 ≤
      18446744073709551616 * 18446744073709551616 :=
    Nat.mul_le_mul_right 18446744073709551616 h1
  rw [pow2_128_eq]
  rw [h3] at h2
  exact Nat.lt_of_lt_of_le h2 h4

private theorem trunc128To64_pack2x64 (lo hi : BitVec 64) :
    trunc128To64 (pack2x64 lo hi) = lo := by
  apply bv_eq_of_toNat
  unfold trunc128To64 pack2x64
  rw [bv_toNat_ofNat_of_lt (pack2x64_bound lo hi)]
  rw [nat_mod_add_mul_right]
  rw [bv_toNat_ofNat, ← pow2_64_eq]
  rw [nat_mod_eq_of_lt lo.isLt, nat_mod_eq_of_lt lo.isLt]

private theorem hi64Of128_pack2x64 (lo hi : BitVec 64) :
    hi64Of128 (pack2x64 lo hi) = hi := by
  apply bv_eq_of_toNat
  unfold hi64Of128 pack2x64
  rw [bv_toNat_ofNat_of_lt (pack2x64_bound lo hi)]
  have hpos : 0 < 18446744073709551616 := by decide
  rw [nat_add_mul_div_right lo.toNat hi.toNat hpos]
  have hzero : Nat.div lo.toNat 18446744073709551616 = 0 := nat_div_eq_of_lt lo.isLt
  rw [hzero, Nat.zero_add]
  rw [bv_toNat_ofNat, nat_mod_eq_of_lt hi.isLt]

private theorem pack2x64_trunc_hi (v : BitVec 128) :
    pack2x64 (trunc128To64 v) (hi64Of128 v) = v := by
  apply bv_eq_of_toNat
  unfold pack2x64 trunc128To64 hi64Of128
  have hpos : 0 < 18446744073709551616 := by decide
  have hmodLt : Nat.mod v.toNat 18446744073709551616 < Nat.pow 2 64 :=
    nat_mod_lt v.toNat hpos
  have hdivLt : Nat.div v.toNat 18446744073709551616 < Nat.pow 2 64 := by
    rw [nat_div_lt_iff_lt_mul hpos]
    rw [pow2_64_eq, ← pow2_128_eq]
    exact v.isLt
  rw [bv_toNat_ofNat_of_lt hmodLt, bv_toNat_ofNat_of_lt hdivLt]
  have heq : Nat.mod v.toNat 18446744073709551616 +
      Nat.div v.toNat 18446744073709551616 * 18446744073709551616 = v.toNat := by
    rw [Nat.mul_comm]
    exact nat_mod_add_div v.toNat 18446744073709551616
  rw [heq]
  exact nat_mod_eq_of_lt v.isLt

/-! ### Equality Reflection Helpers -/

private theorem boolEq_refl : ∀ b : Bool, boolEq b b = true
  | true => rfl
  | false => rfl

private theorem boolEq_eq {a b : Bool} (h : boolEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem targetEq_eq {a b : AbiTarget} (h : targetEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem convEq_eq {a b : CallConv} (h : convEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem sretLocEq_eq {a b : SretLoc} (h : sretLocEq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

private theorem abiTyEq_refl : ∀ t : AbiTy, abiTyEq t t = true
  | .zst b => boolEq_refl b
  | .intScalar n => nat_beq_refl n
  | .float32 => rfl
  | .float64 => rfl
  | .nicheNonNull => rfl
  | .hfa2F64 => rfl
  | .hfa4F32 => rfl
  | .simd4F32 => rfl
  | .bigStruct n => nat_beq_refl n

private theorem abiTyEq_eq {a b : AbiTy} (h : abiTyEq a b = true) : a = b := by
  cases a <;> cases b <;> simp [abiTyEq] at h <;> repeat rfl
  · rw [boolEq_eq h]
  · rw [h]
  · rw [h]

private theorem argModeEq_eq {a b : ArgPassMode} (h : argModeEq a b = true) : a = b := by
  cases a <;> cases b <;> simp [argModeEq] at h <;> repeat rfl
  · rw [h.1, h.2]
  · rw [h]
  · rw [h]
  · rw [h]
  · rw [h]
  · rw [h]
  · rw [h.1, abiTyEq_eq h.2]
  · rw [h.1.1, boolEq_eq h.1.2, abiTyEq_eq h.2]
  · rw [h.1, abiTyEq_eq h.2]

private theorem argModeListEq_eq : ∀ {xs ys : List ArgPassMode}, argModeListEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp [argModeListEq] at h
    rw [argModeEq_eq h.1, argModeListEq_eq h.2]

private theorem retModeEq_eq {a b : RetPassMode} (h : retModeEq a b = true) : a = b := by
  cases a <;> cases b <;> simp [retModeEq] at h <;> repeat rfl
  · rw [h]
  · rw [sretLocEq_eq h.1, abiTyEq_eq h.2]

private theorem symbolRuleEq_refl : ∀ r : LinkerSymbolRule, symbolRuleEq r r = true
  | .undecorated => rfl
  | .vectorcallAtAt n => nat_beq_refl n

private theorem symbolRuleEq_eq {a b : LinkerSymbolRule} (h : symbolRuleEq a b = true) : a = b := by
  cases a <;> cases b <;> simp [symbolRuleEq] at h <;> repeat rfl
  · rw [h]

private theorem symbolRuleEq_iff {a b : LinkerSymbolRule} :
    symbolRuleEq a b = true ↔ a = b :=
  ⟨symbolRuleEq_eq, fun h => by rw [h]; exact symbolRuleEq_refl b⟩

private theorem fullAbiCompatible_eq {a b : ComputedFnAbi}
    (h : fullAbiCompatible a b = true) : a = b := by
  cases a; cases b
  simp [fullAbiCompatible, irOnlyCompatible] at h
  have h1 := targetEq_eq h.1.1.1.1.1
  have h2 := argModeListEq_eq h.1.1.1.1.2
  have h3 := retModeEq_eq h.1.1.1.2
  have h4 := sretLocEq_eq h.1.1.2
  have h5 := convEq_eq h.1.2
  have h6 := symbolRuleEq_eq h.2
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6
  rfl

/-! ### Value Well-Typedness & Word Serialization Roundtrip -/

private theorem checkValHasTy_of_valHasTy {v : AbiVal} {ty : AbiTy}
    (h : valHasTy v ty) : checkValHasTy v ty = true := by
  cases v <;> cases ty <;> repeat exact False.elim h
  · rfl
  · have ⟨hb, hsz, hlt⟩ := h
    subst hb
    simp only [checkValHasTy, nat_beq_refl]
    cases hsz with
    | inl h1 =>
      subst h1
      have hlt' : Nat.blt _ (Nat.pow 2 (1 * 8)) = true := nat_blt_of_lt (hlt (by decide))
      simp [hlt']
    | inr hrest =>
      cases hrest with
      | inl h2 =>
        subst h2
        have hlt' : Nat.blt _ (Nat.pow 2 (2 * 8)) = true := nat_blt_of_lt (hlt (by decide))
        simp [hlt']
      | inr hrest2 =>
        cases hrest2 with
        | inl h4 =>
          subst h4
          have hlt' : Nat.blt _ (Nat.pow 2 (4 * 8)) = true := nat_blt_of_lt (hlt (by decide))
          simp [hlt']
        | inr h8 =>
          subst h8
          rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · have ⟨hlen, hgt⟩ := h
    subst hlen
    simp [checkValHasTy, nat_blt_of_lt hgt]

private theorem decodeValWords_encodeValWords {v : AbiVal} {ty : AbiTy}
    (h : valHasTy v ty) : decodeValWords ty (encodeValWords v) = .ok v := by
  cases v <;> cases ty <;> repeat exact False.elim h
  · rfl
  · have ⟨hb, hsz, hlt⟩ := h
    subst hb
    simp only [encodeValWords, decodeValWords]
    cases hsz with
    | inl h1 =>
      subst h1
      have hlt' := nat_blt_of_lt (hlt (by decide))
      simp [hlt']
    | inr hrest =>
      cases hrest with
      | inl h2 =>
        subst h2
        have hlt' := nat_blt_of_lt (hlt (by decide))
        simp [hlt']
      | inr hrest2 =>
        cases hrest2 with
        | inl h4 =>
          subst h4
          have hlt' := nat_blt_of_lt (hlt (by decide))
          simp [hlt']
        | inr h8 =>
          subst h8
          rfl
  · simp only [encodeValWords, decodeValWords, trunc64To32_zext32To64]
  · rfl
  · rfl
  · rfl
  · simp only [encodeValWords, decodeValWords, unpackLo32_pack2x32, unpackHi32_pack2x32]
  · simp only [encodeValWords, decodeValWords, pack2x64_trunc_hi]
  · have ⟨hlen, hgt⟩ := h
    subst hlen
    simp [encodeValWords, decodeValWords, nat_blt_of_lt hgt]

/-! ### `assocLookup` Frame Lemmas -/

private theorem assocLookup_same {α : Type} (k : Nat) (v : α) (rest : List (Nat × α)) :
    assocLookup k ((k, v) :: rest) = some v := by
  simp [assocLookup]

private theorem assocLookup_ne {α : Type} {k k' : Nat} (hne : k ≠ k')
    (v : α) (rest : List (Nat × α)) :
    assocLookup k ((k', v) :: rest) = assocLookup k rest := by
  simp [assocLookup, nat_beq_false_of_ne hne]

/-! ### `classifyOneArg` Cursor Monotonicity & Upper-Bound Preservation -/

/-- Exact invariant of a single classified argument mode relative to its
pre/post cursors `(gIdx, xIdx, stkIdx) -> (g', x', s')`. -/
private def ModeBounded (gIdx xIdx stkIdx g' x' s' : Nat) : ArgPassMode → AbiTy → Prop
  | .ignore, .zst _ => gIdx ≤ g' ∧ xIdx ≤ x' ∧ stkIdx ≤ s'
  | .directGpr r b, .intScalar b' =>
      b = b' ∧ r = gIdx ∧ gIdx < g' ∧ r < 8 ∧ xIdx ≤ x' ∧ stkIdx ≤ s'
  | .directGpr r b, .nicheNonNull =>
      b = 8 ∧ r = gIdx ∧ gIdx < g' ∧ r < 8 ∧ xIdx ≤ x' ∧ stkIdx ≤ s'
  | .directF32 r, .float32 =>
      r = xIdx ∧ gIdx ≤ g' ∧ xIdx < x' ∧ stkIdx ≤ s'
  | .directF64 r, .float64 =>
      r = xIdx ∧ gIdx ≤ g' ∧ xIdx < x' ∧ stkIdx ≤ s'
  | .directPairF64 r0, .hfa2F64 =>
      r0 = xIdx ∧ gIdx ≤ g' ∧ xIdx + 1 < x' ∧ stkIdx ≤ s'
  | .directPairF64 r0, .hfa4F32 =>
      r0 = xIdx ∧ gIdx ≤ g' ∧ xIdx + 1 < x' ∧ stkIdx ≤ s'
  | .directQuadF32 r0, .hfa4F32 =>
      r0 = xIdx ∧ gIdx ≤ g' ∧ xIdx + 3 < x' ∧ stkIdx ≤ s'
  | .directVec128 r, .simd4F32 =>
      r = xIdx ∧ gIdx ≤ g' ∧ xIdx < x' ∧ stkIdx ≤ s'
  | .indirectGpr r expTy, ty =>
      expTy = ty ∧ r = gIdx ∧ gIdx < g' ∧ r < 8 ∧ xIdx ≤ x' ∧ stkIdx ≤ s'
  | .indirectStack s _ expTy, ty =>
      expTy = ty ∧ s = stkIdx ∧ gIdx ≤ g' ∧ xIdx ≤ x' ∧ stkIdx < s'
  | .directStack s (.intScalar b), .intScalar b' =>
      b = b' ∧ s = stkIdx ∧ gIdx ≤ g' ∧ xIdx ≤ x' ∧ stkIdx < s'
  | .directStack s .nicheNonNull, .nicheNonNull =>
      s = stkIdx ∧ gIdx ≤ g' ∧ xIdx ≤ x' ∧ stkIdx < s'
  | .directStack s .float32, .float32 =>
      s = stkIdx ∧ gIdx ≤ g' ∧ xIdx ≤ x' ∧ stkIdx < s'
  | .directStack s .float64, .float64 =>
      s = stkIdx ∧ gIdx ≤ g' ∧ xIdx ≤ x' ∧ stkIdx < s'
  | .directStack s .hfa2F64, .hfa2F64 =>
      s = stkIdx ∧ gIdx ≤ g' ∧ xIdx ≤ x' ∧ stkIdx + 1 < s'
  | .directStack s .hfa4F32, .hfa4F32 =>
      s = stkIdx ∧ gIdx ≤ g' ∧ xIdx ≤ x' ∧ stkIdx + 1 < s'
  | .directStack s .simd4F32, .simd4F32 =>
      s = stkIdx ∧ gIdx ≤ g' ∧ xIdx ≤ x' ∧ stkIdx + 1 < s'
  | _, _ => False

private theorem maxGprArgs_le_8 : ∀ t : AbiTarget, maxGprArgs t ≤ 8
  | .sysv64 => by decide
  | .win64Msvc => by decide
  | .aapcs64 => by decide
  | .i686SysV => by decide

private theorem le_if_add1 (n : Nat) (b : Bool) : n ≤ (if b then n + 1 else n) := by
  cases b
  · exact Nat.le_refl n
  · exact Nat.le_succ_of_le (Nat.le_refl n)

private theorem le_if_add2 (n : Nat) (b : Bool) : n ≤ (if b then n + 2 else n) := by
  cases b
  · exact Nat.le_refl n
  · exact Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl n))

private theorem ite_bool_true {α : Type} (a b : α) : (if (true = true) then a else b) = a := rfl
private theorem ite_bool_false {α : Type} (a b : α) : (if (false = true) then a else b) = b := rfl

private theorem classifyOneArg_bounded (t : AbiTarget) (rel : RustcRelease)
    (cc : CallConv) (ty : AbiTy) (gIdx xIdx stkIdx : Nat) :
    let res := classifyOneArg t rel cc ty gIdx xIdx stkIdx
    ModeBounded gIdx xIdx stkIdx res.2.1 res.2.2.1 res.2.2.2 res.1 ty := by
  have hmax8 := maxGprArgs_le_8 t
  cases ty with
  | zst reprC =>
    dsimp only [classifyOneArg]
    cases win64ZstIndirect t rel cc reprC
    · exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
    · cases hblt : Nat.blt gIdx (maxGprArgs t)
      · exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
      · exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
               le_if_add1 _ _, Nat.le_refl _⟩
  | intScalar b =>
    dsimp only [classifyOneArg]
    cases hblt : Nat.blt gIdx (maxGprArgs t)
    · exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
    · exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
             le_if_add1 _ _, Nat.le_refl _⟩
  | nicheNonNull =>
    dsimp only [classifyOneArg]
    cases hblt : Nat.blt gIdx (maxGprArgs t)
    · exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
    · exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
             le_if_add1 _ _, Nat.le_refl _⟩
  | float32 =>
    dsimp only [classifyOneArg]
    cases Nat.blt xIdx (maxFloatXmmArgs t cc)
    · exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
    · exact ⟨rfl, le_if_add1 _ _, Nat.lt_succ_self _, Nat.le_refl _⟩
  | float64 =>
    dsimp only [classifyOneArg]
    cases Nat.blt xIdx (maxFloatXmmArgs t cc)
    · exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
    · exact ⟨rfl, le_if_add1 _ _, Nat.lt_succ_self _, Nat.le_refl _⟩
  | hfa2F64 =>
    cases t with
    | sysv64 =>
      cases cc with
      | rust | c =>
        dsimp only [classifyOneArg]
        cases Nat.blt (xIdx + 1) (maxFloatXmmArgs .sysv64 _)
        · rw [ite_bool_false]; dsimp only [ModeBounded]
          exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
        · rw [ite_bool_true]; dsimp only [ModeBounded]
          exact ⟨rfl, Nat.le_refl _, Nat.lt_succ_self _, Nat.le_refl _⟩
      | vectorcall =>
        dsimp only [classifyOneArg]
        cases hblt : Nat.blt gIdx (maxGprArgs .sysv64)
        · rw [ite_bool_false]; dsimp only [ModeBounded]
          exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
        · rw [ite_bool_true]; dsimp only [ModeBounded]
          exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
                 le_if_add1 _ _, Nat.le_refl _⟩
    | aapcs64 =>
      dsimp only [classifyOneArg]
      cases Nat.blt (xIdx + 1) (maxFloatXmmArgs .aapcs64 cc)
      · rw [ite_bool_false]; dsimp only [ModeBounded]
        exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
      · rw [ite_bool_true]; dsimp only [ModeBounded]
        exact ⟨rfl, Nat.le_refl _, Nat.lt_succ_self _, Nat.le_refl _⟩
    | win64Msvc =>
      cases cc with
      | rust =>
        dsimp only [classifyOneArg]
        cases Nat.blt (xIdx + 1) (maxFloatXmmArgs .win64Msvc .rust)
        · rw [ite_bool_false]; dsimp only [ModeBounded]
          exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
        · rw [ite_bool_true]; dsimp only [ModeBounded]
          exact ⟨rfl, le_if_add2 _ _, Nat.lt_succ_self _, Nat.le_refl _⟩
      | c | vectorcall =>
        dsimp only [classifyOneArg]
        cases hblt : Nat.blt gIdx (maxGprArgs .win64Msvc)
        · rw [ite_bool_false]; dsimp only [ModeBounded]
          exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
        · rw [ite_bool_true]; dsimp only [ModeBounded]
          exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
                 le_if_add1 _ _, Nat.le_refl _⟩
    | i686SysV =>
      dsimp only [classifyOneArg, ModeBounded]
      exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
  | hfa4F32 =>
    cases t with
    | aapcs64 =>
      cases cc with
      | c =>
        dsimp only [classifyOneArg]
        cases Nat.blt (xIdx + 3) (maxFloatXmmArgs .aapcs64 .c)
        · rw [ite_bool_false]; dsimp only [ModeBounded]
          exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
        · rw [ite_bool_true]; dsimp only [ModeBounded]
          exact ⟨rfl, Nat.le_refl _, Nat.lt_succ_self _, Nat.le_refl _⟩
      | rust | vectorcall =>
        dsimp only [classifyOneArg]
        cases hblt : Nat.blt gIdx (maxGprArgs .aapcs64)
        · rw [ite_bool_false]; dsimp only [ModeBounded]
          exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
        · rw [ite_bool_true]; dsimp only [ModeBounded]
          exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
                 le_if_add1 _ _, Nat.le_refl _⟩
    | sysv64 =>
      cases cc with
      | c =>
        dsimp only [classifyOneArg]
        cases Nat.blt (xIdx + 1) (maxFloatXmmArgs .sysv64 .c)
        · rw [ite_bool_false]; dsimp only [ModeBounded]
          exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
        · rw [ite_bool_true]; dsimp only [ModeBounded]
          exact ⟨rfl, Nat.le_refl _, Nat.lt_succ_self _, Nat.le_refl _⟩
      | rust | vectorcall =>
        dsimp only [classifyOneArg]
        cases hblt : Nat.blt gIdx (maxGprArgs .sysv64)
        · rw [ite_bool_false]; dsimp only [ModeBounded]
          exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
        · rw [ite_bool_true]; dsimp only [ModeBounded]
          exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
                 le_if_add1 _ _, Nat.le_refl _⟩
    | i686SysV =>
      cases cc with
      | c | vectorcall =>
        dsimp only [classifyOneArg, ModeBounded]
        exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
      | rust =>
        dsimp only [classifyOneArg]
        cases hblt : Nat.blt gIdx (maxGprArgs .i686SysV)
        · rw [ite_bool_false]; dsimp only [ModeBounded]
          exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
        · rw [ite_bool_true]; dsimp only [ModeBounded]
          exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
                 le_if_add1 _ _, Nat.le_refl _⟩
    | win64Msvc =>
      dsimp only [classifyOneArg]
      cases hblt : Nat.blt gIdx (maxGprArgs .win64Msvc)
      · rw [ite_bool_false]; dsimp only [ModeBounded]
        exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
      · rw [ite_bool_true]; dsimp only [ModeBounded]
        exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
               le_if_add1 _ _, Nat.le_refl _⟩
  | simd4F32 =>
    dsimp only [classifyOneArg]
    cases simdDirectEnabled t rel cc
    · cases hblt : Nat.blt gIdx (maxGprArgs t)
      · exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
      · exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
               le_if_add1 _ _, Nat.le_refl _⟩
    · cases Nat.blt xIdx (maxVecXmmArgs t cc)
      · exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
      · exact ⟨rfl, le_if_add1 _ _, Nat.lt_succ_self _, Nat.le_refl _⟩
  | bigStruct n =>
    dsimp only [classifyOneArg]
    cases hblt : Nat.blt gIdx (maxGprArgs t)
    · exact ⟨rfl, rfl, Nat.le_refl _, Nat.le_refl _, Nat.lt_succ_self _⟩
    · exact ⟨rfl, rfl, Nat.lt_succ_self _, Nat.lt_of_lt_of_le (nat_lt_of_blt hblt) hmax8,
             le_if_add1 _ _, Nat.le_refl _⟩

/-! ### Single-Argument Marshal / Unmarshal / `PhysShim` Exactness & Frame Preservation -/

/-- Frame preservation predicate: `f2` agrees with `f1` on all GPRs `< g0` and
on `gpr 8`, all XMMs `< x0`, all stack slots `< s0`, all `mem` keys `< tok0`,
and both x87 slots. -/
private def FramePreserves (g0 x0 s0 tok0 : Nat) (f1 f2 : PhysFrame) : Prop :=
  (∀ r, r < g0 → assocLookup r f2.gprs = assocLookup r f1.gprs) ∧
  assocLookup 8 f2.gprs = assocLookup 8 f1.gprs ∧
  (∀ x, x < x0 → assocLookup x f2.xmms = assocLookup x f1.xmms) ∧
  (∀ s, s < s0 → assocLookup s f2.stack = assocLookup s f1.stack) ∧
  (∀ k, k < tok0 → assocLookup k f2.mem = assocLookup k f1.mem) ∧
  f2.x87F32 = f1.x87F32 ∧
  f2.x87F64 = f1.x87F64

private theorem framePreserves_refl (g0 x0 s0 tok0 : Nat) (f : PhysFrame) :
    FramePreserves g0 x0 s0 tok0 f f :=
  ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

private theorem framePreserves_trans {g0 x0 s0 tok0 g1 x1 s1 tok1 : Nat}
    {f1 f2 f3 : PhysFrame}
    (hg : g0 ≤ g1) (hx : x0 ≤ x1) (hs : s0 ≤ s1) (ht : tok0 ≤ tok1)
    (h12 : FramePreserves g0 x0 s0 tok0 f1 f2)
    (h23 : FramePreserves g1 x1 s1 tok1 f2 f3) :
    FramePreserves g0 x0 s0 tok0 f1 f3 :=
  ⟨fun r hr => Eq.trans (h23.1 r (Nat.lt_of_lt_of_le hr hg)) (h12.1 r hr),
   Eq.trans h23.2.1 h12.2.1,
   fun x hx0 => Eq.trans (h23.2.2.1 x (Nat.lt_of_lt_of_le hx0 hx)) (h12.2.2.1 x hx0),
   fun s hs0 => Eq.trans (h23.2.2.2.1 s (Nat.lt_of_lt_of_le hs0 hs)) (h12.2.2.2.1 s hs0),
   fun k hk0 => Eq.trans (h23.2.2.2.2.1 k (Nat.lt_of_lt_of_le hk0 ht)) (h12.2.2.2.2.1 k hk0),
   Eq.trans h23.2.2.2.2.2.1 h12.2.2.2.2.2.1,
   Eq.trans h23.2.2.2.2.2.2 h12.2.2.2.2.2.2⟩

private theorem marshalOneArg_step
    {g0 x0 s0 g' x' s' : Nat} {m : ArgPassMode} {ty : AbiTy} {v : AbiVal}
    {f : PhysFrame}
    (hBound : ModeBounded g0 x0 s0 g' x' s' m ty)
    (hVal : valHasTy v ty)
    (hTok : f.nextTok < Nat.pow 2 64) :
    ∃ f',
      marshalOneArg f m v = .ok f' ∧
      execPhysWrite f (compileArgWriteOp m ty) (encodeValWords v) = .ok f' ∧
      f.nextTok ≤ f'.nextTok ∧
      f'.nextTok ≤ f.nextTok + 1 ∧
      FramePreserves g0 x0 s0 f.nextTok f f' ∧
      (∀ fFinal, FramePreserves g' x' s' f'.nextTok f' fFinal →
        unmarshalOneArg fFinal m ty = .ok v ∧
        execPhysRead fFinal (compileArgReadOp m ty) = .ok (encodeValWords v)) := by
  have hChk := checkValHasTy_of_valHasTy hVal
  have hDec := decodeValWords_encodeValWords hVal
  cases m with
  | ignore =>
    cases ty <;> repeat exact False.elim hBound
    cases v <;> repeat exact False.elim hVal
    refine ⟨f, rfl, rfl, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _),
      framePreserves_refl _ _ _ _ _, fun _ _ => ⟨rfl, rfl⟩⟩
  | directGpr r b =>
    cases ty <;> repeat exact False.elim hBound
    · -- intScalar
      have ⟨hb, hr, hglt, hr8, hxl, hsl⟩ := hBound
      subst hb; subst r
      cases v <;> repeat exact False.elim hVal
      have ⟨hb2, hsz, hlt⟩ := hVal
      subst hb2
      refine ⟨putGpr f g0 _, ?_, rfl, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · simp [marshalOneArg, hChk]
      · exact ⟨fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
               assocLookup_ne (Nat.ne_of_gt hr8) _ _,
               fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
      · intro fFinal hP
        have hg := hP.1 g0 hglt
        rw [putGpr, assocLookup_same] at hg
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hg, hChk]
    · -- nicheNonNull
      have ⟨hb8, hr, hglt, hr8, hxl, hsl⟩ := hBound
      subst hb8; subst r
      cases v <;> repeat exact False.elim hVal
      refine ⟨putGpr f g0 _, rfl, rfl, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · exact ⟨fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
               assocLookup_ne (Nat.ne_of_gt hr8) _ _,
               fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
      · intro fFinal hP
        have hg := hP.1 g0 hglt
        rw [putGpr, assocLookup_same] at hg
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hg]
  | directF32 r =>
    cases ty <;> repeat exact False.elim hBound
    have ⟨hr, hgl, hxlt, hsl⟩ := hBound
    subst r
    cases v <;> repeat exact False.elim hVal
    refine ⟨putXmm f x0 (zext32To128 _), rfl, ?_, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
    · simp [execPhysWrite, compileArgWriteOp, encodeValWords, trunc64To32_zext32To64]
    · exact ⟨fun _ _ => rfl, rfl,
             fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
             fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    · intro fFinal hP
      have hx := hP.2.2.1 x0 hxlt
      rw [putXmm, assocLookup_same] at hx
      simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hx, trunc128To32_zext32To128]
  | directF64 r =>
    cases ty <;> repeat exact False.elim hBound
    have ⟨hr, hgl, hxlt, hsl⟩ := hBound
    subst r
    cases v <;> repeat exact False.elim hVal
    refine ⟨putXmm f x0 (zext64To128 _), rfl, rfl, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
    · exact ⟨fun _ _ => rfl, rfl,
             fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
             fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    · intro fFinal hP
      have hx := hP.2.2.1 x0 hxlt
      rw [putXmm, assocLookup_same] at hx
      simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hx, trunc128To64_zext64To128]
  | directPairF64 r0 =>
    cases ty <;> repeat exact False.elim hBound
    · -- hfa2F64
      have ⟨hr, hgl, hxlt, hsl⟩ := hBound
      subst r0
      cases v <;> repeat exact False.elim hVal
      refine ⟨putXmm (putXmm f x0 (zext64To128 _)) (x0 + 1) (zext64To128 _), rfl, rfl,
        Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · refine ⟨fun _ _ => rfl, rfl, fun k hk => ?_, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
        rw [putXmm, putXmm]
        rw [assocLookup_ne (Nat.ne_of_lt (Nat.lt_trans hk (Nat.lt_succ_self x0)))]
        rw [assocLookup_ne (Nat.ne_of_lt hk)]
      · intro fFinal hP
        have hx0 := hP.2.2.1 x0 (Nat.lt_trans (Nat.lt_succ_self x0) hxlt)
        have hx1 := hP.2.2.1 (x0 + 1) hxlt
        rw [putXmm, putXmm, assocLookup_ne (Nat.ne_of_lt (Nat.lt_succ_self x0)), assocLookup_same] at hx0
        rw [putXmm, assocLookup_same] at hx1
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hx0, hx1, trunc128To64_zext64To128]
    · -- hfa4F32
      have ⟨hr, hgl, hxlt, hsl⟩ := hBound
      subst r0
      cases v <;> repeat exact False.elim hVal
      refine ⟨putXmm (putXmm f x0 (zext64To128 (pack2x32 _ _))) (x0 + 1) (zext64To128 (pack2x32 _ _)),
        rfl, rfl, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · refine ⟨fun _ _ => rfl, rfl, fun k hk => ?_, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
        rw [putXmm, putXmm]
        rw [assocLookup_ne (Nat.ne_of_lt (Nat.lt_trans hk (Nat.lt_succ_self x0)))]
        rw [assocLookup_ne (Nat.ne_of_lt hk)]
      · intro fFinal hP
        have hx0 := hP.2.2.1 x0 (Nat.lt_trans (Nat.lt_succ_self x0) hxlt)
        have hx1 := hP.2.2.1 (x0 + 1) hxlt
        rw [putXmm, putXmm, assocLookup_ne (Nat.ne_of_lt (Nat.lt_succ_self x0)), assocLookup_same] at hx0
        rw [putXmm, assocLookup_same] at hx1
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hx0, hx1,
              trunc128To64_zext64To128, unpackLo32_pack2x32, unpackHi32_pack2x32]
  | directQuadF32 r0 =>
    cases ty <;> repeat exact False.elim hBound
    have ⟨hr, hgl, hxlt, hsl⟩ := hBound
    subst r0
    cases v with
    | hfa4F32 a b c d =>
      let f1 := putXmm f x0 (zext32To128 a)
      let f2 := putXmm f1 (x0 + 1) (zext32To128 b)
      let f3 := putXmm f2 (x0 + 2) (zext32To128 c)
      let f4 := putXmm f3 (x0 + 3) (zext32To128 d)
      refine ⟨f4, rfl, ?_, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · simp only [execPhysWrite, compileArgWriteOp, encodeValWords,
                   unpackLo32_pack2x32, unpackHi32_pack2x32]
        rfl
      · refine ⟨fun _ _ => rfl, rfl, fun k hk => ?_, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
        have h0 : k ≠ x0 := Nat.ne_of_lt hk
        have h1 : k ≠ x0 + 1 := Nat.ne_of_lt (Nat.lt_trans hk (Nat.lt_succ_self _))
        have h2 : k ≠ x0 + 2 := Nat.ne_of_lt (Nat.lt_trans hk (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)))
        have h3 : k ≠ x0 + 3 := Nat.ne_of_lt (Nat.lt_trans hk (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))))
        change assocLookup k ((x0 + 3, _) :: (x0 + 2, _) :: (x0 + 1, _) :: (x0, _) :: f.xmms) = assocLookup k f.xmms
        rw [assocLookup_ne h3, assocLookup_ne h2, assocLookup_ne h1, assocLookup_ne h0]
      · intro fFinal hP
        have hlt0 : x0 < x' := Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self x0) (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))) hxlt
        have hlt1 : x0 + 1 < x' := Nat.lt_trans (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)) hxlt
        have hlt2 : x0 + 2 < x' := Nat.lt_trans (Nat.lt_succ_self _) hxlt
        have hx0 := hP.2.2.1 x0 hlt0
        have hx1 := hP.2.2.1 (x0 + 1) hlt1
        have hx2 := hP.2.2.1 (x0 + 2) hlt2
        have hx3 := hP.2.2.1 (x0 + 3) hxlt
        have n03 : x0 ≠ x0 + 3 := Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _)))
        have n02 : x0 ≠ x0 + 2 := Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))
        have n01 : x0 ≠ x0 + 1 := Nat.ne_of_lt (Nat.lt_succ_self _)
        have n13 : x0 + 1 ≠ x0 + 3 := Nat.ne_of_lt (Nat.lt_trans (Nat.lt_succ_self _) (Nat.lt_succ_self _))
        have n12 : x0 + 1 ≠ x0 + 2 := Nat.ne_of_lt (Nat.lt_succ_self _)
        have n23 : x0 + 2 ≠ x0 + 3 := Nat.ne_of_lt (Nat.lt_succ_self _)
        have ex0 : assocLookup x0 f4.xmms = some (zext32To128 a) := by
          change assocLookup x0 ((x0 + 3, _) :: (x0 + 2, _) :: (x0 + 1, _) :: (x0, _) :: f.xmms) = _
          rw [assocLookup_ne n03, assocLookup_ne n02, assocLookup_ne n01, assocLookup_same]
        have ex1 : assocLookup (x0 + 1) f4.xmms = some (zext32To128 b) := by
          change assocLookup (x0 + 1) ((x0 + 3, _) :: (x0 + 2, _) :: (x0 + 1, _) :: (x0, _) :: f.xmms) = _
          rw [assocLookup_ne n13, assocLookup_ne n12, assocLookup_same]
        have ex2 : assocLookup (x0 + 2) f4.xmms = some (zext32To128 c) := by
          change assocLookup (x0 + 2) ((x0 + 3, _) :: (x0 + 2, _) :: (x0 + 1, _) :: (x0, _) :: f.xmms) = _
          rw [assocLookup_ne n23, assocLookup_same]
        have ex3 : assocLookup (x0 + 3) f4.xmms = some (zext32To128 d) := by
          change assocLookup (x0 + 3) ((x0 + 3, _) :: (x0 + 2, _) :: (x0 + 1, _) :: (x0, _) :: f.xmms) = _
          rw [assocLookup_same]
        rw [ex0] at hx0; rw [ex1] at hx1; rw [ex2] at hx2; rw [ex3] at hx3
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hx0, hx1, hx2, hx3,
              trunc128To32_zext32To128]
    | zst | intScalar _ _ | float32 _ | float64 _ | nicheNonNull _ | hfa2F64 _ _ | simd4F32 _ | bigStruct _ =>
      exact False.elim hVal
  | directVec128 r =>
    cases ty <;> repeat exact False.elim hBound
    have ⟨hr, hgl, hxlt, hsl⟩ := hBound
    subst r
    cases v <;> repeat exact False.elim hVal
    refine ⟨putXmm f x0 _, rfl, ?_, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
    · simp [execPhysWrite, compileArgWriteOp, encodeValWords, pack2x64_trunc_hi]
    · exact ⟨fun _ _ => rfl, rfl,
             fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
             fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩
    · intro fFinal hP
      have hx := hP.2.2.1 x0 hxlt
      rw [putXmm, assocLookup_same] at hx
      simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hx]
  | indirectGpr r expTy =>
    have ⟨hty, hr, hglt, hr8, hxl, hsl⟩ := hBound
    subst hty; subst r
    let alloc := allocMemWords f (encodeValWords v)
    let f' := putGpr alloc.2 g0 (BitVec.ofNat 64 alloc.1)
    refine ⟨f', ?_, rfl, Nat.le_succ_of_le (Nat.le_refl _), Nat.le_refl _, ?_, ?_⟩
    · simp [marshalOneArg, hChk, alloc, f']
    · exact ⟨fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
             assocLookup_ne (Nat.ne_of_gt hr8) _ _,
             fun _ _ => rfl, fun _ _ => rfl,
             fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _, rfl, rfl⟩
    · intro fFinal hP
      have hg := hP.1 g0 hglt
      have hm := hP.2.2.2.2.1 f.nextTok (Nat.lt_succ_self f.nextTok)
      rw [show assocLookup g0 f'.gprs = some (BitVec.ofNat 64 f.nextTok) from assocLookup_same _ _ _] at hg
      rw [show assocLookup f.nextTok f'.mem = some (encodeValWords v) from assocLookup_same _ _ _] at hm
      have htokEq : (BitVec.ofNat 64 f.nextTok).toNat = f.nextTok := bv_toNat_ofNat_of_lt hTok
      simp [unmarshalOneArg, execPhysRead, compileArgReadOp, abiTyEq_refl, hg, htokEq, hm, hDec]
  | indirectStack s bv expTy =>
    have ⟨hty, hs, hgl, hxl, hslt⟩ := hBound
    subst hty; subst s
    let alloc := allocMemWords f (encodeValWords v)
    let f' := putStack alloc.2 s0 (BitVec.ofNat 64 alloc.1)
    refine ⟨f', ?_, rfl, Nat.le_succ_of_le (Nat.le_refl _), Nat.le_refl _, ?_, ?_⟩
    · simp [marshalOneArg, hChk, alloc, f']
    · exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl,
             fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
             fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _, rfl, rfl⟩
    · intro fFinal hP
      have hst := hP.2.2.2.1 s0 hslt
      have hm := hP.2.2.2.2.1 f.nextTok (Nat.lt_succ_self f.nextTok)
      rw [show assocLookup s0 f'.stack = some (BitVec.ofNat 64 f.nextTok) from assocLookup_same _ _ _] at hst
      rw [show assocLookup f.nextTok f'.mem = some (encodeValWords v) from assocLookup_same _ _ _] at hm
      have htokEq : (BitVec.ofNat 64 f.nextTok).toNat = f.nextTok := bv_toNat_ofNat_of_lt hTok
      simp [unmarshalOneArg, execPhysRead, compileArgReadOp, abiTyEq_refl, hst, htokEq, hm, hDec]
  | directStack s expTy =>
    cases expTy <;> cases ty <;> repeat exact False.elim hBound
    · -- intScalar
      have ⟨hb, hs, hgl, hxl, hslt⟩ := hBound
      subst hb; subst s
      cases v <;> repeat exact False.elim hVal
      have ⟨hb2, hsz, hlt⟩ := hVal
      subst hb2
      refine ⟨putStack f s0 _, ?_, rfl, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · simp [marshalOneArg, hChk]
      · exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl,
               fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
               fun _ _ => rfl, rfl, rfl⟩
      · intro fFinal hP
        have hst := hP.2.2.2.1 s0 hslt
        rw [putStack, assocLookup_same] at hst
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hst, hChk]
    · -- float32
      have ⟨hs, hgl, hxl, hslt⟩ := hBound
      subst s
      cases v <;> repeat exact False.elim hVal
      refine ⟨putStack f s0 (zext32To64 _), rfl, rfl, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl,
               fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
               fun _ _ => rfl, rfl, rfl⟩
      · intro fFinal hP
        have hst := hP.2.2.2.1 s0 hslt
        rw [putStack, assocLookup_same] at hst
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hst, trunc64To32_zext32To64]
    · -- float64
      have ⟨hs, hgl, hxl, hslt⟩ := hBound
      subst s
      cases v <;> repeat exact False.elim hVal
      refine ⟨putStack f s0 _, rfl, rfl, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl,
               fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
               fun _ _ => rfl, rfl, rfl⟩
      · intro fFinal hP
        have hst := hP.2.2.2.1 s0 hslt
        rw [putStack, assocLookup_same] at hst
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hst]
    · -- nicheNonNull
      have ⟨hs, hgl, hxl, hslt⟩ := hBound
      subst s
      cases v <;> repeat exact False.elim hVal
      refine ⟨putStack f s0 _, rfl, rfl, Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · exact ⟨fun _ _ => rfl, rfl, fun _ _ => rfl,
               fun k hk => assocLookup_ne (Nat.ne_of_lt hk) _ _,
               fun _ _ => rfl, rfl, rfl⟩
      · intro fFinal hP
        have hst := hP.2.2.2.1 s0 hslt
        rw [putStack, assocLookup_same] at hst
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hst]
    · -- hfa2F64
      have ⟨hs, hgl, hxl, hslt⟩ := hBound
      subst s
      cases v <;> repeat exact False.elim hVal
      refine ⟨putStack (putStack f s0 _) (s0 + 1) _, rfl, rfl,
        Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · refine ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun k hk => ?_, fun _ _ => rfl, rfl, rfl⟩
        rw [putStack, putStack]
        rw [assocLookup_ne (Nat.ne_of_lt (Nat.lt_trans hk (Nat.lt_succ_self s0)))]
        rw [assocLookup_ne (Nat.ne_of_lt hk)]
      · intro fFinal hP
        have hs0 := hP.2.2.2.1 s0 (Nat.lt_trans (Nat.lt_succ_self s0) hslt)
        have hs1 := hP.2.2.2.1 (s0 + 1) hslt
        rw [putStack, putStack, assocLookup_ne (Nat.ne_of_lt (Nat.lt_succ_self s0)), assocLookup_same] at hs0
        rw [putStack, assocLookup_same] at hs1
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hs0, hs1]
    · -- hfa4F32
      have ⟨hs, hgl, hxl, hslt⟩ := hBound
      subst s
      cases v <;> repeat exact False.elim hVal
      refine ⟨putStack (putStack f s0 (pack2x32 _ _)) (s0 + 1) (pack2x32 _ _), rfl, rfl,
        Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · refine ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun k hk => ?_, fun _ _ => rfl, rfl, rfl⟩
        rw [putStack, putStack]
        rw [assocLookup_ne (Nat.ne_of_lt (Nat.lt_trans hk (Nat.lt_succ_self s0)))]
        rw [assocLookup_ne (Nat.ne_of_lt hk)]
      · intro fFinal hP
        have hs0 := hP.2.2.2.1 s0 (Nat.lt_trans (Nat.lt_succ_self s0) hslt)
        have hs1 := hP.2.2.2.1 (s0 + 1) hslt
        rw [putStack, putStack, assocLookup_ne (Nat.ne_of_lt (Nat.lt_succ_self s0)), assocLookup_same] at hs0
        rw [putStack, assocLookup_same] at hs1
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hs0, hs1,
              unpackLo32_pack2x32, unpackHi32_pack2x32]
    · -- simd4F32
      have ⟨hs, hgl, hxl, hslt⟩ := hBound
      subst s
      cases v <;> repeat exact False.elim hVal
      refine ⟨putStack (putStack f s0 (trunc128To64 _)) (s0 + 1) (hi64Of128 _), rfl, rfl,
        Nat.le_refl _, Nat.le_succ_of_le (Nat.le_refl _), ?_, ?_⟩
      · refine ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun k hk => ?_, fun _ _ => rfl, rfl, rfl⟩
        rw [putStack, putStack]
        rw [assocLookup_ne (Nat.ne_of_lt (Nat.lt_trans hk (Nat.lt_succ_self s0)))]
        rw [assocLookup_ne (Nat.ne_of_lt hk)]
      · intro fFinal hP
        have hs0 := hP.2.2.2.1 s0 (Nat.lt_trans (Nat.lt_succ_self s0) hslt)
        have hs1 := hP.2.2.2.1 (s0 + 1) hslt
        rw [putStack, putStack, assocLookup_ne (Nat.ne_of_lt (Nat.lt_succ_self s0)), assocLookup_same] at hs0
        rw [putStack, assocLookup_same] at hs1
        simp [unmarshalOneArg, execPhysRead, compileArgReadOp, encodeValWords, hs0, hs1,
              pack2x64_trunc_hi]

private theorem modeBounded_le {g0 x0 s0 g' x' s' : Nat} {m : ArgPassMode} {ty : AbiTy}
    (h : ModeBounded g0 x0 s0 g' x' s' m ty) : g0 ≤ g' ∧ x0 ≤ x' ∧ s0 ≤ s' := by
  cases m with
  | ignore =>
    cases ty <;> repeat exact False.elim h
    exact h
  | directGpr r b =>
    cases ty <;> repeat exact False.elim h
    · exact ⟨Nat.le_of_lt h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
    · exact ⟨Nat.le_of_lt h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  | directF32 r =>
    cases ty <;> repeat exact False.elim h
    exact ⟨h.2.1, Nat.le_of_lt h.2.2.1, h.2.2.2⟩
  | directF64 r =>
    cases ty <;> repeat exact False.elim h
    exact ⟨h.2.1, Nat.le_of_lt h.2.2.1, h.2.2.2⟩
  | directPairF64 r0 =>
    cases ty <;> repeat exact False.elim h
    · exact ⟨h.2.1, Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl _)) (Nat.le_of_lt h.2.2.1), h.2.2.2⟩
    · exact ⟨h.2.1, Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl _)) (Nat.le_of_lt h.2.2.1), h.2.2.2⟩
  | directQuadF32 r0 =>
    cases ty <;> repeat exact False.elim h
    exact ⟨h.2.1, Nat.le_trans (Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl _)))) (Nat.le_of_lt h.2.2.1), h.2.2.2⟩
  | directVec128 r =>
    cases ty <;> repeat exact False.elim h
    exact ⟨h.2.1, Nat.le_of_lt h.2.2.1, h.2.2.2⟩
  | indirectGpr r expTy =>
    exact ⟨Nat.le_of_lt h.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  | indirectStack s bv expTy =>
    exact ⟨h.2.2.1, h.2.2.2.1, Nat.le_of_lt h.2.2.2.2⟩
  | directStack s expTy =>
    cases expTy <;> cases ty <;> repeat exact False.elim h
    · exact ⟨h.2.2.1, h.2.2.2.1, Nat.le_of_lt h.2.2.2.2⟩
    · exact ⟨h.2.1, h.2.2.1, Nat.le_of_lt h.2.2.2⟩
    · exact ⟨h.2.1, h.2.2.1, Nat.le_of_lt h.2.2.2⟩
    · exact ⟨h.2.1, h.2.2.1, Nat.le_of_lt h.2.2.2⟩
    · exact ⟨h.2.1, h.2.2.1, Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl _)) (Nat.le_of_lt h.2.2.2)⟩
    · exact ⟨h.2.1, h.2.2.1, Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl _)) (Nat.le_of_lt h.2.2.2)⟩
    · exact ⟨h.2.1, h.2.2.1, Nat.le_trans (Nat.le_succ_of_le (Nat.le_refl _)) (Nat.le_of_lt h.2.2.2)⟩

/-- Master inductive theorem for argument marshaling, unmarshaling, and
`AbiVal`-free `PhysShim` read/write equivalence. -/
private theorem marshalArgsLoop_master
    (t : AbiTarget) (rel : RustcRelease) (cc : CallConv)
    {vals : List AbiVal} {tys : List AbiTy} (hVals : valsHaveTys vals tys) :
    ∀ (g0 x0 s0 : Nat) (f : PhysFrame),
      f.nextTok + tys.length < Nat.pow 2 64 →
      let ms := classifyArgsLoop t rel cc g0 x0 s0 tys
      ∃ fFinal,
        marshalArgsLoop f ms vals = .ok fFinal ∧
        execPhysWrites f (compileArgWrites ms tys) (vals.map encodeValWords) = .ok fFinal ∧
        f.nextTok ≤ fFinal.nextTok ∧
        FramePreserves g0 x0 s0 f.nextTok f fFinal ∧
        unmarshalArgsLoop fFinal ms tys = .ok vals ∧
        execPhysReads fFinal (compileArgReads ms tys) = .ok (vals.map encodeValWords) := by
  induction hVals with
  | nil =>
    intro g0 x0 s0 f _
    exact ⟨f, rfl, rfl, Nat.le_refl _, framePreserves_refl _ _ _ _ _, rfl, rfl⟩
  | @cons v ty vs ts hv hrest ih =>
    intro g0 x0 s0 f hTokBound
    have hStepBound := classifyOneArg_bounded t rel cc ty g0 x0 s0
    dsimp only [classifyArgsLoop]
    let stepRes := classifyOneArg t rel cc ty g0 x0 s0
    let m := stepRes.1
    let g' := stepRes.2.1
    let x' := stepRes.2.2.1
    let s' := stepRes.2.2.2
    have hTokLt : f.nextTok < Nat.pow 2 64 :=
      Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hTokBound
    have ⟨f1, hM1, hW1, hTokLe1, hTokLeSucc, hPres1, hRead1⟩ := marshalOneArg_step hStepBound hv hTokLt
    have hTokRest : f1.nextTok + ts.length < Nat.pow 2 64 := by
      have h1 : f1.nextTok + ts.length ≤ (f.nextTok + 1) + ts.length :=
        Nat.add_le_add_right hTokLeSucc ts.length
      have h2 : (f.nextTok + 1) + ts.length = f.nextTok + (ts.length + 1) := by
        rw [Nat.add_assoc, Nat.add_comm 1 ts.length]
      rw [h2] at h1
      exact Nat.lt_of_le_of_lt h1 hTokBound
    have ⟨fFinal, hMRest, hWRest, hTokLeRest, hPresRest, hURest, hRRest⟩ := ih g' x' s' f1 hTokRest
    have hMono := modeBounded_le hStepBound
    have hPresAll : FramePreserves g0 x0 s0 f.nextTok f fFinal :=
      framePreserves_trans hMono.1 hMono.2.1 hMono.2.2 hTokLe1 hPres1 hPresRest
    have ⟨hU1, hR1⟩ := hRead1 fFinal hPresRest
    refine ⟨fFinal, ?_, ?_, Nat.le_trans hTokLe1 hTokLeRest, hPresAll, ?_, ?_⟩
    · simp only [marshalArgsLoop, hM1]; exact hMRest
    · simp only [compileArgWrites, List.map, execPhysWrites, hW1]; exact hWRest
    · simp only [unmarshalArgsLoop, hU1]
      dsimp only [g', x', s', stepRes] at hURest
      rw [hURest]
    · simp only [compileArgReads, List.map, execPhysReads, hR1]
      dsimp only [g', x', s', stepRes] at hRRest
      rw [hRRest]

/-! ### Threaded `sret` + Return Marshaling / Unmarshaling / `PhysRetShim` Lemmas -/

private theorem initSretBuffer_spec (sLoc : SretLoc) :
    let f0 := initSretBuffer sLoc emptyFrame
    f0.nextTok ≤ 2 ∧
    (sLoc ≠ .none → readSretTok sLoc f0 = some 1) := by
  cases sLoc with
  | none =>
    exact ⟨by decide, fun h => False.elim (h rfl)⟩
  | gpr0 =>
    refine ⟨by decide, fun _ => ?_⟩
    rfl
  | gpr8 =>
    refine ⟨by decide, fun _ => ?_⟩
    rfl
  | stack0 =>
    refine ⟨by decide, fun _ => ?_⟩
    rfl

private theorem framePreserves_readSretTok (t : AbiTarget) (rel : RustcRelease)
    (sig : FnSig) {f0 fCall : PhysFrame}
    (hPres : FramePreserves
      (match (classifyFnAbi t rel sig).sretLoc with | .gpr0 => 1 | _ => 0)
      (match (classifyFnAbi t rel sig).sretLoc, usesWin64PositionalSlots t sig.conv with | .gpr0, true => 1 | _, _ => 0)
      (match (classifyFnAbi t rel sig).sretLoc with | .stack0 => 1 | _ => 0)
      f0.nextTok f0 fCall) :
    readSretTok (classifyFnAbi t rel sig).sretLoc fCall =
      readSretTok (classifyFnAbi t rel sig).sretLoc f0 := by
  cases hloc : (classifyFnAbi t rel sig).sretLoc with
  | none => rfl
  | gpr0 =>
    have h0 := hPres.1 0 (by rw [hloc]; exact Nat.lt_succ_self 0)
    simp [readSretTok, h0]
  | gpr8 =>
    have h8 := hPres.2.1
    simp [readSretTok, h8]
  | stack0 =>
    have h0 := hPres.2.2.2.1 0 (by rw [hloc]; exact Nat.lt_succ_self 0)
    simp [readSretTok, h0]

private theorem classifyRet_sretLoc_consistent (t : AbiTarget) (rel : RustcRelease)
    (sig : FnSig) (loc : SretLoc) (expTy : AbiTy)
    (h : (classifyFnAbi t rel sig).retMode = .indirectSret loc expTy) :
    (classifyFnAbi t rel sig).sretLoc = loc ∧ loc ≠ .none ∧ expTy = sig.ret := by
  cases sig with
  | mk conv args ret =>
    dsimp only [classifyFnAbi] at h; dsimp only [classifyFnAbi]
    have hs : (match classifyRet t rel conv ret with | .indirectSret l _ => l | _ => .none) = loc := by
      rw [h]
    have hne : targetSretLoc t ≠ .none := by cases t <;> intro hc <;> cases hc
    cases ret with
    | zst _ => simp [classifyRet] at h
    | intScalar _ => simp [classifyRet] at h
    | nicheNonNull => simp [classifyRet] at h
    | float32 => cases t <;> cases conv <;> simp [classifyRet] at h
    | float64 => cases t <;> cases conv <;> simp [classifyRet] at h
    | hfa2F64 =>
      cases t <;> cases conv <;> simp [classifyRet] at h <;> (have ⟨hl, he⟩ := h; subst hl; subst he; exact ⟨hs, hne, rfl⟩)
    | hfa4F32 =>
      cases t <;> cases conv <;> simp [classifyRet] at h <;> (have ⟨hl, he⟩ := h; subst hl; subst he; exact ⟨hs, hne, rfl⟩)
    | simd4F32 =>
      simp [classifyRet] at h
      cases hsd : simdDirectEnabled t rel conv
      · rw [hsd] at h; simp at h
        have ⟨hl, he⟩ := h; subst hl; subst he
        exact ⟨hs, hne, rfl⟩
      · rw [hsd] at h; simp at h
    | bigStruct n =>
      simp [classifyRet] at h
      have ⟨hl, he⟩ := h; subst hl; subst he
      exact ⟨hs, hne, rfl⟩

private theorem marshalRet_step
    (t : AbiTarget) (rel : RustcRelease) (sig : FnSig)
    {retVal : AbiVal} (hRet : valHasTy retVal sig.ret)
    {fCall : PhysFrame}
    (hSret : (classifyFnAbi t rel sig).sretLoc ≠ .none →
      readSretTok (classifyFnAbi t rel sig).sretLoc fCall = some 1)
    (hX87 : isX87RetMode (classifyFnAbi t rel sig).retMode = false ∨ isNonSignalingRet retVal) :
    let rm := (classifyFnAbi t rel sig).retMode
    ∃ fOut,
      marshalRet fCall rm retVal = .ok fOut ∧
      execRetWrite fCall (compileRetWriteOp rm) (encodeValWords retVal) = .ok fOut ∧
      unmarshalRet rm sig.ret fOut = .ok retVal ∧
      execRetRead fOut (compileRetReadOp rm) = .ok (encodeValWords retVal) := by
  have hChk := checkValHasTy_of_valHasTy hRet
  have hDec := decodeValWords_encodeValWords hRet
  cases sig with
  | mk conv args ret =>
    dsimp only at hRet hSret hX87; dsimp only
    cases hrm : (classifyFnAbi t rel { conv := conv, args := args, ret := ret }).retMode with
    | ignore =>
      cases ret <;> simp [classifyFnAbi, classifyRet] at hrm
      · cases retVal <;> repeat exact False.elim hRet
        exact ⟨fCall, rfl, rfl, rfl, rfl⟩
      · cases t <;> cases conv <;> simp at hrm
      · cases t <;> cases conv <;> simp at hrm
      · cases t <;> cases conv <;> simp at hrm
      · cases t <;> cases conv <;> simp at hrm
      · cases hsd : simdDirectEnabled t rel conv <;> simp [hsd] at hrm
    | directGpr0 b =>
      cases ret with
      | intScalar b' =>
        simp [classifyFnAbi, classifyRet] at hrm
        subst hrm
        cases retVal <;> repeat exact False.elim hRet
        have ⟨hb, _, _⟩ := hRet; subst hb
        refine ⟨putGpr fCall 0 _, ?_, rfl, ?_, ?_⟩
        · simp [marshalRet, hChk]
        · simp [unmarshalRet, putGpr, assocLookup_same, hChk]
        · simp [execRetRead, compileRetReadOp, encodeValWords, putGpr, assocLookup_same]
      | nicheNonNull =>
        simp [classifyFnAbi, classifyRet] at hrm
        subst hrm
        cases retVal <;> repeat exact False.elim hRet
        refine ⟨putGpr fCall 0 _, rfl, rfl, ?_, ?_⟩
        · simp [unmarshalRet, putGpr, assocLookup_same]
        · simp [execRetRead, compileRetReadOp, encodeValWords, putGpr, assocLookup_same]
      | float32 =>
        cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
        subst hrm
        cases retVal <;> repeat exact False.elim hRet
        refine ⟨putGpr fCall 0 (zext32To64 _), rfl, rfl, ?_, ?_⟩
        · simp [unmarshalRet, putGpr, assocLookup_same, trunc64To32_zext32To64]
        · simp [execRetRead, compileRetReadOp, encodeValWords, putGpr, assocLookup_same]
      | float64 =>
        cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
        subst hrm
        cases retVal <;> repeat exact False.elim hRet
        refine ⟨putGpr fCall 0 _, rfl, rfl, ?_, ?_⟩
        · simp [unmarshalRet, putGpr, assocLookup_same]
        · simp [execRetRead, compileRetReadOp, encodeValWords, putGpr, assocLookup_same]
      | zst _ => simp [classifyFnAbi, classifyRet] at hrm
      | hfa2F64 => cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
      | hfa4F32 => cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
      | simd4F32 => cases hsd : simdDirectEnabled t rel conv <;> simp [classifyFnAbi, classifyRet, hsd] at hrm
      | bigStruct _ => simp [classifyFnAbi, classifyRet] at hrm
    | directXmm0F32 =>
      cases ret with
      | float32 =>
        cases retVal <;> repeat exact False.elim hRet
        refine ⟨putXmm fCall 0 (zext32To128 _), rfl, ?_, ?_, ?_⟩
        · simp [execRetWrite, compileRetWriteOp, encodeValWords, trunc64To32_zext32To64]
        · simp [unmarshalRet, putXmm, assocLookup_same, trunc128To32_zext32To128]
        · simp [execRetRead, compileRetReadOp, encodeValWords, putXmm, assocLookup_same, trunc128To32_zext32To128]
      | simd4F32 =>
        cases hsd : simdDirectEnabled t rel conv <;> simp [classifyFnAbi, classifyRet, hsd] at hrm
      | zst _ | intScalar _ | nicheNonNull | float64 | hfa2F64 | hfa4F32 | bigStruct _ =>
        cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
    | directXmm0F64 =>
      cases ret with
      | float64 =>
        cases retVal <;> repeat exact False.elim hRet
        refine ⟨putXmm fCall 0 (zext64To128 _), rfl, rfl, ?_, ?_⟩
        · simp [unmarshalRet, putXmm, assocLookup_same, trunc128To64_zext64To128]
        · simp [execRetRead, compileRetReadOp, encodeValWords, putXmm, assocLookup_same, trunc128To64_zext64To128]
      | simd4F32 =>
        cases hsd : simdDirectEnabled t rel conv <;> simp [classifyFnAbi, classifyRet, hsd] at hrm
      | zst _ | intScalar _ | nicheNonNull | float32 | hfa2F64 | hfa4F32 | bigStruct _ =>
        cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
    | directX87F32 =>
      rw [hrm] at hX87
      have hns : isNonSignalingRet retVal := by
        cases hX87 with
        | inl hx => cases hx
        | inr hns => exact hns
      cases ret with
      | float32 =>
        cases retVal with
        | float32 bits =>
          have hns' : isF32SignalingNaN bits = false := hns
          have htr : x87TransferF32 bits = bits := by
            dsimp only [x87TransferF32]
            rw [hns', ite_bool_false]
          refine ⟨{ fCall with x87F32 := some bits }, ?_, ?_, rfl, rfl⟩
          · simp [marshalRet, htr]
          · simp [execRetWrite, compileRetWriteOp, encodeValWords, trunc64To32_zext32To64, htr]
        | zst | intScalar _ _ | float64 _ | nicheNonNull _ | hfa2F64 _ _ | hfa4F32 _ _ _ _ | simd4F32 _ | bigStruct _ =>
          exact False.elim hRet
      | simd4F32 =>
        cases hsd : simdDirectEnabled t rel conv <;> simp [classifyFnAbi, classifyRet, hsd] at hrm
      | zst _ | intScalar _ | nicheNonNull | float64 | hfa2F64 | hfa4F32 | bigStruct _ =>
        cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
    | directX87F64 =>
      rw [hrm] at hX87
      have hns : isNonSignalingRet retVal := by
        cases hX87 with
        | inl hx => cases hx
        | inr hns => exact hns
      cases ret with
      | float64 =>
        cases retVal with
        | float64 bits =>
          have hns' : isF64SignalingNaN bits = false := hns
          have htr : x87TransferF64 bits = bits := by
            dsimp only [x87TransferF64]
            rw [hns', ite_bool_false]
          refine ⟨{ fCall with x87F64 := some bits }, ?_, ?_, rfl, rfl⟩
          · simp [marshalRet, htr]
          · simp [execRetWrite, compileRetWriteOp, encodeValWords, htr]
        | zst | intScalar _ _ | float32 _ | nicheNonNull _ | hfa2F64 _ _ | hfa4F32 _ _ _ _ | simd4F32 _ | bigStruct _ =>
          exact False.elim hRet
      | simd4F32 =>
        cases hsd : simdDirectEnabled t rel conv <;> simp [classifyFnAbi, classifyRet, hsd] at hrm
      | zst _ | intScalar _ | nicheNonNull | float32 | hfa2F64 | hfa4F32 | bigStruct _ =>
        cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
    | directPairXmm01F64 =>
      cases ret with
      | hfa2F64 =>
        cases retVal <;> repeat exact False.elim hRet
        refine ⟨putXmm (putXmm fCall 0 (zext64To128 _)) 1 (zext64To128 _), rfl, rfl, ?_, ?_⟩
        · simp [unmarshalRet, putXmm, assocLookup_same, assocLookup_ne (by decide : (0 : Nat) ≠ 1),
                trunc128To64_zext64To128]
        · simp [execRetRead, compileRetReadOp, encodeValWords, putXmm, assocLookup_same,
                assocLookup_ne (by decide : (0 : Nat) ≠ 1), trunc128To64_zext64To128]
      | hfa4F32 =>
        cases retVal <;> repeat exact False.elim hRet
        refine ⟨putXmm (putXmm fCall 0 (zext64To128 (pack2x32 _ _))) 1 (zext64To128 (pack2x32 _ _)),
                rfl, rfl, ?_, ?_⟩
        · simp [unmarshalRet, putXmm, assocLookup_same, assocLookup_ne (by decide : (0 : Nat) ≠ 1),
                trunc128To64_zext64To128, unpackLo32_pack2x32, unpackHi32_pack2x32]
        · simp [execRetRead, compileRetReadOp, encodeValWords, putXmm, assocLookup_same,
                assocLookup_ne (by decide : (0 : Nat) ≠ 1), trunc128To64_zext64To128]
      | simd4F32 =>
        cases hsd : simdDirectEnabled t rel conv <;> simp [classifyFnAbi, classifyRet, hsd] at hrm
      | zst _ | intScalar _ | nicheNonNull | float32 | float64 | bigStruct _ =>
        cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
    | directQuadXmm03F32 =>
      cases ret with
      | hfa4F32 =>
        cases retVal with
        | hfa4F32 a b c d =>
          let f1 := putXmm fCall 0 (zext32To128 a)
          let f2 := putXmm f1 1 (zext32To128 b)
          let f3 := putXmm f2 2 (zext32To128 c)
          let f4 := putXmm f3 3 (zext32To128 d)
          refine ⟨f4, rfl, ?_, ?_, ?_⟩
          · simp only [execRetWrite, compileRetWriteOp, encodeValWords,
                       unpackLo32_pack2x32, unpackHi32_pack2x32]
            rfl
          · simp [unmarshalRet, f4, f3, f2, f1, putXmm, assocLookup_same,
                  assocLookup_ne (by decide : (0 : Nat) ≠ 3), assocLookup_ne (by decide : (0 : Nat) ≠ 2),
                  assocLookup_ne (by decide : (0 : Nat) ≠ 1), assocLookup_ne (by decide : (1 : Nat) ≠ 3),
                  assocLookup_ne (by decide : (1 : Nat) ≠ 2), assocLookup_ne (by decide : (2 : Nat) ≠ 3),
                  trunc128To32_zext32To128]
          · simp [execRetRead, compileRetReadOp, encodeValWords, f4, f3, f2, f1, putXmm, assocLookup_same,
                  assocLookup_ne (by decide : (0 : Nat) ≠ 3), assocLookup_ne (by decide : (0 : Nat) ≠ 2),
                  assocLookup_ne (by decide : (0 : Nat) ≠ 1), assocLookup_ne (by decide : (1 : Nat) ≠ 3),
                  assocLookup_ne (by decide : (1 : Nat) ≠ 2), assocLookup_ne (by decide : (2 : Nat) ≠ 3),
                  trunc128To32_zext32To128]
        | zst | intScalar _ _ | float32 _ | float64 _ | nicheNonNull _ | hfa2F64 _ _ | simd4F32 _ | bigStruct _ =>
          exact False.elim hRet
      | simd4F32 =>
        cases hsd : simdDirectEnabled t rel conv <;> simp [classifyFnAbi, classifyRet, hsd] at hrm
      | zst _ | intScalar _ | nicheNonNull | float32 | float64 | hfa2F64 | bigStruct _ =>
        cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
    | directXmm0Vec128 =>
      cases ret with
      | simd4F32 =>
        cases retVal <;> repeat exact False.elim hRet
        refine ⟨putXmm fCall 0 _, rfl, ?_, ?_, ?_⟩
        · simp [execRetWrite, compileRetWriteOp, encodeValWords, pack2x64_trunc_hi]
        · simp [unmarshalRet, putXmm, assocLookup_same]
        · simp [execRetRead, compileRetReadOp, encodeValWords, putXmm, assocLookup_same]
      | zst _ | intScalar _ | nicheNonNull | float32 | float64 | hfa2F64 | hfa4F32 | bigStruct _ =>
        cases t <;> cases conv <;> simp [classifyFnAbi, classifyRet] at hrm
    | indirectSret loc expTy =>
      have ⟨hsl, hne, heq⟩ :=
        classifyRet_sretLoc_consistent t rel { conv := conv, args := args, ret := ret } loc expTy hrm
      subst heq
      have hTok1 : readSretTok loc fCall = some 1 := by
        rw [← hsl]
        exact hSret (by rw [hsl]; exact hne)
      have hTok1' : readSretTok loc (writeMemWords fCall 1 (encodeValWords retVal)) = some 1 := by
        cases loc <;> exact hTok1
      refine ⟨writeMemWords fCall 1 (encodeValWords retVal), ?_, ?_, ?_, ?_⟩
      · simp [marshalRet, hChk, hTok1]
      · simp [execRetWrite, compileRetWriteOp, hTok1]
      · dsimp only [unmarshalRet]
        rw [abiTyEq_refl]
        simp only [ite_true]
        rw [hTok1']
        simp [writeMemWords, assocLookup_same, hDec]
      · dsimp only [execRetRead, compileRetReadOp]
        rw [hTok1']
        simp [writeMemWords, assocLookup_same]

/-! ### Universal `i686` x87 `f32` / `f64` Signaling-NaN Quietening Arithmetic -/

private theorem nat_div_add_exact {a b d : Nat} (hd : 0 < d) (h : b = 1 * d) :
    Nat.div (a + b) d = Nat.div a d + 1 := by
  subst h
  rw [Nat.one_mul]
  have h1 : a + d = a + 1 * d := by rw [Nat.one_mul]
  rw [h1]
  exact nat_add_mul_div_right a 1 hd

private theorem nat_mod_2_add1_of_eq0 {q : Nat} (h : Nat.mod q 2 = 0) :
    Nat.mod (q + 1) 2 = 1 := by
  have hdecomp : 2 * Nat.div q 2 + Nat.mod q 2 = q := nat_div_add_mod q 2
  rw [h, Nat.add_zero] at hdecomp
  rw [← hdecomp, Nat.mul_comm, Nat.add_comm]
  exact nat_mod_add_mul_right 1 2 (Nat.div q 2)

private theorem x87_f32_snan_quietens (b : BitVec 32) (h : isF32SignalingNaN b = true) :
    x87TransferF32 b ≠ b ∧ isF32SignalingNaN (x87TransferF32 b) = false := by
  unfold isF32SignalingNaN at h
  simp only [bool_and_true_iff] at h
  have ⟨⟨hexp, hqb⟩, hpay⟩ := h
  have hqb0 : Nat.mod (Nat.div b.toNat 4194304) 2 = 0 := nat_eq_of_beq hqb
  have hlt : b.toNat < 4294967296 := b.isLt
  have hpos : 0 < 4194304 := by decide
  have hqlt : Nat.div b.toNat 4194304 < 1024 := by
    rw [nat_div_lt_iff_lt_mul hpos]
    exact hlt
  have hqle : Nat.div b.toNat 4194304 ≤ 1022 := by
    have hdecomp : 2 * Nat.div (Nat.div b.toNat 4194304) 2 + Nat.mod (Nat.div b.toNat 4194304) 2 =
        Nat.div b.toNat 4194304 := nat_div_add_mod _ 2
    rw [hqb0, Nat.add_zero] at hdecomp
    have hk : Nat.div (Nat.div b.toNat 4194304) 2 < 512 := by
      rw [nat_div_lt_iff_lt_mul (by decide : 0 < 2)]
      exact hqlt
    have hk2 : Nat.div (Nat.div b.toNat 4194304) 2 ≤ 511 := Nat.le_of_lt_succ hk
    rw [← hdecomp]
    exact Nat.mul_le_mul_left 2 hk2
  have hSumLt : b.toNat + 4194304 < Nat.pow 2 32 := by
    have hdm : 4194304 * Nat.div b.toNat 4194304 + Nat.mod b.toNat 4194304 = b.toNat :=
      nat_div_add_mod b.toNat 4194304
    have hmLt : Nat.mod b.toNat 4194304 < 4194304 := nat_mod_lt b.toNat hpos
    have hqmul : 4194304 * Nat.div b.toNat 4194304 ≤ 4194304 * 1022 :=
      Nat.mul_le_mul_left 4194304 hqle
    have h1 : b.toNat < 4194304 * 1022 + 4194304 := by
      rw [← hdm]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hmLt _) (Nat.add_le_add_right hqmul 4194304)
    have h2 : b.toNat + 4194304 < (4194304 * 1022 + 4194304) + 4194304 :=
      Nat.add_lt_add_right h1 4194304
    exact h2
  have hsnan : isF32SignalingNaN b = true := by
    unfold isF32SignalingNaN
    simp [hexp, hqb, hpay]
  have htr : x87TransferF32 b = BitVec.ofNat 32 (b.toNat + 4194304) := by
    simp [x87TransferF32, hsnan]
  have htrNat : (x87TransferF32 b).toNat = b.toNat + 4194304 := by
    rw [htr]
    exact bv_toNat_ofNat_of_lt hSumLt
  constructor
  · intro heq
    have hnat : (x87TransferF32 b).toNat = b.toNat := congrArg BitVec.toNat heq
    rw [htrNat] at hnat
    have hlt' : b.toNat < b.toNat + 4194304 := Nat.lt_add_of_pos_right hpos
    rw [hnat] at hlt'
    exact Nat.lt_irrefl _ hlt'
  · unfold isF32SignalingNaN
    rw [htrNat]
    have hdiv : Nat.div (b.toNat + 4194304) 4194304 = Nat.div b.toNat 4194304 + 1 :=
      nat_div_add_exact hpos (by decide)
    rw [hdiv, nat_mod_2_add1_of_eq0 hqb0]
    dsimp only
    have h10 : Nat.beq 1 0 = false := rfl
    rw [h10]
    simp

private theorem x87_f64_snan_quietens (b : BitVec 64) (h : isF64SignalingNaN b = true) :
    x87TransferF64 b ≠ b ∧ isF64SignalingNaN (x87TransferF64 b) = false := by
  unfold isF64SignalingNaN at h
  simp only [bool_and_true_iff] at h
  have ⟨⟨hexp, hqb⟩, hpay⟩ := h
  have hqb0 : Nat.mod (Nat.div b.toNat 2251799813685248) 2 = 0 := nat_eq_of_beq hqb
  have hlt : b.toNat < 18446744073709551616 := b.isLt
  have hpos : 0 < 2251799813685248 := by decide
  have hqlt : Nat.div b.toNat 2251799813685248 < 8192 := by
    rw [nat_div_lt_iff_lt_mul hpos]
    exact hlt
  have hqle : Nat.div b.toNat 2251799813685248 ≤ 8190 := by
    have hdecomp : 2 * Nat.div (Nat.div b.toNat 2251799813685248) 2 +
        Nat.mod (Nat.div b.toNat 2251799813685248) 2 = Nat.div b.toNat 2251799813685248 :=
      nat_div_add_mod _ 2
    rw [hqb0, Nat.add_zero] at hdecomp
    have hk : Nat.div (Nat.div b.toNat 2251799813685248) 2 < 4096 := by
      rw [nat_div_lt_iff_lt_mul (by decide : 0 < 2)]
      exact hqlt
    have hk2 : Nat.div (Nat.div b.toNat 2251799813685248) 2 ≤ 4095 := Nat.le_of_lt_succ hk
    rw [← hdecomp]
    exact Nat.mul_le_mul_left 2 hk2
  have hSumLt : b.toNat + 2251799813685248 < Nat.pow 2 64 := by
    have hdm : 2251799813685248 * Nat.div b.toNat 2251799813685248 +
        Nat.mod b.toNat 2251799813685248 = b.toNat :=
      nat_div_add_mod b.toNat 2251799813685248
    have hmLt : Nat.mod b.toNat 2251799813685248 < 2251799813685248 := nat_mod_lt b.toNat hpos
    have hqmul : 2251799813685248 * Nat.div b.toNat 2251799813685248 ≤ 2251799813685248 * 8190 :=
      Nat.mul_le_mul_left 2251799813685248 hqle
    have h1 : b.toNat < 2251799813685248 * 8190 + 2251799813685248 := by
      rw [← hdm]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hmLt _) (Nat.add_le_add_right hqmul 2251799813685248)
    have h2 : b.toNat + 2251799813685248 <
        (2251799813685248 * 8190 + 2251799813685248) + 2251799813685248 :=
      Nat.add_lt_add_right h1 2251799813685248
    exact h2
  have hsnan : isF64SignalingNaN b = true := by
    unfold isF64SignalingNaN
    simp [hexp, hqb, hpay]
  have htr : x87TransferF64 b = BitVec.ofNat 64 (b.toNat + 2251799813685248) := by
    simp [x87TransferF64, hsnan]
  have htrNat : (x87TransferF64 b).toNat = b.toNat + 2251799813685248 := by
    rw [htr]
    exact bv_toNat_ofNat_of_lt hSumLt
  constructor
  · intro heq
    have hnat : (x87TransferF64 b).toNat = b.toNat := congrArg BitVec.toNat heq
    rw [htrNat] at hnat
    have hlt' : b.toNat < b.toNat + 2251799813685248 := Nat.lt_add_of_pos_right hpos
    rw [hnat] at hlt'
    exact Nat.lt_irrefl _ hlt'
  · unfold isF64SignalingNaN
    rw [htrNat]
    have hdiv : Nat.div (b.toNat + 2251799813685248) 2251799813685248 =
        Nat.div b.toNat 2251799813685248 + 1 :=
      nat_div_add_exact hpos (by decide)
    rw [hdiv, nat_mod_2_add1_of_eq0 hqb0]
    dsimp only
    have h10 : Nat.beq 1 0 = false := rfl
    rw [h10]
    simp

end Stage4ProofHelpers

/-! ## Part VI: Core Target Theorems (To Be Frozen in Stage 3 & Proved in Stage 4) -/

/-- **Theorem 1 (Same-Fingerprint Bit-Exact Argument & Threaded-`sret` Return Roundtrip):**
Under the finite-frame bound `sig.args.length + 2 < Nat.pow 2 64` (preventing
64-bit indirect token wrap-around), for every `(t, rel, sig)` and well-typed
`(vals, retVal)`:
1. Marshaling `vals` succeeds into `fCall` and unmarshals back bit-for-bit to
   `vals` (internally allocating any caller `sret` token at `1` strictly before
   argument indirect tokens `>= 2`, witnessed by the threaded `marshalRet` clause);
2. Marshaling `retVal` into the SAME threaded call frame `fCall` (writing into
   `fCall`'s caller-allocated `sret` buffer when `retMode` is `.indirectSret`)
   succeeds into `fOut` and unmarshals back bit-for-bit to `retVal` whenever
   either `isX87RetMode abi.retMode = false` OR `isNonSignalingRet retVal`
   (tighter than checking `sig.conv = .rust`: also guarantees bit-exact sNaN
   returns for `extern "C"`/`vectorcall` on `sysv64`, `win64Msvc`, `aapcs64`!). -/
theorem same_abi_marshal_roundtrip
    (t : AbiTarget) (rel : RustcRelease) (sig : FnSig)
    (hArity : sig.args.length + 2 < Nat.pow 2 64)
    (vals : List AbiVal) (hVals : valsHaveTys vals sig.args)
    (retVal : AbiVal) (hRet : valHasTy retVal sig.ret) :
    let abi := classifyFnAbi t rel sig
    ∃ fCall,
      marshalArgs abi vals = .ok fCall ∧
      unmarshalArgs abi sig.args fCall = .ok vals ∧
      ((isX87RetMode abi.retMode = false ∨ isNonSignalingRet retVal) →
        ∃ fOut, marshalRet fCall abi.retMode retVal = .ok fOut ∧
                unmarshalRet abi.retMode sig.ret fOut = .ok retVal) := by
  dsimp only
  let abi := classifyFnAbi t rel sig
  let f0 := initSretBuffer abi.sretLoc emptyFrame
  have hS0 := initSretBuffer_spec abi.sretLoc
  have hTokBound : f0.nextTok + sig.args.length < Nat.pow 2 64 := by
    have h1 : f0.nextTok + sig.args.length ≤ 2 + sig.args.length :=
      Nat.add_le_add_right hS0.1 sig.args.length
    rw [Nat.add_comm 2 sig.args.length] at h1
    exact Nat.lt_of_le_of_lt h1 hArity
  have ⟨fCall, hM, _, _, hPres, hU, _⟩ := marshalArgsLoop_master t rel sig.conv hVals
      (match abi.sretLoc with | .gpr0 => 1 | _ => 0)
      (match abi.sretLoc, usesWin64PositionalSlots t sig.conv with | .gpr0, true => 1 | _, _ => 0)
      (match abi.sretLoc with | .stack0 => 1 | _ => 0)
      f0 hTokBound
  refine ⟨fCall, hM, hU, fun hX87 => ?_⟩
  have hSret : abi.sretLoc ≠ .none → readSretTok abi.sretLoc fCall = some 1 := fun hne =>
    Eq.trans (framePreserves_readSretTok t rel sig hPres) (hS0.2 hne)
  have ⟨fOut, hMR, _, hUR, _⟩ := marshalRet_step t rel sig hRet hSret hX87
  exact ⟨fOut, hMR, hUR⟩

/-- **Theorem 2 (Release-Fingerprinted Cross-Compilation Call-Boundary Soundness):**
Whenever `fullAbiCompatible (classifyFnAbi t₁ rel₁ sig) (classifyFnAbi t₂ rel₂ sig) = true`
(under the finite-frame bound), the two compilations share identical calling
convention, `sret` location, pass modes, and `.o` linker `symbolRule` (no `0` vs
`@@0` collision!), and direct caller-to-callee marshaling/unmarshaling is
bit-exact in both directions without an adapter shim. -/
theorem fullAbiCompatible_preserves_call_boundary
    (t₁ t₂ : AbiTarget) (rel₁ rel₂ : RustcRelease) (sig : FnSig)
    (hArity : sig.args.length + 2 < Nat.pow 2 64)
    (hCompat : fullAbiCompatible (classifyFnAbi t₁ rel₁ sig) (classifyFnAbi t₂ rel₂ sig) = true)
    (vals : List AbiVal) (hVals : valsHaveTys vals sig.args)
    (retVal : AbiVal) (hRet : valHasTy retVal sig.ret) :
    let abi₁ := classifyFnAbi t₁ rel₁ sig
    let abi₂ := classifyFnAbi t₂ rel₂ sig
    abi₁.symbolRule = abi₂.symbolRule ∧
    abi₁.conv = abi₂.conv ∧
    ∃ fCall,
      marshalArgs abi₁ vals = .ok fCall ∧
      unmarshalArgs abi₂ sig.args fCall = .ok vals ∧
      ((isX87RetMode abi₂.retMode = false ∨ isNonSignalingRet retVal) →
        ∃ fOut, marshalRet fCall abi₂.retMode retVal = .ok fOut ∧
                unmarshalRet abi₁.retMode sig.ret fOut = .ok retVal) := by
  dsimp only
  have heq : classifyFnAbi t₁ rel₁ sig = classifyFnAbi t₂ rel₂ sig :=
    fullAbiCompatible_eq hCompat
  refine ⟨congrArg ComputedFnAbi.symbolRule heq, congrArg ComputedFnAbi.conv heq, ?_⟩
  rw [← heq]
  exact same_abi_marshal_roundtrip t₁ rel₁ sig hArity vals hVals retVal hRet

/-- **Theorem 3 (Non-Tautological Physical-Frame Adapter-Shim Refinement Across Divergent Releases):**
For ANY same-target release pair `(t, rel₁, rel₂)` and signature `sig` (with
`sig.args.length + 2 < Nat.pow 2 64`), the statically compiled, `AbiVal`-free
physical-frame shim `plan := compileShimPlan abi₁ abi₂ sig`:
1. Transforms `fCaller` into `fCallee` via two-phase raw `BitVec 64` word
   reads/writes (`execArgShim plan fCaller = .ok fCallee`) such that the callee
   unmarshals the EXACT original `vals` bit-for-bit (`unmarshalArgs abi₂ ...`);
2. Transforms the callee's return frame `fCalleeOut` back into the caller's
   original frame `fCaller` (`execRetShim plan fCaller fCalleeOut = .ok fCallerOut`,
   populating caller's `sret` buffer when needed!) such that the caller unmarshals
   the EXACT original `retVal` whenever neither side transfers through x87 or
   `isNonSignalingRet retVal`;
3. Accurately flags `plan.needsLinkerAlias = true ↔ abi₁.symbolRule ≠ abi₂.symbolRule`
   (explicitly signaling when a linker-level wrapper alias is required for `D4`!). -/
theorem phys_shim_bridge_restores_equivalence
    (t : AbiTarget) (rel₁ rel₂ : RustcRelease) (sig : FnSig)
    (hArity : sig.args.length + 2 < Nat.pow 2 64)
    (vals : List AbiVal) (hVals : valsHaveTys vals sig.args)
    (retVal : AbiVal) (hRet : valHasTy retVal sig.ret) :
    let abi₁ := classifyFnAbi t rel₁ sig
    let abi₂ := classifyFnAbi t rel₂ sig
    let plan := compileShimPlan abi₁ abi₂ sig
    (plan.needsLinkerAlias = true ↔ abi₁.symbolRule ≠ abi₂.symbolRule) ∧
    ∃ fCaller fCallee,
      marshalArgs abi₁ vals = .ok fCaller ∧
      execArgShim plan fCaller = .ok fCallee ∧
      unmarshalArgs abi₂ sig.args fCallee = .ok vals ∧
      (((isX87RetMode abi₁.retMode = false ∧ isX87RetMode abi₂.retMode = false) ∨
        isNonSignalingRet retVal) →
        ∃ fCalleeOut fCallerOut,
          marshalRet fCallee abi₂.retMode retVal = .ok fCalleeOut ∧
          execRetShim plan fCaller fCalleeOut = .ok fCallerOut ∧
          unmarshalRet abi₁.retMode sig.ret fCallerOut = .ok retVal) := by
  dsimp only
  let abi₁ := classifyFnAbi t rel₁ sig
  let abi₂ := classifyFnAbi t rel₂ sig
  let plan := compileShimPlan abi₁ abi₂ sig
  refine ⟨?_, ?_⟩
  · constructor
    · intro h heq
      have hsr : symbolRuleEq abi₁.symbolRule abi₂.symbolRule = true :=
        symbolRuleEq_iff.mpr heq
      dsimp only [plan, compileShimPlan] at h
      rw [hsr] at h
      cases h
    · intro hne
      cases hsr : symbolRuleEq abi₁.symbolRule abi₂.symbolRule
      · dsimp only [plan, compileShimPlan]
        rw [hsr]; rfl
      · exact False.elim (hne (symbolRuleEq_eq hsr))
  · let f01 := initSretBuffer abi₁.sretLoc emptyFrame
    have hS01 := initSretBuffer_spec abi₁.sretLoc
    have hTok1 : f01.nextTok + sig.args.length < Nat.pow 2 64 := by
      have h1 : f01.nextTok + sig.args.length ≤ 2 + sig.args.length :=
        Nat.add_le_add_right hS01.1 sig.args.length
      rw [Nat.add_comm 2 sig.args.length] at h1
      exact Nat.lt_of_le_of_lt h1 hArity
    have ⟨fCaller, hM1, _, _, hPres1, _, hR1⟩ := marshalArgsLoop_master t rel₁ sig.conv hVals
        (match abi₁.sretLoc with | .gpr0 => 1 | _ => 0)
        (match abi₁.sretLoc, usesWin64PositionalSlots t sig.conv with | .gpr0, true => 1 | _, _ => 0)
        (match abi₁.sretLoc with | .stack0 => 1 | _ => 0)
        f01 hTok1
    let f02 := initSretBuffer abi₂.sretLoc emptyFrame
    have hS02 := initSretBuffer_spec abi₂.sretLoc
    have hTok2 : f02.nextTok + sig.args.length < Nat.pow 2 64 := by
      have h1 : f02.nextTok + sig.args.length ≤ 2 + sig.args.length :=
        Nat.add_le_add_right hS02.1 sig.args.length
      rw [Nat.add_comm 2 sig.args.length] at h1
      exact Nat.lt_of_le_of_lt h1 hArity
    have ⟨fCallee, _, hW2, _, hPres2, hU2, _⟩ := marshalArgsLoop_master t rel₂ sig.conv hVals
        (match abi₂.sretLoc with | .gpr0 => 1 | _ => 0)
        (match abi₂.sretLoc, usesWin64PositionalSlots t sig.conv with | .gpr0, true => 1 | _, _ => 0)
        (match abi₂.sretLoc with | .stack0 => 1 | _ => 0)
        f02 hTok2
    have hR1' : execPhysReads fCaller (compileArgReads abi₁.argModes sig.args) = .ok (vals.map encodeValWords) := hR1
    have hW2' : execPhysWrites f02 (compileArgWrites abi₂.argModes sig.args) (vals.map encodeValWords) = .ok fCallee := hW2
    have hArgShim : execArgShim plan fCaller = .ok fCallee := by
      dsimp only [execArgShim, plan, compileShimPlan]
      rw [hR1']
      exact hW2'
    refine ⟨fCaller, fCallee, hM1, hArgShim, hU2, fun hX87 => ?_⟩
    have hX87_1 : isX87RetMode abi₁.retMode = false ∨ isNonSignalingRet retVal := by
      cases hX87 with
      | inl h12 => exact Or.inl h12.1
      | inr hns => exact Or.inr hns
    have hX87_2 : isX87RetMode abi₂.retMode = false ∨ isNonSignalingRet retVal := by
      cases hX87 with
      | inl h12 => exact Or.inl h12.2
      | inr hns => exact Or.inr hns
    have hSret1 : abi₁.sretLoc ≠ .none → readSretTok abi₁.sretLoc fCaller = some 1 := fun hne =>
      Eq.trans (framePreserves_readSretTok t rel₁ sig hPres1) (hS01.2 hne)
    have hSret2 : abi₂.sretLoc ≠ .none → readSretTok abi₂.sretLoc fCallee = some 1 := fun hne =>
      Eq.trans (framePreserves_readSretTok t rel₂ sig hPres2) (hS02.2 hne)
    have ⟨fCalleeOut, hMR2, _, _, hRR2⟩ := marshalRet_step t rel₂ sig hRet hSret2 hX87_2
    have ⟨fCallerOut, _, hRW1, hUR1, _⟩ := marshalRet_step t rel₁ sig hRet hSret1 hX87_1
    have hRetShim : execRetShim plan fCaller fCalleeOut = .ok fCallerOut := by
      dsimp only [execRetShim, plan, compileShimPlan]
      rw [hRR2]
      exact hRW1
    exact ⟨fCalleeOut, fCallerOut, hMR2, hRetShim, hUR1⟩

/-- **Theorem 4 (Sharpness of Full Fingerprinting & Universal x87 sNaN Quietening):**
(a) **IR-Only Fingerprint Incompleteness (`D4`):** On the real `E2-6` 2-arg
    `vectorcall` signature `(HfaF32x4, f32) -> HfaF32x4`, `irOnlyCompatible = true`
    across `1.100.0` vs `1.102.0` while `fullAbiCompatible = false` (`@@16 ≠ @@24`);
(b) **Universal `i686` x87 `f32` & `f64` Signaling-NaN Non-Preservation:** For
    EVERY `f32` signaling NaN `b` (`isF32SignalingNaN b = true`), `i686SysV`
    `extern "C"` return strictly alters `b` (`out ≠ b` and `isF32SignalingNaN out = false`),
    whereas `extern "Rust"` preserves `b` bit-for-bit — and identically for EVERY
    `f64` signaling NaN `b64`! -/
theorem fingerprint_and_universal_x87_sharpness :
    (∃ t rel₁ rel₂ sig,
      irOnlyCompatible (classifyFnAbi t rel₁ sig) (classifyFnAbi t rel₂ sig) = true ∧
      fullAbiCompatible (classifyFnAbi t rel₁ sig) (classifyFnAbi t rel₂ sig) = false) ∧
    (∀ b : BitVec 32, isF32SignalingNaN b = true →
      let cAbi := classifyFnAbi .i686SysV .r1_99_1 { conv := .c, args := [], ret := .float32 }
      let rAbi := classifyFnAbi .i686SysV .r1_99_1 { conv := .rust, args := [], ret := .float32 }
      (∃ fC out, marshalRet emptyFrame cAbi.retMode (.float32 b) = .ok fC ∧
                 unmarshalRet cAbi.retMode .float32 fC = .ok (.float32 out) ∧
                 out ≠ b ∧ isF32SignalingNaN out = false) ∧
      (∃ fR, marshalRet emptyFrame rAbi.retMode (.float32 b) = .ok fR ∧
             unmarshalRet rAbi.retMode .float32 fR = .ok (.float32 b))) ∧
    (∀ b : BitVec 64, isF64SignalingNaN b = true →
      let cAbi := classifyFnAbi .i686SysV .r1_99_1 { conv := .c, args := [], ret := .float64 }
      let rAbi := classifyFnAbi .i686SysV .r1_99_1 { conv := .rust, args := [], ret := .float64 }
      (∃ fC out, marshalRet emptyFrame cAbi.retMode (.float64 b) = .ok fC ∧
                 unmarshalRet cAbi.retMode .float64 fC = .ok (.float64 out) ∧
                 out ≠ b ∧ isF64SignalingNaN out = false) ∧
      (∃ fR, marshalRet emptyFrame rAbi.retMode (.float64 b) = .ok fR ∧
             unmarshalRet rAbi.retMode .float64 fR = .ok (.float64 b))) := by
  refine ⟨⟨.sysv64, .r1_100_0, .r1_102_0,
           { conv := .vectorcall, args := [.hfa4F32, .float32], ret := .hfa4F32 },
           rfl, rfl⟩, ?_, ?_⟩
  · intro b hb
    have ⟨hne, hq⟩ := x87_f32_snan_quietens b hb
    refine ⟨⟨{ emptyFrame with x87F32 := some (x87TransferF32 b) }, x87TransferF32 b,
             rfl, rfl, hne, hq⟩,
            ⟨putGpr emptyFrame 0 (zext32To64 b), rfl, ?_⟩⟩
    simp [classifyFnAbi, classifyRet, unmarshalRet, putGpr, assocLookup_same, trunc64To32_zext32To64]
  · intro b hb
    have ⟨hne, hq⟩ := x87_f64_snan_quietens b hb
    refine ⟨⟨{ emptyFrame with x87F64 := some (x87TransferF64 b) }, x87TransferF64 b,
             rfl, rfl, hne, hq⟩,
            ⟨putGpr emptyFrame 0 b, rfl, ?_⟩⟩
    simp [classifyFnAbi, classifyRet, unmarshalRet, putGpr, assocLookup_same]

/-! ## Part VII: Concrete Empirical Drift Witnesses & Positive Canaries (0 `sorry`) -/

/-- Witness `D1` (`rust-lang/rust@429c1c18ca61`): BOTH `sysv64` AND `i686SysV`
`extern "Rust"` `F32x4` break between `1.99.1` (`Indirect + sret`, with `sret`
in `rdi`/`stack0` and arg ptr in `rsi`/`stack1`) and `1.100.0` (`Direct(Vector)`
in `xmm0`), while `extern "C"` SIMD stays direct and stable on `win64Msvc`/`i686SysV`. -/
def sigD1Simd : FnSig := { conv := .rust, args := [.simd4F32], ret := .simd4F32 }
def sigD1SimdC : FnSig := { conv := .c, args := [.simd4F32], ret := .simd4F32 }

theorem ce_d1_x86_64_and_i686_simd_1_99_1_vs_1_100_0 :
    fullAbiCompatible (classifyFnAbi .sysv64 .r1_99_1 sigD1Simd)
                      (classifyFnAbi .sysv64 .r1_100_0 sigD1Simd) = false ∧
    fullAbiCompatible (classifyFnAbi .i686SysV .r1_99_1 sigD1Simd)
                      (classifyFnAbi .i686SysV .r1_100_0 sigD1Simd) = false ∧
    fullAbiCompatible (classifyFnAbi .win64Msvc .r1_99_1 sigD1SimdC)
                      (classifyFnAbi .win64Msvc .r1_102_0 sigD1SimdC) = true ∧
    (match marshalArgs (classifyFnAbi .sysv64 .r1_99_1 sigD1Simd)
             [.simd4F32 (BitVec.ofNat 128 0x1122334455667788)] with
     | .ok f => unmarshalArgs (classifyFnAbi .sysv64 .r1_100_0 sigD1Simd) sigD1Simd.args f = .error .missingReg
     | .error _ => False) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Witness `D2` (`rust-lang/rust@a654a2404565`): `aarch64` `extern "Rust"`
NEON `F32x4` uses dedicated `x8` (`gpr8`) for `sret` while placing the indirect
arg ptr in `x0` (`initGpr = 0`!) through `1.99.1`/`1.100.0`, then breaks at
`1.100.0 -> 1.102.0`. -/
theorem ce_d2_aarch64_neon_x8_sret_and_1_100_0_vs_1_102_0 :
    (classifyFnAbi .aapcs64 .r1_100_0 sigD1Simd).sretLoc = .gpr8 ∧
    (classifyFnAbi .aapcs64 .r1_100_0 sigD1Simd).argModes = [.indirectGpr 0 .simd4F32] ∧
    fullAbiCompatible (classifyFnAbi .aapcs64 .r1_99_1 sigD1Simd)
                      (classifyFnAbi .aapcs64 .r1_100_0 sigD1Simd) = true ∧
    fullAbiCompatible (classifyFnAbi .aapcs64 .r1_100_0 sigD1Simd)
                      (classifyFnAbi .aapcs64 .r1_102_0 sigD1Simd) = false ∧
    (match marshalArgs (classifyFnAbi .aapcs64 .r1_100_0 sigD1Simd)
             [.simd4F32 (BitVec.ofNat 128 42)] with
     | .ok f => unmarshalArgs (classifyFnAbi .aapcs64 .r1_102_0 sigD1Simd) sigD1Simd.args f = .error .missingReg
     | .error _ => False) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Witness `D3` (`rust-lang/rust@916dda0c26e7`): On `win64Msvc` `extern "C"`,
non-`#[repr(C)]` ZST (`reprC = false`, e.g. `()`) was `Indirect` (`rcx`) in
`1.99.1` and `1.100.0`, flipping to `Ignore` in `1.102.0-nightly` (causing silent
register shift corruption: callee reads ZST token `1` from `rcx` as the `u64`
instead of `0xCAFEBABE`!), whereas `#[repr(C)]` ZST (`reprC = true`) stays
`Indirect` and `fullAbiCompatible = true` across ALL three releases! -/
def sigD3Win64ZstNonReprC : FnSig :=
  { conv := .c, args := [.zst false, .intScalar 8], ret := .intScalar 8 }
def sigD3Win64ZstReprC : FnSig :=
  { conv := .c, args := [.zst true, .intScalar 8], ret := .intScalar 8 }

theorem ce_d3_win64_zst_non_repr_c_1_100_0_vs_1_102_0 :
    fullAbiCompatible (classifyFnAbi .win64Msvc .r1_99_1 sigD3Win64ZstNonReprC)
                      (classifyFnAbi .win64Msvc .r1_100_0 sigD3Win64ZstNonReprC) = true ∧
    fullAbiCompatible (classifyFnAbi .win64Msvc .r1_100_0 sigD3Win64ZstNonReprC)
                      (classifyFnAbi .win64Msvc .r1_102_0 sigD3Win64ZstNonReprC) = false ∧
    fullAbiCompatible (classifyFnAbi .win64Msvc .r1_99_1 sigD3Win64ZstReprC)
                      (classifyFnAbi .win64Msvc .r1_102_0 sigD3Win64ZstReprC) = true ∧
    (match marshalArgs (classifyFnAbi .win64Msvc .r1_100_0 sigD3Win64ZstNonReprC)
             [.zst, .intScalar 8 (BitVec.ofNat 64 0xCAFEBABE)] with
     | .ok f =>
       unmarshalArgs (classifyFnAbi .win64Msvc .r1_102_0 sigD3Win64ZstNonReprC)
                     sigD3Win64ZstNonReprC.args f =
         .ok [.zst, .intScalar 8 (BitVec.ofNat 64 1)]
     | .error _ => False) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Witness `D4` (`rust-lang/rust@d11b3f4d61c5`): Exact `E2-6` 2-arg `vectorcall`
signature `(HfaF32x4, f32) -> HfaF32x4` lowers to `sret + indirect ptr + f32`,
giving `irOnlyCompatible = true` yet `@@16` (`8+8`) vs `@@24` (`16+8`) on
`sysv64`/`win64Msvc`, `@@20` (`16+4`) stable on `i686SysV`, AND `bigStruct 3`
breaking `@@8 -> @@24` on `x86_64`! -/
def sigD4VectorcallHfa4 : FnSig :=
  { conv := .vectorcall, args := [.hfa4F32, .float32], ret := .hfa4F32 }
def sigD4BigStruct : FnSig :=
  { conv := .vectorcall, args := [.bigStruct 3], ret := .intScalar 8 }

theorem ce_d4_vectorcall_hfa4_and_bigstruct_linker_breaks :
    irOnlyCompatible (classifyFnAbi .sysv64 .r1_100_0 sigD4VectorcallHfa4)
                     (classifyFnAbi .sysv64 .r1_102_0 sigD4VectorcallHfa4) = true ∧
    fullAbiCompatible (classifyFnAbi .sysv64 .r1_100_0 sigD4VectorcallHfa4)
                      (classifyFnAbi .sysv64 .r1_102_0 sigD4VectorcallHfa4) = false ∧
    (classifyFnAbi .sysv64 .r1_100_0 sigD4VectorcallHfa4).symbolRule = .vectorcallAtAt 16 ∧
    (classifyFnAbi .sysv64 .r1_102_0 sigD4VectorcallHfa4).symbolRule = .vectorcallAtAt 24 ∧
    (classifyFnAbi .i686SysV .r1_100_0 sigD4VectorcallHfa4).symbolRule = .vectorcallAtAt 20 ∧
    (classifyFnAbi .i686SysV .r1_102_0 sigD4VectorcallHfa4).symbolRule = .vectorcallAtAt 20 ∧
    (classifyFnAbi .sysv64 .r1_100_0 sigD4BigStruct).symbolRule = .vectorcallAtAt 8 ∧
    (classifyFnAbi .sysv64 .r1_102_0 sigD4BigStruct).symbolRule = .vectorcallAtAt 24 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Witness `D5`: `0`-arg `extern "C"` (`undecorated`) vs `extern "vectorcall"`
(`vectorcallAtAt 0`) NEVER falsely collide under `fullAbiCompatible`! -/
theorem ce_d5_no_undecorated_vs_vectorcall_at0_collision :
    let sigC : FnSig := { conv := .c, args := [], ret := .intScalar 8 }
    let sigV : FnSig := { conv := .vectorcall, args := [], ret := .intScalar 8 }
    fullAbiCompatible (classifyFnAbi .sysv64 .r1_102_0 sigC)
                      (classifyFnAbi .sysv64 .r1_102_0 sigV) = false := by
  exact rfl

/-- Witness `D6`: `i686` `extern "C"` x87 return quietens signaling NaN
`0x7f800001 -> 0x7fc00001`, while `extern "Rust"` preserves `0x7f800001` exact. -/
theorem ce_d6_i686_x87_snan_quietening_vs_rust_bit_exact :
    let snan : BitVec 32 := BitVec.ofNat 32 0x7f800001
    let qnan : BitVec 32 := BitVec.ofNat 32 0x7fc00001
    let cAbi := classifyFnAbi .i686SysV .r1_99_1 { conv := .c, args := [], ret := .float32 }
    let rAbi := classifyFnAbi .i686SysV .r1_99_1 { conv := .rust, args := [], ret := .float32 }
    (match marshalRet emptyFrame cAbi.retMode (.float32 snan) with
     | .ok f => unmarshalRet cAbi.retMode .float32 f = .ok (.float32 qnan)
     | .error _ => False) ∧
    (match marshalRet emptyFrame rAbi.retMode (.float32 snan) with
     | .ok f => unmarshalRet rAbi.retMode .float32 f = .ok (.float32 snan)
     | .error _ => False) := by
  exact ⟨rfl, rfl⟩

/-- Positive Canary `P1`: `sysv64` `extern "Rust"` on `(Option<NonNull<u8>>, hfa2F64, u32)`
is 100% release-stable across `1.99.1 -> 1.100.0 -> 1.102.0` AND roundtrips exact. -/
def sigP1Stable : FnSig :=
  { conv := .rust, args := [.nicheNonNull, .hfa2F64, .intScalar 4], ret := .hfa2F64 }

theorem canary_p1_sysv64_niche_hfa2_cross_release_stable :
    fullAbiCompatible (classifyFnAbi .sysv64 .r1_99_1 sigP1Stable)
                      (classifyFnAbi .sysv64 .r1_100_0 sigP1Stable) = true ∧
    fullAbiCompatible (classifyFnAbi .sysv64 .r1_100_0 sigP1Stable)
                      (classifyFnAbi .sysv64 .r1_102_0 sigP1Stable) = true ∧
    (let vals : List AbiVal := [.nicheNonNull (BitVec.ofNat 64 0x1000),
                                .hfa2F64 (BitVec.ofNat 64 0x3ff0000000000000) (BitVec.ofNat 64 0x7ff0000000000001),
                                .intScalar 4 (BitVec.ofNat 64 42)]
     match marshalArgs (classifyFnAbi .sysv64 .r1_99_1 sigP1Stable) vals with
     | .ok f => unmarshalArgs (classifyFnAbi .sysv64 .r1_102_0 sigP1Stable) sigP1Stable.args f = .ok vals
     | .error _ => False) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Positive Canary `P2`: Static `AbiVal`-free `PhysShim` restores exact
transport for real `D3` (`Win64` `1.100.0` non-`#[repr(C)]` ZST caller ->
`1.102.0` callee), recovering `0xCAFEBABE`, AND for `D1` (`sysv64` `1.99.1`
`Indirect + sret` SIMD caller <-> `1.100.0` `Direct(Vector)` callee) including
caller `sret` return buffer population! -/
theorem canary_p2_phys_shim_fixes_d3_and_d1_end_to_end :
    let abiD3_100 := classifyFnAbi .win64Msvc .r1_100_0 sigD3Win64ZstNonReprC
    let abiD3_102 := classifyFnAbi .win64Msvc .r1_102_0 sigD3Win64ZstNonReprC
    let planD3 := compileShimPlan abiD3_100 abiD3_102 sigD3Win64ZstNonReprC
    let valsD3 : List AbiVal := [.zst, .intScalar 8 (BitVec.ofNat 64 0xCAFEBABE)]
    let abiD1_99 := classifyFnAbi .sysv64 .r1_99_1 sigD1Simd
    let abiD1_100 := classifyFnAbi .sysv64 .r1_100_0 sigD1Simd
    let planD1 := compileShimPlan abiD1_99 abiD1_100 sigD1Simd
    let vecVal : AbiVal := .simd4F32 (BitVec.ofNat 128 0xDEADBEEFCAFEBABE0123456789ABCDEF)
    (match marshalArgs abiD3_100 valsD3 with
     | .ok fIn =>
       match execArgShim planD3 fIn with
       | .ok fBridged => unmarshalArgs abiD3_102 sigD3Win64ZstNonReprC.args fBridged = .ok valsD3
       | .error _ => False
     | .error _ => False) ∧
    (match marshalArgs abiD1_99 [vecVal] with
     | .ok fCaller =>
       match execArgShim planD1 fCaller with
       | .ok fCallee =>
         unmarshalArgs abiD1_100 sigD1Simd.args fCallee = .ok [vecVal] ∧
         match marshalRet fCallee abiD1_100.retMode vecVal with
         | .ok fCalleeOut =>
           match execRetShim planD1 fCaller fCalleeOut with
           | .ok fCallerOut => unmarshalRet abiD1_99.retMode sigD1Simd.ret fCallerOut = .ok vecVal
           | .error _ => False
         | .error _ => False
       | .error _ => False
     | .error _ => False) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Positive Canary `P3`: Verifies live `rustc` / `E2-6` `vectorcall` edge cases:
(a) `abi_vec_many6_simd` (`7 x F32x4`) spills arg 6 to `.directStack` and stays
`@@112 -> @@112` on `sysv64`, `win64Msvc`, and `i686SysV`;
(b) `sysv64` `vectorcall` `hfa2F64` breaks `@@8 -> @@16` (matching `x86_win64`);
(c) `sysv64` `vectorcall` ZST (`reprC = false` AND `reprC = true`) breaks `@@16 -> @@8`;
(d) `i686SysV` `vectorcall` `bigStruct 3` uses `byval` and stays `@@24 -> @@24`! -/
def sigVecMany6Simd : FnSig :=
  { conv := .vectorcall,
    args := [.simd4F32, .simd4F32, .simd4F32, .simd4F32, .simd4F32, .simd4F32, .simd4F32],
    ret := .simd4F32 }
def sigVecHfa2 : FnSig := { conv := .vectorcall, args := [.hfa2F64], ret := .hfa2F64 }
def sigVecZstRust : FnSig := { conv := .vectorcall, args := [.zst false, .intScalar 8], ret := .intScalar 8 }
def sigVecZstC : FnSig := { conv := .vectorcall, args := [.zst true, .intScalar 8], ret := .intScalar 8 }

theorem canary_p3_vectorcall_many6_hfa2_zst_and_i686_byval :
    (classifyFnAbi .sysv64 .r1_100_0 sigVecMany6Simd).symbolRule = .vectorcallAtAt 112 ∧
    fullAbiCompatible (classifyFnAbi .sysv64 .r1_100_0 sigVecMany6Simd)
                      (classifyFnAbi .sysv64 .r1_102_0 sigVecMany6Simd) = true ∧
    fullAbiCompatible (classifyFnAbi .win64Msvc .r1_100_0 sigVecMany6Simd)
                      (classifyFnAbi .win64Msvc .r1_102_0 sigVecMany6Simd) = true ∧
    fullAbiCompatible (classifyFnAbi .i686SysV .r1_100_0 sigVecMany6Simd)
                      (classifyFnAbi .i686SysV .r1_102_0 sigVecMany6Simd) = true ∧
    (classifyFnAbi .sysv64 .r1_100_0 sigVecHfa2).symbolRule = .vectorcallAtAt 8 ∧
    (classifyFnAbi .sysv64 .r1_102_0 sigVecHfa2).symbolRule = .vectorcallAtAt 16 ∧
    (classifyFnAbi .sysv64 .r1_100_0 sigVecZstRust).symbolRule = .vectorcallAtAt 16 ∧
    (classifyFnAbi .sysv64 .r1_102_0 sigVecZstRust).symbolRule = .vectorcallAtAt 8 ∧
    (classifyFnAbi .sysv64 .r1_100_0 sigVecZstC).symbolRule = .vectorcallAtAt 16 ∧
    (classifyFnAbi .sysv64 .r1_102_0 sigVecZstC).symbolRule = .vectorcallAtAt 8 ∧
    (classifyFnAbi .i686SysV .r1_100_0 sigD4BigStruct).symbolRule = .vectorcallAtAt 24 ∧
    (classifyFnAbi .i686SysV .r1_102_0 sigD4BigStruct).symbolRule = .vectorcallAtAt 24 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end VrustcFormal.F1_3
