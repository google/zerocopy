# Sub-Register Lane Aliasing (`ArchRegLaneSemantics`) and Read-Only Load Rematerialization (`RematLoadCert`) in `RegAllocCert`

## Summary

Extends the post-allocation register-allocator translation-validation certificate checker (`RegAllocCert`) to width-indexed physical sub-register lanes (`ArchRegLaneSemantics`: x86 8/16/32/64-bit GPRs including high-byte `%ah..%dh` vs. `REX` prefix constraints, legacy SSE vs. VEX/EVEX vector upper-lane zeroing, and AArch64 `wN`/`xN` + NEON lane inserts) and five verified rematerialization origins (`RematLoadCert`: `constI`, `frameAddr`, `rodataLoad`, `immutableArgLoad`, and `unmodifiedSpillSlot`), mechanized in `294` lines of self-contained Lean `v4.34.1` (`343` total lines, `0` `sorry`, `0` `native_decide`) and evaluated across `66,249` disassembled `libcore` instructions and `8` high-register-pressure workloads (`66.46%` additional spill-store reduction over constant-only rematerialization).

## Applicability

- **Subjects and pinned revisions:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`): prebuilt `libcore` object corpus (`x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`) and backend register-allocation lowering.
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`): x86-64/i686 and AArch64 sub-register operand encoding and `llvm-objdump` instruction census.
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`): kernel-checked proofs in [support/VerifiedSubRegAndRematCert.lean](support/VerifiedSubRegAndRematCert.lean) (`860.49 ms` verification time).
- **Upstream foundation:** Closes both explicit boundaries in `verified-regalloc2-spill-and-parallel-move-certificate-checker` (`X1`), which modeled each physical register `PReg` as an atomic full-width 64-bit slot (`PReg := Nat`) and restricted rematerialization to integer constants (`Inst.constI`).

## Findings

### 1. Empirical Census of Sub-Register Lanes in `rustc 1.99.1` `libcore`

To quantify why a flat full-width `PReg` model is insufficient for machine-code translation validation, [support/evaluate_subreg_and_remat.py](support/evaluate_subreg_and_remat.py) disassembles all object files in `rustc 1.99.1`'s prebuilt `libcore` on `x86_64-unknown-linux-gnu` (`34,045` instructions) and `aarch64-unknown-linux-gnu` (`32,204` instructions) ([support/subreg_remat_metrics.json](support/subreg_remat_metrics.json)):

| Target & `libcore` Corpus | Total Instructions | 8-Bit Low (`%al..%r15b`) | 8-Bit High (`%ah..%dh`) | 16-Bit (`%ax..%r15w`) | 32-Bit Zero-Extending (`%eax..%r15d` / `w0..w30`) | 64-Bit Full (`%rax..%r15` / `x0..x30`) | Vector (`%xmm` / `b,h,s,d` / `v,q`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `34,045` | `2,565` (`7.53%`) | `14` (`0.04%`) | `507` (`1.49%`) | `7,722` (`22.68%`) | `16,765` (`49.24%`) | `975` (`2.86%`) |
| `aarch64-unknown-linux-gnu` | `32,204` | — (uses `wN`) | — | — (uses `wN`) | `10,274` (`31.90%`) | `16,423` (`51.00%`) | `1,357` (`4.21%`) |

Over `31.7%` of all GPR-referencing instructions on `x86_64` and `31.9%` on `aarch64` operate on sub-64-bit register views, including `14` occurrences of high-byte `%ah..%dh` sub-registers in `x86_64` `libcore`.

### 2. Mechanized Hardware Sub-Register Lane Semantics (`ArchRegLaneSemantics`)

#### 2.1 GPR Write-Merge vs. Zero-Extension Laws (`writeGprLane` & `extractGprLane`)

On x86-64 and AArch64, sub-register writes obey asymmetric hardware update rules that we verify both on live hardware (`X86_SUBREG_LAWS_OK` and `AARCH64_SUBREG_LAWS_OK` in [support/evaluate_subreg_and_remat.py](support/evaluate_subreg_and_remat.py)) and in Lean 4 ([support/VerifiedSubRegAndRematCert.lean](support/VerifiedSubRegAndRematCert.lean)):

```lean
structure Gpr64Word where
  b0   : BitVec 8    -- bits [7:0]   (%al / wN[7:0])
  b1   : BitVec 8    -- bits [15:8]  (%ah / wN[15:8])
  w1   : BitVec 16   -- bits [31:16] (upper half of %eax / wN[31:16])
  hi32 : BitVec 32   -- bits [63:32] (upper 32 bits of %rax / xN[63:32])
  deriving DecidableEq, Repr, Inhabited

def writeGprLane (old : Gpr64Word) (lane : GprLane) (val : Gpr64Word) : Gpr64Word :=
  match lane with
  | .Lo8       => { old with b0 := val.b0 }
  | .Hi8_NoRex => { old with b1 := val.b1 }
  | .Lo16      => { old with b0 := val.b0, b1 := val.b1 }
  | .Lo32_Zext => { b0 := val.b0, b1 := val.b1, w1 := val.w1, hi32 := 0#32 }
  | .Full64    => val
```

This decomposition captures three critical register-allocation invariants proved in [support/VerifiedSubRegAndRematCert.lean](support/VerifiedSubRegAndRematCert.lean):

1. **8-Bit Low/High Disjoint Lane Non-Interference (`gprWritePreservesLane_sound`):** Writing `Lo8` (`%al`, `[7:0]`) and `Hi8_NoRex` (`%ah`, `[15:8]`) on the same physical register `preg` preserves the other 8-bit lane (`gprWritePreservesLane .Lo8 .Hi8_NoRex = true` and `gprWritePreservesLane .Hi8_NoRex .Lo8 = true`), allowing two concurrent 8-bit `VReg`s to inhabit `%al` and `%ah`.
2. **32-Bit Write Implicit Upper-Half Clobber (`lo32_zext_zeroes_hi32` & `bug_eax_clobbers_ah_rejected`):** Writing `Lo32_Zext` (`%eax` or `w0`) zeroes `hi32` (`[63:32]`) and overwrites both `b0` (`%al`) and `b1` (`%ah`). Allocating `v1` to `(%rax, .Hi8_NoRex)` while `v2` writes `(%rax, .Lo32_Zext)` is deterministically rejected by `subRegLocNonInterfering` (`= false`).
3. **x86-64 `REX` Prefix vs. `%ah..%dh` Encoding Legality (`checkRexHi8Compat` & `rex_ah_conflict_rejected`):** In x86-64 machine code, register indices `4..7` in an 8-bit operand decode as `%ah, %ch, %dh, %bh` *only* when no `REX` prefix (`0x40..0x4F`) is present; if any operand in the instruction requires a `REX` prefix (`pregIdx >= 8`, `lane == .Full64`, or low-byte `%spl, %bpl, %sil, %dil`), indices `4..7` decode as `%spl..%dil` instead of `%ah..%bh`. `checkRexHi8Compat` enforces this hardware constraint and rejects illegal combinations such as `movb %ah, %r8b` or `movb %dil, %ah` (`rex_ah_conflict_rejected`).

#### 2.2 Vector Sub-Register Upper-Lane Zeroing (`writeVecLane`)

In [support/VerifiedSubRegAndRematCert.lean](support/VerifiedSubRegAndRematCert.lean) (§3), `Vec512Word` models 512-bit `ZMM` / 256-bit `YMM` / 128-bit `XMM` and AArch64 NEON `V` registers across six write modes (`VecLaneWriteMode`), and theorem `vex128_zeroes_upper_vs_legacy_sse_preserves_upper` proves:
- Legacy x86 SSE 128-bit instructions (`Vec128_LegacySseMerge`, e.g. `movaps %xmm0, %xmm1`) preserve `ymm1` (`[255:128]`), whereas VEX/EVEX 128-bit instructions (`Vec128_VexOrNeonZero`, e.g. `vmovaps %xmm0, %xmm1`) unconditionally zero `[511:128]`.
- On AArch64, scalar FP/SIMD instructions (`Scalar32_ZeroUpper`, e.g. `fmov s0, w1`) zero bits `[127:32]`, whereas single-lane NEON element inserts (`NeonIns32_Lane1`, e.g. `ins v0.s[1], w2`) update only lane `s1` (`[63:32]`) while preserving `s0, s2, s3` (`[31:0]` and `[127:64]`), matching our live `qemu-aarch64` hardware probe (`lo64=0x222200001111 hi64=0x0`).

### 3. Read-Only Memory & Frame-Address Load Rematerialization (`RematLoadCert`)

In `verified-regalloc2-spill-and-parallel-move-certificate-checker` (`X1`), `Inst.remat` only accepted integer immediate constants (`constI`), forcing the register allocator to emit stack spill stores (`Inst.spill`) and reloads (`Inst.reload`) for frame addresses (`lea reg, [rbp - off]`), `.rodata` constant-pool loads (`mov reg, [rip + .LCPI]`), and incoming caller stack arguments.

#### 3.1 Five Verified Rematerialization Origins (`RematOrigin`)

In [support/VerifiedSubRegAndRematCert.lean](support/VerifiedSubRegAndRematCert.lean) (§5), we define `RematOrigin` with five certificate classes and a decidable validator `checkRematOriginValidAcrossWrites`:

```lean
inductive RematOrigin where
  | constI              (val : Int)
  | frameAddr           (slotOff : Int)
  | rodataLoad          (symId : Nat) (byteOff : Nat)
  | immutableArgLoad    (paramIdx : Nat)
  | unmodifiedSpillSlot (slotId : Nat)
  deriving DecidableEq, Repr, Inhabited
```

Theorem `checkRematLoadCert_sound` proves that for any sequence of intervening stack spill writes `writes : List (Nat × Int)`, whenever `checkRematOriginValidAcrossWrites orig (writes.map Prod.fst) = true`, evaluating `evalRematOrigin (applySpillWriteList env writes) orig` produces the exact value `evalRematOrigin env orig` computed at the original SSA definition point.

#### 3.2 Spill-Store Reduction Across `8` High-Register-Pressure Workloads

Evaluating `RematLoadCert` across the `8` high-register-pressure `W_core` kernels (`48..80` simultaneously live `VReg`s) in [support/evaluate_subreg_and_remat.py](support/evaluate_subreg_and_remat.py) ([support/subreg_remat_metrics.json](support/subreg_remat_metrics.json)) yields:

| Workload | Live `VReg`s | Unoptimized Spill Stores | `constI`-Only Spill Stores (`X1`) | Eliminated by `frameAddr` | Eliminated by `rodataLoad` | Eliminated by `immutableArgLoad` | `RematLoadCert` Spill Stores | Additional Spill-Store Reduction over `constI` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `W1_serde_json_escape_scan` | `54` | `18` | `14` | `5` | `3` | `2` | `4` | `71.43%` |
| `W2_regex_dfa_step_unrolled` | `62` | `24` | `18` | `7` | `4` | `3` | `4` | `77.78%` |
| `W3_hashbrown_probe_insert` | `48` | `15` | `12` | `5` | `2` | `2` | `3` | `75.00%` |
| `W4_deflate_lz77_match_window` | `74` | `31` | `25` | `8` | `6` | `4` | `7` | `72.00%` |
| `W5_sha256_compress_schedule` | `68` | `28` | `26` | `4` | `8` | `3` | `11` | `57.69%` |
| `W6_ed25519_field_mul_reduce` | `80` | `35` | `32` | `6` | `7` | `5` | `14` | `56.25%` |
| `W7_format_float_dragonbox` | `58` | `21` | `17` | `5` | `5` | `2` | `5` | `70.59%` |
| `W8_btree_node_split_rebalance` | `52` | `19` | `14` | `6` | `1` | `2` | `5` | `64.29%` |
| **Total (`8` workloads)** | — | **`191`** | **`158`** | **`46`** | **`36`** | **`23`** | **`53`** | **`66.46%` (`72.25%` vs. unoptimized)** |

## Boundaries

1. **x87 `ST(0)..ST(7)` rotating stack register file and MMX (`%mm0..%mm7`) aliasing:** This report mechanizes architectural GPR sub-lanes (`Lo8`, `Hi8_NoRex`, `Lo16`, `Lo32_Zext`, `Full64`) and SSE/AVX/NEON vector sub-lanes (`XMM`/`YMM`/`ZMM` and `bN`/`hN`/`sN`/`dN`/`vN`/`qN`). Legacy x87 stack-top relative addressing (`ST(i)`) and MMX/x87 tag-word aliasing are not used by `Verified Rust` integer/SSE/NEON codegen.
2. **Heap-read rematerialization across aliasing stores:** `RematLoadCert` permits memory-load rematerialization only from provably immutable segments (`rodataLoad` in `.rodata`, `immutableArgLoad` in read-only incoming caller stack parameter slots) or stack spill slots (`unmodifiedSpillSlot s`) guarded by the decidable certificate check `checkRematOriginValidAcrossWrites` proving zero intervening writes to `s`. General heap loads are never rematerialized.
3. **AArch64 SVE scalable vector length (`Z0..Z31` beyond 128-bit NEON):** AArch64 vector lane semantics are mechanized for fixed 128-bit NEON (`V0..V31` / `Q0..Q31`) and scalar `B`/`H`/`S`/`D` views; scalable SVE predicate and vector registers are outside the fixed-width `Vec512Word` model.

## Evidence

- **Lean 4 mechanization ([support/VerifiedSubRegAndRematCert.lean](support/VerifiedSubRegAndRematCert.lean)):** `343` total lines (`294` non-comment code lines), `8` theorems (`extractGprLane_writeGprLane_same`, `gprWritePreservesLane_sound`, `lo32_zext_zeroes_hi32`, `rex_ah_conflict_rejected`, `vex128_zeroes_upper_vs_legacy_sse_preserves_upper`, `checkSubRegLiveInterference_sound`, `bug_eax_clobbers_ah_rejected`, `checkRematLoadCert_sound`), `0` `sorry`, `0` `native_decide`, `#eval checkAllM6 = true`, verified in `860.49 ms`.
- **Empirical probe ([support/evaluate_subreg_and_remat.py](support/evaluate_subreg_and_remat.py) and [support/subreg_remat_metrics.json](support/subreg_remat_metrics.json)):** Audits `66,249` `libcore` instructions across `x86_64` and `aarch64`, verifies hardware lane-merge laws natively and under `qemu-aarch64`, and benchmarks `RematLoadCert`.

## Revalidation

```bash
python3 support/evaluate_subreg_and_remat.py
```
