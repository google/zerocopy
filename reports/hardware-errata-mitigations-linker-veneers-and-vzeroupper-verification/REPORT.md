# Silicon Errata Mitigations, Linker Veneer Synthesis, and `vzeroupper` Verification

## Summary

Empirically reproducing the four principal silicon errata workarounds and microarchitectural transition passes in `rustc 1.99.1` and `rust-lld` (`LLVM 23.1.1`) (`-x86-branches-within-32B-boundaries` for Intel Skylake `SKX102`, `-Ctarget-feature=+fix-cortex-a53-835769`, `rust-lld --fix-cortex-a53-843419` executed under `qemu-aarch64`, and x86 AVX-to-SSE `vzeroupper` in [`support/reproduce_errata_and_veneers.py`](support/reproduce_errata_and_veneers.py) and [`support/errata_veneer_measurements.json`](support/errata_veneer_measurements.json)), and mechanizing their semantics and soundness proofs in Lean `v4.34.1` ([`support/ErrataAndVeneerVerification/ErrataAndVeneerVerification.lean`](support/ErrataAndVeneerVerification/ErrataAndVeneerVerification.lean), `223` lines, `917,120`-byte `.olean`, `0` `sorry`, `0` `native_decide`) establishes:

1. **Intel Skylake Server Erratum `SKX102` (`X86AsmBackend.cpp` 32-Byte Boundary JCC Alignment):**
   - In `skx102_hot_branches`, unmitigated `rustc 1.99.1 -Copt-level=3` places a macro-fused `cmpq %rcx, %r11; jbe 0x50` pair at bytes `0x3b..0x40`, ending on the 32-byte boundary `0x40` (`1` `SKX102` DSB/LSD hazard site).
   - Passing `-Cllvm-args=-x86-branches-within-32B-boundaries` inserts a 5-byte `nopl (%rax,%rax)` (`0f 1f 44 00 00`) at `0x3b..0x40`, shifting `cmpq; jbe` to `0x40..0x45` and shrinking the trailing loop-alignment NOP at `0x4d` from 8 bytes to 3 bytes (`0f 1f 00`) so total object size remains `1,080` bytes with `0` 32-byte boundary hazards.
   - In Lean 4, `skx102_padding_eliminates_hazard` proves that for any branch or macro-fused pair of length $1 \le \text{len} \le 15$, advancing `offset` by `skx102PadBytes offset len` guarantees `crossesOrEndsAt32B (offset + pad) len = false`.
2. **Arm Cortex-A53 Erratum `835769` (`AArch64A53Fix835769.cpp` 64-Bit Multiply-Accumulate After Memory Op):**
   - On `aarch64-unknown-linux-gnu`, `a53_835769_mac_after_mem` compiles without mitigation to adjacent `ldr x9, [x0]; str x1, [x0]; madd x0, x9, x2, x3`.
   - Enabling `-Ctarget-cpu=cortex-a53 -Ctarget-feature=+fix-cortex-a53-835769` inserts `nop` (`d503201f`) at offset `0x8` between `str x1, [x0]` (`0x4`) and `madd x0, x9, x2, x3` (`0xc`).
   - In Lean 4, `unmitigated_835769_faults` and `fix835769_sound_and_safe` prove that `[.str64 src, .madd64 dst rn rm ra]` triggers `.erratum835769Fault` under the hardware-hazard semantics `runA64Safe`, whereas `[.str64 src, .nop, .madd64 dst rn rm ra]` completes with `.ok stFinal` and produces the exact register file of `runA64Ideal`.
3. **Arm Cortex-A53 Erratum `843419` (`lld/ELF/Arch/AArch64.cpp` Page-End `ADRP` Linker Veneer Synthesis):**
   - Placing `str x1, [sp, #-0x10]!` (`0x211ff4`), `adrp x2, 0x200000` (`0x211ff8`, page offset `0xff8`), `ldr x1, [sp], #0x10` (`0x211ffc`, page offset `0xffc`), and `ldr x0, [x2, #0x120]` (`0x212000`) triggers `rust-lld --fix-cortex-a53-843419`.
   - Rather than relocating `adrp x2` itself, `rust-lld` (`AArch64Err843419Patcher`) leaves `adrp x2, 0x200000` in place at `0x211ff8` and overwrites the dependent load at `0x212000` with `b 0x212044 <__CortexA53843419_212000>`, where the synthesized thunk executes `ldr x0, [x2, #0x120]` (`0x212044`) followed by `b 0x212004` (`0x212048`). Both unpatched and patched ELF binaries execute cleanly under `qemu-aarch64` (`exit 0`, returning `0x1122334455667788`).
   - In Lean 4, `patch843419_lld_dependent_ldr_veneer_sound` proves `lld`'s dependent-load thunk observational equivalence (`rfl`), and `patch843419_relocated_adrp_veneer_sound` proves that linkers (such as GNU `bfd`/`gold`) that instead relocate `ADRP` to a veneer page `veneerPageIdx` preserve `evalAdrpPage` when re-centering `imm21 := targetPageIdx - veneerPageIdx`.
4. **x86 AVX-to-SSE Transition Cleanliness (`X86VZeroUpper.cpp` `vzeroupper` Insertion):**
   - In `avx2_caller_into_sse`, `rustc 1.99.1 -Copt-level=3` emits 256-bit `vmovups (%rdi), %ymm0; vaddps %ymm0, %ymm0, %ymm0; vmovups %ymm0, (%rsi)` followed immediately at offset `0xd` by `vzeroupper` (`c5 f8 77`) before `callq *(%rip)` to `sse_legacy_callee`.
   - In Lean 4, `vzeroupper_preserves_xmm_and_clears_dirty` proves over `X86VecState` that inserting `vzeroupper` between 256-bit `YMM` writers and legacy `SSE` instructions preserves all 128-bit `xmmLow` registers bit-for-bit (`stMit.xmmLow = stUnmit.xmmLow`) while clearing `upperDirty` from `true` to `false`.

## Applicability

- **Extends:** `isa-model-hardware-validation-divergences-errata-and-resources`, `verified-minimach-ext-tsp-layout-and-loop-jcc-alignment`, `verified-assemblers-encoders-linkers-and-object-format-models`, `target-features-implications-detection-and-abi-effects`
- **Subjects Examined:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`);
  - `rust-lang/llvm-project` `23.1.1-rust-1.99.1-stable` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, including `rust-lld` and `llvm-objdump`);
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`);
  - `qemu-aarch64` (`11.1.2`).

## Findings

### 1. Empirical Binary Disassembly and Linker Veneer Measurements (`rustc 1.99.1` & `rust-lld`)

`Basis: execution (support/reproduce_errata_and_veneers.py, support/errata_veneer_measurements.json)`

| Erratum / Microarchitectural Pass | Target & Flag Invoked | Unmitigated Machine Code | Mitigated / Patched Machine Code | Verified Invariant & Size Impact |
| :--- | :--- | :--- | :--- | :--- |
| **Intel `SKX102`** (JCC / Macro-Fused Pair on 32B Boundary) | `x86_64-unknown-linux-gnu` `-Cllvm-args=-x86-branches-within-32B-boundaries` | `0x3b: cmpq %rcx, %r11` (`49 39 cb`), `0x3e: jbe 0x50` (`76 10`, ends at `0x40`) | `0x3b: nopl (%rax,%rax)` (`0f 1f 44 00 00`), `0x40: cmpq %rcx, %r11`, `0x43: jbe 0x50` | 32B boundary hazards reduced from `1` to `0`; object size unchanged (`1,080` B) via downstream NOP absorption (`0x4d`). |
| **Arm Cortex-A53 `835769`** (64-bit MAC after `LDR`/`STR`) | `aarch64-unknown-linux-gnu` `-Ctarget-feature=+fix-cortex-a53-835769` | `0x0: ldr x9, [x0]`, `0x4: str x1, [x0]`, `0x8: madd x0, x9, x2, x3` | `0x0: ldr x9, [x0]`, `0x4: str x1, [x0]`, `0x8: nop` (`d503201f`), `0xc: madd x0, x9, x2, x3` | `1` `nop` (`+4` bytes) separates `str` from 64-bit `madd`. |
| **Arm Cortex-A53 `843419`** (`ADRP` at page offset `0xFF8`/`0xFFC`) | `aarch64-unknown-linux-gnu` `rust-lld --fix-cortex-a53-843419` | `0x211ff4: str x1, [sp, #-0x10]!`, `0x211ff8: adrp x2, 0x200000`, `0x211ffc: ldr x1, [sp], #0x10`, `0x212000: ldr x0, [x2, #0x120]` | `0x212000: b 0x212044 <__CortexA53843419_212000>` $\to$ `0x212044: ldr x0, [x2, #0x120]`, `0x212048: b 0x212004` | Synthesizes 8-byte linker thunk `__CortexA53843419_212000`; `qemu-aarch64` returns `exit 0` (`0x1122334455667788`). |
| **x86 AVX $\to$ SSE `vzeroupper`** (`X86VZeroUpper.cpp`) | `x86_64-unknown-linux-gnu` `#[target_feature(enable = "avx2")]` | (Without `vzeroupper`: `upperDirty = true` stalls legacy SSE transitions) | `0x9: vmovups %ymm0, (%rsi)`, `0xd: vzeroupper` (`c5 f8 77`), `0x10: callq *(%rip)` | Emits `vzeroupper` before calling non-AVX `extern "C"` functions while preserving `%xmm0` scalar argument. |

---

### 2. Lean `v4.34.1` Mechanized Soundness Theorems (`ErrataAndVeneerVerification.lean`)

`Basis: execution (support/ErrataAndVeneerVerification/ErrataAndVeneerVerification.lean)`

| Theorem Name | Erratum / Pass | Mechanized Statement | Proof Method |
| :--- | :--- | :--- | :--- |
| `unmitigated_835769_faults` | Cortex-A53 `835769` | `runA64Safe [.str64 src, .madd64 dst rn rm ra] st = .erratum835769Fault` | `rfl` |
| `fix835769_sound_and_safe` | Cortex-A53 `835769` | `∃ stFinal, runA64Safe [.str64 src, .nop, .madd64 dst rn rm ra] st = .ok stFinal ∧ stFinal.regs = (runA64Ideal [.str64 src, .madd64 dst rn rm ra] st).regs` | `refine ⟨..., rfl, rfl⟩` |
| `patch843419_relocated_adrp_veneer_sound` | Cortex-A53 `843419` (GNU `bfd`/`gold` `ADRP` thunk) | `0 ≤ origOff < 4096 → 0 ≤ veneerOff < 4096 → evalAdrpPage pcVeneer (targetPageIdx - veneerPageIdx) = evalAdrpPage pcOrig (targetPageIdx - origPageIdx) ∧ evalAdrpPage pcVeneer immVeneer = targetPageIdx * 4096` | Integer Euclidean division/modulo arithmetic (`omega`) |
| `patch843419_lld_dependent_ldr_veneer_sound` | Cortex-A53 `843419` (`rust-lld` `LDR` thunk) | `runLldPatched843419 st pcAdrp pcVeneer immPages lo12 = runUnpatched843419 st pcAdrp immPages lo12` | `rfl` |
| `skx102_padding_eliminates_hazard` | Intel Skylake `SKX102` | `1 ≤ len → len ≤ 15 → crossesOrEndsAt32B (offset + skx102PadBytes offset len) len = false` | Case split on `crossesOrEndsAt32B offset len` + `omega` |
| `vzeroupper_preserves_xmm_and_clears_dirty` | x86 AVX-to-SSE `vzeroupper` | `stMit.xmmLow = stUnmit.xmmLow ∧ stMit.upperDirty = false ∧ stUnmit.upperDirty = true` | `refine ⟨rfl, rfl, rfl⟩` |

## Boundaries

- **Cycle-Accurate Microarchitectural Pipeline Timing (`not modeled` in Lean):** The Lean 4 models capture architectural register/memory state plus abstract hazard predicates (`lastWasMemOp`, `crossesOrEndsAt32B`, and `upperDirty`) rather than cycle-accurate DSB/MITE/L1D pipeline stalls.
- **Prefix-Padding Variant of `SKX102` (`-x86-pad-max-prefix-size`):** By default, `-x86-branches-within-32B-boundaries` uses architectural NOPs (`nopl`); CS/DS segment-override prefix padding requires an explicit non-zero `-x86-pad-max-prefix-size` flag.

## Evidence

- **Primary Upstream Sources (`rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
  - `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp` (`alignBranchesBegin` / `alignBranchesEnd` for Intel `SKX102`).
  - `llvm/lib/Target/AArch64/AArch64A53Fix835769.cpp` (`runOnMachineFunction` inserting `NOP` between `LDR`/`STR` and 64-bit `MADD`/`MSUB`).
  - `lld/ELF/Arch/AArch64.cpp` (`AArch64Err843419Patcher` and `Patch843419Section` synthesizing `__CortexA53843419_<addr>` veneers).
  - `llvm/lib/Target/X86/X86VZeroUpper.cpp` (AVX-to-SSE dirty-upper-YMM dataflow analysis and `VZEROUPPER` insertion).
- **Preserved Support Artifacts:**
  - [`support/ErrataAndVeneerVerification/ErrataAndVeneerVerification.lean`](support/ErrataAndVeneerVerification/ErrataAndVeneerVerification.lean): Lean `v4.34.1` mechanization of `835769`, `843419`, `SKX102`, and `vzeroupper`.
  - [`support/reproduce_errata_and_veneers.py`](support/reproduce_errata_and_veneers.py): End-to-end compilation, linking, disassembly, and `qemu-aarch64` verification script.
  - [`support/errata_veneer_measurements.json`](support/errata_veneer_measurements.json): Disassembly traces, 32B boundary hazard counts, and `qemu-aarch64` exit codes.

## Revalidation

```bash
python3 reports/hardware-errata-mitigations-linker-veneers-and-vzeroupper-verification/support/reproduce_errata_and_veneers.py
anneal-lean-run --mode build --concurrency 4 -- lake --dir reports/hardware-errata-mitigations-linker-veneers-and-vzeroupper-verification/support/ErrataAndVeneerVerification build
```

Verify that `reproduce_errata_and_veneers.py` exits with `0` (`mitigated_32b_boundary_hazards == 0`, `nop_inserted_between_str_and_madd == true`, `qemu_aarch64_patched_veneer_exit_code == 0`, `vzeroupper_count == 1`) and `lake build` succeeds with `0` warnings and `0` `sorry`.
