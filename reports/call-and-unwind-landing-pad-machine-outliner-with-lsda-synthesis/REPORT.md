# Call- and Unwind-Landing-Pad Machine Outliner with `.eh_frame`/LSDA and `.pdata`/`.xdata` Synthesis

## Summary

Lifting the leaf-only (`mayTrapOrUnwindCall = false`) boundary of
`reports/verified-machine-outliner-and-cross-function-tail-merging/` unlocks
machine outlining for the call-heavy sequences—diverging cold panic calls,
repeated non-diverging `call`/`bl` chains, and shared drop-cleanup landing
pads—that dominate residual `-Oz` `.text` size in Rust crates:

1. **Up to `53.03%` `.text` Reduction (`47.38%` Net Loadable Size Reduction)
   Across All 8 Tier 1 Targets:**
   On the 12-function checked-pipeline workload in
   `support/verified_call_and_unwind_outliner.py` (`-C opt-level=z -C panic=unwind`),
   leaf-only outlining (`allow_calls = False`) achieves `0.0%` `.text` reduction
   on `x86_64-unknown-linux-gnu`, `x86_64-pc-windows-gnu`, and
   `x86_64-pc-windows-msvc` because every repeated basic-block window contains a
   `callq` instruction. Enabling `OutlinerUnwindThunkCert` (`allow_calls = True`)
   reduces `.text` by **`43.14%`** on `x86_64-unknown-linux-gnu` (`32.74%` net
   loadable reduction after `.eh_frame` + `.gcc_except_table`), **`41.65%`** on
   `x86_64-pc-windows-msvc` (`37.65%` net loadable reduction), **`53.03%`** on
   `aarch64-unknown-linux-gnu` (`47.38%` net loadable reduction vs. `38.13%`
   leaf-only), **`48.39%`** on `aarch64-pc-windows-msvc`, **`45.73%`** on
   `aarch64-apple-darwin`, **`23.34%`** on `i686-unknown-linux-gnu`, and
   **`24.99%`** on `i686-pc-windows-msvc`.
2. **Live `std::panic::catch_unwind` Verification Through Synthesized Outlined
   Call-Thunk FDEs (`x86_64` and `i686`):**
   Executing `support/verified_call_and_unwind_outliner.py` compiles and runs
   live unwinding binaries on both `x86_64-unknown-linux-gnu` and
   `i686-unknown-linux-gnu` in which `caller_with_drops` holds three active RAII
   `Guard` values (`_g1`, `_g2`, `_g3`) and invokes `may_panic_callee` through
   `outlined_callseq_thunk` (with synthesized `.cfi_startproc` /
   `.cfi_adjust_cfa_offset` unwind metadata and zero LSDA attached to the thunk).
   Both normal return (`ok_val = 42`) and `std::panic::catch_unwind` recovery
   execute all three caller destructors in exact LIFO order
   (`UNWIND_OK:normal=42,lifo_drops=321`).
3. **Mechanized Soundness of 16-Byte Stack Alignment, `+16` Displacement
   Lifting, and 2-Stage Thunk-to-Caller LSDA Unwinding in Lean `v4.34.1`:**
   `support/VerifiedUnwindThunkOutliner.lean` proves (`0` `sorryAx`) three core
   theorems:
   - `outlined_callseq_sp_align_16`: if `sp % 16 = 0` before `callq OUTLINED_CALLSEQ_k`,
     then after `callq` (`-8`) and the thunk's `subq $8, %rsp` alignment
     prologue (`-8`), `(sp - 8 - 8) % 16 = 0` holds before the inner `callq callee`;
   - `outline_callseq_normal_and_unwind_sim`: for any non-negative caller stack
     slot displacement `disp ≥ 0` and any `CalleeOutcome` (`normalReturn retVal`
     or `raiseUnwind excPtr`), executing `runOutlinedCallSeq` with lifted stack
     displacement `disp + 16` and synthesized FDE `outlinedCallSeqFde` (`CFA = sp + 16`,
     `RA = [CFA - 8]`) produces the exact same `UnwindMachState` (including
     caller LSDA landing-pad dispatch) as `runInlineCallSeq`; and
   - `outline_diverging_panic_thunk_sim`: outlining diverging panic calls into
     `OUTLINED_PANIC_k` entered via `call` with `outlinedPanicThunkFde`
     (`CFA = sp + 8`, `RA = [CFA - 8]`) unwinds directly to the caller's exact
     `callSiteRetPc` and `.gcc_except_table` cleanup landing pad.

## Applicability

- **Subjects examined:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`),
    specifically `-C opt-level=z -C panic=unwind` codegen and `libunwind` /
    `std::panic::catch_unwind` personality dispatch.
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`),
    specifically `llvm/lib/CodeGen/MachineOutliner.cpp`, `llvm-mc`, and
    `llvm-size`.
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Scope:** Call-inclusive machine outlining (`OutlinerUnwindThunkCert`) and
  per-thunk unwind metadata synthesis (`.eh_frame` FDEs, Mach-O `__unwind_info`,
  and COFF `.pdata`/`.xdata`) across all 8 Tier 1 targets.

## Findings

### 1. ABI Frame-Alignment and Unwind-Metadata Contract for Outlined Call Thunks

Basis: source + execution

When an outlined candidate window contains an inner function call (`callq`,
`calll`, or `bl`), the outlined helper `OUTLINED_CALLSEQ_k` is no longer a leaf
function and must satisfy three target-ABI and unwinder invariants:

1. **16-Byte Stack Alignment Before Inner Calls:**
   - On `x86_64` (SysV and Win64), `rsp` is 16-byte aligned before the caller
     executes `callq OUTLINED_CALLSEQ_k`, which pushes the 8-byte caller return
     address (`rsp % 16 = 8`). `OUTLINED_CALLSEQ_k` therefore emits an 8-byte
     alignment prologue `subq $8, %rsp` (`.cfi_adjust_cfa_offset 8` on ELF;
     `UWOP_ALLOC_SMALL 8` on Win64) before executing the inner `callq callee`,
     and `addq $8, %rsp` before `retq`, restoring `(rsp - 16) % 16 = 0`
     (`outlined_callseq_sp_align_16`).
   - On `aarch64` (AAPCS64, Darwin, and Windows ARM64), `bl OUTLINED_CALLSEQ_k`
     clobbers `x30` (`lr`) without modifying `sp`; `OUTLINED_CALLSEQ_k` saves
     the caller's link register while preserving 16-byte `sp` alignment via
     `str x30, [sp, #-16]!` (`.cfi_def_cfa_offset 16; .cfi_offset w30, -16` on
     ELF; `alloc_s 16` + `save_reg_x x30, #[sp, #-16]!` on Windows ARM64) and
     restores it via `ldr x30, [sp], #16; ret`.
2. **Two-Stage Unwind Transparency Without Duplicating Caller LSDAs:**
   When `callee` unwinds inside `OUTLINED_CALLSEQ_k`, `OUTLINED_CALLSEQ_k`'s
   synthesized FDE has `lsda = none` (zero `.gcc_except_table` bytes added per
   thunk) and simply describes how to pop the thunk's 16-byte frame (`CFA = sp + 16`,
   `RA = [CFA - 8]` on `x86_64`; `CFA = sp + 16`, `X30 = [CFA - 16]` on
   `aarch64`). Once the unwinder steps out of `OUTLINED_CALLSEQ_k`, the restored
   instruction pointer `rip` equals the caller's `callq OUTLINED_CALLSEQ_k`
   return PC (`callSiteRetPc`), which falls inside the caller's existing
   `.gcc_except_table` LSDA call-site range (`cs_start .. cs_start + cs_len`)
   and dispatches to the caller's existing cleanup landing pad `cs_lp`.
3. **Caller Stack-Slot Displacement Lifting (`+16`):**
   As mechanized in `outline_callseq_normal_and_unwind_sim`, any caller
   `[rsp + disp]` stack-slot read (`disp ≥ 0`) inside an outlined `x86_64`
   call thunk is lifted by `+16` (`[rsp + disp + 16]`), addressing
   `(sp - 16) + (disp + 16) = sp + disp` without aliasing the pushed return
   address at `sp - 8`.

### 2. Quantitative Evaluation Across All 8 Tier 1 Targets

Basis: execution

Running `support/verified_call_and_unwind_outliner.py` across all 8 Tier 1
targets on the 12-function checked-pipeline crate (`-C opt-level=z -C panic=unwind`)
yields the following `.text` and total loadable (`.text` + unwind + LSDA) byte
counts (`support/call_outliner_8target_results.json`):

| Target | Baseline `.text` (B) | Leaf-Only `.text` (B) | Leaf-Only `.text` Reduction | Call-Outlined `.text` (B) | Call-Outlined `.text` Reduction | Net Loadable Reduction | Call Thunks / Sites Outlined |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| `x86_64-unknown-linux-gnu` | `2,997` | `2,997` | `0.00%` | `1,704` | **`43.14%`** | **`32.74%`** | `5` / `60` |
| `aarch64-unknown-linux-gnu` | `3,892` | `2,408` | `38.13%` | `1,828` | **`53.03%`** | **`47.38%`** | `10` / `120` |
| `i686-unknown-linux-gnu` | `3,608` | `2,766` | `23.34%` | `2,766` | **`23.34%`** | **`28.14%`** | `5` / `60` |
| `x86_64-pc-windows-gnu` | `2,939` | `2,939` | `0.00%` | `1,731` | **`41.10%`** | **`37.20%`** | `4` / `48` |
| `x86_64-pc-windows-msvc` | `2,903` | `2,903` | `0.00%` | `1,694` | **`41.65%`** | **`37.65%`** | `4` / `48` |
| `i686-pc-windows-msvc` | `3,370` | `2,528` | `24.99%` | `2,528` | **`24.99%`** | **`24.99%`** | `5` / `60` |
| `aarch64-pc-windows-msvc` | `3,844` | `2,360` | `38.61%` | `1,984` | **`48.39%`** | **`44.84%`** | `9` / `108` |
| `aarch64-apple-darwin` | `3,604` | `2,332` | `35.29%` | `1,956` | **`45.73%`** | **`45.73%`** | `8` / `96` |

## Boundaries

- **Position-independent GOT/PC-relative addressing on `i686` (`_GLOBAL_OFFSET_TABLE_`):**
  On `i686-unknown-linux-gnu`, PIC call sequences that compute `%ebx` via a
  per-function `.L0$pb` PC-thunk cannot be outlined across functions without
  normalizing the GOT base offset; `is_outlineable_inst` conservatively rejects
  candidate windows referencing `%ebx`, `got`, or `.l0$pb`.
- **Win64 SEH funclet outlining (`CleanupPad` / `CatchSwitch`):**
  While `OutlinerUnwindThunkCert` outlines call sequences whose callers use
  Win64 `.pdata`/`.xdata` unwind tables (`x86_64-pc-windows-msvc`,
  `x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`), outlining instructions
  *inside* a Windows SEH funclet body (`?dtor$...`) requires preserving the
  funclet's `EstablisherFrame` (`rdx`/`x1`) pointer and is left out of scope.

## Evidence

- `support/VerifiedUnwindThunkOutliner.lean` — Standalone Lean 4 (`v4.34.1`)
  mechanization proving `outlined_callseq_sp_align_16`,
  `outline_callseq_normal_and_unwind_sim`, and
  `outline_diverging_panic_thunk_sim` (`0` `sorryAx`).
- `support/verified_call_and_unwind_outliner.py` — 8-target call-outlining
  prototype and live `std::panic::catch_unwind` verification harness on
  `x86_64-unknown-linux-gnu` and `i686-unknown-linux-gnu`.
- `support/call_outliner_8target_results.json` — Complete 8-target `.text` and
  net loadable byte reduction metrics and live unwind execution results.

## Revalidation

```bash
~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  support/VerifiedUnwindThunkOutliner.lean

python3 support/verified_call_and_unwind_outliner.py \
  --out /tmp/call_outliner_8target_results.json
```
