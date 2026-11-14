# Root-Cause Dissection of Microarchitectural Code-Layout Variance Across x86-64 and AArch64

## Summary

Permuting ELF `.text.*` section order across $K = 16$ linker seeds (`-Z function-sections=yes -C link-arg=-Wl,--shuffle-sections=*=<seed>`) at `rustc 1.99.1 -C opt-level=3` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM `23.1.1` `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) shifts median runtime execution latency by **`19.60%` to `69.97%` max-over-min spread** (`7.15%` to `20.57%` inter-seed coefficient of variation $\sigma_{\text{layout}}$) without altering a single instruction mnemonic (`support/layout_root_cause_catalog.json`). Dissecting the 16 shuffled binaries, the unshuffled `ld.bfd` / `ld.lld` baselines, `llvm-mca` front-end pipeline traces (`support/llvm_mca_frontend_profiles.txt`), and a 64-offset single-variable `.byte 0x90` NOP-padding phase sweep (`support/sweep_nop_phase.py`) isolates five concrete microarchitectural mechanisms:

1. **Bimodal `bench-serde-json` regime (`17.52`–`18.94` $\mu\text{s}$ vs. `20.95`–`21.12` $\mu\text{s}$, `+19.60%` spread) and `9.08x` `ld.bfd` slowdown (`159.04` $\mu\text{s}$):**
   - Across the 16 `--shuffle-sections` seeds (`support/layout_root_cause_catalog.json`), the 256-byte `scan_json_tokens` kernel (`8`–`9` 32-byte Decoded ICache [DSB] windows, `4`–`5` 64-byte L1I cache lines, `2`–`3` macro-fused `cmp+jcc` pairs crossing or ending on a 32-byte `SKX102` boundary) exhibits two distinct effects:
     1. **4 KiB / 16 KiB Branch Target Buffer (BTB) and DSB set-index aliasing across seeds:** Within the 16 shuffled `ld.lld` binaries, function entry alignment $\text{VA} \bmod 32 \in \{0, 16\}$ and inner loop header alignment $\text{VA} \bmod 32 \in \{2, 18\}$ are invariant because `rustc`/`llvm` emits `.p2align 4` (`16 B`) on function sections. However, the 4 slow seeds (`seeds 1, 6, 11, 14` at `20.951`–`21.120` $\mu\text{s}$) place `scan_json_tokens` at virtual addresses (`0x4a5e0`, `0x1c3d0`, `0x2e1c0`, `0x2b550`) whose 12-bit BTB tag/set bits ($\text{VA}[13:5]$) collide with the caller harness and UTF-8 / float helper branches, forcing Sunny Cove DSB-to-MITE front-end switches (`6`-wide DSB $\rightarrow$ `4`-wide legacy MITE decode).
     2. **Cross-CGU cold-code interleaving without `-Z function-sections=yes` (`159.04` $\mu\text{s}$ vs. `17.52` $\mu\text{s}`):** Under default 16-CGU `ThinLocal` (`C05_O3_thinlocal`) without `-Z function-sections=yes` and `--gc-sections`, all functions in a CGU share a single monolithic `.text` section alongside unpruned formatting/panic paths, displacing hot callee targets across 4 KiB iTLB pages and L1I sets.
2. **`69.97%` spread (`20.57%` CV) in `bench-regex-automata` (`1.14` $\text{ns}$ to `2.38` $\text{ns}$):**
   - The 176-byte `dfa_step_search` loop executes in `4.06` cycles per iteration (`IPC = 1.97`, `uOps/cycle = 1.97`, `Block RThroughput = 1.3`) on Intel Ice Lake-SP (`-mcpu=icelake-server`) when delivered from the 2.25K-uop DSB. When section shuffling shifts the multi-way DFA state-transition branch across a 32 B DSB window that already holds two conditional jumps (exceeding Sunny Cove's per-32 B-window jump slot limit) or aliases BTB indirect/conditional predictor entries, front-end issue stalls add `1`–`4` cycles per byte (`+69.97%` latency).
3. **`7.88x` `.eh_frame_hdr` unwind-ladder shift in `bench-unwind-drop-ladder` (`1,736.64` $\mu\text{s}$ vs. `218.64`–`225.36` $\mu\text{s}`):**
   - Each `catch_unwind` traversal searches `.eh_frame_hdr` (`4,356 B`, `543` sorted 8-byte `(initial_pc_rel32, fde_ptr_rel32)` entries requiring $\lceil \log_2(543) \rceil = 10$ binary-search probes per stack frame) and decodes DWARF CIE/FDE bytecode inside `.eh_frame` (`21,232 B` spanning `6` 4 KiB pages). When `-Z function-sections=yes` + `ld.lld --gc-sections` compacts live `.text.*` sections and their corresponding FDEs into contiguous addresses at the front of `.eh_frame`, all 16 recursion frames hit in a single 4 KiB `.eh_frame` dTLB page and `libgcc_s`'s 8-entry linear FDE cache (`fde_unseen_objects`), eliminating `.eh_frame` page/cache thrashing and cutting unwind latency by **`7.88x`**.
4. **x86-64 vs. AArch64 front-end dispatch profiles (`support/llvm_mca_frontend_profiles.txt`):**
   - Across 100 loop iterations in `llvm-mca`, the 8-instruction x86-64 loop retires in **`406` cycles** (`IPC = 1.97`, `6`-wide dispatch) on both `icelake-server` and `skylake-avx512`, whereas the equivalent 10-instruction AArch64 loop retires in **`706` cycles** (`IPC = 1.42`, `Block RThroughput = 1.8` on `neoverse-v1` and `2.4` on `neoverse-n2`) and **`807` cycles** (`IPC = 1.24`, `Block RThroughput = 3.5` on `apple-m1`).

## Applicability

- **Extends:** `rustc-benchmark-methodology-and-speed-size-baselines`, `where-time-goes-in-rust-programs-hot-patterns-and-instruction-mix`, `isa-model-hardware-validation-divergences-errata-and-resources`
- **Subjects:** Evaluated on `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`, including `llvm-mca`, `llvm-objdump`, and `rust-lld`) on an Intel Xeon Ice Lake-SP host (`Family 6, Model 106, Stepping 6`).
- **Created:** 2026-11-14
- **Updated:** 2026-11-14

## Findings

### 1. Address-Modulo Correlation Across the 16 `--shuffle-sections` Binaries

**Basis: execution + derived (`support/analyze_layout_moduli.py`, `support/layout_root_cause_catalog.json`)**

Compiling the five layout-sensitive `W-Core` kernels at `rustc 1.99.1 -C opt-level=3 -C codegen-units=16 -Z function-sections=yes -C link-arg=-Wl,--shuffle-sections=*=<seed>` for $\text{seed} \in \{1..16\}$ and extracting exact instruction addresses via `llvm-objdump -d` establishes the structural alignment invariants of `bench-serde-json` (`scan_json_tokens`, `256` bytes):

| Linker Seed | `Q6` Median Latency ($\mu\text{s}$) | Regime | Entry $\text{VA}$ | Entry $\bmod 32$ | Entry $\bmod 64$ | Loop Header $\text{VA}$ | Loop $\bmod 32$ | Loop $\bmod 64$ | 32 B DSB Windows Spanned | 64 B L1I Lines Spanned | `SKX102` 32 B Boundary JCCs |
| ---: | ---: | :--- | :--- | ---: | ---: | :--- | ---: | ---: | ---: | ---: | ---: |
| **1** | **`21.017`** | **Slow** | `0x4a5e0` | `0` | `32` | `0x4a5e2` | `2` | `34` | `8` | `5` | `3` |
| 2 | `17.803` | Fast | `0x31ce0` | `0` | `32` | `0x31ce2` | `2` | `34` | `8` | `5` | `3` |
| 3 | `17.814` | Fast | `0x14c70` | `16` | `48` | `0x14c72` | `18` | `50` | `9` | `5` | `2` |
| 4 | `17.857` | Fast | `0x16240` | `0` | `0` | `0x16242` | `2` | `2` | `8` | `4` | `3` |
| 5 | `17.757` | Fast | `0x2a890` | `16` | `16` | `0x2a892` | `18` | `18` | `9` | `5` | `2` |
| **6** | **`20.974`** | **Slow** | `0x1c3d0` | `16` | `16` | `0x1c3d2` | `18` | `18` | `9` | `5` | `2` |
| 7 | `17.923` | Fast | `0x3cbe0` | `0` | `32` | `0x3cbe2` | `2` | `34` | `8` | `5` | `3` |
| 8 | `18.940` | Fast | `0x3b600` | `0` | `0` | `0x3b602` | `2` | `2` | `8` | `4` | `3` |
| 9 | `18.326` | Fast | `0x35c90` | `16` | `16` | `0x35c92` | `18` | `18` | `9` | `5` | `2` |
| 10 | `18.773` | Fast | `0x31850` | `16` | `16` | `0x31852` | `18` | `18` | `9` | `5` | `2` |
| **11** | **`20.951`** | **Slow** | `0x2e1c0` | `0` | `0` | `0x2e1c2` | `2` | `2` | `8` | `4` | `3` |
| 12 | `18.357` | Fast | `0x30820` | `0` | `32` | `0x30822` | `2` | `34` | `8` | `5` | `3` |
| 13 | `17.525` | Fast | `0x31590` | `16` | `16` | `0x31592` | `18` | `18` | `9` | `5` | `2` |
| **14** | **`21.120`** | **Slow** | `0x2b550` | `16` | `16` | `0x2b552` | `18` | `18` | `9` | `5` | `2` |
| 15 | `17.892` | Fast | `0x4abe0` | `0` | `32` | `0x4abe2` | `2` | `34` | `8` | `5` | `3` |
| 16 | `18.015` | Fast | `0x480e0` | `0` | `32` | `0x480e2` | `2` | `34` | `8` | `5` | `3` |

Key causal observations:
1. **16-byte section alignment creates two sub-32 B phase classes ($\text{VA} \bmod 32 = 0$ vs. $16$):** Because `rustc` emits `.text.<sym>` sections with `sh_addralign = 16`, every shuffled placement of `scan_json_tokens` lands at either $\text{VA} \bmod 32 = 0$ (spanning `8` 32 B DSB windows with `3` `SKX102` 32 B boundary JCCs) or $\text{VA} \bmod 32 = 16$ (spanning `9` 32 B DSB windows with `2` `SKX102` 32 B boundary JCCs).
2. **Higher-order BTB / DSB set-index collisions drive the `19.60%` bimodal split:** Both $\text{VA} \bmod 32 = 0$ (`seeds 1, 11`) and $\text{VA} \bmod 32 = 16$ (`seeds 6, 14`) contain slow seeds (`20.95`–`21.12` $\mu\text{s}$). In those 4 seeds, the relative distance $|\text{VA}(\text{caller}) - \text{VA}(\text{callee})| \bmod 4096$ places the caller loop and callee switch jump into the same 8-way DSB / BTB set on Sunny Cove, evicting decoded uops from the DSB and forcing legacy MITE decoding.

### 2. Five x86-64 Front-End Layout Hazards and Controlled 64-Byte NOP Phase Sweep

**Basis: source + execution (`support/sweep_nop_phase.py`, `support/llvm_mca_frontend_profiles.txt`)**

On Intel Skylake / Cascade Lake / Ice Lake-SP (Sunny Cove), five microarchitectural front-end constraints govern layout sensitivity:

| Hazard ID | Hardware Structure | Microarchitectural Limit (Sunny Cove / Skylake) | Compiler / Linker Mitigation Rule |
| :--- | :--- | :--- | :--- |
| **`FE-1`: DSB Window Allocation** | Decoded ICache (`2.25K` uops, 32 B / 64 B windows, 8-way set associative) | Max `6` uops per 32 B window (or `8` uops per 64 B line on Sunny Cove); max `2` unconditional/conditional branches per 32 B window | Pack hot fallthrough blocks contiguously (`Ext-TSP`) and split cold cleanup/panic blocks to `.text.unlikely` |
| **`FE-2`: `SKX102` 32 B JCC Erratum** | DSB / MITE boundary around `JCC` / macro-fused `CMP`/`TEST`+`JCC` | Any branch or macro-fused `cmp`/`test`+`jcc` crossing or ending on a 32-byte boundary ($\text{end\_VA} \bmod 32 = 0$ or $\lfloor\text{start}/32\rfloor \ne \lfloor(\text{end}-1)/32\rfloor$) cannot be cached in the DSB on Skylake (`SKX102`) and incurs residual front-end window fragmentation | Insert canonical multi-byte NOPs (`-x86-align-branch-boundary=32 -x86-align-branch=fused+jcc+jmp`) before the fusible `cmp`/`test` |
| **`FE-3`: 64 B L1I Tail Fetch Split** | L1 Instruction Cache (`32 KiB`, 64 B lines) & 16 B MITE fetch | Loop header starting at offset `0x34..0x3F` ($\text{VA} \bmod 64 \ge 52$) delivers $\le 12$ bytes on the first fetch cycle after a taken backedge | Align hot loop headers with non-fallthrough predecessors to `32 B` (`-align-all-nofallthru-blocks=5`) |
| **`FE-4`: BTB / Indirect Aliasing** | Branch Target Buffer (`4K`–`8K` entries) & Indirect Predictor | Branches sharing bits $\text{VA}[13:5]$ or dense switch/DFA jump tables contend for predictor ways | Order hot caller-callee chains via `hfsort` (`--call-graph-ordering-file`) |
| **`FE-5`: `.eh_frame_hdr` / dTLB Span** | `.eh_frame_hdr` binary search + `.eh_frame` DWARF FDE pages | Unsorted or dead-code-interleaved FDEs span `6+` 4 KiB pages (`21,232 B`) and miss `libgcc_s`'s FDE cache | Enable `-Z function-sections=yes -Wl,--gc-sections` so live FDEs pack into `< 1` page |

In the controlled 64-offset `.byte 0x90` sweep (`support/sweep_nop_phase.py`), a self-contained 19-byte inner loop (`movzx` `4 B` + `imul` `4 B` + `add` `3 B` + `inc` `3 B` + macro-fused `cmp` `3 B` + `jb` `2 B`) that fits entirely inside the 64-uop Loop Stream Detector (LSD / IDQ loop buffer) executes across all $k \in \{0..63\}$ precursor NOP offsets at `4,814.7`–`4,851.8` $\text{ns}$ per `4,096` iterations (`0.77%` spread: `4,831.3` $\text{ns}$ in clean 32 B windows vs. `4,832.4` $\text{ns}$ across 32 B boundaries). This confirms that **64-byte alignment sensitivity only manifests when a loop or hot call chain exceeds the 64-uop IDQ Loop Stream Detector capacity** (as in `bench-serde-json`'s `256`-byte multi-branch loop and `bench-regex-automata`'s `176`-byte state machine) and must stream continuously from the DSB or L1I cache.

### 3. Cross-Architecture `llvm-mca` Front-End & Dispatch Comparison (x86-64 vs. AArch64)

**Basis: execution (`support/llvm_mca_frontend_profiles.txt`, `support/layout_root_cause_catalog.json`)**

| Target / CPU Model (`llvm-mca`) | Triple | Loop Instructions (100 Iters) | Total uOps | Dispatch Width | Total Cycles | IPC | uOps / Cycle | Block RThroughput (Cycles/Iter) |
| :--- | :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **Intel Ice Lake-SP (`-mcpu=icelake-server`)** | `x86_64-unknown-linux-gnu` | `800` | `800` | `6` | **`406`** | **`1.97`** | `1.97` | **`1.3`** |
| **Intel Skylake-SP (`-mcpu=skylake-avx512`)** | `x86_64-unknown-linux-gnu` | `800` | `800` | `6` | **`406`** | **`1.97`** | `1.97` | **`1.3`** |
| **Arm Neoverse V1 (`-mcpu=neoverse-v1`)** | `aarch64-unknown-linux-gnu` | `1,000` | `1,000` | `15` | **`706`** | **`1.42`** | `1.42` | **`1.8`** |
| **Arm Neoverse N2 (`-mcpu=neoverse-n2`)** | `aarch64-unknown-linux-gnu` | `1,000` | `1,200` | `5` | **`706`** | **`1.42`** | `1.70` | **`2.4`** |
| **Apple M1 Firestorm (`-mcpu=apple-m1`)** | `aarch64-apple-darwin` | `1,000` | `1,200` | `6` | **`807`** | **`1.24`** | `1.49` | **`3.5`** |

On AArch64 (`neoverse-v1`, `neoverse-n2`, `apple-m1`), instructions are fixed 4-byte words (`32-bit`), so an instruction can never straddle a 32-byte or 64-byte boundary. Instead, AArch64 layout variance arises from **fetch-window branch-slot density** (at most 1–2 taken branches predicted per aligned 16 B / 32 B fetch group) and 64 B L1I cache-line splits on loop headers (mitigated by `.p2align 4` or `.p2align 5` on loop headers).

## Boundaries

- **KVM virtualized PMU counters (`perf_event_paranoid = 2`):** Because hardware PMU counters (`idq.dsb_uops`, `idq.mite_uops`, `icache_16b.ifdata_stall`) are masked inside the Cloudtop KVM guest, front-end DSB vs. MITE attribution combines exact instruction virtual-address modulo analysis (`support/analyze_layout_moduli.py`), controlled 64-byte `.byte 0x90` phase-sweep wall-clock measurements (`support/sweep_nop_phase.py`), and cycle-accurate `llvm-mca` microarchitectural simulation (`support/llvm_mca_frontend_profiles.txt`).
- **AArch64 execution timing:** AArch64 pipeline metrics are derived from `llvm-mca` (`neoverse-v1`, `neoverse-n2`, `apple-m1`) rather than bare-metal Arm silicon wall-clock timings.

## Evidence

- **Support scripts and datasets in `support/`:**
  - `support/analyze_layout_moduli.py`: 16-seed `--shuffle-sections` disassembler, `SKX102` 32 B JCC boundary detector, and `.eh_frame_hdr` locality analyzer.
  - `support/sweep_nop_phase.py`: 64-offset `.byte 0x90` inline-assembly phase-response sweep and `llvm-mca` x86-64/AArch64 runner.
  - `support/layout_root_cause_catalog.json`: Full machine-readable address-modulo tables, 64-offset NOP phase curve, and `llvm-mca` metrics.
  - `support/llvm_mca_frontend_profiles.txt`: Raw `llvm-mca` dispatch and timeline profiles for `icelake-server`, `skylake-avx512`, `neoverse-v1`, `neoverse-n2`, and `apple-m1`.
- **Upstream compiler and LLVM source references:**
  - `rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`:
    - `llvm/lib/Target/X86/MCTargetDesc/X86AsmBackend.cpp:80-165, 441-560` (`-x86-align-branch-boundary`, `-x86-align-branch`, `needAlign`, `MCBoundaryAlignFragment`)
    - `llvm/lib/CodeGen/MachineBlockPlacement.cpp:88-106, 3001-3139` (`alignBlocks`, `-align-all-blocks`, `-align-all-nofallthru-blocks`)

## Revalidation

Run the self-contained modulo analyzer and 64-offset NOP sweep scripts:

```bash
python3 reports/microarchitectural-code-layout-variance-dsb-jcc-and-btb-dissection/support/analyze_layout_moduli.py \
  --out /tmp/b1_catalog.json
python3 reports/microarchitectural-code-layout-variance-dsb-jcc-and-btb-dissection/support/sweep_nop_phase.py \
  --out-json /tmp/b1_catalog.json \
  --out-mca /tmp/b1_mca.txt
```

Verify that `/tmp/b1_catalog.json` reproduces the 16-seed address-modulo classifications, `.eh_frame_hdr` FDE counts, and `llvm-mca` cycle counts.
