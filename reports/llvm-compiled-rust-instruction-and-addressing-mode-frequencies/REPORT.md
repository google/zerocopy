# Instruction Mnemonic and Addressing-Mode Frequencies in LLVM-Compiled Rust Across Tier 1 Targets, Optimization Levels, and CPU Microarchitectures

## Summary

Sizing the formal ISA semantics and verified instruction selector/verifier for a
drop-in `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, LLVM 23.1.1
`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) replacement requires measuring how
many distinct machine instructions and addressing modes LLVM actually emits in
compiled Rust binaries across targets, optimization levels, and CPU feature
tiers. Disassembling **1,262,637 machine instructions** across the prebuilt
Rust `1.99.1` standard library archives (`libcore`, `liballoc`, `libstd`,
`libcompiler_builtins`) for all **8 Tier 1 targets**, plus a controlled 6-domain
Rust benchmark suite compiled across **6 optimization levels (`-Copt-level=0,1,2,3,s,z`)**
and **11 CPU microarchitecture targets (`x86-64` through `x86-64-v4`, `generic`,
`apple-m1`/`m3`/`m4`, and `neoverse-n1`/`v1`/`v2`)**, establishes four governing
facts:

1. **Steep Pareto concentration across all 8 Tier 1 standard libraries (`1,262,637` instructions):**
   - Across `libcore`, `liballoc`, `libstd`, and `libcompiler_builtins` combined,
     the top **10 mnemonics** account for **58.18%–70.74%** of all emitted
     instructions on every Tier 1 target, the top **25 mnemonics** cover
     **80.03%–88.07%**, the top **50 mnemonics** cover **92.03%–95.95%**, and
     the top **100 mnemonics** cover **97.85%–99.32%**.
   - Reaching **90% (`p90`)** cumulative instruction coverage requires only
     **42–44 mnemonics** on `x86_64` (`linux-gnu`, `windows-msvc`,
     `windows-gnu`), **31–34 mnemonics** on `aarch64` (`linux-gnu`,
     `apple-darwin`, `windows-msvc`), and **30–34 mnemonics** on 32-bit `i686`
     (`linux-gnu`, `windows-msvc`).
   - Reaching **99% (`p99`)** cumulative coverage requires **124–131 mnemonics**
     on `x86_64`, **91–108 mnemonics** on `aarch64`, and **95–107 mnemonics** on
     `i686`. The remaining 1% long tail (`251–330` total unique mnemonics per
     target) resides disproportionately in `libcompiler_builtins` (`115–260`
     unique mnemonics for soft-float, 128-bit division, and outline atomics) and
     SIMD string/collection routines in `libcore` (`128–203` unique mnemonics),
     whereas `liballoc` uses only **68–86 unique mnemonics** in total (`p99 =
     45–59`).
2. **Addressing-mode and operand-form distribution by architecture:**
   - **`x86_64` (`linux-gnu` / `windows-msvc` / `windows-gnu`):** Register-to-register
     GPR operations (`gpr_reg_to_reg`) represent **33.69%–35.61%** of sysroot
     instructions, followed by base+displacement memory accesses (`base_disp_mem`,
     `20.93%–21.97%`), register-immediate operations (`reg_imm`,
     `15.49%–16.34%`), direct/indirect branch and call targets
     (`branch_or_call_target`, `13.97%–16.89%`), RIP-relative memory addressing
     (`rip_relative_mem`, `2.89%–6.67%`, higher on ELF PIC than Windows COFF),
     scale-index-base (`sib_indexed_mem`, `3.23%–4.34%`), zero-operand
     instructions (`no_operands`, `2.08%–4.05%`), and SIMD register operations
     (`simd_reg_to_reg`, `1.44%–1.96%`).
   - **`aarch64` (`linux-gnu` / `apple-darwin` / `windows-msvc`):** Load/store
     RISC discipline concentrates **67.22%–68.41%** of all instructions into
     scalar register-to-register/immediate-shifted forms (`scalar_reg_to_reg`)
     and **21.98%–22.53%** into PC-relative branches and page-address generation
     (`pc_rel_branch_or_adrp`: `b`, `bl`, `b.<cond>`, `cbz`/`cbnz`, `tbz`/`tbnz`,
     `adrp`), leaving only **6.21%–6.69%** for explicit bracketed memory
     addressing (`base_imm_offset_mem` at `4.33%–4.59%` and scaled/register-offset
     or pre/post-indexed modes at `1.88%–2.17%`).
   - **`i686` (`linux-gnu` / `windows-msvc`):** With only 8 GPRs and stack-passed
     cdecl/stdcall arguments, `base_disp_mem` rises to **31.95%–34.47%** (exceeding
     `gpr_reg_to_reg` at `29.37%–30.64%`), and `movl` + `pushl` alone account for
     **40.0%–40.7%** of all emitted instructions in the entire standard library.
3. **Optimization-level transitions (`-Copt-level=0,1,2,3,s,z`):**
   - Moving from `-Copt-level=0` to `-Copt-level=1` reduces total instruction
     count on the 6-domain workload suite by **73.0%** on `x86_64` (`1,440` →
     `389`), **81.7%** on `aarch64` (`1,551` → `284`), and **75.3%** on `i686`
     (`2,768` → `684`).
   - At `-Copt-level=0`, stack-spill memory traffic dominates: `base_disp_mem`
     is **43.89%** on `x86_64` and **57.26%** on `i686` (`movq`/`movl` alone are
     36.7% and 54.6% of all instructions), while on `aarch64` unscaled stack
     loads/stores (`ldur`/`stur`, `213` instructions) and `ldr`/`str` (`348`
     instructions) dominate.
   - Moving from `-Copt-level=1` to `-Copt-level=2`/`3` triggers loop
     auto-vectorization and unrolling: `aarch64` `neon_or_sve_vector_arrangement`
     jumps from **0%** at `opt=1` to **11.08%** at `opt=2`/`3`, and `i686`
     SSE2 `simd_reg_to_reg` jumps from **1.17%** at `opt=1` to **6.64%** at
     `opt=3` (expanding unique mnemonics from `65` to `80`).
   - Size levels `-Copt-level=s` and `-Copt-level=z` suppress loop vectorization
     and unrolling, shrinking total instructions to **253–259** on `x86_64`
     (`57–59` unique mnemonics) and **214–224** on `aarch64` (`47` unique
     mnemonics, the smallest ISA surface of any configuration).
4. **CPU microarchitecture level shifts (`x86-64-v1..v4`, `apple-m1..m4`, `neoverse-n1/v1/v2`):**
   - On `x86_64` at `-Copt-level=3`, advancing from baseline `x86-64` (`v1`,
     SSE2) to `x86-64-v2` (SSE4.2/POPCNT) and `x86-64-v3` (AVX2/BMI2/FMA)
     replaces legacy SSE encodings (`movdqu`, `paddq`, `pxor`, `addsd`) with
     3-operand VEX encodings (`vmovdqu`, `vpaddq`, `vpxor`, `vfmadd213sd`,
     `vmaxsd`, `vminsd`) and BMI2 `shrxq`/`sarxq`, increasing unique mnemonics
     from **66 (`v1`)** to **82 (`v2`)** and **83 (`v3`)** and raising
     `simd_reg_to_reg` share from **4.35%** to **10.38%–11.06%**.
   - Advancing to `x86-64-v4` (AVX-512F/BW/DQ/VL) introduces EVEX mask-register
     operations (`vpcmpgtq`, `vpblendmq`, `vpmovsxwd`, `vpmuldq`, `vpbroadcastd`,
     `kmovd`), increasing total instructions from `424` to `500`, unique
     mnemonics to **87**, and `simd_reg_to_reg` share to **16.00%**.
   - On `aarch64` at `-Copt-level=3`, `apple-m1`, `apple-m3`, and `apple-m4`
     produce identical instruction counts (`352` instructions, `63` unique
     mnemonics, `p99 = 60`) for standard Rust code, while `neoverse-v1` (which
     enables SVE auto-vectorization via `cntd`, `whilelo`, `ld1w`, `st1w`,
     `smax`, `smin`, `mad`) expands unique mnemonics from **62 (`neoverse-n1` /
     `neoverse-v2`)** to **68 (`neoverse-v1`)** and raises vector-arrangement
     operand share from **10.00%** to **13.40%**.

## Applicability

These measurements apply to **Rust 1.99.1**
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) and its bundled **LLVM 23.1.1**
backend and `llvm-objdump` disassembler (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`)
across all 8 Tier 1 targets (`x86_64-unknown-linux-gnu`,
`aarch64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `aarch64-apple-darwin`,
`x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `aarch64-pc-windows-msvc`,
`i686-pc-windows-msvc`). Complete machine-readable tables are preserved in
`support/instruction_frequencies.json`.

## Findings

### 1. Tier 1 standard library instruction and coverage census (`1,262,637` instructions)

Basis: execution (`support/probe_inst_freq.py` -> `support/instruction_frequencies.json`)

Table 1 summarizes the instruction count, unique mnemonic count, cumulative
coverage percentiles, and per-crate breakdown across all 8 Tier 1 prebuilt
sysroot archives in Rust `1.99.1`.

| Tier 1 Target | Total Sysroot Instructions | Unique Mnemonics | Mnemonics for `p90` / `p95` / `p99` / `p99.9` | Top 10 / 25 / 50 / 100 Coverage (%) | Per-Crate Unique Mnemonics (`core` / `alloc` / `std` / `builtins`) |
| :--- | ---: | ---: | :---: | :---: | :---: |
| `x86_64-unknown-linux-gnu` | 160,773 | 285 | `42` / `65` / `130` / `215` | `60.08%` / `81.43%` / `92.42%` / `97.97%` | `199` / `86` / `166` / `219` |
| `x86_64-pc-windows-msvc` | 141,309 | 276 | `44` / `67` / `131` / `212` | `58.78%` / `80.87%` / `92.03%` / `97.85%` | `203` / `86` / `160` / `209` |
| `x86_64-pc-windows-gnu` | 155,401 | 273 | `43` / `65` / `124` / `203` | `58.18%` / `80.03%` / `92.33%` / `98.13%` | `202` / `86` / `170` / `192` |
| `aarch64-unknown-linux-gnu` | 147,594 | 259 | `31` / `46` / `91` / `163` | `63.69%` / `86.23%` / `95.75%` / `99.28%` | `129` / `68` / `108` / `214` |
| `aarch64-apple-darwin` | 137,981 | 330 | `34` / `51` / `108` / `226` | `63.22%` / `85.32%` / `94.98%` / `98.81%` | `161` / `70` / `145` / `260` |
| `aarch64-pc-windows-msvc` | 124,034 | 167 | `34` / `50` / `92` / `132` | `61.50%` / `84.15%` / `95.15%` / `99.32%` | `128` / `71` / `108` / `115` |
| `i686-unknown-linux-gnu` | 221,424 | 251 | `30` / `45` / `95` / `179` | `70.74%` / `88.07%` / `95.95%` / `99.14%` | `165` / `74` / `149` / `197` |
| `i686-pc-windows-msvc` | 174,121 | 290 | `34` / `52` / `107` / `197` | `67.53%` / `85.56%` / `94.77%` / `98.81%` | `169` / `74` / `180` / `183` |

Key architectural findings from Table 1:

1. **Why `aarch64-apple-darwin` has more unique mnemonics (`330`) than `aarch64-unknown-linux-gnu` (`259`) and `aarch64-pc-windows-msvc` (`167`):**
   - `aarch64-apple-darwin` defaults to `-Ctarget-cpu=apple-m1` (ARMv8.5-A +
     LSE atomics `cas`/`swp`/`ldadd`/`stadd` + FP16 + dotprod + RCPC `ldapr`),
     so `libcore` and `libstd` inline LSE atomic instructions directly, while
     `libcompiler_builtins` also compiles outline-atomic and FP128 helpers.
   - `aarch64-pc-windows-msvc` omits Unix-specific `compiler_builtins` routines
     and uses `167` unique mnemonics across the entire sysroot (`99.32%` covered
     by the top 100 mnemonics).
2. **Top 10 mnemonics per ISA family in the sysroot:**
   - **`x86_64-unknown-linux-gnu` (`160,773` total):** `movq` (`34,713`,
     `21.59%`), `movl` (`11,585`, `7.21%`), `leaq` (`9,802`, `6.10%`), `callq`
     (`7,824`, `4.87%`), `popq` (`6,148`, `3.82%`), `pushq` (`5,726`, `3.56%`),
     `jmp` (`5,673`, `3.53%`), `je` (`5,457`, `3.39%`), `cmpq` (`4,896`,
     `3.05%`), `addq` (`4,763`, `2.96%`).
   - **`aarch64-unknown-linux-gnu` (`147,594` total):** `mov` (`24,911`,
     `16.88%`), `add` (`14,454`, `9.79%`), `ldr` (`9,946`, `6.74%`), `cmp`
     (`8,488`, `5.75%`), `bl` (`7,725`, `5.23%`), `ldp` (`7,219`, `4.89%`),
     `stp` (`6,257`, `4.24%`), `b` (`5,189`, `3.52%`), `str` (`5,063`, `3.43%`),
     `sub` (`4,750`, `3.22%`).
   - **`i686-unknown-linux-gnu` (`221,424` total):** `movl` (`66,087`,
     `29.85%`), `pushl` (`22,423`, `10.13%`), `addl` (`12,250`, `5.53%`),
     `calll` (`10,239`, `4.62%`), `leal` (`9,831`, `4.44%`), `popl` (`9,341`,
     `4.22%`), `subl` (`7,838`, `3.54%`), `cmpl` (`7,043`, `3.18%`), `jmp`
     (`6,350`, `2.87%`), `je` (`5,230`, `2.36%`).

---

### 2. Addressing-mode and operand-form distribution across Tier 1 targets

Basis: execution (`support/instruction_frequencies.json`)

Table 2 breaks down the operand-form and addressing-mode shares across the
8 Tier 1 sysroots.

| Target | Reg-to-Reg (`gpr` / `scalar`) | Base+Disp / Imm-Offset Mem | Reg+Imm (`$imm` / `#imm`) | Branch / Call / PC-Rel (`adrp`) | RIP-Rel Mem (`(%rip)`) | SIB / Scaled-Reg Mem | Zero-Operand (`ret`/`nop`) | SIMD / Vector Reg |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `x86_64-unknown-linux-gnu` | 34.69% | 21.97% | 15.49% | 13.97% | 6.67% | 3.70% | 2.08% | 1.44% |
| `x86_64-pc-windows-msvc` | 35.61% | 20.93% | 16.34% | 14.05% | 3.81% | 3.23% | 4.05% | 1.96% |
| `x86_64-pc-windows-gnu` | 33.69% | 21.76% | 15.57% | 16.89% | 2.89% | 4.34% | 3.13% | 1.73% |
| `i686-unknown-linux-gnu` | 29.37% | 34.47% | 17.26% | 13.67% | 0.00% | 2.90% | 1.22% | 1.11% |
| `i686-pc-windows-msvc` | 30.64% | 31.95% | 18.65% | 11.99% | 0.00% | 2.75% | 2.60% | 1.41% |
| `aarch64-unknown-linux-gnu` | 67.22% | 4.52% | — (in scalar) | 22.40% | — | 2.17% | 2.74% | 0.95% |
| `aarch64-apple-darwin` | 68.41% | 4.59% | — (in scalar) | 22.53% | — | 2.02% | 2.45% | <0.05% (in scalar) |
| `aarch64-pc-windows-msvc` | 67.67% | 4.33% | — (in scalar) | 21.98% | — | 1.88% | 3.10% | 1.05% |

*(Note: In AT&T `llvm-objdump` output on `aarch64`, immediate operands without `#`
and unarranged `q`/`d` register moves are grouped under `scalar_reg_to_reg`,
whereas explicit vector lane arrangements `vN.16b`/`vN.4s`/`zN.s` are counted
under `neon_or_sve_vector_arrangement`.)*

---

### 3. Optimization-level matrix (`-Copt-level=0,1,2,3,s,z`)

Basis: execution (`support/probe_inst_freq.py` -> `support/instruction_frequencies.json`)

Compiling the 6-domain benchmark suite (SwissTable-style hash probing, UTF-8 +
CRC32 lexer state machine, saturating dot-product kernel, Horner FP64 polynomial
evaluation, `u128` decimal formatting, and `AtomicUsize` `compare_exchange_weak`
CAS loop) across all 6 optimization levels reveals how optimization reshapes
instruction selection:

| Target & Metric | `opt-level=0` | `opt-level=1` | `opt-level=2` | `opt-level=3` | `opt-level=s` | `opt-level=z` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: |
| **`x86_64-unknown-linux-gnu` Total Instructions** | 1,440 | 389 | 363 | 368 | 253 | 259 |
| `x86_64` Unique Mnemonics (`p90` / `p99`) | `71` (`21`/`57`) | `64` (`34`/`61`) | `67` (`37`/`64`) | `66` (`37`/`63`) | `59` (`34`/`57`) | `57` (`32`/`55`) |
| `x86_64` `base_disp_mem` / `gpr_reg_to_reg` / `simd` (%) | `43.9%` / `15.4%` / `1.9%` | `5.1%` / `49.9%` / `3.9%` | `6.3%` / `48.2%` / `4.1%` | `6.8%` / `48.1%` / `4.4%` | `4.4%` / `53.4%` / `2.8%` | `3.9%` / `55.6%` / `2.3%` |
| **`aarch64-unknown-linux-gnu` Total Instructions** | 1,551 | 284 | 343 | 348 | 224 | 214 |
| `aarch64` Unique Mnemonics (`p90` / `p99`) | `52` (`18`/`39`) | `53` (`32`/`51`) | `60` (`35`/`57`) | `60` (`35`/`57`) | `47` (`27`/`45`) | `47` (`28`/`45`) |
| `aarch64` `scalar_reg` / `branch_adrp` / `vector` (%) | `67.3%` / `27.5%` / `0.0%` | `75.7%` / `18.0%` / `0.0%` | `67.4%` / `14.0%` / `11.1%` | `67.2%` / `13.2%` / `10.9%` | `71.4%` / `19.2%` / `0.0%` | `70.6%` / `20.1%` / `0.0%` |
| **`i686-unknown-linux-gnu` Total Instructions** | 2,768 | 684 | 715 | 723 | 576 | 630 |
| `i686` Unique Mnemonics (`p90` / `p99`) | `70` (`19`/`52`) | `65` (`28`/`59`) | `80` (`38`/`73`) | `80` (`37`/`73`) | `63` (`27`/`58`) | `60` (`27`/`54`) |
| `i686` `base_disp_mem` / `gpr_reg_to_reg` / `simd` (%) | `57.3%` / `17.6%` / `0.8%` | `30.1%` / `35.4%` / `1.2%` | `28.0%` / `33.3%` / `6.6%` | `27.7%` / `33.2%` / `6.6%` | `30.2%` / `38.2%` / `1.4%` | `31.1%` / `38.1%` / `1.0%` |

---

### 4. CPU microarchitecture level matrix (`x86-64-v1..v4`, `apple-m1..m4`, `neoverse-n1/v1/v2`)

Basis: execution (`support/probe_inst_freq.py` -> `support/instruction_frequencies.json`)

Table 4 shows how `-Ctarget-cpu=<level>` at `-Copt-level=3` changes the emitted
instruction set and operand forms.

| CPU Level (`-Ctarget-cpu`) | Target Triple | Total Insts | Unique Mnemonics | `p90` / `p99` Mnemonics | Vector / SIMD Share (%) | Newly Activated ISA Extensions & Characteristic Mnemonics |
| :--- | :--- | ---: | ---: | :---: | ---: | :--- |
| `x86-64` (`v1` baseline) | `x86_64-unknown-linux-gnu` | 368 | 66 | `37` / `63` | 4.35% | Legacy 2-operand SSE2 (`movdqu`, `movdqa`, `paddq`, `pxor`, `psubd`, `addsd`, `mulsd`, `maxsd`, `minsd`) |
| `x86-64-v2` | `x86_64-unknown-linux-gnu` | 425 | 82 | `47` / `78` | 11.06% | SSE4.1/SSE4.2 (`pmovsxwd`, `pmuldq`, `pmaxsd`, `pminsd`, `blendvpd`, `pcmpgtq`) enabling wider vectorization |
| `x86-64-v3` | `x86_64-unknown-linux-gnu` | 424 | 83 | `49` / `79` | 10.38% | 3-operand VEX AVX/AVX2 + FMA + BMI2 (`vmovdqu`, `vpaddq`, `vpmuldq`, `vpmaxsd`, `vpminsd`, `vfmadd213sd`, `shrxq`) |
| `x86-64-v4` | `x86_64-unknown-linux-gnu` | 500 | 87 | `51` / `82` | 16.00% | EVEX AVX-512F/BW/DQ/VL (`vpcmpgtq %ymm, %ymm, %k1`, `vpblendmq`, `vpbroadcastd`, `vextracti128`, `kmovd`) |
| `generic` (ARMv8.0-A) | `aarch64-unknown-linux-gnu` | 348 | 60 | `35` / `57` | 10.92% | Baseline NEON (`ldp`/`stp q`, `smull.2d`, `smull2.2d`, `sqadd.4s`, `smax.4s`, `smin.4s`, `addp.2d`) + LL/SC (`ldaxr`/`stlxr`) |
| `apple-m1` / `m3` / `m4` | `aarch64-apple-darwin` | 352 | 63 | `37` / `60` | 10.80% | ARMv8.5-A LSE atomics (`casal`), `fmadd`, `fmaxnm`, `fminnm`, Darwin Mach-O alignment `nop`s |
| `neoverse-n1` / `neoverse-v2` | `aarch64-unknown-linux-gnu` | 380 | 62 | `36` / `59` | 10.00% | ARMv8.2-A / ARMv9.0-A LSE (`casal`) + NEON vector loops (`smull`, `sqadd`, `smax`, `smin`) |
| `neoverse-v1` | `aarch64-unknown-linux-gnu` | 403 | 68 | `39` / `64` | 13.40% | Scalable Vector Extension (SVE) predication (`cntd`, `whilelo p0.s`, `ptrue`, `ld1w`, `st1w`, `mad`, `smax z0.s, p0/m`) |

### 5. Minimum ISA-model coverage roadmap for a verified Rust backend

Combining the sysroot census (`Table 1`) with the optimization and CPU matrices
(`Tables 3–4`) yields concrete, tiered ISA modeling milestones for a verified
backend (`Goals 12, 18`):

1. **Scalar + ABI Core (~60 mnemonics per ISA — covers `-Copt-level=0,1,s,z` and ~92–95% of sysroot):**
   - **`x86_64` (~58 mnemonics):** Data movement (`movq`/`l`/`w`/`b`, `movabsq`,
     `movzbl`/`w`, `movsbl`/`w`/`q`, `leaq`, `pushq`, `popq`, `cmov*`), integer
     ALU (`add*`, `sub*`, `adc*`, `sbb*`, `imul*`, `mul*`, `div*`/`idiv*`,
     `inc*`, `dec*`, `neg*`, `not*`, `and*`, `or*`, `xor*`, `shl*`, `shr*`,
     `sar*`, `rol*`, `ror*`, `bswap*`, `lzcnt*`/`tzcnt*`/`popcnt*`), comparisons
     and flags (`cmp*`, `test*`, `set*`), control flow (`jmp`, `j<cc>`, `callq`,
     `retq`, `ud2`), scalar SSE2 FP (`movsd`/`ss`, `addsd`/`ss`, `subsd`/`ss`,
     `mulsd`/`ss`, `divsd`/`ss`, `ucomisd`/`ss`, `cvtsi2sd`/`ss`,
     `cvttsd2si`/`ss`, `xorpd`/`ps`), and atomics (`lock cmpxchg*`, `lock xadd*`,
     `xchg*`).
   - **`aarch64` (~48 mnemonics):** Moves and address generation (`mov`, `movz`,
     `movk`, `movn`, `adr`, `adrp`), loads/stores (`ldr`/`b`/`h`/`sb`/`sh`/`sw`,
     `ldur*`, `ldp`, `str`/`b`/`h`, `stur*`, `stp`), integer ALU (`add`/`adds`,
     `sub`/`subs`, `adc`, `sbc`, `madd`, `msub`, `mul`, `umulh`, `smulh`, `udiv`,
     `sdiv`, `and`/`ands`, `orr`, `eor`, `bic`, `orn`, `lsl`, `lsr`, `asr`,
     `ror`, `extr`, `clz`, `rbit`, `rev`, `sxt*`/`uxt*`, `csel`/`csinc`/`csinv`/`csneg`,
     `ccmp`), comparisons (`cmp`, `cmn`, `tst`), control flow (`b`, `bl`, `blr`,
     `br`, `ret`, `b.<cond>`, `cbz`/`cbnz`, `tbz`/`tbnz`, `brk`), scalar FP
     (`fmov`, `fadd`, `fsub`, `fmul`, `fdiv`, `fmadd`, `fcmp`, `fcsel`, `scvtf`,
     `ucvtf`, `fcvtzs`, `fcvtzu`), and atomics (`ldaxr`/`ldxr`, `stlxr`/`stxr`,
     `ldar`, `stlr`, `dmb`, plus LSE `cas*`, `swp*`, `ldadd*`, `ldclr*`,
     `ldeor*`, `ldset*`).
2. **Baseline Vector / Auto-Vectorizer Tier (+30–45 mnemonics per ISA — covers `-Copt-level=2,3` and ~99% of sysroot):**
   - Adding 128-bit SSE2/SSE4.2 (`x86_64-v1`/`v2`) or 256-bit VEX AVX2
     (`x86-64-v3`) on x86_64, and 128-bit NEON (`aarch64` `generic`/`apple-m1`),
     raises total modeled mnemonics to **~95–130 on `x86_64`** and **~90–108 on
     `aarch64`**, covering **>99%** of all emitted instructions.

## Boundaries

- **Mnemonic grouping vs. encoding forms:** `llvm-objdump` disassembles AT&T
  mnemonics (`movq`, `movl`, `ldr`, `add`), which distinguish operand widths on
  x86 via suffixes (`b`/`w`/`l`/`q`) while grouping register/immediate/memory
  encoding variants under the same mnemonic; our `operand_form_distribution`
  (`Table 2`) explicitly separates those addressing modes.
- **Crates.io multi-crate binary builds:** While the prebuilt Tier 1 sysroots
  provide `1,262,637` compiled instructions across `core`, `alloc`, `std`, and
  `compiler_builtins` and the 6-domain benchmark suite isolates `-Copt-level`
  and `-Ctarget-cpu` transitions, full cross-target compilation of all 3,680
  crates across 8 targets x 6 opt-levels exceeds the single-run build budget and
  is bounded by the sysroot + benchmark suites.

## Evidence

- **Rust 1.99.1 (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`) and LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
  - Prebuilt Tier 1 target sysroots (`lib/rustlib/<target>/lib/lib{core,alloc,std,compiler_builtins}-*.rlib`)
    across all 8 Tier 1 targets (`1,262,637` disassembled instructions).
  - Controlled 6-domain Rust workload compiled across 6 optimization levels (`0`,
    `1`, `2`, `3`, `s`, `z`) and 11 CPU microarchitectures (`x86-64`,
    `x86-64-v2`, `x86-64-v3`, `x86-64-v4`, `generic`, `apple-m1`, `apple-m3`,
    `apple-m4`, `neoverse-n1`, `neoverse-v1`, `neoverse-v2`).
- **Preserved support artifacts:**
  - `support/instruction_frequencies.json`: Complete machine-readable frequency
    tables, coverage percentiles (`p90`, `p95`, `p99`, `p99.9`), and addressing
    mode breakdowns across all 8 Tier 1 sysroots, 6 opt-levels, and 11 CPU
    levels.
  - `support/probe_inst_freq.py`: Reproducible disassembly and classification
    driver.

## Revalidation

Run `python3 support/probe_inst_freq.py` with a Rust toolchain that has the
8 Tier 1 `rust-std` components and `llvm-tools` installed to regenerate
`support/instruction_frequencies.json`.
