# Page-Aligned SIMD Over-Reads, Demonic Hardware Granules, and Early-Exit Search Equivalence

## Summary

Production byte-scanning routines (`glibc` `memchr-avx2.S`, `strlen-avx2.S`, and `sysdeps/aarch64/memchr.S`) accept an arbitrary unpadded byte slice `(ptr, len)`—the exact memory layout of a plain safe Rust `&[u8]`—align the pointer down to a power-of-two vector boundary (`p_aligned = ptr & !(2^k - 1)`), execute aligned SIMD loads (`vmovdqa`, `ldr q`) that intentionally read **before `ptr` and/or past `ptr + len`** inside the enclosing hardware protection granule, mask off out-of-bounds lanes (`shrx`/`lsr`, `bzhi`), and return early on the first match via `vpmovmskb` + `tzcnt` (`rbit` + `clz` on AArch64). Verifying such routines soundly against a safe Rust reference function requires replacing strict byte-exact `memaccess_inbounds` and fixed-stride loop combinators (`prolog_unroll_epilog_equiv`) with a granule-parameterized demonic load contract and a variable-stride early-exit simulation law:

1. **Exact Architectural Soundness Envelope and Four Sharp Failure Modes (`Basis: normative + source + execution + derived`):**
   - **Granule containment (`2^k <= 2^granuleBits`):** An aligned $2^k$-byte non-volatile RAM load at `p_aligned = alignDown k a` never crosses a $2^{\text{granuleBits}}$-byte hardware protection boundary whenever $k \le \text{granuleBits}$ and at least one authorized byte $a \in [\text{ptr}, \text{ptr} + \text{len})$ lies inside $[p_{\text{aligned}}, p_{\text{aligned}} + 2^k)$. Across all `4,096 × 130 = 532,480` `(offset, len)` pairs (`offset ∈ 0..4096`, `len ∈ 0..129`, `3,145,472` live calls in `82.76 ms` surrounded by `PROT_NONE` guard pages and `needle`-poisoned slack in [`support/probe_x86_overread_sanitizers_and_cse.py`](support/probe_x86_overread_sanitizers_and_cse.py)), x86-64 32-byte aligned `vmovdqa` (`k = 5 <= 12`) achieves `0` faults and `0` mismatches, whereas unaligned `vmovdqu` on `len = 1` at `page + 4095` immediately faults with `SIGSEGV` (`signal = 11`).
   - **Dual `len == 0` traps:** Omitting the upfront `if slice.is_empty() { return None; }` guard causes `SIGSEGV` (`signal = 11`) in **two** distinct safe-Rust cases: (a) canonical `&[]` (`NonNull::dangling() == 0x1`, where `0x1 & -32 == 0x0`), and (b) a valid non-dangling end-of-page empty subslice `&page_buf[4096..4096]`, whose pointer equals the adjacent `PROT_NONE` guard page `G2` (`G2 & -32 == G2`). Checking `!ptr.is_null()` alone is unsound.
   - **Armv8.5-A MTE 16-byte tag-granule failure (`G_arch = 16 < load_size = 32`):** Live execution of a static `#![no_std]` AArch64 binary under `qemu-aarch64 -cpu max` (`11.1.2`, [`support/probe_aarch64_mte_granules.py`](support/probe_aarch64_mte_granules.py)) with `PR_MTE_TCF_SYNC` proves empirically that 32-byte aligned `ldp q0, q1, [ptr & !31]` faults synchronously with **`SIGSEGV` / `SEGV_MTESERR` (`si_code = 9`)** both when over-reading forward into `[base + 16, base + 32)` (`fault_offset = 16, fault_ptr_tag = 1`) and when `ptr & !31` steps *backward* from `[base + 16, base + 24)` into `[base, base + 16)` (`fault_offset = 0, fault_ptr_tag = 2`), whereas 16-byte aligned NEON `bic algn, ptr, #15; ldr q, [algn]` (`k = 4 <= 4`, matching `glibc` `sysdeps/aarch64/memchr.S:60-86`) passes all `3,856` tag-flanked checks with `0` faults. Masking with a 48-bit VA mask (`ptr & 0x0000_ffff_ffff_fff0`) strips the MTE tag `[59:56]` to `0` and faults immediately (`si_code = 9, fault_ptr_tag = 0`).
   - **Sanitizer (`ASan`/`TSan`) and LLVM `-C opt-level=3` CSE seams (`rustc 1.99.1` & `1.102.0-nightly`):**
     - Under `-Zsanitizer=address`, `core::arch::x86_64::_mm256_load_si256` aborts on stack and heap redzones (`rc = 1`)—and **still aborts inside `#[sanitize(address = "off")]`** because LLVM refuses to inline `sanitize_address`-attributed `core::core_arch` `_mm256_load_si256` into a non-sanitized caller—whereas inline `asm!` `vmovdqa` (`rc = 0`) and direct `*algn` inside `#[sanitize(address = "off")]` (`rc = 0`) emit zero ASan checks. Furthermore, `AddressSanitizer::instrumentUnusualSizeOrAlignment` (`AddressSanitizer.cpp:1841-1848`) checks **only** endpoints `p` and `p + 31` on 32-byte `<4 x i64>` loads, silently missing poisoned interior bytes `[p + 8 .. p + 24)` (`rc = 0`).
     - Under `-Zsanitizer=thread`, `ThreadSanitizer::getMemoryAccessFuncIndex` (`ThreadSanitizer.cpp:788-794`) handles only `8..128`-bit accesses (`kNumberOfAccessSizes = 5`) and **returns `-1` for all `256`-bit (`AVX2`), `512`-bit (`AVX-512`), and scalable vector loads**: `_mm_load_si128` (`16 B`) emits `@__tsan_read16` and catches concurrent neighbor writes (`rc = 66`), whereas `_mm256_load_si256` (`32 B`) and `asm!` emit **zero** `__tsan_read*` calls (`rc = 0`), letting an off-by-one `asm!` mask leak `69,079 / 150,000` concurrent neighbor writes with zero TSan warnings.
     - Under `-C opt-level=3`, `options(pure, readonly, nostack)` drops `sideeffect` in LLVM IR (`call ... asm inteldialect`), allowing LLVM GVN/EarlyCSE to prove `y: &mut [u8; 16]` `noalias`es `x: &[u8; 16]` in the same 32-byte chunk and **eliminate the second `vmovdqa` (`2 -> 1`)** across `y[0] = needle`. This CSE is 100% sound when `asm!` is slack-oblivious (`[-1, -1]` vs. fresh `-1`), but produces a live miscompilation/inconsistency witness (`[-1, -1]` CSE'd vs. `16` fresh, and `[-1, 16]` under `options(readonly)` without `pure`) when the mask has an off-by-one bug.
2. **Granule-Parameterized `DemonicGranuleLoad` & 1-Safety vs. 2-Safety Split (`Basis: derived + execution`):**
   - Mechanized in Pass-1 Lean `v4.34.1` ([`support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean`](support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean), `44` theorems, `0` `sorryAx`, `0` `._unsafe_rec`, checked in `2.47 s`), `GranuleLoadAdmissible granuleBits authBase authLen k alignedAddr` unifies x86-64 4 KiB pages (`granuleBits = 12`), AArch64 16B MTE (`granuleBits = 4`), and strict byte-exact / MMIO bounds (`granuleBits = 0`, `demonicGranuleLoad_zero_recovers_strict_inbounds`) in one rule. Every out-of-slice lane returns a **fresh per-load demonic nondeterministic byte** `demon step lane` with stripped provenance (`none`), soundly abstracting `MaybeUninit` padding, unexposed sibling `AllocId`s, and concurrent neighbor writes simultaneously.
   - `TotalMirAsmDemonicEquiv` holds iff `asm` never traps, satisfies **`DemonicSlackOblivious`** (`∀ q d1 d2, asm q d1 = asm q d2`), and matches `ref` on `zeroDemon` (`demonic_equiv_iff_slack_oblivious`). Crucially, `glibc`'s unmasked fast-path branch (`if rawMask == 0 { skip } else { check_masked }`) **preserves 1-safety `DemonicSlackOblivious` yet violates 2-safety `LeakTrace` non-interference** when a caller's secret stack variable shares the 32-byte chunk (`unmasked_fastpath_1safety_vs_2safety_leaktrace`); constant-time search kernels must mask slack *before* branching.
3. **Variable-Stride Early-Exit Search Equivalence (`early_exit_simd_search_equiv`) & `CpuFeatures.bmi1` Hazard (`Basis: source + execution + derived`):**
   - In `glibc` `memchr-avx2.S:100-116` (`L(first_vec_x0)`), `tzcntl %eax, %eax; cmpl %eax, %edx; jle L(null)` relies on `BMI1` returning `tzcnt(0) = 32 >= len`. Without `BMI1`, `F3 0F BC` decodes as `bsfl`, which on Intel/AMD hardware leaves `%eax = 0` unmodified on a zero mask, causing `cmpl %eax, %edx` (`1 > 0`) to return a **false match `Some(0)`** (`canary4_bsf_zero_mask_got = 0`, mechanized in `bmi1_tzcnt_vs_bsf_zero_hazard`).
   - Theorem `early_exit_simd_search_equiv` (and `simd_overread_memchr_total_demonic_equiv`) discharges the complete 4-stage aligned-overread SIMD search (empty-slice guard $\to$ misaligned `shrx`+`bzhi` prolog $\to$ $2^k$-aligned main loop $\to$ `bzhi` epilog + `tzcntW` first-set-bit index) against byte-by-byte `memchrRef` for all `k <= granuleBits`, all `(ptr, len)`, and all demonic schedules `demon`.

## Applicability

This report governs formal memory-model rules, compiler/sanitizer interactions, target-granule constraints, and deductive loop-equivalence proofs for inline (`core::arch::asm!`), naked (`naked_asm!`), and external `.S` SIMD search routines operating on unpadded Rust slices (`&[u8]`, `&str`, `&[T]` where `T` is plain byte/integer data).

### Examined Subjects and Their Roles

| Subject | Pinned Identity | Role in Investigation |
| :--- | :--- | :--- |
| **`rustc` `1.99.1`** | `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67` | Executed natively on `x86_64-unknown-linux-gnu` (`532,480`-pair guard-page harness, `-C opt-level=3` CSE/GVN IR & ASM) and cross-compiled static `#![no_std]` MTE binaries to `aarch64-unknown-linux-gnu` |
| **`rustc` `1.102.0-nightly`** | `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | Executed `-Zsanitizer=address`, `-Zsanitizer=thread`, `#[sanitize(address = "off")]`, and `-C opt-level=3` CSE/GVN probes |
| **The Rust Reference** | `rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | Normative specification of `asm!` `options(pure, readonly, nostack)` and FFI memory access rules (`r[asm.rules.mem-same-as-ffi]`) |
| **LLVM (`llvm-project`)** | `llvm/llvm-project@63b8d2fd94ba3b1a80023dae7139949dd5be6b78` | Primary source inspection of `ThreadSanitizer.cpp:120-125, 781-798` (`getMemoryAccessFuncIndex`) and `AddressSanitizer.cpp:1821-1850` (`instrumentUnusualSizeOrAlignment`) |
| **GNU C Library (`glibc`)** | `bminor/glibc@04e750e75b73957cf1c791535a3f4319534a52fc` | Primary source audit of `sysdeps/x86_64/multiarch/{memchr-avx2.S, strlen-avx2.S}` and `sysdeps/aarch64/{memchr.S, multiarch/strlen_asimd.S}` |
| **`BurntSushi/memchr` (`2.8.3`)** | `BurntSushi/memchr@5fdb40c054e1fff359a2f7bdf7f87a13b34b465d` | Primary source contrast (`src/arch/generic/memchr.rs:143-230`, `src/arch/x86_64/avx2/memchr.rs:179-205`, `src/vector.rs:138-192`) for strict in-bounds Rust `core::arch` SIMD |
| **`simdutf`** | `simdutf/simdutf@177945073a2e44f6ef252aa2b9cf1ecb8e4d2ab0` | Primary source contrast (`src/generic/find.h:6-43`, `src/icelake/icelake_find.inl.cpp:1-85`, `src/arm64/arm_find.cpp:1-100`) for scalar-prolog and AVX-512 `_mm512_maskz_loadu_epi8` search |
| **Anneal verifier** | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/audit/TrustedBoundary.lean:442-558` and `trusted/lean/foundation-lock.json` governing Pass-1 Lean syntax and locked `Init.*` imports |
| **Lean 4** | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel checker (`-DElab.async=false -Ddebug.skipKernelTC=false`) for all 44 theorems in [`support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean`](support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean) |
| **Linux kernel** | `torvalds/linux@65e4fd942f72a9dba0e4e257290c4fa1aa756854` | Normative AArch64 `PR_SET_TAGGED_ADDR_CTRL` / `PROT_MTE` / `SEGV_MTESERR` (`9`) syscall and signal ABI (`Documentation/arch/arm64/memory-tagging-extension.rst`) |
| **`qemu-aarch64` (`11.1.2`)** | Debian `1:11.1.2+ds-2`, SHA-256 `8ba579d4...758eb59` | Executed `-cpu max` user-mode emulation for Armv8.5-A MTE (`stg`, `ldr q`, `ldp q0, q1`) and SVE (`ld1b`, `ldff1b`) |

### Relationship to Existing Corpus Coverage

This package builds on—without repeating—established corpus results:
- Cross-level `TotalMirAsmEquiv`, `PrecondMirAsmEquiv`, `PadIndependent` on caller-owned `PaddedSlice<MaybeUninit<u8>>`, Tristan-Leroy software pipelining, and fixed-count `prolog_unroll_epilog_equiv`: `rust-vs-inline-asm-behavioral-equivalence-for-verified-hot-loop-optimization`.
- Reentrant `MIR <-> ISA` call stacks, `Tree Borrows` `FnEntry` protectors, PNVI-ae-udi provenance exposure, and `vendor/lean-miri` `TerminatorHooks`: `reentrant-ffi-mixed-mir-isa-call-stacks-tree-borrows-and-oracle-composition`.
- Hardware `[63:48]` upper-address bit partitions (`TBI`, `MTE` `[59:56]`, `PAC`, `LAM_U57`): `mte-lam-upper-address-tags-libmpk-pitfalls-and-gofetch-prefetching`.
- Baseline shadow-memory layouts of `ASan`, `HWASan`, `MSan`, and `TSan v3`: `shadow-memory-asan-msan-origins-and-tsan-vector-clock-sanitizers`.
- `core::simd` `simd_masked_load` unconditional alignment vs. disabled-lane OOB exemption: `core-simd-mask-all-ones-ub-masked-tail-loads-and-lanewise-chunk-algebras`.

## Findings

### 1. Upstream Production Over-Read Taxonomy Across `glibc`, `BurntSushi/memchr`, and `simdutf`

`Basis: source` (`bminor/glibc@04e750e7`, `BurntSushi/memchr@5fdb40c0`, `simdutf/simdutf@17794507`).

Inspecting four production SIMD search implementations reveals why strict byte-exact `memaccess_inbounds` suffices for Rust/C++ intrinsic code yet rejects real assembly `libc` kernels—and why `glibc` itself splits x86-64 from AArch64 MTE at the hardware protection-granule boundary:

| Implementation & Pinned File | Assumed Granule $G = 2^g$ | Short-Slice (`len < W`) & Prolog Strategy | Out-of-Bounds Masking & Index Extraction | Formal Memory Regime Needed |
| :--- | :---: | :--- | :--- | :--- |
| **`glibc` x86-64 AVX2** (`sysdeps/x86_64/multiarch/memchr-avx2.S:68-117, 374-439`; `strlen-avx2.S:53-110, 509-554`) | **$4,096\text{ B}$** (`g = 12`, MMU page) | Upfront `test %rdx, %rdx; jz L(null)`. If `(edi & 4095) <= 4064`, executes **unaligned 32B over-read** `vpcmpeqb (%rdi), %ymm0, %ymm1` even on `len = 1`; else `L(cross_page_boundary)` aligns via `orq $31, %rcx; vpcmpeqb -31(%rcx)` (`ptr & !31`). | Leading bytes: `sarxl %edi, %eax, %eax` (`L428`); single-vec length check: **`tzcntl %eax, %eax; cmpl %eax, %edx; jle L(null)`** (`L101-114`, requires `BMI1`); tail loop: `movq $-1, %rcx; bzhiq %rdx, %rcx, %rcx` (`L375-376`, `BMI2`). | Page-granule (`g = 12`) over-read (or `g >= 5` aligned `DemonicGranuleLoad` on the cross-page path) |
| **`glibc` AArch64 MTE-safe NEON** (`sysdeps/aarch64/memchr.S:59-118`, vs. non-MTE `strlen_asimd.S:25, 90-95`) | **$16\text{ B}$** (`g = 4`, MTE tag granule) | `bic src, srcin, 15` (preserves MTE tag in `[59:56]`, aligns to 16B); `cbz cntin, L(nomatch)`; `ld1 {vdata.16b}, [src]`. Unrolled loop guards `tbz cntrem, 4, L(loop32_2)` (*"Make sure that it won't overread by a 16-byte chunk"*, `L85-86`). By contrast, `strlen_asimd.S:25` states *"Not MTE compatible"*. | `shrn vend.8b, vhas_chr.8h, 4` packs 4 bits/byte into `synd`; `lsl shift, srcin, 2; lsr synd, synd, shift` strips pre-slice nibbles; `rbit` + `clz` + `lsr #2` + `cmp cntin, ...; csel` checks `< len`. | `DemonicGranuleLoad` with **`granuleBits = 4`** (`16 B`) and tag-preserving alignment |
| **`BurntSushi/memchr` `2.8.3`** (`src/arch/x86_64/avx2/memchr.rs:179-205`, `src/arch/generic/memchr.rs:143-230`) | **$1\text{ B}$** (`g = 0`, strict Rust AM) | Because `_mm256_load_si256` lowers to LLVM `load <4 x i64>` (UB on `< 32 B`), branches to **scalar byte loop for `len < 16`**, SSE2 for `16..31`, and for `len >= 32` uses unaligned `start` load + 128B aligned loop + **overlapping in-bounds `end.sub(32)`** tail (`L223-228`). | No out-of-bounds lanes ever read; `u32::trailing_zeros()` (`src/vector.rs:178`) runs strictly inside `if mask.has_non_zero()`. | Strict byte-exact `memaccess_inbounds` (`granuleBits = 0`) |
| **`simdutf` Haswell vs. Icelake** (`src/generic/find.h:6-43`; `src/icelake/icelake_find.inl.cpp:9-28, 65-83`) | **$1\text{ B}$** or **AVX-512 `maskz`** | Haswell/ARM64 run scalar byte loops until `start % 64 == 0` (`arm64`: `start % 16 == 0`) and scalar tails. Icelake uses hardware fault-suppressing `_mm512_maskz_loadu_epi8(0xFFFF... >> (64 - rem), start)`. | **Critical `maskz` trap (`icelake_find.inl.cpp:20-21, 75`):** `_mm512_maskz_loadu_epi8` zeroes inactive lanes to `0x00`, causing false matches when `character == '\0'` unless `match_mask &= load_mask` is applied *after* `_mm512_cmpeq_epi8_mask`! | Strict `granuleBits = 0` (Haswell/ARM64) or per-lane predicated load (`simd_masked_load` / `maskz`) |

---

### 2. Empirical Soundness Envelope & Failure Modes on x86-64 and AArch64 MTE

#### 2.1 Exhaustive `PROT_NONE` Guard-Page Matrix and Five x86-64 Negative Canaries

`Basis: execution + derived` ([`support/probe_x86_overread_sanitizers_and_cse.py`](support/probe_x86_overread_sanitizers_and_cse.py), [`support/probe_x86_overread_sanitizers_and_cse_results.json`](support/probe_x86_overread_sanitizers_and_cse_results.json), executed on `rustc 1.99.1 -C opt-level=3`, Linux `x86_64`).

Testing `memchr_avx2_overread` (`if len == 0 { return None; }`, `algn = ptr & -32`, `vmovdqa` + `vpcmpeqb` + `vpmovmskb` + `shrx` + `bzhi` + `tzcnt` + `vzeroupper`) across two `mmap`/`mprotect(PROT_NONE)` arenas with every leading and trailing out-of-bounds byte pre-poisoned to `needle = 0xA5`:
- **Single-page tight sandbox `[G0 (PROT_NONE), P1 (4096 B RW), G2 (PROT_NONE)]`:** All **`524,224` `(off, len)` pairs** (`off ∈ 0..4096`, `len ∈ 0..=min(129, 4096 - off)`, **`2,084,608` calls** testing all-miss, last-byte hit, first-and-last early-exit parity, and interior two-match parity) pass with **`0` faults and `0` mismatches**.
- **Full `4,096 × 130` cross-page sandbox `[G0 (PROT_NONE), Q1 (4096 B RW), Q2 (4096 B RW), G3 (PROT_NONE)]`:** All **`532,480` `(off, len)` pairs** (`off ∈ 0..4096`, `len ∈ 0..=129`, including all **`8,256` page-crossing slices** where `off + len > 4096`, **`1,060,864` calls**) pass in **`82.76 ms` total**.
- **Single-byte (`len == 1`) non-crossing invariance vs. `len >= 2` crossing:** A 1-byte slice `[ptr, ptr + 1)` occupies a single address `ptr`, so for every power-of-two granule $2^g \ge 2^k$, $[p_{\text{aligned}}, p_{\text{aligned}} + 2^k) \subseteq [\text{alignDown}(g, \text{ptr}), \text{alignDown}(g, \text{ptr}) + 2^g)$ holds at **all 4,096 page offsets** (`0..4095`) without ever crossing a 32-byte or 4,096-byte boundary (`single_byte_slice_admissible_and_contained`). By contrast, `len >= 2` at `off = 4095` legitimately spans two mapped pages `Q1` and `Q2`, where the prolog reads `[Q1 + 4064, Q1 + 4096)` inside `Q1` and the epilog reads `[Q2, Q2 + 32)` inside `Q2`—still never touching `G0` or `G3`.

Five concrete negative canaries isolate every unsound shortcut:

| Canary | Violated Invariant | Observed Hardware Outcome (`rustc 1.99.1 -C opt-level=3`) | Root Mechanism |
| :--- | :--- | :--- | :--- |
| **Canary 1** | Unguarded `len == 0` on `&[]` | **`SIGSEGV` (`signal = 11`)** | Safe Rust `&[]` uses `NonNull::dangling() == 0x1`; `0x1 & -32 == 0x0`, dereferencing the unmapped null page |
| **Canary 2** | Unguarded `len == 0` on `&page[4096..4096]` | **`SIGSEGV` (`signal = 11`)** | Safe slicing `&buf[buf.len()..]` produces a non-null, 4096-aligned pointer equal to `G2` (`PROT_NONE`); `G2 & -32 == G2` |
| **Canary 3** | Unaligned `vmovdqu` on `len == 1` at `P1 + 4095` | **`SIGSEGV` (`signal = 11`)** | `[P1 + 4095, P1 + 4127)` crosses 31 bytes into trailing guard page `G2` |
| **Canary 4** | `bsf` instead of `tzcnt` (`BMI1`) on `mask == 0` (`glibc` `L(first_vec_x0)` pattern) | **Returns `Some(0)` on non-matching `[0x5A]`** (sound returns `None`) | On Intel/AMD x86-64, `bsf dst, src` leaves `dst` unmodified (`0`) when `src == 0`; `cmp len, 0` sees `1 > 0` and falsely reports index `0` |
| **Canary 5** | Arithmetic `sarx` instead of logical `shrx` (`byte 31 == needle`, `mis = 16`) | **`mask = 0xffff8000`** instead of `0x00008000` | `vpmovmskb` sets sign bit `31 = 1` on byte 31; `sarx` sign-extends `1`s across bits `16..31`, corrupting match counts or unclipped `mask != 0` checks |

#### 2.2 Live Armv8.5-A MTE (`16`-Byte Tag Granule) & SVE Execution Under QEMU `11.1.2`

`Basis: normative + source + execution` (`torvalds/linux@65e4fd94`: `Documentation/arch/arm64/memory-tagging-extension.rst:16-118`; [`support/probe_aarch64_mte_granules.py`](support/probe_aarch64_mte_granules.py), [`support/probe_aarch64_mte_granules_results.json`](support/probe_aarch64_mte_granules_results.json)).

Compiling a static `#![no_std]` `aarch64-unknown-linux-gnu` binary (`rustc 1.99.1`) that enables synchronous MTE checking via `prctl(PR_SET_TAGGED_ADDR_CTRL, PR_TAGGED_ADDR_ENABLE | PR_MTE_TCF_SYNC | (0xfffe << 3))`, maps a `PROT_READ | PROT_WRITE | PROT_MTE` (`0x23`) page, tags 16-byte granules via `stg`, and intercepts `SIGSEGV` (`SA_SIGINFO`) under `qemu-aarch64 -cpu max` (`11.1.2`) establishes five architectural facts and one critical emulator boundary:

| Case (`probe_aarch64_mte_granules_results.json`) | Instruction & Address Setup | Live QEMU `11.1.2` `-cpu max` Result | Architectural Consequence |
| :--- | :--- | :--- | :--- |
| **`mte_16b_aligned_neon_memchr_matrix`** | `bic algn, ptr, #15; ldr q, [algn]` (`16 B`, `k = 4`) across `mis ∈ 0..15`, `len ∈ 0..80`, active tag `5` flanked immediately by left tag `9` and right tag `11` filled with poison `needle` | **`faulted = false`, `3,856 / 3,856` checks passed** | When `load_size = 16 <= G_arch = 16` (`k <= granuleBits`), aligned over-reads stay strictly inside the allocation's 16-byte MTE tag granules |
| **`fault_32b_ldp_trailing_granule_mismatch`** | `ldp q0, q1, [ptr & !31]` (`32 B`, `k = 5`) on slice in `[base, base + 16)` (tag `1`) adjacent to `[base + 16, base + 32)` (tag `2`) | **`SIGSEGV` (`si_signo = 11`), `si_code = 9` (`SEGV_MTESERR`), `fault_offset = 16`, `fault_ptr_tag = 1`** | `32 B > 16 B` over-reads forward into sibling heap/stack granule inside the same 4 KiB page and faults synchronously |
| **`fault_32b_ldp_leading_granule_mismatch`** | `ldp q0, q1, [ptr & !31]` on slice in `[base + 16, base + 24)` (tag `2`) preceded by `[base, base + 16)` (tag `1`) | **`SIGSEGV` (`11`), `SEGV_MTESERR` (`9`), `fault_offset = 0`, `fault_ptr_tag = 2`** | Aligning down by 32 bytes (`(base + 16) & !31 == base`) steps **backward** into an unowned MTE granule and faults *before* reaching `ptr` |
| **`fault_16b_unaligned_ldr_crossing_granule`** | Unaligned `ldr q0, [ptr]` (`16 B`) on `len = 1` at `(base + 1) \| (1 << 56)` | **`SIGSEGV` (`11`), `SEGV_MTESERR` (`9`), `fault_offset = 16`, `fault_ptr_tag = 1`** | Unaligned 16B load crosses 1 byte into `[base + 16, base + 32)` (tag `2`) even on `len = 1` |
| **`fault_48bit_mask_strips_mte_tag`** | `ldr q0, [ptr & 0x0000_ffff_ffff_fff0]` on `(base + 3) \| (1 << 56)` | **`SIGSEGV` (`11`), `SEGV_MTESERR` (`9`), `fault_offset = 0`, `fault_ptr_tag = 0`** | Masking high bits instead of `bic algn, ptr, #15` (`!15`) zeroes MTE logical tag `[59:56]` and faults on the slice's own granule |
| **`sve_ldff1b_prot_none_vs_qemu_user_sve_mte_gap`** | SVE `ldff1b` (`VL = 64 B`) at `page_end - 16` (`PROT_NONE` next page) vs. `ldff1b` at `base \| (2 << 56)` (granule 0 tag `1 != 2`) | `PROT_NONE` truncates `FFR` to **`16` B**; mismatched MTE tag returns **`64` B (`0` fault!)** | **Surrogate-emulator hazard:** `qemu-aarch64 11.1.2` (`linux-user`) enforces MTE on scalar/NEON `ldr`/`ldp` and `PROT_NONE` on SVE `ldff1b`, **but omits MTE tag checks on SVE `ld1b`/`ldff1b`**—passing QEMU user-mode runs do *not* prove SVE+MTE soundness! |

#### 2.3 Dynamic Sanitizer (`ASan` & `TSan`) Compiler Seams and LLVM `-C opt-level=3` CSE

`Basis: source + execution` (`llvm/llvm-project@63b8d2fd`: `AddressSanitizer.cpp:1821-1850`, `ThreadSanitizer.cpp:120-125, 781-798`; [`support/probe_x86_overread_sanitizers_and_cse.py`](support/probe_x86_overread_sanitizers_and_cse.py) on `rustc 1.99.1` and `1.102.0-nightly`).

1. **AddressSanitizer (`-Zsanitizer=address`) — Four Distinct Lowering Regimes:**
   - **Inline `asm!` `vmovdqa` (`asm_stack_and_heap`):** LLVM's `AddressSanitizer` pass does not instrument instructions inside inline `asm!`, so aligned 32-byte `asm!` over-reads across ASan stack (`0xf1`/`0xf2`/`0xf3`, including `detect_stack_use_after_return=1` `FakeStack`) and heap (`0xfa`/`0x04`) redzones execute cleanly with **`rc = 0`**.
   - **`core::arch` `_mm256_load_si256` (`intrinsic_stack`, `intrinsic_heap`):** Lowers to LLVM `load <4 x i64>, ptr %p, align 32`, which ASan instruments and aborts on both stack (`stack-buffer-overflow`, `rc = 1`) and heap (`heap-buffer-overflow`, `rc = 1`) redzones.
   - **The `#[sanitize(address = "off")]` cross-attribute non-inlining trap (`intrinsic_nosan_calls_core` vs. `deref32_nosan_direct`):** Annotating a Rust helper with `#![feature(sanitize)] #[sanitize(address = "off")]` and calling `_mm256_load_si256(algn)` **still crashes with `AddressSanitizer: stack-buffer-overflow` (`rc = 1`)**! Emitted LLVM IR reveals why: `load32_nosan` omits `sanitize_address`, whereas `core::core_arch::x86::avx::_mm256_load_si256` is monomorphized *with* `sanitize_address`; LLVM's inliner refuses to inline a `sanitize_address` callee into a non-`sanitize_address` caller, emitting an out-of-line `tail call fastcc ... __mm256_load_si256` that still checks ASan shadow memory. Only a direct raw dereference `*algn` inside the `#[sanitize(address = "off")]` body (`deref32_nosan_direct`, `rc = 0`) or `asm!` avoids sanitized `core` wrappers.
   - **256-bit ASan interior-granule blind spot (`AddressSanitizer.cpp:1841-1848`, `interior_granule_256b_blindspot`):** For `TypeStoreSize = 256` bits (`32 B`, outside `8..128` standard sizes), `AddressSanitizer::instrumentUnusualSizeOrAlignment` checks **only** `Addr` (`p`) and `LastByte` (`p + 31`). Poisoning the middle 16 bytes `[p + 8, p + 24)` via `__asan_poison_memory_region` while `p` and `p + 31` remain valid passes `_mm256_load_si256` with **`rc = 0`**!
2. **ThreadSanitizer (`-Zsanitizer=thread`) — The 128-Bit vs. 256-Bit Instrumentation Cliff:**
   - Note first that on `rustc 1.102.0-nightly` (`3ef0c22cd`), `-Zsanitizer=thread` alters crate ABI metadata and fails compilation against prebuilt `std` (`mixing -Zsanitizer will cause an ABI mismatch`) unless built with `-Zbuild-std` or `-Cunsafe-allow-abi-mismatch=sanitizer` (and using `pthread_create` directly so TSan intercepts thread synchronization).
   - In `llvm/lib/Transforms/Instrumentation/ThreadSanitizer.cpp:788-794`:
     ```cpp
     uint32_t TypeSize = DL.getTypeStoreSizeInBits(OrigTy);
     if (TypeSize != 8  && TypeSize != 16 &&
         TypeSize != 32 && TypeSize != 64 && TypeSize != 128) {
       NumAccessesWithBadSize++;
       // Ignore all unusual sizes.
       return -1;
     }
     ```
     (Lines `784-786` likewise return `-1` for all `isScalableTy()` SVE/RVV vectors.)
   - **Live confirmation (`tsan_probe`):** When a background thread concurrently mutates `Shared32.adj_in_16b` (`[8..16)`) while the main thread searches `Shared32.hay` (`[0..8)`):
     - **128-bit SSE2 `_mm_load_si128` (`sse2_16b_intrinsic`):** Emits `call void @__tsan_read16(ptr %p)` and **terminates with `rc = 66` (`WARNING: ThreadSanitizer: data race`)**.
     - **256-bit AVX2 `_mm256_load_si256` (`avx2_32b_intrinsic`):** Emits **zero** `__tsan_read*` calls (`rc = 0`, `0` warnings) despite committing an LLVM IR non-atomic data race (`poison` on lanes `8..15`).
     - **Inline `asm!` `vmovdqa` (`asm_sound_32b` vs. `asm_off_by_one_32b`):** Both emit zero `__tsan_read*` calls (`rc = 0`, `0` TSan warnings). With a sound 8-bit mask (`0xff`), `0 / 150,000` calls are affected; with an off-by-one 9-bit mask (`0x1ff`), **`69,079 / 150,000` calls silently return corrupted concurrent neighbor state** while TSan stays completely silent—proving dynamic race detectors cannot substitute for formal slack-obliviousness verification on `asm!`.
3. **`options(readonly)` vs. `options(pure, readonly)` Under `-C opt-level=3` LLVM CSE/GVN:**
   - Across both `rustc 1.99.1` and `1.102.0-nightly`, `options(readonly, nostack)` emits `call ... asm sideeffect inteldialect` (`2` `vmovdqa` loads in `caller_readonly_no_pure_buggy_pair`), whereas adding `pure` (`options(pure, readonly, nostack)`) drops `sideeffect` (`call ... asm inteldialect ... nounwind memory(read)`).
   - Given `x: &[u8; 16]` and `y: &mut [u8; 16]` occupying `[0..16)` and `[16..32)` of the same 32-byte aligned `Adj32` struct, Rust's `noalias` attributes let LLVM GVN/EarlyCSE prove `y[0] = needle` cannot mutate memory reachable through `x`, **eliminating the second `asm!` call (`vmovdqa_count = 1`)** in `let r1 = f(x); y[0] = needle; let r2 = f(x);`!
   - When `f` is **demonic-slack-oblivious** (`caller_pure_readonly_sound_pair`), `r1 == r2 == -1` agrees with a fresh post-mutation call (`sound_fresh_after_mutation = -1`), so `options(pure, readonly)` is **sound**. When `f` has an **off-by-one mask (`len + 1 = 17`)**, `options(readonly)` without `pure` returns `[-1, 16]`, `options(pure, readonly)` CSEs the pair to **`[-1, -1]`**, and an un-inlined call immediately afterward on the identical state returns **`16`**—a concrete miscompilation/time-travel inconsistency caused by violating `DemonicSlackOblivious`.

---

### 3. Granule-Parameterized `DemonicGranuleLoad` & 2-Safety `LeakTrace` in Lean `v4.34.1`

`Basis: derived + execution` ([`support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean`](support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean), lines `38-660`).

#### 3.1 Unified `GranuleLoadAdmissible` and Fresh Per-Load Demonic Slack

Let `pow2 k = 2^k` and `alignDown k addr = (addr / 2^k) * 2^k`. Parameterizing the ISA memory bridge by `granuleBits : Nat` (`12` for 4 KiB x86-64/AArch64 MMU pages without MTE, `4` for 16-byte AArch64 MTE tag granules, `0` for MMIO or strict byte-exact Rust/LLVM semantics), an aligned $2^k$-byte non-volatile load at `alignedAddr` against authorized readable slice `[authBase, authBase + authLen)` is governed by:

```lean
def GranuleLoadAdmissible
    (granuleBits authBase authLen k alignedAddr : Nat) : Prop :=
  k ≤ granuleBits ∧
  Nat.mod alignedAddr (pow2 k) = 0 ∧
  ∃ b, alignedAddr ≤ b ∧ b < alignedAddr + pow2 k ∧
       authBase ≤ b ∧ b < authBase + authLen

def demonicReadLane
    (authBase authLen : Nat) (mem : Nat → Nat) (demonStep : Nat → Nat)
    (alignedAddr lane : Nat) : Nat :=
  match inSlice authBase authLen (alignedAddr + lane) with
  | true => mem (alignedAddr + lane)
  | false => demonStep lane
```

Six kernel-checked theorems establish the exact properties of this bridge:
1. **Granule Containment (`aligned_load_stays_in_granule`):** Whenever `k ≤ granuleBits`, for every byte `b`, `alignDown granuleBits b ≤ alignDown k b` and `alignDown k b + pow2 k ≤ alignDown granuleBits b + pow2 granuleBits`. Thus, if `b ∈ [authBase, authBase + authLen)` is live and readable in hardware granule $G(b)$ (carrying `b`'s page permissions and MTE tag), the entire $2^k$-aligned load span containing `b` lies inside $G(b)$ and cannot fault.
2. **Conservative Recovery of Strict In-Bounds (`demonicGranuleLoad_zero_recovers_strict_inbounds`):** At `granuleBits = 0`, `GranuleLoadAdmissible 0 authBase authLen k alignedAddr ↔ (k = 0 ∧ authBase ≤ alignedAddr ∧ alignedAddr < authBase + authLen)`, collapsing to 1-byte strict `memaccess_inbounds` with zero slack lanes (mandatory for volatile/MMIO regions where side-effecting reads cannot over-read).
3. **Rejection of Empty Slices and MTE Over-Wide Loads (`empty_slice_unguarded_not_admissible`, `mte_16b_granule_rejects_32b_load_and_crosses_tag`):** `authLen = 0` has no witness `b` (`¬ GranuleLoadAdmissible ... 0 k alignedAddr`), and `granuleBits = 4, k = 5` (`32 B > 16 B`) is rejected while exhibiting both forward (`0 -> 16`) and backward (`16 -> 0`) MTE granule crossings.
4. **Why Fresh Per-Load `demon : DemonSched` (`stepIdx -> laneIdx -> Nat`) Captures Three Hazards at Once:**
   - *`MaybeUninit` / struct padding:* Arbitrary uninitialized hardware byte values (`0..255`).
   - *Unexposed sibling `AllocId`s (`&y` in `Adj32`):* Slack lanes yield untyped `Nat` bytes with stripped provenance (`prov = none`, never exposing `y`'s `AllocId`), and universal quantification over `demon` forces `asm` to be invariant under caller writes to `y` (licensing `options(pure, readonly)` LLVM CSE).
   - *Concurrent neighbor writes on other threads:* Because ISA `vmovdqa`/`ldr q` does not produce LLVM `poison` on non-atomic races, sampling a fresh `demon step` on every load step `step` models arbitrary concurrent mutations to neighbor bytes between loads without tearing in-slice bytes `mem (alignedAddr + lane)`.
5. **Demonic Slack Obliviousness Characterization (`demonic_equiv_iff_slack_oblivious`) & Off-by-One Refutation (`off_by_one_mask_violates_demonic_equiv`):** For deterministic safe `ref`, `TotalMirAsmDemonicEquiv ref asm` holds iff `asm` never traps, satisfies `DemonicSlackOblivious asm` (`∀ q d1 d2, asm q d1 = asm q d2`), and agrees with `ref` on `zeroDemon`; an off-by-one `bzhi` width (`len + 1`) fails both.
6. **1-Safety vs. 2-Safety Split on Unmasked Fast-Path Branches (`unmasked_fastpath_1safety_vs_2safety_leaktrace`):** Branching on unmasked `vpmovmskb` (`if rawMask == 0`) before masking slack (`glibc` `memchr-avx2.S:257-258`) satisfies 1-safety `DemonicSlackOblivious` on return values, **yet leaks a caller's adjacent secret stack variable `secSlack` into the branch trace** (`[LeakObs.branch false]` when `secSlack != needle` vs. `[LeakObs.branch true]` when `secSlack == needle`, even when `memchr` is called on a 100% public slice!). Constant-time 2-safety requires `maskedFirstSearch` (masking slack lanes *before* any conditional jump or memory index).

---

### 4. Reusable Variable-Stride Early-Exit Search Equivalence (`early_exit_simd_search_equiv`)

`Basis: derived + execution` ([`support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean`](support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean), lines `375-1465`).

Counted loop combinators (`prolog_unroll_epilog_equiv` in `rust-vs-inline-asm-behavioral-equivalence-for-verified-hot-loop-optimization`) require a static iteration decomposition `n = p + m * U + e` and cannot align a SIMD search loop that advances by variable prolog stride `W - mis ∈ [1..W]`, full stride `W`, or early-exit offset `tzcnt(mask) + 1 ∈ [1..W]`. Mechanizing the complete search pipeline in Pass-1 Lean `v4.34.1` factors into four reusable layers:

1. **Integer Bitmask Window Algebra (`shrx_bzhi_packBits_window`, `masked_demonic_chunk_eq_pure_slice_window`):**
   Defining `packBits W f` (`vpmovmskb`), `shrxMask mis m := Nat.div m (pow2 mis)` (`shrx`), and `bzhiMask cnt m := Nat.mod m (pow2 cnt)` (`bzhi`), whenever `mis + cnt ≤ pow2 k` and `[alignedAddr + mis, alignedAddr + mis + cnt) ⊆ [authBase, authBase + authLen)`:
   $$\text{bzhiMask}(\text{cnt}, \text{shrxMask}(\text{mis}, \text{packBits}(2^k, \lambda i.\, \text{demonicReadLane}_i = \text{needle}))) = \text{packBits}(\text{cnt}, \lambda j.\, \text{mem}(\text{alignedAddr} + \text{mis} + j) = \text{needle}),$$
   erasing `demonStep` identically before any control-flow inspection.
2. **First-Set-Bit Extraction & `CpuFeatures.bmi1` (`tzcntW_packBits_first_match`, `bmi1_tzcnt_vs_bsf_zero_hazard`):**
   Whenever `cnt ≤ W` and `m = packBits cnt g ≠ 0`, `idx := tzcntW W m` satisfies `idx < cnt`, `g idx = true`, and `∀ j < idx, g j = false`. Theorem `bmi1_tzcnt_vs_bsf_zero_hazard` proves that unguarded tail comparison `tzcnt(m) < len` requires `hasBmi1 = true` (`tzcntW 32 0 = 32`), whereas guarding `tzcnt`/`bsf` behind `m == 0` eliminates the `hasBmi1` precondition completely.
3. **Variable-Stride Early-Exit Window Lemma (`scalarSearchLoop_window_step`):**
   For any `cnt ≤ W` and `cnt ≤ rem`, evaluating `m := packBits cnt (fun j => pred (mem (ptr + (idx + j))))` simulates `1 .. cnt` steps of `scalarSearchLoop`:
   - if `m = 0`, `scalarSearchLoop pred mem ptr rem idx = scalarSearchLoop pred mem ptr (rem - cnt) (idx + cnt)` (`cnt` non-matching scalar steps skipped in $O(1)$);
   - if `m ≠ 0`, `scalarSearchLoop pred mem ptr rem idx = some (idx + tzcntW W m)` (exact early exit at the first matching byte).
4. **End-to-End 4-Stage Equivalence (`early_exit_simd_search_equiv` & `simd_overread_memchr_total_demonic_equiv`):**
   `simdAlignedOverreadSearch` executes the runtime-checked granule guard `checkedDemonicChunkMask` on the misaligned prolog (`algn = alignDown k ptr`), every $2^k$-aligned main-loop chunk (`rem > 2^k`), and the $2^k$-aligned masked epilog (`1 ≤ rem ≤ 2^k`). Whenever `k ≤ granuleBits`, `early_exit_simd_search_equiv` proves—for **all** `(ptr, len)`, memories `mem`, needles, and demonic schedules `demon`—that zero loads trap and the returned `Option Nat` equals `memchrRef needle mem ptr len` identically, lifting immediately to `TotalMirAsmDemonicEquiv`.

## Boundaries

- **Not examined — Physical Armv8.5-A / Armv9-A silicon MTE execution:** Hardware MTE behavior was verified via Linux kernel documentation/source (`torvalds/linux@65e4fd94`) and live user-mode execution under `qemu-aarch64 11.1.2 -cpu max`. In particular, how physical Armv9 SVE hardware handles `ldff1b` (first-faulting loads) across intra-page 16-byte MTE tag mismatches was **not examined** on silicon because `qemu-aarch64 11.1.2` skips MTE tag checks on SVE `ld1b`/`ldff1b` (Section 2.2).
- **Not examined — Speculative microarchitectural cache/port leakage of masked-out slack bytes (`Spectre-v1` / `GoFetch` DMP):** Even when `maskedFirstSearch` masks out over-read slack bytes before architectural branches (`LeakTrace` 2-safety), loading an adjacent secret 64-bit pointer into a SIMD register or L1 cache line can still activate hardware Data-Memory-Dependent Prefetchers on affected microarchitectures (documented in `mte-lam-upper-address-tags-libmpk-pitfalls-and-gofetch-prefetching`) or transient execution gadgets; microarchitectural value-dependent leakage inside vector ALUs was **not examined**.
- **Known not to apply — Using `granuleBits > 0` on MMIO / volatile memory or CHERI capability bounds:** Hardware MMIO read registers trigger side effects on every byte lane strobed on the bus, and strict hardware capability architectures (CHERI / Arm Morello) fault when any byte of a wide load falls outside the capability's exact `[base, top)` bounds regardless of page alignment. Both regimes require `granuleBits = 0` (`demonicGranuleLoad_zero_recovers_strict_inbounds`).
- **Known not to apply — Using 32-byte (`k = 5`) or 64-byte (`k = 6`) aligned over-reads under AArch64 MTE (`granuleBits = 4`) or x86-64 HWASan (`16`-byte granules):** As proved in `mte_16b_granule_rejects_32b_load_and_crosses_tag` and live `SEGV_MTESERR` execution (`probe_aarch64_mte_granules.py`), any non-predicated load wider than `16` bytes crosses allocation tag granules and faults synchronously.
- **Known not to apply — Relying on `-Zsanitizer=thread` to detect data races on 256-bit (`AVX2`), 512-bit (`AVX-512`), scalable (`SVE`/`RVV`), or inline-`asm!` loads:** Per `ThreadSanitizer.cpp:784-794` and live execution (`avx2_32b_intrinsic` `rc = 0` vs. `sse2_16b_intrinsic` `rc = 66`), LLVM TSan silently drops instrumentation on all vector accesses wider than 128 bits as well as inline `asm!`.
- **Known not to apply — Expecting `#[sanitize(address = "off")]` on a caller to suppress ASan inside `core::arch` load intrinsics:** Calling `_mm256_load_si256` from a `#[sanitize(address = "off")]` function still executes ASan checks (`rc = 1`) because LLVM blocks cross-`sanitize_address` inlining.
- **Unsupported — `DemonicGranuleLoad` and `TerminatorKind::InlineAsm` in baseline `joshlf/anneal@c131b320`:** Baseline `Trusted/MirSemantics.lean` rejects `InlineAsm` as `FaultKind.unsupported`; integrating `DemonicGranuleLoad` requires instantiating the `InlineAsm` ISA oracle hook and target `granuleBits` parameter in `Trusted/`.

## Evidence

### Primary Upstream Sources (Observed `2026-11-21`)

- **`bminor/glibc` (`04e750e75b73957cf1c791535a3f4319534a52fc`):**
  - `sysdeps/x86_64/multiarch/memchr-avx2.S:68-117, 374-439`: `jz L(null)` zero-length guard (`L68-70`), `PAGE_SIZE = 4096` cross-page check (`L76-79`), unguarded `tzcntl %eax, %eax; cmpl %eax, %edx; jle L(null)` (`L101-114`), `bzhiq` tail mask (`L375-376`), and `orq $31; vpcmpeqb -31(...); sarxl` aligned cross-page prolog (`L408-438`).
  - `sysdeps/x86_64/multiarch/strlen-avx2.S:53-110, 509-554`: `PAGE_SIZE - VEC_SIZE` check and `L(cross_page_boundary)` `sarxl` + `tzcntl`.
  - `sysdeps/aarch64/memchr.S:59-118`: MTE-compatible 16-byte `bic src, srcin, 15` align-down (`L60`), `shrn` 4-bit nibble syndrome (`L66-76`), and `tbz cntrem, 4, L(loop32_2)` 16-byte MTE over-read guard (`L85-86`).
  - `sysdeps/aarch64/multiarch/strlen_asimd.S:22-26, 68-96`: explicit *"Not MTE compatible"* header (`L25`) on `MIN_PAGE_SIZE = 4096` unaligned `ldp` prolog.
- **`BurntSushi/memchr` (`5fdb40c054e1fff359a2f7bdf7f87a13b34b465d`, `v2.8.3`):** `src/arch/x86_64/avx2/memchr.rs:179-205` (`len < 32` SSE2 / `< 16` scalar dispatch), `src/arch/generic/memchr.rs:143-230` (in-bounds overlapping `end.sub(V::BYTES)` tail), `src/vector.rs:138-192` (`SensibleMoveMask::first_offset` via `trailing_zeros`).
- **`simdutf/simdutf` (`177945073a2e44f6ef252aa2b9cf1ecb8e4d2ab0`):** `src/generic/find.h:6-43`, `src/arm64/arm_find.cpp:1-100`, and `src/icelake/icelake_find.inl.cpp:9-28, 65-83` (`_mm512_maskz_loadu_epi8` + post-compare `match_mask &= load_mask` null-byte false-positive guard).
- **`llvm/llvm-project` (`63b8d2fd94ba3b1a80023dae7139949dd5be6b78`):**
  - `llvm/lib/Transforms/Instrumentation/ThreadSanitizer.cpp:120-125, 781-798`: `kNumberOfAccessSizes = 5` (`1..16` B) and `getMemoryAccessFuncIndex` returning `-1` (`Ignore all unusual sizes`) on `TypeSize > 128` bits and scalable vectors.
  - `llvm/lib/Transforms/Instrumentation/AddressSanitizer.cpp:1821-1850`: `instrumentUnusualSizeOrAlignment` checking only `Addr` and `Addr + Size - 1`.
- **`torvalds/linux` (`65e4fd942f72a9dba0e4e257290c4fa1aa756854`):** `Documentation/arch/arm64/memory-tagging-extension.rst:16-118` (`PROT_MTE`, `PR_SET_TAGGED_ADDR_CTRL`, `PR_MTE_TCF_SYNC`, `SEGV_MTESERR`).
- **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** `src/inline-assembly.md` (`options(pure)`, `options(readonly)`, `r[asm.rules.mem-same-as-ffi]`).
- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`):** `trusted/audit/TrustedBoundary.lean:442-558` and `trusted/lean/foundation-lock.json`.

### Preserved Executable Support Artifacts (`support/`, Executed `2026-11-21` on Linux `x86_64`)

| Artifact Path | SHA-256 | Basis & Recorded Observation |
| :--- | :--- | :--- |
| [`support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean`](support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean) | `9c5e0d074cc50407c0426be9feee15efd984a158cbbfd8daca0bb167c14e1bb2` | **execution + derived**: Pass-1 `Init.*`-only Lean `v4.34.1` module (`44` theorems, `2.47 s` synchronous kernel check; `20/44` axiom-free, `24/44` `[propext]`, `0` `sorryAx`, `0` `._unsafe_rec`). |
| [`support/probe_x86_overread_sanitizers_and_cse.py`](support/probe_x86_overread_sanitizers_and_cse.py) | `45c049bcabe04f41e38564f423a391e686dcbcc80493d6ed461db2bc99ad1fdb` | **execution**: Runs the `532,480`-pair `PROT_NONE` guard-page & poison-slack harness, 5 negative `SIGSEGV`/`bsf`/`sarx` canaries, `rustc +nightly` ASan & TSan probes, and `rustc 1.99.1`/`+nightly` `-C opt-level=3` CSE probes. |
| [`support/probe_x86_overread_sanitizers_and_cse_results.json`](support/probe_x86_overread_sanitizers_and_cse_results.json) | `0a023ff6aa9aae2d941db9d19608852ff1ba5dcf9b4483851ea8f93688d442b3` | **execution**: Recorded output from `probe_x86_overread_sanitizers_and_cse.py`. |
| [`support/probe_aarch64_mte_granules.py`](support/probe_aarch64_mte_granules.py) | `c6bf7f319c6ad5d62ba915331f9ffa5fac7191302c1bdc2d89e8f74f4f80054f` | **execution**: Builds static `#![no_std]` `aarch64-unknown-linux-gnu` MTE+SVE binary (`rustc 1.99.1`) and runs 6 fault/non-fault experiments under `qemu-aarch64 -cpu max` (`11.1.2`). |
| [`support/probe_aarch64_mte_granules_results.json`](support/probe_aarch64_mte_granules_results.json) | `019cc07b5a1830ceb9d2c5fd6fcf34a66da236b7e25d19c3f3467d62c552ad8a` | **execution**: Recorded output from `probe_aarch64_mte_granules.py`. |

## Revalidation

Run the following deterministic checks from the report package directory (`< 15 s` total on Linux `x86_64` with `rustc 1.99.1`, `rustc +nightly`, `qemu-aarch64`, and `lean v4.34.1`):

1. **Kernel-check all 44 Lean `v4.34.1` theorems synchronously (`~2.5 s`):**
   ```bash
   elan run leanprover/lean4:v4.34.1 lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/AlignedOverreadDemonicGranulesAndEarlyExitSearch.lean
   ```
   Verify exit code `0` and zero warnings/errors.
2. **Re-run the x86-64 `PROT_NONE` guard-page matrix, ASan/TSan compiler seams, and `-C opt-level=3` CSE probes (`~6 s`):**
   ```bash
   python3 -B support/probe_x86_overread_sanitizers_and_cse.py
   ```
   Verify exit code `0`: if a future LLVM release extends `ThreadSanitizer::getMemoryAccessFuncIndex` past `128` bits, `avx2_32b_intrinsic.rc` will flip from `0` to `66` (`load32_avx2_has_any_tsan_read_in_ir == true`).
3. **Re-run the live AArch64 MTE 16-byte tag-granule & SVE QEMU probe (`~1.5 s`):**
   ```bash
   python3 -B support/probe_aarch64_mte_granules.py
   ```
   Verify exit code `0`: `3,856` passing 16B-aligned NEON checks, `si_code == 9` (`SEGV_MTESERR`) on all four 32B/unaligned/tag-stripped fault cases, and check whether newer QEMU releases wire SVE `ldff1b` through MTE tag checking (`qemu_user_ldff1b_bytes_on_mismatched_mte_tag` dropping from `64` to `0`).
