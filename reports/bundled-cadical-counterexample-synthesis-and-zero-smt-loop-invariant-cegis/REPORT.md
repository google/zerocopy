# Bundled-CaDiCaL Counterexample Synthesis and Zero-SMT Loop-Invariant CEGIS in Lean 4

## Summary

Closing an automated Rust SIMD and inline-assembly (`asm!` / `naked_asm!`) verification pipeline under a strict three-axiom Lean `v4.34.1` trust boundary (`{propext, Classical.choice, Quot.sound}`, `trustLevel := 0`, private-level `toKernelEnv.replay`, and zero external `z3`/`cvc5`/`bitwuzla` binaries on `PATH`) requires two capabilities beyond positive straight-line UNSAT certificates: (1) **dual-polarity counterexample synthesis** that refutes buggy optimizations across demonic machine-code nondeterminism without stalling on $\mathbb{F}_2$ parity circuits, and (2) **zero-SMT loop-invariant (`CutBox`) and schedule-alignment synthesis** that eliminates hand-authored relational loop invariants (`22–74` Lean LOC per loop) without invoking `Z3/Spacer`.

Direct execution and kernel-replayed `prelude` + `Init.*`-only mechanizations in Lean `v4.34.1` (`leanprover/lean4` `5045d0056413266e57c625dcd7c365b10e377c52`), its bundled `bin/cadical` (`CaDiCaL 2.1.2`), and `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) establish four primary results:

1. **Dual-polarity counterexample synthesis (`CaDiCaL exit 10` + coupled SAT-assumption shrinking + $\mathbb{F}_2$ unit-basis extraction) across `12 / 12` SIMD and `asm!` optimization bugs (`Basis: execution + source + derived`):**
   - Modeling the four machine-code nondeterminism channels absent from deterministic scalar MIR—sub-page alignment `pageMisalign ∈ [0, 4096)` (`PROT_NONE` cross-page vector loads), same-page out-of-slice `slackBytes` (`DemonicGranuleLoad`), architecturally undefined x86-64 registers/flags (`bsf` on zero source; `imul` unconditionally clearing `ZF = 0` on Intel Xeon even when `0 * 0 = 0`), and 2-safety relational `LeakTrace` pairs—catches `12 / 12` realistic SIMD/`asm!` bugs.
   - Because `CaDiCaL 2.1.2`'s `--lucky=1` pre-pass initializes unconstrained variables to all-ones (`hw_raw = 63..383` even under `--phase=0`), and single-bit local shrinking stalls on coupled relational constraints (`hw_1bit_local = 256` vs. `1` on 2-safety `vpmovmskb`, `130` vs. `36` on `mulx`+`adcx`/`adox`, and `9` vs. `1` on `vminss`), a two-tier **SAT-assumption coupled shrinker** (explicit word/byte chunk zeroing followed by strict MSB-to-LSB assumption sweeping without opportunistic LSB pinning) collapses witnesses to canonical minima (`x = 0x100` weight-1 SWAR borrow bleed; `a = -0.0f32, b = +0.0f32` weight-1 `vminss` swap; `len = 1, slack0 = 1` tail-mask bleed).
   - On 64-bit `pclmulqdq` CRC-64 2-lane folding (`Bug 8`), SAT-guided shrinking **stalls (`> 3,020 ms` timeout)** on its very first lane-zeroing query (`l == 0`) because refuting counterexamples on the healthy 64-bit lane reduces to an `UNSAT` carryless-multiply parity network. Routing $\mathbb{F}_2$-linear/bilinear circuits through constructive unit-basis search evaluates `65` basis vectors in **`1.22 ms`**, certifies all `64` healthy-lane basis vectors equal without CDCL resolution, and extracts the provably minimal weight-1 witness `(h = 0, l = 1)`.
2. **Dual emission of `[propext]`-only Lean `v4.34.1` kernel refutation theorems (`36.55 ms` replay) and a `2.58 ms` in-process `SIGSEGV` guard-page Rust `#[test]` suite (`Basis: execution + source`):**
   - All `12 / 12` synthesized witnesses compile automatically into `Init.*`-only kernel refutations (`¬ TotalMirAsmEquiv` or `¬ CtLeakEquiv` in [`support/lean/RefuteSimdAsm12.lean`](support/lean/RefuteSimdAsm12.lean), `462.74 ms` compile, `36.55 ms` private-level kernel replay, transitive axioms `['propext']` alone) alongside a formal proof (`triage_classII_noninductive_yet_program_correct`) separating **Class Ia/Ib** reachable code bugs from **Class II** unreachable loop-invariant gaps.
   - Simultaneously, [`support/generated_bug_repros.rs`](support/generated_bug_repros.rs) compiles under `rustc 1.99.1 --test` (`153.88 ms`) and executes all `12 / 12` hardware reproducers—including `mmap` + `mprotect(PROT_NONE)` page-boundary trapping via in-process `sigaction(SIGSEGV, SA_SIGINFO | SA_NODEFER)` + `__sigsetjmp`/`siglongjmp` (`~62x` faster than `fork() + waitpid()`) and demonic slack byte poisoning—in **`2.58 ms` median wall time**.
3. **Zero-SMT trace-matrix schedule inference + Houdini + bundled-`CaDiCaL` CEGIS eliminates `100%` of manual `CutBox` loop-invariant LOC across `6 / 6` hot loops (`Basis: execution + derived`):**
   - Concrete micro-traces (`len ∈ 0..64`) infer `(unrollStride U, pipelineLag mu, hasEarlyExit)` and filter candidate relational clauses (`Houdini`), uniquely discovering the `mu = 1` stage-drain conservation law `(acc + stage) % 2^64 = macPrefixSpec k` on software-pipelined MAC (`PipelinedMac`), the `ymm2 = ones16` constant vector pin on `2x`-unrolled `vpmaddubsw` (`DotMaddubsUnroll2`), positional carry conservation `outLimbs + cf * W^k = aLimbs + bLimbs` on multi-limb `adc` (`AdcLimbCarry`), negative prefix `noMatchBefore(16 * k)` on early-exit `memchr` (`MemchrEarlyExit`), and 2-safety `LeakTrace` lockstep on `cmove` (`CtCmovScan`).
   - Bundled-`CaDiCaL` inductive CEGIS prunes coincidental micro-trace bounds (`rcx <= 192`, `k <= 3`, `idx <= 6`, `k <= 4`, `k1 <= 6`) via **Class II** `exit 10` counterexamples in `2.66–4.63 ms` (`2` CEGIS rounds to fixed point) and harvests trimmed ASCII LRAT UNSAT proofs (`--lrat --no-elim --binary=false`, `exit 20`, `0` RAT steps) directly into `@Nat.rec` GMP `OctTrie` streams (`checkLratPass1Clean`, `0` `._unsafe_rec` constants).
4. **`192.4x` LRAT compression via 1-bit carry-conservation Mealy transducer slicing under Lean `v4.34.1`'s `200,000`-heartbeat `by rfl` ceiling (`Basis: execution + derived`):**
   - Monolithically bit-blasting multi-accumulator unrolled loop steps forces CDCL SAT to refute 4-input and 6-input ripple-carry reassociation (`(acc0 + c0 + c2) + (acc1 + c1 + c3) = (acc0 + acc1) + (c0 + c1) + (c2 + c3)`), exploding from `585` RUP steps on 3-operand `PipelinedMac` (which already hits Lean `v4.34.1`'s default `200,000`-heartbeat `Meta.whnf` cap under `by rfl` due to `1,171` core clauses) to **`16,112` RUP steps (`2.21 MB`)** on `2x`-unrolled `DotMaddubsUnroll2` and **`49,259` RUP steps (`6.97 MB`)** on `4x`-unrolled `ByteSumUnroll4`.
   - Factoring multi-accumulator step obligations into a **1-bit 3-operand carry-conservation Mealy transducer** (`sum2(c_in) = sum2(d_in) -> s_L = s_R ∧ sum2(c_out) = sum2(d_out)`) plus full-width stride/exit control shrinks `ByteSumUnroll4` from `49,259` to **`256` RUP steps (`33.6 KB`, `192.4x` fewer steps)** and `DotMaddubsUnroll2` from `16,112` to **`155` RUP steps (`26.4 KB`, `103.9x` fewer steps)**. All `6 / 6` synthesized `AutoLoop_*.lean` modules (`11.8–34.8 KB`, `0` manual invariant LOC, `type_hints == 0`, transitive axioms `['Quot.sound', 'propext']`) discharge `cegisCert_ok` via plain **`by rfl`** (`0` tactic flags, `2.67–10.12 s` compile, `0.68–2.69 s` private-level kernel replay).

## Applicability

This report governs automated refutation, executable Rust regression synthesis, and zero-external-SMT loop-invariant generation for Rust `core::arch` SIMD and `asm!` / `naked_asm!` verification workflows.

### Examined Subjects and Their Relationships

- **Lean 4 kernel, `Meta.whnf` reducer, and private-level replay (`leanprover/lean4`):** Commit `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`), invoked single-threaded under `-DElab.async=false -Ddebug.skipKernelTC=false -j1` with default `maxHeartbeats = 200000` and default `maxRecDepth = 512` (zero `set_option` overrides), and audited via `importModules ... (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)` followed by `base.toKernelEnv.replay`.
- **Bundled SAT solver binary (`lean-4.34.1-linux-x86_64`):** `bin/lean` (SHA-256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`) and `bin/cadical` (`CaDiCaL 2.1.2`, SHA-256 `8e92f427cfb72072fc605ec6d5f641443c35921b29c39ab2f027776cd533afce`), invoked directly in dual polarity: `-q` (`exit 10` `v ...` literal models for counterexample synthesis and Class II pruning) and `-q --lrat --no-elim --binary=false` (`exit 20` ASCII LRAT proofs for `Pass1GmpLrat` UNSAT harvesting) with zero external SAT/SMT solvers installed.
- **Rust compiler and x86-64 target execution (`rust-lang/rust`):** `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `LLVM 23.1.1`) on `x86_64-unknown-linux-gnu` (`Intel Xeon @ 2.60 GHz`, Linux `7.1.6`, `-C opt-level=3 -C target-feature=+avx2,+bmi2,+adx,+pclmulqdq`).
- **Verification boundary (`joshlf/anneal`):** Evaluated against Anneal's Pass-1 trust invariants (`c131b320eeeb26ef692e5afd5ec8db49ee518613`): `prelude` + `Init.*` foundation isolation, Statement-Origin Separation (`type_hints == 0` on locked theorem types), rejection of `isUnsafe || isPartial` (`._unsafe_rec`) constants, and the three-axiom ceiling (`{propext, Classical.choice, Quot.sound}`).

### Relationship to Neighboring Corpus Coverage

- Extends positive UNSAT bit-blasting and $\mathbb{F}_2$ basis equivalence (`gmp-bitset-lrat-tseitin-bitblasting-and-f2-linear-simd-certificates-in-lean4`) to **negative refutation polarity** (`exit 10` coupled shrinking, constructive $\mathbb{F}_2$ basis mismatch extraction, and IEEE-754 `vminss` bit-blasting) and **inductive loop CEGIS**.
- Extends deterministic scalar MIR counterexample triage (`counterexample-trace-shrinking-span-blame-assignment-and-agent-proof-repair`, where `ValidChoice := c = 0` and live Lean elaboration was unexamined) to **four-channel demonic machine-code nondeterminism**, kernel-compiled Lean `v4.34.1` refutation + Class I/II separation theorems, and runnable `PROT_NONE` guard-page Rust `#[test]` generation.
- Eliminates the `22–74` LOC of manual relational loop invariants (`DotLoopInv`, etc.) remaining after straight-line `HintCert` reflection (`zero-tcb-verified-asm-macros-and-core-arch-mir-equivalence-stability`) while preserving `type_hints == 0` and zero TCB growth.

## Findings

### 1. Four-Channel Demonic Machine-Code Equivalence and Dual-Polarity Counterexample Shrinking

`Basis: normative + source + execution + derived`

#### 1.1 Why Scalar MIR Counterexample Semantics Miss Machine-Code Bugs

Single-threaded safe Rust MIR is deterministic (`ValidChoice := c = 0`), so any bug is witnessed by an input value alone. Machine-code equivalence (`MIR <-> ISA`) introduces four environmental and relational nondeterminism channels mechanized tactic-free in [`support/lean/DemonicIsaModel.lean`](support/lean/DemonicIsaModel.lean):

1. **Sub-page pointer alignment (`pageMisalign ∈ [0, 4096)`):** An unaligned `width`-byte vector load (`vmovdqu`, `width = 32`) on a slice `[ptr, ptr + len)` crosses into a potentially unmapped (`PROT_NONE`) `4096`-byte page whenever `len == 0 && mis + width > 4096` or `0 < len < width && (mis + len - 1) / 4096 < (mis + width - 1) / 4096` (`crossesUnmappedPage`). Standard heap/stack `Vec<u8>` unit tests almost never place `ptr + len` within `31` bytes of an unmapped page boundary.
2. **Same-page out-of-slice granule slack (`slackBytes`):** When `crossesUnmappedPage = false`, hardware loads still read `width - len` bytes past `ptr + len` inside the mapped page (`demonicLoadGranule`). Off-by-one lane masks silently pass all zero-initialized memory tests (`slack == 0`) and fail only under non-zero demonic slack.
3. **Architecturally undefined x86-64 registers and `RFLAGS` (`bsfUndefDst`, `imulUndefZf`):**
   - Intel SDM Vol. 2A (*BSF — Bit Scan Forward*) leaves the destination register **undefined** when the source operand is `0` (`ZF := 1`), whereas `tzcnt` deterministically writes operand width (`64`). Direct execution on `Intel Xeon @ 2.60 GHz` confirms that `bsf dst, 0` leaves `dst` unchanged (`0xdeadbeefcafebabe` vs. `tzcnt = 64`).
   - Intel SDM Vol. 2A (*IMUL — Signed Multiply*) defines `CF` and `OF` (`CF = OF = (product != sign_extend(low))`) while leaving **`SF`, `ZF`, `AF`, and `PF` undefined**. Probing `imul` on `Intel Xeon @ 2.60 GHz` across four `(prior_ZF, a, b)` combinations reveals that hardware `imul` **unconditionally clears `ZF` to `0`**—even when `a = 0, b = 0` (`prod = 0x0, zf_after = 0` after `xor eax, eax`) and when `a = 2^32, b = 2^32` (`low64 = 0x0, zf_after = 0`)—so `imul reg, rhs; jz .Lzero` silently never branches on zero products on live Xeon silicon!
4. **2-Safety Hyperproperty (`CtLeakEquiv`):** Constant-time equivalence quantifies over *pairs* `(sec1, sec2)` sharing public parameters `pub` (`(exec pub sec1).2 = (exec pub sec2).2`). Optimistic SIMD fast-paths (`if _mm_movemask_epi8(cmp) == 0xffff { return true; }`) satisfy `100%` of single-trace functional checks (`cadical` returns `exit 20` `UNSAT` in `2.88 ms`) and are refutable only in the 2-safety product circuit (`exit 10` `SAT` in `3.58 ms`).

#### 1.2 Three Counterexample-Shrinking Failure Modes and Their Remedies

Benchmarking raw `CaDiCaL 2.1.2` (`exit 10`), 1-bit local coordinate shrinking, two-tier SAT-assumption coupled shrinking, and constructive $\mathbb{F}_2$ unit-basis extraction across 12 SIMD/`asm!` bugs ([`support/synth_dual_counterexamples.py`](support/synth_dual_counterexamples.py), [`support/dual_counterexamples_results.json`](support/dual_counterexamples_results.json)) isolates three distinct failure modes:

1. **`CaDiCaL 2.1.2` lucky-phase all-ones inflation (`hw_raw = 63..383`, even with `--phase=0`):**
   By default (`--phase=1`) *and* even when passed `--phase=0`, `CaDiCaL 2.1.2`'s local lucky-phase search (`--lucky=1`) tests all-zeros followed immediately by all-ones, filling unconstrained input bytes, limbs, and slack words with `0xff` (`hw_raw = 383 / 384` bits on Bug 7; `260 / 260` bits on Bug 9; `128 / 128` bits under both `--phase=1` and `--phase=0` on Bug 8).
2. **1-bit coordinate stalling on coupled constraints + premature LSB pinning:**
   - On Bug 7 (`ct_vpmovmskb_early_exit_leak`), raw `CaDiCaL` emits `pub = [0xff; 16], sec1 = [0xff; 16], sec2 = [0xff, ..., 0xfe]` (`hw_raw = 383`). Flipping *any single bit* of `pub` or `sec1` breaks `pub == sec1`, collapsing both traces to `"not_taken"` and losing the leak—stalling 1-bit shrinking at **`hw_1bit_local = 256`**. Assuming whole-byte chunks `pub[i] == 0` inside `CaDiCaL` automatically propagates `sec1[i] := 0`, shrinking to **`hw_shrunk = 1`** (`256x` reduction).
   - On Bug 9 (`adcx_adox_carry_swap`), 1-bit shrinking stalls at `hw_1bit_local = 130` (`t0, t1 != 0`), whereas SAT chunk zeroing clears `t0 = 0, t1 = 0` completely and discovers the algebraic identity $15 \times \text{0x1111\_1111\_1111\_1111} = 2^{64} - 1$ (`a0 = 0x1111111111111112, a1 = 0x1111111111111111, b = 15`, `hw_shrunk = 36`), generating `CF2 = 1` and `OF2 = 0` purely from `mulx` products.
   - *Premature opportunistic LSB pinning trap:* During chunk-zeroing, if the shrinker pins every bit that *happened* to evaluate to `0` in an intermediate SAT model (`pinned_zero.update(u for u in bits if u not in model)`), an intermediate byte `lut0 = 0x80` (`bit 7 = 1, bit 0 = 0`) pins `bit 0 = 0` prematurely, blocking the subsequent MSB-to-LSB sweep from trading `bit 7 -> bit 0` (`128 -> 1`). Restricting `pinned_zero` strictly to explicitly verified zero chunks and already-swept MSBs yields true lexicographic minima (`lut0 = 1` on Bug 10; `x = 1, n = 64` on Bug 12; `a = 0x80000000 = -0.0f32, b = 0x0 = +0.0f32`, `hw_shrunk = 1` on Bug 11).
3. **CDCL SAT shrinking stall (`> 3,020 ms`) vs. `1.22 ms` $\mathbb{F}_2$ unit-basis extraction on `pclmulqdq` (`Bug 8`):**
   On 128-bit `vpclmulqdq` 2-lane CRC-64 folding (`clmul64(h, K1) ^ clmul64(l, K2)` with a 1-bit polynomial constant typo `K2 ^ (1 << 62)`), raw `CaDiCaL` finds `h = l = u64::MAX` (`hw = 128`) in `12.27 ms`, **but SAT-guided shrinking times out (`> 3,020.56 ms`) on its very first chunk query (`l == 0`)**: setting `l = 0` leaves `clmulKaratsuba64(h, K1) != clmul64(h, K1)` on the bug-free lane, an `UNSAT` 64-bit XOR parity tree whose CDCL resolution proof exceeds `20 s`. By contrast, constructive $\mathbb{F}_2$-linear unit-basis search (`find_f2_linear2_witness`, the refutation dual of `F2SimdCert.checkF2Linear2_sound`) evaluates `(1 << i, 0)` for $0 \le i < 64$ (`64` exact matches in GMP/int arithmetic, zero SAT calls) and hits `(0, 1)` on evaluation `65` in **`1.223 ms`** (`hw_shrunk = 1`, `> 2,460x` faster than SAT shrinking).

### 2. Quantitative Matrix Across 12 SIMD / `asm!` Bugs, `[propext]` Kernel Refutations, and `< 3 ms` Guard-Page Rust Tests

`Basis: execution + source`

| # | Bug Archetype (`slug`) | Failure Class | Engine | Gates / Clauses | Solve + Shrink (`ms`) | Bit Weight (`Raw` $\to$ `1-Bit` $\to$ `Final`) | Synthesized Minimal Witness |
| ---: | :--- | :--- | :--- | ---: | ---: | :---: | :--- |
| 1 | `vpmaddubsw` signed `i16` pair saturation (`vpmaddubsw_i16_sat`) | Class Ib | CaDiCaL | `1,514` / `5,089` | `59.05 + 286.89` | `25` $\to$ `24` $\to$ **`18`** | `u0=255, u1=254, s0=64, s1=65` (`32,830` $\to$ `32,767`; canonical `255*(64+65)=32,895` also refuted) |
| 2 | Mycroft SWAR zero-byte count borrow bleed (`swar_borrow_bleed`) | Class Ib | CaDiCaL | `341` / `1,136` | `2.84 + 17.20` | `6` $\to$ `1` $\to$ **`1`** | `x = 0x100` (`7` zero bytes; borrow across byte `1 = 0x01` inflates count to `8`) |
| 3 | `bsf` vs. `tzcnt` zero-mask undef dst (`bsf_zero_undef_dst`) | Class Ia/Ib | CaDiCaL | `781` / `2,352` | `2.83 + 0.02` | `0` $\to$ `0` $\to$ **`0`** | `x = 0, bsfUndefDst = 0` (`0 != 64`; preserves `0xdeadbeef...` poison on Xeon) |
| 4 | `jz` / `sete` on undef `ZF` after `imul` (`imul_zf_undef_branch`) | Class Ia/Ib | CaDiCaL | `707` / `2,349` | `2.72 + 3.73` | `33` $\to$ `3` $\to$ **`0`** | `a = 0, b = 0, imulUndefZf = false` (`0*0 = 0`, Xeon hardware clears `ZF = 0`) |
| 5 | Unguarded `len == 0` `vmovdqu` cross-page fault (`vmovdqu_cross_page_sigsegv`) | Class Ia | CaDiCaL | `155` / `531` | `2.02 + 29.75` | `8` $\to$ `8` $\to$ **`8`** | `len = 0, pageMisalign = 4065` (`4065 + 32 = 4097 > 4096` $\to$ `PROT_NONE` `SIGSEGV`) |
| 6 | Off-by-one shift mask slack bleed (`off_by_one_tail_mask_slack`) | Class Ib | CaDiCaL | `1,069` / `3,304` | `3.89 + 238.73` | `131` $\to$ `2` $\to$ **`2`** | `len = 1, slice = [0], slack0 = 1` (`!0u64 >> ((7-len)*8)` reads `0x0100 != 0`) |
| 7 | Optimistic `vpmovmskb` early-exit leak (`ct_vpmovmskb_early_exit_leak`) | Class Ib-2Safety | CaDiCaL (2x) | `511` / `1,792` | `3.58 + 159.28` | `383` $\to$ `256` $\to$ **`1`** | `pub = [0;16], sec1 = [0,..,0,1], sec2 = [0;16]` (1-trace `UNSAT` in `2.88 ms`; 2-trace leaks) |
| 8 | `pclmulqdq` CRC-64 fold poly bit-flip (`pclmulqdq_crc64_poly_bitflip`) | Class Ib | `F2BasisSimd` | `6,922` / `27,573` | **`1.22 + 0.00`** *(SAT shrink `>3,020`)* | `128` $\to$ `128` $\to$ **`1`** | `h = 0, l = 1` (`65` $\mathbb{F}_2$ unit-basis evals; SAT shrink stalls on `l == 0` `UNSAT` lane) |
| 9 | `mulx` + `adcx`/`adox` carry-flag swap (`adcx_adox_carry_swap`) | Class Ib | CaDiCaL | `3,218` / `10,756` | `10.22 + 1112.70` | `260` $\to$ `130` $\to$ **`36`** | `t0=0, t1=0, b=15, a0=0x1111111111111112, a1=0x1111111111111111` (`CF2=1, OF2=0`) |
| 10 | `vpshufb` bit-7 lane zeroing (`vpshufb_bit7_zeroing`) | Class Ib | CaDiCaL | `410` / `1,240` | `2.52 + 83.32` | `136` $\to$ `2` $\to$ **`2`** | `lut0 = 1, idx0 = 128` (`0x80` clears XMM lane `0` instead of indexing `lut[0] = 1`) |
| 11 | `vminss` operand-order swap (`vminss_nan_signed_zero_swap`) | Class Ib | CaDiCaL | `655` / `2,121` | `2.42 + 14.26` | `63` $\to$ `9` $\to$ **`1`** | Signed-zero: `a=-0.0f32 (0x80000000), b=+0.0f32`; NaN: `a=0x7f800001, b=+0.0f32` |
| 12 | BMI2 `bzhi` `>= 64` saturation vs. `shl` (`bzhi_count_ge64_vs_shift`) | Class Ib | CaDiCaL | `697` / `2,220` | `3.84 + 61.25` | `72` $\to$ `2` $\to$ **`2`** | `x = 1, n = 64` (`_bzhi_u64(1, 64) == 1` vs. `1 & ((1u64 << (64 & 63)) - 1) == 0`) |

All 12 witnesses emit dual machine-checked artifacts automatically:

1. **Pure `[propext]` Lean `v4.34.1` kernel refutation + Class I/II separation ([`support/lean/RefuteSimdAsm12.lean`](support/lean/RefuteSimdAsm12.lean)):**
   `DemonicIsaModel.lean` (`16,320 B`, `0` tactics, `1,048.43 ms` compile) and `RefuteSimdAsm12.lean` (`7,983 B`, `462.74 ms` compile) discharge `refute_bug01`..`refute_bug12` plus `bug07_functional_on_witness_pair` and `triage_classII_noninductive_yet_program_correct` (`¬ StepInductive candidateInvCoincidental ... ∧ TotalMirAsmEquiv triageHealthyPre ...`). Fresh `(trustLevel := 0, plugins := #[], loadExts := false, level := .private)` `base.toKernelEnv.replay` verifies all `21` declarations in **`36.55 ms`** using **only `['propext']`** (`0` `Classical.choice`, `0` `Quot.sound`, `0` native axioms).
2. **`2.58 ms` in-process `PROT_NONE` guard-page Rust `#[test]` suite ([`support/generated_bug_repros.rs`](support/generated_bug_repros.rs)):**
   Forking a child process (`fork() + waitpid()`) around `mmap` + `mprotect(PROT_NONE)` to trap cross-page `vmovdqu` `SIGSEGV` costs **`161.50 ms`** per fault due to Linux VMA/page-table cloning. Installing an in-process `sigaction(SIGSEGV, SA_SIGINFO | SA_NODEFER)` handler backed by `__sigsetjmp` / `siglongjmp` that records `(*info).si_addr` and jumps cleanly back to the test harness verifies both `sig == 11` and `FAULT_ADDR == guard_page as usize`, executing all **12 / 12** hardware tests in **`2.58 ms` median wall time** (`[2.40, 2.52, 2.58, 2.63, 9.59] ms` across 5 runs; `153.88 ms` `rustc 1.99.1` compile).

### 3. Zero-SMT Trace-Matrix Schedule Inference, Houdini Filtering, and Bundled-CaDiCaL Loop CEGIS

`Basis: execution + source + derived`

[`support/synth_loop_cegis.py`](support/synth_loop_cegis.py) replaces external Horn solvers (`Z3/Spacer`) with a three-stage loop-invariant synthesis pipeline backed solely by concrete Python micro-traces (`len ∈ 0..64`), bundled `CaDiCaL 2.1.2`, and [`support/lean/UntrustedCegisHints.lean`](support/lean/UntrustedCegisHints.lean):

```text
  (ref_fn, opt_loop)
         │
         ▼  Phase A: Concrete Micro-Traces (`len ∈ 0..64`, 3–4 traces/loop)
  Header Snapshot Matrix `(k, cursor, regs, flags, ref_prefix)`
         │
         ▼  Phase B: Schedule Alignment `(U, mu, earlyExit)` + Houdini Filter
  Candidate CutBox `C_trace` (retains coincidental small-trace bounds!)
         │
         ▼  Phase C: Bundled `CaDiCaL` Inductive CEGIS (`StepVC` / `ExitVC`)
  ┌────► `exit 10` (SAT) ──► Triage `s_syn` as Class II ──► Drop/Refine Clause ─┐
  │                                                                             │
  └────────────────────────── Iterate (`2` rounds) ◄────────────────────────────┘
         │
         ▼  `exit 20` (UNSAT): `cadical -q --lrat --no-elim --binary=false`
  Backward Core Trim + Slot Recycling (`max_slot ≤ 443`, `oDepth = 5`)
         │
         ▼  Emit `AutoLoop_<Name>.lean` (`0` manual invariant LOC, `type_hints = 0`)
  `by rfl` (`checkLratPass1Clean`, `0` `._unsafe_rec`, `[Quot.sound, propext]`)
```

1. **Automatic Schedule & Lagged Conservation Discovery (`mu = 1` on `PipelinedMac`):**
   In software-pipelined multiply-accumulate (`PipelinedMac`), the prologue preloads `stage := (a[0] * b[0]) % 2^64` and advances `idx := 1` before the first loop-header hit. Naive `mu = 0` matching (`acc == macPrefixSpec k`) fails immediately on micro-traces (`acc = 0 != a[0]*b[0]` at `k = 1`) and is pruned by Houdini. Testing stage-drain linear combinations discovers `mu = 1`: `(acc + stage) % 2^64 == macPrefixSpec aMem bMem k`. Crucially, this **single lagged conservation equation is self-inductive without an auxiliary `stage == a[k-1]*b[k-1]` clause**: in iteration `k`, `acc' := (acc + stage) % 2^64` equals `macPrefixSpec k` and `stage' := (a[k] * b[k]) % 2^64`, so `(acc' + stage') % 2^64 = macPrefixSpec (k + 1)` directly, and epilogue drain `rax := (acc + stage) % 2^64` yields `macPrefixSpec n` at `k = n`.
2. **Class II Coincidental-Clause Pruning & Missing-Pin Detection via `CaDiCaL`:**
   - Micro-traces over small lengths (`len ≤ 64` / `blocks ≤ 3..6`) leave false coincidental bounds in `C_trace` (`rcx <= 192`, `k <= 3`, `idx <= 6`, `k <= 4`, `k1 <= 6`). Bundled `CaDiCaL` refutes each coincidental clause's `StepVC` (`exit 10`) in **`2.66–4.63 ms`** (`witness: k = 3, blocks = 15, rcx = 192` on `ByteSumUnroll4`), classifies the witness as **Class II** (unreachable from bounded trace runs yet non-inductive for general `blocks`), and converges in `2` CEGIS rounds across all 6 loops.
   - Conversely, withholding the constant vector register pin `ymm2 == ones16` on `DotMaddubsUnroll2` causes `CaDiCaL` to falsify `(ymm0Sum + ymm1Sum) == dotPrefix` in **`3.64 ms`** (`exit 10` with `ymm2 != 1` corrupting `vpmaddwd`), confirming that CEGIS detects missing register-pin invariants immediately.

### 4. Multi-Accumulator Ripple-Carry RUP Explosion vs. 1-Bit Carry-Conservation Transducer Slicing

`Basis: execution + derived`

Measuring real `CaDiCaL 2.1.2` ASCII LRAT proofs (`--lrat --no-elim --binary=false`) across all 6 hot loops ([`support/loop_cegis_results.json`](support/loop_cegis_results.json)) uncovers a sharp CDCL resolution cliff on unrolled multi-accumulator loops—and an exact zero-SMT remedy:

- **Why `2x`- and `4x`-unrolled multi-accumulator loops explode monolithically:**
  On 3-operand `PipelinedMac`, `(acc + stage)` is shared structurally on both sides of `(acc + stage) + next == ref + next`, yielding `585` RUP steps (`77.7 KB`). However, in `2x`-unrolled `DotMaddubsUnroll2` (`(y0 + d0) + (y1 + d1) == (y0 + y1) + (d0 + d1)`, 4 operands) and `4x`-unrolled `ByteSumUnroll4` (`(acc0 + c0 + c2) + (acc1 + c1 + c3) == (acc0 + acc1) + (c0 + c1) + (c2 + c3)`, 6 operands), hardware updates parallel accumulator trees while the scalar spec folds sequentially. Refuting 16-bit multi-operand ripple-carry reassociation monolithically blows up to **`16,112` RUP steps (`2,206.8 KB`)** on `DotMaddubsUnroll2` and **`49,259` RUP steps (`6,967.1 KB`)** on `ByteSumUnroll4`. Even more stringently, under plain **`by rfl`** (`Meta.whnf`, `0` tactic flags, default `maxHeartbeats = 200000`), `PipelinedMac`'s monolithic `585`-RUP / `1,171`-clause certificate already exceeds `200,000` heartbeats (real CDCL hint fan-in + `1,171` `octSet` insertions consume `~2.1x` more WHNF reductions per RUP step than synthetic `6`-hint microbenchmarks).
- **`192.4x` compression via 1-bit 3-operand carry-conservation Mealy transducer slicing:**
  Any $w$-bit ripple-carry tree reassociation `(x + y) + z = x + (y + z)` reduces inductively to a **1-bit Mealy transducer** over `(x_i, y_i, z_i) ∈ {0, 1}^3` and carry pairs `(c_0, c_1), (d_0, d_1) ∈ {0, 1}^2` asserting `c_0 + c_1 = d_0 + d_1 -> s_L = s_R ∧ co_0 + co_1 = do_0 + do_1` ($2^7 = 128$ states!). Pairing this 1-bit carry-transducer VC with full-width stride/guard/exit control compresses `ByteSumUnroll4` from `49,259` to **`256` RUP steps (`33.6 KB`, `192.4x` fewer steps, `207.1x` smaller)** and `DotMaddubsUnroll2` from `16,112` to **`155` RUP steps (`26.4 KB`, `103.9x` fewer steps, `83.6x` smaller)**, bringing **all `6 / 6` loops** comfortably inside Lean `v4.34.1`'s `by rfl` `200,000`-heartbeat budget:

| Hot-Loop Archetype (`AutoLoop_*.lean`) | Inferred Schedule `(U, mu, earlyExit)` | Cands (`Init` $\to$ `Houdini` $\to$ `CEGIS`) | Monolithic 16b RUP (`Bytes`) | Sliced `Pass1GmpLrat` RUP (`Core` / `Slot`) | Module Size (`KB`) | Manual Inv LOC | `by rfl` Compile (`s`) | Private Replay (`ms`, Axioms) |
| :--- | :---: | :---: | ---: | ---: | ---: | :---: | ---: | :--- |
| `ByteSumUnroll4` (`4x` `vpsadbw` + `vpaddq`) | `(64, 0, false)` | `6` $\to$ `5` $\to$ **`4`** | `49,259` (`6,967 KB`) | **`256`** (`421` / `443`) | `34.8` | **`0`** | `10.12` | `2,691.6` (`Quot.sound, propext`) |
| `DotMaddubsUnroll2` (`2x` `vpmaddubsw` + `ymm2=1`) | `(64, 0, false)` | `7` $\to$ `6` $\to$ **`5`** | `16,112` (`2,207 KB`) | **`155`** (`389` / `411`) | `27.6` | **`0`** | `7.62` | `2,354.3` (`Quot.sound, propext`) |
| `PipelinedMac` (SW-pipelined 64b MAC, **`mu = 1`**) | `(1, 1, false)` | `5` $\to$ `4` $\to$ **`3`** | `585` (`77.7 KB`)\* | **`186`** (`363` / `364`) | `22.7` | **`0`** | `5.41` | `1,593.8` (`Quot.sound, propext`) |
| `AdcLimbCarry` ($N$-limb 64b `adc`, `RFLAGS.CF`) | `(1, 0, false)` | `5` $\to$ `4` $\to$ **`3`** | `1,880` (`243.6 KB`) | **`122`** (`338` / `339`) | `21.3` | **`0`** | `5.41` | `1,602.1` (`Quot.sound, propext`) |
| `MemchrEarlyExit` (`16`B `vpmovmskb` + `tzcnt`) | `(16, 0, true)` | `4` $\to$ `4` $\to$ **`3`** | `232` (`47.6 KB`) | **`91`** (`213` / `214`) | `11.8` | **`0`** | `2.67` | `684.1` (`Quot.sound, propext`) |
| `CtCmovScan` (branchless `cmove` + **2-safety**) | `(1, 0, false)` | `5` $\to$ `5` $\to$ **`4`** | `473` (`69.7 KB`) | **`149`** (`273` / `274`) | `21.0` | **`0`** | `5.56` | `1,412.5` (`Quot.sound, propext`) |

\* *Monolithic `585` RUP / `1,171` core-clause `PipelinedMac` hits Lean `v4.34.1`'s default `200,000`-heartbeat `Meta.whnf` cap under `by rfl`; 4-bit stage-drain slicing (`186` RUP / `363` core clauses) compiles in `5.41 s` with zero `set_option` overrides.*

Across all 6 `AutoLoop_*.lean` modules, `ReplayLoopsAudit` verifies `manual_invariant_loc == 0`, `type_hints == 0` (`val_hints ∈ {3, 6}`), `unsafe_rec_constants == 0` (`lrat_checker_unsafe_rec == 0` in `UntrustedCegisHints.checkLratPass1Clean`), `rat_steps == 0`, and transitive axioms strictly `['Quot.sound', 'propext']` (`0` `Classical.choice`).

## Boundaries

- **Known not to apply — SAT-guided counterexample shrinking over wide $\mathbb{F}_2$ polynomial / carryless-multiply (`pclmulqdq`) circuits:** As established on Bug 8, any SAT-shrinking assumption (`l == 0` or low-Hamming-weight cardinality constraint) whose subspace contains zero bugs reduces to an `UNSAT` wide XOR parity problem and stalls CDCL SAT (`> 3,020 ms`, exceeding `20 s` on 64-bit `clmul`). Circuits in the $\mathbb{F}_2$-linear / $\mathbb{F}_2$-bilinear fragment must route both equivalence and counterexample extraction through constructive unit-basis evaluation (`F2BasisSimd`).
- **Known not to apply — Monolithic `by rfl` LRAT replay above `~400–550` real-solver RUP steps (`> 1,000` core clauses) under default `maxHeartbeats = 200000`:** While `decide +kernel` (`Kernel.whnf`) scales past `5,000` RUP steps, flag-free `by rfl` (`Meta.whnf`) hits Lean `v4.34.1`'s `200,000`-heartbeat cap at `585` RUP steps / `1,171` core clauses (`PipelinedMac` monolithic probe). Staying under `by rfl` without `set_option maxHeartbeats` requires 1-bit carry-transducer or 4-bit lane slicing (`≤ 260` RUP steps per `rfl` checkpoint).
- **Known not to apply — Expecting hardware `imul` tests on Intel Xeon to catch stale-`ZF == 1` false positives without demonic flag modeling:** On `Intel Xeon @ 2.60 GHz`, `imul` unconditionally clears `ZF` to `0` (`zf_after = 0` even after `xor eax, eax` on `1 * 1` and `0 * 0`). Native Xeon tests therefore catch `jz`-not-taken on zero products (`a = 0, b = 0`) immediately, whereas catching `jz`-falsely-taken on non-zero products (`a = 1, b = 1, imulUndefZf = true`) requires the formal `DemonicEnv` model (or an emulator/ISA checker modeling microarchitectures that leave `ZF = 1` stale).
- **Unsupported — Non-template-expressible quantified heap/graph invariants without predicate-grammar extension:** Zero-SMT trace-matrix + Houdini + CaDiCaL CEGIS synthesizes invariants inside a finite candidate template grammar (affine pointer/counter strides, dual/pipelined accumulator homomorphisms, CPU flag positional weights, chunked prefix negations `noMatchBefore`, and 2-safety lockstep equalities). Arbitrary nested alternating-quantifier or recursive tree/graph separation-logic invariants are **unsupported** without supplying domain-specific candidate predicates to the grammar.
- **Not examined — Multi-nested loop nests (e.g., 2D tile/matrix GEMM outer-inner `CutBox` coupling) and data-dependent variable-stride UTF-8/VarInt state machines:** All 6 benchmarked hot loops have constant per-backedge pointer/index stride `U ∈ {1, 16, 64}`; variable-advance finite-state decoders (`1..4` bytes/iter) and nested 2D/3D loop hierarchies were **not examined**.
- **Unknown — Exact microarchitectural `imul` `ZF` behavior on AMD Zen 4/5 and Intel E-core (Gracemont/Skymont) silicon:** Hardware execution was observed on `Intel Xeon @ 2.60 GHz`; whether AMD Zen or hybrid E-cores also clear `ZF` or compute partial parity/zero flags on `imul` remains **unknown** from these runs (and irrelevant to soundness once `DemonicEnv` treats `imulUndefZf` demonically).
- **Attractive stronger conclusions not established by the evidence:**
  - *"Zero-SMT loop CEGIS synthesizes arbitrary loop invariants from scratch with zero domain structure":* False. Trace-matrix + Houdini + `CaDiCaL` succeeds in `52 ms–5.66 s` precisely because SIMD/assembly hot loops draw from a structured relational vocabulary (pointer stride, vector-lane fold = scalar prefix fold, stage lag `mu ∈ {0, 1}`, flag weight, early-exit chunk negation); it does not invent unseen mathematical functions out of thin air.
  - *"Passing the 12-test `generated_bug_repros.rs` suite on fixed Rust code proves equivalence":* False. The synthesized Rust `#[test]` suite is a concrete **refutation** oracle (`¬ Equiv` witness reproduction in `2.58 ms`); positive correctness still requires the kernel-replayed Lean `v4.34.1` theorem.

## Evidence

### Primary Upstream Sources and Specifications

- **Lean 4 kernel reducer, replay, and bundled CaDiCaL (`normative` + `source`):** `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `src/kernel/type_checker.cpp` (`reduce_nat` GMP bitset operations), `src/Lean/Replay.lean` (`toKernelEnv.replay`, `isUnsafe || isPartial` constant handling), and `lean-4.34.1-linux-x86_64/bin/cadical` (`CaDiCaL 2.1.2`, SHA-256 `8e92f427cfb72072fc605ec6d5f641443c35921b29c39ab2f027776cd533afce`).
- **Rust toolchain & `stdarch` intrinsics (`normative` + `source`):** `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`, `LLVM 23.1.1`), `core::arch::x86_64` (`_mm_maddubs_epi16`, `_mm256_loadu_si256`, `_mm_movemask_epi8`, `_mm_clmulepi64_si128`, `_mm_shuffle_epi8`, `_mm_min_ss`, `_bzhi_u64`) and `core::arch::asm!`.
- **Intel 64 and IA-32 Architectures Software Developer's Manual (`normative`):** Vol. 2A/2B specifications for `BSF` (undefined destination when source is `0`), `IMUL` (undefined `SF`, `ZF`, `AF`, `PF`), `VPMADDUBSW` (`i16` signed saturation of adjacent pairs), `VPSHUFB` (bit-7 control-byte lane zeroing), `VMINSS` (second-operand selection on `NaN` or `-0.0 == +0.0` tie), and `BZHI` (`imm8 >= 64` saturation).
- **Anneal Pass-1 trust model (`normative` + `source`):** `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `THREAT_MODEL.md` and `trusted/audit/TrustedBoundary.lean` (`Statement-Origin Separation`, `ensureReplayableConstant`, and 3-axiom foundation lock).

### Preserved Support Artifacts (`support/`)

All synthesis runs, Lean `v4.34.1` compilations, private-level kernel replays, and `rustc 1.99.1` guard-page hardware tests were executed on `2026-11-21` on `x86_64-unknown-linux-gnu` (`Linux 7.1.6`, `Intel Xeon @ 2.60 GHz`):

| Path | Size (`B`) | SHA-256 | Role |
| :--- | ---: | :--- | :--- |
| [`support/synth_dual_counterexamples.py`](support/synth_dual_counterexamples.py) | `74,902` | `382efcc01951c1fe95c491275eb7f64cb7c73221ba6ec2dc47e2e8f74c49e5ed` | Tseitin bit-blaster, `CaDiCaL exit 10` coupled shrinker, $\mathbb{F}_2$ unit-basis witness extractor, Lean/Rust emitter, and replay harness |
| [`support/dual_counterexamples_results.json`](support/dual_counterexamples_results.json) | `8,753` | `bbf03b7598a35e5d5638bd328460246602416b7c47a47167a3e8b6e91a4db030` | Complete telemetry for all 12 bugs, Lean kernel replay (`36.55 ms`), and Rust test timing (`2.58 ms`) |
| [`support/generated_bug_repros.rs`](support/generated_bug_repros.rs) | `11,455` | `32fa162529ff071da45ce6edfbdefb8ad5a372d3de0711e040b90af459c28870` | Standalone `rustc 1.99.1 --test` suite with `mmap`/`mprotect(PROT_NONE)` `sigsetjmp` guard pages & slack poisoning (`12 / 12` caught) |
| [`support/synth_loop_cegis.py`](support/synth_loop_cegis.py) | `62,981` | `5b8b4252dea8c32ea7c8a55b3bfe38a91d6da169fc3a6381fc1f8ba22e3d9bca` | Zero-SMT trace-matrix schedule/Houdini + `CaDiCaL` CEGIS + ASCII LRAT backward core trimmer/recycler across 6 hot loops |
| [`support/loop_cegis_results.json`](support/loop_cegis_results.json) | `12,250` | `b9a2dda9ae3c13102b5778666cca382757ee2d03850edd500eab51787c6edc06` | Complete telemetry for all 6 hot loops, monolithic-vs-sliced RUP counts, and private-level kernel replay audits |
| [`support/lean/DemonicIsaModel.lean`](support/lean/DemonicIsaModel.lean) | `16,320` | `786ac97efe438865fe227e85a7b42011e5e7ebe366176b840c2a6faf2da22a22` | Tactic-free `Init.*`-only `TotalMirAsmEquiv`, `CtLeakEquiv`, `DemonicEnv`, `demonicLoadGranule`, and 12 bug models |
| [`support/lean/RefuteSimdAsm12.lean`](support/lean/RefuteSimdAsm12.lean) | `7,983` | `b3aefcc818bd50daa03f7b5a4be805e954cf80bb4981f7ee16ab5c3ebcb84b92` | Kernel-checked `[propext]`-only refutation theorems for all 12 bugs + formal Class II vs. Class I separation |
| [`support/lean/LoopCegisBase.lean`](support/lean/LoopCegisBase.lean) | `12,671` | `6b03b681b19ecead45da47f14e6380fc57dd647b0cf3e369df92894a66e490b1` | Tactic-free `Init.*`-only operational state machines and scalar reference specifications for all 6 hot loops |
| [`support/lean/UntrustedCegisHints.lean`](support/lean/UntrustedCegisHints.lean) | `46,719` | `b89e08ff95bbdc22c867c76644bd3ff6c74b62e4ad329a671a2e0cfdf5fb3467` | `@Nat.rec` `Pass1GmpLrat` checker (`0` `._unsafe_rec`) + `CutBox` combinators (`0` TCB LOC) |
| [`support/lean/AutoLoop_ByteSumUnroll4.lean`](support/lean/AutoLoop_ByteSumUnroll4.lean) | `34,827` | `1878d93d22057d17418b9fd2c7e9f4eeb3b0e5cd43366933b7f70729fa63e0c6` | Auto-synthesized `0`-manual-LOC proof + `256`-step LRAT cert for `4x` `vpsadbw` (`type_hints = 0`) |
| [`support/lean/AutoLoop_DotMaddubsUnroll2.lean`](support/lean/AutoLoop_DotMaddubsUnroll2.lean) | `27,613` | `f917de9ae8b04473f6dbcf4915e0c1f9471589e0220fc7b3c90b34c54b41b668` | Auto-synthesized `0`-manual-LOC proof + `155`-step LRAT cert for `2x` `vpmaddubsw` (`type_hints = 0`) |
| [`support/lean/AutoLoop_PipelinedMac.lean`](support/lean/AutoLoop_PipelinedMac.lean) | `22,674` | `8142b1192c49ccb661ffcf598a900e5fdc2ad05af8d04c2e9530e02bba0ff1e7` | Auto-synthesized `0`-manual-LOC proof + `186`-step LRAT cert for `mu = 1` pipelined MAC (`type_hints = 0`) |
| [`support/lean/AutoLoop_AdcLimbCarry.lean`](support/lean/AutoLoop_AdcLimbCarry.lean) | `21,344` | `23d21ce268fdfa4ed41180a119c9726ed878cb2b11cc10478965986bdf4789cc` | Auto-synthesized `0`-manual-LOC proof + `122`-step LRAT cert for $N$-limb `adc` carry loop (`type_hints = 0`) |
| [`support/lean/AutoLoop_MemchrEarlyExit.lean`](support/lean/AutoLoop_MemchrEarlyExit.lean) | `11,808` | `fbfdd690d2ca1e5d6b16475bc9c55b061f3080b62d187e7602a89354abd9a544` | Auto-synthesized `0`-manual-LOC proof + `91`-step LRAT cert for early-exit `memchr` (`type_hints = 0`) |
| [`support/lean/AutoLoop_CtCmovScan.lean`](support/lean/AutoLoop_CtCmovScan.lean) | `21,028` | `0bc5b0a8c355f371ff3d2c74ac035c90cd8905f47fa462302337a6e9ac16c41d` | Auto-synthesized `0`-manual-LOC functional + 2-safety proof + `149`-step LRAT cert (`type_hints = 0`) |

## Revalidation

1. **Fast Rust 12-bug guard-page reproduction (`< 0.3 s` compile + `< 5 ms` run, `rustc` only):**
   To check whether a newer `rustc`, LLVM backend, or x86-64 CPU alters `bsf(0)`, `imul` `ZF`, cross-page `vmovdqu` `SIGSEGV`, or SIMD intrinsic semantics without rebuilding Lean modules:

   ```bash
   tmpdir="$(mktemp -d)"
   trap 'rm -rf "$tmpdir"' EXIT
   rustc --test -C opt-level=3 -C target-feature=+avx2,+bmi2,+adx,+pclmulqdq \
     support/generated_bug_repros.rs -o "$tmpdir/repros"
   "$tmpdir/repros" --test-threads=1
   ```

   Expected result: `test result: ok. 12 passed; 0 failed` in `< 50 ms`.

2. **Full dual-polarity counterexample synthesis + Lean `v4.34.1` `[propext]` kernel replay (`~5 s`):**

   ```bash
   python3 -B support/synth_dual_counterexamples.py
   ```

   Expected result: exits `0`, confirming `12 / 12` bugs synthesized (`CaDiCaL exit 10` + $\mathbb{F}_2$ unit-basis), `RefuteSimdAsm12` replayed at `(level := .private)` with transitive axioms `['propext']`, and all `12` Rust hardware tests passing in `< 50 ms`.

3. **Full 6-loop zero-SMT trace-matrix + `CaDiCaL` CEGIS + `by rfl` LRAT harvest & private replay (`~45 s`):**

   ```bash
   python3 -B support/synth_loop_cegis.py
   ```

   Expected result: exits `0`, confirming `manual_invariant_loc == 0`, `type_hints == 0`, `lrat_checker_unsafe_rec == 0`, and `['Quot.sound', 'propext']` private-level kernel replay across all `6 / 6` `AutoLoop_*.lean` modules.
