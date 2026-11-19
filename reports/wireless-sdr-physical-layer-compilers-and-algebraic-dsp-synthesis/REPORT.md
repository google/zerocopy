# Wireless Software-Defined Radio Physical-Layer Compilers and Algebraic DSP Synthesis

## Summary

Compiling high-throughput wireless physical layers (`IEEE 802.11a/g/n/ac/ax`, `LTE`, `5G NR`) onto general-purpose CPUs, SIMD units, and FPGAs confronts two interlocking requirements that conventional streaming audio DSLs and general-purpose C/C++ compilers cannot satisfy simultaneously:

1. **Data-dependent mid-packet pipeline reconfiguration under hard microsecond SIFS budgets (`Ziria` / `Blink`)**: Unlike static synchronous dataflow (SDF) graphs, an `802.11a` receiver decodes a 24-bit `PLCP` `SIGNAL` header *mid-packet* (1 BPSK-1/2 OFDM symbol) to discover the modulation (`BPSK`, `QPSK`, `16-QAM`, `64-QAM`), code rate (`1/2`, `2/3`, `3/4`), and payload length of the immediately following OFDM symbols—all while completing receive baseband processing, CRC check, MAC ACK generation, and RX-to-TX radio turnaround inside the normative **`16 μs` IEEE 802.11a Short Interframe Space (`aSIFSTime`)** (`~10.5 μs` net Rx baseband slack after RF/MAC/turnaround overheads).
   - **Ziria** (originally developed under the `Blink` / `*.blk` / `wplc` moniker; Stewart et al., ASPLOS 2015, `dimitriv/Ziria`) resolves this via a **two-level type-and-effect language** separating terminating stateful *computers* `ST (C v) a b` (sequenced monadically via `seq { hdata <- DecodePLCP(); Decode(hdata) >>> ... }`) from non-terminating stream *transformers* `ST T a b` (composed synchronously via `>>>` or split across lock-free inter-thread ring buffers via `|>>>|`).
   - Its multi-pass Haskell compiler (`wplc`) performs **static cardinality analysis** (`Card = SCard CAlpha CAlpha | OCard`), **rate-matching vectorization & mitigator elimination** (`Vectorize.hs`, `PassOptMit`), **iterative pipeline fusion** (`PassFold.hs`, up to 10 fixpoint rounds eliminating intermediate buffers), and **automated bit-to-LUT synthesis** (`AutoLUT.hs` / `LUTAnalysis.hs`) gated by 6 static predicates including `mIN_OP_COUNT = 5` and `mAX_LUT_SIZE_DEFAULT = 256 KiB`. On the 802.11a 7-bit LFSR scrambler (`scramble.blk`), capping vectorization at `repeat <= [8,8]` produces an exact `15-bit -> 15-bit` (`64 KiB`) L1/L2-resident lookup table; widening by just 2 bits (`w = 10`) jumps to `384 KiB` and exceeds the `256 KiB` budget.
   - Ziria intentionally delegates heavy linear-algebraic kernels (`64-point` complex16 OFDM FFT, `FFT.blk:24-29` calling `sora_fft`) and SIMD Viterbi/FEC decoders to external C/intrinsics routines—defining the exact architectural boundary where algebraic DSP synthesis (`SPIRAL`) and SIMD FEC toolboxes (`AFF3CT`) compose with bitstream PHY compilers.
2. **Algebraic Kronecker-product synthesis (`SPIRAL`) and Coq-verified lowering to LLVM IR (`HELIX`)**:
   - **SPIRAL** (Püschel et al. 2005; Franchetti et al. 2018; `spiral-software/spiral-software`) models linear DSP transforms (DFT, DCT, WHT, FIR, Viterbi-adjacent permutations) in **SPL** (Signal Processing Language) and **OL** (Operator Language), rewrites non-terminals via mathematical breakdown rules such as Cooley–Tukey $\mathrm{DFT}_{mn} = (\mathrm{DFT}_m \otimes I_n)\, T^{mn}_n\, (I_m \otimes \mathrm{DFT}_n)\, L^{mn}_m$ (`dft_rules.gi:62-84`), lowers structured matrix algebra into loop/gather/scatter **$\Sigma$-SPL** (`ISum`, `Gath`, `Scat`, `Diag`), and applies target-specific vector (`paradigms/vector`) or streaming FPGA/HDL (`paradigms/stream`, `HDLCodegen`, Milder et al. TODAES 2012) rewriting guided by empirical search.
   - **Fixed-point dynamic-range cliff**: Our executable `Q1.15` 64-point OFDM FFT probe demonstrates the core numerical trade-off in `TFixedPt` synthesis: unscaled saturating `Q1.15` collapses to **`0.25 dB` SQNR** (50 saturation events) on a coherent full-scale tone, whereas conservative per-stage $1/2$ scaling (`>> 1` at all 6 stages) avoids saturation (`80.77 dB` on full-scale tone) at the cost of a **`-28.72 dB` SQNR penalty** (`73.28 dB -> 44.56 dB`) on realistic 12 dB crest-factor-backed-off 48-subcarrier OFDM symbols; adaptive block-floating-point (BFP) recovers the full `73.28 dB` while eliminating overflow.
   - **HELIX** (Zaliva et al., VSTTE 2020 & `arXiv:2604.18593`, 2026; `vzaliva/helix` + `spiral-package-hcol`) decouples untrusted SPIRAL optimization search from formal soundness by formalizing the **HCOL $\to$ $\Sigma$-HCOL $\to$ D$\Sigma$-HCOL (RHCOL/FHCOL) $\to$ Vellvm LLVM IR** compilation chain in Coq using Interaction Trees (`eutt` equivalence) and Flocq/Gappa numerical bounds (`Lemma top_to_LLVM` in `coq/LLVMGen/TopLevel.v:1244-1268`). Crucially, source inspection shows that the pinned Coq artifact proves a *fixed, hard-coded* cyber-physical control benchmark (`DynWin_FHCOL_hard`) with an axiomatized real-to-float bridge at the top level rather than an arbitrary user-supplied FFT/PHY compiler—an essential boundary for verification reuse.

## Applicability

This report integrates direct primary-source inspection across four pinned repositories, six peer-reviewed publications, IEEE 802.11a Clause 17 normative OFDM timing definitions, and a reproducible numerical/timing probe:

- **Direct source-level scope (pinned immutable revisions)**:
  - **Ziria / Blink (`dimitriv/Ziria` @ `ccbb0960737fb86bf51a1d33af8e614ee9700ffe`)**: Haskell compiler `wplc` (`src/Main.hs`, `src/BasicTypes/AstComp.hs`, `src/Opts.hs`, `src/Optimize/{PassFold,AutoLUT}.hs`, `src/Codegen/{LUTAnalysis,CgLUT}.hs`, `src/Vectorize/{Vectorize,CardAnalysis}.hs`, `src/Pipeline/PassPipeline.hs`), production IEEE 802.11a/g WiFi PHY (`code/WiFi/receiver/{receiver,OFDM/FFT,decoding/DecodePLCP,decoding/Decode}.blk`, `code/WiFi/transmitter/scramble.blk`). Note: `Blink` is the original Microsoft Research language/file-extension name (`*.blk`, `BlinkDiff` tool in `wplc.cabal:79-92`) that was published as `Ziria` (`wplc` = Wireless Programming Language Compiler).
  - **SPIRAL (`spiral-software/spiral-software` @ `577b2c1268476c885fbb9984b9e06174f71b5386` and `spiral-software/spiral-package-hcol` @ `b4a0118382e3bba91ecd82a6c667f2cdb6389ceb`)**: GAP-based algebraic rewriting engine (`namespaces/spiral/spl/init.g`, `sigma/{init.g,ol.gi}`, `transforms/dft/{init.g,dft.gi,dft_rules.gi}`, `code/types.gi`, `paradigms/{vector,stream}/init.g`, and `spiral-package-hcol/{init.g,formal_compile.gi}`).
  - **HELIX (`vzaliva/helix` @ `f2373ef4c7b25745d2f85cd89dd58d68d4ce0765`)**: Coq 8.13.2 + Vellvm formalization (`coq/DSigmaHCOL/DSigmaHCOL.v`, `coq/LLVMGen/TopLevel.v`, `README.org`, `Makefile`), corroborated against `arXiv:2604.18593v1` (27 Mar 2026) and VSTTE 2020 (`10.1007/978-3-030-63618-0_3`).
  - **AFF3CT (`aff3ct/aff3ct` @ `0e8ecda8191cec97a6fe86a56de0d957b63b3b04`)**: High-throughput SIMD channel-coding library (LDPC, Polar, Turbo, Reed-Solomon, BCH, convolutional/Viterbi) examined at README/module-interface level to contextualize the FEC half of SDR PHY pipelines.
- **Target domain scope**: Applies to high-rate RF baseband pipelines ($20\text{–}400\text{ MHz}$ sampling rates, $4\ \mu\text{s}$ OFDM symbols, $16\ \mu\text{s}$ SIFS budgets, bit-level scramblers/interleavers/FEC + linear complex-valued transforms). Findings on Ziria's static cardinality vectorization and AutoLUT thresholds apply specifically to finite-state bit/byte kernels and do *not* automatically generalize to variable-length cryptographic parsers or dynamic sparse tensors (see **Boundaries**).

## Findings

### 1. Ziria (`Blink` / `wplc`): Two-Level Control + Dataflow Wireless PHY Compilation

`Basis: source + documentation`

#### 1.1 Why Single-Level SDF Graphs Fail on Real Wireless Receivers

Static Synchronous Dataflow (SDF) frameworks (`GNU Radio`, audio `Faust`, `StreamIt`) assume fixed token production/consumption rates across a static block graph. Real packet-based wireless protocols break this assumption mid-packet:

- In **IEEE 802.11a/g** (`code/WiFi/receiver/receiver.blk:43-73`), a receiver first searches an unbounded sample stream for the short training field (`detectPreamble`), estimates carrier frequency offset and channel taps from the long training field (`LTS`), and then processes OFDM symbols (`DataSymbol >>> FFT >>> ChannelEqualization >>> PilotTrack >>> GetData`).
- At `receiveBits()` (`receiver.blk:43-54`) and `DecodePLCP.blk:30-37`, the receiver consumes **exactly 1 BPSK-1/2 OFDM symbol** (`48` coded bits $\to$ `24` decoded PLCP header bits via `DemapBPSK >>> DeinterleaveBPSK >>> ViterbiSig11a`), parses `struct HeaderInfo { modulation, coding, len, err }`, and **immediately switches** the downstream demodulator, deinterleaver, Viterbi puncturing rate, and CRC byte count (`Decode.blk:45-60`):

```haskell
-- Excerpt from dimitriv/Ziria code/WiFi/receiver/receiver.blk:43-54 & Decode.blk:45-60
fun comp receiveBits() {
  seq { hdata <- DecodePLCP()
      ; Decode(hdata) >>>
        seq { (c : arr[32] bit) <- crc(hdata.len-4, false); check_crc(c) } >>>
        repeat { x <- takes 8; if (not hdata.err) then { emits x; } }
      }
}

fun comp Decode(h : struct HeaderInfo) {
  DemapLimit(0)
  >>> { if (h.modulation == M_BPSK) then DemapBPSK() >>> DeinterleaveBPSK()
        else if (h.modulation == M_QPSK) then DemapQPSK() >>> DeinterleaveQPSK()
        else if (h.modulation == M_16QAM) then DemapQAM16() >>> DeinterleaveQAM16()
        else DemapQAM64() >>> DeinterleaveQAM64() }
  >>> Viterbi(h.coding, h.len+2) >>> descrambler()
}
```

#### 1.2 Two-Level Type System and Computation Algebra

Ziria's internal AST (`src/BasicTypes/AstComp.hs:58-177`) cleanly stratifies computations into two kinds under `GCTy ty`:

| Type Constructor (`AstComp.hs:58-63`) | Mathematical Notation | Meaning & Compositional Laws |
| :--- | :--- | :--- |
| **`CTComp v a b`** | `ST (C v) a b` | **Computer**: Stateful stream computation consuming elements of type `a`, emitting elements of type `b`, and *terminating* with return value `v`. Supports monadic bind `BindMany` (`x <- c1; c2`). |
| **`CTTrans a b`** | `ST T a b` | **Transformer**: Non-terminating stream processor (`repeat c`). Supports synchronous push/pull pipeline composition `Par` (`>>>`). |
| **`CTArrow args ret`** | Computation function | Higher-order parameterized block accepting both expression arguments (`CAExp`) and computation arguments (`CAComp`). |

Look at the exact parallel-composition typing rules documented in `AstComp.hs:106-121`:
- `T >>> T`: `ST T a b` and `ST T b c` $\implies$ `ST T a c` (infinite stream transformer).
- `C >>> T` and `T >>> C`: `ST (C u) a b` composed with `ST T b c` (or vice versa) $\implies$ **`ST (C u) a c`** (terminates as soon as the computer half returns `u`, cleanly shutting down the surrounding streaming pipeline without leaks or dynamic allocation!).
- Notice that `C >>> C` is **disallowed** (ambiguous termination value), forcing clean separation of control ownership between upstream and downstream stages.

#### 1.3 Compilation Pipeline: Fusion, Cardinality Vectorization, AutoLUT, and Multi-Core Thread Splitting

Inspecting `src/Main.hs:133-251`, `src/Optimize/PassFold.hs:107-166`, `src/Vectorize/{Vectorize,CardAnalysis}.hs`, `src/Codegen/LUTAnalysis.hs`, and `src/Pipeline/PassPipeline.hs` yields Ziria's exact end-to-end compilation sequence:

1. **Fixpoint Algebraic Folding (`PassFold.hs:85-166`, max depth 10)**:
   - Runs computation-level rewrites (`elim-seq`, `fold`, `purify`, `purify-letref`, `elim-times`, `times-unroll`, `inline`, `take-emit`, `float-let-par`, `ifdead`, `if-return`) and expression-level rewrites (`for-unroll`, `exp-inlining`, `eval`) to fuse adjacent `>>>` stages into single zero-buffer state machines.
   - In single-threaded fused code (`NeverPipeline` / `MaybePipeline`), `c1 >>> c2` compiles to coroutine-like `tick`/`process` C continuations (`CgProgram.hs`) that pass values in registers or stack variables with **zero dynamic heap allocation** (`wpl_alloc.h` static allocation).
2. **Static Cardinality Analysis & Multi-Rate Vectorization (`CardAnalysis.hs:73-84`, `Vectorize.hs:461-615`)**:
   - Infers `Card = SCard CAlpha CAlpha | OCard` for every simple computer (containing no nested `>>>`), where `CAlpha = CAStatic Int | CAMultOf Int` tracks exact or divisor-multiple input/output token counts per step.
   - Computes compatible scale-up/scale-down vectorization candidates (`compSFDU`, `compSFUD`, `compSFDD` in `Vectorize.hs:462-467`) across `>>>` boundaries, respecting programmer annotations `VectAnn = Rigid Bool (Int,Int) | UpTo Bool (Int,Int)` (`AstComp.hs:320-322`), e.g. `repeat <= [8,8]` in `scramble.blk:32`.
   - When upstream and downstream vector widths mismatch (e.g., 48 coded bits/symbol feeding an 8-bit byte-oriented Viterbi input), the vectorizer inserts lightweight rate-matching **mitigators**, which `PassOptMit` (`pass-push-mit`, `elim-automapped-mitigs`, `elim-mitigs` in `PassFold.hs:132-134`) pushes across pipeline boundaries and eliminates whenever GCD/LCM alignment allows.
3. **Automated Bit-to-LUT Synthesis (`AutoLUT.hs:50-88`, `LUTAnalysis.hs:108-200`, `Opts.hs:106-113`)**:
   - After the second round of folding (so vectorized bit loops like 8 iterations of a 1-bit LFSR have been unrolled into pure straight-line bit expressions), `AutoLUT` evaluates every expression `e` with `calcLUTStats`:
     $$\text{lutBytes}(w_{\text{in}}, w_{\text{out}}) = 2^{w_{\text{in}}} \cdot \left\lceil \frac{w_{\text{out}}}{8} \right\rceil$$
   - `shouldLUT` (`LUTAnalysis.hs:185-200`) replaces `e` with a compile-time precomputed C lookup table (`ELUT`) **if and only if all six predicates hold**:
     1. No function calls inside `e` (`not lmHasCall`);
     2. Not already containing a LUT (`not lmHasLUT`);
     3. Output bitwidth strictly exceeds 2 bits (`lut_outbitwidth > 2`);
     4. Operation count strictly exceeds `mIN_OP_COUNT = 5` (`lmOpCount > 5`);
     5. Table size fits within `maxLUTSize dflags` (default **`mAX_LUT_SIZE_DEFAULT = 256 * 1024` bytes = `256 KiB`**, `Opts.hs:107`);
     6. Non-nested output array type (`luttable_out_type`).
   - **Quantitative Scrambler LUT Cliff (`Basis: execution`, probe Part 3)**: For the IEEE 802.11a 7-bit LFSR scrambler (`scramble.blk:28-44`), input width is $w_{\text{in}} = w + 7$ bits (data bits + 7-bit shift-register state) and output width is $w_{\text{out}} = w + 7$ bits:

| Vectorization Width $w$ (bits) | LUT Input / Output Width | Bytes / Entry | Total Table Size | Fits Default `256 KiB` Cap? |
| :---: | :---: | :---: | :---: | :---: |
| `1` | `8 b / 8 b` | `1 B` | `256 B` (`0.2 KiB`) | Yes (but `< 6` ops unrolled) |
| `4` | `11 b / 11 b` | `2 B` | `4,096 B` (`4.0 KiB`) | Yes |
| **`8` (`scramble.blk:32`)** | **`15 b / 15 b`** | **`2 B`** | **`65,536 B` (`64.0 KiB`)** | **Yes (sweet spot: L1/L2 cache)** |
| `10` | `17 b / 17 b` | `3 B` | `393,216 B` (`384.0 KiB`) | **No (rejected by `shouldLUT`)** |
| `12` | `19 b / 19 b` | `3 B` | `1,572,864 B` (`1.5 MiB`) | **No** |
| `16` | `23 b / 23 b` | `3 B` | `25,165,824 B` (`24.0 MiB`) | **No** |

4. **Explicit Multi-Core Pipeline Splitting (`PassPipeline.hs:64-159`, `AstComp.hs:374-392`)**:
   - Where the programmer writes `|>>>|` (`AlwaysPipeline tid1 tid2`), `float_pipe` applies associativity rewrites `c1 >>> (c21 |>>>| c22) ~~> (c1 >>> c21) |>>>| c22` and `(c11 |>>>| c12) >>> c2 ~~> c11 |>>>| (c12 >>> c2)` to float thread boundaries to top level, then `insertBufs` wraps each split with `writeInternal buf_m` and `readInternal buf_m SpinOnEmpty` backed by bounded single-producer/single-consumer ring buffers (`csrc/buf.h`) pinned to dedicated cores (`AffinityMask`).

---

### 2. Hard Real-Time Verification: The IEEE 802.11a `16 μs` SIFS Turnaround Budget

`Basis: normative + execution + source`

In IEEE Std 802.11a (Clause 17, 20 MHz OFDM channel in 5 GHz band), every unicast data frame requires an immediate hardware-timed `ACK` frame transmitted exactly **`aSIFSTime = 16 μs`** after the end of the last OFDM symbol at the air interface (in 2.4 GHz 802.11g ERP-OFDM, `SIFS = 10 μs` plus a mandatory `6 μs` signal extension yields the same `16 μs` decoding window).

#### 2.1 End-to-End SIFS Delay Decomposition

Normatively:
$$\text{aSIFSTime} = \text{aRxRFDelay} + \text{aRxPLCPDelay} + \text{aMACProcessingDelay} + \text{aRxTxTurnaroundTime} = 16.0\ \mu\text{s}$$

| Component | Normative / Typical Budget | Engineering Constraint |
| :--- | :---: | :--- |
| **`aRxRFDelay` + ADC/DMA transfer** | `~0.5–1.5 μs` | PCIe/Sora RCB DMA ring transfer of final 80-sample (`4.0 μs`) OFDM symbol |
| **`aMACProcessingDelay`** | `<= 2.0 μs` (normative max) | FCS/CRC-32 check, address match, pre-modulated ACK template selection |
| **`aRxTxTurnaroundTime`** | `<= 2.0 μs` (normative max) | RF front-end switch from RX LNA to TX PA |
| **`aTxPLCPDelay`** | `~1.0 μs` | Pre-computed ACK waveform DMA launch (Sora/Ziria pre-modulates ACK symbols) |
| **Remaining Rx PHY Baseband Compute Slack** | **`~9.5–10.5 μs`** | Must drain the final OFDM symbol through **64-pt FFT $\to$ Equalization $\to$ QAM Demap $\to$ Deinterleave $\to$ Viterbi traceback $\to$ Descrambler $\to$ CRC-32**! |

#### 2.2 Throughput vs. Tail-Latency Invariants Across 802.11a MCS Modes

`Basis: execution` (probe Part 4):

Each `20 MS/s` OFDM symbol lasts exactly **`4.0 μs`** (`3.2 μs` useful 64-point FFT window + `0.8 μs` 16-sample cyclic prefix = `80` complex16 samples), carrying 48 data subcarriers, 4 pilots, 1 DC null, and 11 guard-band nulls:

| MCS Mode | Coded Bits / Sym (`N_CBPS`) | Code Rate | Data Bits / Sym (`N_DBPS`) | Bytes / `4 μs` Sym | Byte-Aligned (`N_DBPS % 8 == 0`) | Required Sustained Bitrate |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `6 Mbps (BPSK 1/2)` | `48` | `1/2` | `24` | `3 B` | Yes | `6.0 Mb/s` |
| `12 Mbps (QPSK 1/2)` | `96` | `1/2` | `48` | `6 B` | Yes | `12.0 Mb/s` |
| `18 Mbps (QPSK 3/4)` | `96` | `3/4` | `72` | `9 B` | Yes | `18.0 Mb/s` |
| `36 Mbps (16-QAM 3/4)` | `192` | `3/4` | `144` | `18 B` | Yes | `36.0 Mb/s` |
| `48 Mbps (64-QAM 2/3)` | `288` | `2/3` | `192` | `24 B` | Yes | `48.0 Mb/s` |
| `54 Mbps (64-QAM 3/4)` | `288` | `3/4` | `216` | `27 B` | Yes | `54.0 Mb/s` |

Two hard real-time constraints follow directly:
1. **Steady-state throughput bound**: Every per-symbol PHY stage (or parallel core partition via `|>>>|`) must sustain $\le 4.0\ \mu\text{s}$ per OFDM symbol (`~12,000` cycles on a 3 GHz core) for all 64-QAM 3/4 `288`-bit symbols, leaving zero backlog when the last symbol arrives.
2. **End-of-packet flush latency bound**: Even if steady-state throughput meets `4.0 μs/sym`, deep inter-thread buffering (such as GNU Radio's 4–64 KiB asynchronous work-chunk ring buffers) adds **hundreds of microseconds** of pipeline fill/drain latency and catastrophically misses the `16 μs` SIFS deadline. Ziria's zero-allocation fused state machines (`>>>`), fine-grained core-pinned spin buffers (`SpinOnEmpty`), LUT-accelerated bit-ops (`AutoLUT`), and SIMD-vectorized FFT/Viterbi/LDPC kernels (`sora_fft`, `AFF3CT`) are *jointly necessary* to bound worst-case end-of-frame drain latency below `10 μs`.

---

### 3. SPIRAL: Algebraic Kronecker-Product DSP Synthesis Across SIMD and FPGA

`Basis: source + normative + execution`

Where Ziria excels at bit-level framing, control staging, and stream fusion—while calling out to external `sora_fft` (`FFT.blk:27`)—**SPIRAL** (Püschel et al., Proc. IEEE 2005; Franchetti et al., Proc. IEEE 2018; `spiral-software/spiral-software`) systematically synthesizes optimal linear-transform kernels (FFT, DCT, WHT, FIR, convolution, SAR, synthetic aperture) from mathematical specifications across x86 SSE/AVX, ARM NEON, GPUs (`spiral-package-simt`), and streaming FPGAs (`paradigms/stream`).

#### 3.1 Multi-Stage Algebraic Tower: `SPL` $\to$ `OL` $\to$ `Σ-SPL` $\to$ `ICode`

Inspecting `namespaces/spiral/{spl,sigma,transforms/dft,paradigms}` directly exposes SPIRAL's four-layer intermediate language stack:

1. **SPL / Breakdown Rules (`namespaces/spiral/transforms/dft/dft_rules.gi:62-84`)**:
   - A transform is represented as a parameterized non-terminal `DFT(n, k)` whose matrix entry is $\omega_n^{krc} = e^{2\pi i k r c / n}$ (`dft.gi:55`, with `k = -1` for standard forward FFT).
   - SPIRAL's default DFT rule set (`transforms/dft/init.g:24`) activates `[DFT_Base, DFT_Base1, DFT_CT, DFT_Rader, DFT_PD]`. The general Cooley–Tukey rule `DFT_CT` (`dft_rules.gi:62-84`) decomposes any composite $N = m \cdot n$ via exact Kronecker-product algebra:
     $$\mathrm{DFT}_{mn}^{(k)} = \bigl(\mathrm{DFT}_m^{(k \bmod m)} \otimes I_n\bigr)\; T^{mn}_{n,k}\; \bigl(I_m \otimes \mathrm{DFT}_n^{(k \bmod n)}\bigr)\; L^{mn}_m$$
     Verbatim GAP rule in `dft_rules.gi:78-83`:
     ```gap
     apply := (nt, C, cnt) -> let(mn := nt.params[1], m := Rows(C[1]), n := Rows(C[2]),
         Tensor(C[1], I(n)) *
         Diag(fPrecompute(Tw1(mn, n, nt.params[2]))) *
         Tensor(I(m), C[2]) *
         L(mn, m)
     )
     ```
     where `L(mn, m)` is the stride permutation mapping $i \cdot m + j \mapsto j \cdot n + i$, and `Tw1(mn, n, k)` (`dft.gi:125-127`) is the diagonal twiddle matrix $\bigoplus_{i=0}^{m-1} \operatorname{diag}(\omega_{mn}^{k \cdot i \cdot 0}, \dots, \omega_{mn}^{k \cdot i \cdot (n-1)})$.
   - **Verified exactness (`Basis: execution`, probe Part 1)**: Evaluating the literal `dft_rules.gi` formula in double-precision complex arithmetic against dense `DFT_mn` yields $\max_{r,c}|A_{rc} - B_{rc}| \le 4.4 \times 10^{-15}$ across `DFT_12` ($3 \times 4$) and all IEEE 802.11a `DFT_64` factorizations ($8 \times 8$, $4 \times 16$, $16 \times 4$, $2 \times 32$).
   - Alternative factorizations expose distinct memory/parallelism geometries: **Stockham autosort** (`TC4`, `TC5`, `TC6`, `Stockham_radix` in `dft.gi:173-230`, eliminating bit-reversal passes for vector/GPU units), **Pease constant-geometry** (`TC`, `TC2`, `TCBase` in `dft.gi:243-284`, ideal for fixed-interconnect streaming FPGAs), **Good–Thomas** prime-factor decomposition (zero twiddle multiplies when $\gcd(m,n)=1$), and **Rader** (prime sizes).
2. **Operator Language (`OL`) (`namespaces/spiral/sigma/ol.gi:8-101`)**: Generalizes linear matrix transforms to multi-input/multi-output and non-linear dataflow operators using `Cross` (parallel operator juxtaposition), `fCross`, `ExplicitGath`, and explicit layout transpose rules (`ExplicitOLRuleset`).
3. **$\Sigma$-SPL (Index-Explicit Loop/Gather/Scatter IR) (`namespaces/spiral/sigma/init.g`, `spl2sums.gi`, `sums_rules.gi`)**:
   - Lowers Kronecker products $I_m \otimes A_n$ into explicit iterative sums $\sum_{j=0}^{m-1} S_{h_j}\, A_n\, G_{g_j}$ (`ISum`, `Scat`, `Gath`, `Diag`).
   - **Loop fusion and permutation elimination happen algebraically at $\Sigma$-SPL**: composing a permutation matrix $P$ with a gather $G_g$ collapses to $G_{P \circ g}$, fusing bit-reversal and stride permutations directly into load/store index functions (`fCompose`, `fTensor`) with zero temporary scratchpad arrays!
4. **Target-Paradigm Rewriting: SIMD Vectors vs. Streaming FPGA Hardware**:
   - **SIMD (`namespaces/spiral/paradigms/vector/init.g:1-38`)**: Tags sub-formulas with vector length $\nu$ (`VTensor`, `_VHStack`, `_VSUM`) and rewrites $A \otimes I_\nu$ directly into native $\nu$-way vector instructions (SSE, AVX2/AVX-512, ARM NEON), while transforming stride permutations $L^{\nu^2}_\nu$ into in-register transpose/shuffle networks (`vunpacklo`/`vunpackhi`, `trn1`/`trn2`).
   - **Streaming FPGA / RTL (`namespaces/spiral/paradigms/stream/init.g:1-35`; Milder et al., ACM TODAES 2012)**: Sets `StreamDefaults.codegen := HDLCodegen` and `StreamDefaults.compileStrategy := conservativeCompileSSA`, factoring permutations (`bitperms`, `streambitperms`, `permnetwork`) into hardware shift-register / BRAM streaming permutation networks (`streaming width` $w$ samples/cycle) matching Pease/Stockham dataflow so the synthesized Verilog executes a `64-point` FFT at 1 symbol every $64/w$ clock cycles with deterministic single-cycle-accurate latency!

#### 3.2 Fixed-Point `TFixedPt` Synthesis: Bit-Growth vs. SQNR Collapse

`Basis: source + execution`

SPIRAL defines explicit signed/unsigned fixed-point types `TFixedPt(bits, fracbits)` and `TUFixedPt` (`namespaces/spiral/code/types.gi:235-261`, allocating `1` sign bit, `bits - 1 - fracbits` integer bits, and `fracbits` fractional bits) and scaled twiddle diagonals `ScaledTwid` (`dft.gi:159-168`). Because an unscaled $N$-point DFT has worst-case coherent gain $N$ ($\log_2 N$ bits of dynamic-range growth; $+6$ bits for IEEE 802.11a's $N=64$ FFT), every fixed-point DSP compiler faces a fundamental **scaling-schedule cliff**.

Our executable `Q1.15` 64-point radix-2 Cooley–Tukey probe (reproducible script in **Evidence**) quantifies this trade-off directly on two canonical wireless waveforms:

| Input Waveform (64-pt FFT, Q1.15) | Scaling Strategy | Total Right-Shifts | Saturation Clipping Events | Output SQNR (dB) | Engineering Interpretation |
| :--- | :--- | :---: | :---: | :---: | :--- |
| **Single-Tone Pilot** (amp `0.5`, max coherent gain) | `unscaled_sat` | `0` | **`50`** | **`0.25 dB`** | Catastrophic clipping; completely unusable |
| **Single-Tone Pilot** (amp `0.5`) | `static_half` (`>>1`/stage) | `6` | `0` | **`80.77 dB`** | Overflow-free; full 16-bit headroom preserved |
| **Single-Tone Pilot** (amp `0.5`) | `bfp` (adaptive per-stage) | `6` | `0` | **`80.77 dB`** | Matches `static_half` when coherent gain occurs |
| **48-Subcarrier OFDM** (peak `0.25`, 12 dB crest backoff) | `unscaled_sat` | `0` | `0` | **`73.28 dB`** | No saturation due to crest-factor backoff |
| **48-Subcarrier OFDM** (peak `0.25`) | `static_half` (`>>1`/stage) | `6` | `0` | **`44.56 dB`** | **`-28.72 dB` quantization loss!** Erodes 256-QAM margin |
| **48-Subcarrier OFDM** (peak `0.25`) | `bfp` (adaptive per-stage) | `0` | `0` | **`73.28 dB`** | Recovers full `+28.72 dB` SQNR with 0 overflows |

Note that IEEE 802.11a `64-QAM 3/4` requires transmitter/receiver EVM better than `-25 dB` and IEEE 802.11ac/ax `256-QAM 5/6` / `1024-QAM` require `-32 dB` to `-35 dB` total system EVM—meaning a `-28.7 dB` unnecessary FFT noise penalty from naive static scaling consumes nearly the entire analog+digital error budget unless either wider internal accumulators (`Q1.23`/`int32`), mixed-radix asymmetric scaling schedules (`ScaledTwid`), or block-floating-point (`bfp`) tracking is synthesized.

---

### 4. HELIX: Coq-Verified Lowering of SPIRAL Operator Languages to Vellvm LLVM IR

`Basis: source + documentation`

Because SPIRAL's GAP rewriting engine (`>100k` LoC of untyped GAP scripts) performs complex index-function algebra and platform-specific code generation, a single subtle off-by-one bug in a gather/scatter or twiddle index silently corrupts numerical outputs. **HELIX** (Zaliva et al., FHPC 2018, VSTTE 2020 `10.1007/978-3-030-63618-0_3`, `arXiv:2604.18593` 2026; `vzaliva/helix` + `spiral-package-hcol`) closes this trust gap by turning SPIRAL into an **untrusted optimization oracle** whose output is certified in Coq down to **Vellvm** LLVM IR:

#### 4.1 Layered Verified Compilation Architecture

| HELIX Layer (`vzaliva/helix`) | Representation & Semantics | Verification Technique |
| :--- | :--- | :--- |
| **1. `HCOL`** (`coq/HCOL/HCOL.v`) | Purely functional mathematical vector/matrix/non-linear operator algebra over exact real numbers (`CarrierA = R`, `RasCarrierA.CarrierDefs_R`) | Coq mechanized proofs of algebraic operator identities (including non-linear operators like `Max`, `Min`, `Abs`, `Zless` beyond linear SPL) |
| **2. `Σ-HCOL`** (`coq/SigmaHCOL/SigmaHCOL.v`) | Sparse-vector partial-computation algebra (`Gather`, `Scatter`, `ISumUnion`, `Pointwise`, `BinOp`) | Verified semantics-preserving term rewriting (proving parallel/loop decompositions via sparse vector disjointness) |
| **3. `DΣ-HCOL` (`RHCOL` $\to$ `FHCOL`)** (`coq/DSigmaHCOL/DSigmaHCOL.v`) | Imperative memory-explicit AST (`DSHOperator`: `DSHNop`, `DSHAssign`, `DSHIMap`, `DSHBinOp`, `DSHMemMap2`, `DSHPower`, `DSHLoop`, `DSHAlloc`, `DSHSeq`; `AExpr` with `AAbs`, `AMin`, `AMax`, `AZless`) | Verified translation from functional `Σ-HCOL` to imperative real-valued `RHCOL` (VSTTE 2020), then translation validation + **Flocq / Gappa** verified floating-point error analysis bridging `RHCOL` (`R`) to IEEE-754 `binary64` `FHCOL` |
| **4. `LLVM IR` (`Vellvm`)** (`coq/LLVMGen/Compiler.v`, `TopLevel.v`) | Executable monadic **Interaction Trees (ITrees)** semantics for LLVM IR (`interp_mcfg3`, `denote_ocfg`) | Coq bisimulation (`eutt`) proving `compile_w_main` preserves `FHCOL` semantics into LLVM IR memory/return state |

#### 4.2 Exact Top-Level Soundness Statement and Its Explicit Axiomatic Seam

Direct inspection of `vzaliva/helix` (`coq/LLVMGen/TopLevel.v:1244-1268`) reveals the exact top-level Coq theorem `Lemma top_to_LLVM`:

```coq
Lemma top_to_LLVM :
  forall (a : Vector.t CarrierA 3)       (* parameter *)
    (x : Vector.t CarrierA dynwin_i)     (* input *)
    (y : Vector.t CarrierA dynwin_o),    (* output *)
      dynwin_orig a x = y ->
      forall (data : list binary64)
        (PRE : heq_list (Vector.to_list a ++ Vector.to_list x) data),
        input_inConstr a x ->
        forall s pll
          (COMP : compile_w_main (dynwin_fhcolp DynWin_FHCOL_hard) data newState ≡ inr (s, pll)),
        exists g l m r, semantics_llvm pll ≈ Ret (m, (l, (g, r))) /\
                        final_rel_val y r.
```

Look closely at the **two critical caveats explicitly documented in the Coq source itself** (`TopLevel.v:1249-1255`):
1. `(* The program is fixed and hard-coded: the result is not generic, we provide a "framework". *)`: The end-to-end `top_to_LLVM` proof is instantiated for the cyber-physical Dynamic Window robot control monitor (`DynWin_FHCOL_hard`), while the `FHCOL -> LLVM IR` compiler (`genIR`, `LLVMGen/Compiler.v`) is proved generic over `DSHOperator` ASTs.
2. `(* We cannot hide away the [R] level as we axiomatize the real to float approximation performed *)`: While `RHCOL` and `FHCOL` semantics are formally related via `heq_memory` / `final_rel_val` under `input_inConstr a x`, the specific real-to-float approximation bridge at the top level relies on Gappa-assisted / axiomatized floating-point error assumptions, and downstream LLVM-to-machine-code lowering (`llc`/Clang) remains outside the Coq TCB.

---

### 5. Cross-System Architecture Matrix: Composing SDR PHY Compilers, Algebraic DSP, and FEC

`Basis: source + documentation + derived`

| Dimension | **Ziria / Blink** (`dimitriv/Ziria`) | **SPIRAL** (`spiral-software`) | **HELIX** (`vzaliva/helix`) | **AFF3CT** (`aff3ct/aff3ct`) |
| :--- | :--- | :--- | :--- | :--- |
| **Primary Niche** | Complete wireless PHY framing, mid-packet mode switching, bit-level LUTs | Linear & OL DSP transforms (FFT, DCT, WHT, FIR, convolution) | Coq-verified compilation of HCOL/Σ-HCOL numerical kernels to LLVM IR | High-throughput SIMD channel coding (LDPC, Polar, Turbo, Viterbi) |
| **IR / Formalism** | Two-level `ST (C v) a b` + `ST T a b` (`>>>`, `|>>>|`) | `SPL` $\to$ `OL` $\to$ `Σ-SPL` $\to$ `ICode` (GAP) | `HCOL` $\to$ `Σ-HCOL` $\to$ `RHCOL/FHCOL` $\to$ `Vellvm` ITrees | C++ templated MIPP SIMD inter-frame bit-sliced decoders |
| **Dynamic Mode Switching** | Native (`seq { h <- DecodePLCP(); Decode(h) }`) | Static fixed-size kernels (parameterized via runtime dispatch) | Static fixed-size operator DAGs (`DSHOperator`) | Runtime decoder selection per MCS/frame size |
| **Bit-Level Acceleration** | Automated `AutoLUT` (`256 KiB` cap, `>5` ops) + cardinality vectorization | Bit-reversal & stride permutations (`ext_bitperms`, `streambitperms`) | Not targeted (operates on `R`/`binary64` vectors) | Inter-frame SIMD bit-slicing (`Decoder_LDPC_BP_horizontal_layered_inter.hpp`) |
| **Hardware Targets** | x86/ARM C + Sora/BladeRF/FMCOMMS | x86 SSE/AVX, ARM NEON, CUDA/SIMT, Verilog FPGA (`HDLCodegen`) | LLVM IR (Vellvm; downstream `llc` unverified) | x86 SSE/AVX2/AVX-512, ARM NEON |
| **Hard Real-Time / WCET** | Zero-alloc fused C state machines; meets `16 μs` 802.11a SIFS on Sora | Deterministic straight-line/unrolled loops & single-cycle FPGA pipelines | Deterministic terminating loops (`semantics_llvm ≈ Ret ...`) | Predictable bounded iteration counts (`I_max` BP/SC-List) |
| **Formal Verification** | Static type & cardinality safety (no mechanized C codegen proof) | Algebraic identities (unverified GAP rewrite engine) | **Mechanized Coq proofs** down to Vellvm LLVM IR (`top_to_LLVM`) | Unit/BER simulation testing only |

## Boundaries

- **Ziria end-to-end execution on physical RF hardware (`Sora` / `BladeRF`) — `not examined`**: This report inspects `dimitriv/Ziria`'s Haskell compiler passes and `code/WiFi/*.blk` source directly and evaluates the IEEE 802.11a `16 μs` SIFS timing budget arithmetically; physical over-the-air ACK turnaround latency was not measured on Sora/BladeRF hardware (empirical `16 μs` SIFS conformance on Intel Core i7 + Sora is reported in Stewart et al., ASPLOS 2015).
- **Mechanized WCET verification of SIFS deadlines — `unsupported` in Ziria and HELIX**: Neither Ziria (`wplc`) nor HELIX (`vzaliva/helix`) generates a formal worst-case execution time (WCET) certificate bounding microarchitectural cycle counts on out-of-order CPUs (`x86-64`/`ARM64`). Ziria ensures *structural* real-time suitability (zero dynamic allocation, fused control flow, deterministic LUT lookups) while SPIRAL's FPGA backend (`HDLCodegen`) provides cycle-accurate latency only on synchronous RTL targets.
- **HELIX coverage of complex-valued FFTs and fixed-point `TFixedPt` — `not examined` / `unsupported` in pinned `TopLevel.v`**: While `spiral-package-hcol` bridges SPIRAL and HELIX, `vzaliva/helix` @ `f2373ef4c7b25745d2f85cd89dd58d68d4ce0765` proves end-to-end `top_to_LLVM` for a real-valued `binary64` cyber-physical control monitor (`DynWin_FHCOL_hard`, `TopLevel.v:1244-1268`), not a fixed-point `Q1.15` complex OFDM FFT or Viterbi/LDPC decoder, and leaves LLVM-to-assembly lowering (`llc`) outside its Coq proof.
- **5G NR (`3GPP TS 38.211/212`) LDPC / Polar rate-matching and dynamic SCS (`15–240 kHz`) — `not examined`**: Although `AFF3CT` implements 5G NR LDPC/Polar kernels and `dimitriv/Ziria` links to an external LTE/LTE-U platform (`Microsoft/OTP4LTE-U`), 5G NR's slot-level `HARQ` timing and quasi-cyclic LDPC lifting graphs were not audited at source level here.
- **Over-strong claims rejected**:
  - Ziria's `AutoLUT` does **not** automatically make arbitrary bit-level kernels fast: if vectorization width is uncapped, table size grows exponentially ($2^{w_{\text{in}}} \cdot \lceil w_{\text{out}}/8 \rceil$) and silently trips the `256 KiB` `maxLUTSize` threshold, falling back to scalar bit-twiddling—which is why `scramble.blk:32` explicitly bounds vectorization with `repeat <= [8,8]`.
  - Proving algebraic Kronecker-product equivalence in $\mathbb{C}^N$ (`SPIRAL` `DFT_CT`) does **not** guarantee numerical soundness under fixed-point `TFixedPt` lowering: as our probe proves, an algebraically exact 64-point FFT loses `>80 dB` SQNR to clipping when unscaled and `-28.72 dB` SQNR to truncation under naive per-stage `>> 1` scaling on realistic OFDM waveforms.

## Evidence

### Primary Git Repository Sources (Observed `2026-11-19`)

1. **`dimitriv/Ziria` @ `ccbb0960737fb86bf51a1d33af8e614ee9700ffe`**:
   - `wplc.cabal:1-92` — Package metadata (`wplc`, `BlinkDiff` executable, source directories).
   - `src/Main.hs:111-251` — Full compilation pipeline (`tyCheckProg` $\to$ `runFoldPhase` $\to$ `runVectorizePhase` $\to$ `runFoldPhase` (2nd) $\to$ `runAutoLUTPhase` $\to$ `runPipelinePhase` $\to$ `codeGenProgram`).
   - `src/BasicTypes/AstComp.hs:58-177, 320-395` — Two-level `GCTy` (`CTComp`, `CTTrans`, `CTArrow`), `Par` typing rules (`T >>> T`, `C >>> T`, `T >>> C`), `VectAnn` (`Rigid`, `UpTo`), `PlInfo` (`AlwaysPipeline`, `NeverPipeline`, `MaybePipeline`), `ReadType` (`SpinOnEmpty`).
   - `src/Optimize/PassFold.hs:85-166` — Iterative fixpoint fusion (depth 10), `PassOptMit` mitigator elimination (`pass-push-mit`, `elim-automapped-mitigs`, `elim-mitigs`).
   - `src/Vectorize/CardAnalysis.hs:73-84` & `src/Vectorize/Vectorize.hs:73-80, 461-468, 603-615` — Static cardinality `SCard CAlpha CAlpha | OCard` and scale-factor selection (`compSFDU`, `compSFUD`, `compSFDD`).
   - `src/Optimize/AutoLUT.hs:50-88`, `src/Codegen/LUTAnalysis.hs:108-209`, `src/Opts.hs:106-113` — `lutBytes`, `mIN_OP_COUNT = 5`, `mAX_LUT_SIZE_DEFAULT = 256*1024`, 6-condition `shouldLUT`.
   - `src/Pipeline/PassPipeline.hs:64-159` — `float_pipe` associativity rewrites and `insertBufs` thread splitting.
   - `code/WiFi/receiver/{receiver.blk:43-73, decoding/DecodePLCP.blk:30-37, decoding/Decode.blk:45-60, OFDM/FFT.blk:24-29}` and `code/WiFi/transmitter/scramble.blk:26-44`.
2. **`spiral-software/spiral-software` @ `577b2c1268476c885fbb9984b9e06174f71b5386`**:
   - `namespaces/spiral/spl/init.g:1-92`, `namespaces/spiral/sigma/{init.g:1-42, ol.gi:1-101}`.
   - `namespaces/spiral/transforms/dft/{init.g:1-25, dft.gi:16-61, 125-320, dft_rules.gi:62-84}` — `DFT_NonTerm`, `Tw1`, `ScaledTwid`, `Stockham_radix`, `TC`/`TC2` (Pease), and verbatim `DFT_CT` Cooley–Tukey breakdown rule.
   - `namespaces/spiral/code/types.gi:235-261` — `TFixedPt(bits, fracbits)` and `TUFixedPt`.
   - `namespaces/spiral/paradigms/vector/init.g:1-38` (`VTensor`, `_VHStack`, `_VSUM`) and `namespaces/spiral/paradigms/stream/init.g:1-35` (`StreamDefaults.codegen := HDLCodegen`, `conservativeCompileSSA`, `streambitperms`, `permnetwork`).
3. **`spiral-software/spiral-package-hcol` @ `b4a0118382e3bba91ecd82a6c667f2cdb6389ceb`**:
   - `init.g:32-53`, `formal_compile.gi:5-56` (`CoSynthesize`, `ExportCode`, `ExportCProg`).
4. **`vzaliva/helix` @ `f2373ef4c7b25745d2f85cd89dd58d68d4ce0765`**:
   - `README.org:1-126`, `_CoqProject:1-6`, `Makefile:28, 46` (Coq `8.13.2`, Vellvm submodule, Flocq, Gappa).
   - `coq/DSigmaHCOL/DSigmaHCOL.v:271-360` (`AExpr`, `DSHOperator`), `coq/LLVMGen/TopLevel.v:22-35, 165-190, 1244-1268, 2130-2260` (`top_to_FHCOL`, `top_to_LLVM`).
5. **`aff3ct/aff3ct` @ `0e8ecda8191cec97a6fe86a56de0d957b63b3b04`**:
   - `README.md`, `include/Module/Decoder/LDPC/BP/Horizontal_layered/Decoder_LDPC_BP_horizontal_layered_inter.hpp`.

### Peer-Reviewed Literature & Standards

- G. Stewart, M. Gowda, G. Mainland, B. Radunović, D. Vytiniotis, C. Luengo Agulló, *"Ziria: A DSL for Wireless Systems Programming"*, **ASPLOS 2015**, pp. 415–428, DOI `10.1145/2694344.2694368`.
- K. Tan, J. Zhang, J. Fang, H. Liu, Y. Ye, S. Wang, Y. Zhang, H. Wu, W. Wang, G. M. Voelker, *"Sora: High-Performance Software Radio Using General-Purpose Multi-Core Processors"*, **USENIX NSDI 2009** (and CACM 2011).
- M. Püschel et al., *"SPIRAL: Code Generation for DSP Transforms"*, **Proceedings of the IEEE** 93(2), 2005, DOI `10.1109/JPROC.2004.840306`.
- P. A. Milder, F. Franchetti, J. C. Hoe, M. Püschel, *"Computer Generation of Hardware for Linear Digital Signal Processing Transforms"*, **ACM TODAES** 17(2), 2012, DOI `10.1145/2159542.2159547`.
- F. Franchetti et al., *"SPIRAL: Extreme Performance Portability"*, **Proceedings of the IEEE** 106(11), pp. 1935–1968, 2018, DOI `10.1109/JPROC.2018.2873289`.
- V. Zaliva, I. Zaichuk, F. Franchetti, *"Verified Translation Between Purely Functional and Imperative Domain Specific Languages in HELIX"*, **VSTTE 2020**, LNCS 12546, DOI `10.1007/978-3-030-63618-0_3`.
- V. Zaliva, Y. Zakowski, I. Zaichuk, V. Huhnin, C. Beck, I. Yoon, S. Zdancewic, *"HELIX: Verified compilation of cyber-physical control systems to LLVM IR"*, **arXiv:2604.18593v1** [cs.PL], submitted 27 Mar 2026 (`https://doi.org/10.48550/arXiv.2604.18593`).
- A. Cassagne et al., *"AFF3CT: A Fast Forward Error Correction Toolbox!"*, **SoftwareX** 10, 2019, DOI `10.1016/j.softx.2019.100345`.
- IEEE Std 802.11a-1999 / IEEE Std 802.11 Clause 17 (OFDM PHY: `aSIFSTime = 16 μs`, `4 μs` OFDM symbol, 64-point FFT, 48 data + 4 pilot subcarriers).

### Executable Algebraic, Numerical, and Timing Probe (Observed `2026-11-19`, Python 3.13, Stdlib Only)

```python
#!/usr/bin/env python3
import cmath, math

def dft_mat(N, k=-1):
    w = cmath.exp(2j * math.pi * k / N)
    return [[w ** ((r * c) % N) for c in range(N)] for r in range(N)]

def eye(N):
    return [[1.0 + 0j if r == c else 0j for c in range(N)] for r in range(N)]

def kron(A, B):
    ra, ca, rb, cb = len(A), len(A[0]), len(B), len(B[0])
    out = [[0j] * (ca * cb) for _ in range(ra * rb)]
    for i in range(ra):
        for j in range(ca):
            a = A[i][j]
            if a:
                for p in range(rb):
                    for q in range(cb):
                        out[i * rb + p][j * cb + q] = a * B[p][q]
    return out

def matmul(A, B):
    r, k, c = len(A), len(B), len(B[0])
    out = [[0j] * c for _ in range(r)]
    for i in range(r):
        for t in range(k):
            a = A[i][t]
            if a:
                for j in range(c):
                    out[i][j] += a * B[t][j]
    return out

def stride_perm(mn, m):
    n = mn // m
    L = [[0j] * mn for _ in range(mn)]
    for i in range(n):
        for j in range(m):
            L[j * n + i][i * m + j] = 1.0 + 0j
    return L

def twiddle_diag(mn, n, k=-1):
    m = mn // n
    w = cmath.exp(2j * math.pi * k / mn)
    T = [[0j] * mn for _ in range(mn)]
    for i in range(m):
        for j in range(n):
            T[i * n + j][i * n + j] = w ** ((i * j) % mn)
    return T

for m, n in [(3, 4), (8, 8), (4, 16), (16, 4), (2, 32)]:
    mn = m * n
    lhs = dft_mat(mn, -1)
    rhs = matmul(matmul(kron(dft_mat(m, -1), eye(n)), twiddle_diag(mn, n, -1)),
                 matmul(kron(eye(m), dft_mat(n, -1)), stride_perm(mn, m)))
    err = max(abs(lhs[r][c] - rhs[r][c]) for r in range(mn) for c in range(mn))
    print(f"DFT_{mn:2d} ({m}x{n}) max|err| = {err:.3e}")

for w in (1, 4, 8, 10, 12, 16):
    inb = w + 7
    tb = (1 << inb) * ((inb + 7) // 8)
    print(f"scrambler w={w:2d}: {tb:10,d} B (fits_256KiB={tb <= 256*1024})")

# Fixed-point Q1.15 64-point radix-2 DIT FFT scaling vs SQNR probe
def sat16(v): return 32767 if v > 32767 else (-32768 if v < -32768 else v)
def bit_rev(x, b):
    r = 0
    for _ in range(b): r = (r << 1) | (x & 1); x >>= 1
    return r

def fft64_q15(sig, mode):
    re = [sat16(int(round(sig[bit_rev(i, 6)].real * 32767))) for i in range(64)]
    im = [sat16(int(round(sig[bit_rev(i, 6)].imag * 32767))) for i in range(64)]
    shifts = ovf = 0
    for s in range(6):
        m = 1 << (s + 1); half = m >> 1
        do_sh = (mode == "static_half") or (mode == "bfp" and max(max(abs(x) for x in re), max(abs(x) for x in im)) > 11500)
        shifts += int(do_sh)
        for k in range(0, 64, m):
            for j in range(half):
                ang = -2.0 * math.pi * j / m
                wr, wi = sat16(int(round(math.cos(ang) * 32767))), sat16(int(round(math.sin(ang) * 32767)))
                i0, i1 = k + j, k + j + half
                tr = (re[i1] * wr - im[i1] * wi + (1 << 14)) >> 15
                ti = (re[i1] * wi + im[i1] * wr + (1 << 14)) >> 15
                ur, ui = re[i0], im[i0]
                vals = ((ur+tr)>>1, (ui+ti)>>1, (ur-tr)>>1, (ui-ti)>>1) if do_sh else (ur+tr, ui+ti, ur-tr, ui-ti)
                ovf += sum(1 for v in vals if v > 32767 or v < -32768)
                re[i0], im[i0], re[i1], im[i1] = (sat16(v) for v in vals)
    sc = (1 << shifts) / 32767.0
    return [complex(re[i] * sc, im[i] * sc) for i in range(64)], shifts, ovf

M64, Minv = dft_mat(64, -1), dft_mat(64, +1)
tone = [0.5 * cmath.exp(2j * math.pi * 7 * n / 64) for n in range(64)]
bins = [1.0 if ((i*17+3)%2==0) else -1.0 if i in list(range(1,27))+list(range(38,64)) else 0j for i in range(64)]
bins = [bins[i] if i in list(range(1,27))+list(range(38,64)) else 0j for i in range(64)]
ofdm = [sum(Minv[n][k] * bins[k] for k in range(64)) / 64.0 for n in range(64)]
pk = max(abs(x) for x in ofdm)
ofdm = [0.25 * x / pk for x in ofdm]

for name, sig in [("tone", tone), ("ofdm48", ofdm)]:
    ref = [sum(M64[r][c] * sig[c] for c in range(64)) for r in range(64)]
    sp = sum(abs(x)**2 for x in ref)
    for mode in ("unscaled_sat", "static_half", "bfp"):
        out, sh, ovf = fft64_q15(sig, mode)
        ep = sum(abs(ref[i] - out[i])**2 for i in range(64))
        print(f"{name:6s} {mode:12s} shifts={sh} sat={ovf:2d} SQNR={10*math.log10(sp/ep):6.2f} dB")
```

Observed results:
- **Kronecker identities**: `DFT_12 (3x4)` `8.671e-16`; `DFT_64 (8x8)` `3.408e-15`; `DFT_64 (4x16)` `3.788e-15`; `DFT_64 (16x4)` `3.788e-15`; `DFT_64 (2x32)` `4.392e-15`.
- **Q1.15 64-point FFT SQNR**: Single-tone (`amp=0.5`): `unscaled_sat = 0.25 dB` (`50` saturations), `static_half = 80.77 dB` (`0` saturations), `bfp = 80.77 dB` (`0` saturations). 48-subcarrier OFDM (`peak=0.25`): `unscaled_sat = 73.28 dB`, `static_half = 44.56 dB` (`-28.72 dB` penalty), `bfp = 73.28 dB`.
- **Ziria scrambler AutoLUT**: `w=8 -> 65,536 B (64.0 KiB, fits_256KiB=True)`; `w=10 -> 393,216 B (384.0 KiB, fits_256KiB=False)`.

## Revalidation

To cheaply verify whether these findings remain accurate after upstream changes or when targeting new wireless standards (`Wi-Fi 7` 320 MHz / `4096-QAM`, `5G NR` `FR2`):

1. **Ziria compiler invariant checks**:
   - Inspect `src/Codegen/LUTAnalysis.hs` (`shouldLUT`, `mIN_OP_COUNT`) and `src/Opts.hs` (`mAX_LUT_SIZE_DEFAULT`) for changes to AutoLUT thresholds; re-run the table-size formula $2^{w_{\text{in}}} \cdot \lceil w_{\text{out}}/8 \rceil$ against any new scrambler/interleaver vector width.
   - Check `src/BasicTypes/AstComp.hs` (`GCTy`, `Par`) and `src/Vectorize/CardAnalysis.hs` (`Card`) if adding new dynamic-rate stream combinators.
2. **SPIRAL breakdown & fixed-point SQNR checks**:
   - Diff `namespaces/spiral/transforms/dft/dft_rules.gi` (`DFT_CT` and twiddle scaling rules) and `namespaces/spiral/code/types.gi` (`TFixedPt`).
   - Re-run the `Q1.15` / `Q1.23` fixed-point probe with target FFT size (e.g., `N = 256` for 802.11ax 20 MHz, `N = 1024` for 80 MHz, `N = 4096` for Wi-Fi 7 320 MHz) and compare output SQNR against the standard's EVM floor (`-32 dB` for 256-QAM, `-35 dB` for 1024-QAM, `-38 dB` for 4096-QAM).
3. **HELIX Coq verification scope checks**:
   - Diff `vzaliva/helix` `coq/LLVMGen/TopLevel.v` (`Lemma top_to_LLVM`) and `Makefile` (`TESTVOFILES`) to verify whether `top_to_LLVM` has been generalized beyond `DynWin_FHCOL_hard`, whether real-to-float axioms have been replaced by fully mechanized Flocq/Gappa proofs, and whether `coqchk` / `Print Assumptions top_to_LLVM.` reports any newly introduced axioms.
