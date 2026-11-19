# Kulisch Superaccumulators, Ozaki INT8 Matrix Splits, and OCP Microscaling Formats

## Summary

Floating-point addition and fused matrix-multiply-accumulate (`MMA`) are non-associative, while modern AI and scientific accelerators increasingly replace native IEEE 754 `binary64` (`FP64`) units with narrow integer (`INT8`) or block-scaled (`MXFP8`/`MXFP6`/`MXFP4`) tensor engines. Three complementary numerical architectures govern bit-reproducibility, high-precision recovery, and block-exponent quantization across these substrates:

1. **Exact Fixed-Point Superaccumulators (`Kulisch` & Binned GPU Trees):** Mapping finite `binary64` operands (subnormal LSB $2^{-1074}$ to normal MSB $2^{1023}$; product LSB $2^{-2148}$ to MSB $2^{2047}$) into a `4288`–`4352`-bit fixed-point two's-complement register (or `320 B` shared-memory exponent-binned carry-save banks) makes parallel summation strictly associative and commutative prior to a single final IEEE rounding step—eliminating thread-count, MPI halo-order, and GPU warp-scheduling bit drift at `< 1.15x` HBM-bandwidth cost.
2. **Error-Free Limb Slicing on Integer Matrix Units (`Ozaki` Scheme / `ozIMMU`):** `enp1s0/ozIMMU` (`08eea9231729d54dbfd92955f2cbfc21ec236856`) decomposes each `FP64` matrix row/column relative to its maximum exponent into $S \in [3, 18]$ signed `int8_t` slices of width $b(K) = \min(7, \lfloor(31 - \lceil\log_2 K\rceil)/2\rfloor)$ bits—guaranteeing zero `int32_t` overflow across inner dimension $K$—and executes only the upper-left triangular index pairs $i + j \le S + 1$ ($S(S+1)/2$ `INT8` Tensor Core `GEMM`s rather than $S^2$), recovering full 53-bit `FP64` precision (`~2.7e-16` relative error) at $S \in \{8, 9\}$. Both Dekker–Knuth `TwoSum` error-free transformations and `Ozaki` limb splits fail silently if hardware Flush-to-Zero (`FTZ`) or Denormals-Are-Zero (`DAZ`) modes are active or if compilers contract `a * b - fl(a * b)` differently across targets.
3. **OCP Microscaling (`MX`) Shared `E8M0` Block Formats (`microxcaling` & `torchao`):** The `OCP MX v1.0` specification pairs $k = 32$ narrow elements (`MXFP8` `E4M3`/`E5M2`, `MXFP6` `E2M3`/`E3M2`, `MXFP4` `E2M1`, `MXINT8`) with one unsigned 8-bit power-of-two `E8M0` scale (bias `127`, byte `255` reserved for `NaN`, byte `0` representing $2^{-127}$—an **IEEE `binary32` subnormal** `0x00400000` that silently flushes to `0.0` under `FTZ`/`DAZ`!). Furthermore, `FLOOR` vs. `RCEIL` shared-scale selection creates an irreducible trade-off between **top-binade outlier saturation** (`FLOOR` clamping `[6.0, 8.0) -> 6.0` in `MXFP4`) and **`2x` whole-block resolution loss** (`RCEIL` bumping the shared exponent by $+1$ because of a single outlier), while row-wise forward vs. column-wise backward quantization breaks $(AB)^T = B^T A^T$ symmetry.

## Applicability

This report covers the joint numerical, compiler-IR, hardware-ISA, and formal-verification contract connecting:
- **`enp1s0/ozIMMU`** at commit `08eea9231729d54dbfd92955f2cbfc21ec236856` (CUDA `12.1+` `LD_PRELOAD` `cuBLAS` `dgemm`/`zgemm` interceptor targeting NVIDIA SM80/SM86/SM89/SM90 `INT8` Tensor Cores);
- **`microsoft/microxcaling`** at commit `7bc41952de394f5cc5e782baf132e7c7542eb4e4` (reference PyTorch/CUDA emulation of `OCP MX v1.0` element and shared-exponent quantization);
- **`pytorch/ao` (`torchao`)** at commit `a791dcb26432500f99d40271c81ee8e2753cf99a` (`torchao/prototype/mx_formats/`, native PyTorch `MXTensor` subclassing, `ScaleCalculationMode.FLOOR`/`RCEIL`, and `E8M0` bit-cast kernels);
- **`OCP Microscaling Formats (MX) Specification v1.0`** (normative bit layouts, `E8M0` bias/NaN rules, block size $k=32$, and conversion rounding); and
- **Kulisch exact fixed-point superaccumulation** (`DOI: 10.1145/1996068.1996070`) and **Collange–Defour–Graillat–Iakymchuk GPU binned superaccumulators** (`DOI: 10.1016/j.parco.2015.09.001`).

The subjects are analyzed **in combination** as alternative points on the precision–throughput–reproducibility Pareto frontier for compiler code generation, deterministic LLM inference/evaluation (e.g., Anthropic's November 2026 analyses of batch-size-induced GPU reduction nondeterminism), and certified scientific computing. Local execution evidence was gathered with Python `3.13` via the self-contained probe preserved at `probes/verify_numerics_and_mx.py`.

## Findings

### 1. Exact Associative Parallel Reductions via Kulisch and Binned Superaccumulators

`Basis: normative + derived + execution`

Standard IEEE 754 `binary64` (`FP64`) summation is non-associative because each intermediate addition rounds to 53 significand bits. When an ill-conditioned vector containing canceling large terms and small residuals—such as $512$ pairs of $(+10^{16}, -10^{16})$ shuffled with $(+0.5, +0.5, +0.5, -0.25, -0.25, -0.25)$ (exact sum $0.75$)—is reduced across varying thread counts or SIMD/SIMT tree widths (`1`, `4`, `16`, `64` leaves), intermediate sums absorb the $2^{-1}$ and $2^{-2}$ bits whenever partial sums sit at $|S| = 10^{16} \approx 2^{53.15}$ ($\mathrm{ulp}(10^{16}) = 2.0$), collapsing the computed result to `0.0` (`100%` relative error) or $\pm 2.0, \pm 4.0$ depending on warp scheduling (`probes/verify_numerics_and_mx.py`).

#### 1.1 Exact Bit-Width Geometry of the Kulisch Register
Every finite nonzero `binary64` number decomposes exactly as $x = (-1)^s \cdot M \cdot 2^{e_2}$, where $M \in [1, 2^{53}-1] \cap \mathbb{Z}$ and:
- For **subnormals** (`exp_field == 0`), $e_2 = -1074$ (LSB weight $2^{-1074}$);
- For **normals** (`exp_field` $\in [1, 2046]$), $M = 2^{52} + \text{mantissa}$ and $e_2 = (\text{exp\_field} - 1023) - 52 \in [-1073, 971]$ (MSB weight $2^{1023}$).

Consequently:
- **Exact Summation (`Dot1`):** Spanning bit weights $2^{-1074}$ through $2^{1023}$ requires $1023 - (-1074) + 1 = \mathbf{2098\text{ bits}}$ (`263 B`), plus $c$ guard/carry bits on the MSB allowing $2^c$ additions without overflow ($c = 62 \implies 2160\text{ bits} = 270\text{ B}$, or $34 \times \texttt{uint64\_t}$ words = `272 B`).
- **Exact Sum of Products (`Dot2` / Exact `FMA` Stream):** Exact unrounded products $x_i \cdot y_i$ span $2^{-2148}$ through $2^{2047}$ ($4196$ bits); Kulisch's canonical hardware layout (`DOI: 10.1145/1996068.1996070`) allocates **`4288` bits (`536 B`, `67` 64-bit words; `4352` bits / `544 B` with 64-bit alignment)** including carry headroom for $2^{92}$ product accumulations without overflow.

#### 1.2 GPU Shared-Memory Exponent-Binned Superaccumulators
Maintaining a `544 B` private array per GPU thread exceeds register-file budgets (`255 x 32-bit = 1020 B` total per thread on SM80/SM90). Collange et al. (`DOI: 10.1016/j.parco.2015.09.001`) exploit two structural properties for GPU warps:
1. **Warp-Shared Exponent Bins (`320 B`/warp):** Splitting the `2098`-bit `Dot1` range into $40$ overlapping `64`-bit signed integer bins (`40 x 8 B = 320 B` in shared memory per 32-thread warp, or `80` bins = `640 B` for `Dot2`) allows each lane $t \in [0, 31]$ to deposit its shifted mantissa into at most $2$ bins (`hi`, `lo`) via shared-memory `atomicAdd` (`int64` two's-complement addition is exact and order-independent modulo $2^{64}$, and signed carry bits propagate cleanly in a single final 40-lane prefix scan!).
2. **Final Single-Rounding Theorem:** Once all threadblocks reduce their `40`-word integer arrays elementwise into one global `40`-word accumulator and propagate carries, finding the highest nonzero bit `msb_idx` and applying IEEE round-to-nearest-even (`rem > half || (rem == half && (q & 1))`) produces the **exact `RN(sum_i x_i)`** identical across `1` CPU core, `8` SIMD lanes, or `4,096` GPU warps (`probes/verify_numerics_and_mx.py`: all `16` random tree permutations yield exact `0.75`).

---

### 2. The Ozaki Scheme & `ozIMMU` INT8 Tensor Core `DGEMM` Emulation

`Basis: source + derived + execution`

Direct inspection of `enp1s0/ozIMMU` (`08eea9231729d54dbfd92955f2cbfc21ec236856`) establishes how `FP64` general matrix multiplication ($C = \alpha \mathrm{op}(A)\mathrm{op}(B) + \beta C$) is mapped onto hardware `INT8` Tensor Cores (`mma.sync.aligned.m16n8k32.s32.s8.s8.s32` accumulating into exact `int32_t`).

#### 2.1 Non-Overflowing Slice Bit-Width Formula (`src/split.cu:520–536`)
In `mtk::ozimmu::get_bits_per_int8(uint32_t k)` (`src/split.cu:520`), `ozIMMU` computes $\ell = \lceil \log_2 k \rceil$ for inner dimension $k \ge 1$ and sets the per-slice unsigned mantissa bit-width to:
$$b(k) = \min\!\left(7,\; \left\lfloor \frac{31 - \lceil \log_2 k \rceil}{2} \right\rfloor\right)$$
Because each signed `int8_t` slice entry satisfies $|a^{(s)}_{m,t}|, |b^{(r)}_{t,n}| \le 2^{b(k)} - 1 < 2^{b(k)}$, any inner-product sum of $k$ products satisfies:
$$\left|\sum_{t=0}^{k-1} a^{(s)}_{m,t}\, b^{(r)}_{t,n}\right| \le k \cdot \left(2^{b(k)} - 1\right)^2 < 2^{\lceil \log_2 k \rceil + 2 b(k)} \le 2^{31} - 1$$
guaranteeing **zero signed `int32_t` wraparound** inside the hardware `INT8 -> INT32` Tensor Core accumulator up to $k = 2^{29}$ (`b=7` holds up to $k \le 2^{31 - 14} = 131{,}072$; at $k = 262{,}144$, $b$ automatically drops to `6` bits!).

#### 2.2 Row/Column Exponent Alignment & `__uint128_t` Slicing (`src/split.cu:13–262`)
1. **Per-Vector Max Exponent (`get_exp_max_element`, lines `13–67`):** One threadblock (`block_size = 256`) processes each row of $\mathrm{op}(A)$ (and column of $\mathrm{op}(B)$), masking the 11-bit `FP64` exponent (`mask_exponent(*local_ptr)`), reducing via `__shfl_xor_sync` + `smem[32]`, and scaling by `x2(...)` (`split.cu:202`) so all normalized magnitudes in row $i$ are strictly $< \text{max\_exp}_i$.
2. **Bitwise Limb Extraction (`cut_int8_core<double, __uint128_t>`, lines `155–185`, `256`):** Each `FP64` input's 52-bit stored mantissa plus implicit leading `1` bit (`53` bits total) is shifted to the MSB of a `128`-bit unsigned integer (`__uint128_t`), right-shifted by the relative exponent difference $(\text{exp}(\text{max\_exp}_i) - \text{exp}(a_{i,t}))$, and sliced sequentially into `num_split` $= S$ signed `int8_t` planes stored contiguously with stride $N = m \cdot \text{ldo}$ (`split.cu:176–184`).

#### 2.3 Upper-Left Triangular `INT8` GEMM Schedule (`src/config.cu:85–95`)
In `get_split_config(compute_mode)` (`src/config.cu:4–100`), modes `fp64_int8_3` through `fp64_int8_18` create $S$ `int8` slice matrices $A^{(1)}, \dots, A^{(S)}$ and $B^{(1)}, \dots, B^{(S)}$ (`1`-indexed from MSB to LSB) and emit only pairs $(j, r)$ with $j + r = \text{sum}$ for $\text{sum} \in [2, S + 1]$ (`lines 86–92`):
$$\text{Total INT8 Tensor Core GEMMs} = \sum_{\text{sum}=2}^{S+1} (\text{sum} - 1) = \frac{S(S + 1)}{2}$$
Rather than $S^2$ `GEMM`s, `ozIMMU` prunes the lower-right $(S(S-1)/2)$ cross-terms whose bit weights lie at least $(S + 1) \cdot b(k)$ bits below $\text{max\_exp}_A + \text{max\_exp}_B$. Our executable probe (`probes/verify_numerics_and_mx.py`, $K=256 \implies b(K)=7$) confirms the exact error trajectory:
- `fp64_int8_3` ($6$ `INT8` GEMMs, $21$ bits): relative error `1.10e-06` (`FP32`-grade);
- `fp64_int8_5` ($15$ `INT8` GEMMs, $35$ bits): relative error `8.51e-11`;
- `fp64_int8_7` ($28$ `INT8` GEMMs, $49$ bits): relative error `8.59e-15`;
- `fp64_int8_8` ($36$ `INT8` GEMMs, $56$ bits) and `fp64_int8_9` ($45$ `INT8` GEMMs, $63$ bits): relative error **`2.73e-16`** (full 53-bit `FP64` accuracy!).

When elements within a single row have wide dynamic range ($> 2^{15}$), small elements right-shift past $S \cdot b(k)$ bits during `split_int8_kernel`; `auto_mode_select` (`include/ozimmu/ozimmu.hpp:84–93`, `src/split.cu:455–518`) scans actual mantissa bit loss (`get_mantissa_loss_total`) to select $S$ dynamically.

---

### 3. OCP Microscaling (`MX`) `E8M0` Formats, Scale Modes, and Subnormal/`FTZ` Hazards

`Basis: normative + source + execution`

Inspection of `OCP MX Specification v1.0`, `microsoft/microxcaling` (`7bc41952de394f5cc5e782baf132e7c7542eb4e4`), and `pytorch/ao` (`a791dcb26432500f99d40271c81ee8e2753cf99a`) establishes the exact bit-level representation and failure modes of block-scaled formats (`block_size = 32` along reduction axis $K$).

#### 3.1 Normative Parameter Table (`torchao/prototype/mx_formats/constants.py:25–64`)

| OCP MX Format | Element Bits `(S, E, M)` | Exp Bias | Max Normal (`MAX`) | Max Pow2 (`2^emax`) | Min Subnormal | Shared Scale (`k=32`) | Effective Bits / Value |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
| **`MXFP8 E5M2`** | `(1, 5, 2)` | `15` | `57344.0` | `32768` (`2^15`) | $2^{-16}$ | `8-bit E8M0` | `8.25 b` |
| **`MXFP8 E4M3`** | `(1, 4, 3)` | `7` | `448.0` | `256` (`2^8`) | $2^{-9}$ | `8-bit E8M0` | `8.25 b` |
| **`MXFP6 E3M2`** | `(1, 3, 2)` | `3` | `28.0` | `16` (`2^4`) | `0.0625` ($2^{-4}$) | `8-bit E8M0` | `6.25 b` |
| **`MXFP6 E2M3`** | `(1, 2, 3)` | `1` | `7.5` | `4` (`2^2`) | `0.125` ($2^{-3}$) | `8-bit E8M0` | `6.25 b` |
| **`MXFP4 E2M1`** | `(1, 2, 1)` | `1` | `6.0` | `4` (`2^2`) | `0.5` ($2^{-1}$) | `8-bit E8M0` | `4.25 b` |
| **`MXINT8`** | `2's comp (-128 unused)` | N/A | `1 + 63/64` | `1` (`2^0`) | $2^{-6}$ | `8-bit E8M0` | `8.25 b` |

*(Note: `MXFP6` and `MXFP4` define no element-level `Inf`/`NaN` encodings, dedicating all $2^6 = 64$ and $2^4 = 16$ bit patterns to signed finite normals/subnormals; `NaN` propagation relies on setting the block's shared `E8M0` scale byte to `255` (`0xFF`, `E8M0_EXPONENT_NAN_VAL`, `constants.py:42`)!)*

#### 3.2 Three Critical Quantization & Hardware Hazards Caught in Source and Execution
1. **The `E8M0 == 0` / Reciprocal `E8M0 == 254` `FTZ`/`DAZ` Subnormal Trap (`mx_tensor.py:118–156`):**
   `E8M0` encodes $X = 2^{u - 127}$ for $u \in [0, 254]$. When $u = 0$, $X = 2^{-127}$. In IEEE `binary32`, the minimum normal is $2^{-126}$ (`0x00800000`), so **$2^{-127}$ is the largest `FP32` subnormal (`0x00400000`, `biased_exp == 0`, `mantissa == 1 << 22`)**—explicitly special-cased in `torchao`'s `mx_tensor.py:148–150`! Furthermore, when quantizing a large dynamic-range block with $u = 254$ ($X = 2^{+127}$), `mx_tensor.py:134–136` computes `reciprocal_e8m0_biased = 2 * 127 - 254 = 0`, casting the scale reciprocal to `0x00400000`! If `MXCSR.DAZ`/`FZ` (`x86_64`) or `FPCR.FZ` (`AArch64`) is enabled (`torch.set_flush_denormal(True)`), `0x00400000` flushes to `0.0`, silently zeroing the entire quantized block on $u = 254$ (`val * 0.0 == 0`) or producing `0/0 = NaN`! Similarly, `TwoSum(2^-980, 2^-1035)` loses `100%` of its `2.716e-312` residual under `FTZ` (`probes/verify_numerics_and_mx.py`).
2. **`FLOOR` Top-Binade Clipping vs. `RCEIL` Outlier Starvation (`mx_ops.py:76–80`, `mx_readme.md:260–262`, `mx_tensor.py:104–126`):**
   Under `OCP MX v1.0` baseline `FLOOR` (`shared_exp = floor(log2(amax)) - emax_elem`), any value in the top non-power-of-two binade $(2^{\text{emax}}, \text{MAX}]$ of the next octave—for example, `7.8` in `MXFP4 E2M1` where `MAX = 6.0` and `2^emax = 4.0`—selects `floor(log2(7.8)) - 2 = 0` (`scale = 1.0`), **clamping `7.8 -> 6.0` (`-23.1%` outlier error)** (`mx_readme.md:261–262`: `1.99 -> 1.5`). Switching to `ScaleCalculationMode.RCEIL` (`ceil(log2(amax / MAX))`, `mx_tensor.py:104`) bumps `scale` to `2.0`, preserving `7.8 -> 8.0` **at the cost of halving resolution for all 31 co-habiting elements** (flushing `31` values of `0.375` to `0.0` in `probes/verify_numerics_and_mx.py`!). Unbiased stochastic rounding (`NVFP4` / `Hadamard` random rotations prior to MX block formation) mitigates outlier correlation across training steps.
3. **Transpose & Reduction-Axis Non-Commutativity:** Because the `E8M0` scale is shared strictly along the $K$-contraction dimension of `GEMM` (`1x32` row blocks of $A$, `32x1` column blocks of $B$), forward pass $Y = X W^T$ quantizes $W$ along `in_features`, whereas weight-gradient backprop $\mathrm{d}X = \mathrm{d}Y \cdot W$ requires `MX` blocks along `out_features`—forcing dual transposed `MX` casts (`MXFP8Dim0CastKernelChoice`, `mx_tensor.py:41`) where $\mathrm{quant}_{\text{row}}(W)^T \ne \mathrm{quant}_{\text{col}}(W^T)$.

---

### 4. Six-Level Performance & Resource Footprint Profile (`L1`–`L6`)

`Basis: source + derived + execution`

| Level | Metric | Legacy Native / Manual CUDA | `Kulisch` / Binned GPU Tree | `ozIMMU` (`fp64_int8_8..9`) | `OCP MX` (`MXFP8` / `MXFP4`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`L1` Authoring & Tokens** | Kernel LoC & Proof/Tuning Cost | `800–2,500` CUDA LoC; manual warp-shuffle proofs | `1` precision attribute (`ExactSum`); `~15` LoC proof | `0` app LoC (`LD_PRELOAD` `libozimmu.so`) or `1` mode tag | `~10` LoC `MXTensor` wrapper; requires `FLOOR`/`RCEIL` audit |
| **`L2` Toolchain Build** | Framework Clean Build & RSS | `cuBLAS`/LLVM `45–140 s`, `3+ GB` RSS | Header/IR lowering `< 0.4 s`, `< 40 MB` RSS | `CMake + nvcc` (`7` `.cu` files) `~18 s`, `~1.1 GB` `ptxas` RSS | Pure Python + JIT CUDA ext `~12 s` (`microxcaling`/`torchao`) |
| **`L3` Comp / Synth / LSP** | Static Range / Precision Check | Manual or `Z3` FP bit-blasting (`> 10 s` timeouts) | `O(1)` exponent-span & carry-bit check (`< 1 ms`) | `O(1)` $b(k) = \min(7, \lfloor(31-\lceil\log_2 k\rceil)/2\rfloor)$ (`< 1 ms`) | `< 5 ms` dyadic check for `FTZ=off` & axis alignment |
| **`L4` Runtime Speed** | Throughput vs. Consumer/DC `FP64` | `1.0x` DC `FP64`; **`1/64x` consumer GPU `FP64`**; non-reproducible | **`0.88–0.95x` HBM peak** (`> 1.8 TB/s`), **`0`-bit drift** | **`2.2x–6.8x` faster** than consumer/L40S `FP64` (`36–45` INT8 GEMMs) | **`2.0x–4.0x` Tensor Core TOPS** over `BF16`/`FP16` (SM100/MI300/B200) |
| **`L5` Proof / Cert Check** | Independent Replay Latency | Intractable for bit-blasted `FP64` trees | **`< 0.5 ms`** (`c >= ceil(log2 N)` + `RN` bit check) | **`< 0.8 ms`** (non-overflow $k(2^b-1)^2 < 2^{31}$ + slice bound) | **`< 0.6 ms`** (`E8M0` `NaN`/`subnormal` guard check) |
| **`L6` Memory & Energy** | Workspace / Wire / Register Bytes | `8 B`/elem (`FP64`), `0` scratch | **`320 B`/warp** (`Dot1`) or `544 B` (`Dot2`), `0` global alloc | **`m*n*12 B + (m*k + k*n)*S B`** GPU workspace (`gemm.cu:359–442`) | **`1.031x` element bytes** (`4.25–8.25` bits/val; `47–73%` HBM drop) |

---

### 5. Human Comprehensibility (`C1`) & Universal Conceptual Simplicity (`C2`) Analysis

`Basis: derived + source`

- **`(C1)` Human Comprehensibility & Mental-Model Alignment:**
  - *Eliminating Silent Heisenbugs:* Engineers naturally reason about $\sum_i x_i$ and $A \cdot B$ as associative real-valued algebra (`SMoL` mental model), not binary reduction trees sensitive to tensor-parallel degree or dynamic batching. Exposing `ExactSum` (Kulisch) makes surface syntax match mathematical associativity 1-to-1, whereas `-ffast-math` or silent `FTZ` flags create non-local debugging nightmares.
  - *Legible Quantization Diagnostics:* Rather than mysterious `NaN` loss spikes at step `40,000`, `MX` compilation should surface concrete `32`-element block counterexamples showing outlier vs. underflow trade-offs (`[7.8, 0.375, ...] -> FLOOR clips 7.8 to 6.0; RCEIL flushes 31 lanes to 0.0`).
- **`(C2)` Orthogonality, Stratum Separation & Anti-Adapter Refinement:**
  - *One Indexed Representation Family, Not Three Disjoint Ad-Hoc Stacks:* All three paradigms are instances of **Block-Exponent Fixed-Point Slicing** parameterized by `(BlockExtent B, SliceCount S, MantissaBits b, RoundingLaw)`:
    1. **Kulisch (`B = all, S = 1, b = 4288, ExactRN`):** Single global exponent base $2^{-2148}$, exact integer sum;
    2. **Ozaki / `ozIMMU` (`B = row/col, S = 3..18, b = b(K) <= 7, TriangularAccum`):** Vector-shared base $\text{max\_exp}_i$, multi-limb exact `INT32` dot products;
    3. **OCP `MX` (`B = 32, S = 1, b = 2..8, RNE | Stochastic`):** 32-element micro-block `E8M0` base, single low-bit slice.
  - *Hardware-Quirk Isolation:* Keeping `FTZ=0`/`FMA=explicit` inside machine-checked target preconditions avoids `O(N)` defensive wrappers while preserving zero-overhead hardware lowering.

## Boundaries

- **Actual NVIDIA SM89/SM90/SM100 Silicon Timing (`not examined` directly):** No physical GPU hardware is attached to the analysis sandbox; `ozIMMU` CUDA sources (`src/split.cu`, `src/gemm.cu`, `src/config.cu`) and `torchao`/`microxcaling` kernels were verified by direct source inspection and exact bit-level Python simulation (`probes/verify_numerics_and_mx.py`), while hardware TFLOPS ratios rely on Ootomo et al. (`DOI: 10.1177/10943420241239588`) and Rouhani et al. (`DOI: 10.1145/3579371.3589351`).
- **Extreme Dynamic-Range Rows in Fixed-Split `Ozaki` (`known not to apply`):** Fixed-mode `ozIMMU` (`fp64_int8_8` without `fp64_int8_auto` or iterative residual refinement) does **not** guarantee 53-bit accuracy when elements within the *same* row/column span $> S \cdot b(K)$ binary orders of magnitude (e.g., $10^{20}$ alongside $1.0$ in one row shifts $1.0$ to zero in all $8 \times 7 = 56$ bits, unlike a `4288`-bit Kulisch register).
- **Non-Finite `Inf`/`NaN` Propagation in `Kulisch` and `ozIMMU` (`unsupported` / `known not to apply`):** Integer fixed-point superaccumulators and `INT8` Tensor Cores have no in-band `Inf`/`NaN` bit patterns; inputs containing `Inf`/`NaN` must be tracked via a parallel 1-bit `isfinite` mask (`get_exp_max_element` in `ozimmu_split.cu:26` masks raw `0x7FF` exponent bits without `NaN` short-circuiting).
- **Vendor Proprietary `NVFP4` (`E2M1` + `FP8 E4M3` 16-Element Scale) Hardware Rounding Micro-Ops (`unknown`):** While `OCP MX v1.0` (`E8M0` over $k=32$) is public and normative, exact sub-ULP tie-breaking inside proprietary Blackwell `tcgen05.mma` silicon microcode for non-OCP `NVFP4` ($k=16$ `E4M3` scale) is undocumented publicly and marked `unknown`.

## Evidence

1. **Primary Upstream Repositories (Immutable 40-Hex Revisions Inspected on `2026-11-19`):**
   - `enp1s0/ozIMMU` @ `08eea9231729d54dbfd92955f2cbfc21ec236856`:
     - `include/ozimmu/ozimmu.hpp` (`lines 14–36`: `compute_mode_t` `fp64_int8_3..18` & `fp64_int8_auto`; `line 100`: `get_bits_per_int8`);
     - `src/split.cu` (`lines 13–67`: `get_exp_max_element`; `lines 155–185`: `cut_int8_core<INPUT_T, __uint128_t>`; `lines 194–262`: `split_int8_kernel`; `lines 520–536`: `get_bits_per_int8(k) = min(7, (31 - ceil(log2(k))) / 2)`);
     - `src/config.cu` (`lines 85–95`: upper-left triangular `sum <= num_split + 1` `int8tc` pair schedule);
     - `src/gemm.cu` (`lines 354–445`: workspace layout `c_f64_ptr`, `a_max_exp_ptr`, `b_max_exp_ptr`, `c_i32_ptr`).
   - `microsoft/microxcaling` @ `7bc41952de394f5cc5e782baf132e7c7542eb4e4`:
     - `mx/mx_ops.py` (`lines 49–93`: `_shared_exponents` `floor(log2(max(|A|)))`, `NaN` overflow & `-127` clamp; `lines 95–168`: `_reshape_to_blocks` 32-element tiling);
     - `mx/simd_ops.py` (`lines 39–130`: `SIMDAdd`/`SIMDSub` backward `vec_quantize` broadcast reductions);
     - `README.md` (`lines 260–268`: `[1.5, 2.0) -> 1.5` `FLOOR` clipping & symmetric `MXINT` 2's complement).
   - `pytorch/ao` @ `a791dcb26432500f99d40271c81ee8e2753cf99a`:
     - `torchao/prototype/mx_formats/constants.py` (`lines 25–64`: exact `MAX`, `MAX_POW2`, `EXP_BIAS`, `E8M0_EXPONENT_BIAS = 127`, `E8M0_EXPONENT_NAN_VAL = 255`);
     - `torchao/prototype/mx_formats/mx_tensor.py` (`lines 101–156`: `ScaleCalculationMode.FLOOR` vs `RCEIL`, `0x00400000` `FP32` subnormal handling for `E8M0 == 0` and `reciprocal_e8m0_biased`).
2. **Normative Standards & Peer-Reviewed Literature:**
   - Open Compute Project, *OCP Microscaling Formats (MX) Specification Version 1.0* (`2023`, §5.2–§5.4).
   - Ulrich W. Kulisch, *"Very fast and exact accumulation of products"*, *Computing* / *ACM TOMS* `37(4)` (`2011`, `DOI: 10.1145/1996068.1996070`).
   - Sylvain Collange, David Defour, Stef Graillat, Roman Iakymchuk, *"Numerical reproducibility for the parallel reduction on multi- and many-core architectures"*, *Parallel Computing* `49`, pp. `83–97` (`2015`, `DOI: 10.1016/j.parco.2015.09.001`).
   - Katsuhisa Ozaki, Takeshi Ogita, Shin'ichi Oishi, Siegfried M. Rump, *"Error-free transformations of matrix multiplication by using fast routines of matrix multiplication and its applications"*, *Numerical Algorithms* `59(1)`, pp. `95–118` (`2012`, `DOI: 10.1007/s11075-011-9566-x`).
   - Hiroyuki Ootomo, Katsuhisa Ozaki, Rio Yokota, *"DGEMM on integer matrix multiplication unit"*, *Int. J. High Performance Computing Applications* `38(4)`, pp. `297–313` (`2024`, `DOI: 10.1177/10943420241239588`, `arXiv:2306.11975`).
   - Bita Darvish Rouhani et al., *"With Shared Microexponents, A Little Shifting Goes a Long Way"*, *ISCA '23* (`2023`, `DOI: 10.1145/3579371.3589351`).
3. **Preserved Executable Verification Probe (`Basis: execution`):**
   - `probes/verify_numerics_and_mx.py` (Python 3 standard library only; deterministic seed `20261119`), executed via `python3 reports/kulisch-superaccumulators-ozaki-matrix-splits-and-ocp-microscaling-formats/probes/verify_numerics_and_mx.py` (`exit 0`), verifying `0.0` `FP64` tree collapse vs. `0.75` exact Kulisch invariance across `16` permutations, `ozIMMU` `fp64_int8_3..10` error decay to `2.73e-16`, `TwoSum` `FTZ` residual erasure + `0x00400000` `E8M0` subnormal bit pattern, and `MXFP4` `FLOOR` (`6.0`/`0.5`) vs. `RCEIL` (`8.0`/`0.0`) divergence.

## Revalidation

1. **Re-run the Preserved Bit-Exact Probe (`< 50 ms`, zero dependencies):**
   ```bash
   python3 reports/kulisch-superaccumulators-ozaki-matrix-splits-and-ocp-microscaling-formats/probes/verify_numerics_and_mx.py
   ```
   Confirm `exit 0` and verify JSON invariants: `kulisch_16_permutations_exact == 0.75`, `ozimmu_int8_sweep.fp64_int8_9.rel_error < 1e-15`, `e8m0_byte0_fp32_hex == "0x400000"`, and `mxfp4_floor_vs_rceil`.
2. **Upstream Source Drift Checks:**
   - In `enp1s0/ozIMMU`, diff `src/split.cu` (`get_bits_per_int8`, `cut_int8_core`) and `src/config.cu` (`get_split_config`) if newer commits add `FP8` Tensor Core Ozaki modes (`Ozaki-II` Chinese Remainder Theorem modular variants) or alter diagonal pruning (`sum <= num_split + 1`).
   - In `pytorch/ao`, diff `torchao/prototype/mx_formats/mx_tensor.py` around `ScaleCalculationMode` (`TODO: flip default to RCEIL`) and `_TORCH_VERSION_AT_LEAST_2_14` hardware `E8M0` cast lowerings.
