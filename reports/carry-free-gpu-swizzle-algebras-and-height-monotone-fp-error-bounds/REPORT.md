# Carry-Free GPU Swizzle Algebras and Height-Monotone Floating-Point Error Bounds

## Summary

Modern GPU tensor compilers couple three mathematically incompatible layers—integer-additive hierarchical memory layouts $(\mathbb{Z}, +)$ composed with bitwise-XOR shared-memory swizzles $(\mathbb{F}_2^w, \oplus)$, algebraic sparse zero-skipping rewrites, and autotuned parallel floating-point reduction schedules. Direct source inspection and executable verification across NVIDIA CUTLASS/CuTe, Triton, Finch, LLVM, LAProof, FPTaylor, and Gappa establish four core engineering invariants:

1. **Exact Carry-Free Semidirect Swizzle Fragment $\mathcal{CF}(B, M, S)$ (`Basis: source + derived + execution`):** `cute::Swizzle<B, M, S>` (`NVIDIA/cutlass` `include/cute/swizzle.hpp:54-96`) is an $\mathbb{F}_2$-linear involution that couples non-linearly with integer layout addition whenever carries cross bit $M$ or bit $M+B$ (producing silent 32-byte address jumps on Hopper `Swizzle<3, 4, 3>`). Sub-tile translation invariance $\sigma(a + b) = \sigma(a) + b$ holds across coset $a \equiv r_0 \pmod{2^M}$ **if and only if** $r_0 + b < 2^M$. Restricting CuTe layouts to the 3-tier stratified normal form $L(\vec{x}_{\text{out}}, x_{\text{bank}}, x_{\text{vec}}) = 2^{M+B} A_{\text{out}}(\vec{x}_{\text{out}}) + 2^M x_{\text{bank}} + x_{\text{vec}}$ ($S \ge B > 0$, $x_{\text{bank}} < 2^B$, $x_{\text{vec}} < 2^M$) decouples $(\mathbb{Z}, +)$ and $\mathbb{F}_2^B$ into an exact semidirect closed form verifiable in $O(r)$ integer arithmetic without bitvector SAT, making non-aliasing pure Presburger arithmetic and 32-bank GPU shared-memory column-load bank-conflict freedom an $O(1)$ test: **conflict-free iff $\gcd(s, 2^B) = 1$** (eliminating 8-way conflicts on 128-byte Hopper tiles). Negative shifts ($S \le -B < 0$) require 4-window isolation, explaining algebraically why Hopper/Blackwell WGMMA/TMA hardware exclusively uses $S \ge B > 0$.
2. **Sparse Zero-Skipping Violates IEEE Std 754-2019 Without Explicit Guard Regimes (`Basis: normative + source + execution`):** Sparse tensor compilers such as `Finch.jl` (`src/symbolic/symbolic.jl:18-19, 67, 112, 172`) declare `+` associative, `*` distributive over `+`, `iszero(x)` an additive identity for `+`, and `iszero(x)` a multiplicative annihilator for `*`. Under strict IEEE Std 754-2019 (Clauses 6.3 and 7.2), all four axioms fail: $+0.0 \times (+\infty) = \mathrm{NaN}$, $+0.0 \times \mathrm{NaN} = \mathrm{NaN}$, $+0.0 \times (-1.0) = -0.0$ (`0x8000000000000000`), $(-0.0) + (+0.0) = +0.0$ in `roundTiesToEven` (and $(+0.0) + (-0.0) = -0.0$ under `FE_DOWNWARD`), reassociation yields 100% relative error or spurious overflow, and FMA contraction changes bit values (`0.0` vs $-2^{-54}$). Sound sparse/schedule compilation requires explicit numeric preservation regimes corresponding to LLVM `FastMathFlags` (`NoNaNs`, `NoInfs`, `NoSignedZeros`, `AllowReassoc`, `AllowContract` in `llvm/include/llvm/IR/FMF.h:31-40`).
3. **Height-Monotone Reduction-Tree Bounds Decouple Autotuning from Re-Verification (`Basis: normative + source + derived + execution`):** For any binary reduction tree $T$ over active finite non-zero products $S$ with maximum leaf addition depth (height) $h(T)$, the forward rounding error under a schedule-uniform no-overflow envelope satisfies:
   $$\Big|\widehat{y}_T - \sum_{i=1}^n a_i b_i\Big| \;\le\; \sum_{i \in S} g(d_T(i)+1)\,|a_i b_i| + (1 + g(h(T)))\,|S|\,\eta \;\le\; g(h(T)+1)\sum_{i \in S}|a_i b_i| + (1 + g(h(T)))\,|S|\,\eta$$
   where $g(k) = (1 + u)^k - 1 \le \gamma_k = \frac{ku}{1 - ku}$ (`VeriNum/LAProof` `accuracy_proofs/common.v:436, 494-495`, Higham 1993/2002). Because the bound is monotone in $(h(T), |S|)$, verifying a sequential baseline ($h_0 = n - 1$) once in LAProof/FPTaylor lets an autotuner freely explore millions of tiled, SIMD, warp-shuffle, and sparse-pruned schedules $T'$ via an **$O(1)$ integer check $h(T') \le h_{\max}$** with zero solver re-invocation.
4. **Precision-Specific Underflow & Tightening Boundaries (`Basis: execution + derived`):** Across 516 reduction trees in exact `binary32` vs. arbitrary-precision `Fraction` (`0` violations), balanced trees tighten bounds by **`4.86x–6.86x`** on normal-range datasets, but yield **`1.00x`** on deeply subnormal products where the leaf underflow term $|S|\eta$ dominates by $> 10^{17}\times$. Mixed-precision `binary16 -> binary32` eliminates *both* leaf rounding and leaf underflow (`6400/6400` exact products), whereas `bfloat16 -> binary32` eliminates normal-range product rounding **only** and still suffers product underflow (`2^-80 * 2^-80 -> 0.0`) and overflow (`2^80 * 2^80 -> +inf`).

## Applicability

This report integrates thirteen pinned upstream repositories, formal specifications, and peer-reviewed foundations across GPU layout algebra, sparse tensor compilation, and mechanized floating-point verification:

| Domain Layer | Examined Subjects | Role in This Synthesis |
| :--- | :--- | :--- |
| GPU Tensor Layout & Swizzle Algebra | **`NVIDIA/cutlass`** (`dc6ae46e...`); **`triton-lang/triton`** (`458c1a25...`); **Cecka** (`arXiv:2603.02298`); **Carlisle et al.** (`arXiv:2601.05972`) | Contrasts CuTe's hybrid $(\mathbb{Z}, +)$ layout + $\mathbb{F}_2$ `Swizzle<B,M,S>` + `MixedBits` against Triton's pure $\mathbb{F}_2$ `LinearLayout`; grounds Hopper WGMMA SMEM swizzle atoms. |
| Sparse Coiteration & FP Semantics | **`finch-tensor/Finch.jl`** (`7aa1ca16...`, `10.1145/3720473`); **IEEE Std 754-2019** (`10.1109/IEEESTD.2019.8766229`); **`llvm/llvm-project`** (`7d9cd0de...`) | Connects Finch's symbolic algebra predicates (`isannihilator`, `isidentity`, `isassociative`) to exact IEEE-754 Clauses 6.3/7.2 violations and LLVM `FastMathFlags`. |
| Analytical & Mechanized FP Error Bounds | **Higham** (`10.1137/1.9780898718027`, `10.1137/0914050`); **Jeannerod & Rump** (`10.1137/120894488`); **`VeriNum/LAProof`** (`86a9a74a...`, `10.1109/ARITH58626.2023.00021`); **`VeriNum/vcfloat`** (`a203b287...`); **`soarlab/FPTaylor`** (`b5a77cae...`, `10.1145/3230733`); **Gappa** (`10.1145/1644001.1644003`) | Unifies worst-case rounding-error constants ($ku < g(k) < \gamma_k$), underflow residuals ($g_1$), sparse `nnzR` refinement, symbolic Taylor error propagation, and tool capabilities. |

**Scope & Constraints:**
- The carry-free fragment $\mathcal{CF}(B, M, S)$ applies to any bit-XOR swizzle matching `cute::Swizzle<B, M, S>` (used across NVIDIA Ampere `ldmatrix`, Hopper WGMMA/TMA `SW32`/`SW64`/`SW128`, and Blackwell UMMA shared-memory tiles) on 32-bank, 4-byte-stride shared memory.
- Height-monotone error-bound transfer applies to **IEEE-754 compliant binary floating-point accumulators** (default `roundTiesToEven`, gradual underflow enabled, no flush-to-zero) over inner products, GEMM/SpMM contractions, and twice-differentiable outer expressions consuming scalar reductions. Non-IEEE GPU tensor-core accumulation modes (e.g., Hopper/Blackwell internal reduced-mantissa `fp22` accumulators or block-scaled `MXFP4`/`MXFP8` microscaling formats where re-tiling alters block quantization scales) fall outside the uniform-precision reduction-tree theorem and are explicitly documented in **Boundaries**.

## Findings

### 1. CuTe Layout & Swizzle Algebra vs. Triton Pure-$\mathbb{F}_2$ Linear Layouts

`Basis: source + documentation`

#### 1.1 Exact Definition of `cute::Swizzle<B, M, S>` and Hopper WGMMA Atoms

In **`NVIDIA/cutlass`** (`dc6ae46eb5a735a0c2cf96c0b06196caadf8ea31`), hierarchical layouts (formalized mathematically by Cecka, *CuTe Layout Representation and Algebra*, `arXiv:2603.02298`, and categorically via `Tuple`/`Nest` morphisms by Carlisle, Shah, Stern & VanKoughnett, *Categorical Foundations for CuTe Layouts*, `arXiv:2601.05972`) map multi-dimensional coordinates $\vec{x} \in \prod_{i=0}^{r-1} [0, N_i)$ into integer addresses via $L(\vec{x}) = \mathrm{base} + \sum_{i=0}^{r-1} x_i d_i \in (\mathbb{N}, +)$.

To prevent shared-memory bank conflicts, CuTe wraps a linear layout inside `ComposedLayout<Swizzle<B, M, S>, Offset, LayoutB>` (`include/cute/swizzle_layout.hpp:38-61`). Direct inspection of `include/cute/swizzle.hpp:54-96` yields the exact normative bitwise operator:
- Parameters: `BBits` ($B \ge 0$), `MBase` ($M \ge 0$), and `SShift` ($|S| \ge B$, defaulting to $S = B$).
- Disjoint bit masks (`swizzle.hpp:66-69`):
  $$\mathrm{bit\_msk} = 2^B - 1, \qquad \mathrm{yyy\_msk} = \mathrm{bit\_msk} \ll (M + \max(0, S)), \qquad \mathrm{zzz\_msk} = \mathrm{bit\_msk} \ll (M - \min(0, S)).$$
- Application (`swizzle.hpp:76-79`):
  $$\sigma(a) \;=\; a \;\oplus\; \mathrm{shiftr}\big(a \mathbin{\&} \mathrm{yyy\_msk},\; S\big)$$
  where $\mathrm{shiftr}(v, S)$ shifts right by $S$ for $S \ge 0$ and left by $|S|$ for $S < 0$. Because $|S| \ge B$, the source bit window $F_{\text{src}} = \mathrm{yyy\_msk}$ and target bit window $F_{\text{dst}} = \mathrm{zzz\_msk}$ are disjoint; consequently $\sigma$ is an **$\mathbb{F}_2$-linear involution**:
  $$\sigma(a \oplus b) = \sigma(a) \oplus \sigma(b), \qquad \sigma(\sigma(a)) = a \qquad \forall\, a, b \in \mathbb{N}.$$

Direct inspection of Hopper WGMMA shared-memory layout atoms (`include/cute/atom/mma_traits_sm90_gmma.hpp:75-84, 164-167`) confirms the four standard hardware swizzle modes (all operating at byte granularity with $M = 4$ preserving 16-byte / 128-bit vector chunks and positive shift $S = 3 \ge B$):

| Hopper WGMMA Mode | CuTe Swizzle Type | Byte-Granularity Windows ($F_{\text{dst}} \leftarrow F_{\text{src}}$) | Row Atom Width (Bytes) |
| :--- | :--- | :--- | :---: |
| `LayoutType::INTERLEAVE` | `Swizzle<0, 4, 3>` | Identity (no XOR) | 16 B (128 bits) |
| `LayoutType::B32` (`SW32`) | `Swizzle<1, 4, 3>` | Bit `[4]` $\oplus=$ Bit `[7]` | 32 B (256 bits) |
| `LayoutType::B64` (`SW64`) | `Swizzle<2, 4, 3>` | Bits `[4..5]` $\oplus=$ Bits `[7..8]` | 64 B (512 bits) |
| `LayoutType::B128` (`SW128`) | `Swizzle<3, 4, 3>` | Bits `[4..6]` $\oplus=$ Bits `[7..9]` | 128 B (1024 bits) |

#### 1.2 How CuTe (`MixedBits`) and Triton (`LinearLayout`) Confront the $(\mathbb{Z}, +)$ vs. $\mathbb{F}_2$ Split

`Basis: source + derived`

Two production GPU compilers reveal the exact algebraic friction between $(\mathbb{Z}, +)$ and $(\mathbb{F}_2^w, \oplus)$:
1. **CuTe `MixedBits<StaticInt, StaticFlags>` (`include/cute/swizzle.hpp:148-355`) & 5-Mode Projection (`include/cute/swizzle_layout.hpp:92-115, 238-250`):**
   - `MixedBits` tracks disjoint statically known (`StaticInt`) and dynamically varying (`StaticFlags`) bit positions, explicitly commenting at `swizzle.hpp:145`: *"MixedBits can only be manipulated through bitwise operations"* (`&`, `|`, `^`, `shiftl`, `shiftr` — deliberately omitting `operator+` because integer addition leaks carries from dynamic bits into static bits).
   - When slicing or transferring swizzles (`transfer_swizzle` at `swizzle_layout.hpp:93-94`, `slice_and_offset` at `swizzle_layout.hpp:238-243`), CuTe decomposes bit positions into a 5-mode radix layout `make_shape(1<<M, 1<<B, 1<<(abs(S)-B), 1<<B, 1)` separating the untouched base $[0, M)$, destination $Z$, middle gap, source $Y$, and high bits—and decays a swizzled layout to a normal strided layout only when the active subdomain avoids modifying swizzle bits or when `make_swizzle_strides` (`swizzle_layout.hpp:183-224`) can absorb single-bit flips into signed strides $\pm Z$ or $Y \pm Z$.
2. **Triton `LinearLayout` (`triton-lang/triton` `458c1a257c026a24c6aa7937f75f186e9bdf8353`, `include/triton/Tools/LinearLayout.h:19-78`):**
   - Triton (following Adam P. Goucher's construction) models hardware-to-tensor and shared-memory swizzle maps *exclusively* as $\mathbb{F}_2$-linear maps specified on power-of-two basis vectors: $L(t_1 \oplus t_2, w_1 \oplus w_2) = L(t_1, w_1) \oplus L(t_2, w_2)$.
   - **Trade-off:** Pure $\mathbb{F}_2$ linearity makes composition, inversion, and bank-conflict analysis exact linear algebra over $\mathbb{F}_2$ with **zero carry hazards**—at the cost that non-power-of-two dimensions, arbitrary runtime dynamic strides, and general affine pointer arithmetic $a + c$ cannot be represented inside `LinearLayout` without padding/embedding into powers of two.

---

### 2. Carry-Free Semidirect Product Fragment $\mathcal{CF}(B, M, S)$ & Bank-Conflict Freedom

`Basis: derived + execution`

Because binary integer addition satisfies $a + b = (a \oplus b) + 2 \cdot \mathrm{carry}(a, b)$, carries propagating across the boundaries of the swizzle destination window $F_{\text{dst}} = [M, M+B)$ couple $(\mathbb{Z}, +)$ and $(\mathbb{F}_2^w, \oplus)$ non-linearly:

- **Boundary $M$ Carry Counterexample (`Swizzle<3, 4, 3>`, verified via execution):** Take $a = \texttt{0x088}$ ($a \bmod 16 = 8$, bit $7 = 1$) and inner offset $b = 8 < 2^4 = 16$. Since $(a \bmod 16) + b = 16 \ge 2^4$, a carry crosses bit $M = 4$:
  $$\sigma(\texttt{0x088}) = \texttt{0x098}, \qquad \sigma(\texttt{0x088} + 8) = \sigma(\texttt{0x090}) = \texttt{0x080} \;\neq\; \texttt{0x0A0} = \sigma(\texttt{0x088}) + 8$$
  —a **silent 32-byte address jump** when a vector load crosses an unaligned 16-byte boundary!
- **Boundary $M + B$ Carry Counterexample (`Swizzle<3, 4, 3>`, verified via execution):** Take $a = \texttt{0x0E0}$ and $b = \texttt{0x020}$. The bank field $[4..6]$ carries into bit $7 = M + B$:
  $$\sigma(\texttt{0x0E0}) = \texttt{0x0F0}, \qquad \sigma(\texttt{0x0E0} + \texttt{0x020}) = \texttt{0x120} \;\neq\; \texttt{0x110} = \sigma(\texttt{0x0E0}) + \texttt{0x020}.$$

#### 2.1 Exact Carry-Boundary Sub-Tile Translation Theorem

`Basis: derived + execution`

**Theorem 2.1 (IFF Sub-Tile Translation Invariance).** *Fix $\sigma = \mathrm{Swizzle}\langle B, M, S \rangle$ with $S \ge B > 0$, residue $r_0 \in [0, 2^M)$, and inner offset $b \in [0, 2^M)$. Then $\sigma(a + b) = \sigma(a) + b$ holds for **every** base address $a$ in the alignment coset $\{a \in \mathbb{N} \mid a \bmod 2^M = r_0\}$ **if and only if** $r_0 + b < 2^M$ (zero carry across bit $M$).*

*Proof.* ($\Leftarrow$) Write $a = 2^M q + r_0$. Since $r_0 + b < 2^M$, $a + b = (2^M q) \oplus (r_0 + b)$. Because $\sigma$ leaves bits $[0, M)$ invariant and acts only on bits $\ge M$, $\sigma(a + b) = \sigma(2^M q) \oplus (r_0 + b) = \sigma(2^M q) + r_0 + b = (\sigma(2^M q) \oplus r_0) + b = \sigma(a) + b$. ($\Rightarrow$) If $r_0 + b \ge 2^M$, pick $a = 2^{M+S} + r_0$ (bit $M+S$ is $1$, bits $[M, M+B)$ are $0$). Then $\sigma(a) = 2^{M+S} + 2^M + r_0$, so adding $b$ adds a carry into bit $M$ (flipping bit $M$ from $1 \to 0$ and carrying into bit $M+1$), whereas $a + b = 2^{M+S} + 2^M + (r_0 + b - 2^M)$ has $\sigma(a + b) = 2^{M+S} + (r_0 + b - 2^M)$ (bit $M+1$ unchanged), differing by $2^{M+1} \neq 0$. $\square$

*Execution receipt:* Exhaustively verified across every $(r_0, b) \in [0, 4)^2$ and all $q \in [0, 32)$ on `Swizzle<2, 2, 2>`: `holds_for_all_a == (r0 + b < 4)` with `0` discrepancies.

#### 2.2 Exact Characterization of the Carry-Free Semidirect Fragment $\mathcal{CF}(B, M, S)$

`Basis: derived + execution`

**Theorem 2.2 (Carry-Free Semidirect Product Fragment).** *For $S \ge B > 0$, define $\mathcal{CF}(B, M, S) \subset (\mathbb{N} \times [0, 2^M)) \rtimes \mathbb{F}_2^B$ as the class of hierarchical CuTe layouts admitting the **3-Tier Stratified Normal Form**:*
$$L(\vec{x}_{\text{out}}, x_{\text{bank}}, x_{\text{vec}}) \;=\; 2^{M+B} \cdot A_{\text{out}}(\vec{x}_{\text{out}}) \;+\; 2^M \cdot x_{\text{bank}} \;+\; x_{\text{vec}}$$
*where:*
1. *$A_{\text{out}}(\vec{x}_{\text{out}}) \in \mathbb{N}$ is an **arbitrary Presburger affine expression** over $(\mathbb{Z}, +)$ (note: carries inside $A_{\text{out}}$—even across bit $M+S$ or $M+S+B$—are **completely harmless** because $A_{\text{out}}$ is evaluated in $\mathbb{Z}$ before $\sigma$ reads its bit slice!);*
2. *$0 \le x_{\text{bank}} < 2^B$ (strictly confined to $F_{\text{dst}} = [M, M+B)$); and*
3. *$0 \le x_{\text{vec}} < 2^M$ (strictly confined to $[0, M)$).*

*Let $\pi_3(q) \triangleq \lfloor q / 2^{S - B} \rfloor \bmod 2^B \in \mathbb{F}_2^B$. Then for **every** $L \in \mathcal{CF}(B, M, S)$:*
1. **Exact Semidirect Closed Form (Zero Bitvector SAT):**
   $$\sigma\big(L(\vec{x}_{\text{out}}, x_{\text{bank}}, x_{\text{vec}})\big) \;=\; 2^{M+B} \cdot A_{\text{out}}(\vec{x}_{\text{out}}) \;+\; 2^M \cdot \Big(x_{\text{bank}} \oplus \pi_3\big(A_{\text{out}}(\vec{x}_{\text{out}})\big)\Big) \;+\; x_{\text{vec}}.$$
   Because $\pi_3(A_{\text{out}})$ acts on the $\mathbb{F}_2^B$ fiber via XOR without modifying the base tier $A_{\text{out}}$ or vector tier $x_{\text{vec}}$, the address map factors cleanly as a semidirect action.
2. **Decidable Non-Aliasing (Injectivity):** $\sigma \circ L$ is injective **if and only if** $A_{\text{out}}$ is injective (pure Presburger arithmetic—no bitvector solver required!).
3. **Decidable 32-Bank Shared-Memory Bank-Conflict Freedom:** On 32-bank (4-byte word) GPU shared memory where $M = 4$ (each 16-byte chunk spans 4 consecutive banks) and $B \in \{1, 2, 3\}$ (Hopper `SW32`/`SW64`/`SW128` rows of $2^B \times 16$ bytes):
   - **Row loads** (fixed $\vec{x}_{\text{out}}$, varying $x_{\text{bank}} \in [0, 2^B)$) permute $x_{\text{bank}} \mapsto x_{\text{bank}} \oplus \text{const}$, which is always a bijection on $[0, 2^B)$ $\implies$ **always 1-way (0-conflict)**.
   - **Column loads** (fixed $x_{\text{bank}}$, varying row $r \in [0, 2^B)$ stepping $\pi_3(A_{\text{out}})$ by linear stride $s$) visit banks determined by $x_{\text{bank}} \oplus ((s \cdot r) \bmod 2^B)$, which is a bijection over $r \in [0, 2^B)$ **if and only if $\gcd(s, 2^B) = 1$** (i.e., $s$ is odd—an $O(1)$ parity check!).
4. **Negative-Shift Asymmetry ($S \le -B < 0$):** When $S < 0$, $\sigma$ XORs lower bits $[M, M+B)$ *upward* into $[M+|S|, M+|S|+B)$. Carries crossing **any of 4 boundaries** $\{M, M+B, M+|S|, M+|S|+B\}$ corrupt the XOR action, requiring 4-tier window isolation (`x_hi << (M+|S|+B) + x_dst << (M+|S|) + x_src << M + x_vec`). This algebraically explains why hardware TMA/WGMMA swizzles standardize exclusively on $S \ge B > 0$, where arbitrary carries inside $A_{\text{out}}$ are allowed.

**Static Compiler Typing Check ($O(r)$):** Checking membership $L \in \mathcal{CF}(B, M, S)$ for a rank-$r$ CuTe layout requires only $O(r)$ integer inequalities verifying that the mode-range sums within the vector tier stay $< 2^M$, the bank tier stays $< 2^B$ with stride multiple of $2^M$, and outer strides are multiples of $2^{M+B}$ (with base pointer aligned to $2^{M+B}$).

*Execution receipt:* Exhaustively verified on `Swizzle<3, 4, 3>` over all `8,192` coordinates ($A_{\text{out}} \in [0, 64)$, $x_{\text{bank}} \in [0, 8)$, $x_{\text{vec}} \in [0, 16)$), `Swizzle<2, 2, -2>` 4-window isolation + boundary $M+B=4$ carry counterexample (`a=0x0C, b=0x04`), and 32-bank SMEM simulation showing unswizzled 128B column loads suffer **8-way bank conflicts** while `Swizzle<3, 4, 3>` achieves **1-way (conflict-free)** iff $\gcd(s, 8) = 1$ across all strides $s \in [1, 15]$.

---

### 3. IEEE-754 Signed-Zero, NaN, and Reassociation Hazards in Sparse Tensor Compilation

`Basis: normative + source + execution`

#### 3.1 Direct Source Audit of Sparse Compiler Algebraic Assumptions (`Finch.jl` vs. LLVM `FastMathFlags`)

Sparse tensor compilers skip zero-valued runs and spikes by rewriting loops with algebraic identities. Direct source inspection of **`finch-tensor/Finch.jl`** (`7aa1ca1609054b94f3a1b56bb2221ae872513a10`, `src/symbolic/symbolic.jl`) shows `DefaultAlgebra` declares:
- Line 18: `isassociative(::AbstractAlgebra, ::typeof(+)) = true`
- Line 19: `isassociative(::AbstractAlgebra, ::typeof(*)) = true`
- Line 67: `isdistributive(::AbstractAlgebra, ::typeof(*), ::typeof(+)) = true`
- Line 112: `isidentity(::AbstractAlgebra, ::typeof(+), x) = !ismissing(x) && iszero(x)`
- Line 172: `isannihilator(::AbstractAlgebra, ::typeof(*), x) = ismissing(x) || iszero(x)`

In contrast, **`llvm/llvm-project`** (`7d9cd0de00e584d35b3bc077842790fe1bd7771d`, `llvm/include/llvm/IR/FMF.h:31-40`) explicitly forbids all such floating-point rewrites unless opt-in per-instruction `FastMathFlags` bits are set: `AllowReassoc` (`1<<0`), `NoNaNs` (`1<<1`), `NoInfs` (`1<<2`), `NoSignedZeros` (`1<<3`), `AllowReciprocal` (`1<<4`), `AllowContract` (`1<<5`), `ApproxFunc` (`1<<6`).

#### 3.2 Six Execution-Verified IEEE Std 754-2019 Counterexamples

`Basis: normative + execution`

Under **IEEE Std 754-2019** (`10.1109/IEEESTD.2019.8766229`), **every single axiom** relied upon by unconstrained sparse zero-skipping and reduction-tree autotuning fails on concrete bit patterns (all 6 verified in Python 3.13.15, including live hardware `FE_DOWNWARD` rounding via `libm.fesetround(0x400)`):

| # | Algebraic Axiom Assumed | IEEE Std 754-2019 Clause | Concrete Bit-Level Witness | Exact IEEE Result vs. Naive Rewrite | Required LLVM FMF / Guard |
| :-: | :--- | :--- | :--- | :--- | :--- |
| 1 | `0.0 * x == 0.0` (`isannihilator`) | Clause 7.2 (Invalid Operation) | `(+0.0) * (+inf)` | `qNaN` (raises Invalid) vs. skipped `0.0` | `NoInfs` + `NoNaNs` (or finite proof) |
| 2 | `0.0 * x == 0.0` (`isannihilator`) | Clause 6.2 / 7.2 (NaN propagation) | `(+0.0) * NaN` | `qNaN` vs. skipped `0.0` | `NoNaNs` (or finite proof) |
| 3 | `0.0 * x == +0.0` (sign-blind zero) | Clause 6.3 (XOR sign of product) | `(+0.0) * (-1.0)` | `-0.0` (`0x8000000000000000`; `1/y = -inf`) vs. `+0.0` | `NoSignedZeros` |
| 4 | `x + 0.0 == x` (`isidentity`) | Clause 6.3 (Signed-zero addition) | `(-0.0) + (+0.0)` in RN; `(+0.0) + (-0.0)` in `FE_DOWNWARD` | `+0.0 != -0.0` in RN; **`-0.0 != +0.0` in `FE_DOWNWARD`** | `NoSignedZeros` |
| 5 | `(a + b) + c == a + (b + c)` | Clause 4.3 (Rounding) | `a=-2^53, b=2^53, c=1.0` (`binary64`); `big=1e308` | `1.0` vs. `0.0` (100% rel. err); `+inf` vs. `1e308` (overflow) | `AllowReassoc` + error/no-overflow proof |
| 6 | `fma(x,y,z) == fl(x*y) + z` | Clause 5.4.1 (`fusedMultiplyAdd`) | `x=1+2^-27, y=1-2^-27, z=-1.0` (`binary64`) | `-2^-54` (FMA) vs. `0.0` (unfused) | `AllowContract` |

#### 3.3 Four-Regime Numeric Preservation Lattice

`Basis: derived`

To eliminate silent soundness bugs when combining sparse coiteration with GPU schedule optimization, compilers must tag every kernel rewrite with an explicit preservation regime:

| Numeric Regime | Required Input/HW Preconditions | Sound Sparse Zero-Skipping | Sound Reduction-Tree & FMA Schedules |
| :--- | :--- | :--- | :--- |
| **`ExactBits`** | None (full IEEE-754 incl. `NaN`, `±Inf`, `-0.0`) | **None** (except statically proven finite non-negative operands under RN) | Only memory layout/swizzle rewrites (`CF(B,M,S)`) preserving **identical** reduction tree $T$ and FMA boundaries |
| **`FiniteZeroSignFree`** | $\forall i.\; \mathrm{isFinite}(x_i)$ and observer invariant under `+0.0 ~ -0.0` | **All exact-zero skips (`ZeroRun`/`Spike`) are bit-exact** (except sign of zero) | Exact tree $T$ over active non-zero set $S$ (no reassociation) |
| **`EpsReal(ε)`** | Finite inputs + Schedule-Uniform No-Overflow Envelope (Section 4.2) | **All exact-zero skips** (shrinks $|S|$ and lowers $h(T)$!) | **All tiled, SIMD, warp-tree, and FMA schedules with $h(T') \le h_{\max}(\varepsilon)$** ($O(1)$ check!) |
| **`ExactQuire`** | Exact Kulisch / Posit fixed-point super-accumulator | **All exact-zero skips** (bit-exact) | **All permutations and trees** (exact associativity restored) |

---

### 4. Height-Monotone Reduction-Tree Error Bounds & Autotuner Proof Reuse

`Basis: normative + source + derived + execution`

#### 4.1 Exact Hierarchy of Worst-Case Rounding Error Factors ($ku < g(k) < \gamma_k$)

Three closely related error factors appear across numerical analysis and mechanized verification libraries for IEEE-754 `binary32`/`binary64` with unit roundoff $u = 2^{-p}$ ($2^{-24}$ for `binary32`, $2^{-53}$ for `binary64`) and underflow half-ULP $\eta = \frac{1}{2} 2^{e_{\min} - p + 1}$ ($2^{-150}$ for `binary32`, $2^{-1075}$ for `binary64`):

1. **Higham (1993, `10.1137/0914050`; 2002, `10.1137/1.9780898718027`, Lemma 3.1):**
   $$\gamma_k \;\triangleq\; \frac{k u}{1 - k u} \qquad (\text{requires } k u < 1).$$
2. **LAProof (`VeriNum/LAProof` `86a9a74a55bd1ac15f1dab41e430e7498543d016`, `accuracy_proofs/common.v:211-215, 436, 494-495`):**
   $$g(k) \;\triangleq\; (1 + u)^k - 1, \qquad g_1(n_1, n_2) \;\triangleq\; n_1 \cdot \eta \cdot (1 + g(n_2)).$$
   LAProof uses $g(k)$ rather than $\gamma_k$ because $g(k)$ requires **no side-condition $ku < 1$**, satisfies exact multiplicative induction $(1 + u) g(k) + u = g(k + 1)$ (`common.v:484-489`, `one_plus_d_mul_g`), and strictly tightens Higham's factor: $g(k) < \gamma_k$ for all $k \ge 2$ with $ku < 1$.
3. **Jeannerod & Rump (2013, `10.1137/120894488`):**
   Proves that for inner products and summation under round-to-nearest (without underflow), the worst-case relative factor improves to strictly $k u$ (eliminating the $1/(1-ku)$ denominator completely):
   $$k u \;<\; g(k) \;<\; \gamma_k \qquad \forall\, k \ge 2,\; k u < 1.$$

Direct inspection of `VeriNum/LAProof` confirms what is already mechanized in Coq vs. where reduction-tree generalization extends it:
- `accuracy_proofs/sum_acc.v:61-146` (`bSUM`), `197-272` (`fSUM`), `332-350` (`sum_forward_error_permute`): proves backward error $g(n-1)$ and forward error $g(n) \sum |x_i|$ for **sequential** `sumF` (`foldl`) and its permutations.
- `accuracy_proofs/dot_acc.v:91-140` (`dotprod_mixed_error`), `167-187` (`dotprod_forward_error`), `196-217` (`sparse_dotprod_forward_error`): proves forward error $g(n)(|v_1|\cdot|v_2|) + g_1(n, n-1)$ and **sparse refinement** replacing vector length $n$ with exact non-zero count `nnzR` (`common.v:164-165`), still over sequential `dotprodF` (`fold_right`).

#### 4.2 Schedule-Parametric Tree-Height Transfer Theorem

`Basis: derived + execution`

Every GPU reduction schedule for a dense or sparse dot product $\sum_{i=1}^n a_i b_i$ over active non-zero index set $S \subseteq \{1,\dots,n\}$ induces a binary addition tree $T$ with leaf addition depths $d_T(i)$ and maximum height $h(T) = \max_{i \in S} d_T(i)$:
- Sequential left-fold: $h(T_{\text{seq}}) = |S| - 1$;
- Balanced warp/block tree reduction: $h(T_{\text{bal}}) = \lceil \log_2 |S| \rceil$;
- Tiled GPU GEMM (inner sequential tile size $K_t$, outer binary tree across $K/K_t$ split-K/block tiles): $h(T_{\text{tile}}) = (K_t - 1) + \lceil \log_2(K / K_t) \rceil$.

**Theorem 4.1 (Height-Monotone Reduction-Tree Error Transfer & $O(1)$ Autotuner Proof Reuse).** *Let $\vec{a}, \vec{b} \in \mathbb{F}^n$ be finite inputs in an IEEE-754 binary format with unit roundoff $u$, underflow half-ULP $\eta$, and maximum finite magnitude $\Omega_{\max}$. Suppose sparse coiteration skips only exact-zero finite terms ($j \notin S \implies a_j = 0 \lor b_j = 0$) and the **Schedule-Uniform No-Overflow Envelope** holds:*
$$\big(1 + g(h(T) + 1)\big) \sum_{i \in S} |a_i b_i| \;+\; g_1(|S|,\, h(T)) \;<\; \Omega_{\max}.$$
*Then for **every** binary reduction tree $T$ over $S$:*
1. **Zero Intermediate Overflow & Leaf-Only Underflow:** Every internal node evaluates to a finite float. Because exact IEEE-754 floating-point addition never incurs underflow rounding error (Sterbenz/Hauser exactness on subnormals: if $|x + y|$ is subnormal, $x + y$ is exactly representable with zero rounding error), the additive underflow term $\eta$ enters **only** at the $|S|$ leaf multiplications $a_i \otimes b_i$.
2. **Per-Leaf Tight Bound & Height-Monotone Envelope:**
   $$\Big|\widehat{y}_T - \sum_{i=1}^n a_i b_i\Big| \;\le\; \underbrace{\sum_{i \in S} g\big(d_T(i)+1\big)\,|a_i b_i| + g_1\big(|S|,\, h(T)\big)}_{B_{\text{tight}}(T)} \;\le\; \underbrace{g\big(h(T)+1\big)\sum_{i \in S}|a_i b_i| + g_1\big(|S|,\, h(T)\big)}_{B_{\text{height}}(h(T), |S|)} \;\le\; \gamma_{h(T)+1}\sum_{i \in S}|a_i b_i| + (1 + \gamma_{h(T)})|S|\eta.$$
3. **Mixed-Precision Tensor Core Asymmetry (`binary16 -> binary32` vs. `bfloat16 -> binary32`):**
   - For **`binary16` inputs ($p=11$, $e \in [-24, 15]$) accumulated in `binary32` ($p=24$, $e \in [-126, 127]$):** Every product of two finite `binary16` numbers requires at most $22 \le 24$ significand bits and has exponent $\ge -48 > -126$, so **every leaf multiplication is 100% exact with zero rounding and zero underflow!** The bound collapses cleanly to $g(h(T)) \sum_{i \in S} |a_i b_i|$ (dropping both $+1$ in the depth exponent and the entire $g_1$ underflow term).
   - For **`bfloat16` inputs ($p=8$, $e \in [-126, 127]$) accumulated in `binary32`:** Product significands ($16 \le 24$ bits) never round in the normal range, **but** because `bfloat16` shares `binary32`'s 8-bit exponent range, leaf products **can still underflow or overflow** (`2^-80 * 2^-80 -> 0.0`, `2^80 * 2^80 -> +inf`, verified via execution)—so the $g_1$ underflow residual and no-overflow envelope **cannot** be dropped for `bfloat16`!
4. **Nonlinear `FPTaylor` Symbolic Transfer:** In `soarlab/FPTaylor` (`b5a77cae348400f21f83512210d9f43c4bffb381`, `taylor_form.ml:27-30, 297-324`), a floating-point program's error is decomposed into a first-order symbolic Taylor form `{ v0 : expr; v1 : (expr * error_info) list }` plus a rigorously interval-bounded second-order remainder `m2`. For any twice-differentiable outer kernel $f(\dots, s, \dots)$ consuming a linear reduction $s = \sum a_i b_i$ (e.g., softmax denominator, layer-norm variance, activation function), replacing $s$ with an input interval uncertainty bounded by $B_{\text{height}}(h(T), |S|)$ yields a monotone error bound:
   $$\Delta_f(T) \;=\; \Big|\frac{\partial f}{\partial s}\Big|_{\text{ival}} \cdot B_{\text{height}}\big(h(T), |S|\big) \;+\; \Delta_{\text{outer}} \;+\; R_2\big(B_{\text{height}}(h(T), |S|)\big).$$
5. **$O(1)$ Autotuner Proof Reuse Corollary:** Once a baseline schedule (e.g., sequential $h_0 = n - 1$, or a target budget height $h_{\max}(\varepsilon)$) is certified in LAProof/FPTaylor, **every** dense or sparse GPU schedule $T'$ generated by an autotuner that satisfies $h(T') \le h_{\max}$ and $|S'| \le n$ (same accumulator format, finite inputs within the no-overflow envelope) **automatically inherits the machine-checked accuracy certificate via a single $O(1)$ integer comparison—completely decoupling schedule search from solver/proof re-execution.**

#### 4.3 Empirical Verification Across 516 Reduction Schedules (`Basis: execution`)

Evaluating `516` distinct binary reduction trees (`seq`, `bal`, `tile4`, `tile8`, and `125` random irregular trees per dataset) in exact IEEE-754 `binary32` against arbitrary-precision `fractions.Fraction` ground truth on Python 3.13.15 established:

| Dataset | Active `nnz` | $h_{\text{seq}} \to h_{\text{bal}}$ | Violations / Trees | Tightening Ratio $B_{\text{height}}(h_{\text{seq}}) / B_{\text{height}}(h_{\text{bal}})$ | Dominant Error Term |
| :--- | :---: | :---: | :---: | :---: | :--- |
| `Sparse_MixedSign_64` | `34` | `33 -> 6` | `0 / 129` | **`4.86x`** | Relative rounding $g(h+1)\sum|a_i b_i|$ |
| `Adversarial_Cancel_32` | `32` | `31 -> 5` | `0 / 129` | **`5.33x`** | Relative rounding $g(h+1)\sum|a_i b_i|$ |
| `ULP_Boundary_48` | `48` | `47 -> 6` | `0 / 129` | **`6.86x`** | Relative rounding $g(h+1)\sum|a_i b_i|$ |
| `Subnormal_Underflow_32` | `32` | `31 -> 5` | `0 / 129` | **`1.00x`** | Leaf underflow $g_1(32, h) \approx 32 \cdot 2^{-150}$ |

Across all `516` trees, `max(actual_err / B_tight_g) = 0.1159 <= 1.0` (`0` violations). Notably, `Subnormal_Underflow_32` empirically exposes an essential design boundary: when every product lies in the subnormal regime ($a_i b_i \approx 2^{-148}$), the additive underflow residual $|S|\eta$ exceeds the relative rounding term by $> 17$ orders of magnitude, so reducing tree height does not tighten the worst-case bound unless accumulation precision or exponent scaling is increased.

---

### 5. Mechanized Floating-Point Verification Tool Matrix

`Basis: normative + source + documentation`

| Tool / Library | Formal Engine & Proof Certificate | Core Error Model | Handles Subnormal Underflow? | Scales to Parameterized $n$ / Sparse / Arbitrary Trees? | Primary Sweet Spot in GPU Verification Pipeline |
| :--- | :--- | :--- | :---: | :--- | :--- |
| **LAProof** (`VeriNum/LAProof`, ARITH 2023) | Coq + Flocq + MathComp + VST (machine-checked Coq proof linked to C CSR SpMV) | Backward, mixed, & forward bounds via $g(k) = (1+u)^k - 1$ and $g_1(n_1, n_2)$ | **Yes** (explicit `default_abs` $\eta$ in `g1`) | **Yes** for arbitrary $n$ and sparse `nnzR` (`dot_acc.v`); sequential `sumF`/`dotprodF` in pinned rev (extends cleanly to height $h(T)$) | Parametric matrix/vector/SpMM kernel accuracy + end-to-end C/IR refinement |
| **VCFloat** (`VeriNum/vcfloat`) | Coq + Flocq (automated Coq reflection tactic) | Automated forward roundoff VCs for straight-line & loop-body FP expressions | **Yes** (`default_abs`) | Fixed expression ASTs (feeds modular lemmas into LAProof) | Discharging inner scalar/tile arithmetic VCs inside Coq |
| **FPTaylor** (`soarlab/FPTaylor`, TOPLAS 2018) | OCaml + Global Branch-and-Bound Opt + HOL Light / Coq certificate export | Symbolic 1st-order Taylor form (`v0`, `v1`) + rigorously bounded 2nd-order remainder (`m2`) | **Yes** (`delta_exp` in `rounding.ml`) | Fixed expression size (best for small/medium nonlinear formulas; couples via Section 4.2 symbolic transfer!) | Tight bounds on nonlinear outer ops (`exp`, `rsqrt`, `softmax`, transcendental activations) consuming tree-bounded reductions |
| **Gappa** (ACM TOMS 2010) | C++ interval arithmetic + rewriting rules + Coq/Flocq proof script export | Range & relative/absolute rounding error enclosures via forward/backward rewriting | **Yes** (IEEE-754 / fixed-point models) | Small/medium straight-line expressions & elementary function polynomials | Bit-accurate low-level library kernels, range reductions, polynomial approximations, FMA rounding certificates |

## Boundaries

- **Non-IEEE Tensor Core internal accumulators (`known not to apply`):** NVIDIA Hopper/Blackwell WGMMA/UMMA instructions with `fp16`/`bf16` or `fp8` inputs do not necessarily execute full 24-bit IEEE-754 `binary32` rounding at every internal tree node (e.g., Hopper `fp8` WGMMA famously uses reduced-precision internal accumulation ~13–14 mantissa bits before `fp32` promotion). Applying Theorem 4.1 with $u = 2^{-24}$ to hardware executing reduced-width internal accumulation is **unsound**; the unit roundoff $u$ must match the hardware's *actual* internal accumulator precision.
- **Flush-to-Zero (FTZ) / Denormals-Are-Zero (DAZ) modes (`known not to apply`):** Under GPU FTZ/DAZ execution (e.g., PTX `.ftz` modifiers), Sterbenz/Hauser exactness for subnormal addition fails because a subnormal sum is flushed to zero, introducing an additive error up to $2^{e_{\min}}$ at **every** addition node (not just leaf multiplications). Theorem 4.1's leaf-only underflow bound requires standard IEEE-754 gradual underflow.
- **Block-scaled microscaling formats (`OCP MXFP4` / `MXFP8`) (`not examined`):** When every 32-element block shares a dynamic `UE8M0` scale exponent, changing tile boundaries or reduction groupings alters quantization scales *before* accumulation—breaking pure reduction-tree height invariance. Scale-aware error transfer was not modeled in this report.
- **Dynamic / runtime-sized sparse block offsets in $\mathcal{CF}(B, M, S)$ (`unknown`):** Theorem 2.2 checks membership in $\mathcal{CF}(B, M, S)$ statically in $O(r)$ when tile bounds and strides are statically known. For dynamic runtime-sized tensors or compressed sparse row/block pointers (`row_ptr[i]`), lifting offsets into $\mathcal{CF}(B, M, S)$ requires runtime alignment contracts (`2^{M+B} | base`) and boundary predicates whose minimal codegen overhead was not empirically benchmarked on GPU hardware.
- **Probabilistic rounding error bounds (`not examined`):** Higham & Mary (2019/2020) derive tighter $O(\sqrt{h}\,u)$ probabilistic bounds under independent zero-mean rounding assumptions. This report covers strictly **deterministic worst-case** bounds suitable for formal verification certificates; probabilistic bounds do not yield zero-failure guarantees against adversarial cancellation inputs.
- **Live GPU hardware profiling and PTX SASS disassembly (`not examined`):** Bank-conflict counts (`8-way` vs. `1-way`) and `binary32` reduction errors were verified via exact bit-level architectural simulation in Python 3.13.15 against pinned CUTLASS headers rather than hardware performance counters (`Nsight Compute`) on physical Hopper/Blackwell silicon.

## Evidence

### Primary Literature & Normative Specifications (Verified 2026-11-19)

- **CuTe Layout Algebra:** C. Cecka, *"CuTe Layout Representation and Algebra"*, `arXiv:2603.02298` (2026); J. Carlisle, J. Shah, R. Stern, P. VanKoughnett, *"Categorical Foundations for CuTe Layouts"*, `arXiv:2601.05972`, DOI `10.48550/arXiv.2601.05972` (2026).
- **Finch & Looplets:** W. Ahrens, T. Fields Collin, R. Patel, K. Deeds, C. Hong, S. Amarasinghe, *"Finch: Sparse and Structured Tensor Programming with Control Flow"*, PACMPL Vol. 9 (OOPSLA1 2025), DOI `10.1145/3720473`, `arXiv:2404.16730`; W. Ahrens et al., *"Looplets: A Language for Structured Coiteration"*, CGO 2023, DOI `10.1145/3579990.3580020`.
- **IEEE-754 Normative Standard:** *IEEE Standard for Floating-Point Arithmetic*, IEEE Std 754-2019, DOI `10.1109/IEEESTD.2019.8766229` (Clause 5.4.1 FMA, Clause 6.3 Sign bit & signed-zero addition, Clause 7.2 Invalid operation $0 \times \infty$).
- **Rounding Error Analysis:** N. J. Higham, *Accuracy and Stability of Numerical Algorithms* (2nd ed., SIAM, 2002), DOI `10.1137/1.9780898718027`; N. J. Higham, *"The Accuracy of Floating Point Summation"*, SIAM J. Sci. Comput. 14(4):783–799 (1993), DOI `10.1137/0914050`; C.-P. Jeannerod & S. M. Rump, *"Improved Error Bounds for Inner Products in Floating-Point Arithmetic"*, SIAM J. Matrix Anal. Appl. 34(2):338–344 (2013), DOI `10.1137/120894488`.
- **Mechanized FP Tools:** A. E. Kellison, A. W. Appel, M. Tekriwal, D. Bindel, *"LAProof: A Library of Formal Proofs of Accuracy and Correctness for Linear Algebra Programs"*, ARITH 2023, DOI `10.1109/ARITH58626.2023.00021`; A. Solovyev et al., *"Rigorous Estimation of Floating-Point Round-Off Errors with Symbolic Taylor Expansions"* (FPTaylor), ACM TOPLAS (2018), DOI `10.1145/3230733`; M. Daumas & G. Melquiond, *"Certification of Bounds on Expressions Involving Rounded Operators"* (Gappa), ACM TOMS 37(1) (2010), DOI `10.1145/1644001.1644003`.

### Pinned Upstream Source Code Inspections (Observed 2026-11-19)

| Repository | Pinned 40-Hex Commit SHA | Inspected File & Lines | Verified Fact |
| :--- | :--- | :--- | :--- |
| `NVIDIA/cutlass` | `dc6ae46eb5a735a0c2cf96c0b06196caadf8ea31` | `include/cute/swizzle.hpp:54-131,148-355`, `include/cute/swizzle_layout.hpp:92-115,183-250`, `include/cute/atom/mma_traits_sm90_gmma.hpp:75-84,164-167` | Exact `Swizzle<B,M,S>` masks/apply, bitwise-only `MixedBits`, 5-mode Z/Y projection, Hopper WGMMA `Swizzle<{0,1,2,3},4,3>` atoms. |
| `triton-lang/triton` | `458c1a257c026a24c6aa7937f75f186e9bdf8353` | `include/triton/Tools/LinearLayout.h:19-78` | Pure $\mathbb{F}_2$-linear basis layout model $L(t_1 \oplus t_2, w_1 \oplus w_2) = L(t_1, w_1) \oplus L(t_2, w_2)$. |
| `finch-tensor/Finch.jl` | `7aa1ca1609054b94f3a1b56bb2221ae872513a10` | `src/symbolic/symbolic.jl:18-19,67,112,172` | `DefaultAlgebra` declares `+`/`*` associative, `*` distributive over `+`, `iszero(x)` additive identity and multiplicative annihilator. |
| `llvm/llvm-project` | `7d9cd0de00e584d35b3bc077842790fe1bd7771d` | `llvm/include/llvm/IR/FMF.h:23-40` | Exact `FastMathFlags` bitmask (`AllowReassoc`, `NoNaNs`, `NoInfs`, `NoSignedZeros`, `AllowReciprocal`, `AllowContract`, `ApproxFunc`). |
| `VeriNum/LAProof` | `86a9a74a55bd1ac15f1dab41e430e7498543d016` | `accuracy_proofs/common.v:161-165,211-215,436,484-495`, `accuracy_proofs/sum_acc.v:61-146,197-350`, `accuracy_proofs/dot_acc.v:91-218` | Exact `default_rel`, `default_abs`, `g(n)=(1+D)^n-1`, `g1(n1,n2)=n1*E*(1+g(n2))`, `bSUM`, `fSUM`, `dotprod_forward_error`, and sparse `sparse_dotprod_forward_error` (`nnzR`). |
| `soarlab/FPTaylor` | `b5a77cae348400f21f83512210d9f43c4bffb381` | `rounding.ml:13-75`, `taylor_form.ml:20-35,297-340` | Exact `eps_delta_from_bits` (float16/32/64/128), `taylor_form = { v0; v1 }`, and `rounded_form` remainder bounding (`m2`). |

### Executable Verification Probe & Observed Output (`Basis: execution`, 2026-11-19)

**Environment:** `Python 3.13.15` on Linux x86_64 (standard library `struct`, `math`, `fractions`, `ctypes` calling glibc `libm.fesetround`).

**Observed Output (`exit 0`):**
```text
[PASS] Part 1 (CuTe Swizzle Algebra): 8,192 CF(3,4,3) coords exact; Swizzle<2,2,2> carry IFF exact; S=-2 4-window verified; 32-bank SMEM unswizzled=8-way vs swizzled=1-way IFF gcd(s,2^B)==1 (s=1..15)
[PASS] Part 2 (IEEE-754 Hazards): 6/6 counterexamples verified (0*inf=NaN, 0*NaN=NaN, +0*-1=-0 [0x8000...], -0++0=+0, FE_DOWNWARD_checked=True, reassoc 1.0 vs 0.0 & inf vs 1e308, FMA 0.0 vs -2^-54)
[PASS] Part 3 (Height-Monotone FP Bounds): 516 trees across 4 datasets, 0 bound violations, max(err/B_tight_g)=0.1159, seq/bal tightening={'Sparse_MixedSign_64': (34, 4.86), 'Adversarial_Cancel_32': (32, 5.33), 'Subnormal_Underflow_32': (32, 1.0), 'ULP_Boundary_48': (48, 6.86)}, fp16->fp32 exact products=6400/6400, bf16->fp32 underflow/overflow contrast verified, jr < g(k) < gamma_k verified
```

**Self-Contained Minimal Reproducer (runnable directly via `python3 /tmp/verify_swizzle_fp.py`):**
```python
#!/usr/bin/env python3
import math, struct
from fractions import Fraction

def cute_swizzle(B, M, S, a):
    m = ((1 << B) - 1) << (M + max(0, S))
    return a ^ ((a & m) >> S if S >= 0 else (a & m) << (-S))

# 1. Carry spillover on Hopper Swizzle<3,4,3> & CF(3,4,3) closed form over 8,192 coords
assert cute_swizzle(3, 4, 3, 0x088 + 8) == 0x080 != cute_swizzle(3, 4, 3, 0x088) + 8
assert cute_swizzle(3, 4, 3, 0x0E0 + 0x20) == 0x120 != cute_swizzle(3, 4, 3, 0x0E0) + 0x20
for ao in range(64):
    pi3 = ao & 7
    for xb in range(8):
        for xv in range(16):
            assert cute_swizzle(3, 4, 3, (ao << 7) + (xb << 4) + xv) == (ao << 7) + ((xb ^ pi3) << 4) + xv
# 2. 32-bank SMEM conflict-free IFF gcd(s, 8) == 1
for s in range(1, 16):
    banks = {(cute_swizzle(3, 4, 3, ((s * r) % 8) * 128) // 4) % 32 for r in range(8)}
    assert (len(banks) == 8) == (math.gcd(s, 8) == 1)
# 3. IEEE-754 sparse/reassoc/FMA & bf16 vs fp16 contrast
assert math.isnan(0.0 * float("inf")) and struct.unpack(">Q", struct.pack(">d", (+0.0) * (-1.0)))[0] == 0x8000000000000000
assert (-(2.0**53) + 2.0**53) + 1.0 == 1.0 and -(2.0**53) + (2.0**53 + 1.0) == 0.0
assert (1.0 + 2.0**-27) * (1.0 - 2.0**-27) + (-1.0) == 0.0 and math.fma(1.0 + 2.0**-27, 1.0 - 2.0**-27, -1.0) == -(2.0**-54)
f32 = lambda x: struct.unpack(">f", struct.pack(">f", x))[0]
assert f32(f32(2.0**-80) * f32(2.0**-80)) == 0.0  # bfloat16 product underflows binary32!
print("PASS: CuTe CF(3,4,3), 32-bank SMEM IFF, and IEEE-754 hazards verified.")
```

## Revalidation

To verify whether upstream library changes or new GPU architectures alter these findings, run these targeted discriminating checks:

1. **Diff CuTe `Swizzle` and Hopper/Blackwell SMEM atoms against `dc6ae46eb5a735a0c2cf96c0b06196caadf8ea31`:**
   ```bash
   git ls-remote https://github.com/NVIDIA/cutlass.git HEAD
   # Diff include/cute/swizzle.hpp, include/cute/swizzle_layout.hpp, and include/cute/atom/mma_traits_sm90_gmma.hpp
   # (plus any sm100/Blackwell UMMA swizzle headers) to check for non-XOR swizzles or negative-shift hardware atoms.
   ```
2. **Check whether `Finch.jl` introduces IEEE-754-safe float algebras by default:**
   ```bash
   git ls-remote https://github.com/finch-tensor/Finch.jl.git HEAD
   # Inspect src/symbolic/symbolic.jl around isannihilator, isidentity, and isassociative relative to 7aa1ca1609054b94f3a1b56bb2221ae872513a10
   # for float-specialized overrides or NaN/signed-zero guards.
   ```
3. **Check whether `VeriNum/LAProof` adds tree-structured pairwise/blocked summation theorems natively:**
   ```bash
   git ls-remote https://github.com/VeriNum/LAProof.git HEAD
   # Inspect accuracy_proofs/sum_acc.v and accuracy_proofs/dot_acc.v relative to 86a9a74a55bd1ac15f1dab41e430e7498543d016
   # for non-sequential tree summation definitions beyond foldl/fold_right.
   ```
4. **Re-run the bit-exact swizzle and FP error probe on new hardware formats:** Execute the minimal reproducer in **Evidence** (or extend `f32_round` / `U32` / `ETA32` to `fp8` E4M3/E5M2 or internal tensor-core mantissa widths). Passing checks verify only the modeled bitwidth and gradual-underflow assumption; hardware with FTZ or reduced internal accumulator mantissas must substitute the true hardware rounding model before transferring error bounds.
