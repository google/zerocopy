# Fixed-Point SIMD Saturating Narrowing, Wrapping Integral Images, and Dyadic Lyapunov Stability for IIR Filters

## Summary

Bit-accurate verification of real-time audio, image, and control pipelines rests on three coupled fixed-point obligations where floating-point or naive modular abstractions are unsound:

1. **Two-sided saturating SIMD multiply-add and fractional narrowing (`PairSafe`):**
   - `x86` SSSE3/AVX2/AVX-512 `PMADDUBSW` (`_mm_maddubs_epi16`, `llvm.x86.ssse3.pmadd.ub.sw.128`) multiplies unsigned `u8` lanes $u_{2k}, u_{2k+1} \in [0, 255]$ by signed `i8` weights $s_{2k}, s_{2k+1} \in [-128, 127]$ and saturates $u_{2k} s_{2k} + u_{2k+1} s_{2k+1} \in [-65280, +64770]$ to signed `i16` $[-32768, 32767]$. Across all $65,536$ weight pairs, `16,257` (`24.81%`) can saturate on full-range `u8` inputs; exact linearity holds for all $u_0, u_1 \in [0, 255]$ **iff** $\min(s_0, 0) + \min(s_1, 0) \ge -128$ and $\max(s_0, 0) + \max(s_1, 0) \le 128$, while bounding activations to $u_j \in [0, 128]$ makes all $65,536$ weight pairs overflow-free.
   - Arm NEON `SQDMULH` / `SQRDMULH` (`vqdmulhq_s16`, `vqrdmulhq_s16`) saturates solely at $(a, b) = (-2^{W-1}, -2^{W-1})$.
   - RISC-V Vector v1.0 `vnclip` rounds $v$ according to `vxrm` (`rnu`, `rne`, `rdn`, `rod`) **before** clipping to $[-2^{W-1}, 2^{W-1}-1]$ and setting `vxsat`, so $\lfloor v / 2^d \rfloor = 2^{W-1} - 1$ still overflows into $2^{W-1}$ under `rnu`/`rne` when $r = 1$, requiring $v \le 2^d(2^{W-1} - 1) + 2^{d-1} - 1$.
2. **Exact `Wrapping<u32>` sliding-window integral-image bounds:**
   - Accumulating 2D prefix sums modulo $2^{32}$ in `core::num::Wrapping<u32>` allows arbitrarily many full-frame $2^{32}$ wraparounds while the four-corner query $(S(y_1, x_1) \ominus_{32} S(y_0, x_1) \ominus_{32} S(y_1, x_0) \oplus_{32} S(y_0, x_0))$ recovers the **exact** integer window sum whenever $I(\eta, \xi) \ge 0$ and window area $A = (y_1 - y_0)(x_1 - x_0)$ satisfies $A \cdot P_{\max} < 2^{32}$. Under per-pixel quantization error $|\hat{I} - I^*| \le \epsilon$, window error is bounded by $A \cdot \epsilon$ independent of frame size $(H, W)$, avoiding IEEE-754 `f32` catastrophic cancellation.
3. **Division-free `DyadicFloat` ($m \cdot 2^e$) Jury-Stein-Lyapunov stability and contraction certificates:**
   - Because `DyadicFloat` ($\mathbb{D} = \{m \cdot 2^e : m, e \in \mathbb{Z}\}$) is a ring not closed under general division, rational Stein-Lyapunov inversion $P = (I - A_c^T (\cdot) A_c)^{-1}(I_2)$ leaves $\mathbb{D}$ when odd prime factors divide its determinant. For $D(z) = z^2 + a_1 z + a_2$ ($a_1, a_2 \in \mathbb{D}$), the Stein determinant factors **identically** into the three linear Jury margins $\Delta(a_1, a_2) = (1 - a_2)(1 + a_2 - a_1)(1 + a_2 + a_1)$, and canceling a shared $(1 + a_2)$ factor yields the **polynomial, division-free certificate**:
     $$\tilde{P}(a_1, a_2) = \begin{pmatrix} 2(1 + a_2) & 2 a_1 a_2 \\ 2 a_1 a_2 & \Delta(a_1, a_2) + 2(1 + a_2) a_2^2 \end{pmatrix} \in \mathbb{D}^{2 \times 2}$$
     satisfying $\tilde{P} - A_c^T \tilde{P} A_c = \Delta(a_1, a_2) I_2$ in $\mathbb{Z}[a_1, a_2]$ with zero floating-point rounding axioms, certifying Schur stability, quadratic contraction, and invariant roundoff ellipsoids while distinguishing wrapping limit cycles in 1-guard-bit accumulators from saturation-safe coupled realizations.

## Applicability

This report covers deductive and bit-accurate verification across six pinned upstream subjects:

1. **Rust standard architecture SIMD intrinsics (`core_arch`)** (`rust-lang/stdarch` at `ca26a96d57b295dcd927622877242940a0f3c02e`): `crates/core_arch/src/x86/ssse3.rs` (`_mm_maddubs_epi16`, `_mm_mulhrs_epi16`), `avx2.rs` (`_mm256_maddubs_epi16`), and `arm_shared/neon/generated.rs` (`vqdmulhq_s16`, `vqdmulh_s32`, `vqrdmulhq_s16`).
2. **Rust core modular wrapper (`core::num::Wrapping`)** (`rust-lang/rust` at `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, `library/core/src/num/wrapping.rs`).
3. **RISC-V Vector Extension Specification v1.0** (`riscv/riscv-v-spec` at `2f68ef7256d6ec53e4d2bd7cb12862f406d64e34`, `v-spec.adoc`): `vxrm`, `vxsat`, `vsmul.vv`, and `vnclip`/`vnclipu`.
4. **ARM CMSIS-DSP fixed-point biquad filters** (`ARM-software/CMSIS-DSP` at `9f64ba31591e527c505951943b4b95b0eb2f834b`): `Source/FilteringFunctions/arm_biquad_cascade_df1_q15.c`, `arm_biquad_cascade_df1_fast_q15.c`, and `arm_biquad_cascade_df1_q31.c`.
5. **gemmlowp fixed-point primitives** (`google/gemmlowp` at `16e8662c34917be0065110bfcd9cc27d30f52fdf`, `fixedpoint/fixedpoint.h`).
6. **LLVM target SIMD intrinsics** (`llvm/llvm-project` at `c11543baec3048ab67ebb61f2186172f90983d57`).

All algebraic characterizations apply across proof assistants (Lean 4, Rocq, Isabelle/HOL) and SMT bit-vector/integer theories. Match feedback coefficient signs to the target implementation: textbook transfer denominators $D(z) = 1 + a_1 z^{-1} + a_2 z^{-2}$ compute $y[n] = \sum b_k x[n-k] - a_1 y[n-1] - a_2 y[n-2]$, whereas `CMSIS-DSP` (`arm_biquad_cascade_df1_q15.c:554`) stores negated feedback coefficients $a_1^{\text{cmsis}} = -a_1, a_2^{\text{cmsis}} = -a_2$ so `acc += a1_cmsis*y[n-1] + a2_cmsis*y[n-2]`.

## Findings

### 1. Cross-ISA Fixed-Point Saturating Multiply-Add and Narrowing (`PairSafe`)

`Basis: normative + source + derived + execution`

Quantized media and DSP kernels fuse narrow multiplications with pairwise addition or right-shift scaling and two-sided signed saturation $\operatorname{sat}_W(z) = \max(-2^{W-1}, \min(2^{W-1} - 1, z))$. Modeling these operations as exact widening integer arithmetic is sound **only** under explicit `PairSafe` preconditions.

#### 1.1 `x86` SSSE3/AVX2/AVX-512 `PMADDUBSW` (`_mm_maddubs_epi16` / `_mm256_maddubs_epi16`)

In `rust-lang/stdarch` (`crates/core_arch/src/x86/ssse3.rs:288–290, 352–353`; `avx2.rs:1856–1859`), `_mm_maddubs_epi16(a, b)` lowers to `llvm.x86.ssse3.pmadd.ub.sw.128(a.as_u8x16(), b.as_i8x16()) -> i16x8`, computing per lane:
$$y_k = \operatorname{sat}_{16}\!\big(u_{2k} \cdot s_{2k} + u_{2k+1} \cdot s_{2k+1}\big), \qquad u_j \in [0, 255],\; s_j \in [-128, 127]$$
Each single product $u_j s_j \in [-32640, +32385]$ fits in `i16`, **but the adjacent pair sum spans $[-65280, +64770]$**, saturating `i16` on both ends and breaking associativity when fed into `PMADDWD` (`_mm_madd_epi16`).

**`PairSafe` characterization (`PMADDUBSW`):** Over $[0, U_{\max}]^2$ ($U_{\max} \in [0, 255]$), the bilinear form $p(u_0, u_1) = u_0 s_0 + u_1 s_1$ attains its extrema at box corners $u_j \in \{0, U_{\max}\}$:
$$p_{\min}(s_0, s_1; U_{\max}) = U_{\max}\big(\min(s_0, 0) + \min(s_1, 0)\big), \qquad p_{\max}(s_0, s_1; U_{\max}) = U_{\max}\big(\max(s_0, 0) + \max(s_1, 0)\big)$$
Hence $\operatorname{sat}_{16}(u_0 s_0 + u_1 s_1) = u_0 s_0 + u_1 s_1$ holds for **all** $(u_0, u_1) \in [0, U_{\max}]^2$ iff $p_{\min} \ge -32768$ and $p_{\max} \le 32767$:
- **Full-range `u8` ($U_{\max} = 255$):** Since $\lceil -32768 / 255 \rceil = -128$ ($255 \times (-129) = -32895$) and $\lfloor 32767 / 255 \rfloor = 128$ ($255 \times 129 = +32895$),
  $$\operatorname{PairSafe}(s_0, s_1; 255) \iff \min(s_0, 0) + \min(s_1, 0) \ge -128 \;\land\; \max(s_0, 0) + \max(s_1, 0) \le 128$$
  Opposite-sign weight pairs ($s_0 s_1 \le 0$) are unconditionally safe; same-sign pairs require $|s_0 + s_1| \le 128$ (for which $|s_0| + |s_1| \le 128$ suffices). Across all `65,536` pairs in $[-128, 127]^2$, exactly `49,279` (`75.19%`) satisfy $\operatorname{PairSafe}(\cdot; 255)$, `8,001` (`12.21%`) saturate at `+32767`, and `8,256` (`12.60%`) saturate at `-32768`.
- **Bounded `u8` ($U_{\max} \le 128$, including 7-bit $[0, 127]$):** Since $128 \times (-256) = -32768$ and $128 \times 254 = +32512 \le 32767$, **100% (`65,536 / 65,536`)** of `i8` weight pairs are saturation-free. Decomposing $u = (u \mathbin{\&} \text{0x7F}) + ((u \gg 7) \ll 7)$ eliminates `PMADDUBSW` overflow for arbitrary `i8` weights.

#### 1.2 Arm NEON `SQDMULH` / `SQRDMULH` and `gemmlowp` Rounding Bias

In `rust-lang/stdarch` (`neon/generated.rs:40766–40795, 41741`) and `google/gemmlowp` (`fixedpoint/fixedpoint.h:339–363`), Q15 ($W = 16$) and Q31 ($W = 32$) doubling high-multiply maps $a, b \in [-2^{W-1}, 2^{W-1}-1]$ to:
$$\operatorname{SQDMULH}_W(a, b) = \operatorname{sat}_W\!\left(\left\lfloor \frac{2 a b}{2^W} \right\rfloor\right), \qquad \operatorname{SQRDMULH}_W(a, b) = \operatorname{sat}_W\!\left(\left\lfloor \frac{2 a b + 2^{W-1}}{2^W} \right\rfloor\right)$$
Note that `gemmlowp::SaturatingRoundingDoublingHighMul` (`fixedpoint.h:346, 359`) adds `ab >= 0 ? (1 << (W-2)) : (1 - (1 << (W-2)))` before C++ truncating division `/ (1 << (W-1))`, differing by $1$ ULP on exact negative ties from hardware `SQRDMULH`'s floor bias $+2^{W-1}$. Both instructions saturate **if and only if** $a = b = -2^{W-1}$ ($2(-2^{W-1})^2 / 2^W = +2^{W-1} \mapsto 2^{W-1} - 1$), giving $\operatorname{PairSafe}_{\text{sqdmulh}}(a, b) \iff \neg(a = -2^{W-1} \land b = -2^{W-1})$.

#### 1.3 RISC-V Vector v1.0 `vnclip` Pre-Clip Rounding Overflow

In `riscv/riscv-v-spec` (`v-spec.adoc:602–649, 3205–3250`), `vnclip.wv`/`vnclip.wx`/`vnclip.wi` narrows a $2W$-bit signed integer $v$ by shift $d \in [0, 2W - 1]$ into $W$-bit signed range:
$$\operatorname{vnclip}_W(v, d, \text{vxrm}) = \operatorname{sat}_W\!\big((v \gg d) + r(v, d, \text{vxrm})\big)$$
where $v \gg d = \lfloor v / 2^d \rfloor$ and for $d \ge 1$ (`v-spec.adoc:628–632`): `rnu` (`00`) sets $r = v[d-1]$; `rne` (`01`) sets $r = v[d-1] \mathbin{\&} (\mathbb{I}(v[d-2:0] \ne 0) \mathbin{|} v[d])$; `rdn` (`10`) sets $r = 0$; `rod` (`11`) sets $r = (\neg v[d]) \mathbin{\&} \mathbb{I}(v[d-1:0] \ne 0)$.

Because **rounding precedes saturation** (`v-spec.adoc:3230–3231`), $-2^{W-1} \le \lfloor v / 2^d \rfloor \le 2^{W-1} - 1$ does **not** prevent saturation or `vxsat = 1`! For $W = 16, d = 15$ and $v = 32767 \cdot 2^{15} + 2^{14} = 1{,}073{,}725{,}440$, $\lfloor v / 2^{15} \rfloor = 32767$, yet $v[14] = 1$ and $v[15] = 1$ (since $32767$ is odd), so `rnu` and `rne` round to $32768$, clip to `32767`, and set `vxsat = 1`, whereas `rdn` and `rod` leave `vxsat = 0` (`rod` never overflows the top bin $2^{W-1}-1$ because $v[d] = 1 \implies \neg v[d] = 0$!).

| `vxrm` Mode | Exact No-Saturation (`vxsat = 0`) Interval on $v$ ($d \ge 1$) | Worst-Case Rounding Magnitude |
| :--- | :--- | :--- |
| `rdn` (`10`), `rod` (`11`) | $\big[-2^{W-1}\cdot 2^d,\; (2^{W-1}-1)\cdot 2^d + (2^d - 1)\big]$ | $(1 - 2^{-d})$ LSB (`rod` unbiased sticky) |
| `rnu` (`00`), `rne` (`01`) | $\big[-2^{W-1}\cdot 2^d,\; (2^{W-1}-1)\cdot 2^d + (2^{d-1} - 1)\big]$ | $\frac{1}{2}$ LSB (`rne` unbiased ties) |

---

### 2. Exact `Wrapping<u32>` Sliding-Window Integral-Image Bounds

`Basis: normative + source + derived + execution`

For a non-negative 2D image $I(\eta, \xi) \in [0, P_{\max}] \cap \mathbb{Z}$, the summed-area table (Crow 1984) $S(y, x) = \sum_{\eta < y, \xi < x} I(\eta, \xi)$ exceeds $2^{32} - 1$ on high-resolution/HDR frames (e.g., $512 \times 512$ `u16` sums to $1.718 \times 10^{10} > 4 \times 2^{32}$) and suffers severe Mantissa loss in IEEE-754 `f32` above $2^{24}$. Accumulating $\widehat{S}(y, x)$ in `core::num::Wrapping<u32>` (`library/core/src/num/wrapping.rs:41–43, 234–241`) exploits the ring homomorphism $\pi_{32} : \mathbb{Z} \to \mathbb{Z}/2^{32}\mathbb{Z}$ (Belt 2008):

**Exactness and Pre-Filter Error Theorem:** Since $\widehat{S}(y, x) = \pi_{32}(S(y, x))$ for all $(y, x)$, any window $[y_0, y_1) \times [x_0, x_1)$ of area $A = (y_1 - y_0)(x_1 - x_0)$ with true integer sum $W_{\text{exact}} = S(y_1, x_1) - S(y_0, x_1) - S(y_1, x_0) + S(y_0, x_0) \in [0, A \cdot P_{\max}]$ satisfies:
$$\widehat{W} := \big((\widehat{S}(y_1, x_1) \ominus_{32} \widehat{S}(y_0, x_1)) \ominus_{32} \widehat{S}(y_1, x_0)\big) \oplus_{32} \widehat{S}(y_0, x_0) = \pi_{32}(W_{\text{exact}})$$
Whenever **$A \cdot P_{\max} < 2^{32}$**, $\widehat{W}.\texttt{0} = W_{\text{exact}}$ **identically (`0` wrap error)** regardless of how many times $\widehat{S}$ wrapped globally! Furthermore, if each integer pixel $\hat{I}(\eta, \xi) \in [0, P_{\max}]$ comes from an upstream fixed-point SIMD kernel approximating $I^*(\eta, \xi) \ge 0$ with $|\hat{I}(\eta, \xi) - I^*(\eta, \xi)| \le \epsilon$, then $|\widehat{W} - \sum_{\eta, \xi} I^*(\eta, \xi)| \le A \cdot \epsilon$, independent of total frame dimensions $(H, W)$. On a $512 \times 512$ `u16` test frame (total sum $15{,}140{,}873{,}744 > 3.52 \times 2^{32}$, $64 \times 64$ window sum $236{,}294{,}144$), `Wrapping<u32>` yields `236,294,144` (`err = 0`) while `f32` yields `236,288,000.0` (`abs_err = 6,144.0`). Signed residuals in $[-P_{\min}, P_{\max}]$ accumulated in `Wrapping<i32>` are likewise exact whenever $-2^{31} \le -A \cdot P_{\min}$ and $A \cdot P_{\max} \le 2^{31} - 1$.

---

### 3. Division-Free `DyadicFloat` Jury-Stein-Lyapunov Certificates for Biquad/IIR Filters

`Basis: derived + source + execution`

#### 3.1 `DyadicFloat` Ring (`m · 2^e`) vs Rational Division

Representing exact dyadic rationals $\mathbb{D} = \{m \cdot 2^e : m, e \in \mathbb{Z}\}$ (`DyadicFloat { m: Int, e: Int }`, matching Flocq's `Defs.float 2`, Boldo & Melquiond 2011) embeds every Q-format integer coefficient losslessly and reduces $+, -, \times$, and $> 0$ ($m > 0$) to exact integer arithmetic with zero IEEE-754 axioms. Because $\mathbb{D} = \mathbb{Z}[1/2]$ is **not** closed under division by odd integers, Lyapunov certificates over $\mathbb{D}$ must avoid rational inversion.

#### 3.2 Jury Factorization of the Stein Determinant and Polynomial $\tilde{P} \in \mathbb{D}^{2 \times 2}$

For a second-order biquad denominator $D(z) = z^2 + a_1 z + a_2$ ($a_1, a_2 \in \mathbb{D}$) with companion matrix $A_c = \begin{pmatrix} -a_1 & -a_2 \\ 1 & 0 \end{pmatrix}$, Euclidean norm contraction fails whenever $a_1 \ne 0$ because $(I_2 - A_c^T A_c)_{1,1} = -a_1^2 < 0$. Instead, consider the discrete-time Stein-Lyapunov system $P - A_c^T P A_c = Q_0$ for symmetric $P = \begin{pmatrix} p_{11} & p_{12} \\ p_{12} & p_{22} \end{pmatrix}$ and $Q_0 = I_2$:
$$(1 - a_1^2) p_{11} + 2 a_1 p_{12} - p_{22} = 1, \qquad -a_1 a_2 p_{11} + (1 + a_2) p_{12} = 0, \qquad -a_2^2 p_{11} + p_{22} = 1$$
Define the three linear Jury stability margins (Jury & Blanchard 1961):
$$J_1 = 1 - a_2, \qquad J_2 = 1 + a_2 - a_1, \qquad J_3 = 1 + a_2 + a_1$$
Note $J_2 > 0 \land J_3 > 0 \implies 2(1 + a_2) = J_2 + J_3 > 0 \implies a_2 > -1$, so $J_1, J_2, J_3 > 0 \iff |a_2| < 1 \land |a_1| < 1 + a_2$. Eliminating $p_{12}, p_{22}$ yields $[(1 - a_1^2 - a_2^2)(1 + a_2) + 2 a_1^2 a_2] p_{11} = 2(1 + a_2)$, whose coefficient factors over $\mathbb{Z}[a_1, a_2]$ directly into the Jury margins:
$$\Delta(a_1, a_2) := (1 - a_2)\big((1 + a_2)^2 - a_1^2\big) = (1 - a_2)(1 + a_2 - a_1)(1 + a_2 + a_1) = J_1 J_2 J_3$$
Crucially, substituting $p_{11} = 2(1 + a_2)/\Delta$ into $(1 + a_2) p_{12} = a_1 a_2 p_{11}$ **cancels $(1 + a_2)$ identically**, leaving $p_{12} = 2 a_1 a_2 / \Delta$. Multiplying through by $\Delta(a_1, a_2)$ clears all denominators and yields the **exact polynomial `DyadicFloat` certificate**:
$$\tilde{P}(a_1, a_2) = \begin{pmatrix} 2(1 + a_2) & 2 a_1 a_2 \\ 2 a_1 a_2 & \Delta(a_1, a_2) + 2(1 + a_2) a_2^2 \end{pmatrix} \in \mathbb{D}^{2 \times 2}$$

**Theorem (Division-Free `DyadicFloat` Stein-Lyapunov Certificate):** For all $a_1, a_2 \in \mathbb{D}$:
1. $\tilde{P}(a_1, a_2) - A_c^T \tilde{P}(a_1, a_2) A_c = \Delta(a_1, a_2) I_2$ holds as a universal polynomial ring identity over $\mathbb{Z}[a_1, a_2]$.
2. If $J_1, J_2, J_3 > 0$, then $\Delta = J_1 J_2 J_3 > 0$, $\tilde{p}_{11} = J_2 + J_3 > 0$, and $\det \tilde{P} = 2(1 + a_2)\Delta + 4 a_2^2 J_2 J_3 > 0$, establishing $\tilde{P} \succ 0$ and strict contraction $x^T A_c^T \tilde{P} A_c x = x^T \tilde{P} x - \Delta \|x\|_2^2$ via three dyadic sign checks.
3. For Q14 coefficients $a_1 = -24576 \cdot 2^{-14} = -3/2$, $a_2 = 11520 \cdot 2^{-14} = 45/64$ ($|\lambda|^2 = 45/64 < 1$), exact `DyadicFloat` arithmetic gives $J_1 = 19/64, J_2 = 205/64, J_3 = 13/64$, $\Delta = 50635 \cdot 2^{-18}$, $\tilde{P} = \begin{pmatrix} 109/32 & -135/64 \\ -135/64 & 492085/262144 \end{pmatrix}$, and $\det \tilde{P} = 16312465 \cdot 2^{-23} > 0$. Cascaded $K$-biquad IIR filters certify stability section-by-section in $O(K)$ operations.

---

### 4. Finite-Wordlength Limit Cycles, Guard-Bit Wrapping, and Roundoff Ellipsoids

`Basis: source + derived + execution`

1. **1-Guard-Bit Wrapping vs 64-Bit Saturating Accumulators in `CMSIS-DSP`:**
   `arm_biquad_cascade_df1_q15.c` (`L51–56, 531, 566–579`) accumulates in 64-bit `q63_t` (`34.30` format, **33 guard bits**) before `__SSAT((acc >> shift), 16)`. By contrast, `arm_biquad_cascade_df1_fast_q15.c` (`L51–55, 117–124`) and `arm_biquad_cascade_df1_q31.c` (`L51–56`) accumulate in `2.30` or `2.62` with **only 1 guard bit** (`[-2.0, +2.0)`), wrapping on internal overflow. On the Jury-stable biquad $(a_1 = -3/2, a_2 = 45/64)$ from initial state $(28000, -28000)$ with zero input, two's-complement `i16` wrapping sustains a permanent autonomous overflow limit cycle (`(-25804, -3479)` at step `200`), whereas saturating output decays to `(-1, -1)`. Soundness of 1-guard-bit accumulators therefore requires proving $|b_0 u_k + b_1 u_{k-1} + b_2 u_{k-2} - a_1 y_{k-1} - a_2 y_{k-2}| < 2.0 \cdot 2^{\text{postShift}}$ over the reachable state set.
2. **Diagonal Lyapunov Witnesses Eliminate Zero-Input Saturation Oscillations:**
   Under 2-state saturation $\hat{x}_{k+1} = \operatorname{sat}_W(A \hat{x}_k)$, componentwise saturation is non-expansive in $V_P(x) = x^T P x$ for all $z \in \mathbb{R}^2$ **iff $P \succ 0$ is diagonal** (Barnes & Fam 1977; Mills, Mullis & Roberts 1978). Realizing complex poles $\alpha \pm i\beta$ ($\alpha, \beta \in \mathbb{D}$, $\alpha^2 + \beta^2 < 1$) in coupled normal form $A_{\text{coupled}} = \begin{pmatrix} \alpha & -\beta \\ \beta & \alpha \end{pmatrix}$ satisfies $I_2 - A_{\text{coupled}}^T I_2 A_{\text{coupled}} = (1 - \alpha^2 - \beta^2) I_2 \succ 0$ with **diagonal** $P = I_2$, guaranteeing $\|\operatorname{sat}_W(A_{\text{coupled}} x)\|_2^2 \le (\alpha^2 + \beta^2)\|x\|_2^2 < \|x\|_2^2$ for all $x \ne 0$.
3. **Division-Free Roundoff & Input Invariant Ellipsoid ($\mathcal{E}_\infty$):**
   Given $\tilde{P} - A^T \tilde{P} A = \Delta I_2$ ($\Delta > 0$) and trace bound $U = \tilde{p}_{11} + \tilde{p}_{22} > \Delta$, let $\mu = \Delta / U \in (0, 1)$, so $A^T \tilde{P} A \preceq (1 - \mu) \tilde{P}$. For $x_{k+1} = A x_k + e_k$ ($e_k = B u_k + \eta_k$ combining bounded input and rounding error $|\eta_{k,i}| \le \epsilon_{\text{quant}}$) with $e_k^T \tilde{P} e_k \le E_{\max}$, Peter-Paul's inequality with $\theta = \frac{\mu}{2(1 - \mu)}$ proves positive invariance of:
   $$\mathcal{E}_{\infty} = \left\{ x \in \mathbb{R}^2 : \mu^2 (x^T \tilde{P} x) \le (2 - \mu) E_{\max} \right\}$$
   Coordinatewise register bounds follow without square roots or divisions via $x_1^2 \det \tilde{P} \le \tilde{p}_{22} (x^T \tilde{P} x)$ and $x_2^2 \det \tilde{P} \le \tilde{p}_{11} (x^T \tilde{P} x)$ entirely inside $\mathbb{D}$.

## Boundaries

- **`not examined` — Granular deadband limit cycles ($\pm 1$–$2$ LSB zero-input oscillations):** While $\mathcal{E}_\infty$ bounds granular error amplitude by $O(\epsilon_{\text{quant}}/\mu)$ and coupled form eliminates overflow oscillations, exact deadband limit-cycle periods under `rnu`/`rne` vs `rdn` were `not examined`.
- **`not examined` — Time-varying IIR parameter modulation:** All certificates assume stationary coefficients $(a_1, a_2)$ per biquad section; common-Lyapunov synthesis across time-varying audio sweeps was `not examined`.
- **`unknown` — Symbolic factor cancellation in Direct Form Stein adjugates for monolithic order $N \ge 4$:** Whether symbolic denominator factors analogous to $(1 + a_2)$ cancel in monolithic companion matrices of order $N \ge 4$ (without factoring into second-order biquad cascades) remains `unknown`.
- **`known not to apply` — Proving `vnclip` saturation-freedom from $\lfloor v / 2^d \rfloor \le 2^{W-1}-1$ under `rnu` or `rne`:** Pre-clip rounding overflows the top bin ($v = 1{,}073{,}725{,}440$ at $W = 16, d = 15$ sets `vxsat = 1`); the floor bound alone is `known not to apply`.
- **`known not to apply` — Identity-matrix Euclidean contraction ($I_2 - A_c^T A_c \succ 0$) on companion realizations:** Since $(I_2 - A_c^T A_c)_{1,1} = -a_1^2 < 0$ for all $a_1 \ne 0$, unweighted Euclidean contraction is `known not to apply`.
- **`unsupported` — Single-instruction signed-to-unsigned narrowing clip in RVV v1.0:** `riscv/riscv-v-spec` (`v-spec.adoc:3237–3243`) states that single-instruction signed-to-unsigned saturation is `unsupported` (requiring `vmax` against `0` at $2 \cdot \text{SEW}$ followed by `vsetvli` and `vnclipu`).

## Evidence

### Primary Upstream Repositories and Specifications

1. **`rust-lang/stdarch` (`ca26a96d57b295dcd927622877242940a0f3c02e`):** `crates/core_arch/src/x86/ssse3.rs:277–303, 349–357` (`_mm_maddubs_epi16`), `avx2.rs:1853–1860` (`_mm256_maddubs_epi16`), `arm_shared/neon/generated.rs:40755–40795, 41741` (`vqdmulhq_s16`, `vqdmulh_s32`, `vqrdmulhq_s16`).
2. **`rust-lang/rust` (`c7d5ba59d8e11ee2e2204b173458eec4cb41c973`):** `library/core/src/num/wrapping.rs:39–44, 230–270` (`Wrapping<T>`).
3. **`riscv/riscv-v-spec` (`2f68ef7256d6ec53e4d2bd7cb12862f406d64e34`, v1.0):** `v-spec.adoc:602–664` (`vxrm`, `roundoff_signed`, `vxsat`) and `L3153–3250` (`vsmul.vv`, `vnclipu`/`vnclip`).
4. **`ARM-software/CMSIS-DSP` (`9f64ba31591e527c505951943b4b95b0eb2f834b`):** `Source/FilteringFunctions/arm_biquad_cascade_df1_q15.c:50–59, 531–595`, `arm_biquad_cascade_df1_fast_q15.c:50–60, 117–125`, `arm_biquad_cascade_df1_q31.c:50–59, 123–130`.
5. **`google/gemmlowp` (`16e8662c34917be0065110bfcd9cc27d30f52fdf`):** `fixedpoint/fixedpoint.h:262–380` (`SaturatingRoundingDoublingHighMul`).
6. **`llvm/llvm-project` (`c11543baec3048ab67ebb61f2186172f90983d57`):** Target intrinsics `llvm.x86.ssse3.pmadd.ub.sw.128` and `llvm.aarch64.neon.sqdmulh.*`.

### Literature

- R. E. Kalman and J. E. Bertram, "Control system analysis and design via the 'second method' of Lyapunov: II. Discrete-time systems," *J. Basic Eng.*, 82(2):394–400, 1960. DOI: `10.1115/1.3662605`.
- E. I. Jury and J. Blanchard, "A stability test for linear discrete systems in table form," *Proc. IRE*, 49(12):1947–1948, 1961. DOI: `10.1109/JRPROC.1961.288137`.
- C. W. Barnes and A. T. Fam, "Minimum norm recursive digital filters that are free of overflow limit cycles," *IEEE Trans. Circuits Syst.*, CAS-24(10):569–574, 1977. DOI: `10.1109/TCS.1977.1084275`.
- W. L. Mills, C. T. Mullis, and R. A. Roberts, "Digital filter realizations without overflow oscillations," *IEEE Trans. Acoust., Speech, Signal Process.*, ASSP-26(4):334–338, 1978. DOI: `10.1109/TASSP.1978.1163114`.
- F. C. Crow, "Summed-area tables for texture mapping," *SIGGRAPH '84*, pp. 207–212, 1984. DOI: `10.1145/964965.808600`.
- H. J. W. Belt, "Word length reduction for the integral image," *IEEE ICIP 2008*, pp. 805–808, 2008. DOI: `10.1109/ICIP.2008.4711877`.
- S. Boldo and G. Melquiond, "Flocq: A unified library for proving floating-point algorithms in Coq," *IEEE ARITH 2011*, pp. 243–252, 2011. DOI: `10.1109/ARITH.2011.40`.
- B. Jacob et al., "Quantization and Training of Neural Networks for Efficient Integer-Arithmetic-Only Inference," *IEEE/CVF CVPR 2018*, pp. 2704–2713, 2018. DOI: `10.1109/CVPR.2018.00286`.
- A. Volkova, T. Hilaire, and C. Q. Lauter, "Arithmetic Approaches for Rigorous Design of Reliable Fixed-Point LTI Filters," *IEEE Trans. Comput.*, 69(4):489–504, 2020. DOI: `10.1109/TC.2019.2950658`.

### Execution Verification (`2026-11-20`, revalidated `2026-11-21`)

Verified via Python 3.11 exact integer and `DyadicFloat` execution: `49,279 / 65,536` `PMADDUBSW` `PairSafe` pairs at $U_{\max} = 255$ and `65,536 / 65,536` at $U_{\max} = 128$; RVV `vnclip` ($W = 16, d = 15, v = 1{,}073{,}725{,}440$) yields `vxsat = 1` on `rnu`/`rne` vs `0` on `rdn`/`rod`; $512 \times 512$ `u16` `Wrapping<u32>` integral image yields `0` error (`236,294,144`) vs `6,144.0` `f32` error after $3\times$ $2^{32}$ wraps; `DyadicFloat` $\tilde{P}$ satisfies $\tilde{P} - A_c^T \tilde{P} A_c - \Delta I_2 = 0$ identically.

## Revalidation

Run this self-contained `< 0.2 s` Python 3 script to revalidate all four discriminators:

```python
#!/usr/bin/env python3
from dataclasses import dataclass

@dataclass(frozen=True)
class Dyadic:
    m: int; e: int
    @staticmethod
    def norm(m: int, e: int) -> "Dyadic":
        if m == 0: return Dyadic(0, 0)
        while (m & 1) == 0: m >>= 1; e += 1
        return Dyadic(m, e)
    def __add__(self, o: "Dyadic") -> "Dyadic":
        return Dyadic.norm(self.m + (o.m << (o.e - self.e)), self.e) if self.e <= o.e \
               else Dyadic.norm((self.m << (self.e - o.e)) + o.m, o.e)
    def __sub__(self, o: "Dyadic") -> "Dyadic": return self + Dyadic(-o.m, o.e)
    def __mul__(self, o: "Dyadic") -> "Dyadic": return Dyadic.norm(self.m * o.m, self.e + o.e)

safe = sum(
    int(((min(s0, 0) + min(s1, 0) >= -128) and (max(s0, 0) + max(s1, 0) <= 128))
        == (-32768 <= 255 * (min(s0, 0) + min(s1, 0)) and 255 * (max(s0, 0) + max(s1, 0)) <= 32767))
    and int((min(s0, 0) + min(s1, 0) >= -128) and (max(s0, 0) + max(s1, 0) <= 128))
    for s0 in range(-128, 128) for s1 in range(-128, 128)
)
assert safe == 49279

v = (32767 << 15) + (1 << 14)
assert ((v >> 15) + ((v >> 14) & 1)) == 32768 and ((v >> 15) + (1 - ((v >> 15) & 1))) == 32767

W, H = 512, 512
sat_w, sat_z = [[0] * (W + 1) for _ in range(H + 1)], [[0] * (W + 1) for _ in range(H + 1)]
for y in range(1, H + 1):
    rw = rz = 0
    for x in range(1, W + 1):
        px = 50000 + ((y * 73 + x * 137) % 15536)
        rw = (rw + px) & 0xFFFFFFFF; rz += px
        sat_w[y][x] = (sat_w[y - 1][x] + rw) & 0xFFFFFFFF; sat_z[y][x] = sat_z[y - 1][x] + rz
assert sat_z[H][W] > 3 * (1 << 32)
assert ((sat_w[512][512] - sat_w[448][512] - sat_w[512][448] + sat_w[448][448]) & 0xFFFFFFFF) == 236294144

one, two = Dyadic(1, 0), Dyadic(1, 1)
a1, a2 = Dyadic.norm(-24576, -14), Dyadic.norm(11520, -14)
j1, j2, j3 = one - a2, one + a2 - a1, one + a2 + a1
delta = j1 * j2 * j3
p11, p12, p22 = two * (one + a2), two * a1 * a2, delta + two * (one + a2) * a2 * a2
assert j1.m > 0 and j2.m > 0 and j3.m > 0 and (p11 * p22 - p12 * p12).m > 0
assert p11 - (a1 * a1 * p11 - two * a1 * p12 + p22) == delta
assert p12 - (a1 * a2 * p11 - a2 * p12) == Dyadic(0, 0)
assert p22 - (a2 * a2 * p11) == delta
print("ALL REVALIDATION CHECKS PASSED")
```
