# GF(2^8) SIMD Reed-Solomon Erasure Coding, Non-MDS Vandermonde Singularities, DRAM Chipkill vs. DDR5 On-Die ECC Aliasing, and RAID Reconstruction Hazards

## Summary

Storage erasure coding, rank-level DRAM Chipkill ECC, and software RAID share the same underlying linear algebra over binary extension fields $\mathrm{GF}(2^w)$, yet regularly fail in production due to four distinct algebraic and systems boundary violations:

1. **ISA-Dispatch-Dependent Table Layouts and Polynomial Mismatch in $\mathrm{GF}(2^8)$ SIMD (`intel/isa-l`):** `intel/isa-l` operates over $\mathrm{GF}(2^8) \cong \mathbb{F}_2[x]/(x^8 + x^4 + x^3 + x^2 + 1)$ (`0x11d`, primitive root $g = 2$), whereas x86 `GFNI` `VGF2P8MULB` hardcodes the AES Rijndael polynomial $x^8 + x^4 + x^3 + x + 1$ (`0x11b`). Consequently, `isa-l` implements `GFNI` multiplication via `VGF2P8AFFINEQB` using precomputed $8 \times 8$ $\mathrm{GF}(2)$ bit-matrices (`gf_table_gfni`). Although `ec_init_tables` always writes a `32 * k * rows`-byte `unsigned char *g_tbls` array, its in-memory format switches incompatibly at runtime between split-nibble `vpshufb` lookup tables (`tbl[1] == c`) on SSE/AVX2/AVX-512-non-GFNI hosts and quad-replicated `uint64_t` affine bit-matrices (`tbl[1] == 0x40` for $c = 1$) on `GFNI` hosts. Passing a `GFNI`-initialized `g_tbls` to `ec_encode_data_base`, `ec_encode_data_avx2`, or `ec_encode_data_avx512`, or serializing `g_tbls` across heterogeneous CPUs, silently corrupts all encoded parities and reconstructions without error.
2. **Singular Decode Submatrices in Appended Vandermonde Generators vs. Totally Nonsingular Cauchy Matrices:** A systematic generator matrix $G = \begin{bmatrix} I_k \\ P \end{bmatrix} \in \mathrm{GF}(2^w)^{n \times k}$ is Maximum Distance Separable (MDS)—guaranteeing invertibility of *every* $k \times k$ survivor submatrix—if and only if *every* square submatrix of the parity block $P$ of every order $1 \le s \le \min(n-k, k)$ is nonsingular. Appending raw Vandermonde rows $P_{r,c} = (2^r)^c$ directly beneath $I_k$ (`intel/isa-l`'s `gf_gen_rs_matrix`) or $P_{r,c} = (c+1)^r$ (`PARv1` / `klauspost/reedsolomon`'s `buildMatrixPAR1`) violates total nonsingularity in characteristic 2 because lacunary Vandermonde minors factor through Schur polynomials that vanish on $\mathrm{GF}(2^8)$ elements: `gf_gen_rs_matrix` produces non-invertible $k \times k$ survivor matrices at $(k=6, p=5, n=11)$, $(k=5, p=6, n=11)$, and $(k=22, p=4, n=26)$, while `PARv1` fails as early as $(k=3, p=4, n=7)$. Strict MDS behavior over $\mathrm{GF}(2^8)$ requires either a Cauchy parity block $P_{r,c} = (x_r \oplus y_c)^{-1}$ over disjoint $X \cap Y = \emptyset$ (`gf_gen_cauchy1_matrix`, valid for $n \le 256$, failing at $n \ge 257$ due to `uint8_t` wrap) or right-inversion of a full $n \times k$ Vandermonde matrix $G = V \cdot V_{0..k-1}^{-1}$ (`klauspost/reedsolomon`'s default `buildMatrix`).
3. **DDR5 `[136, 128, d=3]` SEC On-Die ECC Miscorrection, `x4` Internal Read-Modify-Write, and Rank Telemetry Suppression:** JEDEC JESD79-5 mandates an internal `[136, 128, d=3]` Single-Error-Correcting (SEC, *without* Double-Error Detection) Hamming code per DRAM die. Because $136$ columns exhaust $136 / 255 \approx 53.3\%$ of the $2^8 - 1 = 255$ non-zero 8-bit syndromes, $88.33\%$ ($8{,}109 / 9{,}180$) of 2-bit raw cell errors within a 136-bit word alias to a non-zero column of $H_{\text{OD}}$ and are **miscorrected into 3-bit post-OD-ECC errors**. When paired with a balanced `[72, 64, d=4]` Hsiao SEC-DED rank code, $59.55\%$ of resulting 3-bit single-burst errors miscorrect again into Silent Data Corruption (`47.97%` 4-bit data corruption, `11.59%` check-bit masking). Furthermore, on `x4` Chipkill devices (`BL16` $= 64$ external bits $= \frac{1}{2}$ of the 128-bit OD-ECC block), every 64-bit write triggers an in-DRAM Read-Modify-Write that can permanently bake a 3-bit miscorrection into the untouched companion 64-bit cache line, while silent OD-ECC correction starves OS `rasdaemon` `mc_event` predictive failure counters unless DDR5 Error Check and Scrub (`ECS`, AMD `SMCA_UMC` `XEC=8,9`) alerts are monitored.
4. **Erasures-vs-Errors Amplification and Non-Atomic RAID Write-Holes:** Minimum distance $d = p + 1$ repairs up to $p$ *located erasures* (`-EIO` / missing shards) or $\lfloor p/2 \rfloor$ *unknown errors*, satisfying $2t + e \le p$. Passing an unflagged corrupted shard ($t \ge 1$) into a linear erasure decoder (`ec_encode_data` / `Reconstruct`) propagates linear combinations of the error into every reconstructed shard; worse, Linux MD RAID-6 `repair` (`!MD_RECOVERY_CHECK` in `handle_parity_checks6`) unconditionally overwrites `P` and `Q` from data disks rather than solving $Q/P = g^j$ to locate a corrupted data disk. Similarly, interrupted sub-stripe writes create a latent parity write-hole $\Delta = D_0 \oplus D_0'$ that corrupts *untouched* sibling disks upon later single-disk rebuild unless closed by copy-on-write full-stripe allocation, full data+parity journaling (`r5c`), or RAID-5 Partial Parity Logging (`PPL`, `raid5-ppl.c`, which still leaves RAID-6 and simultaneous modified-disk crashes uncovered).

## Applicability

The findings in this report govern storage engines, FFI wrappers around SIMD erasure libraries, memory-reliability telemetry daemons, and formal verification models of linear block codes across the following pinned artifacts and relationships:

- **SIMD Erasure Coding Libraries (Comparison and FFI Contract):**
  - `intel/isa-l` at commit `af6a939795a967fc7de4256ab40db85c7fc73ffb` (`include/erasure_code.h`, `erasure_code/ec_base.c`, `erasure_code/ec_base.h`, `erasure_code/ec_highlevel_func.c`, `erasure_code/ec_multibinary.asm`, `erasure_code/gf_vect_gfni.inc`, `erasure_code/gf_vect_dot_prod_avx512.asm`, `erasure_code/gf_vect_dot_prod_avx512_gfni.asm`, `erasure_code/gen_rs_matrix_limits.c`). Note ISA-L's parameter convention: in `gf_gen_rs_matrix(a, m, k)` and `gf_gen_cauchy1_matrix(a, m, k)`, **`m` denotes total shards $n = k + p$** (`srcs + parity`), *not* parity shard count $p$; throughout this report we write $k$ for data shards, $p$ for parity shards, and $n = m_{\text{ISA-L}} = k + p$ for total shards to prevent ambiguity.
  - `klauspost/reedsolomon` at commit `25e5c5227103dc948f3e1888a8c9d62be1bafd1e` (`reedsolomon.go`, `matrix.go`, `galois.go`), contrasted directly against ISA-L's matrix builders (`buildMatrix`, `buildMatrixJerasure`, `buildMatrixPAR1`, `buildMatrixCauchy`, and `leopardFits` FFT skew-table bounds).
  - Distributed Local Reconstruction Codes (`LRC`) as defined by Huang et al. (USENIX ATC 2012) and Plank & Ding (`DOI: 10.1002/spe.631`) / Plank & Xu (`DOI: 10.1109/NCA.2006.43`).
- **DRAM ECC Hardware/OS Telemetry Stack (Vertical Composition):**
  - JEDEC `JESD79-5` DDR5 SDRAM `[136, 128]` on-die SEC ECC and Error Check and Scrub (`ECS`), empirical on-die ECC miscorrection models established by Patel et al. (`DOI: 10.1109/DSN.2019.00017`, `DOI: 10.1109/MICRO50266.2020.00034`), Linux kernel `v6.12` (`torvalds/linux` at `adc218676eef25575469234709c2d87185ca223a`, `drivers/edac/amd64_edac.c`), and `mchehab/rasdaemon` at `5e547c331d31e4f47c0fb4204e039a69a1fcf68d` (`events/ras-mc-handler.c`, `events-arch-x86/mce-amd-smca.c`).
- **Block-Layer RAID Reconstruction and Crash Recovery:**
  - Linux kernel `v6.12` (`torvalds/linux` at `adc218676eef25575469234709c2d87185ca223a`, `drivers/md/raid5.c` and `drivers/md/raid5-ppl.c`).
- **Target Constraints:** SIMD instruction semantics apply to x86-64 processors implementing `SSSE3`/`AVX2`, `AVX-512BW`/`AVX-512VL`, and `GFNI` (`CPUID.7.0:ECX.GFNI[bit 8]`). Algebraic MDS, LRC, and Hamming/Hsiao syndrome results hold mathematically for all implementations sharing the specified field polynomials and parity-check dimensions, independent of CPU architecture.

## Findings

### 1. $\mathrm{GF}(2^8)$ Field Representation, Split-Nibble `vpshufb`, and the `GFNI` Table ABI Hazard

`Basis: normative + source + execution`

Both `intel/isa-l` (`erasure_code/ec_base.c:176-280`, `erasure_code/ec_base.h:104-120`) and `klauspost/reedsolomon` (`galois.go`) represent $\mathrm{GF}(2^8)$ as the quotient ring:

$$\mathrm{GF}(2^8) \cong \mathbb{F}_2[x] / \langle p_{\text{ISA-L}}(x) \rangle, \qquad p_{\text{ISA-L}}(x) = x^8 + x^4 + x^3 + x^2 + 1 \quad (\text{hex } \mathtt{0x11d})$$

Because $p_{\text{ISA-L}}(x)$ is a *primitive* polynomial over $\mathbb{F}_2$, the residue class $\alpha = x \equiv \mathtt{0x02}$ generates the entire multiplicative group $\mathrm{GF}(2^8)^\times$ of order $255 = 3 \times 5 \times 17$: multiplication by $\mathtt{0x02}$ reduces to `(c << 1) ^ ((c & 0x80) ? 0x1d : 0)` (`ec_base.c:178`), discrete logarithms use base $2$ (`gf_mul` and `gf_inv` in `ec_base.c:50-76`), and `0x00` maps to `0x00` under `gf_inv(0) == 0` (`ec_base.c:69-70`).

#### 1.1 Why `GFNI` Kernels Cannot Use `VGF2P8MULB` Directly

The x86 Galois Field New Instructions (`GFNI`) extension provides two multiplication primitives:
- `VGF2P8MULB` performs lane-wise $\mathrm{GF}(2^8)$ multiplication modulo the **hardcoded AES Rijndael polynomial** $p_{\text{AES}}(x) = x^8 + x^4 + x^3 + x + 1$ ($\mathtt{0x11b}$), which is irreducible over $\mathbb{F}_2$ but *not* primitive with generator $x = \mathtt{0x02}$ ($\mathtt{0x02}^{51} \equiv 1 \pmod{p_{\text{AES}}}$; $\mathtt{0x03}$ is primitive instead). Using `VGF2P8MULB` directly on `0x11d`-encoded shards without field-isomorphism basis conversion produces algebraically incompatible parities.
- `VGF2P8AFFINEQB dst, src1, src2, imm8` treats each byte $b = \sum_{j=0}^7 b_j 2^j$ of `src1` as an 8-bit vector over $\mathbb{F}_2$ and multiplies it by an arbitrary $8 \times 8$ binary matrix $M \in \mathbb{F}_2^{8 \times 8}$ packed as a 64-bit qword in `src2`:

$$\text{dst\_bit}_i = \left(\bigoplus_{j=0}^{7} M_{7-i,\, j} \cdot b_j\right) \oplus \text{imm8}_i \qquad (0 \le i \le 7)$$

Because multiplication $x \mapsto c \cdot x$ in $\mathbb{F}_2[x]/\langle p_{\text{ISA-L}}(x)\rangle$ is an $\mathbb{F}_2$-linear endomorphism of $\mathbb{F}_2^8$, every constant multiplier $c \in \mathrm{GF}(2^8)$ is uniquely represented by an $8 \times 8$ matrix $M^{(c)}$ whose $j$-th column ($0 \le j \le 7$) is the 8-bit expansion of $\mathrm{gf\_mul}(c, 2^j)$, packed in MSB-first row order (`byte_idx = 7 - i`) into `uint64_t gf_table_gfni[256]` (`erasure_code/ec_base.h:35-100`). In `erasure_code/gf_vect_gfni.inc:34-72`, `isa-l` fuses up to 6 concurrent parity outputs per source load using `vgf2p8affineqb %%TMP_I, %%SRC, %%GFTABLE_I, 0x00` followed by `vpxorq`, cutting inner-loop instructions per source byte-vector from 6 (`vpandq` + `vpsraw` + `vpandq` + $2\times$`vpshufb` + `vpxorq` in `gf_vect_dot_prod_avx512.asm:149-162`) down to 2 (`vgf2p8affineqb` + `vpxorq`).

#### 1.2 Incompatible `g_tbls` Representations Behind Identical C Signatures

Both `ec_init_tables_base` (`ec_base.c:38-48`) and `ec_init_tables_gfni` (`ec_highlevel_func.c:463-473`) accept `unsigned char *g_tbls` of length $32 \cdot k \cdot \text{rows}$ bytes, and runtime multibinary dispatch (`ec_multibinary.asm:88-93`) routes `ec_init_tables` to `ec_init_tables_gfni` whenever AVX2+GFNI or AVX-512+GFNI is available. However, the 32-byte slot written per coefficient $c$ differs completely:

| Kernel Family | Table Initializer | 32-Byte Slot Contents `tbl[0..31]` for Multiplier $c$ | Value at `tbl[1]` for $c=\mathtt{0x01}, \mathtt{0x02}$ | Tail Handling (`len < 64`) |
| :--- | :--- | :--- | :--- | :--- |
| Scalar (`_base`) | `ec_init_tables_base` | Split-nibble LUT; scalar loop (`ec_base.c:290,320`) reads **only `tbl[1]`** as raw coefficient $c$ | `0x01`, `0x02` | Native byte loop (`len >= 0`) |
| SSE / AVX / AVX2 | `ec_init_tables_base` | `tbl[0..15] = [c*0..c*15]`, `tbl[16..31] = [c*0x00..c*0xf0]` for `pshufb`/`vpshufb` | `0x01`, `0x02` | `ec_encode_data_avx2` falls back to `_base` if `len < 32`; overlapped SIMD tail if `len > 32` |
| AVX-512 (`vpshufb`) | `ec_init_tables_base` | Same 32-byte split-nibble LUT broadcast via `vshufi64x2` (`gf_vect_dot_prod_avx512.asm:153-160`) | `0x01`, `0x02` | `ec_encode_data_avx512` (`ec_highlevel_func.c:308`) falls back to `_base` if `len < 64`; direct `gf_vect_dot_prod_avx512` **fails (`return 1`)** if `len < 32` (`line 184`) |
| AVX2-GFNI / AVX512-GFNI | `ec_init_tables_gfni` | Four identical copies `{val, val, val, val}` of `uint64_t val = gf_table_gfni[c]` (`ec_highlevel_func.c:454-460`) | **`0x40`**, **`0x20`** | **Cannot** call `_base`! `gf_vect_dot_prod_avx512_gfni.asm:170-180` uses EVEX opmask `k1 = (1 << len) - 1` (`vmovdqu8 x0{k1}`) down to `len = 1` |

**FFI and Cross-Call Safety Invariant:** Because `gf_table_gfni[1] = 0x0102040810204080ULL` stores bytes `[0x80, 0x40, 0x20, 0x10, 0x08, 0x04, 0x02, 0x01]` in little-endian memory, byte index 1 (`tbl[1]`) equals `0x40` instead of `0x01`. Any caller that initializes `g_tbls` via `ec_init_tables()` on a GFNI-capable host and subsequently invokes `ec_encode_data_base()`, `gf_vect_dot_prod_base()`, or an explicit arch-pinned symbol (`ec_encode_data_avx2`, `ec_encode_data_avx512`), or caches `g_tbls` across heterogeneous worker nodes, silently multiplies every data byte by `tbl_GFNI[1]` rather than $c$. Furthermore, in non-GFNI SIMD kernels (`gf_vect_dot_prod_avx512.asm:177-180`), unaligned buffer lengths $L > 64$ execute a final **overlapped 64-byte read and write** at `pos = L - 64`; callers wrapping ISA-L in Rust FFI must therefore enforce disjoint mutable borrows (`src[j]` never aliases `dest`, i.e., no in-place overwrite via `ec_encode_data`) and respect minimum length preconditions when invoking low-level `gf_*_dot_prod_*` symbols directly.

---

### 2. Non-MDS Vandermonde Singularities vs. Cauchy Matrices and Local Reconstruction Codes

`Basis: source + execution + derived`

#### 2.1 Total Nonsingularity Criterion for Systematic MDS Codes

Let $G = \begin{bmatrix} I_k \\ P \end{bmatrix} \in \mathbb{F}^{n \times k}$ be a systematic generator matrix with $k$ data rows and $p = n - k$ parity rows ($P \in \mathbb{F}^{p \times k}$). Suppose $e \le p$ shards are erased, leaving $k$ chosen surviving rows indexed by $D \subseteq \{0, \dots, k-1\}$ ($|D| = k - s$ surviving data shards, so $|\overline{D}| = s$ data shards are erased, with $0 \le s \le \min(p, k)$) and $R \subseteq \{0, \dots, p-1\}$ ($|R| = s$ surviving parity rows). Permuting the surviving data rows/columns to the top-left yields the block-triangular structure:

$$G_{\text{surv}} \sim \begin{bmatrix} I_{k-s} & 0 \\ P_{R, D} & P_{R, \overline{D}} \end{bmatrix} \implies \det(G_{\text{surv}}) = \pm \det(P_{R, \overline{D}})$$

(over $\mathrm{GF}(2^w)$, $+1 = -1$, so $\det(G_{\text{surv}}) = \det(P_{R, \overline{D}})$ identically). Hence **$G$ is MDS (every $k \times k$ row submatrix of $G$ is invertible) if and only if $P$ is *totally nonsingular* (superregular): every $s \times s$ square submatrix of $P$ for every $1 \le s \le \min(p, k)$ has non-zero determinant.**

#### 2.2 Why Appended Vandermonde Matrices Fail Over $\mathrm{GF}(2^8)$

A classical square Vandermonde matrix $V_{r, c} = x_r^c$ ($0 \le r, c < s$, contiguous exponents $0, 1, \dots, s-1$) is always nonsingular when $x_0, \dots, x_{s-1}$ are distinct ($\det V = \prod_{a < b} (x_b \oplus x_a) \neq 0$). However, arbitrary $s \times s$ submatrices $P_{R, \overline{D}}$ of a Vandermonde parity block select **non-contiguous column exponents** $0 \le e_1 < e_2 < \dots < e_s < k$, forming a *generalized (lacunary) Vandermonde* determinant:

$$\det\big([x_{r_a}^{e_b}]_{a,b=1}^s\big) = \left(\prod_{1 \le a < b \le s} (x_{r_b} \oplus x_{r_a})\right) \cdot s_{\lambda}(x_{r_1}, \dots, x_{r_s})$$

where $\lambda = (e_s - (s-1), \dots, e_2 - 1, e_1)$ and $s_{\lambda}$ is the Schur polynomial. Over $\mathbb{R}_{>0}$, $s_{\lambda}$ is a sum of positive monomials and cannot vanish; over $\mathrm{GF}(2^8)$, characteristic-2 cancellation and finite multiplicative subgroup orders ($255 = 3 \times 5 \times 17$) cause $s_{\lambda}$ to vanish on distinct non-zero evaluation points (`Plank & Ding, 2005`, `DOI: 10.1002/spe.631`).

Direct primary-source inspection and exhaustive execution over $\mathrm{GF}(2^8)$ (`0x11d`) establish the exact behavior of four canonical matrix constructors in `intel/isa-l` and `klauspost/reedsolomon`:

| Constructor | Upstream Location | Formula for $G \in \mathrm{GF}(2^8)^{n \times k}$ | MDS Status ($n \le 256$) | Minimal Singular $(k, p)$ Witness & Mechanism |
| :--- | :--- | :--- | :--- | :--- |
| `gf_gen_rs_matrix(a, n, k)` | `intel/isa-l` `ec_base.c:78-96` | $\begin{bmatrix} I_k \\ P \end{bmatrix}$ with $P_{r, c} = 2^{r \cdot c}$ ($0 \le r < p, 0 \le c < k$) | **NOT MDS** | Fails at **$(k=6, p=5, n=11)$**: erasing data $\{0, 3, 5\}$ and parity $\{8, 9\}$ leaves $3 \times 3$ parity minor $P_{(0,1,4), (0,3,5)} = \begin{bmatrix} 1 & 1 & 1 \\ 1 & 8 & 32 \\ 1 & 205 & 180 \end{bmatrix}$, which has rank 2. Also fails at **$(k=5, p=6, n=11)$** (survivors `(1,2,5,7,10)`) and **$(k=22, p=4, n=26)$** (minor $r=(0,1,3), c=(0,10,21)$). Safe *only* inside the five bounded regions documented in `erasure_code.h:1092-1096` (`k <= 3`; `k=4, n <= 25`; `k=5, n <= 10`; `k <= 21, p = 4`; `p <= 3`). |
| `buildMatrixPAR1(k, n)` | `klauspost/reedsolomon` `reedsolomon.go:375-394` | $\begin{bmatrix} I_k \\ P \end{bmatrix}$ with $P_{r, c} = (c+1)^r$ | **NOT MDS** | Fails at **$(k=3, p=4, n=7)$** (`survivors=(3, 4, 6)`): because field elements $1 \oplus 2 \oplus 3 = 0$ in $\mathbb{F}_2^8$ and $(a \oplus b)^{2^t} = a^{2^t} \oplus b^{2^t}$, columns satisfy $c_0 \oplus c_1 \oplus c_2 = 0$ on parity rows $r \in \{1, 2, 4, \dots\}$ and linear combinations collapse at $p=4$. |
| `gf_gen_cauchy1_matrix(a, n, k)` / `buildMatrixCauchy(k, n)` | `intel/isa-l` `ec_base.c:99-114`; `reedsolomon.go:396-414` | $\begin{bmatrix} I_k \\ P \end{bmatrix}$ with $P_{r, c} = ((k+r) \oplus c)^{-1}$ | **Strictly MDS** for $1 \le k < n \le 256$ | $X = \{k, \dots, n-1\}$ and $Y = \{0, \dots, k-1\}$ are disjoint in $\mathrm{GF}(2^8)$ whenever $n \le 256$. Every $s \times s$ minor equals $\frac{\prod_{a<b}(x_b \oplus x_a)(y_b \oplus y_a)}{\prod_{a,b}(x_a \oplus y_b)} \neq 0$. **Boundary hazard (`ec_base.c:113`):** ISA-L performs no bounds check on `m <= 256`; at $n = 257$, `(unsigned char)(256 ^ 0) == 0` and `gf_inv(0) == 0`, silently injecting zero entries into parity row 256! (`reedsolomon.go:221` rejects $n > 256$ with `ErrMaxShardNum` unless switching to 16-bit Leopard FFT). |
| `buildMatrix(k, n)` (Right-Inverted Vandermonde) | `klauspost/reedsolomon` `reedsolomon.go:259-283` | $G = V \cdot V_{0..k-1}^{-1}$ where $V_{r,c} = r^c$ ($0 \le r < n$) | **Strictly MDS** for $1 \le k < n \le 256$ | Every $k \times k$ row subset $V_S$ of $V$ has contiguous exponents $0..k-1$ and distinct evaluation nodes, so $\det(V_S) \neq 0$. Right-multiplication by $V_{0..k-1}^{-1} \in \mathrm{GL}_k(\mathrm{GF}(2^8))$ yields $\det(G_S) = \det(V_S)\det(V_{0..k-1})^{-1} \neq 0$ for all $\binom{n}{k}$ subsets $S$. |

#### 2.3 Local Reconstruction Codes (`LRC`) and Characteristic-2 Maximal Recoverability

Standard MDS $(k, p)$ Reed-Solomon codes (e.g., $(12, 4)$ Cauchy RS) achieve optimal storage overhead $(k+p)/k$, but **any single-shard failure requires reading $k = 12$ shards across failure domains** (reconstruction cost $= k$). Local Reconstruction Codes (`Huang et al., USENIX ATC 2012`) partition $k$ data shards into $l$ equal local groups of size $r = k/l$, add $l$ local XOR parities $L_0, \dots, L_{l-1}$ (one per group), and add $g$ global parities $G_0, \dots, G_{g-1}$ across all $k$ data shards ($n = k + l + g$).

1. **Information-Theoretic Distance and Single-Failure Locality:** Any single data or local-parity erasure is repaired by reading only the $r = k/l$ peers in its local group (for Azure `(k=12, l=2, g=2)`, $n=16$, overhead $1.33\times$, single-erasure repair reads **$6$ shards instead of $12$**). By Gopalan et al.'s LRC Singleton bound, minimum distance satisfies:
   $$d \le n - k - \left\lceil \frac{k}{r} \right\rceil + 2 = (k + l + g) - k - l + 2 = g + 2$$
   For `(12, 2, 2)` LRC, $d = 4$, guaranteeing **100% recovery of all $\binom{16}{3} = 560$ 3-shard erasures**.
2. **Exact Combinatorial Partition of 4-Shard Erasures and the Characteristic-2 Subspace Condition:** Out of $\binom{16}{4} = 1{,}820$ 4-shard erasures in `(12, 2, 2)` LRC (with 7-shard closed local groups $A = \{d_0..d_5, L_0\}$, $B = \{d_6..d_{11}, L_1\}$, and global parities $G = \{G_0, G_1\}$), an erasure set $E$ ($|E|=4$) is information-theoretically recoverable if and only if $\max(0, |E \cap A| - 1) + \max(0, |E \cap B| - 1) + |E \cap G| \le 2$. Exactly $252$ patterns violate this information-theoretic rank bound—$2\binom{7}{4} = 70$ of shape $(4,0,0)/(0,4,0)$, $2\binom{7}{3}\binom{2}{1} = 140$ of shape $(3,0,1)/(0,3,1)$, and $2\binom{7}{2}\binom{2}{2} = 42$ of shape $(2,0,2)/(0,2,2)$—leaving **$1{,}568$ ($86.15\%$) information-theoretically recoverable 4-erasure patterns**.
   - **Freshman's Dream Trap in Naive LRC Coefficient Selection:** Suppose $G_0$ uses coefficients $[\alpha_0, \dots, \alpha_5, \beta_0, \dots, \beta_5]$ and $G_1$ uses $[\alpha_0^2, \dots, \alpha_5^2, \beta_0^2, \dots, \beta_5^2]$. On a $(2, 2, 0)$ erasure erasing $\{d_{i_1}, d_{i_2}\} \subset A$ and $\{d_{j_1}, d_{j_2}\} \subset B$, eliminating $d_{i_2}$ and $d_{j_2}$ via $L_0$ and $L_1$ leaves a $2 \times 2$ global system with matrix:
     $$M = \begin{bmatrix} \alpha_{i_1} \oplus \alpha_{i_2} & \beta_{j_1} \oplus \beta_{j_2} \\ \alpha_{i_1}^2 \oplus \alpha_{i_2}^2 & \beta_{j_1}^2 \oplus \beta_{j_2}^2 \end{bmatrix} = \begin{bmatrix} u & v \\ u^2 & v^2 \end{bmatrix} \quad (\text{since } (a \oplus b)^2 = a^2 \oplus b^2 \text{ in } \mathrm{GF}(2^w))$$
     Because $\det(M) = u v (u \oplus v)$, $M$ is singular whenever $\alpha_{i_1} \oplus \alpha_{i_2} = \beta_{j_1} \oplus \beta_{j_2}$! Choosing sequential field elements `1..12` ($\alpha = [1..6], \beta = [7..12]$) causes $1 \oplus 2 = 3 = 8 \oplus 11$, losing cross-group $(2,2,0)$ recoverability. Placing Group 0 coefficients in a nonzero subset of the low nibble $\{1, \dots, 6\} \subset \mathrm{GF}(2^4) \setminus \{0\}$ and Group 1 in a disjoint $\mathbb{F}_2$-linear coset/subspace $\{\mathtt{0x10}, \mathtt{0x20}, \dots, \mathtt{0x60}\}$ guarantees $(A \oplus A) \cap (B \oplus B) = \{0\}$, achieving **100% Maximal Recoverability ($1{,}568 / 1{,}568$ recoverable 4-erasures)** (`Basis: execution + derived`).

---

### 3. DRAM `Chipkill` Symbol ECC vs. DDR5 `[136, 128]` On-Die ECC Aliasing and Telemetry Masking

`Basis: normative + source + execution + derived`

#### 3.1 Rank-Level Symbol Chipkill Architecture and Linux EDAC Decoding

Standard `[72, 64, d=4]` SEC-DED DIMM ECC operates over $\mathrm{GF}(2)$ bits and fails catastrophically when a single DRAM chip suffers a multi-bit pin, column-decoder, or bank failure. Server **Chipkill** (Single Device Data Correction, `SDDC`) aligns algebraic symbols over $\mathrm{GF}(2^b)$ ($b \in \{4, 8, 16\}$) with physical `x4` (or `x8`) device boundaries so any arbitrary bit-corruption pattern confined to a single DRAM die corrupts **at most one symbol** per Reed-Solomon codeword:
- **DDR4 `18x4` Rank:** 16 data `x4` chips + 2 ECC `x4` chips deliver $72\text{ bits/beat} \times 8\text{ beats} = 576\text{ bits}$. Grouping two beats per chip yields an $[n=18, k=16, d=3]$ Reed-Solomon code over $\mathrm{GF}(2^8)$ (or over four beats with $\mathrm{GF}(2^4)$/$\mathrm{GF}(2^8)$ eigenvector matrices in AMD Unified Memory Controllers). In Linux `v6.12` (`drivers/edac/amd64_edac.c:2543-2690`), `decode_syndrome` walks per-symbol 16-bit eigenvector tables (`x4_vectors` with 36 four-vector blocks for `ecc_sym_sz == 4`, `x8_vectors` with 19 eight-vector blocks for `ecc_sym_sz == 8`) against the hardware `MCA_SYND` syndrome to isolate the exact faulty symbol `err_sym` and physical channel.
- **DDR5 `10x4` Sub-Channel (EC8 RDIMM):** JEDEC `JESD79-5` splits each DIMM into **two independent 40-bit sub-channels** (`32` data DQ + `8` side-band ECC DQ $= 10$ `x4` dies per sub-channel) at Burst Length `BL16`, delivering $32 \times 16 = 512$ data bits (one 64 B cache line) + $8 \times 16 = 128$ side-band ECC bits per sub-channel burst ($25\%$ rank ECC overhead, supporting $[10, 8, d=3]$ symbol Chipkill over 8-bit or 16-bit symbol interleaves).

#### 3.2 Algebraic Miscorrection Cascade: `[136, 128, d=3]` On-Die SEC + Rank ECC

Under `JESD79-5` (and reverse-engineered on commercial devices via EIN/BEER in `Patel et al., DSN 2019`, `DOI: 10.1109/DSN.2019.00017`, and `MICRO 2020`, `DOI: 10.1109/MICRO50266.2020.00034`), every DDR5 DRAM die implements an internal **`[136, 128, d=3]` SEC Hamming code** (128 data bits + 8 internal parity bits, parity-check matrix $H_{\text{OD}} \in \mathbb{F}_2^{8 \times 136}$ with 136 distinct non-zero 8-bit columns). Crucially, 8 parity bits satisfy $2^8 - 1 = 255 \ge 136$ (sufficient for $d = 3$ SEC) but violate $2^{8-1} - 1 = 127 < 136$ (insufficient for $d = 4$ SEC-DED, which would require 9 parity bits).

Consequently, `JESD79-5` OD-ECC has **zero uncorrectable-error (`DED`) syndrome**: whenever a raw multi-bit error $e_{\text{raw}} \in \mathbb{F}_2^{136}$ ($\mathrm{wt}(e_{\text{raw}}) \ge 2$) produces a syndrome $s = H_{\text{OD}} e_{\text{raw}}$ matching *any* column $h_k$ of $H_{\text{OD}}$, the in-DRAM decoder flips bit $k$, emitting $e_{\text{post}} = e_{\text{raw}} \oplus u_k$ with $\mathrm{wt}(e_{\text{post}}) = \mathrm{wt}(e_{\text{raw}}) + 1$ onto the DQ bus without signaling any error pin:

1. **88.33% 2-Bit-to-3-Bit Amplification Inside the Die:** Across all $\binom{136}{2} = 9{,}180$ distinct 2-bit raw cell errors in a full-rank `[136, 128, d=3]` SEC code (using dense 8-bit syndromes), **$8{,}109 / 9{,}180$ ($88.33\%$)** collide with one of the 136 columns of $H_{\text{OD}}$ and are **amplified into weight-3 errors** (`Basis: execution`). Even for a random subset of 136 columns drawn uniformly from $\mathbb{F}_2^8 \setminus \{0\}$, the expected miscorrection rate is $134 / 254 = 52.76\%$.
2. **Silent Data Corruption (`SDC`) Under `[72, 64, d=4]` / EC4 SEC-DED Rank ECC:** Without OD-ECC, a 2-bit single-die burst error has even weight 2, so an odd-weight-column Hsiao `[72, 64, d=4]` SEC-DED rank controller detects **100%** of 2-bit errors (`even nonzero syndrome -> UE`). With `[136, 128, d=3]` OD-ECC, every 2-bit error that OD-ECC miscorrects into a 3rd bit within the same 64-bit transfer arrives at the rank controller with **weight 3**, producing an **odd-weight syndrome** ($h_{r,i} \oplus h_{r,j} \oplus h_{r,k}$ has odd Hamming weight because $3 \times \text{odd} \equiv \text{odd} \pmod 2$!). Because 72 of the 128 odd-weight vectors in $\mathbb{F}_2^8$ are valid single-bit columns of $H_{\text{Hsiao}}$, deterministic enumeration (`Basis: execution`) confirms that **$59.55\%$** of such 3-bit burst errors are **falsely "corrected" as single-bit `CE`s into Silent Data Corruption** (`47.97%` flipping a 4th data bit; `11.59%` flipping a rank check bit to bless the 3-bit data corruption), while only **$40.45\%$** raise `UE`!
3. **DDR5 `x4` 64-Bit `BL16` Internal Read-Modify-Write (`RMW`) Companion Corruption:** On a DDR5 `x4` device, one external `BL16` burst transfers $16 \times 4 = 64$ bits—**exactly half** of the 128-bit internal OD-ECC codeword. Every normal 64-bit cache-line write to half $A$ of a `x4` codeword therefore forces an internal DRAM Read-Modify-Write: fetch `[A_old, B_old, P_old]` (136 bits), run the `[136, 128, 3]` SEC decoder, overwrite $A \leftarrow A_{\text{new}}$, recompute 8-bit OD-ECC parity $P_{\text{new}}$, and write back. If untouched companion cache line $B_{\text{old}}$ has accumulated a 2-bit retention error whose syndrome matches a third column $b_3$ in $B$, the write to $A$ **permanently writes a 3-bit corrupted `B'` with fresh valid OD-ECC parity `P_new` back to the DRAM array**! Note that if $B$ was never rewritten via the host memory controller, $B$'s side-band *rank* Chipkill parity on the other 9 `x4` chips still reflects clean `B_clean`, so a single-symbol Chipkill `[10, 8, 3]` rank code can still recover $B_{\text{clean}}$ **provided all 9 sibling dies remain error-free**—whereas if any second die develops a simultaneous 1-bit fault, the 2-symbol error exceeds $t = \lfloor(3-1)/2\rfloor = 1$.
4. **Telemetry Blindness vs. `ECS` Thresholds in `mchehab/rasdaemon`:** `rasdaemon`'s `ras-mc-handler.c:132-148` triggers `mc_ce_stat_threshold` page-offlining alerts strictly on memory-controller `Corrected` `mc_event` tracepoints. Because in-DRAM OD-ECC suppresses host-visible `CE`s until a cell cluster exceeds 1 bit per 136-bit word, degrading DDR5 rows remain invisible to `mc_event` unless firmware/OS explicitly routes JEDEC `JESD79-5` Error Check and Scrub (`ECS`) threshold interrupts (`SMCA_UMC` extended error codes `XEC=8` `"ECS Row Error"` and `XEC=9` `"ECS Error"` in `rasdaemon/events-arch-x86/mce-amd-smca.c:322-323`).

---

### 4. Erasures-vs-Errors Silent Amplification and the RAID-5/6 Parity Write-Hole

`Basis: source + execution + derived`

#### 4.1 Located Erasures vs. Unflagged Errors in Linear Parity Reconstruction

An $[n, k, d = p + 1]$ MDS Reed-Solomon code corrects $e$ **located erasures** and $t$ **unflagged symbol errors** simultaneously if and only if:

$$2t + e \le d - 1 = p$$

Standard storage reconstruction APIs (`intel/isa-l` `ec_encode_data` with inverted survivor submatrix `gf_invert_matrix`, and `klauspost/reedsolomon` `Reconstruct` / `ReconstructData` in `reedsolomon.go:61-78`, whose doc comment explicitly warns: *"The reconstructed shard set is complete, but integrity is not verified"*) assume **$t = 0$**: they select *any* $k$ non-missing shards $S = \{i_1, \dots, i_k\}$, compute $G_S^{-1}$, and set $\hat{m} = G_S^{-1} y_S$.

- **Silent Error Amplification Witness (`Basis: execution`):** Consider $(k=4, p=4)$ Cauchy RS (`gf_gen_cauchy1_matrix`, $d = 5$) encoding $m = [\mathtt{0x10}, \mathtt{0x20}, \mathtt{0x30}, \mathtt{0x40}]$. Suppose shard 0 is lost ($e = 1$ erasure) and shard 1 suffers an unflagged 1-byte silent bit-rot $\mathtt{0x20} \to \mathtt{0xdf}$ ($t = 1$ unknown error, $\Delta_1 = \mathtt{0xff}$). Since $2(1) + 1 = 3 \le 4 = p$, the true message $m$ is **uniquely determined** across the 7 present shards $\{1..7\}$, and syndrome-consistent / Welch-Berlekamp decoding uniquely pinpoints shard 1 as corrupt and recovers $[\mathtt{0x10}, \mathtt{0x20}, \mathtt{0x30}, \mathtt{0x40}]$. By contrast, linear erasure reconstruction from the first $k = 4$ present shards $\{1, 2, 3, 4\}$ computes $\hat{m} = [\mathtt{0xdc}, \mathtt{0xdf}, \mathtt{0x30}, \mathtt{0x40}]$—**amplifying shard 1's unflagged corruption into newly reconstructed shard 0 (`0x10 -> 0xdc`)**! If the repair pipeline then re-encodes missing parities from $\hat{m}$, the corrupted vector becomes a valid MDS codeword ($H \hat{c} = 0$), erasing all algebraic evidence of the fault.
- **Linux MD RAID-6 `repair` Destroys Valid Locating Syndromes (`drivers/md/raid5.c:4533-4563`):** Although RAID-6 maintains two independent syndromes ($P = \bigoplus_j D_j$ and $Q = \bigoplus_j g^j D_j$, minimum distance $d = 3$, capable of locating a single unflagged data-disk error via $S_Q \cdot S_P^{-1} = g^j$ when $s.\text{failed} = 0$), `handle_parity_checks6` in `drivers/md/raid5.c:4542-4563` does **not** perform syndrome error localization during `sync_action = repair` (`!MD_RECOVERY_CHECK`). Instead, whenever `zero_sum_result` flags `SUM_CHECK_P_RESULT` or `SUM_CHECK_Q_RESULT`, it unconditionally sets `R5_Wantcompute` on `pd_idx` and `qd_idx`, **overwriting `P` and `Q` from the corrupted data disk** (`check` mode at `lines 4534-4541` only increments `resync_mismatches` without repairing). End-to-end cryptographic or CRC-32C/XXH64 per-block checksums stored out-of-band (turning every unflagged corruption into a **located erasure** $t \to 0, e \to e+1$) double the effective fault tolerance of every parity shard from $\lfloor p/2 \rfloor$ to $p$.

#### 4.2 The RAID-5/6 Write-Hole and Partial Parity Log (`PPL`) Guarantees vs. Limits

When a sub-stripe write updates $D_0 \to D_0'$ on an $n$-disk RAID-5 stripe $(D_0, D_1, \dots, D_{k-1}, P)$ without atomic multi-disk write commit, a power loss after $D_0'$ reaches non-volatile media (or while $D_0$ is torn to $D_0^{\text{torn}}$) but before $P' = D_0' \oplus \bigoplus_{j=1}^{k-1} D_j$ is persisted leaves a nonzero stripe discrepancy $\Delta = D_0^{\text{disk}} \oplus \left(\bigoplus_{j=1}^{k-1} D_j\right) \oplus P_{\text{old}} \neq 0$. The hazard is **cross-disk collateral corruption**: if an **unrelated, unmodified disk $D_m$ ($m \ge 1$)** subsequently fails, degraded reconstruction computes:

$$\hat{D}_m = D_0^{\text{disk}} \oplus \left(\bigoplus_{j \notin \{0, m\}} D_j\right) \oplus P_{\text{old}} = D_m \oplus \Delta \neq D_m$$

corrupting filesystem blocks or metadata on $D_m$ that were never open for writing at crash time.

Linux MD's **Partial Parity Log (`PPL`, `drivers/md/raid5-ppl.c`)** closes this collateral write-hole for RAID-5 without journaling full data blocks:
1. **Pre-Write Partial Parity Logging (`raid5-ppl.c:158-203, 253-254`):** Before issuing stripe data+parity writes, `ops_run_partial_parity` computes $\text{PP} = \bigoplus_{u \notin W} D_u$—the XOR of all **unmodified** chunks in the stripe (via prexor copy in Read-Modify-Write mode at `lines 174-180`, or `async_xor` of unmodified `R5_UPTODATE` pages in Reconstruct-Write mode at `lines 181-187`)—and writes `ppl_header` + `PP` protected by `crc32c_le` (`line 1001`) with `REQ_OP_WRITE | REQ_FUA` (`line 254`) to the parity disk's dedicated PPL ring.
2. **Crash Recovery (`ppl_recover_entry`, `raid5-ppl.c:860-950`):** After an unclean shutdown, for every valid CRC-verified PPL entry, recovery reads whatever bytes $D_w^{\text{disk}}$ currently reside on the modified disks $w \in W$, XORs them with logged `PP`, and writes $P_{\text{recovered}} = \left(\bigoplus_{w \in W} D_w^{\text{disk}}\right) \oplus \text{PP}$ to `parity_rdev`. Because $\text{PP} = \bigoplus_{u \notin W} D_u$, $P_{\text{recovered}}$ is **algebraically consistent with on-disk data** even if $D_w^{\text{disk}}$ was partially torn; a subsequent failure of any unmodified disk $u \notin W$ reconstructs $D_u$ bit-identically.
3. **Three Residual Hazards Not Closed by `PPL`:**
   - *Modified-chunk tear:* `PPL` restores parity consistency ($P_{\text{recovered}}$ matches $D_w^{\text{disk}}$), *not* write atomicity of $D_w$ itself; upper filesystems still require CoW or data journaling if $D_w$ was overwritten in place.
   - *Simultaneous crash + modified-disk loss (`raid5-ppl.c:884-890`):* If a modified disk $w \in W$ is already missing (`!rdev`) during `ppl_recover_entry`, `update_parity` aborts (`update_parity = false; break;`) because `PP` alone lacks $D_w^{\text{disk}}$. Closing this joint fault requires full data+parity write-ahead journaling (`raid5-cache.c` `r5c`) or CoW full-stripe allocation (ZFS RAIDZ).
   - *RAID-6 Inapplicability:* `PPL` stores only a single unweighted XOR partial parity `PP` and cannot reconstruct the weighted $\mathrm{GF}(2^8)$ `Q` partial syndrome $\bigoplus_{u \notin W} g^u D_u$.

## Boundaries

- **`not examined` — `GF(2^16)` FFT (`Leopard`) SIMD Kernels and Non-x86 Vector Backends:** While `klauspost/reedsolomon`'s `leopardFits` (`reedsolomon.go:237-251`) and `intel/isa-l`'s `aarch64`/`riscv64`/`ppc64le` subdirectories were noted for shard-count limits ($n > 256$), their NEON `tbl` / RVV `vrgather` assembly implementations and cache-timing characteristics were **not examined**.
- **`unknown` — Vendor-Proprietary DDR5 On-Die Parity-Check Permutations Across Die Revisions:** While `JESD79-5` fixes the `[136, 128]` codeword size and `BEER` (`Patel et al., MICRO 2020`) demonstrates how to infer vendor $H_{\text{OD}}$ matrices from retention failures, individual DRAM vendors keep exact column permutations of $H_{\text{OD}}$ proprietary and vary them across die steppings. The *total* 2-bit miscorrection count across all $\binom{136}{2} = 9{,}180$ bit pairs in any full-rank `[136, 128, 3]` code depends on the weight-3 codeword spectrum of $H_{\text{OD}}$ (within tight narrow bounds around $53\%\text{–}88\%$ depending on whether $H_{\text{OD}}$ restricts columns to odd-weight/shortened subsets or dense binary columns), whereas the *exact* bit-triple mapping on an untested commercial stepping is **unknown** without running `BEER` characterization.
- **`known not to apply` — Assuming Single-Die DDR5 OD-ECC Miscorrection Automatically Defeats Full-Burst Symbol Chipkill:** An attractive stronger claim—that OD-ECC 2-bit-to-3-bit miscorrection inside a single `x4` die *by itself* breaks single-device `[10, 8, d=3]` Reed-Solomon Chipkill on a healthy rank—is **known not to apply** when the rank RS symbol covers the entire `x4` device contribution and all other 9 `x4` dies in the sub-channel are error-free: flipping a 3rd bit inside the *same* faulty `x4` die still leaves Hamming weight 1 in $\mathrm{GF}(2^b)$ symbol space. Multi-symbol failure requires *either* (a) a non-Chipkill `SEC-DED` rank code (`[72, 64, 4]`), (b) a bounded-bit sub-symbol ECC scheme (`DUO`), or (c) latent multi-cell degradation masked by OD-ECC colliding with a second fault on another die.
- **`unsupported` — `PPL` on RAID-6 and `gf_gen_cauchy1_matrix` Beyond $n = 256$ Shards:** Linux MD `PPL` is **unsupported** for RAID-6 arrays (only RAID-5 is supported by `raid5-ppl.c`), and `intel/isa-l`'s `gf_gen_cauchy1_matrix` over $\mathrm{GF}(2^8)$ is algebraically **unsupported** for $m_{\text{ISA-L}} = n > 256$ (where `i ^ j` truncates modulo 256 and produces zero entries without returning an error).

## Evidence

1. **Intel ISA-L $\mathrm{GF}(2^8)$ Tables, `GFNI` Dispatch, and Vandermonde Singularity Limits (`intel/isa-l` @ `af6a939795a967fc7de4256ab40db85c7fc73ffb`):**
   - `include/erasure_code.h:58-120, 1080-1137`: `ec_init_tables`, `ec_encode_data`, `gf_invert_matrix`, and exact safe-region inequalities documented on `gf_gen_rs_matrix`.
   - `erasure_code/ec_base.c:38-115, 176-342`: `gf_mul`, `gf_inv`, `gf_gen_rs_matrix` ($P_{r,c} = 2^{r \cdot c}$), `gf_gen_cauchy1_matrix` (`gf_inv(i ^ j)`), `gf_vect_mul_init_base` (`0x1d` reduction), and `ec_encode_data_base` (`v[j * 32 + l * srcs * 32 + 1]` scalar coefficient extraction).
   - `erasure_code/ec_base.h:35-120`: `gf_table_gfni[256]` (`gf_table_gfni[1] = 0x0102040810204080`) and `gff_base` generator table.
   - `erasure_code/ec_highlevel_func.c:303-506`: `ec_encode_data_avx512` (`len < 64` fallback to `ec_encode_data_base`) vs. `gf_vect_mul_init_gfni`, `ec_init_tables_gfni`, and `ec_encode_data_avx512_gfni`.
   - `erasure_code/ec_multibinary.asm:87-93`, `erasure_code/gf_vect_gfni.inc:34-72`, `erasure_code/gf_vect_dot_prod_avx512.asm:130-230`, `erasure_code/gf_vect_dot_prod_avx512_gfni.asm:120-186`: `vgf2p8affineqb` macro, overlapped `len - 64` non-GFNI tail vs. EVEX `k1` byte-masked GFNI tail.
   - `erasure_code/gen_rs_matrix_limits.c:58-118`: Gosper-hack exhaustive submatrix singularity checker for `gf_gen_rs_matrix`.
2. **Go Reed-Solomon Matrix Builders (`klauspost/reedsolomon` @ `25e5c5227103dc948f3e1888a8c9d62be1bafd1e`):**
   - `reedsolomon.go:59-61, 218-283, 366-414`: unverified-integrity note on `Reconstruct`, `ErrMaxShardNum` ($n \le 256$), `leopardFits`, right-inverted `buildMatrix` ($V \cdot V_{0..k-1}^{-1}$), buggy `buildMatrixPAR1`, and `buildMatrixCauchy`.
   - `matrix.go:192-281`: Gaussian elimination `Invert()` and `vandermonde()`.
3. **Linux Kernel `v6.12` EDAC and MD RAID-5/6 (`torvalds/linux` @ `adc218676eef25575469234709c2d87185ca223a`) & `rasdaemon` (`mchehab/rasdaemon` @ `5e547c331d31e4f47c0fb4204e039a69a1fcf68d`):**
   - `drivers/edac/amd64_edac.c:1354-1402, 1555-1571, 2543-2690`: DDR5 `RDDR5`/`LRDDR5` UMC detection, `x4_vectors`/`x8_vectors` Chipkill eigenvector syndrome search.
   - `drivers/md/raid5.c:4358-4388, 4512-4565`: `handle_parity_checks5` and `handle_parity_checks6` overwriting `P` and `Q` on `!MD_RECOVERY_CHECK`.
   - `drivers/md/raid5-ppl.c:158-203, 253-254, 860-1020`: `ops_run_partial_parity`, `REQ_FUA` PPL commit, `crc32c_le` check, and `ppl_recover_entry` (`!rdev` abort at `lines 884-890`).
   - `mchehab/rasdaemon` `events/ras-mc-handler.c:132-148` and `events-arch-x86/mce-amd-smca.c:313-350`: `mc_event` `CE` threshold logic and `SMCA_UMC` `ECS Row Error` / `ECS Error` (`XEC=8, 9`) descriptors.
4. **Peer-Reviewed Literature & Standards:**
   - J. S. Plank and Y. Ding, "Note: Correction to the 1997 Tutorial on Reed-Solomon Coding," *Software: Practice and Experience*, 35(2):189–194, 2005 (`DOI: 10.1002/spe.631`).
   - J. S. Plank and L. Xu, "Optimizing Cauchy Reed-Solomon Codes for Fault-Tolerant Network Storage Applications," *IEEE NCA 2006*, pp. 173–180 (`DOI: 10.1109/NCA.2006.43`).
   - C. Huang et al., "Erasure Coding in Windows Azure Storage," *USENIX ATC 2012*, pp. 15–26.
   - M. Patel, J. S. Kim, H. Hassan, and O. Mutlu, "Understanding and Modeling On-Die Error Correction in Modern DRAM: An Experimental Study Using Real Devices," *IEEE/IFIP DSN 2019* (`DOI: 10.1109/DSN.2019.00017`), and "Bit-Exact ECC Recovery (BEER)," *IEEE/ACM MICRO-53*, 2020 (`DOI: 10.1109/MICRO50266.2020.00034`).
   - JEDEC Standard `JESD79-5`, *DDR5 SDRAM* (`[136, 128]` On-Die SEC ECC, `BL16` `x4` 64-bit RMW, and Error Check and Scrub `ECS`).
5. **Self-Contained Executable Algebraic Probe (`observed_at: 2026-11-19`, Python 3.12+ standard library only):**
   Running the standalone script in **Revalidation** below deterministically verifies:
   - Exact bit-level match between `VGF2P8AFFINEQB` matrix synthesis and `intel/isa-l`'s `gf_table_gfni`, plus `tbl_gfni[1] == 0x40` for $c = 1$;
   - Singular $3 \times 3$ minors in `gf_gen_rs_matrix` at $(k=6, p=5)$ (`[[1, 1, 1], [1, 8, 32], [1, 205, 180]]`) and $(k=22, p=4)$ (`[[1, 1, 1], [1, 116, 117], [1, 96, 161]]`), `PARv1` singularity at $(k=3, p=4)$, and `gf_gen_cauchy1_matrix` nonsingularity vs. $n = 257$ zero entry;
   - `(12, 2, 2)` LRC `560/560` 3-erasure recovery and `1568/1568` (`100%`) Maximally Recoverable 4-erasure recovery under disjoint-nibble cosets vs. failure under sequential `1..12` points;
   - Silent error amplification (`['0x10', '0x20', '0x30', '0x40'] -> ['0xdc', '0xdf', '0x30', '0x40']`) vs. exact syndrome localization (`bad_shard = 1`);
   - `8109/9180` (`88.33%`) 2-bit-to-3-bit miscorrection in `[136, 128, 3]` SEC OD-ECC and `59.55%` (`47.97%` data + `11.59%` check) Silent Data Corruption in balanced `[72, 64, 4]` Hsiao rank SEC-DED.

## Revalidation

1. **Self-Contained Algebraic & Syndrome Revalidation Probe (< 1 second, Python 3.10+ stdlib only):**
   Run the following self-contained command to re-verify all $\mathrm{GF}(2^8)$, `GFNI`, Vandermonde/Cauchy, `(12, 2, 2)` MR-LRC, error-amplification, and `[136, 128, 3]` $\to$ `[72, 64, 4]` ECC aliasing claims:

```bash
python3 - <<'EOF'
from itertools import combinations

PRIM = 0x11D
EXP, LOG = [0] * 512, [0] * 256
v = 1
for i in range(255):
    EXP[i] = EXP[i + 255] = v
    LOG[v] = i
    v = (v << 1) ^ (PRIM if (v & 0x80) else 0)

gf_mul = lambda a, b: 0 if (a == 0 or b == 0) else EXP[LOG[a] + LOG[b]]
gf_inv = lambda a: 0 if a == 0 else EXP[255 - LOG[a]]
gf_pow = lambda a, n: 1 if n == 0 else (0 if a == 0 else EXP[(LOG[a] * n) % 255])

def gf_rank(mat):
    m = [row[:] for row in mat]
    rows, cols, r = len(m), len(m[0]), 0
    for c in range(cols):
        piv = next((i for i in range(r, rows) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv_p = gf_inv(m[r][c])
        for j in range(c, cols):
            m[r][j] = gf_mul(m[r][j], inv_p)
        for i in range(rows):
            if i != r and m[i][c]:
                f = m[i][c]
                for j in range(c, cols):
                    m[i][j] ^= gf_mul(f, m[r][j])
        r += 1
        if r == rows:
            break
    return r

def gfni_u64(c):
    mtx = 0
    for j in range(8):
        p = gf_mul(c, 1 << j)
        for i in range(8):
            if (p >> i) & 1:
                mtx |= (1 << j) << (8 * (7 - i))
    return mtx

assert gfni_u64(1) == 0x0102040810204080 and ((gfni_u64(1) >> 8) & 0xFF) == 0x40
assert gf_rank([[gf_pow(EXP[r], c) for c in (0, 3, 5)] for r in (0, 1, 4)]) == 2
assert gf_rank([[gf_pow(EXP[r], c) for c in (0, 10, 21)] for r in (0, 1, 3)]) == 2
assert gf_rank([[gf_inv((6 + r) ^ c) for c in (0, 3, 5)] for r in (0, 1, 4)]) == 3

pts = [1, 2, 3, 4, 5, 6, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60]
G_mr = [[int(r == c) for c in range(12)] for r in range(12)] + [
    [int(c < 6) for c in range(12)], [int(c >= 6) for c in range(12)],
    pts, [gf_mul(x, x) for x in pts],
]
dec4 = sum(1 for er in combinations(range(16), 4)
           if gf_rank([G_mr[i] for i in range(16) if i not in er]) == 12)
assert dec4 == 1568

pow2 = {1 << b for b in range(8)}
od_cols = [x for x in range(1, 256) if x not in pow2][:128] + [1 << b for b in range(8)]
od_map = {c: i for i, c in enumerate(od_cols)}
mis2 = sum(1 for i, j in combinations(range(136), 2) if (od_cols[i] ^ od_cols[j]) in od_map)
assert mis2 == 8109
print("ALL GF(2^8) / GFNI / LRC / OD-ECC CHECKS PASSED:", {"dec4_mr": dec4, "od_mis2": mis2})
EOF
```

2. **Upstream Source Diff Anchors When Updating Pinned Revisions:**
   - In `intel/isa-l`, diff `erasure_code/ec_multibinary.asm` and `erasure_code/ec_highlevel_func.c` (`gf_vect_mul_init_gfni` vs. `ec_encode_data_base`) to check whether `g_tbls` gains a magic/format tag or bounds check on `gf_gen_cauchy1_matrix` (`m <= 256`).
   - In `torvalds/linux`, diff `drivers/md/raid5.c` (`handle_parity_checks6`) to check whether `!MD_RECOVERY_CHECK` ever adds single-disk `Q/P` syndrome localization, and diff `drivers/edac/amd64_edac.c` / `mchehab/rasdaemon` (`mce-amd-smca.c`) for DDR5 `ECS` event promotion to page-retirement triggers.
