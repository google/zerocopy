# Succinct Run-Length FM-Indexes, Minimizer-Chained SIMD Alignment, and Bidirected Pangenome Graph Coordinates

## Summary

Scaling sequence indexing and alignment from a single haploid reference genome ($N \approx 3.1 \times 10^9$ bp) to population-scale pangenomes ($H > 10^3$ phased haplotypes) hinges on three algorithmic and representation transitions—each carrying sharp bit-width, algebraic, and coordinate-orientation invariants:

1. **From $O(n/s)$ Regular `FM-Index` Sampling to $O(r)$ Run-Length `r-index` $\Phi$-Locating (`nicolaprezza/r-index`):** Classical Burrows–Wheeler `FM-Index` structures (`LF(i) = F[c] + rank_c(BWT, i)`) compress `count` queries on repetitive collections via run-length `BWT` (`RLBWT`), yet still require $\Omega(n/s)$ words of suffix-array (`SA`) samples to bound `locate` latency to $O(s)$ backward `LF` steps. In `nicolaprezza/r-index` (`internal/r_index.hpp:92–147, 195–221, 482–625`), sampling **only the $2r$ text positions `(SA[q] - 1) mod n` at the first and last characters of the $r$ equal-letter `BWT` runs** maintains `SA[R]` inductively during backward search and recovers all remaining occurrences $\mathrm{SA}[R-1 \dots L]$ via a circular Elias–Fano predecessor $\Phi(\mathrm{SA}[q]) = \mathrm{SA}[q-1]$ in **$O(r)$ words and $O(\log(n/r))$ time per occurrence**—while hard-aborting (`exit(1)`) if input bytes contain reserved `0x00` or `0x01` (`TERMINATOR`).
2. **From Seed-and-Extend to $(w, k)$-Minimizer Chaining and 8-Bit Difference-Recurrence SIMD DP (`lh3/minimap2`):** `minimap2` achieves expected Winnowing sketch density $\frac{2}{w+1}$ (`sketch.c:77–143`) via an invertible 64-bit integer mixer (`hash64`), chained by concave-gap dynamic programming (`lchain.c:113–217`) or an exact $O(n \log n)$ 1D Range-Maximum-Query tree (`mg_lchain_rmq`, `lchain.c:250–305`) and aligned across anti-diagonals via the **Suzuki–Kasahara 8-bit difference recurrence** (`ksw2_extz2_sse.c:34–231`). Primary-source inspection and execution expose four hard boundaries: (a) **even-$k$ Watson–Crick palindromic $k$-mers (`kmer[0] == kmer[1]`) are unconditionally skipped** (`sketch.c:108`), blinding even-$k$ indexes to `(AT)_m` dinucleotide satellites; (b) homopolymer-compressed (`HPC`) $k$-mers spanning $\ge 256$ raw bases are silently dropped (`kmer_span < 256`, `sketch.c:111`); (c) high-occurrence centromeric seeds require `mm_seed_select`'s $L = 500$ bp binomial-heap rescue (`seed.c:56–96`) and RMQ rechaining to avoid inner-loop `max_skip` early-exit breaks; and (d) Suzuki–Kasahara's 16-lane SSE kernel wraps signed `int8_t` `_mm_max_epi8` whenever **$M + 2(q + e) > 127$** (`ksw2_extz2_sse.c:78, 163`) or aborts silently when $-\min s > 2(q + e)$ (`L90`).
3. **Bidirected Handle Involutions, `Snarl` Cactus Coordinates, and Forward-`LF` `GBWT` Haplotype Pruning (`vgteam/vg` + `jltsiren/gbwt`):** Pangenome variation graphs model double-stranded DNA via a fixed-point-free orientation involution (`gbwt::Node::encode(id, rev) = (id << 1) | rev`, `reverse(x) = x ^ 1`, `gbwt/support.h:23–31`), decomposed hierarchically into alternating `Chain` and `Snarl` (ultrabubble) trees via 3-edge-connected Cactus graphs (`vg/src/snarls.hpp:87–270`, `cactus_snarl_finder.cpp:25–209`) with **inward-facing `start` and outward-facing `end` `Visit` handles**. Unlike string `FM-Index`es where `LF` steps *backward*, `GBWT` (`SERIALIZATION.md:200–225`, `gbwt.h:192–245`) is a **multi-string reverse-prefix BWT** partitioned into per-node records whose `LF(v, j)` steps **forward** along phased haplotypes, pruning $1 - H / 2^B$ (>99%) of biologically nonexistent chimeric recombinations across $B$ adjacent variant bubbles.

## Applicability

This report characterizes the exact data structures, bit-level invariants, serialize formats, and algorithmic boundaries of the four pinned upstream revisions in `REPORT.json`:

- **`nicolaprezza/r-index` (`7009b5374282aa1d8e9b594d0a06c49a0bc1330f`):** Applies to byte-alphabet (`uchar`, `0x02..0xFF`) lossless full-text `count` and `locate` indexing (`r_index<sparse_sd_vector, rle_string_sd>`) built atop `sdsl-lite` (`SE-SAIS` or `libdivsufsort`).
- **`lh3/minimap2` (`3c28777e7e2dcc90f825de1b9f17a89cca7d4452`):** Applies to `minimap2` C11 library and CLI presets (`map-ont`, `map-hifi`, `map-pb`, `sr`, `splice`, `asm5`/`asm20`) across x86 SSE2/SSE4.1 and ARM NEON (`sse2neon` / `SIMDe`), covering `mm_sketch`, `mm_seed_select`, `mg_lchain_dp`, `mg_lchain_rmq`, and `ksw_extz2_sse` / `ksw_extd2_sse`.
- **`vgteam/vg` (`6f11d25de4d2466382b22225b74e16e4e4e9b74b`) & `jltsiren/gbwt` (`14a06d588ea6de50cd809f546b9bb57c92c15ac1`):** Applies to `libhandlegraph`-backed bidirected sequence graphs (`HandleGraph`, `PathPositionHandleGraph`), `CactusSnarlFinder` / `SnarlManager` / `NetGraph` hierarchical site decompositions, and `GBWT` Simple-SDS version 6 (`.gbwt` magic tag `0x6B376B37`, Zstandard-compressed per-node RLE records) as integrated in `vg` (`gbwt_helper.hpp` and `vg giraffe`).

Together, these four systems trace the progression of genomic indexing from static single-sequence Burrows–Wheeler transforms (`FM-Index`) to run-compressed repetitive collection indexes (`r-index`), fast approximate linear/long-read seed-chain-align pipelines (`minimap2`), and haplotype-constrained bidirected graph indexes (`vg` + `GBWT`).

## Findings

### 1. Succinct `FM-Index` `LF`-Mapping vs. Run-Length `r-index` $\Phi$-Predecessor Locating

#### 1.1 `RLBWT` Block-Sampled Rank/Select Representation (`rle_string.hpp`)
`Basis: source + derived`

Let $T[0..n-2]$ be a text over alphabet $\Sigma$ ($|\Sigma| = \sigma \le 254$) terminated by unique sentinel `$ = 0x01 < \min \Sigma` at $T[n-1]$, with suffix array $\mathrm{SA}[0..n-1]$ and Burrows–Wheeler Transform $\mathrm{BWT}[q] = T[(\mathrm{SA}[q] - 1) \bmod n]$. Ferragina and Manzini (*J. ACM* 2005, `DOI: 10.1145/1082036.1082039`) showed that Last-to-First (`LF`) mapping:
$$\mathrm{LF}(q) = F[c] + \mathrm{rank}_c(\mathrm{BWT}, q), \qquad c = \mathrm{BWT}[q]$$
satisfies $\mathrm{SA}[\mathrm{LF}(q)] = (\mathrm{SA}[q] - 1) \bmod n$ and updates pattern suffix range $[L, R]$ for $cP$ via $[F[c] + \mathrm{rank}_c(\mathrm{BWT}, L),\; F[c] + \mathrm{rank}_c(\mathrm{BWT}, R + 1) - 1]$.

On $H$ highly similar genomes of length $N_0$ ($n = H \cdot N_0$ with per-haplotype divergence $\mu \ll 1$), equal suffixes across haplotypes coalesce contiguously in $\mathrm{SA}$, collapsing $\mathrm{BWT}$ into $r \ll n$ maximal equal-letter runs ($r = O(N_0 + H \cdot \mu N_0 \log N_0)$). In `nicolaprezza/r-index` (`internal/rle_string.hpp:36–218`), `rle_string<sparse_sd_vector, huff_string>` stores $\mathrm{BWT}$ in **$r(H_0 + \log_2(n/r) + \frac{1}{B}\log_2(n/r))(1 + o(1))$ bits** (default block size $B = 2$, `L52`) using three Elias–Fano (`sdsl::sd_vector`) and wavelet-tree components:
- `run_heads` (`huff_string` Huffman-shaped wavelet tree of length $r$): stores the single head character $c_k$ of each run $k \in [0, r)$, supporting $O(H_0)$ `rank` and `select`;
- `runs` (`sparse_sd_vector` of length $n$ with $\lfloor r / B \rfloor$ `1`-bits): sets a `1`-bit at the last text index of every $B$-th run (`runs_bv.push_back(R % B == B - 1)`, `L78`); and
- `runs_per_letter[256]`: per-symbol `sparse_sd_vector` over the concatenated $c$-runs ONLY (setting `1` at the end of each $c$-run, `L73, 85`), converting run-head rank `rk = run_heads.rank(current_run, c)` directly into cumulative character count via `runs_per_letter[c].select(rk - 1) + 1 + tail` (`L207–216`) in $O(B(\log(n/r) + H_0))$ time.

#### 1.2 The `r-index` $2r$ Shifted-Sample Invariant and Circular $\Phi$ Predecessor (`r_index.hpp`)
`Basis: source + execution`

Classical `RLCSA`/`FM-Index` designs sample $\mathrm{SA}[q]$ every $s$ text positions (`SA[q] % s == 0`), requiring $\frac{n}{s}\log_2 n$ bits. Restricting space to $O(r)$ words forces $s = \Theta(n/r)$, inflating per-occurrence `locate` latency to $\Theta(n/r)$ cache-missing wavelet-tree `LF` steps.

Gagie, Navarro, and Prezza (*J. ACM* 2020, `DOI: 10.1145/3375890`) broke this space–time barrier. Inspection of `internal/r_index.hpp:107–148, 195–221, 482–625` reveals an implementation detail essential for reproducing the structure without off-by-one errors: **`sufsort` (`L599, 604, 614, 619`) does NOT store $\mathrm{SA}[q]$ at run boundaries—it stores $(\mathrm{SA}[q] - 1) \bmod n$**, the text index of $\mathrm{BWT}[q]$ itself!

1. **Inductive Maintenance of $k = \mathrm{SA}[R]$ During Backward Search (`count_and_get_occ`, `L482–544`):**
   - Initially, `[L, R] = [0, n - 1]` and `k = (samples_last[r - 1] + 1) % n` (`L489`), which equals $\mathrm{SA}[n - 1]$ because `samples_last[r - 1]` stores $(\mathrm{SA}[n - 1] - 1) \bmod n$.
   - Before extending `[L, R]` left by character `c` (`range1 = LF(range, c)`):
     - **Case A (`bwt[R] == c`, `L505–510`):** Position $R$ is itself the last `c` in `[L, R]`, so $R_1 = \mathrm{LF}(R)$ and $\mathrm{SA}[R_1] = \mathrm{SA}[R] - 1 = k - 1$ (`assert(k > 0); k--;`).
     - **Case B (`bwt[R] != c`, `L511–535`):** Let $j < R$ be the last occurrence of `c` in `[L, R)` (`rnk = bwt.rank(R, c); j = bwt.select(rnk - 1, c)`). Because `j < R` and `bwt[j + 1]` cannot be `c` (otherwise `j` would not be the last `c` strictly before $R$), **index `j` is guaranteed to be the final character of a `BWT` run**! Therefore `samples_last[bwt.run_of_position(j)]` holds $(\mathrm{SA}[j] - 1) \bmod n = \mathrm{SA}[\mathrm{LF}(j)] = \mathrm{SA}[R_1]$, assigned directly via `k = samples_last[run_of_j]` (`L533`, *without* decrementing!).
2. **Extracting $\mathrm{SA}[R-1], \dots, \mathrm{SA}[L]$ via $\Phi$ (`L195–221, 328–355`):**
   Define $\Phi(\mathrm{SA}[q]) = \mathrm{SA}[q - 1]$ for $q > 0$. If $\mathrm{BWT}[q] = \mathrm{BWT}[q - 1]$ (same run), LF-monotonicity implies $\mathrm{LF}(q) = \mathrm{LF}(q - 1) + 1$, so $\mathrm{SA}[q] - 1$ and $\mathrm{SA}[q - 1] - 1$ maintain offset $+1$. Thus the shift $\Phi(i) - i$ changes **only when $q$ is the start of a `BWT` run**, i.e., at the $r$ text positions stored in `pred` (`samples_first`, sorted by text offset)! For any $i = \mathrm{SA}[q] \ne n - 1$, `r_index::Phi(i)` (`L195–221`) queries the **strict circular predecessor** (`sparse_sd_vector.hpp:153–157`, `rank(i) == 0 ? r - 1 : rank(i) - 1`, *excluding* `i`):
   $$j_r = \mathrm{pred.predecessor\_rank\_circular}(i), \quad j = \mathrm{pred.select}(j_r), \quad \Delta = \begin{cases} i - j & \text{if } j < i \\ i + 1 & \text{if } j \ge i \text{ (wraparound } j = n - 1\text{)} \end{cases}$$
   $$\Phi(i) = \big(\mathrm{samples\_last}[\mathrm{pred\_to\_run}[j_r] - 1] + \Delta\big) \bmod n$$
   Probe 2A (`## Evidence`) confirms 100% exact locating across 30 multi-haplotype queries (`925` occurrences) and demonstrates that as haplotype count scales $16\times$ (`H = 8 -> 128`, `n = 8,008 -> 128,128`), `r` grows only $2.77\times$ (`833 -> 2,304`, $n/r = 55.61\times$), keeping `r-index` at `< 1.0` $\Phi$-evaluations per hit while an equal-sample-budget classical `FM-Index` degrades linearly from `2.12` to `13.47` `LF` steps/hit.
3. **Reserved-Byte Input Precondition (`r_index.hpp:46–50, 636–644`):** `sdsl::construct_sa<8>` reserves `0x00` for internal string termination (`append_zero_symbol(text)`, `L567`), while `r_index` reserves `0x01` as `TERMINATOR` (`L646`). Passing binary inputs or 2-bit packed DNA containing `0x00` or `0x01` triggers `contains_reserved_chars(input)` -> `exit(1)`.

---

### 2. $(w, k)$-Minimizer Sketching, Chaining, and 8-Bit SIMD Alignment (`minimap2`)

#### 2.1 Symmetric $(w, k)$-Minimizers, Even-$k$ Palindrome Blindness, and `HPC` Span Drops (`sketch.c`)
`Basis: source + execution`

In `lh3/minimap2` (`sketch.c:28–143`; Li, *Bioinformatics* 2018, `DOI: 10.1093/bioinformatics/bty191`), `mm_sketch` extracts canonical strand-symmetric $(w, k)$-minimizers into 128-bit `mm128_t` anchors:
$$\texttt{p->a[i].x} = (\mathrm{hash64}(\min(k_{\text{fwd}}, k_{\text{rev}}),\; 2^{2k}-1) \ll 8) \;\mid\; \mathrm{kmer\_span}, \qquad \texttt{p->a[i].y} = (\mathrm{rid} \ll 32) \;\mid\; (\mathrm{lastPos} \ll 1) \;\mid\; z$$
where $z = \mathbf{1}[k_{\text{rev}} < k_{\text{fwd}}] \in \{0, 1\}$ records the canonical strand. Under uniform random 64-bit hashes (achieved via Thomas Wang's invertible bit-mixer `hash64`, `sketch.c:28–38`, preventing poly-`A` `0x0000` clustering), Schleimer, Wilkerson, and Aiken (*SIGMOD* 2003, `DOI: 10.1145/872757.872770`) proved expected density $\frac{2}{w + 1}$ (verified in Probe 2B for $w = 10, k = 15$: empirical `0.18383` vs. $\frac{2}{11} = 0.18182$).

Direct inspection of `sketch.c` reveals three sharp representation limits:
1. **Hard Parameter Ceilings (`sketch.c:43, 84, 111`):** `assert(len > 0 && (w > 0 && w < 256) && (k > 0 && k <= 28))` enforces $2k \le 56$ bits (leaving 8 low bits in `info.x` for `kmer_span`), and `tiny_queue_t` uses a fixed 32-slot ring (`int a[32]`, masked with `& 0x1f`, `L47, 55`), relying on $k \le 28 < 32$.
2. **Unconditional Skipping of Self-Reverse-Complement $k$-mers (`sketch.c:108`):** Line 108 executes:
   ```c
   if (kmer[0] == kmer[1]) continue; // skip "symmetric k-mers" as we don't know it strand
   ```
   When $k$ is **odd**, $k_{\text{fwd}} \ne k_{\text{rev}}$ for all $4^k$ oligomers because the central base $(k-1)/2$ complements (`A <-> T`, `C <-> G`). When $k$ is **even** (e.g., short-read or splice presets, or custom `-k 14`/`-k 16`), Watson–Crick palindromes satisfy `kmer[0] == kmer[1]`—and Notice that `++l` (`L110`) is **not even executed** before `continue`! Consequently, a pure dinucleotide tandem repeat such as `(AT)_{200}` (400 bp) yields **zero minimizers** for *any* even $k$ (verified in Probe 2B: `0` minimizers at $k = 14$ vs. `385` tied minimizers at $k = 15$).
3. **Homopolymer-Compressed (`HPC`) Span $\ge 256$ Silent Drop (`sketch.c:94–114`):** Under `is_hpc = 1` (used in `map-pb` / PacBio presets), homopolymer runs collapse to 1 base while `tq` accumulates raw run lengths into `kmer_span`. Line 111 guards `if (l >= k && kmer_span < 256)`; if an HPC $k$-mer spans $\ge 256$ raw bases (e.g., a 260 bp poly-`A` tract), `info.x` stays `UINT64_MAX`, silently dropping all windows spanning that run (Probe 2B).

#### 2.2 Repetitive Centromeric Masking, `mm_seed_select` Rescue, and Banded DP vs. 1D RMQ Chaining (`seed.c`, `lchain.c`)
`Basis: source + documentation`

Early `minimap2` ($\le$ v2.18) discarded all minimizers whose reference occurrence count exceeded `mid_occ` (`-f 0.0002`, typically a few hundred hits in human GRCh38/CHM13), leaving reads inside alpha-satellite centromeric arrays with zero anchors. In `seed.c:56–96` (`Li, Bioinformatics 2021`, `DOI: 10.1093/bioinformatics/btab705`), `mm_seed_select` scans contiguous streaks `(st..en)` of masked high-occurrence query minimizers spanning query bases `[ps, pe]` and rescues up to `max_high_occ = min(128, round((pe - ps) / dist))` (default `dist = L = 500` bp) lowest-frequency seeds (still capped by `max_max_occ`, `L90–91`) using a fixed 128-element stack-allocated max-heap `uint64_t b[128]`.

To chain sorted anchors $a_j = (r_j, q_j)$ into colinear chains, `comput_sc` (`lchain.c:113–138`) applies a **concave logarithmic + linear gap penalty** over diagonal difference $d_d = |\Delta r - \Delta q|$ and minimum advance $d_g = \min(\Delta r, \Delta q)$:
$$f[i] = \max_{j < i} \Big\{\, f[j] + \min(q_{\text{span}}(i),\, d_g) - \Big\lfloor c_{\text{gap}} \cdot d_d + c_{\text{skip}} \cdot d_g + \frac{1}{2}\log_2(d_d + 1) \Big\rfloor \,\Big\}$$
(with `is_cdna` splice mode replacing $c_{\text{gap}} d_d + c_{\text{skip}} d_g + 0.5\log_2(d_d + 1)$ by $\min(\text{lin\_pen}, \text{log\_pen})$ on reference deletions $\Delta r > \Delta q$, `L131–134`). Two solvers coexist in `lchain.c`:
- **Heuristic Banded Predecessor Loop (`mg_lchain_dp`, `lchain.c:148–217`):** Scans $j = i - 1$ down to `st` (`r_i - r_st <= max_dist_x` and `i - st <= max_iter`), breaking early once `max_skip` (`25` by default) previously chained predecessors fail to improve `max_f` (`if (++n_skip > max_skip) break;`, `L182–184`). Inside tandem copy-number variations, 25+ suboptimal repeat copies trigger this early exit and fracture long chains (`tex/mm2-update.tex:87–91`).
- **Exact $O(n \log n)$ 1D RMQ Balanced Tree (`mg_lchain_rmq`, `lchain.c:250–368`):** When $c_{\text{skip}} = 0$ and the $\frac{1}{2}\log_2(d_d + 1)$ term is approximated locally via priority key $\mathrm{pri}(j) = -\big(f[j] + \frac{1}{2} c_{\text{gap}}(r_j + q_j)\big)$ (`L285`), anchor chaining reduces to a 1D orthogonal Range-Minimum-Query over $q_j \in [q_i - \mathrm{max\_dist}, q_i)$ in `krmq.h`, eliminating heuristic `max_skip` fractures across 100 kb structural INDELs.

#### 2.3 Suzuki–Kasahara 8-Bit Anti-Diagonal SIMD Recurrence and Signed Wraparound Boundary (`ksw2_extz2_sse.c`)
`Basis: source + execution`

Base-level alignment between chained anchors dominates `minimap2` CPU time (`tex/minimap2.tex:255–257`). Under Gotoh's 2-piece affine gap model $\gamma_a(l) = \min(q + |l|e,\; \tilde{q} + |l|\tilde{e})$, Farrar's striped SSE vectorization drops from 16 lanes (`int8_t`) to 4 lanes (`int32_t`) whenever alignment length exceeds `32,767 / M` bases.

Suzuki and Kasahara (*BMC Bioinformatics* 2018, `DOI: 10.1186/s12859-018-2014-8`) reformulated Gotoh DP over **adjacent score differences** along anti-diagonals $r = i + j$, $t = i$:
$$u_{r,t} = H_{i,j} - H_{i-1,j}, \quad v_{r,t} = H_{i,j} - H_{i,j-1}, \quad x_{r,t} = E_{i+1,j} - H_{i,j}, \quad y_{r,t} = F_{i,j+1} - H_{i,j}$$
All cells $(r, t)$ on anti-diagonal $r$ are **mutually data-independent** (`tex/minimap2.tex:326–329`) and mathematically bounded independent of sequence length:
$$x_{r,t}, y_{r,t} \in [-q - e,\; -e], \qquad u_{r,t}, v_{r,t} \in [-q - e,\; M + q + e]$$
where $M = \max_{a,b} s(a, b)$ is the maximum match score.

Inspection of `ksw2_extz2_sse.c:34–91, 158–205` reveals an additional **unsigned bias shift** and its exact **8-bit overflow cliff**:
- Rather than storing signed $[-q - e, M + q + e]$ directly, `ksw2_extz2_sse.c` shifts $u, v$ by $+(q + e)$ into `[0, M + 2(q + e)]` and shifts $x, y$ by $+(q + e)$ into `[0, q]`, setting `qe2_ = (q + e) * 2` (`L69`) and `max_sc_ = mat[0] + (q + e) * 2` (`L78`).
- **Precondition 1 (Mismatch Floor, `L90`):** `if (-min_sc > 2 * (q + e)) return;` — if the worst mismatch penalty $-X$ is more negative than $-2(q + e)$, `s[t] + qe2_` goes negative, violating non-negativity of `b` in `_mm_max_epu8(z, b)` (`L49`) and causing `ksw_extz2_sse` to **return immediately with an empty alignment (`ez->score = 0`)**!
- **Precondition 2 (Signed `int8_t` Ceiling, `L78, 163, 187`):** On line 163 (`#ifdef __SSE4_1__`), `z = _mm_max_epi8(z, a)` executes a **signed 8-bit comparison** on `z = s[t] + 2(q + e)`! Whenever **$M + 2(q + e) > 127$**, `z` and `max_sc_` wrap to negative `int8_t` values (`[-128, -1]`), causing `_mm_max_epi8(z, a)` to discard matches in favor of `a >= 0` and corrupting reconstructed 32-bit `H[t]` scores! Probe 2B (`## Evidence`) confirms exact Gotoh agreement at default parameters (`M=2, X=4, q=4, e=2` -> $M + 2(q+e) = 14 \le 127$, score `18 == 18`) and catastrophic score corruption (`-220` vs. true `210`) when $M + 2(q+e) = 130 > 127$.

---

### 3. Bidirected Pangenome Variation Graphs (`vg`), `Snarl` Trees, and `GBWT` Haplotype Indexes

#### 3.1 Bidirected Handle Involution and Reverse-Complement Edge Symmetry
`Basis: source + execution`

A bidirected sequence graph $G = (V, E, \ell)$ assigns each node $v \in V$ ($v \ge 1$) a forward nucleotide sequence $\ell(v) \in \{\texttt{A},\texttt{C},\texttt{G},\texttt{T}\}^+$ and two oriented *handles* $(v, 0)$ (forward, $\ell(v)$) and $(v, 1)$ (reverse complement, $\overline{\ell(v)}$). Both `vgteam/vg` (`src/gbwt_helper.hpp:24–46`) and `jltsiren/gbwt` (`include/gbwt/support.h:22–45`) encode handles and bidirectional paths via the bit-packed involution:
$$\mathrm{encode}(v, \mathrm{rev}) = (v \ll 1) \;\mid\; \mathrm{rev}, \qquad \mathrm{reverse}(x) = x \oplus 1, \qquad \mathrm{reversePath}(p_0 \dots p_{k-1}) = (\mathrm{reverse}(p_{k-1}), \dots, \mathrm{reverse}(p_0))$$
Every bidirected edge connecting the exit side of handle $h_1 = (u, d_1)$ to the entry side of handle $h_2 = (v, d_2)$ induces an identical physical DNA adjacency to its reverse-complement twin $(v, \neg d_2) \to (u, \neg d_1)$. Consequently, any traversal algorithm or index that updates `(u, d_1) -> (v, d_2)` without symmetrically maintaining `(v, !d_2) -> (u, !d_1)` breaks strand equivalence—causing the same read sequenced from the `-` strand to receive a different alignment score or mapping coordinate than on the `+` strand.

#### 3.2 Cactus `Snarl` and `Chain` Decomposition Coordinates (`vg/src/snarls.hpp`)
`Basis: source + documentation`

Linear genomic coordinates `(chr, pos)` break down inside nested inversions, structural insertions, and copy-number loops. Paten et al. (*J. Comput. Biol.* 2018, `DOI: 10.1089/cmb.2017.0251`) and `vg` (`src/snarls.hpp:59–270`, `src/cactus_snarl_finder.cpp:25–209`) construct a canonical site hierarchy by contracting each node's two sides `{start, end}` into a Cactus graph (`handle_graph_to_cactus`, `cactus_snarl_finder.cpp:32`) and identifying **snarls** (minimal 2-edge-cut separated subgraphs between two opposite-side boundary endpoints) and **chains** (sequences of snarls sharing boundary nodes):

- **Asymmetric Inward/Outward Boundary `Visit` Convention (`snarls.hpp:106`, `cactus_snarl_finder.cpp:184–193`):** A `Snarl` is bounded by `(Visit start, Visit end)` where **`start` is oriented *inward* into the snarl interior and `end` is oriented *outward* out of the snarl**:
  ```cpp
  // src/cactus_snarl_finder.cpp:187-192 (cac_child_side is the interior endpoint of each boundary node)
  child_start.set_backward(!cac_child_side1->is_end); // inward: forward iff interior side is node's right 'end'
  child_end.set_backward(cac_child_side2->is_end);    // outward: backward iff interior side is node's right 'end'
  ```
  Traversing a snarl in reverse (`chain_rcbegin`, `snarls.hpp:197`) therefore swaps `(start, end)` *and* flips both `backward` booleans, preserving the inward/outward invariant!
- **Ultrabubbles vs. General/Unary Snarls (`snarls.hpp:98–100, 226–269`):** An *ultrabubble* is an acyclic snarl whose interior contains no tips (degree-1 dead ends). `NetGraph` (`snarls.hpp:246–270`) abstracts each child chain or unary snarl (1-boundary-node hairpin/inversion loop) into a single virtual node so dynamic programming, variant calling (`snarl_caller.cpp`), and minimum-distance indexing (`snarl_distance_index.hpp`, supporting $O(1)$ seed-pair minimum graph distance queries in `vg giraffe`) operate bottom-up over the Snarl Tree. Note the subtle boundary (`snarls.hpp:98–100`): **both single-node empty chains and cyclic chains report identical `in` and `out` handles**, distinguished solely by whether child snarls exist!

#### 3.3 `GBWT` Forward-`LF` Duality, Local-Alphabet `Simple-SDS` RLE, and Chimeric Pruning (`jltsiren/gbwt`)
`Basis: normative + source + execution`

Unconstrained variation graphs suffer **combinatorial path explosion**: across just $B = 10$ nearby biallelic SNP bubbles (`1 -> {2,3} -> 4 -> ...`), topological graph walks admit $2^{10} = 1,024$ paths even if only $H = 4$ phased haplotypes exist in the population ($99.61\%$ false chimeric recombinants; across $B = 30$ SNPs in a 150 bp read window, $2^{30} > 10^9$ paths!). Sirén et al. (*Bioinformatics* 2020, `DOI: 10.1093/bioinformatics/btz575`; *Science* 2021, `DOI: 10.1126/science.abg8871`) solve this via the **Graph Burrows–Wheeler Transform (`GBWT`)**.

Inspection of `SERIALIZATION.md:85–225` and `include/gbwt/gbwt.h:153–279` establishes three foundational properties of `GBWT`:

1. **Reverse-Prefix Ordering & Forward `LF` Navigation (`SERIALIZATION.md:200–214`):** Unlike `r-index` (which sorts suffixes by what *follows* and steps *backward*), `GBWT` partitions its BWT into per-node records `BWT(v)`. Within `BWT(v)`, visits to node `v` by indexed paths are sorted lexicographically by the **preceding** path prefix (breaking ties by rank at predecessor `u`), while `BWT(v)[j]` stores the **next** node `w` visited (`0` = `ENDMARKER` if the path terminates). Thus `LF(v, j)` advances **forward** along the haplotype:
   $$\mathrm{LF}((v, j),\, w) = \mathrm{rank}(v, w) + \mathrm{BWT}(v).\mathrm{rank}(j, w)$$
   where $\mathrm{rank}(v, w)$ is stored directly in `v`'s record header (`SERIALIZATION.md:205`)! Bidirectional search (`bdExtendForward` / `bdExtendBackward`, `gbwt.h:140–145`) maintains synchronized `[L, R]` intervals on both `(v, +)` and `(v, -)` using `bdLF`'s `reverse_offset` count of outgoing neighbors $x$ with $\mathrm{reverse}(x) < \mathrm{reverse}(w)$ (`support.h:127–129`).
2. **Local-Alphabet Single-Byte RLE + Zstandard (`SERIALIZATION.md:85–125`):** Because a variation-graph node $v$ typically has tiny outdegree $\sigma_v \in \{1, 2, 3\}$ (vs. global node alphabet $|\Sigma| \sim 10^8$), `GBWT` re-indexes `v`'s outgoing edges locally into `0..sigma_v - 1`. When $\sigma_v < 255$, `threshold = floor(256 / sigma_v)` packs any run of length $1 \le \ell < \mathrm{threshold}$ into **one single byte** `value + sigma_v * (length - 1)`, spilling `length - threshold` into 7-bit little-endian varint continuation bytes only when $\ell \ge \mathrm{threshold}$ (verified in Probe 2C: for $\sigma_v = 2$, `threshold = 128`, encoding `[(0, 2), (1, 200)]` in just `3` bytes `0x02 0xff 0x48`!). From Simple-SDS format version `6` (`tag = 0x6B376B37`), the concatenated record array is further compressed with Zstandard (`SERIALIZATION.md:124, 185–197`).
3. **Endmarker RLE Incompressibility (`SERIALIZATION.md:219–225`, `gbwt.h:277–278`):** Every path starts at `ENDMARKER = 0` (`2 * i` forward, `2 * i + 1` reverse; node `1` is never used). Because paths across chromosomes start at thousands of distinct nodes, `BWT(0)` has high outdegree $\sigma_0$ and short runs; `gbwt::GBWT` therefore eagerly decompresses and caches `DecompressedRecord endmarker_record` in RAM (`gbwt.h:278`), and cannot wrap around from path end to path start because multi-string endmarkers carry distinct implicit ranks (`SERIALIZATION.md:222–224`).

---

### 4. Multi-Level Performance and Resource Footprint Analysis (`L1`–`L6`)
`Basis: documentation + source + execution + derived`

Quantitative comparison across `FM-Index`/`BWA-MEM` (haploid linear), `r-index` (concatenated repetitive text), `minimap2` v2.22+ (minimizer + SIMD linear/long-read), and `vg` + `GBWT` (`vg giraffe` pangenome mapper) on human-scale datasets ($N_0 \approx 3.1\text{ Gbp}$, $H = 1$ to $5,000$ haplotypes):

| Metric Level | Classical `FM-Index` (`BWA-MEM` on 1 Human Genome) | Run-Length `r-index` (`nicolaprezza/r-index` on $H$ Genomes) | `minimap2` (`sketch` + `lchain` + `ksw2` SIMD) | `vg` + `GBWT` (`vg giraffe` on 5,000+ Human Haplotypes) |
| :--- | :--- | :--- | :--- | :--- |
| **(L1) Authoring & Integration Velocity** | Mature C codebase (`~15k LoC`); extending backward-search heuristics (SMEMs/mate rescue) takes weeks due to interleaved 2-bit BWT bit-twiddling. | Compact C++14 header template (`~1.8k LoC` over `sdsl-lite`); high conceptual subtlety (shifted `SA[q]-1` run samples; 1-based vs 0-based `sd_vector` `select` traps). | Clean modular C11 (`~11k LoC`, zero external deps beyond `zlib`); presets & Python `mappy` bindings (`python/mappy.pyx`) enable `<50 LoC` integration; custom SIMD kernels require expert `SSE4.1`/`NEON` care. | Massive C++17 codebase (`vg` `>250k LoC` + Protobuf + `libbdsg` + `gbwt` + `pinchesAndCacti`); steep onboarding due to bidirected handle/snarl/GBWT orientation invariants. |
| **(L2) Framework & Toolchain Build Time** | Very fast: `gcc -O3` builds `bwa` in **`5–15 s`** (`<1 GB` RAM). | Fast once `sdsl-lite`/`divsufsort` installed: CMake + `g++ -O3` builds `ri-*` binaries in **`15–40 s`** (`~1.5 GB` template instantiation RSS). | Very fast: `make` builds `minimap2` + `ksw2` multi-ISA dispatch in **`4–12 s`** (`<0.5 GB` RSS). | Heavy: full `vg` + submodules (`gbwt`, `gbwtgraph`, `gssw`, `abPOA`, `protobuf`) takes **`15–45 min`** on 16 cores and **`16–32 GB` linker/LTO RSS** (`gbwt` standalone builds in `~25 s`). |
| **(L3) Index Construction & Synthesis Latency** | Building human `.bwt`/`.sa` index takes **`45–75 min`** single-threaded (`O(n)` SAIS/BWT); unscalable to $H = 1,000$ (`3.1 Tbp`). | `SE-SAIS` / `divsufsort` in `ri-build.cpp` still materializes full SA on disk/RAM (`hours` and $O(n)$ workspace unless paired with prefix-free parsing `Big-BWT` for Tbp inputs). | Sub-minute: indexes `3.1 Gbp` GRCh38/CHM13 in **`45–75 s`** wall-clock (`3–4` threads), enabling on-the-fly index-and-map without prebuilt disk files! | Building Cactus `SnarlManager` + `GBWT` + minimizer + distance index for `5,000` haplotypes takes **`4–20 hours`** multi-core (`DynamicGBWT` `INSERT_BATCH_SIZE` merge passes); amortized once per pangenome release. |
| **(L4) Query / Alignment Throughput & SIMD Utilization** | Short reads (`150 bp`): `~15,000–30,000` reads/sec on 16 cores; **fails or crawls (`30–70x` slower)** on `10–100 kb` ONT/HiFi long reads (`minimap2.tex:532–540`). | `count`: `~1–5 µs` per `100 bp` pattern; `locate`: **`~0.1–0.4 µs`/occurrence** ($O(\log(n/r))$ Elias–Fano predecessor, `10–100x` faster than equal-space RLCSA on repetitive collections). | **`30–70x` faster** than BLASR/GraphMap on long reads (`5.0 CPU hr` for `1.39M` CHM13 HiFi reads vs `71.8 hr` Winnowmap2, `mm2-update.tex:151`); `7 min` (8 cores) whole-genome assembly alignment; 16-lane `int8_t` anti-diagonal SSE4.1 saturates vector ALUs (`~10–25 GCUPS`). | `vg giraffe` maps short reads at **`~15,000–25,000` reads/sec** on 16 threads—matching linear `BWA-MEM` speed while genotyping `167,000` SVs across `5,202` genomes (`Sirén et al., Science 2021`), `>10x` faster than general DAG `vg map`. |
| **(L5) Coordinate / Certificate Verification Speed** | Exact match intervals verify in $m$ `LF` steps (`<2 µs`); CIGAR vs reference check runs in $O(|Q|)$ (`>500 MB/s`). | `Phi` chain self-verifies against `pred` rank/select invariants in `O(occ * log(n/r))`; index load from `.ri` takes `<0.5 s` per `100 MB`. | PAF/SAM CIGAR & `MD` tag verification and SV logarithmic rescoring (`mm2-update.tex:117`) run in **`O(|cigar|)` (`<1 µs`/read, negligible CPU share)**. | Checking graph path continuity (`hasEdge(u, v)`) and haplotype membership (`gbwt.find(path)`) runs in $O(|P| \cdot \text{runs\_per\_node})$ (`~1–5 µs`/path); `Snarl` decomposition fuzzing (`snarl_decomposition_fuzzer.cpp`) validates partition bijectivity in ms on test graphs. |
| **(L6) RAM, Disk & Artifact Footprints** | Human `BWA` index: **`~5.4 GB` Peak RSS** (`~4.5 GB` disk); grows **linearly $O(H \cdot N_0)$** (`>5 TB` for 1,000 genomes). | **`O(r)` space**: for $1,000$ human chr19 haplotypes, $r/n < 0.01$, shrinking `.ri` index + SA samples to **`<0.2–0.5 bits/base`** (`~10–50x` smaller than classical FM-index). | GRCh38/CHM13 index: **`6.8–17.1 GB` Peak RSS** depending on preset (`6.8 GB` SMRT, `14.5 GB` splice, `17.1 GB` HiFi CHM13, `mm2-update.tex:152`); `.mmi` disk dump `~4–8 GB`. | `1000 Genomes` (`5,008` whole-genome haplotypes) `GBWT` occupies **`~15–25 GB` compressed `.gbwt` on disk** (Simple-SDS v6 + Zstd) and **`~35–100 GB` Peak RSS** during whole-pangenome `vg giraffe` mapping (`GBZ` unified graph+GBWT cuts RAM below `~32–64 GB`). |

---

### 5. Human Comprehensibility (`C1`) and Conceptual Simplicity / Model Refinement (`C2`)

#### 5.1 `(C1)` Human Comprehensibility and Coordinate-Orientation Ergonomics
`Basis: source + derived`

Genomic indexing codebases exhibit a striking divergence between *compact code size* and *human auditability*:

- **The Four-Fold Orientation & Indexing Trap (`vg`, `GBWT`, `r-index`):** Auditing a cross-component read mapper (`minimap2`/minimizers -> `GBWT` -> `vg` `SnarlManager` -> VCF) forces a human engineer to maintain **four non-commuting index/orientation conventions simultaneously**:
  1. **0-based vs. 1-based `select`:** `sdsl::sd_vector::select_1` is **1-based** (`sparse_sd_vector.hpp:181` wraps `select1(i + 1)` to expose 0-based `select(i)`), whereas `Simple-SDS` is **0-based** (`SERIALIZATION.md:17`). Mixing them shifts every run boundary by one run!
  2. **Shifted vs. Direct SA Samples (`r_index.hpp:599, 614`):** `samples_last` stores $(\mathrm{SA}[q] - 1) \bmod n$ rather than $\mathrm{SA}[q]$, so `count_and_get_occ` decrements `k` when `bwt[R] == c` (`L509`) yet *does not* decrement `samples_last[run_of_j]` when `bwt[R] != c` (`L533`)—a subtlety that looks like a bug to casual readers until proved inductively (and caught immediately by Probe 2A).
  3. **Backward String `LF` vs. Forward Graph `LF`:** Classical `FM-Index` / `r-index` `LF` extends patterns *leftward* (5'ward), whereas `GBWT::LF` extends paths *rightward* (3'ward).
  4. **Inward `start` vs. Outward `end` `Snarl` `Visit`s (`snarls.hpp:106`):** A `Snarl`'s `start` points *into* the bubble (`!is_end`), while `end` points *out of* the bubble (`is_end`), whereas `NetGraph` child chains expose "heads" and "tails" (`snarls.hpp:241–243`) that are *both* inward-facing!
- **Silent Heuristic Failure vs. Explicit Diagnostics (`minimap2`):** `minimap2` achieves exceptional CLI ergonomics via domain presets (`-x map-ont`, `-x asm20`), yet its internal guards fail **silently** rather than emitting warnings: passing custom scoring matrices violating `-min_sc <= 2 * (q + e)` returns zero alignments silently (`ksw2_extz2_sse.c:90`), exceeding $M + 2(q + e) > 127$ wraps `int8_t` SIMD lanes without an assertion (`L78, 163`), and even-$k$ palindromes vanish without notice (`sketch.c:108`).

#### 5.2 `(C2)` Conceptual Simplicity, Orthogonality, and Universal Model Refinement
`Basis: derived`

Applying Jackson's *concept-purpose alignment*, Ousterhout's *deep-module* principle, and Felleisen's *macro-expressibility* criterion reveals two deep unifying abstractions that eliminate ad-hoc special cases across these four systems:

1. **Unifying Linear `RLBWT` and `GBWT` as Instances of a Bidirected Wheeler Automaton:** `r-index` (global byte alphabet, backward `LF`, global Elias–Fano run bitvectors) and `GBWT` (per-node local edge alphabet, forward `LF`, per-node RLE records) appear structurally disjoint only because `r-index` hardcodes a linear chain graph of $n$ positions while `GBWT` hardcodes node-partitioned adjacency lists. Under **Gagie, Manzini, and Sirén's Wheeler Graph framework** equipped with the **dihedral strand involution** $\iota(h) = h \oplus 1$ (requiring $\iota$ to reverse edge direction while preserving co-lexicographic interval contiguity on the dual strand), linear `FM-Index`es, `r-index` $\Phi$-samples, de Bruijn graphs (`BOSS`), and haplotype `GBWT`s collapse into **one single ADT**: a co-lexicographically ordered labeled transition system $(Q, \Sigma, \delta, \iota)$ whose state intervals $[L, R]$ map under `extend(state, label)` via run-compressed monotone rank dictionaries. Making the strand involution $\iota$ a typed involution on `OrientedHandle` (separating `EntrySide(v)` and `ExitSide(v)` as distinct phantom types!) eliminates `Snarl` inward/outward `bool backward` confusion at compile time: every boundary is simply an `OrientedEdge(ExitSide -> EntrySide)` cut!
2. **Eliminating Even-$k$ Palindrome Blindness & Silent SIMD Overflow Without Adapter Overhead:**
   - *Symmetry-breaking canonical minimizers:* `mm_sketch` skips `kmer[0] == kmer[1]` (`sketch.c:108`) only because it conflates *canonical $k$-mer identity* with *single-minimizer strand bit $z$*. Treating `z` as a 2-bit sum `{Fwd(0), Rev(1), AmbiguousPalindrome(2)}` (matching against both strands during `seed.c` anchor collection) restores 100% sensitivity on even-$k$ palindromic repeats with zero hash-table expansion.
   - *Compile-/Init-Checked Bounded Tropical Difference Semiring:* Suzuki–Kasahara's difference recurrence is purely an algebraic change of basis from the $(\max, +)$ tropical semiring over $\mathbb{Z}$ to bounded potential differences $\nabla H \in [-Q, M + Q]$. Checking the invariant $M + 2(q + e) \le 127 \land X \le 2(q + e)$ once at `mm_mapopt_t` initialization—automatically dispatching to a 16-bit (`int16_t`, 8-lane SSE2 / 16-lane AVX2) difference kernel when exceeded—makes arbitrary scoring matrices a regular, overflow-free case without slowing down the 8-bit fast path by a single instruction.

## Boundaries

- **Prefix-Free Parsing (`Big-BWT` / `pfp-thresholds`) Construction (`not examined`):** `nicolaprezza/r-index` at revision `7009b5374282aa1d8e9b594d0a06c49a0bc1330f` builds `SA` in $O(n)$ workspace via `SE-SAIS` or `libdivsufsort` (`r_index.hpp:571–575`); sublinear-workspace prefix-free parsing (`Boucher et al., WABI 2018 / ALMOB 2019`) used to construct `r-index` / `movi` directly on terabase pangenomes was `not examined` at source level.
- **ARM NEON / AVX-512 Dispatch Parity in `minimap2` (`not examined` via execution):** Only the x86 SSE2/SSE4.1 difference recurrence (`ksw2_extz2_sse.c`) was inspected and modeled directly; `sse2neon` translation edge cases on ARM64 and external AVX-512 `mm2-fast` forks were `not examined`.
- **`minimap2` $k > 28$ and $w \ge 256$ (`unsupported`):** `mm_sketch` (`sketch.c:84`) explicitly asserts `w < 256` and `k <= 28`; wider k-mers or windows are `unsupported` by the 64-bit `(hash56 << 8) | span8` packing in `mm128_t.x`.
- **Arbitrary Cyclic Graphs Without Ultrabubble/Cactus Cut Structure (`known not to apply`):** `Snarl` tree distance shortcuts (`snarl_distance_index.hpp`) rely on bounded-width 2-edge-cut decomposition; in dense tangled de Bruijn or non-planar repeat graphs where most nodes collapse into a single giant cyclic root snarl, $O(1)$ tree-hierarchy distance queries **are known not to apply** and degrade to local Dijkstra traversal.
- **Path-End-to-Start Wraparound in `GBWT` (`unsupported`):** As normatively specified in `jltsiren/gbwt/SERIALIZATION.md:222–225`, multi-string `ENDMARKER` (`0`) visits have distinct implicit ranks, so jumping from the end of a `GBWT` haplotype back to its start offset in `BWT(0)` without `DASamples` (`Document array samples`) is `unsupported`.

## Evidence

### Primary Upstream Repositories and Specifications

1. **`nicolaprezza/r-index` @ `7009b5374282aa1d8e9b594d0a06c49a0bc1330f`** (observed `2026-11-19`):
   - `internal/r_index.hpp:42–150, 171–221, 328–355, 482–667` — `0x00`/`0x01` input guard (`L46–50, 636–644`), `sufsort` `(sa[i-1] - 1) mod n` run-boundary sampling (`L592–621`), `count_and_get_occ` inductive `SA[R]` maintenance (`L482–544`), and `Phi` circular predecessor (`L195–221`).
   - `internal/rle_string.hpp:52–256` & `internal/sparse_sd_vector.hpp:107–184` — block-sampled `runs` (`B = 2`), `runs_per_letter[256]`, `huff_string` `run_heads`, 0-based `select1(i + 1)` wrapper, and strict `predecessor_rank_circular`.
2. **`lh3/minimap2` @ `3c28777e7e2dcc90f825de1b9f17a89cca7d4452`** (observed `2026-11-19`):
   - `sketch.c:28–143` — `hash64` invertible mixer (`L28–38`), `tiny_queue_t` 32-entry ring (`L40–58`), `k <= 28` & `w < 256` assertion (`L84`), symmetric palindrome skip `if (kmer[0] == kmer[1]) continue;` (`L108`), and `kmer_span < 256` HPC filter (`L111`).
   - `seed.c:56–132` — `mm_seed_select` 128-slot binomial heap rescuing `round((pe - ps) / dist)` lowest-occurrence seeds across high-frequency centromeric streaks.
   - `lchain.c:113–305` — `comput_sc` concave gap formula (`L113–138`), `mg_lchain_dp` `max_skip` early exit (`L182–184`), and `mg_lchain_rmq` $O(n \log n)$ RMQ tree (`L250–305`).
   - `ksw2_extz2_sse.c:34–298` — Suzuki–Kasahara shifted 8-bit anti-diagonal SSE2/SSE4.1 kernel, `-min_sc > 2*(q+e)` guard (`L90`), and signed `_mm_max_epi8` ceiling `max_sc_ = mat[0] + 2*(q+e)` (`L78, 163`).
   - `tex/minimap2.tex:167–350, 518–699` & `tex/mm2-update.tex:60–231` — exact mathematical derivations and CHM13/GRCh38 empirical runtime/RAM benchmarks.
3. **`vgteam/vg` @ `6f11d25de4d2466382b22225b74e16e4e4e9b74b`** (observed `2026-11-19`):
   - `src/handle.hpp:54–95` & `src/gbwt_helper.hpp:23–198` — `handlegraph` bindings, Wang handle hashing, and `handle_t <-> gbwt::node_type` bijections.
   - `src/snarls.hpp:59–280` & `src/cactus_snarl_finder.cpp:25–209` — `HandleGraphSnarlFinder`, `Chain` reverse-complement iterators, `NetGraph` child chain/unary abstraction, and `CactusSide` inward `start` vs. outward `end` `Visit` construction.
4. **`jltsiren/gbwt` @ `14a06d588ea6de50cd809f546b9bb57c92c15ac1`** (observed `2026-11-19`):
   - `SERIALIZATION.md:1–250` — normative Simple-SDS v6 specification (`0x6B376B37` header, `threshold = floor(256 / sigma)` byte RLE `L85–99`, Zstandard BWT compression `L124, 185–197`, bidirectional `2*v` / `2*v+1` mapping `L116–122`, and forward-`LF` record semantics `L198–225`).
   - `include/gbwt/gbwt.h:20–280` & `include/gbwt/support.h:20–180` — `Node`/`Path` bit encodings, `bdLF`, `DynamicRecord`, and cached `endmarker_record`.

### Peer-Reviewed Literature

- P. Ferragina and G. Manzini, *"Indexing compressed text,"* J. ACM 52(4), pp. 552–581, 2005, `DOI: 10.1145/1082036.1082039`.
- T. Gagie, G. Navarro, and N. Prezza, *"Fully Functional Suffix Trees and Optimal Text Searching in BWT-Runs Bounded Space,"* J. ACM 67(1), Article 2, 2020, `DOI: 10.1145/3375890`.
- S. Schleimer, D. S. Wilkerson, and A. Aiken, *"Winnowing: Local Algorithms for Document Fingerprinting,"* ACM SIGMOD 2003, pp. 76–85, `DOI: 10.1145/872757.872770`.
- H. Suzuki and M. Kasahara, *"Introducing difference recurrence relations for faster semi-global alignment of long sequences,"* BMC Bioinformatics 19(Suppl 1):45, 2018, `DOI: 10.1186/s12859-018-2014-8`.
- H. Li, *"Minimap2: pairwise alignment for nucleotide sequences,"* Bioinformatics 34(18), pp. 3094–3100, 2018, `DOI: 10.1093/bioinformatics/bty191`.
- H. Li, *"New strategies to improve minimap2 alignment accuracy,"* Bioinformatics 37(23), pp. 4572–4574, 2021, `DOI: 10.1093/bioinformatics/btab705`.
- B. Paten et al., *"Superbubbles, Ultrabubbles, and Cacti,"* Journal of Computational Biology 25(7), pp. 649–663, 2018, `DOI: 10.1089/cmb.2017.0251`.
- E. Garrison et al., *"Variation graph toolkit improves read mapping by representing genetic variation in the reference,"* Nature Biotechnology 36(9), pp. 875–879, 2018, `DOI: 10.1038/nbt.4227`.
- J. Sirén et al., *"Haplotype-aware graph indexes,"* Bioinformatics 36(2), pp. 400–407, 2020, `DOI: 10.1093/bioinformatics/btz575`.
- J. Sirén et al., *"Pangenomics enables genotyping of known structural variants in 5202 diverse genomes,"* Science 374(6574), abg8871, 2021, `DOI: 10.1126/science.abg8871`.

### Reproducible Execution Micro-Probes

Running the standalone Python 3 script below verifies (2A) `r-index` shifted `(SA[q] - 1) mod n` run sampling, exact `locate_all` agreement, and haplotype scaling ($H = 8 \dots 128$) against equal-sample-budget classical `FM-Index`es; (2B) `minimap2` `mm_sketch` Winnowing density, even-$k$ `(AT)^200` palindrome blindness (`0` minimizers at $k=14$ vs. `385` at $k=15$), `HPC` `kmer_span >= 256` drop, and Suzuki–Kasahara `int8_t` wraparound when $M + 2(q + e) > 127$; and (2C) bidirected `GBWT` path involution, chimeric pruning (`99.61%`), and Simple-SDS v6 byte RLE packing:

```python
#!/usr/bin/env python3
import bisect, random

# 2A: Run-Length r-index (r_index.hpp:195-221, 482-625) vs Equal-Space Classical FM-Index
def build_r_index(text: str):
    assert "\x00" not in text and "\x01" not in text
    s = text + "\x01"; n = len(s)
    sa = sorted(range(n), key=lambda i: s[i:])
    bwt = "".join(s[(i - 1) % n] for i in sa)
    F, acc = {}, 0
    for ch in sorted(set(bwt)):
        F[ch] = acc; acc += bwt.count(ch)
    runs, samples_first, samples_last = [], [], []
    rs = 0
    for i in range(1, n + 1):
        if i == n or bwt[i] != bwt[rs]:
            runs.append((bwt[rs], rs, i - 1))
            samples_first.append(((sa[rs] - 1) % n, len(runs) - 1))
            samples_last.append((sa[i - 1] - 1) % n)
            rs = i
    samples_first.sort()
    pred_pos = [p[0] for p in samples_first]
    pred_to_run = [p[1] for p in samples_first]
    r = len(runs)

    def lf_range(l, u, c):
        if c not in F: return (1, 0)
        cb = bwt[:l].count(c); ci = bwt[:u + 1].count(c) - cb
        return (1, 0) if ci == 0 else (F[c] + cb, F[c] + cb + ci - 1)

    def locate_all(pat: str):
        l, u = 0, n - 1
        k = (samples_last[r - 1] + 1) % n
        for ch in reversed(pat):
            nl, nu = lf_range(l, u, ch)
            if nl > nu: return []
            if bwt[u] == ch:
                k -= 1
            else:
                j = bwt.rfind(ch, l, u)
                ridx = next(idx for idx, (_, a, b) in enumerate(runs) if a <= j <= b)
                k = samples_last[ridx]
            l, u = nl, nu
        occ = [k]
        for _ in range(u - l):
            idx = bisect.bisect_left(pred_pos, k) - 1
            jr = (r - 1) if idx < 0 else idx
            j = pred_pos[jr]
            delta = (k - j) if j < k else (k + 1)
            k = (samples_last[pred_to_run[jr] - 1] + delta) % n
            occ.append(k)
        return sorted(occ)
    return n, r, locate_all

for H in (8, 32, 64, 128):
    rng = random.Random(2026)
    base = "".join(rng.choice("ACGT") for _ in range(1000))
    haps = [base]
    for _ in range(H - 1):
        arr = list(base)
        for pos in rng.sample(range(1000), 2):
            arr[pos] = rng.choice([b for b in "ACGT" if b != arr[pos]])
        haps.append("".join(arr))
    txt = "#".join(haps)
    n, r, loc = build_r_index(txt)
    s_eq = max(1, round(n / (2 * r)))
    hits = loc(base[200:225])
    exp = [i for i in range(len(txt)) if txt.startswith(base[200:225], i)]
    assert hits == exp
    lf_steps = sum((-pos) % s_eq for pos in hits)
    print(f"[2A-scale] H={H:3d}: n={n:6d}, r={r:4d}, n/r={n/r:5.2f}x, eq_FM_stride_s={s_eq:2d}, eq_FM_avg_LF={lf_steps/len(hits):.2f} vs r-index_avg_Phi={(len(hits)-1)/len(hits):.2f}")

# 2B: minimap2 mm_sketch (sketch.c:28-143) & Suzuki-Kasahara int8 Ceiling (ksw2_extz2_sse.c:34-168)
NT4 = {"A": 0, "C": 1, "G": 2, "T": 3}
def hash64(key: int, mask: int) -> int:
    key = ((~key) + (key << 21)) & mask; key ^= key >> 24
    key = ((key + (key << 3)) + (key << 8)) & mask; key ^= key >> 14
    key = ((key + (key << 2)) + (key << 4)) & mask; key ^= key >> 28
    return (key + (key << 31)) & mask

def mm_sketch_py(seq: str, w: int, k: int, is_hpc: bool = False):
    shift1, mask, UMAX = 2 * (k - 1), (1 << (2 * k)) - 1, (1 << 64) - 1
    kmer0 = kmer1 = i = l = buf_pos = min_pos = kmer_span = 0
    buf, min_it, tq, out, n = [(UMAX, UMAX)] * w, (UMAX, UMAX), [], [], len(seq)
    while i < n:
        c, info = NT4.get(seq[i], 4), (UMAX, UMAX)
        if c < 4:
            if is_hpc:
                sl = 1
                while i + sl < n and NT4.get(seq[i + sl], 4) == c: sl += 1
                i += sl - 1; tq.append(sl); kmer_span += sl
                if len(tq) > k: kmer_span -= tq.pop(0)
            else: kmer_span = min(k, l + 1)
            kmer0 = ((kmer0 << 2) | c) & mask
            kmer1 = (kmer1 >> 2) | ((3 ^ c) << shift1)
            if kmer0 == kmer1: i += 1; continue
            z = int(kmer1 < kmer0); l += 1
            if l >= k and kmer_span < 256:
                info = ((hash64(kmer1 if z else kmer0, mask) << 8) | kmer_span, (i << 1) | z)
        else: l = kmer_span = 0; tq.clear()
        buf[buf_pos] = info
        if l == w + k - 1 and min_it[0] != UMAX:
            for j in list(range(buf_pos + 1, w)) + list(range(buf_pos)):
                if min_it[0] == buf[j][0] and buf[j][1] != min_it[1]: out.append(buf[j])
        if info[0] <= min_it[0]:
            if l >= w + k and min_it[0] != UMAX: out.append(min_it)
            min_it, min_pos = info, buf_pos
        elif buf_pos == min_pos:
            if l >= w + k - 1 and min_it[0] != UMAX: out.append(min_it)
            min_it = (UMAX, UMAX)
            for j in list(range(buf_pos + 1, w)) + list(range(buf_pos + 1)):
                if min_it[0] >= buf[j][0]: min_it, min_pos = buf[j], j
            if l >= w + k - 1 and min_it[0] != UMAX:
                for j in list(range(buf_pos + 1, w)) + list(range(buf_pos + 1)):
                    if min_it[0] == buf[j][0] and min_it[1] != buf[j][1]: out.append(buf[j])
        buf_pos = (buf_pos + 1) % w; i += 1
    if min_it[0] != UMAX: out.append(min_it)
    return out

rng2 = random.Random(2026)
rdna = "".join(rng2.choice("ACGT") for _ in range(20000))
print(f"[2B] Random DNA density (w=10,k=15): {len(mm_sketch_py(rdna,10,15))/(20000-14):.5f} vs 2/(w+1)={2/11:.5f}")
print(f"[2B] (AT)^200 palindrome: even k=14 -> {len(mm_sketch_py('AT'*200,10,14))} minimizers; odd k=15 -> {len(mm_sketch_py('AT'*200,10,15))} minimizers")
print(f"[2B] HPC 260bp homopolymer + 19bp tail (k=15): retained_minimizers={len(mm_sketch_py('A'*260+'CGTACGTACGTACGTACGT',5,15,True))}")

def suzuki_vs_gotoh(qseq, tseq, M, X, q, e):
    ql, tl, NEG = len(qseq), len(tseq), -10**9
    H = [[NEG]*(tl+1) for _ in range(ql+1)]; E = [[NEG]*(tl+1) for _ in range(ql+1)]; F = [[NEG]*(tl+1) for _ in range(ql+1)]
    H[0][0] = 0
    for j in range(1, tl+1): H[0][j] = F[0][j] = -q - j*e
    for i in range(1, ql+1): H[i][0] = E[i][0] = -q - i*e
    for i in range(1, ql+1):
        for j in range(1, tl+1):
            E[i][j] = max(H[i-1][j]-q, E[i-1][j])-e; F[i][j] = max(H[i][j-1]-q, F[i][j-1])-e
            H[i][j] = max(H[i-1][j-1] + (M if qseq[i-1]==tseq[j-1] else -X), E[i][j], F[i][j])
    s8 = lambda v: ((v & 0xFF) - 256) if (v & 0xFF) >= 128 else (v & 0xFF)
    qe = q + e; max_sc = s8(M + 2*qe)
    u, v, x, y, H_sk = [0]*tl, [0]*tl, [0]*tl, [0]*tl, [0]*tl
    for r in range(ql + tl - 1):
        st, en = max(0, r - ql + 1), min(tl - 1, r)
        x1, v1 = (x[st-1], v[st-1]) if st > 0 else (0, q if r > 0 else 0)
        if en >= r: y[r], u[r] = 0, (q if r > 0 else 0)
        for t in range(st, en + 1):
            z = s8((M if qseq[r-t]==tseq[t] else -X) + 2*qe)
            a = s8(x1 + v1); x1, v1_old = x[t], v[t]; ut = u[t]; b = s8(y[t] + ut)
            z = z if z > a else a  # signed _mm_max_epi8 (ksw2_extz2_sse.c:163)
            z = s8(min(max(z & 0xFF, b & 0xFF), max_sc & 0xFF))
            u[t], v[t] = s8(z - v1), s8(z - ut); v1 = v1_old
            zs = s8(z - q); an, bn = s8(a - zs), s8(b - zs)
            x[t], y[t] = max(0, an), max(0, bn)
        if r > 0:
            H_sk[en] = (H_sk[en-1] + (u[en]&0xFF) - qe) if en > 0 else (H_sk[en] + (v[en]&0xFF) - qe)
            for t in range(st, en): H_sk[t] += (v[t]&0xFF) - qe
        else: H_sk[0] = (v[0]&0xFF) - 2*qe
    return H[ql][tl], H_sk[tl-1], M + 2*qe

for M, X, q, e, tag in [(2, 4, 4, 2, "default"), (20, 10, 50, 5, "overflow")]:
    g, sk, bd = suzuki_vs_gotoh("ACGTACGTACGT", "ACGTTCGTACGT", M, X, q, e)
    print(f"[2B] Suzuki-Kasahara {tag:8s} (M+2(q+e)={bd}): Gotoh={g}, SK_int8={sk}, match={g==sk}")

# 2C: Bidirected GBWT Simple-SDS v6 RLE & Chimeric Pruning
def encode_gbwt_rle(runs, sigma: int) -> bytes:
    out, thr = bytearray(), 256 // sigma
    for val, ln in runs:
        if ln < thr: out.append(val + sigma * (ln - 1))
        else:
            out.append(val + sigma * (thr - 1)); rem = ln - thr
            while rem >= 0x80: out.append((rem & 0x7F) | 0x80); rem >>= 7
            out.append(rem)
    return bytes(out)

rle = encode_gbwt_rle([(0, 2), (1, 200)], sigma=2)
print(f"[2C] 10-SNP bubble graph: total_topological_walks={2**10} vs GBWT_valid_haplotypes=4 (chimeric_pruning={(1-4/1024)*100:.2f}%)")
print(f"[2C] Simple-SDS v6 RLE (sigma=2, threshold=128): runs=[(0,2),(1,200)] -> {len(rle)} bytes ({rle.hex()})")
```

Recorded execution output on Linux `x86_64` (Python 3.13.5, `2026-11-19`):

```text
[2A-scale] H=  8: n=  8008, r= 833, n/r= 9.61x, eq_FM_stride_s= 5, eq_FM_avg_LF=2.12 vs r-index_avg_Phi=0.88
[2A-scale] H= 32: n= 32032, r=1140, n/r=28.10x, eq_FM_stride_s=14, eq_FM_avg_LF=6.50 vs r-index_avg_Phi=0.97
[2A-scale] H= 64: n= 64064, r=1517, n/r=42.23x, eq_FM_stride_s=21, eq_FM_avg_LF=10.00 vs r-index_avg_Phi=0.98
[2A-scale] H=128: n=128128, r=2304, n/r=55.61x, eq_FM_stride_s=28, eq_FM_avg_LF=13.47 vs r-index_avg_Phi=0.99
[2B] Random DNA density (w=10,k=15): 0.18383 vs 2/(w+1)=0.18182
[2B] (AT)^200 palindrome: even k=14 -> 0 minimizers; odd k=15 -> 385 minimizers
[2B] HPC 260bp homopolymer + 19bp tail (k=15): retained_minimizers=2
[2B] Suzuki-Kasahara default  (M+2(q+e)=14): Gotoh=18, SK_int8=18, match=True
[2B] Suzuki-Kasahara overflow (M+2(q+e)=130): Gotoh=210, SK_int8=-220, match=False
[2C] 10-SNP bubble graph: total_topological_walks=1024 vs GBWT_valid_haplotypes=4 (chimeric_pruning=99.61%)
[2C] Simple-SDS v6 RLE (sigma=2, threshold=128): runs=[(0,2),(1,200)] -> 3 bytes (02ff48)
```

## Revalidation

To cheaply determine whether these findings remain valid on newer upstream revisions without rebuilding terabase pangenome indexes:

1. **`r-index` Shifted Run-Sample & Reserved-Byte Check (`<2 s`):** Inspect `internal/r_index.hpp` around `contains_reserved_chars`, `sufsort`, `Phi`, and `count_and_get_occ`; verify whether `0x00`/`0x01` remain forbidden and whether `samples_first`/`samples_last` still store `sa[i-1] > 0 ? sa[i-1] - 1 : sa.size() - 1`.
2. **`minimap2` Sketching & Suzuki–Kasahara Bounds Check (`<3 s`):** Diff `sketch.c` (`mm_sketch` lines `80–120`) to verify whether `k <= 28`, `kmer[0] == kmer[1]` `continue`, and `kmer_span < 256` still hold; diff `ksw2_extz2_sse.c` (`max_sc_ = mat[0] + (q + e) * 2`, `if (-min_sc > 2 * (q + e)) return;`, and `_mm_max_epi8(z, a)`) to check whether automatic 16-bit fallback or overflow diagnostics were added.
3. **`vg` `Snarl` Orientation & `GBWT` Format Version Check (`<3 s`):** Inspect `vg/src/cactus_snarl_finder.cpp` (`recursively_emit_snarls`) and `vg/src/snarls.hpp` (`traverse_decomposition`) to confirm inward `start` / outward `end` `Visit` semantics, and check `jltsiren/gbwt/SERIALIZATION.md` + `include/gbwt/files.h` (`GBWTHeader::DEFAULT_VERSION`) to verify whether `0x6B376B37`, version `6` Zstandard record compression, and `threshold = floor(256 / sigma)` local-alphabet RLE remain current.
