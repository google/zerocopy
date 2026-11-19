# Tensor Layout Algebras, Scratchpad DMA Pipelines, and Verified User-Schedulable Accelerator Languages

## Summary

Modern tensor and spatial accelerators (NVIDIA Hopper/Blackwell GPUs with Tensor Cores and TMA, Google TPU systolic arrays with non-cached `VMEM` scratchpads and semaphore-tracked DMA, and systolic ASICs such as Gemmini) require three abstractions absent from scalar/affine C/LLVM compilers: (1) **hierarchical multi-dimensional layout morphisms**, (2) **$\mathbb{F}_2$ bitwise XOR swizzling** for 32-bank SRAM conflict elimination, and (3) **explicit asynchronous scratchpad staging and checked user-level scheduling**. Direct source inspection and executable verification establish six core technical findings:

1. **CuTe Layout Algebra Admissibility & CUTLASS Soundness Gaps**: `CuTe` (`NVIDIA/cutlass`) models mappings as congruent nested `(Shape, Stride)` tuples; categorically (`arXiv:2601.05972`, `ColfaxResearch/layout-categories`), a layout arises from a $\mathbf{Tuple}$/$\mathbf{Nest}$ morphism iff it is **tractable** ($(s_i d_i) \mid d_{i+1}$ after sorting nonzero modes). In `include/cute/layout.hpp:1076-1111`, static `composition_impl` passes wrapping non-divisible strides such as `(4,4):(1,8) o 4:3`, producing `(2,2):(3,8)` with $R(2)=8 \neq 10=A(B(2))$; moreover, left-distributivity fails on strictly injective untractable layouts (`(4,4):(1,8) o (2,2):(1,3)` yields $R(1,1)=4 \neq 8=A(B(1,1))$), dynamic divisibility assertions are commented out, and `pycute/layout.py:316` mis-dispatches `logical_product(A, int)` to `logical_divide`.
2. **Duality of $(\mathbb{Z}, +, \cdot)$ + External `Swizzle` vs. Pure $\mathbb{F}_2$ `LinearLayout`**: Presburger/affine IRs cannot express XOR swizzling. CuTe composes an involution `Swizzle<B,M,S>` (`|S| >= B`) externally via `ComposedLayout` + `MixedBits` + byte-addressed `smem_ptr_flag_bits<B>` (`pointer_flagged.hpp:50-84`), whereas Triton's $\mathrm{GF}(2)$ `LinearLayout` (`LinearLayout.h:20-320`) unifies register/SMEM layouts and XOR swizzling natively (matching CuTe Hopper `SW128` element-for-element) but cannot represent non-power-of-two shapes or padded shared memory (`toLinearLayoutIgnoringPadding`).
3. **Algebraic $\mathbb{F}_2$ Bank-Conflict Criterion**: For 32-bank (4-byte word) GPU SMEM with $\mathbb{F}_2$-affine bank map $b(t) = A t \oplus b_0$ ($A \in \mathbb{F}_2^{5 \times 5}$), the exact warp serialization factor is $2^{5 - \mathrm{rank}_{\mathbb{F}_2}(A)}$; `Swizzle<5,2,5>` (`32x32 f32`, 32-way $\to$ 1-way) and `Swizzle<4,2,5>` (`32x32 f16`, 16-way $\to$ 1-way) lift $\mathrm{rank}_{\mathbb{F}_2}(A)$ to `5` with proven involution $M^2 = I$.
4. **TPU Systolic `VMEM` & DMA Semaphores (`Pallas`/`Mosaic`)**: TPU v4 pairs two TensorCores (four $128\times 128$ MXUs + 16 MiB `VMEM` each) with 128 MiB `CMEM` (ISCA '23). Pallas enforces `(8, 128)` trailing sublane/lane tiling (up to $1024\times$ padding cliff on trailing `1x1` dims) and sequential lexicographic single-core grids, but checks unused `AsyncCopyDescriptor` handles only via a runtime `__del__` log (`mosaic_primitives.py:241-247`) and exposes unchecked hazard hints (`no_hazard`, `no_hazard_no_deps`).
5. **`TritonGPU` Compiler Pitfalls vs. `Futhark` Uniqueness & Incremental Flattening**: Triton's `RemoveLayoutConversions` and `SoftwarePipeliner` exhibit SSA-dominance, stale-remap, reduction-layout, and async-barrier failure modes (`isSafeToPipeline` rejects `dist > 1`, outer loops, and barriers). Futhark enables sound in-place `*[]t` GPU updates via path-sensitive location alias analysis (`Consumption.hs`, `AliasSelf`, saturated-HOF freshness) and compiles nested parallelism via runtime-threshold multi-versioned `Incremental` flattening.
6. **Verified Scheduling Taxonomy**: **Clément & Cohen (OOPSLA '22)** verify affine Halide compilations via **prophetic refinement annotations discharged by an affine solver + Z3** (not Coq); **Coq-verified** scheduling rewrites are provided by **ATL (POPL '22)**. **Exo / Exo 2** (PLDI '22 / ASPLOS '25) externalize `@instr`/`@config`/`Memory`, verify rewrites with Z3 affine effect analysis (`Commutes` vs. `Disjoint_Memory`) + a modulo-config provenance lattice (`proc_eqv.py`) + forwarded AST `Cursor`s, while trusting `@instr` C templates and retaining `unsafe_disable_checks` escape hatches. **Rise/Elevate** (ICFP '20) expresses schedules as typed functional rewrite strategies `Strategy[P] = P => RewriteResult[P]`.

## Applicability

This report analyzes and cross-compares the fifteen durable upstream repositories and peer-reviewed specifications pinned in `REPORT.json`:
- **Layout Algebras & Swizzling**: `NVIDIA/cutlass` (`CuTe` C++ headers, SM90 TMA/GMMA traits, docs, `pycute`) interpreted alongside Cecka (`arXiv:2603.02298v2`), Carlisle et al. (`arXiv:2601.05972v1`), `ColfaxResearch/layout-categories` (`tract`), and `triton-lang/triton` (`LinearLayout`, `TritonGPU` shared-memory encodings).
- **Systolic Scratchpad, Block-SPMD & Functional Flattening Compilers**: `jax-ml/jax` (`Pallas`/`Mosaic` TPU backend and docs) with Jouppi et al. (ISCA '23, TPU v4); `triton-lang/triton` with Tillet et al. (MAPL '19); and `diku-dk/futhark` with Henriksen et al. (PLDI '17, PPoPP '19).
- **Verified User-Schedulable & Exocompilation Languages**: `exo-lang/exo` (Ikarashi et al. PLDI '22, ASPLOS '25), `halide/Halide` (Ragan-Kelley et al. PLDI '13) paired with Clément & Cohen (OOPSLA '22) and Liu et al. ATL (POPL '22), and `elevate-lang/elevate` + `rise-lang/shine` (Hagedorn et al. ICFP '20).

**Version & Hardware Scope**: Exact C++/Python/MLIR/Haskell/Scala line ranges, static assertions, and implementation bugs apply strictly to the pinned 40-character commit SHAs in `REPORT.json`. Algebraic theorems (tractability, wrapping-stride divisibility, $\mathbb{F}_2$ bank-conflict rank, effect commutativity) hold generally for systems matching those definitions. GPU SMEM banking formulas assume 32 four-byte banks (Volta through Blackwell); TPU tiling rules reflect TPU v4–v6e `(8, 128)` VREG geometry as documented in `jax-ml/jax`.

**Adjacent Corpus Cross-References**: This package complements without duplicating `anneal-databases-networking-cloud-builds-and-tensor-survey` (broader MLIR/polyhedral verification survey) and `rust-llvm-o3-loop-and-slp-vectorization-idiom-census` (CPU LLVM `-O3` loop and SLP auto-vectorization idioms in Rust).

## Findings

### 1. CuTe Hierarchical `(Shape, Stride)` Layout Algebra and Exact Admissibility Preconditions

Basis: documentation + source + execution + derived

In NVIDIA CUTLASS 3.x/4.x (`NVIDIA/cutlass`, `include/cute/layout.hpp`, `01_layout.md`, `02_layout_algebra.md`, Cecka `arXiv:2603.02298v2`), a **CuTe `Layout`** is a pair $L = (S, D)$ of **congruent** hierarchical `IntTuple`s (`static_assert(congruent(shape, stride))`), whose leaves are static (`cute::C<N>` / `Int<N>`) or dynamic integers.

#### 1.1 Coordinate Isomorphisms and Layout Evaluation
Any `Shape` $S$ with domain size $|S| = \prod \mathrm{flatten}(S)$ induces a **colexicographic (column-major) isomorphism** between 1-D linear indices $i \in [0, |S|)$, flat natural coordinates $(c_0, \dots, c_{k-1}) \in \prod_j [0, s_j)$, and compatible hierarchical coordinates (`crd2idx` / `idx2crd`):
$$L(c) = \langle \mathrm{idx2crd}(c, S), D \rangle = \sum_{j=0}^{k-1} c_j \cdot d_j, \qquad c_j = \left\lfloor \frac{i}{\prod_{r < j} s_r} \right\rfloor \bmod s_j.$$
Default strides use `LayoutLeft` (left-to-right exclusive prefix products); `LayoutRight` uses right-to-left exclusive prefix products (which matches row-major only at depth 1: on `(2,(2,2))`, `LayoutRight` gives `(4,(2,1))` while `LayoutLeft` gives `(1,(2,4))`). Codomain size is `cosize(L) = L(size(L) - 1) + 1` (`01_layout.md:103`), matching $\max_i L(i) + 1$ for non-negative strides.

#### 1.2 Core Algebraic Operations and Postconditions

| Operation | Definition (`layout.hpp`, `02_layout_algebra.md`) | Checked Postconditions | Kernel Role |
| :--- | :--- | :--- | :--- |
| **`coalesce(L)`** | Flatten and fold adjacent pairs: `s0:d0 ++ 1:d1 => s0:d0`, `1:d0 ++ s1:d1 => s1:d1`, `s0:d0 ++ s1:s0*d0 => s0*s1:d0`, else keep pair (`L867`). | `size(R)==size(L)`, `depth(R)<=1`, $\forall i < |L|,\; R(i)=L(i)$. By-mode `coalesce(L, profile)` preserves top-level rank. | Simplifying address math; detecting contiguous stride-1 vector runs. |
| **`filter(L)`** | Drop `shape==1` and `stride==0` modes, then `coalesce` (`L938`). | Removes broadcast/singleton dimensions before `complement`. | Isolating injective footprint. |
| **`composition(A, B)`** | $R := A \circ B$ with $R(c) = A(B(c))$. Left-distributes over tuple `B` (`L1036-1039`), folds coalesced `A` against integral `s:d` (`L1051-1125`). By-mode for `Tiler`/`Shape`. | `compatible(B, R)` and $\forall i < |B|,\; R(i) = A(B(i))$ **iff exact admissibility & no cross-mode carries hold** (§1.3). | Thread-to-value partitioning, 1-D reshaping, strided sub-tensors. |
| **`complement(A, M)`** | Sort filtered `(stride, shape)` ascending; insert gaps `min_stride / curr` at stride `curr`, update `curr = shape * min_stride`; append `ceil_div(M, curr)` at `curr`; coalesce (`L1182-1287`). | `cosize(A, R) >= M`; strictly increasing $\forall i \in [1, |R|),\; R(i-1) < R(i)$; disjoint $\forall i \in [1, |R|), j \in [0, |A|),\; R(i) \neq A(j)$ ($i \ge 1$ since $R(0)=A(0)=0$). | Computing the "rest" layout of tiles/repetitions not touched by `A`. |
| **`logical_divide(A, B)`** | $A \oslash B := A \circ (B, B^*)$ with $B^* = \mathrm{complement}(B, |A|)$ (`L1599-1603`). | Mode 0 is tile $A \circ B$; mode 1 iterates tiles. `zipped_divide` / `tiled_divide` / `flat_divide` rearrange `((TileM,RestM),(TileN,RestN))`. | Partitioning GMEM/SMEM tensors into CTA, warp, and MMA tiles. |
| **`logical_product(A, B)`** | $A \otimes B := (A, A^* \circ B)$ (`L1693-1697`; doc/PyCuTe uses `cotarget = size(A)*cosize(B)`). | `rank(R)==2`, `compatible(A, R<0>)`, `compatible(B, R<1>)`. `blocked_product` / `raked_product` interleave modes for blocked vs. cyclic tiling. | Replicating TV layouts and SMEM swizzle atoms across shapes. |
| **`right_inverse(A)`** / **`left_inverse(A)`** | `right_inverse` (`L1305-1343`) collects sorted static modes with contiguous `istride == curr`; `left_inverse` (`L1364-1401`) asserts `(istride % size(result_shape)) == 0`. | `A(rinv(i)) == i`; `A(linv(A(i))) == A(i)` (left inverse when injective). | `max_common_vector(A,B) = shape<0>(coalesce(A o rinv(B)))` if `stride<0>==1` (`L1451-1466`) certifies 128-bit coalesced copies. |

#### 1.3 Exact Admissibility Theorem and Verified Soundness Gaps in CUTLASS

For coalesced LHS $A = (c_0, \dots, c_{k-1}) : (\delta_0, \dots, \delta_{k-1})$ and positive integral RHS $B = s : d$, $A \circ B$ is representable as a CuTe layout **iff** at each mode $i < k - 1$ during the left-to-right fold with remaining $(s, d)$:
1. **Trivial**: $s = 1$ or $d = 0$; or
2. **Non-wrapping**: $d < c_i$ and $(s - 1) \cdot d < c_i$ (all $s$ indices stay inside $[0, c_i)$, yielding $s : (d \cdot \delta_i)$); or
3. **Full skip**: $d \ge c_i$ and $c_i \mid d$ (advancing with $d' = d / c_i$); or
4. **Clean wrap**: $d < c_i$, $(s - 1) \cdot d \ge c_i$, **$d \mid c_i$** (resetting inner coordinate to `0` on wrap), **and** **$(c_i / d) \mid s$** (aligning mode split with $s$, advancing with $s' = s / (c_i / d),\; d' = 1$).

Direct source audit of `NVIDIA/cutlass` and execution in `support/verify_cute_algebra_and_swizzle_banks.py` expose three concrete discrepancies:

1. **Static-Assertion Gap on Wrapping Non-Divisible Strides (`include/cute/layout.hpp:1076-1111`)**:
   ```cpp
   CUTE_STATIC_ASSERT_V(((rest_stride % curr_shape) == Int<0>{}) or (rest_stride < curr_shape),
                        "Stride Divisibility Condition");
   // next_shape = ceil_div(curr_shape, abs(rest_stride)); // (a + b - 1) / b (int_tuple.hpp:344)
   // new_shape  = min(next_shape, rest_shape);
   CUTE_STATIC_ASSERT_V(((rest_shape % new_shape) == Int<0>{}),
                        "Shape Divisibility Condition");
   ```
   Relaxing `curr_shape % rest_stride == 0` to `rest_stride < curr_shape` enables Case 2 (`(4,4):(1,8) o 2:3 = 2:3`), **but omits `curr_shape % rest_stride == 0` in Case 4 when wrapping (`rest_shape > next_shape`)**.
   - **Counterexample**: $A = (4, 4) : (1, 8)$, $B = 4 : 3$. Both static assertions pass (`3 < 4`; `next_shape = ceil_div(4, 3) = 2`; `4 % 2 == 0`), emitting $R = (2, 2) : (3, 8)$. Yet $R(2) = 8 \neq 10 = A(6)$ and $R(3) = 11 \neq 17 = A(9)$. By contrast, `pycute/layout.py:211` checks `curr_shape % rest_stride == 0 or rest_stride % curr_shape == 0`, rejecting `(4,4):(1,8) o 4:3` (and conservatively also rejecting non-wrapping `(4,4):(1,8) o 2:3`).
2. **Falsification of Injectivity-Implies-Left-Distributivity (`02_layout_algebra.md:132`, `layout.hpp:1036-1039`)**:
   Left-distributivity $A \circ (B_0, B_1) = (A \circ B_0, A \circ B_1)$ fails even for **strictly injective** $B$ if $B$ is **untractable**.
   - **Counterexample**: $A = (4, 4) : (1, 8)$ and $B = (2, 2) : (1, 3)$ (image $\{0, 1, 3, 4\}$, strictly injective). Each 1-D mode is exact ($A \circ 2:1 = 2:1$, $A \circ 2:3 = 2:3$), so left-distributivity yields $R = (2, 2) : (1, 3)$. At $(1, 1)$, however, $B_0(1) + B_1(1) = 1 + 3 = 4$ carries across mode-0 bound $c_0 = 4$ of $A$, giving $R(1, 1) = \mathbf{4} \neq \mathbf{8} = A(4) = A(B(1, 1))$. Left-distributivity requires zero cross-mode carries, guaranteed by categorical tractability and mutual refinement (§2).
3. **Commented-Out Dynamic Checks & PyCuTe Bug**: Dynamic assertions in `layout.hpp:1078-1081,1102-1105` are commented out (silently emitting wrong layouts at runtime for dynamic non-divisible inputs). Separately, `python/pycute/layout.py:315-316` erroneously implements `logical_product(layoutA, int)` by calling `logical_divide(layoutA, Layout(layoutB))` (unlike C++ `layout.hpp:1711`).

---

### 2. Categorical Foundations of CuTe Layouts: `Tuple`, `Nest`, Tractability, and Mutual Refinement

Basis: source + documentation + execution + derived

Carlisle, Shah, Stern, and VanKoughnett (`arXiv:2601.05972v1`; `ColfaxResearch/layout-categories`, `tract/src/tract/{categories.py,layout_utils.py}`) formalize the tractable fragment of CuTe via three categories:

1. **$\mathcal{E}_0 = \mathcal{E}_0^\otimes$ (`Fin_morphism`, `categories.py:24-170`)**: Finite pointed sets $\langle m \rangle_* = \{*, 1, \dots, m\}$ with maps $\alpha$ preserving $*$ (`0`, representing stride-0 broadcast) and **injective on nonzero elements**. Disjoint-image maps admit wedge sums $\alpha \vee \beta$.
2. **$\mathbf{Tuple}$ (`Tuple_morphism`, `categories.py:550-1150`)**: Objects are positive integer tuples $S = (s_1, \dots, s_m)$; morphisms $f : S \to T$ lie over $\alpha : \langle m \rangle_* \to \langle n \rangle_*$ with $s_i = t_{\alpha(i)}$ whenever $\alpha(i) \neq 0$. The realization functor (`compute_flat_layout`, `layout_utils.py:205-232`) assigns stride $d_i = 0$ if $\alpha(i) = 0$ else $\prod_{j < \alpha(i)} t_j$. For example, $A = (6, 2) : (8, 2)$ corresponds to $f : (6, 2) \to (2, 2, 2, 6)$ with $\alpha = (4, 2)$ (verified in probe).
3. **$\mathbf{Nest}$ (`Nest_morphism`, `categories.py:177-544`, `layout_utils.py:280-315`)**: Arbitrarily nested tuples ordered by **refinement** (`NestedTuple.refines`: $S = T$, or $T = |S|$, or mode-wise refinement).

**Exact Tractability Characterization (`is_tractable`, `layout_utils.py:114-135`)**: A layout $L$ arises from a $\mathbf{Tuple}$/$\mathbf{Nest}$ morphism **iff**, after flattening and sorting by `(stride, shape)`, every nonzero consecutive pair satisfies $(s_i \cdot d_i) \mid d_{i+1}$.
- **Untractable Complement Counterexample**: $L = (2, 3) : (1, 3)$ is injective (image $\{0, 1, 3, 4, 6, 7\}$) yet untractable ($2 \cdot 1 = 2 \nmid 3$). `complement_prefix` (`layout.hpp:1198`) truncates `3 / 2 = 1`, emitting `complement(L, 12) = 2:9`; the combined layout `((2,3),2):((1,3),9)` permanently omits holes $\{2, 5\}$ (verified in probe), breaking `logical_divide`/`logical_product` partition invariants.

**Weak Composition via Mutual Refinement (`layout_utils.py:360-486`)**: Given $f : S \to T$ and $g : U \to V$ in $\mathbf{Nest}$, `mutual_refinement(T, U)` greedily factorizes flattened entries whenever one divides the other to construct $(T', U')$ refining $(T, U)$ with $T'$ a prefix of $U'$. `weak_composite(f, g)` forms $g' \circ \iota \circ f'$ via pullback of $f$ along $T'$, prefix inclusion $\iota : T' \hookrightarrow U'$, and pushforward of $g$ along $U'$, guaranteeing exact functional composition $L_{g' \circ \iota \circ f'}(c) = L_g(L_f(c))$ with zero carry errors, while `Tuple_morphism.complement` (`categories.py:1133-1150`) is exact whenever $0 \notin \mathrm{im}(\alpha)$.

---

### 3. $\mathbb{F}_2$ XOR-Swizzle Morphisms, Hybrid $(\mathbb{Z} \times \mathbb{F}_2)$ Layouts, and Algebraic 32-Bank SMEM Proofs

Basis: normative + source + execution + derived

NVIDIA GPU shared memory (Volta–Blackwell) has **32 four-byte banks**: byte address `addr` maps to word $w = \lfloor \mathrm{addr}/4 \rfloor$ and bank $b = w \bmod 32 = \mathrm{addr}[6:2]$. Simultaneous warp reads to identical words broadcast free; $k$ reads to distinct words in the same bank serialize $k$-way.

#### 3.1 Presburger/Affine Impossibility vs. $\mathbb{F}_2$ Hardware Swizzling
Affine/polyhedral compilers (`MLIR Affine`, `Polly`, `Halide`) model index maps over $(\mathbb{Z}, +, \cdot)$ and can eliminate conflicts only via padding (e.g., stride 33 on a 32-wide tile), which wastes SRAM and breaks 16-byte alignment required by 128-bit vector loads and TMA descriptors (`copy_traits_sm90_tma.hpp:978-984`). Bitwise XOR ($\oplus$) is non-linear over $\mathbb{Z}$ yet linear over $\mathbb{F}_2 = \mathrm{GF}(2)$ with zero carry propagation in hardware.

#### 3.2 CuTe `Swizzle<B, M, S>`, `MixedBits`, and Hopper/Blackwell TMA & `wgmma` Atoms
In `include/cute/swizzle.hpp:54-131`, `Swizzle<B, M, S>(x) = x ^ shiftr(x & yyy_msk, S)` with `yyy_msk = ((1 << B) - 1) << (M + max(0, S))` and `zzz_msk = ((1 << B) - 1) << (M - min(0, S))`.
- **Involution Precondition (`swizzle.hpp:61-63`)**: `M >= 0`, `B >= 0`, and **`abs(S) >= B`** guarantees disjoint masks ($\mathrm{yyy\_msk} \mathbin{\&} \mathrm{zzz\_msk} = 0$), so `YYY` bits are unaltered and $S(S(x)) = x$ (bijection on $[0, 2^{B+M+|S|})$). Two swizzles compose into a single `Swizzle` only when `S0 == S1` (`swizzle.hpp:119-131`).
- **Pre-Swizzle Offset & `MixedBits` (`swizzle.hpp:148-300`, `swizzle_layout.hpp:38-260,460-544`)**: Because $S(a + b) \neq S(a) + S(b)$ over $\mathbb{Z}$, `ComposedLayout<Swizzle<B,M,S>, Offset, LayoutB>` retains `Offset` via `MixedBits<StaticInt, StaticFlags>` (disjoint static/dynamic bit masks `(StaticInt & StaticFlags) == 0`), decaying to a plain strided `Layout` when slicing lands inside `Swizzle`'s identity subdomain. Vectorization width `max_common_vector` clamps to $\min(\mathrm{vec}, 2^{M_0}, 2^{M_1})$ when swizzles differ because only the low $M$ bits remain contiguous.
- **Byte-Addressed `smem_ptr_flag_bits<B>` & SM90/SM100 TMA/GMMA Atoms (`pointer_flagged.hpp:50-84`, `mma_traits_sm90_gmma.hpp:75-122`, `copy_sm90_desc.hpp:260-283`)**:

| Hopper/Blackwell Atom (`mma_traits_sm90_gmma.hpp:75-84`) | Byte Swizzle | Bit-Unit Inner Layout (MN / K) | Hardware TMA Enum (`copy_sm90_desc.hpp:260-283`) |
| :--- | :--- | :--- | :--- |
| `Layout_{MN,K}_INTER_Atom` | `Swizzle<0,4,3>` | `(128,8):(1,128)` / `(8,128):(128,1)` | `CU_TENSOR_MAP_SWIZZLE_NONE` (16B base) |
| `Layout_{MN,K}_SW32_Atom` | `Swizzle<1,4,3>` | `(256,8):(1,256)` / `(8,256):(256,1)` | `CU_TENSOR_MAP_SWIZZLE_32B` (16B base) |
| `Layout_{MN,K}_SW64_Atom` | `Swizzle<2,4,3>` | `(512,8):(1,512)` / `(8,512):(512,1)` | `CU_TENSOR_MAP_SWIZZLE_64B` (16B base) |
| `Layout_{MN,K}_SW128_Atom` | `Swizzle<3,4,3>` | `(1024,8):(1,1024)` / `(8,1024):(1024,1)` | `CU_TENSOR_MAP_SWIZZLE_128B` (16B base); CUDA 12.7+ adds `128B_ATOM_{32B,64B}` (`M=5,6`) |

Crucially, `upcast<N>(ComposedLayout<SwizzleFn, smem_ptr_flag_bits<B>, Layout>)` (`pointer_flagged.hpp:73-76`) scales only `smem_ptr_flag_bits<B*N>` and `layout_b()`, keeping `SwizzleFn` invariant in **byte units** ($2^4 = 16$ bytes = 4 banks = 1 TMA/wgmma atom) until `make_tensor` checks `B == sizeof_bits<Type>` and attaches `SwizzleFn` to `smem_ptr<Type>`.

#### 3.3 Triton's Pure $\mathbb{F}_2$ `LinearLayout` vs. CuTe
Triton (`include/triton/Tools/LinearLayout.h:20-320`, attributed to Adam P. Goucher) defines layouts as $\mathbb{F}_2$-linear maps $L : \mathbb{F}_2^M \to \mathbb{F}_2^N$ from hardware coordinates `(register, lane, warp, block)` or `(offset, block)` to tensor indices `(dim0, ...)` satisfying $L(x \oplus y) = L(x) \oplus L(y)$, fully specified by power-of-two basis columns.
- **Exact Equivalence**: `SwizzledSharedEncodingAttr` (`TritonGPUAttrDefs.td:28-118`) maps $(r, c) \mapsto (r,\; ((c/\mathrm{vec}) \oplus ((r/\mathrm{perPhase}) \bmod \mathrm{maxPhase})) \cdot \mathrm{vec} + (c \bmod \mathrm{vec}))$; probe execution confirms `(vec=8, perPhase=1, maxPhase=8)` on `8x64 f16` matches CuTe `Swizzle<3,3,3>` (byte `Swizzle<3,4,3>`) on every element.
- **Duality**: `LinearLayout` unifies swizzling, broadcasting (non-injective, surjective hardware$\to$tensor maps), inversion (`invertAndCompose`), minimum-transfer conversion (`minimalCvtLayout`), and automated conflict-free SMEM synthesis—but **cannot represent non-power-of-two shapes or padded shared memory** (`LinearLayout.h:301`, `LinearLayoutConversions.h:58-70`: `paddedLinearLayout`, `toLinearLayoutIgnoringPadding`).

#### 3.4 $\mathbb{F}_2$ Matrix-Rank Certification of 0-Way Bank Conflicts
As an $N \times N$ bit-matrix $M \in \mathrm{GL}_N(\mathbb{F}_2)$ (identity plus $B$ off-diagonal entries $(z_k, y_k)$), mask disjointness implies $(M - I)^2 = 0 \implies M^2 \equiv I \pmod 2$ ($\det_{\mathbb{F}_2}(M) = 1$, proving bijectivity). For a 32-lane warp ($t \in \mathbb{F}_2^5$) accessing distinct 4-byte words with $\mathbb{F}_2$-affine bank map $b(t) = A t \oplus b_0$ ($A \in \mathbb{F}_2^{5 \times 5}$), $|\ker(A)| = 2^{5 - \mathrm{rank}_{\mathbb{F}_2}(A)}$, giving exact serialization factor $W_{\text{conflict}} = 2^{5 - \mathrm{rank}_{\mathbb{F}_2}(A)}$ (**0-conflict iff $\mathrm{rank}_{\mathbb{F}_2}(A) = 5$**, decidable in $O(1)$ Gaussian elimination). Execution receipts (`support/verify_cute_algebra_and_swizzle_banks.py`):

| Tile & Access Pattern | Unswizzled Row / Col Ways | Col $\mathrm{rank}_{\mathbb{F}_2}$ (Unswiz $\to$ Swiz) | Byte Swizzle | Swizzled Row / Col Ways | Involution $M^2=I$ & Bijection |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `32x32 f32` (128B/row, 4096B) | `1-way` / **`32-way`** | `0` $\to$ **`5`** | `Swizzle<5,2,5>` | **`1-way` / `1-way`** | Verified $\mathrm{GL}_{12}(\mathbb{F}_2)$ & all 4096B |
| `32x32 f16` (64B/row, 2048B) | `1-way` / **`16-way`** | `1` $\to$ **`5`** | `Swizzle<4,2,5>` | **`1-way` / `1-way`** | Verified $\mathrm{GL}_{11}(\mathbb{F}_2)$ & all 2048B |
| Hopper `8x64 f16` `SW128` (`ldmatrix` 8-row $\times$ 16B) | `1-way` / **`8-way`** | Full 32-bank phase | `Swizzle<3,4,3>` | **`1-way` / `1-way`** | Verified $\mathrm{GL}_{10}(\mathbb{F}_2)$ & Triton match |

---

### 4. Systolic Scratchpad and Asynchronous DMA Pipelines: Google TPU and JAX `Pallas`/`Mosaic`

Basis: normative + documentation + source + derived

Google TPUs are decoupled sequential VLIW-like vector/systolic machines with software-managed SRAM scratchpads and no hardware data cache (`jax-ml/jax`, `docs/pallas/tpu/{details.rst,pipelining.md,matmul.md}`, Jouppi et al. ISCA '23).

- **TPU v4 Microarchitecture & Memory Spaces (`mosaic/core.py:287-375`)**: Each TPU v4 chip houses **two TensorCores** (or fused "Megacore" sharing HBM), each containing **four $128 \times 128$ systolic MXUs** (`bf16` inputs $\to$ `f32` accumulation; default `f32` matmul rounds to `bf16` unless `float32` precision is requested, `details.rst:292-298`), a 128-lane VPU with **`8 x 128` 32-bit VREGs**, an `XLU` transpose/permute unit, a scalar core, **16 MiB `VMEM`** per core (32 MiB/chip), **128 MiB chip-shared `CMEM`**, and two embedding **SparseCores**; pods (4,096 chips) use Optical Circuit Switches (OCSes) over a reconfigurable 3D torus ICI. Pallas exposes `MemorySpace.{HBM, VMEM, VMEM_SHARED, SMEM, CMEM, SEMAPHORE}`, `AccMemorySpace(mxu_id)`, and `SemaphoreType.{REGULAR, DMA, BARRIER}`. Buffers in `HBM` (`pl.ANY`) cannot be directly indexed by vector instructions and must be DMA-staged into `VMEM` (4 KiB tile granularity) or `SMEM` (32-bit random-access scalar SRAM for control flow and block-sparse `BlockSpec` indices, `details.rst:210-253`).
- **`(8, 128)` Trailing Sublane/Lane Tiling & Padding Cliff (`details.rst:75-80,125-160,300-395`)**: Trailing two `BlockSpec` dimensions must be divisible by `8` and `128` (or equal the full array axis). Trailing shapes pad up to `(8, 128)`, making `8x128x1x1` addition **$1024\times$ costlier** than `8x128`. Reshapes/transposes/broadcasts on leading axes are free compile-time metadata, whereas operations touching the trailing two axes incur `XLU` shuffles or compile-time rejection.
- **Sequential Grid Semantics & `emit_pipeline` (`details.rst:89-209`, `pipelining.md:148-249`)**: Single-core grids execute sequentially in lexicographic order, allowing consecutive iterations sharing an input tile to skip redundant DMAs and consecutive reduction iterations (placed on trailing grid axes) to accumulate into an output `VMEM` tile without races. Multi-core `TensorCoreMesh` partitions only leading `pltpu.PARALLEL` axes (followed by `pltpu.ARBITRARY`). `pltpu.emit_pipeline` composes nested ICI + HBM$\leftrightarrow$VMEM pipelines with `pl.Buffered(buffer_count, use_lookahead=...)` (default `2`) and dynamic `pl.BoundedSlice(max_size)` / `pl.ds(start, size)`.
- **Async DMA & Hazard Verification Gaps (`mosaic/primitives.py:219-310,1778-1825`)**: `AsyncCopyDescriptor` (`.start()`, `.wait()`, `.wait_read()`, `.wait_write()`) enforces paired `src_sem`/`dst_sem` on remote ICI copies at runtime (`L232-239`), but detects dropped/unawaited descriptors **only via a Python `__del__` `logging.error`** (`L241-247`)—not static linearity—leaving in-flight read/write races unchecked by the type system. Performance hints (`no_store`, `no_bank_conflict`, `no_hazard`, `no_hazard_no_deps`) explicitly disable compiler hazard/dependency tracking without static proof.

---

### 5. Block-SPMD Compilation (`Triton`) and Uniqueness-Typed Incremental Flattening (`Futhark`)

Basis: source + documentation + derived

#### 5.1 Triton Block-SPMD (`TritonGPU`) Layout & Pipelining Failure Surfaces
Triton (Tillet, Kung & Cox, MAPL '19; `triton-lang/triton`) operates on statically shaped tiles (`tl.load`, `tl.dot`, `tl.store`) lowered through the `TritonGPU` (`#ttg`) MLIR dialect (`TritonGPUAttrDefs.td`: `BlockedEncodingAttr`, `NvidiaMmaEncodingAttr`, `AMDMfmaEncodingAttr`, `AMDWmmaEncodingAttr`, `DotOperandEncodingAttr`, `SliceEncodingAttr`, `LinearEncodingAttr`, `SwizzledSharedEncodingAttr`, `NVMMASharedEncodingAttr` with Blackwell `Fp4`/`Fp6` `NVMmaPadding`, and `PaddedSharedEncodingAttr`). Three verified compiler soundness surfaces dominate:
1. **`RemoveLayoutConversions` (`RemoveLayoutConversions.cpp:44-56`)**: Propagates anchor layouts forward and backward-rematerializes index/mask slices (`LayoutRematerialization::rewriteSlice`) to avoid SMEM-mediated `ttg.convert_layout` ops. Recurring defects include **SSA dominance errors** (`operand #0 does not dominate this use`) when rematerialized slices cross `scf.for`/conditional region boundaries, **stale remap entries** when ops are erased without `updateRematMapping`, and **silent numerical miscompilations** during layout propagation across `ReduceOp` under multi-warp/Hopper MMA encodings.
2. **`SoftwarePipeliner` (`Pipeliner/{SoftwarePipeliner,ScheduleLoops,LowerLoops}.cpp`)**: Separates modulo scheduling from prologue/epilogue expansion and async Hopper/Blackwell MMA dot pipelining (`pipelineWgmma`, `hasMMAv5WaitsInLastStage` for `WaitBarrierOp`). `isSafeToPipeline` (`ScheduleLoops.cpp:37-50`) refuses loops with dependency distance $> 1$, outer loops, or embedded `ttg::BarrierOp`, `GridDependencyWaitOp`, `AssertOp`, or `PrintOp`. Wait-group or barrier-phase miscalculations cause silent races.
3. **Warp-Specialization Boundary**: Uniform block-SPMD does not naturally express Hopper/Blackwell asynchronous producer-consumer warp specialization (TMA producer warps feeding `wgmma`/`tcgen05` consumer warps via `mbarrier` rings), requiring specialized compiler passes (`Transforms/WarpSpecialization/`) or explicit lower-level DSLs (`CuTe DSL`, `Mosaic GPU`).

#### 5.2 Futhark: Uniqueness Types and Incremental Flattening
Futhark (Henriksen et al., PLDI '17, PPoPP '19; `diku-dk/futhark`) pairs purely functional SOACs (`map`, `reduce`, `scan`) with two mechanisms verified in source:
1. **Path-Sensitive Consumption & Alias Analysis (`src/Language/Futhark/TypeChecker/Consumption.hs:1-145`)**: Uniqueness annotations (`*[]f32`) permit sound, referentially transparent in-place array updates by statically forbidding any live alias after consumption. Aliases track leaf paths `Location = (VName, Path)` (`L62-66`) plus `AliasSelf` (`L68-87,130-139`) for internal aliasing inside opaque abstract types (blocking consumption without spuriously aliasing distinct `AliasSelf` values). Internal alias-parametric inference covers **fully saturated** higher-order calls only (`x |> copy` stays fresh; `id >-> copy` loses freshness, `L18-25`). Unlike Rust's lexically/NLL-scoped `&mut [T]` borrows (temporary exclusivity returning to shared access), Futhark uniqueness is consumption/move-based ownership without general sub-slice thread-borrowing.
2. **Regular vs. Uniform Nesting & Incremental Flattening (`Flatten.hs:30-93`, `Flatten/Incremental.hs:1-145`)**: `Flatten.hs` distinguishes *regular* (array shapes; ragged arrays are disallowed directly in Futhark IR) from *uniform* (map-nest-invariant sizes/control-flow; `#[flattening(sequentialise_nonuniform)]` opts out of nonuniform flattening). Rather than statically committing to flat vs. sequential execution of `map f xs`, `Incremental.hs` emits **multi-versioned GPU kernels** (outer-parallel with sequentialized tiled `f`, fully flattened `f`, and `Intrablock` shared-memory parallelized `f`) selected at runtime via `if predicate then sequentialise f else parallelise f` against auto-tuned parallelism thresholds (`sufficientParallelism`, `L90-135`).

---

### 6. Verified User-Schedulable and Exocompilation Languages: `Halide`, `ATL`, `Exo`/`Exo 2`, and `Rise`/`Elevate`

Basis: source + documentation + execution + derived

User-schedulable languages decouple *algorithm* from *schedule*, spanning four distinct verification models:

1. **Halide (`halide/Halide`, Ragan-Kelley et al. PLDI '13), SMT Translation Validation (Clément & Cohen OOPSLA '22), and Coq-Verified `ATL` (Liu et al. POPL '22)**:
   - Production Halide (`Schedule.h`, `Lower.cpp:192-609`) runs 50+ unverified lowering passes (bounds inference, sliding window, storage folding/flattening, GPU cross-talk checks, tensor-core extraction, warp shuffles, SME streaming tasks).
   - **Clément & Cohen (OOPSLA '22, `DOI 10.1145/3527328`)** perform **push-button translation validation** of affine Halide compilations independent of the scheduling language: the compiler attaches **"prophetic" refinement annotations** (Abadi–Lamport refinement mapping) to imperative array assignments, and an external validator discharges equivalence via a **specialized affine solver + Z3 (SMT)**—**not** Coq mechanization.
   - **ATL (Liu et al., POPL '22, `DOI 10.1145/3498717`)** provides the **Coq-verified** counterpart: a functional array language in Coq whose high-level scheduling rewrites (tiling, fusion, padding, guard elimination, reduction reordering) are kernel-checked in Coq prior to C extraction.
2. **`Exo` (PLDI '22) and `Exo 2` (ASPLOS '25) (`exo-lang/exo`)**:
   - **Externalized Hardware (`@instr`, `@config`, `Memory`)**: Accelerator instructions (e.g., Gemmini `ld_i8_block`, `matmul`, `acc_scale` in `src/exo/platforms/gemmini.py:279-565`) pair a LoopIR behavioral model with a C template matched by AST unification (`replace`); stateful registers (`@config`, e.g., `ConfigLoad`) are tracked and dead-eliminated (`delete_config`); scratchpad allocators subclass `Memory` (`src/exo/core/memory.py:81-203`, raising `MemGenError` on illegal direct reads/writes).
   - **Z3 Affine Effect Analysis (`src/exo/rewrite/new_eff.py`, `new_analysis_core.py:618-785`)**: Builds symbolic affine location sets (`LUnion`, `LIsct`, `LDiff`, `LBigUnion`, `LFilter`, `LLetEnv`, `LHideAlloc`) across `READ_H`, `WRITE_H`, `READ_G`, `WRITE_G`, `REDUCE`, and `ALLOC`. Crucially, `Commutes(a1, a2)` (`new_eff.py:1452-1463`, used by `Check_ReorderStmts`, `Check_ReorderLoops`, `Check_FissionLoop`) **permits $\mathrm{Red}_1 \cap \mathrm{Red}_2 \neq \emptyset$** (assuming algebraic associativity/commutativity of `+=`, which alters IEEE-754 rounding order), whereas `Disjoint_Memory(a1, a2)` (`L1438-1449`, used by `Check_ParallelizeLoop`) forbids concurrent reductions to the same address. `stage_mem(..., accum=True)` (`API_scheduling.py:1607-1652`) zero-initializes a scratchpad window and accumulates back strictly when the staged block only reduces into that window (all checks and negative counterexamples verified in `support/verify_cute_algebra_and_swizzle_banks.py`).
   - **Modulo-Config Equivalence Semi-Lattice (`src/exo/core/proc_eqv.py:1-55`)**: Tracks provenance $p \equiv_K q$ modulo hardware `@config` key set $K$ via union-find over $\mathrm{Unv}$ and $\mathrm{Unv} \setminus \{x_i\}$ (closed under monotonicity and meet), certifying `call_eqv`.
   - **Exo 2 Typed Cursors & Provenance Forwarding (`API_cursors.py:29-160`, `API.py:194-205`)**: Replaces brittle Exo 1 string patterns with typed AST cursors (`StmtCursor`, `BlockCursor`, `GapCursor`, `ForCursor`, `AllocCursor`, `ExprCursor`, `InvalidCursor`) translated across rewrite chains via `Procedure.forward(cur)` (composing each step's `_forward` map along `_provenance_eq_Procedure`).
   - **TCB & Unsafe Escape Hatches**: Exo trusts Z3, Python effect checking, FP reduction reassociation, `@instr` C templates and `Memory` subclasses (unverified against RTL/ISA), and exposes explicit unchecked bypasses in `API_scheduling.py`: `fission(..., unsafe_disable_checks=True)` (`L2032`), `fuse(..., unsafe_disable_check=True)` (`L2113`), `remove_loop(..., unsafe_disable_check=True)` (`L2156`), and `add_unsafe_guard(...)` (`L2324`).
3. **`Rise`/`Shine` and `Elevate` (Hagedorn et al., ICFP '20; `elevate-lang/elevate`, `rise-lang/shine`)**:
   - Schedules are composable typed functions `type Strategy[P] = P => RewriteResult[P]` (`elevate/core/package.scala:18`, `RewriteResult.scala:1-46`) built from `id`, `fail`, `seq` (`;`), `leftChoice` (`<+`), `try`, `repeat`, and traversals (`basic.scala:23-50`). Separating local equational identities from traversal control makes atomic rules directly amenable to proof-assistant mechanization (unlike imperative AST mutation), whereas Exo 2 cursors excel at direct stateful loop/buffer/config addressing.

---

### 7. Cross-System Comparison Matrix and Verification Design Blueprint

Basis: derived + source + documentation + execution

| System | Layout / Index Algebra | XOR Swizzle & Banking | Scratchpad & Async Concurrency | Verification & Scheduling Model | Primary Soundness Gap / TCB |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`CuTe` (CUTLASS 3/4)** | Hierarchical `(Shape, Stride)` over $\mathbb{Z}$ (`Tuple`/`Nest` for tractable subset) | External `Swizzle<B,M,S>` + `MixedBits` + byte `smem_ptr_flag_bits` | Explicit CUDA TMA + `mbarrier` + `wgmma` (unchecked lifetimes) | C++ templates + partial `CUTE_STATIC_ASSERT_V` | Wrapping-stride gap (`layout.hpp:1077`); untractable carry break; unchecked dynamic strides |
| **`Triton` (`TritonGPU`)** | Pure $\mathbb{F}_2$ `LinearLayout` (hardware$\to$tensor) + side-band padding | Native in `LinearLayout`; `SwizzledShared` & `NVMMAShared` | Compiler SMEM staging & modulo `Pipeliner/` | Unverified MLIR passes + IR type verifier | `RemoveLayoutConversions` dominance/remat/reduction bugs; pipeliner barrier races; no non-pow2 `LinearLayout` |
| **`JAX Pallas` / `Mosaic` (TPU)** | `(8, 128)` trailing sublane/lane VREG tiling + `BlockSpec` | N/A (2D tiled `VMEM` + `XLU`, not 32-bank GPU SMEM) | Sequential grid + `emit_pipeline` multi-buffering + `AsyncCopyDescriptor` + `SemaphoreType` | Compiler lowering + `InterpretParams()` differential oracle | Runtime `__del__` DMA leak warning only; unchecked `no_hazard*` hints; $1024\times$ padding cliff |
| **`Futhark`** | Regular ND arrays + flat index functions | Internal GPU codegen only | Pure SOACs + `*[]t` uniqueness in-place updates + `Incremental` multi-versioning | Sound alias/consumption typechecker (`Consumption.hs`); unverified backend | Saturated-HOF freshness loss (`id >-> copy`); no direct ragged IR arrays |
| **`Halide` + Clément & Cohen TV + `ATL`** | Affine loop nests + bounds inference (`Schedule.h`, `Lower.cpp`) | Unsupported (Presburger/affine $\mathbb{Z}$) | `compute_at`/`store_at`, sliding window, storage folding | Halide: unverified; C&C: prophetic **affine+Z3 TV**; ATL: **Coq-verified** | Halide pass/bounds bugs; TV trusts Z3 & affine subset; ATL covers high-level rewrites |
| **`Exo` / `Exo 2`** | Affine LoopIR windows & strides (`Memory.window`) | Unsupported in effect checker (opaque in `Memory`/`@instr`) | Explicit `stage_mem`, custom `Memory`, `@config` registers | Typed `Cursor`-forwarded rewrites + **Z3 affine effects** + `proc_eqv` lattice | Trusts Z3, `@instr` C templates, `Memory`, FP reassociation; `unsafe_disable_checks` hatches |
| **`Rise` / `Elevate`** | Functional combinators (`map`, `reduce`, `split`, `join`, `transpose`) | Lowered in `Shine` backend | Functional dataflow $\to$ OpenMP/OpenCL/CUDA | Typed strategies `Strategy[P] = P => RewriteResult[P]` | Unverified rule set & `Shine` imperative backend lowering |

**Four-Layer Verified Accelerator IR Blueprint**:
1. **Hybrid $(\mathbb{Z} \times \mathbb{F}_2)$ Layout Layer**: Enforce `Nest` tractability $(s_i d_i) \mid d_{i+1}$ and mutual refinement for arbitrary-shape striding/padding, composed with $\mathrm{GL}_N(\mathbb{F}_2)$ swizzles certified conflict-free via $O(1)$ Gaussian elimination ($\mathrm{rank}_{\mathbb{F}_2}(A) = 5$) and $M^2 = I$.
2. **Linear Scratchpad/DMA Typestate Layer**: Replace runtime-logged `AsyncCopyDescriptor` / unchecked `mbarrier` calls with linear tokens `Idle -> InFlight(src_borrow, dst_mut, sem) -> Ready` across TPU `VMEM`, GPU `TMA`, and systolic scratchpads.
3. **Proof-Carrying Rewrite Kernel**: Combine `Exo 2` typed cursors and modulo-config equivalence with `ATL`/`Elevate` kernel-checked rules and explicit opt-in floating-point reassociation.
4. **ISA-Anchored Intrinsics**: Verify `@instr` specifications against formal ISA/PTX semantics rather than trusting C code-generation templates as axioms.

## Boundaries

- **not examined**:
  - NVIDIA Blackwell `tcgen05.mma` / `TMEM` allocation protocols beyond observed `TritonGPU` `HoistTMEMAlloc.cpp` / `NVMMASharedEncodingAttr` signatures and CUDA 12.7+ `CU_TENSOR_MAP_SWIZZLE_128B_ATOM_{32B,64B}` enums.
  - AMD CDNA/RDNA LDS rotating-shared-memory banking (`AMDRotatingSharedEncodingAttr`) and `MFMA`/`WMMA` register layouts beyond attribute presence in `TritonGPUAttrDefs.td`.
  - Exact floating-point rounding/accumulation tree order inside TPU `MXU` systolic arrays relative to scalar IEEE-754 dot products (not specified in inspected JAX Pallas or TPU v4 sources).
  - Coq proof scripts of `ATL` (POPL '22) and the validator source code of Clément & Cohen (OOPSLA '22), which were characterized from peer-reviewed publications rather than source checkouts.
  - `Descend` (PLDI '24) GPU borrow-checker internals and `Fireiron` (PACT '20).
- **unknown**:
  - Whether upstream `NVIDIA/cutlass` plans to tighten `include/cute/layout.hpp:1077` against wrapping non-divisible static compositions (`(4,4):(1,8) o 4:3`) or treats tractability as an external caller obligation.
  - Whether `triton-lang/triton` will generalize `LinearLayout` to an affine-plus-$\mathbb{F}_2$ hybrid handling `PaddedSharedEncodingAttr` natively or retain `toLinearLayoutIgnoringPadding`.
- **known not to apply**:
  - Pure $\mathbb{F}_2$ `LinearLayout` completeness does not apply to non-power-of-two shapes or padded shared memory (`LinearLayout.h:301`, `LinearLayoutConversions.h:58-70`).
  - CuTe's informal injectivity-implies-left-distributivity statement (`02_layout_algebra.md:132`) does not apply to untractable injective layouts (`(4,4):(1,8) o (2,2):(1,3)` counterexample).
  - Exo's `Commutes` reduction commutativity (`new_eff.py:1452-1463`) does not preserve bit-exact IEEE-754 floating-point rounding.
  - Pallas single-core sequential grid accumulation does not apply across `PARALLEL` axes on multi-core `TensorCoreMesh` (`details.rst:164-200`).
- **unsupported**:
  - Bitwise XOR swizzling in Presburger/affine polyhedral IRs (`MLIR Affine`, `Halide`, `Exo` effect analysis).
  - Multi-rank dynamic-stride `complement` (`layout.hpp:1185-1186`) and dynamic-stride `left_inverse` (`layout.hpp:1375`) in CUTLASS C++.
  - Direct `HBM` (`pl.ANY`) vector indexing (`pipelining.md:105`), integer reductions (`details.rst:371`), and `jnp.int4` (`details.rst:260-266`) in Pallas TPU.
  - `TritonGPU` software pipelining on loops with dependency distance $> 1$, outer loops, or embedded barriers/asserts/prints (`ScheduleLoops.cpp:37-50`).
  - Direct ragged (irregular) multidimensional arrays in Futhark IR (`Flatten.hs:36-38`).

## Evidence

All source inspections and probe executions were performed on `2026-11-19`.

| Durable Subject | Immutable Identity | Inspected Paths & Symbols / Line Ranges |
| :--- | :--- | :--- |
| `NVIDIA/cutlass` | `dc6ae46eb5a735a0c2cf96c0b06196caadf8ea31` | `include/cute/layout.hpp` (`L867-886,938,1033-1161,1182-1287,1305-1466,1599-1712`), `int_tuple.hpp` (`L326-345`), `swizzle.hpp` (`L54-131,148-300`), `swizzle_layout.hpp` (`L38-260,348-436,460-544`), `pointer_flagged.hpp` (`L50-84`), `atom/mma_traits_sm90_gmma.hpp` (`L75-122`), `atom/copy_traits_sm90_tma.hpp` (`L929-1065`), `arch/copy_sm90_desc.hpp` (`L260-283`), `media/docs/cpp/cute/{01_layout,02_layout_algebra}.md`, `python/pycute/{layout.py:51-367,swizzle.py:60-129}` |
| `ColfaxResearch/layout-categories` | `689369f8b9c61cbcf9aa81c20c83f0ad7cef9719` | `tract/src/tract/categories.py` (`Fin_morphism` `L24-170`, `NestedTuple` `L177-544`, `Tuple_morphism` `L550-1150`), `tract/src/tract/layout_utils.py` (`is_tractable` `L114-135`, `compute_Tuple_morphism` `L139-202`, `compute_flat_layout` `L205-232`, `mutual_refinement` `L360-433`, `weak_composite` `L460-486`) |
| `triton-lang/triton` | `458c1a257c026a24c6aa7937f75f186e9bdf8353` | `include/triton/Tools/LinearLayout.h` (`L20-320`), `include/triton/Dialect/TritonGPU/IR/{LinearLayoutConversions.h:23-210,TritonGPUAttrDefs.td:28-160,230,454-525,700,773,1308,1434}`, `lib/Dialect/TritonGPU/Transforms/{RemoveLayoutConversions.cpp:44-56,Pipeliner/SoftwarePipeliner.cpp:20-56,Pipeliner/ScheduleLoops.cpp:37-50}` |
| `jax-ml/jax` | `bb38c58379173719d63a7e81fc09c22a37502654` | `jax/_src/pallas/mosaic/{core.py:287-375,primitives.py:220-310,1778-1790}`, `docs/pallas/tpu/{details.rst:41-414,pipelining.md:55-265,matmul.md:46-356}` |
| `diku-dk/futhark` | `dc285f6698c118f2b236f65984e38104e72f7939` | `src/Language/Futhark/TypeChecker/Consumption.hs` (`L1-140`), `src/Futhark/Pass/Flatten.hs` (`L3-93`), `src/Futhark/Pass/Flatten/Incremental.hs` (`L1-140`) |
| `exo-lang/exo` | `defe17283d15553ca9d6ad70b2e9f4c22ff36ce2` | `src/exo/{API.py:190-206,API_cursors.py:29-160,API_scheduling.py:1607-1652,2032,2113,2156,2324}`, `core/{internal_cursors.py:55-82,memory.py:81-203,proc_eqv.py:1-55}`, `platforms/gemmini.py:279-565`, `rewrite/{new_eff.py:669-720,1438-1780,new_analysis_core.py:6-8,618-785}` |
| `halide/Halide` | `a92e31666d7272d3d7b76d0eccb95e8b2d23fa9c` | `src/Schedule.h` (`L35-726`), `src/Lower.cpp` (`L192-609`) |
| `elevate-lang/elevate` & `rise-lang/shine` | `0e60de5f1394d6d36e6cef94d13a3ca7d69b9ec5` & `1bd443b1b057d4a6ce46578fb680fced5009af4a` | `elevate/src/main/scala/elevate/core/{package.scala,RewriteResult.scala,strategies/basic.scala}` |

**Verified Publications**: Cecka (`arXiv:2603.02298v2`, `DOI 10.48550/arXiv.2603.02298`); Carlisle, Shah, Stern & VanKoughnett (`arXiv:2601.05972v1`, `DOI 10.48550/arXiv.2601.05972`); Tillet, Kung & Cox (MAPL '19, `DOI 10.1145/3315508.3329973`); Jouppi et al. (ISCA '23, `DOI 10.1145/3579371.3589350`, `arXiv:2304.01433`); Henriksen et al. (PLDI '17 `DOI 10.1145/3062341.3062354`; PPoPP '19 `DOI 10.1145/3293883.3295707`); Ikarashi et al. (PLDI '22 `DOI 10.1145/3519939.3523446`; Exo 2 ASPLOS '25 `DOI 10.1145/3669940.3707218`); Ragan-Kelley et al. (PLDI '13 `DOI 10.1145/2491956.2462176`); Clément & Cohen (OOPSLA '22 `DOI 10.1145/3527328`); Liu, Bernstein, Chlipala & Ragan-Kelley ATL (POPL '22 `DOI 10.1145/3498717`); Hagedorn et al. Elevate (ICFP '20 `DOI 10.1145/3408974`).

**Executable Verification Probe (`support/verify_cute_algebra_and_swizzle_banks.py`, Python 3.10+ stdlib only)**:
```console
python3 -B reports/tensor-layout-algebras-scratchpad-dma-and-user-schedulable-accelerator-languages/support/verify_cute_algebra_and_swizzle_banks.py
```
Exit code `0`, confirming: (a) CuTe `coalesce`/`composition`/`complement`/`logical_divide`/`logical_product`/`right_inverse`/`left_inverse`/`max_common_vector`, `TupleMorphism` round-trip `(2,2,2,6)` / `(4,2)`, untractable complement holes `[2, 5]`, CUTLASS C++ wrapping-stride mismatches `[(2, 8, 10), (3, 11, 17)]`, and injective-carry violation `(4, 8)`; (b) `32x32 f32` `(1,32) -> (1,1)` ($\mathrm{rank}: 0 \to 5$), `32x32 f16` `(1,16) -> (1,1)` ($\mathrm{rank}: 1 \to 5$), Hopper `SW128` `ldmatrix` `8 -> 1`, $M^2 = I$, and Triton/CuTe `SW128` element-wise equivalence; (c) Exo GEMM `(j, k)` reorder (`True`), wavefront `(1,-1)` rejection `(0,1,1,0)`, outer-`i` vs. inner-`k` parallelization (`True` vs. `(0,1)`), 4-tile `accum=True` GEMM exact match, and undersized window rejection.

## Revalidation

1. **Rerun the Self-Contained Probe**: Execute `python3 -B reports/tensor-layout-algebras-scratchpad-dma-and-user-schedulable-accelerator-languages/support/verify_cute_algebra_and_swizzle_banks.py` (exit `0` re-certifies all mathematical identities, counterexamples, $\mathbb{F}_2$ bank ranks, and affine schedule checks).
2. **Narrow Upstream Diffs When Bumping Pinned SHAs**:
   - **CUTLASS**: Diff `include/cute/layout.hpp` (`L1070-1115`, `composition_impl` divisibility checks), `pointer_flagged.hpp` (`smem_ptr_flag_bits`), `arch/copy_sm90_desc.hpp` (`to_CUtensorMapSwizzle`), and `python/pycute/layout.py` (`logical_product`).
   - **Triton**: Diff `LinearLayout.h`, `LinearLayoutConversions.h` (`toLinearLayoutIgnoringPadding`), `ScheduleLoops.cpp` (`isSafeToPipeline`), and `RemoveLayoutConversions.cpp`.
   - **JAX Pallas TPU**: Diff `jax/_src/pallas/mosaic/{core.py,primitives.py}` for linear DMA enforcement, `MemorySpace`/`SemaphoreType` changes, or hazard-hint changes, and `docs/pallas/tpu/details.rst` for new TPU tile geometries.
   - **Futhark & Exo**: Diff `Consumption.hs`, `Flatten/Incremental.hs`, `exo/rewrite/new_eff.py`, `exo/API.py` (`forward`), and `exo/API_scheduling.py` (`unsafe_disable_check*`).
3. **Full Re-Investigation Triggers**: Re-analyze from primary hardware/ISA docs if targeting non-power-of-two SRAM banking, hardware-enforced linear DMA tokens, or Blackwell `tcgen05` `TMEM` layout algebras distinct from `Swizzle<B, M, S>`.
