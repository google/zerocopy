# Rank-Polymorphic Array Languages and Sparse / Structured Tensor Compilers

## Summary

Dense rank-polymorphic array languages (APL, J, BQN, Uiua, Remora, Dex, Futhark) and sparse or spatially structured tensor compilers (TACO, MLIR `sparse_tensor`, Finch, Indexed Streams, Taichi, Scion) attack two faces of the same foundational compiler problem: **decoupling the logical index space of a finite map from its physical storage layout and co-iteration schedule, while making every structural invariant checkable at module and FFI boundaries.**

Key technical findings verified across upstream specifications, compiler sources, peer-reviewed proofs, and executable probes:

- **Leading-axis prefix agreement and trailing-axis broadcasting are mutually incompatible semantics.** Under J/BQN leading-axis theory, applying a rank-$k$ cell function decomposes an array's shape into a leading *frame* and trailing *cells* and requires the shorter frame to be a **prefix** of the longer. Under NumPy-style trailing broadcasting, shapes align on trailing axes and silently stretch length-1 axes. The two conventions reject different valid inputs (`(3,) op (3, 4)` vs. `(4,) op (3, 4)`) and silently diverge on `(3, 1) op (3,)` (shape `(3, 1)` under prefix agreement vs. an implicit `(3, 3)` outer-product expansion under trailing broadcasting).
- **Static shape, index-set, and size type systems eliminate runtime prototypes and bounds checks, while exposing a ragged-array / CSR unity.** Remora (ESOP 2014) statically types implicit rank-polymorphic frame lifting via dependent dimension/shape sorts and existential packaging for data-dependent shapes. Dex (ICFP 2021) generalizes indices from raw integers to arbitrary finite types implementing `interface Ix` (`size'`, `ordinal`, `unsafe_from_ordinal`), decoupling array-of-structures vs. structure-of-arrays layout from semantics and enabling parallelism-preserving autodiff via typed accumulation effects. NESL flattening, columnar list offsets, and CSR `indptr` share one mathematical object: a **compressed sparse level** governed by a single monotone-offset validity predicate.
- **Dense zero-copy array ABIs carry unchecked or actively violated validity invariants.** DLPack (`include/dlpack/dlpack.h`) defines strides in *element* units (and since DLPack v1.2 forbids `NULL` strides for `ndim != 0`), yet explicitly concedes that major producers (PyTorch, CuPy, TensorFlow, TVM) violate its documented 256-byte CUDA alignment contract. Neither DLPack nor the Arrow C Data Interface carries a machine-checked proof of strided in-bounds safety or non-aliasing across negative strides.
- **Sparse co-iteration compiles structured control flow via merge lattices, looplets, and Lean-verified indexed streams.** TACO (OOPSLA 2017) compiles per-mode formats (`dense`, `compressed`, `singleton`) via iteration graphs and merge lattices; MLIR's `SparseTensorEncodingAttr` lifts per-level storage properties (`compressed`, `loose_compressed`, `singleton`, `structured[n, m]`, `nonunique`, `nonordered`) into the tensor type; Indexed Streams (PLDI 2023) unifies sparse tensor contraction and relational joins in ~540 lines of **Lean**-verified compiler code; and Finch (CGO 2023 / OOPSLA 2025) lowers piecewise array structures (RLE, CSR, CSF, triangles, bands, padding) through a compositional **looplet** lattice (`Thunk`, `Sequence`, `Run`, `Switch`, `Spike`, `Jumper`, `Stepper`, `Lookup`) guarded by a compiler-enforced `declare`/`freeze`/`thaw` aliasing lifecycle.
- **Sparse skipping is unsound under IEEE-754 arithmetic, and unchecked sparse kernels silently corrupt results on non-canonical inputs.** Skipping unstored structural zeros in `x * 0.0` relies on the semiring annihilator axiom $x \cdot 0 = 0$, which is **false under IEEE-754**: `inf * 0.0 = nan`, `nan * 0.0 = nan`, and `-5.0 * 0.0 = -0.0` (distinct from `+0.0` via `atan2` and IEEE sign bits). Meanwhile, two-pointer merge-lattice kernels assume canonical sorted, duplicate-free indices (codified normatively in Binsparse v0.1.0 and tracked lazily via SciPy's `has_canonical_format`); passing unsorted or duplicated rows causes silent dropped entries rather than errors.
- **Spatial sparsity introduces allocation-on-write effects and completes the three-artifact separation law.** Taichi's hierarchical SNode trees (`dense`, `bitmasked`, `pointer`, `dynamic`) favor shallow, wide VDB/SPGrid-style branching over deep octrees, but implicit activation on write hides heap allocation inside assignments and lacks cross-backend portability (Metal sparse SNode support deprecated/removed in v1.3.0–v1.4.0). Scion (PLDI 2026) extends the decoupling principle specifically to **bounding volume hierarchies (BVHs)**, confirming the overarching architectural invariant: **logical structure, physical layout, and execution schedule are three separate, independently verifiable artifacts.**

## Applicability

This report synthesizes pinned primary source inspection, formal literature, and standalone executable reference probes across fourteen upstream repositories (`mlochbaum/BQN@0ae87a3763c2023b159410cc2ae1048a1768c184`, `uiua-lang/uiua@951a6a02a509d127a42de5396e0e67683027438c`, `jsoftware/jsource@19e16a988f3cf6ed48f73c28bb6dc06ca93d86e2`, `google-research/dex-lang@25e2e389b90403ae2f8d67fb6d52f47d23c439ee`, `jrslepak/Remora@1a831dec554df9a7ef3eeb10f0d22036f1f86dbd`, `diku-dk/futhark@dc285f6698c118f2b236f65984e38104e72f7939`, `dmlc/dlpack@6eca9e643fcf7e870b7a1c99ee7fb166c5c2c459`, `apache/arrow@931b9cccda5de68d48201dc2db50b6b6a9a72741`, `tensor-compiler/taco@0e79acb56cb5f3d1785179536256e206790b2a9e`, `finch-tensor/Finch.jl@7aa1ca1609054b94f3a1b56bb2221ae872513a10`, `llvm/llvm-project@0782b426c676c774d60a7825095768f682e9fd6d`, `scipy/scipy@cb78cffebeda622447bf19776883b9d5454b31da`, `GraphBLAS/binsparse-specification@28577ecb0eb72932e2887b18fa63019d73534106`, `taichi-dev/taichi@ba0e81dce559fb63a5958bf82feb1d00c55c02fe`), IEEE 754-2019, and the cited peer-reviewed papers.

How the subjects relate:

- **Dense array semantics and type systems:** BQN, J, Uiua, Remora, Dex, and Futhark are compared on rank/frame decomposition, array depth/fill semantics, grammar decidability, and static shape/index typing.
- **Zero-copy descriptors and sparse storage invariants:** DLPack, Apache Arrow C Data Interface, Binsparse v0.1.0, SciPy `_compressed.py`, and MLIR `SparseTensorEncodingAttr` are analyzed jointly as byte-level representation relations and validity predicates.
- **Sparse and spatial compilers:** TACO, MLIR sparsification, Indexed Streams, Finch.jl, Taichi, and Scion are examined as progressive generalizations of co-iteration and layout decoupling—explicitly noting that Scion applies strictly to BVH layouts (not octrees or bitmasked grids, which belong to Taichi SNodes).
- **Execution scope:** Neither `numpy`, `scipy`, Julia/Finch, TACO C++, nor BQN/Uiua native runtimes were installed in the observation environment; execution evidence comes from pure Python 3.13 reference probes (`probe_p2.py`) executing exact IEEE-754 double-precision operations, prefix vs. trailing shape rules, canonical CSR validation vs. unchecked two-pointer merge kernels, and affine strided-view bounds/aliasing tests. Dense GPU tile-layout algebras and user-schedulable accelerator languages (such as CuTe, Halide, Triton, and Exo) are intentionally excluded except as structural reference points for layout/schedule separation.

## Findings

### 1. Leading-Axis Theory vs. Trailing-Axis Broadcasting and the Array-Model Schism

#### 1.1 Frame/Cell Decomposition and Prefix Agreement vs. Trailing Broadcasting

Basis: documentation + source + execution

In leading-axis array languages (J, BQN, modern Dyalog APL, Uiua), applying a function $f$ of intrinsic cell rank $k$ to an array $A$ of shape $s = (d_0, \dots, d_{r-1})$ splits $s$ into two contiguous segments:
- the **frame** $(d_0, \dots, d_{r-k-1})$ (leading $r - k$ axes), and
- the **cell shape** $(d_{r-k}, \dots, d_{r-1})$ (trailing $k$ axes).

$f$ maps independently over every $k$-cell indexed by the frame. BQN's documentation (`mlochbaum/BQN@0ae87a3763c2023b159410cc2ae1048a1768c184`, `doc/leading.md` L5–48) states the core design rationale: *"it's best to make the primitives operate on initial axes, because the Rank modifier (`⎉`) then allows it to apply to later axes as well."* Operations such as Length (`≠`), Reverse (`⌽`), First Cell (`⊏`), Insert (`˝`), and Scan (`` ` ``) act uniformly on **major cells** (leading axis), while `Cells` (`˘`) and `Rank` (`⎉`) peel leading frame axes without transposing trailing structure.

When a dyadic function combines two operands with frames $F_1$ and $F_2$, two dominant ecosystems adopt incompatible agreement laws:
1. **Prefix frame agreement (J, BQN, Uiua):** One frame must be a **prefix** of the other ($F_1 \preceq F_2$ or $F_2 \preceq F_1$); no length-1 axis is implicitly stretched.
2. **Trailing-axis broadcasting (NumPy, PyTorch, TensorFlow, JAX):** Shapes are right-aligned on trailing axes, missing leading axes are padded with `1`, and any axis of length `1` is silently stretched to match the peer's extent.

**Execution probe (`probe_p2.py`, Section 2A, `Basis: execution`):** Evaluating both rules on identical shape pairs exposes systematic cross-boundary semantic inversion:

| Left Shape | Right Shape | Prefix Agreement (J / BQN) | Trailing Broadcasting (NumPy) | Semantic Conflict |
| :--- | :--- | :--- | :--- | :--- |
| `(3,)` | `(3, 4)` | **`(3, 4)`** (row-wise broadcast) | `BROADCAST ERROR` | Valid in J/BQN; error in NumPy |
| `(4,)` | `(3, 4)` | `RANK/SHAPE ERROR` | **`(3, 4)`** (column-wise broadcast) | Error in J/BQN; valid in NumPy |
| `(3, 1)` | `(3,)` | **`(3, 1)`** (matches prefix `(3,)`) | **`(3, 3)`** (silent outer expansion!) | Both succeed with **different shapes and element counts** |
| `(2, 3)` | `(2, 3, 4)` | **`(2, 3, 4)`** | `BROADCAST ERROR` | Leading batch/channel alignment mismatch |
| `(3, 4)` | `(2, 3, 4)` | `RANK/SHAPE ERROR` | **`(2, 3, 4)`** | Trailing batch/channel alignment mismatch |

The `(3, 1) op (3,)` case is the canonical silent broadcasting defect in numerical and ML code: subtracting a column vector `(n, 1)` from a 1D vector `(n,)` silently allocates an $O(n^2)$ matrix `(n, n)` under trailing broadcasting with length-1 stretching, whereas prefix agreement preserves `(n, 1)`.

#### 1.2 The Array-Model Schism, Empty Arrays, and Fill Elements

Basis: documentation + source

Array languages divide sharply over how scalars and nested arrays relate (`mlochbaum/BQN@0ae87a3763c2023b159410cc2ae1048a1768c184`, `doc/based.md` L11–50):
- **Flat model (APL\360):** Arrays contain only homogeneous scalars; no nested arrays.
- **Nested / "floating" model (APL2, Dyalog, GNU APL):** Everything is an array, and a rank-0 scalar containing an atom is *identical* to that atom (`≡ 3` equals `≡ ⊂ 3`). As BQN `doc/based.md` L47 points out, nested arrays **do not form an inductive type** because simple scalars contain themselves (`enclose(3) == 3`).
- **Boxed model (J, SHARP APL):** Boxing (`<`) creates an explicit opaque scalar container distinct from its contents, restoring well-founded depth at the cost of explicit unbox/box ceremony.
- **Based model (BQN):** Atoms (numbers, characters, functions, modifiers) have depth `0` and are **not arrays** (`doc/based.md` L17: *"an atom's not an array"*); arrays form a standard **inductive type** over atoms and arrays (`3` is an atom, `<3` is a depth-1 rank-0 unit array).

**Empty arrays and runtime fill prototypes (`mlochbaum/BQN`, `doc/fill.md` L5–60):** An empty array retains its full shape (`0×3` is distinct from `3×0`). Operations that pad or collapse empty arrays—Take (`↑`), computed-length Reshape (`⥊`), Nudge (`»`, `«`), Merge (`>`), Join (`∾`), and Rank/Cells over an empty frame—require a **fill element** (typically `0` for numbers or `' '` for characters). When no fill can be inferred (e.g., `3↑⟨⟩` or opaque block functions where speculative fill evaluation cannot run without risking side effects), BQN signals a runtime error (`doc/fill.md` L5–6, L23, L59). Structurally, runtime prototypes and fills are dynamically typed array languages reconstructing the **element type** that statically typed languages (Remora, Dex, Futhark) carry at compile time (`Basis: derived`).

#### 1.3 Context-Sensitive Grammars, Ambient Tolerance, and Tacit Stack Checking

Basis: documentation + source

Three historical APL/J traits obstruct ahead-of-time (AOT) compilation and equational verification:
1. **Context-sensitive parsing (`mlochbaum/BQN`, `doc/context.md` L7–45):** In APL and J, parsing `a b c d e` requires knowing at runtime whether each identifier denotes an array (noun), function (verb), monadic operator (adverb), or dyadic operator (conjunction). BQN achieves a **context-free grammar** while remaining dynamically typed by binding syntactic role to **identifier spelling** (`a` = subject, `B` = function, `_d` = 1-modifier, `_m_` = 2-modifier; `doc/context.md` L18–21, L34–45).
2. **Ambient dynamic parameters (`⎕IO`, `⎕CT`):** APL's index origin (`0` vs. `1`) and comparison tolerance (`⎕CT`) alter primitive semantics dynamically across call boundaries. Crucially, **tolerant equality ($|a - b| \le \epsilon \max(|a|, |b|)$) is not transitive**, breaking equivalence-class axioms required by hashing, deduplication, and set membership.
3. **Tacit array + stack unification (`uiua-lang/uiua@951a6a02a509d127a42de5396e0e67683027438c`):** Inspecting Uiua's `readme.md` (L6) and `src/check.rs` (L1–65) confirms that Uiua unifies leading-axis tacit array programming with a **statically stack-signature-checked concatenative VM**: `nodes_all_sigs` executes an abstract `VirtualEnv::from_nodes(nodes)` pass tracking both the main `env.stack` and the auxiliary `env.under` (inverse/under) stack, rejecting stack-height mismatches at compile time before evaluating rank-polymorphic array primitives.

---

### 2. Static Typing for Rank Polymorphism and Index Spaces: Remora, Dex, Futhark, and Named Axes

Basis: normative + documentation + source + derived

Static array type systems represent shape lifting, bounds safety, and layout invariance through four distinct mechanisms:

| System | Array Type Form | Frame / Rank Lifting | Data-Dependent Shapes | Index Safety & Layout Decoupling | Mutation / Effects |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Remora** (ESOP 2014; `jrslepak/Remora`) | Dependent `Array τ [d₁ ... dₙ]` over dimension/shape sorts | Built-in implicit leading-axis lifting captured statically in application rule | Existential shape packaging `(Σ [n] (Array τ [n]))` | Static shape equality via shape-concatenation constraint solving (ARRAY 2018) | Pure functional core |
| **Dex** (ICFP 2021; `google-research/dex-lang`) | Finite table `n => a` for any type `n` with `Ix n` | Explicit pointwise `for i:n. ...` over index-set types | Dependent records / existentials (`List a = Σ n. Fin n => a`) | **Zero bounds checks** by construction via `Ix` bijection; product/sum indices separate logical table from AoS/SoA | Typed effect rows including commutative monoidal accumulation (`Accum`) for parallel reverse-mode AD |
| **Futhark** (`diku-dk/futhark`) | Size-typed regular `[n][m]t` | Explicit `map`/`reduce` over leading dimensions; **regular arrays only** | Existential return sizes `?[n].[n]t` | Size-checked at FFI entry points; flattened GPU execution | Uniqueness types (`*[]t`) governing safe in-place updates |
| **Named Tensor Notation / PEP 646** | Axis-named tensor `T[batch, seq, dim]` / variadic `Array[*Ts]` | Broadcasting by matching axis *name* (order-independent) | Dynamic runtime check (PEP 646 lacks shape arithmetic) | Eliminates positional transpose bugs; axis names erased across C ABIs | Host-dependent |

**Dex's `Ix` abstraction (`google-research/dex-lang@25e2e389b90403ae2f8d67fb6d52f47d23c439ee`, `lib/prelude.dx` L315–355):** Inspecting Dex's prelude directly reveals the minimal index-set interface:

```dex
interface Ix(n|Data)
  size' : () -> Nat
  ordinal : (n) -> Nat
  unsafe_from_ordinal : (Nat) -> n
```

Every primitive finite domain (`Fin n`, `RangeFrom i`, `RangeFromExc i`, `RangeTo i`, products `(a, b)`, and sums `a | b`) implements `Ix`. Because any `i : n` maps bijectively into `[0, size n)`, indexing `tab.i` requires **no runtime bounds check**—the proof obligation moves once to the FFI boundary where an incoming machine integer is checked against `size n` before calling `unsafe_from_ordinal`. Note a verification boundary directly visible in `lib/prelude.dx` L318 and L336: the bijection laws (`ordinal (unsafe_from_ordinal k) == k` for `k < size n` and `unsafe_from_ordinal (ordinal i) == i`) are **assumed contracts rather than mechanically checked by Dex**, and `RangeFrom` carries `# TODO: need a way to indicate constructor as private` (L336).

**Regular vs. irregular nesting and the ragged-array / CSR identity:** NESL (Blelloch 1995) compiles arbitrarily nested irregular (ragged) sequences to flat data-parallel vectors via **flattening** using segment descriptors (offset arrays). Futhark (`docs/language-reference.rst`) explicitly restricts arrays to **regular** rectangular shapes to avoid flattening's space blowup on GPUs. Structurally, **a ragged 2D array's segment descriptor, an Apache Arrow `List` offsets buffer, and a CSR matrix's `indptr` array are the exact same data structure—a compressed sparse level—sharing the identical validity predicate** (`offsets[0] == 0`, monotone non-decreasing, `offsets[M] == data.len`).

---

### 3. Dense Array FFI Descriptors as Validity Predicates: DLPack, Arrow C Data, Python Buffer Protocol, and Fortran C Descriptors

Basis: normative + documentation + source + execution

Four major C-level array descriptor ABIs govern zero-copy interchange across languages and runtimes. Comparing pinned primary headers (`dmlc/dlpack@6eca9e643fcf7e870b7a1c99ee7fb166c5c2c459`, `include/dlpack/dlpack.h` L147–290; `apache/arrow@931b9cccda5de68d48201dc2db50b6b6a9a72741`, `docs/source/format/CDataInterface.rst` L82–330) alongside the Python Buffer Protocol (`Py_buffer`) and Fortran C Descriptors (ISO/IEC TS 29113 / Fortran 2018 `CFI_cdesc_t`) reveals mutually incompatible conventions and unchecked validity gaps:

| Property | DLPack (`DLTensor` / `DLManagedTensorVersioned`) | Apache Arrow (`ArrowArray` + `ArrowSchema`) | Python Buffer Protocol (`Py_buffer`) | Fortran C Descriptor (`CFI_cdesc_t`) |
| :--- | :--- | :--- | :--- | :--- |
| **Stride units** | **Elements** (`int64_t* strides`, L276) | Not strided (1D buffers + validity bitmaps + offsets) | **Bytes** (`Py_ssize_t *strides`) | **Bytes** (`CFI_index_t sm` per dim) |
| **NULL strides** | **Forbidden for `ndim != 0` since DLPack v1.2** (L277, L283–285); allowed before v1.2 | N/A | Allowed (means C-contiguous) | Always populated in `dim[rank]` |
| **Lower bounds** | Fixed `0` | Fixed `0` (with logical slice `offset`) | Fixed `0` | Arbitrary `lower_bound` per dimension |
| **Sub-byte & vector types** | `DLDataType{code, bits, lanes}` (L214–227): supports FP8/FP6/FP4 (`kDLFloat4_e2m1fn = 17U`) in **little bit-endian** packing (L211–212) | Bit-packed booleans & validity bitmaps; format strings (`c`, `i`, `f`, `+l` for lists, etc.) | `struct`-style format strings; byte-granular | Fortran intrinsic/C-interoperable types |
| **Device tag** | Closed `DLDevice{device_type, device_id}` enum (CPU, CUDA, ROCm, Metal, Vulkan, etc.) | Host CPU (Device Data Interface extends separately) | Host CPU only | Host CPU only |
| **Ownership / lifetime** | `deleter` callback on managed wrapper; unspecified calling thread | `void (*release)(struct ArrowArray*)` callback (L315); consumers **MUST NOT** inspect `private_data` (L317) | Producer `bf_releasebuffer` paired with `PyObject` refcount | Allocatable/pointer attribute + caller scope |
| **Alignment contract** | Header L236 claims **256-byte alignment**, then L239–243 **explicitly rescinds reliance** (*"CuPy, PyTorch, TensorFlow, TVM, perhaps others do not adhere... recommended to not rely"*) | Recommended 8/64-byte Arrow buffer alignment (not enforced in C struct) | Unspecified | C type alignment |
| **Zero-size data pointer** | Should be `NULL` (L259–260) | Buffer pointers may be `NULL` for empty/null-free buffers | Non-NULL or NULL if `len == 0` | `base_addr == NULL` for unallocated |

**Affine strided-view validity predicates (`Basis: derived + execution`):** A strided N-dimensional view $(b, \vec{d}, \vec{s})$ over a backing allocation of length $L$ elements is an affine map $\phi(i_0, \dots, i_{r-1}) = b + \sum_{k=0}^{r-1} i_k s_k$ over $0 \le i_k < d_k$. Zero-copy memory safety requires two decidable preconditions that none of the four C ABIs verifies or encodes:
1. **In-bounds validity (with negative strides):** If $\prod d_k = 0$, the view accesses zero elements; otherwise every index lies in $[0, L)$ iff:
   $$b + \sum_{s_k < 0} (d_k - 1) s_k \ge 0 \quad \text{and} \quad b + \sum_{s_k > 0} (d_k - 1) s_k < L.$$
2. **Non-aliasing (for mutable / unique views):** Two views $(b_1, \vec{d}_1, \vec{s}_1)$ and $(b_2, \vec{d}_2, \vec{s}_2)$ on the same buffer are disjoint iff the linear Diophantine system $b_1 + \vec{i}\cdot\vec{s}_1 = b_2 + \vec{j}\cdot\vec{s}_2$ has no integer solution in the bounding box (for 1D views, exact $O(\log \min(|s_1|, |s_2|))$ GCD/extended-Euclidean solvability check; for general N-D views, Presburger / integer linear programming or conservative GCD + bounding-interval checks).

As verified in `probe_p2.py` Section 2D (`Basis: execution`), a reversed 1D view `(base=7, shape=(8,), stride=(-1,), alloc=8)` is valid with exact range `[0, 7]`, whereas `base=6` underflows to `-1` (`False, (-1, 6)`), even/odd slices `(0,4,2)` and `(1,4,2)` are strictly disjoint (`False, []`), and stride-2 vs. stride-3 slices `(0,4,2)` and `(0,3,3)` alias at elements `[0, 6]`.

---

### 4. TACO, MLIR SparseTensor, and Indexed Streams: Level Formats, Merge Lattices, and Lean-Verified Co-Iteration

Basis: normative + documentation + source

#### 4.1 TACO Format Abstraction and Merge Lattices

TACO (Kjolstad, Kamil, Chou, Lugato & Amarasinghe, OOPSLA 2017, DOI `10.1145/3133901`; Chou, Kjolstad & Amarasinghe, OOPSLA 2018; Henry et al., OOPSLA 2021; `tensor-compiler/taco@0e79acb56cb5f3d1785179536256e206790b2a9e`) decouples concrete tensor algebra expressions from per-dimension storage formats:

- **Per-mode level formats (`include/taco/format.h` L21–90):** A `Format` pairs an ordered list of `ModeFormatPack` storage types (`ModeFormat::dense`, `ModeFormat::compressed`, `ModeFormat::singleton`, plus extensible custom `ModeFormatImpl` such as hash or banded formats) with a `modeOrdering` permutation. Standard formats are compositions of level primitives: CSR = `(dense, compressed)`, CSC = `(dense, compressed)` with ordering `[1, 0]`, DCSR = `(compressed, compressed)`, COO = `(compressed[nonunique], singleton)`, CSF = `(compressed, compressed, compressed)`.
- **Iteration graphs and merge lattices (`src/lower/merge_lattice.cpp` L22–75):** TACO constructs an **iteration graph** whose topological order must agree with the storage `modeOrdering` of every accessed tensor (non-concordant access requires transposition or workspace insertion). At each index variable $i$, `MergeLatticeBuilder` builds a finite **merge lattice** from the expression's iteration algebra:
  - **Multiplication (conjunction / intersection):** lattice has a single point requiring all sparse iterators to align (`cA == cB`); loop terminates as soon as *any* sparse operand exhausts.
  - **Addition (disjunction / union):** lattice has $2^k - 1$ points over $k$ sparse operands, emitting a main `while` loop merging all active operands followed by exhaustion loops over every non-empty subset of remaining operands.
- **Result assembly:** Because the output sparsity size is unknown ahead of numeric evaluation, TACO compiles sparse outputs via either two-phase symbolic-then-numeric assembly (Gustavson 1978) or temporary dense scatter workspaces (Kjolstad et al., CGO 2019).

#### 4.2 MLIR `SparseTensorEncodingAttr`: Lifting Level Formats into the Type System

Inspecting `llvm/llvm-project@0782b426c676c774d60a7825095768f682e9fd6d` (`mlir/include/mlir/Dialect/SparseTensor/IR/SparseTensorAttrDefs.td` L117–199; Bik et al., ACM TACO 2022) shows how TACO's format model becomes a first-class compiler type attribute:
- **Semantic `dimension` vs. storage `level` (L135–147):** Explicitly separates mathematical tensor axes (`dimensions`) from physical memory axes (`levels`) via affine dimension-to-level maps, enabling both higher-order block formats (BSR: 2 dimensions $\to$ 4 levels) and linearized lower-order formats.
- **Level types and structural property flags (L169–199):** Supports `dense`, `compressed` (compact `pos(i)..pos(i+1)-1` without holes), `loose_compressed` (explicit `lo(i)..hi(i)` allowing holes and out-of-order intervals), `singleton` (no siblings, AoS by default or `soa`), and `structured[n, m]` ($n:m$ hardware semi-structured sparsity). Crucially, every level is **ordered and unique by default** (L182–183), requiring explicit `nonunique` or `nonordered` flags when relaxing canonicality—directly encoding the merge-lattice preconditions inside the MLIR tensor type!

#### 4.3 Indexed Streams: Lean-Verified Unification of Sparse Tensors and Relational Joins

Kovach, Kolichala, Gu & Kjolstad (*Indexed Streams: A Formal Intermediate Representation for Fused Contraction Programs*, PLDI 2023, DOI `10.1145/3591268`) formalize sparse co-iteration as a minimal operational stream IR built on **four primitive stream operations** (`ready`, `skip`, `index`, `value`) that unifies sparse tensor algebra and worst-case-optimal relational joins (such as `A(i,k) * B(k,j)` and SQL/Datalog equi-joins). Critically, **the authors mechanically verified the core operational semantics and compiler correctness in the Lean theorem prover** (~540 lines of Lean code) against a functional denotational semantics, demonstrating that merge-lattice / stream-fusion compilers are directly amenable to mechanized kernel verification without sacrificing parity with TACO, SQLite, or DuckDB.

---

### 5. Finch Looplets: Co-Optimizing Structured Control Flow and Tensor Lifecycles

Basis: normative + documentation + source

While TACO's merge lattices excel at uniform point-wise sparsity, real scientific and graph tensors exhibit **piecewise structural patterns**: run-length encoding (RLE), upper/lower triangles, banded diagonals, blocks, padding, and short-circuiting control flow (`if`, `break`). **Looplets** (Ahrens, Donenfeld, Kjolstad & Amarasinghe, CGO 2023, DOI `10.1145/3579990.3580020`) and **Finch** (Ahrens et al., PACMPL 9(OOPSLA1), 2025, `arXiv:2404.16730`; `finch-tensor/Finch.jl@7aa1ca1609054b94f3a1b56bb2221ae872513a10`) unify data structure and control flow by representing every tensor iterator over an index interval as a composable **looplet** term that is progressively lowered via rewrite rules.

**Exact looplet hierarchy and style-combination lattice (`Finch.jl`, `src/Finch.jl` L118–130 and `src/looplets/steppers.jl` L1–55):**
Inspecting `src/Finch.jl` and `src/looplets/steppers.jl` confirms Finch's concrete looplet vocabulary and progressive lowering priority (`combine_style`):
- **`Thunk`** (`thunks.jl`): defers preamble setup until a loop body is actually reached.
- **`Sequence`** (`sequences.jl`): splits an iteration interval at a static or dynamic boundary (e.g., padding before/after data, or lower/upper triangular split).
- **`Run`** (`runs.jl`): constant value across a contiguous sub-interval (enabling RLE and zero-fill regions to collapse an entire sub-loop to $O(1)$ arithmetic or skip).
- **`Switch`** (`switches.jl`): selects among multiple body variants based on a condition.
- **`Spike`** (`spikes.jl`): constant body everywhere except the single endpoint of an interval (models compressed sparse elements separated by zero runs: `Run(0)` followed by a single `Spike(val)`).
- **`Stepper` / `Jumper`** (`steppers.jl`, `jumpers.jl`): iterative co-iteration (`while` merge via `stop`/`next`/`seek`) vs. galloping binary-search advancement (`gallop` protocol) for skewed-density intersections.
- **`Lookup`** (`lookups.jl`): $O(1)$ random access (dense arrays, bytemaps, hash tables).

In `src/looplets/steppers.jl` L21–33, `combine_style` resolves multi-operand co-iteration deterministically without hand-coded per-pair kernels: for example, `combine_style(StepperStyle, RunStyle) = RunStyle()`, `combine_style(StepperStyle, SpikeStyle) = SpikeStyle()`, `combine_style(StepperStyle, SequenceStyle) = SequenceStyle()`, and `combine_style(ThunkStyle, StepperStyle) = ThunkStyle()`. Each rewriting pass peels the highest-priority looplet across all co-iterating operands simultaneously, splitting the loop at piecewise boundaries and simplifying sub-expressions (such as `Run(0) * x -> Run(0)`).

**Tensor lifecycle typestate (`src/transforms/enforce_lifecycles.jl` L18–125):**
Sparse structures cannot be safely read and structurally mutated simultaneously (appending to a CSR row invalidates concurrent reader pointers). Finch enforces a compiler-checked **tensor lifecycle** (`declare`, `freeze`, `thaw`) via `EnforceLifecyclesVisitor`:
- `open_stmt` (L49–60) tracks each tensor's current mode (`reader()` vs. `updater(op)`): transitioning `updater -> reader` automatically inserts `freeze(tns, cur_mode.op)` (L52–53), while transitioning `reader -> updater` inserts `thaw(tns, mode.op)` (L54–55).
- `close_scope` (L27–35) automatically freezes every modified tensor at scope exit, and attempting to return a tensor outside its defining scope throws `EnforceLifecyclesError` (L115–119).
- **FFI and ownership insight (`Basis: derived`):** Finch's `declare`/`freeze`/`thaw` lifecycle is structurally identical to **shared (`&T`) vs. exclusive mutable (`&mut T`) borrow typestate**, enforced dynamically inside Finch's Julia-to-Julia macro compiler rather than in an ABI-visible type system. Additionally, Finch requires programs to be **concordant** (loop nesting order matching column-major/level storage order; `transforms/concordize.jl`), and because it is a Julia-hosted staged compiler, foreign C/Rust callers require AOT instantiation for every concrete tuple of operand formats.

---

### 6. The Fill-Value Contract, IEEE-754 Annihilator Failure, and Reduction Order Non-Associativity

Basis: normative + derived + execution

#### 6.1 IEEE-754 Breaks the Semiring Annihilator Axiom ($x \cdot 0 = 0$)

Sparse compilers (TACO, Finch, MLIR `sparse_tensor`) achieve asymptotic speedups by **skipping unstored fill entries** using algebraic rewrite laws:
- Additive skipping relies on the **identity law**: $x + \text{fill} = x$.
- Multiplicative skipping relies on the **annihilator law**: $x \cdot \text{fill} = \text{fill}$.

As stated in the Finch paper (`arXiv:2404.16730`), *"we can use annihilation (x\*0=0), identity ... or other constant propagation properties ... to simplify the computation and avoid redundant work."*

**Critical soundness observation (`Basis: derived + execution`, independent analysis not discussed in the Finch/TACO papers):** **Under IEEE 754-2019 floating-point arithmetic, the identity $x \cdot 0.0 = 0.0$ is FALSE.** Running `probe_p2.py` Section 2B on `dense_x = [inf, -inf, nan, -5.0, 3.0]` against sparse `y` with unstored structural zeros at indices `0..3` (fill `0.0`) and `y[4] = 2.0` produces:

| Index | `x` | Dense IEEE-754 `x * 0.0` | Sparse Skipping (`0.0`) | IEEE-754 Bit-Equal? | Observability |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `0` | `+inf` | **`nan`** | `0.0` | **No** | Silent `NaN` erasure! |
| `1` | `-inf` | **`nan`** | `0.0` | **No** | Silent `NaN` erasure! |
| `2` | `nan` | **`nan`** | `0.0` | **No** | Silent `NaN` erasure! |
| `3` | `-5.0` | **`-0.0`** (`0x8000000000000000`) | **`+0.0`** (`0x0000000000000000`) | **No** | `atan2(-0.0, -1.0) = -3.141593` vs. `atan2(+0.0, -1.0) = +3.141593` |
| `4` | `3.0` | `6.0` | `6.0` | Yes | Both stored non-zeros |

Furthermore, even the additive identity $x + 0.0 = x$ fails bit-equality for `x = -0.0` under IEEE-754 round-to-nearest-even (`-0.0 + (+0.0) = +0.0`), and **reverse-mode differentiation** through a sparse operand skips gradients at structural zeros unless the backward pass explicitly accounts for the fill manifold.

**Verification consequence:** A sparse floating-point kernel is **not** a bit-exact refinement of its dense IEEE-754 counterpart over arbitrary `f32`/`f64` inputs. Sound formal specifications must either:
1. Precondition inputs to **finite non-NaN numbers** and specify equivalence up to signed-zero quotient (`-0.0 ~ +0.0`), or
2. Parameterize the sparse algebra explicitly over a certified **semiring** (as in GraphBLAS, Buluç et al., IPDPSW 2017, where `(plus, times, zero)` is an explicit algebraic parameter—though GraphBLAS C APIs trust rather than verify user-supplied semiring laws).

#### 6.2 Reduction Order and IEEE 754-2019 Clause 9.4

Basis: normative + execution

APL defines reduction (`+/`) sequentially right-to-left (so `- / 1 2 3` evaluates `1 - (2 - 3) = 2`), whereas data-parallel languages (Futhark `reduce`, Finch, TACO, MLIR) re-associate reductions across parallel threads and compressed fiber layouts. **IEEE 754-2019 Clause 9.4 (Reduction operations)** explicitly specifies that multi-term recommended reductions (`sum`, `dot`, `scaledProd`) may **associate in any order and evaluate in any wider intermediate precision**—meaning standard floating-point reductions are intentionally non-deterministic across backends. As verified in `probe_p2.py` Section 2B:

```text
((1e16 + -1e16) + 1.0) = 1.0
(1e16 + (-1e16 + 1.0)) = 0.0
```

Consequently, differential testing between dense and sparse backends cannot assert bit equality on floating-point reductions unless the reduction association tree is fixed as part of the schedule or computed using an exact/reproducible accumulator (e.g., Kulisch superaccumulator or compensated summation).

---

### 7. Sparse Storage Invariants as Zero-Copy Validity Predicates: SciPy, Binsparse, and Unchecked Merge-Lattice Failure

Basis: normative + source + execution

A compressed sparse format is a **byte-level representation relation** between raw integer/value arrays and a logical finite map. Reinterpreting foreign memory as CSR, DCSR, COO, or CSF without checking its structural invariants causes either out-of-bounds memory corruption or silent logical errors.

**Normative canonicality invariants (`GraphBLAS/binsparse-specification@28577ecb0eb72932e2887b18fa63019d73534106`, `spec/draft/index.bs` v0.1.0 L135–305; `arXiv:2506.19175`):**
- **Sparse vector (`indices_0`, `values`):** `indices_0` in bounds, strictly sorted, and no duplicates (L200–201).
- **CSR (`pointers_to_1`, `indices_1`, `values`):** `len(pointers_to_1) == nrows + 1`, `pointers_to_1[0] == 0`, monotone non-decreasing, `pointers_to_1[nrows] == len(indices_1) == len(values)`, and *"Within a row, elements shall be sorted by column index and must not be duplicated"* (L215–218).
- **DCSR (`indices_0`, `pointers_to_1`, `indices_1`, `values`):** `pointers_to_1` contains no repeated values (no empty rows stored), rows sorted and unique, columns within each row sorted and unique (L251–256).
- **COO (`indices_0`, `indices_1`, `values`):** `(row, col)` pairs sorted lexicographically with no duplicates (L290–291).
- **Optional explicit fill:** `fill: true` metadata key indicates a stored `fill_value` (L135–138).

**Library-level tracking (`scipy/scipy@cb78cffebeda622447bf19776883b9d5454b31da`, `scipy/sparse/_compressed.py` L167–192, L1048–1073):**
SciPy separates structural validity (`check_format(full_check=True)` checking integer dtypes, matching `indptr`/`indices` dtypes, 1D shapes, monotone `indptr`, and bounds) from **canonicality** (`has_canonical_format`, lazily computed by `csr_has_canonical_format` and cached on `_has_canonical_format`), and repairs uncanonical inputs lazily via `sort_indices()` and `sum_duplicates()`. Crucially, SciPy's cached `_has_canonical_format` flag **does not travel across a raw C/DLPack/Arrow buffer boundary**.

**Execution probe (`probe_p2.py`, Section 2C, `Basis: execution`):** Feeding malformed CSR rows into a standard TACO-style two-pointer sorted intersection kernel (`while pA < lenA and pB < lenB: c = min(cA, cB); ...`) demonstrates silent miscomputation when preconditions are unchecked:

| Test Case (Logical `A * B`) | `validate_csr` Result | Unchecked Two-Pointer Merge Output | Failure Mode |
| :--- | :--- | :--- | :--- |
| **Canonical** `A={0:2, 2:5}`, `B={0:3, 2:7}` | `(True, 'valid canonical CSR')` | `[(0, 6.0), (2, 35.0)]` | Exact match |
| **Unsorted `A`**: `idx=[2, 0]`, `dat=[5, 2]` | `(False, 'unsorted col 0 after 2 in row 0')` | `[(2, 35.0)]` | **Silently dropped col 0** (`pB` advanced past `0` to `2`, then `pB` exhausted!) |
| **Duplicate `A`**: `idx=[1, 1]`, `dat=[2, 3]` vs `B={1:4}` | `(False, 'duplicate col 1 in row 0')` | `[(1, 8.0)]` | **Silently dropped 2nd duplicate** (`8.0` instead of `(2+3)*4 = 20.0`!) |
| **Non-monotone `indptr`** `[0, 2, 1]` | `(False, 'indptr[-1] != nnz')` | Out-of-bounds / negative slice length | Memory corruption in C/Rust unsafe loops |
| **Out-of-bounds col** `[4]` for `ncols=4` | `(False, 'out-of-bounds col 4 at pos 0')` | Heap buffer overflow on dense gather/scatter | Memory safety violation |

Because canonical CSR validation runs in $O(\text{nrows} + \text{nnz})$ time, verifying the validity predicate once at an FFI ingress boundary and carrying a typed `CanonicalCsr` witness eliminates both memory unsafety and silent merge corruption inside compiled sparse kernels (`Basis: derived`).

---

### 8. Spatial Sparsity and Layout Decoupling: Taichi SNodes, VDB/SPGrid, and Scion BVH Layouts

Basis: normative + documentation + source

#### 8.1 Taichi Structural Nodes (`SNode`) and Implicit Activation-on-Write

Taichi (Hu, Li, Anderson, Ragan-Kelley & Durand, *Taichi: A Language for High-Performance Computation on Spatially Sparse Data Structures*, ACM TOG 38(6), SIGGRAPH Asia 2019, DOI `10.1145/3355089.3356506`; `taichi-dev/taichi@ba0e81dce559fb63a5958bf82feb1d00c55c02fe`, `docs/lang/articles/basic/sparse.md` L32–60 and `taichi/ir/snode.h`) decouples physics/graphics kernels (written using dense-like coordinate indexing `grid[i, j, k]`) from hierarchical **Structural Node (`SNode`)** trees composed of four node primitives:
- `dense`: fixed contiguous block of child cells;
- `bitmasked`: dense storage accompanied by a bitmask tracking active cells (zero pointer chasing, fast parallel compaction);
- `pointer`: sparse array of pointers to child blocks allocated dynamically on demand;
- `dynamic`: variable-length appendable lists (e.g., particles per grid cell).

**Architectural findings verified in Taichi documentation (`docs/lang/articles/basic/sparse.md` L32–60):**
1. **Shallow wide trees beat deep octrees (L32–35):** Because pointer dereferencing stalls modern memory hierarchies, traditional deep binary/quad/octrees perform poorly compared to **shallow trees with large branching factors** inspired by **OpenVDB** (Museth, ACM TOG 2013) and **SPGrid** (Setaluri et al., SIGGRAPH 2014, which leverages OS 4 KiB virtual-memory page tables for sparse grid allocation—creating non-portable OS page-size dependencies).
2. **Implicit activation-on-write is an allocation effect (L57–59):** Reading an inactive cell returns zero/fill, whereas **writing to an inactive cell automatically activates (and for `pointer` SNodes, dynamically allocates) the enclosing hierarchy**. Across an FFI or verified kernel boundary, this breaks no-allocation contracts, introduces concurrent allocation races across GPU threads, and makes read vs. write semantically asymmetric.
3. **Uneven accelerator backend portability (L43–46):** Full spatially sparse SNode execution is supported only on **LLVM-based backends (CPU/CUDA)**; Metal backend sparse support was deprecated, with `Dynamic` SNode removed in Taichi `v1.3.0` and `Pointer`/`Bitmasked` SNodes scheduled for removal in `v1.4.0`.

#### 8.2 Scion and the Three-Artifact Decoupling Law

**Scion** (Gyurgyik, Root & Kjolstad, *Decoupling Data Layouts from Bounding Volume Hierarchies*, PACMPL 10(PLDI), Article 175, 2026, `arXiv:2511.15028`) introduces a DSL and compiler specifically for **bounding volume hierarchies (BVHs)**—explicitly **not** octrees or bitmasked grids (which belong to Taichi SNodes). Scion decouples BVH physical memory layout (node branching factor, AoS vs. SoA bounding-box quantization, sibling/parent packing, pointer vs. offset encoding) from tree traversal algorithms, demonstrating empirically that Pareto-optimal layouts along performance and memory-footprint axes vary strongly across traversal algorithms, CPU/GPU architectures, and scene workloads.

Synthesizing Remora/Dex, TACO/MLIR/Finch, Taichi, and Scion reveals a single unifying compiler invariant (`Basis: derived`): **logical data structure (finite map / tree / tensor), physical storage layout (strided affine view / compressed fiber / SNode / BVH packing), and execution schedule (loop order / looplet lowering / reduction tree) are three independent artifacts.** Proving algorithmic correctness once against the logical structure and transporting it along a verified representation relation (with derived ingress validators for zero-copy bytes) eliminates the $M \times N$ verification explosion across algorithms and layouts.

## Boundaries

- **Native array/sparse runtimes not executed (`not examined`):** Native BQN (`CBQN`), Uiua, J, Dex, Futhark, Julia/`Finch.jl`, TACO C++, MLIR `mlir-opt`, SciPy/NumPy, and Taichi compilers were not installed in the observation environment. Agreement rules, IEEE-754 sparse annihilator discrepancies, unchecked CSR merge corruption, and strided bounds/aliasing were verified via standalone Python 3.13 reference probes (`Basis: execution`) paired with direct pinned upstream source inspection (`Basis: source`).
- **Live DLPack producer alignment survey (`not examined`):** Actual runtime `DLTensor.data` pointer alignment and `strides` outputs across current versions of PyTorch, CuPy, JAX, and TensorFlow were not executed; the finding that major libraries violate DLPack's 256-byte alignment claim rests directly on the upstream warning inside `dmlc/dlpack@6eca9e643fcf7e870b7a1c99ee7fb166c5c2c459` `include/dlpack/dlpack.h` L239–243 (`Basis: source`).
- **Scope of Scion (`known not to apply`):** Scion (`arXiv:2511.15028`) applies strictly to **bounding volume hierarchy (BVH)** layouts and traversals; it does not cover pointer-free bitmasked grids or octrees (which belong to Taichi SNodes / VDB / SPGrid).
- **Attribution of IEEE-754 sparse annihilator analysis (`derived`, not claimed by upstream papers):** Neither the fetched Finch (`arXiv:2404.16730`) nor TACO texts analyze IEEE-754 `inf * 0.0 = nan` or signed-zero `-0.0` violations of the `x * 0 = 0` skipping law; that finding is an independent semantic analysis verified by Python 3 IEEE-754 execution (`probe_p2.py` Section 2B).
- **Dense GPU tile-layout algebras and user-schedulable accelerator DSLs (`not examined`):** CuTe layout algebras, Triton block scheduling, Halide/TVM/Exo schedule languages, and GPU scratchpad DMA lowering are outside the scope of this report.
- **Taichi concurrent GPU activation memory-model guarantees (`unknown`):** The exact atomic synchronization and race semantics of concurrent `pointer`/`bitmasked` SNode activation on CUDA vs. CPU LLVM backends were not traced down to LLVM IR emission in `taichi/codegen/`.
- **Dex `Ix` law verification (`unsupported`):** Dex does not statically verify that user-defined `Ix` instances satisfy bijection laws between `ordinal` and `unsafe_from_ordinal`, nor does it yet enforce private struct constructors for `RangeFrom` (`lib/prelude.dx` L336).

## Evidence

### Pinned Upstream Repositories and Source Citations

1. **`mlochbaum/BQN`** at commit `0ae87a3763c2023b159410cc2ae1048a1768c184`:
   - `doc/leading.md` (L5–59): leading-axis rationale, major cells, `⎉`/`˘` frame/cell splitting.
   - `doc/based.md` (L11–50): based vs. nested vs. boxed models, atoms non-arrays, inductive array definition.
   - `doc/fill.md` (L5–60): fill element rules, operations consulting fills, unknown-fill errors, no-side-effect speculative fill rule.
   - `doc/context.md` (L7–45): APL `a b c d e` ambiguity vs. BQN spelling-encoded syntactic roles giving a context-free grammar.
2. **`uiua-lang/uiua`** at commit `951a6a02a509d127a42de5396e0e67683027438c`:
   - `readme.md` (L6): tacit array programming language description.
   - `src/check.rs` (L1–65): `nodes_all_sigs`, `VirtualEnv::from_nodes`, main `stack` + auxiliary `under` stack static signature checker.
3. **`jsoftware/jsource`** at commit `19e16a988f3cf6ed48f73c28bb6dc06ca93d86e2`: `README.md`.
4. **`google-research/dex-lang`** at commit `25e2e389b90403ae2f8d67fb6d52f47d23c439ee`:
   - `lib/prelude.dx` (L315–355): `interface Ix(n|Data)` (`size'`, `ordinal`, `unsafe_from_ordinal`), `Fin(n)`, `RangeFrom` (`# TODO` private constructor note at L336).
5. **`jrslepak/Remora`** at commit `1a831dec554df9a7ef3eeb10f0d22036f1f86dbd`.
6. **`diku-dk/futhark`** at commit `dc285f6698c118f2b236f65984e38104e72f7939`: `docs/language-reference.rst` (regular-array restriction, existential sizes, uniqueness).
7. **`dmlc/dlpack`** at commit `6eca9e643fcf7e870b7a1c99ee7fb166c5c2c459`:
   - `include/dlpack/dlpack.h`: L147–192 (`DLDataTypeCode` including FP8/FP6/FP4/Bcomplex), L211–227 (`DLDataType`, little bit-endian sub-byte packing), L236–243 (256-byte alignment claim + non-adherence warning for CuPy/PyTorch/TensorFlow/TVM), L259–260 (zero-size `data == NULL`), L276–287 (element-unit `strides`, non-NULL requirement in DLPack v1.2+).
8. **`apache/arrow`** at commit `931b9cccda5de68d48201dc2db50b6b6a9a72741`:
   - `docs/source/format/CDataInterface.rst`: L82–85 (release callback), L95–114 (format strings), L298–318 (`struct ArrowArray`, `release`, opaque `private_data`).
9. **`tensor-compiler/taco`** at commit `0e79acb56cb5f3d1785179536256e206790b2a9e`:
   - `include/taco/format.h` (L21–90): `Format`, `modeOrdering`, `ModeFormat::dense`/`compressed`/`singleton`.
   - `src/lower/merge_lattice.cpp` (L22–75): `MergeLatticeBuilder` over `IndexNotationVisitorStrict` and `IterationAlgebraVisitorStrict`.
10. **`finch-tensor/Finch.jl`** at commit `7aa1ca1609054b94f3a1b56bb2221ae872513a10`:
    - `src/Finch.jl` (L27–130): exported level formats (`SparseList`, `SparseRunList`, `RunList`, `SparseBand`, `SparseCOO`, `SparseByteMap`, `Dense`), masks (`lotrimask`, `uptrimask`, `bandmask`), lifecycle/concordize transforms, looplet module list.
    - `src/looplets/steppers.jl` (L1–55): `Stepper` struct and `combine_style` priority lattice.
    - `src/transforms/enforce_lifecycles.jl` (L18–125): `EnforceLifecyclesVisitor`, automatic `freeze`/`thaw` insertion, `EnforceLifecyclesError`.
11. **`llvm/llvm-project`** at commit `0782b426c676c774d60a7825095768f682e9fd6d`:
    - `mlir/include/mlir/Dialect/SparseTensor/IR/SparseTensorAttrDefs.td` (L117–199): `SparseTensorEncodingAttr`, `dimension` vs. `level`, `compressed`, `loose_compressed`, `singleton`, `structured[n, m]`, default unique+ordered semantics, `nonunique`/`nonordered`/`soa`.
12. **`scipy/scipy`** at commit `cb78cffebeda622447bf19776883b9d5454b31da`:
    - `scipy/sparse/_compressed.py`: L167–192 (`check_format`), L1048–1073 (`has_canonical_format` lazy caching and setter).
13. **`GraphBLAS/binsparse-specification`** at commit `28577ecb0eb72932e2887b18fa63019d73534106` (`arXiv:2506.19175`):
    - `spec/draft/index.bs` (`SPECVERSION 0.1.0`): L135–138 (`fill` / `fill_value`), L200–201 (vector sorted/unique), L215–218 (CSR sorted/unique per row), L251–256 (DCSR no empty rows, sorted/unique), L290–291 (COO lexicographic sorted/unique).
14. **`taichi-dev/taichi`** at commit `ba0e81dce559fb63a5958bf82feb1d00c55c02fe`:
    - `docs/lang/articles/basic/sparse.md` (L32–60): shallow wide trees vs. octrees, Metal deprecation/removal (`v1.3.0`/`v1.4.0`), `pointer`/`bitmasked`/`dynamic`/`dense` SNodes, automatic activation on write.
    - `taichi/ir/snode.h`.

### Peer-Reviewed Literature and Standards Verified

- Slepak, Shivers & Manolios (2014), *An Array-Oriented Language with Static Rank Polymorphism*, ESOP 2014, DOI `10.1007/978-3-642-54833-8_3`; *Rank Polymorphism Viewed as a Constraint Problem*, ARRAY 2018; *The Semantics of Rank Polymorphism* (`arXiv:1907.00509`).
- Paszke, Johnson, Duvenaud, Vytiniotis, Radul, Johnson, Ragan-Kelley & Maclaurin (2021), *Getting to the Point: Index Sets and Parallelism-Preserving Autodiff for Pointful Array Programming*, PACMPL 5(ICFP), DOI `10.1145/3473578` (`arXiv:2104.05372`).
- Henriksen, Serup, Elsman, Henglein & Oancea (PLDI 2017); Blelloch (NESL, CMU-CS-95-170, 1995); Chiang, Rush & Barak (*Named Tensor Notation*, `arXiv:2102.13196`).
- Kjolstad, Kamil, Chou, Lugato & Amarasinghe (2017), *The Tensor Algebra Compiler*, PACMPL 1(OOPSLA), Article 77, DOI `10.1145/3133901`; Chou, Kjolstad & Amarasinghe (OOPSLA 2018, Article 123, `arXiv:1804.10112`); Henry et al. (OOPSLA 2021); Bik et al. (ACM TACO 2022); Buluç et al. (GraphBLAS C API, IPDPSW 2017).
- Ahrens, Donenfeld, Kjolstad & Amarasinghe (2023), *Looplets: A Language for Structured Coiteration*, CGO 2023, DOI `10.1145/3579990.3580020`; Ahrens et al., *Finch: Sparse and Structured Tensor Programming with Control Flow*, PACMPL 9(OOPSLA1), 2025 (`arXiv:2404.16730`).
- Kovach, Kolichala, Gu & Kjolstad (2023), *Indexed Streams: A Formal Intermediate Representation for Fused Contraction Programs*, PACMPL 7(PLDI), DOI `10.1145/3591268` (mechanically verified in Lean).
- Hu, Li, Anderson, Ragan-Kelley & Durand (2019), *Taichi: A Language for High-Performance Computation on Spatially Sparse Data Structures*, ACM TOG 38(6), SIGGRAPH Asia 2019, DOI `10.1145/3355089.3356506`; Museth (OpenVDB, ACM TOG 2013); Setaluri et al. (SPGrid, 2014).
- Gyurgyik, Root & Kjolstad (2026), *Decoupling Data Layouts from Bounding Volume Hierarchies* (Scion), PACMPL 10(PLDI), Article 175 (`arXiv:2511.15028`).
- IEEE 754-2019, Clause 9.4 (Reduction operations: arbitrary association and wider intermediate precision permitted).

### Executable Reference Probe Output (`Basis: execution`)

Observed on Linux x86_64 with Python 3.13 (`2026-11-19`):

```text
=== 2A. Leading-Axis Prefix Agreement (J/BQN) vs Trailing-Axis Broadcasting (NumPy) ===
  (3,)       op (3, 4)     | Prefix(J/BQN): (3, 4)                                     | Trailing(NumPy): BROADCAST ERROR: (3,) vs (3, 4)
  (4,)       op (3, 4)     | Prefix(J/BQN): RANK/SHAPE ERROR: (4,) vs (3, 4) (prefixes (4,) != (3,)) | Trailing(NumPy): (3, 4)
  (3, 1)     op (3,)       | Prefix(J/BQN): (3, 1)                                     | Trailing(NumPy): (3, 3)
  (2, 3)     op (2, 3, 4)  | Prefix(J/BQN): (2, 3, 4)                                  | Trailing(NumPy): BROADCAST ERROR: (2, 3) vs (2, 3, 4)
  (3, 4)     op (2, 3, 4)  | Prefix(J/BQN): RANK/SHAPE ERROR: (3, 4) vs (2, 3, 4) (prefixes (3, 4) != (2, 3)) | Trailing(NumPy): (2, 3, 4)

=== 2B. IEEE-754 Annihilator Failure (x * 0.0 != 0.0) & Reduction Non-Associativity ===
  idx=0 x=   inf | dense(x*0)=   nan (sign=-1) | sparse_skip=  0.0 (sign=+1) | bit-equal=False
  idx=1 x=  -inf | dense(x*0)=   nan (sign=-1) | sparse_skip=  0.0 (sign=+1) | bit-equal=False
  idx=2 x=   nan | dense(x*0)=   nan (sign=+1) | sparse_skip=  0.0 (sign=+1) | bit-equal=False
  idx=3 x=  -5.0 | dense(x*0)=  -0.0 (sign=-1) | sparse_skip=  0.0 (sign=+1) | bit-equal=False
  idx=4 x=   3.0 | dense(x*0)=   6.0 (sign=+1) | sparse_skip=  6.0 (sign=+1) | bit-equal=True
  Observing -0.0 vs +0.0: atan2(dense_prod[3], -1.0)=-3.141593 (bits=0x8000000000000000) vs atan2(sparse_prod[3], -1.0)=3.141593 (bits=0x0000000000000000)
  Float reduction non-associativity: ((1e16 + -1e16) + 1.0) = 1.0 vs (1e16 + (-1e16 + 1.0)) = 0.0

=== 2C. CSR Validity Predicate vs Unchecked TACO-Style Merge-Lattice Intersection ===
  Canonical A, B: (True, 'valid canonical CSR') -> merge: [(0, 6.0), (2, 35.0)]
  Unsorted A:     (False, 'unsorted col 0 after 2 in row 0') -> merge: [(2, 35.0)] (SILENTLY DROPPED col 0!)
  Duplicate A:    (False, 'duplicate col 1 in row 0') -> merge: [(1, 8.0)] (SILENTLY DROPPED second dup: 8.0 vs 20.0!)
  Bad indptr:     (False, 'indptr[-1] != nnz')
  OOB col:        (False, 'out-of-bounds col 4 at pos 0')

=== 2D. Affine Strided-View Bounds & Aliasing Validity Check ===
  Reversed 1D view (base=7, shape=(8,), stride=(-1,), alloc=8): (True, (0, 7))
  OOB negative stride (base=6, shape=(8,), stride=(-1,), alloc=8): (False, (-1, 6))
  Even/Odd strided slices alias (0,4,2) vs (1,4,2): (False, [])
  Stride-2 vs Stride-3 slices alias (0,4,2) vs (0,3,3): (True, [0, 6])
```

## Revalidation

1. **Diff upstream descriptor and compiler contracts:**
   - **DLPack:** Inspect `include/dlpack/dlpack.h` around `DLTensor` to check whether the 256-byte alignment disclaimer has been resolved or whether `strides` / versioned flags changed post-v1.2.
   - **MLIR `sparse_tensor`:** Inspect `mlir/include/mlir/Dialect/SparseTensor/IR/SparseTensorAttrDefs.td` for newly added level types or relaxed ordering/uniqueness defaults.
   - **Finch.jl & Binsparse:** Check `src/transforms/enforce_lifecycles.jl` and `src/looplets/steppers.jl` (`combine_style`) in `finch-tensor/Finch.jl`, and `SPECVERSION` / format invariant clauses in `GraphBLAS/binsparse-specification` `spec/draft/index.bs`.
2. **Re-run the self-contained IEEE-754 annihilator & unchecked CSR merge probe:**

```bash
python3 - <<'EOF'
import math, struct
assert math.isnan(math.inf * 0.0) and struct.unpack('>Q', struct.pack('>d', -5.0 * 0.0))[0] == 0x8000000000000000
assert ((1e16 + -1e16) + 1.0) != (1e16 + (-1e16 + 1.0))
def merge_row(iA, dA, iB, dB):
    pA = pB = 0; out = []
    while pA < len(iA) and pB < len(iB):
        c = min(iA[pA], iB[pB])
        if iA[pA] == c and iB[pB] == c: out.append((c, dA[pA] * dB[pB]))
        pA += int(iA[pA] == c); pB += int(iB[pB] == c)
    return out
assert merge_row([2, 0], [5.0, 2.0], [0, 2], [3.0, 7.0]) == [(2, 35.0)] # col 0 silently lost
assert merge_row([1, 1], [2.0, 3.0], [1], [4.0]) == [(1, 8.0)]          # duplicate silently lost
print("PASS: IEEE-754 annihilator failure and unchecked CSR merge hazards reproduced")
EOF
```

3. **Live sparse-ecosystem revalidation (when SciPy / Finch.jl / PyTorch are available):** Multiply a sparse matrix containing structural zeros by a dense array containing `np.inf`, `np.nan`, and `-5.0` in `scipy.sparse` and `Finch.jl`, and compare against dense multiplication; pass an unsorted/duplicate CSR buffer with `_has_canonical_format = True` vs. default construction to confirm whether the target library validates, repairs, or silently miscomputes.
