# Self-Referential Projections, Disjoint Slice Witnesses, Polonius Graph Limits, and Autovectorization Barriers

## Summary

Safe ownership type systems and optimizing SIMD/GPU compilers reject or silently degrade four well-defined classes of dynamically safe programs—forcing engineers into brittle `unsafe` adapters that have repeatedly caused subtle aliasing CVEs and scalar performance cliffs:

1. **Self-referential arenas, futures, and `Pin` projection soundness traps:** Vanilla Rust forbids structs holding references to sibling fields because arbitrary bitwise moves (`memcpy`) invalidate internal pointers and structural field drop order runs parent fields before or while borrowed references remain live. `Pin<Ptr>` (`core/src/pin.rs`) prevents moves only when coupled with strict `!Unpin` and `#[pinned_drop]` enforcement (`taiki-e/pin-project`). Macro workarounds that erase `'this -> 'static` (`someguynamedjosh/ouroboros` `< 0.16.0`) triggered **RUSTSEC-2023-0042**: under Stacked Borrows (`10.1145/3371109`) and Tree Borrows (`10.1145/3735592`), passing a struct containing a `&'static` / `&'static mut` reference into `drop(&mut self)` installs a function-entry aliasing protector that becomes immediate UB the instant the backing owner field drops inside that function. Even after wrapping the internal struct in `MaybeUninit<#internal_ident>` (`ouroboros_macro/src/generate/struc.rs:19-24`) or `KindaSortaDangling<C>` (`unicode-org/icu4x` `yoke.rs:80-93`, `cartable_ptr.rs:179-195`) to suppress `dereferenceable`/`noalias` retags on `Box<T>`, ergonomics and soundness remain fragile across contravariant lifetimes and `Drop` projections.
2. **NLL conditional-return rejections, `-Zpolonius=next`, and the interprocedural partial-borrow wall:** Non-Lexical Lifetimes (NLL) ties loan liveness to coarse lexical output lifetimes, rejecting conditional return patterns (Problem Case #3, e.g., `HashMap::get_mut` followed by `insert` on `None`) with `E0499`—verified live on `rustc 1.98.0-nightly (14210df0e 2026-05-31)`. Switching to `-Zpolonius=next` (`compiler/rustc_borrowck/src/polonius/mod.rs`) replaces Datalog `subset` transitive-closure blowup (`rust-lang/polonius`) with reachability over a `LocalizedConstraintGraph` + `LiveLoans` bitset (`num_points * num_borrows`) and compiles Problem Case #3 cleanly, **while explicitly flagging an unresolved tension between backward time-traveling invariance edges and flow-insensitive `loan_killed_at` facts (`mod.rs:221-258`)**. Crucially, **even `-Zpolonius=next` still fails (`E0502`) on interprocedural disjoint field borrows** (`e.get_config()` held across `e.mutate_scratch()`), because Rust method signatures borrow all of `&self` / `&mut self` without **View Types** or **Place Capability Graphs** (`10.1145/3763122`).
3. **Non-contiguous and bijective mutable slice splitting beyond `split_at_mut` and `get_disjoint_mut`:** `slice::split_at_mut` (`core/src/slice/mod.rs:1997`) handles only single contiguous partitions, while `slice::get_disjoint_mut<I, const N: usize>` (`L5194-5255, 5737`) requires compile-time fixed arity `N` and runs an $O(N^2)$ pairwise `is_overlapping()` loop. Dynamic disjoint index patterns—Cooley–Tukey FFT butterfly pairs `(k, k ^ stride)`, CSR sparse row scatter, and bipartite graph updates—are dynamically disjoint yet unrepresentable in safe Rust without raw-pointer `unsafe` blocks or verified bijection witnesses.
4. **Safe autovectorization and SIMT lowering barriers (AVX-512, ARM SVE, WGSL):** `LLVM`'s `LoopVectorizationLegality` (`llvm/lib/Transforms/Vectorize/LoopVectorizationLegality.cpp:1202-1581`) aborts vectorization whenever predicated loads cannot be proved non-faulting (`isDereferenceableAndAlignedInLoop`), runtime pointer-alias checks multiply branches (`saxpy_aliasing`: 23 `cmp/jmp` vs 14 with `__restrict__`), or strict IEEE-754 floating-point summation forbids tree reassociation (`sum_strict_fp`: 0 `ymm` instructions under `gcc 15.2.0 -O3 -mavx2 -mfma`). Live `rustc` assembly probes confirm that conditional pointer dereferencing (`cond_deref_raw`) emits **0** `ymm`/`zmm` instructions on AVX2 (`haswell`), whereas AVX-512 (`skylake-avx512`) unlocks vectorization via **10 opmask `{%k}` instructions and 5 fault-suppressing `vpgatherqd ... {%k}` gathers** (`simd_avx512.s:42-89`). In WebGPU `WGSL` (`gpuweb/gpuweb`), static uniformity analysis (`wgsl/index.bs:12504-13867`) rejects barriers inside branches conditioned on uniform fields extracted from mixed-uniformity structs (`Composite Value Analysis Limitations`), while `vec3<f32>` (`AlignOf=16, SizeOf=12`) and 4-byte `bool` impose hidden layout padding.

## Applicability

This report examines concrete compiler passes, libraries, specifications, and executable probes verified on `2026-11-19`:

- **Rust Borrow Checker, `core`, & Polonius** (`rust-lang/rust` @ `c884ecfbabb04b04fa5054dafc67ec258ecde745`; `rust-lang/polonius` @ `bfd4c945b7713d0e66a3cde80475d9a4494740df`; `rustc 1.98.0-nightly (14210df0e 2026-05-31)`): Applies to `NLL`, legacy Datafrog Polonius (`polonius-engine`), `-Zpolonius=next` (`rustc_borrowck/src/polonius/mod.rs`), `core::pin::Pin`, and `core::slice::{split_at_mut, get_disjoint_mut}`.
- **Self-Referential Rust Crates & Aliasing Models** (`unicode-org/icu4x` @ `ffe417bb7f83d097047151cd40dde184bdc9cdc4`; `someguynamedjosh/ouroboros` @ `b75b9c16e6d79b6b8a678ac5bca602134473951d`; `Voultapher/self_cell` @ `93cb06e430e7516ac9b436029a15127782b6c2b6`; `taiki-e/pin-project` @ `a0191954d8bdb1c125eb9f53980760c0df743eeb`): Interpreted under Stacked Borrows (`10.1145/3371109`), Tree Borrows (`10.1145/3735592`), `RUSTSEC-2023-0042`, Oxide (`arXiv:1903.00982`), and Place Capability Graphs (`10.1145/3763122`).
- **SIMD & GPU Vectorization Toolchains** (`llvm/llvm-project` @ `de85491c7e327289d654790197b3432003723b4a`; `gpuweb/gpuweb` @ `d178d9145ab1652ec933e71a8c30e8f6470f00a3`; `gcc 15.2.0` on x86-64; `rustc 1.98.0-nightly` targeting `haswell` vs `skylake-avx512`): Applies to LLVM `LoopVectorizationLegality` and WGSL host-shareable memory/uniformity rules. ARM SVE First-Faulting behavior (`ldff1w`) is noted from architectural specification/literature (`not executed` on native x86-64 hardware).
- **Diagnostics**: `zesterer/ariadne` @ `5e62913d34dabf34140ad812448dc8faae5abf15` and `rustc` E0499/E0502 error spans.

## Findings

### 1. Self-Referential Arenas, `Pin` Projection Traps, and `ouroboros`/`yoke` Soundness Anatomy

**Basis:** `normative` (`core/src/pin.rs`, `10.1145/3371109`, `10.1145/3735592`) + `source` (`pin-project/src/lib.rs`, `ouroboros_macro/src/generate/{struc,drop}.rs`, `icu4x/utils/yoke/src/{yoke,cartable_ptr}.rs`, `self_cell/src/lib.rs`) + `documentation` (`RUSTSEC-2023-0042`).

#### 1.1 Why `Pin<&mut T>` Projection Fails Without Macro/Type Discipline

In Rust (`core/src/pin.rs:49-160`), `Pin<Ptr>` enforces that an address-sensitive (`!Unpin`) value remains at a fixed memory address from first pin until `Drop::drop` finishes (**the `Drop` guarantee**). Projecting `Pin<&mut S>` to a field `f` admits only two mutually exclusive safe strategies:

1. **Structural Pinning (`Pin<&mut F>`):** `S` never exposes `&mut F` directly, implements `!Unpin` unless all structurally pinned fields are `Unpin`, and forbids `Drop::drop(&mut mut_self)` from moving out of `f`. `taiki-e/pin-project` (`src/lib.rs:29-75, 122-150`) enforces this statically via `#[pin_project]` + `#[pinned_drop]` + `UnsafeUnpin` because a hand-written `impl<T> Unpin for S<T>` or standard `Drop::drop(&mut self)` immediately breaches the `Pin` contract (`Pin::new_unchecked(&mut self.f)` followed by `mem::swap`).
2. **Non-Structural Pinning (`&mut F`):** Requires guaranteeing `F` is never structurally pinned anywhere; mixing structural and non-structural access to the same field allows safe code to swap `F` via `mem::replace` while self-pointers still target `F`'s address.

#### 1.2 `RUSTSEC-2023-0042` (`ouroboros`), `yoke`'s `KindaSortaDangling`, and `self_cell` Variance Traps

| Crate / Mechanism | Internal Storage & Lifetime Trick | Aliasing / Variance Soundness Hazard | Mitigation & Remaining Limitation |
| :--- | :--- | :--- | :--- |
| **`ouroboros` `< 0.16.0`** (`RUSTSEC-2023-0042`) | Replaced `'this` with `'static` directly on fields inside generated struct | Under Stacked Borrows (`10.1145/3371109`) & Tree Borrows (`10.1145/3735592`), passing `&mut Self` into `drop(&mut self)` installs a **function-entry protector** on every `&'static` / `&'static mut` inside `Self`; dropping the owner invalidates the borrowed target *while the protector is still active* (`UB` in Miri) | An intermediate `[u8; N]` byte-array fix failed on **struct padding bytes** (uninitialized reads during optimization). `ouroboros >= 0.16` (`struc.rs:19-68, drop.rs:16-20`) wraps the reversed-field `#internal_ident` inside `MaybeUninit<#internal_ident>` (`assume_init_drop()`), creating references strictly *inside* accessor/drop bodies rather than as function arguments |
| **`icu4x` `yoke`** (`ffe417bb...`) | `Yoke<Y: for<'a> Yokeable<'a>, C>` (`yoke.rs:80-93`) stores `(yokeable, cart)` both wrapped in `KindaSortaDangling<T>`, plus `CartableOptionPointer` (`cartable_ptr.rs:81-195`) | Early `Yoke` versions moving `Box<T>` carts by value emitted LLVM `dereferenceable` + `noalias` retags that **invalidated derived pointers held by `yokeable`** (`yoke.rs:87-91`, referencing `icu4x#2095` & `rust-lang/rust#147228`) and risked soundness if `Debug`/projection leaked contravariant lifetimes | `KindaSortaDangling<T>` suppresses `noalias`/`dereferenceable` compiler tags during moves/drops; `CartableOptionPointer` leaks/reconstructs `NonNull<Self::Raw>` (`option_into_raw`/`drop_raw`). Requires unsafe `for<'a> Yokeable<'a>` trait impls and manual `Yoke::map_project` (`L984-1028`) |
| **`self_cell`** (`93cb06e4...`) | Heap-allocates owner + dependent together (`UnsafeSelfCell`), drops dependent before owner (`self_cell.rs:407-413`) | Exposing `borrow_dependent(&self) -> &Dependent<'_>` on **non-covariant** `Dependent<'a>` (e.g., `Cell<&'a T>` or `fn(&'a ())`) allows shortening `'a` unsoundly (`self_cell#5`); contravariant owners also leak variance (`self_cell#18`) | `_covariant_access!` (`L425-445`) verifies covariance via `_assert_covariance` before emitting `borrow_dependent()`, and `_covariant_owner_marker!` (`L450-465`) forces invariant `PhantomData<fn(&'a ()) -> &'a ()>` on `not_covariant` cells |

### 2. Conditional-Return & Loop Borrow-Checker Rejections (`NLL`, `Polonius`, View Types, and PCG)

**Basis:** `source` (`rust-lang/polonius` `facts.rs`, `datafrog_opt.rs`; `rust-lang/rust` `rustc_borrowck/src/polonius/mod.rs`) + `documentation` (`Polonius Revisited`, `View types for Rust`) + `normative` (`10.48550/arXiv.1903.00982`, `10.1145/3763122`) + `execution` (`polonius_probe.rs`, `view_probe.rs` in `## Evidence`).

#### 2.1 NLL Problem Case #3 vs. Datalog Polonius vs. `-Zpolonius=next`

Under standard NLL, a reference returned from a function forces its origin `'r` to outlive the entire function body (every exit path). In `get_or_insert` (`polonius_probe.rs` in `## Evidence`), returning `v: &'r mut V` in the `Some(v)` arm forces the initial `map.get_mut(&key)` borrow to remain active in the *disjoint* `None` arm, causing `rustc 1.98.0-nightly` to reject both `map.insert(...)` and the fallback `map.get_mut(&key)` with `E0499`:

```text
error[E0499]: cannot borrow `*map` as mutable more than once at a time
  --> /tmp/repro_pkg2/polonius_probe.rs:9:13
   |
 2 |   fn get_or_insert<'r, K: Eq + std::hash::Hash + Copy, V: Default>(
   |                    -- lifetime `'r` defined here
...
 6 |       match map.get_mut(&key) {
   |       -     --- first mutable borrow occurs here
   |  _____|
   | |
 7 | |         Some(v) => v,
 8 | |         None => {
 9 | |             map.insert(key, V::default());
   | |             ^^^ second mutable borrow occurs here
...  |
12 | |     }
   | |_____- returning this value requires that `*map` is borrowed for `'r`
```

Running the exact same file with `rustc -Zpolonius=next` compiles cleanly (`exit 0`) and prints `polonius_pc3: 10`. Examining how Polonius solves this—and where its implementations hit scaling and soundness walls—exposes two architectural generations:

1. **Legacy Datalog / Datafrog Engine (`rust-lang/polonius` `facts.rs:6-90`, `datafrog_opt.rs:50-310`):** Encodes 16 MIR fact relations (`loan_issued_at`, `subset_base`, `cfg_edge`, `loan_killed_at`, `loan_invalidated_at`, `origin_live_on_entry`, `placeholder`, etc.) and computes fixed-point `subset(origin1, origin2, point)` and `dying_can_reach` transitive closures per CFG point. Computing the full `O(|Origins|^2 * |Points|)` point-indexed subset closure caused severe compile-time RSS and latency blowups on real crates (`rustc` crater regressions).
2. **`-Zpolonius=next` Localized Constraint Graph (`rustc_borrowck/src/polonius/mod.rs:64-262`):** Replaces point-indexed Datalog `subset` closures with graph reachability over `(Origin, Point)` nodes (`LocalizedConstraintGraph`), storing outputs in a single packed `LiveLoans` matrix (`DenseBitSet<usize>` of size `num_points * num_borrows`, `L65-85`) and encoding type variance directly into edge direction (`ConstraintDirection::{Forward, Backward, Bidirectional}`, `L114-123`).
   - **Documented Time-Travel vs. Kill Soundness Tension (`mod.rs:221-258`):** Invariant types generate `Bidirectional` edges, allowing loan reachability to "time-travel" backward along CFG edges (`L17-18`). As `rustc_borrowck/src/polonius/mod.rs:221-258` explicitly notes (`FIXME: analyze potential unsoundness`), `loan_killed_at` prevents a loan from propagating forward past a reassignment, *yet* backward time-traveling traversals and flow-insensitive kills can cross kill points unless a two-step traversal (exit reachability ignoring kills, then normal forward continuation) is used—leaving `-Zpolonius=next` as an actionable subset matching NLL soundness on crater while needing formalization against `a-mir-formality`.

#### 2.2 The Interprocedural Partial-Borrow Wall (`E0502` Under `-Zpolonius=next`)

Even with `-Zpolonius=next`, **Rust borrow checking stops cleanly at function boundaries**. When `view_probe.rs` (`## Evidence`) calls `let cfg = e.get_config();` (`&self -> &[u32]`, returning `&self.config`) and then `e.mutate_scratch(cfg[0]);` (`&mut self`, mutating only `self.scratch`) while keeping `cfg` alive through `println!`, `-Zpolonius=next` still rejects the dynamically safe program:

```text
error[E0502]: cannot borrow `e` as mutable because it is also borrowed as immutable
  --> /tmp/repro_pkg2/view_probe.rs:11:5
   |
10 |     let cfg = e.get_config();
   |               - immutable borrow occurs here
11 |     e.mutate_scratch(cfg[0]);
   |     ^^^^^^^^^^^^^^^^^^^^^^^^ mutable borrow occurs here
12 |     println!("view: {:?} {:?}", cfg, e.scratch);
   |                                 --- immutable borrow later used here
```

Why? Rust has no **View Types** (`&{config} Self` vs `&{mut scratch} Self`, proposed by Niko Matsakis) or modular **Place Capability Graphs** (`10.1145/3763122`), so every `&self` / `&mut self` signature over-approximates field disjointness to the entire receiver struct. Developers must either inline field access at every callsite, duplicate free-function helpers taking split field arguments, or inject `RefCell` runtime borrow-flag checks.

### 3. Non-Contiguous & Bijective Mutable Slice Splitting Beyond `split_at_mut` and `get_disjoint_mut`

**Basis:** `source` (`rust-lang/rust` `library/core/src/slice/mod.rs:1997-2203, 5160-5805`) + `execution` (`disjoint_probe.rs` in `## Evidence`) + `derived`.

`core::slice` provides only two safe mutable partitioning primitives:

1. **`split_at_mut(mid)` (`mod.rs:1997`):** Splits one slice into two contiguous intervals `[0..mid)` and `[mid..len)`. It cannot express multi-way non-contiguous disjoint sets or cyclic/strided partitions without recursive sequential chopping.
2. **`get_disjoint_mut<I, const N: usize>(&mut self, indices: [I; N])` (`mod.rs:5194-5255, 5737`):** Accepts a fixed compile-time array `[I; N]` (`GetDisjointMutIndex`, checked for `is_in_bounds` and `is_overlapping`), verified on `[1, 5]` in `disjoint_probe.rs`. Crucially, its implementation performs an **$O(N^2)$ runtime pairwise overlap scan** (`mod.rs:5198, 5737`), explicitly warning callers about quadratic scaling for large `N`, and cannot return a variable-length slice of disjoint mutable references (`N` is a `const` generic)!

Consequently, four ubiquitous numeric and systems kernels cannot be expressed cleanly in safe Rust without falling back to `unsafe { slice::get_disjoint_unchecked_mut }` or raw `*mut T`:

| Kernel Pattern | Algebraic Disjointness Law | Why `split_at_mut` & `get_disjoint_mut` Fail |
| :--- | :--- | :--- |
| **Cooley–Tukey Radix-2 FFT Butterfly** | Pairs `(k, k \| stride)` for `(k & stride) == 0` form a bijection on `[0, 2^m)` | Runtime `stride = 1 << stage`; variable count `n/2` cannot instantiate `const N`; `chunks_exact_mut(2 * stride)` still needs `split_at_mut(stride)` + nested zipping for each stage, breaking general radix-$r$ or mixed-radix layouts |
| **Bit-Reversal / Cycle-Permutation In-Place Transpose** | $i \mapsto \pi(i)$ is a permutation (`bitrev(i) != i` swapped once) | Requires splitting at arbitrary runtime pairs `[i, pi[i]]` inside a loop or parallelizing disjoint permutation cycles statically |
| **CSR Sparse Matrix / Graph Row-Scatter** | Disjoint row bucket slices `[row_ptr[r]..row_ptr[r+1]]` where `row_ptr` is monotone non-decreasing (`row_ptr[r] <= row_ptr[r+1]`) | Variable number of rows `R`; non-uniform lengths prevent `chunks_mut`; scanning `row_ptr` requires sequential `split_at_mut` reborrowing that defeats `rayon` random-access work-stealing unless wrapped in `unsafe` `Sync` pointers |
| **Even/Odd Phase or Stride-$k$ Sublattice Updates** | Modulo congruence classes $\{i \mid i \equiv r \pmod k\}$ (`red-black` Gauss–Seidel) | No safe `&mut StridedSlice<T, k>` abstraction in `core::slice`; `chunks_mut` forces fixed chunk contiguity rather than modular stride slices |

### 4. Safe Autovectorization and SIMT Lowering Barriers (AVX-512, ARM SVE, and WGSL)

**Basis:** `source` (`llvm/llvm-project` `LoopVectorizationLegality.cpp`, `gpuweb/gpuweb` `wgsl/index.bs`) + `documentation` (*The story of ispc*) + `execution` (`simd_probe.rs`, `simd_alias_fp.c` in `## Evidence`).

Even when borrow-checking succeeds, safe scalar Rust and C++ loops fail LLVM's `LoopVectorizationLegality` (`LoopVectorizationLegality.cpp:1202-1581`) across four concrete compiler/ISA gates:

1. **Predicated Pointer-Load Fault Suppression (`LoopVectorizationLegality.cpp:1398-1581`):** When an `if` branch loads memory conditionally (`blockNeedsPredication(BB)`), LLVM cannot execute the load unconditionally across SIMD lanes unless `isDereferenceableAndAlignedInLoop` (`L1544`) proves every lane's address is mapped and non-faulting—or the target ISA provides hardware fault-suppressing masked loads/gathers (`blockCanBePredicated`, `L1426-1434`). Our live `rustc 1.98.0-nightly` probe (`simd_probe.rs`) confirms this exact hardware cliff:
   - On **AVX2 (`-C target-cpu=haswell`)**, `cond_deref_raw` (`if mask[i] != 0 { sum += *ptrs[i]; }`) emits **0 `ymm` / `zmm` / gather instructions**—falling back completely to scalar because `ptrs[i]` for masked-off lanes may be null/unmapped, and AVX2 lacks fault suppression on unpredicated scalar-emulated derefs.
   - On **AVX-512 (`-C target-cpu=skylake-avx512`)**, LLVM emits **10 opmask `{%k}`-predicated vector instructions (`vptestmb`, `vmovdqu64 ... {%k4} {z}`) and 5 hardware fault-suppressing `vpgatherqd (,%ymm4), %xmm8 {%k4}` instructions** (`simd_avx512.s:42-89`), because AVX-512 suppresses page faults on zeroed opmask lanes (`k_i == 0`).
   - Similarly, on **ARM SVE**, First-Faulting loads (`ldff1w` + `rdffr` predicate check) allow vectorizing variable-length or page-straddling tail loops (`strlen` / unaligned search) without knowing buffer bounds up front, whereas NEON/AVX2 must scalarize tails or emit runtime alignment prologues.
2. **Runtime Aliasing Check Explosion (`simd_alias_fp.c`):** Unlike Rust `&mut [T]`/`&[T]` slices (which emit LLVM `noalias` metadata on function arguments—*except* when slices are hidden inside structs or raw pointers!), C/C++ pointers force `LoopAccessInfo` to emit quadratic runtime overlap guards up to `RuntimeMemoryCheckThreshold`. In our `gcc 15.2.0 -O3 -mavx2 -mfma` probe, `saxpy_aliasing` bloats from **72 to 99 instructions** (`23` compare/branch instructions vs `14` with `__restrict__`) before entering the vectorized `ymm` body.
3. **Strict IEEE-754 Non-Associativity (`sum_strict_fp`):** Because IEEE-754 `(a + b) + c != a + (b + c)`, standard safe Rust `iter().sum::<f32>()` and C `for (i) acc += a[i]` forbid tree-lane horizontal SIMD reduction. In our `gcc -O3 -mavx2 -mfma` probe, `sum_strict_fp` compiles to **0 `ymm` instructions**, serializing onto dependent scalar `vaddss` chains (`xmm0`).
4. **WGSL Uniformity Analysis & Host-Shareable Layout Traps (`gpuweb/gpuweb` `wgsl/index.bs`):**
   - **Static Uniformity Over-Approximation (`L12504-12652, L13810-13867`):** `workgroupBarrier()` must execute strictly inside uniform control flow (`L12652`). Yet WGSL's uniformity graph does not track struct fields independently: as `wgsl/index.bs:13812-13837` demonstrates, placing uniform `@builtin(workgroup_id) wgid` inside `struct Inputs` alongside non-uniform `@builtin(local_invocation_index) lid` taints *the entire struct*, rejecting `if inputs.wgid.x == 1 { workgroupBarrier(); }` at shader compilation!
   - **Host-Shareable Padding & Race Alignment (`L11821-12010`):** WGSL mandates 4-byte `bool` (`L11821, 11932-11936`, preventing 1-byte sub-word write races) and assigns `vec3<f32>` `AlignOf = 16` yet `SizeOf = 12` (`L11840-11842`), creating silent CPU-to-GPU struct stride mismatches (`StrideOf(array<vec3<f32>>) = 16`, `L11771, 12000-12007`) unless host Rust/C++ types insert explicit padding or explicit `#[align(16)]` layout checks.
   - As Matt Pharr documented in *The story of ispc*, implicit scalar autovectorization makes vector speed brittle against minor IR/alias perturbations; explicit SPMD type annotations (`uniform` vs `varying`) turn vector legality into a **compile-time type contract** rather than a fragile middle-end heuristic.

### 5. Six-Level Performance, Footprint, and Verification Matrix (`L1`–`L6`)

**Basis:** `source` (`polonius`, `rustc`, `yoke`, `ouroboros`, `LLVM`, `wgsl`) + `execution` (measured `rustc 1.98.0-nightly` & `gcc 15.2.0` probes) + `normative` (`10.1145/3763122`, `10.1145/3735592`) + `derived`.

| Dimension | Rust NLL (`rustc` default) | Datalog Polonius (`polonius-engine`) | `-Zpolonius=next` (`LocalizedConstraintGraph`) | Self-Ref Crates (`yoke` / `self_cell` / `ouroboros`) | Disjoint Slice Splitting (`get_disjoint_mut` vs `unsafe`) | LLVM Auto-Vec vs Explicit SIMD/ISPC/WGSL |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **(L1) Authoring & Day-2 Velocity** | High on local trees; **frequent Day-2 refactoring pain** on Problem Case #3 & interprocedural `self` borrows | Solves Problem Case #3; unshipped as default due to compile cost | Solves Problem Case #3; still fails partial-borrow method splits (`E0502`) | High macro/trait ceremony (`Yokeable` unsafe impls, `'this` restrictions); historical CVE churn (`RUSTSEC-2023-0042`) | `get_disjoint_mut` ergonomic for fixed `[i, j]`; dynamic patterns (FFT/CSR) force `unsafe` wrappers | Scalar loops trivial to write, **brittle Day-2 speedups** (silent AVX2 fallbacks); `ispc`/WGSL enforce explicit SPMD types upfront |
| **(L2) Toolchain & Analyzer Build Cost** | Built into `rustc_borrowck` (no external solver) | Extra `datafrog` engine crate | Built directly inside `rustc_borrowck::polonius` | `ouroboros_macro` proc-macro syn/quote compile overhead (`self_cell` zero proc-macro dep, declarative `macro_rules!`) | Monomorphized `core::slice` generic | LLVM `LoopVectorize` pass + WebGPU Tint/Naga WGSL compiler |
| **(L3) Compile / Check / Lowering Latency** | Fast per-fn MIR fixed-point (~ms); interactive IDE latency | Slow (`O(|Origins|^2 * |Points|)` Datalog tuples caused severe crate timeouts) | Lazy on-demand liveness (`DeferredLivenessSource`, `mod.rs:183`) + packed bitset; orders of magnitude faster than Datalog | Proc-macro expansion (`ouroboros`) vs zero-macro `yoke`; PCG (`10.1145/3763122`) extracts modular capability graphs quickly | Compile-time `O(1)` (`N` const-checked) | Runtime alias/SCEV analysis in LLVM (`LoopVectorizationLegality`); WGSL uniformity graph linear in CFG size (`ShaderCreation` time) |
| **(L4) Runtime Execution Performance** | Zero runtime cost (erased lifetimes) | Zero runtime cost | Zero runtime cost | Zero extra indirection in `Yoke` (inline raw ptrs); `self_cell` allocates 1 combined heap block (`JoinedCell`) | `get_disjoint_mut` pays **$O(N^2)$ runtime overlap check** (`mod.rs:5198, 5737`) vs 0-cycle `unsafe` bijection witness | `cond_deref_raw`: **0 vector ops on AVX2** vs **10 `{%k}`-masked ops + 5 gathers on AVX-512**; `saxpy_aliasing`: 99 vs 72 insns; `sum_strict_fp`: **0 `ymm` ops** (scalar `vaddss` latency bound) |
| **(L5) Verification / Soundness Checking Speed** | Checked on every `cargo check` | Soundness matches MIR facts when complete | `mod.rs:221-258` notes unverified kill + time-travel corner cases requiring `a-mir-formality` / Miri cross-checks | Requires **Miri (`-Zmiri-tree-borrows`)** dynamic checking (`O(10x–100x)` slowdown) to catch `RUSTSEC-2023-0042` / `KindaSortaDangling` UB | Verified statically only by external provers (Creusot/Prusti/Verus) or `assert!` panics | Static `WGSL` uniformity pass rejects barrier races at shader creation; LLVM vectorization uses soundness-conservative opt-out (`0` false miscompile when bailing to scalar) |
| **(L6) Memory & Binary Footprints** | Smallest compiler RSS (compact `RegionVid` bitsets) | High peak compiler RSS on tuple joins in `datafrog` | `LiveLoans`: `num_points * num_borrows` bits (`mod.rs:65-71`) | `Yoke`: 0-byte wrapper (`KindaSortaDangling` niche-preserved via `CartableOptionPointer`, `cartable_ptr.rs:7-14`); `ouroboros`: `#[repr(transparent)] MaybeUninit` | Static `get_disjoint_mut` inlines quadratic `N*(N-1)/2` compare loop per callsite `N` | `saxpy_aliasing` emits +37.5% more instructions (99 vs 72 insns) in `.text` for alias runtime guards; WGSL `vec3<f32>`/`bool` pads CPU->GPU buffers by 25–300% |

### 6. Human Comprehensibility (`C1`) and Universal Conceptual Simplicity (`C2`)

**Basis:** `derived` from inspected sources (`rustc`, `polonius`, `yoke`, `ouroboros`, `LLVM`, `wgsl`, `zesterer/ariadne`) and `10.1145/3763122`.

#### 6.1 (C1) Human Comprehensibility & Diagnostic Legibility

1. **Borrow-Error Working-Memory Overload (`NLL` vs `Polonius` vs `ariadne`):** In `polonius_probe.rs` (`## Evidence`), NLL's diagnostic blames `returning this value requires that *map is borrowed for 'r` across lines 6–12 even though the `None` branch never returns `v`. Conversely, raw Polonius graph traversals risk reporting multi-hop `Origin at Point` time-travel chains across bidirectional invariant edges; `rustc_borrowck/src/polonius/mod.rs:100-104` explicitly filters out `boring_nll_locals` specifically to avoid overwhelming human error renderers (such as `ariadne`-style multi-span overlays) with noisy transitive origins.
2. **Hidden Aliasing Rules in Self-Referential Crates:** No Rust programmer reading `#[self_referencing]` can verify Stacked Borrows / Tree Borrows function-entry protector survival in working memory; discovering why `Drop::drop(&mut self)` triggered UB in `RUSTSEC-2023-0042` or why `Box<T>` needed `KindaSortaDangling` requires knowing compiler MIR `Retag` and LLVM `dereferenceable` lowering rules.
3. **Opaque Compiler Heuristics in Autovectorization & WGSL:** When LLVM silently declines to vectorize `cond_deref_raw` on AVX2 or `sum_strict_fp` on AVX2, the programmer gets **zero compiler error**—only an order-of-magnitude throughput drop visible via `-Rpass-missed=loop-vectorize` or assembly inspection. Similarly, WGSL's composite uniformity rule (`inputs.wgid.x`, `wgsl/index.bs:13810-13837`) breaks intuition because two orthogonal struct fields cross-contaminate uniformity without an annotation in the struct declaration.

#### 6.2 (C2) Simplicity, Adapter Conservation & Minimal Universal Representation

Comparing all four problem domains reveals a striking structural unity: **every failure stems from conflating *address/memory extent* with *disjoint access permissions*, and lacking first-class *place/index partition contracts* in signatures.**

1. **Where Existing Workarounds Merely Shift Complexity:**
   - `ouroboros` and `self_cell` hide self-reference syntax behind macros while shifting soundness onto fragile `'static` erasure, reversed drop fields, `MaybeUninit`, and covariance annotations.
   - `slice::get_disjoint_mut` avoids `unsafe` only by pushing an $O(N^2)$ dynamic overlap check onto fixed-arity arrays `[I; N]`, forcing real kernels (FFT, CSR) back into raw pointers.
   - Scalar autovectorizers avoid language extensions only by shifting performance determinism into fragile middle-end alias/dereferenceability heuristics.
2. **Minimal Universal Model (*Indexed Place & Region Capability Partitions*):** Separating **pinned/stable backing extent** (`Extent(base, len)`) from **partitioned linear capabilities** (`Cap(PlaceSet | IndexPredicate, AccessKind)`) unifies all four domains with fewer concepts than current ad-hoc patches:
   - **Self-Referential Arenas:** A value borrows from a pinned backing `Extent` via relative offsets or capability-indexed handles bound to an existential lifetime, dropping dependents before freeing the `Extent` without `'static` lies or function-entry protector collisions.
   - **Modular Partial Borrows (View Types / PCG):** Method signatures name exact disjoint place capabilities (`&{config} Self` + `&mut {scratch} Self`) instead of whole `&self`, eliminating Problem Case #3 workarounds *and* cross-method `E0502` rejections locally at the type signature level.
   - **Arbitrary Disjoint Slice Splitting & Safe SIMD:** Replacing fixed-arity `O(N^2)` runtime scans with **static/verified disjoint partition witnesses** (e.g., `Partition(S, P_0 ⊔ P_1)` via monotonic `row_ptr` intervals, `(k, k ^ stride)` FFT bit-predicates, or explicit SPMD `uniform`/`varying` lane masks) exposes `LLVM` `noalias` and non-overlapping lane predicates directly to both the borrow checker and the vectorizer—eliminating `unsafe` adapters, `RuntimeMemoryCheckThreshold` branch bloat, and silent AVX2/NEON scalarization in one stroke.

## Boundaries

- **ARM SVE First-Faulting (`ldff1w` / `rdffr`) Codegen Execution:** `not examined` via native execution; this host runs x86-64, so SVE First-Faulting register mechanics are cited from ARM ISA semantics rather than executed natively alongside our `haswell` vs `skylake-avx512` `rustc` probes.
- **Miri (`-Zmiri-tree-borrows`) Execution on `ouroboros < 0.16.0`:** `not executed` in this local environment; the `RUSTSEC-2023-0042` protector violation mechanism is grounded directly in the official RustSec advisory text, Stacked/Tree Borrows publications (`10.1145/3371109`, `10.1145/3735592`), and post-patch source inspection (`ouroboros_macro/src/generate/{struc,drop}.rs`).
- **Soundness Proof of `-Zpolonius=next` Time-Traveling Kills:** `unknown` upstream; `rust-lang/rust` @ `c884ecfbabb04b04fa5054dafc67ec258ecde745` (`compiler/rustc_borrowck/src/polonius/mod.rs:257-258`) explicitly carries `FIXME: analyze potential unsoundness` for backward edge traversal past `loan_killed_at`.
- **Full Rust Language Support for View Types:** `unsupported` in upstream `rustc 1.98.0-nightly (14210df0e 2026-05-31)` as demonstrated by `view_probe.rs` failing with `E0502` even under `-Zpolonius=next`.
- **Variable-Arity Safe Mut Slice Splitting in `core::slice`:** `unsupported` in `rust-lang/rust` @ `c884ecfb...` (`library/core/src/slice/mod.rs:5227`), where `get_disjoint_mut` requires a compile-time `const N: usize` array `[I; N]` and checks overlap in $O(N^2)$ time.
- **Standalone WGSL Shader Execution Against GPU Driver Compilers (Tint/Naga):** `not examined` at runtime; WGSL uniformity and alignment rules are cited directly from the normative specification (`gpuweb/gpuweb` @ `d178d9145ab1652ec933e71a8c30e8f6470f00a3`, `wgsl/index.bs`).

## Evidence

- **Rust Compiler, `core`, & Polonius (`rust-lang/rust` @ `c884ecfbabb04b04fa5054dafc67ec258ecde745`; `rust-lang/polonius` @ `bfd4c945b7713d0e66a3cde80475d9a4494740df`):**
  - `compiler/rustc_borrowck/src/polonius/mod.rs` (L64–262): `LiveLoans` `DenseBitSet`, `LocalizedConstraintGraph`, `ConstraintDirection`, `boring_nll_locals`, and `L221-258` kill/time-travel soundness caveat.
  - `polonius-engine/src/facts.rs` (L6–90) & `polonius-engine/src/output/datafrog_opt.rs` (L50–310): 16 `AllFacts` relations and Datafrog transitive-closure rules.
  - `library/core/src/pin.rs` (L49–160): Move semantics and `Pin` `Drop` guarantee.
  - `library/core/src/slice/mod.rs` (L1997, L5160–5255, L5737–5805): `split_at_mut`, `get_disjoint_unchecked_mut`, `get_disjoint_mut<I, const N: usize>`, quadratic `is_overlapping` loop.
- **Self-Referential Crates:**
  - `taiki-e/pin-project` @ `a0191954d8bdb1c125eb9f53980760c0df743eeb` (`src/lib.rs:29-75, 122-150`).
  - `someguynamedjosh/ouroboros` @ `b75b9c16e6d79b6b8a678ac5bca602134473951d` (`ouroboros/src/lib.rs:144-157`, `ouroboros_macro/src/generate/{struc.rs:19-68, drop.rs:16-20}`) and `RUSTSEC-2023-0042` (`https://rustsec.org/advisories/RUSTSEC-2023-0042.html`).
  - `unicode-org/icu4x` @ `ffe417bb7f83d097047151cd40dde184bdc9cdc4` (`utils/yoke/src/yoke.rs:80-93, 984-1028`, `utils/yoke/src/cartable_ptr.rs:81-195`).
  - `Voultapher/self_cell` @ `93cb06e430e7516ac9b436029a15127782b6c2b6` (`src/lib.rs:390-465`).
- **SIMD, GPU, & Diagnostic Specs:**
  - `llvm/llvm-project` @ `de85491c7e327289d654790197b3432003723b4a` (`llvm/lib/Transforms/Vectorize/LoopVectorizationLegality.cpp:1202-1581`).
  - `gpuweb/gpuweb` @ `d178d9145ab1652ec933e71a8c30e8f6470f00a3` (`wgsl/index.bs:11750-12010` layout/stride/padding, `12504-12652` uniformity rules, `13810-13867` composite uniformity taint).
  - `zesterer/ariadne` @ `5e62913d34dabf34140ad812448dc8faae5abf15`.
- **Peer-Reviewed & Non-Academic Primary Literature:**
  - Jung et al., *Stacked Borrows: An Aliasing Model for Rust*, POPL 2020 (`DOI: 10.1145/3371109`).
  - Villani et al., *Tree Borrows*, PLDI 2025 (`DOI: 10.1145/3735592`).
  - Weiss et al., *Oxide: The Essence of Rust*, `arXiv:1903.00982` (`DOI: 10.48550/arXiv.1903.00982`).
  - *Place Capability Graphs: A General-Purpose Model of Rust's Ownership and Borrowing Guarantees*, OOPSLA 2025 (`DOI: 10.1145/3763122`).
  - Non-academic engineering blogs & advisories: Niko Matsakis (*View types for Rust*, Nov 2021; *Polonius revisited, parts 1 & 2*, Sep 2023); Rémy Rakic & Niko Matsakis (*Polonius update*, Inside Rust Blog, Oct 2023); `RUSTSEC-2023-0042` post-mortem; Matt Pharr (*The story of ispc*).
- **Self-Contained Executable Micro-Probes (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `gcc 15.2.0`):**

```bash
mkdir -p /tmp/repro_pkg2

cat <<'RS' > /tmp/repro_pkg2/polonius_probe.rs
use std::collections::HashMap;
fn get_or_insert<'r, K: Eq + std::hash::Hash + Copy, V: Default>(
    map: &'r mut HashMap<K, V>,
    key: K,
) -> &'r mut V {
    match map.get_mut(&key) {
        Some(v) => v,
        None => {
            map.insert(key, V::default());
            map.get_mut(&key).unwrap()
        }
    }
}
fn main() {
    let mut m: HashMap<i32, i32> = HashMap::new();
    *get_or_insert(&mut m, 1) += 10;
    println!("polonius_pc3: {}", m[&1]);
}
RS

cat <<'RS' > /tmp/repro_pkg2/view_probe.rs
struct Engine { config: Vec<u32>, scratch: Vec<u32> }
impl Engine {
    fn get_config(&self) -> &[u32] { &self.config }
    fn mutate_scratch(&mut self, factor: u32) {
        for x in &mut self.scratch { *x *= factor; }
    }
}
fn main() {
    let mut e = Engine { config: vec![2, 3], scratch: vec![10, 20] };
    let cfg = e.get_config();
    e.mutate_scratch(cfg[0]);
    println!("view: {:?} {:?}", cfg, e.scratch);
}
RS

cat <<'RS' > /tmp/repro_pkg2/disjoint_probe.rs
fn main() {
    let mut data = [10u32, 20, 30, 40, 50, 60, 70, 80];
    let [a, b] = data.get_disjoint_mut([1, 5]).unwrap();
    std::mem::swap(a, b);
    println!("disjoint_static_arity: {:?}", &data);
}
RS

cat <<'RS' > /tmp/repro_pkg2/simd_probe.rs
#[no_mangle]
pub unsafe fn cond_deref_raw(mask: &[u8], ptrs: &[*const u32]) -> u32 {
    let n = mask.len().min(ptrs.len());
    let mut sum = 0u32;
    for i in 0..n {
        if mask[i] != 0 { sum = sum.wrapping_add(*ptrs[i]); }
    }
    sum
}
#[no_mangle]
pub fn cond_slice_sum(mask: &[u8], vals: &[u32]) -> u32 {
    let n = mask.len().min(vals.len());
    let mut sum = 0u32;
    for i in 0..n {
        if mask[i] != 0 { sum = sum.wrapping_add(vals[i]); }
    }
    sum
}
RS

cat <<'C' > /tmp/repro_pkg2/simd_alias_fp.c
#include <stddef.h>
void saxpy_aliasing(float *out, const float *a, const float *b, float k, size_t n) {
    for (size_t i = 0; i < n; i++) out[i] += k * a[i] + b[i];
}
void saxpy_restrict(float * __restrict out, const float * __restrict a, const float * __restrict b, float k, size_t n) {
    for (size_t i = 0; i < n; i++) out[i] += k * a[i] + b[i];
}
float sum_strict_fp(const float *a, size_t n) {
    float acc = 0.0f;
    for (size_t i = 0; i < n; i++) acc += a[i];
    return acc;
}
C

# 1. NLL Problem Case #3 (E0499 under NLL, passes under -Zpolonius=next)
rustc /tmp/repro_pkg2/polonius_probe.rs -o /tmp/repro_pkg2/p1 || true
rustc -Zpolonius=next /tmp/repro_pkg2/polonius_probe.rs -o /tmp/repro_pkg2/p1 && /tmp/repro_pkg2/p1

# 2. Interprocedural partial borrow (E0502 even with -Zpolonius=next)
rustc -Zpolonius=next /tmp/repro_pkg2/view_probe.rs -o /tmp/repro_pkg2/p2 || true

# 3. Constant-arity slice::get_disjoint_mut
rustc /tmp/repro_pkg2/disjoint_probe.rs -o /tmp/repro_pkg2/p3 && /tmp/repro_pkg2/p3

# 4. Conditional pointer deref SIMD probe: AVX2 (haswell) vs AVX-512 (skylake-avx512)
rustc --crate-type=lib -C opt-level=3 -C target-cpu=haswell --emit=asm /tmp/repro_pkg2/simd_probe.rs -o /tmp/repro_pkg2/simd_avx2.s
rustc --crate-type=lib -C opt-level=3 -C target-cpu=skylake-avx512 --emit=asm /tmp/repro_pkg2/simd_probe.rs -o /tmp/repro_pkg2/simd_avx512.s

# 5. C aliasing & strict IEEE-754 summation probe (gcc 15.2.0)
gcc -O3 -mavx2 -mfma -S /tmp/repro_pkg2/simd_alias_fp.c -o /tmp/repro_pkg2/simd_alias_fp.s
```

Recorded execution observations (`2026-11-19`):

```text
# Probe 1a (default NLL): exit 1 -> error[E0499] on map.insert(...) and map.get_mut(&key)
# Probe 1b (-Zpolonius=next): exit 0 -> stdout: polonius_pc3: 10
# Probe 2  (-Zpolonius=next on view_probe.rs): exit 1 -> error[E0502] cannot borrow `e` as mutable (e.get_config() vs e.mutate_scratch())
# Probe 3  (get_disjoint_mut): exit 0 -> stdout: disjoint_static_arity: [10, 60, 30, 40, 50, 20, 70, 80]
# Probe 4  (simd_avx2.s vs simd_avx512.s):
#   simd_avx2.s:   cond_deref_raw={'zmm': 0, 'ymm': 0, 'k_mask': 0, 'gather': 0}, cond_slice_sum={'zmm': 0, 'ymm': 20, 'k_mask': 0, 'gather': 0}
#   simd_avx512.s: cond_deref_raw={'zmm': 0, 'ymm': 10, 'k_mask': 10, 'gather': 5} (vptestmb + vmovdqu64 {%k} {z} + vpgatherqd {%k}), cond_slice_sum={'zmm': 0, 'ymm': 15, 'k_mask': 5, 'gather': 0}
# Probe 5  (simd_alias_fp.s):
#   saxpy_aliasing: total_insns=99 ymm_insns=5 cmp_jmp=23
#   saxpy_restrict: total_insns=72 ymm_insns=5 cmp_jmp=14
#   sum_strict_fp:  total_insns=67 ymm_insns=0 cmp_jmp=19 fp_ops=['vaddss (%rax), %xmm0, %xmm0', ...]
```

## Revalidation

To test whether these borrow-checker, self-reference, or vectorization boundaries change in newer toolchains:

1. **Polonius & Interprocedural View-Type Support Check:** Re-run Probes 1 and 2 against a newer `rustc` (with default borrowck and `-Zpolonius=next`) and inspect `compiler/rustc_borrowck/src/polonius/mod.rs` to check whether kill/time-travel caveats or field-level view types have been resolved:
   ```bash
   curl -sSL "https://raw.githubusercontent.com/rust-lang/rust/<rev>/compiler/rustc_borrowck/src/polonius/mod.rs" | grep -E "FIXME|ConstraintDirection|LiveLoans"
   ```
2. **Self-Referential Crate Storage & `core::slice` Disjointness APIs:** Inspect `icu4x/utils/yoke/src/{yoke,cartable_ptr}.rs` (`KindaSortaDangling`), `ouroboros_macro/src/generate/struc.rs` (`MaybeUninit`), and `library/core/src/slice/mod.rs` (`get_disjoint_mut` overlap complexity):
   ```bash
   curl -sSL "https://raw.githubusercontent.com/rust-lang/rust/<rev>/library/core/src/slice/mod.rs" | grep -n -A5 "fn get_disjoint_mut"
   ```
3. **LLVM & WGSL Predication/Uniformity Gates:** Diff `LoopVectorizationLegality::canVectorizeWithIfConvert` (`LoopVectorizationLegality.cpp`) and `wgsl/index.bs` (`Composite Value Analysis Limitations`), and re-run Probe 4 (`--emit=asm -C target-cpu=haswell` vs `skylake-avx512`) and Probe 5 (`gcc -O3 -mavx2 -mfma -S`) to verify whether new hardware or compiler passes change scalar fallback behavior.
