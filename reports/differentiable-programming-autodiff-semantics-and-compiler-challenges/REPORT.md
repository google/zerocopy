# Differentiable Programming: Automatic Differentiation Semantics, Compiler Placement, Checkpointing, and Hazards

## Summary

Automatic differentiation (AD) is a program transformation whose runtime cost, memory footprint, parallelism, and mathematical soundness are governed by four coupled axes: **compiler IR placement**, **reversal of irreversible control and state**, **semantic behavior at branch boundaries and nested invocations**, and **foreign-function / parallelism contracts**.

1. **IR placement trades optimization leverage against semantic structure.** Differentiating *after* scalar/loop optimizations on LLVM IR (`Enzyme`) avoids differentiating dead code, stack temporaries, and uninlined abstractions—achieving a 4.5x geometric mean speedup over pre-optimization IR AD (Moses & Churavy 2020)—but must reconstruct erased byte types (`TypeAnalysis`), pointer activity (`ActivityAnalysis`), and minimal caching (`DifferentialUseAnalysis::minCut`), hitting hard walls on inline assembly, type-erased `memcpy`, opaque FFI, and indirect calls in parallel regions. Conversely, functional linearize-then-transpose compilers (`Dex`, `JAX`; Radul et al. 2023) eliminate dynamic tapes for statically bounded loops (`For Fwd` $\leftrightarrow$ `For Rev`, `RunReader` $\leftrightarrow$ `RunWriter`) at the cost of rejecting reverse-mode dynamic `while_loop` (`jax/_src/lax/control_flow/loops.py`) and arbitrary array mutation (`Zygote.jl` `src/lib/array.jl`).
2. **Binomial checkpointing (`Revolve`) is optimal on uniform chains, while general reversal is NP-complete.** Reverse-mode taping turns $O(1)$-space forward loops into $O(l)$ memory. On uniform chains of length $l$ with $c$ checkpoint slots, Griewank & Walther's Algorithm 799 attains the exact dynamic-programming optimum $p(l, c) = r \cdot l - \binom{c+r}{c+1}$ where $\binom{c+r-1}{c} < l \le \binom{c+r}{c}$, achieving simultaneous $O(\log l)$ space and $O(\log l)$ recomputation factor along $c = r$ ($\beta(6, 6) = 924$). On arbitrary graphs, optimal Jacobian accumulation (Naumann 2008), call-tree reversal (Naumann 2008), and DAG reversal (Naumann 2009) are all NP-complete, forcing compilers to rely on polynomial heuristics (Enzyme `minCut`) or user policies (`jax.checkpoint`).
3. **Operational AD is intensional, almost-everywhere correct, and does *not* guarantee Clarke subgradients.** Operational AD differentiates only the branch taken, breaking extensionality (`id_plain(x) = x` vs. `0.0 if x == 0.0 else x` gives `1.0` vs. `0.0` at `0`). Because Clarke's generalized Jacobian lacks an equality chain rule, composing valid ReLU subgradients on the $C^\infty$ identity $h(x) = \mathrm{ReLU}(x) - \mathrm{ReLU}(-x) \equiv x$ produces `0.0` (`x > 0`) or `2.0` (`x >= 0`) at $x = 0$, both outside $\partial^C h(0) = \{1\}$. Rigorous semantics use **diffeologies and categorical gluing** for higher-order smooth AD (Huot, Staton & Vákár 2020), **PAP intensional derivatives** (Lee et al. 2020), **conservative fields** (Bolte & Pauwels 2021), and **almost-everywhere correctness up to measure zero** in PCF (Mazza & Pagani 2021).
4. **Nested differentiation and floating-point masking corrupt gradients silently unless explicitly guarded.** Untagged dual numbers suffer **perturbation confusion** (Siskind & Pearlmutter 2008), returning `2.0` (with primal `2x`) instead of `1.0` for $\frac{d}{dx}[x \cdot \frac{d}{dy}(x + y)\big|_{y=1}]$. Naive dynamic nesting-depth tagging still fails on escaping higher-order closures (Manzyuk et al. 2019), requiring monotonic fresh tag identities (e.g., JAX `TraceTag` + leak checks). In predicated reverse mode, IEEE-754 `0.0 * inf = NaN` poisons masked branches (`where(x > 0, sqrt(x), 0.0)` at `0.0`), requiring primal double-`where` guards or zero-cotangent short-circuiting (`Enzyme` `strongZero`).
5. **Parallelism and FFI are duality and unchecked trust boundaries.** Reverse-mode duality converts race-free concurrent forward reads into concurrent adjoint writes, requiring atomic float accumulation (`Enzyme` OpenMP/GPU) or typed commutative monoid effects (`Dex` `RunWriter`/`MExtend`). Custom derivative hooks (`enzyme_gradient`, `custom_vjp`, `@adjoint`, `@derivative`) form the de facto derivative FFI, yet remain mathematically unchecked trust assumptions across production compilers.

## Applicability

This report documents compiler architecture, checkpointing complexity, formal semantics, and numerical/FFI failure modes for **automatic differentiation and differentiable programming toolchains** across low-level imperative IRs, mid-level SSA IRs, and functional array languages.

### Subject Relationships

The twenty durable subjects in `REPORT.json` cross-check four layers of primary evidence:

- **Pinned compiler implementations (`source`)**: `EnzymeAD/Enzyme` (`0fa6f8401af6b8211a783213643692be20508842`), `google-research/dex-lang` (`25e2e389b90403ae2f8d67fb6d52f47d23c439ee`), `jax-ml/jax` (`bb38c58379173719d63a7e81fc09c22a37502654`), `FluxML/Zygote.jl` (`78463a14bc67a66435fc5ac3797422eaf9f6d589`), and `swiftlang/swift` (`49fb0090b22cd6dcde645455e7cbf089380f88e4`) provide direct source-code evidence of pass placement, tape/transposition invariants, custom-rule ABI hooks, and unsupported boundaries.
- **Compiler & complexity literature (`normative` / `documentation`)**: Moses & Churavy (2020), Moses et al. (2021, 2022), Paszke et al. (2021), Radul et al. (2023), Griewank & Walther (2000), and Naumann (2008, 2009) establish speedup measurements, linear-type transposition soundness, optimal binomial checkpointing, and NP-completeness bounds.
- **Semantic & hazard theory (`normative`)**: Huot, Staton & Vákár (2020), Lee et al. (2020), Mazza & Pagani (2021), Bolte & Pauwels (2021), Siskind & Pearlmutter (2008), Manzyuk et al. (2019), and Hückelheim et al. (2023) formalize exact derivative objects and systemic pitfalls.
- **Executable probe (`execution`)**: [`support/verify_autodiff_transposition_and_hazards.py`](support/verify_autodiff_transposition_and_hazards.py) (Python 3.10+ stdlib only) reproduces and asserts the Dex 3-pass pipeline, perturbation-confusion bugs and fixes, Clarke/NaN branch hazards, and Revolve optimality on a live 100-step recurrence.

### Adjacent Corpus Cross-References and Scope Limits

- For PDE scientific computing frameworks (Firedrake, FEniCSx, Dedalus, Devito) and floating-point error verification (VCFloat), see `anneal-synbio-crns-pde-physics-math-and-rail-survey`.
- For LLVM IR memory/poison semantics (`noalias`, MemorySSA) and middle-end pass verification (Alive2, Vellvm, Crellvm, Lean-MLIR) underlying post-optimization IR AD, see `anneal-mid-level-ir-optimizations-and-lowering-survey`.
- Compiler-specific source citations apply strictly to the pinned revisions listed above. Semantic theorems over $\mathbb{R}$ (Huot et al., Lee et al., Mazza & Pagani, Bolte & Pauwels) do not automatically carry over to IEEE-754 rounding or `NaN` propagation; floating-point hazards are documented separately.

## Findings

### 1. Compiler IR Placement and Architectural Taxonomy of Reverse-Mode AD

Basis: source (`EnzymeAD/Enzyme`, `google-research/dex-lang`, `jax-ml/jax`, `FluxML/Zygote.jl`, `swiftlang/swift`) + normative (Moses & Churavy 2020; Paszke et al. 2021; Radul et al. 2023) + execution (`support/verify_autodiff_transposition_and_hazards.py` Part a)

Where AD sits in the compilation pipeline determines both asymptotic code quality and which language features can be differentiated. Early AD preserves source types and domain abstractions, but differentiates dead branches, uninlined wrappers, and redundant allocations, emitting coupled primal+tape code that downstream optimizers struggle to simplify. Late post-optimization AD differentiates lean scalarized loops, but must recover erased type, alias, and activity metadata via static analyses that fail on opaque low-level constructs.

| Architecture Class | Reference System | IR / Pipeline Placement | Primal-to-Adjoint State | Mutation & Aliasing | Dynamic `while` Loops | Primary Friction Wall |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Eager Dynamic Tape** | PyTorch Autograd (baseline) | Runtime dispatch (pre-IR) | Heap autograd graph / saved tensors | Version-counter check; errors on clobbered primal | Supported dynamically (unrolled tape) | Dispatch overhead, missed fusion/SROA, unbounded tape RAM |
| **High-Level SSA Pullback** | `FluxML/Zygote.jl` (`78463a14`) | Julia `IRTools.IR` (pre-LLVM opt) | Pullback closures + `BranchNumber` block args (`reverse.jl:239-253`) | Forbidden on `AbstractArray` (`lib/array.jl:71-91`); opt-in `Buffer` (`lib/buffer.jl`) | Dynamic pullback stack & branch tags | Closure allocation, type instability, mutation errors |
| **Mandatory Mid-Level SSA** | `swiftlang/swift` (`49fb0090`) | Swift mandatory SIL (`PassPipeline.cpp:206`, pre-opt) | Per-BB linear-map tuples + `predecessor` trace enums (`LinearMapInfo.cpp:341-415`) | Value semantics & `inout` via SIL ownership / `bufferMap` (`PullbackCloner.cpp:100`) | Recursive/boxed trace enums | Pre-optimization AD; loop trace boxing |
| **Staged Partial Eval + Transpose** | `jax-ml/jax` (`bb38c583`) | Python trace $\to$ functional `jaxpr` $\to$ XLA | `linearize` extracts residuals + linear `jaxpr` (`ad.py:227-275`) | Pure arrays; restricted Ref discharge | JVP works (`loops.py:1998`); reverse raises `ValueError` (`loops.py:2192-2195`) | XLA static-shape bound blocks reverse `while_loop` |
| **Typed Index-Set Transpose** | `google-research/dex-lang` (`25e2e389`) | Typed `SimpIR` with index sets `Ix` | `linearizeExprDefuncGeneral` residuals (`Linearize.hs:255-267`) + `For Fwd` $\leftrightarrow$ `For Rev` (`Transpose.hs:259-265`) | Typed `RunWriter`/`MExtend` & `RunState`; raw `MemOp` rejected (`Transpose.hs:220`) | Statically bounded `For` index sets | Strict linearity; `Select`/`SumCon`/`BitcastOp` unimplemented |
| **Post-Opt Low-Level IR** | `EnzymeAD/Enzyme` (`0fa6f840`) | LLVM IR post `AlwaysInliner`, `GVN`, `SROA` (`Enzyme.cpp:3253-3284`) | Shadow pointers + `minCut` primal cache/tape (`DifferentialUseAnalysis.cpp:874-995`) | Imperative pointers, aliasing, OpenMP/CUDA atomics | Supported via dynamic reallocated tapes (`CacheUtility`) | Type-erased `memcpy`, `InlineAsm`, opaque FFI, OpenMP indirect calls |

#### 1.1 Post-Optimization LLVM IR AD (`EnzymeAD/Enzyme`)

Moses & Churavy (NeurIPS 2020, `arXiv:2010.01709`) measured a **4.5x geometric mean speedup** from differentiating *optimized* LLVM IR over pre-optimization IR across ADBench and ML benchmarks. Direct inspection of `EnzymeAD/Enzyme@0fa6f8401af6b8211a783213643692be20508842` exposes the exact pipeline mechanics, required analyses, and hard walls:

- **Pass placement**: In LLVM's Legacy Pass Manager (`EnzymePassLoader.cpp:47-78`), `loadPass` hooks into `PassManagerBuilder::EP_VectorizerStart`, bracketing `Enzyme(PostOpt=true)` with `PreserveNVVM`, `GVN`, and `SROA` before AD and `GVN`, `SROA`, `LoopDeletion`, and `GlobalOpt` after AD—collapsing stack allocations into SSA registers before synthesizing tapes and avoiding target vector shuffles. In LLVM 16+'s New Pass Manager (`Enzyme.cpp:3253-3294`), `loadPass` runs `prePass -> AlwaysInlinerPass -> GVNPass -> SROAPass -> EnzymeNewPM -> PreserveNVVMNewPM -> GVNPass -> SROAPass -> LoopDeletionPass -> GlobalOptPass` via `PB.registerOptimizerEarlyEPCallback(loadPass)` (lines `3283, 3290-3292` note that `registerVectorizerStartEPCallback` requires a `FunctionPass` whereas Enzyme is a `ModulePass`). Under LTO (`Enzyme.cpp:3243-3250`), differentiation defers to post-link unless `-enzyme-lto-prelink=1` is set.
- **Four static recovery analyses**:
  1. **Type Analysis (`TypeAnalysis/TypeAnalysis.h:133-218`)**: Because LLVM opaque pointers (`ptr`) and untyped `llvm.memcpy`/`malloc` erase float-vs-integer layouts, Enzyme computes an interprocedural byte-offset `TypeTree` per SSA value so `TypeResults::query(val)` distinguishes floating-point tangent slots from integer/pointer metadata.
  2. **Activity Analysis (`ActivityAnalysis.h:67-138`, `ActivityAnalysis.cpp:960-1200`)**: `ActivityAnalyzer` runs bidirectional (`UP | DOWN`) hypothesis propagation using LLVM `AliasAnalysis` and `TargetLibraryInfo` to separate active values from constants. Callers declare argument/return `DIFFE_TYPE` (`CONSTANT`, `OUT_DIFF`, `DUP_ARG`, `DUP_NONEED`; `Enzyme.cpp:568-579`). `Enzyme.cpp:934-938` rejects `OUT_DIFF` (`enzyme_active`) on non-`byval` pointer arguments (requiring `DUP_ARG` / `enzyme_dup` with a shadow pointer), whereas mis-annotating an active argument `enzyme_const` or active callee `enzyme_inactive` compiles cleanly into **silently zeroed gradients**.
  3. **Shadow Pointers & Overwrite Taping (`CacheUtility.h:82-145, 270-297`, `EnzymeLogic.cpp:237-304`)**: Active memory allocations get shadow allocations holding cotangents; overwritten primal values needed in reverse (`is_value_mustcache_from_origin`) are cached on forward tapes indexed by loop trip limits (`LimitContext`).
  4. **Min-Cut Caching (`DifferentialUseAnalysis.h:548-562`, `DifferentialUseAnalysis.cpp:874-995`)**: `DifferentialUseAnalysis::minCut` builds a split-vertex flow graph `G` between `Recomputes` and `Required` reverse-pass values, solves max-flow/min-cut via BFS augmenting paths, and weights candidates by `getCacheLoop` (handling entry-block `alloca` with intra-loop `llvm.lifetime.start`) and `getCacheSizeInBits` to choose minimal primal caching versus reverse-pass recomputation.
- **Hard low-level walls in Enzyme**:
  - **Type-erased memory transfers (`AdjointGenerator.h:4020-4201`)**: `visitMemTransferCommon` calls `EmitNoTypeError("Cannot deduce type of copy ...")` (`L4195-4196`) when `TypeAnalysis` fails on `llvm.memcpy`/`memmove`, falling back to `BaseType::Integer` or `BaseType::Pointer`. Analogous type-deduction errors guard loads, stores, phis, and aggregate extracts/inserts (`AdjointGenerator.h:620-628, 1394-1438, 2347, 2523`; `EnzymeLogic.cpp:3566`).
  - **Inline assembly (`CallDerivatives.cpp:3515-3546`, `ActivityAnalysis.cpp:605-609, 2798-2807`)**: Only `"exit"` and `"cpuid"` are recognized as inactive inline assembly, and only the exact x86 string `"maxpd $1, $0"` has a derivative rule (delegated to `Intrinsic::maxnum`). Any other active `InlineAsm` fails.
  - **Indirect calls (`AdjointGenerator.h:5886-5898, 6284-6297, 5504-5505`)**: Active indirect calls require loading a paired shadow function pointer (guarded by a runtime `"Attempting to call an indirect active function whose runtime value is inactive"` check), and OpenMP indirect calls hit `assert(0 && "openmp indirect unhandled")` (`L5505`).
  - **Opaque external calls (`EnzymeLogic.cpp:2548-2552, 4402`)**: Active external functions lacking IR bodies abort with `"No augmented forward pass found"` / `"No reverse pass found"` unless paired with custom-rule metadata (`Utils.h:1744-1749`).

#### 1.2 Functional 3-Pass Decomposition: Linearize + Unzip + Structural Transpose (`Dex`)

Radul et al. (POPL 2023, `arXiv:2204.10923`, DOI `10.1145/3571236`) and Paszke et al. (ICFP 2021, `arXiv:2104.05372`, DOI `10.1145/3473593`) decompose reverse-mode AD into three composable passes:

1. **Linearize (`JVP`)**: Transform $f : A \to B$ into $x \mapsto (f(x), \; df_x : T_x A \multimap T_{f(x)} B)$, statically proving $df_x$ is algebraically linear in tangents.
2. **Unzip (Partial Evaluation)**: Separate nonlinear primal computations from the linear tangent map, returning $(y, r)$ (output plus minimal residuals $r$) and a residualized linear map $L(r) : TA \multimap TB$. Choosing whether to save a `let`-binding in $r$ or recompute it in $L$ naturally yields checkpointing.
3. **Structural Transpose (`VJP`)**: Mechanically flip $L(r)$ into $L(r)^\top : T^* B \multimap T^* A$ without knowing nonlinear calculus rules (`sin`, `exp`, `div`), since all local derivatives were already lowered into residual multipliers during linearization.

In `google-research/dex-lang@25e2e389b90403ae2f8d67fb6d52f47d23c439ee`, this architecture eliminates dynamic tapes for pointful array loops:
- **`src/lib/Linearize.hs:216-267, 604-621`**: `linearizeExprDefuncGeneral` runs `linearizeExpr` to produce `WithTangent primalResult tangentFun` and uses `telescopicCapture` (`MaybeReconAbs`: `TrivialRecon` vs. `ReconWithData`) to bundle only needed residuals. For a `For d ixTy lam` loop (`L606-621`), the primal `For` emits a statically typed residual array indexed by `ixTy`, consumed by a matching linear tangent `For` loop.
- **`src/lib/Transpose.hs:27-55, 89-148, 155-306`**:
  - `withAccumulator` (`L89-106`) introduces a `RunWriter` effect over the tangent monoid `(0, +)` (omitted via `LinTrivial` for singleton types).
  - `transposeWithDecls` (`L115-137`) walks `LinearLet` bindings in reverse; `Project` and `TabApp` (`x.i`) use `projectLinearRef` (`L139-148`) to emit `mkProjRef` / `mkIndexRef` projections directly into the parent accumulator, converting forward gathers into in-place `MExtend` scatter-adds (`L108-111`).
  - `transposeHof` (`L257-288`) executes exact control/effect duality: `For ann ixTy lam` becomes `For (flipDir ann) ixTy ...` (`Fwd` $\leftrightarrow$ `Rev`, `L303-306`) with **zero dynamic tape**; `RunReader` $\leftrightarrow$ `RunWriter` (`MAsk` $\leftrightarrow$ `MExtend`, `L190-195, 273-287`); `RunState` $\leftrightarrow$ `RunState` (`MGet` adds into state cotangent; `MPut` pulls and zeroes, `L196-201, 266-272`).
  - `BinOp FMul x y` relies on the canonical invariant that the linear argument is always on the LHS (`L210-214`). `MemOp` fails (`notLinear`, `L220`), while `Select`, `CastOp`, `BitcastOp`, `SumCon`, `DepPair`, `IndexRef`, and `ProjRef` are `notImplemented` (`L202-203, 233-237, 295-297`).

Our executable probe (`support/verify_autodiff_transposition_and_hazards.py` Part a) implements this 3-pass IR—including a pointful `SumFor` loop with overlapping fan-out reads `w[i % 3]` and `w[(i + 1) % 3]` transposed into `TransposedForRev` associative accumulation—and verifies `|JVP - exact| = 0.00e+00`, `|<Jv, u> - <v, J^T u>| = 1.78e-15`, and maximum central finite-difference error `9.48e-10` with zero dynamic tape.

#### 1.3 Staged `jaxpr` (`JAX`) vs. High-Level SSA Pullbacks (`Zygote.jl`, `Swift` SIL)

- **`jax-ml/jax@bb38c58379173719d63a7e81fc09c22a37502654`**: `linearize` (`jax/_src/interpreters/ad.py:227-275`) traces Python through `LinearizeTrace` and `pe.DynamicJaxprTrace(dbg, auto_dce=True)` (stamped with a fresh `core.TraceTag()`), yielding residuals and a linear `jaxpr`. `backward_pass` / `backward_pass3` (`ad.py:300-526`) reverses that `jaxpr` using `ValAccum` accumulators for `UndefinedPrimal` inputs (`L277-289`). Because XLA requires static memory bounds, `_while_loop_jvp` (`jax/_src/lax/control_flow/loops.py:1998-2051`) supports forward-mode `while_loop`, whereas `ad.primitive_transposes[while_p] = _while_transpose_error` (`L2192-2195, 2603`) raises `ValueError` for reverse-mode `while_loop` and dynamic-bound `fori_loop`, forcing bounded `lax.scan` + `jax.checkpoint` (`ad_checkpoint.py:255-399`) or `custom_vjp`.
- **`FluxML/Zygote.jl@78463a14bc67a66435fc5ac3797422eaf9f6d589`**: Differentiates Julia `IRTools.IR` before LLVM optimization. `record_branches!` (`src/compiler/reverse.jl:239-253`) inserts synthetic `BranchNumber` arguments at CFG join blocks; `adjointcfg` (`L335-350`) reverses blocks by switching on `BranchNumber`; `adjoint` (`L378-393`) accumulates adjoints via `AccumBuffer`. Because Julia arrays allow unchecked aliasing, `src/lib/array.jl:71-91` rejects `setindex!`, `copyto!`, `push!`, `pop!`, `pushfirst!`, and `popfirst!` (`"Mutating arrays is not supported"`), requiring `Zygote.Buffer` (`src/lib/buffer.jl:1-55`), whose `setindex!` pullback reads and zeroes the side-table `grad_mut` entry.
- **`swiftlang/swift@49fb0090b22cd6dcde645455e7cbf089380f88e4`**: Runs `P.addDifferentiation()` inside the **mandatory SIL pipeline** (`PassPipeline.cpp:206`), prior to general SIL/LLVM optimizations. `LinearMapInfo.cpp:341-415` synthesizes per-block `predecessor`/`successor` branching trace enums and linear-map tuples in reverse post-order, and `PullbackCloner.cpp:61-120` emits post-order reversed blocks using `bufferMap` for address-only values; loop traces thus require heap-backed recursive enums unless later scalarized.

---

### 2. Memory/Time Complexity, Binomial Checkpointing (`Revolve`), and NP-Hardness of General Reversal

Basis: normative (Griewank & Walther 2000; Naumann 2008, 2009) + source (`EnzymeAD/Enzyme`, `jax-ml/jax`) + execution (`support/verify_autodiff_transposition_and_hazards.py` Part d) + derived

#### 2.1 Reverse-Mode Space-Time Asymmetry and Binomial Checkpointing (`Revolve`)

By the Baur–Strassen cheap-gradient bound, reverse-mode AD computes all $n$ partial derivatives of $f : \mathbb{R}^n \to \mathbb{R}$ in $O(T)$ arithmetic operations (versus $O(n \cdot T)$ for forward mode). Because backward propagation consumes nonlinear intermediates in reverse chronological order, reversing an $l$-step in-place loop $s_{t+1} = F_t(s_t, \theta)$ requires either $O(l)$ memory (full tape) or $\frac{l(l-1)}{2} = \Theta(l^2)$ forward recomputations (storing only $s_0$).

**Griewank & Walther (2000, ACM TOMS 26(1), DOI `10.1145/347837.347846`)** proved the exact optimum for reversing a uniform $l$-step chain using at most $c$ checkpoint slots. Let $p(l, c)$ be the minimum number of forward **advance** steps (excluding the $l$ mandatory `youturn` forward+adjoint steps). Holding the start state in one slot, advancing $k$ steps, reversing $[k, l)$ with $c - 1$ slots, restoring and freeing the suffix slots, and reversing $[0, k)$ with $c$ slots gives:

$$p(1, c) = 0 \;\; (c \ge 0), \qquad p(l, 0) = +\infty \;\; (l > 1), \qquad p(l, c) = \min_{1 \le k \le l-1}\!\big(k + p(l - k, c - 1) + p(k, c)\big).$$

The maximum chain length reversible with $c$ slots and at most $r$ advance repetitions per step is the binomial capacity:

$$\beta(c, r) = \binom{c + r}{c} = \frac{(c + r)!}{c!\, r!}.$$

Let $r \ge 0$ be the unique integer with $\beta(c, r - 1) < l \le \beta(c, r)$ ($\beta(c, -1) = 0$). Then the exact DP optimum is:

$$p(l, c) = r \cdot l - \binom{c + r}{c + 1},$$

achieved by any split $k$ with $\max(1, \beta(c, r-2), l - \beta(c-1, r)) \le k \le \min(l-1, \beta(c, r-1), l - \beta(c-1, r-1))$. Along $c = r$, $\beta(c, c) = \binom{2c}{c} \sim \frac{4^c}{\sqrt{\pi c}}$, yielding **simultaneous $O(\log l)$ space and $O(\log l)$ recomputation factor** ($\beta(5, 5) = 252$, $\beta(6, 6) = 924$).

##### Binomial Capacity $\beta(c, r) = \binom{c+r}{c}$

| Slots $c$ | $r = 1$ | $r = 2$ | $r = 3$ | $r = 4$ | $r = 5$ | $r = 6$ |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **1** | 2 | 3 | 4 | 5 | 6 | 7 |
| **2** | 3 | 6 | 10 | 15 | 21 | 28 |
| **3** | 4 | 10 | 20 | 35 | 56 | 84 |
| **4** | 5 | 15 | 35 | 70 | 126 | 210 |
| **5** | 6 | 21 | 56 | 126 | 252 | 462 |
| **6** | 7 | 28 | 84 | 210 | 462 | **924** |

##### Live Revolve Adjoint Execution vs. Full Tape ($l = 100$)

Verified in `support/verify_autodiff_transposition_and_hazards.py` Part (d) on $s_{t+1} = 0.6 \sin(s_t + 0.1 t) + 0.35 \theta \cos(s_t)$, $\mathcal{L}(s_{100}) = \frac{1}{2} s_{100}^2$, after confirming exact `DP[l][c] == r*l - C(c+r, c+1)` across all 960 cells in $1 \le l \le 120, 1 \le c \le 8$:

| Strategy | Peak Slots | Forward Advances $p(100, c)$ | Total Forward Factor $(p + l)/l$ | Max Repetitions $r$ | Gradient Error vs. Full Tape |
| :--- | ---: | ---: | ---: | ---: | :--- |
| Full Tape | 100 | 0 | $1.00\times$ | 0 | $0$ (FD diff $1.93 \times 10^{-12}$) |
| Fixed-Stride $\sqrt{l}$ (2-level) | 19 | 90 | $1.90\times$ | 1 | $O(\varepsilon_{\text{mach}})$ |
| **Revolve ($c = 10$)** | **10** | **222** | **$3.22\times$** | 3 | $< 10^{-13}$ (exact optimal) |
| **Revolve ($c = 5$)** | **5** | **316** | **$4.16\times$** | 4 | $< 10^{-13}$ (exact optimal) |
| **Revolve ($c = 4$)** | **4** | **374** | **$4.74\times$** | 5 | $< 10^{-13}$ (exact optimal) |
| **Revolve ($c = 3$)** | **3** | **490** | **$5.90\times$** | 7 | $< 10^{-13}$ (exact optimal) |
| **Revolve ($c = 2$)** | **2** | **845** | **$9.45\times$** | 13 | $< 10^{-13}$ (exact optimal) |
| Naive Recompute ($c = 1$) | 1 | 4,950 | $50.50\times$ | 99 | $O(\varepsilon_{\text{mach}})$ |

At $c = 5$, Revolve cuts memory by **20x** for only **4.16x** forward work; at $c = 10$, **10x** memory reduction costs **3.22x**.

#### 2.2 NP-Completeness on General Graphs and Compiler Approximations

Beyond uniform chains of known length $l$, Uwe Naumann proved **three distinct NP-completeness barriers**:

1. **Optimal Jacobian Accumulation** (Naumann 2008, *Math. Program.* 112(2), pp. 427–441, DOI `10.1007/s10107-006-0042-z`): Minimizing scalar multiplications over vertex/edge elimination orders on a fixed linearized computational graph is NP-complete.
2. **Call Tree Reversal** (Naumann 2008, *Advances in Automatic Differentiation*, LNCSE 64, pp. 13–22, DOI `10.1007/978-3-540-68936-2_2`): Choosing split (taped) vs. joint (checkpointed/recomputed) reversal across a weighted call tree under a global memory bound is NP-complete.
3. **DAG Reversal** (Naumann 2009, *J. Discrete Algorithms* 7(4), pp. 402–410, DOI `10.1016/j.jda.2008.12.003`): Finding a minimum-recomputation schedule to reverse an arbitrary computational DAG under a fixed checkpoint budget is NP-complete.

**Engineering consequence (derived):** Compilers partition reversal into tractable approximations: Enzyme's polynomial max-flow/min-cut solver (`DifferentialUseAnalysis.cpp:874-995`) plus MLIR structured binomial checkpointing (`LowerBinomialProgressPass.cpp`); JAX's declarative `jax.checkpoint` / `checkpoint_policies` (`ad_checkpoint.py:255-399, 892-918`); and implicit differentiation for convergence-driven `while` loops whose trip count $l$ is unknown ahead of time.

---

### 3. Semantic Foundations, Non-Differentiable Branch Traps, Perturbation Confusion, and Float Hazards

Basis: normative (Huot, Staton & Vákár 2020; Lee, Yu, Rival & Yang 2020; Mazza & Pagani 2021; Bolte & Pauwels 2021; Siskind & Pearlmutter 2008; Manzyuk et al. 2019; Hückelheim et al. 2023) + source (`EnzymeAD/Enzyme`, `jax-ml/jax`) + execution (`support/verify_autodiff_transposition_and_hazards.py` Parts b & c)

#### 3.1 Higher-Order Semantics: Diffeological Spaces and Categorical Gluing

First-order smooth AD admits direct calculus semantics (Abadi & Plotkin, POPL 2020, DOI `10.1145/3371106`), but finite-dimensional smooth manifolds ($\mathbf{Man}$) are **not Cartesian closed** and cannot interpret higher-order function types $A \Rightarrow B$. **Huot, Staton & Vákár (FoSSaCS 2020, DOI `10.1007/978-3-030-45231-5_17`, `arXiv:2001.02209`)** interpret higher-order languages with algebraic data types in the Cartesian-closed category $\mathbf{Diff}$ of **diffeological spaces** (sets equipped with smooth "plots" $U \subseteq \mathbb{R}^n \to X$ closed under smooth reparametrization, constants, and gluing), characterize forward-mode AD as the unique structure-preserving macro, and prove semantic correctness via **categorical gluing** (a semantic logical relation). Companion foundations extend this to higher-order reverse-mode AD via **CHAD** (Vákár ESOP 2021, DOI `10.1007/978-3-030-72019-3_22`; Smeding & Vákár TOPLAS 2022, DOI `10.1145/3527634`) and provably asymptotically efficient higher-order reverse AD (Krawiec et al., POPL 2022, DOI `10.1145/3498710`).

#### 3.2 Non-Differentiable Branches and Refutation of the Clarke Subdifferential Myth

Operational AD differentiates *the branch actually taken*, causing three concrete pathologies verified in `support/verify_autodiff_transposition_and_hazards.py` Part (c):

1. **Extensionality breaks at branch boundaries**: `id_plain(x) = x` and `id_piecewise(x) = 0.0 if x == 0.0 else x` are extensionally equal on all $\mathbb{R}$ ($C^\infty$, derivative `1.0`), yet operational AD returns **`0.0`** for `id_piecewise` at $x = 0.0$ (and unguarded `x * (x / x)` produces `NaN`).
2. **Boundary asymmetry at `ReLU(0)`**: `relu_gt(x) = x if x > 0.0 else 0.0` yields `0.0` at $x = 0$, whereas `relu_ge(x) = x if x >= 0.0 else 0.0` yields `1.0`.
3. **Operational AD can violate Clarke subdifferentials even on $C^\infty$ functions**: Clarke's generalized Jacobian obeys only inclusion ($\partial^C(f \circ g)(x) \subseteq \operatorname{conv}\{\partial^C f(g(x)) \cdot \partial^C g(x)\}$), not equality. Consider $h(x) = \mathrm{ReLU}(x) - \mathrm{ReLU}(-x) \equiv x$ identically on $\mathbb{R}$, so $h'(0) = 1$ and $\partial^C h(0) = \{1\}$. Yet operational AD evaluates both ReLUs independently at $x = 0$:
   - Under `relu_gt` ($x > 0$): both arms return `0.0` $\implies \text{AD}[h](0) =$ **`0.0`** $\notin \{1\}$.
   - Under `relu_ge` ($x \ge 0$): the arms return `1.0` and `-1.0` $\implies \text{AD}[h](0) = 1 - (-1) =$ **`2.0`** $\notin \{1\}$.

| Work | Language / Class | Derivative Object | Formal Guarantee | Residual Gap |
| :--- | :--- | :--- | :--- | :--- |
| **Lee, Yu, Rival & Yang (NeurIPS 2020)** | First-order **PAP functions** (*piecewise analyticity under analytic partition*) | **Intensional derivatives** (representation-dependent) | Always exist, capture operational AD, and equal true derivatives **almost everywhere** (outside a measure-zero set) | Syntactic sensitivity on boundaries; need not lie in $\partial^C$ |
| **Bolte & Pauwels (Math. Program. 2021)** | Definable / o-minimal networks | **Conservative set-valued fields** (obeying exact chain rule) | Backpropagation selects a conservative field everywhere; yields nonsmooth SGD convergence | Strictly larger than $\partial^C$ at spurious cancellations (e.g., $\{0, 1, 2\}$ above) |
| **Mazza & Pagani (POPL 2021)** | Higher-order Turing-complete **PCF + reals** (forward & reverse) | Standard Fréchet derivative on convergence domain | **Almost everywhere correct** (Lebesgue measure-zero failure set; countable union of polynomial zero sets for polynomial primitives) | Optimization fixed points, discrete float grids, and discontinuities under expectations |

**Why "almost everywhere" still fails in practice (derived):** (i) $\ell_1$ sparsity, dead ReLUs, and active constraints actively steer optimizers *onto* $x = 0$; (ii) IEEE-754 floats assign positive probability to `0.0` under zero initialization or clamping; and (iii) differentiating pointwise inside an expectation $\mathbb{E}_z[f(\theta, z)]$ with a $\theta$-dependent jump drops the boundary Dirac-delta term, biasing gradients everywhere.

#### 3.3 Perturbation Confusion: Untagged Duals vs. Escaping Higher-Order Closures

In nested forward-mode AD, untagged dual numbers conflate distinct infinitesimals $\varepsilon_1 \neq \varepsilon_2$ (**perturbation confusion**, Siskind & Pearlmutter 2005; HOSC 2008, DOI `10.1007/s10990-008-9037-1`). On $g_1(x) = x \cdot \left.\frac{d}{dy}(x + y)\right|_{y=1} = x$ (true derivative `1.0`), verified in Part (b) at $x = 3.5$:
- Outer `diff` passes $x = \mathrm{Dual}(3.5, 1.0)$; inner `diff` evaluates $\mathrm{Dual}(3.5, 1.0) + \mathrm{Dual}(1.0, 1.0) = \mathrm{Dual}(4.5, 2.0)$ and extracts **`2.0`**; outer then computes $\mathrm{Dual}(3.5, 1.0) \cdot 2.0 = \mathrm{Dual}(7.0, 2.0)$—corrupting both primal (`7.0 = 2x`) and derivative (**`2.0`**).
- Similarly, for $g_2(x) = x \cdot \left.\frac{d}{dy}(x \cdot y)\right|_{y=1} = x^2$ (true derivative $2x = 7.0$), untagged duals return $x + 1 =$ **`4.5`**.

**Manzyuk, Pearlmutter, Radul, Rush & Siskind (JFP 2019, DOI `10.1017/S095679681900008X`)** further showed that **dynamic nesting-depth tagging** (`depth += 1` / `depth -= 1`) breaks on higher-order curried functions whose closures escape `diff`:

```python
# c(z) = d/dx (x + z)|_{x=2.0} == 1.0  =>  d/dz [z * c(z)] == 1.0
c_bug = diff_dynamic_depth_bug(lambda x: (lambda y: x + y), 2.0)  # captures tag=1, resets depth=0
ho_bug = diff_dynamic_depth_bug(lambda z: z * c_bug(z), 3.0)      # recycles tag=1 -> returns 2.0!
```

Part (b) of our probe confirms `ho_bug == 2.0` while strictly **monotonic fresh gensym tags** (ordered $t_1 < t_2$, never decremented) return exact `(1.0, 7.0, 1.0)`. `jax-ml/jax` prevents this via unique `core.TraceTag()` object identity (`ad.py:229, 536-541`: `val._trace.tag is self.tag`) coupled with `core.ensure_no_leaks(lin_trace)` (`ad.py:237`) forbidding escaped tracers.

#### 3.4 IEEE-754 `0.0 * inf = NaN` Masking and Numerical AD Pitfalls

In predicated/vectorized reverse mode (`select(cond, a, b)` / `jnp.where`), both arms evaluate eagerly. For $y = \operatorname{where}(x > 0, \sqrt{x}, 0.0)$ at $x = 0.0$, the untaken `True` arm receives cotangent `0.0` while its local derivative is `0.5 / sqrt(0.0) = +inf`; IEEE-754 computes `0.0 * (+inf) = NaN`, poisoning the taken arm's `0.0` gradient (verified in Part c). Two production fixes eliminate this hazard:
1. **Double-`where` primal guard (`JAX` idiom)**: `safe_x = where(x > 0, x, 1.0); where(x > 0, sqrt(safe_x), 0.0)` keeps the local derivative finite (`0.5`), yielding `0.0 * 0.5 = 0.0`.
2. **Cotangent zero short-circuit (`Enzyme` `strongZero`)**: `AdjointGenerator.h:2799-2805, 2824-2830, 3108, 3386` wraps reverse-mode products/quotients in `select (fcmp oeq idiff, 0.0), idiff, res` (`checkedMul`), enforcing $0 \cdot x = 0$ even against `Inf`/`NaN` local derivatives (trading off genuine `NaN` propagation when `idiff == 0`).

At the algorithm level, **Hückelheim et al. (2023, `arXiv:2305.07546`)** document systemic pitfalls where exact differentiation of numerical code diverges from the mathematical derivative: unrolled iterative solvers (fixed-point truncation error vs. implicit function theorem $-(\partial_x G)^{-1}\partial_\theta G$), chaotic systems (exponential $O(e^{\lambda T})$ trajectory sensitivity blowup vs. smooth ergodic averages), and piecewise-constant discretizations/lookup tables (zero derivative a.e.).

---

### 4. FFI, Custom Derivative Contracts, Parallelism, and Verification Boundaries

Basis: source (`EnzymeAD/Enzyme`, `google-research/dex-lang`, `jax-ml/jax`, `FluxML/Zygote.jl`, `swiftlang/swift`) + normative (Moses et al. SC '21, SC '22; Paszke et al. ICFP 2021) + derived

#### 4.1 Parallelism Duality: Shared Forward Reads Become Concurrent Adjoint Writes

When $k$ parallel threads or GPU lanes read a shared weight $w_j$ during a race-free forward pass, reverse-mode fan-in converts those reads into $k$ concurrent updates to $\bar{w}_j$—a **write-write data race** unless synchronized:
- **`Enzyme` (`SC '21`, `SC '22`)**: Sets `AtomicAdd = true` inside OpenMP/GPU regions (`AdjointGenerator.h:5090, 5311`), emitting `AtomicRMWInst::FAdd` (`AtomicOrdering::Monotonic`, `L952-1056`) or warp/shared reductions, plus explicit `FMax`/`FMin` handling (`L1065-1075`). Unordered floating-point atomics introduce bitwise nondeterminism due to float non-associativity.
- **`Dex` (`ICFP 2021`)**: Types reverse fan-in as a `RunWriter` / `MExtend` effect over commutative monoid `(0, +)` (`Transpose.hs:89-112, 259-287`), proving the reversed `For Rev` body never reads partial sums and permitting lock-free privatization + reduction trees.
- **Ownership/aliasing leverage (derived)**: Static exclusive-mutability invariants (e.g., Rust `&mut` lowering to LLVM `noalias`) sharpen LLVM alias analysis, shrinking Enzyme's conservative overwrite tapes (`is_value_mustcache_from_origin`, `minCut`) and eliminating spurious atomic promotions—provided lowering preserves sound `noalias` semantics (`anneal-mid-level-ir-optimizations-and-lowering-survey`).

#### 4.2 Opaque Foreign Calls and Unchecked Custom-Rule Trust Boundaries

| System | Custom Derivative Hook (Verified Source) | Validation Status | Failure Mode on Omission / Error |
| :--- | :--- | :--- | :--- |
| **`EnzymeAD/Enzyme`** | Metadata `enzyme_augment`, `enzyme_gradient`, `enzyme_derivative`, `enzyme_splitderivative` (`Utils.h:1744-1749`); `enzyme_inactive` (`ActivityAnalysis.cpp:602, 612`) | **Unchecked trust** (`shouldDisableNoWrite`, `Utils.h:1751-1760`) | Missing body/rule $\to$ compile error (`EnzymeLogic.cpp:2551, 4402`); false `enzyme_inactive` $\to$ **silent zero** |
| **`jax-ml/jax`** | `@jax.custom_jvp`, `@jax.custom_vjp` (`custom_derivatives.py:87, 526`; `ad.py:571-600`) | **Unchecked trust** (sampled FD tests only) | Wrong `bwd` rule $\to$ **silent wrong gradient**; `custom_vjp` blocks forward `jvp` |
| **`FluxML/Zygote.jl`** | `@adjoint` / `ChainRulesCore.rrule` (`compiler/chainrules.jl`, `lib/array.jl:69-91`) | **Unchecked trust** (empirical testing) | Missing rule traces Julia internals $\to$ fails on `ccall` or array mutation |
| **`swiftlang/swift`** | `@derivative(of:)` SIL witnesses (`PullbackCloner.cpp:51`, `PassPipeline.cpp:204-206`) | Signature type-checked; derivative math **unchecked** | Missing witness on foreign C import $\to$ compile-time SIL error |

**Formal verification gap (derived):** Formal soundness proofs (Abadi & Plotkin 2020; Huot et al. 2020; Mazza & Pagani 2021; Vákár & Smeding 2022; Krawiec et al. 2022) cover idealized pure calculi over $\mathbb{R}$, whereas production AD compilers transform floating-point SSA IRs with pointer aliasing, unchecked custom FFI rules, dynamic tapes, and `NaN` masking. Closing this gap requires decomposing verified AD into three explicit obligations: (1) a **real-valued relational spec** naming the exact derivative class (Fréchet, intensional, or conservative field) and regularity preconditions for both core ops and custom FFI rules, (2) **IR translation validation** checking alias framing, shadow-pointer disjointness, and `minCut` caching, and (3) **IEEE-754 error and `NaN`-freedom bounds**.

## Boundaries

- **not examined**:
  - Source internals or benchmarks of PyTorch `torch.compile`/AOTAutograd, Tapenade, Clad, Enzyme MLIR passes beyond tree discovery of `LowerBinomialProgressPass.cpp`, and nightly Rust `std::autodiff` front-end macro desugaring.
  - GPU register-spilling, warp-shuffle, and shared-memory occupancy heuristics inside Enzyme's NVVM/AMDGPU lowering beyond SC '21 claims and `PreserveNVVM`/`AtomicRMW` source hooks.
  - Discrete stochastic gradient estimators (ADEV, StochasticAD, REINFORCE vs. reparameterization).
- **unknown**:
  - Whether automated per-function translation validation (SMT/Alive2-style) can verify Enzyme's generated LLVM IR reverse passes against primal IR across dynamic heap tapes, `minCut` cuts, and `strongZero` guards at realistic loop depths.
  - Empirical `TypeAnalysis` failure rates across large unannotated C/C++ or unsafe Rust corpora with heavy type punning (`memcpy`, unions, custom allocators).
- **known not to apply**:
  - **Clarke subdifferential membership** does not hold universally for operational AD on composite piecewise-analytic programs (counterexample `relu(x) - relu(-x)` executed in Part c).
  - **Revolve's closed-form optimum** $p(l, c) = r \cdot l - \binom{c+r}{c+1}$ does not apply under non-uniform step costs/sizes, unknown trip counts $l$, or arbitrary DAGs/CFGs (NP-complete per Naumann 2009).
  - **Dynamic nesting-depth tagging** does not apply soundly to higher-order languages with escaping closures (counterexample executed in Part b; Manzyuk et al. 2019).
  - **Almost-everywhere correctness over $\mathbb{R}$** does not guarantee valid gradients at optimization fixed points, under IEEE-754 grids hitting `0.0`, or under expectations with parameter-dependent jump discontinuities.
- **unsupported**:
  - `jax-ml/jax@bb38c58379173719d63a7e81fc09c22a37502654` rejects reverse-mode `lax.while_loop` and dynamic-bound `lax.fori_loop` (`_while_transpose_error`, `loops.py:2192-2195, 2603`).
  - `FluxML/Zygote.jl@78463a14bc67a66435fc5ac3797422eaf9f6d589` rejects in-place `AbstractArray` mutation (`setindex!`, `copyto!`, `push!`, `pop!`, `pushfirst!`, `popfirst!`; `src/lib/array.jl:71-91`).
  - `google-research/dex-lang@25e2e389b90403ae2f8d67fb6d52f47d23c439ee` rejects `MemOp` (`Transpose.hs:220`) and leaves `Select`, `CastOp`, `BitcastOp`, `UnsafeCoerce`, `SumCon`, `DepPair`, `IndexRef`, and `ProjRef` unimplemented (`Transpose.hs:202-203, 233-237, 295-297`).
  - `EnzymeAD/Enzyme@0fa6f8401af6b8211a783213643692be20508842` does not differentiate active `InlineAsm` other than `"maxpd $1, $0"` (`CallDerivatives.cpp:3515-3546`), aborts on OpenMP indirect calls (`AdjointGenerator.h:5505`), rejects `OUT_DIFF` on non-`byval` pointers (`Enzyme.cpp:934-938`), and errors on untyped `memcpy`/`memmove` (`AdjointGenerator.h:4194-4196`) or bodyless external calls without custom rules (`EnzymeLogic.cpp:2551, 4402`).

## Evidence

All primary sources, commits, and execution probes were observed on `2026-11-19`.

### Pinned Repositories

- **`EnzymeAD/Enzyme`** (`0fa6f8401af6b8211a783213643692be20508842`): `enzyme/Enzyme/Enzyme.cpp` (`L109-111, 397-400, 568-579, 934-938, 3243-3294`), `Clang/EnzymePassLoader.cpp` (`L47-78`), `ActivityAnalysis.h` (`L67-138, 256-263`), `ActivityAnalysis.cpp` (`L602-609, 960-1200, 2798-2807`), `TypeAnalysis/TypeAnalysis.h` (`L133-218`), `DifferentialUseAnalysis.h` (`L548-562`), `DifferentialUseAnalysis.cpp` (`L874-995`), `CacheUtility.h` (`L82-145, 270-297`), `EnzymeLogic.cpp` (`L237-304, 2118-2552, 3566, 3844-4402, 4830-4846`), `AdjointGenerator.h` (`L620-628, 952-1075, 1394-1438, 2347, 2523, 2799-2830, 3108, 3386, 4020-4201, 5087-5091, 5310-5318, 5504-5505, 5886-5898, 6284-6297`), `CallDerivatives.cpp` (`L3515-3546`), `Utils.h` (`L1742-1765`), `MLIR/Passes/LowerBinomialProgressPass.cpp`.
- **`google-research/dex-lang`** (`25e2e389b90403ae2f8d67fb6d52f47d23c439ee`): `src/lib/Linearize.hs` (`L216-267, 279-280, 604-621`), `src/lib/Transpose.hs` (`L27-55, 89-148, 155-288, 290-306`).
- **`jax-ml/jax`** (`bb38c58379173719d63a7e81fc09c22a37502654`): `jax/_src/interpreters/ad.py` (`L122-180, 227-289, 300-542, 571-600`), `jax/_src/lax/control_flow/loops.py` (`L1709-1711, 1998-2051, 2192-2195, 2601-2603`), `jax/_src/ad_checkpoint.py` (`L255-399, 892-918`), `jax/_src/custom_derivatives.py` (`L87, 526`).
- **`FluxML/Zygote.jl`** (`78463a14bc67a66435fc5ac3797422eaf9f6d589`): `src/compiler/reverse.jl` (`L239-253, 306-317, 335-350, 378-393`), `src/lib/array.jl` (`L69-91`), `src/lib/buffer.jl` (`L1-55`).
- **`swiftlang/swift`** (`49fb0090b22cd6dcde645455e7cbf089380f88e4`): `lib/SILOptimizer/PassManager/PassPipeline.cpp` (`L204-206`), `lib/SILOptimizer/Differentiation/LinearMapInfo.cpp` (`L58-65, 341-415`), `lib/SILOptimizer/Differentiation/PullbackCloner.cpp` (`L61-120`).

### Verified Primary Literature

- Moses & Churavy, *Instead of Rewriting Foreign Code for Machine Learning, Automatically Synthesize Fast Gradients*, NeurIPS 2020, Vol. 33, DOI `10.5555/3495724.3496770`, `arXiv:2010.01709`.
- Moses et al., *Reverse-Mode Automatic Differentiation and Optimization of GPU Kernels via Enzyme*, SC '21, DOI `10.1145/3458817.3476165`; *Scalable Automatic Differentiation of Multiple Parallel Paradigms through Compiler Augmentation*, SC '22, DOI `10.1109/SC41404.2022.00065`.
- Paszke et al., *Getting to the Point: Index Sets and Parallelism-Preserving Autodiff for Pointful Array Programming*, PACMPL 5 (ICFP 2021), DOI `10.1145/3473593`, `arXiv:2104.05372`.
- Radul et al., *You Only Linearize Once: Tangents Transpose to Gradients*, PACMPL 7 (POPL 2023), DOI `10.1145/3571236`, `arXiv:2204.10923`.
- Griewank & Walther, *Algorithm 799: Revolve: An Implementation of Checkpointing for the Reverse or Adjoint Mode of Computational Differentiation*, ACM TOMS 26(1), 2000, DOI `10.1145/347837.347846`.
- Naumann, *Optimal Jacobian accumulation is NP-complete*, Math. Program. 112(2), 2008, DOI `10.1007/s10107-006-0042-z`; *Call tree reversal is NP-complete*, LNCSE 64, 2008, DOI `10.1007/978-3-540-68936-2_2`; *DAG reversal is NP-complete*, J. Discrete Algorithms 7(4), 2009, DOI `10.1016/j.jda.2008.12.003`.
- Siskind & Pearlmutter, *Nesting Forward-Mode AD in a Functional Framework*, HOSC 21(4), 2008, DOI `10.1007/s10990-008-9037-1`.
- Manzyuk, Pearlmutter, Radul, Rush & Siskind, *Perturbation Confusion in Forward Automatic Differentiation of Higher-Order Functions*, JFP 29:e12, 2019, DOI `10.1017/S095679681900008X`.
- Lee, Yu, Rival & Yang, *On Correctness of Automatic Differentiation for Non-Differentiable Functions*, NeurIPS 2020, Vol. 33.
- Mazza & Pagani, *Automatic Differentiation in PCF*, PACMPL 5 (POPL 2021), Art. 28, DOI `10.1145/3434309`.
- Huot, Staton & Vákár, *Correctness of Automatic Differentiation via Diffeologies and Categorical Gluing*, FoSSaCS 2020, LNCS 12077, DOI `10.1007/978-3-030-45231-5_17`, `arXiv:2001.02209`.
- Bolte & Pauwels, *Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning*, Math. Program. 188, 2021, DOI `10.1007/s10107-020-01501-5`.
- Hückelheim et al., *Understanding Automatic Differentiation Pitfalls*, `arXiv:2305.07546`, 2023, DOI `10.48550/arXiv.2305.07546`.
- Cross-referenced foundations: Abadi & Plotkin (POPL 2020, DOI `10.1145/3371106`), Vákár (ESOP 2021, DOI `10.1007/978-3-030-72019-3_22`), Smeding & Vákár (TOPLAS 2022, DOI `10.1145/3527634`), Krawiec et al. (POPL 2022, DOI `10.1145/3498710`).

### Execution Probe Receipt (`2026-11-19`)

Command (`python3` 3.13 stdlib only):

```console
python3 -B support/verify_autodiff_transposition_and_hazards.py
```

Observed output (exit code `0`):

```text
[PASS] (a) Dex 3-pass AD: primal=1.603342, |JVP-exact|=0.00e+00, |<Jv,u>-<v,J^Tu>|=1.78e-15, max_array_FD_err=9.48e-10
[PASS] (b) Perturbation confusion: untagged d/dx[x*d/dy(x+y)]=2.0 (primal=7.0=2x, true=1.0), untagged d/dx[x*d/dy(x*y)]=4.5 (true=7.0); dynamic-depth escaping-closure bug=2.0 (true=1.0); monotonic-tag fixed=(1.0, 7.0, 1.0)
[PASS] (c) Branch & NaN hazards: id_branch'(0)=0.0 (true=1.0), [relu(x)-relu(-x)]'(0)={gt:0.0, ge:2.0} outside Clarke={1}; predicated where(x>0,sqrt(x),0) naive=nan, double_where=0.0, strongZero=0.0
[PASS] (d) Revolve checkpointing (L=100, DP==closed-form on 120x8 grid, |rev-tape|<1e-13, |tape-FD|=1.93e-12): c=2:adv=845(peak=2), c=3:adv=490(peak=3), c=4:adv=374(peak=4), c=5:adv=316(peak=5), c=10:adv=222(peak=10)
ALL AD VERIFICATION PROBES PASSED
```

## Revalidation

1. **Mathematical & algorithmic probe (seconds)**: Run `python3 -B reports/differentiable-programming-autodiff-semantics-and-compiler-challenges/support/verify_autodiff_transposition_and_hazards.py` and verify exit code `0`. Passing confirms the 3-pass adjoint identity, perturbation-confusion reproductions/fixes, Clarke and `0.0 * inf = NaN` hazards, and Revolve 120x8 DP vs. closed-form and 100-step live optimality.
2. **Enzyme LLVM pass placement and walls**: Diff `Enzyme.cpp` (`registerOptimizerEarlyEPCallback`), `CallDerivatives.cpp` (`InlineAsm`), `AdjointGenerator.h` (`visitMemTransferCommon`, `openmp indirect unhandled`, `strongZero`), and `DifferentialUseAnalysis.cpp` (`minCut`) against `0fa6f8401af6b8211a783213643692be20508842`.
3. **JAX `while_loop` and tracer isolation**: Check `ad.primitive_transposes[while_p]` in `jax/_src/lax/control_flow/loops.py` and `JVPTrace.to_primal_tangent_pair` / `core.ensure_no_leaks` in `jax/_src/interpreters/ad.py` against `bb38c58379173719d63a7e81fc09c22a37502654`.
4. **Dex, Zygote, and Swift boundaries**: Diff `google-research/dex-lang:src/lib/Transpose.hs` (`notImplemented` arms), `FluxML/Zygote.jl:src/lib/array.jl` (`@adjoint! setindex!`), and `swiftlang/swift:lib/SILOptimizer/PassManager/PassPipeline.cpp` (`addDifferentiation`) against their pinned commits.
5. **Scope of revalidation**: Re-running the standalone Python probe re-checks mathematical models only; verifying gradient preservation of a production compiler (e.g., Enzyme on a newer LLVM version) requires compiling and differential-testing that compiler directly.
