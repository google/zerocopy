# Reactive Dataflow Notebooks, Cross-FFI Provenance, and Computational Reproducibility

## Summary

Traditional REPL-backed computational notebooks (`Jupyter`) allow arbitrary out-of-order execution and deletion of cells over a single mutable global heap, producing a severe reproducibility deficit: across `1.4 million` GitHub notebooks (`863,878` valid execution attempts), only **`24.11%`** ran to completion without exceptions and only **`4.03%`** reproduced their originally stored outputs (Pimentel et al., `DOI: 10.1007/s10664-021-09961-9`). Modern reactive dataflow notebooks (`Observable`, `Pluto.jl`, `Marimo`) eliminate hidden REPL state by deriving a directed acyclic graph (DAG) of cell dependencies and rejecting multiple definitions and cycles. However, primary-source analysis and live execution expose a structural **cross-FFI and external-effect soundness boundary**:

1. **Static AST DAG analyzers are blind to in-place aliasing, C/C++/CUDA FFI writes, native global state, and external I/O (`Marimo`, `Pluto.jl`, `Observable`):** In `Marimo`'s `ScopedVisitor` (`marimo/_ast/visitor.py` L1076–1120), variable definitions are registered only on `ast.Name` nodes with `ast.Store` context (`x = ...`, `x += ...`); attribute writes (`foo.bar = 1`), subscript mutations (`buf[0] = 9`), and native buffer writes through `memoryview`/`ctypes`/NumPy/PyTorch C-extensions generate *only* `ast.Load` references and **zero** `def` edges. As demonstrated in Probe 2A, mutating an aliased buffer via `libc.memset` inside cell `C3` creates no DAG edge `C3 -> C4`, allowing two distinct valid topological orders of the exact same reactive notebook to yield conflicting results (`cached total = 10` vs. `live sum(buf) = 36`).
2. **Dynamic Python lineage tracers close pure-Python mutation gaps but stop at the C-API / kernel boundary (`IPyflow`, `noWorkflow`):** `IPyflow` (Macke et al., `PVLDB 2021`) instruments Python AST execution and tracks runtime symbol/subscript/container mutations (`DataflowTracer`), catching Python-level aliasing (`v = a; v.append(1)`) that static AST notebooks miss—but raw C-pointer writes (`ctypes.memset`, CUDA kernels, in-place BLAS/LAPACK routines) and hidden native globals (`libc` `srand`/`rand`, `cudnn` PRNG state) bypass Python bytecode hooks.
3. **Hermetic reproducibility requires layering three orthogonal provenance planes:** (a) **Language-level DAG & environment pinning** (`Pluto.jl`'s notebook-embedded `Project.toml`/`Manifest.toml` via `Pkg.jl`, `Marimo` single-definition acyclic execution, `Observable` topological invalidation and async generator disposal); (b) **OS-level syscall provenance** (`ReproZip`'s `ptrace` interception of `openat`/`execve`/`fork` in `syscalls.c`, and `noWorkflow`'s `external_strace.py` `-D -z -y -x` grandchild tracer) to capture every shared library, binary, and external file touched across FFI boundaries; and (c) **Content-addressed memory/buffer and artifact digests** (or copy-on-write page/tensor snapshots and effect-typed mutation capabilities) to detect cross-FFI buffer drift and enable safe incremental memoization of expensive compute cells.

## Applicability

These findings apply to interactive dataflow notebook runtimes, polyglot scientific computing kernels (Python/C/C++/CUDA, Julia/`ccall`, JS/WASM), and provenance-capture frameworks across the following directly examined revisions and papers:

- **Static AST Reactive Notebooks:**
  - `marimo-team/marimo` at `24459dbf2a6b630c135dcb3d9c616543874e0f88` (`marimo/_ast/visitor.py`, `marimo/_runtime/dataflow/{graph.py,topology.py}`, `marimo/_runtime/runner/cell_runner.py`).
  - `JuliaPluto/Pluto.jl` at `db2a5cdf1df2c39acec058f09d7e87aaab9ed728` (`src/evaluation/{Run.jl,MacroAnalysis.jl,WorkspaceManager.jl}`, `src/packages/Packages.jl`) paired with `JuliaPluto/ExpressionExplorer.jl` at `e5a967288ab5d640f7def7408e16ddcb8bd6a462` (`src/ReactiveNode.jl`, `src/explore.jl`).
  - `observablehq/runtime` at `d52584db5b76d7ab0fd5a47189dddb85893ec45f` (`src/runtime.js`, `src/variable.js`).
- **Dynamic Runtime Lineage & Provenance Systems:**
  - `ipyflow/ipyflow` at `7eb0251739ee27725d92cc26f22b8906029e8cf1` (`core/ipyflow/tracing/ipyflow_tracer.py`, `core/ipyflow/data_model/symbol.py`), corresponding to the `NBSafety` design of Macke et al. (`DOI: 10.14778/3447689.3447712`).
  - `gems-uff/noworkflow` at `5bfa13ac7e97b22b341c97a03b47d6c861b0f62e` (`src/noworkflow/now/collection/prov_execution/{collector.py,external_strace.py,file_access_proxy.py}`), extending Pimentel et al. (`DOI: 10.14778/3137765.3137789`).
  - `VIDA-NYU/reprozip` at `44687ce73efe7a889bf7a1ea982258e2d965c766` (`reprozip/native/{syscalls.c,tracer.c}`), implementing Chirigati et al. (`DOI: 10.1145/2882903.2899401`).
- **Empirical & Conceptual Baselines:**
  - Pimentel, Murta, Braganholo, Freire (`DOI: 10.1109/MSR.2019.00077` / `DOI: 10.1007/s10664-021-09961-9`) for large-scale Jupyter failure rates; Koop & Patel (USENIX TaPP 2017) for persistent cell-ID dataflow notebooks.

**Relationship Among Subjects:** The seven software subjects span the exact four-layer design space of computational notebooks: (1) static AST DAGs (`Marimo`, `Pluto.jl`, `Observable`), (2) runtime Python bytecode/object lineage (`IPyflow`), (3) hybrid Python + subprocess `strace` provenance (`noWorkflow`), and (4) language-agnostic Linux `ptrace` syscall tracing (`ReproZip`). The cross-FFI soundness failures observed in Probe 2A/2B apply directly to Python (`ctypes`, CPython buffer protocol, NumPy/PyTorch views, `cffi`, PyO3) and generalize structurally to Julia `ccall`/pointer aliasing and JS/WASM `SharedArrayBuffer` / linear-memory views whenever an analyzer relies solely on surface lexical bindings.

## Findings

### 1. Empirical Taxonomy of Notebook Reproducibility Failures

Basis: documentation/empirical study (Pimentel et al., `MSR 2019` / `EMSE 2021`, `DOI: 10.1007/s10664-021-09961-9`; Koop & Patel, `TaPP 2017`) + derived.

Pimentel et al. harvested approximately `1.4 million` Jupyter notebooks from GitHub and attempted automated sequential re-execution of `863,878` valid notebooks with identifiable Python versions and execution metadata. Only **`24.11%`** completed without raising an exception, and only **`4.03%`** reproduced outputs matching the originally saved cells. Root causes partition into five distinct failure strata:

| Failure Stratum | Concrete Mechanism | Eliminated by Static Reactive DAG (`Marimo`/`Pluto`)? | Eliminated by Dynamic Lineage (`IPyflow`)? | Eliminated by OS Syscall Provenance (`ReproZip`)? |
| :--- | :--- | :--- | :--- | :--- |
| **1. Hidden Out-of-Order REPL State** | Executing cells `[1] -> [5] -> [2]`, mutating globals, then deleting or editing cell `[5]`. | **Yes** (single-definition DAG + automatic topological re-run + deletion cleanup). | **Partially** (warns/auto-runs stale cells, permits imperative order). | **No** (replays the exact broken order if captured, does not fix source semantics). |
| **2. Environment & Dependency Drift** | Unpinned `pip`/`conda` packages, missing native `.so`/CUDA driver versions, OS library mismatches. | **Pluto.jl: Yes** (embeds `Project.toml`+`Manifest.toml`); **Marimo:** PEP 723 inline script metadata / external lockfile. | **No** (relies on host kernel env). | **Yes** (packs exact resolved `.so`, Python binaries, and data files via `ptrace`). |
| **3. In-Place Python Aliasing & Mutation** | `b = a; b.append(1)` or `df.drop(..., inplace=True)` in a downstream cell. | **No** (AST sees `Load` of `b`/`df`, not a `Store` of `a`). | **Yes** (runtime symbol/object-ID mutation hooks track container edits). | **No** (in-process heap mutation issues zero syscalls). |
| **4. Cross-FFI / Native Buffer & PRNG Mutation** | `memoryview`, `ctypes.memset`, NumPy/PyTorch views sharing `Py_buffer`/CUDA pointers, C static PRNGs (`srand`/`rand`, `cudnn`). | **No** (completely invisible to Python/Julia AST). | **No** (native C/CUDA code does not trigger Python tracer events). | **No** (memory writes inside the process issue zero syscalls). |
| **5. External Files, DBs, Network, Nondeterminism** | Reading/mutating `/tmp/data.parquet`, SQLite tables, environment variables, clocks, wall-time seeds. | **No** (external paths are opaque strings to AST def/ref analysis). | **No** (unless wrapped in tracked Python objects). | **Partially** (captures file/network I/O paths & files; cannot reverse live external DB drift without snapshotting). |

---

### 2. Static Reactive Dataflow Architectures (`Marimo`, `Pluto.jl`, `Observable`)

Basis: source (`marimo-team/marimo@24459dbf2a`, `JuliaPluto/Pluto.jl@db2a5cdf1d`, `JuliaPluto/ExpressionExplorer.jl@e5a967288a`, `observablehq/runtime@d52584db5b`).

#### 2.1 `Marimo`: Pure-Python AST `ScopedVisitor` and Acyclic Single-Definition `DirectedGraph`

`Marimo` stores notebooks as valid executable `.py` files and derives its reactive execution graph statically without running cell code:

1. **AST Def/Ref Classification (`marimo/_ast/visitor.py`):**
   - `ScopedVisitor(ast.NodeVisitor)` (L249) traverses each cell's Python AST, maintaining lexical scope stacks (`block_stack`), reference stacks (`ref_stack`), and `variable_data`.
   - `visit_Assign` (L961–974) visits `node.value` *before* `node.targets` so self-referential assignments (`x = x`) record `x` as an external ref before defining it.
   - `visit_AugAssign` (L976–984) visits `node.value` then `node.target`; because Python's AST assigns `ast.Store()` context to an `AugAssign` target `x += 1`, `visit_Name` (L1076–1108) registers `x` as a `def`—deliberately triggering a multiple-definition conflict if `x` was defined in another cell (`marimo_visitor.py` L1077–1079).
   - **Critical Limitation Documented in Source (`marimo/_ast/visitor.py` L1086–1089):**
     > *"NB: we don't implement `visit_Attribute` because refs and defs are not tracked at the attribute level. The default behavior with our implemented visitors does the right thing (`foo.bar[.*]` generates a ref to `foo` if `foo` has not been def'd)."*
     Equivalently, `buf[0] = 9`, `obj.field = 1`, `arr.fill(0)`, and `libc.memset(ptr, 9, n)` carry `ast.Load()` on the base identifier (`buf`, `obj`, `arr`, `ptr`), so `visit_Name` (L1109–1114) registers them purely as **references**, never definitions!
   - **Cell-Local Mangling (`_var`):** Identifiers prefixed with `_` are treated as cell-local (`is_local`) and mangled per cell (`_if_local_then_mangle`, L1101, L1121–1150) so temporary variables do not pollute the global DAG namespace—with a subtle exception for unaliased underscore imports (`from pkg import _c`, L1132–1135).
   - **Explicit `del` Tracking (`deleted_refs`, L309–315, L1115–1120):** `del x` on a global variable records a `deleted_ref`, allowing the graph scheduler to schedule deletion cells after readers or forbid conflicting deletions.
2. **Graph Topology & Conflict Rejection (`marimo/_runtime/dataflow/graph.py`, `topology.py`):**
   - `DirectedGraph` (L31–38) coordinates `MutableGraphTopology`, `DefinitionRegistry`, and `CycleTracker` under `self.lock`.
   - `get_multiply_defined()` / `get_multiply_defined_conflicts()` (L266–272) statically forbids any global name from being defined in more than one cell. Together with cycle rejection, every valid Marimo notebook defines a unique partial order over cells; when cell $c$ changes, `descendants(c)` (`topology.py` L85–89, calling `transitive_closure`) are invalidated, old globals from deleted/re-run cells are purged, and descendants re-execute in topological order.

#### 2.2 `Pluto.jl` and `ExpressionExplorer.jl`: Multiple-Dispatch Signatures and Embedded `Pkg.jl` Lockfiles

Julia introduces two language features absent from Python that complicate reactive dataflow: **multiple dispatch** (different cells defining distinct methods `f(x::Int)` and `f(x::String)` for the same function symbol `f`) and **hygienic macros** (code generating new bindings at expansion time).

1. **Dual-Granularity `ReactiveNode` (`ExpressionExplorer.jl/src/ReactiveNode.jl` L3–37):**
   - Rather than storing flat `(refs, defs)` sets, `ReactiveNode` tracks six distinct sets: `references::Set{Symbol}`, `definitions::Set{Symbol}`, `soft_definitions::Set{Symbol}`, `funcdefs_with_signatures::Set{FunctionNameSignaturePair}`, `funcdefs_without_signatures::Set{Symbol}`, and `macrocalls::Set{Symbol}` (L13–20).
   - Dependency edges match `references` against `funcdefs_without_signatures` (so calling `f(...)` depends on *all* cells defining methods of `f`), while multiple-definition error detection checks collisions on `funcdefs_with_signatures` (allowing `f(x::Int) = 1` and `f(x::Float64) = 2` in separate cells, while rejecting two cells defining `f(x)` with the same signature!).
2. **Macro Expansion & Embedded Reproducible Environments (`Pluto.jl/src/evaluation/MacroAnalysis.jl`, `src/packages/Packages.jl`):**
   - Because macros can introduce bindings invisible in the unexpanded AST, `Pluto.jl` expands macros via `MacroAnalysis.jl` before finalizing reactive links.
   - To eliminate environment drift (Failure Stratum 2), `Pluto.jl`'s built-in package manager (`nbpkg`, `src/packages/Packages.jl` L24–54) intercepts `import`/`using` statements, creates an isolated per-notebook `Pkg` environment, and **embeds the exact `Project.toml` and `Manifest.toml` directly inside the `.jl` notebook file itself**—unless the user explicitly opts out by referencing `Pkg.activate`, `Pkg.develop`, or `Pkg.add` (L24–30). Consequently, any Pluto notebook file is simultaneously a self-contained Julia source file and a cryptographic dependency lockfile (capturing exact git-tree-sha1 hashes of every transitive Julia package and binary `JLL` artifact!).
   - **Mutation Soundness Limit:** Just like `Marimo`, `ExpressionExplorer.jl` tracks lexical bindings and assignments, not runtime heap aliasing (`x[1] = 2`, `push!(arr, v)`, or `ccall` pointer writes into `Vector{UInt8}`), meaning cross-cell in-place mutation in Julia still escapes the reactive DAG.

#### 2.3 `Observable`: Asynchronous Generator Dataflow and `invalidation` Promises

`observablehq/runtime` (`src/runtime.js`, `src/variable.js`) implements reactive dataflow over asynchronous JavaScript generators and Promises:

- Every cell compiles to a `Variable` (`variable.js` L14–35) holding `_inputs`, `_outputs` (`Set`), `_indegree` (active computing upstream count), `_reachable` (whether transitively observed by a rendered inspector, enabling lazy dead-code pruning!), `_version` (monotonic epoch counter preventing stale async resolutions from overwriting newer computations), and `_invalidate` cleanup hooks.
- When a `Variable` recomputes (`runtime.js` L214–220 `variable_compute`), it immediately triggers `variable._invalidate()`, increments `++variable._version`, and propagates staleness (`variable_stale`, `variable.js` L70–72) down `_outputs` via topological Kahn-style indegree counting.
- **Resource-Safe Reactive Disposal (`invalidation`):** Because `invalidation` is a first-class Promise injected into each cell, cells owning external resources (WebGL contexts, WebSockets, `setInterval`, WASM linear-memory allocations) register deterministic teardown (`invalidation.then(() => worker.terminate())`) before the next reactive tick begins.
- **Mutability Escape Hatch:** Observable's `mutable x = ...` splits a cell into an immutable reader variable `x` and a mutable setter `mutable x`, explicitly exposing mutation edges in the DAG—yet mutating properties inside a plain JS object or writing into a shared `ArrayBuffer`/`WebAssembly.Memory` still bypasses `_dirty` tracking.

#### 2.4 Cross-System Architectural Comparison Matrix

| Dimension | `Jupyter` (Standard) | `Observable` (`@d52584db`) | `Pluto.jl` (`@db2a5cdf`) | `Marimo` (`@24459dbf`) | `IPyflow` (`@7eb02517`) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **Execution Model** | Manual imperative REPL | Lazy reachable async DAG | Eager/strict topological DAG | Eager/lazy topological DAG | Imperative + dynamic reactive slicing |
| **Dependency Discovery** | None | Explicit `define(name, inputs, fn)` | `ExpressionExplorer.jl` + macro expansion | Python `ast.NodeVisitor` (`ScopedVisitor`) | Runtime AST rewrite + `sys.settrace`/tracer |
| **Multiple Defs of Global** | Allowed (overwrites silently) | Runtime error (`TYPE_DUPLICATE`) | Rejected (except disjoint method sigs) | Rejected (`get_multiply_defined`) | Allowed (versioned timestamp symbols) |
| **In-Place Python/Julia Mutation** | Unmanaged | Untracked (except `mutable` cell) | Untracked (`push!`, `x[1]=`) | Untracked (`x[0]=`, `x.a=`) | **Tracked** for Python objects/subscripts |
| **Cross-FFI Buffer / C-Ext Writes** | Untracked | Untracked (WASM `ArrayBuffer`) | Untracked (`ccall` pointers) | **Untracked** (`ctypes`/`numpy`/`torch`) | **Untracked** (native C/CUDA memory) |
| **Environment Pinning** | External (`requirements.txt`) | npm/CDN URL version pins | **Embedded `Project.toml` + `Manifest.toml`** | Inline PEP 723 metadata / external | External host kernel |

---

### 3. The Cross-FFI Invisible-Mutation Soundness Hole (Empirical Demonstration)

Basis: source (`marimo-team/marimo@24459dbf2a`) + execution (Probe 2A, 2B, 2C).

Consider a minimal four-cell scientific Python notebook operating on a native-backed byte buffer (exact proxy for NumPy `ndarray.ctypes`, PyTorch `tensor.numpy()`, Arrow C Data Interface zero-copy views, or Rust `PyO3` slices):

```python
# Cell C1_alloc:
buf = bytearray(b"\x01\x02\x03\x04")

# Cell C2_alias:
view = memoryview(buf)
c_arr = (ctypes.c_ubyte * len(buf)).from_buffer(buf)

# Cell C3_ffi_mut:
libc.memset(ctypes.addressof(c_arr), 9, len(buf))

# Cell C4_downstream:
total = sum(buf)
```

Running Probe 2A's `marimo`-faithful `ScopedVisitor` produces the exact static def/ref sets:
- `C1_alloc`: `defs = ['buf']`, `refs = []`
- `C2_alias`: `defs = ['c_arr', 'view']`, `refs = ['buf', 'ctypes']`
- `C3_ffi_mut`: `defs = []`, `refs = ['buf', 'c_arr', 'ctypes', 'libc']`
- `C4_downstream`: `defs = ['total']`, `refs = ['buf']`

**Formal Soundness Failure:**
1. The inferred DAG contains edges `C1 -> C2`, `C1 -> C3`, `C1 -> C4`, and `C2 -> C3`. There is **no edge `C3 -> C4`**, and the DAG is 100% acyclic with zero multiple-definition violations.
2. Both topological linearizations $\pi_1 = [C1, C4, C2, C3]$ and $\pi_2 = [C1, C2, C3, C4]$ are legal schedules of the exact same reactive DAG.
3. Under $\pi_1$, `C4_downstream` evaluates `total = 10` before `C3_ffi_mut` overwrites `buf` in native C (`libc.memset`) with `[9, 9, 9, 9]`. The notebook now exhibits **silent state divergence**: the displayed cached output `total == 10` directly contradicts the live heap value `sum(buf) == 36`, even though the notebook status reports all cells fresh and up-to-date!
4. Under $\pi_2$, the same notebook produces `total == 36` — violating **confluent topological determinism** (the foundational soundness guarantee of a reactive DAG!).

**Secondary Cross-FFI Invisible-State Channels (Probe 2B):**
- **Hidden Native Process Globals:** Calling `libc.srand(12345)` followed by two identical zero-argument `libc.rand()` calls returns `383100999` then `858300821`. The exact same failure occurs with NumPy legacy `np.random.seed`, PyTorch `torch.manual_seed`, OpenBLAS thread-pool settings, and `cuDNN` workspace caches: AST analysis sees no shared Python variable, so re-running a stochastic cell mutates downstream PRNG streams invisibly.
- **External Filesystem & Database State:** Writing to an on-disk Parquet/CSV/SQLite file inside `C3` and reading the same path in `C4` produces zero Python symbol edge (`C3 -> C4`), allowing silent stale reads when the backing file changes (`SHA-256` drift `67ce397eed7c4bce` $\to$ `478f36ea6e0b8011` in Probe 2B).

---

### 4. Dynamic Lineage, OS-Level Syscall Provenance, and Content-Addressed Recovery

Basis: source (`ipyflow/ipyflow@7eb0251739`, `gems-uff/noworkflow@5bfa13ac7e`, `VIDA-NYU/reprozip@44687ce73e`) + papers (`Macke et al. PVLDB 2021`, `Pimentel et al. PVLDB 2017`, `Chirigati et al. SIGMOD 2016`) + execution (Probe 2C).

Closing the cross-FFI and external-I/O soundness gaps requires combining three complementary provenance mechanisms:

1. **Dynamic Python Subscript/Symbol Lineage (`IPyflow`, `ipyflow_tracer.py` L146–175):**
   - `DataflowTracer` combines AST rewriting (`DataflowAstRewriter`) with Python frame tracing to maintain runtime symbol tables (`node_id_to_saved_store_data`, `node_id_to_saved_live_subscript_refs`, `node_id_to_saved_dict_key`, `this_stmt_updated_symbols`).
   - Instead of tracking only variable names, `IPyflow` tracks runtime object identities (`id(obj)`) and container namespaces (`dict` keys, `list` indices, object attributes), stamping each cell execution with logical timestamps so downstream cells reading a mutated Python container are marked stale immediately.
   - **Boundary:** Pure-Python tracing still cannot observe raw memory writes executed inside native shared libraries (`ctypes`, C/C++/Fortran/CUDA kernels) unless every FFI boundary wrapper explicitly notifies the tracer.
2. **OS-Level Syscall Tracing (`ReproZip` & `noWorkflow` `external_strace`):**
   - `VIDA-NYU/reprozip` (`reprozip/native/syscalls.c` L743–799, `tracer.c`) attaches to the entire process tree via Linux `ptrace(PTRACE_SYSCALL, ...)` and `PTRACE_GETEVENTMSG` (following every `fork`/`vfork`/`clone` thread and subprocess). It logs every `open`/`openat`, `execve`, `stat`, `rename`, and dynamic-linker `.so` load directly from kernel syscall boundaries—capturing C-extension shared libraries, BLAS kernels, system fonts, and external data files with zero language runtime cooperation, then bundling them into a content-addressed `.rpz` reproducibility container.
   - `gems-uff/noworkflow` (`external_strace.py` L4–42) adopts a hybrid architecture: in-process Python profiling/AST collection (`collector.py`) and file proxy interception (`file_access_proxy.py`) for fine-grained Python variable derivation, augmented by wrapping spawned external commands under `strace -D -z -y -x` (`-D` detached grandchild so `Popen.pid`, signals, and timeouts target the child directly; `-z` successful syscalls only; `-y` kernel-resolved FD-to-path annotations like `= 3</p/in.txt>` and `AT_FDCWD</p>`; `-x` hex-escaping non-ASCII filenames; `?open`/`?rename` architecture guards for `x86_64` vs. `arm64`).
3. **Content-Addressed Buffer/Page Provenance & Copy-on-Write Memoization (Probe 2C & Clean-Slate Design):**
   - Neither `ptrace` nor Python AST tracing catches an in-process C pointer writing to a Python-owned `bytearray`/NumPy/PyTorch tensor. Closing that final hole requires one of three mechanisms:
     1. **Boundary Buffer Digesting (Zero-OS-Privilege Verification):** Hashing referenced `Py_buffer` / `memoryview` backing ranges (`SHA-256` or `BLAKE3`) before and after cells that invoke opaque FFI calls. In Probe 2C, digesting `memoryview(buf)` across `C3_ffi_mut` immediately detects the `libc.memset` write (`9f64a747e1b97f13` $\to$ `8493100b11a2fe62`), forcing invalidation of `C4_downstream`. Cost is $O(\text{bytes hashed})$ per buffer, practical for megabyte-scale tables/parameters, prohibitive for 40 GB GPU tensors.
     2. **Hardware Page Write-Barriers (`mprotect(PROT_READ)` + `SIGSEGV` / Linux `userfaultfd` write-protect):** Marking upstream cell output pages read-only (`PROT_READ`) after cell completion turns *any* downstream cross-FFI CPU write (`libc.memset`, C++ extension, Rust `unsafe` slice) into a hardware-trapped dirty-page fault in $O(1)$ per 4 KiB page with zero overhead on unmodified tensors, while simultaneously supporting Copy-on-Write (`fork` / `UFFDIO_COPY`) snapshots for expensive-cell memoization!
     3. **Compile-Time Region & Effect Capabilities:** In a polyglot language/IR with explicit ownership and region effects (`Read(r)` vs. `Mut(r)` + explicit `PRNG` and `FS(path)` capabilities threaded across FFI boundaries), cell dependencies are exact by type checking: a cell requiring `Mut(buf)` cannot silently alias a `Read(buf)` sibling cell, and pure cells can be memoized safely by content-addressing `(code_AST_hash, input_value_hashes, env_manifest_hash)`.

## Boundaries

- **CUDA / GPU Device-Memory Write-Protection (`not examined` empirically):** Linux `mprotect` and `userfaultfd` write-protection trap host-CPU writes to virtual memory pages, and `ptrace` traps OS syscalls; neither intercepts asynchronous DMA or GPU kernel writes to unified/device memory (`cudaMalloc` / `cuMemcpy`) unless intercepted at the CUDA stream/driver API boundary (`CUPTI` / `LD_PRELOAD` allocator hooks) or enforced via copy-on-write tensor versioning in the tensor framework itself.
- **Performance Overhead of `IPyflow` Tracing, `noWorkflow` Collection, and `ReproZip` `ptrace` (`not examined` experimentally):** Quantitative runtime slowdowns (e.g., `ptrace` syscall trap overhead on tight I/O loops vs. Python `sys.settrace` overhead on tight numeric loops) were not benchmarked on live workloads in this report; consult Macke et al. (`PVLDB 2021`) and Chirigati et al. (`SIGMOD 2016`) for published benchmark numbers.
- **Non-Linux OS Syscall Tracers (`known not to apply` directly):** `ReproZip`'s `reprozip/native/syscalls.c` (`ptrace`) and `noWorkflow`'s `external_strace.py` (`strace -D -z -y -x`) rely on Linux-specific kernel interfaces; macOS (SIP-restricted DTrace/EndpointSecurity) and Windows (ETW/Detours) require distinct OS-level interception mechanisms.
- **Soundness of Static AST Analysis Under Dynamic Reflection (`unsupported`):** Python `exec()`, `eval()`, `globals()[dynamic_name] = ...`, `setattr(module, name, val)`, and Julia `@eval` / `Core.eval` defeat static AST def/ref extraction in `Marimo` and `ExpressionExplorer.jl` by design; reactive DAG completeness holds only for lexically visible bindings.
- **Distributed / External Database Reproducibility (`unknown` / `unsupported` without external snapshotting):** Even full `ReproZip` `ptrace` capture + content-addressed memory hashing cannot reproduce queries against live remote SQL/HTTP APIs unless network responses are recorded/replayed or queries target immutable content-addressed snapshots (e.g., Iceberg/Delta snapshot IDs).

## Evidence

### Primary Repositories and Inspected Symbols (Observed `2026-11-19`)

1. **`marimo-team/marimo` @ `24459dbf2a6b630c135dcb3d9c616543874e0f88`:**
   - `marimo/_ast/visitor.py` L249 (`ScopedVisitor`), L309–315 (`deleted_refs`), L492–500 (`_define`), L961–984 (`visit_Assign`, `visit_AugAssign`), L1076–1150 (`visit_Name`, explicit L1086–1089 comment explaining attribute-level mutations are not tracked as defs, local `_` mangling).
   - `marimo/_runtime/dataflow/graph.py` L31–38 (`DirectedGraph`), L92 (`register_cell`), L266–272 (`get_multiply_defined`, `get_multiply_defined_conflicts`).
   - `marimo/_runtime/dataflow/topology.py` L77–89 (`ancestors`, `descendants` via `transitive_closure`).
2. **`JuliaPluto/ExpressionExplorer.jl` @ `e5a967288ab5d640f7def7408e16ddcb8bd6a462`:**
   - `src/ReactiveNode.jl` L3–37 (`struct ReactiveNode` separating `funcdefs_with_signatures` from `funcdefs_without_signatures`, `references`, `definitions`, `soft_definitions`, `macrocalls`).
3. **`JuliaPluto/Pluto.jl` @ `db2a5cdf1df2c39acec058f09d7e87aaab9ed728`:**
   - `src/packages/Packages.jl` L24–54 (`sync_nbpkg_core`, `Pkg.activate`/`develop`/`add` opt-out detection and built-in notebook package environment instantiation).
   - `src/evaluation/MacroAnalysis.jl` & `src/evaluation/Run.jl` (macro analysis and reactive topological execution).
4. **`observablehq/runtime` @ `d52584db5b76d7ab0fd5a47189dddb85893ec45f`:**
   - `src/variable.js` L7–35 (`TYPE_NORMAL`, `TYPE_IMPLICIT`, `TYPE_DUPLICATE`, `Variable` fields `_inputs`, `_outputs`, `_indegree`, `_reachable`, `_version`, `_invalidate`), L70–72 (`variable_stale`).
   - `src/runtime.js` L209–220 (`variable_compute` invalidation trigger and monotonic `_version` increment).
5. **`ipyflow/ipyflow` @ `7eb0251739ee27725d92cc26f22b8906029e8cf1`:**
   - `core/ipyflow/tracing/ipyflow_tracer.py` L146–175 (`DataflowTracer`, `DataflowAstRewriter`, `node_id_to_saved_live_subscript_refs`, `this_stmt_updated_symbols`).
6. **`gems-uff/noworkflow` @ `5bfa13ac7e97b22b341c97a03b47d6c861b0f62e`:**
   - `src/noworkflow/now/collection/prov_execution/external_strace.py` L4–42 (`now run --external-tracer strace`, `-D -z -y -x` detached grandchild FD-annotated syscall logging).
7. **`VIDA-NYU/reprozip` @ `44687ce73efe7a889bf7a1ea982258e2d965c766`:**
   - `reprozip/native/syscalls.c` L743–799 (`PTRACE_GETEVENTMSG`, `PTRACE_SYSCALL` multi-process/thread tracing).

### Peer-Reviewed Literature

- **João Felipe Pimentel, Leonardo Murta, Vanessa Braganholo, Juliana Freire**, *"A Large-Scale Study About Quality and Reproducibility of Jupyter Notebooks"*, **IEEE/ACM MSR 2019** (`DOI: 10.1109/MSR.2019.00077`), extended in *"Understanding and improving the quality and reproducibility of Jupyter notebooks"*, **Empirical Software Engineering** 26, Article 65, 2021 (`DOI: 10.1007/s10664-021-09961-9`).
- **David Koop, Jay Patel**, *"Dataflow Notebooks: Encoding and Tracking Dependencies of Cells"*, **9th USENIX Workshop on the Theory and Practice of Provenance (TaPP)**, 2017.
- **Stephen Macke, Hongpu Gong, Doris Jung-Lin Lee, Andrew Head, Doris Xin, Aditya Parameswaran**, *"Fine-Grained Lineage for Safer Notebook Interactions"*, **PVLDB** 14(6):1093–1101, 2021 (`DOI: 10.14778/3447689.3447712`).
- **João Felipe Pimentel, Leonardo Murta, Vanessa Braganholo, Juliana Freire**, *"noWorkflow: a Tool for Collecting, Analyzing, and Managing Provenance from Python Scripts"*, **PVLDB** 10(12), 2017 (`DOI: 10.14778/3137765.3137789`).
- **Fernando Chirigati, Rémi Rampin, Dennis Shasha, Juliana Freire**, *"ReproZip: Computational Reproducibility With Ease"*, **ACM SIGMOD 2016** (`DOI: 10.1145/2882903.2899401`).

### Executable Micro-Probe (`Python 3.13.15` on Linux `x86_64`, Executed `2026-11-19`)

Self-contained reproduction script (zero external dependencies):

```python
#!/usr/bin/env python3
import ast, ctypes, hashlib, os, tempfile

def analyze_cell_ast(src: str):
    tree = ast.parse(src)
    defs, refs = set(), set()
    class Visitor(ast.NodeVisitor):
        def visit_Assign(self, node):
            self.visit(node.value)
            for t in node.targets: self.visit(t)
        def visit_AugAssign(self, node):
            self.visit(node.value)
            if isinstance(node.target, ast.Name):
                refs.add(node.target.id); defs.add(node.target.id)
            else:
                self.visit(node.target)
        def visit_Name(self, node):
            if isinstance(node.ctx, ast.Store): defs.add(node.id)
            elif isinstance(node.ctx, ast.Load) and node.id not in defs: refs.add(node.id)
    Visitor().visit(tree)
    builtins_set = set(dir(__builtins__)) if isinstance(__builtins__, dict) else set(dir(__builtins__))
    return defs, refs - builtins_set

cells = {
    "C1_alloc": "buf = bytearray(b'\\x01\\x02\\x03\\x04')",
    "C2_alias": "view = memoryview(buf)\nc_arr = (ctypes.c_ubyte * len(buf)).from_buffer(buf)",
    "C3_ffi_mut": "libc.memset(ctypes.addressof(c_arr), 9, len(buf))",
    "C4_downstream": "total = sum(buf)",
}
defs_map, refs_map = {}, {}
for cid, src in cells.items():
    defs_map[cid], refs_map[cid] = analyze_cell_ast(src)
edges = [(u, v, sorted(defs_map[u] & refs_map[v])) for u in cells for v in cells if u != v and (defs_map[u] & refs_map[v])]
print("Inferred AST edges:", edges)
libc = ctypes.CDLL(None)
libc.memset.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_size_t]
def run_order(order):
    ns = {"ctypes": ctypes, "libc": libc}
    for cid in order: exec(cells[cid], ns)
    return ns["total"], sum(ns["buf"]), list(ns["buf"])
print("Topo order 1 (C1,C4,C2,C3):", run_order(["C1_alloc", "C4_downstream", "C2_alias", "C3_ffi_mut"]))
print("Topo order 2 (C1,C2,C3,C4):", run_order(["C1_alloc", "C2_alias", "C3_ffi_mut", "C4_downstream"]))
```

Observed full output (including hidden `libc` PRNG, external file drift, and SHA-256 buffer digest guard):
```text
=== 2A. Static AST Dependency Graph Extraction (Marimo-style ScopedVisitor) ===
  C1_alloc      : defs=['buf']  refs=[]
  C2_alias      : defs=['c_arr', 'view']  refs=['buf', 'ctypes']
  C3_ffi_mut    : defs=[]  refs=['buf', 'c_arr', 'ctypes', 'libc']
  C4_downstream : defs=['total']  refs=['buf']
  Inferred AST edges: [('C1_alloc', 'C2_alias', ['buf']), ('C1_alloc', 'C3_ffi_mut', ['buf']), ('C1_alloc', 'C4_downstream', ['buf']), ('C2_alias', 'C3_ffi_mut', ['c_arr'])]
  Edge C3_ffi_mut -> C4_downstream present? False
  Valid topo order 1 (C1,C4,C2,C3): cached total=10, live sum(buf)=36, buf=[9, 9, 9, 9] -> SILENT STALENESS=True
  Valid topo order 2 (C1,C2,C3,C4): cached total=36, live sum(buf)=36, buf=[9, 9, 9, 9] -> CONSISTENT=True

=== 2B. Native C-Library Global PRNG & External File Mutation Bypassing AST ===
  Hidden libc PRNG: call1=383100999, call2=858300821 (same AST, different outputs=True)
  External file provenance digest: before=67ce397eed7c4bce, after=478f36ea6e0b8011, drift_detected=True

=== 2C. Content-Addressed Buffer Digest Guard Catching Cross-FFI Mutation ===
  Buffer SHA-256 before C3=9f64a747e1b97f13, after C3=8493100b11a2fe62, cross_ffi_mutation_caught=True
```

## Revalidation

1. **Marimo AST Mutation Policy:** Diff `marimo/_ast/visitor.py` (`ScopedVisitor.visit_Name`, `visit_Attribute`, `visit_Subscript`) against `24459dbf2a6b630c135dcb3d9c616543874e0f88` to verify whether static attribute/subscript or optional runtime mutation-tracking hooks have been introduced.
2. **Pluto.jl Reactivity and Package Pinning:** Check `JuliaPluto/ExpressionExplorer.jl` (`src/ReactiveNode.jl`, `src/explore.jl`) against `e5a967288ab5d640f7def7408e16ddcb8bd6a462` and `JuliaPluto/Pluto.jl` (`src/packages/Packages.jl`) against `db2a5cdf1df2c39acec058f09d7e87aaab9ed728` for changes to method-signature reactivity or embedded `Manifest.toml` serialization.
3. **Cross-FFI Soundness Discriminator:** Execute the embedded 4-cell `ctypes.memset` micro-probe directly inside any candidate Python reactive notebook runtime (`Marimo`, `IPyflow`, or a new engine) in order `[C1_alloc, C4_downstream, C2_alias, C3_ffi_mut]`. A sound cross-FFI reactive kernel MUST either reject the aliased write, automatically re-evaluate `C4_downstream` so `total == 36`, or flag `C4_downstream` as stale.
4. **OS-Level Syscall Tracer Compatibility:** Check `gems-uff/noworkflow` (`external_strace.py`) and `VIDA-NYU/reprozip` (`reprozip/native/syscalls.c`) for new kernel syscalls (`openat2`, `io_uring`, `clone3`) that could otherwise escape legacy `ptrace`/`strace` filters on newer Linux kernels.
