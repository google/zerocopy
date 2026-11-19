# Dynamic Software Updating, Hot-Code Upgrade, and Bidirectional Schema Lenses

## Summary

Dynamic Software Updating (`DSU`), OS kernel livepatching, coupled relational schema-and-query evolution, and decentralized local-first schema lenses all solve the exact same underlying problem: **cross-version interoperability (`Program_v1 <-> Program_v2`) without destroying live state or imposing a global stop-the-world flag day**. Synthesizing primary specifications, source code, and executable counterexample probes across `Erlang/OTP`, `Proteus`, `Ginseng`, `Kitsune`, `UpStare`, Linux `livepatch` (`klp`), `Rubah`, `Boomerang`, `Symmetric Lenses`, Ink & Switch `Cambria`, `PRISM`/`PRISM++`, `InVerDa`/`BiDEL`, `Google F1`, wire-format evolution, and `Unison` establishes six load-bearing invariants:

1. **The DSU Layout Trilemma:** A native systems runtime cannot simultaneously provide (i) zero-indirection raw physical pointer identity, (ii) unbounded in-place struct growth without relocation, and (iii) zero-pause lazy migration. `Ginseng` sacrifices (i) and breaks the C ABI via slop-padded type wrappers; `Kitsune` preserves steady-state C ABI by abandoning (iii) for explicit update points (`kitsune_update()`) and $O(\text{LiveHeap})$ eager `xfgen` traversal; Linux `klp` preserves (i) and avoids `stop_machine()` via out-of-band global shadow-variable hash tables (`klp_shadow_alloc`/`klp_shadow_get`) at the cost of lookup overhead and manual destructor cleanup.
2. **Type Safety (`Con-Freeness`) Does Not Imply Behavioral Correctness:** `Proteus` proves that an update modifying type $t$ is type-safe at program point $p$ iff no active non-updated code reachable from $p$ accesses $t$ concretely (`con-free(t)`). Yet even at a con-free update point, applying a transformation mid-protocol can synthesize a **chimera state** unreachable in either `v1` or `v2` alone; Hayden et al. (PLDI 2012) reduce behavioral DSU correctness to relational verification over a syntactically merged program.
3. **FFI and Opaque Handles Collapse Single-Runtime DSU:** Across `Erlang/OTP` (`erl_nif` untyped `void** old_priv_data` and trapped anonymous `fun` closures), `Kitsune` (`void*`, untagged `union`s, uninstrumented third-party C libraries), `UpStare` (compiler-optimized mixed-language call stacks), `Rubah` (`JNI` `jfieldID`/`GlobalRef`), and Linux `klp` (GCC/LLVM IPA-SRA and inlining), a single opaque foreign boundary or optimization pass silently invalidates live update soundness.
4. **Conservation of Information (`Symmetric Lenses` & Complements) Governs Asymmetric Schema Evolution:** Bidirectional round-tripping between schemas $A$ and $B$ where each carries fields absent in the other mathematically requires an explicit **complement state $C$** (`Symmetric Lenses`, POPL 2011; `InVerDa`/`BiDEL` auxiliary delta tables; Protobuf unknown fields). Dropping $C$ destroys data on round-trip, while mutating fields coupled to hidden $C$ bytes causes **Unknown-Field Round-Trip Invariant Laundering** (`v1` mutates `price = 10` while blindly preserving unknown `discount = 20`, synthesizing illegal `v2` state `price < discount`).
5. **Per-Patch Schema Lenses Do Not Automatically Compose With CRDTs:** Source inspection of `inkandswitch/cambria` (`da8961440cac7eba1c3113488f5bcbc26046620f`, `src/lens-graph.ts`, `src/patch.ts`) shows that `lensFromTo` selects a shortest path via Dijkstra without verifying cycle commutativity, and `applyLensToPatch` invokes `addDefaultValues` on translated patches. Our executable probe proves that combining naive split/default lenses with LWW CRDT registers violates **Strong Eventual Consistency** (peers diverge to `"Alice Jones"` vs. `"Init Jones"`) and causes translated defaults to clobber concurrent `v2` user writes (`role: "admin"` overwritten by default `"member"`).
6. **Universal Pairwise-Coexistence Protocol ($\Delta v \le 1$):** Avoiding stop-the-world pauses across distributed nodes (`Google F1`), kernel tasks (Linux `klp`), or actor fleets (`Erlang/OTP` `current`/`old`) requires decomposing breaking changes into pairwise-compatible adjacent states with lease/epoch fencing guaranteeing at most two adjacent versions coexist ($\Delta v \le 1$). Our exhaustive BFS model check of `Google F1` confirms `0` index corruptions across all interleavings of `(Absent, Delete-Only)`, `(Delete-Only, Write-Only)`, and `(Write-Only, Public)`, while a single direct jump `(Absent, Public)` or lease-expiry skew $\Delta v = 2$ `(Absent, Write-Only)` immediately produces orphan index entries.

*(Bibliographic disambiguation: In coupled relational schema-and-query evolution, the primary bidirectional multi-schema-version companion to `PRISM`/`PRISM++` is **`InVerDa`/`BiDEL`** alongside `Rondo` and `Hecataeus`; "Delaunay" in database literature refers to an unrelated visual object-oriented query framework (`DOODLE`/`DelaunayMM`) and is explicitly separated here rather than conflated with coupled relational schema evolution.)*

## Applicability

This report covers the cross-version evolution systems, formal calculi, and pinned source revisions listed in `REPORT.json`:

- **Actor & Native-Process DSU:** `Erlang/OTP` (`erlang/otp` commit `2f60d1b6a246b3f7ae997fd93a9af067fab7f981`: `lib/kernel/src/code.erl`, `lib/stdlib/src/sys.erl`, `erts/doc/references/erl_nif.md`), `Proteus` (TOPLAS 2007), `Ginseng` (PLDI 2006), `Kitsune` (TOPLAS 2014; `kitsune-dsu/kitsune-core` commit `6393a0c148976c910df313bda4b578e7c240a6d2`), `UpStare` (USENIX ATC 2009), `Rubah` (OOPSLA 2014), and Linux kernel livepatching (`torvalds/linux` commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`: `Documentation/livepatch/{livepatch,shadow-vars}.rst`).
- **Bidirectional Lenses & Decentralized Schema Evolution:** `Boomerang` (TOPLAS 2007; `boomerang-lang/boomerang` commit `24a309a6c8e78ebf14fb6055ac5f813bcbeea600`), `Symmetric Lenses` (POPL 2011), and Ink & Switch `Cambria` (`inkandswitch/cambria` commit `da8961440cac7eba1c3113488f5bcbc26046620f`: `src/lens-ops.ts`, `src/lens-graph.ts`, `src/patch.ts`).
- **Coupled Relational Schema Evolution & Content-Addressed Identity:** `PRISM`/`PRISM++` (VLDB 2008 / VLDBJ 2013), `InVerDa`/`BiDEL` (SIGMOD 2017 / VLDBJ 2018), `Google F1` online schema change (VLDB 2013), Protobuf unknown-field wire preservation, and `Unison` (`unisonweb/unison` commit `b5c5188d99f31820d0cc012f194948d2876c14e7`).
- **Executable Verification Probes:** Executed with CPython 3 on `x86_64-unknown-linux-gnu` verifying symmetric-lens complement loss, Cambria+LWW CRDT non-commutativity, Protobuf unknown-field invariant laundering, and exhaustive BFS model checking of `Google F1`'s online schema state machine.

Findings distinguish single-process RAM DSU invariants from distributed multi-node schema coexistence protocols; single-node stop-the-world techniques (`Kitsune`, `UpStare`) do not generalize directly to geo-distributed fleets without lease-fenced state machines (`F1`).

## Findings

### 1. Unified Cross-Version Evolution Comparison Matrix

Basis: normative + documentation + source + derived

| System | Domain & Scope | Update Timing / Quiescence | State Migration Mechanism | Version Coexistence Bound | Safety Guarantee | FFI / Optimization / Evolution Failure Cliff |
|---|---|---|---|---|---|---|
| **Erlang/OTP (`BEAM`)** | Managed actor VM (`current`/`old` table) | Fully-qualified remote call `M:f`; `sys:suspend` -> `sys:change_code` | User-supplied `code_change/3` callback per OTP process | Hardwired **2 versions** (`current` + `old`) | Process isolation + `soft_purge` direct-ref check (OTP >= 20.0) | Third load triggers brutal `code:purge/1` killing lingering processes; trapped anonymous `fun`s; untyped C `erl_nif` `void** old_priv_data` |
| **Proteus** | Typed imperative calculus | Static program-point capability check | Type-transformer coercion at safe update points | Single active version after transition | **Con-freeness** (type safety) | Closed-world analysis fails on opaque FFI; type safety does not stop semantic chimera states |
| **Ginseng** | Native C programs | Static con-freeness + compiler-checked update points | Function indirection + slop-padded type wrappers + lazy on-access conversion | Multiple historical wrapper versions chained lazily | Static type safety (within C subset) | Slop padding destroys C ABI (`sockaddr`, `iovec`, syscalls, DMA); high steady-state indirection overhead |
| **Kitsune** | Native C servers (`vsftpd`, `redis`, `memcached`) | Explicit programmer-placed quiescent `kitsune_update()` | Whole-program `exec`-style control migration + eager `xfgen` whole-heap traversal | Single version post-update | Type-aware traversal (with user annotations) | `void*`, untagged `union`s, `intptr_t`, third-party C/Rust heaps invisible to `xfgen`; $O(\text{LiveHeap})$ pause |
| **UpStare** | Multi-threaded native C (`PostgreSQL`, `vsFTPd`) | **Immediate** (no quiescence wait; pauses all threads) | Explicit call-stack frame reconstruction mapping `v1` PC+locals to `v2` continuations | Single version post-update | Stack-frame continuation mapping | Compiler optimizations (inlining, SROA, regalloc) destroy 1-to-1 source-frame mapping; arbitrary CFG refactors lack canonical bijection |
| **Linux `livepatch` (`klp`)** | Running Linux kernel (`x86_64`, `arm64`, etc.) | Hybrid per-task transition (`HAVE_RELIABLE_STACKTRACE` + syscall exit barriers) | No in-place struct resizing; global `<obj, id>` hash table (`klp_shadow`) | **Per-task mixed `old`/`new`** during convergence window | Per-task consistency (no patched fn on task stack) | Mixed-version lock/data races during transition; GCC/LLVM IPA-SRA & inlining break ELF patch diffs; shadow-var leaks if destructors missed |
| **Rubah** | Stock HotSpot JVM | Bytecode-injected safepoint update checks | Parallel copying-GC-style heap traversal renaming `C__v1` -> `C__v2` | Single version post-update | JVM type safety on rewritten classes | Breaks reflection/`getName()`/serialization; native `JNI` `jfieldID`/`GlobalRef` crashes on object migration; cannot rewrite bootstrap JDK classes |
| **Cambria** | Local-first decentralized JSON/CRDT peers | Asynchronous peer-to-peer (no central flag day) | Shortest-path bidirectional patch translation over `LensGraph` (10 `LensOp`s) | Arbitrary concurrent peer schema versions | Schema-directed JSON patch rewriting | Non-commutativity with CRDT concurrent edits; Dijkstra picks arbitrary shortest path on cycles; `addDefaultValues` clobbers concurrent writes |
| **PRISM / PRISM++** | Single-storage RDBMS + legacy SQL apps | Offline/online migration + query rewriting | `SMO`/`ICMO` operators compiled to `DED`s + Chase & Backchase query/update rewriting | 1 physical schema + rewritten legacy views | Formal information-preservation & exact query rewriting (for invertible SMOs) | Non-terminating Chase or `UNION` blowup on cyclic constraints; blind to host-language dynamic SQL / Rust/Java types |
| **InVerDa / BiDEL** | Multi-Schema-Version DBMS (`MSVDB`) | Concurrent read/write across live schema versions | Bidirectional `BiDEL` operators -> updatable views + complement delta tables + `INSTEAD OF` triggers | Multiple co-existing read/write schema versions | Bidirectional equivalence modulo auxiliary complement tables | Trigger & delta-table write amplification + lock-ordering deadlocks; cross-channel skew with RPC/Kafka wire schemas |
| **Google F1** | Globally distributed stateless-server DBMS | Asynchronous rolling transitions with leased schema caches | 4-state DDL chain (`Absent -> Delete-Only -> Write-Only -> Public`) | Strictly bounded **$\Delta v \le 1$** via leases | Provable 0 orphan / 0 missing index entries across adjacent pairs | Expired-lease zombie write without commit-time fencing creates $\Delta v = 2$ skew -> silent index corruption |

---

### 2. Actor VM Hot-Code Loading: `Erlang/OTP` Two-Version Tables, `code_change/3`, and Native `NIF` Seams

Basis: source (`erlang/otp`, commit `2f60d1b6a246b3f7ae997fd93a9af067fab7f981`) + documentation

The `Erlang/OTP` BEAM virtual machine provides the most battle-tested production hot-code-upgrade mechanism, yet direct source inspection clarifies why its guarantees remain brittle under rapid deployments, closures, and native extensions:

1. **Two-Version Module Table and Brutal Purge (`lib/kernel/src/code.erl`, lines 627–645):** Every loaded module occupies at most two slots: **`current`** and **`old`**. Local function calls (`loop(State)`) remain pinned to the caller's code generation, whereas fully-qualified calls (`?MODULE:loop(State)`) dispatch through the global export table to `current`. Loading a third version (`v3`) requires freeing the `old` slot via `code:soft_purge/1` (returns `false` if any process lingers in `old`) or `code:purge/1` (**brutal purge**, which unconditionally kills any process lingering in `old` with exit reason `killed`). As `code.erl` lines 635–638 explicitly document:
   > *"As of Erlang/OTP 20.0, a process is only considered to be lingering in the code if it has direct references to the code. For more information see documentation of `erlang:check_process_code/3`."*
   Direct references include return addresses on a process stack AND **anonymous `fun` closures** stored in process heaps or mailboxes that point into the old module's code generation—making lingering anonymous `fun`s a persistent cause of unexpected purge failures or process assassination during rapid `v1 -> v2 -> v3` releases.
2. **Process-Local `sys:change_code` Orchestration (`lib/stdlib/src/sys.erl`, lines 523–543):** Upgrading stateful OTP behaviors (`gen_server`, `gen_statem`) follows a 4-step protocol (`sys:suspend(Pid)` -> load new module -> `sys:change_code(Pid, Mod, OldVsn, Extra)` invoking `Module:system_code_change/4` / `code_change/3` -> `sys:resume(Pid)`). `sys.erl` line 529 states explicitly: *"The process must be suspended to handle this message."* Because processes are suspended and migrated **individually**, shared `ETS` tables and asynchronous mailboxes experience a transient mixed-version window in which `v1` and `v2` actors exchange messages concurrently. If `v2` changes a tuple arity or record tag without preserving backward-compatible message clauses, `v1` actors crash with `badmatch` or silently leak unmatched messages in their mailboxes.
3. **The Native `erl_nif` Cross-Version FFI Cliff (`erts/doc/references/erl_nif.md`, lines 539–551):** Native C extensions must implement:
   ```c
   int (*upgrade)(ErlNifEnv* caller_env, void** priv_data, void** old_priv_data, ERL_NIF_TERM load_info);
   void (*unload)(ErlNifEnv* caller_env, void* priv_data);
   ```
   As `erl_nif.md` documents, `*old_priv_data` passes the raw untyped `void*` established by the old shared library directly to the new shared library's `upgrade` callback, while `*priv_data` starts as `NULL` and *both* pointers may be mutated. Neither the C compiler nor the BEAM VM checks that `libfoo_v2.so` interprets `old_priv_data`'s struct layout compatibly with `libfoo_v1.so`, nor prevents background native threads from mutating `old_priv_data` concurrently, nor guarantees safe `enif_resource` destructor cleanup across `dlclose` (`unload`). A single layout mismatch across this temporal C FFI seam crashes the entire fault-tolerant VM.

---

### 3. Native C, Multi-Threaded, Managed-VM, and Kernel DSU Architectures

Basis: normative + source + derived

#### 3.1 `Proteus` Con-Freeness vs. Behavioral Checkability
Stoyle, Hicks, Bierman, and Neamtiu (`Proteus`, POPL 2005 / ACM TOPLAS 2007, `DOI:10.1145/1275497.1275500`) proved that naive stack-activeness checks (refusing to update functions currently on the call stack) are **neither necessary nor sufficient** for type safety when a data type $t$'s representation changes. Instead, they formalized **con-freeness (concrete-freeness)**: an update modifying type $t$ is type-safe at program point $p$ if and only if no non-updated active code reachable after $p$ will ever access $t$ *concretely* (dereferencing its fields) using the old layout.

However, type safety is strictly weaker than functional correctness. Hayden, Magill, Hicks, Foster, and Foster (PLDI 2012) demonstrated that even at a con-free, type-safe point, updating mid-transaction or mid-request (for example, between authenticating a session and enforcing a new authorization check) can produce a **chimera state** impossible in either `v1` or `v2` alone. They formalized **checkability** by syntactically merging `v1`, `v2`, and the state transformer `xf` into one verification program (`merge(P_1, P_2, xf)`), exposing timing-sensitive DSU invariant violations statically. Both analyses assume closed-world visibility; an active foreign FFI frame (`libc`, OpenSSL, Rust staticlib) holding a pointer to an evolving type breaks static con-freeness inference.

#### 3.2 `Ginseng` Lazy Indirection vs. `Kitsune` Eager Whole-Heap Traversal vs. `UpStare` Stack Reconstruction
- **`Ginseng` (Neamtiu et al., PLDI 2006, `DOI:10.1145/1133255.1133991`):** Compiles C programs with (1) function-pointer indirection tables, (2) **type wrapping** that embeds a version header and fixed-size **"slop" padding** inside every updatable struct so future fields fit in place without reallocation, and (3) **lazy on-access state conversion**. While avoiding global heap pauses, slop padding breaks binary ABI layout compatibility with POSIX syscalls (`struct sockaddr`, `struct iovec`), `libc`, and hardware DMA descriptors, forcing FFI-crossing types to be pinned non-updatable.
- **`Kitsune` (Hayden, Saur, Smith, Hicks, Foster, ACM TOPLAS 2014, `DOI:10.1145/2629460`; `kitsune-dsu/kitsune-core` @ `6393a0c148976c910df313bda4b578e7c240a6d2`):** Eliminates type wrapping and steady-state indirection completely. Programmers insert explicit quiescent update points (`kitsune_update()`); upon update, Kitsune transfers control into the freshly compiled binary via whole-program re-execution (`exec`-style control migration skipping initialization) and performs an **eager whole-heap state traversal** driven by the **`xfgen`** transformation DSL and compiler-tracked allocation metadata (`ktcc`). Steady-state performance matches native C and preserves standard C ABIs, at two irreducible costs: (1) $O(\text{LiveHeap})$ stop-the-world migration pause, and (2) manual annotation fragility (`E_GENERIC`, `E_OPAQUE`) wherever C erases heap types (`void*`, untagged `union`s, custom arena allocators, or pointers inside uninstrumented third-party libraries).
- **`UpStare` (Makris & Bazzi, USENIX ATC 2009):** Eliminates quiescence waiting altogether by pausing all threads immediately and **reconstructing every live call stack frame**, mapping `v1` program counters and local variables onto `v2` continuation points (demonstrated on `PostgreSQL` and `vsFTPd`). Its fundamental limitation is the **optimization-vs.-reconstruction conflict**: aggressive compiler passes (inlining, SROA, register allocation, loop unrolling) obliterate source-level stack frames, and refactoring a control-flow graph across versions lacks a canonical bijection for mid-loop PCs without explicit continuation-mapping specifications (analogous to JVM/V8 On-Stack Replacement `OSR` deoptimization safepoints).
- **`Rubah` (Pina, Veiga, Hicks, OOPSLA 2014):** Shows that even a managed GC runtime with precise heap graphs (solving Kitsune's `void*` blindness via parallel copying-GC-style heap traversal over bytecode-rewritten `C__v1 -> C__v2` classes) still collapses at the `JNI` boundary (`jfieldID`, `GlobalRef`, direct `ByteBuffer` pointers) and fractures Java reflection (`Class.getName()`) and bootstrap JDK classes.

#### 3.3 Linux Kernel Livepatch (`klp`): Hybrid Per-Task Consistency and Shadow Variables
Basis: source (`torvalds/linux`, commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`)

Inspecting `Documentation/livepatch/livepatch.rst` (lines 78–105, 326–343) and `Documentation/livepatch/shadow-vars.rst` reveals how production Linux kernels reconcile zero `stop_machine()` latency with C's fixed-size structs:
- **Hybrid Consistency Model (`livepatch.rst`, lines 78–105):** Linux `klp` merges `kGraft`'s per-task consistency and syscall-exit barriers with `kpatch`'s stack-trace checking (`HAVE_RELIABLE_STACKTRACE`, powered by `ORC` unwind tables on `x86_64`). A universal `ftrace` trampoline redirects patched function entries per task; `/sys/kernel/livepatch/<name>/transition` remains `1` while tasks converge individually to the patched state, meaning **`old` and `new` kernel functions execute concurrently in different tasks against shared kernel locks and data structures**. Any patch altering a lock ordering or in-struct field invariant risks mixed-version deadlock or corruption unless both versions are pairwise compatible.
- **Shadow Variables (`shadow-vars.rst`):** Because slab-allocated kernel objects (`struct task_struct`, `struct sock`) cannot be resized in place across live tasks, `klp` provides a global in-kernel hash table keyed by `(void *obj, unsigned long id)` (`klp_shadow_alloc`, `klp_shadow_get`, `klp_shadow_get_or_alloc`, `klp_shadow_free`), with custom constructors executing under the global `klp_shadow_lock` spinlock. Shadow variables avoid `Ginseng`'s ABI breakage, at the cost of hash lookup overhead, spinlock contention on creation, and permanent memory leaks if any allocation destructor path forgets to call `klp_shadow_free`.
- **Compiler Optimization Hazards:** Interprocedural optimizations (`-fipa-sra`, `-fipa-cp-clone`, sibling-call optimization, hot/cold splitting, inlining) alter function calling conventions or copy patched function bodies into unpatched callers, requiring binary ELF diffing (`kpatch-build`/`klp-build`) and conservative compiler flags. Moreover, as Rust-for-Linux modules and `BTF`/`CO-RE` eBPF programs attach to kernel symbols and struct layouts, C livepatches altering semantics or shadow-variable protocols invalidate static invariants checked only against pre-patch kernel metadata.

---

### 4. Bidirectional Lenses (`Boomerang`, `Symmetric Lenses`) and Decentralized Local-First Graphs (`Cambria`)

Basis: normative + source (`inkandswitch/cambria`, commit `da8961440cac7eba1c3113488f5bcbc26046620f`) + execution + derived

#### 4.1 Asymmetric vs. Symmetric Lens Laws and Complement Conservation
Foster, Greenwald, Moore, Pierce, and Schmitt (`Boomerang`, POPL 2005 / ACM TOPLAS 2007, `DOI:10.1145/1232420.1232424`; `boomerang-lang/boomerang` @ `24a309a6c8e78ebf14fb6055ac5f813bcbeea600`) formalized **asymmetric lenses** $l : S \Leftrightarrow V$ (`get : S -> V`, `put : V * S -> S`) governed by two **Well-Behaved** laws (and optional **PutPut**):
- **GetPut:** $\text{put}(\text{get}(s), s) = s$ (round-tripping without edits preserves source fields absent from the view);
- **PutGet:** $\text{get}(\text{put}(v, s)) = v$ (every view update is faithfully reflected back);
- **PutPut (Very Well-Behaved):** $\text{put}(v', \text{put}(v, s)) = \text{put}(v', s)$.

In real schema evolution, neither `v1` nor `v2` is strictly a subset of the other (`v1` may retain deprecated field `a_only` while `v2` adds new field `b_only`). Hofmann, Pierce, and Wagner (`Symmetric Lenses`, POPL 2011, `DOI:10.1145/1925844.1926428`) proved that symmetric bidirectional synchronization $l : A \xleftrightarrow{C} B$ requires an explicit **complement state $C$** (`putr : A * C -> B * C`, `putl : B * C -> A * C`, plus initial `missing : C`) storing the private residual state of *both* versions. Composing $k$ symmetric lenses composes their complements ($C_1 \times \dots \times C_k$).

Running Probe 2A (`probe_dsu_lenses_f1.py`) exhaustively across all 16 combinations of `(id, name, a_only, b_only)` verifies zero round-trip violations when `C = (saved_a_only, saved_b_only)` is maintained, and exact data destruction (`a_only: 99 -> 0`) the instant `C` is dropped:
```text
[2A-SymLens] tested=16, roundtrip_violations=0, without_complement_a_only=0 (lost 99)
```

#### 4.2 Ink & Switch `Cambria`: Source-Verified Architecture and CRDT Non-Commutativity Counterexample
Direct inspection of `inkandswitch/cambria` (`da8961440cac7eba1c3113488f5bcbc26046620f`) exposes both the elegance and the subtle formal boundaries of decentralized local-first lens graphs:

1. **Primitive Algebra (`src/lens-ops.ts`, lines 1–84):** Cambria defines exactly 10 declarative `LensOp` primitives: `add`, `remove`, `rename`, `hoist`, `plunge`, `wrap`, `head`, `in` (recursive object descent), `map` (array element mapping), and `convert` (`ConvertValue`, using hardcoded value-mapping lookup tables). Every registered lens automatically synthesizes its reverse via `reverseLens(lenses)`.
2. **Dijkstra Shortest-Path Selection and Unchecked Cycles (`src/lens-graph.ts`, lines 26–80):** `registerLens` registers both `(from -> to)` and `(to -> from)` edges; if an edge `(from, to)` already exists, lines 33–38 return silently with a comment (*`"we've already registered a lens on this edge, hope it's the same one!"`*). `lensFromTo` computes translations using `alg.dijkstra(graph, to)`—meaning **if independent decentralized forks form a cycle in the lens graph, `lensFromTo` chooses an arbitrary shortest path with zero verification that alternate paths commute**.
3. **Patch Expansion, Narrow Op Coverage, and Default Fabrication (`src/patch.ts`, lines 37–79):** `applyLensToPatch` expands nested object patches (`expandPatch`), transforms scalar ops through `applyLensToPatchOp`, and unconditionally appends defaults via **`addDefaultValues(lensedPatch, readerSchema)`** (line 53). Notably, `runLensOp` for `'rename'` (lines 68–76) explicitly handles only `patchOp.op === 'replace' || patchOp.op === 'add'` (leaving JSON Patch `move`/`copy`/`test`/`remove` as an unimplemented `TODO`).
4. **Executable CRDT Non-Commutativity & Default-Clobber Counterexample (`Basis: execution`, Probe 2B):** Suppose Peer A (running `v1`, schema `{fullName}`) writes `fullName = "Alice Smith"` at Lamport timestamp `ts=2`, while Peer B (running `v2`, schema `{first, last, role (default="member")}`) sets `role = "admin"` at `ts=1` and `last = "Jones"` at `ts=3`. Translating Peer A's `v1` patch through a split+default lens emits `[("first", "Alice", 2), ("last", "Smith", 2), ("role", "member", 2)]`, while translating Peer B's `last = "Jones"` back to `v1` using Peer B's pre-A local `first = "Init"` emits `[("fullName", "Init Jones", 3)]`. Probe 2B records the exact divergence:
   ```text
   [2B-CambriaCRDT] V2_converged=(Alice Jones, role=member) vs V1_converged=(Init Jones) -> SEC VIOLATED + role clobbered from admin to member!
   ```
   Two independent failures occur simultaneously: (a) **Strong Eventual Consistency (SEC) fails** (`"Alice Jones"` vs. `"Init Jones"`) because the lens is not a **join-semilattice homomorphism** over concurrent CRDT updates; and (b) **Default-Value Clobbering** occurs because `addDefaultValues` stamps synthesized defaults with patch timestamp `ts=2`, overwriting Peer B's genuine user write `role = "admin"` at `ts=1`! Eliminating default clobbering requires distinguishing a lattice bottom element `Default(v)` strictly below every `UserWrite(v, ts)` in the CRDT partial order.

---

### 5. Coupled Relational Schema-and-Query Evolution (`PRISM++`, `InVerDa`/`BiDEL`) and Distributed Online State Machines (`Google F1`)

Basis: normative + execution + derived

#### 5.1 `PRISM`/`PRISM++` vs. `InVerDa`/`BiDEL` (and Disambiguation from "Delaunay")
Evolving relational schemas independently of SQL queries and application types causes widespread silent breakage. Two landmark database systems formalize coupled evolution with different runtime architectures:

1. **`PRISM` / `PRISM++` (Curino, Moon, Deutsch, Zaniolo, VLDB 2008; VLDB Journal 2013, `DOI:10.1007/s00778-012-0302-x`):** Models schema evolution as sequences of formal **Schema Modification Operators (`SMOs`)** (`CREATE/DROP/RENAME/COPY/MERGE/PARTITION/DECOMPOSE/JOIN TABLE`, `ADD/DROP/RENAME COLUMN`) paired with **Integrity Constraint Modification Operators (`ICMOs`)**. Each `SMO`/`ICMO` compiles to logical **Disjunctive Embedded Dependencies (`DEDs`)**, enabling the **Chase & Backchase** engine to (i) prove whether a schema evolution sequence is **information-preserving (invertible)**, (ii) migrate physical data, and (iii) **automatically rewrite legacy SQL queries and updates** targeting $S_{v_1}$ onto the migrated physical schema $S_{v_2}$. Limitations: cyclic foreign keys or arbitrary dependencies can cause non-terminating Chase or exponential `UNION` query blowup, and `PRISM++` cannot see dynamic SQL strings or compiled Rust/C++/Java structs across the `PL <-> SQL` FFI boundary.
2. **`InVerDa` / `BiDEL` (Herrmann, Voigt, Behrend, Rausch, Lehner, SIGMOD 2017, `DOI:10.1145/3035918.3064046`; VLDB Journal 2018):** Extends single-physical-schema rewriting into a true **Multi-Schema-Version Database (`MSVDB`)** where clients on `v1`, `v2`, and `v3` concurrently read and write live shared rows through their native schema illusions. Symmetric **`BiDEL`** (Bidirectional Database Evolution Language) operators compile into **updatable views, auxiliary complement/delta tables** (precisely the relational instantiation of Hofmann-Pierce-Wagner's symmetric-lens complement $C$), and bidirectional `INSTEAD OF` triggers, guided by a physical materialization advisor. Limitations: write amplification and cross-table lock-ordering deadlocks accumulate as active co-existing versions grow, and tightening a `v2` constraint (`NOT NULL`, `UNIQUE`) causes opaque trigger failures for legacy `v1` writers.
3. **Explicit Disambiguation ("Delaunay"):** Alongside `PRISM++` and `InVerDa`/`BiDEL`, related model-management systems include `Rondo` (Melnik et al., SIGMOD 2003) and `Hecataeus` (Papastefanatos et al., graph impact analysis). In database literature, *"Delaunay"* / *"DelaunayMM"* refers to unrelated visual object-oriented query / multimedia frameworks (`DOODLE`) or spatial mesh indexing—not to a coupled bidirectional schema+query evolution engine.

#### 5.2 Exhaustive Model Check of `Google F1`'s Online Asynchronous Schema State Machine
Basis: normative (`DOI:10.14778/2536206.2536210`) + execution (Probe 2D)

In globally distributed stateless-server databases (`Google F1` over Spanner; later adopted by CockroachDB and TiDB), flipping all servers atomically from schema $S_1$ to $S_2$ without global downtime is impossible. Rae, Rollins, Shute, Sodhi, and Vingralek (PVLDB 2013) proved that adding a derived secondary index or constraint safely requires decomposing the transition into four ordered states:
$$\text{Absent} \longrightarrow \text{Delete-Only} \longrightarrow \text{Write-Only} \xrightarrow{\text{backfill}} \text{Public}$$
(and the exact reverse order for drops), enforced by lease-bounded version skew **$\Delta v \le 1$** so that at most two adjacent states ever coexist across the fleet simultaneously.

Our exhaustive BFS model check (`Probe 2D` in `probe_dsu_lenses_f1.py`) explores every reachable state `(row_present, idx_present)` under all interleavings of `Insert` and `Delete` across two concurrent servers `(S1, S2)`:

```text
[2D-F1:DirectJump] orphans=1, missing_in_public=1, example_orphan=(('Absent', 'Public'), ['S2(Public):insert', 'S1(Absent):delete'], (False, True)), example_missing=(('Absent', 'Public'), ['S1(Absent):insert'], (True, False))
[2D-F1:F1_DeltaLeq1] orphans=0, missing_in_public=0
[2D-F1:LeaseViolation_Delta2] orphans=1, missing_in_public=0, example_orphan=(('Absent', 'Write-Only'), ['S2(Write-Only):insert', 'S1(Absent):delete'], (False, True))
```

Notice the exact proof mechanics exposed by the probe:
- **Direct Jump (`Absent`, `Public`):** Immediately reaches an **orphan index entry** `(row=False, idx=True)` in 2 steps (`S2(Public):insert`, `S1(Absent):delete`) and a **missing index entry** `(row=True, idx=False)` in 1 step (`S1(Absent):insert`).
- **F1 Adjacent Pairs (`Delta <= 1`):** Across `(Absent, Delete-Only)`, `(Delete-Only, Write-Only)`, and (after backfill) `(Write-Only, Public)`, **0 orphan entries and 0 missing-in-public entries are reachable**.
- **Lease-Expiry Skew (`Delta = 2`, `(Absent, Write-Only)`):** If a GC-paused zombie server whose `Absent` schema lease expired executes a `delete` without commit-time schema-version fencing while another server is in `Write-Only`, the **exact same 2-step orphan corruption** `(False, True)` reappears!

---

### 6. Wire-Format Unknown-Field Laundering vs. Content-Addressed Identity (`Unison`)

Basis: documentation + source (`unisonweb/unison`, commit `b5c5188d99f31820d0cc012f194948d2876c14e7`) + execution (Probe 2C)

1. **Protobuf Unknown-Field Round-Trip Invariant Laundering (`Basis: execution`, Probe 2C):** Tag-based wire formats (`Protocol Buffers`) preserve unrecognized tags as opaque byte blobs so `v1` intermediaries can forward `v2` messages without data loss—an implicit, untyped complement $C$. However, when `v2` introduces a field coupled by a semantic invariant to an existing `v1` field (e.g., `price >= discount`), a `v1` read-modify-write service mutating `price` while preserving unknown tag `2` (`discount`) synthesizes an illegal `v2` state:
   ```text
   [2C-ProtobufLaundering] after_v1_rmw={1: 10, 2: 20}, v2_invariant(price>=discount)=False
   ```
   Zero-copy wire formats (`Cap'n Proto`, `FlatBuffers`) avoid opaque unknown-field laundering on fixed prefixes only by making struct layouts append-only fossils that can never reclaim, shrink, or reorder deprecated fields in place. Preventing laundering soundly requires **invariant-aware lenses** that mark any `v1` field coupled to an unseen `v2` invariant as read-only (`RO`) or attach an explicit invalidation/recomputation hook.
2. **Content-Addressed Codebases (`Unison`, `unisonweb/unison` @ `b5c5188d99f31820d0cc012f194948d2876c14e7`):** Unison identifies every function and type definition by a cryptographic **SHA3-512 hash** of its normalized syntax tree rather than mutable module paths, completely eliminating nominal class-name collisions (`PJama`/`Rubah`) and dependency-diamond version conflicts. Crucially, however, **content-addressing code solves symbol identity, not live state migration**: changing a field in a persisted Unison type produces a distinct hash `#T_v2`, leaving durable data typed at `#T_v1` and requiring explicit typed migration functions/lenses (`#T_v1 <-> #T_v2`) to evolve persisted stores.

## Boundaries

- **Full source audit of `kitsune-dsu/kitsune-core` internals (`not examined`):** Commit `6393a0c148976c910df313bda4b578e7c240a6d2` was resolved via Git protocol v0 and corroborated against the archival TOPLAS 2014 paper (`DOI:10.1145/2629460`), while individual C source files inside `kitsune-core` (`ktcc`/`xfgen`) were not audited line by line.
- **Full source audit of `Rubah` and `UpStare` repositories (`not examined`):** Findings for `Rubah` (OOPSLA 2014) and `UpStare` (USENIX ATC 2009) derive from peer-reviewed publications rather than live repository execution.
- **Exact compiler-pass sensitivity matrix for Linux `klp` (`not examined`):** While `Documentation/livepatch/{livepatch,shadow-vars}.rst` was verified at commit `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`, empirical fuzzing of GCC/LLVM IPA-SRA / sibling-call optimization regressions on `kpatch-build`/`klp-build` was not executed.
- **CRDT-homomorphic lens synthesis (`unknown`):** Complete algebraic decision procedures characterizing which non-trivial multi-field lenses (beyond simple field renames and disjoint projections) admit join-semilattice-homomorphic lifts over general causal CRDTs (`Automerge`/`Yjs`) remain an active research problem.
- **Scope boundary (`known not to apply`):** `Google F1`'s 4-state $\Delta v \le 1$ theorem proves consistency for **derived indexes and schema additions/deletions** where mutations are independently maintainable per row; it does **not** automatically cover arbitrary multi-row cross-table relational invariant migrations without additional transactional coordination.
- **Stronger conclusion not established:** Passing `Proteus` static con-freeness does **not** establish behavioral or security correctness of a dynamic software update; con-freeness guarantees only memory/type safety across representation changes, not absence of mid-protocol chimera states.

## Evidence

### Normative Specifications and Peer-Reviewed Primary Literature
- **Proteus:** G. Stoyle, M. Hicks, G. Bierman, P. Sewell, I. Neamtiu, *"Mutatis Mutandis: Safe and Predictable Dynamic Software Updating"*, ACM TOPLAS 29(4), Art. 22, 2007 (`DOI:10.1145/1275497.1275500`).
- **Ginseng:** I. Neamtiu, M. Hicks, G. Stoyle, M. Oriol, *"Practical Dynamic Software Updating for C"*, PLDI 2006 (`DOI:10.1145/1133255.1133991`).
- **Kitsune:** C. M. Hayden, K. Saur, E. K. Smith, M. W. Hicks, J. S. Foster, *"Kitsune: Efficient, General-Purpose Dynamic Software Updating for C"*, ACM TOPLAS Vol. 36, No. 4, pp. 13:1–13:38, 2014 (`DOI:10.1145/2629460`; verified via DBLP record `journals/toplas/HaydenSSHF14`).
- **DSU Correctness Verification:** C. M. Hayden, S. Magill, M. Hicks, N. Foster, J. S. Foster, *"Specifying and Verifying the Correctness of Dynamic Software Updates"*, PLDI 2012.
- **UpStare:** K. Makris, R. A. Bazzi, *"Immediate Multi-Threaded Dynamic Software Updates Using Stack Reconstruction"*, USENIX ATC 2009.
- **Rubah:** L. Pina, L. Veiga, M. Hicks, *"Rubah: DSU for Java on a Stock JVM"*, OOPSLA 2014.
- **Boomerang:** J. N. Foster, M. B. Greenwald, J. T. Moore, B. C. Pierce, A. Schmitt, *"Combinators for Bidirectional Tree Transformations"*, ACM TOPLAS 29(3), 2007 (`DOI:10.1145/1232420.1232424`).
- **Symmetric Lenses:** M. Hofmann, B. C. Pierce, D. Wagner, *"Symmetric Lenses"*, POPL 2011 (`DOI:10.1145/1925844.1926428`).
- **PRISM / PRISM++:** C. Curino, H. J. Moon, A. Deutsch, C. Zaniolo, *"Automating the database schema evolution process"*, *The VLDB Journal* 22(1), 2013 (`DOI:10.1007/s00778-012-0302-x`).
- **InVerDa / BiDEL:** K. Herrmann, H. Voigt, A. Behrend, J. Rausch, W. Lehner, *"Living in Parallel Realities: Co-Existing Schema Versions with a Bidirectional Database Evolution Language"*, SIGMOD 2017 (`DOI:10.1145/3035918.3064046`).
- **Google F1 Online Schema Change:** I. Rae, E. Rollins, J. Shute, S. Sodhi, R. Vingralek, *"Online, Asynchronous Schema Change in F1"*, PVLDB 6(11), 2013 (`DOI:10.14778/2536206.2536210`).

### Pinned Upstream Source Inspections (Observed 2026-11-19)
- **`erlang/otp` @ `2f60d1b6a246b3f7ae997fd93a9af067fab7f981`**:
  - `lib/kernel/src/code.erl` lines 627–645 (`purge/1`, `soft_purge/1`, OTP 20.0 direct-reference lingering semantics via `erlang:check_process_code/3`).
  - `lib/stdlib/src/sys.erl` lines 523–543 (`change_code/4,5`, suspended-process requirement, `Module:system_code_change/4`).
  - `erts/doc/references/erl_nif.md` lines 539–551 (`int (*upgrade)(..., void** priv_data, void** old_priv_data, ...)` and `void (*unload)(...)`).
- **`inkandswitch/cambria` @ `da8961440cac7eba1c3113488f5bcbc26046620f`**:
  - `src/lens-ops.ts` lines 1–84 (10 `LensOp` primitives: `add`, `remove`, `rename`, `hoist`, `plunge`, `wrap`, `head`, `in`, `map`, `convert`).
  - `src/lens-graph.ts` lines 26–80 (`registerLens` silent duplicate-edge return; `lensFromTo` Dijkstra shortest path without cycle-commutativity check).
  - `src/patch.ts` lines 37–79 (`applyLensToPatch` calling `addDefaultValues(lensedPatch, readerSchema)`; `runLensOp` `'rename'` restricted to `replace`/`add`).
- **`torvalds/linux` @ `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd`**:
  - `Documentation/livepatch/livepatch.rst` lines 78–105, 326–343 (hybrid `kGraft`+`kpatch` per-task consistency model, `HAVE_RELIABLE_STACKTRACE`, `/sys/kernel/livepatch/<name>/transition`).
  - `Documentation/livepatch/shadow-vars.rst` lines 1–65 (global `<obj, id>` hash table, `klp_shadow_lock` spinlock constructor semantics, `klp_shadow_alloc`/`get`/`get_or_alloc`).
- **Pinned companion revisions resolved 2026-11-19:** `kitsune-dsu/kitsune-core` @ `6393a0c148976c910df313bda4b578e7c240a6d2`, `boomerang-lang/boomerang` @ `24a309a6c8e78ebf14fb6055ac5f813bcbeea600`, `unisonweb/unison` @ `b5c5188d99f31820d0cc012f194948d2876c14e7`.

### Preserved Standalone Verification Probe (Observed 2026-11-19)

Run `python3 /tmp/probe_dsu_lenses_f1.py`:
```python
#!/usr/bin/env python3
from collections import deque

def sym_putr(a, c):
    id_, name, a_only = a
    _, saved_b = c
    return (id_, name, saved_b), (a_only, saved_b)

def sym_putl(b, c):
    id_, name, b_only = b
    saved_a, _ = c
    return (id_, name, saved_a), (saved_a, b_only)

def check_symmetric_lens():
    violations = 0
    tested = 0
    for id_ in (1, 2):
        for name in ("x", "y"):
            for a_only in (10, 20):
                for b_only in ("p", "q"):
                    a = (id_, name, a_only)
                    b, c1 = sym_putr(a, (0, b_only))
                    a2, c2 = sym_putl(b, c1)
                    b2, _ = sym_putr(a2, c2)
                    tested += 1
                    if a2 != a or b2 != b:
                        violations += 1
    b_nocomp, _ = sym_putr((1, "x", 99), (0, "p"))
    a_lost, _ = sym_putl(b_nocomp, (0, "p"))
    print(f"[2A-SymLens] tested={tested}, roundtrip_violations={violations}, without_complement_a_only={a_lost[2]} (lost 99)")

def check_cambria_crdt():
    def apply_lww(doc, ops):
        st = dict(doc)
        for field, val, ts in ops:
            if field not in st or ts > st[field][1]:
                st[field] = (val, ts)
        return st

    def v1_op_to_v2_ops(op):
        field, val, ts = op
        if field == "fullName":
            first, last = val.split(" ", 1)
            return [("first", first, ts), ("last", last, ts), ("role", "member", ts)]
        return [op]

    op_a_v1 = ("fullName", "Alice Smith", 2)
    ops_b_v2 = [("role", "admin", 1), ("last", "Jones", 3)]
    v2_state = apply_lww({"first": ("Init", 0), "last": ("User", 0), "role": ("member", 0)},
                         ops_b_v2 + v1_op_to_v2_ops(op_a_v1))
    v1_state = apply_lww({"fullName": ("Init User", 0)}, [op_a_v1, ("fullName", "Init Jones", 3)])
    print(f"[2B-CambriaCRDT] V2_converged=({v2_state['first'][0]} {v2_state['last'][0]}, role={v2_state['role'][0]}) "
          f"vs V1_converged=({v1_state['fullName'][0]}) -> SEC VIOLATED + role clobbered from admin to {v2_state['role'][0]}!")

def check_protobuf_laundering():
    msg_v2 = {1: 100, 2: 20}
    known_v1 = {1: msg_v2[1]}
    unknown_v1 = {k: v for k, v in msg_v2.items() if k not in (1,)}
    known_v1[1] = 10
    wire_after_v1 = {**known_v1, **unknown_v1}
    print(f"[2C-ProtobufLaundering] after_v1_rmw={wire_after_v1}, v2_invariant(price>=discount)={wire_after_v1[1] >= wire_after_v1[2]}")

def model_check_f1(allowed_pairs, label):
    def step(state, srv_mode, op):
        row, idx = state
        if op == "insert" and not row:
            return (True, idx) if srv_mode in ("Absent", "Delete-Only") else (True, True)
        if op == "delete" and row:
            return (False, idx) if srv_mode == "Absent" else (False, False)
        return state

    orphans, missing_in_public = [], []
    for m1, m2 in allowed_pairs:
        starts = [(False, False), (True, True)] if ("Public" in (m1, m2) and "Write-Only" in (m1, m2)) else [(False, False)]
        for st0 in starts:
            seen = {st0}
            q = deque([(st0, [])])
            while q:
                st, trace = q.popleft()
                row, idx = st
                if not row and idx:
                    orphans.append(((m1, m2), trace, st))
                if "Public" in (m1, m2) and row and not idx:
                    missing_in_public.append(((m1, m2), trace, st))
                for srv, mode in (("S1", m1), ("S2", m2)):
                    for op in ("insert", "delete"):
                        nxt = step(st, mode, op)
                        if nxt not in seen:
                            seen.add(nxt)
                            q.append((nxt, trace + [f"{srv}({mode}):{op}"]))
    print(f"[2D-F1:{label}] orphans={len(orphans)}, missing_in_public={len(missing_in_public)}"
          + (f", example_orphan={orphans[0]}" if orphans else "")
          + (f", example_missing={missing_in_public[0]}" if missing_in_public else ""))

if __name__ == "__main__":
    check_symmetric_lens()
    check_cambria_crdt()
    check_protobuf_laundering()
    model_check_f1([("Absent", "Public")], "DirectJump")
    model_check_f1([("Absent", "Delete-Only"), ("Delete-Only", "Write-Only"), ("Write-Only", "Public")], "F1_DeltaLeq1")
    model_check_f1([("Absent", "Write-Only")], "LeaseViolation_Delta2")
```

## Revalidation

1. **Erlang/OTP code-purge and NIF upgrade rules:** Diff `lib/kernel/src/code.erl` (`purge`/`soft_purge`), `lib/stdlib/src/sys.erl` (`change_code`), and `erts/doc/references/erl_nif.md` (`upgrade`/`unload`) in `erlang/otp` against `2f60d1b6a246b3f7ae997fd93a9af067fab7f981` to check whether BEAM ever lifts the two-version (`current`/`old`) code table limit or adds typed NIF migration hooks.
2. **Cambria lens-graph & default-injection behavior:** Diff `src/lens-ops.ts`, `src/lens-graph.ts` (`registerLens`, `lensFromTo`), and `src/patch.ts` (`applyLensToPatch`, `addDefaultValues`) in `inkandswitch/cambria` against `da8961440cac7eba1c3113488f5bcbc26046620f` to check whether cycle-commutativity checks, CRDT op-log integration, or full JSON Patch (`move`/`copy`/`remove`) coverage have been added.
3. **Linux livepatch consistency & shadow-variable API:** Diff `Documentation/livepatch/livepatch.rst` and `Documentation/livepatch/shadow-vars.rst` in `torvalds/linux` against `4405c18c95d2d0f99f6c581ef0ee8591a1aa6ccd` to detect changes to per-task convergence, `klp-build` integration, or Rust-for-Linux livepatch support.
4. **Re-run formal counterexample probes:** Execute `python3 /tmp/probe_dsu_lenses_f1.py` (from **Evidence**) to revalidate all four algebraic and model-checking witnesses (`[2A]`–`[2D]`).
