# Storage deadness under aliasing: CompCert's verified value and neededness analyses, proved and production escape analyses, Clang loan/origin liveness, Go pointer liveness, and Mojo origin-based destruction

## Summary

- **One predicate, five actions.** Every examined system decides that storage is dead with the same two-part test: an over-approximating *may-reference* relation (CompCert abstract pointers, escape-graph edges, Clang loan sets per origin, Mojo origins) combined with the *liveness of the references themselves*. Storage is dead at a point only if no reference that may still be used may reach it. The systems differ in what they do with the answer: CompCert *eliminates* stores, the escape analyses (Blanchet, Choi et al., partial escape analysis, Go) *promote* storage to the heap, Clang *warns*, Mojo *extends* the owner's lifetime or *rejects* the program, and the Go runtime *skips scanning* dead address-taken stack objects. Basis: source + documentation + derived.
- **CompCert 3.18 can mark only two kinds of memory dead: byte intervals of the current function's stack frame (`Stk ofs`) and precise offsets inside a named global (`Gl id ofs`).** A store through any less precise abstract pointer (`Stack`, `Glo`, `Glob`, `Nonstack`, `Ptop`) is never removed and kills nothing. A load through `Glob`, `Nonstack` or `Ptop` makes *all* memory live. A call to an unknown function makes all memory live. `Ireturn` and `Itailcall` kill exactly the frame's `[0, fn_stacksize)`. The dead-code pass is proved by a forward simulation whose memory invariant (`magree`) requires source and target memories to agree only on locations that `nlive` reports live. Basis: source.
- **The Robert–Leroy (2012) verified alias analysis is not the analysis that CompCert ships.** The paper's analysis uses allocation-site abstract blocks (`Allocs(Just l)`), performs weak updates only, raised compilation time by about 40% on most test files, and let CSE remove about 1,400 more loads than the 5,600 it removed without alias information. The CompCert 3.18 value analysis (introduced in release 2.2, 2014) uses an eight-constructor abstract-pointer lattice that has no allocation sites, and it replaces (strongly updates) the abstract cell stored at a `Stk ofs` or `Gl id ofs` address. Basis: documentation (paper full text, changelog) + source + derived.
- **Of the four escape analyses examined, only Blanchet's claims a correctness proof in the material read.** It is proved with aliases as an intermediate step. The abstract of Choi et al. presents connection-graph summaries with experimental results and claims no proof. The abstract of the partial-escape-analysis paper reports performance, not a proof. Go's `escape` package states two invariants and enforces them with a conservative graph walk. In Go, the following force heap allocation:
  - dynamic calls (interface methods, function values);
  - storing into a location declared at a shallower loop depth;
  - assignments from a child closure to an outer variable;
  - returning an address to a caller;
  - size thresholds of 128 KiB for explicit variables and 64 KiB for implicit allocations.

  All five behaviors were reproduced with the released go1.27.3 compiler. Basis: source + execution.
- **Liveness of references is computed by flow-sensitive analyses that are not verified.**
  - Clang's lifetime-safety analysis runs a backward `LiveOrigins` analysis with `Must`/`Maybe` confidence and a forward loan-propagation analysis. It warns when a loan whose access path has expired is still held by a live origin. Heap and global access paths are explicitly not modeled.
  - Go's liveness maps exclude address-taken variables. Those variables become "stack objects" that the garbage collector traces dynamically. A dead stack object stays allocated, in a "moribund state", until its frame is popped.
  - Mojo destroys a value after its last use. Origins extend the owner's lifetime to cover live references. Untracked origins and pointers that cross into C sever that link without a compiler error.

  Basis: source + execution (Go) + documentation (Mojo).
- **Dead value, dead reference and dead storage coincide only when every reference to the storage is tracked.** In Pearce's Featherweight Rust, lifetimes are lexical, so storage dies at block exit regardless of last use. Pearce's soundness proof is a paper proof (in an appendix), backed by model checking more than 500 billion programs and by fuzzing `rustc` against 2 billion programs. The preprint describes no proof-assistant mechanization. Basis: documentation + derived.

## Applicability

The report compares independent subjects; it does not study their combination.

- **CompCert** (`AbsInt/CompCert` at the pinned revision, `VERSION` file `version=3.18`): `backend/ValueDomain.v`, `backend/ValueAnalysis.v`, `backend/NeedDomain.v`, `backend/Deadcode.v`, `backend/Deadcodeproof.v`, and the x86 instance `x86/NeedOp.v`. The neededness of individual operators is architecture-specific (`NeedOp.v`). The memory-neededness and soundness statements cited here are architecture-independent backend files.
- **Robert and Leroy, CPP 2012**: read in full from the authors' PDF. It describes an analysis integrated into a CompCert of that era. No repository revision of that integration was examined.
- **Clang lifetime safety** (`llvm/llvm-project` at the pinned revision): `clang/lib/Analysis/LifetimeSafety/*.cpp` and `clang/include/clang/Analysis/Analyses/LifetimeSafety/*.h`, plus `clang/include/clang/Basic/DiagnosticGroups.td`. Behavior was examined from source only, because no Clang binary was run.
- **Go**: source was examined at `golang/go` revision `34c413ad2a85db3857ecfd73d9d6d682e40e30d5` (2026-11-20): `src/cmd/compile/internal/escape/*.go`, `src/cmd/compile/internal/liveness/plive.go`, `src/cmd/compile/internal/ir/cfg.go` and `src/runtime/mgcstack.go`. Probes were executed with the *released* go1.27.3 compiler (tag commit `2aae1000ea1d4b28923b96db28acf4e3b99d6aff`) on linux/amd64; the compile tool's SHA-256 is recorded in `support/toolchain.txt`. The executed toolchain is a distribution-packaged build of that tag; distribution patches were not inspected. Probe results are claimed for go1.27.3 only. Agreement with the HEAD source is an inference from reading the same rules (`outlives`, `HeapAllocReason`, `tagHole`, `shouldTrack`) in the HEAD tree; it was not re-executed at HEAD.
- **Mojo** (`modular/modular` at the pinned revision): the user manual pages `Mojo/docs/site/manual/lifecycle/death.mdx` and `Mojo/docs/site/manual/values/lifetimes.mdx`, and the design note `Mojo/proposals/origin-design.md`, whose status line reads `**Status**: Draft`. The Mojo compiler passes named there (`CheckLifetimes`, `LowerLIT`) are not in the repository, so every Mojo claim has documentation basis only. `death.mdx` records `Compiler verified: 2026-10-16, Mojo 1.2.0.dev2026101520 (d2872eb2)`.
- **Escape-analysis papers**: Blanchet (TOPLAS 2003) and Choi et al. (TOPLAS 2003, journal version of OOPSLA 1999) were examined through their abstracts in Crossref metadata. Stadler et al. (CGO 2014) was examined through its abstract as indexed from the authors' institution. Their full texts were not read; claims about their proofs are limited accordingly.
- **Pearce (TOPLAS 2021)**: the abstract comes from Crossref. The technical content comes from the author's March 2020 preprint, so wording may differ from the published version.

## Findings

### 1. CompCert: value analysis → neededness → dead-code elimination

**1.1 Abstract pointers and the "private call" escape test.** `ValueDomain.v` abstracts a pointer by an eight-way lattice (lines 121–129):

```coq
Inductive aptr : Type :=
  | Pbot | Gl (id: ident) (ofs: ptrofs) | Glo (id: ident) | Glob
  | Stk (ofs: ptrofs) | Stack | Nonstack | Ptop.
```

Blocks are classified as `BCinvalid | BCglob id | BCstack | BCother`. The invariant `sound_state_base` for a regular state includes `(SP: bc sp = BCstack)`: the current frame is the unique `BCstack` block (`ValueAnalysis.v` line 1115). Whether the frame has escaped is decided per call by `analyze_call` (`ValueAnalysis.v` lines 39–43):

```coq
Definition analyze_call (am: amem) (aargs: list aval) :=
  if pincl am.(am_nonstack) Nonstack
  && forallb (fun av => vpincl av Nonstack) aargs
  then (Ifptr Nonstack, mafter_private_call am)
  else (Vtop, mafter_public_call).
```

If no argument and no non-stack memory may hold a pointer into the frame, the call is *private*: the abstract stack contents `am_stack` survive the call. Otherwise, `mafter_public_call := mtop` forgets everything. This one Boolean is CompCert's escape analysis for stack frames. Basis: source.

**1.2 Pointer arithmetic degrades precision rather than soundness.** `poffset` maps `Gl id ofs ↦ Glo id` and `Stk ofs ↦ Stack` (lines 358–363). The "provenance" comment states the GCC-style policy that "undefined" arithmetic on a pointer yields a pointer into the *same block* at an unknown offset. In conservative mode, an integer literal used as an address is treated as `Nonstack` (`int_provenance`, line 828), except for 0. Consequently, any masked or realigned stack pointer becomes `Stack`, which falls into the "never killed" class below. Basis: source.

**1.3 The neededness domain.** Register neededness is `nval ::= Nothing | I mask | L mask | All` (bit-level for 32- and 64-bit integers). Memory neededness is (`NeedDomain.v` lines 1901–1903):

```coq
Inductive nmem : Type :=
  | NMemDead
  | NMem (stk: ISet.t) (gl: PTree.t ISet.t).
```

`NMem stk gl` means "all memory locations are used, except" the stack offsets in `stk` and the per-global offsets in `gl`. `nlive` (line 1917) is the concrete reading: a location `(b, ofs)` is live unless `b = sp` and `ofs ∈ stk`, or `b` is the block of a global `id` and `ofs ∈ gl!id`. Deadness is therefore recorded as a finite set of byte intervals, and the default is *live*. The three operations are deliberately asymmetric:

| Abstract address `p` | `nmem_add` (load makes range live) | `nmem_remove` (store kills range) | `nmem_contains` (is store needed?) |
|---|---|---|---|
| `Stk ofs` | removes interval from `stk` | adds interval to `stk` | precise interval test |
| `Gl id ofs` | removes interval from `gl!id` (if present) | adds interval to `gl!id` | precise interval test |
| `Glo id` | drops `id` from `gl` | no change | `true` (conservative) |
| `Stack` | empties `stk` | no change | `true` |
| `Glob`, `Nonstack`, `Ptop` | `nmem_all` (everything live) | no change | `true` |

Basis: source (`nmem_add` lines 1940–1957, `nmem_remove` 2025–2041, `nmem_contains` 2077–2091; the comment at line 2089 reads `(**r conservative answer *)`).

**1.4 Transfer function and transformation (`Deadcode.v`).** The analysis is a backward dataflow (`Backward_Dataflow_Solver`) over `NA.t = nenv × nmem`. The memory-relevant rules are:

- `Istore`: if `nmem_contains nm p (size_chunk chunk)` then the stored value and the address registers become needed and the range is removed (killed). Otherwise the state is unchanged, and `transf_instr` replaces the store with `Inop` (lines 147–152 and the `Istore` case of `transf_instr`).
- `Iload`: if the destination register is dead, the load is removed. Otherwise the loaded range is added with `nmem_add`.
- `Icall` to a function that is not a known runtime function: `(..., nmem_all)` (line 156). All memory becomes live before an unknown call, because the callee may read anything the analysis cannot rule out.
- `Itailcall` and `Ireturn`: `nmem_dead_stack f.(fn_stacksize)` (lines 165, 174). The frame `[0, sz)` is dead and everything else is live, which reflects the frame being freed.
- `EF_memcpy`: the copy is removed when its destination is not needed. Otherwise the destination is killed and the source added. Unknown builtins yield `nmem_all`.

Basis: source.

**1.5 Soundness statement.** `Deadcodeproof.v` line 1263:

```coq
Theorem transf_program_correct:
  forward_simulation (RTL.semantics prog) (RTL.semantics tprog).
```

The simulation invariant is `match_states s1 s2 /\ sound_state prog s1`, so value-analysis soundness is a conjunct. For regular states, the memory component is (line 529):

```coq
(MEM: magree m tm (nlive ge sp (snd (transfer f (prog_defmap cu) (vanalyze cu f) pc an!!pc))))
```

`magree m1 m2 P` (line 40) is a weakened `Mem.extends`. Permissions agree in both directions up to `Max Nonempty`, `nextblock` is equal, and contents are `memval_lessdef` *only at locations satisfying `P`*. At call and return states, the invariant is the full `Mem.extends m tm`. Deadness therefore never crosses a call boundary: any memory the callee might observe must agree exactly up to `lessdef`. This is the formal counterpart of rule 1.4's `nmem_all` at unknown calls. Basis: source.

**1.6 Program patterns where CompCert must treat storage as possibly live.** Each row follows from 1.1–1.4.

| Pattern | Mechanism | Effect on dead-store elimination |
|---|---|---|
| Local whose address is passed to, or stored where reachable by, a callee | `analyze_call` sees a stack-pointing value, so the call is public and `mtop` | Stack contents become unknown after the call; neededness before an unknown call is `nmem_all` |
| Any call to an unknown or external function | `Icall` with no known runtime function, so `nmem_all` | No store before the call is removable |
| Pointer arithmetic, masking or realignment | `poffset`: `Stk ofs` becomes `Stack` | Stores through it are never removed and kill nothing |
| Integer cast to a pointer (conservative mode) | `int_provenance` gives `Nonstack` | A load through it makes all memory live |
| Heap (`malloc`) storage | represented by `Nonstack`/`Ptop` | Heap stores are never eliminated |
| Imprecise global offset (array indexed by a variable) | `Glo id` | Kills nothing; the needed-test is `true` |
| Unknown builtin, volatile access | `transfer_builtin` default yields `nmem_all` | No elimination across it |

Basis: source + derived.

**1.7 Relation to Robert–Leroy (CPP 2012).** The paper's analysis abstracts blocks as `Stack | Globals(Just id) | Globals(All) | Allocs(Just l) | Allocs(All) | Other | ⊤`, and abstract locations as pairs of a block and an offset. It is "intraprocedural, flow-sensitive, field-sensitive, and untyped". Its soundness proof is constructive: for each reachable concrete state it builds an "abstracter" `block -> option absb`. The paper lists strong updates as future work. It reports roughly 1,200 lines of Coq specification and 2,200 lines of proof. In its evaluation on the CompCert test suite, "overall compilation times increase by 40%", and a few SPASS files more than double. CSE removed "about 1400 redundant loads in addition to the 5600 it removes without this information, a 25% gain". The changelog for CompCert release 2.2 (2014-02-24) introduces "Value analysis, tracking constants, some integer range information, and pointer aliasing information" and "Neededness analysis, generalizing liveness analysis to individual bits of integer values and to stack memory locations".

Comparing the paper's block grammar with `aptr` at the pinned revision shows three differences in the shipped analysis:
- it has **no allocation-site blocks**;
- it **merges pointer and value abstraction** in one `aval` domain;
- its `store` *replaces* the abstract cell at a `Stk ofs` or `Gl id ofs` address (`ablock_store`, lines 3669–3675: `ZTree.set` after invalidating overlapping cells, with only the block summary joined). Stores through `Stack` or `Glo id` reset the block to its summary (`ablock_store_anywhere`), and stores through `Glob`, `Nonstack` or `Ptop` empty `am_glob`.

Basis: documentation + source + derived.

### 2. Escape analyses: what each correctness statement quantifies over

| System | Formal status | Quantifies over | Unit of escape | Constructs that force heap or "escaping" |
|---|---|---|---|---|
| Blanchet, TOPLAS 2003 | Correctness proof; "a new method to prove the correctness of this analysis, using aliases as an intermediate step" (abstract) | Executions of the analyzed Java program under the paper's semantics (details of the semantics not examined) | Integers representing "the escaping parts of values" (abstract) | Not examined beyond the abstract; field assignments are analyzed flow-insensitively |
| Choi et al., OOPSLA 1999 / TOPLAS 2003 | Algorithm with experimental evaluation; no proof is claimed in the abstract | Objects not reachable after their creating method returns (stack allocation), or reachable from one thread only (lock elision) | Connection-graph nodes, with per-method summaries reusable "in different calling contexts without introducing imprecision" | Not examined beyond the abstract |
| Stadler et al., CGO 2014 (partial escape analysis) | Abstract reports evaluation only; full text not examined | Per control-flow path rather than all-or-nothing per allocation | Virtual objects, materialized on paths where they escape | Escape on a path forces materialization on that path only |
| Go `escape` (go1.27.3 and HEAD) | No proof. Two invariants are documented in `escape.go` lines 26–31: "(1) pointers to stack objects cannot be stored in the heap, and (2) pointers to a stack object cannot outlive that object" | Locations in a directed weighted graph whose edges are assignments weighted by dereferences minus address-ofs | Whole variables ("without distinguishing elements within a compound variable", line 74) | See the following table |

Go's heap-forcing rules (source: `solve.go` `outlives` lines 370–422, `call.go` `tagHole` lines 390–393, `utils.go` `HeapAllocReason` line 173, `ir/cfg.go` lines 11 and 19), with execution results from `support/go_escape`:

| Construct | Source rule | Probe | go1.27.3 diagnostic |
|---|---|---|---|
| Return `&x` | result parameter sink: "pessimistically we need to assume they flow to the heap" | E1 | `moved to heap: x` |
| Address used only locally | none fires | E2 | (no heap diagnostic) |
| Pointer declared outside a loop gets a per-iteration allocation | `s.loopDepth < other.loopDepth` gives outlives | E3 | `new(int) escapes to heap`, although the pointer never leaves the function |
| Allocation and pointer both inside the loop | none fires | E3b | `new(int) does not escape` |
| Pointer passed through an interface call | `tagHole`: "If this is a dynamic call, we can't rely on param.Note", so `heapHole()` | E4 | `moved to heap: x`; `leaking param: s` |
| Same callee, static call | parameter tag `p does not escape` | E5 | (no heap diagnostic) |
| Store into a package-level variable | heap sink | E6 | `moved to heap: x` |
| `reflect.ValueOf(&x)` | flows to heap through the callee's tags | E7 | `moved to heap: x` |
| Closure called immediately vs. returned | `ContainsClosure` / closure-result rules | E8a / E8b | `func literal does not escape` / `moved to heap: x`, `func literal escapes to heap` |
| `var a [200000]byte` | `MaxStackVarSize = 128*1024` | E9a | `moved to heap: a` |
| `new([70000]byte)` / `new([60000]byte)` | `MaxImplicitStackVarSize = 64*1024` | E9b / E9c | `escapes to heap` / `does not escape` |
| `make([]int, n)` with non-constant `n` | hybrid: a constant-size stack backing store when `cap <= K`, otherwise `makeslice` (utils.go lines 221–234) | E10 | `make([]int, n) does not escape` |

Basis: source + execution (go1.27.3, linux/amd64). E3 shows that Go's notion of "outlives" is *scope-based*, keyed by loop depth, not *use-based*: the allocation is heap-allocated because a pointer variable declared outside the loop could carry it across iterations, even though no use ever does. Basis: execution + derived.

`go` statements route arguments through `heapHole()` (`call.go`, `goDeferStmt`), so values passed to a new goroutine are heap-allocated by construction. Top-level `defer` arguments are an exception: they "don't escape to the heap, but they do need to last until they're invoked". Basis: source.

### 3. Liveness of references

**3.1 Clang lifetime safety (intraprocedural, diagnostic only).** The header describes the design as "based on the concepts of 'origins' and 'loans'" and links an RFC for intraprocedural lifetime analysis. Its components are:

- A **loan** is issued by a borrow (`IssueFact`) to an **access path** (`x`, `x.field`, `x.*`, `$param.field`). `Loans.h` line 126 reads `TODO: Model access paths of other types, e.g. heap and globals.` Placeholder paths (parameters, `this`, fields) "never expire within the function scope" (line 75).
- An **origin** is the abstract lifetime variable of a pointer-like expression or declaration. `LoanPropagation` is a forward analysis mapping each origin to "the set of loans it contains" with union joins. An `IssueFact` replaces the origin's loans ("Old loans are erased"). `OriginFlowFact` either replaces or merges.
- `LiveOrigins` is a **backward** analysis (`LiveOrigins.cpp`):
  - A `UseFact` makes an origin live with `Must` confidence (line 153).
  - An `OriginEscapesFact` (return, field, global, `this`) makes the origin live, but a `ParamEscapeFact` does not (lines 168–170). Such facts are "only used to verify annotations".
  - An `IssueFact` *kills* liveness of its origin (line 176).
  - A flow propagates liveness from destination to source and optionally kills the destination (line 182).
  - At joins, an origin live on only one branch is demoted to `Maybe` (line 128: `Only return "Must" if both paths are "Must", otherwise Maybe`).
  - Block-local origins are dropped at block exit (`transferAtBlockExit`, line 105).
- `MovedLoans` is a forward analysis that marks loans whose storage may have been moved out. It feeds the "-moved" diagnostic variants, which `DiagnosticGroups.td` documents as possibly containing "false-positives, e.g. when the borrowed storage is potentially moved and is not destroyed at scope exit" (line 576).
- `Checker::checkExpiry` (line 301) fires at each `ExpireFact`. For every live origin it looks at the loans the origin holds; when the expired path is a prefix of a loan's path, it records a pending warning. The warning is "dominating" only if liveness is `Must` (`causingFactDominatesExpiry`, line 36). `-Wlifetime-safety-permissive` groups the non-moved variants; `-Wlifetime-safety-strict` adds the moved variants (lines 671–685).

The examined files only emit diagnostics; nothing in them changes generated code. The analysis is not verified, and no soundness statement exists in the examined files. Basis: source + derived.

**3.2 Go pointer liveness maps and stack objects.** `plive.go` computes, for each safe point, which pointer-containing stack slots are live. `shouldTrack` (line 220) admits `PAUTO` variables that did not escape, plus parameters and results. Address-taken variables are not tracked by the dataflow. They are emitted as stack objects (`emitStackObjects`, line 1498: `shouldTrack(n) && n.Addrtaken() && n.Esc() != ir.EscHeap`). `runtime/mgcstack.go` explains why: accesses made through a pointer to such a variable cannot in general be followed by a static analysis (lines 19–24), so the runtime traces stack objects reachable from statically live pointers. "Any dead stack objects are not scanned and their contents will not keep heap objects live", but "they live on in a moribund state until the stack frame that contains them is popped" (lines 46–50).

Execution with `-gcflags='-live -l'` (`support/go_live/live.txt`):

| Probe | Situation | Live set at `safepoint()` |
|---|---|---|
| L1 | heap pointer `p` last used before the call | `p` not listed (dead) |
| L2 | `p` used after the call | `live at call to safepoint: p` |
| L3 | `runtime.KeepAlive(p)` after the call | `live at call to safepoint: p` |
| L4 | address-taken `var b box` containing a pointer | `b` not in the map at the safepoint; the compiler reports `stack object b box` |

Basis: execution + source. In Go, therefore, *reference deadness* is decided statically for non-address-taken slots and dynamically for address-taken ones. *Storage deadness* of a stack slot is never acted on before frame exit. *Value deadness* of the heap object depends on both. Basis: derived.

**3.3 Mojo: ASAP destruction with origins (documentation only).** The rules, as documented:
- "Mojo destroys values as soon as they're no longer used", and "At compile time, Mojo determines the last use of each value" (`death.mdx` lines 11, 17).
- "A pointer whose origin ties back to the owner keeps the owner alive automatically" (line 185).
- "Without an origin, a dependency is invisible and the owner dies after the pointer construction and origin cast" (line 221). The worked example casts to `MutUntrackedOrigin` and documents the later use as "undefined behavior: the owner is already gone".
- "If the C side retains a pointer past the call, no origin saves you" (line 239).
- RAII guards and erased-origin pointers "particularly need explicit lifetime extension", and "Neither produces a compiler error" (line 266).
- `_ = value` "can only extend the lifetime of a value, it never forces a value to be destroyed" (line 275).

The design note (`origin-design.md`) states four invariants enforced by `CheckLifetimes`: "Use before destroy", "Lifetime extension", "Argument exclusivity", and "ASAP destruction". It says "Origins are symbolic, compile-time values. They do not name storage addresses", and `LowerLIT` "strips all origin types/attrs", so origins have no run-time representation. Interior origins are "experimental". They apply "cleanly" only when the base value "uniquely owns" the storage, and they "do not help with untracked pointers ... or code that stores raw addresses past the lifetime of the owning container" (lines 885–899). Basis: documentation.

**3.4 Featherweight Rust (Pearce).** FR "most closely resembles that of Rust 1.0 where lifetimes were largely based on the lexical structure of programs" and "does not support non-lexical lifetimes". A block `{…}^m` drops, on exit, every location declared in lifetime `m` (`R-BlockB` with `drop(S, m)`, Definition 3.4). `drop` recursively deallocates locations reached through *owning* references `ℓ•` but not through *borrowed* references `ℓ∘`. Heap boxes receive the global lifetime `*`. Theorem 4.12 (Type and Borrow Safety) states that a well-typed term in a valid state reduces to a terminal state. Borrow safety, meaning at most one mutable borrow per lval, is a separate corollary (4.14) over "borrow safe" environments. The theorem requires termination; the text notes that loops and recursion would need a weaker theorem. Validation (abstract): "model checked our calculus using over 500B input programs", and fuzz testing of `rustc` against "2B programs" found "one confirmed compiler bug". Basis: documentation (preprint + abstract).

### 4. What "dead" means at a program point

| System | Dead value | Dead reference | Dead storage | Coincide under aliasing? |
|---|---|---|---|---|
| CompCert neededness | Register `r` with `nreg = Nothing`, or bits outside the `I`/`L` mask | No separate notion; pointers are values in registers or memory | A byte interval in `stk` (own frame) or `gl!id` that no later load can read, given the abstract pointers | Only for `Stk ofs` / `Gl id ofs` addresses; storage reachable through imprecise pointers is always live |
| Go escape analysis | Not modeled (no last-use) | Not modeled | Storage may stay on the stack iff no path to a location that *outlives* it (heap, caller result, outer loop depth, enclosing function) | No: decided by scope and loop depth, not by last use (probe E3) |
| Go liveness + GC | Heap object unreachable from live slots or traced stack objects | Pointer slot not live at the safe point (static), or stack object unreachable from live pointers (dynamic) | A stack slot is reclaimed only at frame pop; dead stack objects are "moribund" | Reference deadness yes; storage deadness never before frame exit |
| Clang lifetime safety | Not modeled | Origin absent from the `LiveOrigins` state (`Must`/`Maybe` otherwise) | `ExpireFact` at scope end or invalidation; storage death is lexical C++ scope, not an analysis result | Diagnoses only (live origin ∧ expired loan). Heap and global paths not modeled |
| Mojo | After the last use, extended by the uses of every reference whose origin names it | Last use of the reference value | Destroyed right after the value's (extended) last use | Yes for tracked origins. No for untracked/`AnyOrigin`/FFI, where the owner may die while a raw pointer is live (documented undefined behavior) |
| Featherweight Rust | Value dropped when its owning location is dropped | A borrowed reference may not outlive its lifetime (typing) | Lexical block exit (`drop(S, m)`) | Yes by typing, but deadness is lexical, so last-use reclamation is not modeled |
| Blanchet / Choi / PEA | Not examined | Not examined | Object does not escape its method or thread (stack allocation / scalar replacement) | Not examined beyond the abstracts |

Only Mojo makes **storage death follow reference liveness**: storage dies when its last live reference dies. All other systems fix storage death independently and then either restrict references to fit it (FR, Clang, Go escape) or ignore references they cannot see (CompCert's imprecise pointers are conservatively live). Basis: derived from the rows above.

### 5. Performance and resource footprint (L1–L6)

Every cell is measured, cited, derived, or marked `not measured`. "Measured" means counted or run on a 96-core Intel Xeon @ 2.60 GHz Linux host.

| System | L1 authoring / proof size | L2 toolchain build | L3 analysis latency | L4 generated-code effect | L5 proof check | L6 memory / size |
|---|---|---|---|---|---|---|
| Robert–Leroy 2012 | about 1,200 spec + 2,200 proof lines of Coq (cited); proof/spec = 1.83 (derived) | not measured | compilation time +40% on most files; more than 2× on some SPASS files (cited) | about 1,400 extra loads removed vs 5,600 (cited; static count, not runtime) | not measured | not measured |
| CompCert 3.18 files | non-blank, non-comment lines inside/outside `Proof…Qed` (measured): `ValueDomain.v` 2,521/2,124; `ValueAnalysis.v` 1,119/687; `NeedDomain.v` 1,122/853; `Deadcode.v` 0/215; `Deadcodeproof.v` 848/320 (ratio 2.65, derived) | not measured | not measured | not measured | not measured | not measured |
| Blanchet 2003 | not measured | not measured | not measured | 13–95% of data stack-allocated; up to 43% runtime decrease, 21% average (cited) | not measured | not measured |
| Choi et al. 2003 | not measured | not measured | not measured | more than 70% of objects stack-allocatable in 3 of 10 benchmarks, median 19%; 11–92% of lock operations removed (median 51%); 2–23% execution-time reduction (median 7%) on a 333-MHz PowerPC (cited) | n/a (no proof) | not measured |
| Partial escape analysis (Graal) | not measured | not measured | not measured | allocated memory reduced by up to 58.5%; performance improved by up to 33% (cited abstract) | n/a | not measured |
| Go escape + liveness | `escape/*.go` 3,764 lines; `plive.go` 1,645 lines at HEAD (measured, `wc -l`) | not measured | not measured | heap vs stack classification of E1–E10 (measured); runtime cost not measured | n/a (no proof) | stack thresholds 128 KiB explicit, 64 KiB implicit (source); E9 probes confirm both boundaries (measured) |
| Clang lifetime safety | `LifetimeSafety/*.cpp` + `Dataflow.h` 4,044 lines; headers 1,548 lines (measured, `wc -l`) | not measured | not measured | none expected (diagnostic-only; derived from source) | n/a (no proof) | not measured |
| Mojo origins | not measured | not measured | not measured | none from origins themselves; stripped in `LowerLIT` (documentation) | n/a | zero run-time bytes for origins (documentation) |
| Featherweight Rust | paper proof in an appendix; size not measured | not measured | not measured | n/a (calculus) | over 500 billion programs model-checked; 2 billion programs used to fuzz `rustc` (cited) | not measured |

### 6. Human comprehensibility and conceptual simplicity (C1–C2)

- **Concept count (C1).** The number of distinct notions a reader must hold to predict "is this store or object dead?" differs widely between systems. The counts below are derived from the cited definitions.
  - CompCert: 8 `aptr` constructors, 4 `nval` cases, the `nmem` reading ("everything is live except listed intervals"), and the private/public call test: about 15 concepts.
  - Go escape: locations, holes, deref weights, 4 location attributes (escapes, persists, mutates, calls), loop depth, closure containment, parameter tags, and 2 size thresholds: about 12.
  - Clang: loans, access paths, origins, 9 fact kinds, `Must`/`Maybe`, persistent vs block-local origins: about 16.
  - Mojo (user-facing): last use, origins, origin unions, untracked/any origins, interior origins, discard-pattern extension: about 6.

  Mojo's model is the smallest for users because the compiler's internal model is hidden. That also makes its two documented silent hazards (an early-released RAII guard, and a use-after-free through an erased origin) *nonlocal*: the failure appears far from the cast that caused it. Basis: derived.
- **Diagnostic legibility.**
  - Go `-m=2` prints the flow path that forced each heap allocation (for example `flow: {heap} ← &x: from s.Size(&x) (call parameter)`), so the reason for every escape can be checked locally.
  - Clang records a causing use or escape fact, and an optional move or invalidation expression, for each warning.
  - CompCert offers no user diagnostic; a store that survives is invisible unless the RTL output is inspected.

  Basis: execution (Go) + source (Clang, CompCert).
- **One invariant, several mechanisms (C2).** The common invariant is: *no access through a possibly-live reference may observe storage that has been reclaimed or repurposed*. The systems enforce it four different ways:
  - by eliminating only provably unobserved writes (CompCert);
  - by moving storage to a longer-lived region (escape analyses);
  - by rejecting programs (Clang warnings, Mojo use-after-destroy errors, FR typing);
  - by extending lifetimes (Mojo origins, Go `KeepAlive`).

  A single abstraction covers all of them: a may-reference map from live references to storage names, plus a per-system *action* on the set of storage that is unreachable from live references. CompCert's `nmem` intervals, Clang's loan sets, and Mojo's origin sets are three granularities of that map. Applying the map uniformly would not remove the conservative cases. It would make explicit that each system's "always live" cases (CompCert's imprecise pointers, Clang's untracked heap and global paths, Mojo's untracked origins, Go's address-taken variables) are exactly the storage the map cannot name. Basis: derived.

### 7. How each mechanism is validated (V1–V4)

- **V1 (specification adequacy).**
  - CompCert's dead-code theorem is stated against the full RTL semantics (`forward_simulation`). The specification is the semantics itself, with no separate neededness specification to validate.
  - Clang ships unit tests (`clang/unittests/Analysis/LifetimeSafetyTest.cpp`, 61,857 bytes at the pinned revision); their content was not examined.
  - Go's repository has 34 `test/escape*.go` files (198,455 bytes) at the pinned revision; their content was not examined.
  - FR was validated by bounded exhaustive model checking (cited).

  Mutation testing of any of these specifications: not examined.
- **V2 (compiler fuzzing).** Pearce reports fuzzing `rustc` with FR as an oracle (cited). Csmith-style differential testing of C compilers is reported in Yang et al., PLDI 2011 (`10.1145/1993498.1993532`); its findings for the CompCert passes examined here were not examined.
- **V3 (concurrency).** Go forces `go`-statement arguments to the heap (source). Clang's analysis is single-function and thread-agnostic (derived). Mojo's design note says interior origins "do not solve cross-task or GPU lifetime problems". Weak-memory or crash validation of any examined analysis: not examined.
- **V4 (human mental models).** Mojo's documentation itself warns about two failure classes that produce no compiler error (documentation). No empirical study of programmers' predictions of destruction points was examined.

## Boundaries

- **Not examined:**
  - the full text of Blanchet (TOPLAS 2003), Choi et al. (both versions), and Stadler et al. (CGO 2014). Their correctness statements, proof structure, and treatment of loops, closures, interfaces and reflection are recorded only as far as their abstracts state them;
  - Graal's partial-escape-analysis source;
  - Blanchet's POPL 1998 functional-language escape analysis (`10.1145/268946.268949`; metadata only);
  - CompCert's `Unusedglob` and its other passes that consume value analysis;
  - Clang's `FactsGenerator.cpp` fact-emission rules in detail;
  - Mojo's compiler implementation, which is not in the pinned repository.
- **Unknown:**
  - whether go1.27.3 and Go HEAD `34c413ad2a85db3857ecfd73d9d6d682e40e30d5` produce identical escape and liveness results for the probes, since the probes were run on the release only;
  - whether the distribution build of go1.27.3 carries patches affecting escape analysis;
  - the run-time cost of any heap promotion observed in the probes.
- **Not measured:** every `not measured` cell in Finding 5, including all analysis-time (L3) and checker-time (L5) figures for CompCert, Clang, Go and Mojo, and every peak-memory figure.
- **Known not to apply:**
  - CompCert's neededness never treats heap storage as dead; heap dead-store elimination is out of its scope;
  - Clang's lifetime safety does not model heap or global access paths (`Loans.h` TODO);
  - Go's escape analysis does not use last-use information (probe E3).
- **Unsupported:**
  - FR does not support non-lexical lifetimes, loops or recursion in its main theorem;
  - Mojo's documentation states that origins cannot protect pointers retained by C code past a call.
- **Stronger conclusions not supported:**
  - That CompCert ships the Robert–Leroy analysis: it ships a different, later value analysis.
  - That Clang's lifetime analysis is sound: no soundness claim exists in the examined files, and the documentation for the `-moved` variants admits false positives.
  - That FR is mechanized: the preprint presents a paper proof and bounded model checking, and describes no proof-assistant development.
  - That Mojo's ASAP destruction is verified: the evidence is documentation of a closed implementation.

## Evidence

Evidence was gathered on 2026-11-20 (UTC).

**Repositories (path, symbol, and line ranges at the pinned revisions):**
- `AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc`:
  - `backend/ValueDomain.v`: `block_class` (line 22), `aptr` (121–129), `poffset` (358–363), provenance comment and `provenance` (770–809), `int_provenance` (828), `amem` (4319), `store` (4383–4407), `ablock_store` (3669–3675), `ablock_store_anywhere` (3677–3678);
  - `backend/ValueAnalysis.v`: `mafter_public_call` (31), `analyze_call` (39–43), `sound_state_base` (1106–1115);
  - `backend/NeedDomain.v`: `nval` (34–38), `vagree` (55), `nmem` (1901–1903), `nlive` (1917), `nmem_all` (1928), `nmem_add` (1940), `nmem_remove` (2025), `nmem_contains` (2077), `nmem_dead_stack` (2118);
  - `backend/Deadcode.v`: `transfer` (Istore 147, unknown `Icall` 156, `Itailcall` 165, `Ireturn` 174), `transf_instr`;
  - `backend/Deadcodeproof.v`: `magree` (40), `match_states` (521–549), `transf_program_correct` (1263);
  - `Changelog.md`: Release 2.2 section (lines 1229–1250).
- `llvm/llvm-project` @ `087db4daf2e284f23f41d70fde3339597ccc9e7d`:
  - `clang/lib/Analysis/LifetimeSafety/LiveOrigins.cpp`: lines 105, 128, 153, 168–170, 176, 182, 199;
  - `Checker.cpp`: lines 36, 301–327;
  - `MovedLoans.cpp`: line 76;
  - `LoanPropagation.cpp`: lines 94, 122;
  - `clang/include/clang/Analysis/Analyses/LifetimeSafety/Loans.h`: lines 75, 126;
  - `Facts.h`: fact kinds (102–125) and `ParamEscapeFact` (330–335);
  - `clang/include/clang/Basic/DiagnosticGroups.td`: lines 568–685;
  - `clang/unittests/Analysis/LifetimeSafetyTest.cpp` (existence and size only).
- `golang/go` @ `34c413ad2a85db3857ecfd73d9d6d682e40e30d5`:
  - `src/cmd/compile/internal/escape/escape.go`: lines 22–88 and 179–183;
  - `solve.go`: `outlives` (368–422);
  - `call.go`: `tagHole` (390–393), `goDeferStmt` (237–246);
  - `utils.go`: `HeapAllocReason` (173–242);
  - `src/cmd/compile/internal/ir/cfg.go`: lines 8–19;
  - `src/cmd/compile/internal/liveness/plive.go`: `shouldTrack` (220–222), `emitStackObjects` (1498–1501);
  - `src/runtime/mgcstack.go`: lines 9–50.
- `golang/go` @ `2aae1000ea1d4b28923b96db28acf4e3b99d6aff` (tag go1.27.3): the executed release.
- `modular/modular` @ `2b2fdf54810989d009a3aa1f186fba49504a91ea`:
  - `Mojo/docs/site/manual/lifecycle/death.mdx`: lines 8–23 and 175–276;
  - `Mojo/docs/site/manual/values/lifetimes.mdx`: lines 10–50 and 128–145;
  - `Mojo/proposals/origin-design.md`: lines 1–125 and 877–905.

**Literature (DOIs verified against Crossref metadata):**
- V. Robert, X. Leroy, "A Formally-Verified Alias Analysis", CPP 2012, LNCS, pp. 11–26, `10.1007/978-3-642-35308-6_5`. Full text read from the authors' PDF.
- B. Blanchet, "Escape analysis for Java™: Theory and practice", ACM TOPLAS 25(6):713–775, 2003, `10.1145/945885.945886`. Abstract only.
- J.-D. Choi, M. Gupta, M. Serrano, V. C. Sreedhar, S. Midkiff, "Escape analysis for Java", OOPSLA 1999, pp. 1–19, `10.1145/320384.320386` (metadata only). Journal version: "Stack allocation and synchronization optimizations for Java using escape analysis", ACM TOPLAS 25(6):876–910, 2003, `10.1145/945885.945892`; abstract only.
- L. Stadler, T. Würthinger, H. Mössenböck, "Partial Escape Analysis and Scalar Replacement for Java", CGO 2014, pp. 165–174, `10.1145/2544137.2544157`. Abstract only.
- D. J. Pearce, "A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust", ACM TOPLAS 43(1):1–73, 2021, `10.1145/3443420`. Crossref abstract, plus the March 2020 preprint from the author's site.
- X. Yang, Y. Chen, E. Eide, J. Regehr, "Finding and understanding bugs in C compilers", PLDI 2011, `10.1145/1993498.1993532` (metadata only).

**Execution (2026-11-20; Linux, Intel Xeon @ 2.60 GHz; go1.27.3 linux/amd64):**
- `support/go_escape`: `go build -gcflags='-m' ./...` gives `escape_m1.txt`, and `go build -gcflags='-m=2 -l' ./...` (filtered to probe lines) gives `escape_m2_noinline.txt`.
- `support/go_live`: `go build -gcflags='-live -l' ./...` gives `live.txt`.
- Line counts were taken with `wc -l` on the pinned raw files. The Coq proof/specification split counts non-blank, non-comment lines between a line starting `Proof` and the next line ending `Qed.`/`Defined.`/`Admitted.` as proof; all other such lines count as specification.

## Revalidation

- **CompCert:** diff `backend/NeedDomain.v` (`nmem_add`, `nmem_remove`, `nmem_contains`), `backend/Deadcode.v` (`transfer`), and `backend/ValueAnalysis.v` (`analyze_call`) against the pinned revision. If the `_ => true (**r conservative answer *)` and `_ => nmem_all` cases and the unknown-`Icall` `nmem_all` rule are unchanged, Findings 1.3–1.6 hold. Recheck that `transf_program_correct` still states `forward_simulation` and that `match_states` still uses `magree ... nlive`.
- **Go:** rerun the two commands in `support/README.txt` with the target toolchain and diff against the stored outputs. A changed E3 line (`new(int) escapes to heap`) would indicate a move away from scope-based outlives. Diff `solve.go` `outlives` and `plive.go` `shouldTrack`/`emitStackObjects`.
- **Clang:** grep `Loans.h` for the heap/globals TODO, and `LiveOrigins.cpp` for the `ParamEscapeFact` early return and the `Must`/`Maybe` join. Diff `DiagnosticGroups.td` lines 568–685 for group membership.
- **Mojo:** reread `death.mdx` "Keeping a value alive" and `origin-design.md` "Cautions and limitations", and check the `Compiler verified` stamp. Any claim about compiler behavior requires running a Mojo toolchain, which this report did not do.
- **Papers:** published papers do not change. To extend the escape-analysis comparison, read the full texts listed under Boundaries.
