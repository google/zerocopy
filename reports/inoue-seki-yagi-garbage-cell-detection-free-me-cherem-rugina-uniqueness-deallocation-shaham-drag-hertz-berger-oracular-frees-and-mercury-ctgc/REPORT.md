# Static Release of Individual Heap Objects: Garbage-Cell Detection, Compile-Time Reuse, Verified Frees, and Measuring the Gap to Ideal Release

## Summary

- **Three reference points bound every static release decision.** An object can be released no earlier than its **last use** (liveness), no later than the moment it becomes **unreachable** (the last instant a program can still name it in a `free`), and, for stack, region or scope-based schemes, at **scope or frame exit**. *Drag* is the time from last use to actual release. It splits into a program-dependent part (last use to unreachability) and a collector-dependent part (unreachability to collection). Studies that report a "gap to ideal" differ mainly in which of these points they call ideal and in whether they measure **peak** heap or the **space-time integral**.
- **What the measurements say.** An oracular study of Java (Hertz and Berger, OOPSLA 2005) found little difference between liveness-based and reachability-based explicit freeing: liveness reduced heap footprint by at most 15% and runtime was similar. Against reachability-based freeing, a generational collector needed about 5× the memory to match its speed. It ran on average 17% slower at 3× and nearly 70% slower at 2×. Earlier dynamic measurements by Shaham, Kolodner and Sagiv put the potential saving at 15% on average from nulling each heap reference after its last use, and 39% given complete information about future use.
- **Static analyses recover part of that gap, with very different safety evidence:**
  - Inoue, Seki and Yagi (1988) detect garbage cells in first-order list programs using formal languages and state *sufficient conditions*.
  - Mercury's compile-time garbage collection (CTGC) turns structure-sharing plus liveness facts into dead-cell detection at deconstructions and reuse at constructions. It records *reuse conditions* that are re-checked at call sites. At the pinned revision it is experimental, off by default, and switched off for the Java and C# back ends.
  - Shaham, Yahav, Kolodner and Sagiv (SAS 2003) *verify* each proposed `free` with per-object heap-safety automata over a shape analysis. The examples were small; the largest manually sliced JavaCard program took about 56 MB and about 980 s on a 900 MHz Pentium III.
  - Go now ships a production analogue behind the `runtimefreegc` experiment. A conservative, pattern-based alias analysis proves that certain `append` targets are unaliased, and the runtime then frees the old backing array, under a contract that the pointer is "the last and only pointer to its referent".
- **Measured here** (Go at the pinned revision, rebuilt with `GOEXPERIMENT=runtimefreegc`; 5 runs per configuration): compiler-inserted frees in an append-growth microbenchmark cut `runtime.MemStats.Mallocs` from 1,800,144 to 208,485 (medians), `TotalAlloc` from 4,797 MiB to 1,965 MiB, and GC cycles from 1,595 to 637. Wall-clock differences could not be attributed because host noise was large: an unaffected control varied 2–3× between runs.
- **What is not established.** No examined system mechanizes the safety proof of its inserted frees end to end. The quantitative results of Free-Me and of the two Cherem–Rugina papers were not examined in full text (see **Boundaries**).

## Applicability

Subjects and their roles:

| Subject (see `REPORT.json`) | Role in this report | How examined |
|---|---|---|
| Mercury compiler, `Mercury-Language/mercury` at the pinned revision | Compile-time garbage collection and structure reuse in a logic/functional language | Source reading of `compiler/ctgc*.m`, `structure_reuse*.m`, `structure_sharing*.m`, `options.m`, `handle_options.m`, `mercury_compile_middle_passes.m`. Not built or run. |
| Go toolchain, `golang/go` at the pinned revision | Production escape analysis; compiler-inserted `freegc` of `append` backing arrays (`runtimefreegc` experiment) | Source reading. Built from source with `GOEXPERIMENT=runtimefreegc`, and two micro-probes executed. |
| GHC user's guide, `ghc/ghc` GitHub mirror at the pinned revision | Production definition of lag/use/drag/void heap biographies | Documentation reading |
| Inoue–Seki–Yagi 1988; Mazur et al. 2001; Shaham–Yahav–Kolodner–Sagiv 2003; Hertz–Berger 2005; Röjemo–Runciman 1996; Shaham–Kolodner–Sagiv 2000 and 2002; Karkare–Sanyal–Khedker (arXiv cs/0611093) | Analyses, safety arguments, and measurements of the gap to ideal release | Metadata for every DOI checked against Crossref. Full text read: SAS 2003, OOPSLA 2005, arXiv cs/0611093. Inoue et al. and Mazur et al.: abstracts only. |
| Free-Me (PLDI 2006); Cherem–Rugina (ISMM 2006, ISMM 2007) | Individual-object reclamation in a managed language | Metadata verified. Free-Me: abstract figures only, via a web index. Cherem–Rugina: no text examined. |

The subjects are compared, not combined. The Mercury and Go source findings hold only at the pinned revisions. The Go execution results hold for that revision built with the experiment on, on one host: 96-vCPU Intel Xeon @ 2.60 GHz Linux x86-64 VM, 236 GiB RAM, `GOMAXPROCS=4` for the benchmark. Paper results are the authors' measurements on their own platforms (Jikes RVM/SimpleScalar, TVLA on Windows 2000, MIT/GNU Scheme). They are reported as cited, not reproduced. Findings about the shape of a measurement (which reference point, peak vs. integral) are derived and platform-independent. Numbers are not transferable.

## Findings

### F1. Reference points, drag, and what each study calls "ideal"

Basis: documentation (GHC user's guide) + source (paper texts) + derived

The GHC user's guide (`docs/users_guide/profiling.rst`, "Biographical Profiling") defines four states: the **lag** stage runs from creation to first use; **use** runs from first use to last use; **drag** runs "from the final use until the last reference to the object is dropped"; and an object never used is **void**. Its `-hb` heap profile reports "the portion of the live heap in each of the four states". Karkare, Sanyal and Khedker (arXiv cs/0611093, §I-B) split drag as δ = δ_rch + δ_gc: δ_rch runs from last use to unreachability and "depends upon the program but is independent of the garbage collector"; δ_gc runs from unreachability to collection and "depends heavily upon the garbage collector". They also note that for reference counting δ_gc = 0 (ignoring cycles).

| Release point | Who uses it as the reference | Implementable statically? |
|---|---|---|
| Last use (liveness) | Hertz–Berger "lifetime/liveness-based oracle": "free objects after their last use — the earliest time they can safely be freed"; SAS 2003 free property restricted to uses at `pt` | Only with future-use information; the SAS 2003 analysis approximates it |
| Unreachability | Hertz–Berger "reachability-based oracle": "the last moment a program could call free"; Merlin trace algorithm | Reference counting reaches it dynamically. Static placement needs sharing information. |
| Scope/frame exit | Go escape analysis (stack allocation); region inference | Yes, by construction, but it holds values beyond their last use |
| Next collection after unreachability | Any tracing collector (δ_gc > 0) | Not a static decision |

Hertz–Berger (§3.1) note that the liveness oracle also frees some objects the reachability oracle never frees. These are objects that stay reachable but "plausibly could be deallocated by a knowledgeable programmer". Only pseudoJBB (3.8%) and `_201_compress` (4.4%) freed more than 0.8% more objects that way.

**Peak and integral measure different things** (derived, illustrated by a toy model in support material). In the toy trace "build an n-node list, traverse it once, hold the head until scope exit" (n = 1000, 32-byte nodes), liveness-based release cuts retained byte-ticks from 112,016,000 to 32,000,000. Peak bytes stay at 32,000 under every policy, because all nodes are live together before the traversal starts. A study that reports heap-size multiples (Hertz–Berger) can therefore show a smaller gap than a study that reports drag or space-time (Shaham et al., Karkare et al.) for the same program. `Basis: execution (toy model written for this report, not a measurement of any runtime)`.

### F2. Inoue–Seki–Yagi: garbage-cell detection from formal languages

Basis: documentation (publisher abstract via Crossref) + source (characterization in SAS 2003)

The abstract (TOPLAS 10(4):555–578, 1988) describes the problem as follows: for a subexpression *F(G(…))* where both functions return lists, "if a cell *c* is created during the computation of *G* and if *c* does not appear in a list-type value of *F*, then *c* becomes a garbage cell at the end of the computation of *F*." The analysis is posed "on the basis of formal languages derived from the functional program text". It gives "some sufficient conditions that predict the generation of garbage cells", plus "an efficient algorithm to detect at compile time the generation of garbage cells which are linearly linked". The authors implemented it in an experimental LISP system and conclude from sample programs that the method "is effective". The abstract gives no numbers.

Placement point: the end of *F*'s computation, a boundary in the composition. Safety evidence: sufficient conditions, so the analysis is conservative by construction; whether the paper contains a full soundness proof was not examined. SAS 2003 (§1.2–1.3) uses this work as its example of "reachability based compile-time garbage collection mechanisms … which only consider the history". It notes that such techniques will not free a traversed list element that is still reachable from the list head.

### F3. Mercury CTGC at the pinned revision

Basis: source

**Pipeline** (`compiler/mercury_compile_middle_passes.m`: `maybe_structure_sharing_analysis_pass`, then `maybe_structure_reuse_analysis_pass`, each followed by an HLDS dump stage). `handle_options.m:2049` makes `structure_reuse_analysis` imply `structure_sharing_analysis`. `structure_reuse.analysis.m:17` splits reuse into "the direct reuse analysis", "the indirect analysis", and "the generation of the optimised procedures". Lines 24–45 illustrate this with `list.append/3`:
- the deconstruction `H1 => [X | Xs]` produces a cell that "dies provided some condition about the structure sharing of H1 is true";
- the construction `H3 <= [X | Zs]` reuses it, which is a *direct* reuse;
- the recursive call may target the reuse version, which imposes "a new condition to be met by the headvars of any call", an *indirect* reuse.

**Dead-cell test** (`structure_reuse.direct_detect_garbage.m`, `unification_verify_reuse`, lines ≈277–305). A deconstruction `deconstruct(Var, ConsId, …)` yields a reusable cell only when all of the following hold:
- the constructor has nonzero arity (line 284);
- the type is not a no-tag type;
- the sharing at that point is not ⊤ (`not sharing_as_is_top(Sharing)`, line 297; "If Sharing is top, then everything should automatically be considered live");
- `var_not_live(…)` (line 300) holds, i.e. live-data analysis derived from local forward use (LFU), local backward use (LBU) and sharing finds no live node.

The cell table entry records a `reuse_condition` built from those facts. Generic calls with unknown sharing force ⊤ (`top_cannot_improve("generic call …")`).

**Conditions and lattice** (`structure_reuse.domain.m`). `reuse_condition` (line 296) has two constructors:
- `always`;
- `condition(reuseable_nodes, local_use_headvars, local_sharing_headvars)`, meaning the reuse is valid only if, at the call site, the head-variable data structures are dead and share as described.

Procedure summaries form `no_reuse < unconditional < conditional(list(reuse_condition))` (lines 315–326). Conditional reuse is the mechanism that keeps the analysis modular. Callers check the condition and choose between the original and the reuse version of a procedure (`structure_reuse.versions.m`). For `pragma external` predicates an entry is still added so that "something will be written out to optimisation interface files" (`structure_reuse.direct.m:109`). Cross-module reuse information therefore travels through interface files rather than requiring whole-program compilation.

**Status and limits at the pinned revision** (source):
- The options are grouped under "XXX All the help text for these experimental options should be private" (`options.m:3846`) and default to off:
  - `--structure-reuse` (alias `--ctgc`) and `--structure-sharing` default to `bool(no)`;
  - `--structure-reuse-constraint` defaults to `within_n_cells_difference` with threshold 0 (reuse only for equal arity);
  - `--structure-reuse-max-conditions` is a "soft limit" defaulting to 10.
- `--structure-reuse-free-cells` ("Immediately free cells which are known to be dead but which cannot be reused") carries the comment "This option is likely to break many optimisations which haven't been updated" (`options.m:3889`).
- Enabling reuse disables `reclaim_heap_on_semidet_failure`, because "The code of interval.m … throws an exception if given a unification whose HowToConstruct field contains either reuse_cell" (`handle_options.m:727`).
- For the Java and C# targets, reuse and sharing analysis are forced off "Because mlds_to_java_stmt.m does not handle assign_if_in_heap" (`handle_options.m:1060`, with the option resets at :1083–1084).

**Reported recovery.** The Mazur, Ross, Janssens and Bruynooghe abstract (ICLP 2001) describes "a working and well performing near-to-ship CTGC-system built into the Melbourne Mercury Compiler", with "substantial memory savings and a noticeable reduction in execution time". The abstract gives no figures, and the full text was not examined. No measurement was run here, because the Mercury compiler was not built.

### F4. Verifying inserted frees with local temporal heap-safety automata (SAS 2003)

Basis: source (full text of the authors' copy)

**Property.** A *heap safety automaton* (HSA) is "a deterministic finite state automaton" over events for a single object. The analysis "verif[ies] that on all execution paths, all objects are in an HSA accepting state". Under **Free Property (pt, x)**, the object referenced by `x` at `pt` is not used after `pt`, so `free x` may be inserted "immediately after pt". The **assign-null** property is the analogous statement for a heap reference. Both use forward history and backward future information. Restricting `x` to variables used at `pt` yields frees "exactly at the earliest time possible" and "exactly once" (§5).

**Method.** Java `.class` files are translated to TVLA through a Soot front end. Lists use spatial instrumentation predicates (sharing, reachability, cyclicity); other programs use allocation-site abstraction; interprocedural information is computed. Several properties can be verified at once by keeping several automaton states per object.

**Cost** (Table 3; 900 MHz Pentium III, 512 MB, Windows 2000; space in MB, time in seconds):

| Program | Free: MB / s | Assign-null: MB / s |
|---|---|---|
| Loop (running example) | 1.71 / 1.93 | 1.37 / 1.76 |
| CReverse | 3.03 / 5.17 | 2.58 / 4.79 |
| Delete | 5.33 / 19.66 | 4.21 / 13.84 |
| DLoop | 2.09 / 2.91 | 1.75 / 2.68 |
| DPairs | 2.76 / 5.01 | 2.54 / 4.86 |
| small javac (parser emulation) | N/A | 16.02 / 43.84 |
| JavaPurse' slice | 56.3 / 979 | 56.15 / 991 |
| GuessNumber' slice | 9.99 / 17.3 | N/A |

**Limitations stated by the authors:**
- "Our benchmarks programs were used as a proof of concept, thus we did not measure the total savings obtained by our analysis."
- "for scalability reasons we analyze slices of rewritten JavaCard programs. Our current implementation does not include a slicer, thus we manually slice the code."

**Contrast with escape analysis** (§7): stack allocation "is limited to objects that do not escape their allocating method", whereas the free analysis applies "to all program objects, and allows freeing objects before their allocating method returns".

### F5. Individual-object reclamation in managed runtimes

Basis: documentation (abstract figures) for Free-Me; source + execution for Go; nothing examined for Cherem–Rugina beyond metadata

- **Free-Me** (Guyer, McKinley, Frampton; PLDI 2006, pp. 364–375). Abstract figures retrieved through a web index (full text not examined): compared with mark-sweep alone, compiler-inserted frees cut "total time by 22% on average, collector time by 50% to 70%", and let programs run "in 17% less memory". The mechanism, benchmark set, fraction of objects freed, and causes of missed opportunities were not verified from the paper. Treat any further characterization as unexamined.
- **Cherem–Rugina** (ISMM 2006, pp. 138–149, "Compile-time deallocation of individual objects"; ISMM 2007, pp. 117–128, "Uniqueness inference for compile-time object deallocation"). Only the titles, venues and pages were verified (Crossref). Their analyses, benchmarks and recovery figures are **not examined** here.
- **Go `runtimefreegc` (production analogue at the pinned revision).**
  - **Contract.** `src/runtime/malloc.go` lines 1824–1864 document `freegc`: "freegc must be called by the effective owner of ptr who knows the pointer is logically dead, with no possible aliases that might be used past that moment. In other words, ptr must be the last and only pointer to its referent." The comment continues: "The intended caller is the compiler", and "please do not send changes that attempt to add freegc calls to the standard library". It is a no-op below 16 bytes or above 32 KiB minus the malloc header, requires that the object have no specials (finalizers or cleanups), and "currently throws if noscan is false". The runtime enables it only when the experiment is on and no memory sanitizer is active (`runtimeFreegcEnabled`, line 1003).
  - **Producer.** `src/cmd/compile/internal/escape/alias.go` (lines 51–57): `aliasAnalysis` "looks for specific patterns of slice usage and proves that certain appends are operating on non-aliased slices… The analysis is conservative, giving up on any operation we do not explicitly understand." It recognizes `var s []T`, `s := make(...)` and `s := []T{...}` declarations followed by `s = append(s, ...)`. It treats other uses as potential aliasing, and it postpones decisions about appends inside loops until control returns to the declaring loop depth. Proven appends set `call.AppendNoAlias` when `-d=freeappend` is nonzero, which is the default (`base/flag.go:188`, `Debug.FreeAppend = 1`). `escape.go:528` runs the pass only `if goexperiment.RuntimeFreegc`, a constant baked into the toolchain build. Setting `GOEXPERIMENT` when using a toolchain built without it therefore has no effect, which was observed with an installed go1.27.3: no alias diagnostics.
  - **Consumer.** `src/runtime/slice.go:303–323`: `growsliceNoAlias` calls `growslice` and then, if the old pointer is not on the current stack and differs from the new array, calls `freegc(oldPtr, oldCap*elemsize, noscan)`.
  - **Measured effect** (execution; pinned revision built by `make.bash` with `GOEXPERIMENT=runtimefreegc`; version string `go1.28-devel_d7fbd868 … X:runtimefreegc`). The probe `esc.go` (support material) appends 1,000 `int`s to a fresh slice, 200,000 times. `build` is the unaliased pattern; `buildAliased` adds `keep = s` inside the loop. The two binaries differ only in `-gcflags=-d=freeappend=0`. Disassembly confirms the difference: `main.build` calls `runtime.growsliceNoAlias` in the default binary and `runtime.growslice` with `freeappend=0`; `main.buildAliased` calls `runtime.growslice` in both. `-d=escapealias=1` reports exactly one proven append (`esc.go:33`, in `build`).

| Configuration (median of 5) | Mallocs | TotalAlloc MiB | GC cycles | GC pause ms | Wall ms (min–max) |
|---|---|---|---|---|---|
| `build`, freeappend on | 208,485 | 1,965.2 | 637 | 44.6 | 685 (604–1,422) |
| `build`, freeappend off | 1,800,144 | 4,797.4 | 1,595 | 109.3 | 1,346 (1,113–2,837) |
| `buildAliased`, on (control) | 2,400,125 | 4,808.1 | 1,402 | 104.1 | 1,756 (1,194–2,785) |
| `buildAliased`, off (control) | 2,400,139 | 4,808.1 | 1,408 | 179.4 | 2,942 (1,261–3,535) |

Derived: Mallocs fall 88.4% (208,485/1,800,144 = 0.116), TotalAlloc falls 59.0%, and GC cycles fall 60.1%. The control rows run identical code in both binaries, yet their wall times differ 1.7× at the median. Wall-clock effects are therefore **not attributable** at this sample size. How `MemStats` accounts for a reused freed object, and hence how to interpret the counter drop, was not examined. `Basis: execution (real toolchain, microbenchmark; not representative of application workloads)`.

### F6. Production escape analysis as static release at frame exit (Go)

Basis: source + execution

`escape.go:24–31` states the two invariants: "(1) pointers to stack objects cannot be stored in the heap, and (2) pointers to a stack object cannot outlive that object (e.g., because the declaring function returned and destroyed the object's stack frame, or its space is reused across loop iterations for logically distinct variables)." The analysis builds a weighted location graph where the edge weight is "derefs", the number of dereferences minus address-of operations (`p = &q` → −1). Constructs are lowered "generally without sensitivity to flow, path, or context; and without distinguishing elements within a compound variable" (lines 72–88).

Interprocedural precision comes from **parameter tags**, summaries of flows from parameters to the heap and to results, "used at static call sites" (lines 44–48) and recorded "for package export data" (line 443). `HeapAllocReason` (`utils.go:171ff.`) forces heap allocation above `ir.MaxStackVarSize` and, for implicit allocations (`new`, `&T{}`, closures, method values, `make`), above `ir.MaxImplicitStackVarSize`.

Probe (`go build -gcflags=-m` on `esc.go`, installed go1.27.3):
- `&T{...} does not escape` for a local that is only read (line 17);
- `escapes to heap` when the pointer is stored in a global (line 20) or returned (line 23);
- `t escapes to heap` when a value is converted to `any` and stored globally (line 26);
- `append escapes to heap` for both builders (the slice is returned).

### F7. Correctness evidence by system

Basis: derived from F2–F6

| System | What is released | Where | Safety evidence | Recovery evidence |
|---|---|---|---|---|
| Inoue–Seki–Yagi | Linearly linked list cells produced inside *G* and absent from *F*'s result | End of *F* in *F(G(…))* | Sufficient conditions over derived formal languages (abstract) | Qualitative ("effective"), experimental LISP |
| Mercury CTGC | Top cell of a deconstructed term | Reused at a later construction in the same procedure, or via a reuse version for callers meeting conditions | Argued in the analysis design. Conditions re-checked at call sites. No mechanized proof examined. | Abstract claims only (not examined) |
| SAS 2003 free/assign-null | Any object for which the HSA property is verified | After `pt` | Per-instance verification by abstract interpretation (sound with respect to the embedding theorem) | Not measured by the authors |
| Free-Me | Objects judged dead by the analysis | Inserted `free` | Not examined | Abstract: −22% total time, −50–70% GC time, −17% memory |
| Go `runtimefreegc` | Old `append` backing arrays, noscan, 16 B – 32 KiB | Inside `growsliceNoAlias` | Conservative syntactic alias analysis plus runtime preconditions (stack check, size, specials, noscan) | Measured here (F5) |
| Go escape analysis | Whole objects proven not to outlive the frame | Frame exit (stack) | Documented invariants plus a flow-insensitive graph analysis | `-m` diagnostics only (no space measurement here) |

### F8. Inputs: computable per module vs. requiring whole-program information

Basis: source (Mercury, Go) + derived

| Analysis input | Mercury CTGC | Go escape / alias | SAS 2003 |
|---|---|---|---|
| Intraprocedural liveness (LFU/LBU, last use) | Per procedure | Per function | Per program point; needs future information across calls |
| Callee effects | Sharing and reuse summaries in optimization interface files | Parameter tags in export data | Interprocedural TVLA (whole program or slice) |
| Unknown or higher-order callees | Sharing set to ⊤ ("generic call") → no reuse | Conservative flows to the heap | Not examined |
| Caller context needed? | Yes. Conditional reuse is discharged at call sites by choosing a reuse version. | No for stack allocation (frame-local). The alias pattern is intraprocedural. | Yes (heap paths) |

Derived: per-module passes can compute liveness and summaries. A *precise* "dead after this point" fact for heap-reachable objects needs either caller-side discharge of conditions (Mercury), or whole-program or sliced shape analysis (SAS 2003).

### F9. Six-level performance and resource footprint

| Level | Mercury CTGC | Go (escape + `runtimefreegc`) | SAS 2003 TVLA | Oracular / drag studies |
|---|---|---|---|---|
| L1 authoring/maintenance | not measured | not measured. The 2025-dated `alias.go` is 528 lines (wc). | not measured | not measured |
| L2 toolchain build | not measured | `make.bash` with the experiment: 57.14 s wall, 918 s user, max RSS 438,636 KB (measured, 96-vCPU host) | not measured | not applicable |
| L3 analysis latency | not measured | not measured (build of the probe package was interactive, untimed) | 1.93 s – 991 s per property set (cited, Table 3) | Oracle generation off-line (Hertz–Berger); time not measured here |
| L4 generated code | "noticeable reduction in execution time" (abstract, no figure) | Mallocs −88%, GC cycles −60%; wall time not attributable (measured, F5) | not measured (proof of concept) | GC vs. explicit: equal at 5× heap; +17% at 3×; ≈+70% at 2× (cited) |
| L5 certificate check | not applicable (no certificates) | not applicable | not applicable | not applicable |
| L6 memory/footprint | "substantial memory savings" (abstract, no figure) | TotalAlloc −59% in the probe (measured) | 1.37–56.3 MB analysis memory (cited) | Liveness vs. reachability: ≤15% footprint (cited); 15% and 39% potential savings (cited, Shaham et al. 2002) |

Hertz–Berger also fit GenMS execution time as `a/(b − h²) + c`, where `h` is the heap-size multiple, with a = −0.246, b = 0.59, c = 0.942 and RMS error 0.0024 (cited, §5.1). They report that "explicit memory management does not depend on heap size, and is linear in the number of objects allocated".

### F10. Comprehensibility (C1) and conceptual simplicity (C2)

Basis: derived

- **C1, local vs. non-local reasoning.**
  - Go's `freegc` contract is a one-sentence *local* obligation ("last and only pointer"). The producing analysis is a short list of syntactic patterns, and an unmatched use simply disables the optimization. The `-d=escapealias=1..4` diagnostics show which appends were proven.
  - Mercury's conditional reuse is non-local by design: a reuse in `append` is valid only under conditions on callers' head variables, which appear in optimization interface files rather than in the source. A human must reason about sharing across module boundaries to understand why a reuse version was or was not chosen.
  - SAS 2003 makes the obligation explicit as an automaton per property, which is auditable. A failed verification, however, is an abstract structure with a non-accepting state, not a source-level counterexample.
- **C2, one invariant, several mechanisms.**
  - Every system enforces the same invariant: no access after release. They differ in where they discharge it: at frame exit, at a deconstruction/construction pair, at an arbitrary point after verification, or at an `append` growth.
  - Drag decomposition shows that "distance from ideal" has two orthogonal parts. δ_rch belongs to the program and to static analysis; δ_gc belongs to the collector. Studies that mix them (for example, by comparing against a collector at one heap size) conflate analysis quality with collector tuning.
  - A minimal common abstraction is a per-object last-use event plus a release event. All oracles and policies in F1 are choices of release event, which the toy model in support material encodes in about 80 lines.

### F11. Validation of the analyses and their implementations (V1–V4)

Basis: derived + source

- **V1, specification adequacy.**
  - SAS 2003 restricts free properties to "used at pt" to make them non-vacuous and earliest; the paper does not test the properties against mutants.
  - Go's `alias.go` has an optional self-check (`-d=escapealiascheck`) that counts node visits against a simple walk "to help catch missing any nodes squirreled away in some spot we forgot to examine". This is a completeness check of the traversal, not of soundness.
  - The tree also carries `test/escape_alias.go` and the asm-check test `test/codegen/append_freegc.go`. The latter (`//go:build goexperiment.runtimefreegc`) asserts that `growsliceNoAlias` is emitted for `Append1` and plain `growslice` for named-result variants.
- **V2, differential testing of the lowering.** No differential or metamorphic testing of inserted frees was found in the examined sources or papers. Hertz–Berger validated the simulator with a "live" oracular manager on real hardware. They found its distortion "unacceptably large and erratic" (12–33% runtime increase with a null oracle on `_228_jack`) but its trends consistent with the simulation.
- **V3, concurrency and crash.** `freegc` throws if called "during signal", without a P, or on a deadlock condition, and is disabled under ASan, MSan and Valgrind. Behaviour under the race detector is allowed (`malloc.go:997–1003`). Weak-memory or interleaving validation of the free path was not examined.
- **V4, field and comprehension validation.** No study examined here tests whether programmers predict where frees or reuse are inserted.

## Boundaries

- **Not examined:**
  - full texts of Free-Me, Cherem–Rugina 2006 and 2007, Inoue–Seki–Yagi 1988, Mazur et al. 2001, Shaham–Kolodner–Sagiv 2000 and 2002, Röjemo–Runciman 1996, and Lee–Yang–Yi (SCP 2005, "Static insertion of safe and effective memory reuse commands into ML-like programs", DOI 10.1016/j.scico.2005.02.007, metadata only). The ACM and Elsevier full texts were not accessible to this investigation;
  - fraction of objects freed, effect on collection time, and causes of missed opportunities for Free-Me and Cherem–Rugina: **unknown** from this evidence;
  - Mercury CTGC execution (the compiler was not built), so allocations and reuses with and without `--structure-reuse` are **not measured**;
  - HotSpot C2 escape analysis, Graal partial escape analysis, and region-based systems.
- **Unknown:**
  - whether Mercury's reuse analysis has a published soundness proof covering the current implementation. The code comments mark divergences from an earlier "reuse-branch implementation" (`XXX Different implementation from the reuse-branch implementation`, `structure_reuse.direct_detect_garbage.m:271`);
  - how `runtime.MemStats.Mallocs` and `TotalAlloc` count allocations satisfied from `freegc`-recorded objects. The counter drop in F5 may partly reflect accounting rather than allocator work avoided;
  - why `buildAliased` records about 12 mallocs per call and `build` (with frees off) about 9. One possibility is stack-backed small appends moved to the heap at return (both binaries call `runtime.moveSliceNoCapNoScan` in `main.build`); this is unverified.
- **Known not to apply:**
  - the Go probe's 88% malloc reduction to programs whose appends alias, escape inside loops, use pointerful element types (`freegc` "currently throws if noscan is false", and the compiler path is limited accordingly), or exceed 32 KiB per backing array;
  - Hertz–Berger's heap-multiple results to multithreaded allocators, smart-pointer reference counting, or custom allocation, which the authors discuss qualitatively (§3.3–3.6) rather than measure.
- **Unsupported:** Mercury structure reuse with the Java or C# back ends (forced off in `handle_options.m`). `--structure-reuse-free-cells` is flagged by its own source as likely to break other optimizations.
- **Attractive but unsupported conclusions:**
  - "Static release reaches the liveness oracle": no examined system demonstrates this beyond small verified examples (SAS 2003) or narrow patterns (Go).
  - "The 15% liveness-vs-reachability footprint gap bounds what static analysis can win": that figure compares two *oracles*, not an analysis against an oracle, and is peak-footprint-based (see F1).
  - Wall-clock speedups from the Go probe: not established (see F5 control rows).

## Evidence

Observation date: all evidence was gathered on 2026-11-21 (UTC).

**Pinned source (GitHub, read via raw file access at the exact commit):**
- `Mercury-Language/mercury@305d2b1bafebc99247340f2ac3d0e300e516bd2e`:
  - `compiler/ctgc.m`, `structure_reuse.m`, `structure_sharing.m` (package structure);
  - `compiler/structure_reuse.analysis.m:17–45` (phases; `append` example);
  - `compiler/structure_reuse.direct_detect_garbage.m:267–330` (`unification_verify_reuse`, `var_not_live`);
  - `compiler/structure_reuse.domain.m:296–326` (`reuse_condition`, `reuse_as`);
  - `compiler/structure_reuse.direct.m:102–112`;
  - `compiler/options.m:3846–3893`;
  - `compiler/handle_options.m:720–735, 1060, 1083–1084, 2049`;
  - `compiler/mercury_compile_middle_passes.m:253–260, 1288–1326`.
- `golang/go@d7fbd868e418c3766423fcb8ffb12655c5c5d58d`:
  - `src/cmd/compile/internal/escape/escape.go:22–88, 443, 528–534`;
  - `src/cmd/compile/internal/escape/alias.go:16–193`;
  - `src/cmd/compile/internal/escape/utils.go:171–240`;
  - `src/cmd/compile/internal/base/debug.go:38–43`;
  - `src/cmd/compile/internal/base/flag.go:188`;
  - `src/internal/goexperiment/flags.go:116–117`;
  - `src/runtime/malloc.go:997–1003, 1810–1870`;
  - `src/runtime/slice.go:300–323`;
  - `test/codegen/append_freegc.go`.
- `ghc/ghc@83038fbee5efea8e3ebd5090b2ff5537462e169d` (GitHub mirror of GHC): `docs/users_guide/profiling.rst:972–976, 1199–1242`.

**Literature** (DOIs verified against Crossref metadata: title, authors, venue, year and pages):
- Inoue, Seki, Yagi, TOPLAS 10(4):555–578, 1988, DOI 10.1145/48022.48025 (the abstract quoted is Crossref's publisher abstract).
- Röjemo, Runciman, ICFP 1996, pp. 34–41, DOI 10.1145/232627.232633.
- Shaham, Kolodner, Sagiv, ISMM 2000, pp. 12–17, DOI 10.1145/362422.362430.
- Mazur, Ross, Janssens, Bruynooghe, ICLP 2001 (LNCS), pp. 105–119, DOI 10.1007/3-540-45635-X_15 (abstract via Semantic Scholar).
- Shaham, Kolodner, Sagiv, ISMM 2002, pp. 64–75, DOI 10.1145/512429.512437.
- Shaham, Yahav, Kolodner, Sagiv, SAS 2003 (LNCS), pp. 483–503, DOI 10.1007/3-540-44898-5_27 (full text: authors' copy).
- Hertz, Berger, OOPSLA 2005, pp. 313–326, DOI 10.1145/1094811.1094836 (full text: authors' copy).
- Guyer, McKinley, Frampton, PLDI 2006, pp. 364–375, DOI 10.1145/1133981.1134024.
- Cherem, Rugina, ISMM 2006, pp. 138–149, DOI 10.1145/1133956.1133975.
- Cherem, Rugina, ISMM 2007, pp. 117–128, DOI 10.1145/1296907.1296923.
- Karkare, Sanyal, Khedker, "Effectiveness of Garbage Collection in MIT/GNU Scheme", arXiv:cs/0611093 (v2, 2007; arXiv record checked).

**Execution** (Linux x86-64, 96 vCPU Intel Xeon @ 2.60 GHz, 236 GiB RAM):
1. Toolchain:
   ```
   git fetch --depth 1 https://github.com/golang/go d7fbd868e418c3766423fcb8ffb12655c5c5d58d
   cd src && GOROOT_BOOTSTRAP=/usr/lib/go-1.27 GOEXPERIMENT=runtimefreegc ./make.bash
   ```
   `go version` → `go1.28-devel_d7fbd868 … X:runtimefreegc linux/amd64`.
2. Build the two probe binaries:
   ```
   go build -gcflags='-d=escapealias=1,freeappend=2' -o esc_free .
   go build -gcflags='-d=freeappend=0' -o esc_nofree .
   ```
   The first prints `./esc.go:33:13: alias analysis: append using non-aliased slice: append(s, i) in func build`.
3. Disassembly: `go tool objdump -s 'main\.build$' <bin>` shows `growsliceNoAlias` vs. `growslice`.
4. Benchmark: `GOMAXPROCS=4 ./<bin> {build|aliased} 200000`, 5 rounds interleaved. The raw output is in `support/go-freegc/ab_results.txt`.
5. Escape diagnostics: `go build -gcflags=-m` with the installed `go1.27.3` (Debian package `/usr/lib/go-1.27`).
6. Toy model: `python3 support/release-policy-toy/release_policy_toy.py` (output in `out.txt`).

Support material: `support/go-freegc/{esc.go,go.mod,ab_results.txt}` and `support/release-policy-toy/{release_policy_toy.py,out.txt}`.

## Revalidation

1. **Go contract and producer:**
   ```
   git diff d7fbd868e418c3766423fcb8ffb12655c5c5d58d <new> -- src/runtime/malloc.go src/runtime/slice.go src/cmd/compile/internal/escape/alias.go src/cmd/compile/internal/base/flag.go
   ```
   Check that `freegc` still says "last and only pointer", that the size and noscan limits are unchanged, and that `Debug.FreeAppend` still defaults to 1.
2. **Go effect:** rebuild with `GOEXPERIMENT=runtimefreegc` and rerun `support/go-freegc/esc.go`. The discriminating checks are:
   - `objdump` shows `growsliceNoAlias` in `main.build` only;
   - `Mallocs` in `build` mode differs by a large factor between `freeappend` on and off, while the `aliased` rows match.
   
   For wall time, use `perf stat` with pinned CPUs and at least 20 runs before claiming any speedup.
3. **Mercury status:** in a newer tree, grep `options.m` for `structure_reuse_analysis, *bool(` (the default), and `handle_options.m` for `structure_reuse_analysis, bool(no)` (target disables). Re-read `unification_verify_reuse` for the dead-cell conditions.
4. **Measuring a gap:** reuse the release-event abstraction of the toy model. For a real system, log per-object allocation, last use, unreachability (Merlin-style), and actual free. Report **both** peak and byte-time integrals, and separate δ_rch from δ_gc.
5. **Unexamined papers:** reading the Free-Me and Cherem–Rugina full texts is the cheapest way to fill the **Boundaries** gaps (fraction freed, GC-time effect, causes of misses).
