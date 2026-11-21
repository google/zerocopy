# Liveness-driven reclamation: what language specifications license, how finalizers, cleaners and weak references observe it, which fences restore intent, and how much liveness precision changes retained memory

## Summary

- **Reachability is not lexical scope.** Four production language definitions or runtimes explicitly allow an implementation to reclaim an object after its last use even while a variable naming it is still in scope, or while one of its own methods is still executing:
  - the Java Language Specification (JLS SE 25 §12.6.1);
  - the Go runtime documentation (`runtime.SetFinalizer`, `runtime.AddCleanup`);
  - the .NET runtime source commentary for `GC.KeepAlive`;
  - ECMA-262, which defines liveness formally through "WeakRef-oblivious" executions.
- **Only reclamation-observing mechanisms can see it.** Early reclamation is invisible unless the program can observe it through a finalizer, a cleaner, a weak reference or finalization registry, or a native resource that one of these releases. The pinned Java and Go texts give the canonical failure: a cleanup closes a file descriptor or nulls a table slot while a method that has already read the handle is still using it.
- **Every examined platform supplies an explicit fence.** The fences differ in memory-ordering strength:
  - Java's `Reference.reachabilityFence` makes prior actions *happen-before* the collector clears references.
  - Go's `runtime.KeepAlive` explicitly does **not** "synchronize before" the finalizer.
  - .NET's `GC.KeepAlive` is an empty `NoInlining`/`Intrinsic` method.
  - The Boehm–Demers–Weiser collector's `GC_reachable_here` is an empty `asm volatile` with the pointer as an input operand.
  - ECMA-262 keeps a `WeakRef.prototype.deref` result alive (the `[[KeptAlive]]` list) until the host calls `ClearKeptObjects` at the end of synchronous execution.
  - The JLS additionally keeps an object alive while a lock is held on it, if its finalizer may synchronize on it.
- **Measured on real toolchains** (x86-64 Linux; probes and raw output in `support/`):
  - Go 1.27.3: across all no-fence runs, a cleanup or finalizer closed the descriptor before a later `write` in 277 of 280 trials. The runs covered both mechanisms, both builds, and run lengths of 20 and 50 trials. The one miss whose index was recorded was trial 0. Early release occurred with **both** default optimization and `-gcflags='all=-N -l'`. Adding `runtime.KeepAlive` gave `0` in every run.
  - OpenJDK 27.0.1 HotSpot: `0/20` early cleanings in the interpreter (`-Xint`) and `20/20` with C1- or C2-compiled code (`-Xcomp`). Under default tiered compilation, early cleaning began at trial 256, immediately after `actionNoFence` was compiled at tier 3. `reachabilityFence(this)` in a `finally` gave `0` in every configuration.
  - So in Java, whether early reclamation happens depends on the execution tier, not on the source text.
- **The abstract theory has a limit.** Morrisett–Felleisen–Harper (FPCA 1995) define a binding as garbage iff removing it leaves the program Kleene-equivalent. They prove optimal collection undecidable, prove the free-variable (reachability) rule correct, and prove that a type-inference rule can reclaim *reachable* bindings in cycle-free heaps. Their observables are integer results and termination only. "Collections never change results" therefore holds by definition, and the theory says nothing about finalizer-observable reclamation or about space.
- **Measured precision gains are workload-skewed.**
  - Agesen–Detlefs–Moss (PLDI 1998): stack liveness over type-precise roots cut the heap time-space product by 11% on average, but by 3.6% without the one outlier (`ellisgc`, 78.7%). Live-precise stack maps cost about 50% more to generate.
  - Shaham–Kolodner–Sagiv (ISMM 2002): heap-reference liveness offered an average potential saving of 39% with complete liveness information, and 15% with a restricted interface. Stack liveness gave small benefits.
  - Hirzel–Diwan–Henkel (TOPLAS 2002): liveness accuracy reduced the reachable heap by up to 62%, but simple intraprocedural schemes were "largely ineffective", and type accuracy had an "insignificant impact".
  - GHC still implements (`+RTS -hb`) the lag/drag/void/use heap-cell biography of Röjemo and Runciman (ICFP 1996). The definitions are taken from the same authors' 1996 lecture notes, because the ICFP full text was not examined.
- **Never-worse holds only at a fixed heap state, and none of the studies measured observable-behaviour effects.** In every study above, the more precise configuration marks a subset of what the less precise one marks at the same heap state, so "never retains more at that instant" is structural rather than measured. None of the studies measured observable-behaviour effects of earlier reclamation. Where finalizers, cleaners or weak references exist, liveness-driven reclamation changes observable behaviour, so it is not a semantics-preserving optimization in general.

## Applicability

**Subjects and their relationship.** This report compares how one phenomenon is specified, implemented, observed and measured across several subjects. The phenomenon is reclaiming an object that is still in lexical scope but no longer live. The subjects are:

| Role | Subject (pins in `REPORT.json`) | Examined how |
|---|---|---|
| Normative language text | JLS SE 25 §12.6–12.6.2 (HTML at docs.oracle.com) | read |
| Java API and VM source | `openjdk/jdk` @ `b76004bf59b75303c539de649ce9321fd8d28cf3` | read: `Reference.java`, `Cleaner.java`, `Object.java`, `vmIntrinsics.hpp`, `opto/reachability.{hpp,cpp}`, jtreg tests; call sites counted |
| Go runtime and compiler | `golang/go` @ `86147150ffa135e77b0429208dd0b15df1206ea3` | read: `mfinal.go`, `mcleanup.go`, `ssagen/intrinsics.go`, `ssa/_gen/genericOps.go`; call sites counted |
| .NET runtime | `dotnet/runtime` @ `f23392b4a8e37dbbf072eb893f547705312a457a` | read `GC.CoreCLR.cs` only; **not executed** |
| ECMAScript | `tc39/ecma262` @ `74c33d406ec1763ca9ee5ad9165571661649d6e6` | read `spec.html`; **no engine executed** |
| Conservative C/C++ collector | `ivmai/bdwgc` @ `35ad5371a9c8524c5512e50892506217043cb52d` | read `include/gc/gc.h` only |
| Lazy functional runtime | `ghc/ghc` @ `83038fbee5efea8e3ebd5090b2ff5537462e169d` | read `docs/users_guide/profiling.rst`, `rts/sm/Evac.c`; **not executed** |
| Executed toolchains | Go go1.27.3 (`golang/go` @ `2aae1000ea1d4b28923b96db28acf4e3b99d6aff`); OpenJDK 27.0.1 HotSpot vendor build | probes run |
| Literature | eight papers plus one lecture-notes chapter (DOIs in `REPORT.json`) | full text or abstract, as stated per item under **Evidence** |

**Version scope.**
- The JLS text quoted is the SE 25 edition. The clauses quoted from §12.6.1, including the "Finalizer Guardian" discussion, are long-standing, but earlier editions were **not examined**.
- The OpenJDK pin is a development-head snapshot in which `Reference.reachabilityFence` carries `@IntrinsicCandidate` and C2 lowers it to `ReachabilityFenceNode`. How earlier JDK releases implemented the fence was **not examined**.
- The executed JDK is a vendor build that reports `27.0.1` (released 2026-11-18). Its exact source revision was not verified, so execution results are attributed to that binary, not to the `openjdk/jdk` pin.
- The executed Go toolchain reports `go1.27.3 linux/amd64`. Its packaging provenance was not verified; the `go1.27.3` tag resolves to the commit pinned above.

**Configurations covered by execution.**
- Go: default build vs. `-gcflags='all=-N -l'`; `runtime.AddCleanup` vs. `runtime.SetFinalizer`; with and without `runtime.KeepAlive`.
- Java (default G1 collector): `-Xint`; `-Xcomp -XX:TieredStopAtLevel=1` (C1); `-Xcomp -XX:-TieredCompilation` (C2); default tiered; with and without `reachabilityFence`.
- Host: x86-64 Linux VM, 96 vCPUs (Intel Xeon @ 2.60 GHz), 236 GiB RAM.
- Other architectures, collectors (ZGC, Shenandoah, Serial, Parallel), GOGC settings and Go GC modes were **not examined**.

**Out of scope.**
- Reference-counted runtimes (CPython, Swift ARC).
- Ownership-based reclamation (Rust drop elaboration).
- Region systems.
- These have different "last use" semantics and were **not examined**.

## Findings

### F1. Abstract collection rules: what is defined and proved (Morrisett–Felleisen–Harper 1995)

Basis: documentation (paper full text, author-hosted copy) + derived.

MFH model the heap syntactically. A program is `letrec H in e`: `H` is a set of bindings, which represents the heap, and evaluation allocates into `H`.

| Notion | MFH definition or result (quoted or paraphrased from the paper) | Correspondence (derived) |
|---|---|---|
| Observables | "we consider only integer results and non-termination to be observable" (Kleene equivalence, Definition 2.2) | No finalizers, weak references or space are observable |
| Semantic garbage | Definition 2.3: binding `x = h` is garbage w.r.t. `P` iff `P ≃ letrec H in e` (Kleene-equivalent without it); a *collection* removes some garbage bindings | The "liveness" ideal: anything whose removal is unobservable |
| Optimal collection | Proposition 2.4 (Garbage Undecidable), by reduction from halting | No implementation can collect exactly the semantic garbage |
| Free-variable rule (`fv`) | Removes `H2` when its domain is not free in `H1` or in the current expression; Theorem 3.3 (Correctness of `fv`): one `fv` step yields a collection; proved via Postponement (3.1) and Diamond (3.2) lemmas; models mark/sweep and copying collectors | Reachability from the *remaining* term. In a substitution semantics, a variable whose last occurrence has been consumed is no longer free, so `fv` already behaves like a collector with exact *root* liveness for the remaining term. A scope-based (lexical-retention) collector is not one of MFH's rules |
| Tag-free typed rule (`mono`) | Collect if the residual program is still well typed; Theorem 4.4 | Type-precise roots (the analogue of Agesen et al.'s "type-precise" level) |
| Inference rule | Theorem 5.3 (Inference GC): if a heap location can be given a type variable in a typing of a **cycle-free** program, it can be rebound to `0` without affecting evaluation — "an object is semantically garbage even though the object is still reachable" | Collects strictly beyond reachability; requires the cycle-freedom side condition |

Consequences for liveness-driven narrowing (derived):
1. Every MFH rule is proved to produce a *collection*, which by Definition 2.3 preserves results. "A collection rule never changes program results" is therefore a theorem *relative to observables that exclude finalization and weak references*. Once a finalizer or weak reference is added, removing a reachable-but-dead binding can change the result, and the MFH correctness theorems no longer apply.
2. MFH compare rules by which bindings they may remove, not by peak or integrated space. The rules nest: everything `fv` removes is semantic garbage, and the inference rule removes some reachable bindings that `fv` keeps. MFH do **not** state a space theorem of the form "rule A's residency is never larger than rule B's".

### F2. What each production specification licenses, how programs observe it, and what fence restores intent

Basis: normative (JLS, ECMA-262) + documentation and source (OpenJDK, Go, .NET, bdwgc), at the pins in `REPORT.json`.

| Platform | Licence for early reclamation (quoted) | Observers | Fence / keep-alive | Ordering guarantee of the fence |
|---|---|---|---|---|
| Java (JLS SE 25 §12.6.1) | "Optimizing transformations of a program can be designed that reduce the number of objects that are reachable to be less than those which would naively be considered reachable." Example: storing field values in registers; "Note that this sort of optimization is only allowed if references are on the stack, not stored in the heap." | `finalize`; `java.lang.ref` references (JLS defers to API docs) | Synchronization: "If an object's finalizer can result in synchronization on that object, then that object must be alive and considered reachable whenever a lock is held on it." | §12.6.2 reachability decision points; constructor completion happens-before `finalize` |
| Java API (`Reference.java`) | apiNote: "the virtual machine can reorder operations of an object's methods such that the object becomes unneeded earlier than might naively be expected — including while a method of the object is still running" (lines 575–593) | `Cleaner`, finalizers, reference processing | `Reference.reachabilityFence(Object)` since 9 (lines 549–664) | "Actions in a thread prior to calling `reachabilityFence(x)` happen-before the garbage collector clears any reference to `x`." (lines 570–573) |
| Go (`mfinal.go`, `mcleanup.go`) | "A function argument or receiver may become unreachable at the last point where the function mentions it." (`mfinal.go` 397–404; same text for cleanups at `mcleanup.go` 65–73) | `SetFinalizer`, `AddCleanup`, `weak` pointers | `runtime.KeepAlive(x)` (`mfinal.go` 547–582) | "there is no guarantee that KeepAlive(x) or any other use of x 'synchronizes before' f(x)" (`mfinal.go` 421–431) |
| .NET (`GC.CoreCLR.cs`) | "The JIT is very aggressive about keeping an object's lifetime to as small a window as possible, to the point where a 'this' pointer isn't considered live in an instance method unless you read a value from the instance." (lines 263–272) | finalizers (`Finalize`) | `GC.KeepAlive(object?)`: `[MethodImpl(MethodImplOptions.NoInlining)] [Intrinsic]`, empty body (lines 298–302) | none stated in the examined file |
| ECMAScript (ECMA-262 `spec.html`) | Liveness defined via WeakRef-oblivious executions (lines 12635–12672); "Optimizations such as dead variable elimination and scalar replacement on properties of non-escaping objects whose identity is not observed are allowed. These optimizations are thus allowed to observably empty WeakRefs that point to such objects." (line 12698) | `WeakRef`, `FinalizationRegistry`, `WeakMap`/`WeakSet` | `[[KeptAlive]]`: `WeakRef.prototype.deref` performs `AddToKeptObjects(target)` (line 48359); the list is cleared by `ClearKeptObjects` (lines 12733–12741) | read consistency within one synchronous run; host schedules clearing |
| C/C++ conservative GC (`bdwgc gc.h`) | "This prevents the argument pointer from being optimized away, even it is otherwise no longer needed." (lines 1873–1881) | finalizers, "disappearing links" | `GC_reachable_here(ptr)`: `__asm__ __volatile__(" " : : "X"(ptr) : "memory")` on GNU C (lines 1882–1900) | compiler barrier only (`"memory"` clobber) |

Details that matter when composing components:

- **Java heap vs. stack asymmetry (normative).**
  - JLS §12.6.1 permits reachability-reducing transformations only for stack references. A field that is never read, such as the "Finalizer Guardian" inner object, must not be nulled out early: "This sort of transformation is therefore not legal: the inner class object should be reachable for as long as the outer class object is reachable."
  - A conforming narrowing pass may therefore shorten the lifetime of locals, parameters and `this`, but not of heap edges.
- **Java's formal model (normative).** §12.6.2 defines *reachability decision points* `d_i` and *active uses*:
  - a read or write of an element of `X`;
  - a lock or unlock of `X`, when some lock action on `X` happens-after the invocation of `X`'s finalizer;
  - a write of a reference to `X`;
  - an active use of some `Y` from which `X` is definitely reachable.
  
  If `X` is marked unreachable at `d_i`, all of its active uses that come after `d_i` must be in its finalizer or must follow a fresh read of a reference to `X`. A method that has already copied `this.idx` into a register therefore makes no active use of `this` afterwards.
- **Java finalization is being phased out (source).** `Object.finalize` is `@Deprecated(since="9", forRemoval=true)` (`Object.java` 702–703), and its Javadoc points to JEP 421 (lines 679–683). Lines 607–611 add: "When running in a Java virtual machine in which finalization has been disabled or removed, the garbage collector will never call `finalize()` for any object." The same early-reclamation hazard applies to `Cleaner`:
  - "the cleaning action must not refer to the object being registered. If so, the object will not become phantom reachable" (`Cleaner.java` 50–55);
  - "The cleaning action could be a lambda but all too easily will capture the object reference" (lines 120–122).
- **Go details (documentation).**
  - Finalizers run sequentially on one goroutine; cleanups "may also run concurrently with one another (unlike finalizers)" (`mcleanup.go` 39).
  - `AddCleanup` panics if `arg == ptr`, because "If ptr is reachable from cleanup or arg, ptr will never be collected" (`mcleanup.go` 29–31; check at lines 95–99).
  - Tiny pointer-free objects (≲16 bytes) may be batched into one allocation slot, so their finalizers or cleanups "may never run" (`mfinal.go` 389–395; `mcleanup.go` 57–63).
  - `SetFinalizer(x, f)` "synchronizes before" `f(x)` (line 422). Without extra synchronization, mutable state touched by both the program and the finalizer is a data race.
- **ECMA-262 obligations (normative).**
  - "If an object's identity is observable, and that object is in the `[[WeakRefTarget]]` internal slot of a WeakRef, optimizations such as rematerialization that observably empty the WeakRef are prohibited." (line 12700)
  - Emptying must be atomic over the chosen non-live set: "it is not conformant for an implementation to empty a WeakRef pointing to a value _v_ without emptying out other WeakRefs that, if not emptied, could result in an execution that observes the value of _v_." (line 12706)
  - "Liveness as defined here is undecidable. In practice, engines use conservative approximations such as reachability." (line 12671)
  - "This specification does not make any guarantees that any object or symbol will be garbage collected." (line 12616)

### F3. Compiler and collector obligations that keep early reclamation safe under optimization

Basis: source (HotSpot C2, Go compiler, GHC RTS, bdwgc) + normative (JLS, ECMA-262) + derived.

1. **Fence-induced liveness must reach every safepoint that interferes with the referent's live range (HotSpot C2).**
   - `opto/reachability.cpp` lines 35–90 describe the design. `Reference::reachabilityFence()` calls are intrinsified into `ReachabilityFenceNode` CFG nodes (`reachability.hpp` 39–42; intrinsic id `_Reference_reachabilityFence` at `vmIntrinsics.hpp` 486–487). The referent must appear in the oop map of every interfering safepoint.
   - The stated hazard is: "Live ranges of values are routinely extended during loop opts. And it can break the invariant that all interfering safepoints contain the referent in their oop map. (If an interfering safepoint doesn't keep the referent alive, then it becomes possible for the referent to be prematurely GCed.)" (lines 68–70).
   - The representation therefore moves through four numbered stages:
     - (0) fence nodes are materialized at parse time;
     - (1) during loop optimization, redundant fences are eliminated and loop-invariant ones are moved after the loop;
     - (2) after loop optimization, fences become extra safepoint edges;
     - (3) fences are re-materialized after their safepoints before register allocation.
   - `ReachabilityFenceNode::is_redundant` (lines 95–106) treats a null referent as a no-op. When `OptimizeReachabilityFences` is on and `PreserveReachabilityFencesOnConstants` is off, it also drops fences on constants ("constants are strongly reachable").
   - The design comment cites `compiler/c2/TestReachabilityFence.java` (line 72), but that path does not exist at the pin (HTTP 404). The test that exercises the loop-hoisting case is `test/hotspot/jtreg/compiler/c2/ReachabilityFenceTest.java` (`@bug 8290892`; lines 163–167 describe the hoisted `payload[id]` load). This is a stale comment reference, not a functional defect.
2. **Go: `KeepAlive` is a memory-threaded, zero-width SSA use.**
   - `ssagen/intrinsics.go` lines 157–163 replace `runtime.KeepAlive` with `OpKeepAlive(IData(x), mem)`.
   - `genericOps.go` line 597 declares it `zeroWidth: true` with the comment "arg[0] is a value that must be kept alive until this mark".
   - The fallback body (`mfinal.go` 575–582) keeps an uneliminable use, because "We need x to be alive on entry for `defer runtime.KeepAlive(x)`; see issue 21402."
   - Measured effect on generated code: see F4.
3. **Java: stack-only narrowing and the synchronization exception (normative).** A narrowing pass that is conforming under JLS §12.6.1 may drop dead stack and register references. It must not drop heap references. It must keep an object reachable while a lock on it is held, if its finalizer may synchronize on it.
4. **ECMAScript: no rematerialization that empties an observable WeakRef, and atomic emptying (normative).** Dead-variable elimination and scalar replacement are explicitly allowed even when they observably empty WeakRefs.
5. **Conservative C/C++: the compiler must not hide the base pointer.** `GC_reachable_here` forces the pointer to exist as an `asm` input at that program point (`gc.h` 1882–1900). The broader compiler obligations of Boehm 1996 (PLDI, "Simple Garbage-Collector-Safety") were **not examined** beyond bibliographic metadata.
6. **Collector-side repair of known space leaks.** GHC's copying collector evaluates selector thunks during evacuation (`rts/sm/Evac.c` `eval_thunk_selector`, lines 1240–1252). It bails out when the selectee has already been evacuated, because "we won't save any space leaks by evaluating this selector thunk anyhow" (lines 1381–1385). This is the collector-modification approach whose origin secondary sources attribute to Wadler 1987. Wadler's Crossref abstract reads only: "A modification to the garbage collector is suggested which solves this problem in some cases."

Which obligations a compositional, per-component pass can discharge locally (derived):

| Obligation | Local to one function or component? | Why |
|---|---|---|
| Keep each fence's referent in every interfering safepoint's root map | Yes, if the fence is in that function and the pass runs after all live-range-extending transforms | C2 makes this ordering requirement explicit (stage 2 only after loop opts) |
| JLS heap-reference rule (never narrow heap edges) | Yes (syntactic: only stack slots and registers) | — |
| Do not narrow an object whose finalizer may synchronize while a lock is held | **No** in general | The finalizer's body may be in another component, and the possible dynamic receiver class is a whole-program fact |
| Whether narrowing is observable at all | **No** | Requires knowing whether any finalizer, cleaner, weak reference or registry can reach the object, which is a heap-wide, cross-component property |
| ECMA-262 atomic emptying over a non-live set | **No** (collector-global) | Defined over all WeakRefs that could observe the set |
| Go: avoid tiny-object batching for cleanup arguments | Runtime-local | `AddCleanup` side-steps the tiny allocator for its argument box (`mcleanup.go` 115–125) |

### F4. Execution probes: early reclamation and fences on real toolchains

Basis: execution (real toolchains as described under **Applicability**; the probe programs are mine).

Probe design (identical intent in both languages). An object wraps a "native" handle:
- in Go, the write end of an OS pipe;
- in Java, an index into a `freed` flag table.

A cleanup or finalizer releases the handle when the object becomes unreachable. A method or function reads the handle (the last use of the object), forces three GC cycles with 20 ms pauses, and then uses the handle. Sources: `support/go/early.go`, `support/java/EarlyReclaim.java`.

**Go go1.27.3** (`support/go/output.txt`):

| Build | Mechanism | Fence | Early release observed (`write` → `EBADF`): 20-trial run | 50-trial run |
|---|---|---|---|---|
| `go build` (default) | `AddCleanup` | none | 19 / 20 | 50 / 50 |
| default | `SetFinalizer` | none | 19 / 20 | 49 / 50 (the miss was trial 0) |
| default | each mechanism | `runtime.KeepAlive(p)` after the write | 0 / 20 | not run |
| `-gcflags='all=-N -l'` | `AddCleanup` | none | 20 / 20 | 50 / 50 |
| `-N -l` | `SetFinalizer` | none | 20 / 20 | 50 / 50 |
| `-N -l` | each mechanism | `KeepAlive` | 0 / 20 | not run |

The 20-trial runs did not record which trial missed. Total without a fence: 277 / 280 (derived: 19 + 19 + 20 + 20 + 50 + 49 + 50 + 50).

Disabling optimization and inlining did **not** extend the parameter's lifetime to the end of the function in this toolchain. Go's documented rule ("may become unreachable at the last point where the function mentions it") is observable even in debug builds.

**Go code generation for `KeepAlive`** (`go build -gcflags=-S`, amd64; `support/go/asm_amd64.txt`):
- `useNoFence` is 83 bytes and `useKeepAlive` is 98 bytes. The difference (+15 bytes, +18.1%; derived 98 − 83) is one store of `p` to its argument spill slot (`MOVQ AX, main.p+64(SP)`) plus alignment `NOP`s.
- The stack-map index at the `gcAndWait` call changes from `PCDATA $1, $1` to `PCDATA $1, $0`.
- No call to `runtime.KeepAlive` is emitted.

**OpenJDK 27.0.1 HotSpot, G1** (`support/java/output.txt`):

| Configuration | `actionNoFence` early cleanings | `actionFence` (`reachabilityFence(this)` in `finally`) |
|---|---|---|
| `-Xint` | 0 / 20 | 0 / 20 |
| `-Xcomp -XX:TieredStopAtLevel=1` (C1) | 20 / 20 | 0 / 20 |
| `-Xcomp -XX:-TieredCompilation` (C2) | 20 / 20 | 0 / 20 |
| default tiered | 144 / 400; first at trial 256 | 0 / 400 |
| default tiered + `-XX:+PrintCompilation` | 44 / 300; first at trial 256 | not run |

- With `-XX:+PrintCompilation`, `EarlyReclaim$Resource::actionNoFence` was compiled at tier 3 (compile id 77) just before trial 256. Early cleaning began exactly when compiled code replaced interpretation.
- OpenJDK's own regression test encodes the same expectation. `test/jdk/java/lang/ref/ReachabilityFenceTest.java` (`@bug 8133348`, lines 24–35) runs `-Xint` with `-Dpremature=false` and `-Xbatch -XX:TieredStopAtLevel=1..4` with `-Dpremature=true`.

### F5. Measured effect of liveness precision on retained memory

Basis: documentation (paper text or abstracts as noted) + derived arithmetic.

| Study | Programs | Precision levels compared | Metric | Reported result | Never-worse property |
|---|---|---|---|---|---|
| Agesen, Detlefs, Moss, PLDI 1998 (full text) | SPEC-candidate Java benchmarks (e.g., `compress`, `jess`, `javac`, `raytrace`, `db`), plus `ellisgc`, `hotjava`, `volano` and others | type-precise vs. live-precise stack roots, both in one JVM; mark phases of both run on the same heap every 100K words allocated | integral of marked words over allocation time (time-space product); geometric means | "liveness information reduces the time-space product by an average of 11%"; "omitting ellisgc … improves by an average of 3.6%". `ellisgc` ratio 0.2129 (derived: 78.7% reduction); `hotjava` 929,484,329 vs. 929,502,587 (derived: < 0.01%); "almost every program we ran shows a measurable difference". Cost: live-precise map generation about 50% more than type-precise (measured increase 54–58%); stack maps averaged 57% of bytecode size | **Structural**: live-precise roots ⊆ type-precise roots and both mark the same heap state, so each sample cannot be larger (derived from the method). Not separately measured |
| Shaham, Kolodner, Sagiv, ISMM 2002 (abstract from publisher-affiliated page) | 10 benchmarks, 5 from SPECjvm98 | actual collection time vs. earliest possible collection time given (i) stack, (ii) global, (iii) heap reference liveness, and combinations; instrumented JVM | potential space savings (drag-style) | "stack reference liveness may yield small benefits, global reference liveness combined with stack reference liveness may yield medium benefits, and heap reference liveness yields the largest potential benefit"; heap: "average potential savings of 39% using an interface with complete liveness information, and an average savings of 15% using a more restricted interface" | **Assumed** (savings are measured against an oracle of earliest possible collection; not a deployed collector) |
| Hirzel, Diwan, Henkel, TOPLAS 2002 (Crossref abstract) | C, C++ and Eiffel programs | type accuracy × liveness accuracy (intraprocedural locals through interprocedural globals) | reachable heap size | "liveness accuracy reduces the reachable heap size by up to 62%"; "the simpler liveness schemes (e.g., intraprocedural analysis of local variables) are largely ineffective … one must analyze global variables using interprocedural analysis"; "Type accuracy has an insignificant impact" | Structural for each traversal; observable-behaviour effects not addressed |
| Röjemo, Runciman, ICFP 1996 (bibliographic record) + Runciman, Röjemo 1996 lecture notes (full text) | nhc-compiled Haskell programs (notes: `xref`, `clausify`) | biographical classification of heap cells over time | bytes × seconds per phase | Notes define the phases: void = never used; lag = creation to first use; use = first to last use; drag = last use to destruction; "used" = "scrutinised in a case, or taken part in a primitive operation, or updated with its result". Example `xref` profile: 80% lag, 20% use. A 2015 York thesis (secondary) attributes two findings to "the authors" of the biographical profile (its reference [39]; the bibliography entry was not recovered from the extracted text): "most of the heap usage of NHC was found to be lag, drag and void", and they "reduced the space consumption of NHC by a factor of two". **Primary ICFP text not examined** | Not applicable (diagnostic, not a collector) |

Interpretation (derived):
- Stack-slot liveness (Agesen et al.; Shaham et al.'s "small") usually buys little.
- Its value is in tail cases: Agesen et al.'s conclusion is "the main benefit of the liveness analysis is preventing bad surprises".
- Larger savings need heap-edge or interprocedural global liveness (Shaham et al.; Hirzel et al.). That is exactly the class of narrowing the JLS forbids implementations to perform silently on heap references (F2).
- Drag is the profiler's name for the retained-after-last-use residue. GHC still exposes it: `profiling.rst` lines 1199–1222 define lag, use, drag and void, and `+RTS -hbdrag,void` restricts a profile to them.

### F6. Never-worse and observability (derived)

- **Instantaneous retention.** For a fixed heap state and collection point, removing roots (narrowing) cannot increase the marked set. Monotonicity of reachability in the root set gives this.
- **No global space theorem in the examined sources.** None of the examined sources proves a global statement such as "peak or integrated residency under liveness-driven reclamation is never larger". MFH compare rules by removable bindings only (F1).
- **What could break never-worse is not modelled.** Two mechanisms could make liveness-driven reclamation consume *more* memory or time:
  - weak caches emptied earlier and then rebuilt;
  - finalizers that resurrect or allocate.

  Neither the measurement studies nor MFH model either mechanism. No examined source measured such a case.
- **Behaviour can change.** The probes in F4 show a semantics change: an I/O call fails. The same source program under a different execution tier (Java) produces it. In Go, no source-level option other than `KeepAlive` prevents it.

### F7. Performance and resource footprint at six levels

Every cell is cited, measured (host class under **Applicability**), derived, or `not measured`.

| Level | Item | Value | Basis |
|---|---|---|---|
| L1 authoring | `reachabilityFence(` code call sites in `openjdk/jdk` `src/` at the pin, excluding Javadoc mentions and the declaration | 68 (52 in `java.base`, 9 `java.smartcardio`, 5 `java.net.http`, 1 `jdk.crypto.cryptoki`, 1 `java.desktop`) | measured (tarball grep; script in **Revalidation**) |
| L1 | `runtime.KeepAlive(` non-test, non-comment call sites in `golang/go` `src/` at the pin | 147 (124 excluding `testdata` and `cmd/vendor`); 56 non-test files; most in `src/net` (18 files) and `src/os` (11 files) | measured |
| L1 | Person-time or LLM-turn cost of placing fences | not measured | — |
| L2 toolchain build | Build time or memory of JDK/Go/.NET/engines | not measured | — |
| L3 analysis latency | Live-precise vs. type-precise stack-map generation | about 50% more; measured increase 54–58% across benchmarks | cited (Agesen et al.) |
| L3 | C2 cost of fence stages; Go liveness-analysis cost | not measured | — |
| L4 generated code | Go `KeepAlive` | +1 store and +15 bytes (83 → 98) in the probe function; no call emitted | measured (`-gcflags=-S`, amd64) |
| L4 | HotSpot fence code; .NET `GC.KeepAlive` | not measured (C2's comment states a design goal of reducing runtime overhead, without numbers) | — |
| L5 proof/certificate checking | no certificate is produced by any examined subject | not applicable | — |
| L6 memory | Heap time-space product with stack liveness | −11% geometric mean; −3.6% without `ellisgc`; −78.7% `ellisgc` | cited + derived |
| L6 | Stack-map size | average 57% of bytecode size | cited (Agesen et al.) |
| L6 | Potential savings from heap-reference liveness | 39% (complete information), 15% (restricted interface) | cited (Shaham et al.) |
| L6 | Reachable-heap reduction from liveness accuracy | up to 62% | cited (Hirzel et al.) |
| L6 | nhc space after biographical profiling | "factor of two" | secondary (thesis); primary not examined |
| L6 | Retained-memory effect of fences in the probes | not measured | — |

### F8. Human comprehensibility and conceptual simplicity (C1, C2)

- **C1: working-memory load.** A reader must hold three separate notions: lexical scope; liveness (future use); and reachability (what the collector traces, which in a JIT depends on the execution tier). The bug class arises because programmers reason with scope while implementations reclaim by liveness.
  - The failure is **non-local**: the hazard is in a method body, but the trigger is a cleanup registered elsewhere.
  - It is also **tier-dependent**: in F4, interpreted Java never showed it.
  - The diagnostic surface is poor: the symptom is a use-after-close (`EBADF`) far from its cause. No examined runtime emits a warning when a finalizable object's last use precedes a native call on its handle.
- **C1: human-auditable fences.** Fences are explicit, local and greppable (F7: 68 and 147 sites). Their placement rule ("after the last point where the object must remain reachable", and in Java "in a `finally` block … across all paths") is a whole-method obligation that is easy to omit on one path.
- **C2: one invariant, several mechanisms.** The underlying invariant is the same everywhere: an object whose release has an observable effect must stay in the root set until its last *semantic* use. It is enforced through different means:
  - JLS synchronization;
  - `reachabilityFence`;
  - `KeepAlive`;
  - `GC_reachable_here`;
  - ECMA-262's kept-objects list;
  - ownership in `try`-with-resources and `Close`/`Dispose`, which avoids the collector entirely.
- **C2: a minimal unifying abstraction (derived).** Distinguish *observable-release* objects (those with a finalizer, cleaner, weak reference or registry) from all others. For ordinary objects, narrowing is unobservable, and MFH's correctness argument applies unchanged. For observable-release objects, treat release as an effect ordered after an explicit last-use point. The fence primitives above are that last-use point in different syntaxes. This does not remove the whole-program question of *which* objects are observable-release (F3 table). It only localizes it.

### F9. How solutions are validated (V1–V4)

- **V1: specification adequacy and non-vacuity.** OpenJDK's `ReachabilityFenceTest` is self-validating. Its negative "nonFenced" part checks that premature finalization *does* occur in VM modes where it is expected, which "validates the test itself" (lines 44–57), and only then checks the fenced part. My probes reuse that design: each configuration's no-fence column is the negative control. ECMA-262 GC behaviour is permissive ("may"), so a conformance test cannot require emptying. How test262 covers it was **not examined**.
- **V2: compiler soundness testing.** The C2 IR test `compiler/c2/irTests/ReachabilityFenceTest.java` checks loop transformations around fences (`@bug 8290892`). Differential or metamorphic fuzzing of fence handling across compilers was **not examined**.
- **V3: concurrency.** Finalizer and cleaner threads race with mutators. The probes are stress tests with sleeps, not stateless model checking. The Go "synchronizes before" gap (F2) was not exercised. No `GenMC`/`Loom`-style exploration was **examined**.
- **V4: human mental models.** No empirical study of programmers' scope-versus-liveness expectations was examined. The platform documents rely on worked examples instead: the JLS Finalizer Guardian; Java `Resource.action`; Go `syscall.Read`/`syscall.Write`; .NET `Foo.Problem`.

## Boundaries

- **Not examined.**
  - Execution of .NET, any ECMAScript engine, GHC, or bdwgc. Their rows rest on source and specification text only.
  - JDK collectors other than G1.
  - Non-x86-64 targets.
  - Go with `GOGC`/`GOEXPERIMENT` variations.
  - Earlier JLS editions and earlier JDK implementations of `reachabilityFence` (before the C2 intrinsic).
  - The full texts of Röjemo–Runciman ICFP 1996, Boehm 1996, Boehm 2003 and Wadler 1987: the publisher site was not reachable from the research environment. Their content here is limited to Crossref metadata and abstracts, secondary summaries (labelled), and Boehm's 2003 slide titles. Those titles include "Garbage collectors should run finalizers from a separate thread." and "Late finalization is necessary, but".
  - The Shaham et al. and Hirzel et al. papers beyond their abstracts. Per-benchmark numbers and the "restricted interface" design are not reproduced here.
- **Unknown.**
  - Whether the `go1.27.3` binary and the OpenJDK vendor build differ from their upstream tags in ways relevant to liveness. Not verified.
  - Why one `SetFinalizer` trial (trial 0) did not show early release. The finalizer goroutine's start-up is plausible, but this was not investigated.
- **Known not to apply.**
  - MFH's "collection never changes results" does not extend to programs with finalizers, cleaners or weak references (F1).
  - Go `-N -l` does not keep parameters alive to the end of the function (F4).
- **Unsupported.** ECMA-262 gives no guarantee that any object is ever collected or that finalization callbacks ever run (line 12616 and the execution clause notes). Tests may not rely on either.
- **Attractive stronger conclusions not established.**
  - (a) That liveness-driven reclamation never increases peak or total memory. Only the per-instant structural property holds.
  - (b) That interprocedural heap liveness is deployable at the savings Shaham et al. report. Their numbers are potential savings against an oracle.
  - (c) That any probe count is a rate. Trials were sequential on one host with fixed sleeps.
  - (d) That `KeepAlive` costs one store in general. That was measured for one function on amd64.

## Evidence

All repository evidence was read at the pinned commits on 2026-11-21 (UTC), via `raw.githubusercontent.com/<repo>/<sha>/<path>`. Probe executions also ran on 2026-11-21.

- **JLS SE 25**, `https://docs.oracle.com/javase/specs/jls/se25/html/jls-12.html`:
  - §12.6 ("The completion of an object's constructor happens-before … its finalize method");
  - §12.6.1 ("Optimizing transformations …"; registers example; "only allowed if references are on the stack"; Finalizer Guardian; "synchronization may keep the object alive");
  - §12.6.2 (reachability decision points; "definitely reachable"; "active use").
- **`openjdk/jdk` @ `b76004bf59b75303c539de649ce9321fd8d28cf3`**:
  - `src/java.base/share/classes/java/lang/ref/Reference.java` lines 549–573 (contract and happens-before), 575–593 (apiNote), 594–658 (example), 660–664 (`@IntrinsicCandidate public static void reachabilityFence(Object ref)`, body comment "Does nothing. HotSpot JVM retains the ref and does not GC it before a call to this method.");
  - `Cleaner.java` lines 35–39, 50–55, 73–75, 120–122;
  - `Object.java` lines 607–611, 679–683, 702–703;
  - `src/hotspot/share/classfile/vmIntrinsics.hpp` 486–487;
  - `src/hotspot/share/opto/reachability.hpp` 31–42;
  - `src/hotspot/share/opto/reachability.cpp` 35–90, 95–106;
  - `test/jdk/java/lang/ref/ReachabilityFenceTest.java` 24–57;
  - `test/hotspot/jtreg/compiler/c2/ReachabilityFenceTest.java` 37–38, 155–175;
  - `test/hotspot/jtreg/compiler/c2/irTests/ReachabilityFenceTest.java` 34–38;
  - `test/hotspot/jtreg/compiler/c2/TestReachabilityFence.java` → HTTP 404.
- **`golang/go` @ `86147150ffa135e77b0429208dd0b15df1206ea3`**:
  - `src/runtime/mfinal.go` lines 341–431 (`SetFinalizer` documentation), 432 (signature), 547–582 (`KeepAlive`);
  - `src/runtime/mcleanup.go` lines 20–76 (`AddCleanup` documentation and signature), 95–99, 115–125;
  - `src/cmd/compile/internal/ssagen/intrinsics.go` 157–163;
  - `src/cmd/compile/internal/ssa/_gen/genericOps.go` 595–597;
  - `src/cmd/compile/internal/liveness/plive.go` 296 and 367 (`OpKeepAlive` handled as a use).
- **`dotnet/runtime` @ `f23392b4a8e37dbbf072eb893f547705312a457a`**: `src/coreclr/System.Private.CoreLib/src/System/GC.CoreCLR.cs` lines 263–302 (comment 263–296; attributes and empty body 298–302).
- **`tc39/ecma262` @ `74c33d406ec1763ca9ee5ad9165571661649d6e6`**, `spec.html`:
  - lines 12610–12631 (processing model, objectives);
  - 12635–12672 (liveness);
  - 12675–12707 (execution and permitted/prohibited optimizations);
  - 12733–12760 (`ClearKeptObjects`, `AddToKeptObjects`);
  - 48359 and 48411 (`deref` → `AddToKeptObjects`).
- **`ghc/ghc` @ `83038fbee5efea8e3ebd5090b2ff5537462e169d`**: `docs/users_guide/profiling.rst` 974–976, 1055, 1199–1242; `rts/sm/Evac.c` 1240–1252, 1381–1385.
- **`ivmai/bdwgc` @ `35ad5371a9c8524c5512e50892506217043cb52d`**: `include/gc/gc.h` 1872–1900.
- **DOIs**: all ten were verified against `api.crossref.org/works/<doi>` (title, authors, venue, pages). The verified DOIs are:
  - `10.1145/224164.224182` (pp. 66–77);
  - `10.1145/277650.277738` (pp. 269–279);
  - `10.1145/512429.512437` (pp. 64–75);
  - `10.1145/586088.586089` (pp. 593–624);
  - `10.1145/232627.232633` (pp. 34–41);
  - `10.1007/3-540-61628-4_6`;
  - `10.1002/spe.4380170904` (pp. 595–608);
  - `10.1145/231379.231394` (pp. 89–98);
  - `10.1145/604131.604153` (pp. 262–272).
- **Full texts and abstracts read.**
  - MFH 1995: `https://www.cs.cmu.edu/~rwh/papers/gc/fpca95.pdf`.
  - Agesen et al. 1998: `http://www.cs.umass.edu/~moss/papers/pldi-1998-liveness.pdf`.
  - Shaham et al. 2002 abstract: `https://research.ibm.com/publications/estimating-the-impact-of-heap-liveness-information-on-space-consumption-in-java--1`.
  - Hirzel et al. 2002 abstract: Crossref record.
  - Runciman–Röjemo 1996 lecture notes: author-formatted PDF via `https://scispace.com/pdf/heap-profiling-for-space-efficiency-513k778a6f.pdf`.
  - Secondary source: F. Moalla, *Fresh Techniques for Memory Profiling of Lazy Functional Programs*, PhD thesis, University of York (`https://etheses.whiterose.ac.uk/id/eprint/13214/1/FirasMoalla.pdf`), §2.3.3.
  - Boehm 2003 slide titles: `https://www.hboehm.info/popl03/web/index.html`.
- **Probe environment.** x86-64 Linux VM, 96 vCPUs, 236 GiB RAM.
  - Go: `go version go1.27.3 linux/amd64`, with `GOTOOLCHAIN=local` and `GOCACHE` under `/tmp`.
  - Java: OpenJDK 27.0.1 HotSpot 64-Bit Server VM (vendor build suffix redacted in `support/java/output.txt`), with default flags including `-XX:+UseG1GC`.
- **Support files.** `support/go/early.go` and `support/go/output.txt`. The first 20-trial block in `output.txt` was produced by the same program before the `writes_ok_at_trials` field was added. The rest of the support material is `support/go/asm_amd64.txt`, `support/java/EarlyReclaim.java` and `support/java/output.txt`.

## Revalidation

1. **Spec and source drift.** Re-fetch the quoted regions at a new revision and diff them:
   - `Reference.java` `reachabilityFence` Javadoc and annotation;
   - `mfinal.go` `KeepAlive` and the "may become unreachable at the last point" sentence;
   - `GC.CoreCLR.cs` `KeepAlive` attributes;
   - `spec.html` `sec-weakref-processing-model` and `sec-weakref-execution`;
   - `opto/reachability.cpp` header comment.

   A change in the happens-before sentence, the Go "synchronizes before" disclaimer, or the ECMA-262 optimization paragraphs invalidates F2.
2. **Go probe (≈30 s).**
   ```bash
   export GOCACHE=/tmp/gocache GOTOOLCHAIN=local
   go build -o early_opt early.go && go build -gcflags='all=-N -l' -o early_noopt early.go
   for b in early_opt early_noopt; do for m in cleanup finalizer; do for f in nofence keepalive; do ./$b $m $f 20; done; done; done
   go build -gcflags=-S -o /dev/null early.go 2>&1 | grep -A40 'main.useKeepAlive STEXT'
   ```
   Expect high `write_failed_EBADF` without the fence, 0 with it, and no `CALL runtime.KeepAlive`.
3. **Java probe (≈2 min).**
   ```bash
   javac -d classes EarlyReclaim.java
   for cfg in "-Xint" "-XX:TieredStopAtLevel=1 -Xcomp" "-XX:-TieredCompilation -Xcomp"; do
     for m in nofence fence; do java $cfg -cp classes EarlyReclaim $m 20; done; done
   java -XX:+PrintCompilation -cp classes EarlyReclaim nofence 300 | grep -E 'actionNoFence|cleaned'
   ```
   Expect `-Xint` 0; compiled modes 20 without the fence and 0 with it; and early cleaning starting at the first trial after `actionNoFence` is compiled.
4. **Call-site counts (L1).** Download `https://codeload.github.com/<repo>/tar.gz/<sha>`, extract it, and run:
   - `grep -rn --include='*.java' 'reachabilityFence(' src`, dropping lines whose prefix contains `*`, `//` or `{@`, and dropping the declaration;
   - `grep -rn --include='*.go' 'runtime\.KeepAlive(' src`, dropping `_test.go` files and lines with `//` before the call.
5. **Literature numbers.** Re-read Agesen et al. Table 4 and §8.3 (time-space ratios), the Shaham et al. abstract (39%/15%), and the Hirzel et al. abstract (62%). These are static facts, so the only revalidation needed is checking that the DOIs still resolve.
