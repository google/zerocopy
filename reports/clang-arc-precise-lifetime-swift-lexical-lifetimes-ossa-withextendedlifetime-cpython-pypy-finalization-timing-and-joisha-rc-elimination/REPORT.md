# Release-timing contracts in reference-counted languages: Clang ARC precise and imprecise lifetime, Swift lexical lifetimes and deinit barriers, CPython and PyPy finalization timing, and conditions for removing or moving reference-count operations

## Summary

- **Three reference-counted languages, three release-timing contracts.**
  - *Clang ARC:* a strong local's object may die after the last use that loads from the variable ("imprecise lifetime") unless the local is marked `objc_precise_lifetime`.
  - *Swift (since 5.7):* named, non-trivial, copyable values are anchored to lexical scope, but the destroy may be hoisted up to the nearest *deinit barrier*. Eager-move types (`String`, `Array`, `Set`, `Dictionary`) may die at last use, and `~Copyable` values have strict, C++-like lifetimes.
  - *Python:* the language promises no promptness. CPython frees at the last decrement but keeps locals alive until frame exit. PyPy documents finalization and file closing as "not reliable or timely".
- **ARC's permission to shorten is one bit of IR metadata.** Clang tags releases of imprecise locals and temporaries with `!clang.imprecise_release`. LLVM's ObjCARC optimizer treats a tagged release as `S_MovableRelease` and an untagged one as `S_Stop` ("code motion is stopped") (`PtrState.cpp:189-195`, pinned LLVM).
- **Measured on clang 19.1.7, x86_64, logging stand-in runtime:**
  - At `-O1` and above, the retain/release pair in `Obj *x = g; f(x);` is deleted, so when `f` releases `g` the object is deallocated *inside* `f`. With `objc_precise_lifetime` the pair survives.
  - A lone `+1` local's release was not hoisted.
  - In an ARC callee, a retained parameter's release was hoisted to just after its last use, ahead of a later side-effecting call.
  - Interior-pointer receivers get `objc_retainAutorelease` only when their variable has imprecise lifetime.
- **Swift's deinit-barrier predicate in source is broader than the four documented kinds.** The documented kinds are synchronization, weak/unowned loads, pointer accesses, and exclusively-checked global/class accesses. The source adds every full apply, `yield`, `hop_to_executor`, dynamic `end_access`, and memory-accessing builtins. Intent-restoring tools are `withExtendedLifetime`/`extendLifetime` (`Builtin.fixLifetime`), `consume` (SE-0366), and `borrowing`/`consuming` (SE-0377). Swift was not executed.
- **Measured on CPython 3.13.15 (GIL build):**
  - A local's `__del__` ran at function return, not at last use.
  - `del`, rebinding and temporaries released immediately.
  - A cycle waited for `gc.collect()`.
  - An unclosed file was flushed, and a socket closed, at the decrement.
  - PEP 703's free-threaded build frees deferred-count objects (top-level functions, code objects, modules, methods) only during GC. That build and PyPy were not executed.
- **Conditions for deleting or moving count operations fall into three families:**
  1. *Local:* nested pairs on one RC identity, or no intervening possible decrement.
  2. *Contract:* the release may move earlier only if the language allows death before scope end.
  3. *Origin/borrow:* a pair may be dropped across a decrement only if another owned reference provably keeps the object alive (Swift guaranteed parameters, ARC `self`/`objc_externally_retained`, borrowed parameters in Lean-style RC).

  Only the third family needs to know which owner backs a reference.

## Applicability

This report compares contracts, not implementations of one contract.

- **Clang ARC and LLVM.** The `llvm/llvm-project` pin supplies the ARC specification, Clang code generation (`CGObjC.cpp`, `CGDecl.cpp`) and the ObjCARC optimizer.
- **Executed clang.** The executed compiler, Debian clang 19.1.7, is older than that pin (LLVM main, 2026-11-21). Source claims hold at the pin; execution claims hold for 19.1.7. Its emitted IR carries the same `clang.imprecise_release` metadata, but line-by-line identity of its ObjCARC sources with the pin was **not checked**.
- **Swift.** The `swiftlang/swift` and `swiftlang/swift-evolution` pins are source and documentation only.
- **Python.** The `python/cpython` pin (development branch) supplies documentation and `Include/refcount.h`. The executed interpreter is CPython 3.13.15 (GIL build). `python/peps` and `pypy/pypy` are documentation only.
- **Literature.** Each paper's examined depth is stated in **Boundaries**. Hudak 1986 and Joisha 2006/2007 were seen only bibliographically, so they are cited in **Evidence** but not listed as subjects.

**ARC probe configuration.**

- `clang-19 -fobjc-arc -fobjc-runtime=gnustep-2.0 -O{0,1,2,3,s}`, plus `-fno-inline` for the callee probe.
- Objects are opaque `@class Obj` pointers passed to C functions; no message sends execute.
- The runtime is a 113-line logging stand-in (`arc_stub_runtime.c`), **not** Apple's or GNUstep's. It never frees memory, so "deallocated" objects can be inspected safely.

**Python probe configuration.** The probe runs under `python3 -X dev` (the preserved runs use a `runpy` wrapper so that warnings print relative paths) on an x86_64 Linux workstation with 96 logical CPUs. Timings are best-of-5 wall-clock on that host only.

## Findings

### 1. Cross-language release-timing contract matrix

| System and binding kind | Earliest permitted release | Latest release | How the programmer pins it |
|---|---|---|---|
| Clang ARC, `__strong` local (default) | After the last load from the variable on which the computation depends; a value only passed as an argument, or only stored elsewhere, does not count as a dependence | End of scope; ARC may not observably *extend* lifetime | `__attribute__((objc_precise_lifetime))` on the local |
| Clang ARC, precise-lifetime local; globals, ivars | Full formal lifetime of the variable | Same | — |
| Clang ARC, full-expression temporary | After the last dependent use within the full-expression | End of full-expression | — |
| Clang ARC, `self` in non-init method; `objc_externally_retained`; fast-enumeration variable | No retain or release emitted; lifetime is the caller's responsibility | Same | `objc_externally_retained` opt-in |
| Swift, non-trivial copyable `let`/`var`/argument (lexical) | Destroy may be hoisted only up to the nearest deinit barrier | End of lexical scope | `withExtendedLifetime`, `extendLifetime`, `_fixLifetime`; `@_lexical` |
| Swift, eager-move (`String`, `Array`, `Set`, `Dictionary`; `@_eagerMove`, `@_noImplicitCopy`) | Immediately after last use, "independent of any side-effects present in the deinitializer" | End of scope | — |
| Swift, `~Copyable` | Exactly at consumption, or at scope end in reverse declaration order (strict) | Same | `consume`; `discard` (not examined) |
| CPython 3.13 (GIL build) | When the count reaches zero; locals hold a count until frame exit | Never guaranteed for cycles until `gc` runs | `del`, `with`, explicit `close()` |
| CPython free-threaded (PEP 703) | As above, except deferred-count objects (top-level functions, code objects, modules, methods) die only during cyclic GC; biased counting may delay others "slightly" | Next cyclic GC | Same |
| PyPy | When a tracing GC finds it unreachable; `__del__` timing "not reliable or timely" | Unbounded; no automatic `gc.collect()` at exit | Explicit `close()`/`with`; `gc.collect()` |

Basis: normative (ARC spec; Python language reference) + documentation (Swift `Ownership.md`, PEPs, PyPy docs) + source (Swift `Instruction.swift`) + execution (rows for Clang and CPython 3.13 GIL build).

### 2. Clang ARC: the normative text

Pinned `clang/docs/AutomaticReferenceCounting.md`:

- **Liveness (lines 1664-1678).** ARC may not deallocate `X` at time `T` if `X` is held by a `__strong` object `S` with precise lifetime. If `S` has imprecise lifetime, `X` is protected only if "at some point after `T` but before the next store to `S`, the computation history features a load from `S` and in some way depends on the value loaded". The same protection applies to full-expression temporaries until the end of their full-expression.
- **Dependence (lines 1690-1738).** Dependence covers comparison of, loads from and stores to `P`, and pointers derived from or loaded from `P`. It "does not occur merely because a separate pointer value dynamically aliases `P`", is "not carried by values that are stored to objects", and is not created merely by passing an argument. It does propagate through pointer-typed returns; for example, ARC must not release `p` between the load of `p->ivar` and its retain.
- **No lifetime extension (lines 1743-1756).** An object dead in the formal history by an observable side effect must be dead by that side effect, "except as influenced by the re-ordering of the destruction of objects". Hence retains and releases are eliminated "only in pairs".
- **Precise lifetime (lines 1768-1788).** "By default, local variables of automatic storage duration do not have precise lifetime semantics"; `objc_precise_lifetime` opts in. The motivating example (lines 1622-1632) is `id x = _ivar; [x foo];`, whose pair is removable only if the optimizer may shorten `x`'s object.
- **Related rules.**
  - Arguments and results are neither retained nor released (lines 338-344).
  - `ns_consumed` parameters are retained by the caller and released by the callee (lines 360-379).
  - Non-init `self` is externally retained, and deallocating it during a send is "undefined behavior, or at least dangerous" (lines 2004-2011).
  - `objc_externally_retained` elides retain/release and makes the variable `const` (lines 1945-1964).
  - ARC may assume non-ARC code balances (lines 1654-1660).
  - Interior pointers (lines 2120-2155): an `objc_returns_inner_pointer` receiver lives at least until the earlier of the last use of a derived pointer and the autorelease-pool restore, except that "no extension is required if the receiver is loaded directly from a `__strong` object with precise lifetime semantics".

Basis: normative.

### 3. How Clang and LLVM carry the permission

| Location (pinned `llvm/llvm-project`) | Content |
|---|---|
| `clang/lib/CodeGen/CGDecl.cpp:2258-2260` (also 666-670) | `// Use the imprecise destroyer by default.` `if (!var->hasAttr<ObjCPreciseLifetimeAttr>()) destroyer = CodeGenFunction::destroyARCStrongImprecise;` |
| `clang/lib/CodeGen/CGObjC.cpp:347-350` | `// All variables have precise lifetime except local variables with automatic storage duration that aren't specially marked.` `return (var->hasLocalStorage() && !var->hasAttr<ObjCPreciseLifetimeAttr>());` (this predicate decides whether an interior-pointer receiver needs retain+autorelease) |
| `clang/lib/CodeGen/CGObjC.cpp:2165-2166` | `// Releases at the end of the full-expression are imprecise.` `CGF.EmitARCRelease(object, ARCImpreciseLifetime);` |
| `clang/lib/CodeGen/CGObjC.cpp:2503-2519` | `EmitARCRelease`: emits `objc_release`; `if (precise == ARCImpreciseLifetime) call->setMetadata("clang.imprecise_release", ...)` |
| `llvm/lib/Transforms/ObjCARC/PtrState.h:41-48` | `enum Sequence { S_None, S_Retain, S_CanRelease /* foo(x) -- x could possibly see a ref count decrement */, S_Use, S_Stop /* code motion is stopped */, S_MovableRelease /* objc_release(x), !clang.imprecise_release */ };` |
| `llvm/lib/Transforms/ObjCARC/PtrState.h:56-68` | `KnownSafe`: after a retain or before a release the count "is known to be positive"; pairs inside such regions "can be eliminated, regardless of any side effects between them", as can a pair nested in another pair "on the known same pointer value" |
| `llvm/lib/Transforms/ObjCARC/PtrState.cpp:189-195` | `MDNode *ReleaseMetadata = I->getMetadata(Cache.get(ARCMDKindID::ImpreciseRelease)); Sequence NewSeq = ReleaseMetadata ? S_MovableRelease : S_Stop; ResetSequenceProgress(NewSeq); if (NewSeq == S_Stop) InsertReverseInsertPt(I);` |
| `llvm/lib/Transforms/ObjCARC/ObjCARCOpts.cpp:1161-1169`, `1886-1889` | A release is pushed into non-null PHI predecessors only if tagged; moved releases keep the tag |
| `llvm/include/llvm/Analysis/ObjCARCAnalysisUtils.h:115-126` | `GetRCIdentityRoot`: strips pointer casts and forwarding calls; "two RCIdentical values must alias" |

**Reading.** The optimizer identifies *which object* by a syntactic RC-identity root computed within the function, and *whether a release may move* by one front-end bit per call site (Basis: source). Nothing here tracks which other owner keeps an object alive. "Known positive" comes only from a dominating retain or post-dominating release on the same RC identity (Basis: source + derived).

### 4. Execution: where clang 19.1.7 places releases

Probe sources and full outputs are in `support/arc/`. Each scenario prints the stand-in runtime's `retain`/`release`/`dealloc` events interleaved with marker calls. "Same" means the event order equals the `-O0` order.

| Scenario | Source shape | `-O0` order | `-O1`, `-O2`, `-O3`, `-Os` order | IR at `-O2` |
|---|---|---|---|---|
| A (imprecise) | `Obj *x = obj_new(); use(x); note(...);` (`+1`, no retain) | use, marker, release, dealloc | Same as `-O0` (release **not** hoisted above `note`) | `llvm.objc.release` with `!clang.imprecise_release` at end |
| Ap (precise) | same with `objc_precise_lifetime` | use, marker, release, dealloc | Same | release without the tag |
| B (imprecise) | `Obj *x = g; clear_global_and_check(x); note(...);` | retain, (callee: release `g`, object **alive**), marker, release, dealloc | Callee releases `g` → **dealloc inside callee**; callee sees object **deallocated** | no retain, no release in caller |
| Bp (precise) | same with `objc_precise_lifetime` | retain, callee: alive, marker, release, dealloc | Same as `-O0` | retain + untagged release kept |
| C (weak) | `Obj *x = obj_new(); __weak Obj *w = x; use(x); note(...); Obj *y = w;` | weak load returns object | Same (weak load returns object) | releases tagged, not hoisted |
| D (ARC callee) | `void f(Obj *x) { release_global(); use(x); note(...); }`, called with `g` | retain, release g, use, marker, release, dealloc | (`-O2` tested) retain, release g, use, **release, dealloc, marker** | retain kept; tagged release moved to directly after `use` |
| Interior (imprecise receiver) | `Buf *b = buf_new(); char *p = [b bytes]; ...` | `objc_retainAutorelease(b)` before send | (`-O2`) kept | — |
| Interior (precise receiver) | same with `objc_precise_lifetime` | no retain/autorelease | (`-O2`) none | — |

Basis: execution (real compiler; toy runtime that only logs reference-count operations, not a real Objective-C runtime).

Interpretation:

- **B is the specification's own motivating example.** The spec permits it: no load from `x` occurs after `T`, so rule 2 does not protect `x`'s object. The callee, a non-ARC C function, does not retain its parameter. An ARC-compiled callee would have retained it on entry. The spec relies on that ("ARC may assume that non-ARC code engages in sensible balancing behavior", lines 1654-1660).
- **D shows the second consequence.** Inside an ARC callee the parameter's retain survives, because a decrementing call (`release_global`) precedes a use. The imprecise release, however, moves up to directly after the last use and ahead of the later side-effecting `note` call. A deinitializer with an externally visible side effect would therefore run before `note`'s output.
- **A and C show the limit.** A release with no matching retain stayed at scope end, although the spec permits earlier release. The ObjCARC code examined moves releases mainly through retain/release pair motion (`MoveCalls` re-inserts releases at the pair's reverse insertion points). The one lone-release motion examined pushes tagged releases into non-null PHI predecessors (`ObjCARCOpts.cpp:1161-1169`). Basis: source + execution; established for these shapes only.

### 5. Swift: Ownership SSA, lexical lifetimes, deinit barriers

**Lifetime categories** (`docs/SIL/Ownership.md:742-820`, pinned `swiftlang/swift`):

- **Strict** (`~Copyable`): the deinit runs at consumption, or at scope end in reverse declaration order.
- **Lexical** (Copyable, non-trivial, not eager-move, or annotated `@_lexical`): "the lifetime of a named source-level value is anchored to the variable's lexical scope and confined by deinit barriers ... code motion may not move the ends of these lifetimes across a deinit barrier."
- **Optimized** (eager-move: `String`, `Array`, `Set`, `Dictionary`, all-eager-move aggregates, and `@_eagerMove`/`@_noImplicitCopy`): "the optimizer may end the lifetime ... immediately after its last use ... independent of any side-effects present in the deinitializer."

**IR representation** (lines 822-849). SILGen emits `begin_borrow [lexical]`, `move_value [lexical]` and `alloc_stack [lexical]`; function arguments can be lexical themselves. Inlining adds a lexical borrow for each `@guaranteed` argument and a lexical move for each `@owned` one, so inlining cannot drop the constraint.

**Deinit barriers.** The documentation (lines 861-897) lists four kinds:

1. synchronization points;
2. weak/unowned loads;
3. pointer accesses;
4. accesses of exclusively-checked globals or class members.

Its examples are a file handle closed in `deinit`, a weak reference that becomes `nil` if the destroy is hoisted, a buffer used after its owner's deinit, and aliasable class properties.

The source `Instruction.isDeinitBarrier` (`SwiftCompilerSources/Sources/SIL/Instruction.swift:157-200`) returns `true` for:

- every full apply site, `end_apply`, `abort_apply` and `yield`;
- weak/unowned loads and unowned/unmanaged strong copies;
- `hop_to_executor`;
- dynamic `end_access`;
- memory-accessing builtins;
- any memory access through a pointer or global (`FindPointerOrGlobalWalker`).

`OptUtils.swift:652-661` (`isBarrierForDestroy`) exempts effect-free instructions and trivial types, and refines apply sites with a callee-effects analysis. Basis: documentation + source.

**Disagreement to preserve.** `docs/SIL/ARCOptimization.md:898-960` ("Deinit Model", self-described as documenting "where things are today") says deinits "are not sequenced with regards to each other or code in normal control flow". Its example lets the optimizer swap `useC(c)` with a later global read. The pinned `isDeinitBarrier` treats a read through a global address as a barrier. This suggests the swap is not applied to a lexical `c` at this revision. Basis: derived from two pinned sources; not executed.

**Default.** `include/swift/AST/SILOptions.h:94-96` sets `LexicalLifetimes = LexicalLifetimesOption::On` ("extend object lifetime to the observable end of lexical scope"). The alternative, `DiagnosticMarkersOnly` (lines 35-44), strips the markers after raw SIL. The switch is `-enable-lexical-lifetimes=true|false` (`include/swift/Option/FrontendOptions.td:365-371`). The Swift 5.7 announcement (swift.org, 2022-09-12) says the compiler "adopted a new internal representation that tracks the lexical scope of each variable" so that common patterns "are safe without requiring programmers to explicitly use withExtendedLifetime()". Basis: source + documentation.

**Explicit primitives** (pinned sources):

| Primitive | Definition | Effect |
|---|---|---|
| `extendLifetime(_: borrowing T)` | `stdlib/public/core/LifetimeManager.swift:13-23`: `Builtin.fixLifetime(x)` | Lifetime reaches at least this point |
| `withExtendedLifetime(_:_:)` | `LifetimeManager.swift:36-46`, `70-80`: `defer { _fixLifetime(x) }; return try body()` | `x` not destroyed before `body` returns |
| `_fixLifetime` | `LifetimeManager.swift:92-98`: "so that the ARC optimizer does not shorten the lifetime of x to be before this point" | Same |
| `consume x` | SE-0366, "Implemented (Swift 5.9)": "`consume` ends the lifetime of a specific local `let`" (line 18) | Upper bound on the binding's ownership; SE-0366 notes that lexical scoping "cannot be used by itself to shorten the lifetime of function parameters" (lines 396-440) |
| `borrowing` / `consuming` | SE-0377, "Implemented (Swift 5.9)", lines 25-48 | Borrow: "caller guarantees that its argument object will stay alive for the duration of the call"; consume: callee releases. By default initializers and setters consume and other functions borrow |
| `endScope` (design) | `docs/OwnershipManifesto.md:1295-1320` | "does not promise that these things happen exactly at that point: the implementation is still free to end them earlier" |

**RC identity** (`docs/SIL/ARCOptimization.md:90-135`). An instruction is RC-identity preserving if a `retain_value` on its operand before it is equivalent to one on its result after it. This is a local, syntactic origin, analogous to LLVM's `GetRCIdentityRoot`. Basis: documentation.

### 6. Python: CPython and PyPy

**Normative.** `Doc/reference/datamodel.rst:61-76` (pinned cpython) says: "Objects are never explicitly destroyed; however, when they become unreachable they may be garbage-collected. An implementation is allowed to postpone garbage collection or omit it altogether". In an implementation-detail box: "CPython currently uses a reference-counting scheme with (optional) delayed detection of cyclically linked garbage, which collects most objects as soon as they become unreachable ... Do not depend on immediate finalization of objects when they become unreachable (so you should always close files explicitly)." The language therefore promises no release timing; promptness is an implementation property. Basis: normative.

**CPython mechanism.** At the pinned cpython, `Include/refcount.h:415-427` (default build) defines `Py_DECREF` as follows: if not immortal, `if (--op->ob_refcnt == 0) { _Py_Dealloc(op); }`. Deallocation, and hence `tp_finalize`/`__del__`, runs synchronously on the decrementing thread. In the free-threaded build (`refcount.h:366-385`), the owning thread decrements `ob_ref_local` and calls `_Py_MergeZeroLocalRefcount` at zero. Other threads call `_Py_DecRefShared`. Basis: source.

**PEP 442 (Final, Python 3.4).** "An object's finalizer is always called exactly once, even if it was resurrected afterwards. For CI [cyclic isolate] objects, the order in which finalizers are called ... is undefined" (`peps/pep-0442.rst:197-204`). Basis: normative (Final PEP).

**PEP 703 (Final, Python 3.13).** Deferred reference counting applies to "top-level functions, code objects, modules, and methods". The interpreter skips their count updates for stack pushes and pops. "The true reference count can only be safely computed when all threads are paused during cyclic garbage collection. Consequently, objects that use deferred reference counting can only be deallocated during garbage collection cycles" (`peps/pep-0703.rst:599-631`). Compatibility notes (lines 1448-1456) say that destructors and weakref callbacks for code objects and top-level functions are delayed until the next cyclic GC. Destructors of some objects accessed by multiple threads "may be delayed slightly due to biased reference counting". Basis: normative (Final PEP).

**PyPy** (documentation, pinned `pypy/doc/cpython_differences.rst`):

- Objects "are not freed instantly"; files and sockets are "not promptly closed", and buffered output can leave files "empty or truncated" (lines 14-24).
- CPython's behaviour is "a side-effect of the implementation ... programs relying on this are basically bogus" (lines 36-43).
- `__del__` timing "is not reliable or timely" (line 76).
- A weakref callback may not run when object and weakref die together (lines 85-97).
- `__del__` is called at most once, and dead cycles with `__del__` are finalized rather than put in `gc.garbage` (lines 111-121).
- A PyPy3 `memoryview` pins its exporter until GC, so resizing raises `BufferError` (lines 60-69).
- There is no automatic `gc.collect()` at exit (lines 159-162), and no `sys.getrefcount` (line 164).

Basis: documentation.

**Execution (CPython 3.13.15, GIL build; `support/python/`).**

| Scenario | Event order observed |
|---|---|
| Local held to function end, last use then marker | use → marker → `__del__` → `weakref.finalize` callback → return (released at frame exit, **not** at last use) |
| `del x` | `__del__` → marker |
| Expression-statement temporary | `__del__` → marker |
| Rebinding `x` | `__del__ first` → marker; second object at return |
| Two-object cycle with `__del__` | marker → `__del__` a, b only inside `gc.collect()` |
| Exception from inner frame caught with `as e` | `__del__` of inner-frame local after the `except` clause ends (name `e` unbound), before the next marker |
| Suspended generator inside `try/finally`, then `del` | `finally` block runs → marker |
| `open(path,'w').write('hello')`, then `del f` | file size 0 before drop, 5 after drop (flush at decrement; `ResourceWarning` under `-X dev`) |
| `socket.socket()`, then `del s` | `os.fstat(fd)` fails after drop (descriptor closed at decrement) |

Basis: execution.

**Reading.** CPython releases at the last decrement, and a frame slot holds a reference until frame exit. It therefore releases later than ARC imprecise locals or Swift eager-move values, and near scope end like Swift lexical values, except that its "scope" is the whole function. "The file is closed when its last reference dies" holds for the CPython GIL build, but not for PyPy or for free-threaded deferred-count objects (Basis: derived).

### 7. When can count operations be removed or moved?

| Condition | Decidable from local code alone? | Needs origin information (which owner keeps the object alive)? | Where it appears |
|---|---|---|---|
| Pair on the same RC identity with no intervening possible decrement | Yes (RC-identity root + side-effect classification) | No | ObjCARC `S_CanRelease` tracking; Swift ARC sequence optimization |
| Pair nested in another pair on the same pointer value, regardless of side effects | Yes | No (the enclosing pair is the owner) | ObjCARC `KnownSafe` (`PtrState.h:56-68`) |
| Pair across a possibly-decrementing call, deleted because the language allows the object to die at its last dependent use | Yes, given the contract bit | No, but it changes *when* deallocation is observed | Clang ARC imprecise lifetime (`S_MovableRelease`; probe B) |
| Release moved earlier to just after last use | Yes, given the contract bit and barrier set | No | ObjCARC (probe D); Swift lexical up to a deinit barrier; Swift eager-move unconditionally |
| Callee performs no retain/release because the caller guarantees liveness | No: requires an interface contract | **Yes** (the caller's owned reference backs the callee's borrowed one) | Swift `borrowing`/guaranteed convention; ARC `self`, `objc_externally_retained`, for-in variables; Lean-style borrowed parameters |
| Borrowed parameter must not be the subject of in-place reuse or escape via partial application | No: requires per-parameter inference | **Yes** | Ullrich and de Moura 2019, §5.2: "we must never mark x as borrowed if it is used by a `let y = reset x` instruction"; partial applications of functions with borrowed parameters are wrapped to owned |
| Removing stack-reference count updates in nondeferred RC (RC subsumption) | Per the abstract, a static analysis of stack references (full text not examined) | Unknown at the depth examined | Joisha 2006, 2007 |

Basis: source + execution + documentation. The "needs origin" column is derived.

**Derived invariant.** Deleting a retain/release pair on reference `x` over region `R` preserves memory safety iff throughout `R` the object's count is otherwise known positive. That is, some other owned reference `y` with `RCroot(y) = RCroot(x)` is live across `R`, or `R` contains no operation that can decrement it. Deleting the pair preserves *release timing* only if `R` contains no possible decrement at all. When `R` does contain one, the deletion is legal only under a contract that allows the object to die inside `R`: Clang's imprecise lifetime, or Swift's eager-move. Probes B and D are concrete instances of the timing change. They are not memory-safety violations under the ARC contract, because the non-ARC callee in B is outside the contract's balancing assumption.

**Boehm 2003 (author's slides).** "Running finalizers 'immediately' is not meaningful unless they are run from the thread overwriting the last pointer". That thread may already hold a lock the finalizer needs ("deadlock (or worse)"), so "a reference count decrement should not trigger finalization calls. Unfortunately, standard reference count libraries usually do." The slides also estimate that finalization-enabling an object raises allocation and collection cost "perhaps by 3x" (in the context of Java finalization). CPython's synchronous `__del__` on decrement is the design these slides argue against for concurrent code (Basis: documentation + derived).

### 8. Performance and resource footprint (L1–L6)

| Level | Clang ARC | Swift | CPython / PyPy |
|---|---|---|---|
| L1 authoring/maintenance | One attribute per local to pin (`objc_precise_lifetime`); not measured in LoC or person-time | `withExtendedLifetime` boilerplate "not required" for common patterns since 5.7 (announcement; no count given); not measured | `with`/`close()` discipline required for PyPy portability (docs); not measured |
| L2 toolchain build | not measured | not measured | not measured |
| L3 compile latency | Probe TU (~60 lines), 3 runs each (`support/arc/compile_time.txt`): `-O0` 0.03–0.19 s wall (first run cold), 104,412–105,676 KB max RSS; `-O2` 0.03–0.04 s, 108,956–108,996 KB [real measurement, trivial input]; ObjCARC pass time on real code not measured | not measured | n/a (interpreted); bytecode compile not measured |
| L4 generated-code execution | Number of `objc_retain`/`objc_release` calls removed in probe B at `-O1+`: 2 of 2 per call (derived from IR); cycle cost not measured | not measured | CPython 3.13.15, three preserved runs: create+drop of a `__slots__` object (best of 5 × 10⁶) 83.7–89.9 ns plain vs 126.6–138.5 ns with an empty `__del__` (+41.9 to +48.6 ns, derived per run); `gc.collect()` over 100,000 two-object cycles (200,000 objects) 56.1–64.0 ms [real measurement, one host]; PyPy not measured; free-threaded build not measured |
| L5 checking/verification speed | n/a (no certificate); not measured | n/a; not measured | n/a |
| L6 memory/footprint | Retain+autorelease of interior-pointer receivers can "significantly inflat[e] memory use" (spec rationale, lines 2158-2162; no figure); not measured | Lexical lifetimes may hold objects longer than last use (by design); not measured | Unclosed files may exhaust OS descriptor limits on PyPy (docs); deferred-count objects in free-threaded build persist until GC (PEP 703); not measured |

### 9. Comprehensibility and conceptual simplicity (C1–C2)

**C1, human mental model.**

- *Clang ARC.* The rule is local but counter-intuitive: the variable is in scope, yet its object may be dead after the last *load*. The spec says the dependence restrictions exist so that an optimizer "with only incomplete information" can apply them. Probe B shows the failure surfacing in a *different* function, so diagnostics are non-local.
- *Swift.* Lexical lifetimes restore the scope model, but a reader must also know a type's category (eager-move or `~Copyable`) to predict `deinit` timing. The source barrier set is broader than the documented one.
- *CPython.* "Freed at the last decrement" has three non-obvious exceptions: whole-function local lifetime, traceback-held frames, and cycles. PyPy drops the promise entirely.

**C2, orthogonality.** Each system separates *which object* an operation concerns from *whether its release may move*. The first is a syntactic RC identity: LLVM `GetRCIdentityRoot`, Swift RC identity. The second is a per-binding contract: the ARC metadata bit, Swift lexical/eager-move/strict, and nothing in Python.

A minimal common model is a per-binding release window `[earliest, latest]` plus a set of barrier events that a release may not cross:

- ARC imprecise: earliest = last dependent load, no barriers.
- ARC precise: earliest = latest = scope end.
- Swift lexical: earliest = last use, barriers = `isDeinitBarrier`.
- Swift eager-move: no barriers.
- CPython: earliest = latest = last decrement, with the frame slot counted as a reference.

`objc_precise_lifetime`, `withExtendedLifetime` and `consume` then become ordinary window adjustments. This framing is a derived synthesis, not a model any of these systems states.

### 10. Validation of the contracts and implementations (V1–V4)

| Axis | Evidence found | Gaps |
|---|---|---|
| V1 spec adequacy | ARC spec gives worked rationale examples (lines 1622-1632, 1715-1717); Swift `Ownership.md` gives four barrier examples; PEP 442 states exact-once finalization | No mutation or property-based testing of any contract located; not examined |
| V2 lowering/optimizer soundness | Probe compares `-O0` vs `-O1..-Os` behaviour of one compiler (a differential check, 8 shapes); LLVM has an ObjCARC test directory (not examined) | No Alive2-style or randomized differential testing of ARC release motion located; not examined |
| V3 concurrency/crash | PEP 703 discusses biased/deferred counting; Boehm slides discuss finalizer deadlock | No weak-memory model checking of retain/release or finalization located; not examined |
| V4 human-model validation | Swift 5.7 change was motivated by user-visible early-release bugs (announcement text) | No empirical study of programmer expectations of release timing located; not examined |

## Boundaries

- **Not examined:**
  - The Swift compiler was not executed. All Swift claims are source or documentation, including pre/post-5.7 behaviour and `-enable-lexical-lifetimes=false`; the SE-0366 and SE-0377 implementations were not inspected.
  - PyPy and CPython free-threaded builds were not executed.
  - Apple libobjc and GNUstep libobjc2 were not used.
  - Darwin targets, ARC exceptions, Objective-C++, blocks, LTO, autorelease-pool timing and multithreaded ARC were not tested.
  - Only clang 19.1.7 was executed, not the pinned LLVM main.
  - LLVM ObjCARC and Swift SIL test suites were not examined.
  - Literature depth:
    - Hudak 1986: bibliographic only.
    - Joisha 2006 and 2007: bibliographic plus a secondary abstract index naming "RC subsumption".
    - Joisha 2008: author-page abstract only (def/use-based uniform insertion of increments and decrements handling exceptions, interior pointers and pinning).
    - Boehm 2003: author's slides only.

    The removal conditions, correctness arguments and measurements of these papers are **not examined**, so which of Joisha's conditions need origin information is **unknown**.
- **Unknown:**
  - Whether ObjCARC ever hoists a release with no matching retain. Probes A and C showed none; that is not a proof.
  - Whether the `ARCOptimization.md` reordering example still applies to lexical values (§5).
- **Known not to apply:**
  - CPython does not release a local at last use (probe).
  - `objc_precise_lifetime` is irrelevant to non-init `self`, which is externally retained by rule.
- **Not measured:** all L1, L2, L5 and L6 cells; L3 for Swift and for ObjCARC on realistic code; L4 for Swift, PyPy, free-threaded CPython and ARC call cycles.
- **Not established:**
  - "Clang never shortens a `+1` local": shown only for one shape on one compiler.
  - "Swift guarantees deinit at scope end": false for barriers and eager-move types.
  - "CPython guarantees prompt finalization": disclaimed by the language reference.
  - "Deleting a retain/release pair is timing-neutral": probe B is a counterexample.
  - "PyPy never finalizes promptly": its documentation says only "not reliable".

## Evidence

All evidence was acquired on **2026-11-21 (UTC)**. Repositories were resolved via the GitHub commits API, and files were read at these SHAs.

- `llvm/llvm-project` @ `5a16359b417eac2413c493856d80cc2877c3f6aa` (committed 2026-11-21T03:26Z):
  - `clang/docs/AutomaticReferenceCounting.md`, lines 338-379, 1593-1796, 1945-2011, 2120-2163;
  - `clang/lib/CodeGen/CGDecl.cpp`, lines 666-670 and 2255-2261;
  - `clang/lib/CodeGen/CGObjC.cpp`, lines 340-351, 2158-2167, 2500-2520 and 2885-2913;
  - `llvm/lib/Transforms/ObjCARC/PtrState.h`, lines 36-80;
  - `llvm/lib/Transforms/ObjCARC/PtrState.cpp`, lines 174-230 and 346-375;
  - `llvm/lib/Transforms/ObjCARC/ObjCARCOpts.cpp`, lines 1155-1175 and 1878-1892;
  - `llvm/include/llvm/Analysis/ObjCARCAnalysisUtils.h`, lines 115-126.
- `swiftlang/swift` @ `876c94b16c5d1c9ff94fe67e8476a123da0d4f50`:
  - `docs/SIL/Ownership.md`, lines 742-897;
  - `docs/SIL/ARCOptimization.md`, lines 90-135 and 898-960;
  - `docs/OwnershipManifesto.md`, lines 1295-1320;
  - `stdlib/public/core/LifetimeManager.swift`, lines 13-98;
  - `SwiftCompilerSources/Sources/SIL/Instruction.swift`, lines 157-200;
  - `SwiftCompilerSources/Sources/Optimizer/Utilities/OptUtils.swift`, lines 652-661;
  - `include/swift/AST/SILOptions.h`, lines 35-44 and 94-96;
  - `include/swift/Option/FrontendOptions.td`, lines 365-371.
- `swiftlang/swift-evolution` @ `58a97fabc7233f58af6b8a1e8d3d5a25fb4f7060`: `proposals/0366-move-function.md` and `proposals/0377-parameter-ownership-modifiers.md`.
- `python/cpython` @ `dc222c8d6c366e3d52d4b0d0053ad7bb8a601fff`: `Doc/reference/datamodel.rst`, lines 56-92, and `Include/refcount.h`, lines 366-385 and 413-429.
- `python/peps` @ `4434e728a7db24540d581f52e96570ca1230356e`: `peps/pep-0442.rst` (Final, 3.4; lines 197-204) and `peps/pep-0703.rst` (Final, 3.13; lines 599-631, 1448-1456).
- `pypy/pypy` @ `dc27dd3d6d624e4516c965d450c84d3023640dba`: `pypy/doc/cpython_differences.rst`, lines 14-170.
- **Documentation URLs:**
  - https://www.swift.org/blog/swift-5.7-released/ (2022-09-12);
  - https://www.hboehm.info/popl03/slides.pdf (pages 7, 10-12);
  - the Microsoft Research publication page for MSR-TR-2007-104 (abstract only; the PDF and ACM pages were not retrievable).
- **DOIs**, each checked against Crossref metadata (title, authors, venue, year, pages) on 2026-11-21:
  - `10.1145/1133956.1133976`: ISMM 2006, pp. 150-161. Crossref splits the title into "Compiler optimizations for nondeferred reference" and the subtitle "counting garbage collection".
  - `10.1145/1296907.1296926`: ISMM 2007, pp. 141-158.
  - `10.1145/1346256.1346275`: VEE 2008, pp. 131-140.
  - `10.1145/319838.319876`: LFP 1986, pp. 351-363.
  - `10.1145/604131.604153`: POPL 2003, pp. 262-272.
  - `10.1145/3412932.3412935`: IFL 2019, pp. 1-12; also arXiv:1908.05647v3, §5.2 read.
- **Execution environment:** x86_64 Linux workstation (Debian kernel 7.1.6, 96 logical CPUs); Debian clang 19.1.7 (`10.1+build1`); CPython 3.13.15 (`Py_GIL_DISABLED=0`, gc thresholds `(2000, 10, 10)`).
- **Support material:**
  - `support/arc/`: probe sources `arc_probe.m`, `arc_callee.m`, `arc_interior.m`; the stand-in runtime `arc_stub_runtime.c`; `d_main.c`; `run_arc_probe.sh`; its full output `arc_probe_output.txt`; and `compile_time.txt`.
  - `support/python/`: `py_finalization_probe.py` and `py_probe_out.txt`.

## Revalidation

- **Clang ARC.**
  - Run `support/arc/run_arc_probe.sh` with `CC=clang-NN`. The discriminators are `callee: parameter object B is DEALLOCATED` at `-O2`, and `dealloc D` printed before `-- D: marker after use`.
  - At a new LLVM revision, run `grep -n 'S_MovableRelease : S_Stop' llvm/lib/Transforms/ObjCARC/PtrState.cpp` and `grep -n 'clang.imprecise_release' clang/lib/CodeGen/CGObjC.cpp`.
  - Re-read the spec sections `arc.optimization.liveness` and `arc.optimization.precise`.
- **Swift.**
  - Diff `Instruction.isDeinitBarrier`, the `LexicalLifetimes` default in `SILOptions.h`, and the "Variable Lifetimes" and "Deinit Barriers" sections of `Ownership.md`.
  - To close the execution gap, port probes A–D to a class with a printing `deinit`. Compile with `swiftc -O` and with `-Xfrontend -enable-lexical-lifetimes=false`, and compare the event order.
- **Python.**
  - Run `support/python/py_finalization_probe.py` under `pypy3`, `python3.13t` or a newer CPython. Compare where `__del__ local` falls relative to the marker, the file size after the drop, and the socket state after the drop.
  - Re-read the PyPy section "Differences related to garbage collection strategies" and PEP 703 "Deferred Reference Counting".
- **Literature.** Settling the Joisha and Hudak conditions requires reading the full texts; there is no cheap probe.
