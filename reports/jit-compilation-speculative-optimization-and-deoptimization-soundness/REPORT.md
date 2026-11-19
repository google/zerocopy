# Speculative JIT Compilation and Deoptimization Soundness: Guards, Global Assumptions, Frame-State Reconstruction, Virtual Objects, and the Reach of Mechanized Proofs

## Summary

A speculative just-in-time (JIT) compiler is sound exactly when every transfer out
of optimized code lands in a reference-tier (interpreter) state that the reference
semantics could have reached, with every visible effect performed exactly once.
The systems examined (SELF as published in 1992, HotSpot, Graal/Truffle/Substrate
VM, V8, PyPy/RPython, LuaJIT, CPython's experimental JIT) discharge that
obligation with the same small protocol under different names:

1. **Two kinds of speculation with different failure protocols.** A *local guard*
   (branch direction, receiver class/map, value) is checked inline; failure is an
   *eager* deoptimization that resumes **before** the guarded bytecode. A *global
   assumption* (single implementor, unmodified prototype or method table, constant
   global, "protector" cell) is **not** checked inline; the code registers a
   dependency, and when the assumption breaks the runtime must reach *every*
   activation of every dependent code object, including those suspended in a
   call. These are deoptimized *lazily*: the return address (or the code after
   the call, or a polled flag) leads to a deopt trampoline and the frame is
   rebuilt in an **after-call** state when control returns to it.
2. **Deoptimization metadata is a state relation.** At each deopt point the
   compiler records how to compute one or more reference frames (inlined callers
   included), the resume position kind (re-execute / after call / rethrow), the
   locked monitors, and descriptions of objects whose allocation was removed.
3. **Scalar replacement moves allocation into the deoptimizer.** The runtime must
   allocate elided objects at deopt time, preserve identity (one object per
   virtual object, also across earlier stack inspection), rebuild cyclic graphs
   (allocate all, then initialize), survive a GC triggered by its own
   allocations, re-acquire elided monitors in a legal order, and handle allocation
   failure.
4. **"Not entrant" is not "deoptimized".** A failed local guard need only stop
   new entries: other activations stay correct because each checks its own
   guards. A broken global assumption invalidates all activations, even of code
   that is already not entrant. The model here detects conflating the two.
5. **Meta-compilation trades engine-specific compilers for trusted annotations.**
   RPython hints (`elidable`, `promote`, green/red variables) and Truffle
   directives (`@CompilationFinal`, `@TruffleBoundary`, `Assumption`,
   `transferToInterpreter`) are unchecked assertions with documented contracts.
   Copy-and-patch is a code-generation technique, orthogonal to speculation.
6. **Mechanized results stop well short of production features.** CoreJIT
   (POPL 2021, Coq) proves a backward-simulation theorem for speculation insertion,
   constant propagation and inlining on an IR with explicit `Anchor`/`Assume`
   instructions; its LLVM backend is unverified. FM-JIT (POPL 2023, Coq) proves
   native code generation by reusing CompCert's backend, but does not insert
   speculation or inline, and synthesizes one frame per deopt. Neither models
   virtual objects, global invalidation of suspended frames, OSR entry, garbage
   collection or concurrent compilation.
7. The probe `support/verify_speculative_deopt_simulation.py` is a runnable
   model of items 1 to 4. It checks observational equivalence against a
   small-step interpreter in 3,501 mixed-mode runs (3,322 with forced
   deoptimizations) and shows that 13 deliberately broken variants are each
   detected.

## Applicability

**Subjects and their relationship.** `REPORT.json` lists eight Git repositories at
pinned commits and nine publications. The repositories are independent systems
that are *compared*: `v8/v8`, `openjdk/jdk` (HotSpot), `oracle/graal` (Graal
compiler, Truffle, Substrate VM), `pypy/pypy` (RPython meta-tracing JIT),
`python/cpython` (development tree reporting version `3.16.0a2+dev`),
`LuaJIT/LuaJIT`, and the Coq developments `Aurele-Barriere/CoreJIT` and
`Aurele-Barriere/FM-JIT`. The publications are read as the designers' own
descriptions of those systems or their ancestors. Source statements apply to the
pinned commits only (development heads on 2026-11-19; CoreJIT and FM-JIT were
last changed in 2022). No engine was built or run: every engine claim comes from
reading source, comments and papers.

**What is exact and what is generalized.** Quoted comments, enum members and line
ranges are exact observations. The cross-engine protocol in Findings 1 and 9 is a
*derived* synthesis, supported by each engine having an identifiable
implementation of each role, not by any engine documenting the abstraction. The
probe is a model written for this report: it characterizes the protocol, not any
engine, and its guest language (register bytecode, flat method tables, recursive
monitors, single thread) is far simpler than JavaScript, Java or Python.

**Configuration notes.** HotSpot object rematerialization and relocking sit in
`#ifdef COMPILER2` blocks and depend on `DoEscapeAnalysis`, `EliminateAllocations`,
`EliminateLocks` and related flags; the commit also contains value-class paths
(`realloc_value_type_result`) that were not studied. V8 statements cover the
deoptimizer shared by Maglev and Turbofan code, not WebAssembly deoptimization.
CPython's JIT is opt-in at build time (`--enable-experimental-jit`).

**Bibliographic coordinates that are easy to get wrong** (per Crossref).
"Formally Verified Speculation and Deoptimization in a JIT Compiler"
is by Barrière, Blazy, Flückiger, Pichardie and Vitek (PACMPL 5(POPL), article
46, 2021). "Formally Verified Native Code Generation in an Effectful JIT: Turning
the CompCert Backend into a Formally Verified JIT Compiler" is by Barrière, Blazy
and Pichardie (PACMPL 7(POPL), article 9, 2023): a POPL paper, not an OOPSLA or
PLDI one. Their artifacts are CoreJIT and FM-JIT; a third repository, JIThm, is
described by its README as a fork of FM-JIT "with some added features of
CoreJIT". "Deoptless" (PLDI 2022) has DOI 10.1145/3519939.3523729.

**Adjacent corpus packages.** Verified JITs *without* speculation (Jitk,
Jitterbug, CertrBPF for eBPF) are covered by
`ebpf-certificate-verifying-kernels-and-verified-jits-2014-2026`; simulation
directions, CompCert pass structure and translation validation for *static*
optimizers by `verified-and-validated-compiler-optimization-precedents`. This
report does not repeat their tables; it adds what exists only in a speculative,
mixed-mode setting.

## Findings

### 1. One protocol under several vocabularies

| Role | SELF (1992 paper) | HotSpot | Graal / Truffle / Substrate | V8 | RPython / PyPy | LuaJIT | CPython JIT | CoreIR (CoreJIT) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| Point where state is recoverable | interrupt point | safepoint with debug info, uncommon trap | node carrying a `FrameState` | deopt exit with a translation | guard with resume data | snapshot | `_DEOPT`, `_EXIT_TRACE` side exit | `Anchor` |
| State description | scope descriptors + PC map | `ScopeDesc`, `ScopeValue`, `MonitorInfo` | `FrameState` (`outerFrameState`, `values`, `monitorIds`, `virtualObjectMappings`) | `TranslationOpcode` stream | `rd_numb`, `rd_virtuals` | `SnapShot`, `SnapEntry` | exit data and target | deopt target, varmap, extra frames |
| Removed allocation | not described | `ObjectValue` in scope | `VirtualObjectNode` + `EscapeObjectState` | `CAPTURED_OBJECT`, `DUPLICATED_OBJECT` | `VirtualInfo` family | `RID_SUNK` | not examined | none |
| Global assumption | dependency links | `Dependencies::DepType` | `Assumption` / `OptimizedAssumption` | `DependentCode` groups, protector cells | quasi-immutable field + `GUARD_NOT_INVALIDATED` | trace flush functions (`lj_trace_flushproto`, `lj_trace_flushall`); triggers not examined | executor `valid` flag + bloom filter | none ("non-local assumption checks" listed as future work) |
| Reaching suspended frames | return address rewritten | `frame::deoptimize` patches PC to deopt handler | lazy deopt stub replaces return address | `ReplacePC` with safepoint trampoline | guard code activated in place; `GUARD_NOT_FORCED` | not examined | `_CHECK_VALIDITY` re-checked after escaping instructions | none |

A row names the artifact that plays the role; it does not imply equal
guarantees. "none": the cited description of the system has no such role; "not
examined": the relevant files were not read.

Basis: source (pinned commits, files cited in Evidence) + documentation (papers) +
derived (the alignment of roles across systems).

### 2. Local guards: inline caches, type feedback, and what a passing guard licenses

- The polymorphic inline cache (PIC) paper describes a "specially-generated stub
  routine" that caches "all lookup results for a given polymorphic call site",
  and classifies sends as monomorphic, polymorphic or megamorphic. It reports a
  median speedup of 11% from PICs alone and 27% when the compiler recompiles
  using the receiver types recorded in PICs. The same record is thus both a
  dispatch accelerator and the *profile* that later speculation is built from.
- A guard licenses only facts that cannot change while the guarded value is
  live. A receiver-class (map, shape) check proves the object's layout; it does
  not prove that the class's method table or prototype chain still holds what
  the compiler saw. That second fact is a global assumption (Finding 3). The
  probe's scenario `midcall_method_mutation_lazy_deopt` separates the two: the
  class guard keeps passing after the method table is mutated, and only the
  dependency protocol prevents the stale inlined body from running.
- HotSpot separates cause from policy. `DeoptReason` includes
  `Reason_class_check`, `Reason_bimorphic`, `Reason_range_check` and
  `Reason_unstable_if` ("a branch predicted always false was taken");
  `DeoptAction` ranges over `Action_none` ("just interpret, do not invalidate
  nmethod"), `Action_maybe_recompile`, `Action_reinterpret`,
  `Action_make_not_entrant` and `Action_make_not_compilable`. The action decides
  whether future entries are affected.
- CPython distinguishes two exits with different tiering consequences: a "side
  exit" generated by `EXIT_IF` "may trigger recording of another trace", while a
  "deopt" generated by `DEOPT_IF` "does not trigger recording".

Basis: documentation (PIC paper; CPython `InternalDocs/jit.md`) + source (HotSpot
`deoptimization.hpp`) + execution (probe scenario) + derived (guard/assumption
distinction).

### 3. Global assumptions: registration, install-time validation, invalidation

**Kinds of assumption.** HotSpot's `Dependencies::DepType` members are
`evol_method`, `mismatch_calling_convention`, `leaf_type` ("A context type CX is a
leaf it if has no proper subtype"), `abstract_with_unique_concrete_subtype`,
`unique_concrete_method`, `unique_implementor`, `no_finalizable_subclasses` and
`call_site_target_value`. V8's `DependentCode::DependencyGroup` has ten members,
among them `kPrototypeCheckGroup` ("code objects that omit run-time prototype
checks"), `kPropertyCellChangedGroup`, `kFieldTypeGroup`, `kFieldConstGroup` and
`kInitialMapChangedGroup`; the compiler-side list in
`compilation-dependencies.cc` has 21 kinds including `Protector`, `StableMap` and
`PrototypeProperty`. V8 protectors are property cells holding
`kProtectorValid = 1` or `kProtectorInvalid = 0` (for example
`ArraySpeciesProtector`, `NoElementsProtector`, `PromiseThenProtector`).

**Three steps every implementation has.**

1. *Register.* Truffle's paper states the contract most directly: the compiler
   "intrinsifies `isValid` to a no-op, i.e., no code is emitted for it. Instead,
   the compiler adds the compiled code to a dependency list stored in the
   assumption object."
2. *Validate at install time,* because compilation ran against a heap that kept
   changing. HotSpot's `ciEnv::validate_compile_task_dependencies` ("Check for
   changes during compilation (e.g. class loads, evolution, breakpoints, call
   site invalidation)") fails the compile with "concurrent class loading";
   `InstanceKlass::add_to_hierarchy` notes "The compiler reads the hierarchy
   outside of the Compile_lock." V8's `CompilationDependencies::Commit` says
   "Check each dependency's validity again right before installing it". Truffle's
   `OptimizedAssumption` closes the window differently: `registerDependency()`
   returns a *pending* entry before the code exists, `invalidateImpl` blocks in
   `awaitDependency()` until the compilation supplies the installed code, and if
   the assumption is already invalid `registerDependency()` returns `null`, "in
   which case the caller (e.g., the compiler) must ensure the dependent code is
   never executed."
3. *Invalidate and reach running code.* HotSpot:
   `add_to_hierarchy` calls `CodeCache::mark_dependents_on(&deopt_scope, this)`
   under `Compile_lock`, then `deopt_scope.deoptimize_marked()` outside it;
   `Deoptimization::deoptimize_all_marked` makes the marked methods not entrant
   and runs `deoptimize_marked_methods()` on every Java thread (at a safepoint or
   by handshake), which walks the stack and calls `frame::deoptimize`; that saves
   the original PC (`nm->set_original_pc(this, pc())`) and patches the frame's PC
   to `nm->deopt_handler_entry()`. V8:
   `PropertyCell::InvalidateProtector` stores `kProtectorInvalid` and calls
   `DependentCode::DeoptimizeDependencyGroups(..., kPropertyCellChangedGroup)`,
   which marks code (`SetMarkedForDeoptimization`) and calls
   `Deoptimizer::DeoptimizeMarkedCode`; its `ActivationsFinder` visits the current
   and all archived threads' stacks, looks up the safepoint entry for each
   optimized frame's PC, and replaces the PC with the entry's `trampoline_pc`
   ("Replace the current pc on the stack with the trampoline"), or, where return
   addresses must not be rewritten (`v8_flags.cet_compatible`, fast C calls),
   patches the code after the call (`Deoptimizer::PatchToJump`). PyPy:
   `QuasiImmut.invalidate` marks every registered loop token and calls
   `cpu.invalidate_loop`, specified as "Before this call, all
   GUARD_NOT_INVALIDATED do nothing; after this call, they all fail." CPython:
   `_Py_Executors_InvalidateDependency` scans a contiguous bloom-filter array
   (an over-approximation that can only invalidate too much) and clears `vm_data.valid`; traces poll it with
   `_CHECK_VALIDITY`, defined as `DEOPT_IF(!current_executor->vm_data.valid)`.
   The optimizer keeps exactly the checks a lazy protocol needs:
   "`_SET_IP` is needed if the following instruction escapes or could error.
   `_CHECK_VALIDITY` is needed if the previous instruction could have escaped."

**Invariants (derived, each exercised by the probe).**

| Id | Invariant | Symptom when violated |
| --- | --- | --- |
| G1 | Every fact used without an inline check has a registered dependency. | Stale constant or stale inlined callee forever. |
| G2 | Invalidation reaches all activations, not only future entries. | Suspended frame resumes after the call with stale facts. |
| G3 | G2 holds even if the code is already not entrant for another reason. | Recursive activations of once-deoptimized code keep stale facts. |
| G4 | Code that breaks its own assumption must leave optimized code immediately after the effect. | The running frame continues with stale facts until its next exit. |
| G5 | A suspended frame is rebuilt in an after-call state: the callee's effects and return value are kept, the call is not repeated. | Duplicated or lost callee effects. |

Basis: source (HotSpot, V8, Graal, PyPy and CPython files listed under Evidence)
+ documentation (Truffle PLDI 2017 section 3.3) + execution (probe mutants
`no_dep_registration`, `no_stack_patch`, `skip_patch_if_not_entrant`,
`no_self_check`, `reexecute_call`, `drop_retval`) + derived (invariant table).

### 4. Rebuilding reference frames: resume positions, inlined frames, frame growth

**The 1992 design already has the structure of frame reconstruction.** Hölzle, Chambers and
Ungar restrict suspension to *interrupt points* ("method prologues ... and the end
of loop bodies ('backward branches')") so that "the compiler may perform any
optimization whose effects either do not reach an interrupt point or can be undone
at that point." The compiler emits *scope descriptors* "for the initial source
method and all methods inlined within it" plus "a mapping between physical and
virtual program counters". Deoptimization of a frame in the middle of the stack
is deferred: "the return address of g (the stack frame called by f) is changed to
point to a routine which will transform f when g returns", which "simplifies the
transformation process because no other stack frames need to be adjusted even if
deoptimization causes the stack frames to grow in size." The cost is also
stated: "dead stores cannot be eliminated, and the registers of dead variables
cannot be reused without spilling the variable to memory first" unless "there is
no interrupt point within the variable's scope", and the compiler performs no
tail-call elimination because "it is not possible to reconstruct the stack
frames eliminated by these optimizations."

**Resume position is part of the metadata, not implied by the PC.**

| System | Encoding | Meaning |
| --- | --- | --- |
| HotSpot | `ScopeDesc::should_reexecute()`; `Unpack_deopt`, `Unpack_exception`, `Unpack_uncommon_trap` ("redo last byte code (C2 only)"), `Unpack_reexecute` (C1 only), `Unpack_none` | Only the top frame may re-execute: `vframeArray.cpp` asserts "reexecute allowed only for the top frame"; callers resume after their call. |
| Graal | `FrameState.StackState`: `BeforePop` ("Arguments to the current bytecode are on the top of stack"), `AfterPop` ("primarily used for deopt at call sites since the arguments have been consumed but the return value will come implicitly from the callee return value"), `Rethrow` | Same three cases as HotSpot's reexecute / during-call / rethrow bits. |
| V8 | Frame kinds in the translation: `INTERPRETED_FRAME_WITH_RETURN` / `_WITHOUT_RETURN`, `BUILTIN_CONTINUATION_FRAME`, `JAVASCRIPT_BUILTIN_CONTINUATION_FRAME`, two construct-stub frames, `INLINED_EXTRA_ARGUMENTS`; `DeoptimizeKind` = `kEager`, `kLazyAfterFastCall`, `kLazy` | Besides interpreter frames, a translation can describe *continuation* frames (`frame-states.h`: "Represents a continuation to a stub"; "a lazy deopt continuation for a JS to Wasm call"), so a resume position need not be a bytecode offset. |
| CoreIR | `Assume` refers to an earlier `Anchor` | "Assume does not have to be placed right after an Anchor instruction. This will cause deoptimization to appear to jump back in time and some instructions will be executed twice. It is up to the compiler to ensure these re-executed instructions are idempotent." |

**One optimized frame becomes many.** HotSpot's `fetch_unroll_info_helper`
collects "a growable array of VFrames where each VFrame represents an inlined Java
frame", rematerializes objects, relocks, then builds a `vframeArray`, under the
rule "we MUST NOT stop at a safepoint once the vframeArray is created". V8's
`DoComputeOutputFrames` iterates the translated frames and dispatches on frame
kind (`DoComputeUnoptimizedFrame`, `DoComputeInlinedExtraArguments`,
`DoComputeBuiltinContinuation`, two construct-stub cases). RPython's `blackhole_from_resumedata` builds "a
chain of blackhole interpreters whose length is given by the positions in the
numbering".

**Reference frames can be larger than the optimized frame.** V8 documents the
resulting stack-limit invariant as "fairly tricky to guarantee, since the size of
an optimized frame and its deoptimized counterparts usually differs"; optimized
code compensates "by applying an offset to stack checks".

**Lazy deopt and code validity are separate decisions.** V8's deoptimizer comments
"Lazy deopts don't invalidate the underlying optimized code since the code object
itself is still valid (as far as we know); the called function caused the deopt,
not the function we're currently looking at", and
`IsDeoptimizationWithoutCodeInvalidation` lists reasons
(`kPrepareForOnStackReplacement`, `kOSREarlyExit`) for which "no actual
assumptions in the Maglev code object are violated".

Basis: documentation (Hölzle et al. 1992 sections 2.1, 3.1, 3.3, 3.4; CoreJIT paper
section 3) + source (HotSpot, Graal, V8 and PyPy files listed under Evidence) +
execution (probe: up to 4 interpreter frames rebuilt from one optimized frame;
mutants `skip_instruction`, `reexecute_call`).

### 5. Virtual objects at deoptimization time

Kotzmann and Mössenböck state the root cause: "Since the interpreter does not know
about the scalar replacement and synchronization removal performed by the
compiler, the deoptimization framework was extended to reallocate and relock
objects on demand", by extending the debugging information with "information
about the fields of eliminated objects and about which objects must be locked."

| Obligation | Where each engine discharges it |
| --- | --- |
| M1. One heap object per virtual object, shared by all references and frames | V8: `DUPLICATED_OBJECT` is a back-reference to an earlier `CAPTURED_OBJECT`; `ResolveCapturedObject`. LuaJIT `lj_snap_restore`: "De-duplicate sunk allocations". PyPy `getvirtual_ptr`: per-resume `virtuals_cache`. |
| M2. Cyclic and nested virtual graphs | V8: `MaterializationState` `kUninitialized` → `kAllocated` → `kFinished`; `EnsureObjectAllocatedAt` allocates the whole reachable group with a worklist, `InitializeObjectAt` fills fields afterwards under `DisallowGarbageCollection`. PyPy: "the allocate() methods must fill in the cache as soon as they have the object, before they fill its fields." RPython resume data is described as supporting "virtuals with arbitrary cycles". |
| M3. Allocation during deopt can trigger GC | V8 `MaterializeHeapObjects`: "Materialization can cause a GC. Clear the raw heap pointers, keeping a handle to the Code." HotSpot `rematerialize_objects`: "Reallocation may trigger GC. If deoptimization happened on return from call which returns oop we need to save it since it is not in oopmap." Substrate lazy deopt: frame construction "is interruptible and involves allocation", so an object-valued `gpReturnValue` "must be explicitly turned into an object reference so that the GC is aware of said reference." |
| M4. Elided monitors are re-acquired, once, in order | HotSpot `restore_eliminated_locks`: "Start locking from outermost/oldest frame", guarded by `assert(!EscapeBarrier::objs_are_deoptimized(...), "must relock just once")`; `relock_objects` inflates the lock because "We have lost information about the correct state of the lock stack." Graal partial escape analysis forbids late materialization that would reorder locks under lightweight locking: "We materialize all virtual objects that potentially get materialized in subsequent control flow point and hold locks with lock depth smaller than `lockDepth`." |
| M5. Identity is stable across stack inspection before the deopt | V8 `StoreMaterializedValuesAndDeopt`: an object materialized for inspection of a live optimized frame is kept in the `MaterializedObjectStore` keyed by frame pointer, the function is lazily deoptimized (`kFrameValueMaterialized`), and `UpdateFromPreviouslyMaterializedObjects` reuses the object. HotSpot `deoptimize_objects_internal`: "Deoptimize objects, that is reallocate and relock them, just before they escape through JVMTI" (`Unpack_none`: "not deoptimizing the frame, just reallocating/relocking for JVMTI"). PyPy `force_now`: "Implemented by forcing *all* virtualrefs and the virtualizable", and the forced objects are kept "for later blackholing from the future failure of the GUARD_NOT_FORCED". |
| M6. Allocation failure during deopt | HotSpot threads a `realloc_failures` flag through `rematerialize_objects`, `create_vframeArray` and `pop_frames_failed_reallocs`. |
| M7. Moving an allocation is observable through its failure point and identity | Truffle `CompilerDirectives.ensureAllocatedHere`: "Prevents the compiler from moving an allocation, enabling precise `OutOfMemoryError` exception locations." `@ValueType`: "Reference comparisons (==) between instances of those classes have undefined semantics". |

Ordering in HotSpot's `fetch_unroll_info_helper` is: collect virtual frames;
rematerialize (allocation, GC possible); enter `NoSafepointVerifier` ("Ensure that
no safepoint is taken after pointers have been stored in fields of rematerialized
objects"); relock; build the `vframeArray`. Allocation precedes the no-safepoint
region because it may collect; everything after must not.

Sinking is partial by design: Graal's `PartialEscapeClosure` materializes at
escape points, merges, phis and loop exits (`COUNTER_MATERIALIZATIONS_MERGE`,
`_PHI`, `_LOOP_EXIT`), and LuaJIT's pass first marks "all non-sinkable
allocations" and then sinks the rest "and the related stores". In the probe's `sunk_allocation_partial_escape` the interpreter allocates 12 objects
and the mixed-mode run 7 (five iterations allocate nothing; once the rare branch
has been seen, each side exit must materialize).

Basis: documentation (Kotzmann and Mössenböck 2005) + source (V8, HotSpot, Graal,
Substrate, PyPy and LuaJIT files listed under Evidence) + execution (probe
mutants `dup_materialize`, `shallow_materialize`, `no_relock`).

### 6. On-stack-replacement entry

OSR entry mirrors deoptimization: reference state flows *into* optimized code at
a loop header.

- HotSpot (`SharedRuntime::OSR_migration_begin`, "called from very start of a
  compiled OSR nmethod"): "A temp array is allocated to hold the interesting bits
  of the interpreter frame. The active object monitor oops and caches, and active
  interpreter locals are copied into the temp buffer. ... All of this is done NOT
  at any Safepoint, nor is any safepoint or GC allowed." Monitors are part of the
  transferred state, as they are for deoptimization.
- V8 Turbofan (`OsrHelper::SetupFrame`): "The optimized frame will subsume the
  unoptimized frame. Do so by reserving the first spill slots." Maglev code that
  wants to OSR into Turbofan does so "by first deoptimizing in order to restore
  the unoptimized frame layout", so optimized-to-optimized OSR is composed from
  deopt followed by OSR entry.
- CPython replaces the hot `JUMP_BACKWARD` with `ENTER_EXECUTOR`; hotness is also
  detected at `RESUME`.
- Two invariants follow (derived): code entered at a loop header may assume only
  what holds on *every* arrival at that header, not what held on first entry;
  and values carried around the back edge must be transferred as a parallel
  assignment. The probe's mutants `osr_assumes_preloop_constants` and
  `sequential_loop_moves` violate them and are detected (the first by
  non-termination, the second by a wrong trace in a register-swap loop).
- CoreJIT does not model OSR entry: "a production JIT would also support
  transfers of control into optimized code".

Basis: source (HotSpot `sharedRuntime.cpp`; V8 `compiler/osr.cc`,
`deoptimize-reason.h`; CPython `InternalDocs/jit.md`) + documentation (CoreJIT
paper, introduction) + execution (probe) + derived (the two invariants).

### 7. Meta-tracing, partial evaluation and copy-and-patch

| Aspect | Meta-tracing (RPython, PyPy) | Partial evaluation (Truffle on Graal) | Copy-and-patch (Xu and Kjolstad; CPython) |
| --- | --- | --- | --- |
| What the language implementer writes | A bytecode interpreter in RPython plus hints | A self-specializing AST interpreter in Java plus directives | Per-operation templates compiled ahead of time into binary "stencils" |
| How compiled code is derived | Trace the *interpreter* while it runs one iteration of a guest loop; "One crucial point is to unroll the bytecode dispatch loop, based on two hints" (`jit_merge_point`, `can_enter_jit`; `JitDriver(greens=..., reds=...)`) | First Futamura projection: partially evaluate the interpreter with the specialized AST as constant input; "PE stops at calls to ... methods that are annotated with ... `PEBoundary`" | Concatenate stencils and patch "holes" (constants, addresses) recorded as relocations |
| Where speculation comes from | Guards "at every possible point where the path could have followed another direction"; promotion; quasi-immutable fields | Interpreter-recorded specializations treated as stable (`PEFinal` in the paper, `@CompilationFinal` in the API); `Assumption` objects | None in the technique itself; the paper names "type profiling, type speculation, and inline caching" as future combination |
| Trusted, unchecked inputs | `@elidable`: "it's fine to remove the call completely if we can guess the result"; "the function call can be moved around by optimizer, but only so it'll be called earlier and not later"; side effects must be idempotent | "The interpreter is allowed to write the field, but compiled code must not write to it. Every write must be preceded by a call to the intrinsic method `transferToInterpreter`"; `@TruffleBoundary`; `@ExplodeLoop` | Calling convention and tail-call behaviour of the host C compiler |
| Documented failure behaviour | Applying "an unmodified tracing JIT to a program that is itself a bytecode interpreter results in very limited or no speedup" | `@ExplodeLoop`: "loops without a constant number of iterations will cause the compiler to bailout due to the graph exceeding maximum size"; a simple PE without the primitives "leads to code explosion" or "mediocre performance" | CPython stencils must be built with LLVM (version 21 at the examined commit), although users need no LLVM at run time |

Further verified details:

- Truffle PLDI 2017 reports speedups "relative to the V8 JavaScript VM is 0.83x,
  relative to JRuby is 3.8x, and relative to GNU R is 5x".
- Copy-and-patch's stencils "use continuation-passing style" and, "Combined with
  the GHC calling convention ... in which all registers are saved by the caller
  and all parameters are passed in registers, continuation-passing removes most
  of the calling overhead between stencils." The paper reports code generation
  "two orders of magnitude faster than LLVM -O0" on TPC-H, and a WebAssembly
  compiler that "generates code 4.9X-6.5X faster than Liftoff" with output
  "39%-63%" faster on Coremark and PolyBenchC.
- CPython at the examined commit: `Tools/jit/template.c` declares the stencil
  function `__attribute__((preserve_none))` and chains stencils with
  `__attribute__((musttail)) return`; `Python/jit.c` (POSIX branch) allocates
  memory `PROT_READ | PROT_WRITE`, applies `patch_*` relocation functions, then
  `mark_executable` switches it to `PROT_EXEC | PROT_READ`, matching PEP 744's
  "at no point is the data both writable and executable". The front end is a
  trace recorder over micro-ops (`InternalDocs/jit.md`), so the system combines
  trace selection with copy-and-patch code generation.
- Warm-up is not guaranteed to converge: Barrett et al. found that "at most
  43.5% of <VM, Benchmark> pairs consistently reach a steady state of peak
  performance".

Basis: documentation (Bolz et al. 2009; Würthinger et al. 2017; Xu and Kjolstad
2021; PEP 744; Barrett et al. 2017 abstract; CPython `InternalDocs/jit.md`,
`Tools/jit/README.md`) + source (PyPy `rlib/jit.py`; Graal
`CompilerDirectives.java`, `ExplodeLoop.java`; CPython `template.c`, `jit.c`).

### 8. What mechanized proofs establish

| Work | Mechanization | Proved | Explicitly outside the proof |
| --- | --- | --- | --- |
| Sourir (Flückiger et al., POPL 2018) | None mentioned in the paper text; the FM-JIT paper says CoreJIT later "mechanized these formal semantics" | An IR with `assume` instructions and versions of functions; two invariants: *version equivalence* ("all versions of a function are observationally equivalent") and *assumption transparency* ("even if the assumption predicates do hold, deoptimizing to the target should be correct"); "at every assume the varmap provides a complete mapping from the new version to the base. This simulation relation between versions is our correctness argument." | Native code, runtime system. |
| CoreJIT (Barrière et al., POPL 2021) | Coq, extracted to OCaml | For any optimization heuristics `h` and source program `p`, if `p` is safe then every behavior of the JIT execution is a behavior of `p` (backward property over termination, divergence and I/O traces). Passes: constant propagation, inlining, and "a speculative optimization pass" (Anchor insertion, Assume insertion). Technique: *nested simulations* (an internal backward simulation between the source program and the current optimized program is the invariant of the external simulation), *loud* instrumented semantics for the nondeterministic `Anchor`, and delay invariants. | "We do not prove the native code generation ... as we use LLVM for a backend"; the Lua frontend; "a production JIT would also support transfers of control into optimized code, and non-local assumption checks." |
| FM-JIT (Barrière, Blazy, Pichardie, POPL 2023) | Coq, extracted to OCaml, primitives in C | A JIT with interpretation and dynamically generated x86 code whose behaviors are behaviors of the source program; impure components are specified as primitives through "a variation of free monads"; CompCert's backend and proofs are reused by "generating RTL programs" that use the primitives and custom calling conventions. | "The insertion of dynamic speculation is out of scope"; "the Anchor instruction ... has been removed"; "`Assume` ... is simplified to only allow the synthesis of a single stackframe at once"; "FM-JIT does not perform inlining"; the C primitive implementations "are also not proved correct". |
| Myreen (POPL 2010); Jitawa (Myreen and Davis, ITP 2011) | Proof assistant not determined here | 2010, per the CoreJIT paper's summary: a verified JIT "from a stack-based bytecode to x86" with "an operational semantics for self-modifying x86 code". 2011: a verified Lisp runtime of "7,500 lines of machine code" in which "functions are just-in-time compiled to native x86 machine code". | Speculation and deoptimization (the CoreJIT paper names them as its difference from the 2010 work); Jitawa was read only in abstract and introduction. |

Coverage gap (derived). The native-code, speculation-insertion, inlining,
single-frame, OSR-entry and non-local-assumption cells restate the authors'
limitations quoted above; other "no" cells mean the feature does not appear in
the IR and theorem as presented:

| Production feature | Sourir | CoreJIT | FM-JIT |
| --- | --- | --- | --- |
| Guard insertion with deopt metadata | modeled | proved | consumes pre-inserted `Assume` only |
| Multi-frame synthesis for inlined callers | modeled (extra frames) | proved (inlining pass) | no |
| Native code generation | no | unverified LLVM | proved via CompCert |
| Virtual objects / allocation sinking | no | no | no |
| Global assumptions and lazy invalidation of suspended frames | no | no | no |
| OSR entry | no | no | no |
| Garbage collection, moving objects during deopt | no | no | no (heap is "a fixed-size array of 64-bit integer values") |
| Concurrent compilation and install-time validation | no | no | no |

For the non-speculative end of the spectrum see
`ebpf-certificate-verifying-kernels-and-verified-jits-2014-2026`; for the
forward/backward simulation vocabulary used here see
`verified-and-validated-compiler-optimization-precedents`.

Assumption transparency and CoreJIT's nondeterministic `Anchor` both say that
deoptimizing must be correct *even when the guard's predicate is true*. That
gives a cheap testing principle (force any deopt point to fire), which is the
basis of the probe's sweep.

Basis: documentation (the cited papers; quotes verified in author-hosted or arXiv
full texts) + source (CoreJIT `Readme.md`, FM-JIT and JIThm `README.md`: file
layout and naming only; the Coq proofs were not rebuilt) + derived (gap table).

### 9. Deopt metadata, debug information, stack maps and simulation relations

The claim that these four artifacts encode one relation between machine state and
source state is a **derived** reading. The supporting observations are:

- *Deopt metadata was debug information first.* The 1992 deoptimizer consumes the
  debugger's scope descriptors; Kotzmann and Mössenböck extended HotSpot's
  "debugging information"; Graal's `FrameState` javadoc says it "can be used as
  debug or deoptimization information."
- *Deopt metadata and GC maps are co-located and share PCs.* A V8 safepoint
  table entry stores, per PC, the collector's stack map and, "if this entry has a
  deopt index", the `deopt_index_delta` and `trampoline_delta` used for lazy
  deoptimization. Substrate VM swaps one for the other: after eager deopt "the
  frame of the deoptimized method is no longer valid and the GC will ignore it.
  Instead, the GC will also visit the reference to the `DeoptimizedFrame`".
- *Deopt metadata is the simulation witness.* Sourir: "This simulation relation
  between versions is our correctness argument." CoreJIT's Assume-insertion proof
  relies on the inserted `Assume` and its `Anchor` sharing "the same
  deoptimization metadata", so "they deoptimize to the same semantic state".

| Encoding | Consumer | Must be exact? | Must be complete? |
| --- | --- | --- | --- |
| Deopt frame state | Deoptimizer rebuilding executable state | Yes: execution resumes from it | For every value the reference tier can still read at that point (V8's translation has an `OPTIMIZED_OUT` opcode for the others; the probe drops registers that are dead in the reference tier) |
| GC stack map | Collector | Yes, for which slots hold references | For every live reference in the optimized frame |
| Debug location information | Human or tool inspecting state | Best effort in static compilers | No: "optimized out" is acceptable |
| Simulation relation | Proof | Yes | Quantifies over all reachable states |

Practical reading: a pass that preserves deopt frame states already maintains
the data its simulation proof needs, and a pass that cannot express its effect
on the frame state (tail-call elimination in SELF, lock reordering in Graal) has
no expressible simulation relation at that point. The debug-information row is
an analogy to static compilers; no DWARF producer was examined.

Basis: derived, from documentation (Hölzle et al. 1992; Kotzmann and Mössenböck
2005; sourir and CoreJIT papers) + source (Graal `FrameState.java`; V8
`safepoint-table.h`, `translation-opcode.h`; Substrate `Deoptimizer.java`).

### 10. Executable model: checked invariants and negative controls

`support/verify_speculative_deopt_simulation.py` (Python 3.10+, standard library
only) implements a guest register bytecode with heap objects, mutable per-class
method tables (`setmethod`), recursive monitors, globals and an output trace; a
small-step reference interpreter; a profile-directed compiler for function
entries and loop headers with inlining, branch and class guards, global-constant
folding and devirtualization under registered dependencies, and allocation and
monitor sinking; and a deoptimizer for eager, lazy, self-invalidation and
side-exit transfers.

Deoptimization metadata in the model is a snapshot per deopt point:

```text
Snap.kind      'before' (re-execute top instruction) | 'after_call' (result -> wait_dst)
Snap.frames    outermost-first: (function, pc, wait_dst, ((register, operand), ...))
Snap.virtuals  vid -> (class, monitor depth, ((field, operand), ...))
operand        ('k', constant) | ('s', machine slot) | ('v', virtual object id)
```

Only registers live in the reference tier are recorded. A narrated lazy deopt
from the run (`--verbose`):

```text
code ('work', 2, 'osr') invalidated while suspended in a call; snapshot kind=after_call
  frame work@pc7 result->r6 live registers: r0=s0, r1=s1, r2=s2, r3=s3, r5=v0
  virtual v0: class Box, monitor depth 1, fields v=s2
  rebuilt interpreter frame work@pc8: [Counter{lock=0, {'n': 5}}, 9, 5, 1, None, Box{lock=1, {'v': 5}}, 5, None, None, None]
```

**Property.** Equal termination status and error kind, equal output trace, equal
return value, equal method tables, and equal heap reachable from the result and
globals up to isomorphism (class, fields, monitor depth, aliasing, cycles).

**Sweep.** 13 hand-written scenarios under three tiering thresholds, with *every*
deopt point of each unforced run forced individually plus 30 sampled pairs; 140
seeded random programs with a sampled single-point sweep.

**Result (CPython 3.13.15, 2026-11-19).** Exit status 0; every run matched the
reference. 3,501 mixed-mode runs, 3,322 of them with forced deopts. Unforced
runs: 742 compilations, 558 OSR entries, 246 guard deopts, 24 lazy deopts, 83
self-invalidation deopts, 908 side exits, 1 deopt for a statically known error.
All runs: 30,262 interpreter frames rebuilt (at most 4 from one optimized
frame), 8,506 virtual objects materialized, 703 of them re-locked.

**Negative controls.** Each row is a small switch in the model; each was detected.

| Variant | Violated invariant | First detecting scenario |
| --- | --- | --- |
| `no_stack_patch` | G2 | `midcall_method_mutation_lazy_deopt` |
| `skip_patch_if_not_entrant` | G3 | `recursive_activations_all_patched` |
| `no_self_check` | G4 | `global_constant_self_invalidation` |
| `no_dep_registration` | G1 | `midcall_method_mutation_lazy_deopt` |
| `reexecute_call`, `drop_retval` | G5 | `midcall_method_mutation_lazy_deopt` (the second only with a forced deopt) |
| `skip_instruction` | resume position (Finding 4) | `sunk_allocation_partial_escape` |
| `dup_materialize` | M1 | `alias_identity_after_materialization` |
| `shallow_materialize` | M2 | `cyclic_virtual_graph` |
| `no_relock` | M4 | `midcall_method_mutation_lazy_deopt` |
| `unsound_liveness` | frame-state completeness (Finding 9) | random program, seed 0 |
| `osr_assumes_preloop_constants` | OSR entry (Finding 6) | `sunk_allocation_partial_escape` (non-termination trap) |
| `sequential_loop_moves` | OSR entry (Finding 6) | `loop_carried_swap_osr_entry` |

`skip_patch_if_not_entrant` encodes G3: in the recursive scenario the innermost
activation fails a guard (the code becomes not entrant), then mutates a method
table that every suspended activation depends on. `drop_retval` is detected only
under forced deoptimization, so the forced sweep adds discriminating power
beyond naturally occurring deopts.

Basis: execution (commands and output in Evidence; golden output preserved in
`support/expected_output.txt`) + derived (mapping of variants to invariants).

## Boundaries

**Not examined.**

- JavaScriptCore, SpiderMonkey, .NET, Android Runtime, LLVM statepoints.
- The full texts of Stadler et al. (partial escape analysis, CGO 2014,
  DOI 10.1145/2544137.2544157), D'Elia and Demetrescu (OSR, PLDI 2018,
  DOI 10.1145/3192366.3192396), "Deoptless" beyond its abstract, Chambers, Ungar
  and Lee (OOPSLA 1989), Deutsch and Schiffman (POPL 1984), Guo and Palsberg
  (POPL 2011) and Icarus (SOSP 2024, DOI 10.1145/3694715.3695949). Their records
  were verified; no finding rests on their contents (the Graal source stands in
  for the CGO paper).
- The Coq proof scripts of CoreJIT, FM-JIT and JIThm (not compiled or read);
  theorem statements are taken from the papers.
- WebAssembly tiers, graph construction in any optimizing compiler, and Graal's
  `OptimizedCallTarget` invalidation path beyond `OptimizedAssumption`.
- Which CPython mutations call `_Py_Executors_InvalidateDependency`, whether
  CPython's optimizer removes allocations, and what LuaJIT's trace flush does to
  a trace that is currently executing.
- Security consequences of JIT bugs, and JIT hardening in general.

**Unknown.**

- Whether a failed eager guard in V8 also redirects *other* activations of the
  same code (`deoptimize-reason.h` has a lazy reason "marked due to eager deopt";
  the call path was not traced).
- Memory cost of deopt metadata per engine, and frequency of deopt-state bugs.
- Common claims about tracing JITs (trace explosion on branch-heavy code, bridge
  proliferation) and about Truffle warm-up memory were not found in the primary
  sources read and are not asserted here.
- No PLDI 2023 or OOPSLA 2023 paper by Barrière and co-authors on JIT
  verification was found; only the two POPL papers and three repositories.

**Known not to apply.**

- FM-JIT's theorem does not cover speculation *insertion*, inlining, or
  multi-frame deoptimization; CoreJIT's theorem does not cover native code.
  Citing either as "a verified speculative JIT down to machine code" is wrong;
  JIThm's README claims a combination, which was not examined.
- The copy-and-patch paper contains no deoptimization or speculation mechanism;
  those properties of CPython's JIT come from its micro-op trace layer.
- The probe's result says nothing about the correctness of any engine. The
  model has one thread, synchronous compilation, no moving collector, no
  exception handlers, no stack inspection and no install-time race; invariants
  about those (Finding 3 step 2, M3, M5, M6) rest on source reading only.

**Unsupported (by the subjects themselves).**

- SELF as published performs no tail-call elimination because eliminated frames
  cannot be reconstructed.
- Truffle's `Assumption.ALWAYS_VALID` "fails with an
  `UnsupportedOperationException` if invalidated."
- CPython's JIT is experimental and off by default (PEP 744: Draft when read).

**Stronger conclusions the evidence does not establish.** That the engines agree
on *when* deopt points must exist (only SELF's rule is quoted); that any engine
satisfies G1 to G5 or M1 to M7 in all configurations; that any engine team
describes its design through the four-encodings view.

## Evidence

All sources were read on 2026-11-19. Line numbers refer to the pinned commits.

**V8** `v8/v8` @ `e88118f63dd96f24a9acb8bd0665e7880063f5c0`

- `src/deoptimizer/deoptimizer.cc`: `ActivationsFinder::VisitThread` L374-425;
  `Deoptimizer::DeoptimizeMarkedCode` L437-485; `DoComputeOutputFrames` L1706-1988
  (frame-kind dispatch from L1809; lazy-deopt validity comment L1906-1909;
  stack-size invariant L1976-1984); `MaterializeHeapObjects` L3210-3255.
- `src/deoptimizer/translated-state.{h,cc}`: `MaterializationState` (`.h`
  L109-115); `InitializeObjectAt`/`InitializeCapturedObjectAt` (`.cc` L2145-2200);
  `EnsureObjectAllocatedAt` L2263-2283; `StoreMaterializedValuesAndDeopt`
  L2871-2939.
- `src/deoptimizer/translation-opcode.h` L14-67; `src/deoptimizer/deoptimize-reason.h`
  L125-158; `src/common/globals.h` L1053-1057 (`DeoptimizeKind`).
- `src/objects/dependent-code.h` L37-72; `src/objects/dependent-code.cc` L137-184;
  `src/objects/objects.cc` L6431-6440 (`PropertyCell::InvalidateProtector`);
  `src/execution/protectors.{h,cc}`; `src/compiler/compilation-dependencies.cc`
  L27-48 and L1450-1487; `src/codegen/safepoint-table.h` L218-234;
  `src/compiler/osr.cc` L21-25; `src/compiler/frame-states.h` L68-89.

**HotSpot** `openjdk/jdk` @ `4f33273115381cd7697082fcb1bb2642dae19043`, under
`src/hotspot/share/`

- `runtime/deoptimization.cpp`: `DeoptimizationScope` L116-200;
  `rematerialize_objects` L356-437; `restore_eliminated_locks` L474-496;
  `deoptimize_objects_internal` L498-522; `fetch_unroll_info_helper` from L524;
  `deoptimize_all_marked` L1084-1096; `relock_objects` L1469-1511.
- `runtime/deoptimization.hpp`: `DeoptReason` L76-123, `DeoptAction` L127-134,
  unpack modes L145-150.
- `runtime/frame.cpp` L353-411 (`frame::deoptimize`); `runtime/javaThread.cpp`
  L1178-1186; `runtime/vframeArray.cpp` L171-190 and L261-290;
  `code/scopeDesc.hpp` L72-74; `code/dependencies.hpp` L105-160;
  `oops/instanceKlass.cpp` L1775-1798; `ci/ciEnv.cpp` L973-988;
  `runtime/sharedRuntime.cpp` L3836-3849.

**Graal** `oracle/graal` @ `3fd1dcaa85129cc6df8232487f9506d73787a755`

- `compiler/src/jdk.graal.compiler/src/jdk/graal/compiler/nodes/FrameState.java`
  L70-74 (javadoc), L98-140 (`StackState`), L169-183 (inputs).
- `.../virtual/phases/ea/PartialEscapeClosure.java` L613-689 (lock ordering and
  `materializeVirtualLocksBefore`), materialization counters throughout.
- `truffle/src/com.oracle.truffle.api/src/com/oracle/truffle/api/CompilerDirectives.java`
  (`transferToInterpreter` L79, `CompilationFinal` L286, `TruffleBoundary` L313,
  `ValueType` L342, `ensureAllocatedHere`), `.../api/Assumption.java`,
  `.../api/nodes/ExplodeLoop.java`.
- `truffle/src/com.oracle.truffle.runtime/src/com/oracle/truffle/runtime/OptimizedAssumption.java`
  L62-100, L167-226, L280-305.
- `substratevm/src/com.oracle.svm.core/src/com/oracle/svm/core/deopt/Deoptimizer.java`
  class javadoc L106-200.

**PyPy** `pypy/pypy` @ `8fce4f7066e606c971268834548f15626f418b5d`:
`rpython/jit/metainterp/resume.py` L19-22, L945-956, L1312-1351;
`rpython/jit/metainterp/compile.py` L944-1001;
`rpython/jit/metainterp/quasiimmut.py` L84-110; `rpython/jit/backend/model.py`
L145-153; `rpython/rlib/jit.py` L14-36.

**CPython** `python/cpython` @ `441c010fef90ab2860ae8142cbfd1fd52f53ba75`
(`Include/patchlevel.h`: `PY_VERSION "3.16.0a2+dev"`): `InternalDocs/jit.md`;
`Tools/jit/README.md`; `Tools/jit/template.c` L90-133; `Python/jit.c` L117-181 and
`patch_*` from L304; `Python/bytecodes.c` L6113 (`_EXIT_TRACE`), L6152-6154
(`_CHECK_VALIDITY`), L6194-6199 (`_DEOPT`); `Python/optimizer.c` L1916-1949;
`Python/optimizer_analysis.c` L725-730 (`remove_unneeded_uops`).

**LuaJIT** `LuaJIT/LuaJIT` @ `63c8f1a9b479ba5518cf6a170ff7729178bc3cfd`:
`src/lj_snap.c` L832-833 (`snap_unsink`), L939-990 (`lj_snap_restore`);
`src/lj_opt_sink.c` L1-2, L235-239; `src/lj_trace.c` L258-276 (flush functions).

**Coq developments.** `Aurele-Barriere/CoreJIT` @
`8740d4149be649d0746d9f0d2d759b387a8f3246`, `Readme.md` (file roles: `specIR.v`,
`jit.v`, `jit_proof.v`, `internal_simulations.v`; "The additional OCaml code is
out of scope of our verification work"). `Aurele-Barriere/FM-JIT` @
`deedcb59d030b7957433fecc493a3c0f0a6bfdd6`, `README.md`. `Aurele-Barriere/JIThm`
@ `ad3ae5a3d6759a070195815e321df1b372d982b9`, `README.md` (not a listed subject).

**Publications.** Metadata from Crossref (`https://api.crossref.org/works/<DOI>`);
quotations from the stated full-text copies.

- Hölzle, Chambers, Ungar. PLDI 1992, DOI 10.1145/143095.143114; text:
  `bibliography.selflanguage.org/_static/dynamic-deoptimization.pdf`.
- Hölzle, Chambers, Ungar. ECOOP 1991, DOI 10.1007/BFb0057013;
  text: `bibliography.selflanguage.org/_static/pics.pdf`.
- Kotzmann, Mössenböck. VEE 2005, DOI 10.1145/1064979.1064996; text:
  `usenix.org/events/vee05/full_papers/p111-kotzmann.pdf`.
- Bolz, Cuni, Fijałkowski, Rigo. ICOOOLPS 2009,
  DOI 10.1145/1565824.1565827; text: `stups.hhu-hosting.de/downloads/pdf/BoCuFiRi09_246.pdf`.
- Würthinger, Wimmer, Humer, Wöß, Stadler, Seaton, Duboscq, Simon, Grimmer.
  PLDI 2017, DOI 10.1145/3062341.3062381; text:
  `chrisseaton.com/truffleruby/pldi17-truffle/pldi17-truffle.pdf`.
- Xu, Kjolstad. PACMPL 5(OOPSLA), 2021, DOI 10.1145/3485513; text: arXiv
  2011.13127v3.
- Flückiger, Scherer, Yee, Goel, Ahmed, Vitek. PACMPL 2(POPL), 2018,
  DOI 10.1145/3158137; text: arXiv 1711.03050v2.
- Barrière, Blazy, Flückiger, Pichardie, Vitek. PACMPL 5(POPL), article 46, 2021,
  DOI 10.1145/3434327; text: `janvitek.org/pubs/popl21.pdf`.
- Barrière, Blazy, Pichardie. PACMPL 7(POPL), article 9, 2023,
  DOI 10.1145/3571202; text: arXiv 2212.03129v1.
- Barrett, Bolz-Tereick, Killick, Mount, Tratt. PACMPL 1(OOPSLA), 2017,
  DOI 10.1145/3133876 (Crossref abstract).
- Myreen. POPL 2010, DOI 10.1145/1706299.1706313. Myreen, Davis. ITP 2011,
  DOI 10.1007/978-3-642-22863-6_20 (abstract: `kookamara.com/jared/papers.html`).
- PEP 744 (Bucher, Ostrowski), `https://peps.python.org/pep-0744/`: Draft,
  Informational, Created 11-Apr-2024, Python-Version 3.13.

**Execution.** From the corpus root, with CPython 3.13.15 on Linux:

```console
$ python3 -B reports/jit-compilation-speculative-optimization-and-deoptimization-soundness/support/verify_speculative_deopt_simulation.py
speculative deoptimization equivalence probe
  scenarios: 13 hand-written x 3 tiering thresholds, 1415 runs
  ...
PASS: mixed-mode execution is observationally equivalent to the reference interpreter in every run, and every negative control was detected
```

The full `--verbose` output (statistics, per-scenario lines, negative-control
table, narrated deopt; without the timing line) is preserved in
`support/expected_output.txt`, whose first line records the script's SHA-256.

## Revalidation

- **Model and invariants.** Run the probe; exit status 0 and the final `PASS`
  line are the criterion. Compare with `support/expected_output.txt` (ignore the
  `elapsed` line; random-program counts depend on Python's `random.Random`
  sequence and do not affect the criterion). `--random N` widens the random
  sweep; `--verbose` prints the narrated lazy deopt. To test a new invariant, add
  a scenario and a mutant, and require that the mutant is detected.
- **Engine source claims.** Each is tied to a file and a short quoted phrase;
  for a newer commit, search for the phrase rather than the line number:
  `Replace the current pc on the stack with the trampoline`,
  `Materialization can cause a GC` (V8 `deoptimizer.cc`); `must relock just
  once`, `MUST NOT stop at a safepoint` (HotSpot `deoptimization.cpp`);
  `awaitDependency` (Graal `OptimizedAssumption.java`); `unstructured locking`
  (Graal `PartialEscapeClosure.java`); `all GUARD_NOT_INVALIDATED do nothing`
  (PyPy `backend/model.py`); `De-duplicate sunk allocations` (LuaJIT
  `lj_snap.c`); `_CHECK_VALIDITY` (CPython `bytecodes.c`). A missing phrase
  means the mechanism was renamed or redesigned and the row must be re-read.
- **Enumerations.** Diff HotSpot `DepType`, `DeoptReason`, `DeoptAction`; V8
  `DependencyGroup`, `TranslationOpcode`, `DeoptimizeKind`; Graal `StackState`.
  Additions usually mark a new kind of speculation or resume position.
- **Mechanized results.** Check the CoreJIT and FM-JIT repositories for commits
  after 2022 and the authors' publication lists for successors; the gap table in
  Finding 8 is the part most likely to age. Only rebuilding the Coq developments
  confirms theorem statements beyond the papers. Re-resolve DOIs via Crossref.
- **What has no cheap check.** Install-time races, GC during materialization and
  identity across stack inspection (Finding 3 step 2; M3, M5, M6) need a built
  engine and targeted stress tests (V8's `deopt_every_n_times` flag is consulted
  in `MaterializeHeapObjects`; HotSpot has `VerifyStack`); nothing in this
  package exercises them.
