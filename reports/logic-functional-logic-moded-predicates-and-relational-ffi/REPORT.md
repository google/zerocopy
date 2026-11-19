# Logic, Functional-Logic, Moded Predicates, and Relational FFI

## Summary

Mainstream native ABIs assume that every procedure invocation (1) receives fully bound inputs on entry, (2) returns at most once with a single value, (3) runs on a strictly LIFO call stack whose frames die on return, and (4) commits side effects irreversibly. Logic and functional-logic languages systematically lift these restrictions, forcing compilers and foreign-function interfaces (FFIs) to confront five independent call-shape coordinates: **mode** (input/output instantiation direction), **determinism** (minimum and maximum solution cardinality), **continuation multiplicity** (how many times a caller's continuation is invoked), **argument evaluation discipline** (strict, lazy, lenient, or residuating), and **undo discipline** (untrailed, trailed, or transactional rollback).

Key operational and verification invariants established across the examined systems:

- **Backtracking breaks native LIFO stack and ownership assumptions.** Warren Abstract Machine (WAM) implementations retain environment frames below active choice points and unwind bindings through a conditional **trail** (`addr < hb`), reclaiming younger heap allocations in $O(1)$ on failure. Because native C/Rust stack frames cannot be frozen and re-entered after destructors run, foreign nondeterministic predicates must be inverted into explicit re-entrant state machines (`PL_FIRST_CALL`, `PL_REDO`, `PL_PRUNED`, `PL_RESUME` in SWI-Prolog) or compiled via explicit success-continuation passing (`model_non` in Mercury's high-level C backend). Untrailed foreign mutations survive backtracking and silently break declarative soundness.
- **Modes and determinism compile one relation into distinct native calling conventions.** Mercury compiles each `:- mode` of a predicate into a separate procedure whose determinism (`det`, `semidet`, `multi`, `nondet`, `failure`, `erroneous`, plus committed-choice `cc_multi`/`cc_nondet`) fixes its ABI: `model_det` uses ordinary returns, `model_semi` adds a boolean success flag (`SUCCESS_INDICATOR` in `foreign_proc`), and `model_non` passes a success continuation `(func_ptr, env_ptr)`. Exporting `multi` or `nondet` procedures directly to C is rejected as a compile-time error, and cross-mode semantic equivalence of mode-specific clauses or `foreign_proc` implementations is trusted via `pragma promise_equivalent_clauses` rather than verified.
- **Destructive uniqueness under backtracking requires a three-point liveness lattice.** Because a failure continuation may still observe a value that has no remaining forward references, Mercury distinguishes `unique`/`dead` (`di`/`uo`, usable only in `det`/`cc_multi` code) from `mostly_unique`/`mostly_dead` (`mdi`/`muo`, requiring trailed undo on backtrack). The examined Mercury compiler explicitly documents incomplete unique-mode support (no nested unique modes, no `ui` modes, and no automatic compile-time reuse of `dead` cells outside library primitives).
- **Determinism, tabling, interleaving, and confluence trade search completeness against evaluation order and metatheory.** SLG tabling resolves SLD left-recursion divergence and computes three-valued well-founded models (`true`, `false`, `undefined`), while Answer Set Programming (Clingo) computes two-valued stable models at the cost of an exponential grounding bottleneck ($O(n^k)$ per $k$-variable rule) and non-monotonicity. miniKanren guarantees complete disjunction search via thunk-swapping interleaving (`mplus`/`bind`), whereas the Verse calculus achieves deterministic ordered choice (`one{}`, `all{}`) and lenient unification at the expense of laziness, parallel or-search, and an open skew-confluence proof for general recursion. Constraint Handling Rules (CHR) decide confluence via critical-pair joinability only for terminating programs, and confluence is not closed under rule-set union—directly explaining cross-module trait/type-class coherence failures.

## Applicability

This report synthesizes primary source inspection, formal literature, and standalone executable reference probes across seven pinned upstream repositories (`SWI-Prolog/swipl-devel@3992b97ba46231c1a27ef39d06f52f7c92a52e49`, `mthom/scryer-prolog@47f2c4e7cf9232137e2d43c7190c5504eb1a0045`, `Mercury-Language/mercury@ec2bc5ccbf9aa77641ae09380ee46bbc731079cc`, `potassco/clingo@f1d4b8e63a665898fddf4a620333eb0a1bfdebd9`, `michaelballantyne/faster-miniKanren@a25c70209800ab781983ace5c6840784bb32b4da`, `SWI-Prolog/packages-chr@3f81d6be337cd547b218922e1f4fd36121472bf1`, `LPCIC/elpi@631d14a63489ed0e8359ad036f7a8580bb373f33`), the ISO/IEC 13211-1:1995 Prolog Core standard, and the cited peer-reviewed papers.

How the subjects relate:

- **Comparative FFI and compilation core:** SWI-Prolog, Scryer Prolog, and Mercury are examined directly in source for virtual-machine state representation, choice-point/trail invariants, mode/determinism compilation, and C foreign interfaces.
- **Search, constraint, and functional-logic design space:** The Verse calculus, faster-miniKanren, Clingo, SWI-Prolog CHR, and ELPI (λProlog) are examined alongside formal literature (SLG resolution, Curry needed narrowing, LogicT, CHR confluence, linear effect handlers) to map how search completeness, constraint stores, higher-order unification, and rule confluence constrain ABI boundaries and formal verification.
- **Execution scope:** Native `swipl`, `mmc`, and `clingo` compiler/runtime binaries were not installed in the observation environment; execution evidence therefore comes from self-contained Python 3 reference models reproducing WAM conditional trailing, occurs-check cycles, SLG fixpoint vs. SLD divergence, Gelfond-Lifschitz reducts, `faster-miniKanren` `mplus` interleaving, Verse choice floating, and CHR critical-pair non-confluence. Claims about exact compiler diagnostics emitted by `mmc` or runtime handle lifetimes in compiled `swipl` C extensions rest on pinned upstream source and manual text rather than live native compiler execution.

Claims about general ABI design and verification obligations (such as viewing `0..n` callee determinism as dual to `0..n` caller continuation multiplicity, or treating FFI imports as access-limited relations) are explicitly marked `Basis: derived` and generalize beyond individual revisions only insofar as the underlying semantic invariants hold.

## Findings

### 1. Call-Shape Coordinates Across Logic, Functional-Logic, and Native ABIs

Basis: derived + documentation + source

Every cross-language boundary implicitly fixes a point in a five-dimensional call-shape space. Mainstream C and Rust ABIs inhabit a single degenerate corner (`in`-only arguments, `det` single return, one-shot LIFO continuation, strict call-by-value arguments, irreversible side effects). Logic and functional-logic systems occupy distinct points across all five axes:

| System | Mode / Directionality | Determinism / Cardinality | Continuation Multiplicity | Argument Evaluation | Undo / Effect Discipline Under Choice |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **C / Rust native ABI** | Fixed `in` (mutation via pointer/`&mut`) | `1` (`det`) or `0` (diverge/abort); partiality encoded as `Option`/`Result`/sentinel | `1` (one-shot LIFO stack frame) | Strict call-by-value | Irreversible; `Drop` / unwind runs once on exit |
| **ISO / SWI / Scryer Prolog** | Unmoded (runtime instantiation; any arg may be unbound var) | Unchecked `0..n`; explicit pruning via cut `!` | `0..n` via retained WAM environments & choice points | Strict term construction; unbound logical vars | Conditional trail (`addr < hb`) undoes term bindings; foreign state requires explicit trail or `PL_PRUNED` |
| **Mercury (MLDS C / LLDS C)** | Static per-mode inst transitions (`in`, `out`, `di`, `uo`, `mdi`, `muo`) | Checked 8-element lattice (`det`, `semidet`, `multi`, `nondet`, `cc_multi`, `cc_nondet`, `failure`, `erroneous`) | `0..1` (`model_det`/`model_semi`), `0..n` via explicit success continuation (`model_non`) | Strict, mode-reordered conjunctions | Pure by default; `foreign_proc` declares `may_modify_trail` / `will_not_modify_trail`; `di` forbidden across backtracking |
| **Verse Calculus (VC)** | Unmoded logical variables (`∃x. e`) with unification `e1 = e2` | Scoped choice expressions (`e1 \| e2`, `fail`) discharged by `one{}` (`0..1`) or `all{}` (`0..n` ordered tuple) | Choice duplicated spatially in rewrite context rather than heap stack frames | **Lenient** (call-by-value on non-ground terms; blocked equations residuate) | Failure contexts (`decides` + `transacts` in full Verse) require transactional rollback of effects |
| **Curry** | Unmoded; narrowing (instantiate) vs. residuation (suspend) | Unchecked `0..n`; encapsulated search (`findall`/set functions) | `0..n` with per-branch thunk memoization (**call-time choice**) | Lazy (call-by-need) + needed narrowing | Rigid foreign calls suspend until arguments are ground (floundering risk) |
| **miniKanren (`faster-miniKanren`)** | Unmoded relational goals `State -> SearchStream` | Lazy stream of `0..n` substitutions (`#f`, thunk, singleton, pair) | `0..n` via heap-allocated immature stream thunks | Strict host calls; lazy stream suspension at `fresh`/`mplus` | Pure immutable substitution + constraint store (no trail needed; host side effects break relationality) |
| **Clingo (ASP)** | Safe range-restricted rules grounded bottom-up | `0..n` stable models (or optimal models under `#minimize`) | Batch solver callback (`clingo_model_t` valid only during callback) | Ground-time eager `@`-calls + CDNL solving | Theory propagator `undo()` callback rolls back solver decision levels |

A central structural duality emerges across these systems (`Basis: derived`, corroborated by Tang et al. POPL 2024): **callee determinism (`0..n` solutions) and caller continuation multiplicity (`0..n` invocations of the success continuation) are the same cardinality datum read from opposite sides of a call boundary.** When a runtime restricts continuations to be one-shot (such as native C stacks, OCaml 5 effect handlers, or one-shot WebAssembly effect handlers), a nondeterministic callee cannot transparently yield multiple solutions through a foreign frame; it must either invert control into a heap-allocated state machine (SWI-Prolog `PL_retry`, Rust `Iterator`), pass a heap closure as a success continuation (Mercury `model_non`), or materialize a collection at the boundary (`all{}` / `findall`).

---

### 2. Prolog and the Warren Abstract Machine (WAM): Choice Points, Conditional Trailing, Cut, and Foreign Interfaces

#### 2.1 WAM Memory Architecture, Conditional Trailing, and Frame Retention

Basis: documentation + source + execution

In Warren's Abstract Machine (Warren 1983; Aït-Kaci 1991) and modern implementations such as Scryer Prolog (`mthom/scryer-prolog@47f2c4e7cf9232137e2d43c7190c5504eb1a0045`, `src/machine/machine_state.rs` L118–157 and `src/machine/stack.rs` L31–95), execution state is partitioned across:

1. **Global heap (`heap`)**: holds compound terms and unbound `REF` cells, growing monotonically during forward execution.
2. **Local stack (`stack`)**: interleaves **environment (`AndFrame`)** records (storing `num_cells`, previous environment `e`, continuation pointer `cp`, and permanent variables) with **choice points (`OrFrame`)** (storing argument registers, saved `e`, `cp`, previous choice point `b`, cut register `b0`, heap watermark `hb`, and trail pointer `tr`). In Scryer Prolog (`src/machine/stack.rs` L12–85), `AndFrame` and `OrFrame` share a contiguous `RawBlock<Stack>` whose variable-sized permanent variable slots are indexed directly past `AndFramePrelude` via pointer arithmetic (`with_exposed_provenance`).
3. **Trail (`trail: Vec<TrailEntry>`, watermark `tr`)**: an undo log recording bindings made to variables that predate the most recent choice point.

**Conditional trailing invariant:** When unifying an unbound heap variable at address `a` with a term, the WAM records `a` on the trail **if and only if `a < hb`** (for heap variables, or `a < b` for stack variables), where `hb` is the heap-top watermark saved in the newest choice point `b`. Any variable allocated *after* `b` satisfies `a >= hb` and will be reclaimed in $O(1)$ time on backtracking simply by resetting `heap_top := hb` without touching the trail. On failure, the WAM unwinds `trail[tr_saved .. tr]` to restore every older variable cell back to an unbound self-referential `REF(a)`, resets `heap_top := hb`, restores argument registers, and jumps to the alternative clause address.

**Environment protection invariant:** Even when a procedure exits, its `AndFrame` cannot be popped if a younger choice point `b > e` exists above it on the local stack, because backtracking to `b` may re-enter the continuation that depends on `e`'s permanent variables. Consequently, WAM activation records form a **cactus tree** embedded in a linear stack rather than a LIFO stack.

**Execution probe (`probe_p1.py`, Section 1A):** In our executable WAM model (`Basis: execution`), allocating `x` at heap address `0`, pushing a choice point (`hb=1, tr=0`), allocating `y` at address `1`, binding `x -> a` and `y -> b`, and incrementing an untrailed `foreign_counter` yields:

- Before backtrack: `x=('ATOM', 'a') (trailed=True)`, `y=('ATOM', 'b') (trailed=False)`, `trail=[0]`, `foreign_counter=1`.
- After backtrack: `x=('REF', 0)`, `len(heap)=1` (`y` instantly reclaimed), `trail=[]`, **`foreign_counter=1 (LEAKED!)`**.

This demonstrates the fundamental FFI soundness law under backtracking: **any mutation performed by foreign code between a choice point and a subsequent failure silently persists across alternative branches unless it is registered on the trail or guarded by an effect discipline that forbids mutation inside choice contexts.**

#### 2.2 SWI-Prolog Nondeterministic Foreign Protocol and Foreign Term Frames

Basis: source

Because C stack frames cannot be retained or re-entered after returning, SWI-Prolog (`SWI-Prolog/swipl-devel@3992b97ba46231c1a27ef39d06f52f7c92a52e49`, `src/SWI-Prolog.h` L204, L316–375, L444–471) implements nondeterministic foreign predicates by inverting the foreign procedure into a **re-entrant state machine** registered with `PL_FA_NONDETERMINISTIC (0x04)`:

- **Control dispatch (`PL_foreign_control(control_t)`):**
  - `PL_FIRST_CALL (0)`: initial entry into the predicate.
  - `PL_REDO (2)`: backtracking re-entry requesting the next solution, retrieving saved state via `PL_foreign_context(ctx)` (signed integer) or `PL_foreign_context_address(ctx)` (pointer).
  - `PL_PRUNED (1)` (deprecated alias `PL_CUTTED`): invoked when a cut (`!`), `once/1`, or `PL_cut_query`/`PL_close_query` discards the choice point before exhaustion, giving foreign code a mandatory cleanup hook to `free()` heap-allocated iterator contexts without leaking memory.
  - `PL_RESUME (3)` paired with `PL_yield_address(void *)`: supports foreign yielding/coroutine resumption (`PL_can_yield()`).
- **Return macros (`src/SWI-Prolog.h` L321–348):**
  - `PL_succeed` (`return true`) / `PL_fail` (`return false`): deterministic final solution or failure (closes the choice point).
  - `PL_retry(intptr_t n)` / `PL_retry_address(void *a)`: succeeds *and* leaves a foreign choice point carrying state `n` or `a`. Note 2 at `src/SWI-Prolog.h` L332–333 explicitly constrains `PL_retry(n)` to a **`sizeof(ptr)-2` bits signed integer** because the low 2 tag bits encode the foreign return kind in `foreign_t`.
- **Opaque term handles and foreign frames (`src/SWI-Prolog.h` L204, L445–463):**
  - `typedef uintptr_t term_t;` is an **opaque term handle** (an offset into the local stack's current environment/foreign frame, not a raw heap pointer), insulating C code from stack shifts and compacting WAM garbage collection (Appleby et al., CACM 1988, which preserves heap cell ordering so choice-point `hb` instant reclamation remains valid).
  - Foreign code manages scratch `term_t` lifetimes via `PL_open_foreign_frame()`, `PL_rewind_foreign_frame(fid)` (undoing bindings and discarding term refs created inside the frame while keeping the frame open, used e.g. in exception recovery at `src/pl-fli.c` L5099), `PL_close_foreign_frame(fid)` (discarding term refs while keeping bindings), and `PL_discard_foreign_frame(fid)` (undoing both bindings and term refs, e.g. `src/pl-fli.c` L5305, L5601).
  - When C calls back into Prolog via `PL_open_query` / `PL_next_solution`, terminating the query cleanly distinguishes `PL_cut_query(qid)` (commit current variable bindings, discard remaining alternatives, firing `PL_PRUNED` on open foreign choice points) from `PL_close_query(qid)` (discard both bindings and alternatives, rolling back the trail).

#### 2.3 Cut (`!`), Negation as Failure, Logical Update View, and Occurs-Check / Rational Trees

Basis: normative + documentation + source + execution

Four classic Prolog features create severe semantic and FFI discontinuities:

1. **Cut (`!`) as an untyped search-pruning effect:** Executing `!` sets `b := b0` (where `b0` is the choice-point pointer saved on entry to the enclosing predicate, stored explicitly in Scryer Prolog's `MachineState.b0` at `src/machine/machine_state.rs` L129), discarding every intermediate choice point. Cut violates commutativity of disjunction and conjunction, depends on textual clause order, and has opaque scope across meta-calls (`call/1`) or foreign callbacks.
2. **Negation as failure (`\+ G`) and meta-logical predicates:** `\+ G` is sound with respect to Clark's completion only for ground goals; on non-ground goals (e.g., `\+ p(X), X = a` vs. `X = a, \+ p(X)`), goal reordering flips truth values. Extra-logical predicates (`var/1`, `==/2`, `copy_term/2`) expose instantiation state and break declarative invariance.
3. **Logical update view for dynamic clauses (ISO/IEC 13211-1:1995):** Adopted from Lindholm and O'Keefe (ICLP 1987) and standardized in ISO/IEC 13211-1:1995, the logical update view mandates that a call to a dynamic predicate observes the exact snapshot of clauses present when the call began, unaffected by subsequent `asserta`/`assertz`/`retract` mutations during its backtracking execution. Implementations realize this via clause creation/erasure generation timestamps—mechanically identical to **Multi-Version Concurrency Control (MVCC) snapshot isolation** in relational databases. Foreign code iterating dynamic clauses must participate in the generation epoch to avoid dangling clause pointers or phantom reads.
4. **Omission of the occurs check vs. finite and rational trees:** Standard WAM unification omits the occurs check because checking reachability inside naive tree representations degrades linear-time `append/3` to quadratic time (even though near-linear unification algorithms exist: Paterson & Wegman 1978; Martelli & Montanari 1982). ISO/IEC 13211-1:1995 leaves unification of cyclic terms (`X = f(X)`) implementation-defined/undefined and provides `unify_with_occurs_check/2` separately; Scryer Prolog parameterizes unification via `MachineState.occurs_check: &'static dyn OccursCheckImpl` (`src/machine/machine_state.rs` L155). As verified in `probe_p1.py` Section 1B (`Basis: execution`), `X = f(X)` is rejected by finite-tree occurs checking, whereas omitting the check creates a cyclic rational tree (`REF -> STR(f, [REF])`) that causes unbounded recursion if passed across FFI to any host deserializer, structural equality checker, or inductive-type decoder (such as a Lean/Rocq inductive term model, which cannot inhabit infinite regular trees without coinduction or explicit graph handles).

#### 2.4 SLG Tabling and Three-Valued Well-Founded Semantics

Basis: normative + documentation + source + execution

Standard top-down SLD resolution loops indefinitely on left-recursive clauses (e.g., `path(X, Y) :- path(X, Z), edge(Z, Y)`) and cycles in the underlying graph. **SLG resolution** (Chen & Warren, JACM 1996, DOI `10.1145/227595.227597`) memoizes tabled subgoals and their derived answers, suspends consumer calls when no new answers are available, resumes consumers as producers generate answers, and detects **completion** per strongly connected component (SCC) of mutually dependent subgoals. Crucially, for general logic programs containing negation, SLG **delays** negative literals involved in negative loops (e.g., `p :- \+ p`), yielding **conditional answers** with a residual delay list and computing the **three-valued well-founded model** (Van Gelder, Ross & Schlipf, JACM 1991) with truth values `{true, false, undefined}`.

As demonstrated in `probe_p1.py` Section 1C (`Basis: execution`):
- On cyclic edges `{(a,b), (b,a), (b,c)}`, left-recursive SLD diverges immediately (`diverged after 10 left-recursive expansions`), whereas tabled fixpoint evaluation terminates with `path(a, Y) ∈ {a, b, c}`.
- On `{p :- not p}`, well-founded semantics assigns `p = UNDEFINED` (no two-valued stable model exists).
- On `{a :- not b; b :- not a}`, well-founded semantics assigns `a = UNDEFINED, b = UNDEFINED` (skeptical intersection across the two stable models `{a}` and `{b}`).

Implementation mechanisms and FFI barriers:
- **XSB SLG-WAM** freezes WAM stack segments (preserving suspended consumer stacks in place) or copies choice-point trails (CHAT), while **SWI-Prolog** (`src/pl-tabling.c`, originally prototyped via delimited continuations in Desouter, van Dooren & Schrijvers, TPLP/ICLP 2015, `arXiv:1507.08087`) suspends and resumes tabled worklists using continuation/trie infrastructure.
- **FFI boundaries:** (1) Native C/Rust frames cannot sit inside a suspended consumer stack; Mercury's `foreign_proc` therefore carries an explicit `will_not_call_mm_tabled` / `may_call_mm_tabled` attribute (`Mercury-Language/mercury@ec2bc5ccbf9aa77641ae09380ee46bbc731079cc`, `doc/mercury_reference_manual.texi` L9437–9452) to notify the compiler whether minimal-model tabling may suspend across a callback. (2) Foreign callers have no native 3-valued boolean type for `undefined` conditional answers (mirroring SQL 3-valued `NULL` logic); callers must inspect residual delay lists explicitly or risk conflating `undefined` with `true`. (3) Cutting over an incomplete table corrupts SCC completion invariants and is rejected or restricted by tabled engines.

---

### 3. Mercury: Mode Analysis, Determinism Lattice, Uniqueness Under Backtracking, and Multi-Procedure C Compilation

#### 3.1 Mode System: One Predicate Compiled to Multiple Native Procedures

Basis: normative + documentation + source

Mercury (Somogyi, Henderson & Conway, JLP 1996, DOI `10.1016/S0743-1066(96)00068-4`; `Mercury-Language/mercury@ec2bc5ccbf9aa77641ae09380ee46bbc731079cc`, `doc/mercury_reference_manual.texi`, `compiler/modes.m`) makes dataflow direction a static, checked property of every predicate. Each `:- mode` declaration specifies an **instantiation state (inst) transition** `InitialInst >> FinalInst` for every argument (`in == ground >> ground`, `out == free >> ground`), and each declared mode compiles into a **distinct procedure** (a distinct native C function symbol per mode).

- **Automatic conjunct reordering:** Within each mode, `compiler/modes.m` schedules conjunctions so that every variable is bound by its producer before any consumer reads it. Thus a single declarative definition of `list.append/3` compiles to separate specialized C functions for `(in, in, out) is det` (forward list copy), `(out, out, in) is multi` (nondeterministic split), and `(in, out, in) is semidet` (prefix match).
- **Mode-specific clauses and the cross-mode equivalence hole:** When reordering cannot produce an efficient or terminating schedule, Mercury allows mode-annotated clauses (`::`) or per-mode `pragma foreign_proc` definitions. The reference manual warns that predicates with mode-specific clauses are **assumed impure by default** unless the programmer supplies `:- pragma promise_equivalent_clauses(Pred/Arity).` (`doc/mercury_reference_manual.texi` L4684–4694), and all `pragma foreign_proc` declarations are assumed impure unless annotated `promise_pure`. **Crucial verification boundary:** the compiler *trusts* `promise_equivalent_clauses` and `promise_pure` without checking that two mode implementations denote the same mathematical relation. At the native ABI level, there is no relational object—only independent C functions whose mutual consistency is an unverified axiom.

#### 3.2 Determinism Lattice as Calling Convention

Basis: normative + source

Mercury classifies every procedure mode along two orthogonal axes—**can it fail before producing a first solution?** and **what is its maximum solution count (`0`, `1`, or `> 1`)?**—plus committed-choice pruning (`doc/mercury_reference_manual.texi` L4858–4913):

| Can fail? | Max 0 solutions | Max 1 solution | Max > 1 solutions (all) | Max > 1 solutions (committed choice) | MLDS High-Level C Code Model |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **no** | `erroneous` | `det` | `multi` | `cc_multi` | `det`/`erroneous`/`cc_multi` $\to$ `model_det`; `multi` $\to$ `model_non` |
| **yes** | `failure` | `semidet` | `nondet` | `cc_nondet` | `semidet`/`failure`/`cc_nondet` $\to$ `model_semi`; `nondet` $\to$ `model_non` |

Switch detection promotes a disjunction to `det` or `semidet` when every disjunct unifies the same `in`-moded variable with mutually exclusive (and, for `det`, exhaustive) data constructors. Committed-choice nondeterminism (`cc_multi`, `cc_nondet`) selects a single arbitrary solution without backtracking; to preserve declarative soundness, committed choice is **propagated upward through the call graph** (a function-coloring effect: every caller of a `cc_multi` procedure becomes `cc_multi` unless encapsulated via `promise_only_solution` or `io.state` at `main/2`).

**Exact MLDS high-level C calling convention (`compiler/ml_call_gen.m` L768–794):** Inspecting `Mercury-Language/mercury@ec2bc5ccbf9aa77641ae09380ee46bbc731079cc` confirms how `determinism_to_code_model(Detism, CodeModel)` directly determines the generated C ABI:

1. **`model_det` (`det`, `cc_multi`, `erroneous`):** Direct C function call returning outputs via return value / out-pointer parameters (`RetLvals = RetLvals0`). Zero backtracking overhead.
2. **`model_semi` (`semidet`, `cc_nondet`, `failure`):** Prepends a boolean success indicator to the return values (`ml_success_lval(Success, !Info)`, `RetLvals = [Success | RetLvals0]`). In `pragma foreign_proc("C", ...)`, foreign code **must assign a truth value to the macro `SUCCESS_INDICATOR`** (which may be a hardware register macro whose address cannot be taken; `doc/mercury_reference_manual.texi` L10759–10781).
3. **`model_non` (`multi`, `nondet`):** Synthesizes a **success continuation** via `ml_gen_success_cont` yielding `success_cont(FuncPtrRval, EnvPtrRval, _)` and appends `[FuncPtrRval, EnvPtrRval]` to the C function's parameter list (`ArgRvals = ArgRvals0 ++ [FuncPtrRval, EnvPtrRval]`, L770–775). Under `--nondet-copy-out`, outputs are passed directly into the continuation rather than returned (`RetLvals = []`). Thus the C call stack stays strictly LIFO: the nondeterministic callee invokes `(*cont)(cont_env_ptr, out_args...)` once for each solution, and returning from the callee signals failure/exhaustion (Henderson & Somogyi, CC 2002).

**Hard FFI restrictions in Mercury (`doc/mercury_reference_manual.texi` L9429–9460, L9589–9590, L10593–10638):**
- **No `multi`/`nondet` C exports:** `"It is an error to export a Mercury procedure that has a determinism of multi or nondet."` (L9589–9590). Only `det`, `semidet`, `cc_multi`, and `cc_nondet` procedures may cross `pragma foreign_export("C", ...)`, because C callers cannot supply Mercury's internal continuation environment protocol.
- **No cross-FFI exceptions:** Throwing a Mercury exception across the C foreign interface is unsupported and results in undefined behavior.
- **Trail and VM liveness contracts:** Every `pragma foreign_proc` carries explicit attributes: `may_modify_trail` (default) vs. `will_not_modify_trail` (L9429–9435), `may_call_mm_tabled` vs. `will_not_call_mm_tabled` (L9437–9452), and `affects_liveness` vs. `does_not_affect_liveness` (L9454–9460).
- **Zero-sized state erasure:** Arguments of type `io.state` or `store.store(_)` are erased completely at the C ABI boundary and are not passed as C parameters.

#### 3.3 Uniqueness Meets Backtracking: Mercury's "Mostly Dead" Lattice and Implementation Limits

Basis: documentation + source

To permit in-place destructive update (such as array mutation and I/O threading) in a purely declarative language, Mercury defines unique insts (`unique`, `dead`) and three standard modes (`doc/mercury_reference_manual.texi` L4750–4785):

```mercury
:- mode uo == free >> unique.    % unique output (freshly allocated, sole reference)
:- mode ui == unique >> unique.  % unique input (inspected without losing uniqueness)
:- mode di == unique >> dead.    % destructive input (consumed; caller retains zero refs)
```

**Fundamental interaction with backtracking:** A value is **not** `unique` if an active choice point could backtrack and observe its old state. Consequently, `di`/`uo` are sound only in `det` or `cc_multi` contexts (L4781). For backtrackable destructive updates (e.g., mutable solver arrays that log their undo actions on the trail), Mercury introduces **`mostly_unique`** and **`mostly_dead`** insts (`muo`, `mui`, `mdi`), which count *only references reachable on the forward execution path* while allowing older choice points to retain references provided the callee trails the inverse update.

This exposes an irreducible law shared with Rust's `UnwindSafe` and linear effect handlers (Tang et al., POPL 2024, DOI `10.1145/3632896`): **destructive linearity is always relative to the set of live continuations.** A resource unique only with respect to the success continuation (`mostly_unique`) cannot be irreversibly freed until all failure/unwind continuations holding it have been pruned.

**Documented Mercury compiler limitations (`doc/mercury_reference_manual.texi` L4737–4739, L4830–4845):** At the pinned revision, Mercury explicitly states:
1. `"We have not yet implemented unique modes fully, and the details are still in a state of flux."`
2. `"it is not possible to use nested unique modes, i.e. modes in which anything but the top level of a variable is unique."`
3. `"It is also not possible to use unique-input modes; only destructive-input and unique-output modes work."`
4. `"The Mercury compiler does not (yet) reuse dead values. The only destructive update in the current implementation occurs in library modules, e.g. for I/O and arrays."`

Thus Mercury's unique-mode system successfully enforces linear state threading for library primitives (`io.state`, `array`) at compile time, while general user-defined nested uniqueness and automatic compile-time garbage collection remain unimplemented in mainline mode checking.

---

### 4. The Verse Calculus: Lenient Evaluation, Choice Floating, and Skew Confluence

Basis: normative + documentation + execution

The Verse calculus (**VC**; Augustsson, Breitner, Claessen, Jhala, Peyton Jones, Shivers, Steele & Sweeney, *The Verse Calculus: A Core Calculus for Deterministic Functional Logic Programming*, PACMPL 7(ICFP), Article 203, 2023, DOI `10.1145/3607845`) defines a small-step **rewrite semantics** for functional logic programming without an external search-tree machine. Its core expression grammar is:

```text
e ::= v | eq; e | ∃x. e | fail | e1 | e2 | v1 v2 | one{e} | all{e}
```

Key semantic mechanisms and verified metatheoretic boundaries:

1. **Spatial choice floating and deterministic ordering:** Rather than exploring choices temporally via a backtracking stack, VC treats choice `e1 | e2` as a term constructor that **floats outward** through evaluation contexts (duplicating surrounding contexts) until captured by a delimiting scope:
   - `one{e}` evaluates to the *leftmost* surviving value of `e` (or `fail` if all branches fail)—a lexically scoped, declarative replacement for Prolog's `!` / `once/1`.
   - `all{e}` collects all surviving values of `e` into a tuple in a **well-specified left-to-right order** (as verified in `probe_p1.py` Section 1E: `all{x = (1 | 2); y = (10 | 20); x + y}` deterministically yields `(11, 21, 12, 22)`).
2. **Design price of determinism:** As the authors explicitly analyze, guaranteeing deterministic result ordering rules out both call-by-need laziness (which could avoid forcing failing subexpressions) and parallel first-come-first-returned or-search strategies.
3. **Lenient evaluation and occurs-check rewriting:** VC is **lenient**—neither strict call-by-value nor lazy call-by-need. Function application `(\x. e) v` substitutes an unbound logical variable `x` before `v` is ground, and equations whose operands are not yet resolved **residuate** in place until another part of the term binds them. Crucially, unlike standard WAM Prolog, VC includes an explicit occurs-check rewrite rule: an equation `x = v` with $x \in \mathrm{fv}(v)$ rewrites directly to `fail`, preserving finite-tree semantics.
4. **Confluence and the open skew-confluence boundary:** Theorem 4.1 of Augustsson et al. (ICFP 2023) proves ordinary confluence for *well-behaved* (non-recursively cyclic) terms. When general recursion is introduced via recursive bindings, eager substitution breaks ordinary Church-Rosser confluence (diverging rewrite paths can unfold different finite prefixes of an infinite normal form). The paper adopts **skew confluence** (Ariola & Blom 2002), while the authors' extended version explicitly notes that **the full skew-confluence proof for VC with recursion is not yet complete**.
5. **Transactional failure contexts and FFI floundering:** In the surface Verse language, failure-driven conditionals run inside failure contexts typed with the `decides` and `transacts` effects, requiring every state mutation performed before a `fail` to roll back transactionally. Crossing a native FFI from a lenient functional-logic core encounters two irreducible hazards: (a) native callees cannot accept unresolved logical variables (requiring suspension/residuation, which **flounders** into deadlock if no producer ever grounds the variable), and (b) any foreign side effect called inside a `decides` context must either participate in transactional rollback or be statically rejected by the effect checker.

---

### 5. Interleaving Search (miniKanren), Call-Time Choice (Curry), and Constraint Stores (CLP)

#### 5.1 miniKanren: Fair Interleaving Streams and Constraint Normal Forms

Basis: source + documentation + execution

Depth-first search (Prolog/WAM) is **incomplete**: if the first disjunct of `disj(G1, G2)` produces an infinite branch (e.g., `fives`), answers from `G2` (`sixes`) are never reached. miniKanren (Kiselyov, Shan, Friedman & Sabry, ICFP 2005, DOI `10.1145/1086365.1086390`; Hemann & Friedman, Scheme Workshop 2013) represents a goal as a function `State -> SearchStream`, where an **immature stream** is a zero-argument thunk delaying search work.

Inspecting `michaelballantyne/faster-miniKanren@a25c70209800ab781983ace5c6840784bb32b4da` (`mk.scm` L285–326) shows the exact four-case interleaving primitives:

```scheme
(define (mplus stream f)
  (case-inf stream
    (() (f))
    ((f^) (lambda () (mplus (f) f^)))        ; swap on immature stream!
    ((c) (cons c f))
    ((c f^) (cons c (lambda () (mplus (f) f^))))))

(define (bind stream g)
  (case-inf stream
    (() #f)
    ((f) (lambda () (bind (f) g)))
    ((c) (g c))
    ((c f) (mplus (g c) (lambda () (bind (f) g))))))
```

Whenever `mplus` encounters a suspended stream `f^` (introduced at every `fresh` via `(suspend ...)` at `mk.scm` L333), it **swaps the two streams** `(mplus (f) f^)`, guaranteeing that every finite-depth answer in a disjunction is eventually enumerated (`probe_p1.py` Section 1D: `mplus(fives, sixes)` yields `[5, 6, 5, 6, 5, 6, 5, 6]`).

**Trade-offs and FFI failure modes:**
- **Memory cost and conjunction fragility:** Fair interleaving retains suspended closures for every active branch in heap memory (unlike WAM's $O(\text{depth})$ stack), and **conjunction order (`bind`) still determines termination** when an earlier goal generates infinitely many ground answers rejected by a later goal.
- **Constraint stores (`=/=`, `absento`):** `faster-miniKanren/mk.scm` L486–680 maintains normalized disequality (`normalize-diseq`) and `absento` constraint stores alongside the substitution. Answers returned to a host caller are therefore *constrained substitutions*, not bare ground values.
- **Non-relational host calls:** Calling a host function via `project` silently forces its arguments to be ground at evaluation time, fixing a single mode and breaking reverse execution (e.g., running a relational interpreter backward for program synthesis; Byrd et al., ICFP 2017).

#### 5.2 Curry: Needed Narrowing, Call-Time Choice, and Encapsulated Search

Basis: documentation

Curry combines **needed narrowing** (Antoy, Echahed & Hanus, JACM 2000—optimal for inductively sequential rewrite systems) with **residuation** (suspending rigid/external operations until logical arguments become ground). Curry's defining semantic choice is **call-time choice**: in `let x = (0 ? 1) in x + x`, both occurrences of `x` observe the *same* nondeterministic choice, producing `{0, 2}` and never `1` (contrasting with run-time choice, which re-evaluates `0 ? 1` independently to yield `{0, 1, 2}`).

Under call-by-need laziness, call-time choice means a shared thunk must be memoized **per search branch** rather than globally, creating notorious interactions with **encapsulated search** (Braßel et al. 2004; Fischer, Kiselyov & Shan, ICFP 2009): the answer set of an encapsulated search can change depending on whether an outer shared nondeterministic expression was forced before or after entering the encapsulation boundary. Across FFI, a lazy nondeterministic value cannot be forced by foreign code because the foreign caller cannot name the branch context.

#### 5.3 CLP(X) and Attributed Variables as a Hidden Heap

Basis: documentation + source

Constraint Logic Programming (Jaffar & Lassez, POPL 1987) replaces syntactic unification with constraint solving over a domain $\mathcal{X}$ (reals, finite domains, booleans). In Prolog engines (e.g., Scryer Prolog's `attr_var_init` and `verify_attr` interrupt handling in `src/machine/machine_state.rs` L133, L146), this is implemented via **attributed variables** and coroutining (`freeze/2`, `dif/2`, `when/2`): unifying an attributed variable fires a hook that re-enters Prolog to propagate constraints.

Three FFI and verification hazards follow directly:
1. **Re-entrant unification:** A C foreign function unifying a `term_t` that happens to be an attributed variable can trigger arbitrary Prolog wakeup code mid-unification.
2. **Constraint stripping:** Copying, asserting, collecting via `findall/3`, or marshaling an attributed variable across FFI as a plain host value silently drops its attached domain/disequality invariants—creating a soundness leak analogous to erasing a refinement predicate at a foreign boundary.
3. **Silent floundering:** Incomplete finite-domain or delayed-goal solvers can succeed with unsatisfied residual constraints still suspended in the store; a host caller inspecting only variable bindings mistakes an undecided constraint system for a verified witness.

---

### 6. Answer Set Programming (Clingo): Stable Models, Grounding Complexity, and Multi-Shot Propagator FFI

Basis: normative + documentation + source + execution

Answer Set Programming (ASP) replaces Prolog's procedural top-down SLD search with **stable model semantics** (Gelfond & Lifschitz, ICLP/SLP 1988): a set of ground atoms $M$ is a stable model (answer set) of ground program $P$ iff $M$ equals the unique least Herbrand model of the **reduct** $P^M$ (formed by deleting every rule with a negative body literal `not a` where $a \in M$, and stripping all remaining negative literals).

As verified in `probe_p1.py` Section 1C (`Basis: execution`), stable model semantics differs sharply from three-valued well-founded semantics:
- `{p :- not p}` has **zero** stable models (`[]`), whereas WFS yields `{p = undefined}`.
- `{a :- not b; b :- not a}` has **two** stable models (`[['a'], ['b']]`), enabling declarative search over combinatorial choices without backtracking predicates.

**Complexity and the grounding wall:** Deciding stable-model existence is $\text{NP}$-complete for ground normal programs and $\Sigma_2^P$-complete for ground disjunctive programs (Eiter & Gottlob 1995), rising by an exponential ($\text{NEXP}$ / $\text{NEXP}^{\text{NP}}$) for non-ground programs (Dantsin et al., ACM Computing Surveys 2001). Clingo (`potassco/clingo@f1d4b8e63a665898fddf4a620333eb0a1bfdebd9`; Gebser, Kaminski, Kaufmann & Schaub, TPLP 2019, DOI `10.1017/S147406841800018X`) uses a two-phase **ground (`gringo`) then solve (`clasp` CDNL)** architecture. A single non-ground rule with $k$ variables over a Herbrand domain of size $n$ can materialize $\Theta(n^k)$ ground rules—the **grounding bottleneck**—motivating lazy-grounding solvers (Alpha, ASPeRiX, `arXiv:1903.12510`) at the cost of weaker conflict-driven unit propagation.

**Clingo's C FFI (`libclingo/clingo.h` L553, L728–729, L1131–1147, L1482–1507, L2954–2970):**
1. **Multi-shot solving & `#external` atoms:** `clingo_control_ground` and `clingo_control_solve` allow incremental grounding and solving across steps while preserving learned nogoods, with `#external` atoms toggling assumptions without re-grounding. Structural theory-atom tables are reset after `clingo_control_solve()` (L728–729).
2. **Ground-time host callbacks (`clingo_ground_callback_t`, L2954–2956):** Rules may invoke host `@name(args...)` functions during grounding, returning zero or more `clingo_symbol_t` values via `symbol_callback`. Soundness requires `@`-functions to be pure and deterministic; side effects or nondeterministic outputs break grounding reproducibility.
3. **Theory propagators (`struct clingo_propagator`, L1482–1507):** Exposes a clean four-hook **propagate / undo / check** interface (`init`, `propagate`, `undo`, `check`, plus `decide`) parameterized by `clingo_propagator_check_mode_t` (`none`, `total`, `fixpoint`, `both`, L1131–1136) and `clingo_propagator_undo_mode_t` (`default`, `always`, L1142–1144). Crucially, L1487–1488 enforces a strict phase boundary: `init()` is *"the last point to access symbolic and theory atoms. Once the search has started, they are no longer accessible."* Inside `propagate()`, if `clingo_propagate_control_add_clause()` or `clingo_propagate_control_propagate()` returns `false` (conflict), the propagator must return `true` (no API error) immediately so `clasp` can backtrack and invoke `undo()`.
4. **Verification asymmetry:** Checking that a returned answer set $M$ is a valid stable model of a ground program is polynomial-time (compute $P^M$ and verify its least fixpoint equals $M$), making ASP well-suited as an untrusted search oracle for positive witnesses; however, certifying **unsatisfiability** or **optimality** requires proof logging (e.g., DRAT/pseudo-Boolean/ASP proof certificates) rather than a single model check.

---

### 7. Constraint Handling Rules (CHR): Confluence, Refined Operational Semantics, and Cross-Module Coherence

Basis: normative + documentation + source + execution

Constraint Handling Rules (Frühwirth, JLP 1998, DOI `10.1016/S0743-1066(98)10005-5`; SWI-Prolog implementation in `SWI-Prolog/packages-chr@3f81d6be337cd547b218922e1f4fd36121472bf1`, `chr_runtime.pl` and `chr_swi.pl`) rewrite a multiset constraint store using three multi-headed guarded rule forms:
- **Simplification:** `H1, ..., Hn <=> G | B` (replaces heads with body `B` when guard `G` holds).
- **Propagation:** `H1, ..., Hn ==> G | B` (adds `B` while keeping heads, firing at most once per head tuple via propagation history).
- **Simpagation:** `H_kept \ H_removed <=> G | B` (retains `H_kept`, removes `H_removed`, adds `B`).

**Metatheory and the $\omega_t$ vs. $\omega_r$ gap:**
- **Confluence decidability:** Abdennadher, Frühwirth & Meuss (*Constraints* 1999, DOI `10.1023/A:1009809016172`) proved that for **terminating** CHR programs, confluence under the theoretical nondeterministic semantics $\omega_t$ is **decidable** by testing joinability of all finite **critical pairs** (minimal overlapping states where two rules can both fire). General CHR termination is undecidable (CHR is Turing-complete and can express arbitrary algorithms at optimal asymptotic complexity; Sneyers, Schrijvers & Demoen, TOPLAS 2009).
- **Refined operational semantics ($\omega_r$):** Production CHR compilers (including SWI-Prolog's `packages-chr`) execute the deterministic **refined operational semantics** $\omega_r$ (Duck et al., ICLP 2004), fixing textual rule order and active-constraint traversal order. As a result, real programs routinely rely on rule ordering and succeed deterministically under $\omega_r$ while being **non-confluent** under $\omega_t$—meaning their declarative first-order reading is unsound if constraints arrive in a different order.
- **Non-modularity of confluence and cross-FFI trait/type-class coherence:** Sulzmann, Duck, Peyton Jones & Stuckey (JFP 2007) formalized Haskell type classes with functional dependencies via translation to CHR, where sound and decidable type inference corresponds directly to **confluence and termination** of the generated CHR rules. Crucially, **confluence is not preserved under rule-set union**: as verified in `probe_p1.py` Section 1F (`Basis: execution`), $R_1 = \{a \Leftrightarrow b\}$ and $R_2 = \{a \Leftrightarrow c\}$ are each trivially terminating and confluent, yet $R_1 \cup R_2$ produces an unjoinable critical pair $(b, c)$ whose output flips between `('b',)` and `('c',)` depending on rule order. When two modules or two languages' generic/trait systems link across an FFI boundary, global coherence requires critical-pair confluence of the *combined* rule set—the mathematical root of orphan-instance restrictions in Rust and Haskell.

---

### 8. Relational Bridges: Adornments, Higher-Order Pattern Unification, Constrained Horn Clauses, and Continuation Multiplicity

Basis: documentation + source + derived

Four cross-cutting connections unify logic programming with compilers, databases, and formal verifiers:

1. **Magic-set adornments and access-limited relations = Mercury modes:** In deductive databases, the magic-sets transformation (Bancilhon et al., PODS 1986; Beeri & Ramakrishnan) annotates each predicate with a bound/free **adornment** string (e.g., `bf` vs. `fb`) and chooses a sideways information-passing strategy (SIPS) to restrict bottom-up evaluation to query-relevant tuples. An adornment is isomorphic to a Mercury mode (`in`/`out`), and SIPS selection is mode-directed conjunct reordering. Viewing an imported native C/Rust function as a **relation restricted to a single bound-input adornment** (with declared determinism and purity) unifies relational query planning, bidirectional codec compilation (parse and serialize as two verified modes of one layout relation), and FFI scheduling (`Basis: derived`).
2. **Higher-order logic programming and Miller's pattern fragment (`ELPI` / λProlog):** λProlog extends first-order Horn clauses with simply typed $\lambda$-terms (higher-order abstract syntax with $\beta\eta$-conversion), scoped hypothetical implications (`D => G`), and universal quantifiers (`pi x\ G`) for fresh nominal constants. Because full higher-order unification is undecidable, Miller (JLC 1991) isolated the **pattern fragment ($L_\lambda$)**—restricting flexible applications `F x1 ... xn` to distinct bound variables—where unification is decidable with unique most general unifiers; equations outside $L_\lambda$ suspend as delayed constraints. Embeddable λProlog engines like **ELPI** (`LPCIC/elpi@631d14a63489ed0e8359ad036f7a8580bb373f33`; Dunchev et al., LPAR 2015) serve as proof-assistant elaboration/tactic languages (Coq-Elpi), while Lean 4 applies **tabled resolution** to type-class synthesis (Selsam, Ullrich & de Moura, `arXiv:2001.04301`) to avoid exponential diamond-instance blowup and detect cyclic instances.
3. **Constrained Horn Clauses (CHCs) as a verifier IR:** Program partial correctness is mathematically identical to CHC satisfiability: a model assigns inductive invariants to unknown predicates, while a refutation yields a counterexample trace (Bjørner et al. 2015). **RustHorn** (Matsushita, Tsukada & Kobayashi, ESOP 2020) eliminates explicit heap modeling for safe Rust mutable borrows (`&mut T`) by encoding each borrow as a pair `(current_val, prophecy_final_val)` in pure CHCs. Linking CHCs across two languages across an FFI requires both frontends to emit clauses over a shared ABI and memory-model predicate vocabulary.
4. **Linear resources under multi-shot backtracking (`Soundly Handling Linearity`, POPL 2024):** Tang, Hillerström, Lindley & Morris (POPL 2024, DOI `10.1145/3632896`) formalize how multi-shot continuations (equivalent to nondeterministic backtracking) break naive linear typing unless the type system tracks both **continuation multiplicity** and **captured-resource linearity**. Combined with Mercury's `unique` vs. `mostly_unique` distinction, this establishes the minimal type discipline for sound nondeterministic FFI: every resource crossing a call site must be classified by whether it is linear across *all* live continuations (`unique@{success, fail, unwind}`), linear only on the forward path with a registered trail undo handler (`mostly_unique` + `Trail` capability), or freely duplicable/immutable.

## Boundaries

- **Native toolchain binaries not executed (`not examined`):** `swipl`, `mmc` (Mercury compiler), `clingo`, and `elpi` binaries were not installed in the observation container. Exact C code emitted by `mmc --highlevel-code` vs. `--lowlevel-code`, exact compiler error strings when attempting `pragma foreign_export("C", ...)` on a `nondet` predicate, and live runtime `PL_retry`/`PL_PRUNED` trace behavior under `swipl` were verified from pinned upstream source and reference manuals (`Basis: source + documentation`), not observed by executing those native binaries.
- **Verse calculus skew-confluence proof (`unknown`):** Augustsson et al. (ICFP 2023, extended version) explicitly report that the skew-confluence proof for the full Verse calculus with recursion was incomplete at publication. Whether a complete mechanized proof covering full recursive VC has been published since is not established by the evidence examined here.
- **Verified nondeterministic FFI (`not found` / `unsupported`):** No examined production logic or functional-logic system provides a machine-checked soundness proof of its nondeterministic foreign-function interface, nor does Mercury verify cross-mode equivalence for `pragma promise_equivalent_clauses` or `pragma foreign_proc` declarations.
- **Mercury unique-mode compiler completeness (`unsupported`):** Directly confirmed in `doc/mercury_reference_manual.texi` L4737–4845: nested unique modes, `ui` modes, and automatic compile-time reuse of `dead` values are explicitly unsupported in the examined mainline Mercury revision.
- **Datalog engine internals, SQL execution, and general delimited-continuation ABIs (`not examined`):** Semi-naive Datalog storage engines, relational SQL optimizers, and general-purpose delimited-continuation/effect-handler ABIs (such as OCaml 5 and WebAssembly stack switching) are outside the core scope of this report except where directly touching adornment/mode correspondence and continuation multiplicity.
- **ISO/IEC 13211-1:1995 verbatim clause text (`not examined`):** The paywalled ISO standard PDF was not directly inspected; claims regarding ISO Prolog's adoption of the logical update view and undefined cyclic-term unification are grounded in secondary peer-reviewed literature (`arXiv:1301.7669`, Lindholm & O'Keefe 1987) and upstream Prolog implementations (`swipl-devel`, `scryer-prolog`).
- **Overclaiming boundary (`known not to apply`):** Do not generalize Mercury's `model_non` LIFO C continuation passing to arbitrary C callees (only Mercury-generated `model_non` procedures obey the `(cont, cont_env_ptr)` protocol; C functions cannot directly be exported from `multi`/`nondet` Mercury procedures). Similarly, CHR confluence decidability (`Abdennadher et al. 1999`) is **known not to apply** to non-terminating CHR programs or to unions of individually confluent programs without checking cross-module critical pairs.

## Evidence

### Pinned Upstream Repositories and Source Citations

1. **`SWI-Prolog/swipl-devel`** at commit `3992b97ba46231c1a27ef39d06f52f7c92a52e49`:
   - `src/SWI-Prolog.h`: L204 (`typedef uintptr_t term_t; /* opaque term handle */`), L321–322 (`PL_succeed`/`PL_fail`), L332–333 (`PL_retry` `sizeof(ptr)-2` bits signed intptr_t constraint), L336–352 (`PL_FIRST_CALL (0)`, `PL_PRUNED (1)`, `PL_REDO (2)`, `PL_RESUME (3)`, `PL_retry`, `PL_retry_address`, `PL_yield_address`, `PL_foreign_control`), L368 (`PL_FA_NONDETERMINISTIC (0x04)`), L445–448 (`PL_open_foreign_frame`, `PL_rewind_foreign_frame`, `PL_close_foreign_frame`, `PL_discard_foreign_frame`), L459–463 (`PL_open_query`, `PL_next_solution`, `PL_close_query`, `PL_cut_query`).
   - `src/pl-fli.c`: L5099 (`PL_rewind_foreign_frame`), L5305 & L5601 (`PL_discard_foreign_frame`).
   - `src/pl-tabling.c`: native SLG tabling runtime.
2. **`mthom/scryer-prolog`** at commit `47f2c4e7cf9232137e2d43c7190c5504eb1a0045`:
   - `src/machine/machine_state.rs`: L118–157 (`MachineState` struct: `b`, `b0`, `e`, `cp`, `heap`, `stack`, `trail: Vec<TrailEntry>`, `tr`, `hb`, `attr_var_init`, `ball_stack`, `occurs_check: &'static dyn OccursCheckImpl`).
   - `src/machine/stack.rs`: L12–95 (`RawBlock<Stack>`, `AndFramePrelude`, `AndFrame`, `with_exposed_provenance` slot indexing past prelude).
3. **`Mercury-Language/mercury`** at commit `ec2bc5ccbf9aa77641ae09380ee46bbc731079cc`:
   - `doc/mercury_reference_manual.texi`: L4289–4290 (`mostly_unique`), L4684–4694 (`pragma promise_equivalent_clauses`), L4737–4785 (unique modes `uo`, `ui`, `di`; `det`/`cc_multi` restriction), L4830–4845 (`Limitations of the current implementation`: no nested unique modes, no `ui`, no automatic `dead` reuse), L4858–4913 (`Determinism categories` 2×3 matrix), L9429–9460 (`will_not_modify_trail`/`may_modify_trail`, `will_not_call_mm_tabled`/`may_call_mm_tabled`, `affects_liveness`), L9589–9590 (`It is an error to export a Mercury procedure that has a determinism of multi or nondet`), L10759–10781 (`SUCCESS_INDICATOR` assignment contract in C `foreign_proc`).
   - `compiler/ml_call_gen.m`: L768–794 (`determinism_to_code_model`, `model_non` generating `success_cont(FuncPtrRval, EnvPtrRval, _)` appended to `ArgRvals`, `model_semi` prepending `Success` to `RetLvals`).
   - `compiler/det_analysis.m` (L355), `compiler/modes.m`, `compiler/unique_modes.m`, `compiler/mlds_to_c_func.m`.
4. **`potassco/clingo`** at commit `f1d4b8e63a665898fddf4a620333eb0a1bfdebd9`:
   - `libclingo/clingo.h`: L728–729 (theory-atom reset after `clingo_control_solve`), L1131–1147 (`clingo_propagator_check_mode_e` and `clingo_propagator_undo_mode_e`), L1482–1507 (`struct clingo_propagator`, `init` phase boundary, `propagate` conflict-return contract), L2954–2970 (`clingo_ground_callback_t`, backend types including `aspif` and `reify`).
5. **`michaelballantyne/faster-miniKanren`** at commit `a25c70209800ab781983ace5c6840784bb32b4da`:
   - `mk.scm`: L285–298 (`mplus` swapping on immature stream `f^`, `bind`), L317–340 (`suspend`, `mplus*`, `fresh`), L486 & L608–680 (`absento`, `normalize-diseq`).
6. **`SWI-Prolog/packages-chr`** at commit `3f81d6be337cd547b218922e1f4fd36121472bf1`: `chr_runtime.pl`, `chr_swi.pl`.
7. **`LPCIC/elpi`** at commit `631d14a63489ed0e8359ad036f7a8580bb373f33`: `README.md`.

### Peer-Reviewed Literature and Standards Verified

- Warren (1983), *An Abstract Prolog Instruction Set*, SRI Technical Note 309; Aït-Kaci (1991), *Warren's Abstract Machine: A Tutorial Reconstruction*, MIT Press.
- ISO/IEC 13211-1:1995, *Information technology — Programming languages — Prolog — Part 1: General core*; Lindholm & O'Keefe (ICLP 1987); *Extending the Logical Update View with Transaction Support* (`arXiv:1301.7669`).
- Chen & Warren (1996), *Tabled Evaluation with Delaying for General Logic Programs*, JACM 43(1), DOI `10.1145/227595.227597`; Desouter, van Dooren & Schrijvers (TPLP/ICLP 2015), `arXiv:1507.08087`.
- Somogyi, Henderson & Conway (1996), *The Execution Algorithm of Mercury, an Efficient Purely Declarative Logic Programming Language*, JLP 29(1-3), DOI `10.1016/S0743-1066(96)00068-4`; Henderson & Somogyi (CC 2002).
- Augustsson, Breitner, Claessen, Jhala, Peyton Jones, Shivers, Steele & Sweeney (2023), *The Verse Calculus: A Core Calculus for Deterministic Functional Logic Programming*, PACMPL 7(ICFP), Article 203, DOI `10.1145/3607845`.
- Kiselyov, Shan, Friedman & Sabry (2005), *Backtracking, Interleaving, and Terminating Monad Transformers*, ICFP 2005, DOI `10.1145/1086365.1086390`; Hemann & Friedman (Scheme Workshop 2013); Byrd et al. (ICFP 2017).
- Antoy, Echahed & Hanus (JACM 2000); Fischer, Kiselyov & Shan (ICFP 2009); Jaffar & Lassez (POPL 1987).
- Gelfond & Lifschitz (ICLP/SLP 1988); Gebser, Kaminski, Kaufmann & Schaub (2019), *Multi-shot ASP solving with clingo*, TPLP 19(1), pp. 27–82, DOI `10.1017/S147406841800018X`; lazy-grounding survey (`arXiv:1903.12510`).
- Frühwirth (1998), *Theory and Practice of Constraint Handling Rules*, JLP 37, DOI `10.1016/S0743-1066(98)10005-5`; Abdennadher, Frühwirth & Meuss (1999), *Confluence and Semantics of Constraint Simplification Rules*, Constraints 4(2), pp. 133–165, DOI `10.1023/A:1009809016172`; Duck et al. (ICLP 2004); Sulzmann, Duck, Peyton Jones & Stuckey (JFP 2007).
- Miller (JLC 1991); Dunchev et al. (LPAR 2015); Selsam, Ullrich & de Moura (`arXiv:2001.04301`); Bjørner et al. (2015); Matsushita, Tsukada & Kobayashi (ESOP 2020); Tang, Hillerström, Lindley & Morris (2024), *Soundly Handling Linearity*, PACMPL 8(POPL), DOI `10.1145/3632896`.

### Executable Reference Probe Output (`Basis: execution`)

Observed on Linux x86_64 with Python 3.13 (`2026-11-19`) by running the standalone script below (reproducing WAM conditional trailing, occurs-check vs. rational-tree cycle, SLD vs. SLG fixpoint and Gelfond-Lifschitz stable models, `faster-miniKanren` `mplus` interleaving, Verse `all{}`/`one{}`, and CHR union non-confluence):

```text
=== 1A. WAM Conditional Trailing & Untrailed Foreign Mutation Hazard ===
Before backtrack: x=('ATOM', 'a') (trailed=True), y=('ATOM', 'b') (trailed=False), trail=[0], foreign_counter=1
After backtrack:  x=('REF', 0), len(heap)=1, trail=[], foreign_counter=1 (LEAKED!)

=== 1B. Occurs Check vs Cyclic Rational Tree ===
Occurs check on X = f(X): True -> rejected under finite-tree semantics
Without occurs check: traversing X = f(X) unrolls indefinitely (depth 6 reached without base case)

=== 1C. SLD Divergence vs SLG Well-Founded 3-Valued Semantics ===
SLD left-recursive path(a,Y): diverged after 10 left-recursive expansions
SLG tabled path(a,Y): ['a', 'b', 'c']
Stable models of {p :- not p}: [] (WFS assigns p=UNDEFINED)
Stable models of {a :- not b; b :- not a}: [['a'], ['b']] (WFS assigns a=UNDEFINED, b=UNDEFINED)

=== 1D. miniKanren Interleaving (mplus/bind) vs Depth-First ===
Interleaving mplus(fives, sixes) first 8: [5, 6, 5, 6, 5, 6, 5, 6]

=== 1E. Verse Calculus Choice Floating (all{} / one{}) ===
Verse all{x = (1|2); y = (10|20); x + y} = (11, 21, 12, 22)
Verse one{x = (1|2); x = 2; x * 10} = 20

=== 1F. CHR Confluence vs Non-Confluent Union ===
Union R1 U R2 under order [R1, R2]: ('b',)
Union R1 U R2 under order [R2, R1]: ('c',) -> NON-CONFLUENT critical pair (b, c)!
```

## Revalidation

1. **Diff pinned FFI and compiler contracts against newer revisions:**
   - **SWI-Prolog:** Check `src/SWI-Prolog.h` (`PL_FIRST_CALL`, `PL_PRUNED`, `PL_REDO`, `PL_RESUME`, `PL_retry`, `PL_FA_NONDETERMINISTIC`, `PL_open_foreign_frame`) for changes in `foreign_t` bit tagging or foreign-frame invariants.
   - **Mercury:** Check `doc/mercury_reference_manual.texi` sections `Limitations of the current implementation` (whether nested unique modes, `ui`, or compile-time `dead` reuse have been implemented) and `Calling Mercury from foreign code` (whether `multi`/`nondet` C export remains an error), and diff `compiler/ml_call_gen.m` around `determinism_to_code_model` (`model_non` continuation signature).
   - **Clingo:** Check `libclingo/clingo.h` (or Clingo 6 C API headers under `lib/c-api/include/clingo/`) for changes to `clingo_propagator` lifecycle (`init`/`propagate`/`undo`/`check`) and `clingo_ground_callback_t`.
2. **Re-run the standalone Python 3 semantic probe:**

```bash
python3 - <<'EOF'
# Minimal check of WAM conditional trail leak, Gelfond-Lifschitz stable models, mplus interleaving, and CHR union non-confluence
# 1. WAM conditional trailing & untrailed foreign mutation leak
heap, trail, foreign = [("REF", 0)], [], [0]
hb, tr = len(heap), len(trail)
heap.append(("REF", 1))
heap[0] = ("ATOM", "a"); trail.append(0)  # addr 0 < hb -> trailed
heap[1] = ("ATOM", "b")                   # addr 1 >= hb -> not trailed
foreign[0] += 1                           # untrailed foreign side effect
while len(trail) > tr: a = trail.pop(); heap[a] = ("REF", a)
del heap[hb:]
assert heap == [("REF", 0)] and foreign[0] == 1

# 2. miniKanren mplus interleaving (faster-miniKanren mk.scm L285-290)
def mplus(s1, s2):
    if s1 is None: return s2()
    if callable(s1): return lambda: mplus(s2(), s1)
    return (s1[0], lambda: mplus(s2(), s1[1]))
def take(n, s):
    out = []
    while n > 0 and s is not None:
        if callable(s): s = s()
        else: out.append(s[0]); s = s[1]; n -= 1
    return out
def fives(): return lambda: (5, fives())
def sixes(): return lambda: (6, sixes())
assert take(6, mplus(fives(), sixes)) == [5, 6, 5, 6, 5, 6]

# 3. CHR union non-confluence (R1: a<=>b, R2: a<=>c)
def chr_run(rules):
    s = ["a"]
    for lhs, rhs in rules:
        if lhs in s: s.remove(lhs); s.append(rhs); break
    return tuple(s)
assert chr_run([("a", "b"), ("a", "c")]) != chr_run([("a", "c"), ("a", "b")])
print("PASS: WAM trail leak, mplus interleaving, and CHR union non-confluence verified")
EOF
```

3. **Live native toolchain revalidation (when `mmc` and `swipl` are available):**
   - Compile a minimal Mercury module containing `:- pragma foreign_export("C", p(out), "c_p").` where `p(out)` has determinism `det`, `semidet`, and `nondet`, confirming `mmc` accepts `det`/`semidet` and rejects `nondet` with a determinism export error.
   - Compile and run a SWI-Prolog C foreign predicate registered with `PL_FA_NONDETERMINISTIC` returning `PL_retry(1)` and test `once(my_pred(X))` to observe the exact `PL_FIRST_CALL` -> `PL_PRUNED` transition sequence.
