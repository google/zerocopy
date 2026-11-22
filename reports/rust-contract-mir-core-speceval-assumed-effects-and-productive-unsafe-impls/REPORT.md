# Rust Contract MIR Core Semantics: Pure Closure `SpecEval`, Effect-Indexed Assumed Calls, `extern "C"` Unwinding, and Productive `unsafe impl` Stratification

## Summary

Empirical `rustc` `Runtime(PostCleanup)` MIR probes across two nightlies six months apart (`1.98.0-nightly` `f8a08b688` and `1.102.0-nightly` `6905905bb`), source inspection of Anneal's trusted MIR semantics (`google/zerocopy@a007a51af473e5901915b003083e61c7c89c7bd1`), and a 25-theorem zero-`sorry` Lean `v4.34.1` mechanization (`support/SpecCoreSoundness.lean`, axioms strictly within `{propext, Classical.choice, Quot.sound}`) establish six foundational soundness invariants for a syntax-independent Rust specification core (`FnContract` + `SpecEval` + `InvariantEnv`):

1. **Strict `safetyPre` vs. `behaviorPre` separation:** On a safe Rust function (`isUnsafe = false`), a `#[requires]` contract MUST NOT guard `WellFormed` (UB-freedom); safe callers can invoke the function outside `#[requires]` under `-Zcontract-checks=no`. Only `unsafe fn` (`isUnsafe = true`) may assume `safetyPre` for `WellFormed`; `behaviorPre` gates postconditions and effect obligations (`postReturn`, `postUnwind`, `postAbort`, `terminates`, `noUnwind`, `noAbort`) on both safe and unsafe functions (`safe_fn_requires_cannot_waive_ub`).
2. **General 8-mask `AssumedContractRealizable` & `extern "C"` ABI unwinding:** Restricting realizability checks to only `(terminates = true, noUnwind = true, noAbort = true)` leaves a soundness hole when `terminates = true, noUnwind = false, noAbort = true` and both `postReturn` and `postUnwind` are `False` (`three_way_only_realizability_gap_witness`). The exact condition equivalent to demonic call-choice inhabitation (`realizable_iff_valid_choice_inhabited`) is the 4-way disjunction over enabled outcomes (`terminates = false ∨ ∃ out, postReturn q out ∨ (noUnwind = false ∧ ∃ m, postUnwind q m) ∨ (noAbort = false ∧ ∃ m, postAbort q m)`). Moreover, `rustc` emits `unwind unreachable` on every call to a foreign `extern "C"` function under both `-C panic=unwind` and `-C panic=abort` (and emits `bb (cleanup): { terminate(abi); }` for foreign `extern "C-unwind"` under `-C panic=abort`), so foreign `extern "C"` assumed contracts MUST set `noUnwind = true` (`extern_c_fails_without_noUnwind`, `extern_c_wellFormed_with_noUnwind`).
3. **Mutual recursion soundness boundary:** Modular assume-guarantee over arbitrary mutual recursion is unconditionally sound for safety and partial correctness (`terminates = false`, `mutual_recursion_partial_sound`), unconditionally unsound for termination without a well-founded measure (`mutual_recursion_termination_unsound_without_measure`), and sound for total correctness when every recursive call within a `terminates = true` SCC strictly decreases a `Nat` measure (`mutual_recursion_termination_sound_with_measure`).
4. **Stepwise `callerMem` immutability, `#139548` outer-block rejection, and short-circuiting in `SpecEval`:** `rustc` accepts `#[requires({ x.set(99); true })]` on `&Cell<u32>` without warning and places outer-block mutations (`#[ensures({ *x = 0; move |_| true })]`, upstream issue `rust-lang/rust#139548`) inside the `const false` scaffold block before closure construction. Endpoint-only equality `mem' = q.callerMem` wrongly accepts intermediate write-then-restore on `UnsafeCell`, whereas stepwise immutability (`∀ s_mid, Reaches s₀ s_mid → stateCallerMem s_mid = q.callerMem`) rejects both (`specEval_rejects_cell_mutation`, `stepwise_specEval_rejects_mutate_and_restore_while_endpoint_accepts`), while fail-closed scaffold validation rejects any non-capture statement in the dead prologue block. Multi-clause contracts MUST compose with short-circuiting `&&` rather than eager bitwise `&` (`short_circuit_clause_safe_vs_eager_panics`).
5. **Universal dead-branch marker ABI (`if false { contract_requires(...); let o = contract_old(...); contract_ensures::<Ret, _>(...); }`) works on stable/nightly Rust without `'static` or `Copy` walls:** Across all 28 MIR bodies of six test shapes (`&mut u32`, moved `Vec<u8>`, non-`'static` `&'a [u8]`, generic `<T: Copy + PartialEq>`, early `return` + `unwinds_if`, `mut` value param), the `if false` prologue passes borrowck and produces **100% byte-identical** `Runtime(PostCleanup)` MIR across `1.98.0-nightly` and `1.102.0-nightly`, while dead-branch erasure preserves `WellFormed`, `Behavior`, and `Diverges` bidirectionally (`dead_branch_erasure_{wellFormed,diverges,behavior}_iff`).
6. **`ProductiveUnsafeImpl` replaces naive `NoUnsafeImplCycles`:** A naive rule banning any trait-impl dependency cycle touching an `unsafe impl` falsely rejects standard `struct BoxNode { next: Option<Box<BoxNode>> }` because `alloc`'s `unsafe impl<T: Send> Send for Box<T>` sits directly on the cycle `BoxNode: Send → Option<Box<BoxNode>>: Send → Box<BoxNode>: Send → BoxNode: Send` (`naive_scc_rejects_box_node`). Requiring every cycle to cross at least one indirection-guarded (`isIndirectionGuarded = true`) edge paired with a depth-indexed well-founded proof obligation admits `BoxNode: Send` (`boxNode_send_well_founded`) while rejecting both `unsafe impl Send for NotSend where NotSend: Send {}`, mutual auto/unsafe cycles, and fake wrappers containing `Rc<()>` (`productive_gate_admits_boxNode_and_rejects_unsound_cycles`, `notSend_and_fakeBox_unprovable`).

## Applicability

- **Compiler probes:** Directly executed on `x86_64-unknown-linux-gnu` with `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` (`LLVM 22.1.6`) and `rustc 1.102.0-nightly (6905905bb 2026-11-19)` (`LLVM 23.1.6`), Edition 2024, `-Z mir-preserve-ub`, inspecting `*.3-2-000.runtime-post-cleanup.after.mir` (the exact `mir_drops_elaborated_and_const_checked` phase captured by `anneal/trusted/rustc-capture/src/capture.rs:743`).
  - **Shared across both nightlies:** All 28 `Runtime(PostCleanup)` MIR bodies for the universal dead-branch marker ABI, all 6 `-C panic=unwind` and 6 `-C panic=abort` ABI unwinding bodies, `core::contracts` `const false` vs. `const true` switching (`-Zcontract-checks=no` vs. `yes`), `#139548` outer-block placement inside dead `bb1`, and classic + `-Znext-solver` trait acceptance/rejection across all three coinductive impl probes are identical across both nightlies.
  - **Differs between nightlies:** In `1.102.0-nightly`, `Box` deref inside `f_alloc_in_req::{closure#0}` lowers via `BoxRaw<u32> as *const u32 (BoxDerefTransmute)` rather than `Unique<u32>.0 as *const u32 (Transmute)`, and empty synthetic debug scopes (`scope 3 {}`) are omitted in `f_early_ret` and `f_mut_param_ensures`.
- **Anneal MIR baseline:** Direct source inspection of `google/zerocopy@a007a51af473e5901915b003083e61c7c89c7bd1` (`anneal/trusted/lean/Trusted/{MirModel,MirAst/Terminators,MirAst/Body,MirSemantics/Boundary,MirSemantics/State,MirSemantics/Step}.lean`, `anneal/trusted/rustc-capture/src/{capture,driver,extract,ir}.rs`).
- **Lean mechanization (`support/SpecCoreSoundness.lean`):** Self-contained abstract operational model compiled under `leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) using core `Init` only. Its theorems characterize the abstract operational semantics and contract judgments directly; they do not mechanize a full correspondence proof against `rustc` or `Trusted.MirSemantics.evalStep`.

## Findings

### 1. Live `rustc` `Runtime(PostCleanup)` MIR Lowering of `core::contracts` and Universal Dead-Branch Marker ABI

`Basis: execution + source`

1. **`core::contracts` (`#![feature(contracts)]`, `rust-lang/rust#128044`) on `&mut T`, `&Cell<T>`, `mut` params, and `#139548` (`support/probe_core_contracts.rs`, `support/probe_139548.rs`):**
   - For `#[requires(*x > 0)] pub fn f_mut_ref(x: &mut u32) -> u32`, `Runtime(PostCleanup)` MIR emits `bb0: _3 = const false; switchInt(move _3) -> [0: bb3, otherwise: bb1];` under default `-Zcontract-checks=no`, and flips solely `_3 = const true` under `-Zcontract-checks=yes`. Inside `bb1`, `rustc` constructs `_6 = &(*_1)` (a shared reborrow of the mutable pointee) before passing `{closure#0} { x: move _6 }` to `contract_check_requires`. Thus `-Zcontract-checks=yes` injects a live shared reborrow (perturbing Tree Borrows state) and converts violated `requires` into `panic_nounwind` aborts that mask UB absent in production builds.
   - `#[ensures(|r| *r == x + 1)]` without `move` fails with `E0597` (`requires that x is borrowed for 'static` at `library/core/src/contracts.rs:21`) and `E0506` (`cannot assign to x because it is borrowed`); adding `move` (`#[ensures(move |r| *r == x + 1)]`) compiles for `Copy + 'static` parameters because `{closure#1}` captures `copy _1` in `bb2` prior to body execution.
   - `#[requires({ x.set(99); true })]` on `x: &Cell<u32>` compiles cleanly with zero warnings, emitting `Cell::<u32>::set(move _3, const 99_u32)` inside `{closure#0}`. Rust's `Fn() -> bool` signature therefore does **not** guarantee read-only contract evaluation.
   - `#[requires(a / b > 0 && a + b < 100)]` emits `assert(!move _6, "attempt to divide ... by zero")` and `AddWithOverflow` + `assert(!move (_10.1: bool), ...)` inside `{closure#0}`, with short-circuiting `switchInt(move _2)` between the two conjuncts.
   - For `#[ensures({ *x = 0; move |_| true })]` (`support/probe_139548.rs`), both `1.98.0-nightly` and `1.102.0-nightly` place `(*_1) = const 0_u32;` inside the dead `const false` block `bb1` immediately before `_5 = {closure#0}` and `build_check_ensures(move _5)`. A capture pass that inspects only `{closure#0}` without validating `bb1` would silently drop the outer-block side effect; `rustc-capture` must therefore fail closed if the dead scaffold contains any statement other than `StorageLive`/`StorageDead`, pure reference/copy capture setup, closure `Aggregate` construction, and the recognized contract marker call.

2. **Syntax-agnostic Universal Dead-Branch Marker ABI (`support/probe_universal_dead_branch_abi.rs`):**
   - Placing four ordinary `#[inline(never)]` marker calls (`contract_requires<F: FnOnce() -> bool>`, `contract_old<T, F: FnOnce() -> T> -> T`, `contract_ensures<Ret: ?Sized, F: FnOnce(&Ret) -> bool>`, `contract_unwinds_if<F: FnOnce() -> bool>`) inside a single entry `if false { ... }` prologue compiles cleanly on **both** `1.98.0-nightly` and `1.102.0-nightly` without `#![feature(contracts)]`, without `+ 'static`, and without `+ Copy`:
     - `bump_mut(x: &mut u32) -> u32`: `requires(|| *x < u32::MAX)`, `let __old_0 = old(|| *x)`, `ensures::<u32, _>(|ret| *x == __old_0 + 1 && *ret == __old_0)` — borrowck closes all prologue borrows before the body mutates `*x`.
     - `consume_non_copy(v: Vec<u8>) -> usize`: borrows `&v` in `requires` and `old(|| v.len())` before the body moves and drops `v`.
     - `lifetime_ref<'a>(s: &'a [u8]) -> &'a u8`: captures non-`'static` references directly.
     - `generic_swap<T: Copy + PartialEq>(x: &mut T, y: T) -> T`: captures generic parameters directly.
     - `mut_ref_early_ret(x: &mut u32) -> Result<u32, u32>`: handles multiple `return` paths and `unwinds_if` without duplicating postcondition blocks at every exit.
   - All 28 `Runtime(PostCleanup)` MIR bodies are byte-identical across `1.98.0-nightly` and `1.102.0-nightly`. In `bump_mut`, `{closure#2}`'s `Aggregate` explicitly lists `{ x: &(*_1), __old_0: &_7 }` and accepts `_2: &u32`, giving an unambiguous capture map:
     - `requires` and `old_i` closures evaluate in `(q.args, q.callerMem)` (pre-state), yielding pre-state snapshot values `v_old_i : Val` via `SpecEvalVal` (avoiding `AllocId` collisions between pre-state and post-state memory!).
     - `ensures` evaluates in `out.callerMem` (post-state), reading post-state `*x` through `q.args[i]` in `out.callerMem`, pre-state snapshots from fresh read-only allocations holding `v_old_i`, and return value from a fresh read-only allocation holding `out.ret`.
   - When pruning the dead `const false` prologue blocks from the runtime CFG, `rustc-capture` must verify that no surviving runtime local has its sole `StorageLive`/`StorageDead` annotation inside the pruned blocks (preserving `hasStorageAnnotation`), and `dead_branch_erasure_{wellFormed,diverges,behavior}_iff` proves exact bidirectional equivalence across all three operational judgments.

### 2. Foreign ABI Unwinding (`extern "C"` vs. `extern "C-unwind"`) and `-> !` in `Runtime(PostCleanup)` MIR

`Basis: execution + source + derived`

Inspecting `support/probe_abi_unwind_never.rs` across both nightlies under `-C panic=unwind` and `-C panic=abort` yields an exact ABI terminator table:

| Function / Call Pattern | `-C panic=unwind` (`Runtime(PostCleanup)`) | `-C panic=abort` (`Runtime(PostCleanup)`) | Required `FnContract` Semantics |
| :--- | :--- | :--- | :--- |
| Call to `unsafe extern "C" { fn ext_c(u32) -> u32; }` | `ext_c(move _2) -> [return: bb1, unwind unreachable]` | `ext_c(move _2) -> [return: bb1, unwind unreachable]` | **MUST set `noUnwind = true`** (otherwise demonic unwind hits `UnwindAction.unreachable → .fault .undefined`) |
| Call to `unsafe extern "C-unwind" { fn ext_c_unwind(u32) -> u32; }` | `ext_c_unwind(move _2) -> [return: bb1, unwind continue]` | `ext_c_unwind(move _2) -> [return: bb1, unwind: bb2]` with `bb2 (cleanup): { terminate(abi); }` | Defaults to `noUnwind = false`; requires `TerminatorKind.unwindTerminate` in `Trusted.MirAst` stepping to `.done (.aborted callerMem)` |
| Call to `unsafe extern "C" { fn ext_abort() -> !; }` | `ext_abort() -> unwind unreachable` (`target: None`) | `ext_abort() -> unwind unreachable` (`target: None`) | `noUnwind = true`, `postReturn := False` (automatically enforced via `ValidVal .never _ = False`) |
| Rust-defined `pub extern "C" fn` panicking | `panic_fmt(...) -> unwind terminate(abi)` | `panic_fmt(...) -> unwind unreachable` | Never unwinds out of frame; aborts (`.aborted`) under `panic=unwind` |
| Rust-defined `pub extern "C-unwind" fn` panicking | `panic_fmt(...) -> unwind continue` | `panic_fmt(...) -> unwind unreachable` | May unwind (`.unwound`) under `panic=unwind` |

In `google/zerocopy@a007a51af473e5901915b003083e61c7c89c7bd1`, `Trusted/MirAst/Terminators.lean:155-157` maps `TerminatorKind::UnwindTerminate` to `.unsupported` and `Trusted/MirModel.lean:181-183` defines only `TerminalOut.{returned, unwound}`. Supporting `extern "C-unwind"` under `-C panic=abort` and `extern "C"` panics therefore requires adding both `TerminalOut.aborted (callerMem : CallerMemory := ⟨[]⟩)` and `TerminatorKind.unwindTerminate`.

### 3. Effect-Indexed `FnContract`, 8-Mask Realizability, and Mutual Recursion Soundness

`Basis: execution (Lean kernel) + derived`

In `support/SpecCoreSoundness.lean` (25 kernel-checked theorems, zero `sorry`):

1. **Safe-function soundness (`conflated_pre_wrongly_accepts_unsound_safe_fn`, `safe_fn_requires_cannot_waive_ub`):** Conflating `behaviorPre` with `safetyPre` lets a safe function with `#[requires(x < 10)]` that executes UB on `x = 20` pass verification. Splitting `FnContract` into `safetyPre` (active strictly when `isUnsafe = true`, matching `Trusted.MirSemantics.BodyVerified` at `Boundary.lean:251`) and `behaviorPre` (guarding `postReturn`, `postUnwind`, `postAbort`, and `EffectMask` only) rejects the unsound safe function while allowing safe functions to carry behavioral contracts.
2. **Exact 8-mask realizability (`default_partial_always_realizable`, `three_way_only_realizability_gap_witness`, `realizable_iff_valid_choice_inhabited`):** Checking realizability only when `terminates ∧ noUnwind ∧ noAbort` are all `true` misses `(terminates = true, noUnwind = false, noAbort = true)` with `postReturn = False ∧ postUnwind = False`. The 4-way disjunction
   ```lean
   def AssumedContractRealizable (isUnsafe : Bool) (c : FnContract) : Prop :=
     ∀ q, c.effectiveBehaviorPre isUnsafe q →
       (c.effects.terminates = false) ∨
       (∃ out, c.postReturn q out) ∨
       (c.effects.noUnwind = false ∧ ∃ mem, c.postUnwind q mem) ∨
       (c.effects.noAbort  = false ∧ ∃ mem, c.postAbort  q mem)
   ```
   is proved logically equivalent (`↔`) to `ValidAssumedChoice` inhabitation across all 8 `EffectMask` bit combinations. Under default `terminates = false`, it holds unconditionally (`Or.inl rfl`) even for `postReturn = False` (`-> !` or `#[ensures(false)]`), making `False` derivation impossible.
3. **Call-site ABI interaction (`extern_c_fails_without_noUnwind`, `extern_c_wellFormed_with_noUnwind`):** Invoking an assumed callee at a call site with `UnwindAction.unreachable` faults `.undefined` whenever `c.effects.noUnwind = false` and `c.postUnwind` is inhabited, and is `WellFormed` when `c.effects.noUnwind = true` and `ValidAssumedChoice` is inhabited.
4. **Mutual recursion (`mutual_recursion_partial_sound`, `mutual_recursion_termination_unsound_without_measure`, `mutual_recursion_termination_sound_with_measure`):** For partial correctness (`terminates = false`), modular assume-guarantee over arbitrary mutual recursion is sound by strong induction on execution step depth. For `terminates = true`, unmeasured modular assume-guarantee accepts infinite mutual recursion `f() { g() } / g() { f() }`; adding a well-founded decreasing `Nat` measure across `terminates = true` SCCs restores concrete termination soundness.

### 4. `SpecEval` Stepwise Immutability and Short-Circuiting Semantics

`Basis: execution (Lean kernel) + execution (rustc)`

1. **Stepwise `callerMem` immutability (`specEval_rejects_cell_mutation`, `stepwise_specEval_rejects_mutate_and_restore_while_endpoint_accepts`, `specEval_rejects_panic`):** Requiring `∀ s₀ s_mid, initState q = .ok s₀ → Reaches s₀ s_mid → stateCallerMem s_mid = q.callerMem` (in addition to `WellFormed`, `¬ Diverges`, and `Behavior q out → out = .returned ⟨v, q.callerMem⟩`) rejects both persistent `Cell::set` mutation and intermediate write-then-restore on `UnsafeCell`, whereas endpoint-only `mem' = q.callerMem` accepts intermediate write-then-restore.
2. **Short-circuiting clause conjunction (`short_circuit_clause_safe_vs_eager_panics`):** Joining dependent multi-clause specs (`[i < len, arr[i] == 0]`) with eager bitwise `&` evaluates `arr[i]` when `i == len` and panics/UBs; short-circuiting `&&` (or sequential `SpecEvalClauses` conjunction in `Prop`) returns `false` cleanly without evaluating later clauses.

### 5. `InvariantEnv`, `ProductiveUnsafeImpl` (Fixing Naive `NoUnsafeImplCycles`), and `VisCone`

`Basis: execution (rustc + Lean kernel) + source`

1. **Live `rustc` solver behavior (`support/probe_coinductive_*.rs`):** On both `1.98.0-nightly` and `1.102.0-nightly`, under both classic and `-Znext-solver`:
   - `probe_coinductive_unsafe_impls.rs` is **ACCEPTED** — admitting BOTH unsound coinductive `unsafe impl Send for NotSend where NotSend: Send {}` and mutual `MutA(MutB)` / `unsafe impl Send for MutB where MutA: Send {}` alongside legitimate `BoxNode { next: Option<Box<BoxNode>> }` and custom `MyBox<T>` / `MyNode`.
   - `probe_coinductive_wrap_growth.rs` (`unsafe impl<T> Send for Wrap<T> where Wrap<Wrap<T>>: Send {}`) and `probe_coinductive_non_auto.rs` (`unsafe impl MyUnsafe for S where S: MyUnsafe {}`) are **REJECTED** with `E0275`.
2. **Counterexample to naive SCC rejection (`naive_scc_rejects_box_node`):** Because `alloc::boxed::Box<T>` implements `Send` via an `unsafe impl<T: Send> Send for Box<T>`, the trait-impl dependency graph for `struct BoxNode { next: Option<Box<BoxNode>> }` contains the 3-cycle `BoxNode: Send → Option<Box<BoxNode>>: Send → Box<BoxNode>: Send (unsafe impl) → BoxNode: Send`. A naive gate rejecting every cycle touching an `unsafe impl` therefore rejects standard recursive `Box` data structures.
3. **Sound stratification (`boxNode_send_well_founded`, `productive_gate_admits_boxNode_and_rejects_unsound_cycles`, `notSend_and_fakeBox_unprovable`):** Defining `SendAt : Nat → TyRep → Prop` indexed by finite heap-indirection depth `d` and requiring every cycle in the trait-impl dependency graph to traverse at least one indirection-guarded (`isIndirectionGuarded = true`) edge—while every `unsafe impl` still discharges its guarded depth-indexed proof obligation—proves `∀ d, SendAt d .boxNode` by ordinary induction on `d` while rejecting `NotSend`, `MutA`/`MutB`, and structurally subterm-decreasing but semantically unsound `FakeBox<T>(Rc<()>, PhantomData<T>)`.
4. **`FullValid` and `VisCone` unwind closure (`fromBytes_fullValid_rejects_nonZero`, `visCone_encapsulation_soundness`, `visCone_missing_unwind_breaks_invariant`):** Defining `FromBytes` over `FullValid := LangValid ∧ LibValid` rejects `NonZeroU32` where `LangValid`-only accepts it. For encapsulated types, every item in `VisCone(S)` must preserve `LibValid S` across **both** `.returned` and `.unwound` exits; omitting `.unwound` allows a `catch_unwind` client to observe a violated `LibValid`.

## Boundaries

- **Known not to apply:**
  - `SpecCoreSoundness.lean` proves its 25 theorems over a self-contained abstract operational semantics (`Sem`, `MemSem`, `MStmt`, `TyRep`), not by importing `Trusted.MirSemantics.evalStep` directly; lifting these results into `anneal/trusted/lean/` requires threading `TerminalOut.aborted`, `TerminatorKind.unwindTerminate`, and `CallerMemory` support for pointer/reference arguments into `Trusted.MirSemantics`.
  - Depth-indexed `SendAt : Nat → TyRep → Prop` models acyclic finite heap ownership (`Box`, `Vec`, structs/enums); cyclic interior-mutable shared heap graphs (`Arc<Mutex<Node>>` / `Rc<RefCell<Node>>`) require step-indexed later modalities (`▷`) or Kripke/Iris-style worlds (`not examined` in `SpecCoreSoundness.lean`).
- **Not examined:**
  - Async coroutines (`Coroutine` / `Yield`), `become` explicit tail calls, and CTFE (`const fn`) evaluation of `core::contracts` closures.
  - Reentrant FFI callbacks where an assumed `extern "C"` function calls back into a verified Rust function via a function pointer or trait object (creating a verified↔assumed mutual recursion cycle).
  - Full Tree Borrows tag-tree operational rules inside `Trusted.MirSemantics` (only the structural non-interference boundary of shadow-state `SpecEval` and empirical `rustc` `&(*_1)` reborrow emission were examined).
- **Unsupported (upstream `rustc` at both tested nightlies):**
  - Capturing non-`'static` references or non-`Copy` values in `#[core::contracts::ensures]` (`E0597` / `E0277` due to `C: Fn(&Ret) -> bool + Copy + 'static` in `library/core/src/contracts.rs:21`).
  - Stacking multiple `#[core::contracts::requires]` attributes on one function.

## Evidence

- **Anneal baseline (`google/zerocopy@a007a51af473e5901915b003083e61c7c89c7bd1`):**
  - `anneal/trusted/lean/Trusted/MirModel.lean:181-183` (`TerminalOut.{returned, unwound}` without `aborted`).
  - `anneal/trusted/lean/Trusted/MirAst/Terminators.lean:155-177` (`UnwindTerminate` collapsed to `.unsupported`).
  - `anneal/trusted/lean/Trusted/MirSemantics/Boundary.lean:245-252` (`BodyVerified` gating `safetyPre` strictly by `body.isUnsafe = true`).
  - `anneal/trusted/rustc-capture/src/capture.rs:74-76, 743-749` (`mir_drops_elaborated_and_const_checked` `Runtime(PostCleanup)` capture hook).
- **Preserved Lean 4 mechanization (`support/SpecCoreSoundness.lean`, SHA-256 `23cebaf03a78e86e1d99671d9dceb4dabe443553eccaf5478208147ca49040ce``6b8b6ed8a9de7ad6543278f314bfbe94d777c69ee71b456f1bf97acc0b375cc8`):**
  - Compiled on `2026-11-22` with `leanprover/lean4:v4.34.1` (`lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`): exit code `0`, `0` warnings, `25 / 25` theorems with zero `sorryAx` and axioms strictly within `{propext, Classical.choice, Quot.sound}`.
- **Preserved Rust compiler probes (`support/probe_*.rs`):**
  - Executed on `2026-11-22` under both `rustc 1.98.0-nightly (f8a08b688 2026-05-30)` and `rustc 1.102.0-nightly (6905905bb 2026-11-19)` (`--crate-type=lib --edition=2024 -Z mir-preserve-ub -Z dump-mir=all`):
    - `support/probe_core_contracts.rs` (`-Zcontract-checks=no` and `-Zcontract-checks=yes`)
    - `support/probe_139548.rs` (`-Zcontract-checks=no`)
    - `support/probe_universal_dead_branch_abi.rs` (28 MIR bodies byte-identical across both nightlies)
    - `support/probe_abi_unwind_never.rs` (`-C panic=unwind` and `-C panic=abort`, 6 + 6 MIR bodies byte-identical across both nightlies)
    - `support/probe_coinductive_unsafe_impls.rs` (ACCEPTED by classic and `-Znext-solver` on both nightlies)
    - `support/probe_coinductive_wrap_growth.rs` and `support/probe_coinductive_non_auto.rs` (REJECTED with `E0275` by classic and `-Znext-solver` on both nightlies)

## Revalidation

1. **Re-verify the 25-theorem Lean `v4.34.1` kernel check (~3 s):**
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/SpecCoreSoundness.lean
   ```
   Confirm exit code `0`, zero warnings, and every `#print axioms` line lists only subsets of `{propext, Classical.choice, Quot.sound}` (zero `sorryAx`).
2. **Re-verify `rustc` `Runtime(PostCleanup)` MIR lowering and solver behavior on a new nightly:**
   ```bash
   OUT=/tmp/reval_spec_core && rm -rf "$OUT" && mkdir -p "$OUT"/{cc_no,cc_yes,uabi,abi_u,abi_a,p139548}
   rustc --crate-type=lib --edition=2024 -Z mir-preserve-ub -Z dump-mir=all \
     -Z dump-mir-dir="$OUT/cc_no" support/probe_core_contracts.rs -o "$OUT/libcc_no.rlib"
   rustc --crate-type=lib --edition=2024 -Z mir-preserve-ub -Z contract-checks=yes -Z dump-mir=all \
     -Z dump-mir-dir="$OUT/cc_yes" support/probe_core_contracts.rs -o "$OUT/libcc_yes.rlib"
   rustc --crate-type=lib --edition=2024 -Z mir-preserve-ub -Z dump-mir=all \
     -Z dump-mir-dir="$OUT/uabi" support/probe_universal_dead_branch_abi.rs -o "$OUT/libuabi.rlib"
   rustc --crate-type=lib --edition=2024 -C panic=unwind -Z mir-preserve-ub -Z dump-mir=all \
     -Z dump-mir-dir="$OUT/abi_u" support/probe_abi_unwind_never.rs -o "$OUT/libabi_u.rlib"
   rustc --crate-type=lib --edition=2024 -C panic=abort -Z mir-preserve-ub -Z dump-mir=all \
     -Z dump-mir-dir="$OUT/abi_a" support/probe_abi_unwind_never.rs -o "$OUT/libabi_a.rlib"
   rustc --crate-type=lib --edition=2024 -Z mir-preserve-ub -Z dump-mir=all \
     -Z dump-mir-dir="$OUT/p139548" support/probe_139548.rs -o "$OUT/lib139548.rlib"
   rustc --crate-type=lib --edition=2024 support/probe_coinductive_unsafe_impls.rs -o "$OUT/libcoind.rlib"
   rustc --crate-type=lib --edition=2024 -Znext-solver support/probe_coinductive_unsafe_impls.rs -o "$OUT/libcoind_n.rlib"
   ```
   Check `*.3-2-000.runtime-post-cleanup.after.mir` to confirm whether: (a) `core::contracts` still guards `contract_check_requires`/`build_check_ensures` under `switchInt(const false)` at `-Zcontract-checks=no`, (b) `probe_139548.rs` still places `(*_1) = const 0_u32` inside `bb1`, (c) `probe_universal_dead_branch_abi.rs` still preserves the `if false` prologue and closure captures, (d) `call_ext_c` still emits `unwind unreachable` and `call_ext_c_unwind` under `-C panic=abort` still emits `terminate(abi)`, and (e) `rustc` still accepts `NotSend` / `MutB` coinductive `unsafe impl Send`.
