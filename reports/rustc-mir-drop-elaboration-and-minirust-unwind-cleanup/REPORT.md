# `rustc` MIR Drop Elaboration, Effectful Destructor Unwinding, and MiniRust `ResumeUnwind` Frame-Cleanup Semantics

## Summary

Rust's ownership, drop-order, partial-move, and unwinding rules are lowered by `rustc` into explicit `Runtime(PostCleanup)` Mid-level Intermediate Representation (MIR) control-flow graphs before reaching an operational semantics such as MiniRust. This report documents how `rustc` elaborates aggregate and scope destruction, partial moves with `std::mem::forget`, and unwinding destructor paths into explicit stack drop flags (`_16: bool`), normal and `(cleanup)` basic blocks, and `unwind terminate(cleanup)` edges; how those elaborated shapes map onto MiniRust's explicit `Call`, `StorageDead`, and `ResumeUnwind` primitives at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`; where `tooling/minimize` diverges from `rustc` MIR on unwinding drops; and how seven Lean 4.34.1 operational models verify the resulting control, memory-effect, and frame-pop invariants.

Key findings:

1. **Aggregate field drop order vs. scope drop order:** Under the pinned Rust Reference (`82da570bafd9efed421bdbae0f8603ede8dd308b`) and `core::ops::Drop` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), local variables and temporaries in a scope are dropped in **reverse declaration/creation order**, whereas fields of a struct or tuple are dropped in **declaration order** (first field before second field), even when the outer struct does not implement `Drop`.
2. **Configured `Runtime(PostCleanup)` MIR lowering (`cleanup.rs`):** In `exercise` (`support/cleanup_binding.mir:811-918` and `support/cleanup_binding.1.99.1.mir:811-918`), `rustc` uses CFG progression to track consumption of the unconditionally initialized first field `_4.0` and allocates a stack drop flag `_16: bool` only for the conditionally moved second field `_4.1`. Before the aggregate `_4 = Pair { first: move _5, second: move _6 }` is constructed at `bb2`, an unwind from the second constructor `make(2, ...)` at `bb1` branches to `bb9 (cleanup)`, which drops only the temporary `_5`. Once `_4` is constructed (`_16 = const true`), moving `_4.1` into `std::mem::forget` at `bb4` clears `_16 = const false`. If `drop((_4.0: Leaf))` panics at normal scope exit (`bb6`), control transfers to `bb11 (cleanup)`, which never retries `_4.0`, checks `_16` (`bb11 -> bb12`), drops `_4.1` if still owed with `unwind terminate(cleanup)`, and resumes unwinding at `bb10`.
3. **Destructor payload access vs. `MiniRust::Deinit`:** In `<Leaf as Drop>::drop` (`cleanup_binding.mir:690-743`), the destructor body reads `(*_1).1`, increments it via `wrapping_add(1)`, and writes it back at `bb2` before checking `panic_on_drop` (`(*_1).2`) at `bb2 -> bb3 -> bb4`. Clearing a drop obligation before destructor entry therefore cannot be lowered to `MiniRust::Deinit` (`spec/lang/step/statements.md:134-155`), which overwrites the place's bytes with `Uninit`; obligation clearing must leave payload bytes intact for `&mut self` destructor reads and writes.
4. **MiniRust `ResumeUnwind` phase ordering and `minimize` lowering gap:** MiniRust (`spec/lang/step/terminators.md:424-454`) has no `Drop` terminator or automatic drop-glue synthesis. Its `ResumeUnwind` step pops the active callee stack frame first (`stack.pop().unwrap()`), deallocates all live callee stack locals via `frame.storage_dead(&mut self.mem, local)?`, invokes `self.mem.end_call(frame.extra)?` (which in Tree Borrows releases the popped frame's protectors in list order and can fail mid-list with UB after mutating earlier allocation trees), and finally jumps to the caller's `unwind_block` (or raises UB on `BottomOfStack` or `unwind_block == None`). In `tooling/minimize/src/bb.rs:220-274`, `rs::TerminatorKind::Drop` is lowered to `Terminator::Call` with `unwind_block: None` (discarding the MIR `Drop` unwind edge) and `TerminatorKind::UnwindTerminate` is rejected with `span_bug!`.
5. **Machine-checked operational models and negative controls:** Seven Lean 4.34.1 modules (`Combined`, `CleanupElaboration`, `EffectfulDestructor`, `TwoCleanup`, `EffectfulControls`, `ResumeUnwindPhase`, and `ResumeUnwindPhaseControls`, totaling 141 `#print axioms` audits across target modules) formalize high-to-low drop-elaboration simulation, coupled 4-step effectful destructors over permissioned memory, structural well-formedness preservation across mid-destructor UB residuals, and two-frame `ResumeUnwind` execution over both monolithic (`TreeMemory`) and per-allocation factored (`TreeFactoredMemory`) representations, alongside mutant discriminators that fail if destructor writes are rolled back, if panicking destructors are retried, if the wrong frame's protector list is passed to `end_call`, or if frame pop is delayed until after `end_call`.

## Applicability

These findings apply to:

- Verification tools, MIR analyzers, and operational-semantics translations that lower `rustc` `Runtime(PostCleanup)` MIR into MiniRust or related abstract machines.
- Soundness arguments for unsafe Rust code interacting with partial moves, `std::mem::forget`, unwinding destructors (`-C panic=unwind`), and frame-exit borrow-protector release (`TreeBorrows::end_call`).
- Understanding the exact semantic boundary between `rustc`'s MIR drop elaboration pass (`Runtime(PostCleanup)`), `tooling/minimize`'s subset translator, and MiniRust's language-level `Return` and `ResumeUnwind` terminators.

Specific version and configuration anchors:

- **Rust compiler and standard library:** `rust-lang/rust` release `1.99.1` (commit `58cf8f9c35b355199727627d07ae34a4e2846d67`, verified locally on `x86_64-unknown-linux-gnu`) and prior MIR capture baseline `1.99.0` (commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `aarch64-apple-darwin`), compiled with `--edition=2024 -C opt-level=0 -C panic=unwind -C codegen-units=1 --emit=mir,link`.
- **Rust Reference:** `rust-lang/reference` commit `82da570bafd9efed421bdbae0f8603ede8dd308b`.
- **MiniRust specification and `minimize`:** `minirust/minirust` commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`.
- **Lean 4 kernel verification:** Lean `4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`, `x86_64-unknown-linux-gnu`).

## Findings

### 1. Normative and Documentation Contracts for Partial Moves, Drop Order, `forget`, and Unwinding

`Basis: normative | documentation`

The pinned Rust Reference (`82da570bafd9efed421bdbae0f8603ede8dd308b`) and `core` library documentation (`58cf8f9c35b355199727627d07ae34a4e2846d67`) establish six distinct obligations governing value destruction and unwinding:

| Obligation | Pinned Source Passages | Contract and Operational Consequence |
| --- | --- | --- |
| Partial move deinitialization | `src/expressions.md:193-217` (blob `1fc8a7076850949c740f70cfba523d69d1a0fa9e`) | Moving a non-`Copy` field out of a variable deinitializes that field and prevents the whole aggregate variable from being used as a single value, while remaining initialized fields stay usable and droppable. The enclosing struct must not implement `Drop`. |
| Aggregate field drop order | `src/destructors.md:5-18, 40-52` (blob `f9db534f8832c4598c4fbabac44d15ca6d3cb0f3`), `library/core/src/ops/drop.rs:9-16, 56-66` (blob `5d4b9f7dbeb9b4de002c0a5e91605216e75049b7`) | Dropping an initialized struct or tuple runs `<T as Drop>::drop` on the outer type (if implemented) and then recursively runs the destructors of its initialized fields in **declaration order** (field 0 before field 1). |
| Scope local and temporary drop order | `src/destructors.md:55-87`, `src/expressions/block-expr.md:51-67` (blob `cb64b33cd7dc6b2fa1dd37146f18f7825e1e486f`) | Variables declared in a block scope and temporaries within a temporary scope are dropped in **reverse declaration or creation order**. Consequently, while constructor temporaries `_5` and `_6` are live before aggregate construction, they follow reverse creation order; once moved into `Pair { first, second }`, the fields of `Pair` follow forward declaration order (`first` then `second`). |
| `std::mem::forget` suppression | `src/destructors.md:628-634`, `library/core/src/mem/mod.rs:74-100` (blob `42c7224fb41a2b13db3977b747d3d4a2de15df7e`) | `std::mem::forget` takes ownership of its argument and returns without running its destructor or freeing resources owned by that value. |
| Single-execution and double-panic abort | `library/core/src/ops/drop.rs:209-234`, `src/panic.md:103-116` (blob `d6b7c54784d1cb9398df04d218704be02a29d23d`) | Explicit user calls to `Drop::drop` are forbidden. If `Drop::drop` panics during destruction, the destructor is considered to have run and is **not** invoked a second time during the resulting unwind. If a second panic occurs while already unwinding (such as a field destructor panicking on a cleanup path), the runtime aborts (`terminate(cleanup)`). |
| Unwind vs. abort and ABI boundaries | `src/panic.md:103-116`, `src/items/functions.md:238-261` (blob `aa1eb712c9f10fd0a3df06c8e0f1055cf85d79b2`), `src/destructors.md:636-643` | Under `-C panic=unwind`, panicking unwinds the stack and runs destructors for live objects in each frame across unwinding-compatible ABI boundaries; under `-C panic=abort` or across non-unwinding FFI boundaries, stack cleanup is skipped or aborts immediately. |

### 2. Configured `rustc` `Runtime(PostCleanup)` MIR Lowering and Execution (`cleanup.rs`)

`Basis: execution | source`

To observe how `rustc` lowers these obligations into concrete MIR, `support/cleanup.rs` (3,075 bytes, SHA-256 `982e1015fc53150698b1947f79dcb12ad83fa4c3b2dd7069f7dd1b66e0545340`) defines a `Leaf` type with a `Drop` implementation that mutates its own payload (`self.payload = self.payload.wrapping_add(1)`), records `DropEnter(self.id, self.payload)`, optionally panics (`if self.panic_on_drop { panic!(...) }`), and otherwise records `DropExit(self.id, self.payload)`. It embeds two `Leaf` values in `struct Pair { first: Leaf, second: Leaf }` (which does not implement `Drop`) inside:

```rust
fn exercise(second_panics: bool, forget_second: bool, first_drop_panics: bool) {
    let pair = Pair {
        first: make(1, false, first_drop_panics),
        second: make(2, second_panics, false),
    };
    if forget_second {
        let second = pair.second;
        record(Event::Forgotten(second.id));
        std::mem::forget(second);
    }
    record(Event::AfterScope);
}
```

Compiling `cleanup.rs` with `--crate-name cleanup_binding --edition=2024 -C opt-level=0 -C panic=unwind -C codegen-units=1 --emit=mir,link` under both pinned `rustc 1.99.0` (`support/cleanup_binding.mir`, 57,370 bytes, SHA-256 `b5fd9b2f30575cfea1c5ecbe73aa2c9e6d8cef284d0d85675547caee1d025237`) and `rustc 1.99.1` (`support/cleanup_binding.1.99.1.mir`, 57,370 bytes, SHA-256 `f156c47a7f7f1c933861a4d445e135beb72cb0b855d5cac9adb7a0b6e8943b53`) yields byte-for-byte identical MIR across `exercise` (lines 811–918), `<Leaf as Drop>::drop` (lines 690–743), and `make` (lines 745–809), differing only in the 40-hex-character sysroot commit hash inside `EVENTS::{constant#0}` (lines 531–601).

#### 2.1 Basic-Block Anatomy of `exercise` (`cleanup_binding.mir:811-918`)

In `exercise`, `_4: Pair` is the aggregate local, `_5: Leaf` is the temporary holding the result of the first `make` call, `_6: Leaf` is the temporary holding the result of the second `make` call, `_11: Leaf` is the local `second` in the `if forget_second` branch, and `_16: bool` is the compiler-synthesized stack drop flag tracking whether `(_4.1: Leaf)` remains initialized:

1. **Drop-flag initialization and first field construction (`bb0`):**
   - `bb0` initializes `_16 = const false` and calls `_5 = make(const 1_u8, const false, copy _3) -> [return: bb1, unwind continue]`. If `make(1, ...)` unwinds, nothing in `exercise` requires cleanup yet (`unwind continue`).
2. **Second field construction and pre-aggregate unwind (`bb1`, `bb9`, `bb10`):**
   - `bb1` calls `_6 = make(const 2_u8, copy _1, const false) -> [return: bb2, unwind: bb9]`.
   - At `bb1`, `_4` has not yet been constructed; only temporary `_5` is live. If `make(2, ...)` panics (`second_constructor_panics`), control transfers to `bb9 (cleanup)`, which executes `drop(_5) -> [return: bb10, unwind terminate(cleanup)]`, followed by `bb10 (cleanup): resume`.
3. **Aggregate construction (`bb2`):**
   - `bb2` sets `_16 = const true` and initializes `_4 = Pair { first: move _5, second: move _6 }`, then branches on `copy _2` (`forget_second`): `[0: bb5, otherwise: bb3]`.
4. **Partial move and `std::mem::forget` (`bb3`, `bb4`, `bb18`):**
   - `bb3` reads `_9 = copy ((_4.1: Leaf).0: u8)` and calls `_7 = record(Forgotten(move _9)) -> [return: bb4, unwind: bb17]`. Note that `_16` is still `true` during `record(Forgotten(...))` at `bb3`, so an unwind from `record` would still drop both `_4.0` and `_4.1` via `bb17`.
   - `bb4` sets `_16 = const false`, moves `_11 = move (_4.1: Leaf)`, and calls `_10 = std::mem::forget::<Leaf>(move _11) -> [return: bb18, unwind: bb17]`. Because `_16` was cleared before `forget`, `_4.1` will not be dropped on subsequent normal or cleanup paths.
5. **Pre-drop scope body (`bb5`, `bb17`, `bb15`, `bb16`):**
   - `bb5` calls `_12 = record(const Event::AfterScope) -> [return: bb6, unwind: bb17]`.
   - Any unwind from `bb3`, `bb4`, or `bb5` lands at `bb17 (cleanup)`, which runs `drop((_4.0: Leaf)) -> [return: bb15, unwind terminate(cleanup)]`. `bb15 (cleanup)` switches on `copy _16 -> [0: bb10, otherwise: bb16]`, where `bb16 (cleanup)` runs `drop((_4.1: Leaf)) -> [return: bb10, unwind terminate(cleanup)]`.
6. **Normal scope-exit drop sequence (`bb6`, `bb13`, `bb14`, `bb7`):**
   - `bb6` drops the first field in declaration order: `drop((_4.0: Leaf)) -> [return: bb13, unwind: bb11]`. No drop flag is allocated for `_4.0` because its consumption is represented purely by CFG progression past `bb6`.
   - On normal return (`bb13`), `switchInt(copy _16) -> [0: bb7, otherwise: bb14]` skips `_4.1` if `forget_second` cleared `_16`, and otherwise runs `bb14: drop((_4.1: Leaf)) -> [return: bb7, unwind continue]`. `bb7` resets `_16 = const false` and returns.
7. **First-destructor panic and remaining-field cleanup (`bb6 -> bb11 -> bb12 -> bb10`):**
   - If `drop((_4.0: Leaf))` panics at `bb6`, control jumps to `bb11 (cleanup): switchInt(copy _16) -> [0: bb10, otherwise: bb12]`.
   - `_4.0` is **never retried**. If `_16` is `true`, `bb12 (cleanup)` drops the remaining initialized sibling field `_4.1`: `drop((_4.1: Leaf)) -> [return: bb10, unwind terminate(cleanup)]`. If `_4.1`'s destructor were also to panic during this cleanup, `unwind terminate(cleanup)` aborts execution immediately.

#### 2.2 Destructor Payload Mutation in `<Leaf as Drop>::drop` (`cleanup_binding.mir:690-743`)

In `<Leaf as Drop>::drop(_1: &mut Leaf)`:

- `bb0` reads `_5 = copy ((*_1).1: u8)` and computes `_6 = move _5.wrapping_add(const 1_u8) -> [return: bb1, unwind continue]`.
- `bb1` writes `((*_1).1: u8) = move _6`, reads `_3 = copy ((*_1).0: u8)` and `_4 = copy ((*_1).1: u8)`, and calls `record(DropEnter(move _3, move _4)) -> [return: bb2, unwind continue]`.
- `bb2` tests `_7 = copy ((*_1).2: bool)` (`panic_on_drop`): `[0: bb3, otherwise: bb4]`. `bb4` calls `rt::begin_panic(const "first destructor panic") -> unwind continue`, whereas `bb3` increments `((*_1).1: u8)` a second time and records `DropExit`.

Executing the compiled binary (`support/cleanup-binding-results.json`, `run.stdout` SHA-256 `0a4ea49e1dc777a4a5b761ed26ea46504a122fabc7ddb2acc2769b33bb085ac5`) confirms all four runtime traces:

| Case | `(second_panics, forget_second, first_drop_panics)` | `catch_unwind` Returned | Recorded Event Trace |
| --- | --- | --- | --- |
| `normal` | `(false, false, false)` | `true` | `[ConstructStart(1), Constructed(1), ConstructStart(2), Constructed(2), AfterScope, DropEnter(1, 21), DropExit(1, 22), DropEnter(2, 41), DropExit(2, 42)]` (note: in `cleanup.rs`, `AfterScope` is recorded before the closing brace of `exercise`, or after an inner block) |
| `second_constructor_panics` | `(true, false, false)` | `false` | `[ConstructStart(1), Constructed(1), ConstructStart(2), DropEnter(1, 21), DropExit(1, 22)]` |
| `forget_second` | `(false, true, false)` | `true` | `[ConstructStart(1), Constructed(1), ConstructStart(2), Constructed(2), Forgotten(2), DropEnter(1, 21), DropExit(1, 22), AfterScope]` |
| `first_destructor_panics` | `(false, false, true)` | `false` | `[ConstructStart(1), Constructed(1), ConstructStart(2), Constructed(2), DropEnter(1, 21), DropEnter(2, 41), DropExit(2, 42)]` |

(Note: In `cleanup.rs:54-65`, `pair` is bound inside an inner block `{ let pair = ...; if forget_second { ... } }` before `record(Event::AfterScope)` at line 66, so on non-panicking paths `DropEnter`/`DropExit` precede `AfterScope`.)

### 3. MiniRust Syntax, `Deinit`/`StorageDead` Statements, `ResumeUnwind` Frame-Cleanup Ordering, and `minimize` Lowering

`Basis: source`

Auditing MiniRust at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed` establishes how `rustc`'s elaborated cleanup MIR relates to MiniRust's operational primitives:

1. **Absence of implicit drop glue (`spec/lang/syntax.md:285-384, 502-514`):** MiniRust `Terminator` has `Goto`, `Switch`, `Unreachable`, `Intrinsic`, `Call { callee, calling_conv, args, ret, next_block, unwind_block }`, `Return`, `StartUnwind { unwind_payload, unwind_block }`, `StopUnwind(next_block)`, and `ResumeUnwind`. Basic blocks carry `BbKind` (`Regular`, `Cleanup`, `Catch`, `Terminate`), checked statically by well-formedness rules (`spec/lang/well-formed.md:240-264`). MiniRust has no `Drop` terminator and never synthesizes destructor calls automatically.
2. **`Deinit` and `StorageDead` vs. destructor obligations (`spec/lang/step/statements.md:134-185`):**
   - `Statement::Deinit(place)` (`statements.md:134-155`) writes `List::from_elem(Uninit, size)` into the target memory range. Because `<Leaf as Drop>::drop` reads and mutates the fields of `*self` (`((*_1).1: u8)`) after destructor entry, clearing a drop obligation before invoking `Drop::drop` cannot be represented as `Deinit(place)`.
   - `Statement::StorageLive(local)` and `Statement::StorageDead(local)` (`statements.md:160-185`) allocate and deallocate backing stack allocations in `self.mem` (`self.mem.allocate` / `self.mem.deallocate`) and update `frame.locals` without running any user code.
3. **Exact `Return` and `ResumeUnwind` phase ordering (`spec/lang/step/terminators.md:323-373, 424-454`, `spec/lang/machine.md:267-301`):**
   - Both `Return` (`terminators.md:323-373`) and `ResumeUnwind` (`terminators.md:424-454`) pop the callee stack frame **first** via `let mut frame = self.active_thread_mut().stack.pop().unwrap()` (`machine.md:267-269`), before performing fallible local deallocation and `end_call`.
   - Specifically, `ResumeUnwind` executes four ordered sub-steps:
     1. **Pop frame:** Removes the top `StackFrame` from `active_thread_mut().stack`, exposing `frame.locals` and `frame.extra` while the caller frame (if any) becomes `cur_frame_mut()`.
     2. **Deallocate live locals:** Loops `while let Some(local) = frame.locals.keys().next() { frame.storage_dead(&mut self.mem, local)?; }`, calling `self.mem.deallocate(ptr, size, align, AllocationKind::Stack)` (`statements.md:174-185`) for every remaining live local in the popped callee frame.
     3. **End call (`self.mem.end_call(frame.extra)?`):** Passes the **popped callee frame's** `frame.extra` to the memory model. In Tree Borrows (`spec/mem/tree_borrows/memory.md:259-262, 153-174`), `end_call` iterates `for (id, tag) in extra.protectors` in list order, looks up `alloc.extra.borrow_tree()`, and calls `release_protector(tag)`. For strong protectors, `release_protector` performs an implicit read access across all locations in the allocation (`tree_borrows/tree.md:258-291`) and removes `tag` from `extra.protectors` before advancing to the next list element. If element $k$ fails with UB (e.g., a `Frozen` or `Disabled` violation on a strongly protected tag), `end_call` short-circuits via `?` after allocations $0 \dots k-1$ have already been mutated and after all callee stack locals have already been deallocated.
     4. **Transfer control:** Matches `self.active_thread().stack.last()`: if `None` (`BottomOfStack`), raises `throw_ub!("unwind reached the bottom of the stack")`; if `Some(caller)`, matches `caller.unwind_block`: if `Some(block)`, calls `self.cur_frame_mut().jump_to_block(block)` (`machine.md:298-301`, setting `next_block = block` and `next_stmt = 0`); if `None`, raises `throw_ub!("unwinding from a function where the caller did not specify an unwind_block")`. `ResumeUnwind` leaves `thread.unwind_payloads` untouched (`StopUnwind` pops the payload at `terminators.md:402-422`).
4. **`tooling/minimize` lowering gap (`tooling/minimize/src/bb.rs:220-274`):**
   - In `tooling/minimize/src/bb.rs` (blob `45f794ea44bab2524861136279d282f8df7074b8`, lines 220–264), `rs::TerminatorKind::Drop { place, target, .. }` ignores the MIR `unwind` field, resolves `Instance::resolve_drop_in_place(place_ty, &self.tcx)`, and emits `Terminator::Call` with `next_block: Some(self.bb_name_map[&target])` and **`unwind_block: None`**.
   - At lines 267–274, `rs::TerminatorKind::UnwindTerminate(_)` is rejected at translation time with `span_bug!(terminator.source_info.span, "terminator not supported: {terminator:?}")`.
   - Consequently, `minimize`-translated MIR drops cannot execute caller cleanup blocks (`bb11`/`bb12`) when a destructor unwinds; instead, `ResumeUnwind` inside the unwinding destructor encounters `caller.unwind_block == None` and raises UB.

### 4. Machine-Checked Operational Models in Lean 4.34.1

`Basis: execution | derived`

Seven Lean 4.34.1 modules in `support/` (verified in `support/lean-check-results.json` with 0 errors, 0 warnings, and no `sorryAx`) formalize the operational semantics and negative controls for drop elaboration, effectful destructors, and `ResumeUnwind`:

| Lean Module (`support/`) | Source SHA-256 | Audits (Axiom-Free) | Key Checked Theorems and Controls |
| --- | --- | ---: | --- |
| `Combined.lean` | `34ce39266b559a757ea76cc1af4c7b07842d0eb47830414b9411e86b59e5dbb0` | 10 (1) | Couples byte-copy jobs with post-copy frame cleanup (`copy_then_cleanup_verified`). Proves that a cleanup failure followed by an infinite `.spin` loop is still rejected as unsafe (`cleanup_failure_then_spin`, `reachable_cleanup_failure_unsafe`, `Examples.copy_then_failed_cleanup_then_spin`) and that a sibling write after an aliased read faults (`Examples.alias_read_then_sibling_write_faults`). |
| `CleanupElaboration.lean` | `6411696e58060c29e47508f3ee9e35e1780b467169b617e949a3117224cc2503` | 11 (9) | Proves lockstep forward simulation (`simulation`), safety transfer (`safety_transfer`), and finite-prefix event-trace preservation (`finite_prefix_trace`) between a high-level obligation-list machine (`HighStep`) and a low-level CFG interpreter (`LowStep`) with explicit `test`, `clear`, `call (normal, unwind)`, and `abort` instructions. Verifies `clear_before_call_keeps_payload` and all five concrete specimens: `ordinary_cleanup_order`, `second_constructor_unwind_cleans_only_first`, `partial_move_skips_second`, `panicking_drop_is_not_retried`, and `destructor_bad_prefix_before_later_loop` / `destructor_spin_safe` / `destructor_spin_infinite`. |
| `EffectfulDestructor.lean` | `53b28ac7efe67bb729dd12a2eefd3e95f90bb3ce5359a9741b966c3392601afa` | 11 (3) | Replaces abstract destructor labels with a 4-step destructor engine (`readU8`, modulo-256 increment, `writeRaw`, `returned`/`unwound`) over `MemoryPermissions.runCoupled`. Proves `effectful_call`, `completed_engineCost`, `failure_keeps_residual`, and concrete pair persistence (`Concrete.first_write_still_present_at_second_entry`, `Concrete.both_payloads_updated`). |
| `TwoCleanup.lean` | `bf2ffe8e1b873c69603538229bcc06de5d1713e7a96d1f4d91666632e544a947` | 23 (2) | Proves simulation (`simulation`), safety transfer (`safety_transfer`), determinism (`low_step_deterministic`), and concrete pair safety (`Concrete.second_entry_preserves_first_write`, `Concrete.pair_low_safe`, `Concrete.pair_high_safe`, `Concrete.suppressed_second_low_safe`) between a high-level `Todo` controller (`both`, `secondOnly`, `done`) and a low-level CFG controller that stores only `secondOwed : Bool` (`_16`) while encoding first-field consumption via PC progression (`dropFirst -> afterFirst`). Proves two negative mutants: `Negative.rollback_changes_second_entry` (rolling back memory on destructor unwind changes the sibling destructor's read from `21` to `20`) and `Negative.retry_duplicates_entry_event` (retrying a panicking destructor duplicates `dropEnter .first 20`). |
| `EffectfulControls.lean` | `7f7009604a076aaf263e8acceb1484471e1f84a6005592bb4af5875198a248bb` | 42 (0) | Proves `MemoryWF` preservation across every engine and controller transition (`Admission.engine_step_preserves_MemoryWF`, `ControllerAdmission.high_reachable_MemoryWF`, `ControllerAdmission.low_reachable_MemoryWF`), including UB residuals (`localWriteFrozen`). Proves that permission UB at engine step 3 halts before the configured step-4 unwind decision (`BeforeUnwind.read_preserved_and_write_fails_before_exit_choice`, `ControllerUB.high_not_safe`, `ControllerUB.low_not_safe`, `ControllerUB.low_bad_terminal`), plus `RestartControls.rollback_changes_actual_read` and `RestartControls.retry_invocation_updates_again`. |
| `ResumeUnwindPhase.lean` | `0b021df3fea1d474cf4a0138ca512351d53acfed701fb37c148eef432b091c1c` | 19 (0) | Formalizes a two-frame (`caller`, `callee`), one-local `ResumeUnwind` phase runner on `TreeMemory` (`runR`) and per-allocation `TreeFactoredMemory` (`runF`). Proves `source_adapter_pop`, `runR_equation`, `runR_success_iff`, exact reification agreement under `WellSized` (`run_agrees`), and `WellSized` preservation across all outcomes (`runF_preserves`). |
| `ResumeUnwindPhaseControls.lean` | `584e1e7884b59364720aba6cd722418d6a1189edafcb878814bf8be6582611a6` | 25 (3) | Concrete 4-allocation controls (heap/protector allocations 0, 1, 2 at bases 16, 32, 48 and stack local allocation 3 at base 64) proving `actual_positive`, `actual_missing_continuation`, `actual_partial_failure` (stack local 3 is freed and allocation 0's strong protector is released before allocation 1 fails with `unprotectedLocalWriteFrozen`, leaving allocation 2 untouched and caller PC at `(5, 7)`), `wrong_list_value_discriminator` (`callerExtra` and `recordedExtra` succeed with identical PC, stack depth, and ghost log but fail to release allocation 0's strong protector), `late_pop_config_differs` (`latePop` leaves 2 frames on stack on partial failure), `rollback_memory_differs` (`rollbackWholePhaseOnError` leaves stack local 3 live), and factored equivalents (`actual_factored_positive`, `actual_factored_failure`). |

## Boundaries

- **`not examined`:**
  - General compiler correctness of `rustc`'s full drop elaboration pass (`rustc_mir_transform::elaborate_drops`) across arbitrary loops, generator/coroutine state machines, async functions, or inline assembly.
  - Boxed slice or dynamically sized type (`?Sized`) vtable drop-glue generation in `rustc` and `minimize`.
  - Unwind tables (DWARF/SEH), platform ABI personality routines (`rust_eh_personality`), or `catch_unwind` runtime payload allocation.
- **`unknown`:**
  - Whether upstream MiniRust will add a dedicated `Terminator::Terminate` or extend `tooling/minimize` to lower MIR `Drop` unwind edges (`unwind: bb_cleanup`) and `UnwindTerminate` (`terminate(cleanup)`) instead of emitting `unwind_block: None` and `span_bug!`.
- **`known not to apply`:**
  - Clearing a drop obligation before destructor entry does **not** correspond to `MiniRust::Statement::Deinit`: `Deinit` overwrites the place's bytes with `Uninit`, which invalidates legitimate field reads inside `<T as Drop>::drop(&mut self)`.
  - Scope-exit reverse declaration order does **not** apply to struct or tuple fields: aggregate fields are dropped in forward declaration order (`_4.0` before `_4.1`).
  - Whole-phase rollback on `ResumeUnwind` failure does **not** match MiniRust's operational semantics: `ResumeUnwind` pops the frame, deallocates stack locals, and mutates borrow trees incrementally before `?` propagates an `end_call` UB error.
- **`unsupported`:**
  - In `tooling/minimize` at commit `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`, `rs::TerminatorKind::UnwindTerminate(_)` is explicitly unsupported (`span_bug!`), and `rs::TerminatorKind::Drop` drops its `unwind` target (`unwind_block: None`).

## Evidence

All primary evidence artifacts are archived in `support/`:

| File | Bytes | SHA-256 | Role |
| --- | ---: | --- | --- |
| `support/cleanup.rs` | 3,075 | `982e1015fc53150698b1947f79dcb12ad83fa4c3b2dd7069f7dd1b66e0545340` | Executable Rust specimen exercising normal drop order, constructor panic, partial move + `forget`, and panicking first-field destructor. |
| `support/cleanup_binding.mir` | 57,370 | `b5fd9b2f30575cfea1c5ecbe73aa2c9e6d8cef284d0d85675547caee1d025237` | Baseline `Runtime(PostCleanup)` MIR emitted by `rustc 1.99.0` (`b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`). |
| `support/cleanup_binding.1.99.1.mir` | 57,370 | `f156c47a7f7f1c933861a4d445e135beb72cb0b855d5cac9adb7a0b6e8943b53` | Revalidated `Runtime(PostCleanup)` MIR emitted by `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`). |
| `support/cleanup-binding-results.json` | 3,789 | `06f263790e79c6c5402f7efb7d15e97fc5bbb793e9cc0a8e4d2a72a495698e8b` | Original compilation and runtime trace manifest for `cleanup.rs`. |
| `support/Combined.lean` | 16,366 | `34ce39266b559a757ea76cc1af4c7b07842d0eb47830414b9411e86b59e5dbb0` | Lean 4.34.1 model of coupled copy-then-cleanup execution and bad-prefix-before-spin detection. |
| `support/CleanupElaboration.lean` | 19,950 | `6411696e58060c29e47508f3ee9e35e1780b467169b617e949a3117224cc2503` | Lean 4.34.1 model of high-to-low drop elaboration simulation and trace preservation. |
| `support/EffectfulDestructor.lean` | 12,490 | `53b28ac7efe67bb729dd12a2eefd3e95f90bb3ce5359a9741b966c3392601afa` | Lean 4.34.1 model of 4-step effectful destructors over permissioned memory. |
| `support/TwoCleanup.lean` | 33,944 | `bf2ffe8e1b873c69603538229bcc06de5d1713e7a96d1f4d91666632e544a947` | Lean 4.34.1 model of two-field cleanup controller simulation and rollback/retry negative controls. |
| `support/EffectfulControls.lean` | 25,286 | `7f7009604a076aaf263e8acceb1484471e1f84a6005592bb4af5875198a248bb` | Lean 4.34.1 model of `MemoryWF` preservation and mid-destructor permission UB before unwind choice. |
| `support/ResumeUnwindPhase.lean` | 24,605 | `0b021df3fea1d474cf4a0138ca512351d53acfed701fb37c148eef432b091c1c` | Lean 4.34.1 model of two-frame `ResumeUnwind` phase over monolithic and factored Tree Borrows memory. |
| `support/ResumeUnwindPhaseControls.lean` | 29,034 | `584e1e7884b59364720aba6cd722418d6a1189edafcb878814bf8be6582611a6` | Lean 4.34.1 concrete 4-allocation controls and partial-failure / wrong-list / late-pop / rollback discriminators. |
| `support/lean-check-results.json` | 245,875 | `bd2f89988327f6fb67205f45c74ed9f9f7d3bf54f604aabdeaccc28164a2d47d` | Revalidation ledger for all 7 target Lean modules and their transitive dependencies under Lean 4.34.1. |

## Revalidation

To revalidate the `rustc` MIR emission and runtime traces:

```bash
rustc +1.99.1 support/cleanup.rs \
  --crate-name cleanup_binding \
  --edition=2024 \
  -C opt-level=0 \
  -C panic=unwind \
  -C codegen-units=1 \
  --emit=mir,link \
  -o /tmp/cleanup_binding
/tmp/cleanup_binding
```

Expected runtime output (`SHA-256: 0a4ea49e1dc777a4a5b761ed26ea46504a122fabc7ddb2acc2769b33bb085ac5`):

```text
normal: returned=true events=[ConstructStart(1), Constructed(1), ConstructStart(2), Constructed(2), DropEnter(1, 21), DropExit(1, 22), DropEnter(2, 41), DropExit(2, 42), AfterScope]
second_constructor_panics: returned=false events=[ConstructStart(1), Constructed(1), ConstructStart(2), DropEnter(1, 21), DropExit(1, 22)]
forget_second: returned=true events=[ConstructStart(1), Constructed(1), ConstructStart(2), Constructed(2), Forgotten(2), DropEnter(1, 21), DropExit(1, 22), AfterScope]
first_destructor_panics: returned=false events=[ConstructStart(1), Constructed(1), ConstructStart(2), Constructed(2), DropEnter(1, 21), DropEnter(2, 41), DropExit(2, 42)]
```

To revalidate the seven Lean 4.34.1 modules (using the topological dependency order recorded in `support/lean-check-results.json`):

```bash
# With AnnealResearch base dependencies compiled on LEAN_PATH:
for mod in Combined CleanupElaboration EffectfulDestructor TwoCleanup EffectfulControls ResumeUnwindPhase ResumeUnwindPhaseControls; do
  lean -j1 -M2048 -o "/tmp/build/AnnealResearch/${mod}.olean" "support/${mod}.lean"
done
```
