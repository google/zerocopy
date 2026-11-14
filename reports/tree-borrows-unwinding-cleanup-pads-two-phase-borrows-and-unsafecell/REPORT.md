# Tree Borrows Protectors Under `panic=unwind` `cleanup` Landing Pads, `dead_on_unwind` (`sret`), Two-Phase Borrows, and `UnsafeCell` Interior Mutability

## Summary

In `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), Tree Borrows
function-entry protectors (`ProtectorKind::StrongProtector` for references,
`ProtectorKind::WeakProtector` for `Box<T>`) interact with `panic=unwind`
`cleanup` landing pads, indirect return slots (`sret`), two-phase borrows
(`RetagKind::TwoPhase`), and sub-object `UnsafeCell<T>` fields through four
exact invariants established by source inspection, a 56-entry transition matrix
([`support/tree_borrows_transition_matrix.json`](support/tree_borrows_transition_matrix.json)),
a 24-test Miri (`0.1.0`, `3ef0c22cdb`) unwind and interior-mutability suite
([`support/miri_unwind_unsafecell_24_results.json`](support/miri_unwind_unsafecell_24_results.json)),
and a zero-axiom Lean `v4.34.1` mechanization
([`support/TreeBorrowsUnwindAndUnsafeCellProbe.lean`](support/TreeBorrowsUnwindAndUnsafeCellProbe.lean)):

1. **Identical Two-Stage Protector Release on Normal `Return` and Exceptional
   `UnwindResume` (`machine.rs:1952-1977`, `stack.rs:431-472`):**
   - Both `TerminatorKind::Return` (`unwinding = false`) and
     `TerminatorKind::UnwindResume` (`unwinding = true`) exit the current stack
     frame by calling `InterpCx::pop_stack_frame_raw` ->
     `MiriMachine::before_stack_pop` -> `EvalContextExt::on_stack_pop`
     (`borrow_tracker/mod.rs:362-400`) *before* `cleanup_stack_frame`
     deallocates callee stack locals.
   - Consequently, a function-entry protector on `x: &mut T` remains active
     throughout all callee `BasicBlockData { is_cleanup: true, .. }` landing-pad
     blocks (allowing callee drop guards to read, write, and reborrow `*x` on
     the unwind path, verified in `U03`, `U15`, and `U21`), and is **cleanly
     retired** when `UnwindResume` pops the callee frame—emitting the
     `AccessCause::FnExit` implicit read/write (`perform_protector_end_access`)
     with `SkipChildrenOfAccessed` and removing `x`'s tag from
     `global.protected_tags`.
   - After `f(x: &mut T)` unwinds, the caller is fully permitted to read,
     mutate, or run `Drop::drop` on the referent of `x` inside a caller
     `cleanup` landing pad or after `std::panic::catch_unwind` (`U01`, `U02`,
     `U04`, `U14`).
2. **Unsoundness of Uncompensated Store Motion / `DSE` on `&mut T` Across
   `may_unwind` Calls vs. Soundness on `sret` (`dead_on_unwind`):**
   - Because the caller can observe `*x` after `f(x: &mut T)` unwinds, deleting
     or sinking a store `*x = v1` across a potentially unwinding call `g()` in
     `*x = v1; g(); *x = v2` **without** compensating on the `cleanup` edge is
     **unsound**: if `g()` unwinds, the caller observes the stale pre-store
     value `v0` instead of `v1` (`dseAcrossMayUnwindCall_unsound_counterexample`,
     [`support/TreeBorrowsUnwindAndUnsafeCellProbe.lean:199-202`](support/TreeBorrowsUnwindAndUnsafeCellProbe.lean#L199-L202)).
   - Store-sinking / `DSE` of `*x = v1` across `g()` in `MiniSSA` is sound if
     and only if at least one of three side conditions holds:
     1. `g()` is proven `nounwind` (`!fn_abi.can_unwind` or
        `UnwindAction::Unreachable`);
     2. `*x = v1` is sunk onto **both** the normal continuation edge and the
        `UnwindAction::Cleanup(bb_cleanup)` landing pad before `UnwindResume`
        (`compensatedStoreSinkingAcrossMayUnwind_refines`,
        [`support/TreeBorrowsUnwindAndUnsafeCellProbe.lean:207-211`](support/TreeBorrowsUnwindAndUnsafeCellProbe.lean#L207-L211)); or
     3. The destination is the function's indirect return slot `_0` (`sret`),
        which `rustc_codegen_llvm` marks `sret([N x i8]) writable dead_on_unwind
        noalias` (`compiler/rustc_codegen_llvm/src/abi.rs:495-512`) because the
        caller never reads or drops `*_0` when the callee unwinds
        (`sretDeadOnUnwindStoreSinking_refines`,
        [`support/TreeBorrowsUnwindAndUnsafeCellProbe.lean:226-229`](support/TreeBorrowsUnwindAndUnsafeCellProbe.lean#L226-L229),
        `U05`).
3. **Two-Phase Borrows (`RetagKind::TwoPhase`) vs. Protected `&mut T` and
   `&mut UnsafeCell<T>` (`perms.rs:147-217`, `mod.rs:164-207`):**
   - In `Runtime(PostCleanup)` MIR, `Retag([two-phase] _place)` uses
     `RetagMode::Default` (`is_protected = false`), initializing `&mut T` to
     `ReservedFrz { conflicted: false }` (when `T: Freeze`) or `ReservedIM`
     (when `T: !Freeze`). Under `is_protected = false`, a foreign/parent read
     leaves `ReservedFrz { conflicted: false }` unchanged (`perms.rs:162-170`),
     allowing subsequent child writes to activate the tag to `Unique`
     (`twoPhaseUnprotected_allows_parentRead_then_childWrite`, `U06`, `U07`,
     `U08`, `U23`).
   - By contrast, a function-entry `&mut T` (`RetagMode::FnEntry`,
     `is_protected = true`) is **always** initialized to `ReservedFrz {
     conflicted: false }` **even when `T` contains `UnsafeCell`**
     (`tree_borrows/mod.rs:185-188`: `else if is_protected || frozen {
     Permission::new_reserved_frz() }`, so `ReservedIM` never exists under a
     protector, `perms.rs:117`). A foreign read during the call sets
     `ReservedFrz { conflicted: true }` (`perms.rs:161`), which permits child
     reads (`U20`) but **forbids** child writes (`perms.rs:193`,
     `protectedReservedFrz_forbids_foreignRead_then_childWrite`).
4. **Byte-Precise `Freeze` vs. `UnsafeCell` Partitioning (`precise_interior_mut`)
   and `Freeze`-Field Load Hoisting (`freezeFieldLoadHoisting_refines`):**
   - For a shared reference `r: &StructWithCell`, `tb_reborrow`
     (`tree_borrows/mod.rs:329-363`) runs `visit_freeze_sensitive(place,
     ptr_size, ...)` to partition `inside_perms` at byte granularity:
     - Byte ranges outside `UnsafeCell` (`frozen == true`) receive
       `LocationState::new_accessed(Permission::new_frozen(), Read)`
       (`accessed = true`, `associated_access = Some(Read)`), actively protected
       by `StrongProtector` against any foreign or child write;
     - Byte ranges inside `UnsafeCell` (`frozen == false`) receive
       `LocationState::new_non_accessed(Permission::new_cell(), Write)`
       (`accessed = false`, `associated_access = None`), which ignores all child
       and foreign reads/writes (`perms.rs:143,152,189,209`), skips deallocation
       protector checks (`tree.rs:576`), and emits no implicit access on
       protector release (`perms.rs:314`).
   - Consequently, `MiniSSA`'s `GVN` and `LICM` passes can soundly hoist and
     common-subexpression-eliminate loads from the `Freeze` byte ranges of
     `&StructWithCell` across arbitrary unknown function calls that mutate
     sibling `UnsafeCell` fields (`freezeFieldLoadHoisting_refines`,
     [`support/TreeBorrowsUnwindAndUnsafeCellProbe.lean:303-307`](support/TreeBorrowsUnwindAndUnsafeCellProbe.lean#L303-L307),
     `U11`–`U13`, `U16`, `U17`, `U24`).

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), its bundled `LLVM 23.1.1` backend
(`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), Miri `0.1.0`
(`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), and `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`) when verifying or optimizing
functions with `panic=unwind` `cleanup` edges, `sret` return slots, two-phase
borrows, and `UnsafeCell` interior mutability in Anneal and `MiniSSA`.

It extends four corpus reports:
- `tree-borrows-two-stage-protector-release-and-reborrow-contracts`
- `rustc-drop-elaboration-unwind-landing-pads-and-extensible-mir-semantics`
- `unwinding-on-elf-and-macho-targets`
- `unwinding-on-windows-targets-and-32bit-seh`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. Complete Miri Tree Borrows State-Transition and Protector Matrix (`perms.rs` & `tree.rs`)

Basis: source + execution

In `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:10-332` and
`tree.rs:132-728` (`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`),
every byte offset of each `BorTag` in an allocation's `LocationTree` holds a
`LocationState { accessed: bool, permission: PermissionPriv,
idempotent_foreign_access }` (`tree.rs:37-57`). The complete 56-case transition
table extracted in
[`support/tree_borrows_transition_matrix.json`](support/tree_borrows_transition_matrix.json)
(for `accessed = true` locations, plus `associated_access` on protector release)
is:

| Initial `PermissionPriv` | `protected` (`FnEntry`) | `Child Read` | `Foreign Read` | `Child Write` | `Foreign Write` | `associated_access()` on `FnExit` / `UnwindResume` |
| :--- | :---: | :--- | :--- | :--- | :--- | :--- |
| `Cell` | `false` / `true` | `Cell` | `Cell` | `Cell` | `Cell` | `None` (no implicit access; never blocks `dealloc`) |
| `ReservedFrz(false)` | `false` | `ReservedFrz(false)` | `ReservedFrz(false)` | `Unique` | `Disabled` | `Some(Read)` |
| `ReservedFrz(false)` | `true` | `ReservedFrz(false)` | `ReservedFrz(true)` | `Unique` | **`UB(ProtectedDisabled)`** | `Some(Read)` |
| `ReservedFrz(true)` | `false` | `ReservedFrz(true)` | `ReservedFrz(true)` | `Unique` | `Disabled` | `Some(Read)` |
| `ReservedFrz(true)` | `true` | `ReservedFrz(true)` | `ReservedFrz(true)` | **`UB(ChildAccessForbidden)`** | **`UB(ProtectedDisabled)`** | `Some(Read)` |
| `ReservedIM` | `false` | `ReservedIM` | `ReservedIM` | `Unique` | `ReservedIM` | `Some(Read)` |
| `ReservedIM` | `true` | *Unreachable* (`NewPermission::new` uses `ReservedFrz` whenever `is_protected == true`, `mod.rs:185-188`) | *Unreachable* | *Unreachable* | *Unreachable* | *Unreachable* |
| `Unique` | `false` | `Unique` | `Frozen` | `Unique` | `Disabled` | `Some(Write)` |
| `Unique` | `true` | `Unique` | **`UB(ProtectedDisabled)`** | `Unique` | **`UB(ProtectedDisabled)`** | `Some(Write)` |
| `Frozen` | `false` | `Frozen` | `Frozen` | **`UB(ChildAccessForbidden)`** | `Disabled` | `Some(Read)` |
| `Frozen` | `true` | `Frozen` | `Frozen` | **`UB(ChildAccessForbidden)`** | **`UB(ProtectedDisabled)`** | `Some(Read)` |
| `Disabled` | `false` | **`UB(ChildAccessForbidden)`** | `Disabled` | **`UB(ChildAccessForbidden)`** | `Disabled` | `Some(Read)` (only if `accessed == true`, which is unreachable under `protected == true`) |

**Why `ReservedFrz(conflicted)` Exists Specifically for Protected Two-Phase /
Read-Only `&mut T`:**
1. When `protected == false` (`RetagKind::Default` or `RetagKind::TwoPhase`), a
   foreign read on `ReservedFrz(false)` leaves `conflicted = false` (`perms.rs:164-170`),
   so a subsequent child write transitions cleanly to `Unique`. Even if
   `conflicted` became `true` while protected, once the protector is released at
   frame exit (`protected` becomes `false`), a child write on
   `ReservedFrz(true)` is permitted again (`perms.rs:193-196`)!
2. When `protected == true` (`RetagKind::FnEntry`), a foreign read sets
   `conflicted = true` (`perms.rs:161`). While `protected == true`, child reads
   remain valid (`U20`), but any child write triggers `ChildAccessForbidden` UB
   (`perms.rs:193`), enforcing LLVM `noalias`: within a single function activation,
   a protected `&mut T` cannot both be written through `x` and read through a
   foreign alias.

### 2. Unwind Landing Pads (`UnwindAction::Cleanup`), `UnwindResume`, and `dead_on_unwind` (`sret`)

Basis: source + execution + derived

In `compiler/rustc_const_eval/src/interpret/stack.rs:431-472` and
`src/tools/miri/src/machine.rs:1952-2001`, stack frame termination executes in
three ordered steps regardless of whether the frame exited via
`TerminatorKind::Return` (`unwinding = false`) or `TerminatorKind::UnwindResume`
(`unwinding = true`):
1. `MiriMachine::before_stack_pop(ecx)` calls `ecx.on_stack_pop(frame)`
   (`borrow_tracker/mod.rs:362-400`), which iterates over
   `frame.extra.borrow_tracker.protected_tags`, runs
   `alloc_borrow_tracker.release_protector(...)` on every still-live allocation,
   and then removes the frame's tags from `global.protected_tags` via
   `end_call`.
2. `self.stack_mut().pop()` removes the frame from the call stack.
3. `cleanup_stack_frame(unwinding, frame)` deallocates all live stack locals of
   the popped frame (`self.deallocate_local(local.value)`) and invokes
   `MiriMachine::after_stack_pop(ecx, frame, unwinding)` ->
   `ecx.handle_stack_pop_unwind(frame.extra, unwinding)` to branch to the
   caller's `ReturnContinuation::Goto { ret, unwind }` target.

Contrast between reference parameters (`x: &mut T`), indirect by-value
arguments (`PassMode::Indirect`), and indirect return slots (`sret` / `_0`) in
`compiler/rustc_codegen_llvm/src/abi.rs:488-545`:

| ABI Parameter Class | `rustc_codegen_llvm` Attributes (`OptLevel != No`) | Caller Observation on Normal `Return` | Caller Observation on `UnwindResume` | Uncompensated `DSE` / Store Sinking Across `may_unwind` Call |
| :--- | :--- | :--- | :--- | :--- |
| `x: &mut T` (`T: Unpin`) | `noalias noundef align(A) dereferenceable(S) nofree writable` (`abi.rs:84-95`, `rustc_ty_utils/src/abi.rs:366-410`) | Caller may read/write/drop `*x` | **Caller may read/write/drop `*x`** (`catch_unwind` or caller `Drop` in `cleanup` pad, `U01`–`U04`) | **UNSOUND** (`dseAcrossMayUnwindCall_unsound_counterexample`); requires `nounwind` callee or `cleanup`-pad store compensation (`compensatedStoreSinkingAcrossMayUnwind_refines`) |
| `_0: Sret` (`PassMode::Indirect` on `fn_abi.ret`) | `sret([S x i8]) noalias noundef align(A) dereferenceable(S) nofree writable dead_on_unwind` (`abi.rs:495-512`) | Caller reads constructed return value `*_0` | **Never read or dropped by caller** (return slot remains uninitialized on unwind, `U05`) | **SOUND** (`sretDeadOnUnwindStoreSinking_refines`) |
| `arg: IndirectByVal` (`PassMode::Indirect { on_stack: false }` on `fn_abi.args`) | `noalias noundef align(A) dereferenceable(S) nofree captures(address) dead_on_return` (`abi.rs:536-544`, `callconv/mod.rs:409-427`) | Never read by caller after return (`dead_on_return`; callee drops `arg` before `Return`) | **Never read by caller on unwind** (callee `cleanup` pad drops `arg` before `UnwindResume`) | **SOUND** after callee drop / before `Return` |

### 3. Sub-Object `UnsafeCell` Projections (`&StructWithCell`) and 24-Test Miri Verification

Basis: source + execution

When a composite type `T` contains both `Freeze` fields and `UnsafeCell<U>`
fields (such as `StructWithCell { frozen_hdr: u64, counter: Cell<u64>,
frozen_tail: u64 }` in `U11`–`U13`), `rustc`'s `pointee_info_at` marks the
whole pointer `PointerKind::SharedRef { frozen: false }`, suppressing top-level
LLVM `noalias` and `readonly` on the pointer parameter (`rustc_ty_utils/src/abi.rs:367,400,412`).
However, inside the operational semantics (`tree_borrows/mod.rs:329-363`),
`visit_freeze_sensitive` assigns per-byte permissions:
- `[0..8)` (`frozen_hdr`): `Frozen`, `accessed = true`, `StrongProtector`;
- `[8..16)` (`counter: UnsafeCell<u64>`): `Cell`, `accessed = false`,
  `StrongProtector` (inert on `Cell`);
- `[16..24)` (`frozen_tail`): `Frozen`, `accessed = true`, `StrongProtector`.

Consequently, within `MiniSSA` (which has full `Runtime(PostCleanup)` MIR type
and field-projection information on `_1.0` vs. `_1.1`), loads from a `Freeze`
field projection `(*_1).frozen_hdr` of a function-entry shared reference
`_1: &StructWithCell` are invariant across any call during `_1`'s lifetime
(`freezeFieldLoadHoisting_refines`), enabling `GVN` and `LICM` on `Freeze`
headers/metadata of interior-mutable structs even though flat LLVM IR loses
whole-argument `readonly`.

Summary of the 24 Miri litmus tests in
[`support/run_tree_borrows_unwind_unsafecell_probe.py`](support/run_tree_borrows_unwind_unsafecell_probe.py)
([`support/miri_unwind_unsafecell_24_results.json`](support/miri_unwind_unsafecell_24_results.json)):

| Test IDs | Category | Description | Tree Borrows (`-Zmiri-tree-borrows`) | Stacked Borrows |
| :--- | :--- | :--- | :--- | :--- |
| `U01`–`U05` | Unwind protector release & `sret` | Callee writes `&mut u64` then panics; caller `catch_unwind` and `Drop` read `*x`; callee `cleanup` guard writes `*x` before `UnwindResume`; 3-frame nested unwind; `sret` `[u64; 8]` unwind (`dead_on_unwind`) | **`PASS (5 / 5)`** | `PASS (5 / 5)` |
| `U06`–`U08`, `U23` | Two-phase borrows (`RetagKind::TwoPhase`) | `vec.push(vec.len())`, shared reborrow during reservation, nested two-phase borrows, panic during argument evaluation aborting reservation | **`PASS (4 / 4)`** | `PASS (4 / 4)` |
| `U09`–`U10`, `U20` | `ReservedIM` vs. protected `ReservedFrz` | `U09`: unprotected `&mut UnsafeCell<u64>` (`ReservedIM`) survives foreign write; `U10`: protected `&mut UnsafeCell<u64>` (`ReservedFrz`); `U20`: protected `&mut u64` foreign read followed by panic without child write | **`PASS (3 / 3)`** | **`FAIL`** on `U09` and `U20` (SB pops `Unique` on foreign write/read) |
| `U11`–`U13`, `U16`–`U17`, `U24` | Sub-object `UnsafeCell` (`&StructWithCell`) | Reading `Freeze` fields before/after mutating sibling `Cell<u64>` fields, aliased `(&StructWithCell, &StructWithCell)`, unwind after mutating `Cell`, array of `Cell`s, enum with `Pure` vs `InteriorMut` variants | **`PASS (6 / 6)`** | `PASS (6 / 6)` |
| `U14`–`U15`, `U21`–`U22` | Sub-slice reborrows & `cleanup` guards | `split_at_mut` across panic, conditional return-reborrow vs unwind-drop guard, child reborrow inside `cleanup` `Drop`, ZST `&mut ()` / `&UnsafeCell<()>` unwind | **`PASS (4 / 4)`** | `PASS (4 / 4)` |
| `U18`–`U19` | `Box<T>` (`WeakProtector`) unwind | Explicit `drop(b)` before panic (`WeakProtector` allows deallocation during call) and implicit `cleanup`-pad drop of `Box<u64>` | **`PASS (2 / 2)`** | `PASS (2 / 2)` |

## Boundaries

1. **Enum Variants Mixing `Freeze` and `UnsafeCell` (`U17`, `EnumWithCell`):**
   - **Known not to apply without discriminant stability:** When an enum `&EnumWithCell`
     has one variant `Pure(u64)` (`Freeze`) and another variant
     `InteriorMut(Cell<u64>)` (`!Freeze`) overlapping at the same byte offsets,
     `visit_freeze_sensitive` inspects the **active runtime discriminant** at
     retag time (`tree_borrows/mod.rs:355`). `MiniSSA` can hoist loads from the
     `Pure` payload only within a branch dominated by a `SwitchInt` check on the
     enum discriminant (since the discriminant itself lies outside the
     `UnsafeCell` payload and is `Frozen`).
2. **`Box<T>` Deallocation Under `WeakProtector` vs. `&mut T` Under
   `StrongProtector` (`U18` vs. `tree.rs:572`):**
   - **Known not to apply to `Box<T>` after deallocation:** Unlike `&mut T`
     (`StrongProtector`, `nofree`), a `Box<T>` parameter carries
     `WeakProtector` (`mod.rs:218`) and may be deallocated inside the callee
     (`U18`). When `Box<T>` is deallocated before frame exit, `on_stack_pop`
     checks `matches!(kind, AllocKind::LiveData)` (`borrow_tracker/mod.rs:386`)
     and skips `release_protector` on the freed allocation; `MiniSSA` must never
     sink stores to a `Box<T>` past a call that may deallocate it.

## Evidence

1. **Lean `v4.34.1` Mechanization (`0` `sorryAx`, `0` `Lean.ofReduceBool`):**
   - File:
     [`support/TreeBorrowsUnwindAndUnsafeCellProbe.lean`](support/TreeBorrowsUnwindAndUnsafeCellProbe.lean)
   - Verified theorems: `twoPhaseUnprotected_allows_parentRead_then_childWrite`,
     `protectedReservedFrz_forbids_foreignRead_then_childWrite`,
     `dseAcrossMayUnwindCall_unsound_counterexample`,
     `compensatedStoreSinkingAcrossMayUnwind_refines`,
     `sretDeadOnUnwindStoreSinking_refines`, and
     `freezeFieldLoadHoisting_refines`.
2. **Miri Tree Borrows State-Transition Matrix and 24-Test Unwind + `UnsafeCell`
   Suite:**
   - Script:
     [`support/run_tree_borrows_unwind_unsafecell_probe.py`](support/run_tree_borrows_unwind_unsafecell_probe.py)
   - Transition matrix JSON:
     [`support/tree_borrows_transition_matrix.json`](support/tree_borrows_transition_matrix.json)
   - 24-test Miri results JSON:
     [`support/miri_unwind_unsafecell_24_results.json`](support/miri_unwind_unsafecell_24_results.json)
3. **`rustc 1.99.1` and Miri Source Coordinates (`58cf8f9c35b355199727627d07ae34a4e2846d67`):**
   - `src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:10-332`
     (`PermissionPriv`, `transition::perform_access`, `associated_access`)
   - `src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:109-364`
     (`NewPermission::new`, `tb_reborrow`, `visit_freeze_sensitive`)
   - `src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs:132-728`
     (`LocationState::perform_access`, `dealloc`, `perform_protector_end_access`)
   - `src/tools/miri/src/borrow_tracker/mod.rs:362-400` (`on_stack_pop`,
     `end_call`)
   - `compiler/rustc_codegen_llvm/src/abi.rs:488-545` (`StructRet`,
     `Writable`, `DeadOnUnwind`, `DeadOnReturn`)

## Revalidation

1. **Re-verify the Lean `v4.34.1` Mechanization:**
   ```bash
   anneal-lean-run --mode file --concurrency 4 -- \
     ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
     reports/tree-borrows-unwinding-cleanup-pads-two-phase-borrows-and-unsafecell/support/TreeBorrowsUnwindAndUnsafeCellProbe.lean
   ```
2. **Re-run the Transition Matrix Generator and 24-Test Miri Suite:**
   ```bash
   python3 reports/tree-borrows-unwinding-cleanup-pads-two-phase-borrows-and-unsafecell/support/run_tree_borrows_unwind_unsafecell_probe.py
   ```
