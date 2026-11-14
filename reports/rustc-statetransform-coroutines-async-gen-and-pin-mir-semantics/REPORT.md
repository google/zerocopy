# Formal Semantics and Empirical Anatomy of `StateTransform` Coroutines, `async`/`await`, `gen` Blocks, and `Pin<&mut Self>` at `Runtime(PostCleanup)` MIR

## Summary

In `rustc 1.99.1` (`rust-lang/rust` `58cf8f9c35b355199727627d07ae34a4e2846d67`),
`StateTransform` (`compiler/rustc_mir_transform/src/coroutine/mod.rs:1032-1226`,
`PassPolicy::Required`) is a mandatory phase-transition pass that runs at the
boundary from `Analysis(PostCleanup)` to `Runtime(Initial)`—before
`mir_drops_elaborated_and_const_checked` (`Runtime(PostCleanup)`). Consequently,
every `.anneal-mir` body captured at `Runtime(PostCleanup)` has already eliminated
`TerminatorKind::Yield` and `TerminatorKind::CoroutineDrop`, replacing each
`async fn`, `async {}`, `gen fn`, `gen {}`, `async gen`, and `#[coroutine]`
closure with a concrete state-machine `Coroutine::resume` / `Future::poll` /
`Iterator::next` body and an associated `InstanceKind::Shim(ShimKind::DropGlue)`
coroutine drop shim (`body.coroutine.coroutine_drop`). Source inspection, a
50-coroutine `Runtime(PostCleanup)` MIR census
([`support/coroutine_mir_census.json`](support/coroutine_mir_census.json)), and
a 20-test Miri self-referential coroutine litmus suite under both Tree Borrows
and Stacked Borrows
([`support/miri_litmus_results.json`](support/miri_litmus_results.json))
establish four governing invariants:

1. **Deterministic State-Machine Layout and Variant Dispatch (`0`, `1`, `2`,
   `3..3+K`):**
   - `locals_live_across_suspend_points` (`coroutine/layout.rs:82-183`) computes
     the bitset of `CoroutineSavedLocals` by intersecting `MaybeRequiresStorage`
     with `MaybeLiveLocals` (unioned with `MaybeBorrowedLocals` whenever the
     coroutine is immovable, `movable == false`, L120–133) at every `Yield`
     terminator. `compute_storage_conflicts` (`layout.rs:234-290`) constructs a
     symmetric `BitMatrix<CoroutineSavedLocal, CoroutineSavedLocal>` recording
     which saved locals can be simultaneously `StorageLive`, enabling non-conflicting
     saved locals from disjoint lexical scopes to share physical byte offsets
     inside the `CoroutineLayout` state union.
   - `CoroutineArgs` (`compiler/rustc_middle/src/ty/sty.rs:83-97`) reserves
     three fixed variant indices before suspension states:
     `UNRESUMED = 0` (`"Unresumed"`), `RETURNED = 1` (`"Returned"`), and
     `POISONED = 2` (`"Panicked"`, `RESERVED_VARIANTS = 3`). The $K$ suspension
     points receive variants `3 .. 3 + K - 1` (`"Suspend0"` .. `"Suspend{K-1}"`).
   - `insert_switch` (`coroutine/mod.rs:710-748`) replaces `START_BLOCK` (`bb0`)
     with a single `SwitchInt(Move(_discr))` dispatcher where `_discr =
     discriminant((*_1))` (or `discriminant((*_unpinned))` when pinned) and the
     otherwise target is `TerminatorKind::Unreachable` (`mod.rs:917-918`).
2. **Dual Aliasing Regimes for `Pin<&mut Self>` vs. `&mut Self` (`!Unpin`
   Exemption in LLVM `noalias` and Tree Borrows `NewPermission`):**
   - Static (`Movability::Static`) coroutines—including all `async fn`,
     `async {}`, `async gen`, and `#[coroutine] static` closures—do not implement
     the `Unpin` auto-trait unless explicitly overridden. Both
     `ty_and_layout_pointee_info_at` (`compiler/rustc_middle/src/ty/layout.rs:1066-1069`)
     and Miri's `NewPermission::new`
     (`src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:136-155`) check
     `pointee.is_unpin(tcx, typing_env) && pointee.is_unsafe_unpin(tcx, typing_env)`.
   - When `CoroutineState: !Unpin`, `rustc_ty_utils::abi::arg_attrs_for_rust_scalar`
     (`compiler/rustc_ty_utils/src/abi.rs:366-410`) suppresses `NoAlias`,
     `Writable`, and `NoFree` on the `Pin<&mut CoroutineState>` (`_1`) parameter,
     and Miri's Tree Borrows makes `Retag` (`[fn entry]` and `[default]`) a
     complete **no-op** (`return None` at `tree_borrows/mod.rs:151-155`).
   - Conversely, movable `gen fn` / `gen {}` blocks (`CoroutineDesugaring::Gen`)
     cannot hold borrows across `yield`, take `&mut CoroutineState` directly via
     `make_coroutine_state_argument_indirect` (`coroutine/mod.rs:555-565`),
     implement `Unpin` when their upvars and saved locals are `Unpin`, and
     receive full LLVM `noalias` + `nofree` + `writable` and Tree Borrows
     `StrongProtector` + `ReservedFrz` protection on `Iterator::next`.
3. **100% (`20 / 20`) Tree Borrows and Stacked Borrows Acceptance on Safe
   `StateTransform` Lowerings:**
   - Across all 20 self-referential and lifecycle litmus tests in
     [`support/run_miri_coroutine_litmus.py`](support/run_miri_coroutine_litmus.py)
     (`L01`–`L20`), including shared and mutable self-references across 1–3
     `.await` points, `split_at_mut` across `.await`, inner `Unpin` field
     borrows paired with sibling field mutation inside an outer `!Unpin` frame
     (`L05`), nested `poll` self-references (`L06`), `UnsafeCell` interior
     mutability (`L08`), partial drops at `Suspend0`/`Suspend1` (`L09`, `L10`),
     and mid-`await` panic unwinding (`L11`, `L20`), both Tree Borrows and
     Stacked Borrows report **zero Undefined Behavior (`20 / 20` pass)**.
   - By contrast, the negative control (`FORGED_UNPIN_UB_SOURCE`, manually
     implementing `Unpin` on a self-referential state struct) triggers immediate
     UB under both Tree Borrows (`read access through <525> at alloc222[0x0] is
     forbidden`) and Stacked Borrows (`tag does not exist in the borrow stack`),
     proving that the `!Unpin` retag/noalias suppression is both necessary and
     sufficient for self-referential coroutine soundness.
4. **Empirical Scale of `Runtime(PostCleanup)` Coroutine State Machines (`50`
   Coroutines):**
   - Across the 50-coroutine census (`c01`–`c50` in
     [`support/coroutine_mir_census.json`](support/coroutine_mir_census.json)),
     suspension-point counts span $K \in [0, 20]$ (median $2.0$, total $145$
     suspension points), post-`StateTransform` `resume`/`poll` bodies span
     `10` to `451` basic blocks (median `52.0` BBs, with `3` to `121` `cleanup`
     blocks), synthesized `coroutine_drop` shims span `2` to `89` basic blocks
     (median `20.0` BBs), and coroutine state sizes span `16 B` to `328 B`
     (median `64.0 B`), with `storage_conflicts` overlap packing compressing
     disjoint-scope saved locals by up to `2.46x` (`416 B` sum of variant
     payloads packed into a `168 B` coroutine frame in
     `c06_disjoint_scopes_storage_overlap`).

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), Miri `0.1.0`
(`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), the Ferrocene Language
Specification (`946eacae5a4a33a89af7832178504692439e7478`), and MiniRust
(`063d784186d3252bee242217f218223205c0b568`) when capturing, verifying, or
compiling `Runtime(PostCleanup)` MIR in Anneal and the verified `rustc` backend
(`MiniSSA` / `MiniMach`).

It extends four corpus reports:
- `rustc-mir-construct-semantics-miri-minirust-and-codegen`
- `rust-language-and-library-codegen-feature-inventory`
- `rustc-monomorphization-vtables-statics-symbols-and-cgu-partitioning`
- `rust-aliasing-models-stacked-tree-minirust-and-llvm-attributes`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. Exact Mechanics of `StateTransform` (`compiler/rustc_mir_transform/src/coroutine/`)

Basis: source + execution

`StateTransform::run_pass` (`compiler/rustc_mir_transform/src/coroutine/mod.rs:1034-1220`)
executes in ten ordered phases on every MIR body whose `body.yield_ty()` is
`Some(_)`:

1. **`get_context` Inlining for Async Desugarings (`mod.rs:664-704, 1095-1097`):**
   - HIR lowering of `.await` wraps the `&mut Context<'_>` task context in
     `std::future::ResumeTy(NonNull<Context<'static>>)` and calls the
     `LangItem::GetContext` intrinsic (`std::future::get_context`) before each
     inner `Future::poll` call so borrow checking does not see two live `&mut
     Context` references across suspension points (`#105501`).
   - Before liveness analysis runs, `eliminate_get_context_calls` replaces every
     `Call` to `get_context(_arg)` with a direct `CastKind::Transmute` of
     `(_arg.0: NonNull<Context>)` to `&mut Context<'_>` (`mod.rs:687-701`),
     preventing `ResumeTy` and `&mut Context<'_>` from appearing simultaneously
     live across a call terminator.
2. **Saved-Local Liveness and Storage Conflict Bitmatrix (`layout.rs:82-330`):**
   - `locals_live_across_suspend_points` runs four dataflow analyses over the
     pre-transform CFG:
     - `always_storage_live_locals(body)` (locals without any `StorageLive` /
       `StorageDead` statements, such as return place `_0` and arguments);
     - `MaybeStorageLive` (upper bound on storage lifetime);
     - `MaybeBorrowedLocals` (locals that have had a reference or raw pointer
       taken prior to a program point, including transitive projections);
     - `MaybeRequiresStorage` (locals that are `MaybeStorageLive` and either
       initialized or `MaybeBorrowedLocals`); and
     - `MaybeLiveLocals` (backward value liveness ignoring borrows).
   - At each `TerminatorKind::Yield` in `block` (`layout.rs:112-157`), the pass
     computes:
     $$\text{LiveAtYield}(b) = \begin{cases} (\text{MaybeLiveLocals}(b) \cup \text{MaybeBorrowedLocals}(b)) \cap \text{MaybeRequiresStorage}(b) \setminus \{\texttt{\_1}\} & \text{if } \neg\text{movable} \\ (\text{MaybeLiveLocals}(b) \cap \text{MaybeRequiresStorage}(b)) \setminus \{\texttt{\_1}\} & \text{if } \text{movable} \end{cases}$$
   - The union over all suspension points defines `saved_locals :
     CoroutineSavedLocals`.
   - `compute_storage_conflicts` (`layout.rs:234-290`) walks all reachable basic
     blocks not ending in `Unreachable` and marks two `CoroutineSavedLocal`s as
     conflicting iff both are simultaneously in `MaybeRequiresStorage` at any
     statement or terminator (plus marking any saved local in
     `always_live_locals` as conflicting with all saved locals, L247–280).
3. **Aliasing Validation (`EnsureCoroutineFieldAssignmentsNeverAlias`,
   `mod.rs:1104-1112, 1240-1324`):**
   - Before remapping locals to coroutine fields, `EnsureCoroutineFieldAssignmentsNeverAlias`
     verifies that in every assignment `lhs = rhs` (or `Call` destination write)
     where both `lhs` and a read operand in `rhs` map to `CoroutineSavedLocal`s
     $s_1 \ne s_2$, `storage_conflicts.contains(s_1, s_2)` is `true` so layout
     packing never overlaps the source and destination of a single MIR assignment.
4. **Place Remapping and `StorageLive`/`StorageDead` Rewriting
   (`TransformVisitor`, `mod.rs:403-543`):**
   - Every local `l` in `remap` is rewritten to a downcasted variant field
     projection on `_1`:
     `((_1 as variant#V).field#F: Ty)` (`make_field`, `mod.rs:351-358`).
   - All existing `StorageLive(l)` and `StorageDead(l)` statements for remapped
     locals `l` are erased to `StatementKind::Nop` (`mod.rs:463-468`), because
     their storage now resides permanently inside the coroutine struct `*_1`.
   - Special case for `PlaceElem::Index(idx_local)` (`mod.rs:430-450`): because
     MIR syntax requires the index inside `place[idx_local]` to be a bare `Local`
     rather than a projected place, if `idx_local` was remapped to a coroutine
     field, `process_projection_elem` leaves `idx_local` in `PlaceElem::Index`
     and injects `idx_local = Copy(((_1 as variant#V).field#F))` immediately
     before the indexing statement (`WithRetag::No`), Verified in census item
     `c10_array_index_across_yield` and Miri litmus test `L14`.
5. **Rewriting `Return` and `Yield` Terminators (`mod.rs:483-538`):**
   - A `TerminatorKind::Return` block is rewritten to:
     1. Construct the return wrapper (`Poll::Ready(_ret)`, `Option::None`,
        `AsyncGenFinished`, or `CoroutineState::Complete(_ret)`) into `_0`;
     2. Emit `SetDiscriminant { place: _1, variant_index: VariantIdx(1) }`
        (`CoroutineArgs::RETURNED = 1`);
     3. Terminate with `TerminatorKind::Return`.
   - The $k$-th `TerminatorKind::Yield { value, resume, resume_arg, drop }`
     ($k \in [0, K-1]$) is assigned state index $s_k = 3 + k$
     (`CoroutineArgs::RESERVED_VARIANTS + k`) and rewritten to:
     1. Construct the yield wrapper (`Poll::Pending`, `Option::Some(value)`,
        `value`, or `CoroutineState::Yielded(value)`) into `_0`;
     2. Emit `StorageDead(l)` for every non-remapped, non-always-live local `l`
        that was `StorageLive` at this yield block (`mod.rs:515-524`);
     3. Emit `SetDiscriminant { place: _1, variant_index: VariantIdx(3 + k) }`;
     4. Terminate with `TerminatorKind::Return` (recording `SuspensionPoint {
        state: 3 + k, resume, resume_arg, drop, storage_liveness }`).
6. **Saving Initial Parameters into `Unresumed` Entry (`mod.rs:1149-1163`):**
   - Original function parameters (`body.args_iter()`) that are live across any
     suspension point are moved into their remapped coroutine variant fields at
     the start of `START_BLOCK`:
     `((_1 as variant#V).field#F) = Move(_arg)` (`WithRetag::Yes`).
7. **Upvar Drop Ladder for `UNRESUMED` (`drop.rs:68-157`):**
   - `insert_clean_drop` and `elaborate_coroutine_drops` synthesize and
     drop-elaborate a `drop_clean` basic block that drops `Place::from(_1)`
     (which in the unresumed state drops only the captured upvars / initial
     arguments stored in the coroutine prefix).
8. **Cloning and Synthesizing the `coroutine_drop` Shim (`drop.rs:160-227`):**
   - `create_coroutine_drop_shim` clones the post-transform `body`, sets
     `arg_count = 1` and `_0: ()`, builds dispatch cases via
     `create_cases(body, transform, Operation::Drop)` mapping `(0, drop_clean)`
     and `(3 + k, drop_switch_bb_k)` (where `drop_switch_bb_k` emits
     `StorageLive(l)` for non-remapped storage-live locals and jumps to
     `point.drop`), and sets `default_block` to an immediate `Return` block
     (`drop.rs:184`).
   - Crucially, both `RETURNED` (`1`) and `POISONED` (`2`) are omitted from
     `cases` in `coroutine_drop`, so dropping a completed (`1`) or panicked (`2`)
     coroutine jumps directly to `default_block` (`Return`) without re-dropping
     any fields. Every `TerminatorKind::CoroutineDrop` along the per-suspend
     drop ladders is rewritten to `TerminatorKind::Return` (`drop.rs:187-192`),
     `make_coroutine_state_argument_indirect` rewrites `_1` to `&mut
     CoroutineState`, dead resume-only blocks are removed via
     `simplify::remove_dead_blocks`, and the shim is stored in
     `body.coroutine.coroutine_drop` with `InstanceKind::Shim(ShimKind::DropGlue(drop_glue, Some(coroutine_ty)))`.
9. **Unwind Poisoning and `create_coroutine_resume_function` (`mod.rs:826-949`):**
   - When `can_unwind(tcx, body)` is true (`panic=unwind` and at least one
     terminator has an unwind edge), `generate_poison_block_and_redirect_unwinds_there`
     (`mod.rs:826-864`) appends a cleanup `poison_block`:
     ```text
     bb_poison (cleanup): {
         discriminant((*_1)) = 2; // CoroutineArgs::POISONED
         resume;
     }
     ```
     and redirects every existing `TerminatorKind::UnwindResume` (after all local
     and saved-field cleanup drop ladders have finished!) and every non-cleanup
     `UnwindAction::Continue` edge to `poison_block`.
   - `create_cases(body, &transform, Operation::Resume)` (`mod.rs:976-1030`)
     builds a resume trampoline block for each suspension point $s_k = 3 + k$
     that re-establishes `StorageLive(l)` for non-remapped storage-live locals,
     moves the resume argument `_2` into `point.resume_arg` (`WithRetag::Yes`),
     and jumps to `point.resume`.
   - `insert_switch` installs the `SwitchInt(Move(_discr))` table at `bb0`:
     - `0` (`UNRESUMED`) $\rightarrow$ `former_entry` (the original entry block,
       pushed to the end of `basic_blocks`);
     - `1` (`RETURNED`) $\rightarrow$ `Assert(false, ResumedAfterReturn)` for
       `Async` and `Coroutine`, or `insert_none_ret_block` (`_0 = Option::None;
       return` for `Gen`, `_0 = AsyncGenFinished; return` for `AsyncGen`);
     - `2` (`POISONED`) $\rightarrow$ `Assert(false, ResumedAfterPanic)` (when
       `can_unwind` is true);
     - `3 .. 3 + K - 1` (`Suspend0 .. Suspend{K-1}`) $\rightarrow$ the resume
       trampoline blocks;
     - `otherwise` $\rightarrow$ `Unreachable`.
10. **Pinning vs. Indirect `self` Argument and Async Context Bridge
    (`mod.rs:555-658, 920-944`):**
    - For `Async`, `AsyncGen`, and `Coroutine`, `make_coroutine_state_argument_pinned`
      (`mod.rs:568-600`) sets `_1: Pin<&mut CoroutineState>`, allocates a fresh
      local `_unpinned: &mut CoroutineState`, inserts
      `_unpinned = Copy((_1.0: &mut CoroutineState))` (`WithRetag::Yes`) as the
      very first statement of `bb0`, and rewrites all coroutine state accesses to
      dereference `*_unpinned`.
    - For `Gen` (`gen fn` / `gen {}`), `make_coroutine_state_argument_indirect`
      (`mod.rs:555-565`) sets `_1: &mut CoroutineState` directly (`arg_count = 1`)
      and rewrites state accesses to `(*_1)`.
    - For `Async` and `AsyncGen`, `transform_async_context` (`mod.rs:620-658`)
      sets `_2: &mut Context<'_>` and prepends two statements at `bb0` entry that
      transmute `Move(_2)` into `NonNull<Context<'static>>` and wrap it in
      `ResumeTy` for the body's internal uses.

Table 1 summarizes the four lowered coroutine kinds at `Runtime(PostCleanup)`
MIR (full machine-readable table in
[`support/state_transform_invariants.json`](support/state_transform_invariants.json)).

| Coroutine Kind | Movability & `Unpin` | `_1` (`self`) Type & Entry Projection | `_2` (Resume Arg) Type | Return Type (`_0`) | `RETURNED` (`1`) Resume Arm | LLVM `_1` Attributes | Tree Borrows Retag on `_1` / `_unpinned` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`Async`** (`async fn`, `async {}`) | `Static` (`!Unpin`) | `Pin<&mut Coro>` $\rightarrow$ `_u = Copy(_1.0)` | `&mut Context<'_>` | `Poll<Output>` | `Assert(false, ResumedAfterReturn)` | `noundef nonnull align(A) dereferenceable(S)` (**no `noalias`**, **no `nofree`**, **no `writable`**) | **NOP** (`NewPermission::new` returns `None`) |
| **`Gen`** (`gen fn`, `gen {}`) | `Movable` (`Unpin` if fields `Unpin`) | `&mut Coro` (`*_1` directly) | None (`arg_count = 1`) | `Option<Yield>` | `_0 = Option::None; return` | `noalias noundef nonnull align(A) writable nofree dereferenceable(S)` | `StrongProtector` + `ReservedFrz` (`FnEntry`) |
| **`AsyncGen`** (`async gen fn`, `async gen {}`) | `Static` (`!Unpin`) | `Pin<&mut Coro>` $\rightarrow$ `_u = Copy(_1.0)` | `&mut Context<'_>` | `Poll<Option<Yield>>` | `_0 = AsyncGenFinished; return` | `noundef nonnull align(A) dereferenceable(S)` (**no `noalias`**) | **NOP** (`NewPermission::new` returns `None`) |
| **`Coroutine`** (`#[coroutine]`) | `Static` (`!Unpin`) or `Movable` (`Unpin`) | `Pin<&mut Coro>` $\rightarrow$ `_u = Copy(_1.0)` | `Resume` | `CoroutineState<Y, R>` | `Assert(false, ResumedAfterReturn)` | `noalias writable nofree` **iff** `Movable && Unpin` | **NOP** if `Static`; `StrongProtector` + `ReservedFrz` if `Movable && Unpin` |

### 2. Self-Referential Borrows Across `Yield`, `!Unpin`, and Tree Borrows Soundness

Basis: source + execution + derived

When an `async fn` holds a reference `r: &T` or `r: &mut T` across an `.await`
suspension point pointing to another variable saved in the same coroutine frame:
1. Both `r` and its referent variable are in `MaybeRequiresStorage` across the
   `Yield` terminator (because `r` is in `MaybeLiveLocals` and the referent is in
   `MaybeBorrowedLocals` while `!movable`, `layout.rs:120-133`), so
   `compute_storage_conflicts` marks their `CoroutineSavedLocal`s as conflicting
   and assigns them disjoint byte ranges inside `*self`.
2. On resume, `Future::poll(self: Pin<&mut Self>, cx: &mut Context<'_>)` receives
   `_1: Pin<&mut CoroutineState>` and executes `_unpinned = Copy(_1.0)`
   (`WithRetag::Yes`). When `-Zmir-emit-retag` runs (`AddRetag`), it emits
   `Retag([fn entry] _1)` and `Retag(_unpinned)`.
3. Why does creating and dereferencing `_unpinned: &mut CoroutineState` (covering
   the entire coroutine struct `[0, sizeof(CoroutineState))`) **not** invalidate
   or conflict with the pre-existing self-referential tag `t_r` stored inside
   `((*_unpinned as variant#V).field_r)`?
   - In `src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:136-155`,
     `NewPermission::new` checks:
     ```rust
     let ty_is_unpin = pointee.is_unpin(*cx.tcx, cx.typing_env())
         && pointee.is_unsafe_unpin(*cx.tcx, cx.typing_env());
     if matches!(ref_mutability, Some(Mutability::Mut) | None if !ty_is_unpin) {
         // Mutable reference / Box to pinning type: retagging is a NOP.
         return None;
     }
     ```
   - Because every `Movability::Static` coroutine (`async fn`, `async {}`,
     `async gen`, `#[coroutine] static`) is `!Unpin`, `NewPermission::new`
     returns `None` for both `Retag([fn entry] _1)` and `Retag(_unpinned)`.
     Neither `_1` nor `_unpinned` creates a new `BorTag` or attaches a
     `StrongProtector` to the coroutine frame! Instead, `_unpinned` inherits the
     parent pointer's tag (the caller's `Pin<&mut CoroutineState>` tag `t_frame`,
     which is an ancestor of every self-referential borrow tag `t_r` created
     inside previous `poll` invocations).
   - What if `poll` mutates a sibling field `((*_unpinned as variant#V).field_s)`
     or takes a fresh `&mut InnerUnpin` (`Unpin`) to a sibling field while a
     self-referential borrow `t_r: &mut u64` of `field_a` is live across `.await`
     (tested in Miri litmus `L05_inner_unpin_sibling_mutation`)?
     - Because `field_s` and `field_a` occupy **disjoint byte ranges** inside the
       coroutine allocation (`EnsureCoroutineFieldAssignmentsNeverAlias` +
       `storage_conflicts`), writing to `field_s` through `t_frame` (or retagging
       `&mut (*_unpinned).field_s` as a new `ReservedFrz` child tag on the byte
       range of `field_s`) only performs a `LocalAccess` on `field_s`'s byte
       range! Under Tree Borrows (`NewPermission::outside_perm = ReservedFrz`
       with `accessed = false`, `tree_borrows/mod.rs:170-212`), `t_r` is
       uninitialized (`accessed = false`) outside `field_a`'s byte range, so
       writes and retags on disjoint sibling fields of the coroutine frame never
       disable `t_r`!
   - What if an `async fn` unwinds mid-`.await` while a self-referential mutable
     borrow `r = &mut local_arr[0]` and a drop guard `CountedDrop` are live
     (litmus tests `L11` and `L20`)?
     - The inner `poll`'s unwind transitions along the `cleanup` edge of the
       outer `poll`, which drops `guard` (`CountedDrop::drop`) and then jumps to
       `poison_block` (`discriminant((*_unpinned)) = 2; resume`). When the
       caller catches the panic (`catch_unwind`) and drops the pinned coroutine,
       `coroutine_drop` switches on `discriminant == 2`, hits `default_block`,
       and returns immediately without touching `guard` or `local_arr` a second
       time (`DROP_COUNTER == 1`).

Table 2 summarizes the 20 Miri litmus tests and the negative `Unpin` control
from [`support/miri_litmus_results.json`](support/miri_litmus_results.json).

| Litmus ID | Pattern Tested | Tree Borrows (`-Zmiri-tree-borrows`) | Stacked Borrows (Default) |
| :--- | :--- | :--- | :--- |
| `L01` | Shared borrow `&[u64; 4]` across 1 `.await` | PASS (`0` UB) | PASS (`0` UB) |
| `L02` | Two shared slice borrows across 3 `.await`s | PASS (`0` UB) | PASS (`0` UB) |
| `L03` | Mutable borrow `&mut u64` across 1 `.await` | PASS (`0` UB) | PASS (`0` UB) |
| `L04` | `split_at_mut` disjoint `&mut [u64]` across 2 `.await`s | PASS (`0` UB) | PASS (`0` UB) |
| `L05` | Self-ref `&mut u64` to inner `Unpin` struct + sibling mutation across `.await` | PASS (`0` UB) | PASS (`0` UB) |
| `L06` | Outer self-ref `async fn` awaiting inner self-ref `async fn` | PASS (`0` UB) | PASS (`0` UB) |
| `L07` | Layered two-level `&mut` reborrow across sequential `.await`s | PASS (`0` UB) | PASS (`0` UB) |
| `L08` | `UnsafeCell<u64>` shared aliases mutated across `.await` | PASS (`0` UB) | PASS (`0` UB) |
| `L09` | Partial drop of suspended future at `Suspend0` (`1` guard live, `1` uninit) | PASS (`0` UB, `1` drop) | PASS (`0` UB, `1` drop) |
| `L10` | Partial drop of suspended future at `Suspend1` (`2` guards live) | PASS (`0` UB, `2` drops) | PASS (`0` UB, `2` drops) |
| `L11` | Mid-`.await` panic unwinds through cleanup ladder into `POISONED` (`2`) | PASS (`0` UB, `1` drop) | PASS (`0` UB, `1` drop) |
| `L12` | Drop of unresumed `async move` future (`UNRESUMED = 0` `drop_clean` path) | PASS (`0` UB, `1` drop) | PASS (`0` UB, `1` drop) |
| `L13` | Disjoint-scope saved arrays sharing overlapped coroutine storage slots | PASS (`0` UB) | PASS (`0` UB) |
| `L14` | Saved array index local restored via `MirPatch` before `PlaceElem::Index` | PASS (`0` UB) | PASS (`0` UB) |
| `L15` | Movable `gen move` block (`Iterator::next(&mut self)` with `FnEntry` protector) | PASS (`0` UB) | PASS (`0` UB) |
| `L16` | `gen fn` partial iteration + mid-stream drop at `Suspend1` | PASS (`0` UB, `2` drops) | PASS (`0` UB, `2` drops) |
| `L17` | `#[coroutine] static move` with self-referential `&mut [u64; 2]` across yields | PASS (`0` UB) | PASS (`0` UB) |
| `L18` | Heap `Box::pin` self-referential future polled across 4 suspension points | PASS (`0` UB) | PASS (`0` UB) |
| `L19` | Resuming completed `async fn` (`RETURNED = 1` $\rightarrow$ `ResumedAfterReturn`) | PASS (defined panic) | PASS (defined panic) |
| `L20` | Resuming panicked `async fn` (`POISONED = 2` $\rightarrow$ `ResumedAfterPanic`, `0` double-drop) | PASS (defined panic) | PASS (defined panic) |
| **NegCtrl** | Manual `impl Unpin` on self-referential struct passed as `&mut Self` | **REJECTED (Tree Borrows UB)** | **REJECTED (Stacked Borrows UB)** |

### 3. Empirical Anatomy of 50 `Runtime(PostCleanup)` Coroutine State Machines

Basis: execution

Table 3 summarizes the 50-coroutine `Runtime(PostCleanup)` MIR census
([`support/coroutine_mir_census.json`](support/coroutine_mir_census.json))
compiled with `rustc 1.99.1` (`-Zmir-opt-level=0 -Zdump-mir=StateTransform|coroutine_drop -Zprint-type-sizes`).

| Metric Across 50 Coroutines (`c01`–`c50`) | Minimum | Median | Maximum | Total / Notes |
| :--- | :---: | :---: | :---: | :--- |
| Suspension points ($K$) | `0` (`c01`) | `2.0` | `20` (`c50`) | `145` total yield points across 50 coroutines |
| Total variants ($3 + K$) | `3` | `5.0` | `23` | `UNRESUMED` (`0`), `RETURNED` (`1`), `POISONED` (`2`), `Suspend0..K-1` |
| Pre-`StateTransform` basic blocks | `4` | `47.5` | `428` (`c50`) | Before `insert_switch` and resume trampolines |
| Post-`StateTransform` `resume`/`poll` BBs | `10` | `52.0` | `451` (`c50`) | $+2 + K$ blocks added (`bb0` switch, `Unreachable`, $K$ trampolines, panic/poison blocks) |
| Post-`StateTransform` `cleanup` BBs | `3` | `20.0` | `121` (`c50`) | All unwind edges funneled through `poison_block` (`discr = 2`) |
| Synthesized `coroutine_drop` shim BBs | `2` | `20.0` | `89` (`c50`) | Drops only live-at-suspend fields; `1` and `2` jump to `default_block` (`Return`) |
| Coroutine state `sizeof` (bytes) | `16 B` | `64.0 B` | `328 B` (`c14`) | `c06` packs `416 B` of disjoint-scope variant payloads into `168 B` (`2.48x` overlap packing) |
| Coroutine state `alignof` (bytes) | `8 B` | `8.0 B` | `8 B` | Pointer/u64-aligned across all 50 state machines |

Representative structural highlights from `support/coroutine_mir_census.json`:
- **Storage-conflict overlap packing (`c06_disjoint_scopes_storage_overlap`):**
  Three sequential lexical scopes each hold a 128-byte `[u64; 16]` buffer across
  an `.await` point ($K = 3$). Because their `MaybeRequiresStorage` live ranges
  are pairwise disjoint, `compute_storage_conflicts` records zero cross-buffer
  conflicts; the three 136-byte `Suspend0`/`Suspend1`/`Suspend2` variants (`408 B`
  sum) overlap at the exact same offset inside a `168 B` coroutine struct.
- **Linear growth in nested `poll` combinator chains (`c31`–`c39`):**
  Nesting `async fn` calls from depth 2 (`c31_nested_depth2`) to depth 10
  (`c39_nested_depth10`) without inlining grows the outer coroutine struct size
  linearly from `112 B` (`c31`) $\rightarrow$ `128 B` (`c32`) $\rightarrow$
  `144 B` (`c33`) $\rightarrow$ `168 B` (`c34`) $\rightarrow$ `184 B` (`c35`)
  $\rightarrow$ `200 B` (`c36`) $\rightarrow$ `216 B` (`c37`) $\rightarrow$
  `232 B` (`c38`) $\rightarrow$ `248 B` (`c39`, `264 B` in `c39` outer), while
  each layer's un-inlined `poll` body stays small (`28` BBs) and delegates via a
  nested `Future::poll` call on `((_1 as variant#3).0: InnerFuture)`.

## Boundaries

1. **Async drop (`AsyncDrop` / `coroutine_drop_async`, `drop.rs:38-65, 231-321`)
   is unstable and feature-gated:** In `rustc 1.99.1`, `has_async_drops` is
   `false` for all standard Rust programs unless `#![feature(async_drop)]` is
   enabled; standard coroutines always synthesize the synchronous
   `coroutine_drop` shim (`InstanceKind::Shim(ShimKind::DropGlue)`).
2. **`UnsafePinned` (`#125735`) per-byte `!Unpin` tracking is not yet active in
   Miri's Tree Borrows (`tree_borrows/mod.rs:153`):** As noted in Miri's `FIXME:
   with UnsafePinned, this should do proper per-byte tracking`, both `rustc
   1.99.1` and Miri `0.1.0` gate `noalias` and `NewPermission` retagging on whole-type
   `pointee.is_unpin() && pointee.is_unsafe_unpin()`.
3. **Cross-crate `.anneal-mir` capture of coroutine witnesses:** Because
   `StateTransform` runs before `Runtime(PostCleanup)`, `.anneal-mir` captures
   the concrete `CoroutineLayout` inside `body.coroutine.coroutine_layout` and
   the concrete `coroutine_drop` body inside `body.coroutine.coroutine_drop`; no
   `TerminatorKind::Yield` or `TerminatorKind::CoroutineDrop` ever survives to
   `Runtime(PostCleanup)` MIR.

## Evidence

- **Primary `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and Miri
  (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) sources:**
  - `compiler/rustc_mir_transform/src/coroutine/mod.rs:161-1324` (`StateTransform`,
    `TransformVisitor`, `insert_switch`, `generate_poison_block_and_redirect_unwinds_there`,
    `create_coroutine_resume_function`, `make_coroutine_state_argument_pinned`,
    `make_coroutine_state_argument_indirect`, `transform_async_context`,
    `eliminate_get_context_calls`, `EnsureCoroutineFieldAssignmentsNeverAlias`).
  - `compiler/rustc_mir_transform/src/coroutine/layout.rs:53-442`
    (`locals_live_across_suspend_points`, `compute_storage_conflicts`,
    `compute_layout`).
  - `compiler/rustc_mir_transform/src/coroutine/drop.rs:68-227`
    (`elaborate_coroutine_drops`, `insert_clean_drop`,
    `create_coroutine_drop_shim`).
  - `compiler/rustc_middle/src/ty/sty.rs:83-143` (`CoroutineArgs::UNRESUMED = 0`,
    `RETURNED = 1`, `POISONED = 2`, `RESERVED_VARIANTS = 3`).
  - `compiler/rustc_middle/src/ty/layout.rs:979-996, 1058-1074` (`ty::Coroutine`
    variant layout and `ty_and_layout_pointee_info_at` `unpin` check).
  - `compiler/rustc_ty_utils/src/abi.rs:117-222, 322-420` (`fn_sig_for_fn_abi`
    for coroutines and `arg_attrs_for_rust_scalar` `NoAlias`/`Writable`/`NoFree`
    gating on `unpin`).
  - `src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:126-221`
    (`NewPermission::new` `!ty_is_unpin` retag NOP).
- **Preserved support artifacts (observed 2026-11-14):**
  - [`support/collect_coroutine_mir_census.py`](support/collect_coroutine_mir_census.py)
    and [`support/coroutine_mir_census.json`](support/coroutine_mir_census.json)
    (50-coroutine `Runtime(PostCleanup)` MIR and layout dataset).
  - [`support/run_miri_coroutine_litmus.py`](support/run_miri_coroutine_litmus.py)
    and [`support/miri_litmus_results.json`](support/miri_litmus_results.json)
    (20 safe self-referential Miri litmus tests + negative `Unpin` UB control).
  - [`support/state_transform_invariants.json`](support/state_transform_invariants.json)
    (formal `StateTransform` state and aliasing invariant table).

## Revalidation

Run the preserved census and Miri litmus scripts from the package root:

```bash
python3 support/collect_coroutine_mir_census.py
python3 support/run_miri_coroutine_litmus.py
```

A passing run regenerates `support/coroutine_mir_census.json` (50 coroutines) and
verifies `20 / 20` Miri passes under both `-Zmiri-tree-borrows` and Stacked
Borrows plus UB rejection on the forged-`Unpin` negative control.
