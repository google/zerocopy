# Rust Coroutines, `gen` Blocks, `AsyncDrop`, and Self-Referential Generator Pinning

## Summary

Rust lowers `async` functions and blocks (RFC 2394), Rust 2024 `gen` blocks (RFC 3513), `async gen` blocks, and experimental `#[coroutine]` closures (RFC 2033) through a single MIR `StateTransform` pass into discriminant-indexed state machines (`ty::Coroutine`). Every lowered coroutine reserves three variant indices ahead of suspension points: `0` (`Unresumed`), `1` (`Returned`), and `2` (`Panicked` / `POISONED`), followed by `3 + i` (`Suspend{i}`) for each lowered `TerminatorKind::Yield`. Although MIR types `Rvalue::Discriminant` on a coroutine as `u32`, physical ABI layout narrows the tag scalar to `Integer::fit_unsigned(max_discr)` (`u8` for up to 256 variants) with `TagEncoding::Direct`, wraps every saved interior local `T` in `MaybeUninit<T>`, promotes multi-variant and storage-conflicting locals into an alignment-sorted outer prefix alongside captured upvars and the tag, and forces `largest_niche: None` so outer enums (`Option<Coroutine>`) cannot alias self-referential fields when reading a niche tag.

Self-referential borrows held across `Yield` are permitted only in immovable coroutines (`Movability::Static`: `async`, `async gen`, and `static #[coroutine]`), which take `self: Pin<&mut Self>` on resumption (`Future::poll`, `AsyncIterator::poll_next`, `Coroutine::resume`). Movable coroutines (`Movability::Movable`: `gen` blocks and non-`static` `#[coroutine]`) forbid cross-yield borrows and implement `Unpin` unconditionally without field sub-obligations; `gen` blocks take `&mut Self` via `Iterator::next` and implement `FusedIterator` via a compiler lang item. Because `StateTransform` copies `(_1.0: &mut Coroutine)` into a plain `&mut Coroutine` local with `WithRetag::Yes` on poll entry, standard `&mut` uniqueness would invalidate intra-coroutine self-references. Both `rustc` ABI lowering and Miri's Tree Borrows avoid Undefined Behavior by gating mutable-reference aliasing rules on `Unpin` (and `UnsafeUnpin`): when `!ty_is_unpin`, LLVM `noalias`, `nofree`, and `writable` attributes are omitted, and Tree Borrows `NewPermission::new` returns `None`, making `&mut !Unpin` and `Box<!Unpin>` retags (including `FnEntry` protectors) complete no-ops until per-field `UnsafePinned<T>` (RFC 3467) replaces whole-struct suppression.

Source inspection and toolchain execution establish three critical destructor and failure boundaries:
1. **Unwind poisoning discrepancy on `gen` blocks:** Although RFC 3513 specifies that a panicking `gen` block unwinds out of `next()` and behaves like `return` thereafter, `StateTransform` routes unwind edges to `POISONED` (`2`) and emits an unconditional `Assert` on resumption for all coroutine kinds, causing a subsequent `next()` call on a panicked `gen` block to panic with the literal placeholder string `` "`gen fn` should just keep returning `None` after panicking" ``.
2. **Synchronous unwind fallback under `AsyncDrop`:** Experimental `AsyncDrop` (`feature(async_drop)`) embeds child `async_drop_in_place<Field>` coroutines into extra `Suspend` variants of the parent coroutine for scope-exit and async cancellation paths, while synchronous unwinding (`is_cleanup` blocks) and unresumed drops (`Unresumed = 0`) still invoke synchronous `Drop::drop`.
3. **Missing `RETURNED` transition in `create_coroutine_drop_shim_async`:** Reaching `TerminatorKind::CoroutineDrop` inside an async drop shim returns `Poll::Ready(())` without setting the dropped coroutine's discriminant to `RETURNED` (`1`), while `async_drop_in_place` returns `Poll::Ready(())` idempotently on re-poll; polling `async_drop_in_place` twice executes `AsyncDrop::drop` twice on already-dropped state.

## Applicability

This report covers the joint behavior of four upstream subjects recorded in `REPORT.json`:
- **`rust-lang/rust` at `560abf7946ae41fd210edac5dfe829d7eff86eec`:** Implementation source for `rustc_mir_transform::coroutine`, `rustc_abi::layout::coroutine`, `rustc_ty_utils::{abi, layout}`, `rustc_trait_selection`, `rustc_next_trait_solver`, `core::{ops::coroutine, pin, future::async_drop, panicking}`, and Miri's `borrow_tracker::tree_borrows`.
- **`rustc` `1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`):** Executed compiler used to record `-Z print-type-sizes` layouts, `--emit=mir` output, and runtime execution of `async`, `gen`, and `async_drop` probes.
- **`rust-lang/rfcs` at `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`:** Specifications in RFC 2033, RFC 2349, RFC 2394, RFC 3467, and RFC 3513.
- **`rust-lang/reference` at `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`:** Language rules in `src/destructors.md` and `src/special-types-and-traits.md`.

Configuration boundaries: `async` applies to stable Rust (editions 2018–2024); `gen` blocks require `#![feature(gen_blocks)]` (`gen` reserved in edition 2024, `k#gen` in 2021); raw coroutines require `#![feature(coroutines, coroutine_trait)]`; `AsyncDrop` requires `#![feature(async_drop)]`; `UnsafePinned` requires `#![feature(unsafe_pinned)]`. Poisoning (`POISONED = 2`) requires `-C panic=unwind` with `can_unwind == true` and default `-Z async-panic=yes`. Complementary corpus packages `rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics` and `self-referential-unpin-coroutine-field-slicing-and-sroa` cover LLVM SROA optimization barriers on coroutines; this report focuses on cross-flavor state synthesis, witness/niche layout, `!Unpin` vs `UnsafePinned` protector suppression, panic poisoning, and `AsyncDrop`.

## Findings

### 1. Coroutine Taxonomy, Receiver Signatures, and Auto-Trait Witness Rules

`Basis: normative + source + execution`

Every `async` body, `gen` block, `async gen` block, and `#[coroutine]` closure has type `TyKind::Coroutine(DefId, GenericArgsRef)` distinguished by `hir::CoroutineKind`. `StateTransform` (`compiler/rustc_mir_transform/src/coroutine/mod.rs:938-968, 1093-1119`) and `fn_sig_for_fn_abi` (`compiler/rustc_ty_utils/src/abi.rs:119-224`) rewrite the pre-transform by-value coroutine body into the target resumption ABI:

| `CoroutineKind` | `Movability` | Lowered Resumption Signature | Yield (`make_state(..., false)`) | Return (`make_state(..., true)`) | Builtin `Unpin` | Builtin `FusedIterator` |
| --- | --- | --- | --- | --- | --- | --- |
| `Desugared(Async, _)` | `Static` | `fn(Pin<&mut Self>, &mut Context<'_>) -> Poll<Ret>` | `Poll::Pending` (`1`) | `Poll::Ready(val)` (`0`) | Never (`!Unpin`) | No |
| `Desugared(Gen, _)` | `Movable` | `fn(&mut Self) -> Option<Yield>` (`arg_count = 1`) | `Option::Some(val)` (`1`) | `Option::None` (`0`) | Always (`Unpin`) | Yes (`LangItem`) |
| `Desugared(AsyncGen, _)` | `Static` | `fn(Pin<&mut Self>, &mut Context<'_>) -> Poll<Option<Y>>` | `val` (`Poll<Option<Y>>`) | `AsyncGenFinished` (`Ready(None)`) | Never (`!Unpin`) | No |
| `Coroutine(Static)` | `Static` | `fn(Pin<&mut Self>, Resume) -> CoroutineState<Y, Ret>` | `Yielded(val)` (`0`) | `Complete(val)` (`1`) | Never (`!Unpin`) | No |
| `Coroutine(Movable)` | `Movable` | `fn(Pin<&mut Self>, Resume) -> CoroutineState<Y, Ret>` | `Yielded(val)` (`0`) | `Complete(val)` (`1`) | Always (`Unpin`) | No |

Three type-checking and trait rules govern these constructs:
1. **`ResumeTy` lifetime erasure for `async` / `async gen`:** HIR passes `ResumeTy` (wrapping `NonNull<Context<'static>>`) across `.await` yields to avoid higher-ranked region errors in borrowck. `eliminate_get_context_calls` (`coroutine/mod.rs:660-700`) inlines `LangItem::GetContext` into pointer casts before liveness analysis so `ResumeTy` and `&mut Context<'_>` do not conflict across `.await`, and `transform_async_context` (`lines 616-654`) retypes `_2` to `&mut Context<'_>`. For `Gen` blocks, `body.arg_count` becomes `1` (`line 1199`) and `START_BLOCK` initializes `CTX_ARG` to `()` (`lines 953-968`).
2. **Non-structural `Unpin` vs structural `CoroutineWitness` auto traits:** For `Send`, `Sync`, `Freeze`, `UnwindSafe`, and `RefUnwindSafe`, `ty::Coroutine(def_id, args)` decomposes structurally into `[tupled_upvars_ty, CoroutineWitness(def_id, args)]` (`compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs:87-98`), checking every upvar and every saved interior local except non-TLS `LocalInfo::StaticRef` and `LocalInfo::FakeBorrow` (`ignore_for_traits = true`, `coroutine/layout.rs:372-382`). For `LangItem::Unpin`, `candidate_assembly.rs:816-829` and `confirmation.rs:258-259` bypass `CoroutineWitness` completely: `Movability::Static` suppresses `Unpin` unconditionally (even with zero `.await`s), whereas `Movability::Movable` emits a subgoal-free `BuiltinCandidate` (even if a `gen` block holds `PhantomPinned` across `yield`).
3. **`FusedIterator` divergence from RFC 3513 and `#[must_not_suspend]`:** Whereas RFC 3513 (`text/3513-gen-blocks.md:159, 801-803`) stated that `gen` blocks would not implement `FusedIterator` for lack of a lang item, `rustc` defines `LangItem::FusedIterator` and implements it automatically for `gen` coroutines (`confirmation.rs:243-249`). At `mir_coroutine_witnesses` time, `check_suspend_tys` (`coroutine/layout.rs:534-730`) checks saved types for `#[must_not_suspend]` lints and rejects `#[rustc_scalable_vector]` types held across suspension points with a hard error (`lines 616-620`).

### 2. `StateTransform` Discriminant Synthesis, Conflict Coloring, and Physical Layout

`Basis: source + execution + derived`

`CoroutineArgsExt` (`compiler/rustc_middle/src/ty/sty.rs:84-150`) assigns variant indices `UNRESUMED = 0` (`"Unresumed"`), `RETURNED = 1` (`"Returned"`), `POISONED = 2` (`"Panicked"`), and `RESERVED_VARIANTS + i = 3 + i` (`"Suspend{i}"`).

`locals_live_across_suspend_points` (`compiler/rustc_mir_transform/src/coroutine/layout.rs:83-184`) runs `MaybeStorageLive`, `MaybeBorrowedLocals`, `MaybeRequiresStorage`, and `MaybeLiveLocals`. At each `Yield` block $b$, saved locals are:
$$S_b = \begin{cases} \bigl(\mathrm{Live}(b) \cap \mathrm{RequiresStorage}(b)\bigr) \setminus \{\text{\_1}\} & \text{if } \mathrm{movable}, \\ \bigl((\mathrm{Live}(b) \cup \mathrm{Borrowed}(b)) \cap \mathrm{RequiresStorage}(b)\bigr) \setminus \{\text{\_1}\} & \text{if } \neg\mathrm{movable}. \end{cases}$$

Unioning with `MaybeBorrowedLocals` when `!movable` preserves referents of interior references across `Yield` until `StorageDead` even when the referent local is never named again directly. `StorageConflictVisitor` (`coroutine/layout.rs:294-341`) records pairwise simultaneous storage-liveness across all reachable non-`Unreachable` blocks, and `EnsureCoroutineFieldAssignmentsNeverAlias` (`coroutine/mod.rs:1272-1385`) verifies that direct saved-local assignments `_lhs = _rhs` always conflict so their slots never alias (`rust-lang/rust#73137`). Because MIR `PlaceElem::Index(local)` requires a bare `Local`, `process_projection_elem` (`coroutine/mod.rs:425-445`) injects `local = copy (((*_self) as variant#v).idx)` before any array index using a remapped local, while stripping `StorageLive`/`StorageDead` on remapped locals (`lines 459-464`).

Physical layout (`compiler/rustc_ty_utils/src/layout.rs:549-604` and `compiler/rustc_abi/src/layout/coroutine.rs:61-339`) enforces four invariants:
1. **`MaybeUninit<T>` wrapping of saved locals:** Every saved local `T` in `field_tys` is laid out as `MaybeUninit<T>` (`Ty::new_maybe_uninit`, `rustc_ty_utils/src/layout.rs:572-574`), permitting uninitialized padding and heterogeneous slot overlap (e.g., `NonZeroU64` in `Suspend0` sharing bytes with `0u64` in `Suspend1`) without scalar validity UB when moving unpinned coroutines. Upvars keep their exact types.
2. **Greedy prefix promotion (`coroutine_saved_local_eligibility`, `coroutine.rs:62-156`):** Locals live in $>1$ variant become `Ineligible` (promoted to the outer prefix). Conflicting pairs across distinct variants greedily promote whichever local has more total storage conflicts (`lines 100-125`). If $<2$ variants retain private locals, all saved locals are promoted to eliminate inter-region padding (`lines 132-145`).
3. **MIR `u32` vs ABI narrowed tag and joint prefix sorting:** While `CoroutineArgs::discr_ty` is `u32` (`sty.rs:148-150`), ABI layout selects `discr_int = Integer::fit_unsigned(max_discr)` with `valid_range: 0..=max_discr` (`u8` for $\le 256$ total variants) and `TagEncoding::Direct` (`coroutine.rs:184-189, 316-321`). Upvars, the tag scalar, and promoted locals are sorted jointly by `layout_of_univariant` (`lines 191-198`), so promoted locals can precede upvars at offset `0`.
4. **Niche suppression (`largest_niche: None`):** `coroutine.rs:324-330` sets `largest_niche: None` on the coroutine `LayoutData`. Even though the `u8` tag leaves `max_discr + 1 ..= 255` unused, exposing an interior niche to `Option<Coroutine>` could read aliased self-referential bytes (`rust-lang/rust#63818`, `rust-lang/miri#3780`).

On `self_ref_two_awaits(seed: u64, flag: bool) -> u64` (`rustc 1.98.0-nightly -Z print-type-sizes`), total size is `72` bytes (align `8`): `local_buf: [u64; 2]` (16 B, live in `Suspend0` and `Suspend1`) is promoted to `offset: 0` ahead of upvar `seed: u64`, while `Suspend0`-only `r: &mut u64` (8 B) overlaps `Suspend1`-only `val: u64` (8 B) + `non_overlapping: [u8; 24]` (24 B).

### 3. Self-Referential Locals, Pinning, and Tree Borrows Protector Omission

`Basis: normative + source + derived`

Once an immovable coroutine suspends with an interior borrow `r: &mut T = &mut local_x`, `Pin<&mut Coroutine>` (RFC 2349, `library/core/src/pin.rs`) forbids moving or invalidating `*self` prior to drop completion. Yet on resumption, `make_coroutine_state_argument_pinned` (`coroutine/mod.rs:564-596`) inserts at `START_BLOCK[0]`:

```text
_unpinned = copy (_1.0: &mut Coroutine); // WithRetag::Yes
```

All field projections dereference `_unpinned` while `r` aliases `(*_unpinned).local_x`. Under ordinary `&mut` rules, `_1` and `_unpinned` would (a) carry LLVM `noalias`, `nofree`, and `writable`, making writes via `r` followed by reads via `_unpinned` immediate LLVM UB (RFC 3467 `text/3467-unsafe-pinned.md:92-145`), and (b) under Tree Borrows (Villani et al., PLDI 2025, DOI `10.1145/3735592`), create a `ReservedFrz`/`Unique` child tag with `ProtectorKind::StrongProtector` (`RetagMode::FnEntry`) that transitions to `Disabled` (immediate UB) upon any write through sibling tag `r`.

`rustc` and Miri prevent this UB by gating `&mut` and `Box` uniqueness on `Unpin`:
- **ABI attribute omission (`compiler/rustc_ty_utils/src/abi.rs:350-405`):** For `PointerKind::MutableRef { unpin }`, `NoAlias` (`line 364`), `Writable` (`line 375`), and `NoFree` (`line 398`) are emitted **only when `unpin == true`** (and `PointerKind::Box { unpin, global }` emits `NoAlias` only when `unpin && global && box_noalias`, `line 365`).
- **Tree Borrows retag no-op (`src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:126-155`):**

```rust
let ty_is_unpin = pointee.is_unpin(*cx.tcx, cx.typing_env())
    && pointee.is_unsafe_unpin(*cx.tcx, cx.typing_env());
...
if matches!(ref_mutability, Some(Mutability::Mut) | None if !ty_is_unpin) {
    return None;
}
```

When `!ty_is_unpin`, `NewPermission::new` returns `None` in both `RetagMode::Default` and `RetagMode::FnEntry`: no child tag is added to the borrow tree and no `(AllocId, BorTag)` protector is pushed onto `FrameState::protected_tags`.

**RFC 3467 vs implemented `UnsafePinned<T>`:** Because `!Unpin` coarsely disables `noalias` on the entire struct and `Unpin` is a safe trait, `library/core/src/pin/unsafe_pinned.rs:24-40` adds `#[lang = "unsafe_pinned"] #[repr(transparent)] pub struct UnsafePinned<T: ?Sized> { value: UnsafeCell<T> }`. Notably, whereas RFC 3467 (`text/3467-unsafe-pinned.md:233-254, 301-303`) specified `value: T` with read-only `&UnsafePinned<T>` (`get(&self) -> *const T`) and `impl<T: Copy> Copy`, upstream wraps `UnsafeCell<T>`, exposing `get(&self) -> *mut T` (`unsafe_pinned.rs:110-112`) and making `UnsafePinned<T>` **neither `Copy` nor `Freeze`** (while implementing `Sync` when `T: Sync` at `line 33`). Per-byte `UnsafePinned` tracking in Tree Borrows (`tree_borrows/mod.rs:153`) and coroutine field wrapping (`coroutine.rs:329`) remain open `FIXME`s.

### 4. Resume, Synchronous Drop, and Panic-During-Poll Poisoning Invariants

`Basis: normative + source + execution`

`create_coroutine_resume_function` (`coroutine/mod.rs:877-986`) and `create_coroutine_drop_shim` (`coroutine/drop.rs:177-254`) dispatch on `discriminant((*_self))`:

| Discriminant | `Resume` (`poll` / `next` / `resume`) | Sync `Drop::drop` (`drop_glue`) | Unwind in `Resume` (`can_unwind`) |
| --- | --- | --- | --- |
| `0` (`Unresumed`) | Jump to entry; move args into saved fields | Jump to `drop_clean`: drop upvars only | Drop active locals; set discr `= 2`; `UnwindResume` |
| `1` (`Returned`) | `Async`/`Coroutine`: `Assert(false, ResumedAfterReturn)` (`Poll::Pending` if `-Z async-panic=no`; `Ready(())` if `async_drop_in_place`). `Gen`: `None`. `AsyncGen`: `Ready(None)` | Default arm: no-op (`return`) | N/A |
| `2` (`Panicked`) | **All kinds** (`Async`, `Gen`, `AsyncGen`, `Coroutine`): if `can_unwind`, `Assert(false, ResumedAfterPanic)` (`Poll::Pending` if `-Z async-panic=no`); else `Unreachable` | Default arm: no-op (`return`) | N/A |
| `3 + i` (`Suspend{i}`) | `StorageLive` non-remapped locals; move `CTX_ARG` to `resume_arg`; goto `point.resume` | `StorageLive` non-remapped locals; goto `point.drop` ladder (`CoroutineDrop` -> `Return`) | Run local cleanup ladder; jump to `poison_block` (`discr = 2`, `UnwindResume`) |
| Other `u32` | `TerminatorKind::Unreachable` (UB) | Default arm: `return` | N/A |

**`gen` block post-panic discrepancy vs RFC 3513:** RFC 3513 (`text/3513-gen-blocks.md:147`) states that if a `gen` block panics, *"the behavior is similar to that of `return`, except that the call to `next` unwinds instead of returning `None`."* While `library/core/src/panicking.rs:206` defines `panic_const_gen_fn_none_panic = "\`gen fn\` should just keep returning \`None\` after panicking"`, `create_coroutine_resume_function` (`coroutine/mod.rs:897-909`) maps `CoroutineArgs::POISONED` (`2`) to `insert_panic_block(..., ResumedAfterPanic(...))` **without** branching on `Gen` (unlike `RETURNED` at `lines 927-930`). Executing `g_panic.next()` after catching an earlier panic in `rustc 1.98.0-nightly` panics with `` "`gen fn` should just keep returning `None` after panicking" `` instead of returning `None`.

### 5. `AsyncDrop` State Machine Expansion, Cleanup Fallback, and Re-Poll Hazards

`Basis: source + execution`

Under `#![feature(async_drop)]` (`library/core/src/future/async_drop.rs:28-58`), `has_async_drops` (`coroutine/drop.rs:55-82`) checks whether any `Yield` is reachable from the `drop` target ("dropline") of an earlier `Yield` across non-cleanup blocks. When true:
1. **Inline child drop futures and `Suspend` multiplication:** In `probe_coroutines`, an `async` block with a single `.await` holding `AsyncGuard` embeds `{async fn body of async_drop_in_place<AsyncGuard<'_>>()}` (`40` B) into the parent layout (`112` B total) across **four** suspension variants: `Suspend0 (3)` for `pending().await`, `Suspend1 (4)` for normal scope-exit async drop, and `Suspend2 (5)` / `Suspend3 (6)` for `coroutine_drop_shim_async` cancellation suspensions (which panic with `` "`async fn` resumed after async drop" `` if passed to `Future::poll`).
2. **Synchronous `Drop` on unwind and unresumed states:** `has_async_drops` skips `is_cleanup` blocks (`drop.rs:60-63`), emitting synchronous `drop(_g)` along unwind edges (`probe_coroutines.mir:1774-1776`), and `elaborate_coroutine_drops` sets `produce_async_drops: false` (`drop.rs:103`), dropping `Unresumed` (`0`) upvars synchronously.
3. **Double-drop bug on re-polling `async_drop_in_place`:** `coroutine/mod.rs:917-918` makes `async_drop_in_place<T>::{closure}` return `Poll::Ready(())` when re-polled in state `1`, while `create_coroutine_drop_shim_async` (`coroutine/drop.rs:304-310`) rewrites `TerminatorKind::CoroutineDrop` to `Return` + `Poll::Ready(())` **without** setting the target coroutine's discriminant to `RETURNED` (`1`). Polling `pin!(async_drop_in_place(&mut *outer))` twice returns `Ready(())` twice and executes `AsyncGuard::drop` **twice** (`LOG=["async_drop_begin", "async_drop_end", "async_drop_begin", "async_drop_end"]`).

### 6. Verification Engineering Obligations for Mechanized MIR Semantics

`Basis: derived`

1. **Variant-erased field addressing:** Post-`StateTransform` MIR accesses a multi-variant saved local via `((*_self) as variant#v).idx` using only the first variant `v` recorded in `remap` (`coroutine/layout.rs:424-429`), even when `discriminant(*_self) != v` (e.g., initializing `variant#4.0` while discriminant is `0`). Operational semantics must resolve `(variant#v, field#idx)` on `ty::Coroutine` directly to byte offset `layout.variants[v].fields.offset(idx)` without asserting active-variant equality.
2. **`!Unpin` retag suppression:** MIR borrow checkers must omit `Retag` child tags and `FnEntry` protectors on `&mut T` and `Box<T>` whenever `!(T.is_unpin() && T.is_unsafe_unpin())`.
3. **Non-fusing `Gen` panics and dual `AsyncDrop` destructors:** Verifiers cannot assume `FusedIterator` implies post-panic `None` on `gen` blocks, must verify `AsyncDrop` types under both `AsyncDrop::drop` and synchronous `Drop::drop`, and must enforce single-completion polling on `async_drop_in_place`.

## Boundaries

- **`not examined`:** `-Z pack-coroutine-layout` (`CapturesOnly`, currently ignored via `FIXME` at `coroutine/layout.rs:451-452`), `AsyncFn` by-move body synthesis (`coroutine/by_move_body.rs`), and Wasm/MSVC SEH funclet lowering of `poison_block` were **not examined**.
- **`unknown`:** Final stabilization of per-field `UnsafePinned<T>` in coroutine lowering (`rust-lang/rust#125735`) and whether `rustc` will change `POISONED` `Gen` blocks to return `None` or amend RFC 3513 remain **unknown**.
- **`known not to apply`:**
  - LLVM `noalias` and Tree Borrows `FnEntry` protectors are **known not to apply** to `Pin<&mut Coroutine>` for `Movability::Static` (`!Unpin`), and **do apply** to `&mut GenBlock` (`Movability::Movable`, `Unpin`).
  - Enum niche optimization (`size_of::<Option<Coroutine>>() == size_of::<Coroutine>()`) is **known not to apply** because `largest_niche` is forced to `None`.
  - Witness-structural `Unpin` derivation is **known not to apply** to `ty::Coroutine`.
- **`unsupported`:**
  - Holding borrows across `yield` inside `gen` blocks is **unsupported** (RFC 3513 `text/3513-gen-blocks.md:163-175`).
  - Holding `#[rustc_scalable_vector]` locals across suspension points is **unsupported** (`coroutine/layout.rs:616-620`).
  - Querying `layout_of` on `ty::Coroutine` outside `TypingMode::Codegen` is **unsupported** (`LayoutError::TooGeneric`, `rustc_ty_utils/src/layout.rs:550-561`).

## Evidence

### Primary Upstream Source Coordinates (`rust-lang/rust` @ `560abf7946ae41fd210edac5dfe829d7eff86eec`)

| Subsystem | File Path | Symbols and Line Ranges |
| --- | --- | --- |
| `StateTransform`, `Pin` retag, poisoning, `Gen` `None` block | `compiler/rustc_mir_transform/src/coroutine/mod.rs` | `TransformVisitor` (`177-539`), `make_coroutine_state_argument_pinned` (`564-596`), `generate_poison_block_and_redirect_unwinds_there` (`845-874`), `create_coroutine_resume_function` (`877-986`), `StateTransform::run_pass` (`1064-1258`), `EnsureCoroutineFieldAssignmentsNeverAlias` (`1272-1385`) |
| Liveness, borrowed union, conflicts, `#[must_not_suspend]` | `compiler/rustc_mir_transform/src/coroutine/layout.rs` | `locals_live_across_suspend_points` (`83-184`), `compute_storage_conflicts` (`235-292`), `compute_layout` (`344-459`), `check_must_not_suspend_ty` (`581-701`) |
| Sync & `AsyncDrop` shims, missing `RETURNED` write | `compiler/rustc_mir_transform/src/coroutine/drop.rs` | `has_async_drops` (`55-82`), `elaborate_coroutine_drops` (`85-145`), `create_coroutine_drop_shim` (`177-254`), `create_coroutine_drop_shim_async` (`258-352`) |
| Discriminant constants & MIR `u32` `discr_ty` | `compiler/rustc_middle/src/ty/sty.rs` | `CoroutineArgsExt` (`83-150`) |
| `MaybeUninit` local wrapping, prefix packing, `largest_niche: None` | `compiler/rustc_ty_utils/src/layout.rs`, `compiler/rustc_abi/src/layout/coroutine.rs` | `ty::Coroutine` (`rustc_ty_utils/src/layout.rs:549-604`), `coroutine_saved_local_eligibility` (`coroutine.rs:62-156`), `layout` (`coroutine.rs:159-339`) |
| Coroutine `FnSig` & `!Unpin` `NoAlias`/`NoFree`/`Writable` gate | `compiler/rustc_ty_utils/src/abi.rs` | `fn_sig_for_fn_abi` (`119-224`), `arg_attrs_for_rust_scalar` (`318-414`) |
| `Unpin` (`Movability`), `FusedIterator`, & `CoroutineWitness` | `compiler/rustc_trait_selection/src/traits/select/{candidate_assembly.rs, confirmation.rs}`, `compiler/rustc_next_trait_solver/src/solve/assembly/structural_traits.rs` | `candidate_assembly.rs` (`816-837`), `confirmation.rs` (`243-260`), `structural_traits.rs` (`87-98`) |
| Tree Borrows `!Unpin` / `!UnsafeUnpin` retag omission | `src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs` | `NewPermission::new` (`126-155`), `tb_reborrow` (`238-434`) |
| Library traits, `UnsafePinned`, & panic strings | `library/core/src/{ops/coroutine.rs, future/async_drop.rs, pin/unsafe_pinned.rs, panicking.rs}` | `Coroutine` (`coroutine.rs:11-140`), `AsyncDrop` (`async_drop.rs:29-58`), `UnsafePinned` (`unsafe_pinned.rs:24-180`), `panic_const` (`panicking.rs:186-216`) |

### Specifications and Peer-Reviewed Literature

- **RFCs (`rust-lang/rfcs` @ `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`):** RFC 2033 (`text/2033-experimental-coroutines.md`), RFC 2349 (`text/2349-pin.md`), RFC 2394 (`text/2394-async_await.md`), RFC 3467 (`text/3467-unsafe-pinned.md`), RFC 3513 (`text/3513-gen-blocks.md`).
- **The Rust Reference (`rust-lang/reference` @ `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):** `src/destructors.md`, `src/special-types-and-traits.md`.
- **Papers:** Neven Villani, Johannes Hostert, Derek Dreyer, and Ralf Jung, *"Tree Borrows"*, PACMPL Vol. 9, PLDI 2025, Article 188, DOI `10.1145/3735592`; Ralf Jung, Hoang-Hai Dang, Jeehoon Kang, and Derek Dreyer, *"Stacked Borrows: An Aliasing Model for Rust"*, PACMPL Vol. 4, POPL 2020, Article 41, DOI `10.1145/3371109`; Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, and Derek Dreyer, *"RustBelt: Securing the Foundations of the Rust Programming Language"*, PACMPL Vol. 2, POPL 2018, Article 66, DOI `10.1145/3158154`; Ana Lúcia de Moura and Roberto Ierusalimschy, *"Revisiting Coroutines"*, ACM TOPLAS Vol. 31, No. 2, Article 6, 2009, DOI `10.1145/1462166.1462167`.

### Reproducible Execution Probe (`2026-11-20`, `rustc 1.98.0-nightly 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`)

Save `/tmp/probe_coroutines.rs`:

```rust
#![feature(gen_blocks, async_drop)]
#![allow(incomplete_features)]
use std::future::{AsyncDrop, Future, async_drop_in_place};
use std::mem::ManuallyDrop;
use std::pin::{Pin, pin};
use std::task::{Context, Poll, Waker};

pub async fn self_ref_two_awaits(seed: u64, flag: bool) -> u64 {
    let mut local_buf = [seed, seed + 1];
    let r: &mut u64 = &mut local_buf[0];
    *r += 10;
    core::future::pending::<()>().await;
    let val = *r;
    if flag {
        let non_overlapping: [u8; 24] = [7; 24];
        core::future::pending::<()>().await;
        val + non_overlapping[0] as u64
    } else {
        val
    }
}

struct AsyncGuard<'a>(&'a mut Vec<&'static str>);
impl Drop for AsyncGuard<'_> { fn drop(&mut self) { self.0.push("sync_drop"); } }
impl AsyncDrop for AsyncGuard<'_> {
    async fn drop(mut self: Pin<&mut Self>) {
        self.0.push("async_drop_begin");
        core::future::ready(()).await;
        self.0.push("async_drop_end");
    }
}

fn main() {
    let _ = self_ref_two_awaits(1, true);
    let mut g_panic = gen { yield 1u32; if true { panic!("gen boom"); } };
    assert_eq!(g_panic.next(), Some(1));
    let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| g_panic.next()));
    let second = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| g_panic.next()));
    println!("GEN_AFTER_PANIC: {:?}", second.err().and_then(|e| e.downcast_ref::<&'static str>().copied()));

    let mut cx = Context::from_waker(Waker::noop());
    let mut log = Vec::new();
    let mut outer = ManuallyDrop::new(async {
        let _g = AsyncGuard(&mut log);
        core::future::pending::<()>().await;
    });
    assert_eq!(unsafe { Pin::new_unchecked(&mut *outer) }.poll(&mut cx), Poll::Pending);
    {
        let mut drop_fut = pin!(unsafe { async_drop_in_place(&mut *outer) });
        println!("POLL1={:?} POLL2={:?}", drop_fut.as_mut().poll(&mut cx), drop_fut.as_mut().poll(&mut cx));
    }
    println!("LOG={log:?}");
}
```

Run `rustc --edition=2024 -Z print-type-sizes --emit=mir,link /tmp/probe_coroutines.rs -o /tmp/probe_coroutines && /tmp/probe_coroutines`. Observed output:
- `GEN_AFTER_PANIC: Some("`gen fn` should just keep returning `None` after panicking")`
- `POLL1=Ready(()) POLL2=Ready(())`
- `LOG=["async_drop_begin", "async_drop_end", "async_drop_begin", "async_drop_end"]`

## Revalidation

1. **Single-file execution check (< 1 s):** Re-run `/tmp/probe_coroutines.rs` on the target `rustc`. Check whether `GEN_AFTER_PANIC` becomes `None` (fusing panicked `gen` blocks), whether `LOG` records a single `async_drop_begin`/`async_drop_end` pair (fixing missing `RETURNED` assignment in `create_coroutine_drop_shim_async`), and whether `-Z print-type-sizes` keeps `Option<self_ref_two_awaits>` larger than `self_ref_two_awaits` (`largest_niche: None`).
2. **Targeted source diff:** Diff `compiler/rustc_ty_utils/src/abi.rs` (`PointerKind::MutableRef { unpin }`) and `src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs` (`NewPermission::new`) to detect when per-byte `UnsafePinned` tracking replaces whole-pointee `!Unpin` retag suppression.
