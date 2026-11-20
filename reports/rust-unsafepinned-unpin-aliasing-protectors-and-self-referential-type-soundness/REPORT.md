# `UnsafePinned<T>`, `Unpin` vs. `UnsafeUnpin` Aliasing Protectors, and Self-Referential Type Soundness in Rust

## Summary

Rust's `core::pin::UnsafePinned<T>` (RFC 3467, `#125735`, `#![feature(unsafe_pinned)]`) opts mutable references `&mut UnsafePinned<T>`—and structs containing `UnsafePinned<T>` by value—out of uniqueness aliasing assumptions so self-referential futures, coroutines, and intrusive lists can coexist with active internal aliases. Inspecting upstream `rust-lang/rust` (`5c56312f346d7cc8209d9fc0fd660c72e6fc6950`), `rust-lang/miri` (`7e679961edcfe2c526f19153bb8b03de346efa5c`), and RFC 3467 (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`) establishes five core results:

1. **Upstream `UnsafeCell<T>` Containment vs. RFC 3467:** Contrary to RFC 3467's original `value: T` (`Freeze`/`Copy`) sketch, upstream `library/core/src/pin/unsafe_pinned.rs:24-40, 110-125` defines `#[lang = "unsafe_pinned"] #[repr(transparent)] pub struct UnsafePinned<T: ?Sized> { value: UnsafeCell<T> }`, omits `Copy`, explicitly implements `Sync where T: Sync`, and returns `*mut T` from `get(&self)`. Wrapping `UnsafeCell<T>` prevents safe `Pin::as_ref` (`Deref`) calls from placing read-only `Frozen` / `SharedReadOnly` barriers over aliased pinned memory.
2. **Dual `is_unpin && is_unsafe_unpin` Gate:** `library/core/src/marker.rs:927-943` introduces `pub unsafe auto trait UnsafeUnpin {}` (`!UnsafeUnpin` on `UnsafePinned<T>` and `PhantomPinned`). Both `rustc` (`ty_and_layout_pointee_info_at` in `layout.rs:1131-1158`; `arg_attrs_for_rust_scalar` in `abi.rs:362-409`) and Miri (`tree_borrows/mod.rs:136-155`, `stacked_borrows/mod.rs:74-90`) gate `NoAlias`, `Writable`, `NoFree`, nonzero `PointeeInfo::size`, and unique retagging on `is_unpin && is_unsafe_unpin`. This closes safe-`Unpin` soundness holes (`PollFn` wrappers are `Unpin + !UnsafeUnpin`) while keeping the `!Unpin` safeguard for `ty::Coroutine` until coroutine lowering wraps saved locals in `UnsafePinned`.
3. **Why Protector Omission Alone Still Fails in Tree Borrows:** Under `NewPermission::new` (`tree_borrows/mod.rs:151-155`), `!ty_is_unpin` mutable references and `Box`es omit child retagging entirely (`return None`). Omitting only `StrongProtector` while creating an unprotected child tag (`ReservedFrz` or `ReservedIM`) **still causes UB**: an outer write via `&mut SelfRef` transitions the internal pointer tag to `Disabled`, while an outer read—or merely re-entering `poll` via `associated_access() = Some(Read)`—demotes an active `Unique` internal pointer to `Frozen`, triggering UB on the next internal write (`perms.rs:179, 197, 215`). Only full retag omission or per-byte `Permission::Cell` avoids mutual invalidation.
4. **Validity Relaxation vs. `&mut` Safety Invariant:** `UnsafePinned` prevents immediate aliasing UB on `&mut Wrapper(UnsafePinned<T>)`, but exposing overlapping `&mut Wrapper` to safe code remains unsound via `core::mem::swap`. Sound public APIs must confine aliased mutability behind `Pin<&mut Wrapper>` and avoid forging `&mut Field` on `Unpin + UnsafeUnpin` subfields (as demonstrated in `tokio::util::linked_list::Pointers<T>`).

## Applicability

Findings apply to the exact pinned revisions in `REPORT.json`:
- **`rust-lang/rust` (`5c56312f346d7cc8209d9fc0fd660c72e6fc6950`)**: `core::pin::{Pin, UnsafePinned}` (`#![feature(unsafe_pinned)]`), `core::marker::{Unpin, UnsafeUnpin}` (`#![feature(unsafe_unpin)]`), `core::future::PollFn`, `rustc_middle::ty::layout::ty_and_layout_pointee_info_at`, `rustc_ty_utils::{abi, layout}`, `rustc_trait_selection`, and `rustc_mir_transform::coroutine`. Pointer attribute emission requires `tcx.sess.opts.optimize != OptLevel::No` (`layout.rs:1102`); `-C opt-level=0` omits `NoAlias`/`dereferenceable` unconditionally.
- **`rust-lang/rfcs` (`f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`, `text/3467-unsafe-pinned.md`)**: Evaluated jointly with upstream `rust-lang/rust`, explicitly contrasting the RFC's `value: T` draft against `core`'s `UnsafeCell<T>` implementation.
- **`rust-lang/miri` (`7e679961edcfe2c526f19153bb8b03de346efa5c`)**: Default Tree Borrows (`precise_interior_mut = true`, `implicit_writes = false`) and Stacked Borrows borrow trackers across `RetagMode::{Default, FnEntry, Raw}`.
- **`tokio-rs/tokio` (`717c508f9e9ac4317665ff1eb30f29c139ea6363`)**: Production intrusive list `Pointers<T>` (`tokio/src/util/linked_list.rs`).
- **Literature**: Tree Borrows (`doi:10.1145/3735592`), Stacked Borrows (`doi:10.1145/3371109`), and RustBelt (`doi:10.1145/3158154`).

Sibling corpus reports `rustc-miri-freeze-visitor-pointee-retag-and-scalarpair-transmute`, `tree-borrows-two-stage-protector-release-and-reborrow-contracts`, and `ghostcell-branded-tokens-intrusive-containers-and-generational-arenas` cover `UnsafeCellVisitor`, `WeakProtector` vs. `StrongProtector` release, and offset-based intrusive `Adapter`s without `Pin`.

## Findings

### 1. Normative Contract of `core::pin::UnsafePinned<T>` and the `UnsafeCell<T>` Divergence

Basis: normative + source + documentation + derived

In `library/core/src/pin/unsafe_pinned.rs:24-40`, `UnsafePinned<T>` is declared as a `#[repr(transparent)]` lang item wrapping `UnsafeCell<T>`:

```rust
#[lang = "unsafe_pinned"]
#[repr(transparent)]
#[unstable(feature = "unsafe_pinned", issue = "125735")]
pub struct UnsafePinned<T: ?Sized> {
    value: UnsafeCell<T>,
}

#[unstable(feature = "unsafe_pinned", issue = "125735")]
unsafe impl<T: ?Sized + Sync> Sync for UnsafePinned<T> {}

#[unstable(feature = "unsafe_pinned", issue = "125735")]
impl<T: ?Sized> !Unpin for UnsafePinned<T> {}
```

Upstream `core` diverges deliberately from RFC 3467 (`text/3467-unsafe-pinned.md:237-313, 412-418`) on four points:

| Property | RFC 3467 Draft (`f43d5789`) | Upstream `core` (`5c56312f`) | Soundness Consequence |
|---|---|---|---|
| Inner storage | `#[lang = "unsafe_aliased"]`, `value: T` | `#[lang = "unsafe_pinned"]`, `value: UnsafeCell<T>` | Subsumes `UnsafeCell`: blocks `Freeze` on `&UnsafePinned<T>` |
| `Sync` impl | Automatic structural inheritance | Explicit `unsafe impl<T: ?Sized + Sync> Sync` | Overrides `UnsafeCell`'s `!Sync` opt-out; `Send`/`Sync` match `T` |
| `Copy` / `Clone` | `impl<T: Copy> Copy`, `Clone` | Omitted (`!Copy`) | Prevents generic code from equating `Copy` with `Freeze` / unaliased |
| `get` / `raw_get` | `get(&self) -> *const T`, `raw_get(*const Self) -> *const T` | `get(&self) -> *mut T`, `raw_get(*const Self) -> *mut T` | `&self` yields `Cell` / `SharedReadWrite` instead of read-only `Frozen` |

Two technical imperatives drive this design:
1. **`Pin::as_ref` (`Deref`) Soundness (`pin.rs:1365-1371, 1687-1692`):** Because `Pin<Ptr>` unconditionally implements `Deref`, safe code holding `Pin<&mut S>` can always construct `&S` (e.g., to inspect status fields). Under RFC 3467's original `value: T` design, `UnsafePinned<T>` remained `Freeze`, so retagging `&S` imposed `Permission::Frozen` (Tree Borrows) / `SharedReadOnly` (Stacked Borrows) and LLVM `readonly noalias`, triggering immediate UB on any later write through an internal pointer (`Case E_rfc3467` in the probe). Nesting `UnsafeCell<T>` forces `UnsafePinned<T>: !Freeze`, giving `&UnsafePinned<T>` `Permission::Cell` / `SharedReadWrite` (`Case E_core_unsafecell`).
2. **Niche Suppression & `&mut` Safety Invariant (`rustc_ty_utils/src/layout.rs:726-730`, RFC 3467:315-346):** Layout computation sets `NicheOptimizations::Disabled` whenever `def.is_unsafe_cell() || def.is_unsafe_pinned()`, preventing enum discriminant elision from reading niches inside aliased storage. Simultaneously, `UnsafePinned` relaxes only the Abstract Machine uniqueness rule on `&mut`—not its library safety invariant: RFC 3467's `duplicate(&mut S) -> (&mut S, &mut S)` helper produces no immediate UB, yet safe `core::mem::swap(s1, s2)` triggers immediate UB. Sound libraries must therefore gate aliased `&mut S` access behind `Pin<&mut S>` (`!Unpin` prevents safe `Pin::deref_mut`) and expose raw `*mut T` via `get_mut_pinned(self: Pin<&mut Self>)` (`unsafe_pinned.rs:73-76`).

### 2. `Unpin` vs. `UnsafeUnpin` Auto-Trait Split, `PollFn`, and Compiler Attribute Gating

Basis: normative + source + derived + execution

`library/core/src/marker.rs:921-943, 1014-1039` separates safe movability (`pub auto trait Unpin {}`) from aliasing uniqueness (`pub unsafe auto trait UnsafeUnpin {}`, `#[lang = "unsafe_unpin"]`):
- `UnsafeUnpin` is opted out by `UnsafePinned<T>` (`marker.rs:932`) and by `PhantomPinned` (`marker.rs:1038`: unit-struct backwards-compatibility rule preserving `!UnsafeUnpin` without adding an `UnsafePinned<()>` field).
- Like `Freeze`, `UnsafeUnpin` is unconditionally implemented for `PhantomData<T>`, `*const T`, `*mut T`, `&T`, and `&mut T` (`marker.rs:933-943`); it detects only by-value containment.

Why the compiler and Miri require the conjunction `is_unpin && is_unsafe_unpin`:
1. **Closing Safe-`Unpin` `noalias` Miscompilations (`PollFn`, RFC 3467:382-392):** Because `Unpin` is a safe trait, any wrapper `Wrapper<F>` can write `impl<F> Unpin for Wrapper<F> {}` without `unsafe` (as `core::future::PollFn` historically did before tightening to `impl<F: Unpin> Unpin for PollFn<F>`, `poll_fn.rs:144`). When `F` captures an `UnsafePinned` field, `Wrapper<F>` is `Unpin + !UnsafeUnpin`. Under an `Unpin`-only compiler check, that stray safe `impl Unpin` re-enables LLVM `noalias` and triggers UB even without moving `Wrapper<F>`. Checking `is_unpin && is_unsafe_unpin` keeps `noalias` disabled (`Case C`).
2. **Exact `rustc` Attribute Rules (`rustc_middle/src/ty/layout.rs:1091-1159`, `rustc_ty_utils/src/abi.rs:362-409`):**
   When `optimize != OptLevel::No`, `ty_and_layout_pointee_info_at` computes `unpin = optimize && pointee.is_unpin(tcx, typing_env) && pointee.is_unsafe_unpin(tcx, typing_env)` for both `&mut T` (`PointerKind::MutableRef { unpin }`) and built-in `Box<T>` (`PointerKind::Box { unpin, global }`), setting `PointeeInfo::size = layout.size * unpin as _` (zeroing `dereferenceable` when `!unpin` so speculative reads cannot invalidate aliases). `arg_attrs_for_rust_scalar` then gates `NoAlias` (`unpin && !is_return`), `Writable` (`MutableRef { unpin: true } && !is_return` under `-Z llvm-writable`), and `NoFree` (`unpin && !is_return` for `&mut T`) on that same `unpin` bit.
3. **Why `is_unpin` Cannot Be Dropped Yet (`candidate_assembly.rs:816-837`, `coroutine/mod.rs:567-596`):** `ty::Coroutine(def_id, _)` suppresses only `LangItem::Unpin` for `hir::Movability::Static`, while still generating a normal `AutoImplCandidate` for `UnsafeUnpin`. Meanwhile, `coroutine::StateTransform` still creates `unpinned_local: &mut Coroutine = Copy(_1.0)` with `WithRetag::Yes` before saved locals are wrapped in `UnsafePinned`. Dropping `is_unpin` before coroutine lowering adopts `UnsafePinned` would emit `noalias` on self-referential `async fn` futures.

### 3. Tree Borrows and Stacked Borrows Retag Rules: Why Protector Omission Alone Fails

Basis: source + derived + execution

In Miri (`7e679961edcf`), Tree Borrows (`src/borrow_tracker/tree_borrows/mod.rs:136-155`) evaluates `ty_is_unpin = pointee.is_unpin && pointee.is_unsafe_unpin` and executes:

```rust
if matches!(ref_mutability, Some(Mutability::Mut) | None if !ty_is_unpin) {
    // Mutable reference / Box to pinning type: retagging is a NOP.
    // FIXME: with `UnsafePinned`, this should do proper per-byte tracking.
    return None;
}
```

Stacked Borrows (`src/borrow_tracker/stacked_borrows/mod.rs:74-90, 136-153`) analogously degrades `&mut T` / `Box<T>` when `!ty_is_unpin` to `Permission::SharedReadWrite` with `access: None, protector: None`.

Notice why Tree Borrows **must** omit child-tag creation (`return None`) rather than merely omitting `ProtectorKind::StrongProtector` (`protector = None`) while still allocating an unprotected child tag (`ReservedFrz` or `ReservedIM`) on `&mut SelfRef`. Under Miri's exact Tree Borrows transition rules (`perms.rs:138-233, 311-319`, `doi:10.1145/3735592`):

1. **Both `ReservedFrz` and `ReservedIM` Perform a `Read` on Retag (`perms.rs:317`, `mod.rs:369-394`):** Only `Permission::Cell` has `associated_access() == None`. Retagging an unprotected child `t_poll` of root `t0` with `ReservedFrz` or `ReservedIM` immediately executes `Read` on `t0`, which acts as a **foreign read** to sibling internal pointer tag `t_ptr`.
2. **Two Orthogonal Failure Paths Under Protector-Omission-Only (`Case B1`, `Case B2`):**
   - **Outer Write Disables Internal Pointer (`Case B1`):** If `this: &mut SelfRef` (unprotected child `t_poll2: ReservedIM`) writes to the struct (e.g., updating any overlapping/target byte), `child_write` (`perms.rs:196`) activates `t_poll2 -> Unique` and issues a `ForeignWrite` to sibling `t_ptr`, unconditionally setting `t_ptr -> Disabled` (`perms.rs:215`). The next access via `t_ptr` triggers UB (`ChildRead`/`ChildWrite on Disabled`).
   - **Outer Read or Next-Poll Entry Freezes Internal Pointer (`Case B2`):** Once `t_ptr` activates to `Unique` on an internal write, *any* subsequent read through `t_poll2`—or re-entering `poll` where a new child `t_poll3` executes its retag `Read` on `t0`—delivers `ForeignRead` to unprotected `t_ptr: Unique`. By `foreign_read` (`perms.rs:176-180`), unprotected `Unique` transitions to **`Frozen`** (supporting read-read reordering); the next write through `t_ptr` fails with `child_write(Frozen) = None` (`perms.rs:197`).
3. **Retag Omission vs. Future Per-Byte `Cell` Partitioning (`Case C`, `Case D`):**
   - Returning `None` keeps both `&mut SelfRef` and `t_ptr` on ancestor tag `t0`, so all accesses are `Local` (`Case C`).
   - Replacing whole-struct omission with per-byte partitioning (`tree_borrows/mod.rs:153` `FIXME`) assigns **`Permission::Cell`** solely to bytes inside `UnsafePinned<T>`—the unique Tree Borrows state invariant under all `ChildRead`, `ChildWrite`, `ForeignRead`, and `ForeignWrite` transitions (`perms.rs:143, 152, 189, 209`, `associated_access = None`)—while keeping protected `ReservedFrz` (`StrongProtector`) and full `noalias` optimizations on sibling `Unpin + UnsafeUnpin + Freeze` fields (`Case D`). Note `compatible_with_protector` (`perms.rs:99-104`) explicitly rejects `ReservedIM | Cell` because `Cell` cannot enforce `noalias` under `StrongProtector`.

### 4. Formal Memory Invariants for Self-Referential and Intrusive Pinned Types

Basis: normative + source + derived

Combining RFC 2349's `Pin` contract (`pin.rs:430-586`), `UnsafePinned`'s API (`unsafe_pinned.rs:73-140`), Tokio's `LinkedList` (`tokio/src/util/linked_list.rs:74-137`), and RustBelt's semantic model (`doi:10.1145/3158154`), a sound pinned type `S` at base address `ell` must satisfy a four-part separation-logic contract:

1. **Monotonic Pin Anchoring (`Unpinned -> PinnedActive -> PinnedDrop`):** Prior to pinning, `ActiveAliases(ell) = empty` (or only dormant unresumed tags exist). Once pinned with active internal or neighbor pointers, `Anchored(ell)` holds—forbidding bitwise relocation or deallocation until `S::drop(&mut self)` completes (`Drop` guarantee, `pin.rs:510-586`).
2. **Internal Alias Containment:** Every active interior/sibling pointer `p in ActiveAliases(ell)` targeting byte span `[ell + a, ell + b)` within `S` satisfies `[ell + a, ell + b) subseteq UnsafePinnedBytes(ell, S)`.
3. **Raw Sub-Field Projection Discipline (`tokio::util::linked_list::Pointers<T>`):** In `tokio/src/util/linked_list.rs:74-105`, Tokio currently manually composes `UnsafeCell<PointersInner<T>>` + `PhantomPinned` + `unsafe impl Send/Sync`. `UnsafePinned<PointersInner<T>>` unifies all three, **but** Tokio's warning (`linked_list.rs:81-89`) remains binding: never form `&mut (*ptr).prev` or `&mut (*ptr).next`! Because `Option<NonNull<T>>` implements `Unpin + UnsafeUnpin` (`rustc_middle/src/ty/util.rs:1245-1258`), creating `&mut Option<NonNull<T>>` spawns a fresh unique child retag (and `noalias` expectation) over that field, re-introducing UB if another link pointer mutates it. Accesses must project strictly through raw pointers (`UnsafePinned::get_mut_pinned(p)` -> `&raw mut (*ptr).prev`).
4. **`Drop` Alias Severance:** Because `Drop::drop(&mut self)` receives an unpinned `&mut Self` (`text/3467-unsafe-pinned.md:410`), `drop` must sever all incoming aliases (e.g., unlinking nodes) using `UnsafePinned::get_mut_unchecked(&mut self) -> *mut T` before storage `[ell, ell + sizeof(S))` is freed.

## Boundaries

- **`not examined` — Native `rustc`/LLVM IR Compilation and Mechanized Coq/Lean Proofs:** Live `rustc` / LLVM machine-code runs and mechanized Coq/Lean formalizations of `UnsafePinned` were outside this inspection; compiler attribute and layout behavior come from `rustc` source (`5c56312f346d`), Miri source (`7e679961edcf`), and the executable Python Tree Borrows model.
- **`unsupported` — Byte-Precise Per-Field `UnsafePinned` Retagging in Miri (`tree_borrows/mod.rs:153`) and Coroutine Lowering (`coroutine/mod.rs:567-596`):** Miri does not yet assign per-byte `Cell` vs. protected `ReservedFrz` across `UnsafePinned` vs. sibling fields, and `rustc` `StateTransform` does not yet wrap address-taken coroutine locals in `UnsafePinned`. Safe structural field projections for `UnsafePinned` are likewise unsupported without `unsafe` raw-pointer code.
- **`known not to apply` — Unpinned Mutable Aliasing (`mem::swap`) and Inner `&mut Field` Projections:** `UnsafePinned` does **not** make exposing overlapping `&mut MyType` references to arbitrary safe code sound (`core::mem::swap` causes UB), nor does wrapping an outer struct in `UnsafePinned` protect an `Unpin + UnsafeUnpin` subfield once `unsafe` code forms `&mut (*ptr).field`.
- **`unknown` — Protected `Cell` Semantics (`perms.rs:100-103`) and Final RFC 3467 Stabilization Shape (`#125735`):** `perms.rs:100` (`FIXME(TB-Cell)`) leaves unresolved how `Permission::Cell` integrates with `StrongProtector` `noalias` guarantees, and `#125735` has not finalized stabilization details for `&UnsafePinned<T>` vs. `UnsafeCell`.

## Evidence

### Primary Subjects and Inspected Locations

| Subject | Immutable Identity | Inspected Paths & Lines | Key Observed Facts |
|---|---|---|---|
| `rust-lang/rust` | `5c56312f346d7cc8209d9fc0fd660c72e6fc6950` | `library/core/src/pin/unsafe_pinned.rs:24-140` | `#[lang = "unsafe_pinned"]`, `value: UnsafeCell<T>`, `unsafe impl Sync`, `!Unpin`, `get(&self) -> *mut T`, `get_mut_pinned`, `raw_get_mut` |
| `rust-lang/rust` | `5c56312f346d7cc8209d9fc0fd660c72e6fc6950` | `library/core/src/marker.rs:905-1039` | `unsafe auto trait UnsafeUnpin`, `!UnsafeUnpin` on `UnsafePinned` & `PhantomPinned` |
| `rust-lang/rust` | `5c56312f346d7cc8209d9fc0fd660c72e6fc6950` | `library/core/src/pin.rs:430-586, 1365-1371, 1621-1692`; `future/poll_fn.rs:138-162` | `Pin::as_ref`, `Deref`, `get_unchecked_mut`, `Drop` guarantee, `PollFn` |
| `rust-lang/rust` | `5c56312f346d7cc8209d9fc0fd660c72e6fc6950` | `compiler/rustc_middle/src/ty/{layout.rs:1091-1159, util.rs:1227-1278}`; `rustc_ty_utils/src/{abi.rs:342-409, layout.rs:726-730}` | `unpin = optimize && is_unpin && is_unsafe_unpin`, `NoAlias`/`Writable`/`NoFree`, `NicheOptimizations::Disabled` |
| `rust-lang/rust` | `5c56312f346d7cc8209d9fc0fd660c72e6fc6950` | `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:816-837`; `rustc_mir_transform/src/coroutine/mod.rs:567-596` | `Coroutine` special-cases only `Unpin`, keeps `UnsafeUnpin` auto-impl and `unpinned_local` `WithRetag::Yes` |
| `rust-lang/rfcs` | `f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` | `text/3467-unsafe-pinned.md:11-473` | Original `value: T` design, `duplicate`+`mem::swap`, `PollFn` rationale |
| `rust-lang/miri` | `7e679961edcfe2c526f19153bb8b03de346efa5c` | `src/borrow_tracker/tree_borrows/{mod.rs:126-221, perms.rs:10-396, tree.rs:671-727}`, `stacked_borrows/mod.rs:62-154` | `NewPermission::new` `return None`, `Permission` state machine, `perform_protector_end_access` |
| `tokio-rs/tokio` | `717c508f9e9ac4317665ff1eb30f29c139ea6363` | `tokio/src/util/linked_list.rs:74-137` | `Pointers<T>` (`UnsafeCell` + `PhantomPinned` + raw getters/setters) |
| Peer-Reviewed DOIs | `10.1145/3735592`, `10.1145/3371109`, `10.1145/3158154` | PLDI 2025, POPL 2020, POPL 2018 | Tree Borrows, Stacked Borrows, RustBelt foundations |

### Reproducible Execution Probe (`Python 3.13.15`)

Saving the following standalone script to `/tmp/probe_unsafepinned_tb.py` and executing `python3 /tmp/probe_unsafepinned_tb.py` (`exit 0`) verifies all Tree Borrows scenarios analyzed above:

```python
#!/usr/bin/env python3
"""Tree Borrows state-machine probe for UnsafePinned, Unpin vs. UnsafeUnpin,
and protector omission vs. retag omission (miri 7e679961edcfe2c5)."""

from dataclasses import dataclass


class AliasingUB(Exception):
    pass


@dataclass
class Node:
    tag: str
    parent: str | None
    state: str  # Cell | ReservedFrz | ReservedIM | Unique | Frozen | Disabled
    conflicted: bool = False
    protected: bool = False
    accessed: bool = False


class TBTree:
    def __init__(self) -> None:
        self.nodes = {"t0": Node("t0", None, "Unique", accessed=True)}

    def is_anc(self, anc: str, node: str) -> bool:
        cur: str | None = node
        while cur is not None:
            if cur == anc:
                return True
            cur = self.nodes[cur].parent
        return False

    def step(self, n: Node, kind: str, foreign: bool) -> None:
        st, p = n.state, n.protected
        if not foreign:
            if kind == "R":
                if st == "Disabled":
                    raise AliasingUB(f"ChildRead on Disabled {n.tag}")
                n.accessed = True
            elif st == "Cell":
                return
            elif st == "ReservedFrz" and n.conflicted and p:
                raise AliasingUB(f"ChildWrite on conflicted ReservedFrz {n.tag}")
            elif st in ("ReservedFrz", "ReservedIM", "Unique"):
                n.state, n.conflicted, n.accessed = "Unique", False, True
            else:
                raise AliasingUB(f"ChildWrite on {st} {n.tag}")
        elif kind == "R":
            if st == "ReservedFrz" and p:
                n.conflicted = True
            elif st == "Unique":
                if p:
                    n.state = "Disabled"
                    if n.accessed:
                        raise AliasingUB(f"ForeignRead disabled protected Unique {n.tag}")
                else:
                    n.state = "Frozen"
        elif st not in ("Cell", "ReservedIM"):
            ub = p and n.accessed and st != "Disabled"
            n.state, n.conflicted = "Disabled", False
            if ub:
                raise AliasingUB(f"ForeignWrite disabled protected {st} {n.tag}")

    def access(self, src: str, kind: str) -> None:
        for t, n in self.nodes.items():
            self.step(n, kind, not self.is_anc(t, src))

    def retag(self, par: str, new: str, mut: str, unpin: bool, unsafe_unpin: bool,
              frz: bool, fn_entry: bool, *, force_unprot_retag: bool = False) -> str:
        eff_unpin = unpin and unsafe_unpin
        if mut == "Mut" and not eff_unpin and not force_unprot_retag:
            return par  # Miri tree_borrows/mod.rs:151-155 omits retag
        prot = fn_entry and (not force_unprot_retag or eff_unpin)
        if mut == "Not":
            st, acc = ("Frozen", "R") if frz else ("Cell", None)
        else:
            st, acc = ("ReservedFrz" if (prot or frz) else "ReservedIM", "R")
        if acc:
            self.access(par, acc)
        self.nodes[new] = Node(new, par, st, protected=prot, accessed=bool(acc))
        return new

    def retag_cell(self, par: str, new: str) -> str:
        self.nodes[new] = Node(new, par, "Cell")
        return new

    def release(self, tag: str) -> None:
        n = self.nodes[tag]
        n.protected = False
        if n.accessed and n.state != "Cell":
            k = "W" if n.state == "Unique" else "R"
            for t, o in self.nodes.items():
                if not self.is_anc(tag, t):
                    self.step(o, k, not self.is_anc(t, tag))


def main() -> None:
    # A1: Unpin+UnsafeUnpin: poll#1 writes t1_ptr, poll#2 retag Read freezes t1_poll1/t1_ptr
    t = TBTree()
    p1 = t.retag("t0", "t1_poll1", "Mut", True, True, True, True)
    ptr = t.retag(p1, "t1_ptr", "Mut", True, True, True, False)
    t.access(ptr, "W")
    t.release(p1)
    t.retag("t0", "t2_poll2", "Mut", True, True, True, True)
    try:
        t.access(ptr, "W")
        raise AssertionError("expected A1 UB")
    except AliasingUB as e:
        print(f"[CASE_A1] unwrapped_unpin_reentry={e}")

    # A2: poll#1 stores t1_ptr (ReservedFrz); poll#2 writes t1_ptr -> kills protected t2_poll2
    t = TBTree()
    p1 = t.retag("t0", "t1_poll1", "Mut", True, True, True, True)
    ptr = t.retag(p1, "t1_ptr", "Mut", True, True, True, False)
    t.release(p1)
    t.retag("t0", "t2_poll2", "Mut", True, True, True, True)
    try:
        t.access(ptr, "W")
        raise AssertionError("expected A2 UB")
    except AliasingUB as e:
        print(f"[CASE_A2] unwrapped_unpin_protected={e}")

    # B1: Protector omitted, child retag kept: outer write disables t1_ptr
    t = TBTree()
    ptr = t.retag("t0", "t1_ptr", "Mut", False, False, False, True, force_unprot_retag=True)
    t.access(ptr, "W")
    p2 = t.retag("t0", "t2_poll2", "Mut", False, False, False, True, force_unprot_retag=True)
    t.access(p2, "W")
    try:
        t.access(ptr, "R")
        raise AssertionError("expected B1 UB")
    except AliasingUB as e:
        print(f"[CASE_B1] protector_omission_outer_write={e}")

    # B2: Protector omitted, child retag kept: outer read freezes t1_ptr
    t = TBTree()
    ptr = t.retag("t0", "t1_ptr", "Mut", False, False, False, True, force_unprot_retag=True)
    p2 = t.retag("t0", "t2_poll2", "Mut", False, False, False, True, force_unprot_retag=True)
    t.access(ptr, "W")
    t.access(p2, "R")
    try:
        t.access(ptr, "W")
        raise AssertionError("expected B2 UB")
    except AliasingUB as e:
        print(f"[CASE_B2] protector_omission_outer_read={e}")

    # C: Miri retag omission + PollFn (Unpin + !UnsafeUnpin)
    t = TBTree()
    a = t.retag("t0", "t1", "Mut", False, False, False, True)
    b = t.retag("t0", "t2", "Mut", True, False, False, True)
    assert a == "t0" and b == "t0"
    t.access(a, "W")
    t.access(b, "R")
    t.access(b, "W")
    print("[CASE_C] miri_retag_omission=OK; pollfn_unpin_only_conjunction=OK")

    # D: Per-byte UnsafePinned (Cell) + protected Unpin sibling
    d, s = TBTree(), TBTree()
    d_ptr, d_p2 = d.retag_cell("t0", "t1_ptr"), d.retag_cell("t0", "t2_poll2")
    s_p2 = s.retag("t0", "t2_poll2", "Mut", True, True, True, True)
    d.access(d_ptr, "W"); d.access(d_p2, "R"); d.access(d_p2, "W"); d.access(d_ptr, "W")
    s.access(s_p2, "W")
    try:
        s.access("t0", "R")
        raise AssertionError("expected D sibling noalias UB")
    except AliasingUB as e:
        print(f"[CASE_D] per_byte_cell_ok_sibling_noalias={e}")

    # E: Shared ref &UnsafePinned: RFC 3467 (Freeze -> UB) vs core (UnsafeCell -> Cell OK)
    for label, frz in (("rfc3467", True), ("core_unsafecell", False)):
        t = TBTree()
        tm = t.retag_cell("t0", "t_mut")
        ts = t.retag("t0", "t_shr", "Not", False, False, frz, False)
        t.access(tm, "W")
        try:
            t.access(ts, "R")
            res = "OK"
        except AliasingUB:
            res = "UB_ON_FROZEN_SHARED_REF"
        print(f"[CASE_E_{label}] {res}")


if __name__ == "__main__":
    main()
```

Observed output (`2026-11-20`, Python `3.13.15`):

```text
[CASE_A1] unwrapped_unpin_reentry=ChildWrite on Frozen t1_poll1
[CASE_A2] unwrapped_unpin_protected=ForeignWrite disabled protected ReservedFrz t2_poll2
[CASE_B1] protector_omission_outer_write=ChildRead on Disabled t1_ptr
[CASE_B2] protector_omission_outer_read=ChildWrite on Frozen t1_ptr
[CASE_C] miri_retag_omission=OK; pollfn_unpin_only_conjunction=OK
[CASE_D] per_byte_cell_ok_sibling_noalias=ForeignRead disabled protected Unique t2_poll2
[CASE_E_rfc3467] UB_ON_FROZEN_SHARED_REF
[CASE_E_core_unsafecell] OK
```

## Revalidation

To verify cheaply whether newer revisions of `rust-lang/rust` or `rust-lang/miri` alter these invariants:

1. **Diff `library/core/src/pin/unsafe_pinned.rs` and `library/core/src/marker.rs`:** Confirm `UnsafePinned<T>` still wraps `UnsafeCell<T>` (`!Freeze`), implements `!Unpin` and `!UnsafeUnpin`, exposes `get(&self) -> *mut T`, and `UnsafeUnpin` remains `unsafe auto trait`.
2. **Diff `rustc_middle/src/ty/layout.rs`, `rustc_ty_utils/src/{abi,layout}.rs`, and `rustc_mir_transform/src/coroutine/mod.rs`:** Inspect `ty_and_layout_pointee_info_at`, `arg_attrs_for_rust_scalar`, `NicheOptimizations::Disabled`, and coroutine lowering to detect when `UnsafePinned` replaces `!Unpin` in `unpin = optimize && is_unpin && is_unsafe_unpin`.
3. **Diff `src/borrow_tracker/tree_borrows/{mod,perms}.rs`:** Check whether `NewPermission::new` still returns `None` for `!ty_is_unpin` or implements per-byte `Permission::Cell` partitioning, and whether `compatible_with_protector` changes for `Cell`.
4. **Rerun `python3 /tmp/probe_unsafepinned_tb.py` (`< 0.1 s`)** after updating any transition rule.
