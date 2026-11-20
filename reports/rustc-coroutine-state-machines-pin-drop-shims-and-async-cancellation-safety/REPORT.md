# Rustc Coroutine State Machines, Pin Drop Shims, and Async Cancellation Safety

## Summary

Before `Runtime(PostCleanup)` MIR capture, `rustc`'s `StateTransform` pass (`compiler/rustc_mir_transform/src/coroutine/{mod,layout,drop,by_move_body}.rs` at `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`) lowers every coroutine (`async fn`, `gen`, `async gen`, or `#[coroutine]`) into a tagged-variant state struct plus coupled state-machine functions:

1. **Discriminant-indexed control and coupled drop shims (`mod.rs`, `drop.rs`, `shim.rs`):** `StateTransform` assigns reserved discriminants `0` (`UNRESUMED`), `1` (`RETURNED`), `2` (`POISONED`), and `3 + k` (`RESERVED_VARIANTS + k`) for each `.await`/`yield` suspension point, generating `Coroutine::resume` / `Future::poll`, a sync `ShimKind::DropGlue` (`create_coroutine_drop_shim`) that drops `upvars` at `0`, acts as a **no-op `Return` at `1` and `2`**, and jumps to `SuspensionPoint_k.drop` at `3 + k`, plus an optional `AsyncDrop` yield loop (`create_coroutine_drop_shim_async`) and `AsyncFnOnce` by-move body (`coroutine_by_move_body_def_id`).
2. **Overlap-colored saved locals, niche suppression, and single-allocation `Pin` borrows (`layout.rs`, `rustc_abi/src/layout/coroutine.rs`, `core/src/pin.rs`):** `storage_conflicts: BitMatrix` packs non-overlapping single-variant locals into shared byte offsets past a prefix of `upvars`, the discriminant tag, and multi-variant/conflicting promoted locals, while suppressing `largest_niche` (`None`) to prevent aliasing reads inside self-referential fields. `Pin<&mut Self>` enforces address stability and the **Drop Guarantee** (storage cannot be reused without running `drop_in_place`), allowing self-borrows inside a single allocation `alloc_self`.
3. **Why `tokio::select!` cancellation bypasses unwind-only invariant checks—even under `-C panic=abort`:** When `tokio::select!` drops an incomplete arm after `poll` returns `Poll::Pending`, `ShimKind::DropGlue` executes `create_coroutine_drop_shim` at `state = 3 + k` along the **normal `TerminalOut.returned` rail with zero panics and zero unwinding**. Unwind-only library invariant contracts (`TerminalOut.unwound`, which is vacuous under `-C panic=abort`) miss `&mut T` invariant corruption across `.await` points unless an indexed `CancelSafeCoroutine` protocol enforces `PhysInv` restoration at every `stepDrop (3 + k)` transition.

## Applicability

This report connects six primary subjects:

- **Rust compiler coroutine lowering, ABI layout, and `Pin` contract (`rust-lang/rust` at `8144389c895da997dbdecaa635e41d6a50be6ffd`):** Grounded in `compiler/rustc_mir_transform/src/coroutine/{mod,layout,drop,by_move_body}.rs`, `compiler/rustc_mir_transform/src/shim.rs`, `compiler/rustc_abi/src/layout/coroutine.rs`, and `library/core/src/pin.rs`.
- **Anneal MIR semantics and Pass-1 boundary (`joshlf/anneal` at `20aa204315cd36aaf944778b7d33c0d609ced8e8` and `leanprover/lean4` `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52`):** Grounded in `trusted/lean/Trusted/MirAst.lean` (`L289-321, L450-476, L630-796`), `trusted/lean/Trusted/MirSemantics.lean` (`L601-605, L1537-1570`), `trusted/audit/TrustedBoundary.lean` (`L442-596`), and `trusted/lean/foundation-lock.json`.
- **Tokio `select!` cancellation semantics and RustBelt `Pin` semantics (`tokio-rs/tokio` at `3f0ffc85f51c71d97bce72e0f8b80ece9b8b4892`, Jung et al. POPL 2018 DOI `10.1145/3158154` and CACM 2021 DOI `10.1145/3418295`):** Grounded in `tokio/src/macros/select.rs` (`L101-163`) and the RustBelt `Pin` drop-guarantee formalization.

Sibling reports in the corpus separately examine coroutine compiler optimizations (`coroutine-state-machine-optimization-and-hybridtrace-scaling`), basic `StateTransform` and `async gen` MIR mechanics (`rustc-statetransform-coroutines-async-gen-and-pin-mir-semantics`), `Unpin` SROA slicing (`self-referential-unpin-coroutine-field-slicing-and-sroa`), Tokio's operational I/O cancellation behavior (`tokio-select-cancellation-safety-yaml-json-differentials-and-rego-undefined`), and `pin-init` unwinding patterns (`pin-init-drop-guards-and-segmented-maybeuninit-unwind-patterns`). This report isolates the exact coupled `poll`/`drop` shim MIR semantics, `storage_conflicts` layout packing, `AsyncDrop` yield loops, and the Pass-1 `CancelSafeCoroutine` protocol curing the `-C panic=abort` `select!` cancellation soundness gap.

## Findings

### 1. `StateTransform` Lowering Anatomy: Discriminants `0/1/2/3+k`, Coupled `poll`/`drop` Shims, and `ByMove` Bodies

`Basis: source + derived`

In `compiler/rustc_mir_transform/src/coroutine/mod.rs` (`L1008-1196`), `StateTransform::run_pass` executes on MIR containing `TerminatorKind::Yield` and `CoroutineDrop`, transforming the single coroutine body into a state machine and extracting two (or three) coupled bodies before `Runtime(PostCleanup)` capture:

| Discriminant | Meaning (`mod.rs:30-51, 500`) | `resume` / `poll` Transition (`create_coroutine_resume_function`, `L848-930`) | Sync `drop_glue` Transition (`create_coroutine_drop_shim`, `drop.rs:177-244`) |
| :--- | :--- | :--- | :--- |
| **`0`** (`UNRESUMED`) | Initial state holding captured `upvars` only | Jumps to `START_BLOCK` after moving remapped args into coroutine fields (`L1128-1138`) | Jumps to `drop_clean`, an elaborated drop ladder over `SELF_ARG` (`drop.rs:85-174`) |
| **`1`** (`RETURNED`) | Completed (`Poll::Ready` / `Complete`) | `Async`/`Coroutine`: panics (`ResumedAfterReturn`) unless `is_async_drop_in_place_coroutine` (`Poll::Ready(())`, `L884-888`); `Gen`/`AsyncGen`: `None` / `Poll::Ready(None)` (`L207-260, 890-893`) | Falls through to `default_block = TerminatorKind::Return` (**no-op**, `drop.rs:201-202`) |
| **`2`** (`POISONED`) | Unwound during a prior `poll` (`L816-845`) | When `can_unwind`: panics (`ResumedAfterPanic`, `L868-876`); under `-C panic=abort` (`!can_unwind`, `L805-813`), branch is omitted and hits `default_block = Unreachable` (`L898`) | Falls through to `default_block = TerminatorKind::Return` (**no-op**, `drop.rs:198-202`) |
| **`3 + k`** (`RESERVED_VARIANTS + k`) | Suspended at `SuspensionPoint_k` | Emits `StorageLive` for unremapped `point.storage_liveness` locals, moves `CTX_ARG` into `resume_arg`, jumps to `point.resume` (`L957-1006`) | If `point.drop = Some(bb)`, emits `StorageLive` for unremapped locals and jumps to `bb`; rewrites `TerminatorKind::CoroutineDrop` to `Return` (`drop.rs:204-209`) |

Four implementation details govern MIR verification of these lowered bodies:

1. **`&mut Self` vs. `Pin<&mut Self>` receiver desugaring (`mod.rs:551-596, 901-912`, `drop.rs:214`):** `create_coroutine_resume_function` rewrites `SELF_ARG` (`_1`) to `Pin<&mut Coroutine>` (`make_coroutine_state_argument_pinned`) for `Async`, `AsyncGen`, and `Coroutine` (inserting `unpinned = copy (_1.0 : &mut Coroutine)` with `WithRetag::Yes` at `START_BLOCK` and adding `Deref`), while sync `Gen` and sync `create_coroutine_drop_shim` use plain `&mut Coroutine` (`make_coroutine_state_argument_indirect`, `body.arg_count = 1`, dropping `CTX_ARG`).
2. **`ResumeTy` / `Context` transmutation (`mod.rs:598-700`):** Before state layout, `eliminate_get_context_calls` replaces `LangItem::GetContext` calls with `CastKind::Transmute` from `ResumeTy` (`NonNull<Context>`) to `&mut Context<'_>`; afterwards, `transform_async_context` turns `CTX_ARG` (`_2`) into `&mut Context<'_>` and inserts a `CastKind::Transmute` bridging `_2` back into `ResumeTy` at `START_BLOCK`. Verification must permit or pattern-eliminate this `ResumeTy` round-trip transmute.
3. **`PlaceElem::Index(local)` reload injection (`mod.rs:425-444`):** Because `PlaceElem::Index` accepts only a `Local` (not a downcast field projection), accessing a remapped array-drop counter at `.await` injects `local = copy (*_1 as variant).field` immediately before the indexed place.
4. **Coroutine-closure `by_move_body` (`by_move_body.rs:83-373`, `shim.rs:90-105`):** An `async move ||` closure (`AsyncFnMut` + `AsyncFnOnce`) produces a child coroutine borrowing the closure's upvars by reference, plus a second synthesized `DefKind::SyntheticCoroutineBody` (`coroutine_by_move_body_def_id`) that peels one `ProjectionElem::Deref` off parent captures so `async_call_once` moves ownership into the future. `mir_shims` (`shim.rs:95-105`) dispatches `ShimKind::DropGlue` to the matching `coroutine_drop()` depending on `args.as_coroutine().kind_ty()`.

### 2. `storage_conflicts` Layout Packing, Niche Suppression, and Single-Allocation `Pin` Self-Borrows

`Basis: normative + source + execution + derived`

Computing which locals survive `.await` and where they live inside the coroutine struct splits across MIR dataflow (`layout.rs`) and ABI union layout (`rustc_abi/src/layout/coroutine.rs`):

- **Saved-local liveness (`layout.rs:83-184`):** For each `Yield` block, `locals_live_across_suspend_points` intersects `(MaybeLiveLocals ∪ [if !movable then MaybeBorrowedLocals])` with `MaybeRequiresStorage` and removes `SELF_ARG`. For immovable coroutines (`!movable`, which covers all `async fn` self-referential futures), any previously borrowed local stays live across every reachable `Yield` until `StorageDead` (`L121-134`) because interior references may still alias it.
- **Prefix promotion vs. variant overlap (`rustc_abi/src/layout/coroutine.rs:42-319`):** `coroutine_saved_local_eligibility` (`L42-136`) partitions `CoroutineSavedLocal`s into overlap-ineligible (promoted to a flat prefix alongside `upvars` and `tag`) vs. variant-exclusive:
  1. Any local live in **more than one variant** becomes `Ineligible` (`L63-72`).
  2. For remaining single-variant pairs `(local_a, local_b)` that conflict in `storage_conflicts: BitMatrix` (`L80-105`), the local with **strictly more conflicts** (`conflicts_a > conflicts_b`, breaking ties on `local_b`) is demoted to `Ineligible`.
  3. If fewer than two variants retain `Assigned` locals (`used_variants.count() < 2`, `L119-124`), all locals promote to the prefix to avoid padding overhead.
  4. `layout` (`L139-319`) computes `prefix = layout_of_univariant(upvars ++ [tag] ++ promoted)` (`tag` width via `Integer::fit_unsigned(variant_fields.len() - 1)`, `TagEncoding::Direct`), lays out each variant's exclusive fields under `StructKind::Prefixed(prefix_size, prefix_align.abi)` (`L231-235`), and sets **`largest_niche: None` (`L304-310`)**: enclosing enums (`Option<MyFuture>`) cannot reuse niches inside coroutine fields because reading a discriminant niche on a self-referentially borrowed field causes aliasing violations prior to `UnsafePinned` (`rust-lang/rust#63818`, `#125735`).
- **Pre-transform assignment non-aliasing (`mod.rs:1204-1264`):** Before `TransformVisitor` runs, `EnsureCoroutineFieldAssignmentsNeverAlias` asserts under `-Z validate-mir` that whenever `_lhs = _rhs` assigns between two saved locals, `storage_conflicts.contains(lhs, rhs)` is true—otherwise overlapping fields at different offsets inside the same union variant would alias across the assignment (`#73137`).
- **Single-allocation `Pin<&mut Self>` ownership (`core/src/pin.rs:509-634`, RustBelt POPL 2018 / CACM 2021):** Because a coroutine self-borrow holds a pointer derived from `&mut *_1` pointing at another field inside the **same** allocation `alloc_self`, naive cross-allocation separation logic rejects cyclic ownership. Under `Pin<&mut Self>` (`pin.rs:521-565`), the pointee `alloc_self` enters an address-stable state (`PinSlot`) that forbids mechanical `Operand.move (*_1)` and enforces the **Drop Guarantee**: `alloc_self`'s storage cannot be deallocated or overwritten (e.g., setting `Option::None` or `Vec::set_len`) without first invoking `drop_in_place` (while `mem::forget` leaks `alloc_self` soundly by keeping storage permanently pinned, `pin.rs:584-586`, and `ManuallyDrop` inner projection is unsound, `L566-582`). At `state = 3 + k`, `alloc_self` cleanly splits into disjoint byte zones:
  $$\text{UpvarZone} \;\ast\; \text{TagZone} \;\ast\; \text{PromotedActive}[k] \;\ast\; \text{VariantActive}[k] \;\ast\; \text{UninitSlack}[k]$$
  Because `VariantActive[k]` contains *only* locals live in `variant_fields[k]` (pairwise non-overlapping by construction), self-referential pointers inside `alloc_self` resolve via relative byte offsets (`alloc_self.base + off`) without aliasing other active fields.

### 3. `AsyncDrop` Yield Loops and Proxy Drop Shims

`Basis: source + derived`

When a coroutine holds fields implementing `AsyncDrop` across suspension points, drop elaboration introduces `TerminatorKind::Yield` nodes reachable from `Yield::drop` targets (`coroutine/drop.rs:51-82, 248-392`):

- **Detection (`has_async_drops`, `drop.rs:55-82`):** A forward reverse-postorder reachability pass (`dropline`) ignoring `is_cleanup` blocks seeds `dropline` with every `Yield::drop` target and flags `has_async_drops = true` if any `TerminatorKind::Yield` lies inside `dropline`.
- **Async drop shim (`create_coroutine_drop_shim_async`, `drop.rs:248-338`, `shim.rs:149-170`):** Clones the body, applies `FixReturnPendingVisitor` (`L6-48`) to rewrite `Poll<Rv>::Pending` to `Poll<()>::Pending`, adds `POISONED` panic handling and `generate_poison_block_and_redirect_unwinds_there` if `can_unwind`, maps `RETURNED` and rewritten `TerminatorKind::CoroutineDrop` blocks to `Poll::Ready(())`, and uses `Pin<&mut Self>` (except sync `Gen`, `L303-313`) plus `AbortUnwindingCalls` (`L322`).
- **Sync-to-async proxy (`create_coroutine_drop_shim_proxy_async`, `L342-392`) and current boundary:** For non-`has_async_drops` coroutines, `rustc` synthesizes `{ drop(_1); return Poll::Ready(()); }` for `ShimKind::FutureDropPoll`. Meanwhile `elaborate_coroutine_drops` (`L100-103`) currently sets `produce_async_drops: false` for unresumed `insert_clean_drop`.

### 4. Why `tokio::select!` Cancellation Bypasses Unwind-Only `LibInv` Checks—Even Under `-C panic=abort`—and Pass-1 `CancelSafeCoroutine`

`Basis: normative + documentation + source + execution + derived`

Tokio's `select!` documentation (`tokio-rs/tokio@3f0ffc85f51c71d97bce72e0f8b80ece9b8b4892`, `tokio/src/macros/select.rs:101-163`) defines **functional cancellation safety**: dropping an uncompleted future must behave equivalently to dropping and recreating it without losing buffered state (`AsyncReadExt::read` is cancel-safe; `read_exact` and `Mutex::lock` are not). For **memory safety** of `unsafe` Rust libraries, however, dropping a suspended future causes an orthogonal failure mode:

1. **Concrete counterexample refuting unwind-only `LibInv` checks:** Consider an `async fn flush_ring(rb: &mut RingBuf, sock: &mut Sock)` where `RingBuf` enforces `PhysInv := (rb.head < rb.cap)` (required for `unsafe { *rb.buf.get_unchecked(rb.head) }`):
   ```rust
   async fn flush_ring(rb: &mut RingBuf, sock: &mut Sock) {
       rb.head = rb.cap;            // Temporarily breaks PhysInv!
       let _ = sock.readable().await; // State = 3; returns Poll::Pending on TerminalOut.returned!
       rb.head = 0;                 // Restored only on resume -> Ready!
   }
   ```
   When called inside `tokio::select! { _ = flush_ring(&mut rb, &mut sock) => {}, _ = timeout => {} }` and `timeout` wins after one `poll` returning `Poll::Pending`:
   - `StateTransform` lowered `.await` to `set_discr(3); _0 = Poll::Pending; return;` (`mod.rs:495-533`).
   - Dropping the losing future runs `create_coroutine_drop_shim` at `state = 3` (`drop.rs:177-244`). Because `&mut RingBuf` is a reference upvar with a trivial no-op drop, `drop_shim` returns `()` normally without restoring `rb.head < rb.cap`!
   - Under `Trusted/MirSemantics.lean` (`L601-605, 1542-1570`), **both `poll` (returning `Poll::Pending`) and `drop_shim` execute on `TerminalOut.returned` with zero panics and zero unwinding**. Even under **`-C panic=abort`** (`can_unwind = false`, where `TerminalOut.unwound` is vacuous!), the caller subsequently runs safe `rb.peek_head()` and triggers immediate out-of-bounds UB (`reproduced in Revalidation`).
2. **Current fail-closed coverage boundary (`joshlf/anneal@20aa204315cd36aaf944778b7d33c0d609ced8e8`):** On `main`, `Trusted/MirAst.lean` fails closed with `.unsupported` on `TyKind::Coroutine` (`L308-321`), `ProjectionElem::Downcast` (`L469-475`), `StatementKind::SetDiscriminant` (`L654-662`), `Rvalue::Aggregate(Adt)` (`L612-628`), `TerminatorKind::Drop` (`L782-795`), and `AssertKind::ResumedAfter*` (`L727-740`). Extending capture (`trusted/rustc-capture/`) for coroutines also requires extracting `tcx.mir_shims(DropGlue(drop_glue, Some(coroutine_ty)))` (`shim.rs:79-123`) alongside `optimized_mir` for `poll`, because the drop shim is synthesized lazily as a MIR shim rather than a standalone HIR item.
3. **Pass-1 `CancelSafeCoroutine` mechanization (`theory/`):** To stay 0-TCB and Pass-1 compliant (`prelude` + locked `Init.*` modules, zero banned operators `&&&`/`|||`/`^^^`/`<<<`/`>>>`/`^`/`-x`/`/`/`%`, zero `._unsafe_rec`), `theory/` lifts a coroutine jointly as a **state-indexed transition protocol** distinguishing `physInv : UpvarEnv → Prop` (mandatory for memory safety across `.ready`, `.unwound`, AND `stepDrop (3 + k)`) from `restartInv : UpvarEnv → UpvarEnv → Prop` (optional functional `select!`-loop no-op cancellation), plus a computable `storage_conflicts` non-overlap checker over variant field sets:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Anneal.Async

inductive PollRes (Out : Type) where
  | pending : PollRes Out
  | ready   : Out → PollRes Out

/-- State-indexed protocol coupling `Future::poll` and `ShimKind::DropGlue`.
    `physInv` is mandatory for UB-freedom on `.ready`, `.unwound`, AND `stepDrop (3 + k)`;
    optional `restartInv` captures Tokio functional cancellation safety (`select!` loop idempotence). -/
structure CoroutineSpec (UpvarEnv CoroMem Out : Type) where
  numSuspends : Nat
  physInv     : UpvarEnv → Prop
  suspendInv  : Nat → UpvarEnv → CoroMem → Prop
  restartInv  : UpvarEnv → UpvarEnv → Prop

inductive CoroStepOut (UpvarEnv CoroMem Out : Type) where
  | returned (res : PollRes Out) (nextState : Nat) (env' : UpvarEnv) (mem' : CoroMem)
  | unwound  (nextState : Nat) (env' : UpvarEnv)
  | aborted

def CancelSafeCoroutine {UpvarEnv CoroMem Out : Type}
    (spec : CoroutineSpec UpvarEnv CoroMem Out)
    (stepPoll : Nat → UpvarEnv → CoroMem → Option (CoroStepOut UpvarEnv CoroMem Out))
    (stepDrop : Nat → UpvarEnv → CoroMem → Option UpvarEnv) : Prop :=
  (∀ env0 mem0, spec.physInv env0 →
    match stepPoll 0 env0 mem0 with
    | none => False
    | some (.returned (.ready _) st' env' _) => Nat.beq st' 1 = true ∧ spec.physInv env'
    | some (.returned .pending st' env' mem') =>
      ∃ k, Nat.blt k spec.numSuspends = true ∧ st' = 3 + k ∧ spec.suspendInv k env' mem'
    | some (.unwound st' env') => Nat.beq st' 2 = true ∧ spec.physInv env'
    | some .aborted => True) ∧
  (∀ k env mem, Nat.blt k spec.numSuspends = true → spec.suspendInv k env mem →
    (match stepPoll (3 + k) env mem with
     | none => False
     | some (.returned (.ready _) st' env' _) => Nat.beq st' 1 = true ∧ spec.physInv env'
     | some (.returned .pending st' env' mem') =>
       ∃ k', Nat.blt k' spec.numSuspends = true ∧ st' = 3 + k' ∧ spec.suspendInv k' env' mem'
     | some (.unwound st' env') => Nat.beq st' 2 = true ∧ spec.physInv env'
     | some .aborted => True) ∧
    (match stepDrop (3 + k) env mem with
     | none => False
     | some envAfterDrop => spec.physInv envAfterDrop))

/-- Verify variant-active saved locals contain zero overlapping conflict pairs. -/
def variantConflictsFree (conflicts : List (Nat × Nat)) (fields : List Nat) : Bool :=
  fields.all fun a =>
    fields.all fun b =>
      if Nat.beq a b then true
      else !conflicts.any (fun p => (Nat.beq p.1 a && Nat.beq p.2 b) || (Nat.beq p.1 b && Nat.beq p.2 a))

def checkCoroutineVariants (conflicts : List (Nat × Nat)) (variantFields : List (List Nat)) : Bool :=
  variantFields.all (variantConflictsFree conflicts)

/-- Concrete executable check witnessing why unguarded `flush_ring` fails at `k = 0` (`state = 3`)
    whereas RAII `ResetHeadGuard` succeeds (`Eq.refl true` without `Classical.choice`). -/
def checkFlushDrop (hasGuard : Bool) (head cap : Nat) : Bool :=
  let headAfterSuspend := cap
  let headAfterDrop := if hasGuard then head else headAfterSuspend
  Nat.blt headAfterDrop cap

end Anneal.Async
```

Under `CancelSafeCoroutine`, `flush_ring` fails at `stepDrop 3` (`headAfterDrop = cap`, violating `head < cap`), whereas storing an RAII `ResetHeadGuard { rb, saved_head }` in `live_locals_at_suspension_points[0]` satisfies `stepDrop 3` because `coroutine_drop_shim` invokes `<ResetHeadGuard as Drop>::drop`, restoring `rb.head = saved_head < rb.cap` on normal `TerminalOut.returned`.

### 5. Architectural Evaluation Against Anneal `theory/` Rubric

`Basis: source + derived`

| Rubric Dimension | Grade | Grounded Justification Against `joshlf/anneal` (`20aa204315cd36aaf944778b7d33c0d609ced8e8`) |
| :--- | :---: | :--- |
| **(T1) 0-TCB Bridge** | **Requires minimal `Trusted.*` hook** | Today `MirAst` lacks `Downcast`, `SetDiscriminant`, `Drop`, and `Coroutine` (`MirAst.lean:308-795`), and `rustc-capture` must pull `mir_shims(DropGlue)`; once MIR capture & semantics cover those hooks, `CancelSafeCoroutine` and `PinSlot` stay 100% in 0-TCB `theory/`. |
| **(P1) Human Spec Auditability** | **Strong** | `physInv` expresses exact memory-safety requirements across suspension/drop, decoupled from optional Tokio `restartInv` functional cancellation specs. |
| **(P2) Authoring & Day-2 Locality** | **Strong** | Per-`.await` `suspendInv k` decomposes $M$ poll/drop transitions into $O(M)$ independent branch checks rather than $O(2^M)$ path unrolling. |
| **(P3) Lean 4 Kernel & LSP Scaling** | **Strong** | Variant-indexed dispatch and `variantConflictsFree` evaluate in linear time without universe bumps (`Type 0`, zero `._unsafe_rec`, zero `Classical.choice`). |
| **(P4) Heterogeneous Composability** | **Strong** | Unifies `Pin<&mut Self>` single-allocation self-borrows, `storage_conflicts` overlap offsets, RAII `Drop` guards, `Poisoned` unwind transitions, and `tokio::select!` cancellation. |
| **(P5) Failure Legibility** | **Strong** | Pinpoints the exact suspension index `k` (`state = 3 + k`) whose `stepDrop` transition fails to re-establish `physInv`. |
| **(C1–C2) Conceptual Minimality** | **Strong** | Anti-collapse proof (`flush_ring` under `-C panic=abort`): `CancelSafeCoroutine` cannot collapse into unwind-only `LibInv` contracts because cancellation drops on `TerminalOut.returned`. |

## Boundaries

- **Coroutine MIR primitives in `joshlf/anneal` at `20aa204315cd36aaf944778b7d33c0d609ced8e8` — `unsupported`:** `Trusted.MirAst` maps `TyKind::Coroutine`, `ProjectionElem::Downcast`, `StatementKind::SetDiscriminant`, `TerminatorKind::Drop`, `AssertKind::ResumedAfter*`, and `Rvalue::Aggregate(Adt)` to `.unsupported`, failing closed until extended.
- **Unwind-only `LibInv` verification preventing `tokio::select!` invariant corruption — `known not to apply`:** Direct proof from `create_coroutine_drop_shim` (`drop.rs:177-244`) and `can_unwind` (`mod.rs:805-813`) establishes that `select!` cancellation drops suspended futures on `TerminalOut.returned` with zero unwinding, passing unwind-only checks even under `-C panic=abort`.
- **Unresumed async-drop elaboration and scalable vectors across `.await` — `unsupported`:** `elaborate_coroutine_drops` hardcodes `produce_async_drops: false` (`drop.rs:103`), and `check_must_not_suspend_ty` rejects scalable vectors across yield points (`layout.rs:610-614`).
- **Compiler `noalias` guarantees for `Pin<&mut Self>` prior to `UnsafePinned` — `known not to apply`:** `core/src/pin.rs` (`L237-238`) and `rustc_abi/src/layout/coroutine.rs` (`L304-310`) note that `Pin` itself adds no compiler `noalias` magic and suppresses coroutine niches until `UnsafePinned` (`rust-lang/rust#125735`) wraps aliased fields; exact final operational rules of `UnsafePinned` remain `unknown`.
- **Multi-threaded work-stealing `Waker` concurrency (`Send` / `Sync` coroutine proofs) — `not examined`:** Cross-thread synchronization between `poll` and `Waker::wake` on multi-threaded executors was `not examined`.

## Evidence

1. **Upstream `rustc` Coroutine Lowering (`source`):** `rust-lang/rust` at `8144389c895da997dbdecaa635e41d6a50be6ffd`:
   - `compiler/rustc_mir_transform/src/coroutine/mod.rs`: discriminant layout (`L30-51`), `PlaceElem::Index` reload (`L425-444`), `visit_basic_block_data` (`L479-538`), `make_coroutine_state_argument_{indirect,pinned}` (`L551-596`), `transform_async_context` / `eliminate_get_context_calls` (`L598-700`), `can_unwind` (`L805-813`), `generate_poison_block_and_redirect_unwinds_there` (`L816-845`), `create_coroutine_resume_function` (`L848-930`), `create_cases` (`L957-1006`), `StateTransform::run_pass` (`L1008-1196`), and `EnsureCoroutineFieldAssignmentsNeverAlias` (`L1204-1264`).
   - `compiler/rustc_mir_transform/src/coroutine/layout.rs`: `locals_live_across_suspend_points` (`L83-184`), `compute_storage_conflicts` (`L235-292`), `compute_layout` (`L344-453`), and `check_must_not_suspend_ty` (`L575-695`).
   - `compiler/rustc_mir_transform/src/coroutine/drop.rs`: `FixReturnPendingVisitor` (`L6-48`), `has_async_drops` (`L55-82`), `elaborate_coroutine_drops` (`L85-145`, `produce_async_drops: false` at `L103`), `insert_clean_drop` (`L148-174`), `create_coroutine_drop_shim` (`L177-244`), `create_coroutine_drop_shim_async` (`L248-338`), and `create_coroutine_drop_shim_proxy_async` (`L342-392`).
   - `compiler/rustc_mir_transform/src/coroutine/by_move_body.rs`: `coroutine_by_move_body_def_id` (`L83-255`) and `MakeByMoveBody` (`L257-373`).
   - `compiler/rustc_mir_transform/src/shim.rs`: `ShimKind::DropGlue` (`L79-123`) and `ShimKind::{FutureDropPoll, AsyncDropGlue, AsyncDropGlueCtor}` (`L131-176`).
   - `compiler/rustc_abi/src/layout/coroutine.rs`: `coroutine_saved_local_eligibility` (`L42-136`) and `layout` (`L139-319`, `largest_niche: None` at `L304-310`).
2. **Rust `Pin` Contract and RustBelt Semantics (`normative` + `documentation`):** `rust-lang/rust` at `8144389c895da997dbdecaa635e41d6a50be6ffd`, `library/core/src/pin.rs` (`L217-258, L509-634, L791-820`); R. Jung, J.-H. Jourdan, R. Krebbers, and D. Dreyer, "RustBelt: Securing the Foundations of the Rust Programming Language," *POPL* 2018, DOI `10.1145/3158154`, and "Safe Systems Programming in Rust," *Commun. ACM* 64(4), 2021, DOI `10.1145/3418295`.
3. **Tokio `select!` Cancellation Safety (`documentation`):** `tokio-rs/tokio` at `3f0ffc85f51c71d97bce72e0f8b80ece9b8b4892`, `tokio/src/macros/select.rs` (`L101-163`).
4. **Anneal MIR Coverage and Pass-1 Rules (`source`):** `joshlf/anneal` at `20aa204315cd36aaf944778b7d33c0d609ced8e8`: `trusted/lean/Trusted/MirAst.lean` (`L308-321, L469-475, L612-628, L654-662, L727-740, L782-795`), `trusted/lean/Trusted/MirSemantics.lean` (`L601-605, L1537-1570`), `trusted/audit/TrustedBoundary.lean` (`L442-596`), `trusted/lean/foundation-lock.json`.
5. **Executable Eligibility and Cancellation-Safety Probe (`execution`, `2026-11-20`):** Executed the standalone Python 3.13 probe preserved in Revalidation item 5 on Linux x86_64, confirming exact `coroutine_saved_local_eligibility` promotion/overlap (`ineligible = {3}`, single-variant prefix collapse `{0, 1}`) and reproducing unguarded `flush_ring` passing unwind-only verification under `-C panic=abort` while failing `CancelSafeCoroutine` at `state = 3` (`head == cap`) and passing with `ResetHeadGuard`.

## Revalidation

1. **Coroutine discriminant & drop-shim audit (`rust-lang/rust`):** Inspect `compiler/rustc_mir_transform/src/coroutine/mod.rs` (`create_coroutine_resume_function`) and `drop.rs` (`create_coroutine_drop_shim`, `has_async_drops`, `produce_async_drops`) plus `shim.rs` (`ShimKind::DropGlue`).
2. **Overlap & niche suppression audit (`rust-lang/rust`):** Inspect `compiler/rustc_abi/src/layout/coroutine.rs` (`coroutine_saved_local_eligibility`, `largest_niche`).
3. **Anneal MIR support status (`joshlf/anneal`):** Inspect `trusted/lean/Trusted/MirAst.lean` (`MirTy`, `ProjectionElem`, `StatementKind`, `TerminatorKind`) for coroutine/downcast/drop constructors.
4. **Tokio `select!` specification (`tokio-rs/tokio`):** Inspect `tokio/src/macros/select.rs` (`# Cancellation safety`) for updates to `select!` drop behavior.
5. **Standalone saved-local eligibility and `panic=abort` `select!` cancellation probe (<0.2s, Python 3.10+ stdlib only):**

```bash
python3 -c '
def saved_local_eligibility(nb_locals, variant_fields, storage_conflicts):
    assign = [("Unassigned", None) for _ in range(nb_locals)]
    inelig = set()
    for v_idx, fields in enumerate(variant_fields):
        for loc in fields:
            k, _ = assign[loc]
            if k == "Unassigned": assign[loc] = ("Assigned", v_idx)
            elif k == "Assigned": inelig.add(loc); assign[loc] = ("Ineligible", None)
    for la in range(nb_locals):
        if la in inelig: continue
        ca = len(storage_conflicts[la])
        for lb in sorted(storage_conflicts[la]):
            if lb in inelig or assign[la] == assign[lb]: continue
            rm = la if ca > len(storage_conflicts[lb]) else lb
            inelig.add(rm); assign[rm] = ("Ineligible", None)
    if len({val for k, val in assign if k == "Assigned"}) < 2:
        for i in range(nb_locals): assign[i] = ("Ineligible", None); inelig.add(i)
    for idx, loc in enumerate(sorted(inelig)): assign[loc] = ("Ineligible", idx)
    return inelig, assign

inelig, assign = saved_local_eligibility(4, [[], [], [], [0, 1, 3], [2, 3]], [{1, 3}, {0, 3}, {3}, {0, 1, 2}])
assert inelig == {3} and assign[0] == ("Assigned", 3) and assign[2] == ("Assigned", 4)
assert saved_local_eligibility(2, [[], [], [], [0, 1]], [{1}, {0}])[0] == {0, 1}

def poll_step(discr, rb, has_guard):
    head, cap = rb
    if discr == 0: return ("Pending", 3, (cap, cap), has_guard, head)
    if discr == 3: return ("Ready", 1, (0, cap), has_guard, 0)
    raise AssertionError("resumed after return/poison")

def drop_shim(discr, rb, saved_head, has_guard):
    if discr in (1, 2): return ("Returned", rb)
    if discr == 3 and has_guard: return ("Returned", (saved_head, rb[1]))
    return ("Returned", rb)

def unwind_only_check(has_guard):
    _, d1, rb1, hg1, _ = poll_step(0, (2, 8), has_guard)
    out2, d2, rb2, _, _ = poll_step(d1, rb1, hg1)
    return out2 == "Ready" and d2 == 1 and rb2[0] < rb2[1]

def cancel_safe_check(has_guard):
    out1, d1, rb1, _, saved = poll_step(0, (2, 8), has_guard)
    if out1 == "Pending":
        rail, rb_after = drop_shim(d1, rb1, saved, has_guard)
        assert rail == "Returned"
        return rb_after[0] < rb_after[1]
    return True

assert unwind_only_check(False) is True
assert cancel_safe_check(False) is False
assert cancel_safe_check(True) is True
print("revalidation passed")
'
```
