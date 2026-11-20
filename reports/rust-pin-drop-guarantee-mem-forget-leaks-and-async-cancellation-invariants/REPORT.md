# Rust's `Pin` Drop Guarantee, `mem::forget` Leaks, Async Cancellation Invariants, and `!Unpin` Retagging in Tree Borrows

## Summary

Rust's asynchronous safety contract rests on the interaction of three distinct language mechanisms: **safe destructor skipping (`RFC 1066`, `core::mem::forget`)**, **`Pin<Ptr>`'s conditional `Drop` guarantee (`RFC 2349`)**, and **`!Unpin` / `UnsafePinned` aliasing relaxation (`RFC 3467`, Tree Borrows)**:

1. **Why `core::mem::forget(Box::pin(fut))` Legally Skips `Future::drop` Without Violating `Pin`'s Drop Guarantee:**
   - Following the 2015 `thread::scoped::JoinGuard` soundness vulnerability (`rust-lang/rust#24292`), **RFC 1066** removed `unsafe` from `core::mem::forget` (`pub const fn forget<T>(t: T)` carries **no** `'static` or `Unpin` bound), codifying that safe Rust can skip any destructor via `mem::forget` or `Rc`/`Arc` reference cycles.
   - **RFC 2349** (`core::pin::Pin`) defines the **`Drop` guarantee** on `!Unpin` pointees: once pinned at address $p$, **the backing storage at $p$ must not be invalidated, deallocated, or repurposed until `<T as Drop>::drop` (via `drop_in_place`) returns or unwinds**.
   - Crucially, **`Pin`'s drop guarantee is a material implication ($\text{StorageInvalidated}(p) \implies \text{DropRanBefore}(p)$), NOT a liveness promise ($\text{DropRuns}(p)$)**! Calling `core::mem::forget(Box::pin(fut))` permanently leaks the `Box`'s heap block: because the heap bytes at $p$ are *never* freed or reused, $\text{StorageInvalidated}(p)$ is `false` and the drop guarantee holds vacuously (`library/core/src/pin.rs:584-586`). Conversely, stack pinning via `core::pin::pin!(fut)` (`pin.rs:2145-2192`) binds an unnameable `super let mut pinned: PinMacroHelper<_>` local on the stack frame and yields only `Pin<&mut T>`: calling `mem::forget(p)` forgets only the reference while scope exit still runs `PinMacroHelper::drop` before stack storage reuse.
2. **Separating `physInv` from `cancelInv` Across `.await` Suspension Points:**
   - In synchronous Rust (`slice::sort`, `BinaryHeap`, or `std::thread::scope`), an active stack frame cannot be forgotten by its callee, so an internal RAII `Drop` guard runs on every normal return or unwind.
   - In `async` Rust, `StateTransform` reifies the suspended stack frame into a first-class `CoroutineEnv<'a>` value! A `#![forbid(unsafe_code)]` caller can construct `let mut fut = Box::pin(drain_batch(&mut rb, &mut io));`, poll it once to `Poll::Pending` (a normal `Return` at MIR level), and call **`core::mem::forget(fut)`**—ending lifetime `'a` of `&'a mut rb` **without running `coroutine_drop_shim` or any RAII guard stored inside the future**!
   - Formal coroutine specifications must therefore separate:
     - **`physInv` (Memory-Safety Invariant):** MUST hold on all borrowed upvars and shared memory at **every** `Poll::Pending` yield, every `Poll::Ready` return, and every unwind exit (using `Vec::Drain`-style pre-poising / *leak amplification* rather than relying on `Drop`); and
     - **`cancelInv` (Logical / Resource Cancellation Invariant):** Restored by `coroutine_drop_shim` (or multi-poll `create_coroutine_drop_shim_async`) when `tokio::select!` or scope exit drops an uncompleted future.
3. **`!Unpin`, `UnsafePinned`, and `#[rustc_no_writable]` in `rustc` ABI and Tree Borrows (`lean-miri`):**
   - Inspecting `compiler/rustc_ty_utils/src/abi.rs:362-396` and `proofs-rs/lean-miri` (`Miri/TreeBorrows/RetagPolicy.lean:68-93, 124-133`) establishes three exact aliasing laws:
     1. For `&mut T` (`Mutable`) and `Box<T>` (`Box`), `!(isUnpin && isUnsafeUnpin)` suppresses LLVM `noalias`, `writable`, and `nofree` attributes and makes `RetagPolicy.create` return **`none`** (zero Tree Borrows retag and zero protector registration, preserving interior self-borrows across `Future::poll`).
     2. **Shared `Pin<&T>` Asymmetry & RFC 3467 Divergence:** For `&T` (`Shared`), `!tyIsUnpin` does **not** return `none`! A `PhantomPinned` type (`isUnpin = false, isFreeze = true`) is **still retagged as `Permission.Frozen`** under `Pin<&T>`. By contrast, upstream `core::pin::UnsafePinned<T>` (`core/src/pin/unsafe_pinned.rs:24-29`, diverging from RFC 3467's `value: T` sketch) wraps `UnsafeCell<T>` (`isFreeze = false`), retagging `Pin<&T>` as `Permission.Cell`.
     3. **`#[rustc_no_writable]` on `core::mem::forget` (`core/src/mem/mod.rs:190`):** Disables `implicitWritesEnabled` (`RetagPolicy.lean:72-74`), downgrading `FnEntry` retags of `Unpin` `&mut T` from eager `Permission.Unique` to lazy `Permission.ReservedFrz false`.

## Applicability

This report covers pinned specifications, compiler/runtime implementations, and mechanized semantics in `REPORT.json`:

- **Specifications & Rustonomicon:** `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (RFC 1066 `safe-mem-forget`, RFC 2349 `pin`, RFC 3467 `unsafe-pinned`) and `rust-lang/nomicon@b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6` (`src/leaking.md`).
- **Compiler, Standard Library, and Tokio:** `rust-lang/rust@4b5350e87e487aed08ab2f9f0160a4b2616438bc` (`core/src/pin.rs`, `core/src/pin/unsafe_pinned.rs`, `core/src/mem/mod.rs`, `std/src/thread/scoped.rs`, `rustc_mir_transform/src/coroutine/{mod,drop}.rs`, `rustc_ty_utils/src/abi.rs`) and `tokio-rs/tokio@3f0ffc85f51c71d97bce72e0f8b80ece9b8b4892` (`tokio/src/macros/select.rs`).
- **Mechanized Semantics & Literature:** `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Miri/TreeBorrows/RetagPolicy.lean`, `Miri/Interpreter/TypedRetag.lean`), `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted/MirSemantics.lean`, `Anneal/PureLift/SpatialPin.lean`), and Villani et al. (PLDI 2025), Jung et al. (POPL 2018, POPL 2020), and Gäher et al. (PLDI 2024).

**Relationship to Adjacent Corpus Packages:** Complements `self-referential-unpin-coroutine-field-slicing-and-sroa` (which proves `PinFieldSplitCert` SROA bisimulations) with source-level `Pin` drop and `mem::forget` soundness rules; extends `tokio-select-cancellation-safety-yaml-json-differentials-and-rego-undefined` by showing why internal RAII `Drop` guards that repair `tokio::select!` cancellation are bypassed by `mem::forget(Box::pin(fut))`; and extends `rustc-miri-freeze-visitor-pointee-retag-and-scalarpair-transmute` and `tree-borrows-two-stage-protector-release-and-reborrow-contracts`.

## Findings

### 1. The 2015 Leakpocalypse (`RFC 1066`), Safe Leaks, and Proxy-Guard Design Laws

`Basis: normative + documentation + source + derived`

Before Rust 1.0 (April 2015), `std::mem::forget` was marked `unsafe` and `std::thread::scoped` returned an RAII `JoinGuard<'a>` borrowing stack data of lifetime `'a` from the parent frame, relying on `JoinGuard::drop` to block until the child thread finished (`RFC 1066`, `text/1066-safe-mem-forget.md:14-45` at `f43d5789b838`; `nomicon/src/leaking.md:177-254` at `b0bb569883a3`). Issue `rust-lang/rust#24292` proved `JoinGuard` unsound in `#![forbid(unsafe_code)]` Rust: placing two `Rc<RefCell<...>>` nodes into a cycle leaked `JoinGuard<'a>` without `unsafe`, expiring `'a` and popping the parent's stack frame while the child thread still wrote to freed stack memory.

**RFC 1066** removed `unsafe` from `core::mem::forget` (`library/core/src/mem/mod.rs:190-193` at `4b5350e87e48`: `pub const fn forget<T>(t: T) { let _ = ManuallyDrop::new(t); }`, with **no `'static` or `Unpin` bound**) and established the **Destructor-Independence Law**: *unsafe code must never rely on `Drop::drop` executing to uphold memory safety*. Standard-library proxy types enforce this via two mechanisms:

1. **Pre-Poising / Leak Amplification (`Vec::Drain` & `Rc`, `nomicon/src/leaking.md:52-176`):** `vec.drain(..)` sets `vec.len = 0` **before** yielding its first item (`physInv` holds at every suspension!), restoring `vec.len` only in `Drain::drop`. Calling `mem::forget(drainer)` mid-iteration leaves `vec` safely empty (`len == 0`), leaking unconsumed elements without UAF (*leak amplification*). Likewise, `Rc::clone` aborts if `ref_count` reaches `usize::MAX` (`L166-175`), blocking `mem::forget` refcount-wraparound UAF.
2. **Higher-Ranked Closure Inversion (`std::thread::scope`, `library/std/src/thread/scoped.rs:141-174`):** When external threads or hardware DMA touch stack memory, the guard cannot be returned by value. Rust 1.63+ `pub fn scope<'env, F, T>(f: F) -> T where F: for<'scope> FnOnce(&'scope Scope<'scope, 'env>) -> T` keeps the barrier on `scope`'s own stack frame, wrapping `f(&scope)` in `catch_unwind` (`L158`) and parking in `while scope.data.num_running_threads.load(Ordering::Acquire) != 0` (`L161-164`) before returning or resuming unwind.

---

### 2. Why `core::mem::forget(Box::pin(fut))` Satisfies `Pin`'s Drop Guarantee

`Basis: normative + documentation + source + execution + derived`

RFC 2349 (`text/2349-pin.md:29-36, 131-137`) and `library/core/src/pin.rs:509-587` (`4b5350e87e48`) state that pinning a `!Unpin` value at location $\ell$ requires: (1) the value is never moved out of $\ell$, and (2) **$\ell$ is never invalidated, deallocated, or repurposed until `<T as Drop>::drop` returns or panics** (`L521-534`).

Crucially, `pin.rs:566-586` contrasts **deallocation without drop** against **permanent heap leak**:
- **Violation (`Box<ManuallyDrop<T>>`, `L566-582`):** Projecting `Pin<Box<ManuallyDrop<T>>>` to `Pin<&mut T>` is **unsound** because `Box::drop` frees heap block $\ell$ (`StorageInvalidated = true`) while `ManuallyDrop` suppresses `T::drop` (`DropRan = false`), leaving dangling intrusive-list pointers (`L498-506`).
- **Vacuous Satisfaction (`mem::forget(Box::pin(fut))`, `L584-586`):**
  > *"Of course, \*leaking\* memory in such a way that its underlying storage will never get invalidated or re-used is still fine: [`mem::forget`]ing a [`Box<T>`] prevents its storage from ever getting re-used, so the [`drop`] guarantee is still satisfied."*

Formally, $\text{PinDropGuarantee}(\ell) \triangleq \forall t > t_{\text{pin}},\; \text{Invalidated}(\ell, t) \longrightarrow \exists t_{\text{drop}} \in [t_{\text{pin}}, t),\; \text{DroppedInPlace}(\ell, t_{\text{drop}})$:

| Configuration | Consumed by `mem::forget` | `Drop::drop` Runs? | Storage `ℓ` Invalidated / Reused? | `PinDropGuarantee` | Status |
| :--- | :--- | :---: | :---: | :---: | :--- |
| **`let b = Box::pin(fut);` (normal drop)** | *(not called)* | **Yes** (before dealloc) | **Yes** (heap freed after `drop`) | **True** ($\text{T} \to \text{T}$) | **Sound** |
| **`core::mem::forget(Box::pin(fut))`** | Owning `Pin<Box<Fut>>` | **No** | **No** (heap leaked forever) | **True** ($\text{F} \to \text{F}$) | **Safe Rust** (`pin.rs:584-586`) |
| **`let p = pin!(fut); mem::forget(p);`** | Only `p: Pin<&mut Fut>` | **Yes** (`PinMacroHelper` drops) | **Yes** (stack popped after `drop`) | **True** ($\text{T} \to \text{T}$) | **Safe Rust** (`pin.rs:2145-2192`) |
| **`Box::pin(ManuallyDrop::new(fut))` $\to$ `Pin<&mut Fut>`** | `ManuallyDrop` skips `Fut::drop` | **No** | **Yes** (`Box::drop` frees heap) | **False** ($\text{T} \to \text{F}$) | **UNSOUND / UB** (`pin.rs:566-582`) |

In stack pinning (`library/core/src/pin.rs:2145-2192`), because stack frames are unconditionally reused upon return ($\text{Invalidated} = \text{true}$), `pin!($value)` hides the backing slot in `super let mut pinned: PinMacroHelper<_> = PinMacroHelper { value: $value };` and hands user code only `Pin<&mut Fut>`: forgetting `Pin<&mut Fut>` cannot suppress `pinned`'s destructor! By contrast, `Box::pin(fut)` gives the caller ownership of the heap `Box`, so `mem::forget(Box::pin(fut))` leaks the heap allocation—satisfying `Pin`'s drop guarantee while **immediately ending any non-`'static` borrow `'a` captured inside `fut`**! *(This also explains why `tokio-uring` mandates `IoBuf: Unpin + 'static` rather than borrowing stack `&'a [u8]` across `io_uring` DMA.)*

---

### 3. Separating `physInv` from `cancelInv` in Async Coroutine Verification

`Basis: source + execution + derived`

In `compiler/rustc_mir_transform/src/coroutine/{mod.rs,drop.rs}` (`4b5350e87e48`):
- Calling an `async fn` constructs `CoroutineEnv<'a>` at discriminant **`UNRESUMED = 0`** (`coroutine/mod.rs:894`).
- Each `.await` suspension writes live locals to variant `3 + k`, sets discriminant `3 + k`, and exits `Future::poll` via a **normal `TerminatorKind::Return` (`Poll::Pending`)** (`0` panics, reachable even under `-C panic=abort`). Resuming on `POISONED = 2` (`L897-909`) or `RETURNED = 1` (`L911-926`) branches to `AssertKind::ResumedAfterPanic` / `ResumedAfterReturn` (or `Poll::Pending` when `!can_unwind` / `!async_panic`).
- Dropping `CoroutineEnv<'a>` runs `create_coroutine_drop_shim` (`coroutine/drop.rs:177-254`, or multi-poll `create_coroutine_drop_shim_async` at `L258-277` under `AsyncDrop`).

Consider `RingBuf` with physical safety invariant $\text{physInv}(\text{rb}) \triangleq (\text{rb.head} < \text{rb.cap} = \text{rb.buf.len}())$ guarding `pub fn peek_head(&self) -> u8 { unsafe { *self.buf.get_unchecked(self.head) } }`, and logical permit invariant $\text{cancelInv}(\text{rb}) \triangleq (\text{rb.inflight} = 0)$. Suppose `drain_batch_unsound(rb: &mut RingBuf, io: &mut AsyncSink)` sets `rb.head = rb.cap` before `io.send().await` and relies on a coroutine-local RAII `ResetHeadGuard` whose `Drop` restores `rb.head`:

1. **Caller A (`tokio::select!` Drop Cancellation, `tokio/src/macros/select.rs:101-155`):** When a sibling branch wins `select!`, `select!` drops the suspended future via `coroutine_drop_shim`. Without `ResetHeadGuard`, `rb.head == rb.cap` survives and `rb.peek_head()` triggers OOB UB; *with* `ResetHeadGuard`, `coroutine_drop_shim` restores `rb.head`, masking the bug under `select!` testing!
2. **Caller B (`core::mem::forget(Box::pin(...))` — Refutes `ResetHeadGuard` in `#![forbid(unsafe_code)]`):**
   ```rust
   #![forbid(unsafe_code)]
   pub fn exploit(rb: &mut RingBuf, io: &mut AsyncSink, cx: &mut core::task::Context<'_>) -> u8 {
       {
           let mut fut = Box::pin(drain_batch_unsound(rb, io)); // Borrows `rb` for inner scope `'a`
           let _ = fut.as_mut().poll(cx);                       // `Poll::Pending` with `rb.head == rb.cap`
           core::mem::forget(fut);                              // Safe! Leaks Box, SKIPS `ResetHeadGuard::drop`!
       } // Lifetime `'a` of `&'a mut rb` expires here!
       rb.peek_head() // Executes `buf.get_unchecked(rb.cap)` -> IMMEDIATE OOB UB!
   }
   ```
   Because `mem::forget(fut)` consumes `fut` without running `coroutine_drop_shim`, `'a` ends while `rb.head == rb.cap` (`Basis: execution`, §Revalidation Probe: `select_drop_ub == false` yet `mem_forget_ub == true`)! By contrast, leaving `rb.inflight == 1` across `mem::forget(fut)` merely leaks a logical permit without UB. Sound coroutine verification **must** therefore require `physInv` at **every** `Poll::Pending` yield, `Poll::Ready` return, and `Unwind` exit, using `dropStep` solely to restore `cancelInv`.

---

### 4. `!Unpin`, `UnsafePinned`, and `#[rustc_no_writable]` in `rustc` ABI and Tree Borrows

`Basis: normative + source + execution + derived`

When a self-referential coroutine suspends holding `&scratch[..n]` inside `(*self)` (`SpatialPin` in `theory/Anneal/PureLift/SpatialPin.lean:202-250` at `joshlf/anneal@c131b320eeeb`), **Tree Borrows** (Villani et al., PLDI 2025, DOI `10.1145/3735592`; cf. **Stacked Borrows**, Jung et al., POPL 2020, DOI `10.1145/3371109`) and `rustc` ABI lowering (`compiler/rustc_ty_utils/src/abi.rs:356-398` at `4b5350e87e48`) coordinate via three exact rules mechanized in `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Miri/TreeBorrows/RetagPolicy.lean:28-146` & `Miri/Interpreter/TypedRetag.lean:42-191`):

1. **`&mut T` and `Box<T>` Skip Retagging and `noalias` When `!(isUnpin && isUnsafeUnpin)`:**
   - `abi.rs:362-397` emits LLVM `noalias`, `writable`, and `nofree` on `PointerKind::MutableRef { unpin }` / `Box { unpin, global }` **only when `unpin == true`**.
   - `RetagPolicy.lean:68-76` checks `let tyIsUnpin := facts.isUnpin && facts.isUnsafeUnpin; if (kind == .Mutable || kind == .Box) && !tyIsUnpin then return none`, with theorems `pinned_mutable_reference_is_not_retagged` (`L124-127`) and `pinned_box_is_not_retagged` (`L129-132`) proving zero retag and zero protector registration across all modes (`Default`, `TwoPhase`, `FnEntry`). Thus `Future::poll(Pin<&mut CoroutineEnv>, cx)` never invalidates interior self-borrows.
2. **RFC 3467 vs. Upstream `UnsafePinned<T>` Divergence and the Shared `Pin<&T>` Trap:**
   - In `RetagPolicy.lean:75`, `!tyIsUnpin` early-return applies **only** to `.Mutable` and `.Box`—**never** to `.Shared` (`&T` / `Pin<&T>`), which selects `.Frozen` on frozen bytes and `.Cell` inside `UnsafeCell` (`L54, 77-92`).
   - **Source Disagreement:** RFC 3467 (`text/3467-unsafe-pinned.md:234-241, 286-303`) defined `struct UnsafePinned<T> { value: T }` (`Freeze` if `T: Freeze`, `get(&self) -> *const T`) and stated `&UnsafePinned<T>` stays read-only without `UnsafeCell`. Upstream `library/core/src/pin/unsafe_pinned.rs:9-10, 27-34, 110-112` instead defines `pub struct UnsafePinned<T: ?Sized> { value: UnsafeCell<T> }` (`!Freeze`, `get(&self) -> *mut T`, plus `unsafe impl<T: ?Sized + Sync> Sync`).
   - Consequently, a `PhantomPinned`-only struct (`isUnpin = false, isFreeze = true`) skips retagging on `Pin<&mut S>` **but retags as `Permission.Frozen` on `Pin<&S>`** (making interior `*mut` writes UB while `Pin<&S>` is live), whereas `UnsafePinned<T>` (`isUnpin = false, isFreeze = false`) retags `Pin<&S>` as `Permission.Cell`!
3. **`#[rustc_no_writable]` on `core::mem::forget` (`core/src/mem/mod.rs:190` × `RetagPolicy.lean:72-74`):**
   - Setting `rustcNoWritable = true` turns `implicitWritesEnabled` `false` on `FnEntry`, downgrading `Unpin` `&mut T` retagging from eager `Permission.Unique` (`associatedAccess = some .Write`) to lazy `Permission.ReservedFrz false` (`associatedAccess = none`).

---

### 5. Standalone `prelude`-Compliant Lean 4 (`v4.34.1`) Mechanization

`Basis: source + derived`

The following Lean 4 (`v4.34.1`, `prelude` + `Init.*` only, zero custom axioms) specification encodes `PinDropGuaranteeHolds`, the 5-state `ForgetAndCancelSafe` coroutine contract, and `selectOutsideTbPerm`:

```lean
prelude
import Init.Core
import Init.Data.List.Basic
import Init.Data.Nat.Basic

namespace Verification.PinForgetAsync

/-- Conditional `Pin` drop guarantee (`core/src/pin.rs:521-587`):
    `storageInvalidated -> dropRanBefore` for `!Unpin` storage.
    Leaking via `mem::forget(Box::pin(fut))` (`storageInvalidated = false`) holds vacuously! -/
def PinDropGuaranteeHolds (isUnpin dropRanBefore storageInvalidated : Bool) : Bool :=
  isUnpin || (!storageInvalidated) || dropRanBefore

theorem mem_forget_box_pin_ok : PinDropGuaranteeHolds false false false = true := rfl
theorem box_manually_drop_ub  : PinDropGuaranteeHolds false false true  = false := rfl

inductive CoroPhase where
  | unresumed
  | returnedDone
  | poisoned
  | suspended     (k : Nat)
  | asyncDropping (d : Nat)

inductive StepOutcome (Ret Upvars Frame : Type) where
  | pending (nextPhase : CoroPhase) (upvars : Upvars) (frame : Frame)
  | ready   (ret : Ret) (upvars : Upvars)
  | unwound (upvars : Upvars)
  | aborted

structure CoroSpec (Upvars Frame Ret : Type) where
  numSuspends : Nat
  numDropPts  : Nat
  physInv     : Upvars → Prop
  cancelInv   : Upvars → Prop
  suspendInv  : Nat → Upvars → Frame → Prop
  dropInv     : Nat → Upvars → Frame → Prop

/-- `physInv` MUST hold at every `.pending` yield (`mem::forget(Box::pin(fut))` defense!),
    while `dropStep` restores `cancelInv` across synchronous/async cancellation. -/
def ForgetAndCancelSafe {Upvars Frame Ret : Type}
    (S        : CoroSpec Upvars Frame Ret)
    (pollStep : CoroPhase → Upvars → Frame → Option (StepOutcome Ret Upvars Frame))
    (dropStep : CoroPhase → Upvars → Frame → Option (StepOutcome Unit Upvars Frame)) : Prop :=
  (∀ ph u fr,
    ((ph = .unresumed ∧ S.physInv u ∧ S.cancelInv u) ∨
     (∃ k, Nat.blt k S.numSuspends = true ∧ ph = .suspended k ∧
           S.physInv u ∧ S.suspendInv k u fr)) →
    match pollStep ph u fr with
    | none => False
    | some .aborted => True
    | some (.unwound u') => S.physInv u'
    | some (.ready _ u') => S.physInv u' ∧ S.cancelInv u'
    | some (.pending ph' u' fr') =>
      S.physInv u' ∧
      ∃ k', Nat.blt k' S.numSuspends = true ∧ ph' = .suspended k' ∧
            S.suspendInv k' u' fr') ∧
  (∀ ph u fr,
    ((ph = .unresumed ∧ S.physInv u ∧ S.cancelInv u) ∨
     (∃ k, Nat.blt k S.numSuspends = true ∧ ph = .suspended k ∧
           S.physInv u ∧ S.suspendInv k u fr) ∨
     (∃ d, Nat.blt d S.numDropPts = true ∧ ph = .asyncDropping d ∧
           S.physInv u ∧ S.dropInv d u fr)) →
    match dropStep ph u fr with
    | none => False
    | some .aborted => True
    | some (.unwound u') => S.physInv u'
    | some (.ready _ u') => S.physInv u' ∧ S.cancelInv u'
    | some (.pending ph' u' fr') =>
      S.physInv u' ∧
      ∃ d', Nat.blt d' S.numDropPts = true ∧ ph' = .asyncDropping d' ∧
            S.dropInv d' u' fr')

inductive TbPerm where
  | frozen | cell | unique | reservedFrz | reservedIM

inductive RefKind where
  | shared | mutable | boxPtr

def selectOutsideTbPerm
    (isUnpin isUnsafeUnpin isFreeze isFnEntry implicitWrites rustcNoWritable : Bool)
    (kind : RefKind) : Option TbPerm :=
  let tyIsUnpin := isUnpin && isUnsafeUnpin
  let impWr := isFnEntry && implicitWrites && (!rustcNoWritable)
  match kind with
  | .shared => some (match isFreeze with | true => .frozen | false => .cell)
  | .mutable | .boxPtr =>
    match tyIsUnpin with
    | false => none
    | true  => some (match impWr || isFnEntry || isFreeze with
                     | true  => .reservedFrz
                     | false => .reservedIM)

theorem phantomPinned_shared_frozen :
    selectOutsideTbPerm false true true true true false .shared = some .frozen := rfl

theorem unsafePinned_shared_cell :
    selectOutsideTbPerm false false false true true false .shared = some .cell := rfl

end Verification.PinForgetAsync
```

*(Note on conditional `mem::forget` drop flags in MIR: when a synchronous guard exposes `pub fn abort(self) { ...; core::mem::forget(self); }` called inside `if cancel { g.abort(); }`, `rustc` emits a boolean drop-flag local `_df_g` joining `(0, .uninit)` and `(1, .init)` before `SwitchInt(_df_g) -> [0: bb_ret, otherwise: bb_drop]`; abstract interpreters must track a relational `flagged (dfLocal : LocalId) (val : Val)` slot state rather than widening `g` to `InitDom.top`.)*

## Boundaries

- **Unstable `AsyncDrop` (`#![feature(async_drop)]`, `unknown` ecosystem adoption):** While `coroutine/drop.rs:258` lowers `create_coroutine_drop_shim_async` (covered by `.asyncDropping d` above), whether standard combinators like `tokio::select!` will poll async destructors upon stabilization is **unknown**; regardless, `mem::forget(Box::pin(fut))` will still skip `AsyncDrop`, keeping `physInv` at `Poll::Pending` mandatory.
- **Unstable `UnsafePinned` (`#![feature(unsafe_pinned)]`, `#125735`, `unknown` final `DispatchFromDyn` contract):** `core/src/pin/unsafe_pinned.rs:177` carries an open `FIXME(unsafe_pinned)` regarding `DispatchFromDyn` soundness, so its final stabilized trait impls remain **unknown**.
- **Must-Not-Leak Types (`?Leak`, `unsupported` in Rust):** Per RFC 1066 (`text/1066-safe-mem-forget.md:104-119`), preventing callers from passing a owned `Future` to `mem::forget` or an `Rc` cycle is **unsupported** in Rust; mandatory pre-return cleanup requires closure inversion (`std::thread::scope`).
- **Legacy Stacked Borrows vs. Tree Borrows (`known not to apply` identically on `PhantomPinned` `&S`):** Tree Borrows' lazy `Reserved`/`Cell` state transitions in `RetagPolicy.lean` are **known not to apply** verbatim to `-Zmiri-stacked-borrows` when raw pointers derived from shared `&S` are mutated without `UnsafeCell`.
- **`RawWakerVTable` Reentrancy Across Intrusive Executor Lists (`not examined`):** Reentrant `cx.waker().wake_by_ref()` calls mutating intrusive executor wait-queues (`tokio::sync::Notify`) during `Future::poll` were **not examined** here.

## Evidence

1. **Normative RFCs & Rustonomicon:** `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` (`text/1066-safe-mem-forget.md:8-62, 104-119`; `text/2349-pin.md:29-60, 88-267, 341-403`; `text/3467-unsafe-pinned.md:11-74, 202-348`); `rust-lang/nomicon@b0bb569883a3e65ab19d4f1adf1b8dbc1629d0a6` (`src/leaking.md:23-254`).
2. **Compiler, Standard Library & Tokio (`rust-lang/rust@4b5350e87e487aed08ab2f9f0160a4b2616438bc` & `tokio-rs/tokio@3f0ffc85f51c71d97bce72e0f8b80ece9b8b4892`):**
   - `library/core/src/pin.rs:509-587` (`Drop` guarantee, `ManuallyDrop` UB counterexample `L566-582`, `mem::forget(Box<T>)` heap-leak clause `L584-586`) & `L2145-2200` (`pub macro pin`, `PinMacroHelper`, `#153438`).
   - `library/core/src/pin/unsafe_pinned.rs:7-40, 89-113` (`UnsafePinned` wrapping `UnsafeCell<T>`, `get(&self) -> *mut T`); `library/core/src/mem/mod.rs:190-193` (`#[rustc_no_writable] pub const fn forget`); `library/std/src/thread/scoped.rs:141-174` (`std::thread::scope`).
   - `compiler/rustc_mir_transform/src/coroutine/mod.rs:889-928` & `coroutine/drop.rs:177-277`; `compiler/rustc_ty_utils/src/abi.rs:356-398` (`NoAlias`, `Writable`, `NoFree`).
   - `tokio/src/macros/select.rs:101-155` (losing-branch drop cancellation).
3. **Mechanized Semantics & Literature:** `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Miri/TreeBorrows/RetagPolicy.lean:28-93, 124-146`; `Miri/Interpreter/TypedRetag.lean:42-72, 102-191`); `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted/MirSemantics.lean:45-108`, `Anneal/PureLift/SpatialPin.lean:202-250`); Villani et al. (`10.1145/3735592`), Jung et al. (`10.1145/3371109`, `10.1145/3158154`), Gäher et al. (`10.1145/3656422`).
4. **Execution (`2026-11-20`, Python `3.13.15` on `x86_64` Linux):** Ran §Revalidation probe (`exit 0`), verifying all `4` `Pin` drop scenarios, `ResetHeadGuard` refutation under `mem::forget(Box::pin(fut))` (`select_drop_ub: false`, `mem_forget_ub: true`), `0` UB under `physInv` + `cancelInv`, and all `192` `RetagPolicy.create` combinations.

## Revalidation

1. **Upstream Diff Checks (~10 seconds):** Diff `library/core/src/pin.rs` (`Drop` guarantee & `pin!`), `library/core/src/pin/unsafe_pinned.rs` (`UnsafeCell<T>` backing), `compiler/rustc_ty_utils/src/abi.rs` (`MutableRef`/`Box` `unpin` attributes), `library/core/src/mem/mod.rs` (`#[rustc_no_writable]`), and `Miri/TreeBorrows/RetagPolicy.lean` (`create`).
2. **Deterministic Model Probe (<0.1 seconds, Python 3.10+ stdlib only):**

```python
#!/usr/bin/env python3
"""Self-contained revalidation probe for Pin drop guarantee, mem::forget, async cancellation, and Tree Borrows."""
from __future__ import annotations
import itertools
import json

def pin_drop_guarantee_holds(is_unpin: bool, drop_ran: bool, storage_invalidated: bool) -> bool:
    return is_unpin or (not storage_invalidated) or drop_ran

def check_async_ringbuf(breaks_phys_inv_at_yield: bool, has_drop_guard: bool) -> dict[str, bool]:
    head_at_pending = 8 if breaks_phys_inv_at_yield else 0
    tickets_at_pending = 1
    head_select = 0 if (not breaks_phys_inv_at_yield or has_drop_guard) else head_at_pending
    tickets_select = 0 if has_drop_guard else tickets_at_pending
    return {
        "select_drop_ub": not (head_select < 8),
        "mem_forget_ub": not (head_at_pending < 8),
        "select_restores_cancel_inv": tickets_select == 0,
    }

def tb_create(is_unpin: bool, is_unsafe_unpin: bool, is_freeze: bool,
              kind: str, mode: str, implicit_writes: bool, rustc_no_writable: bool):
    if mode == "None":
        return None
    ty_is_unpin = is_unpin and is_unsafe_unpin
    is_protected = (mode == "FnEntry")
    imp_wr = is_protected and implicit_writes and (not rustc_no_writable)
    if kind in ("Mutable", "Box") and (not ty_is_unpin):
        return None

    def sel(part: str) -> str:
        frozen = True if part == "InsideFrozen" else (False if part == "InsideUnsafeCell" else is_freeze)
        if kind == "Shared":
            return "Frozen" if frozen else "Cell"
        if imp_wr and part != "Outside":
            return "Unique"
        return "ReservedFrz(false)" if (is_protected or frozen) else "ReservedIM"

    return {
        "freezePermission": sel("InsideFrozen"),
        "nonfreezePermission": sel("InsideUnsafeCell"),
        "outsidePermission": sel("Outside"),
        "protector": ("WeakProtector" if kind == "Box" else "StrongProtector") if is_protected else None,
    }

assert pin_drop_guarantee_holds(False, True, True) is True
assert pin_drop_guarantee_holds(False, False, False) is True
assert pin_drop_guarantee_holds(False, True, True) is True
assert pin_drop_guarantee_holds(False, False, True) is False

guard_only = check_async_ringbuf(True, True)
split_inv = check_async_ringbuf(False, True)
assert guard_only == {"select_drop_ub": False, "mem_forget_ub": True, "select_restores_cancel_inv": True}
assert split_inv == {"select_drop_ub": False, "mem_forget_ub": False, "select_restores_cancel_inv": True}

combos = list(itertools.product(
    ("Shared", "Mutable", "Box"),
    ("None", "Default", "TwoPhase", "FnEntry"),
    (False, True), (False, True), (False, True), (False, True),
))
assert len(combos) == 192
assert sum(1 for k, m, u, uu, f, nw in combos
           if k in ("Mutable", "Box") and not (u and uu) and tb_create(u, uu, f, k, m, True, nw) is not None) == 0
assert tb_create(False, True, True, "Shared", "FnEntry", True, False)["outsidePermission"] == "Frozen"
assert tb_create(False, False, False, "Shared", "FnEntry", True, False)["outsidePermission"] == "Cell"
assert tb_create(True, True, True, "Mutable", "FnEntry", True, False)["freezePermission"] == "Unique"
assert tb_create(True, True, True, "Mutable", "FnEntry", True, True)["freezePermission"] == "ReservedFrz(false)"
print(json.dumps({"status": "ok", "tb_combinations": len(combos), "guard_only_mem_forget_ub": guard_only["mem_forget_ub"]}))
```

3. **Verifier Canary Check:** Submit `drain_batch_unsound` (with internal `ResetHeadGuard`) paired with `exploit` (`Box::pin` $\to$ `poll` $\to$ `core::mem::forget` $\to$ `peek_head`). Any sound async Rust verifier **must reject** `drain_batch_unsound` (`exit 1`) because `physInv` fails at `Poll::Pending`.
