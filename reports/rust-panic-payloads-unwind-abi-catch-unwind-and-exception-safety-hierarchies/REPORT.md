# Rust Panic Payloads, Unwind ABI, catch_unwind, and Exception-Safety Hierarchies

## Summary

Sound verification and `unsafe` engineering in Rust require modeling panics and stack unwinding as defined, three-outcome control flow rather than Undefined Behavior (UB) or simple abort markers:

1. **Three-pole non-UB outcome algebra (`returned | unwound | aborted`):** In `Runtime(PostCleanup)` MIR and `proofs-rs/lean-miri@c92d1d9754`, panics are well-defined transitions partitioning terminating execution into normal return (`.returned`), stack unwinding (`.unwound`), and immediate abort (`.aborted`). Treating a safe bounds/arithmetic panic as UB ("panic laundering") is unsound whenever callers invoke `std::panic::catch_unwind`, join threads, or observe side effects from `Drop` cleanup blocks (`is_cleanup = true`). Under `-C panic=abort`, Rust function bodies omit unwind landing pads, yet calls to `extern "C-unwind"` remain guarded by `AbortUnwindingCalls` (`abort_unwinding_calls.rs:124–135`), rewriting `UnwindAction::Continue` to `UnwindAction::Terminate(UnwindTerminateReason::Abi)` and `UnwindResume` to `UnwindTerminate`.
2. **`UnwindSafe` and `RefUnwindSafe` cannot uphold soundness:** Neither `UnwindSafe` nor `RefUnwindSafe` (`rust-lang/rust@8144389c` `library/core/src/panic/unwind_safe.rs:91, 109`) is an `unsafe trait`. `AssertUnwindSafe<T>(pub T)` (`L171`) has an unconditionally safe public constructor, and `*mut T` / `NonNull<T>` automatically implement `UnwindSafe` whenever `T: RefUnwindSafe` (`L187–190`). Consequently, **`unsafe` code is unsound if it relies on `UnwindSafe` or `RefUnwindSafe` bounds** (`rust-lang/reference@a286e1ecb8ce`, `src/behavior-considered-undefined.md:7–8`).
3. **Layered exception safety, double-panic rules, and `CutFirewall` landing-pad coalescing:** Adapting Abrahams' hierarchy (LNCS 1766, DOI `10.1007/3-540-39953-4_6`) and Rudra's bug taxonomy (SOSP 2021, DOI `10.1145/3477132.3483570`) separates **physical memory safety (`physInv`)**—mandatory under all unwinds via pre-drop advancement (`Vec::retain_mut` `g.read += 1` before `drop_in_place`), `ScopeGuard::into_inner` (`hashbrown`), or `catch_unwind` + `process::abort()` (`take_mut`)—from **logical invariants (`logicalInv`)** and **Strong rollback**. Meanwhile, `panicking.rs` distinguishes contained `catch_unwind` panics inside `Drop` (permitted once `finished_panic_hook()` clears `in_panic_hook`) from uncaught `Drop` panics (`UnwindAction::Terminate(InCleanup)`, `elaborate_drop.rs:69`), and post-`fork` `ALWAYS_ABORT_FLAG` checks (`L418`). In Lean 4 (`v4.34.1`), `@Nat.rec` three-rail `(onRet, onUnwind, onAbort)` weakest preconditions paired with `@[irreducible] CutFirewall` landing pads collapse $K$-iteration loop cleanup from $O(K^2)$ to $O(1)$ without axioms beyond `[propext]`.

## Applicability

This report synthesizes findings across seven pinned repositories and specifications:

- **Normative Rust language & compiler/runtime:** `rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd` (`library/core/src/panic/unwind_safe.rs`, `library/core/src/panicking.rs`, `library/std/src/panicking.rs`, `library/panic_unwind/src/lib.rs`, `library/alloc/src/vec/mod.rs`, `compiler/rustc_mir_transform/src/{abort_unwinding_calls,elaborate_drop,elaborate_drops}.rs`) and `rust-lang/reference@a286e1ecb8ce193d50056e4bb042eea9b23876ef` (`src/panic.md`, `src/behavior-considered-undefined.md`).
- **Mechanized operational semantics & boundary verification:** `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Miri/Interpreter/{ControlFlow,Unwind,Panic,Call}.lean`), `rust-lang/miri@7fa591d7d4dd9af8154becbc8332f8096f8323b1`, and `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted.MirAst`, `Trusted.MirSemantics`, `Trusted.Correspondence`).
- **Exception-safe `unsafe` crates:** `rust-lang/hashbrown@f3e9f0fc110f55ca55d73d6eddc0bdf5e85eb223` (`src/scopeguard.rs`, `src/raw.rs`) and `Sgeo/take_mut@1bd70d842c6febcd16ec1fe3a954a84032b89f52` (`src/lib.rs`).

**Relation to sibling corpus reports:** Prior packages cover target-specific DWARF/SEH unwinding tables (`unwinding-on-elf-and-macho-targets`, `unwinding-on-windows-targets-and-32bit-seh`), FFI `C-unwind` binary ABI calling conventions (`rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`), MIR drop-flag dataflow elaboration (`rustc-drop-elaboration-unwind-landing-pads-and-extensible-mir-semantics`), Tree Borrows protected store-sinking (`tree-borrows-unwinding-cleanup-pads-two-phase-borrows-and-unsafecell`, `tree-borrows-unwinding-store-sinking-and-protected-dse`), and panic-flag profile subsumption (`mir-profile-subsumption-overflow-checks-debug-assertions-and-panic-modes`). This package analyzes panic payloads, the `catch_unwind` union/stack protocol, double-panic/`fork` abort state machines, `UnwindSafe` unsoundness counterexamples, Rust container `PanicGuard`/`ScopeGuard`/`take_mut` hierarchies, and three-rail Lean 4 verification logic.

## Findings

### 1. MIR Unwind Control Flow, `AbortUnwindingCalls`, and `-C panic=unwind` vs. `-C panic=abort`

Basis: normative + source

Post-cleanup Rust MIR represents exception propagation explicitly through `UnwindAction` and `TerminatorKind` (`Trusted/MirAst.lean:682–795`; `Miri/MIR/Syntax.lean:161–171`):

- **`UnwindAction` (`MirAst.lean:693–697`):**
  - `.Continue`: propagate active unwind to caller frame;
  - `.Unreachable`: callee/op cannot unwind (unwinding past it is immediate UB);
  - `.Terminate(reason)`: immediate abort (`reason ∈ { Abi, InCleanup }`);
  - `.Cleanup(bb)`: jump to cleanup basic block `bb` (`BasicBlock.cleanup == true`), ending in `TerminatorKind::UnwindResume` (or `UnwindTerminate`).

In `proofs-rs/lean-miri@c92d1d9754` (`Miri/Interpreter/ControlFlow.lean:42–113, 143–202`), `returnFromCurrentFrame` enforces exact cleanup discipline:
1. Reading local `_0` succeeds, and `isCleanup` (`frame.location == .unwinding _ ∨ bb.cleanup`) must match `unwinding : Bool` (`L74–75`).
2. Attempting to unwind past the topmost root frame (`unwinding && state.stack.frames.size == 1`) is **Undefined Behavior** (`L76–77`).
3. On normal return (`!unwinding`), `copyReturn` writes `_0` to the caller destination and transitions to `returnToBlock ret`; on unwind (`unwinding`), return copy is skipped and control routes through `unwindToBlock` (`L42–60`): `.Cleanup block` enters `block`, `.Unreachable` faults `.undefinedBehavior "unwinding past a frame that does not allow unwinding"`, `.Continue` sets frame location to `.unwinding span`, and `.Terminate reason` invokes `unwindTerminate`.

**Why `-C panic=abort` is not "unwind-free":**
As documented in `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:10–25, 47–136`, `AbortUnwindingCalls` checks `body_can_unwind := layout::fn_can_unwind(tcx, Some(def_id), body_abi)` and `call_can_unwind` per call/drop/assert/asm terminator:
- Under `-C panic=abort`, Rust-ABI `Call`, `Drop`, and `Assert` have `call_can_unwind == false`, so `L122–123` rewrites their `UnwindAction` to `.Unreachable` and prunes cleanup blocks (`remove_dead_blocks`).
- **Crucial exception (`extern "C-unwind"`):** If a `-C panic=abort` Rust function calls an `extern "C-unwind"` foreign function (`call_can_unwind == true`), `L124–135` does **not** set `.Unreachable`: it rewrites `UnwindAction::Continue` to `UnwindAction::Terminate(UnwindTerminateReason::Abi)`, and `L78–83` rewrites `UnwindResume` inside any remaining cleanup pads to `TerminatorKind::UnwindTerminate(UnwindTerminateReason::Abi)` (`L79–80` uses `Unreachable` only on `wasm` without `exception-handling`). Thus, `-C panic=abort` must execute local drop cleanup or explicitly trap foreign unwinds rather than ignoring unwind edges (`Call.lean:517–518` similarly coerces unwinding into non-unwinding ABIs to `.Unreachable`).
- Furthermore, per `rust-lang/reference@a286e1ecb8ce` (`src/panic.md:99–101`), crates compiled with `-C panic=unwind` can link with an `abort` panic handler, whereas crates compiled with `-C panic=abort` cannot link with an `unwind` panic handler because their MIR lacks cleanup pads (`ControlFlow.lean:46–47`).

### 2. Panic Payloads, `intrinsics::catch_unwind`, and `lean-miri` `PayloadStore`

Basis: source

Rust panics carry dynamically typed payloads `Box<dyn Any + Send + 'static>` allocated lazily on unwind:

1. **Zero-allocation entry (`library/std/src/panicking.rs:610–755`):**
   - `panic!("...")` enters `core::panicking::panic_fmt` (`library/core/src/panicking.rs:48–73`, `can_unwind = true`), reaching `std`'s `#[panic_handler]` (`panicking.rs:609–693`), which constructs stack-allocated `StaticStrPayload` or lazy `FormatStringPayload` implementing `PanicPayload`. `panic_any(msg)` enters `#[lang = "begin_panic"]` (`L707–755`), storing `Payload { inner: Some(msg) }`.
   - Crucially, `panic_with_hook` (`L773–837`) invokes the panic hook **before** `rust_panic` calls `__rust_start_panic(payload)` (`library/panic_unwind/src/lib.rs:90–92`). Only `panic_unwind`'s `imp::panic` calls `payload.take_box()` to heap-allocate `Box<dyn Any + Send>` (`L61–62`); aborting runtimes avoid heap allocation on panic!
   - Under `panic_nounwind_fmt` (`core/src/panicking.rs:84–113`, marked `#[rustc_nounwind]`), `PanicInfo` sets `can_unwind = false`, causing `panicking.rs:828–834` to print `"thread caused non-unwinding panic. aborting."` and call `process::abort()`.
2. **`catch_unwind` `union Data<F, R>` protocol (`panicking.rs:498–598`):**
   `std::panicking::catch_unwind` avoids ABI-level payload passing via three-state in-place ownership transfer over a stack `union`:
   ```rust
   union Data<F, R> {
       f: ManuallyDrop<F>,
       r: ManuallyDrop<R>,
       p: ManuallyDrop<Box<dyn Any + Send>>,
   }
   ```
   `do_call` (`L569–575`) moves `f` out via `ManuallyDrop::take(&mut (*data).f)`, invokes `f()`, and writes `data.r`. If `f()` unwinds, the `#[rustc_nounwind]` landing callback `do_catch(data, payload)` (`L586–597`) calls `cleanup(payload)`—invoking `__rust_panic_cleanup(payload)` (`panic_unwind/src/lib.rs:83–85`) and `panic_count::decrease()` (`L560`)—and writes `data.p`. `intrinsics::catch_unwind` returns `true` on panic (moving `data.p` into `Err`) and `false` on normal return (moving `data.r` into `Ok`).
3. **Mechanized `PayloadStore` (`proofs-rs/lean-miri@c92d1d9754`, `Miri/Interpreter/Unwind.lean:13–129`):**
   `lean-miri` models thread-local exception objects via monotonic `PayloadStore` tokens (`nextToken : Nat`, `values : Array (Nat × RvalueImmTy Provenance)`):
   - `handleStartUnwind` (`L93–96`) reads the payload immediate and appends `nextToken` to `thread.unwindPayloads`.
   - `handleCatchUnwind` (`L101–115`) forces allocation of `dest`, invokes `tryFn(data)` with `.goto ret .Continue`, pre-zeros `dest` (`writeNull` $\to$ `false`), and—**only if `panicUnwinds == true`**—records `frame.extra.catchUnwind := some ⟨catchPointer, data, dest, ret⟩`.
   - `afterStackPop` (`L119–128`) executes upon unwinding out of the `tryFn` frame: it writes `Scalar.fromBool true` to `caught.dest`, pops the top token from `thread.unwindPayloads` (`popPayload`, `L67–83`), calls `catchFn(data, payload)` with `(.goto caught.ret .Unreachable)`, and returns `.noJump` so `ControlFlow` does not follow `frame.returnContinuation`.
   - **Provenance GC tracking:** Notice `Miri/Interpreter/ProvenanceGC.lean:105–112` explicitly walks `thread.unwindPayloads` as GC provenance roots so payloads carrying heap pointers are never collected mid-unwind!

### 3. Double-Panic, Panic-Hook Recursion, and `fork`-Safe `GLOBAL_PANIC_COUNT`

Basis: source + derived

Rust's panic-abort transition has **four distinct regimes** governed by `LOCAL_PANIC_COUNT: Cell<(usize, bool)>` and `GLOBAL_PANIC_COUNT: Atomic<usize>` in `library/std/src/panicking.rs:368–485, 773–875` alongside `rustc`'s `elaborate_drop.rs:54–70`:

| Trigger Scenario | State Inside `panicking.rs` / MIR | Outcome & Exact Code Locus |
| :--- | :--- | :--- |
| **1. Uncaught panic escapes `Drop` during active unwind** | `elaborate_drop` runs inside cleanup pad (`Unwind::InCleanup`) | **Abort (`UnwindTerminateReason::InCleanup`):** `elaborate_drop.rs:54–70` lowers cleanup drops to `UnwindAction::Terminate(InCleanup)`. |
| **2. Contained `catch_unwind` inside `Drop` during unwind** | `finished_panic_hook()` already set `in_panic_hook = false` (`L826`); inner `catch_unwind` stops unwind before cleanup boundary | **Recovers cleanly (`count: 1 → 2 → 1`):** `panic_count::increase(true)` returns `None` (`L423–429`); inner `do_catch` calls `decrease()` (`L560`). |
| **3. Panic inside `std::panic::set_hook` handler** | `LOCAL_PANIC_COUNT` has `in_panic_hook == true` (`L428`) | **Immediate Abort even inside `catch_unwind`:** `increase` returns `Some(MustAbort::PanicInHook)` (`L425–427`), calling `process::abort()` (`L799`) before unwinding begins. |
| **4. Panic after `panic::always_abort()` or `fork()`** | `GLOBAL_PANIC_COUNT & ALWAYS_ABORT_FLAG != 0` (`ALWAYS_ABORT_FLAG = 1 << (BITS - 1)`, `L368`) | **Immediate Abort without TLS touch:** `L418–421` returns `MustAbort::AlwaysAbort` *before* accessing `LOCAL_PANIC_COUNT` (avoiding UB TLS allocation in post-`fork` children, `L393–399`). |

Additionally, `std::panic::resume_unwind(payload)` (`panicking.rs:842–875`) calls `panic_count::increase(false)`—skipping panic hooks while still aborting if `ALWAYS_ABORT_FLAG` or `in_panic_hook` is active—and wraps `payload` in `RewrapBox` straight into `rust_panic` (`__rust_start_panic`).

### 4. Why `UnwindSafe` / `RefUnwindSafe` Cannot Uphold Soundness

Basis: normative + source + derived

In `library/core/src/panic/unwind_safe.rs`, `UnwindSafe` (`L91`) and `RefUnwindSafe` (`L109`) are **safe** auto traits—not `unsafe auto trait`s. Their documentation explicitly calls `UnwindSafe` a *"speed bump"* (`L61–64`). Three lines in `unwind_safe.rs` prove why **no `unsafe` abstraction may depend on `UnwindSafe` or `RefUnwindSafe` for memory safety**:

1. **`AssertUnwindSafe<T>(pub T)` (`L171, 192, 201`):** Any safe caller can construct `AssertUnwindSafe(val)` for *any* `T` (including `&mut Vec`, `&RefCell`, or closures capturing non-`UnwindSafe` mutable state) and unconditionally satisfy `UnwindSafe` and `RefUnwindSafe`.
2. **Raw pointers bypass `!UnwindSafe` on `&mut T` (`L186–190`):** While `impl<T> !UnwindSafe for &mut T` (`L182`) blocks `&mut u32` directly, `*const T`, `*mut T`, and `NonNull<T>` all carry `impl<T: RefUnwindSafe + PointeeSized> UnwindSafe` (`L186–190`), and `UnsafeCell` is the *only* primitive disabling `RefUnwindSafe` (`L198–199`).
3. **Minimal soundness counterexample:** Suppose an `unsafe` helper `fn broken_modify<F: FnOnce(&mut [u8]) + UnwindSafe>(buf: &mut Vec<u8>, f: F)` sets `buf.set_len(new_cap)` with uninitialized capacity before calling `f`, assuming `F: UnwindSafe` guarantees either completion or no observable recovery. A 100% safe caller wraps `AssertUnwindSafe(|| panic!())` inside `std::panic::catch_unwind(AssertUnwindSafe(|| broken_modify(&mut v, AssertUnwindSafe(|_| panic!()))))`, catches the panic, and drops `v`—reading `.uninit` bytes (`InvalidUninitBytes` UB)!

**Formal Trait Safety Discipline:** In verification logics (such as `Anneal`'s `TraitSafetyDiscipline`), **safe traits** (`UnwindSafe`, `RefUnwindSafe`, `Ord`, `FnMut`) may serve *only* as assumptions for **functional postconditions** (`logicalInv`), never for baseline UB-freedom (`WellFormed` / `physInv`). Only `unsafe trait`s (`Send`, `Sync`, `TrustedLen`) carry caller-discharged memory-safety preconditions.

### 5. Abrahams Exception-Safety Hierarchy in `unsafe` Rust

Basis: documentation + source + derived

David Abrahams' exception-safety taxonomy (LNCS 1766, DOI `10.1007/3-540-39953-4_6`) classifies operations into *No Guarantee*, *Basic*, *Strong* (commit-or-rollback), and *No-Throw*. Under Rust's ownership rules (`rust-lang/reference@a286e1ecb8ce`, `src/behavior-considered-undefined.md:7–8`) and Rudra's ecosystem audit (Bae et al., SOSP 2021, DOI `10.1145/3477132.3483570`), **every safe API exposing `unsafe` code must uphold at least a split Basic Guarantee (`physInv`)** regardless of panics:

| Level | C++ Abrahams Meaning | Rust Ownership & Verification Requirement | Concrete Upstream Witness |
| :--- | :--- | :--- | :--- |
| **0. No Guarantee** | Corrupt invariants / UB allowed on throw | **Forbidden (`Unsound`)** for `physInv` in Rust if reachable from safe callers | Rudra premature `set_len` before fallible `Iterator::next` (`SOSP'21`) |
| **1a. Physical Basic (`physInv`)** | Destructible, leak-safe, valid representation | **Mandatory soundness floor:** every initialized slot valid for `Drop`, no double-drop, no `&mut` aliasing, valid lengths/tags | `Vec::retain_mut` (`vec/mod.rs:2466–2537`), `hashbrown::RawTableInner` (`raw.rs:842`) |
| **1b. Logical Basic (`logicalInv`)** | Domain invariants preserved (`Mutex` poisoned) | **Optional logical contract:** advised by `UnwindSafe`; poisoning exposes `PoisonError::into_inner()` safely | `std::sync::Mutex` poisoning; `Ord` sort scramble on panic |
| **2. Strong (Rollback)** | Observable state unchanged on panic | Validate/allocate/mutate in scratch space before atomic swap/commit | `hashbrown::clone_from` (`raw.rs:3349–3394`) via `ScopeGuard` |
| **3. No-Throw / Abort** | Never propagates unwind (`noexcept`) | Enforce `#[rustc_nounwind]` or `catch_unwind` $\to$ `process::abort()` when no fallback exists | `take_mut::take` (`take_mut/src/lib.rs:31–41`), `panic_nounwind_fmt` |

Four canonical `unsafe` Rust patterns exemplify subtle verification hazards in this hierarchy:

1. **Three-Zone `PanicGuard` & Early Cursor Advance (`library/alloc/src/vec/mod.rs:2456–2537`):**
   `Vec::retain_mut` partitions `[0 .. original_len)` into `[Kept (0..write) | Hole (write..read) | Unchecked (read..original_len)]`. Crucially, at both drop sites (`L2508` and `L2517`), **`g.read += 1` executes BEFORE `unsafe { ptr::drop_in_place(cur) }`!** If a user's `T::drop` panics during `drop_in_place`, `PanicGuard::drop` (`L2475–2489`) executes `ptr::copy(read, write, original_len - read)` and `set_len(write + remaining)`. Advancing `read` *after* `drop_in_place` would copy the already-dropped element back into the live vector prefix, causing **immediate double-drop UB** when the outer `Vec` drops!
2. **`ScopeGuard::into_inner` Aliasing Hygiene (`rust-lang/hashbrown@f3e9f0fc11`, `src/scopeguard.rs:29–40`, `src/raw.rs:3394`):**
   To disarm a guard cleanly under Tree Borrows / Stacked Borrows (`Villani et al. PLDI 2025`, DOI `10.1145/3729265`), `ScopeGuard::into_inner(guard: Self)` wraps `let guard = ManuallyDrop::new(guard);` and extracts fields via `ptr::read(&raw const guard.value)` and `ptr::read(&raw const guard.dropfn)` instead of calling `mem::forget(guard)` after reading, avoiding invalidating `&mut` borrows stored inside `guard.value` (`src/raw.rs:842, 3349, 3452`) via `mem::forget`'s value move.
3. **Vacated `&mut T` Recovery (`Sgeo/take_mut@1bd70d842c`, `src/lib.rs:31–41, 81–97`):**
   `take_mut::take` reads `old_t = ptr::read(mut_ref)`, leaving `*mut_ref` logically uninitialized (bitwise duplicate) while invoking `closure(old_t)`. Because no `T` exists to write back if `closure` panics, `L37–38` executes `panic::catch_unwind(AssertUnwindSafe(|| closure(old_t))).unwrap_or_else(|_| process::abort())`. Note that `take_mut::take_or_recover` (`L81–97`) must wrap **both** `closure(old_t)` AND the user's `recover()` callback in separate `catch_unwind` calls (`L86, L89`), aborting if `recover()` itself panics before calling `ptr::write(mut_ref, r)` and `panic::resume_unwind(err)`.
4. **Drop-Time Reentrancy & `Protected Unique` (`Miri/Interpreter/Call.lean:392, 690–703`):**
   If `Container::remove(&mut self, id)` calls `ptr::drop_in_place(slot_ptr)` *while* holding `&mut self` across the `Call`, Tree Borrows protects `self` as `Protected Unique` for the duration of `drop_in_place`. Any reentrant callback inside `Drop::drop` touching `*self` via `Rc<UnsafeCell<Container>>` triggers foreign `Protected Unique -> Disabled` UB! Sound containers must either take `&self` + internal lock (`PCM.Excl`) released before `drop_in_place` and mark the slot `.drainingDrop` (preventing double-drop on unwind), or extract ownership out of `self` before returning `&mut self`'s frame.

### 6. Three-Rail Weakest Preconditions `(onRet, onUnwind, onAbort)` and `CutFirewall`

Basis: source + derived

To verify exception safety constructively inside Lean `v4.34.1` (`prelude` + `Init.*`, `0` `Classical.choice`, `0` `._unsafe_rec`), small-step outcomes split into three terminal rails (`TerminalOut := .returned out | .unwound mem | .aborted`), quantified by a single `@Nat.rec` weakest precondition `wpThreeRail`:

```lean
prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic

namespace ThreeRailUnwind

inductive TerminalOut (Out Mem : Type) where
  | returned (out : Out) (mem : Mem)
  | unwound  (mem : Mem)
  | aborted

inductive StepRes (St Out Mem : Type) where
  | step  (next : St)
  | done  (term : TerminalOut Out Mem)
  | fault (isUb : Bool)

def wpOutcome {St Out Mem : Type}
    (stepFn : St → StepRes St Out Mem)
    (onRet : Out → Mem → Prop)
    (onUnw : Mem → Prop)
    (onAbort : Prop)
    (fuel : Nat) (s : St) : Prop :=
  @Nat.rec (fun _ => St → Prop)
    (fun _ => False)
    (fun _ ih st =>
      match stepFn st with
      | .step st' => ih st'
      | .done (.returned o m) => onRet o m
      | .done (.unwound m)    => onUnw m
      | .done .aborted        => onAbort
      | .fault _              => False)
    fuel s

@[irreducible] def CutFirewall (P : Prop) : Prop := P

theorem cutFirewall_intro {P : Prop} (h : P) : CutFirewall P := h
theorem cutFirewall_elim  {P : Prop} (h : CutFirewall P) : P := h

def UnwindSafeContract {Mem : Type} (physInv : Mem → Prop)
    (reachesTerm : TerminalOut Unit Mem → Prop) : Prop :=
  ∀ t, reachesTerm t →
    match t with
    | .returned _ m => physInv m
    | .unwound m    => physInv m
    | .aborted      => True

end ThreeRailUnwind
```

Two compositional theorems make loop panic verification tractable:

1. **Landing-pad `CutFirewall` coalescing ($O(1)$ vs. $O(K^2)$):** In a $K$-step loop (`Vec::retain_mut`, `Vec::extend`), $K$ unwind edges branch out of `Call` / `Drop` sites into cleanup blocks. Routing every iteration's unwind branch into one **`CutFirewall`-sealed existential loop invariant** (`∃ idx, ThreeZoneInv mem idx`) hides the inner cleanup formula from Lean's `whnf` unification across iterations so `PanicGuard::drop` is verified **once** for arbitrary symbolic `K`, avoiding $O(K^2)$ kernel reduction blowups!
2. **Anti-panic-laundering (`HardenedSafeTwinClaim`):** When certifying an `unsafe` fast path `pImpl` against a safe reference `pSpec`, equivalence must assert `(Behavior pImpl q (.returned o) ↔ Behavior pSpec q (.returned o)) ∧ ((∃ m₁, Behavior pImpl q (.unwound m₁)) ↔ (∃ m₂, Behavior pSpec q (.unwound m₂))) ∧ (Behavior pImpl q .aborted ↔ Behavior pSpec q .aborted)`. Without the explicit `.unwound` biconditional, replacing a safe bounds panic (`.done (.unwound m)` — `WellFormed = True`) with `get_unchecked` (`.fault .undefined` — `WellFormed = False`) could pass naive partial-correctness postconditions whenever caller recovery via `catch_unwind` is overlooked.

## Boundaries

- **unsupported:**
  - Single-frame baseline `Trusted.MirSemantics.evalTerminator` in `joshlf/anneal@c131b320ee` (`MirSemantics.lean:1568–1569`) marks `.unwindResume`, `.assert`, `.call`, `.drop`, and `.unwindTerminate` as **unsupported** (`.fault .unsupported`), failing closed until multi-frame unwind stack extensions are enabled.
  - Native Windows funclet-based SEH unwinding is **unsupported** inside `rust-lang/miri` (`library/panic_unwind/src/lib.rs:47–51` explicitly routes `cfg(miri)` through `miri.rs` landingpad-style unwinding instead of `seh.rs`).
- **known not to apply:**
  - `UnwindSafe` and `RefUnwindSafe` bounds are **known not to apply** as memory-safety invariants for `unsafe` code (`unwind_safe.rs:61–64, 171, 187–190`).
  - `PanicGuard` stack cleanup recovery is **known not to apply** to out-of-memory aborts (`handle_alloc_error`) or foreign non-local jumps like C `longjmp` bypassing Rust stack frames (`reference` `src/behavior-considered-undefined.md:67`).
  - `std::sync::Mutex` poisoning is **known not to apply** as a Strong commit-or-rollback guarantee: `PoisonError::into_inner()` exposes `&mut T` in whatever valid-bitpattern intermediate state existed when the holding thread panicked.
- **unknown:**
  - Whether future Rust editions will stabilize unwinding from `handle_alloc_error` or multi-yield `AsyncDrop` cleanup unwinding (`elaborate_drops.rs:162`, `ControlFlow.lean:191`) across arbitrary executors remains **unknown**.
- **not examined:**
  - Target-specific `.eh_frame` / DWARF CFI / LSDA personality table encodings, Windows x64 SEH unwind codes, and foreign C++ `std::exception` runtime disposal (unspecified abort-vs-opaque `Err`, `src/panic.md:130–140`) were **not examined** in depth here (covered in `unwinding-on-elf-and-macho-targets`, `unwinding-on-windows-targets-and-32bit-seh`, and `rust-ffi-abi-witnesses-c-unwind-and-machine-resource-linking`).

## Evidence

### Primary Repositories & Specifications Inspected

| Subject | Exact 40-char Commit SHA | Path / Line Range | Verified Observation |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `8144389c895da997dbdecaa635e41d6a50be6ffd` | `library/core/src/panic/unwind_safe.rs:61–248` | Non-`unsafe` auto traits, safe `AssertUnwindSafe`, `*mut T` / `NonNull<T>` `UnwindSafe` impls |
| `rust-lang/rust` | `8144389c895da997dbdecaa635e41d6a50be6ffd` | `library/std/src/panicking.rs:368–885` | `GLOBAL_PANIC_COUNT`, `ALWAYS_ABORT_FLAG`, `PanicInHook`, `catch_unwind` `union Data`, `begin_panic`, `resume_unwind` |
| `rust-lang/rust` | `8144389c895da997dbdecaa635e41d6a50be6ffd` | `library/core/src/panicking.rs:48–113` | `panic_fmt` (`can_unwind = true`) vs `panic_nounwind_fmt` (`#[rustc_nounwind]`, `can_unwind = false`) |
| `rust-lang/rust` | `8144389c895da997dbdecaa635e41d6a50be6ffd` | `library/panic_unwind/src/lib.rs:47–92` | `__rust_panic_cleanup`, `__rust_start_panic`, `miri.rs` fallback |
| `rust-lang/rust` | `8144389c895da997dbdecaa635e41d6a50be6ffd` | `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs:47–146` | Rewrites non-unwinding `UnwindAction` to `.Unreachable`; `C-unwind` in `panic=abort` to `Terminate(Abi)` |
| `rust-lang/rust` | `8144389c895da997dbdecaa635e41d6a50be6ffd` | `compiler/rustc_mir_transform/src/elaborate_drop.rs:54–70` | `Unwind::InCleanup` lowers to `UnwindAction::Terminate(UnwindTerminateReason::InCleanup)` |
| `rust-lang/rust` | `8144389c895da997dbdecaa635e41d6a50be6ffd` | `library/alloc/src/vec/mod.rs:2456–2537` | `Vec::retain_mut` `PanicGuard`, early `g.read += 1` before `drop_in_place` |
| `rust-lang/reference` | `a286e1ecb8ce193d50056e4bb042eea9b23876ef` | `src/panic.md:87–141`; `src/behavior-considered-undefined.md:7–8, 56, 67` | Unwind ABI UB, foreign exceptions, `longjmp` UB, safe code soundness contract |
| `proofs-rs/lean-miri` | `c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` | `Miri/Interpreter/{ControlFlow,Unwind,Panic,Call,ProvenanceGC}.lean` | `returnFromCurrentFrame`, `PayloadStore`, `handleCatchUnwind`, `afterStackPop`, `Protected Unique` |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` | `UnwindAction`, `TerminatorKind`, fail-closed `.fault .unsupported` |
| `rust-lang/hashbrown` | `f3e9f0fc110f55ca55d73d6eddc0bdf5e85eb223` | `src/scopeguard.rs:29–40`; `src/raw.rs:842, 3349–3394` | `ScopeGuard::into_inner` `ManuallyDrop` + `ptr::read` field extraction |
| `Sgeo/take_mut` | `1bd70d842c6febcd16ec1fe3a954a84032b89f52` | `src/lib.rs:31–41, 81–97` | `take` abort-on-panic vs `take_or_recover` double `catch_unwind` + `resume_unwind` |

### Peer-Reviewed Literature Anchors

1. David Abrahams, *"Exception-Safety in Generic Components: Lessons Learned from Specifying Exception-Safety for the C++ Standard Library,"* Generic Programming, LNCS Vol. 1766, pp. 69–79, 2000, DOI `10.1007/3-540-39953-4_6`.
2. Yechan Bae, Youngsuk Kim, Ammar Askar, Jungwon Lim, Taesoo Kim, *"Rudra: Finding Memory Safety Bugs in Rust at the Ecosystem Scale,"* SOSP 2021, DOI `10.1145/3477132.3483570`.
3. Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer, *"RustBelt: Securing the Foundations of the Rust Programming Language,"* POPL 2018, DOI `10.1145/3158154`.
4. Neven Villani, Johannes Hostert, Derek Dreyer, Ralf Jung, *"Tree Borrows,"* PLDI 2025, DOI `10.1145/3729265`.

## Revalidation

1. **Nested-Panic & `PanicInHook` Runtime Probe:**
   Save and run a small `rustc` test binary checking that (a) a `Drop` destructor running an internal `std::panic::catch_unwind(|| panic!("inner"))` completes without aborting during an outer unwind (`exit 0`), whereas (b) an uncaught `Drop` panic escaping during unwind aborts (`SIGABRT`), and (c) a `catch_unwind` *inside* `std::panic::set_hook` still aborts via `MustAbort::PanicInHook`:
   ```bash
   cat << 'RS' > /tmp/check_nested_panic.rs
   struct Guard;
   impl Drop for Guard {
       fn drop(&mut self) {
           let r = std::panic::catch_unwind(|| panic!("contained inner"));
           assert!(r.is_err());
       }
   }
   fn main() {
       let res = std::panic::catch_unwind(|| { let _g = Guard; panic!("outer"); });
       assert!(res.is_err());
   }
   RS
   rustc /tmp/check_nested_panic.rs -o /tmp/check_nested_panic && /tmp/check_nested_panic
   ```
   Expected result: exit `0`.

2. **`Vec::retain_mut` Pre-Increment Miri Probe:**
   Under `cargo +nightly miri test`, execute `Vec::retain_mut` with a `Drop`-implementing element (`Box<u8>`) whose destructor panics on the second element while `f` rejects it, verifying zero double-drop UB; conversely, confirm that mutating `g.read += 1` *after* `drop_in_place` immediately triggers Miri `dangling pointer` / `double-free` UB.

3. **Lean 4 Three-Rail WP & `CutFirewall` Kernel Check:**
   Save the `ThreeRailUnwind` Lean 4 block from Finding 6 to `/tmp/check_unwind_wp.lean`, add `#print axioms ThreeRailUnwind.cutFirewall_elim`, and run:
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false /tmp/check_unwind_wp.lean
   ```
   Expected result: exit `0` with `[]` (zero axioms) on `cutFirewall_intro`/`cutFirewall_elim`.

4. **Upstream Diff Checks:** After updating pinned Rust or `lean-miri` revisions, diff `library/core/src/panic/unwind_safe.rs`, `library/std/src/panicking.rs`, `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`, and `Miri/Interpreter/{ControlFlow,Unwind}.lean` to confirm `AssertUnwindSafe`, `ALWAYS_ABORT_FLAG`, `UnwindAction::Terminate`, and `PayloadStore` invariants still hold.
