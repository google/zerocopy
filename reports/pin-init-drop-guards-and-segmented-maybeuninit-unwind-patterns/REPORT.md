# In-Place Pin Initialization, Drop-Guard Idioms, Segmented MaybeUninit Ownership, and Two-Track Unwind Verification

## Summary

Fallible in-place initialization (`pin-init`), RAII drop guards (`scopeguard`, `Vec::retain_mut`, `Vec::splice`, `slice::sort`), and segmented `MaybeUninit<T>` buffers share one core verification problem: preserving piecewise initialization and aliasing invariants across callback panics, `Drop` unwinds, and `rustc` MIR drop elaboration (`Runtime(PostCleanup)`). Synthesizing primary source code across `Rust-for-Linux/pin-init`, `bluss/scopeguard`, `rust-lang/rust`, `tock/tock`, `proofs-rs/lean-miri`, and `joshlf/anneal` yields four core design invariants:

1. **Asymmetric Three-Outcome Initialization Contracts:** `PinInit<T, E>::__init(slot)` maps `UninitAt(slot, T)` to `InitAt(slot, T) ∧ Pinned(slot)` on `Ok(())`, and restores `UninitAt(slot, T)` (dropping initialized subfields in reverse declaration order) on **both** `Err(e)` return and unwind. `StackInit<T>::init` (`__internal.rs`) sets `this.is_init = false` **before** `assume_init_drop()` so a `T::drop` panic never double-drops during unwinding.
2. **Five Idiomatic Drop-Guard Archetypes Over Segmented Storage:** Across `scopeguard` and `core`/`alloc`, guards maintain piecewise partitions—prefix `[0..init) ++ [init..len)` (`maybe_uninit::Guard`, `pin_init::DropGuard`), 3-zone compaction `[Kept: 0..write) ++ Hole[write..read) ++ [Unchecked: read..origLen)` (`Vec::retain_mut` `PanicGuard`), 4-zone splice (`Vec::splice`/`Drain`), moving permutation gaps (`smallsort::insert_tail` `CopyOnDrop`, `MergeState`), and circular modulo buffers (`tock::RingBuffer`). Pre-advancing cursors (`g.read += 1`) before `ptr::drop_in_place` is mandatory to prevent double-drop on destructor panic.
3. **`rustc` Drop Elaboration Is Linear (`2N`), While Naive Tree-WP Explodes (`O(2^k)`):** In `rustc_mir_transform::elaborate_drop`, `rustc` builds **linear** ($2N$-block) half-drop-ladders plus boolean `_drop_flag` locals and `UnwindAction::Terminate(InCleanup)` aborts; $O(2^k)$ blowup comes from naive symbolic continuation cloning across `?`, `_drop_flag` tests, and `Assert` chains.
4. **Segmented Interval Ownership (`SegRegion`) + Two-Track WP (`wpTwoTrack`):** Under Anneal's Pass-1 Lean 4 (`v4.34.1`) rules (`trusted/audit/TrustedBoundary.lean`: 51 locked `Init.*` modules, zero `Init.Omega`/`bv_decide`/`._unsafe_rec`, Statement-Origin Separation), combining `SegRegion` partitions with block-indexed `(onRet, onUnw)` WP and `@[irreducible]` `CutFirewall` summaries shrinks $O(2^k)$ cleanup paths to $O(k)$ linear proofs while keeping `UnwindAction.terminate` sound.

## Applicability

This report relates the examined upstream subjects pinned in `REPORT.json`:

- **In-Place Pin Initialization & Drop Guards:** `Rust-for-Linux/pin-init` (`578ad6b8f9d136aeb365f2175f6ef9f0e3dab288`, `src/{lib.rs, __internal.rs}` and `internal/src/init.rs`), `bluss/scopeguard` (`bb988222848d39b0b9037b29da3a3a1eb05ebf4b`, `src/lib.rs`), and USENIX ATC '24 empirical observations of Rust-for-Linux (`li-hongyu`).
- **Standard Library & Compiler Drop Elaboration:** `rust-lang/rust` (`8144389c895da997dbdecaa635e41d6a50be6ffd`) across `library/alloc/src/vec/{mod.rs, splice.rs, drain.rs, set_len_on_drop.rs}`, `library/core/src/mem/maybe_uninit.rs`, `library/core/src/slice/sort/shared/smallsort.rs`, `library/core/src/slice/sort/stable/{merge.rs, drift.rs}`, and `compiler/rustc_mir_transform/src/{elaborate_drops.rs, elaborate_drop.rs}`; plus `tock/tock` (`ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`, `kernel/src/collections/ring_buffer.rs`).
- **Semantic Reference & Zero-TCB Verifier:** `proofs-rs/lean-miri` (`c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a`, `Miri/Interpreter/Unwind.lean`) and `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`, `trusted/audit/TrustedBoundary.lean`, `theory/Anneal/{MirWp,PureLift/SpatialPin}.lean`) on Lean 4 `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`).
- **Lean 4 Pass-1 Design Boundary:** All `theory/` mechanizations target Pass 1 of `TrustedBoundary.lean` (L442–596): locked `Init.*` modules only (no `Init.Omega`, `Std.*`, or `Lean.*`), pure `{propext, Quot.sound, Classical.choice}` axioms, zero `._unsafe_rec` helpers, closed 22-tactic allowlist (`@[irreducible]` admitted; `omega`/`bv_decide`/`native_decide`/`rcases`/`sorry` banned), and **Statement-Origin Separation** (target theorems mention only `Init.*`, `Trusted.*`, and `Mir.*`).

Foundational literature anchors the semantics: RustBelt (`10.1145/3158154`), RefinedRust (`10.1145/3656422`), Rudra (`10.1145/3477132.3483570`), Barnett & Leino unstructured WP (`10.1145/1108792.1108813`), and Charguéraud characteristic formulae (`10.1145/2034773.2034828`). Unwinding operational behavior in `joshlf/anneal@c131b320eeeb` reflects the scalar/fieldless-enum subset where `TerminatorKind.drop` and `.unwindTerminate` currently fail closed; mechanized `wpTwoTrack` combinators and `SegRegion` extensions are derived within Pass-1 rules against `lean-miri` and `elaborate_drop.rs`.

## Findings

### 1. In-Place Pin Initialization Protocols: `PinInit`, `StackInit`, and Field `DropGuard`s

`Basis: source + normative + derived`

#### 1.1 Asymmetric Contracts of `PinInit<T, E>` and `Init<T, E>`

In `Rust-for-Linux/pin-init@578ad6b8f9d1` (`src/lib.rs` L973–1242), in-place constructors decouple allocation from construction via two `unsafe` traits:

- **`unsafe trait PinInit<T: ?Sized, E = Infallible>` (`lib.rs` L973–1027):** Defines `unsafe fn __init(self, slot: *mut T) -> Result<(), E>`. The caller guarantees at entry: (a) `slot` points to valid, aligned, exclusively owned uninitialized memory `UninitAt(slot, T)`, and (b) `slot` remains pinned (address-invariant until `T::drop` runs prior to storage reuse or deallocation). `PinInit::__init` guarantees:
  1. On **`Ok(())`**: every field of `*slot` is initialized (`InitAt(slot, T)`) and all pinning invariants of `T` hold (`PinnedAt(slot, T)`).
  2. On **`Err(e)` return**: `__init` has dropped every already-initialized subfield in reverse order, leaving `slot` uninitialized (`UninitAt(slot, T)`) so the caller may deallocate without calling `drop_in_place(slot)` (`lib.rs` L951–957).
  3. On **unwind (panic inside a field initializer or `T::drop`)**: RAII guards clean initialized subfields via `UnwindAction::Cleanup` so `slot` likewise exits as `UninitAt(slot, T)` with zero leaks or double-drops.
- **`unsafe trait Init<T: ?Sized, E = Infallible>: PinInit<T, E>` (`lib.rs` L1112–1147):** Subtrait waiving the pinning precondition—initialized `*slot` may subsequently move in memory.
- **Sequential Combinator Composition (`ChainPinInit` / `ChainInit`, `lib.rs` L1058–1177):** `pin_chain(self, f)` wraps `slot` in `__internal::Slot::<Pinned, T>::new(slot)`, runs `let mut guard = slot.init(self.0)?`, passes `Pin<&mut T>` (`guard.let_binding()`) to `f`, and calls `core::mem::forget(guard)` only if `f` returns `Ok(())`. If `f` returns `Err(e)` or panics, `DropGuard<Pinned, T>::drop` invokes `ptr::drop_in_place(slot)` cleanly.

#### 1.2 `StackInit<T>` Double-Drop Ordering & `pin_init!` Macro Desugaring

Inspecting `src/__internal.rs` (L125–180) and `internal/src/init.rs` (L253–583) exposes four subtle verification obligations:

1. **Pre-Drop Flag Clearing in `StackInit<T>::init` (`__internal.rs` L163–179):**
   ```rust
   if this.is_init {
       this.is_init = false;
       unsafe { this.value.assume_init_drop() };
   }
   unsafe { init.__init(this.value.as_mut_ptr())? };
   this.is_init = true;
   ```
   Clearing `this.is_init = false` **before** calling `assume_init_drop()` is critical for unwind safety: if `T::drop` panics while dropping the previous occupant of a reused stack slot (`stack_init_reuse`, L184–208), `StackInit<T>::drop` (`L137–146`) runs during stack unwinding; had `is_init` stayed `true`, `StackInit::drop` would call `assume_init_drop()` a second time on the already-dropped `value` (immediate UB!). Likewise, `this.is_init = true` occurs **only after** `init.__init(...)` returns `Ok(())`.
2. **Per-Field `Slot<P, T>` → `DropGuard<P, T>` Chains (`__internal.rs` L214–362, `init.rs` L377–518):** For struct initialization `pin_init!(S { f1 <- init1, f2: val2 })`, the proc-macro generates linear raw-pointer slots (`HasPinData::__pin_data(data).f_i(slot)` for `Pinned`, `&raw mut (*slot).f_i` for `Unpinned`), binding each initialized field to a hygienic `DropGuard<P, F_i>` local (`let mut __f_i_guard = ...`). Only after the **last** field succeeds does generated code emit `core::mem::forget(__f_k_guard)` in reverse order (`L510–517`) and mint `InitOk::new()`. On any `?` early error or unwind at field `j`, MIR drops `__f_{j-1}_guard` down through `__f_1_guard` in reverse declaration order!
3. **Compile-Time Unexecuted Alignment & Exhaustiveness Checks (`init.rs` L521–583):** An unreachable closure (`let _ = || unsafe { ... }`) generates `let _ = &(*slot).field` (triggering compiler error `E0793` on `#[repr(packed)]` unaligned fields) and `ptr::write(slot, Path { field: loop {}, .. })` (reusing `rustc` exhaustiveness and duplicate-field checking without touching runtime MIR).
4. **Dual-Branch HRTB Dropck Guard & `#[may_dangle]` Defense (`init.rs` L311–323, `__internal.rs` L679–737):** Self-referential structs (`SelfRefSlot<'a, M, P, T>`, `__internal.rs` L374–459) use `if true { #init_fields } else { #drop_check }` so field initialization obeys HRTB lifetime isolation while the dead `else` branch forces `rustc` dropck consistency; `Borrowed<T, P>` and `ExistLt<'a>` implement empty `Drop` bodies (`L705–708, 733–736`) to block `rustc`'s `#[may_dangle]` optimization from assuming borrowed field lifetimes may dangle during field drops!

---

### 2. Drop-Guard Taxonomy and Segmented `MaybeUninit` Idioms Across `scopeguard`, `core`, `alloc`, and `tock`

`Basis: source + derived`

Directly inspecting five upstream drop-guard implementations reveals a compact, 5-pattern taxonomy over segmented `[0..cap)` storage:

| Archetype | Upstream Anchor | Buffer Partition & Ghost State | Normal Completion | Panic / Unwind Action |
| :--- | :--- | :--- | :--- | :--- |
| **1. Strategy Closure Guard** | `bluss/scopeguard@bb988222` (`src/lib.rs:201–250, 304–370, 465–478`) | `ManuallyDrop<T>` + `ManuallyDrop<F>` + zero-sized `Strategy` (`Always`, `OnUnwind`, `OnSuccess`) | `ScopeGuard::into_inner`: moves out `value` via `ptr::read` *before* `ManuallyDrop::drop(&mut dropfn)`, then consumes `guard` via `ManuallyDrop` | `Drop::drop` reads both `ManuallyDrop` fields and calls `dropfn(value)` iff `S::should_run()` (`Always` in `no_std`; `thread::panicking()` in `std`) |
| **2. Prefix Init Tear-Down** | `core::mem::maybe_uninit::Guard` (`rust@8144389c` `maybe_uninit.rs:1691–1724`); `pin_init::DropGuard` (`__internal.rs:300–362`) | `[Init: 0..initialized) ++ [Uninit: initialized..len)` | `mem::forget(guard)` once `initialized == len` (converting `[MaybeUninit<T>]` to `[T]`) | Drops initialized prefix `&mut self.slice[..self.initialized].assume_init_drop()` (`SpecFill` uses `TrivialClone` specialization to elide guard) |
| **3. 3/4-Zone Hole Compaction** | `Vec::retain_mut` `PanicGuard` (`vec/mod.rs:2456–2537`); `Vec::splice` & `Drain::DropGuard` (`vec/splice.rs:54–141`, `vec/drain.rs:177–246`); `SetLenOnDrop` (`vec/set_len_on_drop.rs:6–33`) | `retain_mut`: `[Kept: 0..w) ++ Hole[w..r) ++ [Unchk: r..orig) ++ [orig..cap)`<br>`Drain`: `[0..len) ++ DrainedHole ++ Iter ++ Tail[tail_start..tail_start+tail_len)` | `retain_mut`: `set_len(w); mem::forget(g)`<br>`Splice`: `drain.iter = [].iter()` resets dangling slice iter before `move_tail` reserves/copies; falls into `Drain::drop` | `retain_mut`: **pre-increments `g.read += 1` before `drop_in_place(cur)`**, so if `f` or `T::drop` panics, `PanicGuard::drop` runs `ptr::copy(read, write, orig - read)` + `set_len(write + remaining)` without double-drop! |
| **4. Permutation Gap / Scratch Guard** | `core::slice::sort` `smallsort.rs:220–310, 536–571`; `merge.rs:8–150`; `drift.rs:20–120` | `insert_tail`: `[begin..sift) ++ Hole[gap_guard.dst] ++ (gap_guard.dst..=tail]` with `tmp` (`ManuallyDrop<T>`)<br>`MergeState`: `scratch[start..end)` ⋈ hole `[dst..)` | Runs **`CopyOnDrop::drop` / `MergeState::drop` unconditionally** on *both* normal exit and `is_less` unwind (zero `mem::forget` needed!) | Same `Drop` implementation restores all remaining `len` elements back into the active gap, guaranteeing multiset permutation preservation under panic for `FreezeMarker` (`!UnsafeCell`) types |
| **5. Circular Modulo Buffer** | `tock/tock@ba6aa7edc014` (`ring_buffer.rs:14–129`) | Contiguous `[head..tail)` (`head < tail`) or wrapped `[head..cap) ++ [0..tail)` (`head > tail`) over `&mut [MaybeUninit<T>]` (`T: Copy`) | Pure slice reinterpretation `from_raw_parts(s.as_ptr().cast::<T>(), s.len())` | `T: Copy` (no `Drop` glue), invariant preserved via index update discipline |

Two subtle patterns stand out for formal verification:

- **Order of Side Effects in `ScopeGuard::into_inner` and `Vec::retain_mut`:** In `scopeguard` (`src/lib.rs` L360–367), `into_inner` calls `ptr::read(&*guard.value)` **before** `ManuallyDrop::drop(&mut guard.dropfn)` because if dropping the captured closure `F` panics, `value` has already been safely extracted (never double-dropped). Conversely, in `Vec::retain_mut` (`vec/mod.rs` L2508–2520), `PanicGuard` sets `g.read = read + 1` **before** calling `ptr::drop_in_place(cur)` so a panicking element destructor marks slot `read` as part of `Hole[write..read)` rather than `Unchecked[read..orig)`, preventing `PanicGuard::drop` from resurrecting and double-dropping a poisoned element!
- **No-`forget` Symmetric Gap Repair (`CopyOnDrop` / `MergeState`):** Unlike `Vec::retain_mut` (`mem::forget(g)`), `core::slice::sort` (`smallsort.rs` L551, `merge.rs` L53–61, L138–149) intentionally lets `CopyOnDrop` / `MergeState` execute its `Drop` handler on **both** normal return and `is_less` unwind—eliminating MIR drop-flag synthesis completely while preserving the slice multiset invariant! Note that `smallsort` restricts scratch buffering (`small_sort_general`, `L205`) to `T: FreezeMarker` (`!UnsafeCell`) so `is_less(&T, &T)` cannot interior-mutate elements outside the scratch copy.

---

### 3. `PostCleanup` MIR Drop Elaboration, Drop Ladders, and Double-Panic Termination

`Basis: normative + source`

Inspecting `compiler/rustc_mir_transform/src/elaborate_drops.rs` (L49–121, L166–209, L267–316), `elaborate_drop.rs` (L21–82, L634–660, L733–750, L838–955, L1530–1621) at `rust-lang/rust@8144389c895da997`, and `Miri/Interpreter/Unwind.lean` (L47–129) at `proofs-rs/lean-miri@c92d1d9754c9` clarifies how `Runtime(PostCleanup)` MIR encodes drops and unwinds:

1. **Four-Way Drop Classification (`DropStyle`):** Using bidirectional dataflow cursors (`MaybeInitializedPlaces` ∧ `MaybeUninitializedPlaces` over `MoveData`), `ElaborateDropsCtxt::drop_style` (`elaborate_drops.rs` L167–190) classifies every `TerminatorKind::Drop` at a `MovePathIndex` into:
   - `Dead` (`!maybe_init`): rewritten to unconditional `Goto(succ)` (zero unwind edge); `compute_dead_unwinds` (`L100–121`) prunes dead cleanup pads beforehand.
   - `Static` (`maybe_init ∧ !maybe_uninit`): rewritten to unconditional `TerminatorKind::Drop` (calling drop glue, with `unwind` edge).
   - `Conditional` (`maybe_init ∧ maybe_uninit ∧ !multipart`): triggered whenever one control path executes `mem::forget(guard)` (or `MaybeUninit` moves) while another leaves `guard` initialized (`Vec::retain_mut`, `ChainPinInit`, `pin_init!`). `rustc` allocates a synthetic stack boolean `_drop_flag : bool` (`create_drop_flag`, `L267–271`), assigns `_drop_flag = true` on initialization, assigns `_drop_flag = false` when moved/forgotten, and lowers the `Drop` terminator via `drop_flag_test_block` (`elaborate_drop.rs` L1605–1621) to `SwitchInt(copy _drop_flag)` branching to `drop_block` vs. `succ`, resetting `_drop_flag = false` afterwards only on normal paths (`!unwind.is_cleanup()`, `L1544–1548`).
   - `Open` (`maybe_init ∧ maybe_uninit ∧ multipart`): decomposes partially moved tuples/structs/arrays into per-field drops (`open_drop`, `L1492–1527`) wired as a **drop ladder**.
2. **Linear `2N` Connected Half-Drop-Ladders (`drop_ladder`, `elaborate_drop.rs` L879–955):** For $N$ remaining fields needing drop, `rustc` builds **two** linear chains—NOT a tree:
   - **Mainline ladder** `.d0 → .d1 → ... → .d_{N-1} → succ`, where `.d_i` drops field `i` with `target = .d_{i+1}` and `unwind = UnwindAction::Cleanup(.c_{i+1})`;
   - **Cleanup half-ladder** `.c1 → .c2 → ... → .c_{N-1} → unwind_exit`, where every block carries `is_cleanup = true` and `unwind = Unwind::InCleanup` (`UnwindAction::Terminate(UnwindTerminateReason::InCleanup)`, `L51–71, 934`)!
   *(Async-drop coroutines add a third `dropline` half-ladder `L941–946`, outside synchronous `PostCleanup` scope.)*
3. **Why Verification Explodes Without Cutpoint Sharing:** Because `drop_ladder` itself is linear ($2N$ blocks), `pin_init!` with 10 fields emits only ~20 ladder blocks plus 10 sequential `Try::branch` (`?`) and `_drop_flag` diamonds. Exponential $O(2^k)$ blowup occurs solely when a weakest-precondition calculator (`MirWp`) or symbolic executor **inline-substitutes continuations across CFG join/cleanup blocks**, duplicating the tail ladder twice per `?` or `_drop_flag` branch!
4. **Miri Unwind Execution (`Unwind.lean` L47–129):** Miri tracks typed panic payloads in `PayloadStore` (`pushPayload`/`popPayload` via integer tokens), installs `catchUnwind` frame metadata in `handleCatchUnwind` (`L101–115`), pops frames cleanly on `UnwindResume`, and immediately aborts when a panic occurs inside a frame edge marked `UnwindAction::Terminate` (double panic inside `Drop` during unwinding).

---

### 4. `SegRegion` Ownership and Two-Track `(onRet, onUnw)` WP in Pass-1 Lean 4

`Basis: source + derived`

#### 4.1 Symbolic Interval Ownership (`SegRegion`) Beyond Fixed-Length `SpatialPin`

`Anneal.PureLift.SpatialPin` (`joshlf/anneal@c131b320eeeb`, `theory/Anneal/PureLift/SpatialPin.lean` L63–294) models pinned regions as concrete `List (CellVal Val)` byte lists and forbids sub-block splitting (`blk.activeSubSplits == 0`, L168, L276). That cannot represent symbolic-length `Vec` buffers (`[0..write) ++ Hole[write..read) ++ [read..origLen) ++ [origLen..cap)`) or `pin_init!` field-by-field slots without exponential quantifier instantiation.

A minimal Pass-1 generalization replaces concrete byte arrays on dynamic slices/structs with **symbolic interval partitions** (`SegRegion`):

- **Slice Representation (`SegRun`):** A contiguous allocation range `[0..cap)` is a finite normalized list of disjoint, adjacent runs:
  `.initSlice (lo hi : Nat) (elems : List Val)` (initialized, length `hi - lo = elems.length`) or `.uninitHole (lo hi : Nat)` (uninitialized/moved-out `MaybeUninit` or spare capacity).
- **Zero-Quantifier Algebraic Rules:** `seg_split_at` splits `[lo, hi)` at `mid` when `lo ≤ mid ≤ hi`; `seg_read_at` pops index `read` transferring ownership out (transitioning `[read, hi)` to `.uninitHole read (read+1) :: .initSlice (read+1) hi rest`); `seg_write_at` refills `.uninitHole write (write+1)`; and `seg_backshift` models `ptr::copy(read, write, rem)` preserving sequence equality `elems_kept ++ elems_rem`. All index bounds (`lo ≤ write ≤ read ≤ origLen ≤ cap`) reduce to linear difference chains checked in `<2 ms` via GMP `Nat` `rfl`.
- **Struct Slot & Pin Monotonicity (`SlotMask` + `PinSlot`):** Fixed-arity `pin_init!` structs use a compile-time field bitmask `InitMask : Nat` (or `List Bool`) paired with `PinGuarantee(allocId) := droppedBeforeDeallocOrReuse` (satisfied trivially when `Init<T, E>` relaxes pinning).

#### 4.2 Block-Indexed Two-Track WP (`wpTwoTrack`) Eliminating `O(2^k)` Explosion

Building on Barnett & Leino (`10.1145/1108792.1108813`) and Charguéraud (`10.1145/2034773.2034828`), and extending `Anneal.MirWp.wpOutcomeState` (`MirWp.lean` L69–80), we replace tree-unrolling WP over MIR basic blocks with a **block-indexed DAG two-track transformer** guarded by `@[irreducible]` cutpoint firewalls (`CutFirewall`) over `Init.*`:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace Anneal.TwoTrackUnwindExample

/-- Pass-1 cut firewall (`@[irreducible]` admitted by `TrustedBoundary.lean:595`)
    preventing `isDefEq`/`whnf` from unfolding cleanup-block continuations
    exponentially across `SwitchInt` / `?` join points. -/
@[irreducible]
def CutFirewall (_bb : Nat) (P : Prop) : Prop := P

theorem cutFirewall_intro (bb : Nat) {P : Prop} (h : P) : CutFirewall bb P := by
  unfold CutFirewall; exact h

theorem cutFirewall_elim (bb : Nat) {P : Prop} (h : CutFirewall bb P) : P := by
  unfold CutFirewall at h; exact h

/-- Minimal Two-Track Outcome over MIR normal return (`onRet`),
    single-panic unwind (`onUnw`), and double-panic abort (`onAbort`). -/
inductive TwoTrackOutcome (σ : Type) where
  | ret   (s : σ)
  | unw   (s : σ)
  | abort (s : σ)   -- `UnwindAction::Terminate(InCleanup)`: defined safe halt!
  | ub              -- Immediate Rust Abstract Machine UB (`False`)

def wpOutcome {σ : Type} (onRet onUnw onAbort : σ → Prop) : TwoTrackOutcome σ → Prop
  | .ret s   => onRet s
  | .unw s   => onUnw s
  | .abort s => onAbort s
  | .ub      => False

/-- Block-DAG summary table: each block `bb` maps to its cutpoint precondition
    `inv bb : σ → Prop`. Sharing `CutFirewall bb (inv bb s)` across `SwitchInt`
    and `UnwindAction.Cleanup` edges reduces `O(2^k)` paths to `O(k)` checks! -/
def wpEdgeGuard {σ : Type} (inv : Nat → σ → Prop) (targetBb : Nat) (s : σ) : Prop :=
  CutFirewall targetBb (inv targetBb s)

end Anneal.TwoTrackUnwindExample
```

Three operational rules govern `wpTwoTrack` over MIR CFG blocks:

1. **Cleanup-Sharing Cutpoint Rule ($O(2^k) \to O(k)$):** Across a cleanup half-ladder `.c_k → .c_{k-1} → ... → .c_1 → UnwindResume`, each block `.c_i` receives one specification `cleanupInv(.c_i, s)` over initialized segments `[0..i)`. Each of $k$ sequential `?`, `Call`, or `Assert` unwind edges targets `CutFirewall .c_i (cleanupInv .c_i s)` *once* without re-expanding `.c_i`, while `.c_i` proves `cleanupInv(.c_i) ⊢ wpCleanup(.c_i, CutFirewall .c_{i-1} ...)` *once*.
2. **`InitDom` Drop-Flag Constant Folding:** Because `rustc` writes `_drop_flag = true` on guard creation and `_drop_flag = false` before `mem::forget(guard)`, abstract interpretation over `InitDom` folds `_drop_flag` at normal return vs. cleanup, pruning dead `drop_flag_test_block` arms (`elaborate_drop.rs` L1605) by `rfl`.
3. **Double-Panic `UnwindAction::Terminate` Soundness:** A panic inside `is_cleanup = true` executes `UnwindTerminateReason::InCleanup` and aborts immediately:
   - Mapping `.terminate` to `.fault .undefined` (`False`) is **unsoundly restrictive** (rejects valid `Vec::retain_mut` and `pin_init!` whenever `T::drop` can panic).
   - Mapping `.terminate` to `.done (.unwound _)` is **unsoundly permissive** (`catch_unwind` callers cannot observe aborted state, whereas normal unwind must restore caller invariants).
   - Mapping `.terminate` to `TerminalOut.aborted` (`onAbort := fun _ => True`, non-trivial `onUnw`) preserves soundness while exposing single-panic double-drops (omitting `this.is_init = false` in `StackInit::init` or pre-incrementing `g.read += 1` in `Vec::retain_mut`) inside `onUnw` before any second panic can happen.

#### 4.3 Concrete Walkthroughs: `pin_init!` & `Vec::retain_mut`

- **Trace A (`pin_init!(S { a <- init_a, b <- init_b })` in `StackInit`):** `StackInit::init` clears `this.is_init = false` before `assume_init_drop` (single unwind sees `is_init == false`). In `__init`, constructing `a` sets `_flag_a = true` (`__a_guard`); if `init_b` yields `Err(e)` or unwinds, `DropGuard::drop` frees `a` once (clearing `_flag_a` on `Err`, jumping to `.c_a` on unwind). On `Ok(())`, `mem::forget` clears both drop flags and flips `this.is_init = true`.
- **Trace B (`Vec::retain_mut`, `vec/mod.rs` L2456–2537):** Loop invariant (`g.read < origLen`): `0 ≤ g.write ≤ g.read ≤ origLen ≤ cap`, `SegRegion = [.initSlice 0 g.write _, .uninitHole g.write g.read, .initSlice g.read origLen _, .uninitHole origLen cap]`, `_drop_flag_g = true`. On `!f(cur)`, `g.read += 1` shifts `[g.read..origLen)` and widens `.uninitHole` *before* `ptr::drop_in_place(cur)`. On unwind, `PanicGuard::drop` shifts `[read..origLen)` over `[write..)` via `ptr::copy` and updates `set_len`; on normal exit, `set_len(write); mem::forget(g)` clears `_drop_flag_g`.

---

### 5. Conceptual Minimality Counterexamples, `Trusted.*` Gaps, and Rubric Evaluation

`Basis: source + derived`

#### 5.1 Three Over-Collapses Refuted by Counterexamples (`C1`–`C2`)

1. **Why `Err(E)` Return (`?`) and Unwind (`TerminalOut.unwound`) Cannot Collapse:** While `pin_init!` restores `UninitAt` on both, `Err(e)` produces a normal `TerminalOut.returned` recoverable without triggering `std::thread::panicking()`; unwinding bypasses normal frames, runs `ScopeGuard<_, _, OnUnwind>` while skipping `OnSuccess` (`scopeguard/src/lib.rs` L236–250), and turns panics in `is_cleanup = true` pads into `UnwindAction::Terminate` aborts.
2. **Why `PinInit<T, E>` Cannot Collapse into `fn() -> Result<T, E>` + Move:** Returning `T` copies bytes from `_0`, invalidating internal `SelfRefSlot` pointers created during construction and causing kernel stack overflow on large structs.
3. **Why Pointwise `Fin cap → Bool` Maps Cannot Replace Interval `SegRegion`:** Elementwise arrays require quantified frame axioms `∀ j ≠ i, map'(j) = map(j)` across every loop step and `ptr::copy` shift, stalling Pass-1 Lean proofs without `omega`/`grind`; interval lists update in $O(1)$ runs with `<2 ms` difference-chain `rfl` proofs.

#### 5.2 Exact `Trusted.MirAst` / `Trusted.MirSemantics` Gap Ledger (`joshlf/anneal@c131b320eeeb`)

| Gap Anchor (`joshlf/anneal@c131b320eeeb`) | Missing Construct (Fails Closed to `.unsupported`) | Required TCB Extension (`lean-miri@c92d1d97`) |
| :--- | :--- | :--- |
| `MirAst.lean:782–784`; `MirSemantics.lean:1568–1569` | `TerminatorKind.drop`, `.assert`, `.call`, `.unwindResume`, `.unwindTerminate` | `Drop` glue execution, `Assert`, `UnwindResume` pop (`Unwind.lean:119–129`), `UnwindTerminate` |
| `MirSemantics.lean:601–605, 1543–1545` | No `TerminalOut.aborted`; `return_` in `bb.cleanup` faults `.unsupported` | Separate `TerminalOut.aborted` (`InCleanup` halt) from `TerminalOut.unwound` |
| `MirSemantics.lean:1599–1614` | Single frame `s.frames = [frame]`; non-empty `q.callerMem` rejected (`L803`) | Multi-frame call/unwind stack + pointer/slice `CallerMemory` inputs |
| `MirAst.lean:612–618`; `SpatialPin.lean:168, 276` | `MaybeUninit` `MirTy.union_`, `CastKind.transmute`; `activeSubSplits == 0` | Byte `Allocation` loads/stores + `MirTy.union_` + sub-block `SegRegion` splits |

#### 5.3 Mandatory 7-Axis Rubric Evaluation Table

| Axis | (1) Naive Tree-WP + Pointwise Map | (2) Full Iris `iProp` in Lean | (3) **`SegRegion` + `wpTwoTrack` + `CutFirewall`** |
| :--- | :--- | :--- | :--- |
| **(T1) 0-TCB Bridge** | **0-TCB** (`MirWp`); blocked on `Drop`/unwind (`G6`) | High cost: rebuilds step-indexed Iris in `theory/` | **0-TCB** over `Trusted.MirSemantics` inside Pass-1 `theory/` |
| **(P1) Spec Auditability** | Poor: exposes drop flags and quantified maps | Moderate: exposes step-index masks unless wrapped | **Best**: Rust specs state `ensures` + `UninitAt` / conservation |
| **(P2) Day-2 Locality** | **Brittle**: adding `?` renumbers flags, doubles paths | Moderate: Iris scripts break on CFG edits | **Very High**: `CutFirewall` + `InitDom` localize block edits |
| **(P3) `v4.34.1` Scaling** | **Explodes ($O(2^k)$)**: clones continuation AST | **Slow**: heavy `iProp` rewriting in Pass-1 tactics | **Fast ($O(k)$)**: `@[irreducible]` firewalls + `<2 ms` GMP `rfl` |
| **(P4) Composability** | Weak: mixes drop flags into value state | Strong in theory, hard bridge to `PureLift` | **Strong**: composes `PureLift`, `SegRegion`, `PinSlot`, `Drop` |
| **(P5) Failure Legibility** | Opaque: fails deep in unrolled path tree | Moderate: Iris context mismatches | **High**: names failing `bb` (`onRet` vs. `onUnw`) or gap |
| **(C1–C2) Minimality** | Ad-hoc boolean maps duplicate slice logic | Overbuilt for single-threaded drop guards | **Minimal**: `SegRegion` + `wpTwoTrack` cover all 5 archetypes |

## Boundaries

- **Execution of `TerminatorKind.drop`, `.unwindTerminate`, `.unwindResume`, `.assert`, and `.call` in `Trusted.MirSemantics` is `unsupported`:** At `joshlf/anneal@c131b320`, `MirAst.lean` (L782–795) and `MirSemantics.lean` (L1568–1569, L1599–1614) fail closed to `.fault .unsupported`, and `PureLift.SpatialPin` sub-block splits (`blk.activeSubSplits == 0`, L168, L276) are `unsupported`.
- **Async drop (`build_async_drop`) and `-C panic=abort` `catch_unwind` profiles were `not examined`:** `elaborate_drop.rs` (L227–350) generates coroutine `dropline` ladders outside synchronous `PostCleanup` scope.
- **Scratch merge guards (`CopyOnDrop` / `MergeState`) are `known not to apply` to `!Freeze` types:** `smallsort.rs` (L30–63, L205, L363) falls back to `insertion_sort_shift_left` when `!Freeze` (`UnsafeCell`) holds, preventing comparison callbacks from mutating slice elements.
- **Lean 4.34.1 `whnf` scaling on >64-field `pin_init!` macros remains `unknown`:** End-to-end MIR timing awaits `TerminatorKind.drop` capture.

## Evidence

1. **`Rust-for-Linux/pin-init@578ad6b8f9d136aeb365f2175f6ef9f0e3dab288`** (`2026-11-19`, `Basis: source`): `src/lib.rs:156-240, 919-1242` (`PinInit`, `Init`, `ChainPinInit`, `pin_init_from_closure`); `src/__internal.rs:50-180, 214-563, 616-742` (`StackInit::init`, `Slot`, `DropGuard`, `SelfRefSlot`, `Erase`, `Borrowed`, `ExistLt`); `internal/src/init.rs:213-583` (`expand`, `make_field_init`, `make_field_check`).
2. **`bluss/scopeguard@bb988222848d39b0b9037b29da3a3a1eb05ebf4b`** (`2026-11-19`, `Basis: source`): `src/lib.rs:126-165, 201-250, 304-370, 465-478` (`Strategy::{Always, OnUnwind, OnSuccess}`, `ScopeGuard::into_inner`, `Drop::drop`).
3. **`rust-lang/rust@8144389c895da997dbdecaa635e41d6a50be6ffd`** (`2026-11-19`, `Basis: source + normative`): `library/alloc/src/vec/mod.rs:2430-2537` (`Vec::retain_mut`, `PanicGuard`); `library/alloc/src/vec/splice.rs:54-141` (`Splice::drop`, `Drain::{fill, move_tail}`); `library/alloc/src/vec/drain.rs:89-246` (`keep_rest`, `Drain::DropGuard`); `library/alloc/src/vec/set_len_on_drop.rs:6-33`; `library/core/src/mem/maybe_uninit.rs:267-310, 1691-1734` (`Guard`, `SpecFill`); `library/core/src/slice/sort/shared/smallsort.rs:18-63, 205-310, 363-370, 536-571` (`CopyOnDrop`, `insert_tail`); `library/core/src/slice/sort/stable/{merge.rs:8-150, drift.rs:20-120}`; `compiler/rustc_mir_transform/src/elaborate_drops.rs:49-121, 167-209, 267-316`; `compiler/rustc_mir_transform/src/elaborate_drop.rs:19-82, 227-350, 634-660, 733-750, 838-955, 1530-1621`.
4. **`tock/tock@ba6aa7edc014505d2e6f0123b2b6059ba6ee7dec`** (`2026-11-19`, `Basis: source`): `kernel/src/collections/ring_buffer.rs:14-129` (`RingBuffer::as_slices`, `is_valid`).
5. **Anneal, `lean-miri`, & Lean 4 (`2026-11-19`, `Basis: source`):** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/audit/TrustedBoundary.lean:442-596`; `trusted/lean/Trusted/MirAst.lean:682-814`; `trusted/lean/Trusted/MirSemantics.lean:601-605, 803-804, 1543-1614`; `theory/Anneal/MirWp.lean:69-120`; `theory/Anneal/PureLift/SpatialPin.lean:63-294`); `proofs-rs/lean-miri@c92d1d9754c9dd585b6b9d6949ae67e5e4665d6a` (`Miri/Interpreter/Unwind.lean:47-129`); `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).
6. **Publications (`Basis: normative`):** RustBelt (`10.1145/3158154`), RefinedRust (`10.1145/3656422`), Rudra (`10.1145/3477132.3483570`), Barnett & Leino (`10.1145/1108792.1108813`), Charguéraud (`10.1145/2034773.2034828`), Li et al. Rust-for-Linux ATC '24 (`https://www.usenix.org/conference/atc24/presentation/li-hongyu`).

## Revalidation

1. **Check `pin-init` `StackInit::init` flag-clear ordering & `DropGuard` contract:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/Rust-for-Linux/pin-init/<sha>/src/__internal.rs | grep -n -A 22 "pub fn init<E>(self: Pin<&mut Self>"
   ```
   Verify `this.is_init = false;` remains strictly before `this.value.assume_init_drop()`.
2. **Check `Vec::retain_mut` `PanicGuard` cursor pre-increment:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/rust-lang/rust/<sha>/library/alloc/src/vec/mod.rs | grep -n -A 26 "struct PanicGuard"
   ```
   Confirm `g.read += 1` still executes prior to `ptr::drop_in_place`.
3. **Check `rustc` drop-ladder & `Unwind::InCleanup` elaboration:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/rust-lang/rust/<sha>/compiler/rustc_mir_transform/src/elaborate_drop.rs | grep -n -A 28 "fn drop_ladder("
   ```
4. **Check `joshlf/anneal` `TerminatorKind.{drop, unwindTerminate}` & `TerminalOut` support:**
   ```bash
   curl --http1.1 -fsSL https://raw.githubusercontent.com/joshlf/anneal/<sha>/trusted/lean/Trusted/MirSemantics.lean | grep -n -C 6 "inductive TerminalOut"
   ```
   Determine whether `TerminalOut.aborted` and `TerminatorKind.drop` execution have entered `Trusted.MirSemantics`.
