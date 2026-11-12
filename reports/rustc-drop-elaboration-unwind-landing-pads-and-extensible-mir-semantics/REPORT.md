# rustc Drop Elaboration, Unwind Landing Pads, and Extensible MIR Semantics

## Summary

A formal verification tool that captures `rustc`'s `Runtime(PostCleanup)` Mid-level
Intermediate Representation (MIR) must model four tightly coupled features of
real-world Rust code:

1. **Unwind landing-pad control flow (`UnwindAction::Cleanup(bb)`) and elaborated
   drop glue:** When a function holds any local variable with a destructor (or
   is called from an outer stack frame), `ElaborateDrops` lowers panics,
   overflow/bounds assertions, and unwinding calls into cleanup basic blocks
   (`BasicBlockData { is_cleanup: true, .. }`) ending in
   `TerminatorKind::UnwindResume` or `TerminatorKind::UnwindTerminate`. If an
   operational semantics collapses `UnwindAction` into a boolean flag
   `hasCleanup : Bool` (`!matches!(unwind, UnwindAction::Continue)`) and steps
   to `.failed` (undefined behavior) whenever `hasCleanup || !s.stack.isEmpty`
   holds on a `panic` or failed `assert`, it conflates defined stack unwinding
   with undefined behavior and cannot verify any asserting function with local
   destructors or caller frames.
2. **The `#[may_dangle]` vs. `StorageDead` ordering seam:** When a type implements
   `unsafe impl<#[may_dangle] 'a> Drop for Guard<'a>`, `rustc`'s borrow checker
   omits `'a` from the drop-liveness constraints at `Drop` terminators
   (`destructor_constraints` marks `'a` as `pure_wrt_drop`), so `StorageDead`
   for a borrowed local can execute *before* `drop(guard)` in
   `Runtime(PostCleanup)` MIR. However, `#[may_dangle]` does **not** set
   `AdtFlags::IS_MAYBE_DANGLING`. An operational model that eagerly validates
   nested references inside `Guard<'a>` at `Drop` entry falsely rejects valid
   `#[may_dangle]` destructors unless reference liveness is checked at
   dereference/retag sites or wrapped in `MaybeDangling` / `ManuallyDrop`.
3. **Path-projected references (`List PlaceElem`) and single-pass byte-fragment
   transmutation:** Representing shared field borrows via a scalar nesting count
   (`fieldDepth : Nat`) and multi-field aggregates via untyped right-nested
   cons cells (`fieldCons`) fails on non-zero field borrows (`&pair.1`) and
   1-field structs wrapping tuples. Likewise, splitting `transmute` /
   `transmute_copy` into a syntactic `peelTransparent` pass (restricted to
   single-field structs) followed by a concrete bit-packing fallback
   (`extractTransmuteBits`) fails on `#[repr(transparent)]` wrappers with
   sibling zero-sized fields (`PhantomData<T>`, `()`) and on `#[repr(C)]`
   aggregates mixing symbolic type parameters with concrete integers. A flat
   list of byte-level fragments (`Fragment.byte`, `Fragment.symByte`,
   `Fragment.uninit`) unifies both paths in a single operational rule.
4. **Open table-driven intrinsic dispatch (`Terminator.callIntrinsic`):**
   Hardcoding each compiler intrinsic or standard-library primitive (`size_of`,
   `align_of`, `transmute_copy`, `AtomicUsize::load`) as dedicated `MirTy`,
   `MirVal`, and `Terminator` constructors forces every new intrinsic to touch
   every syntax-directed theorem and lowering pass. Factoring intrinsics into a
   single `Terminator.callIntrinsic (op : IntrinsicOp) (typeArgs : List MirTy)
   (args : List MirVal) (dst : LocalId) (target : BlockId)` over standard
   `MirTy.adt` and `MirTy.ref` types reduces frame and statement-index
   invariance proofs to a single `callIntrinsic` case proved once for all
   current and future `IntrinsicOp` entries.

All findings are backed by primary `rust-lang/rust` compiler source analysis,
compiled `Runtime(PostCleanup)` MIR probes
([`support/unwind_drop_and_intrinsics_probe.rs`](support/unwind_drop_and_intrinsics_probe.rs)
and
[`support/unwind_drop_and_intrinsics_postcleanup.mir`](support/unwind_drop_and_intrinsics_postcleanup.mir)),
and a standalone, zero-axiom Lean 4 (`v4.34.1`) mechanization
([`support/UnwindFragmentsAndIntrinsics.lean`](support/UnwindFragmentsAndIntrinsics.lean)).

## Applicability

These findings govern:

- **`rustc` MIR extraction (`anneal-rustc-capture`):** Lowering of cleanup basic
  blocks (`BasicBlockData::is_cleanup`), `UnwindAction` variants (`Continue`,
  `Unreachable`, `Terminate(UnwindTerminateReason)`, `Cleanup(BasicBlock)`),
  `TerminatorKind::Drop`, `TerminatorKind::UnwindResume`,
  `TerminatorKind::UnwindTerminate`, multi-field reference projections, and
  intrinsic calls from `Runtime(PostCleanup)` MIR.
- **Trusted MIR operational semantics (`Trusted/MirAst.lean`,
  `Trusted/MirSemantics.lean`):** Small-step stack unwinding, reference and
  aggregate value representations, byte-level transmutation semantics, and
  extensible intrinsic evaluation.
- **Verification lowering and proof automation (`theory/Anneal/Lowering.lean`,
  `theory/Anneal/MirLemmas.lean`):** Preserving constant-size case splits in
  control-flow and frame-invariance lemmas as the set of supported Rust
  intrinsics and standard-library primitives grows.

Pinned subject revisions:

- `rust-lang/rust` compiler source:
  `49d734536222bf28bb6d07d885b3a81d145981da` (and Anneal baseline
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `1.98.0-nightly`).
- `rustc` probe binary: `19833af7224424e8b53e288097d56b6af43d5bcf`
  (`1.101.0-nightly 2026-10-20`).
- `rust-lang/reference`: `82da570bafd9efed421bdbae0f8603ede8dd308b`.
- `leanprover/lean4`: `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`).

## Findings

### Finding 1: `ElaborateDrops`, `AbortUnwindingCalls`, and Cleanup Landing-Pad Topologies in `Runtime(PostCleanup)` MIR

#### 1.1 The Four `UnwindAction` Variants and `TerminatorKind` Unwind Primitives

In `compiler/rustc_middle/src/mir/syntax.rs` (lines 723–754 and 1126–1286 at
`49d734536222bf28bb6d07d885b3a81d145981da`), every potentially unwinding MIR
terminator (`Drop`, `Call`, `Assert`, `InlineAsm`) carries an explicit
`UnwindAction`:

```rust
pub enum UnwindAction {
    Continue,
    Unreachable,
    Terminate(UnwindTerminateReason),
    Cleanup(BasicBlock),
}

pub enum UnwindTerminateReason {
    Abi,
    InCleanup,
}
```

In addition, two dedicated terminators govern cleanup-block exits:

- `TerminatorKind::UnwindResume`: resumes stack unwinding to the caller frame
  after all cleanup landing-pad destructors in the current frame have completed
  (`syntax.rs:1145-1150`).
- `TerminatorKind::UnwindTerminate(UnwindTerminateReason)`: halts unwinding via
  process abort (`core::panicking::panic_cannot_unwind` for `Abi` or
  `core::panicking::panic_in_cleanup` for `InCleanup`, `syntax.rs:1152-1157`).

#### 1.2 How `ElaborateDrops` Constructs Normal and Cleanup Drop Topologies

During the transition from `Analysis` to `Runtime(Initial)` MIR,
`ElaborateDrops` (`compiler/rustc_mir_transform/src/elaborate_drops.rs` and
`compiler/rustc_mir_transform/src/elaborate_drop.rs`) runs move-path dataflow
(`MaybeInitializedPlaces` and `MaybeUninitializedPlaces`) and classifies every
`TerminatorKind::Drop { place, target, unwind, .. }` into one of four styles
(`elaborate_drops.rs:167-190`):

| `DropStyle` | Dataflow Condition | Lowered `Runtime(PostCleanup)` Structure |
| :--- | :--- | :--- |
| `Dead` | Place is definitely uninitialized | Patched in place to `TerminatorKind::Goto { target }`. |
| `Static` | Place is definitely initialized across all subfields | Kept as `TerminatorKind::Drop { place, target, unwind }` (`assert_with_drop_cleanup`, `bb3` and `bb5`). |
| `Conditional` | Place is dynamically initialized or uninitialized as a whole | Allocated a boolean local `_drop_flag : bool`; emits `drop_flag_test_block` (`SwitchInt(copy _drop_flag)`) branching to `drop_flag_reset_block` -> `Drop` or skipping directly to `target`. |
| `Open` | Subfields of an aggregate have mixed initialization states (e.g., after a partial move) | Decomposed via `open_drop` (`elaborate_drop.rs:413-444`) and `drop_ladder` (`elaborate_drop.rs:856-973`) into a two-half-ladder of subfield drops. |

Three implementation invariants in `ElaborateDrops` and `AbortUnwindingCalls`
determine the exact shape of `Runtime(PostCleanup)` cleanup blocks:

1. **Double-panic guard (`Unwind::InCleanup -> UnwindAction::Terminate(InCleanup)`):**
   When `ElaborateDrops` elaborates a `Drop` inside a basic block where
   `data.is_cleanup` is `true` (`elaborate_drops.rs:362-377`), it sets the drop
   cacher's unwind mode to `Unwind::InCleanup`. Under
   `Unwind::into_action(self)` (`elaborate_drop.rs:68-73`), `Unwind::InCleanup`
   maps to `UnwindAction::Terminate(UnwindTerminateReason::InCleanup)`. Thus, in
   `assert_with_drop_cleanup`
   ([`support/unwind_drop_and_intrinsics_postcleanup.mir`](support/unwind_drop_and_intrinsics_postcleanup.mir),
   lines 95–114):
   - Normal drop (`bb3`): `drop(_2) -> [return: bb4, unwind: bb6]`
   - Cleanup drop (`bb5 (cleanup)`):
     `drop(_2) -> [return: bb6, unwind terminate(cleanup)]`
   - Cleanup exit (`bb6 (cleanup)`): `resume`
2. **Asymmetric drop-flag setting (`drop_flags_for_fn_rets` vs.
   `drop_flags_for_locs`) and elided cleanup flag resets:**
   - When a `Call` has `UnwindAction::Cleanup(_)`, `drop_flags_for_fn_rets`
     (`elaborate_drops.rs:435-453`) sets the destination's drop flag to `true`
     at the start of the `return` target block (`Location { block: tgt,
     statement_index: 0 }`) because `tgt` cannot be a critical edge.
   - When a `Call` has `UnwindAction::Continue | Unreachable | Terminate(_)`,
     `drop_flags_for_locs` (`elaborate_drops.rs:505-520`) sets the destination's
     drop flag to `true` **before** the `Call` terminator (`Location { block:
     bb, statement_index: data.statements.len() }`) because any unwind will
     bypass local cleanup anyway.
   - In `drop_flag_reset_block` (`elaborate_drop.rs:1556-1581`), when
     `unwind.is_cleanup()` is `true`, `rustc` **omits** `_drop_flag = const
     false` before the `Drop` terminator (`if !unwind.is_cleanup() {
     this.clear_drop_flag(...); }`), because a cleanup path never re-reads that
     drop flag (`conditional_drop_flag_unwind`, `bb9 (cleanup)` vs. `bb6` in
     [`support/unwind_drop_and_intrinsics_postcleanup.mir`](support/unwind_drop_and_intrinsics_postcleanup.mir),
     lines 228–248).
3. **`DropStyle::Open` two-half-ladder cross-edges (`drop_ladder`):**
   When an aggregate suffers a partial move (`open_drop_partial_move`, where
   `pair.0` is conditionally moved and dropped in `bb1` while `pair.1` remains
   live), `drop_ladder` (`elaborate_drop.rs:856-973`) builds two parallel chains
   of subfield drops from back to front:
   - A **cleanup half-ladder** (`bb13 -> bb12 -> bb11 -> bb7`) where every drop
     uses `unwind terminate(cleanup)`.
   - A **normal half-ladder** (`bb5 -> bb10 -> bb9 -> bb6`) where dropping field
     `i` (`_3.0` in `bb10`) sets its unwind target to step `i + 1` of the
     **cleanup half-ladder** (`bb8`, which drops `_3.1` with
     `unwind terminate(cleanup)` before jumping to `bb7 (cleanup): resume`).
4. **Non-unwinding ABI boundaries (`AbortUnwindingCalls`):**
   In `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs` (lines 79–85
   and 125–136), when a function's ABI cannot unwind (such as `extern "C" fn
   extern_c_cleanup_then_terminate`), `AbortUnwindingCalls` **preserves**
   `UnwindAction::Cleanup(bb5)` on assertions and calls so that local destructors
   still execute in `bb5 (cleanup)`, and rewrites only the terminal `resume` in
   `bb6 (cleanup)` into `terminate(abi)`
   (`TerminatorKind::UnwindTerminate(UnwindTerminateReason::Abi)`,
   [`support/unwind_drop_and_intrinsics_postcleanup.mir`](support/unwind_drop_and_intrinsics_postcleanup.mir),
   lines 475–481).

#### 1.3 Small-Step Unwind State Machine vs. Fail-Closed `hasCleanup : Bool`

In [`support/UnwindFragmentsAndIntrinsics.lean`](support/UnwindFragmentsAndIntrinsics.lean)
(`Part 1: UnwindAndDropModel`), we contrast the fail-closed `hasCleanup : Bool`
model (`brittle_model_treats_cleanup_and_callee_unwind_as_failed`) with the
structurally recursive small-step transition `initiateUnwindStack` /
`initiateUnwind`:

```lean
def initiateUnwindStack (stack : List CallFrame) (dropLog : List Nat)
    (fnId : FnId) (natLocals : List (LocalId × Nat))
    (boolLocals : List (LocalId × Bool)) (act : UnwindAction) : StepResult :=
  match act with
  | .cleanup bb =>
    .running { fnId, bb, natLocals, boolLocals, stack, dropLog }
  | .terminate reason => .terminated (.cleanAbort reason) dropLog
  | .unreachable => .failed
  | .continue_ =>
    match stack with
    | [] => .terminated .cleanUnwind dropLog
    | frame :: rest =>
      initiateUnwindStack rest dropLog frame.fnId frame.savedNatLocals
        frame.savedBoolLocals frame.unwindAction
```

Mechanized theorems in `UnwindAndDropModel` verify that:

- `initiateUnwind_cleanup` and `initiateUnwind_continue_pop` hold universally
  for any call-stack depth;
- `assert_with_drop_cleanup_unwinds_and_runs_drop` and
  `double_panic_in_cleanup_aborts_with_inCleanup` execute cleanup block `bb5`
  and distinguish `.terminated .cleanUnwind [10]` from
  `.terminated (.cleanAbort .inCleanup) [10]`;
- `conditional_drop_flag_drops_once_on_all_paths` proves that across all four
  `(cond, calleeUnwinds)` paths, `TrackedGuard` is dropped exactly once
  (`dropLog = [20]`);
- `open_drop_half_ladder_preserves_exact_field_drops` proves that both fields of
  `GuardPair` are dropped in order `[1, 2]` across early field move, callee
  unwind, and mid-ladder normal-drop panic (`bb10 -> bb8 -> bb7`);
- `extern_c_runs_cleanup_drop_before_abi_terminate` proves that local drop glue
  runs before `.terminated (.cleanAbort .abi)`.

---

### Finding 2: The `#[may_dangle]` vs. `StorageDead` Ordering Seam

When a type implements `unsafe impl<#[may_dangle] 'a> Drop for EyepatchGuard<'a>`,
how does `rustc` lower its drop site in `Runtime(PostCleanup)` MIR?

1. **Borrow-checker liveness relaxation (`destructor_constraints`):**
   In `compiler/rustc_middle/src/ty/util.rs` (lines 464–536) and
   `compiler/rustc_borrowck/src/type_check/liveness/trace.rs` (lines 547–592,
   `add_drop_live_facts_for`), `#[may_dangle]` marks generic parameter `'a` as
   `pure_wrt_drop`. Borrowck therefore omits region `'a` from the drop-live
   constraints at `drop(g)`.
2. **`StorageDead` precedes `Drop` in `Runtime(PostCleanup)` MIR:**
   In `may_dangle_storage_dead_order`
   ([`support/unwind_drop_and_intrinsics_postcleanup.mir`](support/unwind_drop_and_intrinsics_postcleanup.mir),
   lines 388–406), local `_4` (`scoped_val`) is borrowed into `_2`
   (`EyepatchGuard(&scoped_val)`), and at the end of the inner block:
   ```text
   StorageDead(_4);
   StorageDead(_3);
   _0 = const 42_usize;
   drop(_2) -> [return: bb2, unwind: bb3];
   ```
   When `drop(_2)` invokes `<EyepatchGuard as Drop>::drop(_1: &mut EyepatchGuard<'_>)`,
   the pointee `_4` of `(*_1).0: &usize` is **already dead** (`StorageDead(_4)`
   has already incremented `_4`'s generation / deallocated `_4`)!
3. **`#[may_dangle]` does NOT set `AdtFlags::IS_MAYBE_DANGLING`:**
   In `compiler/rustc_middle/src/ty/sty.rs` (lines 2184–2195),
   `Ty::is_like_maybe_dangling` checks only `AdtFlags::IS_MAYBE_DANGLING ||
   AdtFlags::IS_MANUALLY_DROP` (plus closures/coroutines), which is set only by
   `#[rustc_adino]` (`MaybeDangling<T>`) or `#[lang = "manually_drop"]`. Why
   does Miri/CTFE accept `EyepatchGuard::drop(&mut _2)` when `_4` is dead?
   Because in `compiler/rustc_const_eval/src/interpret/validity.rs` (lines
   1707–1718) and `compiler/rustc_codegen_ssa/src/mir/retag.rs` (lines 203–229),
   passing `_1: &mut EyepatchGuard<'_>` checks/retags the outer `&mut
   EyepatchGuard` reference (`_2`, which is still live!) and sets
   `start_in_may_dangle = true` for pointers *behind* that outer reference. So a
   dangling `(*_1).0: &usize` inside `*_1` does not fault on `Drop::drop` entry
   unless the destructor body actually loads or retags `(*_1).0` as a reference
   (which `EyepatchGuard::drop` avoids by forming only `&raw mut (*_1)`).

In [`support/UnwindFragmentsAndIntrinsics.lean`](support/UnwindFragmentsAndIntrinsics.lean)
(`may_dangle_after_storage_dead_characterization`), we prove that an operational
semantics that recursively requires `isRefLive` on every `MirVal.ref` nested
inside a dropped local at `Terminator.drop` (`eagerDeepCheck = true`) falsely
rejects `may_dangle_storage_dead_order`, whereas checking reference liveness at
dereference/retag points (`eagerDeepCheck = false`) or wrapping the field in
`MaybeDangling` accepts `EyepatchGuard::drop` while still rejecting any wild
dereference of `(*_1).0`.

---

### Finding 3: Path-Projected References (`List PlaceElem`) and Single-Pass Byte-Fragment Transmutation

#### 3.1 Why Scalar `fieldDepth : Nat` and Untyped `fieldCons` Fail

Two representation shortcuts for aggregates and references break on standard
`Runtime(PostCleanup)` MIR:

1. **Scalar `fieldDepth : Nat` reference projections:**
   Representing a field-projected shared reference as
   `MirVal.ref frameId gen loc (fieldDepth : Nat)` where dereferencing peels
   `fieldDepth` layers of field `0` can only represent `&s.0`, `&s.0.0`, etc.
   In `borrow_second_field`
   ([`support/unwind_drop_and_intrinsics_postcleanup.mir`](support/unwind_drop_and_intrinsics_postcleanup.mir),
   lines 489–504), `rustc` emits `_2 = &((*_1).1: usize); _0 = copy (*_2);`,
   which projects field `1` of `TwoUsize`.
2. **Untyped right-nested `fieldCons` aggregates (`packFields`):**
   If a 1-field ADT is represented as `.adt id v` (unwrapped) while an $n$-field
   ADT ($n \ge 2$) is represented as `.adt id (.fieldCons v_1 ...)` and tuples
   reuse `.fieldCons`, then a 1-field struct `struct Wrap((u64, u64))` has
   payload `v = .fieldCons 10 20`. A typing predicate `validFields [f] v` that
   rejects `.fieldCons` for single-field ADTs (`| [f], .fieldCons _ _ => false`)
   misclassifies the inner 2-tuple as an ill-typed multi-field struct list
   (`brittle_fieldDepth_and_fieldCons_counterexamples` in
   [`support/UnwindFragmentsAndIntrinsics.lean`](support/UnwindFragmentsAndIntrinsics.lean)).

Replacing `fieldDepth : Nat` with `proj : List PlaceElem` and `fieldCons` with
explicit `fields : List MirVal` (`MirVal.adt id fields`, `MirVal.tuple fields`)
resolves both counterexamples (`path_projected_ref_resolves_second_field_and_nested_tuple`).

#### 3.2 Unifying `peelTransparent` and Bit-Level Transmutation via Byte Fragments

Why does a two-stage `evalTransmuteVal` (first attempting a syntactic
`peelTransparent` + `wrapTransparent` pass and falling back to concrete integer
bit-packing `extractTransmuteBits` + `constructTransmuteVal`) fail on legitimate
transmutations?

- If `peelTransparent` requires `decl.fields.length == 1`, then
  `#[repr(transparent)] pub struct TransparentWithPhantom<T>(pub PhantomData<u64>, pub (), pub T)`
  (which is valid Rust per The Rust Reference, *Type layout —
  `#[repr(transparent)]`*, because `PhantomData<u64>` and `()` are 1-ZSTs) has 3
  fields and fails Stage 1; when `T` is a generic type parameter `.symParam 0`,
  it has no concrete integer bits and also fails Stage 2!
- If a `#[repr(C)]` struct mixes a symbolic parameter `T` and a concrete integer
  `u32`, Stage 1 does not apply (not transparent) and Stage 2 fails (cannot pack
  `.symParam 0` into a `Nat`).

In [`support/UnwindFragmentsAndIntrinsics.lean`](support/UnwindFragmentsAndIntrinsics.lean)
(`Part 2C`), we replace both stages with a single byte-fragment representation:

```lean
inductive Fragment where
  | byte (b : Nat)
  | symByte (paramIdx : Nat) (byteOffset : Nat)
  | uninit
```

Together with `encodeFragments : MirTy → MirVal → Option (List Fragment)` and
`decodeFragments : MirTy → List Fragment → Option (MirVal × List Fragment)`,
`evalTransmuteUnified` has a single operational rule:

1. Verify `tyByteSize srcTy == tyByteSize dstTy`;
2. Encode `(srcTy, srcVal)` into `frags : List Fragment`;
3. Decode `frags` at `dstTy` and require zero leftover fragments.

We prove four theorems in `ProjectionAndFragmentModel`:

- `unit_tuple_field_erasure`: prepending a 0-sized field leaves
  `fieldListByteSize` and `encodeFieldFragments` identically unchanged for any
  tail field list;
- `unified_transmute_handles_transparent_with_phantom_zsts`:
  `TransparentWithPhantom<T> <-> T` round-trips in both directions via
  `evalTransmuteUnified` without any special-case `peelTransparent` logic;
- `unified_transmute_handles_mixed_symbolic_and_concrete_repr_c`: a `#[repr(C)]`
  struct `(T, u32)` transmutes into `(T, (u16, u16))` in a single pass,
  preserving symbolic `T` while splitting `0x00020001 : u32` into little-endian
  `(1 : u16, 2 : u16)`;
- `unified_transmute_rejects_uninit_padding_to_int`: uninitialized padding bytes
  (`Fragment.uninit`) cannot be decoded into `MirTy.int` or `MirTy.symParam`
  (`evalTransmuteUnified (.padding 4) (.int 4) (.uninitBytes 4) = none`),
  failing closed on undefined padding reads while allowing initialized integer
  bytes to be discarded into target padding.

---

### Finding 4: Open Table-Driven Intrinsic Dispatch vs. Hardcoded AST Constructors

In `intrinsic_and_atomic_gallery`
([`support/unwind_drop_and_intrinsics_postcleanup.mir`](support/unwind_drop_and_intrinsics_postcleanup.mir),
lines 523–646), `Runtime(PostCleanup)` MIR represents calls to `size_of::<T>()`,
`align_of::<T>()`, `transmute_copy::<Src, Dst>(src)`, `Atomic::<usize>::load`,
`usize::swap_bytes`, `usize::leading_zeros`, and `usize::wrapping_add` as
`TerminatorKind::Call` nodes targeting `DefId`s with generic type arguments and
standard ADT/reference operands (`&Atomic<usize>`, `Ordering::Relaxed`).

When a MIR formalization adds dedicated `MirTy` and `MirVal` constructors for
individual library types (`MirTy.refAtomicUsize`, `MirTy.atomicOrdering`,
`MirVal.atomicLoc`, `MirVal.ordering`) and dedicated `Terminator` constructors
per intrinsic family (`Terminator.callLayout`, `Terminator.callTransmuteCopy`,
`Terminator.callAtomicLoad`), every new intrinsic forces $O(N)$ boilerplate case
splits across all syntax-directed definitions and lowering theorems.

In [`support/UnwindFragmentsAndIntrinsics.lean`](support/UnwindFragmentsAndIntrinsics.lean)
(`Part 3: OpenIntrinsicModel`), we model all intrinsics and well-known library
primitives via a single `ExtensibleTerminator.callIntrinsic` constructor
parameterized by `IntrinsicOp`:

```lean
inductive IntrinsicOp where
  | sizeOf
  | alignOf
  | offsetOf (fieldIdx : Nat)
  | transmuteCopy
  | atomicLoad
  | bswap
  | ctlz
  | overflowingAdd
```

In this design:

- `Ordering` (`orderingAdtId = 500`) and `Atomic<usize>` (`atomicUsizeAdtId =
  501`) are ordinary `MirTy.adt` / `MirVal.adt` values accessed through standard
  `MirVal.ref loc path` references;
- `evalTerminator_stmtIdx_invariant` proves in 2 lines (`cases t <;> rfl`) that
  statement-index updates commute with `evalExtensibleTerminator` for **all**
  `IntrinsicOp` variants simultaneously;
- `intrinsic_gallery_executes_uniformly` verifies `sizeOf`, `alignOf`,
  `offsetOf`, `transmuteCopy`, `atomicLoad`, `bswap`, `ctlz`, and
  `overflowingAdd` through the single `.callIntrinsic` operational rule.

## Boundaries

1. **Catching unwinds (`std::panic::catch_unwind` / `core::intrinsics::catch_unwind`):**
   Our small-step unwind state machine models intra-frame cleanup landing pads
   (`UnwindAction.cleanup bb`), inter-frame stack unwinding
   (`Terminator.unwindResume` / `UnwindAction.continue_`), and abort boundaries
   (`UnwindAction.terminate reason` / `Terminator.unwindTerminate reason`). Modeling
   `core::intrinsics::catch_unwind` requires an additional frame marker that
   intercepts an unwinding stack pop and redirects control to the catch
   handler's normal return block.
2. **Pointer provenance inside byte fragments:**
   `Fragment` models concrete integer bytes (`Fragment.byte`), symbolic generic
   type parameter bytes (`Fragment.symByte`), and uninitialized padding bytes
   (`Fragment.uninit`). Extending `evalTransmuteUnified` to pointer-to-pointer or
   pointer-to-integer transmutations requires carrying pointer provenance
   (`Fragment.ptrByte`) alongside byte values.
3. **Weak memory concurrency for atomics:**
   Modeling `Atomic<usize>` as a standard `MirTy.adt` accessed via
   `IntrinsicOp.atomicLoad` captures sequential / acquire-release contract
   dispatch without polluting `MirTy`; full weak-memory litmus verification
   would require a concurrent event-graph state rather than a sequential local
   store.

## Evidence

- **Primary `rust-lang/rust` source files** (at revision
  `49d734536222bf28bb6d07d885b3a81d145981da`):
  - `compiler/rustc_middle/src/mir/syntax.rs`: lines 723–754 (`UnwindAction`,
    `UnwindTerminateReason`) and lines 1126–1286 (`TerminatorKind::Drop`,
    `UnwindResume`, `UnwindTerminate`, `Call`, `Assert`).
  - `compiler/rustc_mir_transform/src/elaborate_drops.rs`: lines 167–190
    (`DropStyle`), lines 362–377 (`Unwind::InCleanup` inside cleanup blocks),
    lines 435–453 (`drop_flags_for_fn_rets`), and lines 505–520
    (`drop_flags_for_locs`).
  - `compiler/rustc_mir_transform/src/elaborate_drop.rs`: lines 68–73
    (`Unwind::into_action`), lines 413–444 (`open_drop`), lines 856–973
    (`drop_ladder` two-half-ladder), and lines 1556–1581
    (`drop_flag_reset_block` skipping `clear_drop_flag` when
    `unwind.is_cleanup()`).
  - `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs`: lines 79–85 and
    125–136 (preserving `UnwindAction::Cleanup` while rewriting `UnwindResume`
    to `UnwindTerminate(Abi)` in non-unwinding functions).
  - `compiler/rustc_middle/src/ty/util.rs`: lines 464–536
    (`destructor_constraints` marking `#[may_dangle]` parameters as
    `pure_wrt_drop`).
  - `compiler/rustc_borrowck/src/type_check/liveness/trace.rs`: lines 547–592
    (`add_drop_live_facts_for` omitting `pure_wrt_drop` regions at drop sites).
  - `compiler/rustc_middle/src/ty/sty.rs`: lines 2184–2195
    (`is_like_maybe_dangling` checking only `IS_MAYBE_DANGLING ||
    IS_MANUALLY_DROP`).
  - `compiler/rustc_const_eval/src/interpret/validity.rs`: lines 1707–1718
    (`start_in_may_dangle` behind references).
- **Compiled `Runtime(PostCleanup)` MIR probes:**
  - [`support/unwind_drop_and_intrinsics_probe.rs`](support/unwind_drop_and_intrinsics_probe.rs):
    self-contained probe crate covering `assert_with_drop_cleanup`,
    `conditional_drop_flag_unwind`, `open_drop_partial_move`,
    `may_dangle_storage_dead_order`, `extern_c_cleanup_then_terminate`,
    `borrow_second_field`, `transmute_copy_transparent_phantom`, and
    `intrinsic_and_atomic_gallery`.
  - [`support/unwind_drop_and_intrinsics_postcleanup.mir`](support/unwind_drop_and_intrinsics_postcleanup.mir):
    exact `Runtime(PostCleanup)` MIR emitted by `rustc 1.101.0-nightly
    (19833af72 2026-10-20)`.
- **Lean 4 (`v4.34.1`) mechanization:**
  - [`support/UnwindFragmentsAndIntrinsics.lean`](support/UnwindFragmentsAndIntrinsics.lean):
    standalone, zero-`sorry` Lean 4 development mechanizing all three tracks and
    their counterexamples and positive theorems.

## Revalidation

To revalidate the Rust probes and Lean 4 mechanization from this package's
directory:

```bash
# 1. Compile and execute the Runtime(PostCleanup) MIR probe suite
rustc -C opt-level=0 -Z mir-opt-level=0 -C panic=unwind --emit=mir,link \
  support/unwind_drop_and_intrinsics_probe.rs -o unwind_probe_bin && \
  ./unwind_probe_bin && rm -f unwind_probe_bin unwind_probe_bin.mir

# 2. Type-check the standalone Lean 4 (v4.34.1) mechanization
lean support/UnwindFragmentsAndIntrinsics.lean
```
