# MIR Drop Elaboration, Dynamic Drop Flags, Partial Moves (`E0509`), `ManuallyDrop`/`MaybeUninit`, and Deterministic Drop Order

## Summary

`rustc` compiles implicit destruction in MIR in two stages:

1. **Pre-elaboration MIR construction** (`rustc_mir_build::builder::scope::build_scope_drops`) emits abstract `TerminatorKind::Drop` terminators unconditionally for every live owned binding and temporary in scope-exit cleanups—even along control-flow paths where the place is statically uninitialized, overwritten after a partial move, or wrapped inside a non-dropping carrier.
2. **`rustc_mir_transform::ElaborateDrops`** lowers those abstract `TerminatorKind::Drop` terminators into concrete CFG drop-glue ladders and destructor calls using two-pass fixpoint dataflow (`MaybeInitializedPlaces` followed by `MaybeUninitializedPlaces`) over a tree of place-granular `MovePath`s filtered by `Ty::needs_drop`.

At each `Drop` terminator, `DropElaborator::drop_style` partitions every reachable move path under `(maybe_init, maybe_uninit, multipart)` into four lowering modes: `Dead` (rewritten to `Goto`), `Static` (unconditional `Drop`), `Conditional` (guarded by a synthesized `bool` stack drop flag initialized to `false` at `Location::START`, set to `true` on initialization and `false` on move/drop, and branched via `switchInt`), and `Open` (expanded piecewise over surviving fields, elements, or enum variants).

Partial moves out of non-`Drop` structs, tuples, fixed-size arrays, and dereferenced `Box<T>` values elaborate field-granularly (`drop((_p.i: T))`, shallow `<Box<T> as Drop>::drop` deallocation, or array subslices) because `MoveDataBuilder` constructs independent `MovePath` children for their fields. By contrast, any ADT implementing `Drop` stops child `MovePath` creation (`if adt.has_dtor(tcx) { return; }`), causing borrowck to reject partial field moves with `E0509` (`InteriorOfTypeWithDestructor`) so user destructors never receive a partially moved `&mut self`. Types that suppress automatic drops—`ManuallyDrop<T>`, `MaybeUninit<T>` (a `union` wrapping `ManuallyDrop<T>`), zero-length arrays `[T; 0]`, and bare `union`s—short-circuit `drop_tys_helper` to empty drop glue so `ElaborateDrops` replaces any remaining `Drop` terminators with `Goto` unless the caller invokes an explicit unsafe destructor (`ManuallyDrop::drop` or `MaybeUninit::assume_init_drop`).

Deterministic drop ordering is governed by two independent rules: locals within a scope drop in **reverse declaration order** (`scope.drops.iter().rev()`), whereas fields of structs, tuples, and elements of whole-dropped arrays drop in **declaration / forward index order** (`0..n`). Source inspection across four `rust-lang/rust` snapshots and live compiler execution reveal an important upstream behavioral split on **partial moves out of fixed-size arrays**: revisions `14210df0e` (`rustc 1.98.0-nightly`) and `49d734536` double-reverse `drop_ranges.iter().rev()` inside `open_drop_for_array` before passing into `drop_ladder`, causing remaining elements to drop in reverse index order (`[2, 0]`), whereas later revisions `3ef0c22cd` (`rustc 1.102.0-nightly`) and `0259d5e9a` omit `.rev()`, restoring forward order (`[0, 2]`).

This behavior is independently backed by a kernel-checked Lean `v4.34.1` mechanization (`MirDropElaborationDynamicFlagsAndOrderSoundness.lean`, `5,412` lines, `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`, checked under `-DwarningAsError=true`) establishing exact `DropEvent` trace equivalence (`elaborateProgram_exact_trace_equiv`), the dynamic drop-flag simulation invariant (`drop_flag_simulation_invariant`), zero-fault/no-double-drop/no-leak preservation (`elaborated_zero_faults_and_terminal_freeze`, `elaborated_no_double_drop_and_no_leak`), partial-move field disjointness, `E0509` soundness necessity, zero implicit drops under `ManuallyDrop`/`MaybeUninit`, and the `open_drop_for_array` pre-/post-fix reversal theorem, alongside a live empirical probe harness (`probe_drop_elaboration_and_order.py` + `probe_results.json`) running on `rustc 1.98.0-nightly`.

## Applicability

These findings characterize the relationship among six directly examined subjects listed in `REPORT.json`:

1. **`rust-lang/rust` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly`, `2026-05-31`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`)** — examined through both primary Rust compiler source (`elaborate_drops.rs`, `elaborate_drop.rs`, `drop_flag_effects.rs`, `move_paths/mod.rs`, `move_paths/builder.rs`, `move_errors.rs`, `scope.rs`, `needs_drop.rs`, `manually_drop.rs`, `maybe_uninit.rs`) and live execution of all probes in `support/probe_drop_elaboration_and_order.py` with Edition 2024 and `-Zdump-mir=ElaborateDrops`.
2. **`rust-lang/rust` (`49d734536222bf28bb6d07d885b3a81d145981da`)** — examined via primary compiler source snapshot (`elaborate_drop.rs`) as a pre-fix comparison point for `open_drop_for_array`.
3. **`rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc 1.102.0-nightly`, `2026-11-11`, LLVM `23.1.5`)** — examined via primary compiler source (`elaborate_drop.rs`) and Edition 2024 baseline probe outputs (`LOCALS`, `STRUCT_FIELDS`, `TUPLE`, `ARRAY`, `MD_SUPPRESSED`, `MD_EXPLICIT`, `E0509`, `partial_move_probe`, `cond_init`, `mu_uninit_and_ignored`).
4. **`rust-lang/rust` (`0259d5e9a81c6af08e40f8c204f2c0c41dca1647`, `main`, checked `2026-11-23`)** — examined via primary compiler source (`elaborate_drops.rs`, `elaborate_drop.rs`, `move_errors.rs`, `needs_drop.rs`) to confirm upstream continuity on `main`.
5. **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)** — used to kernel-check the operational semantics and drop-elaboration soundness mechanization in `support/MirDropElaborationDynamicFlagsAndOrderSoundness.lean` (`axioms`: at most `[Quot.sound, propext]`, `unsafeRecs = 0`).
6. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)** — examined for semantic applicability to Anneal's trusted MIR layer (`trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean`).

### Shared vs. Version-Specific Behavior Across Examined `rustc` Revisions

- **Shared across all four `rustc` revisions (`14210df0e`, `49d734536`, `3ef0c22cd`, `0259d5e9a`):**
  - `ElaborateDrops::run_pass` performs `MaybeInitializedPlaces` -> `compute_dead_unwinds` -> `MaybeUninitializedPlaces` over `MoveData::gather_moves(..., |ty| ty.needs_drop(tcx, typing_env))`.
  - The 4-way `DropStyle` decision table (`Dead`, `Static`, `Conditional`, `Open`) in `DropElaborator::drop_style`.
  - Initialization of every allocated stack drop flag `bool` to `false` at `Location::START`, setting `DropFlagState::Present` (`true`) on initializations/arguments/call-returns and `DropFlagState::Absent` (`false`) on moves/drops.
  - Reverse-declaration local drop ordering (`scope.drops.iter().rev()`), declaration-order aggregate field/tuple/whole-array dropping via backward `drop_halfladder` chaining, `E0509` partial-move rejection on `Drop` types (`adt.has_dtor(tcx)`), and `ManuallyDrop<T>` / `union` / `MaybeUninit<T>` implicit-drop suppression.
- **Version-specific divergences:**
  - **`open_drop_for_array` partial-move ordering:** In `14210df0e` (`elaborate_drop.rs:1133-1135`) and `49d734536` (`elaborate_drop.rs:1392-1394`), `open_drop_for_array` builds `fields` via `drop_ranges.iter().rev()`, which double-reverses when passed to `drop_ladder`/`drop_halfladder` and executes surviving elements from highest index to lowest (`[2, 0]` on `[Track; 3]` after moving `[1]`, verified live in `14210df0e`). In `3ef0c22cd` (`elaborate_drop.rs:1370-1372`) and `0259d5e9a` (`elaborate_drop.rs:1370-1372`), `.rev()` is removed (`drop_ranges.iter()`), restoring forward declaration/index order (`[0, 2]`).
  - **`DropElaborator` flag clearing and pass-policy API:** In `14210df0e`, `ElaborateDrops` implements `fn is_required(&self) -> bool { true }` (`elaborate_drops.rs:91-93`), uses `MaybeUninitializedPlaces::new(...).include_inactive_in_otherwise()` (`line 71`), and clears drop flags through `DropElaborator::clear_drop_flag` (`elaborate_drops.rs:195-206`, `elaborate_drop.rs:113`). In `49d734536`, `3ef0c22cd`, and `0259d5e9a`, the trait method is refactored to `DropElaborator::drop_flags_for -> Vec<Place<'tcx>>` (`0259d5e9a/elaborate_drops.rs:190-206`, `elaborate_drop.rs:112`) for unified async/sync cleanup (`build_async_drop`, `0259d5e9a/elaborate_drop.rs:199-235`), and `ElaborateDrops` reports `PassPolicy::Required` via `fn policy(...)` (`0259d5e9a/elaborate_drops.rs:89-92`, omitting `include_inactive_in_otherwise()` and `TerminatorKind::Drop { async_fut, .. }`); synchronous drop semantics, ladder structure, and boolean flag invariants remain unchanged.

### Applicability to Anneal MIR Verification (`joshlf/anneal` `c131b320e`)

On `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), `Trusted.MirAst.TerminatorKind` explicitly classifies `TerminatorKind::Drop` under `.unsupported` (`trusted/lean/Trusted/MirAst.lean:782-784`), and `evalOperandToSlot` (`trusted/lean/Trusted/MirSemantics.lean:949-972`) rejects non-empty place projections (`!place.projection.isEmpty -> .error .unsupported`) while unconditionally modeling `deinitMovedPlace = true` via `liveUninitSlot` (`Operand.move` on a local marks its non-ZST slot uninitialized). Extending Anneal's MIR semantics to owning / non-`Copy` types, pre-elaboration MIR, or partially moved aggregates therefore requires: (1) adding concrete field/element projection support and `Drop`/drop-glue call lowering to `MirAst`/`MirSemantics`, (2) maintaining the per-move-path initialization invariant (`liveUninitSlot` per `MovePath` atom rather than whole-local only), or (3) consuming post-`ElaborateDrops` MIR directly where `Drop` terminators execute unconditionally on statically/flag-gated places (noting `Drop` behind `&mut T` / `*t` when `!place.local` is tracked only via borrowck `replace: true` invariants and post-elaboration `Drop` terminators still dispatch to drop-glue shims).

## Findings

### 1. Pass Architecture and Two-Pass Initialization Dataflow

`ElaborateDrops` is a mandatory MIR pass (`is_required() -> true` in `14210df0e/elaborate_drops.rs:91-93`; `PassPolicy::Required` in `49d734536`, `3ef0c22cd`, and `0259d5e9a/elaborate_drops.rs:89-92`)—it cannot be disabled even at `-C opt-level=0`.

Basis: source + derived

Its `run_pass` pipeline executes four sequential phases (`14210df0e/elaborate_drops.rs:52-89`, `275-288`):

1. **Move-path construction filtered by `needs_drop`:**
   `MoveData::gather_moves(body, tcx, |ty| ty.needs_drop(tcx, typing_env))` (`elaborate_drops.rs:59`) builds a forest of tracked `MovePath`s only for locals and places whose type potentially requires drop glue. Places whose type satisfies `!ty.needs_drop(tcx, typing_env)` (e.g., scalars, `&T`, `[T; 0]`, `ManuallyDrop<T>`, `MaybeUninit<T>`) receive no `MovePath` entry.
2. **Forward `MaybeInitializedPlaces` fixpoint:**
   Computes the set of `MovePathIndex`es that *may* be initialized before each MIR program point, configured with `.exclude_inactive_in_otherwise()` and `.skipping_unreachable_unwind()` (`elaborate_drops.rs:63-67`).
3. **Dead-unwind filtering (`compute_dead_unwinds`):**
   Scans every `TerminatorKind::Drop { place, unwind: UnwindAction::Cleanup(_), .. }` (`elaborate_drops.rs:98-119`). Seeking `inits` right before the terminator (`body.terminator_loc(bb)`), if `flow_inits.analysis().is_unwind_dead(place, flow_inits.get())` holds (the place cannot have any live sub-path to drop), the block is recorded in `dead_unwinds : DenseBitSet<BasicBlock>` so unreachable cleanup edges do not pollute `MaybeUninitializedPlaces`.
4. **Second-pass `MaybeUninitializedPlaces` fixpoint & patch synthesis:**
   Computes which `MovePathIndex`es *may* be uninitialized at each point using `.mark_inactive_variants_as_uninit()` and `.skipping_unreachable_unwind(dead_unwinds)` (`14210df0e/elaborate_drops.rs:70-75`, with `.include_inactive_in_otherwise()` in `14210df0e:71`). Then `ElaborateDropsCtxt::elaborate()` (`elaborate_drops.rs:277-287`) allocates a sparse `drop_flags: IndexVec<MovePathIndex, Option<Local>>` table (`line 77`) and executes:
   - `collect_drop_flags()` — determines every `MovePathIndex` reachable under a `Drop` terminator that is ambiguously initialized (`maybe_init && maybe_uninit == true`), allocating one `bool` temporary local per such move path via `patch.new_temp(tcx.types.bool, span)` (`elaborate_drops.rs:265-333`).
   - `elaborate_drops()` — transforms every `TerminatorKind::Drop` into `Goto`, static `Drop`, drop-flag `switchInt`, or an `Open` drop ladder (`elaborate_drops.rs:335-402`).
   - `drop_flags_on_init()` — sets every allocated `bool` drop flag to `const false` at `Location::START` (`elaborate_drops.rs:424-431`).
   - `drop_flags_for_fn_rets()` — sets call-destination drop flags to `Present` (`true`) on normal return when the call has an `UnwindAction::Cleanup(_)` edge (`elaborate_drops.rs:433-451`).
   - `drop_flags_for_args()` — sets function-argument drop flags to `Present` at `Location::START` via `drop_flag_effects_for_function_entry` (`elaborate_drops.rs:453-462`).
   - `drop_flags_for_locs()` — iterates over *original* basic blocks only (`self.body.basic_blocks.iter_enumerated()`, `lines 464-520`), inserting `flag = true` (`Present`) or `flag = false` (`Absent`) assignments for statements and non-`Drop` terminators according to `drop_flag_effects_for_location`, plus critical-edge pre-marking for non-cleanup `Call` destinations (`lines 503-518`).

Basis: source (`14210df0e/elaborate_drops.rs:50-520` vs `0259d5e9a/elaborate_drops.rs:51-520`)

Because `elaborate_drops()` checks `!place.ty(...).ty.needs_drop(tcx, typing_env)` first (`elaborate_drops.rs:347-354`), any spurious `Drop` on a non-dropping place is replaced unconditionally by `TerminatorKind::Goto { target }` (or `TerminatorKind::goto(target)` in `0259d5e9a`) even without a move path. Conversely, if a `Drop` *does* need dropping yet `rev_lookup.find(place.as_ref())` yields `LookupResult::Parent(Some(_))`—meaning borrowck permitted overwriting behind a reference/slice/raw pointer (`drop_and_replace` / `replace == true`)—`elaborate_drops()` asserts `replace` cannot be false (or emits `span_bug!`) and leaves an unconditional `Drop` terminator because `&mut T` / `*ptr` overwrite requires full prior initialization (`elaborate_drops.rs:389-400`).

Basis: source (`14210df0e/elaborate_drops.rs:347-401`, `0259d5e9a/elaborate_drops.rs:348-401`)

---

### 2. `MovePath` Tree Decomposition, Place Granularity, and `Drop`-Type `E0509` Protection

In `compiler/rustc_mir_dataflow/src/move_paths/mod.rs` (`14210df0e:16-90`), `MoveData` organizes tracked places as a linked tree of `MovePath<'tcx>` nodes indexed by `MovePathIndex` (`mp0`, `mp1`, ...):

```rust
pub struct MovePath<'tcx> {
    pub next_sibling: Option<MovePathIndex>,
    pub first_child: Option<MovePathIndex>,
    pub parent: Option<MovePathIndex>,
    pub place: Place<'tcx>,
}
```

When descending along projections in `MoveDataBuilder` (`compiler/rustc_mir_dataflow/src/move_paths/builder.rs:140-230` in `14210df0e`):

- **Non-`Drop` structs, tuples, closures, coroutines, fixed-size arrays (`ConstantIndex`), and `Box<T>` (`Deref`):** `builder.rs` decomposes the place into child `MovePath`s (e.g., `_2.0`, `_2.1`, `_2[1 of 3]`, `*_2`), allowing independent per-child tracking in `MaybeInitializedPlaces` / `MaybeUninitializedPlaces` and independent `DropFlag` allocation. Specifically, for `Box<T>`, `Deref` creates an interior child `MovePath` while the `Box` shell retains its own shallow heap-deallocation responsibility (`builder.rs:115-145`; `elaborate_drop.rs:737-817`).
- **ADTs implementing `Drop` (`adt.has_dtor(tcx)`):** At `builder.rs:177-181`, encountering a `Field` projection inside an ADT with a custom destructor executes an immediate early return:

  ```rust
  MoveSubPath::Field(_) => match place_ty.kind() {
      ty::Adt(adt, _) => {
          if adt.has_dtor(tcx) {
              return;
          }
          if adt.is_union() {
              union_path.get_or_insert(base);
          }
      }
      ...
  ```

- **Resulting `E0509` enforcement:** Because no child `MovePath` exists inside a `Drop` ADT (and likewise for slice/array indexing), attempting to move out of `o.a` where `OuterWithDrop: Drop` fails in MIR borrowck (`compiler/rustc_borrowck/src/type_check/...` / `move_errors.rs:31-39`), classifying the move error as `IllegalMoveOriginKind::InteriorOfTypeWithDestructor { container_ty }` and emitting `error[E0509]: cannot move out of type ..., which implements the Drop trait`. Overwriting `o.a = Inner(3)` in place (`o.a = new_val`) compiles and executes cleanly because drop-and-replace drops the old field or mutates in place while leaving the `OuterWithDrop` container wholly initialized before `&mut self` destructor execution.

Basis: source + execution (`14210df0e/move_paths_mod.rs:58-90`, `builder.rs:177-184`, `move_errors.rs:31-39`; live probe `b_partial_move_and_e0509`)

#### Formal Necessity of `E0509` (`Drop` Type Protection)

The Lean mechanization formalizes `isValidMovePath` (`MirDropElaborationDynamicFlagsAndOrderSoundness.lean:217-247`) directly mirroring `builder.rs:177-181` (rejecting projections through `.structTy true ...`, `.manuallyDrop`, and `.maybeUninit`). Theorem `e0509_partial_move_drop_type_necessity` (`line 4483`) establishes a two-horned soundness necessity proof: if moving field `0` out of a custom-`Drop` struct `outerTy` were permitted while `atomsOfPlace` tracks `outerTy` as a single `.adtDrop` atom `[outerAtom]`, then *either*:
1. Retaining `outerAtom = true` invokes `OuterWithDrop::drop(&mut self)` over an uninitialized field `0` (`traceHasFault = true`), *or*
2. Clearing `outerAtom = false` suppresses `OuterWithDrop::drop` altogether, violating `noLeakTag` (`countTagDrops = 0 < 1 = countTagCreates`).

Basis: derived (kernel-checked Lean proof, theorem `e0509_partial_move_drop_type_necessity`, axioms `[propext]`)

---

### 3. Dynamic Boolean Drop-Flag Synthesis, Updates, and Critical-Edge Ordering

`DropFlagState` (`compiler/rustc_mir_dataflow/src/drop_flag_effects.rs:9-26`) is a two-value boolean state:

```rust
pub enum DropFlagState {
    Present, // .value() -> true
    Absent,  // .value() -> false
}
```

#### Allocation Criterion (`collect_drop_flags`)

A stack `bool` temporary local (`self.drop_flags[child] : Option<Local>`) is synthesized **if and only if** some `TerminatorKind::Drop { place, .. }` references an `Exact(path)` having a descendant `child` (including `path` itself) with `maybe_init == true && maybe_uninit == true` right before that terminator (`elaborate_drops.rs:290-334`). Places whose state is statically `(true, false)` (always initialized) or `(false, _)` (definitely dead) receive **zero** stack drop flags (`None`).

#### Transition Rules (`drop_flag_effects_for_location` and Statement Placement)

1. **Function entry (`Location::START`, `elaborate_drops.rs:424-431, 453-462`):**
   - `drop_flags_on_init()` sets *all* allocated drop flags to `const false`.
   - `drop_flags_for_args()` then emits `flag = const true` (`DropFlagState::Present`) for every argument's move path (ordered cleanly at `Location::START`).
2. **Moves, drops, and writes (`drop_flag_effects.rs:106-135`):**
   At each `loc` in original blocks, `drop_flag_effects_for_location`:
   - First marks all RHS move outs (`move_data.loc_map[loc]`) and all non-`Drop`-elaborated `TerminatorKind::Drop` places (for all children via `on_all_children_bits`) as `DropFlagState::Absent` (`false`).
   - Then marks all initialized targets (`for_location_inits`) as `DropFlagState::Present` (`true`).
   Because `MirPatch::add_assign(loc, flag, val)` inserts the flag update **immediately before** the statement at `loc`, the runtime `switchInt` condition reflects the exact post-move/post-init state.
3. **Function calls and critical unwind edges (`elaborate_drops.rs:433-451, 500-518`):**
   - If `TerminatorKind::Call` has an `UnwindAction::Cleanup(_)` block, setting the destination drop flag to `Present` inside `tgt.start_location()` avoids falsely marking the return local initialized if the call panics before writing its destination.
   - Conversely, if `TerminatorKind::Call` has `UnwindAction::Continue | UnwindAction::Unreachable | UnwindAction::Terminate(_)`, setting the flag to `Present` happens at the terminator location *before* the call because `tgt` may be the join point of a critical edge shared with another predecessor where the destination was *not* written! (And on `Continue`/`Terminate`/`Unreachable`, this function has no local cleanup handler that could drop the uninitialized destination during unwind of the call.)
4. **Clearing flags inside elaborated ladders (`elaborate_drop.rs:488-496, 626-634`):**
   In `cond_init` (`bb11`) and `cond_move_and_reinit` (`bb11`), both normal drop completion and scope exit clear `_flag = const false` (`drop_ladder_bottom` / `drop_flag_reset_block`) before freeing storage (`StorageDead`) so no subsequent loop back-edge or enclosing drop can re-drop an already-destroyed value. Importantly, `drop_flags_for_locs()` skips *newly created* ladder blocks (`elaborate_drops.rs:465-469`) and skips `TerminatorKind::Drop` (`line 477`) so ladder-internal moves or flag clears do not clobber flags before they are tested.

Basis: source + execution (`14210df0e/elaborate_drops.rs:290-520`, `drop_flag_effects.rs:10-135`; live dumps of `cond_init` and `cond_move_and_reinit`)

---

### 4. `DropStyle` Classification Lattice and Full vs. Half Drop-Ladder Control Flow

At a `Drop` terminator `(bb, place, path, succ, unwind, dropline)`, `DropElaborator::drop_style(path, DropFlagMode::Deep)` (`14210df0e/elaborate_drops.rs:170-193`) aggregates `(some_maybe_init, some_maybe_uninit)` across all `on_all_children_bits` and counts `children_count`:

| `some_maybe_init` | `some_maybe_uninit` | `multipart` (`children_count != 1`) | Resulting `DropStyle` | Lowered MIR Control Flow |
| :---: | :---: | :---: | :--- | :--- |
| `false` | `false` or `true` | any | **`Dead`** | Replace terminator with `Goto { target: succ }` (`elaborate_drop.rs:502-506`). Zero destructor call, zero drop flag. |
| `true` | `false` | any | **`Static`** | Keep unconditional `Drop` (`build_drop(bb)`, `elaborate_drop.rs:507-509`). No drop flag tested. |
| `true` | `true` | `false` (`children_count == 1`) | **`Conditional`** | Generate flag-clear + static drop blocks gated by `switchInt(copy flag) -> [0: succ, otherwise: drop_bb]` (`complete_drop`, `elaborate_drop.rs:510-515`). |
| `true` | `true` | `true` (`children_count != 1`, i.e. `0` or `>= 2` with ambiguous init across paths/children) | **`Open`** | Expand structure via `open_drop()` into tuple/struct/enum/array/box piecewise sub-drops (`open_drop_for_*` + `drop_ladder`, `elaborate_drop.rs:516-521`). |

Note a subtle edge case verified directly in source: `multipart` is `children_count != 1` (not merely `> 1`), so an aggregate with child paths split by partial moves or multi-field ADTs takes `DropStyle::Open` whenever any ambiguity exists across children (`partial_move_probe`: `pair.0` moved out makes `pair.0` dead and `pair.1` alive -> `open_drop_for_adt` drops only `(_2.1: Track<'_>)`).

#### Full Ladder vs. Unwind Cleanup Half-Ladder (`drop_ladder` / `drop_halfladder`)

Suppose an `Open` composite has live fields `[f0, f1, f2]` (`elaborate_drop.rs:609-716`):

1. **Fields filtering:** `fields.retain(|&(place, _)| self.place_ty(place).needs_drop(...))` drops zero-drop fields statically (`elaborate_drop.rs:688-690`).
2. **Unwind half-ladder built first:** When `unwind` is `Unwind::To(succ)` (`!data.is_cleanup`), `drop_ladder` calls `drop_halfladder(&all_in_cleanup, ..., succ, &fields)` iterating `fields.iter().rev()`, returning `[succ, c_{n-1}, ..., c_1, c_0]` where `c_0 = *unwind_ladder.last()` becomes the ladder's unwind entry block while `unwind_ladder[n - 1 - k]` (`= c_{k+1}` with `c_n = succ`) pairs with `fields[k]`.
3. **Normal mainline ladder built second:** Calling `drop_halfladder(&unwind_ladder, ..., succ, &fields)` chains `d_0 -> d_1 -> ... -> d_{n-1} -> succ`, where **`d_k`'s unwind edge points to `c_{k+1}`** (the next remaining field in cleanup mode `Unwind::InCleanup`).
4. **Panic-during-drop guarantee:** If dropping `f_0` (`f1_panics`) panics mid-ladder, unwinding jumps cleanly to `c_1`, which drops `f_1` (`f2`) and `f_2` (`f3`) in declaration order **without** double-dropping `f_0` and without leaking `f_1` or `f_2`!

```text
Normal entry -> d0: drop(f0) --[return]--> d1: drop(f1) --[return]--> d2: drop(f2) --> bottom(succ)
                     |                          |                          |
                  [unwind]                   [unwind]                   [unwind]
                     v                          v                          v
                    c1: drop(f1) ------------> c2: drop(f2) ------------> bottom(unwind)
```

5. **Cleanup block flattening:** If the original `Drop` terminator is *already* in a cleanup block (`is_cleanup == true`), `unwind` is `Unwind::InCleanup` (`elaborate_drops.rs:361`), so only the single cleanup half-ladder (`c_0 -> c_1 -> c_2`) is emitted. Notice also `drop_ladder_bottom()` (`elaborate_drop.rs:626-635`) clears the parent's *shallow* drop flag at the **end** of the ladder (essential for `enum` discriminants: clearing the discriminant flag *before* dropping variant fields would forfeit knowledge of which variant to drop, whereas reading `Rvalue::Discriminant(self.place)` happens *before* the variant sub-drops in `open_drop_for_multivariant`, lines `948-963`!).
6. **`Box<T>` deref-move handling (`open_drop_for_adt` / `open_drop_for_box_contents`):** When `adt.is_box()` (`elaborate_drop.rs:801-808`), `open_drop_for_box_contents` (`737-771`) extracts the raw interior pointer by transmuting `(_box.0: Unique<T>).0: NonNull<T>` into a temporary `*const T` (`ptr_local`), emits a `drop_subpath` on `*ptr_local` (using `deref_subpath`, which collapses to a no-op if `*boxed` was moved out!), and chains into `<Box<T> as Drop>::drop(&mut _box)` (`destructor_call_block_sync`) which frees the heap allocation without double-dropping the already-moved `T`!

Basis: source + execution (`14210df0e/elaborate_drop.rs:609-832, 935-1012`; live MIR dumps of `unwind_field_ladder` and `partial_move_box_deref_probe`)

---

### 5. Deterministic Drop-Order Contracts and `open_drop_for_array` Divergence

Cross-checking source implementation, live `rustc` execution, and standard Rust language rules yields five crisp deterministic ordering laws:

| Construct | Observed Runtime Order | Source Mechanism & Anchor | Basis |
| :--- | :--- | :--- | :--- |
| **Locals in same scope / nested scopes** | Reverse declaration order (`["c", "b", "a"]`; inner scope before outer shadowing variable `["inner_scope", "shadow_x", "outer_x"]`) | `build_scope_drops` iterates `for drop_data in scope.drops.iter().rev()` (`14210df0e/scope.rs:1872`), pushing temporaries and inner scopes after outer locals. | normative + source + execution |
| **Non-`Drop` struct fields** | Declaration order (`["f1", "f2", "f3"]`), both normally and during field-drop panic unwind | `open_drop_for_adt_contents` -> `variant.fields.iter_enumerated()` -> `drop_ladder` (`elaborate_drop.rs:534-560, 617, 825-828`). Also holds when struct implements `Drop`: `Drop::drop(&mut self)` runs first, followed by fields in declaration order (struct drop-glue shim behavior). | normative + source + execution |
| **Tuple elements & enum variant fields** | Declaration order (`["t0", "t1", "t2"]`, `["e0", "e1"]`) | `open_drop_for_tuple` (`719-733`: `tys.iter().enumerate()`); `open_drop_for_multivariant` (`834-931`) passes `move_paths_for_fields` in field-declaration order to `drop_ladder`. | normative + source + execution |
| **Drop-and-replace assignment (`r = new`)** | Old value `r_old` drops *before* replacement `r_new` becomes owned by `r` (`["r_old", "after_assign", "r_new"]`) | Before assignment, pre-elab MIR emits `drop(old_place)` then overwrites `place = move rhs`; `ElaborateDrops` deletes the dead post-move `drop(rhs)` temporary (`drop_replace_order.after.mir: bb1 -> goto -> bb3`). | normative + source + execution |
| **Whole array `[T; N]` (no partial moves)** | Forward index order (`["arr0", "arr1", "arr2"]`) | Exact `rev_lookup` exists for whole `[T; N]` (`drop_style == Static`), keeping `drop(_2)` invoking array drop glue (`slice_drop_in_place`), which drops `0..N` forward. | normative + source + execution |
| **Partially moved array `[T; N]` (`let [_, moved_mid, _] = arr;`)** | **`rustc 1.98.0-nightly` (`14210df0e`) / `49d734536`:** **Reverse** remaining index order (`["a1", "after_mid_drop", "a2", "a0"]`)<br>**`3ef0c22cd` (`rustc 1.102.0-nightly`) / `0259d5e9a`:** **Forward** remaining index order (`[0, 2]`) | Pre-fix `open_drop_for_array` calls `drop_ranges.iter().rev()` (`14210df0e:1133-1135`, `49d734536:1392-1394`) and passes that reversed vector to `drop_ladder` -> `drop_halfladder` (`fields.iter().rev()`), double-reversing into `[2, 0]` (`bb24: drop(_2[2..3]) -> bb22: drop(_2[0..1])`). Removing `.rev()` (`3ef0c22cd:1370-1372`, `0259d5e9a:1370-1372`) restores single reversal (`[0, 2]`). | source + execution + derived |

#### Exact Source Comparison of `open_drop_for_array`

In `14210df0e` (`elaborate_drop.rs:1129-1137`) and `49d734536` (`elaborate_drop.rs:1388-1395`):

```rust
if !drop_ranges.is_empty() {
    if dropping {
        drop_ranges.push(ProjectionKind::Drop(start..size));
    }
    let fields = drop_ranges
        .iter()
        .rev() // <--- causes reverse drop [2..3] before [0..1] in drop_ladder!
        .map(|p| { ... })
        .collect::<Vec<_>>();
    let (succ, unwind, dropline) = self.drop_ladder_bottom();
    return self.drop_ladder(fields, succ, unwind, dropline).0;
}
```

In `3ef0c22cd` (`rustc 1.102.0-nightly`, `elaborate_drop.rs:1366-1396`) and `0259d5e9a` (`main`, `elaborate_drop.rs:1366-1396`), the `.rev()` call on line 1372/1371 is absent:

```rust
    let fields = drop_ranges
        .iter()
        .map(|p| { ... })
        .collect::<Vec<_>>();
```

Because `drop_ranges` is collected monotonically while scanning `for i in 0..size`, removing `.rev()` yields `fields = [Subslice(0..1), Keep(1), Subslice(2..3)]`. Passing `fields` into `drop_ladder` / `drop_halfladder` then chains `bb_drop(0..1) -> bb_drop(2..3)` so runtime destruction executes in ascending index order `[0, 2]` (consistent with whole-array forward drop order).

Basis: source (`14210df0e`, `49d734536`, `3ef0c22cd`, `0259d5e9a`) + execution (`probe_results.json` live run of `partial_move_array_pattern_probe`)

---

### 6. `ManuallyDrop<T>` and `MaybeUninit<T>` Zero-Implicit-Drop Semantics

Three independent compiler layers enforce zero implicit destruction for `ManuallyDrop<T>` and `MaybeUninit<T>`:

1. **Type-level `needs_drop_raw` / `drop_tys_helper` (`compiler/rustc_ty_utils/src/needs_drop.rs:352-374`):**
   - When `adt_def.is_manually_drop()`, `drop_tys_helper` returns `Ok(Vec::new())` (`needs_drop.rs:353-355`).
   - Because `MaybeUninit<T>` is a `#[repr(transparent)] pub union MaybeUninit<T> { uninit: (), value: ManuallyDrop<T> }`, its `adt_def.is_union()` branch *also* returns `Ok(Vec::new())` (`needs_drop.rs:371-373`), and unions do not auto-drop fields.
   - Live probe verification (`NEEDS_DROP`): `std::mem::needs_drop::<ManuallyDrop<Track<'_>>>() == false`, `needs_drop::<MaybeUninit<Track<'_>>>() == false`, `needs_drop::<[Track<'_>; 0]>() == false`, `needs_drop::<[Track<'_>; 3]>() == true`.
2. **Dataflow & `MoveData::gather_moves` (`elaborate_drops.rs:58`):**
   Neither `ManuallyDrop<Track>` nor `MaybeUninit<Track>` enters `MoveData` (just as `elaborate_drops()` sees `!place.ty(...).needs_drop(...)` at `elaborate_drops.rs:347-354`). Any cleanup `drop(_3)` temporary constructed *inside* the initializer argument expression (`Track::new(...)` before `ManuallyDrop::new(move _3)` moves `_3` into `_2`) has `_3` marked dead and its cleanup `drop(_3)` replaced by `goto -> bb3` (`md_suppressed_probe.after.mir` and `mu_uninit_and_ignored.after.mir`), while `_2` (`ManuallyDrop<Track>`) and `_3` (`MaybeUninit<Track>`) receive **no** `Drop` terminator at all!
3. **`open_drop_for_adt` defensive guard (`elaborate_drop.rs:783-796`):**
   Sets `let skip_contents = adt.is_union() || adt.is_manually_drop();` so even inside drop-glue elaboration an open ADT drop never walks `ManuallyDrop` or `union` fields. Destruction occurs *only* via explicit unsafe APIs (`ManuallyDrop::drop(&mut md)` / `ManuallyDrop::into_inner(md)` / `MaybeUninit::assume_init_drop()` / `assume_init()`).

Basis: normative + documentation (`library/core/src/mem/manually_drop.rs:8-66`, `maybe_uninit.rs:7-105`) + source (`needs_drop.rs:353-373`, `elaborate_drops.rs:58,348-355`, `elaborate_drop.rs:783-796`) + execution

---

### 7. Live `rustc` Empirical Verification & MIR Case Studies

All empirical probes in `support/probe_drop_elaboration_and_order.py` executed cleanly on **`rustc 1.98.0-nightly (14210df0e 2026-05-31)`** (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, Edition `2024`). Complete captured stdout, stderr, exit codes, and `.before.mir` / `.after.mir` dumps reside in `support/probe_results.json`.

#### Summary Table of Live Execution Probes (`probe_results.json`)

| Probe Group / Case | Compile / Run RC | Observed Output / Diagnostic | Verified MIR / Drop-Flag Mechanism |
| :--- | :---: | :--- | :--- |
| `a_deterministic_drop_order` | `0` / `0` | `LOCALS=["c", "b", "a"]`<br>`SHADOW_NESTED=["inner_scope", "shadow_x", "outer_x"]`<br>`STRUCT_FIELDS=["f1", "f2", "f3"]`<br>`TUPLE=["t0", "t1", "t2"]`<br>`ARRAY=["arr0", "arr1", "arr2"]`<br>`ENUM_FIELDS=["e0", "e1"]`<br>`DROP_REPLACE=["r_old", "after_assign", "r_new"]`<br>`MD_SUPPRESSED=[]`<br>`MD_EXPLICIT=["md_explicit", "after_explicit_drop"]`<br>`NEEDS_DROP track=true md=false mu=false arr0=false arr3=true tup=true nodrop=false` | `locals_order`: `bb2` `unwind continue` promoted to `unwind: bb6` (resume); `drop_replace_order`: post-move `bb1: drop(_4)` replaced by `goto -> bb3`; `md_suppressed_probe`: `bb2 (cleanup): drop(_3)` replaced by `goto -> bb3`. |
| `b_partial_move_and_e0509.partial_move_without_drop_impl` | `0` / `0` | `PARTIAL_MOVE=["end_inner_fn", "p0", "p1"]`<br>`PARTIAL_MOVE_REINIT=["p0_orig", "end_reinit_fn", "p0_reinit", "p1_orig"]`<br>`BOX_DEREF_MOVE=["after_unbox", "boxed", "after_unboxed_drop"]`<br>`ARRAY_PATTERN_MOVE=["a1", "after_mid_drop", "a2", "a0"]` | `partial_move_probe`: `drop(_2)` becomes `bb17: drop((_2.1: Track<'_>))` while `_16: bool` protects `moved_p0` (`_7`); `partial_move_box_deref_probe`: extracts `*const Track` into `_25` (`bb24`) and calls `<Box<Track<'_>> as Drop>::drop` shallow heap free (`bb21`) without double-dropping moved `boxed`; `partial_move_array_pattern_probe`: drops `bb24: drop(_2[2..3])` then `bb22: drop(_2[0..1])`. |
| `b_partial_move_and_e0509.partial_move_with_drop_impl_e0509` | `1` / `N/A` | `error[E0509]: cannot move out of type OuterWithDrop, which implements the Drop trait` at `let _moved = o.a;` | `MoveDataBuilder` halts child paths when `adt.has_dtor(tcx)` is true; borrowck emits `E0509`. |
| `b_partial_move_and_e0509.drop_impl_field_assign_valid` | `0` / `0` | Compiles and exits `0` | Mutating/overwriting `o.a = Inner(3)` in place preserves `OuterWithDrop` full initialization across `Drop::drop`. |
| `c_conditional_init_drop_flag_unwind_and_panic_and_maybe_uninit` | `0` / `0` | `COND_TRUE=["exit_scope", "dyn"]`<br>`COND_FALSE=["exit_scope"]`<br>`COND_MOVE_REINIT=(false, false)=["v1"] (true, false)=["v1"] (true, true)=["v1", "v2"] (false, true)=["v1", "v2"]`<br>`LOOP_COND_INIT=["even", "after_loop", "even"]`<br>`UNWIND_PARTIAL_MOVE=["p0", "before_panic", "p1"]`<br>`UNWIND_FIELD_LADDER=["f1_panics", "f2", "f3"]`<br>`MU_IGNORED=[]`<br>`MU_EXPLICIT=["mu_explicit", "after_mu_drop"]` | `cond_init`: `_15: bool` initialized `false` at `bb0`, set `true` at `bb2`/`bb3`, checked via `switchInt(copy _15)` at `bb16`/`bb18`; `cond_move_and_reinit`: `_14: bool` guards both overwrite-drop (`bb16`) and scope exit (`bb18`/`bb20`); `unwind_field_ladder`: panic in `f1_panics` continues cleanup along `f2` -> `f3` (`["f1_panics", "f2", "f3"]`); `unwind_partial_move`: cleanup drops only `bb15: drop((_3.1: Track<'_>))`; `mu_uninit_and_ignored`: `bb3 (cleanup): drop(_4)` replaced by `goto -> bb4`. |

#### Selected Verbatim Before/After MIR Evidence (`support/probe_results.json`)

**1. Conditional Initialization Stack Drop Flag (`cond_init`):**
Before `ElaborateDrops`, `bb1` unconditionally contains `drop(_3)` before `_3 = move _6`, and scope exit `bb10` unconditionally contains `drop(_3)` regardless of `cond`. After `ElaborateDrops`, a synthetic flag `_15: bool` replaces both with deterministic boolean state updates and `switchInt` guards:

```mir
    bb0: {
        _15 = const false;
        StorageLive(_3);
        ...
        switchInt(move _5) -> [0: bb5, otherwise: bb1];
    }
    bb2: {
        _15 = const true;
        _3 = move _6;
        goto -> bb4;
    }
    ...
    bb11: {
        _15 = const false;
        StorageDead(_3);
        return;
    }
    bb15: {
        drop(_3) -> [return: bb11, unwind: bb14];
    }
    bb16: {
        switchInt(copy _15) -> [0: bb11, otherwise: bb15];
    }
```

And symmetrically for cleanup unwinding in `bb18` -> `bb17: drop(_3)` (`unwind terminate(cleanup)`).

**2. Conditional Move + Conditional Reinitialization (`cond_move_and_reinit`):**
Here `x` (`_4`) starts initialized (`bb0: _14 = const true`), is conditionally dropped via `std::mem::drop(move _9)` (`bb1: _14 = const false`), and may be overwritten (`_11 = "v2"`, jumping through `bb5 -> bb16`). **Both** the overwrite point `bb16` and the scope exit `bb18`/`bb20` read the *same* single flag `_14: bool`:

```mir
    bb5: {
        ...
        _11 = Track::<'_> { log: move _12, label: const "v2", panic_on_drop: const false };
        StorageDead(_12);
        goto -> bb16;
    }
    bb6: {
        _14 = const true;
        _4 = move _11;
        goto -> bb8;
    }
    ...
    bb15: {
        drop(_4) -> [return: bb6, unwind: bb7];
    }
    bb16: {
        switchInt(copy _14) -> [0: bb6, otherwise: bb15];
    }
```

When `(do_move, do_reinit) == (true, true)`, `_14` is `false` entering `bb16`, suppressing `bb15: drop(_4)` on the dead old slot before `bb6` sets `_14 = const true` for `"v2"`; when `(false, true)`, `_14` is `true`, so `bb15` drops `"v1"` before `bb6` moves `"v2"` in. This matches all four empirical outcomes: `(false, false)=["v1"]`, `(true, false)=["v1"]`, `(true, true)=["v1", "v2"]`, `(false, true)=["v1", "v2"]`.

**3. Box Deref Partial Move (`partial_move_box_deref_probe`):**
After `_5 = move (*_2)` (`bb1`), `open_drop_for_adt` (`adt.is_box() == true`) delegates to `open_drop_for_box_contents` (`bb24`), which extracts the non-null pointer for the statically dead inner slot and chains unconditionally to shallow heap deallocation (`bb21`):

```mir
    bb21: {
        _21 = &mut _2;
        _22 = <Box<Track<'_>> as Drop>::drop(move _21) -> [return: bb20, unwind: bb19];
    }
    ...
    bb24: {
        _25 = copy ((_2.0: std::ptr::Unique<Track<'_>>).0: std::ptr::NonNull<Track<'_>>) as *const Track<'_> (Transmute);
        goto -> bb23;
    }
```

Hence `Track::drop` runs exclusively on `unboxed` (`"boxed"`), never inside `bb24`, while the `Box` heap allocation is still reclaimed.

**4. Pre-Fix Array Pattern Partial-Move Ordering (`partial_move_array_pattern_probe` on `rustc 1.98.0-nightly`):**
Moving middle element `_9 = move _2[1 of 3]` (`bb3`) lowers exit `drop(_2)` into subslice drops `bb24` then `bb22`:

```mir
    bb22: {
        drop(_2[0..1]) -> [return: bb18, unwind: bb17];
    }
    bb23: {
        goto -> bb22;
    }
    bb24: {
        drop(_2[2..3]) -> [return: bb23, unwind: bb20];
    }
```

Directly executing `ARRAY_PATTERN_MOVE=["a1", "after_mid_drop", "a2", "a0"]` confirms runtime destruction of element `2` (`"a2"`) prior to element `0` (`"a0"`).

Basis: execution (`support/probe_drop_elaboration_and_order.py` + `support/probe_results.json`)

---

### 8. Kernel-Checked Lean `v4.34.1` Soundness Mechanization

File `support/MirDropElaborationDynamicFlagsAndOrderSoundness.lean` (`5,412` lines, `241,411` bytes, `1,166` module declarations) formalizes MIR move-path initialization semantics, two-pass abstract dataflow certification, `ElaborateDrops` lowering (static, dead, conditional flag-guarded, and open drop ladders with panic cleanup half-ladders), partial moves, `E0509`, `ManuallyDrop`/`MaybeUninit`, and deterministic drop ordering.

#### Purity & Axiom-Isolation Architecture

Every `def` in the module is declared `noncomputable def` using explicit recursion on `Nat`, `Bool`, `Option`, `List`, and domain inductives—with **zero** `partial def`, **zero** `sorry`, **zero** `Classical.choice`, **zero** `omega`, **zero** `bv_decide`, **zero** `native_decide`, **zero** `noncomputable section`, **zero** `deriving DecidableEq`/`Repr` on recursive inductives, and **zero** `._unsafe_rec` kernel constants (`check_meta.lean`: `declCount=1166 unsafeRecs=0 ([]) unsafes=0 partials=0 axioms=[Quot.sound, propext]`).

#### Semantic Structure (`Sections 1–8`)

1. **Types, MovePaths & Ordering (`Sections 1–3`):**
   - `DropFlagState` (`present`/`absent`), `DropStyle` (`dead`/`static_`/`conditional`/`open_`), `DropStyle` matrix `dropStyleOf`, and `MirTy` (`scalar`, `dropLeaf`, `structTy hasDrop selfTag fields`, `tupleTy`, `arrayTy`, `enumTy`, `boxTy`, `manuallyDrop`, `maybeUninit`).
   - `placeTypeWalk`, `isValidMovePathWalk` / `isValidMovePath` (mirroring `builder.rs:177-184` disallowing partial moves inside `Drop` ADTs, `ManuallyDrop`, and `MaybeUninit`), `atomsOfPlace`, `localsDropOrder` (`listReverse`), `dropHalfLadderOrder`, `openDropArrayRemainingPreFix` vs. `openDropArrayRemainingPostFix`.
2. **Source MIR Semantics (`Section 4`):**
   - `SrcProgram`, `SrcStmt` (`storageLive`, `storageDead`, `initPlace`, `movePlace`, `explicitDrop`, `noop`), `SrcTerm` (`goto`, `switchBool`, `drop`, `scopeExit`, `ret`, `unwindResume`, `unwindAbort`).
   - `evalSrcDropAtomsGo` / `stepSrcBlock` / `execSrcFuel` execute abstract drops **atomically guided by exact live state `st.init : AtomMap`** and emit exact `DropEvent` traces (`create`, `dropCall`, `boxDealloc`, `doubleOrUninitFault`, `uninitFieldInDropImpl`). If an atom panics mid-drop during normal execution (`isCleanup == false`), `evalSrcDropAtomsGo` switches `panicked` to `true`, continues dropping all remaining live atoms along the panic/cleanup order (aborting immediately on a double-panic), and returns `panicked = true` so `stepSrcBlock` branches to `unwind` (or `.aborted` when `unwind = none`), matching the lowered `d_k -> c_{k+1}` ladder behavior; panicking while already in cleanup (`isCleanup == true`) aborts immediately.
3. **Target Elaborated MIR Semantics (`Section 5`):**
   - `ElabProgram`, `ElabStmt` (`storageLive`, `storageDead`, `setFlag`, `initRaw`, `moveRaw`, `explicitDropRaw`, `noop`), `ElabTerm` (`goto`, `switchBool`, `switchFlag FlagId bbPresent bbAbsent`, `staticDropAtom Atom target unwind`, `ret`, `unwindResume`, `unwindAbort`).
   - Crucially, the target semantics drops **concrete single `Atom`s** via `switchFlag` stack booleans (`st.flags : FlagMap`) rather than inspecting oracle initialization maps for implicit drops (`mem : AtomMap` acts purely as a physical fault monitor confirming every executed `staticDropAtom` sees `st1.mem a == true`), verifying that elaborated drop-flag control flow alone guarantees safety.
4. **`ElaborateDrops` Lowering Pass (`Section 6`):**
   - Formalizes `DataflowCert` (`ValidDataflowCert prog numBlocks df`) and `FlagAlloc` (`ValidFlagAlloc prog numBlocks df fa`) enforcing soundness of forward `mayInit` (`initConsistent`), backward `mayUninit`, block index bounds, flag injectivity (`inj`), and mandatory flag allocation whenever `mayInit a == true ∧ mayUninit a == true`.
   - `elaborateProgram prog numBlocks df fa` inserts `Location::START` `false`-initializations (followed by `Present` arg initializations) at block `0`, shifts original blocks to `1..numBlocks`, rewrites statements using `setFlagsForAtoms` (clearing RHS move flags then setting LHS init flags), builds cleanup half-ladders (`lowerDropCleanupHalfLadder`) followed by normal ladders (`lowerDropNormalLadder`), and emits `emitAtomDropRung` (`dead -> skip`, `static -> dropAtom + clearFlag`, `conditional -> switchFlag -> dropAtom + clearFlag`).

#### Core Proven Theorems & Verified Kernel Axioms

| Lean Identifier (`Vrustc.MirDropElaboration.*`) | Line | Proven Statement / Guarantee | Verified Axioms |
| :--- | :---: | :--- | :--- |
| `elaborateProgram_exact_trace_equiv` | `4072` | For every well-formed `SrcProgram`, `ValidDataflowCert`, `ValidFlagAlloc`, `oracle`, and fuel `n`, there exists `m` such that `e.trace = s.trace`, `e.exit = s.exit`, `e.mem = s.init`, `FlagSimulatesInit fa s.init e.flags`, `e.dropIdx = s.dropIdx`, `e.branchIdx = s.branchIdx`. | `[Quot.sound, propext]` |
| `drop_flag_simulation_invariant` | `4096` | At every simulated boundary, `∀ a fid, fa.flagOf a = some fid → e.flags fid = s.init a` (`flag = true ↔ init(a)`). | `[Quot.sound, propext]` |
| `elaborated_zero_faults_and_terminal_freeze` | `4117` | Whenever `s` terminates without fault (`traceHasFault s.trace = false`, `s.exit ≠ .running`, `s.exit ≠ .faulted`), `e` stays fault-free and frozen at `s.trace` for all `m' ≥ m`. | `[Quot.sound, propext]` |
| `elaborated_no_double_drop_and_no_leak` | `4148` | Preserves `noDoubleDropTag tag` (`countTagDrops ≤ countTagCreates ∧ traceHasFault = false`) and `noLeakTag tag` (`countTagCreates ≤ countTagDrops`) from source to elaborated CFG across all branches and panics. | `[Quot.sound, propext]` |
| `partial_move_field_disjointness_sound` | `4390` | Moving field `i` (`src = (l, [.field i])`) into `dstLoc ≠ l` sets all atoms in `src` to `false` while preserving `st'.init a = st.init a` for every sibling field atom `j ≠ i`. | `[propext]` |
| `isValidMovePath_rejects_drop_adt_field` | `4433` | Rejects moving any `.field i :: rest` out of `.structTy true ...` (`Drop` ADT). | `[propext]` |
| `isValidMovePath_rejects_manuallyDrop_interior` | `4442` | Rejects interior projections inside `.manuallyDrop inner` (`isValidMovePath = false`). | `[propext]` |
| `isValidMovePath_rejects_maybeUninit_interior` | `4458` | Rejects interior projections inside `.maybeUninit inner` (`isValidMovePath = false`). | `[propext]` |
| `e0509_partial_move_drop_type_necessity` | `4483` | Constructs the two-horned impossibility counterexample for partial moves out of `Drop` ADTs (`traceHasFault` if `Drop::drop` runs vs. `¬ noLeakTag` if suppressed). | `[propext]` |
| `manuallyDrop_and_maybeUninit_zero_implicit_drop` | `4636` | Under `AllPlacesDropSuppressed prog`, *both* source and `ElaborateDrops`-lowered executions yield `trace = []` on every oracle and fuel horizon `n`. | `[Quot.sound, propext]` |
| `localsDropOrder_reverse_three` | `4670` | `localsDropOrder [l0, l1, l2] = [l2, l1, l0]`. | `[]` |
| `dropHalfLadderOrder_preserves_declaration_order` | `4677` | `dropHalfLadderOrder fields = fields` (double-reversal identity of backward ladder construction). | `[]` |
| `struct_tuple_array_drop_trace_order` | `4714` | Live unpanicked drops of struct `[t0, t1, t2]`, tuple `[t0, t1, t2]`, and `[tElem; 3]` emit exact forward declaration-order traces. | `[propext]` |
| `openDropArray_rev_removal_divergence` | `4761` | Proves `openDropArrayRemainingPreFix 3 (fun i => natEq i 1) = [2, 0]`, `openDropArrayRemainingPostFix 3 (fun i => natEq i 1) = [0, 2]`, and universally `openDropArrayRemainingPreFix len isMoved = listReverse (openDropArrayRemainingPostFix len isMoved)`. | `[]` |

#### End-to-End Concrete Verified Witnesses (`Section 8.5`)

Four complete MIR programs have fully proved `ValidDataflowCert`, `ValidFlagAlloc`, `WellFormedSrcDrops`, and kernel `rfl` execution witnesses connecting concrete traces directly to the generic soundness theorems:

1. **`condInitProg`** (`condInit_main_theorems_apply`, axioms `[Quot.sound, propext]`): 5-block CFG with flag `fid = 0`; proves `sTrue.trace = eTrue.trace = [.create 100 0, .dropCall 100 0 false]` on true branch and `[]` on false branch, plus universal flag simulation across all oracles.
2. **`condMoveReinitProg`** (`condMoveReinit_all_4_paths_witness`, axioms `[propext]`): 8-block CFG with flag `fid = 0`; kernel-verifies all 4 boolean path combinations `(false,false)`, `(true,false)`, `(true,true)`, `(false,true)` with exact `noDoubleDropTag 201` and `noLeakTag 201`.
3. **`partialMovePairProg`** (`partialMovePair_witness`, axioms `[propext]`): Struct `[.dropLeaf 10, .dropLeaf 20]` with empty flag allocation (`allFlags = []`); verifies partial move of `.field 0` explicitly drops `10` first and scope exit drops only `20` (`[.create 10 0, .create 20 0, .dropCall 10 1 true, .dropCall 20 0 false]`) with zero flags needed.
4. **`unwindHalfLadderProg`** (`unwindHalfLadder_panic_witness`, axioms `[propext]`): 3-field struct `[1, 2, 3]` where `panicFirstOracle` triggers a panic on field `0` (`natEq d 0`); proves cleanup unwind half-ladder executes `[.dropCall 1 0 false, .dropCall 2 0 false, .dropCall 3 0 false]` (`s.exit = .unwound`, `e.exit = .unwound`, zero double-drops, zero leaks).

Basis: derived (kernel-checked Lean `v4.34.1` proofs in `support/MirDropElaborationDynamicFlagsAndOrderSoundness.lean`)

## Boundaries

The scope and precision of these results are bounded by the following explicit limits:

- **Unsized slice drop loop (`[T]` / `drop_loop`, `opt_size = None`) — `not examined` (runtime / Lean execution), `source` only:**
  `elaborate_drop.rs:1025-1093` (`14210df0e`) implements index-iterated pointer destruction (`cur = 0..len`, `cur = cur + 1`, dropping `0..len-1` forward) for dynamically sized arrays/slices when `opt_size` is `None`. Neither the runtime probes nor the Lean `MirTy.arrayTy elem len` model exercises dynamically sized `[T]` drop loops.
- **Coroutine / `async` drop poll-loop expansion (`DropElaborator::allow_async_drops`, `StateTransform`) — `not examined` (runtime / Lean):**
  Although `elaborate_drop.rs` (`build_async_drop`, `211-479` in `14210df0e`, substantially refactored in `3ef0c22cd`/`0259d5e9a`) outlines `AsyncDrop` yield/dropline ladders before `StateTransform`, experimental `AsyncDrop` coroutines and `CoroutineDrop` terminators were neither probed via live nightly feature flags nor modeled in `MirDropElaborationDynamicFlagsAndOrderSoundness.lean`.
- **Enum discriminant read & multi-variant partial move runtime execution — `not examined` (live probe) / partial (`Lean`):**
  The live probe suite executed a whole `enum` field-order check (`ENUM_FIELDS=["e0", "e1"]`) and source-audited `open_drop_for_multivariant` (`14210df0e/elaborate_drop.rs:834-963`, which clears the master discriminant flag at `drop_ladder_bottom` after switching on `Rvalue::Discriminant` and emits MSVC EH funclet cleanup chains). Live MIR dumps of a *partially moved* multi-variant `enum` and runtime discriminant-tag switching inside the Lean lowering pass were not constructed; Lean `atomsOfVariants` models per-variant atoms statically without dynamic discriminant lowering (`switchInt` over `Discriminant(place)`).
- **Unsafe / aliasing / uninitialized memory UB (`MaybeUninit::assume_init`, double `ManuallyDrop::drop`, self-move aliasing) — `known not to apply`:**
  Static soundness in `rustc` and `elaborateProgram_exact_trace_equiv` applies **only** to borrow-checked safe code or `unsafe` callers upholding validity/aliasing preconditions. Double-calling `ManuallyDrop::drop`, calling `assume_init` on uninitialized bytes, or dropping partially initialized `Drop` values via raw pointers violates soundness invariants and is outside MIR drop-flag protection. Furthermore, `partial_move_field_disjointness_sound` requires `dstLoc ≠ l` (non-overlapping distinct destination local).
- **`rustc` binary vs. Lean extraction gap — `unsupported` (by standalone mechanization):**
  `MirDropElaborationDynamicFlagsAndOrderSoundness.lean` formalizes a high-fidelity model of `rustc`'s `MoveData`, two-pass initialization certificate (`ValidDataflowCert`), and `ElaborateDrops` lowering rather than running inside `rustc` as a verified binary pass or proving fixpoint convergence of Rust's `MaybeInitializedPlaces` solver (`rustc_mir_dataflow`). Soundness in the Lean proofs is conditional on `ValidDataflowCert`, `ValidFlagAlloc`, and `WellFormedSrcDrops` (each discharged concretely on the four Section 8.5 witness programs).
- **Exact upstream PR/commit bisecting `49d734536` and `3ef0c22cd` for `.iter().rev()` removal — `unknown`:**
  Source inspection proves `.iter().rev()` is present in `14210df0e` (`elaborate_drop.rs:1133-1135`) and `49d734536` (`elaborate_drop.rs:1392-1394`) and absent in `3ef0c22cd` (`elaborate_drop.rs:1370-1372`) and `0259d5e9a` (`elaborate_drop.rs:1370-1372`), and `3ef0c22cd` postdates `49d734536` (`rustc 1.102.0-nightly`, `2026-11-11`). Pinpointing the exact single intermediate commit hash between `49d734536` and `3ef0c22cd` was not performed via git bisect or live GitHub PR metadata lookup.
- **Unmodified `rustc 1.102.0-nightly` (`3ef0c22cd`) runtime re-execution of `probe.partial_move_array_pattern_probe` — `not examined`:**
  While `3ef0c22cd` source directly shows `drop_ranges.iter()` without `.rev()` (`elaborate_drop.rs:1370-1372`), live runtime `ARRAY_PATTERN_MOVE` execution in `probe_results.json` was performed specifically on `rustc 1.98.0-nightly` (`14210df0e`), matching the pre-fix `open_drop_for_array` code (`[a2, a0]`). Forward `[a0, a2]` execution on `3ef0c22cd` is derived from source inspection and `openDropArray_rev_removal_divergence`.

## Evidence

### 1. Primary Upstream Source Citations (`rust-lang/rust` & `joshlf/anneal`)

| Repository & Commit (`40-hex`) | File Path & Symbol | Exact Line Range | Key Observation |
| :--- | :--- | :---: | :--- |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_transform/src/elaborate_drops.rs`<br>`ElaborateDrops::run_pass`, `is_required`, `compute_dead_unwinds`, `DropElaborator::drop_style`, `clear_drop_flag`, `ElaborateDropsCtxt` | `48-135`, `170-287`, `290-520` | Two-pass dataflow (`include_inactive_in_otherwise()` on uninits) over `needs_drop` `MoveData`, `DropStyle` 4-way matrix, `clear_drop_flag`, `false` flag init at `START`, location & critical-edge flag assignment. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_transform/src/elaborate_drop.rs`<br>`elaborate_drop`, `drop_halfladder`, `drop_ladder`, `open_drop_for_*` | `113`, `166-180`, `500-560`, `609-963`, `1096-1155` | `clear_drop_flag` trait method, backward unwind+mainline drop ladders, `adt.is_box()` shallow free + interior drop, `adt.is_manually_drop()`, `.iter().rev()` in `open_drop_for_array` (`1133-1135`). |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_dataflow/src/drop_flag_effects.rs`<br>`DropFlagState`, `drop_flag_effects_for_function_entry`, `drop_flag_effects_for_location` | `10-26`, `90-135` | Binary `Present` (`true`) / `Absent` (`false`) transitions; moves and `Drop` clear children before inits mark children `Present`. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_dataflow/src/move_paths/{mod.rs, builder.rs}`<br>`MovePath`, `MovePathIndex` | `mod.rs:19-90`; `builder.rs:177-184` | Linked parent/child/sibling `MovePath` tree; stops child path creation on `adt.has_dtor(tcx)`. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_borrowck/src/diagnostics/move_errors.rs`<br>`IllegalMoveOriginKind::InteriorOfTypeWithDestructor` | `23-39` | Protects `Drop` ADTs from partial field moves (`E0509`) so `&mut self` destructor sees wholly initialized fields. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_mir_build/src/builder/scope.rs`<br>`build_scope_drops` | `1835-1885` (`1872`) | Iterates `scope.drops.iter().rev()`, emitting reverse-declaration local drops and chained cleanup pads. |
| `rust-lang/rust`<br>`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_ty_utils/src/needs_drop.rs`<br>`needs_drop_raw`, `drop_tys_helper` | `17-33`, `327-395` (`353-373`) | Short-circuits `is_manually_drop()` and `is_union()` (including `MaybeUninit<T>`) to empty drop glue. |
| `rust-lang/rust`<br>`49d734536222bf28bb6d07d885b3a81d145981da` | `compiler/rustc_mir_transform/src/elaborate_drop.rs`<br>`open_drop_for_array` | `1355-1415` (`1392-1394`) | Retains `drop_ranges.iter().rev()`. |
| `rust-lang/rust`<br>`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `compiler/rustc_mir_transform/src/elaborate_drop.rs`<br>`open_drop_for_array` | `1333-1395` (`1370-1372`) | Omits `.rev()`, iterating `drop_ranges.iter()` forward. |
| `rust-lang/rust`<br>`0259d5e9a81c6af08e40f8c204f2c0c41dca1647` | `compiler/rustc_mir_transform/src/{elaborate_drops.rs, elaborate_drop.rs}`<br>`ElaborateDrops::policy`, `DropElaborator::drop_flags_for`, `open_drop_for_array` | `elaborate_drops.rs:89-92`, `190-206`; `elaborate_drop.rs:112`, `1333-1396` | `PassPolicy::Required`, `clear_drop_flag` refactored to `drop_flags_for`, and `open_drop_for_array` forward `drop_ranges.iter()` preserved on `main`. |
| `joshlf/anneal`<br>`c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/{MirAst.lean, MirSemantics.lean}`<br>`TerminatorKind`, `evalOperandToSlot`, `liveUninitSlot` | `MirAst.lean:742-785`; `MirSemantics.lean:949-976` | `Drop` terminator currently mapped to `.unsupported`; non-empty projections return `.unsupported`; `Operand.move` deinitializes non-ZST locals (`deinitMovedPlace = true`). |

### 2. Preserved Package Support Material & Checksums

| File | Size / Lines | SHA-256 Digest | Verification Role |
| :--- | :---: | :--- | :--- |
| `support/probe_drop_elaboration_and_order.py` | `16,494` B / `562` lines | `4081f0d1ae5f2dccaf356e36fdae7f6483a9546ca81fdc15603ed793ffc48a85` | Standalone Edition 2024 harness using `tempfile.TemporaryDirectory()`, invoking `rustc -Zdump-mir=ElaborateDrops -Zdump-mir-dir=...` and compiling/running all Probe A/B/C programs. |
| `support/probe_results.json` | `82,708` B / `88` lines | `e5038654e21e24cdbb402cf59e042ab6dc8321355a3df687c6048730034d27b7` | Captured empirical results on `rustc 1.98.0-nightly` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `2026-05-31`, LLVM `22.1.6`), stdout/stderr, and complete `.before.mir`/`.after.mir` dumps. |
| `support/MirDropElaborationDynamicFlagsAndOrderSoundness.lean` | `241,411` B / `5,412` lines | `95863acd9b8cfcae87208f80369e958202f6f32de3d3206f474ec3d5b6f106cc` | Kernel-checked Lean `v4.34.1` formalization (`Vrustc.MirDropElaboration.*`) with strict zero-`sorry`, zero-`Classical.choice`, zero-`._unsafe_rec` purity. |

### 3. Lean `v4.34.1` Kernel Verification Record

- **Toolchain:** `Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)`.
- **Exact strict compiler check (`2026-11-23`):**
  ```console
  lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/MirDropElaborationDynamicFlagsAndOrderSoundness.lean
  ```
  Exited with status `0`, zero errors, zero warnings.
- **MetaM declaration & axiom audit (`-M4096 --run`):**
  - `declCount=1166 unsafeRecs=0 ([]) unsafes=0 partials=0 axioms=[Quot.sound, propext]`.
  - Forbidden-token verification across `support/MirDropElaborationDynamicFlagsAndOrderSoundness.lean`: zero `sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial def`, `noncomputable section`, `deriving`, or unannotated plain `def`.

### 4. Baseline Comparison Provenance

- **Live capsule execution (`2026-11-23`):** `rustc 1.98.0-nightly (14210df0e 2026-05-31)` — full `probe_results.json` run including `SHADOW_NESTED`, `ENUM_FIELDS`, `NEEDS_DROP`, `BOX_DEREF_MOVE`, `ARRAY_PATTERN_MOVE`, `COND_MOVE_REINIT`, `LOOP_COND_INIT`, `UNWIND_PARTIAL_MOVE`, `UNWIND_FIELD_LADDER`, and `E0509` + field re-assignment check.
- **Later toolchain observation baseline:** `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, LLVM `23.1.5`) — confirmed matching `LOCALS`, `STRUCT_FIELDS`, `TUPLE`, `ARRAY`, `MD_SUPPRESSED`, `MD_EXPLICIT`, `PARTIAL_MOVE`, `E0509`, `COND_TRUE`/`COND_FALSE`, `MU_IGNORED`/`MU_EXPLICIT`, and `elaborate_drop.rs:1370-1372` `.rev()` removal.

## Revalidation

To test whether these findings hold on a new `rustc` revision or target platform with minimal cost:

1. **Rerun the live empirical probe suite (`~2–4 s`):**
   From the package directory, execute:
   ```console
   python3 support/probe_drop_elaboration_and_order.py
   ```
   Verify all `compile_returncode` / `run_returncode` pairs (expect `0/0` everywhere except `partial_move_with_drop_impl_e0509`, which must fail with `1` and `error[E0509]`), and check `ARRAY_PATTERN_MOVE`: `["a1", "after_mid_drop", "a2", "a0"]` indicates pre-fix `drop_ranges.iter().rev()` behavior, whereas `["a1", "after_mid_drop", "a0", "a2"]` confirms the forward index ordering of `3ef0c22cd` / `0259d5e9a`.
   *Scope limit:* A clean run validates only the specific control-flow graphs, struct/tuple/array/box shapes, and Edition 2024 semantics exercised in `PROBE_A_CODE`..`PROBE_C_CODE`; it does not cover `[T]` slice drop loops, `AsyncDrop` coroutines, or multi-variant partial enum moves.

2. **Target-narrow source diff against upstream `rust-lang/rust`:**
   Compare future revisions against `0259d5e9a81c6af08e40f8c204f2c0c41dca1647` specifically across:
   - `compiler/rustc_mir_transform/src/elaborate_drops.rs` (`drop_style`, `drop_flags_on_init`, `drop_flags_for_*`),
   - `compiler/rustc_mir_transform/src/elaborate_drop.rs` (`drop_ladder`, `open_drop_for_adt`, `open_drop_for_array`, `open_drop_for_box_contents`),
   - `compiler/rustc_mir_dataflow/src/move_paths/builder.rs` (`adt.has_dtor(tcx)`),
   - `compiler/rustc_mir_build/src/builder/scope.rs` (`scope.drops.iter().rev()`), and
   - `compiler/rustc_ty_utils/src/needs_drop.rs` (`is_manually_drop()`, `is_union()`).
   If `drop_ranges.iter()` or `adt.has_dtor(tcx)` or `drop_style` changes, re-run live MIR dumps (`-Zdump-mir=ElaborateDrops`) for the affected construct.

3. **Kernel-check the Lean `v4.34.1` mechanization (`~3–8 s`):**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MirDropElaborationDynamicFlagsAndOrderSoundness.lean
   ```
   A zero exit status establishes that all theorems, invariants, and four end-to-end witness executions compile inside Lean's trusted kernel without warnings or `sorry`. Re-running a Lean `collectAxioms` + `isUnsafe`/`isPartial`/`_unsafe_rec` check with `-M4096` confirms axiom purity (`[Quot.sound, propext]`, `unsafeRecs = 0`).
