# `rustc` drop elaboration: drop flags, open-drop ladders, unwind cleanup, and a kernel-checked refinement model

## Summary

`ElaborateDrops` turns every *conditional* `Drop` terminator of analysis MIR ("drop whatever is
initialized here") into unconditional drops guarded by boolean drop-flag locals. This report pins
the pass at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, measures it on real MIR and
at run time with that exact compiler, and gives a Lean `v4.34.1` model of it with a kernel-checked
refinement theorem and three sharpness counterexamples. What a later reader should retain:

1. **Four drop styles, decided per `Drop` from two dataflow bitsets.** No move path below the
   place may be initialized: `Dead` (the terminator becomes `goto`). None may be uninitialized:
   `Static` (an unconditional `Drop` stays). Otherwise a single move path is `Conditional`
   (`switchInt` on its flag, then drop) and a place with child move paths is `Open` (a *ladder* of
   per-field drops; if one field's destructor panics, the remaining fields are dropped on a
   cleanup half-ladder whose own unwind action is `terminate(cleanup)`). A flag local is created
   only for a move path that is both maybe-initialized and maybe-uninitialized at some `Drop`.
   `Basis: source + execution`
2. **Measured cost on 32 specimen functions:** 16 flag locals in 14 functions, 39 flag tests, 64
   flag writes (19 `true`, 45 `false`); basic blocks 376 → 540 immediately after the pass and 382
   at `runtime-post-cleanup`; `Drop` terminators 153 → 127. The 153 pre-elaboration drops were
   elaborated as 67 `Dead`, 54 `Static`, 18 `Open`, 14 `Conditional`. `-C panic=abort` does
   not change the elaboration (same flags, styles, drops and flag tests in every function);
   `AbortUnwindingCalls` afterwards turns every unwind edge into `unreachable` and deletes all
   cleanup blocks. `Basis: execution`
3. **Elaborated `Static` and `Conditional` drops do not clear the drop flag.** In the MIR that
   MIR building produced for the specimens, such a drop is followed by a `StorageDead` (treated as
   a move-out, which clears the flag), by the assignment of a new value (which sets it), or by the
   end of the function. A hand-written analysis-dialect body that drops a
   place on one branch and again at the join, with no `StorageDead` in between, is compiled by the
   real pass into a flag test that reads the stale `true`: the destructor **runs twice** in the
   native binary. The pass therefore has an input side condition beyond its dataflow.
   `Basis: source + execution`
4. **What runs between a fatal second panic and the abort depends on the drop style.** With a
   fully initialized 3-tuple and a first destructor that panics during unwinding, a `Static` drop
   (one call of the tuple's drop glue) still runs the other two destructors before aborting, an
   `Open` ladder runs none. Same source-level ownership state, different output before `SIGABRT`.
   Any correctness statement for the pass must leave that window unspecified. `Basis: execution`
5. **Arrays with element move paths are open-dropped in reverse range order.** A fully
   initialized `[a0, a1]` whose element `a0` is moved by an array pattern on another path is
   dropped `a1` then `a0`; the same array with no such path is dropped `a0` then `a1`.
   `Basis: source + execution`
6. **Kernel-checked model** (`support/DropElaborationRefinement.lean`, 2,984 lines, 142 theorems,
   axioms `propext` and `Quot.sound` only): for every control-flow graph whose dataflow certificate
   passes a decidable checker, the elaborated body has the same outcome and the same trace of
   initializations, moves, destructor runs and panics as the reference semantics, for every fuel
   bound and every environment oracle; on aborting runs the elaborated trace *extends* the
   reference trace (item 4). No unconditional drop reaches an uninitialized leaf, and the leaves
   live at exit are those of the reference run. Three side conditions are shown necessary by
   kernel-evaluated counterexamples: the drop flag at a conditional-move join (double drop, or
   leak, without it), `terminate` on the cleanup half-ladder (with `continue` the run keeps
   unwinding after two panics and skips the rest of the ladder), and the stale-flag condition of
   item 3. `Basis: execution (Lean kernel) + derived`
7. **Anneal's trusted MIR cannot ingest any of this** at
   `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `Drop` and `UnwindTerminate` map to
   `TerminatorKind.unsupported`, and `unwindResume`, `assert`, `call` and every cleanup-block
   `return_` evaluate to `.fault .unsupported`. `Basis: source`

> **Scope caution.** The Lean development is a standalone model with its own small MIR. It is not
> a proof about the Rust source of `ElaborateDrops`, it does not import Anneal's `Trusted.*`
> modules, and it covers tuple/struct-like move-path trees only (no enum variants, `Box`
> contents, arrays, slices, `Drop` impls on aggregates, async drops or coroutines). See
> **Boundaries**.

## Applicability

**Subjects and how they relate.**

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` is the commit hash reported by the
  compiler binary that produced every MIR dump and native run here (`rustc 1.98.0-nightly
  (14210df0e 2026-05-31)`, host `x86_64-unknown-linux-gnu`, LLVM 22.1.6). All source citations
  with a `compiler/` or `library/` path refer to this commit, so source and execution describe
  the same compiler.
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476` is the `src/doc/reference`
  submodule commit recorded by that `rust-lang/rust` commit; it supplies the documented drop
  order and "partially initialized" rule.
- `rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07` supplies RFC 320, the design the pass
  implements (`text/0320-nonzeroing-dynamic-drop.md`).
- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` is examined only for what its trusted
  MIR syntax and semantics do with `Drop` and unwinding.
- `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) is the toolchain that
  kernel-checked the model.

**Configuration of the measurements.** Edition 2021, `-C opt-level=0 -C debuginfo=0`, each
specimen file compiled once with `-C panic=unwind` and once with `-C panic=abort`. MIR is dumped
with the unstable `-Zdump-mir` flag around `ElaborateDrops` and `AbortUnwindingCalls` and at
`runtime-post-cleanup`. Seven specimen bodies are hand-written MIR (`#[custom_mir]`, an unstable
compiler-internal testing feature); they are identified as such wherever they are used.

**What generalizes and why.**

- The description of the pass (Findings 1–5, 9, 10) is tied to the cited source lines. It applies
  to other compiler versions only as far as those lines are unchanged; the file that holds the
  generic elaborator has already moved once (Finding 1).
- The counts in Finding 8 describe the 32 specimen functions of this package, which were written
  to exercise the pass. They are not a census of real code and should not be extrapolated.
- Native behaviour was observed on one target (`x86_64-unknown-linux-gnu`). The MIR-level
  findings are target-independent in the source; the abort mechanics (signal, messages) are not
  claimed for other targets.
- The Lean theorems hold for every body, certificate, fuel bound and oracle of the model. Their
  bearing on `rustc` rests on the correspondence argued in Findings 11 and 14, which is checked
  only on the shapes listed there.

## Findings

### 1. Where the pass sits and what it consumes

`Basis: source + execution`

`run_runtime_lowering_passes` (`compiler/rustc_mir_transform/src/lib.rs` L626–650) runs, in
order, `CriticalCallEdges`, `PostAnalysisNormalize`, `Subtyper`, `ElaborateDrops`, the
`CheckDropRecursion` lint, `AbortUnwindingCalls`, `AddMovesForPackedDrops`, `EraseDerefTemps`,
`ElaborateBoxDerefs`, `StateTransform`. The dumps number them `2-2-004.ElaborateDrops` and
`2-2-006.AbortUnwindingCalls`.

The pass lives in two files. `compiler/rustc_mir_transform/src/elaborate_drops.rs` (521 lines)
owns the dataflow, the flags and the per-terminator driver. The generic elaborator
(`DropStyle`, `DropFlagMode`, `Unwind`, the `DropElaborator` trait at L82–140, `elaborate_drop`,
and the ladder builders) is `compiler/rustc_mir_transform/src/elaborate_drop.rs` (1,424 lines).
The path `compiler/rustc_mir_dataflow/src/elaborate_drops.rs`, where this code used to live, does
not exist at this commit (HTTP 404 on the raw file); `compiler/rustc_mir_dataflow` retains
`DropFlagState::{Present, Absent}` (`drop_flag_effects.rs` L10–26, where `DropFlagState::value`
maps `Present` to `true` and `Absent` to `false`) and `drop_flag_effects_for_location`.

Upstream itself documents the input semantics as unfinished. The doc comment of
`TerminatorKind::Drop` (`compiler/rustc_middle/src/mir/syntax.rs` L742–760) reads:

> `Drop` before drop elaboration is a *conditional* execution of the drop glue. Specifically, the
> `Drop` will be executed if...
>
> **Needs clarification**: End of that sentence. This in effect should document the exact
> behavior of drop elaboration. The following sounds vaguely right, but I'm not quite sure:
>
> > The drop glue is executed if, among all statements executed within this `Body`, an assignment
> > to the place or one of its "parents" occurred more recently than a move out of it. This does
> > not consider indirect assignments.

The reference semantics of the Lean model (Finding 11) is one precise completion of that
sentence, per move-path leaf.

The driver (`elaborate_drops.rs` L52–88) gathers move paths only for types with
`needs_drop`, runs `MaybeInitializedPlaces` and `MaybeUninitializedPlaces` to a fixpoint, and then
calls, in this order, `collect_drop_flags`, `elaborate_drops`, `drop_flags_on_init`,
`drop_flags_for_fn_rets`, `drop_flags_for_args`, `drop_flags_for_locs` (L276–287).

### 2. Drop styles, flag creation and flag writes

`Basis: source + execution`

`drop_style` (`elaborate_drops.rs` L170–193), for the mode `Deep` used on every `Drop`
terminator, ORs the two bits over the move path and all its descendants and counts them:

```rust
match (maybe_init, maybe_uninit, multipart) {
    (false, _, _) => DropStyle::Dead,
    (true, false, _) => DropStyle::Static,
    (true, true, false) => DropStyle::Conditional,
    (true, true, true) => DropStyle::Open,
}
```

`multipart` is `children_count != 1`. `Open` therefore also covers a place whose parts are each
statically known but differ: `partial_move_tuple` (an unconditional `consume(p.0)`) has 2 `Open`
drops and 0 flags.

`collect_drop_flags` (L289–333) creates a `bool` temp for a move path only when
`maybe_init && maybe_uninit` holds for it at some `Drop` that covers it. `set_drop_flag`
(L416–422) takes a `DropFlagState` (`Present` → `const true`, `Absent` → `const false`) and is a
no-op for a path without a flag. Through the `DropElaborator` trait (`elaborate_drop.rs` L82–140),
the generic elaborator queries `drop_style`, `get_drop_flag`, `clear_drop_flag`, and subpath
projections (`field_subpath`, `deref_subpath`, `downcast_subpath`, `array_subpath`) from the
driver.

Flag writes come from four places:

| Source function | Writes |
| :-- | :-- |
| `drop_flags_on_init` (L424–431) | `flag = const false` for every flag at `Location::START` |
| `drop_flags_for_args` (L453–462) | `true` for argument paths at `Location::START` |
| `drop_flags_for_locs` (L464–520) | at every statement and terminator location of the *original* blocks, `false` for each move-out and `true` for each initialization (`drop_flag_effects_for_location`, `compiler/rustc_mir_dataflow/src/drop_flag_effects.rs` L106–135); `Drop` terminators are skipped with the comment "drop elaboration should handle that by itself" (L477–480) |
| `drop_flags_for_fn_rets` (L433–451) and the tail of `drop_flags_for_locs` (L500–518) | `true` for a call destination: at the start of the return block when the call's unwind action is `Cleanup`, before the call otherwise |

`StorageDead(local)` counts as a move-out of the local in move-path gathering
(`compiler/rustc_mir_dataflow/src/move_paths/builder.rs` L401–406), so every `StorageDead` of a
flagged local writes `false`.

Measured on `cond_move` (`let x = Loud::new("x"); if c { consume(x); } effect("join");`), from
`support/probe_output/mir/panic_unwind/cond_move.ElaborateDrops.after.mir`: one new local
`_8: bool`; `_8 = const false;` then `_8 = const true;` in `bb0` before the constructor call;
`_8 = const false;` before `_6 = move _2;`; the scope-end `drop(_2) -> [return: bb7, unwind
continue]` replaced by `goto` to a new block `switchInt(copy _8) -> [0: bb7, otherwise: bb11]`
with `bb11: drop(_2) -> [return: bb7, unwind: bb10]`; and `_8 = const false;` in `bb7` at the
`StorageDead(_2)`. The cleanup-path `drop(_2) -> [return: bb10, unwind terminate(cleanup)]`
gets its own flag test in new cleanup blocks. Native output: `effect join; drop x` with argument
`0`, `consume x; drop x; effect join` with argument `1`; one destructor run in both.

### 3. Open drops: the ladder and its unwind half

`Basis: source + execution`

`open_drop` (`elaborate_drop.rs` L1251–1286) dispatches on the type. For tuples, closures and
non-enum ADTs it builds a *drop ladder* (`drop_ladder`, L675–716). The doc comment gives the
shape for three fields:

```text
.d0:
    ELAB(drop location.0 [target=.d1, unwind=.c1])
.d1:
    ELAB(drop location.1 [target=.d2, unwind=.c2])
.d2:
    ELAB(drop location.2 [target=`self.succ`, unwind=`self.unwind`])
.c1:
    ELAB(drop location.1 [target=.c2])
.c2:
    ELAB(drop location.2 [target=`self.unwind`])
```

Three properties matter:

- Fields are dropped in declaration order: `drop_halfladder` (L609–624) walks
  `fields.iter().rev()` and threads each new block's target to the previously built one, so the
  block for field 0 is entered first.
- Every step of the unwind half-ladder is built with `Unwind::InCleanup`
  (`let unwind_ladder = vec![Unwind::InCleanup; fields.len() + 1];`, L695), which
  `Unwind::into_action` (L64–69) turns into
  `UnwindAction::Terminate(UnwindTerminateReason::InCleanup)`. If the drop being elaborated is
  itself in a cleanup block, the driver passes `Unwind::InCleanup`
  (`_ if data.is_cleanup => Unwind::InCleanup`, `elaborate_drops.rs` L361) and no unwind half is
  built at all.
- Each field is elaborated recursively (`drop_subpath`, L564–596). A field with its own move
  path gets a fresh `Drop` that is elaborated again with mode `Deep`; a field without one is
  guarded by the *parent's* flag (`complete_drop` with `path: self.path`, i.e. `DropFlagMode::Shallow`
  in `drop_flag_test_block`, L1369–1385).

Measured on `cond_partial_move_tuple` (`let p = (Loud::new("p0"), Loud::new("p1")); if c {
consume(p.0); }`): one flag `_10` for the move path `_2.0`, and the probe finds exactly one
instance of this block structure in the post-elaboration dump:

```text
bb23: switchInt(copy _10) -> [0: bb20, otherwise: bb22]
bb22: drop((_2.0: Loud)) -> [return: bb20, unwind: bb16]
bb20: drop((_2.1: Loud)) -> [return: bb15, unwind: bb14]
bb16 (cleanup): drop((_2.1: Loud)) -> [return: bb14, unwind terminate(cleanup)]
bb14 (cleanup): resume
```

`_2.1` has no move path of its own; `_2` itself is definitely initialized, so its part is dropped
unconditionally. Native output with argument `1`: `consume p0; drop p0; effect join; drop p1`.
The struct and nested-tuple specimens behave the same way (`drop s.a; drop s.c` after
`consume(s.b)`; `drop n00; drop n1` after `consume((n.0).1)`).

### 4. Assignment over an initialized place

`Basis: execution + source`

MIR building lowers `x = make("new", c)` to: evaluate the right-hand side into a temporary;
`drop(x)`; move the temporary into `x`. The dump of `assign_overwrite_old_dtor_panics`
(`support/probe_output/mir/panic_unwind/`) shows the unwind edge of that `drop` leading to a
cleanup block that *also* performs the move:

```text
bb2: drop(_2) -> [return: bb3, unwind: bb4]
bb3: _2 = move _3; ...
bb4 (cleanup): _2 = move _3; ... -> bb8
bb8 (cleanup): drop(_2) -> [return: bb9, unwind terminate(cleanup)]
```

Observed behaviour:

| Specimen, argument | Standard output | Exit |
| :-- | :-- | :-- |
| `assign_overwrite`, `0` | `drop old; effect after-assign; drop new` | 0 |
| `assign_overwrite`, `1` (constructor of the new value panics) | `drop old` | 101, 1 panic |
| `assign_overwrite_old_dtor_panics` (destructor of the old value panics) | `drop old; drop new` | 101, 1 panic |

So the old value is dropped exactly once whether or not the constructor panics, and when the old
value's destructor panics the assignment is still completed and the *new* value is dropped by the
cleanup chain. After elaboration both `drop(_3)` terminators for the moved-from temporary are
`Dead`.

### 5. Panics in destructors

`Basis: execution + source + documentation`

The documentation of `Drop::drop` (`library/core/src/ops/drop.rs` L221–231) states that a panic
in `drop()` during unwinding ("a 'double panic'") "will likely abort the program" and that "even
if this panics, the value is considered to be dropped". The mechanism is static: a `Drop` or call
in a cleanup block carries `unwind terminate(cleanup)`, and that edge ends in the lang item
`core::panicking::panic_in_cleanup` (`library/core/src/panicking.rs` L340–354; its doc comment
says it "is called directly by the codegen backend"), which raises a non-unwinding panic with the
text "panic in a destructor during cleanup".

| Specimen | What happens | Standard output | Result |
| :-- | :-- | :-- | :-- |
| `dtor_panics_normal_path` | destructor of `a` panics at scope end | `effect body; drop a; drop b` | exit 101, 1 panic |
| `tuple_first_dtor_panics` | first field of a 3-tuple panics inside the tuple's drop glue | `effect body; drop t0; drop t1; drop t2` | exit 101, 1 panic |
| `tuple_two_dtors_panic` | first and second field panic | `effect body; drop t0; drop t1` | `SIGABRT` |
| `double_panic` | explicit panic, then destructor of `a` panics during unwinding | `drop a` | `SIGABRT`; `b` never dropped |
| `static_glue_in_cleanup` | explicit panic; fully initialized 3-tuple dropped by one `Static` drop in a cleanup block; `t0` panics | `drop t0; drop t1; drop t2` | `SIGABRT` |
| `open_ladder_in_cleanup`, `0` | same tuple, same run-time state, but `t.2` is moved on another path, so the cleanup drop is an `Open` ladder | `drop t0` | `SIGABRT` |

Every `SIGABRT` row prints "panic in a destructor during cleanup" and "thread caused
non-unwinding panic. aborting.".

The last two rows differ only in the style chosen by the pass. In `static_glue_in_cleanup` the
cleanup block is `drop(_3) -> [return: bb14, unwind terminate(cleanup)]`: the drop glue of the
tuple is an ordinary function with its own ladder, so after `t0` panics it drops `t1` and `t2`,
resumes unwinding, and only then reaches the `terminate` edge. In `open_ladder_in_cleanup` the
cleanup blocks are `drop((_3.0: Loud)) -> [return: bb35, unwind terminate(cleanup)]`,
`drop((_3.1: Loud)) -> ...`, a flag test, `drop((_3.2: Loud)) -> ...`: the first panic takes the
`terminate` edge immediately. Which destructors run between the fatal panic and the abort is
therefore a function of the dataflow precision, not of the program's run-time state.

### 6. Types without drop glue

`Basis: execution + source`

`MoveData::gather_moves(body, tcx, |ty| ty.needs_drop(tcx, typing_env))` (`elaborate_drops.rs`
L59) restricts move paths to types that need dropping, and the driver replaces a `Drop` of a
place whose type does not need dropping by `goto` before looking at move paths (L345–355).

| Specimen | `Drop` terminators before → after | Destructor runs |
| :-- | :-- | :-- |
| `manually_drop` (`ManuallyDrop::new(Loud::new("m"))`) | 1 → 0 | 0 |
| `maybe_uninit` (`MaybeUninit::new(Loud::new("u"))`) | 1 → 0 | 0 |
| `copy_type` (a `Copy` struct) | 0 → 0 | 0 |

The single pre-elaboration drop in the first two rows is not a drop of the wrapper: it is the
cleanup-path drop of the temporary `Loud` that was moved into the constructor call, and it is
`Dead`. MIR building emits no `Drop` for the `ManuallyDrop<Loud>` or `MaybeUninit<Loud>` local.
The generic `generic_cond_move<T>(x: T, c: bool)` keeps a flag and a `Conditional` drop for `x`
in its (polymorphic) MIR; what monomorphization at a `Copy` type does with it was not examined.

### 7. `-C panic=abort` and non-unwinding ABIs

`Basis: execution + source`

`ElaborateDrops` is insensitive to the panic strategy. For all 32 functions the `panic=abort`
build has the same flag locals, style counts, post-elaboration `Drop` count and flag-test count
as the `panic=unwind` build (probe check `panic_abort::same_elaboration_as_unwind`); totals are
378 → 542 blocks versus 376 → 540 (two specimens without drops have one extra cleanup block
before the pass under `panic=abort`).

The difference is made two passes later. `AbortUnwindingCalls`
(`compiler/rustc_mir_transform/src/abort_unwinding_calls.rs` L67–139):

- replaces `UnwindResume` by `UnwindTerminate(Abi)` in a body whose ABI cannot unwind (L77–83);
- sets the unwind action of a call, `Drop`, `Assert` or `FalseUnwind` in a non-cleanup block to
  `Unreachable` when the callee cannot unwind (L116–122); under `panic=abort` this is every Rust
  call and every `Drop`;
- otherwise, in a body that cannot unwind, turns `Continue` into `Terminate(Abi)` (L123–134);
- removes dead blocks (L138).

Measured over the 32 functions under `panic=abort`: 542 blocks and 209 cleanup blocks before the
pass, 333 blocks and 0 cleanup blocks after, 156 unwind edges, all `unreachable`. At run time the
first panic aborts and no destructor runs (`double_panic`: empty standard output, `SIGABRT`, 1
panic message).

`nounwind_abi` (an `extern "C"` function with a local `g` and a call that panics) under
`panic=unwind`: before `AbortUnwindingCalls` 1 `resume` and 1 `unwind continue`; after, 0
`resume`, 1 `terminate(abi)` terminator and 1 `unwind terminate(abi)` edge, cleanup edges kept.
Native run with argument `1`: `drop g`, then "panic in a function that cannot unwind" and
`SIGABRT`: cleanup runs up to the ABI boundary, as the Reference allows
(`destructors.process-termination`: "either no destructors will run, or all destructors up until
the ABI boundary will run").

### 8. Measured elaboration overhead

`Basis: execution`

Totals over the 32 analysed functions of `support/specimens/drop_specimens.rs`, `panic=unwind`
(`support/probe_output/probe_results.json`, key `configurations.panic_unwind.totals`):

| Quantity | Before `ElaborateDrops` | After `ElaborateDrops` | At `runtime-post-cleanup` |
| :-- | --: | --: | --: |
| Basic blocks | 376 | 540 | 382 |
| Cleanup blocks | 108 | 207 | 126 |
| Locals (arguments included) | 254 | 281 | not measured |
| `bool` drop-flag locals | 0 | 16 (in 14 functions) | not measured |
| `Drop` terminators | 153 | 127 | not measured |
| `Drop` terminators in cleanup blocks | 78 | 81 | not measured |
| Flag tests (`switchInt(copy flag)`) | 0 | 39 | not measured |
| Flag writes | 0 | 64 (19 `true`, 45 `false`) | not measured |
| Unwind edges `unwind: bbN` | 114 | 124 | not measured |
| Unwind edges `unwind continue` | 70 | 32 | not measured |
| Unwind edges `unwind terminate(cleanup)` | 78 | 83 | not measured |

The 11 additional non-flag locals are temporaries of the box ladder (8, in `box_cond_move`) and
discriminant temporaries of the enum ladder (3, in `option_cond_move`). `unwind
continue` shrinks because the driver maps `Continue` to an explicit resume block
(`UnwindAction::Continue => Unwind::To(self.patch.resume_block())`, `elaborate_drops.rs` L363).

Style of the 153 pre-elaboration `Drop` terminators (a syntactic classification of the
post-elaboration dump by the probe, described in the docstring of
`support/probe_drop_elaboration.py`): `Dead` 67, `Static` 54, `Open` 18, `Conditional` 14.

Selected rows:

| Function | Flags | Blocks before → after (→ `runtime-post-cleanup`) | Styles |
| :-- | --: | :-- | :-- |
| `static_drop` | 0 | 6 → 6 (6) | 2 static |
| `cond_move` | 1 | 11 → 15 (12) | 2 conditional, 1 dead |
| `cond_init` | 1 | 12 → 16 (11) | 2 conditional, 3 dead |
| `loop_break_move` | 1 | 17 → 21 (18) | 2 conditional, 1 dead |
| `two_cond_moves` | 2 | 16 → 24 (18) | 4 conditional, 2 dead |
| `partial_move_tuple` | 0 | 12 → 19 (9) | 2 open, 1 static, 3 dead |
| `cond_partial_move_tuple` | 1 | 15 → 28 (17) | 2 open, 1 static, 3 dead |
| `cond_partial_move_struct` | 1 | 18 → 34 (23) | 2 open, 2 static, 4 dead |
| `cond_partial_move_nested` | 1 | 20 → 44 (23) | 2 open, 2 static, 6 dead |
| `option_cond_move` | 2 | 16 → 35 (16) | 2 open, 4 dead |
| `box_cond_move` | 1 | 13 → 25 (16) | 2 open, 2 dead |
| `array_cond_move` | 1 | 17 → 30 (18) | 2 open, 1 static, 5 dead |

Run-time cost (time, code size) of flags and ladders: not measured.

### 9. Stale flags: what the pass relies on

`Basis: source + execution + derived`

The dataflow treats a `Drop` terminator as de-initializing its place
(`drop_flag_effects_for_location`, `drop_flag_effects.rs` L124–130: "Drop does not count as a
move but we should still consider the variable uninitialized"). The flag machinery does not:

- `drop_flags_for_locs` skips `Drop` terminators (`elaborate_drops.rs` L477–480);
- `elaborate_drop` (`elaborate_drop.rs` L500–523) emits a plain `Drop` for `Static` and
  `drop_flag_test_block` + `Drop` for `Conditional` (`complete_drop`, L1289–1292);
- the only flag clears issued by the elaborator are `drop_flag_reset_block` (L1297–1312) at the
  bottom of an open ladder, for the parent's own flag (`drop_ladder_bottom`, L626–635), and in the
  slice drop loop (L1239); the function returns without clearing when on the unwind path.

So after a `Static` or `Conditional` drop the flag of the dropped path can still be `true`. In
the MIR that MIR building produced for this package's specimens this is invisible: such a drop is
followed by `StorageDead(local)` (scope exit) or by the assignment of the new value, both of
which write the flag, or by the exit of the function. That no later flag test can observe the
stale value is an input invariant of the pass, not something the pass checks.

Three hand-written analysis-dialect bodies in `support/specimens/custom_mir_specimens.rs` isolate
it. Each calls a constructor into `x`, branches on `c`, and ends in `Drop(x)` at the join:

| Body | On the `true` branch | Flag locals | Standard output, argument `1` |
| :-- | :-- | --: | :-- |
| `join_reference` | `consume(Move(x))` | 1 | `consume x; drop x` (one destructor run) |
| `stale_flag_join` | `Drop(x)` | 1 | `drop x; drop x` (**two** destructor runs) |
| `stale_flag_join_storage_dead` | `Drop(x)` then `StorageDead(x)` | 1 | `drop x` |

The post-elaboration MIR of `stale_flag_join` is

```text
bb0: _3 = const false; _3 = const true; _2 = make() -> [return: bb1, unwind continue]
bb1: switchInt(copy _1) -> [1: bb2, otherwise: bb3]
bb2: drop(_2) -> [return: bb3, unwind: bb5]
bb3: goto -> bb7
bb7: switchInt(copy _3) -> [0: bb4, otherwise: bb6]
bb6: drop(_2) -> [return: bb4, unwind: bb5]
```

with no write to `_3` after `bb2`. The first drop was classified `Static`, the second
`Conditional`. With the literal reading of the documented sentence in Finding 1 ("an assignment
... occurred more recently than a move out of it") the second drop *should* run, because a
`Drop` is not a move; with the reading the dataflow uses, it should not. The two readings agree
on every body in which no flag is read while stale; the Lean checker's `st` component (Finding 11)
is exactly that condition, and `staleFlagJoin_double_drop` (Finding 13) is this body in the model.

`#[custom_mir]` bypasses MIR building and borrow checking and is not a supported way to write
programs; this is a statement about what the pass assumes of its input, relevant to any tool that
feeds pre-elaboration MIR from another source into it or re-implements it.

### 10. Arrays

`Basis: source + execution`

`open_drop_for_array` (`elaborate_drop.rs` L1096–1161) partitions a fixed-size array into
sub-slices without element move paths and single elements with one, and passes them to
`drop_ladder` as

```rust
let fields = drop_ranges
    .iter()
    .rev()
    .map(|p| { ... })
```

Since `drop_ladder` drops its `fields` in list order (Finding 3), the ranges are dropped from the
last to the first.

| Specimen, argument | Run-time state at scope end | Destructor order |
| :-- | :-- | :-- |
| `array_static_drop` | `[arr0, arr1]` initialized, no element move path | `drop arr0; drop arr1` |
| `array_cond_move`, `0` | `[arr0, arr1]` initialized, `arr0` has a move path (moved when `c`) | `drop arr1; drop arr0` |
| `array_cond_move`, `1` | `arr0` moved out | `consume arr0; drop arr0; ...; drop arr1` |

The Reference (`destructors.operation`) says "The elements of an array or owned slice are dropped
from the first element to the last." The second row does not follow that order. Whether upstream
regards this as intended was not examined.

### 11. The Lean model: what is defined

`Basis: source (support/DropElaborationRefinement.lean) + derived`

The file has no imports. Sections 1–7 (1,051 lines, 55 definitions) are the specification; the
main theorem's statement mentions only these and the two-line relation `RRel` (Finding 12).

- **Places.** `MovePath := Nat`. `PlaceTree` is `leaf mp | node l r`: the move-path tree below a
  place; binary nodes nest to any arity. `PlaceTree.leaves` lists leaves in drop (declaration)
  order.
- **Run-time ownership.** `InitTree` is `leaf mp init | node l r`: the frame's move-path tree
  with one initialization bit per leaf (`get`, `setAll`, `live`).
- **Observations.** `Event` is `init mp | moved mp | drop mp | panic`. `Outcome` is
  `returned live | unwound live | aborted | unreachable | badJump | doubleDrop mp | outOfFuel`,
  where `live` lists the leaves still initialized at exit. An `Oracle` (a list of booleans)
  decides branch directions, whether a call panics and whether a destructor panics.
- **Drop glue** `glue mode leaves unwinding init oracle`: drops leaves in order; a destructor
  that panics still consumes its value; after the first panic the remaining leaves are dropped
  with `unwinding = true`; a panic while `unwinding` aborts. Modes: `conditional` (skip
  uninitialized leaves: pre-elaboration `Drop`), `checked` (unconditional; a drop of an
  uninitialized leaf is reported as `doubleDrop`), `blind` (unconditional, nothing checked: a
  machine).
- **Reference bodies.** Statements `init p | move p | nop`; terminators
  `goto | branch | call ret unw | drop p ret unw | ret | resume | abort | unreachable` with
  `UnwindAction` `continue_ | cleanup b | terminate | unreachable`. `drop p ret unw` runs
  `glue .conditional` over the leaves of `p`; if `unw` is `terminate` the glue starts with
  `unwinding = true`. `runRef` is the fuel-bounded run from block 0 with nothing initialized.
- **Certificate.** Every block carries `Facts` `{mi, di, st}`: leaves that may be initialized,
  leaves that are definitely initialized (the complement of `MaybeUninitializedPlaces`), leaves
  whose flag may be stale. `check` requires: facts flow along every edge (`Facts.le`), the entry
  block claims nothing definitely initialized, every `init` targets leaves of the frame, and for
  every `drop p` (`dropOk`) the place has no repeated move path and each leaf that is maybe-
  but not definitely-initialized owns a flag and is not in `st`. A drop adds to `st` the leaves it
  covers that may have been initialized; `init` and `move` remove their leaves from `st`.
- **Elaboration.** `elaborate` maps every block. Statements get `setFlag mp true/false` in front
  of each `init`/`move` for the flagged leaves. `drop p ret unw` becomes a `Ladder`, a tree of
  `exit kont | test flag set unset | drop p ret unw` nodes standing for the fresh blocks of one
  elaborated drop:

  ```lean
  noncomputable def elabDrop (f : Facts) : PlaceTree → Ladder → Ladder → Ladder
    | .leaf l, ret, unw =>
      if !f.mi.contains l then ret
      else if f.di.contains l then .drop (.leaf l) ret unw
      else .test l (.drop (.leaf l) ret unw) ret
    | .node a b, ret, unw =>
      if (a.leaves ++ b.leaves).all (fun l => !f.mi.contains l) then ret
      else if (a.leaves ++ b.leaves).all (fun l => f.di.contains l) then .drop (.node a b) ret unw
      else elabDrop f a (elabDrop f b ret unw) (elabCleanup f b unw)
  ```

  `elabCleanup` is the same with `.exit .abort` as the unwind continuation of every drop
  (`Unwind::InCleanup`). The four branches are `Dead`, `Static`, `Conditional` and `Open`; the
  third argument of the recursive call is the unwind half-ladder. As in the pass, elaborated
  drops do not write flags.
- **Elaborated semantics.** `runElab mode` executes the elaborated body. Flag tests read the
  `DropFlagEnv` (`MovePath → Bool`, all `false` at entry); `drop` is `glue mode` over *all* leaves
  of its place. The `InitTree` is ghost state there: no elaborated instruction reads it.

Deliberate abstractions, each a point where the model is simpler than `rustc`: fresh blocks are a
tree instead of numbered blocks; the dataflow result is an input validated by `check`, not
computed; the parent's-own-bit of a move path with children is a separate leaf ("the rest of
`p`"); the flag clear at the bottom of an open ladder is omitted (it only makes a stale flag
accurate again, so the model's side condition is conservative there); a call's destination is
initialized by an `init` statement at the head of its return block.

### 12. The Lean model: what is proved

`Basis: execution (kernel check of support/DropElaborationRefinement.lean) + source`

```lean
def RRel (t s : Result) : Prop :=
  t = s ∨ (s.outcome = .aborted ∧ t.outcome = .aborted ∧ ∃ extra, t.trace = s.trace ++ extra)

theorem elaborate_refines (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle) :
    RRel (runElab .checked b fuel o) (runRef b fuel o)

theorem elaborate_refines_blind (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle) :
    RRel (runElab .blind b fuel o) (runRef b fuel o)

theorem elaborate_no_double_drop (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle) :
    NoDoubleDrop (runElab .checked b fuel o)

theorem elaborate_no_leak (b : Body) (hc : check b = true) (fuel : Nat) (o : Oracle)
    (h : NoLeak (runRef b fuel o)) : NoLeak (runElab .checked b fuel o)

theorem double_panic_aborts (b : Body) (hd : cleanupDiscipline b = true) (fuel : Nat) (o : Oracle) :
    (∀ live, (runRef b fuel o).outcome = .returned live →
      panicCount (runRef b fuel o).trace = 0) ∧
    (∀ live, (runRef b fuel o).outcome = .unwound live →
      panicCount (runRef b fuel o).trace = 1)
```

Reading:

- `elaborate_refines`: same outcome always (including the list of leaves live at `return` or at
  unwinding exit); identical trace unless the run aborts (`elaborate_exact_unless_aborted`); on
  an aborting run the elaborated trace is the reference trace followed by further events
  (`elaborate_trace_extends`). The proof is a lock-step simulation by induction on fuel. Its
  invariant `Inv` says: the facts are sound for the ownership state, and every flag whose leaf is
  not in `st` equals the initialization bit of its leaf. The ladder lemma `elab_ladder` relates
  the elaborated ladder of a place to conditional glue over its leaves, by induction on the
  `PlaceTree`.
- `elaborate_refines_blind`: the same for a machine that checks nothing, obtained from
  `runTgt_blind_eq_checked` (where the checked run reports no double drop, the unchecked run is
  equal to it).
- `NoDoubleDrop r` is `∀ mp, r.outcome ≠ .doubleDrop mp`. It holds on returning, unwinding *and*
  aborting runs, so it also covers the extra destructor runs before an abort.
- `NoLeak r` is `∀ live, (r.outcome = .returned live ∨ r.outcome = .unwound live) → live = []`.
  It is *preserved*, not established: whether the reference run leaves a leaf initialized at exit
  is a property of the body (MIR building schedules the drops), not of the pass.
- `double_panic_aborts`: `cleanupDiscipline` is the model's copy of the MIR validator's rules
  (`compiler/rustc_mir_transform/src/validate.rs`, `check_edge` L140–166 and `check_unwind_edge`
  L247–276: ordinary edges stay on one side of the cleanup boundary, `Continue` and `Cleanup` only
  outside cleanup blocks, `Terminate(InCleanup)` only inside, `Return` not in a cleanup block,
  `UnwindResume` only in one). Under it, a returning run contains no panic and a run that unwinds
  out of the frame contains exactly one; a second panic can only end in `aborted` (or in one of
  the error outcomes). `double_panic_aborts_elaborated` transfers this to `runElab`.

The "extends" clause is not slack in the proof: `Example.trace_before_abort_depends_on_certificate`
exhibits one sequence of blocks with two certificates that both check and whose elaborations
produce different traces on the same aborting run (Finding 13), mirroring Finding 5.

### 13. Sharpness: three kernel-evaluated counterexamples and their native mirrors

`Basis: execution (Lean kernel; native runs of hand-written MIR)`

Unless stated otherwise the theorems below are in `namespace DropElab.Example` and rest on
`decide`, i.e. on kernel evaluation of the model on a concrete body, fuel and oracle.

**CE1: the drop flag at a conditional-move join is necessary.** Body `condMove`: block 0
initializes `x` and branches; block 1 moves `x` out; block 2 (join) drops `x`; block 3 returns.

- `ce1_no_flag_always_drop_double_drop`: lowering the join to an unconditional drop gives, on the
  path that moved `x`, the trace `[init 0, moved 0, drop 0]`: one initialization, **two**
  discharges of ownership (`dischargeCount = 2`); the checked semantics reports `doubleDrop 0`.
- `ce1_no_flag_never_drop_leak`: deleting the drop gives, on the path that kept `x`, the trace
  `[init 0]` and outcome `returned [0]`: one initialization, **zero** discharges
  (`dischargeCount = 0`), leaf still live at `return`.
- `condMove_exactly_once`: the real elaboration gives `dischargeCount = 1` on both paths.
- General form, not tied to this body and proved by induction (`namespace DropElab`):
  `no_flagFree_ladder_is_conditional` shows that *no* ladder without a flag test can emit
  `[drop mp]` in one ownership state and `[]` in another; `flagFree_state_independent` shows such
  a ladder's events and exit do not depend on the ownership state or on the flags at all.

Native mirror (`support/specimens/custom_mir_specimens.rs`, runtime-dialect hand-written MIR, so
`Drop` is unconditional and no pass intervenes): `join_no_flag_always_drop` with argument `1`
prints `consume x; drop x; drop x` (two destructor runs); `join_no_flag_never_drop` with argument
`0` prints nothing for `x` (zero destructor runs); the analysis-dialect `join_reference`, lowered
by the real pass, prints `drop x` exactly once for both arguments.

**CE2: `terminate` on the unwind half of a ladder is necessary.** Body `threeFields`: a 3-field
place whose third field is conditionally moved, so its scope-end drop is `Open`. Oracle: do not
move; the destructors of fields 0 and 1 both panic.

- `ce2_reference_aborts`: reference trace `[init 0, init 1, init 2, drop 0, panic, drop 1,
  panic]`, outcome `aborted`. `ce2_terminate_lowering_aborts`: the real elaboration is equal.
- `ce2_continue_lowering_unwinds`: with `elaborateContinue`, identical except that a panic on the
  unwind half continues to the enclosing unwind target, the same trace ends in `unwound [2]`:
  two panics, no abort, the ladder step for field 2 skipped, field 2 initialized once and dropped
  zero times when the frame is left. `ce2_continue_is_not_a_refinement` states that this variant
  violates the refinement relation on a body whose certificate checks.
- At the level of unwind actions: `cleanupChain .terminate` passes both `check` and
  `cleanupDiscipline` and aborts on the nested panic; `cleanupChain .continue_` fails
  `cleanupDiscipline` and leaves the frame unwinding after two panics with a leaf live
  (`cleanupChain_continue_violates_law`), contradicting the conclusion of `double_panic_aborts`.

Native mirror: none can be produced, because the compiler refuses the shape. Compiling
`support/specimens/custom_mir_cleanup_continue.rs` (a cleanup-block `Drop` with
`UnwindContinue()`) fails with exit code 101 and "broken MIR in ... `UnwindAction::Continue` in
cleanup block" from `validate.rs`, without `-Zvalidate-mir` being passed. The well-formed variant
`cleanup_terminate` aborts with `SIGABRT` after `drop bomb`.

**CE3: the stale-flag condition is necessary.** Body `staleFlagJoin` is Finding 9's
`stale_flag_join`. `staleFlagJoin_rejected`: `check` is `false`. `staleFlagJoin_reference`: the
reference drops `x` once. `staleFlagJoin_double_drop`: the elaborated body's trace is `[init 0,
drop 0, drop 0]`, `dropCount = 2` for one initialization, and the checked semantics reports
`doubleDrop 0`. `staleFlagJoinStorageDead_ok`: with a move-out after the first drop the
certificate checks and `x` is dropped once. Native mirror: Finding 9.

**The pre-abort window.** `pairInCleanup di`: a pair dropped in a cleanup block, with a
certificate that either knows both fields are initialized (`[0, 1]`, `Static`) or only the first
(`[0]`, `Open`). Both certificates check (`pairInCleanup_both_check`), both reference runs are
`[init 0, init 1, panic, drop 0, panic]` / `aborted`, the `Static` elaboration additionally emits
`drop 1` after the fatal panic (`pairInCleanup_static_trace`), the `Open` one does not
(`pairInCleanup_open_trace`). Native mirror: `static_glue_in_cleanup` versus
`open_ladder_in_cleanup` (Finding 5).

### 14. Correspondence between the model and the compiler

`Basis: derived (from the execution evidence of Findings 2–10 and the Lean theorems)`

The model is tied to `rustc` only through the following points, each checked on one shape.

| Shape | Compiler evidence | Lean theorem (`DropElab.Example`) |
| :-- | :-- | :-- |
| Conditional move: flag written at init and at the move, tested at the join | `cond_move` dump and runs (Finding 2) | `condMove_elaborated_flag_writes`, `condMove_elaborated_join`, `condMove_moved`, `condMove_kept` |
| Two-field open ladder with unwind half | probe check `open_drop_ladder_shape::cond_partial_move_tuple` (Finding 3) | `condFieldMove_ladder` (the same five-block structure as a `Ladder` term) |
| One destructor panics: siblings still dropped, unwinding continues | `tuple_first_dtor_panics` | `condFieldMove_first_dtor_panics` |
| Two destructors panic: abort, later fields not dropped | `tuple_two_dtors_panic`, `open_ladder_normal_two_panics` | `condFieldMove_both_dtors_panic`, `ce2_reference_aborts` |
| Assignment over an initialized place, three panic scenarios | Finding 4 | `assignOverwrite_normal`, `assignOverwrite_constructor_panics`, `assignOverwrite_old_dtor_panics`, `assignOverwrite_double_panic` |
| Stale flag at a join; cleared by `StorageDead` | Finding 9 | `staleFlagJoin_double_drop`, `staleFlagJoinStorageDead_ok` |
| Join lowered without a flag | Finding 13, CE1 mirror | `ce1_no_flag_always_drop_double_drop`, `ce1_no_flag_never_drop_leak` |
| Pre-abort destructor runs depend on style | Finding 5 | `pairInCleanup_static_trace`, `pairInCleanup_open_trace` |

There is no mechanical translation from `rustc` MIR to the model's `Body`; the Lean bodies were
written by hand to mirror the specimens.

### 15. Anneal trusted MIR: `Drop` and unwind ingestion gaps

`Basis: source (joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613)`

`trusted/lean/Trusted/MirAst.lean` models `Runtime(PostCleanup)` MIR, i.e. MIR after this pass.

- `inductive UnwindAction` (L693–697) has `continue_ | unreachable | terminate | cleanup block`;
  `terminate` carries no `UnwindTerminateReason`.
- `inductive TerminatorKind` (L785–795; doc comment L742–784) has `goto`, `switchInt`, `return_`,
  `unreachable`, `unwindResume`, `assert`, `call` and `unsupported`. Its doc comment (L783–784)
  lists what `unsupported` stands for: "`UnwindTerminate`, `Drop`, indirect `Call`, `TailCall`,
  `Yield`, `CoroutineDrop`, `FalseEdge`, `FalseUnwind`, and `InlineAsm`".
- `structure BasicBlock` (L810–813; doc comment L797–809) keeps `cleanup : Bool := false`.
- `inductive TerminalOut` (`MirSemantics.lean` L602–604) has only `returned` and `unwound`, with
  no `aborted` outcome for `UnwindTerminate`.
- `isSupportedScalarOrUnitTy` (`MirSemantics.lean` L721–724) admits `bool` drop-flag locals
  (`.bool`) while rejecting non-fieldless ADTs; `evalOperandToSlot` (L949–976, which conservatively
  deinitializes moved non-ZST locals via `liveUninitSlot`) and `evalStatement` (L1407) also require
  `place.projection.isEmpty`, rejecting field-projected open drops.
- `trusted/rustc-capture/src/driver.rs` (L75–84) does not yet emit MIR bodies (`after_analysis`
  records only whether analysis completed without errors).

`trusted/lean/Trusted/MirSemantics.lean`, `evalTerminator` (L1537–1569):

```lean
  | .return_ =>
    if bb.cleanup then
      .fault .unsupported
    ...
  | .unwindResume | .assert _ _ _ _ _ | .call _ _ _ _ _ | .unsupported =>
    .fault .unsupported
```

Consequences for a body that went through `ElaborateDrops`:

| Construct after elaboration | In `Trusted.MirAst` | In `Trusted.MirSemantics` |
| :-- | :-- | :-- |
| `Drop(place)` (any style that keeps a drop) | `.unsupported` | `.fault .unsupported` |
| Flag locals, flag writes, `switchInt(copy flag)` | ordinary `bool` local, `assign`, `switchInt` | executable |
| `unwind: bbN`, `unwind terminate(cleanup)` edges | representable on `assert` and `call` only | never taken: `assert` and `call` fault first |
| Cleanup blocks | representable (`cleanup := true`) | unreachable; `return_` inside one faults |
| `resume` | `.unwindResume` | `.fault .unsupported` |
| `terminate(cleanup)` / `terminate(abi)` terminators | `.unsupported` | `.fault .unsupported` |

So the flag bookkeeping of this pass is already within the executable fragment, while everything
the flags guard (the drops themselves, drop glue, unwinding, double-panic abort) is outside it.
A semantics for `Drop` in that setting needs at least: drop glue per type; an unwinding control
state; the `terminate` reason; and a decision on the pre-abort window of Finding 5. Because the
ingested MIR is post-elaboration, the conditional-drop semantics and the certificate checker of
the model are not needed for ingestion; they matter for a verified re-implementation of the pass
or for validating its output against pre-elaboration MIR.

### 16. Analytical dimensions scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

| ID | Dimension | Basis | Result |
| :-- | :-- | :-- | :-- |
| `L1` | Authoring and proof velocity | execution (artifact size only) | Elapsed effort: **not measured**. Artifact size: 2,984 lines, 133,513 bytes, 142 `theorem`, 88 `def`, 26 `inductive`/`structure`; specification prefix (sections 1–7) 1,051 lines with 55 definitions. |
| `L2` | Toolchain / TCB build time | none | **not measured** (released Lean `v4.34.1` binary used; no imports beyond `Init`). |
| `L3` | Pass / certificate synthesis latency | none | **not measured**: the model has no dataflow solver (the certificates of the example bodies are written by hand), and the run time of `rustc`'s pass was not timed. |
| `L4` | Generated code performance | execution (static MIR counts only) | Run-time performance: **not measured**. Static MIR overhead (Finding 8): 16 flags, 39 flag tests, 64 flag writes, blocks 376 → 540 → 382 over 32 functions. |
| `L5` | Checking latency and throughput | execution | Kernel check of the module: 13.990 s wall clock (synchronous elaboration, kernel type checking on); audit run: 4.954 s. Throughput on larger bodies: **not measured**. |
| `L6` | RAM and artifact footprint | execution | Peak resident memory 637,564 kB (module) and 1,634,604 kB (audit, which imports `Lean`); `.olean` 4,294,408 bytes; package support material 732,592 bytes in 91 files. |
| `C1` | Specification and assumption auditability | execution (audit) | 0 imports; axioms used by any theorem: `propext`, `Quot.sound`; 329 of 596 kernel theorem constants use no axiom; 0 axioms, 0 `opaque` constants, 0 non-`safe` definitions, 0 `_unsafe_rec` helpers among 1,282 constants; the main statement depends on sections 1–7 and `RRel` only. |
| `C2` | Orthogonality and simplicity | derived | One `glue` function with three modes serves the reference, the checked and the unchecked semantics; normal and cleanup elaboration differ only in the unwind continuation; the certificate is three lists per block and `check` is a conjunction of per-statement, per-edge and per-drop conditions. |
| `V1` | Adequacy, mutation and non-vacuity | execution (Lean kernel; native runs) | 40 kernel-checked theorems on concrete bodies, including 9 bodies whose certificate checks (conditional move, field move, assignment with cleanup blocks, loop, three-field ladder, cleanup chain, stale-flag join with a move-out, cleanup pair under two certificates) and 5 mutants that each break one side condition (join without flag keeping the drop, join without flag deleting it, `continue` on the unwind half of a ladder, `continue` on a cleanup-block drop, stale flag). 39 probe checks pass on 136 native runs. |
| `V2` | Differential fuzzing | none | **not measured**: no generator; model and compiler are compared on 8 hand-picked shapes (Finding 14). |
| `V3` | Weak memory / crash / silicon | derived | **known not to apply** to the model (sequential, single frame). Native runs on one `x86_64-unknown-linux-gnu` host only. |
| `V4` | Held-out ecosystem replay | none | **not examined**: no crate outside this package's specimens was compiled or replayed. |

## Boundaries

**Not examined.**

- Enum variants (`open_drop_for_multivariant`, discriminant switches, the "master" flag of an
  enum), `Box` contents (`open_drop_for_box_contents`), slices and the drop loop, `Drop` impls on
  aggregates (`destructor_call_block`), async drops, drop lines and coroutines. `option_cond_move`
  and `box_cond_move` are measured (flags, blocks, output) but not modelled.
- `compute_dead_unwinds` and the `skipping_unreachable_unwind` refinement of the dataflow
  (`elaborate_drops.rs` L99–120), `RemoveUninitDrops`, `AddMovesForPackedDrops`,
  `RemoveNoopLandingPads`.
- Code generation of `Drop` terminators and drop glue (`build_drop_shim`), monomorphization of
  polymorphic drops, optimized builds (`opt-level > 0`, MIR inlining), targets other than
  `x86_64-unknown-linux-gnu`, Windows funclet unwinding (the source comment at
  `elaborate_drop.rs` L865–881 says the enum half-ladder is duplicated for MSVC).
- `catch_unwind`, multiple frames, and the panic runtime's own counters; the model is a single
  frame and treats "leaves the frame unwinding" as an outcome.
- Whether the reversed array order of Finding 10 or the stale flag of Finding 9 are known
  upstream; upstream bug reports were not searched.
- Run-time cost of drop flags; real-crate frequencies of the four styles.

**Unknown.**

- Whether any MIR that MIR building can produce reads a stale flag. No specimen does (no value
  was destroyed twice in any of the 124 runs of MIR-built specimens), and the argument in Finding
  9 is informal. The model shows the condition is *sufficient* and *necessary in general*; it
  does not show MIR building always satisfies it.

**Known not to apply.**

- The refinement theorem does not give trace equality on aborting runs, and cannot:
  `trace_before_abort_depends_on_certificate` and Finding 5.
- `NoLeak` is not a theorem about arbitrary bodies: `ce1_no_flag_never_drop_leak` aside, a
  reference body that never drops a value leaks in both semantics.
- The theorems do not apply to a body whose certificate fails `check`; `staleFlagJoin` is one.
- The model does not police its input the way the borrow checker and MIR building do: an `init`
  of an already initialized leaf (a value overwritten without being dropped) and a `move` of an
  uninitialized leaf are executed identically by both semantics and are reported neither as a
  leak nor as a use after move.
- The Lean model is not connected to Anneal's `Trusted.MirSemantics`; at the examined revision it
  could not be, since `Drop` is `.unsupported` there (Finding 15).

**Unsupported.**

- A cleanup-block `Drop` with `UnwindAction::Continue` cannot be compiled: the MIR validator
  rejects it (Finding 13).
- `#[custom_mir]` and `-Zdump-mir` are unstable and nightly-only.

**Stronger conclusions the evidence does not establish.**

- "`ElaborateDrops` is verified." It is not: the proof is about a model, and the correspondence
  to the Rust implementation is argued on 8 shapes.
- "The pass has a soundness bug." Finding 9 needs hand-written MIR that MIR building does not
  produce.
- "Drop flags cost 43.6% more basic blocks." 376 → 540 is the raw output of the pass on
  specimens chosen to trigger it; after the cleanup passes the same functions have 382 blocks.
- "The certificate checker accepts what `rustc`'s dataflow computes." `check` was run only on
  hand-written certificates for hand-written model bodies.

## Evidence

**Upstream source, `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (commit dated
2026-05-31; resolved through the GitHub API on 2026-11-21 and equal to the `commit-hash` printed
by `rustc -Vv`):

| Path | Lines | Content |
| :-- | :-- | :-- |
| `compiler/rustc_mir_transform/src/lib.rs` | 572–602, 626–650 | pass order around `ElaborateDrops` |
| `compiler/rustc_mir_transform/src/elaborate_drops.rs` | 20–48, 52–88, 99–120, 170–193, 276–287, 289–333, 335–403, 416–422, 424–520 | pass doc, driver, dead unwinds, `drop_style`, order of steps, flag creation, per-terminator driver and `Unwind` mapping, flag writes |
| `compiler/rustc_mir_transform/src/elaborate_drop.rs` | 19–36, 40–45, 49–80, 82–140, 500–523, 564–596, 609–635, 675–716, 1096–1161, 1239, 1251–1312, 1369–1385 | `DropStyle`, `DropFlagMode`, `Unwind`, `DropElaborator`, `elaborate_drop`, `drop_subpath`, half-ladder and ladder bottom, `drop_ladder`, arrays, slice flag reset, `open_drop`, `complete_drop`, `drop_flag_reset_block`, `drop_flag_test_block` |
| `compiler/rustc_mir_dataflow/src/drop_flag_effects.rs` | 10–26, 106–135 | `DropFlagState::{Present, Absent}` and `value()`; effects of a location on flags; `Drop` de-initializes |
| `compiler/rustc_mir_dataflow/src/move_paths/builder.rs` | 401–406 | `StorageDead` gathered as a move |
| `compiler/rustc_mir_transform/src/abort_unwinding_calls.rs` | 26–139 | `AbortUnwindingCalls` |
| `compiler/rustc_mir_transform/src/validate.rs` | 140–166, 247–276, 491–511 | cleanup-edge and unwind-action rules |
| `compiler/rustc_middle/src/mir/syntax.rs` | 742–788, 1030–1055 | `TerminatorKind::Drop` doc, `UnwindAction`, `UnwindTerminateReason` |
| `library/core/src/ops/drop.rs` | 221–231 | panics in `Drop::drop` |
| `library/core/src/panicking.rs` | 335–354 | `panic_cannot_unwind`, `panic_in_cleanup` |
| `src/doc/rustc-dev-guide/src/mir/drop-elaboration.md` | whole file | descriptive account of the pass (still speaks of `DropAndReplace`, which no longer exists as a terminator) |

`compiler/rustc_mir_dataflow/src/elaborate_drops.rs` returns HTTP 404 at this commit.

**Documentation.** `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`,
`src/destructors.md` (rules `destructors.intro`, `destructors.operation`,
`destructors.process-termination`) and `src/panic.md` (`panic.unwind.destruction`).
`rust-lang/rfcs@f43d5789b838fb0d80962e3d4b45fb9ddfcc9a07`,
`text/0320-nonzeroing-dynamic-drop.md`.

**Anneal.** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`:
`trusted/lean/Trusted/MirAst.lean` L682–697, L742–795, L797–813;
`trusted/lean/Trusted/MirSemantics.lean` L602–604, L721–724, L949–976, L1406–1408, L1537–1569;
`trusted/rustc-capture/src/driver.rs` L75–84.

**Execution, this package** (all produced on 2026-11-21 on `x86_64-unknown-linux-gnu`):

| File | Content |
| :-- | :-- |
| `support/specimens/drop_specimens.rs` | 31 dispatched specimens plus one generic helper (sha256 `92e91500e9bcd1170ed12b90d60c8b1b885a50f74427e5ac8ee923d1d2355e05`) |
| `support/specimens/custom_mir_specimens.rs` | 6 hand-written MIR bodies: 3 analysis-dialect, 3 runtime-dialect (sha256 `179688e19e779dec7f28322186d5e9f95bb41f08a89fa7e04859e979d4749187`) |
| `support/specimens/custom_mir_cleanup_continue.rs` | the body the validator rejects (sha256 `c2f79e5b3899239127f95b30dad80e7ab0f4f5db168868474cf2522fe04e0e64`) |
| `support/probe_drop_elaboration.py` | compiles, dumps, parses, runs, checks; standard library only |
| `support/probe_output/probe_results.json` | per-function statistics before and after `ElaborateDrops`, around `AbortUnwindingCalls` and at `runtime-post-cleanup`; classification of every pre-elaboration drop; 136 native runs (62 per panic strategy, 12 hand-written MIR); 39 checks, all passing |
| `support/probe_output/probe_summary.md` | the same as tables |
| `support/probe_output/mir/` | raw dumps: before/after `ElaborateDrops` for every function under `panic=unwind` and for the analysis-dialect hand-written bodies; `runtime-post-cleanup` for the runtime-dialect ones; `nounwind_abi` around `AbortUnwindingCalls` under both strategies |
| `support/DropElaborationRefinement.lean` | the model and proofs (sha256 `d98b59dd88e00ab9cfd4852d1e41c436e4828b277af3c35397aba9b4944e1a1a`) |
| `support/DropElaborationAudit.lean` | walks every constant of the module: rejects axioms, `opaque` constants, non-`safe` definitions, `_unsafe_rec` helpers, and theorems using an axiom other than `propext` and `Quot.sound` |
| `support/check_lean.py` | token scan, kernel check, audit, timing; writes the receipt |
| `support/lean_check_receipt.json` | receipt of the last run: Lean `4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), flags `-DElab.async=false -Ddebug.skipKernelTC=false`, 0 errors, 0 warnings, 0 occurrences of each forbidden token, audit summary, time and memory |
| `support/verify_pins.py`, `support/pin_receipt.json` | resolves every pinned revision of `REPORT.json` through the GitHub API and requires the returned 40-hex SHA to equal the pin; fetches the 17 cited files at those revisions and records their HTTP status (16 present, the moved `rustc_mir_dataflow` path absent) |

The probe's "style" of a pre-elaboration drop is inferred from the shape of the post-elaboration
MIR, not reported by the compiler; the rule is in the script's docstring.

**Literature** (context for the method; none of these papers was re-derived here):

- T. Ramananandro, G. Dos Reis, X. Leroy. "A Mechanized Semantics for C++ Object Construction
  and Destruction, with Applications to Resource Management." POPL 2012, pp. 521–532.
  doi:10.1145/2103656.2103718. A mechanized account of destruction order and of destroying
  partially constructed objects when an exception propagates.
- J.-B. Tristan, X. Leroy. "Formal Verification of Translation Validators: A Case Study on
  Instruction Scheduling Optimizations." POPL 2008. doi:10.1145/1328438.1328444. The pattern used
  here: an untrusted analysis result validated by a checker that is proved sound once.
- R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer. "RustBelt: Securing the Foundations of the Rust
  Programming Language." POPL 2018 (PACMPL 2, Article 66). doi:10.1145/3158154. Its conclusion
  states: "We do not model ... (3) stack unwinding when a panic occurs ... We proved safety of the
  destructors of the verified libraries, but do not handle automatic destruction". Checked against
  the paper's text on 2026-11-21.
- M. Cui, C. Chen, H. Xu, Y. Zhou. "SafeDrop: Detecting Memory Deallocation Bugs of Rust Programs
  via Static Data-flow Analysis." ACM TOSEM 2023. doi:10.1145/3542948. Static MIR data-flow
  analysis targeting double-free and invalid-drop defects around Rust drop glue.
- L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer. "RefinedRust: A Type System for
  High-Assurance Verification of Rust Programs." PLDI 2024. doi:10.1145/3656422. Foundational
  refinement-type verification of Rust programs over a MIR-level operational semantics.
- N. Villani, J. Hostert, D. Dreyer, R. Jung. "Tree Borrows." PLDI 2025 (PACMPL 9, pp. 1019–1042).
  doi:10.1145/3735592. Tree-structured aliasing semantics governing borrowing and protector
  lifetimes across normal and unwinding execution.

## Revalidation

**Cheapest discriminating checks, in order.**

1. *Is the compiler the same?* `rustc -Vv` must print `commit-hash:
   14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`. For another compiler, first diff
   `compiler/rustc_mir_transform/src/elaborate_drop.rs` and `elaborate_drops.rs` against that
   commit; `drop_style`, `elaborate_drop`, `drop_ladder`, `drop_flag_reset_block` and
   `drop_flags_for_locs` decide Findings 2, 3 and 9, and `open_drop_for_array` decides Finding 10.
2. *Rerun the probe* (about 5 seconds; needs a nightly `rustc`, Python 3.10+ and nothing else):

   ```console
   python3 support/probe_drop_elaboration.py --out /tmp/drop_probe
   ```

   It exits non-zero if any of its 39 checks fails. The checks that carry the findings are
   `custom_mir::stale_flag_join_runs_destructor_twice` and `custom_mir::storage_dead_clears_flag`
   (Finding 9), `pre_abort_trace_differs_between_static_and_open` (Finding 5),
   `array::open_ladder_reverses_range_order` (Finding 10),
   `open_drop_ladder_shape::cond_partial_move_tuple` (Finding 3),
   `panic_abort::same_elaboration_as_unwind` and
   `panic_abort::no_cleanup_after_abort_unwinding_calls` (Finding 7),
   `custom_mir::no_flag_always_drop_runs_destructor_twice`, `custom_mir::no_flag_never_drop_leaks`
   and `custom_mir::continue_in_cleanup_rejected` (Finding 13). A changed count in Finding 8 with
   all checks passing means MIR building or a neighbouring pass changed, not necessarily this one:
   compare `/tmp/drop_probe/mir` with `support/probe_output/mir`.
3. *Recheck the Lean model* (about 20 seconds; needs Lean `v4.34.1` on `PATH`):

   ```console
   python3 support/check_lean.py --lean lean --out /tmp/lean_check_receipt.json
   ```

   It scans the source for forbidden tokens, compiles with `-DElab.async=false
   -Ddebug.skipKernelTC=false`, runs the audit, and exits non-zero if a forbidden token occurs, if
   compilation reports an error, or if the audit finds a violation. A passing run establishes that the statements quoted in Finding 12 are proved in that
   file from `propext` and `Quot.sound` alone; it says nothing about `rustc`.
4. *Anneal.* For another revision, look at `inductive TerminatorKind` in
   `trusted/lean/Trusted/MirAst.lean` and at the last arm of `evalTerminator` in
   `trusted/lean/Trusted/MirSemantics.lean`. If `Drop` has become a constructor, Finding 15 is
   obsolete and Findings 5 and 9 become the questions to ask of the new semantics.

**What has to be redone by hand.** The correspondence table of Finding 14: if the ladder shape or
the flag-write sites change in the compiler, the model's `elabDrop`, `elabStmt` and the example
bodies must be re-read against the new dumps; no tool in this package translates MIR into the
model.
