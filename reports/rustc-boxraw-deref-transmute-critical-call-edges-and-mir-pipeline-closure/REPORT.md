# rustc MIR: Box-deref elaboration (`BoxRaw`, `CastKind::BoxDerefTransmute`), critical call-edge splitting, unneeded-drop removal, return duplication, constructor MIR, and the full `rustc_mir_transform` pass order

## Summary

**What was and was not executed.** The source claims below were read at three pinned
`rust-lang/rust` commits. The execution claims come from one toolchain only,
`rustc 1.98.0-nightly (14210df0e 2026-05-31)` with its Miri. That toolchain predates both
`CastKind::BoxDerefTransmute` and `BoxRaw`, so **the `BoxRaw`/`BoxDerefTransmute` lowering was
not executed for this report**; it is established from source, and corroborated only by a
retained MIR dump from an earlier run on `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` whose
inputs were not preserved. Everything else that is labelled *execution* was run.

1. **Box-deref lowering has four source-visible forms.** `ElaborateBoxDerefs` replaces a place
   whose first projection is a `Deref` of a `Box`-typed local by a deref of a fresh raw-pointer
   temporary. The assignment that defines the temporary reads as follows at the commits examined
   (commits between them were not read):

   | At commit (date of the commit object; `fcf68f21`, `2cee4210` and `5d260fd3` are pull-request commits, so that date is not when they reached `main`) | Statement emitted for `*_b` with `_b: Box<T>` |
   |---|---|
   | `f8a08b68` (2026-05-30), `14210df0` (2026-05-31) | `_p = copy ((_b.0: Unique<T>).0: NonNull<T>) as *const T (Transmute)` |
   | `fcf68f21` (2026-08-01) | `_p = copy ((_b.0: Unique<T>).0: NonNull<T>) as *const T (BoxDerefTransmute)` |
   | `2cee4210` (2026-08-01) | `_p = copy (_b.0: Unique<T>) as *const T (BoxDerefTransmute)` |
   | `5d260fd3` (2026-10-10), `3ef0c22c`, `bdf712ee` | `_p = copy (_b.0: BoxRaw<T>) as *const T (BoxDerefTransmute)` |

   `BoxRaw<T>` is a private `#[repr(transparent)]` struct `{ pointer: NonNull<T>, _marker:
   PhantomData<T> }`. It is not itself a pattern type; the pattern type
   (`*const T is !null`) is the single field of `NonNull<T>`. The pass stops projecting at
   field 0 of `Box` because one more projection would reach that pattern type, which cannot be
   projected into in a MIR body.
2. **`BoxDerefTransmute` differs from `Transmute` in exactly one way:** the cast is undefined
   behaviour if its input would not be valid as a `Box<T>`. The interpreter implements this by
   transmuting the input to `Box<T>` and dereferencing it. Code generators treat both kinds
   identically.
3. **`AddCallGuards::CriticalCallEdges` inserts an empty `goto` block on an edge only when the
   target has more than one predecessor edge and the terminator will be emitted as a
   block-terminating instruction**: a `Call` whose unwind action is `Cleanup` or `Terminate`
   (LLVM `invoke`), or an `asm!` with an output operand and either a `label` operand (LLVM
   `callbr`) or such an unwind action. It is scheduled at seven sites, two of them in the main
   pipeline: first in the lowering to runtime MIR, last in the optimization list. The second run
   is necessary because CFG simplification removes the inserted blocks again (executed: 7 → 8 →
   7 → 8 blocks) and because MIR validation rejects critical `Call` edges once the body is in
   `Runtime(Optimized)`.
4. **`RemoveUnneededDrops`** turns `Drop` into `Goto` when the dropped place's type has
   `needs_drop == false` in the body's typing environment, then simplifies the CFG. It runs once,
   after inlining, at every MIR optimization level including the one Miri uses.
5. **`MultipleReturnTerminators`** turns `Goto` into `Return` when the target block has no
   statements and a `Return` terminator. It is enabled only at `-Zmir-opt-level` 4 or higher and
   is scheduled twice.
6. **Tuple-struct and tuple-variant constructors never enter the pass pipeline.** `optimized_mir`
   returns `mir_for_ctfe` for them, which returns a synthesized one-block body
   `_0 = Adt(move _1, …); return`.
7. **The main pipeline in `lib.rs` has 81 pass-list entries at `bdf712ee`**; 18 of them are
   `PassPolicy::Required`. The full table is in Findings. Of the 81 names declared by
   `declare_passes!`, 78 are scheduled in some pass list in the crate; `AllCallEdges` is not
   scheduled anywhere.
8. **A kernel-checked Lean model** proves, for model definitions of the four transformations:
   exact preservation of terminal behaviour by critical-edge splitting; that after splitting every
   output-bearing edge is the only edge into its target; that under this property storing a call
   result at the entry of the destination block is equivalent to MIR semantics; bidirectional
   soundness of the drop-removal, return-duplication and Box-deref elaborations; and
   counterexamples for each unsound variant. These are theorems about the model, not about
   `rustc`.

## Applicability

**Subjects and how they relate.**

| Short name used below | Subject | Role |
|---|---|---|
| `bdf712ee` | `rust-lang/rust@bdf712ee87c22a2b5c60db2e1af8a63e3cfd1a2e`, the tip of `main` when this report was written (committer date 2026-11-21) | Source audit. **All line numbers are at this commit unless another commit is named.** Not executed. |
| `3ef0c22c` | `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, the commit of `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` | Source cross-check; origin of the retained record. Not executed for this report. |
| `14210df0` | `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, the commit of `rustc 1.98.0-nightly (14210df0e 2026-05-31)` | Source, and the only toolchain executed (`rustc` and Miri, host `x86_64-unknown-linux-gnu`, LLVM 22.1.6). |
| `f8a08b68` | `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` | The compiler version hard-coded in Anneal's capture driver. One file compared. |
| Anneal | `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` | Its trusted MIR syntax and capture driver are read to state what these passes mean for it. |
| Lean | `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (tag `v4.34.1`) | Checks the model. |

The report is a comparison across the three `rustc` commits plus a model. It is not a claim about
any release channel other than these nightlies.

**Shared across all three `rustc` commits** (source at each; the algorithm bodies are textually
identical apart from the constructor `TerminatorKind::goto(target)` replacing
`TerminatorKind::Goto { target }`): the algorithms of `AddCallGuards`, `RemoveUnneededDrops`,
`MultipleReturnTerminators`, `Derefer` and `EraseDerefTemps`; the seven scheduling sites of
`CriticalCallEdges`; the constructor bypass in `optimized_mir`; Miri's default MIR flags.

**Different between commits:**

| Aspect | `14210df0` | `3ef0c22c` | `bdf712ee` |
|---|---|---|---|
| Box-deref cast | `Transmute` of `NonNull<T>` | `BoxDerefTransmute` of `BoxRaw<T>` | same as `3ef0c22c` (file byte-identical) |
| Pass gating API | `is_enabled(sess)` / `is_required()` | `policy(ctx) -> PassPolicy` | same as `3ef0c22c` |
| `RemoveUnneededDrops` gating | `is_required() = true` | `PassPolicy::optional(true)` | same |
| Interpreter place deref of a `Box` | compiler bug (`bug!`), no validity check on any place deref | null/alignment/dereferenceability checked for references and boxes | same as `3ef0c22c` |
| `PostAnalysisNormalize` | in the lowering list, after `CriticalCallEdges` | same position | run on its own, before the lowering list |
| Constructor body phase | left as built, one dump named `built` | forced to `Runtime(Optimized)` with an empty pass list | same as `3ef0c22c` |
| `lib.rs` list entries | 76 | 81 | 81 |

**Configuration of the executed observations.** Edition 2024, `-C panic=unwind`, host
`x86_64-unknown-linux-gnu`. MIR dumps: `-Zdump-mir=all`. Four flag sets: `-C opt-level=3
-Zmir-opt-level=2`; `-C opt-level=3 -Zmir-opt-level=4`; no optimization flags; and the
MIR-affecting flags Miri passes by default (`-Zmir-opt-level=0 -Zmir-preserve-ub
-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums`). Miri itself was run with its
defaults (Stacked Borrows) and, for one program, also with `-Zmiri-tree-borrows` and
`-Zmiri-disable-stacked-borrows`. The inline-asm observation is x86-64 only.

**Extension beyond what was observed.** Execution results about `AddCallGuards`,
`RemoveUnneededDrops` and `MultipleReturnTerminators` on `14210df0` are expected to carry over to
`3ef0c22c` and `bdf712ee` because the pass bodies are textually unchanged and their positions in
the pass lists are unchanged relative to the passes around them; this is an argument from source,
not an observation. No such argument is available for the Box-deref MIR text or for Miri's
treatment of an invalid `Box`, both of which changed.

**The "retained record".** One support file holds MIR dumps and counters produced earlier on
`3ef0c22c` by a similar probe. The Rust source and command lines that produced it were not kept
with it and it was not re-run. It is used for exactly one thing: its
`ElaborateBoxDerefs` dump shows the statement form that the source at the same commit predicts.

## Findings

### 1. `ElaborateBoxDerefs`, `BoxRaw`, and `CastKind::BoxDerefTransmute`

Basis: source (`bdf712ee`, `3ef0c22c`, `14210df0`, plus the two intermediate commits for the
history) + execution (`14210df0` only) + retained record (`3ef0c22c`).

**Types.** At `bdf712ee` and `3ef0c22c`, `library/alloc/src/boxed.rs:233-241` and `:308-311`:

```rust
/// An internal wrapper for the pointer + `PhantomData` inside a `Box`.
/// This type has no semantic meaning. It only exists because the layout of
/// `Box` is hard-coded into the compiler, and because moving the
/// auto trait impls to `Box` would cause regressions (#162850).
#[repr(transparent)]
struct BoxRaw<T: ?Sized> {
    pointer: NonNull<T>,
    _marker: PhantomData<T>,
}
pub struct Box<T: ?Sized, A: Allocator = Global>(BoxRaw<T>, A);   // attributes elided
```

and `library/core/src/ptr/non_null.rs:78-80`:
`pub struct NonNull<T: PointeeSized> { pointer: crate::pat::pattern_type!(*const T is !null) }`
(the macro path is `crate::pattern_type!` at `3ef0c22c`). At `14210df0`, field 0 of `Box` is
`Unique<T>` (`boxed.rs:237`).

**The pass** (`compiler/rustc_mir_transform/src/elaborate_box_derefs.rs`, 157 lines, byte-identical
at `bdf712ee` and `3ef0c22c`). For every place whose *first* projection is `Deref` and whose base
local has a `Box` type (`:51-52`), it allocates a new temporary of type `*const T` (`:58`),
inserts before the current location (`:60-68`)

```rust
// Project to the first field (a `BoxRaw`), then transmute that. We could project one
// further but in the end we'd hit a pattern type so we'd always have to transmute.
let field_place =
    Place::from(place.local).project_to_field(FieldIdx::ZERO, &*self.local_decls, tcx);
self.patch.add_assign(
    location,
    Place::from(ptr_local),
    Rvalue::Cast(CastKind::BoxDerefTransmute, Operand::Copy(field_place), ptr_ty),
);
```

and replaces the place's base local by the temporary (`:70`). Each elaborated deref gets its own
temporary. Variable debug info is rewritten separately (`:112-150`) with a longer projection that
does go through the pattern type, which the source comment says is permitted there. Policy:
`PassPolicy::Required`, "Implements Box dereference semantics so backends and Miri do not have to
handle them" (`:153-156`).

At `14210df0` the same file (167 lines) emits `Rvalue::Cast(CastKind::Transmute, …)` on the place
`(_b.0: Unique<T>).0: NonNull<T>` (`:70-81`).

**Why only first-projection derefs.** `Derefer` (`deref_separator.rs:23-81`, `Required`; its policy
comment says later MIR passes expect a `Deref` only as the first place projection) splits every
place that has a `Deref` after its first projection, introducing temporaries defined by `Rvalue::CopyForDeref`.
`EraseDerefTemps` (`erase_deref_temps.rs:19-25`, `Required`) later turns each `CopyForDeref` into
`Rvalue::Use(Operand::Copy(place), WithRetag::No)`, with the comment "We do *NOT* want a retag
here! This assignment might copy a mutable reference we can't actually copy". Order in `lib.rs`:
`Derefer` `:648`, `EraseDerefTemps` `:675`, `ElaborateBoxDerefs` `:676`.

**Position relative to MIR phases.** `ElaborateBoxDerefs` is in the list whose completion sets the
body's phase to `MirPhase::Runtime(RuntimePhase::Initial)` (`lib.rs:659-681`). The phase
documentation (`compiler/rustc_middle/src/mir/syntax.rs:140-142`) states the corresponding
restriction one step later: beginning with `RuntimePhase::PostCleanup`, "the following variant is
disallowed: `ProjectionElem::Deref` of `Box`".

**Semantics of the cast kind** (`syntax.rs:1521-1528`, identical at `bdf712ee` and `3ef0c22c`):

> A special transmute used by elaborated `box` deref's to turn the inner pointer into a raw
> pointer. This is almost equivalent to a regular transmute except that if the input would not be
> valid as `Box<T>`, the cast is UB. Backends that do not care about UB detection can treat this
> like a regular transmute.
>
> Well-formedness: The input type must be a pointer type or a newtype around one (e.g. `NonNull`).
> The output type must be a raw pointer.

Implementation sites at `bdf712ee`:

- Interpreter, `compiler/rustc_const_eval/src/interpret/cast.rs:192-218`: handled in the same arm
  as `Transmute` and `Subtype`, plus (`:206-214`) "Do the extra UB checking by making the input an
  actual `Box<T>` pointer and dereferencing it": the immediate is transmuted to `Box<pointee>` and
  passed to `deref_pointer`. `deref_pointer` (`interpret/place.rs:464-502`) checks "metadata
  validity, null, alignment, and dereferenceability" for references and boxes only
  (`if ptr_ty.is_ref() || ptr_ty.is_box()`, `:490`), not for raw pointers.
- MIR validator, `rustc_mir_transform/src/validate.rs:1404-1445`: both operand and target type
  must be `Sized`; for `BoxDerefTransmute` additionally the target must be a raw pointer
  ("Cannot BoxDerefTransmute to non-pointer type", `:1440`).
- Code generation: `rustc_codegen_ssa/src/mir/rvalue.rs` and `rustc_codegen_cranelift/src/base.rs`
  match `Transmute | BoxDerefTransmute | Subtype` in one arm (seen at `3ef0c22c`,
  `rvalue.rs:618`, `base.rs:830`).
- Borrow checking never sees it: `rustc_borrowck/src/type_check/mod.rs:1605` (at `3ef0c22c`) is
  `CastKind::Subtype | CastKind::BoxDerefTransmute => bug!(…)`.

**History** (source; each commit's version of the pass file was read, and the MIR test
expectations changed by `2cee4210` show the second and third forms verbatim).
`fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f` ("introduce a new CastKind for ElaborateBoxDerefs")
switched the cast kind while still projecting to `NonNull<T>`;
`2cee42105a5cc121030724e6ac806e3dd509c6e6` ("ElaborateBoxDeref: remove unnecessary projection")
stopped at field 0; `5d260fd3da7b0165d6365adab12746bfc389d913` ("Replace `Unique` in
`Box` with a `(NonNull, PhantomData)` wrapper") introduced `BoxRaw`. All three are ancestors of
`3ef0c22c` (they appear in the file's history queried at that commit). Their commit objects are
dated 2026-08-01, 2026-08-01 and 2026-10-10; these are pull-request commits, so the dates on
which they reached `main`, and the first nightly containing each, were not determined.

**Execution on `14210df0`** (function `pub fn read_box_u64(b: &Box<u64>) -> u64 { **b }`):

```text
// before ElaborateBoxDerefs            // after ElaborateBoxDerefs
_2 = no_retag copy (*_1);               _2 = no_retag copy (*_1);
_0 = copy (*_2);                        _3 = copy ((_2.0: std::ptr::Unique<u64>).0: std::ptr::NonNull<u64>) as *const u64 (Transmute);
return;                                 _0 = copy (*_3);
                                        return;
```

**Retained record on `3ef0c22c`**, same function name and same "before" body; the "after" body has
`_3 = copy (_2.0: std::boxed::BoxRaw<u64>) as *const u64 (BoxDerefTransmute);`. This matches what
the source at `3ef0c22c` emits. It was not re-executed.

**An invalid `Box` used only as a place.** Program: allocate a `Box<u8>`, free its allocation
through a raw pointer, then evaluate `&raw const *b` (no load), then exit without dropping `b`.

- Execution, Miri at `14210df0`: no undefined behaviour reported, exit status 0, under Stacked
  Borrows, Tree Borrows and with the aliasing model disabled. The control program that *loads*
  through the dangling box (`let v = *b;`) is rejected: "Undefined Behavior: memory access failed:
  alloc… has been freed, so this pointer is dangling".
- Source, `14210df0`: consistent with that. `deref_pointer` there (`interpret/place.rs:466-482`)
  performs no validity check for any pointer type, and treats a `Box` operand as a compiler bug
  ("Derefer should have removed all Box derefs").
- Derived, for `3ef0c22c` and `bdf712ee`, **not executed**: the same program should be reported as
  undefined behaviour at the `BoxDerefTransmute` cast, because the cast dereferences its input as
  a `Box` and `deref_pointer` now checks dereferenceability for boxes. This is a prediction from
  `cast.rs:206-214` and `place.rs:482-502`. The probe records what Miri does with this program
  and deliberately does not assert an expected outcome.

### 2. `AddCallGuards::CriticalCallEdges`

Basis: source (algorithm identical at all three commits) + execution (`14210df0`).

**Algorithm** (`rustc_mir_transform/src/add_call_guards.rs`, 140 lines):

1. `pred_count[bb]` is the number of occurrences of `bb` among `terminator().successors()` of all
   blocks, with multiplicity, in a `u8` with saturating addition (`:34-39`). Only `> 1` is tested,
   so saturation cannot change a decision.
2. Work list (`:46-79`):
   - `TerminatorKind::Call { target: Some(destination), unwind, .. }` is queued
     `if pred_count[destination] > 1 && (generates_invoke(unwind) || self == &AllCallEdges)`.
   - `TerminatorKind::InlineAsm { asm_macro: InlineAsmMacro::Asm, targets, operands, unwind, .. }`
     is considered only for `CriticalCallEdges`. With `has_outputs` = some operand is `InOut` or
     `Out`, and `has_labels` = some operand is `Label`: `if has_outputs && (has_labels ||
     generates_invoke(unwind))`, then *each* target with `pred_count[*target] > 1` is queued
     separately.
3. For each queued edge a new block is appended whose only content is `goto` to the old target,
   with the source block's `is_cleanup` flag and the terminator's `source_info`; the edge is
   redirected to it (`:85-124`). All counts are taken before any edge is redirected.
4. `generates_invoke(unwind)` is `true` for `UnwindAction::Cleanup(_)` and `Terminate(_)`, `false`
   for `Continue` and `Unreachable` (`:134-140`).

Policy: `PassPolicy::Required`, "Breaks critical edges so codegen can place edge-specific actions
without affecting other control-flow edges" (`:127-131`).

Two consequences of the text that are easy to miss: a `Call` with `UnwindAction::Terminate` has a
single MIR successor, so the edge is not critical in the graph-theoretic sense, yet it is split
when its target has other predecessors; and an `asm!` without output operands is never split.

**Why the code generator needs it.** `rustc_codegen_ssa/src/mir/block.rs`, `do_call`: when an
unwind block exists the call is emitted with `bx.invoke(…)` (`:277`) and the store of the return
value is emitted *into the target block*: `bx.switch_to_block(fx.llbb(target))` (`:294`), then
`fx.store_return(bx, ret_dest, &fn_abi.ret, invokeret)` (`:299`). Without an unwind block it is a
plain `bx.call`, the store follows in the same block, and only then is the branch emitted. For
inline asm with labels, `rustc_codegen_llvm/src/asm.rs:380-407` says "Write results to outputs. We
need to do this for all possible control flow" and stores every output in the fallthrough block
and in each label block; the instruction itself is `bx.callbr(…)` (`:615`). MIR's own account of
the outputs is `syntax.rs:951-952`: "`out` and `inout` operands are only considered written-to
when execution continues with `targets`". A store placed in a block that has another predecessor
also executes on that predecessor's path. The module documentation says the same (`:6-12`).

**Scheduling: seven sites.** Main pipeline: `lib.rs:662` (first entry of
`run_runtime_lowering_passes`) and `lib.rs:782` (in `run_optimization_passes`, after the last
`MultipleReturnTerminators`, before the two `prettify` passes). Shim bodies: `shim.rs:117`, `:141`,
`:161`, `:198` and `shim/async_destructor_ctor.rs:37`. (At `3ef0c22c` the `lib.rs` lines are 658
and 780; at `14210df0`, 629 and 765.) `AllCallEdges` is declared and compared against at `:52` but
is not scheduled anywhere in the crate.

**Why twice in the main pipeline.** (a) The module documentation warns "NOTE: Simplify CFG will
happily undo most of the work this pass does" (`:16`); `SimplifyCfg` collapses chains of empty
`goto` blocks (`simplify.rs:240-241`, `collapse_goto_chain`). (b) The MIR validator fails on a
critical `Call` edge once `body.phase >= MirPhase::Runtime(RuntimePhase::Optimized)`
(`validate.rs:386-401`; predicate `is_critical_call_edge` at `:277-281`: unwind is `Cleanup` or
`Terminate` and the target has more than one predecessor), with the comment "The code generation
assumes that there are no critical call edges". The pass manager validates unconditionally on the
change to `Runtime(Optimized)` (`pass_manager.rs:409`). The validator's predicate covers `Call`
only; it has no corresponding check for `InlineAsm`.

**Execution on `14210df0`.** Source:

```rust
pub fn crit_call(c: bool) -> u32 { let _g = Guard(1); let y = if c { opaque(1) } else { 7 }; y }
```

where `Guard` has a `Drop` impl (so the call gets a cleanup edge) and `opaque` is
`#[inline(never)]`. Before the first `AddCallGuards`:

```text
bb0: _2 = Guard(const 1_u32); _4 = copy _1; switchInt(move _4) -> [0: bb2, otherwise: bb1];
bb1: _3 = opaque(const 1_u32) -> [return: bb3, unwind: bb5];
bb2: _3 = const 7_u32; goto -> bb3;
bb3: _0 = copy _3; drop(_2) -> [return: bb4, unwind continue];
```

The pass changes `bb1` to `-> [return: bb7, unwind: bb5]` and appends `bb7: goto -> bb3`.

| Function | 1st `AddCallGuards` | `SimplifyCfg-pre-optimizations` | last `AddCallGuards` |
|---|---|---|---|
| `crit_call` (unwinding call into a join block) | 7 → 8 blocks | 8 → 7 | 7 → 8 |
| same without `Guard` (`unwind continue`) | 4 → 4 | 4 → 4 | 4 → 4 |
| `asm!` with `out(reg)` and `label {}` | 3 → 4 | 4 → 3 | 2 → 4 |

In the asm case the terminator before the last run is `-> [return: bb1, label: bb1, unwind
unreachable]`: both targets are the same block, each is split, and two blocks are added. Its
unwind action is `Unreachable`, so the split is due to `has_outputs && has_labels` alone.

### 3. `RemoveUnneededDrops`

Basis: source + execution (`14210df0`).

`remove_unneeded_drops.rs:23-40`: for every block whose terminator is `Drop { place, target, .. }`,
compute the place's type; if `ty.needs_drop(tcx, typing_env)` is false, replace the terminator by
`goto(target)`; if anything changed, call `simplify_cfg`. The unwind edge of the removed `Drop`
disappears with it. The module comment gives the reason the pass exists: MIR building already
checks `needs_drop` before emitting a `Drop`, but this pass "runs after type checking, so it can
make use of `TypingMode::PostAnalysis` to provide more precise type information, especially about
opaque types". The contract it relies on is the documentation of `Ty::needs_drop`
(`rustc_middle/src/ty/util.rs:1346`, comment immediately above): "if it returns `false`, then
`ty` definitely has no destructor (i.e., no drop glue)".

Scheduled once, `lib.rs:733`, after `Inline`, `RemoveStorageMarkers` and `RemoveZsts`, under the
comment "Inlining and instantiation may introduce ZST and useless drops". Policy
`PassPolicy::optional(true)`: on at every MIR optimization level unless disabled by
`-Zmir-enable-passes`. At `14210df0` the same pass declares `is_required() = true`.

Execution: `#[inline(always)] pub fn drop_val<T>(x: T) {}` keeps `drop(_1)` in its own generic
body. In `drop_caller_u32(x: u32)`, after inlining, `drop(_3) -> [return: bb1, unwind continue]`
with `_3: u32` is present before the pass and absent after it, and the body goes from 2 blocks to
1. In `drop_caller_string(x: String)` the pass leaves the body unchanged (one `Drop` before and
after). Under Miri's default MIR flags the pass still produces a dump, i.e. it runs.

### 4. `MultipleReturnTerminators`

Basis: source + execution (`14210df0`).

`multiple_return_terminators.rs:17-36`: collect the blocks with `statements.is_empty()` and a
`Return` terminator; then for every block whose terminator is `Goto { target, .. }` with `target`
in that set, replace the terminator by `Return`; finally `remove_dead_blocks`. The set is computed
on the input body before any rewrite. Only `Goto` is rewritten: a `SwitchInt` arm that targets a
return block is untouched. Policy `PassPolicy::optional(ctx.mir_opt_level() >= 4)` (`:13-15`).
Scheduled at `lib.rs:739` and `lib.rs:780`.

Execution, `pub fn multi_return_branch(x: u32) -> u32 { match x { 0 => 10, 1 => 20, _ => 30 } }`:
at `-Zmir-opt-level=2` the optimized MIR has three arms ending in `goto -> bb4` and one `return;`,
and the pass produces no dump; at `-Zmir-opt-level=4` each arm ends in its own `return;` (three in
total) and the pass produces dumps for both scheduled positions.

### 5. Constructor MIR

Basis: source + execution (`14210df0`).

`lib.rs:792-802`:

```rust
fn optimized_mir(tcx: TyCtxt<'_>, did: LocalDefId) -> &Body<'_> {
    if tcx.is_constructor(did.to_def_id()) {
        // There's no reason to run all of the MIR passes on constructors when
        // we can just output the MIR we want directly. This also saves const
        // qualification and borrow checking the trouble of special casing
        // constructors.
        return tcx.mir_for_ctfe(did);
    }
    tcx.arena.alloc(inner_optimized_mir(tcx, did))
}
```

- `is_constructor` is `matches!(self.def_kind(def_id), DefKind::Ctor(..))` (`ty/util.rs:651`).
- Only function-like constructors have MIR at all: `mir_keys` adds a constructor's `DefId` only
  when `variant.ctor` is `Some((CtorKind::Fn, _))`, for structs and enum variants (`lib.rs:349-359`).
- `inner_mir_for_ctfe` returns `shim::build_adt_ctor` for them (`lib.rs:507-513`).
  `build_adt_ctor` (`shim.rs:1011`) builds one block with the single statement
  `_0 = Aggregate(Adt(def, variant, args), [move _1, …, move _n])` and a `Return`, sets an empty
  mentioned-items list, and then "We don't pass any passes here, we just force a phase change to
  `Optimized`" (`shim.rs:1081`) by calling the pass manager with an empty list. The pass manager
  still validates the body on that phase change.
- `mir_promoted` asserts it is never asked for a constructor (`lib.rs:441`) and `promoted_mir`
  returns an empty vector for one.

Execution: for `struct Pair(u32, u32)`, `enum E { V(u8), W }` and `struct Guard(u32)`, each
constructor produced exactly one MIR dump (named `built` on this toolchain, where the body's phase
is not changed), against 110 dump files for an ordinary function in the same crate; the emitted
MIR lists the body `_0 = Pair(move _1, move _2); return;` twice, once as optimized MIR and once
as MIR for CTFE. Under Miri, using `Pair`, `E::V` and `Some` as `fn` pointers and as arguments
to `Iterator::map` runs without error.

### 6. Pass manager semantics and the pass order of the main pipeline

Basis: source (`bdf712ee`; differences at the other two commits are stated) + execution of the
order on `14210df0`.

**`PassPolicy`** (`pass_manager.rs:86-100`):

- `Required`: "This pass implements a mandatory lowering step, either to implement parts of the
  MIR semantics or to bring MIR into a shape that is easier to deal with for later passes/codegen.
  Passes using this cannot be disabled via any means. **They must not remove any UB, as they will
  run in Miri.** They must also come with a comment justifying why they must always run."
- `Optional { enabled_by_default }`: "An optional pass that may be configured by
  `-Zmir-enable-passes`."

`should_run_pass` (`:256`): a `Required` pass always runs; an `Optional` pass runs if the last
matching `-Zmir-enable-passes` entry says so, otherwise if `enabled_by_default`.
`WithMinOptLevel(n, pass)` (written `o1(pass)` in `lib.rs` for `n = 1`) additionally requires the
MIR optimization level to be at least `n` and is a compiler bug around a `Required` pass. The
`Lint` adapter wraps passes that cannot mutate the body, disables their MIR dump, and has policy
`optional(true)`. The MIR optimization level of a body is `-Zmir-opt-level` if given, else 1 at
`-C opt-level=0` and 2 otherwise (`rustc_session/src/config.rs:121-128`), adjustable per function
by `#[optimize]`.

**Miri** prepends `-Zmir-preserve-ub`, `-Zmir-opt-level=0`,
`-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums` and
`-Zmir-enable-passes=-ReferencePropagation,-GVN` (`src/tools/miri/src/lib.rs:200-214`).

**How to read the table.** One row per entry of a pass list in `lib.rs`, in file order. "phase set
afterwards" is the `MirPhase` argument of the pass-manager call: the body is in the *previous*
phase while the list runs. *Class* is the undefined-behaviour status the source assigns: **R** =
`Required`, bound by the "must not remove any UB" rule quoted above; **O** = optional, to which
that rule does not apply; **L** = lint, which cannot change the body. *Miri default* is **derived**:
the policy expression evaluated under Miri's default flags with every other option at its default
and an unwinding panic strategy. Rows 13-18 belong to side paths: 13-15 run only when computing
MIR for compile-time evaluation, 16-18 only when `const_precise_live_drops` checking is enabled.

**`mir_built`** (`lib.rs:418`), `pm::run_passes`, phase set afterwards: none

| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |
|---|---|---|---|---|---|---|
| 1 | 418 | `LintAndRemoveUninhabited` | Required | always | on | R |
| 2 | 420 | `Lint(CheckForceInline)` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | L |
| 3 | 421 | `Lint(CheckCallRecursion)` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | L |
| 4 | 422 | `Lint(CheckPackedRef)` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | L |
| 5 | 423 | `Lint(CheckConstItemMutation)` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | L |
| 6 | 424 | `Lint(CheckMutRestriction)` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | L |
| 7 | 425 | `Lint(FunctionItemReferences)` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | L |
| 8 | 427 | `SimplifyCfg::Initial` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | O |
| 9 | 428 | `Lint(SanityCheck)` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | L |

**`mir_promoted`** (`lib.rs:484`), `pm::run_passes`, phase set afterwards: `Analysis(Initial)`

| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |
|---|---|---|---|---|---|---|
| 10 | 484 | `PromoteTemps` | Required | always | on | R |
| 11 | 484 | `SimplifyCfg::PromoteConsts` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | O |
| 12 | 484 | `InstrumentCoverage` | Optional | `-Cinstrument-coverage` | off | O |

**`inner_mir_for_ctfe`** (`lib.rs:534`), `pm::run_passes`, phase set afterwards: none

| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |
|---|---|---|---|---|---|---|
| 13 | 534 | `CtfeLimit` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | O |
| 14 | 534 | `MentionedItems` | Required | always | on | R |

**`inner_mir_for_ctfe`** (`lib.rs:536`), `pm::run_passes`, phase set afterwards: none

| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |
|---|---|---|---|---|---|---|
| 15 | 536 | `CtfeLimit` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | O |

**`run_analysis_to_runtime_passes`** (`lib.rs:622`), `pm::run_passes`, phase set afterwards: none

| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |
|---|---|---|---|---|---|---|
| 16 | 622 | `RemoveUninitDrops` | Required | always | on | R |
| 17 | 623 | `SimplifyCfg::RemoveFalseEdges` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | O |
| 18 | 624 | `Lint(CheckLiveDrops)` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | L |

**`run_analysis_cleanup_passes`** (`lib.rs:644`), `pm::run_passes`, phase set afterwards: `Analysis(PostCleanup)`

| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |
|---|---|---|---|---|---|---|
| 19 | 644 | `ImpossibleClauses` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | O |
| 20 | 645 | `CleanupPostBorrowck` | Required | always | on | R |
| 21 | 646 | `RemoveNoopLandingPads` | Optional | panic strategy unwinds | on | O |
| 22 | 647 | `SimplifyCfg::PostAnalysis` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | O |
| 23 | 648 | `Derefer` | Required | always | on | R |

**`run_analysis_cleanup_passes`** (`lib.rs:655`), `pm::run_passes`, phase set afterwards: none

| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |
|---|---|---|---|---|---|---|
| 24 | 655 | `PostAnalysisNormalize` | Required | always | on | R |

**`run_runtime_lowering_passes`** (`lib.rs:662`), `pm::run_passes_no_validate`, phase set afterwards: `Runtime(Initial)`

| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |
|---|---|---|---|---|---|---|
| 25 | 662 | `AddCallGuards::CriticalCallEdges` | Required | always | on | R |
| 26 | 664 | `Subtyper` | Required | always | on | R |
| 27 | 665 | `ElaborateDrops` | Required | always | on | R |
| 28 | 667 | `Lint(CheckDropRecursion)` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | L |
| 29 | 671 | `AbortUnwindingCalls` | Required | always | on | R |
| 30 | 674 | `AddMovesForPackedDrops` | Required | always | on | R |
| 31 | 675 | `EraseDerefTemps` | Required | always | on | R |
| 32 | 676 | `ElaborateBoxDerefs` | Required | always | on | R |
| 33 | 677 | `StateTransform` | Required | always | on | R |
| 34 | 678 | `Lint(KnownPanicsLint)` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | L |

**`run_runtime_cleanup_passes`** (`lib.rs:686`), `pm::run_passes`, phase set afterwards: `Runtime(PostCleanup)`

| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |
|---|---|---|---|---|---|---|
| 35 | 686 | `LowerIntrinsics` | Required | always | on | R |
| 36 | 687 | `RemovePlaceMention` | Optional | not `-Zmir-preserve-ub` | off | O |
| 37 | 688 | `SimplifyCfg::PreOptimizations` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | O |

**`run_optimization_passes`** (`lib.rs:711`), `pm::run_passes`, phase set afterwards: `Runtime(Optimized)`

| # | `lib.rs` line | Pass | Policy | Enabled by default when | Miri default | Class |
|---|---|---|---|---|---|---|
| 38 | 711 | `CheckAlignment` | Optional | `ub_checks()` | off | O |
| 39 | 712 | `CheckNull` | Optional | `ub_checks()` | off | O |
| 40 | 713 | `CheckEnums` | Optional | `ub_checks()` | off | O |
| 41 | 718 | `LowerSliceLenCalls` | Optional | level >= 1 | off | O |
| 42 | 721 | `InstSimplify::BeforeInline` | Optional | level >= 1 | off | O |
| 43 | 723 | `ForceInline` | Required | always | on | R |
| 44 | 725 | `Inline` | Optional | level 2 with `-C opt-level` 2/3 and no incremental; level >= 3; or `-Zinline-mir` | off | O |
| 45 | 730 | `RemoveStorageMarkers` | Optional | level >= 1; no lifetime markers | off | O |
| 46 | 732 | `RemoveZsts` | Optional | level >= 1 | off | O |
| 47 | 733 | `RemoveUnneededDrops` | Optional | always (unless `-Zmir-enable-passes=-…`) | on | O |
| 48 | 736 | `UnreachableEnumBranching` | Optional | level >= 1 | off | O |
| 49 | 737 | `UnreachablePropagation` | Optional | level >= 2 | off | O |
| 50 | 738 | `o1(SimplifyCfg::AfterUnreachableEnumBranching)` | Optional | level >= 1 | off | O |
| 51 | 739 | `MultipleReturnTerminators` | Optional | level >= 4 | off | O |
| 52 | 743 | `InstSimplify::AfterSimplifyCfg` | Optional | level >= 1 | off | O |
| 53 | 752 | `o1(SimplifyConstCondition::AfterInstSimplify)` | Optional | level >= 1 | off | O |
| 54 | 753 | `ReferencePropagation` | Optional | level >= 2 | off | O |
| 55 | 754 | `ScalarReplacementOfAggregates` | Optional | level >= 2 | off | O |
| 56 | 755 | `SimplifyLocals::BeforeConstProp` | Optional | level >= 1 | off | O |
| 57 | 756 | `DeadStoreElimination::Initial` | Optional | level >= 2 | off | O |
| 58 | 757 | `GVN` | Optional | level >= 2 | off | O |
| 59 | 758 | `SimplifyLocals::AfterGVN` | Optional | level >= 1 | off | O |
| 60 | 761 | `SsaRangePropagation` | Optional | level >= 2 | off | O |
| 61 | 762 | `MatchBranchSimplification` | Optional | level >= 2 | off | O |
| 62 | 763 | `DataflowConstProp` | Optional | level >= 3 | off | O |
| 63 | 764 | `SingleUseConsts` | Optional | level >= 1 | off | O |
| 64 | 765 | `o1(SimplifyConstCondition::AfterConstProp)` | Optional | level >= 1 | off | O |
| 65 | 766 | `JumpThreading` | Optional | level >= 2; target is not GPU-like | off | O |
| 66 | 767 | `EarlyOtherwiseBranch` | Optional | level >= 2 | off | O |
| 67 | 768 | `SimplifyComparisonIntegral` | Optional | level >= 2 | off | O |
| 68 | 769 | `o1(SimplifyConstCondition::Final)` | Optional | level >= 1 | off | O |
| 69 | 770 | `o1(RemoveNoopLandingPads)` | Optional | level >= 1; panic strategy unwinds | off | O |
| 70 | 771 | `o1(SimplifyCfg::Final)` | Optional | level >= 1 | off | O |
| 71 | 773 | `StripDebugInfo` | Optional | `-Zmir-strip-debuginfo` set | off | O |
| 72 | 774 | `CopyProp` | Optional | level >= 1 | off | O |
| 73 | 775 | `DeadStoreElimination::Final` | Optional | level >= 2 | off | O |
| 74 | 776 | `DestinationPropagation` | Optional | level >= 2; not `-Zmir-move-elimination` | off | O |
| 75 | 777 | `TailCopyToMove` | Optional | level >= 2; `-Zmir-move-elimination` | off | O |
| 76 | 778 | `MoveElimination` | Optional | level >= 2; `-Zmir-move-elimination` | off | O |
| 77 | 779 | `SimplifyLocals::Final` | Optional | level >= 1 | off | O |
| 78 | 780 | `MultipleReturnTerminators` | Optional | level >= 4 | off | O |
| 79 | 782 | `AddCallGuards::CriticalCallEdges` | Required | always | on | R |
| 80 | 784 | `ReorderBasicBlocks` | Optional | off unless `-Zmir-enable-passes=+…` | off | O |
| 81 | 785 | `ReorderLocals` | Optional | off unless `-Zmir-enable-passes=+…` | off | O |

Counts: 81 entries; 18 are `Required` (17 distinct passes, `CriticalCallEdges` twice); 10 are
lints; 53 are other optional entries.

**Differences at the other commits.** At `3ef0c22c` the list contents are the same 81 entries, but
`PostAnalysisNormalize` is the second entry of `run_runtime_lowering_passes` (`lib.rs:660`),
i.e. it runs *after* the first `CriticalCallEdges` (which is at `lib.rs:658` there), and the
entries after it are 2 lines lower than in the table. At
`14210df0` there are 76 entries: no `LintAndRemoveUninhabited`, no `CheckMutRestriction`, no
`TailCopyToMove`/`MoveElimination`, a single CTFE list, `ImpossibleClauses` is named
`ImpossiblePredicates`, and the optimization list additionally contains `EnumSizeOpt`.

**Passes outside the main pipeline** (`bdf712ee`): seven more lists with 24 entries, all for shims
and coroutine helper bodies (`shim.rs:115`, `:139`, `:159`, `:190`,
`shim/async_destructor_ctor.rs:35`, `coroutine/mod.rs:974`, `coroutine/drop.rs:336`). They use
only `MentionedItems`, `AbortUnwindingCalls`, `CriticalCallEdges`, `SimplifyCfg::MakeShim`,
`StateTransform`, `AddMovesForPackedDrops`, `RemoveNoopLandingPads`, `InstSimplify::BeforeInline`
and `ForceInline`. `MentionedItems` is additionally run directly at `lib.rs:824`.

**Census of `declare_passes!`** (`lib.rs:123-214`): 67 pass types, 81 names when each enum variant
is counted. 77 names occur in `lib.rs` lists; `SimplifyCfg::MakeShim` occurs only in shim lists;
three names occur in no list: `AddCallGuards::AllCallEdges` (no use at all),
`RequiredConstsVisitor` (called directly, `lib.rs:477`) and `Validator` (run by `validate_body`,
`pass_manager.rs:423`). No list refers to a pass that is not declared.

**Execution of the order on `14210df0`.** The sequence of MIR dumps for one function is a
subsequence of the source order at that commit under all four flag sets (52, 55, 43 and 22 pass
dumps). Under Miri's default MIR flags the passes that produced a dump are, in order:
`SimplifyCfg-initial`, `PromoteTemps`, `SimplifyCfg-promote-consts`, `ImpossiblePredicates`,
`CleanupPostBorrowck`, `RemoveNoopLandingPads`, `SimplifyCfg-post-analysis`, `Derefer`,
`AddCallGuards`, `PostAnalysisNormalize`, `Subtyper`, `ElaborateDrops`, `AbortUnwindingCalls`,
`AddMovesForPackedDrops`, `EraseDerefTemps`, `ElaborateBoxDerefs`, `StateTransform`,
`LowerIntrinsics`, `SimplifyCfg-pre-optimizations`, `ForceInline`, `RemoveUnneededDrops`,
`AddCallGuards`. That is exactly the non-lint rows marked "on" in the *Miri default* column of the
main path, modulo the rename and the one pass (`LintAndRemoveUninhabited`) that did not exist yet.
So of the optimization list, only `ForceInline`, `RemoveUnneededDrops` and the last
`CriticalCallEdges` run under Miri's defaults.

### 7. The mechanized model

Basis: derived (machine-checked). File `support/BoxDerefCallGuardsAndReturnDupSoundness.lean`,
2,402 lines, Lean core only, no imports. Checked with Lean v4.34.1 and
`-DwarningAsError=true -Ddebug.skipKernelTC=false -DElab.async=false`.

**What the kernel accepted.** An environment walk over every constant the file adds (217 theorem
constants, 277 definition constants, 44 others) finds: axioms used anywhere are `propext` and
`Quot.sound` only; no `sorryAx`, no `Classical.choice`, no `Lean.ofReduceBool`; no constant is
`unsafe`, `partial`, an `axiom`, an `opaque`, or a `*._unsafe_rec` compiler helper. A false
theorem appended to a copy of the file is rejected. The source text contains no `omega`,
`bv_decide`, `native_decide` or `sorry`.

One fact about the toolchain was learned in the process: a plain recursive `def` makes Lean
v4.34.1 add a compiler-only constant `<name>._unsafe_rec` flagged `partial`. A text search for
`partial def` does not see these. A section-level `noncomputable section` does not prevent them;
a per-definition `noncomputable def` does. All 74 definitions carry the marker; the 11 helper
constants present before were gone afterwards.

**The model and what each piece stands for.**

| Model | Stands for | Not modelled |
|---|---|---|
| `Env := Nat → Nat`; block = list of `Env → Option Env` statements + terminator; `none` = UB | locals; statements | types, memory, places |
| `Term.out inv dst rhs sel targets cleanup` | a `Call` (one target) or an `asm!` with an output (fallthrough and label targets): if `sel env` indexes a target, `dst := rhs env` and control goes there; otherwise control takes `cleanup` without writing `dst`, or aborts if there is none. `inv` = "is emitted as `invoke`/`callbr`" | several outputs; `is_cleanup`; the callee |
| `predCount`, `splitEdge p inv t := inv && 1 < predCount p t` | `pred_count` and the two conditions of the pass | `u8` saturation (irrelevant to `> 1`) |
| `addCallGuards`: block ids `orig b` / `guard b i` | new `goto` block per split (block, target slot) | `rustc`'s consecutive numbering of new blocks |
| `stepLow` with register `reg` and `entry : block → list of locals` | a code generator that leaves an `invoke`/`callbr` result in an SSA value and stores it at the *entry* of each normal destination | LLVM IR itself |
| `IsEntryLowering q entry` | `entry y` contains `d` exactly when `y` is a normal destination of some `out true d …` | — |
| `Term.drop needsDrop glue t unwind`, `DropsWf` | `Drop`; `needsDrop = false` implies the glue is the identity and never unwinds | drop elaboration, partial moves |
| `BoxModel`: `Val.box a`, `Val.raw a`, heap `Nat → Option Val`, address 0 = null | a `Box` value, a raw pointer, liveness | alignment, provenance, size, allocator field |

**Theorems** (names as in the file).

Critical-edge splitting:

- `addCallGuards_operational_equivalence`: for every program `p`, block `b`, environment `e` and
  result `r` (a returned environment, or UB/abort), `p` halts with `r` from `(b, e)` if and only
  if `addCallGuards p` halts with `r` from `(orig b, e)`. Since this holds for every `r`,
  non-termination is preserved as well. The proof is a simulation in which the transformed
  program may take one extra step (the guard block).
- `predCount_unique`: if `predCount p t ≤ 1`, any two (block, slot) pairs with successor `t` are
  equal. This is the step from the pass's counting criterion to a statement about edges.
- `addCallGuards_noCriticalOutEdge`: in `addCallGuards p`, the target of every `out true` normal
  edge has that edge as its only incoming edge.
- `addCallGuards_outEdge_target_entered_only_from_source`: consequently every step that enters
  such a target was taken from the terminator's own block (a unique immediate predecessor, which
  is stronger than dominance).
- `stepLow_erase`, `lowering_sound`: for any graph with that property and any `entry` satisfying
  `IsEntryLowering`, the lowered program and MIR agree step for step.
- `lowering_register_independent`: under the same hypotheses the result does not depend on the
  register's initial value; no entry store ever reads a register value that was not defined on
  the edge just taken.
- `addCallGuards_then_lowering_sound`: combining the above, with no side condition on `p`.

Other passes:

- `removeUnneededDrops_sound`, `removeUnneededDrops_bidirectional`: under `DropsWf`, step-for-step
  equality, hence the same terminal behaviours in both directions.
- `multipleReturnTerminators_bidirectional`: the same terminal behaviours in both directions, with
  no hypothesis; here the *original* program takes the extra step.
- `BoxModel.elaborate_sound`, `elaborate_ub_iff`: for one statement, the elaborated pair is
  undefined exactly when the original is, and otherwise the stores agree except at the temporary.
- `BoxModel.elaborateList_sound`: the same for a statement list, started from stores that agree
  except at the temporary, provided the temporary occurs in no statement.

Counterexamples and witnesses, all closed terms evaluated in the kernel:

- `ce1_unsplit_call_or_callbr_critical_edge_clobbers_other_predecessor_value`: on the shape of the
  `crit_call` MIR above, the forced store placement is a valid `IsEntryLowering`, the property
  fails, and on the path through the *other* predecessor (which set the local to 7) MIR returns 7
  while the lowered program returns the stale register, 0.
- `ce1_after_split_lowering_agrees`: for the same program after `addCallGuards`, a valid placement
  exists and both paths agree with MIR (7 and 42). This shows the hypotheses of the general
  theorem are satisfiable.
- `ce1b_unsplit_callbr_critical_edge_reexecutes_output_store`: `callbr` shape where the label block
  overwrites the output and then joins the fallthrough block: MIR returns 5, the lowered program
  42. Here the register *is* defined on the path taken, so the lowered program is not reading an
  undefined value; it is simply wrong.
- `ce2_remove_drop_on_needs_drop_type_omits_destructor_side_effect`: removing a `Drop` whose type
  needs dropping changes the result from 1 to 0.
- `ce3_multiple_return_duplicating_nonempty_return_block_omits_statements`: ignoring the
  "no statements" condition changes the result from 5 to 0.
- `multipleReturnTerminators_fires`, `removeUnneededDrops_fires`: each pass does change a program,
  and `DropsWf` is satisfiable.
- `BoxModel.plain_transmute_loses_box_validity_ub`: a dangling `Box` used only in
  `&raw const *b` is undefined before elaboration and after elaboration with `BoxDerefTransmute`,
  but defined after elaboration with a plain `Transmute`.
  `BoxModel.plain_transmute_sound_for_loads` shows the plain form loses nothing when the place is
  actually loaded from.

### 8. What this means for Anneal's trusted boundary

Basis: source (`joshlf/anneal@c131b320`) + derived.

Source facts:

- `trusted/lean/Trusted/MirAst.lean` describes itself as "the trusted abstract syntax tree for
  post-cleanup runtime Mid-level Intermediate Representation (`Runtime(PostCleanup)` MIR) extracted
  by `anneal-rustc-capture`" (`:52-54`).
- Its type descriptor `MirTy` (`:312-321`) has no constructor for general ADTs or pattern types;
  the comment (`:308-311`) routes non-fieldless-enum `Adt` and `Pat` to `.unsupported`.
- `Rvalue` (`:620-628`) has no cast constructor; the comment (`:612-618`) lists `Cast` and
  non-tuple `Aggregate` among the variants represented by `.unsupported`.
- `TerminatorKind` (`:785-795`) has `.call callee args dst target unwind` for direct calls and
  routes `Drop` and `InlineAsm` to `.unsupported` (`:782-784`).
- `trusted/rustc-capture/src/driver.rs:25` pins `"1.98.0-nightly (f8a08b688 2026-05-30)"`, and
  its analysis callback states "No compiler data or verification obligation is extracted here"
  (`:79`). At this commit the driver does not yet extract MIR.

Derived consequences for a capture at `Runtime(PostCleanup)`:

1. *Upstream of that point:* `Derefer`, the first `CriticalCallEdges`, `EraseDerefTemps`,
   `ElaborateBoxDerefs` (all `Required`), then `LowerIntrinsics`, `RemovePlaceMention` and
   `SimplifyCfg::PreOptimizations`. *Downstream, never seen by such a capture:* the whole
   optimization list, including `RemoveUnneededDrops`, both `MultipleReturnTerminators` and the
   last `CriticalCallEdges`.
2. Such MIR can contain critical call edges. The first split is undone by
   `SimplifyCfg::PreOptimizations` before the phase change (executed on `14210df0`: 8 → 7 blocks),
   and the validator's rule applies only from `Runtime(Optimized)`. A consumer must therefore give
   `Call` its MIR meaning (the destination is written as part of the terminator, on the return
   edge) and must not assume the return target has a single predecessor. `MirAst`'s `.call`
   carries `dst` inside the terminator, which is compatible with this.
3. At `f8a08b68` the Box-deref lowering is the `Transmute` form: its `elaborate_box_derefs.rs` is
   byte-identical to the one at `14210df0`. Either form is outside the modelled fragment (`Box` is
   an unsupported type, `Cast` an unsupported rvalue), so a body that dereferences a `Box` fails
   closed at either compiler version. If the compiler pin moves to a commit that contains
   `fcf68f21`, any code that matches on `CastKind` exhaustively gains a variant; once it contains
   `5d260fd3`, the operand's type is `BoxRaw<T>`.
4. Constructor bodies are not produced by the pipeline at all. A capture that hooks pipeline
   queries does not see them; their body is a single non-tuple `Aggregate`, which `MirAst` maps to
   `.unsupported`.

## Boundaries

**Not examined.**

- No `rustc` at `3ef0c22c` or `bdf712ee` was executed. In particular the `BoxDerefTransmute` MIR
  text, Miri's behaviour on an invalid `Box` at those commits, and the constructor dump name there
  are not observed.
- Targets other than `x86_64-unknown-linux-gnu`; `-C panic=abort`; incremental compilation;
  Cranelift and GCC back ends beyond the one-line match noted above; Windows SEH and wasm
  exception handling, where `do_call` decides differently whether to emit `invoke`.
- LLVM IR was not inspected. The statement that the store lands in the target block is from
  `rustc`'s code generator source, not from emitted IR.
- `Box<T, A>` with a non-`Global` allocator; unsized pointees; `ThinBox`.
- The bodies of the other passes in the table. The table states where and under which policy each
  pass is scheduled, not what it does or whether it is sound.
- The shim and coroutine lists beyond their contents.
- The second `rustc` commit that `MirAst.lean` cites for its quotations.

**Unknown.**

- Whether Miri at `3ef0c22c`/`bdf712ee` reports the dangling-place program; the prediction is from
  source only.
- Whether any real `asm!` reaches code generation with an unsplit output edge. The validator does
  not check `InlineAsm`, and nothing here tests it.
- Why `AllCallEdges` is retained.

**Known not to apply.**

- "`BoxRaw` is a pattern type" is false; it wraps `NonNull`, which wraps one.
- "`CriticalCallEdges` runs twice" holds for the main pipeline only; crate-wide there are seven
  sites.
- "Every unwinding call edge is split": only those whose target has another predecessor.
- "`RemoveUnneededDrops` is an optimization that Miri does not see": it runs at MIR optimization
  level 0.
- The retained record's counters are not comparable with this report's probe results; the two
  come from different probe functions.

**Unsupported.**

- The probe needs a nightly toolchain. `asm_goto_with_outputs` is a feature gate on `14210df0`;
  the probe retries without the gate if the first compile fails.
- Disabling `AddCallGuards` to observe a miscompilation is not possible through
  `-Zmir-enable-passes`: the pass is `Required` (`is_required() = true` at `14210df0`).

**Stronger conclusions this report does not establish.**

- That `rustc`'s passes are correct. The theorems are about a small model whose correspondence to
  `rustc` is argued in prose (the table in Finding 7).
- That splitting critical edges is *sufficient* for correct code generation in LLVM. The model
  shows sufficiency for one abstract placement rule.
- That an entry-store placement exists for every program after splitting. It is exhibited for one
  program; the general theorem quantifies over placements.
- A whole-program theorem for `ElaborateBoxDerefs`. The result is for straight-line statement
  lists with one reused temporary, whereas `rustc` allocates one temporary per deref.
- That the pass table "covers" `rustc_mir_transform` in any sense beyond scheduling: 78 of 81
  declared names are located in pass lists and the other three are accounted for.

## Evidence

**Commit identities.** Each was resolved on 2026-11-21 through the GitHub REST API
(`GET /repos/{owner}/{repo}/commits/{ref}`), which returned the same 40-hex `sha`:
`rust-lang/rust` `main` → `bdf712ee87c22a2b5c60db2e1af8a63e3cfd1a2e`;
`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`; `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`;
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`; `fcf68f21cf2f50e824bc4054ca4f46f0dd8ce42f`;
`2cee42105a5cc121030724e6ac806e3dd509c6e6`; `5d260fd3da7b0165d6365adab12746bfc389d913`;
`joshlf/anneal` → `c131b320eeeb26ef692e5afd5ec8db49ee518613`; `leanprover/lean4` tag `v4.34.1` →
`5045d0056413266e57c625dcd7c365b10e377c52`. `rustc -vV` of the executed toolchain prints
`commit-hash: 14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`; `lean --version` prints the Lean commit.

**Source.** Files were read from `raw.githubusercontent.com` at the commits above; for `14210df0`
also from the toolchain's own `rustc-src` and `rust-src` components, which matched the GitHub
copies for the files compared. `support/source_anchors.json` records, for 81 cited source lines,
the line number at each of the three `rustc` commits (an empty list where the construct does not
exist), and SHA-256 and line counts of the 20 files involved. From it: `add_call_guards.rs`,
`elaborate_box_derefs.rs`, `remove_unneeded_drops.rs`, `multiple_return_terminators.rs`,
`deref_separator.rs`, `erase_deref_temps.rs`, `mir/syntax.rs`, `interpret/cast.rs`,
`interpret/place.rs`, `boxed.rs` and Miri's `lib.rs` are byte-identical at `bdf712ee` and
`3ef0c22c`; `lib.rs`, `pass_manager.rs`, `shim.rs`, `validate.rs`, `block.rs`, `asm.rs`,
`ty/util.rs`, `config.rs` and `non_null.rs` differ between those two, and all 20 differ at
`14210df0`.

**Pass pipeline.** `support/pass_pipeline_rustc_{bdf712ee,3ef0c22c,14210df0e}.json`, generated by
`support/extract_pass_pipeline.py` from all 97 `.rs` files of the crate at each commit. The
extractor cross-checks itself: every line that consists of a single pass reference inside a
`&[…]` literal must have been parsed as a list entry, and it writes nothing otherwise. The table
in Finding 6 is the output of `support/render_pass_table.py` on the `bdf712ee` file.

**Execution** (2026-11-21). `support/probe_boxraw_call_guards_and_pipeline_closure.py` embeds the
Rust sources and prints the commands it runs. Its output on `14210df0` is
`support/probe_results_rustc_14210df0e.json`: 16 checks held, 0 failed, 0 skipped. Miri needed a
sysroot built from the toolchain's own `rust-src`. Command shape:

```sh
python3 probe_boxraw_call_guards_and_pipeline_closure.py \
    --rustc "$TOOLCHAIN/bin/rustc" --miri "$TOOLCHAIN/bin/miri" \
    --miri-sysroot "$MIRI_SYSROOT" --out probe_results.json
```

**Retained record.** `support/recorded_observation_rustc_3ef0c22c.json`; see Applicability for its
status. Its toolchain block reads `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, LLVM 23.1.5.

**Lean** (2026-11-21). `support/verify_lean.py` runs the three checks described in Finding 7;
`support/lean_verification_result.json` is its output. Compiler flags:
`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

**Anneal.** `trusted/lean/Trusted/MirAst.lean` (944 lines) and
`trusted/rustc-capture/src/driver.rs` (152 lines) at `c131b320`, line numbers as cited.

**Synthesis versus source.** The three-form table in the Summary, the "why twice" argument, the
*Miri default* and *Class* columns, the correspondence table of Finding 7 and all of Finding 8's
consequences are this report's synthesis. Quoted text and line numbers are source.

## Revalidation

Cheapest checks first.

1. **Has the Box-deref form changed again?** At the commit of interest, read
   `compiler/rustc_mir_transform/src/elaborate_box_derefs.rs` and look at the `Rvalue::Cast(…)`
   it builds, and at the declaration of `Box` in `library/alloc/src/boxed.rs`. Two lines decide it.
2. **Does a given toolchain behave as described?** Run the probe. It classifies the lowering it
   sees (`box_deref_lowering_era`), re-checks the block counts around both `AddCallGuards` runs
   and `SimplifyCfg-pre-optimizations`, the drop removal, the return counts at levels 2 and 4, and
   the constructor dumps. A passing probe establishes only those checks. On a toolchain that
   contains `5d260fd3`, the fields to read first are `box_deref_lowering_era` (expected
   `BoxDerefTransmute-of-BoxRaw`) and `dangling_box_place_only_summary` (this report predicts UB
   is reported there; the probe does not assert it).
3. **Has the pipeline changed?** `extract_pass_pipeline.py --fetch <commit>` followed by a diff of
   the `lists` and `census` sections against the files here. If the extractor exits with status 3,
   the shape of a pass list changed and the extractor needs attention before its output can be
   trusted.
4. **Do the cited lines still exist?** `locate_source_anchors.py --root <commit>=<checkout>`; an
   anchor that becomes an empty list points at the finding to re-read.
5. **Critical-edge rule.** Diff `add_call_guards.rs` (the two `if` conditions and
   `generates_invoke`) and `validate.rs` around `is_critical_call_edge`.
6. **Lean.** `verify_lean.py --lean <lean>`; on another Lean version expect to adjust tactic
   proofs, not statements. Check the `audit` block of its output, not just the exit status of the
   plain run: the `*._unsafe_rec` constants were invisible to both a text search and the plain run.
7. **Anneal.** Re-read the header of `MirAst.lean` for the target phase and
   `COMPILER_VERSION` in the capture driver; if that compiler contains `fcf68f21`, Finding 8.3
   needs the newer lowering.

No cheap check exists for the correspondence between the Lean model and `rustc`; that argument
has to be re-read against the pass sources.
