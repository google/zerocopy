# Non-diverging MIR intrinsic statements (`assume`, `copy_nonoverlapping`), unreachable-switch pruning, and the `assume` gap between `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR

## Summary

`rustc` MIR has exactly two intrinsic *statements*, both variants of
`StatementKind::Intrinsic(Box<NonDivergingIntrinsic>)`: `Assume(Operand)` and
`CopyNonOverlapping { src, dst, count }`. What a consumer of MIR needs to retain:

1. **Who creates them.** `LowerIntrinsics` turns a *direct* call to
   `core::intrinsics::assume` / `core::intrinsics::copy_nonoverlapping` into the
   statement plus a `goto`. The stable wrappers `core::hint::assert_unchecked`,
   `core::ptr::copy_nonoverlapping` and `core::hint::unreachable_unchecked` are
   ordinary functions, so user code that calls them still contains a `Call`
   terminator in `Runtime(PostCleanup)` MIR; the statement only appears in the
   caller once `Inline` splices the wrapper body in. Independently,
   `remove_successors_from_switch` (called by `UnreachablePropagation` and by
   `MatchBranchSimplification`) *synthesizes* `assume` statements when it removes
   `SwitchInt` arms that lead to unreachable blocks.

2. **The gap, measured.** Compiling `google/zerocopy` 0.8.64 with rustc
   1.98.0-nightly (`14210df0e`) at `-C opt-level=2`: `Runtime(PostCleanup)` MIR
   contains **0** `assume` and **0** `copy_nonoverlapping` statements in 4,838
   bodies; `Runtime(Optimized)` MIR contains **406** `assume` statements in 54
   bodies and **6** `copy_nonoverlapping` statements in 6 bodies (4,586 bodies).
   The per-pass ledger attributes this exactly: `Inline` +56 `assume` and +6
   `copy_nonoverlapping`, `UnreachablePropagation` +355 `assume` (peak 411),
   `SimplifyConstCondition-after-inst-simplify` −9, `MatchBranchSimplification`
   +8, `SimplifyCfg-final` −4; no other pass changes either count. All 355
   statements added by `UnreachablePropagation` are `assume(discr == value)`.
   A recorded run on 1.102.0-nightly (`3ef0c22cd`), which was not re-executed
   for this report, shows the same shape: 0, then 420 after
   `UnreachablePropagation`, then 385 in 58 bodies.

3. **What they mean.** `assume(op)` with `op == false` is undefined behaviour,
   exactly like reaching `TerminatorKind::Unreachable`. For
   `copy_nonoverlapping`, **alignment of both pointers is required even when
   `count * size_of::<T>() == 0`**; nothing else is required for a zero-length
   copy, so **null and dangling aligned pointers are accepted**. A non-empty
   copy additionally needs both ranges dereferenceable and non-overlapping.

4. **Two readings that look right and are wrong.** (a) A program that passes a
   syntactic `ptr::null()` to `ptr::copy_nonoverlapping(.., 0)` fails with exit
   status 1 under Miri, but the failure is the deny-by-default *compile-time
   lint* `invalid_null_arguments`, not an interpreter verdict; with the lint
   allowed, or the null hidden behind `black_box`, Miri accepts the program in
   every mode tested. (b) The MIR passes `CheckNull` and `CheckAlignment` do
   **not** instrument a `copy_nonoverlapping` statement; they instrument
   raw-pointer *dereference places*. The debug-build check for
   `ptr::copy_nonoverlapping` is the library precondition inside the wrapper,
   which enforces alignment at zero length and exempts null at zero length.

5. **Pruning is exact, with two side conditions.** For a `SwitchInt` with at
   least one valued arm and pairwise distinct arm values, replacing arms into
   unreachable blocks by `assume` statements yields a block that has undefined
   behaviour exactly when the original has, and otherwise continues at the same
   successor (kernel-checked, `pruneSwitch_exact` / `pruneSwitch_ub_iff`). The
   `assume` is what makes this bidirectional: removing an arm without it turns
   undefined behaviour into defined behaviour. A `SwitchInt` with *zero* valued
   arms is rewritten to a bare `goto`, which drops the discriminant read; with an
   uninitialized discriminant Miri reports undefined behaviour before the pass
   and none after it.

6. **Consequence for a verifier that models `SwitchInt` and `Unreachable` but
   not `Intrinsic`.** In `joshlf/anneal` at `c131b320`, `Trusted.MirAst.StatementKind`
   has the constructors `assign`, `storageLive`, `storageDead`, `nop`,
   `unsupported`; `Intrinsic` lowers to `.unsupported`, which steps to
   `.fault .unsupported`, while `TerminatorKind.switchInt` and
   `TerminatorKind.unreachable` are modeled. A switch the model can express
   before `UnreachablePropagation` is therefore turned into a statement it
   rejects, although the two forms are equivalent (finding 12). One statement constructor with the semantics "operand `true`
   continues, operand `false` faults as undefined" closes the gap; alternatively
   `assume(op)` can be re-expressed as `switchInt(op) -> [0: unreachable block,
   otherwise: next]` (`assume_as_switch_gadget`).

## Applicability

**Subjects and how they relate.**

- `rust-lang/rust` at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` is both the
  source revision audited line by line and the toolchain executed
  (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, host
  `x86_64-unknown-linux-gnu`, LLVM 22.1.6, with the `miri`, `rust-src` and
  `rustc-dev` components of that same nightly). Every execution result in this
  report was produced with it.
- `rust-lang/rust` at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`
  (`1.102.0-nightly`, 2026-11-11) is a **source-only** comparison revision: the
  same files were fetched and diffed, nothing was executed. Differences that
  matter are listed under "Differences between the two rustc revisions".
- `google/zerocopy` at `907b9175fee081872ec883ca4709e6ad922f8ed0` (crate version
  0.8.64) is the workload of the whole-crate census.
- `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613` is the verifier
  whose trusted MIR model (`trusted/lean/Trusted/MirAst.lean`,
  `trusted/lean/Trusted/MirSemantics.lean`,
  `trusted/correspondence/Trusted/Correspondence.lean`) is read against the
  rustc facts. Only those three Lean files were examined.
- `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`)
  is the kernel that checked the mechanization.

**Configuration of the execution evidence.** The census compiles the crate root
directly with `rustc --edition=2021 --crate-type rlib --cfg feature="alloc"
--cfg feature="simd"` plus the `--cfg` flags printed by the crate's `build.rs`
(on this toolchain: `no_zerocopy_allocator_api_1_100_0`), `-C opt-level=2`, no
incremental compilation, default panic strategy. Under these flags
`mir_opt_level()` is 2, so `Inline`, `UnreachableEnumBranching` and
`UnreachablePropagation` are all enabled. At `-C opt-level=0`
`UnreachablePropagation` is disabled (it requires `mir_opt_level() >= 2`) and
`Inline` is disabled; with `-C incremental` `Inline` is disabled at
`mir_opt_level() == 2`. Counts therefore do not transfer to other optimization
levels, feature sets, incremental builds, other targets, or other crates; what
transfers is the mechanism.

**Scope of the interpreter evidence.** Miri was run on single-file programs with
its default settings (Stacked Borrows, `-Zmir-opt-level=0` for the program),
with `-Zmiri-tree-borrows`, and with `-Zmir-opt-level=2 -Copt-level=2` (which
inlines the library wrappers into the program before interpretation). Verdicts
were identical in the three modes for all 17 specimens.

**Scope of the mechanization.** `support/NonDivergingIntrinsicsAndUnreachableProp.lean`
is a standalone model, not an extract of rustc or of `joshlf/anneal`: locals map
to optional values, memory is a flat map from addresses to optional slots,
pointers are bare addresses, discriminants are compared by bit pattern. Its
theorems are statements about that model. The model's switch-pruning function
was compared against rustc's actual output for every reachable `SwitchInt` in
the census (2,431 terminators, 0 disagreements), which is execution evidence
that the function mirrors `remove_successors_from_switch`; the semantic
theorems themselves are not validated against rustc beyond the Miri specimens.

**Exact observation versus extension.** Statements about `3ef0c22cd` are source
readings only. The claim that the mechanism applies to it rests on the diff:
`remove_successors_from_switch`, `variant_discriminants`, the body of
`UnreachableEnumBranching::run_pass`, `eval_nondiverging_intrinsic`,
`copy_intrinsic`, `check_and_deref_ptr`, the library precondition and the lint
table are textually unchanged apart from API renames (see below).

## Findings

### 1. The two statements and their documented meaning

Basis: source.

`compiler/rustc_middle/src/mir/syntax.rs` (lines 432–434 and 469–492 at
`14210df0e`; 436 and 462–485 at `3ef0c22cd`, same text):

```rust
/// Denotes a call to an intrinsic that does not require an unwind path and always returns.
/// This avoids adding a new block and a terminator for simple intrinsics.
Intrinsic(Box<NonDivergingIntrinsic<'tcx>>),

pub enum NonDivergingIntrinsic<'tcx> {
    /// Denotes a call to the intrinsic function `assume`.
    ///
    /// The operand must be a boolean. [...]
    /// If the argument is `false`, this operation is equivalent to `TerminatorKind::Unreachable`.
    Assume(Operand<'tcx>),

    /// Denotes a call to the intrinsic function `copy_nonoverlapping`.
    ///
    /// First, all three operands are evaluated. `src` and `dest` must each be a reference, pointer,
    /// or `Box` pointing to the same type `T`. `count` must evaluate to a `usize`. Then, `src` and
    /// `dest` are dereferenced, and `count * size_of::<T>()` bytes beginning with the first byte of
    /// the `src` place are copied to the contiguous range of bytes beginning with the first byte
    /// of `dest`.
    ///
    /// **Needs clarification**: In what order are operands computed and dereferenced? ...
    /// **Needs clarification**: Is this typed or not, ie is there a typed load and store involved? ...
    CopyNonOverlapping(CopyNonOverlapping<'tcx>),
}
```

The MIR validator (`compiler/rustc_mir_transform/src/validate.rs:1496–1532` at
`14210df0e`) requires the `assume` operand to have type `bool`
(``"`assume` argument must be `bool`"``), and requires `src` and `dst` of
`copy_nonoverlapping` to be pointers to assignment-compatible pointee types.
The pretty-printer renders the statements as `assume({op:?})` and
`copy_nonoverlapping(dst = {dst:?}, src = {src:?}, count = {count:?})`
(`compiler/rustc_middle/src/mir/pretty.rs:914–923`); those two shapes are what
the census counts.

### 2. Producers and consumers at `14210df0e`

Basis: source (a search for `NonDivergingIntrinsic` and `Intrinsic(` over
`rustc_mir_transform`, `rustc_mir_build`, `rustc_const_eval`,
`rustc_codegen_ssa`, `rustc_middle/src/mir`, `rustc_borrowck`).

| Role | Location | What it does |
|---|---|---|
| producer | `lower_intrinsics.rs:61–79` | direct call to the `copy_nonoverlapping` intrinsic → `CopyNonOverlapping` statement + `goto` |
| producer | `lower_intrinsics.rs:80–92` | direct call to the `assume` intrinsic → `Assume` statement + `goto` |
| producer | `unreachable_prop.rs:104–116` (`add_assumption`) | `tmp = <Eq or Ne>(copy discr, const v); assume(move tmp)`; reached from `UnreachablePropagation` (`unreachable_prop.rs:38`) and from `MatchBranchSimplification` (`match_branches.rs:401–409`) |
| producer | `large_enums.rs:135–141` (`EnumSizeOpt`) | byte-wise `CopyNonOverlapping` for moves of large enums; enabled only with `-Zunsound-mir-opts` and `mir_opt_level() >= 3` (`large_enums.rs:34–39`), so inactive in every run reported here |
| producer | `rustc_mir_build/src/builder/custom/parse/instruction.rs:24` | `Assume` in hand-written custom MIR |
| consumer | `simplify_branches.rs:53–64` (`SimplifyConstCondition`) | `assume(const true)` → `nop`; `assume(const false)` → the block's terminator becomes `Unreachable` |
| consumer | `jump_threading.rs:635–640`, `ssa_range_prop.rs:146` | use the assumed condition as a fact |
| consumer | `dataflow_const_prop.rs:195–199` | ignores `Assume` ("Could use this, but ignoring it is sound.") |
| consumer | `rustc_const_eval/src/interpret/step.rs:114` → `intrinsics.rs:905–929` | interpretation (CTFE and Miri) |
| consumer | `rustc_codegen_ssa/src/mir/statement.rs:70–96` | `bx.assume(..)` and `bx.memcpy(dst, align, src, align, count * elem_size, ..)` |

`LowerIntrinsics` is the first pass of `run_runtime_cleanup_passes`
(`rustc_mir_transform/src/lib.rs:653–666`: `LowerIntrinsics`,
`RemovePlaceMention`, `SimplifyCfg::PreOptimizations`), whose result is
`Runtime(PostCleanup)` MIR. `Inline`, `UnreachableEnumBranching`,
`UnreachablePropagation` and `MatchBranchSimplification` are in
`run_optimization_passes` (`lib.rs:675–773`, positions 709, 720, 721 and 746),
whose result is `Runtime(Optimized)` MIR. A body whose entry block is a lone
`unreachable` skips the optimization pipeline entirely (`lib.rs:810–817`).

### 3. `LowerIntrinsics`: direct intrinsic calls versus stable wrappers

Basis: source + execution (`support/probe_results.json`, key
`pass_specimens.lower_intrinsics`).

| Function body | terminator before `LowerIntrinsics` | after `LowerIntrinsics` | statements in `Runtime(Optimized)` |
|---|---|---|---|
| `core::intrinsics::assume(c)` | `_0 = assume(move _2) -> [return: bb1, unwind unreachable];` | `assume(move _2); goto -> bb1;` | 1 `assume` |
| `core::intrinsics::copy_nonoverlapping(src, dst, n)` | `_0 = std::intrinsics::copy_nonoverlapping::<u64>(move _4, move _5, move _6) -> [return: bb1, unwind unreachable];` | `copy_nonoverlapping(dst = move _5, src = move _4, count = move _6); goto -> bb1;` | 1 `copy_nonoverlapping` |
| `core::intrinsics::unreachable()` | `_0 = unreachable() -> unwind unreachable;` | `unreachable;` | (body skips optimization) |
| `core::hint::assert_unchecked(c)` | `_0 = assert_unchecked(move _2) -> [return: bb1, unwind continue];` | unchanged `Call` | 1 `assume` (after `Inline`) |
| `core::ptr::copy_nonoverlapping(src, dst, n)` | `_0 = std::ptr::copy_nonoverlapping::<u64>(move _4, move _5, move _6) -> [return: bb1, unwind continue];` | unchanged `Call` | 1 `copy_nonoverlapping` (after `Inline`) |
| `core::hint::unreachable_unchecked()` | `_0 = unreachable_unchecked() -> unwind continue;` | unchanged `Call` | 1 `unreachable` (after `Inline`) |

The wrappers are defined in `library/core/src/hint.rs:202–212`
(`assert_unchecked`: precondition check, then `crate::intrinsics::assume(cond)`),
`library/core/src/ptr/mod.rs:530–552` (`copy_nonoverlapping`: precondition
check, then `crate::intrinsics::copy_nonoverlapping(src, dst, count)`) and
`library/core/src/hint.rs:103–112`. Because stable code can only reach the
intrinsics through these wrappers, a crate that does not enable
`core_intrinsics` has no intrinsic statement in its own `Runtime(PostCleanup)`
bodies; this is the source-level reason for the zeros in the census.

### 4. `remove_successors_from_switch`: the complete case table

Basis: source (`unreachable_prop.rs:65–154` at `14210df0e`) + execution
(golden blocks and model comparison in `support/probe_results.json`, key
`pass_specimens.switch_pruning`).

`UnreachablePropagation` visits blocks in post-order and keeps a set of
unreachable blocks: a block joins the set when its terminator is `Unreachable`,
when it is a `Goto` to a member (the terminator is patched to `Unreachable`), or
when it is a `SwitchInt` that `remove_successors_from_switch` reports as fully
unreachable. After patching, the statements of every member are cleared.

Let `targets` be the valued arms, `otherwise` the fallback, `reach` the valued
arms whose block is not in the set, and `num_targets = len(reach) + 1`:

| `otherwise` unreachable | `reach` | statements appended | new terminator |
|---|---|---|---|
| yes | empty | none | `Unreachable` (block joins the set) |
| yes | exactly one arm `(v, t)` | `tmp = Eq(copy discr, const v); assume(move tmp)` | `Goto t` |
| yes | two or more arms | none | `SwitchInt` over `reach` (unchanged if nothing was removed) |
| no | empty | one `tmp_i = Ne(copy discr, const v_i); assume(move tmp_i)` per removed arm | `Goto otherwise` |
| no | non-empty | same `Ne` assumptions, one per removed arm | `SwitchInt` over `reach` (unchanged if nothing was removed) |

Details that matter to a consumer: each assumption uses its own fresh `bool`
temporary (`patch.new_temp`); the discriminant operand is converted with
`to_copy()`, so a `switchInt(move _2)` yields `Ne(copy _2, ..)`; the constant is
built as `Const::from_scalar(tcx, Scalar::from_uint(value, discr_size), discr_ty)`,
i.e. a constant of the discriminant's own type (`const false` for a `bool`,
`const 0_isize` for an enum discriminant); no `Ne` assumption is emitted when
`otherwise` is itself unreachable, because the removed value then falls through
to an unreachable block anyway.

Golden blocks observed at `14210df0e` (function names are those of the specimen
crate embedded in the probe):

| Specimen | block before | block after |
|---|---|---|
| `up_one_arm_otherwise_unreachable` | `switchInt(copy _1) -> [5: bb2, otherwise: bb1];` | `_3 = Eq(copy _1, const 5_u8); assume(move _3); goto -> bb2;` |
| `up_removed_arm_otherwise_reachable` | `switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1];` | `_3 = Ne(copy _1, const 0_u8); assume(move _3); switchInt(copy _1) -> [1: bb2, otherwise: bb1];` |
| `up_all_arms_unreachable_otherwise_reachable` | `switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1];` | `_4 = Ne(copy _1, const 0_u8); assume(move _4); _5 = Ne(copy _1, const 1_u8); assume(move _5); goto -> bb1;` |
| `up_everything_unreachable` | `switchInt(copy _1) -> [0: bb2, otherwise: bb1];` | `unreachable;` |
| `up_two_arms_otherwise_unreachable` | `switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1];` | unchanged, no `assume` |
| `up_bool_discriminant` | `switchInt(move _2) -> [0: bb2, otherwise: bb1];` | `_4 = Ne(copy _2, const false); assume(move _4); goto -> bb1;` |
| `up_degenerate_zero_arm_switch` (custom MIR) | `switchInt(copy _1) -> bb1;` | `goto -> bb1;` |
| `ueb_result_infallible` | `switchInt(move _2) -> [0: bb3, 1: bb1, otherwise: bb1];` | `_4 = Eq(copy _2, const 0_isize); assume(move _4); goto -> bb3;` |

The probe contains an executable reference model of the function
(`model_remove_successors`, with the unreachable set computed as the least
fixpoint over blocks reachable from `bb0`). It predicts rustc's output for all
10 specimens and, in the census, for **all 2,431** reachable `SwitchInt`
terminators present before `UnreachablePropagation` (366 rewrites: 355 of the
"one surviving arm" kind, each with exactly one `Eq` assumption, and 11
reductions to a smaller `SwitchInt` with no assumption; 0 disagreements). The
Lean function `pruneSwitch` is the same case table; ten `golden_*` theorems
check by `rfl` that `pruneSwitch` and `enumBranching` reproduce the blocks rustc
emitted for these specimens and for those of finding 5 (the zero-arm block is
checked inside `ce4`).

**The zero-arm case.** The pattern `(1, false) => Goto { target: otherwise }`
is matched *before* the "nothing has changed" exit, so a `SwitchInt` with no
valued arm and a reachable `otherwise` becomes a `goto` and its discriminant is
no longer read. Execution: a custom-MIR function whose `SwitchInt` reads an
uninitialized local is reported by Miri as
`Undefined Behavior: using uninitialized data, but this operation requires initialized memory`
at `-Zmir-opt-level=0`, and prints `result=7` with exit status 0 once
`UnreachablePropagation` alone is enabled
(`-Zmir-opt-level=0 -Zmir-enable-passes=+UnreachablePropagation`). The rewrite
is a refinement (undefined behaviour may become anything) but not an
equivalence.

**Why distinct arm values matter.** `SwitchInt` selects the first arm whose
value matches. The validator rejects repeated values
(``"duplicated values in `SwitchInt` terminator"``, `validate.rs:346–363`), and
`syntax.rs` documents "Target values may not appear more than once." (line 703
at `14210df0e`, 696 at `3ef0c22cd`) Without that invariant the "one surviving arm" rewrite would not be
exact (`ce5_duplicate_switch_values_break_exactness`).

### 5. `UnreachableEnumBranching`

Basis: source (`unreachable_enum_branching.rs:17–171` at `14210df0e`) +
execution (same specimen crate).

The pass applies to a non-cleanup block that ends in
`switchInt(move local)` whose last statement is `local = discriminant(place)`
with `place` of enum type. It computes the set of discriminants of *inhabited*
variants from the layout (`Variants::Empty` → empty set; `Variants::Single` →
that variant; `Variants::Multiple` → variants whose layout is not uninhabited;
if the layout is unavailable for a generic type, all variants). Then:

1. every explicit arm whose value is not in the set (`allowed_variants.remove`
   returns `false`) is redirected to an empty unreachable block;
2. if at most one inhabited discriminant has no explicit arm and `otherwise` is
   not already an empty unreachable block, that discriminant (if any) gets an
   explicit arm to the old `otherwise`, and `otherwise` becomes the unreachable
   block.

The pass emits no `assume`; it only creates arms into an unreachable block.
`UnreachablePropagation`, which runs immediately afterwards, then applies the
table of finding 4. Observed chain for `match r { Ok(v) => v, Err(_) => 7 }`
with `r: Result<u32, Infallible>`:

```text
before UnreachableEnumBranching   switchInt(move _2) -> [0: bb3, 1: bb2, otherwise: bb1];
after  UnreachableEnumBranching   switchInt(move _2) -> [0: bb3, 1: bb1, otherwise: bb1];
after  UnreachablePropagation     _4 = Eq(copy _2, const 0_isize); assume(move _4); goto -> bb3;
Runtime(Optimized), whole body    _2 = discriminant(_1); _3 = Eq(copy _2, const 0_isize);
                                  assume(move _3); _0 = copy ((_1 as Ok).0: u32); return;
```

Other observed shapes: `enum E3 { A, B(Infallible), C }` matched exhaustively
goes from `[0: bb4, 1: bb3, 2: bb2, otherwise: bb1]` to
`[0: bb4, 1: bb1, 2: bb2, otherwise: bb1]` and then (no `assume`) to
`[0: bb4, 2: bb2, otherwise: bb1]`; a three-variant fieldless enum matched as
`Less => .., Equal => .., _ => ..` goes from `[0: bb3, 1: bb2, otherwise: bb1]`
to `[0: bb3, 1: bb2, 2: bb1, otherwise: bb5]` with `bb5: unreachable`.

Soundness depends on the discriminant actually being that of an inhabited
variant, which the validity invariant of enum values provides in Rust
(derived; mechanized as `enumBranching_sound`, with the necessity of the
hypothesis shown by `enumBranching_forged_hits_unreachable` and `ce3`).

### 6. Operational semantics in the interpreter

Basis: source + execution.

`eval_nondiverging_intrinsic` (`interpret/intrinsics.rs:905–929` at
`14210df0e`):

```rust
NonDivergingIntrinsic::Assume(op) => {
    let op = self.eval_operand(op, None)?;
    let cond = self.read_scalar(&op)?.to_bool()?;
    if !cond {
        throw_ub_format!("`assume` called with `false`");
    }
    interp_ok(())
}
NonDivergingIntrinsic::CopyNonOverlapping(mir::CopyNonOverlapping { count, src, dst }) => {
    let src = self.eval_operand(src, None)?;
    let dst = self.eval_operand(dst, None)?;
    let count = self.eval_operand(count, None)?;
    self.copy_intrinsic(&src, &dst, &count, /* nonoverlapping */ true)
}
```

`copy_intrinsic` (`intrinsics.rs:1045–1070`) then performs, in this order:

1. `count` is read as a target `usize`; the pointee layout gives `size` and
   `align`;
2. `compute_size_in_bytes(size, count)` must succeed, otherwise
   ``overflow computing total size of `copy_nonoverlapping` ``;
3. `check_ptr_align(src, align)` and `check_ptr_align(dst, align)` —
   **unconditionally, before the total size is looked at**;
4. `mem_copy(src, dst, size, nonoverlapping = true)`.

`mem_copy_repeatedly` (`interpret/memory.rs`, from line 1486) asks
`get_ptr_access` for both ranges; `check_and_deref_ptr` (`memory.rs:519–534`)
starts with

```rust
// Everything is okay with size 0.
if size == 0 {
    return interp_ok(None);
}
```

and a zero-sized source returns early ("Zero-sized *source*, that means dest is
also zero-sized and we have nothing to do"). For a pointer without an
allocation (an integer address such as null or `NonNull::dangling()`),
`is_ptr_misaligned` (`memory.rs:579–624`) tests the address itself, and address
0 is a multiple of every alignment. Hence: zero-length copy ⇒ only alignment is
checked; non-empty copy ⇒ both ranges must be inside live allocations, and if
both lie in the same allocation the offsets must not overlap
(``"`copy_nonoverlapping` called on overlapping ranges"``, `memory.rs:1581–1590`).

Miri matrix (17 programs × 3 modes; exit status and first diagnostic were
identical across the three modes in every row; `support/probe_results.json`,
key `miri_matrix`):

| Program (pointee `u64` unless noted) | exit | first diagnostic |
|---|---|---|
| `assert_unchecked(black_box(false))` | 1 | ``Undefined Behavior: `assume` called with `false` `` |
| `assert_unchecked(black_box(true))` | 0 | — |
| `unreachable_unchecked()` reached | 1 | `Undefined Behavior: entering unreachable code` |
| `count = 0`, `src = null` (lint allowed) | 0 | — |
| `count = 0`, `dst = null` (lint allowed) | 0 | — |
| `count = 0`, `src = black_box(null)` | 0 | — |
| `count = 0`, `src` misaligned by one byte | 1 | `Undefined Behavior: accessing memory with alignment 1, but alignment 8 is required` |
| `count = 0`, `dst` misaligned by one byte | 1 | same |
| `count = 0`, `src = dst = NonNull::dangling()` | 0 | — |
| pointee `()`, `count = 5`, both null | 0 | — |
| `count = 1`, `src = null` | 1 | `Undefined Behavior: memory access failed: attempting to access 8 bytes, but got null pointer` |
| `count = 1`, `src = NonNull::dangling()` | 1 | `Undefined Behavior: memory access failed: attempting to access 8 bytes, but got 0x8[noalloc] which is a dangling pointer (it has no provenance)` |
| `count = 1`, `src == dst`, initialized | 1 | ``Undefined Behavior: `copy_nonoverlapping` called on overlapping ranges`` |
| `count = 2`, ranges offset by one element, initialized | 1 | same |
| `count = 1`, `src == dst`, **uninitialized** | 0 | — (interpreter detection gap, finding 8) |
| `count = 2`, disjoint; destination compared afterwards | 0 | — |
| `count = usize::MAX`, dangling pointers | 1 | ``Undefined Behavior: overflow computing total size of `copy_nonoverlapping` `` |

### 7. Five layers that look at the pointers, and where they disagree

Basis: documentation + source + execution. The disagreement is preserved, not
resolved.

| Layer | `src = null`, zero length | misaligned, zero length | `src = null`, non-empty |
|---|---|---|---|
| Library documentation of `ptr::copy_nonoverlapping` (`library/core/src/ptr/mod.rs:453–473`) | allowed: "`src` must be valid for reads of `count * size_of::<T>()` bytes or that number must be 0" | undefined behaviour: "even if the effectively copied size ... is `0`, the pointers must be properly aligned" | undefined behaviour |
| Library precondition in the wrapper (`ptr/mod.rs:531–547`, `ub_checks.rs:118–125`): `zero_size = count == 0 \|\| size == 0`, `maybe_is_aligned(ptr, align) && (is_zst \|\| !ptr.is_null())` | passes (native debug build: exit 0) | aborts with "unsafe precondition(s) violated: ptr::copy_nonoverlapping requires that both pointer arguments are aligned and non-null and the specified memory ranges do not overlap" (exit by `SIGABRT`) | aborts, same message |
| Interpreter (finding 6) | accepted | undefined behaviour | undefined behaviour |
| Lint `invalid_null_arguments` (`compiler/rustc_lint/src/ptr_nulls.rs:36–57, 150–200`), deny by default | **compile error** when the argument is syntactically a null pointer and the pointee is not a 1-ZST; `count` is not inspected: "calling this function with a null pointer is undefined behavior, even if the result of the function is unused" | not applicable | compile error under the same syntactic condition |
| MIR passes `CheckAlignment` / `CheckNull` | no check inserted | no check inserted | no check inserted |

Two consequences:

- A harness that records only the exit status of `miri file.rs` cannot tell the
  lint row from an interpreter verdict: both give status 1 (for the lint
  specimen the probe records `rustc_returncode` 1 and `miri_returncode` 1 with
  the same first diagnostic). The recorded
  diagnostic distinguishes them (``= note: `#[deny(invalid_null_arguments)]` on by default``
  versus `error: Undefined Behavior: ...`). The lint's message is
  broader than the documented contract for the zero-length case.
- `CheckAlignment` and `CheckNull` share `check_pointers`
  (`compiler/rustc_mir_transform/src/check_pointers.rs:43–123`), whose visitor
  returns immediately unless the visited place is indirect
  (`if !self.should_visit_place(context) || !place.is_indirect() { return; }`,
  `check_pointers.rs:180–183`). The operands of a `copy_nonoverlapping`
  statement are pointer values, not dereferences, so nothing is inserted.
  Execution with `-C opt-level=0 -C debug-assertions=on`: a body consisting of
  `core::intrinsics::copy_nonoverlapping(src, dst, n)` has 0 `assert`
  terminators after `CheckNull`, while `*p` and `*p = 1` each get 2
  ("misaligned pointer dereference: address must be a multiple of {} but is {}"
  and "null pointer dereference occurred"). Natively, the same debug build runs
  `core::intrinsics::copy_nonoverlapping(misaligned, dst, 0)` to completion
  (exit 0), whereas the wrapper aborts: the only debug-build check is the
  wrapper's precondition, and it is evaluated only when `ub_checks` is on
  (`-Zub-checks`, defaulting to `-C debug-assertions`) and never under Miri
  (`check_language_ub` is `!cfg!(miri) && intrinsics::ub_checks()`,
  `ub_checks.rs:96–108`).

### 8. Overlap detection for an uninitialized source differs between the revisions

Basis: source (both revisions) + execution (`14210df0e` only).

At `14210df0e`, `mem_copy_repeatedly` returns through its
`if init.no_bytes_init() { ... return interp_ok(()); }` fast path
(`memory.rs:1563–1573`) *before* the overlap test (`memory.rs:1581–1590`). A
`copy_nonoverlapping(p, p, 1)` on a `MaybeUninit<u64>` is accepted by Miri
(exit 0 in all three modes), although the library contract forbids overlap
regardless of initialization. At `3ef0c22cd` the overlap test is placed before
the fast path (`memory.rs:1550–1560` versus `1565–1576`) and the fast path
carries the comment "IMPORTANT: there are no more UB checks below that we would
skip here"; that revision was not executed.

### 9. Whole-crate census at `14210df0e`

Basis: execution (`support/probe_results.json`, key `zerocopy_census`).

Counting rule: one MIR dump file whose crate component is `zerocopy` is one
body; a statement or terminator is counted by the shape of its dump line
(`assume(...)`, `copy_nonoverlapping(dst = ...`, `unreachable;`,
`switchInt(...) -> ...`).

| Snapshot | bodies | `assume` stmts (bodies) | `copy_nonoverlapping` stmts (bodies) | `unreachable` terms (bodies) | `SwitchInt` terms |
|---|---|---|---|---|---|
| `Runtime(PostCleanup)` | 4,838 | 0 (0) | 0 (0) | 541 (179) | 1,145 |
| entry of the optimization pipeline (bodies that are optimized) | 4,586 | 0 (0) | 0 (0) | 512 (150) | 1,040 |
| `Runtime(Optimized)` | 4,586 | 406 (54) | 6 (6) | 780 (780) | 1,772 |

All passes dumped for an optimized body were measured before and after; the
chain is consistent (each pass's "before" equals the previous pass's "after",
and the last "after" equals the `Runtime(Optimized)` snapshot). Passes with a
non-zero effect on the three constructs:

| Pass (pipeline order) | Δ `assume` | Δ `copy_nonoverlapping` | Δ `unreachable` | Δ `SwitchInt` | running `assume` total |
|---|---|---|---|---|---|
| `LowerIntrinsics` (runtime cleanup) | 0 | 0 | +1 | 0 | 0 |
| `Inline` | +56 | +6 | +666 | +1,391 | 56 |
| `UnreachableEnumBranching` | 0 | 0 | +8 | 0 | 56 |
| `UnreachablePropagation` | +355 | 0 | 0 | −355 | 411 |
| `SimplifyCfg-after-unreachable-enum-branching` | 0 | 0 | −392 | 0 | 411 |
| `SimplifyConstCondition-after-inst-simplify` | −9 | 0 | +9 | −113 | 402 |
| `MatchBranchSimplification` | +8 | 0 | −13 | −20 | 410 |
| `SimplifyCfg-final` | −4 | 0 | −10 | −163 | 406 |

The other dumped passes (`LowerSliceLenCalls`, `InstSimplify-*`, `ForceInline`,
`RemoveZsts`, `RemoveUnneededDrops`, `ReferencePropagation`,
`ScalarReplacementOfAggregates`, `SimplifyLocals-*`, `DeadStoreElimination-*`,
`GVN`, `SsaRangePropagation`, `SingleUseConsts`,
`SimplifyConstCondition-after-const-prop`, `JumpThreading`,
`EarlyOtherwiseBranch`, `SimplifyComparisonIntegral`,
`SimplifyConstCondition-final`, `RemoveNoopLandingPads`, `CopyProp`,
`DestinationPropagation`, `AddCallGuards`, and the runtime-cleanup passes
`RemovePlaceMention` and `SimplifyCfg-pre-optimizations`) leave the `assume`,
`copy_nonoverlapping` and `unreachable` counts unchanged.

Reading the ledger:

- the 56 `assume` and 6 `copy_nonoverlapping` statements that `Inline` brings in
  come from library bodies (finding 3);
- `UnreachablePropagation` converts exactly 355 `SwitchInt` terminators into
  `assume` + `goto` (Δ `SwitchInt` = −355 = −Δ `assume`), matching the model's
  355 predicted "one surviving arm" rewrites;
- the defining right-hand side of the assumed boolean in `Runtime(Optimized)`
  MIR is `Eq(..)` for 402 statements and `Le(..)` for 4; every statement added
  by `UnreachablePropagation` is an `Eq`;
- the bodies with the most `assume` statements are the generated
  `impls-tuples-_-{impl#N}-is_safe` bodies (26, 25, 24, ... statements), i.e.
  the statements concentrate in few bodies: 54 of 4,586 optimized bodies (1.2%)
  contain at least one.

### 10. A recorded comparison run on the newer toolchain

Basis: execution, **recorded and not re-run** (`support/recorded_census_rustc_1_102_0_nightly.json`).

A per-pass census of the same kind, recorded with
`rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, LLVM 23.1.5, reports: after
`LowerIntrinsics` 4,663 bodies with 0 `assume`, 0 `copy_nonoverlapping`, 531
`unreachable`; before `UnreachablePropagation` 4,302 bodies with 65 `assume`
(38 bodies) and 4 `copy_nonoverlapping`; after `UnreachablePropagation` 420
`assume` (66 bodies) and 1,172 `unreachable`; before and after
`SimplifyLocals-final` 385 `assume` (58 bodies), 4 `copy_nonoverlapping`, 768
`unreachable`. It shows the same shape as finding 9 (0 → several hundred, with
`UnreachablePropagation` contributing 355 in both). The recording does not
embed the crate revision, feature set or flags, so the two runs are not known
to differ only in the toolchain, and their numbers must not be mixed.

### 11. Differences between the two rustc revisions

Basis: source (all 17 audited files differ textually between the revisions
except `library/core/src/ub_checks.rs`).

| Area | `14210df0e` | `3ef0c22cd` |
|---|---|---|
| `LowerIntrinsics` for `assume` / `copy_nonoverlapping` | pushes the intrinsic statement, sets `Goto`; the call's unit destination is **not** assigned | additionally pushes `destination = const ()` (`Rvalue::Use(Operand::zero_sized_constant(unit), WithRetag::Yes)`) after the intrinsic statement (`lower_intrinsics.rs:60–89, 90–115`) |
| `TerminatorKind::Goto` | `Goto { target }` | `Goto { target, loop_hint_attrs }`; passes construct it with `TerminatorKind::goto(target)` |
| pass enablement API | `is_enabled(&Session)` / `is_required()` | `policy(&PassCtx) -> PassPolicy` (`PassPolicy::optional(ctx.mir_opt_level() >= 2)` for `UnreachablePropagation`, `>= 1` for `UnreachableEnumBranching`) |
| `remove_successors_from_switch`, `variant_discriminants`, `UnreachableEnumBranching::run_pass` | — | same logic (renames only) |
| `eval_nondiverging_intrinsic`, `copy_intrinsic`, `check_and_deref_ptr` | — | same logic (`layout.align` instead of `layout.align.abi`) |
| overlap test versus uninitialized fast path in `mem_copy_repeatedly` | fast path first | overlap test first (finding 8) |
| `CheckNull` | one assert kind | distinguishes `AssertKind::NullReferenceConstructed` for borrows; still place-based |
| wrapper precondition, lint table | — | unchanged |

The first row means that at `14210df0e` a function whose tail expression is the
intrinsic call (`pub unsafe fn f(c: bool) { core::intrinsics::assume(c) }`)
returns without ever assigning `_0: ()`. A model that initializes zero-sized
locals on entry is unaffected; `Trusted.MirSemantics` at `c131b320` does so
("live `.unit` locals start inhabited by `Val.unit`",
`liveUninitSlot .unit = .live (some .unit)`).

### 12. Mechanized results

Basis: derived (kernel-checked; `support/NonDivergingIntrinsicsAndUnreachableProp.lean`,
1,634 lines, no imports, 76 theorems).

Model in one paragraph: `execAssume` returns the unchanged state when the
operand evaluates to `bool true` and undefined behaviour otherwise; `execCopy`
checks, in the interpreter's order, total size bound, alignment of `src`,
alignment of `dst`, then — only if the size is non-zero — that both ranges are
mapped and disjoint, and then copies slot by slot; `execTerm` for `SwitchInt`
takes the first arm whose value equals the discriminant's bit pattern, else
`otherwise`; `pruneSwitch` is the case table of finding 4; `collapse U` turns
"continue at a block flagged by `U`" into undefined behaviour.

| Declaration | Lines | Statement |
|---|---|---|
| `pruneSwitch_exact` | 835–1110 | If the discriminant operand reads no local at or above the first fresh temporary, the arm values are pairwise distinct and there is at least one valued arm, then `collapse U` of the original `SwitchInt` and `collapse U` of the pruned block are either both undefined behaviour or both continue at the same block with states that agree on memory and on all locals below the first fresh temporary |
| `pruneSwitch_ub_iff` | 1133–1140 | under the same hypotheses: original is undefined behaviour **iff** pruned block is |
| `doomed_reaches_ub`, `doomed_never_done` | 526–570, 593–597 | every block in the inductive closure "ends in `unreachable` / `goto` to such a block / `SwitchInt` whose successors are all such blocks" reaches undefined behaviour from every state and never returns; this justifies `collapse` |
| `unreachable_block_statements_irrelevant` | 368–370 | the statements of a block ending in `unreachable` do not affect its outcome (the pass may clear them) |
| `assume_as_switch_gadget` | 1170–1185 | for an operand that evaluates to a boolean, `switchInt(op) -> [0: u, otherwise: next]` with `u` flagged equals `assume(op)` followed by a jump to `next` |
| `assume_ok_iff` | 1144–1154 | `assume(op)` is defined iff `op` evaluates to `bool true` |
| `enumBranching_sound` | 1345–1396 | for every discriminant in the inhabited set, the rewritten switch of `UnreachableEnumBranching` has the same successor as the original |
| `enumBranching_forged_hits_unreachable` | 1401–1423 | a discriminant outside the inhabited set that has an explicit arm is sent to the unreachable block |
| `execCopy_isSome_iff` | 154–174 | the copy is defined iff the total size is within bound, both pointers are aligned, and either the size is zero or both ranges are mapped and disjoint |
| `copy_zero_count_ok_iff_aligned`, `copy_zero_count_null_ok` | 200–204, 185–187 | a zero-length copy is defined iff both pointers are aligned; in particular from and to address 0 |
| `copy_nonempty_unmapped_src_ub`, `copy_overlap_ub` | 213–228, 231–243 | a non-empty copy from an unmapped first slot (e.g. null) or between overlapping ranges is undefined behaviour |
| `copy_ok_slotwise` | 247–274 | a defined non-empty copy writes slot `src + i` to `dst + i` for all `i` below the size and changes nothing else |
| `golden_*` (10 theorems) | 1450–1513 | `pruneSwitch` / `enumBranching` reproduce the blocks rustc emitted for the specimens of findings 4 and 5 |

Sharpness counterexamples (all closed instances proved by computation):

| Declaration | Lines | What it shows |
|---|---|---|
| `ce1_switch_prune_without_assume_loses_ub_reverse_unsound` | 1521–1533 | `switchInt(_1) -> [0: flagged, 1: bb2, otherwise: bb1]` with `_1 = 0` is undefined behaviour; with the arm removed and **no** `assume` the same input continues at `otherwise`; with the `assume` rustc emits it is undefined behaviour again. Dropping the `assume` keeps the transformation a refinement but breaks the converse direction, so absence of undefined behaviour in the pruned body would no longer imply absence in the original |
| `ce2_copy_nonoverlapping_zero_count_misaligned_ub_but_null_ok`, `ce2_statement_level` | 1539–1563 | with element size 8 and alignment 8: zero-length copy from address 17 or to address 17 is undefined behaviour; from/to address 0 and between unmapped aligned addresses is defined; one element from address 0, with `src == dst`, or with ranges offset by 4 slots is undefined behaviour; one element between disjoint mapped ranges copies |
| `ce3_forged_uninhabited_enum_discriminant_hits_unreachable_ub` | 1574–1586 | for inhabited discriminants {0, 2}, the forged values 1 and 5 run ordinary code in the original switch and enter the unreachable block in the rewritten one; 0 and 2 are unaffected |
| `ce4_zero_arm_switch_drops_discriminant_read` | 1592–1596 | the zero-arm rewrite of finding 4 turns undefined behaviour (uninitialized discriminant) into a defined jump: the "at least one valued arm" hypothesis is necessary |
| `ce5_duplicate_switch_values_break_exactness` | 1602–1608 | with arms `[5: flagged, 5: bb2]` and a flagged `otherwise` the original is undefined behaviour while the pruned block assumes `_1 == 5` and continues: the distinct-values hypothesis is necessary |

`#print axioms` reports `[propext]` for 41 theorems, `[propext, Quot.sound]` for
30 and no axiom for 5 (`support/lean_axioms_all_theorems.txt`); no theorem
depends on `Classical.choice`, `sorryAx` or `Lean.ofReduceBool`. Two core
lemmas that would have introduced `Classical.choice`
(`List.filter_eq_nil_iff`, `List.mem_erase_of_ne`) are replaced in the file by
directly proved equivalents (`filter_reach_nil`, `mem_eraseVal_of_ne`).

### 13. What this means for `Trusted.MirAst` at `joshlf/anneal@c131b320`

Basis: source + derived.

- `trusted/lean/Trusted/MirAst.lean:52–54` states that the module "defines the
  trusted abstract syntax tree for post-cleanup runtime Mid-level Intermediate
  Representation (`Runtime(PostCleanup)` MIR) extracted by
  `anneal-rustc-capture`". Lines 630–662 define

  ```lean
  inductive StatementKind where
    | assign (dst : Place) (rvalue : Rvalue)
    | storageLive (localId : LocalId)
    | storageDead (localId : LocalId)
    | nop
    | unsupported
  ```

  with the documented correspondence "`.unsupported` represents all other
  `StatementKind` variants (`FakeRead`, `SetDiscriminant`, `PlaceMention`,
  `AscribeUserType`, `Coverage`, `Intrinsic`, `ConstEvalCounter`, and
  `BackwardIncompatibleDropHint`)".
- `trusted/lean/Trusted/MirSemantics.lean:1427` steps `.unsupported` to
  `.fault .unsupported`; lines 1551–1567 step `.unreachable` to
  `.fault .undefined` and evaluate `.switchInt` by first matching branch, else
  `otherwise`. `FaultKind` has exactly `undefined` and `unsupported`
  (lines 332–334), and both falsify well-formedness.
- `trusted/correspondence/Trusted/Correspondence.lean:2010–2028` maps the model's
  `.unsupported` statement to the interpreter-side statement
  `.Intrinsic (.Assume (.Copy ⟨0, Array.empty⟩))` as a **fail-closed sentinel**,
  so that the interpreter-side step routes it to the `intrinsic` hook, which is
  `fun _ _ st => (st, .error (.unsupported "Intrinsic"))` (line 2263). This is
  not a semantic treatment of `assume`.

Derived consequences:

1. On `Runtime(PostCleanup)` MIR of a crate that does not call the intrinsics
   directly, the missing constructor costs nothing: the census finds no such
   statement in 4,838 bodies.
2. On `Runtime(Optimized)` MIR, every body with an `assume` (54 bodies here)
   and every body with a `copy_nonoverlapping` (6 here) contains a statement
   that the syntax tree can only represent as `.unsupported`. For the 355
   statements produced by `UnreachablePropagation`, the rejected form is, in
   the standalone model (`pruneSwitch_ub_iff`), equivalent to the `SwitchInt` +
   `Unreachable` form it was derived from, and those two terminators are ones
   `Trusted.MirSemantics` does model.
3. Two ways to admit `assume` without changing what is provable about the
   source: (a) add one constructor `assume (op : Operand)` whose step is
   "evaluate `op`; `true` → next statement; `false` → `.fault .undefined`"
   (the same fault kind as `.unreachable`, as rustc documents); or (b) keep the
   syntax tree unchanged and re-express `assume(op)` during import as a block
   split with `switchInt(op) -> [0: U, otherwise: next]`, `U` ending in
   `unreachable` (`assume_as_switch_gadget`). Option (b) changes block
   numbering; option (a) changes the trusted syntax tree.
4. If option (a) is taken, the sentinel of
   `Correspondence.lean:2010–2028` can no longer be an `Assume` statement,
   because a real `assume` would then map to the same interpreter-side
   constructor as the fail-closed marker (derived from the two definitions; not
   tested).
5. `copy_nonoverlapping` needs pointer and memory semantics; the conditions any
   model has to reproduce are those of `execCopy_isSome_iff`, including the
   asymmetric treatment of alignment (always) and null (only for non-empty
   copies).

## Boundaries

**Not examined.**

- Targets other than `x86_64-unknown-linux-gnu`; crates other than `zerocopy`;
  feature sets other than `alloc` + `simd`; `-C opt-level` values other than 2
  for the census; incremental builds; `-Zmir-opt-level=3` and above (where
  `DataflowConstProp` and, with `-Zunsound-mir-opts`, `EnumSizeOpt` run).
- What backends do with `bx.assume` / `bx.memcpy` (whether LLVM keeps, exploits
  or drops the assumption), and any miscompilation risk downstream of MIR.
- The overlapping-copy intrinsic `copy`, `write_bytes`, `typed_swap_nonoverlapping`
  and other pointer intrinsics that remain `Call`s or lower to other constructs.
- The questions the rustc documentation itself leaves open for
  `CopyNonOverlapping` (order of operand evaluation versus dereference; typed
  versus untyped copy), and the aliasing-model side of the copy (which tags are
  read or written under Stacked or Tree Borrows). The matrix only shows that the
  verdict classes above are the same under both models.
- The part of `joshlf/anneal` that turns rustc MIR into `Trusted.MirAst` values;
  a search for `StatementKind::` over the non-Lean files under `trusted/` at
  `c131b320` returns no match, so which rustc MIR snapshot is exported, and how,
  was not determined from source.
- Execution on `3ef0c22cd`: no claim about that revision is backed by a run made
  for this report.

**Unknown.**

- The crate revision, features and flags behind the recorded 1.102 census
  (finding 10).
- Whether `invalid_null_arguments` is intended to stay broader than the
  documented zero-length contract.
- Whether the Miri acceptance of an overlapping copy of uninitialized memory at
  `14210df0e` was regarded upstream as a bug; only the code movement between
  the two revisions was observed.

**Known not to apply.**

- "A zero-length `copy_nonoverlapping` from a null pointer is undefined
  behaviour": contradicted by the library documentation, the library
  precondition, and the interpreter (findings 6 and 7).
- "`CheckNull` / `CheckAlignment` instrument `copy_nonoverlapping`":
  contradicted by source and by the dump (finding 7).
- "`UnreachablePropagation` is an exact equivalence on every `SwitchInt`": false
  for a `SwitchInt` without valued arms (finding 4, `ce4`).
- Exactness of the pruning without the distinct-values invariant (`ce5`).

**Unsupported.**

- `StatementKind::Intrinsic` in `Trusted.MirAst` at `c131b320` (finding 13).
- The mechanization does not model provenance, uninitialized bytes inside a
  mapped slot, typed copies, the overlap test's restriction to a single
  allocation, pointer-sized arithmetic overflow of `src + size`, or
  `Operand::Move` de-initialization; discriminants are natural numbers compared
  by bit pattern, without width truncation.

**Stronger conclusions the evidence does not establish.**

- `pruneSwitch_exact` is a statement about one block. Lifting it to whole
  bodies needs, in addition, that no other statement reads the fresh
  temporaries and that the post-order set computed by the pass coincides with
  the inductive closure of `Doomed`; both are argued in finding 4 and checked
  empirically by the model comparison, but neither is mechanized.
- The census does not show that every `assume` in optimized MIR originates from
  switch pruning: 56 arrive through `Inline` from library bodies and 8 through
  `MatchBranchSimplification`, and 4 of the final 406 assume a `Le` comparison.
- Agreement of the reference model with rustc on 2,431 terminators of one crate
  is not a proof that the model equals `remove_successors_from_switch`.
- Nothing here shows that admitting `assume` is *sufficient* for a verifier to
  accept optimized MIR; optimized bodies contain other constructs outside the
  fragment described in finding 13.

## Evidence

**Source, `rust-lang/rust`.** Line numbers at `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`
(and at `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` in parentheses). The first 17
files were fetched from GitHub at both revisions through the contents API on
2026-11-21; at `14210df0e` each fetched blob has the same Git blob hash as the
corresponding file of the executed toolchain's `rustc-src` / `rust-src`
components, so the lines quoted are the lines that ran.

| File | Items |
|---|---|
| `compiler/rustc_middle/src/mir/syntax.rs` | `StatementKind::Intrinsic` 432–434 (436); `NonDivergingIntrinsic` 469–492 (462–485); `struct CopyNonOverlapping` 622 (615) |
| `compiler/rustc_mir_transform/src/lower_intrinsics.rs` | `sym::unreachable` 23–25 (23); `sym::copy_nonoverlapping` 61–79 (60–89); `sym::assume` 80–92 (90–115) |
| `compiler/rustc_mir_transform/src/unreachable_prop.rs` | pass body 16–57; statement clearing 51–56 (56); `remove_successors_from_switch` 65–154 (62–151); `add_assumption` 104–116 (101); case match 135–150 (132) |
| `compiler/rustc_mir_transform/src/unreachable_enum_branching.rs` | `variant_discriminants` 51–77 (52); `run_pass` 84–171 (85); `replace_otherwise_to_unreachable` 146–147 (147) |
| `compiler/rustc_mir_transform/src/check_pointers.rs` | `check_pointers` 43–123; `visit_place` 180–228 (180) |
| `compiler/rustc_mir_transform/src/check_null.rs`, `check_alignment.rs` | `insert_null_check` 32–127 (29); `insert_alignment_check` 42 (39); both enabled by `sess.ub_checks()` |
| `compiler/rustc_mir_transform/src/lib.rs` | `run_runtime_cleanup_passes` 653–666 (682); `run_optimization_passes` 675–773 (698); `Inline` 709 (723); `UnreachableEnumBranching` 720 (734); `UnreachablePropagation` 721 (735); `MatchBranchSimplification` 746 (760); lone-`unreachable` exit 810–817 |
| `compiler/rustc_const_eval/src/interpret/step.rs` | dispatch 114 (116) |
| `compiler/rustc_const_eval/src/interpret/intrinsics.rs` | `eval_nondiverging_intrinsic` 905–929 (860–884); `copy_intrinsic` 1045–1070 (1044–1069) |
| `compiler/rustc_const_eval/src/interpret/memory.rs` | `check_and_deref_ptr` 519–534 (531); `is_ptr_misaligned` 579–624 (579); `mem_copy_repeatedly` 1486 (1473); uninitialized fast path 1563–1573 (1565–1576); overlap test 1581–1590 (1550–1560) |
| `compiler/rustc_lint/src/ptr_nulls.rs` | lint declaration 36–57 (55); argument table 160–173 (170); emission 175–200 |
| `compiler/rustc_codegen_ssa/src/mir/statement.rs` | `Assume` 70–73 (90–93); `CopyNonOverlapping` 74–96 (94) |
| `library/core/src/ptr/mod.rs` | safety documentation 453–473 (487); `copy_nonoverlapping` 530–552 (544–566) |
| `library/core/src/hint.rs` | `unreachable_unchecked` 103–112 (103); `assert_unchecked` 202–212 (202) |
| `library/core/src/intrinsics/mod.rs` | `assume` 400 (661); `copy_nonoverlapping` 3028 (3016) |
| `library/core/src/ub_checks.rs` | `check_language_ub` 96–108; `maybe_is_aligned_and_not_null` 118–125 (identical blob at both revisions) |

Read only from the executed toolchain's `rustc-src` component at `14210df0e`
(not separately fetched): `rustc_mir_transform/src/validate.rs` 346–363 and
1496–1532; `simplify_branches.rs` 53–64; `match_branches.rs` 392–409;
`large_enums.rs` 34–39 and 135–141; `inline.rs` 46–59;
`jump_threading.rs` 635–640; `ssa_range_prop.rs` 146;
`dataflow_const_prop.rs` 195–199;
`rustc_mir_build/src/builder/custom/parse/instruction.rs` 22–25;
`rustc_middle/src/mir/pretty.rs` 914–923; `rustc_session/src/session.rs`
617–622 (`mir_opt_level`) and 728–730 (`ub_checks`).

**Source, `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`.**
`trusted/lean/Trusted/MirAst.lean` 52–54, 630–662;
`trusted/lean/Trusted/MirSemantics.lean` 150–160, 332–334, 744–749, 1427,
1537–1569; `trusted/correspondence/Trusted/Correspondence.lean` 2010–2028,
2219–2270.

**Revision identities.** The five revisions in `REPORT.json` were resolved
through the GitHub commits API on 2026-11-21; `v4.34.1` of `leanprover/lean4`
resolves to `5045d0056413266e57c625dcd7c365b10e377c52`, which is also the commit
printed by `lean --version` of the binary that checked the file.

**Execution (2026-11-21, `x86_64-unknown-linux-gnu`).**

- `support/probe_nondiverging_intrinsics.py` — the probe. It embeds every
  specimen source, compiles with `-Zdump-mir=<pass names>` into a temporary
  directory, runs Miri through `miri --sysroot $(cargo miri setup --print-sysroot)`,
  and scrubs absolute paths from what it records.
- `support/probe_results.json` — its complete output: toolchain identity;
  `pass_specimens` (findings 3–5); `pointer_checks` (finding 7: MIR dump counts
  and native runs of a debug-assertions build and a release build);
  `miri_matrix` (finding 6, with each program's source text and the lint row);
  `miri_switch_pruning_differential` (11 input cases × 3 modes for the pruning
  specimens, including the zero-arm case); `zerocopy_census` (finding 9: the
  three snapshots, the full pass ledger, assumed-condition shapes, the 15 bodies
  with the most `assume` statements, and the model comparison).
- `support/recorded_census_rustc_1_102_0_nightly.json` — the recorded comparison
  run of finding 10: its toolchain identity and per-pass census are reproduced
  verbatim; nothing else from the recording is included.

For the probe run reported here the crate source was supplied with
`--zerocopy-dir` from a checkout of `907b9175fee081872ec883ca4709e6ad922f8ed0`.
Without that option the probe downloads the commit tarball from GitHub; that
download path was not exercised in the reported run.

**Mechanization (2026-11-21).**

- `support/NonDivergingIntrinsicsAndUnreachableProp.lean` — the Lean source.
- `support/lean_check_output.txt` — output of the check command given under
  Revalidation (exit status 0; 23 `#print axioms` lines).
- `support/lean_axioms_all_theorems.txt` — `#print axioms` for each of the 76
  theorems, obtained by appending one `#print axioms` line per `theorem` name to
  a copy of the file.

## Revalidation

**Is a newer rustc still creating the statements the same way?** Diff these
regions against the line ranges above; they determine every finding:

```text
compiler/rustc_mir_transform/src/unreachable_prop.rs        fn remove_successors_from_switch
compiler/rustc_mir_transform/src/unreachable_enum_branching.rs   fn run_pass, fn variant_discriminants
compiler/rustc_mir_transform/src/lower_intrinsics.rs        arms sym::assume, sym::copy_nonoverlapping
compiler/rustc_const_eval/src/interpret/intrinsics.rs       fn eval_nondiverging_intrinsic, fn copy_intrinsic
compiler/rustc_const_eval/src/interpret/memory.rs           fn check_and_deref_ptr, fn mem_copy_repeatedly
compiler/rustc_mir_transform/src/check_pointers.rs          PointerFinder::visit_place
compiler/rustc_lint/src/ptr_nulls.rs                        the (arg_indices, are_zsts_allowed) table
library/core/src/ptr/mod.rs                                 fn copy_nonoverlapping (docs and precondition)
compiler/rustc_middle/src/mir/syntax.rs                     enum NonDivergingIntrinsic (a third variant would be new)
```

**Rerun the probe** (needs a nightly toolchain with the `miri` and `rust-src`
components; five to eight minutes with the census, under twenty seconds without):

```bash
python3 support/probe_nondiverging_intrinsics.py --out fresh_results.json
python3 support/probe_nondiverging_intrinsics.py --out fresh_quick.json --skip-zerocopy
python3 support/probe_nondiverging_intrinsics.py --out fresh_results.json \
    --zerocopy-dir path/to/zerocopy-checkout/zerocopy     # offline variant
```

Discriminating fields, in decreasing order of value:

- `zerocopy_census.reference_model_vs_unreachable_propagation.disagree` must be
  absent (or 0): a disagreement means the case table of finding 4 changed;
- `zerocopy_census.ledger_chain_consistent` must be `true`; then compare
  `runtime_post_cleanup`, `runtime_optimized` and
  `passes_changing_assume_or_copy_or_unreachable` with finding 9 (numbers are
  expected to move with the toolchain; a non-zero `assume` count at
  `runtime_post_cleanup` would be a qualitative change);
- `miri_matrix.specimens.*.modes.*.returncode` against the table of finding 6;
  `copy_zero_count_null_src` flipping to 1 or
  `copy_zero_count_misaligned_src` flipping to 0 would change finding 6, and
  `copy_count1_overlap_uninitialized` is expected to flip to 1 on toolchains
  that contain the reordering of finding 8;
- `miri_matrix.compile_time_lint_row.lint_note` must still name
  `invalid_null_arguments`;
- `pointer_checks.mir_instrumentation.direct_copy_nonoverlapping.assert_terminators_after_check_null`
  must stay 0 for finding 7;
- `miri_switch_pruning_differential.cases[*]`: the only case with
  `ub_verdict_identical_across_modes == false` should be
  `up_degenerate_zero_arm_switch_uninit`.

A passing probe establishes only these observations for the toolchain it ran
on.

**Recheck the mechanization** (a Lean `v4.34.1` toolchain, no other dependency;
about ten seconds):

```bash
lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
    support/NonDivergingIntrinsicsAndUnreachableProp.lean
```

Expected: exit status 0 and the 23 lines of `support/lean_check_output.txt`,
each listing only `propext` and `Quot.sound` (or no axiom). If the case table of
`remove_successors_from_switch` changes, update `pruneCore`, re-transcribe the
`golden_*` right-hand sides from fresh dumps, and re-prove `pruneSwitch_exact`;
the `golden_*` theorems fail first and cheaply when the model and rustc drift
apart.

**Recheck the `joshlf/anneal` reading.** Look at the constructor list of
`Trusted.MirAst.StatementKind` and at the `.unsupported` clause of
`toMiriStatementForDispatch` in `Trusted/Correspondence.lean`; if `Intrinsic` is
no longer in the documented `.unsupported` list, finding 13 is superseded for
that revision.
