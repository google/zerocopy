# `rustc` `CheckPackedRef` (`E0793`), `AddMovesForPackedDrops`, Miri Alignment Undefined Behavior, `Pin` Structural Projections, and `zerocopy::Unalign<T>`

## Summary

Creating a shared (`&T`) or mutable (`&mut T`) reference to an unaligned place violates Rust's pointer/reference validity invariant and causes immediate undefined behavior (UB), even if the reference is never dereferenced and even for zero-sized types (ZSTs) with `align > 1` (`#[repr(align(4))]`). Across the examined `rustc` toolchain and upstream compiler sources (`rust-lang/rust` revisions `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` and `277240238554297f93fa9ee3c7643dfa03ccbbb4`), the safety boundary across static lints, MIR lowering, `core::pin::Pin`, dynamic Miri execution, and `google/zerocopy`'s `Unalign<T>` wrapper reduces to five coupled mechanisms:

1. **Static Borrow Rejection (`CheckPackedRef` / `place_unalignment`, `E0793`)**: During MIR linting (`compiler/rustc_mir_transform/src/check_packed_ref.rs`), `PackedRefChecker::visit_place` flags every borrow (`context.is_borrow()`) for which `rustc_const_eval::util::alignment::place_unalignment` returns `Some((adt, pack))`. Traversing projections inward-to-outward from the place end, `most_packed_projection` computes `min(adt.repr().pack)` across packed ADT field projections and halts at `ProjectionElem::Deref` (`Deref` resets packed context because a Rust reference/raw pointer indirection restores its pointee's normal ABI alignment assumption). A borrow inside a packed chain is permitted statically **if and only if** `tcx.layout_of(place.ty)` succeeds and `layout.align <= pack` (`layout.align.abi <= pack` in `14210df0e`) **and** either `layout.is_sized()` holds or `struct_tail_for_codegen(ty)` is `ty::Slice(..)` or `ty::Str`. By-value copy loads (`PlaceContext::Copy`), move operands (`PlaceContext::Move`), and raw pointer creation (`&raw const` / `&raw mut` -> `PlaceContext::RawBorrow`) bypass `CheckPackedRef` completely; built-in `#[derive(...)]` methods triggering `place_unalignment` hit `span_bug!` instead of `E0793`.
2. **MIR Drop Staging (`AddMovesForPackedDrops`)**: Running as a mandatory runtime-lowering pass (`PassPolicy::Required` in `277240238`; `is_required() == true` in `14210df0e`) immediately after `ElaborateDrops`, `AddMovesForPackedDrops` inspects every `TerminatorKind::Drop { place, .. }` using the exact same `util::place_unalignment` predicate. Whenever `place_unalignment` returns `Some(_)`, the pass inserts `StorageLive(temp); temp = move place;` (`Rvalue::Use(Operand::Move(*place), WithRetag::Yes)`), retargets `Drop` to the aligned stack local `temp`, and routes normal return through a fresh `StorageDead(temp)` block before the original `target`. Consequently, `drop_in_place::<Field>` observes an **aligned stack temporary address** (`drop_addr % align_of::<Field>() == 0`) that differs from the packed field's in-struct storage address whenever the packed field was misaligned.
3. **Incompatible Structural Pinning on Packed Structs (`PinV2OnPacked`, RFC 2349)**: Calling `drop_in_place` via a moved stack temporary relocates an over-aligned packed field prior to running its destructor, directly violating `Pin`'s address-stability invariant (`Pin` drop guarantee requires in-place destruction at the pinned address for `!Unpin` values). Accordingly, `rustc_hir_analysis::check::check_packed` rejects `#[pin_v2]` on any `repr(packed)` ADT (`diagnostics::PinV2OnPacked`), `core::pin` module docs forbid structural pin projections through `#[repr(packed)]`, and `core::pin::Pin` restricts safe construction (`Pin::new`), unwrapping (`Pin::into_inner`), mutable extraction (`Pin::get_mut`), and `DerefMut` (via sealed helper `helper::PinHelper` / `PinDerefMutHelper`) to `Target: Unpin` (`E0277` / `E0596` when blocked by `PhantomPinned`).
4. **Miri Alignment Enforcement vs. Explicit Unaligned Access**: Live `cargo +nightly miri` probes under both Stacked Borrows and Tree Borrows confirm that moving/copying packed fields and performing `&raw const` / `&raw mut` + `ptr::read_unaligned` / `ptr::write_unaligned` on a field at `(ptr as usize) % 4 == 1` executes cleanly including `AddMovesForPackedDrops` destructor staging (`exit 0`). Conversely, creating `&*raw` (`encountered an unaligned reference (required 4 byte alignment but found 1)`), dereferencing `*raw` directly (`accessing memory based on pointer with alignment 1, but alignment 4 is required`), or even creating a ZST reference `&*raw_zst` to `#[repr(align(4))] struct Align4Zst` (`required 4 byte alignment but found 1`) immediately faults as Miri UB (`exit 1`).
5. **`google/zerocopy::Unalign<T>` Soundness and Mechanized Proofs**: `zerocopy::Unalign<T>` (`#[repr(C, packed)]`, `align = 1`, `size = size_of::<T>()`) isolates misaligned storage behind a type-level wall (`dc2008d8` == `v0.8.64` `907b9175` across `wrappers.rs`, `util/mod.rs`, `util/macro_util.rs`, `pointer/ptr.rs`). Infallible `Deref`/`DerefMut` implementations exist **only** when `T: Unaligned` (`E0277` for `u32`). Arbitrary `T` is accessed by copy via `get`/`set`/`into_inner`, by panic-safe stack staging via `update` (`WriteBackOnDrop` using `ManuallyDrop<T>` + `ptr::write` in `Drop::drop` so unwinds still write back), or by runtime modulo check via `try_deref`/`try_deref_mut` (`t.addr() % mem::align_of::<T>() == 0` in `validate_aligned_to`). All four core properties are kernel-checked in Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) in `support/PackedFieldE0793PinAndUnalignSoundness.lean` (`3,317` lines, `255` local theorems, `0` unsafe recursors, `0` partial constants, and `0` non-constructive axioms).

## Applicability

This report characterizes six concrete upstream and toolchain subjects whose revisions and relationships are summarized below:

| Subject | Repository & Immutable Revision / Version | Role in Report | Scope Relation |
|---|---|---|---|
| `rustc` + `core` (`main` audit) | `rust-lang/rust` @ `277240238554297f93fa9ee3c7643dfa03ccbbb4` | Primary source for MIR lints, layout/alignment helpers, HIR pack checks, `core::pin`, `core::marker`, `core::ptr`, and `E0793` docs | Authoritative static source reference |
| `rustc` + `miri` (executed toolchain) | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, LLVM `22.1.6`, `miri 0.1.0 (14210df0e2 2026-05-31)`) | Live compiler diagnostics, `-Z dump-mir` outputs, native executables, `cargo +nightly miri` (Stacked Borrows & Tree Borrows), and local `rustlib` sources | Execution subject; diffs against `277240238` tracked explicitly below |
| `zerocopy` (`main` audit) | `google/zerocopy` @ `dc2008d87d8a4efbb391b2ef01c7fa31538d9d75` | Primary source for `Unalign<T>`, `validate_aligned_to`, `Ptr::try_into_aligned`, and macro unaligned helpers | Upstream `main` reference; examined files match `v0.8.64` byte-for-byte |
| `zerocopy` (`v0.8.64` execution) | `google/zerocopy` @ `907b9175fee081872ec883ca4709e6ad922f8ed0` (version `0.8.64`) | Compiled directly with `rustc` and executed natively and under `miri -Zmiri-tree-borrows` | Executed crate subject for `Unalign<T>` probes |
| `anneal` TCB | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Audit of trusted Lean MIR semantics (`Trusted.MirAst`, `Trusted.MirSemantics`) relative to packed moves, drop terminators, and alignment assertions | Comparison baseline for Anneal MIR subset coverage and pure `noncomputable def` discipline |
| Lean 4 kernel checker | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Independent kernel verification (`-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`) and MetaM environment/axiom inspection | Mechanization verifier for `support/PackedFieldE0793PinAndUnalignSoundness.lean` |

### Version Behavior Differences (`14210df0e` vs. `277240238` in `rust-lang/rust`, `dc2008d8` vs. `907b9175` in `google/zerocopy`)

Basis: source comparison across `14210df0e` (`rustlib`/rustc source) and `277240238` (`main`), plus byte-level file equality check between `google/zerocopy` `907b9175` and `dc2008d8`.

- **Alignment-Bound Representation (`compiler/rustc_const_eval/src/util/alignment.rs`)**: Both `14210df0e` and `277240238` implement the identical semantic predicate for `place_unalignment` and `most_packed_projection`. Only the `Layout` field projection differs cleanly due to compiler `Align`/`AbiAndPrefAlign` refactoring: `14210df0e` checks `if layout.align.abi <= pack` (`L28`), whereas `277240238` checks `if layout.align <= pack` (`L28`) because `Layout::align` itself is `rustc_abi::Align`. Note also that upstream path discovery in `277240238` places this shared helper in `compiler/rustc_const_eval/src/util/alignment.rs` (re-exported as `crate::util` inside `rustc_mir_transform`), rather than inside `compiler/rustc_mir_transform/src/`.
- **`CheckPackedRef` Visitor & Diagnostic Type (`compiler/rustc_mir_transform/src/check_packed_ref.rs`)**: Both revisions gate on `context.is_borrow() && let Some((adt, pack)) = util::place_unalignment(...)` and `span_bug!` if `tcx.is_builtin_derived(impl_def_id)`. In `14210df0e`, `run_lint` calls `checker.visit_body(body)` while updating `self.source_info` in `visit_statement` / `visit_terminator`, emitting `errors::UnalignedPackedRef`. In `277240238`, `run_lint` iterates `for (bb, data) in body.basic_blocks.iter_enumerated()`, calls `checker.visit_basic_block_data(bb, data)`, retrieves `self.body.source_info(location)` directly, and emits `diagnostics::UnalignedPackedRef`.
- **`AddMovesForPackedDrops` Policy & Terminator Fields (`compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs`)**: Both revisions transform matching `TerminatorKind::Drop` terminators into `StorageLive(temp); temp = move place; drop(temp) -> storage_dead_block` with `StorageDead(temp)` -> `goto target`. Two internal API evolutions appear: `14210df0e` constructs `ty::TypingEnv::post_analysis(tcx, body.source.def_id())`, implements `fn is_required(&self) -> bool { true }`, and preserves `async_fut` on `TerminatorKind::Drop`; `277240238` uses `body.typing_env(tcx)`, implements `fn policy(&self, _) -> PassPolicy { PassPolicy::Required }`, and drops the removed `async_fut` field (`L85`, `L103-109`).
- **`core::ptr::{read_unaligned, write_unaligned}` (`library/core/src/ptr/mod.rs`)**: In `14210df0e` (executed rustlib source), `read_unaligned` (`L1812-1824`) initializes `MaybeUninit<T>` and calls `intrinsics::copy_nonoverlapping(src as *const u8, ..., size_of::<T>())` followed by `assume_init()`, while `write_unaligned` (`L2014-2023`) uses `copy_nonoverlapping` onto `dst as *mut u8` plus `intrinsics::forget(src)`. In `277240238`, both functions cast to `#[repr(Rust, packed)] struct Unaligned<T>(T)` (`L2865`) and use `ptr::read` + `mem::transmute_neo` (`L1842-1861`) or `ptr::write(dst.cast(), Unaligned(src))` (`L2052-2065`), keeping the exact same `align = 1` memory-access semantics while simplifying `const` evaluation.
- **Edition & Miri Mode Constraints**: Empirical probes run under Rust Edition `2024` (with `zerocopy v0.8.64` compiled in its native Edition `2021`) on `x86_64-unknown-linux-gnu`. Extending `place_unalignment` MIR findings to targets or versions outside these two `rust-lang/rust` revisions requires checking the `alignment.rs`, `check_packed_ref.rs`, and `add_moves_for_packed_drops.rs` regions itemized under **Revalidation**.
- **`google/zerocopy` Revision Equivalence**: File-by-file byte comparison confirms that all four audited source files (`zerocopy/src/wrappers.rs`, `zerocopy/src/util/mod.rs`, `zerocopy/src/util/macro_util.rs`, and `zerocopy/src/pointer/ptr.rs`) are byte-for-byte identical between `google/zerocopy@907b9175fee081872ec883ca4709e6ad922f8ed0` (`v0.8.64`, executed) and `google/zerocopy@dc2008d87d8a4efbb391b2ef01c7fa31538d9d75` (`main`).

## Findings

### 1. MIR Pipeline Ordering and `CheckPackedRef` Static Boundary (`E0793`)

Basis: source (`rust-lang/rust` `277240238` and `14210df0e`) + execution (`rustc 1.98.0-nightly`).

In the MIR pipeline (`compiler/rustc_mir_transform/src/lib.rs:422` in `277240238`), `CheckPackedRef` runs as a `MirLint` immediately after MIR building (alongside borrow/lint passes prior to `SimplifyCfg::Initial`). Its visitor checks **only** places whose `PlaceContext` satisfies `context.is_borrow()`:

```rust
// compiler/rustc_mir_transform/src/check_packed_ref.rs:26-49 (277240238)
impl<'tcx> Visitor<'tcx> for PackedRefChecker<'_, 'tcx> {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if context.is_borrow()
            && let Some((adt, pack)) =
                util::place_unalignment(self.tcx, self.body, self.typing_env, *place)
        {
            let source_info = self.body.source_info(location);
            let def_id = self.body.source.instance.def_id();
            if let Some(impl_def_id) = self.tcx.trait_impl_of_assoc(def_id)
                && self.tcx.is_builtin_derived(impl_def_id)
            {
                span_bug!(source_info.span, "builtin derive created an unaligned reference");
            } else {
                self.tcx.dcx().emit_err(diagnostics::UnalignedPackedRef {
                    span: source_info.span,
                    ty_descr: adt.descr(),
                    align: pack.bytes(),
                });
            }
        }
    }
}
```

Evaluating whether a place borrow is potentially unaligned delegates unconditionally to `rustc_const_eval::util::alignment::place_unalignment` (`compiler/rustc_const_eval/src/util/alignment.rs:9-78`):

1. **Outermost-packed minimum after last `Deref` (`most_packed_projection`, `L56-78`)**: `place.iter_projections().rev().take_while(|(_base, elem)| !matches!(elem, ProjectionElem::Deref))` scans field/sub-place projections backwards from the borrowed place toward the local root, stopping immediately if a `ProjectionElem::Deref` is encountered. Along that un-dereferenced suffix, every `base` whose type is an ADT with `adt.repr().pack == Some(pack)` contributes `pack`, and `.min_by_key(|(_, align)| *align)` selects the tightest packing bound `min_pack`.
2. **Exact `Deref` reset semantics**: Because `take_while` halts at `ProjectionElem::Deref`, a borrow such as `&(*p.r).x` where `p` is `#[repr(packed)]` and `p.r : &Unpacked { x: u32 }` stops at the `Deref` on `p.r` (though note that the implicit copy/load of `p.r` itself—or taking `&p.r`—checks `(p, .field r)`). Direct execution (`a_packed_e0793_and_acceptance_boundary.deref_reset_vs_direct_ref_borrow` in `support/probe_results.json`) confirms `&(*p.r).x` compiles cleanly (`exit 0`, reading `p.r` by unaligned copy and dereferencing an aligned `&Unpacked`), whereas `&p.r` emits `E0793`.
3. **Exact acceptance condition (`place_unalignment`, `L24-49`)**: Let `ty = place.ty(local_decls, tcx).ty`. The place is considered properly aligned (returning `None`) if and only if `tcx.layout_of(typing_env.as_query_input(ty))` yields `Ok(layout)` satisfying:
   - `layout.align <= pack` (`277240238`) / `layout.align.abi <= pack` (`14210df0e`), **and**
   - `layout.is_sized() || matches!(unsized_tail().kind(), ty::Slice(..) | ty::Str)`.
   Otherwise—including if `layout_of` fails (e.g., due to unnormalized/generic/monomorphization unknowns), if `layout.align > pack`, or if the tail is `dyn Trait` or an opaque foreign type—`place_unalignment` conservatively returns `Some((descr, pack))`.

Notice the deliberate **unsized-tail asymmetry**: for `#[repr(C, packed)] struct S { tag: u8, tail: [u8] }`, `layout_of([u8])` has alignment `1 <= 1` and `struct_tail_for_codegen([u8]).kind()` matches `ty::Slice(_)`, so `&s.tail` is accepted statically; conversely, for `tail: [u32]`, `layout.align = 4 > pack = 1`, triggering `E0793` (`(&s.tail).len()` rejected at line `50` in `rejected_e0793`). Similarly, for `#[repr(C, packed(1))] struct UnsizedTail { ... }` with `dyn core::fmt::Debug`, `layout.is_sized()` is `false` and the tail is `ty::Dynamic`, so it fails `place_unalignment` conservatively regardless of field alignment.

#### Observed `CheckPackedRef` Static Boundary Matrix

| Form / Construct | Effective `align` vs. `min_pack` | MIR `PlaceContext` / Mechanism | `rustc 1.98.0-nightly` Verdict | Preserved Evidence |
|---|---|---|---|---|
| `&p1.b_u32` (`packed(1)`) | `4 > 1` (`sized`) | Borrow (`PlaceContext::Borrow`) | `E0793` (`this struct is 1-byte aligned`) | `a_packed_e0793...rejected_e0793` |
| `&p2.c_u32` (`packed(2)`) | `4 > 2` (`sized`) | Borrow (`PlaceContext::Borrow`) | `E0793` (`this struct is at most 2-byte aligned`) | `a_packed_e0793...rejected_e0793` |
| `&p4.c_u64` (`packed(4)`) | `8 > 4` (`sized`) | Borrow (`PlaceContext::Borrow`) | `E0793` (`this struct is at most 4-byte aligned`) | `a_packed_e0793...rejected_e0793` |
| `&nested.inner.x` (`packed(2)` wrapping `packed(4)`, `x: u32`) | `4 > min(2, 4) = 2` | `most_packed_projection` takes minimum `2` | `E0793` | `a_packed_e0793...rejected_e0793` |
| `(&slice_u32_tail.tail).len()` (`[u32]` in `packed(1)`) | `4 > 1` (`Slice`) | Tail `Slice`, alignment exceeds `1` | `E0793` | `a_packed_e0793...rejected_e0793` |
| `format!("{}", p1.b_u32)` / `fn_taking_ref(&p1.b_u32)` | `4 > 1` | Implicit borrow in macro/arg | `E0793` | `a_packed_e0793...rejected_e0793` |
| `unsafe { &u.b }` (`#[repr(C, packed)] union`, `u32`) | `4 > 1` | `unsafe` block does not waive `E0793` | `E0793` | `a_packed_e0793...rejected_e0793` |
| `&p1.b_u32 as *const u32` | `4 > 1` | Borrow coerced to raw pointer still starts with `&` | `E0793` | `a_packed_e0793...rejected_e0793` |
| `&p1.a_u8`, `&p1.arr_u8` (`[u8; 3]`), `&p2.b_u16`, `&p4.b_u32` | `align <= pack` (`1<=1`, `2<=2`, `4<=4`) | `place_unalignment` returns `None` | Accepted (`0`, stdout `RA=7 RARR=4 RB2=0x4242 RB4=0xcafebabe`) | `a_packed_e0793...accepted_boundary` |
| `&slice_u8_tail.tail` (`[u8]` in `packed(1)`) | `1 <= 1`, `unsized_tail == Slice` | Accepted exception in `alignment.rs:29-30` | Accepted (`0`, `TAIL_LEN=3`) | `a_packed_e0793...accepted_boundary` |
| `&(*p1.r).x` (`p1` `packed(1)`, `r: &'static Unpacked`) | Stopped at `Deref` (`r` loaded by unaligned copy) | `take_while(!Deref)` resets `most_packed` | Accepted (`0`, `DEREF=0x778899aa`) | `a_packed_e0793...accepted_boundary` |
| `let x = p1.b_u32;`, `{ p1.b_u32 }` | `4 > 1` | `PlaceContext::Copy` / `Move` (not borrow) | Accepted (`0`, `COPY=0x12345678 BRACE=0x12345678`) | `a_packed_e0793...accepted_boundary` |
| `&raw const p1.b_u32` + `read_unaligned`, `&raw mut` + `write_unaligned` | `4 > 1` | `PlaceContext::RawBorrow` (not borrow) | Accepted (`0`, `RAW_BEFORE=0x12345678 RAW_AFTER=0x87654321`) | `a_packed_e0793...accepted_boundary` |

### 2. `AddMovesForPackedDrops` MIR Transformation and Address Relocation

Basis: source (`add_moves_for_packed_drops.rs`, `rustc_mir_transform/src/lib.rs`) + execution (`rustc -Z dump-mir=AddMovesForPackedDrops`).

Unlike `CheckPackedRef` (which only lints borrows), `drop(_1.1)` requires passing an `&mut DropType` to `Drop::drop(&mut self)`. Creating `&mut` directly into a packed field would commit immediate reference-alignment UB whenever `align_of::<DropType>() > pack`. Consequently, `AddMovesForPackedDrops` runs as a **required** pass during runtime MIR lowering (`compiler/rustc_mir_transform/src/lib.rs:665-674`), **after** `ElaborateDrops` has expanded composite struct drops into individual field `TerminatorKind::Drop` terminators:

```rust
// compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:90-110 (277240238)
let ty = place.ty(body, tcx).ty;
let temp = patch.new_temp(ty, source_info.span);
let storage_dead_block = patch.new_block(BasicBlockData::new_stmts(
    vec![Statement::new(source_info, StatementKind::StorageDead(temp))],
    Terminator { source_info, kind: TerminatorKind::goto(target) },
    is_cleanup,
));
patch.add_statement(loc, StatementKind::StorageLive(temp));
patch.add_assign(loc, Place::from(temp), Rvalue::Use(Operand::Move(*place), WithRetag::Yes));
patch.patch_terminator(
    loc.block,
    TerminatorKind::Drop { place: Place::from(temp), target: storage_dead_block, unwind, replace, drop },
);
```

Live MIR dumps captured from `rustc 1.98.0-nightly` confirm the exact syntactic differential between `packed(1)` and `packed(4)` for a field `DropCounted(u32)` (`align = 4`):

- **Unpacked / insufficiently-packed drop (`Packed4Drop`, `align = 4 <= pack = 4`)**: `place_unalignment` returns `None`, leaving `mir_probe.reassign_packed4_drop` byte-identical across `.before.mir` and `.after.mir`: `drop((_1.1: DropCounted)) -> [return: bb1, unwind: bb2];` (`59` MIR lines both before and after).
- **Over-aligned packed drop (`Packed1Drop`, `align = 4 > pack = 1`)**: `place_unalignment` returns `Some((Packed1Drop, Align(1)))`. Before the pass (`59` lines), `bb0` ends with `drop((_1.1: DropCounted)) -> [return: bb1, unwind: bb2];`. After `AddMovesForPackedDrops` (`67` lines), `bb0` becomes:
  ```mir
  bb0: {
      StorageLive(_2);
      _2 = DropCounted(const 7_u32);
      StorageLive(_7);
      _7 = move (_1.1: DropCounted);
      drop(_7) -> [return: bb8, unwind: bb2];
  }
  ...
  bb8: {
      StorageDead(_7);
      goto -> bb1;
  }
  ```
- **Observed Runtime Relocation**: Under both native execution (`SUM1=8 SUM4=11 DROPS=67 FIELD_MOD4=1 DROP_MOD4=0 RELOCATED=true`) and Miri Tree Borrows (`FIELD_MOD4=1 DROP_MOD4=0 ADDR_CHANGED=true`), when `Packed1Drop` sits inside an aligned holder such that its `Drop` field starts at `addr % 4 == 1`, `Drop::drop` observes `&mut self` at an aligned stack temporary (`addr % 4 == 0`, distinct address from `&raw const holder.p.field`).
- **Connection to `joshlf/anneal` (`c131b320e`)**: In `trusted/lean/Trusted/MirSemantics.lean:949-976`, `evalOperandToSlot` models `.move place` by returning `optVal` and resetting `locals[place.localId]` to `liveUninitSlot ty` (`deinitMovedPlace = true`), while `MirAst.lean:738` models `AssertKind.misalignedPtrDeref` and `MirSemantics.lean:578-580` records `Allocation.alignLog2`. However, `joshlf/anneal` at `c131b320e` currently lowers any projected `.copy`/`.move` place (`!place.projection.isEmpty` at `MirSemantics.lean:953, 962`), any retagging `Rvalue::Use(_, WithRetag::Yes)` on reference/box-containing types (`MirAst.lean:596-597`), and any `TerminatorKind::Drop` (`MirAst.lean:782-795`) **fail-closed** to `.unsupported`. Supporting packed-drop lowering inside Anneal therefore depends simultaneously on projected places, `Drop`, `WithRetag::Yes` retagging semantics, and packed ADT field layout metadata.

### 3. Dynamic Alignment Semantics Under Miri (Stacked Borrows and Tree Borrows)

Basis: execution (`cargo +nightly miri`, `miri 0.1.0 (14210df0e2 2026-05-31)`).

Compiler lints cannot guard raw-pointer dereferences (`*raw` or `&*raw`). Live Miri experiments placing packed buffers at odd addresses inside `#[repr(C, align(4))]` holder structs (verified with runtime `assert_eq!((raw as usize) % 4, 1)`) establish four sharp runtime laws identically under Stacked Borrows (`MIRIFLAGS=""`) and Tree Borrows (`MIRIFLAGS="-Zmiri-tree-borrows"`):

1. **Unaligned raw R/W + packed drop passes Miri**: Initializing fields via `&raw mut`, reading via `ptr::read_unaligned`, overwriting via `ptr::write_unaligned`, and dropping packed `Drop` values through `AddMovesForPackedDrops` completes cleanly (`MIRI_PACKED_SAFE_OK mod4=1 v1=0x12345678 v2=0xcafebabe drops=14`, `exit 0` under both Stacked Borrows and Tree Borrows).
2. **Constructing an unaligned reference `&*raw` faults immediately**: Even without reading or writing through the resulting `&u32`, `let bad_ref: &u32 = unsafe { &*raw };` aborts (`exit 1`) with:
   `error: Undefined Behavior: constructing invalid value of type &u32: encountered an unaligned reference (required 4 byte alignment but found 1)`.
3. **Aligned raw dereference `*raw` without `read_unaligned` faults immediately**: `let _bad_load: u32 = unsafe { *raw };` does not construct `&u32`, yet still aborts (`exit 1`) because non-unaligned raw loads/stores require pointee alignment:
   `error: Undefined Behavior: accessing memory based on pointer with alignment 1, but alignment 4 is required`.
4. **Zero-sized types (ZSTs) still require reference alignment (`&Align4Zst`)**: On `#[repr(align(4))] struct Align4Zst;` inside a `packed(1)` struct at `(raw_zst as usize) % 4 == 1`, `let _bad_zst_ref: &Align4Zst = unsafe { &*raw_zst };` aborts (`exit 1`) with:
   `error: Undefined Behavior: constructing invalid value of type &Align4Zst: encountered an unaligned reference (required 4 byte alignment but found 1)`.
   Although reading/writing zero bytes accesses zero memory, constructing a Rust reference carries the type's ABI alignment validity invariant even when `size_of::<T>() == 0`.

### 4. `Pin<Ptr>`, `Unpin`, `PhantomPinned`, Structural Projections, and Packed-Drop Incompatibility

Basis: normative (`core::pin` module specification in `pin.rs`), source (`library/core/src/{pin.rs, marker.rs}`, `compiler/rustc_hir_analysis/src/check/check.rs`), execution (`rustc` + `miri -Zmiri-tree-borrows`).

`Pin<Ptr>` (`#[repr(transparent)] #[fundamental]`, `pin.rs:1087-1093`) is an encapsulation wrapper over pointer `Ptr` enforcing two invariants for `!Unpin` pointees (`library/core/src/pin.rs:594-860`):

- **Address-stability invariant**: Once constructed around a `!Unpin` target `T` (unless moved out solely to be dropped as an unpinned value — which is forbidden once pinned), `T` remains at the exact memory address `origAddr` until `Drop::drop` finishes (or permanently if leaked via `mem::forget`). Note Rust's leak-amplification consequence: leaking `Pin<&mut T>` or `Pin<Box<T>>` does **not** release the address-stability obligation on `T` if intrusive waitlists or self-pointers exist — stack pinning must run `Drop::drop` before deallocating storage!
- **Drop guarantee (`Drop::drop` before storage reuse/free)**: Storage holding a pinned `!Unpin` `T` must not be deallocated, overwritten, or reused unless `T::drop` has executed cleanly at `origAddr` (hence `Drop` implementations on pinned containers must also clear self-references/intrusive waiter nodes in `drop`).
- **Auto-trait opt-out via `PhantomPinned` (`marker.rs:1015-1038`)**: `pub auto trait Unpin {}` (`#[lang = "unpin"]`) implements `Unpin` structurally for every ADT whose fields are `Unpin`. `pub struct PhantomPinned;` carries `impl !Unpin for PhantomPinned {}` (`L1031`, plus unstable `impl !UnsafeUnpin for PhantomPinned {}` at `L1038`). Any struct containing `PhantomPinned` is `!Unpin`, triggering safe API barriers in `core::pin`:
  - `Pin::new(pointer)` and `Pin::into_inner(pin)` live inside `impl<Ptr: Deref<Target: Unpin>> Pin<Ptr>` (`pin.rs:1159-1212`), rejecting `!Unpin` targets with `E0277` (executed probe diagnostic: ``error[E0277]: `PhantomPinned` cannot be unpinned``).
  - `Pin::get_mut(self)` lives inside `impl<'a, T: ?Sized> Pin<&'a mut T> where T: Unpin` (`pin.rs:1600-1605`), also rejecting `!Unpin` with `E0277`.
  - `DerefMut` on `Pin<Ptr>` (`pin.rs:1746-1759`) delegates to sealed private module `helper::PinHelper<Ptr>: helper::PinDerefMutHelper` (`L1716-1741`), which requires `Ptr::Target: Unpin`. Because `PinHelper` is unexported and non-`#[fundamental]`, orphan rules simultaneously forbid downstream crates from implementing `DerefMut for Pin<&_>` directly (`issue #85099`) and yield `E0596` (``cannot borrow data in dereference of `Pin<&mut PinnedState>` as mutable``) when attempting `&mut *p`.

#### Structural vs. Non-Structural Pin Projection Rules (RFC 2349 & `core::pin` Docs)

When projecting a pinned `&mut Outer` via `unsafe { Pin::map_unchecked_mut }` or `Pin::get_unchecked_mut`, every field `f` falls into a strict binary partition governed by four mandatory consistency obligations:

1. **`Unpin` consistency**: `impl Unpin for Outer` may hold **only if** every structurally pinned field is `Unpin` (`Pin<Ptr>` for an `Unpin` struct permits safe `DerefMut` swaps `core::mem::swap(&mut *p1, &mut *p2)`, which relocates `Outer` and every field).
2. **`Drop` consistency**: `Outer::drop(&mut self)` takes `&mut Outer` (not `Pin<&mut Outer>`), so `Drop` must treat every structurally pinned field as still pinned (`#[repr(packed)]` violates this automatically via compiler-inserted `AddMovesForPackedDrops`!).
3. **Destructor guarantee across leaks**: Calling `core::mem::forget(pinned_outer)` cannot corrupt `Outer`'s pinning invariants (stack-allocated `pin!` keeps storage alive until scope exit where `drop` runs; heap-allocated `Box::pin` leaks the heap allocation permanently rather than reusing un-dropped memory).
4. **No mixed structural + non-structural projection**: A single field `f` cannot expose BOTH `Pin<&mut Field>` (structural) and `&mut Field` (non-structural `core::mem::swap`), because moving via `&mut Field` relocates `f` while structural borrowers assume `f.addr == f.origAddr`.

This structural rule explains `check_packed` in `compiler/rustc_hir_analysis/src/check/check.rs:1671-1681`:
```rust
if repr.packed() {
    // `#[pin_v2]` on a packed type is unsound: drop glue for a packed type moves an
    // over-aligned field to an aligned location before running its destructor, which would
    // move a structurally pinned field out from under a `Pin<&mut _>` that was handed out.
    if def.is_pin_project() {
        tcx.dcx().emit_err(diagnostics::PinV2OnPacked { ... });
    }
```
Notice the crucial distinction confirmed empirically:
- Even **constructing `Pin::new_unchecked(&mut packed_val)` and invoking `AddMovesForPackedDrops`** (documented in `probe_results.json` under `packed_drop_relocation_breaks_address_stability_miri`, `stdout: FIELD_MOD4=1 DROP_MOD4=0 ADDR_CHANGED=true`) demonstrates the exact hazard physically under Miri Tree Borrows: the field lives at `mod 4 == 1`, yet `Drop::drop` runs at `mod 4 == 0` with `addr != origAddr`.

### 5. `google/zerocopy::Unalign<T>` Design and Soundness

Basis: source (`google/zerocopy` `dc2008d8` == `907b9175` across `wrappers.rs`, `util/mod.rs`, `util/macro_util.rs`) + execution (`rustc` + `cargo +nightly miri -Zmiri-tree-borrows` against real `zerocopy v0.8.64`).

`zerocopy::Unalign<T>` (`zerocopy/src/wrappers.rs:115-421`) eliminates the `E0793` / Miri alignment trap by wrapping `T` in a `1`-byte-aligned transparent-layout container:

```rust
// zerocopy/src/wrappers.rs:115-118 (dc2008d8 == 907b9175)
#[derive(Default, Copy)]
#[cfg_attr(any(feature = "derive", test), derive(Immutable, FromBytes, IntoBytes, Unaligned))]
#[repr(C, packed)]
pub struct Unalign<T>(T);
```

Because `Unalign<T>` has `align_of::<Unalign<T>>() == 1`, `size_of::<Unalign<T>>() == size_of::<T>()`, and single field `.0` at offset `0`, references `&Unalign<T>` and `&mut Unalign<T>` are valid at **every** byte address (`addr % 1 == 0`) and implement `zerocopy::Unaligned` unconditionally for any `T` (`wrappers.rs:150`). Key safety invariants per method:

| Method / Impl | Source (`wrappers.rs`) | Mechanism & Invariant | Observed Probe Result (`v0.8.64`) |
|---|---|---|---|
| `new(val: T)` / `get(&self)` / `set(&mut self, t: T)` / `into_inner(self)` | `L174, L401-404, L319-321, L180-191` | Copy/move via packed field (`let Unalign(val) = *self; val`) or `transmute_unchecked` | `ZC_SIZE=4 ZC_ALIGN=1 GET=0xdeadbeef SET=0x11223344` |
| `try_deref(&self)` / `try_deref_mut(&mut self)` | `L202-228` -> `util/mod.rs:127-139` | Converts `&Self` to `Ptr`, transmutes to `T`, calls `try_into_aligned()` (`t.addr() % mem::align_of::<U>() == 0`) | Misaligned (`MIS_MOD4=1`): `MIS_DEREF=false MIS_DEREF_MUT=false`; aligned (`AL_MOD4=0`): `AL_DEREF=0xcafebabe` |
| `update<O, F>(&mut self, f: F)` | `L339-395` | Fast-path if `align_of::<T>() == 1` (`deref_mut_unchecked`); otherwise reads `T` via `ptr::read(self).into_inner()` into stack `WriteBackOnDrop { copy: ManuallyDrop<T>, slf: *mut Unalign<T> }`, passes aligned `&mut copy` to `f`, writes back via `ptr::write(self.slf, Unalign::new(copy))` in `Drop::drop` | Normal: `MIS_GET=0x1020304 AFTER_UPDATE=0x1020305`; unwinding panic inside `f`: `catch_unwind` still observes `AFTER_UNWIND=0x55667788` (no leaked/double-dropped value!) |
| `Deref` / `DerefMut` | `L407-421` | `impl<T: Unaligned> Deref for Unalign<T>` via `bikeshed_recall_aligned()` | Fails with `E0277: the trait bound u32: zerocopy::Unaligned is not satisfied` on `&Unalign<u32>`; succeeds (`UNALIGNED_DEREF=1`) for `Unalign<u8>` / `Unalign<[u8; 4]>` |
| `deref_unchecked` / `deref_mut_unchecked` | `L239-269` | Caller-discharged safety precondition `self` satisfies `align_of::<T>()` | Unsafe bypass checked by caller (not called unchecked in safe probes) |
| Documentation anomaly (`L240`) | `L240` | Comment reads ``// SAFETY: `Unalign<T>` is `repr(transparent)` ``, even though `Unalign<T>` is actually `#[repr(C, packed)]` (`L117`) | Soundness still holds because `#[repr(C, packed)]` single field `.0` is at offset `0` with identical size/bit-validity and caller asserts alignment (`L237`); preserved here as source discrepancy without silent erasure |

Running the complete `zerocopy::Unalign<T>` probe (covering `try_deref` misaligned & aligned, `get`/`set`/`into_inner`, `update` across normal return & panic unwind, `[u8; 4]` aligned cast inside misaligned buffer, and `Unaligned` `Deref`) passes under `cargo +nightly miri` with `-Zmiri-tree-borrows` (`MIRI_ZEROCOPY_UNALIGN_OK`, `exit 0`).

### 6. Kernel-Checked Lean `v4.34.1` Formalization (`PackedFieldE0793PinAndUnalignSoundness.lean`)

Basis: source + execution (`leanprover/lean4` `v4.34.1`, `5045d0056413266e57c625dcd7c365b10e377c52`).

`support/PackedFieldE0793PinAndUnalignSoundness.lean` (`3,317` lines, `154,698` bytes, `sha256: dc59211c60961c241d46336e8f568fea5b36bf1807824e9ab69ee1a52697ff5b`) formalizes all four pillars strictly from `prelude` + `Init.*` modules using explicit `noncomputable def` declarations everywhere (`badRec=0`, `badPartial=0`, `badAxiom=0`, `localThms=255`, `localConsts=831`):

- **Theorem 1 (`checkPackedRef_alignment_safety`)**: Given `PlaceAlignedWF mem p` (live, typed base slot aligned to `slotTy.abiAlignExp`, `ProjChainAligned` step alignment, and `DerefAbiWellFormed` restoring ABI alignment at every `.deref`), `ProjChainLayoutWF p.base.baseTy p.projections` (`fieldOffsetAlignExp curTy fTy <= curTy.abiAlignExp`), and `checkPackedRefAbi .borrow p = .ok`, there exists `finalAddr : Nat` such that `evalPlaceAddr mem p = some finalAddr`, `IsAlignedExp finalAddr p.ty.abiAlignExp` (`finalAddr % 2 ^ p.ty.abiAlignExp = 0`), and `miriCheckRefAbi finalAddr p.ty = .ok`. Companion corollaries `rawPtr_and_copyLoad_never_e0793`, `deref_resets_mostPacked`, `e0793_rejects_pack1_u32_and_miri_catches`, `e0793_rejects_nested_pack2_pack4_u32`, `checkPackedRef_accepts_pack2_u16`, and `checkPackedRef_slice_tail_boundary` mechanize the exact compiler acceptance frontier.
- **Theorem 2 (`addMovesForPackedDrops_staging_soundness`)**: Given `PlaceAlignedWF mem p`, `ProjChainLayoutWF`, and `DropSourceLiveInit mem p`, executing `addMovesForPackedDropsTransform tmpId p` never returns `.ubUnalignedDropRef`, evaluates to `.ok finalMem valAtPlace dropAddr` with `IsAlignedExp dropAddr p.ty.abiAlignExp` (`alignUpToExp_aligned`), marks the source slot deinitialized, and relocates `dropAddr != srcAddr` whenever `¬ IsAlignedExp srcAddr p.ty.abiAlignExp` (`packed_drop_relocates_address` + concrete `addMovesForPackedDrops_pack1_vs_pack4`).
- **Theorem 3 (`unalign_try_deref_soundness_ok`, `unalign_try_deref_fail_closed`, `unalign_deref_unaligned_always_safe`, `unalign_update_stages_and_writes_back`)**: Proves `Unalign<T>::try_deref` yields `.ok` **only if** `IsAlignedExp refAddr inner.abiAlignExp` and `miriCheckRefAbi refAddr inner = .ok`, fails closed with `.err (.misaligned inner.abiAlignExp)` when unaligned, succeeds unconditionally when `T: Unaligned` (`abiAlignExp = 0`, `unaligned = true`), and `update` runs its user closure on an aligned stack temporary `tmpAddr` while writing `f s.payloadVal` back into `slotId`.
- **Theorem 4 (`pin_step_preserves_invariants`, `pin_trace_preserves_invariants`, `pin_unpin_rejects_phantom_pinned`) + Necessity Counterexamples**: Defines an operational `PinHeap` / `PinOp` state machine (`pinNewSafe`, `pinNewUnchecked`, `pinGetMutSafe`, `pinIntoInnerSafe`, `pinDerefMutSwapSafe`, `projectStructural`, `projectNonStructural`, `registerSelfPtr`, `registerWaiter`, `dropInPlace`, `freeAfterDrop`, `memForgetLeak`) and proves every valid step and arbitrary trace `List PinOp` preserves `PinSystemInv` = `(∀ o, PinObjStructWellFormed o) ∧ PinAddrStabilityInv h ∧ PinDropGuaranteeInv h ∧ PinPtrValidityInv h`. Four explicit necessity counterexamples prove that dropping any side-condition breaks soundness:
  1. `pin_counterexample_impl_unpin_breaks_selfref` (`Unpin` impl on self-referential struct allows `DerefMut` swap to relocate the object out from under `selfPtr?`);
  2. `pin_counterexample_mixed_projection_breaks_addr_stability` (non-structural move on a pinned `!Unpin` field violates `PinAddrStabilityInv`);
  3. `pin_counterexample_skip_drop_breaks_drop_guarantee` (freeing pinned storage with `wasDropped = false` breaks `PinDropGuaranteeInv`);
  4. `pin_counterexample_packed_drop_breaks_addr_stability` (coupling `AddMovesForPackedDrops` on `packed(1)` `Drop` field at `addr = 5` stages the drop at stack temp `tmpAddr = 8 != 5`, directly explaining `PinV2OnPacked`).

## Boundaries

The negative space below prevents over-generalizing observed results beyond what primary sources, empirical probes, and Lean proofs establish:

- **Known not to apply (`UnsafePinned`, `rustc` `#[pin_v2]` lowering beyond `check_packed`)**: `PhantomPinned` is explicitly documented as a legacy hack acting as `!Unpin` (`marker.rs:1021-1024`), whereas nightly `UnsafePinned<T>` opts out of `noalias` aliasing assumptions in LLVM (`marker.rs:932`). Our empirical `Pin` probes tested `PhantomPinned` under Edition `2024` and audited `check_packed`'s rejection of `#[pin_v2]` on packed types (`check.rs:1675-1681`), rather than end-to-end execution of unstable `#[pin_v2]` lowering on non-packed types (**not examined**).
- **Known not to apply (MIR `BorrowCheck` vs. `CheckPackedRef` for non-ADT raw derefs)**: `CheckPackedRef` checks only borrows of places with a packed ADT prefix prior to the last `Deref`. Taking `&*raw` inside `unsafe` where `raw : *const u32` was already detached from the packed projection compiles cleanly (passing `CheckPackedRef`) and fails only at runtime under Miri (`encountered an unaligned reference`) or UB under optimization.
- **Known not to apply (Lean model scope)**: `support/PackedFieldE0793PinAndUnalignSoundness.lean` formalizes a dedicated structural/operational model of power-of-two `place_unalignment`, `AddMovesForPackedDrops`, `Unalign<T>`, and the `PinHeap` projection/drop state machine inside `Init.*`. It is **not** connected directly by a machine-checked refinement proof to upstream `rustc_const_eval` Rust code or `joshlf/anneal@c131b320e`'s `Trusted.MirSemantics` AST/machine (note `joshlf/anneal` currently returns `.unsupported` for non-empty operand places, `TerminatorKind::Drop`, and `WithRetag::Yes` reference retagging — **unsupported** in $M_{\text{anneal}}$ at `c131b320e`).
- **Not examined (`#[repr(packed)]` enum discriminants / `MaybeUninit::uninit()` drop elaboration / non-`x86_64` ABIs)**: All live `rustc` and `Miri` executions ran on `x86_64-unknown-linux-gnu`. While `alignment.rs` logic is target-independent (driven by `tcx.layout_of` and `adt.repr().pack`), packed enum discriminant placement (`discriminant_for_variant`) and target-specific ABI edge cases (e.g., over-aligned ABI types on embedded targets or Windows LLP64 vs. SysV LP64) were **not examined**.
- **Not examined (Rust `unsafe impl !Unpin` interaction with `zerocopy::Unaligned` on compound structs)**: `zerocopy` probes tested `u32`, `u8`, `[u8; 4]`, `Cell<u32>`, and unwind safety of `Unalign::update`; interaction between `Unalign<T>` and `!Unpin` self-referential fields was **not examined** empirically (by Theorem 4 `Counterexample 4` + `#[repr(C, packed)]`, structurally pinning fields inside `Unalign<T>` with non-trivial `Drop` fails the drop/move stability contract).
- **Unknown (future stabilization of `UnsafeUnpin` and `pin_v2`)**: Upstream `rustc` and `core::marker` carry active `#[unstable]` gates for `UnsafeUnpin` (`issue #125735`) and `#[pin_v2]` (`PinV2OnPacked`); whether future `rustc` revisions relax or reshape `PinDerefMutHelper` / `UnsafePinned` rules across packed boundaries cannot be extrapolated beyond `277240238`.

## Evidence

All primary-source citations, live compiler/Miri artifacts, and mechanized proofs are preserved immutably or packaged inside `support/`:

### 1. Upstream Primary Source Anchors

- **`rust-lang/rust` @ `277240238554297f93fa9ee3c7643dfa03ccbbb4` (`main`)**:
  - `compiler/rustc_mir_transform/src/check_packed_ref.rs:8-50` (`CheckPackedRef::run_lint`, `PackedRefChecker::visit_place`, `span_bug!` on builtin derives, `diagnostics::UnalignedPackedRef`).
  - `compiler/rustc_const_eval/src/util/alignment.rs:9-78` (`place_unalignment`, `layout.align <= pack`, `layout.is_sized() || matches!(unsized_tail().kind(), ty::Slice(..) | ty::Str)`, `most_packed_projection`, `take_while` stopping at `ProjectionElem::Deref`).
  - `compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:38-111` (`AddMovesForPackedDrops`, `PassPolicy::Required`, `add_move_for_packed_drop` inserting `StorageLive`, `Rvalue::Use(Operand::Move(*place), WithRetag::Yes)`, retargeted `TerminatorKind::Drop`, and `StorageDead` block).
  - `compiler/rustc_mir_transform/src/lib.rs:422, 665-674` (lint pass ordering for `CheckPackedRef`; runtime-lowering ordering for `ElaborateDrops` then `AddMovesForPackedDrops`).
  - `compiler/rustc_hir_analysis/src/check/check.rs:1668-1754` (`check_packed`, `diagnostics::PinV2OnPacked`, `E0634`, `E0587`, `ALIGNED_FIELDS_IN_PACKED`).
  - `compiler/rustc_error_codes/src/error_codes/E0793.md:1-96` (normative `E0793` diagnostic documentation covering copy workaround, `addr_of!` + `read_unaligned`, and packed unions).
  - `library/core/src/pin.rs:594-860, 1087-1213, 1538-1765` (RFC 2349 structural pinning contract explicitly excluding `#[repr(packed)]` at `L630-633, L807`; `Pin::new`, `Pin::into_inner`, `Pin::get_mut`, `Pin::get_unchecked_mut`, `map_unchecked`, `map_unchecked_mut`, `helper::PinHelper` / `PinDerefMutHelper`).
  - `library/core/src/marker.rs:929-1045` (`UnsafeUnpin`, `Unpin`, `PhantomPinned`, negative impls `!Unpin` and `!UnsafeUnpin`).
  - `library/core/src/ptr/mod.rs:558-580, 1842-1861, 2052-2065, 2865` (`copy_nonoverlapping` alignment requirement, `read_unaligned`, `write_unaligned` via `#[repr(Rust, packed)] struct Unaligned<T>(T)` and `mem::transmute_neo`).
- **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`)**:
  - `compiler/rustc_const_eval/src/util/alignment.rs:9-78` (`layout.align.abi <= pack` at `L28`).
  - `compiler/rustc_mir_transform/src/check_packed_ref.rs:8-60` (`visit_body`, `errors::UnalignedPackedRef`).
  - `compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:38-115` (`TypingEnv::post_analysis`, `is_required() -> true`, `TerminatorKind::Drop { .., async_fut }`).
  - `library/core/src/ptr/mod.rs:1812-1824, 2014-2023` (`MaybeUninit<T>` + `copy_nonoverlapping` implementation).
- **`google/zerocopy` @ `dc2008d87d8a4efbb391b2ef01c7fa31538d9d75` (byte-identical on examined files to `907b9175fee081872ec883ca4709e6ad922f8ed0` `v0.8.64`)**:
  - `zerocopy/src/wrappers.rs:115-421` (`#[repr(C, packed)] pub struct Unalign<T>(T)`, `try_deref`, `try_deref_mut`, `deref_unchecked` stale `repr(transparent)` safety comment at `L240`, `get_ptr`/`get_mut_ptr`, `set`, `update` with `WriteBackOnDrop`, `get`, `impl<T: Unaligned> Deref/DerefMut`).
  - `zerocopy/src/util/mod.rs:127-139` (`validate_aligned_to`, `t.addr() % mem::align_of::<U>()`).
  - `zerocopy/src/util/macro_util.rs:183-196, 585` (`ptr::addr_of!`, `core::ptr::read_unaligned`).
- **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`**:
  - `trusted/lean/Trusted/MirAst.lean:77-92, 583-618, 732-740, 782-795` (`noncomputable def` convention avoiding `._unsafe_rec`, `WithRetag::Yes` fail-closed rule, `AssertKind.misalignedPtrDeref`, `TerminatorKind` omitting `Drop`).
  - `trusted/lean/Trusted/MirSemantics.lean:578-583, 949-976, 1551` (`Allocation.alignLog2`, `evalOperandToSlot` failing on `!place.projection.isEmpty` and clearing moved locals with `deinitMovedPlace = true`).

### 2. Preserved Package Support Artifacts

| Artifact | Purpose & Verification Metrics | Size (bytes) & SHA-256 |
|---|---|---|
| `support/probe_packed_e0793_pin_unalign.py` | Self-contained probe harness executing `rustc` (`E0793` matrix, `-Z dump-mir=AddMovesForPackedDrops`), native binaries, `cargo +nightly miri` (Stacked Borrows & Tree Borrows), and real `zerocopy` (`v0.8.64`) inside `with tempfile.TemporaryDirectory():` | `27,329` bytes; `sha256: 118923f27cf1b39b372febd01125248ccc1d7592bf6689ff7fedc8b7528f6631` |
| `support/probe_results.json` | Captured structured output from `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0 (14210df0e2 2026-05-31)` and `zerocopy v0.8.64` across all 5 suites (`observed_at: 2026-11-23`) | `32,292` bytes; `sha256: 74d78e50713992170eb2fea1fd3fdc80a0a93020e2305bc3faecd1c57a0dc332` |
| `support/PackedFieldE0793PinAndUnalignSoundness.lean` | Standalone `prelude` + `Init.*` Lean `v4.34.1` formalization (`3,317` lines): kernel-checked cleanly (`-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`), MetaM audit `AUDIT_OK badRec=0 badPartial=0 badAxiom=0 localThms=255 localConsts=831` | `154,698` bytes; `sha256: dc59211c60961c241d46336e8f568fea5b36bf1807824e9ab69ee1a52697ff5b` |

## Revalidation

To verify these findings against a newer `rust-lang/rust` nightly, `google/zerocopy` revision, or `leanprover/lean4` toolchain without repeating full exploration:

1. **Rerun Empirical `rustc`, `Miri`, and `zerocopy::Unalign` Probes**:
   From the package directory (supplying a path to a clean `zerocopy` checkout under `google/zerocopy`):
   ```bash
   python3 support/probe_packed_e0793_pin_unalign.py --zerocopy-src /path/to/zerocopy/zerocopy --out /tmp/revalidated_probe_results.json
   ```
   Confirm `compile_returncode == 1` with `E0793` on all packed over-aligned borrows, identical `AddMovesForPackedDrops` `StorageLive`/`move`/`StorageDead` rewriting for `Packed1Drop` vs. unchanged `Packed4Drop`, `Miri` `exit 1` with exact alignment error messages on `&*raw`, `*raw`, and `&*raw_zst`, `E0277`/`E0596` on `PhantomPinned`, and `exit 0` with `MIRI_ZEROCOPY_UNALIGN_OK` on `zerocopy::Unalign<T>`.
2. **Diff Narrow Upstream Implementation Regions**:
   Check git diffs across `compiler/rustc_const_eval/src/util/alignment.rs` (`place_unalignment`, `most_packed_projection`), `compiler/rustc_mir_transform/src/{check_packed_ref.rs, add_moves_for_packed_drops.rs}`, `compiler/rustc_hir_analysis/src/check/check.rs` (`check_packed`), `library/core/src/{pin.rs, marker.rs}`, and `zerocopy/src/wrappers.rs` (`Unalign`). If `most_packed_projection` stops checking `!matches!(elem, ProjectionElem::Deref)`, or if `place_unalignment` alters its `Slice`/`Str` check, Section 1 invariants must be revisited.
3. **Re-Check Lean `v4.34.1` Formalization & Axiom Hygiene**:
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/PackedFieldE0793PinAndUnalignSoundness.lean
   ```
   Verify exit status `0`, zero warnings, zero occurrences of non-constructive axioms beyond `propext`/`Quot.sound` via Lean's MetaM axiom collector, and zero compiler-generated unsafe recursor helpers.
