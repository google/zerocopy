# `rustc` `#[repr(packed(N))]` Unaligned Field Projections, `E0793` Enforcement, `AddMovesForPackedDrops` Staging, and Synthesized Drop-Shim Alignment-Check Blind Spots

## Summary

`Basis: normative + source + execution + derived`

In `rustc`, `#[repr(packed(N))]` relaxes field and outer-object alignment shallowly without altering inner field types, creating a five-component chain of invariants across layout calculation (`rustc_abi`), THIR unsafety checking (`rustc_mir_build`), MIR borrow linting (`CheckPackedRef`), MIR drop staging (`AddMovesForPackedDrops`), MIR runtime UB instrumentation (`CheckAlignment` under `-Z ub-checks`), synthesized shims (`make_shim`), and SSA/LLVM codegen (`rustc_codegen_ssa`). Primary-source audits at `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly 2026-05-31`, Miri `0.1.0`, LLVM `22.1.6`) and upstream main `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, five live compiler/Miri/LLVM-IR probe suites, and a constructive Lean `v4.34.1` mechanization establish the following load-bearing results:

1. **Shallow clamping, ABI promotion suppression, and `E0588` drift (`rustc_abi`, `rustc_hir_analysis`):** `#[repr(packed(N))]` clamps each direct field's placement alignment to $\min(\text{align}(F_i), N)$ and caps outer alignment at $\max_i \min(\text{align}(F_i), N) \le N$ (`compiler/rustc_abi/src/layout.rs:1278-1285, 1311-1316`), suppressing `Scalar`/`ScalarPair` newtype promotion whenever outer alignment falls below the field's ABI alignment (`L1343`, confirmed in `-O0` LLVM IR where `PackedNewtype(u64)` routes through `llvm.memcpy` + `load i64, align 1`). Internal padding and inner slice-DST rounding moduli remain unchanged (`OuterPackedInnerAligned`: size `9`, align `1`; `OuterPacked2Dst`: sizes `6, 10, 10, 14` for `0, 1, 2, 5` bytes). Between `14210df0e` (`check.rs:1640-1674`) and `c7d5ba59d8` (`check.rs:1707-1748`), transitively embedding a `#[repr(align)]` type inside `#[repr(packed)]` drifted from hard error **`E0588`** to the **`ALIGNED_FIELDS_IN_PACKED`** lint gated on `repr.c()`. `Basis: normative + source + execution`
2. **Codegen alignment tracking vs. raw-pointer dereference reset (`rustc_codegen_ssa`):** `PlaceRef::project_field` computes `effective_field_align = self.val.align.restrict_for_offset(offset)` (`compiler/rustc_codegen_ssa/src/mir/place.rs:173`; `Align::restrict_for_offset` in `rustc_abi/src/lib.rs:1133-1141`), so direct by-value reads/writes emit `align 1` for `packed(1)`, `align 2` for `packed(2)` at offset `2`, and `align 4` for `packed(4)` `u32`/`u64` fields at offsets `4`/`8`. Conversely, `OperandRef::deref` (`operand.rs:275-289`) resets alignment to `layout.align.abi`, so `*(&raw const p.x)` emits `load i32, ptr ..., align 4` (UB) whereas `core::ptr::read_unaligned(&raw const p.x)` emits `load i32, ptr ..., align 1` at `-O2`. `Basis: source + execution`
3. **`E0793` lives in `CheckPackedRef` inside `mir_built` (before `mir_borrowck`), not `check_unsafety`:** Unaligned references `&packed.f` / `&mut packed.f` are rejected unconditionally—even inside `unsafe` blocks—by the MIR lint `CheckPackedRef` (`compiler/rustc_mir_transform/src/check_packed_ref.rs:8-61`), invoked during `mir_built` (`lib.rs:408`) using `rustc_const_eval::util::place_unalignment` (`compiler/rustc_const_eval/src/util/alignment.rs:9-78`). `most_packed_projection` walks projections in reverse, stops at `ProjectionElem::Deref`, takes the minimum enclosing `pack`, and suppresses the error only when `layout_of(ty)` succeeds with `layout.align.abi <= pack` and either `layout.is_sized()` or a slice/`str` unsized tail. THIR `check_unsafety` (`compiler/rustc_mir_build/src/check_unsafety.rs:468-492`) permits `&raw const` / `&raw mut` on packed struct fields in completely safe code. `Basis: normative + source + execution`
4. **`AddMovesForPackedDrops` stages unaligned drops in both user MIR and `DropGlue` shims, including cleanup landing pads:** Whenever `place_unalignment` returns `Some` for a `TerminatorKind::Drop`, `AddMovesForPackedDrops` (`compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:38-115`) inserts `StorageLive(_tmp); _tmp = move place; drop(_tmp) -> [return: bb_dead, unwind: orig_unwind];` with `StorageDead(_tmp); goto -> orig_target;` in a newly allocated block inheriting `is_cleanup`. It runs both in `run_runtime_lowering_passes` (`lib.rs:643`, rewriting direct field overwrites in user MIR) and inside `make_shim` (`shim.rs:236`, rewriting `DropGlue` shims). On nested `OuterPacked1` (`packed(1)`) wrapping `InnerPacked4` (`packed(4)`) wrapping `Logged16` (`align = 16`) with a panicking first field, every destructor—including cleanup-path unwind destructors—observes `addr % 16 == 0` identically in native (`-C panic=unwind`) and Miri, even though pre-drop field addresses satisfy `addr % 16 == 5`. Notably, `AddMovesForPackedDrops` emits `StorageDead(_tmp)` only on the normal `target` edge, leaving `_tmp` storage-live along the `unwind` edge until frame exit. `Basis: source + execution`
5. **The four-layer `-Z ub-checks=yes` vs. Miri alignment-check blind spot (`core::ptr::drop_in_place`, `make_shim`, `?Sized` generics, and terminators):** While direct user-MIR `&mut *raw_ptr` and `*raw_ptr` immediately abort under `-Z ub-checks=yes` (`rc = -6`, `SIGABRT`, 1 MIR alignment assert) and fault in Miri (`rc = 1`), **`core::ptr::drop_in_place(ptr)` on a misaligned pointer silently exits `0` under `-Z ub-checks=yes` at both `-O0` and `-O2`** while faulting immediately in Miri (`rc = 1`). Direct source inspection at both `14210df0e` and `c7d5ba59d8` reveals four interacting mechanisms:
   - *(a) `?Sized` suppression:* `core::ptr::drop_in_place<T: PointeeSized>` (`library/core/src/ptr/mod.rs:808-821` at `14210df0e`; `L836-849` at `c7d5ba59d8`) executes `unsafe { drop_glue(&mut *to_drop) }`, where `T` is not `Sized`; `PointerFinder::visit_place` (`check_pointers.rs:209-212`) unconditionally skips any dereference whose `pointee_ty` fails `is_sized` (also reproduced identically in user code via `#[inline(always)] unsafe fn generic_unsized_ref<T: ?Sized>` -> `0` asserts, `rc = 0`, vs. `T: Sized` -> `1` assert, `rc = -6`).
   - *(b) `CheckAlignment`-before-`Inline` ordering and precompiled `libcore`:* `CheckAlignment` runs at `lib.rs:695` *before* `ForceInline` (`L707`) and `Inline` (`L709`), so inlining a `?Sized` or precompiled `libcore` callee introduces raw-pointer dereferences after `CheckAlignment` has already completed.
   - *(c) `make_shim` omits `CheckAlignment` completely:* For synchronous `DropGlue`, `VTableShim`, `FnPtrShim`, `ReifyShim`, `ClosureOnceShim`, `CloneShim`, `ThreadLocalShim`, `FnPtrAddrShim`, and coroutine `DropGlue`, `make_shim` (`shim.rs:231-246` at `14210df0e`; `L186-201` at `c7d5ba59d8`) runs an 8-pass list that includes `AddMovesForPackedDrops` but omits `CheckAlignment`, `CheckNull`, and `CheckEnums` (unlike `FutureDropPollShim` and `AsyncDropGlue`, which call `run_optimization_passes`).
   - *(d) Statements-only loop in `check_pointers`:* `check_pointers` (`check_pointers.rs:74-122`) iterates only `basic_blocks[block].statements` and never visits `basic_blocks[block].terminator`, despite matching `MutatingUseContext::{Call, Yield, Drop}` in `should_visit_place` (`L160-176`). A `#[custom_mir]` terminator-only `Call(ret = sink(Move(*p)))` produces `0` alignment asserts, exits `0` at `-O0 -Z ub-checks=yes`, crashes with unguarded `SIGSEGV` (`rc = -11`) at `-O2 -Z ub-checks=yes`, and faults immediately in Miri (`rc = 1`). `Basis: source + execution`
6. **Optimizer amplification under `-O2 -Z ub-checks=yes`:** Because `drop_in_place` passes `&mut *to_drop` into `drop_glue(&mut T)` without triggering an alignment check, LLVM 22.1.6 propagates the `&mut Aligned64` (`align 64`) / `&mut DropU128` (`align 16`) alignment assumption into `Drop::drop(&mut self)`. At `-O0 -Z ub-checks=yes`, `Drop::drop` prints the true misaligned modulus (`DROP_ALIGNED64_MOD64=1`, `DROP_U128_MOD16=1`); at `-O2 -Z ub-checks=yes`, LLVM constant-folds `(self as *const Self).addr() % 64` to **`0`** (`DROP_ALIGNED64_MOD64=0`, `DROP_U128_MOD16=0`) even while `pre_mod=1`! `Basis: execution + derived`
7. **Anneal trusted MIR boundary (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`):** `Trusted.MirAst` and `Trusted.MirSemantics` currently fail closed (`.fault .unsupported`) on all packed structs (no ADT layout or `repr(packed)` metadata in `MirTy`), all non-empty place projections in `evalStatement` (`MirSemantics.lean:1407-1408`) and `evalRvalue`, `Rvalue.ref` / `Rvalue.addressOf` (`L1313`), `TerminatorKind.drop` (mapped to `.unsupported` at `MirAst.lean:782-784`), `TerminatorKind.assert` (including `AssertKind.misalignedPtrDeref`, `MirSemantics.lean:1568`), and `Operand::RuntimeChecks` (`MirAst.lean:548-556`). `Basis: source`
8. **Kernel-checked Lean `v4.34.1` formalization (`support/PackedProjectionsAndAlignedDropStaging.lean`):** A self-contained constructive formalization (zero `sorry`, zero `Classical.choice`, zero `omega`, zero `bv_decide`, zero `native_decide`, zero `partial def`, zero `._unsafe_rec`) models byte-addressed memory, power-of-two alignment arithmetic, `computeStructLayout`, `placeUnaligned` / `effAlign`, `checkPackedRefBody`, `addMovesForPackedDropsBody`, and dual strict-Miri vs. `-Z ub-checks` semantics. It proves: (i) alignment-preserving soundness and byte-payload preservation of `addMovesForPackedDrops`, (ii) static absence of misaligned safe references and drops under `E0793` + `Copy` staging + `addMovesForPackedDrops`, (iii) an exact biconditional `whole_program_ub_checks_complete_iff_shims_instrumented`, and (iv) three kernel-evaluated sharpness counterexamples (`ce1_direct_packed_drop_passes_misaligned_self_ub`, `ce2_uninstrumented_drop_shim_escapes_ub_checks`, `ce3_unsized_generic_deref_escapes_user_ub_checks`). `Basis: execution (Lean kernel) + derived`

> **Scope caution.** The Lean `v4.34.1` module is a standalone formal model of the MIR passes and dual semantics, not a translation-validation proof over `rustc`'s Rust source code, and does not import `joshlf/anneal`'s `Trusted.*` modules. Dynamic execution evidence was collected on `x86_64-unknown-linux-gnu` with `rustc 1.98.0-nightly (14210df0e 2026-05-31)`; upstream `c7d5ba59d8` was verified by direct source inspection rather than execution. See **Boundaries**.

## Applicability

`Basis: documentation + source`

### Subjects and how they relate

- **`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`** (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `miri 0.1.0 (14210df0e2 2026-05-31)`, LLVM `22.1.6`, host `x86_64-unknown-linux-gnu`): The exact compiler, Miri engine, and standard library both inspected in source and executed across all five empirical probe experiments (`support/probe_packed_projections_and_drops.py`). Unless explicitly tagged with `c7d5ba59d8`, every `compiler/` and `library/` line citation refers to this revision so source and execution match bit-for-bit.
- **`rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`** (upstream main, 2026-11-20): Audited in source across `check.rs`, `check_packed_ref.rs`, `add_moves_for_packed_drops.rs`, `check_alignment.rs`, `check_pointers.rs`, `shim.rs`, `alignment.rs`, `layout.rs`, `check_unsafety.rs`, `place.rs`, and `library/core/src/ptr/mod.rs` to establish which mechanisms are invariant across the six-month span and which drifted.
- **`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`** and **`rust-lang/reference@bcd62f35e8bf480ec5b0fa569b6d12ea5924030c`**: The exact `src/doc/reference` submodule commits pinned by `14210df0e` and `c7d5ba59d8` respectively, supplying normative rules for `#[repr(packed(N))]` (`src/type-layout.md`) and misaligned places/references (`src/behavior-considered-undefined.md`).
- **`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`**: Audited directly at `trusted/lean/Trusted/{MirAst,MirSemantics}.lean`, `trusted/correspondence/Trusted/Correspondence.lean`, and `trusted/rustc-capture/src/driver.rs` to determine exact current admission boundaries and obligations for verified-rustc MIR lowering.
- **`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`** (`v4.34.1`, Release): Toolchain used to kernel-check `support/PackedProjectionsAndAlignedDropStaging.lean` with `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.

### Shared behavior vs. version-specific drift (`14210df0e` vs. `c7d5ba59d8`)

| Mechanism | `14210df0e` (`2026-05-31`, source + executed) | `c7d5ba59d8` (`2026-11-20`, source audited) | Status |
| :--- | :--- | :--- | :--- |
| `#[repr(packed)]` transitively containing `#[repr(align)]` | Hard error **`E0588`** (`check.rs:1640-1674`) for all packed types | **`ALIGNED_FIELDS_IN_PACKED`** lint gated on `repr.c()` (`check.rs:1707-1748`) | **Changed** |
| `place_unalignment` & `most_packed_projection` | `rustc_const_eval/src/util/alignment.rs:9-78` (`layout.align.abi <= pack`) | Same algorithm (`alignment.rs:9-78`, refactored field name `layout.align <= pack`) | **Shared** |
| `CheckPackedRef` (`E0793`) in `mir_built` | `check_packed_ref.rs:8-61`, `lib.rs:408`, unconditional even inside `unsafe` | Same semantics (`check_packed_ref.rs:8-50`, refactored `diagnostics::UnalignedPackedRef`) | **Shared** |
| `AddMovesForPackedDrops` in user lowering & `make_shim` | `add_moves_for_packed_drops.rs:38-115`, `lib.rs:643`, `shim.rs:236` (`is_required() = true`) | Same rewrite (`add_moves_for_packed_drops.rs:38-111`, `PassPolicy::Required`, `async_fut` field removed) | **Shared** |
| `core::ptr::drop_in_place<T: PointeeSized>` body | `unsafe { drop_glue(&mut *to_drop) }` (`core/src/ptr/mod.rs:808-821`) | Identical body (`core/src/ptr/mod.rs:836-849`) | **Shared** |
| `make_shim` pass list omitting `CheckAlignment` | `shim.rs:231-246` (`InstanceKind`, 8 passes, no `CheckAlignment`/`CheckNull`) | `shim.rs:186-201` (`ShimKind`, identical 8 passes, no `CheckAlignment`/`CheckNull`) | **Shared** |
| `check_pointers` skipping `!is_sized` & skipping terminators | `check_pointers.rs:74-122, 209-212` | Identical statements-only loop and `!pointee_ty.is_sized` skip (`check_pointers.rs:74-144, 215-218`) | **Shared** |
| `CheckAlignment` before `ForceInline` / `Inline` | `lib.rs:695` before `L707`/`L709` | Same ordering in `run_optimization_passes` | **Shared** |

### Configuration and scope boundaries

- **Execution configuration:** Rust Edition 2021, host/target `x86_64-unknown-linux-gnu`. Layout and MIR dumps run with `-C opt-level=0 -C debuginfo=0`; LLVM IR alignment checks run at both `-C opt-level=0` and `-C opt-level=2`; the alignment-check matrix runs each specimen across `-C opt-level=0 -Z ub-checks=yes`, `-C opt-level=2 -Z ub-checks=yes`, `-C opt-level=0 -Z ub-checks=no`, and `cargo miri run --offline`. One specimen (`case5i_custom_mir_terminator_only_deref`) uses unstable `#![feature(custom_mir, core_intrinsics)]` to construct a terminator-only raw-pointer dereference cleanly.
- **Relationship to adjacent corpus packages:** Complements `repr-packed-unaligned-references-slice-dst-alignment-and-cell-projections` (which focuses on `zerocopy` slice-DST `KnownLayout` rounding algebra and `UnsafeCell`/`Cell` Tree Borrows interactions) and `rustc-drop-elaboration-drop-flags-and-unwind-cleanup-mir-refinement` (which focuses on `ElaborateDrops` drop-flag dataflow and open-drop ladders). This package specifically establishes compiler-internal `rustc` MIR/codegen/shim ground truth for packed field projections, `AddMovesForPackedDrops`, LLVM IR alignment emission, and the `-Z ub-checks` vs. Miri alignment-check blind spot.

## Findings

### 1. Shallow Packing Layout Algebra, ABI Promotion Suppression, and `E0588` Drift

`Basis: normative + source + execution`

Under the Rust Reference (`rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, `src/type-layout.md:486-512`), `#[repr(packed(N))]` ($N = 2^k \in [1, 2^{29}]$, default $N = 1$ for `#[repr(packed)]`) modifies field positioning and outer struct/union alignment shallowly without modifying the layout or internal padding of any field's own type.

In `compiler/rustc_abi/src/layout.rs` (`14210df0e`), `LayoutCalculator::univariant_biased` (`L1100-1360`) implements these rules directly:

```rust
// compiler/rustc_abi/src/layout.rs:1107-1109, 1278-1285, 1311-1320 (14210df0e)
let pack = repr.pack;
let mut align = if pack.is_some() { dl.i8_align } else { dl.aggregate_align };
let mut max_repr_align = repr.align;
...
let field_align = if let Some(pack) = pack {
    field.align.min(AbiAlign::new(pack))
} else {
    field.align
};
offset = offset.align_to(field_align.abi);
align = align.max(field_align.abi);
max_repr_align = max_repr_align.max(field.max_repr_align);
...
let unadjusted_abi_align = align;
if let Some(repr_align) = repr.align {
    align = align.max(repr_align);
}
let size = min_size.align_to(align);
```

Three structural consequences follow directly from this algorithm and are confirmed by `exp1_layout_and_llvm_ir` and `exp2_e0793_and_wfcheck_matrix`:

1. **Shallow clamping & non-transitivity:** For `struct { tag: u8, x: u32, y: u64 }`:
   - `#[repr(C, packed)]` (`Packed1`): `size = 13`, `align = 1`, offsets `(0, 1, 5)`.
   - `#[repr(C, packed(2))]` (`Packed2`): `size = 14`, `align = 2`, offsets `(0, 2, 6)`.
   - `#[repr(C, packed(4))]` (`Packed4`): `size = 16`, `align = 4`, offsets `(0, 4, 8)`.
   - Embedding `#[repr(C)] struct InnerAligned { a: u32, b: u8 }` (`size = 8, align = 4`, offsets `(0, 4)`, 3 bytes trailing padding) inside `#[repr(C, packed)] struct OuterPackedInnerAligned { tag: u8, inner: InnerAligned }` yields `size = 9`, `align = 1`, offsets `(0, 1)`—preserving all 3 trailing padding bytes inside `InnerAligned`.
   - Embedding `#[repr(C)] struct InnerDst { a: u32, tail: [u8] }` inside `#[repr(C, packed(2))] struct OuterPacked2Dst { b: u8, inner: InnerDst }` yields dynamic sizes `6, 10, 10, 14` for `0, 1, 2, 5` tail elements: the outer struct aligns `inner` to `2` (offset `2`), while `InnerDst` retains its internal 4-byte rounding modulus (`4, 8, 8, 12`).
2. **ABI newtype promotion suppression (`layout.rs:475-483, 1332-1359`):** Single-non-ZST-field structs and unions are promoted from `BackendRepr::Memory { sized: true }` to `BackendRepr::Scalar` / `ScalarPair` only when `offsets[i].bytes() == 0 && align == field.align.abi && size == field.size` (`L1343`; unions check `repr.scalar_align(dl).unwrap() != align` at `L479-482`). For `#[repr(packed)] struct PackedNewtype(u64)`, `align = 1 != 8`, suppressing scalar promotion. In `-O0` LLVM IR (`exp1`), `pass_aligned_newtype(v: AlignedNewtype)` uses `v` directly as an `i64` register (`define i64 @pass_aligned_newtype(i64 %v)` with zero memory operations), whereas `pass_packed_newtype(v: PackedNewtype)` copies into an `align 1` stack slot via `call void @llvm.memcpy.p0.p0.i64(ptr align 1 %v, ptr align 8 %1, i64 8, i1 false)` followed by `%_0 = load i64, ptr %v, align 1`.
3. **Well-formedness errors (`E0587`, `E0634`, `E0277`, and the `E0588` -> `ALIGNED_FIELDS_IN_PACKED` drift):**
   - `#[repr(packed, align(8))]` triggers hard error **`E0587`** (`check.rs:1632-1639` at `14210df0e`; `L1699-1706` at `c7d5ba59d8`).
   - Duplicate `#[repr(packed(1), packed(2))]` triggers hard error **`E0634`**.
   - An unsized tail in a packed struct whose type `needs_drop()` triggers **`E0277`** (`the size for values of type [D] cannot be known at compilation time`) because `compiler/rustc_hir_analysis/src/check/wfcheck.rs:1104-1114` computes `needs_drop_copy = || packed && ty.needs_drop(...)` and forces a `Sized` bound on the tail so `AddMovesForPackedDrops` can move it to a stack temporary. Wrapping the tail in `ManuallyDrop<[D]>` sets `needs_drop == false` and compiles cleanly (`exp2`).
   - **Version drift on transitive `#[repr(align)]` fields:** At `14210df0e` (`check.rs:1640-1674`), `check_packed_inner` emits hard error **`E0588`** (`packed type cannot transitively contain a #[repr(align)] type`) for any packed struct transitively containing a `#[repr(align)]` ADT, confirmed in `exp2` (`packed_containing_repr_align_e0588` fails with `E0588`). At upstream main `c7d5ba59d8` (`check.rs:1707-1748`), `E0588` was replaced by the **`ALIGNED_FIELDS_IN_PACKED`** lint gated on `repr.c()`. Natural over-alignment without `#[repr(align)]` (such as `u128` with ABI alignment `16` on `x86_64-unknown-linux-gnu`) is accepted in packed structs at both revisions.

---

### 2. Effective Place Alignment and LLVM IR Load/Store Alignment Emission

`Basis: normative + source + execution`

The Rust Reference (`src/behavior-considered-undefined.md:92-131` at `ad35aca48175`) defines a place as *"based on a misaligned pointer"* strictly by the **last `*` projection**: if there is no `*` projection (accessing a local or `static`), or if the last `*` dereferenced a pointer aligned for its pointee type (e.g., `&Packed1` with alignment `1` or `&Packed2` with alignment `2`), subsequent field projections `.f` do **not** make the place based on a misaligned pointer, even when `align_of::<Field>() > pack`.

`rustc_codegen_ssa` and Miri implement this rule with two complementary invariants:

1. **SSA Codegen `PlaceValue.align` clamping (`compiler/rustc_codegen_ssa/src/mir/place.rs:26-35, 166-193, 349-359`):**
   - Every `PlaceRef` carries `val.align: Align` separately from `layout.align.abi` (`place.rs:88-90`: *"You probably shouldn't use the alignment from this layout; rather you should use the `.val.align` of the actual place"*).
   - Stack `alloca` starts at `layout.align.abi` (`place.rs:127`).
   - `PlaceRef::project_field` (`place.rs:172-173`) clamps alignment across every field projection via:
     ```rust
     let offset = self.layout.fields.offset(ix);
     let effective_field_align = self.val.align.restrict_for_offset(offset);
     ```
     where `Align::restrict_for_offset(self, size)` (`compiler/rustc_abi/src/lib.rs:1133-1141`) returns `self.min(Align { pow2: size.bytes().trailing_zeros() as u8 })`—the greatest power of two dividing both `self` and `offset`.
   - `BuilderMethods::load_from_place` (`compiler/rustc_codegen_ssa/src/traits/builder.rs:249-252`) and `OperandValue::store_with_flags` (`compiler/rustc_codegen_ssa/src/mir/operand.rs:942-959`) emit LLVM `load`/`store` instructions tagged with `place.val.align`.
   - **Crucial reset at `ProjectionElem::Deref` (`place.rs:351`, `operand.rs:275-289`):** Dereferencing *any* pointer or reference calls `OperandRef::deref`, which executes `self.val.deref(layout.align.abi).with_type(layout)`—unconditionally restoring full ABI alignment of the pointee type! Thus `*(&raw const p.x)` discards the packed container's `align 1` and emits a full `align 4` LLVM load (UB if `addr % 4 != 0`).
2. **Miri `MemPlace.misaligned` propagation (`compiler/rustc_const_eval/src/interpret/place.rs:51-95`):** Miri stores `misaligned: Option<Misalignment>` on `MemPlace`. Field projection via `offset_with_meta` (`L94`) preserves `misaligned: self.misaligned` unchanged, so projecting `.x` from an aligned `&Packed1` preserves `misaligned = None`. Dereferencing a raw `*const u32` recomputes misalignment against `align_of::<u32>() = 4` (`memory.rs:629-635`) and triggers immediate UB on load/store/borrow.

Empirical LLVM IR emitted by `rustc 1.98.0-nightly (14210df0e)` (`exp1_layout_and_llvm_ir`, LLVM `22.1.6`) confirms every alignment attribute exactly:

| Function (`exp1`) | Operation | Field Offset | ABI Align | LLVM IR (`-O0`) | LLVM IR (`-O2`) |
| :--- | :--- | :---: | :---: | :--- | :--- |
| `read_p1_u32(p: &Packed1)` | Direct `p.x` (`u32`) | `1` | `4` | `load i32, ptr %0, align 1` | `load i32, ptr %0, align 1, !noundef` |
| `write_p1_u32(p: &mut Packed1, v)` | Direct `p.x = v` | `1` | `4` | `store i32 %v, ptr %0, align 1` | `store i32 %v, ptr %0, align 1` |
| `read_p2_u32(p: &Packed2)` | Direct `p.x` (`u32`) | `2` | `4` | `load i32, ptr %0, align 2` | `load i32, ptr %0, align 2, !noundef` |
| `write_p2_u32(p: &mut Packed2, v)` | Direct `p.x = v` | `2` | `4` | `store i32 %v, ptr %0, align 2` | `store i32 %v, ptr %0, align 2` |
| `read_p4_u32(p: &Packed4)` | Direct `p.x` (`u32`) | `4` | `4` | `load i32, ptr %0, align 4` | `load i32, ptr %0, align 4, !noundef` |
| `read_p4_u64(p: &Packed4)` | Direct `p.y` (`u64`) | `8` | `8` | `load i64, ptr %0, align 4` | `load i64, ptr %0, align 4, !noundef` |
| `read_p1_unaligned_raw(p: &Packed1)` | `ptr::read_unaligned(&raw const p.x)` | `1` | `4` | calls `core::ptr::read_unaligned` (`copy_nonoverlapping` as `*const u8`) | `load i32, ptr %raw, align 1` |
| `read_p1_ub_deref_raw(p: &Packed1)` | `*black_box(&raw const p.x)` (UB) | `1` | `4` | `load i32, ptr %raw, align 4` | `load i32, ptr %0, align 4, !noundef` |

*(Note: without `black_box`, MIR optimization at `-O2` folds `*(&raw const p.x)` back into direct `p.x` before codegen, masking the `align 4` UB in a trivial synthetic function; `black_box` preserves the raw-pointer dereference into codegen, exposing `load i32, ptr %0, align 4` at both `-O0` and `-O2`.)*

---

### 3. Static Prohibition of Unaligned References: `CheckPackedRef` (`E0793`), THIR `check_unsafety`, `Copy` Copy-Out, and Raw-Pointer Projections

`Basis: normative + source + execution`

Creating a Rust reference (`&T` or `&mut T`) whose address is not a multiple of `align_of_val` produces an invalid value—immediate UB even if the reference is never dereferenced (`src/behavior-considered-undefined.md:70-73, 121-130`). `rustc` enforces this across three distinct frontend/MIR components:

1. **Unalignment predicate (`compiler/rustc_const_eval/src/util/alignment.rs:9-78`):** Both `CheckPackedRef` and `AddMovesForPackedDrops` share a single predicate `place_unalignment` backed by `most_packed_projection`:
   ```rust
   // compiler/rustc_const_eval/src/util/alignment.rs:56-78 (14210df0e & c7d5ba59d8)
   pub fn most_packed_projection<'tcx, L>(
       tcx: TyCtxt<'tcx>,
       local_decls: &L,
       place: Place<'tcx>,
   ) -> Option<(AdtDef<'tcx>, Align)>
   where
       L: HasLocalDecls<'tcx>,
   {
       place
           .iter_projections()
           .rev()
           // Stop at `Deref`; standard ABI alignment applies there.
           .take_while(|(_base, elem)| !matches!(elem, ProjectionElem::Deref))
           .filter_map(|(base, _elem)| {
               let adt = base.ty(local_decls, tcx).ty.ty_adt_def()?;
               let pack = adt.repr().pack?;
               Some((adt, pack))
           })
           .min_by_key(|(_, align)| *align)
   }
   ```
   Given `Some((descr, pack))`, `place_unalignment` (`L24-50`) queries `tcx.layout_of(typing_env.as_query_input(ty))`. It returns `None` (guaranteed aligned) **if and only if** `Ok(layout)` holds with `layout.align.abi <= pack` (`layout.align <= pack` at `c7d5ba59d8`) **and** `(layout.is_sized() || matches!(unsized_tail().kind(), ty::Slice(..) | ty::Str))`. In all other cases—including polymorphic generic types whose layout cannot yet be computed and non-slice unsized tails such as `dyn Trait`—it conservatively returns `Some((descr, pack))`.
2. **Hard error `E0793` in `CheckPackedRef` during `mir_built` (BEFORE `mir_borrowck`!):**
   - `CheckPackedRef` (`compiler/rustc_mir_transform/src/check_packed_ref.rs:8-61`) runs inside `mir_built` (`compiler/rustc_mir_transform/src/lib.rs:408`)—earlier than `mir_borrowck` (`lib.rs:523`).
   - Whenever `context.is_borrow()` and `util::place_unalignment(...)` returns `Some((adt, pack))`, it emits `errors::UnalignedPackedRef` (`compiler/rustc_mir_transform/src/errors.rs:56-75`, code **`E0793`**), or ICEs via `span_bug!` if triggered inside a builtin `#[derive]` (`check_packed_ref.rs:45-51`).
   - Crucially, `CheckPackedRef` does **not** consult `unsafe` blocks: `unsafe { &p.x }` fails with `E0793` identically to safe `&p.x`.
   - `rustc_borrowck` (`compiler/rustc_borrowck/src/lib.rs`) contains **zero** `E0793` / packed-reference alignment checks; borrowck operates on MIR bodies that have already passed `CheckPackedRef` in `mir_built`.
3. **THIR `check_unsafety` (`compiler/rustc_mir_build/src/check_unsafety.rs:468-508`) and safe `&raw const` / `Copy` copy-out:**
   - `check_unsafety.rs` contains zero packed-field borrow errors. Instead, `ExprKind::RawBorrow` (`L468-492`) explicitly permits `&raw const` / `&raw mut` on packed struct fields—and even peels `Deref` (`L469-476`) and `union` field projections (`L481-491`)—without requiring `unsafe`.
   - Direct `Copy` reads (`let v = p.x;` or braced temporaries `println!("{}", { p.x });`) lower to `Operand::Copy(p.x)` (not `PlaceContext::is_borrow()`), bypassing `CheckPackedRef` and emitting packed-aligned loads as shown in Finding 2.

All 15 compile-time cases in `exp2_e0793_and_wfcheck_matrix` confirm the exact decision boundary:

| Case (`exp2`) | Expression / Definition | Result | Error Code | Mechanism |
| :--- | :--- | :---: | :---: | :--- |
| `safe_ref_packed1_u32` | `&p.x` (`u32` in `packed(1)`) | Reject | `E0793` | `CheckPackedRef`: `align 4 > pack 1` |
| `unsafe_ref_packed1_u32` | `unsafe { &p.x }` | Reject | `E0793` | `CheckPackedRef` ignores `unsafe` |
| `println_implicit_ref_packed1_u32` | `println!("{}", p.x)` | Reject | `E0793` | Macro expands to `&p.x` |
| `braced_copy_packed1_u32` | `println!("{}", { p.x })` | Pass | — | Copies `u32` to aligned stack temp first |
| `safe_ref_packed1_u8_ok` | `&p.tag` (`u8` in `packed(1)`) | Pass | — | `align 1 <= pack 1` -> `place_unalignment = None` |
| `safe_ref_packed4_u32_ok` | `&p4.x` (`u32` in `packed(4)`) | Pass | — | `align 4 <= pack 4` -> `place_unalignment = None` |
| `safe_ref_packed4_u64_err` | `&p4.y` (`u64` in `packed(4)`) | Reject | `E0793` | `align 8 > pack 4` |
| `safe_raw_ptr_packed1_u32_ok` | `(&raw const p.x, &raw mut p.x)` in safe `fn` | Pass | — | `Rvalue::RawPtr` not a borrow; `check_unsafety` allows |
| `packed_unsized_drop_tail_err` | `#[repr(C, packed)] struct S { tag: u8, tail: [D] }` | Reject | `E0277` | `wfcheck.rs:1104-1114` `needs_drop_copy` |
| `packed_unsized_manually_drop_tail_ok` | `tail: ManuallyDrop<[D]>` | Pass | — | `ManuallyDrop::needs_drop == false` |
| `repr_packed_and_align_conflict_e0587` | `#[repr(packed, align(8))]` | Reject | `E0587` | `check.rs:1632-1639` |
| `packed_containing_repr_align_e0588` | `#[repr(C, packed)]` containing `#[repr(align(64))]` | Reject | `E0588` | `check.rs:1640-1674` (`14210df0e`; lint at `c7d5ba59d8`) |
| `repr_packed_duplicate_e0634` | `#[repr(packed(1), packed(2))]` | Reject | `E0634` | `check.rs` conflicting packed hints |
| `custom_drop_move_from_mut_ref_e0507` | `impl Drop` moving `self.d` | Reject | `E0507` | Cannot move out of `&mut self` |
| `custom_drop_owned_move_field_e0509` | `fn f(s: S) -> D { s.d }` on `Drop` packed `S` | Reject | `E0509` | Cannot move out of type implementing `Drop` |

---

### 4. Aligned Stack Staging in `AddMovesForPackedDrops` (User MIR, `DropGlue` Shims, Nested Packing, and Unwind Cleanup)

`Basis: source + execution`

Because `Drop::drop(&mut self)` requires an aligned `&mut T`, dropping a field stored at an unaligned offset inside a `#[repr(packed(N))]` struct cannot pass a reference to the field in place. `AddMovesForPackedDrops` (`compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:38-115`) solves this by rewriting every `TerminatorKind::Drop { place, target, unwind, replace, drop, .. }` satisfying `util::place_unalignment(tcx, body, typing_env, place).is_some()` (`L53-54`) into:

```rust
// compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:92-114 (14210df0e)
let ty = place.ty(body, tcx).ty;
let temp = patch.new_temp(ty, source_info.span);
let storage_dead_block = patch.new_block(BasicBlockData::new_stmts(
    vec![Statement::new(source_info, StatementKind::StorageDead(temp))],
    Some(Terminator { source_info, kind: TerminatorKind::Goto { target } }),
    is_cleanup,
));
patch.add_statement(loc, StatementKind::StorageLive(temp));
patch.add_assign(loc, Place::from(temp), Rvalue::Use(Operand::Move(*place), WithRetag::Yes));
patch.patch_terminator(
    loc.block,
    TerminatorKind::Drop { place: Place::from(temp), target: storage_dead_block, unwind, replace, drop, async_fut },
);
```

Four load-bearing engineering details emerge from source inspection and `exp3`/`exp4` MIR dumps:

1. **Two execution sites (`lib.rs:643` and `shim.rs:236`):**
   - When user code drops a packed field directly—such as overwriting `holder.0.aligned = replacement` (`exp3`, `overwrite_packed_field`), or partial moves generating an `Open` drop ladder—`ElaborateDrops` emits `drop(((_1.0: PackedHolder).1: DropU128))` directly inside the user function, and `run_runtime_lowering_passes` (`lib.rs:643`) invokes `AddMovesForPackedDrops` (`2-2-007.AddMovesForPackedDrops`) on that user MIR. In `exp3`, `bb2` is visibly rewritten from `drop(((_1.0: PackedHolder).1: DropU128)) -> [return: bb3, unwind: bb4]` to:
     ```text
     StorageLive(_20);
     _20 = move ((_1.0: PackedHolder).1: DropU128);
     drop(_20) -> [return: bb20, unwind: bb4];
     ```
     with `bb20: { StorageDead(_20); goto -> bb3; }`, and cleanup block `bb18 (cleanup)` is identically staged through `_21`.
   - When user code drops the packed struct as a whole (`drop_whole_packed_holder` in `exp3`), the user body itself only executes `drop(_1)` (`Align16<PackedHolder>`), so `AddMovesForPackedDrops` on the user function is a no-op! Instead, `make_shim` (`shim.rs:236`, `1-1-001.AddMovesForPackedDrops`) runs `AddMovesForPackedDrops` on the synthesized **`std::ptr::drop_glue::<PackedHolder>`** shim, rewriting both the normal drop block (`bb5`) and the cleanup block (`bb4 (cleanup)`):
     ```text
     // core.ptr-drop_glue.PackedHolder.1-1-001.AddMovesForPackedDrops.before.mir -> after.mir
     bb4 (cleanup): {                                  bb4 (cleanup): {
         drop(((*_1).1: DropU128))                         StorageLive(_2);
           -> [return: bb2, unwind terminate(cleanup)];    _2 = move ((*_1).1: DropU128);
     }                                                     drop(_2) -> [return: bb6, unwind terminate(cleanup)];
                                                       }
     bb5: {                                            bb5: {
         drop(((*_1).1: DropU128))                         StorageLive(_3);
           -> [return: bb3, unwind: bb2];                  _3 = move ((*_1).1: DropU128);
     }                                                     drop(_3) -> [return: bb7, unwind: bb2];
                                                       }
                                                       bb6 (cleanup): { StorageDead(_2); goto -> bb2; }
                                                       bb7:           { StorageDead(_3); goto -> bb3; }
     ```
   - Across both paths in `exp3`, `Align16<PackedHolder>` guarantees deterministic unaligned field address `(&raw const holder.0.aligned).addr() % 16 == 1` (`OVERWRITE_FIELD_MOD16=1`, `WHOLE_FIELD_MOD16=1`), while inside `Drop::drop(&mut self)`, every invocation observes **`addr % 16 == 0`** (`OVERWRITE_DROP_MOD16=0`, `FINAL_MOD16=0`, `WHOLE_DROP_MOD16=0`, `TOTAL_COUNT=3`) identically on native and Miri!
2. **Nested packing and double-staged unwind safety (`exp4`):** With `OuterPacked1` (`packed(1)`) wrapping `InnerPacked4` (`packed(4)`) wrapping `f1: Logged16` (`align = 16`, panics on drop) and `f2: Logged16` (`align = 16`), plus `tail: Logged16`:
   - `drop_glue::<OuterPacked1>` stages `InnerPacked4` (`align = 4 > pack 1`) into 4-aligned locals `_5` (normal) and `_3` (cleanup) and stages `tail` (`align = 16 > pack 1`) into 16-aligned locals `_4` (normal) and `_2` (cleanup).
   - `drop_glue::<InnerPacked4>` then stages `f1` and `f2` (`align = 16 > pack 4`) into 16-aligned locals `_5`, `_4` (normal) and `_3`, `_2` (cleanup).
   - When `inner.f1` panics during drop, `inner.f2` and `outer.tail` both execute along cleanup landing pads. Both native (`-C panic=unwind`) and Miri produce identical output:
     ```text
     CAUGHT=true PRE_MOD16=(5,5,5) LOG=[inner.f1:mod16=0:panic=true,inner.f2:mod16=0:panic=false,outer.tail:mod16=0:panic=false]
     ```
     confirming that every staged drop on both the normal path and the panic-unwinding cleanup path receives a properly aligned `&mut self`.
3. **`is_cleanup` preservation vs. missing unwind-edge `StorageDead`:** `add_move_for_packed_drop` (`add_moves_for_packed_drops.rs:96-100`) passes `is_cleanup` to `storage_dead_block`, keeping cleanup-block well-formedness intact. However, it splices `storage_dead_block` **only onto `target` (the normal return edge)** and forwards `unwind` unchanged (`L108-109`). Consequently, if `drop(temp)` unwinds, `StorageDead(temp)` never executes on the unwind path (the stack local remains storage-live until the enclosing frame exits or unwinds out). Any MIR verifier checking balanced `StorageLive`/`StorageDead` along unwind paths must account for this asymmetry.
4. **Why `#[repr(packed)]` cannot support structural `Pin` projection:** Because `AddMovesForPackedDrops` relocates fields via `move` to a different stack address before running `Drop::drop`, the `Drop` guarantee of `Pin` (RFC 2349) cannot hold for any over-aligned field inside a packed struct.

---

### 5. `CheckAlignment` (`-Z ub-checks`) Architecture and the Four-Layer Alignment-Check Blind Spot

`Basis: source + execution + derived`

Under `-Z ub-checks=yes` (or default debug builds with `debug-assertions=yes`), `rustc` runs `CheckAlignment` (`compiler/rustc_mir_transform/src/check_alignment.rs:12-147`) via the shared raw-pointer visitor `check_pointers` (`compiler/rustc_mir_transform/src/check_pointers.rs:43-245`). For each discovered raw-pointer access on a non-excluded type (excluding `bool`, `i8`, `u8`, `check_alignment.rs:21`), `insert_alignment_check` (`L42-147`) splits the basic block before the statement and emits:
1. `thin_ptr = copy ptr as *const () (PtrToPtr)`
2. `addr = copy thin_ptr as usize (Transmute)`
3. `alignment_mask = Sub(<T as SizedTypeProperties>::ALIGN, 1)` (further masked by `target.max_reliable_alignment()` if `< Align::MAX`)
4. `alignment_bits = BitAnd(copy addr, copy alignment_mask)`
5. `is_ok = Eq(copy alignment_bits, 0)`
6. `TerminatorKind::Assert { cond: Copy(is_ok), expected: true, msg: MisalignedPointerDereference { required, found }, target: new_block, unwind: UnwindAction::Unreachable }` (`check_pointers.rs:106-119`; calls a `#[rustc_nounwind]` panic routine causing `SIGABRT` / `rc = -6`).

However, **four interacting architectural gaps** in `rustc` (`14210df0e` and unchanged at `c7d5ba59d8`) allow misaligned raw-pointer drops, `?Sized` generic dereferences, and terminator-only dereferences to bypass `CheckAlignment` completely:

1. **Gap 1 — `core::ptr::drop_in_place<T: PointeeSized>` fails `pointee_ty.is_sized` (`library/core/src/ptr/mod.rs:808-821` + `check_pointers.rs:209-212`):**
   At both `14210df0e` (`mod.rs:808-828`) and `c7d5ba59d8` (`mod.rs:836-859`), `core::ptr::drop_in_place` is a regular `#[inline(always)]` generic function in `libcore`, NOT the lang item itself:
   ```rust
   // library/core/src/ptr/mod.rs:804-826 (14210df0e; L836-858 at c7d5ba59d8)
   #[inline(always)]
   pub const unsafe fn drop_in_place<T: PointeeSized>(to_drop: *mut T)
   where
       T: [const] Destruct,
   {
       unsafe { drop_glue(&mut *to_drop) }
   }

   #[lang = "drop_glue"]
   pub(crate) const unsafe fn drop_glue<T: PointeeSized>(_: &mut T)
   ```
   Inside `drop_in_place`, `&mut *to_drop` dereferences `to_drop: *mut T` where `T: PointeeSized` (`?Sized`). Because `CheckAlignment` runs on **polymorphic** MIR (`optimized_mir` before monomorphization), `PointerFinder::visit_place` (`check_pointers.rs:209-212`) checks:
   ```rust
   if !pointee_ty.is_sized(self.tcx, self.typing_env) {
       trace!("Raw pointer, but pointee is not known to be sized: {:?}", pointer_ty);
       return;
   }
   ```
   and **unconditionally skips emitting any alignment check**—even if `libcore` itself were rebuilt with `-Z ub-checks=yes`! (Furthermore, distributed precompiled `libcore` is built with `debug-assertions=no` / `ub-checks=no` anyway.)
2. **Gap 2 — `CheckAlignment` executes before `ForceInline` / `Inline` (`compiler/rustc_mir_transform/src/lib.rs:695-710`):**
   In `run_optimization_passes`:
   ```rust
   &check_alignment::CheckAlignment, // L695
   &check_null::CheckNull,           // L696
   &check_enums::CheckEnums,         // L697
   &lower_slice_len::LowerSliceLenCalls,
   &instsimplify::InstSimplify::BeforeInline,
   &inline::ForceInline,             // L707
   &inline::Inline,                  // L709
   ```
   When a user crate compiled with `-Z ub-checks=yes` calls `core::ptr::drop_in_place::<Aligned64>(ptr)` or a local `#[inline(always)] unsafe fn generic_unsized_ref<T: ?Sized>(ptr: *mut T) -> &mut T`, `CheckAlignment` sees only the `TerminatorKind::Call` in the caller (no raw deref) and skips the callee (because `T: ?Sized`). When `Inline` subsequently substitutes `T = Aligned64` (now concretely `Sized`!) and splices `&mut *ptr` into the caller, `CheckAlignment` has already run and never re-runs!
3. **Gap 3 — `make_shim` omits `CheckAlignment` (`compiler/rustc_mir_transform/src/shim.rs:231-246` at `14210df0e`; `L186-201` at `c7d5ba59d8`):**
   Synchronous `DropGlue`, `VTableShim` (which explicitly takes `self: *mut Self` and dereferences `*self` at `shim.rs:72-75, 874-881, 900`!), `FnPtrShim`, `ReifyShim`, `ClosureOnceShim`, `CloneShim`, `ThreadLocalShim`, and `FnPtrAddrShim` bypass `run_optimization_passes` and instead run a fixed 8-pass list:
   ```rust
   // compiler/rustc_mir_transform/src/shim.rs:231-246 (14210df0e; L186-201 at c7d5ba59d8)
   pm::run_passes_no_validate(
       tcx,
       &mut result,
       &[
           &mentioned_items::MentionedItems,
           &add_moves_for_packed_drops::AddMovesForPackedDrops,
           &remove_noop_landing_pads::RemoveNoopLandingPads,
           &simplify::SimplifyCfg::MakeShim,
           &instsimplify::InstSimplify::BeforeInline,
           &inline::ForceInline,
           &abort_unwinding_calls::AbortUnwindingCalls,
           &add_call_guards::CriticalCallEdges,
       ],
       Some(MirPhase::Runtime(RuntimePhase::Optimized)),
   );
   ```
   Coroutine `DropGlue` (`shim.rs:148-158`) runs only 3 passes (`MentionedItems`, `AbortUnwindingCalls`, `CriticalCallEdges`). Only `FutureDropPollShim` (`L183`) and `AsyncDropGlue` (`L206`) invoke `run_optimization_passes`. Moreover, even if `CheckAlignment` were added to `make_shim`, `drop_glue` takes `&mut T` (`ty::Ref`, not `ty::RawPtr`), which `check_pointers.rs:190` intentionally ignores—meaning a complete fix requires **both** checking `&mut *to_drop` inside `drop_in_place` (post-monomorphization or via `align_of_val_raw`) **and** running `CheckAlignment` on `VTableShim` and other raw-pointer-accepting shims in `make_shim`.
4. **Gap 4 — `check_pointers` only visits statements, never terminators (`compiler/rustc_mir_transform/src/check_pointers.rs:74-122`):**
   Although `PointerFinder::should_visit_place` (`L160-176`) explicitly matches `MutatingUseContext::{Call, Yield, Drop}`, the outer loop in `check_pointers` iterates exclusively over `for statement_index in (0..basic_blocks[block].statements.len()).rev() { finder.visit_statement(statement, location); }` (`L75-87`) and never calls `finder.visit_terminator`. Any MIR body (for instance `#[custom_mir]` or an optimization pass that folds a copy into a `Call`/`Drop` terminator operand) whose only raw-pointer dereference sits in a terminator completely escapes `CheckAlignment`.

All nine cases of `exp5_ub_checks_vs_miri_matrix` (`rustc 1.98.0-nightly 14210df0e`, Miri `0.1.0`, LLVM `22.1.6`) empirically confirm every single layer of this matrix:

| Case (`exp5`) | MIR Asserts (`-O0 -Zub`) | `-O0 -Z ub-checks=yes` | `-O2 -Z ub-checks=yes` | `-O0 -Z ub-checks=no` | `Miri` |
| :--- | :---: | :--- | :--- | :--- | :--- |
| `5a`: direct `&mut *ptr` (`DropU128`, align 16) | **1** | **`rc = -6` (SIGABRT)** `misaligned pointer dereference` | **`rc = -6` (SIGABRT)** | `rc = 0` (`addr_mod=1`) | **`rc = 1` UB** (required 16, found 1) |
| `5b`: direct `&mut *ptr` (`Aligned64`, align 64) | **1** | **`rc = -6` (SIGABRT)** `misaligned pointer dereference` | **`rc = -6` (SIGABRT)** | `rc = 0` (`addr_mod=1`) | **`rc = 1` UB** (required 64, found 1) |
| `5c`: direct `(*ptr).0[0]` (`DropU128`, align 16) | **1** | **`rc = -6` (SIGABRT)** `misaligned pointer dereference` | **`rc = -6` (SIGABRT)** | `rc = 0` (`v=42`) | **`rc = 1` UB** (required 16, found 1) |
| `5d`: `drop_in_place(ptr)` (`DropU128`, align 16) | **0** | **`rc = 0` SILENT** (`DROP_U128_MOD16=1`) | **`rc = 0` SILENT + FOLDED** (`DROP_U128_MOD16=0`, `pre_mod=1`!) | `rc = 0` (`MOD16=1`) | **`rc = 1` UB** (required 16, found 1) |
| `5e`: `drop_in_place(ptr)` (`Aligned64`, align 64) | **0** | **`rc = 0` SILENT** (`DROP_ALIGNED64_MOD64=1`) | **`rc = 0` SILENT + FOLDED** (`DROP_ALIGNED64_MOD64=0`, `pre_mod=1`!) | `rc = 0` (`MOD64=1`) | **`rc = 1` UB** (required 64, found 1) |
| `5f`: `drop_in_place(ptr)` (`GlueOnly16`, field drop only) | **0** | **`rc = 0` SILENT** (`DROP_LEAF_VAL=99`) | **`rc = 0` SILENT** (`DROP_LEAF_VAL=99`) | `rc = 0` (`VAL=99`) | **`rc = 1` UB** (required 16, found 1) |
| `5g`: `#[inline(always)] fn<T>(*mut T) -> &mut T` (`Sized`) | **1** | **`rc = -6` (SIGABRT)** | **`rc = -6` (SIGABRT)** | `rc = 0` (`addr_mod=1`) | **`rc = 1` UB** (required 16, found 1) |
| `5h`: `#[inline(always)] fn<T: ?Sized>(*mut T) -> &mut T` | **0** | **`rc = 0` SILENT** (`addr_mod=1`) | **`rc = 0` SILENT** (`addr_mod=1`) | `rc = 0` (`addr_mod=1`) | **`rc = 1` UB** (required 16, found 1) |
| `5i`: `#[custom_mir]` terminator `Call(sink(Move(*p)))` | **0** | **`rc = 0` SILENT** (`v=77`) | **`rc = -11` (SIGSEGV!)** (no UB panic) | `rc = 0` (`v=77`) | **`rc = 1` UB** (required 16, found 1) |

Look closely at two secondary empirical surprises revealed by this table:
- **Optimizer constant-folding in `5d` and `5e` at `-O2 -Z ub-checks=yes`:** Because `drop_in_place` creates `&mut *to_drop` without an alignment assertion and calls `drop_glue(&mut T)`, LLVM receives an `align 16` / `align 64` parameter attribute on `self` inside `Drop::drop(&mut self)`. At `-O2`, LLVM 22.1.6 optimizes `(self as *const Self).addr() % 64` to the compile-time constant **`0`**, so the binary prints `DROP_ALIGNED64_MOD64=0` even though `pre_mod=1` was passed on the exact same line! Thus at `-O2`, even manual runtime self-checks inside `Drop::drop(&mut self)` are silently optimized away.
- **Hardware `SIGSEGV` (`rc = -11`) in `5i` at `-O2 -Z ub-checks=yes`:** Because `CheckAlignment` misses the terminator-only `Move(*p)` on `*const DropU128`, `-O0` silently succeeds (`v=77`), while `-O2` lowers the 32-byte `align 16` copy to aligned SSE instructions (`movaps`) that fault with hardware `SIGSEGV` (`rc = -11`) rather than a `-Z ub-checks` panic.

---

### 6. Anneal Trusted MIR Boundary Audit (`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`)

`Basis: source + derived`

Direct inspection of `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/lean/Trusted/MirAst.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `trusted/correspondence/Trusted/Correspondence.lean`, `trusted/rustc-capture/src/driver.rs`) shows that Anneal currently fails closed on every construct involved in packed field projections, packed drop elaboration, and alignment UB checks:

| Required Feature | Current Status in `joshlf/anneal@c131b320` | Exact Source Location |
| :--- | :--- | :--- |
| `#[repr(packed(N))]` ADT types & field offsets | Absent: `MirTy` has only `bool`, `int`, `unit`, `never`, fieldless `enum`, `tuple`, `ref`, `rawPtr`, `unsupported` (no struct `Adt`, no `pack : Option Align`, no per-field byte offsets) | `Trusted/MirAst.lean:312-321` |
| Place projections (`ProjectionElem.deref`, `.field`) | AST defines `.deref` and `.field`, **but** `evalStatement` (`Assign`) and `evalRvalue` (`Discriminant`) immediately reject `!place.projection.isEmpty` with `.fault .unsupported` | `Trusted/MirAst.lean:472-475`; `Trusted/MirSemantics.lean:1270-1271, 1407-1408` |
| `Rvalue::Ref` and `Rvalue::RawPtr` (`&raw const`/`&raw mut`) | AST defines `.ref` and `.addressOf`, **but** `evalRvalue` hits catch-all `\| _ => .error .unsupported` | `Trusted/MirAst.lean:625-626`; `Trusted/MirSemantics.lean:1313` |
| `TerminatorKind::Drop` & `UnwindTerminate` | Lowered to `TerminatorKind.unsupported`; `evalTerminator` returns `.fault .unsupported`; `Correspondence.lean:2186` returns `.error (.unsupported "Drop unsupported")` | `Trusted/MirAst.lean:782-784`; `Trusted/MirSemantics.lean:1568`; `Trusted/Correspondence.lean:2186` |
| `AssertKind::MisalignedPointerDereference` & `TerminatorKind::Assert` | AST defines `AssertKind.misalignedPtrDeref`, **but** `evalTerminator` maps every `.assert` to `.fault .unsupported` | `Trusted/MirAst.lean:738`; `Trusted/MirSemantics.lean:1568` |
| `Operand::RuntimeChecks(UbChecks)` | Explicitly unmodeled in `MirAst.Operand`; must fail closed at capture | `Trusted/MirAst.lean:548-556` |
| `rustc-capture` compiler driver | Currently validates compiler version (`1.98.0-nightly (f8a08b688 2026-05-30)`) and reaches `after_analysis` without yet extracting MIR or `make_shim` bodies | `trusted/rustc-capture/src/driver.rs:25, 75-84` |

**Concrete architectural requirements for verified-rustc MIR lowering:**
1. Capture must preserve **both** user `optimized_mir` bodies **and** synthesized `mir_shims` (`DropGlue`, `VTableShim`, etc.) with explicit `ReprOptions::pack` and field-offset layout metadata so `Place` evaluation can compute `effAlign = min(baseAlign, restrict_for_offset)` and distinguish direct packed `Copy` loads (`align = pack`) from deref-reset loads (`align = abiAlign`).
2. Capturing at `Runtime(PostCleanup)` (`mir_drops_elaborated_and_const_checked`) observes MIR **after** `AddMovesForPackedDrops` (`lib.rs:643`) and **before** `CheckAlignment` (`lib.rs:695`). A verified compiler cannot rely on `rustc`'s `-Z ub-checks` to establish runtime alignment safety of `drop_in_place` calls, `?Sized` generic dereferences, or shims; it must verify alignment obligations against the strict Miri/Reference semantics (`PtrValidAligned`) directly across all reachable user bodies and synthesized shims.
3. Because `AddMovesForPackedDrops` omits `StorageDead(temp)` on unwind edges (`add_moves_for_packed_drops.rs:96-114`), MIR-to-SSA/codegen lowering proofs must treat frame-exit stack reclamation as releasing any storage-live temporaries left live across an unwinding `Drop`.

---

### 7. Kernel-Checked Lean `v4.34.1` Formalization (`support/PackedProjectionsAndAlignedDropStaging.lean`)

`Basis: execution (Lean kernel) + derived`

The standalone module `support/PackedProjectionsAndAlignedDropStaging.lean` formalizes the full stack—byte-addressed memory, power-of-two alignment arithmetic, `#[repr(packed(N))]` layout calculation, `place_unalignment` / `effAlign`, `CheckPackedRef` (`E0793`), `AddMovesForPackedDrops`, and dual strict-Miri vs. `-Z ub-checks` semantics across user functions and synthesized `DropGlue` shims.

#### Axiom and hygiene guarantees

Checked with `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) under `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` (`2,004` lines, `67` theorems):
- **0 errors**, **0 warnings**, **0 `sorry` / `sorryAx`**, **0 `Classical.choice`**, **0 `omega`**, **0 `bv_decide`**, **0 `native_decide` / `Lean.ofReduceBool`**, **0 `partial def`**, **0 `._unsafe_rec`**.
- Direct `#print axioms` audit confirms: `verified_packed_layouts` depends on **no axioms (`[]`)**; `e0793_and_copy_staging_no_misaligned_safe_refs`, `ce1_direct_packed_drop_passes_misaligned_self_ub`, `ce2_uninstrumented_drop_shim_escapes_ub_checks`, `ce3_unsized_generic_deref_escapes_user_ub_checks`, and all layout/alignment lemmas depend only on **`[propext]`**; `addMovesForPackedDrops_alignment_sound` and `whole_program_ub_checks_complete_iff_shims_instrumented` depend only on **`[propext, Quot.sound]`**.
- Every arithmetic divisibility lemma (`Align.check_eq_true_iff`, `Align.divides_mono`, `Align.divides_add`, `Align.divides_alignUp`, `Align.restrictForOffset_divides_addr`) is proved constructively from `Init` `Nat` lemmas using power-of-two exponents `Align := { pow2 : Nat }`.

#### Theorem inventory

| Declaration | Kind | Formal Guarantee |
| :--- | :--- | :--- |
| `Align.restrictForOffset_divides_addr` | Lemma | Models `Align::restrict_for_offset`: if `base.Divides addr`, then `(restrictForOffset base off).Divides (addr + off)`. |
| `allocAligned_ptrValidAligned` & `allocAligned_write_read_same` | Lemmas | Stack staging allocations satisfy `PtrValidAligned` (`InBounds ∧ reqAlign.Divides base`) and exact byte round-trip read/write. |
| `layout_outer_align_le_pack` & `layout_field_offset_divisible` | Theorems | `computeStructLayout (some p) fields` caps outer alignment at `≤ p` and places every field at an offset divisible by `min(field.abiAlign, p)`. |
| `effAlignProjs_divides_derefFree` & `wellAlignedAtEnd_divides` | Theorems | Deref-free packed projections preserve `effAlign`; unpacked or sufficiently-packed projections (`reqAlign ≤ pack`) guarantee `reqAlign.Divides addr`. |
| `stagePackedDropsList_no_unaligned_drops` | Theorem | Static completeness: zero unaligned `.dropPlace` statements remain after `AddMovesForPackedDrops`. |
| `addMovesForPackedDrops_alignment_sound` | **Core Theorem 1** | Every staged packed drop executes with `ty.abiAlign.Divides base`, drops the exact original field byte payload (`payload`), and marks the staging slot `StorageDead`. |
| `e0793_and_copy_staging_no_misaligned_safe_refs` | **Core Theorem 2** | Any safe body passing `checkPackedRefBody` (`E0793`)—permitting aligned `mkRef`, `Copy` `copyFromPlace`, and `mkRawPtr`—and transformed by `addMovesForPackedDropsBody` never produces `.ubMisaligned` under strict Miri semantics and maintains `AllDropsAligned`. |
| `instrumentWholeProgram_complete` | Lemma | Whole-program instrumentation (`CheckAlignment` on both `.userFn` and all synthesized `DropGlue` shims) traps every sized-pointee strict-Miri alignment UB as `.ubTrap`. |
| `whole_program_ub_checks_complete_iff_shims_instrumented` | **Core Theorem 3** | Exact biconditional: `UbChecksCompleteFor (policyOf instrumentShims) ↔ instrumentShims = true`. |
| `verified_packed_layouts` | Theorem (`rfl`) | Evaluates `Packed1` (`size 13, align 1`), `Packed2` (`size 14, align 2`), `Packed4` (`size 16, align 4`), and `PackedHolder` (`size 65, align 1`) in kernel WHNF. |
| `ce1_direct_packed_drop_passes_misaligned_self_ub` | **Sharpness CE 1** | Dropping `PackedHolder.aligned` at address `65` (`65 % 64 = 1`) without staging immediately faults `.ubMisaligned "drop_place" 65 align64`; with `addMovesForPackedDropsBody`, it stages to aligned address `192` (`64 * 3`) and drops the exact 64-byte payload cleanly. |
| `ce2_uninstrumented_drop_shim_escapes_ub_checks` | **Sharpness CE 2** | On address `65`, user-MIR `&mut *ptr` traps `.ubTrap 65 align64` under `instrumentUserOnly`; `drop_in_place(ptr)` faults `.ubMisaligned` under strict Miri, **escapes as `.silentMisalignedExec`** under `instrumentUserOnly` (real `rustc`), and deterministically traps `.ubTrap 65 align64` under `instrumentWholeProgram`. |
| `ce3_unsized_generic_deref_escapes_user_ub_checks` | **Sharpness CE 3** | Models `T: PointeeSized` (`isSized = false`): even inside a `.userFn` under `instrumentWholeProgram`, skipping `!isSized` lets misaligned `&mut *ptr` escape as `.silentMisalignedExec` while strict Miri faults `.ubMisaligned`. |

## Boundaries

`Basis: source + execution + derived`

- **Not examined:**
  - *Non-`x86_64` targets and strict-alignment hardware architectures (e.g., SPARC, strict-alignment ARM/RISC-V configurations, or targets where `target.max_reliable_alignment() < Align::MAX`):* While `check_alignment.rs:85-107` explicitly masks checks by `max_reliable_alignment()`, runtime behavior and codegen lowering on non-`x86_64` targets were not executed.
  - *Cranelift (`rustc_codegen_cranelift`) and GCC (`rustc_codegen_gcc`) codegen backends:* Only LLVM `22.1.6` via `rustc_codegen_ssa` was inspected and executed.
  - *`AsyncDropGlue` / `FutureDropPollShim` runtime execution:* Source inspection (`shim.rs:168-209` at `14210df0e`, `L130-170` at `c7d5ba59d8`) shows those experimental async shims call `run_optimization_passes`, unlike synchronous `DropGlue`, but nightly async-drop execution was not probed.
  - *`VTableShim` runtime execution under `-Z ub-checks=yes`:* Source inspection confirms `VTableShim` takes `*mut Self`, dereferences `*self`, and uses `make_shim`'s 8-pass list without `CheckAlignment`, but an end-to-end misaligned raw-vtable dispatch specimen was not executed.
  - *`#[repr(packed)]` unions with `ManuallyDrop` fields, `#[repr(simd, packed)]`, and inline assembly alignment constraints:* Not probed.
- **Unknown:**
  - *Whether an upstream `rustc` fix for the `drop_in_place` / `make_shim` blind spot will instrument `drop_in_place` via `align_of_val_raw` (supporting `?Sized` types dynamically), run `CheckAlignment` post-inlining/post-monomorphization, or add `CheckAlignment` to `make_shim`:* Upstream design intent beyond the inspected source commits was not determined.
  - *Exact execution behavior of `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973`:* Source inspection verifies identical logic in `check_packed_ref.rs`, `add_moves_for_packed_drops.rs`, `check_alignment.rs`, `check_pointers.rs`, `shim.rs`, and `core/src/ptr/mod.rs`, plus the `E0588` -> `ALIGNED_FIELDS_IN_PACKED` change in `check.rs`, but no binary from `c7d5ba59d8` was compiled or executed.
- **Known not to apply:**
  - *`E0588` hard rejection of `#[repr(align)]` inside `#[repr(packed)]` does not apply uniformly across all 2026 nightlies:* It is a hard error at `14210df0e` (`check.rs:1640-1674`) and an `ALIGNED_FIELDS_IN_PACKED` lint gated on `repr.c()` at `c7d5ba59d8` (`check.rs:1707-1748`).
  - *`AddMovesForPackedDrops` does not stage fields whose alignment already satisfies `layout.align.abi <= pack`:* For example, dropping a `u32` (or an align-4 struct) inside `#[repr(C, packed(4))]` leaves the `Drop` terminator in place without a stack temporary (`place_unalignment` returns `None`).
  - *`CheckAlignment` does not instrument `bool`, `i8`, `u8`, `[u8; N]`, or references (`&T`/`&mut T`):* `check_alignment.rs:21` excludes 1-byte scalars/arrays, and `check_pointers.rs:190` checks only `ty::RawPtr`.
- **Unsupported:**
  - *`joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` does not currently support packed structs, non-empty place projections, `Rvalue::{Ref, RawPtr}`, `TerminatorKind::{Drop, Assert}`, or `Operand::RuntimeChecks`:* All fail closed with `.fault .unsupported`.
  - *Safe unsized tails that `needs_drop()` inside `#[repr(packed)]`:* Explicitly rejected by `rustc` (`E0277`, `wfcheck.rs:1104-1114`).
- **Attractive stronger conclusions not established:**
  - *Passing `-Z ub-checks=yes` does NOT imply absence of misaligned-pointer UB across a Rust program:* As proved both empirically (`exp5` cases `5d`, `5e`, `5f`, `5h`, `5i`) and formally (`ce2`, `ce3`), `drop_in_place`, `?Sized` generics, synthesized shims, and terminator-only dereferences escape `-Z ub-checks=yes`.
  - *Observing `(self as *const Self).addr() % align == 0` at runtime inside `Drop::drop(&mut self)` under `-O2` does NOT prove `self` was aligned:* As `exp5` cases `5d` and `5e` demonstrate, LLVM constant-folds that check to `0` from the UB-violated `&mut self` alignment attribute!
  - *The Lean formalization does not prove correctness of `rustc`'s Rust compiler implementation:* It mechanizes a faithful model of the MIR passes and dual semantics, without a verified compiler-source bridge.

## Evidence

### Primary Git source citations

#### `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly 2026-05-31`, executed)
- `compiler/rustc_abi/src/lib.rs:147-160` (`ReprOptions::pack`), `L1133-1141` (`Align::max_aligned_factor`, `Align::restrict_for_offset`).
- `compiler/rustc_abi/src/layout.rs:406, 461-483` (union `repr.pack` alignment clamping & ABI suppression), `L588-590` (enum `ReprConflict`), `L1107-1109, 1157-1160, 1258-1261, 1278-1285, 1311-1320, 1342-1359` (`univariant_biased` field alignment clamping `min(field.align, pack)`, `unadjusted_abi_align`, and `BackendRepr::Scalar`/`ScalarPair` suppression).
- `compiler/rustc_hir_analysis/src/check/check.rs:1632-1675, 1678-1700` (`E0587` conflict, `E0588` `check_packed_inner` transitive `#[repr(align)]` check).
- `compiler/rustc_hir_analysis/src/check/wfcheck.rs:1049, 1104-1114` (`needs_drop_copy` forcing `Sized` on packed unsized tails that `needs_drop`).
- `compiler/rustc_mir_build/src/check_unsafety.rs:468-508` (`ExprKind::RawBorrow` safe raw borrows on packed/union fields vs. `ExprKind::Deref` requiring `unsafe`).
- `compiler/rustc_const_eval/src/util/alignment.rs:9-78` (`place_unalignment`, `most_packed_projection`).
- `compiler/rustc_const_eval/src/interpret/place.rs:51-95` (`MemPlace.misaligned`, `offset_with_meta` preserving `self.misaligned`); `compiler/rustc_const_eval/src/interpret/memory.rs:629-635` (`check_ptr_align`).
- `compiler/rustc_mir_transform/src/check_packed_ref.rs:8-61` (`CheckPackedRef` MIR lint) and `compiler/rustc_mir_transform/src/errors.rs:56-75` (`UnalignedPackedRef`, `code = E0793`).
- `compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs:38-115` (`AddMovesForPackedDrops`, `add_move_for_packed_drop`).
- `compiler/rustc_mir_transform/src/check_alignment.rs:12-147` (`CheckAlignment`, `insert_alignment_check`) and `compiler/rustc_mir_transform/src/check_pointers.rs:43-245` (`check_pointers` statements-only loop `L74-122`, `should_visit_place` `L160-176`, `RawPtr` filter `L190`, `FollowProjections` `L197-206`, `!pointee_ty.is_sized` skip `L209-212`).
- `compiler/rustc_mir_transform/src/lib.rs:401-417` (`mir_built` running `CheckPackedRef`), `L521-526` (`mir_borrowck`), `L626-650` (`run_runtime_lowering_passes` running `ElaborateDrops` -> `AbortUnwindingCalls` -> `AddMovesForPackedDrops`), `L690-715` (`run_optimization_passes` running `CheckAlignment` before `ForceInline` and `Inline`).
- `compiler/rustc_mir_transform/src/shim.rs:67-251` (`make_shim`, coroutine `DropGlue` `L148-158`, `FutureDropPollShim` `L172-183`, `AsyncDropGlue` `L193-206`, synchronous `DropGlue`/`VTableShim` 8-pass list `L231-246` with `AddMovesForPackedDrops` and without `CheckAlignment`), `L303-405` (`build_drop_shim`), `L455-514` (`DropShimElaborator`), `L874-905` (`VTableShim` `*mut Self` deref).
- `compiler/rustc_mir_transform/src/elaborate_drop.rs:972-985` (`Rvalue::Ref` for `Drop::drop` call inside `build_drop_shim`).
- `compiler/rustc_codegen_ssa/src/mir/place.rs:26-35, 82-92, 121-128, 166-193, 229-247, 349-359` (`PlaceValue.align`, `PlaceRef::project_field` calling `restrict_for_offset`, `Deref` calling `load_operand().deref()`).
- `compiler/rustc_codegen_ssa/src/mir/operand.rs:101-104, 275-289, 922-961` (`OperandRef::deref` resetting alignment to `layout.align.abi`, `store_with_flags` using `dest.val.align`).
- `compiler/rustc_codegen_ssa/src/traits/builder.rs:249-252` (`load_from_place` passing `place.align`).
- `library/core/src/ptr/mod.rs:804-828` (`drop_in_place<T: PointeeSized>` calling `drop_glue(&mut *to_drop)`), `L1812-1824` (`read_unaligned` via `copy_nonoverlapping`), `L2014-2023` (`write_unaligned` via `copy_nonoverlapping`).

#### `rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973` (upstream main, source audited)
- `compiler/rustc_hir_analysis/src/check/check.rs:1699-1748` (`E0587` retained; `E0588` replaced by `ALIGNED_FIELDS_IN_PACKED` gated on `repr.c()`).
- `compiler/rustc_const_eval/src/util/alignment.rs:9-78` (identical logic; `layout.align <= pack` at `L28`).
- `compiler/rustc_mir_transform/src/check_packed_ref.rs:8-50`, `add_moves_for_packed_drops.rs:38-111`, `check_alignment.rs:12-148`, `check_pointers.rs:43-251`, `shim.rs:28-206` (`ShimKind` rename, identical 8-pass list in `make_shim` omitting `CheckAlignment`), `library/core/src/ptr/mod.rs:836-859` (identical `drop_in_place` -> `drop_glue(&mut *to_drop)`).

#### Normative & verification repositories
- `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`: `src/type-layout.md:138-149, 486-527` (`layout.repr.alignment.*`); `src/behavior-considered-undefined.md:26-34, 69-74, 92-131` (`undefined.misaligned.*`).
- `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/lean/Trusted/MirAst.lean:312-321, 472-475, 548-556, 620-628, 732-740, 785-795`; `trusted/lean/Trusted/MirSemantics.lean:1240-1313, 1406-1427, 1537-1570`; `trusted/correspondence/Trusted/Correspondence.lean:2186`; `trusted/rustc-capture/src/driver.rs:25, 75-84`.
- `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`: `Lean (version 4.34.1, x86_64-unknown-linux-gnu, Release)`.

### Preserved support artifacts

All empirical scripts, recorded outputs, and mechanized proofs are preserved under `support/` inside this package:
- `support/probe_packed_projections_and_drops.py`: Standalone Python 3.10+ probe driver running all 5 experiments (`exp1` layout & LLVM IR, `exp2` 15-case compile matrix, `exp3` `AddMovesForPackedDrops` user MIR + `DropGlue` shim MIR + native/Miri runs, `exp4` nested `OuterPacked1`/`InnerPacked4` panicking unwind safety across native/Miri, `exp5` 9-case x 4-configuration `-Z ub-checks` vs. Miri divergence matrix) with deterministic path/PID/address scrubbing.
- `support/probe_packed_projections_and_drops.json`: Complete scrubbed JSON output (51,456 bytes) recorded on 2026-11-21 against `rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `miri 0.1.0 (14210df0e2 2026-05-31)`, LLVM `22.1.6`.
- `support/PackedProjectionsAndAlignedDropStaging.lean`: Self-contained constructive Lean `v4.34.1` formalization (`2,004` lines, `67` theorems) establishing Core Theorems 1–3 and Sharpness Counterexamples 1–3 with `0` errors, `0` warnings, `0` `sorry`, `0` `Classical.choice`, and `#print axioms` restricted strictly to `[]`, `[propext]`, and `[propext, Quot.sound]`.

## Revalidation

`Basis: execution + derived`

Revalidating these findings on a newer `rustc` / Miri / Lean toolchain requires only four narrow, cheap checks rather than repeating the full source crawl:

1. **Rerun the 5-experiment compiler/Miri/LLVM-IR probe (~15 seconds):**
   ```console
   python3 support/probe_packed_projections_and_drops.py --out /tmp/packed_reval.json
   ```
   Key discriminating assertions to check in `/tmp/packed_reval.json`:
   - `exp1`: `read_p1_u32` emits `align 1`, `read_p2_u32` emits `align 2`, `read_p4_u64` emits `align 4`, `read_p1_ub_deref_raw` emits `align 4`, and `read_p1_unaligned_raw` at `-O2` emits `align 1`.
   - `exp2`: `safe_ref_packed1_u32` and `unsafe_ref_packed1_u32` fail `E0793`; `safe_raw_ptr_packed1_u32_ok` and `safe_ref_packed4_u32_ok` pass; `packed_containing_repr_align_e0588` distinguishes `E0588`-era compilers (fail) from `ALIGNED_FIELDS_IN_PACKED`-era compilers (pass with warning).
   - `exp3` & `exp4`: Native and Miri stdout match byte-for-byte with `MOD16=0` inside every `Drop::drop` call despite `PRE_MOD16 != 0`, and `AddMovesForPackedDrops` emits `StorageLive`/`move`/`drop`/`StorageDead` in both `overwrite_packed_field` and `core.ptr-drop_glue.*`.
   - `exp5`: Check whether `case5d`, `case5e`, `case5f` (`drop_in_place`), `case5h` (`T: ?Sized`), or `case5i` (`#[custom_mir]` terminator deref) flip from `rc = 0` (`0` asserts) to `rc = -6` (`SIGABRT`, `1` assert) under `-Z ub-checks=yes`. Any such flip signals that upstream closed one of the four alignment-check blind spots documented in Finding 5.
2. **Diff the six decisive `rust-lang/rust` implementation regions against `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`:**
   - `compiler/rustc_mir_transform/src/shim.rs` (`make_shim` pass list)
   - `compiler/rustc_mir_transform/src/check_pointers.rs` (`check_pointers` loop over `statements` vs. `terminator`, and `!pointee_ty.is_sized`)
   - `compiler/rustc_mir_transform/src/lib.rs` (ordering of `CheckAlignment` relative to `ForceInline` / `Inline`)
   - `library/core/src/ptr/mod.rs` (`drop_in_place` body calling `drop_glue(&mut *to_drop)`)
   - `compiler/rustc_const_eval/src/util/alignment.rs` (`place_unalignment` / `most_packed_projection`)
   - `compiler/rustc_mir_transform/src/add_moves_for_packed_drops.rs` (`add_move_for_packed_drop`)
3. **Re-check the Lean `v4.34.1` formalization and axiom footprint (<5 seconds once a build slot is free):**
   ```console
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/PackedProjectionsAndAlignedDropStaging.lean
   ```
   Confirm exit code `0`, zero warnings, zero `sorry` / `Classical.choice` / `omega` / `bv_decide` / `native_decide` / `partial def` / `._unsafe_rec`, and verify `#print axioms` on `addMovesForPackedDrops_alignment_sound`, `e0793_and_copy_staging_no_misaligned_safe_refs`, `whole_program_ub_checks_complete_iff_shims_instrumented`, `ce1_direct_packed_drop_passes_misaligned_self_ub`, `ce2_uninstrumented_drop_shim_escapes_ub_checks`, and `ce3_unsized_generic_deref_escapes_user_ub_checks`.
4. **Re-check Anneal MIR admission (`joshlf/anneal`):** Diff `trusted/lean/Trusted/{MirAst,MirSemantics}.lean` against `c131b320eeeb26ef692e5afd5ec8db49ee518613` whenever packed ADT layout, place projections, `Drop`, or `CheckAlignment` are added to Anneal's trusted boundary.
