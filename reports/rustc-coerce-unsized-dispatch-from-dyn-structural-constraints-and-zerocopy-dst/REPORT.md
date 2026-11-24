# CoerceUnsized, DispatchFromDyn Structural Constraints (E0374–E0378), Builtin Unsize Tail-Field Rules (E0277), and Zerocopy KnownLayout DST Construction

## Summary

Rust's unstable unsizing and dynamic-dispatch smart-pointer traits (`core::ops::CoerceUnsized` and `core::ops::DispatchFromDyn`, gated behind `#![feature(coerce_unsized)]` and `#![feature(dispatch_from_dyn)]`) and its built-in dynamically sized type (DST) coercion machinery (`core::marker::Unsize`, `#![feature(unsize)]`) are governed by four compiler subsystems whose structural invariants interlock across coherence checking, well-formedness checking, trait selection, ABI lowering, and SSA codegen:

1. **Structural Uniqueness in `CoerceUnsized` (`E0374`, `E0375`, `E0377`; retired `E0376`)** [normative/source/execution]:
   In `compiler/rustc_hir_analysis/src/coherence/builtin.rs` (`coerce_unsized_info`), a struct impl `CoerceUnsized<S<B..>> for S<A..>` must coerce between the **same** `struct` ADT (`E0377` otherwise, including distinct structs and non-struct ADTs such as `enum`s after legacy error code `E0376` was folded into `E0377`) and, after skipping normalized `core::marker::PhantomData` fields, must have **strictly one** field whose instantiated types differ (`E0374` for `0` differing fields, `E0375` for `>= 2` differing fields), recursively satisfying `CoerceUnsized` (`custom_kind = Some(CustomCoerceUnsized::Struct(i))`).
2. **ABI Newtype Invariance in `DispatchFromDyn` (`E0378`)** [source/execution/derived]:
   `visit_implementation_of_dispatch_from_dyn` permits `&T -> &U` / `*const T -> *const U` / `*mut T -> *mut U` only with identical mutability and lifetimes, and restricts struct impls to Rust/transparent representations (forbidding `#[repr(C)]` and `#[repr(packed)]`, `E0378`) in which every unchanged non-`PhantomData` field has layout `layout.is_1zst() && !ty_a.has_non_region_param()` (`E0378`). Notice that upstream documentation (`E0378.md`) lags implementation: it mentions only `PhantomData` exceptions, whereas `builtin.rs` and live `rustc 1.98.0-nightly` explicitly accept non-generic concrete 1-ZST sibling fields while rejecting over-aligned ZSTs (`#[repr(align(8))]`), non-ZST siblings, and non-`PhantomData` generic 1-ZST wrappers (`Marker<M>`). Downstream `make_thin_self_ptr` (`compiler/rustc_ty_utils/src/abi.rs`) relies on this exact invariant when unwrapping non-pointer receivers with `non_1zst_field(cx)` to pass `self` as `*mut ()` ABI in vtable dispatch thunks, and `rustc_codegen_ssa::base::unsize_ptr` relies on it for in-register `ScalarPair` unsizing.
3. **Tail-Only `?Sized` Prefix-Offset Invariance & Prefix Parameter Capture (`E0277`, `E0308`)** [source/execution]:
   Well-formedness checking (`compiler/rustc_hir_analysis/src/check/wfcheck.rs`) forces all struct fields strictly preceding the final field to implement `Sized` (`E0277`). Built-in `Unsize` confirmation (`compiler/rustc_trait_selection/src/traits/select/confirmation.rs`, `confirm_builtin_unsize_candidate`) delegates structural parameter eligibility to `unsizing_params_for_adt` (`compiler/rustc_ty_utils/src/ty.rs`), which collects generic type/const parameters appearing in the tail field and subtracts every parameter mentioned in any prefix field (`#[repr(Rust)]` or `#[repr(C)]`). Consequently, a struct whose prefix mentions the unsizing type parameter (e.g., `struct PrefixMentionsParam<T: ?Sized> { meta_ptr: *const T, tail: T }`) passes struct well-formedness cleanly yet fails pointer unsizing coercion (`E0308`).
4. **Stable `zerocopy` DST Construction and the `#[repr(C)]` Architectural Duality** [source/execution/derived]:
   Because `CoerceUnsized` and `DispatchFromDyn` remain unstable (`#![feature(...)]`), `google/zerocopy` implements stable slice-DST construction without unstable unsizing traits via `KnownLayout::{LAYOUT, raw_from_ptr_len, pointer_to_metadata}`, `DstLayout::validate_cast_and_convert_metadata`, `Ptr` transmutes/`CastUnsized`, and `Ref::from_bytes_with_elems`. Empirically and in `zerocopy-derive`, deriving slice-DST `KnownLayout` **requires** `#[repr(C)]` (non-`#[repr(C)]` structs fall back to `SelfBounds::SIZED` and fail with `E0277`), creating an exact representation disjointness with `DispatchFromDyn`, which **forbids** `#[repr(C)]` (`E0378`). Both `coerce_unsized` casts and non-fieldless-enum/slice ADTs currently lower to `.unsupported` in `joshlf/anneal` (`trusted/lean/Trusted/MirAst.lean` and `MirSemantics.lean`).
5. **Kernel-Checked Lean v4.34.1 Soundness Proof (`2,906` LOC)** [execution/derived]:
   All four structural theorems—Single-Field Unsize Structural Preservation (`coerceUnsized_single_field_preservation`, `coerceWitness_preserves_ptr_address`), `DispatchFromDyn` ABI Register-Equivalence (`dispatchFromDyn_implies_coerceUnsized`, `dispatchFromDyn_strong_non_1zst`, `dispatchFromDyn_abi_register_equivalence`, `adding_1zst_siblings_preserves_thin_self_ptr`), Tail-Only `?Sized` Prefix-Offset Invariance (`tail_only_unsized_prefix_offset_invariance`, `unsize_preserves_prefix_offsets`), and `zerocopy` DST validation bounds/duality (`validateCast_splitAt_bounds`, `prefix_suffix_splitAt_complement`, `repr_c_duality_disjoint`)—alongside constructive counterexamples for every error code compile under `leanprover/lean4 v4.34.1` (`-DwarningAsError=true -Ddebug.skipKernelTC=false`) with `0` `sorry`, `0` `Classical.choice`, `0` `._unsafe_rec`, `0` forbidden tactics, and MetaM-verified axiom footprint `[propext]` only.

## Applicability

This report documents primary-source compiler behavior, empirical execution receipts, and a clean-room Lean mechanization across six pinned subjects listed in `REPORT.json`:

1. **`rust-lang/rust` source (`f7da9a42368f31abb02b8064bb93a11bf9ba9f5e`)**: Primary source of coherence (`compiler/rustc_hir_analysis/src/coherence/builtin.rs`, `diagnostics.rs`), well-formedness (`wfcheck.rs`), trait selection (`candidate_assembly.rs`, `confirmation.rs`), `unsizing_params_for_adt` (`rustc_ty_utils/src/ty.rs`), call ABI unwrapping (`rustc_ty_utils/src/abi.rs`), SSA unsizing codegen (`rustc_codegen_ssa/src/base.rs`, `mir/rvalue.rs`), `dyn`-compatibility (`dyn_compatibility.rs`), `library/core/src/ops/unsize.rs`, and `compiler/rustc_error_codes/src/error_codes/E037{4,5,7,8}.md`.
2. **`rust-lang/rust` executed toolchain (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly 2026-05-31`, LLVM `22.1.6`, `x86_64-unknown-linux-gnu`)**: Used to compile and run all 17 empirical Rust and `zerocopy` probes in `support/probe_coerce_unsized_dispatch_from_dyn.py` (producing `support/probe_results.json`). A direct line-by-line diff of `compiler/rustc_hir_analysis/src/coherence/builtin.rs` between `1.98.0-nightly` (`14210df0e2`) and `rust-lang/rust` HEAD (`f7da9a4236`) confirms all structural checks for `CoerceUnsized` and `DispatchFromDyn` match; the differences between those revisions are mechanical (`errors::` -> `diagnostics::` module rename, `LangItem` import move to `rustc_attr_ir`, direct `match tcx.as_lang_item(trait_def_id)` dispatch in `check_trait`, `TraitErrors::HasErrors` wrapper, and sibling `CoerceShared`/`Reborrow`/`CoercePointeeValidated` additions). All exact diagnostic outputs emitted by `rustc 1.98.0-nightly` are preserved verbatim in `support/probe_results.json`, and documentation drift (`E0378.md` lagging `builtin.rs`) is recorded explicitly under Findings.
3. **`google/zerocopy` (`907b9175fee081872ec883ca4709e6ad922f8ed0`, crate `zerocopy 0.8.64`, edition `2021`) & `google/zerocopy` `main` HEAD (`e05af9265ec8521e8c187dfde4e1bf5650b9d800`)**: Probe execution compiled the `zerocopy` and `zerocopy-derive` workspace at `907b9175fee08`; a live GitHub compare between `907b9175fee08` and `e05af9265ec85` confirms `110` intervening commits touched only repository CI/tools/Anneal subtrees and top-level editor/style config dotfiles, with **zero diffs** inside `zerocopy/` or `zerocopy-derive/`.
4. **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)**: Audited specifically at `trusted/lean/Trusted/MirAst.lean` and `trusted/lean/Trusted/MirSemantics.lean` to determine current verified-MIR lowering coverage for `Rvalue::Cast` and unsized ADTs/slices.
5. **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`)**: Kernel and MetaM auditor used to verify `support/CoerceUnsizedDispatchFromDynStructuralSoundness.lean`.

### Relationship to Peer Corpus Reports

This package sits cleanly alongside three published `reference-corpus/1` reports without duplicating their specialized analyses:
- `custom-unsized-types-coerce-unsized-vtable-metadata-and-gat-lifetime-variance` analyzes custom smart-pointer GAT variance and vtable metadata projection hazards; the present report complements it by auditing and mechanizing the full coherence gate (`builtin.rs`), downstream `make_thin_self_ptr` / `unsize_ptr` register-pair invariants, and all diagnostic separation boundaries (`E0374`–`E0378`).
- `zerocopy-knownlayout-slicedst-rounding-phase-and-split-at-padding-overlap` establishes the core `DstLayout` rounding-phase algebra and `split_at` tail-padding overlap hazard; the present report incorporates the post-fix normalized `size_base`/`size_phase` formula (`layout.rs:734-773`, `1705-1852`) into our verified Lean theorem suite (`validateCast_splitAt_bounds`, `prefix_suffix_splitAt_complement`) and links `zerocopy`'s `#[repr(C)]` slice-DST derive requirement to the `DispatchFromDyn` representation ban (`#[repr(C)]` duality).
- `repr-packed-unaligned-references-slice-dst-alignment-and-cell-projections` characterizes packed-field references and `Cell` projection constraints; here we isolate specifically how `#[repr(packed)]` is explicitly barred from `DispatchFromDyn` (`builtin.rs:364-366`) and how packed tail DST drops interact with `wfcheck.rs:1056-1065`.

Results apply to custom DSTs (arrays/slices and `dyn Trait` trait objects), arbitrary wrapper structs implementing `CoerceUnsized`/`DispatchFromDyn`, and `zerocopy` slice-DST types on `64`-bit pointer architectures where thin pointers are `1` machine word (`8` bytes) and wide pointers are `2`-word scalar pairs (`16` bytes), and exclude unstable `ptr_metadata` custom thin-metadata `Pointee` variants beyond slice lengths and trait vtables.

## Findings

### 1. Builtin Coherence Checking for `CoerceUnsized` and `DispatchFromDyn`

#### 1.1 Trait Dispatch Entry Point (`builtin.rs`)
Evidence role: **source**.

In `compiler/rustc_hir_analysis/src/coherence/builtin.rs`, HIR coherence validates every explicit `impl` of built-in lang-item marker traits via `check_trait` (`f7da9a42:32-54`):
- `LangItem::CoerceUnsized` routes to `visit_implementation_of_coerce_unsized` (`f7da9a42:248-256`), which forces `tcx.ensure_result().coerce_unsized_info(impl_did)` (`f7da9a42:655-888`) purely for its validation side-effects and cached `CoerceUnsizedInfo { custom_kind }` metadata consumed later by codegen.
- `LangItem::DispatchFromDyn` routes to `visit_implementation_of_dispatch_from_dyn` (`f7da9a42:287-469`), which **first** iterates `tcx.for_each_relevant_impl(LangItem::CoerceUnsized, source, ...)` (`f7da9a42:306-313`) to ensure any present `CoerceUnsized` impl on `source` does not fail before emitting independent `DispatchFromDyn` errors, and then runs its stricter layout/representation checks. Notice that when `source` omits `CoerceUnsized` altogether, `for_each_relevant_impl` visits zero impls (`res` stays `Ok(())`), so `DispatchFromDyn` checking still runs independently (`f7da9a42:330-469`).

Both coherence queries instantiate the impl's trait ref via `instantiate_identity().skip_norm_wip()` and inspect `source` vs `target` (`trait_ref.args.type_at(1)`). Crucially, `builtin.rs` matches on **syntactic equality `ty_a == ty_b`** rather than subtyping/projection equivalence (commented explicitly at `f7da9a42:803-814` and `397-398` to avoid computing variance or constraining opaque types during coherence).

#### 1.2 Pointer, Reference, and Pattern Base Cases (`check_mutbl` vs Strict Equality)
Evidence role: **source** + **normative**.

Comparing the non-ADT arms reveals why `CoerceUnsized` accepts coercions that `DispatchFromDyn` rejects (`libcore/src/ops/unsize.rs:40-77, 126-137`):

| Arm `(source.kind(), target.kind())` | `coerce_unsized_info` (`builtin.rs:698-727`) | `visit_implementation_of_dispatch_from_dyn` (`builtin.rs:331-348`) | Emitted Nested Obligation |
| :--- | :--- | :--- | :--- |
| `(&ty::Pat(ty_a, pat_a), &ty::Pat(ty_b, pat_b))` | Requires `pat_a == pat_b` (`CoerceSamePatKind`); `custom_kind = None` | Requires `pat_a == pat_b` (`CoerceSamePatKind`) and returns `Ok(())` directly without a recursive field obligation | `ty_a: CoerceUnsized<ty_b>` (for `CoerceUnsized`; immediate `Ok(())` in `DispatchFromDyn`) |
| `(&ty::Ref(r_a, ty_a, mut_a), &ty::Ref(r_b, ty_b, mut_b))` | `infcx.sub_regions(RelateObjectBound, r_b, r_a)` (`'b: 'a` contravariant shortening) AND `check_mutbl(mut_a, mut_b)` (`mut_a >= mut_b`) | Requires **exact equality** `r_a == *r_b && mut_a == *mut_b` (no lifetime shortening, no `&mut -> &`); rejects mismatch with `E0377` (`CoerceUnsizedNonStruct` fallback!) | `ty_a: Unsize<ty_b>` (`CoerceUnsized`), early `Ok(())` in `DispatchFromDyn` |
| `(&ty::Ref(_, ty_a, mut_a), &ty::RawPtr(ty_b, mut_b))` | Permitted when `mut_a >= mut_b` (`&mut T -> *mut/*const U`, `&T -> *const U`) | **Rejected** (falls through to `_ => CoerceUnsizedNonStruct` `E0377`) | `ty_a: Unsize<ty_b>` (for `CoerceUnsized`) |
| `(&ty::RawPtr(ty_a, mut_a), &ty::RawPtr(ty_b, mut_b))` | Permitted when `mut_a >= mut_b` (`*mut -> *const`, eq mut) | Requires **exact equality** `a_mutbl == b_mutbl` (`*mut -> *const` rejected with `E0377`) | `ty_a: Unsize<ty_b>` (early `Ok(())` in `DispatchFromDyn`) |

In `coerce_unsized_info` (`f7da9a42:680-696`), `check_mutbl` checks `if mt_a.mutbl < mt_b.mutbl`, reporting a type mutability mismatch (`*const T -> *mut U` or `&T -> &mut U`), then generates nested `ty_a: Unsize<ty_b>`. Meanwhile, `visit_implementation_of_dispatch_from_dyn` rejects region subtyping or reference-to-raw-ptr conversions because method dispatch thunks (`self: Rc<Self>`) require the caller and callee receiver types to match structurally up to the trait-object unsizing step (`dyn_compatibility.rs:649-695`).

#### 1.3 Struct Constraints, `PhantomData` vs `1-ZST`, and Error Codes (`E0374`–`E0378`)
Evidence role: **source** + **execution** + **documentation**.

For `(&ty::Adt(def_a, args_a), &ty::Adt(def_b, args_b))`, BOTH `coerce_unsized_info` (`f7da9a42:729-855`) and `visit_implementation_of_dispatch_from_dyn` (`f7da9a42:349-468`) gate first on `if def_a.is_struct() && def_b.is_struct()`:

1. **Non-Struct ADTs (`enum` / `union`) & Retired `E0376`**:
   When either `def_a` or `def_b` is an `enum` or `union`, the pattern guard `def_a.is_struct() && def_b.is_struct()` fails and execution falls through to the catch-all arm (`f7da9a42:851-855` / `468`), emitting `diagnostics::CoerceUnsizedNonStruct` (`diagnostics.rs:1466-1472`), whose diagnostic attribute is **`code = E0377`** (`"the trait \`{$trait_name}\` may only be implemented for a coercion between structures"`). Legacy error `E0376` (`compiler/rustc_error_codes` historical enum/union diagnostic) no longer exists in `rustc_hir_analysis::diagnostics` or `coherence/builtin.rs` and emits `E0377` at compile time (`non_struct_enum_rejected_e0377_formerly_e0376`, Probe 6). Note the subtle user-facing difference between the two `E0377` structs in `diagnostics.rs:1466-1496`:
   - `CoerceSameStruct` (`L1485-1496`, emitted when `def_a != def_b` between two structs at `builtin.rs:732-742` & `352-362`) includes `note: true` (`"expected coercion between the same definition; expected \`{$source_path}\`, found \`{$target_path}\`"`).
   - `CoerceUnsizedNonStruct` (`L1466-1472`, emitted when an `enum`/`union`/tuple/etc. falls into `_ =>` at `builtin.rs:851-855` & `468`) emits **`E0377`** *without* that same-definition note.

2. **`#[repr(C)]` and `#[repr(packed)]` Ban in `DispatchFromDyn` (`E0378`)**:
   Immediately after verifying `def_a == def_b`, `visit_implementation_of_dispatch_from_dyn` checks (`f7da9a42:364-366`):
   ```rust
   if def_a.repr().c() || def_a.repr().packed() {
       return Err(tcx.dcx().emit_err(diagnostics::DispatchFromDynRepr { span }));
   }
   ```
   `DispatchFromDynRepr` (`diagnostics.rs:1202-1203`) emits **`E0378`**: `"structs implementing \`DispatchFromDyn\` may not have \`#[repr(packed)]\` or \`#[repr(C)]\`"`. Crucially, **`CoerceUnsized` has NO representation restriction** (`#[repr(C)]` and `#[repr(packed)]` structs freely implement `CoerceUnsized`), which we verified directly in Probes 10–11 where both `impl CoerceUnsized` succeeded and only `impl DispatchFromDyn` was rejected. The reason is ABI-level: Rust assumes `DispatchFromDyn` wrappers satisfy Rust's `#[repr(transparent)]`-equivalent ABI around a single scalar/scalar-pair pointer (`builtin.rs:322-329`), whereas `#[repr(C)]` changes aggregate pass-by-value ABI rules across platform calling conventions (e.g., SysV `TwoScalar` vs memory struct passing, or suppressing field reordering / layout collapsing) and `#[repr(packed)]` can demote alignment / prevent register scalar-pair equivalence.

3. **Two-Stage Field Filtering (`PhantomData` FIRST, then `ty_a == ty_b`, then `is_1zst && !has_non_region_param`)**:
   In `coerce_unsized_info` (`builtin.rs:784-820`), every field `f` in `def_a.non_enum_variant().fields` is processed as follows:
   - Normalize `tcx.type_of(f.did).instantiate_identity()` with `TypingEnv::non_body_analysis(tcx, def_a.did())`; if `.is_phantom_data()` is `true`, **ignore the field** (`return None`).
   - Otherwise compare instantiated `a == b`; if syntactically equal, ignore the field (`return None`).
   - Otherwise push `(i, a, b, span)` to `diff_fields`.
   Notice that **any non-differing non-`PhantomData` field**—including `u32`, `[u8; 8]`, `Align8Zst`, or generic `Marker<M>`—is silently allowed by `CoerceUnsized`!

   In `visit_implementation_of_dispatch_from_dyn` (`builtin.rs:378-423`), field filtering differs sharply when `ty_a == ty_b`:
   - First, normalize `tcx.type_of(field.did).instantiate_identity()`; if `.is_phantom_data()` is `true`, **ignore the field immediately** (`L382-392`) — even if `PhantomData<M>` mentions a generic parameter `M`!
   - Otherwise, if `ty_a == ty_b` (`L398`):
     - Compute `tcx.layout_of(infcx.typing_env(param_env).as_query_input(ty_a))` (`L403-404`).
     - Accept and skip **only if** `layout.is_1zst() && !ty_a.has_non_region_param()` (`L405-409`).
     - Otherwise emit `diagnostics::DispatchFromDynZST` (`code = E0378`, `diagnostics.rs:1326-1328`) naming `"ZST fields with 1 byte alignment that don't mention type/const generics, and nothing else"`.
   - Look carefully at the **generic `PhantomData` vs wrapper 1-ZST boundary** established by reading `L382-416` alongside `rustc`'s comment at `L399-402`:
     Direct `PhantomData<T>` or `PhantomData<M>` is bypassed by `is_phantom_data()` at `L389` *before* `!ty_a.has_non_region_param()` runs (`L406`). By contrast, a user-defined 1-ZST struct wrapping `PhantomData`, such as `struct Marker<M>(PhantomData<fn() -> M>)`, returns `is_phantom_data() == false`, enters `L398`, passes `layout.is_1zst() == true`, and **fails `!ty_a.has_non_region_param()`** at `L406`, emitting **`E0378`** (`dispatch_from_dyn_generic_1zst_rejected_e0378`, Probe 9). Meanwhile a concrete non-generic 1-ZST `struct UnitTag;` (and even `TaggedPtr<T: ?Sized>(*const T, UnitTag, PhantomData<T>)`) **passes both `CoerceUnsized` and `DispatchFromDyn`** and dispatches dynamically (`TAGGED_DYN_DISPATCH=77`, Probe 2).

   **Documentation Drift Finding (`E0378.md`)** [documentation vs source]:
   `compiler/rustc_error_codes/src/error_codes/E0378.md:21-24` states:
   > *"the struct must have only one field (except for `PhantomData`), and that field must itself implement `DispatchFromDyn`."*
   That prose is incomplete in two concrete ways relative to `builtin.rs` and `diagnostics.rs:1202, 1326`: (a) it omits concrete non-generic 1-ZST fields (`UnitTag`) accepted since commit additions modeled at `L403-410`, and (b) it omits the `#[repr(C)]` / `#[repr(packed)]` prohibition (`L364-366`).

4. **Field Cardinality Check (`E0374` vs `E0375` vs Recursive Obligation)**:
   Both `coerce_unsized_info` (`L822-848`) and `visit_implementation_of_dispatch_from_dyn` (`L426-466`) check the collected slice length:
   - `len == 0` -> `diagnostics::CoerceNoField` (**`E0374`**)
   - `len == 1` -> verify recursive `a: CoerceUnsized<b>` (`L858-886`, returning `CustomCoerceUnsized::Struct(i)`) or `ty_a: DispatchFromDyn<ty_b>` (`L432-458`); note that if the `#[derive(CoercePointee)]` macro (`is_from_coerce_pointee_derive`) emitted the impl, recursive fulfillment failures rewrite to `diagnostics::CoerceFieldValidity` (`L442-449`, `L871-878`). Note an asymmetry: `rustc` has **no** separate `E0374`/`E0375`-like distinction for `ty_a == ty_b` when `CoerceUnsized` succeeds on a struct with an extra `u32` (Probe 7) — `CoerceUnsized` ignores unchanged `u32` and succeeds, while `DispatchFromDyn` rejects unchanged `u32` via `DispatchFromDynZST` (`E0378`), not `E0374`.
   - `len > 1` -> `diagnostics::CoerceMulti` (**`E0375`**).

### 2. Why These Rules Exist: `make_thin_self_ptr` ABI and SSA Coercion Codegen

#### 2.1 Dynamic Dispatch Thunk ABI (`compiler/rustc_ty_utils/src/abi.rs`)
Evidence role: **source**.

Why does `DispatchFromDyn` allow **only** 1-ZST non-generic extra fields and ban `#[repr(C)]` / `#[repr(packed)]`, whereas `CoerceUnsized` allows arbitrary fields and `#[repr(C)]`? The answer sits in `make_thin_self_ptr` (`compiler/rustc_ty_utils/src/abi.rs:696-739`):

```rust
let mut wide_pointer_layout = layout;
while !wide_pointer_layout.ty.is_raw_ptr() && !wide_pointer_layout.ty.is_ref() {
    wide_pointer_layout = wide_pointer_layout
        .non_1zst_field(cx)
        .expect("not exactly one non-1-ZST field in a `DispatchFromDyn` type")
        .1
}
wide_pointer_layout.ty
```
And then `make_thin_self_ptr` replaces that unwrapped type's `TyAndLayout` fields with the layout of `*mut ()` (`unit_ptr_ty`, `L730-738`) while keeping `ty: wide_pointer_ty`!
Look at the **exact invariants** `make_thin_self_ptr` assumes without checking:
1. For a `Sized` `self` receiver (`!layout.is_unsized()`, `L705-709`), `layout.backend_repr` is asserted to be `BackendRepr::ScalarPair { .. } | BackendRepr::Scalar(..)`, otherwise **`bug!("receiver type has unsupported layout: {:?}", layout)`**! That immediately explains the `#[repr(C)]` and `#[repr(packed)]` ban: under C ABI rules, a multi-field or wrapped struct (or packed type whose scalar alignment differs) is not guaranteed to share `#[repr(transparent)]`-equivalent `ScalarPair`/`Scalar` ABI lowering with its sole non-1-ZST pointer field.
2. Inside the `while` loop (`L717-722`), every wrapper layer that is not already a raw pointer or reference **must** satisfy `.non_1zst_field(cx).is_some()`—meaning **strictly one** field is not a 1-ZST, and peeling that field recursively reaches a built-in `&T`, `&mut T`, `*const T`, or `*mut T`. If two non-1-ZST fields existed (or zero existed!), `.expect(...)` would ICE the compiler. `DispatchFromDyn`'s coherence check (`visit_implementation_of_dispatch_from_dyn`) statically discharges every precondition of `make_thin_self_ptr`: `repr` exclusion guarantees transparent ABI matching, `len == 1` differing field guarantees termination toward a primitive ref/ptr via recursive `DispatchFromDyn`, and `is_1zst()` on every other non-`PhantomData` field (while `PhantomData` itself is a 1-ZST) guarantees `non_1zst_field(cx)` uniquely selects that single coerced field!

#### 2.2 SSA Unsizing Codegen (`rustc_codegen_ssa/src/base.rs` & `mir/rvalue.rs`)
Evidence role: **source**.

Downstream MIR codegen (`compiler/rustc_codegen_ssa/src/mir/rvalue.rs:139-184, 564-570`) splits `Rvalue::Cast(PointerCoercion::Unsize, source, _)` into two codegen paths based on `dest.layout.backend_repr`:

1. **Fast Register/ScalarPair Path (`base::unsize_ptr`, `base.rs:221-264`)**:
   Triggered whenever `dest.layout.backend_repr` is `BackendRepr::ScalarPair { .. }` (`rvalue.rs:146, 564-570`). For ADT smart pointers (`base.rs:236-261`), `unsize_ptr` iterates `0..src_layout.fields.count()`, skips `src_f.is_1zst()`, asserts `offset == 0`, `src_layout.size == src_f.size`, `src_f.ty != dst_f.ty`, and `result == None` (`L251-258`), and computes the new `(data_ptr, meta)` pair purely in registers! Even a `#[repr(Rust)]` struct implementing only `CoerceUnsized` with 1-ZST fields takes this fast path if its layout reduces to `ScalarPair`.
2. **General Structural Copy Path (`base::coerce_unsized_into`, `base.rs:268-313`)**:
   Triggered whenever `dest.layout.backend_repr` is **not** `ScalarPair`—exactly the case for nontrivial `CoerceUnsized` structs carrying extra non-ZST fields (such as `struct WithTag<T: ?Sized>(*const T, u32)`) or `#[repr(C)]` structs! If `operand` is `Immediate` or `Pair`, codegen allocates a scratch `PlaceRef::alloca` (`rvalue.rs:168-172`), stores `operand`, and invokes `base::coerce_unsized_into(bx, src, dst)`:
   - For ADTs (`base.rs:292-310`), `coerce_unsized_into` loops over every field index `i` in `FIRST_VARIANT`:
     - Skips ZST fields (`if dst_f.layout.is_zst() { continue; }`, `L299-302`).
     - If `src_f.layout.ty == dst_f.layout.ty`, performs a **typed bitwise copy** `bx.typed_place_copy(dst_f.val, src_f.val, src_f.layout)` (`L304-305`).
     - For the unique field with `src_f.layout.ty != dst_f.layout.ty`, recurses `coerce_unsized_into(bx, src_f, dst_f)` (`L307`), eventually calling `unsize_ptr` on the leaf raw pointer/reference (`L283-289`).

Notice an instructive interaction with `builtin.rs`: `coerce_unsized_into` compares **monomorphized layout types** (`src_f.layout.ty == dst_f.layout.ty`, `L304`), whereas coherence (`builtin.rs:812`) compared **unmonomorphized generic fields** (`a == b`), AND codegen does not inspect `CustomCoerceUnsized::Struct(i)` directly here because monomorphized field type inequality (`!=`) rediscovers the unique differing non-ZST field guaranteed to exist by `coerce_unsized_info`!

### 3. Builtin `Unsize` Tail-Only `?Sized` Well-Formedness and Prefix Parameter Exclusion

#### 3.1 `wfcheck.rs`: Only the Final Field May Be `?Sized` (`E0277`)
Evidence role: **source** + **execution**.

In `compiler/rustc_hir_analysis/src/check/wfcheck.rs:1056-1091` (`check_variances_for_type_defn` / struct field WF check):
- `all_sized` is `false` for `struct` definitions (except unions/enums or `#[repr(packed)]` with a `Drop` tail, `needs_drop_copy`, `L1056-1065`), setting `let unsized_len = if all_sized { 0 } else { 1 };` (`L1066`).
- Every field in `variant.fields.raw[..variant.fields.len() - unsized_len]` receives a mandatory `Sized` obligation (`wfcx.register_bound(..., LangItem::Sized)`, `L1068-1091`).
- Consequently, placing `?Sized` parameter `T` in a non-final field (`BadFirst<T: ?Sized> { head: T, tail: u32 }`, Probe 13) or in multiple fields (`BadTwo<T: ?Sized> { a: T, b: T }`, Probe 14) immediately triggers **`E0277`**: *"only the last field of a struct may have a dynamically sized type"*.
- Because all prefix fields are `Sized`, all prefix field layouts and byte offsets depend **strictly** on types occurring in the prefix fields—guaranteeing that for `Packet<T: ?Sized> { hdr: u32, tag: u16, payload: T }` (`#[repr(C)]`, Probe 12), `offset_of!(Packet<[u8; 4]>, hdr) == 0`, `offset_of!(..., tag) == 4`, and `offset_of!(..., payload) == 6` hold identically before and after unsizing `&Packet<[u8; 4]> -> &Packet<[u8]>`.

#### 3.2 `ty.rs` & `confirmation.rs`: Prefix-Param Subtraction (`E0308` Trap)
Evidence role: **source** + **execution**.

Passing `wfcheck.rs` is **necessary but NOT sufficient** for `Struct<A>: Unsize<Struct<B>>`. Builtin candidate assembly (`compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:1083-1106`) assembles `BuiltinUnsizeCandidate` whenever `(ty::Array(..), ty::Slice(_))`, `(_, ty::Dynamic(..))`, or `(&ty::Adt(def_id_a, _), &ty::Adt(def_id_b, _)) if def_id_a.is_struct() && def_id_a == def_id_b`, plus `TraitUpcastingUnsizeCandidate`. Then confirmation (`compiler/rustc_trait_selection/src/traits/select/confirmation.rs:1108-1165`) checks:
1. Queries `let unsizing_params = tcx.unsizing_params_for_adt(def.did());` (`L1109`); if empty, returns `Err(SelectionError::Unimplemented)`.
2. Look at `unsizing_params_for_adt` (`compiler/rustc_ty_utils/src/ty.rs:305-347`):
   - Splits `let Some((tail_field, prefix_fields)) = def.non_enum_variant().fields.raw.split_last()` (`L325`).
   - Walks the unnormalized identity type of `tail_field`, inserting every `ty::Param(p)` or `ty::ConstKind::Param(p)` (ignoring lifetimes) into `unsizing_params` (`L329-334`).
   - **Walks every `field in prefix_fields` (`L338-344`) and calls `unsizing_params.remove(i)` for any type/const param mentioned anywhere inside a prefix field**—even behind an indirection (`*const T`, `&T`, `PhantomData<T>`) that *itself* is `Sized`!
3. Replaces parameters in `args_a` with `args_b[i]` ONLY where `unsizing_params.contains(i as u32)` (`confirmation.rs:1142-1144`), equates `target == new_struct` (`L1146-1150`), and emits the single nested obligation `source_tail: Unsize<target_tail>` (`L1154-1162`).

**Subtle Edge Case Verified Live (`PrefixMentionsParam`, Probe 15)**:
```rust
struct PrefixMentionsParam<T: ?Sized> {
    meta_ptr: *const T, // Sized! Passes wfcheck (no E0277).
    tail: T,            // Last field! Also passes wfcheck.
}
```
Why does `&PrefixMentionsParam<[u8; 4]> -> &PrefixMentionsParam<[u8]>` compile-fail with **`error[E0308]: mismatched types`** (Probe 15)? Because `*const [u8; 4]` is `8` bytes (thin pointer) whereas `*const [u8]` is `16` bytes (wide pointer)! Unsizing coercion preserves non-tail bytes bit-for-bit without rewriting interior prefix pointers (`unsizing_params.remove(0)` empties `unsizing_params` -> `SelectionError::Unimplemented` -> coercion falls through to `E0308`). Thus `rustc` avoids creating dangling/corrupted wide-pointer prefixes—a crucial soundness boundary confirmed cleanly in both source, execution, and Lean (`prefix_mentions_param_wf_ok_yet_unsize_rejected`).

### 4. Empirical `rustc 1.98.0-nightly` & `zerocopy 0.8.64` Probe Matrix

Evidence role: **execution** (`support/probe_coerce_unsized_dispatch_from_dyn.py` + `support/probe_results.json`, `17` probes executed cleanly on `rustc 1.98.0-nightly 14210df0e2` and offline Cargo against `zerocopy 907b9175fee0`).

| Probe # | Probe Key | Rule / Scenario Tested | Expected & Observed Outcome | Exact Stdout / Diagnostic Code |
| :---: | :--- | :--- | :--- | :--- |
| 1 | `valid_myptr_coerce_unsized_and_dispatch_from_dyn` | `MyPtr<T: ?Sized>(*const T)` unsizing to `[u8]`, `dyn Display`, and `dyn Measure` method call | Compile `rc=0`, Run `rc=0` | `UNSIZE_SLICE=4 UNSIZE_DYN=42 DYN_DISPATCH=99` |
| 2 | `valid_dispatch_from_dyn_non_generic_1zst_sibling` | `TaggedPtr<T: ?Sized>(*const T, UnitTag, PhantomData<T>)` dynamic dispatch | Compile `rc=0`, Run `rc=0` | `TAGGED_DYN_DISPATCH=77` |
| 3 | `zero_unsizable_fields_rejected_e0374` | `Zero<T: ?Sized>(PhantomData<T>, u32)` `impl CoerceUnsized` | Compile `rc=1` | `error[E0374]` (`"expected a single field to be coerced, none found"`) |
| 4 | `two_unsizable_fields_rejected_e0375` | `Two<T: ?Sized>(*const T, *const T)` `impl CoerceUnsized` | Compile `rc=1` | `error[E0375]` (`"does not allow multiple fields to be coerced"`) |
| 5 | `distinct_structs_rejected_e0377` | `CoerceUnsized<PtrB<U>> for PtrA<T>` | Compile `rc=1` | `error[E0377]` (`note: expected coercion between the same definition; expected PtrA, found PtrB`) |
| 6 | `non_struct_enum_rejected_e0377_formerly_e0376` | `enum EnumPtr<T: ?Sized> { Ptr(*const T) }` `impl CoerceUnsized` | Compile `rc=1` | `error[E0377]` (`CoerceUnsizedNonStruct`; legacy `E0376` folded into `E0377`) |
| 7 | `dispatch_from_dyn_extra_field_rejected_e0378` | `BadDyn<T: ?Sized>(*const T, u32)`: `CoerceUnsized` OK, `DispatchFromDyn` rejected | Compile `rc=1` | `error[E0378]` (`note: extra field \`1\` of type \`u32\` is not allowed`) |
| 8 | `dispatch_from_dyn_overaligned_zst_rejected_e0378` | `#[repr(align(8))] struct Align8Zst` sibling in `BadDynAlign<T>`: `CoerceUnsized` OK, `DispatchFromDyn` rejected | Compile `rc=1` | `error[E0378]` (`note: extra field \`1\` of type \`Align8Zst\` is not allowed`) |
| 9 | `dispatch_from_dyn_generic_1zst_rejected_e0378` | `struct Marker<M>(PhantomData<fn() -> M>)` 1-ZST wrapper sibling: `CoerceUnsized` OK, `DispatchFromDyn` rejected | Compile `rc=1` | `error[E0378]` (`note: extra field \`1\` of type \`Marker<M>\` is not allowed`) |
| 10 | `dispatch_from_dyn_repr_c_rejected_e0378` | `#[repr(C)] struct BadRepr<T: ?Sized>(*const T)`: `CoerceUnsized` OK, `DispatchFromDyn` rejected | Compile `rc=1` | `error[E0378]` (`structs implementing \`DispatchFromDyn\` may not have \`#[repr(packed)]\` or \`#[repr(C)]\``) |
| 11 | `dispatch_from_dyn_repr_packed_rejected_e0378` | `#[repr(packed)] struct BadPacked<T: ?Sized>(*const T)`: `CoerceUnsized` OK, `DispatchFromDyn` rejected | Compile `rc=1` | `error[E0378]` (`structs implementing \`DispatchFromDyn\` may not have \`#[repr(packed)]\` or \`#[repr(C)]\``) |
| 12 | `custom_dst_tail_unsizing_ok` | `#[repr(C)] struct Packet<T: ?Sized> { hdr: u32, tag: u16, payload: T }` unsized coercion | Compile `rc=0`, Run `rc=0` | `PACKET_LEN=4 HDR=7 OFF_HDR=0 OFF_TAG=4 OFF_PAYLOAD=6` |
| 13 | `custom_dst_non_last_unsized_field_rejected_e0277` | `struct BadFirst<T: ?Sized> { head: T, tail: u32 }` + coercion | Compile `rc=1` | `error[E0277]` (`only the last field of a struct may have a dynamically sized type`) + `error[E0308]` |
| 14 | `custom_dst_two_unsized_fields_rejected_e0277` | `struct BadTwo<T: ?Sized> { a: T, b: T }` + coercion | Compile `rc=1` | `error[E0277]` + `error[E0308]` |
| 15 | `custom_dst_prefix_mentions_param_rejected` | `struct PrefixMentionsParam<T: ?Sized> { meta_ptr: *const T, tail: T }` | Compile `rc=1` | `error[E0308]` ONLY (`wfcheck` passed!) |
| 16 | `zerocopy_known_layout_ref_from_bytes_with_elems_dst` | `Ref::<&[u8], [u32]>::from_bytes_with_elems`, `from_prefix_with_elems`, `from_suffix_with_elems`, error cases | Compile `rc=0`, Run `rc=0` | `ZC_DST_LEN=3 ZC_META=3 ZC_SUM=60 PREF_REST=8 SUFF_HEAD=8 SIZE_ERR=true ALIGN_ERR=true ZERO_SUFF_ERR=true` |
| 17 | `zerocopy_derive_custom_dst_packet` | `#[derive(KnownLayout)] #[repr(C)] struct Packet` (`elems=5` vs `elems=4` tail-padding multiplicity), `Ptr::transmute` `Cell`/`UnsafeCell`, vs non-`#[repr(C)]` negative | Run `rc=0`, Neg `rc=101` | Pos: `ZC_CUSTOM_DST_META5=5 META4=4 HDR=7 TAG=4660 SUM5=150 SUM4=100 BYTES_LEN=16 UCELL_META=3`; Neg: `error[E0277]` (`Sized is not implemented for [u16]`) |

### 5. `zerocopy` Stable Slice-DST Construction and the `#[repr(C)]` Structural Duality

#### 5.1 How `zerocopy` Constructs Wide DSTs Without Unstable `CoerceUnsized`
Evidence role: **source** + **execution**.

Rather than relying on unstable `CoerceUnsized` or custom thin-to-wide coercions (aside from stable array-to-slice unsizing for `[T; N]`), `google/zerocopy` abstracts slice-DST construction safely on stable Rust through `KnownLayout` (`zerocopy/src/lib.rs:748-815, 1130-1137`):
- `KnownLayout::PointerMetadata` fixes metadata types on stable Rust (`()` for `Sized` types, `usize` for `[T]` and structs with trailing `[T]`).
- `KnownLayout::raw_from_ptr_len(bytes: NonNull<u8>, meta: Self::PointerMetadata) -> NonNull<Self>` constructs a wide pointer cleanly via stable `ptr::slice_from_raw_parts_mut` plus pointer `.cast::<Self>()` (or for custom `#[derive(KnownLayout)] #[repr(C)]` DSTs, computing the exact trailing slice length).
- `KnownLayout::pointer_to_metadata(ptr: *mut Self) -> Self::PointerMetadata` extracts dynamic metadata without unstable `core::ptr::metadata` (`L812, 1137`).
- `Ref::from_bytes_with_elems(source: B, count: usize)` (`zerocopy/src/ref.rs:736-776`) validates **both** exact byte length (`T::size_for_metadata(count)`) and dynamic pointer validation (`Ptr::from_ref(source.deref()).try_cast_into_no_leftover::<T, BecauseImmutable>(Some(count))`) before calling `Ref::new_unchecked(source, count)`. Note how `CastError::Size` and `CastError::Alignment` fire cleanly in Probe 16: `from_bytes_with_elems(&aligned.0[..12], 4)` returns `Err(CastError::Size)` (`SIZE_ERR=true`), `from_bytes_with_elems(&aligned.0[1..13], 3)` returns `Err(CastError::Alignment)` (`ALIGN_ERR=true`), and `Ref::from_suffix_with_elems(&aligned.0[..13], 0)` rejects even a **zero-element** `[u32]` suffix cast with `Err(CastError::Alignment)` (`ZERO_SUFF_ERR=true`) because its end address `addr + 13` violates `align_of::<u32>() == 4` (`layout.rs:1768-1780`).

- Furthermore, `zerocopy::pointer::cast::CastUnsized` (`zerocopy/src/pointer/mod.rs:178-231`) enables size-and-alignment-preserving zero-cost casts between distinct `KnownLayout` DSTs sharing identical `PointerMetadata`, guarded by a compile-time `static_assert!` verifying matching `align`, `trailing.offset`, and `src_trailing.has_same_size_sequence(dst_trailing)` (`L194-206`), followed by `Src::pointer_to_metadata` + `Dst::raw_from_ptr_len` (`L208-209`). Probe 17 exercises the `KnownLayout` transparent wrapper chain `UnpaddedPacket -> Cell<UnpaddedPacket> -> UnsafeCell<UnpaddedPacket>` via `Ptr::transmute` (`UCELL_META=3`, `BYTES_LEN=16`).

#### 5.2 Normalized Rounding Phase & `split_at` Complementarity
Evidence role: **source** + **execution** + **derived**.

In `zerocopy/src/layout.rs:734-773` and `1705-1852`, `DstLayout::validate_cast_and_convert_metadata(addr, bytes_len, cast_type)` computes `(elems, split_at)` using a **normalized** phase representation `(size_base, size_phase)` modulo `size_align`:
- `trailing.max_trailing_bytes(bytes_len)` returns `Some(max_rounded_bytes - size_phase)` when `bytes_len >= min_aligned_size`.
- `elems = max_slice_bytes / elem_size`, `unused_bytes = max_slice_bytes % elem_size`, `unused_aligned_bytes = round_down(unused_bytes, size_align)`, `max_rounded_bytes = round_down(bytes_len - size_base, size_align)`, and `self_bytes = size_base + (max_rounded_bytes - unused_aligned_bytes)` (`L1821-1834`).
- `split_at` is `self_bytes` for `CastType::Prefix` and `bytes_len - self_bytes` for `CastType::Suffix` (`L1840-1849`).

Look closely at **padding-absorption multiplicity** verified both live in Probe 17 and in Lean (`packet_dst_elems5_vs_elems4_witness`):
For `#[repr(C)] struct Packet { hdr: u32, tag: u16, payload: [u16] }`:
- `prefix_size = 6`, `prefix_align = 4`, `elem_size = 2`, `elem_align = 2`, `align = max(4, 2) = 4`.
- On a `16`-byte buffer (`aligned.0`, 4-byte aligned):
  - With `elems = 5`: `size = round_up(6 + 5 * 2, 4) = round_up(16, 4) = 16` -> **`from_bytes_with_elems(&buf, 5)` succeeds** (`META5=5`, `SUM5=150`).
  - With `elems = 4`: `size = round_up(6 + 4 * 2, 4) = round_up(14, 4) = 16` -> **`from_bytes_with_elems(&buf, 4)` ALSO succeeds** on the exact same `16`-byte slice (`META4=4`, `SUM4=100`), because the remaining 2 bytes are absorbed as trailing struct alignment padding!
  - Meanwhile `validate_cast_and_convert_metadata(..., Prefix)` maximizes whole elements (`elems = 5`, `split_at = 16`).

#### 5.3 The Structural `#[repr(C)]` Duality (`zerocopy-derive` vs `DispatchFromDyn`)
Evidence role: **source** + **execution** + **derived**.

Inspecting `zerocopy/zerocopy-derive/src/derive/known_layout.rs:252-292` establishes a sharp, mathematically disjoint representation dichotomy in today's Rust compiler and `zerocopy`:
```rust
let c_struct_repr = match &ctx.ast.data {
    Data::Struct(..) => {
        let repr = StructUnionRepr::from_attrs(&ctx.ast.attrs)?;
        if repr.is_c() { Some(repr) } else { None }
    }
    Data::Enum(..) | Data::Union(..) => None,
};
```
- When `derive_known_layout_for_repr_c_struct` runs, only **`#[repr(C)]` structs** obtain DST `KnownLayout` support (`#[derive(KnownLayout)]` on non-`#[repr(C)]` slice-tail struct `NonReprCPacket` falls back at `L274-282` to `SelfBounds::SIZED`, failing with **`E0277`**: *"the trait `Sized` is not implemented for `[u16]`"*, verified in Probe 17 `rc=101`).
- Conversely, `DispatchFromDyn` explicitly **forbids** `#[repr(C)]` (and `#[repr(packed)]`, `E0378`, `builtin.rs:364-366`), admitting only `#[repr(Rust)]` and `#[repr(transparent)]` wrappers!

Hence, for any non-transparent named struct definition `d`, `zerocopyDeriveDstEligible(d)` and `reprAllowedForDispatch(d.repr)` are **strictly disjoint** (mechanized as `repr_c_duality_disjoint`): a stable `zerocopy` custom slice DST *must* be `#[repr(C)]` (or `#[repr(transparent)]` wrapping another `#[repr(C)]`/slice DST), while a custom dynamic-dispatch smart pointer *cannot* be `#[repr(C)]`. (Only `CoerceUnsized` spans both sides, e.g., `#[repr(C)]` smart-pointer-like structs can coerce fields structurally while remaining barred from `DispatchFromDyn`.)

### 6. Relevance to `joshlf/anneal` Verification TCB (`c131b320e`)
Evidence role: **source** + **derived**.

Inspecting `trusted/lean/Trusted/MirAst.lean` and `MirSemantics.lean` at `joshlf/anneal` HEAD (`c131b320eeeb26ef692e5afd5ec8db49ee518613`) establishes how Anneal currently treats these features:
- `MirTy` (`MirAst.lean:312-321`) models `.bool`, `.int`, `.unit`, `.never`, `.enum`, `.tuple`, `.ref`, `.rawPtr`, and `.unsupported`; unsized types (`[T]`, `dyn Trait`, unsized ADTs) and custom non-fieldless-enum structs lower to `.unsupported`.
- `Rvalue` (`MirAst.lean:620-628`) models `.use`, `.binaryOp`, `.unaryOp`, `.discriminant`, `.ref`, `.addressOf`, `.aggregateTuple`, and `.unsupported`; `Rvalue::Cast` (`PointerCoercion::Unsize` and `PtrToPtr` / `Transmute`) and `StatementKind::SetDiscriminant`/slice indexing map to `.unsupported` (`MirSemantics.lean:1240-1315`), which fail closed deterministically as `.error .unsupported` / `.fault .unsupported`.
- Extending Anneal to verify custom smart pointers (`CoerceUnsized`/`DispatchFromDyn`), wide pointers, or `zerocopy` DST casts inside the Trusted Boundary would require: (1) adding scalar-pair pointer values `(addr, metadata)` alongside slice/ADT `MirTy` representations, (2) recording checked `CoerceUnsizedInfo` field-index / `Unsize` tail witnesses without permitting unverified wide-pointer metadata forgery, and (3) verifying `KnownLayout` normalized alignment/size predicates (`from_bytes_with_elems`) rather than relying on `#[derive(KnownLayout)]` macros as trusted. Note further that Anneal's `TrustedBoundary.lean` forbids `Classical.choice`, `Lean.ofReduceBool`/`native_decide`, `omega`/`bv_decide`, `partial def`, and generated `._unsafe_rec` constants—the exact discipline satisfied by the companion Lean mechanization below.

### 7. Kernel-Checked Lean v4.34.1 Mechanization Architecture
Evidence role: **execution** + **derived**.

`support/CoerceUnsizedDispatchFromDynStructuralSoundness.lean` (`2,906` lines, `126,521` bytes, `83` `noncomputable def`s, `86` `theorem`s) formalizes the coherence checkers, `Unsize` tail/prefix-param rules, runtime coercion and `make_thin_self_ptr` ABI semantics, constructive counterexamples for every diagnostic class, and `zerocopy` DST layout soundness over pure `prelude` + `Init.*` with zero Mathlib dependencies:

| Section | Core Modeled Definitions | Principal Kernel-Checked Theorems (`[propext]` only) | Verified Property |
| :--- | :--- | :--- | :--- |
| **1–2** | `alignUp`, `roundDown`, `Mutability`, `Ty`, `substTy`, `paramOccursInTy`, `filterNotIn` | `alignUp_ge`, `roundDown_le`, `substTy_irrelevant_of_agree` | Pure arithmetic bounds; substitution irrelevance when argument lists agree outside unused params |
| **3** | `Layout` (`TyLayout`, `layoutOfFuel`, `combineAdtFieldLayouts`, `computePrefixOffsets`, `wfAdtFields`, `unsizingParamsForAdt`, `checkUnsizeFuel`) | `tail_only_unsized_prefix_offset_invariance`, `unsize_preserves_prefix_offsets` | Well-formed `?Sized` tail structs fix every prefix field offset & prefix alignment independently of tail unsizing target |
| **4** | `collectDiffFieldsCoerce`, `collectDiffFieldsDispatch`, `checkCoerceUnsizedFuel`, `checkDispatchFromDynFuel`, `not1ZstStrong` | `dispatchFromDyn_implies_coerceUnsized`, `dispatchFromDyn_strong_non_1zst`, `collectDiffFieldsDispatch_split_fields` | Every `DispatchFromDyn` witness entails valid `CoerceUnsized` with identical `CoerceWitness` and carries a strong non-1-ZST layout |
| **5** | `RuntimeVal`, `PtrMeta`, `coerceRuntimeVal`, `targetPtrAddr`, `collectNon1ZstFields`, `extractThinSelfPtr` | `coerceUnsized_single_field_preservation`, `coerceWitness_preserves_ptr_address`, `dispatchFromDyn_abi_register_equivalence`, `adding_1zst_siblings_preserves_thin_self_ptr` | Single-field mutation preserves ADT identity, field length, all sibling fields bit-for-bit, and thin data pointer `addr` across arbitrary 1-ZST siblings |
| **6** | `stdEnv`, concrete ADT defs (`defMyPtr`..`defRustPacket`) | 16 constructive `rfl`/`⟨rfl,..⟩` witnesses & counterexamples | Kernel-evaluated witnesses for `valid_myptr_*`, `E0374`, `E0375` ambiguity, `E0377` (incl. enum), `E0378` (u32/align8/generic-ZST/C/packed), `E0277`, `E0308` |
| **7** | `TrailingSliceLayout`, `fromBytesWithElemsValid`, `validateCastAndConvertMetadata` (`trailingNormSizeBase/Phase`), `zerocopyDeriveDstEligible` | `validateCast_splitAt_bounds`, `prefix_suffix_splitAt_complement`, `packet_dst_elems5_vs_elems4_witness`, `repr_c_duality_disjoint`, `packet_repr_c_duality_witness` | `split_at <= bytes_len`, `sPref + sSuff = bytes_len`, `elems=5`/`elems=4` valid on same `16B` buffer, `#[repr(C)]` disjointness from `DispatchFromDyn` |

Every recursive definition uses `noncomputable def` on explicit structural parameters (and `Nat`-fuel indexing for `Ty`/value/layout mutual recursion), avoiding Lean's `WellFounded.fix`/computable codegen `_unsafe_rec` emission entirely (`unsafe_rec_count = 0` confirmed by MetaM kernel inspection).

## Boundaries

Per `FORMAT.md`, negative space is separated into explicit epistemic categories:

1. **Known Not to Apply / Unsupported by `rustc` or `zerocopy`**:
   - **Multifield simultaneous unsizing** (`E0375`): `rustc` intentionally forbids coercing structs with `>= 2` differing fields (e.g., dual pointers) even though a structural representation could theoretically update multiple metadata slots; coherence comments (`builtin.rs:770-772`) record this as a deliberate simplicity boundary.
   - **`#[repr(C)]` or `#[repr(packed)]` dynamic-dispatch receivers** (`E0378`) and **`DispatchFromDyn` with `Align8Zst` or generic `Marker<M>`**: known rejected at coherence time (`builtin.rs:364-416`).
   - **Non-`#[repr(C)]` custom DST `#[derive(KnownLayout)]`**: `zerocopy-derive` falls back to requiring `Self: Sized` (`known_layout.rs:278-282`), making non-`#[repr(C)]` slice-tail DST derives unsupported on stable Rust (`E0277`, Probe 17).
   - **Arbitrary custom `Unsize` impls in user code**: `#![feature(unsize)]` permits referencing `Unsize`, not manually implementing it; all `Unsize` candidates are built-in to trait selection.
2. **Formal Modeling Abstractions (Clean-Room Lean Scope vs Full `rustc`)**:
   - **Not modeled natively from `rustc` AST**: `CoerceUnsizedDispatchFromDynStructuralSoundness.lean` models a faithful self-contained type/layout/ABI calculus of `builtin.rs`, `ty.rs`, `abi.rs`, `wfcheck.rs`, and `zerocopy::layout`, not a direct extractor from `rustc_middle::ty::TyCtxt` or an import of `joshlf/anneal`'s `Trusted.MirSemantics`.
   - **Omitted nightly/advanced Rust features (`not examined` in Lean)**: `ty::Pat` pattern-type coercions (`builtin.rs:698-708, 331-341`), `#[derive(CoercePointee)]` validity macros (`visit_implementation_of_coerce_pointee_validity`), `dyn Trait -> dyn Supertrait` trait-upcasting vtable slot offsets (`select/candidate_assembly.rs:1053-1080`), thin custom `Pointee::Metadata` types beyond `sliceLen` and `vtable`, `#[repr(transparent)]` multi-ZST interaction in `zerocopy-derive` beyond `#[repr(C)]` struct DSTs, and packed `Drop` tail checks (`wfcheck.rs:1056-1065`) are documented from `rust-lang/rust` source but excluded from the Lean model AST.
   - **Syntactic field comparison vs monomorphized normalization**: `builtin.rs` skips `PhantomData` after `try_normalize_erasing_regions` on field definitions while comparing generic `ty_a == ty_b` syntactically without normalization (`FIXME` at `builtin.rs:397, 803`); our Lean model mirrors this faithfully via unnormalized `substTy` structural equality `tyBeq`.
   - **`zerocopy` ZST slice elements (`elem_size == 0`)**: `DstLayout::validate_cast_and_convert_metadata` panics on zero-sized slice elements (`layout.rs:1743-1746`), and `fromBytesWithElemsValid` / `validateCastAndConvertMetadata` in Lean enforce `1 <= elemSize` fail-closed.
3. **Unknown / Version-Drift Qualification**:
   - Empirical binaries in `support/probe_results.json` ran under `rustc 1.98.0-nightly (14210df0e)` (May 2026) while the full source audit inspected `rust-lang/rust` HEAD `f7da9a4236` (Nov 2026). Although diffing `coherence/builtin.rs` across both revisions showed identical `CoerceUnsized`/`DispatchFromDyn` constraint logic, re-running `probe_coerce_unsized_dispatch_from_dyn.py` on a post-May-2026 nightly is required if exact diagnostic span wrapping on `E0375` or error message strings on newer toolchains are relied upon.

## Evidence

### Primary-Source Anchors Inspected

| Repository | Immutable Commit SHA | Path & Line Range / Symbol | Evidence Role & Observed Fact |
| :--- | :--- | :--- | :--- |
| `rust-lang/rust` | `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_hir_analysis/src/coherence/builtin.rs:32-54` (`check_trait`), `248-256` (`visit_implementation_of_coerce_unsized`), `287-469` (`visit_implementation_of_dispatch_from_dyn`), `655-888` (`coerce_unsized_info`) | **source**: Exact structural checks for `CoerceUnsized` and `DispatchFromDyn`, `def_a.is_struct()`, `repr().c() \|\| repr().packed()`, `is_phantom_data()` skip before `ty_a == ty_b`, `layout.is_1zst() && !ty_a.has_non_region_param()`, `CustomCoerceUnsized::Struct(i)`. |
| `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `compiler/rustc_hir_analysis/src/coherence/builtin.rs` (`rustc 1.98.0-nightly`) | **source** + **execution**: Diffed cleanly against `f7da9a4236`; identical coercion constraint logic aside from `errors::` -> `diagnostics::`, `TraitErrors::HasErrors`, `LangItem` import move, and sibling `CoerceShared`/`Reborrow` additions. |
| `rust-lang/rust` | `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_hir_analysis/src/diagnostics.rs:1202-1203` (`DispatchFromDynRepr`), `1326-1356` (`DispatchFromDynZST`, `CoerceNoField`, `CoerceMulti`), `1466-1496` (`CoerceUnsizedNonStruct`, `CoerceSameStruct`) | **source**: Assigns exact codes `E0374`, `E0375`, `E0377` (for both non-struct ADTs and distinct structs; legacy `E0376` absent), and `E0378`. |
| `rust-lang/rust` | `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_error_codes/src/error_codes/E0374.md:1-30`, `E0375.md:1-30`, `E0377.md:1-34`, `E0378.md:1-59` | **documentation**: Documents `E0374`/`E0375`/`E0377`; `E0378.md:21-24` omits non-generic 1-ZSTs and `#[repr(C)]`/`#[repr(packed)]` bans present in `builtin.rs`. |
| `rust-lang/rust` | `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_hir_analysis/src/check/wfcheck.rs:1056-1091` | **source**: Enforces `Sized` on `variant.fields.raw[..len - unsized_len]` (`E0277`). |
| `rust-lang/rust` | `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_ty_utils/src/ty.rs:305-347` (`unsizing_params_for_adt`), `compiler/rustc_trait_selection/src/traits/select/candidate_assembly.rs:1083-1106`, `confirmation.rs:1108-1165` | **source**: Collects tail type/const params, strips params appearing in prefix fields (`unsizing_params.remove(i)`), confirms `Struct<T>: Unsize<Struct<U>>`. |
| `rust-lang/rust` | `f7da9a42368f31abb02b8064bb93a11bf9ba9f5e` | `compiler/rustc_ty_utils/src/abi.rs:696-739` (`make_thin_self_ptr`), `rustc_middle` / `rustc_codegen_ssa/src/base.rs:221-313` (`unsize_ptr`, `coerce_unsized_into`), `rustc_codegen_ssa/src/mir/rvalue.rs:139-184, 564-570`, `rustc_hir_analysis/src/hir_ty_lowering` / `dyn_compatibility.rs:649-830`, `library/core/src/ops/unsize.rs:35-137` | **source**: `make_thin_self_ptr` unwraps unique `non_1zst_field(cx)` to `*mut ()` ABI; codegen splits `ScalarPair` (`unsize_ptr`) vs general ADT fieldwise `typed_place_copy` + recursion (`coerce_unsized_into`). |
| `google/zerocopy` | `907b9175fee081872ec883ca4709e6ad922f8ed0` (identical in `zerocopy/` & `zerocopy-derive/` at `e05af9265ec8521e8c187dfde4e1bf5650b9d800`) | `zerocopy/src/lib.rs:748-815, 1130-1137` (`KnownLayout`), `zerocopy/src/ref.rs:736-776` (`Ref::from_bytes_with_elems`), `zerocopy/src/pointer/mod.rs:178-231` (`CastUnsized`), `zerocopy/src/layout.rs:734-773, 1705-1852` (`validate_cast_and_convert_metadata`), `zerocopy-derive/src/derive/known_layout.rs:252-292` | **source** + **execution**: Stable slice-DST metadata/cast machinery; `#[repr(C)]` required for non-`Sized` struct `KnownLayout` derive. |
| `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirAst.lean:312-321, 620-628`, `trusted/lean/Trusted/MirSemantics.lean:1240-1315` | **source**: Unsized ADTs, slices, and `Rvalue::Cast` lower fail-closed to `.unsupported`. |
| `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` | Release `v4.34.1` (`lean` kernel + `Elab.runFrontend` MetaM axiom/environment auditor) | **execution**: Compiled `support/CoerceUnsizedDispatchFromDynStructuralSoundness.lean` cleanly and audited all `869` constants. |

### Preserved Empirical & Verification Receipts

1. **`support/probe_coerce_unsized_dispatch_from_dyn.py` (`783` lines) & `support/probe_results.json` (`159` lines)**:
   Contains the complete, sanitized source programs, Cargo configuration generator, exact compiler stderrs, and runtime stdout strings across all `17` probes on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and `zerocopy 0.8.64` (`907b9175fee0`).
2. **`support/CoerceUnsizedDispatchFromDynStructuralSoundness.lean` (`2,906` lines, `126,521` bytes)**:
   Strict kernel-checked verification transcript observed on `leanprover/lean4 v4.34.1`:
   - Compiler invocation: `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` exited `0` (zero errors, zero warnings).
   - MetaM kernel/axiom/codegen audit (`Elab.runFrontend`):
     - `file_lines=2907` (with trailing newline; `wc -l` `2906`)
     - `local_constants=869`
     - `unsafe_rec_count=0`
     - `axioms_used=[propext]` (`Quot.sound` not even required)
     - `forbidden_axiom_hits=0` (`Classical.choice`, `sorryAx`, `Lean.ofReduceBool`, `Lean.trustCompiler`, and `_unsafe_rec` all `0`)
   - Syntactic scan outside comments confirmed: `83` `noncomputable def` definitions, `0` plain `def`, `86` `theorem` declarations, and `0` hits for `sorry`, `partial`, `deriving`, `Classical`, `omega`, `bv_decide`, `native_decide`, `axiom`, or `noncomputable section`.

### Key Diagnostic Behavior Transcripts (Verbatim Highlights from `support/probe_results.json`)

- **Retired `E0376` Confirmed on `enum` Impl** (`non_struct_enum_rejected_e0377_formerly_e0376`):
  ```text
  error[E0377]: the trait `CoerceUnsized` may only be implemented for a coercion between structures
    --> probe.rs:10:1
     |
  10 | impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<EnumPtr<U>> for EnumPtr<T> {}
     | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  ```
- **Generic `Marker<M>` Wrapper 1-ZST Rejected While `UnitTag` Passes** (`dispatch_from_dyn_generic_1zst_rejected_e0378` vs `valid_dispatch_from_dyn_non_generic_1zst_sibling`):
  ```text
  error[E0378]: the trait `DispatchFromDyn` may only be implemented for structs containing the field being coerced, ZST fields with 1 byte alignment that don't mention type/const generics, and nothing else
    --> probe.rs:13:1
  ...
     = note: extra field `1` of type `Marker<M>` is not allowed
  ```
- **Non-`#[repr(C)]` `#[derive(KnownLayout)]` Slice DST Failure** (`zerocopy_derive_custom_dst_packet` negative check):
  ```text
  error[E0277]: the size for values of type `[u16]` cannot be known at compilation time
   --> src/main.rs:4:10
    |
  4 | #[derive(KnownLayout)]
    |          ^^^^^^^^^^^ doesn't have a size known at compile-time
    = help: within `NonReprCPacket`, the trait `Sized` is not implemented for `[u16]`
  ```

## Revalidation

To verify the report's empirical and formal claims on another toolchain version, target, or commit of `rust-lang/rust` or `google/zerocopy`:

1. **Re-run all 17 live `rustc` and `zerocopy` probes**:
   Execute the preserved offline harness against a target nightly `rustc` and checked-out `google/zerocopy` workspace inside an ephemeral `tempfile.TemporaryDirectory()`:
   ```bash
   python3 reports/rustc-coerce-unsized-dispatch-from-dyn-structural-constraints-and-zerocopy-dst/support/probe_coerce_unsized_dispatch_from_dyn.py \
     --zerocopy-src <path-to-zerocopy>/zerocopy \
     --out /tmp/revalidated_probe_results.json
   ```
   Confirm `0` process errors, compare all `compile_returncode` / `run_stdout` fields against `support/probe_results.json`, and verify that `non_struct_enum_rejected_e0377_formerly_e0376` still emits `E0377`, `valid_dispatch_from_dyn_non_generic_1zst_sibling` still outputs `TAGGED_DYN_DISPATCH=77`, `dispatch_from_dyn_generic_1zst_rejected_e0378` / `align` / `repr_c` / `repr_packed` still fail `E0378`, `custom_dst_prefix_mentions_param_rejected` fails with `E0308` alone, and `zerocopy_derive_custom_dst_packet` prints `META5=5 META4=4` alongside `non_repr_c_derive_compile_returncode = 101`.

2. **Re-check the Lean v4.34.1 mechanization with strict kernel flags**:
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     reports/rustc-coerce-unsized-dispatch-from-dyn-structural-constraints-and-zerocopy-dst/support/CoerceUnsizedDispatchFromDynStructuralSoundness.lean
   ```
   Expect exit code `0` with no errors or warnings; inspect every exported declaration's axioms and check that zero `_unsafe_rec` constants or non-standard axioms (`Classical.choice`, `sorryAx`, `Lean.ofReduceBool`) are referenced.

3. **Diff the narrow upstream compiler gate on future `rust-lang/rust` or `zerocopy` revisions**:
   - Check `compiler/rustc_hir_analysis/src/coherence/builtin.rs` (`visit_implementation_of_dispatch_from_dyn`, `coerce_unsized_info`) for any relaxation of `#[repr(C)]`/`is_1zst`/`has_non_region_param` or multi-field restrictions (`E0374`/`E0375`/`E0377`/`E0378`).
   - Check `compiler/rustc_ty_utils/src/ty.rs` (`unsizing_params_for_adt`) and `compiler/rustc_ty_utils/src/abi.rs` (`make_thin_self_ptr`).
   - Check `zerocopy-derive/src/derive/known_layout.rs` (`derive`) for any future support of non-`#[repr(C)]` unsized structs, and `zerocopy/src/layout.rs` (`validate_cast_and_convert_metadata`) for rounding-phase changes.

4. **Validate corpus structure cleanly**:
   ```bash
   python3 tools/reference.py check
   ```
   Expect `reference check passed` with exit code `0`.
