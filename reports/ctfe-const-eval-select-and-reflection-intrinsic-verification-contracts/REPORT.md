# CTFE `const_eval_select` Relational Equivalence (`ConstEvalSelectEquiv`), `is_val_statically_known`, and Reflection Intrinsic Verification Contracts

## Summary

In `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`),
`core::intrinsics::const_eval_select((args...), called_in_const, called_at_rt)`
is the sole standard-library primitive that intentionally dispatches a `const fn`
to two different implementations at compile time vs. runtime. Auditing
`compiler/rustc_mir_transform/src/lib.rs:240-314, 506-532, 790-802`,
`compiler/rustc_const_eval/src/const_eval/machine.rs:483-550`, and every
`const_eval_select`, `is_val_statically_known`, `const_allocate`,
`const_deallocate`, `type_id`, and `type_name` site across `library/core` and
`library/alloc`
([`support/std_const_eval_select_census.json`](support/std_const_eval_select_census.json)),
together with a zero-axiom Lean `v4.34.1` mechanization
([`support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean`](support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean)),
establishes four architectural contracts for `.anneal-mir`, Anneal source
verification, and `MiniSSA`'s `MirConstFoldCert`:

1. **`Runtime(PostCleanup)` MIR Preserves Both `called_in_const` (`f_ct`) and
   `called_at_rt` (`f_rt`) Before `remap_mir_for_const_eval_select`:**
   - In `compiler/rustc_mir_transform/src/lib.rs:240-314`,
     `remap_mir_for_const_eval_select` does **not** run during `mir_built`,
     `mir_promoted`, or `mir_drops_elaborated_and_const_checked`
     (`Runtime(PostCleanup)` MIR). Instead, `mir_for_ctfe` (`lib.rs:506-517`)
     clones `mir_drops_elaborated_and_const_checked` and remaps
     `const_eval_select` to `called_in_const` (`Constness::Const`), while
     `inner_optimized_mir` (`lib.rs:800-801`) steals
     `mir_drops_elaborated_and_const_checked` and remaps `const_eval_select` to
     `called_at_rt` (`Constness::NotConst`).
   - Consequently, a single `.anneal-mir` artifact captured at
     `Runtime(PostCleanup)` retains the un-remapped 3-argument
     `TerminatorKind::Call` to `const_eval_select(tupled_args, f_ct, f_rt)` with
     both function operands intact (verified empirically in
     [`support/audit_const_eval_select_in_std.py`](support/audit_const_eval_select_in_std.py)).
2. **Complete 30-Site Standard-Library Census of `const_eval_select` in
   `rustc 1.99.1` Across Four Semantic Categories:**
   - Across `library/core` (`25` sites) and `library/alloc` (`5` sites), all
     `30` `const_eval_select` invocations partition cleanly into:
     - **Category 1 — Arch SIMD / Word-Chunked Fast Path vs. Scalar Byte Loop
       (`7` sites:** `<[u8]>::is_ascii`, `find_non_ascii_slow`, `memchr_aligned`,
       `CStr::from_bytes_until_nul`, `CStr::from_ptr`, `ptr::swap_nonoverlapping`,
       `intrinsics::compare_bytes`): satisfy strong observational equivalence
       `ObsEquivOnValid` (`∀ x, P x → f_ct x = f_rt x`), mechanized for
       `is_ascii` in `asciiCheck_ctfe_runtime_obsEquiv`
       ([`support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean:188-196`](support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean#L188-L196)).
     - **Category 2 — Pointer Alignment & Null Inspection (`7` sites:**
       `run_utf8_validation`, `<*const T>::{is_null, align_offset,
       is_aligned_to}`, `<*mut T>::{align_offset, is_aligned_to}`): where CTFE
       cannot inspect symbolic `AllocId` alignment via `ptrtoint` and either uses
       `ptr_guaranteed_cmp` or returns conservative `usize::MAX` (`align_offset`),
       satisfying `ObsEquivOnValid` at the enclosing caller (`run_utf8_validation`)
       or `BothSatisfySpec` (`align_offset`).
     - **Category 3 — Compile-Time Heap Allocation (`8` sites:**
       `Global::{alloc_impl, deallocate, grow_impl, shrink, handle_alloc_error}`
       in `library/alloc/src/alloc.rs:424-649` and `const_deallocate` in
       `library/core/src/intrinsics/mod.rs:2875`): dispatch to
       `const_allocate` / `const_deallocate` (`MemoryKind::Heap {
       was_made_global: false }`, `machine.rs:490-543`) in CTFE vs.
       `__rust_alloc` / `__rust_dealloc` at runtime.
     - **Category 4 — Runtime UB-Checks & Diverging Panic Hooks (`8` sites:**
       `ub_checks::{check_language_ub, maybe_is_aligned_and_not_null,
       maybe_is_nonoverlapping}` in `library/core/src/ub_checks.rs:98-166`,
       `sub_ptr` / `len_nonnull_check` in `{const_ptr,mut_ptr}.rs`, and panic
       hooks in `{panic,panicking,str/mod}.rs`): return `true` at CTFE (where the
       CTFE interpreter already checks alignment and overlap natively on every
       access) or diverge (`-> !`) on both arms, satisfying `BothSatisfySpec` and
       `ObsEquivOnValid` on all UB-free inputs.
3. **Two-Tier Verification Contract: `ObsEquivOnValid` (for `MirConstFoldCert`)
   vs. `BothSatisfySpec` (for Anneal Source Specs):**
   - When `MiniSSA`'s `MirConstFoldCert` folds a runtime call `f(const_args)` to
     its CTFE result, `f` must satisfy `ObsEquivOnValid P f_ct f_rt`
     (`constEvalSelect_refines_of_obsEquiv`,
     [`support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean:87-95`](support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean#L87-L95));
     without an `ObsEquivOnValid` witness, `checkConstFoldWithSelectCert`
     rejects constant folding (`divergentConstEvalSelect_constFold_rejected`,
     [`support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean:206-208`](support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean#L206-L208)).
   - When Anneal verifies a user contract `#[anneal_spec(P, Q)]` on a `const fn`,
     proving `BothSatisfySpec P Q f_ct f_rt` on the single `Runtime(PostCleanup)`
     MIR body certifies both CTFE evaluation and runtime execution
     (`annealSpec_constEvalSelect_sound`,
     [`support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean:102-112`](support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean#L102-L112)).
4. **Angelic Non-Deterministic Contract for `is_val_statically_known`
   (`isValStaticallyKnown_foldFalse_refines`, `isValStaticallyKnown_foldTrue_refines`):**
   - Across all `11` call sites in `library/core` (`num/{int_macros,uint_macros,
     flt2dec}`, `slice/specialize.rs`, `fmt/mod.rs`), `is_val_statically_known(x)`
     selects between an constant-folding-friendly fast path (e.g., power-of-two
     division) and a general fallback.
   - Modeling `is_val_statically_known(x)` in source `Runtime(PostCleanup)` MIR
     as angelic non-deterministic choice $\exists b \in \{\texttt{true},
     \texttt{false}\}$ proves that both CTFE's unconditional `false`
     (`machine.rs:549`) and `MiniSSA` / LLVM's `true` after `ConstProp`
     (`llvm.is.constant`, `compiler/rustc_codegen_llvm/src/intrinsic.rs:244-253`)
     are unconditional forward refinements (`isValStaticallyKnown_foldFalse_refines`,
     `isValStaticallyKnown_foldTrue_refines`,
     [`support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean:131-143`](support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean#L131-L143)).

## Applicability

This report applies to `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`), `Lean 4 v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`), and Anneal
(`joshlf/anneal@d4ca2c861f664f200b69cdced9f6af38b5b1175a`) when verifying
`const fn` bodies, standard-library intrinsics, and compile-time constant folding
(`MirConstFoldCert`) in `MiniSSA`.

It extends two corpus reports:
- `rustc-ctfe-globalalloc-promoted-constants-and-runtime-mir-equivalence`
- `unified-farkas-knownbits-and-aegraph-side-condition-certificates`

Created: 2026-11-14 · Updated: 2026-11-14

## Findings

### 1. Exhaustive Taxonomy of `const_eval_select` Call Sites in `rustc 1.99.1`

Basis: source + execution

Table 1 summarizes the `30` `const_eval_select` call sites extracted from
`library/core` and `library/alloc` in `rustc 1.99.1`
([`support/std_const_eval_select_census.json`](support/std_const_eval_select_census.json)):

| Site ID(s) | File & Line (`rust-lang/rust@58cf8f9c35b3`) | Enclosing `const fn` | `called_in_const` (`f_ct`) | `called_at_rt` (`f_rt`) | Category & Verification Contract |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `CES-01` | `core/src/slice/ascii.rs:468` | `<[u8]>::is_ascii` | `is_ascii_simple` (byte loop) | `is_ascii_simd` (`usize`/SIMD mask) | **Cat 1:** `ObsEquivOnValid` (`asciiCheck_ctfe_runtime_obsEquiv`) |
| `CES-02` | `core/src/slice/ascii.rs:662` | `find_non_ascii_slow` | `find_non_ascii_comptime` | `find_non_ascii_runtime` | **Cat 1:** `ObsEquivOnValid` (first non-ASCII index) |
| `CES-03` | `core/src/slice/memchr.rs:56` | `memchr_aligned` | `memchr_naive` | `memchr_general_case` (SWAR) | **Cat 1:** `ObsEquivOnValid` (`Option<usize>` equality) |
| `CES-04` | `core/src/str/validations.rs:136` | `run_utf8_validation` | `const fn -> usize::MAX` | `v.as_ptr().align_offset(8)` | **Cat 2:** `ObsEquivOnValid` on outer `run_utf8_validation` |
| `CES-05` | `core/src/ffi/c_str.rs:390` | `CStr::from_bytes_until_nul` | `from_bytes_until_nul_comptime` | `from_bytes_until_nul_runtime` | **Cat 1:** `ObsEquivOnValid` |
| `CES-06` | `core/src/ffi/c_str.rs:754` | `CStr::from_ptr` | `strlen_ctfe` | `strlen_rt` (`libc::strlen`) | **Cat 1:** `ObsEquivOnValid` on valid C string |
| `CES-07` | `core/src/ptr/mod.rs:1421` | `swap_nonoverlapping` | `swap_nonoverlapping_compiletime` | `swap_nonoverlapping_runtime` | **Cat 1:** `ObsEquivOnValid` (memory post-state equality) |
| `CES-08` | `core/src/ptr/const_ptr.rs:26` | `<*const T>::is_null` | `guaranteed_eq(null)` | `addr() == 0` | **Cat 2:** `ObsEquivOnValid` on non-ambiguous pointers |
| `CES-09,12,13,15` | `core/src/ptr/{const_ptr,mut_ptr}.rs` | `sub_ptr`, `len_nonnull_check` | `ctfe_noop` | `rt_ub_check` | **Cat 4:** `ObsEquivOnValid` on UB-free inputs |
| `CES-10,14` | `core/src/ptr/{const_ptr,mut_ptr}.rs:711` | `align_offset` | `const fn -> usize::MAX` | `align_offset_runtime` | **Cat 2:** `BothSatisfySpec` (permissive postcondition) |
| `CES-11` | `core/src/ptr/const_ptr.rs:845` | `is_aligned_to` | `is_aligned_to_ctfe` | `(addr & (align - 1)) == 0` | **Cat 2:** `ObsEquivOnValid` when `align <= base_align` |
| `CES-16..19` | `core/src/ub_checks.rs:98,123,136,166` | `check_language_ub`, `maybe_is_*` | `const fn -> true` | `is_aligned_rt`, `is_nonoverlapping_rt` | **Cat 4:** `ObsEquivOnValid` on UB-free inputs |
| `CES-20..22` | `core/src/{panic,panicking,str/mod}.rs` | `panic_display`, `slice_error_fail` | `ctfe_panic` (`-> !`) | `rt_panic` (`-> !`) | **Cat 4:** `BothSatisfySpec` (both diverge) |
| `CES-23..25` | `core/src/intrinsics/mod.rs:2875,2907,3828` | `const_deallocate`, `raw_eq`, `compare_bytes` | `ctfe_intrinsic` | `rt_impl` | **Cat 1 / Cat 3:** `ObsEquivOnValid` |
| `CES-26..30` | `alloc/src/alloc.rs:424,436,454,471,649` | `Global::{alloc_impl, deallocate, grow_impl, shrink, handle_alloc_error}` | `const_allocate` / `const_deallocate` | `__rust_alloc` / `__rust_dealloc` | **Cat 3:** `ObsEquivOnValid` up to fresh `AllocId` isomorphism |

### 2. Lean `v4.34.1` Mechanization of `ConstEvalSelectEquiv` and `asciiCheck_ctfe_runtime_obsEquiv`

Basis: source + execution

All six theorems in
[`support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean`](support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean)
are kernel-checked in Lean `v4.34.1` with zero `sorryAx` and zero
`Lean.ofReduceBool`:

| Theorem Name | Lines | Mechanized Property |
| :--- | :---: | :--- |
| `constEvalSelect_refines_of_obsEquiv` | `87-95` | Under `ObsEquivOnValid P f_ct f_rt`, replacing a runtime call `evalConstEvalSelect .runtimeExec c f_ct f_rt` with its CTFE value `.ok v` (`MirConstFoldCert`) is an exact refinement. |
| `annealSpec_constEvalSelect_sound` | `102-112` | Under `BothSatisfySpec P Q f_ct f_rt` at the pre-remapped `Runtime(PostCleanup)` boundary, `evalConstEvalSelect m x f_ct f_rt` satisfies `Q` in both `.ctfeConst` and `.runtimeExec`. |
| `isValStaticallyKnown_foldFalse_refines` | `131-134` | Folding `is_val_statically_known(x)` to `false` refines `SourceAllowsIsValStaticallyKnown`. |
| `isValStaticallyKnown_foldTrue_refines` | `140-143` | Folding `is_val_statically_known(x)` to `true` after `ConstProp` refines `SourceAllowsIsValStaticallyKnown`. |
| `asciiCheck_ctfe_runtime_obsEquiv` | `188-196` | Inductive `BitVec 8` proof via `BitVec.and_or_distrib_right` that `asciiCheckBytewiseCtfe bytes = asciiCheckWordRuntime bytes` for all `bytes : List (BitVec 8)`. |
| `divergentConstEvalSelect_constFold_rejected` | `206-208` | `checkConstFoldWithSelectCert` rejects `MirConstFoldCert` when `hasObsEquivProof = false`. |

### 3. Lowering Contract for `const_allocate`, `const_deallocate`, `const_make_global`, `type_id`, and `type_name`

Basis: source + derived

In `compiler/rustc_const_eval/src/const_eval/machine.rs:490-543` and
`compiler/rustc_const_eval/src/interpret/intrinsics.rs:78-215`:
1. **`const_allocate(size, align)` & `const_deallocate(ptr, size, align)` (`machine.rs:490-537`):**
   - During CTFE, `const_allocate` creates a fresh allocation of kind
     `MemoryKind::Machine(MemoryKind::Heap { was_made_global: false })`. If such
     a pointer survives to the end of a `const` / `static` evaluation without
     either being freed by `const_deallocate` or promoted to immutable global
     storage via `const_make_global` (`machine.rs:539-543`, used by
     `ThinBox::new_unsize` in `library/alloc/src/boxed/thin.rs:335`), CTFE
     finalization rejects the constant with an unfreed-allocation error.
   - At runtime (`library/core/src/intrinsics/mod.rs:2875`), `const_deallocate`
     is a no-op via `const_eval_select`, while `Global::alloc_impl` /
     `Global::deallocate` (`library/alloc/src/alloc.rs:424-508`) dispatch to
     `__rust_alloc` / `__rust_dealloc`.
2. **`type_id` & `type_name` (`intrinsics.rs:78-120, 191-215`):**
   - `type_name::<T>()` allocates a deduplicated `'static` UTF-8 string slice
     via `alloc_type_name(tcx, tp_ty)` (`GlobalAlloc::Memory`).
   - `type_id::<T>()` writes the 128-bit SipHash `tcx.type_id_hash(tp_ty)`
     decorated with `GlobalAlloc::TypeId { ty: tp_ty }` provenance. Alongside the
     128-bit runtime hash, `.anneal-mir` exports a crate-local injective
     `TypeIdIndex(u32)` table so Anneal specifications can prove
     `TypeId::of::<T>() != TypeId::of::<U>()` for distinct concrete types
     directly from type inequality without assuming global hash-collision freedom.

## Boundaries

1. **User-Defined `const_eval_select` With Intentionally Divergent Arms (`known not to apply` for `MirConstFoldCert`):**
   - Because `const_eval_select` is an internal unstable intrinsic
     (`#![feature(const_eval_select)]`), if an external unstable crate invokes
     `const_eval_select` with closures that return distinct values (`0` vs. `1`),
     `MiniSSA` must **not** apply `MirConstFoldCert` across that call site unless
     an `ObsEquivOnValid` proof is registered in thetrusted intrinsic table
     (`divergentConstEvalSelect_constFold_rejected`).
2. **`align_offset` Permissive Contract (`CES-10`, `known not to apply` for exact equality):**
   - `<*const T>::align_offset` (`library/core/src/ptr/const_ptr.rs:711`) returns
     `usize::MAX` in CTFE and the actual alignment offset at runtime. It
     satisfies `BothSatisfySpec` (since `align_offset`'s specification explicitly
     permits returning `usize::MAX` whenever computing the offset is not
     supported), **not** `ObsEquivOnValid`; callers such as `run_utf8_validation`
     (`CES-04`) restore `ObsEquivOnValid` by falling back to a bytewise loop
     when `align == usize::MAX`.

## Evidence

1. **Compiler and Standard Library Source Coordinates (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`):**
   - `compiler/rustc_mir_transform/src/lib.rs:240-314, 506-532, 790-802`
     (`remap_mir_for_const_eval_select`, `mir_for_ctfe`, `inner_optimized_mir`).
   - `compiler/rustc_const_eval/src/const_eval/machine.rs:490-550`
     (`const_allocate`, `const_deallocate`, `const_make_global`,
     `is_val_statically_known`).
   - `compiler/rustc_codegen_llvm/src/intrinsic.rs:244-254`
     (`is_val_statically_known` lowering to `llvm.is.constant`).
   - All `30` `const_eval_select` sites in `library/core/src/**` and
     `library/alloc/src/**` listed in Table 1 and
     [`support/std_const_eval_select_census.json`](support/std_const_eval_select_census.json).
2. **Lean `v4.34.1` Mechanization (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`):**
   - [`support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean`](support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean)
     (zero `sorryAx`, zero `Lean.ofReduceBool`).
3. **Executable Census Script and Preserved Dataset:**
   - [`support/audit_const_eval_select_in_std.py`](support/audit_const_eval_select_in_std.py)
   - [`support/std_const_eval_select_census.json`](support/std_const_eval_select_census.json)

## Revalidation

```bash
anneal-lean-run --mode file --concurrency 4 -- lake env lean \
  reports/ctfe-const-eval-select-and-reflection-intrinsic-verification-contracts/support/CtfeConstEvalSelectAndIntrinsicContractProbe.lean
python3 reports/ctfe-const-eval-select-and-reflection-intrinsic-verification-contracts/support/audit_const_eval_select_in_std.py
```
