# Forward-Compatible MIR Semantics and Reference-Admissible Refinement

## Summary

This report analyzes the semantic boundary between **normative Rust Reference
guarantees** (`rust-lang/reference` commit
`82da570bafd9efed421bdbae0f8603ede8dd308b`) and **pinned-`rustc` implementation
coincidences** (`rust-lang/rust` commit
`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, `rustc 1.98.0-nightly (2026-05-30)`)
when verifying layout-sensitive Rust `Runtime(PostCleanup)` MIR against
Zerocopy's forward-compatible soundness policy (`google/zerocopy` commit
`8fb35253fbc703cb2cd0997f4efcda76cf9062b6`, `POLICIES.md:31-49`). It includes a
standalone, kernel-checked Lean 4 (`v4.34.1`, commit
`5045d0056413266e57c625dcd7c365b10e377c52`) mechanization
([`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean),
3,197 lines, 39 theorems, zero `sorryAx`, zero `Lean.ofReduceBool`) that
formalizes and compares three candidate MIR semantic architectures on top of a
self-contained `Preorder` / `Partial` / `Behavior` / `Language` / `StepResult` /
`SmallStepMachine` refinement spine.

Key findings:

1. **Four-Category Classification of MIR Semantic Rules and Extractor Predicates**:
   Every operational rule and compiler-extraction predicate in a `Runtime(PostCleanup)`
   MIR verification pipeline falls into one of four categories:
   - **Category (A) Normative Stable Reference / Stdlib Guarantee**,
   - **Category (B) Target-Specific Fact**,
   - **Category (C) Pinned-`rustc` Implementation Coincidence**, or
   - **Category (D) Sound Conservative Under-Approximation**.
2. **Six Concrete Forward-Compatibility and Soundness Hazards in Pinned-`rustc` MIR Capture**:
   - **Unchecked `#[repr(Rust)]` single-field structs (`V1–V4`)**:
     An extractor that lowers a single-variant, single-field struct as a
     transparent wrapper whenever `repr.align.is_none() && repr.pack.is_none()`
     and `tcx.layout_of(self_ty).size == tcx.layout_of(field_ty).size` in
     `rustc 1.98.0`—without checking `adt.repr().transparent()` or
     `adt.repr().c()`—treats a **Category (C)** implementation coincidence of
     `rustc_abi::layout::LayoutCalculator::univariant_biased`
     (`compiler/rustc_abi/src/layout.rs:1283-1320`) as a layout guarantee. This
     unsoundly accepts four distinct patterns (**V1–V4**) of `transmute_copy` and
     `size_of` proofs over default `#[repr(Rust)]` wrappers (`struct Wrapper(pub u64)`,
     `struct Inner(pub u32)` nested inside `#[repr(transparent)]`, and
     user-defined niche wrappers missing `#[repr(transparent)]`) that violate
     `r[layout.repr.rust.unspecified]` and Zerocopy's soundness policy.
   - **Multi-field `fields := []` zero-size bug**:
     When an extractor represents unsupported multi-field structs such as
     `struct Pair(pub u32, pub u32)` by emitting an `AdtDecl` with `fields := []`,
     any `tySize` recurrence that folds `decl.fields` starting from `some 0`
     computes `tySize Pair = some 0`, allowing `transmute_copy::<(), Pair>(&())`
     to succeed and construct `Val.agg []` (`model1_multi_field_repr_rust_size_zero_bug`).
   - **Why `-Z randomize-layout` in `rustc 1.98.0` is insufficient as a layout-soundness oracle**:
     Empirical probing ([`support/randomize_layout_probe.rs`](support/randomize_layout_probe.rs),
     [`support/randomize_layout_probe.jsonl`](support/randomize_layout_probe.jsonl))
     and source analysis of `compiler/rustc_abi/src/layout.rs:1110-1320` prove
     that `-Z randomize-layout` in `rustc 1.98.0-nightly (f8a08b688)` **never**
     inserts synthetic padding into 1-field `#[repr(Rust)]` structs (`fields.len() > 1`
     guard at `L1110`), never randomizes tuple field order (`ReprOptions::default()`
     in `compiler/rustc_ty_utils/src/layout.rs:207-211, 571-576`), and never
     randomizes the tail field of a generic struct with `T: ?Sized`
     (`StructKind::MaybeUnsized` at `L1111-L1115`).
   - **Unbounded `Nat` representation of `MirVal.usize (bits : Nat)`**:
     If a well-typedness predicate `validStep` defines `| .usize, .usize _ => True`
     without bounding `bits < 2^(8 * ptrWidthBytes)` (while `.uint w` bounds
     `bits < w.modulus`), `MirVal.usize (2^64)` is admitted as a valid `usize`
     value satisfying `!= 0` or `!= 2^64` invariants.
   - **Entry-assumed vs. path-executed `RequiresConst` (`body.required_consts`)**:
     Assuming that all `ConstBlock` items in `body.required_consts()` succeed at
     function entry is **Category (A)** along execution paths that reach the
     `const { ... }` block (`r[expr.block.const.evaluation]`), but **Category (C)**
     (`rustc` `RequiredConstsVisitor` + `MentionedItems`) when the `const` block
     sits in an untaken dead branch (`r[expr.block.const.not-executed]`).
   - **Unconditional `UnwindTerminate` lowering on `TerminatorKind::Assert`**:
     Lowering `TerminatorKind::Assert { cond, expected, target, unwind }` to an
     unconditional `.unwindTerminate` terminator whenever `unwind` is not
     `UnwindAction::Continue` (e.g., `Cleanup(bb)` when a local has a `Drop`
     impl, or `Terminate(Abi)` in an `extern "C"` function) truncates execution
     at the `Assert` and treats the remainder of the function as vacuously safe
     whenever `.terminated .unwind` is classified as safe (`PrefixOutcome.isSafe`).
3. **Kernel-Checked Architectural Comparison (`Models 1, 2, and 3`) and Boundary Extensions**:
   In [`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean),
   we prove across 39 kernel-checked theorems:
   - **Model 1 (`Sem_PinnedRustc`, Pinned-`rustc` Single-Field Layout Oracle)**
     unsoundly accepts `transmute_copy::<u64, ReprRustWrapper>`
     (`model1_unsoundly_accepts_repr_rust_transmute`) and miscomputes
     `size_of::<Pair>() == 0` under the `fields.foldl` recurrence
     (`model1_multi_field_repr_rust_size_zero_bug`).
   - **Model 2 (`Sem_NaiveFailClosed`, Naive Fail-Closed `Option` Oracle)**
     rejects `transmute_copy::<u64, ReprRustWrapper>`
     (`model2_rejects_repr_rust_transmute_u64`), but **falsely rejects**
     reflexive `transmute_copy::<ReprRustWrapper, ReprRustWrapper>`,
     `copy_nonoverlapping::<ReprRustWrapper>(..., 1)`,
     `size_of::<ReprRustWrapper>() == size_of::<ReprRustWrapper>()`, and
     target-width-parametric `1usize + 1usize`
     (`model2_falsely_rejects_reflexive_and_polymorphic_ops`).
   - **Model 3 (`Sem_ForwardCompatible`, Demonic Quantification over `ReferenceAdmissible` Realizations)**
     both **soundly rejects** `transmute_copy::<u64, ReprRustWrapper>`
     (`model3_rejects_repr_rust_u64_transmute`) and **soundly accepts**
     `#[repr(transparent)]` and padding-free `#[repr(C)]` transmutation
     (`model3_accepts_repr_transparent_and_padding_free_repr_c_transmute`),
     reflexive `#[repr(Rust)]` operations (`model3_accepts_reflexive_repr_rust_transmute_and_copy`),
     and target-parametric vs. `#[cfg]`-gated `usize` arithmetic
     (`model3_target_parametric_vs_cfg_gated_usize`), while refining every
     admissible pinned compiler environment (`model3_refinement_bridge_and_tcb_stratification`).
   - **Extension Theorems A–D**:
     - `repr_rust_zst_vs_non_zst_discrimination`: `r[layout.repr.rust.struct-zst]`
       guarantees `size == 0` for `#[repr(Rust)]` structs whose fields are all
       0-sized (`RustZstWrapper(())`), while `ReprRustWrapper(u64)` is refuted at
       `size == 8` by `env_16_zst`.
     - `repr_c_target_u64_alignment_and_aggregate_align_boundary`: proves both
       that `#[repr(C)] struct WithU64 { a: u32, b: u64 }` has `(size = 12,
       hasUninitPadding = false)` when `i64AlignBytes = 4` (`i686-unknown-linux-gnu`)
       and `(size = 16, hasUninitPadding = true)` when `i64AlignBytes = 8`
       (`x86_64-unknown-linux-gnu`), so `transmute_copy::<WithU64, [u8; 16]>`
       fails across both target families (`reprC_withU64_padding_depends_on_target_i64_align`),
       and that setting `aggregateAlignBytes = 4` in a custom target JSON
       violates `r[layout.repr.transparent]` (`custom_target_aggregate_align_gt_one_violates_transparent_law`).
     - `in_memory_transmute_vs_extern_c_fn_abi_discrimination`: proves that
       in-memory `transmute_copy` succeeds for both `ReprTransparentWrapper(u64)`
       and `ReprCWrapper(u64)`, whereas `extern "C" fn() -> u64` ABI transmutation
       succeeds for `ReprTransparentWrapper(u64)` (`r[layout.repr.transparent.layout-abi]`)
       and steps to `StepResult.err` for `ReprCWrapper(u64)` on `i686` (`sret`).
     - `ub_checks_dual_soundness_trap_and_repair`: proves that both
       `(UbChecks = true, panic_nounwind_fmt ↦ .terminated .unwind)` and
       `(UbChecks = false, skipping precondition_check)` falsely certify UB code
       as safe (`≤ safeUnwindOrNormalSpec` when `cond = false`), whereas
       `(UbChecks = true, panic_nounwind_fmt ↦ StepResult.failed)` refines
       `safeUnwindOrNormalSpec` **if and only if** `cond = true`.

## Applicability

- **Lean 4 (`leanprover/lean4`)**: Examined and kernel-checked at `v4.34.1`
  (commit `5045d0056413266e57c625dcd7c365b10e377c52`) with
  `-DElab.async=false -Ddebug.skipKernelTC=false`.
- **Rust compiler and standard library (`rust-lang/rust`)**: Examined at commit
  `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` (`rustc 1.98.0-nightly (2026-05-30)`),
  covering `rustc_abi`, `rustc_middle`, `rustc_ty_utils`, `rustc_mir_transform`,
  `rustc_monomorphize`, `rustc_target`, and `library/core/src/ub_checks.rs`.
- **The Rust Reference (`rust-lang/reference`)**: Examined at commit
  `82da570bafd9efed421bdbae0f8603ede8dd308b` (bundled with `rustc 1.99.1`),
  specifically `src/type-layout.md`, `src/types/numeric.md`, `src/types/boolean.md`,
  `src/types/tuple.md`, `src/types/pointer.md`, `src/expressions/operator-expr.md`,
  `src/expressions/block-expr.md`, and `src/behavior-considered-undefined.md`.
- **Zerocopy (`google/zerocopy`)**: Examined at commit
  `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`, specifically `POLICIES.md:31-49`.

## Findings

### 1. Four-Category Classification of MIR Semantic Rules and Extractor Predicates

Basis: normative, documentation, source, derived

When verifying Rust `Runtime(PostCleanup)` MIR (`tcx.mir_drops_elaborated_and_const_checked`)
in a formal proof assistant, every semantic rule and compiler-extraction
decision falls into one of four epistemic categories:

- **Category (A) — Normative Stable Reference / Stdlib Guarantee**: Holds across
  all conforming Rust compilers and targets by normative rule in the Rust
  Reference (`82da570bafd9efed421bdbae0f8603ede8dd308b`) or stable `core::mem` /
  `core::num` API documentation (`f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`).
- **Category (B) — Target-Specific Fact**: Depends on a target parameter (`usize`
  bit width, endianness, or target data layout such as `i64` alignment) that the
  Rust Reference leaves target-dependent.
- **Category (C) — Pinned-`rustc` Implementation Coincidence**: True in
  `rustc 1.98.0-nightly (f8a08b688)` (or on a specific host run), but **not**
  guaranteed by the Rust Reference across arbitrary conforming compilers, valid
  `-Z randomize-layout` runs, or future `rustc` versions.
- **Category (D) — Sound Conservative Under-Approximation**: A fail-closed error
  transition (`StepResult.failed`, `Option.none`, or an unmodeled AST fallback)
  that rejects unmodeled constructs without admitting any unsound execution.

#### 1.1 Operational Semantics Rules

| Construct / Rule (Formalized in [`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean)) | Category | Normative / Compiler Basis & Forward-Compatibility Analysis |
| :--- | :--- | :--- |
| `Partial`, `Behavior`, `Language`, `StepResult`, `SmallStepMachine`, `ReachesPrefix`, `PrefixOutcome.isSafe`, `Language.WellFormed` (`support/ForwardCompatibleMirSemantics.lean:75-390`) | **(A)** | Pure semantic refinement framework. Crucially, `PrefixOutcome.isSafe` (`support/ForwardCompatibleMirSemantics.lean:255-260`) treats both `.terminated (.normal v)` and `.terminated .unwind` as safe (`True`) and `.failed`/`.stuck` as unsafe (`False`), which governs how abort-on-unwind terminators (`.unwindTerminate`) and `panic_nounwind_fmt` interact with UB checks (see Section 5.4). |
| `IntWidth.bitWidth` (`8, 16, 32, 64, 128`) and `IntWidth.modulus` ($2^w$) (`support/ForwardCompatibleMirSemantics.lean:401-421`) | **(A)** | `[r-type.numeric.int.size]` (`types/numeric.md:45-61`): fixed-width integer bit widths are normatively fixed across all targets and compilers. |
| Scalar `tySize`: `.uint w` / `.int w` $\mapsto w / 8$; `.bool` $\mapsto 1$; `.unit` $\mapsto 0` | **(A)** | `[r-layout.primitive.size-align]` (`type-layout.html:180-204`), `[r-type.bool.layout]` (`types/boolean.md:27-30`), `[r-layout.tuple.unit]` (`type-layout.html:279-282`). |
| Unconditional `.usize` / `.isize` $\mapsto$ `some 8` (`tySizeStepModel1`, `support/ForwardCompatibleMirSemantics.lean:613-614`) | **(B)** | **Target-Specific (64-bit target assumption)**. Per `[r-type.numeric.int.size.usize]` (`types/numeric.md:62-75`) and `[r-layout.primitive.size-align.usize]`, `size_of::<usize>()` equals the target pointer width ($\ge 16$ bits; 2, 4, or 8 bytes on supported Rust targets). |
| Single-field `.adt id` with `fields := [f]` $\mapsto$ `tySize f.ty` without checking `#[repr(...)]` (`tySizeStepModel1`, `support/ForwardCompatibleMirSemantics.lean:621-630`) | **(C)** if `#[repr(Rust)]` with non-ZST field; **(A)** only if `#[repr(transparent)]`, `#[repr(C)]` (no `align(N)`), or ZST `f.ty` | **Pinned-`rustc` Implementation Coincidence** for default `#[repr(Rust)]` single-field structs. `[r-layout.repr.rust.unspecified]` (`type-layout.html:415-419`) states: *"There are no guarantees of data layout made by this representation, except for those explicitly specified in this section."* Only `[r-layout.repr.rust.struct-zst]` (`type-layout.html:421-424`, all fields size 0 $\implies$ struct size 0), `[r-layout.repr.transparent.layout-abi]` (`type-layout.html:573-577`), and `[r-layout.repr.c.struct]` (`type-layout.html:443-478`, when `repr.align.is_none()`, since offset 0 rounded up to `align_of::<F>()` is `field.size`) guarantee `size_of::<S>() == size_of::<F>()`. |
| Multi-field `.adt` erased to `fields := []` under a `fields.foldl` size recurrence starting at `some 0` (`tySizeStepModel1`, `support/ForwardCompatibleMirSemantics.lean:624-629`) | **Unsound Bug** | Folding `[]` from `some 0` computes `tySize = some 0` for any multi-field struct whose fields were erased to `[]`, allowing 0-byte `transmute_copy::<(), Pair>` (`model1_multi_field_repr_rust_size_zero_bug`). Returning `none` for multi-field structs when layout is unmodeled is **Category (D)**. |
| Two's complement modular arithmetic and signed conversion (`intUnsignedModulus`, `toSignedInt`, `fromSignedInt`) | **(A)** for `.uint w`/`.int w`; **(B)** for `.usize`/`.isize` | `[r-type.numeric.int.two-complement]` (`types/numeric.md:45-61`). Target-specific when `.usize`/`.isize` modulus is fixed to $2^{64}$ rather than $2^{8 \cdot \text{ptrWidthBytes}}$. |
| Well-typedness of `MirVal.usize (bits : Nat)`: `\| .usize, .usize _ => True` vs. `bits < 2^(8 * ptrWidthBytes)` | **Soundness Caveat** if unbounded | Omitting `bits < 2^(8 * ptrWidthBytes)` for `.usize` (while enforcing `bits < w.modulus` for `.uint w` and `.int w`) admits `MirVal.usize (2^64)` as a valid 64-bit `usize` value in Lean, which satisfies `denoteInvariant { ne := 0 }` (`2^64 ≠ 0`) and renders `!= 2^64` invariants non-vacuous in Lean even though no 64-bit `usize` can ever equal $2^{64}$. |
| Local / field / deref place projection (`evalPlace`, `updatePlace`) and aggregate construction (`Rvalue.aggregate`) | **(A) / (D)** | Constructing a 1-field `#[repr(Rust)]` struct via `Rvalue.aggregate` and projecting its field via `PlaceElem.field 0` is **Category (A)** (`[r-expr.struct]`, `[r-expr.field]`) because Rust struct construction and field projection do not depend on in-memory byte layout. The Category (C) leak occurs **only** when `size_of` or `transmute_copy` exposes the in-memory layout of a `#[repr(Rust)]` struct. |
| Recursive single-field struct peeling and reconstruction in `transmute_copy` (`extractBitsModel1`, `constructValModel1`, `support/ForwardCompatibleMirSemantics.lean:638-687`) | **(C)** for `#[repr(Rust)]` wrappers; **(A)** for `#[repr(transparent)]` & `#[repr(C)]` (no `align(N)`); **(B)** for `.usize`/`.isize` | **Critical Forward-Compatibility Violation for `#[repr(Rust)]` (`V1–V4`)**: Unconditionally peeling and constructing any captured 1-field `.adt` assumes its in-memory representation is guaranteed to equal its sole field's bytes with zero padding. Under `[r-layout.repr.rust.unspecified]`, a `#[repr(Rust)]` struct `struct Wrapper(pub u64)` is **not** guaranteed to have the same layout or size as `u64` and may contain arbitrary padding bytes: (1) transmuting `Wrapper -> u64` reads potentially uninitialized padding bytes into `u64` (`[r-undefined.validity.scalar]`), and (2) transmuting `u64 -> Wrapper` assumes `size_of::<Wrapper>() == 8`, whereas in any compiler realization where `size_of::<Wrapper>() > 8`, `transmute_copy::<u64, Wrapper>(&x)` reads out-of-bounds past `x: u64` (`[r-undefined.pointer-access]`). |
| Post-monomorphization error (PME) admission at function entry (`MonoAdmitted` over `body.required_consts`) | **(A)** for path-executed `const` blocks; **(C)** for dead-branch `const` blocks | **Subtle Split Between Executed vs. Dead-Branch Consts**: <br>• **Executed `const { ... }` block (`[r-expr.block.const.evaluation]`, `expressions/block-expr.md:145-150`)**: *"If the const block expression is executed at runtime, then the constant is evaluated. Even if the value of the expression is unused, any errors that occur during evaluation will result in a compile-time error."* Along any execution path that actually reaches the `const { ... }` block, assuming `ConstSucceeds` is **Category (A)**. <br>• **Dead-branch `const { ... }` block (`[r-expr.block.const.not-executed]`, `expressions/block-expr.md:152-157`)**: *"If the const block expression is not executed at runtime, then the constant may or may not be evaluated. Consequently, any errors that would occur during evaluation may or may not result in a compile-time error."* Assuming `ConstSucceeds` at function entry for a `const { assert!(...) }` block sitting inside an untaken `if false` branch is **Category (C)** (relying on `rustc`'s eager `RequiredConstsVisitor` in `compiler/rustc_mir_transform/src/required_consts.rs:14-48` and `collect_items_rec` in `compiler/rustc_monomorphize/src/collector.rs:1349-1362`). |

#### 1.2 Compiler MIR Extraction Predicates (`rustc 1.98.0-nightly`)

| Extraction Pattern | Category | Normative / Compiler Basis & Forward-Compatibility Analysis |
| :--- | :--- | :--- |
| Extracting `Runtime(PostCleanup)` MIR via `tcx.mir_drops_elaborated_and_const_checked(def_id)` | **(C) / (A)** | Stage boundary of `rustc` MIR (`compiler/rustc_mir_transform/src/lib.rs:514-579`): runs after `ElaborateDrops` and `check_consts`, before post-cleanup optimizations (`CheckAlignment`, `InstCombine`, `ReferencePropagation`, `PreCodegen`). |
| Lowering a single-variant, single-field struct with `fields := [f]` whenever `repr.align.is_none() && repr.pack.is_none()` and `tcx.layout_of(self_ty).size == tcx.layout_of(field_ty).size`, without checking `repr.transparent()` or `repr.c()` | **(C)** | Because `rustc 1.98.0`'s `LayoutCalculator::univariant_biased` (`compiler/rustc_abi/src/layout.rs:1283-1320`) lays out a 1-field `#[repr(Rust)]` struct `struct Wrapper(T)` with `size == field.size` (even under `-Z randomize-layout`), an extractor that checks only `adt_layout.size == field_layout.size` lowers **every** 1-field `#[repr(Rust)]` struct as indistinguishable from `#[repr(transparent)]`. |
| Lowering `TerminatorKind::Assert { cond, expected, target, unwind }` to `.unwindTerminate` whenever `!matches!(unwind, mir::UnwindAction::Continue)` | **(C)** / **Soundness Trap** | When `.unwindTerminate` transitions unconditionally to `.terminated .unwind` (`PrefixOutcome.isSafe = True`), replacing a `TerminatorKind::Assert` whose `unwind` action is `UnwindAction::Cleanup(bb)`, `UnwindAction::Unreachable`, or `UnwindAction::Terminate(_)` with `.unwindTerminate` **never branches to `target` and never executes subsequent statements in `target`**. In `Runtime(PostCleanup)` MIR (`ElaborateDrops`), if a function has a local requiring drop (`UnwindAction::Cleanup(cleanup_bb)`) or is `extern "C"` (`UnwindAction::Terminate(Abi)`), this silently truncates execution at the `Assert` and treats the remainder of the function as vacuously safe (`.terminated .unwind`). |
| Checking `#[rustc_layout_scalar_valid_range_*]` niches via `BackendRepr::Scalar` `valid_range` for `core::num::NonZero<T>` | **(A)** | Matches the standard library layout guarantee of `core::num::NonZero<T>` (`#[repr(transparent)]` with non-zero niche). |

---

### 2. Four Concrete `#[repr(Rust)]` Transmutation Patterns Violating Zerocopy's Soundness Policy (`POLICIES.md:31-49`)

Basis: normative, documentation, source, derived

Zerocopy's soundness policy (`google/zerocopy@8fb35253fbc703cb2cd0997f4efcda76cf9062b6`,
`POLICIES.md:31-49`) states:

> *"Broadly, a rationale for the soundness of layout-dependent code must connect
> two endpoints: the definition of a target type (including its layout-relevant
> attributes and the layouts of its constituent fields) and the preconditions of
> the operations performed on that type. Each step in that reasoning must be load-
> bearing, and thus must be justified by the normative text of the Rust Reference
> or the standard library documentation. Reasoning may not rely on
> implementation details of `rustc`, even if they have been stable in practice for
> a long time, nor may it rely on informal consensus about how Rust 'ought' to
> work."*

Whenever a MIR semantics and extractor treat single-field structs whose pinned
`rustc` size equals their field's size as layout-transparent without checking
`#[repr(transparent)]` or `#[repr(C)]` (**Model 1** in
[`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean)),
the verifier unsoundly accepts four distinct code patterns (**V1–V4**) that
violate Zerocopy's soundness policy and the Rust Reference:

1. **Pattern V1 — Direct `transmute_copy` from a primitive into a default `#[repr(Rust)]` single-field struct (`u64 -> Wrapper`)**:
   ```rust
   pub struct Wrapper(pub u64); // default #[repr(Rust)] — NO #[repr(transparent)] or #[repr(C)]!

   pub unsafe fn transmute_u64_to_repr_rust(x: u64) -> Wrapper {
       unsafe { core::mem::transmute_copy::<u64, Wrapper>(&x) }
   }
   ```
   - **Why Model 1 accepts it**: `Wrapper` has 1 variant, 1 field (`u64`),
     `repr.align == None`, `repr.pack == None`, and
     `adt_layout.size (8) == field_layout.size (8)` in `rustc 1.98.0`, so Model 1
     assigns `tySizeModel1 Wrapper = some 8 == tySizeModel1 u64` and steps
     `.transmuteCopy` to `.terminated (.normal (.adt "Wrapper" (.u64 x)))`
     (`model1_unsoundly_accepts_repr_rust_transmute`).
   - **Why it violates `rust-lang/reference` and `POLICIES.md`**: Under
     `[r-layout.repr.rust.unspecified]` (`type-layout.html:415-419`), `Wrapper`
     is not guaranteed to have `size_of::<Wrapper>() == 8`. In any conforming
     compiler realization where `size_of::<Wrapper>() == 16` (e.g., 8 bytes of
     padding around the `u64` field), `core::mem::transmute_copy::<u64, Wrapper>(&x)`
     performs an out-of-bounds `ptr::read` of 16 bytes from an 8-byte `u64`
     allocation (`[r-undefined.pointer-access]`).

2. **Pattern V2 — Direct `transmute_copy` from a default `#[repr(Rust)]` single-field struct into a primitive (`Wrapper -> u64`)**:
   ```rust
   pub struct Wrapper(pub u64); // default #[repr(Rust)]

   pub unsafe fn transmute_repr_rust_to_u64(w: Wrapper) -> u64 {
       unsafe { core::mem::transmute_copy::<Wrapper, u64>(&w) }
   }
   ```
   - **Why Model 1 accepts it**: `extractBitsModel1` peels `.adt` to `w.0` and
     `constructValModel1` builds `.u64`.
   - **Why it violates `rust-lang/reference` and `POLICIES.md`**: If a compiler
     realization places `u64` at offset `8` inside a 16-byte `Wrapper` (with 8
     leading uninitialized padding bytes at offset `0..8`),
     `transmute_copy::<Wrapper, u64>(&w)` reads the first 8 bytes of `w`—which
     are uninitialized padding—into a `u64`, causing immediate undefined behavior
     under `[r-undefined.validity.scalar]` (`behavior-considered-undefined.md:208-212`).

3. **Pattern V3 — Nested `#[repr(Rust)]` single-field struct inside an outer `#[repr(transparent)]` wrapper (`Outer(Inner(u32))`)**:
   ```rust
   pub struct Inner(pub u32); // default #[repr(Rust)]!

   #[repr(transparent)]
   pub struct Outer(pub Inner); // outer is transparent, but inner is repr(Rust)!

   pub unsafe fn transmute_nested(x: u32) -> Outer {
       unsafe { core::mem::transmute_copy::<u32, Outer>(&x) }
   }
   ```
   - **Why Model 1 accepts it**: Both `tySizeStepModel1` and
     `extractBitsModel1`/`constructValModel1` recurse through arbitrary chains
     of 1-field `.adt` wrappers without checking that every link in the chain
     is `#[repr(transparent)]` or `#[repr(C)]`.
   - **Why it violates `rust-lang/reference` and `POLICIES.md`**: Under
     `[r-layout.repr.transparent.layout-abi]` (`type-layout.html:573-577`),
     `Outer` is only guaranteed to have the same layout as `Inner`; because
     `Inner` is `#[repr(Rust)]`, `Inner`'s layout relative to `u32` is
     unspecified.

4. **Pattern V4 — Single-field `#[repr(Rust)]` struct with a non-zero field invariant transmuted from a constrained primitive (`u32 -> MyNonZeroU32`)**:
   ```rust
   pub struct MyNonZeroU32(u32); // missing #[repr(transparent)]!

   pub unsafe fn make_nonzero(x: u32) -> MyNonZeroU32 {
       // Precondition: x != 0
       unsafe { core::mem::transmute_copy::<u32, MyNonZeroU32>(&x) }
   }
   ```
   - **Why Model 1 accepts it**: Attaching a `!= 0` field invariant to
     `MyNonZeroU32` without requiring `#[repr(transparent)]` or `#[repr(C)]`
     allows `constructValModel1` to succeed whenever `x != 0`.
   - **Why it violates `rust-lang/reference` and `POLICIES.md`**: Standard
     library `core::num::NonZero<T>` is explicitly `#[repr(transparent)]`. A
     user-defined `MyNonZeroU32(u32)` without `#[repr(transparent)]` or
     `#[repr(C)]` has no layout guarantee in the Rust Reference.

---

### 3. Why `rustc`'s `-Z randomize-layout` Does Not Detect All Non-Guaranteed Layout Assumptions

Basis: normative, source, execution

To test what `-Z randomize-layout` in `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`
actually varies versus what the Rust Reference (`82da570bafd9efed421bdbae0f8603ede8dd308b`)
leaves unspecified, we wrote and executed
[`support/randomize_layout_probe.rs`](support/randomize_layout_probe.rs) across
unrandomized compilation and `-Z randomize-layout -Z layout-seed=0..15`,
recording the exact JSONL output in
[`support/randomize_layout_probe.jsonl`](support/randomize_layout_probe.jsonl),
and inspected `rustc`'s layout engine in `compiler/rustc_abi/src/layout.rs`,
`compiler/rustc_abi/src/lib.rs`, `compiler/rustc_middle/src/ty/mod.rs`, and
`compiler/rustc_ty_utils/src/layout.rs`.

#### 3.1 Normative Freedom vs. Empirical `-Z randomize-layout` Behavior (`rustc 1.98.0-nightly`)

| Type & Construct | Repr | Normative Rust Reference Rule (`82da570b`) | Empirical Behavior across Default & `-Z randomize-layout -Z layout-seed=0..15` ([`support/randomize_layout_probe.jsonl`](support/randomize_layout_probe.jsonl)) | Detected by `-Z randomize-layout`? | Sound to Assume Fixed under `POLICIES.md`? |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `struct SingleRust(u64)` | `repr(Rust)` | **Unspecified** (`[r-layout.repr.rust.unspecified]`, `type-layout.html:415-419`): size, alignment, and field offset of non-ZST `repr(Rust)` structs are not guaranteed. | Always `size = 8, align = 8, off0 = 0` across all 16 seeds | **NO** | **NO** |
| `#[repr(transparent)] struct SingleTrans(u64)` | `repr(transparent)` | **Guaranteed** (`[r-layout.repr.transparent.layout-abi]`, `type-layout.html:573-577`): layout and ABI match `u64`. | Always `size = 8, align = 8, off0 = 0` | N/A (Guaranteed) | **YES** |
| `#[repr(C)] struct SingleC(u64)` | `repr(C)` | **Guaranteed** (`[r-layout.repr.c.struct]`, `type-layout.html:443-478`): field 0 at offset 0; total size is `8` rounded up to `align_of::<u64>() == 8`. | Always `size = 8, align = 8, off0 = 0` | N/A (Guaranteed) | **YES** |
| `struct RustWithZst((), u64)` | `repr(Rust)` | **Unspecified** (`[r-layout.repr.rust.unspecified]`) | `size = 8, align = 8`, `off0_zst ∈ {0, 8}` (`0` in default & seeds 0,1,2,4,6,8,10,12,13,15; `8` in seeds 3,5,7,9,11,14), `off1_u64 = 0` | ZST offset varies; `u64` offset/size stay `0`/`8` | **NO** |
| `#[repr(transparent)] struct TransWithZst((), u64)` | `repr(transparent)` | **Guaranteed for `u64` field & overall layout; unspecified for 1-ZST field offset** (`[r-layout.repr.transparent.layout-abi]`) | `size = 8, align = 8`, `off0_zst ∈ {0, 8}` (`0` in default & seeds 0,1,3,5,6,7,9,11,12,14; **`8` in seeds 2,4,8,10,13,15**!), `off1_u64 = 0` | **YES** for 1-ZST offset (because `IS_TRANSPARENT` is not in `FIELD_ORDER_UNOPTIMIZABLE`!) | **YES** for overall layout & non-ZST field at offset `0`; **NO** for ZST field offset |
| `struct MultiPaddedRust(u8, u16, u8)` | `repr(Rust)` | **Unspecified** (`[r-layout.repr.rust.unspecified]`) | **`size ∈ {4, 6}`**, `align = 2`: in default & most seeds `size = 4` (`(2, 0, 3)` or `(0, 2, 1)`), but in **seeds 2 and 12**, field order `(0, 2, 4)` produces **`size = 6`** (2 bytes of inter-field/trailing padding)! | **YES (`size_of` changes between 4 and 6!)** | **NO** |
| `#[repr(C)] struct MultiPaddedC(u8, u16, u8)` | `repr(C)` | **Guaranteed** (`[r-layout.repr.c.struct]`): `(off0, off1, off2) = (0, 2, 4)`, `size = 6, align = 2` (with uninit padding at bytes 1 and 5). | Always `size = 6, align = 2, (0, 2, 4)` | N/A (Guaranteed) | **YES** (for offsets/size; bytes 1 & 5 are uninit padding) |
| `struct WithUnsizableTail<T: ?Sized>(u8, u16, T)` instantiated at `T = u8` | `repr(Rust)` | **Unspecified** (`[r-layout.repr.rust.unspecified]`) | Always `size = 4, align = 2, off0_u8 = 2, off1_u16 = 0, off2_tail_u8 = 3` across **all 16 seeds**! The tail field `T` is **never** shuffled with earlier fields and `size` never becomes `6`! | **NO** (tail field is excluded from shuffling by `StructKind::MaybeUnsized`!) | **NO** |
| `type TuplePadded = (u8, u16, u8)` | `repr(Rust)` tuple | **Unspecified** (`[r-layout.tuple.def]`, `type-layout.html:274-277`: *"Tuples are laid out according to the `Rust` representation."*) | Always `size = 4, align = 2, (off0, off1, off2) = (2, 0, 3)` across default and **all 16 seeds**! | **NO (`-Z randomize-layout` never shuffles tuples!)** | **NO** |
| `struct NicheStructDiff(bool, NonZeroU8)` & `Option<...>` | `repr(Rust)` | **Unspecified** (`[r-layout.repr.rust.unspecified]`; `Option<T>` niche optimization is only guaranteed for specific pointer/reference/`NonZero` types in `[r-layout.option-niche]`, `type-layout.html:360-398`). | Always `size = 2, opt_size = 2`, using `bool` (254 niches > `NonZeroU8`'s 1 niche) as niche, **but** `(off0_bool, off1_nz)` alternates between `(0, 1)` (`None` bytes `[2, 255]`, placing discriminant `2` at byte `0` and leaving byte `1` uninitialized `0xFF`) and `(1, 0)` (`None` bytes `[255, 2]`, placing discriminant `2` at byte `1`, leaving byte `0` uninitialized `0xFF`!) | **YES** (moves `Option` discriminant offset!) | **NO** |
| `struct NicheStructEqual(NonZeroU8, NonZeroU8)` & `Option<...>` | `repr(Rust)` | **Unspecified** (`[r-layout.repr.rust.unspecified]`) | Always `size = 2, opt_size = 2`, `(off0_nz0, off1_nz1)` alternates between `(0, 1)` (field `1` at offset `1` chosen as niche; `None` bytes `[255, 0]`) and `(1, 0)` (field `0` at offset `1` chosen as niche; `None` bytes `[255, 0]`) | **YES** (changes which field carries the `Option` niche!) | **NO** |
| `enum MultiEnum { A(u8, u16, u8), B(u32, u8) }` | `repr(Rust)` enum | **Unspecified** (`[r-layout.repr.rust.unspecified]`) | **`size ∈ {8, 12}`**, **`opt_size ∈ {8, 12}`**, `align = 4` (`8` in default & seeds 6,9,10,11; **`12`** in seeds 0..5,7,8,12..15) | **YES (`size_of` changes between 8 and 12!)** | **NO** |

#### 3.2 `rustc 1.98.0-nightly (f8a08b688)` Code Mechanics Explaining `-Z randomize-layout`'s Blind Spots

1. **Where `ReprFlags::RANDOMIZE_LAYOUT` and `field_shuffle_seed` are constructed (`compiler/rustc_middle/src/ty/mod.rs:1506-1604`, `repr_options_of_def`)**:
   - When `tcx.sess.opts.unstable_opts.randomize_layout` is enabled (`L1593-L1598`), `rustc` sets `flags.insert(ReprFlags::RANDOMIZE_LAYOUT)` on ADT `ReprOptions` and computes
     `field_shuffle_seed = tcx.def_path_hash(did).0.to_smaller_hash() ^ tcx.sess.opts.unstable_opts.layout_seed.unwrap_or(0)`.
   - Because `repr_options_of_def` is only called for ADT definitions (`DefId`), **tuples** `(T0, T1, ...)`—whose layout is computed in `compiler/rustc_ty_utils/src/layout.rs:207-211, 571-576` using `ReprOptions::default()`—**never** receive `ReprFlags::RANDOMIZE_LAYOUT`, even though `[r-layout.tuple.def]` specifies that non-unit tuples have the `Rust` representation.
2. **Which representations inhibit field reordering (`compiler/rustc_abi/src/lib.rs:98-101, 219-227`)**:
   - `FIELD_ORDER_UNOPTIMIZABLE = ReprFlags::IS_C.union(ReprFlags::IS_SIMD).union(ReprFlags::IS_SCALABLE).union(ReprFlags::IS_LINEAR)`.
   - `ReprOptions::inhibit_struct_field_reordering(&self)` returns `self.flags.intersects(FIELD_ORDER_UNOPTIMIZABLE) || self.int.is_some()`.
   - Crucially, **`ReprFlags::IS_TRANSPARENT` is NOT in `FIELD_ORDER_UNOPTIMIZABLE`**. Thus, when a `#[repr(transparent)]` struct has 1-ZST fields alongside its single non-ZST field (`struct TransWithZst((), u64)`), `optimize_field_order` remains `true` and `-Z randomize-layout` shuffles the 1-ZST field between offset `0` and offset `8`, while the single non-ZST field (`u64`) necessarily remains at offset `0`.
3. **Why single-field `#[repr(Rust)]` structs are never randomized by `-Z randomize-layout` (`compiler/rustc_abi/src/layout.rs:1110-1140`, `LayoutCalculator::univariant_biased`)**:
   - In `univariant_biased`:
     ```rust
     if optimize_field_order && fields.len() > 1 {
         let end = if matches!(kind, StructKind::MaybeUnsized) {
             fields.len() - 1
         } else {
             fields.len()
         };
         let optimizing = &mut in_memory_order.raw[..end];
         if repr.flags.contains(ReprFlags::RANDOMIZE_LAYOUT) {
             ...
             shuffle(optimizing);
         } else { ... }
     }
     ```
   - Because of the guard `fields.len() > 1` (`L1110`) and because `univariant_biased` never inserts synthetic leading or trailing padding bytes (`L1254-L1320`), a 1-field `#[repr(Rust)]` struct `struct SingleRust(u64)` always has `in_memory_order = [0]`, `offsets[0] = 0`, and `size = field.size` under `-Z randomize-layout`—even though `[r-layout.repr.rust.unspecified]` makes no such guarantee.

---

### 4. Architectural Comparison of Three Candidate MIR Semantic Models (`Models 1, 2, and 3`)

Basis: normative, source, execution, derived

In [`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean),
we formalize and compare three candidate semantic architectures on top of a
self-contained `Preorder` / `Partial` / `Behavior` / `Language` / `StepResult` /
`SmallStepMachine` refinement spine (`support/ForwardCompatibleMirSemantics.lean:75-390`).

| Property / Operation | Model 1: Pinned-`rustc` Single-Field Layout Oracle (`Sem_PinnedRustc`) | Model 2: Naive Fail-Closed `Option` Oracle (`Sem_NaiveFailClosed`) | Model 3: Demonic Quantification over `ReferenceAdmissible` Realizations (`Sem_ForwardCompatible`) |
| :--- | :--- | :--- | :--- |
| `transmute_copy::<u64, ReprRustWrapper>(&x)` (`#[repr(Rust)]`) | **Unsoundly accepts** (`model1_unsoundly_accepts_repr_rust_transmute`) | Rejects (`model2_rejects_repr_rust_transmute_u64`) | **Soundly rejects** (`model3_rejects_repr_rust_u64_transmute`, via witness `env_16`) |
| Multi-field `#[repr(Rust)]` `struct Pair(u32, u32)` with `fields := []` | **Computes `tySize = some 0`** and accepts `transmute_copy::<(), Pair>` $\to$ `Val.agg []` (`model1_multi_field_repr_rust_size_zero_bug`) | Rejects (`tySize = none`) | **Soundly constrains `size ≥ 8`** across all `ReferenceAdmissible` realizations |
| `size_of::<RustZstWrapper>() == 0` (`#[repr(Rust)]` all-ZST fields, `r[layout.repr.rust.struct-zst]`) | Accepts | **Falsely rejects** (`tySize = none`) | **Soundly accepts** across all `ReferenceAdmissibleWithZstLaw` realizations (`repr_rust_zst_vs_non_zst_discrimination`) |
| `transmute_copy::<u64, ReprTransparentWrapper>(&x)` (`#[repr(transparent)]`) | Accepts | Accepts | **Soundly accepts** across all `ReferenceAdmissible` realizations (`model3_accepts_repr_transparent_and_padding_free_repr_c_transmute`) |
| `transmute_copy::<u64, ReprCWrapper>(&x)` (`#[repr(C)]`, padding-free) | Accepts | Accepts | **Soundly accepts** across all `ReferenceAdmissible` realizations (`model3_accepts_repr_transparent_and_padding_free_repr_c_transmute`) |
| `transmute::<extern "C" fn() -> u64, extern "C" fn() -> Wrapper>` | Unmodeled | Unmodeled | **Accepts `#[repr(transparent)]`; rejects `#[repr(C)]`** (`in_memory_transmute_vs_extern_c_fn_abi_discrimination`) |
| `transmute_copy::<WithU64, [u8; 16]>` (`#[repr(C)] { a: u32, b: u64 }`) | Host-dependent | Host-dependent | **Soundly rejects on both `i686` (`size = 12`) and `x86_64` (padding at `4..8`)** (`repr_c_target_u64_alignment_and_aggregate_align_boundary`) |
| Reflexive `transmute_copy::<ReprRustWrapper, ReprRustWrapper>(&w)` | Accepts | **Falsely rejects** (`model2_falsely_rejects_reflexive_and_polymorphic_ops`) | **Soundly accepts** across all `ReferenceAdmissible` realizations (`model3_accepts_reflexive_repr_rust_transmute_and_copy`) |
| `copy_nonoverlapping::<ReprRustWrapper>(&src, &mut dst, 1)` | Accepts (1-field only) | **Falsely rejects** (`model2_falsely_rejects_reflexive_and_polymorphic_ops`) | **Soundly accepts** across all `ReferenceAdmissible` realizations (`model3_accepts_reflexive_repr_rust_transmute_and_copy`) |
| `size_of::<ReprRustWrapper>() == size_of::<ReprRustWrapper>()` | Accepts | **Falsely rejects** (`model2_falsely_rejects_reflexive_and_polymorphic_ops`) | **Soundly accepts** (`true` in every `env`, `model3_accepts_reflexive_repr_rust_transmute_and_copy`) |
| Target-parametric `1usize + 1usize` (`ptrWidthBytes ∈ {2, 4, 8}`) | Assumes 64-bit only | **Falsely rejects** (`model2_falsely_rejects_reflexive_and_polymorphic_ops`) | **Soundly accepts** on all 16/32/64-bit targets (`model3_target_parametric_vs_cfg_gated_usize`) |
| `60000usize + 10000usize` (overflows 16-bit `usize`) | Unsoundly accepts without `cfg` guard | Rejects even under `#[cfg(target_pointer_width = "64")]` | **Rejects under `.any`; accepts under `.ptrWidth64`** (`model3_target_parametric_vs_cfg_gated_usize`) |
| `assert_unsafe_precondition!` + `panic_nounwind_fmt` (`UbChecks`) | Fails closed on `runtimeChecks` | Fails closed on `runtimeChecks` | **Refines `safeUnwindOrNormalSpec` iff `cond = true`** (`ub_checks_dual_soundness_trap_and_repair`) |
| Refinement bridge to pinned `rustc` (`Sem_PinnedRustcEnv ≤ Sem_ForwardCompatible`) | N/A | N/A | **Proved** via `checkReferenceAdmissible_sound` (`model3_refinement_bridge_and_tcb_stratification`) |

#### 4.1 Model 1 (`Sem_PinnedRustc`)

Model 1 (`support/ForwardCompatibleMirSemantics.lean:593-850`) formalizes both:
1. **`model1_unsoundly_accepts_repr_rust_transmute`**: When an extractor emits
   `fields := [{ ty := .uint .u64, access := .pubSafe }]` for
   `#[repr(Rust)] pub struct ReprRustWrapper(pub u64)` without checking
   `decl.repr`, `Sem_PinnedRustc` satisfies
   $$\forall x : \mathbb{N},\; (\mathsf{Sem\_PinnedRustc}\;\mathsf{testCrateModel1}\;(\mathsf{transmuteCopy}\;\mathtt{u64}\;\mathtt{ReprRustWrapper}\;x)).\mathsf{sem}\;() \;\le\; \mathsf{safeSpec}$$
   and steps deterministically to `.terminated (.normal (.adt "ReprRustWrapper" (.u64 x)))`.
2. **`model1_multi_field_repr_rust_size_zero_bug`**: Under the `fields.foldl`
   size recurrence (`tySizeStepModel1`, `support/ForwardCompatibleMirSemantics.lean:611-631`),
   emitting `fields := []` for a 2-field `#[repr(Rust)] pub struct Pair(pub u32, pub u32)`
   computes `tySizeModel1 testCrateModel1 (.adt "Pair") = some 0`, causing
   `size_of::<Pair>()` to evaluate to `.usize 0` and `reinterpretValModel1` to
   accept `transmute_copy::<(), Pair>(&())` producing `Val.agg []`.

#### 4.2 Model 2 (`Sem_NaiveFailClosed`)

Model 2 (`support/ForwardCompatibleMirSemantics.lean:852-1044`) replaces
unguaranteed `tySize` queries (`#[repr(Rust)]` ADTs and unpinned `usize`) with
`Option.none` (stepping to `StepResult.failed`).
While **`model2_rejects_repr_rust_transmute_u64`** proves that Model 2 rejects
`transmute_copy::<u64, ReprRustWrapper>(&x)`,
**`model2_falsely_rejects_reflexive_and_polymorphic_ops`** proves that Model 2
steps to `StepResult.err` (and violates `≤ safeSpec`) on all four Reference-sound
operations:
- reflexive `transmute_copy::<ReprRustWrapper, ReprRustWrapper>(&w)`,
- `copy_nonoverlapping::<ReprRustWrapper>(&src, &mut dst, 1)`,
- `size_of::<ReprRustWrapper>() == size_of::<ReprRustWrapper>()`, and
- target-width-parametric `1usize + 1usize`.

Why does a naive `Option` oracle fail on these four operations? Because in any
single execution environment $e \in \mathsf{ReferenceAdmissible}$,
$\mathsf{size\_of}\langle\mathtt{ReprRustWrapper}\rangle_e$ is a **fixed,
deterministic natural number** $n_e \ge 8$ (so $n_e = n_e$ holds identically in
every $e$), and `transmute_copy::<T, T>(&w)` reads and writes the exact same
type `T` (including its padding bytes at identical offsets in $e$, without
reading uninitialized padding into a scalar or violating field validity in $e$).
Replacing $n_e$ with `Option.none` conflates *"unknown across environments"*
with *"undefined within a single environment."*

#### 4.3 Model 3 (`Sem_ForwardCompatible`, Demonic Quantification over `ReferenceAdmissible`)

Model 3 (`support/ForwardCompatibleMirSemantics.lean:1046-2496`) resolves this
cleanly inside the `Language` / `Behavior` / `StepResult` refinement framework:

1. **Syntactic Representation Attribution (`ReprAttr`)**:
   Every `AdtDecl` carries its syntactic `#[repr(...)]` attribute (`ReprAttr`:
   `.rust`, `.transparent`, `.c alignOpt packOpt`, `.primitiveInt w`,
   `.cAndInt w`) alongside its actual syntactic `fields : List FieldDecl`
   (never erasing multi-field structs to `fields := []`).
2. **Demonic Quantification over `ReferenceAdmissible` Realizations**:
   A `CompilerRealization` (`env`) specifies a concrete, deterministic choice of
   all implementation-defined and target-dependent parameters (`ptrWidthBytes`,
   `adtLayout : String → AdtLayoutRealization`, and `evalDeadBranchConsts : Bool`).
   The normative predicate `ReferenceAdmissible c targetCfg env` (and its
   executable decision procedure `checkReferenceAdmissible`, proved equivalent
   in **`checkReferenceAdmissible_iff`** and sound in
   **`checkReferenceAdmissible_sound`**) constrains `env` by the exact laws of
   the Rust Reference:
   - `r[type.numeric.int.size.usize]`: `env.ptrWidthBytes ∈ {2, 4, 8}` (and
     satisfies any active `#[cfg(target_pointer_width = "...")]` constraint
     `targetCfg`).
   - `r[layout.repr.transparent.layout-abi]`: For `.transparent`, `L.size`,
     `L.align`, and `L.hasUninitPadding` equal those of the single non-ZST field
     at offset `0`.
   - `r[layout.repr.c.struct]`: For `.c none none`, `L` equals the deterministic
     C forward-offset accumulation recurrence `reprCForwardLayout env decl`
     (`alignUp` per field, `hasUninitPadding = true` iff any inter-field or
     trailing alignment gap is non-zero or any field has padding).
   - `r[layout.repr.rust]`: For `.rust`, `L.align ≥ 1`, `L.size ≥ sumFieldSizes env decl.fields`,
     and `L.size > sumFieldSizes` implies `L.hasUninitPadding = true` (leaving
     exact field offsets, total size $\ge \sum \text{fields}$, and padding
     presence unconstrained).
3. **Isomorphic Embedding into `StepResult.choice` and `Language.Query`**:
   We formalize both ways of embedding `ReferenceAdmissible` into
   `Language` and `StepResult`:
   - **Step-0 `StepResult.choice` (`Sem_ForwardCompatible`)**: At initial state
     `.choosing`, the machine transitions via
     $$\mathsf{StepResult.choice}\;\bigl(\{\, .\mathsf{running}\;\mathit{env}.\mathsf{val} \mid \mathit{env} : \{ \mathit{env} // \mathsf{ReferenceAdmissible}\;c\;\mathit{targetCfg}\;\mathit{env} \} \,\}\bigr)$$
   - **Query-Indexed `Language.Query` (`Sem_ForwardCompatible_Query`)**: Sets
     `ForwardQuery := { env // ReferenceAdmissible c targetCfg env } × Unit`.
   - **`sem_forwardCompatible_choice_iff_query`** proves constructively (`↔`)
     that for any postcondition `post : MirVal → Prop`, `Sem_ForwardCompatible`
     satisfies `safePostSpec _ post` if and only if `Sem_ForwardCompatible_Query`
     satisfies `querySafePostSpec _ post`, and both are equivalent to:
     $$\forall \mathit{env},\; \mathsf{ReferenceAdmissible}\;c\;\mathit{targetCfg}\;\mathit{env} \;\longrightarrow\; \exists v,\; \mathsf{evalOpInEnv}\;c\;\mathit{env}\;\mathit{op} = .\mathsf{terminated}\;(.\mathsf{normal}\;v) \;\wedge\; \mathit{post}\;v$$
4. **Core Discrimination and Refinement Bridge Theorems of Model 3**:
   - **`model3_rejects_repr_rust_u64_transmute`**: Constructs two concrete
     admissible realizations `env_8` (`size = 8, hasUninitPadding = false`) and
     `env_16` (`size = 16, hasUninitPadding = true`), proves both satisfy
     `ReferenceAdmissible testCrate .any`, and proves that because
     `transmute_copy::<u64, ReprRustWrapper>(&x)` steps to `StepResult.failed`
     in `env_16`, `Sem_ForwardCompatible` does **not** refine `safeSpec`.
   - **`model3_accepts_repr_transparent_and_padding_free_repr_c_transmute`**:
     Proves that across **all** `ReferenceAdmissible` environments,
     `transmute_copy::<u64, ReprTransparentWrapper>(&x)` and
     `transmute_copy::<u64, ReprCWrapper>(&x)` succeed and refine `safePostSpec`.
   - **`model3_accepts_reflexive_repr_rust_transmute_and_copy`**: Proves that
     across **all** `ReferenceAdmissible` environments (regardless of whether
     `ReprRustWrapper` has size 8, 16, or 1,024 or uninitialized padding),
     reflexive `transmute_copy::<ReprRustWrapper, ReprRustWrapper>(&w)`,
     `copy_nonoverlapping::<ReprRustWrapper>(&src, &mut dst, 1)`, and
     `size_of::<ReprRustWrapper>() == size_of::<ReprRustWrapper>()` all succeed
     and refine `safePostSpec` (via symbolic value representation
     `ValBytes.opaqueAdt "ReprRustWrapper" n (.adt "ReprRustWrapper" inner)`).
   - **`model3_target_parametric_vs_cfg_gated_usize`**: Proves that `1usize + 1usize`
     succeeds across all 16/32/64-bit targets (`.any`), whereas
     `60000usize + 10000usize` fails under `.any` (overflowing on 16-bit targets
     in `env_ptr16`) and succeeds under `.ptrWidth64` (`#[cfg(target_pointer_width = "64")]`).
   - **`model3_refinement_bridge_and_tcb_stratification`** (and
     **`model3_dead_branch_required_consts_discrimination`**): Proves the general
     refinement bridge
     $$\mathsf{ReferenceAdmissible}\;c\;\mathit{targetCfg}\;\mathit{env}_{\text{rustc}} \;\longrightarrow\; (\mathsf{Sem\_PinnedRustcEnv}\;c\;\mathit{env}_{\text{rustc}}\;\mathit{op}).\mathsf{sem}\;() \;\le\; (\mathsf{Sem\_ForwardCompatible}\;c\;\mathit{targetCfg}\;\mathit{op}).\mathsf{sem}\;()$$
     so any spec $S$ proved for `Sem_ForwardCompatible` (`Sem_ForwardCompatible ≤ S`)
     automatically holds for every Reference-conforming compiler realization
     `env_rustc` (`Sem_PinnedRustcEnv ≤ S`) by `Preorder.le_trans`, while also
     proving that a `const { assert!(false) }` in an untaken dead branch cannot
     rescue downstream UB across all admissible realizations (`env_lazy_dead_const`).

---

### 5. Normative Layout, Target ABI, and `UbChecks` Boundary Extensions

Basis: normative, source, derived

Section 6 of [`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean)
establishes four additional boundary theorems governing `#[repr(Rust)]` ZSTs,
target-dependent `u64` alignment and `aggregate_align` in `#[repr(C)]` and
`#[repr(transparent)]`, in-memory transmutation vs. `extern "C" fn` calling
conventions, and `core::ub_checks` + `panic_nounwind_fmt`.

#### 5.1 `r[layout.repr.rust.struct-zst]` vs. Non-ZST `#[repr(Rust)]` (`repr_rust_zst_vs_non_zst_discrimination`)

Under `r[layout.repr.rust.struct-zst]` (`rust-lang/reference@82da570b`,
`src/type-layout.md`, lines 421–424):

> *"A struct with the default representation where all fields have a size of 0
> will also have a size of 0."*

We refine `ReferenceAdmissible` to `ReferenceAdmissibleWithZstLaw` (requiring
`L.size = 0 ∧ L.hasUninitPadding = false` whenever `decl.repr == .rust` and
`sumFieldSizes env decl.fields == some 0`) and prove in
**`repr_rust_zst_vs_non_zst_discrimination`** (`support/ForwardCompatibleMirSemantics.lean:2639-2666`):
1. Across **all** realizations `env` satisfying `ReferenceAdmissibleWithZstLaw`,
   `#[repr(Rust)] pub struct RustZstWrapper(pub ())` has `size = 0`,
   `hasUninitPadding = false`, and `size_of::<RustZstWrapper>() == 0`.
2. By contrast, for `#[repr(Rust)] pub struct ReprRustWrapper(pub u64)`, both
   `env_8_zst` (`size = 8`) and `env_16_zst` (`size = 16`) satisfy
   `ReferenceAdmissibleWithZstLaw`, refuting `size_of::<ReprRustWrapper>() == 8`.

#### 5.2 Target `u64` Alignment (`i64AlignBytes ∈ {4, 8}`) and `aggregateAlignBytes` Boundary (`repr_c_target_u64_alignment_and_aggregate_align_boundary`)

Across built-in `rustc_target` specifications in `rustc 1.98.0-nightly (f8a08b688)`:
- `align_of::<u64>()` (`i64AlignBytes`) is `4` on 32-bit x86 SysV
  (`i686-unknown-linux-gnu`) and `8` on `x86_64-unknown-linux-gnu`.
- Every built-in `rustc_target` spec has `aggregateAlignBytes = 1` (none sets LLVM
  data-layout `a:N` above 1 byte), whereas a custom target JSON setting `-a:32`
  (`aggregateAlignBytes = 4`) causes `rustc_abi::layout::univariant_biased`
  (`compiler/rustc_abi/src/layout.rs:1106-1114`) to raise the alignment and size
  of **all** aggregates—even `#[repr(transparent)]` wrappers—to at least 4 bytes.

In [`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean)
(lines 2672–2871), we prove:
1. **`reprC_withU64_padding_depends_on_target_i64_align`**:
   For `#[repr(C)] pub struct WithU64 { pub a: u32, pub b: u64 }`:
   - When `i64AlignBytes = 4` (`i686-unknown-linux-gnu`),
     `reprCForwardLayoutWithI64Align 4 withU64Decl` yields
     `size = 12, align = 4, fieldOffsets = [0, 4], hasUninitPadding = false`.
   - When `i64AlignBytes = 8` (`x86_64-unknown-linux-gnu`),
     `reprCForwardLayoutWithI64Align 8 withU64Decl` yields
     `size = 16, align = 8, fieldOffsets = [0, 8], hasUninitPadding = true`
     (4 bytes of inter-field padding at offsets `4..8`).
   - Consequently, across **every** valid target `i64AlignBytes ∈ {4, 8}`,
     `transmute_copy::<WithU64, [u8; 16]>` steps to `StepResult.err`—from size
     mismatch (`12 ≠ 16`) on `i686` and from reading uninitialized padding bytes
     at `4..8` into `[u8; 16]` on `x86_64`.
2. **`custom_target_aggregate_align_gt_one_violates_transparent_law`**:
   When `aggregateAlignBytes = 4`, `univariantBiasedLayout 4 1 1` inflates
   `#[repr(transparent)] pub struct TransU8(pub u8)` to
   `size = 4, align = 4, hasUninitPadding = true`, which **violates**
   `ReferenceAdmissible crateTransU8 .any` (`r[layout.repr.transparent]`),
   whereas every target satisfying `ValidTargetSpec` (`aggregateAlignBytes = 1`)
   satisfies `ReferenceAdmissible`.

#### 5.3 In-Memory `transmute_copy` vs. `extern "C" fn` ABI Discrimination (`in_memory_transmute_vs_extern_c_fn_abi_discrimination`)

While `#[repr(C)] pub struct ReprCWrapper(pub u64)` and
`#[repr(transparent)] pub struct ReprTransparentWrapper(pub u64)` have identical
in-memory layouts (`size = 8, align = i64Align, hasUninitPadding = false`), they
differ in `extern "C" fn` calling conventions:
- Under `r[layout.repr.transparent.layout-abi]` (`type-layout.html:573-577`),
  `#[repr(transparent)]` guarantees that the wrapper is passed and returned with
  the **exact same calling-convention `PassMode`** as its single non-ZST field.
- By contrast, `#[repr(C)]` sets `ReprFlags::ABI_UNOPTIMIZABLE` in `rustc`
  (`compiler/rustc_abi/src/lib.rs:103-105`), which on `i686-unknown-linux-gnu`
  (`compiler/rustc_target/src/callconv/x86.rs`) and `x86_64-pc-windows-msvc`
  causes `extern "C" fn() -> ReprCWrapper` to return indirectly via a hidden
  stack pointer (`PassMode::Indirect { on_stack: true }` / `sret`), whereas
  `extern "C" fn() -> u64` and `extern "C" fn() -> ReprTransparentWrapper`
  return directly in registers (`edx:eax` or `rax`).

In **`in_memory_transmute_vs_extern_c_fn_abi_discrimination`**
(`support/ForwardCompatibleMirSemantics.lean:2968-2999`), we prove that:
1. Across **all** `ReferenceAdmissible` environments `env` and **all**
   `CallAbiAdmissible` realizations `callAbi`, in-memory `transmute_copy`
   succeeds for both `ReprTransparentWrapper(u64)` and `ReprCWrapper(u64)`, AND
   `extern "C" fn() -> u64` $\to$ `extern "C" fn() -> ReprTransparentWrapper`
   ABI transmutation succeeds.
2. Under the valid `i686-unknown-linux-gnu` calling-convention realization
   `callAbi_i686_sysv` (`CallAbiAdmissible testCrate callAbi_i686_sysv`),
   `extern "C" fn() -> u64` $\to$ `extern "C" fn() -> ReprCWrapper` steps to
   `StepResult.err` (`.failed`).

#### 5.4 `UbChecks` + `panic_nounwind_fmt` Dual Soundness Trap and Repair (`ub_checks_dual_soundness_trap_and_repair`)

In `core` (`library/core/src/ub_checks.rs`), functions with language or library
UB preconditions—such as `hint::unreachable_unchecked`, `slice::get_unchecked`,
`ptr::read`, and `str::from_utf8_unchecked`—expand
`assert_unsafe_precondition!(check_language_ub / check_library_ub, cond)` into
`Runtime(PostCleanup)` MIR:

```text
_ub = UbChecks();
switchInt(_ub) -> [true: bb_check, false: bb_cont];
bb_check:
  switchInt(cond) -> [true: bb_cont, false: bb_fail];
bb_fail:
  core::panicking::panic_nounwind_fmt(...) -> unreachable;
bb_cont:
  // continuation (e.g., raw pointer/slice cast in from_utf8_unchecked)
```

Because `PrefixOutcome.isSafe` (`support/ForwardCompatibleMirSemantics.lean:255-260`)
defines `isSafe (.terminated .unwind) = True` so that normal unwinding panics do
not count as UB under `Language.WellFormed` (`safeUnwindOrNormalSpec`), we prove
in **`ub_checks_dual_soundness_trap_and_repair`**
(`support/ForwardCompatibleMirSemantics.lean:3106-3171`):
1. **Trap 1 (`UbChecks = true`, `panic_nounwind_fmt ↦ .terminated .unwind`)**:
   Satisfies `(LangUbBrokenUnwind false retVal).sem () ≤ safeUnwindOrNormalSpec _`
   even when `cond = false`, falsely certifying UB code as safe because `.unwind`
   has `isSafe = True`.
2. **Trap 2 (`UbChecks = false`, skipping `precondition_check`)**:
   Satisfies `(LangUbBrokenSkip false retVal).sem () ≤ safeUnwindOrNormalSpec _`
   even when `cond = false`, falsely certifying library-UB code (such as
   `str::from_utf8_unchecked` on invalid UTF-8, whose continuation body is a raw
   pointer/slice cast) as safe.
3. **Sound Repair (`UbChecks = true`, `panic_nounwind_fmt ↦ StepResult.failed`)**:
   Satisfies
   $$\bigl((\mathsf{LangUbSoundFailed}\;\mathit{cond}\;\mathit{retVal}).\mathsf{sem}\;() \;\le\; \mathsf{safeUnwindOrNormalSpec}\bigr) \;\Longleftrightarrow\; \mathit{cond} = \mathsf{true}$$
   certifying the operation if and only if the safety precondition `cond` holds.

---

### 6. Complete List of Kernel-Checked Lean 4 Theorems and Axiom Footprint

Basis: execution, derived

All 39 theorems in
[`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean)
compile cleanly under Lean `v4.34.1` (`commit 5045d0056413266e57c625dcd7c365b10e377c52`)
with `-DElab.async=false -Ddebug.skipKernelTC=false`, zero `sorryAx`, and zero
`Lean.ofReduceBool`:

1. `StepResult.no_step_of_err`
2. `StepResult.no_step_of_ret`
3. `model1_unsoundly_accepts_repr_rust_transmute` (**Theorem 1a**)
4. `model1_multi_field_repr_rust_size_zero_bug` (**Theorem 1b**)
5. `model2_rejects_repr_rust_transmute_u64` (**Theorem 2a**)
6. `model2_falsely_rejects_reflexive_and_polymorphic_ops` (**Theorem 2b**)
7. `list_all_iff_forall`
8. `checkReferenceAdmissible_iff`
9. `checkReferenceAdmissible_sound`
10. `env_8_admissible`
11. `env_16_admissible`
12. `env_ptr16_admissible_any`
13. `env_ptr32_admissible_any`
14. `env_8_admissible_ptr64`
15. `env_lazy_dead_const_admissible`
16. `sem_forwardCompatible_choice_iff_query`
17. `evalOpInEnv_transmuteCopy_u64_reprRust_env8`
18. `evalOpInEnv_transmuteCopy_u64_reprRust_env16`
19. `model3_rejects_repr_rust_u64_transmute` (**Model 3 Theorem 1**)
20. `reprTransparentWrapper_layout_in_all_admissible`
21. `reprCWrapper_layout_in_all_admissible`
22. `model3_accepts_repr_transparent_and_padding_free_repr_c_transmute` (**Model 3 Theorem 2**)
23. `reprRustWrapper_pos_size_in_all_admissible`
24. `model3_accepts_reflexive_repr_rust_transmute_and_copy` (**Model 3 Theorem 3**)
25. `usize_bounds_in_all_admissible_any`
26. `usize_eq_8_in_all_admissible_ptr64`
27. `model3_target_parametric_vs_cfg_gated_usize` (**Model 3 Theorem 4**)
28. `model3_refinement_bridge_and_tcb_stratification` (**Model 3 Theorem 5a**)
29. `model3_dead_branch_required_consts_discrimination` (**Model 3 Theorem 5b**)
30. `checkReferenceAdmissibleWithZstLaw_sound`
31. `env_8_zst_admissible`
32. `env_16_zst_admissible`
33. `repr_rust_zst_vs_non_zst_discrimination` (**Extension Theorem A**)
34. `reprC_withU64_padding_depends_on_target_i64_align` (**Extension Theorem B.1**)
35. `custom_target_aggregate_align_gt_one_violates_transparent_law` (**Extension Theorem B.2**)
36. `repr_c_target_u64_alignment_and_aggregate_align_boundary` (**Extension Theorem B**)
37. `callAbi_i686_sysv_admissible`
38. `in_memory_transmute_vs_extern_c_fn_abi_discrimination` (**Extension Theorem C**)
39. `ub_checks_dual_soundness_trap_and_repair` (**Extension Theorem D**)

Exact `#print axioms` output from the Lean 4.34.1 kernel:

```text
'ForwardCompatibleMirSemantics.model1_unsoundly_accepts_repr_rust_transmute' depends on axioms: [propext]
'ForwardCompatibleMirSemantics.model1_multi_field_repr_rust_size_zero_bug' depends on axioms: [propext]
'ForwardCompatibleMirSemantics.model2_rejects_repr_rust_transmute_u64' depends on axioms: [propext]
'ForwardCompatibleMirSemantics.model2_falsely_rejects_reflexive_and_polymorphic_ops' depends on axioms: [propext]
'ForwardCompatibleMirSemantics.checkReferenceAdmissible_iff' depends on axioms: [propext, Quot.sound]
'ForwardCompatibleMirSemantics.checkReferenceAdmissible_sound' depends on axioms: [propext, Quot.sound]
'ForwardCompatibleMirSemantics.sem_forwardCompatible_choice_iff_query' depends on axioms: [propext, Quot.sound]
'ForwardCompatibleMirSemantics.model3_rejects_repr_rust_u64_transmute' depends on axioms: [propext, Quot.sound]
'ForwardCompatibleMirSemantics.model3_accepts_repr_transparent_and_padding_free_repr_c_transmute' depends on axioms: [propext,
 Quot.sound]
'ForwardCompatibleMirSemantics.model3_accepts_reflexive_repr_rust_transmute_and_copy' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'ForwardCompatibleMirSemantics.model3_target_parametric_vs_cfg_gated_usize' depends on axioms: [propext, Quot.sound]
'ForwardCompatibleMirSemantics.model3_refinement_bridge_and_tcb_stratification' depends on axioms: [propext, Quot.sound]
'ForwardCompatibleMirSemantics.model3_dead_branch_required_consts_discrimination' depends on axioms: [propext,
 Quot.sound]
'ForwardCompatibleMirSemantics.repr_rust_zst_vs_non_zst_discrimination' depends on axioms: [propext, Quot.sound]
'ForwardCompatibleMirSemantics.reprC_withU64_padding_depends_on_target_i64_align' depends on axioms: [propext]
'ForwardCompatibleMirSemantics.custom_target_aggregate_align_gt_one_violates_transparent_law' depends on axioms: [propext,
 Quot.sound]
'ForwardCompatibleMirSemantics.repr_c_target_u64_alignment_and_aggregate_align_boundary' depends on axioms: [propext,
 Quot.sound]
'ForwardCompatibleMirSemantics.in_memory_transmute_vs_extern_c_fn_abi_discrimination' depends on axioms: [propext,
 Quot.sound]
'ForwardCompatibleMirSemantics.ub_checks_dual_soundness_trap_and_repair' does not depend on any axioms
```

## Boundaries

- **Scope of the Lean 4 mechanization**:
  [`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean)
  mechanizes a self-contained `Preorder` / `Partial` / `Behavior` / `Language` /
  `StepResult` / `SmallStepMachine` refinement spine and a self-contained core
  of `MirTy`, `MirVal`, `AdtDecl`, `ReprAttr`, `CompilerRealization`,
  `ReferenceAdmissible`, `transmute_copy`, `copy_nonoverlapping`, `size_of`,
  `usize` checked arithmetic, `RequiresConst`, `extern "C" fn` ABI
  transmutation, and `UbChecks` + `panic_nounwind_fmt`. It does not model
  raw-pointer provenance/aliasing graphs, multi-byte endian-split scalar
  transmutations (`u32 <-> [u8; 4]`), or floating-point NaN payloads.
- **Target specifications**:
  Target alignment results (`i64AlignBytes ∈ {4, 8}` and
  `aggregateAlignBytes = 1`) apply to built-in `rustc_target` specifications in
  `rustc 1.98.0-nightly (f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1)`. Custom
  target JSON specs that set `aggregateAlignBytes > 1` (`-a:32`) violate
  `ValidTargetSpec` and `r[layout.repr.transparent]`, as proved in
  `custom_target_aggregate_align_gt_one_violates_transparent_law`.

## Evidence

- **Rust Reference (`rust-lang/reference` at `82da570bafd9efed421bdbae0f8603ede8dd308b`)**:
  - `src/type-layout.md` (`r[layout.primitive.size-align]`, `r[layout.tuple.def]`,
    `r[layout.tuple.unit]`, `r[layout.option-niche]`, `r[layout.repr.rust.unspecified]`,
    `r[layout.repr.rust.struct-zst]`, `r[layout.repr.c.struct]`,
    `r[layout.repr.transparent.layout-abi]`)
  - `src/types/numeric.md` (`r[type.numeric.int.size]`, `r[type.numeric.int.size.usize]`,
    `r[type.numeric.int.two-complement]`)
  - `src/types/boolean.md` (`r[type.bool.layout]`)
  - `src/expressions/block-expr.md` (`r[expr.block.const.evaluation]`,
    `r[expr.block.const.not-executed]`)
  - `src/behavior-considered-undefined.md` (`r[undefined.validity.scalar]`,
    `r[undefined.pointer-access]`, `r[undefined.call-abi]`)
- **Rust compiler and standard library (`rust-lang/rust` at `f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`)**:
  - `compiler/rustc_abi/src/lib.rs:98-105, 219-227`
  - `compiler/rustc_abi/src/layout.rs:1106-1140, 1254-1320`
  - `compiler/rustc_middle/src/ty/mod.rs:1506-1604`
  - `compiler/rustc_ty_utils/src/layout.rs:207-211, 571-576`
  - `compiler/rustc_mir_transform/src/required_consts.rs:14-48`
  - `compiler/rustc_mir_transform/src/lib.rs:514-579`
  - `compiler/rustc_monomorphize/src/collector.rs:1349-1362`
  - `library/core/src/ub_checks.rs`
- **Zerocopy (`google/zerocopy` at `8fb35253fbc703cb2cd0997f4efcda76cf9062b6`)**:
  - `POLICIES.md:31-49`
- **Preserved Support Artifacts**:
  - [`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean):
    Standalone Lean 4 (`v4.34.1`) mechanization (3,197 lines, 39 theorems, 19
    `#print axioms` checks, zero `sorryAx`, zero `Lean.ofReduceBool`).
  - [`support/randomize_layout_probe.rs`](support/randomize_layout_probe.rs) and
    [`support/randomize_layout_probe.jsonl`](support/randomize_layout_probe.jsonl):
    Empirical `-Z randomize-layout` probe source and JSONL measurements across
    unrandomized compilation and `-Z layout-seed=0..15` on `rustc 1.98.0-nightly (f8a08b688)`.

## Revalidation

To re-verify the standalone Lean 4 mechanization in
[`support/ForwardCompatibleMirSemantics.lean`](support/ForwardCompatibleMirSemantics.lean)
with full kernel typechecking enabled and confirm zero `sorryAx` and zero
`Lean.ofReduceBool`:

```bash
anneal-lean-run --mode file --concurrency 2 -- \
  ~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -DElab.async=false -Ddebug.skipKernelTC=false \
  reports/anneal-forward-compatible-mir-semantics-and-reference-admissible-refinement/support/ForwardCompatibleMirSemantics.lean
```

To re-run the `-Z randomize-layout` empirical probe on `rustc 1.98.0-nightly (f8a08b688 2026-05-30)`:

```bash
rustc +nightly-2026-05-30 -O \
  reports/anneal-forward-compatible-mir-semantics-and-reference-admissible-refinement/support/randomize_layout_probe.rs \
  -o /tmp/probe_default && /tmp/probe_default default
for seed in $(seq 0 15); do
  rustc +nightly-2026-05-30 -O -Z randomize-layout -Z layout-seed=$seed \
    reports/anneal-forward-compatible-mir-semantics-and-reference-admissible-refinement/support/randomize_layout_probe.rs \
    -o /tmp/probe_$seed && /tmp/probe_$seed $seed
done
```
