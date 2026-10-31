<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Exhaustive `rustc` Obligation Inventory and Single-Source x86-64 Codegen

## Summary

Sound whole-crate verification in Anneal requires two compiler-boundary
invariants:

1. **Exhaustive typed obligation inventory:** `anneal-rustc-capture` must
   discover 100% of soundness-bearing crate items and metadata from `rustc`'s
   typed query graph (`TyCtxt`) so that no verification obligation in
   `Mir.crate : Trusted.Crate` can be omitted or spoofed by surface syntax.
2. **Single-source artifact binding:** When Anneal lowers MIR to x86-64
   assembly, the assembly file `.anneal/Prog.s` assembled into the binary must
   be mathematically bound to the exact `X86Body` abstract syntax trees
   verified by `Proof.verify_crate` inside the Lean 4 kernel.

Direct source inspection and executable probes across Anneal's MIR semantic
verification baseline (`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and
MIR-to-x86-64 codegen pipeline (`4f45f0a391a921ced9c9dc773b9a040dbc215d14`)
establish four core results:

1. **Textual source and `--emit=mir` scraping omits and spoofs crate
   obligations:** `capture_crate_with_options` reads only `src/lib.rs`, scans
   raw source lines via `parse_source_metadata`, and parses human-facing
   `--emit=mir` text via `parse_emitted_mir_with_metadata`. This pipeline
   hardcodes a single struct name (`NonZeroUsize`), allows comments or string
   literals to spoof field privacy and `pub unsafe fn` preconditions, never
   emits `unsafeImpls` (`Mir.crate.unsafeImpls` is unconditionally `[]`),
   collapses all constant bodies to a single hardcoded identifier
   (`pme_assert_const`), and omits submodule files, `#[unsafe]` fields,
   `#[non_exhaustive]` ADTs, inherited trait default methods,
   compiler-synthesized drop glue (`ShimKind::DropGlue`), and dead-branch
   `mentioned_items`.
2. **An in-process `rustc_driver` `TyCtxt` inventory closes all five obligation
   categories without text parsing:** A standalone `rustc_driver` probe
   (`support/obligation_inventory_probe/`) executed against `rustc 1.99.1`
   (`58cf8f9c35b355199727627d07ae34a4e2846d67`) demonstrates the exact `TyCtxt`
   queries required to enumerate every trait `impl` header and polarity, ADT
   field visibility/safety and `#[non_exhaustive]` flag, inherited trait
   default method instance, explicit destructor and `ShimKind::DropGlue` body,
   and `Runtime(PostCleanup)` MIR body across `mir_for_ctfe`,
   `mir_drops_elaborated_and_const_checked`, `required_consts`, and
   `mentioned_items`.
3. **Dual Rust emitters in the MIR-to-x86-64 pipeline leave `.anneal/Prog.s`
   unbound to the Lean kernel and diverge on four constructs:** In
   `4f45f0a391a921ced9c9dc773b9a040dbc215d14`, `anneal-rustc-capture` lowers
   MIR to x86-64 in Rust and runs two independent printers:
   `render_mir_lean_with_metadata` (writing `Trusted.X86Body` terms to
   `.anneal/Mir.lean`) and `render_x86_assembly` (writing
   `.intel_syntax noprefix` text to `.anneal/Prog.s`). Neither `anneal-audit`
   nor `TrustedBoundary.lean` ever reads or hashes `.anneal/Prog.s`. Four
   semantic discrepancies already exist between `Mir.lean`
   (`X86Semantics.lean`) and `Prog.s` (`render_x86_assembly`), including
   `CapturedTerminator::Panic` emitting a safe unwind terminator (`abortPanic`)
   in `Mir.lean` while emitting `ud2` (hardware `SIGILL` undefined behavior) in
   `Prog.s`.
4. **In-Lean deterministic `.s` serialization with `.olean` environment binding
   eliminates the shadow-artifact gap:** A mechanized Lean 4 (`v4.34.1`) and
   x86-64 prototype (`support/artifact_binding_probe/`) demonstrates a
   single-source pipeline where `Mir.crate` contains only `MirBody`,
   `Prog.x86Crate` is computed inside Lean via `compileStage0` and
   `optimizePeephole`, `Trusted.emitX86CrateAsm` is the sole assembly printer,
   `Trusted.CrateTheorem` checks `Trusted.emitX86CrateAsm xc = asmText` by
   kernel `rfl`, and `AuditMain.lean` verifies that `Prog.asmText` in the
   replayed `.olean` environment matches `Prog.s` on disk byte-for-byte.

## Applicability

The findings in this report apply to the interaction of four concrete subjects:

- **`joshlf/anneal` at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`** (MIR
  semantic verification baseline): specifically
  `trusted/rustc-capture/src/lib.rs`, `trusted/rustc-capture/src/proof_gen.rs`,
  and `trusted/lean/Trusted/MirSemantics.lean`.
- **`joshlf/anneal` at `4f45f0a391a921ced9c9dc773b9a040dbc215d14`**
  (MIR-to-x86-64 codegen pipeline): specifically
  `trusted/rustc-capture/src/lib.rs`, `trusted/rustc-capture/src/proof_gen.rs`,
  `trusted/lean/Trusted/X86Semantics.lean`,
  `theory/Anneal/Compiler/NaiveCodegen.lean`,
  `theory/Anneal/Compiler/Peephole.lean`, and
  `trusted/audit/TrustedBoundary.lean`.
- **`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`** (`rustc
  1.99.1`, `x86_64-unknown-linux-gnu`), invoked with `RUSTC_BOOTSTRAP=1` and
  the `rustc-dev` and `rustc-src` toolchain components to access
  `rustc_private` internal query APIs (`rustc_driver`, `rustc_hir`,
  `rustc_interface`, `rustc_middle`).
- **`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`** (Lean 4
  `v4.34.1`, `x86_64-unknown-linux-gnu`), invoked with `-DElab.async=false` and
  `-Ddebug.skipKernelTC=false`.

The `rustc_middle::ty` and `rustc_mir_transform` query signatures documented in
Section 2 are internal compiler APIs with no stability guarantee across `rustc`
releases; exact method names and return wrappers (such as `clauses_of`,
`impl_trait_header`, and `Instance::resolve_drop_glue`) apply specifically to
`58cf8f9c35b355199727627d07ae34a4e2846d67`. The kernel reduction costs for
`String` equality in Section 4 apply to Lean 4 `v4.34.1`, where `String` is
backed by `ByteArray` (`Array UInt8` / `List UInt8`).

## Findings

### 1. Omission and Spoofing Vulnerabilities in `trusted/rustc-capture`

`Basis: source + derived`

In both `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`
(`trusted/rustc-capture/src/lib.rs:399-550`) and
`4f45f0a391a921ced9c9dc773b9a040dbc215d14`
(`trusted/rustc-capture/src/lib.rs:577-795`), `capture_crate_with_options`
reads a single source file (`src/lib.rs`), runs `parse_source_metadata` over
raw lines (`src.lines()`), invokes `rustc --emit=mir=crate.mir`, and parses the
textual MIR dump via `parse_emitted_mir_with_metadata`. This architecture has
six distinct soundness vulnerabilities:

1. **Single-file and hardcoded-identifier ADT discovery (`lib.rs:408`,
   `517-531`, `850-863`, `1296-1312` in `e6a0b2da5ec3`):**
   `capture_crate_with_options` reads only `crate_dir.join("src/lib.rs")`; any
   item declared in a submodule file (`mod sub;`) is unseen by
   `parse_source_metadata`. Even within `src/lib.rs`, `parse_source_metadata`
   only checks `line.contains("struct NonZeroUsize")`. Every other `struct`,
   `enum`, or `union` in the crate is omitted from `Mir.crate.adts`.
2. **Line-scanner spoofing of `allFieldsPubSafe` and `FieldAccess`
   (`lib.rs:517-531` in `e6a0b2da5ec3`; `lib.rs:762-776` in `4f45f0a391a9`):**
   Once `"struct NonZeroUsize"` is seen, `parse_source_metadata` executes:
   ```rust
   } else if nonzero_field_pub_safe.is_some() {
       if line.starts_with("pub val: usize") {
           nonzero_field_pub_safe = Some(true);
       } else if line.starts_with("val: usize") {
           nonzero_field_pub_safe = Some(false);
       }
   }
   ```
   Because `nonzero_field_pub_safe.is_some()` remains `true` for the remainder
   of `src/lib.rs`, a struct with a public field (`pub val: usize`) followed
   anywhere later in the file by a raw string literal or multi-line comment
   containing a line starting with `val: usize` overwrites
   `nonzero_field_pub_safe` back to `Some(false)` (`FieldAccess.priv`). Even
   without a comment, formatting `pub\n val: usize` across two lines or using a
   tuple struct `pub struct NonZeroUsize(pub usize);` leaves
   `allFieldsPubSafe := false` in `Mir.crate`. In
   `Trusted/MirSemantics.lean:778-785`, `AdmissibleAdtInv` only constrains
   `allFieldsPubSafe = true` types to `TrivialValInv`; setting
   `allFieldsPubSafe := false` on a publicly constructible struct allows the
   crate to attach a non-trivial library invariant `I_lib(v) := v != 0` that
   safe external callers can violate by constructing `NonZeroUsize { val: 0 }`
   directly. Conversely, `#[unsafe]` fields (RFC 3458) and `#[non_exhaustive]`
   attributes are ignored.
3. **Spoofing and omission of `FnKind` (`pubSafe`, `pubUnsafe`, `priv`)
   (`lib.rs:532-542`, `701-705`, `1274-1287` in `e6a0b2da5ec3`):**
   `parse_source_metadata` populates `meta.unsafe_fns` solely via
   `line.strip_prefix("pub unsafe fn ")`.
   - **False-positive `pubUnsafe` spoofing:** Placing `\npub unsafe fn foo(`
     inside a block comment `/* ... */` or raw string literal `r#"..."#`
     inserts `"foo"` into `meta.unsafe_fns`. When `foo` is actually a safe
     `pub fn foo(x: usize)`, `render_mir_lean_with_metadata` emits
     `FnKind.pubUnsafe True newUncheckedSafetyPre`, granting a safe public
     function an unchecked caller precondition (`x != 0`) and discharging its
     verification obligation under a false assumption.
   - **False-negative `pubSafe` and missing `priv` classification:** A public
     unsafe function written as `pub const unsafe fn`,
     `pub unsafe extern "C" fn`, or across two lines (`pub unsafe\nfn`) fails
     `strip_prefix("pub unsafe fn ")` and is emitted as
     `CapturedFnKind::PubSafe`. Moreover, `CapturedFnKind` has no `Priv`
     variant (`Trusted.FnKind.priv` exists in `MirSemantics.lean:769`, but
     `rustc-capture` only models `PubSafe` and `PubUnsafeNewUnchecked`), and
     `parse_fn_header` (`lib.rs:753-760`) strips all module and impl prefixes
     via `raw_name.rsplit("::").next()`, colliding functions that share a
     basename across modules or `impl` blocks.
4. **Total omission of `unsafeImpls` (`Trusted.UnsafeImplObligation`)
   (`MirSemantics.lean:826-838`, `X86Semantics.lean:855-867`):**
   Although `Trusted.Crate` defines
   `unsafeImpls : List UnsafeImplObligation := []` and `CrateTheorem` requires
   `AllHold (c.unsafeImpls.map ...)`, `render_mir_lean_with_metadata` in
   `trusted/rustc-capture/src/lib.rs` (`e6a0b2da5ec3:1296-1312` and
   `4f45f0a391a9:1532-1548`) never emits the `unsafeImpls` field. Consequently,
   `Mir.crate.unsafeImpls` defaults to `[]` for every crate, and every
   `unsafe impl Send`, `unsafe impl Sync`, or user-defined `unsafe trait`
   implementation is unverified.
5. **Constant/static collision and missing `mentioned_items` (`lib.rs:456-460`,
   `591-595`, `1062-1071` in `e6a0b2da5ec3`):**
   `parse_emitted_mir_with_metadata` only recognizes top-level MIR headers
   matching `line.starts_with("const ")` or `line.contains("::{constant#")`
   combined with `line.ends_with(": () = {")`, and renames every matched
   constant to the single hardcoded identifier `"pme_assert_const"`. Any
   non-`()` constant or `static` initializer is rejected (`unsupported function
   header`), two `()` constants in the same crate produce duplicate Lean
   declarations (`Mir.pme_assert_const_body`), and `requiredConsts` is
   populated only by matching statement text against `::ASSERT` or
   `::{constant#`. Calls in dead branches (`if false { f::<0>(); }`) whose
   post-monomorphization error (PME) obligations are tracked via
   `Body::mentioned_items` are omitted when `SimplifyCfg` removes the branch.
6. **Invisibility of inherited trait default methods and compiler shims:**
   When a crate implements a trait (`impl SafeTrait for LocalAdt {}` or
   `impl Clone for LocalAdt { fn clone(&self) -> Self { ... } }`) without
   overriding a default method (`SafeTrait::default_mutate` or
   `Clone::clone_from`), `--emit=mir` emits no MIR body for the inherited
   method specialization on `LocalAdt`. Likewise, compiler-synthesized drop
   glue (`ShimKind::DropGlue`) for a struct containing droppable fields has no
   entry in `tcx.mir_keys(())` or `--emit=mir`.

### 2. Exhaustive Crate Obligation Inventory via `rustc_driver` `TyCtxt` Queries

`Basis: source + execution`

Replacing the subprocess `--emit=mir` invocation with an in-process
`rustc_driver::Callbacks::after_analysis` pass provides direct access to
`TyCtxt` after type checking, borrow checking, privacy analysis, and drop
elaboration have succeeded (`compiler/rustc_interface/src/passes.rs:1154-1282`).
The standalone probe in `support/obligation_inventory_probe/` verifies the
exact `rustc 1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) query recipes
and required guards across all five obligation categories:

| Category | Soundness-Bearing Obligation | Exact `rustc 1.99.1` (`58cf8f9c3`) `TyCtxt` Query Recipe | Empirical Pitfalls & Required Guards |
| :--- | :--- | :--- | :--- |
| **(a) `unsafe impl` & Polarities** | Every local trait `impl` (`unsafe impl`, safe `impl`, negative `impl !Trait`) and its `where`-clauses | Iterate `tcx.hir_crate_items(()).definitions()` where `tcx.def_kind(def_id) == DefKind::Impl { of_trait: true }`. Query `let header = tcx.impl_trait_header(def_id);` (`ty::ImplTraitHeader` at `rustc_middle/src/ty/mod.rs:299-304`) for `header.safety` (`hir::Safety::Unsafe` vs `Safe`), `header.polarity` (`ImplPolarity::Positive`, `Negative`, `Reservation`), `let trait_ref = header.trait_ref.skip_binder();`, `tcx.trait_def(trait_ref.def_id).safety`, and `tcx.clauses_of(def_id).clauses` (`rustc_middle/src/ty/generics.rs:386-389`). | In `rustc 1.99.1`, `header.trait_ref.instantiate_identity()` returns `Unnormalized<'tcx, TraitRef<'tcx>>`; use `header.trait_ref.skip_binder()` (or `.instantiate_identity().skip_norm_wip()`) to access `.def_id`, `.self_ty()`, and `.args`. Also, `tcx.predicates_of` was replaced by `tcx.clauses_of(def_id)`. Negative impls (`impl !Sync for RawPtrBox`) have `header.polarity == ImplPolarity::Negative` and no associated methods. |
| **(b) ADTs, Field Visibilities, `#[non_exhaustive]`, `#[unsafe]`** | Every `Struct`, `Enum`, and `Union`; per-field `Trusted.FieldAccess` (`pubSafe`, `priv`, `unsafeField`); `allFieldsPubSafe` | Filter `tcx.hir_crate_items(()).definitions()` for `DefKind::Struct \| DefKind::Enum \| DefKind::Union`. Query `let adt_def = tcx.adt_def(def_id);`, `let eff_vis = tcx.effective_visibilities(());`, `adt_def.adt_kind()`, `adt_def.repr()`, and `let is_non_exhaustive = adt_def.is_variant_list_non_exhaustive() \|\| adt_def.variants().iter().any(\|v\| v.is_field_list_non_exhaustive());`. For each `field` in `variant.fields`, inspect `field.safety` (`Safety::Unsafe` vs `Safe`) and `eff_vis.is_reachable(field.did.expect_local())`. | **Syntactic `vis.is_public()` vs. effective reachability:** In `mod inner_private { pub struct UnreachableAllPub { pub x: usize } }`, `field.vis.is_public()` is `true`, whereas `eff_vis.is_reachable(...)` is `false` because `inner_private` is unexported (`output.txt:41-43`). Conversely, for a reachable struct, `allFieldsPubSafe` is `true` iff `adt_def.is_struct() && !is_non_exhaustive && adt_eff_reachable && variants[0].fields.iter().all(\|f\| f.safety == Safety::Safe && eff_vis.is_reachable(f.did.expect_local()))`. Unions (`adt_def.is_union()`) have unsafe field reads in Rust even when all fields are `pub` (`output.txt:44-47`), so `allFieldsPubSafe` must be `false` for unions unless modeled separately. |
| **(c) Trait Default Methods & Safe Trait Impls** | Overridden and inherited default methods on every positive local trait `impl` (including foreign traits such as `core::clone::Clone`) | For each positive `DefKind::Impl { of_trait: true }`, obtain `let trait_ref = header.trait_ref.skip_binder();`, `let impl_map = tcx.impl_item_implementor_ids(impl_def_id);`, and `let typing_env = ty::TypingEnv::non_body_analysis(tcx, impl_def_id);`. Iterate `tcx.associated_items(trait_ref.def_id).in_definition_order().filter(\|it\| it.is_fn())` and resolve each method via `ty::Instance::try_resolve(tcx, typing_env, assoc_item.def_id, trait_ref.args)` (`rustc_middle/src/ty/instance.rs:562-601`). Fetch the body via `tcx.instance_mir(inst.def)`. | When an impl omits a default method (`SafeMutatorTrait::default_zero_out` or `core::clone::Clone::clone_from` on `EncapsulatedNonZero`), `impl_map.get(&assoc_item.def_id)` is `None`, and the specialized method does **not** appear in `tcx.mir_keys(())`. However, `Instance::try_resolve` resolves it to `Instance { def: Item(default_fn_did), args: [EncapsulatedNonZero, ...] }` (`output.txt:72, 76`), allowing `anneal-rustc-capture` to instantiate and verify the default method against `EncapsulatedNonZero`'s `AdmissibleAdtInv`. |
| **(d) `Drop::drop`, Drop Glue, & Shims** | Explicit `Drop::drop` impls, synthesized `ShimKind::DropGlue`, `ShimKind::ClosureOnce`, `ShimKind::Reify`, `ShimKind::VTable`, `ShimKind::Clone` | For each ADT, query `adt_def.destructor(tcx)` for explicit `Drop::drop`. For non-polymorphic ADTs (`!tcx.generics_of(def_id).requires_monomorphization(tcx)`), construct `let adt_ty = Ty::new_adt(tcx, adt_def, GenericArgs::identity_for_item(tcx, def_id));` and call `ty::Instance::resolve_drop_glue(tcx, adt_ty)` (`instance.rs:789-799`), then `tcx.instance_mir(drop_inst.def)`. For closures (`DefKind::Closure`), extract `let ty::TyKind::Closure(_, closure_args) = *tcx.type_of(def_id).skip_binder().kind()` and call `ty::Instance::fn_once_adapter_instance(tcx, def_id, closure_args)` (`instance.rs:823-851`). | 1. In `rustc 1.99.1`, `InstanceKind::Shim(ty::ShimKind::...)` wraps `ShimKind`, and `resolve_drop_in_place` was renamed to `Instance::resolve_drop_glue(tcx, ty)` (`instance.rs:789`).<br>2. For `OuterWithDropGlue`, `adt_def.destructor(tcx)` is `None`, yet `Instance::resolve_drop_glue` returns `Shim(DropGlue(core::ptr::drop_glue, Some(OuterWithDropGlue)))` (`bbs=2`, `output.txt:95`).<br>3. Calling `Instance::fn_once_adapter_instance` with `GenericArgs::identity_for_item(tcx, closure_did)` **panics** (`closure_sig_as_fn_ptr_ty is not a fn-ptr: /#1`) because closure identity args contain synthetic `ParamTy` placeholders; extract `closure_args` from `tcx.type_of(def_id).skip_binder().kind()`. |
| **(e) `static`, `const`, `required_consts`, & `mentioned_items`** | Every MIR body in `tcx.mir_keys(())`, CTFE initializers, inline `const { ... }` blocks, and PME obligations in dead branches | Iterate `tcx.mir_keys(())` (`rustc_mir_transform/src/lib.rs:327-358`). First check `if tcx.is_trivial_const(local_def_id)` and use `tcx.trivial_const(local_def_id)`. Otherwise: for `DefKind::Const { .. } \| DefKind::AssocConst { .. } \| DefKind::Static { .. } \| DefKind::AnonConst`, query `tcx.mir_for_ctfe(def_id)` (`phase == Runtime(PostCleanup)`). For `DefKind::Fn \| DefKind::AssocFn \| DefKind::Closure`, borrow `tcx.mir_drops_elaborated_and_const_checked(local_def_id)` **before** calling `tcx.optimized_mir(def_id)` to obtain the exact `Runtime(PostCleanup)` body, and then read `tcx.optimized_mir(def_id).mentioned_items`. | 1. **Trivial const guard:** Calling `tcx.mir_for_ctfe(def_id)` on a trivial constant (`pub const TRIVIAL_CONST: usize = 99;`) trips `debug_assert!(!tcx.is_trivial_const(def_id))` (`rustc_mir_transform/src/lib.rs:493`). Always check `tcx.is_trivial_const(local_def_id)` first (`output.txt:115, 122`).<br>2. **`mentioned_items` panic guard:** `MentionedItems` runs only inside `inner_optimized_mir` (`rustc_mir_transform/src/lib.rs:810`). Calling `body.mentioned_items()` on `mir_for_ctfe` (for any `Const`, `AssocConst`, `Static`, or `AnonConst`) **panics** (`mentioned_items for DefId(...) have not yet been set`). Read `body.required_consts.as_deref()` and `body.mentioned_items.as_deref()` as `Option`s.<br>3. **Steal ordering for `Runtime(PostCleanup)`:** `tcx.optimized_mir(did)` steals `tcx.mir_drops_elaborated_and_const_checked(did)` (`rustc_mir_transform/src/lib.rs:800`) and transitions `body.phase` to `Runtime(Optimized)` (even at `-Z mir-opt-level=0`, running passes such as `RemoveStorageMarkers`, `RemoveZsts`, and `InstSimplify`). To capture unadulterated `Runtime(PostCleanup)` MIR for functions while still obtaining `mentioned_items`, clone or serialize `tcx.mir_drops_elaborated_and_const_checked(local_def_id).borrow()` before invoking `tcx.optimized_mir(def_id)` (`output.txt:120`). |

### 3. Dual-Emitter and Shadow-Artifact Defects in the MIR-to-x86-64 Pipeline

`Basis: source + derived`

Tracing the verification and assembly pipeline in `joshlf/anneal` at
`4f45f0a391a921ced9c9dc773b9a040dbc215d14` shows that there is no `Prog.lean`
artifact. Instead, `capture_crate_with_options`
(`trusted/rustc-capture/src/lib.rs:577-680`) parses textual MIR into a Rust
vector `Vec<CapturedFunction>` (each already lowered in Rust to `Vec<X86Block>`
via `lower_block` and `lower_rvalue` at lines 1123–1433) and feeds that slice
into two unlinked Rust string formatters:

1. `render_mir_lean_with_metadata(&functions, &meta)` (`lib.rs:1435-1561`),
   which writes `.anneal/Mir.lean` containing `def <fn>_body : Trusted.X86Body`
   and `def crate : Trusted.Crate` (with
   `tcb := [Trusted.TCBItem.assemblerLowering "<fn>" <fn>_body]`), and
2. `render_x86_assembly(&functions)` (`lib.rs:1589-1820`), which writes
   `.anneal/Prog.s` containing `.intel_syntax noprefix` GNU assembly text.

When `cargo-anneal` runs (`trusted/cargo-anneal/src/lib.rs:341-425`), it runs
`lake build Proof` (compiling `.anneal/Proof.lean` generated by
`render_proof_lean` in `trusted/rustc-capture/src/proof_gen.rs:42-201`) and
then invokes `anneal-audit` (`trusted/audit/src/lib.rs:1494-1658`) and
`TrustedBoundary.lean` (`trusted/audit/TrustedBoundary.lean:900-974`). Neither
`anneal-audit` nor `TrustedBoundary.lean` ever opens, hashes, or inspects
`.anneal/Prog.s`. In `Trusted/X86Semantics.lean:706-770`, `TargetArtifact` is
defined as a trivial unit wrapper
(`structure TargetArtifact where unit : Unit := ()`) and
`opaque assemble : X86Body → TargetArtifact := fun _ => { unit := () }`.

This pipeline has two structural soundness defects.

#### Defect 3.1: Discrepancies Between `Mir.lean` and `Prog.s`

`Basis: source`

Because `CapturedFunction::to_lean` (`lib.rs:334-465`) and
`render_x86_assembly` (`lib.rs:1589-1820`) are independent Rust code paths over
`CapturedFunction`, they disagree on four constructs in commit
`4f45f0a391a921ced9c9dc773b9a040dbc215d14`:

| Construct in `trusted/rustc-capture/src/lib.rs` (`4f45f0a391a9`) | What `render_mir_lean_with_metadata` Emits into `.anneal/Mir.lean` & How `X86Semantics.lean` Models It | What `render_x86_assembly` Emits into `.anneal/Prog.s` & What the CPU Executes | Soundness Impact |
| :--- | :--- | :--- | :--- |
| **`CapturedTerminator::Panic`** | Emits `Trusted.X86Term.abortPanic` (`lib.rs:422`). `X86Semantics.lean:410` (`execTerm`) models `.abortPanic` as `pure (.terminated .unwind s)`, which satisfies `SafeOutcome` (`X86Semantics.lean:486-490`: `.terminated .unwind _ => True`). | `lib.rs:1756-1758` merges `CapturedTerminator::Unreachable \| CapturedTerminator::Panic => writeln!(out, "    ud2")`! | **Unsoundness on panic paths:** Any function that panics (such as `assert!(x != 0)`) is verified in Lean as safely unwinding (`.terminated .unwind`), while `.anneal/Prog.s` executes `ud2` (`SIGILL` illegal instruction trap) instead of `call abort`. |
| **`CapturedTerminator::CallSizeOf { dst, ty, target }`** | Emits `Trusted.X86Term.movSizeOfJmp ⟨dst⟩ ty ⟨target⟩` (`lib.rs:433`). `X86Semantics.lean:419-424` writes `evalX86TyByteSize s.tySizes ty` (`0` for `unit`, `1` for `bool`, `8` for `usize`, `tySizes idx` for `param idx`). | `lib.rs:1773-1780` ignores `ty` (`let _ = ty;`) and unconditionally emits `mov QWORD PTR [rbp - {dst_off}], 8`! | **Wrong runtime value for `size_of::<T>()`:** For `bool`, `()`, or any generic `T` with `size_of::<T>() != 8`, Lean proves correctness assuming `size_of` returns `0`, `1`, or `tySizes idx`, while `.anneal/Prog.s` hardcodes `8`. |
| **`CapturedTerminator::CallTransmuteCopy { src_ptr, dst, src_ty, dst_ty, target }`** | Emits `Trusted.X86Term.repMovsbJmp ⟨src_ptr⟩ ⟨dst⟩ src_ty dst_ty ⟨target⟩` (`lib.rs:442`). `X86Semantics.lean:426-447` checks `n = evalX86TyByteSize s.tySizes dst_ty` and copies `n` bytes (`0`, `1`, `8`, or `tySizes idx`). | `lib.rs:1782-1796` ignores `src_ty` and `dst_ty` (`let _ = (src_ty, dst_ty);`) and unconditionally emits an 8-byte load/store (`mov rax, QWORD PTR [rsi]; mov QWORD PTR [rbp - {dst_off}], rax`)! | **Out-of-bounds 8-byte read on `<8`-byte `transmute_copy`:** For a 1-byte `bool` or 0-byte `()`, Lean verifies a 1-byte or 0-byte read, while `.anneal/Prog.s` performs an 8-byte `QWORD PTR [rsi]` read past the allocation. |
| **64-bit Arithmetic & Shifts (`evalX86BinOp`)** | `X86Semantics.lean:207-216` models `add`, `sub`, `mul`, `shl`, and `shr` over unbounded Lean `Nat`: `a + b`, `a - b` (saturating at `0` when `a < b`), `a * b`, `a <<< b` (unmasked), `a >>> b` (unmasked). | `lib.rs:1707-1725` emits 64-bit modular `add rax, rcx`, `sub rax, rcx` (wrapping modulo $2^{64}$, so `0 - 1 = UINT64_MAX`), `imul rax, rcx`, and `shl rax, cl` / `shr rax, cl` (which mask `cl` by `0x3f`, so `1ULL << 65 == 2ULL`). | **Semantic model mismatch between `X86Semantics.lean` and hardware ISA:** Proofs in Lean reason about saturating `Nat` subtraction and unmasked `Nat` shifts, whereas the emitted instructions wrap modulo $2^{64}$ and mask shift counts modulo 64. |

#### Defect 3.2: Unverified Rust Lowering and Bypassable `compileStage0`

`Basis: source + execution`

In `4f45f0a391a921ced9c9dc773b9a040dbc215d14`, `.anneal/Mir.lean` does not
contain `MirBody`; it contains `Trusted.X86Body` lowered by Rust code in
`trusted/rustc-capture/src/lib.rs:1123-1433`. Although
`theory/Anneal/MirLemmas.lean` (lines 448 and 761) defines
`idCopyBody : X86Body := compileStage0 idCopyMirBody` so that auto-generated
proofs check `compileStage0 idCopyMirBody = Mir.id_body` by definitional
equality (`rfl`), `Mir.crate` itself records only `X86Body`. Consequently:

1. **Custom proofs (`--keep-proof`) can bypass `compileStage0` and `MirSem`
   entirely:** A user-supplied `Proof.lean` only has to prove
   `Trusted.CrateTheorem Mir.crate` over the `X86Body` terms in `Mir.lean`.
   Nothing in `Trusted.CrateTheorem` or `TrustedBoundary.lean` requires
   `compileStage0` (or any `MirBody`) to appear in the proof.
2. **In-Lean optimizations (`theory/Anneal/Compiler/Peephole.lean`) cannot be
   reflected in `Prog.s`:** `Peephole.lean` defines
   `optimizePeephole : X86Body → X86Body` and proves `optimizePeephole_sound`.
   Because `.anneal/Mir.lean` and `.anneal/Prog.s` are emitted by
   `anneal-rustc-capture` before Lean runs, applying `optimizePeephole` inside
   Lean causes `optimizePeephole (compileStage0 ...)` to no longer be
   definitionally equal to the unoptimized `Mir.<fn>_body` in `Mir.lean`, while
   `.anneal/Prog.s` remains unoptimized.
3. **`Peephole.lean` uses `WellFounded.fix` recursion that blocks kernel `rfl`
   reduction:** In `theory/Anneal/Compiler/Peephole.lean:18-26`,
   `peepholeInstrs` recurses on `peepholeInstrs (i1 :: rest)` and
   `peepholeInstrs (i2 :: rest)`. Executing this pattern in Lean `v4.34.1`
   compiles via `WellFounded.fix`, which hits `maximum recursion depth has been
   reached` when reduced by `rfl`. Rewriting `peepholeInstrs` via
   `List.foldr peepholeStep []` (lines 229–240 of
   `support/artifact_binding_probe/SingleSourceCodegen.lean`) uses primitive
   structural recursion (`List.rec`) and reduces by `rfl` inside the Lean
   kernel.

### 4. Single-Source Artifact Binding Architecture and Prototype Evaluation

`Basis: source + execution + derived`

To eliminate both the shadow-artifact gap between `Mir.lean` and `Prog.s` and
the unverified Rust MIR-to-x86 lowering, two candidate single-source artifact
binding mechanisms were evaluated:

- **Mechanism (i) — In-Lean Total Deterministic `.s` Serializer
  (`Trusted.emitX86CrateAsm : X86Crate → String`) + Kernel/Auditor Binding:**
  1. `anneal-rustc-capture` emits **only** captured `MirBody` definitions into
     `.anneal/Mir.lean` (`Mir.crate : Trusted.MirCrate`). All Rust-side x86
     lowering (`lower_block`, `lower_rvalue`, `render_x86_assembly`) is deleted
     from `trusted/rustc-capture`.
  2. In `theory/Anneal/Compiler/`, Lean functions compile and optimize
     `Mir.crate` into `Prog.x86Crate : Trusted.X86Crate`
     (`compileAndOptimizeCrate Mir.crate`).
  3. `trusted/lean/Trusted/X86Emit.lean` defines a pure, total, structural
     serializer `Trusted.emitX86CrateAsm : Trusted.X86Crate → String`.
  4. During build and verification, Lean writes `.anneal/Prog.s` by evaluating
     `Trusted.emitX86CrateAsm Prog.x86Crate`.
  5. During `anneal-audit`, `TrustedBoundary.lean` enforces byte-for-byte
     identity between the kernel-verified `Prog.x86Crate` and `.anneal/Prog.s`
     on disk via one of two sub-variants:
     - **Sub-variant (i-a) (`CrateTheorem` `rfl` commitment + `.olean` string
       literal check):** `Trusted.CrateTheorem mc xc asmText` includes the
       field `asm_eq : Trusted.emitX86CrateAsm xc = asmText`, which the Lean 4
       kernel verifies by `rfl` during `Environment.replay`.
       `TrustedBoundary.lean` then inspects `env.find? ``Prog.asmText`, checks
       that its value is a raw string literal
       `Lean.Expr.lit (.strVal committedAsm)`, and verifies
       `committedAsm == (← IO.FS.readFile progSPath)`.
     - **Sub-variant (i-b) (Post-replay `X86Crate` AST decoding in
       `TrustedBoundary.lean`):** After `Environment.replay` verifies
       `Proof.verify_crate : Trusted.CrateTheorem Mir.crate Prog.x86Crate`,
       `TrustedBoundary.lean` decodes the closed `X86Crate` term from the
       replayed kernel `Environment` (extending `checkTargetConstants` at
       `TrustedBoundary.lean:622-720`), evaluates
       `Trusted.emitX86CrateAsm decodedCrate` directly inside the auditor, and
       verifies
       `Trusted.emitX86CrateAsm decodedCrate == (← IO.FS.readFile progSPath)`.
- **Mechanism (ii) — Rust-Side `.s` Emitter with `.olean` AST Round-Trip
  Check:**
  `anneal-rustc-capture` continues to emit `.anneal/Prog.s` in Rust, and
  `anneal-audit` reconstructs the `X86Crate` AST from `.olean` in Rust (or
  parses `.anneal/Prog.s` back into `X86Crate`) to check equivalence.

| Evaluation Criterion | Mechanism (i-a): In-Lean `emitX86CrateAsm` + Kernel `rfl` on `Prog.asmText` | Mechanism (i-b): In-Lean `emitX86CrateAsm` + Auditor AST Evaluation | Mechanism (ii): Rust Emitter + `.olean` AST Round-Trip Check |
| :--- | :--- | :--- | :--- |
| **Number of `.s` assembly printers in repository** | **1** (`Trusted/X86Emit.lean`) | **1** (`Trusted/X86Emit.lean`) | **2** (one in Rust `rustc-capture`, one in Lean/Rust auditor) |
| **Supports in-Lean verified optimization passes (`Peephole.lean`) without Rust duplication** | **Yes** (`Prog.x86Crate := compileAndOptimizeCrate Mir.crate`) | **Yes** (if `Prog.x86Crate` is stored as a concrete AST or reduced in auditor) | **No** (unless every Lean optimization pass is duplicated in Rust `rustc-capture`) |
| **New lines of code in `trusted/audit/TrustedBoundary.lean`** | **~15 LOC** (match `Expr.lit (.strVal committedAsm)` on `Prog.asmText` and compare to `IO.FS.readFile`) | **~90 LOC** (structural `Expr` decoders for `X86Crate`, `X86Body`, `X86Instr`, `X86Term`) | **~250+ LOC** (full `X86Body` binary `.olean` decoder or `.s` assembly parser in `trusted/audit/src/lib.rs`) |
| **Kernel reduction scaling on large crates** | In Lean `v4.34.1`, `String` is `ByteArray` (`List UInt8`); `rfl` on a single `N`-byte `String` takes `~2N` defeq steps (requiring `set_option maxRecDepth` or per-function/per-line `List String` equality for large functions). | **O(1) in kernel** (no `String` equality inside the kernel; `TrustedBoundary.lean` runs compiled `Trusted.emitX86CrateAsm` in native code after `replay`). | **O(1) in kernel**, but shifts complexity into effectful Rust `.olean` parsing. |

Mechanism (i) establishes `Trusted.emitX86CrateAsm : Trusted.X86Crate → String`
in `trusted/lean/Trusted/` as the single assembly emitter in Anneal. Sub-variant
(i-a) is mechanized end-to-end in
`support/artifact_binding_probe/SingleSourceCodegen.lean` and
`support/artifact_binding_probe/AuditMain.lean`: `SingleSourceCodegen.lean`
compiles a `MirCrate` to `X86Crate`, runs `optimizePeephole`, proves
`CrateTheorem Mir.crate Prog.x86Crate Prog.asmText` with
`-Ddebug.skipKernelTC=false`, emits `Prog.s`, verifies acceptance of genuine
`Prog.s` and rejection of tampered `Prog_tampered.s`, and executes the
assembled function on the x86-64 CPU.

## Boundaries

- **Known not to apply:**
  - `ty::Instance::resolve_drop_glue(tcx, ty)` is **known not to apply** to
    uninstantiated polymorphic `Ty<'tcx>` values (`requires_monomorphization`):
    `rustc` asserts monomorphic types inside `resolve_drop_glue`
    (`compiler/rustc_middle/src/ty/instance.rs:168-170`).
  - `tcx.mir_for_ctfe(def_id)` is **known not to apply** to trivial constants
    where `tcx.is_trivial_const(local_def_id)` is `true`
    (`compiler/rustc_mir_transform/src/lib.rs:493`); callers must branch on
    `tcx.is_trivial_const` and use `tcx.trivial_const(local_def_id)` first.
  - `body.mentioned_items()` is **known not to apply** to `mir_for_ctfe` bodies
    (`Const`, `AssocConst`, `Static`, `AnonConst`) because the `MentionedItems`
    pass runs only inside `inner_optimized_mir`
    (`compiler/rustc_mir_transform/src/lib.rs:810`).
- **Unsupported:**
  - Both examined Anneal revisions (`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`
    and `4f45f0a391a921ced9c9dc773b9a040dbc215d14`) leave `unsafeImpls`
    **unsupported** in `trusted/rustc-capture/src/lib.rs`, emitting `[]` by
    default.
- **Not examined:**
  - Polymorphic drop-shim extraction via
    `rustc_mir_transform::build_drop_shim`
    (`compiler/rustc_mir_transform/src/lib.rs:56`) versus post-monomorphization
    reachability traversal for generic ADTs was **not examined** experimentally
    in `support/obligation_inventory_probe/`.
  - Migrating `Trusted/X86Semantics.lean` from unbounded `Nat` arithmetic to
    64-bit modular `UInt64` / `BitVec 64` across the full `MirLemmas.lean` and
    `NaiveCodegen.lean` proof suite was **not examined** beyond the standalone
    `UInt64` mechanization in
    `support/artifact_binding_probe/SingleSourceCodegen.lean`.

## Evidence

### Primary Git and Toolchain Sources

- **`joshlf/anneal` at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`:**
  - `trusted/rustc-capture/src/lib.rs`: lines 399–550
    (`capture_crate_with_options`, `parse_source_metadata`), lines 568–863
    (`parse_emitted_mir_with_metadata`, `parse_fn_header`, `NonZeroUsize`
    hardcoding), lines 1062–1071 (`pme_assert_const` hardcoding), and lines
    1250–1315 (`render_mir_lean_with_metadata`, omission of `unsafeImpls`).
  - `trusted/rustc-capture/src/proof_gen.rs`: lines 51–132
    (`render_proof_lean`, fixed 1/2/3-function template dispatch).
  - `trusted/lean/Trusted/MirSemantics.lean`: lines 768–845 (`FnKind`,
    `AdmissibleAdtInv`, `UnsafeImplObligation`, `Crate`, `CrateTheorem`).
- **`joshlf/anneal` at `4f45f0a391a921ced9c9dc773b9a040dbc215d14`:**
  - `trusted/rustc-capture/src/lib.rs`: lines 334–465
    (`CapturedFunction::to_lean`), lines 577–680 (`capture_crate_with_options`
    dual emission of `Mir.lean` and `Prog.s`), lines 745–795
    (`parse_source_metadata`), lines 1123–1433 (unverified Rust MIR-to-x86
    lowering), lines 1435–1561 (`render_mir_lean_with_metadata`), and lines
    1589–1820 (`render_x86_assembly`, specifically lines 1756–1758 for
    `Panic => ud2`, lines 1773–1780 for `CallSizeOf => 8`, and lines 1782–1796
    for `CallTransmuteCopy => 8-byte mov`).
  - `trusted/rustc-capture/src/proof_gen.rs`: lines 42–201
    (`render_single_fn_proof_term`, `render_proof_lean` emitting
    `theorem verify_crate : Trusted.CrateTheorem Mir.crate` with no binding to
    `.anneal/Prog.s`).
  - `trusted/lean/Trusted/X86Semantics.lean`: lines 207–216 (`evalX86BinOp` on
    `Nat`), lines 408–448 (`execTerm` for `abortPanic`, `movSizeOfJmp`,
    `repMovsbJmp`), and lines 706–875 (`TargetArtifact`, `opaque assemble`,
    `CrateTheorem`).
  - `trusted/audit/TrustedBoundary.lean`: lines 622–720
    (`checkTargetConstants`) and lines 900–974 (`runAudit`).
  - `trusted/audit/src/lib.rs`: lines 1494–1658 (`run_audit`).
  - `theory/Anneal/Compiler/NaiveCodegen.lean`: lines 201–209
    (`compileStage0`).
  - `theory/Anneal/Compiler/Peephole.lean`: lines 18–30 (`peepholeInstrs`) and
    lines 84–140 (`optimizePeephole`, `optimizePeephole_sound`).
  - `theory/Anneal/MirLemmas.lean`: lines 448 and 761 (`idCopyBody`,
    `binOpBody`).
- **`rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67` (`rustc
  1.99.1`):**
  - `compiler/rustc_hir/src/def.rs`: lines 100–204 (`DefKind`).
  - `compiler/rustc_middle/src/ty/mod.rs`: lines 298–305 (`ImplTraitHeader`).
  - `compiler/rustc_middle/src/ty/generics.rs`: lines 121–382 (`Generics`) and
    lines 385–460 (`GenericClauses`, `tcx.clauses_of`).
  - `compiler/rustc_middle/src/ty/instance.rs`: lines 33–198 (`Instance`,
    `InstanceKind`, `ShimKind`) and lines 562–851 (`Instance::try_resolve`,
    `Instance::resolve_drop_glue`, `Instance::fn_once_adapter_instance`).
  - `compiler/rustc_middle/src/mir/mod.rs`: lines 265–285 (`required_consts`,
    `mentioned_items`) and lines 717–750 (`Body::required_consts`,
    `Body::mentioned_items`).
  - `compiler/rustc_mir_transform/src/lib.rs`: lines 327–358 (`mir_keys`),
    lines 432–532 (`mir_promoted`, `mir_for_ctfe`), lines 537–685
    (`mir_drops_elaborated_and_const_checked`,
    `run_analysis_to_runtime_passes`), and lines 778–824 (`optimized_mir`,
    `MentionedItems`).
  - `compiler/rustc_interface/src/passes.rs`: lines 1154–1282
    (`run_required_analyses`, `analysis`).

### Preserved Package Support Artifacts

All executable probes and golden outputs are preserved under `support/` inside
this package directory (observed on `2026-10-31`):

| Package Relative Path | Lines | SHA-256 Digest | Role |
| :--- | ---: | :--- | :--- |
| `support/obligation_inventory_probe/driver.rs` | 344 | `c57203d0d5a407d764b5bccaa4ef44ab61b888e4ae7a1eab5568e608c2952109` | `rustc_driver` `Callbacks` harness querying `TyCtxt` in `rustc 1.99.1` |
| `support/obligation_inventory_probe/src/lib.rs` | 241 | `56608b737fce68d485cacc62a611db230f7291f68cf6b9407fbc658743114c6b` | Target Rust crate exercising all five obligation categories (a)–(e) |
| `support/obligation_inventory_probe/output.txt` | 124 | `98476f987b2c323d1425cb781f0e0fc92ae6b65e2805de04fa22bc7707b10269` | Captured stdout of `obligation_inventory_probe` on `src/lib.rs` |
| `support/artifact_binding_probe/SingleSourceCodegen.lean` | 309 | `2180538f940e3ad65200ad48cbb6b605da161246105ffb88b5c4fc146d4ff972` | Lean 4 (`v4.34.1`) mechanization of `MirCrate → X86Crate → emitX86CrateAsm` and `Proof.verify_crate` |
| `support/artifact_binding_probe/AuditMain.lean` | 64 | `32ab7bca619bb5a4162dacdc11d3454855c347e6adc407b08ae42f8bf8e5c071` | `.olean` environment inspector verifying `Proof.verify_crate` and `Prog.asmText == diskAsm` |
| `support/artifact_binding_probe/main.c` | 21 | `51b03421d87457ebd41a20a0dfcf169f7e57c720f648d1a5af774ba8370845cc` | C test harness calling `anneal_double_u64` in `Prog.s` |
| `support/artifact_binding_probe/run_probe.sh` | 41 | `aca8ce388b30a0e3aa46881fbe3642b1363afe93c2c08b942fad08b14e0a4580` | End-to-end verification, tamper-rejection, assembly, and CPU execution script |
| `support/artifact_binding_probe/Prog.s` | 20 | `43004780607d2288338789a217ec11edf96a2b8ded5bbb7dbb76b7a1841cc3a1` | x86-64 assembly emitted by `Trusted.emitX86CrateAsm Prog.x86Crate` |
| `support/artifact_binding_probe/output.txt` | 10 | `e72e34a962e649521d2a6b0cba52a6da308347a703b4b3bfe71f86751c93ebb3` | Captured stdout of `run_probe.sh` |

## Revalidation

Revalidate this report's claims whenever:

1. Anneal updates its pinned `rustc` toolchain from `1.99.1`
   (`58cf8f9c35b355199727627d07ae34a4e2846d67`), which may alter internal
   `rustc_middle::ty` or `rustc_mir_transform` query signatures (`clauses_of`,
   `impl_trait_header`, `Instance::resolve_drop_glue`,
   `mir_drops_elaborated_and_const_checked`).
2. Anneal updates its pinned Lean 4 toolchain from `v4.34.1`
   (`5045d0056413266e57c625dcd7c365b10e377c52`), which may change `String` /
   `ByteArray` kernel reduction behavior or `Lean.Environment` constant
   representations.
3. `trusted/rustc-capture`, `trusted/lean/Trusted/`, or
   `trusted/audit/TrustedBoundary.lean` is modified.

To rerun both preserved probes from this package directory:

```bash
# 1. Re-run the rustc_driver obligation inventory probe
SYSROOT="$(rustc +stable --print sysroot)"
RUSTC_BOOTSTRAP=1 rustc +stable --edition=2021 \
  support/obligation_inventory_probe/driver.rs \
  -o /tmp/obligation_inventory_driver \
  -C link-args="-Wl,-rpath,$SYSROOT/lib"
RUSTC_BOOTSTRAP=1 /tmp/obligation_inventory_driver \
  --crate-type=lib --edition=2024 \
  support/obligation_inventory_probe/src/lib.rs
rm -f /tmp/obligation_inventory_driver

# 2. Re-run the Lean 4 + x86-64 single-source artifact binding probe
LEAN="${LEAN:-lean}" ./support/artifact_binding_probe/run_probe.sh
```
