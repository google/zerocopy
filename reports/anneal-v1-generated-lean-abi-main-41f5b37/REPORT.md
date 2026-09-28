# Anneal V1 generated-Lean ABI and Aeneas coupling

## Summary

Retained Anneal V1 does not discover the Lean interface produced by Aeneas and then generate proofs against that discovered interface. It predicts a substantial part of that interface independently from Rust syntax and naming conventions, then emits Lean which must elaborate against Aeneas's generated modules. That prediction boundary is the effective **generated-Lean ABI** between the two tools.

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, the contract has four important layers:

1. **Artifact/module identity.** Anneal computes a stable PascalCase artifact slug and expects Aeneas output beneath `generated/<Slug>/`, particularly `Funs.lean` and `Types.lean`. Anneal's own specification file is `<Slug>.lean` in the same directory and imports `«<Slug>».Funs` and `«<Slug>».Types`.
2. **Names and types.** Anneal predicts Aeneas namespaces, function identifiers, Rust-to-Lean type names, generic parameters, and explicit trait-dictionary arguments. This is source-derived duplication of Aeneas lowering conventions, not a typed interface read from Aeneas output.
3. **Function result shape.** Anneal assumes Aeneas models a translated call as `Result α` and that mutable-reference post-state is encoded in the successful result. It generates a postcondition over the Aeneas call and destructures the successful value according to a locally predicted tuple shape.
4. **Compatibility shims and fail-closed checks.** V1 contains concrete repairs for Aeneas output (`@[discriminant]` and a `show` identifier collision), adds `noncomputable section` to `Funs.lean`, copies external templates into live modules, and rejects missing `Funs.lean` or `Types.lean` when its source scan says those outputs should exist.

The coupling is therefore broader than file names. A change in Aeneas naming, type rendering, dictionary ordering, reference erasure, successful-result tuple shape, external-file conventions, or emitted Lean syntax can break Anneal even when LLBC translation itself still succeeds. The checked-in integration goldens show this contract in use, including an Anneal theorem over an Aeneas `Result` function and a mutable-reference case destructuring `(ret, x')`.

This is a historical V1 contract, not current Anneal V2 design authority. A future design should avoid treating these source-level predictions as a stable upstream ABI unless it deliberately owns and tests that compatibility surface.

## Applicability

The Anneal subject is the retained historical implementation at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, under `anneal/v1`. Its `Cargo.toml` pins Aeneas revision `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` and Lean `leanprover/lean4:v4.30.0-rc2`. The report concerns the interface between that exact Anneal source and that pinned Aeneas family as encoded by Anneal's generator/orchestrator and preserved integration fixtures.

The term **ABI** here means a generated-source integration contract, not a machine calling convention and not a compatibility promise made by Lean or Aeneas. Some parts are deliberately stabilized by Anneal itself, such as its artifact slug. Others are implementation assumptions duplicated from Aeneas behavior, such as function naming, trait dictionary conventions, and post-state tuple shape.

Evidence is source inspection plus checked-in regression/golden artifacts. No fresh Anneal, Aeneas, Charon, Lean, or integration-test execution was performed in this report. The preserved fixtures are evidence of behavior exercised when those fixtures were produced; they are not a fresh observation from this run.

## Findings

### Artifact identity is shared across LLBC, Aeneas modules, and Anneal specifications

`AnnealArtifact::artifact_slug` constructs a Lean-compatible identifier from the package name, target name, target kind, and a stable SHA-256-derived hash that includes the manifest path. Package and target components are converted to PascalCase. The hash makes otherwise identical package/target names in different manifests or target kinds distinct.

That slug becomes the cross-stage identity:

```text
llbc/<Slug>.llbc
generated/<Slug>/Funs.lean
generated/<Slug>/Types.lean
generated/<Slug>/FunsExternal.lean       when needed
generated/<Slug>/TypesExternal.lean      when needed
generated/<Slug>/<Slug>.lean             Anneal specs/proofs
generated/<Slug>/<Slug>.lean.map         Rust↔Lean source map
```

Anneal invokes Aeneas with `-backend lean -dest generated/<Slug> -split-files -abort-on-error`. The generated Lake library uses `generated` as its source directory and registers `<Slug>.Funs`, `<Slug>.Types`, and any external modules as roots. Anneal's generated spec imports the Funs and Types modules by that same slug.

This is one of the more intentionally controlled parts of the ABI: the slug algorithm lives in Anneal and is also the output-directory/module prefix under which it asks Aeneas to generate. But compatibility still assumes that split-file Aeneas generation uses the expected `Funs.lean` and `Types.lean` module names within that directory.

Basis: **source**, `scanner.rs` (`AnnealArtifact::artifact_slug`, `llbc_file_name`, `lean_spec_file_name`) and `aeneas.rs` (`run_aeneas`, generated Lake roots, `generate_lean_workspace`).

### Anneal imports Aeneas output directly rather than through a generated adapter

Every Anneal specification file begins with a fixed header that imports:

```lean
import Anneal
import Aeneas.Std.Scalar.Core
import «<Slug>».Funs
import «<Slug>».Types
```

It then opens `Aeneas Aeneas.Std Result`, starts a `noncomputable section`, calls `inject_builtins`, and enters a namespace derived from the Rust target name with hyphens replaced by underscores.

There is no generated adapter layer which first reads Aeneas declarations and re-exports a normalized Anneal interface. Consequently, names and signatures referenced later in the file must match Aeneas output directly.

The checked-in `expand_output` golden makes this concrete. Its Aeneas portion defines `expand_output.foo : Result Unit` in namespace `expand_output`; its Anneal portion imports the slugged `Funs` and `Types` modules, enters `namespace expand_output`, and proves a theorem whose proposition is `Aeneas.Std.WP.spec (foo) ...`.

Basis: **source** + preserved **execution/regression artifact**, `generate.rs::generate_artifact` and `tests/fixtures/expand_output/expected-all.stdout`.

### Function and namespace lookup is predicted from Rust syntax

Anneal computes the Aeneas function reference without inspecting the generated Funs module. For a function it uses the Rust function identifier as the Aeneas call name. For module nesting it uses the scanned Rust module path, omitting the leading `crate`; inherent impl methods additionally insert the implementing type path. The fully-qualified helper name used by proof tactics is then assembled as `_root_.<crate>.<namespace>.<function>`.

The same `NamingContext` puts the generated Anneal theorem inside corresponding namespaces. Each function receives its own namespace and a theorem or axiom named `spec`.

This design means namespace flattening and method naming are ABI assumptions. If Aeneas changes how a Rust item is named in Lean while Anneal's independent reconstruction stays unchanged, the generated specification references the wrong declaration even though both tools may individually process the Rust program successfully.

Basis: **source**, `generate.rs::NamingContext`, `generate_function`, and `render_theorem`.

### Anneal maintains its own Rust-to-Lean type renderer

`generate.rs::map_type` maps parsed Rust types into the Lean names Anneal expects Aeneas to use. Among the explicit rules at this revision:

- integer primitives map to `Std.U8`, `Std.U16`, ..., `Std.Isize`;
- `bool` maps to `Bool`;
- `&T` and `&mut T` erase the reference wrapper and map as `T`;
- `*mut T` and `*const T` map to `MutRawPtr T` and `ConstRawPtr T`;
- slices map to `Slice T`;
- arrays map to `Array T N`;
- `!` maps to `Never`;
- tuples map to Lean products;
- ordinary paths are reconstructed by joining Rust path segments with `.` and recursively rendering generic arguments.

This is not derived from Aeneas's generated type declarations. It is a second implementation of expected Aeneas naming/type conventions. `MatchError` is used as the fallback for unsupported mirrored types, and `is_unit_return` treats both `Unit` and `MatchError` as having no ordinary return value; that makes unsupported type mapping especially important to validate at the earlier parsing/validation boundary rather than interpreting `MatchError` as a real compatible ABI type.

Basis: **source**, `generate.rs::map_type`, `extract_args_metadata`, and `is_unit_return`.

### References are erased at the input type boundary, while mutable post-state reappears in the result

Anneal's type renderer erases both shared and mutable Rust references to their referent Lean type. It separately remembers whether an input was a true `&mut T`. A merely mutable by-value Rust binding is not marked this way.

For a function with mutable-reference arguments, Anneal expects the successful Aeneas result to carry updated referent state. Its generated postcondition destructures the `Result` payload according to these rules:

- ordinary return, no mutable references: use the payload as `ret`;
- ordinary return plus mutable references: expect `(ret, x', y', ...)` syntax;
- no ordinary return plus exactly one mutable reference: expect the payload directly as `x'`;
- no ordinary return plus multiple mutable references: expect `(x', y', ...)` syntax;
- no ordinary return and no mutable reference: ignore the `Unit` payload.

The postcondition structure itself has matching output parameters and adds automatic `Anneal.IsValid.isValid` obligations for the ordinary return and each mutable post-state.

This is a high-value compatibility boundary because Anneal computes the tuple shape from the Rust signature rather than reading the translated Aeneas function's result type. A change in Aeneas state-threading or return packing can invalidate generated proofs without changing the Rust signature.

The checked-in `extern_never_verified/out.txt` preserves a concrete generated case:

```lean
Aeneas.Std.WP.spec (die x) (fun ret_ =>
  let (ret, x') := ret_
  Post x ret x')
```

with the proof branch introducing `⟨ret, x'⟩`.

Basis: **source** + preserved **execution/regression artifact**, `generate.rs::extract_args_metadata`, `generate_function`, and `tests/fixtures/extern_never_verified/out.txt`.

### `Result` and `WP.spec` are part of the cross-tool contract

The pinned Aeneas `Aeneas.Std.Primitives` defines:

```lean
inductive Result (α : Type u) where
  | ok (v : α)
  | fail (e : Error)
  | div
```

and its `Aeneas.Std.WP` layer defines `spec` by applying a weakest-precondition interpretation to a `Result`. Successful `ok x` satisfies the supplied postcondition at `x`; both failure and divergence make `spec` false. The same WP module contains helpers for decomposing product-valued postconditions.

Anneal emits `Aeneas.Std.WP.spec (<Aeneas call>) (fun ret_ => ...)` for every generated function specification. Its orthogonal proof wrapper then separates the proof that evaluation reaches success from the proof that the successful payload meets the generated `Post` structure.

Thus the generated ABI includes not only names and tuple geometry but the semantic carrier: Anneal assumes translated functions inhabit Aeneas's `Result` model and proves properties through this particular `WP.spec` relation.

Basis: Aeneas **source** (`Aeneas/Std/Primitives.lean`, `Aeneas/Std/WP.lean`) + Anneal **source** (`generate.rs`).

### Trait bounds use a locally reconstructed explicit-dictionary convention

For generic bounds, Anneal does not uniformly ask Lean typeclass synthesis to find the Aeneas dictionary. `extract_generic_params` special-cases `Sized`, but for ordinary Rust trait bounds it constructs an explicit dictionary parameter. It takes the base trait name, appends `Inst`, constructs a trait application with `Self`/generic arguments, emits a binder such as `(TraitInst : Trait T ...)`, and passes that dictionary explicitly in the generated Aeneas call.

The source comment says this mirrors Aeneas lowering and specifically references naming patterns such as `Clause0Inst` and `TraitInst`. This is another duplicated convention, including both dictionary existence and ordering. Aeneas can change trait lowering without changing Rust syntax; Anneal would then require a coordinated change.

Basis: **source**, `generate.rs::extract_generic_params` and `generate_function`.

### `Pre`, `Post`, and `spec` are Anneal-owned wrappers around the Aeneas declaration

For each annotated function, Anneal creates a function namespace. Inside it:

- `Pre` exists when there are arguments or proposition-valued `requires` clauses;
- every argument gets an automatic `h_<arg>_is_valid` field in `Pre`;
- user preconditions become additional fields;
- `Post` is always emitted and is parameterized by the original arguments plus the ordinary return and mutable-reference post-states that exist for that signature;
- `Post` contains automatic validity fields for outputs and user `ensures` clauses;
- the theorem/axiom is named `spec` and relates the predicted Aeneas function call to `Post` via `Aeneas.Std.WP.spec`.

These wrappers are not themselves Aeneas ABI. They are Anneal's side of the boundary. But their binders and call expressions are generated from the same predicted Aeneas names/types/result shape, so their successful elaboration is an integration test of that prediction.

Basis: **source**, `generate.rs::generate_function`, `render_struct`, and `render_theorem`; corroborated by checked-in generated outputs.

### Type and trait annotations also assume Aeneas names directly

For an annotated Rust type, Anneal generates an `Anneal.IsValid` instance for the Lean type name it predicts from the Rust type. For an unsafe Rust trait, it generates a nested `Safe` class taking an explicit instance of the predicted Aeneas trait application.

The type/trait side therefore has the same architectural property as function specs: Anneal is not resolving an exported declaration table from Aeneas. It expects its source-derived name and type reconstruction to elaborate against Aeneas's generated `Types.lean`.

Basis: **source**, `generate.rs::generate_type`, `generate_trait`, and `map_type`.

### Missing split output is treated as a translation failure, not silently papered over

Aeneas can legitimately omit `Funs.lean` if there are no translated functions and omit `Types.lean` if there are no translated types. Anneal therefore has a conditional compatibility rule:

- if the file is absent and Anneal's scan found no corresponding items, it creates an empty file so its fixed imports remain valid;
- if the file is absent but Anneal found function/impl or type/trait items, it aborts rather than manufacturing an empty module.

The checked-in `missing_output/expected.stderr` records the fail-closed diagnostic for the function case: Aeneas failed to generate `Funs.lean` even though Anneal found function/impl items, which Anneal describes as a silent Aeneas translation failure.

This check is important because the generated ABI otherwise permits a superficially well-formed empty module to hide missing translation coverage.

Basis: **source** + preserved **execution/regression artifact**, `aeneas.rs` and `tests/fixtures/missing_output/expected.stderr`.

### V1 carries concrete syntax-compatibility patches for generated Aeneas files

The retained V1 code contains direct textual repairs to generated Aeneas Lean:

1. In `Types.lean`, bare `@[discriminant]` is replaced with `@[discriminant isize]` because Anneal's pinned Lean/Aeneas environment expects the attribute to carry an integer-type parameter.
2. In `Funs.lean`, `(show :` is replaced with `(show1 :` because Aeneas can emit the Lean keyword `show` as an argument name without the renaming Anneal expects.
3. `Funs.lean` receives `noncomputable section` after its imports because translated functions may call opaque axioms and Lean's bytecode compiler otherwise rejects those definitions even though Anneal verification does not execute them directly.

These are not theoretical risks. They are source-level compatibility shims whose existence demonstrates that the Aeneas-generated Lean surface changed or differed enough to require downstream repair. They also show why “Aeneas produced Lean successfully” is weaker than “the produced Lean satisfies Anneal's consumed ABI.”

Basis: **source**, `aeneas.rs::patch_discriminants` and `patch_funs`.

### External templates are promoted into modules Anneal/Lake can import

When Aeneas emits `FunsExternal_Template.lean`, Anneal copies it to `FunsExternal.lean` if the latter does not already exist. The analogous rule applies to `TypesExternal_Template.lean`. These modules are then registered as Lake roots and imported by `Generated.lean` when present.

The generated external module therefore has a lifecycle contract beyond Aeneas's template naming: Anneal expects the template suffix, promotes it to the non-template filename, and relies on the resulting module as the default axiom-bearing implementation for opaque functions/types.

This matters for upgrades because changing the template naming convention or import expectations can break the generated workspace even if the ordinary Funs/Types declarations are unchanged.

Basis: **source**, `aeneas.rs::run_aeneas`.

### Source maps are a parallel generated interface, not semantic proof evidence

Anneal writes `<Slug>.lean.map` beside the spec file. Entries contain generated-Lean byte intervals, original Rust paths/ranges, and a mapping kind (`Source`, `Synthetic`, or `Keyword`). The diagnostic pass later recompiles each generated spec with `lean --json`, converts Lean line/column positions to byte ranges, and projects overlapping mappings back into Rust diagnostics.

A synthetic mapping anchors the generated `spec` identifier to the source Rust function name. User-authored proof lines receive direct source mappings. Keyword mappings support targeted redirection of diagnostics such as “declaration uses `sorry`.”

This source map is part of the usability ABI between generated code and diagnostics, but it is not evidence that the Aeneas declaration matched Rust semantics. It records blame/provenance positions for Anneal-generated text after the name/type/result-shape assumptions have already been made.

Basis: **source**, `generate.rs::{MappingKind,SourceMapping,LeanBuilder}` and `aeneas.rs::{generate_lean_workspace,run_lake,resolve_mapping}`.

### The preserved expand golden is a compact end-to-end ABI specimen

`tests/fixtures/expand_output/expected-all.stdout` contains both sides of the interface in one checked-in artifact. The Aeneas part defines:

```lean
namespace expand_output

def foo : Result Unit := do
  ok ()

end expand_output
```

The Anneal part imports the slugged Aeneas Funs/Types modules, enters the same `expand_output` namespace, creates `namespace foo`, emits `Post`, and proves:

```lean
theorem spec :
  Aeneas.Std.WP.spec (foo) (fun ret_ => Post) := by
  ...
```

This fixture is particularly useful for revalidation because it simultaneously exercises slug/module import, target namespace, function name, `Result Unit`, and the `WP.spec` wrapper. It does not by itself cover generics, trait dictionaries, mutable-reference tuples, or every type renderer case.

Basis: preserved **execution/regression artifact**.

## Boundaries

- **Historical scope only.** These findings describe retained Anneal V1 at `41f5b37...`; they are not current V2 architecture requirements.
- **No fresh execution.** No Charon, Aeneas, Anneal, Lean, Lake, or integration test was run for this report. Checked-in expected outputs are preserved regression evidence.
- **Not an upstream compatibility guarantee.** Neither the Aeneas project nor Lean is claimed here to promise this generated source interface as a stable ABI across releases.
- **No complete Aeneas lowering specification.** The report characterizes the portions Anneal predicts and consumes. It does not inventory every Aeneas naming, type, control-flow, borrow, trait, or external-model lowering rule.
- **Tuple notation is reported at the consumed interface.** The report states the tuple/product syntax Anneal generates and preserves a concrete `(ret, x')` example. It does not generalize that syntax into a separately proven canonical nesting law for every arity without a corresponding generated specimen.
- **Type rendering is not semantically validated here.** `map_type` records Anneal's expected Lean spellings. This report does not prove that every supported Rust type maps correctly or that unsupported `MatchError` cases are unreachable in every input path.
- **Scanner/compiler correspondence is separate.** Anneal's source scanner can disagree with the cfg-selected rustc/Charon program view; the dedicated source-scanner report owns that issue. The missing-output check is recorded here only because it protects the generated ABI boundary.
- **`isValid`, `isSafe`, and `unsafe(axiom)` soundness are separate.** Their generated declaration shapes matter here, but the separate V1 soundness reports own whether the resulting proof obligations are sufficient.
- **Source mappings are diagnostic metadata.** They should not be interpreted as source-to-Lean semantic correspondence proofs.
- **The textual patches establish coupling, not upstream fault assignment.** This report records what retained V1 does and why its comments say it does it; it does not infer which upstream revision introduced each mismatch or whether a newer upstream revision still needs the patches.

## Evidence

**Primary Anneal source:** `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`.

- `anneal/v1/Cargo.toml`, blob `f545b31c8e15a3cc5b5bbaf277abb9e56afc2e33`: pins Aeneas `42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` and Lean `v4.30.0-rc2`.
- `anneal/v1/src/scanner.rs`, blob `44b66417a827192b87d4cad3e62421e8ca497d28`: `AnnealArtifact`, stable artifact slug, LLBC/spec filename derivation, and source-item classification.
- `anneal/v1/src/generate.rs`, blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`: generated-file header/imports; `NamingContext`; `Pre`/`Post`/`spec`; predicted Aeneas names; mutable-reference result destructuring; generic dictionary convention; Rust-to-Lean type rendering; source mappings.
- `anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`: Aeneas invocation, Funs/Types existence checks, compatibility patches, external-template promotion, Lake roots, spec/map materialization, and diagnostic use of the sidecar map.
- `anneal/v1/docs/agent/04_specifications_and_syntax.md`, blob `1b5a7a8c9f7cc25b6549bc4f2697040c72e14f71`: documented user-facing `Pre`/`Post`, mutable post-state, validity, and proof names.
- `anneal/v1/docs/agent/05_proof_architecture.md`, blob `8f7f589c629876a4696ed86f215ba1c050a4ba36`: documented orthogonal WP proof shape and output-state environment.
- `anneal/v1/docs/design/design.md`, blob `f09bf3c9ecd828fb457006853632bc824b1218df`: design examples of generated `Pre`, `Post`, and `Aeneas.Std.WP.spec` use.

**Pinned Aeneas source:** `AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`.

- `backends/lean/Aeneas/Std/Primitives.lean`, blob `5a73ea5bfae575baf2f26e1d86ea00768d1bccea`: `Result.ok`, `Result.fail`, `Result.div`, and monadic bind.
- `backends/lean/Aeneas/Std/WP.lean`, blob `a599b2b6632fbfdfadbe3dcfb68ee17a6048be5d`: `WP.spec`, success/failure/divergence semantics, product-postcondition helpers, and `spec_imp_exists`.

**Preserved regression artifacts at the Anneal revision:**

- `anneal/v1/tests/fixtures/expand_output/expected-all.stdout`, blob `b4934dc041ad81cca05eeb4aa94a8e22ae39a66f`: one file containing the expected Aeneas output and expected Anneal output, including the matching namespace/function and `Result Unit` → `WP.spec` interface.
- `anneal/v1/tests/fixtures/extern_never_verified/out.txt`, blob `9cf7a9e663c0dc77597cbd007bc8917c87e6f9e2`: generated mutable-reference post-state example using `let (ret, x') := ret_` and `rintro ⟨ret, x'⟩`.
- `anneal/v1/tests/fixtures/missing_output/expected.stderr`, blob `5255829806d2be2cadf5c87060f17e3b12d9d7cf`: fail-closed diagnostic when an expected `Funs.lean` is absent.

No fresh **execution** evidence was produced in this run.

## Revalidation

For another Anneal/Aeneas revision pair, the cheapest reliable check is to treat the interface as a compatibility matrix rather than merely asking whether Aeneas exits successfully.

First diff the consumers/producers which define the contract:

1. Anneal's `AnnealArtifact::artifact_slug`, `lean_spec_file_name`, and generated workspace layout;
2. Aeneas split-file names and module names (`Funs`, `Types`, external templates);
3. Anneal `NamingContext` versus Aeneas crate/module/function/method naming;
4. `map_type` versus actual Aeneas-generated type names for all supported primitive, aggregate, pointer, reference, slice, array, tuple, generic, and user-defined cases;
5. trait dictionary names, binder order, and call-site argument order;
6. translated result types for zero, one, and multiple `&mut` parameters with and without an ordinary return;
7. Aeneas `Result`/`WP.spec` definitions used by Anneal proofs;
8. `patch_funs` and `patch_discriminants` to determine whether the upstream output still requires the same repairs;
9. external template naming/import behavior; and
10. source-map file naming and the generated spec positions that diagnostics depend on.

On an execution-capable surface, preserve a compact golden matrix. At minimum include:

- a no-argument `fn -> ()`;
- primitive arguments and return;
- one `&mut T` with return;
- one `&mut T` with unit return;
- two mutable references, with and without return;
- a free function, module function, inherent method, trait method, and foreign/opaque function;
- a generic function with `Sized` and at least one non-`Sized` trait bound;
- user types, tuples, slices, arrays, raw pointers, and a never-returning function;
- an opaque function/type which produces external templates;
- a type with a discriminant attribute; and
- an identifier colliding with a Lean keyword such as `show`.

For every specimen, compare the **actual Aeneas declarations** with the names, types, dictionary arguments, and result destructuring Anneal emits. Then build/check the generated Anneal spec file. A byte-level golden diff is useful, but the decisive compatibility test is successful elaboration of the generated spec against the exact generated Aeneas modules while preserving the intended function/result correspondence.

Keep a deliberate fail-closed test in which Aeneas omits a file for an item Anneal believes should translate. A successful empty-file fallback in that case would be a regression in coverage protection, not improved compatibility.
