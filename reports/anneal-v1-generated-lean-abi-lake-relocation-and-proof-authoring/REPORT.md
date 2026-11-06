# Anneal V1 Generated-Lean ABI, Lake Relocation Architecture, Prebuilt Archive Reuse, and Proof Authoring

## Summary

Retained Anneal V1 (`anneal/v1` in `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` and `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`) bridges Rust source annotations, Aeneas LLBC-to-Lean translation (`AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`), Lake build/cache orchestration (`leanprover/lean4:v4.30.0-rc2`), and tactic-driven Lean 4 proof authoring through four tightly coupled architectural mechanisms:

1. **Source-Predicted Generated-Lean ABI and Aeneas Coupling (`anneal/v1/src/{scanner.rs,generate.rs,aeneas.rs}`):** Rather than inspecting Aeneas's emitted Lean AST or symbol table, Anneal V1 predicts Aeneas module paths, namespace hierarchies, function identifiers, Rust-to-Lean type spellings (`map_type`), explicit trait-dictionary parameters (`*Inst` vs. special-cased `Sized`), reference erasure (`&T` / `&mut T` $\rightarrow$ `T`), and mutable-reference post-state tuple packing directly from parsed `syn` Rust syntax. It emits a sibling specification module (`generated/<Slug>/<Slug>.lean`) and byte-interval source map (`<Slug>.lean.map`) that import `«<Slug>».Funs` and `«<Slug>».Types` directly, apply three concrete textual compatibility patches to Aeneas output (`@[discriminant]` $\rightarrow$ `@[discriminant isize]`, `(show :` $\rightarrow$ `(show1 :`, and `noncomputable section` injection), promote `*_Template.lean` external files into live Lake roots, and enforce fail-closed checks when expected `Funs.lean` or `Types.lean` split files are omitted.
2. **Lake Ownership Evolution, Worker-Cache Disk Amplification, and Clean-Workspace Prebuilt Archive Reuse (`anneal/v1/src/{setup.rs,aeneas.rs}`, `anneal/v1/tests/integration.rs`):** Anneal V1's Lake integration evolved across four distinct ownership models:
   - *Stage 1 — Per-worker mutable clones (`d410c162d51977635ca5afac67d99a3b10327a94`, removed in PR #3305 / `f98458e7eaf54ff34b69e417ee34e79036f06547`):* An integration-test worker pool (`WorkerCacheGuard`, `acquire_worker_cache`, `smart_clone_cache`) scaled to $\lceil 1.5 \times \text{available\_parallelism}\rceil$ capped at $\lfloor\text{MemAvailable} / 2\text{ GiB}\rfloor$ and materialized per-worker copies of mutable `.git`/`.trace`/`.json`/`.hash`/`.log`/`lake.lock` metadata alongside symlinked `.olean` artifacts, causing a reported $\approx 100$-worker integration test run to consume $\approx 100\text{ GB}$ of disk space.
   - *Stage 2 — Pinning and `LAKE_ARTIFACT_CACHE=1` (`234131c52`, `8b193d733`):* Attempted shared path dependencies and symlinked `.lake/packages`, which still exposed user-global directories to concurrent Lake writes.
   - *Stage 3 — Local `file://` Git indirection and symlink materialization (PRs #3304/#3305/#3306, `9329ada1b`, `be6f199fd`):* Converted Aeneas and transitive Lean packages into local Git remotes so workspaces owned mutable checkouts while sharing Lake's content-addressed artifact cache, eliminating the worker pool at the cost of trace/manifest rewriting and an intermediate $\approx 5\text{ GB}$ ($\sim 5,000$ `.olean`) per-workspace copy stage before symlink optimization.
   - *Stage 4 — Direct read-only prebuilt archive with complete relative root manifest (PRs #3438, #3443, #3450, #3453):* Retained V1 consumes an immutable Exocrate-installed omnibus archive by generating a complete root `lake-manifest.json` whose Aeneas and transitive package `dir` entries are computed relative to the **final post-rename generated workspace**, stripping ambient `CI` so `precompileModules` matches archive traces, and invoking `lake --keep-toolchain --old build Generated Anneal` followed by `lake --keep-toolchain env lean --json`.
3. **Generated-Workspace Relocation and Interactive LSP Dependency-Invalidation Probes (`bd0956be95c5f798f0c0484921b9b9d1fc6e9988`):**
   - *Workspace Relocation Probe:* Moving a V1-generated Lean workspace to a different directory depth without regenerating its `lake-manifest.json` causes `lake --keep-toolchain --old --offline build Generated Anneal` to fail immediately (`exit 1`, `package directory ... not found`). Reseeding the relative `dir` entries for the moved path allows the offline build to complete (`exit 0`, `1688 jobs`, peak RSS $\approx 1.26\text{ GB}$), whereas moving the installed toolchain itself also requires rebinding the absolute path in `lakefile.lean`.
   - *Interactive LSP Dependency-Invalidation Probe:* In a live `lake --offline env lean --server` session over a V1-generated workspace (`relocate_probe::identity`), mutating the imported `Funs.lean` definition from `ok x` to `ok (U32.ofNat 0)`, rebuilding `.olean` artifacts (`lake --offline build Generated`), sending `workspace/didChangeWatchedFiles`, and bumping the proof document version via `textDocument/didChange` **still returned `"no goals"` (`goals: []`) for the now-invalid `rfl` proof**. Only spawning a fresh Lean server process (or batch `lean --json`) exposed the type mismatch (`exit 1`).
4. **Orthogonal Proof-Split Ergonomics, Duplicated Execution Reasoning, and the Unfinished `concat_slices` Challenge (`anneal/v1/src/Anneal.lean`, `anneal/v1/examples/{abs.rs,anatomy.rs,ptr_concat.rs}`):** V1's `Anneal.wp_prove_orthogonal` splits `Aeneas.Std.WP.spec m P` into an existential progress goal (`∃ y, m = .ok y`) and a conditional postcondition goal (`∀ y, m = .ok y → P y`). While this enables per-field postcondition diagnostics when execution gets stuck (`stuck_wps`), it forces complex proofs (`abs.rs`, `anatomy.rs`) to duplicate monadic unfolding/branch-splitting across `h_progress` and `Post` fields, renders `Post` field proofs vacuously true if `h_progress` is left open or admitted under `--allow-sorry`, creates a documentation contradiction around Aeneas's `progress` tactic (`06_tactics_and_tooling.md` vs. `anatomy.rs`), and leaves the multi-obligation `concat_slices` benchmark (`ptr_concat.rs`) as an unfinished `todo!()` challenge with three trusted `unsafe(axiom)` helpers.

---

## Applicability

This report applies to the historical retained Anneal V1 implementation and its pinned verification toolchain across the revisions recorded in `REPORT.json`:

| Subject / Component | Repository & Revision(s) | Scope & Role in This Report |
| :--- | :--- | :--- |
| Retained Anneal V1 (current main snapshot) | `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` | Primary source for the generated-Lean ABI (`scanner.rs`, `generate.rs`, `aeneas.rs`), clean-workspace prebuilt-archive consumption (`setup.rs`, `aeneas.rs`, `tests/integration.rs`), and non-applicability of the removed worker-cache pool. |
| Retained Anneal V1 (relocation, LSP, history, and proof-split snapshot) | `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988` (`cargo-anneal 0.1.0-alpha.24`) | Primary source and execution target for the generated-workspace relocation probe, interactive LSP dependency-invalidation probe, Lake integration chronology (`PRINCIPLES.md`, `DESIGN.md`, `anneal/v1/AGENTS.md`), and `wp_prove_orthogonal` / `concat_slices` analysis. |
| Historical Anneal V1 worker-cache pre-removal snapshot | `google/zerocopy@d410c162d51977635ca5afac67d99a3b10327a94` (`anneal/tests/integration.rs`, blob `55c9d14f8dbf01e1643cf67013ad24841177188c`) | Source of `WorkerCacheGuard`, `acquire_worker_cache`, `calculate_dynamic_lean_concurrency_limit`, `TestContext::new`, and `smart_clone_cache` immediately prior to deletion. |
| Historical Anneal V1 worker-cache removal commit | `google/zerocopy@f98458e7eaf54ff34b69e417ee34e79036f06547` (PR #3305, merged 2026-04-21) | Deletes the per-worker cache pool and records the $\approx 100$-worker / $\approx 100\text{ GB}$ integration-test disk amplification incident. |
| Historical Lake ownership & archive transition commits | `google/zerocopy`: PR #3297 (`aa4ef2afe4d36fcc078b8ce3fb6dac8fb21aa03b`, unmerged), PR #3304 (`69e77a55f1b80f051b9dd9555363d2e074c48d3a`), PR #3306 (`37d1fef927ec84a9086312ad1bb9840c205b0d87`), PR #3438 (`47d907d6fa27610a0900f075c0bec879777107a9`), PR #3443 (`11bf7f723639c90d6fa88b5dfd9333ec89c5f763`), PR #3450 (`f6aeb9bd14ee0196635f7e1e46bf0641b16950b6`), PR #3453 (`93cab05584dc15cf9f12236ec0ef24becd21beb0`), Issue #3668; plus historical commits `9b8b49e74`, `7ebe0e048`, `a918be80b`, `234131c52`, `8b193d733`, `9329ada1b`, `be6f199fd`, `fc1923372`, `e8a9861bc`, `3845553ae` | Document and implement the transition from worker clones to `LAKE_ARTIFACT_CACHE=1`, local `file://` Git remotes, and the Nix-built read-only omnibus archive. |
| Historical proof-split & Hermes provenance commits | `google/zerocopy`: `ad4252c93` (2026-03-07, named bounds), `c12d64763` (2026-03-08, orthogonal progress/correctness split), `79b93f211` (2026-03-08, hygienic `proof context`), `b2c394cfa`, `4bcec9bc9`, `dbb81cc77` | Provenance of `wp_prove_orthogonal`, named `Pre`/`Post` fields, and `proof context` under `tools/hermes/` prior to moving to `anneal/v1/`. |
| Pinned Aeneas Lean Backend | `AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4` | Defines `Aeneas.Std.Primitives.Result` (blob `5a73ea5bfae575baf2f26e1d86ea00768d1bccea`) and `Aeneas.Std.WP.spec` (blob `a599b2b6632fbfdfadbe3dcfb68ee17a6048be5d`) consumed by Anneal V1's generated specifications. |
| Pinned Lean 4 & Lake Toolchain | `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) | Executes `lake --keep-toolchain --old build`, `lake env lean --json`, and `lake --offline env lean --server` in the relocation and interactive dependency-invalidation probes. |

All findings describe the historical Anneal V1 prototype and its empirical behavior; they do not constitute current Anneal V2 design authority, which is governed by `anneal/PRINCIPLES.md` and `anneal/DESIGN.md`.

Basis: **source** + **documentation** + **execution** + **derived**.

---

## Findings

### 1. Anneal V1 Generated-Lean ABI and Aeneas Lowering Coupling

Retained Anneal V1 does not parse or introspect the Lean environment emitted by Aeneas to discover translated declaration names, argument orders, or return types. Instead, `anneal/v1/src/{scanner.rs,generate.rs,aeneas.rs}` independently predicts Aeneas's output surface from `syn`-parsed Rust syntax and emits Lean specifications that must elaborate directly against Aeneas's generated modules (`support/anneal-v1-generated-lean-abi-main-41f5b37/generated-lean-abi.json`, `support/anneal-v1-generated-lean-abi-main-41f5b37/source-map.json`).

#### 1.1 Cross-Stage Artifact Slug and Split-File Module Layout (`scanner.rs`, `aeneas.rs`)

`AnnealArtifact::artifact_slug` (`anneal/v1/src/scanner.rs`, blob `44b66417a827192b87d4cad3e62421e8ca497d28`) constructs a deterministic, Lean-compatible identifier by converting the Cargo package name and target name to `PascalCase` and appending a 16-hex-character SHA-256 suffix derived from the package name, target name, target kind, and manifest path:

$$\text{Slug} = \text{PascalCase}(\text{pkg\_name}) \mathbin{\Vert} \text{PascalCase}(\text{target\_name}) \mathbin{\Vert} \operatorname{hex}_{16}\!\bigl(\operatorname{SHA256}(\text{pkg\_name}, \text{target\_name}, \text{target\_kind}, \text{manifest\_path})\bigr)$$

Anneal invokes Aeneas with `-backend lean -dest generated/<Slug> -split-files -abort-on-error` (`anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`), binding the entire cross-stage directory layout to `<Slug>`:

```text
llbc/<Slug>.llbc                           # Charon LLBC input
generated/<Slug>/Funs.lean                 # Aeneas translated functions
generated/<Slug>/Types.lean                # Aeneas translated types & traits
generated/<Slug>/FunsExternal.lean         # Promoted from FunsExternal_Template.lean when emitted
generated/<Slug>/TypesExternal.lean        # Promoted from TypesExternal_Template.lean when emitted
generated/<Slug>/<Slug>.lean               # Anneal-generated Pre/Post/spec module
generated/<Slug>/<Slug>.lean.map           # Byte-interval Rust <-> Lean diagnostic sidecar map
```

Every Anneal-generated `<Slug>.lean` file begins with a fixed import preamble (`generate.rs::generate_artifact`, blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`):

```lean
import Anneal
import Aeneas.Std.Scalar.Core
import «<Slug>».Funs
import «<Slug>».Types

open Aeneas Aeneas.Std Result
noncomputable section
inject_builtins

namespace <rust_target_name_with_underscores>
```

Because there is no intermediate adapter module, every declaration name and signature emitted later in `<Slug>.lean` must match `«<Slug>».Funs` and `«<Slug>».Types` directly. The preserved golden `anneal/v1/tests/fixtures/expand_output/expected-all.stdout` (blob `b4934dc041ad81cca05eeb4aa94a8e22ae39a66f`) demonstrates both halves in a single file: Aeneas emits `namespace expand_output` containing `def foo : Result Unit := do ok ()`, and Anneal imports the slugged `Funs` and `Types` modules, enters `namespace expand_output`, defines `namespace foo`, and proves `theorem spec : Aeneas.Std.WP.spec (foo) (fun ret_ => Post) := by ...`.

Basis: **source** (`anneal/v1/src/scanner.rs`, `anneal/v1/src/generate.rs`, `anneal/v1/src/aeneas.rs`) + preserved **execution** golden (`tests/fixtures/expand_output/expected-all.stdout`).

#### 1.2 Predicted Namespace Hierarchy, Type Rendering (`map_type`), and Trait Dictionaries (`generate.rs`)

Anneal V1 reconstructs Aeneas identifiers and types from Rust syntax via three independent translation rules in `anneal/v1/src/generate.rs` (blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`):

1. **Function & Method Namespace Prediction (`NamingContext`):**
   - Free functions use their Rust identifier directly inside the scanned Rust module path (dropping the leading `crate` segment).
   - Inherent `impl` methods insert the implementing type's path segment before the method identifier.
   - Fully qualified helper references passed to proof tactics (`verify_is_valid`, `verify_user_bound`) are constructed as `_root_.<crate_ident>.<namespace_path>.<fn_ident>`.
   - Each annotated function creates a nested `namespace <fn_ident>` containing `Pre`, `Post`, and `theorem spec` (or `axiom spec` for `unsafe(axiom)` functions).

2. **Independent Rust-to-Lean Type Renderer (`generate.rs::map_type`):**

   | Parsed Rust Type (`syn::Type`) | Predicted Lean Type Emitted by `map_type` | ABI Coupling & Fallback Notes |
   | :--- | :--- | :--- |
   | `u8`, `u16`, `u32`, `u64`, `u128`, `usize` | `Std.U8`, `Std.U16`, `Std.U32`, `Std.U64`, `Std.U128`, `Std.Usize` | Must match Aeneas scalar wrapper names in `Aeneas.Std.Scalar`. |
   | `i8`, `i16`, `i32`, `i64`, `i128`, `isize` | `Std.I8` through `Std.I128` and `Std.Isize` | Signed scalar wrappers in `Aeneas.Std`. |
   | `bool` | `Bool` | Direct Lean `Bool`. |
   | `&T`, `&mut T` | Mapped recursively as `T` (reference wrapper erased) | `extract_args_metadata` separately records `is_mut_ref = true` only for syntactic `&mut T` (never for `mut x: T` by-value bindings). |
   | `*mut T`, `*const T` | `MutRawPtr T`, `ConstRawPtr T` | Raw pointer wrappers defined in `Anneal.lean` / `Aeneas.Std`. |
   | `[T]` / `&[T]` | `Slice T` | Aeneas slice model. |
   | `[T; N]` | `Array T N` | Aeneas fixed-size array model. |
   | `!` (never type) | `Never` | Aeneas uninhabited return type. |
   | `(T1, T2, ...)` / `()` | `(T1 × T2 × ...)` / `Unit` | Lean product types / `Unit`. |
   | Path `a::b::Foo<G1, G2>` | `a.b.Foo G1 G2` | Joined with `.` and applied to recursively rendered generic arguments. |
   | Unrecognized / unsupported `syn::Type` | `MatchError` | Fallback sentinel; `is_unit_return` treats both `Unit` and `MatchError` as having no ordinary return value, so any unsupported return type that bypasses scanner validation silently drops `ret` from `Post`. |

3. **Explicit Trait-Dictionary Lowering (`extract_generic_params`):**
   - `Sized` bounds are special-cased to emit the Anneal typeclass binder `[Anneal.Sized T]` (which is omitted from explicit Aeneas function call arguments).
   - Every other Rust trait bound `T: Trait<Args>` is lowered into an **explicit dictionary parameter** by appending `Inst` to the base trait identifier (`(<Trait>Inst : <Trait> T <Args>)`) and passing `<Trait>Inst` positionally to the predicted Aeneas function call. As noted in `generate.rs` comments referencing Aeneas's `Clause0Inst`/`TraitInst` conventions, any change in Aeneas's dictionary naming or parameter ordering breaks generated Anneal specs even when LLBC translation succeeds.
   - Annotated Rust types emit `instance : Anneal.IsValid <PredictedType>` against `Types.lean`, and annotated `unsafe trait` items emit a nested `class Safe (<Trait>Inst : <PredictedTraitApp>) : Prop` wrapper (`generate_type`, `generate_trait`).

Basis: **source** (`anneal/v1/src/generate.rs`).

#### 1.3 Reference Erasure, Mutable Post-State Tuple Packing, and `Aeneas.Std.WP.spec`

In pinned Aeneas (`AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`), `backends/lean/Aeneas/Std/Primitives.lean` (blob `5a73ea5bfae575baf2f26e1d86ea00768d1bccea`) defines the monadic evaluation carrier:

```lean
inductive Result (α : Type u) where
  | ok (v : α)
  | fail (e : Error)
  | div
```

and `backends/lean/Aeneas/Std/WP.lean` (blob `a599b2b6632fbfdfadbe3dcfb68ee17a6048be5d`) defines `Aeneas.Std.WP.spec (m : Result α) (P : α → Prop) : Prop`, which holds if and only if `m` evaluates to `Result.ok v` for some `v` satisfying `P v` (both `.fail` and `.div` make `WP.spec` false).

Because Aeneas functionalizes mutable borrows by returning updated referent values inside `Result.ok`, `generate.rs::generate_function` predicts the exact tuple shape of `Result`'s payload from the Rust function signature's return type and its syntactic `&mut` parameters (`x`, `y`, ...):

| Ordinary Return Value (`!is_unit_return`) | Count of `&mut` Parameters | Predicted `Result` Payload Destructuring in `WP.spec` Continuation | `Post` Output Binders & Auto-Injected `IsValid` Fields |
| :--- | ---: | :--- | :--- |
| No (`()` or `MatchError`) | `0` | `fun _ => Post <args>` | None (`Post` takes only input `<args>`). |
| Yes (`RetTy`) | `0` | `fun ret_ => let ret := ret_; Post <args> ret` (or `fun ret_ => Post <args> ret_`) | `(ret : RetTy)` + `h_ret_is_valid : Anneal.IsValid.isValid ret`. |
| No (`()`) | `1` (`x: &mut X`) | `fun ret_ => let x' := ret_; Post <args> x'` | `(x' : X)` + `h_x'_is_valid : Anneal.IsValid.isValid x'`. |
| No (`()`) | $k \ge 2$ (`x`, `y`, ...) | `fun ret_ => let (x', y', ...) := ret_; Post <args> x' y' ...` | `(x' : X) (y' : Y) ...` + `h_<arg>'_is_valid` for each. |
| Yes (`RetTy`) | $k \ge 1$ (`x`, ...) | `fun ret_ => let (ret, x', ...) := ret_; Post <args> ret x' ...` | `(ret : RetTy) (x' : X) ...` + `h_ret_is_valid` and `h_<arg>'_is_valid`. |

The preserved regression fixture `anneal/v1/tests/fixtures/extern_never_verified/out.txt` (blob `9cf7a9e663c0dc77597cbd007bc8917c87e6f9e2`) captures the `(ret, x')` case in concrete generated Lean:

```lean
Aeneas.Std.WP.spec (die x) (fun ret_ =>
  let (ret, x') := ret_
  Post x ret x')
```

with the corresponding correctness branch introducing `rintro ⟨ret, x'⟩ h_returns`.

Basis: **source** (`anneal/v1/src/generate.rs`, `Aeneas/Std/Primitives.lean`, `Aeneas/Std/WP.lean`) + preserved **execution** artifact (`tests/fixtures/extern_never_verified/out.txt`).

#### 1.4 Textual Compatibility Shims, External Template Promotion, Fail-Closed Split-File Checks, and `.lean.map` Sidecars (`aeneas.rs`, `generate.rs`)

`anneal/v1/src/aeneas.rs` (blob `9b4618a20938315afc290744bbdfa498848620f4`) enforces four post-processing rules between Aeneas invocation and Lake compilation:

1. **Concrete Textual Compatibility Shims (`patch_discriminants`, `patch_funs`):**
   - *Discriminant attribute repair (`Types.lean`):* Replaces bare `@[discriminant]` with `@[discriminant isize]` because pinned Lean/Aeneas requires an integer type parameter on `@[discriminant]`.
   - *Keyword collision repair (`Funs.lean`):* Replaces `(show :` with `(show1 :` when Aeneas emits a parameter named `show` without escaping the Lean tactic keyword.
   - *Bytecode compiler bypass (`Funs.lean`):* Inserts `noncomputable section` immediately after the import block of `Funs.lean` so Lean's bytecode compiler does not reject translated functions that call `opaque` / `axiom` external definitions.
2. **External Template Promotion (`run_aeneas`):**
   - When Aeneas emits `FunsExternal_Template.lean` or `TypesExternal_Template.lean` (for opaque/foreign functions or types), Anneal copies each template to `FunsExternal.lean` / `TypesExternal.lean` if absent, registers those modules as Lake roots in `lakefile.lean`, and imports them in `Generated.lean`.
3. **Fail-Closed vs. Benign Missing Split-File Checks (`run_aeneas`):**
   - Aeneas with `-split-files` omits `Funs.lean` when no functions are translated and omits `Types.lean` when no types are translated.
   - If `Funs.lean` (or `Types.lean`) is missing and Anneal's scanner found **zero** corresponding function/impl (or type/trait) items in the artifact, Anneal writes an empty file so `<Slug>.lean`'s fixed `import «<Slug>».Funs` / `Types` header still elaborates.
   - If `Funs.lean` (or `Types.lean`) is missing but Anneal's scanner **did** find function/impl (or type/trait) items, Anneal fails closed and aborts verification. `anneal/v1/tests/fixtures/missing_output/expected.stderr` (blob `5255829806d2be2cadf5c87060f17e3b12d9d7cf`) preserves the exact fail-closed diagnostic for a silent Aeneas translation failure on `Funs.lean`.
4. **Parallel Byte-Interval Diagnostic Sidecar (`<Slug>.lean.map`):**
   - `LeanBuilder` (`generate.rs`) emits `<Slug>.lean.map` containing `SourceMapping` entries with generated-Lean byte intervals, original Rust file/byte spans, and a `MappingKind` (`Source` for user proof lines, `Synthetic` anchoring the `spec` theorem identifier to the Rust `fn` span, or `Keyword` for redirecting warnings like `"declaration uses 'sorry'"`).
   - During `run_lake` / `resolve_mapping` (`aeneas.rs`), Anneal runs `lake --keep-toolchain env lean --json` on each `<Slug>.lean`, converts Lean line/column diagnostics to byte offsets, and maps overlapping spans back to Rust compiler-style diagnostics. This sidecar is a diagnostic provenance map, not semantic evidence that Aeneas's translated model matches Rust semantics.

Basis: **source** (`anneal/v1/src/aeneas.rs`, `anneal/v1/src/generate.rs`) + preserved **execution** artifact (`tests/fixtures/missing_output/expected.stderr`).

---

### 2. Evolution of V1 Lake Integration, Worker-Cache Disk Amplification, and Clean-Workspace Prebuilt Archive Reuse

#### 2.1 Four-Stage Chronology of V1 Lake Ownership (`support/anneal-v1-integration-test-disk-amplification-f98458e/source-map.json`)

Across its development history (`anneal/PRINCIPLES.md`, `anneal/DESIGN.md`, `anneal/v1/AGENTS.md`, Issue #3668), Anneal V1 iterated through four distinct architectures for sharing prebuilt Aeneas and Mathlib Lean artifacts across verification runs and parallel integration tests:

| Stage & Era | Representative Commits & PRs (`google/zerocopy`) | Ownership & Materialization Mechanism | Operational Problem Addressed & Failure Mode Exposed |
| :--- | :--- | :--- | :--- |
| **Stage 1: Per-Worker Smart-Clone Pool** (April 2026) | `9b8b49e74`, `7ebe0e048`, `a918be80b`, pre-removal snapshot `d410c162d51977635ca5afac67d99a3b10327a94` (`anneal/tests/integration.rs`, blob `55c9d14f8dbf01e1643cf67013ad24841177188c`); removed in PR #3305 (`f98458e7eaf54ff34b69e417ee34e79036f06547`) | Allocated persistent `target/worker_caches/<worker>/` directories guarded by `flock` (`WorkerCacheGuard`). Cloned `aeneas/backends/lean` and `lean_lake` per worker via `smart_clone_cache` and symlinked test `.lake` to `worker_cache.lean_lake`. | Isolated concurrent test writers from mutating a shared global `.lake` directory, but multiplied mutable metadata/directory trees by host concurrency ($\approx 100$ parallel workers consumed $\approx 100\text{ GB}$ of disk in PR #3305). |
| **Stage 2: Package Pinning & `LAKE_ARTIFACT_CACHE=1`** | `234131c52`, `8b193d733` (`anneal/src/{setup.rs,aeneas.rs}`), unmerged exploratory PR #3297 (`aa4ef2afe4d36fcc078b8ce3fb6dac8fb21aa03b`) | Built `Mathlib`, `Aeneas`, and `AeneasMeta` with `LAKE_ARTIFACT_CACHE=1`; patched `lake-manifest.json` and symlinked `.lake/packages` into each generated workspace. | Reduced network re-downloads, but treating installed Aeneas as a shared path dependency with symlinked `.lake/packages` still exposed shared directories to concurrent Lake writes and races. |
| **Stage 3: Local `file://` Git Remotes & Symlink Materializer** | PR #3304 (`69e77a55f1b80f051b9dd9555363d2e074c48d3a`), PR #3305 (`f98458e7eaf54ff34b69e417ee34e79036f06547`), PR #3306 (`37d1fef927ec84a9086312ad1bb9840c205b0d87`), `9329ada1b`, `be6f199fd` (merges `88393fcf1`, `64bd6d6f1`, `3b29d25ae`) | Initialized installed Aeneas and transitive Lean packages as local `file://` Git repositories (`git "file://..." @ "main"`) backed by a shared Lake cache; `9329ada1b` copied prebuilt package trees and rewrote `.trace` paths; `be6f199fd` replaced full copying with a symlink materializer and marked installed packages read-only. | Allowed each workspace to own mutable checkout state while deleting the `worker_caches` pool. However, intermediate full package copying (`9329ada1b` / `be6f199fd`, Issue #3668) copied $\approx 5\text{ GB}$ ($\sim 5,000$ `.olean` files) per workspace before symlink optimization, and required fragile manifest/trace rewriting. |
| **Stage 4: Read-Only Omnibus Archive + Complete Relative Root Manifest** | PR #3438 (`47d907d6fa27610a0900f075c0bec879777107a9`), PR #3443 (`11bf7f723639c90d6fa88b5dfd9333ec89c5f763`), PR #3450 (`f6aeb9bd14ee0196635f7e1e46bf0641b16950b6`), PR #3453 (`93cab05584dc15cf9f12236ec0ef24becd21beb0`), `fc1923372`, `e8a9861bc`, `3845553ae`; current `41f5b37...` and `bd0956b...` | Consumes a Nix-built Exocrate omnibus archive (`setup.rs`) directly in place. Emits a complete root `lake-manifest.json` with relative path entries for Aeneas and all transitive packages (`aeneas.rs`), strips `CI`, and runs `lake --keep-toolchain --old build Generated Anneal`. | Eliminates per-worker and per-workspace dependency trees and trace rewriting. Requires a conjunctive 5-part reuse contract (prepared outputs, normalized mtimes, complete manifest, relative path resolution at final workspace location, and `--old` with matching `CI` env). |

Basis: **source** + **documentation** + **derived**.

#### 2.2 Anatomy of the Stage 1 Worker-Cache Disk Amplification (`d410c162d51977635ca5afac67d99a3b10327a94` $\rightarrow$ `f98458e7eaf54ff34b69e417ee34e79036f06547`)

In `google/zerocopy@d410c162d51977635ca5afac67d99a3b10327a94` (`anneal/tests/integration.rs`, blob `55c9d14f8dbf01e1643cf67013ad24841177188c`), every non-mock integration test called `TestContext::new`, which acquired an exclusive `flock`-backed `WorkerCacheGuard` over `target/worker_caches/<worker_id>/`:

1. **Concurrency-Proportional Pool Sizing (`acquire_worker_cache`, `calculate_dynamic_lean_concurrency_limit`):**
   - The pool size was computed as:
     $$N_{\text{workers}} = \min\!\left(\left\lceil 1.5 \times \operatorname{available\_parallelism}() \right\rceil,\; \left\lfloor \frac{\text{MemAvailable}}{2\text{ GiB}} \right\rfloor\right)$$
     falling back to $4$ workers if `/proc/meminfo` was unreadable. On high-core-count, high-memory hosts, this created roughly $100$ persistent worker directories.
2. **Selective Copy vs. Symlink Split (`smart_clone_cache`):**
   - On first use of worker $i$, `acquire_worker_cache` initialized two persistent directory trees under `target/worker_caches/<i>/`: `aeneas/backends/lean` and `lean_lake`.
   - `smart_clone_cache` did **not** deep-copy `.olean` binaries; it symlinked `.git/objects` and ordinary immutable build files back to the installed toolchain, while **physically copying** every directory entry and every file classified as potentially mutable metadata:
     - all files under `.git/` (outside `.git/objects`);
     - all files with extensions `.trace`, `.json`, `.hash`, or `.log`; and
     - `lake.lock`.
   - `TestContext::new` then copied `lake-manifest.json`, injected Aeneas, and symlinked the temporary test sandbox's `.lake` directory to `worker_cache.lean_lake`.
3. **Operational Incident and Architectural Lesson (PR #3305):**
   - Commit `f98458e7eaf54ff34b69e417ee34e79036f06547` (PR #3305) deleted `WorkerCacheGuard`, `acquire_worker_cache`, `calculate_dynamic_lean_concurrency_limit`, and `smart_clone_cache`, recording that a specific integration-test run with approximately 100 parallel worker threads and caches consumed approximately **100 GB of disk space**.
   - Even when heavyweight `.olean` artifacts are symlinked, replicating the directory hierarchy, Git metadata, and thousands of Lake `.trace`/`.json`/`.hash` files per concurrent worker scales disk consumption linearly with host parallelism.

Basis: **source** (`d410c162d51977635ca5afac67d99a3b10327a94`) + **documentation** (PR #3305 / `f98458e7eaf54ff34b69e417ee34e79036f06547`, PR #3297, Issue #3668).

#### 2.3 Stage 4 Clean-Workspace Prebuilt Archive Contract (`41f5b37afe7060fd9fe08c00b200672cd76d77b9`)

At `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`support/anneal-v1-clean-workspace-prebuilt-archive-41f5b37/source-map.json`), Anneal V1 strictly separates the **immutable installed toolchain archive** (`anneal/v1/src/setup.rs`, blob `32216cedf11c5d6d4b5a4618d8d7bf2578e44b4d`) from the **mutable generated consumer workspace** (`anneal/v1/src/aeneas.rs`, blob `9b4618a20938315afc290744bbdfa498848620f4`):

1. **Five-Part Conjunctive Reuse Contract:**
   Reusing prebuilt `.olean` artifacts from the read-only archive without triggering package reconfiguration or writes into the archive requires all five conditions simultaneously:
   - **Prepared dependency outputs:** The Exocrate archive contains pre-elaborated `.olean` and `.trace` files for Aeneas, Mathlib, Qq, Batteries, Aesop, Quote4, ProofWidgets, LeanSearchClient, Plausible, and Cli.
   - **Normalized input timestamps (PR #3443, `11bf7f723639c90d6fa88b5dfd9333ec89c5f763`):** Archive source and configuration file mtimes are normalized during archive creation so prepared build outputs compare as newer under Lake's `--old` timestamp check.
   - **Complete relative root `lake-manifest.json` (`generated_lake_manifest` in `aeneas.rs`, PR #3450 `f6aeb9bd14ee0196635f7e1e46bf0641b16950b6`):** `generated_lake_manifest` reads the installed Aeneas `lake-manifest.json`, converts Aeneas itself and every transitive dependency into `path` package entries, marks transitive packages `inherited = true`, strips archive-internal fields, and computes each `dir` relative to the **final post-rename generated workspace path**. Without a complete root manifest, Lake attempts to reconfigure path dependencies and write lock/config files (`lake.lock`, `.lake/config`) into read-only archive directories.
   - **Staging-to-Final Path Rebasing (`aeneas.rs:L314-L380`):** Because V1 generates the workspace inside a temporary sibling directory and swaps it into the final `lean/` path (preserving any prior workspace-local `.lake` directory across reruns), `generated_lake_manifest` canonicalizes the final workspace's **parent** directory and appends the target leaf name before computing relative `dir` paths. A unit test (`aeneas.rs:L989`) verifies that these relative paths resolve to Aeneas, Mathlib, and Qq after the final directory is created.
   - **Matching `CI` Environment & `--old` Invocation (`aeneas.rs:L518, L712`):** V1 explicitly strips the `CI` environment variable before invoking `lake --keep-toolchain --old build Generated Anneal` because Aeneas's `lakefile.lean` toggles `precompileModules` based on `CI`; an ambient `CI=true` in the consumer environment invalidates archive traces built without `CI` and causes Lake to attempt rebuilding inside the read-only archive.
2. **Checked-In Clean-Workspace Regression (`anneal/v1/tests/integration.rs`, blob `8fc6f6b9b4d4785e532e0647466a2e2373fe709a`, PR #3453 `93cab05584dc15cf9f12236ec0ef24becd21beb0`):**
   - `run_archive_lake_cache_reuse_test` $\rightarrow$ `assert_archive_lake_cache_reuse` first calls `assert_no_write_bits(&aeneas_root)`, recursively verifying that no ordinary non-symlink file or directory under the installed Aeneas tree has any write permission bit set.
   - It then creates a brand-new temporary `generated-workspace/` with **no preexisting `.lake` directory**, writes `lean-toolchain`, `generated/Generated.lean` (`import Aeneas`), a minimal `lakefile.lean`, and the complete relative `lake-manifest.json` (`write_relative_archive_manifest`), and executes both production consumer phases:
     ```bash
     lake --keep-toolchain --old build Generated
     lake --keep-toolchain env lean --json generated/Generated.lean
     ```

Basis: **source** (`anneal/v1/src/{setup.rs,aeneas.rs}`, `anneal/v1/tests/integration.rs`) + **documentation** (PRs #3438, #3443, #3450, #3453, Issue #3668).

---

### 3. Executed Relocation and Interactive LSP Dependency-Invalidation Probes (`bd0956be95c5f798f0c0484921b9b9d1fc6e9988`)

#### 3.1 Generated-Workspace Relocation Execution Probe (`support/anneal-v1-generated-workspace-relocation-probe/v1-execution/`)

To test whether a V1-generated Lean workspace can be relocated after generation (`google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`, `cargo-anneal 0.1.0-alpha.24`, `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), `cargo-anneal generate` was run on a one-function Rust library (`relocate_probe::identity(x: u32) -> u32`, `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/fixture-lib.rs` and `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/fixture-Cargo.toml`). Because the local scratch Aeneas manifest initially contained Git package entries, it was temporarily converted to local path entries to satisfy `generated_lake_manifest`.

1. **Initial Generation (`generate.stdout`, `generate.stderr`, `moved-lakefile.lean`):**
   - `cargo-anneal generate` succeeded, emitting the generated Lean workspace under `<target>/anneal/<hash>/lean` with a `lakefile.lean` containing an **absolute path** `require aeneas from "<toolchain_dir>/aeneas/backends/lean"` (`support/anneal-v1-generated-workspace-relocation-probe/v1-execution/moved-lakefile.lean`) and a `lake-manifest.json` containing **relative `dir` paths** (six parent-directory steps up to `toolchain/...`) computed for that exact directory depth.
2. **Unmodified Move Fails Closed Before Build (`stale-move.exit`, `stale-move.stderr`):**
   - Moving the generated `lean` workspace directory to a shallower path (`move-parent/moved-lean`) without regenerating `lake-manifest.json` and running `lake --keep-toolchain --old --offline build Generated Anneal` failed immediately (`exit 1`, `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/stale-move.exit`):
     ```text
     error: package directory '<wrong_resolved_path>/aeneas/backends/lean' not found
     ```
     (`support/anneal-v1-generated-workspace-relocation-probe/v1-execution/stale-move.stderr`).
3. **Reseeding Relative Manifest Paths Succeeds for Workspace-Only Move (`reseeded-manifest.json`, `reseeded-move.exit`, `reseeded-move.stdout`, `reseeded-move.stderr`):**
   - Recomputing the 10 relative `dir` entries in `lake-manifest.json` (two parent-directory steps up to `toolchain/aeneas/backends/lean` and `toolchain/aeneas/backends/lean/.lake/packages/<pkg>`, preserved in `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/reseeded-manifest.json`) while keeping the toolchain at its original location allowed `lake --keep-toolchain --old --offline build Generated Anneal` to succeed (`exit 0`, `Build completed successfully (1688 jobs)`, peak process-tree RSS $\approx 1.26\text{ GB}$, `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/reseeded-move.exit` and `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/reseeded-move.stdout`).
   - Because `moved-lakefile.lean` embeds an absolute path to the installed Aeneas toolchain in `require aeneas from ...`, relocating the **toolchain/archive** (rather than only the generated workspace) requires regenerating or rebinding both `lakefile.lean` and `lake-manifest.json`.

Basis: **execution** + **source** (`anneal/v1/src/aeneas.rs` at `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`).

#### 3.2 Interactive LSP Dependency-Invalidation Execution Probe (`support/anneal-v1-interactive-dependency-invalidation/`)

While retained V1 did not ship an interactive editor/LSP bridge (placing Rust-editor goal state under "Future Work" in `anneal/v1/docs/design/design.md:L499`), an execution probe (`support/anneal-v1-interactive-dependency-invalidation/replay-query.py`, full transcript in `support/anneal-v1-interactive-dependency-invalidation/query-transcript.json`) tested how a live `lake --offline env lean --server` process over the V1-generated `relocate_probe` workspace (`support/anneal-v1-interactive-dependency-invalidation/fixture/`) behaves across document edits and an out-of-band rebuild of an imported generated module (`Funs.lean`):

| Step in `query-transcript.json` | Action Performed on Workspace / LSP Server (`lake --offline env lean --server`) | `Funs.lean` SHA-256 (`identity` body) | Observed LSP / Batch Response |
| :--- | :--- | :--- | :--- |
| **1. Initial Open (`Probe-v1.lean`, version 1)** | `textDocument/didOpen` with `apply And.intro` on `WP.spec (identity x) ...` (`support/anneal-v1-interactive-dependency-invalidation/Probe-v1.lean`); query `$/lean/plainGoal` before and after `apply And.intro`. | `27b02d8843009c22cbd74fb430b3ccc3dc9a25c7c515aa373f4f62f6e65c69eb` (`ok x`) | Before tactic: 1 conjunction goal. After tactic: 2 subgoals (`case left`, `case right`). Batch control exits `1` with matching unsolved goals. |
| **2. In-Memory Proof Completion (`Probe-v2.lean`, version 2)** | `textDocument/didChange` (version 2) replacing proof with `exact ⟨rfl, trivial⟩` (`support/anneal-v1-interactive-dependency-invalidation/Probe-v2.lean`); `$/lean/waitForDiagnostics` (version 2); query `$/lean/plainGoal`. | `27b02d884300...` (`ok x`) | Diagnostics empty; `$/lean/plainGoal` returns `"no goals"` (`goals: []`). Batch `lean --json` control exits `0`. |
| **3. Dependency Mutation & Rebuild + Same-Server Re-Query (version 3)** | Mutate `Funs.lean` so `identity x := ok (U32.ofNat 0)` (`support/anneal-v1-interactive-dependency-invalidation/dependency-mutated-Funs.lean`); run `lake --offline build Generated` (`exit 0`); send `workspace/didChangeWatchedFiles` for `Funs.lean`; send `textDocument/didChange` (version 3) with `Probe-v2.lean`; wait for version 3 diagnostics and query `$/lean/plainGoal`. | `935d3ca2e5d5c5add0ec4e42c46f8606fa7b244215930c1061325b837d272149` (`ok (U32.ofNat 0)`) | **Stale acceptance:** Same Lean server process emits **zero error diagnostics** and `$/lean/plainGoal` still returns **`"no goals"` (`goals: []`)** after `rfl`! |
| **4. Fresh Server & Batch Verification on Mutated Dependency** | Spawn a **new** `lake --offline env lean --server` process and open `Probe-v2.lean` (and run batch `lake --offline env lean --json`, `support/anneal-v1-interactive-dependency-invalidation/batch-after-dependency.json`). | `935d3ca2e5d5...` (`ok (U32.ofNat 0)`) | **Rejected (`exit 1`):** Fresh server and batch run both report type mismatch at `rfl` (`U32.ofNat 0 = x` fails) and return the unsolved conjunction goal. |

**Architectural Implication:** In Lean 4 (`v4.30.0-rc2`), imported `.olean` modules are mapped into the server's environment at file initialization (`parseHeader` / `importModules`). Rebuilding an imported `.olean` on disk, sending `workspace/didChangeWatchedFiles`, and incrementing the open proof document's `version` via `didChange` does **not** reload the imported environment inside an existing worker process. Any interactive proof-cache or agent-facing goal-query adapter must include the **transitive imported module/`.olean` content hashes** in its validity key and restart or invalidate the Lean server worker whenever a generated dependency (`Funs.lean`, `Types.lean`) changes.

Basis: **execution** (`support/anneal-v1-interactive-dependency-invalidation/query-transcript.json`, `batch-after-dependency.json`, `baseline-build.log`, `replay-query.py`) + **derived** cache-key requirement.

---

### 4. Orthogonal Proof-Split (`wp_prove_orthogonal`) Ergonomics, Vacuity Boundaries, and the Unfinished `concat_slices` Challenge

#### 4.1 The `wp_prove_orthogonal` Split and Duplicated Execution Reasoning (`Anneal.lean`, `abs.rs`, `anatomy.rs`)

Introduced in `c12d64763` (2026-03-08, following named bounds in `ad4252c93` and hygienic `proof context` in `79b93f211`), `anneal/v1/src/Anneal.lean:L62` (at `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`) factors `Aeneas.Std.WP.spec m P` into two independent premises:

```lean
theorem wp_prove_orthogonal {α : Type u} (m : Result α) (P : α → Prop)
    (h_progress : ∃ y, m = .ok y)
    (h_post : ∀ y, m = .ok y → P y) :
    Aeneas.Std.WP.spec m P
```

When `generate.rs:L453` emits `theorem spec`, it applies `Anneal.wp_prove_orthogonal` (`anneal/v1/docs/design/named_bounds.md:L87`):
- **Branch 1 (`h_progress`):** Discharged either by a user-supplied `proof (h_progress)` block or by the default `eval_progress` tactic (`Anneal.lean:L68`), which attempts unfolding, `split`, `⟨_, rfl⟩`, and `simp`, falling back to `sorry` only when `Anneal.allow_sorry` is enabled (`--allow-sorry`).
- **Branch 2 (`h_post`):** Introduces the output value(s) and `h_returns : m = .ok y`, destructures `h_req : Pre ...`, injects any user `proof context` block (`have`/`let` bindings in term mode), and constructs the `Post` structure record where each field `h_i` is proved by its explicit `proof (h_i)` script or by `autoParam` tactics (`verify_is_valid` / `verify_user_bound`).

**Observed Benefit vs. Observed Ergonomic & Soundness Costs:**
1. *Independent Field Diagnostics (`stuck_wps`):* In `anneal/v1/tests/fixtures/stuck_wps/` (`source/crates/app/src/lib.rs`, `anneal.toml`, `expected.stderr`), running `verify --allow-sorry` allows individual `Post` fields to elaborate and report localized errors even when execution progress (`h_progress`) is stuck on an opaque call or complex loop.
2. *Duplicated Symbolic Execution Across Branches (`abs.rs`, `anatomy.rs`):* Because `h_progress` only exports the bare existence witness `∃ y, m = .ok y` (and `h_post` only receives the unreduced equality `h_returns : m = .ok ret`), intermediate symbolic execution facts (branch conditions, overflow bounds, intermediate call results) are **not shared** between `h_progress` and `h_post`:
   - In `anneal/v1/examples/abs.rs:L1`, the identical multi-step `unfold abs; split <;> intros <;> ... <;> scalar_tac` branch and arithmetic deduction must be written in `h_progress` and repeated inside each of `h0`, `h1`, and `h2`.
   - In `anneal/v1/examples/anatomy.rs:L53-L148`, `proof context` shares setup among the `Post` fields, but `h_progress` must separately reconstruct layout bounds and `fast_add` evaluation, manually converting `fast_add`'s `WP.spec` theorem into an existential `.ok` equality via `Aeneas.Std.WP.spec_imp_exists`.
3. *Contradiction in V1 Tactic Guidance (`06_tactics_and_tooling.md` vs. `anatomy.rs`):* `anneal/v1/docs/agent/06_tactics_and_tooling.md:L24` (and `named_bounds.md`) advises proof authors to use Aeneas's `progress` tactic inside explicit `proof (h_progress)` blocks. However, as `anneal/v1/examples/anatomy.rs:L141` explicitly documents, Aeneas's `progress` tactic operates on `Aeneas.Std.WP.spec` goals, **not** on the existential equality goal `∃ y, m = .ok y` produced by `wp_prove_orthogonal`—forcing authors to manually chain `.ok` equalities and `spec_imp_exists`.
4. *Conditional Vacuity of `h_post` When `h_progress` Is Open or Admitted:* Because `∀ y, m = .ok y → P y` is vacuously true whenever `m` diverges (`.div`) or panics/fails (`.fail e`), a locally green `Post` field proof provides **zero unconditional guarantee** unless `h_progress : ∃ y, m = .ok y` is also proved without `sorry` (`anneal/v1/docs/agent/04_specifications_and_syntax.md:L294`, `05_proof_architecture.md:L63`).

Basis: **source** (`anneal/v1/src/{Anneal.lean,generate.rs,aeneas.rs}`, `anneal/v1/examples/{abs.rs,anatomy.rs}`, `anneal/v1/tests/fixtures/{stuck_wps,named_bounds_lean_failures}/`) + **documentation** (`anneal/v1/docs/`).

#### 4.2 The Unfinished `concat_slices` Benchmark (`anneal/v1/examples/ptr_concat.rs`)

`anneal/v1/examples/ptr_concat.rs:L1-L60` at `bd0956be95c5f798f0c0484921b9b9d1fc6e9988` is preserved in the repository as an explicit evaluation benchmark for whether an agent can specify and verify pointer/slice manipulation in Anneal V1:
- **Trusted `unsafe(axiom)` Leaf Helpers:** The file defines three small `unsafe(axiom)` helper functions for slice length, pointer casting, and raw slice construction whose contracts state metadata, address, byte size, and `isize` bounds, but whose Rust bodies are unverified axiomatic leaves.
- **Unfinished Target (`concat_slices`):** The target function `concat_slices` contains a structured `TODO` comment listing five missing specification/proof requirements:
  1. Both input slices belong to the **same allocation**;
  2. The second slice is **immediately contiguous** after the first;
  3. The slices are **non-overlapping**;
  4. The returned slice's **elements equal the concatenation** of the two input slices; and
  5. The returned slice belongs to the **same allocation**.
- Its `#[anneal::spec]` block is **empty** and its Rust implementation body is **`todo!()`** (`ptr_concat.rs:L24`). Furthermore, V1's surface pointer/slice metadata and address equalities do not by themselves model allocation identity, provenance, lifetime validity, byte initialization, or contiguous memory contents. Consequently, `concat_slices` remains an unfinished specification and verification challenge in retained V1.

Basis: **source** (`anneal/v1/examples/ptr_concat.rs`).

---

## Boundaries

1. **Historical V1 Scope Only:** All findings describe the retained Anneal V1 prototype (`anneal/v1` at `41f5b37afe7060fd9fe08c00b200672cd76d77b9` and `bd0956be95c5f798f0c0484921b9b9d1fc6e9988`) and its historical evolution (`d410c162d51977635ca5afac67d99a3b10327a94`, `f98458e7eaf54ff34b69e417ee34e79036f06547`). They are **known not to apply** as normative requirements for current Anneal V2 (`anneal/PRINCIPLES.md`, `anneal/DESIGN.md`).
2. **Distinction Between Executed Probes and Source/Fixture Reviews:**
   - The generated-workspace relocation probe (`support/anneal-v1-generated-workspace-relocation-probe/v1-execution/`) and the interactive LSP dependency-invalidation probe (`support/anneal-v1-interactive-dependency-invalidation/`) were **freshly executed** against `google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988` and `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.
   - The generated-Lean ABI report (`41f5b37...`), clean-workspace prebuilt-archive report (`41f5b37...`), worker-cache disk-amplification report (`d410c162d...` / `f98458e...`), Lake history review (`bd0956b...`), and proof-split / `concat_slices` review (`bd0956b...`) are **source, documentation, and preserved-fixture inspections** (`fresh_execution = false`); the $\approx 100$-worker / $\approx 100\text{ GB}$ and $\approx 5\text{ GB}$ figures were **not examined** via live reproduction in this session.
3. **Archive Reuse Test vs. Strict Zero-Rebuild / Zero-Network Proof:** While `assert_archive_lake_cache_reuse` (`anneal/v1/tests/integration.rs`) enforces `assert_no_write_bits(&aeneas_root)` before running `lake --keep-toolchain --old build Generated` and `lake --keep-toolchain env lean --json`, it does not run inside a network-disabled namespace or trace whether Lake rebuilt any artifact inside writable workspace-local `.lake` storage. Furthermore, `assert_no_write_bits` checks only the installed `aeneas_root` subtree, not the entire Exocrate installation root.
4. **Relocation Probe Shim Limitations:** The relocation probe at `bd0956be95c5f798f0c0484921b9b9d1fc6e9988` used a local symlinked scratch toolchain with Git manifest entries temporarily converted to local path entries rather than a frozen Nix-built Exocrate archive, did not run `lake setup-file` or `lean --json` after the move, and observed pre-existing `sorry` warnings in imported dependencies.
5. **Unfinished `concat_slices` Benchmark (`unsupported` as a completed proof):** Because `anneal/v1/examples/ptr_concat.rs` has an empty `spec` block, a `todo!()` body, and three axiomatized `unsafe(axiom)` helpers, any claim that V1 verified `concat_slices` is **unsupported**.

---

## Evidence

All primary-source coordinates, commit revisions, blob hashes, and staged support artifacts are indexed below:

1. **Generated-Lean ABI and Aeneas Coupling (`support/anneal-v1-generated-lean-abi-main-41f5b37/`):**
   - Machine-readable ABI summary: `support/anneal-v1-generated-lean-abi-main-41f5b37/generated-lean-abi.json`.
   - Source and blob map: `support/anneal-v1-generated-lean-abi-main-41f5b37/source-map.json` (`google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`: `anneal/v1/Cargo.toml` blob `f545b31c8e15a3cc5b5bbaf277abb9e56afc2e33`, `anneal/v1/src/scanner.rs` blob `44b66417a827192b87d4cad3e62421e8ca497d28`, `anneal/v1/src/generate.rs` blob `f087023d08011a90d56bcbdc759e6cbc90c344b5`, `anneal/v1/src/aeneas.rs` blob `9b4618a20938315afc290744bbdfa498848620f4`; `AeneasVerif/aeneas@42c0e90dacf486f7d3ed5b6cde3a9a81f04915a4`: `backends/lean/Aeneas/Std/Primitives.lean` blob `5a73ea5bfae575baf2f26e1d86ea00768d1bccea`, `backends/lean/Aeneas/Std/WP.lean` blob `a599b2b6632fbfdfadbe3dcfb68ee17a6048be5d`; preserved fixtures `expand_output/expected-all.stdout` blob `b4934dc041ad81cca05eeb4aa94a8e22ae39a66f`, `extern_never_verified/out.txt` blob `9cf7a9e663c0dc77597cbd007bc8917c87e6f9e2`, `missing_output/expected.stderr` blob `5255829806d2be2cadf5c87060f17e3b12d9d7cf`).
2. **Clean-Workspace Prebuilt Archive Reuse (`support/anneal-v1-clean-workspace-prebuilt-archive-41f5b37/`):**
   - Source and PR map: `support/anneal-v1-clean-workspace-prebuilt-archive-41f5b37/source-map.json` (`anneal/v1/tests/integration.rs` blob `8fc6f6b9b4d4785e532e0647466a2e2373fe709a`, `anneal/v1/src/aeneas.rs` blob `9b4618a20938315afc290744bbdfa498848620f4`, `anneal/v1/src/setup.rs` blob `32216cedf11c5d6d4b5a4618d8d7bf2578e44b4d`, PRs #3438, #3443, #3450, #3453, Issue #3668).
3. **Worker-Cache Disk Amplification (`support/anneal-v1-integration-test-disk-amplification-f98458e/`):**
   - Source and PR map: `support/anneal-v1-integration-test-disk-amplification-f98458e/source-map.json` (`google/zerocopy@d410c162d51977635ca5afac67d99a3b10327a94` `anneal/tests/integration.rs` blob `55c9d14f8dbf01e1643cf67013ad24841177188c`; removal commit `f98458e7eaf54ff34b69e417ee34e79036f06547` / PR #3305; related PRs #3304, #3306, #3297, Issue #3668).
4. **Generated-Workspace Relocation Execution Probe (`support/anneal-v1-generated-workspace-relocation-probe/v1-execution/`):**
   - Rust fixture: `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/fixture-Cargo.toml`, `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/fixture-lib.rs`.
   - Generator logs & Lakefile: `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/generate.stdout`, `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/generate.stderr`, `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/moved-lakefile.lean`.
   - Unmodified move failure: `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/stale-move.exit`, `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/stale-move.stderr`.
   - Reseeded manifest & passing offline build (`1688 jobs`): `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/reseeded-manifest.json`, `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/reseeded-move.exit`, `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/reseeded-move.stdout`, `support/anneal-v1-generated-workspace-relocation-probe/v1-execution/reseeded-move.stderr`.
5. **Interactive LSP Dependency-Invalidation Execution Probe (`support/anneal-v1-interactive-dependency-invalidation/`):**
   - Replay script & transcripts: `support/anneal-v1-interactive-dependency-invalidation/replay-query.py`, `support/anneal-v1-interactive-dependency-invalidation/query-transcript.json`, `support/anneal-v1-interactive-dependency-invalidation/baseline-build.log`, `support/anneal-v1-interactive-dependency-invalidation/batch-after-dependency.json`.
   - Probe snapshots: `support/anneal-v1-interactive-dependency-invalidation/Probe-v1.lean`, `support/anneal-v1-interactive-dependency-invalidation/Probe-v2.lean`, `support/anneal-v1-interactive-dependency-invalidation/dependency-mutated-Funs.lean`.
   - Generated V1 workspace fixture: `support/anneal-v1-interactive-dependency-invalidation/fixture/Cargo.toml`, `support/anneal-v1-interactive-dependency-invalidation/fixture/src/lib.rs`, `support/anneal-v1-interactive-dependency-invalidation/fixture/lakefile.lean`, `support/anneal-v1-interactive-dependency-invalidation/fixture/lake-manifest.json`, `support/anneal-v1-interactive-dependency-invalidation/fixture/lean-toolchain`, `support/anneal-v1-interactive-dependency-invalidation/fixture/generated/Generated.lean`, `support/anneal-v1-interactive-dependency-invalidation/fixture/generated/RelocateProbeRelocateProbe93d79f43b0c543cb/Funs.lean`, `support/anneal-v1-interactive-dependency-invalidation/fixture/generated/RelocateProbeRelocateProbe93d79f43b0c543cb/Types.lean`.
6. **Lake Relocation History & Proof-Split / `concat_slices` Sources (`google/zerocopy@bd0956be95c5f798f0c0484921b9b9d1fc6e9988`):**
   - `anneal/PRINCIPLES.md`, `anneal/DESIGN.md`, `anneal/v1/AGENTS.md`, `anneal/v1/src/{Anneal.lean,aeneas.rs,generate.rs,resolve.rs,main.rs}`, `anneal/v1/docs/design/{design.md,named_bounds.md}`, `anneal/v1/docs/agent/{04_specifications_and_syntax.md,05_proof_architecture.md,06_tactics_and_tooling.md,07_workflow.md}`, `anneal/v1/examples/{abs.rs,anatomy.rs,ptr_concat.rs}`, and `anneal/v1/tests/fixtures/{stuck_wps,named_bounds_lean_failures}/`.

---

## Revalidation

1. **Generated-Lean ABI Compatibility Matrix Check:**
   - Diff `anneal/v1/src/{scanner.rs,generate.rs,aeneas.rs}` and `Aeneas/Std/{Primitives.lean,WP.lean}` against the 10-point contract in `support/anneal-v1-generated-lean-abi-main-41f5b37/generated-lean-abi.json` (slug derivation, split-file names, `NamingContext`, `map_type`, explicit `*Inst` trait dictionaries, `&mut` result tuple packing, `WP.spec`, textual patches in `patch_funs`/`patch_discriminants`, external template promotion, and fail-closed missing-output checks).
   - Build and elaborate a golden matrix covering `fn -> ()`, scalar inputs/outputs, $0/1/\ge 2$ `&mut` parameters with and without return values, generic trait bounds (`Sized` + non-`Sized`), opaque external templates, `@[discriminant]` types, `show` argument names, and a negative fail-closed missing-`Funs.lean` case.
2. **Clean-Workspace Prebuilt Archive & Relocation Verification:**
   - Materialize the Exocrate omnibus archive, recursively strip write bits (`chmod -R a-w`), and run `run_archive_lake_cache_reuse_test` across two independent fresh temporary workspaces under network isolation while auditing that zero files are written inside the archive and zero dependency `.olean` targets are rebuilt.
   - To revalidate relocation, generate a workspace at path `A`, move it to a different depth `B`, confirm that an unregenerated manifest fails closed, then regenerate both `lake-manifest.json` and `lakefile.lean` for `B` and verify `lake --keep-toolchain --old --offline build`, `lake setup-file`, and `lake env lean --json`.
3. **Interactive LSP Dependency-Invalidation Replay:**
   - Copy `support/anneal-v1-interactive-dependency-invalidation/fixture/` into `BASE/move-parent/moved-lean`, link the local Aeneas and Lean (`v4.30.0-rc2`) trees at `BASE/toolchain`, and run:
     ```bash
     python3 support/anneal-v1-interactive-dependency-invalidation/replay-query.py \
       --workspace BASE/move-parent/moved-lean \
       --evidence-dir OUT
     ```
   - Confirm whether the tested Lean server version still requires worker restart / transitive `.olean` hash invalidation after an imported module rebuild.
4. **Proof-Split & `concat_slices` Evaluation:**
   - When evaluating proof-authoring workflows or `concat_slices` (`anneal/v1/examples/ptr_concat.rs`), separately audit (a) the Rust memory/allocation contract and any trusted `unsafe(axiom)` leaves, (b) non-vacuous discharge of `h_progress` (`∃ y, m = .ok y`), (c) discharge of all `Post` fields, and (d) `#print axioms` freedom from `sorryAx`.
