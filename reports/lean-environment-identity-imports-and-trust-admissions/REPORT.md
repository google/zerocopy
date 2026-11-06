# Lean Environment Identity, Module Import Semantics, Invalidation, and Trust Admissions

## Summary

Across `leanprover/lean4` at `v4.30.0-rc2` (`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`) and `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), a `Lean.Environment` is a persistent, append-only in-memory structure constructed by loading compiled module artifacts (`.olean`, plus `.olean.server` and `.olean.private` under the `module` system) and initializing persistent environment extensions. Lean does **not** compute or expose a semantic content hash of `Lean.Environment` to decide whether an elaboration state is reusable. As `Lean.Language.Lean.process` explicitly documents, there is no cheap test for semantic `Environment` equality: incremental reuse inside a single file relies on retained `Snapshot` chains and syntactic prefix equality, stopping state forwarding at the first syntactic change, while external dependency changes in `lean --server` mark dependent workers stale (`$/lean/staleDependency`) and require a worker restart because imported compacted memory regions cannot be freed in place.

An `import` directive names a logical Lean module (`Name`), not a source file. `Lean.Elab.HeaderSyntax.imports` parses the header into `Lean.Import` records (prepending ordinary and `meta` imports of `Init` unless `prelude` is present), resolves module names through `LEAN_PATH` (`findOLean`) or Lake's pre-resolved `ImportArtifacts`, and reconstructs the transitive dependency DAG from the `imports : Array Import` array serialized inside each loaded `ModuleData` artifact rather than from dependency `.lean` files on disk. Files without the `module` header import the full reachable closure at `.private` level and reject `public`, `meta`, and `all` qualifiers. Files with the `module` header compute effective import visibility (`all`, `public`, `privateAll`, `private`, `none`) and `IRPhases` (`runtime`, `comptime`, `both`) as a least fixed point over the import DAG, deduplicating each reached module into a single `ModuleIdx` entry in `EnvironmentHeader.modules` and upgrading its visibility/phase level when stronger paths are encountered.

Logical proof checking, axiom auditing (`#print axioms`), executable code generation, and artifact freshness are independent boundaries, as established by source inspection at `v4.30.0-rc2` and `v4.34.1` and confirmed by a 6-command execution suite on `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`):

1. **Axiom audit vs. proposition and local hypotheses**: `#print axioms` (`Lean.CollectAxioms`) walks global constant references (and precomputed `exportedAxiomsExt` summaries for imported modules) to report `.axiomInfo` entries (`axiom`, `sorryAx`). It reports an empty axiom set both for a valid closed proof (`ordinary : 2 + 2 = 4 := by decide`) and for a tautological implication with a false local premise (`localHyp (h : False) : False := h`), while catching private-helper assumptions (`viaHelper` -> `assumedFalse`).
2. **Logical reduction vs. `@[implemented_by]` and `native_decide`**: Marking a safe function `f : Bool := false` with `@[implemented_by fImpl]` (where `fImpl` returns `true`) allows kernel reduction (`by rfl`) to prove `logicalResult : f = false` with zero axioms, while `native_decide` (`Lean.Meta.Native.nativeEqTrue`) executes compiled code and introduces a fresh non-unsafe axiom (`nativeResult._native.native_decide.ax_1_1`) to accept `nativeResult : f = true`.
3. **Kernel-check bypass (`debug.skipKernelTC`)**: Ordinary `Kernel.Environment.addDecl` rejects an ill-typed theorem body (`forged : False := True.intro`, exit `1`). Enabling `set_option debug.skipKernelTC true` routes insertion through `addDeclWithoutChecking` (`lean_add_decl_without_checking`), exiting `0` and reporting **zero axioms** under `#print axioms forged` because no `.axiomInfo` constant appears in `True.intro`.
4. **Imported `.olean` vs. mutated `.lean` source**: When `Producer.lean` is compiled to `Producer.olean` with `oldAssumption` and its source file is subsequently overwritten with `newAssumption` without recompiling, `Consumer.lean` exits `0` and reports `oldAssumption` from the retained `.olean`.

## Applicability

The findings in this report apply to the following subjects recorded in `REPORT.json`:

- **Lean 4 `v4.30.0-rc2`**: `leanprover/lean4` revision `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, selected by `google/zerocopy` revision `41f5b37afe7060fd9fe08c00b200672cd76d77b9` (`anneal/flake.nix`, `leanVersion = "v4.30.0-rc2"`) and `AeneasVerif/aeneas` revision `ac9f1bc5262a5e4ff1e24ca78617121382202727` (`backends/lean/lean-toolchain`).
- **Lean 4 `v4.34.1` source and executed binary**: `leanprover/lean4` revision `5045d0056413266e57c625dcd7c365b10e377c52`, executed release binary SHA-256 `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554` on `arm64-apple-darwin24.6.0` (Darwin 27.0.0 arm64).
- **Adjacent baseline reference (`v4.29.0`)**: `leanprover/lean4` revision `98dc76e3c0a9b856c9b98726b713fb04fab16740` (referenced for cross-version corpus provenance; all source and runtime claims below are explicitly scoped to `v4.30.0-rc2` and `v4.34.1`).

### Shared Behavior vs. Version-Specific Behavior (`v4.30.0-rc2` vs. `v4.34.1`)

- **Shared across `v4.30.0-rc2` and `v4.34.1`**:
  - Header parsing (`HeaderSyntax.imports`), implicit `Init` imports, `Import` flags (`importAll`, `isExported`, `isMeta`), search-path resolution (`findOLean`), and explicit `ImportArtifacts` path bundles.
  - Transitive import graph reconstruction from `ModuleData.imports` in `.olean*` files, `EnvironmentHeader` (`imports` vs. deduplicated `modules`), the non-`module` `.private` import regime, and the `module`-system 5-level effective-import fixed-point lattice (`all`, `public`, `privateAll`, `private`, `none`) plus `IRPhases` (`runtime`, `comptime`, `both`).
  - Persistent `Lean.Environment` / `Kernel.Environment` representation (`SMap`), absence of a semantic `Environment` hash, syntax-prefix incremental reuse in `Lean.Language.Lean.process`, and server stale-dependency worker restart on compacted-region boundaries.
  - Trust and admission architecture: `AxiomVal`, `sorryAx`, `Lean.CollectAxioms` (`collect`, `exportedAxiomsExt`), `DefinitionSafety` (`unsafe`, `safe`, `partial`), `@[implemented_by]`, `@[csimp]`, `Lean.Meta.Native.nativeEqTrue` (`native_decide` / `bv_decide`), and `debug.skipKernelTC` (`addDeclWithoutChecking` / `lean_add_decl_without_checking`).
- **Version-specific coordinates and execution coverage**:
  - In `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`), `src/Lean/Environment.lean` is 2,903 lines (SHA-256 `ee364e4788ce0560...`, with `markQuotInit` at line 288 and `ReplayFn` at line 1307) and `src/Lean/Elab/Import.lean` is 206 lines (SHA-256 `5d46fc36944ed3cb...`, with `processHeaderCore` at line 141, `importModules` at line 159, and `processHeader` at line 177).
  - The 6-command runtime verification suite (`support/lean-admissions-imports-and-native-checking/`) was executed directly on the `v4.34.1` binary (`1b370cfcbf44e80d...`), providing concrete execution transcripts and `.olean` specimens for the trust, native-evaluation, `debug.skipKernelTC`, and stale-source-import mechanisms characterized by source inspection at `v4.30.0-rc2`.

## Findings

### 1. Module Header Parsing, Artifact Resolution, and the Import Visibility Lattice

Basis: **source + checked-in tests + derived** (`src/Lean/Setup.lean`, `src/Lean/Parser/Module.lean`, `src/Lean/Elab/Import.lean`, `src/Lean/Util/Path.lean`, `src/Lean/Environment.lean`, `tests/pkg/module/Module/*.lean`).

#### Structured `Lean.Import` Records and Implicit `Init` Dependencies

`Lean.Elab.HeaderSyntax.imports` (`src/Lean/Elab/Import.lean`) converts a parsed file header into an `Array Import`. Each `Lean.Import` (`src/Lean/Setup.lean`) contains:

- `module : Name` — logical module name;
- `importAll : Bool` — whether `import all` was specified (exposing private module data);
- `isExported : Bool` — whether the import is re-exported (`public import` in `module` files, or always `true` in non-`module` files); and
- `isMeta : Bool` — whether `meta import` was specified (requesting compile-time IR for elaboration).

Unless the file header begins with `prelude`, `HeaderSyntax.imports` automatically prepends two imports of `Init`: one ordinary import and one `meta` import. `Lean.Parser.Module.parseHeader` rejects `public import`, `meta import`, and `import all` outside a file that begins with the `module` keyword, and prohibits combining `public` and `all` on a single `import` directive (requiring two separate directives: `public import M` and `import all M`).

#### Artifact Lookup and Transitive Import Graph Reconstruction

Lean resolves each `Import.module` (`A.B.C` -> `A/B/C.olean`) either via `findOLean` across `LEAN_PATH` and the installation's `lib/lean` (`src/Lean/Util/Path.lean`) or via explicit file paths passed in `ModuleSetup.importArts` (`ImportArtifacts` in `src/Lean/Setup.lean`, lines 65–160).

When `importModulesCore` (`src/Lean/Environment.lean`, lines 2038–2180 in `v4.30.0-rc2`; `processHeaderCore` at line 141 and `importModules` at line 159 of `src/Lean/Elab/Import.lean` in `v4.34.1`) loads a module via `readModuleDataParts`, it reads the serialized `ModuleData.imports : Array Import` stored inside that `.olean*` artifact and follows those edges recursively. Consequently:

- The current `.lean` file's header determines only **direct** imports; all **transitive** imports come from the serialized headers inside the resolved `.olean` artifacts.
- `EnvironmentHeader` (`src/Lean/Environment.lean`, lines 151–189) stores direct imports in `imports : Array Import` and the deduplicated transitive closure in `modules : Array ModuleSpec`, where each module's array index is its `ModuleIdx`.

#### Non-`module` Regime vs. `module` Fixed-Point Visibility Lattice

`processHeaderCore` selects the root import level based on whether the file uses `module`:

- **Ordinary (non-`module`) files**: `processHeaderCore` invokes `importModules` at level `.private`. `importModulesCore` loads all transitively reachable modules and ignores module-system visibility filtering.
- **`module` files**: `processHeaderCore` selects `.exported` in batch compilation and `.server` in language-server elaboration. `importModulesCore` computes the least fixed point over a 5-point effective data-import lattice for each reached module in `moduleNameMap`:
  1. `all` — public data in public scope and private data in private scope (initial state of the root module);
  2. `public` — public data in public scope (`public import` propagation);
  3. `privateAll` — public and private data in private scope (`import all` reached from a `all`/`privateAll` importer);
  4. `private` — public data in private scope (ordinary `import` inside a `module` file); and
  5. `none` — no `.olean` data loaded.

If a module is reached along multiple paths in a diamond or via paired `public import M` + `import all M` directives, `importModulesCore` joins the requirements; whenever a module's effective level or `IRPhases` (`runtime`, `comptime`, `both`) strengthens, the loader revisits that module's transitive imports. In particular, `A meta import B` followed by `B import C` propagates `comptime` IR requirement to `C`, whereas `A import B` followed by `B meta import C` does not propagate `B`'s internal meta requirement to `A`.

#### Constant Merging, Conflict Detection, and Persistent Environment Extensions

`finalizeImport` (`src/Lean/Environment.lean`) constructs the public and private constant maps from all loaded `ModuleData` parts. If two imported modules define the same declaration name incompatibly (outside the narrow theorem/axiom subsumption allowed for proof irrelevance and module-system export), `finalizeImport` fails with `throwAlreadyImported` (`tests/pkg/module/Module/ConflictingImported.lean`). When `loadExts := true` (the default in `processHeaderCore`), `finalizeImport` also initializes all registered persistent environment extensions (syntax, attributes, typeclass instances, `@[simp]` sets, tactics), which can execute extension initialization callbacks.

### 2. Environment Identity and Three-Layer Invalidation

Basis: **source + documentation + derived** (`src/Lean/Environment.lean`, `src/Lean/Data/SMap.lean`, `src/Lean/Language/Basic.lean`, `src/Lean/Language/Lean.lean`, `src/Lean/Elab/Command.lean`, `src/Lean/Server/FileWorker.lean`, `src/Lean/Server/Watchdog.lean`, `src/Lean/Server/README.md`).

#### Persistence Without a Semantic Digest

`Kernel.Environment` (`src/Lean/Environment.lean`, lines 207–220 in `v4.30.0-rc2`) and elaborator `Lean.Environment` (lines 560–622 in `v4.30.0-rc2`; 2,903 lines total in `v4.34.1`, SHA-256 `ee364e4788ce0560...`) are persistent: adding a declaration updates thestaged `SMap` (`src/Lean/Data/SMap.lean`, separating imported stage-0 constants from local stage-1 persistent map entries) and returns a new `Environment` value without mutating prior snapshots. Neither `Environment` nor `ModuleData` (lines 122–143) carries a content hash or semantic fingerprint of the whole environment.

In `src/Lean/Language/Lean.lean` (lines 81–118 and 365–384 in `v4.30.0-rc2`), the incremental processor explicitly states that there is **no cheap way to check whether the `Environment` is unchanged**, and `SnapshotBundle` (`src/Lean/Language/Basic.lean`, lines 397–406) notes that replacing the one-version snapshot history with a strong-hash cache remains future work.

#### The Three Invalidation Layers

| Scope | Mechanism in Lean (`v4.30.0-rc2` & `v4.34.1`) | What Triggers Invalidation | What Is Reused or Rebuilt |
| --- | --- | --- | --- |
| **1. Intra-file commands** (`Lean.Language.Lean.process`, `parseCmd`) | `Language.mkIncrementalProcessor` feeds the previous `Snapshot` chain into the next edit. | First syntactic difference in command syntax (even if semantically equivalent). | Commands before the first syntax diff reuse their prior `Snapshot` and `Command.State` (`Environment`); all snapshots from the first syntax diff onward receive `old? = none` and re-elaborate. |
| **2. Intra-worker header** (`parseHeader`, `processHeader`) | Compares newly parsed header syntax against the prior snapshot's header syntax (modulo trailing trivia). | Any syntactic edit to the `import` / `module` header. | Unchanged header syntax reuses the prior import snapshot without re-checking disk `.olean` files; changed header syntax cancels old state and reruns `setupImports` + `processHeaderCore`. |
| **3. Cross-file server dependencies** (`Watchdog.lean`, `FileWorker.lean`) | Watchdog records each worker's imported-module closure (`FileWorker.lean`, lines 543–549) and listens for `didSave` and watched `.lean` events (`Watchdog.lean`, lines 939–949, 1259–1290). | Saving an imported `.lean` file or receiving a watched-file change notification. | Watchdog sends `$/lean/staleDependency`; `FileWorker` (lines 632–652) publishes a sticky `"Imports are out of date and should be rebuilt"` diagnostic. Reloading requires restarting the worker process (`src/Lean/Server/README.md`) so compacted `.olean` regions can be freed and `lake setup-file` re-executed. |

### 3. Logical Admissions, Executable Trust Boundaries, and `v4.34.1` Execution Probes

Basis: **source + execution + derived** (`src/Lean/Util/CollectAxioms.lean`, `src/Lean/Meta/Native.lean`, `src/Lean/AddDecl.lean`, `src/kernel/environment.cpp`, `support/lean-trust-admissions/FINDINGS.md`, `support/lean-trust-admissions/SOURCES.md`, `support/lean-admissions-imports-and-native-checking/observations.json`, `support/lean-admissions-imports-and-native-checking/source-index.json`, `support/lean-admissions-imports-and-native-checking/probes/*`).

#### Source-Level Trust Taxonomy (`v4.30.0-rc2` and `v4.34.1`)

1. **Global axioms (`AxiomVal` / `Declaration.axiomDecl`)**: Carry `name`, `levelParams`, `type`, and `isUnsafe : Bool`, with no value body. The kernel verifies only that `type` is well-typed.
2. **`sorry` (`sorryAx`)**: `Init.Prelude` defines `axiom sorryAx (α : Sort u) (synthetic : Bool) : α`; user `sorry` elaborates with `synthetic := false` and parser/elaborator recovery uses `synthetic := true`. Even if `warn.sorry` warnings are suppressed, the transitive dependency on `sorryAx` remains in the declaration's expression graph.
3. **Transitive axiom collection (`#print axioms` / `Lean.CollectAxioms`)**: `Lean/Util/CollectAxioms.lean` traverses constant references in both the type and value of `.defnInfo`, `.thmInfo`, and `.opaqueInfo` declarations (`opaque` and `noncomputable` declarations are traversed rather than treated as axioms). For imported declarations, `CollectAxioms` reuses precomputed axiom arrays from `exportedAxiomsExt` serialized in the imported `.olean` rather than re-walking imported proof bodies unless explicitly replayed (`ReplayFn` at `src/Lean/Environment.lean:1307` in `v4.34.1`).
4. **Kernel safety fence (`DefinitionSafety.unsafe`) vs. `unsafe t`**: The kernel rejects references to `unsafe` constants (such as `unsafe axiom lcProof`) inside `safe` or `partial` declarations. The surface term `unsafe t : α` bridges this only at the compiler level by synthesizing an auxiliary `unsafe` definition and attaching `@[implemented_by]` to a safe wrapper (requiring non-emptiness of `α`).
5. **Compiler replacement (`@[implemented_by]` and `@[csimp]`)**: `@[implemented_by impl]` replaces compiled code calls without proving semantic equivalence to the logical definition (`@[csimp]` requires an equality theorem, whose own axiom closure must still be checked).
6. **Native evaluation (`Lean.Meta.Native.nativeEqTrue`)**: Used by `native_decide` and `bv_decide` (`src/Lean/Meta/Native.lean`). Compiles and executes a closed `Bool` expression in native/interpreter code, verifies that evaluation returns `true`, and inserts a fresh non-unsafe axiom (`<decl>._native.<kind>.ax_...`) asserting `e = true`.
7. **Kernel type-checking bypass (`debug.skipKernelTC`)**: Registered with default `false`. When `true`, `Lean.AddDecl.addDecl` (`src/Lean/AddDecl.lean`, line 22 in `v4.34.1`) calls `Kernel.Environment.addDeclWithoutChecking`, which invokes `lean_add_decl_without_checking` (`src/kernel/environment.cpp`, line 297 in `v4.34.1`) and inserts the declaration without checking its proof term.

#### Six-Command `v4.34.1` Execution Matrix (`support/lean-admissions-imports-and-native-checking/`)

Executed on `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`, binary SHA-256 `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554` on Darwin arm64, recorded in `support/lean-admissions-imports-and-native-checking/observations.json`):

| Probe Command / Specimen | Key Construct Executed | Exit Code | `#print axioms` / Diagnostic Output | Trust Boundary Demonstrated |
| --- | --- | --- | --- | --- |
| `logical-and-assumed` (`support/lean-admissions-imports-and-native-checking/probes/logical-and-assumed.lean`) | `ordinary : 2 + 2 = 4 := by decide`; `localHyp (h : False) : False := h`; `viaHelper : False` calling private helper using `axiom assumedFalse : False` | `0` | `ordinary`: no axioms; `localHyp`: no axioms; `viaHelper`: `[assumedFalse]` | `#print axioms` catches private transitive axioms, but a clean axiom list on `localHyp` does not mean the proposition is unconditional—the theorem type itself must be inspected. |
| `native-implementation` (`support/lean-admissions-imports-and-native-checking/probes/native-implementation.lean`) | `def f : Bool := false` with `@[implemented_by fImpl]` (`fImpl : Bool := true`); `logicalResult : f = false := by rfl`; `nativeResult : f = true := by native_decide` | `0` | `logicalResult`: no axioms; `nativeResult`: `[nativeResult._native.native_decide.ax_1_1]` | Kernel reduction (`rfl`) uses the logical body (`false`), whereas `native_decide` executes `fImpl` (`true`) and records the generated native-evaluation axiom. |
| `checked-rejection` (`support/lean-admissions-imports-and-native-checking/probes/checked-rejection.lean`) | `addDecl` of theorem `forged : False` with proof body `True.intro` under default options (`debug.skipKernelTC = false`) | `1` | Kernel error: `(kernel) declaration type mismatch, 'forged' has type 'False' but it is expected to have type 'True'` | Ordinary kernel checking rejects ill-typed proof bodies injected via metaprogramming. |
| `kernel-bypass` (`support/lean-admissions-imports-and-native-checking/probes/kernel-bypass.lean`) | Same `forged : False := True.intro` insertion under `set_option debug.skipKernelTC true` | `0` | `theorem forged : False := True.intro`; `'forged' does not depend on any axioms` | `#print axioms` only walks `.axiomInfo` nodes in the expression graph; it does **not** detect that `debug.skipKernelTC` bypassed the kernel type checker. |
| `compile-producer` (`support/lean-admissions-imports-and-native-checking/probes/Producer-v1.lean` -> `Producer.olean`) | Compiles `theorem exportedFalse : False := oldAssumption` to `Producer.olean` | `0` | Emits `support/lean-admissions-imports-and-native-checking/probes/Producer.olean` | Baseline compiled artifact capturing `oldAssumption` in `ModuleData` and `exportedAxiomsExt`. |
| `stale-source-import` (`Producer-v2.lean` overwrites `Producer.lean`; run `Consumer.lean`) | `Producer.lean` on disk now uses `newAssumption`, but `Producer.olean` is not rebuilt; `Consumer.lean` runs `import Producer` and `#print axioms exportedFalse` | `0` | `'exportedFalse' depends on axioms: [oldAssumption]` | `import Producer` loads `Producer.olean` (`oldAssumption`) and ignores the uncompiled edit to `Producer.lean` (`newAssumption`). |

### 4. Implications for Verification Oracles and Anneal Boundary Auditing

When a verification tool (such as Anneal's verification model over transition systems `StepResult` and `Behavior` with `ChoiceKind`) audits a user or agent proof:

```lean
inductive StepResult (State : Type) where
  | step (next : State)
  | done
  | trapped
  | stuck

inductive Behavior (Obs : Type) where
  | terminates (trace : List Obs)
  | traps      (trace : List Obs)
  | diverges   (trace : Nat → Obs)
  | goesWrong

inductive ChoiceKind where
  | demonic
  | angelic
```

neither "Lean exited `0`" nor "`#print axioms` reported no disallowed axioms" is sufficient by itself. A complete acceptance oracle must jointly enforce:

1. **Checker configuration integrity**: `debug.skipKernelTC` must be `false`, and user/proof code must not invoke `addDeclWithoutChecking` or load untrusted plugins/native initializers.
2. **Explicit axiom whitelist**: `#print axioms` on the target theorem must contain only foundational axioms permitted by policy (rejecting `sorryAx`, user axioms, and—unless native compilation and `@[implemented_by]` replacements are explicitly in the trusted computing base—`._native.native_decide.ax_*` / `._native.bv_decide.ax_*`).
3. **Target theorem signature check**: The audited declaration's kernel type in the final `Environment` must match the expected obligation statement (preventing vacuous local hypotheses as in `localHyp`).
4. **Resolved artifact-graph freshness**: Every imported `.olean` (and `.olean.server`/`.olean.private`) loaded via `LEAN_PATH` or `ModuleSetup.importArts` must correspond to the current source and toolchain generation, or the final environment must be rechecked from exported declarations via `Lean.Environment.replay` (`ReplayFn`).

## Boundaries

- **Byte-level `.olean` compacted-region layout (`not examined`)**: This report characterizes `ModuleData`, `EnvironmentHeader`, and `readModuleDataParts` at the Lean source and CLI execution levels; internal pointer-fixup and compacted-region byte offsets inside `.olean` files were **not examined** here.
- **Cyclic `.olean` import graphs (`not examined`)**: `importModulesCore` specifies the import graph as a DAG; failure behavior on manually forged cyclic `.olean` headers was **not examined**.
- **Cross-process `Lean.Environment` digest (`unsupported`)**: Lean explicitly lacks a cheap semantic equality test or portable hash for `Lean.Environment` across processes (**unsupported** by `Lean.Language.Lean.process` at both `v4.30.0-rc2` and `v4.34.1`).
- **Automatic `.lean` source reparsing during `import` (`known not to apply`)**: Lean's `importModules` loads `.olean` artifacts and is **known not to apply** uncompiled edits from `.lean` source files on disk (`stale-source-import`).
- **Kernel soundness under `debug.skipKernelTC = true` (`known not to apply`)**: Kernel proof checking is **known not to apply** when `debug.skipKernelTC` is enabled, even when `#print axioms` reports an empty axiom set (`kernel-bypass`).
- **Formal verification of the Lean C++ kernel, compiler, or OS (`not examined`)**: These findings characterize Lean's implementation boundaries and audit mechanisms; formal verification of the C++ kernel, runtime memory manager, or host hardware was **not examined**.

## Evidence

### Primary Upstream Source (`leanprover/lean4`)

- **Module headers, import resolution, and `Environment` construction (`v4.30.0-rc2` @ `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` and `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`)**:
  - `src/Lean/Setup.lean` (`v4.30.0-rc2` lines 65–160): `Import`, `ModuleHeader`, `ImportArtifacts`, `ModuleSetup`.
  - `src/Lean/Parser/Module.lean`: `parseHeader` (qualifier validation for `module` vs. non-`module` headers).
  - `src/Lean/Elab/Import.lean` (`v4.34.1` 206 lines, SHA-256 `5d46fc36944ed3cb...`): `HeaderSyntax.imports`, `processHeaderCore` (line 141), `importModules` (line 159), `processHeader` (line 177).
  - `src/Lean/Util/Path.lean`: `modToFilePath`, `SearchPath.findWithExt`, `findOLean`.
  - `src/Lean/Environment.lean` (`v4.30.0-rc2` lines 122–220, 560–622, 1825–1881, 2038–2180; `v4.34.1` 2,903 lines, SHA-256 `ee364e4788ce0560...`): `ModuleData`, `EffectiveImport`, `EnvironmentHeader`, `Kernel.Environment`, `Lean.Environment`, `markQuotInit` (line 288 in `v4.34.1`), `ReplayFn` (line 1307 in `v4.34.1`), `mkModuleData`, `writeModule`, `importModulesCore`, `readModuleDataParts`, `finalizeImport`.
  - `src/Lean/Data/SMap.lean`: staged map (`SMap`) separating imported and local constants.
  - Checked-in module-system test suite (`v4.30.0-rc2`): `tests/pkg/module/Module/Basic.lean`, `tests/pkg/module/Module/Imported.lean`, `tests/pkg/module/Module/PrivateImported.lean`, `tests/pkg/module/Module/ImportedAll.lean`, `tests/pkg/module/Module/MetaImported.lean`, `tests/pkg/module/Module/ConflictingImported.lean`.
- **Incremental processor and language-server invalidation**:
  - `src/Lean/Language/Basic.lean` (lines 397–406 in `v4.30.0-rc2`): `SnapshotBundle` and `Language.mkIncrementalProcessor`.
  - `src/Lean/Language/Lean.lean` (lines 81–118, 365–499 in `v4.30.0-rc2`): `Language.Lean.process`, absence of cheap `Environment` equality check, unchanged-header fast path, syntax-prefix reuse cutoff.
  - `src/Lean/Elab/Command.lean`: `Command.State` snapshot invariant.
  - `src/Lean/Server/FileWorker.lean` (lines 475–496, 543–549, 632–652 in `v4.30.0-rc2`) and `src/Lean/Server/Watchdog.lean` (lines 939–949, 1259–1290 in `v4.30.0-rc2`): import-closure registration, `notifyAboutStaleDependency`, `$/lean/staleDependency`, sticky restart diagnostic.
  - `src/Lean/Server/README.md`: compacted-region lifetime rationale for worker restart on dependency updates.
- **Trust, axiom collection, native evaluation, and kernel bypass**:
  - `src/Lean/Util/CollectAxioms.lean`: `collect`, `exportedAxiomsExt`, `collectAxioms`.
  - `src/Lean/Meta/Native.lean`: `nativeEqTrue`.
  - `src/Lean/AddDecl.lean` (line 22 in `v4.34.1`): `debug.skipKernelTC` dispatch to `addDeclWithoutChecking`.
  - `src/kernel/environment.cpp` (line 297 in `v4.34.1`): `lean_add_decl_without_checking`.

### Preserved Package Support Artifacts

- **`v4.30.0-rc2` trust and admissions reference notes (observed 2026-09-26)**:
  - `support/lean-trust-admissions/FINDINGS.md`, `support/lean-trust-admissions/BOUNDARIES.md`, `support/lean-trust-admissions/EVIDENCE.md`, `support/lean-trust-admissions/REVALIDATION.md`, and `support/lean-trust-admissions/SOURCES.md` (recording exact `v4.30.0-rc2` file paths and Git blob SHA-1s).
- **`v4.34.1` admissions, native evaluation, kernel-bypass, and stale-import execution suite (observed 2026-10-14)**:
  - Execution summary, source index, and probe runner: `support/lean-admissions-imports-and-native-checking/observations.json`, `support/lean-admissions-imports-and-native-checking/source-index.json`, `support/lean-admissions-imports-and-native-checking/run-probes.py`.
  - Probe inputs, compiled `.olean`, and captured stdout/stderr:
    - `support/lean-admissions-imports-and-native-checking/probes/logical-and-assumed.lean` (`.stdout`, `.stderr`)
    - `support/lean-admissions-imports-and-native-checking/probes/native-implementation.lean` (`.stdout`, `.stderr`)
    - `support/lean-admissions-imports-and-native-checking/probes/checked-rejection.lean` (`.stdout`, `.stderr`)
    - `support/lean-admissions-imports-and-native-checking/probes/kernel-bypass.lean` (`.stdout`, `.stderr`)
    - `support/lean-admissions-imports-and-native-checking/probes/Producer-v1.lean`, `support/lean-admissions-imports-and-native-checking/probes/Producer-v2.lean`, `support/lean-admissions-imports-and-native-checking/probes/Producer.lean`, `support/lean-admissions-imports-and-native-checking/probes/Producer.olean`, `support/lean-admissions-imports-and-native-checking/probes/Consumer.lean`
    - `support/lean-admissions-imports-and-native-checking/probes/compile-producer.stdout` (`.stderr`) and `support/lean-admissions-imports-and-native-checking/probes/stale-source-import.stdout` (`.stderr`).

## Revalidation

1. **Rerun the 6-command admissions, native-evaluation, bypass, and stale-import probe suite**:
   In a disposable copy of this package, run the probe script (wrapping CLI Lean invocations with `anneal-lean-run` on shared hosts):
   ```bash
   python3 -B support/lean-admissions-imports-and-native-checking/run-probes.py --lean /path/to/lean
   ```
   Verify in the generated `observations.json` that:
   - `logical-and-assumed` exits `0` with empty axioms for `ordinary` and `localHyp` and `[assumedFalse]` for `viaHelper`;
   - `native-implementation` exits `0` with empty axioms for `logicalResult` and a generated `._native.native_decide.ax_*` axiom for `nativeResult`;
   - `checked-rejection` exits `1` with a kernel declaration-type mismatch;
   - `kernel-bypass` exits `0` and reports no axioms despite the ill-typed proof body; and
   - `stale-source-import` exits `0` and still reports `oldAssumption` from `Producer.olean` after `Producer.lean` is overwritten with `newAssumption`.

2. **Source diff checklist for new Lean revisions**:
   - Diff `src/Lean/Setup.lean`, `src/Lean/Elab/Import.lean` (`HeaderSyntax.imports`, `processHeaderCore`), and `src/Lean/Environment.lean` (`ModuleData`, `importModulesCore`, `finalizeImport`, `ReplayFn`).
   - Diff `src/Lean/Language/Lean.lean` (`process`, `parseHeader`, `parseCmd`) and `src/Lean/Language/Basic.lean` (`SnapshotBundle`) to check whether Lean has introduced a semantic `Environment` digest or still relies on syntax-prefix reuse.
   - Diff `src/Lean/Util/CollectAxioms.lean`, `src/Lean/Meta/Native.lean` (`nativeEqTrue`), `src/Lean/AddDecl.lean` (`debug.skipKernelTC`), and `src/kernel/environment.cpp` (`lean_add_decl_without_checking`).
