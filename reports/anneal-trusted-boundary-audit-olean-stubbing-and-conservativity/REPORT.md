# Kernel Boundary Auditing for `Std`, `realizeConst` Diamond Duplicates, Computable Recursion, Two-Stage `.olean` Axiom-Stubbing, Conservativity, and `nanoda_lib` in Anneal

## Summary

Anneal enforces its verification boundary through a Rust orchestrator
(`trusted/audit/src/lib.rs` / `trusted/cargo-anneal/src/audit.rs`) and a
two-phase Lean 4 environment inspector (`trusted/audit/TrustedBoundary.lean`)
pinned to Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). In its
baseline single-stage configuration, `TrustedBoundary.lean` admits only 51
locked `Init.*` modules from `trusted/lean/foundation-lock.json`, rejects any
`.olean` module whose `ModuleData.constants` array contains a constant with
`ci.isPartial == true` or a constant name that appears in more than one module,
and replays every declaration of every non-foundation module (`Trusted.*`,
`Anneal.*`, `Mir`, and `Proof`) through `Kernel.Environment.replay` (`~1.88 s`)
on every per-crate `cargo anneal` run.

Scaling Anneal's untrusted `theory/` and `Proof` layers to use computable
recursive symbolic evaluators (`Anneal.evalSymState`), the full Lean `v4.34.1`
`Init.*` and `Std.*` libraries (`Std.Data.ExtHashMap`,
`Init.Data.BitVec.Lemmas`, `Std.Do`, `omega`, `grind`), multi-crate
verification DAGs, and fast two-stage pre-audited `.olean` caches establishes
six central results across our 9 standalone Lean 4.34.1 probes in this package:

1. **On-Demand `realizeConst` Theorem Subsumption Across Diamond Imports
   (`sameRealizedThmHeader`):** Across all 1,020 exported modules (`114,233`
   `data.constants` entries) and 1,138 private-level modules (`117,715` entries)
   of `Init` and `Std` in Lean `v4.34.1`, exactly 108 exported constant names
   (119 at `level := .private`) appear in `data.constants` of more than one
   module. All 108 / 108 (and 119 / 119) are `.thmInfo` (`TheoremVal`)
   declarations generated on demand by `Lean.Environment.realizeConst`
   (`src/lean/Lean/Environment.lean:2709-2783`). Zero duplicates differ in
   `type`, `levelParams`, `kind`, or `all`. Exactly 9 exported constants across
   12 non-last module occurrences (12 constants across 17 non-last occurrences
   at `level := .private`) have differing `value? (allowOpaque := true)` solely
   because realizing `<fn>.eq_def` or `<fn>.induct_unfolding` inside module
   `<M>` triggers nested realization of a matcher splitter prefixed with
   `_private.<M>.0.`. During `finalizeImport`
   (`Lean/Environment.lean:2268-2283`, `2332-2348`), Lean checks `subsumesInfo`,
   retains the first module in `const2ModIdx` (`env.getModuleIdxFor?`), and
   overwrites `privateConstantMap` (`env.checked`) with the last module's
   `ConstantInfo`. Permitting cross-module duplicate entries and proof-term
   differences if and only if both `stored` and `ci` are `.thmInfo` with
   identical `(name, type, levelParams, all)` (`sameRealizedThmHeader`)—and
   recording `stored` from `env.checked` for axiom-closure and replay checks—is
   sound by `Prop` proof irrelevance and matches `Lean/Replay.lean:89-96`.
2. **Distinguishing Compiler-Generated `<base>._unsafe_rec` from User
   `partial def` (`ci.isCEnv`):** Of the 804 constants with `ci.isPartial ==
   true` across all 1,020 `Init` and `Std` modules, all 804 are compiler
   companions ending in `._unsafe_rec`. In Lean `v4.34.1`, both total
   computable recursion (`structuralRecursion` at
   `Lean/Elab/PreDefinition/Structural/Main.lean:198` and `wfRecursion` at
   `Lean/Elab/PreDefinition/WF/Main.lean:83`) and user-written `partial def`
   (`addAndCompilePartial` at `Lean/Elab/PreDefinition/Main.lean:20-36`) call
   `addAndCompilePartialRec` (`Lean/Elab/PreDefinition/Basic.lean:280-296`),
   which emits `<base>._unsafe_rec` with `safety := DefinitionSafety.partial`
   (`ci.isPartial == true`, `ci.isCEnv == false`). However, their `<base>`
   declarations in `env.checked` are disjoint: a total recursive `def`
   elaborates `<base>` as `.defnInfo` with `safety == .safe`, whereas a user
   `partial def` elaborates `<base>` as `.opaqueInfo` (`isUnsafe == false`).
   Excluding `ci.isPartial` companions from `locals` (matching
   `ConstantInfo.isCEnv` in `Lean/Replay.lean:160-163`) while verifying after
   the module loop that every local `ci.isPartial` constant has
   `Compiler.isUnsafeRecName? cName == some baseName` where `locals.get?
   baseName` is `.defnInfo` with `baseVal.safety == .safe` eliminates
   sensitivity to `PersistentHashMap` `foldStage2` hash-trie ordering, unlocks
   all 26 computable recursive definitions in
   `theory/Anneal/FunctionalTranslation.lean` (removing all 26 `noncomputable`
   modifiers), and rejects user `partial def` in both Phase 1 (`"preflight"`)
   and Phase 2 (`"audit"`).
3. **Kernel Isolation of `@[implemented_by]`, `@[extern]`, and `@[csimp]`,
   Closure-Only Replay, and Independent `nanoda_lib` Checking:** Inspection of
   Lean `v4.34.1`'s C++ kernel (`src/kernel/type_checker.cpp:614-635, 693-721,
   761, 1057-1135`) establishes that `@[implemented_by]`, `@[extern]`, and
   `@[csimp]` are stored in environment extensions consulted by the kernel
   exclusively inside `type_checker::reduce_native`, which executes only when
   reducing `Lean.reduceBool` or `Lean.reduceNat`. Because `Lean.reduceBool`
   and `Lean.reduceNat` depend on `axiom Lean.trustCompiler : True`
   (`src/lean/Init/Core.lean:2338-2385`), restricting the transitive axiom
   closure (with `allowOpaque := true`) to `{Classical.choice, Quot.sound,
   propext}` guarantees that `reduce_native` is never invoked and compiler
   overrides in `Std.*` and unlocked `Init.*` are completely inert in the
   kernel. Combining a two-tier `toolchainLibrary` base with
   `collectLocalClosure` (Closure-Only Replay) speeds up kernel replay by
   **52.3×** when importing `Std.*` (`1,204 ms` for 2,121 closure declarations
   vs. `62,999 ms` for all 64,862 safe declarations across 646 non-foundation
   modules) and by **2.26×** on local workspace declarations (`559 ms` for 762
   reachable declarations vs. `1,266 ms` for all 1,897 local declarations),
   while `lean4export` (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`) and
   `nanoda_lib` (`8de7e0c4ed3052745a7f8725164efd9e76d84c56`, `v0.4.31`)
   export and recheck all 3,753 transitive declarations from an empty
   environment in an independent Rust kernel in **1.33 s** total.
4. **Two-Stage `preaudit` (`theory-lock.json`) + Single-`importEnv` Stage-2
   `runtime-audit` and Single-File `.olean` Axiom-Stubbing (Config 3b):**
   Splitting verification into a one-time **Stage-1 `preaudit`** (`foundation ++
   Trusted ++ Anneal` -> `theory-lock.json`) and a per-crate **Stage-2
   `runtime-audit`** (`Mir ++ Proof` replayed over the locked Stage-1 kernel
   environment) combined with **Single-File `.olean` Axiom-Stubbing**
   (converting Stage-1 `.thmInfo` entries to `.axiomInfo` and pruning
   unreachable `_private.*._proof_*` subterms via `readModuleData` +
   `saveModuleData` with `isModule := false`, **Config 3b**) reduces Stage-1
   `.olean` disk size by **54.6%** (`17.11 MB -> 7.77 MB`; `MirLemmas.olean`
   shrinks **9.63x** from `1.71 MB` to `178 KB`, and
   `FunctionalTranslation.olean` shrinks **2.50x** from `12.55 MB` to
   `5.02 MB`), reduces per-crate `Proof.lean` elaboration time by **18.6%**
   (`320.7 ms -> 261.2 ms`), reduces Stage-2 `runtime-audit` wall-clock time
   from `2,013.5 ms` to **`75.2 ms`** (**26.8x speedup**), and cuts peak RSS by
   **43.9%** (`616.5 MiB -> 346.1 MiB`).
5. **Formal Conservative Extension, Cut-Elimination (`Deriv.linkAxioms`), and
   Vacuous-Helper Immunity (`support/ConservativityModel.lean`):**
   Mechanized proofs in [`ConservativityModel.lean`](support/ConservativityModel.lean)
   (452 lines, zero `sorry`) prove that replacing kernel-replayed Stage-1
   theorems with `.axiomInfo` stubs of identical `(name, levelParams, type)`—paired
   with a monotonic 6-feature candidate summary (`axioms`, `directFeats`,
   `guardedFeats : Feature -> Finset Feature`) in `theory-lock.json`—is both
   **sound and complete** (`staged_precompilation_sound_and_complete`), and that
   vacuous definitions or theorems in `theory/Anneal/` (`def BrokenSpec : Prop :=
   True`) cannot help derive `Trusted.CrateTheorem Mir.crate`
   (`vacuous_helper_immunity`).
6. **Six Boundary-Audit Vulnerabilities Discovered and Closed
   (`support/SingleImportTwoStageBoundary.lean`):**
   Red-teaming the single-stage and two-stage boundary checkers uncovered and
   resolved 6 concrete vulnerabilities: (1) unhashed foundation/prefix-cache
   `.olean` files, (2) latent `hasLooseBVars` false-positive rejection on
   extracted `Trusted.candidate` subexpressions under `lam`/`forallE`/`letE`
   binders, (3) pure-source `-DElab.async=false` universe-parameter spoofing on
   `Proof.verify_crate.{v}`, (4) cross-stage `realizeConst` equation and
   splitter constants emitted into `Proof.olean`, (5) direct and deferred
   `Trusted.candidate` guard laundering across stubbed `.olean`s, and (6)
   `dep == depOwner` false-positive guard-dispatch coupling in
   `checkTrustedNonContamination`.

---

## Applicability

The findings, primary-source analyses, and runnable probes in this report apply
to the subjects identified in `REPORT.json` under the following scope and
configuration constraints:

| Subject | Revision / Digest | Role & Scope in This Investigation |
| :--- | :--- | :--- |
| `joshlf/anneal` | `24367bd1a8c784f2578535954f9915e24894a56f` & `f2bc17e9be87b777d63c785b31f3370ff058d69b` (`ca5600a7cf83d1431789c61c6d2bf8fd3ab0b383`) | Governs `trusted/audit/src/lib.rs` (lines 1–1961), `trusted/audit/TrustedBoundary.lean` (lines 1–1014), `trusted/lean/foundation-lock.json` (`schema_version == 3`, 51 locked `Init.*` modules), and `theory/Anneal/FunctionalTranslation.lean` (lines 1–8315). |
| `leanprover/lean4` | `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | Pinned Lean 4 toolchain (`x86_64-unknown-linux-gnu` and `aarch64-apple-darwin`) providing `bin/lean`, `bin/leanchecker`, `Lean.SMap`, `src/runtime/compact.cpp`, the C++ kernel (`src/kernel/`), the environment/elaborator (`src/lean/Lean/`), and the 1,020 exported / 1,138 private `Init` and `Std` `.olean` modules. |
| `leanprover/lean4export` | `df81913eee5519d5a88ae5b0fd701b5298cc29ab` (format `v3.1.0`) | Standalone Lean 4 declaration exporter (`Export.lean`, `Main.lean`) used to serialize transitive kernel declaration closures (including `OpaqueVal.value`) to NDJSON at `trustLevel := 0`. |
| `ammkrn/nanoda_lib` | `v0.4.31` (`8de7e0c4ed3052745a7f8725164efd9e76d84c56`) | Independent Rust implementation of the Lean 4 kernel (`nanoda_bin`) used to re-verify NDJSON exports from an empty environment with an explicit `permitted_axioms` allowlist. |
| `leanprover/comparator` | `865edc14486c3388e9225daa971da8e157488c3e` | Challenge-solution verification orchestrator (`Compare.lean`, `Axioms.lean`) examined for attribute/instance modification checks (`checkImportedConstantsNotModified`). |
| `leanprover/lean4checker` | `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` | Standalone environment replay repository compared against the built-in `leanchecker` binary (`src/lean/LeanChecker.lean`) shipped in Lean `v4.34.1`. |
| `digama0/lean4lean` | `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` | Pure Lean 4 kernel reimplementation (`Lean4Lean/TypeChecker.lean`, `Lean4Lean/Primitive.lean`) examined for primitive-type shape validation invariants. |

---

## Findings

### Finding 1: Baseline `anneal-audit` Architecture and Complete Inventory of `Init` and `Std` in Lean `v4.34.1`

Basis: `source` + `execution`

#### 1.1 Two-Layer Enforcement in `anneal-audit` and `TrustedBoundary.lean`

In `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f`, boundary validation
is split between a Rust host orchestrator (`trusted/audit/src/lib.rs`) and a
Lean inspector (`trusted/audit/TrustedBoundary.lean`):

| Layer & Phase | Source Location | Enforced Invariants |
| :--- | :--- | :--- |
| **Rust Host & Lock Verification** | `trusted/audit/src/lib.rs:514-911, 1026-1748` | Verifies `trusted/lean/foundation-lock.json` (`schema_version == 3`), SHA-256 digests of regular non-symlinked `bin/lean`, `bin/lake`, and all 51 locked `lib/lean/Init/*.olean` files, `AUDIT_SOURCE_FILES` digests against `EMBEDDED_BOUNDARY_SCRIPT`, Cargo manifest hygiene (forbidding build scripts and proc-macros), Lakefile hygiene, `.olean` freshness (`olean_mtime >= src_mtime`), and a comment-stripped textual forbidden-token pre-filter. |
| **Phase 1: `"preflight"` (Source Syntax & Trust Table)** | `trusted/audit/TrustedBoundary.lean:212-500, 999-1010` | Imports only the locked foundation parser environment (`trustLevel := 0`, `loadExts := true`), parses each `.lean` source file via `Parser.parseHeader` and `Parser.parseCommand`, requires an explicit `prelude` header without `module`/`public`/`meta`/`all` modifiers, restricts top-level commands to `commandKinds` and attributes to `allowedAttributeNames` (`simp`, `instance`, `reducible`, `semireducible`, `irreducible`, plus `@[vetted]` and `@[candidate <feat>]` in `Trusted.*`), forbids `unsafe`, `partial`, `meta`, `axiom`, `example`, `coinductive`, `open scoped`, `set_option`, `by_elab`, `run_tac`, `native_decide`, `decide +native`, and `deriving`, and extracts `(fullDeclarationName, trustStatus)` pairs. |
| **Phase 2: `"audit"` (`.olean` Inventory, Non-Contamination, Closure & Replay)** | `trusted/audit/TrustedBoundary.lean:501-997, 1011-1018` | Loads compiled `.olean` artifacts from explicit runner paths (`arts`) at `trustLevel := 0`, `plugins := #[]`, `loadExts := false`, and `level := .private` (`setExporting false`). Verifies the module import DAG (`validateGraph`), declaration provenance and body presence (`verifyAndCollectLocals`), two-color `@[vetted]` vs. `@[candidate <feat>]` non-contamination (`checkTrustedNonContamination`), `<mirMod>.crate : Trusted.Crate` and `<proofMod>.verify_crate : Trusted.CrateTheorem <mirMod>.crate` envelope shapes, axiom closure (`{Classical.choice, Quot.sound, propext}`), demand-driven candidate feature reachability (`collectActiveCandidateFeatures`), and fresh kernel replay (`base.toKernelEnv.replay`). |

#### 1.2 Complete Constant Inventory of `Init` and `Std` in Lean `v4.34.1`

Running [`support/DiagnoseRealizeConst.lean`](support/DiagnoseRealizeConst.lean)
against Lean `v4.34.1` (`import Std`) loads **1,020 modules** at `level :=
.exported` (`114,233` `data.constants` entries representing `114,068` unique
constants) and **1,138 modules** at `level := .private` (`117,715`
`data.constants` entries representing `117,534` unique constants):

| Module Tier (`level := .exported`) | Modules | `data.constants` Entries | Axioms (`axiomInfo`) | `unsafe` (`isUnsafe`) | `partial` (`isPartial`) | `opaque` (`opaqueInfo`) | `@[implemented_by]` | `@[extern]` | `@[csimp]` |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| **1. Locked `Init.*` (`foundation-lock.json`)** | 51 | 9,463 | **15** | 42 | 172 | 93 | 19 | 182 | 15 |
| **2. Unlocked `Init.*` (outside lock)** | 480 | 53,216 | **0** | 24 | 318 | 163 | 18 | 468 | 36 |
| **3. `Std.*`** | 489 | 51,554 | **0** | 14 | 314 | 167 | 14 | 100 | 0 |
| **Total (`Init` + `Std`, `.exported`)** | **1,020** | **114,233** | **15** | **80** | **804** | **423** | **51** | **750** | **51** |

Four structural properties of the `Init` + `Std` closure govern boundary
design:

1. **Zero Axioms Outside `Init.Prelude` and `Init.Core`:** All 15 `axiomInfo`
   declarations in the entire 1,020-module `Init` + `Std` closure reside in two
   already-locked foundation modules: `Init.Prelude` (11 axioms:
   `Classical.choice`, `Quot.sound`, `sorryAx`, and 8 compiler-erasure axioms
   `lcProof`, `lcUnreachable`, `lcErased`, `lcAny`, `lcCast`, `Quot.lcInv`,
   `unsafeIntro`, `isScalarObj`) and `Init.Core` (4 axioms: `propext`,
   `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`). Zero
   unlocked `Init.*` or `Std.*` modules declare an `axiom`.
2. **Location of `BitVec` Theory in Lean `v4.34.1`:** `Std.BitVec` does not
   exist in Lean `v4.34.1`; `Init.Data.BitVec.Basic` and
   `Init.Data.BitVec.Bootstrap` belong to the 51 locked foundation modules,
   whereas `Init.Data.BitVec` and `Init.Data.BitVec.Lemmas` reside in the 480
   unlocked `Init.*` modules.
3. **Transitive Import Closure Sizes of Target Libraries:**
   - `Init.Data.BitVec.Lemmas`: 173 modules (51 locked `Init.*`, 122 unlocked
     `Init.*`, 0 `Std.*`), with 10 `unsafe` and 101 `isPartial` constants in
     unlocked modules.
   - `Std.Data.ExtHashMap`: 217 modules (51 locked `Init.*`, 144 unlocked
     `Init.*`, 22 `Std.*`), with 12 `unsafe` and 155 `isPartial` constants in
     unlocked modules.
   - `Std.Do`: 457 modules (51 locked `Init.*`, 384 unlocked `Init.*`, 22
     `Std.*`), with 16 `unsafe` and 301 `isPartial` constants in unlocked
     modules.
   - Combined `Init.Omega` + `Init.Grind` + `Init.GrindInstances` +
     `Init.Data.Int.OfNat` + `Std.Data.ExtHashMap` closure: 285 base modules
     (51 locked `Init.*` + 234 `toolchainLibrary` modules).
4. **Why `prelude` Files Using `grind` on `Nat` Inequalities Require
   `Init.Data.Int.OfNat`:** When a module begins with `prelude` (omitting the
   implicit `import Init` umbrella) and invokes `grind` on `Nat` inequalities,
   it must explicitly import `Init.Grind`, `Init.GrindInstances`, and
   `Init.Data.Int.OfNat`, because `grind`'s Cutsat/linear-integer-arithmetic
   `Nat` embedding constructs proof terms referencing `Nat.ToInt.le_eq` in
   `Init.Data.Int.OfNat`.

---

### Finding 2: Diagnosis and Soundness of `realizeConst` Duplicate `.thmInfo` Constants Across Diamond Imports

Basis: `source` + `execution` + `derived`

#### 2.1 Primary-Source Mechanism in `src/lean/Lean/Environment.lean`

In Lean `v4.34.1`, equation theorems (`.eq_1`, `.eq_def`), congruence lemmas
(`.congr_simp`, `.congr_eq_1`), and functional induction unfolding theorems
(`.induct_unfolding`, `.fun_cases_unfolding`) are not generated eagerly when a
function `f` is elaborated. Instead, `enableRealizationsForConst f` marks `f`
as realizable, and downstream modules generate those theorems on demand via
`Lean.Meta.realizeConst` (`src/lean/Lean/Meta/Basic.lean:2727-2765`), which
invokes `Lean.Environment.realizeConst`
(`src/lean/Lean/Environment.lean:2709-2783`).

Four mechanisms in `src/lean/Lean/Environment.lean` and
`src/lean/Lean/Replay.lean` determine how on-demand realized constants behave
across diamond module imports:

1. **Stage-2 Serialization into `ModuleData.constants` (`mkModuleData`,
   `Lean/Environment.lean:1858-1885`):** When module `M` realizes a theorem `c`
   for an imported function `f`, `realizeConst` adds `c` into `M`'s kernel
   environment via `kenv.addDeclCore` (`Lean/Environment.lean:2614, 2749`),
   inserting `c` into stage 2 (`map₂`) of `kenv.constants`. When `M` is
   written to `.olean`, `mkModuleData` folds over `kenv.constants.foldStage2`
   (`Lean/Environment.lean:1868-1872`) and exports `c` in `M`'s
   `data.constants` array. If two incomparable modules `M₁` and `M₂` in a
   diamond import graph both realize `c`, both `M₁.olean` and `M₂.olean`
   contain `c` in their `data.constants` arrays.
2. **Module-Scoped Private Splitters in Proof Terms (`setMainModule`,
   `Lean/Environment.lean:1183-1190`):** When `finalizeImport` initializes
   `importRealizationCtx?`, `setMainModule M` sets
   `importRealizationCtx?.env.header.mainModule := M`. If realizing an equation
   or unfolding theorem `c` (such as `List.drop.eq_def`) inside module `M`
   triggers nested realization of a private matcher splitter via
   `mkPrivateName` (such as `List.take.match_1.splitter`), Lean prefixes that
   private splitter with `_private.<M>.0.`. Consequently, `M₁`'s proof term
   `ci₁.value? true` references `_private.<M₁>.0.List.take.match_1.splitter`,
   whereas `M₂`'s proof term `ci₂.value? true` references
   `_private.<M₂>.0.List.take.match_1.splitter`.
3. **Asymmetric Retention Between `const2ModIdx` (First Module) and
   `privateConstantMap` (Last Module) (`Lean/Environment.lean:2268-2283`,
   `2332-2348`):** When importing a diamond graph containing `M₁` (at module
   index `modIdx₁`) and `M₂` (at `modIdx₂ > modIdx₁`), `finalizeImport` merges
   duplicate constants using `subsumesInfo`:
   ```lean
   -- src/lean/Lean/Environment.lean:2268-2275
   private def subsumesInfo (constMap : ConstMap) (info₁ info₂ : ConstantInfo) : Bool := Id.run do
     if !(info₁.name == info₂.name && info₁.type == info₂.type && info₁.levelParams == info₂.levelParams) then
       return false
     match info₁, info₂ with
     | .thmInfo tv₁, .thmInfo tv₂ => tv₁.all == tv₂.all
     | .defnInfo dv₁, .defnInfo dv₂ =>
       dv₁.safety == dv₂.safety && dv₁.all == dv₂.all &&
         subsumesValue constMap dv₁.value dv₂.value
     | _, _ => false
   ```
   Because `subsumesInfo` returns `true` for any two `.thmInfo` entries with
   identical `(name, type, levelParams, all)`, `privateConstantMap.insert cname
   cinfo` **overwrites** `env.checked` with the **last** module's `ConstantInfo`
   (`M₂`), while `const2ModIdx.insertIfNew cname modIdx` retains the **first**
   module's index (`M₁`)!
4. **Matching Subsumption Rule in `Lean.Kernel.Environment.replay'`
   (`src/lean/Lean/Replay.lean:89-96`):** Lean's kernel replay implementation
   contains the identical `.thmInfo` header check.

#### 2.2 Complete Quantitative Classification Across `Init` and `Std`

Running [`support/DiagnoseRealizeConst.lean`](support/DiagnoseRealizeConst.lean)
establishes the following exact counts across all `Init` and `Std` modules in
Lean `v4.34.1`:

| Metric | `level := .exported` (`1,020` modules) | `level := .private` (`1,138` modules) |
| :--- | ---: | ---: |
| Total `data.constants` entries across all modules | 114,233 | 117,715 |
| Unique constant names in `env.checked.get.constants` | 114,068 | 117,534 |
| Duplicate constant names (`allOccurrences[c].size > 1`) | **108** (165 extra entries) | **119** (181 extra entries) |
| Duplicate constants that are `.thmInfo` (`TheoremVal`) | **108 / 108 (100%)** | **119 / 119 (100%)** |
| Category A: Identical `(type, levelParams, kind, all)` and `value? true` | **99** | **107** |
| Category B: Identical `(type, levelParams, kind, all)`, differing `value? true` | **9** (12 non-last occurrences) | **12** (17 non-last occurrences) |
| Category C: Differing `type`, `levelParams`, `kind`, or `all` | **0** | **0** |
| Duplicate `data.extraConstNames` across modules | **0** | **0** |
| `env.getModuleIdxFor? c` equals **first** module in `env.header.modules` | **108 / 108 (100%)** | **119 / 119 (100%)** |
| `env.checked.get.find? c` stores **last** module's `ConstantInfo` | **108 / 108 (100%)** | **119 / 119 (100%)** |

#### 2.3 Complete Table of Category B Duplicates (Differing `value? true`)

| # | Constant Name | Kind | Defining Modules in `Init` + `Std` (`.private`) | Sole Difference in `value? true` Across Defining Modules |
| ---: | :--- | :--- | :--- | :--- |
| 1 | `List.drop.eq_def` | `.thmInfo` | `Init.Data.Array.GetLit`, `Init.Data.List.TakeDrop` | `_private.<Mod>.0.List.take.match_1.splitter` |
| 2 | `List.eraseIdx.eq_def` | `.thmInfo` | `Init.Data.List.Impl`, `Init.Data.List.Erase`, `Init.Data.List.Nat.Basic` | `_private.<Mod>.0.List.eraseIdx.match_1.splitter` |
| 3 | `List.find?.eq_def` | `.thmInfo` | `Init.Data.List.Impl`, `Init.Data.List.ToArray` | `_private.<Mod>.0.List.getLast?.match_1.splitter` |
| 4 | `List.take.eq_def` | `.thmInfo` | `Init.Data.List.TakeDrop`, `Init.Data.List.Impl` | `_private.<Mod>.0.List.take.match_1.splitter` |
| 5 | `List.takeWhile.eq_def` | `.thmInfo` | `Init.Data.List.TakeDrop`, `Init.Data.List.Impl` | `_private.<Mod>.0.List.getLast?.match_1.splitter` |
| 6 | `List.zipIdx.eq_def` | `.thmInfo` | `Init.Data.List.Impl`, `Init.Data.List.Sort.Lemmas` | `_private.<Mod>.0.List.findIdx.go.match_1.splitter` |
| 7 | `Nat.repeat.eq_def` | `.thmInfo` | `Init.Data.String.Length`, `Std.Data.Iterators.Lemmas.Producers.Repeat` | `_private.<Mod>.0.Nat.repeat.match_1.splitter` |
| 8 | `String.Slice.Pos.revSkipWhile._unary.induct_unfolding` | `.thmInfo` | `Init.Data.String.Lemmas.Pattern.{TakeDrop.Basic, Pred, Char, String.ForwardPattern}` | `_private.<Mod>.0.String.Slice.Pos.{revSkipWhile._unary.eq_def, skipWhile.match_1.splitter}` |
| 9 | `String.Slice.Pos.skipWhile._unary.induct_unfolding` | `.thmInfo` | `Init.Data.String.Lemmas.Pattern.{TakeDrop.Basic, Pred, Char, String.ForwardPattern}` | `_private.<Mod>.0.String.Slice.Pos.{skipWhile._unary.eq_def, skipWhile.match_1.splitter}` |
| 10 | `List.flatMapM.loop.eq_def` | `.thmInfo` | `Init.Data.List.Monadic`, `Init.Data.List.Impl` (`.private` only) | `_private.<Mod>.0.List.flatMapM.loop.match_1.splitter` |
| 11 | `List.foldl.eq_def` | `.thmInfo` | `Init.Data.List.MinMaxOn`, `Init.Data.List.Lemmas` (`.private` only) | `_private.<Mod>.0.List.foldl.match_1.splitter` |
| 12 | `String.Slice.Pattern.Model.split._unary.induct_unfolding` | `.thmInfo` | `Init.Data.String.Lemmas.Pattern.Split.{Pred, Basic}` (`.private` only) | `_private.<Mod>.0.String.Slice.Pattern.Model.split...` |

#### 2.4 Soundness of `sameRealizedThmHeader` in `TrustedBoundary.lean`

Replacing the unconditional equality check with `sameRealizedThmHeader`
([`support/PatchedTrustedBoundaryPrototype.lean`](support/PatchedTrustedBoundaryPrototype.lean)):

```lean
def sameRealizedThmHeader (a b : ConstantInfo) : Bool :=
  match a, b with
  | .thmInfo ta, .thmInfo tb =>
    ta.name == tb.name &&
    ta.type == tb.type &&
    ta.levelParams == tb.levelParams &&
    ta.all == tb.all
  | _, _ => false
```

preserves soundness across all threat vectors: (1) restricted strictly to
`.thmInfo` (`Prop` theorems); (2) justified by `Prop` proof irrelevance in the
kernel; and (3) inserts `stored` from `env.checked.get` into `locals` so both
the axiom closure walk and `base.toKernelEnv.replay` inspect the exact proof
term `stored.value? true` present in `env.checked`.

---

### Finding 3: Distinguishing Compiler-Generated `<base>._unsafe_rec` from User `partial def`

Basis: `source` + `execution` + `derived`

#### 3.1 Stage-2 `ConstantInfo` Representation of Total vs. Partial Recursion

Running [`support/ProbePartialVsTotal.lean`](support/ProbePartialVsTotal.lean)
on Lean `v4.34.1` demonstrates the exact stage-2 `ConstantInfo` entries emitted
into `env.checked` and `ModuleData.constants`:

| Source Construct | Base Constant (`<name>`) | Companion Constant (`<name>._unsafe_rec`) |
| :--- | :--- | :--- |
| Structurally recursive `def totalStruct` | `.defnInfo` (`safety = .safe`, `isPartial = false`, `isCEnv = true`) | `.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some totalStruct`) |
| Well-founded recursive `def totalWF` | `.defnInfo` (`safety = .safe`, `isPartial = false`, `isCEnv = true`) | `.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some totalWF`) |
| Mutual well-founded `def mutualEven` / `mutualOdd` | `.defnInfo` (`safety = .safe`, `isPartial = false`, `isCEnv = true`) | `.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some mutualEven` / `mutualOdd`) |
| Private recursive `private def privRec` | `.defnInfo` (`safety = .safe`, `isPartial = false`, `isCEnv = true`) | `.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some _private...privRec`) |
| Nested `where` recursive `def withWhere.loop` | `.defnInfo` (`safety = .safe`, `isPartial = false`, `isCEnv = true`) | `.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some withWhere.loop`) |
| **User-written `partial def userPartial`** | **`.opaqueInfo` (`isUnsafe = false`, `isPartial = false`, `isCEnv = true`)** | **`.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some userPartial`)** |
| User-written `opaque userOpaque` | `.opaqueInfo` (`isUnsafe = false`, `isPartial = false`, `isCEnv = true`) | *(none)* |

Recording `(ci.name, m.module, isTrusted)` in `pendingPartials` during the
module scan and verifying after the loop
([`support/PatchedTrustedBoundaryPrototype.lean`](support/PatchedTrustedBoundaryPrototype.lean)):

```lean
for (cName, modName, isTrusted) in pendingPartials do
  let errMsg :=
    if isTrusted then s!"unsafe/partial Trusted declaration {cName}"
    else s!"unsafe/partial declaration {cName} in {modName}"
  let some baseName := Compiler.isUnsafeRecName? cName | fail errMsg
  let some (.defnInfo baseVal) := locals.get? baseName | fail errMsg
  unless baseVal.safety == .safe && (← origin env baseName) == modName do
    fail errMsg
```

admits all total recursive definitions (allowing removal of all 26
`noncomputable` modifiers across `theory/Anneal/FunctionalTranslation.lean`)
while rejecting any user-written `partial def`.

---

### Finding 4: C++ Kernel Soundness Analysis of `@[implemented_by]`, `@[extern]`, `@[csimp]`, `@[irreducible]`, `opaque`, `.thmInfo`, and `.axiomInfo` (`ProbeKernelReducibility.lean`)

Basis: `source` + `execution` + `derived`

#### 4.1 Native Execution Isolation (`reduce_native`)

Across the 969 unlocked `Init.*` and `Std.*` modules in Lean `v4.34.1`, there
are 32 `@[implemented_by]` overrides, 568 `@[extern]` bindings, and 36 `@[csimp]`
theorems. In `src/kernel/type_checker.cpp:614-635`, `reduce_native` is called at
only two sites in the entire C++ kernel (`whnf_core` at line 761 and
`lazy_delta_reduction_step` at lines 1101-1105), and only when reducing an
application of `Lean.reduceBool` or `Lean.reduceNat`. Because both reference
`axiom Lean.trustCompiler : True` (`src/lean/Init/Core.lean:2338-2385`),
restricting reachable axioms (with `allowOpaque := true`) to `{Classical.choice,
Quot.sound, propext}` guarantees that `reduce_native` is never invoked and
`@[implemented_by]`, `@[extern]`, and `@[csimp]` in `Init.*` and `Std.*` are
100% inert in the kernel.

#### 4.2 Why Only `.opaqueInfo` (in `Type`) and `.axiomInfo` (in `Prop`) Prevent C++ Kernel Unfolding

Inspection of `src/kernel/type_checker.cpp` and `src/kernel/declaration.h`,
verified empirically by
[`support/ProbeKernelReducibility.lean`](support/ProbeKernelReducibility.lean),
shows that:
1. `@[irreducible]` is stored only in `reducibilityCoreExt` after `addDecl`
   (`Lean/Elab/PreDefinition/Basic.lean:214-216`); in the C++ kernel it is a
   regular `.defnInfo`.
2. Even raw `.defnInfo` with `ReducibilityHints.opaque` is unfolded by
   `type_checker::whnf` (`is_delta` checks `info->has_value()`, ignoring hints)
   and `lazy_delta_reduction_step` (`unfold_both` when both hints are `.opaque`).
3. In C++ `constant_info::has_value(bool allow_opaque = false)`
   (`src/kernel/declaration.h:466-468`), `has_value(false)` returns **`true` for
   `is_theorem()` (`.thmInfo`)** and **`false` for `is_opaque()` (`.opaqueInfo`)
   and `is_axiom()` (`.axiomInfo`)**. While `is_def_eq_proof_irrel`
   (`type_checker.cpp:932-939`) short-circuits `is_def_eq` on proofs in `O(1)`,
   `whnf_core` and `inductive_reduce_rec` (`Acc.rec`) still unfold `.thmInfo`
   bodies unless they are stubbed to `.axiomInfo`:

| Declaration Kind | `ConstantInfo` Constructor | Kernel `hints` | Lean `hasValue (allowOpaque := false)` | C++ `constant_info::has_value(false)` | `Kernel.whnf` Unfolds? | `Kernel.isDefEq` vs. Ground Value Unfolds? |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `def` (standard) | `.defnInfo` | `.regular h` | `true` | `true` | **Yes** | **Yes** (`O(fuel)`) |
| `@[irreducible] def` | `.defnInfo` | `.regular h` | `true` | `true` | **Yes** | **Yes** (`O(fuel)`) |
| Raw `.defnInfo` with `.opaque` hints | `.defnInfo` | `.opaque` | `true` | `true` | **Yes** | **Yes** (`O(fuel)`) |
| `opaque d : T := v` | `.opaqueInfo` | N/A | `false` | **`false`** | **No** | **No** (`isDefEq d v = false`) |
| `axiom a : T` (in `Type`) | `.axiomInfo` | N/A | `false` | **`false`** | **No** | **No** |
| `theorem t : P := p` (`Prop`) | `.thmInfo` | N/A | `false` | **`true`** | **Yes** (if `Kernel.whnf` called) | **No** (`is_def_eq_proof_irrel` short-circuits in `O(1)`) |
| `axiom t : P` (`Prop` stub) | `.axiomInfo` | N/A | `false` | **`false`** | **No** | **No** (`is_def_eq_proof_irrel` short-circuits in `O(1)`) |

| `fuel` | `@[irreducible] def` Kernel `Eq.refl` (`us`) | Raw `.defnInfo (.opaque)` Kernel `Eq.refl` (`us`) | `.thmInfo` Application Kernel Check (`us`) | `.thmInfo` vs. `@[irreducible]` Speedup |
| ---: | ---: | ---: | ---: | ---: |
| `200` | `4,659 us` | `4,752 us` | `59 us` | **79.0x** |
| `500` | `12,188 us` | `11,729 us` | `58 us` | **210.1x** |
| `1000` | `23,932 us` | `23,365 us` | `29 us` | **825.2x** |
| `2000` | `46,772 us` | `46,778 us` | `62 us` | **754.4x** |

---

### Finding 5: Two-Tier `toolchainLibrary` Admission, Closure-Only Replay (`collectLocalClosure`), Multi-Crate DAG Verification, and `lean4export` + `nanoda_lib`

Basis: `source` + `execution`

#### 5.1 Replay Strategy Comparison & Multi-Crate DAG Benchmark

| Benchmark Configuration | Loaded Modules | Total Checked Constants | Replayed Declarations | Replay Wall Time | Speedup |
| :--- | ---: | ---: | ---: | ---: | ---: |
| **External `Std.*` + `Init.*` Module-Wide Replay** (replaying all safe declarations in 646 non-foundation modules) | 697 | ~74,300 | 64,862 | **62,999 ms** | 1.0× |
| **External `Std.*` + `Init.*` Closure-Only Replay** (replaying only transitive non-foundation closure of `verify_crate`) | 697 | ~74,300 | **2,121** | **1,204 ms** | **52.3×** |
| **Patched `TrustedBoundary.lean` Full Local Replay** (285 locked `foundation ++ toolchainLibrary` base + all 15 local modules) | 300 | 38,000+ | 1,897 | **1,266 ms** | 1.0× |
| **Patched `TrustedBoundary.lean` Closure-Only Local Replay (`collectLocalClosure`)** (285 base + reachable local closure of multi-crate DAG) | 300 | 38,000+ | **762** | **559 ms** | **2.26×** |

| Verification Phase / Check | Modules | Constants Checked | Replayed Local Decls | Exit Code & Result | Wall Time |
| :--- | ---: | ---: | ---: | :--- | ---: |
| **CLI Phase 1 (`"preflight"`)** (`51` `foundation` + `234` `toolchainLibrary` + `15` local `.lean` files) | 285 base + 15 source | 187 `trustDeclarations` | — | `0` (`"ok": true`) | **3,517 ms** |
| **CLI Phase 2 (`"audit"`) — Multi-Crate DAG** `[(Upstream.Mir, Upstream.Proof), (Downstream.Mir, Downstream.Proof)]` | 300 | 38,000+ (`5,312` reachable) | **762** (of 1,897) | `0` (`"ok": true`) | **8,691 ms** |
| **CLI Phase 2 (`"audit"`) — Single-Crate Downstream** `[(Downstream.Mir, Downstream.Proof)]` (`Upstream` in `theory`) | 300 | 38,000+ (`5,312` reachable) | **762** (of 1,897) | `0` (`"ok": true`) | **8,976 ms** |
| **In-Process `verifyAndCollectLocals` across all `Init` + `Std` + 15 local modules** (`level := .private`) | 1,153 | 119,595 | — | `ok` (`17` diff-val realized dups, `9` `_unsafe_rec`) | **329 ms** |
| **Negative Control 1: User `partial def badLoop` in Phase 1 (`"preflight"`)** | 285 base + 1 source | — | — | `1` (`policy:unsupported source form Lean.Parser.Command.partial`) | Rejected |
| **Negative Control 2: User `partial def badLoop` in Phase 2 (`"audit"` on `.olean`)** | 301 | — | — | `1` (`policy:unsafe/partial declaration badLoop._unsafe_rec in BadPartial`) | Rejected |

#### 5.2 Comparative Audit of External Kernel Checkers and Dual-Kernel Verification with `lean4export` + `nanoda_lib`

| Checker / Pipeline | Revision / Version | Reads `.olean` Directly? | Replays `Init.Prelude`? | Enforces Axiom Allowlist & Theorem Envelope? | `reduce_native` (`native_decide`) Exposure | Wall Time on `e2e_test/Proof` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`PatchedTrustedBoundaryPrototype.lean`** | `ca20c8df946a...` (`v4.34.1`) | Yes (`importModules` with explicit `arts`) | No (pins `.olean` SHA-256 digests in `foundation-lock.json`) | **Yes:** Phase 1 syntax preflight, `@[vetted]`/`@[candidate]` non-contamination, statement-origin check, axiom allowlist | Blocked by Phase 1 syntax ban and Phase 2 ban on `Lean.trustCompiler` / `Lean.ofReduceBool` | **1.20 s** (`2,121` non-foundation closure decls); **0.56 s** (`762` local decls) |
| **Built-in `leanchecker`** (`src/lean/LeanChecker.lean`) | `5045d0056413...` (`v4.34.1`) | Yes (`withImportModulesConst`) | Yes (with `--fresh`) | **No:** permits `sorryAx`, `Lean.trustCompiler`, and arbitrary user `axiom` declarations; does not inspect theorem statements | Exposed if `Lean.ofReduceBool` is present in the module closure | **4.65 s** (`--fresh` on all 697 modules); **0.07 s** (single module) |
| **`leanprover/lean4checker`** | `91a7f0e8e9df...` | Yes | Yes (`--fresh`) | **No** (superseded upstream by built-in `bin/leanchecker`; see `README.md:1-14`) | Same as built-in `leanchecker` | Superseded by `bin/leanchecker` |
| **`leanprover/comparator`** | `865edc14486c...` | Via `lean4export` | Yes (via `nanoda_bin`) | **Yes:** compares challenge vs. solution theorem types (`Compare.lean:45-62`), checks axioms (`Axioms.lean:15-36`), forbids upstream attribute/instance modifications (`Compare.lean:24-43`) | None (delegates kernel checking to `nanoda_bin`) | Designed for challenge-solution Lake packages in `landrun` sandbox |
| **`lean4export` + `nanoda_lib` (`nanoda_bin`)** | `df81913eee55...` + `8de7e0c4ed30...` (`v0.4.31`) | `lean4export` reads `.olean`; `nanoda_bin` reads NDJSON | **Yes** (starts from empty `Env` in `src/env.rs`) | **Yes:** `nanoda_bin` enforces `permitted_axioms` (`src/parser.rs:344-368`) and pretty-prints target declarations (`pp_declars`) | **Zero exposure:** `nanoda_lib` has no compiler, no IR interpreter, and no `reduce_native` | **1.33 s total** (`0.85 s` export of `325,834` NDJSON lines + `0.48 s` 4-thread check of `3,753` decls) |
| **`digama0/lean4lean`** | `67f63b0c8189...` (`v4.33.0-rc2`) | Yes (`Lean4Lean/Replay.lean`) | Yes (`--fresh`) | Validates primitive shapes (`Lean4Lean/Primitive.lean:11-97`: `Bool`, `Nat`, `String`, `Quot`, `Char`); no axiom allowlist or target theorem check | None in pure Lean typechecker | Targets `v4.33.0-rc2` (~2–3× slower than C++ kernel) |

---

### Finding 6: Formal Conservative Extension (`ConservativityModel.lean`), Two-Stage Trust-Boundary Architecture (`preaudit` + `theory-lock.json` + Single-`importEnv` `runtime-audit`), Six Boundary Vulnerabilities Resolved, and Single-File `.olean` Axiom-Stubbing

#### 6.1 Mechanized Conservativity Laws (`support/ConservativityModel.lean`)

[`support/ConservativityModel.lean`](support/ConservativityModel.lean) (452 lines,
zero `sorry`) mechanizes Anneal's 5-origin partition (`Origin.foundation`,
`.trusted`, `.theory`, `.mir`, `.proof`) and proves:
1. **`statement_origin_invariance`:** Because `Trusted.CrateTheorem` has origin
   `.trusted` and `Mir.crate` has origin `.mir`, `DefEq E₁ t u ↔ DefEq E₂ t u`
   for any `E₁, E₂` sharing `SameComputablePrefix` regardless of whether
   `Anneal.*` theorems are `.thmInfo` or `.axiomInfo`.
2. **`linked_axioms_subset_allowed` & `staged_precompilation_sound_and_complete`:**
   Recursive cut-elimination (`Deriv.linkAxioms`) links any Stage-2 derivation
   over `E.axiomize S` with Stage-1 derivations `hBase` into a single-stage
   derivation in `E` with `axiomsUsed ⊆ AllowedAxioms`.
3. **`vacuous_helper_immunity`:** A vacuous helper specification (`def BrokenSpec
   (c : Trusted.Crate) : Prop := True`) and theorem (`broken_sound`) in
   `theory/Anneal/`, even when imported as an `.axiomInfo` stub in Stage 2,
   cannot help derive `Trusted.CrateTheorem Mir.crate`.
4. **`flat_summary_incomplete_counterexample` & `conditional_summary_sound_and_complete`:**
   A flat per-constant feature set `candUsed(c)` fails on `@[vetted]` bridge
   definitions (`@[vetted] def bridge (x : Nat) : Nat := Trusted.candidate
   "mir_ast" x`), whereas the conditional pair `(directFeats(c),
   guardedFeats(c) : Feature -> Finset Feature)` is both sound and complete.

#### 6.2 Partition of the 12 `TrustedBoundary.lean` Invariants Across Stage 1 and Stage 2

| # | Invariant (`TrustedBoundary.lean`) | Stage-1 `preaudit` (`foundation ++ Trusted ++ Anneal`) | Stage-2 `runtime-audit` (`Mir ++ Proof` over Locked Stage 1) |
| :-: | :--- | :--- | :--- |
| **1** | **Foundation lock** (`verifyFoundationLock`, lines 881-912) | Verify `foundation-lock.json` against `Init.*`/`Lean.*` modules; bind `foundationLockSha256` into `theory-lock.json`. | Verify `foundation-lock.json` (or `theory-lock.json` digest) against loaded `Init.*`/`Lean.*` `.olean`s. |
| **2** | **Import graph provenance** (`verifyImportGraph`, lines 914-926) | Verify all non-foundation imports of `Trusted.*` and `Anneal.*` stay within `Trusted.* ∪ Anneal.*`. | Verify `Mir` imports only `Foundation ∪ Trusted ∪ Anneal` and `Proof` imports only `Foundation ∪ Trusted ∪ Anneal ∪ {Mir}`. |
| **3** | **Local constant classification & namespace isolation** (`collectLocals`, lines 518-558) | Classify all constants in `Trusted.*` and `Anneal.*`; reject `Mir.*`, `Proof.*`, or unknown roots. | Inspect only `Mir.olean` and `Proof.olean` via `readModuleData`; reject any constant whose root is not `Mir` or `Proof` unless it is a valid `realizeConst` equation/splitter of a Stage-1 constant. |
| **4** | **Declaration-kind policy** (`verifyDeclKinds`, lines 560-599) | Enforce `Trusted.*` kind rules (no `unsafe`/`partial`, axioms only `[vetted]`/`[candidate]`, inductives `[vetted]`/`[candidate]`) and `Anneal.*` kind rules (no axioms, no `unsafe`/`partial`). | Enforce `Mir.*` kind rules (no axioms, no `unsafe`/`partial`) and `Proof.*` kind rules (`verify_crate` is `.thmInfo`, no axioms, no `unsafe`/`partial`). |
| **5** | **`Trusted.candidate` syntax & feature-name registry** (`candidateSyntaxError?`, lines 435-466) | Validate all `Trusted.candidate` applications in `Trusted.*` and `Anneal.*` against the 6-feature registry. | Validate all `Trusted.candidate` applications in `Mir.*` and `Proof.*`. |
| **6** | **Vetted-type ownership & constructor non-contamination** (`buildTrustedOwnerMap`, `checkTrustedNonContamination`, lines 601-745) | Fully check `Trusted.*` and populate `ownerMap : HashMap Name Name` in `theory-lock.json`. | Load `ownerMap` from `theory-lock.json` (no new `Trusted.*` constants can exist in Stage 2). |
| **7** | **Stage-1 kernel replay** (`Kernel.Environment.replay` on `Trusted.* ∪ Anneal.*`) | Replay all `4,650` constants in `Trusted.* ∪ Anneal.*` once during `preaudit`. | **Skipped (`0 ms`)**: Stage-1 `.olean`s are hash-verified against `theory-lock.json` and loaded into `map₁`. |
| **8** | **Stage-2 kernel replay** (`Kernel.Environment.replay` on `Mir.* ∪ Proof.*`) | N/A | Replay only the `~65` constants in `Mir.olean` and `Proof.olean` against `base.toKernelEnv` (`map₁`) in **`~2.2 ms`**. |
| **9** | **Envelope check on `Mir.crate` and `Proof.verify_crate`** (`verifyCrateEnvelope`, lines 928-969) | Confirm `Trusted.Crate` and `Trusted.CrateTheorem` exist in `Trusted.*`, have `levelParams == []`, and depend on zero candidate features. | Confirm `Mir.crate : Trusted.Crate` (`.defnInfo`, `levelParams == []`), `Proof.verify_crate : Trusted.CrateTheorem Mir.crate` (`.thmInfo`, `levelParams == []`), and `Mir.crate` reaches zero candidate features. |
| **10** | **Reachable closure & axiom policy** (`verifyProofClosure`, lines 768-830) | Compute transitive `axioms : Array Name` for every constant `c ∈ Trusted.* ∪ Anneal.*` and store in `theory-lock.json`. | Traverse Stage-2 DAG from `Proof.verify_crate` and `Mir.crate`; on Stage-1 constants, union precomputed `summary.axioms` from `theory-lock.json` in `O(1)`. |
| **11** | **Unconditional & deferred `Trusted.candidate` feature tracking** (lines 774-821) | Compute `(directFeats, guardedFeats)` for every constant `c ∈ Trusted.* ∪ Anneal.*` via the 6-feature fixed point and store in `theory-lock.json`. | Traverse Stage-2 DAG with `activeGuard?`; on Stage-1 constants, union `directFeats` (or route to `deferred[g]`) and union `guardedFeats` into `deferred`, then run the 6-feature fixed point. |
| **12** | **No open expressions (`hasLooseBVars`)** (`exprEdges`, lines 479-481) | Verify `!e.hasLooseBVars` at top level of every `Trusted.*` and `Anneal.*` declaration. | Verify `!e.hasLooseBVars` at top level of every `Mir.*` and `Proof.*` declaration (with `allowLooseBVarsInSubexpr = true` inside binder-under-`candidate` subexpressions). |

#### 6.3 Six Boundary-Audit Vulnerabilities Discovered and Resolved

1. **Unhashed Foundation and `--prefix-cache-dir` `.olean`s (`trusted/audit/src/lib.rs:1117-1173, 1676-1803`):**
   Resolved by hashing every foundation and Stage-1 `.olean` into
   `theory-lock.json` (`foundationLockSha256` and `artifactSha256`) and
   verifying SHA-256 digests before Stage-2 `importModules`.
2. **Latent `hasLooseBVars` Rejection on Extracted `Trusted.candidate` Subexpressions Under Binders (`TrustedBoundary.lean:479-503, 702, 782, 795`):**
   Resolved by parameterizing `exprEdges (e : Expr) (allowLooseBVarsInSubexpr :
   Bool := false)` so top-level declarations require `!e.hasLooseBVars` while
   extracted `DeferredGuard.subexpr` fragments under outer `lam`/`forallE`/`letE`
   binders allow bound `.bvar` indices (`SingleImportTwoStageBoundary.lean:160-189`).
3. **Pure-Source `-DElab.async=false` Universe-Parameter Spoofing on `Proof.verify_crate.{v}` (`TrustedBoundary.lean:948-958`):**
   Under `-DElab.async=false`, `MutualDef.lean:1243` takes `elabSync`, and
   `getLevelParamsPreDecls` (`PreDefinition/Basic.lean:68-70`) collects universe
   parameters from both `preDef.type` and `preDef.value`, allowing `universe v` +
   `let _ : PUnit.{v} := PUnit.unit` inside the proof body to produce
   `Proof.verify_crate.{v}` with `levelParams = [v]`. Resolved by requiring
   `mirCrateCi.levelParams.isEmpty` and `proofCi.levelParams.isEmpty` in
   `verifyCrateEnvelope`.
4. **Cross-Stage `realizeConst` Equation and Splitter Constants in `Proof.olean`:**
   Resolved via `realizedRootPrefix?` (requiring the stripped root definition to
   exist in `baseEnv` `map₁`), `sameRealizedThmHeader` on duplicate realizations,
   and `isVettedRealizedEqInStage2` (`lockSummary.vettedDefs.contains rootName`)
   so `Proof`-realized equations of Stage-1 `@[vetted]` definitions do not
   trigger false-positive unguarded candidate errors.
5. **Direct and Deferred `Trusted.candidate` Guard Laundering Across Stubbed Stage-1 `.olean`s (`support/ProbePrecompileThreats.lean`):**
   Resolved by precomputing `(axioms, directFeats, guardedFeats)` from the
   unstubbed `.thmInfo` bodies into `theory-lock.json` before stubbing.
6. **False-Positive Guard-Dispatch Coupling When `dep == depOwner` (`TrustedBoundary.lean:715-721`):**
   In `checkTrustedNonContamination`, referencing a `@[vetted]` type name `I` in
   a type annotation had `dep = I == depOwner`. Resolved by guarding with `if
   dep != depOwner then ...` (`SingleImportTwoStageBoundary.lean:358-363`).

#### 6.4 Single-File `.olean` Axiom-Stubbing (Configs 0 through 3d) and Runtime Benchmarks

| Stage-1 Module | Constants (`.thmInfo`) | Config 0/1 Baseline (B) | Config 2a All 3 `.olean*` (B) | Config 2b `.olean` Only (B) | Config 3a `.thmInfo -> .axiomInfo` (B) | Config 3b + Prune `_proof_*` (B) | Config 3c `elab-minimal` (B) | Config 3d `audit-only` (B) | Config 3b vs. Baseline |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `Trusted/Core.olean` | `138` (`0`) | `176,472` | `191,824` | `78,024` | `176,472` | `176,472` | `124,040` | `85,784` | `0.0%` (`1.00x`) |
| `Trusted/Memory.olean` | `190` (`0`) | `174,568` | `191,720` | `80,960` | `174,568` | `174,568` | `120,032` | `94,408` | `0.0%` (`1.00x`) |
| `Trusted/MirAst.olean` | `677` (`0`) | `647,784` | `706,664` | `282,424` | `647,784` | `647,784` | `460,552` | `370,128` | `0.0%` (`1.00x`) |
| `Trusted/MirSemantics.olean` | `223` (`1`) | `664,536` | `732,728` | `495,536` | `664,296` | `664,296` | `539,304` | `484,064` | `-0.04%` (`1.00x`) |
| `Trusted/Refinement.olean` | `31` (`0`) | `28,152` | `30,152` | `11,032` | `28,152` | `28,152` | `18,432` | `11,648` | `0.0%` (`1.00x`) |
| `Trusted/RustcCapture.olean` | `7` (`0`) | `3,536` | `3,760` | `2,920` | `3,536` | `3,536` | `3,536` | `1,632` | `0.0%` (`1.00x`) |
| `Trusted/StepResult.olean` | `37` (`0`) | `27,824` | `29,888` | `13,808` | `27,824` | `27,824` | `18,744` | `14,720` | `0.0%` (`1.00x`) |
| `Trusted.olean` | `0` (`0`) | `1,256` | `1,400` | `1,256` | `1,256` | `1,256` | `1,256` | `1,256` | `0.0%` (`1.00x`) |
| `Anneal/MirLemmas.olean` | `299` (`188`) | `1,709,392` | `1,622,872` | `93,656` | `182,784` | **`177,560`** | `133,312` | `102,424` | **`-89.6%` (`9.63x`)** |
| `Anneal/FunctionalTranslation.olean` | `2,980` (`310`) | `12,545,816` | `12,131,808` | `2,331,136` | `5,041,840` | **`5,015,656`** | `3,974,728` | `3,569,208` | **`-60.0%` (`2.50x`)** |
| `Anneal.olean` | `1,068` (`28`) | `1,133,288` | `1,041,472` | `266,280` | `850,464` | **`850,464`** | `715,928` | `277,736` | **`-25.0%` (`1.33x`)** |
| **Total (11 Stage-1 modules)** | **`4,650` (`527`)** | **`17,112,624`** (`17.11 MB`) | **`16,684,288`** (`16.68 MB`) | **`3,657,032`** *(unsound)* | **`7,798,976`** (`7.80 MB`) | **`7,767,568`** (**`7.77 MB`**) | **`6,109,864`** (`6.11 MB`) | **`5,013,008`** (`5.01 MB`) | **`-54.6%` (`2.20x`)** |

| Configuration | Stage-1 `.olean` Disk Size | `lean Proof.lean` Elab Time (`ms`) | Audit `import_base` (`ms`) | Audit `import_2nd_env` (`ms`) | Audit `collect_locals` / `readModuleData` (`ms`) | Audit `kernel_replay` (`ms`) | Audit `envelope + closure` (`ms`) | **Total Stage-2 Audit (`ms`)** | **Speedup vs. Config 0** | Peak RSS (`MiB`) | Audit RSS Delta (`MiB`) | Sound & Complete? |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | :---: |
| **Config 0: Single-Stage Full Replay** (`TrustedBoundary.lean` baseline) | `17.11 MB` | `320.7 ms` | `78.4 ms` | `0.0 ms` | `49.7 ms` | `1,885.1 ms` | `0.30 ms` | **`2,013.5 ms`** | `1.00x` | `616.5 MiB` | `+252.9 MiB` | Yes (`382` consts) |
| **Config 1 (Double-Import): Two-Stage Unmodified `.olean`s** | `17.11 MB` | `320.7 ms` | `83.9 ms` | `53.8 ms` | `50.8 ms` | `3.55 ms` | `0.46 ms` | **`192.9 ms`** | `10.44x` | `412.2 MiB` | `+99.1 MiB` | Yes (`382` consts) |
| **Config 1 (Single-Import + `readModuleData`): Unmodified `.olean`s** | `17.11 MB` | `320.7 ms` | `74.4 ms` | **`0.0 ms`** | **`0.71 ms`** | `2.38 ms` | `0.34 ms` | **`79.3 ms`** | **`25.39x`** | `361.9 MiB` | **`+49.2 MiB`** | Yes (`382` consts) |
| **Config 2a: Lean 4 `module` System (All 3 `.olean*` in `LEAN_PATH`)** | `16.68 MB` | `315.4 ms` | `82.1 ms` | `51.0 ms` | `56.6 ms` | `3.67 ms` | `0.48 ms` | **`194.2 ms`** | `10.37x` | `409.5 MiB` | `+97.8 MiB` | Fragile (requires 33 extra `Init` lock entries) |
| **Config 2b: Lean 4 `module` System (`.exported` `.olean` Only)** | `3.66 MB` | `261.9 ms` | `77.6 ms` | `46.6 ms` | `55.6 ms` | `3.52 ms` | `0.39 ms` | **`184.0 ms`** | `10.94x` | `397.7 MiB` | `+85.4 MiB` | **NO** (drops 90 `_private` consts: `292` vs. `382`) |
| **Config 3a (Double-Import): `.thmInfo -> .axiomInfo`** | `7.80 MB` | `261.9 ms` | `78.9 ms` | `49.2 ms` | `52.5 ms` | `3.58 ms` | `0.46 ms` | **`185.0 ms`** | `10.88x` | `396.3 MiB` | `+83.6 MiB` | Yes (`382` consts) |
| **Config 3b (Double-Import): `.thmInfo -> .axiomInfo` + Prune `_proof_*`** | `7.77 MB` | `261.2 ms` | `78.2 ms` | `48.6 ms` | `51.2 ms` | `3.55 ms` | `0.46 ms` | **`182.3 ms`** | `11.04x` | `396.0 MiB` | `+83.4 MiB` | Yes (`382` consts) |
| **Config 3b (Single-Import + `readModuleData` — RECOMMENDED)** | **`7.77 MB` (`-54.6%`)** | **`261.2 ms` (`-18.6%`)** | **`69.9 ms`** | **`0.0 ms`** | **`0.71 ms`** | **`2.21 ms`** | **`0.34 ms`** | **`75.2 ms`** | **`26.78x`** | **`346.1 MiB` (`-43.9%`)** | **`+49.2 MiB`** | **Yes (`382` consts)** |
| **Config 3c (Single-Import): Config 3b + Strip 5 LCNF/IR Extensions** | `6.11 MB` (`-64.3%`) | `258.4 ms` (`-19.4%`) | `69.1 ms` | `0.0 ms` | `0.70 ms` | `2.20 ms` | `0.34 ms` | **`74.3 ms`** | **`27.10x`** | `344.2 MiB` | `+49.0 MiB` | Yes (breaks `native_decide` on Stage 1) |
| **Config 3d (Single-Import): Config 3b + Strip All `entries`** | `5.01 MB` (`-70.7%`) | *N/A (cannot elab `Proof.lean`)* | `68.0 ms` | `0.0 ms` | `0.69 ms` | `2.19 ms` | `0.34 ms` | **`73.1 ms`** | **`27.54x`** | `341.8 MiB` | `+48.8 MiB` | Audit-only (requires dual `.olean` dirs) |

---

## Boundaries

1. **Built-in `leanchecker --fresh` Is Not a Substitute for `TrustedBoundary.lean`:**
   While `leanchecker --fresh` replays all module constants from
   `mkEmptyEnvironment` in 4.65 s, it does not enforce an axiom allowlist
   (`sorryAx`, `Lean.trustCompiler`, and user `axiom bad : False` pass with exit
   code `0`), does not verify `<proofMod>.verify_crate`'s type against
   `Trusted.CrateTheorem <mirMod>.crate`, and does not check `@[vetted]` vs.
   `@[candidate <feat>]` non-contamination.
2. **`sameRealizedThmHeader` Does Not Permit Duplicate `.defnInfo` or `.opaqueInfo` Declarations:**
   Across all 1,020 exported and 1,138 private modules of `Init` and `Std`, zero
   `.defnInfo` duplicates occur (`108 / 108` and `119 / 119` are `.thmInfo`).
   `sameRealizedThmHeader` restricts duplicate tolerance strictly to `.thmInfo`
   so computational definitions in `Trusted`, `Anneal`, and `Mir` must always
   have unique origins and bit-for-bit identical values.
3. **Relaxing `@[implemented_by]`, `@[extern]`, or `opaque` Applies Only to Tier 2 (`Std.*`, Unlocked `Init.*`, `theory/`), Never Tier 1 (`Trusted` and `Mir`):**
   In Tier 1 (`trusted/lean/` and `Mir.lean`), an `opaque` definition in the
   theorem statement could conceal a vacuous specification (`opaque Spec : Prop :=
   True`), so Phase 1 syntax preflight must continue to forbid `opaque`,
   `partial`, `unsafe`, `@[extern]`, and `@[implemented_by]`.
4. **Stage-1 `.defnInfo` Bodies Cannot Be Stripped if Unfolded by Stage 2:**
   While Stage-1 `.thmInfo` proof bodies can be replaced with `.axiomInfo` stubs
   via proof irrelevance and cut elimination (`Deriv.linkAxioms`), Stage-1
   `.defnInfo` value bodies (`2.44 MB` in `FunctionalTranslation.olean`) are
   required whenever `Proof.lean` or Stage-2 `is_def_eq` unfolds those
   definitions.
5. **`theory-lock.json` Must Be Bound to Both `foundation-lock.json` and Every Stage-1 `.olean` SHA-256 Digest:**
   Axiom-stubbing Stage-1 `.olean` files is sound **only** when paired with
   `theory-lock.json` generated from the unstubbed Stage-1 environment *before*
   `.thmInfo -> .axiomInfo` stubbing, and verified via SHA-256 over the stubbed
   `.olean` files *before* Stage-2 `importModules`.

---

## Evidence

All claims, theorems, vulnerability reproducers, and benchmarks in this report
are backed by the 10 preserved support artifacts in this package:

| File Path | Lines | SHA-256 Digest | Purpose |
| :--- | ---: | :--- | :--- |
| [`support/DiagnoseRealizeConst.lean`](support/DiagnoseRealizeConst.lean) | 225 | `01b13a9843828c664fe79ad44052fa280bbc554fe06a9d6dd25ba4dda4ce930b` | Loads `Init` + `Std` at `level := .private`, enumerates all 119 duplicate realized constants, verifies `const2ModIdx` vs. `env.checked` retention, and prints all 12 differing-value `.thmInfo` constants. |
| [`support/ProbePartialVsTotal.lean`](support/ProbePartialVsTotal.lean) | 134 | `ac32784cb3edb4e26d4a933d62f778976901367f599e33728a8866735359a8a6` | Elaborates structural, well-founded, mutual, `private`, and `where` total recursive `def`s alongside `partial def` and `opaque`, printing their stage-2 `ConstantInfo` kinds, `isPartial`, `isCEnv`, and `isUnsafeRecName?`. |
| [`support/PatchedTrustedBoundaryPrototype.lean`](support/PatchedTrustedBoundaryPrototype.lean) | 1,214 | `ca20c8df946a628abef8ebcb43b89a87a6a31cbf9ebfb89d63ae06e9a2a1607e` | Standalone prototype of `TrustedBoundary.lean` implementing `sameRealizedThmHeader`, `pendingPartials` `Compiler.isUnsafeRecName?` validation, `toolchainLibrary` admission, multi-crate `"crates"` support, and `collectLocalClosure`. |
| [`support/source-manifest.json`](support/source-manifest.json) | 296 | — | Machine-readable manifest of inspected repositories, revisions, file paths, byte counts, line counts, and SHA-256 digests. |
| [`support/ConservativityModel.lean`](support/ConservativityModel.lean) | 452 | `9fa5dc4018783b185275c3089870cc0241f3062680464eef782920b51bd5ed86` | Mechanized formalization of Anneal's 5-origin partition and all 6 conservativity meta-theorems (`statement_origin_invariance`, `linked_axioms_subset_allowed`, `staged_precompilation_sound_and_complete`, `vacuous_helper_immunity`, `flat_summary_incomplete_counterexample`, `conditional_summary_sound_and_complete`), zero `sorry`. |
| [`support/ProbeKernelReducibility.lean`](support/ProbeKernelReducibility.lean) | 230 | `da91db6ea689fa75d6a78246bf59e40f9c1206584d5b595085204a4efe4856ea` | Empirical C++ kernel probe testing `@[irreducible] def`, raw `.defnInfo` with `ReducibilityHints.opaque`, `.opaqueInfo`, `.thmInfo`, and `.axiomInfo` under `Kernel.whnf` and `Kernel.isDefEq` across `fuel = 200, 500, 1000, 2000`. |
| [`support/ProbePrecompileThreats.lean`](support/ProbePrecompileThreats.lean) | 383 | `e7b17d248439e9f621525f950accd83941d593c0d257aadf382c1f3abe41a1e7` | End-to-end threat suite reproducing and verifying defenses against direct candidate laundering, `waived` obligation tampering, deferred `Trusted.candidate` guard laundering, and `Lean.reduceBool` native-evaluation bypass. |
| [`support/ProbeTwoStagePreAudit.lean`](support/ProbeTwoStagePreAudit.lean) | 651 | `6710c085670f7ea7d46e9b2527ddc74d766dd88c64e27c048f91c0c6c1800848` | Prototype two-stage boundary auditor (`preaudit` + `runtime-audit`) measuring double-import Stage-2 latency against single-stage full replay. |
| [`support/ProbeAxiomStubRuntime.lean`](support/ProbeAxiomStubRuntime.lean) | 430 | `21a5196ef1fbfd192a444a6b77e804b2e3a2bb4e81dbe99d77dbec043edda613` | Empirical benchmark and byte-level `.olean` analyzer across Configs 0, 1, 2a, 2b, 3a, 3b, 3c, and 3d on the 11 Stage-1 modules of Anneal. |
| [`support/SingleImportTwoStageBoundary.lean`](support/SingleImportTwoStageBoundary.lean) | 1,405 | `94b02641581a2b470df710a42fcaeae90c143404ae7b42f106280f3172eae422` | Production-grade single-`importEnv` + `readModuleData` two-stage boundary auditor implementing `preaudit`, `runtime-audit`, `stub-oleans` (Config 3b), `benchmark`, and 10 automated security `self-test` cases. |

---

## Revalidation

To revalidate all 9 preserved Lean `v4.34.1` probes from the root of this report
package, run:

```bash
lean support/DiagnoseRealizeConst.lean
lean support/ProbePartialVsTotal.lean
lean support/PatchedTrustedBoundaryPrototype.lean
lean --run support/DiagnoseRealizeConst.lean
lean -DwarningAsError=true support/ConservativityModel.lean
lean -DwarningAsError=true support/ProbeKernelReducibility.lean
lean -DwarningAsError=true support/ProbePrecompileThreats.lean
lean -DwarningAsError=true support/ProbeTwoStagePreAudit.lean
lean -DwarningAsError=true support/ProbeAxiomStubRuntime.lean
lean -DwarningAsError=true support/SingleImportTwoStageBoundary.lean
lean --run support/SingleImportTwoStageBoundary.lean self-test
```

Confirm that:
1. `support/ProbePartialVsTotal.lean` reports
   `defnInfo(safety=Lean.DefinitionSafety.safe)` for the base constant of every
   total recursive `def` and `opaqueInfo(isUnsafe=false)` for `userPartial`.
2. `support/DiagnoseRealizeConst.lean` reports `1138` modules loaded at
   `level := .private`, `119` duplicate constant names (`119 / 119` of kind
   `thm`, `0` with differing `type`/`levelParams`/`kind`/`all`), `107` with
   identical `value? true`, and `12` with differing `value? true`.
3. `support/ConservativityModel.lean` compiles with zero warnings and zero
   `sorryAx`, and `support/SingleImportTwoStageBoundary.lean self-test` passes
   all 10 positive and negative security regression checks.
