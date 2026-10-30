# Kernel Boundary Auditing for `Std`, `realizeConst` Diamond Duplicates, Computable Recursion, Closure-Only Replay, and `nanoda_lib` in Anneal

## Summary

Anneal enforces its verification boundary through a Rust orchestrator
(`trusted/audit/src/lib.rs` / `trusted/cargo-anneal/src/audit.rs`) and a
two-phase Lean 4 environment inspector (`trusted/audit/TrustedBoundary.lean`)
pinned to Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). In its
baseline configuration, `TrustedBoundary.lean` admits only 51 locked `Init.*`
modules from `trusted/lean/foundation-lock.json`, rejects any `.olean` module
whose `ModuleData.constants` array contains a constant with `ci.isPartial ==
true` or a constant name that appears in more than one module, and replays
every declaration of every non-foundation module through
`Kernel.Environment.replay`.

Scaling Anneal's untrusted `theory/` and `Proof` layers to use computable
recursive symbolic evaluators (`Anneal.evalSymState`), the full Lean `v4.34.1`
`Init.*` and `Std.*` libraries (`Std.Data.ExtHashMap`,
`Init.Data.BitVec.Lemmas`, `Std.Do`, `omega`, `grind`), and multi-crate
verification DAGs exposes three soundness-preserving invariants in Lean
`v4.34.1`'s elaborator and kernel environment representation:

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
   while verifying a 15-module multi-crate DAG `[(Upstream.Mir,
   Upstream.Proof), (Downstream.Mir, Downstream.Proof)]`. As a defense-in-depth
   second opinion, `lean4export` (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`)
   and `nanoda_lib` (`8de7e0c4ed3052745a7f8725164efd9e76d84c56`, `v0.4.31`)
   export and recheck all 3,753 transitive declarations (including
   `Init.Prelude`) from an empty environment in an independent, memory-safe
   Rust kernel with zero `reduce_native` support in **1.33 s** total (`0.85 s`
   export + `0.48 s` 4-thread check).

---

## Applicability

The findings, primary-source analyses, and runnable probes in this report apply
to the subjects identified in `REPORT.json` under the following scope and
configuration constraints:

| Subject | Revision / Digest | Role & Scope in This Investigation |
| :--- | :--- | :--- |
| `joshlf/anneal` | `24367bd1a8c784f2578535954f9915e24894a56f` (skeleton worktree `e75556f5767705404404c0675c6d2d9bcee41d6f`) | Governs `trusted/audit/src/lib.rs` (lines 1–1961), `trusted/audit/TrustedBoundary.lean` (lines 1–1014), `trusted/lean/foundation-lock.json` (`schema_version == 3`, 51 locked `Init.*` modules), and `theory/Anneal/FunctionalTranslation.lean` (lines 1–8315). |
| `leanprover/lean4` | `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | Pinned Lean 4 toolchain (`x86_64-unknown-linux-gnu` and `aarch64-apple-darwin`) providing `bin/lean`, `bin/leanchecker`, the C++ kernel (`src/kernel/`), the environment/elaborator (`src/lean/Lean/`), and the 1,020 exported / 1,138 private `Init` and `Std` `.olean` modules. |
| `leanprover/lean4export` | `df81913eee5519d5a88ae5b0fd701b5298cc29ab` (format `v3.1.0`) | Standalone Lean 4 declaration exporter (`Export.lean`, `Main.lean`) used to serialize transitive kernel declaration closures (including `OpaqueVal.value`) to NDJSON at `trustLevel := 0`. |
| `ammkrn/nanoda_lib` | `v0.4.31` (`8de7e0c4ed3052745a7f8725164efd9e76d84c56`) | Independent Rust implementation of the Lean 4 kernel (`nanoda_bin`) used to re-verify NDJSON exports from an empty environment with an explicit `permitted_axioms` allowlist. |
| `leanprover/comparator` | `865edc14486c3388e9225daa971da8e157488c3e` | Challenge-solution verification orchestrator (`Compare.lean`, `Axioms.lean`) examined for attribute/instance modification checks (`checkImportedConstantsNotModified`). |
| `leanprover/lean4checker` | `91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709` | Standalone environment replay repository compared against the built-in `leanchecker` binary (`src/lean/LeanChecker.lean`) shipped in Lean `v4.34.1`. |
| `digama0/lean4lean` | `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` | Pure Lean 4 kernel reimplementation (`Lean4Lean/TypeChecker.lean`, `Lean4Lean/Primitive.lean`) examined for primitive-type shape validation invariants. |
| `support/DiagnoseRealizeConst.lean` | SHA-256 `01b13a9843828c664fe79ad44052fa280bbc554fe06a9d6dd25ba4dda4ce930b` | Preserved diagnostic probe enumerating and classifying all duplicate constants across `Init` and `Std` in Lean `v4.34.1`. |
| `support/ProbePartialVsTotal.lean` | SHA-256 `ac32784cb3edb4e26d4a933d62f778976901367f599e33728a8866735359a8a6` | Preserved diagnostic probe comparing stage-2 `ConstantInfo` representations of total recursion (`structural`, `WF`, `mutual`, `private`, `where`) against `partial def` and `opaque`. |
| `support/PatchedTrustedBoundaryPrototype.lean` | SHA-256 `ca20c8df946a628abef8ebcb43b89a87a6a31cbf9ebfb89d63ae06e9a2a1607e` | Preserved prototype of `TrustedBoundary.lean` implementing `sameRealizedThmHeader`, `pendingPartials` `Compiler.isUnsafeRecName?` verification, `toolchainLibrary` admission, multi-crate `"crates"` verification, and `collectLocalClosure`. |

All empirical timings were recorded on an `x86_64-unknown-linux-gnu` host using
the pinned `leanprover/lean4:v4.34.1` toolchain (`bin/lean` under
`leanprover--lean4---v4.34.1`). Exact constant counts (`1,020` exported
modules, `1,138` private modules, `108` / `119` duplicate realized theorems,
`804` `._unsafe_rec` companions, `15` total axioms) apply specifically to
`leanprover/lean4:v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`). The
structural invariants—that `realizeConst` duplicates are `.thmInfo`
declarations governed by `subsumesInfo`, that total computable recursive
definitions emit `<base>._unsafe_rec` paired with a `.defnInfo(safety = .safe)`
base constant, and that `type_checker::reduce_native` is gated on
`Lean.reduceBool` and `Lean.reduceNat`—apply to any Lean 4 revision whose
`Lean/Environment.lean`, `Lean/Elab/PreDefinition/`, and
`src/kernel/type_checker.cpp` preserve those definitions.

---

## Findings

### Finding 1: Baseline `anneal-audit` Architecture and Complete Inventory of `Init` and `Std` in Lean `v4.34.1`

Basis: `source` + `execution`

#### 1.1 Two-Layer Enforcement in `anneal-audit` and `TrustedBoundary.lean`

In `joshlf/anneal@24367bd1a8c784f2578535954f9915e24894a56f` (and the
skeleton-branch auditor `e75556f5767705404404c0675c6d2d9bcee41d6f`), boundary
validation is split between a Rust host orchestrator
(`trusted/audit/src/lib.rs`) and a Lean inspector
(`trusted/audit/TrustedBoundary.lean`):

| Layer & Phase | Source Location | Enforced Invariants |
| :--- | :--- | :--- |
| **Rust Host & Lock Verification** | `trusted/audit/src/lib.rs:514-911, 1026-1748` | Verifies `trusted/lean/foundation-lock.json` (`schema_version == 3`), SHA-256 digests of regular non-symlinked `bin/lean`, `bin/lake`, and all 51 locked `lib/lean/Init/*.olean` files, `AUDIT_SOURCE_FILES` digests against `EMBEDDED_BOUNDARY_SCRIPT`, Cargo manifest hygiene (forbidding build scripts and proc-macros), Lakefile hygiene, `.olean` freshness (`olean_mtime >= src_mtime`), and a comment-stripped textual forbidden-token pre-filter. |
| **Phase 1: `"preflight"` (Source Syntax & Trust Table)** | `trusted/audit/TrustedBoundary.lean:212-500, 999-1010` | Imports only the locked foundation parser environment (`trustLevel := 0`, `loadExts := true`), parses each `.lean` source file via `Parser.parseHeader` and `Parser.parseCommand`, requires an explicit `prelude` header without `module`/`public`/`meta`/`all` modifiers, restricts top-level commands to `commandKinds` and attributes to `allowedAttributeNames` (`simp`, `instance`, `reducible`, `semireducible`, `irreducible`, plus `@[vetted]` and `@[candidate <feat>]` in `Trusted.*`), forbids `unsafe`, `partial`, `meta`, `axiom`, `example`, `coinductive`, `open scoped`, `set_option`, `by_elab`, `run_tac`, `native_decide`, `decide +native`, and `deriving`, and extracts `(fullDeclarationName, trustStatus)` pairs. |
| **Phase 2: `"audit"` (`.olean` Inventory, Non-Contamination, Closure & Replay)** | `trusted/audit/TrustedBoundary.lean:501-997, 1011-1018` | Loads compiled `.olean` artifacts from explicit runner paths (`arts`) at `trustLevel := 0`, `plugins := #[]`, `loadExts := false`, and `level := .private` (`setExporting false`). Verifies the module import DAG (`validateGraph`), declaration provenance and body presence (`verifyAndCollectLocals`), two-color `@[vetted]` vs. `@[candidate <feat>]` non-contamination (`checkTrustedNonContamination`), `<mirMod>.crate : Trusted.Crate` and `<proofMod>.verify_crate : Trusted.CrateTheorem <mirMod>.crate` envelope shapes, axiom closure (`{Classical.choice, Quot.sound, propext}`), demand-driven candidate feature reachability (`collectActiveCandidateFeatures`), and fresh kernel replay (`base.toKernelEnv.replay`). |

#### 1.2 Complete Constant Inventory of `Init` and `Std` in Lean `v4.34.1`

Running `probe_std_inventory.lean` and `support/DiagnoseRealizeConst.lean`
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
   ` unsafeIntro`, `isScalarObj`) and `Init.Core` (4 axioms: `propext`,
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
     `Init.Data.Int.OfNat` + `Std.Data.ExtHashMap` closure (used in our
     multi-crate verification benchmark): 285 base modules (51 locked `Init.*`
     + 234 `toolchainLibrary` modules).
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
   Inside the module import loop (`Lean/Environment.lean:2335-2344`):
   ```lean
   match privateConstantMap.getThenInsertIfNew? cname cinfo with
   | (cinfoPrev?, constantMap') =>
     privateConstantMap := constantMap'
     if let some cinfoPrev := cinfoPrev? then
       if subsumesInfo privateConstantMap cinfo cinfoPrev then
         privateConstantMap := privateConstantMap.insert cname cinfo
       else if !subsumesInfo privateConstantMap cinfoPrev cinfo then
         throwAlreadyImported s const2ModIdx modIdx cname
   const2ModIdx := const2ModIdx.insertIfNew cname modIdx
   ```
   Because `subsumesInfo` returns `true` for any two `.thmInfo` entries with
   identical `(name, type, levelParams, all)`, `privateConstantMap.insert cname
   cinfo` **overwrites** `env.checked` with the **last** module's `ConstantInfo`
   (`M₂`), while `const2ModIdx.insertIfNew cname modIdx` retains the **first**
   module's index (`M₁`)!
4. **Matching Subsumption Rule in `Lean.Kernel.Environment.replay'`
   (`src/lean/Lean/Replay.lean:89-96`):** Lean's kernel replay implementation
   contains the identical `.thmInfo` header check:
   ```lean
   -- src/lean/Lean/Replay.lean:89-96
   if let some info' := (← read).env.find? name then
     match info, info' with
     | .thmInfo info, .thmInfo info' =>
       if info.name == info'.name && info.type == info'.type &&
          info.levelParams == info'.levelParams && info.all == info'.all then
         return
     | _, _ => pure ()
   ```

#### 2.2 Complete Quantitative Classification Across `Init` and `Std`

Running `support/DiagnoseRealizeConst.lean` establishes the following exact
counts across all `Init` and `Std` modules in Lean `v4.34.1`:

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

At `level := .exported`, the 108 duplicate `.thmInfo` constants partition by
realized suffix into 63 `<fn>.eq_<n>` lemmas (58.3%), 30 `<fn>.congr_simp`
lemmas (27.8%), 8 `<fn>.eq_def` lemmas (7.4%), 4 `<fn>.induct_unfolding` lemmas
(3.7%), and 3 `<fn>.{congr_eq_1, congr_eq_2, fun_cases_unfolding}` lemmas
(2.8%). At `level := .private`, the 119 duplicates partition into 68
`<fn>.eq_<n>`, 32 `<fn>.congr_simp`, 10 `<fn>.eq_def`, 5
`<fn>.induct_unfolding`, and 4 `<fn>.{congr_eq_1, congr_eq_2,
fun_cases_unfolding}` lemmas.

#### 2.3 Complete Table of Category B Duplicates (Differing `value? true`)

Every Category B duplicate across `Init` and `Std` (`9` at `.exported`, `12` at
`.private`) is a realized `.thmInfo` whose proof terms in different modules are
identical except for the `_private.<Module>.0.` prefix on a nested realized
helper:

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

In unpatched `TrustedBoundary.lean:843-852`, `verifyAndCollectLocals` requires
`stored.type == ci.type && stored.value? true == ci.value? true`,
`!locals.contains ci.name`, and `orig == m.module` for every `ci` in
`data.constants`. Whenever a diamond import triggers `realizeConst` across
two base modules, a base module and a local module, or two incomparable local
modules (such as `Upstream.Proof` and `Downstream.Proof`), those checks fail
because `orig` points to the first realizing module while `stored` holds the
last realizing module's proof term.

Replacing the unconditional equality check with `sameRealizedThmHeader`
(`support/PatchedTrustedBoundaryPrototype.lean:889-896`):

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

preserves soundness across all threat vectors:

1. **Restricted strictly to `.thmInfo` (`Prop` theorems):** Computational
   definitions (`.defnInfo`), inductive types (`.inductInfo`), constructors
   (`.ctorInfo`), recursors (`.recInfo`), axioms (`.axiomInfo`), and opaques
   (`.opaqueInfo`) never satisfy `sameRealizedThmHeader` and must still satisfy
   exact `stored.value? true == ci.value? true`, `orig == m.module`, and
   `!locals.contains ci.name`.
2. **Proof irrelevance in Lean's kernel:** Two `.thmInfo` declarations with
   identical `name`, `type`, `levelParams`, and `all` prove the exact same
   proposition `ta.type` and are definitionally interchangeable in the kernel.
3. **Authoritative `stored` verification:** Whenever a local module contains a
   realized `.thmInfo` duplicate, `verifyAndCollectLocals` inserts `stored`
   (the authoritative `ConstantInfo` from `env.checked.get`) into `locals`
   (`support/PatchedTrustedBoundaryPrototype.lean:988-990`). Consequently, both
   the axiom closure walk (`closure`) and kernel replay
   (`base.toKernelEnv.replay`) inspect and typecheck the exact proof term
   `stored.value? true` present in `env.checked`.

---

### Finding 3: Distinguishing Compiler-Generated `<base>._unsafe_rec` from User `partial def`

Basis: `source` + `execution` + `derived`

#### 3.1 Stage-2 `ConstantInfo` Representation of Total vs. Partial Recursion

Running `support/ProbePartialVsTotal.lean` on Lean `v4.34.1` demonstrates the
exact stage-2 `ConstantInfo` entries emitted into `env.checked` and
`ModuleData.constants` for every recursion and opacity construct:

| Source Construct | Base Constant (`<name>`) | Companion Constant (`<name>._unsafe_rec`) |
| :--- | :--- | :--- |
| Structurally recursive `def totalStruct` | `.defnInfo` (`safety = .safe`, `isPartial = false`, `isCEnv = true`) | `.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some totalStruct`) |
| Well-founded recursive `def totalWF` | `.defnInfo` (`safety = .safe`, `isPartial = false`, `isCEnv = true`) | `.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some totalWF`) |
| Mutual well-founded `def mutualEven` / `mutualOdd` | `.defnInfo` (`safety = .safe`, `isPartial = false`, `isCEnv = true`) | `.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some mutualEven` / `mutualOdd`) |
| Private recursive `private def privRec` | `.defnInfo` (`safety = .safe`, `isPartial = false`, `isCEnv = true`) | `.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some _private...privRec`) |
| Nested `where` recursive `def withWhere.loop` | `.defnInfo` (`safety = .safe`, `isPartial = false`, `isCEnv = true`) | `.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some withWhere.loop`) |
| **User-written `partial def userPartial`** | **`.opaqueInfo` (`isUnsafe = false`, `isPartial = false`, `isCEnv = true`)** | **`.defnInfo` (`safety = .partial`, `isPartial = true`, `isCEnv = false`, `isUnsafeRecName? = some userPartial`)** |
| User-written `opaque userOpaque` | `.opaqueInfo` (`isUnsafe = false`, `isPartial = false`, `isCEnv = true`) | *(none)* |

#### 3.2 Primary-Source Elaborator Trace and Post-Loop Verification Rule

1. **Why total computable recursive definitions emit `<base>._unsafe_rec`:**
   In `src/lean/Lean/Elab/PreDefinition/Structural/Main.lean:195-200` and
   `src/lean/Lean/Elab/PreDefinition/WF/Main.lean:77-85`, after adding the
   logical kernel definition of `<base>` (constructed via `.brecOn` or
   `WellFounded.fix`) as a safe `.defnInfo` (`safety := .safe`), the elaborator
   calls `addAndCompilePartialRec preDefs`
   (`src/lean/Lean/Elab/PreDefinition/Basic.lean:280-296`) whenever the
   definition is computable (`shouldGenCodeFor`). `addAndCompilePartialRec`
   creates `<base>._unsafe_rec` (`Compiler.mkUnsafeRecName`) with
   `safety := DefinitionSafety.partial` (`ci.isPartial == true`) so the LCNF
   compiler (`src/lean/Lean/Compiler/LCNF/ToLCNF.lean:445-447`) compiles direct
   recursive equations instead of unfolding `WellFounded.fix` or `.brecOn` at
   runtime.
2. **Why `ci.isPartial` companions must be excluded from `locals` before
   `toKernelEnv.replay`:** Because `<base>._unsafe_rec`'s body directly calls
   `<base>._unsafe_rec` (`usedConstants` contains itself), passing it to
   `Kernel.Environment.replay` fails with an unknown-constant error. Lean's
   `src/lean/Lean/Replay.lean:160-163, 181-196` defines
   `ConstantInfo.isCEnv (ci : ConstantInfo) : Bool := !(ci.isUnsafe ||
   ci.isPartial)` and excludes `!ci.isCEnv` constants from `mkReplayMap`.
3. **Why checking `pendingPartials` after the module loop avoids hash-trie
   ordering sensitivity and rejects user `partial def`:** Because `mkModuleData`
   populates `data.constants` via `kenv.constants.foldStage2` over a
   `PersistentHashMap` trie (`src/lean/Lean/Environment.lean:1868-1872`),
   `<base>._unsafe_rec` can appear before `<base>` inside `data.constants`.
   Recording `(ci.name, m.module, isTrusted)` in `pendingPartials` during the
   module scan and verifying after the loop
   (`support/PatchedTrustedBoundaryPrototype.lean:1002-1009`):
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
   admits all total recursive definitions while rejecting any user-written
   `partial def` (whose `<base>` in `locals` is `.opaqueInfo` from
   `Lean/Elab/PreDefinition/Main.lean:32-35`, failing the `some (.defnInfo
   baseVal)` pattern match even if Phase 1 syntax preflight were bypassed).
4. **Effect on `theory/Anneal/FunctionalTranslation.lean`:** Applying this
   rule allows removing all **26 `noncomputable` modifiers** across the
   8,315-line `theory/Anneal/FunctionalTranslation.lean` (which emits 9
   `._unsafe_rec` compiler companions: `buildPureSymStateAux._unsafe_rec`,
   `computePlanAux._unsafe_rec`, `countUpLoopPlan._unsafe_rec`,
   `evalSymState._unsafe_rec`, `evalSymStateToReturn._unsafe_rec`,
   `extractSymArgsAux._unsafe_rec`, `lookupLoanCurVals._unsafe_rec`,
   `noAliasBefore._unsafe_rec`, and `noMutAliasBefore._unsafe_rec`), enabling
   symbolic execution proofs to discharge `evalSymState` obligations directly by
   kernel `rfl`.

---

### Finding 4: C++ Kernel Soundness Analysis of `@[implemented_by]`, `@[extern]`, and `@[csimp]`

Basis: `source` + `derived`

Across the 969 unlocked `Init.*` and `Std.*` modules in Lean `v4.34.1`, there
are 32 `@[implemented_by]` overrides (such as
`Std.Data.DTreeMap.Internal.Impl.{balance, balanceL, balanceR}` and 11
bitblaster overrides in `Std.Tactic.BVDecide.Bitblast.BVExpr.Basic`), 568
`@[extern]` bindings, and 36 `@[csimp]` theorems (such as
`BitVec.flattenList_eq_flattenListFast`). Direct inspection of the Lean
`v4.34.1` C++ kernel (`src/kernel/`) proves that these attributes cannot affect
kernel typechecking or definitional equality when `Lean.trustCompiler`,
`Lean.ofReduceBool`, and `Lean.ofReduceNat` are excluded from the axiom
closure:

1. **Storage in Environment Extensions Outside `m_constants`:**
   `@[implemented_by]` (`src/lean/Lean/Compiler/ImplementedByAttr.lean:15-21`),
   `@[extern]` (`src/lean/Lean/Compiler/ExternAttr.lean:117-125`), and
   `@[csimp]` (`src/lean/Lean/Compiler/CSimpAttr.lean:38-55`) are stored in
   environment extensions (`irBaseExts`). Standard kernel delta-reduction
   (`type_checker::unfold_definition_core` at
   `src/kernel/type_checker.cpp:693-721` and `lazy_delta_reduction` at
   `src/kernel/type_checker.cpp:1057-1135`) looks up `m_env.find(c)` in
   `m_constants` (`src/kernel/environment.h:61-147`) and unfolds the logical
   kernel definition `constant_info::get_value()`, never consulting
   `@[implemented_by]`, `@[extern]`, or `@[csimp]`.
2. **Exclusive Kernel Entrypoint to Native/IR Execution (`reduce_native`):**
   In `src/kernel/type_checker.cpp:614-635`:
   ```cpp
   optional<expr> type_checker::reduce_native(expr const & e) {
       if (!is_app(e)) return none_expr();
       expr const & fn = app_fn(e);
       if (!is_constant(fn)) return none_expr();
       expr arg = whnf(app_arg(e));
       if (!is_constant(arg)) return none_expr();
       if (const_name(fn) == get_lean_reduce_bool_name()) {
           return some_expr(ir::lean_eval_const(env(), const_name(arg), m_Partial));
       } else if (const_name(fn) == get_lean_reduce_nat_name()) {
           return some_expr(ir::lean_eval_nat_const(env(), const_name(arg), m_Partial));
       }
       return none_expr();
   }
   ```
   `reduce_native` is called at only two sites in the entire C++
   kernel—`whnf_core` (`type_checker.cpp:761`) and `lazy_delta_reduction_step`
   (`type_checker.cpp:1101-1105`)—and only when reducing an application of
   `Lean.reduceBool` or `Lean.reduceNat`.
3. **Complete Gating by `Lean.trustCompiler`, `Lean.ofReduceBool`, and
   `Lean.ofReduceNat`:** In `src/lean/Init/Core.lean:2338-2385`,
   `Lean.reduceBool` and `Lean.reduceNat` are `opaque` definitions whose
   `OpaqueVal.value` (`ci.value? (allowOpaque := true)`) references
   `axiom Lean.trustCompiler : True`, while `Lean.ofReduceBool` and
   `Lean.ofReduceNat` are `axiom` declarations in `Init.Core`. Because
   `declarationEdges` (`support/PatchedTrustedBoundaryPrototype.lean:586-602`)
   traverses `ci.value? (allowOpaque := true)` and `closure` (`lines 616-637`)
   restricts reachable axioms to `{Classical.choice, Quot.sound, propext}`, no
   audited declaration or proof can transitively reference `Lean.reduceBool`,
   `Lean.reduceNat`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, or
   `Lean.trustCompiler`. Therefore, `type_checker::reduce_native` is never
   called during kernel typechecking or replay of an audited closure, and
   `@[implemented_by]`, `@[extern]`, and `@[csimp]` in `Init.*` and `Std.*` are
   100% inert in the kernel.

---

### Finding 5: Two-Tier `toolchainLibrary` Admission, Closure-Only Replay (`collectLocalClosure`), and Multi-Crate DAG Verification

Basis: `source` + `execution`

#### 5.1 Replay Strategy Comparison: Module-Wide Replay vs. Closure-Only Replay

When `theory/` or `Proof` modules import large `Std.*` and unlocked `Init.*`
hierarchies, replaying every safe declaration of every imported non-foundation
module is dominated by thousands of unused library declarations. We benchmarked
two architectures across both a standalone 697-module `Std.Data.ExtHashMap` +
`Init.Data.BitVec.Lemmas` + `Std.Do` test (`probe_two_tier_e2e.lean`) and the
full 15-module computable `Anneal/FunctionalTranslation.lean` multi-crate DAG
(`support/PatchedTrustedBoundaryPrototype.lean`):

| Benchmark Configuration | Loaded Modules | Total Checked Constants | Replayed Declarations | Replay Wall Time | Speedup |
| :--- | ---: | ---: | ---: | ---: | ---: |
| **External `Std.*` + `Init.*` Module-Wide Replay** (replaying all safe declarations in 646 non-foundation modules) | 697 | ~74,300 | 64,862 | **62,999 ms** | 1.0× |
| **External `Std.*` + `Init.*` Closure-Only Replay** (replaying only transitive non-foundation closure of `verify_crate`) | 697 | ~74,300 | **2,121** | **1,204 ms** | **52.3×** |
| **Patched `TrustedBoundary.lean` Full Local Replay** (285 locked `foundation ++ toolchainLibrary` base + all 15 local modules) | 300 | 38,000+ | 1,897 | **1,266 ms** | 1.0× |
| **Patched `TrustedBoundary.lean` Closure-Only Local Replay (`collectLocalClosure`)** (285 base + reachable local closure of multi-crate DAG) | 300 | 38,000+ | **762** | **559 ms** | **2.26×** |

Two implementation invariants in `declarationEdges` and `collectLocalClosure`
(`support/PatchedTrustedBoundaryPrototype.lean:586-602, 902-915`) are required
for Closure-Only Replay to succeed in `Lean/Replay.lean`:

1. **Inductive and Mutual-Block Completion:** When an inductive type `I`,
   constructor `c`, or recursor `I.rec` is in the closure,
   `src/lean/Lean/Replay.lean:62-75` looks up all sibling types (`v.all`) and
   all constructors (`v.ctors`) in the replay map to reconstruct
   `Declaration.inductDecl`. Even if a proof only mentions `Or.inl`, `Or.inr`
   must be included in the replay map. `declarationEdges` guarantees this by
   adding `v.all` for `.defnInfo`, `.thmInfo`, `.opaqueInfo`, and `.recInfo`,
   `v.all ++ v.ctors` for `.inductInfo`, `v.induct` for `.ctorInfo`, and
   `rule.ctor` + `expressionEdges rule.rhs` for every recursor rule.
2. **Opaque Witness Traversal (`allowOpaque := true`):**
   `src/lean/Lean/Replay.lean:98-103` replays every `ConstantInfo.opaqueInfo`
   by typechecking both `ci.type` and `ci.value!` in the kernel
   (`addDecl (.opaqueDecl ...)`). Because `declarationEdges` calls
   `ci.value? (allowOpaque := true)`, every constant referenced inside an
   `OpaqueVal.value` witness is included in `collectLocalClosure`.

#### 5.2 End-to-End Multi-Crate DAG Verification Benchmark

We verified `support/PatchedTrustedBoundaryPrototype.lean` on a 15-module local
verification graph (`6` `Trusted` modules, `5` computable `Anneal` modules
including the 8,315-line `Anneal/FunctionalTranslation.lean` with zero
`noncomputable` keywords, `Upstream.{Mir, Proof}`, and `Downstream.{Mir,
Proof}`) on top of 285 base modules (`51` `foundation` + `234`
`toolchainLibrary` modules including `Init.Omega`, `Init.Grind`,
`Init.GrindInstances`, `Init.Data.Int.OfNat`, and `Std.Data.ExtHashMap`):

- `Upstream.Proof` proves `upstream_add_bounded_rfl` by kernel `rfl` on
  computable `evalSymState`, `upstream_add_bounded_bound_omega` by `omega`,
  `upstream_add_bounded_comm_grind` by `grind`, `upstream_ext_hashmap_lookup`
  on `Std.ExtHashMap` by `simp`, and `Upstream.Proof.verify_crate :
  Trusted.CrateTheorem Upstream.Mir.crate`.
- `Downstream.Proof` imports `Upstream.Mir`, `Upstream.Proof`, and
  `Downstream.Mir`, composing `rfl` on computable `evalSymState` with
  `Upstream.Proof.upstream_add_bounded_eval`, `grind` with
  `Upstream.Proof.upstream_add_bounded_bound_omega`, and `Std.ExtHashMap`
  lookup with `Upstream.Proof.upstream_ext_hashmap_lookup` to prove
  `Downstream.Proof.verify_crate : Trusted.CrateTheorem Downstream.Mir.crate`.

| Verification Phase / Check | Modules | Constants Checked | Replayed Local Decls | Exit Code & Result | Wall Time |
| :--- | ---: | ---: | ---: | :--- | ---: |
| **CLI Phase 1 (`"preflight"`)** (`51` `foundation` + `234` `toolchainLibrary` + `15` local `.lean` files) | 285 base + 15 source | 187 `trustDeclarations` | — | `0` (`"ok": true`) | **3,517 ms** |
| **CLI Phase 2 (`"audit"`) — Multi-Crate DAG** `[(Upstream.Mir, Upstream.Proof), (Downstream.Mir, Downstream.Proof)]` | 300 | 38,000+ (`5,312` reachable) | **762** (of 1,897) | `0` (`"ok": true`) | **8,691 ms** |
| **CLI Phase 2 (`"audit"`) — Single-Crate Downstream** `[(Downstream.Mir, Downstream.Proof)]` (`Upstream` in `theory`) | 300 | 38,000+ (`5,312` reachable) | **762** (of 1,897) | `0` (`"ok": true`) | **8,976 ms** |
| **In-Process `verifyAndCollectLocals` across all `Init` + `Std` + 15 local modules** (`level := .private`) | 1,153 | 119,595 | — | `ok` (`17` diff-val realized dups, `9` `_unsafe_rec`) | **329 ms** |
| **Negative Control 1: User `partial def badLoop` in Phase 1 (`"preflight"`)** | 285 base + 1 source | — | — | `1` (`policy:unsupported source form Lean.Parser.Command.partial`) | Rejected |
| **Negative Control 2: User `partial def badLoop` in Phase 2 (`"audit"` on `.olean`)** | 301 | — | — | `1` (`policy:unsafe/partial declaration badLoop._unsafe_rec in BadPartial`) | Rejected |

---

### Finding 6: Comparative Audit of External Kernel Checkers and Dual-Kernel Verification with `lean4export` + `nanoda_lib`

Basis: `source` + `execution`

We audited five external Lean 4 verification tools against Anneal's threat
model and benchmarked them on the `e2e_test/Proof.olean` artifact (which
transitively imports `Std.Data.ExtHashMap`, `Init.Data.BitVec.Lemmas`, and
`Std.Do`, spanning 697 modules and 3,753 transitive closure declarations):

| Checker / Pipeline | Revision / Version | Reads `.olean` Directly? | Replays `Init.Prelude`? | Enforces Axiom Allowlist & Theorem Envelope? | `reduce_native` (`native_decide`) Exposure | Wall Time on `e2e_test/Proof` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`PatchedTrustedBoundaryPrototype.lean`** | `ca20c8df946a...` (`v4.34.1`) | Yes (`importModules` with explicit `arts`) | No (pins `.olean` SHA-256 digests in `foundation-lock.json`) | **Yes:** Phase 1 syntax preflight, `@[vetted]`/`@[candidate]` non-contamination, statement-origin check, axiom allowlist | Blocked by Phase 1 syntax ban and Phase 2 ban on `Lean.trustCompiler` / `Lean.ofReduceBool` | **1.20 s** (`2,121` non-foundation closure decls); **0.56 s** (`762` local decls) |
| **Built-in `leanchecker`** (`src/lean/LeanChecker.lean`) | `5045d0056413...` (`v4.34.1`) | Yes (`withImportModulesConst`) | Yes (with `--fresh`) | **No:** permits `sorryAx`, `Lean.trustCompiler`, and arbitrary user `axiom` declarations; does not inspect theorem statements | Exposed if `Lean.ofReduceBool` is present in the module closure | **4.65 s** (`--fresh` on all 697 modules); **0.07 s** (single module) |
| **`leanprover/lean4checker`** | `91a7f0e8e9df...` | Yes | Yes (`--fresh`) | **No** (superseded upstream by built-in `bin/leanchecker`; see `README.md:1-14`) | Same as built-in `leanchecker` | Superseded by `bin/leanchecker` |
| **`leanprover/comparator`** | `865edc14486c...` | Via `lean4export` | Yes (via `nanoda_bin`) | **Yes:** compares challenge vs. solution theorem types (`Compare.lean:45-62`), checks axioms (`Axioms.lean:15-36`), forbids upstream attribute/instance modifications (`Compare.lean:24-43`) | None (delegates kernel checking to `nanoda_bin`) | Designed for challenge-solution Lake packages in `landrun` sandbox |
| **`lean4export` + `nanoda_lib` (`nanoda_bin`)** | `df81913eee55...` + `8de7e0c4ed30...` (`v0.4.31`) | `lean4export` reads `.olean`; `nanoda_bin` reads NDJSON | **Yes** (starts from empty `Env` in `src/env.rs`) | **Yes:** `nanoda_bin` enforces `permitted_axioms` (`src/parser.rs:344-368`) and pretty-prints target declarations (`pp_declars`) | **Zero exposure:** `nanoda_lib` has no compiler, no IR interpreter, and no `reduce_native` | **1.33 s total** (`0.85 s` export of `325,834` NDJSON lines + `0.48 s` 4-thread check of `3,753` decls) |
| **`digama0/lean4lean`** | `67f63b0c8189...` (`v4.33.0-rc2`) | Yes (`Lean4Lean/Replay.lean`) | Yes (`--fresh`) | Validates primitive shapes (`Lean4Lean/Primitive.lean:11-97`: `Bool`, `Nat`, `String`, `Quot`, `Char`); no axiom allowlist or target theorem check | None in pure Lean typechecker | Targets `v4.33.0-rc2` (~2–3× slower than C++ kernel) |

Key primary-source findings for dual-kernel integration (`lean4export` +
`nanoda_lib`):

1. **Opaque Witness Export (`Export.lean:212-222`):** For every
   `ConstantInfo.opaqueInfo` in the transitive closure, `lean4export` (format
   `v3.1.0`) exports `{"opaque": {"name": ..., "levelParams": ..., "type": ...,
   "value": ...}}` including the opaque constant's inhabitedness witness
   `val.value`.
2. **Conservative Opaque Handling in `nanoda_lib` (`src/tc.rs:141-155`):**
   `nanoda_lib` typechecks `Declar::Opaque` by inferring the type of `val.value`
   and verifying definitional equality with `val.type`, then stores the
   declaration as an un-unfoldable `Opaque` in `Env` (never unfolding `Opaque`
   during `whnf`).
3. **Primitive Reduction Shape Validation (`src/env.rs:180-375`):** Before
   enabling `Quot`, `Nat`, or `String` kernel reductions from an empty
   environment, `nanoda_lib` verifies that the exported `Init.Prelude`
   declarations of `Quot`, `Nat`, `String`, `Char`, `Bool`, and `List` have
   their exact expected constructor and universe signatures.

---

## Boundaries

To prevent future agents from over-generalizing these results, the following
boundaries distinguish what is established from what is known not to apply,
unsupported, or not examined:

1. **Known Not to Apply — Built-in `leanchecker --fresh` Is Not a Substitute
   for `TrustedBoundary.lean`:** While `leanchecker --fresh` replays all
   module constants from `mkEmptyEnvironment` in 4.65 s, it does not enforce an
   axiom allowlist (`sorryAx`, `Lean.trustCompiler`, and user `axiom bad :
   False` pass with exit code `0`), does not verify `<proofMod>.verify_crate`'s
   type against `Trusted.CrateTheorem <mirMod>.crate`, and does not check
   `@[vetted]` vs. `@[candidate <feat>]` non-contamination.
2. **Known Not to Apply — `sameRealizedThmHeader` Does Not Permit Duplicate
   `.defnInfo` or `.opaqueInfo` Declarations:** In Lean `v4.34.1`,
   `subsumesInfo` (`Lean/Environment.lean:2273-2275`) also includes a
   `.defnInfo` branch (`subsumesValue`) for compiler definitions. Across all
   1,020 exported and 1,138 private modules of `Init` and `Std`, zero
   `.defnInfo` duplicates occur (`108 / 108` and `119 / 119` are `.thmInfo`).
   `sameRealizedThmHeader` deliberately restricts duplicate tolerance to
   `.thmInfo` so computational definitions in `Trusted`, `Anneal`, and `Mir`
   must always have unique origins and bit-for-bit identical values.
3. **Known Not to Apply — Relaxing `@[implemented_by]`, `@[extern]`, or
   `opaque` in Tier 1 (`Trusted` and `Mir`):** Our C++ kernel isolation proof
   (Finding 4) establishes that `@[implemented_by]`, `@[extern]`, `@[csimp]`,
   and `opaque` in Tier 2 (`Std.*`, unlocked `Init.*`, and `theory/`) cannot
   forge a proof of a Tier 1 theorem when `Lean.trustCompiler` is banned. That
   permission does **not** extend to Tier 1 (`trusted/lean/` and `Mir.lean`),
   where an `opaque` definition in the theorem statement could conceal a
   vacuous specification (`opaque Spec : Prop := True`) and where Phase 1
   syntax preflight must continue to forbid `opaque`, `partial`, `unsafe`,
   `@[extern]`, and `@[implemented_by]`.
4. **Unsupported — `Lean4Lean` on Lean `v4.34.1` Without Upstream Migration:**
   `digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` targets Lean
   `v4.33.0-rc2` and does not build unmodified against Lean `v4.34.1`.
5. **Not Examined — Cross-Version `Init` + `Std` Duplicate Counts Beyond Lean
   `v4.34.1`:** The exact counts of 108 exported / 119 private duplicate
   realized theorems and 9 exported / 12 private differing-value `.thmInfo`
   declarations were measured on `leanprover/lean4:v4.34.1`
   (`5045d0056413266e57c625dcd7c365b10e377c52`). Upgrading the Lean toolchain
   requires re-running `support/DiagnoseRealizeConst.lean` (see
   **Revalidation**).

---

## Evidence

All primary-source coordinates, commit revisions, and SHA-256 digests are
recorded in `support/source-manifest.json` and summarized below.

### 1. Primary Source Code Coordinates

- **`joshlf/anneal`** (main revision `24367bd1a8c784f2578535954f9915e24894a56f`,
  skeleton worktree `e75556f5767705404404c0675c6d2d9bcee41d6f`):
  - `trusted/audit/src/lib.rs:479-911, 1026-1834` (SHA-256
    `38680775417451dde2154702669fe807e0d96780d45cf1c44dea9e0f51f1c4d9`): Host
    toolchain lock verification, Cargo/Lake hygiene checks, source scanner, and
    cached `trusted-boundary` binary execution.
  - `trusted/audit/TrustedBoundary.lean:1-1014` (SHA-256
    `d2124ac0c7b07af7cafd6b6caeaabd2db962ff3c00163e0c63091cf4bda42d77`):
    Baseline two-phase `"preflight"` and `"audit"` kernel-environment inspector.
  - `trusted/lean/foundation-lock.json:1-1335` (SHA-256
    `37f780b6257d0bc99fd5d7d3d0a1f16d168ef066a2a01466f4076f080d3425d2`):
    Schema v3 lockfile pinning `leanprover/lean4:v4.34.1` and 51 `Init.*`
    modules.
  - `theory/Anneal/FunctionalTranslation.lean:1-8315` (SHA-256
    `9b40696b6b504a67bc569042df3db5a9e08ac42beab65fb874bb0bac9a595385`):
    Plan-guided symbolic evaluator (`evalSymState`, `computePlanAux`, and 24
    companion definitions).
- **`leanprover/lean4`** (`v4.34.1`, commit
  `5045d0056413266e57c625dcd7c365b10e377c52`):
  - `src/lean/Lean/Environment.lean:1183-1197, 1858-1885, 2268-2283, 2332-2348,
    2709-2783` (SHA-256
    `ee364e4788ce0560c87f621eeb3c4c3dfec62e8db4e15e099fd80e6adc533b86`):
    `setMainModule`, `toKernelEnv`, `mkModuleData` (`foldStage2`),
    `subsumesInfo`, `finalizeImport` (`privateConstantMap` vs. `const2ModIdx`),
    and `realizeConst`.
  - `src/lean/Lean/Meta/Basic.lean:2727-2765` (SHA-256
    `942fef8c68f6076188691c4698e83789e695e8a59dfadafc38c658f3ab03a7b4`):
    `Lean.Meta.realizeConst`.
  - `src/lean/Lean/Replay.lean:62-103, 160-196` (SHA-256
    `c434b5b2bc5047ca58d4a095fcf1d9935d413c788ae98a4f21948e6a95ca3fb0`):
    Inductive block reconstruction, `.thmInfo` header deduplication,
    `replayOpaque`, `ConstantInfo.isCEnv`, and `mkReplayMap`.
  - `src/lean/Lean/Elab/PreDefinition/Basic.lean:280-296, 380-416` (SHA-256
    `46a2876ccbe1efc4cc491dc24658fea5e972544a64da888334fe2ffcc9c1a5c7`),
    `src/lean/Lean/Elab/PreDefinition/Main.lean:20-36` (SHA-256
    `b384fe2a3fd637f36194cab22821440871e9112d700a8dbb1c4c7392fe399647`),
    `src/lean/Lean/Elab/PreDefinition/Structural/Main.lean:195-200` (SHA-256
    `8a86ae2d1bae7f1b6c3e52a86f20e3460eecf0dbb7f7a891a16f89971d36be29`), and
    `src/lean/Lean/Elab/PreDefinition/WF/Main.lean:77-85` (SHA-256
    `cc673e422dd83756dda6cfc04ea3a02f3aae04dc00b37d11e61e18b6cde0b01d`):
    Elaboration of total vs. `partial` recursion and emission of
    `<base>._unsafe_rec`.
  - `src/lean/Init/Core.lean:2338-2385` (SHA-256
    `6218a9825a0ce51a6bbe3949ec7a86c4406f4f216bd3cd1262736cfc1c997c54`):
    `Lean.trustCompiler`, `Lean.reduceBool`, `Lean.reduceNat`,
    `Lean.ofReduceBool`, and `Lean.ofReduceNat`.
  - `src/kernel/type_checker.cpp:99-105, 614-635, 693-721, 761, 1057-1135`
    (SHA-256
    `5312a8f02318d6e3fe7eca68bf3525d5f3558fa98f5737612b52cac2e588c447`),
    `src/kernel/environment.cpp:150-355` (SHA-256
    `6748cf9368a16b7e4fd8546accc78f98874fb69323934b21c796e722dad136b2`), and
    `src/kernel/environment.h:61-147` (SHA-256
    `95e9b7aad9f138830197972c1812ca206317dae059ace9b7815674beec8500ed`): C++
    kernel `infer_constant`, `reduce_native`, `unfold_definition_core`, and
    `lazy_delta_reduction`.
- **External Kernel Checkers:**
  - `leanprover/lean4export@df81913eee5519d5a88ae5b0fd701b5298cc29ab`:
    `Export.lean:1-438` (SHA-256
    `6e9f24262253678960b05b8392a1774a3cbf36b21ed2fc1b834906659b8ca95a`).
  - `ammkrn/nanoda_lib@8de7e0c4ed3052745a7f8725164efd9e76d84c56` (`v0.4.31`):
    `src/parser.rs:344-368` (SHA-256
    `d84b01b2a3ac5b5598e63e5b06d31d6fed3ca18859086eee97fd3e07b6fd6748`),
    `src/env.rs:180-328` (SHA-256
    `52c1593f0e08c4e7b9b9f8a97e48bfdde1d449253bf0c3e4967321b46dbece01`), and
    `src/tc.rs:141-155` (SHA-256
    `fcee3a4e6e7581c5aedebba7100b26c9fe8ba067a88d70ae2ad3d34644a28d4b`).
  - `leanprover/comparator@865edc14486c3388e9225daa971da8e157488c3e`:
    `Comparator/Compare.lean:24-62` (SHA-256
    `9bc34cb7de5a069a6fef7f3b13b20fea22f1d52603f74320a93d519b735ad3dd`) and
    `Comparator/Axioms.lean:15-36` (SHA-256
    `863c5e1329811be0427880e08c171de733343491c5a3619b5dbf2e12b34c6125`).
  - `leanprover/lean4checker@91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`:
    `README.md:1-14` (SHA-256
    `2560c266894dd699a83b8a6f6359bc251a03aa76f46c4f9a78801f39505b25a3`).
  - `digama0/lean4lean@67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`:
    `Lean4Lean/Primitive.lean:11-97` (SHA-256
    `af331c517b78d805ae74c10332f8cf8deb14428d798601ec964e6c5410258afe`).

### 2. Preserved Support Artifacts in `support/`

| File Path | Lines | Bytes | SHA-256 Digest | Purpose |
| :--- | ---: | ---: | :--- | :--- |
| `support/DiagnoseRealizeConst.lean` | 225 | 10,154 | `01b13a9843828c664fe79ad44052fa280bbc554fe06a9d6dd25ba4dda4ce930b` | Loads `Init` + `Std` at `level := .private`, enumerates all 119 duplicate realized constants, verifies `const2ModIdx` vs. `env.checked` retention, and prints all 12 differing-value `.thmInfo` constants and their `_private.<Mod>.0.` splitters. |
| `support/ProbePartialVsTotal.lean` | 134 | 5,120 | `ac32784cb3edb4e26d4a933d62f778976901367f599e33728a8866735359a8a6` | Elaborates structural, well-founded, mutual, `private`, and `where` total recursive `def`s alongside `partial def` and `opaque`, printing their stage-2 `ConstantInfo` kinds, `isPartial`, `isCEnv`, and `isUnsafeRecName?` base kinds. |
| `support/PatchedTrustedBoundaryPrototype.lean` | 1,214 | 64,985 | `ca20c8df946a628abef8ebcb43b89a87a6a31cbf9ebfb89d63ae06e9a2a1607e` | Standalone prototype of `TrustedBoundary.lean` implementing `sameRealizedThmHeader`, `pendingPartials` `Compiler.isUnsafeRecName?` validation, `toolchainLibrary` admission, multi-crate `"crates"` support, and `collectLocalClosure`. |
| `support/source-manifest.json` | 296 | 9,532 | — | Machine-readable manifest of all inspected repositories, revisions, file paths, byte counts, line counts, and SHA-256 digests. |

---

## Revalidation

To revalidate the preserved Lean `v4.34.1` probes from the root of this report
package
(`reports/anneal-audit-std-realizeconst-closure-replay-and-nanoda-2026/`), run:

```bash
# 1. Verify that all three support Lean files typecheck cleanly with zero warnings:
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  support/DiagnoseRealizeConst.lean
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  support/ProbePartialVsTotal.lean
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  support/PatchedTrustedBoundaryPrototype.lean

# 2. Run the Init + Std duplicate realized-constant diagnostic probe:
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  --run support/DiagnoseRealizeConst.lean
```

Confirm that:

1. `support/ProbePartialVsTotal.lean` reports
   `defnInfo(safety=Lean.DefinitionSafety.safe)` for the base constant of every
   total recursive `def` (`totalStruct`, `totalWF`, `mutualEven`, `mutualOdd`,
   `_private...privRec`, `withWhere.loop`) and `opaqueInfo(isUnsafe=false)` for
   `userPartial`.
2. `support/DiagnoseRealizeConst.lean` reports `1138` modules loaded at
   `level := .private`, `119` duplicate constant names (`119 / 119` of kind
   `thm`, `0` with differing `type`/`levelParams`/`kind`/`all`), `107` with
   identical `value? true`, and `12` with differing `value? true`.

Revalidate this report whenever:

1. Anneal upgrades `trusted/lean/lean-toolchain` and
   `trusted/lean/foundation-lock.json` to a new `leanprover/lean4` release, to
   confirm that `subsumesInfo` in `src/lean/Lean/Environment.lean`,
   `addAndCompilePartialRec` in `src/lean/Lean/Elab/PreDefinition/Basic.lean`,
   and `type_checker::reduce_native` in `src/kernel/type_checker.cpp` preserve
   the invariants documented in Findings 2–4.
2. `trusted/audit/TrustedBoundary.lean` or `trusted/cargo-anneal/src/audit.rs`
   modifies `verifyAndCollectLocals`, `declarationEdges`, `closure`, or the
   Phase 1 (`"preflight"`) syntax allowlists.
