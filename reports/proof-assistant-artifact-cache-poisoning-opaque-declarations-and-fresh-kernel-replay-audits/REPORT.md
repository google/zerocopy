# Proof-Assistant Artifact Cache Poisoning, Opaque Declarations, and Fresh Kernel Replay Audits

## Summary

Auditing mechanized proofs via incremental builds and syntactic axiom queries suffers from two silent, compounding soundness gaps: **vacuous artifact cache hits** and **unreported `opaque` declarations**. Direct source inspection across Lean 4 (`v4.34.1`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), `lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`), `nanoda_lib` (`v0.4.32`), Mathlib (`v4.34.1`), Rocq (`25f5b18a320e4796f181f938d3b74bebe7db4dc4`), and Isabelle (`Isabelle2025`) establishes four invariants:

1. **`lake clean && lake --no-cache build` does not force a from-source kernel rebuild in Lean `v4.34.1`.** `Package.clean` (`Lake/Config/Package.lean:424-425`) removes only `.lake/build`, leaving `.lake/cache` and `$LAKE_CACHE_DIR` intact. `--no-cache` (`LAKE_NO_CACHE`) suppresses only whole-package Reservoir/GitHub tarball downloads (`Lake/Build/Package.lean:60-70`), whereas `Package.isArtifactCacheReadable` (`Lake/Config/Monad.lean:192-193`) **defaults to `true`** and `LakeOptions.trustHash` (`Lake/CLI/Main.lean:58`) defaults to `true`. `Module.recBuildLean` (`Lake/Build/Module.lean:1014-1095`) therefore restores cached `.olean` artifacts via `restoreArtifact` (`Lake/Build/Common.lean:648-666`) without running `lean`. Moreover, `LAKE_CACHE_DIR=""` merely falls back to `<pkg>/.lake/cache` (`Lake/Config/Workspace.lean:31-35`). Parallel gaps exist in Rocq's `-vos` delayed `opaquetab` / Dune cache and Isabelle's Poly/ML heap reuse (`isabelle build -c` vs. `-f`).
2. **`importModules` with `trustLevel := 0` never re-typechecks `.olean` constants.** `finalizeImport` (`src/Lean/Environment.lean:2307-2388`) copies `ModuleData.constants` straight from compacted regions without calling `addDeclCore`, and Rocq's `objFile.ml:105-114` invokes `Marshal.from_channel` *before* verifying its 16-byte MD5 digest.
3. **`#print axioms` (`Lean.CollectAxioms`) misses `opaque` declarations and trusts precomputed `exportedAxiomsExt` summaries.** In `src/Lean/Util/CollectAxioms.lean:56-67`, `.opaqueInfo v` (`line 62`) recurses into `v.type` and `v.value` without inserting the constant name into `axioms`. Because `mkDefViewOfOpaque` (`src/Lean/Elab/DefView.lean:187-199`) desugars `opaque c : T` to `default_or_ofNonempty%`—synthesizing constructive `default` witnesses (`0`, `false`, `none`, `fun _ => default`) with **zero axioms**—and `addAndCompilePartial` (`src/Lean/Elab/PreDefinition/Main.lean:20-36`) elaborates `partial def` as `.opaqueInfo`, vendored `opaque` specs and `@[extern]` stubs yield `"does not depend on any axioms"`. Under Lean's `module` system, non-exposed `opaque` items export as `.axiomInfo` (`src/Lean/AddDecl.lean:123-127`), yet `exportedAxiomsExt` (`CollectAxioms.lean:120-146`) evaluates `#[]` in `privateEnv` and caches it for downstream `#print axioms` lookups.
4. **Fresh `trustLevel := 0` replay (`lean4checker --fresh`, `nanoda_lib`) passes vendored `opaque` stubs.** Because `environment::add_opaque` (`src/kernel/environment.cpp:211-223`) and `Kernel.Environment.replay` (`src/Lean/Replay.lean:100-101`) only check that `OpaqueVal.value : OpaqueVal.type`, closing both gaps requires a **Three-Gate Audit**: (Gate 1) cache-bypassed build (`LAKE_ARTIFACT_CACHE=false`, isolated `LAKE_CACHE_DIR`, `--no-cache --rehash`, purged build/cache trees; `DUNE_CACHE=disabled` + `-vok`; `isabelle build -f -o skip_proofs=false`), (Gate 2) fresh `trustLevel := 0` kernel replay (`lean4checker --fresh`, `lean4export` + `nanoda_lib`, `coqchk -o -axiom-free`), and (Gate 3) direct `env.checked` (not `exportedAxiomsExt`) statement- and proof-cone scanning rejecting all unexpected `.opaqueInfo`, `.axiomInfo`, `partial`/`unsafe`, and `@[extern]`/`@[implemented_by]`/`@[csimp]` declarations.

---

## Applicability

These findings govern proof-audit pipelines, build reproducibility, and TCB enforcement for:
- **Lean 4 (`v4.34.1`, `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`)**, `lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`), `lean4export` (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`), `nanoda_lib` (`v0.4.32`, `0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`), `comparator` (`865edc14486c3388e9225daa971da8e157488c3e`), and Mathlib (`v4.34.1`, `leanprover-community/mathlib4@d13f23b723b8a846827a245b89c10fc7d3f11612`).
- **Rocq (`rocq-prover/rocq@25f5b18a320e4796f181f938d3b74bebe7db4dc4`)** `.vo`/`.vos` persistence (`lib/objFile.ml`, `vernac/library.ml`) and `coqchk` (`checker/{coqchk_main,checkLibrary,checkFlags}.ml`).
- **Isabelle/HOL (`Isabelle2025`, Wenzel 2025; Berghofer & Nipkow 2000)** Poly/ML heap builds (`-c` vs. `-f`, `skip_proofs`, `export_proofs`).

### Cross-References to Adjacent Corpus Reports

- `mathlib-cache-protocol-artifact-format-and-pruning` covers Mathlib's `.ltar` format and `get`/`get!`/`get-`; this report covers Lake's generic `CacheMap` artifact cache, cache-bypass rules, and Rocq/Isabelle caches.
- `lean-environment-identity-imports-and-trust-admissions` covers `EnvironmentHeader`, `module` visibility lattices, and `debug.skipKernelTC`; this report covers `.opaqueInfo` blind spots in `CollectAxioms.lean` and Lake cache restoration.
- `proof-kernels-opaque-interfaces-and-adversarial-spec-hardening` covers kernel `.thmInfo` unfolding vs. Rocq `OpaqueDef` / Agda `OpaqueBlock`; this report covers `opaque` declarations as unmonitored trust stubs.
- `independent-proof-checkers-and-smaller-trusted-computing-bases` and `untrusted-proof-dependencies-effect-isolation-and-guarantee-verification` cover `lean4export`/`nanoda_lib` architecture, `SafeVerify` bypasses, and sandboxing; this report isolates `--fresh` vs. non-fresh replay and why kernel replay must be paired with `ConstantInfo.opaqueInfo` cone inspection.

---

## Findings

### 1. Vacuous Verification Rebuilds and Poisoning Vectors in Proof-Assistant Artifact Caches

Basis: **source + documentation + derived**

When an auditor runs an incremental build (`lake build`, `rocq compile` / Dune, `isabelle build`) to confirm that proofs hold under the current kernel and sources, cached artifacts can turn the intended verification check into a no-op file copy.

#### 1.1 Lean 4 Lake Artifact Cache, `.hash` Sidecars, and `--no-cache` Limits (`lean4@5045d005...`)

In Lean `v4.34.1`, Lake separates whole-package archive fetching from per-module artifact caching across four independent knobs:

| Mechanism | Options / Env Vars (`v4.34.1`) | Default | Effect on Kernel Checking | Primary Source |
|---|---|---|---|---|
| **Remote package build cache** (Reservoir / GitHub releases) | `--no-cache`, `--try-cache`, `LAKE_NO_CACHE` | `noCache := false` (`getTryCache` = `true`) | Downloads dependency `.lake/build` archives when `buildDir` is absent; **does not disable local artifact cache** | `Lake/CLI/Main.lean:61, 284-285`; `Lake/Config/Env.lean:38-42, 176`; `Lake/Build/Package.lean:60-70` |
| **Artifact cache read** (`isArtifactCacheReadable`) | `LAKE_ARTIFACT_CACHE`, `PackageConfig.enableArtifactCache?` | **`true`** | Restores `.olean`, `.olean.server`, `.olean.private`, `.ilean`, `.c`, `.ir`, `.ir.sig` by `inputHash` without running `lean` | `Lake/Config/Monad.lean:192-193`; `Lake/Config/Workspace.lean:133-134`; `Lake/Build/Module.lean:1014-1095` |
| **Artifact cache write** (`isArtifactCacheWritable`) | `LAKE_ARTIFACT_CACHE`, `PackageConfig.enableArtifactCache?` | `false` | Writes `CacheMap` JSONL entries and saves hard-linked/copied blobs to `lakeCache` | `Lake/Config/Monad.lean:202-203`; `Lake/Build/Common.lean:454-470, 553-556` |
| **Sidecar `.hash` trust** (`getTrustHash`) | `--rehash` / `-H` | `trustHash := true` | Returns `.hash` file text instead of hashing bytes (`computeFileHash`) | `Lake/CLI/Main.lean:58, 222, 286`; `Lake/Build/Common.lean:401-409` |
| **Cache directory** (`computeLakeCache`) | `LAKE_CACHE_DIR` | Toolchain/system cache; `""` falls back to `<pkg>/.lake/cache` | Empty string sets `noSystemCache := true` and `lakeCache? := none`, falling back to `pkg.lakeDir / "cache"` | `Lake/Config/Env.lean:48-63, 192-204`; `Lake/Config/Workspace.lean:31-35` |

Tracing `Module.recBuildLean` (`src/lake/Lake/Build/Module.lean:999-1102`) reveals five concrete poisoning/bypass vectors:

1. **`lake clean && lake --no-cache build` still hits the artifact cache:** `Package.clean` (`Package.lean:424-425`) removes only `self.buildDir` (`.lake/build`), leaving `.lake/cache` and `$LAKE_CACHE_DIR` intact. `--no-cache` disables only `Package.maybeFetchBuildCache` (`Build/Package.lean:60-70`). Because `isArtifactCacheReadable` defaults to `true` (`Monad.lean:192-193`), `fetchCore` (`Module.lean:1092-1095`) enters `fetchFromCache?` (`lines 1014-1050`), looks up `inputHash` in `CacheMap` (`Cache.lean:30-73, 121-145`), and runs `restoreArtifact` (`Common.lean:648-666`)—populating `.lake/build` without invoking `compileLeanModule`.
2. **Hard-link cache poisoning (`restoreArtifact`, `Common.lean:652-664`):** `restoreArtifact` attempts `IO.FS.hardLink art.path file` first. Although `saveArtifact` and `restoreArtifact` set `0444` permissions (`lines 466-467, 657`), hard-linked files share the cache inode; any same-UID `chmod` or `#eval` script writing `.lake/build/.../*.olean` corrupts `$LAKE_CACHE_DIR` persistently, and `CacheMap.parseCacheEntry` (`Cache.lean:57-72`) trusts unauthenticated JSONL lines.
3. **Trace-to-cache promotion (`getArtifactsUsingTrace?`, `Common.lean:545-560`):** When a pre-existing `.trace` file matches `inputHash` and `isArtifactCacheWritable` holds, Lake copies its unverified `outputs?` into `CacheMap` (`writeOutputs`, `overwrite := false`) without rebuilding.
4. **Per-package `lakefile` override precedence (`Monad.lean:193` vs. `Workspace.lean:134`):** `Package.isArtifactCacheReadable` evaluates `self.enableArtifactCache? <|> ·.enableArtifactCache?`. A dependency setting `enableArtifactCache := true` overrides `LAKE_ARTIFACT_CACHE=false`, making an isolated empty `LAKE_CACHE_DIR` and `.lake/cache` deletion mandatory alongside `LAKE_ARTIFACT_CACHE=false`.
5. **Untrusted `.hash` sidecars (`Common.lean:401-409`):** With `trustHash := true`, replacing `<Mod>.olean` without touching `<Mod>.olean.hash` preserves `inputHash` hits unless `-H` / `--rehash` is passed. (Mathlib's `lake exe cache` in `mathlib4@d13f23b7...` likewise unpacks remote `.ltar` binaries without local elaboration; see `mathlib-cache-protocol-artifact-format-and-pruning`.)

#### 1.2 Rocq `.vo`/`.vos`/Dune Caches (`rocq@25f5b18a...`) and Isabelle Heaps (`Isabelle2025`)

| Prover | Cache & Key | Unsafe / Delayed Proof Mode | Deserialization & Poisoning Hazard | Required Bypass & Audit Invocation |
|---|---|---|---|---|
| **Lean 4** (`v4.34.1`) | `.olean` + `.trace` + `CacheMap` JSONL (`inputHash`) | `debug.skipKernelTC`, `opaque`, stale `.olean` | `lean_compacted_region_read` (unchecked pointer relocation); `hardLink` sharing; `trustHash := true` | Purge `.lake/{build,cache}` + `.lake/packages/*/.lake/{build,cache}`; `LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR="$(mktemp -d)" LAKE_NO_CACHE=true lake --no-cache --rehash build` + fresh replay |
| **Rocq** (`25f5b18a...`) | `.vo`/`.vos`/`.vok` (`lib/objFile.ml`); Dune cache | `-vos` leaves `opaquetab` (`library.ml:181-235`) empty; `Admitted` | `objFile.ml:105-114` runs `Marshal.from_channel` **before** checking 16-byte MD5; `CheckLibrary` (`checkLibrary.ml:54-56`) ignores `coqc`'s unchecked bool only when checked | `DUNE_CACHE=disabled` clean `.vo` build + `coqchk -R <dir> <LogicalRoot> -o -axiom-free <Logical.Module>` (logical names, never `-admit`/`-norec`) |
| **Isabelle** (`Isabelle2025`, Wenzel 2025) | Poly/ML session heaps (`PolyML.SaveState`) | `skip_proofs=true`, `condition_proofs=true`, `quick_and_dirty=true`, `Thm.oracle` | `isabelle build -c` cleans selected sessions only while reusing cached ancestor heaps; opaque runtime heap image | `isabelle build -f -o skip_proofs=false -o condition_proofs=false -o quick_and_dirty=false <Session>` + `export_proofs=true` verification (Berghofer & Nipkow 2000, DOI `10.1007/3-540-44659-1_3`) |

---

### 2. Why Lean 4's `#print axioms` Misses `opaque` Declarations and Exported Axiom Summaries

Basis: **source + execution + derived**

#### 2.1 Kernel vs. Elaborator Treatment of `opaque` and `partial def`

1. **Kernel semantics (`src/kernel/declaration.h:147-158, 466-468`, `src/kernel/environment.cpp:211-223`):** `OpaqueVal` stores `{ name, levelParams, type, value, isUnsafe, all }`. `environment::add_opaque` verifies `value : type` (preventing `opaque p : False` without axioms), while `has_value(bool allow_opaque = false)` returns `false`, preventing `whnf` and `is_def_eq` from ever unfolding `value`.
2. **Constructive zero-axiom desugaring (`src/Lean/Elab/DefView.lean:187-199`):** `mkDefViewOfOpaque` defaults missing bodies to `default_or_ofNonempty%` (`lines 193-194`). For any `Inhabited` type (`Bool`, `Nat`, `UInt32`, `Option α`, `α → β` with `Inhabited β`), `OpaqueVal.value` synthesizes `Inhabited.default` (`false`, `0`, `fun _ => none`) using **zero axioms**.
3. **`partial def` (`src/Lean/Elab/PreDefinition/Main.lean:20-36`):** `addAndCompilePartial` elaborates the public constant `f` as `DefKind.opaque` (`.opaqueInfo` with `mkInhabitantFor` dummy body) alongside `f._unsafe_rec` (`safety := .partial`).

#### 2.2 Two Structural Blind Spots in `src/Lean/Util/CollectAxioms.lean`

```lean
-- src/Lean/Util/CollectAxioms.lean:56-67
  match env.checked.get.find? c with
  | some (.axiomInfo v)  =>
      modify fun s => { s with axioms := s.axioms.insert c }
      collectExpr v.type
  | some (.defnInfo v)   => collectExpr v.type *> collectExpr v.value
  | some (.thmInfo v)    => collectExpr v.type *> collectExpr v.value
  | some (.opaqueInfo v) => collectExpr v.type *> collectExpr v.value
```

1. **Direct `.opaqueInfo` omission (`CollectAxioms.lean:62`):** Only `.axiomInfo` inserts `c` into `s.axioms`. Walking `.opaqueInfo v` inspects `v.type` and `v.value` (`fun _ => none`) and yields zero axioms. A vendored dependency declaring `opaque decodeInsn : UInt32 → Option Insn` or `opaque validState : State → Bool` lets theorems reference uninterpreted functions while `#print axioms` prints `"does not depend on any axioms"`.
2. **Module-system `exportedAxiomsExt` caching (`AddDecl.lean:123-127` + `CollectAxioms.lean:102-146`):** Under `module`, `addDeclCore` exports non-exposed `opaqueDecl` and `defnDecl` entries publicly as `.axiomInfo` (`AddDecl.lean:126`), storing original kinds in `privateConstKindsExt` (`src/Lean/OriginalConstKind.lean:16-30`). However, `exportedAxiomsExt.exportEntriesFnEx` (`CollectAxioms.lean:128, 139`) switches to `privateEnv := env.setExporting false`—where `op` is `.opaqueInfo`—and caches `(op, #[])` in the `.olean`. Downstream `#print axioms` calls hit `ExportedAxiomsState.find?` (`lines 102-111`) and trust that `#[]` without re-walking `env.checked`.

#### 2.3 Four Unmonitored Trust Vectors

1. **Constructive uninterpreted spec stubs:** `opaque` predicates/decoders over `Inhabited` types have zero axioms and zero definitional equations, hiding vacuous or disconnected theorem statements.
2. **`@[extern]` / `@[implemented_by]` / `@[csimp]` divergence:** `@[extern "c_verify"] opaque verify : ByteArray → Bool` links unverified C at runtime while remaining an uninterpreted `.opaqueInfo` in the kernel with empty `#print axioms`.
3. **`partial def` inside specs:** `addAndCompilePartial` turns `partial def` into `.opaqueInfo`, breaking kernel transparency without triggering `#print axioms`.
4. **`debug.skipKernelTC` + stale `exportedAxiomsExt`:** `lean_add_decl_without_checking` (`AddDecl.lean:25-33`, `environment.cpp:297-301`) inserts `forged : False := True.intro` with zero `.axiomInfo` dependencies; trusting `exportedAxiomsExt` masks upstream compromises.

---

### 3. Closing Both Gaps: Cache-Bypassed Builds, Fresh `trustLevel := 0` Replay, and Opaque Cone Audits

Basis: **source + execution + derived**

#### 3.1 Why `importModules (trustLevel := 0)` Does Not Check `.olean` Proofs

Although `LEAN_BELIEVER_TRUST_LEVEL = 1024` (`src/kernel/environment.h:23`), `importModules` (`src/Lean/Environment.lean:2438-2460`) with `trustLevel := 0` invokes `finalizeImport` (`lines 2307-2388`), which inserts `ModuleData.constants` directly into `privateConstantMap`/`publicConstantMap` without ever invoking `addDeclCore`. Re-checking `.olean` files requires explicit kernel replay.

#### 3.2 Comparing `lean4checker` Default vs. `--fresh` vs. External Checkers

- **`lean4checker` default (`replayFromImports`, `lean4checker/Main.lean:14-36`):** Loads imported `.olean` dependencies via `importModulesCore` *unchecked* and replays only the target module's local constants (`parts[parts.size-1].1`). Poisoned dependency `.olean`s pass undetected.
- **`lean4checker --fresh <RootMod>` (`replayFromFresh`, `Main.lean:38-40, 120-127`):** Loads the full closure and calls `(← mkEmptyEnvironment).replay' env.constants.map₁`, replaying **every** non-`unsafe`/non-`partial` constant from `Init.Prelude` upward via `addDeclCore 0 0` (`src/Lean/Replay.lean:60`), plus `checkPostponedConstructors` / `checkPostponedRecursors` (`Replay.lean:148-165`). Note that `--fresh` rejects multiple module arguments (`Main.lean:121-123`).
- **`lean4export` + `nanoda_lib` (`comparator`):** Eliminates C++ `.olean` pointer-relocation UB and single-kernel bugs by exporting NDJSON v3.1.0 and replaying in safe Rust (`overflow-checks = true`).

#### 3.3 The Three-Gate Audit Protocol

1. **Gate 1 — Cache-Bypassed Build:** Purge `.lake/{build,cache}` and `.lake/packages/*/.lake/{build,cache}` and rebuild with `LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR="$(mktemp -d)" LAKE_NO_CACHE=true lake --no-cache --rehash build` (Rocq: `DUNE_CACHE=disabled` clean `.vo`; Isabelle: `isabelle build -f -o skip_proofs=false -o condition_proofs=false`).
2. **Gate 2 — Fresh `trustLevel := 0` Kernel Replay:** Run `lake env lean4checker --fresh <RootMod>` and/or `lean4export <RootMod> | nanoda_bin` (Rocq: `coqchk -R <dir> <LogicalRoot> -o -axiom-free <Logical.Mod>`; Isabelle: proof-term check).
3. **Gate 3 — Direct `env.checked` `ConstantInfo.opaqueInfo` & Override Cone Audit:** Because `Replay.lean:100-101` replays `.opaqueDecl` and passes `default_or_ofNonempty%`, walk `env.checked` directly (ignoring `exportedAxiomsExt`) from target theorem `T`:
   - **Statement cone (`deps(T.type)`):** Reject every `.opaqueInfo`, `.axiomInfo`, `unsafe`/`partial` safety, `privateConstKindsExt` (`getOriginalConstKind?`) mismatch under `module` builds, and `@[extern]`/`@[implemented_by]`/`@[csimp]` override; check structural equality against the pinned specification.
   - **Proof/value cone (`deps(T.type) ∪ deps(T.value)`):** Restrict `.axiomInfo` to `{propext, Classical.choice, Quot.sound}`, reject all `.opaqueInfo` and `partial`/`unsafe`/override declarations, while permitting unrelated `partial` tactics outside `T`'s cone.

#### 3.4 Execution Matrix (`probe_cache_and_opaque_audit.py`)

Running the inline Python 3.10+ model across 8 adversarial scenarios (`S1`–`S8`) and 4 honest scenarios (`H1`–`H4`, with `H2` holding an unrelated `partial` tactic outside the cone) yields (`SHA256: 0312ae201380af0a63af6a960aa4db753d6c969303a991aba942767fe1e4e373`):

| Scenario | Bypass Vector | `#print axioms` | Non-Fresh Replay | Fresh Replay Only | Three-Gate Audit | Rejection Reason |
|---|---|---|---|---|---|---|
| `S1` | Poisoned `$LAKE_CACHE_DIR` hit after `rm -rf .lake/build` | Admits (`[]`) | Admits | Admits (if dep cached) | **Rejects** | `gate2_unknown_const:evilAx` |
| `S2` | `debug.skipKernelTC` in cached dep with valid `.hash` | Admits (`[]`) | Admits | Rejects | **Rejects** | `gate2_unknown_const:bad_lemma` |
| `S3` | Constructive `opaque ArchDecode` (`default_or_ofNonempty%`) | Admits (`[]`) | Admits | **Admits** | **Rejects** | `gate3_stmt_uninterpreted_opaque:ArchDecode` |
| `S4` | `@[extern] opaque cVerify` in proof cone | Admits (`[]`) | Admits | **Admits** | **Rejects** | `gate3_disallowed_opaque:cVerify` |
| `S5` | `partial def` (`searchOracle` `.opaqueInfo`) in cone | Admits (`[]`) | Admits | **Admits** | **Rejects** | `gate3_disallowed_opaque:searchOracle` |
| `S6` | `module` `opaque` exported as `.axiomInfo` (`exportedAxiomsExt = #[]`) | Admits (`[]`) | Admits | **Admits** | **Rejects** | `gate3_stmt_uninterpreted_opaque:hiddenSpec` |
| `S7` | `@[implemented_by]` override in spec `defn` | Admits (`[]`) | Admits | **Admits** | **Rejects** | `gate3_disallowed_implemented_by:specCheck` |
| `S8` | Rocq `-vos` omitted `opaquetab` proof in dependency | Admits (`[]`) | Admits | Rejects | **Rejects** | `gate2_unknown_const:lem_vos` |
| `H1`–`H4` | Honest proofs (incl. `H2` unrelated `partial` tactic) | Admits (`[propext]`) | Admits | Admits | **Admits (`4/4`)** | `ok_three_gate_audit` |

Totals: `#print axioms` alone and non-fresh replay each miss **8 / 8** adversarial scenarios; fresh replay without cache-bypass and `opaque`/override scanning misses **6 / 8**; Three-Gate Audit rejects **8 / 8** adversarial scenarios and admits **4 / 4** honest developments.

---

## Boundaries

- **Remote cache TLS, Sigstore, and CDN server compromise (`not examined`):** Network transport and server authentication in `CacheService` (`Lake/Config/Cache.lean:586-645`) were **not examined**; findings govern local/shared disk caches and post-download kernel verification.
- **Post-`v4.34.1` upstream Lake changes to `restoreArtifact` and `CacheMap` (`unknown`):** Whether future `leanprover/lean4` releases will flip `Package.isArtifactCacheReadable`'s `true` default, discontinue `hardLink` inode sharing, or add cryptographic tags to `CacheMap` JSONL entries is **unknown**.
- **Relying on `#print axioms`, non-fresh `lean4checker`, or `lake clean && lake --no-cache build` alone (`known not to apply`):** Source inspection (`CollectAxioms.lean:62, 102-146`, `Main.lean:14-41`, `Package.lean:60-70`, `Monad.lean:192-193`) establishes that these mechanisms are **known not to apply** as complete defenses against `opaque` stubs, cache poisoning, or dependency `debug.skipKernelTC`.
- **Multi-module `lean4checker --fresh` arguments and kernel-enforced `@[irreducible]` (`unsupported`):** Passing multiple module targets to `lean4checker --fresh` is **unsupported** (`Main.lean:121-123`), and enforcing kernel opacity via `@[irreducible]` is **unsupported** in Lean 4's C++ kernel (`declaration.h:466-468`), unlike Rocq `OpaqueDef` or Agda `OpaqueBlock`.

---

## Evidence

- **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`, observed `2026-11-20`):**
  - `src/Lean/Util/CollectAxioms.lean` (`lines 37-74, 102-146`: `.opaqueInfo` at `line 62`, `exportedAxiomsExt` using `privateEnv` at `lines 128, 139`).
  - `src/Lean/AddDecl.lean` (`lines 23-33, 118-148`), `src/Lean/OriginalConstKind.lean` (`lines 16-30`), `src/Lean/Elab/DefView.lean` (`lines 187-199`), `src/Lean/Elab/PreDefinition/Main.lean` (`lines 20-36`).
  - `src/Lean/Environment.lean` (`lines 2307-2460`), `src/Lean/Replay.lean` (`lines 59-190`), `src/kernel/environment.h` (`line 23`), `src/kernel/declaration.h` (`lines 147-158, 466-468`), `src/kernel/environment.cpp` (`lines 211-223, 297-301`).
  - `src/lake/Lake/CLI/Main.lean` (`lines 58-61, 222, 284-286`), `Lake/Config/{Env,Monad,Workspace,Package,Cache}.lean`, `Lake/Build/{Common,Module,Package}.lean`.
- **`leanprover/lean4checker` (`91a7f0e8e9dffe927089f5a6edcfeeb8a0e07709`):** `Main.lean` (`lines 14-40, 120-127`).
- **`ammkrn/nanoda_lib` (`0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929`, `v0.4.32`), `leanprover/lean4export` (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`), `leanprover/comparator` (`865edc14486c3388e9225daa971da8e157488c3e`), `leanprover-community/mathlib4` (`d13f23b723b8a846827a245b89c10fc7d3f11612`, `v4.34.1`).**
- **`rocq-prover/rocq` (`25f5b18a320e4796f181f938d3b74bebe7db4dc4`):** `lib/objFile.ml:105-114`, `vernac/library.ml:181-235`, `checker/{checkLibrary.ml:54-56, 106-140, checkFlags.ml:24-43, coqchk_main.ml:42-46, 190-207, 500-507}`.
- **Literature:** Berghofer & Nipkow (TPHOLs 2000, DOI `10.1007/3-540-44659-1_3`), Wenzel (*Isabelle2025 System Manual*), Pollack (1998, DOI `10.1093/oso/9780198501275.003.0013` / `10.7146/brics.v4i18.18945`).
- **Probe Execution (observed `2026-11-20`):** Python 3.10+ script below exited `0` (`SHA256: 0312ae201380af0a63af6a960aa4db753d6c969303a991aba942767fe1e4e373`), verifying `8/8` adversarial rejections and `4/4` honest admissions.

---

## Revalidation

### 1. Executable Self-Contained Audit Probe (`python3` 3.10+, Standard Library Only)

Save to `/tmp/probe_cache_and_opaque_audit.py` and run `python3 /tmp/probe_cache_and_opaque_audit.py` (expected exit `0`, `rejected == 8`, `admitted == 4`):

```python
#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json
from dataclasses import dataclass

@dataclass(frozen=True)
class Decl:
    name: str
    kind: str  # axiom | defn | thm | opaque | induct
    trefs: tuple[str, ...] = ()
    vrefs: tuple[str, ...] = ()
    safety: str = "safe"
    ext: bool = False
    impl: str | None = None
    skip_tc: bool = False
    vos: bool = False
    mod_opaque_ax: bool = False
    ax_ext: tuple[str, ...] | None = None

@dataclass
class Mod:
    name: str
    inhash: str
    decls: dict[str, Decl]
    hash_ok: bool = True
    cached: bool = False
    compiled: bool = False

def collect_axioms(env: dict[str, Decl], ext: dict[str, tuple[str, ...]], root: str) -> tuple[str, ...]:
    seen: dict[str, tuple[str, ...]] = {}
    def go(c: str) -> tuple[str, ...]:
        if c in ext: return ext[c]
        if c in seen: return seen[c]
        seen[c] = ()
        d = env.get(c)
        if not d: return ()
        acc = {c} if d.kind == "axiom" else set()
        for r in (d.trefs if d.kind == "axiom" else d.trefs + d.vrefs):
            acc.update(go(r))
        seen[c] = tuple(sorted(acc))
        return seen[c]
    return go(root)

def rebuild(m: Mod, cache: dict[str, Mod], no_cache: bool, rehash: bool) -> Mod:
    if not no_cache and m.inhash in cache and (cache[m.inhash].hash_ok or not rehash):
        c = cache[m.inhash]
        return Mod(c.name, c.inhash, dict(c.decls), c.hash_ok, cached=True, compiled=False)
    clean = {k: v for k, v in m.decls.items() if not v.skip_tc and not v.vos}
    return Mod(m.name, m.inhash, clean, True, cached=False, compiled=True)

def replay(mods: list[Mod], target: str, fresh: bool) -> tuple[bool, str]:
    env = {k: v for m in mods for k, v in m.decls.items()}
    if target not in env: return False, "missing_target"
    if not fresh:
        for d in mods[-1].decls.values():
            if d.skip_tc or d.vos: return False, f"root_bad:{d.name}"
        return True, "ok_nonfresh"
    vis: set[str] = set()
    def go(c: str) -> str | None:
        if c in vis: return None
        vis.add(c)
        d = env.get(c)
        if not d: return f"unknown_const:{c}"
        for dep in d.trefs + d.vrefs:
            if e := go(dep): return e
        return f"rejected:{d.name}" if (d.skip_tc or d.vos) else None
    err = go(target)
    return err is None, err or "ok_fresh"

def three_gate(mods: list[Mod], cache: dict[str, Mod], target: str, specs: dict[str, tuple[str, ...]]) -> tuple[bool, str]:
    rebuilt = [rebuild(m, cache, no_cache=True, rehash=True) for m in mods]
    if any(m.cached or not m.compiled for m in rebuilt): return False, "gate1_cache_hit"
    ok, msg = replay(rebuilt, target, fresh=True)
    if not ok: return False, f"gate2_{msg}"
    env = {k: v for m in rebuilt for k, v in m.decls.items()}
    vis_s: set[str] = set()
    def ws(c: str) -> str | None:
        if c in vis_s: return None
        vis_s.add(c)
        d = env.get(c)
        if not d: return f"gate3_stmt_missing:{c}"
        if d.kind in ("opaque", "axiom") or d.mod_opaque_ax: return f"gate3_stmt_opaque_or_ax:{c}"
        if d.safety != "safe" or d.ext or d.impl: return f"gate3_stmt_override:{c}"
        if c in specs and d.trefs != specs[c]: return f"gate3_stmt_drift:{c}"
        return next((e for r in d.trefs if (e := ws(r))), None)
    if err := next((e for r in env[target].trefs if (e := ws(r))), None): return False, err
    vis_v: set[str] = set()
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    def wv(c: str) -> str | None:
        if c in vis_v: return None
        vis_v.add(c)
        d = env.get(c)
        if not d: return f"gate3_val_missing:{c}"
        if d.kind == "axiom" and c not in allowed: return f"gate3_axiom:{c}"
        if d.kind == "opaque": return f"gate3_opaque:{c}"
        if d.safety != "safe" or d.ext or d.impl: return f"gate3_override:{c}"
        return next((e for r in d.trefs + d.vrefs if (e := wv(r))), None)
    err = wv(target)
    return err is None, err or "ok_three_gate"

def main() -> None:
    nat, px = Decl("Nat", "induct"), Decl("propext", "axiom")
    sp = Decl("SpecProp", "defn", ("Nat",), ("Nat",))
    dep_ok = Mod("Dep", "in1", {"Nat": nat, "SpecProp": sp})
    dep_poison = Mod("Dep", "in1", {"Nat": nat, "SpecProp": sp, "evilAx": Decl("evilAx", "axiom", ax_ext=())})
    dep_skip = Mod("Dep", "in1", {"Nat": nat, "SpecProp": sp, "bad_lemma": Decl("bad_lemma", "thm", skip_tc=True)})
    dep_vos = Mod("Dep", "in1", {"Nat": nat, "SpecProp": sp, "lem_vos": Decl("lem_vos", "thm", vos=True)})
    cases = [
        ("S1_poisoned_lake_cache", [dep_ok, Mod("M", "in2", {"main_thm": Decl("main_thm", "thm", ("SpecProp",), ("evilAx",))})], {"in1": dep_poison}, False),
        ("S2_skipKernelTC_dep", [dep_skip, Mod("M", "in2", {"main_thm": Decl("main_thm", "thm", ("SpecProp",), ("bad_lemma",))})], {"in1": dep_skip}, False),
        ("S3_opaque_spec_stub", [dep_ok, Mod("M", "in2", {"Arch": Decl("Arch", "opaque", ("Nat",), ("Nat",)), "main_thm": Decl("main_thm", "thm", ("SpecProp", "Arch"), ("Arch",))})], {}, False),
        ("S4_extern_opaque", [dep_ok, Mod("M", "in2", {"cVer": Decl("cVer", "opaque", ("Nat",), ("Nat",), ext=True), "main_thm": Decl("main_thm", "thm", ("SpecProp",), ("cVer",))})], {}, False),
        ("S5_partial_in_cone", [dep_ok, Mod("M", "in2", {"f": Decl("f", "opaque", ("Nat",), ("Nat",)), "f._unsafe_rec": Decl("f._unsafe_rec", "defn", ("Nat",), ("Nat",), safety="partial"), "main_thm": Decl("main_thm", "thm", ("SpecProp",), ("f", "f._unsafe_rec"))})], {}, False),
        ("S6_mod_opaque_ax_ext", [dep_ok, Mod("M", "in2", {"h": Decl("h", "opaque", ("Nat",), ("Nat",), mod_opaque_ax=True, ax_ext=()), "main_thm": Decl("main_thm", "thm", ("SpecProp", "h"), ("h",))})], {}, False),
        ("S7_implemented_by", [dep_ok, Mod("M", "in2", {"chk": Decl("chk", "defn", ("Nat",), ("Nat",), impl="evil"), "main_thm": Decl("main_thm", "thm", ("SpecProp",), ("chk",))})], {}, False),
        ("S8_rocq_vos_omitted", [dep_vos, Mod("M", "in2", {"main_thm": Decl("main_thm", "thm", ("SpecProp",), ("lem_vos",))})], {"in1": dep_vos}, False),
        ("H1_honest_pure", [dep_ok, Mod("M", "in2", {"propext": px, "main_thm": Decl("main_thm", "thm", ("SpecProp",), ("propext", "SpecProp"))})], {}, True),
        ("H2_unrelated_partial", [dep_ok, Mod("M", "in2", {"propext": px, "tac._unsafe_rec": Decl("tac._unsafe_rec", "defn", safety="partial"), "main_thm": Decl("main_thm", "thm", ("SpecProp",), ("propext", "SpecProp"))})], {}, True),
        ("H3_cross_mod_lemma", [Mod("Dep", "in1", {"Nat": nat, "SpecProp": sp, "propext": px, "hLem": Decl("hLem", "thm", ("SpecProp",), ("propext",))}), Mod("M", "in2", {"main_thm": Decl("main_thm", "thm", ("SpecProp",), ("hLem",))})], {}, True),
        ("H4_honest_defn", [dep_ok, Mod("M", "in2", {"propext": px, "cSpec": Decl("cSpec", "defn", ("Nat",), ("Nat",)), "main_thm": Decl("main_thm", "thm", ("SpecProp",), ("cSpec", "propext"))})], {}, True),
    ]
    rows = []
    for name, mods, cache, exp in cases:
        def_mods = [rebuild(m, cache, no_cache=False, rehash=False) for m in mods]
        env = {k: v for m in def_mods for k, v in m.decls.items()}
        ext = {k: v.ax_ext for m in def_mods for k, v in m.decls.items() if v.ax_ext is not None}
        axs = collect_axioms(env, ext, "main_thm")
        ok3, reason3 = three_gate(mods, cache, "main_thm", {"SpecProp": ("Nat",)})
        assert ok3 == exp
        rows.append({"scenario": name, "axioms": list(axs), "nonfresh": replay(def_mods, "main_thm", False)[0], "fresh_only": replay(def_mods, "main_thm", True)[0], "three_gate": ok3, "reason": reason3})
    summary = {"rejected": sum(1 for r in rows if not r["three_gate"]), "admitted": sum(1 for r in rows if r["three_gate"]), "rows": rows}
    raw = json.dumps(summary, indent=2)
    print(raw)
    print("SHA256:", hashlib.sha256(raw.encode()).hexdigest())

if __name__ == "__main__":
    main()
```

### 2. Targeted Live Revalidation Commands

- **Lean 4 `opaque` blind-spot check (expected: `does not depend on any axioms`):**
  ```bash
  lean --stdin <<'EOF'
  opaque archDecode : UInt32 → Option Nat
  theorem vacuous_check : ∃ f : UInt32 → Option Nat, f = archDecode := ⟨archDecode, rfl⟩
  #print axioms vacuous_check
  EOF
  ```
- **Cache-bypassed Lake rebuild + fresh replay:**
  ```bash
  rm -rf .lake/build .lake/cache .lake/packages/*/.lake/build .lake/packages/*/.lake/cache
  tmp_cache="$(mktemp -d)"
  LAKE_ARTIFACT_CACHE=false LAKE_CACHE_DIR="$tmp_cache" LAKE_NO_CACHE=true lake --no-cache --rehash build
  lake env lean4checker --fresh RootModule && rm -rf "$tmp_cache"
  ```
