<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Lean 4 (`v4.34.1`) Lake, Reservoir, Nix, and Library Publishing

## Summary

This report documents the mechanics required to package, build hermetically in
Nix, publish to the Lean Reservoir package registry, and compose across Rust
crates the reusable verification libraries in Anneal under Lean `v4.34.1` (Lake
`5.0.0-src+5045d00`, commit `5045d0056413266e57c625dcd7c365b10e377c52`).

- **Lake manifests and hermetic Nix builds:** Lake `v4.34.1` emits
  `lake-manifest.json` schema version `"1.2.0"` (adding top-level
  `"fixedToolchain": Bool` to the `"1.1.0"` schema that introduced `"scope"` on
  package entries) and accepts any `1.x.y` manifest via `Manifest.getVersion`.
  Standard `lake build` fails inside a Nix sandbox because `PackageEntry.git`
  invokes `git clone` and `PackageEntry.path` attempts to write `.lake/build`
  into its target directory. Hermetic Nix derivations must pre-fetch each Git
  dependency via `pkgs.fetchFromGitHub`, copy the sources into writable
  `$TMPDIR` staging directories, generate a `package-overrides.json` file
  mapping each dependency to `"type": "path"`, invoke `lake build --packages
  <overrides.json>` with `LAKE_NO_CACHE=true`, and set `dontPatchELF = true` on
  the Lean binary archive so that `bin/lean` preserves the exact SHA-256 digest
  pinned in `foundation-lock.json`.
- **Reservoir indexing and Fuchsia 3-file licensing (`OD-01`):** Reservoir
  evaluates five eligibility criteria (`Reservoir/Criterion.lean:33-114`): (1)
  the `.lake-manifest` GitHub repository topic or at least 10 stars, (2) a root
  `lakefile.toml` or `lakefile.lean`, (3) a root `lean-toolchain` file, (4) an
  OSI-approved SPDX license in GitHub's `repository.licenseInfo.spdxId`, and
  (5) non-fork repository status. GitHub populates `licenseInfo.spdxId` using
  Ruby `licensee/licensee`, which ranks candidate license files by filename
  preference (`LICENSE` scores `1.0`; `LICENSE-APACHE`, `LICENSE-BSD`, and
  `LICENSE-MIT` score `0.9`, `0.7`, and `0.8`, respectively) and requires the
  sole winner at the highest tier to exceed a `0.70` weight threshold and a 98%
  Sørensen-Dice similarity match against a single SPDX template. Fuchsia's
  three-file layout (`LICENSE-APACHE`, `LICENSE-BSD`, `LICENSE-MIT`) succeeds
  automatically on GitHub and Reservoir—resolving to `"spdxId": "Apache-2.0"`
  as verified on `google/zerocopy`—provided the repository satisfies two strict
  invariants: (a) no root `LICENSE` or `COPYING` summary file exists, and (b)
  `LICENSE-APACHE` retains the complete 11,350-byte canonical Apache-2.0 text
  including its 1,626-byte `APPENDIX` section.
- **Lean library hygiene, linters, and documentation:** Lean `v4.34.1` ships
  six core linters (`linter.missingDocs`, `linter.unusedVariables`,
  `linter.unusedSimpArgs`, `linter.constructorNameAsVariable`,
  `linter.deprecated`, and `linter.omit`) plus `warningAsError = true` in
  `[leanOptions]`, enabling zero-warning enforcement without depending on
  `Batteries` or `Mathlib`. Regression test suites in standalone libraries use
  `#guard_msgs` (`src/Lean/Elab/GuardMsgs.lean`) combined with `#print axioms`
  to lock kernel axiom footprints without external test runners.
- **Anneal's four publishable library layers:** Anneal's verification stack
  factors cleanly into four standalone packages in increasing order of coupling:
  (1) `anneal-refinement` (`Anneal.Refinement` and `Anneal.StepResult`, 593
  lines, zero Rust or MIR dependencies, demonstrated in
  [`AnnealRefinementOutboundProbe.lean`][probe1]),
  (2) `anneal-mir` (`Memory`, `MirAst`, `MirSemantics`, and `MirLemmas`, 1,262
  lines), (3) `anneal-tactics` (`FunctionalTranslation` symbolic evaluator,
  loop framing, forward/backward borrow lenses, and `KernelBVDecide` /
  `KernelLRAT` tactics, 8,315 lines), and (4) `anneal-audit` (the standalone
  `.olean` kernel-environment and `@[vetted]` / `@[candidate]` boundary auditor,
  1,073 lines).
- **Cross-crate verification and receipt composition (`OD-08` and
  `LIB-01`–`LIB-10`):** Downstream crates consume upstream verified crates
  along three complementary paths, all mechanized in
  [`CrossCrateReceiptsProbe.lean`][probe2]:
  (1) abstract specification reuse (`CalleeSatisfiesAbstractSpec` contracts
  discharged without unfolding callee MIR), (2) direct dependency MIR body
  inspection when an upstream contract is absent or too weak, and (3)
  transitive `VerifiedCrateReceipt` checking across the crate dependency DAG,
  binding the rustc `StrictVersionHash`, Lean `.olean` digests, target layout
  parameters (`SubjectIdentity`), and TCB policy (`TrustPolicy`) of every
  upstream crate into the downstream crate's `VerificationResult`.

## Applicability

The findings in this report are governed by the exact repository revisions,
toolchain binaries, and support probes listed below, observed on `2026-10-30`
on `x86_64-linux`.

| Subject | Revision / Digest | Role in Report |
| :--- | :--- | :--- |
| `leanprover/lean4` (`v4.34.1`) | Commit `5045d0056413266e57c625dcd7c365b10e377c52`; `x86_64-linux` archive SHA-256 `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4` | Lake `5.0.0-src+5045d00` manifest loader, `--packages` override engine, `LAKE_NO_CACHE`, core linters, `#guard_msgs`, `shake`, and compiler for both support probes |
| `joshlf/anneal` (`main` and `skeleton`) | `main` commit `24367bd1a8c784f2578535954f9915e24894a56f`; `skeleton` commit `e75556f5767705404404c0675c6d2d9bcee41d6f` | `flake.nix`, `trusted/lean/foundation-lock.json`, `theory/Anneal/Refinement.lean`, `theory/Anneal/StepResult.lean`, `theory/Anneal/MirLemmas.lean`, `theory/Anneal/FunctionalTranslation.lean`, and `trusted/audit/` |
| `leanprover/reservoir` | Commits `a5774ea3b51fef4a496f35c791cfa660c914454f` and `d58b4e3866c57690f7fd74099f08bd20d62de98b` | Reservoir indexing criteria (`Reservoir/Criterion.lean`, `Reservoir/Index.lean`), GitHub GraphQL queries (`Reservoir/GitHub.lean`), and SPDX table (`Reservoir/Spdx.lean`) |
| `leanprover/lean-action` | Commits `bd5cb0b830eda614ce3fc186d8429b9409b16c47` and `52bbb8dde6eb0c6c1ef3a12bccecfdeaa25eb792` | Standard GitHub Actions CI workflow (`action.yml`, `scripts/build.sh`, `scripts/test.sh`, `scripts/lint.sh`) |
| `leanprover/doc-gen4` | Commit `b968d9679900841dbe9b86894ae7ff8f454a2b1f` | HTML API documentation generator (`DocGen4/Output.lean`) |
| `leanprover/verso` | Commit `a62a15bbe7719a9086442c5bbe83140f5334aa6f` | Long-form literate documentation and blueprint authoring framework |
| `lenianiva/lean4-nix` | Commits `6067688bc484f50f16dde1f2749bbb3e373198c9` (`Pantograph/flake.lock`) and `2ad74592e34c2e6ff5e8bec9d8abab8f4e9c3a37` (`main`) | Community Nix overlay (`lib/lake.nix`, `lib/toolchain.nix`) compared against Anneal's hermetic Nix build pattern |
| `licensee/licensee` | Commit `9a9c98b19d04585d9c7213ff52bd385aa182617a` | GitHub's Ruby license classifier (`lib/licensee.rb`, `lib/licensee/projectFiles/license_file.rb`, `lib/licensee/project.rb`) |
| `google/zerocopy` | Commit `d19b86bee54a80f957fba6cd536ccaca0df50fb4` | Reference Fuchsia 3-file repository (`LICENSE-APACHE` at 11,350 bytes, `LICENSE-BSD`, `LICENSE-MIT`) resolving to `"spdxId": "Apache-2.0"` |
| `NethermindEth/LeanCIL` | Commit `4229b5485e3773e33c2867d8aa29e3d61a6c7242` | Empirical failure case 1: 207-byte root `LICENSE` summary file causing `"spdxId": "NOASSERTION"` and Reservoir exclusion |
| `rust-random/rand` | Commits `9e7d328f60d6372ae22927f37d1a816fc980f25e` and `a49e4ad730c028a21cf8bc85b4bc2f57ce33fa2a` | Empirical failure case 2: 9,724-byte `LICENSE-APACHE` (missing 1,626-byte `APPENDIX`) causing `"spdxId": "NOASSERTION"` |
| [`AnnealRefinementOutboundProbe.lean`](support/AnnealRefinementOutboundProbe.lean) | SHA-256 `2225e7df1a82185b62ee1de5efb473b1f7c98e1f02370a6bbef700320afc761f` (20,015 bytes, 512 lines) | Standalone Lean `v4.34.1` synthesis of the `anneal-refinement` package |
| [`CrossCrateReceiptsProbe.lean`](support/CrossCrateReceiptsProbe.lean) | SHA-256 `a2352c7ff2b7e6b4f6f9451a1481ffafc52137530641ffa17f652d48c63dd283` (30,106 bytes, 742 lines) | Standalone Lean `v4.34.1` synthesis of cross-crate specification reuse, direct MIR inspection, and transitive receipt checking |

## Findings

### 1. Lake (`v4.34.1`) Manifests, `--packages`, and Hermetic Nix Builds

#### 1.1 `lake-manifest.json` Schema Evolution (`1.1.0` to `1.2.0`)

Basis: `primary source` (`leanprover/lean4` commit
`5045d0056413266e57c625dcd7c365b10e377c52`,
`src/lake/Lake/Load/Manifest.lean:33-248`) and `empirical probe` (Lake
`5.0.0-src+5045d00` manifest generation and override resolution).

In Lake `v4.34.1`, the manifest data structure `Manifest`
(`src/lake/Lake/Load/Manifest.lean:180-189`) serializes to `lake-manifest.json`
under schema version `1.2.0` (`Manifest.version : StdVer := {major := 1, minor
:= 2}`, lines 50–52):

```json
{
  "version": "1.2.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {
      "type": "git",
      "scope": "joshlf",
      "name": "anneal-refinement",
      "url": "https://github.com/joshlf/anneal-refinement",
      "rev": "0123456789abcdef0123456789abcdef01234567",
      "inputRev": "main",
      "subDir": null,
      "inherited": false,
      "configFile": "lakefile.toml"
    }
  ],
  "name": "downstream-consumer",
  "lakeDir": ".lake",
  "fixedToolchain": false
}
```

The version history in `Manifest.lean:50-56` and `Manifest.fromJson?`
(`lines 205-248`) governs backward compatibility across Lean 4 releases:

- **Schema `"1.1.0"`** introduced the optional `"scope": String` field on
  `PackageEntry` (`Manifest.lean:64-97`) to record the Reservoir owner/scope of
  a dependency alongside its package `"name"`.
- **Schema `"1.2.0"`** (current in `v4.34.1`) added the top-level boolean field
  `"fixedToolchain": Bool` (`Manifest.lean:187`, `240`, `257`).
- **Forward/backward acceptance:** `Manifest.getVersion` (`lines 217-231`)
  accepts legacy versions `0.5.0`, `0.6.0`, and `0.7.0` as well as any version
  with `ver.major == 1`. When Lake `v4.34.1` reads a `"1.1.0"` manifest that
  omits `"fixedToolchain"`, `obj.getD "fixedToolchain" false` (`line 240`)
  defaults the field to `false` without warning or error.

Each element of the `"packages"` array deserializes into `PackageEntry`
(`Manifest.lean:64-158`), which is a tagged union discriminated by `"type"`:

- **`PackageEntry.path` (`"type": "path"`):** Contains `name : Name`,
  `scope : String`, `inherited : Bool`, `configFile : System.FilePath`, and
  `dir : System.FilePath` (the filesystem path to the package root, interpreted
  relative to the workspace root via `entry.inDirectory pkg.rootDir` at
  `Manifest.lean:160-169`).
- **`PackageEntry.git` (`"type": "git"`):** Contains `name : Name`,
  `scope : String`, `inherited : Bool`, `configFile : System.FilePath`,
  `url : String`, `rev : String` (the locked 40-character Git commit SHA),
  `inputRev : Option String` (the branch or tag constraint in `lakefile.toml`),
  and `subDir : Option System.FilePath` (for monorepo subdirectory packages).

#### 1.2 `--packages` (`package-overrides.json`) Resolution Mechanics

Basis: `primary source` (`leanprover/lean4` commit
`5045d0056413266e57c625dcd7c365b10e377c52`,
`src/lake/Lake/Load/Config.lean:47-51`,
`src/lake/Lake/CLI/Main.lean:295-305`,
`src/lake/Lake/Load/Manifest.lean:274-292`, and
`src/lake/Lake/Load/Workspace.lean:345-419`) and `empirical probe`.

During `Workspace.materializeDeps` (`Lake/Load/Workspace.lean:345-419`), Lake
loads package overrides before materializing any entry from
`lake-manifest.json`:

1. **Default override file:** Lake checks `.lake/package-overrides.json` inside
   the root package's `.lake` directory (`Workspace.lean:365`, via
   `ws.packageOverridesFile`).
2. **CLI override file (`--packages=<file>` or `--packages <file>`):** The CLI
   parser (`src/lake/Lake/CLI/Main.lean:295-305`) populates
   `LoadConfig.packageOverrides : Option System.FilePath`
   (`src/lake/Lake/Load/Config.lean:47-51`). When present, `Workspace.lean:366`
   calls `Manifest.tryLoadEntries path` (`Manifest.lean:274-292`) and appends
   those entries to the override map keyed by `entry.name`.
3. **Entry substitution:** As Lake iterates through the locked entries in
   `lake-manifest.json` (`Workspace.lean:385-401`), if `overrides.find?
   entry.name` returns `some overrideEntry`, Lake replaces the manifest's
   `PackageEntry.git` record with `overrideEntry.inDirectory ws.root.rootDir`
   before calling `dep.materialize`.

Because `Manifest.tryLoadEntries` (`Manifest.lean:274-292`) accepts either a
full manifest object (`{"version": "1.2.0", "packages": [...]}`) or a bare JSON
array of `PackageEntry` objects (`[{"type": "path", ...}]`), a build driver can
redirect every Git dependency in `lake-manifest.json` to a local directory
without mutating the tracked `lake-manifest.json` file.

#### 1.3 Why Naive `lake build` Fails in Nix and How `LAKE_NO_CACHE` Works

Basis: `primary source` (`leanprover/lean4` commit
`5045d0056413266e57c625dcd7c365b10e377c52`,
`src/lake/Lake/Load/Materialize.lean:81-269`,
`src/lake/Lake/Config/Cache.lean:19-40`, and
`src/lake/Lake/Config/Env.lean:288-334`) and `empirical probe`.

Running `lake build` directly inside a hermetic Nix derivation (`__noChroot =
false`) fails for three distinct reasons in Lake's materialization and caching
code:

1. **Network Git clones (`Materialize.lean:81-178`):** When materializing a
   `PackageEntry.git` entry into `.lake/packages/<name>`, `materializeGitPkg`
   checks whether `.lake/packages/<name>` exists; if not, it spawns `git clone`
   and `git fetch` against `url`, which fails immediately when network access
   is disabled in the Nix sandbox.
2. **Read-only store paths (`Materialize.lean:226-269`):** When a
   `PackageEntry.path` entry points directly to a read-only `/nix/store/`
   derivation output (`"dir": "/nix/store/...-source"`), Lake sets the
   dependency's `rootDir` to that `/nix/store/` path and attempts to create its
   build directory at `<rootDir>/.lake/build`, failing with `Permission denied`
   (`EACCES`).
3. **Artifact cache probes (`Env.lean:288-334`, `Cache.lean:19-40`):** In Lake
   `v4.34.1`, `Lake.Env.compute` reads the environment variable `LAKE_NO_CACHE`
   (`Env.lean:290`) and the CLI flag `--no-cache`. Setting `LAKE_NO_CACHE=true`
   forces `env.noCache := true`, preventing Lake from querying remote Reservoir
   or GitHub artifact caches or attempting to write to `$HOME/.lake/cache`.

#### 1.4 Comparing `lenianiva/lean4-nix` with Anneal's Hermetic Nix Pattern

Basis: `primary source` (`lenianiva/lean4-nix` commit
`2ad74592e34c2e6ff5e8bec9d8abab8f4e9c3a37`, `lib/lake.nix:1-265` and
`lib/toolchain.nix:1-155`; `joshlf/anneal` commit
`24367bd1a8c784f2578535954f9915e24894a56f`, `flake.nix` and
`trusted/lean/foundation-lock.json`) and `design deduction`.

The community Nix overlay `lenianiva/lean4-nix` (`lib/lake.nix` and
`lib/toolchain.nix`) and Anneal's hermetic Nix build differ on two security- and
reproducibility-critical points:

| Dimension | `lenianiva/lean4-nix` (`lib/toolchain.nix`, `lib/lake.nix`) | Anneal Hermetic Nix Architecture (`flake.nix`, `foundation-lock.json`) |
| :--- | :--- | :--- |
| **Lean binary ELF patching** | `fetchBinaryLean` (`lib/toolchain.nix:39-101`) applies `autoPatchelfHook` and `makeWrapper` (`wrapProgram`) on Linux to rewrite the ELF interpreter and `RPATH` of `bin/lean` and `bin/lake`. | Sets `dontPatchELF = true` and `dontStrip = true` on the fetched Lean release archive so that `bin/lean` retains its exact upstream byte sequence and matches the `sha256` pinned in `trusted/lean/foundation-lock.json`. |
| **Dependency fetching** | `buildDeps` (`lib/lake.nix:68-97`) uses `builtins.fetchGit { url = dep.url; rev = dep.rev; shallow = true; }` at Nix evaluation time, which depends on the Nix daemon's Git fetcher rather than fixed-output `narHash` store derivations. | Locks each dependency with `pkgs.fetchFromGitHub { owner; repo; rev; sha256 = "sha256-..."; }` so every dependency is a fixed-output derivation verified by content hash before entering the sandbox. |
| **Writable dependency staging & overrides** | `mkLakeDerivation` (`lib/lake.nix:103-214`) copies each pre-built dependency's `.lake` directory into `.lake/packages/${dep.name}/.lake`, `chmod -R +w`s the tree, and writes `.lake/package-overrides.json` with `"dir": ".lake/packages/${name}"`. | Copies each `fetchFromGitHub` source tree into `$TMPDIR/lake-deps/<name>`, `chmod -R u+w`s the copy, writes `$TMPDIR/package-overrides.json` pointing to `$TMPDIR/lake-deps/<name>`, and runs `LAKE_NO_CACHE=true lake build --packages "$TMPDIR/package-overrides.json"`. |

For Anneal or any downstream project that audits the SHA-256 of `bin/lean`
against a lockfile (`trusted/lean/foundation-lock.json`), `autoPatchelfHook`
cannot be applied directly to `bin/lean` because rewriting the ELF `.interp` or
`.dynamic` section changes the binary hash. Instead, when running on NixOS
where `/lib64/ld-linux-x86-64.so.2` is absent, hermetic Nix derivations must
either invoke the unpatched `bin/lean` through explicit loader invocation or
run inside a `buildFHSEnv` / container namespace that provides the standard ELF
interpreter path without mutating the `bin/lean` file bytes.

The canonical hermetic Nix build phase for a multi-package Lake `v4.34.1`
workspace is:

```nix
buildPhase = ''
  runHook preBuild
  export HOME="$TMPDIR/home"
  export LAKE_NO_CACHE=true
  mkdir -p "$HOME" "$TMPDIR/lake-deps"

  cp -r ${annealRefinementSrc} "$TMPDIR/lake-deps/anneal-refinement"
  chmod -R u+w "$TMPDIR/lake-deps/anneal-refinement"

  cat > "$TMPDIR/package-overrides.json" <<EOF
  {
    "version": "1.2.0",
    "packagesDir": ".lake/packages",
    "packages": [
      {
        "type": "path",
        "scope": "joshlf",
        "name": "anneal-refinement",
        "inherited": false,
        "dir": "$TMPDIR/lake-deps/anneal-refinement",
        "configFile": "lakefile.toml"
      }
    ]
  }
  EOF

  lake build --packages "$TMPDIR/package-overrides.json"
  runHook postBuild
'';
```

---

### 2. Reservoir Indexing and Fuchsia 3-File Licensing (`OD-01`)

#### 2.1 Reservoir's Five Eligibility Gates and Ingestion Pipeline

Basis: `primary source` (`leanprover/reservoir` commits
`a5774ea3b51fef4a496f35c791cfa660c914454f` and
`d58b4e3866c57690f7fd74099f08bd20d62de98b`, `Reservoir/Criterion.lean:33-114`,
`Reservoir/Index.lean:140-310`, `Reservoir/GitHub.lean:21-98`, and
`Reservoir/Spdx.lean:14-617`).

Reservoir discovers and indexes Lean 4 repositories on GitHub through a crawler
that queries the GitHub GraphQL API (`Reservoir/GitHub.lean:21-98`) and filters
candidates through `Reservoir/Criterion.lean:33-114` and
`Reservoir/Index.lean:287-300`. A repository is eligible for automatic
inclusion only if all five conditions hold simultaneously:

1. **Discovery / popularity (`Criterion.lean:94-114`):** Either the GitHub
   repository has the topic `.lake-manifest`, or `stargazerCount >= 10`. Adding
   the `.lake-manifest` topic on GitHub bypasses the 10-star threshold
   immediately for newly published packages.
2. **Root Lake configuration (`Index.lean:146-164`):** The repository root on
   the default branch must contain `lakefile.toml` or `lakefile.lean`.
   Reservoir prefers `lakefile.toml` when parsing package metadata without
   executing arbitrary Lean elaboration code.
3. **Root `lean-toolchain` (`Index.lean:166-190`):** The repository root must
   contain a `lean-toolchain` file specifying a valid Lean 4 release tag (such
   as `leanprover/lean4:v4.34.1`).
4. **OSI-approved SPDX license (`Criterion.lean:77-92`):** GitHub's GraphQL
   field `repository.licenseInfo.spdxId` (`GitHub.lean:45-51`) must be non-null,
   must resolve via `Spdx.findLicense` (`Reservoir/Spdx.lean:14-617`), and must
   satisfy `license.isOsiApproved == true` (`Criterion.lean:81-88`).
5. **Non-fork status (`Criterion.lean:45-58`):** `repository.isFork` must be
   `false` (unless manually allowlisted in the Reservoir index configuration).

#### 2.2 Resolution of `OD-01`: GitHub Licensee and Fuchsia 3-File Licensing

Basis: `primary source` (`licensee/licensee` commit
`9a9c98b19d04585d9c7213ff52bd385aa182617a`, `lib/licensee.rb:6-42`,
`lib/licensee/projectFiles/license_file.rb:8-140`, and
`lib/licensee/project.rb:15-171`; `leanprover/reservoir` commit
`d58b4e3866c57690f7fd74099f08bd20d62de98b`, `Reservoir/Criterion.lean:77-92`
and `Reservoir/Spdx.lean:14-617`) and `empirical probe` (GitHub REST/GraphQL
and Reservoir API responses for `google/zerocopy`, `NethermindEth/LeanCIL`, and
`rust-random/rand`).

Open Decision `OD-01` asked whether Fuchsia's standard three-file license
layout (`LICENSE-APACHE`, `LICENSE-BSD`, `LICENSE-MIT` at the repository root,
with no single `LICENSE` file) causes GitHub's Licensee detector to return
`"spdxId": "NOASSERTION"`, which would cause Reservoir (`Criterion.lean:77-92`)
to reject the repository.

Source inspection of `licensee/licensee` (commit
`9a9c98b19d04585d9c7213ff52bd385aa182617a`) and empirical queries against
GitHub and Reservoir establish the exact two-stage classification rule:

1. **Candidate filename scoring (`projectFiles/license_file.rb:8-140`):**
   Licensee scans root filenames against `PREFERRED_EXT_REGEX` and
   `ANY_EXT_REGEX` (`lines 25-65`) and assigns each matching file a preference
   weight via `LicenseFile.name_score` (`lines 91-118`):
   - Exact `LICENSE` (or `LICENSE.md` / `LICENSE.txt`): weight **`1.0`**.
   - `LICENSE-APACHE` (matches `LICENSE_REGEX` + `-\b(apache)\b` at lines
     55–61, 108): weight **`0.9`**.
   - `LICENSE-MIT` (matches `-\b(mit)\b` at lines 55–61, 109): weight **`0.8`**.
   - `LICENSE-BSD` (matches `-\b(bsd)\b` at lines 55–61, 111): weight **`0.7`**.
   - Any file with weight `< LESS_PREFERRED_SCORE` (`0.70`, `line 67`) is
     discarded before content matching (`project.rb:135-148`).
2. **Tiered single-winner selection (`lib/licensee/project.rb:50-120`):**
   `Project#matched_file` iterates through `license_files` in descending order
   of `name_score` and returns the **first** file whose content matches a known
   SPDX license template with Sørensen-Dice similarity $\ge 98\%$
   (`Licensee::CONFIDENCE_THRESHOLD = 98` in `lib/licensee.rb:11`), provided
   no other file *at the same `name_score` tier* creates an ambiguity.

Because `LICENSE-APACHE` (`0.9`), `LICENSE-MIT` (`0.8`), and `LICENSE-BSD`
(`0.7`) sit at **strictly distinct** preference tiers (`0.9 > 0.8 > 0.7`),
Licensee evaluates `LICENSE-APACHE` first. When `LICENSE-APACHE` matches the
canonical Apache-2.0 text at $\ge 98\%$ similarity, Licensee immediately binds
`repository.licenseInfo.spdxId = "Apache-2.0"` (`isOsiApproved = true`), and
Reservoir accepts the repository.

Empirical verification across three live repositories confirms both the success
path and the two failure traps to avoid:

| Repository (Commit) | Root License Files (Byte Size) | Licensee Top Tier (`name_score`) | GitHub `licenseInfo.spdxId` | Reservoir Status |
| :--- | :--- | :--- | :--- | :--- |
| `google/zerocopy` (`d19b86bee54a80f957fba6cd536ccaca0df50fb4`) | `LICENSE-APACHE` (11,350 B), `LICENSE-BSD` (1,296 B), `LICENSE-MIT` (1,023 B) | `LICENSE-APACHE` (`0.9`) — includes full 1,626-byte `APPENDIX`, Dice similarity 100% | `"Apache-2.0"` | Eligible (`isOsiApproved == true` in `Reservoir/Spdx.lean:45`) |
| `NethermindEth/LeanCIL` (`4229b5485e3773e33c2867d8aa29e3d61a6c7242`) | `LICENSE` (207 B summary), `LICENSE-APACHE` (10,850 B), `LICENSE-MIT` (1,072 B) | `LICENSE` (`1.0`) — 207-byte human summary fails all SPDX templates; Licensee stops or reports ambiguity | `"NOASSERTION"` | **Rejected** (HTTP 404 on Reservoir API despite `.lake-manifest` topic) |
| `rust-random/rand` (`9e7d328f60d6372ae22927f37d1a816fc980f25e`) | `LICENSE-APACHE` (9,724 B), `LICENSE-MIT` (1,023 B) | `LICENSE-APACHE` (`0.9`) — commit `a49e4ad730c028a21cf8bc85b4bc2f57ce33fa2a` stripped the 1,626-byte `APPENDIX`, failing Licensee's length/Dice check | `"NOASSERTION"` | **Rejected** (`"NOASSERTION"` fails `Spdx.findLicense`) |

Consequently, every Anneal repository published to Reservoir under Fuchsia's
three-file license must uphold two concrete rules:

1. **Never add a root `LICENSE` or `COPYING` summary file:** Keep only
   `LICENSE-APACHE`, `LICENSE-BSD`, and `LICENSE-MIT` at the repository root,
   and state the triple-license choice in `README.md` and `lakefile.toml`.
2. **Preserve the complete 11,350-byte `LICENSE-APACHE` file (including the
   `APPENDIX` section):** Do not strip the trailing `APPENDIX: How to apply the
   Apache License to your work` block (`1,626` bytes), because Licensee's
   `License#max_delta` length filter and 98% Dice matcher compare against the
   full Apache-2.0 template including the appendix.

#### 2.3 `lakefile.toml` Metadata Fields for Outbound Reservoir Packages

Basis: `primary source` (`leanprover/lean4` commit
`5045d0056413266e57c625dcd7c365b10e377c52`,
`src/lake/Lake/Config/Package.lean:123-243`).

Lake `v4.34.1` defines the package metadata fields parsed from `lakefile.toml`
in `PackageConfig` (`src/lake/Lake/Config/Package.lean:123-243`):

- `name : Name` — The Lake package identifier (such as `"anneal-refinement"`).
- `version : StdVer` — Semantic version string (such as `"0.1.0"`).
- `versionTags : StrPat` — Git tag pattern recognized by Reservoir as package
  releases (defaulting to tags starting with `v`, such as `"v0.1.0"`).
- `description : String` — Short summary displayed on Reservoir package cards.
- `keywords : Array String` — Search tags on Reservoir.
- `homepage : String` — Canonical repository or documentation URL.
- `license : String` — SPDX license expression (`"Apache-2.0 OR BSD-2-Clause OR
  MIT"`). Note that while `lakefile.toml` validates and stores this string,
  Reservoir (`Reservoir/Criterion.lean:77-92`) currently gates indexing on
  GitHub's `repository.licenseInfo.spdxId` rather than `PackageConfig.license`.
- `licenseFiles : Array FilePath` — Defaults to `#["LICENSE"]`; for Fuchsia's
  three-file layout, set `licenseFiles = ["LICENSE-APACHE", "LICENSE-BSD",
  "LICENSE-MIT"]` so Lake's local packaging tools track all three files.
- `readmeFile : FilePath` — Defaults to `"README.md"`.
- `reservoir : Bool` — Defaults to `true`; setting `reservoir = false` opts a
  public repository out of Reservoir indexing.

---

### 3. Lean Library Hygiene, Linters, Documentation, and CI

#### 3.1 Core Lean `v4.34.1` Linters vs. `Batteries` / `Mathlib` Linters

Basis: `primary source` (`leanprover/lean4` commit
`5045d0056413266e57c625dcd7c365b10e377c52`, `src/Lean/Linter/Basic.lean`,
`src/Lean/Linter/MissingDocs.lean`, `src/Lean/Linter/UnusedVariables.lean`,
`src/Lean/Linter/UnusedSimpArgs.lean`,
`src/Lean/Linter/ConstructorAsVariable.lean`, `src/Lean/Linter/Deprecated.lean`,
`src/Lean/Linter/Omit.lean`, and `src/Lean/Elab/InfoTree/Main.lean`) and
`empirical probe` ([`AnnealRefinementOutboundProbe.lean`][probe1]).

A foundational verification library such as `anneal-refinement` should have
zero external Lake dependencies so that downstream users (including non-Rust
verification projects) can depend on it without pulling `Batteries` or
`Mathlib4` into their build graph. Lean `v4.34.1` builds six syntax/elaboration
linters directly into the `Lean.Linter` core library:

| Option Name | Defining Module in `leanprover/lean4` (`v4.34.1`) | Default | Purpose in Outbound Libraries |
| :--- | :--- | :--- | :--- |
| `linter.missingDocs` | `src/Lean/Linter/MissingDocs.lean` | `false` | Emits a warning on any public `def`, `abbrev`, `structure`, `inductive`, `class`, or `theorem` (and public structure fields/constructors) lacking a `/-- ... -/` docstring. |
| `linter.unusedVariables` | `src/Lean/Linter/UnusedVariables.lean` | `true` | Warns on bound variables in definitions, theorems, or tactics that are not referenced. |
| `linter.unusedSimpArgs` | `src/Lean/Linter/UnusedSimpArgs.lean` | `true` | Warns when an explicit `simp [h]` argument does not fire during simplification. |
| `linter.constructorNameAsVariable` | `src/Lean/Linter/ConstructorAsVariable.lean` | `true` | Warns when a pattern variable shadows an existing constructor name of the matched inductive type. |
| `linter.deprecated` | `src/Lean/Linter/Deprecated.lean` | `true` | Warns on references to declarations marked `@[deprecated]`. |
| `linter.omit` | `src/Lean/Linter/Omit.lean` | `true` | Validates `omit` section-variable directives. |
| `warningAsError` | `src/Lean/Elab/InfoTree/Main.lean` | `false` | Promotes all compiler and linter warnings (including `declaration uses 'sorry'` and `linter.missingDocs`) to hard compilation errors (exit code `1`). |

By contrast, environment-wide linters such as `docBlameThm`, `dupNamespace`,
`explicitVarsOfIff`, and `style.header` live in `Batteries.Tactic.Lint` and
`Mathlib.Tactic.Linter`. Enabling `linter.missingDocs = true` and
`warningAsError = true` inside `[leanOptions]` in `lakefile.toml` gives a
zero-dependency library full API docstring and warning enforcement at compile
time:

```toml
[leanOptions]
warningAsError = true
"linter.missingDocs" = true
"linter.unusedVariables" = true
"linter.unusedSimpArgs" = true
"linter.constructorNameAsVariable" = true
"linter.deprecated" = true
```

#### 3.2 Regression Testing with `#guard_msgs` and `#print axioms`

Basis: `primary source` (`leanprover/lean4` commit
`5045d0056413266e57c625dcd7c365b10e377c52`,
`src/Lean/Elab/GuardMsgs.lean:1-310` and `src/Init/Guard.lean:1-45`) and
`empirical probe` ([`AnnealRefinementOutboundProbe.lean`][probe1] and
[`CrossCrateReceiptsProbe.lean`][probe2]).

Lean `v4.34.1` provides built-in test harnesses that execute during normal
`lake test` compilation (`testDriver = "<TestLibName>"` in `lakefile.toml`)
without external runner dependencies:

- **`#guard_msgs in <cmd>` (`src/Lean/Elab/GuardMsgs.lean`):** Captures all
  diagnostic messages (info, warnings, or errors) produced by `<cmd>` and fails
  compilation if they do not match the preceding `/-- ... -/` docstring.
- **`#guard_msgs` + `#print axioms <decl>`:** Combining `#guard_msgs` with
  `#print axioms` locks the exact kernel axiom footprint of every exported
  theorem. For example, in
  [`AnnealRefinementOutboundProbe.lean`][probe1-tests]:
  - `AnnealRefinement.Pass.comp_correct` is verified (`Lines 493–494`) to print
    `'AnnealRefinement.Pass.comp_correct' does not depend on any axioms` (pure
    constructive dependent type theory).
  - `AnnealRefinement.verify_with_pass` (`Lines 499–500`) is verified to depend
    on zero axioms, while `AnnealRefinement.runFuel_toPartialObs_refines`
    (`Lines 505–506`) is verified to depend only on `[propext]`, with zero
    `sorryAx` and zero `Classical.choice`.
- **`#guard <bool_expr>` (`src/Init/Guard.lean`):** Evaluates a decidable
  proposition or `Bool` expression at elaboration time and fails compilation if
  it reduces to `false`.

#### 3.3 Docs (`doc-gen4`, `verso`), Import Hygiene (`shake`), and CI

Basis: `primary source` (`leanprover/doc-gen4` commit
`b968d9679900841dbe9b86894ae7ff8f454a2b1f`, `DocGen4/Output.lean`;
`leanprover/verso` commit `a62a15bbe7719a9086442c5bbe83140f5334aa6f`,
`README.md`; `leanprover/lean4` commit
`5045d0056413266e57c625dcd7c365b10e377c52`, `src/Shake/Main.lean:1-95`; and
`leanprover/lean-action` commit `52bbb8dde6eb0c6c1ef3a12bccecfdeaa25eb792`,
`action.yml:1-319`).

- **API reference generation (`doc-gen4`) vs. narrative manuals (`verso`):**
  `leanprover/doc-gen4` (`DocGen4/Output.lean`) extracts module `/-- ... -/`
  and `/-! ... -/` docstrings, declaration signatures, and source links from
  compiled `.olean` files to generate searchable HTML API reference sites. To
  avoid polluting the library's own `lake-manifest.json` (and downstream
  consumers' transitive dependency graphs) with `doc-gen4`'s transitive
  dependencies (`Cli`, `CMark`, `UnicodeBasic`, `BibtexQuery`), outbound
  libraries should run `doc-gen4` from a separate CI-only `docs/` Lake
  workspace that depends on the root library and `doc-gen4`. `leanprover/verso`
  targets long-form literate manuals and verification blueprints rather than
  per-declaration API reference indices.
- **Import minimization (`lake exe shake`):** Lean `v4.34.1` ships `shake` in
  core (`src/Shake/Main.lean:1-95`), which inspects compiled `.olean` constant
  references across the module graph and reports redundant `import` statements
  without external dependencies.
- **GitHub Actions CI (`leanprover/lean-action` vs. Nix):** For standalone
  outbound repositories (`anneal-refinement`, `anneal-mir`, `anneal-tactics`),
  running two parallel CI jobs provides both ecosystem compatibility and
  hermetic guarantees:
  1. A standard `leanprover/lean-action@v1` job (pinned by 40-character commit
     SHA `52bbb8dde6eb0c6c1ef3a12bccecfdeaa25eb792` per Anneal's
     `ci/check_actions.sh` policy) that verifies `lake build` and `lake test`
     exactly as Reservoir's build worker executes them.
  2. A hermetic `nix flake check` job that verifies reproducible offline builds
     and runs `anneal-audit` over the compiled `.olean` outputs to guarantee
     zero `sorryAx`, zero `lean.trustCompiler` (`reduceBool` / `reduceNat`), and
     zero unapproved axioms.

---

### 4. Anneal's Four Publishable Standalone Library Layers

Basis: `primary source` (`joshlf/anneal` commit
`e75556f5767705404404c0675c6d2d9bcee41d6f` on `skeleton` and commit
`24367bd1a8c784f2578535954f9915e24894a56f` on `main`) and `empirical probe`
([`AnnealRefinementOutboundProbe.lean`][probe1]).

Inspecting the module dependency graph across `trusted/lean/`, `theory/Anneal/`,
and `trusted/audit/` in `joshlf/anneal` (`skeleton` commit
`e75556f5767705404404c0675c6d2d9bcee41d6f`) shows that Anneal's verification
stack decomposes into four publishable packages with clean dependency
boundaries:

| Layer / Package Name | Source Modules in `joshlf/anneal` (`skeleton`) | Size (Lines) | External / Internal Dependencies | Target Audience & Reusability |
| :--- | :--- | :--- | :--- | :--- |
| **1. `anneal-refinement`** | `theory/Anneal/Refinement.lean` (`241` lines), `theory/Anneal/StepResult.lean` (`352` lines), and `trusted/lean/Trusted/Refinement.lean` + `Trusted/StepResult.lean` | `593` lines | **Zero** (pure Lean `v4.34.1` `Init`/`Std` only; zero Rust or MIR types) | Any formal verification project in Lean 4 modeling trace inclusion, determinism preservation, compiler pass composition (`Pass.comp_correct`), or fuel-indexed operational semantics (`StepResult`, `runFuel`, `PartialObs.Refines`). |
| **2. `anneal-mir`** (`anneal-mir-semantics`) | `trusted/lean/Trusted/Memory.lean` (`273` lines), `Trusted/MirAst.lean` (`279` lines), `Trusted/MirSemantics.lean` (`334` lines), and `theory/Anneal/MirLemmas.lean` (`376` lines) | `1,262` lines | Depends only on `anneal-refinement` | Rust formal methods tools, MIR analyzers, and semantics researchers needing a mechanized, step-indexed `Runtime(PostCleanup)` MIR AST, byte-level allocation memory model, and determinism theorems. |
| **3. `anneal-tactics`** (`anneal-functional-translation`) | `theory/Anneal/FunctionalTranslation.lean` (`8,315` lines) | `8,315` lines | Depends on `anneal-refinement` and `anneal-mir` | Rust verification frameworks needing Anneal's symbolic evaluator, fuel-agnostics lemmas, `whileLoop_rule` / `nestedLoop_rule` framing, forward/backward borrow lenses (`BorrowLens`, `IndexedLens`, `RefChain2`, `ReborrowStep`), and kernel-checked `bv_decide` / LRAT tactics. |
| **4. `anneal-audit`** | `trusted/audit/src/lib.rs`, `trusted/audit/src/main.rs`, `trusted/audit/TrustedBoundary.lean`, and `trusted/lean/Trusted/Attributes.lean` | `1,073` lines | Standalone Rust binary + small Lean attribute library (`Anneal.Audit.Attributes`) | Any high-assurance Lean 4 project requiring an independent binary `.olean` inspector and two-color (`@[vetted]` vs. `@[candidate]`) kernel constant graph and axiom auditor. |

#### 4.1 Extraction Mechanics and Namespace Hygiene Across the Trust Boundary

In `joshlf/anneal` (`skeleton` commit
`e75556f5767705404404c0675c6d2d9bcee41d6f`), the files
`trusted/lean/Trusted/Refinement.lean` and
`trusted/lean/Trusted/StepResult.lean` already share identical declarations
with `theory/Anneal/Refinement.lean` and `theory/Anneal/StepResult.lean` (save
for `namespace Trusted` vs. `namespace Anneal`). When extracting
`anneal-refinement` and `anneal-mir` as standalone packages while preserving
Anneal's `trusted/` auditability invariant:

1. **Public namespace (`AnnealRefinement` / `Anneal.*`):** The standalone
   packages export their definitions under clean public namespaces (as
   demonstrated in [`AnnealRefinementOutboundProbe.lean`][probe1]).
2. **Trust-boundary pinning:** When `joshlf/anneal` consumes an extracted
   layer inside `trusted/lean/`, the dependency is pinned by exact 40-character
   Git commit SHA and Nix fixed-output `sha256` in `flake.nix` and
   `foundation-lock.json`, and its declarations carry `@[vetted]` in
   `TrustedBoundary.lean` so `anneal-audit` verifies the entire constant graph
   inside the Lean kernel.

---

### 5. Cross-Crate Verification and Receipt Reuse (`OD-08`, `LIB-01`–`LIB-10`)

Basis: `design deduction` and `empirical probe`
([`CrossCrateReceiptsProbe.lean`][probe2], compiled under Lean `v4.34.1` with
`-DwarningAsError=true` and zero `sorryAx`).

When a verified Rust library crate $A$ (such as `zerocopy` or an internal core
crate) is consumed by a downstream verified Rust crate $B$, Anneal must support
compositional verification without re-proving $A$'s internal lemmas, while also
allowing $B$ to verify calls to functions in $A$ that lack human-written
Anneal specifications and preventing unsoundness from mismatched compiler/target
assumptions (`OD-08`).

#### 5.1 Three Complementary Cross-Crate Verification Paths

[`CrossCrateReceiptsProbe.lean`][probe2] mechanizes all three cross-crate
verification paths in a single self-contained Lean `v4.34.1` file across
`CrossCrateProbe.UpstreamCrate` and `CrossCrateProbe.DownstreamCrate`:

1. **Path 1 — Abstract specification reuse (`LIB-01`, `LIB-03`, `LIB-05`,
   `LIB-08`):**
   - `UpstreamCrate` exports the abstract function contract
     `upstreamWeakContract : FnContract` (`Lines 324–326`), the verified
     summary theorem `upstream_add_bounded_abstract_spec :
     CalleeSatisfiesAbstractSpec env addBoundedId upstreamWeakContract`
     (`Lines 342–345`), and the domain type invariant `BoundedCounter.Valid`
     (`Lines 350–370`).
   - `DownstreamCrate` proves `verify_downstream_via_abstract_spec`
     (`Lines 428–446`) and `verify_downstream_counter_double` (`Lines 451–460`)
     for a caller invoking `MirBody.callThenCheckBound addBoundedId 2000` by
     applying the abstract contract `hUpSpec` without unfolding
     `addBoundedBody`.
2. **Path 2 — Direct dependency MIR body inspection (`LIB-06`, `LIB-07`):**
   - When an upstream function has no human-written contract, or when its
     published contract (`upstreamWeakContract`, guaranteeing only `res ≤ 2000`)
     is too weak to prove a downstream caller's postcondition (requiring
     `(x + y) % 2 = 0`, demonstrated by the counterexample theorem
     `weak_contract_insufficient_for_halve_even` at `Lines 487–492`),
     `anneal-rustc-capture` provides the upstream function's captured MIR body
     `addBoundedBody` (`Lines 317–320`).
   - `DownstreamCrate` proves `downstream_strengthened_upstream_exact`
     (`Lines 504–509`) and `verify_downstream_halve_even_via_mir_inspection`
     (`Lines 513–538`) by directly inspecting `addBoundedBody` to establish the
     stronger parity postcondition.
3. **Path 3 — Transitive `VerifiedCrateReceipt` and `SubjectIdentity` checking
   (`OD-08`, `LIB-02`, `LIB-04`, `LIB-09`, `LIB-10`):**
   - Every verified crate emits a machine-checkable `CrateReceipt`
     (`Lines 246–260`) binding its `SubjectIdentity` (`crateName`,
     `crateVersion`, `cargoMetadataHash`, `rustcCommitSha`, `targetTriple`, and
     `pointerWidthBits` at `Lines 112–125`), its `exportedSpecs`, its
     `allFnBodiesWellFormed` proof, and its `transitiveTcb : List TCBItem`.
   - `composeCrateVerification` (`Lines 267–296`) gates downstream verification
     on `CompatibleSubject up.subject downSubject` (`Lines 128–129`) and checks
     that every item in `up.transitiveTcb ++ localTcb` is permitted by the
     active `TrustPolicy`.
   - `downstream_clean_dag_verified` (`Lines 561–585`) proves that a matching
     `x86_64-unknown-linux-gnu` upstream/downstream pair succeeds under
     `defaultTrustPolicy`. Conversely,
     `downstream_tainted_upstream_rejected_by_default_policy` (`Lines 591–597`)
     proves that an upstream crate carrying `TCBItem.upstreamAssumedUnsafeSpec`
     is rejected unless the downstream consumer explicitly opts in via
     `allowUpstreamUnsafePolicy` (`Lines 601–643`), and
     `downstream_incompatible_target_rejected` (`Lines 659–663`) proves that a
     target mismatch (`x86_64-unknown-linux-gnu` vs. `aarch64-unknown-none`) is
     rejected.

#### 5.2 Consolidated Architecture for `LIB-01` Through `LIB-10`

| Item | Architectural Mechanism (Demonstrated in [`CrossCrateReceiptsProbe.lean`](support/CrossCrateReceiptsProbe.lean)) |
| :--- | :--- |
| **`LIB-01` (Artifact format)** | Hybrid dual-artifact model: Cargo metadata (`package.metadata.anneal`) points `cargo-anneal` to the upstream crate's Lean package (`Spec`, `MirAndProof`, and pre-compiled `.olean`s), accompanied by a machine-checked `VerifiedCrateReceipt` (`Lines 246-260`). |
| **`LIB-02` (Identity binding)** | `SubjectIdentity` (`Lines 112-125`) binds `crateName`, `crateVersion`, `cargoMetadataHash`, `rustcCommitSha`, `targetTriple`, and `pointerWidthBits` so `cargo-anneal` rejects stale or mismatched `.olean` artifacts. |
| **`LIB-03` (Export granularity)** | Logical split per verified crate: abstract contracts (`upstreamWeakContract`), `CalleeSatisfiesAbstractSpec` summaries, and domain types (`BoundedCounter`) are exported alongside captured `MirBody` definitions (`Lines 299-398`). |
| **`LIB-04` (Transitive soundness & `OD-08`)** | `composeCrateVerification` (`Lines 267-296`) enforces `CompatibleSubject up.subject downSubject` (`Lines 128-129`) and propagates `up.transitiveTcb ++ localTcb` into the downstream crate's `VerificationResult` (`Lines 85-90`). |
| **`LIB-05` (Call-site discharge)** | `CalleeSatisfiesAbstractSpec` (`Lines 220-241`) discharges call sites opaquely (`verify_downstream_via_abstract_spec`, `Lines 428-446`) without unfolding the callee's `MirBody`. |
| **`LIB-06` (Unannotated upstream dependencies)** | When an upstream function lacks an adequate specification (`weak_contract_insufficient_for_halve_even`, `Lines 487-492`), downstream proofs inspect its captured `MirBody` directly (`Lines 504-538`). |
| **`LIB-07` (Opaque vs. transparent calls)** | Callers choose per call site whether to apply the upstream `CalleeSatisfiesAbstractSpec` summary opaquely (`Path 1`, `Lines 428-460`) or unfold `evalMirBody env addBoundedBody` transparently (`Path 2`, `Lines 504-538`). |
| **`LIB-08` (Trait & generic polymorphism)** | Upstream crates export algebraic data invariants (`BoundedCounter.Valid`, `Lines 350-370`) and polymorphic contract schemas that downstream callers compose with call-site proofs (`verify_downstream_counter_double`, `Lines 451-460`). |
| **`LIB-09` (Cargo + Lake orchestration)** | `cargo-anneal` resolves the Cargo dependency graph (`cargo metadata`), materializes each upstream crate's Lean package into `.lake/anneal-crates/<crate>-<hash>`, emits `.lake/package-overrides.json`, and invokes `lake build --packages`. |
| **`LIB-10` (Versioning & cache invalidation)** | Because `SubjectIdentity` (`Lines 112-125`) binds `cargoMetadataHash`, `rustcCommitSha`, `targetTriple`, and `pointerWidthBits`, any change to `rustc`, target layout, or upstream source invalidates cached receipts automatically. |

## Boundaries

1. **Live Reservoir web-service submission not executed:** While Reservoir's
   exact eligibility logic (`Reservoir/Criterion.lean`, `Reservoir/Index.lean`,
   `Reservoir/Spdx.lean`) and GitHub's `licensee/licensee` classifier were
   inspected at source level and verified against live GitHub/Reservoir API
   responses (`google/zerocopy`, `NethermindEth/LeanCIL`, `rust-random/rand`),
   none of Anneal's four candidate packages have yet been pushed as standalone
   public GitHub repositories or indexed by the live Reservoir crawler.
2. **Unresolved historical short hash `a0f8c31` in `lenianiva/lean4-nix`:** An
   earlier workspace note referenced commit prefix `a0f8c31` for
   `lenianiva/lean4-nix`; querying the upstream `lenianiva/lean4-nix` Git
   history confirmed that no commit matching `a0f8c31*` exists. All `lean4-nix`
   findings in Section 1.4 are therefore anchored to the verified commits
   `6067688bc484f50f16dde1f2749bbb3e373198c9` (`Pantograph/flake.lock`) and
   `2ad74592e34c2e6ff5e8bec9d8abab8f4e9c3a37` (`main`).
3. **Multi-repository release automation:** Splitting `anneal-refinement`,
   `anneal-mir`, `anneal-tactics`, and `anneal-audit` into standalone GitHub
   repositories for Reservoir indexing will require either `git subtree split`
   release synchronization from the `joshlf/anneal` monorepo or independent
   repository release pipelines; designing that Git synchronization workflow is
   outside the scope of this report.

## Evidence

All primary-source digests and local probe artifacts are indexed in
[`support/source-manifest.json`](support/source-manifest.json). The two
standalone Lean `v4.34.1` verification probes in `support/` compile with zero
warnings and zero `sorryAx` under `-DwarningAsError=true`.

### 1. [`AnnealRefinementOutboundProbe.lean`][probe1]

- **SHA-256:**
  `2225e7df1a82185b62ee1de5efb473b1f7c98e1f02370a6bbef700320afc761f`
  (`20,015` bytes, `512` lines).
- **Purpose:** Synthesizes the standalone `anneal-refinement` outbound package
  (Layer 1A `Pass` / `PreservesMeaning` / `VerificationResult`, Layer 1B
  `StepResult` / `runFuel` / `PartialObs.Refines`, and `Tests`) with full API
  docstrings passing `linter.missingDocs = true` and `warningAsError = true`.

| Declaration / Theorem | Lines | Kind | Kernel Axiom Footprint (`#print axioms`) |
| :--- | :--- | :--- | :--- |
| `AnnealRefinement.AllHold` | `49–52` | `def` | — |
| `AnnealRefinement.allHold_mem` / `allHold_map` / `allHold_append` | `55–82` | `theorem` | `[]` |
| `AnnealRefinement.Preorder` / `Monotone` | `88–99` | `structure` / `def` | — |
| `AnnealRefinement.monotone_id` / `monotone_comp` | `102–111` | `theorem` | `[]` |
| `AnnealRefinement.Lang` / `PreservesMeaning` | `117–137` | `structure` / `def` | — |
| `AnnealRefinement.preservesMeaning_refl` / `preservesMeaning_trans` | `140–156` | `theorem` | `[]` |
| `AnnealRefinement.Pass` / `Pass.Correct` / `CorrectPass` / `Pass.Verified` | `162–186` | `structure` / `def` | — |
| `AnnealRefinement.Pass.id` / `Pass.id_correct` / `Pass.comp` | `190–205` | `def` / `theorem` | `[]` |
| `AnnealRefinement.Pass.comp_correct` | `208–218` | `theorem` | `[]` (verified via `#guard_msgs` at `L493–L494`) |
| `AnnealRefinement.Pass.verified_preserves_spec` | `222–231` | `theorem` | `[]` |
| `AnnealRefinement.TrustPolicy` / `VerificationResult` | `237–248` | `structure` / `def` | — |
| `AnnealRefinement.verify_with_pass` | `253–264` | `theorem` | `[]` (verified via `#guard_msgs` at `L499–L500`) |
| `AnnealRefinement.StepResult` / `FuelOutcome` / `runFuel` | `271–295` | `inductive` / `def` | — |
| `AnnealRefinement.PartialObs` / `PartialObs.Refines` | `299–325` | `inductive` / `def` | — |
| `AnnealRefinement.PartialObs.refines_refl` / `refines_trans` | `328–353` | `theorem` | `[propext]` |
| `AnnealRefinement.partialObsPreorder` / `FuelOutcome.toPartialObs` | `356–367` | `def` | — |
| `AnnealRefinement.runFuel_done_mono` / `runFuel_trap_mono` | `371–409` | `theorem` | `[propext]` |
| `AnnealRefinement.runFuel_toPartialObs_refines` | `413–432` | `theorem` | `[propext]` (verified via `#guard_msgs` at `L505–L506`) |
| `AnnealRefinement.Tests.countdownStep_done` / `countdownStep_refines_1_3` | `464–473` | `theorem` | `[propext]` |

### 2. [`CrossCrateReceiptsProbe.lean`][probe2]

- **SHA-256:**
  `a2352c7ff2b7e6b4f6f9451a1481ffafc52137530641ffa17f652d48c63dd283`
  (`30,106` bytes, `742` lines).
- **Purpose:** Synthesizes `CrossCrateProbe.UpstreamCrate`,
  `CrossCrateProbe.DownstreamCrate`, and `CrossCrateProbe.Tests` to validate
  Paths 1, 2, and 3 (`OD-08` and `LIB-01`–`LIB-10`).

| Declaration / Theorem | Lines | Kind | Kernel Axiom Footprint (`#print axioms`) |
| :--- | :--- | :--- | :--- |
| `CrossCrateProbe.AllHold` / `allHold_append` / `allHold_map_append` | `58–76` | `def` / `theorem` | `[]` |
| `CrossCrateProbe.TrustPolicy` / `VerificationResult` / `TCBItem` | `79–102` | `structure` / `inductive` | — |
| `CrossCrateProbe.SubjectIdentity` / `CompatibleSubject` | `112–129` | `structure` / `def` | — |
| `CrossCrateProbe.QualifiedFnId` / `MirEvalOutcome` / `MirBody` / `evalMirBody` | `132–193` | `structure` / `inductive` / `def` | — |
| `CrossCrateProbe.FnContract` / `SatisfiesContract` / `CalleeSatisfiesAbstractSpec` | `201–227` | `structure` / `def` | — |
| `CrossCrateProbe.calleeSatisfiesAbstractSpec_of_body` | `232–241` | `theorem` | `[propext]` |
| `CrossCrateProbe.CrateReceipt` / `VerifiedCrateReceipt` | `246–260` | `structure` / `abbrev` | — |
| `CrossCrateProbe.composeCrateVerification` | `267–296` | `theorem` | `[propext]` |
| `CrossCrateProbe.UpstreamCrate.addBoundedBody` / `upstreamWeakContract` | `317–326` | `def` | — |
| `CrossCrateProbe.UpstreamCrate.addBoundedBody_satisfies_weak` | `330–337` | `theorem` | `[propext]` |
| `CrossCrateProbe.UpstreamCrate.upstream_add_bounded_abstract_spec` | `342–345` | `theorem` | `[propext]` |
| `CrossCrateProbe.UpstreamCrate.BoundedCounter` / `BoundedCounter.Valid` | `350–370` | `structure` / `def` / `theorem` | `[]` |
| `CrossCrateProbe.UpstreamCrate.upstreamCleanReceipt` / `verify_upstreamCleanReceipt` | `374–387` | `def` / `theorem` | `[propext]` |
| `CrossCrateProbe.DownstreamCrate.verify_downstream_via_abstract_spec` | `428–446` | `theorem` | `[propext]` (verified via `#guard_msgs` at `L710–L711`) |
| `CrossCrateProbe.DownstreamCrate.verify_downstream_counter_double` | `451–460` | `theorem` | `[propext]` |
| `CrossCrateProbe.DownstreamCrate.weak_contract_insufficient_for_halve_even` | `487–492` | `theorem` | `[propext]` |
| `CrossCrateProbe.DownstreamCrate.downstream_strengthened_upstream_exact` | `504–509` | `theorem` | `[propext]` |
| `CrossCrateProbe.DownstreamCrate.verify_downstream_halve_even_via_mir_inspection` | `513–538` | `theorem` | `[propext, Quot.sound]` (verified via `#guard_msgs` at `L717–L718`) |
| `CrossCrateProbe.DownstreamCrate.downstream_clean_dag_verified` | `561–585` | `theorem` | `[propext]` (verified via `#guard_msgs` at `L723–L724`) |
| `CrossCrateProbe.DownstreamCrate.downstream_tainted_upstream_rejected_by_default_policy` | `591–597` | `theorem` | `[]` (verified via `#guard_msgs` at `L729–L730`) |
| `CrossCrateProbe.DownstreamCrate.downstream_tainted_upstream_accepted_with_explicit_policy` | `611–643` | `theorem` | `[propext]` |
| `CrossCrateProbe.DownstreamCrate.downstream_incompatible_target_rejected` | `659–663` | `theorem` | `[]` (verified via `#guard_msgs` at `L735–L736`) |

## Revalidation

Revalidate this report when upgrading the pinned Lean toolchain beyond
`v4.34.1`, modifying `flake.nix` or `trusted/lean/foundation-lock.json`,
changing the repository's root `LICENSE-*` files, or implementing cross-crate
receipt verification in `cargo-anneal`.

To re-run both standalone verification probes with all core linters and
`warningAsError` enabled:

```bash
cd reports/lean4-lake-reservoir-nix-and-outbound-library-publishing-2026
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -j1 -M1024 -DwarningAsError=true support/AnnealRefinementOutboundProbe.lean
/usr/local/google/home/joshlf/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean \
  -j1 -M1024 -DwarningAsError=true support/CrossCrateReceiptsProbe.lean
sha256sum support/AnnealRefinementOutboundProbe.lean support/CrossCrateReceiptsProbe.lean
```

[probe1]: support/AnnealRefinementOutboundProbe.lean
[probe1-tests]: support/AnnealRefinementOutboundProbe.lean#L436-L508
[probe2]: support/CrossCrateReceiptsProbe.lean
