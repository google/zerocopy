# Proof breakage across prover and library upgrades: AFP release carry-forward, Mathlib toolchain bumps and adaptation notes, Mathport alignment, Rocq CI overlays, and repair mining (PUMPKIN PATCH, PRISM)

## Summary

- **No examined source reports a per-prover-release breakage rate.** The quantitative proof-engineering studies examined here (seL4 process and productivity studies, the Archive of Formal Proofs mining study, PUMPKIN PATCH case studies, piCoq) measure proof size, effort, rework after *code or specification* changes, or proof-checking time. The only upgrade-induced breakage counts found are anecdotal case studies: one Coq standard-library change broke 18 standard-library proofs and was followed by 12 commits to downstream contributions; another broke 46 standard-library proofs (Ringer et al. 2018).
- **Every large ecosystem examined absorbs upgrade breakage with the same three-part protocol, but leaves different public records.**
  - The parts are an exact *pin*, a *test-ahead channel* against the next prover, and an *adaptation record*.
  - The AFP records only *presence* in each release: `afp_release` appends a release row for every entry currently in the archive.
  - Mathlib records toolchain bumps as commits. On `master` there were 37 bumps in the 12 months to 2026-11-20 (11 final releases and 26 release candidates), plus in-source `#adaptation_note` markers (364) and per-declaration `set_option backward.*` opt-outs (7,913).
  - Rocq records per-PR downstream *overlays*: 126 overlay files, with 309 `overlay` calls over 43 downstream projects, dominated by plugins that link the OCaml API.
- **Whole-library translation is mostly mechanical renaming.** Mathport's Lean 3 to Lean 4 declaration alignment table has 130,784 entries. Of these, 122,739 rename the declaration, and 106,250 of those renames differ only in letter case or underscores. Alignment support (`#align`) has since been removed from Mathlib, and no `#align` lines remain at the examined commit.
- **Repair tools and datasets are themselves version-bound.**
  - PUMPKIN PATCH builds for Coq 8.9.1 only. It handles six change kinds and does not apply the patches it finds.
  - PRISM keys every mined repair by *(project, initial commit, repaired commit, initial Coq version, repaired Coq version)*. That key lets the dataset express upgrade-induced repairs, but its tested Coq range is 8.9–8.15.
- **Compared with general package ecosystems:** about one third of Maven Central releases introduce at least one binary-incompatible change (Raemaekers et al. 2017). A later replication finds that 83.4% of 119,879 upgrades comply with semantic versioning and that only 7.9% of clients are affected (Ochoa et al. 2022). The proof libraries examined do not use semantic versioning at all. Their version axis is the prover release, and they replace compatibility promises with exact pins plus co-evolution processes. That is why "breaking change rate" in the semantic-versioning sense is not directly measurable for them.

## Applicability

**Subjects and their relationship.** This report compares *processes* and *records* across independent ecosystems. It does not compose the subjects with one another.

- **Lean/Mathlib.** `leanprover-community/mathlib4` at `5fc503cdd50c2c198f54ccc97121ec82919e2930` (committed 2026-11-20). At this commit `lean-toolchain` is `leanprover/lean4:v4.37.0-rc1`.
- **Mathport.** `leanprover-community/mathport` at `375a0a491c3179de17e4524875c69a7d92459588` (committed 2024-11-21, after Lean 3 end-of-life). Its `lean-toolchain` is `leanprover/lean4:v4.10.0-rc2`.
- **Isabelle AFP.** The GitHub mirror `isabelle-prover/mirror-afp-devel` at `523cdc72b5ae4a91c9ab8e1025d4a30b40472720` (committed 2026-11-18). The authoritative repository is Mercurial on Heptapod, and only the mirror was examined.
- **Rocq.** `rocq-prover/rocq` at `ddb69e5c5cff459fc2b0dfe3ec4ed0c968720c76` (committed 2026-11-20).
- **Repair tools.** `uwplse/PUMPKIN-PATCH` at `75e93275290c76d13a7a8b3a2124257be895f5e4` (committed 2021-09-02) and `Radiance-Technologies/prism` at `f54c9bf25488d022be16362944a389f1d01cbbe0` (committed 2024-02-05).
- **Literature.** Ten papers identified by DOI in `REPORT.json`. Full text was read for Andronick et al. 2012, Ringer et al. 2018, Palmskog et al. 2018, Raemaekers et al. 2017, Ochoa et al. 2022, and Decan–Mens 2021. Only the abstract or landing page was read for Blanchette et al. 2015, Staples et al. 2014, Klein 2014, and Reichel et al. 2023.

**Scope boundaries.**

- "Upgrade-induced breakage" means a proof or a definition that checked under prover/library version *v* and fails under *v′*, with no change to the proof's own project.
- Counts derived from repository files describe the examined revision only. Counts derived from commit history describe the window 2025-11-20 to 2026-11-20 (UTC) of commits reachable from the pinned commit.
- No prover, library, or downstream project was built. All build-time, memory, and artifact-size cells that are not cited are `not measured`.
- Findings about Mathlib's process apply to `master`. The `nightly-testing` branches live in a separate repository (`leanprover-community/mathlib4-nightly-testing`, named in `scripts/nightly-testing-checklist.lean` line 384), which was not examined.

## Findings

### 1. A common model: pin, test-ahead, adapt, record

Every ecosystem examined implements one protocol over three roles: an **upstream** (the prover, or a base library), a **library** (Mathlib, an AFP entry, a Rocq CI project), and **downstreams**.

```text
State per library L:   pin(L) = exact upstream revision L builds against
Upgrade step:          upstream publishes v'
  1. test-ahead:       build L against v' on a side channel (nightly branch / devel AFP / CI with overlays)
  2. adapt:            edit L (proof changes, compatibility switches, deprecation aliases)
  3. record:           leave an artifact describing the adaptation (or not)
  4. advance pin:      pin(L) := v'   (commit to lean-toolchain / AFP release / Rocq merge)
  5. propagate:        downstream D re-runs 1–4 with upstream := L
Invariant:             at every published state, L checks against pin(L)
```

Basis: derived from the source files cited in §§3–6.

| Mechanism | Mathlib (Lean) | AFP (Isabelle) | Rocq CI |
|---|---|---|---|
| Pin of prover | `lean-toolchain` (one line) | AFP release = Isabelle release; devel follows Isabelle repository head | Rocq PR head; downstream projects follow `master` until release, then commit hashes (`release-process.md` line 28) |
| Pin of libraries | `lake-manifest.json` `rev` (40-hex) per package, with `inputRev` branch names; `"fixedToolchain": true` (line 86) | single monorepo; no per-entry pin | `ci-basic-overlay.sh` `project <name> <giturl> <ref>` (73 `project` lines, 3 `subproject` lines) |
| Test-ahead channel | `nightly-testing` branches (separate repository); release candidates adopted on `master` | `afp-devel` against Isabelle development head; `isabelle afp_build -A` | full CI on every Rocq PR |
| Adaptation record | `#adaptation_note` (364 uses), `set_option backward.*` (7,913 uses), `@[deprecated]` (5,607 uses) | `[history]` entries in `metadata/entries/<entry>.toml` for changes that are more than maintenance (`doc/maintenance.md`) | overlay file `dev/ci/user-overlays/NNNNN-*.sh` plus a PR in the downstream repository |
| Who repairs downstream | PR authors and bump maintainers | entry maintainers, or Isabelle developers for small changes (`doc/maintenance.md` line 38) | downstream maintainers for libraries; PR author must prepare plugin overlays (`README-developers.md` §Breaking changes) |
| Escalation | — | email notification on failure (`afp_build_ci.scala` line 83) | project disabled in CI if not updated within 7 days (`README-developers.md` line 82) |

### 2. What quantitative studies actually measure

| Study | Corpus | Reported measure | Upgrade-induced? |
|---|---|---|---|
| Andronick et al. 2012 (ICSE) | seL4/L4.verified | design, development and verification cost under 14 person-years. Maintenance about one full-time person on average. Re-verifying a significant feature (memory-allocation API) took on the order of 6 months. Worst case: a change to under 5% of the code caused proof rework equal to 17% of the original effort (citing earlier seL4 work). Common case: re-verification effort is about 3–5× the code-change effort, e.g. 2 h to implement and about 6 h to re-verify | No: code/specification change |
| Staples et al. 2014 (ESEM) | nine L4.verified-related projects | "strong linear relationships between effort (in person-weeks) and size (in lines of proof script)" (abstract) | No |
| Klein 2014 (FM) | seL4 proof family | about 400,000 lines of Isabelle/HOL proof scripts (abstract) | No numbers on upgrades in the abstract |
| Blanchette et al. 2015 (CICM) | Archive of Formal Proofs | size, dependencies and proof style (landing-page abstract) | Full text not examined |
| Ringer et al. 2018 (CPP) | Coq standard library, CompCert, coq-contribs | case studies: an integer→real injection change broke 18 standard-library proofs and was followed by 12 commits to coq-contribs. A change to `divide` before Coq 8.4 broke 46 standard-library proofs | **Yes**, but anecdotal (two changes) |
| Palmskog et al. 2018 (ISSTA) | Coq projects across revisions | 4-way parallel proof checking with selection is up to 28.6× faster than sequential from-scratch checking, and up to 2.8× faster than sequential checking with selection | No: project revisions |

Basis: documentation (papers; full text or abstract as listed under Applicability).

**Consequence:** the published empirical base for *prover-upgrade* breakage is case studies, not rates. The operational records in §§3–6 are the only large-scale data, and none of them was designed to measure breakage.

### 3. Archive of Formal Proofs: release carry-forward and what its metadata can count

**Release mechanics (source).**

- `tools/afp_release.scala` lines 46–51 define `afp_release(date, isabelle)`, which appends `Metadata.Release(entry.name, date, isabelle)` to **every** entry in `AFP_Structure.load().entry_list`.
- `metadata/release-dates` maps Isabelle versions to dates: 31 Isabelle releases, from `2003 = 2003-05-13` to `2026 = 2026-10-25`.
- `metadata/releases.toml` stores, per entry, `<date> = "<Isabelle version>"` rows.

**Continuity measurement** (`support/afp_releases.py`; Basis: execution over the pinned files).

| Quantity | Value |
|---|---|
| Entries in `releases.toml` / `metadata/entries/*.toml` | 1,043 / 1,043 |
| Entries with a release row for Isabelle2026 | 1,042 |
| Entries whose last release is older than 2026 | 1 (`Iptables_Semantics`, last `2025-2`; still listed in `thys/ROOTS`) |
| Entries with a skipped Isabelle release between their first and last release | 1 (`Nominal2`) |
| Entries with more than one tarball date for one Isabelle release | 185 |
| Entry counts at selected releases | 2003: 4; 2013: 141; 2016: 313; 2021: 641; 2025: 940; 2025-2: 1,039; 2026: 1,042 |

**Interpretation limits.**

- Because `afp_release` registers every entry present in the structure, a release row records *presence at release time*, not "built without change".
- The 1,042/1,043 continuity is therefore a property of the editorial process (broken entries are fixed or temporarily removed before release), not a breakage rate.
- The 185 multi-date entries indicate re-issued tarballs within one Isabelle version. Their causes are not recorded in this file.
- Breakage *during* a development cycle is visible only in the Mercurial history of `afp-devel` and in CI status (`status.json` written by `afp_build_ci.scala` `sitegen`, lines 114–145), neither of which was examined.

**Maintenance policy (documentation, `doc/maintenance.md`).**

- Maintainers choose to work "in close lock step with Isabelle development, i.e. fix the entry immediately each time it breaks, or loosely, i.e. only shortly before a new Isabelle release" (lines 32–34). Lock step is recommended for base libraries.
- "Small changes might be done by the Isabelle development team for you as the change is introduced to Isabelle" (line 38). The prover's own developers therefore absorb part of the breakage cost, inside the archive.
- `tools/afp_build_ci.scala` line 189 builds all sessions except group `very_slow`, and line 83 emails maintainers on failure.
- `doc/regression-test.md` documents `isabelle afp_build -A` and the `slow`/`very_slow` exclusions.

### 4. Mathlib: toolchain pin, test-ahead, adaptation notes, deprecation windows, downstream checks

**Pins (source).**

- `lean-toolchain` = `leanprover/lean4:v4.37.0-rc1`.
- `lake-manifest.json` pins 8 packages (`plausible`, `LeanSearchClient`, `importGraph`, `proofwidgets`, `aesop`, `Qq`, `batteries`, `Cli`) by 40-hex `rev`, each with an `inputRev` branch or tag (`main`, `master`, or `v4.37.0-rc1` for the inherited `Cli`).
- The manifest carries `"fixedToolchain": true`.
- The daily workflow `update_dependencies.yml` (documented in `docs/workflows.md`) runs `lake update` and opens a bot PR with the new manifest. Library pins therefore advance by PR, never implicitly.

**Bump cadence** (`support/history_counts.sh`, `support/toolchain_cadence.py`; Basis: execution over GitHub commit history).

| Quantity (2025-11-20 → 2026-11-20, `master`) | Value |
|---|---|
| Commits changing `lean-toolchain` | 37, all titled `chore: bump toolchain to …` |
| Bumps to final releases | 11 (v4.26.0 … v4.36.0) |
| Bumps to release candidates | 26 (e.g. v4.29.0-rc1, -rc2, -rc3, -rc4, -rc6, -rc7, -rc8) |
| Interval between bumps | mean 10.1 d, median 6.6 d, min 0.63 d, max 40.6 d |
| rc1 → final adoption on `master`, per minor version | 17.0–51.8 d (v4.27–v4.36) |

Derived: Mathlib `master` advances its prover pin about every 10 days on average, and in this window it never pinned a nightly. Nightlies are confined to the separate `nightly-testing` repository.

**Test-ahead automation (source).**

- `scripts/nightly-testing-checklist.lean` "only reports" by default (module docstring).
- Its `--fix` loop repairs exactly one error class: `BuildError.isFixable` returns `e.message.contains "has already been declared"` (lines 188–189). That is the error raised when a declaration Mathlib defines has been upstreamed into Lean core or Batteries. The fix deletes the Mathlib command (byte range from `find_command_range.lean`) and rebuilds, for up to `maxIterations := 50` (line 300). It reverts if the first error does not move later.
- All other breakage classes are repaired by hand.

**Adaptation notes (source + execution).**

- `Mathlib/Tactic/AdaptationNote.lean` defines `#adaptation_note /-- … -/` as a command (line 58), a tactic, and a term wrapper (line 66). It logs an error if the doc comment is missing (line 38).
- Measurement (`support/adaptation_notes.py`) at the pinned commit counts command-position uses and excludes the defining file, textual mentions, strings, and commented-out code:

| Quantity | Value |
|---|---|
| `#adaptation_note` uses | 364 (Mathlib 353, MathlibTest 11) in 239 files |
| Notes citing a Lean PR (`lean4#N` or `leanprover/lean4/pull/N`) | 102 (93 PR-only, 4 with a nightly date, 3 with a bare date, 2 with a release version) |
| Notes citing a `nightly-YYYY-MM-DD` date | 33 (first year cited: 2023: 1, 2024: 2, 2025: 5, 2026: 25) |
| Notes with no version, PR or date reference | 222 |
| Notes immediately followed by `set_option backward.*` | 217 (203 `backward.isDefEq.respectTransparency.types`) |
| All `set_option backward.*` lines in `Mathlib/` | 7,913 (3,518 `…respectTransparency`, 1,970 `…respectTransparency.types`, 1,761 `backward.defeqAttrib.useBackward`, 459 `backward.privateInPublic`, …) |
| `Mathlib/` size | 8,730 `.lean` files, 2,373,450 lines, 100,432,116 bytes |

Derived:

- Only 217/7,913 ≈ 2.7% of backward-compatibility opt-outs carry an adaptation note.
- Adaptation notes therefore under-count upgrade debt by a large factor. The `backward.*` options are the more complete machine-readable record of *which declarations still depend on pre-upgrade semantics*.
- Notes average about 14.9 per 100,000 lines (353 / 2,373,450 × 10⁵).
- 222 of 364 notes (61%) cannot be tied to a prover version without consulting `git blame`.

**Deprecation window (source + execution).**

- `support/deprecations.py` counts 5,607 `@[deprecated …]` attributes in `Mathlib/`. 5,596 carry `since := "2026-…"` and 11 carry no `since`. There are also 146 `deprecated_module` commands.
- `.github/workflows/remove_deprecated_decls.yml` removes declarations deprecated before `'6 months ago'` (lines 16 and 104), monthly.
- Derived: Mathlib gives downstream users a rolling window of about six months to migrate away from renamed or removed declarations. The window is visible in the data, since no deprecation at the pinned commit is dated before 2026.

**Downstream checks (source).**

- `scripts/downstream_repos.yml` lists 35 downstream repositories (e.g. FLT, Carleson, PrimeNumberTheoremAnd, formal-conjectures).
- `.github/workflows/pr_check_downstream.yml` accepts `!downstream-check <name>[@rev] [--merge-branch]`. The default "LKG mode" cherry-picks the PR "onto the downstream's last-known-good mathlib commit" (lines 30–33), and `--merge-branch` tests the would-be-merged tree.
- `scripts/verify_version_tags.py` checks that each `vX.Y.Z[-rcK][-patchM]` Mathlib tag matches `lean-toolchain`, has a cache, and builds with `lake build --no-build`.

### 5. Mathport: whole-library translation with declaration alignment

- Mathport has two components: "binport" (Lean 3 `.lean` → Lean 4 `.olean`) and "synport" (best-effort Lean 3 `.lean` → Lean 4 `.lean`) (README).
- The README now begins with an end-of-life warning: "upstream (mathlib4) support for `#align` statements has ended, meaning that mathport no longer works on modern versions of mathlib4". It directs users to the `v3-eol` tags of both repositories, then to manual upgrade with `lake update`.
- At the pinned Mathlib commit there are 0 lines beginning `#align` under `Mathlib/`.

**Alignment table** (`Aligns/mathlib-align.json`, 8,508,151 bytes; `support/mathport_aligns.py`; Basis: execution).

| Quantity | Value |
|---|---|
| Lean 3 → Lean 4 declaration entries | 130,784 |
| Identical names | 8,045 |
| Renamed | 122,739 |
| Renamed only by letter case or underscores | 106,250 |
| Distinct Lean 4 targets | 129,416 |
| Lean 4 targets with more than one Lean 3 source | 303 |
| Module mappings (`mathlib-alignImport.json`) | 3,019 |

Derived:

- 86.6% of aligned declarations (106,250 / 122,739) changed name only by the naming-convention change (case/underscore).
- The remaining 16,489 renames, plus the 303 many-to-one merges, are the alignments that carry real semantic decisions.
- A translation with a declarative alignment table converts the "same theorem, new name" part of a major-version break into data, which is cheap to review. The rest needs human review.
- Mathport's `update_ports.sh` clones `lean3port` and `mathlib3port`, runs their `update.sh` scripts, and pushes the results, so translation output was regenerated repeatedly rather than produced once. How it was scheduled (`.github/workflows/update.yml`) was not examined.

### 6. Rocq: downstream CI with per-PR overlays

**Policy (documentation, `dev/ci/README-developers.md`).**

- A PR that breaks tested external projects must "assess the breakage" and write porting instructions.
- For plugins, the PR author "must prepare yourself an overlay".
- An unresponsive project is disabled after 7 days (line 82).
- "Fixes to external libraries (pure Rocq projects) *must* be backward compatible" (line 114). Plugin patches "can very rarely be made backward compatible and plugins we test will generally have a dedicated branch per Rocq version" (line 121).

**Format and semantics (source).**

- An overlay file is named with a five-digit PR number (`user-overlays/README.md` line 77). It contains `overlay <project> <giturl> <ref> <prnumber> [<prbranch>]` calls (line 84).
- `dev/ci/scripts/ci-common.sh` lines 23–41 implement `overlay`. The URL/ref replacement and the "not a known project" error apply only when `$CI_PULL_REQUEST` or `$CI_BRANCH` matches (lines 32–36), so overlays of merged PRs are inert.

**Overlay census** (`support/rocq_overlays.py`; Basis: execution over the pinned files).

| Quantity | Value |
|---|---|
| Overlay files present | 126 (PR numbers 19023–22854) |
| `overlay` calls | 309 over 43 distinct projects |
| Calls per file | 1: 68 files; 2: 23; 3: 13; 4–13: 22 files |
| Most-overlaid projects | elpi 53, equations 35, tactician 29, metarocq 24, mtac2 18, rocq_lsp 13, paramcoq 13, waterproof 13, lean_importer 11, rewriter 11, coq_lsp 9, quickchick 8 |
| Projects declared in `ci-basic-overlay.sh` | 73 `project` + 3 `subproject` |
| Overlaid names no longer declared | `bbv`, `coq_lsp`, `kami` (inert per lines 32–36) |
| Commits touching `dev/ci/user-overlays` (12 months) | 148; per month 4–18 |

Derived:

- The most-overlaid projects are predominantly plugins or tools that link Rocq's OCaml API (elpi, equations, tactician, metarocq, mtac2, paramcoq, rocq_lsp/coq_lsp), not pure proof libraries. This is consistent with the documented asymmetry: library fixes must be backward compatible and can merge ahead, while plugin fixes cannot.
- The *ML-API surface*, not the proof language, is the dominant upgrade-breakage channel visible in this record.
- Classification of each project as plugin or library was done by name and documentation, not by inspecting each repository.

**Release pinning (documentation, `dev/doc/release-process.md`).**

- At branching, "Pin the versions of libraries and plugins in `dev/ci/ci-basic-overlay.sh` to use commit hashes" (line 28).
- "any PR with overlays will require manually bumping the pinned commits when backporting" (line 37).
- The downstream pin is thus floating (`master`) during development and exact (commit hash) on release branches. Mathlib uses the reverse arrangement: it is exact on `master`, and nightlies float on a separate repository.

### 7. Repair tools and datasets mined from upstream changes

**PUMPKIN PATCH** (source + documentation).

- `plugin/src/configuration/kindofchange.ml` lines 6–27 enumerate the supported change kinds: `Conclusion`, `InductiveType`, `FixpointCase`, `ConclusionCase`, `Hypothesis`, `Identity`.
- The README states that the plugin "works for Coq 8.9.1" (branches for 8.5/8.6/8.8 unmaintained). It also says "PUMPKIN does not automatically apply patches that it finds". The suggested workaround is `Hint Resolve patch`.
- The paper's evaluation applies patches found from one example to analogous broken proofs, including the Coq 8.4 `divide` change.
- The repository's recorded evaluation logs (`plugin/eval/results.txt`, `default_results.txt`, `no_red_results.txt`, all headed "Welcome to Coq 8.5pl3") contain 50 patch searches each. `results.txt` and `default_results.txt` record 33 `SUCCESS` and 17 `FAILURE`; `no_red_results.txt` records 31 and 19.
- Every search in those logs finished in 0.049 s or less.
- Which failures are intended negative tests was not determined. Basis: source (recorded upstream output), not re-executed.

**PRISM** (source + documentation).

- Mining runs in two stages: cache extraction, which builds each commit and extracts per-command context through SerAPI, then repair mining over pairs of extracted commits.
- `prism/data/repair/mining.py` lines 381–405 define the repair key `CommitPairDBRecord(project_name, initial_commit_sha, repaired_commit_sha, initial_coq_version, repaired_coq_version)`.
- Because the Coq version is part of the key, a repair induced *only* by a prover-version change is representable (equal SHAs, different versions). Whether the published dataset contains such pairs was not examined.
- The README states SerAPI support for "7 minor versions of Coq ranging from 8.9 to 8.15" and default Coq 8.10.2. Extraction failures are grouped into build, cache, and miscellaneous errors, and "determination of the underlying cause of failure is a manual procedure".
- The dataset lists in `dataset/` name 193 accepted, 47 rejected, and 56 skipped projects. `split.json` assigns 162/61/62 project names to train/validation/test.
- Abstract (Reichel et al. 2023): commits are aligned across old and new versions of definitions and proofs. Building the dataset "highlight[ed] a number of challenges and gaps in existing infrastructure".

**piCoq** (documentation): see §2. Hypothesis: proof selection yields no savings on a prover upgrade, because every file depends on the changed prover. See Boundaries.

### 8. Comparison with general package ecosystems

| Property | Maven/npm/Cargo/Packagist/Rubygems (cited) | Proof libraries examined |
|---|---|---|
| Version signal | semantic versioning. ~1/3 of Maven releases have ≥1 breaking change (35.8% of majors, 35.7% of minors) (Raemaekers et al. 2017). 83.4% of 119,879 upgrades comply with semver, compliance is rising, and 7.9% of 293,817 clients are affected (Ochoa et al. 2022) | no semver. Mathlib tags mirror Lean versions (`verify_version_tags.py`); AFP releases are Isabelle releases; Rocq CI projects follow `master` |
| Dependency constraints | ranges. Post-1.0.0 constraints are largely compliant in Cargo, npm and Packagist; >16% of constraints in npm, Packagist and Rubygems were restrictive in Dec 2017 (Decan–Mens 2021) | exact pins (`lake-manifest.json` 40-hex `rev`; AFP monorepo; Rocq release-branch commit hashes) |
| Who absorbs a break | each client, after upgrade | the library and its CI (Rocq overlays, Mathlib bump PRs, Isabelle developers editing AFP entries) *before* the pin advances |
| Deprecation | Raemaekers et al. report deprecation tags "applied improperly" | Mathlib: dated `@[deprecated (since := …)]` with automated ~6-month removal |
| Measurable "breaking-change rate" | yes (API diff between versions) | not directly: the published state always checks, so breakage exists only transiently on test-ahead channels |

Derived:

- The proof ecosystems trade client-side breakage for centralized co-evolution, and they have the data to do so because the *checker* (the prover) is a perfect, mechanical client test.
- The cost is that breakage is invisible in published versions. It must be recovered from bump PRs, overlays, adaptation notes, and compatibility options.

### 9. Measuring breakage per prover release from public histories

| Signal | Distinguishes | Cannot distinguish |
|---|---|---|
| Mathlib `chore: bump toolchain` PR diffs | files/lines touched per bump; deletions of declarations upstreamed into core (`has already been declared`) | breakage absorbed earlier on `nightly-testing`; fixes landed by other PRs |
| `#adaptation_note` + `set_option backward.*` added per bump (diff over the bump commit) | semantic changes needing local opt-out; Lean PR when cited | 222/364 notes lack version references; 97% of opt-outs lack notes |
| Rocq overlay files per merged PR | which downstream projects a core change broke; plugin vs library | size of the downstream patch (lives in other repositories) |
| AFP `releases.toml` | presence/absence per release (1 entry absent in 2026) | amount of adaptation (needs `afp-devel` Mercurial diffs between release tags) |
| PRISM repair DB | proof-level repairs, keyed with Coq versions | causes of extraction failure (manual) |

Basis: derived from §§3–7.

**Recommended design.**

1. For each bump commit *c* (Mathlib) or merged PR with overlay (Rocq), compute the diff restricted to proof files, excluding the `lean-toolchain`/overlay line.
2. Classify each hunk as rename/deprecation (matched by `@[deprecated]` additions), compatibility opt-out (`set_option backward.*`), upstreamed-declaration deletion, or proof edit.
3. Normalize by library size at *c*.

No such measurement was run for this report.

### 10. Performance and resource footprint (L1–L6)

| Level | Quantity | Value | Source |
|---|---|---|---|
| L1 authoring/repair | seL4 re-verification after local code change | ≈3–5× code-change effort (2 h implement + ≈6 h proofs) | Andronick et al. 2012 |
| L1 | worst-case rework | <5% code change → 17% of original proof effort | Andronick et al. 2012 (citing earlier seL4 work) |
| L1 | maintenance staffing | ≈1 FTE on average after proof completion | Andronick et al. 2012 |
| L1 | upgrade adaptation effort per Lean or Isabelle release | not measured | — |
| L1 | adaptation markers in Mathlib | 364 notes; 7,913 `backward.*` opt-outs; 5,607 deprecations | this report, execution |
| L2 toolchain build | Lean/Rocq/Isabelle from scratch | not measured | — |
| L3 elaboration | Mathlib full build time per toolchain | not measured | — |
| L3 | PUMPKIN patch search | ≤0.049 s per recorded search (Coq 8.5pl3 logs) | upstream recorded output |
| L4 generated code | not applicable to proof upgrade breakage | — | — |
| L5 checking | regression proving speedup | up to 28.6× (4-way, vs sequential from scratch); up to 2.8× (vs sequential with selection) | Palmskog et al. 2018 |
| L5 | AFP full-archive check time | not measured (`very_slow` group excluded from CI) | — |
| L6 footprint | Mathlib source | 100,432,116 bytes, 8,730 files | this report, execution |
| L6 | Mathport alignment table | 8,508,151 bytes | this report, execution |
| L6 | `.olean`/`.vo` sizes, peak RSS of builds | not measured | — |

### 11. Human comprehensibility and conceptual simplicity (C1, C2)

**C1 (comprehensibility).**

- An adaptation note is human-oriented, which is good, but non-local: understanding *why* a proof looks odd requires the note's Lean PR reference. 61% of notes have none.
- A `set_option backward.X false in` line is machine-precise but semantically opaque without reading Lean's option documentation.
- Rocq overlays move diagnosis to the PR author, who sees CI failures in unfamiliar downstream code. The documentation's 7-day ultimatum is a social mechanism for bounding that cognitive load.
- AFP's "Isabelle developers fix small breakages" policy keeps diagnosis with the person who made the change, which is the most comprehensible assignment. It is feasible only because the archive is co-located.
- Distinguishing human from agent ease: the Mathlib `--fix` loop shows the only class that is fully mechanical today (duplicate declarations). Everything else is left to people.

**C2 (simplicity).**

- One invariant, "every published state checks against its pin", is enforced by four different mechanisms: toolchain file, manifest, release table, overlay file. These differ mainly in *where the pin lives* and *who may advance it*.
- A minimal common abstraction is a pin graph whose edges carry (upstream revision, adaptation patch, rationale). Adaptation notes, overlays, `backward.*` options and deprecations are all edge labels in that graph.
- The exceptions disappear if the rationale field is mandatory and links to the upstream change, as Rocq's overlay naming by PR number already does.
- This is a design observation, not a measured result.

### 12. Validation of the processes and tools (V1–V4)

- **V1 (specification adequacy, non-vacuity).**
  - Upgrade processes validate only that proofs *still check*, not that statements kept their meaning.
  - A `set_option backward.*` opt-out or a deprecation alias can preserve checking while a statement's elaboration changes. No examined process compares pre- and post-upgrade statements.
  - Mathport's alignment table is the one artifact that makes statement correspondence reviewable as data.
- **V2 (checker and lowering soundness).**
  - Mathlib's daily workflow runs `leanchecker` and nanoda (an independent checker), per `docs/workflows.md` line 83, on `master` and the current bump branch. A toolchain bump is therefore re-validated by an independent kernel daily.
  - The examined AFP and Rocq records show no equivalent independent re-check.
- **V3 (concurrency, crash, silicon).** Not applicable, apart from proof-checking parallelism (piCoq), whose correctness relies on Coq's asynchronous proof processing. Not examined.
- **V4 (field replay, human validation).**
  - Downstream checks are field replay: Mathlib's 35-repository list with LKG and merge modes, Rocq's 73-project CI, and AFP's whole-archive build.
  - REPLica-style instrumentation of real proof-engineer behaviour (Ringer et al., CPP 2020) exists for proof changes in general. Its data on upgrades was not examined.

## Boundaries

- **Not examined:**
  - the full texts of Blanchette et al. 2015, Staples et al. 2014, Klein 2014, and Reichel et al. 2023 (abstracts only);
  - the PRISM dataset contents (no count of repairs with differing Coq versions);
  - the `afp-devel` Mercurial history and CI `status.json`;
  - the `mathlib4-nightly-testing` repository and the `mathlib-ci` workflows;
  - Mathport's `update.yml` schedule;
  - the downstream repositories' adaptation patches;
  - Isabelle's own `NEWS`/incompatibility notes;
  - opam package constraints for Rocq libraries;
  - the Lean `lake update` semantics beyond the manifest fields quoted.
- **Unknown:**
  - the rate of upgrade-induced proof breakage per release in any ecosystem;
  - why `Iptables_Semantics` lacks an Isabelle2026 release row, and why `Nominal2` has a gap;
  - which PUMPKIN PATCH log failures are expected negative tests;
  - whether the 185 multi-date AFP releases are breakage fixes.
- **Hypothesis (not established):**
  - Regression proof selection (piCoq/iCoq) yields no savings on a prover upgrade, because compiled proof artifacts are prover-version-specific and every file transitively depends on the prover's prelude. Only parallelism would help.
  - The premise that `.vo` files are rejected across Coq versions was not checked at a pinned revision.
- **Known not to apply:** Andronick et al.'s 3–5× and 17% figures concern changes to the verified *code*, not prover upgrades. They must not be used as upgrade-cost estimates.
- **Attractive but unsupported conclusions:**
  - "Plugins break more often than libraries" is supported only as "plugins dominate the *overlay* record". Library breakage fixed backward-compatibly and merged ahead leaves no overlay, so overlays under-count library breakage.
  - "Mathlib needs a bump every 10 days" describes adoption on `master`, not the rate at which Lean breaks Mathlib.
  - "AFP entries rarely break" does not follow from 1,042/1,043 continuity.
- **Unsupported:**
  - PUMPKIN PATCH on any Coq other than 8.9.1 (per README);
  - Mathport on Mathlib after `v3-eol` (per README);
  - PRISM SerAPI support outside Coq 8.9–8.15 (per README).

## Evidence

All evidence was gathered on 2026-11-20 (UTC).

**Repositories (full revision, paths, lines).**

- `leanprover-community/mathlib4` @ `5fc503cdd50c2c198f54ccc97121ec82919e2930`:
  - `lean-toolchain`;
  - `lake-manifest.json` (line 86 `"fixedToolchain": true`);
  - `Mathlib/Tactic/AdaptationNote.lean` (lines 38, 58, 66);
  - `scripts/nightly-testing-checklist.lean` (lines 188–189, 300, 384);
  - `scripts/downstream_repos.yml`;
  - `scripts/verify_version_tags.py` (module docstring);
  - `.github/workflows/remove_deprecated_decls.yml` (lines 16, 104);
  - `.github/workflows/pr_check_downstream.yml` (lines 30–33);
  - `docs/workflows.md` (lines 83–84, 91).
  - Source tree obtained from `https://codeload.github.com/leanprover-community/mathlib4/tar.gz/<rev>` (24,391,637 bytes, SHA-256 `0cde257a632ef02363022720c9a0c407854c0c456445ac1f07d01449d0af39e1`; codeload archives are not guaranteed byte-stable).
- `leanprover-community/mathport` @ `375a0a491c3179de17e4524875c69a7d92459588`:
  - `README.md` (EOL warning; binport/synport);
  - `update_ports.sh`;
  - `lean-toolchain`;
  - `Aligns/mathlib-align.json` (SHA-256 `654868abefec155460d8d14be5f7a9fb9f9bcb5e3b01d040a697f77bf479a390`);
  - `Aligns/mathlib-alignImport.json` (SHA-256 `4de3ef426d001404fa1a63a1c1d3aefa107129478d1e4e40b1ee7ab0c9438c70`).
- `isabelle-prover/mirror-afp-devel` @ `523cdc72b5ae4a91c9ab8e1025d4a30b40472720`:
  - `metadata/releases.toml`;
  - `metadata/release-dates`;
  - `metadata/entries/*.toml`;
  - `thys/ROOTS`;
  - `tools/afp_release.scala` (lines 46–51);
  - `tools/afp_build_ci.scala` (lines 83, 114–145, 189);
  - `doc/maintenance.md` (lines 32–38);
  - `doc/regression-test.md`;
  - `doc/editors/merge-release-into-devel.md`.
- `rocq-prover/rocq` @ `ddb69e5c5cff459fc2b0dfe3ec4ed0c968720c76`:
  - `dev/ci/README-developers.md` (lines 82, 114, 121);
  - `dev/ci/user-overlays/README.md` (lines 77, 84);
  - `dev/ci/user-overlays/*.sh` (126 files);
  - `dev/ci/ci-basic-overlay.sh`;
  - `dev/ci/scripts/ci-common.sh` (lines 23–41);
  - `dev/doc/release-process.md` (lines 28, 37).
- `uwplse/PUMPKIN-PATCH` @ `75e93275290c76d13a7a8b3a2124257be895f5e4`:
  - `README.md`;
  - `plugin/src/configuration/kindofchange.ml` (lines 6–27);
  - `plugin/eval/results.txt`, `default_results.txt`, `no_red_results.txt`.
- `Radiance-Technologies/prism` @ `f54c9bf25488d022be16362944a389f1d01cbbe0`:
  - `README.md`;
  - `prism/data/repair/mining.py` (lines 105–118, 381–405);
  - `prism/data/repair/instance.py` (`ErrorInstance` docstring);
  - `dataset/accepted_names.txt`, `rejected_names.txt`, `skipped_names.txt`, `split.json`.

**Commit-history queries.** These used the GitHub REST API (`commits?path=…&sha=<pinned rev>&since=2025-11-20&until=2026-11-20`). The output is preserved with 12-character abbreviated SHAs in `support/history_counts.out`. Example bump commits: `31ce06eaadf4` (v4.37.0-rc1, PR #46167), `fc4f59e577fe` (v4.36.0, PR #46085), `7cc87f6abc95` (v4.26.0-rc2, PR #31877).

**Execution.** All scripts are under `support/` and are Python 3 standard library only, run on an x86_64 Linux workstation:

| Command | Output file |
|---|---|
| `python3 support/adaptation_notes.py <mathlib-root>` | `adaptation_notes.out` |
| `python3 support/deprecations.py <mathlib-root>` | `deprecations.out` |
| `python3 support/mathport_aligns.py mathlib-align.json mathlib-alignImport.json` | `mathport_aligns.out` |
| `python3 support/afp_releases.py releases.toml release-dates <tree-listing>` | `afp_releases.out` |
| `python3 support/rocq_overlays.py <user-overlays-dir> ci-basic-overlay.sh` | `rocq_overlays.out` |
| `bash support/history_counts.sh` | `history_counts.out` |
| `python3 support/toolchain_cadence.py history_counts.out` | `toolchain_cadence.out` |

The tree listing for `afp_releases.py` is the output of `gh api repos/<repo>/git/trees/<rev>?recursive=1 --jq '.tree[].path'`. Mathlib `.lean` line and byte totals came from `find Mathlib -name '*.lean' | xargs cat | wc -lc`.

**Literature.** DOIs were checked against dblp records on 2026-11-20. The Crossref API was not reachable from the fetch tool used.

| Work | DOI | Read |
|---|---|---|
| Andronick et al., ICSE 2012 | 10.1109/ICSE.2012.6227120 | full text, §V |
| Staples et al., ESEM 2014 | 10.1145/2652524.2652551 | abstract |
| Klein, FM 2014 | 10.1007/978-3-319-06410-9_2 | abstract |
| Blanchette, Haslbeck, Matichuk, Nipkow, CICM 2015 | 10.1007/978-3-319-20615-8_1 | landing-page abstract |
| Ringer, Yazdani, Leo, Grossman, CPP 2018 | 10.1145/3167094 | full text, §§1, 4.3 |
| Palmskog, Celik, Gligoric, ISSTA 2018 | 10.1145/3213846.3213877 | abstract and introduction |
| Raemaekers, van Deursen, Visser, JSS 2017 | 10.1016/j.jss.2016.04.008 | accepted manuscript, abstract and Table on release types |
| Ochoa, Degueule, Falleri, Vinju, EMSE 2022 | 10.1007/s10664-021-10052-y | arXiv:2110.07889 abstract |
| Decan and Mens, TSE 2021 | 10.1109/TSE.2019.2918315 | author manuscript, findings and conclusion |
| Reichel, Henderson, Touchet, Gardner, Ringer, ITP 2023 | 10.4230/LIPIcs.ITP.2023.26 | DROPS abstract |

Also cited without being examined in depth: Ringer et al., CPP 2020 (REPLica), DOI 10.1145/3372885.3373823.

## Revalidation

1. **Mathlib record drift.**
   - Re-download the tarball at a new commit and rerun `adaptation_notes.py` and `deprecations.py`. Each takes about 1 s on the extracted tree.
   - Compare against the counts here: 364 notes, 217 notes followed by `backward`, 7,913 `backward` opt-outs, 5,607 deprecations.
   - Check that `nightly-testing-checklist.lean` `isFixable` still matches only `"has already been declared"`, and that `remove_deprecated_decls.yml` still defaults to `'6 months ago'`.
2. **Bump cadence.** Rerun `history_counts.sh` with a new window and `toolchain_cadence.py`. A change in the share of `-rc` bumps, or the appearance of `nightly-` toolchains on `master`, would change §4's conclusions.
3. **AFP carry-forward.**
   - Rerun `afp_releases.py` on a newer mirror commit.
   - Diff `tools/afp_release.scala` lines 46–51. If `afp_release` stops registering every entry, release rows would start carrying build-status information.
4. **Rocq overlays.** Rerun `rocq_overlays.py` on the current `dev/ci/user-overlays/`. Diff `ci-common.sh` lines 23–41 for the activation condition and the 7-day and backward-compatibility rules in `README-developers.md`.
5. **Repair tools.** Check whether `PUMPKIN-PATCH` `README.md` still names Coq 8.9.1, and whether `prism` `mining.py` `CommitPairDBRecord` still includes both Coq-version fields.
6. **No cheap check exists for a breakage rate.** Producing one requires the measurement design in §9 (diffing bump commits and overlay PRs), which was not run.
