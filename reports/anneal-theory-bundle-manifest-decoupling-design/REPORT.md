# Decoupling Pass-1 `theory/` Registration from `trusted/` Magnet Files

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Adding a single `0`-TCB-LOC Pass-1 Lean theory module under `anneal/theory/Anneal/<Module>.lean` previously required modifying **five files inside `anneal/trusted/`** (`bundle.rs`, `bundled_resources.rs`, `target.rs`, `boundary_audit.rs`, and `SKILL.md`) plus `anneal/docs/alpha.md`, causing N-way merge conflicts with `trusted/` PRs and forcing Pass-2 TCB diff review on purely untrusted proof libraries.

The decoupled architecture separates trusted and untrusted bundle inventories across the trust boundary while preserving `cargo-anneal`'s self-contained packaging (`cargo package --locked -p cargo-anneal`, `--no-default-features`, zero `build.rs`, zero runtime checkout discovery):
1. **`anneal/theory/bundle-manifest.json`:** A sorted, schema-validated (`schema_version: 1`, `#[serde(deny_unknown_fields)]`), SHA-256-pinned opt-in inventory of bundled `theory/Anneal/**/*.lean` modules outside `trusted/`.
2. **Split pure-data embedding (`trusted/cargo-anneal/src/bundled_theory.json`):** Generated deterministically from `theory/bundle-manifest.json` and embedded via `include_str!("bundled_theory.json")` (pure UTF-8 JSON data, zero executable Rust syntax), leaving `trusted/cargo-anneal/src/bundled_resources.rs` strictly scoped to the 23 canonical `TRUSTED_BUNDLE_SOURCES` and `CORRESPONDENCE_PROVENANCE_JSON`.
3. **Dynamic test & audit discovery:** `EmbeddedBundle::assert_exact_theory_retention` (`target.rs`) and `boundary_audit.rs` consume `theory/bundle-manifest.json` / `bundle.theory_modules` dynamically, reducing hand-edited `trusted/` files per new `theory/` module from `4` to `0` and `trusted/` `.rs` (`include!`) churn from `1` to `0`.

## Applicability

This design characterizes `anneal/trusted/cargo-anneal/`, `anneal/trusted/audit/`, `anneal/theory/`, and `anneal/docs/alpha.md` in `google/zerocopy`, analyzed against the baseline of merged PR `#4092` (`[theory] Add classical excluded middle library`) and live `ExecSeal` / `ClaimAudit` / Receipt v3 PR `#4036` (`34006cc8fe`). Because the source design note (`support/DESIGN.md`) did not record full 40-hex commit hashes for `origin/main` or `#4092`, `REPORT.json` records `google/zerocopy` path coordinates and the inspected `#4036` short revision `34006cc8fe`.

Findings apply to `cargo-anneal` packaging (`cargo package --locked -p cargo-anneal` with default and `--no-default-features`), `regenerate_bundle`, and Pass-1 / Pass-2 `anneal-audit` (`scan_lean_tree_opts`, `cargo_boundary.rs`).

## Findings

### 1. Coupling Bottleneck in the Pre-Decoupling Layout

Basis: source (`support/DESIGN.md` §1, §4).

Prior to decoupling, registering a new bundled `theory/Anneal/<Module>.lean` module (such as `#4091` `Anneal.InitLemmas` or `#4092` `Anneal.ClassicalEm`) touched six shared "magnet" files:

| File | Inside `trusted/`? | Hand-edited? | Coupling Cause |
| :--- | :---: | :---: | :--- |
| `anneal/trusted/cargo-anneal/src/bundle.rs` | Yes | Yes | Hardcoded `BUNDLE_SOURCES` Rust array and doc comment listing every `theory/` module |
| `anneal/trusted/cargo-anneal/src/bundled_resources.rs` | Yes | Generated (`.rs`) | Single `include!`-ed Rust file combining `trusted/` files, `CORRESPONDENCE_PROVENANCE_JSON`, and all `theory/` files |
| `anneal/trusted/cargo-anneal/src/target.rs` | Yes | Yes | Existing `live_demand_driven_*` tests hardcoded negative assertions (`!sources.contains("Anneal.<Other>")`) for every bundled theory module |
| `anneal/trusted/audit/tests/boundary_audit.rs` | Yes | Yes | `rejects_trusted_correspondence_import_of_theory_in_pass2_preflight` duplicated a hardcoded bundled `theory/` list |
| `anneal/trusted/cargo-anneal/skills/cargo-anneal/SKILL.md` | Yes | Yes | Inline prose list enumerating every bundled `Anneal.*` module |
| `anneal/docs/alpha.md` | No | Yes | Inline prose list enumerating every bundled `Anneal.*` module |

This produced N-way merge conflicts with `trusted/` PRs (such as `#4036`, `#4062`, `#4063`) and forced Pass-2 TCB diff review on purely untrusted proof additions.

### 2. Hash-Locked `theory/bundle-manifest.json` + Split Pure-Data Bundle

Basis: source + derived (`support/DESIGN.md` §2, §4).

1. **Manifest (`anneal/theory/bundle-manifest.json`):** Uses `schema_version: 1` with `#[serde(deny_unknown_fields)]`, listing opt-in bundled `theory/Anneal/**/*.lean` modules and their SHA-256 digests in strictly ascending lexicographic order. Explicit opt-in ensures internal unbundled `theory/` modules (`Anneal.lean`, `Anneal.Core`, `Anneal.MirTotal`, `Anneal.PureLift`) are never packaged accidentally, while sorted ordering reduces concurrent `theory/` PR merge conflicts.
2. **Trusted Source Array (`bundle.rs`):** Retains only the 23 canonical `TRUSTED_BUNDLE_SOURCES`. `load_theory_bundle_manifest` and `render_bundled_theory` validate the manifest; `parse_bundled_theory` / `embedded_theory_bundle` re-validate schema, path confinement, canonical ordering, core module presence, and per-file SHA-256 digests.
3. **Disjoint Generated Outputs:**
   - `trusted/cargo-anneal/src/bundled_resources.rs` is generated solely from `TRUSTED_BUNDLE_SOURCES` + `CORRESPONDENCE_PROVENANCE_JSON` (preserving the exact `const CORRESPONDENCE_PROVENANCE_JSON: &str = ...;` line read by `anneal/flake.nix` and `tests/mvp_e2e.rs`, leaving `trusted/root-manifest.sha256` untouched).
   - `trusted/cargo-anneal/src/bundled_theory.json` records `manifest_sha256` and `{path, sha256, content}` per module, embedded strictly as UTF-8 data via `include_str!("bundled_theory.json")` (zero executable Rust syntax).
4. **Dynamic Test & Doc References:** `target.rs` introduces `EmbeddedBundle::assert_exact_theory_retention`, verifying retained modules and asserting that every other `Anneal.*` module in `bundle.theory_modules` (plus `Anneal.Unused`) is pruned from `sources`, compiled `.olean`s, and `--export-lean-lib`. `boundary_audit.rs` queries `TRUSTED_BUNDLE_SOURCES` and `load_theory_bundle_manifest`. `alpha.md` and `SKILL.md` point to `theory/bundle-manifest.json` rather than inline lists.

**Per-PR File Touch Comparison (against `#4092` baseline):**

| Category | Before (`#4092` baseline) | After Decoupling |
| :--- | :--- | :--- |
| Hand-edited `trusted/` files | `4` (`bundle.rs`, `target.rs`, `boundary_audit.rs`, `SKILL.md`) | `0` |
| Generated `.rs` (`include!`) files in `trusted/` | `1` (`bundled_resources.rs`) | `0` (`bundled_resources.rs` untouched) |
| Generated pure-data `.json` (`include_str!`) files in `trusted/` | `0` | `1` (`bundled_theory.json`, disjoint from `trusted/` PRs) |
| Total `trusted/` files touched | `5` | `1` (pure JSON data) |
| Magnet prose docs touched | `2` (`alpha.md`, `SKILL.md`) | `0` |
| Untrusted `theory/` files touched | `2` (`Foo.lean`, `Anneal.lean`) | `3` (`Foo.lean`, `Anneal.lean`, `bundle-manifest.json`) |

### 3. Preserved Security Invariants and Policy Boundaries

Basis: normative + source (`support/DESIGN.md` §3, §5).

| Security Invariant | Enforcement Mechanism |
| :--- | :--- |
| No runtime discovery of model/theory files from untrusted checkouts | `cargo-anneal verify` stages solely from compiled-in `BUNDLE` (`bundled_resources.rs`) and `embedded_theory_bundle()` (`include_str!("bundled_theory.json")`). |
| No executable Rust code outside `trusted/` and no `build.rs` | `cargo_boundary.rs` bans `build.rs`, `package.build`, and external path deps; `bundled_theory.json` uses `include_str!`, never `include!`. |
| Pass-2 containment (`include!`/`include_str!` stays inside `trusted/`) | `include_str!("bundled_theory.json")` references only a sibling file in `trusted/cargo-anneal/src/`. |
| Self-contained `cargo package --locked -p cargo-anneal` and `--no-default-features` | Both `bundled_resources.rs` and `bundled_theory.json` sit inside `trusted/cargo-anneal/src/`. |
| Statement-Origin Separation (`TargetRole::Model` vs. `TargetRole::Proof`) | `verify.rs` and `target.rs` assign `TargetRole::Model` only to `trusted/lean/*.lean` in `BUNDLE` and `TargetRole::Proof` unconditionally to `embedded_theory_bundle()`. |
| Fail-closed manifest & parity checks (`anneal-audit`, `regenerate_bundle --check`) | Rejects missing/symlinked manifest or parent dirs, malformed JSON, unknown fields, wrong `schema_version`, empty module list, missing `theory/Anneal/MirWp.lean`, duplicate/unsorted paths, paths outside `theory/Anneal/**/*.lean`, invalid Lean identifiers, bad SHA-256 digests, and disk/generated mismatches. |
| Pass-1 / Pass-2 Lean tree containment (`scan_lean_tree_opts`) | Explicit `allowed_non_lean: &[&str]` slice: `trusted/lean/` permits `["lean-toolchain", "foundation-lock.json"]`; `theory/` permits `["bundle-manifest.json"]`; `trusted/correspondence/` and `correspondence/` permit `&[]`. |
| Unchanged root manifest (`trusted/root-manifest.sha256`) | `Cargo.toml`, `Cargo.lock`, `flake.nix`, and `flake.lock` require zero changes. |

**Why `bundled_theory.json` Remains Under `trusted/cargo-anneal/`:** Moving `bundled_theory.json` outside `trusted/` fails `cargo package --locked -p cargo-anneal` (or violates `AGENTS.md`'s ban on `include_str!("../../../theory/...")` reaching outside `trusted/`), and `cargo_boundary.rs` forbids `build.rs`. Runtime loading from `share/anneal/theory/` was rejected because standalone `cargo anneal verify rustc` invocations without a share tree would break and would still require pinning a manifest hash inside `trusted/`. Consequently, `bundled_theory.json` stays in `trusted/cargo-anneal/src/`, while any relaxation of Pass-2 review rules in `anneal/AGENTS.md` when `bundled_theory.json` is the sole `trusted/` change remains an explicit maintainer policy choice.

### 4. Compatibility with `#4036` (`ExecSeal`, `ClaimAudit`, Receipt v3)

Basis: source (`support/DESIGN.md` §6, inspected against `#4036` at `34006cc8fe`).

- `bundle.rs`: Untouched by `#4036` (zero conflict).
- `verify.rs`: `#4036` modifies lines 43+ and 1497+; decoupling touches lines 1350–1383 (`BUNDLE` staging loop), yielding zero hunk conflict.
- `bundled_resources.rs`: `#4036` edits only `TrustedBoundary.lean`; rebasing onto post-`#4036` `main` only requires running `regenerate_bundle --root .`.
- `target.rs`: `#4036` renames `checker.stage.join("target-lib/...")` to `checker.stage.join("lib/...")`; centralizing the stage path parameter in `assert_exact_theory_retention` makes rebasing a mechanical `"target-lib"` → `"lib"` parameter update.
- `boundary_audit.rs`, `alpha.md`, `SKILL.md`: Disjoint hunk ranges from `#4036`.

## Boundaries

- **not examined (post-implementation runtime execution):** The source document (`support/DESIGN.md`) is a pre-landing architectural design and conflict analysis; compiled test-execution receipts from running `cargo test` and `anneal-audit` after landing the patch are not included in `support/DESIGN.md`.
- **known not to apply (literal zero `trusted/` files):** `trusted/cargo-anneal/src/bundled_theory.json` still lives under `trusted/` due to `cargo package --locked -p cargo-anneal` and `include_str!` confinement rules; `anneal/AGENTS.md` Pass-2 triggers are not automatically waived without explicit maintainer policy approval.
- **unsupported (runtime checkout discovery & `build.rs`):** Both runtime `theory/` discovery from untrusted checkouts and `build.rs` code generation remain intentionally excluded by `cargo_boundary.rs`.

## Evidence

- **Primary preserved design document:** [DESIGN.md](support/DESIGN.md) (copied cleanly from the design record, preserving all tables, threat-model invariants, and `#4036` hunk analyses).
- **Inspected repository references cited in `support/DESIGN.md`:**
  - `google/zerocopy` `anneal/trusted/cargo-anneal/src/{bundle.rs,bundled_resources.rs,target.rs,verify.rs}`
  - `google/zerocopy` `anneal/trusted/audit/tests/boundary_audit.rs`, `anneal/trusted/audit/src/{cargo_boundary.rs,repo_audit.rs}` (`scan_lean_tree_opts`)
  - `google/zerocopy` `anneal/docs/alpha.md`, `anneal/trusted/cargo-anneal/skills/cargo-anneal/SKILL.md`, `anneal/trusted/root-manifest.sha256`, `anneal/flake.nix`
  - `google/zerocopy` PR `#4036` (`34006cc8fe`) and PR `#4092` (compared baseline).

## Revalidation

To confirm this architecture holds against a live `google/zerocopy` checkout:
1. Inspect `anneal/theory/bundle-manifest.json` and `anneal/trusted/cargo-anneal/src/{bundle.rs,bundled_resources.rs,bundled_theory.json}` to verify that `bundled_resources.rs` contains only `TRUSTED_BUNDLE_SOURCES` + `CORRESPONDENCE_PROVENANCE_JSON` and `bundle.rs` embeds `bundled_theory.json` solely via `include_str!`.
2. Run `cargo run -p anneal-audit -- regenerate-bundle --check` (or `regenerate_bundle --check`) and `sha256sum --check --strict anneal/trusted/root-manifest.sha256`.
3. Run `cargo package --locked -p cargo-anneal` and `cargo test -p cargo-anneal --no-default-features` to verify self-contained packaging and offline parity.
