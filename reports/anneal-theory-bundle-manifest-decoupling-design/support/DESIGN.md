# Decoupling Pass-1 `theory/` Registration from `trusted/` Magnet Files

## 1. Problem Statement

Before this change, adding a single untrusted, `0`-TCB-LOC Pass-1 Lean theory
module under `anneal/theory/Anneal/<Module>.lean` (for example `#4091`
`Anneal.InitLemmas` or `#4092` `Anneal.ClassicalEm`) required editing **five
files inside `anneal/trusted/`** plus `anneal/docs/alpha.md`:

| File | Inside `trusted/`? | Hand-edited? | Why every new bundled `theory/` PR touched it |
| :--- | :---: | :---: | :--- |
| `anneal/trusted/cargo-anneal/src/bundle.rs` | Yes | Yes | Hardcoded `BUNDLE_SOURCES` Rust array + doc comment enumerating every `theory/` module |
| `anneal/trusted/cargo-anneal/src/bundled_resources.rs` | Yes | Generated (`.rs`) | Single generated Rust file (`include!`-ed) combining `trusted/` files, `CORRESPONDENCE_PROVENANCE_JSON`, and all `theory/` files |
| `anneal/trusted/cargo-anneal/src/target.rs` | Yes | Yes | Every existing `live_demand_driven_*` test hardcoded `assert!(!sources.contains("Anneal.<Other>"))` for every other bundled theory module |
| `anneal/trusted/audit/tests/boundary_audit.rs` | Yes | Yes | `rejects_trusted_correspondence_import_of_theory_in_pass2_preflight` duplicated a hardcoded list of bundled `theory/` files |
| `anneal/trusted/cargo-anneal/skills/cargo-anneal/SKILL.md` | Yes | Yes | Inline prose list enumerating every bundled `Anneal.*` module |
| `anneal/docs/alpha.md` | No | Yes | Inline prose list enumerating every bundled `Anneal.*` module |

This coupling caused two structural problems:

1. **N-way merge conflicts with `trusted/` PRs:** Untrusted `theory/` PRs
   collided directly with `trusted/` PRs modifying `TrustedBoundary.lean`,
   `bundled_resources.rs`, `target.rs`, `boundary_audit.rs`, `alpha.md`, and
   `SKILL.md` (notably `#4036`, `#4062`, `#4063`).
2. **Spurious TCB / Pass-2 review surface:** Every `0`-TCB-LOC `theory/` PR
   modified four hand-edited files plus a `include!`-ed Rust source file inside
   `trusted/`, forcing human/Pass-2 TCB diff review for purely untrusted proof
   libraries.

---

## 2. Architecture: Hash-Locked `theory/bundle-manifest.json` + Split Pure-Data Bundle

This design splits trusted and untrusted bundle inventories along the trust
boundary while keeping `cargo-anneal` 100% self-contained (zero runtime
filesystem discovery, full `cargo package --locked -p cargo-anneal` and
`--no-default-features` compatibility, zero `build.rs`):

1. **`anneal/theory/bundle-manifest.json` (new, outside `trusted/`):**
   - Sorted, schema-validated (`schema_version: 1`, `#[serde(deny_unknown_fields)]`),
     SHA-256-pinned JSON manifest listing the opt-in set of bundled Pass-1
     `theory/Anneal/**/*.lean` modules.
   - Preserves explicit opt-in semantics: unbundled internal `theory/` trees
     (`Anneal.lean`, `Anneal.Core`, `Anneal.MirTotal`, `Anneal.PureLift`) are
     never accidentally packaged into target verification.
   - Strictly ascending lexicographic order eliminates duplicate entries and
     reduces concurrent `theory/` PR merge conflicts (independent modules insert
     at distinct sorted positions).
2. **`anneal/trusted/cargo-anneal/src/bundle.rs` (`TRUSTED_BUNDLE_SOURCES`):**
   - Retains only the 23 canonical `trusted/` source paths
     (`TRUSTED_BUNDLE_SOURCES`).
   - Loads and strictly validates `theory/bundle-manifest.json` via
     `load_theory_bundle_manifest` and `render_bundled_theory`.
   - Embeds `trusted/cargo-anneal/src/bundled_theory.json` strictly as UTF-8
     data via `include_str!("bundled_theory.json")` and re-validates schema,
     path confinement, canonical ordering, required core module presence, and
     per-file SHA-256 digests in `parse_bundled_theory` /
     `embedded_theory_bundle`.
3. **Split generated outputs inside `trusted/cargo-anneal/src/`:**
   - `trusted/cargo-anneal/src/bundled_resources.rs`: Generated **solely** from
     `TRUSTED_BUNDLE_SOURCES` + `CORRESPONDENCE_PROVENANCE_JSON`. Never changes
     when `theory/` modules are added or edited. Preserves the exact
     `const CORRESPONDENCE_PROVENANCE_JSON: &str = ...;` line consumed by
     `anneal/flake.nix` (so `flake.nix` and `trusted/root-manifest.sha256`
     remain untouched) and `tests/mvp_e2e.rs`.
   - `trusted/cargo-anneal/src/bundled_theory.json`: Generated deterministically
     from `theory/bundle-manifest.json` + the verified on-disk `theory/` source
     files, embedding `manifest_sha256` plus `{path, sha256, content}` per
     module. Included via `include_str!` (pure UTF-8 data — **zero executable
     Rust syntax**).
4. **Dynamic test helpers (`target.rs`, `boundary_audit.rs`) and docs (`alpha.md`, `SKILL.md`):**
   - `target.rs` adds `EmbeddedBundle::assert_exact_theory_retention`, checking
     every retained module AND asserting that **every other** bundled `Anneal.*`
     module in `bundle.theory_modules` (plus `Anneal.Unused`) is pruned from
     `sources`, compiled `.olean`s, and `--export-lean-lib`. This is strictly
     stronger than prior hand-maintained negative assertion lists and requires
     zero edits when new `theory/` modules are added.
   - `boundary_audit.rs` (`rejects_trusted_correspondence_import_of_theory_in_pass2_preflight`)
     copies bundled sources dynamically from `TRUSTED_BUNDLE_SOURCES` and
     `load_theory_bundle_manifest` instead of duplicating a hardcoded list.
   - `docs/alpha.md` and `trusted/cargo-anneal/skills/cargo-anneal/SKILL.md`
     cite illustrative examples and point to `theory/bundle-manifest.json` as
     the canonical inventory.

---

## 3. Threat Model & Preserved Security Invariants

| Security Invariant (`docs/trust-model.md` / `AGENTS.md` / `cargo_boundary.rs`) | Enforcement Mechanism |
| :--- | :--- |
| **No runtime discovery of model/theory files from untrusted checkouts** | `cargo-anneal verify` stages exclusively from compiled-in `BUNDLE` (`bundled_resources.rs`) and `embedded_theory_bundle()` (`include_str!("bundled_theory.json")`). Neither `theory/bundle-manifest.json` nor the repository checkout is ever read at target verification runtime. |
| **No executable Rust code outside `trusted/` and no `build.rs`** | `cargo_boundary.rs` still bans `build.rs`, `package.build`, and any crate or path dependency outside `trusted/`. `bundled_theory.json` is pure JSON data embedded with `include_str!`, never compiled as Rust syntax (`include!`). |
| **`AGENTS.md` Pass-2 containment (`include!`/`include_str!` never reaches outside `trusted/`)** | `include_str!("bundled_theory.json")` references only a sibling file inside `trusted/cargo-anneal/src/`. No `#[path]`, `include!`, or `include_str!` reaches outside `trusted/`. |
| **Self-contained `cargo package --locked -p cargo-anneal` and `--no-default-features`** | Both `bundled_resources.rs` and `bundled_theory.json` reside inside `trusted/cargo-anneal/src/` and are packaged into the crate tarball automatically. |
| **Statement-Origin Separation (`TargetRole::Model` vs. `TargetRole::Proof`)** | `verify.rs` and `target.rs` assign `TargetRole::Model` exclusively to `trusted/lean/*.lean` entries from `BUNDLE` and unconditionally assign `TargetRole::Proof` to every entry from `embedded_theory_bundle()`. |
| **Fail-closed manifest & parity checks in CI (`anneal-audit` + `regenerate_bundle --check`)** | `load_theory_bundle_manifest`, `render_bundled_theory`, and `verify_bundled_resources` fail closed (policy exit code `1`) on: missing/symlinked manifest or parent dirs, malformed JSON or unknown fields, wrong `schema_version`, empty module list, missing required `theory/Anneal/MirWp.lean`, duplicate or unsorted paths, paths outside `theory/Anneal/**/*.lean` (including `theory/Anneal.lean`, `trusted/...`, and `..` traversal), invalid Lean identifiers, non-lowercase/invalid SHA-256 digests, any on-disk file hash mismatch, and any byte mismatch or deletion/symlink of `bundled_resources.rs` or `bundled_theory.json`. |
| **Pass-1 / Pass-2 Lean tree containment (`scan_lean_tree_opts`)** | `scan_lean_tree_opts` takes an explicit `allowed_non_lean: &[&str]` slice: `trusted/lean/` permits only `lean-toolchain` and `foundation-lock.json`; `theory/` permits only `bundle-manifest.json` (still rejecting symlinks and any other non-Lean file); `trusted/correspondence/` and `correspondence/` permit `&[]` (rejecting `bundle-manifest.json`). Every `.lean` file in `theory/` still undergoes Pass-1 `"preflight"` + `"audit"` + fresh kernel replay. |
| **Unchanged root manifest (`trusted/root-manifest.sha256`)** | `Cargo.toml`, `Cargo.lock`, `flake.nix`, and `flake.lock` require zero modifications (`sha256sum --check --strict trusted/root-manifest.sha256` passes unchanged). |

---

## 4. Before vs. After: File Touches for a New Bundled `theory/` Module

Measuring against real merged PR `#4092` (`[theory] Add classical excluded middle library`):

| Category | Before (`#4092` on `origin/main`) | After (this patch) |
| :--- | :--- | :--- |
| **Hand-edited `trusted/` files** | **4** (`bundle.rs`, `target.rs`, `boundary_audit.rs`, `SKILL.md`) | **0** |
| **Generated `.rs` (`include!`) files in `trusted/`** | **1** (`bundled_resources.rs`, shared with `TrustedBoundary.lean` & `CORRESPONDENCE_PROVENANCE_JSON`) | **0** (`bundled_resources.rs` untouched) |
| **Generated data-only `.json` (`include_str!`) files in `trusted/`** | **0** | **1** (`trusted/cargo-anneal/src/bundled_theory.json`, disjoint from all `trusted/` PRs) |
| **Total `trusted/` files touched** | **5** (4 hand-edited + 1 `include!` `.rs`) | **1** (0 hand-edited + 1 generated pure-data `.json`) |
| **Magnet prose docs touched (`alpha.md`, `SKILL.md`)** | **2** (`alpha.md` + `SKILL.md`) | **0** |
| **Untrusted `theory/` files touched** | **2** (`theory/Anneal/Foo.lean`, `theory/Anneal.lean`) | **3** (`theory/Anneal/Foo.lean`, `theory/Anneal.lean`, `theory/bundle-manifest.json`) |
| **Conflicts with `#4036` / `#4062` / `#4063`** | Collides on 5–6 shared files | **0** conflicting files |

---

## 5. Honest Analysis of `anneal/AGENTS.md` Pass-2 Triggers & Future Zero-`trusted/` Options

Per `anneal/AGENTS.md` (*Pass order and surface scope*), Pass 2 is triggered
whenever a PR touches any path under `trusted/`. Because
`trusted/cargo-anneal/src/bundled_theory.json` physically resides under
`trusted/`, **this patch intentionally does NOT claim literal 0 `trusted/`
files or unilaterally relax `anneal/AGENTS.md`**:

- **Why `bundled_theory.json` must remain under `trusted/cargo-anneal/` today:**
  1. `cargo package --locked -p cargo-anneal` packs only files inside
     `anneal/trusted/cargo-anneal/`; an `include_str!("../../../theory/...")`
     fails packaging and breaks self-contained `cargo-anneal` /
     `--no-default-features` builds.
  2. `anneal/AGENTS.md` Pass-2 containment explicitly forbids `trusted/` from
     using `include!`, `include_str!`, or `#[path]` to reach outside `trusted/`.
  3. `cargo_boundary.rs` forbids `build.rs` scripts.
- **Why this still resolves the operational and review bottleneck cleanly:**
  - `bundled_theory.json` contains **zero Rust syntax**, is embedded strictly as
    UTF-8 data via `include_str!`, is parity-verified byte-for-byte against
    `theory/bundle-manifest.json` by `anneal-audit` and `regenerate_bundle --check`,
    and is **100% disjoint** from `bundled_resources.rs`, `bundle.rs`,
    `target.rs`, `boundary_audit.rs`, `SKILL.md`, and `alpha.md`.
  - **Optional follow-up (requires explicit human Gate-5 policy approval):**
    Maintainers may add a narrow clause in `anneal/AGENTS.md` noting that when
    `trusted/cargo-anneal/src/bundled_theory.json` is the *sole* path changed
    under `trusted/`, Pass-2 review of that file reduces to verifying
    `regenerate_bundle --check` and `anneal-audit` parity rather than full TCB
    code review.
  - **Why loading `theory/` from `share/anneal/theory/` at runtime was rejected:**
    It would break `--no-default-features` and standalone `cargo anneal verify
    rustc` invocations that supply only `--capture`, `--sysroot`, and `--lean`,
    and would still require pinning a manifest hash inside `trusted/` to prevent
    untrusted checkout substitution.

---

## 6. Compatibility with PR `#4036` (`ExecSeal`, `ClaimAudit`, Receipt v3)

Inspected against live PR `#4036` (`34006cc8fe`):

- `bundle.rs`: Untouched by `#4036` (zero conflict).
- `verify.rs`: `#4036` modifies lines 43+ (`include!("bundled_resources.rs");`)
  and lines 1497+; this patch touches only lines 1350–1383 (`BUNDLE` staging
  loop) and puts `include_str!("bundled_theory.json")` inside `bundle.rs`,
  yielding **zero hunk conflict** with `#4036`.
- `bundled_resources.rs`: `#4036` updates only `TrustedBoundary.lean` inside
  `bundled_resources.rs`; rebasing onto post-`#4036` `main` requires only
  running `regenerate_bundle --root .`.
- `target.rs`: `#4036` renames `checker.stage.join("target-lib/...")` to
  `checker.stage.join("lib/...")`; because this patch centralizes that path
  argument through `assert_exact_theory_retention`, rebasing onto `#4036` is a
  mechanical `"target-lib"` -> `"lib"` parameter update across the test calls.
- `boundary_audit.rs`, `alpha.md`, `SKILL.md`: All edits sit in disjoint hunk
  ranges from `#4036` (zero conflict).
