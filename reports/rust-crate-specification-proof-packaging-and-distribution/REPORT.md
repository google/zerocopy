# Rust Crate Specification, Proof, and Receipt Packaging and Distribution

## Summary

Distributing formal specifications, proofs, verification receipts, shared domain theories, and transitive verification dependencies alongside Rust crates involves five interacting constraints across Cargo, `crates.io`, downstream build systems (Bazel `rules_rust`, Fuchsia `cargo-gnaw`), Rust compilers, and theorem-prover toolchains:

1. **Registry limits, index omission, and packaging hazards (`crates.io` and Cargo):** `crates.io` enforces a 10 MiB compressed `.crate` upload cap, a 512 MiB unpacked cap, 30,000 tarball entries, and a 1 MiB cap on `Cargo.toml`/`.cargo_vcs_info.json`. The `crates.io` sparse/git index omits `[package.metadata.*]` entirely, so discovering manifest-embedded verification metadata requires unpacking the `.crate` tarball. Setting both `package.include` and `package.exclude` causes `cargo package` to silently ignore `exclude`. Namespaced `dep:` and weak `pkg?/feat` feature syntax requires Cargo `>= 1.60.0` (breaking crates with lower MSRVs such as `zerocopy` at `1.56.0`).
2. **Cargo dependency-graph and vendoring asymmetry:** Live execution against `cargo 1.102.0-nightly` and source inspection of `rust-lang/cargo` establish a three-way split for companion crates: (a) an upstream registry crate's `[dev-dependencies]` never enter downstream `Cargo.lock` or `cargo vendor`; (b) an upstream registry crate's inactive `optional = true` `[dependencies]` likewise stay **out** of downstream `Cargo.lock` and `cargo vendor` (unlike a workspace member's own inactive optional dependencies, which are locked and vendored); and (c) an upstream crate's `[target.'cfg(any())'.dependencies]` enter downstream `Cargo.lock` and `cargo vendor` unconditionally while never being compiled by `rustc`.
3. **Circular checksum constraint and supply-chain binding:** Because `cargo package` rewrites `Cargo.toml` (saving `Cargo.toml.orig`), injects `.cargo_vcs_info.json`, and hashes the resulting `.crate` archive into `Cargo.lock`, neither `[package.metadata.*]` nor any file inside the `.crate` can contain the `.crate` tarball SHA-256. Furthermore, `.cargo-checksum.json` explicitly warns it is not a security mechanism and `DirectorySource::verify` checks only listed keys (`files: {}` or untracked files pass unchecked). A canonical sorted manifest SHA-256 over `(logical_rel_path, sha256)` of the `rustc`-consumed Rust and specification source files is invariant across Git checkouts, unpacked `.crate` archives, `cargo vendor`, and Bazel/GN/Nix extractions. `crates.io` Trusted Publishing (OIDC) publicly exposes registry-asserted `trustpub_data` (`provider`, `repository`/`project_path`, `run_id`/`job_id`, `sha`) on version API responses, but does not serve downloadable Sigstore/SLSA DSSE cryptographic attestation bundles.
4. **Non-monotonic feature unification and slice identity:** Because Rust code uses negative `cfg` predicates (for example, `zerocopy/src/` contains 8 live `not(feature = "derive")` sites and `zerocopy/build.rs` emits up to 10 negative toolchain-version `cfg`s), Cargo's additive workspace feature unification is **non-monotonic at the MIR level**. A pre-verified slice receipt `(target, cfgs_A)` cannot safely be reused under `(target, cfgs_A ∪ cfgs_B)` by `cfg`-subset matching alone. Today's `cargo-anneal` `capture_sha256` hashes raw `capture.json` (which contains host paths, raw `cfg` strings, and crate-wide unselected `census`), so cross-machine and feature-unification slice invariance requires hashing the canonical path-free `Program` (`Captured.lean` / `manifest.program`) together with `SemanticProfile` (`{target, opt_level, debug_assertions, overflow_checks, mir_preserve_ub, pointer_bits, endian}`).
5. **Cross-crate composition, downstream Bazel/GN amplification, and ecosystem prior art:** Across Verus, Creusot, Kani/`verify-rust-std`, Charon/Aeneas, Dafny `.doo`, LiquidHaskell `.hi`/`.spec`, SPARK/Alire, Frama-C WP, Rocq `.vos`/`.vok`, `cargo-vet`/`cargo-crev`, and TypeScript `@types`/`package.json` `"exports"`, ecosystems converge on five lessons: (i) ship lightweight proof-free specifications/interfaces separately from proof bodies and toolchain-locked binaries; (ii) fail closed on conflicting transitive external specifications rather than merging them; (iii) disambiguate crate namespaces by `PackageId`/`StableCrateId` to survive semver-major diamonds; (iv) guard against `rules_rust` `crate_universe`'s consumer-side default `compile_data_glob = ["**"]`, which sweeps in-crate files into production `rust_library` `compile_data`; and (v) treat `exocrate` (`0.3.0`) as a compile-time `(OS, ARCH)` CLI-toolchain fetcher (whose pre-SHA staging bug is fixed on `google/zerocopy` `a6864119`) rather than a dynamic dependency-graph proof resolver, whereas a zero-runtime `#![no_std]` Cargo "theory carrier crate" natively inherits `Cargo.lock` + `cargo vendor` offline distribution.

## Applicability

This report synthesizes primary-source code inspection and live Cargo execution across the 22 subjects pinned in `REPORT.json` as of `2026-11-23`:

- **Rust packaging and build systems:** `rust-lang/cargo` (`930a674d`), live `cargo 1.102.0-nightly (c07ac2c4d 2026-11-06)`, `rust-lang/crates.io` (`18a7cf31`), `bazelbuild/rules_rust` (`5d99ff2e`, `crate_universe`), and Fuchsia `tools/cargo-gnaw` (`af754e2e`).
- **Anneal, `exocrate`, and `zerocopy`:** `google/zerocopy` at `a68641199cdfa99f96cb62f0cde921c9d36bfb22` (`anneal-v0.2.0-alpha.8`). This report builds on—rather than repeating—existing corpus reports covering `exocrate` archive layout, Lean 4 `v4.34.1` Lake/Reservoir publishing, monorepo `rustc`/`Cargo` multi-version orchestration, and ELF/Mach-O/PE compiled-binary evidence bundles; where `exocrate` changed since earlier corpus revisions, the updated behavior at `a6864119` is noted explicitly.
- **Prior-art verification and overlay ecosystems:** Verus (`1ce6a59b`), Creusot (`faeb61f5`), Kani (`87c87010`), `verify-rust-std` (`1feeadd9`), Charon (`b23c297f`), Aeneas (`2e3d4488`), `cargo-vet` (`a9bde859`), `cargo-crev` (`e0e71f9d`), Dafny (`427892ac`), LiquidHaskell (`7c809b68`), SPARK 2014 (`1ce0965f`), Alire (`65765597`), Frama-C WP (`639a3647`), Rocq (`21891774`), DefinitelyTyped (`de614c26`), and `microsoft/typescript-go` (`89d5d5b2`).

Findings describe source-level packaging, dependency resolution, metadata discovery, trust binding, and cross-crate composition for Rust crates. They do not describe post-link binary attestation formats (covered separately in binary-evidence corpus reports).

## Findings

### 1. Cargo and `crates.io` Packaging Mechanics and Limits

Basis: source + documentation + execution.

- **Hard `crates.io` publish limits (`rust-lang/crates.io` @ `18a7cf31`, `src/config/publish_limits.rs:3-41`):**
  - `upload_size = 10 * 1024 * 1024` (10 MiB compressed `.crate` tarball; per-crate database overrides exist on `crates.io`, `src/controllers/krate/publish.rs:275-278`).
  - `unpack_size = 512 * 1024 * 1024` (512 MiB decompressed).
  - `tarball_entries = 30_000` (`DEFAULT_TARBALL_ENTRIES`).
  - `metadata_file_size = 1024 * 1024` (1 MiB cap on `Cargo.toml` and `.cargo_vcs_info.json`).
  - `dependencies = 500`, `features = 300`.
- **Sparse/git index omits `[package.metadata.*]` (`crates/crates_io_index/src/data.rs:7-55`; `rust-lang/cargo` @ `930a674d`, `src/sources/registry/index/mod.rs:208-239, 696-744`):**
  - Registry index entries serialize only `name`, `vers`, `deps`, `cksum`, `features`, `features2`, `yanked`, `links`, `rust_version`, `pubtime`, and schema version `v`.
  - `[package.metadata.*]` is preserved verbatim inside the packaged `Cargo.toml` by `Manifest::to_normalized_contents` (`src/workspace/manifest.rs:569-595`), but cannot be queried from the sparse index without downloading and unpacking the `.crate` archive (or querying an external index).
- **`cargo package` normalization, `include`/`exclude` precedence, and MSRV feature syntax (`src/ops/cargo_package/mod.rs:109, 483-540, 887-939`, `vcs.rs:35-269`, `doc/book/src/reference/features.md:152, 222`):**
  - If a manifest sets **both** `package.include` and `package.exclude`, Cargo warns and **completely ignores `exclude`** (`cargo_package/mod.rs:483-488`).
  - Packaging preserves the original manifest as `Cargo.toml.orig`, writes normalized `Cargo.toml`, adds `.cargo_vcs_info.json` when inside a Git repository, and stamps generated files with fixed mtime `1153704088` (`mod.rs:932`).
  - Namespaced `dep:` and weak `pkg?/feat` syntax (`features2`, index schema `v = 2`) was stabilized in Rust `1.60.0`; crates maintaining a lower MSRV (such as `zerocopy` at `rust-version = "1.56.0"`) cannot use `dep:` or `pkg?/feat` in `[features]`.
- **Observed file-size budget on `google/zerocopy` (`a6864119`):**
  - `zerocopy/src/`: 20 files, `1,351,003` bytes (`1,319.3 KiB`).
  - `zerocopy/proofs/` (4 bootstrap proof units, currently excluded from `.crate` via `exclude = [".*", "/proofs"]` in `zerocopy/Cargo.toml`): 13 files, `46,543` bytes (`45.5 KiB` total; `Spec.lean` `2,175`–`4,848` B/unit, `Proof.lean` `2,491`–`12,713` B/unit, `request.json` `1,204`–`1,773` B/unit).
  - `anneal/theory/`: 59 files, `2,564,509` bytes (`2,504.4 KiB`); `anneal/trusted/lean/`: 21 files, `302,326` bytes (`295.2 KiB`); `anneal/correspondence/`: 16 files, `1,141,669` bytes (`1,114.9 KiB`).
  - Shipping declarative specifications in-crate stays well under `crates.io` limits; shipping compiled `.olean` artifacts or large proof/session archives at crate-wide scale risks hitting the 10 MiB upload cap and `30,000` entry limit.

### 2. Cargo Dependency-Graph and Vendoring Asymmetry for Companion Crates

Basis: source + execution (`support/cargo_lock_vendor_probe.py`).

Resolving and vendoring an upstream registry crate (`upstream-lib 0.1.0`) from a downstream crate (`downstream-app 0.1.0`) under `cargo 1.102.0-nightly (c07ac2c4d 2026-11-06)` against an offline local registry demonstrates three distinct Cargo behaviors (`src/ops/resolve.rs:469-517`, `src/ops/cargo_vendor.rs:153-182`):

| Upstream declaration in `upstream-lib/Cargo.toml` | Enters downstream `Cargo.lock`? | Enters downstream `cargo vendor`? | Compiled by downstream `rustc`? | Practical trade-off for companion spec/proof/theory crates |
| :--- | :---: | :---: | :---: | :--- |
| `[dev-dependencies]` (`dep-dev`) | No | No | No | Invisible to downstream offline/vendored consumers. |
| `[dependencies] dep-opt = { optional = true }` (disabled downstream) | **No** | **No** | No | Zero lockfile/vendor/compile cost for non-verifying consumers; enters `Cargo.lock` and `vendor/` only when a downstream feature enables it (or on `--all-features` / `docs.rs`). |
| Workspace member's *own* `optional = true` dep (disabled) | **Yes** | **Yes** | No | `ws.require_optional_deps()` (`resolve.rs:469`) locks all optional deps of workspace members. |
| `[target.'cfg(any())'.dependencies]` (`dep-cfgany`) | **Yes** | **Yes** | **No** | Guarantees lockstep version pinning (`=X.Y.Z`) and offline availability in every downstream `Cargo.lock` and `vendor/` without ever compiling `dep-cfgany`, at the cost of one extra locked/vendored crate per consumer. |

- **Theory carrier crate viability (execution):** A `#![no_std]` crate (`foo-spec-theory`, `edition = "2021"`, `rust-version = "1.56.0"`, empty `src/lib.rs`, `theory/Foo.lean`) packages cleanly with `cargo package` and lands offline in `vendor/foo-spec-theory/` with both the `.crate` SHA-256 (`Cargo.lock` and `.cargo-checksum.json` `"package"`) and per-file SHA-256 (`"theory/Foo.lean"` in `.cargo-checksum.json` `"files"`), requiring no `lake` or network access at verify time.

### 3. Circular Checksum Paradox, `cargo vendor` Integrity, and `crates.io` Trusted Publishing

Basis: source + execution + derived.

- **`.cargo-checksum.json` security boundary (`rust-lang/cargo` @ `930a674d`, `src/ops/cargo_vendor.rs:182, 343, 459-467`, `src/sources/directory.rs:69-260`, confirmed in live execution):**
  - `cargo vendor` emits `{"$comment": "This file only protects against accidental modifications. It is not a security mechanism and does not protect against malicious changes.", "files": {"<path>": "<sha256>"}, "package": "<tarball-sha256>|null"}`.
  - `"package"` is the `.crate` SHA-256 for registry crates and `null` for Git dependencies (`cargo_vendor.rs:459-467`).
  - `DirectorySource::verify` (`directory.rs:229-260`) checks *only* keys present in `cksum.files`; locally patched vendored crates with `"files": {}` and extra unindexed files in a vendored directory pass `DirectorySource::verify` without error.
- **Circularity constraint and canonical invariant digest (derived from Cargo packaging + `anneal-rustc-capture`):**
  - Because `Cargo.toml` is archived inside the `.crate` tarball, neither `[package.metadata.*]` nor an in-crate receipt can embed the `.crate` `package` SHA-256. Similarly, embedding an external proof/receipt archive URL+SHA-256 in `Cargo.toml` prior to `cargo publish` forbids the external archive from depending on `Cargo.toml`, `Cargo.toml.orig`, `.cargo_vcs_info.json`, or `.cargo-checksum.json`.
  - A canonical sorted manifest SHA-256 over `(logical_rel_path, sha256(bytes))` of the exact `rustc`-consumed Rust source files (`CaptureManifest.source_files[]`, `anneal/trusted/rustc-capture/src/ir.rs:1088-1092`) plus specification source files (`specification_manifest_sha256`) breaks the cycle and remains byte-identical across Git checkouts, unpacked `crates.io` tarballs, `cargo vendor` directories, and Bazel/GN/Nix extractions.
- **`crates.io` Trusted Publishing (RFC 3691 OIDC, `rust-lang/crates.io` @ `18a7cf31`):**
  - `EncodableVersion` (`crates/crates_io_api_types/src/lib.rs:366, 916-1039`) publicly exposes `checksum` (tarball SHA-256), `published_by`, `trustpub_only`, and `trustpub_data: Option<TrustpubData>`.
  - `TrustpubData` (`crates/crates_io_database/src/models/trustpub/data.rs:14-33`) records `{provider: "github", repository, run_id, sha}` or `{provider: "gitlab", project_path, job_id, sha}`.
  - `crates.io` does **not** serve downloadable Sigstore/SLSA DSSE cryptographic attestation bundles per version; `trustpub_data` is registry-asserted metadata extracted from the publish-time OIDC JWT.

### 4. Non-Monotonic Feature Unification, `build.rs` `cfg`s, and Slice-Identity Invariance

Basis: source + documentation + derived.

- **Real-world `cfg` surface (`google/zerocopy` @ `a6864119`, `zerocopy/Cargo.toml`, `zerocopy/build.rs:64-120`):**
  - `zerocopy` defines 6 public Cargo features (`alloc`, `derive`, `simd`, `simd-nightly`, `float-nightly`, `std`), 10 negative toolchain-version `cfg`s emitted by `build.rs` whenever `rustc < target_ver` (`no_zerocopy_allocator_api_1_100_0` through `no_zerocopy_panic_in_const_and_vec_try_reserve_1_57_0`: all 10 active on MSRV `1.56.0`, 0 on `1.100.0`, 1 on `nightly-2026-09-30`), 11 additional `rustc-check-cfg` names (`doc_cfg`, `kani`, `kani_slow`, `coverage_nightly`, `zerocopy_inline_always`, `zerocopy_unstable_ptr`, `zerocopy_unstable_linux`, `no_fp_fmt_parse`, and 3 internal CI/test `cfg`s), and compile-time `CARGO_PKG_VERSION`.
- **MIR non-monotonicity under Cargo feature unification (`rust-lang/cargo` `doc/book/src/reference/features.md:263-382` + `zerocopy/src/`):**
  - Cargo unifies features additively across the dependency graph (with `resolver = "2"`/`"3"` isolating host, dev, and target-specific edges).
  - Production crates still use negative feature gates: `zerocopy/src/` contains 8 live `not(feature = "derive")` directives (`zerocopy/src/lib.rs:741, 1723, 1960, 3762, 4374, 6021, 6661`; `zerocopy/src/split_at.rs:80`), alongside `build.rs`'s negative toolchain `cfg`s. Adding features (`cfgs_A ∪ cfgs_B`) can therefore delete or replace MIR bodies, so a receipt keyed solely by `(target, cfgs_A)` cannot soundly be reused under `(target, cfgs_A ∪ cfgs_B)`.
- **Distinction between current `capture_sha256` and a sound cross-machine / `2^F × T` slice key (`anneal/trusted/cargo-anneal/src/verify.rs:1516, 1547`, `anneal/trusted/rustc-capture/src/ir.rs:1065-1136`):**
  - Today, `cargo-anneal` computes `capture_sha256 = sha256_bytes(&capture_bytes)` over raw `capture.json` (`Manifest`), which embeds host `PathBuf`s (`compiler.sysroot`, `configuration.crate_root`, `source_files[].path`), raw `configuration.cfg`, and the crate-wide `census` (including unselected items).
  - Therefore, raw `capture_sha256` is **not** invariant across machines or irrelevant feature additions. Soundly collapsing the `2^F × T` matrix onto distinct verified MIR slices requires re-running Phase 1 capture under the consumer's actual unified flags and matching the digest of the **canonical path-free `Program` (`Captured.lean` / `manifest.program`)** paired with **`SemanticProfile` (`{target, opt_level, debug_assertions, overflow_checks, mir_preserve_ub, pointer_bits, endian}`)** — stripped of host paths, unselected `census`, and raw `cfg` lists. Any `cfg(not(...))`-induced change to a reachable MIR body or layout changes that digest and fails closed.

### 5. Bazel `crate_universe`, Fuchsia `cargo-gnaw`, and `exocrate` Constraints

Basis: source + documentation.

- **Bazel `rules_rust` `crate_universe` (`bazelbuild/rules_rust` @ `5d99ff2e`, `crate_universe/src/context/crate_context.rs:97-126`, `crate_universe/src/config.rs:271-410`, `crate_universe/extensions.bzl:427-1016, 1473-1678`):**
  - `CommonAttributes::compile_data_glob` defaults to `default_glob_all()` (`["**"]`). Every file inside a `.crate` tarball—including `specs/`, `proofs/`, or receipts—becomes a `compile_data` input to the generated production `rust_library` target unless excluded via `compile_data_glob_excludes`.
  - `crate.annotation(compile_data_glob_excludes = ..., data_glob = ..., additive_build_file_content = ...)` is strictly **consumer-side** (configured in the downstream Bazel `MODULE.bazel`/`WORKSPACE`). Upstream `Cargo.toml` cannot suppress `default_glob_all()`. For immutable `crates.io` tarballs, small in-crate specs only churn when the crate version itself bumps, whereas in-repo/Git/path dependencies or large proof/receipt trees bloat remote-execution input roots and invalidate downstream `rust_library` caches on unannotated workspaces.
- **Fuchsia `cargo-gnaw` (`fuchsia` @ `af754e2e`, `tools/cargo-gnaw/README.md:69, 97-131`, `src/lib.rs:89-265`):**
  - `cargo-gnaw` operates over vendored crates to generate `BUILD.gn` targets, intentionally does **not** run `build.rs` at compile time, and instead configures per-platform `features`, `remove_features`, `rustflags`, and `reviewed_features` in a centralized workspace `Cargo.toml` (`[gn.package.<name>."<ver>".platform."cfg(...)"]`). Negative-sense toolchain `cfg`s (such as `zerocopy`'s `no_zerocopy_*`) exist specifically so non-Cargo build systems invoking `rustc` directly work cleanly with zero extra `--cfg` flags on recent toolchains.
- **`exocrate` (`google/zerocopy` @ `a6864119`, `exocrate/src/lib.rs:200-245, 420-520`, `exocrate/src/sync.rs:101-194`):**
  - **Update over earlier corpus revisions (`41f5b37a`/`bd0956be`):** On `a6864119`, `exocrate 0.3.0` resolves the pre-SHA-verification staging vulnerability: `install()` streams `Source::Remote` bytes into an anonymous private `tempfile::tempfile_in(sync::staging_parent(dst))` and checks the SHA-256 digest *before* passing any bytes to `zstd` or `tar` (`lib.rs:422-439`), and `ManagedDirName::check_exists_or_create` extracts into a fresh per-attempt `0o700` `.staging-<prefix>.<rand>.staging` directory under an exclusive `fs2` lock before atomic `fs::rename` (`sync.rs:133-172`).
  - **Remaining limits for dependency-graph proof distribution:** `parse_remote_archive!` (`lib.rs:478-514`) parses a single local `Cargo.toml` at **compile time** via `toml_const!` keyed by `(std::env::consts::OS, ARCH)` for tool binaries, not dynamically across a Cargo dependency graph; `Source::Remote` calls `ureq::get(url)` with no built-in offline mirror fallback; `Source::Local` skips SHA-256 verification (`expected_sha = None`, `lib.rs:240-243`); and `exocrate` provides no built-in cache garbage collection (`lib.rs:138-141`).

### 6. Cross-Ecosystem Prior Art: Packaging, Composition, Diamonds, and Trust Binding

Basis: source + documentation.

#### 6.1 Rust Verifiers (`Verus`, `Creusot`, `Kani`/`verify-rust-std`, `Charon`/`Aeneas`)

- **Verus (`verus-lang/verus` @ `1ce6a59b`):**
  - Declares `[package.metadata.verus]` (`verify`, `is-vstd`, `is-core`, `is-builtin`, `no-vstd`, `trusted_crates`; `source/cargo-verus/src/metadata.rs:11-41`). `export_crate` (`source/rust_verify/src/import_export.rs:61-116`) prunes private functions and non-public-spec bodies (`functionx.body = None`) and serializes the remaining `Krate` + `CrateMetadata` via `bincode_next` to `.vir`.
  - **MSRV/dependency cost:** `source/vstd/Cargo.toml` pulls hard `[dependencies]` on `verus_builtin`, `verus_builtin_macros`, and `verus_state_machines_macros` (`0.0.0-YYYY-MM-DD-HHMM`), plus `[lints.rust] unexpected_cfgs` for `verus_keep_ghost`, `verus_verify_core`, `verus_keep_ghost_body`; non-Verus builds compile an erased `vstd` crate rather than eliminating the dependency.
  - **Diamonds & conflicting external specs:** `cargo-verus` disambiguates per-package env vars via `make_package_id(name, version, hash(manifest_path)[..12])` (`metadata.rs:275-285`), but `transitive_verified_import_names` (`metadata.rs:155-180`) passes bare target names (`--VIA-CARGO import-dep-if-present=<name>`) for transitive dependencies and `collect_vstd_metadata` (`L215-221`) relies on `0.0.0-*` semver compatibility so Cargo rejects multiple `vstd` instances. Duplicate `assume_specification` / `external_type_specification` / `external_trait_specification` fails closed (`source/vir/src/well_formed.rs:1937-1976`), and `--no-cheating` forbids `external_body`/`assume_specification` (`L1756-1761`). Individual trait/impl items cannot be marked `external` (`source/rust_verify/src/external.rs:28-32, 306-326, 437-445`).
- **Creusot (`creusot-rs/creusot` @ `faeb61f5`):**
  - Emits sibling `<crate>.cmeta` binary metadata adjacent to `.rmeta` (`creusot/src/metadata.rs:284-300`), indexed by `DefPathHash`.
  - **MSRV/dependency cost:** `creusot-std/Cargo.toml` uses `edition = "2024"`, `[target.'cfg(creusot)'.dependencies]`, `[lints.rust] unexpected_cfgs` (`cfg(creusot)`), and hard-depends on proc-macro `creusot-std-proc`.
  - **Diamonds, trait contracts, & duplicate `extern_spec!`:** Default `.cmeta` resolution uses `tcx.used_crate_source(cnum).paths().next().unwrap().with_extension("cmeta")` (`metadata.rs:297-299`), inheriting Cargo's `-Cmetadata=<hash>` disambiguator so semver-major diamonds survive (whereas CLI `--metadata-path` `overrides: HashMap<String, PathBuf>` at `L289` keys by bare crate name and collides). Trait contracts, purity (`#[check(ghost)]`, `#[check(terminates)]`), `#[logic(law)]`, `#[open_inv]`, and `#[trusted]` live on the trait and are validated against every local impl (`creusot/src/validate/traits.rs:53-176`). Loading two `.cmeta` dependencies with overlapping `extern_spec!` or `extern_type` triggers a hard `panic!` (`metadata.rs:100-110`).
- **Kani (`87c87010`) and `verify-rust-std` (`1feeadd9`):**
  - Kani emits sibling `.kani-metadata.json` (`kani_metadata/src/artifact.rs:34`) and supports `#[kani::requires]`/`#[kani::ensures]` + `#[kani::proof_for_contract]` + `#[kani::stub_verified]`.
  - `verify-rust-std` places `library/contracts/safety/` as a proc-macro dependency of `library/core/Cargo.toml` switched via `#[cfg(kani_host)]` (`kani.rs` vs `runtime.rs` erasure) plus `build.rs` `cargo:rustc-check-cfg=cfg(kani_host)`, alongside `core`'s `check-cfg` entries for `kani`, `flux`, `rapx` and `[package.metadata.flux]`.
- **Charon (`b23c297f`) and Aeneas (`2e3d4488`):**
  - Extracts whole crates to `.llbc`; external dependency items default to `<opaque>` (`charon/tests/cargo/dependencies.out`) unless explicitly extracted, shifting Lean packaging to generated `lakefile.lean` and `FunsExternal_Template.lean`.

#### 6.2 Cross-Language Verification Artifacts, Audit Registries, and External Overlays

| System | Shipped / Exported Artifact | Proof Body Omitted at Interface? | Version / Option Lock | Trust & Identity Binding |
| :--- | :--- | :---: | :--- | :--- |
| **Dafny `.doo`** (`427892ac`, `DooFile.cs:21-227`) | ZIP archive (`manifest.toml` + `program` text), loaded via `--library` | No (full source text; skips re-verification) | `Validate` (`L165-227`) rejects **any** `DafnyVersion` mismatch (`L172-176`) or incompatible option (`L218`) | Trusts pre-verified `.doo` if version + options match |
| **LiquidHaskell** (`7c809b68`, `SpecFinder.hs:60-140`) | Serialized `LiquidLib` (`libTarget` + flat `libDeps`) inside GHC `.hi` files; `<Mod>_LHAssumptions` fallback only when `.hi` has no spec (`L60-63`) | Yes (refinement types + measures) | Exact GHC `.hi` ABI + `SpecReference` fingerprint (`L123-139`, fails closed on mismatch or unbuilt dep) | Unit ID + saved spec fingerprint; whole-module selection (never field-merged) |
| **SPARK 2014 / Alire** (`1ce0965f`, `how_to_run_gnatprove.rst:130, 319-320, 360-377`; `65765597`) | Separate `.ads` spec vs `.adb` body; Why3 `why3session.xml` + `gnatprove --replay --steps` | Yes (callers verify against `.ads` without `.adb`) | Prover versions and step budgets (`--steps` for machine-independent replay) | Replay re-verifies saved VC discharges |
| **Frama-C WP** (`639a3647`, `ProofSession.ml:33`, `wp_parameters.ml:571-573, 1064-1073`) | ACSL contracts in C `.h` headers + `-wp-session` script dir + `-wp-cache` (`update`/`replay`/`none`) | Yes (`.h` contracts separate from `.c` bodies) | WP memory model (`-wp-model`) and prover versions | Session scripts and VC cache keyed by goal identity |
| **Rocq / Coq** (`21891774`, `man/coqc.1`) | `.vos` (interfaces + definitions, opaque proofs skipped) + `.vok` (async proof check certificates) | Yes (`-vos` omits `Qed` proofs) | Exact Rocq + OCaml version | `.vok` certifies deferred proof check |
| **`cargo-vet`** (`a9bde859`, `src/format.rs:233-470`, `book/src/importing-audits.md:19-21`) | Team `audits.toml` + non-transitive `imports.lock` + `delta` (`v1 -> v2`) audit collapse | N/A (human review criteria, e.g. `safe-to-deploy`, `ub-risk-N`) | Explicit non-transitive trust imports | Keyed by `(crate, semver[@git:hash])`, relying on `Cargo.lock` / registry `cksum` |
| **`cargo-crev`** (`e0e71f9d`, `package_info.rs`, `review/package.rs`, `proof/mod.rs`) | Cryptographically signed YAML proofs (`BEGIN CREV PROOF`) in Git proof repos | N/A (human/tool reviews + web-of-trust) | Explicit transitive trust depth | Binds signed proof to `PackageInfo.digest` (content digest of unpacked crate source) + `revision` + `version` |
| **TypeScript / DefinitelyTyped** (`de614c26`; `typescript-go` @ `89d5d5b2`, `resolver.go:620-695, 1140-1149, 1767, 2325`) | Bundled `.d.ts` via `package.json` `"exports"` `"types"` / `"types@>=X"` > `"typesVersions"` > `"types"` > external `@types/<pkg>` | Yes (erased JS runtime) | `"types@..."` / `"typesVersions"` selector; `@types` `Major.Minor.*` + npm `dist-tags` | In-package types take precedence over `@types` fallback; external `@types` suffers version skew and split maintenance |

#### 6.3 Cross-Cutting Architectural Implications (Derived)

Basis: derived from Sections 1–6.2.

1. **In-crate vs. companion vs. overlay split:** Shipping lightweight, proof-free specifications (either inert `#[cfg_attr(anneal, ...)]` or out-of-tree spec files) alongside or tightly coupled to the crate avoids TypeScript `@types` version skew while staying far under `crates.io`'s 10 MiB cap, whereas compiled `.olean`s, multi-megabyte proof trees, and toolchain-specific artifacts belong out-of-crate so non-verifying builds and unannotated Bazel `crate_universe` workspaces are not taxed.
2. **Semver-major diamond safety in Lean:** Unlike Creusot's `.cmeta` (which rides Cargo's `-Cmetadata` filename hash), bare Lean module roots such as `Zerocopy.Spec` collide whenever a dependency graph contains two semver-major versions (`0.7` and `0.8`). Lean crate-spec namespaces must be disambiguated by `PackageId`/`StableCrateId`.
3. **Orphan/external spec soundness:** Following Creusot (`metadata.rs:100-110`), Verus (`well_formed.rs:1937-1976`), and LiquidHaskell (`SpecFinder.hs:60-63, 123-125`), assumed external specifications for unverified third-party crates must never be silently merged across transitive dependencies (two dependencies assuming contradictory specs `P(u)` and `¬P(u)` derive `False`); they belong strictly in the top-level consumer's explicit TCB assumption ledger.

## Boundaries

- **`not examined` — Non-Linux `cargo vendor` symlink/permission edge cases, Cargo alternative registries (`--registry`), and Windows path-length limits on deeply nested `.lean` trees:** Live Cargo execution ran on Linux `x86_64` against an offline local registry.
- **`not examined` — Full `opam` constraint solver and Coq Platform overlay CI mechanics:** Prior corpus reports already examine AFP/Coq CI overlay maintenance; this report pins only Rocq `.vos`/`.vok` separation (`man/coqc.1`).
- **`not examined` — `cargo-verus` behavior under `resolver = "3"` MSRV-aware resolution (`Cargo >= 1.84`) with conflicting `vstd` patches:** Verified only `collect_vstd_metadata` source logic (`0.0.0-*` lock) and live `cargo 1.102.0-nightly` local-registry resolution of `upstream-lib`.
- **`known not to apply` — Assuming an upstream registry crate's disabled `optional = true` dependency bloats downstream `Cargo.lock` or `cargo vendor`:** Refuted by live execution (`support/cargo_lock_vendor_probe.py`, Case A vs. Case C); only *workspace-member* disabled optional dependencies or upstream `[target.'cfg(any())'.dependencies]` enter downstream `Cargo.lock` and `vendor/` when inactive.
- **`known not to apply` — Relying on `.cargo-checksum.json` as a cryptographic supply-chain authentication boundary:** Explicitly disclaimed by Cargo's own `$comment` field and `DirectorySource::verify` skipping extra files and empty `files: {}` maps.
- **`known not to apply` — Reusing Anneal's current raw `capture_sha256` across machines or under unified Cargo features:** At `google/zerocopy@a6864119`, `verify.rs:1547` hashes raw `capture.json` containing host paths, raw `cfg` strings, and unselected `census`.
- **`unsupported` — Upstream crate control over Bazel `rules_rust` `crate_universe` `compile_data_glob_excludes`:** `crate.annotation` is strictly consumer-side in `rules_rust@5d99ff2e`.
- **`unsupported` — Reading `[package.metadata.*]` from the `crates.io` sparse index without downloading `.crate` archives, or fetching Sigstore/SLSA DSSE bundles from `crates.io` Trusted Publishing:** Absent in `crates.io@18a7cf31`.
- **`unknown` — Future `crates.io` RFCs adding downloadable Sigstore provenance bundles or index-level custom metadata fields:** Not established by current `rust-lang/crates.io@18a7cf31` source.

## Evidence

All primary evidence was acquired on `2026-11-23`.

- **Cargo (`rust-lang/cargo` @ `930a674da900a73c1dfbe16be62c42e75bdfdfc0`):**
  - `src/ops/cargo_package/mod.rs:109, 483-540, 887-939` (`ORIGINAL_MANIFEST_FILE`, `include` overriding `exclude`, `prepare_for_publish`, fixed mtime `1153704088`).
  - `src/ops/cargo_package/vcs.rs:35-269` (`.cargo_vcs_info.json` dirty checks).
  - `src/workspace/manifest.rs:569-595` (`to_normalized_contents`, preserving `custom_metadata`).
  - `src/sources/registry/index/mod.rs:208-239, 696-744` (sparse index schema).
  - `src/ops/resolve.rs:469-517` (`ws.require_optional_deps()` workspace vs. upstream resolution).
  - `src/ops/cargo_vendor.rs:148-499` and `src/sources/directory.rs:69-260` (`.cargo-checksum.json` generation and `DirectorySource::verify`).
  - `doc/book/src/reference/features.md:152, 222, 263-382` (Rust `1.60` `dep:`/`?` stabilization and feature unification).
- **Live Cargo execution (`cargo 1.102.0-nightly (c07ac2c4d 2026-11-06)` on Linux `x86_64`):**
  - Preserved runnable script: `support/cargo_lock_vendor_probe.py`. Observed output: Case A `lock=['dep-cfgany', 'downstream-app', 'foo-spec-theory', 'upstream-lib']`, `vendor=['dep-cfgany', 'foo-spec-theory', 'upstream-lib']`; Case B `lock=['dep-cfgany', 'dep-opt', 'downstream-app-b', 'upstream-lib']`, `vendor=['dep-cfgany', 'dep-opt', 'upstream-lib']`; Case C `lock=['dep-opt', 'downstream-app-c']`, `vendor=['dep-opt']`; `foo-spec-theory/.cargo-checksum.json` includes `"theory/Foo.lean"` and `"Cargo.toml.orig"` under `"files"` and matches `"package"` tarball SHA-256.
- **`crates.io` (`rust-lang/crates.io` @ `18a7cf31c4818d1a54f240cacfa25d09ba6c0671`):**
  - `src/config/publish_limits.rs:3-41` (`upload_size`, `unpack_size`, `tarball_entries`, `metadata_file_size`, `dependencies`, `features`).
  - `crates/crates_io_index/src/data.rs:7-55` (`Crate` index struct).
  - `crates/crates_io_api_types/src/lib.rs:366, 916-1039` (`EncodableVersion`, `trustpub_only`, `trustpub_data`).
  - `crates/crates_io_database/src/models/trustpub/data.rs:14-33` (`TrustpubData::GitHub` / `TrustpubData::GitLab`).
- **`zerocopy`, `exocrate`, and Anneal (`google/zerocopy` @ `a68641199cdfa99f96cb62f0cde921c9d36bfb22`, tag `anneal-v0.2.0-alpha.8`):**
  - `zerocopy/Cargo.toml` (`rust-version = "1.56.0"`, `exclude = [".*", "/proofs"]`, `[target.'cfg(any())'.dependencies]`, `[package.metadata.build-rs]`).
  - `zerocopy/build.rs:64-120` (10 negative toolchain-version `cfg`s and 11 `rustc-check-cfg` predicates).
  - `zerocopy/src/lib.rs:741, 1723, 1960, 3762, 4374, 6021, 6661` and `zerocopy/src/split_at.rs:80` (8 `not(feature = "derive")` sites).
  - `zerocopy/proofs/` (4 units, 13 files, `46,543` B), `zerocopy/src/` (`1,351,003` B), `anneal/theory/` (`2,564,509` B).
  - `exocrate/src/lib.rs:138-141, 200-245, 420-520` and `exocrate/src/sync.rs:101-194` (pre-unpack SHA-256 verification via `tempfile_in`, fresh `0o700` `.staging-*` dir, compile-time `parse_remote_archive!`, unverified `Source::Local`).
  - `anneal/trusted/cargo-anneal/src/verify.rs:1516-1548` and `anneal/trusted/rustc-capture/src/ir.rs:1065-1136` (`capture_sha256` hashing raw `capture.json` `Manifest`).
- **Bazel `rules_rust` & Fuchsia `cargo-gnaw`:**
  - `bazelbuild/rules_rust` @ `5d99ff2e58d1a0c9387fc4945029df11144bc8a3`: `crate_universe/src/context/crate_context.rs:97-126`, `crate_universe/src/config.rs:271-410`, `crate_universe/extensions.bzl:427-1016, 1473-1678`.
  - `https://fuchsia.googlesource.com/fuchsia` @ `af754e2ee6b2ca26df3bd0fbef1429b591d199f3`: `tools/cargo-gnaw/README.md:69, 97-131`, `tools/cargo-gnaw/src/lib.rs:89-265`.
- **Verifier, registry, and overlay prior art:**
  - `verus-lang/verus` @ `1ce6a59bd72713cf486a7660097fe5ac57519617`: `source/cargo-verus/src/{metadata.rs:11-41, 155-221, 275-285; subcommands.rs:600-688}`, `source/vstd/Cargo.toml`, `source/rust_verify/src/{import_export.rs:61-116, external.rs:28-32, 306-326, 437-445, rust_to_vir_func.rs:3304}`, `source/vir/src/well_formed.rs:1756-1761, 1937-1976`.
  - `creusot-rs/creusot` @ `faeb61f5b5a8ffda94fde1f100ef96a1d798088b`: `creusot/src/metadata.rs:100-110, 284-300`, `creusot/src/validate/traits.rs:53-176`, `creusot-std/Cargo.toml`.
  - `model-checking/kani` @ `87c87010eda7797d7fa14033ca68bcbe17184a63`: `kani_metadata/src/artifact.rs:34`, `docs/src/reference/experimental/contracts.md`.
  - `model-checking/verify-rust-std` @ `1feeadd937956b8067ec2fb147ef55469361dab4`: `library/contracts/safety/{Cargo.toml,build.rs,src/{lib.rs,kani.rs}}`, `library/core/Cargo.toml`.
  - `AeneasVerif/charon` @ `b23c297f57c0b2072de7967c7f17088db0278a8c`: `charon/tests/cargo/dependencies*`; `AeneasVerif/aeneas` @ `2e3d4488280bb8a95411db81019a7854a784861f`.
  - `mozilla/cargo-vet` @ `a9bde85910409be3d2d61e6f6ff6ba7a521f0412`: `src/format.rs:233-470`, `book/src/{audit-criteria.md,importing-audits.md}`.
  - `crev-dev/cargo-crev` @ `e0e71f9dc2938c061ae0e99554caa8928d2299f1`: `crev-data/src/proof/{mod.rs,package_info.rs,review/package.rs}`.
  - `dafny-lang/dafny` @ `427892ac6f36204c6a1c760b328b74e0715a0efa`: `Source/DafnyCore/DooFile.cs:21-227`.
  - `ucsd-progsys/liquidhaskell` @ `7c809b687388dc837c53b9db29b0a70b7165b716`: `liquidhaskell-boot/src/Language/Haskell/Liquid/GHC/Plugin/SpecFinder.hs:60-140`.
  - `AdaCore/spark2014` @ `1ce0965fbb11e23ca3560b94d50875abd385b4ab`: `docs/ug/en/source/how_to_run_gnatprove.rst:130, 319-320, 360-377`; `alire-project/alire` @ `65765597471480f80b963cbc1c1ca3e691ff16fd`.
  - `Frama-C/Frama-C-snapshot` @ `639a3647736bf8ac127d00ebe4c4c259f75f9b87`: `src/plugins/wp/{ProofSession.ml:33-63, wp_parameters.ml:571-573, 1064-1073}`.
  - `rocq-prover/rocq` @ `21891774bf0131945f6cf454e56121d6a4fda02e`: `man/coqc.1`.
  - `DefinitelyTyped/DefinitelyTyped` @ `de614c26a55ac82a2b8c2344facf563179eb2d66`: `README.md:65-96`; `microsoft/typescript-go` @ `89d5d5b2849a0db0957065889ca58536fa6d2e4a`: `internal/module/resolver.go:620-695, 1140-1149, 1767, 2325`.

## Revalidation

1. **Re-run the live Cargo lockfile/vendoring and theory-carrier probe:**
   ```sh
   python3 support/cargo_lock_vendor_probe.py
   ```
   A passing run confirms that Cargo's lockfile and `cargo vendor` treatment of upstream `[dev-dependencies]`, inactive/active `optional = true` `[dependencies]`, `[target.'cfg(any())'.dependencies]`, and `#![no_std]` `.lean`-carrying crates still matches Sections 2 and 3 on the tested `cargo` binary.
2. **Check `crates.io` limits, index schema, and Trusted Publishing API changes:** Diff `src/config/publish_limits.rs`, `crates/crates_io_index/src/data.rs`, and `crates/crates_io_api_types/src/lib.rs` (`EncodableVersion`) in `rust-lang/crates.io` against `18a7cf31c4818d1a54f240cacfa25d09ba6c0671`.
3. **Check Bazel `crate_universe` default `compile_data_glob`:** Diff `crate_universe/src/context/crate_context.rs` (`default_glob_all`) and `crate_universe/src/config.rs` (`CrateAnnotations`) in `bazelbuild/rules_rust` against `5d99ff2e58d1a0c9387fc4945029df11144bc8a3`.
4. **Check Anneal `capture_sha256` and `exocrate` changes:** Diff `anneal/trusted/cargo-anneal/src/verify.rs` (`capture_sha256`), `anneal/trusted/rustc-capture/src/ir.rs` (`Manifest`), and `exocrate/src/{lib.rs,sync.rs}` in `google/zerocopy` against `a68641199cdfa99f96cb62f0cde921c9d36bfb22`.
