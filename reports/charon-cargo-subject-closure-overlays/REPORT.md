# Charon and Cargo Compilation-Subject Closure, Item Identity, and Materialized Overlay Controls

## Summary

Across eight offline component experiments under pinned Charon `0.1.210` and Rust/Cargo `nightly`, a Rust compilation and extraction subject is not uniquely identified by a primary `.rs` file path, a single-file content digest, a serialized LLBC `translated.crate_name`, or a zero process exit code:

1. **Input closure beyond the primary source file:** Holding the primary library or binary source file byte-identical while mutating `include_str!` payloads, `build.rs`-generated `include!` files, environment variables consumed via `env!` or `rerun-if-env-changed`, Cargo feature flags, `Cargo.toml` default features, path-dependency implementations, procedural-macro implementations, or doc comments inspected by derive macros (`DocWitness`) changes compiled program behavior or emitted Charon LLBC declarations. Conversely, mutating an external path dependency's function body leaves its signature `Opaque` and unchanged inside the primary crate's LLBC, requiring extraction cache keys to cover the resolved Cargo unit graph and input closure rather than primary-crate LLBC bytes alone.
2. **Compilation-unit collisions and multi-unit destination overwrites:** Requesting `charon cargo --dest-file <one.llbc> -- --test check` invokes `charon-driver rustc` for the library, the integration test, and the binary; across four identical cold runs all exiting `0`, the single destination file ended as the `check` test crate twice and the `subject_matrix_cli` binary crate twice. A workspace-wide `--workspace --lib` request exited `101` while compiling the dependent app crate but left a valid, parseable LLBC for the `shared_closure` path dependency at the requested destination. Furthermore, two sibling Cargo packages (`left_package` and `right_package`) declaring `[lib] name = "shared_unit"` both serialize `"translated_crate_name": "shared_unit"` and identical item paths (`shared_unit::marker`), colliding unless disambiguated by Cargo package ID or manifest path.
3. **Within-LLBC and cross-run item identity:** Identical `src/lib.rs` bytes (`2ff9c22c8e7256331b538113fc4a7f856313142dad50bf4ac053a0968dc20a28`) yield 10, 10, and 19 local LLBC functions under default library, `--features selected`, and `--tests` targets. Within one LLBC, short names (`duplicate`) and trait-default doc attributes (`Rule::defaulted` at `def_id` 6 and its impl method at `def_id` 8) are one-to-many, `macro_rules!` item spans point into the macro definition rather than the invocation site, and moving an unchanged function shifts its numeric `def_id` from `2` to `0`.
4. **Saved versus materialized overlay and warm-target hazards:** Equal-length private materialized overlays (`saved-00` versus `overl-NN`) preserve normalized Cargo `--unit-graph` structure, computed subject keys (`f1c8ac4ffd7e…`), and local declaration-body projections even though raw LLBC hashes differ due to embedded paths. However, copying a workspace to a different-length path (`shadow-copy-longer`) while reusing the origin workspace's warmed `CARGO_TARGET_DIR` mixes the new Rust function body with the origin's stale path-dependent `build.rs` constant (`205` instead of `217`) while still exiting `0` with `has_errors: false`.
5. **Non-atomic regular-file output and ABA ownership:** Interrupting regular-file LLBC emission with `RLIMIT_FSIZE=4096` kills `charon-driver` with signal `25` (exit `255`) and overwrites the active destination with a 4,096-byte unparsable prefix (`4390037b…`), whereas a failed compile (`pub fn broken(`) exits `101` leaving the prior successful LLBC byte-identical at the destination path. On the input side, content-hash-only checks accept stale writers after an `A → B → A` edit-and-revert cycle unless paired with a monotonic causal revision counter.

## Applicability

All observations in this report apply to the combined execution of:

- **Charon `0.1.210`** (`AeneasVerif/charon@0c91ca1a8e002d6bfa8d8f1f452804fce2f92cf1`, macOS `aarch64-apple-darwin` executable SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`);
- **Rust compiler `1.98.0-nightly` (`nightly`)** (`rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1`, executable SHA-256 `2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`);
- **Cargo `1.98.0-nightly` (`nightly`)** (`rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`, executable SHA-256 `71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`).

Only a single version of each tool is in scope; no cross-version delta is claimed here. Every Charon and Cargo invocation ran offline (`--offline --locked`, `CARGO_NET_OFFLINE=true`) on macOS 26.6.2 `arm64` (8 GiB RAM) with `CARGO_BUILD_JOBS=1`, `CARGO_INCREMENTAL=0`, and `RAYON_NUM_THREADS=1`, using `--preset aeneas` for Charon extractions unless otherwise noted. Each subprobe used isolated, disposable Cargo target directories and destination paths except in the explicit shared-target and prefilled-destination failure controls. These component experiments characterize the raw Cargo, `rustc`, and Charon boundaries; they do not execute an editor LSP server, an in-memory compiler virtual-file overlay, Aeneas Lean generation, or an orchestration daemon.

## Findings

### Build-Input Closure and Saved-Versus-Materialized Overlay Fidelity

Two complementary 10-request matrices (`support/charon-build-closure-control/` and `support/saved-vs-private-rust-overlay/`) exercised a three-package offline Cargo workspace (`app_closure` library and `app_closure_cli` binary, `dep_path` path dependency, and `proc_local` procedural macro) where the primary library combines a `build.rs`-generated `include!`, `include_str!`, `env!`, path-dependency calls, and proc-macro-generated code. In `support/charon-build-closure-control/`, Cargo's verbose log recorded four `rustc` driver units (`build_script_build` and `proc_local` compiled as host artifacts under `target/debug`; `dep_path` and `app_closure` compiled for `aarch64-apple-darwin` under `target/aarch64-apple-darwin/debug`), and all baseline LLBC outputs parsed with `has_errors: false`.

In `support/saved-vs-private-rust-overlay/`, the harness additionally captured `cargo build -Z unstable-options --unit-graph` before each extraction (`support/saved-vs-private-rust-overlay/graphs/`): the library selection has a five-unit graph (`app_closure` library, build-script compile and run units, `dep_path` library, and `proc_local` proc macro), and the binary selection adds a sixth unit. When `saved-00` and clean `overl-NN` copies use equal-length directory names (holding `CARGO_MANIFEST_DIR` string length constant), they share identical relative source manifests, normalized unit-graph hashes, computed subject keys (`f1c8ac4ffd7e…`), and declaration-body hash projections, while their whole-file LLBC SHA-256 digests differ (`40a41bade541…` versus `f061ff1c9aa3…`) because Charon embeds absolute source and destination paths.

| Controlled input change | Observed effect in `support/charon-build-closure-control/` and `support/saved-vs-private-rust-overlay/` |
| --- | --- |
| `BUILD_VALUE=7` → `8` | Build-script-generated `BUILD_SUBJECT` source text and its LLBC declaration body changed; `app_closure::root` body hash stayed unchanged because it references `BUILD_SUBJECT` by declaration ID. |
| `PROC_VALUE=3` → `4` | Proc-macro-generated `macro_generated` declaration body and literal changed. |
| `PROBE_ENV=A` → `AA` | `app_closure::root` declaration body changed through `env!`. |
| `include_str!` payload edit | `app_closure::root` declaration body changed. |
| Path dependency `wrapping_add(11)` → `wrapping_add(12)` | Source and subject-key hashes changed and Cargo/Charon recompiled the `dep_path` unit, but `dep_path::dep` remained `Opaque` inside `app_closure`'s LLBC; primary declaration body hashes did not change. |
| Proc-macro source `wrapping_add` → `wrapping_mul` | Primary LLBC function table changed from `core::num::wrapping_add` to include `core::num::wrapping_mul`; the serialized `macro_generated` body uses a function ID, shifting the projected function-ID graph in `support/saved-vs-private-rust-overlay/` while leaving the isolated body-only hash in `support/charon-build-closure-control/` unchanged. |
| `build.rs` expression edit | Generated `BUILD_SUBJECT` Rust text and declaration body changed. |
| Source root path length (`CARGO_MANIFEST_DIR`) | Extending the workspace path in `support/charon-build-closure-control/` changed generated text and the `BUILD_SUBJECT` declaration body through `CARGO_MANIFEST_DIR`. |

Presenting a changed `include_str!` payload record or the opaque `dep_path` mutation record under the saved subject key `f1c8ac4ffd7e…` caused the harness's subject-manifest gate in `support/saved-vs-private-rust-overlay/` to reject both with `stale or foreign subject manifest`. Presenting a successful `--bin app_closure_cli` extraction (`translated.crate_name = "app_closure_cli"`) to the library unit check failed with `wrong compilation unit` in both subprobes.

Basis: **execution** of `support/charon-build-closure-control/probe.py` and `support/saved-vs-private-rust-overlay/probe.py`; the requirement to key extraction caches on the full Cargo input closure is **derived**.

### Compiler-Observed Comments, Stdin Overlays, and ABA Ownership Revisions

In `support/rust-input-snapshot/`, a two-crate dependency-free fixture (`app` plus path-only proc-macro crate with `DocWitness` derive, `include_str!("proof_note.txt")`, and feature `selected`) demonstrated three additional input-closure and ownership boundaries while `app/src/main.rs` stayed at SHA-256 `50d20d8c…`:

- **Non-source Cargo inputs:** Baseline output printed `macro=1 included=alpha feature=0`. Mutating only `app/src/proof_note.txt` to `beta` printed `macro=1 included=beta feature=0`. Restoring that file and passing `--features selected` (or editing `app/Cargo.toml` from `default = []` to `default = ["selected"]`) printed `macro=1 included=alpha feature=10`. Perturbing the local package version in `Cargo.lock` made `cargo --locked` exit `101` (`cannot update the lock file ... because --locked was passed`).
- **Macro-visible doc comments:** Changing only a `///` doc comment from `proof: alpha` to `proof: beta` caused the `DocWitness` derive macro to emit `Marker::DOC_TAG = 2` instead of `1`, changing compiled program output from `macro=1` to `macro=2` before reverting to `A` restored `macro=1`. A proof-only edit classifier therefore cannot treat comment or attribute edits as compilation-inert unless procedural macros and build scripts are proven unable to inspect them.
- **Direct `rustc` stdin overlay and `A → B → A` compare-and-swap ownership:** Compiling `host.rs` (`disk-A`) from disk while passing unsaved source (`buffer-B`) to `rustc` on standard input succeeded for both while `host.rs` remained unchanged on disk. In a file-backed `{revision, content}` compare-and-swap harness using `flock` and `os.replace`, editor transitions `rev 1 (A) → rev 2 (B) → rev 3 (A)` restored the original content hash of `A`; a stale agent holding expected `rev 1 (A)` and attempting to write `C` at `rev 3` would be accepted by a content-hash-only check (`ABA_hash_only_would_accept: true`) but was rejected by the paired `(revision, content_hash)` guard.

Basis: **execution** in `support/rust-input-snapshot/raw-results.json`.

### Root-Selection Scaling versus Cargo Build Closure

In `support/charon-scaling-subject-closure/`, a two-member offline Cargo workspace (`app_closure` depending on `shared_closure`) was generated at 24-root (`support/charon-scaling-subject-closure/fixture-24-lib.rs`) and 192-root (`support/charon-scaling-subject-closure/fixture-192-lib.rs`, SHA-256 `0f62c857c9ae3cfd14d12bb25616ecbb6a18230762cc27b0ec527efeae153d8a`) scales. Each `root_N` calls `node_N`, which calls `leaf_N` and `shared_closure::dep`, and reads `BUILD_VALUE` generated by `build.rs` (SHA-256 `d1fac8596ecbbe3295cfab055478731ced6384bfc765572306fde5d5d2efebd6`).

| Case | Local functions in LLBC | Wall time | Maximum sampled process-tree RSS sum | LLBC size |
| --- | ---: | ---: | ---: | ---: |
| 24 roots, one selected (`crate::root_000`) | 4 | 0.547 s | 185 MiB | 25 KB |
| 24 roots, eight selected | 25 | — | — | — |
| 24 roots, whole library | 75 | 0.505 s | 193 MiB | 318 KB |
| 192 roots, one selected (`crate::root_000`) | 4 | 0.535 s | 193 MiB | 61 KB |
| 192 roots, 32 selected | 97 | 0.538 s | 185 MiB | 448 KB |
| 192 roots, whole library | 579 | 0.580 s | 190 MiB | 2.47 MB |

- **Narrower local root chasing than Cargo compilation:** Cargo's unit graph (`support/charon-scaling-subject-closure/unit-graphs.json`, SHA-256 `ad57412dd7cf2bf9e51e7bbc4f1f1850bc0474fc1e6713da3e268fa6c7e248bf`) always built four units (app library, build-script compile, build-script run, and `shared_closure` library), yet `shared_closure::dep` remained an `Opaque` foreign signature in `app_closure` unless `shared_closure --lib` was extracted as its own primary subject. Each successful run left ~1.13 MB in its temporary Cargo target directory (+28 bytes with `--features selected`).
- **Fixed-source variations:** Holding `app/src/lib.rs` fixed at `0f62c857…`, enabling `--features selected` kept 579 local functions but swapped `default_only` for `selected`; changing `BUILD_VALUE` from `7` to `9` changed the serialized `BUILD_VALUE` constant body; changing `app/src/payload.txt` from `payload-A` to `payload-BBBBB` changed the `payload_len` body.
- **Misleading LLBC left by failed `--workspace --lib`:** Invoking `charon cargo --dest-file n192-workspace-libs.llbc -- --workspace --lib --offline --locked` (a two-root unit graph) exited `101` with `extern location for shared_closure does not exist` while compiling `app_closure`, but left a valid, parseable LLBC at `n192-workspace-libs.llbc` containing `crate_name: "shared_closure"`.

Basis: **execution** in `support/charon-scaling-subject-closure/raw-results.json` (SHA-256 `241fce12441015b490cc3e4c5c5bf9430fdc87b7767447ef938cda92b1041585`).

### Compilation-Unit Identity, Multi-Unit Destination Races, and Regular-File Interruption

In `support/charon-subject-output-phase-matrix/`, 17 bounded requests exercised `subject_matrix` (base `src/lib.rs` SHA-256 `b4013f29aab99417d099eba3acc9bb803e600b2e1038c040b89d23a16614d0e7`, independent `subject_matrix_cli` binary, and `check` integration test):

| Request | Actual `charon-driver` units in verbose log | Final destination outcome |
| --- | --- | --- |
| `--lib` | `subject_matrix` | Parseable library LLBC (14,708 bytes). |
| `--bin subject_matrix_cli` | `subject_matrix`, then `subject_matrix_cli` | Parseable binary LLBC (54,391 bytes). |
| Four `--test check` requests | `subject_matrix`, `check`, and `subject_matrix_cli` in varying order | Two parseable `check` LLBCs and two parseable `subject_matrix_cli` LLBCs; all four exited `0`. |
| `--lib --features selected` | `subject_matrix` (selected) | `feature_only` present; `default_only` absent. |
| `--lib --target aarch64-apple-darwin` | `subject_matrix` (host-target) | Parseable library LLBC matching base local names and body-hash projection. |
| `--lib` with `RUSTFLAGS=-C opt-level=1` | `subject_matrix` | Parseable library LLBC matching base local names and body-hash projection. |
| `--lib` comment prefix, declaration reorder, and restored A | one `subject_matrix` driver per request | Spans/declaration order shifted under edits; restored A recovered baseline local names and body-hash projection despite differing raw LLBC SHA-256. |
| Two simultaneous private `--lib` requests (default and `selected`) | one `subject_matrix` driver per process (~0.18 s each) | Separate parseable outputs with their respective feature functions. |
| `--lib --target x86_64-apple-darwin` | attempted library | Exit `101` (`rustc` `E0463`, missing `x86_64` `std`), no destination written. |
| Regular-file write under `RLIMIT_FSIZE=4096` | `subject_matrix` interrupted by signal `25` | Exit `255`; prior valid destination (`c4060a3b6d1221566c26acc9610d4f76e8011bd5c2deb5c831c2e60a0df18e24`) overwritten by 4,096-byte unparsable partial file (`4390037b0612ebba6ea815a004418de02c8a60d4e14cb0952ff47750203315aa`). Separate `last-good.llbc` survived and uncapped retry succeeded. |

In addition, the harvested sibling-package probe (`support/sibling-package-shared-lib-collision/probe.py`, `support/sibling-package-shared-lib-collision/results.json`) compiled two distinct Cargo packages (`left_package` and `right_package`) in the same workspace that both declare `[lib] name = "shared_unit"` and `pub fn marker() -> u32` (returning `11` in `left_package` and `29` in `right_package`). Both extractions emitted `"translated_crate_name": "shared_unit"` and identical serialized function names (`shared_unit::marker`) with distinct LLBC digests (`support/sibling-package-shared-lib-collision/artifacts/left.llbc` versus `support/sibling-package-shared-lib-collision/artifacts/right.llbc`). Consequently, compilation-unit keys must include the Cargo package ID / manifest path, target kind, target name, target triple, profile, and feature set rather than `(crate_name, item_path)` alone.

Basis: **execution** in `support/charon-subject-output-phase-matrix/raw-results.json` (SHA-256 `153519e76c32aae9ebaf735eac748519deaec9023db9566f8d5e6d372fd9b56a`) and `support/sibling-package-shared-lib-collision/results.json`.

### Item Identity, Ambiguity, and Structural Moves Within and Across LLBC Extractions

In `support/charon-subject-identity/`, six extractions over `support/charon-subject-identity/fixture/src/lib.rs` (base version A SHA-256 `2ff9c22c8e7256331b538113fc4a7f856313142dad50bf4ac053a0968dc20a28`) established four constraints on compiler-backed annotation attachment (`support/charon-subject-identity/mapping-manifest.json`):

1. **Subject-dependent item presence:** From identical version A source bytes, the default library had 10 local functions (including `default_only`, lacking `selected_only` and `tests::test_subject`), `--features selected` had 10 local functions (reversing `default_only` and `selected_only` and attaching `#[cfg_attr(feature = "selected", doc = "proof-id: conditional")]`), and `--tests` had 19 local functions (adding `tests::test_subject` and test-harness functions).
2. **Short-name and trait-default multiplicity inside one LLBC:** The default library LLBC contained two local functions named `duplicate` distinguished only by full structured path and in-crate ID (`subject_identity_probe::left::duplicate` at `def_id` 4 and `subject_identity_probe::right::duplicate` at `def_id` 5). A single authored `/// proof-id: trait-default` comment on trait method `Rule::defaulted` (`def_id` 6, line 22) was duplicated onto the impl-associated method `defaulted` (`def_id` 8, span on the impl block at lines 27–30).
3. **Macro-generated item span provenance:** `macro_rules! emit_generated` (invoked at line 38) emitted local function `generated` (`def_id` 1) carrying `proof-id: macro-generated`, but its serialized item span pointed into the macro definition (file ID 0, line 35, columns 8–40) with `source_text: null` and `generated_from_span: null`.
4. **Non-persistent numeric `def_id` across structural edits (`A → B → C → A`):** In version A, `movable` at line 41 had `def_id` 2 (`default_only` was 0, `generated` was 1). Moving the unchanged `movable` block to line 4 in version B reassigned `movable` to `def_id` 0 and shifted `default_only` to 1 and `generated` to 2. Adding a duplicate `copy::movable` with the same `proof-id: movable` comment in version C matched two local items (`def_id` 0 and `def_id` 10). Restoring version A returned `movable` to line 41 and `def_id` 2.

Basis: **execution** in `support/charon-subject-identity/raw-results.json` and `support/charon-subject-identity/mapping-manifest.json`.

### Warm-Target Regeneration versus Stale Path-Sensitive Shared-Target Products

In `support/charon-warm-target-controls/`, 11 Charon requests and two plain `cargo build -v` warmups ran against `warm_probe` (which computes `pub const SNAPSHOT_VALUE: u32 = BUILD_VALUE + len(CARGO_MANIFEST_DIR)` in `build.rs`):

| Case | Wall time | LLBC destination outcome | Target directory state |
| --- | ---: | --- | --- |
| Origin A, cold shared target | 0.518 s | New parseable `warm_probe` LLBC | 1,193,497 bytes after build. |
| Origin A, same warm target, invalid sentinel prewritten | 0.077 s | Sentinel overwritten by parseable LLBC | 1,193,497 bytes. |
| Origin A, same warm target, destination absent | 0.077 s | New parseable LLBC created | 1,193,497 bytes. |
| Origin A, separate cold target | 0.502 s | New parseable LLBC created | 1,193,539 bytes. |
| Origin A, separate target then warm sentinel | 0.077 s | Sentinel overwritten by parseable LLBC | 1,193,539 bytes. |
| Origin A, target prewarmed by two `cargo build -v` calls (0.414 s, then 0.017 s logging `Fresh warm_probe`) | 0.509 s | Charon still compiled `warm_probe` and created LLBC | 2,236,319 bytes after Charon. |

When candidate B was materialized into a longer path (`support/charon-warm-target-controls/fixture/shadow-copy-longer/`) with a **private** target directory, `build.rs` emitted `SNAPSHOT_VALUE = 217`, whereas building identical B source bytes at the shorter origin path (`support/charon-warm-target-controls/fixture/origin/`) emitted `205`. When `shadow-copy-longer` B was extracted against the origin workspace's **warmed shared target**, Charon exited `0` (`has_errors: false`) and translated B's updated `step` function body, but reused the origin's cached `generated.rs` (`SNAPSHOT_VALUE = 205`), producing a hybrid compilation subject that matched neither clean private shadow B (`217`) nor origin A. Finally, writing malformed `pub fn broken(` to origin and running Charon against the warm target exited `101` while leaving the prefilled prior A LLBC (`support/charon-warm-target-controls/artifacts/failed-old.llbc`) byte-identical.

Basis: **execution** in `support/charon-warm-target-controls/results.json` (SHA-256 `cbab1f2a121f0596e05cb071b07c6e6c5e4d3adcebae7478be6b29bf73da53a6`).

## Boundaries

- **Not examined:** Live editor open/change/save/close buffer lifecycles, LSP/MCP transport protocols, in-memory `rustc` virtual file loaders inside Cargo/Charon, or Aeneas/Lean proof checking. The `rustc` standard-input control in `support/rust-input-snapshot/` and the file-copied workspaces in `support/saved-vs-private-rust-overlay/` do not exercise an in-memory compiler overlay API.
- **Not examined:** Same-process `charon_lib` or compiler-driver state reset across sequential or concurrent requests; every extraction launched a fresh OS process.
- **Unknown:** Whether other Cargo wrapper modes, target triples with installed cross-standard libraries, or future Charon revisions can cause a warm Cargo invocation to exit `0` while skipping the `charon-driver` invocation for the requested unit.
- **Known not to apply:** Treating `(translated.crate_name, item_path)` or numeric `def_id` as a globally unique or cross-edit persistent identifier is falsified by `support/sibling-package-shared-lib-collision/` and `support/charon-subject-identity/`. Treating an exit code of `0` or an existing parseable `.llbc` file as proof that the requested unit succeeded is falsified by the `--test check` alternation, the `--workspace --lib` partial failure, and the `pub fn broken(` stale-destination control.
- **Unsupported:** `--workspace --lib` extraction across dependent workspace crates failed with exit `101` (`extern location for shared_closure does not exist`) under this Charon `0.1.210` invocation mode, and cross-compilation to `x86_64-apple-darwin` failed with `E0463` because the target `std` library was not installed on the host.

## Evidence

- **Build-closure and overlay subprobes:**
  - `support/charon-build-closure-control/probe.py`, `support/charon-build-closure-control/verify.py`, `support/charon-build-closure-control/raw-results.json`, `support/charon-build-closure-control/fixture/`, and `support/charon-build-closure-control/artifacts/`.
  - `support/saved-vs-private-rust-overlay/probe.py`, `support/saved-vs-private-rust-overlay/verify.py`, `support/saved-vs-private-rust-overlay/results.json`, `support/saved-vs-private-rust-overlay/fixture/`, `support/saved-vs-private-rust-overlay/graphs/`, and `support/saved-vs-private-rust-overlay/artifacts/`.
  - `support/rust-input-snapshot/probe.py` (SHA-256 `4101c4def098de100aaa87b2cb8002d7f22ff7872717f50950a8fa6cee37b079`), `support/rust-input-snapshot/raw-results.json`, `support/rust-input-snapshot/fixture/` (canonical file-hash map SHA-256 `2e78b1712c66a02a2167b2102e16c4dfe0b60ecb75e1b89d1bae320640b2561f`), `support/rust-input-snapshot/command.stdout`, and `support/rust-input-snapshot/host.txt`.
- **Scaling and unit-graph subprobe:**
  - `support/charon-scaling-subject-closure/probe.py` (SHA-256 `3a97c7f96332b63c1ab021769afec44e83f3de50e9c2fb8e38eeac79174c8d84`), `support/charon-scaling-subject-closure/raw-results.json` (SHA-256 `241fce12441015b490cc3e4c5c5bf9430fdc87b7767447ef938cda92b1041585`), `support/charon-scaling-subject-closure/unit-graphs.json` (SHA-256 `ad57412dd7cf2bf9e51e7bbc4f1f1850bc0474fc1e6713da3e268fa6c7e248bf`), `support/charon-scaling-subject-closure/fixture/`, `support/charon-scaling-subject-closure/fixture-24-lib.rs`, `support/charon-scaling-subject-closure/fixture-192-lib.rs`, and `support/charon-scaling-subject-closure/artifacts/`.
- **Subject identity and sibling-package collision subprobes:**
  - `support/charon-subject-identity/probe.py` (SHA-256 `4561c1da3a588c91d35c1c534a101170e43a9a5a3c9a4bab78c456e5f7f16814`), `support/charon-subject-identity/raw-results.json`, `support/charon-subject-identity/mapping-manifest.json`, `support/charon-subject-identity/tool-versions.txt` (SHA-256 `28822e0797f54b39411537a2b206434dbabfab9d335db51e67f22f7bd69986fe`), `support/charon-subject-identity/fixture/`, `support/charon-subject-identity/versions/`, and `support/charon-subject-identity/artifacts/`.
  - `support/sibling-package-shared-lib-collision/probe.py`, `support/sibling-package-shared-lib-collision/results.json`, `support/sibling-package-shared-lib-collision/inputs/`, `support/sibling-package-shared-lib-collision/artifacts/left.llbc`, and `support/sibling-package-shared-lib-collision/artifacts/right.llbc`.
- **Output-phase and warm-target subprobes:**
  - `support/charon-subject-output-phase-matrix/probe.py` (SHA-256 `71f10e3745448d1da23af25c985688bdff7c7aff71f325b87e127b5ecda1e8fa`), `support/charon-subject-output-phase-matrix/raw-results.json` (SHA-256 `153519e76c32aae9ebaf735eac748519deaec9023db9566f8d5e6d372fd9b56a`), `support/charon-subject-output-phase-matrix/manifests/`, `support/charon-subject-output-phase-matrix/fixture/`, `support/charon-subject-output-phase-matrix/artifacts/quota-partial.llbc`, and `support/charon-subject-output-phase-matrix/artifacts/last-good.llbc`.
  - `support/charon-warm-target-controls/probe.py` (SHA-256 `c9bc12936bf3dd34741f615eee0670457c5d22e156c750bfb6bc0c5bcdade665`), `support/charon-warm-target-controls/results.json` (SHA-256 `cbab1f2a121f0596e05cb071b07c6e6c5e4d3adcebae7478be6b29bf73da53a6`), `support/charon-warm-target-controls/fixture/`, `support/charon-warm-target-controls/versions/`, `support/charon-warm-target-controls/artifacts/cases/`, and `support/charon-warm-target-controls/artifacts/failed-old.llbc`.

## Revalidation

To verify the retained artifacts offline without invoking Charon or Cargo, run:

```sh
python3 support/charon-build-closure-control/verify.py
python3 support/saved-vs-private-rust-overlay/verify.py
```

To re-execute the probes on a host with the pinned Charon and nightly Rust toolchain installed and at least 15–20 GiB of free disk space, run each subprobe script in a disposable copy of the package (passing `--work <new-absent-scratch-dir>` to `support/charon-build-closure-control/probe.py`, `support/charon-subject-output-phase-matrix/probe.py`, and `support/saved-vs-private-rust-overlay/probe.py`, or running `support/charon-scaling-subject-closure/probe.py`, `support/charon-subject-identity/probe.py`, `support/charon-warm-target-controls/probe.py`, `support/rust-input-snapshot/probe.py`, and `support/sibling-package-shared-lib-collision/probe.py`). Compare declaration-body hash projections, normalized unit graphs, missing/ambiguous locator counts, and failure-control classifications rather than raw whole-file LLBC hashes, which embed execution-time paths.
