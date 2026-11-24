# Verification Receipt Inspection, Anti-Spoofing, and Semantic Diff Architecture (`cargo anneal inspect`)

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

Raw multi-hundred-line Receipt Schema v3 JSON documents emitted by `cargo anneal verify` pose three hazards when read directly by humans or ad-hoc CI scripts: (1) untrusted strings (`crate_name`, Rust `DefPath`, `sorry_declarations`, multi-line `detail`) enable 7-bit/8-bit ANSI/OSC terminal escape injection, Trojan Source bidirectional reordering, column-0 log spoofing, `cmark-gfm` table/fence escapes, and `serde_json::Value` duplicate-key smuggling; (2) partial (`selected_unit`), tainted (`sorry_in_proof`, `unpinned_lean`, `unsandboxed_elaboration`), unattested (`external_unverified_by_binary`), or failed receipts can be misread as verified; and (3) raw diffs bury `Spec.lean` or trust regressions under benign `Proof.lean` digest churn.

`cargo anneal inspect` (`trusted/cargo-anneal/src/{output.rs, inspect/*.rs}`) provides a compiler- and prover-free inspection, offline artifact re-verification, deterministic golden ledger, and 3-tier semantic diff subcommand with **zero new Cargo dependencies** (`#![forbid(unsafe_code)]`, leaving `Cargo.lock` and `trusted/root-manifest.sha256` unchanged):
1. **Strict Duplicate-Key-Rejecting Parsing (`StrictJsonDom` + `ObjectCursor`):** Rejects duplicate keys at **every** object depth (`exit 2`), caps size (`64 MiB`) and nesting (`128`), tracks unrecognized RFC 6901 JSON pointers (`--unknown-fields={warn,deny}`), and enforces `14` cross-field `validate_envelope_invariants` equations (`exit 2` on contradictions).
2. **Type-Enforced Sanitization (`SanitizedInline`, `SanitizedBlock` in shared `output.rs`):** Neutralizes ASCII C0 (`0x00..=0x1F`), DEL (`0x7F`), UTF-8 C1 (`U+0080..=U+009F`), Unicode Bidi/Tags/`Default_Ignorable` codepoints, column-0 newline forging (mandatory `"  | "` gutter), and `cmark-gfm` table/fence/mention escapes (`\|` + dynamic `N+1`-backtick wrapping).
3. **Six-Axis `AssuranceProfile` Lattice & Semantic Diff:** Projects an unforgeable top-line headline across `(verdict × provenance × scope × containment × kernel_replay × axioms)`, re-hashes disk artifacts safely via `O_RDONLY | O_NOFOLLOW | O_NONBLOCK` + `fstat` `S_ISREG` (`--verify-artifacts <dir>`), compares deterministic `--format ledger` text (`--compare-ledger`), and partitions `--diff <base> <head>` into **Tier A (Trust Regression)**, **Tier B (Spec/Subject Delta)**, and **Tier C (Benign Proof-Only Churn)**.

## Applicability

Findings apply to `trusted/cargo-anneal/` in `google/zerocopy` at commit `d3362d9a65` (with in-flight `#4147` `NdjsonAuditVerdict` and `#4152` `FailureReceipt.hint`), isolated `serde 1.0.229` / `serde_json 1.0.154` (Rust `edition = "2024"`) duplicate-key probes, and primary-source/execution audits preserved at `google/zerocopy:reference@425401baa150b7a009b2a46780c3e9b4cf31555f`. Because the inspected baseline recorded short hash `d3362d9a65` without a full 40-hex SHA, `REPORT.json` records `d3362d9a65`. `cargo anneal inspect` compiles with and without the `setup` Cargo feature (`--no-default-features`) and never invokes `rustc`, `lean`, external kernels, or network I/O.

## Findings

### 1. Five-Stage Pipeline, CLI Contract, and Exit Codes (`0` / `1` / `2`)

Basis: source + derived (`d3362d9a65`, `main.rs:174-189`, `verify.rs:2125-2127`).

- **Shared `output.rs` (`~280` LOC, co-owned with `cli-tty-arch`):** Provides `ColorChoice { Auto, Always, Never }` (`--color` > non-empty `NO_COLOR` > `TERM=dumb` > `CLICOLOR_FORCE`/`FORCE_COLOR` > `std::io::IsTerminal`), `SafeWriter` (catches `BrokenPipe` cleanly while preserving pre-computed non-zero exit codes), `SanitizedInline`/`SanitizedBlock`, and `AssuranceBadge`.
- **Sequential Pipeline (`inspect/{mod,strict_json,schema,artifacts,lattice,render}.rs`, `~1,380` total LOC):**
  1. *Ingest (`strict_json.rs`):* Reads regular file or stdin `-` (`<= 64 MiB`), validates UTF-8, parses `StrictJsonDom` (`remaining_depth <= 128`, no duplicate keys, zero trailing tokens), gates `schema_version == 3` (`< 3` or `> 3` fail with `exit 2`), and records unconsumed keys in `unrecognized_fields: BTreeSet<SanitizedInline>`.
  2. *Cross-check (`schema.rs`):* Enforces all `14` envelope invariants (`CORRUPT_RECEIPT_ENVELOPE` → `exit 2`).
  3. *Offline artifacts (`artifacts.rs`):* On `--verify-artifacts <dir>`, checks `symlink_metadata(!is_symlink && is_dir)`, validates `Component::Normal` paths, opens with `O_RDONLY | O_NOFOLLOW | O_NONBLOCK`, verifies `fstat` `S_ISREG` and `st_size <= 256 MiB`, streams SHA-256 over the FD (`request.json`, `capture/capture.json`, `Captured.lean`, `rust/*`, `authored/*.lean`, `anneal/*`, `Expected.lean`, `lean-lib/*`), and classifies directory walk (`follow_links(false)`, zero symlinks allowed) as `ManifestExact` or `SubsetWithExtraFiles`.
  4. *Lattice & Gates (`lattice.rs`):* Computes `AssuranceProfile` (or 3-tier `ReceiptDiff` for `--diff <base> <head>`) and evaluates `--passive`, `--check`, `--require-untainted`, `--require-crate-scope`, `--require-containment`, `--require-kernel-replay`, `--allowed-axioms`, `--require-exact-artifacts`, `--no-regressions`, `--require-unchanged-specs`, and `--compare-ledger`.
  5. *Render (`render.rs`):* Emits `--format {human,ledger,markdown,json}` to `stdout` (`--output <path>` optional atomic write; diagnostics to `stderr`).
- **Exit Codes:** `0` = valid receipt + all active policy gates passed; `1` = structurally valid receipt failed a policy/integrity gate (`FailureReceipt`, `tainted_*`/`unrecognized_fields` under gate mode, `--verify-artifacts` mismatch, `--compare-ledger` drift, `--diff` Tier A/B regression); `2` = CLI error, I/O error, `> 64 MiB` / `> 128` depth, duplicate JSON key, `schema_version != 3`, `--unknown-fields=deny`, or `CorruptEnvelope`.

### 2. Duplicate-Key Defense and 14 Envelope Cross-Consistency Equations

Basis: source + execution (`serde 1.0.229` + `serde_json 1.0.154` live probe).

Live execution confirmed that `serde_json::Value` (`Map::insert`) and `#[derive(Deserialize)]` with `#[serde(flatten)] extra: BTreeMap<String, Value>` both silently last-wins overwrite duplicate keys (including duplicate unknown keys and nested `audit.axioms` duplicates). `StrictJsonDom`'s `visit_map` checks `Map::contains_key` at every nesting level and aborts (`exit 2`, line/column) on collision.

`validate_envelope_invariants` enforces 14 cross-field checks before rendering:
1. Disjoint `status` sets (`{"crate_verified", "selected_unit_verified", "tainted_crate_verified", "tainted_selected_unit_verified"}` forbidding `phase`/`detail` vs. `{"unsupported", "proof_failed", "compiler_failed", "tool_failed"}` forbidding `audit`).
2. `status.starts_with("tainted_") <==> !taint_reasons.is_empty()`.
3. Sorted unique `taint_reasons` in `{"sorry_in_proof", "unpinned_lean", "unsandboxed_elaboration"}` (or explicit unknown taint under `--unknown-fields=warn`).
4. Scope biconditionals (`scope.kind == "crate"` vs. `"selected_unit"` with non-empty `scope.roots`).
5. Canonical root binding (`Trusted.MirSemantics.CrateTheorem` vs. `UnitTheorem`).
6. `elaboration_sandbox == "none" <==> "unsandboxed_elaboration" ∈ taint_reasons`.
7. 4-way `sorry` consistency (`"sorry_in_proof" ∈ taint_reasons <==> sorry_declarations.is_some()`, `sorry_declarations == Some(audit.sorry_declarations)`, `!audit.sorry_declarations.is_empty() <==> "sorryAx" ∈ audit.axioms`).
8. Closed axiom ceiling `{"Classical.choice", "Quot.sound", "propext"}` (+ `"sorryAx"` iff tainted).
9. 4-way `unpinned_lean` consistency (`correspondence_provenance.applicable == false`, `toolchain_identity.sha256_locked` empty).
10. `audit.replay == true`, `audit.exact_type == true`, `replayed_declarations > 0`, non-empty `subject`/`model`/`specification` closures.
11. Top-level ↔ `audit.bindings` SHA-256 equality (`request`, `capture`, `model_manifest`, `specification_manifest`).
12. Strict `[0-9a-f]{64}` format on every `*_sha256` / `sha256` field.
13. `selected` ↔ `census` consistency (`selected == true && has_body == true`; zero `required && !selected` for `crate` scope).
14. NDJSON quorum consistency (`"nanoda_bin"` and `"con-ron"` in `kernels_passed`, plus `"con-leche"` and `"lean4lean"` when `paranoid_quorum && kernels_skipped.is_empty()`).

### 3. Terminal, Ledger, and `cmark-gfm` Sanitization Grammar

Basis: execution (isolated Rust `edition = "2024"` unit suite + `/usr/bin/openssl` C1/RLO probe).

- **Escape Set (`is_dangerous_codepoint`):** Escapes C0/DEL (`0x00..=0x1F`, `0x7F`; `\n`/`\r`/`\t` preserved inline or escaped per context, ESC/BEL as `\xNN`), **UTF-8 C1 (`U+0080..=U+009F`)** as `\u{00XX}`, Bidi overrides/isolates (`U+061C`, `U+200E..=U+200F`, `U+202A..=U+202E`, `U+2066..=U+2069`), `U+2028..=U+2029`, invisible `Default_Ignorable` / variation selectors (`U+00AD`, `U+034F`, `U+200B..=U+200D`, `U+2060..=U+2065`, `U+FEFF`, `U+FFF9..=U+FFFB`, `U+FE00..=U+FE0F`, `U+E0100..=U+E01EF`), and Unicode Tags (`U+E0000..=U+E007F`).
- **`SanitizedBlock` Col-0 Gutter:** Splits on `\n`, escapes lone `\r`, prepends `"  | "` to every line so multi-line `detail`/`hint` never forge `[VERIFIED]` at column 0.
- **`cmark-gfm` Defense:** Escapes `|` → `\|` inside table cells before wrapping in `N + 1` backticks (neutralizing `@username`, `#1234`, `![img](url)`, `<html/>`); multi-line blocks emit inside `max(3, N + 1)` fenced blocks separated from `<details>` tags by blank lines.

### 4. Six-Axis `AssuranceProfile`, Formats, and 3-Tier Semantic `--diff`

Basis: source + derived (`google/zerocopy:reference@425401baa1`).

- **Six Orthogonal Axes (`lattice.rs`):**
  1. `verdict_tier`: `Rejected(FailureStatus) < Tainted(BTreeSet<TaintAtom>) < UnverifiedExtensions(BTreeSet<JsonPtr>) < VerifiedClean`.
  2. `provenance_tier`: `PassiveUnverified < ArtifactsSubsetVerified < ArtifactsExactVerified`.
  3. `scope_tier`: `NotApplicable | SelectedUnit { selected_bodies, required_bodies, unverified_required_bodies, unverified_required_types, total_census } < WholeCrate { verified_bodies, total_census }`.
  4. `containment_tier`: `Unknown < Unsandboxed < ExternalUnverifiedByBinary < SplitActionUnauthenticated < SelfExecSealTier2Landlock < SelfExecSealTier1Bwrap`.
  5. `kernel_tier`: `NotRun < InProcessSingleKernel < NdjsonDualKernelWithSkips < NdjsonDualKernel < NdjsonParanoidQuorum4`.
  6. `axiom_footprint`: `sorryAx < {Classical.choice, Quot.sound, propext} < {Quot.sound, propext} < {propext} < ∅`.
- **Headline Law & Mandatory Badges:** Always renders exact `[FAIL]`, `[TAINTED]`, `[WARN]` (`UNVERIFIED EXTENSIONS`), `[SCOPED]` (`SELECTED UNIT ONLY — K/R required crate bodies; R-K UNVERIFIED`), `[UNATTESTED-SANDBOX]` (`PENDING EXTERNAL CI PROVENANCE`), or `[OK]` (`CRATE VERIFIED (M/M required crate bodies)`), plus Provenance (`[PASSIVE JSON]` vs `[ARTIFACTS VERIFIED]`) and `[STAGE 0 ALPHA — EXPERIMENTAL]` badges even under `--quiet`.
- **Deterministic `--format ledger` (`anneal-receipt-ledger: v1`):** Five fixed sections (`What Is Proved`, `Unverified Crate Scope & Open Caveats`, `Human-Reviewed Specification Closure`, `Trusted Computing Base, Containment & Axioms`, `Not Trusted`), omitting volatile `timing_ms` and listing `proof_modules_count` (not `Proof.lean` hashes) in Section 5 so proof-only refactors keep checked-in `.ledger.txt` goldens stable (`--compare-ledger`).
- **3-Tier Semantic `--diff <base> <head>`:**
  - **Tier A (Trust/Coverage Regression, fails `--no-regressions`):** Any drop in `verdict_tier`, `scope_tier`, `containment_tier`, or `kernel_tier`; new taint, `sorry`, axiom, assumption, `tcb_shim`, `deferred`, `unhashed`, `unrecognized_fields`, or `correspondence_provenance.applicable: true -> false`.
  - **Tier B (`SPEC / SUBJECT REVIEW REQUIRED`, fails `--require-unchanged-specs`):** Changes to `specification_manifest_sha256`, `audit.specificationClosure`, `Specification` sources, `spec_warnings`, `configuration`, Rust `sources`, `capture_sha256`, `model_manifest_sha256`, `toolchain`, `correspondence_provenance`, or strictly positive trust upgrades.
  - **Tier C (`PROOF-ONLY CHANGE`, `exit 0`):** Changes strictly in `Proof`-role digests, `audit.proofNdjsonSha256`, `replayedDeclarations`, `checkedAlternateProofs`, `timing_ms`, or host artifact paths.

### 5. Eliminated Alternatives, Negative Controls, and Open Decisions

Basis: execution + derived.

- **Eliminated alternatives (`A1`–`A6`):** `serde_json::Value` / `#[serde(flatten)]` duplicate-key vulnerability (`A1`); raw printing or ASCII-only sanitization leaking C1 `U+009B` and RLO (`A2`); boolean `"Verified: true"` / outer-status masking (`A3`); naive `std::fs::read(dir.join(rel))` vulnerable to `..`/FIFO hangs (`A4`); raw `diff -u` over JSON (`A5`); adding `anstream`/`owo-colors`/`comfy-table`/`pulldown-cmark` to `trusted/cargo-anneal/Cargo.toml` (`A6`).
- **Negative controls & first-customer target:** Dogfoods `zerocopy/proofs/01..04` (replacing `verify_zerocopy.py`'s custom `validate_receipt()` assertions) plus `tests/inspect.rs` covering duplicate-key smuggling, all 14 envelope tamperings, C0/C1/OSC/Bidi/Tag/`\r`/col-0 escapes, `cmark-gfm` injection (`|`, ```` ``` ````, `</details>`, `![beacon](...)`, `@alice`, `#4012`), symlink/FIFO `--verify-artifacts` attacks, and 3-tier `--diff` monotonicity.
- **Open maintainer policy defaults (`D1`–`D4`):** (`D1`) `--check` validator-by-default (`--passive` opt-out); (`D2`) `--unknown-fields=warn` by default (downgrades headline to `UNVERIFIED EXTENSIONS` and exits `1` under `--check`; `--unknown-fields=deny` exits `2`); (`D3`) 16-hex SHA prefixes in compact `human`/`markdown` (`64`-hex in `--full-digests`/`--verbose`/`ledger`/`json`); (`D4`) exit `0` on untainted `selected_unit_verified` by default (showing `[SCOPED] K/R` banner; `--require-crate-scope` enforces crate-wide).

## Boundaries

- **not examined (full `inspect` production landing & `cli-tty-arch` `output.rs` merge):** The architecture was validated via an isolated Rust `edition = "2024"` prototype (`4/4` unit tests passing) rather than compiled inside `trusted/cargo-anneal` directly.
- **unsupported (compromised build host & specification-intent adequacy):** Consistent with `THREAT_MODEL.md` §2.1–2.2, `inspect --verify-artifacts` verifies disk SHA-256 bindings against the receipt and cannot attest remote CI execution (`external_unverified_by_binary` requires SLSA/RBE logs) or judge whether `Spec.specs` matches human intent.
- **unsupported (legacy pre-alpha v1/v2 receipts):** `schema_version != 3` fails closed (`exit 2`).

## Evidence

- **Inspected baseline:** `google/zerocopy@d3362d9a65` (`anneal/trusted/cargo-anneal/src/{main,verify,target,toolchain}.rs`, `anneal/trusted/rustc-capture/src/{capture,ir}.rs`, `anneal/trusted/cargo-anneal/Cargo.toml`, `anneal/ci/verify_zerocopy.py`, `zerocopy/proofs/01_usize_pointer_metadata/request.json`, `anneal/THREAT_MODEL.md`, `anneal/docs/{build-systems-and-receipts,auditing-and-comparator,spec-core-and-golden-closure}.md`) + `#4147`, `#4152`.
- **Live execution probes:** Isolated Rust `edition = "2024"` tests (`serde 1.0.229`, `serde_json 1.0.154`) proving duplicate-key `Value`/`#[serde(flatten)]` silent overwrites (`4/4` `StrictJsonDom`/`SanitizedInline`/`SanitizedBlock` tests passed); `/usr/bin/openssl` C1/RLO and `gpg` framing probes archived in `google/zerocopy:reference@425401baa150b7a009b2a46780c3e9b4cf31555f`.

## Revalidation

1. After landing `trusted/cargo-anneal/src/{output.rs,inspect/*.rs}`, run `cargo test -p cargo-anneal --no-default-features` and `cargo test -p cargo-anneal --test inspect` covering duplicate JSON keys, all 14 `validate_envelope_invariants` mutations, C0/C1/Bidi/Tag/`cmark-gfm` escapes, `O_NOFOLLOW`/FIFO `--verify-artifacts` attacks, and 3-tier `--diff`.
2. Run `cargo anneal inspect --check --require-untainted --require-containment=execseal --allowed-axioms=propext --verify-artifacts <dir>` against live `zerocopy/proofs/01..04` receipts and verify `Cargo.lock` + `trusted/root-manifest.sha256` remain unmodified.
