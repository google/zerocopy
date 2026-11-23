# Designing CLI Inspectors for Verification Receipts, Attestations, and Audit Ledgers

## Summary

CLI tools that inspect, diff, render, and gate machine-readable verification receipts, supply-chain attestations, and formal-audit reports face four recurring failure classes across cryptographic, SBOM, and formal-verification ecosystems:

1. **Terminal escape, Bidi, and framing spoofing:** Even mature security CLIs leak terminal control characters or mask untrusted data. Live execution against OpenSSL (`crypto/asn1/a_strex.c`) proves that `ASN1_STRFLGS_ESC_CTRL` escapes ASCII C0 (`\x1b` as `\1B`) yet passes raw UTF-8 C1 CSI (`U+009B`) and Unicode Bidi override (`U+202E`) unescaped when `BUF_TYPE_CONVUTF8` is active. Live execution against `gpg --verify` confirms it exits `0` and prints `Good signature` with zero warning when unsigned header and trailer lines surround a valid clearsigned message. In contrast, `gh attestation inspect` (`cli/cli`) prints untrusted certificate/statement URIs unsanitized, and `cosign verify-attestation` prints raw attestation JSON payloads verbatim.
2. **JSON parser differentials in Rust (`serde_json 1.0.154` / `serde 1.0.229`):** Live execution establishes that `serde_json::Value` silently applies last-wins semantics on duplicate keys (`{"a":[1],"a":[]}` -> `[]`). Crucially, even a typed Rust struct using `#[serde(flatten)]` into `BTreeMap<String, Value>` for forward compatibility only rejects duplicate *known* top-level fields: it **silently accepts and last-wins overwrites duplicate unknown keys and duplicate nested keys**.
3. **False assurance from omitted caveats and passive-vs-verified conflation:** Strong inspectors prevent "looks verified when tainted" states structurally. `cargo-vet` never emits a bare `"Vetting Succeeded"` when exemptions exist (`"Vetting Succeeded (X fully audited, Y partially audited, Z exempted)"`); Verus `--output-json` omits `"success": true` whenever `!is_verifying_entire_crate()` and `--no-cheating` bans partial-scope flags alongside `assume`/`admit`/`external_body`; `gh attestation inspect` (`Hidden: true`) discards `verificationResult` under `WithoutArtifactUnsafe()`, though its table formatter still prints `"true (GitHub)"` for `Authentic`. Conversely, `dafny audit`'s `AuditReport.AddAssumptions` hides inner `assume` and bodiless `forall ensures false` findings whenever `{:axiom}` is present on the same declaration, and skips `include`d files.
4. **Deterministic ledgers, golden diffing, and unambiguous exit codes:** Millipede's `<file>.ledger.txt` (`Millipede/Top/Ledger.lean`) and `Tests/Ledger.lean` show how a deterministic plain-text trust table can be regression-tested against the actual codebase (`#guard` checks verifying every cited test script exists and allowlists match). `dafny audit --compare-report` enforces byte-exact CI drift checks, `rust-audit-info` (`cargo-auditable`) bounds decompression (`1 GiB` input / `8 MiB` JSON zip-bomb limit), and Rust security CLIs (`cargo-audit`, `in-toto-verify`, `grype`) reserve distinct non-zero codes for policy/verification failures vs CLI/parse errors.

## Applicability

- **Subjects and relationship:** This report compares 22 cryptographic, supply-chain, SBOM, parser, and formal-verification CLI tools and libraries pinned in `REPORT.json`, synthesizing design invariants for CLI inspectors of verification receipts and audit ledgers.
- **Executed vs source-only evidence:**
  - *Execution + source:* OpenSSL (`openssl x509`), GnuPG (`gpg --verify`, `gpg --decrypt`), and `serde_json` `1.0.154` + `serde` `1.0.229` were executed directly on Linux (`x86_64`) alongside primary-source inspection.
  - *Source-only:* `cli/cli`, `sigstore/cosign`, `slsa-framework/slsa-verifier`, `in-toto/in-toto`, `in-toto/witness`, `mozilla/cargo-vet`, `rust-secure-code/cargo-auditable`, `rustsec/rustsec` (`cargo-audit`), `EmbarkStudios/cargo-deny`, `zizmorcore/zizmor`, `anchore/grype`, `CycloneDX/cyclonedx-cli`, `dafny-lang/dafny`, `verus-lang/verus`, `verus-lang/verus-spec-check`, `graydon/millipede`, `seL4/l4v`, `AbsInt/CompCert`, and `rust-lang/rust` (`compiler/rustc_parse`) were analyzed directly from pinned source revisions (not executed, except `gh 2.103.3` and `cargo-vet 0.8.0` `--help` flag listings).
- **Relationship to prior corpus reports:** Builds on `isabelle-oracle-derivations-hol4-tags-acl2-ttags-pvs-proofchain-status-agda-infective-options-rocq-critical-bugs-lean-native-axioms-and-dafny-audit` (assumption propagation internals and `dafny audit` masking), `millipede-llm-era-verified-systems-language-in-lean` (Millipede compiler overview), `binary-evidence-packaging-provenance-attestations-and-rustc-reproducibility` (`in-toto`/SLSA/Sigstore/`cargo-auditable` formats), and `github-actions-artifact-attestations-fulcio-oidc-and-gh-verify-reusable-workflows` (`gh attestation verify` policy flags). This report isolates **CLI inspection, rendering, diffing, sanitization, and exit-code behavior**.

## Findings

### 1. Passive Display vs. Cryptographic / Artifact Re-Verification

Basis: source (`cli/cli@de06af2c`, `sigstore/cosign@19c90f91`, `slsa-framework/slsa-verifier@46099781`, `in-toto/in-toto@e352b43a`, `in-toto/witness@1eaafd56`, `rust-secure-code/cargo-auditable@8e1e4eb5`)

Tools fall into three distinct epistemic tiers, and conflating passive inspection with verification creates false confidence:

| Tool (Pinned Revision) | Mode | What Is Actually Checked | Key Implementation Detail & Risk |
|---|---|---|---|
| `gh attestation inspect` (`cli/cli@de06af2c`, `pkg/cmd/attestation/inspect/inspect.go:33-54, 167-282`) | Passive + root authenticity (`Hidden: true`) | Checks Fulcio/Rekor/TSA trust against `WithoutArtifactUnsafe()` + `WithoutIdentitiesUnsafe()`. Does **not** hash any artifact or check signer identity. | Explicitly discards `verificationResult` (*"to avoid even implying that it is 'verified'"*, L172-173), yet `formatAuthentic` prints `"true (GitHub)"` (L259, 293-303), risking user confusion with `gh attestation verify`. |
| `cosign verify-attestation` / `verify-blob-attestation` (`sigstore/cosign@19c90f91`, `verify_attestation.go:115-117`, `verify_blob_attestation.go:140-155`, `common.go:87-108`) | Active cryptographic verify (claim check opt-in via `--check-claims`) | Without `--check-claims`, `verify-blob-attestation` calls `sgverify.WithoutArtifactUnsafe()`. `PrintVerificationHeader` enumerates exact checks performed (claims, offline tlog vs online Rekor, pubkey vs Fulcio). | Separating *which checks ran* in an explicit header (`common.go:87-108`) avoids overclaiming, though skipping `--check-claims` still allows valid signatures on mismatched subjects unless the caller passes `--check-claims`. |
| `slsa-verifier verify-artifact` (`46099781`, `verify/verify_artifact.go:44-87`) | Always-active verify | Always computes SHA-256 of local artifact, verifies envelope/provenance/builder, prints `PASSED`/`FAILED` to `stderr`, and dumps provenance JSON to `stdout` only with `--print-provenance`. | Keeps verdict stream (`stderr`) distinct from machine provenance output (`stdout`). |
| `in-toto-verify` (`e352b43a`, `in_toto_verify.py:236-241`) & `witness verify` (`1eaafd56`, `cmd/verify.go:205-249`) | Active supply-chain policy verify | Verifies layout/policy signatures, expiry, step thresholds, and artifact rules/digests; `witness` prints per-step `Passed` reference vs `Rejected` reason (`L218-247`). | Full end-to-end verification; no passive inspection mode on `verify`. |
| `rust-audit-info` (`cargo-auditable@8e1e4eb5`, `rust-audit-info/src/main.rs:25-34`) | Pure passive extractor | Extracts `.dep-v0` zlib-compressed JSON from a compiled binary with zip-bomb bounds (`1 GiB` input cap, `8 MiB` decompressed JSON cap, `L14-15`). | Never verifies that embedded metadata matches the actual linked binary or source; writes raw JSON bytes directly to `stdout`. |

**Design takeaway:** Any CLI `inspect` command that reads a receipt JSON without re-hashing workspace inputs/outputs on disk must prominently distinguish **passive format rendering** from **verified artifact re-checking** (`--verify-artifacts`) in its output header so a valid JSON parse cannot be mistaken for live workspace verification.

---

### 2. Preventing Visual Spoofing and Untrusted-String Terminal Injection

Basis: source (`openssl/openssl@24111468`, `rust-lang/rust@58cf8f9c`, `cli/cli@de06af2c`, `sigstore/cosign@19c90f91`, `zizmorcore/zizmor@0af0be98`) + execution (`openssl`, `gpg`)

Receipt and attestation parsers ingest untrusted strings (package names, source paths, error details, certificate CNs/SANs, predicate fields). Five concrete failure modes appear in primary sources and live probes:

1. **OpenSSL UTF-8 C1 & Bidi bypass (`openssl@24111468`, `crypto/asn1/a_strex.c:91-115, 208-226` + execution):**
   - In `do_esc_char`, ASCII bytes (`<= 0x7f`) consult `char_type[chtmp] & flags`, so `ASN1_STRFLGS_ESC_CTRL` escapes `0x1b` (`ESC`) as `\1B`. Bytes `> 0x7f` instead check `flags & ASN1_STRFLGS_ESC_MSB` (`a_strex.c:91-92`).
   - When `BUF_TYPE_CONVUTF8` is active (used for UTF-8 output), `do_buf` converts each codepoint into UTF-8 bytes and passes each byte `> 0x7f` to `do_esc_char` (`a_strex.c:208-226`) where `ASN1_STRFLGS_ESC_MSB` is `0`.
   - **Live probe on `/usr/bin/openssl`:** Generating a self-signed X.509 cert with `CN = EVIL\x1b[32mVERIFIED\x1b[0m` printed `subject=CN=EVIL\1B[32mVERIFIED\1B[0m` (escaped), whereas `CN = EVIL\x9b32m_BIDI_\u202efake` (`\xc2\x9b` = C1 CSI `U+009B`, `\xe2\x80\xae` = RLO `U+202E`) emitted **raw unescaped C1 CSI and RLO bytes** on both `openssl x509 -noout -subject` and `-nameopt utf8`.
2. **GnuPG clearsigned framing spoof (live execution on `/usr/bin/gpg`):**
   - Wrapping a valid clearsigned block in `UNSIGNED HEADER SPOOF\n...\nUNSIGNED TRAILER SPOOF\n` caused `gpg --status-fd=1 --verify` to exit **`0`**, print `gpg: Good signature from "Alice" [ultimate]` to stderr, and emit `[GNUPG:] GOODSIG` and `VALIDSIG` to stdout with **zero warning** that unsigned surrounding text existed. Only `gpg --decrypt -o verified.txt` isolated the signed payload (`REAL SIGNED PAYLOAD\n`).
   - For terminal escaping of key UIDs (`Evil\x1b[32mFake`), GnuPG C-escaped stderr (`Evil\\x1b[32mFake`) and percent-escaped `--status-fd` (`Evil%1B[32mFake`).
3. **Unsanitized terminal printing in modern Go/Rust CLIs:**
   - `gh attestation inspect` (`inspect.go:256-282`) prints `SubjectAlternativeName`, `PredicateType`, `RunInvocationURI`, and `SourceRepositoryURI` via `OutPrintf` without stripping or escaping ANSI/Bidi sequences. `cosign` (`common.go:121-151`) and `slsa-verifier` (`verify_artifact.go:76`) print raw JSON payload strings directly to stdout.
   - `zizmor` (`output/github.rs:36-47`) interpolates workflow filenames, descriptions, and annotations directly into GitHub Actions workflow command lines (`::error file=...,line=...,title=...::{message}`), which requires newline/percent sanitization when untrusted strings appear in annotations.
4. **Rust compiler Trojan Source & confusable catalog (`rust-lang/rust@58cf8f9c`):**
   - `rustc` defends against CVE-2021-42574 via `TEXT_DIRECTION_CODEPOINT_IN_LITERAL` / `TEXT_DIRECTION_CODEPOINT_IN_COMMENT` (`compiler/rustc_parse/src/lexer/mod.rs:14`) and maintains `UNICODE_ARRAY` (`compiler/rustc_parse/src/lexer/unicode_chars.rs:11-70`) covering confusable spaces (`U+00A0`, `U+1680`, `U+2000..U+200A`, `U+2028`, `U+2029`, `U+202F`, `U+205F`, `U+3000`).
5. **Markdown / PR-comment injection (`dafny-lang/dafny@427892ac`, `AuditReport.cs:88-104`):**
   - `dafny audit` emits Markdown tables (`| {GetFullName(decl)} | ... |`) and HTML (`<tr><td>...`) without escaping `|`, `<`, `>`, or backticks inside declaration names, and only converts backtick literals in `Assumption.UpdateVerbatim`.
   - For GitHub `cmark-gfm` PR comments, wrapping untrusted strings inside dynamic $N+1$-backtick inline code spans neutralizes raw HTML (`<details>`, `<!--`), Markdown image beacons (`![x](https://...)`), and `@user`/`#123` mention pings, while escaping `|` (`\|`) prevents GFM table column injection (note `cmark-gfm` splits table pipes before parsing inline code spans, so arbitrary untrusted text is safest in fenced code blocks or bulleted lists with escaped `|`).

**Complete sanitization rule derived from these sources:** Every text renderer (TTY, plain, ledger, Markdown) must neutralize:
- ASCII C0 (`0x00..=0x1F`) and DEL (`0x7F`) — blocking ANSI CSI (`\x1b[`), OSC 8 hyperlinks (`\x1b]8;;`), OSC 0/2/52, and raw `\r` line-overwrites;
- C1 controls (`U+0080..=U+009F`, including CSI `U+009B`, ST `U+009C`, OSC `U+009D`);
- `Default_Ignorable` / Bidi formatting characters (`U+061C`, `U+200B..=U+200F`, `U+202A..=U+202E`, `U+2028..=U+2029`, `U+2060`, `U+2066..=U+2069`, `U+FEFF`, `U+E0000..=U+E007F`, and variation selectors `U+FE00..=U+FE0F`, `U+E0100..=U+E01EF`);
- Unbounded newlines in single-line fields (escaped as `\n`), and column-0 log forging in multi-line blocks (prefixing every emitted line with a fixed gutter such as `  | `).

---

### 3. JSON Parser Differentials & Forward-Compatibility Paradox (`serde_json`)

Basis: source (`serde-rs/json@f51fa15a`, `src/de.rs:34-67, 145-148, 1372-1385`) + execution (`serde_json 1.0.154`, `serde 1.0.229`)

Testing `serde_json` live against a receipt-like payload (`taint_reasons`) exposes a subtle parser differential when supporting unknown forward-compatible fields:

| Deserialization Strategy | Trailing Tokens | Duplicate Known Top-Level Key | Duplicate *Unknown* Top-Level Key | Duplicate Nested Key (inside `Value`) | Unknown Field Handling |
|---|---|---|---|---|---|
| `serde_json::Value` | Rejected (`de.rs:148`) | **Accepted (last-wins)** | **Accepted (last-wins)** | **Accepted (last-wins)** | Preserved silently |
| `#[derive(Deserialize)]` struct (no `flatten`) | Rejected | **Rejected** | Ignored | **Accepted (last-wins)** if field is `Value` | Ignored silently |
| `#[derive(Deserialize)]` + `#[serde(flatten)] extra: BTreeMap<String, Value>` | Rejected | **Rejected** | **Accepted (last-wins)** | **Accepted (last-wins)** | Captured in `extra` |
| `#[derive(Deserialize)]` + `#[serde(deny_unknown_fields)]` | Rejected | **Rejected** | **Rejected** | **Rejected** (if all nested types are structs) | Rejected |

**Security consequence:** Using `serde_json::Value` or `#[serde(flatten)]` into `BTreeMap<String, Value>` reintroduces RFC 8259 duplicate-key ambiguity (`{"new_taint":["a"],"new_taint":[]}` silently becomes `[]`), while silently ignoring unknown fields lets an older inspector render a clean banner on a newer receipt that added a critical caveat field (such as skipped kernels or weakened containment). A sound inspector must either enforce `deny_unknown_fields` with a recursive duplicate-key-rejecting validator, or capture unknown fields through a **custom recursive duplicate-key-rejecting `DeserializeSeed` / `MapAccess` pass** and visibly downgrade the top-line verdict with an `UNRECOGNIZED_FIELDS` notice whenever `extra` is non-empty.

---

### 4. Preventing "Looks Verified When Tainted" Across Verification Tools

Basis: source (`mozilla/cargo-vet@a9bde859`, `verus-lang/verus@1ce6a59b`, `verus-lang/verus-spec-check@8ffdbe43`, `dafny-lang/dafny@427892ac`, `graydon/millipede@4f13d398`, `seL4/l4v@df4f4448`, `AbsInt/CompCert@2685140b`)

| System | Strong Anti-Masking Pattern | Residual Gap / Footgun |
|---|---|---|
| **`cargo-vet`** (`a9bde859`, `src/resolver.rs:2114-2126, 2205-2254`) | `Success::print_human` never prints a bare `"Vetting Succeeded"`: it always parenthesizes `"Vetting Succeeded (X fully audited, Y partially audited, Z exempted)"`; JSON splits `vetted_fully`, `vetted_partially`, `vetted_with_exemptions`. | Exits `0` even when exemptions or expiring wildcards exist (emitting warnings only). |
| **`verus`** (`1ce6a59b`, `source/rust_verify/src/{main.rs:543-558,config.rs:896-920}`, `tests/no_cheating*.rs`) | `--output-json` **omits `"success"` entirely** whenever `!is_verifying_entire_crate()`; `--no-cheating` bans partial-scope flags (`--verify-root`, `--verify-module`, `--verify-only-module`, `--verify-function`, `--no-lifetime`, `--no-erasure-check`, `--no-trait-conflicts`, `-V allow-inline-air`, `-V ignore-unexpected-smt`) and `assume`/`admit`/`#[verifier::external_body]`/`assume_specification`/`#[verifier::assume_termination]`. | Without `--no-cheating`, `verified` counts still increment alongside `assume`/`admit` warnings; `#[verus::trusted]` overrides work top-down (`trusted_child_below_untrusted_is_rejected`). |
| **`verus-spec-check`** (`8ffdbe43`, `README.md:68-85`) | Complements proofs with `#[vcheck_cov_mutate]` (mutation kill rate) and `#[vcheck_cov_fuzz]` (branch coverage) with `threshold = N` build failure gates. | Requires patched `verus_builtin_macros` (`#[vcheck]`). |
| **`dafny audit`** (`427892ac`, `AuditReport.cs:38-45, 193-196`, `Auditor.cs:108-159`) | Explicit assumption taxonomy (`Assumption.cs`), 4 deterministic formats (`txt`, `html`, `md-table`, `md-ietf`), and `--compare-report` golden drift failure. | `AddAssumptions` drops inner `assume`s and bodiless `forall`s when `{:axiom}` is on the declaration (`AuditReport.cs:38-45`); `BuildReport` skips `FromIncludeDirective` code (`L193`). |
| **`Millipede`** (`4f13d398`, `Millipede/Top/Ledger.lean:150-215`, `Tests/Ledger.lean:35-96`) | Emits deterministic `.ledger.txt` separating `== What is proved ==`, `== Open claims ==`, `== Trusted ==`, and `== Not trusted (proved) ==`; prints `NOT CHECKED` / `NOT PROVED` in caps; `#guard` tests verify every cited script exists and matches `#audit` allowlists. | Ledger text is coupled to `Ledger.lean` definitions rather than independently parsed from an external receipt. |
| **`seL4/l4v`** (`df4f4448`, `misc/stats/sorry-count.sh`, `misc/regression/run_tests.py:72-78`) | `sorry-count.sh` counts `sorry` per directory; `run_tests.py` checks `isabelle options -g skip_proofs` and emits a visible warning before running. | `skip_proofs` warns rather than aborting local developer runs. |
| **`CompCert`** (`2685140b`, `Makefile:297-299, 459-468`) | `check-admitted` (`admit`/`Admitted`), `check-leftovers` (`Check`/`Print`/`Search`), `check-proof` (`coqchk compcert.driver.Complements`), and extraction `AXIOM TO BE REALIZED` grep all fail the build (`exit 2`). | Makefile grep checks depend on source conventions alongside `coqchk`. |

---

### 5. Artifact Directory Verification, Semantic Diffing, and Exit Codes

Basis: source (`in-toto@e352b43a`, `CycloneDX/cyclonedx-cli@b3cfa4b0`, `rustsec/rustsec@bafea68f`, `EmbarkStudios/cargo-deny@6d512893`, `zizmorcore/zizmor@0af0be98`, `anchore/grype@8b2987cf`)

1. **Offline directory verification traps (`in-toto/verifylib.py:712`):** Path-prefix normalization alone in Python `open()` does not prevent symlink escapes, `..` traversal, FIFOs (`/dev/zero` hang), or unreferenced extra files in an untrusted artifact directory. Hardened artifact re-verification requires relative `Normal`-component paths only, `O_RDONLY | O_NOFOLLOW | O_NONBLOCK`, `fstat` regular-file (`S_ISREG`) checks, streaming SHA-256 over the open FD, bounded file reads, and explicit reporting of extraneous unreferenced files (`manifest-exact` vs `subset`).
2. **Semantic diffing (`cyclonedx-cli@b3cfa4b0`, `DiffCommand.cs:51-108`; `cargo-vet@a9bde859`, `main.rs:2050-2166`; `dafny@427892ac`, `Auditor.cs:140-150`):**
   - `cyclonedx-cli diff` supports structured JSON vs `-`/`=`/`+` text diffs; `cargo vet diff` runs `git diff --no-index` in a TTY-aware pager; `dafny audit --compare-report` writes `<file>.expect` on mismatch.
   - For formal-verification receipts, semantic diffs improve auditability when partitioned monotonically: **(A) Trust/soundness regressions** (verdict/scope downgrade, new taint/axioms/shims, containment downgrade, fewer kernels) surfaced first and gateable via `--no-regressions`; **(B) Specification/capture boundary changes** requiring spec review; **(C) Proof-only/operational timing churn** with identical trust and specification digests.
3. **Exit-code conventions across security & verification CLIs:**
   - **Clean (`0`) vs Policy/Verification Failure (`1`) vs Tool/CLI/Parse Error (`2`):** `cargo-audit` (`cargo-audit/src/commands/mod.rs:152-160`: `0` clean, `1` vulnerability/policy fail, `2` parse/DB error) and `in-toto-verify` (`in_toto_verify.py:20-23, 245-247`: `0` pass, `1` verification fail, `2` arg parse error).
   - **Severity / bitmask non-zero codes:** `anchore/grype` (`cmd/grype/cli/cli.go:83-89`: `0` clean, `1` error, `2` `--fail-on` severity threshold exceeded, `100` DB update); `zizmor` (`registry.rs:258-268`, `main.rs:600-604`: `0` clean, `1` error, `3` `NoInputs`, `11..=14` severity); `cargo-deny` (`src/cargo-deny/stats.rs`: `1..=15` check bitmask, `1` error).
   - **Opt-in failure hazard:** `cyclonedx validate` (`ValidateCommand.cs:154`) returns `ExitCode.Ok` (`0`) even on invalid BOMs unless `--fail-on-errors` is passed, and `gh attestation inspect` (`inspect.go:177-182`) exits `0` even when `Authentic: false`. For verification receipt inspectors used in CI, defaulting to non-zero on failed/tainted receipts (or requiring explicit `--allow-tainted` / `--passive` for `0`) prevents silent CI false-greens when callers omit `--check`.

## Boundaries

- **Not executed (`not examined` dynamically):** `cli/cli` `gh attestation inspect` (hidden in `gh 2.103.3` help), `cosign`, `slsa-verifier`, `in-toto-verify`, `witness`, `cargo-audit`, `cargo-deny`, `zizmor`, `grype`, `cyclonedx-cli`, `dafny audit`, `verus`, `verus-spec-check`, `seL4/l4v`, and `CompCert` were inspected from pinned source only; only `openssl`, `gpg`, and `serde_json` (`1.0.154`) + `serde` (`1.0.229`) were executed in live probes.
- **Not examined (`not examined`):** Unicode terminal width (`wcwidth`) / combining-mark rendering discrepancies across specific terminal emulators (e.g., kitty, iTerm2, Windows Terminal), and non-JSON receipt formats (CBOR/COSE, ASN.1 DER) parser differentials.
- **Known limits (`known not to apply`):** RFC 8259 duplicate-key rejection in a receipt parser does not by itself protect against malicious content inside single valid keys; it must be paired with typed schema validation and output sanitization. Likewise, passive receipt inspection cannot detect post-verification workspace tampering without `--verify-artifacts` re-hashing against disk.

## Evidence

All primary evidence was gathered or executed on `2026-11-23`:

- **GitHub sources (pinned commits in `REPORT.json`):**
  - `cli/cli@de06af2c2ea536d5722fda35dc2001565f9b9f64`: `pkg/cmd/attestation/{attestation.go,inspect/{inspect.go,bundle.go,options.go},verify/verify.go}`.
  - `sigstore/cosign@19c90f91263701e6e3fb9f6e32ae1a8199712baf`: `cmd/cosign/cli/{tree.go,verify/{common.go,verify.go,verify_attestation.go,verify_blob_attestation.go}}`.
  - `slsa-framework/slsa-verifier@46099781eca1b8e91884770f40476631b033e0e8`: `cli/slsa-verifier/{main.go,verify/verify_artifact.go}`.
  - `in-toto/in-toto@e352b43ad7cb8915d84c36d791aa61346152a0a3`: `in_toto/{in_toto_verify.py,verifylib.py}`.
  - `in-toto/witness@1eaafd56616bdf6c136e80ab92a9a0944e6c0ced`: `cmd/verify.go`.
  - `mozilla/cargo-vet@a9bde85910409be3d2d61e6f6ff6ba7a521f0412`: `src/{main.rs,cli.rs,out.rs,resolver.rs}`.
  - `rust-secure-code/cargo-auditable@8e1e4eb579a99622f4430b2b28e441a24fb2d74d`: `rust-audit-info/src/main.rs`.
  - `rustsec/rustsec@bafea68f94f3b9587f826c5b7ceda78955c5ba84`: `cargo-audit/src/{commands/mod.rs,terminal.rs,presenter.rs}`.
  - `EmbarkStudios/cargo-deny@6d512893fcfea934e8e69c5df44132a4970c42d0`: `src/cargo-deny/{main.rs,check.rs,stats.rs}`.
  - `zizmorcore/zizmor@0af0be985a4cae71ecfaa64ef574a94b35dc722a`: `crates/zizmor/src/{main.rs,registry.rs,output/{plain.rs,github.rs}}`.
  - `anchore/grype@8b2987cf575c69fb715ae4d3b15bb470e3e8f83b`: `cmd/grype/{main.go,cli/{cli.go,commands/root.go}}`.
  - `CycloneDX/cyclonedx-cli@b3cfa4b0edc356dad07e0b6e7ab6da0a94af0246`: `src/cyclonedx/{Program.cs,Commands/{DiffCommand.cs,ValidateCommand.cs}}`.
  - `openssl/openssl@241114689e8a032d00f7408987bda6309f34c45b`: `crypto/asn1/a_strex.c`, `apps/x509.c`.
  - `dafny-lang/dafny@427892ac6f36204c6a1c760b328b74e0715a0efa`: `Source/DafnyCore/Auditor/{Assumption.cs,AuditReport.cs,Auditor.cs}`, `Source/DafnyDriver/Commands/AuditCommand.cs`, `Source/IntegrationTests/TestFiles/LitTests/LitTest/auditor/TestAuditor.dfy.md.expect`.
  - `verus-lang/verus@1ce6a59bd72713cf486a7660097fe5ac57519617`: `source/rust_verify/src/{config.rs,main.rs,verifier.rs,external.rs}`, `source/rust_verify_test/tests/{no_cheating.rs,no_cheating_assumptions.rs}`.
  - `verus-lang/verus-spec-check@8ffdbe43a1ac47db6208eb2da338676244143d9f`: `README.md`.
  - `graydon/millipede@4f13d3980a5570177a774e63cfbc95e652dd3cde`: `Millipede/Top/Ledger.lean`, `Tests/Ledger.lean`.
  - `seL4/l4v@df4f444823f8c9f99b4a9f45990001eecc820a5a`: `misc/stats/sorry-count.sh`, `misc/regression/run_tests.py`, `run_tests`.
  - `AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`: `Makefile`, `driver/{Driver.ml,Complements.v}`.
  - `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`: `compiler/rustc_parse/src/lexer/{mod.rs,unicode_chars.rs}`.
  - `serde-rs/json@f51fa15a7015c7d02817a46d2db44c899a0016e8`: `src/de.rs`.
- **Live execution probes (preserved in `support/`):**
  - `support/probe_openssl_gpg_spoofing.py`: Reproduces OpenSSL escaping `\x1b` while passing raw UTF-8 `\x9b` (C1 CSI) and `\u202e` (RLO), and reproduces `gpg --verify` exiting `0` on clearsigned text wrapped in unsigned header/trailer lines vs `gpg --decrypt`.
  - `support/probe_serde_duplicate_keys.py`: Reproduces `serde_json` `Value` and `#[serde(flatten)]` silent last-wins behavior on duplicate unknown and nested keys vs strict `#[derive(Deserialize)]` rejection of top-level known duplicates.

## Revalidation

1. **Re-run the OpenSSL and GnuPG terminal/framing probes:**
   ```bash
   python3 reports/receipt-attestation-audit-cli-inspection-and-anti-spoofing/support/probe_openssl_gpg_spoofing.py
   ```
   Checks whether a newer OpenSSL escapes UTF-8 C1 (`U+009B`) or Bidi (`U+202E`) in `openssl x509 -subject`, and whether `gpg --verify` warns or exits non-zero when unsigned text wraps a clearsigned message.
2. **Re-run the `serde_json` duplicate-key and `#[serde(flatten)]` probe (requires Rust toolchain + network or cached `serde`/`serde_json` crates):**
   ```bash
   python3 reports/receipt-attestation-audit-cli-inspection-and-anti-spoofing/support/probe_serde_duplicate_keys.py
   ```
   Verifies whether `serde` / `serde_json` changes duplicate-key rejection inside `#[serde(flatten)]` or `Value`.
3. **Check upstream source diffs on key inspector hooks:**
   Diff `crypto/asn1/a_strex.c` in `openssl/openssl` against `24111468`, `pkg/cmd/attestation/inspect/inspect.go` in `cli/cli` against `de06af2c`, and `Source/DafnyCore/Auditor/AuditReport.cs` in `dafny-lang/dafny` against `427892ac`.
