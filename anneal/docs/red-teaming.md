<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Automated Red-Teaming Harness

Anneal's automated red-teaming harness (`ci/redteam/`) evaluates adversarial
candidate proofs, Rust crates, specifications, and theory extensions against an
immutable defender configuration in a fresh ephemeral workspace.

> [!NOTE]
> The harness tests Anneal's own verification guarantees. Any candidate that
> wins indicates a real soundness, preflight, audit, or sandbox-confinement
> bypass inside the tool under test and triggers automated mechanism
> deduplication.

## Workspace composition preamble

Automated red-teaming builds directly on the workspace staging and role-binding
rules documented in [workspace composition](workspace-composition.md). Before
invoking `cargo anneal verify`, the defender harness assembles `request.json`,
defender-owned Rust/Spec/Proof assets, and strictly slot-checked attacker
inputs into an isolated directory, while `cargo-anneal` generates
`capture/Captured.lean` (`Captured.program`) and `generated/Expected.lean`
(`Expected.claim`) inside the private execution stage:

- **`s1a_ub_proof_hack` / `s1b_spec_violation_proof_hack`:** Defender locks
  `src/lib.rs`, `Spec.lean` (`TargetRole::Specification`), and `request.json`
  (`selected_unit` scope); attacker controls only `Proof/*.lean`
  (`TargetRole::Proof`) trying to prove defender's `Expected.claim`.
- **`s2_code_and_proof_hack`:** Defender locks `Cargo.toml`, whole-crate
  `Spec.lean`, and `request.json` (`crate` scope); attacker controls
  `src/**/*.rs` and `Proof/*.lean` (plus optional `witness.json`, Tier-E1
  `incorrectness/semantics.patch` + `incorrectness/Proof.lean`, or Tier-E2
  `incorrectness/claim.md`), composed into attacker `Captured.program` +
  defender `Spec.specs` under `CrateTheorem`. When Anneal wrongly accepts flawed
  code without Miri/rustc confirmation, E1 proves
  `¬ Spec.targetSpec Captured.program` under a strictly scoped
  `Trusted/MirSemantics/*.lean` patch validated by strict `anneal-audit` and a
  Preservation Canary Gate (`target(x) = x` + positive `MirSemantics` canaries).
- **`s3_spec_preflight_hack`:** Defender locks `src/lib.rs`, broken
  `Proof.lean`, and `request.json` (`selected_unit` scope); attacker supplies
  `Spec.lean` / `Spec/*.lean` (`TargetRole::Specification`) before
  `cargo-anneal` binds it into `Expected.claim`.
- **`s4_theory_audit_hack`:** Defender locks pinned `anneal/` sources
  (`Cargo.*`, `flake.*`, `trusted/`, `tests/`, `tools/`, `vendor/`,
  `correspondence/`); attacker supplies `theory/**/*.lean` for Pass-1
  `anneal-audit --json`.

See [workspace composition][wc-rt] for full details on generated modules,
`CrateTheorem`/`UnitTheorem` bindings, and reserved module roots.

[wc-rt]: workspace-composition.md#automated-red-teaming-composition-contract

## Design principles and trust boundaries

Red-teaming separates untrusted **attacker-controlled slots** from
**defender-fixed assets**:

1. **Isolated ephemeral staging:** Every run unpacks only clean regular files
   inside the active scenario's declared `allowed_paths`. Symbolic links,
   hardlinks (`st_nlink > 1`), `..` traversals, backslashes, NUL bytes,
   out-of-slot paths, and oversized archives fail closed as
   `INVALID_SUBMISSION`.
2. **Defender-private SHA-256 inventory:** `Cargo.toml`, `request.json`,
   defender-fixed `Spec.lean` or `src/`, `trusted/` sources, and CLI invocation
   policy belong exclusively to the defender. The harness computes the pre-run
   defender SHA-256 inventory (and optional attacker-submission digests for
   experimental reproducibility) strictly in defender-private memory/storage
   outside the ephemeral workspace—never written to disk or readable by
   attacker code.
3. **Pre-run verification, in-run containment, and escape detection:** Primary
   enforcement comes from pre-run staging verification together with OS-level
   in-run containment (`ExecSeal`: `linux_bwrap` / `linux_landlock_seccomp`,
   plus zero `--allow-*` flags and scrubbed environment variables). Post-run
   defender hashing is **not** a TOCTOU boundary against modify-then-revert
   tricks; rather, if a **rule-following** submission
   (`INVALID_SUBMISSION == false`) mutates, replaces, or deletes any
   defender-owned file during execution (including forbidden Lean
   metaprogramming firing before preflight),
   that reveals a real sandbox or anti-cheating bug: the harness surfaces
   `sandbox_escape_detected: true` (`defender_integrity_ok: false`) as
   `ATTACKER_WON` (`escape_mechanism: "sandbox_escape"`), never masking it as
   `DEFENDER_HELD` or `HARNESS_ERROR`.
4. **Zero weakening:** `cargo anneal verify` runs with default `ExecSeal`
   containment and zero `--allow-*` flags (`status` must be `crate_verified`
   or `selected_unit_verified` with zero taints and only baseline `deferred`
   items: `"complete review-surface reporting"` and
   `"source-to-deployed-binary correspondence"`). Every passing run is
   cross-checked by `cargo anneal inspect` with `--require-untainted`,
   `--require-containment`, `--verify-artifacts`, and
   `--require-exact-artifacts`.
5. **Ignore untrusted claims:** Comments, descriptions, or metadata supplied by
   the attacker never enter verdict logic or deduplication keys.

## Verdicts

| Verdict | Meaning | `dedup` field |
| --- | --- | --- |
| `ATTACKER_WON` | Rule-following submission bypassed Anneal (`verify`/`inspect`/`audit` clean pass) **with** either fixed-target violation (`PROOF_HACK`, `SPEC_PREFLIGHT_HACK`, `THEORY_AUDIT_HACK`) or Tier-E0 oracle confirmation (`P0`), **or** mutated a defender asset during execution (`sandbox_escape_detected: true`, `P0`). | Present |
| `NEEDS_HUMAN_REVIEW` | `s2_code_and_proof_hack` passed strict unpatched `verify` + `inspect` cleanly without Tier-E0 confirmation, and supplied either passing Tier-E1 `semantics.patch` + `Proof.lean` + Preservation Canary Gate (`lean_patch_proof`, `P1`) or Tier-E2 `incorrectness/claim.md` alone (`prose_claim`, `P2`). Surfaces for human review without inflating `ATTACKER_WON` metrics. | Present (`witness_hash` excludes `claim.md`) |
| `DEFENDER_HELD` | Submission was valid and Anneal caught or rejected the flaw (`anneal-audit` exit `1` for Scenario 4; or, in Scenario 2, neither E0/E1/E2 triggered, or supplied E1 failed `anneal-audit` / broke the Preservation Canary Gate). | `null` |
| `INVALID_SUBMISSION` | Path violation, link, out-of-slot file, incomplete E1 pair, patch > 250 lines or outside `Trusted/MirSemantics/*.lean`, or invalid schema. | `null` |
| `HARNESS_ERROR` | Pre-run setup, defender infrastructure or operational failure (missing tool binaries, corrupt host staging, `cargo anneal verify`/`inspect` timeout, malformed output, or operational non-`1` exit, `anneal-audit` timeout, operational non-`1` exit, or invalid JSON on clean theory), or incomplete post-accept defender audit (e.g., Lean AST inspector timeout or parse divergence). Never used for rule-following post-run mutations or post-pass bypasses. | `null` |

### Tiered incorrectness evidence for `s2_code_and_proof_hack`

Because an attacker controls both `src/**/*.rs` and `Proof/*.lean` in
`s2_code_and_proof_hack` and Miri alone has blind spots, the harness evaluates
accepted unpatched runs (`anneal_verify_ok && anneal_inspect_ok`) against a
fail-closed 3-tier evidence ladder recorded via
`incorrectness_evidence_tier`, `patch_incorrectness_verified`,
`preservation_gate_passed`, `human_review_required`, and `proposed_severity`:

1. **Tier `E0` (`executable_oracle`, `P0`):** Miri (`-Zmiri-tree-borrows`) or
   `rustc` confirms UB, panic, or `target(x) != x` on `DEFAULT_S2_INPUTS`
   plus optional `witness.json`. Emits `ATTACKER_WON`
   (`human_review_required: false`).
2. **Tier `E1` (`lean_patch_proof`, `P1`, strict human-review gated):**
   Attacker supplies both `incorrectness/semantics.patch` (`<= 250` changed
   lines strictly within `anneal/trusted/lean/Trusted/MirSemantics/*.lean`) and
   `incorrectness/Proof.lean` (plus optional `incorrectness/Helper/*.lean`).
   After strict unpatched `verify` + `inspect` pass, the defender stages an
   isolated patched copy of `anneal/`, generates defender-owned
   `IncorrectnessExpected.lean` (`¬ Spec.targetSpec Captured.program`) binding
   the exact unpatched `Captured.program` + immutable defender `Spec.specs`,
   enforces patched `anneal-audit` verification
   (`{propext, Classical.choice, Quot.sound}` only), strict `TrustedBoundary`
   preflight and kernel-replay audit inside `bwrap` (`ExecSeal`), and a
   **Defender Preservation Canary Gate** requiring valid
   `pub fn target(x: u32) -> u32 { x }` against `Spec.specs` plus all pinned
   positive `MirSemantics` canaries to keep passing. Passing `E1` emits
   `NEEDS_HUMAN_REVIEW` (`proposed_severity: "P1"`,
   `patch_incorrectness_verified: true`, `preservation_gate_passed: true`) so
   unvalidated semantics edits stay separate from confirmed `ATTACKER_WON` `P0`
   incidents; any broken canary fails closed as `DEFENDER_HELD`
   (`preservation_gate_passed: false`, without falling through to `claim.md`).
3. **Tier `E2` (`prose_claim`, `P2`, human-review gated):** When unpatched
   Anneal accepts without `E0` or supplied `E1` artifacts, valid
   `incorrectness/claim.md` (`<= 64 KiB` UTF-8 Markdown) emits
   `NEEDS_HUMAN_REVIEW` (`proposed_severity: "P2"`), attaching a scrubbed
   `incorrectness_claim` excerpt to `trace_artifacts` without influencing
   `dedup` or `witness_hash`.

## Scenario catalog

List available scenarios and exact machine-readable submission schemas with:

```bash
# Print scenario catalog as JSON
(cd anneal && python3 -B ci/redteam/harness.py list-scenarios --json)
```

| Scenario ID | Kind | Attacker slots | Win rule |
| --- | --- | --- | --- |
| `s1a_ub_proof_hack` | `PROOF_HACK` | `Proof/Proof.lean` (+ `Proof/*.lean`) | `verify` + `inspect` pass clean on defender's UB crate (`usize::MAX.unchecked_add(1)`), or defender files are escaped. |
| `s1b_spec_violation_proof_hack` | `PROOF_HACK` | `Proof/Proof.lean` (+ `Proof/*.lean`) | `verify` + `inspect` pass clean on defender's crate that violates `Spec.returnsZero`, or defender files are escaped. |
| `s2_code_and_proof_hack` | `CODE_AND_PROOF_HACK` | `src/**/*.rs`, `Proof/*.lean`, optional `witness.json`, optional `incorrectness/` (`E1` patch+proof or `E2` `claim.md`) | Unpatched `verify` + `inspect` pass clean AND either `E0` Miri/rustc confirms UB/`target(x) != x` (`P0`) or sandbox escape (`P0`); `E1` `semantics.patch` + `Proof.lean` + Preservation Canary Gate (`P1`) and `E2` `claim.md` (`P2`) emit `NEEDS_HUMAN_REVIEW`. |
| `s3_spec_preflight_hack` | `SPEC_PREFLIGHT_HACK` | `Spec/Spec.lean` (+ `Spec/*.lean`) | `verify` + `inspect` pass clean AND non-admitted Lean constructs or axioms leaked past `SpecPreflight` (or sandbox escape). |
| `s4_theory_audit_hack` | `THEORY_AUDIT_HACK` | `theory/<RelPath>.lean` | `anneal-audit --json` exits `0` despite forbidden constructs or extra axioms in `theory/` (or sandbox escape). |

See [the attacker prompt template](../ci/redteam/REDTEAM_PROMPT_TEMPLATE.md)
for the exact file layout expected in `--submission-dir` / `--submission-tar`.

## Tier-1 bucketing and structured `trace_artifacts`

When a run yields `ATTACKER_WON` or `NEEDS_HUMAN_REVIEW`, the defender computes
two complementary outputs strictly from defender-side observations:

1. **Maintainable Tier-1 `dedup` (`RT-<KIND>-<12hex>` or `RT-ESC-<12hex>`):**
   Hashed directly from **already-structured defender outputs**—`scenario_kind`,
   `oracle_fault_class` / tier / scenario check ID (or `"sandbox_escape"`),
   and sorted receipt/audit/inspect anomaly tags—paired with a normalized
   `witness_hash` over code/proof files (explicitly excluding `manifest.json`
   and E2 `incorrectness/claim.md` prose). Downstream semantic clustering uses
   `trace_artifacts` rather than source lexers or MIR AST alpha-renamers in
   `dedup.py`.
2. **Structured `trace_artifacts`:** Compact, public-safe defender diagnostics
   (`verify_summary`, `inspect_summary`, `audit_summary`, `capture_summary`,
   `code_oracle_diagnostic`, `tool_stderr_snippet`, `sandbox_escape`,
   `attacker_provenance_sha256`, `mir_excerpt`, `spec_preflight_output`,
   `incorrectness_patch_diff`, `preservation_canary_summary`,
   `incorrectness_proof_audit`, and `incorrectness_claim`) with ephemeral host
   directory prefixes stripped.

## Local usage

Evaluate a candidate submission directory or `.tar.gz`:

```bash
# Evaluate a candidate submission locally against s1a_ub_proof_hack
(cd anneal && python3 -B ci/redteam/harness.py evaluate \
  --scenario s1a_ub_proof_hack \
  --submission-dir /path/to/submission \
  --json-out /tmp/redteam-receipt.json)
```

Replay a saved winning witness (`replay-tripwires`) to confirm reproducibility
or verify that a fix blocks the exploit:

```bash
# Replay a stored witness and emit verification JSON
(cd anneal && python3 -B ci/redteam/harness.py replay-tripwires \
  --scenario s1a_ub_proof_hack \
  --submission-dir /path/to/witness \
  --json-out /tmp/redteam-replay.json)
```

Run the unit, containment, calibration, deduplication, and smoke tests:

```bash
# Run red-team harness test suite
(cd anneal && python3 -I -B -m unittest discover -s ci/redteam -v)
```

Related docs:
- [Workspace composition and role binding](workspace-composition.md)
- [Trust model](trust-model.md)
- [Elaborator containment design](elaborator-containment-design.md)
- [Build systems and receipts](build-systems-and-receipts.md)
