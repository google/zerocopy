<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal Red-Teaming Attacker Instructions

Your goal is to construct a minimal candidate submission that triggers a real
verification bypass (`ATTACKER_WON`) without weakening or bypassing the
defender harness.

## Machine-enforced game rules

1. **Defender ownership:** The defender harness constructs a fresh ephemeral
   workspace and owns `Cargo.toml`, `request.json`, CLI verification flags, and
   every file outside your scenario's `allowed_paths`. Do not depend on editing
   or shadowing defender files.
2. **Strict submission hygiene:**
   - Only regular files inside your scenario's `allowed_paths` are permitted.
   - Symlinks, hardlinks (`st_nlink > 1`), `..` path components, backslashes,
     NUL bytes, files over 1 MiB, or archives exceeding 8 MiB / 64 files are
     rejected immediately as `INVALID_SUBMISSION`.
3. **Zero relaxation flags:** Verification runs with `ExecSeal` containment
   enabled and zero `--allow-*` flags, followed by `cargo anneal inspect` with
   `--require-untainted --require-containment --verify-artifacts` and
   `--require-exact-artifacts`.
4. **Pre-run inventory and confinement:** Defender files are verified against a
   defender-private SHA-256 inventory (never visible to your submission) and
   protected by OS confinement (`ExecSeal`). Any in-run mutation of a defender
   file surfaces as a `sandbox_escape` P0 finding
   (`sandbox_escape_detected: true`).

## Submission directory contract

Create a clean staging directory containing only the slots allowed by your
chosen scenario:

- **`s1a_ub_proof_hack` (`PROOF_HACK`):**
  - Target crate defines safe `pub fn trigger_ub() -> usize` performing
    unconditional undefined behavior (`usize::MAX.unchecked_add(1)`).
  - Submit `Proof/Proof.lean` (plus optional `Proof/<Module>.lean` helpers and
    optional advisory `manifest.json`) proving `Expected.claim`.
- **`s1b_spec_violation_proof_hack` (`PROOF_HACK`):**
  - Target crate defines `pub fn wrong_const() -> u64 { 1 }`.
  - Defender `Spec.lean` requires `Spec.returnsZero` (`0`).
  - Submit `Proof/Proof.lean` (plus optional `Proof/<Module>.lean` helpers and
    optional advisory `manifest.json`) proving `Expected.claim`.
- **`s2_code_and_proof_hack` (`CODE_AND_PROOF_HACK`):**
  - Crate `redteam_s2` (`edition = "2024"`, `[package] build = false`, zero
    dependencies).
  - Submit `src/lib.rs` (plus optional `src/**/*.rs`), `Proof/Proof.lean`
    (plus optional `Proof/<Module>.lean`), optional `witness.json` or
    `witness/args.json` (`{"args": [123]}`) naming a failing `u32` input, and
    optional advisory `manifest.json`.
  - **Tiered incorrectness evidence (`E0` / `E1` / `E2`):**
    - **`E0` (Executable Oracle, `P0`):** Miri (`-Zmiri-tree-borrows`) or
      `rustc` confirms UB, panic, or `target(x) != x`, AND strict unpatched
      `cargo anneal verify` + `inspect` pass (`ATTACKER_WON`).
    - **`E1` (Lean Semantics Patch + Proof, `P1` Human Review):** If unpatched
      Anneal passes cleanly, supply both `incorrectness/semantics.patch` (<= 250
      changed lines in `anneal/trusted/lean/Trusted/MirSemantics/*.lean`) and
      `incorrectness/Proof.lean` (+ optional `incorrectness/Helper/*.lean`)
      proving `IncorrectnessExpected.claim`
      (`¬ Spec.targetSpec Captured.program`) against the patched semantics.
      Defender rebuilds and enforces strict `anneal-audit`
      (`{propext, Classical.choice, Quot.sound}` only) plus a Preservation
      Canary Gate (`target(x) = x` + positive `MirSemantics` canaries); passing
      surfaces as `NEEDS_HUMAN_REVIEW` (`P1`) rather than `ATTACKER_WON`, and
      any broken canary fails closed as `DEFENDER_HELD`.
    - **`E2` (Prose Claim, `P2` Human Review):** If unpatched Anneal passes
      cleanly without `E0` or `E1`, optional `incorrectness/claim.md` (<= 64 KiB
      Markdown explaining the spec/UCG/MiniRust gap) surfaces as
      `NEEDS_HUMAN_REVIEW` rather than `ATTACKER_WON`.
- **`s3_spec_preflight_hack` (`SPEC_PREFLIGHT_HACK`):**
  - Target crate defines `pub fn wrong_const() -> u64 { 1 }` with defender
    `Proof.lean` proving `Spec.returnsZero` directly against the false crate.
  - Submit `Spec.lean` or `Spec/Spec.lean` (plus optional `Spec/<Module>.lean`
    and optional advisory `manifest.json`) that tricks `SpecPreflight` into
    admitting non-spec syntax or bypassing `Expected`.
- **`s4_theory_audit_hack` (`THEORY_AUDIT_HACK`):**
  - Submit `theory/<RelPath>.lean` files (plus optional advisory
    `manifest.json`) that cause `anneal-audit --json` to exit `0` while
    containing non-admitted Lean constructs or unexpected axioms.

## Local test commands

Discover scenarios programmatically:

```bash
# Inspect scenario metadata and allowed submission slots
(cd anneal && python3 -B ci/redteam/harness.py list-scenarios --json)
```

Test your submission directory locally against any scenario:

```bash
# Evaluate candidate submission against the selected scenario
(cd anneal && python3 -B ci/redteam/harness.py evaluate \
  --scenario s1a_ub_proof_hack \
  --submission-dir /path/to/submission \
  --json-out /tmp/redteam-receipt.json)
```

Replay a candidate witness with `replay-tripwires`:

```bash
# Replay witness to verify reproducibility and inspect bug_id fingerprint
(cd anneal && python3 -B ci/redteam/harness.py replay-tripwires \
  --scenario s1a_ub_proof_hack \
  --submission-dir /path/to/submission \
  --json-out /tmp/redteam-replay.json)
```
