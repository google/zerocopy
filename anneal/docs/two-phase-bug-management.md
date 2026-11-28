<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Two-Phase Soundness Bug Management

When differential testing, fuzzing, red-teaming, or correspondence audits
uncover a soundness defect in Anneal's capture, MIR semantics, or TCB
auditing, landing a permanent root-cause fix (`Trusted.MirSemantics`,
correspondence proofs, and `check_guard_mutation.py` refutations) can take days.
Leaving the soundness hole open on `main` in the meantime risks admitting
unsound code.

Anneal separates emergency containment from permanent fixes using a
mechanically checked **Phase 0 -> Phase 1** workflow:

1. **Phase 0 (Fail-Closed Containment Tripwire):** Narrow capture, execution,
   or admission strictly monotonically so affected inputs fail closed (for
   example `status: "unsupported"` emitting `[PHASE0_TRIPWIRE:<bug_id>]` in
   capture, or `.fault .unsupported` at runtime) without altering semantics on
   surviving inputs.
2. **Phase 1 (Root-Cause Fix, Cleanup & Test Flip):** Land the permanent fix,
   correspondence updates, and guard-mutation coverage, completely delete the
   Phase-0 tripwire (zero commented or disabled stubs), and flip the bound
   regression test to positive verification or `FaultUb` parity.

## Canonical bug ID namespaces

Every Phase-0 tripwire and tracked record uses one of five canonical formats
validated by `^(?:ITREE|DIFF|RT|LMIRI|MINIRUST)-[A-Z][A-Z0-9_]*-[0-9a-f]{12}$`:

- `ITREE-<CATEGORY>-<12hex>` — observable-trace differential fuzzing
  ([differential bug guide][itree-doc]).
- `DIFF-<CATEGORY>-<12hex>` — standalone differential harnesses outside
  `itree_diff` ([differential bug guide][itree-doc]).
- `LMIRI-<CATEGORY>-<12hex>` — Lean-Miri correspondence or TCB gaps
  ([correspondence bug guide][corr-doc]).
- `MINIRUST-<CATEGORY>-<12hex>` — MiniRust operational/spec correspondence gaps
  ([correspondence bug guide][corr-doc]).
- `RT-<KIND>-<12hex>` — red-team containment, preflight, and proof-hack vectors
  ([red-team bug guide][rt-doc]).

## Authoritative issue tracking & private disclosure

Default rule: every non-selftest bug gets a public GitHub issue in
`google/zerocopy` titled `[anneal][<subsystem>] <BUG_ID>: <concise summary>`
with label `anneal` and a reference to its owning `[anneal][*]` subsystem
umbrella (`[anneal][mir]`, `[anneal][capture]`, `[anneal][audit]`,
`[anneal][theory]`, `[anneal][ffi-isa]`, `[anneal][specs]`, or `[anneal][ux]`):

- **Private / Embargoed Security Disclosure Exception (`issue: "embargoed"`):**
  Per `AGENTS.md` and [rustc workarounds][rustc-wa], an unvetted upstream
  compiler soundness/security defect or an exploitable `RT-*` false-receipt or
  containment-escape bug stays under **private maintainer security disclosure**
  while `main` is exposed or upstream disclosure is embargoed. Do **not** file a
  public issue or publish a minimal exploit reproducer until responsible
  disclosure completes; instead coordinate privately with maintainers, set
  `issue: "embargoed"` (or `issue="embargoed"` in comment markers), keep
  `scope`, `rationale`, PR text, and regression tests restricted strictly to
  neutral fail-closed invariants (without claiming upstream unsoundness or
  publishing exploit payloads), confirm guard necessity privately at Gate 5,
  and update to a public issue URL once unembargoed.
- **Pre-Triage Human Confirmation (`needs_human_review` for non-oracle `RT-*`
  reports):** Red-team reports lacking executable-oracle (`rustc`/Miri)
  confirmation—either a candidate `Trusted.MirSemantics` fix with a
  machine-checked incorrectness + canary-preservation proof, or a structured
  prose incorrectness claim—enter `needs_human_review` before triage. Humans
  confirm incorrectness first; validated candidate semantics patches seed Phase
  1 directly ([red-team bug guide][rt-doc]).
- **Opening, Deduplication & Triage (`open` -> `triaged`):** For non-embargoed
  bugs, file the public issue on `google/zerocopy` before merging Phase 0
  containment, capturing a minimal reproducible witness and collapsing
  syntactic variants onto the same root-cause issue. If a non-embargoed Phase-0
  tripwire guards an upstream compiler or toolchain defect, also anchor it with
  `RUSTC-WORKAROUND(#NNNN)` per [rustc workarounds][rustc-wa] and link the
  owning `[anneal][*]` umbrella.
- **Phase 0 PR (`mitigated_phase0`, issue stays OPEN):** Link non-embargoed
  Phase-0 PRs using **`Mitigates #<N>`** (never `Fixes #<N>`), and record the
  exact issue URL `https://github.com/google/zerocopy/issues/<N>` (or
  `"embargoed"` under coordinated private disclosure) in the tripwire's `issue:`
  field. `check_phase0_tripwires.py` rejects active tripwires lacking either a
  valid public issue URL or `"embargoed"` and requires a live Cargo negative
  regression test executed by CI (`anneal/tests/<crate>/tests/*.rs`, or
  `anneal/ci/test_*.py` for comment/runtime rules) asserting
  `[PHASE0_TRIPWIRE:<bug_id>]` refusal.
- **Phase 1 PR (`fixed`, closes `#<N>`):** Only after deleting the tripwire,
  flipping the regression test off `[PHASE0_TRIPWIRE:<bug_id>]`, and replaying
  all retained duplicate witnesses cleanly on the un-tripwired Phase-1 tree,
  close `#<N>` with **`Fixes #<N>`** (or retire the private security tracker for
  embargoed issues). Any surviving witness that still fails Phase-1 verification
  opens a distinct `[anneal][...]` issue instead of closing `#<N>`.

## Setup & teardown runbooks

### Runbook A: Static `rustc-capture` tripwire (`tripwires.rs`)

Default Phase-0 mechanism. Hooks `check_crate` and `check_mir_body` in
[`capture.rs`][capture-rs] inspect crate flags and raw `&mir::Body<'_>` before
IR extraction. Leaving `ACTIVE_PHASE0_TRIPWIRES` empty incurs zero production
change; `SYNTHETIC_DEMO_TRIPWIRE` (`ITREE-DEMO-000000000001`) and
`SYNTHETIC_DEMO_CRATE_TRIPWIRE` (`ITREE-DEMO_CRATE-000000000001`) activate
only on explicit `--env ANNEAL_PHASE0_TRIPWIRE_SELFTEST=...` in
[selftest integration tests][phase0-tests].

**Phase 0 Setup checklist:**

1. Open public issue `#<N>` in `google/zerocopy` (`[anneal][<subsys>] <BUG_ID>`)
   and allocate `<BUG_ID>` (or use `issue: "embargoed"` with neutral
   fail-closed rationale under coordinated private security disclosure).
2. Edit only between `// === PHASE 0 MUTABLE REGISTRY START ===` and `END` in
   [`tripwires.rs`][tripwires-rs] to add a `PHASE0_TRIPWIRE!` entry with
   `issue: "https://github.com/google/zerocopy/issues/<N>"` (or
   `"embargoed"`) and `activation: TripwireActivation::Always`. Keep the macro
   definition, `SYNTHETIC_DEMO_TRIPWIRE`, `check_crate`, `check_mir_body`, and
   `#[cfg(test)]` unchanged.
3. Add a dedicated negative Cargo integration test under
   `anneal/tests/{rustc-capture,itree_diff}/tests/*.rs` matching `*phase0*` or
   `*tripwire*` (`#[test]`, never `#[ignore]`) asserting both
   `[PHASE0_TRIPWIRE:<BUG_ID>]` and refusal (`unsupported` / error exit).
4. Verify locally via `check_phase0_tripwires.py --mode tree`,
   `--mode phase0-diff --base origin/main --head HEAD`, and targeted
   `anneal-rustc-capture` tests, then open a PR with `Mitigates #<N>`.

**Phase 1 Teardown checklist:**

1. Land the permanent root-cause fix (`rustc-capture` / `Trusted.MirSemantics`).
2. Delete the `PHASE0_TRIPWIRE!` rule and any helper predicates completely from
   [`tripwires.rs`][tripwires-rs] (zero commented-out or disabled stubs).
3. Keep the regression test function at the exact `regression_test` path::fn,
   flipping it from `[PHASE0_TRIPWIRE:<BUG_ID>]` refusal to positive
   verification or `FaultUb` parity, and replay all retained duplicate
   witnesses cleanly.
4. Run `--mode phase1-cleanup --base <phase0_head> --head HEAD`, confirm zero
   residual `<BUG_ID>` references across `anneal/trusted/`, and merge with
   `Fixes #<N>`.

### Runbook B: Dynamic `Trusted.MirSemantics` fallback (`.fault .unsupported`)

Fallback mechanism used **only** when a static MIR-shape predicate in
`tripwires.rs` would reject unrelated valid proof crates too broadly.

**Phase 0 Setup checklist:**

1. Document why `tripwires.rs` is over-broad in `#<N>` (`Mitigates #<N>`).
2. Add the narrow runtime check returning `StepResult.fault .unsupported` in
   [`Trusted/MirSemantics/`][mir-semantics] (`Boundary.lean`'s
   `WellFormed[V2]` quantifies universally over all `FaultKind` values, so
   converting an unsound step to `.fault .unsupported` remains sound on
   surviving runs). Annotate immediately above with:
   ```lean
   -- PHASE0_TRIPWIRE(
   --   bug_id="...",
   --   issue="https://github.com/google/zerocopy/issues/<N>",
   --   owner="...", added_date="YYYY-MM-DD", scope="...", rationale="...",
   --   regression_test="anneal/tests/.../phase0_...::fn")
   ```
3. Add a dedicated negative regression test asserting `.fault .unsupported`
   refusal (`FaultKind.unsupported`, which carries no runtime string payload)
   and tagging `<BUG_ID>` in the assertion failure context.
4. Check downstream TCB impacts (`trusted/root-manifest.sha256`,
   [`check_guard_mutation.py`][guard-mut], `correspondence/`,
   `cargo test -p anneal-audit-tests`), audit with
   `--mode phase0-diff --allow-runtime-semantics-fallback`, and complete full
   Pass 2 semantic review before merge (`isolated_tripwire_surface = false`).

**Phase 1 Teardown checklist:**

1. Replace the `.fault .unsupported` guard with the real operational rule and
   delete the `-- PHASE0_TRIPWIRE(...)` comment and any bug-ID mentions across
   all of `anneal/trusted/`.
2. Update [`MirCorrespondence`][corr-doc] / `MiniRust` proofs, add a negative
   refutation theorem + guard entry to [`check_guard_mutation.py`][guard-mut],
   and refresh `trusted/root-manifest.sha256` if tracked manifests change.
3. Flip the bound regression test to positive / `FaultUb` parity, replay
   retained witnesses, pass `--mode phase1-cleanup`, and land with `Fixes #<N>`.

*(For pure proof, preflight, or sandbox escapes where `rustc-capture` is not the
right layer, see [Red-team & TCB containment escapes][rt-doc].)*

## CI enforcement & local Git-history tools

[`check_phase0_tripwires.py`][tripwire-ci] (covered by
[`test_check_phase0_tripwires.py`][tripwire-ci-tests]) provides three modes:

- **`--mode tree` (runs automatically in CI):** Wired into `anneal-ci-tests`
  via [`run_anneal_check.sh`][run-check] (`ci-tests`) alongside
  `test_check_phase0_tripwires.py`. Validates every `PHASE0_TRIPWIRE!` and
  comment marker across `anneal/trusted/**/*.{rs,lean}`, public GitHub `issue`
  URLs (or `"embargoed"` under private disclosure), unique canonical IDs, ISO
  dates, live active/non-comment negative test assertions on Cargo or CI
  `unittest` targets, and absence of raw `Phase0Tripwire` structs, split
  `#[cfg(test)]` decoys, or commented/disabled stubs.
- **`--mode phase0-diff` (local pre-PR Git-history check):** Compares immutable
  `--base` and `--head` Git trees (not run in `ci-core`, whose sandbox omits
  `.git` history). Confirms changes stay inside `tripwires.rs`'s mutable
  registry plus dedicated `*phase0*`/`*tripwire*` Cargo tests or
  `anneal/ci/test_phase0_*.py` suites unless
  `--allow-runtime-semantics-fallback` is explicitly requested. Passing this
  check measures diff isolation only and never waives `AGENTS.md` Pass 1 /
  Pass 2 `trust-review` gates.
- **`--mode phase1-cleanup` (local pre-PR Git-history check):** Confirms every
  removed or resolved bug ID leaves zero residual `PHASE0_TRIPWIRE` or bug-ID
  tokens anywhere in `anneal/trusted/**/*.{rs,lean}` at `--head` while keeping
  the bound regression test active and flipped off refusal.

### Scope & threat model

[`check_phase0_tripwires.py`][tripwire-ci] is a **structural CI hygiene lint**,
not a soundness boundary or an adversarial malware sandbox. Its job is to catch
accidental omissions, malformed metadata, disabled tests, stale markers or
helpers, and obvious vacuous stubs in contributor-authored PRs before review.

It does **not** attempt to decide arbitrary runtime behavior or defeat
intentionally malicious, self-modifying, or obfuscated test code executed by CI
(for example, overwriting Cargo-built binaries on disk via `std::fs::write`,
replacing `sys.modules["unittest"]` at import time, wrapping assertions in a
custom `__exit__`-swallowing context manager, hiding a Phase-0 witness behind
`std::hint::black_box(false)`, or crafting deliberate local-binding identifier
collisions in trusted Lean or Rust code). Defending against intentionally
adversarial or deceptive test implementations is enforced by Gate 1 review,
Gate 2 cross-family code review, Gate 5 maintainer approval, and hermetic
sandboxed CI execution — never by heuristic static linting alone.

[rustc-wa]: rustc-workarounds.md
[itree-doc]: bug-management/itree-and-differential.md
[corr-doc]: bug-management/correspondence-divergences.md
[rt-doc]: bug-management/redteam-and-tcb-escapes.md
[tripwires-rs]: ../trusted/rustc-capture/src/tripwires.rs
[capture-rs]: ../trusted/rustc-capture/src/capture.rs
[phase0-tests]: ../tests/rustc-capture/tests/phase0_tripwires.rs
[mir-semantics]: ../trusted/lean/Trusted/MirSemantics/Boundary.lean
[guard-mut]: ../ci/check_guard_mutation.py
[tripwire-ci]: ../ci/check_phase0_tripwires.py
[tripwire-ci-tests]: ../ci/test_check_phase0_tripwires.py
[run-check]: ../ci/run_anneal_check.sh
