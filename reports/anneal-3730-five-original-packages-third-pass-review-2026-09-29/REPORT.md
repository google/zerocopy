# Third-pass review of five original #3730/#3731 report packages

## Review point and integrity

This review covers the five original packages after the prior second-pass review, starting from checkout HEAD `75fa78c1b623ab8db9d9acb4f31ec7958bfb9110` on 2026-09-29. It is a source, evidence, and checker review. `support/manifest.json` pins the 28 current files, the prior review record and checker, and the prior report narrative. Run `python3 support/check.py` to verify these pins and replay all five package checkers. No package catalog or issue status was changed.

The prior review's first-pass 18 hashes and second-pass 24 hashes remain unchanged. Its revised checker compares those hashes with Git blobs at `df4f6d6c84f936489c01edfa5ff19b2ee005f4d0` and `c89f1410d4f1cfbd9b654ea5268b38f5c81e115e` respectively, when local Git history is present. A separate `third_pass.files_sha256` section records current files. This avoids treating a historical digest as the current digest after legitimate later edits.

## Dispositions

| Package | Third-pass finding |
| --- | --- |
| `aeneas-concurrent-generation-determinism-nightly-2026-06-03` | **Supplementary process probe added.** `support/simultaneous-transcript.json` records four independent-output children and three shared-output children observed alive after each group's final spawn. All seven returned 0. The four independent inventories match, and the final shared inventory has the same file hashes. `support/simultaneous_probe.py` and the package checker retain and verify this narrower, actual simultaneity observation. The result covers the pinned Aeneas binary, input, flags, and bounded seven processes. |
| `anneal-3730-3731-coverage-audit-2026-09-29` | **No change.** Its checker and source counts remain valid: 159 base investigations, 64 scope extensions, 174 crosswalk rows, and 41 partial new-evidence rows. This is a dated initial snapshot; later audits supersede its status ledger. No further experiment is warranted within that historical snapshot. |
| `anneal-interactive-model-probes-2026-09-29` | **Finite schedule gap added.** `support/supersession-gap.json` enumerates 10 valid orders between A staging/publication and B request/staging/publication. Advancing the desired token only when B stages admits stale A in 2 orders; advancing at B request admits 0. The checker replays the enumeration. The report now scopes APFS publication evidence to the local filesystem fixture; it does not infer global scheduler correctness from that probe. |
| `lean-same-server-dependency-generation-v4-30-0-rc2` | **Fixture identity corrected.** The earlier claimed zerocopy source revision did not contain this direct Lean server fixture. The report now identifies its own `support/probe.py` by SHA-256 `6ece16cbce20da90f037379274c4707002133d5459c1740c6c7403f642b17744`, which its checker verifies. No additional Lean run was needed. |
| `lean-import-refresh-cross-version-v4-29-to-v4-30-rc2` | **Checker strengthened.** The retained summary goals must now correspond to goal responses in the protocol event stream from one server PID for each transcript. Both pinned-version transcripts pass. No new Lean run was needed. |

## Limits

The Aeneas probe establishes simultaneous liveness at a sampled point, not a concurrency scaling limit. The finite request-to-stage model establishes its stated interleavings and token behavior, not an implementation proof. The Lean packages remain direct-server fixture results under their pinned toolchains. Later item-level audits track broader product and environment gates.
