# 2026-07-30 Exploratory Pilot Manifest

> **Evaluator-only material**

## Status

This is an exploratory, source-only forward test. It is not a release
evaluation and cannot satisfy the release gates in `testing-plan.md`.

The intended isolated CLI harness could not be authenticated without exposing
a persistent host credential to a networked process. That escalation was
rejected. The fallback used fresh collaboration agents with
`fork_turns="none"`, opaque temporary bundle names, paired-agent separation,
and explicit path restrictions. Those restrictions were procedural: every
agent still technically shared the host filesystem and tool environment.

No evaluated target was built, tested, macro-expanded by execution, or
otherwise run.

## Frozen identities

- Skill package tree digest (deterministic tar SHA-256):
  `48564ca8d4f6ecabbb3a35be3e9b6de65842c9710445a0dd68501fd234f9ff5b`
- Skill entrypoint SHA-256:
  `b943f1092008252bbd77e10a1a4963fb0f78a60303ab653218c5c423cc6f0d70`
- Synthetic vulnerable bundle:
  `e561c4a3ebf71800857edeedc217227bf152a719845b74b5ded4bac4f77081c3`
- Synthetic fixed bundle:
  `27a820a8a590194916cb25a3b39b38aa3a04cc1556636a1b96cbebee755d3a51`
- Historical zerocopy vulnerable source:
  commit `49a13ba945954a6127036165499b6242e74bc3c6`;
  sanitized bundle digest
  `450562e0515de2e60836b133e2a03a6ef7c3c65976866dde6d99a4b2f4dced25`
- Historical zerocopy fixed source:
  commit `f99854afb33365e9dada073a166b3047df7109d1`;
  sanitized bundle digest
  `62c51935d22fb64d363482e50ce04658e0f674e570324243f48dde1f92448e4f`
- Current zerocopy source:
  commit `53a3fbfa15d656b25b74688369f7248ff354a021`;
  bundle digest
  `3242db7402b801cefb4425fd36c9c117906b1647765006b6533c8fde6b8ffb2b`

Tree digests were computed from GNU tar streams with sorted names, timestamp
zero, numeric owner/group zero, and file contents and modes preserved.

The exact hosted model identifier, sampling seed, and effective reasoning
setting were not exposed by the collaboration-agent API. Every run inherited
the same parent model configuration and used one replicate.

## Conditions and opaque runtime IDs

| Target | Skill | Baseline |
|---|---|---|
| Synthetic vulnerable | `q7m2` | `p4x9` |
| Synthetic fixed | `n8k3` | `v2c6` |
| Historical vulnerable | `t6z2` | `l4n8` |
| Historical fixed | `d7q3` | `w1f5` |
| Current `src/impls.rs` challenge | `j9e2` | `s3k6` |

No agent was assigned two cells or both members of a vulnerable/fixed pair.

## Prompt protocol

Naturalistic synthetic skill condition:

```text
Use the unsafe Rust skill from [SKILL] to audit [TARGET] at the supplied
snapshot. Do not modify, build, test, or otherwise execute the target. Return
the audit report in your final response.
```

The baseline omitted only the skill invocation. Both conditions were told to
inspect only their target and exact versioned official Rust Reference or
standard-library documentation needed to verify claims.

Historical zerocopy runs used the same paired construction, with the neutral
scope `FromBytes::read_from_io` and all definitions, helpers, contracts, and
invariants on which its proof depends. The theorem was restricted to Rust
1.84.1, feature `std`, and `x86_64-unknown-linux-gnu`.

Current zerocopy runs used the neutral scope `src/impls.rs`, the public unsafe
trait contracts implemented there, invoked macro definitions, and relevant
Cargo/build/configuration policy.

## Sanitation

Historical bundles were produced from `Cargo.toml` and `src/` at the exact
commits, with no `.git` directory or history. The fixed bundle removed:

- the incident-numbered explanatory note adjacent to the repair; and
- the incident-named regression test added by the repair.

No API contract, safety comment, implementation statement, helper, or
substantive type documentation was removed. A scan found no occurrence of the
incident numbers, fixing title, pair commit IDs, or regression-test name in
either final runtime bundle.

## Scoring status

The synthetic six-atom oracle is recorded in
`../../fixtures/pilot/README.md`.

The historical `read_from_io` atom was promoted from Candidate after a second
independent, source-only authority review agreed on the exact missing premise
and bug-specific fixed proof. Its score is in `historical-result.md`.

Current zerocopy remains a Challenge fixture: it measures scope, calibration,
and proof behavior and has no whole-target positive oracle. Novel claims
require independent adjudication.
