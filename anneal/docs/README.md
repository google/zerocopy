<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Developing Anneal

> [!WARNING]
> **This is alpha software!** Anneal (`0.2.0-alpha`, Stage 0) is an
> experimental verifier whose TCB audit is incomplete. Today it checks only a
> small, pointer-free scalar subset of Rust without returning calls
> (`Profile v1` on `x86_64-unknown-linux-gnu`). Passing results depend on an
> intact build host (`rustc`—and any `build.rs` or proc-macro run to produce
> inputs—executes outside the Lean sandbox) and human review of stated
> specifications (the declared primary specification module, every
> `specification`-role module, and their transitive meaning dependencies),
> compilation and scope configuration, and TCB audit logs (complete
> review-surface reporting remains under active development). See
> [alpha usage](alpha.md) and the [threat model](../THREAT_MODEL.md).

The MIR-based implementation lives at [`anneal/`](../). See the
[repository layout](architecture.md#repository-layout) for the workspace
structure.

## Build and test the current toolchain

On Linux with Cargo and Nix flakes enabled, run these commands from the
Zerocopy checkout. The archive bundles the pinned Rust and Lean toolchains,
the compiler driver, and Anneal's Lean sources.

```sh
cd anneal
mkdir -p target
nix build .#omnibus-archive --out-link target/omnibus-link
XDG_CACHE_HOME="$(mktemp -d)" \
  cargo run --locked -p cargo-anneal -- setup --local-archive target/omnibus-link
```

The command uses a fresh cache because setup reuses an existing installation
for the same version key.

The [MIR verifier alpha](alpha.md) includes an end-to-end scalar example.

See the [scaffold build and testing guide](scaffolding.md) to run workspace
tests with the pinned toolchain, execute or filter `installed_smoke` cases,
check `cargo-anneal` packaging, and reproduce retained failure bundles.

To audit the checkout, use the `lean/bin/lean` under the installation path
printed by setup. The full MIR correspondence audit uses Linux bubblewrap
at `/usr/bin/bwrap`.

```sh
cargo run --locked -p anneal-audit -- \
  --lean /path/to/installed/lean/bin/lean --require-correspondence
```

## CI, releases, and review

- Zerocopy's [Anneal Tests workflow](../../.github/workflows/anneal.yml)
  calls the [current verifier checks](../../.github/workflows/anneal-current.yml).
  On `pull_request`, draft PRs skip `current_anneal` (and heavy Zerocopy jobs)
  unless labeled `run-ci`, ready Anneal-relevant PRs run `static-checks`
  unless `run-ci` opts into the full suite, and `merge_group` / `push` to
  `main` always build and install the archive, audit the trust boundary, and
  test the Rust workspace in full.
- The [release workflows](alpha.md#cut-the-release) prepare and publish
  the [Anneal alpha](alpha.md).
- The [Gate 2 review guide](codex-review.md) describes review gates and the
  standalone diagnostic evaluator.

## Documentation index

Documents below distinguish between **Current** behavior (what runs in Stage 0
alpha today) and **Target Architecture** or **Planned Interop** designs landing
incrementally.

### Governing and top-level docs

| Document | Status | Scope |
| :--- | :--- | :--- |
| [Project principles](../PRINCIPLES.md) | Current (governing) | Correctness promise and design principles. |
| [Threat model](../THREAT_MODEL.md) | Current (governing) | Adversary assumptions, bounded two-surface human review, and in-scope defenses. |
| [Meta-principles](../META_PRINCIPLES.md) | Current (governing) | Invariant goals governing principles and threat model. |
| [Agent instructions](../AGENTS.md) | Current | Contributor and AI-agent repository obligations. |

### Current developer and architecture docs

| Document | Status | Scope |
| :--- | :--- | :--- |
| [Design overview](design.md) | Current + planned | Detailed verification workflow, library-centric model, specification modes, and incremental adoption. |
| [MIR verifier alpha](alpha.md) | Current (Stage 0) | Exact Profile v1 scalar MIR subset, `verify` usage, taint flags, and alpha releases. |
| [Scaffolding and testing](scaffolding.md) | Current | Running workspace tests, `installed_smoke`, packaging checks, and failure bundles. |
| [Multi-step MIR architecture](architecture.md) | Current + planned | Three-stage MIR pipeline, repository layout, and compiler integration. |
| [Trust model and boundary enforcement](trust-model.md) | Current | The `trusted/` boundary, dependency pins, and repository CI audits. |
| [Elaborator containment and Receipt v3](elaborator-containment-design.md) | Current | Linux `ExecSeal` sandboxing, specification preflight, target replay, and Receipt v3 taint law. |
| [Performance tracking and dashboard](perf-tracking.md) | Current | Continuous benchmark collection, Tier A budgets, MAD regression checks, and the static `/bench/anneal/` dashboard pipeline. |
| [MIR correspondence design](mir-correspondence-design.md) | Current | Pass 2 correspondence anchoring `Trusted.MirSemantics` against `vendor/lean-miri/`. |
| [MIR correspondence strategy](mir-correspondence-strategy.md) | Current | Proof strategy and simulation obligations for MIR correspondence. |
| [Lean-Miri provenance](lean-miri-provenance.md) | Current | Provenance and patching policy for `vendor/lean-miri/`. |
| [Review policy design](review-policy-design.md) | Current | Contributor review rules and policy-placement structure. |
| [Gate 2 review guide](codex-review.md) | Current | Automated review gates and standalone diagnostic evaluator. |

### Target architecture and interop docs

| Document | Status | Scope |
| :--- | :--- | :--- |
| [Build systems and orthogonal Receipt v3](build-systems-and-receipts.md) | Target Architecture | Five-phase split-action contract (Cargo, Bazel, Soong, GN, Buck2), orthogonal Receipt v3, Tier 1/2 cross-crate MIR, `nominal`/`fixed-buckets=K` sharding, and Lean `module` / `v4.35.0`. |
| [Auditing and Universal NDJSON Comparator](auditing-and-comparator.md) | Target Architecture | Universal NDJSON Comparator (`5a`/`5b`/`5c`, `nanoda_bin` + `con-ron`), `check_guard_mutation.py` CI, and honest non-adversarial `audit-spec` sanity checks. |
| [Specification Core v2 and golden spec closure](spec-core-and-golden-closure.md) | Target Architecture | `FnContract` (`safetyPre`/`behaviorPre`), 8-mask `EffectMask` realizability, mutual-recursion stratification, and always-rendered golden spec closures under `CODEOWNERS`/`OWNERS`. |
| [Testing and verification architecture](testing-architecture.md) | Target Architecture | Two-zone `trusted/` vs. `tests/` isolation, `anneal-testkit` scaffolding, declarative `adversarial`/`differential`/`real_crates` corpora, performance and axiom gates, and `D1-A`–`D4-A` policy decisions. |
| [Anneal–Aeneas interop bridge](aeneas-interop-bridge.md) | Planned Interop | Opt-in zero-TCB `anneal/interop/aeneas-bridge/` architecture, strict vs. liberal `.fail` refinement, MIR prerequisites, and `read_u64` / `write_uint` / `split_at_mut` canaries. |

## Historical workspaces

The earlier [V1 verifier][v1] and [V2 prototype and toolchain][v2] are
available in the repository history with their original build instructions.

[v1]: https://github.com/google/zerocopy/tree/ec75fb464cda7b18581faa83a6a82d0dfdf422d9/anneal/v1
[v2]: https://github.com/google/zerocopy/tree/ec75fb464cda7b18581faa83a6a82d0dfdf422d9/anneal/v2
