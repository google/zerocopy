<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Workspace Composition and Role Binding

`cargo anneal verify` composes Rust source inputs, captured MIR artifacts,
installed semantics and theory modules, generated claim modules, and authored
Lean files inside an isolated temporary workspace before running elaborator
containment (`ExecSeal`) and fresh kernel replay (`TrustedBoundary`
`targetAudit`).

> [!NOTE]
> Earlier design documents ([architecture](architecture.md),
> [design](design.md), and [trust model](trust-model.md)) refer informally to
> `Mir.lean` as the captured MIR module. The shipped pipeline generates
> `capture/Captured.lean` (defining `Captured.program`), optional
> `capture/Captured/Shard_NNN.lean` modules, and `generated/Expected.lean`
> (defining `Expected.claim`).

## Entrypoints and canonical request assembly

Two CLI frontends in `trusted/cargo-anneal/src/verify.rs` normalize into the
same `Request` (`schema_version = 1`):

1. **Explicit request (`cargo anneal verify --request path/to/request.json`):**
   - `compilation`: `source_root`, `crate_root`, `crate_name`, `crate_type`
     (`lib` or `bin`), `panic` (`unwind` or `abort`), `overflow_checks`
     (boolean), `edition` (`2024` default), `target` (`x86_64-unknown-linux-gnu`
     default), `cfg`, `env`, `source_files`, and optional `stdlib_crate`
     (selected-unit scope only; incompatible with `--allow-unstable-feature`).
   - `scope`:
     - `{"kind": "crate"}` — whole-crate obligation (`crate_verified`); or
     - `{"kind": "selected_unit", "roots": [...], "instantiations": [...]}` —
       selected-unit obligation (`selected_unit_verified`).
   - `proof`: `source_root`, `specification` (`"Spec.specs"` default), `theorem`
     (`"Proof.verify"` default), optional `specification_module` and
     `theorem_module`, and `sources` listing `{module, path, role}` entries
     with `role` in `{"specification", "proof"}`.

2. **Cargo manifest shortcut (`--manifest-path Cargo.toml --proof-dir <dir>`):**
   - Inspects Cargo metadata for a single primary `lib` or `bin` target without
     active normal/build dependencies, build scripts, proc-macros,
     `rust-toolchain{,.toml}` overrides, or non-allowlisted `.cargo/config`
     tables.
   - Stages `.rs` files under the package root (excluding `target/`, hidden
     entries, non-primary targets, and top-level `tests/`, `benches/`, and
     `examples/` unless `crate_root` resides there).
   - Selects `{"kind": "crate"}` unless `--select` or `--instantiate` is passed,
     in which case it emits `{"kind": "selected_unit", ...}`.
   - Walks `--proof-dir` for `*.lean` files: module `Spec` and `Spec.*` receive
     role `specification`; every other Lean module receives role `proof`.
     `specification` defaults to `Spec.specs` and `theorem` to `Proof.verify`.

Both frontends enforce strict regular-file Staging (`declared_file`) with zero
symlink traversal and verify `--receipt-out` aliasing before invalidating any
prior receipt file on disk.

## Ephemeral workspace layout and ownership

During execution, `cargo-anneal` materializes an isolated working tree (`work/`)
partitioned strictly between **tool/defender-owned** artifacts and
**authored/untrusted** modules:

```text
work/
├── request.json                  # Canonical pretty-printed Request (request_sha256)
├── rust/<source_files...>        # Read-only Rust source snapshot verified against capture
├── capture/
│   ├── capture.json              # Capture Schema v5 receipt (PINNED_RUSTC_COMMIT + scope)
│   ├── Captured.lean             # TargetRole::Capture (defines Captured.program)
│   ├── capture_shards.json       # Present iff bodies > --shard-min-bodies
│   └── Captured/Shard_NNN.lean   # TargetRole::Capture shard modules (sharded captures)
├── anneal/
│   ├── Trusted/.../*.lean        # Embedded model bundle (TargetRole::Model)
│   └── Anneal/.../*.lean         # Embedded theory bundle (TargetRole::Proof)
├── authored/<Module>.lean        # User/attacker Lean files (Specification or Proof)
├── generated/
│   ├── Expected.lean             # Tool-generated TargetRole::Expected claim bridge
│   └── Proof/IdTree.lean         # Tool-generated TargetRole::Proof index (sharded only)
└── audit-request.json            # Serialized TargetAuditRequest sent to anneal-audit
```

### Reserved module roots

Authored Lean sources in `proof.sources` cannot declare any module whose top
component is reserved for generated or trusted artifacts
(`reserved_proof_module` in `verify.rs`):

`Captured`, `Expected`, `Trusted`, `Anneal`, `Init`, `Std`, `Lean`, `Lake`,
`TrustedBoundary`, `SpecPreflight`.

Embedded `Anneal.*` theory libraries shipped inside the `cargo-anneal` bundle
are assigned `TargetRole::Proof`, never `TargetRole::Model` or
`TargetRole::Specification`, so bundled tactics/helpers undergo fresh kernel
replay alongside authored proofs without widening the model or specification.

## Connecting `scope`, `mir_profile_version`, `Spec`, and `Expected.claim`

`cargo-anneal` generates `generated/Expected.lean` exclusively from validated
kernel identifiers (using `module\nprelude\npublic import ...` when both
`Captured.lean` and the specification module start with `module`, otherwise
`prelude\nimport ...`):

```lean
namespace Expected
def claim : Prop :=
  _root_.Trusted.MirSemantics.<RootTheorem>
    (_root_.Trusted.MirSemantics.<CrateCtor>.mk
      _root_.Captured.program
      _root_.<specification>)
end Expected
```

The root proposition and receipt status depend only on
`(scope, mir_profile_version)`:

| `scope.kind` | `mir_profile_version` | Canonical `<RootTheorem>` | `<CrateCtor>` | Untainted Receipt `status` |
| :--- | :--- | :--- | :--- | :--- |
| `crate` | `1` | `CrateTheorem` | `Crate` | `crate_verified` |
| `crate` | `2` | `CrateTheoremV2` | `CrateV2` | `crate_verified` |
| `selected_unit` | `1` | `UnitTheorem` | `Crate` | `selected_unit_verified` |
| `selected_unit` | `2` | `UnitTheoremV2` | `CrateV2` | `selected_unit_verified` |

`TrustedBoundary` `targetAudit` (invoked by `cargo anneal verify` under
`ExecSeal`) validates:
1. Dependency edges obey `TargetRole.allows`:
   - `Model` -> `Model`;
   - `Specification` -> `Model | Specification` (transitively free of `Lean.*`,
     effectful/meta constants, `sorryAx`, and opaque specs);
   - `Capture` -> `Model | Capture`;
   - `Expected` -> `Model | Specification | Capture | Expected` (never `Proof`);
   - `Proof` -> all roles.
2. Fresh kernel `isDefEq` confirms `Expected.claim ≡ canonicalRoot (...)` and
   `<theorem>.type ≡ Expected.claim`.
3. Receipt v3 binds `request_sha256`, `capture_sha256`, `model_manifest_sha256`,
   and `specification_manifest_sha256`.

## Automated red-teaming composition contract

In [automated red-teaming](red-teaming.md), the defender harness locks every
workspace input outside the active scenario's `allowed_paths` (`Cargo.toml`,
synthesized `request.json`, `Spec.lean` / `src/` / `Proof.lean` when defender-
fixed, `Trusted.*`, `Expected.lean`, and `capture/`), keeping pre-run SHA-256
inventories strictly in defender-private memory:

| Scenario | Defender-fixed inputs | Attacker-supplied slots | Bound `Expected.claim` / audit target |
| :--- | :--- | :--- | :--- |
| `s1a_ub_proof_hack` | `src/lib.rs` (UB fn), `Spec.lean`, `request.json` | `Proof/*.lean` | `UnitTheorem` over defender `Captured.program` + defender `Spec.specs` |
| `s1b_spec_violation_proof_hack` | `src/lib.rs` (`wrong_const`), `Spec.lean`, `request.json` | `Proof/*.lean` | `UnitTheorem` over defender `Captured.program` + defender `Spec.returnsZero` |
| `s2_code_and_proof_hack` | `Cargo.toml`, `Spec.lean` (`targetSpec`), `request.json` | `src/**/*.rs`, `Proof/*.lean`, optional `witness.json` | `CrateTheorem` over attacker `Captured.program` + defender `Spec.specs` |
| `s3_spec_preflight_hack` | `src/lib.rs` (`wrong_const`), `Proof.lean`, `request.json` | `Spec.lean` / `Spec/*.lean` | `UnitTheorem` over defender `Captured.program` + attacker `Spec.specs` tested against fixed `Proof.verify` |
| `s4_theory_audit_hack` | `anneal/{Cargo.*,flake.*,trusted,tests,tools,vendor,correspondence}/` | `theory/**/*.lean` | Pass-1 `anneal-audit --json` over defender TCB + attacker `theory/` overlay |
