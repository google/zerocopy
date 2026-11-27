<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# `anneal-obligations`: a per-function evidence ledger

`cargo anneal-obligations` lists every function it learns about from its
inputs, with one evidence tier per function, and can fail CI when evidence
regresses. It is an untrusted reporting tool. It re-checks no proof and does
not validate receipt integrity, so first validate each receipt with
`cargo anneal inspect`, whose default mode rejects tainted, failing, or
malformed receipts unless told otherwise.

```sh
cargo run -p anneal-obligations -- \
  --receipt receipt.json --request request.json \
  --spec-src-root src --spec lib.rs --spec util/mod.rs
```

Once installed (`cargo install --path obligations`), Cargo also runs the
binary as `cargo anneal-obligations`.

## Inputs

| Flag | Input | What it contributes |
| :--- | :--- | :--- |
| `--receipt FILE` | Receipt Schema v3 JSON from `cargo anneal verify --format json` or `--receipt-out` | Every function and associated function with a body in the compiler census; for a verified receipt, a proof of the functions it selects |
| `--request FILE` | A `cargo anneal verify` `request.json` | A stated specification for each selected-unit `scope.roots` entry, for the function each zero-argument `scope.instantiations` entry names, and for the generic function of each other `scope.instantiations` entry and the instances it produces |
| `--spec FILE` | Rust sources with `anneal::spec` attributes or `anneal::external_spec!` blocks (relative to `--spec-src-root DIR` if given, as for `anneal-spec-lower --src-root`) | A stated specification for each target |

Every receipt and request must be for the same crate, and for `--crate NAME`
when given. An item's ID is `rust-path-v1::` followed by its census path,
which is the path that request roots and `anneal-spec` targets use. Closures,
constants, statics, and bodiless declarations are not listed. Repeating an
input has no effect.

A `scope.instantiations` entry with no generic arguments names a non-generic
function, such as `<impl KnownLayout for u8>::m`. Capture selects it under its
census path, so the ledger treats it like a `scope.roots` entry.

A body that a receipt verifies through an entry with generic arguments is its
own item, named by the instance path that the receipt records, such as
`f::<u8>`: a proof of one instance says nothing about the others. The generic
function itself stays `deferred`, since its request states a specification
only for the listed instances. The request's contract applies to each instance
that a receipt selects through an entry the request also lists (the same path
and arguments), so the instance needs a verified receipt for that request, as
a root does. The ledger cannot print instance paths itself, so when several
entries for one function could have produced an instance, a request listing
any of them states a contract for it; this can leave an instance `deferred`
but never proves one. An instance that no receipt selects is not listed.

## Tiers

Tiers are ordered from weakest to strongest; `--ratchet` treats a move down
this list as a regression.

| Tier | Meaning |
| :--- | :--- |
| `uncontracted` | In a receipt census, with no stated specification. |
| `deferred` | Has a stated specification, but no input supplies a complete verified proof. A receipt leaves its functions here, with the reasons listed, when its proof uses `sorry` (`sorry_in_proof`) or an axiom outside `propext`, `Quot.sound`, and `Classical.choice` (`nonfoundation_axiom:<name>`), or when its audit did not replay the proof in the kernel (`no_kernel_replay`), did not match the theorem's type exactly (`inexact_theorem_type`), or names an `audit.canonicalRoot` that is not a known Profile v1 or v2 theorem (`unrecognized_canonical_root`). A receipt whose `audit.canonicalRoot` is the theorem for the other `scope.kind` is rejected. |
| `assumed` | A `proven_conditional` function under `--audit-assumptions`. |
| `runtime_checked`, `checked_fuzz`, `envelope_minted` | Reserved for runtime checks, fuzzed runtime checks, and verified validators. No input format produces them yet, so the ledger never reports them; baselines may name them. |
| `proven_conditional` | Selected by a verified receipt that discloses at least one condition (below). |
| `proven_closed` | Selected by a verified receipt that discloses no condition. |

When `--request` or `--spec` states specifications for a function, every stated
contract on that function must be discharged by a verified receipt bound to it
(`request_sha256` for a request, or `specification_manifest_sha256` of the
lowered specification module for `--spec`); otherwise the function stays
`deferred`. Within a single contract (or when no contracts are stated), a
function selected by several receipts takes the strongest single receipt's tier
and conditions so conditions from alternative proofs of one obligation are
never combined; across distinct stated contracts on one function, the function
takes the weakest contract's tier and the union of each contract's strongest
proof's conditions.

## Conditions

These conditions make a proof `proven_conditional`. Several correspond to
`DisclosedGap` constructors in `Trusted.Framework`, which the receipt does
not list directly.

| Condition | Receipt signal |
| :--- | :--- |
| `selected_unit_scope` | `scope.kind` is `selected_unit` (`DisclosedGap.selectedUnitScope`). |
| `unbridged_semantics`, `caller_memory_thread_isolation` | `audit.canonicalRoot` is a Profile v2 theorem, whose model discloses `unbridgedSemantics "mir_profile_v2"` and `callerMemoryThreadIsolation` on every result. |
| `correspondence_not_bound` | `correspondence_provenance.applicable` is false on a Profile v1 receipt, so the receipt binds no correspondence evidence (a pinned run leaves it to the repository's `anneal-audit --require-correspondence` check). |
| `candidate_tier_model` | `experimental` is true: the theorem depends on candidate-tier trusted modules. |
| `taint:<atom>` | Each `taint_reasons` atom other than `sorry_in_proof`. |
| `tcb_shim:<status>:<id>` | Each `tcb_shims` entry whose status is not `proved`. |
| `correspondence_tcb_shim:<status>:<id>`, `correspondence_taint:<atom>` | The same, for `correspondence_provenance.tcb_shims` and `correspondence_provenance.taint_reasons`. |
| `bounded_horizon:<k>`, `horizon:<kind>` | `horizon` is bounded by `k`, or has a kind other than `unbounded`. |
| `correspondence_scope:<kind>` | `correspondence_provenance.qualifiers.scope_kind` is not `full_gate`, such as `partial_gate`. The qualifiers' `choice_total: false` and nonempty `assumed_seams` also add `correspondence_taint:choice_total_false` and `correspondence_taint:assumed_seams_present`. |
| `correspondence_claim:<kind>` | `correspondence_provenance.claim_kind` is present and is not `exact_refines`, the strongest claim. |
| `model_system_relation:none`, `correspondence_model_system_relation:none` | `model_system_relation.kind`, or `correspondence_provenance.model_system_relation.kind`, is `none`. |
| `spec_warning:<code>` | Each warning code in `spec_warnings` or `audit.specWarnings`, such as `trivial_property` or `unsatisfiable_safety`. The anti-vacuity lint does not block verification, so a specification weakened to `True` still verifies. |
| `spec_lint_not_run` | The receipt has no `spec_warnings` field, as when the NDJSON comparator route skips the lint. |

Every result also rests on assumptions that apply to all functions alike,
such as faithful compiler capture and the gaps between verified MIR and the
deployed binary. The ledger does not repeat these per function; read them
from each receipt's `assumptions` and `deferred` fields.

`--audit-assumptions` reports every `proven_conditional` function as
`assumed`, so that the summary's unproven count includes every proof that
rests on a disclosed condition.

## Output

The default text output has one line per function, `<tier> <id>`, followed by
any conditions in brackets, then a summary of the counts per tier. Text output
and diagnostics escape control and bidirectional-formatting characters from
the inputs, as `\n` or `\u{1b}`, so that an input cannot forge lines or send
sequences to a terminal.
`--format json` writes an `anneal-obligations/1` document: `crate`,
`audit_assumptions`, the sorted `sources`, a `summary` with the item count,
the unproven count, and every tier's count, and `items` sorted by ID. Each
item records its `tier`, `conditions`, the receipt that supplied the tier
(`evidence`), and the requests and source files that state its specification
(`contracts`). The output depends only on the inputs, not on the order of the
flags.

## Ratchet

`--ratchet BASELINE` compares the ledger with an earlier `--format json` ledger
and exits 1 if any baseline item now has a lower tier or is missing, if a
`proven_conditional` or `assumed` item gained a condition, or if the number of
unproven items grew. A missing item counts as a regression so that omitting a
receipt cannot hide lost proofs; regenerate the baseline after deleting a
function. Build the baseline from the same kinds of inputs as the ledger it
guards: adding a receipt's census for the first time adds its uncontracted
functions to the unproven count. Ledgers for different crates, or one built with
`--audit-assumptions` and one without, are not comparable, and comparing them
exits 2.

Exit status: 0 on success, 1 on a ratchet regression, and 2 on usage, I/O, or
input errors.
