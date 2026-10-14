# Consumer-owned statements, reusable receipts, and producer containment

## Summary

Anneal can leave search, tactic execution and certificate generation untrusted only if a consumer controls the requested statement, admissible semantic environment, checking path and final verdict. Artifact identity, logical validity, source correspondence, obligation coverage and execution containment are separate gates. A cached or signed result must preserve all of them when it is reused.

A bounded native experiment establishes one containment mechanism on the observed macOS host: a restricted process could write its own output but could not overwrite a protected challenge. It does not prove an Anneal service secure, authenticate a theorem or justify its Rust meaning.

## Applicability

The execution subject is Darwin 27 arm64, `/usr/bin/sandbox-exec` SHA-256 `58839ef01b4eef8aac0d2aa8f9d1c074ae45aafe3533965b030672450064acc8`, and Python 3.14.8 executable SHA-256 `7ebde552773a4045532637b114d645a313e045ac07b26f5e520bf039f1e34063`. The owned test uses no submitted producer code. It is a write-protection probe with a minimal environment, not a confidentiality, descendant-supervision or adversarial-host audit.

The logical/loading comparison reuses substantively reviewed corpus evidence for Lean 4.34.1/comparator and Charon 0.1.210; their exact pins are in metadata. Historical cache specimens use nightly Rust 2026-05-31. These are distinct subjects. No compatibility with Anneal's4.31 library is inferred.

The design findings address T046/T049/T051–T060/T062/T091–T100, R086 and P115–P119/P123–P126 at the interfaces stated below. Verified parsing, cryptographic execution soundness, full coverage checking and representative scaling measurements require their own evidence. This is a concrete proposed acceptance design with a native containment control, not its implementation or an end-to-end Anneal theorem.

## Findings

### Fix the statement independently of the proposed proof

Basis: **source** + **execution**, reviewed Lean/comparator reports; **derived**, Anneal contract.

The consumer must select an exact program/configuration, permitted entry states, required source semantics, mandatory safety predicates and user property before evaluating a proposed certificate. The theorem type includes local hypotheses, universes, instantiated type classes and every definition affecting that type. An empty global axiom list does not establish that its local premises cover permitted Rust callers.

The inspected comparator separately compares declaration headers and used definitions, audits assumptions and replays proof objects. Its name-based axiom policy is strengthened by comparing the allowed axioms' declarations with a consumer challenge. Equality of producer-generated challenge and producer-generated solution cannot establish that either expresses the independent Rust request. Source: [comparison and replay report](../theorem-authority-and-consumer-statements-2026-10-14/REPORT.md), Findings, statement comparison and replay.

For Anneal, a canonical target can have the form `Guarantee semantics exactProgram target callerDomain requiredProperties`. Generated models, authored specifications and extraction relations become arguments or checked dependencies of this proposition, rather than permitting a generator to choose a weaker proposition. A conditional model theorem may be useful evidence while still failing this final claim.

There are two viable statement interfaces. An exact core-declaration comparator is conservative and straightforward about identity, but rejects some equivalent presentations. A checked translation/equivalence witness can accept alternate encodings, at the cost of another proved interpretation interface. Names, notation, filenames and a displayed theorem string are insufficient for either route.

### Authentication and provenance identify bytes without proving their meaning

Basis: **derived**.

A digest binds selected bytes under its collision-resistance assumption; a signature associates them with a signing authority under its authentication assumptions. Neither proves that those bytes denote the required property, that a compiler preserved semantics, or that a signer checked the right subject. A reproducible output likewise establishes an equality observation, not a source/model theorem.

Use distinct fields for input identity, semantic-library identity, theorem/assumption identity and checking evidence. Provenance can establish which producer ran on which configured inputs; correspondence must establish what its transformation preserved. A receipt that omits a target, generic instance, callee contract, model revision or checking policy is inapplicable when that omitted fact changes the claim.

Cryptographic computation receipts can authenticate a specified checker execution under additional program/circuit/cryptographic assumptions. They need a separately justified correspondence from public inputs and outputs to this acceptance proposition. This report does not examine those proof systems or assign them an unconditional trust-reduction benefit.

### Treat a receipt as evidence that must pass the current applicability rule

Basis: **derived**, proposed interface.

| Receipt component | Required consumer interpretation |
|---|---|
| Exact source and configured generated inputs | Same admitted compilation subject, including dependencies, selected units, build scripts and macros |
| Program and model representations | Same checked AST/definition meaning; encoding migrations require evidence |
| Target and caller domain | Same ABI/width/alignment and permitted inputs; a narrower domain is a different claim |
| Property and assumptions | Exact required statement and permitted local/global premise policy |
| Certificate/dependency graph | All required nodes checked, references resolved, relevant cycles justified |
| Checking path | Enabled validation, allowed evaluation policy, validated imports and binary/runtime frontier |
| Final result | All mandatory stages succeeded on that immutable subject; timeout or missing stage is incomplete |

A durable receipt may be replayable proof data, a trusted checker's attestation, or a cryptographic execution witness. These are different assurance contracts. An opaque in-process acceptance token can restrict construction to a checked path for ordinary code respecting its API. Serializing it into unrestricted data removes that construction restriction; deserialization must re-establish its proposition or invoke an explicit trusted attestation policy. Neither a private struct field nor a hash protects against arbitrary memory corruption or a compromised same-user host.

### Fresh reconstruction changes the imported-artifact boundary

Basis: **source** + **execution**, reviewed Lean/Charon reports; **derived**, design implications.

Lean 4.34.1's inspected import path reads compacted module data and constructs an environment; it does not freshly insert/check every imported proof body. It can load plugins and initialize extensions. The retained stale-source experiment imported the old compiled producer after its source changed. Axiom summaries can describe that selected artifact while failing to establish its relation to visible source. [Exact controls and source paths](../lean-admissions-imports-and-native-checking-v4-34-1/REPORT.md).

Data-only certificates followed by fresh replay can exclude producer build scripts, tactics and plugins from the checking execution. The parser, primitive interpretation, trusted bootstrap environment and serializer correspondence remain gates. Freshness means the checked artifact family and expected statement agree; it does not require rerunning the original producer.

Charon 0.1.210's inspected envelope carries version, translated crate and `has_errors`. Convenience deserializers return the crate while discarding the latter metadata; package-version equality is distinct from commit/schema/semantic identity. Its deduplication references require real reader validation. [Pinned serialization comparison](https://github.com/google/zerocopy/blob/a0ff759e7d2d9a953f0ac40b326dd23197bd9188/reports/charon-serialization-compatibility-api-0-1-210/REPORT.md). A certificate reader should reject unknown constructors, ambiguous identifiers, invalid references, integer-range violations, missing required data and incomplete extraction. A version tag or successful parse alone cannot satisfy these requirements.

### Dependency closure and compression need a semantic checking contract

Basis: **derived**.

The consumer computes the required obligation graph from its admitted program or accepts checked evidence for that graph. A producer's roster cannot silently omit callees, cleanup, vtable targets or model primitives. Every edge must identify the exact proposition and implementation it consumes. Separate logical-proof dependencies from executable dependencies: a proof can be closed while the source call graph remains incomplete.

DAG sharing and schemas reduce repeated syntax without changing this rule. A decoder can reconstruct abbreviated proof terms and submit them to a kernel, or a once-proved checker can interpret compressed derivations. The decompressor then either remains trusted or has a soundness/round-trip theorem. Unknown references and forward cycles are not ordinary shared subproofs.

Recursive program certificates are different from cyclic proof references. They require a simultaneous induction, guarded/step-indexed judgment or appropriate fixed-point theorem. Two contracts that merely assume each other's safety do not establish closure. Resource parameters and callee assumptions must remain in the root statement until a valid composition rule discharges them.

### Cache equality is neither an invalidation policy nor an upgrade proof

Basis: **execution evidence reused** + **derived**.

The historical equal-length-root Charon experiment compared source-edit/revert output with cold oracles and observed the selected bodies agree. Its report also retains a prior path-sensitive build-script counterexample from another fixture. These are specific reuse observations, not proof that any shared Cargo target is an Anneal proof cache. [Edit/revert and bounds](https://github.com/google/zerocopy/blob/a0ff759e7d2d9a953f0ac40b326dd23197bd9188/reports/anneal-3731-i080-source-edit-revert-incremental-cache-2026-09-29/REPORT.md).

An applicability key must include every fact the checked theorem depends on. Changes to source, generated inputs, configuration, selected implementations, layout, primitive definitions, imported assumptions, checker options or policy invalidate the corresponding evidence unless a checked compatibility argument explicitly permits reuse. A revert can restore identical bytes while retaining different generated environment inputs; source equality alone is insufficient.

Keep schema upgrade, semantic-model upgrade, checker implementation upgrade and policy upgrade separate. A format migration proves representation preservation; a model change needs a property-transfer relation; a checker replacement needs an implementation/acceptance argument; a policy change must re-evaluate assumptions. Reinterpreting an old certificate under new meanings is unsound unless that interpretation bridge is established.

### A native control protects the consumer challenge from one producer process

Basis: **execution**, retained probe and result.

The test profile denies network operations and file writes except in one owned producer-output directory. The producer successfully wrote `out.txt`. Its attempted write to the protected challenge raised `PermissionError` with errno 1; the challenge digest remained unchanged. The sandboxed process exited 0 and reported the two outcomes. The host's initial tool-sandbox invocation failed at `sandbox_apply` with status 71; no producer executed in that attempt. Running the same bounded test outside that enclosing restriction permitted the macOS profile to apply. The first failure is preserved separately from the successful control.

This supports the specific process/file-write boundary tested. It does not establish confidentiality, resistance to a compromised OS or another unrestricted same-user process, full descendant lifetime control, protection of every service resource, or Anneal deployment correctness. Ordinary separate directories and hashes would not provide the tested denial by themselves.

Producer containment and logical checking solve different problems. Containment protects the consumer challenge, policy, checker and acceptance record from mutation; statement comparison, proof checking and source correspondence establish the submitted claim. The consumer should copy validated data into its own immutable input and never grant a producer's success log authority to mint an accepted result.

### Verdicts and shared frontends should consume one complete acceptance result

Basis: **derived**, proposed protocol.

Distinguish accepted, rejected, unsupported, incomplete and operational failure. A process exit, solver status or diagnostic string is only one stage observation. Acceptance requires the exact subject, expected root proposition, complete dependency closure, permitted assumptions and all required checking/transfer evidence. Canceled, truncated, stale or skipped work cannot fill a missing gate.

CI, batch, editor and agent clients should call the same acceptance component. Interactive partial results can display local proof progress while remaining explicitly incomplete. The accepted record must bind the consumed immutable artifacts; publishing a log before that record is complete must not make the log an acceptance capability.

The operational transaction boundary is narrower than the mathematical theorem. A service needs owned immutable inputs, bounded producer execution, precise statuses, atomic visibility of a completed record where supported, and recovery/reconciliation after partial failure. Filesystem durability, process containment and concurrent publication are implementation obligations distinct from checker soundness. No portable all-or-nothing transaction across independent durable stores is assumed.

Generation time, checking time, memory, certificate size, reuse and failure latency should be measured separately on matched programs/configurations. DAG sharing or a small checker does not establish favorable costs. This report supplies a cost protocol, not the realistic-program scaling measurements requested by P125.

## Boundaries

The native fixture is a successful containment discriminator, not production security assurance. No certificate parser was proved correct, no compressed proof checker or persistent acceptance service was implemented, and no whole Rust source-safety theorem was constructed. Cryptographic execution systems and verified serialization literature require their separate reports.

The identity/receipt/cache/dependency/verdict findings are derived proposed contracts grounded in exact inspected implementation boundaries and historical controls. Real dependency-roster certification, full threat-model testing, arbitrary-caller coverage, upgrade proofs, representative cost measurements and deployment recovery remain unexamined here. Future engineering includes implementing those gates against the selected Anneal frontend/model.

## Evidence

- **execution/source:** `support/sandbox_probe.py`, successful `sandbox-results.json`, and first environmental failure record. Binary hashes and exact outcomes are retained; no submitted producer or external application was touched.
- **source/execution reused:** Lean 4.34.1 and comparator packages cited above, independently reviewed during this initiative; no version continuity is inferred.
- **source reused:** Charon serialization package at corpus baseline a0ff759e7d2d9a953f0ac40b326dd23197bd9188, Findings on envelope/error metadata, exact-version gates, deduplication and convenience readers.
- **execution reused:** historical edit/revert cache report at that same corpus baseline; its selected projections, environment and exclusions define the result's scope.
- **derived:** receipt components, upgrade obligations, acceptance-capability comparison and proposed shared verdict protocol. They are requirements for evaluating a design, not fresh upstream theorems.

## Revalidation

Run the preserved sandbox probe on the identified macOS/Python subjects from a disposable package copy. Require successful producer output, denied protected write and unchanged challenge together; an unchanged challenge after launcher failure is not a containment result. Preserve launch failure separately and do not silently broaden the profile or replace denial with digest-only detection.

For a concrete acceptance design, mutate theorem-dependent definitions, allowed axiom types, domains, callees, target and model revisions independently while holding the consumer request fixed. Challenge stale artifact families, duplicate/unknown references, canceled stages and schema upgrades. Inspect the final consumed artifacts and root proposition, then test the same verdict path through each frontend. A successful local proof or cached output cannot replace those checks.

*Authored by an AI agent acting on joshlf's behalf.*
