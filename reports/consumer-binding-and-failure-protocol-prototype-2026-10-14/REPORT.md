# Consumer binding, assumption policy, and failure controls for certificates

## Summary

The standalone wrapper binds validated certificate data to a caller-selected challenge, original source, selected model/kernel identities, consumer-owned Lean claim, successful checking, and actual assumption policy. The suite produced the expected four acceptances and 34 rejections in 38 protocol cases.

Five extra real Lean controls distinguish kernel checking from policy: direct/imported hidden axioms and native assumptions elaborate but policy rejects; missing/malformed proofs fail elaboration. The wrapper is trusted unverified code, and private task directories are not OS sandboxing.

## Applicability

checker.py, selected challenge/model, mutation specimens, generated proofs, and outputs are identified by report-owned artifact hashes. Kernel execution uses exact Lean 4.31.0 at 68218e876d2a38b1985b8590fff244a83c321783 and its recorded executable SHA256.

The supported profile is this safe-byte subject, all 256 u8 inputs, wrapping-byte-tree-v1, concrete u8 scale5 helper/instance, declared target/flags, and fixed assumption policy. This is not a general crate/trait resolver, scheduler, sandbox, proof-object loader, or authenticated result store.

Coverage contributes to T101–T110/P134/P137 at the actual tested frontier. No unsafe destructor/cleanup path, arbitrary trait dictionary, full dependency DAG, parallel writer, or OS adversary was exercised.

## Findings

### The consumer selects meaning and immutable byte snapshots

Basis: **source** + **execution**.

check receives challenge/candidate bytes, an external expected challenge hash, and the consumer's producer-process outcome. It rejects changed challenge bytes and unsupported consumer profiles. Candidate bindings must exactly match source/program, domain/property, semantics, concrete callee/instance, target/flags, revisions, generation, policy, model hash, and kernel binary hash.

The wrapper reads and hashes the original source, performs its trusted whole-file capture, and compares it with the selected tree. It reads a model snapshot and checks its selected hash, then checks the actual Lean executable hash. Only validated operation tags/byte numbers enter the consumer-owned proof template. Producer Lean code is outside the schema.

The generated claim always states the consumer's selected hash equality and all-u8 source/IR evaluator correspondence. It is not constructed from a producer-selected expected predicate. Corrupting a proposed model and weakening its expected goal does not change this selected obligation.

Immutable here describes the byte snapshots inside a call. It does not describe filesystem permissions or protection from another same-user process.

### Logical checking and the artifact wrapper have different authority

Basis: **source** + **execution**.

The kernel checks consumerAccepted using ArithmeticModel.lean's proved checker/translator endpoints. The wrapper handles schema, real-byte binding, selected profile, process/stage status, and exact dependency policy.

The allowlist is propext, Classical.choice, Quot.sound, with native-proof assumptions forbidden. Actual successful baselines report only propext. Kernel exit 0 alone does not satisfy this policy.

Dependency output comes from a consumer-owned template and trusted Lean process. This is not a proved checker API or authentication of arbitrary stdout. Data-only fields prevent normal certificate injection of print directives; an actor with equivalent OS privileges could alter scripts/runtime/output. Hashes and private directories do not supply that isolation.

A complete transitive .olean/shared-runtime identity was not established. The selected kernel executable hash is checked; import/runtime remains an explicit frontier.

### Mutation verdicts are tied to actual gates

Basis: **execution**.

Expected rejections include changed source/program; property True; narrowed/empty/even-only domains; changed semantics; target/flags/generation/instance/callee/revision/model/binary/policy substitutions; corrupt model plus weakened goal; actual model-snapshot substitution; invalid opcode/reference; literal 256; conflicting/truncated exports; missing/duplicate rows; missing/partial stages; accepted-record or proof-code injection.

A missing concrete callee inventory tests this schema's completeness gate. It does not establish completeness of arbitrary Rust trait instances, dynamic dispatch, or crate DAGs.

Two material cases pass binding/schema and reach the kernel: a multiplier changed from 5 to 6 and an incorrect native output row. Their acceptance proofs fail and the wrapper rejects the nonzero exits. These are semantic checker controls, rather than only metadata mismatch controls.

### Real assumption and proof controls

Basis: **execution**.

| Fixture | Kernel exit | Policy verdict |
| --- | ---: | --- |
| Direct hidden correspondence axiom | 0 | Reject hidden |
| Imported HiddenHelper.assumedFalse | 0 | Reject transitive imported assumption |
| native_decide for the valid certificate | 0 | Reject acceptance._native.native_decide.ax_1_1 |
| Malformed requested proof | 1 | Reject kernel failure |
| Missing consumerAccepted declaration | 1 | Reject kernel failure |

Direct/imported/native fixtures display the same consumer claim as the baseline but different actual dependencies. A theorem name or successful elaboration does not identify its assumptions. Failed diagnostics may include error-recovery declarations; they are not accepted proofs.

These are consumer-owned proof-object experiments. The normal wrapper accepts data certificates; it does not execute arbitrary producer Lean source.

### Failure, aggregation, and cached data

Basis: **source** + **execution**.

A real producer subprocess exits 7. Another is cancelled by a 0.02-second timeout. Both reject despite otherwise valid candidate data. Missing and pending aggregate stages also reject. This exercises a fail-closed gate, not production cleanup, scheduler recovery, or atomic publication.

The cache stores candidate data only and never supplies cached acceptance authority. Generation-001 data reject under a selected generation-002 challenge. An updated generation-002 candidate is rebound and kernel checked again, then accepted.

There was no parallel-writer or OS-race test. Candidate stage/status labels are checked for the required values; the caller separately supplies the producer process outcome. These labels do not independently prove that upstream stages executed or certify an arbitrary obligation roster. The kernel proof checks the captured claim regardless; the wrapper/orchestrator remains trusted for operational stage provenance. Selected snapshots bind this call; they do not protect a final result file from arbitrary same-user writes.

### Scope of the acceptance result

Basis: **derived**.

The pure accepted_predicate requires valid binding, producer/stages, kernel success, policy success, and selected snapshots. Its implementation and caller selection remain trusted. A proved logical Boolean checker does not verify the entire Python binding wrapper or process execution.

The observed 38 protocol cases yield four acceptances (three routes plus current-generation rechecking), 34 rejections, and five separately rejected assumption/proof controls. These support the stated gates at this fixed schema/frontier.

## Boundaries

**Known checker boundary (source reviewed 2026-10-14):** the recorded Lean 4.31 and legacy 4.30rc2 runs are observations conditional on checker soundness. Their pinned `src/kernel/inductive.cpp` lacks the final nested-parameter validation added by [fix a39eab69](https://github.com/leanprover/lean4/commit/a39eab69e1eee9ad38f4efe507907b1026a77808). The [official 4.32.2 notes](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/) describe arbitrary false-theorem acceptance and a combined external-checker exploit. This source finding does not establish exact exploit portability or invalidate these owned terms, but successful exit and a clean axiom list do not establish sound acceptance of arbitrary producer proofs. No exploit was executed, toolchain upgraded, or recorded result rewritten. A deployment needs a separately justified checker/version and dependency policy; presence of the fix in 4.34.1 is not a universal soundness theorem.

**Answered:** this schema's source/domain/property/config binding; parser/structural failures; model/goal substitution; actual direct/imported/native policy; missing/malformed proofs; crash/cancel; partial stages; stale data-cache rechecking.

**Research still open:** full crate/trait/callee closure, unsafe guards/destructors/cleanup, imported-library identity, independent proof-object loading, wrapper correctness, real DAG/cache scheduling, concurrent publication, OS isolation, and authenticated final records.

**Known trust:** consumer selector/template/capture, Python wrapper, actual Lean output/import/runtime, and relevant OS actors. No sandboxing or verified wrapper is claimed.

**No P128/P136 completion:** no verified executable checker binary or full original-Rust adequacy is produced. The claim concerns the captured byte model under named frontiers.

## Evidence

support/checker.py and run_mutations.py retain implementation and test driver. support/experiments/ retains challenge/source/model/candidate, mutation specimens, generated protocol proofs/logs, HiddenHelper source, assumption controls, and mutation-results.json. artifact-index.json hashes every preserved item. Compiled .olean/native binaries are excluded; the controlled helper can be rebuilt from its source.

Input/output hashes identify observed artifacts; they do not authenticate their producers or prevent same-user modification. No upstream source mirror is required.

## Revalidation

In a task-owned copy, set LEAN_BINARY to the exact Lean 4.31.0 executable and run python3 -B run_mutations.py. Compare all 38 verdicts, both semantic kernel failures, and all five assumption/proof dispositions. Require rechecking for the current generation, rather than trusting a cached success flag.

An extended pipeline needs independent challenge selection, explicit capture/binding assurance, complete dependency closure, scheduler/publication semantics, and real OS controls where adversarial code executes. This suite establishes only its stated prototype gates.



*Authored by an AI agent acting on joshlf's behalf.*
