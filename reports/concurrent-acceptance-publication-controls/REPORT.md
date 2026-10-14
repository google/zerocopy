# Controlled concurrent acceptance and publication failures

## Summary

The retained experiment runs real producer and consumer processes, rejects stale generations before atomic publication, and keeps the previous accepted record when a process dies after writing only a partial file. It also demonstrates that same-user producers can change files. Rechecking a final record rejects tested semantic corruption, but these wrapper controls are not an OS sandbox or authenticated stage provenance.

## Applicability

`support/protocol.py` operates only on fresh report-owned directories. Python and the local filesystem/process implementation are trusted operational machinery. The consumer selects a finite arithmetic claim: the 16-entry table must equal `i+1` for inputs 0–15, with exact subject, domain, target, callee and generic/dispatch metadata. This is a controlled protocol claim, not Rust execution, a kernel theorem, or an interpretation of real trait dictionaries/cleanup effects.

No producer-boundary OS sandbox was installed or invoked. Existing sandbox results in other packages are separate observations. Paths, statuses, inputs and the final selected run are retained under support.

## Findings

### The acceptance predicate owns its finite claim and commit condition

Basis: **source**, **execution**.

The producer emits data; `semantic_check` requires exact schema/subject/effects and independently recomputes the full required table. The wrapper additionally checks the actual managed producer outcome, the capture receipt, current fixed policy and checker-input bytes. A capture subprocess really reads and hashes its input. A missing capture invocation supplies neither its result nor receipt and is denied.

Only after those gates does the consumer acquire a filesystem lock, reread the current challenge and require the original generation to remain current. It writes a fresh temporary record, flushes the file, replaces the final path atomically and flushes the directory. The generation check and replacement occur under the same cooperative commit lock. These operations establish the tested process/filesystem protocol; they are not a proved filesystem transaction or a cryptographic stage attestation.

### Failures do not silently become partial acceptance

Basis: **execution**.

The retained run has 25 scenarios. Malformed JSON and a scalar schema are denied; a boolean table element is denied by an exact integer check, and a boolean epoch is denied by canonical JSON subject equality. Python equality alone would otherwise equate `True` with `1`. Real producer exits 7 and 9, timeout termination, SIGTERM cancellation, a partial candidate, omitted consumer capture, and an uncommitted partial consumer record yield no valid accepted record. The return codes and process states remain separate in results.json; a crash is not called semantic rejection.

A real consumer subprocess writes a partial file and exits 13. The prior committed record remains byte-for-byte unchanged and passes readback. This tests death before replacement, not arbitrary crash windows after replacement, reboot/power-loss recovery, remote filesystem semantics or durable multi-file transactions.

### Competing generations and parallel consumers use one commit gate

Basis: **execution**.

Two producers run concurrently for different consumer-selected epochs. The new generation is accepted; the slower old generation is rejected as stale despite its independently correct table. Two separate consumer processes then attempt publication over those same generation-bound artifacts: the old one reports stale-generation, the current one accepts, and the final record rechecks against the current challenge.

This observes actual parallel processes and cooperative locking. It does not establish fairness, starvation freedom, hostile lock bypass resistance, or correctness of every possible interleaving. There is no majority or last-finished-wins policy.

### Mutation rejection and file protection are different results

Basis: **execution**.

| Control | Observed result |
| --- | --- |
| Incorrect table value | semantic mismatch; no valid final record |
| Omitted cleanup tag | omitted-effect gate |
| Wrong generic, associated type, dispatch or callee tag | subject mismatch |
| Producer changes challenge | write succeeds; current-generation check denies publication |
| Producer changes policy | write succeeds; fixed-policy gate denies publication |
| Producer changes checker input | write succeeds; input-binding gate denies publication |
| Producer directly writes a forged final record | forged record fails readback; consumer subsequently replaces it with a checked record |
| Postcommit same-user table tampering | write succeeds; readback rejects the changed semantics |

The metadata mutants test applicability gates. They do not prove that a corresponding Rust destructor, guard, associated-type implementation or dynamic callee was included in a semantic certificate. The cleanup tag itself is admission metadata. An omitted real source behavior needs a source/IR certificate experiment; this protocol does not substitute for it.

### The retained stage facts are operational observations

Basis: **derived** from the implementation and controls.

The parent process observes its child's exit/cancel/timeout and checks captured data. Producer-written completion labels are ignored. The separate consumer test reads local process/capture records; those are trusted same-user orchestration inputs, not authenticated certificates that arbitrary upstream stages ran. A hostile same-user process could modify those files or bypass the advisory lock. The final `read_accepted` function rechecks binding/data semantics, not the historical provenance of all stages.

Successful semantic readback therefore means the stored finite table and consumer subject recheck now. It must not be described as a protected durable accepted-result authority. Protecting challenge, policy, checker inputs, stage records and final publication paths requires a separate process/OS authority design. A private directory or matching hash does not provide it.

For Anneal, keep logical theorem acceptance separate from a generation-bound acceptance record and from OS protection. Require a single shared commit predicate to check all mandatory stage results, preserve unsupported/incomplete/operational outcomes, and revalidate cached data against the current subject. This experiment supplies real observations for concurrency/failure design while leaving source correspondence and hostile isolation explicit.

## Boundaries

**Not examined:** new OS sandbox enforcement, malicious filesystem replacement/symlink races, reboot durability, cache eviction/GC, distributed publication, or authenticated upstream execution history. **Partial source experiment scope:** real Rust guard/destructor/dispatch substitution is absent; only the exact data/protocol mutations above were executed. Extending the tested protocol to a selected deployment is future engineering, while untested hostile-authority and source behavior cases remain research scope.

## Evidence

support/protocol.py is self-contained. support/results.json records scenario verdicts, commands, PIDs, statuses and timing; its run_root locates the corresponding retained inputs/candidates/process outputs/final and partial records. support/environment.json identifies Python, host and source hashes. The results use controlled owned files only.

## Revalidation

In support, run `python3 -B protocol.py experiment --root runs` and preserve the JSON output. Confirm both concurrent process results, the unchanged prior record after exit 13, and the positive same-user write controls. If adding a sandbox, independently review and test the precise enforcement policy before interpreting write denial as a protected authority boundary.

*Authored by an AI agent acting on joshlf's behalf.*
