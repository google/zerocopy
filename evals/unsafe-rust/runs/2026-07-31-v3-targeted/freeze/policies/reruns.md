# Frozen Attempts, Reminders, and Rerun Policy

Every attempt is immutable and receives its own directory. Preserve every
regular filesystem output byte, agent identity, timestamps, hashes, known
tool/path deviations, API completion/error state, and disposition before
considering another attempt. The canonical file is the sole evaluated channel;
chat-return prose need not be duplicated byte-for-byte.

Only an externally established infrastructure failure may authorize a fresh
agent attempt. Examples are a service error before semantic work, a tool crash,
or a write failure caused by unavailable infrastructure. Refusal, word-budget
exhaustion, timeout after substantive work, invalid reasoning, missing atoms,
or other semantic noncompletion is a failed replicate and may not be rerun.

An API failure that produces no agent identity is not an evaluated attempt;
record it separately as `API_NO_AGENT_START`, then launch the same next attempt
number. This applies to report, scorer, and adjudicator launches. For any
started attempt, use only these infrastructure disposition codes:
`SERVICE_ERROR_BEFORE_OUTPUT`, `ORCHESTRATOR_TOOL_FAILURE`, and
`FILESYSTEM_FAILURE`. Record the observed evidence and preserve every partial
artifact. A condition not fitting one of those codes is not rerunnable.

A started scorer or adjudicator infrastructure failure likewise preserves its
own attempt directory and authorizes exactly the next numbered fresh attempt.
A schema-invalid, semantically incomplete, or otherwise non-infrastructure
scorer/adjudicator output is non-rerunnable and makes the evaluation `INVALID`.

A terminal report-agent noncompletion is represented by its usable `report.md`
when one exists or by an evaluator-marked placeholder otherwise, is blind-scored
under the ordinary rubric, and is never rerun. Never fabricate a replacement
report, score, or adjudication. An empty or whitespace-only `report.md` is
semantic noncompletion, never a complete report.

Preserved evaluator-attempt and invalid-output directories are inventoried in
both directions against unique ledger events. Any orphan directory, missing
directory, duplicate event, invalid hierarchy, `INVALID.json` marker, or
terminal-invalid ledger event fails closed. Once either terminal-invalid signal
exists, no later evaluation operation is permitted; a complete invalid state
must bind the marker, attestation, return event, and invalidation event exactly.

One exact neutral reminder from `prompts/report.md` is permitted at 180 seconds.
No second reminder or substantive steering is permitted. Scorers and
adjudicators receive no reminders.
