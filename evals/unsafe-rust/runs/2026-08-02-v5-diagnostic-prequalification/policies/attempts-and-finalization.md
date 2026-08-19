# Attempts and Finalization — DRAFT / UNSEALED

Each scheduled slot has one exclusive started-attempt lease bound to an agent,
attempt ID, and exact envelope-spec bytes. Once leased, the slot is counted and
must not be retried for timeout, exception, malformed output, incomplete output,
or an inconvenient final response. A failure before lease creation is not a
started attempt.

Leasing is forbidden until root `STATIC-LOCK.json` passes whole-file
reverification against root `STATIC-MANIFEST.sha256`. Post-lock mutable
coordinator evidence is written only under `runtime/state/**`; the presence of
any other `runtime/` child invalidates static verification.

Every attempt uses a fresh output directory. After the agent returns, the
coordinator captures all regular output bytes, special-entry defects, exact
final-response bytes, process disposition, and coordinator metadata into one
staged envelope. The complete envelope is fsynced and renamed to its
content-addressed object path before an exclusive canonical pointer is created.
The first pointer wins; later completion cannot replace it. Missing, extra,
oversize, or malformed content remains canonical and is evaluated afterward.
Every undeclared tree entry, including an empty directory, is a defect. The
envelope spec also freezes a full-match UTF-8 format for the operational final
response (normally only the declared report path). Published object trees are
made read-only and every nested file/directory is fsynced before publication.

Because response receipt and sealing are initiated by the coordinator rather
than a trusted runner in the agent's execution boundary,
`G-OUTPUT-FINALIZATION` remains direct `FAIL` and release eligibility remains
false even when these coordinator-side mechanics work perfectly.
