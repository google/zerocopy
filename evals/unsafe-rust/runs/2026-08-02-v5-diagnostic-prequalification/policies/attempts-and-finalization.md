# Attempts and Finalization — DRAFT / UNSEALED

Before any semantic lease, one authenticated production coordinator must
no-replace claim the run with an immutable record bound to the verified static
lock. The coordinator identity is permanently distinct from the eleven
source/snapshot reviewers and every semantic agent. Each eligible slot then has
one exclusive started-attempt lease bound to an agent, attempt ID, exact launch,
input packet, and envelope-spec bytes. Once leased, the slot is counted and no
fresh semantic execution or replacement attempt is permitted for timeout,
exception, malformed output, incomplete output, or an inconvenient final
response. The coordinator may only resume an interrupted lease initialization
or sealing operation; it may not rerun the agent. Before a terminal claim
exists, an uncommitted private envelope stage may be discarded and recaptured,
and preserving the same final observed attempt-output tree plus unchanged
final-response, process, and metadata arguments is a procedural coordinator
invariant because no persisted request or capture yet exists to compare. Only
the successful capture becomes authoritative. Once the terminal claim exists,
the runtime mechanically accepts only its exact claim-bound request. A failure
before lease creation is not a started attempt.

Leasing is forbidden until root `STATIC-LOCK.json` passes whole-file
reverification against root `STATIC-MANIFEST.sha256`. Post-lock mutable
coordinator evidence is written only under `runtime/state/**`; the presence of
any other `runtime/` child invalidates static verification.
The coordinator must retain uninterrupted custody of the verified bundle,
runtime state, external commitment, and lock from final publication through
bound-gate evaluation, including between commands. A lock does not prevent a
same-UID actor from atomically substituting or chmodding those paths; uncertain
custody invalidates the run.

Every attempt owns a fresh external workspace containing exactly `input/` and
`output/`. Reports receive only their authenticated static input plan;
evaluators receive only the packet and schema tree for their assignment as
derived from the committed immutable predecessor aggregation stage. Production
evaluator leasing accepts no caller-selected packet, launch, schema, or
workspace path. Under the seal lock, the coordinator revalidates the exact
workspace topology and lease-bound input bytes, then captures regular output,
special-entry defects, final-response bytes, process disposition, and
coordinator metadata into one staged envelope. At most 4 MiB of payload across
retained regular files and final-response bytes, 4,096 tree entries, and 256
KiB of cumulative canonical pathname-token bytes are retained. A spec-level
overage below the aggregate byte ceiling is still fully captured. A file
beyond the remaining file-capture budget becomes an authenticated
`captured:false` size record; a final response beyond the remaining aggregate
budget is likewise authenticated but not retained. Entry-count or pathname-byte
overflow becomes one reason-specific authenticated capture-limit sentinel. Any
hard overflow makes the declared primary semantically unavailable and therefore
reaches the phase's terminal `ERROR` rather than exhausting coordinator memory.
For a final-response source larger than 4 MiB, the terminal claim records its
stable actual file size and an explicitly named SHA-256 of the first 4 MiB plus
one byte; it does not misrepresent that bounded prefix as a whole-file digest.
Every portable UTF-8 relative output path is recorded literally. Any other
POSIX pathname byte sequence—including backslashes, controls, reserved-prefix
names, or non-UTF-8 bytes—is recorded with the canonical injective
`_encoded-posix-path/<base64url>` token. Every retained regular file—portable
or otherwise—is copied to a fixed-width digest-safe internal payload path. A
nonportable path is therefore a format defect, but it cannot prevent canonical
sealing or make the envelope JSON/path framing ambiguous.

The complete private envelope is fsynced and hardened before an immutable
terminal claim is exclusively published. That first-terminal claim binds the
request fields and envelope digest. The staged envelope is then renamed to its
content-addressed object path; after semantic verification, an exclusive
canonical pointer completes the seal. Later completion cannot replace either
authority. Missing, extra, oversize, or malformed content remains canonical and
is evaluated afterward. Every undeclared tree entry, including an empty
directory, is a defect. The envelope spec also
freezes a full-match UTF-8 format for the operational final response (normally
only the declared report path). Published object trees are made read-only and
every nested file/directory is fsynced before publication.

Seal-time input comparison detects persistent workspace drift but is not a
history of bytes observed during execution. A same-UID agent can otherwise
mutate an input, use it, and restore it before the check. A threat model that
includes this behavior requires OS-enforced read-only input mounts or separate
ownership; chmod and comparison are not sufficient isolation.

Aggregation proceeds only at sealed phase barriers through the exact immutable
prefix `01-report-products`, `02-scorer-products`,
`03-consistency-products`, `04-score-products`,
`05-materiality-products`, `final`. Each complete, fsynced, read-only stage is
atomically published without replacement and has a canonical manifest binding
the static lock, coordinator, predecessor manifest, cumulative envelopes, and
payload bytes. A successful run contains 154 through 163 canonical attempts.
An absent/non-UTF-8 report primary, or an absent, format-invalid, or
semantic-invalid evaluator primary, instead publishes one authenticated
terminal `ERROR` bound to the exact failed phase and precludes both later
attempts and a final aggregate. A usable report with another format defect,
including a spec-over-cap report retained below the 4 MiB hard ceiling,
continues to the final aggregate and receives its frozen gate consequence. A
report beyond the hard ceiling is intentionally unavailable rather than
partially interpreted and produces the authenticated terminal `ERROR`.

Because response receipt and sealing are initiated by the coordinator rather
than a trusted runner in the agent's execution boundary,
`G-OUTPUT-FINALIZATION` remains direct `FAIL` and release eligibility remains
false even when these coordinator-side mechanics work perfectly.
