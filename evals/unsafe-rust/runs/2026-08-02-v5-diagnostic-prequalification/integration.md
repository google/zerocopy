# V5 Static Integration — DRAFT / UNSEALED

Static production integration has two review boundaries and five publication
stages, listed below. The separate post-lock semantic runtime has six
aggregation stages documented in its own section later in this file.

1. `integrate.py prepare-source-review` mechanically transforms the checked-in
   DRAFT semantic templates into an immutable `SOURCE-REVIEW-CANDIDATE`. The
   candidate binds the exact trusted source declaration, all eight target
   source trees, the 38 original DRAFT templates, the 38 transformed semantic
   files, canonical report authority packet, concrete procedures and receipt
   schema, full trusted reviewer-tool inventory, requested values, and seeds.
2. Two independent oracle reviewers and one coherence reviewer each use
   `review-source-subject`, work only from their verified private copy, run
   `verify-source-quotations` where required, and author only the complete
   contracted item-by-item work product and result evidence. The trusted
   `build-source-review-receipt` command rechecks disjoint source/private-copy
   custody, binds the actual
   runtime and deterministic digests, validates that authored work, and
   no-replace-publishes canonical read-only JSON. Finalization requires and
   preserves those exact receipt bytes. Their canonical identities must be distinct
   and authenticated out of band. `finalize-reviewed-inputs` verifies all
   three exact receipts and no-replace-publishes the admitted candidate bytes;
   it does not silently rewrite semantic content.
3. `integrate.py prepare-snapshot` consumes those finalized reviewed inputs,
   promotes lifecycle fields to READY, materializes packages and targets,
   derives every map, schedule, report prompt/input-plan/launch record,
   evaluator prompt/launch contract, envelope specification, and execution
   manifest, and publishes a read-only `REVIEW-CANDIDATE` without replacement.
   Report agents receive the exact target/authority mount set plus the selected
   treatment package when applicable; they receive no evaluator or
   attempt-envelope schema.
4. Eight distinct snapshot reviewers use `review-subject` and
   `review-custody-check` on private copies. Every hook contract binds exact
   artifacts, concrete procedure and receipt schema, reviewer tools/runtime,
   acceptance requirements, and complete work-product coverage. The trusted
   `build-snapshot-review-receipt` command performs the same disjoint-custody, binding,
   validation, and no-replace publication discipline. These eight
   identities must also be disjoint from the three source reviewers and are
   permanently ineligible for every runtime semantic role.
5. `integrate.py finalize` re-verifies and copies the candidate, validates the
   exact receipt inventory, adds only those receipts plus the final status,
   first requires `runtime/state/` to remain exactly empty, constructs the
   static manifest, and writes `STATIC-LOCK.json` as the final
   static byte mutation. The finalizer derives the external commitment from
   that fully verified private stage, re-verifies the stage and re-derives the
   same commitment, then publishes the directory with
   `renameat2(RENAME_NOREPLACE)`. It fully verifies the published path and
   requires its derived commitment to equal the prepublication stage identity;
   a coherently substituted bundle is therefore rejected rather than blessed.
   It fails closed where that primitive is unavailable. It then completely writes and fsyncs a same-directory
   commitment stage, changes it to `0444`, fsyncs it again, and publishes it to
   the separately custodied final path with
   `renameat2(RENAME_NOREPLACE)` plus a parent-directory fsync. Thus an
   interruption cannot expose a partial or writable final commitment. This
   commitment is required to detect coherent replacement of the whole
   otherwise-self-consistent bundle.

There is no production bypass combining these stages. The public production
validators accept only canonical, read-only `PASS` receipts; the integration
review-finalization boundary captures each receipt from one
`O_NOFOLLOW|O_CLOEXEC|O_NONBLOCK` descriptor, verifies stable read-only regular
inode metadata around the read, and copies only the validated captured bytes.
It never validates one pathname read and later copies a second pathname read.
The integration
self-test's independent-review receipt helpers carry the
distinct `SYNTHETIC-TEST-ONLY` status. The private self-test
path carries an identity-checked process-local sentinel and can request only
`SYNTHETIC-TEST-ONLY`; both status and lock bind that kind. This is API
separation, not a Python-process security boundary. The public verifier requires
an expected kind, and both its Python API and CLI require an expected external
commitment for `PRODUCTION`; the CLI defaults to that kind.

The checked-in schema files truthfully describe DRAFT source. Snapshot
construction deterministically promotes only each schema's top-level lifecycle
comment, and every later snapshot/lock verification byte-compares the complete
schema inventory against that exact derivation. It additionally rejects
`DRAFT` or `UNSEALED` prose in every schema mounted to an evaluator. Thus source
status is not leaked through a READY agent-visible schema, and a caller cannot
substitute an independently rewritten schema while preserving the comment.

## Exact production command sequence

The coordinator first creates a fresh input directory containing only
`reviewed-values.json` (status `SOURCE-REVIEW-CANDIDATE`, an empty
`reviewed_static` array, and `reviewed_static_base` equal to
`DERIVED-BY-TRUSTED-SOURCE-REVIEW-BUILDER`) and `seeds.json`. Then:

1. Run `integrate.py prepare-source-review --source-root UNSAFE_RUST_ROOT
   --inputs SOURCE_INPUTS --output SOURCE_CANDIDATE
   --acknowledge-source-review-values`.
2. Give each of three independently authenticated actors a fresh private path.
   Each runs `review-source-subject SOURCE_CANDIDATE --private-copy COPY`,
   `reviewer-runtime-attestation`, its bound procedure (including
   `verify-source-quotations --private-copy COPY` for the oracle reviews), and
   writes its itemized `WORK_PRODUCT.json` and exact `RESULT.json`, then runs
   `build-source-review-receipt --snapshot SOURCE_CANDIDATE --private-copy
   COPY --review-name REVIEW_NAME --actor-id ACTOR_ID --work-product
   WORK_PRODUCT.json --result RESULT.json --output
   SOURCE_RECEIPTS/REVIEW_NAME`. Run `validate-source-review-receipts
   --snapshot SOURCE_CANDIDATE --receipts SOURCE_RECEIPTS` after all three
   read-only receipts exist.
3. Run `finalize-reviewed-inputs --snapshot SOURCE_CANDIDATE --receipts
   SOURCE_RECEIPTS --output REVIEWED_INPUTS
   --acknowledge-authenticated-source-reviewers`.
4. Run `prepare-snapshot --source-root UNSAFE_RUST_ROOT --inputs
   REVIEWED_INPUTS --output SNAPSHOT --workspace-base FRESH_OPAQUE_WORKSPACE
   --acknowledge-reviewed-inputs`.
5. Give each of the eight distinct hook reviewers a fresh private copy using
   `review-subject SNAPSHOT --private-copy COPY`. Each runs
   `reviewer-runtime-attestation`, performs the bound procedure, writes its
   itemized `WORK_PRODUCT.json` and exact `RESULT.json`, then runs
   `build-snapshot-review-receipt --snapshot SNAPSHOT --private-copy COPY
   --hook-id HOOK_ID --actor-id ACTOR_ID --work-product WORK_PRODUCT.json
   --result RESULT.json --output SNAPSHOT_RECEIPTS/HOOK_ID.json`. Run
   `validate-snapshot-review-receipts --snapshot SNAPSHOT --receipts
   SNAPSHOT_RECEIPTS` after all eight read-only receipts exist.
6. After authenticating all eleven identities and their pairwise separation,
   run `finalize --snapshot SNAPSHOT --receipts SNAPSHOT_RECEIPTS --output
   BUNDLE --external-commitment-output EXTERNAL_COMMITMENT
   --acknowledge-reviewed-snapshot`.
7. Before any semantic launch, run `verify-static BUNDLE
   --expected-bundle-kind PRODUCTION --expected-external-commitment
   EXTERNAL_COMMITMENT` from the separately trusted harness.

The acknowledgement flags record coordinator decisions; they do not prove
identity, reviewer honesty, or custody. Candidate trees, receipts, private
copies, the final bundle, and external commitment must occupy disjoint paths.

## Production staged runtime

After static verification and before any semantic lease, run
`protocol.py advance-aggregation --static-root BUNDLE
--external-commitment EXTERNAL_COMMITMENT --coordinator-actor ACTOR`. On the
first call this no-replace publishes an immutable coordinator claim bound to
the verified static-lock digest. The actor must be independently authenticated,
must be distinct from all eleven source/snapshot reviewers, and is reserved
from every report or evaluator role. A preexisting semantic lease without this
claim is invalid; later calls must use the same claimed identity.

The returned progress first exposes only the 120 report assignments. Lease a
report by run ID, never by caller-supplied launch/input paths, and seal it
through the production route. Once all 120 are sealed, `advance-aggregation`
derives and atomically publishes `01-report-products`. Each later call exposes
only the exact evaluator assignment frontier derivable from the committed
predecessor stage. `lease-evaluator` accepts the assignment and agent identity,
then finds and rederives that assignment's packet, launch, and envelope spec
from the immutable stage; a caller cannot provide or substitute those paths.

The exact stage order is:

1. `01-report-products`;
2. `02-scorer-products`;
3. `03-consistency-products`;
4. `04-score-products`;
5. `05-materiality-products`; and
6. `final`.

Each stage is first built as a complete private sibling tree, fsynced, checked
for its exact file and directory inventory, hardened read-only, and published
with `renameat2(RENAME_NOREPLACE)`. Its canonical manifest binds the verified
static-lock digest, immutable coordinator claim, exact predecessor-manifest
digest, cumulative canonical envelope digests, and every stage payload. Only an
exact prefix is legal. An interrupted private staging tree has no authority and
may be deterministically discarded before retry; a committed stage is accepted
only if it byte-for-byte rederives.

The successful path seals 154 through 163 attempts: 120 reports, 16 scorers,
16 consistency reviewers, zero through eight conditional mode adjudicators,
two materiality reviewers, and zero or one conditional materiality
adjudicator. `aggregation-status` is read-only: `WAITING` means report
collection is incomplete, `PUBLISHED` means an immutable stage is waiting on
its next cohort, and `DERIVABLE` means the current sealed phase can produce an
unpublished next artifact. `TERMINAL-FAILURE` means the exact current sealed
phase produced the authenticated mutually exclusive `ERROR` outcome.
`COMPLETE` requires 154 through 163 sealed assignments, all six manifests, and
a final aggregate digest.

At each sealed phase barrier, the coordinator first determines whether semantic
derivation is possible. A report with no primary output or non-strict-UTF-8
primary bytes produces immutable `aggregation/terminal-failure.json` with
outcome `ERROR` before Stage 01. Other canonical report format defects continue
through aggregation. In particular, a usable over-cap report is counted and
projected; the final aggregate then makes `D-OUTPUT-VALID` fail. For scorers,
consistency reviewers, either adjudicator role, and materiality reviewers, an
absent primary or any format/semantic invalidity produces the authenticated
terminal `ERROR` at that phase barrier because no downstream semantic packet
can safely be derived. The terminal record binds the exact static lock,
coordinator, blocked stage, predecessor, cumulative phase envelopes, and
failure facts. It is mutually exclusive with `aggregation/final`, makes all
later leasing/sealing invalid, and causes bound aggregate/gate evaluation to
report the rederived error rather than fabricate a final context.

Every acquired workspace must contain exactly the lease-bound `input/` and
`output/` children. The production seal revalidates that topology and the exact
report plan or evaluator packet/schema input tree under the operation lock
before accepting output. This detects persistent drift. It cannot detect a
same-UID agent that mutates an input, uses the changed bytes, and restores the
original before seal-time verification. Where such an agent is in the threat
model, launch with OS-enforced read-only input mounts or separate ownership;
chmod and post-execution comparison are insufficient.

Output sealing retains at most 4 MiB total across regular-file and
final-response payload, at most 4,096 accepted tree entries, and at most 256
KiB of cumulative canonical pathname-token bytes. Observing the 4,097th entry
triggers the entry-count sentinel rather than retaining it. Spec-level overages below the
aggregate byte ceiling remain fully captured and receive their later gate
consequence. A file or final response beyond its remaining hard budget is
authenticated but not retained; an entry-count or pathname-byte overflow
collapses to one reason-specific authenticated capture-limit sentinel. Any hard
overflow makes the primary semantically unavailable and produces the phase's
terminal `ERROR` without unbounded coordinator memory or traversal work.
Retained files use fixed-width digest-derived payload paths, while their literal
or injective encoded POSIX pathname remains in the envelope record.
For a final-response source larger than 4 MiB, sealing binds the stable actual
source size and an explicitly named digest of the first 4 MiB plus one byte;
the bounded prefix is never labeled as a digest of the complete source.

Sealing fsyncs and hardens a complete private envelope before exclusively
publishing the terminal claim that binds its digest and the request fields.
That claim is the first-terminal authority. The coordinator then publishes and
semantically verifies the content-addressed object before exclusively writing
the canonical pointer that completes the seal. Before the claim exists, crash
recovery may discard an uncommitted private stage and recapture without
rerunning the agent; preserving the same final observed attempt-output tree and
unchanged final-response, process, and metadata arguments is a procedural
coordinator invariant because there is no persisted request or capture to
compare. Only the successful capture becomes authoritative. After the claim
exists, exact-argument recovery is mechanically enforced.

## Commitments and path domain

New manifests use `V5_DOMAIN_FRAMED_TREE_V1`, not a `sha256sum`-style text
format. A tree begins with its NUL-separated domain and an unsigned 64-bit
record count. Each sorted record contains the domain, `NUL + "RECORD" + NUL`,
a one-byte `D` or `F` kind, an unsigned 64-bit path-byte length, exact path
bytes, an unsigned 64-bit content length, an unsigned 64-bit mode-field length,
the optional four-byte mode, and a 32-byte content digest (zero for a
directory). Integers are big-endian. Domain tags distinguish source-copy,
review-snapshot, and final-static manifests. This length/domain framing is
injective over the accepted record domain.

Every represented path is normalized relative POSIX text in
`PORTABLE_ASCII_RELATIVE_PATH_V1`: each nonempty component starts with an ASCII
letter or digit and otherwise uses only ASCII letters, digits, `.`, `_`, `+`,
`@`, `%`, `=`, `:`, `,`, or `-`. Absolute paths, `..`, alternate spellings,
non-UTF-8 names, controls, delimiters, symlinks, and special files are rejected.
Historical package and target identities remain byte-for-byte `BYTE_TREE_V1`;
the stricter path-domain admission check does not alter any accepted historical
encoding.

The final static manifest inventories files and directories and includes their
modes. Static files are `0444`, static directories and the bundle root are
`0555`, and `runtime/` plus `runtime/state/` are `0700`. Descendants of
`runtime/state/` are the sole mutable exclusion; both directory records remain
in the static inventory. These modes reduce accidental mutation. They are not
an operating-system security boundary, because the owner may chmod them; every
consumer must re-run the trusted verifier before relying on the bundle.
`runtime/state/` is required to be exactly empty throughout snapshot creation,
review verification, finalization copying, receipt insertion, and lock
creation. It becomes mutable only after a valid static lock exists.

## Production authority and external commitment

Production preparation and verification do not trust the candidate's own
source selection. They compare its embedded declaration byte-for-byte with the
trusted harness `static-inputs/source-declaration.json`, recompute the declared
package and target trees from the trusted unsafe-rust source root, and require
the materialized package, `SKILL.md`, target, source-binding, and generated
identity records to equal those trusted identities. Candidate copies of
`integrate.py`, `prepare.py`, `protocol.py`, and the executed `word_count.py`
must equal the separately
trusted harness bytes.

Report artifacts are not accepted merely because their hashes agree with one
another. The trusted verifier regenerates and byte-compares all 120 prompts,
input plans, and launch records from the authenticated condition and target
maps, launch schedule, reviewed invocation/environment values, execution and
envelope contracts, and trusted package/target identities. In particular, the
mounted target must be the target selected by the slot's target label, and the
mounted package must be exactly the package selected by its condition role.
The trusted runtime repeats this relational validation before report leasing
or aggregate reconstruction; a launch's self-declared content digests are not
premises for those joins.

`finalize --external-commitment-output PATH` requires a fresh path outside the
bundle. The commitment binds the trusted source declaration, snapshot
descriptor and manifest, review-receipt index, final manifest and lock, and the
trusted integration/prepare/protocol/word-counter implementation digests. Production consumers pass
that separately stored value to the trusted verifier/protocol. Without it,
local recomputation can detect internal corruption but cannot distinguish a
coherently replaced bundle from the originally accepted bundle. The commitment
must be authenticated and custodied by the coordinator; placing it inside
attacker-replaceable candidate storage defeats its purpose.

The trusted production verifier also returns the eleven reviewer identities
and a canonical review-evidence object from the same descriptor-captured
receipt bytes whose sizes, modes, and digests it authenticates against the
framed static manifest. That object also binds the exact canonical
`STATIC-LOCK.json` bytes and must agree with the separately custodied external
commitment. Runtime state, lease, and seal operations carry the returned
exclusion set. Aggregation consumes the returned source- and snapshot-review
records and lock digest directly for oracle/coherence decisions, input digests,
and materiality review scope. No consumer may reopen those receipt or lock
paths or derive a second identity/evidence set after static verification
completes.

Publishing a directory and an external file cannot be one atomic filesystem
transaction. Finalization first derives the commitment from its verified
private stage, re-verifies that stage and requires a second derivation to
agree, no-replace-publishes the bundle, fully verifies the published path, and
requires that path to derive the identical prepublication commitment. Only
then does it atomically no-replace-publish the already-complete, fsynced,
read-only commitment file and perform a final committed verification. A crash
can therefore leave a valid bundle with no final
commitment path; it cannot leave a partial or writable file at that path. A
hard interruption may leave an unreferenced same-directory staging file, which
has no authority and may never be substituted for the required final path.

`recover-external-commitment` exists only for that bundle-present,
commitment-missing interruption window. It requires a missing output outside
the bundle, revalidates exact trusted source and harness provenance before and
after deriving the commitment, never overwrites any path, and requires the
coordinator to explicitly attest uninterrupted trusted custody of that exact
published bundle since successful finalization and that no commitment was
previously published. This continuity-of-custody fact is not mechanically
derivable: without it, a self-consistent replacement could be blessed as the
original reviewed bundle. If custody is uncertain, or any commitment path
already exists, recovery is forbidden; discard the bundle and repeat the
review/finalization workflow.

## Trust assumptions

The verifier and its `prepare.py` and `protocol.py` dependencies are loaded
from the trusted harness installation, never from the candidate tree. The
candidate's staged `word_count.py` is descriptor-captured and compared with a
separately captured trusted harness copy, but only the trusted capture is
compiled and executed; selecting that trusted harness source and Python runtime
is therefore a TCB decision.

The verifier authenticates bytes, not continued ownership of a pathname. From
successful final publication until bound-gate evaluation completes, the
coordinator must retain uninterrupted, non-adversarial custody of the bundle
root, its ancestors and descendants, `runtime/state`, the external commitment,
and any coordinator lock. This includes intervals between commands and while
semantic agents run; those agents receive only external materialized
workspaces. A same-UID actor able to atomically replace or chmod the custodied
tree is outside the mechanical guarantees. If that threat is in scope, the
coordinator must first place the bundle in a private OS-enforced namespace or
provide an equivalent descriptor-anchored snapshot. File modes and advisory
locks constrain cooperating processes only. The external commitment detects a
replacement at the next verification boundary, but cannot make already-returned
`Path` objects immutable or authenticate mutable runtime state. If custody is
ever uncertain, discard the bundle and its state.

The same limitation applies independently to the external agent workspaces.
Seal-time exact-tree revalidation authenticates their final observed state, not
every byte an agent observed during execution. Preventing transient same-UID
input substitution is therefore an explicit runner/OS TCB obligation even when
bundle custody itself is sound.

SHA-256 collision resistance, filesystem and kernel behavior (including fsync
and `renameat2`), and honest authentication of the identity/version claims in
independently supplied review receipts remain explicit external assumptions.
Receipt validation mechanically proves content, procedure,
artifact-inventory, and evidence-string binding; it does not prove that the
named actor performed the work honestly, provide a signature, or provide an
identity authority. The coordinator must authenticate reviewers and trust
their honest execution out of band. Reviewer custody of the verified private
copy between the two verification points is likewise an explicit
actor/coordinator assumption. None of these mechanisms repairs the diagnostic
harness's known shared-agent isolation and output-capture limitations.
