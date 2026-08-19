# V5 Static Integration — DRAFT / UNSEALED

Production has three irreversible logical stages:

1. `integrate.py prepare-snapshot` validates the selected sources and reviewed
   overlay, materializes packages and targets, derives every map, schedule,
   report prompt, report launch record, evaluator prompt, evaluator launch
   contract, envelope specification, and execution manifest, and publishes a
   read-only `REVIEW-CANDIDATE` without replacement. Report agents receive an
   exact target/authority mount set plus the selected treatment package when
   applicable; they receive no evaluator or attempt-envelope schema.
2. Independent reviewers use `review-subject --private-copy` to verify the
   published tree and create a separately custodied immutable copy. Every hook
   has a locked contract naming exact artifact paths and hashes, the recognized
   procedure/version, required check IDs, and evidence bindings. Reviewers
   inspect the private copy and run `review-custody-check` at the end. Each v2
   receipt binds the contract, descriptor, payload manifest, and reviewed
   artifact-set digest. Prompt and randomization reviews therefore happen only
   after their exact derived bytes exist. The receipt directory is flat and
   contains exactly one `<HOOK-ID>.json` for every hook marked
   `INDEPENDENT_RECEIPT_REQUIRED`—no missing, extra, or nested entry is accepted.
3. `integrate.py finalize` re-verifies and copies the candidate, validates the
   exact receipt inventory, adds only those receipts plus the final status,
   first requires `runtime/state/` to remain exactly empty, constructs the
   static manifest, and writes `STATIC-LOCK.json` as the final
   static byte mutation. Publication uses `renameat2(RENAME_NOREPLACE)` and
   fsyncs content and parent directories. It fails closed where that primitive
   is unavailable. It then completely writes and fsyncs a same-directory
   commitment stage, changes it to `0444`, fsyncs it again, and publishes it to
   the separately custodied final path with
   `renameat2(RENAME_NOREPLACE)` plus a parent-directory fsync. Thus an
   interruption cannot expose a partial or writable final commitment. This
   commitment is required to detect coherent replacement of the whole
   otherwise-self-consistent bundle.

There is no production bypass combining these stages. The private self-test
path carries an identity-checked process-local sentinel and can request only
`SYNTHETIC-TEST-ONLY`; both status and lock bind that kind. This is API
separation, not a Python-process security boundary. The public verifier requires
an expected kind, and both its Python API and CLI require an expected external
commitment for `PRODUCTION`; the CLI defaults to that kind.

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

Publishing a directory and an external file cannot be one atomic filesystem
transaction. Finalization verifies and no-replace-publishes the bundle first,
then atomically no-replace-publishes the already-complete, fsynced, read-only
commitment file. A crash can therefore leave a valid bundle with no final
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

The verifier and its `prepare.py` and `protocol.py` dependencies are loaded from the trusted harness
installation, never from the candidate tree. The exact staged `word_count.py`
bytes are executed by the coordinator during integration self-test; selecting
that harness source is therefore a TCB decision. SHA-256 collision resistance,
filesystem and kernel behavior (including fsync and `renameat2`), and honest
authentication of the identity/version claims in independently supplied review
receipts remain explicit external assumptions. Receipt validation mechanically
proves content, procedure, artifact-inventory, and evidence-string binding; it
does not prove that the named actor performed the work honestly, provide a
signature, or provide an identity authority. The coordinator must authenticate
reviewers and trust their honest execution out of band. Reviewer custody of the
verified private copy between the two verification points is likewise an
explicit actor/coordinator assumption. None of these mechanisms
repairs the diagnostic harness's known shared-agent isolation and output-capture
limitations.
