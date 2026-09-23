# Independent Snapshot Review — DRAFT / UNSEALED

Review only the assigned `SNAPSHOT_REVIEW` hook against the published
`REVIEW-CANDIDATE`. Begin by running trusted
`integrate.py review-subject SNAPSHOT --private-copy PRIVATE_COPY`. Inspect only
that verified private copy while it remains in your custody. Load the assigned
`static/integration/review-contracts/<HOOK-ID>.json`; inspect every exact
artifact path/hash it names using precisely its `procedure_id` and
`procedure_version`. Do not review source intent as a substitute for the
generated prompts, evaluator templates, schedules, maps, packets, or manifests
which will actually be locked.

Return a v2 integration receipt with your independently authenticated identity,
role `INDEPENDENT_REVIEWER`, the exact review procedure name and version, the
three exact input digests (descriptor, manifest, and hook contract), the
reviewed payload-manifest and artifact-set output digests, a substantive
summary, and exactly the ordered `required_check_ids` with the concrete digest,
version, and hook-ID evidence required by the contract. Immediately before
issuing the receipt, run trusted `integrate.py review-custody-check --snapshot
SNAPSHOT --private-copy PRIVATE_COPY` and include its exact end-state bindings.
Do not manufacture an output by hashing a favorable claim. If any
check is unsupported, incomplete, or fails, do not produce a PASS receipt;
report the defect and require a new snapshot after correction.

The receipt authenticates a review statement only to the extent that the
coordinator authenticates your identity and trusts your honest procedure
execution out of band. Its hashes do not provide actor authentication. Never
edit the candidate or private copy, write a receipt inside either one, surrender
custody mid-review, or inspect a later replacement tree while claiming to have
reviewed the original snapshot.
