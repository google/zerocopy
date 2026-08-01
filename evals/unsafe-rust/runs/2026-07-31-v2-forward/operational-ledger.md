# V2 Forward Evaluation Operational Ledger

This file records post-freeze operational facts. It does not amend the frozen
packages, fixtures, prompt, oracle, schedule, conditions, or gates.

## Collection

- Runtime root: `/tmp/unsafe-rust-v2-eval.9epWDK`.
- 150 valid reports completed: ten modes, three conditions, five fresh reports
  per cell. Every valid report was nonempty and at most 1,400 words.
- Word counts: minimum 472, maximum 980, total 107,035, mean 713.57.
- Reports were copied byte-for-byte to [`reports/`](reports/). The archived
  report directory's deterministic GNU-tar digest is
  `cbc6de5f526f4c89f68fea5e91f91e002a18b1dd351abc6a796837cd0dd12989`.
- One initial `r006` launch was interrupted before producing any report. It was
  rerun with a fresh agent; no invalid report existed to preserve.
- The permitted target-neutral completion reminder was used where recorded in
  the three shard ledgers. No reminder supplied a finding, semantic hint,
  expected verdict, or condition identity.
- Atomic shard and rebalance claims produced no duplicate report, overwrite,
  or lost output. Dispatch failures caused by the collaboration thread limit
  created no agent and touched no report.
- [`collection-ledgers/shard-1.tsv`](collection-ledgers/shard-1.tsv),
  [`collection-ledgers/shard-2.md`](collection-ledgers/shard-2.md), and
  [`collection-ledgers/shard-3.jsonl`](collection-ledgers/shard-3.jsonl)
  preserve the detailed helper-thread events.
- No target was modified, built, tested, macro-expanded by execution, or
  otherwise executed.

## Blind scoring

- Runtime root: `/tmp/unsafe-rust-v2-score.IpMWrc`.
- Twenty valid scores completed: two fresh blind scorers for each mode. Valid
  score word counts were 1,769–2,386, below the frozen 6,000-word cap.
- The raw valid scores are preserved in [`blind-scores/raw/`](blind-scores/raw/).
  Its deterministic GNU-tar digest is
  `5e19f6e16aba04079e9e519ba8597ac2eb41bc6cf11e3daf3a18a3da37b88856`.
- One first Mode T scorer consulted and cited a Rust release-blog page. The
  frozen prompt permitted only the packet and exact-version Reference or
  standard-library documentation. Its otherwise-complete score was therefore
  excluded, preserved as
  [`blind-scores/invalid/T-s2-attempt-1.md`](blind-scores/invalid/T-s2-attempt-1.md)
  with SHA-256
  `47fdd0495848b4d4a2c5447673819fee629eb2482e39328a014d5a06edd0adab`,
  and replaced by a fresh blind retry.
- All 20 valid scores were checked for completeness, word limit, and prohibited
  external-source leakage before comparison.
- The three parallel-orchestrator records are preserved byte-for-byte in
  [`scoring-ledgers/`](scoring-ledgers/). Their recorded fourteen score hashes
  and word counts match the archived raw scores. Intermediate
  owned-elsewhere/skipped states are reconciled in
  [`scoring-ledgers/README.md`](scoring-ledgers/README.md), including Shard 3's
  accurate pre-T-s2 snapshot of 19 present scores and the later invalid-attempt
  and fresh-retry chronology.
- The deterministic GNU-tar digest of [`scoring-ledgers/`](scoring-ledgers/) is
  `966b9b8c56a31ab33a03c1c9c06c9f8d28c8266f876e9f6ba76569589716ad5b`.
- Modes V and I agreed exactly. Modes U, D, and T differed only in wording for
  the same hard-error decisions. Modes A, C, H, N, and P contained semantic
  disagreements and proceeded to adjudication.

## Blind adjudication

- Runtime root: `/tmp/unsafe-rust-v2-adjudicate.0UjXc7`.
- Five fresh blind adjudicators resolved only the cells recorded in
  [`blind-scores/disagreements/`](blind-scores/disagreements/), preserving all
  agreed cells.
- Adjudication word counts were 1,121–1,725, below the frozen 3,500-word cap.
- Adjudications are preserved in
  [`blind-scores/adjudicated/`](blind-scores/adjudicated/). Its deterministic
  GNU-tar digest is
  `417282fc1c80582feeac9165b188a48ca9a4d131dd642bda2153f5ba57f3fa1a`.
- One canonical final blind matrix per mode was then copied to
  [`blind-scores/final/`](blind-scores/final/). Its deterministic GNU-tar digest
  is `7aa6d3b0fab2739450ed1130a413ab30d39a148a422750b6ad7202ff74cd9198`.
- No condition or package identity was consulted until all ten canonical final
  blind matrices were frozen and verified byte-for-byte.
- The complete [`blind-scores/`](blind-scores/) directory, including raw,
  invalid, disagreement, adjudication, and final artifacts, has deterministic
  GNU-tar digest
  `f1247530c8cc29e8201d1938879f70c983dab03db896085b5f5ac132814c345e`.

## Unblinding and aggregation

- [`aggregate_scores.py`](aggregate_scores.py) mechanically joins the frozen
  launch schedule, blind map, and canonical final matrices. It asserts all 150
  scheduled runs, all 15 reports per mode, and all five reports per condition.
- [`results.md`](results.md) is byte-identical to the aggregator's output and
  has SHA-256
  `a75612b9b3ca7461c89e2c9e7948c9fe4005a9b0086a7422a84de41a2f1a7c5b`.
- The preregistered V2 gate result is `FAIL`. This result was preserved without
  widening validation or editing the frozen package or oracle.

## Post-unblinding interpretation

- [`qualitative-findings.md`](qualitative-findings.md) records the failure
  anatomy, successful capabilities, comparative limits, and next-revision
  hypotheses. It is explicitly post hoc and changes no frozen score or gate.
- Its SHA-256 is
  `ac46a4271a8aaaa176435791cf679cc571e9373e3070a62ab417d61282c55228`.

## Frozen-artifact verification

- V2 oracle SHA-256:
  `555752594765637b691f10f185cede3c6ebd6f92f2e7fb3289a372f67d498e97`.
- Initial frozen manifest SHA-256, before this post-freeze ledger append:
  `dcf87219ac19316787d0460b17ce523f57834792a4b16eed055ee1675f4c27f8`.
- Blind-map SHA-256:
  `50ee500df93e321c3ed1282b88c3ac503d3ab1170abfdd1ff0425c30ef70db8a`.
- Scoring-prompt SHA-256:
  `c2f3041316bc2e5deecb99f43d9a272179bd8052662a882e71ac005f63b928c0`.
- Adjudication-prompt SHA-256:
  `a16446761ea313769c77e00308a6af645d089f91102c7c2a61d15724ac1e162b`.
- The live `skills/unsafe-rust/` tree remained byte-for-byte identical to the
  frozen V2 package after unblinding.
