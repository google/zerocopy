# Independent review of Anneal #3731 I107–I159 and two I147 refresh controls

## Summary

At the retained #3731 issue scope and `reference` baseline `75fa78c1b623ab8db9d9acb4f31ec7958bfb9110`, the 53 investigations I107–I159 remain **2 complete at disposable-prototype scope, 49 partial, and 2 conditional**. I137 and I138 are the complete prototype rows; I141 and I143 are conditional. No current Anneal V2 product acceptance claim is complete in this range. [The row review](support/row-review.csv) gives the exact issue question, status, gate, evidence-qualified residual, and next prerequisite for every ID.

The v22 ledger carries two stale residual clauses. I147 says that source-unchanged artifact and changed external-model controls remain untested, although its cited reports already executed both. I151 says conflicting Lake writers remain untested, although its cited shared-tree package executed reverse killed-writer schedules. Both rows remain partial. This review also records the relevant I126 trust-execution evidence more precisely, adds the human interpretation gate to I129, and narrows I148's remaining question to intended flags and representative cost rather than arbitrary unselected variants.

Two new local-only I147 controls were executed against the pinned Lean/Lake `v4.30.0-rc2` binary. A valid `.olean` replacement preserved the original nanosecond mtime and unchanged Lake hash sidecar: the old open file still reported no goals, while a new file, reopened file, fresh server, and fresh batch saw the changed imported value. Separately, changing only an equal-length source comment produced a different source hash but a byte-identical rebuilt `.olean`; old, new, and reopened live files agreed, and a fresh batch proof passed. These are direct Lean/Lake fixture observations, not Anneal worker policy.

## Applicability

The issue wording and scope-extension comment are the public #3731 bytes retained in the v22 audit, last reread there at 2026-09-29 18:49:42 UTC. This review did not refetch them, change issue status, or treat issue proposals as adopted requirements. The corpus point is the local authoritative `reference` checkout at `75fa78c1b623ab8db9d9acb4f31ec7958bfb9110`. The [v22 row challenge](../anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support/row-challenge-v22.json) and [full ledger](../anneal-3730-3731-final-coverage-audit-2026-09-29-v22/support/investigation-final-v22.csv) are the dated baseline, not an assertion that later product work has occurred.

The local probes used the cached Lean 4.30.0-rc2 arm64 macOS executable identified in `REPORT.json`, direct `lean --server`, a tiny private Lake project, `LEAN_NUM_THREADS=1`, and fresh direct `lean --json` batch checks. The scripts were adapted from the retained three-launch-mode refresh harness and run under a conversation-specific Meta/Data scratch directory. No dependency was fetched or installed. Each probe used one server session at a time, a 25% free-memory admission floor, and a 3 GiB sampled process-tree RSS cap. The final report package retains the modified scripts, sanitized wire transcripts, decisive OLean bytes, and fresh batch records.

## Findings

### Per-ID disposition

The [row review](support/row-review.csv) is the per-ID decision record; it preserves the exact requested scope and gives one corrected remaining delta per row. The groupings below make the 53 results navigable without promoting a component fixture to Anneal behavior.

| IDs | Review decision and exact remaining class |
| --- | --- |
| I107–I112 | Partial. Real Cargo ownership, OS locks, FD exhaustion, direct Lean restart/edit storms, and LSP sequence controls exist. Anneal's single-flight ownership, lock graph, failure classification, restart state, fairness and missed-event reconciliation remain product gates. |
| I113–I120 | Partial. Retained byte/RSS/footprint, small worker sweeps, soak, APFS/overlayfs, pruning and preparation controls answer bounded component cells. Representative Anneal disk, latency, nested-budget, sharing and extensibility policy remain; I114–I117 also have resource or platform gates. |
| I121–I125 | Partial. Reader-owned cooperative leases, direct artifact lifetime, path-alias, APFS/overlayfs and plugin reversal fixtures exist. Anneal reader/GC ownership, repeated crash retention, workspace routing, selected platform behavior and native-extension identity remain. |
| I126–I128 | Partial. I126's build-script, proc-macro and Lean `run_cmd` execution effects were directly observed in an owned fixture. I127 has only synthetic minimization, and I128 one untrusted-text worker observation; product containment/evidence flow and independent interpretation remain. |
| I129–I135 | Partial. Direct Lean goal/trust/oracle/comparator, finite fault-model, causal barrier and interaction controls exist. Complete Anneal claim coverage, source/import/worker identity, machine status and real request races remain. I129 additionally asks for user/agent interpretation. |
| I136 | Partial with external gate. Cached 4.29/4.30 and paired Charon/Aeneas bundles were compared locally; independent host/operator and selected compatible upgrade remain. |
| I137–I138 | Complete for the issue's expressly disposable prototypes. The retained generated-model unsaved-proof and failed-intermediate/late-result transcripts meet those narrow steps. Actual Anneal parser, scheduler, editor/MCP and durable publisher are separate open product questions. |
| I139–I140 | Partial. Tiny guarded Lean worker and prior agent-task controls exist; representative parallel generated projects and matched V2 agent interface evaluation need product and resource scope. |
| I141 | Conditional. The study protocol has frozen case specifications but no product UI, consented participants or response data. |
| I142 | Partial. Small optimization comparisons exist; adoption gates need matched V2 workloads and an owner choice. |
| I143 | Conditional. Remote durability should be selected only after measured local need and explicit target/authorization. |
| I144–I146 | Partial. Decision ledgers, identity models, generation manifests and 1/2/4 retention tiers exist. An adopted V2 contract, complete cross-layer response identity, representative 8/16 retention economics and regression policy remain. |
| I147 | Partial. The prior source-only/OLean-only and unchanged-generated-output external-model controls plus this report's same-mtime and byte-identical rebuild controls answer four distinct component cells. Wider timestamps/options/native/setup identities and Anneal imported-generation policy remain. |
| I148–I150 | Partial. Pinned Charon/Aeneas process, manifest and prepared-Lake operation controls exist. Intended V2 flags, semantic text variance cost, authenticated declaration/obligation provenance and product prepared archive/RPC contract remain. |
| I151 | Partial. Conflicting same-tree Lake writers with reverse kill schedules were already executed. Matched isolation and artifact-write interruption in that shared tree, positive ownership policy and Anneal integration remain. |
| I152–I157 | Partial. Local MCP-shaped subscription/broker, direct Lean server/pool and shadow-document controls exist. Real adapters, independent editor/MCP clients, representative capacity and one structured V2 engine behind batch/live shells remain. |
| I158–I159 | Partial. The cached tuple replay and N01–N12 component falsifications exist; a selected newer compatible tuple, workaround deletion and matched alternatives inside an implemented Anneal service remain. |

The [package inventory](support/cited-package-inventory.csv) binds 123 cited report packages (including 44 `support/check.py` files) to exact report and checker hashes. The [evidence inventory](support/cited-evidence-inventory.csv) binds all 232 explicitly cited evidence files in these 53 ledger rows. Each cited path existed at review. This checks the corpus pointers and preserved bytes; the row judgments also use the package methods and stated boundaries. It does not independently reinterpret every raw transcript event in 123 packages.

### I147: same-mtime artifact replacement

The first probe built source value 7 and opened an old proof worker. It replaced `Dep.olean` with a separately valid value-9 artifact while keeping source bytes, the original artifact's nanosecond mtime, and the `.olean.hash` sidecar unchanged. Baseline OLean SHA-256 `c363ec99…` changed to `3b025404…`, while `mtime_ns` remained equal in the recorded before/after states. The old worker returned `no goals` both immediately and after a new file finished. New, reopened, and fresh-server workers each returned `⊢ selected = 7`. A fresh batch proof of `selected = 7` exited 1 with `rfl` failure and `#eval selected` reported 9. The retained `setup-file` and `--rehash setup-file` calls exited 0 and left the value-9 OLean in place. Basis: **execution** in [`i147-same-mtime/transcript.json`](support/i147-same-mtime/transcript.json) and [`fresh-batch.json`](support/i147-same-mtime/fresh-batch.json); the offline checker compares those records and both retained OLean byte strings.

The unchanged mtime makes this a distinct perturbation from the earlier older-mtime replacement. It does not prove that Lake caches in general ignore mtimes: the replacement was a deliberate valid local artifact swap under this one setup path. A second launch mode, other timestamp orderings, native plugins and an Anneal worker are outside this run.

### I147: changed source with identical compiled bytes

The second probe changed `-- model A` to the equal-length `-- model B` above `def selected : Nat := 7`. Source SHA-256 changed from `549d9af4…` to `7bf2f354…`; the Lake-built `Dep.olean` before and after the new-file/setup sequence had the same SHA-256 `45ac0f37…` and retained identical bytes. Old, new and reopened server files all returned `no goals` at the solved tactic. A fresh batch proof of `selected = 7` exited 0 and evaluated 7. Basis: **execution** in [`i147-comment-equivalence/transcript.json`](support/i147-comment-equivalence/transcript.json), its two retained OLean copies, and fresh batch record.

This is one source-only comment change with unchanged Lean semantics. It does not establish equivalence for meaningful Rust or Lean model edits, or imply that source/provenance identity may be dropped from an Anneal response. The producer's source bytes changed even though the selected artifact bytes did not.

### Corrected residuals and overlooked work

- **I151:** [`anneal-3730-lake-shared-tree-conflicting-writers-2026-09-29`](../anneal-3730-lake-shared-tree-conflicting-writers-2026-09-29/REPORT.md) already ran two real Lake processes in one writable tree after changing the shared `Dep.lean` source, killed each writer in reverse schedules, and checked fresh Lean, no-build and retry. Its offline checker passed in this review. The experiment does not establish shared-tree safety; the stale v22 clause saying this cell was untested is removed from this review's row.
- **I147:** The cited [three-launch-mode matrix](../anneal-3730-lean-launch-refresh-matrix-v4-30-0-rc2/REPORT.md) already ran source-fixed valid OLean replacement, and [E10](../anneal-3730-external-model-without-codegen-change-2026-09-29/REPORT.md) already changed a separate external Lean model while Aeneas output stayed fixed. E10's checker passed in this review. The two new controls above add exact-mtime and byte-identical-rebuild cells without changing the row status.
- **I126:** The [trust/evidence boundary fixture](../anneal-3730-trust-evidence-boundary-2026-09-29/REPORT.md) executed build-script, proc-macro and Lean command side effects; the prior residual mentioned only the separate R44 cross-tool bundle. The complete trust-entry and enforced containment question remains open.
- **I129/I148:** I129's user/agent interpretation requires a controlled evaluation in addition to the product status lattice. I148 needs the selected product flags and a measured semantic/text-cost comparison; arbitrary unselected tool options are outside its stated completion target.

The only newly executed cached-only work in this review is I147. A more exact I151 shared-tree artifact-write interruption is feasible with the cached Lake binary, but prior two-writer probes reached about 3.6 GiB sampled summed RSS and already settle the narrower historical “never tested” error. The next run should be scheduled only with a measured resource budget and a specific ownership decision it can affect. No other distinct cached-only experiment emerged from the 53 reviewed residuals; the remaining gates are listed per ID in the CSV.

## Boundaries

- The v22 status labels are preserved. “Complete” for I137/I138 is explicitly the disposable prototype specified by those issue rows, not an Anneal V2 implementation result. “Partial” can contain strong direct component evidence without completing the product question.
- The new I147 scripts adapt an existing harness. They execute one tiny imported definition on one macOS host and one Lean/Lake pin; they do not test current Anneal V2 or a cross-version migration. The fresh batch `Check.lean` records are separate from the harness's intentionally unfinished scratch theorem.
- Package/evidence inventories establish path presence and exact bytes at this checkout. They are not independent replication of every old toolchain experiment, nor a claim that a passing checker proves a report's broader interpretation.
- The issue snapshot is retained from v22 and was not refreshed; a later source edit requires a new scope comparison. Current V2 source reachability remains as reported by v22's separate source-surface package.

## Evidence

- [Per-ID review](support/row-review.csv), [cited packages](support/cited-package-inventory.csv), [cited evidence files](support/cited-evidence-inventory.csv), and [validation record](support/validation.json) preserve the 53 decisions, exact v22 baseline hashes, 123 report packages, 44 checker paths, and 232 evidence files. The inventories include report-owned hashes, not outside private workspace contents.
- [`support/build_review.py`](support/build_review.py) reconstructs the three CSVs and validation record from the frozen v22 ledger plus the five explicit residual/gate refinements. [`support/check.py`](support/check.py) validates their exact bytes, cited pointers, the retained I147 artifacts, wire outcomes, and fresh batch controls without modifying files. Selected existing checkers for I137/I138, generated-history retention, E10, shared Lake writers and real-generation publication also passed during this review.
- [`support/i147-same-mtime/`](support/i147-same-mtime/) and [`support/i147-comment-equivalence/`](support/i147-comment-equivalence/) each retain the adapted probe, full sanitized direct-server transcript, decisive OLean bytes, `Check.lean`, and fresh batch result. The scripts' copied source is in this package; the original three-mode harness remains in its own report.

## Revalidation

Run `python3 support/check.py` from this package directory. It is read-only and checks all 53 row decisions and source scopes against v22, all 123 report/metadata/checker hashes, 232 cited evidence hashes, and the two I147 executions. `python3 support/build_review.py` rewrites only this package's three CSVs and validation record if deliberate regeneration is needed. To reacquire either Lean probe, first copy its `i147-*` directory to a new owned scratch directory, set `LEAN_BIN` to the exact cached binary, and run `python3 probe.py`; the probe replaces its own `work/` and transcript. Re-run the separate fresh batch `Check.lean` oracle afterward. A new pin or product bridge requires its own report rather than broadening this dated conclusion.
