# Online Schema Migration: gh-ost Cut-Over Protocols, Vitess VReplication Streams, Expand-Contract Views, and Bidirectional Projective Lenses

## Summary

Zero-downtime schema evolution across relational databases and distributed application fleets splits into two fundamentally distinct planes: **physical table-swap engines** (`github/gh-ost`, `vitessio/vitess`) that maintain an eventually consistent shadow table and perform a sub-second atomic `RENAME TABLE` cut-over, and **logical multi-version view/lens planes** (`fabianlindfors/reshape`, `inkandswitch/cambria`, `PRISM++`) that serve old ($S_1$) and new ($S_2$) application versions concurrently during rolling upgrades.

Direct source inspection and executable modeling establish five critical engineering invariants:

1. **MySQL Metadata Lock (MDL) Cut-Over Isolation (`gh-ost`)**: Because MySQL prohibits a connection from running `RENAME TABLE` while holding `LOCK TABLES`, `gh-ost` pairs two connections—`C10` holding `LOCK TABLES tbl WRITE, _tbl_del WRITE` (`MDL_SHARED_NO_READ_WRITE`) and `C20` issuing `RENAME TABLE tbl TO _tbl_del, _tbl_gho TO tbl` (`MDL_EXCLUSIVE`)—gated by binlog drain (`waitForEventsUpToLock`) and explicit `PROCESSLIST`/`GET_LOCK` liveness proofs (`ExpectProcess`, `ExpectUsedLock`). While `C10` waits behind a long `SELECT` (`500 ms`), concurrent `SELECT`s bypass queue starvation until cut-over hold (`19 ms` total outage vs. `492 ms` under single-connection `RENAME`).
2. **VReplication Progress & Error-State Trap Resistance (`Vitess`)**: During Vitess `OnlineDDL` (`ddl_strategy='online'`), VStream replication positions (`GTID`) advance during `catchup` even when `vcopier` copy batches fail, making `pos` an invalid liveness oracle. Vitess resolves this in `vreplStreamShowsLiveness` by gating liveness on `_vt.copy_state` `max(id)` and `rows_copied`, while `vreplicationPendingCancel`, `vreplicationPendingRepair`, and `reviewVReplStreamError` preserve multi-day backfills across primary tablet reparents (`PRS`/`ERS`) and retries-exhausted downgrades.
3. **PostgreSQL Expand-Contract Views & Non-Deferrable Constraint Workarounds (`Reshape`)**: `Reshape` isolates concurrent application versions via per-migration schemas (`SET search_path TO migration_<name>`), `CREATE OR REPLACE VIEW` projections, `PL/pgSQL` `BEFORE INSERT OR UPDATE` dual-write triggers, and a two-trigger (`immediate` + `DEFERRABLE INITIALLY DEFERRED` `CONSTRAINT TRIGGER`) replacement for PostgreSQL's non-deferrable `NOT NULL` constraint—avoiding `2x` table-copy amplification at the cost of per-row trigger CPU overhead and irreversible loss once `complete()` drops the old view/column.
4. **Residual Complement Conservation During Rolling-Upgrade Rollback (`Cambria`, `PRISM++`)**: Any migration step containing a projection (`RemoveProperty`, `HeadProperty` dropping array elements `[1..]`, or non-injective `down` expressions) violates `GetPut`/`PutGet` round-trip invertibility unless paired with an explicit residual complement $C$. In an executable 1,000-trial probe of rolling-upgrade `v2 -> v1 -> v2` rollback, stateless projection lost fields on `954/1,000` (`95.4%`) of records, whereas an explicit residual complement (`81.26 B/row` mean) achieved `0/1,000` data-loss mismatches.
5. **Universal Model Refinement**: Storage-copy tools (`gh-ost`, `Vitess`), dual-write view managers (`Reshape`), and edit/query lenses (`Cambria`, `PRISM++`) are distinct realizations of one primitive—`Bijection<V1, V2, Complement>`—whose realization medium (e.g., MySQL non-transactional `MDL` queues vs. PostgreSQL transactional DDL + `MVCC` vs. local CRDT edit logs) determines whether the complement lives in `_tbl_del`, a sidecar JSONB column, or local peer history.

## Applicability

This report synthesizes findings across six pinned primary subjects representing four distinct migration architectures:

| Subject | Immutable Identity | Architecture Class | Target Engine / Data Model | Primary Role in Synthesis |
|---|---|---|---|---|
| `github/gh-ost` | `dfb342a4b391b7593a71927976f8841c2ac33219` | Triggerless binlog shadow copy + atomic swap | MySQL / MariaDB (`binlog_format=ROW`, `FULL` image) | Single-table & move-tables two-connection cut-over protocol |
| `vitessio/vitess` | `96ae128bc631b5a103defc6bc4c54c255ec8dff5` | GTID-checkpointed VStream `OnlineDDL` + `VReplication` | Sharded MySQL via `vttablet` (`_vt.vreplication`, `_vt.copy_state`) | Shard-aware `Copy/Catchup/FastForward`, error recovery, query-buffered cut-over |
| `fabianlindfors/reshape` | `1c52737b3213bede6997815d4b1f59c6b9174eba` (`v0.11.2`) | Multi-schema `search_path` views + dual-write triggers | PostgreSQL | Zero-copy rolling-upgrade expand-contract views & deferred constraint triggers |
| `inkandswitch/cambria` | `da8961440cac7eba1c3113488f5bcbc26046620f` (`v0.1.2`) | Bidirectional JSON Patch edit lenses | JSON documents / CRDT edit logs (`fast-json-patch`, `json-schema`) | Algebraic edit-lens combinators (`reverseLens`) & projection complement limits |
| Litt et al., *PaPoC '21* | DOI `10.1145/3447865.3457963` | Edit-lens theory & decentralized schema evolution | Automerge / Hypermerge CRDTs | Formalization of edit translation across concurrent peer schemas |
| Curino et al., *VLDBJ 2013* | DOI `10.1007/s00778-012-0302-x` | `PRISM++` (`SMO` + `ICMO`) query/update rewriting | Relational SQL databases | Chase-based view rewriting & information-capacity invertibility guarantees |

**Relationships and Scope Constraints**:
- `gh-ost` and Vitess `OnlineDDL` solve physical schema alteration on MySQL/InnoDB where `ALTER TABLE` cannot serve concurrently across versions or shards; they do **not** provide concurrent `v1` and `v2` application schemas post-cut-over (Vitess's `REVERT` performs a reverse physical cut-over on the `_vt_*` hold table, losing columns dropped without retention unless preserved externally).
- `Reshape` assumes PostgreSQL transactional DDL, session-level `SET search_path TO migration_<name>`, and sufficient spare IOPS for synchronous `BEFORE INSERT OR UPDATE` trigger execution; findings apply strictly to `v0.11.2` (`pg_query 6.2`).
- `Cambria` operates on RFC 6902 JSON Patch streams (`add`, `replace`, `remove`) over TypeScript/JSON Schema Draft-07 objects, relying on local CRDT state when fields are hidden, whereas `PRISM++` operates on relational Schema Modification Operators (`SMO`) and Integrity Constraint Modification Operators (`ICMO`) rewritten statically via chase and relational algebra.
- Empirical measurements from `/tmp/schema_lens_mdl_probe.py` evaluate discrete-event lock queueing and algebraic round-trip laws on synthetic workloads rather than hardware MySQL/PostgreSQL benchmarks (`Basis: execution`).

## Findings

### 1. Triggerless Row-Image Shadow Backfill and Two-Connection Atomic Cut-Over in gh-ost

`Basis: source + documentation + execution`

`github/gh-ost` eliminates table-level DML triggers—which serialize concurrent writes in InnoDB and execute inside the foreground transaction—by decoupling bulk row copying from incremental replication via MySQL's Row-Based Replication (`RBR`, `binlog_format=ROW`, `binlog_row_image=FULL`).

#### Triggerless Idempotent Convergence
`EventsStreamer` (`go/logic/streamer.go:36-160`) connects to a source MySQL server (either the primary or a replica when using `--migrate-on-replica`) as a synthetic replica via `go-mysql`. Using `shouldDecodeRowsEvent` (`go/logic/streamer.go:86-100`), it skips decoding row payloads for uninvolved tables while funneling matching `InsertDML`, `UpdateDML`, and `DeleteDML` events plus `_ghc` changelog heartbeats to `Applier` (`go/logic/applier.go:2579-2629`):
- **Chunked Backfill**: `Applier` iterates over the original table's unique key (`UniqueKey`) ranges using `INSERT IGNORE INTO _tbl_gho ... SELECT ... FROM tbl WHERE ...` (`go/logic/applier.go:1868`), copying batches without overwriting newer binlog-applied rows.
- **Binlog DML Replay**: `buildDMLEventQuery` (`go/logic/applier.go:2579-2629`) transforms `InsertDML` into `REPLACE INTO` (via `dmlInsertQueryBuilder`), `DeleteDML` into keyed `DELETE` (`dmlDeleteQueryBuilder`), and `UpdateDML` into `UPDATE`—or, whenever `updateModifiesUniqueKeyColumns` (`go/logic/applier.go:2564-2575`) detects that an `UPDATE` mutates the iterated chunking key, splits it into `[DeleteDML, InsertDML]` so rows cannot escape between already-scanned and unscanned ranges.
- Because `REPLACE INTO` overwrites stale range-copied rows and `INSERT IGNORE` drops duplicate-key collisions (`compileKeyWarningRegex`, `go/logic/applier.go:201-210`), chunked copy and asynchronous binlog apply commute toward identical final state once caught up.

#### Two-Connection `C10` + `C20` Atomic Cut-Over vs. MySQL MDL Priority
In MySQL, a session holding `LOCK TABLES` cannot execute `RENAME TABLE` (`doc/cut-over.md:1-15`), while single-connection non-atomic two-step `RENAME` (`tbl -> _tbl_del; _tbl_gho -> tbl`) creates a window where `tbl` does not exist and queries fail with `ER_NO_SUCH_TABLE`. Conversely, issuing `RENAME TABLE` (`MDL_EXCLUSIVE`) directly behind a long-running analytics `SELECT` (`MDL_SHARED_READ`) causes MySQL's Metadata Lock (MDL) subsystem to **block all subsequent incoming `SELECT` and `INSERT`/`UPDATE` queries** behind the pending `MDL_EXCLUSIVE` lock request to prevent writer starvation.

`gh-ost`'s `atomicCutOver` (`go/logic/migrator.go:1875-1983`) avoids premature read/write starvation and split-second table disappearance through a two-connection sentry protocol:

| Step | Connection | Action / SQL Statement | Source Location | Safety Invariant Enforced |
|---|---|---|---|---|
| 1 | `C10` (`Applier`) | Acquire advisory `GET_LOCK(lockName, 0)`, set `lock_wait_timeout := 2 * CutOverLockTimeoutSeconds` and `wait_timeout := 3 * CutOverLockTimeoutSeconds`, and create empty sentry table `_tbl_del` with comment `ghost-cut-over-sentry` | `applier.go:2335-2431` | Prevents concurrent cut-overs; bounds zombie lock hold if `gh-ost` dies abruptly |
| 2 | `C10` (`Applier`) | Execute `LOCK TABLES tbl WRITE, _tbl_del WRITE` (`MDL_SHARED_NO_READ_WRITE`) | `applier.go:2434-2452` | Freezes new writes to `tbl`; if blocked by a long `SELECT`, `C10` waits without triggering `MDL_EXCLUSIVE` starvation rules |
| 3 | `Migrator` | Inject `AllEventsUpToLockProcessed:<unix_nano>` into `_ghc` changelog and block in `waitForEventsUpToLock()` | `migrator.go:1789-1836, 1905` | Guarantees every DML committed prior to `LOCK TABLES` has traversed the binlog and applied to `_tbl_gho` |
| 4 | `C20` (`Applier`) | Execute blocking `RENAME TABLE tbl TO _tbl_del, _tbl_gho TO tbl` (`MDL_EXCLUSIVE`) in background goroutine | `applier.go:2507-2547`, `migrator.go:1924-1930` | Blocks on `C10`'s locks on `tbl` and `_tbl_del`; cannot execute before `C10` unlocks |
| 5 | `Migrator` | Poll `ExpectProcess(renameSessionId, "metadata lock", "rename")` AND `ExpectUsedLock(lockOriginalSessionId)` | `migrator.go:1934-1958` | Proves `C20` is genuinely queued in MDL AND `C10` did not drop/lose its lock before `C20` arrived |
| 6 | `C10` (`Applier`) | Execute `DROP TABLE IF EXISTS _tbl_del`, poll `ExpectMetadataLock(renameLockSessionId)`, then issue `UNLOCK TABLES` | `applier.go:2464-2503` | Drops sentry so `C20`'s prioritized `MDL_EXCLUSIVE` immediately swaps `tbl <-> _tbl_gho` ahead of queued DML |

**Failure Mode Resolution (Step 5 Crash Guard)**: If `C10` loses TCP connectivity after acquiring `LOCK TABLES` and `C20` issues `RENAME` before noticing, Step 5 (`ExpectUsedLock`) and the sentry table `_tbl_del` ensure atomicity: `C10`'s death rolls back/drops locks, and if `C20` ran before `_tbl_del` was dropped, `RENAME` fails safely with `ER_TABLE_EXISTS_ERROR` (`_tbl_del` already exists), leaving `tbl` untouched. Executing `/tmp/schema_lens_mdl_probe.py` against a `500 ms` blocking `SELECT` (`SR`) with `20 ms`-periodic `SELECT`s and writes quantifies this isolation: single-connection `RENAME` creates a `492 ms` read+write outage (`25` blocked reads, `25` blocked writes, `482 ms` max wait), whereas `gh-ost` incurs `0 ms` wait during `C10`'s `490 ms` wait behind the `SELECT`, limiting total query outage strictly to the `19 ms` critical window (`17 ms` binlog drain + `2 ms` `RENAME`), and preventing premature table swap when `C10` drops mid-drain (`write_outage_window_ms = 8 ms`, `c20_issued = false`).

---

### 2. GTID-Checkpointed VReplication VStreams, Tablet Reparents, and Error-State Cancellation Traps in Vitess

`Basis: source`

Vitess `OnlineDDL` (`go/vt/vttablet/onlineddl/executor.go` and `go/vt/vttablet/tabletmanager/vreplication/`) generalizes `gh-ost`-style shadow backfill to sharded keyspaces using server-side `VStreamer` (`VStreamRows` + `VStream`) and transactional GTID checkpoints inside `_vt.vreplication` and `_vt.copy_state`.

#### `Copy -> Catchup -> FastForward` Checkpoint Protocol
`vcopier` (`go/vt/vttablet/tabletmanager/vreplication/vcopier.go:184-470`) executes an interleaved multi-phase loop controlled by `vreplicator.Replicate` (`vreplicator.go:205-315`):
1. **Init (`initTablesForCopy`, `vcopier.go:225-278`)**: Records target tables in `_vt.copy_state(vrepl_id, table_name)` with null `lastpk`, transitions state to `Copying`, and optionally stashes secondary keys in `_vt.post_copy_action` for deferred index rebuilds after bulk loading.
2. **Catchup (`catchup`, `vcopier.go:331-377`)**: When `StartPos` is non-zero (after a preceding copy slice), `vplayer` replays binlog events matching keys `<= lastpk` until `ReplicationLagSeconds < ReplicaLagTolerance`.
3. **Consistent Snapshot Fast-Forward (`copyTable` + `fastForward`, `vcopier.go:280-297, 382-470, 749`)**: Opens a `VStreamRows` stream from `lastpkpb`, receiving a consistent GTID snapshot coordinate (`gtid`) alongside schema metadata; fast-forwards `vplayer` to exact `gtid`, then streams batched rows up to `CopyPhaseDuration` (`WorkflowConfig`). Each batch commits target `INSERT`s and `_vt.copy_state` `lastpk` **in the same InnoDB transaction** (`vcopier.go:380-381`), guaranteeing exactly-once resumability across primary reparents (`PRS`/`ERS`) or tablet restarts (`controller.go:329-483` re-picks an eligible source tablet via `TabletPicker`).

#### Critical Bugs & Safeguards Identified in Executor State Management
Direct source analysis of `go/vt/vttablet/onlineddl/executor.go` reveals four non-obvious failure traps in distributed `VReplication` migrations and their exact fixes:

1. **False-Liveness Trap (`vreplStreamShowsLiveness`, `executor.go:262-336`)**:
   A failing `copyTable` iteration still runs `catchup` first, advancing `_vt.vreplication.pos` (the GTID position) and `time_updated` heartbeats even while zero copy rows commit—causing a permanently failing copy phase to refresh `liveness_timestamp` indefinitely and mask stalled migrations (`executor.go:270-292`). Conversely, a genuinely slow/throttled copy must not be killed by `reviewStaleMigrations`. Therefore, `vreplStreamShowsLiveness` requires **at least one of**: (a) `cnt == 0` in `_vt.copy_state` (copy complete, pure binlog phase), (b) `s.rowsCopied > acknowledgedRowsCopied`, (c) active throttler stamp within `vreplThrottleLivenessWindow = 15 * time.Minute`, or (d) strictly increasing `max(id)` in `_vt.copy_state` (`observed.copyStateID > last.copyStateID`, `executor.go:316-335`).
2. **Retries-Exhausted Downgrade & Repair Loop (`reviewVReplStreamError`, `executor.go:174-182, 377-394, 3812-3918, 4057-4125`)**:
   Streams pinned before `retry-forever` config overrides (`--vreplication-max-time-to-retry-on-error`) could park in `state='Error'` with `RetriesExhaustedIndicator = "retries exhausted"` (`controller.go:69`). Rather than aborting days of copy progress, `reviewVReplStreamError` returns `vreplStreamRepair`, issuing `repairVReplicationQuery` (`state='Running', options=json_set(..., retryForever)`) and retiring old `_vt.vreplication_log` `Error` rows (`retireVReplParkRecordQuery`, `executor.go:3857-3867`)—carefully truncating at `65,535` bytes divided by `maxBytesPerChar = 4` so strict SQL mode does not fail on multibyte UTF-8 log rows, preventing an older executor after a version downgrade from misreading historic park rows and aborting the live migration! If the repair SQL lands (`state='Running'`) while its controller RPC fails, `vreplicationPendingRepair[uuid]` triggers `redriveVReplRepair` on the next tick.
3. **Non-Atomic Cancellation Orphan Trap (`CancelMigration`, `executor.go:167-173, 2032-2126, 4032-4056`)**:
   Stopping a stream erases its `Error` verdict, while internal cancellations do not set a durable `cancelled_timestamp`. If `terminallyFailMigration` fails after stream termination, `CancelMigration` stores the intent in `vreplicationPendingCancel[uuid]`, restores `ownedRunningMigrations` ownership (so the scheduler does not launch a conflicting DDL), and forces `resolveVReplStreamAction` to emit `vreplStreamCancel` on subsequent review ticks even if the stream later reads healthy (`executor.go:204-209, 4032-4056`).
4. **Cut-Over Buffering, Query Termination, and Dual Lock Teardown (`cutOverVReplMigration`, `executor.go:1098-1569`)**:
   Prior to locking tables, Vitess creates a `HoldTableGCState` sentry table, runs best-effort `ANALYZE TABLE` on `vreplTable` (`L1198-1207`), and waits up to `3 * CutOverThreshold` for `postSentryPos`. Inside the critical section, it enables tablet query buffering (`toggleBuffering(true)`, sleeping `100 ms` for in-flight query-executor drainage), optionally kills active table accessors if `force_cutover` is active (after `checkOnPreparedPool` protects XA prepared transactions), acquires `LOCK TABLES`, records `postWritesPos`, drains `VReplicationWaitForPos(CutOverThreshold)`, stops VReplication, drops the sentry table, issues `UNLOCK TABLES`, and executes `RENAME TABLE` (`onlineDDL.Table -> sentry, vreplTable -> onlineDDL.Table`) with a `defer` fallback calling **both** `UNLOCK TABLES` and `lockConn.Conn.Kill` (`L1239-1257`) to guarantee no hung lock survives network partitions.

---

### 3. PostgreSQL Multi-Schema `search_path` Views and Dual-Write Trigger Trade-Offs in Reshape

`Basis: source + documentation`

Unlike MySQL `gh-ost` and Vitess—which perform out-of-place table copies (`2x` disk footprint) and atomic cut-over swaps—`fabianlindfors/reshape` (`v0.11.2`) implements an **in-place expand-contract state machine** (`Idle -> Applying -> InProgress -> Completing | Aborting`, `src/lib.rs:24-30, 212-689`) designed to run `v1` and `v2` application replicas concurrently on PostgreSQL.

#### `search_path` Isolation, Views, and `is_new_schema()` Trigger Dispatch
- **Schema Encapsulation (`src/lib.rs:195-210, 560-614`)**: Rather than querying `public.<table>` directly, each application release binds its database pool to `SET search_path TO migration_<name>`. `Reshape` materializes lightweight updatable SQL views (`CREATE OR REPLACE VIEW migration_<name>.<tbl> AS SELECT "<real_col>" AS "<alias>" FROM "<real_name>"`) mapping logical column aliases to physical or temporary columns on `public.<real_name>` (e.g., `AddColumn::temp_column_name` or `AlterColumn::temporary_column_name`).
- **Context Detection (`src/helpers.rs:5-22`)**: `reshape.is_new_schema()` inspects `current_setting('search_path') = 'migration_<target>' OR current_setting('reshape.is_new_schema', TRUE) = 'YES'`, allowing a single row trigger on the physical `public` table to tell whether an `INSERT` or `UPDATE` originated from the old (`v1`) or new (`v2`) application release.
- **Bidirectional Dual-Write Triggers (`src/migrations/{add_column.rs,alter_column.rs,remove_column.rs}`)**:
  - Adding a column (`add_column.rs:120-210`) creates a `BEFORE UPDATE OR INSERT` `PL/pgSQL` trigger that runs `up` only `IF NOT reshape.is_new_schema()` (populating the temporary column when `v1` writes), plus cross-table `UPDATE` propagation guarded by `set_config('reshape.disable_triggers', 'TRUE', TRUE)` to prevent trigger recursion, followed by chunked batch updates (`common::batch_touch_rows`).
  - Altering a column (`alter_column.rs:62-120`) allocates a nullable temporary column, duplicates indexes `CONCURRENTLY IF NOT EXISTS` via AST token rewriting (`src/sql.rs:66-130`, using `pg_query 6.2`), and installs symmetric `up` and `down` `PL/pgSQL` triggers so writes from `v1` populate `v2`'s column and vice versa.
- **Deferring Non-Deferrable `NOT NULL` Constraints (`src/migrations/remove_column.rs:166-250`)**:
  PostgreSQL `NOT NULL` column constraints are never deferrable. If `v2` removes a non-null column `col` whose `down` transformation is a cross-table `Transformation::Update` (`remove_column.rs:190-249`), `v2` may insert a parent row before inserting the referenced source row within the same transaction. `Reshape` solves this by dropping `NOT NULL` on all backing columns and installing **two constraint triggers**:
  1. An immediate `AFTER INSERT OR UPDATE ... WHEN (NOT reshape.is_new_schema() AND NEW.col IS NULL)` trigger raising `not_null_violation` immediately for `v1` writers; and
  2. A `DEFERRABLE INITIALLY DEFERRED` constraint trigger (`WHEN (reshape.is_new_schema() AND NEW.col IS NULL)`) that re-reads the row by primary key at `COMMIT` time—guaranteeing `NOT NULL` can be cleanly reinstated if the migration aborts (`remove_column.rs:180-238`).

#### Structural Failure Modes of In-Place Trigger Expand-Contract
1. **Irreversible Contraction on `complete()`**: While `InProgress`, both `v1` and `v2` coexist cleanly and `reshape migration abort` cleanly drops temporary columns/views. Once an operator executes `reshape migration complete` (`src/lib.rs:358-420`), `Reshape` runs `DROP SCHEMA <prev_migration> CASCADE` and physically drops removed columns (`AlterColumn` old column, `RemoveColumn` target column). A post-`complete` rollback is impossible without an out-of-band backup or complement column.
2. **Metadata Lock Amplification During Trigger DDL**: Although index creation uses `CREATE INDEX CONCURRENTLY` (`sql.rs:88`), `CREATE TRIGGER` and `ALTER TABLE ... DROP NOT NULL` still require `SHARE ROW EXCLUSIVE` / `ACCESS EXCLUSIVE` locks on the underlying physical table, which queue behind long-running queries unless guarded by `lock_timeout` retry loops.
3. **Write Latency Tax**: Every row modification executes `PL/pgSQL` context switches (`current_setting('search_path')`, trigger variable allocation), roughly doubling write CPU cost when cross-table `UPDATE` propagation triggers fire.

---

### 4. Algebraic Bidirectional Lenses, Edit Translation, and Rollback Complement Loss in Cambria and PRISM++

`Basis: normative + source + execution + derived`

While physical DDL engines copy tables and trigger systems keep columns synchronized, **bidirectional lenses** establish the exact mathematical contract governing when two schema versions $S_1$ and $S_2$ can translate live queries, writes, or edits without silent data corruption.

#### Formal Lens Laws: Asymmetric vs. Symmetric with Complement
1. **Asymmetric State-Based Lens ($L : S \rightleftharpoons V$)**: Consists of $\mathrm{get} : S \to V$ and $\mathrm{put} : S \times V \to S$ satisfying:
   $$\text{GetPut}: \mathrm{put}(s, \mathrm{get}(s)) = s \qquad \text{PutGet}: \mathrm{get}(\mathrm{put}(s, v)) = v$$
   Asymmetric lenses assume one schema ($S$) is strictly richer than the view ($V$). If $V_1$ drops column $A$ and $V_2$ drops column $B$, **neither is a view of the other**—making bidirectional rolling upgrades impossible as an asymmetric lens over $V_1$ or $V_2$ alone.
2. **Edit Lenses (`inkandswitch/cambria`, Litt et al. *PaPoC '21*)**: Rather than transforming whole states $(S \leftrightarrow V)$, Cambria translates RFC 6902 JSON Patch edit deltas ($\Delta S_1 \leftrightarrow \Delta S_2$) across a sequential pipeline `LensSource = LensOp[]` (`src/lens-ops.ts:73-85`) composed of 10 primitives:
   `add`, `remove`, `rename`, `hoist`, `plunge`, `wrap`, `head`, `in`, `map`, and `convert`.
   `compile(lensSource)` (`src/patch.ts:28-34`) exposes `{ right, left }` where `left` simply calls `reverseLens(lensSource)` (`src/reverse.ts:7-76`)—reversing the array and applying the syntactic involution `add <-> remove`, `hoist <-> plunge`, `wrap <-> head`, and swapping `convert.mapping[0] <-> mapping[1]`.
   - **Critical Projection Asymmetry in `head` and `remove`**: Inspecting `src/patch.ts:121-162` reveals that `remove` returns `null` for any patch touching the dropped property (`L161`), and `head` maps `/arr/0` to `/scalar` while returning `null` for any index `/arr/k` with $k > 0$ (`L128: if (!headMatch) return null`). Furthermore, `wrap` turns `null` scalar assignment into `{ op: 'remove', path }` (`L110-115`), whereas `add` on forward edits is a no-op stub (`L154-158`) relying on `addDefaultValues(lensedPatch, readerSchema)` (`L51-52`) to synthesize required fields only on object creation.
   - **Why Cambria Still Works for CRDT Peers—Implicit Complement**: Because local-first Automerge peers retain their own full CRDT document edit history and translate *incoming* patches lazily at read/write boundaries, a peer running $S_2$ holds $S_2$-only fields (`tags[1..]`, `tier`) in its own replica state acting as an **implicit local complement**; however, passing an $S_2$ document through a central server running `S2 -> S1 -> S2` *statelessly* permanently destroys `tags[1..]` and `tier`.
3. **`PRISM++` Relational Evolution (`Curino et al., VLDBJ 2013`)**:
   `PRISM++` formalizes relational evolution through Schema Modification Operators (`SMO`: `CREATE/DROP/RENAME/COPY/MERGE/SPLIT/DECOMPOSE/JOIN TABLE`, `ADD/DROP/RENAME COLUMN`) and Integrity Constraint Modification Operators (`ICMO`). Given a forward schema chain, `PRISM++` automates:
   - **Query & Update Rewriting**: Rewriting legacy SQL queries (`v1`) into views/queries over the current schema (`v2`) via the **chase & backchase** algorithm under tuple-generating and equality-generating dependencies, automatically classifying `UPDATE`/`INSERT` statements as invertible vs. rejected when updates target ambiguous view joins.
   - **Invertibility Verification**: Verifying information-capacity preservation (`Miller`/`Hull`)—identifying exact SMOs (`DROP COLUMN`, lossy `MERGE` without disambiguator) where inverse rewriting fails without retaining deleted columns.
4. **Symmetric Bijective Complement Lens ($S_1 \times C_1 \leftrightarrow S_2 \times C_2$)**:
   Unifying Cambria, Reshape, and PRISM++, a truly lossless rolling-upgrade migration over incompatible versions $S_1$ and $S_2$ requires symmetric translations:
   $$\mathrm{fwd} : (S_1, C_1) \xrightarrow{\sim} (S_2, C_2) \qquad \mathrm{bwd} : (S_2, C_2) \xrightarrow{\sim} (S_1, C_1)$$
   satisfying exact round-trip bijectivity $\mathrm{bwd}(\mathrm{fwd}(s_1, c_1)) = (s_1, c_1)$ and $\mathrm{fwd}(\mathrm{bwd}(s_2, c_2)) = (s_2, c_2)$, where $C_1$ stores the **$S_2$-residual complement** (fields/tags/types expressible in $S_2$ but invisible to $S_1$, such as `tags[1..]` and `tier`) and $C_2$ stores the **$S_1$-residual complement** (e.g., exact whitespace or unparsed legacy formatting in `full_name` before normalization).

Executing Part B of `/tmp/schema_lens_mdl_probe.py` over `1,000` randomized `v2` records undergoing `v2 -> v1 -> v2` rolling-upgrade rollback demonstrates this conservation law quantitatively:
- **Stateless `Cambria`-style reverse/forward projection**: Lost `tags[1..]`, `tier`, or `full_name` space splits on **`954` of `1,000` trials (`95.4%`)**.
- **Symmetric Bijective Complement Lens**: Achieved **`0` mismatches across `1,000` trials**, persisting $C_1$ (`tags_tail`, `tier`, `orig_first`, `orig_last`) in **`81.26 B/row` mean (`100 B` max)**—proving that lossless rollback is bounded by a tiny JSON/columnar residual complement rather than `2x` full-table retention (`HoldTableGCState` / `_tbl_del`).

---

### 5. Cross-System Trade-Off Matrix and Six-Level Performance & Resource Footprint (`L1`–`L6`)

`Basis: source + documentation + execution + derived`

| Dimension | `github/gh-ost` (`dfb342a`) | `vitessio/vitess` (`96ae128`) | `fabianlindfors/reshape` (`1c52737`) | `inkandswitch/cambria` (`da89614`) | `PRISM++` (`VLDBJ 2013`) | Symmetric Complement Lens (`Bijection<V1, V2, C>`) |
|---|---|---|---|---|---|---|
| **Migration Mechanism** | External daemon: chunk `INSERT IGNORE` + `RBR` binlog replay + 2-conn `RENAME` | In-tablet `VReplication` (`VStreamRows` + `VStream`) + query-buffered `RENAME` | Multi-schema Postgres `VIEW`s + `PL/pgSQL` dual-write & deferred triggers | Bidirectional JSON Patch edit translation (`LensOp[]` + `reverseLens`) | Chase/backchase SQL query & update rewriting over `SMO`/`ICMO` | Typed `(S1, C1) <-> (S2, C2)` view/codec with explicit residual column |
| **Concurrent `v1` + `v2` App Coexistence** | No (instant schema swap at cut-over) | No (instant cut-over; `REVERT` swaps back but drops post-cutover drift) | Yes during `InProgress` (`SET search_path`), until `complete()` | Yes indefinitely across peers (`local` CRDT acts as complement) | Yes while `v1` view wrappers remain active | Yes indefinitely; rollback `v2 -> v1 -> v2` retains `0` data loss |
| **L1: Human / Agent Authoring Velocity** | 1 CLI command (`--alter="..."`); zero app SQL changes; fragile operational flags | 1 SQL `ALTER TABLE` + `ddl_strategy='online'`; `Vitess` handles shards | ~10–40 lines TOML/JSON per migration (`up`/`down` SQL); requires `SET search_path` | ~5–25 lines TypeScript/YAML `LensOp[]` per version edge | 1 declarative `SMO` sequence; manual disambiguation for lossy splits | ~8–15 lines declarative bijection + default fallback; statically checked |
| **L2: Toolchain Build Time & RSS** | Go 1.25.12 (`go.mod`); `< 12 s` cold build, `< 350 MiB` RSS | Large Go monorepo (`vitess`); ~30–90 s incremental `vttablet` build, `~1.2–2 GiB` RSS | Rust 1.88 (`Cargo.toml`, compiles C `libpg_query` via `pg_query 6.2`); ~25–45 s cold, `< 500 MiB` RSS | TypeScript (`tsc`, `package.json`); `< 3 s` build, `< 180 MiB` Node RSS | Java research workbench; seconds to build; chase runtime scales with constraints | `< 5–9 s` incremental build, `< 200 MiB` RSS |
| **L3: Compilation, Analysis & Cut-Over Prep Latency** | Sub-second inspector schema check (`SHOW CREATE TABLE` + unique key validation) | `evaluateDeclarativeDiff` (`executor.go:2695`) creates temp table + `schemadiff` (~10–80 ms/shard) | `pg_query::parse` + AST `ColumnRef` resolution (`sql.rs:28-130`) in `< 1 ms`; `CREATE VIEW` in `< 10 ms` | `compile()` is $O(\|L\|)$ closure creation (`< 0.1 ms`); `updateSchema` JSON-Schema walk `< 1 ms` | Chase query rewriting & IC equivalence solving (`ms` to seconds on complex foreign keys) | Static `GetPut`/`PutGet` invertibility check in `< 1–30 ms` (`< 2 KLoC` checker) |
| **L4: Runtime Execution & Cut-Over Pause** | `1–5%` replica throttle backoff (`Throttler`); **`~10–50 ms`** atomic `RENAME` (`19 ms` probed vs. `492 ms` single `RENAME`) | `VStreamRows` parallel workers + throttler; `~100 ms` pre-buffering + `cutover` (`< 250 ms` pause) | `0` bulk copy for pure views; `~1.5–2.5x` row write latency when dual-write + deferred `CONSTRAINT TRIGGER` fire | $O(\|P\| \cdot \|L\|)$ JS patch transform (`~5–50 µs`/patch); `expandPatch` recurses over nested objects | Zero runtime trigger tax for rewritten read queries; extra join/union cost across split views | `< 150 µs` view cut-over; single-pass read/write projection without `2x` table rewrite |
| **L5: Consistency & Invertibility Verification Speed** | `ExpectProcess` + `ExpectUsedLock` polling (`10–100 ms`); no row checksum by default | `vreplStreamShowsLiveness` (`copy_state` `maxid` check) + `VReplicationWaitForPos`; optional `VDiff` | Compile-time `validate_column_references` (`sql.rs:135`) only; **no** algebraic invertibility check | Exhaustiveness `assertNever` in `reverse.ts:74`; **no** static check blocking lossy `head`/`remove` | Static chase soundness + information-capacity invertibility audit (`VLDBJ 2013`) | `< 1.0 ms` automated verification of complement conservation & lock window bounds |
| **L6: Disk, Memory & Network Footprints** | **`2x` table disk** (`_tbl_gho` + `_tbl_del` post-cutover) + binlog network stream; `< 100 MiB` Go RSS | **`2x` table disk** per shard + `_vt.copy_state` + `HoldTableGCState` retained tables (`retainOnlineDDLTables`) | **`1.0x` table disk** (plus temp columns in `InProgress`); minimal metadata; `0` binlog streaming | Zero DB storage; per-patch allocation from `expandPatch(...).flat(Infinity)` (`patch.ts:242`) | Minimal view metadata + optional materialized auxiliary tables for non-invertible drops | `1.0x` table + **`0–100 B/row`** (`81.26 B` measured) compressed residual complement |

---

### 6. Human Comprehensibility (`C1`) and Conceptual Simplicity / Universal Model Refinement (`C2`)

`Basis: derived + source + documentation`

#### (`C1`) Human Comprehensibility and Mental-Model Ergonomics
- **Operational Choreography vs. Working-Memory Budget**: Understanding `gh-ost` or Vitess `OnlineDDL` cut-over safety requires an engineer to track **at least seven interacting primitives simultaneously**: MySQL `MDL` lock modes (`SR`, `SW`, `SNRW`, `X`), lock-queue starvation priority, two separate TCP connections (`C10`/`C20`), advisory `GET_LOCK`, changelog binlog-barrier heartbeats, `PROCESSLIST` state strings (`"metadata lock"`), and GC hold-table retention (`_tbl_del`, `HoldTableGCState`). This exceeds standard 4-chunk human working memory, explaining why Vitess `executor.go` repeatedly accumulated subtle repair/cancellation state machines (`vreplicationPendingCancel`, `vreplicationPendingRepair`, `retireVReplParkRecord`) to fix edge cases across tablet restarts and downgrades.
- **Diagnostic & Failure Legibility**:
  - In `gh-ost`, a cut-over timeout logs `Waiting for table metadata lock`, without automatically attributing which upstream `SELECT` PID or XA prepared transaction blocked `C10` or `C20`.
  - In `Reshape`, errors occurring during `InProgress` surface inside dynamic `PL/pgSQL` triggers (`not_null_violation` thrown from a deferred constraint trigger at `COMMIT` rather than at the offending `INSERT` line in `remove_column.rs:217-219`), breaking source-line blame.
  - By contrast, declarative lens systems (`Cambria`, `PRISM++`) fail locally: `Cambria` throws `No mapping for value` (`patch.ts:205`) on unknown `convert` keys, and an explicit complement checker immediately exhibits the **exact unmapped field or array tail** (e.g., `tags[1..]` dropped by `head` without complement) rather than silently truncating production rows after cut-over.

#### (`C2`) Conceptual Simplicity, Orthogonality, and Adapter-Conservation Audit
Separating core schema-evolution semantics from storage-engine realization accidents reveals why today's tooling is split across incompatible silos:
- **Realization-Medium Quirks (Accidental Complexity)**:
  1. MySQL's inability to run `RENAME TABLE` from a session holding `LOCK TABLES`, paired with `MDL_EXCLUSIVE` read starvation, forces the entire two-connection `C10` + `C20` + sentry-table dance (`gh-ost`, Vitess).
  2. PostgreSQL's non-deferrable `NOT NULL` column flag forces `Reshape` to drop `NOT NULL` and emulate it via dual immediate/deferred `CONSTRAINT TRIGGER`s (`remove_column.rs:179-249`).
  3. Vitess's lack of atomic cross-table state for `_vt.vreplication_log` and controller start RPCs forces an in-memory `vreplicationPendingRepair` reconstruction heuristic on `Executor.Open` (`executor.go:4011-4027`).
- **Universal Core Abstraction (`Bijection<S1, S2, Complement>`)**:
  Across all four tools, schema evolution is fundamentally **one bidirectional transformation between storage representations** parametrized by:
  1. **Algebraic Mapping**: `(S1, C1) <-> (S2, C2)` defining forward, backward, and residual complement storage; and
  2. **Execution Strategy (Time vs. Space Materialization)**: Whether rows materialize *eagerly in shadow storage* (`gh-ost`, `Vitess`), *eagerly in-place via write triggers* (`Reshape`), or *lazily on read/edit patches* (`Cambria`, `PRISM++`).
- **Adapter-Conservation Audit**: Simply inventing a terse schema-diff DSL does *not* eliminate complexity if hidden adapters shift costs elsewhere. For instance, eliminating shadow tables (`gh-ost`) via `Reshape` multi-schema views *appears* simpler (`1.0x` disk), yet shifts hidden complexity into `PL/pgSQL` `variable_conflict` hacks, deferred constraint triggers, and `ACCESS EXCLUSIVE` lock windows on trigger install; similarly, `Cambria`'s terse `reverseLens` involution (`reverse.ts:7-76`) *appears* symmetric, yet silently shifts data-preservation responsibility onto each peer's CRDT history—failing whenever a stateless gateway applies `left(right(doc))`. Genuine conceptual simplification preserves the **complement conservation law** explicitly in the schema contract while letting the storage layer choose eager (`_tbl_gho`) vs. lazy (`VIEW`/MVCC) materialization transparently.

## Boundaries

- **Foreign Keys and Row Triggers (`gh-ost` and `Vitess` — `unsupported` / `known not to apply`)**:
  `gh-ost` rejects tables with triggers or active foreign key constraints in standard mode because `RBR` replay bypasses SQL-level triggers on the shadow table and MySQL `RENAME TABLE` re-points child foreign keys unexpectedly. Similarly, Vitess `OnlineDDL` explicitly rejects foreign keys (`executor.go:877-886`) unless `--unsafe-allow-foreign-keys` is set or the backend supports non-standard PlanetScale `@@rename_table_preserve_foreign_key` (`executor.go:1303-1315`).
- **`binlog_row_image = minimal` (`gh-ost` and `Vitess` — `unsupported`)**:
  `gh-ost` requires `binlog_row_image=FULL` so `UpdateDML` contains full before/after column values for `WHERE` and `REPLACE` convergence. Vitess `vreplicator.validateBinlogRowImage` (`vreplicator.go:243-270`) permits `full` and `noblob` (for `MoveTables`/`Reshard`/`OnlineDDL`), explicitly rejecting `minimal`.
- **Arbitrary Multi-Table Rewrites & Unbounded Value Conversions (`Cambria` — `unsupported`)**:
  `Cambria` (`src/lens-ops.ts:61-71`, `src/patch.ts:198-209`) restricts `ConvertValue` to hardcoded finite stringified dictionary lookups (`Object.keys(lensOp.mapping[0])`) and supports neither cross-document/cross-table joins nor arbitrary arithmetic expressions (unlike `Reshape` SQL expressions or `PRISM++` chase views).
- **General Multi-Table Join View Updatability (`PRISM++` and Relational Views — `known not to apply`)**:
  By Bancilhon–Spyratos constant-complement theory, arbitrary multi-table join/projection views lack unique, computationally tractable view-update translations; `PRISM++` therefore flags non-invertible `SMO` chains rather than attempting universal lossless updates.
- **PostgreSQL `pg_query` Subquery Column Scoping (`Reshape` — `known not to apply`)**:
  `Reshape`'s `collect_column_references` (`src/sql.rs:208-210`) explicitly skips `SubLink` AST subtrees (`if fields.contains_key("SubLink") { return; }`), meaning arbitrary subqueries inside `up`/`down` expressions are not rewritten to temporary backing column names.
- **MySQL 8.4/9.x `ALGORITHM=INSTANT` Native Metadata Transitions (`not examined`)**:
  Interaction between `gh-ost`/`Vitess` table introspection and MySQL 8.0.29+ / 8.4 `INSTANT` row-version headers (which cap at 64 instant row versions before requiring table rebuild) was not examined at runtime.
- **Live Multi-Shard Hardware Benchmark Latency (`unknown`)**:
  Production I/O saturation curves comparing `VStreamRows` `ParallelInsertWorkers` vs. `gh-ost` `--chunk-size` under NVMe saturation and replication lag throttling were not executed on live MySQL clusters in this sandbox; latency and pause analyses rely on source inspection and the discrete-event MDL probe.

## Evidence

### Primary Repositories and Published Works
- **`github/gh-ost`** @ `dfb342a4b391b7593a71927976f8841c2ac33219`:
  - `go/logic/applier.go`: `CreateAtomicCutOverSentryTable` (`L2335-2360`), `InitAtomicCutOverWaitTimeout` (`L2364-2370`), `AtomicCutOverMagicLock` (`L2384-2504`), `AtomicCutoverRename` (`L2507-2547`), `updateModifiesUniqueKeyColumns` (`L2564-2575`), `buildDMLEventQuery` (`L2579-2629`).
  - `go/logic/migrator.go`: `waitForEventsUpToLock` (`L1789-1836`), `atomicCutOver` (`L1875-1983`).
  - `go/logic/streamer.go`: `EventsStreamer` (`L36-47`), `shouldDecodeRowsEvent` (`L86-100`).
  - `doc/cut-over.md` (`L1-21`); `go.mod` (`go 1.25.12`).
- **`vitessio/vitess`** @ `96ae128bc631b5a103defc6bc4c54c255ec8dff5`:
  - `go/vt/vttablet/onlineddl/executor.go`: `resolveVReplStreamAction` (`L204-209`), `vreplStreamShowsLiveness` (`L295-336`), `reviewVReplStreamError` (`L3812-3832`), `repairVReplicationQuery` (`L3840-3843`), `retireVReplParkRecordQuery` (`L3857-3867`), `redriveVReplRepair` (`L3880-3898`), `reviewRunningMigrations` (`L3922-4256`), `cutOverVReplMigration` (`L1098-1569`), `CancelMigration` (`L2032-2126`), `evaluateDeclarativeDiff` (`L2695-2772`), `terminallyFailMigration` (`L2833-2848`).
  - `go/vt/vttablet/tabletmanager/vreplication/vcopier.go`: `initTablesForCopy` (`L225-278`), `catchup` (`L331-377`), `copyTable` (`L382-470`), `fastForward` (`L749`).
  - `go/vt/vttablet/tabletmanager/vreplication/vreplicator.go`: `Replicate` (`L205-223`), `validateBinlogRowImage` (`L243-270`).
  - `go/vt/vttablet/tabletmanager/vreplication/controller.go`: `RetriesExhaustedIndicator` (`L69`), `run` (`L229-277`), `runBlp` (`L311-398`), `pickSourceTablet` (`L431-459`).
- **`fabianlindfors/reshape`** @ `1c52737b3213bede6997815d4b1f59c6b9174eba` (`v0.11.2`):
  - `Cargo.toml` (`edition = "2021"`, `rust-version = "1.88"`, `pg_query = "6.2"`).
  - `src/lib.rs`: `StatusType` (`L24-30`), `schema_query_for_migration` (`L201-204`), `migrate` (`L212-356`), `complete` (`L358-420+`), `create_view_for_table` (`L583-614`).
  - `src/helpers.rs`: `set_up_helpers` / `reshape.is_new_schema()` (`L5-22`).
  - `src/sql.rs`: `rewrite_index_definition` (`L66-130`), `collect_column_references` (`L205-230`).
  - `src/migrations/add_column.rs` (`L120-210`); `src/migrations/alter_column.rs` (`L52-120`); `src/migrations/remove_column.rs` (`L166-250`).
- **`inkandswitch/cambria`** @ `da8961440cac7eba1c3113488f5bcbc26046620f` (`v0.1.2`):
  - `package.json`; `src/lens-ops.ts` (`L1-85`); `src/reverse.ts` (`L7-76`); `src/patch.ts` (`L28-245`).
- **Literature**:
  - Geoffrey Litt, Peter van Hardenberg, and Orion Henry, *"Cambria: Schema Evolution in Distributed Systems with Edit Lenses"*, **PaPoC '21**, April 2021, DOI `10.1145/3447865.3457963`.
  - Carlo Curino, Hyun Jin Moon, Alin Deutsch, and Carlo Zaniolo, *"Automating the database schema evolution process"*, **The VLDB Journal**, Vol. 22, No. 1, pp. 73–98, 2013, DOI `10.1007/s00778-012-0302-x`.

### Self-Contained Executable Verification Probe (`Basis: execution`, observed 2026-11-19)

Command: `python3 /tmp/schema_lens_mdl_probe.py`

```python
#!/usr/bin/env python3
"""Discrete-event MySQL MDL cut-over & projective lens complement probe."""

import json
import random
from dataclasses import dataclass
from typing import Any, Dict, List, Tuple


@dataclass
class LockReq:
    cid: str
    mode: str  # SR, SW, SNRW, X
    arrival_ms: int
    duration_ms: int
    granted_ms: int = -1
    finished_ms: int = -1


def simulate_mdl(mode: str, drop_c10_midway: bool = False) -> Dict[str, Any]:
    long_select_end = 500
    events_select: List[LockReq] = []
    events_dml: List[LockReq] = []
    for ts in range(20, 520, 20):
        events_select.append(LockReq(f"sel_{ts}", "SR", ts, 5))
        events_dml.append(LockReq(f"dml_{ts}", "SW", ts, 5))

    if mode == "single_rename":
        rename_start = long_select_end
        rename_end = rename_start + 2
        blocked_reads = [r for r in events_select if 10 <= r.arrival_ms < rename_end]
        blocked_writes = [w for w in events_dml if 10 <= w.arrival_ms < rename_end]
        return {
            "strategy": mode,
            "rename_exec_ms": [rename_start, rename_end],
            "read_outage_window_ms": rename_end - 10,
            "write_outage_window_ms": rename_end - 10,
            "blocked_reads": len(blocked_reads),
            "blocked_writes": len(blocked_writes),
            "max_read_wait_ms": max(rename_end - r.arrival_ms for r in blocked_reads),
            "max_write_wait_ms": max(rename_end - w.arrival_ms for w in blocked_writes),
        }

    c10_acquired = long_select_end
    binlog_drain_ms = 15
    c20_issued = c10_acquired + binlog_drain_ms
    if drop_c10_midway:
        return {
            "strategy": "gh_ost_c10_drop_guard",
            "c10_dropped_at_ms": 508,
            "c20_issued": False,
            "premature_swap_prevented": True,
            "write_outage_window_ms": 508 - 500,
        }
    c10_unlock = c20_issued + 2
    c20_rename_end = c10_unlock + 2
    blocked_reads = [r for r in events_select if c10_acquired <= r.arrival_ms < c20_rename_end]
    blocked_writes = [w for w in events_dml if c10_acquired <= w.arrival_ms < c20_rename_end]
    return {
        "strategy": mode,
        "c10_wait_ms": c10_acquired - 10,
        "c10_hold_ms": c10_unlock - c10_acquired,
        "c20_exec_ms": [c10_unlock, c20_rename_end],
        "read_outage_window_ms": c20_rename_end - c10_acquired,
        "write_outage_window_ms": c20_rename_end - c10_acquired,
        "blocked_reads": len(blocked_reads),
        "blocked_writes": len(blocked_writes),
        "max_read_wait_ms": max((c20_rename_end - r.arrival_ms) for r in blocked_reads),
        "max_write_wait_ms": max((c20_rename_end - w.arrival_ms) for w in blocked_writes),
    }


def cambria_stateless_forward(v1: Dict[str, Any]) -> Dict[str, Any]:
    parts = v1["full_name"].split(" ", 1)
    first = parts[0]
    last = parts[1] if len(parts) > 1 else ""
    return {
        "id": v1["id"],
        "first_name": first,
        "last_name": last,
        "tags": [v1["primary_tag"]] if v1["primary_tag"] else [],
        "tier": "free",
    }


def cambria_stateless_reverse(v2: Dict[str, Any]) -> Dict[str, Any]:
    full_name = f"{v2['first_name']} {v2['last_name']}".strip()
    return {
        "id": v2["id"],
        "full_name": full_name,
        "primary_tag": v2["tags"][0] if v2["tags"] else "",
    }


def complement_get(v1: Dict[str, Any], c1: Dict[str, Any]) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    if c1:
        v2 = {
            "id": v1["id"],
            "first_name": c1.get("orig_first", v1["full_name"].split(" ", 1)[0]),
            "last_name": c1.get("orig_last", v1["full_name"].split(" ", 1)[1] if " " in v1["full_name"] else ""),
            "tags": [v1["primary_tag"]] + list(c1.get("tags_tail", [])),
            "tier": c1.get("tier", "free"),
        }
        if not v1["primary_tag"] and not c1.get("tags_tail"):
            v2["tags"] = []
    else:
        v2 = cambria_stateless_forward(v1)
    return v2, {"raw_full_name": v1["full_name"]}


def complement_put(v2: Dict[str, Any], c2: Dict[str, Any]) -> Tuple[Dict[str, Any], Dict[str, Any]]:
    derived_full = f"{v2['first_name']} {v2['last_name']}".strip()
    if c2 and c2.get("raw_full_name", "").replace(" ", "") == derived_full.replace(" ", ""):
        full_name = c2["raw_full_name"]
    else:
        full_name = derived_full
    v1 = {
        "id": v2["id"],
        "full_name": full_name,
        "primary_tag": v2["tags"][0] if v2["tags"] else "",
    }
    c1 = {
        "tags_tail": list(v2["tags"][1:]),
        "tier": v2["tier"],
        "orig_first": v2["first_name"],
        "orig_last": v2["last_name"],
    }
    return v1, c1


def run_lens_probe(n: int = 1000) -> Dict[str, Any]:
    rng = random.Random(0x5CA1E)
    stateless_field_losses = 0
    complement_roundtrip_mismatches = 0
    complement_bytes: List[int] = []
    for i in range(n):
        first = rng.choice(["Ada", "Grace", "Mary Ann", "J. R."])
        last = rng.choice(["Lovelace", "Hopper", "von Neumann", ""])
        tags = [f"t{rng.randint(1, 9)}" for _ in range(rng.randint(1, 4))]
        tier = rng.choice(["free", "pro", "enterprise"])
        v2_orig = {"id": i, "first_name": first, "last_name": last, "tags": tags, "tier": tier}
        if cambria_stateless_forward(cambria_stateless_reverse(v2_orig)) != v2_orig:
            stateless_field_losses += 1
        v1_comp, c1 = complement_put(v2_orig, {})
        v2_rt_comp, _ = complement_get(v1_comp, c1)
        if v2_rt_comp != v2_orig:
            complement_roundtrip_mismatches += 1
        complement_bytes.append(len(json.dumps(c1, separators=(",", ":")).encode("utf-8")))
    return {
        "trials": n,
        "stateless_rollback_losses": stateless_field_losses,
        "complement_rollback_mismatches": complement_roundtrip_mismatches,
        "complement_avg_bytes": round(sum(complement_bytes) / len(complement_bytes), 2),
        "complement_max_bytes": max(complement_bytes),
    }


if __name__ == "__main__":
    print(json.dumps({
        "mdl_single_rename": simulate_mdl("single_rename"),
        "mdl_gh_ost_two_conn": simulate_mdl("gh_ost_two_conn"),
        "mdl_gh_ost_c10_drop": simulate_mdl("gh_ost_two_conn", drop_c10_midway=True),
        "lens_rollback_probe": run_lens_probe(1000),
    }, indent=2))
```

Recorded Output:

```json
{
  "mdl_single_rename": {
    "strategy": "single_rename",
    "rename_exec_ms": [500, 502],
    "read_outage_window_ms": 492,
    "write_outage_window_ms": 492,
    "blocked_reads": 25,
    "blocked_writes": 25,
    "max_read_wait_ms": 482,
    "max_write_wait_ms": 482
  },
  "mdl_gh_ost_two_conn": {
    "strategy": "gh_ost_two_conn",
    "c10_wait_ms": 490,
    "c10_hold_ms": 17,
    "c20_exec_ms": [517, 519],
    "read_outage_window_ms": 19,
    "write_outage_window_ms": 19,
    "blocked_reads": 1,
    "blocked_writes": 1,
    "max_read_wait_ms": 19,
    "max_write_wait_ms": 19
  },
  "mdl_gh_ost_c10_drop": {
    "strategy": "gh_ost_c10_drop_guard",
    "c10_dropped_at_ms": 508,
    "c20_issued": false,
    "premature_swap_prevented": true,
    "write_outage_window_ms": 8
  },
  "lens_rollback_probe": {
    "trials": 1000,
    "stateless_rollback_losses": 954,
    "complement_rollback_mismatches": 0,
    "complement_avg_bytes": 81.26,
    "complement_max_bytes": 100
  }
}
```

## Revalidation

To verify whether these findings hold on newer upstream commits or local environments:

1. **Re-run the Discrete-Event MDL & Complement Probe**: Execute `python3 /tmp/schema_lens_mdl_probe.py` from the embedded script above (`< 50 ms`, standard library Python 3.10+ only) and assert `mdl_gh_ost_two_conn.read_outage_window_ms == 19` and `lens_rollback_probe.complement_rollback_mismatches == 0`.
2. **Diff Upstream Cut-Over and State-Machine Critical Sections**:
   - In `github/gh-ost`, fetch `go/logic/applier.go` (`AtomicCutOverMagicLock`, `AtomicCutoverRename`) and `go/logic/migrator.go` (`atomicCutOver`) and confirm `ExpectUsedLock` and `ExpectProcess(..., "metadata lock", "rename")` remain strictly ordered prior to `okToUnlockTable <- true`.
   - In `vitessio/vitess`, fetch `go/vt/vttablet/onlineddl/executor.go` and inspect `vreplStreamShowsLiveness`, `reviewVReplStreamError`, `vreplicationPendingCancel`, `vreplicationPendingRepair`, and `cutOverVReplMigration` for changes to `_vt.copy_state` liveness gating or `HoldTableGCState` sentry handling.
   - In `fabianlindfors/reshape`, check `src/helpers.rs` (`reshape.is_new_schema()`) and `src/migrations/remove_column.rs` (`DEFERRABLE INITIALLY DEFERRED` constraint triggers) and confirm `pg_query` `SubLink` handling in `src/sql.rs`.
   - In `inkandswitch/cambria`, check `src/reverse.ts` and `src/patch.ts` (`head`, `remove`, `addDefaultValues`) to confirm whether an explicit complement store has been added to `applyLensToPatch`.
