# Post-publication #3731 I054–I106 residual audit and same-name Charon control

## Summary

The live #3731 wording for all **53 investigations I054–I106** still matches the published v23 ledger exactly. This audit retains v23's **51 partial, one not-run (I072), and one conditional (I081)** classifications. The [per-ID decision table](support/row-decisions.csv) records the exact requested scope, cited evidence, fresh assessment, availability decision, and remaining gate for every row.

One `new_distinct_cached_only_experiment_available: false` decision was too broad as a statement about *all possible bounded components*: I076 still lacked a same-named sibling-crate control. With cached Charon/Cargo/rustc, two distinct Cargo packages exported libraries named `shared_unit`. Both Charon runs succeeded and serialized the same crate and function names, while one function returned `11` and the other `29`. This is a concrete collision for a key made only from serialized crate/function names. It does **not** implement or validate Anneal's complete compilation-unit key, output selection, or collision rejection, so I076 remains partial. No other distinct cached-only cell was identified for the exact remaining gates after the scoped tool and package review.

## Applicability

The audit point is published `reference@9d2426519c7eaaf58b13b109a2f4c16d84c51616`, its v23 investigation ledger, and the [live #3731 body](https://github.com/google/zerocopy/issues/3731) fetched through GitHub's public API on 2026-09-29 (`updated_at` `2026-09-29T05:39:11Z`). The full body SHA-256 was `e1ca20c129376f0459674098d4f6ddd5355f4b24cdceaad0f2a9c6cb7e4d98aa`; the 53 retained scope lines have SHA-256 `e2b1de4faa69aaef8fd0bfbae01108d0f01eb7d0c49c5e19bb755f77cb6890b0`. All 53 title, method, and scope strings match v23. The issue is a research agenda, not an implemented Anneal contract.

The new execution used Charon `0.1.210` (binary SHA-256 `51bb6d23beab3f97a684c25162d3e402fc820c891b57b21d2ca781c1da211a8b`), Cargo nightly 2026-05-31 (`71d7b3f81809731f3c95737386b0056cf0a335dd1e3dcb42ac4e3d81599480b1`), and rustc nightly 2026-05-31 (`2ab7af1ea2ec5c69195fd8dfb0e1f91afdb7cc1e53127bba416616ce43a18dbc`) on macOS arm64. The probe used `--offline --locked`, one Cargo job, disabled incremental compilation, a 30-second command timeout, and an owned work directory. No dependency was fetched or installed.

## Findings

### Row-by-row decision

[`support/row-decisions.csv`](support/row-decisions.csv) is the complete 53-row audit. Each row retains v23's status and exact remaining delta, identifies the prior packages considered, and states why the local cache did or did not offer another distinct cell. The [86-package inventory](support/cited-package-inventory.csv) covers every citation in that table (the prior 85-package review omitted its own newly produced I080 report from its inventory). Its hashes describe the published review point; later corrections to another report are not a failure of this historical observation. The offline checker verifies the current citation paths and inventory structure without assuming other reports can never change.

The practical gates divide as follows:

| Rows | Fresh availability conclusion |
| --- | --- |
| I054–I064, I066–I070, I073–I075, I078–I080, I083–I085, I090–I093, I096–I100, I102, I105–I106 | Existing executions and models cover bounded components. Their exact remaining decisions require an Anneal publisher, generated subject/obligation owner, editor/MCP route, production cache policy, representative workload, or full stage scheduler. Repeating another tiny surrogate would not test those missing interfaces. |
| I065, I071–I072 | The scoped Python and global npm inventory found no independent MCP SDK or installed existing Lean MCP adapter. Existing raw-wire clients are toy bridges, and no Anneal shared-workspace adapter is running. I072 remains not-run for its specified existing-adapter comparison. |
| I077, I081–I082, I086–I088 | Cached Charon and Aeneas CLIs exist, but the inspected `charon_lib` surface exposed LLBC deserialization rather than a reusable extraction worker; `ocamlc`, `dune`, and `opam` were absent on `PATH`. Same-process/reset and compiled-registry questions remain gated. I081 remains conditional. |
| I076 | A distinct same-named sibling-package Charon component ran here. The complete compilation-unit key and collision-rejecting Anneal output policy remain unimplemented. |
| I089, I094–I095, I101, I103–I104 | The bounded inventory found Lean 4.29.0 and 4.30.0-rc2, no built Anneal omnibus archive, and no later compatible tuple. Small prepared Lake, relocation, sandbox, and file-observer reports remain component evidence; a real archive/consumer and complete trace or new compatible pin are missing. |

The row table preserves the more precise gate for each ID; the groups above are a navigation summary. The existing v23 prerequisite corrections for I065, I071, I077, I089, I094, I101, and I103 remain sound. The new I076 cell changes neither an issue status nor the broader product gate.

### I076: serialized name is not a full subject key

The retained workspace has package names `left_package` and `right_package`; each manifest declares `[lib] name = "shared_unit"`. Their source files respectively define `pub fn marker() -> u32 { 11 }` and `{ 29 }`. Each command selected its package and `--lib` explicitly, used the same workspace and private Cargo target, and wrote a separate LLBC destination. Both exited 0 with `has_errors: false`.

| Package | Serialized `crate_name` / local function | Body literal | LLBC SHA-256 |
| --- | --- | ---: | --- |
| `left_package` | `shared_unit` / `shared_unit::marker` | `11` | `07aef8e7dcc9caf48e0a0d6a80dfe87f74d2cb639c293011f17184557ac6a703` |
| `right_package` | `shared_unit` / `shared_unit::marker` | `29` | `d5301c18f06024c9cb13c8b58b74567fe9dc45f701208621384ef3a5f8cc2a29` |

The serialized file records retain `left/src/lib.rs` versus `right/src/lib.rs`; the experiment therefore does **not** claim Charon loses all source provenance. It shows that an Anneal selector using only the crate/function names would conflate two distinct Cargo subjects. The earlier [subject/output-phase matrix](../anneal-3730-charon-subject-output-phase-matrix-2026-09-29/REPORT.md) already found a different hazard: a `--test` request could finish with either a test or binary LLBC at one destination. Together these controls support checking package/target/invocation identity and actual produced output before publication. They do not define a sufficient universal key, and no Anneal wrapper was exercised. Basis: **execution** for the two raw LLBCs; **derived** for the name-only-key implication.

## Boundaries

- The local availability inventory is scoped to named `.anneal-local-tools` paths, `PATH`, Python module resolution, and globally installed npm packages. It does not prove no suitable SDK, archive, toolchain, or editor exists elsewhere or could be supplied later. `fs_usage` and `dtrace` are present on `PATH`, but mere presence is not a complete I095/I104 attempted-access trace.
- The I076 probe uses two small libraries, no proc macro/host unit, no translation or Lean proof, no concurrent writers, and no Anneal CLI. Both Charon runs use separate destination files; actual output-path collision arbitration remains untested.
- The v23 status rows are research coverage decisions, not product verification results. There is still no executed current Anneal V2 verification, editor, or MCP workflow in this audit.
- The package inventory pins report bytes at this review point. A later correction to a cited package requires a new semantic comparison; it does not retroactively alter what this audit inspected.

## Evidence

- [`support/live-issue-scope.txt`](support/live-issue-scope.txt) retains all 53 live issue lines. [`support/row-decisions.csv`](support/row-decisions.csv) compares each to v23, cites the relevant prior report packages, and states its retained status and remaining gate. [`support/cited-package-inventory.csv`](support/cited-package-inventory.csv) records 86 cited package metadata/report hashes.
- [`support/availability.json`](support/availability.json) records the bounded local tool/asset inventory and observed absence checks. No credentials or service content were accessed.
- [`support/inputs/`](support/inputs/) retains the exact offline Cargo workspace. [`support/artifacts/left.llbc`](support/artifacts/left.llbc) and [`right.llbc`](support/artifacts/right.llbc) retain complete Charon output. [`support/results.json`](support/results.json) records binary/input/output hashes, exact command arguments, exits, streams, timings, and decoded identities. The literal values are checked from the serialized function bodies, not inferred only from source text.
- [`support/probe.py`](support/probe.py) replays the I076 cell in an absent owned work directory; [`support/check.py`](support/check.py) checks the retained row table, scope match, citations, and raw I076 specimens without launching toolchains. The v23 ledger has SHA-256 `df8517ecf396a7fd1ee230afa95a67c0ed5929edb48dc7b571949c74466a234a`.

## Revalidation

From this package, run `python3 support/check.py`. To replay I076, copy the package if the retained artifacts must remain unchanged, then run `python3 support/probe.py --work /new/absent/owned/path` with the exact cached tools; the script replaces only this package's `support/artifacts/{left,right}.llbc` and `support/results.json`. Compare package/source identity, serialized crate/function name, body literal, and exit status before comparing raw LLBC hashes, which include the destination path.

For the full I076 residual, select and implement Anneal's compilation-unit key and output ownership contract, then rerun the sibling-name and earlier wrong-final-unit controls through that wrapper. For the other 52 rows, use the exact remaining gate in `row-decisions.csv` and acquire the named product, archive, client, later tuple, or tracing surface before treating another component exercise as completion.
