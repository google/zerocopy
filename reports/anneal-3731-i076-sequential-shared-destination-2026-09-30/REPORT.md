# Sequential Charon writes to one profile/cfg LLBC destination

## Summary

One dependency-free Rust source produced distinct Charon LLBC models under a release profile and a debug `--cfg probe_alt` build. In two serial orders, both Charon requests exited 0 when directed to the same initially absent `.llbc` path. The retained file after the second request contained the **second subject's** selected function literals in each order. This directly observes a last-completed-write outcome for the selected Charon 0.1.210 pin and fixture. It adds bounded #3731 **I020/I076** and #3730 **D07** evidence to the earlier [profile/cfg slug report](../anneal-v2-profile-cfg-subject-slug-collision-2026-09-29/REPORT.md), which had shown distinct models under one copied Anneal V2 artifact slug but used separate destinations.

The experiment did not invoke Anneal's extraction publisher or test concurrent writers, readers, interrupted writes, or proof selection. I020 and I076 remain **partial** at their existing product gates. D07 gains bounded component context; its residual, gate and prerequisite remain unchanged.

## Applicability

The observed Charon, Cargo and rustc binaries have the SHA-256 values in [REPORT.json](REPORT.json) and [results.json](support/results.json). The toolchain path is `nightly-2026-05-31-aarch64-apple-darwin`. Those hashes identify the actual tools in this run; this package does not establish their source-build provenance. The unchanged `src/lib.rs` SHA-256 is `990beab58abb9a04f48c119fdcea2918865232730e278de3def35e15831b123d`, including the `#[cfg(debug_assertions)]` and `#[cfg(probe_alt)]` branches. The checked-in Anneal V2 scanner source pin and copied slug result belong to the prior linked report; this run did not execute that helper.

All six Charon calls selected `--lib`, used `--preset aeneas`, `--offline --locked -v -j 1`, one Rayon thread, disabled Cargo incremental compilation, and private `CARGO_TARGET_DIR` values. Release requests used `--release`, `CARGO_PROFILE_RELEASE_DEBUG_ASSERTIONS=false`, and no custom `RUSTFLAGS`; cfg requests used debug mode, `RUSTFLAGS=--cfg probe_alt`, and `CARGO_PROFILE_DEV_DEBUG_ASSERTIONS=true`. Each request invoked `charon-driver rustc --crate-name unit_key_probe` once according to its retained verbose stderr. The release driver line contains `-C opt-level=3`; the cfg driver line contains `--cfg probe_alt`.

The controls used separate `.llbc` destinations. The shared-path cells then used two different initially absent private paths: release→cfg at one and cfg→release at the other. Each writer completed before the next started, and the script copied the destination **immediately after each step** to preserve both states. It retained full argv, selected environment, PID, command interval, stdout/stderr, source/output hashes and resource samples. No package fetch or installation occurred.

## Findings

| Cell | First snapshot: selected `profile_value` / `config_value` U32 | Second snapshot: selected literals | Snapshot SHA-256 prefixes, first → second |
| --- | --- | --- | --- |
| Separate release and cfg controls | release `11 / 23` | cfg `7 / 29` | `89a6ce7259ea` / `3460774c7dba` |
| Shared release→cfg | release `11 / 23` | cfg `7 / 29` | `f64506320b0c` → `06fc00c73422` |
| Shared cfg→release | cfg `7 / 29` | release `11 / 23` | `b42b4d6982a4` → `cf4fd779cde4` |

All six outputs were parseable, had `has_errors: false`, and included the same source-file contents hash. The two shared paths were absent before their first command. All six commands exited 0. In both orders the second snapshot's decoded literals matched its separate subject control and differed from the first snapshot. The serialized `dest_file` field was the same within each shared pair. Thus, in these two serial cells, Charon accepted an existing destination and replaced its observable LLBC model with the second request's model without a reported conflict. **Basis: execution.**

The raw `.llbc` hashes are intentionally unequal even between a control and the corresponding shared snapshot: the serialized destination path differs, and other serialized fields may vary. The conclusion compares selected local function literals and source hashes, not whole-file byte identity. The full copied outputs and per-command stderr are retained for inspection.

The runner's fresh preflight measured **38.2198%** estimated reclaimable host memory and **18,989,817,856 bytes** free disk. Across all six commands, the lowest sampled reclaimable estimate was **36.0027%**, the lowest sampled free disk **18,989,367,296 bytes**, the largest sampled process-group RSS **123,216 KiB**, and the largest private scratch **184 KiB**. All remained inside the declared 20%, 10 GiB, 512 MiB, 100 MiB and 15-second limits. The six command intervals summed to 1.8684 seconds. The private work tree was removed after evidence capture. These are sampled admission/cleanup readings, not throughput or a process-attributed physical-memory peak. **Basis: execution.**

## Boundaries

| Item | Added evidence | Still required |
| --- | --- | --- |
| #3731 I020 | Distinct profile/cfg LLBC subjects can successively occupy the same selected Charon destination, with the later selected model observable. | Connect checked-in V2 root/slug selection to an actual Anneal Charon request, publication and proof-context validation. |
| #3731 I076 | Two serial orders confirm concrete output alias behavior for profile/cfg subjects beyond the prior source-level slug equality and separate-output models. | A complete compilation-unit key, output ownership, collision rejection, concurrent arbitration and Anneal publisher integration. |
| #3730 D07 | The omitted profile/cfg dimensions now have a direct sequential destination behavior cell. | End-to-end subject invalidation and producer/consumer controls in an implemented Anneal owner. |

Only one source, one library target, two compilation variants and one Charon pin were tested. The orders ran serially with independent target directories, so this is not evidence of concurrent races, atomic replacement, a cache hit, a stale consumer, or a proof mismatch. The copied slug calculation in the prior report is source-level derivation; this run cannot prove that the V2 CLI would choose or reuse the shared path. A successful second write does not establish that a real Anneal publisher would permit it.

## Evidence

- [`support/acquisition-probe.py.txt`](support/acquisition-probe.py.txt) preserves the exact executed guarded script, including its historical prelaunch banner. [`support/probe.py`](support/probe.py) differs only in that banner and is the replay script. Both hashes appear in `REPORT.json`. [`support/fixture/`](support/fixture/) retains the exact source and manifest. [`support/results.json`](support/results.json) records all preflights, argv/environment, PID/interval, resource samples, output projections, hashes and cleanup.
- [`support/raw/`](support/raw/) contains complete stdout/stderr for all six commands. [`support/artifacts/`](support/artifacts/) contains the two controls and four immediate shared-path snapshots.

## Revalidation

Run `python3 -B support/check.py` from this package. It verifies retained hashes, six command/resource records, both initial path absences, control literals, all four snapshots and cleanup without launching Charon. To reacquire observations, use a fresh package copy without results/raw/artifacts/work and run `python3 -B support/probe.py` only after fresh resource admission; this will create a new observation with path-sensitive raw hashes.
