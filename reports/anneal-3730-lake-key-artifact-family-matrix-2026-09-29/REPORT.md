# Lake input keys and valid cross-generation artifact families at one pin

## Result

Six tiny private Lake producer/consumer roots used the same isolated artifact cache and pinned Lean/Lake 4.30.0-rc2 on macOS arm64. Identical source/configuration in two different root paths reused the same producer output-map key. Changing the producer source added a map key; changing a package `leanOptions` setting added another key even though the resulting `.olean`, `.ilean`, and C bytes matched the baseline. Changing only the consumer manifest/package name added **no new producer map key** in this fixture. A cache fetch did not place a conventional `Dep.olean` in the copied producer's local build tree: `lake --no-build setup-file` succeeded and named a cache OLean, while direct `lean --json Generated.lean` using that root's local `LEAN_PATH` failed with `unknown module prefix 'Dep'`. This is an operation/placement difference, not a claim that the cache key should have included the consumer name.

A second matrix copied **valid but incompatible** output bytes from another generation over one local baseline file at a time: `.olean` from a `depValue = 9` build; `.ilean` from a build with an added declaration; generated `.c` from `depValue = 9`; and `Dep.setup.json` from the option-changing build. In all four copies, `lake --no-build build Dep` and `lake --no-build setup-file Generated.lean` exited zero and did not repair the overwritten local file. Setup returned the baseline cache OLean SHA-256 `cebebbbc892381bd3920a0b12ab5e4d65f1804574357994ccb20f95f87f98f9b`; a fresh batch import through that **returned setup artifact** proved `depValue + 1 = 8`. A separate fresh batch import through the overwritten **local artifact path** failed for the wrong-generation OLean and passed for the other three families. Fresh direct Lean server diagnostics in isolated directories likewise saw `10` plus a failed `decide` under the wrong OLean, and `8` without proof error under mixed ILean or C. Thus setup success and a proof's success can describe different consumed bytes unless the consumer path is recorded. The direct server watchdogs were forcibly torn down after diagnostics (`-9`); their diagnostic observations are retained, but they do not demonstrate graceful shutdown.

A separate native-plugin control reused the two valid `.dylib` generations preserved in the earlier pinned [plugin-artifact identity report](../anneal-3730-lake-plugin-artifact-identity-v4-30-0-rc2/REPORT.md). Fresh batch processes loaded each under its required `plugin__probe_Plugin.dylib` basename and compiled the same proof, but initializer markers were `plugin-v1` versus `plugin-v2`. The theorem alone did not distinguish loaded native code. These plugin binaries came from the prior fixture; no native plugin was built during this run. This is a separate plugin-load matrix, not a complete combined cache-family/ABI acceptance test.

This is a pinned component experiment. It does not operate on a generated Anneal archive, simulate power loss, or prove safe key design for arbitrary Lake inputs.

## Setup and exact evidence

The installed `lake` binary SHA-256 is `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; `lean` is `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. The experiment used `LAKE_ARTIFACT_CACHE=true`, one private `LAKE_CACHE_DIR`, `LEAN_NUM_THREADS=1`, an isolated home, no package downloads, and at most one command at a time. Each command had a 30-second timeout; the initial system-wide free-memory reading was 47%, above the 35% guard, and the host had more than 15 GiB free disk. The fixture is one `Dep` module, one consumer `Generated.lean`, and a local path manifest. `support/probe.py` created the private scratch root under `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731/r15-lake-key-family`, retained 39 command records in `support/results.json`, and copied exact input/output specimens into `support/artifacts/`. `support/check.py` verifies these bytes and the stated outcomes offline.

| Input case | New producer map key | Local `Dep.olean` after Lake | Direct batch outcome |
| --- | --- | --- | --- |
| Baseline `depValue = 7` | `bc2ee9095550ff31.json` | Present | Exit 0, value 8 |
| Same bytes, different root path | None beyond baseline | Absent after fetch | Exit 1, unknown module prefix |
| Source body `depValue = 9` | `9f80558e806f84cd.json` | Present | Exit 1, expected 8 false; value 10 |
| Added declaration with value still 7 | `56754994d46eab8e.json` | Present | Exit 0 |
| Producer `pp.unicode.fun` option | `ae8ebb304e3ca915.json` | Present | Exit 0; baseline OLean/ILean/C hashes, changed setup hash |
| Consumer manifest name only | None beyond prior four | Absent after fetch | Exit 1, unknown module prefix |

The map filenames are Lake's observed opaque names, not our SHA-256 values. The table reports *new* keys in one cumulative cache. The option case's source bytes were unchanged; its producer `lakefile.lean` changed. The consumer-manifest case changed only the consumer package name in `lakefile.lean`/`lake-manifest.json`. These six cases are selected input ablations, not a proof of a minimal sufficient cache key.

| Valid replacement at baseline local path | Lake no-build `build Dep` | Lake no-build `setup-file` | Fresh batch via setup-returned OLean | Fresh batch via local path | Fresh isolated Lean server via local path |
| --- | ---: | ---: | ---: | ---: | --- |
| Wrong-generation `.olean` | 0 | 0 | 0 | 1, false proposition and value 10 | Failed `decide`, value 10 |
| Added-declaration `.ilean` | 0 | 0 | 0 | 0 | No proof error, value 8 |
| Wrong-generation `.c` | 0 | 0 | 0 | 0 | No proof error, value 8 |
| Option-generation `Dep.setup.json` | 0 | 0 | 0 | 0 | Not queried in this case |

For the mixed local `.olean`, the no-build/setup operations returned the **unchanged baseline cache OLean**, rather than attesting the overwritten local file. The direct batch/server commands were deliberately bound to the local file. A proof-only oracle cannot detect wrong ILean, C or setup bytes in this fixture; their full SHA-256 mismatch did. The local generation mix may be unsupported by Lake; the experiment measures detection boundaries, not a recommended way to assemble packages.

## Coverage and residuals

| #3731 row | Contribution | Remaining exact delta |
| --- | --- | --- |
| I089 | Fresh copied roots plus cache fetch and setup/batch difference. | Real Anneal prepared archive from empty home/cache with read-only dependencies and first-goal writes. |
| I090 | Changed consumer package name without a new producer key in this graph. | Duplicate names, versions, order, rename, and larger package-graph collisions. |
| I091 | File-specific setup names an exact cache OLean while direct local batch lacks one. | Worker-issued setup choice for live/unsaved current documents. |
| I092 | Selected no-build build/setup succeed under valid local family replacement. | Full no-build/no-cache contract across incomplete archive/config/artifact/server families. |
| I093 | Producer Lean option and consumer manifest/name ablations. | TOML/Lean dynamic configuration and graph/env-input variants. |
| I094 | One Lake/Lean pin only. | Compatible later Lake pin and migration of prepared outputs. |
| I095 | Cached path copy did not place a local OLean and setup named a cache object. | Process read/write trace, realized parallelism and larger prepared graph. |
| I096 | Explicit binary, home, cache and path selection. | CLI/editor/MCP/CI discovery, executable selection and cwd variants. |
| I097 | Selected source, path, producer-option and consumer-manifest key changes plus valid wrong-generation local bytes. | Source/model/tool/flag/path key ablations and independent integrity policy for every actual consumer. |
| I098 | Different valid OLean/ILean/C/setup bytes and two valid plugin generations, checked by operation. | Native/plugin/setup *combined* compatibility, servers with Lake discovery, and full generated dependency family. |
| I099 | Baseline fresh proof and setup-artifact import agree on one theorem; local mixed OLean diverges. | Complete clean-versus-prepared declarations, assumptions, diagnostics, goals and loaded artifact identities. |
| I100 | Same-byte source under a different root path reused one key. | mtime, trace, source-order and normalization hazards over real generated graphs. |
| I101 | Different roots consume same cache key. | Relocated producer-removed prepared Anneal archive and native/server path behavior. |
| I102 | No new interruption in this run; earlier R10 retains real partial-write controls. | Concurrent failure schedules, causal artifact/syscall collision and power-loss durability. |
| I103 | Only local package copies, no archive installation replacement. | Same-label archive replacement and attested consumed-byte identity. |
| I104 | No remote dependency or download in this fixture. | Enforced network denial and traced producer/consumer filesystem attempts. |
| I108 | One process at a time here. | Cross-component lock-order, restart and GC with conflicting writers. |
| I109 | Timeouts and preflight guards only. | Memory/disk/fd/process exhaustion and Anneal last-good recovery. |
| I151 | Single-writer local replacement, separate from R10's private-root cache pairs. | Shared writable package-tree conflict and interruption with integrity/recovery oracles. |

## Reproduce and validate

Run `python3 support/check.py` from this package to verify the retained data without toolchains; it reports six input variants, four mixed artifact families, fresh batch/setup/server oracles, two valid plugin generations and 39 command records. To reacquire on the pinned host, run `python3 support/probe.py --work /absolute/absent/owned/scratch-directory`; it requires the already installed toolchain and the cited local prior-plugin package, and replaces only its own retained `support/results.json` and `support/artifacts/`. Use a fresh absent scratch root. The command captures server diagnostics before bounded forced teardown; server exit `-9` must not be interpreted as a successful graceful lifecycle. Compare semantic outcomes and full artifact hashes on replay rather than expecting path-bearing compiled bytes to be stable across roots or revisions.
