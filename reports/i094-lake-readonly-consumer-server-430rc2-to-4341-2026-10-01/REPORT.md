# I094: installed Lake 4.30 versus 4.34 read-only consumer and server

## Result

In a controlled two-package fixture, the installed Lean/Lake **4.30.0-rc2** tuple could consume a prebuilt, read-only local dependency when a relative consumer `lake-manifest.json` was seeded before first use. A fresh consumer **without** that manifest failed both `lake build Generated` and `lake setup-file Generated.lean`: Lake attempted to create `producer/.lake/config/probe_dep/lakefile.olean.lock` and received permission denied. A fresh `lake serve` likewise reported configuration errors, fell back to plain `lean --server`, and never published the expected value diagnostic.

With the same source layout and its own compatible prebuilt dependency, installed Lean/Lake **4.34.1** built the fresh manifest-absent consumer, returned a `setup-file` object resolving the dependency OLean, and served a live open file whose diagnostics included `7`. The dependency directory was read-only throughout those consumer and server calls. Its complete path, file-content hash, mode, and modification-time inventory was identical before and after all calls at each version. This directly narrows the 4.30 preseeded-manifest workaround for this fixture; it does not establish that 4.34.1 never writes to any read-only dependency layout.

**I094 remains partial.** This closes the small installed-tuple comparison for a single local path dependency and one Lean module, including a live server open. Still open are the actual content-identified Anneal/Aeneas/Mathlib archive, its coupled generated artifacts and toolchain, broader native/plugin/cache artifact families, relocation and multiple-consumer scaling, enforced write tracing, and a source-level explanation of the changed Lake ownership path. No actual Aeneas/Mathlib archive was built or read for this probe.

## Exact tuples and fixture

Both executables came only from `/Users/josh/Codex/Projects/zerocopy/.anneal-local-tools/elan/toolchains`; [identity.json](identity.json) records the full version strings, commits, and SHA-256 hashes. Lake was `5.0.0-src+3dc1a08` with Lean `4.30.0-rc2` (commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`), versus Lake `5.0.0-src+5045d00` with Lean `4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`). The respective Lake hashes were `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` and `c8c24f1398162ab4004e2a869952d8469f54293651151feaad4526f2b8474c6e`.

For each version, `producer/Dep.lean` defines `depValue : Nat := 7`; `consumer/Generated.lean` imports `Dep` and evaluates it. The consumer Lake file has `require probe_dep from "../producer"`. The fixture follows the earlier [4.30 read-only Lake probe](../lake-generated-workspace-readonly-probe-v4-30-0-rc2/REPORT.md) but was rebuilt from source independently at each compatible tuple. There was no cross-version OLean reuse. The only source difference between versions was `lean-toolchain`; the source hashes and retained trees are under [work](work). Fresh seeded consumers copied their version's generated relative manifest. Fresh unseeded consumers had no manifest before their first command. The independent `fresh-build-first` directories are decisive for build because an earlier `setup-file` command in the other unseeded directories created a consumer manifest at 4.34.1.

## Observed matrix

| Operation against read-only producer | 4.30.0-rc2 | 4.34.1 |
| --- | --- | --- |
| Fresh consumer, preseeded relative manifest: `--keep-toolchain --no-cache --old --no-build build Dep` | Up to date | Up to date |
| Same seeded consumer: `--keep-toolchain --no-cache --old build Generated` | Exit 0; evaluates `7` | Exit 0; evaluates `7` |
| Same seeded consumer: `--keep-toolchain --no-cache setup-file Generated.lean` and `env lean --json Generated.lean` | Exit 0; resolves `Dep.olean`; JSON value `7` | Exit 0; resolves `Dep.olean`; JSON value `7` |
| Independent manifest-absent `fresh-build-first`: `--keep-toolchain --no-cache --old build Generated` | Exit 1; dependency config lock permission denied | Exit 0; evaluates `7` |
| Independent manifest-absent `fresh-unseeded`: `--keep-toolchain --no-cache setup-file Generated.lean` | Exit 1; same lock | Exit 0; resolves `Dep.olean` |
| Seeded live `lake --keep-toolchain --no-cache serve`, initialize and didOpen | Published `7` | Published `7` |
| Independent manifest-absent live `lake serve`, initialize and didOpen | Workspace configuration error and plain Lean fallback; no `7` | Published `7` |

The 4.34 `setup-file` JSON represents `importArts.Dep` with one extra array level relative to 4.30. The object in each run pointed to that version's own `producer/.lake/build/lib/lean/Dep.olean`. This is a protocol-shape difference visible in the raw output; consumers must parse the version they run.

The raw [runs.jsonl](runs.jsonl) contains every batch command, cwd, selected environment, exit, full stdout/stderr, admission check and periodic resource samples. [server.py](server.py) sent exact framed LSP initialize, initialized and didOpen messages, then shutdown and exit; the four [server transcript files](server-4.34.1-fresh-server-unseeded.json) retain all input and output frames, stderr and samples. The two independent manifest-absent server transcripts are [4.30](server-4.30.0-rc2-fresh-server-unseeded.json) and [4.34](server-4.34.1-fresh-server-unseeded.json). The two seeded server transcripts are [4.30](server-4.30.0-rc2.json) and [4.34](server-4.34.1.json).

## Controls and resource bounds

All Lake and live server runs were serial. [guard.py](guard.py) and [server.py](server.py) launched each command in its own process group, sampled group RSS, `memory_pressure -Q`, and free disk, and were set to kill the group at **2 GiB RSS**, **<10% `memory_pressure` free**, or **≤10 GiB disk free**. No abort fired. The maximum sampled group RSS was approximately **1,021 MiB** for batch commands and **1,015 MiB** for live servers. The lowest sampled `memory_pressure` free value was **43%** and the lowest sampled disk free was **17,601,011,712 bytes**. These are sampled RSS and host readings, not a shared-page-adjusted peak or proof against sub-sample spikes. The user explicitly waived the former >30% reclaimable-RAM admission gate for this experiment; the 2 GiB group ceiling here does not change the separate R428 1 GiB rule.

The per-version [before](snap-4.30.0-rc2-before.json) and [final](snap-4.30.0-rc2-final.json) inventories for 4.30, and [before](snap-4.34.1-before.json) and [final](snap-4.34.1-final.json) inventories for 4.34, are exactly equal within each version: 25 and 22 producer entries respectively. They include all dependency source and built files, paths, modes, mtimes and SHA-256 hashes. Consumer `lean-toolchain`, `lakefile.lean` and `Generated.lean` hashes matched across the initial, seeded, fresh-build-first and fresh-server-unseeded copies within each version. The generated consumer manifest and `.lake` outputs were allowed to change in the consumer's own directory.

No network or external package asset was fetched, no dependency was installed, and no user project or shared publication checkout was modified. This is an entirely local path-dependency fixture; `--no-cache` alone is not a network-denial proof. At finish, no Lean/Lake experiment process remained, the retained evidence and fixture used about **2.5 MiB**, and the host still had about **15 GiB** available by `df -g`. The retained read-only producer trees and logs are intentional audit material; no external cleanup was needed.

## Interpretation for I094

The preseeded consumer manifest is an observed 4.30 workaround in this fixture. Upgrading to the installed 4.34.1 tuple removes that particular first-use lock failure here, while a stable Anneal design still needs an explicit read-only dependency contract, consumer-owned writable state, versioned setup-file handling, and validation against the real archive. This experiment cannot promote the local two-module result into a claim about all Lake path dependencies or the full Anneal service.

## Revalidation

Run `python3 -B support/check.py` from this report directory. The offline checker validates toolchain identity metadata, exact producer snapshot equality, all 18 guarded command outcomes and resource bounds, and the four framed LSP transcripts. It does not invoke Lean/Lake or prove behavior beyond this retained fixture.
