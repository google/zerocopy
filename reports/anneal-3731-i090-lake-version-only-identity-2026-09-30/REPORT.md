# Lake package-version-only identity ablation

Observed 2026-09-30 on this Apple Silicon host with the installed Lean/Lake `v4.30.0-rc2` toolchain. The exact Lake executable SHA-256 is `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb`; Lean is `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`. These executable hashes identify the binaries used; this package does not independently establish the source commit from which they were built.

## Question and prior gap

I090 asks which dependency identity inputs current Lake exposes. The earlier consumer-identity report varied a package's version and `Dep.lean` value together, so it could not isolate the version declaration. Here the producer and consumer remain at fixed physical paths, with one assigned package name, one dependency index, unchanged manifests, and unchanged `Dep.lean` value `7`. The only main-cell input edit is `version := v!"1.0.0"` to `v!"2.0.0"` in the producer `lakefile.lean`, followed by a return to `1.0.0`. A separate private-path control keeps version `1.0.0` and changes only `Dep.lean` from value `7` to `9`. The #3730 F05 crosswalk points to I090, I096, and I145; this report supplies bounded I090 evidence and F05 context only.

## Method and retained evidence

The checked-in [`oracle.json`](oracle.json) predefines all source bytes, SHA-256 digests, variants, and tool hashes. [`probe.py`](probe.py) creates one `main` and one `control` package pair under private `work/` paths, then runs `lake build Generated`, `lake setup-file Generated.lean`, and `lake env lean --json Generated.lean` sequentially per cell. Both packages use local path manifests; no packages are fetched. Every command used `--keep-toolchain --no-cache --no-ansi -v`, `LAKE_ARTIFACT_CACHE=false`, `LAKE_NO_CACHE=1`, `LAKE_NO_NET=1`, and one Lean thread. [`results.json`](results.json) records exact argv, working directory, environment overrides, PIDs, exit codes, elapsed time, resource samples, and full before/after per-action file inventories (hash, size, mtime). `raw/` retains complete stdout and stderr. `snapshots/` retains each cell's source, manifests, producer configuration OLean and trace, producer `Dep.olean`, consumer `Generated.olean`, and other selected files. `work/` retains the final files. [`check.py`](check.py) verifies the raw outputs and snapshots against the recorded hashes and controlled inputs.

Two completed acquisitions under `preliminary/first/` and `preliminary/second/` are retained but excluded from the checker and findings. The first omitted intermediate config-trace bytes and full per-action inventories. The second added those captures but rewrote byte-identical `Dep.lean` between main cells, changing its mtime and weakening strict version-only isolation. The final acquisition writes a fixture file only when its bytes change; its full inventories show the producer `lakefile.lean` as the sole changed input between main cells, with `Dep.lean` content **and mtime** fixed.

Fresh final-run admission was 31.56% reclaimable RAM and 18.60 GB free disk. Across 15 commands, live minimum reclaimable RAM was 29.73%, maximum process-group RSS was 1,015,360 KiB, minimum free disk was 18,599,862,272 bytes, and maximum work scratch was 441,005 bytes. All 15 Lake parent commands exited 0 within their 30-second cell deadlines; no guard fired. `check.py` passes.

## Results

| Cell | Producer version | `Dep.lean` value | Producer config OLean SHA-256 prefix | Config trace `configHash` | `Dep.olean` SHA-256 prefix | `Generated.olean` SHA-256 prefix | Fresh `#eval` |
|---|---:|---:|---|---|---|---|---:|
| main A | 1.0.0 | 7 | `b6b95601a569` | `a5b4b476a0591aca` | `cebebbbc8923` | `eedfc1593799` | 7 |
| main B | 2.0.0 | 7 | `ca501585c360` | `b74db869a8cb920f` | `cebebbbc8923` | `eedfc1593799` | 7 |
| main A return | 1.0.0 | 7 | `b6b95601a569` | `a5b4b476a0591aca` | `cebebbbc8923` | `eedfc1593799` | 7 |
| source control A | 1.0.0 | 7 | `b6b95601a569` | `a5b4b476a0591aca` | `cebebbbc8923` | `eedfc1593799` | 7 |
| source control B | 1.0.0 | 9 | `b6b95601a569` | `a5b4b476a0591aca` | `fe893ce3c24d` | `eedfc1593799` | 9 |

In main B and the A return, verbose `build` output said `Replayed Dep`; the full per-action inventory recorded content changes only to producer `lakefile.olean` and its trace on those build calls, aside from a newly present config lock file in B and a later lock-file mtime change. `setup-file` reported the same `Dep.olean` import path throughout main A/B/A, and neither setup nor fresh eval changed files in those cells. The source-value control's second `build` said `Built Dep`; its inventory records changed `Dep.olean`, `Dep.trace`, `Dep.c`/`Dep.c.hash`, and consumer `Generated.trace` while `Generated.olean` retained its hash. Its subsequent fresh `#eval` returned `9`. Source and manifest hashes are retained and checked; the version-only main cells keep `Dep.lean`, both manifests, and the consumer file byte-identical.

**Bounded inference:** In this fixed-path Lake 4.30.0-rc2 fixture, this isolated version-line edit changed the producer's compiled Lake configuration and config trace hash, then reverted when the version reverted. It did not change the observed module OLean bytes or evaluated value and Lake replayed `Dep`. A source-value edit had a different observed pattern. This is evidence about these exact configuration and module artifacts, not proof of a general package-version cache-key rule. It does not establish a complete Lake cache key, archive reuse safety, relocation behavior, another version/platform, or Anneal producer/consumer identity semantics. I090's product-side preparation identity and F05's broader collision question remain open.
