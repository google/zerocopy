# I125: plugin basename resolution and path alias under Lean 4.30.0-rc2

## Result and exact scope

Pinned Lean's `--plugin=file` accepts a relative basename, but its plugin loader resolves that pathname with `IO.FS.realPath` before loading. It does **not** search `LEAN_PATH` or the system library path for a plugin basename. With `LEAN_PATH` set to directory A, invoking `--plugin=plugin__probe_Plugin.dylib` from an empty cwd failed with `no such file or directory`; invoking the identical argument from A loaded v1, and from B loaded v2. The successful cwd cases are relative pathname resolution, not a search-path collision.

A separate, narrower path-alias fixture kept one server cwd fixed while a same-basename symlink changed target from the v1 binary in A to the v2 binary in B. The first file's initializer marker was `plugin-v1`. After the alias switch, a newly opened file's marker was `plugin-v2`; the earlier file still answered a goal request. A fresh server then produced `plugin-v2`. This adds cwd and canonical-path evidence to the existing I125/I154 stable-path replacement reports. It does not test ABI compatibility or establish Anneal product routing.

## Pinned source and CLI evidence

The installed Lean source is `Lean/LoadDynlib.lean` SHA-256 `88941bc513806a35f7a86ee4056e1cecab8af9a8feb596ad01000914d3f570f1`. Lines 93–98 say `loadPlugin` first calls `IO.FS.realPath path`, then derives the file stem and calls `Dynlib.load` on the resolved path. Its comment at line 94 explicitly rejects system library search for plugins. Lines 105–107 document persistence; the earlier docstring states plugins are never unloaded. This differs from generic `Dynlib.load`, whose lines 27–34 permit system-dependent search when called directly.

The installed `Lean/Shell.lean` SHA-256 is `0de8cdbadedf418ccfb051ec8cb2c7bcd3bb6fef524c16962c72e4acfbf64d54`. Lines 409–413 pass the `--plugin` argument directly to `Lean.loadPlugin` and forward the same argument to workers. CLI help line 168 describes `--plugin=file` as a file argument. The pinned Lean executable SHA-256 was `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997`.

## Fixture and observations

The fixture reused the compiled v1/v2 marker plugins from `anneal-3730-plugin-reversal-worker-order-2026-09-29`; no compiler, package manager, or network fetch ran. Both files had the same basename `plugin__probe_Plugin.dylib` in separate A and B directories. Their SHA-256s were v1 `3f4a1cb3a67a0027f0c90e819afc20d009ddb921cb7f4c0e0095db074e085aa4` and v2 `f7b4c875cb1c91a35259462b5034f48ad96f819e519d9414edc68975045f92a9`. `Dep.olean` and the proof bytes were fixed throughout. The marker is a compiled initializer execution witness, not a process memory map or loader attestation.

| Case | `--plugin` argument and cwd | Resolved binary | Observation |
| --- | --- | --- | --- |
| CLI negative | basename, empty cwd; `LEAN_PATH=A` | none | exit 1, no marker, `no such file or directory` |
| CLI A | basename, cwd A | v1 | exit 0, `plugin-v1` |
| CLI B | basename, cwd B; `LEAN_PATH=A` | v2 | exit 0, `plugin-v2` |
| Retained server, first file | basename, cwd alias→A | v1 | `plugin-v1`, diagnostics and goal succeeded |
| Same server, new file after alias→B | basename, same cwd | v2 | `plugin-v2`, diagnostics and goal succeeded; old file goal still succeeded |
| Fresh server, alias→B | basename, same cwd | v2 | `plugin-v2`, diagnostics and goal succeeded |

The retained server exited 0 before the fresh server started; at most one server ran at a time. The retained preflight recorded 50% free system memory and 48,665,923,584 free disk bytes. The run required at least 25% free memory and 10 GiB free disk.

## I125 mapping and limits

I125 asks for library lookup paths, plugin revisions, initialization state, ABI-compatible-looking replacements, loaded binaries and restart needs, then an Anneal integration rule. This package resolves one lookup ambiguity for the pinned Lean `--plugin` path: a bare name is cwd-relative after `realPath`, and `LEAN_PATH` is not its lookup path. It also records canonical target and content hash beside each marker during a target alias change and shows a fresh server selecting the current target. The existing direct replacement report covers v1→v2→v1 on one explicit path. Neither report determines compatible ABI limits, multiple plugin dependencies, native mapping identity, product routing, or whether Anneal's own worker/GC protocol pins plugin identities. These remain I125 residuals.

## Replay and check

`python3 support/check.py` validates the saved transcript, pinned Lean hash, prior report's retained plugin binary hashes, expected failure and marker order, response success, and sequential server lifetimes offline. To repeat the bounded experiment, run `python3 support/probe.py --lean /absolute/path/to/pinned/lean --work /absolute/path/to/absent/scratch`. The script checks the Lean hash, uses the prior reports' retained fixture and plugin binaries, and writes only to the new scratch directory. The recorded run's work directory was under `/Users/josh/Codex/Meta/Data/20260929-issue-3730-3731-publish/i125-plugin-path-alias`. A changed toolchain or input plugin is a new subject.
