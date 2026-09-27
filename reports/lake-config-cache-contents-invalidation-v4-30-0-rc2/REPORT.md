# `.lake/config` contents and invalidation in Lake v4.30.0-rc2

## Summary

At Lake v4.30.0-rc2, `.lake/config` is the compiled-configuration cache for **Lean-authored** package configuration files. For a package assigned the name `P` and a configuration file such as `lakefile.lean`, Lake uses:

```text
<package>/.lake/config/P/lakefile.olean
<package>/.lake/config/P/lakefile.olean.trace
<package>/.lake/config/P/lakefile.olean.lock
```

The `.olean` contains the compiled Lean environment for the configuration. The `.olean.trace` is JSON containing six fields: workspace package index, assigned package name, target platform, Lean Git hash, a content hash of the configuration file, and the Lake `-K` option map used when the configuration was elaborated. The `.olean.lock` is a synchronization file used while changing the `.olean`/trace pair; the pinned code does not treat its file contents as configuration data.

The ordinary cache-validity predicate is narrower than the trace schema. Reuse requires the `.olean` to exist and requires equality of `idx`, `name`, `configHash`, `platform`, and `leanHash`. It does **not** compare the trace's persisted `options` with current `cfg.lakeOpts`, and it does not compare current `cfg.leanOpts`. If those five compared fields match, Lake imports the cached `.olean`.

When another compared field is stale, Lake re-elaborates using the **options persisted in the old trace**, not current `-K` options. Current `-K` options are used when there is no trace or when `reconfigure` is explicitly requested. The trace is deliberately written before elaboration and an old `.olean` is removed first; if elaboration fails, the next invocation sees no matching `.olean` and must reconfigure again.

This cache is package-local at this revision because `LoadConfig.lakeDir` is `pkgDir / ".lake"`. The trace nevertheless includes workspace-assigned identity (`idx` and assigned `name`), so two workspaces sharing one dependency tree can invalidate the same physical cache if they assign that package different identities. File locking protects the `.olean`/trace pair from torn concurrent updates, but Lake intentionally refuses one class of simultaneous reconfiguration rather than waiting and risking deadlock.

TOML-authored package configuration does not use this compiled `.lake/config` cache in the pinned load path; it is read and decoded directly.

Basis: exact pinned source + derived synthesis. No fresh Lake execution was performed.

## Applicability

These findings apply to Lake in `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`, tagged `v4.30.0-rc2`.

The subject is deliberately narrower than general package/workspace configuration ownership. It records the contents and behavior of the compiled Lean-configuration cache under `.lake/config`, including its path, persistent files, trace fields, freshness predicate, failure recovery, `-K` option behavior, and locking.

The issue inventory separately tracks Lake configuration ownership after the Lean 4.31 change. No conclusion in this report should be projected onto v4.31 or later without re-reading the corresponding source.

## Findings

### `.lake/config` is package-local at this revision

`LoadConfig` separately records the root workspace directory and the package directory being loaded. Its `lakeDir` accessor is:

```text
cfg.pkgDir / defaultLakeDir
```

where `defaultLakeDir` is `.lake`.

For a Lean-authored configuration, `importConfigFile` then appends `config/<assigned-package-name>`. Thus the cache root is based on the package being configured, including dependency packages; it is not a single cache under the root workspace.

This placement matters independently of freshness. `importConfigFile` calls `createDirAll` on the package-local configuration directory before deciding whether an existing `.olean` is reusable, so even a cache-hit attempt expects enough filesystem access to ensure the directory exists.

Evidence:
- [`LoadConfig` and `LoadConfig.lakeDir`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Config.lean#L19-L70)
- [`importConfigFile` cache directory](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L175-L188)

### The cache has three named files with distinct roles

For configuration filename `F`, Lake derives three paths under `.lake/config/<assigned-name>/`:

- `F.olean`: the compiled Lean module produced from the configuration;
- `F.olean.trace`: JSON metadata used to decide whether the compiled configuration can be reused; and
- `F.olean.lock`: an auxiliary file used to coordinate a transition from shared trace reading to exclusive reconfiguration.

The code reads and writes the trace and imports or rewrites the `.olean`. The lock file is opened for locking but its contents are not inspected or persisted as semantic cache metadata in this algorithm.

The assigned package name participates in the directory path. Consequently, assigning the same physical package a different dependency name selects a different `.lake/config/<name>/` subtree even before the trace's own `name` check is considered.

Evidence:
- [cache-file derivation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L180-L188)
- [trace/lock synchronization](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L189-L231)

### `.olean.trace` stores six fields

The pinned `ConfigTrace` schema is:

```text
idx        : Nat
name       : Name
platform   : String
leanHash   : String
configHash : Hash
options    : NameMap String
```

`idx` and `name` are the package's identity as assigned by the current workspace load. `platform` is `System.Platform.target`. `leanHash` is the selected Lean Git hash from Lake's environment. `configHash` is a hash of the configuration file's text. `options` is the Lake configuration option map supplied through `-K` and dependency options for the elaboration being cached.

The configuration-file hash uses Lake's `computeTextFileHash`, which reads the file as text and hashes `Hash.ofText`; the source documents normalization of CRLF to LF for cross-platform compatibility. This is a content check, not an mtime check.

Evidence:
- [`ConfigTrace`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L166-L173)
- [trace construction](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L232-L253)
- [`computeTextFileHash`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Trace.lean#L227-L248)

### Ordinary reuse compares five identity fields and the `.olean`'s existence

Unless `cfg.reconfigure` is true, Lake reads the trace under a shared lock and parses it as `ConfigTrace`. It considers the compiled configuration up to date only when all of these conditions hold:

1. the `.olean` file exists;
2. `trace.idx == cfg.pkgIdx`;
3. `trace.name == cfg.pkgName`;
4. `trace.configHash == computeTextFileHash(cfg.configFile)`;
5. `trace.platform == System.Platform.target`; and
6. `trace.leanHash == cfg.lakeEnv.leanGithash`.

If they all hold, Lake imports the cached `.olean` using the current `cfg.leanOpts` and releases the shared trace lock.

Several things are therefore *not* direct freshness inputs in this predicate: the configuration file's mtime, current `cfg.lakeOpts`, current `cfg.leanOpts`, workspace path, package path, and dependency manifest state. Some of those values can affect higher-level behavior or how Lake reaches this cache, but this particular cache check does not compare them.

Evidence:
- [trace validation and reuse](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L260-L279)

### The trace records `-K` options but ordinary freshness does not compare them

`ConfigTrace.options` is populated from the option map used for elaboration. However, `options` is absent from the `upToDate` conjunction.

This has a precise source-level consequence. If the trace is otherwise valid, changing only current `cfg.lakeOpts` does not make this cache check stale. Lake imports the old compiled configuration.

If some *other* compared field makes a validly parsed trace stale, Lake calls `elabConfig` with `trace.options`, preserving the option map from the old cache rather than switching to current `cfg.lakeOpts`. By contrast, an explicit `cfg.reconfigure` uses current `cfg.lakeOpts`, and first-time configuration with no trace also uses current `cfg.lakeOpts`.

Thus `options` serves both as provenance and as the input Lake preserves across automatic re-elaboration. `-R`/`reconfigure` is the explicit path that discards that preservation and applies the current option map.

This report does not infer that every CLI-level `-K` change is intended to be ignored. It records the exact cache algorithm at this pin; the revalidation probe should preserve the observable CLI behavior.

Evidence:
- [`ConfigTrace.options`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L166-L173)
- [current-versus-persisted options during validation](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L260-L287)

### Current Lean elaboration options are also absent from the trace identity

`LoadConfig` carries `leanOpts`, and both fresh configuration elaboration and cached `.olean` import receive `cfg.leanOpts`. But `ConfigTrace` has no `leanOpts` field and the freshness predicate does not compare them.

The narrow conclusion is that `.lake/config` does not provide a persistent identity check for changes in `cfg.leanOpts`. Whether callers normally vary those options in ways that affect package configuration is a separate API/CLI question. Consumers should not use the trace schema as evidence that every elaboration-affecting input has been content-addressed.

Evidence:
- [`LoadConfig.leanOpts`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Config.lean#L46-L54)
- [elaboration/import use of `cfg.leanOpts`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L245-L279)

### Failure recovery makes trace publication intentionally precede `.olean` publication

When Lake must re-elaborate, it first tries to remove any old `.olean`. If removal succeeds or the file is absent, it writes the new trace JSON and truncates the trace file **before** elaborating the configuration. It then elaborates and finally writes the new `.olean`.

The comment explains this order. If elaboration fails, the trace should no longer authenticate an old compiled module. Removing the old `.olean` before writing the new trace means the next run fails the `olean.pathExists` part of the freshness predicate and reconfigures automatically.

If removing the old `.olean` fails for another reason, Lake logs the error, unlocks the trace, and removes the trace file. This also prevents a stale trace from continuing to authenticate the old compiled configuration.

The pair is therefore not published atomically as one filesystem object. Correctness relies on the explicit ordering plus the trace/lock protocol.

Evidence:
- [re-elaboration write order and failure handling](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L232-L259)

### Malformed traces have a compatibility fallback centered on `options`

If the trace parses as JSON but cannot be decoded as the current `ConfigTrace` schema, Lake does not immediately discard it. It tries to recover just the `options` field. If that succeeds, Lake re-elaborates using those recovered options.

If the trace is not valid JSON, or if it is JSON without a decodable `options` field, Lake reports:

```text
compiled configuration is invalid; run with '-R' to reconfigure
```

This fallback makes `options` unusually durable across trace-schema changes. It also means an arbitrary malformed or manually rewritten trace is not always self-healing: recovery requires enough JSON structure to recover the option map, unless the user explicitly forces reconfiguration.

Evidence:
- [trace parse/schema fallback](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L260-L287)

### Missing traces are created with an exclusive first-writer path

If no trace exists, Lake ensures `cfg.lakeDir` exists and opens the trace with `writeNew`. The successful first writer locks the new trace and elaborates with current `cfg.lakeOpts`.

A race is explicitly handled. If `writeNew` reports that another process created the trace first, Lake reopens the now-existing trace for reading and runs the ordinary validation path rather than blindly overwriting it.

This startup path reduces one creation race, but it does not make arbitrary simultaneous reconfiguration transparent. The stale-trace upgrade path has its own non-blocking lock rule described below.

Evidence:
- [missing-trace creation/race path](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L288-L297)

### Locking protects the pair but can reject simultaneous reconfiguration

A reader validating the trace holds a shared lock. To reconfigure after discovering staleness, Lake cannot simply wait while retaining that shared lock: two processes could each hold a shared trace lock while one waits for a lock transition blocked by the other.

The implementation therefore uses the companion `.olean.lock` as an upgrade gate. It calls `tryLock` rather than waiting. The winner releases its shared trace lock, reopens the trace read/write, takes an exclusive trace lock, releases the companion lock, and performs reconfiguration. A loser reports that another process may already be reconfiguring the package.

The source explicitly says simultaneous reconfigures are likely to produce unexpected results and treats an error as preferable to the deadlock-prone wait.

For a shared immutable dependency universe, this matters because the cache is physically package-local while `idx` and `name` can vary across workspaces. Two consumers can therefore turn a reusable source checkout into a reconfiguration-contention point even without editing source files.

Evidence:
- [locking rationale and `tryLock` upgrade](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Lean/Elab.lean#L189-L231)

### TOML package configuration bypasses this compiled cache

`loadPackageCore` dispatches `.lean` package configuration to `loadLeanConfig` and `.toml` configuration to `loadTomlConfig`. The TOML loader reads the configuration file directly, parses and decodes it, and constructs the `Package`; it does not call `importConfigFile` and therefore does not create this Lean-configuration `.olean`/trace/lock cache.

This does not mean a TOML package is globally read-only or cache-free. It means only that `.lake/config/<name>/<config>.olean*` belongs to the Lean-authored configuration path at this pin.

Evidence:
- [configuration-language dispatch](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Package.lean#L51-L84)
- [`loadTomlConfig`](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Load/Toml.lean#L470-L507)

## Boundaries

This report does not own the broader question of package-versus-workspace configuration ownership. It uses only the ownership facts needed to locate this cache. A separate report covers that model at v4.30.0-rc2, and a separate inventory item covers the post-4.30 change.

It also does not claim that the six-field trace is a complete semantic cache key. The source shows the opposite: `options` and `leanOpts` are not both compared as freshness inputs, and other package/workspace state is outside this trace.

The report does not establish exact filesystem-lock behavior on NFS, network filesystems, Windows, or unusual filesystems. It records Lake's lock algorithm and documented intent at the source level.

It does not establish whole-package read-only behavior. Even a seeded valid configuration cache coexists with build outputs, manifests, traces, release artifacts, and other Lake state covered by separate subjects.

No fresh exact-pin executable probe was run. In particular, the predicted behavior of changing only `-K`/Lean options and the observed user-facing lock errors should be preserved with a runtime fixture when an appropriate execution surface is available.

## Evidence

Primary revision: `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`).

Pinned source blobs inspected:

- `src/lake/Lake/Load/Config.lean` — `f1fe9b199f41e00d3cf10725b4dfc6b2d3623ec2`
- `src/lake/Lake/Load/Lean/Elab.lean` — `c72b295cb0b9d7365d21cf2ebd323a3cc4068eab`
- `src/lake/Lake/Load/Package.lean` — `e9e858a54048ffa96972d264dbd51ca35b4ba403`
- `src/lake/Lake/Load/Toml.lean` — `b9893aa31ad6b3784cbfd35ebed8ff1bf0706161`
- `src/lake/Lake/Load/Resolve.lean` — `ec7c9978ab99b9a998a1c24d5e1e7ecce3cfa928`
- `src/lake/Lake/Build/Trace.lean` — `656c991fab8a6475802373224514ec7e73f9b18b`

A neighboring durable `Lake configuration ownership at Lean v4.30.0-rc2` report was used to keep this report scoped to the cache rather than repeating the entire package/workspace model. The cache-schema and invalidation conclusions here were rechecked directly against the pinned source listed above.

## Revalidation

After a Lake version change, compare these exact boundaries first:

1. `LoadConfig.lakeDir`: package-local versus workspace-local cache root;
2. `importConfigFile`: configuration-directory naming and the `.olean`, trace, and lock paths;
3. `ConfigTrace`: fields and JSON representation;
4. the `upToDate` predicate: every value compared and every value deliberately omitted;
5. stale-trace behavior: whether re-elaboration uses persisted or current Lake options;
6. failure ordering: old `.olean` removal, trace write, elaboration, and new module write;
7. malformed-trace fallback;
8. first-writer/race handling for a missing trace;
9. lock-upgrade semantics for concurrent stale readers; and
10. Lean-versus-TOML configuration dispatch.

A compact exact-pin fixture should then preserve the observable behavior:

- first-load a Lean-configured package after deleting `.lake/config` and capture the three created files plus decoded trace JSON;
- rerun unchanged and verify the `.olean` is reused;
- change only the configuration text and verify `configHash` invalidates the cache;
- vary only package index and then only assigned package name across two workspaces sharing one checkout, recording which cache subtree/trace changes;
- run once with `-K x=one`, then with `-K x=two` without `-R`, and record the trace and effective configuration; repeat with `-R`;
- vary a caller-supplied Lean option that demonstrably affects configuration elaboration, if such an option is supported by the exercised CLI/API path, and compare reuse behavior;
- corrupt the trace as invalid JSON, then as JSON retaining only an `options` field, and preserve the differing recovery results;
- force a configuration elaboration failure after a stale transition and verify the next run cannot authenticate the removed old `.olean`;
- trigger two concurrent stale reconfigurations and preserve the documented exclusive-lock failure; and
- repeat with a TOML-authored package to confirm this compiled configuration cache is not created by configuration loading alone.

Preserve exact command lines, toolchain identity, directory listings, trace JSON, file hashes, and process output. Do not use the result as evidence for v4.31 or later without separately checking the ownership/layout change tracked by the inventory.