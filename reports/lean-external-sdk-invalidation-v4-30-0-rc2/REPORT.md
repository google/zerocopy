# External prebuilt SDK imports and local invalidation on Lean/Lake v4.30.0-rc2

## Summary

For a tiny frozen prebuilt SDK on Lean/Lake `v4.30.0-rc2`, `lake env` retained an external `LEAN_PATH`, but `lake build` discarded it when compiling a local module. Placing the SDK OLean in an extended immutable Lean sysroot let stock Lake compile that local import without making the SDK a Lake package dependency. A coherent overlay needed **both** Lean and Lake launchers copied into the new sysroot; symlinked launchers selected the old installation in different ways.

The SDK's identity was then **absent from Lake's local module hash**. Switching from SDK v1 (`sdkValue = 10`) to SDK v2 (`sdkValue = 20`) while leaving the consumer source and Lake configuration byte-and-mtime identical replayed the old `Client.olean`. A new `#eval` reported the equality false while the old `clientProof : clientValue = sdkValue` remained available. Changing the root package name, changing an imported private identity module, or cleaning private outputs caused recompilation and rejected that now-false proof. A versioned SDK consumer must therefore bind its local build identity to the exact SDK digest; compilation success alone is not a safe identity check.

## Applicability

The executed Lean/Lake subject is `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc` (`v4.30.0-rc2`) on `arm64-apple-darwin24.6.0`. The tested Lean executable's SHA-256 is `b48bc5ab229bd8b320a224b87e20fc428dba6fa8a1c054bd4fa6def846e19997` (49,968 bytes); Lake's is `9a89b2af1bddb7e6d5a8dbb2c715288bcb4f24b9129132640cee950734366bcb` (51,840 bytes). The tiny source fixture is preserved under [`support/fixtures/`](support/fixtures/), with its input hashes and original output hashes in [`support/observations.json`](support/observations.json). Its SDK modules contain only `def sdkValue : Nat := 10` or `20`; the consumer's `by decide` proof is intentionally sensitive to the change. This is an incremental-build mechanism canary, not a Mathlib theorem or full Anneal proof test.

The second subject, the exact June 2026 macOS arm64 omnibus bundle with SHA-256 `b4e0a5b420eb441e37564c365f06c215f61a3b825fc3df37293da7c3010d2b81`, was used only for the separate coherent-launcher native smoke cell. That cell linked to the bundle's existing `libaeneas_AeneasMeta.dylib` (SHA-256 `0ffa1ca9ecf894cd4256c75a049287dd285225767c0b41ae9b2e9a3e6e7e4745`) and built a private module importing `AeneasMeta.Saturate.Tactic`; it did not copy or rebuild the published dependency. The SDK-switch and invalidation results use **only** the tiny synthetic SDK, not this real bundle.

All executions were on one local macOS host on 2026-10-03. Lake used `--keep-toolchain --no-cache`, the selected `LEAN_SYSROOT`, `LAKE_OVERRIDE_LEAN=true` for overlays, a private `HOME`, `LAKE_ARTIFACT_CACHE=false`, `LAKE_RESTORE_ARTIFACTS=false`, and `LEAN_NUM_THREADS=1`; the test scrubbed `CI` and controlled `LEAN_PATH`. The process-group guard capped each tiny canary command at 1.5 GiB RSS and monitored host memory and disk. The shared SDK trees were frozen, compared before/after, and guarded against writes. The coherent native cell used the same read-only policy and a fresh private consumer. These observations do not automatically apply to another Lean revision, operating system, toolchain layout, or artifact tuple.

## Findings

### Lake's build path does not inherit the external compiled-module path

The two tiny `Sdk.olean`s were compiled once and frozen. With only `LEAN_PATH=<frozen-SDK-lib>`, `lake env` printed a path containing that directory, but `lake build Client` failed at `import Sdk` with `unknown module prefix 'Sdk'`; the compiler's search-path diagnostic listed only the consumer output directory and stock Lean `lib/lean`. **Basis: execution + source.** The RC2 `Module.buildLean` calls `compileLeanModule` with `getLeanPath`, which is `Workspace.leanPath` (workspace package library directories). `Workspace.augmentedLeanPath`, used for `lake env`, adds the inherited environment path. This distinction explains the otherwise surprising discrepancy, rather than assuming an environment variable was lost before Lake started.

### Extended sysroot visibility needs a coherent launcher pair

The first scratch overlay symlinked `bin/lean` to the stock executable and added frozen `Sdk.olean` under overlay `lib/lean`. Its `lake build Client` still failed: Lean resolved its own executable to the original sysroot. A second overlay copied only the 49,968-byte Lean launcher. Lake successfully built `Client` against the SDK, but bare `lake env lean Inspect.lean` still chose stock Lean and failed to import `Sdk`, because Lake itself was a symlink to the original installation. The explicit overlay Lean path worked for the subsequent invalidation canary.

A third **coherent** scratch view copied both the Lean and Lake launchers (49,968 and 51,840 bytes) and symlinked all larger runtime/artifact content to the frozen install. `lake env lean --print-prefix` returned that new view, a fresh private native smoke module built, and `setup-file` listed the AeneasMeta plugin. Lake's relayed compiler stdout contains a dyld line for loading the real bundle's `libaeneas_AeneasMeta.dylib`. Before/after snapshots found the view and base SDK content/metadata unchanged, the archive's tree metadata unchanged, and selected launcher/OLean/native hashes unchanged; the tracer recorded no blocked shared mutations or network attempts. **Basis: execution + source.** Lean `getBuildDir` derives the installation from `IO.appDir`; Lake separately detects its own installation from `IO.appPath`. `LEAN_SYSROOT` informs Lake's selected Lean install but does not make a symlinked Lean executable behave as if it lived in the overlay.

### An SDK switch can silently reuse a semantically stale proof

The fully copied-Lean sysroot canary (using the overlay Lean executable explicitly for inspection) gave this exact sequence:

| Consumer step | Exit | `#eval clientValue` | `#eval sdkValue` | `#eval decide (clientValue = sdkValue)` | `#check clientProof` |
| --- | ---: | ---: | ---: | --- | --- |
| Build/inspect with frozen SDK v1 | 0 | 10 | 10 | `true` | available |
| Change only selected sysroot to frozen SDK v2, build/inspect same consumer | 0 | 10 | 20 | `false` | **still available** |

The v1 and v2 SDK OLean SHA-256 values were `e1733ea9a13718cff38370c3bfd8943e2a9c0550ba53768cb631390b01315dea` and `140067d410c7281b5541ef536b549c9edd58dbd47428a95e0af2dbfd5a05e6a1`. The baseline `Client.lean` input SHA-256 was `32360b65999d561922aaebccd74e9caef29e6a471f594ae091ea189356aeb81e`; its Lakefile SHA-256 was `d85e761d1073b61f157c0c346fd930d787631603ee47ce1c0611e7f8ca98c9dd`. Both files had identical recorded mtime nanoseconds before the two builds. Lake reused the same `Client` OLean SHA-256 `4b2214fb7481862b29f89ad74ea7a83c7e200f079a9826479963ee7c253a203a`, trace SHA-256 `8e60db6762802f1089f9cc9626bb2d90924fdac363ea1547e965cf5b11069b86`, and dependency hash `90b5218aeee20417`. Thus the changed external SDK OLean was not an input to this local Lake trace. The post-switch `#check` and `#eval` were run under SDK v2, not copied from the v1 process. **Basis: execution + derived.** The hash conclusion follows from changed SDK bytes with unchanged local inputs and unchanged recorded local trace/artifact identities.

Three separate controls switched to SDK v2 but invalidated the private consumer build first. Changing `package probe_consumer` to `package probe_consumer_renamed`, changing imported local `SdkIdentity.lean` from `"v1"` to `"v2"`, and `lake clean` on the private baseline each caused recompilation; all three builds exited 1 because `decide` found `clientValue = sdkValue` false. The root-name and identity controls preserved `Client.lean` bytes while changing only the named local identity input. These are concrete ways to force invalidation in this fixture. A production policy must derive such an identity from the SDK digest and reject mismatches before permitting old local outputs to load. **Basis: execution + derived.** The policy recommendation follows from the stale-proof counterexample; the canary does not prove which production representation is most robust.

## Boundaries

- The tiny OLean switch establishes a local invalidation failure for this RC2 setup. It does not establish that all sysroot imports, native modules, or Lake versions have the same hash behavior. In particular, it is not evidence about a full v4.30.0-final Aeneas/Mathlib bundle.
- `#check clientProof` and the three `#eval` commands expose a stale semantic combination; they are not a general kernel soundness audit. This report does not infer Rust proof soundness or complete theorem equivalence from them.
- The coherent copied-launcher native cell proves prefix selection, one private tactic module build, plugin setup metadata, and one dyld load. It does not test a live language-server interaction under that **coherent** view. Separate real-bundle LSP evidence exists elsewhere but is not needed to establish these launcher findings.
- The preserved output excerpts omit unrelated verbose lines and replace private absolute prefixes with symbolic tokens. [`support/observations.json`](support/observations.json) retains SHA-256 hashes of the original unmodified raw streams and of each preserved normalized excerpt, but the original raw streams and the prebuilt binary artifacts are not committed. The offline checker verifies the retained evidence's internal consistency; it cannot authenticate the earlier machine's execution independently.
- The optional replay script requires a matching installed RC2 sysroot and available resources. It was syntax-checked and dry-run-checked for this report, **not run** as part of report packaging. Its result on another host is a new observation, not a retroactive test of the original traces.

## Evidence

The observation set in [`support/observations.json`](support/observations.json) records 20 selected guarded cells: the two tiny SDK producer builds plus consumer/launcher cells, with exits, abort status, relevant normalized stdout/stderr, original stream SHA-256 values, source SHA-256/mtime tokens, SDK and Client OLean hashes, trace and dependency hashes, and shared-tree integrity. The exact tiny source inputs are in [`support/fixtures/`](support/fixtures/); the report package contains no binaries or Mathlib source mirror. Each output excerpt applies four ordered prefix substitutions: original task validation root → `<VALIDATION_ROOT>`, original relocated RC2 sysroot → `<LEAN_RC2_ROOT>`, project root → `<PROJECT_ROOT>`, and home → `<HOME>`. Hashes labelled `original` are for the pre-substitution raw streams; excerpt hashes are for the preserved text. The report deliberately does not need the private absolute path to interpret a failure or rerun the fixture.

The decisive preserved labels are `20261003-sdk-canary-2-baseline-v1-build` and `...-lake-env-path` (external-path split); `20261003-overlay-1-baseline-v1-build` (symlinked Lean); `20261003-overlay-2-baseline-v1-build` and `...-v1-eval` (copied Lean, symlinked Lake); `20261003-overlay-3-baseline-v1/v2-build` and `...-v1/v2-eval` (stale switch); `...-root-name-v2-build`, `...-identity-v2-build`, and `...-baseline-v2-rebuild-after-clean` (invalidation controls); and `20261003-112910-prefix/build/setup` (both copied launchers and native plugin). The package's [`support/check.py`](support/check.py) checks these exact relationships offline. The original experiments and this material preservation were both on 2026-10-03.

Pinned primary source for the mechanism (all `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`):

- [`src/lake/Lake/Build/Module.lean`, `Module.buildLean`, lines 849–861](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Build/Module.lean#L849-L861) passes `getLeanPath` to the compiler.
- [`src/lake/Lake/Config/Monad.lean`, path accessors, lines 136–154](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Monad.lean#L136-L154) distinguishes workspace and augmented paths; [`src/lake/Lake/Config/Workspace.lean`, lines 288–327](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/Workspace.lean#L288-L327) defines their contents.
- [`src/lean/Lean/Util/Path.lean`, `getBuildDir`, lines 84–85](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lean/Lean/Util/Path.lean#L84-L85) derives Lean's running prefix; [`src/lake/Lake/Config/InstallPath.lean`, `findLakeInstall?`, lines 347–360](https://github.com/leanprover/lean4/blob/3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc/src/lake/Lake/Config/InstallPath.lean#L347-L360) detects Lake from its running path.

## Revalidation

Run the cheap no-compiler checker from this package:

```console
python3 support/check.py
```

For a new installed RC2 toolchain, the optional [`support/reproduce.py`](support/reproduce.py) re-creates the tiny SDKs and launcher variants under one **new, nonexistent** scratch path and checks the external-path failure, stale proof, and three invalidation controls:

```console
python3 support/reproduce.py --lean-root /path/to/lean-v4.30.0-rc2 --scratch /path/to/new-scratch --run
```

It refuses a different Lean commit and an existing scratch directory. It does not download dependencies or touch a global package tree, but it executes multiple compiler processes and should be admitted only on a host with enough memory and disk. To revalidate a different Lean release or a real Aeneas/Mathlib SDK, repeat these discriminating cases with the exact intended compiled-artifact tuple and include native/plugin and editor checks; do not extrapolate from adjacent versions or from this tiny fixture's success.
