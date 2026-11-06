# Evidence

**Source — Lean/Lake revision.** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

- `src/lake/Lake/Config/Workspace.lean`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`: `Workspace`, root-package anchoring, package array/map, facet configuration, cache/environment state, and manifest path.
- `src/lake/Lake/Config/Package.lean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`: `Package` identity, concrete configuration path, manifest path, dependency/target declarations, Lake/build directories, and package-derived paths.
- `src/lake/Lake/Config/Defaults.lean`, blob `03033b5a032e450540ad99cc7c3be73544ad7416`: default `.lake`, `.lake/packages`, `lakefile`, `lake-manifest.json`, and `.lake/build` paths.
- `src/lake/Lake/Config/PackageConfig.lean`, blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`: package configuration, build directory, Lean/server/native output settings, and extension of workspace/Lean configuration.
- `src/lake/Lake/Load/Package.lean`, blob `e9e858a54048ffa96972d264dbd51ca35b4ba403`: root package configuration loading, Lean-versus-TOML selection, and concrete configuration-file resolution.
- `src/lake/Lake/Load/Workspace.lean`, blob `9f25dd62bc752ede695a25fc20371157eb65d64b`: workspace-root loading followed by dependency update/materialization or manifest-driven materialization.
- `src/lake/Lake/Load/Manifest.lean`, blob `760eb81419762fb0ab11393e93082930645e2b6d`: manifest schema/version, package source entries, materialization identity, compatibility parsing, and serialization.
- `src/lake/Lake/Build/Key.lean`, blob `39d17709dfcdfa21727c384c82695b1502e7b36a`: `BuildKey`, partial CLI keys, package/module/target/facet identities, and textual syntax.
- `src/lake/Lake/Config/TargetConfig.lean`, blob `1387a409048f81744c02af044c0f310ca44278c6`: custom target fetch functions.
- `src/lake/Lake/Config/FacetConfig.lean`, blob `723ef981abb80c6ee4386d95c93fec524077cb51`: typed facet configuration, fetch functions, output kinds, buildability, and memoization.
- `src/lake/Lake/Build/Index.lean`, blob `9ef1a052ac80b17f406fe9a02ff6b956ffad7c29`: recursive build-key dispatch, target/facet fetching, memoization, and topological recursive builds.
- `src/lake/Lake/Build/Job/Basic.lean`, blob `1f0066910478137341388422d8d593ddffbaca18`: `JobAction`, `JobState`, `Job`, task result, trace/log/timing/rebuild state.
- `src/lake/Lake/Build/Trace.lean`, blob `656c991fab8a6475802373224514ec7e73f9b18b`: `BuildTrace`, hash/mtime composition, hash implementation, and freshness helpers.
- `src/lake/Lake/Build/Common.lean`, blob `c283fda65ba4d6e3138a0b4ab8252885bf78a014`: persisted `BuildMetadata`, trace schema `2025-09-10`, build-action writes, `buildUnlessUpToDate?`, old-mode fallback, `.nobuild`, `.hash` sidecars, and file-trace computation.
- `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`: module trace inputs, target-specific trace file, imported-artifact traces, build/cache paths, and module artifact production.
- `src/lake/Lake/Build/Run.lean`, blob `afae31b7d20a37e6a505d4dc7a9ce875467faf7e`: top-level build context/monitor, Lean toolchain trace, build actions, rebuild status, and no-build exit behavior.
- `src/lake/Lake/Build/Target/Basic.lean`, blob `025199b3e85dbd8a4bbd5d757597d7d554884acc`: typed `Target` as a partial build key plus output type.

No evidence above is fresh **execution**. Claims about concrete source behavior are **source** claims; the layered producer/consumer model is **derived** from those source structures.
