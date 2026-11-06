# Evidence

**Source — Lean/Lake revision.** `leanprover/lean4@3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

- `src/lake/Lake/CLI/Serve.lean`, blob `27d3e89530105b7ea9fe9f951b9459c1ee1f9cc9`: `lake serve` process launch, workspace/environment/global server arguments, configuration-error fallback, `lake setup-file`, exit codes, workspace loading, and `setupServerModule` invocation.
- `src/Lean/Server/FileWorker/SetupFile.lean`, blob `35a756819a8de5ebb05256bb39d83148f9f24145`: worker invocation of `setup-file <path> -`, header JSON on stdin, dependency-build policy, no-build/no-cache mode, exit-code mapping, JSON parsing, and dynamic-library loading.
- `src/lake/Lake/Build/Module.lean`, blob `21c5f343112a1690390188642a05d6092432ab84`: server-module setup, edited/external module paths, dependency/import/plugin/dynlib fetching, transitive import artifacts, server options, ordinary module build path, and explicit note that setup-file top-level builds do not construct proper trace state.
- `src/Lean/Setup.lean`, blob `38e7f619e852e8ae17d13c94de35a25d279387b6`: `ImportArtifacts`, server olean selection, `ModuleSetup` fields, JSON serialization, and setup-file loading contract.
- `src/Lean/Server/FileWorker.lean`, blob `c803034ed8810f13a5ef38a603a21e610efca2bc`: import-header callback, setup result handling, out-of-date fail-closed diagnostic, option merging, setup-to-language-processor transfer, and one-import-load-per-worker restart rule.
- `src/lake/Lake/Config/LeanLib.lean`, blob `077efb6c244fd53bab5dead6c850d40161c96e7f`: library server-option composition and distinction from ordinary Lean options.
- `src/lake/Lake/Config/Workspace.lean`, blob `b9c01f130240ae7c65ee298778351ddbe312374e`: workspace server options for external files and workspace environment state.
- `src/lake/Lake/Config/Package.lean`, blob `2c73b6a471d6face8084c8b1957f5b802cfa90b7`: package global/server options and environment/path configuration.
- `src/lake/Lake/Config/PackageConfig.lean`, blob `27a50fb2a713a6bb590260fd4a82d135c2b84952`: `moreGlobalServerArgs`, `moreServerArgs`, and package-level server/build configuration.
- `src/Lean/Data/Lsp/Internal.lean`, blob `bd64732ada62ab8127091ef690fa13f85acb4071`: language-server setup-status notification data, including whether `lake setup-file` failed and the direct imports.
- `src/Lean/Language/Lean.lean`, blob `124d4739bc910eb30ec35844348c785bf9f6c70a`: `SetupImportsResult` and the point where server-derived setup enters Lean's incremental language processor.

No evidence above is fresh **execution**. Source comments documenting intended use are treated as upstream **documentation** embedded in the pinned source. The conclusion that a prepared interactive environment has distinct process-launch and per-document setup obligations is **derived** from these source paths.
