# Boundaries

- No fresh `lake serve`, `lake setup-file`, `lake build`, Lean server, or editor session was run.
- The report establishes the source-level preparation graph at Lean/Lake `v4.30.0-rc2`; it does not prove that a specific Anneal-generated project currently satisfies it.
- It does not establish the minimum filesystem subset needed for read-only server use. `setup-file` can build dependencies, write build/cache state, and return absolute paths; dedicated read-only experiments remain necessary.
- It does not establish relocation. The returned `ModuleSetup` can contain explicit artifact, dynamic-library, and plugin paths.
- It does not establish offline operation. Workspace loading, dependency materialization, and artifact fetching have separate possible network paths.
- It does not establish that an ordinary `lake build` of one chosen target has built every artifact that an arbitrary later edited header can request. A changed import header can require a different dependency closure.
- It does not establish that `--no-build --no-cache` is side-effect-free in every filesystem dimension; it establishes the worker invocation and fail-closed out-of-date result from source.
- It does not establish performance or how often a real editor/server calls `setup-file` under long-running workloads.
- It does not establish batch/server semantic equivalence, only the shared `ModuleSetup` interface and source-level option/artifact differences.
- It does not establish the complete `.ilean`/reference-index setup graph. Tactic-state lookup for the current file does not require every reference/index feature to be primed, while navigation features can require additional state.
- It does not prescribe whether Anneal should call Lake directly, cache `ModuleSetup`, or reproduce the setup contract another way.
- It does not assume adjacent Lean/Lake releases retain the same setup-file protocol or server behavior.
