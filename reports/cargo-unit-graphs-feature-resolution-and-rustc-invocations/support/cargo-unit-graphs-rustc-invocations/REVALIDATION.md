# Revalidation

For a later Cargo revision, resolve the exact Cargo source first. Recheck root generation, `unit_dependencies.rs`, `prepare_rustc` and `build_deps_args`, late `BuildScriptOutputs` handling, compiler wrapper construction, and the current unit-graph schema.

For empirical confirmation, use a small workspace with a library, binary, integration test, build script, one dependency used in both normal and build contexts with different features, and a procedural macro. Record the pinned Cargo unit graph and verbose build output for both a native build and a cross-target build. Use a benign compiler wrapper that records the executable and argument vector it receives; repeat with both general and workspace wrappers configured. Preserve build-script output as well.

Compare planned units with observed actions. Check the build-script compile/run split, host-side proc-macro and build-dependency work, same-package library edges, build-script-derived flags that appear only after script execution, wrapper order, and the no-change second build where fresh units are skipped.

This confirms the observable graph-to-process mapping for the fixture and exact revision. It does not establish a stable unit-graph API or exhaustive behavior for every Cargo feature family.
