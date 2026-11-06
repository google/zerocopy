# Invocation-stage findings

## Build-script output is added after dependencies finish

Cargo cannot finish every compiler command while building the graph because build scripts have not yet executed.

The rustc job captures relevant build-script identities, but its execution closure waits for dependencies. It then reads `BuildScriptOutputs` and applies `add_native_deps`, `add_plugin_deps`, and `add_custom_flags`. These add native search and link state, plugin search paths, build-script compiler flags, and environment variables. The source explicitly says these values are discovered only at runtime.

Stable `cargo metadata` and the unstable unit graph therefore cannot reconstruct the complete final compiler process by themselves.

Basis: **source**.

## Unit dependency edges become --extern and search-path arguments

`build_deps_args` reads direct `UnitDep` values, adds computed search paths, emits `--extern` arguments for linkable Rust dependencies, sets `OUT_DIR` from the package's build-script execution, and exports artifact-dependency paths through environment variables.

The graph explains why a dependency input exists. The final process state records the concrete artifact path Cargo passed. Those are complementary forms of evidence.

Basis: **source**.

## Compiler wrappers change the executable chain

Cargo's `Rustc::process()` creates the selected compiler wrapped by the general wrapper. `workspace_process()` additionally inserts the workspace wrapper. `Compilation::rustc_process` chooses the workspace process for workspace members, the default process for other units, or a primary-unit override when installed.

Cargo's documentation states that, when both wrappers are configured, the effective invocation is:

`$RUSTC_WRAPPER $RUSTC_WORKSPACE_WRAPPER $RUSTC <rustc arguments>`.

The wrapper receives the next executable as its first argument. The workspace wrapper also affects Cargo's artifact hash, so it is not merely an observational layer.

Basis: **source** + **documentation**.

## Compiler flags and wrappers are independent dimensions

The Cargo reference separates compiler selection, wrapper selection, and flags. `RUSTC` or `build.rustc` selects the compiler executable. `RUSTC_WRAPPER` and `RUSTC_WORKSPACE_WRAPPER` alter the process chain. `RUSTFLAGS` or `CARGO_ENCODED_RUSTFLAGS` add compiler arguments.

Target- and profile-derived rustflags also participate in unit state. Recovering "what rustc Cargo invoked" therefore requires both process identity and argument state.

Basis: **documentation** + **source**.

## The unit graph is a plan, not a final argv transcript

The unstable unit graph exposes package ID, Cargo target, effective profile, platform, mode, features, standard-library status, dependency edges, and roots. It can answer structural questions such as which sibling library is required, which units are host-side, and whether a build script has a separate execution node.

It does not serialize the final `ProcessBuilder`, and build-script-derived state does not exist when the graph is created. The graph also includes non-rustc work such as `run-custom-build`, while documentation modes can invoke rustdoc.

Claims about exact compiler argv, environment, wrapper chain, or dynamically supplied link state require evidence beyond the unit graph.

Basis: **source** + **documentation** + **derived**.

## A planned unit may not execute in a particular incremental run

After graph construction, `BuildRunner` fingerprints units. A fresh unit can be skipped.

Presence in the unit graph therefore means the build requires the unit's result, not that Cargo started a new compiler process during this invocation. Planned-work evidence and observed-process evidence answer different questions.

Basis: **source**.
