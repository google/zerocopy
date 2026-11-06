# Findings

## Roots expand into a recursive build graph

Cargo first generates top-level `Unit` values for command-selected targets, then calls `build_unit_dependencies` to walk resolved dependencies and construct the `UnitGraph`. Only after that does `BuildRunner` fingerprint units, create jobs, and drain the dependency queue.

Command-line target selection therefore chooses roots; it does not enumerate every crate Cargo will compile. A later whole-graph pass also fills dependency hashes and safely shares units that initially had to remain distinct.

Basis: **source**.

## Non-library targets can depend on the same package's library

Cargo adds this relation explicitly because package resolution does not return a package as its own dependency. In `compute_deps`, binaries, tests, examples, and similar non-library targets can acquire the package library through `maybe_lib`. Integration tests and benchmarks can additionally cause binary targets to be built.

A command selecting one binary can therefore require a separate library compiler unit before the binary unit.

Basis: **source**.

## Host-executed dependencies split from target work

Ordinary dependency units derive their compilation kind from the parent and dependency target. Procedural macros are special because they execute in the host compiler process, so Cargo treats them as host-side work. Build scripts are likewise compiled for the host.

A cross-target library can therefore depend simultaneously on target-compiled ordinary libraries and host-compiled proc macros or build machinery.

Basis: **source**.

## A build script has a compile unit and an execution unit

`compute_deps_custom_build` makes a `run-custom-build` unit depend on another unit that compiles the build-script target. That compile unit is explicitly `CompileKind::Host` and `CompileMode::Build`.

Cargo later executes the resulting program as the separate `run-custom-build` node. `connect_run_custom_build_deps` can add dependencies from that execution to build-script executions of relevant linked packages.

"The build script" therefore names two distinct kinds of work: compiling its Rust source and running the compiled program whose output directs Cargo.

Basis: **source**.

## Build and proc-macro contexts can duplicate package compilation

Cargo preserves separate units when one package participates as ordinary target code and as host-side build/compiler machinery. With decoupled feature resolution, the same dependency can have different normal and build feature sets.

The build-script dependency code records a concrete consequence: a build script can be compiled twice when normal and host/build features differ because the script can inspect `CARGO_FEATURE_*` at runtime. Collapsing those units would change observable behavior.

Basis: **source**.

## A rustc command is assembled from unit state and dependency artifacts

For an ordinary Rust unit, Cargo's `rustc` job calls `prepare_rustc`. Static command construction adds crate name, edition, source path, crate types, output mode, target selection, effective profile/codegen settings, configured rustflags, and Cargo's diagnostic protocol.

`build_deps_args` then adds library search paths and `--extern` arguments derived from direct dependency units and their produced artifacts. A graph edge is therefore not merely a scheduling relation; for Rust dependencies it becomes a concrete compiler input.

Basis: **source**.

Further invocation-stage findings are in [FINDINGS-INVOCATIONS.md](FINDINGS-INVOCATIONS.md).
