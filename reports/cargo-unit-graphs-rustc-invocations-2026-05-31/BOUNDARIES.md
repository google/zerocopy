# Boundaries

- No fresh Cargo, rustc, build-script, procedural-macro, cross-target, or wrapper execution was performed.
- No fresh `-vv` transcript or wrapper-captured argv specimen is preserved here.
- The exact 2026-05-31 static Cargo binary was not independently mapped byte-for-byte to the studied source revision.
- Feature resolution is covered only where it explains distinct units. The separate **Cargo metadata feature resolution** subject remains open.
- Unstable artifact dependencies and `-Z build-std` are not exhaustively inventoried.
- Rustdoc and doctest work are mentioned only to bound the graph; their command construction is not exhaustively analyzed.
- A planned `Unit` is not evidence that its command ran in a particular incremental build.
- A unit-graph node is not always a rustc process: `run-custom-build` is build-script execution and documentation modes can invoke rustdoc.
- Build-script output changes later compiler process state, but this report does not claim a stable external API for reading that complete state.
- Wrapper nesting is established from source and documentation without fresh wrapper execution.
- This package records Cargo behavior; it does not choose an Anneal interception or result architecture.
