# Evidence

**Source — primary Cargo revision.** `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`.

- `src/cargo/ops/cargo_compile/mod.rs`, blob `aae55186a3701da74a7dbf940ca2c06baf101c4b`: compilation pipeline, root generation, graph construction, sharing and dependency hashing.
- `src/cargo/core/compiler/unit_dependencies.rs`, blob `2d0ea7c3c62bfa3bd76730dcfacf052d0e8268ef`: recursive dependency units, same-package library edges, host proc-macro/build-script treatment, build-script compile/run split, linked build-script dependencies.
- `src/cargo/core/compiler/unit_graph.rs`, blob `944b062cddf6cb617e93a31d72e9d4a8ccb7675a`: `UnitGraph` and `UnitDep`.
- `src/cargo/core/compiler/mod.rs`, blob `746e01d01e256f254481160467b025afc220d2fe`: rustc job creation, static command construction, dependency arguments, and late build-script-derived state.
- `src/cargo/core/compiler/compilation.rs`, blob `2249c8a1b4bd6f2604f2a6781b6228351664b5bb`: compiler process selection and wrapper templates.
- `src/cargo/util/rustc.rs`, blob `42c06ecabe6601a6002834f6b52c43987ca29d2d`: general/workspace wrapper construction.
- `src/cargo/core/compiler/custom_build.rs`, blob `f4f77b7095057bb39f6ade77f79961abba671259`: build-script output state.

**Documentation — same Cargo revision.**

- `src/doc/src/reference/unstable.md`, blob `139b7f7491e0754b8dbf7518490ade02ba751cc2`: unit-graph schema and `run-custom-build`.
- `src/doc/src/reference/config.md`, blob `2a2f94376b831ca405a1150b1f15eaab7c563446`: compiler and wrapper configuration.
- `src/doc/src/reference/environment-variables.md`, blob `df1b180a0971d4890f70eb8bf5425c5aa6f44a97`: compiler selection, wrapper nesting, and rustflags.

**Source — toolchain relation.**

- `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`: Cargo submodule points to the studied revision.
- `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`: Anneal selects the 2026-05-31 Rust toolchain.
- `AeneasVerif/charon@a535e914f74db4fd9e6be7048f4233270d8945c0`: `rust-toolchain` selects `nightly-2026-05-31`.

There is no fresh **execution** evidence in this package.
