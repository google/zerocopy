# Relocating Anneal's Nix-packaged Rust and Lean toolchain trees

## Summary

On `aarch64-darwin`, the Rust and Lean recursive fixed-output trees selected by Anneal's pinned flake were copied outside `/nix/store` and the copied executables successfully reported versions and compiled/ran small programs. Each copy's NAR hash and complete path/type/mode/size inventory matched its store source. This establishes direct use from the copied paths on this host while `/nix` remained mounted; it does not establish operation with the original store unavailable or relocation of the final omnibus archive.

## Applicability

The probe used the Anneal flake at `google/zerocopy@41f5b37afe7060fd9fe08c00b200672cd76d77b9`, Nix 2.35.2, and an Apple Silicon Mac running Darwin 25.6.0. The Rust output is the synthesized `nightly-2026-05-31` tree. The Lean output is Lean `v4.30.0-rc2` at commit `3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`. The exact source-output identities and declared hashes are in [`relocation-observations.json`](relocation-observations.json).

For each tree, the source was the Nix store output and the destination was a project-local scratch directory outside the store. The probe copied with `cp -a`, compared full inventories and recursive NAR hashes, then ran the copied command-line tools. The source and destination coexisted and the store stayed mounted throughout.

## Findings

### Both copied trees retained their Nix fixed-output identity

`nix hash path --type sha256` returned the same hash for each store output and its copied tree, matching the `aarch64-darwin` hash declared in `anneal/flake.nix`:

| Tree | NAR SHA-256 | Inventory |
| --- | --- | --- |
| Lean 4.30.0-rc2 | `sha256-dpUCCLkhoGDKkDKPZxr7WrmkifxHi4MWLpD148z2vhg=` | 14,447 entries; inventory SHA-256 `77c2af70d52e0f6c48d429def71b9aa495a34e98a5d5d2f1c57a27680b89460a` |
| Rust nightly-2026-05-31 | `sha256-X7ndqbjsmnjL6KZzNCxkVFJPzAsAjUqerD/wc1rxK5E=` | 8,193 entries; inventory SHA-256 `d94ef08200855aa736c74040bca79a50b432b5396a140abc4c972d9097e1d388` |

Both inventories reported zero symlinks. The copied `bin/lean`, `bin/lake`, `bin/rustc`, and `bin/cargo` were regular files with mode `0555`. The respective tree sizes were 2.5 GiB and 1.6 GiB.

Basis: **execution** using `nix hash path` and byte-identical source/copy inventories.

### The copied command-line tools ran at their new paths

From the copied Rust tree, `rustc --version` reported `1.98.0-nightly (f8a08b688 2026-05-30)`, `cargo --version` reported `1.98.0-nightly (fbb61be30 2026-05-26)`, and a Rust smoke program compiled and printed `relocated rust ok`.

From the copied Lean tree, `lean --version` reported Lean `4.30.0-rc2`, `lake --version` reported `5.0.0-src+3dc1a08`, and a Lean smoke program run with `lean --run` printed `relocated lean ok`.

`otool -L` showed the copied Rust compiler using `@rpath/librustc_driver-c20cab87d43f5461.dylib` and the copied Lean executable using `@rpath` Lean libraries. Their load paths were relative to the executable: `@loader_path/../lib` for Rust and `@executable_path/../lib` plus `@executable_path/../lib/lean` for Lean.

Basis: **execution**. The complete smoke sources are preserved as [`smoke.rs`](support/smoke.rs) and [`Smoke.lean`](support/Smoke.lean); commands and output are in the support logs.

### This is a tree-copy result, not a final-archive relocation result

The tools ran from copied Nix outputs while the original `/nix/store` paths remained present. The probe did not use `otool` to scan every Mach-O file in either tree, hide or detach the original store, invoke the combined Aeneas/Charon/Mathlib environment, or build and move the omnibus archive. A runtime dependency could still have resolved from the mounted store. The result is therefore limited to successful use from the copied roots under this host's normal runtime environment.

Basis: the **execution** setup and **derived** scope limit.

## Boundaries

**One host and architecture.** No Linux ELF result or cross-architecture claim follows from this `aarch64-darwin` run.

**Original Nix store stayed available.** The run did not demonstrate store-independent execution.

**Not the omnibus archive.** The copied trees were the Rust and Lean fixed-output outputs, not `omnibus-tar` or a compressed archive. They do not cover Aeneas, Charon, Mathlib, Lake package configuration, or end-to-end generated-workspace operation.

**Limited smoke programs.** The Rust and Lean probes demonstrate startup and a minimal compile/run path; they do not validate Anneal verification workloads.

## Evidence

The experiment ran on 2026-09-27 with Nix 2.35.2, macOS arm64, Darwin 25.6.0, and 8 GiB RAM. The source outputs were the flake's recursively hashed `aarch64-darwin` Rust and Lean trees. NAR hashes, inventory counts/hashes, selected load paths, command versions, and resource readings are preserved in [`relocation-observations.json`](relocation-observations.json).

The minimal smoke sources and scripts used to copy, inventory, and exercise these fixed outputs are under [`support/`](support/). The exact source-map identity is in [`source-map.json`](source-map.json). No store garbage collection was performed.

Evidence roles: **source** for the flake output definitions; **execution** for copying, inventory, hashing, Mach-O inspection, and smoke commands; **derived** for the stated limits.

## Revalidation

For each exact flake output, build serially, copy it with metadata preservation to a distinct location outside the Nix store, compare its NAR hash and a complete no-follow path/type/mode/size/symlink inventory, then invoke the copied entry points and compile/run minimal Rust and Lean programs. Record Nix version, host, architecture, output paths, and resource readings.

To claim independence from the store, use a disposable system or VM where the original `/nix/store` can safely be made unavailable after the copy. To claim omnibus relocation, build and move the actual archive and test its complete Aeneas/Charon/Rust/Lean/Lake workflow separately.
