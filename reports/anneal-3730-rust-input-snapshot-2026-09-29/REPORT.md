# Cargo input closure and workspace ownership controls for an interactive Rust subject

## Summary

At one pinned Rust/Cargo toolchain, a dependency-free two-crate fixture produced different compiled output while `app/src/main.rs` stayed byte-identical: changing a file consumed by `include_str!`, selecting a Cargo feature, or changing the manifest's default feature altered the program. Changing a doc comment from `proof: alpha` to `proof: beta` changed a local derive macro's generated constant and the binary's output. A→B→A restored the original source hash/output but represented a later causal revision in a separate file-backed ownership control. A stale writer with the old A revision was rejected even after content returned to A.

These are compiler and filesystem facts for this fixture. They are counterexamples to treating one Rust source path, one source-file hash, or a comment-only edit as sufficient evidence of unchanged compilation semantics under arbitrary Cargo inputs/macros. They do not establish Anneal annotation attachment, Charon extraction, or proof validity.

## Applicability

The commands ran on macOS 26.6.2 arm64 with rustc `1.98.0-nightly` at `rust-lang/rust@f8a08b688cbe60acc386ed1fbd1b7cbaaf5576b1` and Cargo `1.98.0-nightly` at `rust-lang/cargo@fbb61be30e5f9ac3a6ad58e56a5c0f5db2d2b3ef`; executable SHA-256 values are in `REPORT.json` and `support/host.txt`. The fixture has an app and a path-only proc-macro crate, no registry dependencies, workspace resolver 2, one feature named `selected`, one included text file, and one derive macro that inspects the tokenized doc attribute. All Cargo invocations used `--offline --locked`, a fresh temporary `CARGO_HOME` and `CARGO_TARGET_DIR`, and the pinned `RUSTC` path. The driver ran eight ordered Cargo cases and preserved all input-file hashes, commands, stdout/stderr, exits, and binary hashes.

The additional overlay control directly invoked the same pinned rustc on a disk source and on different source passed through standard input. The ownership control used a file-backed `{revision, content}` state, `flock`, and atomic `os.replace` on the same APFS host; the scripted clients were interleaved in a fixed order. Those controls model interface choices rather than claiming an editor or Anneal engine implements them.

The experiment chiefly informs [#3731](https://github.com/google/zerocopy/issues/3731) I009, I011, I012, I014, I018, and I020. It narrows only one or two dimensions of each. The earlier `cargo-rust-charon-anneal-coverage-matrix-2026-09-28` report already shows broader Cargo/Charon target coverage and V1 behavior; this report isolates same-path mutation and ownership counterexamples, so it does not repeat that survey.

## Findings

### The main source pathname and bytes do not close the compilation input set

The baseline command printed `macro=1 included=alpha feature=0`. Replacing only `app/src/proof_note.txt` with `beta` printed `macro=1 included=beta feature=0`; the `main.rs` SHA-256 remained `50d20d8c...`. Restoring that file and passing `--features selected` printed `macro=1 included=alpha feature=10` with the same source, manifest, and lockfile hashes. Independently, editing only `app/Cargo.toml` from `default = []` to `default = ["selected"]` produced feature value 10 without a feature flag, then reverting it restored 0.

The precise observation is about program output under selected Cargo commands, not the full set of Charon or Anneal semantic inputs. It confirms that `include_str!` payload bytes, active feature selection, and feature defaults can matter even when the principal `.rs` bytes do not change. A cache keyed only on the main source file would collide on these cases. The choice of `--locked` also mattered: perturbing the local path package version in `Cargo.lock` while keeping source and manifests fixed made Cargo exit 101 with `cannot update the lock file ... because --locked was passed`. This is a lockfile acceptance/freshness control, not a demonstration that the altered lock bytes would change compiled semantics after resolution.

Basis: **execution**, `support/raw-results.json` `cargo.observations` cases `baseline`, `included-file-beta`, `cli-feature-selected`, `manifest-default-selected`, `manifest-revert`, and `stale-lockfile`; cache-key implication is **derived**. I009 still needs real subject closure including dependency versions, target/profile/cfg, build-script outputs, environment, external models, generated artifacts, and tool upgrades.

### A comment-like region can affect compiler output through a macro

The local `DocWitness` derive receives the struct's doc attribute, tests its token string for `proof: alpha` or `proof: beta`, and emits `Marker::DOC_TAG` as 1 or 2. Changing only that `///` line changed the run output from `macro=1` to `macro=2`. Reverting the source to A restored the original `main.rs` SHA-256 and program output; the raw record orders these as baseline → doc B → source A again.

This is a concrete counterexample to a proof-only edit classifier that unconditionally assumes Rust doc-comment changes cannot affect compilation. It does not imply every Rust comment is macro-visible or that Anneal's eventual annotation encoding is a doc comment. A classifier can safely shorten the invalidation path only after proving its storage syntax and all configured macro/build consumers cannot observe the changed bytes, or by treating uncertain cases conservatively.

Basis: **execution** of pinned rustc/Cargo and the preserved local macro source; design condition is **derived**. This partially informs I018. `include_str!` is a separate external-file input case, not a claim that ordinary Rust comments are directly read by `include_str!` without an explicit file path.

### Disk text, supplied text, and writer revision are independent ownership facts

The disk/standard-input control compiled `host.rs` containing `disk-A` and separately compiled an unsaved string containing `buffer-B`; both exited 0 and the binaries printed their respective values while the disk file remained unchanged. This demonstrates that a compiler can consume a different source snapshot from current disk bytes when a caller supplies one. It does not exercise an LSP open buffer, Cargo overlay, rustc virtual-file mapping, or Charon; I012's lifecycle matrix remains open.

In the file-backed multiwriter control, editor revision 1/A → revision 2/B succeeded, a stale agent's expected revision 1/A → C failed, editor revision 2/B → revision 3/A succeeded, and the agent's old revision 1/A → C still failed. At revision 3 the content hash equaled the original A hash; a hash-only guard would have accepted the old A request. The paired revision-plus-hash compare under `flock` rejected it. Thus content identity can support reuse, but an operation tied to a historical causal revision needs a separate guard. This is a controlled file fixture, not a proof of all concurrent schedules or distributed ownership semantics.

Basis: **execution**, `support/raw-results.json` `overlay` and `ownership`; distinction between cache identity and edit authorization is **derived**. These controls partially inform I011/I012/I014.

## Boundaries

- **Not examined:** Anneal V2's incomplete translation pipeline, historical V1 parser output, Charon LLBC, Aeneas generated Lean, Lean elaboration, or user proof obligations. The phrase `proof: alpha` is an invented fixture doc comment, not a claim about Anneal syntax.
- **Not examined:** a real editor open/change/save/rename/delete lifecycle, multi-document atomic edit, concurrent process race, or shared MCP/LSP client. The overlay is rustc stdin; the CAS schedule is sequential and controlled.
- **Not examined:** compiler-backed annotation attachment for cfg-removed items, macro-generated functions, aliases, trait defaults, local items, or repeated names (I019). The selected feature changes an ordinary `let` value, not annotation identity.
- **Not examined:** all environment variables, target triples, build scripts, dependency resolution across registry versions, external proof/model files, or native links. Toolchain identity is pinned but not perturbed. The small fixture therefore does not establish a minimum sufficient I009 input tuple.
- **Not examined:** tolerant discovery under malformed typing, annotation moves/duplicates, shared helpers, unavailable Rust models, or authored-source preservation through regeneration (I017/I021–I024). The conclusions are deliberately limited to input closure and ownership controls.
- A successful Cargo run establishes compiled program behavior for these inputs, not semantic equivalence of two Rust programs or completeness of any verification claim.

## Evidence

- `support/fixture/` preserves all two-crate source files, manifests, `Cargo.lock`, and included text. `support/raw-results.json` records SHA-256 for each fixture file and every mutated case. The canonical JSON of the sorted fixture file-hash map has SHA-256 `2e78b1712c66a02a2167b2102e16c4dfe0b60ecb75e1b89d1bae320640b2561f`.
- `support/probe.py` is the complete replay driver, SHA-256 `4101c4def098de100aaa87b2cb8002d7f22ff7872717f50950a8fa6cee37b079`. It creates a disposable copy under its own package, invokes exact toolchain binaries without network dependencies, and removes build output at completion.
- `support/raw-results.json` preserves all eight Cargo command/result records, tool versions, disk-versus-stdin rustc commands/results, file ownership operations, input hashes, and assertions. `support/command.stdout` has the one-line summary. `support/host.txt` identifies macOS, Python, rustc/Cargo revisions and binary hashes, harness hash, and the report checkout parent `37a0ecd080d333f93bfe900d9c7dab193608e478`.
- Existing corpus context: `cargo-rust-charon-anneal-coverage-matrix-2026-09-28` for actual Cargo/Charon/V1 coverage, `rust-conditional-compilation-nightly-2026-05-31` for pinned cfg mechanics, `generated-rust-visibility-nightly-2026-05-31` for macro/build generation, and `anneal-v1-source-scanner-versus-rustc-main-41f5b37` for historical scanner/compilation differences. Their claims are not re-executed by this package.

Run `python3 support/probe.py` from this package directory. The expected successful summary reports eight Cargo cases, true input-closure assertions, `disk-A`/`buffer-B`, and `ABA_hash_only_would_accept: true`. The runner needs the exact installed toolchain path recorded at the top of the script; at another host, change that path and record the new executable identity.

## Revalidation

At a new Rust/Cargo pin, rerun the package and compare every command's selected inputs and output, especially the doc derive and `--locked` rejection. For Anneal, replace the toy marker with its chosen annotation encoding, capture the complete Cargo/Charon compilation subject and source bytes, then test whether proof-text edits can influence macro/build inputs before offering a proof-only fast path. Re-run the ownership schedule through real open-buffer, disk, and agent edit APIs with a versioned compare-and-swap; a hash-only A→B→A success should be treated as a failing control for stale edit authorization.
