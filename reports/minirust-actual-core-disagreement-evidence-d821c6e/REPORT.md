# Actual MiniRust core probes and disagreement evidence classes

## Summary

The exact pinned MiniRust specification was translated with the exact pinned Specr transpiler and its real generated core was built and exercised. Twenty-three selected upstream tests passed. Eight owned core-API cases additionally distinguish valid/invalid Boolean representation, unchecked overflow, enum tagger/discriminator coherence and wide-pointer union metadata preservation.

The real core confirms two useful boundaries: a checker-admitted incoherent enum can encode variant 1 and decode variant 0, and an accepted one-word union chunk can discard the second word of a wide pointer. These are concrete core observations. The investigation does not run minimize, establish that rustc emits either candidate type, compare Miri, or prove a general semantic correspondence.

## Applicability

MiniRust is `d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`; Specr/libspecr is `15200eb5e676e2ee91f43bd79e674f8fc32e5348` (0.1.41). Their acquired source archives are retained and hash-bound. Every tracked file was checked against the pinned Git blob inventory before and after execution: 368 MiniRust files and 61 Specr files, with no mismatch.

The transpiler was built using installed rustc 1.99.0 `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`. The successful core/test compiler is the specification's requested nightly 2026-05-01: rustc 1.97.0-nightly `f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, host aarch64-apple-darwin. Cargo 1.99.0 `5f94df4789f005f9a352888e8355ffc645b7ed0e` drives this compiler explicitly; that pairing was observed to work for this bounded build. The modeled target is miniutil's `DefaultTarget = x86_64`, independent of the Apple Silicon host. Memory is `BasicMem`, which omits alias enforcement.

Only generated core, unchanged miniutil/minitest crate sources and the owned harness were built. Minimize, rustc-dev, source Rust lowering and the installing `mini` helper script were excluded. All Cargo home/target/generation outputs were task-private. No global cache/toolchain installation or source-code patch was made. Official compiler/host-stdlib archive hashes are preserved; their task-private assembly was coordinated by the parent investigator.

## Findings

### 1. The real source-to-generated-core path is retained

The source archives are 224,303 B and36,679 B, with SHA-256s `0b808e620296bde607ed6cf74642f39a023c2dbf9fe842d458fdfb69392913c0` and `7e39738319f77a43fd0ce8e185888306b3a777f7b3f9d3234ec1802b9da5e220`. Specr's exact lock lists 42 registry packages. Twenty-five cached crate archives were checksum-verified and copied into a private Cargo home; the remaining 17 were fetched separately. Initial private Cargo storage was 28,716,688 B, well below the authorized250MB dependency cap.

Generation/build-script inspection preceded compilation. The inspected crates use local code generation, compiler-version/feature probes and task-private OUT_DIR outputs; no extra C/native-library toolchain was needed. The actual Specr build was offline/locked and succeeded. A separate harness TOML selected the exact local libspecr source and the original MiniRust attributes. The generator produced 5 files totaling 288,411 B.

The harness workspace contains only unchanged miniutil/minitest copies and excludes the generated crate as the original workspace does. Its owned manifest removes coupling to minimize without changing upstream Rust source. The exact original, harness and owned-probe lockfiles, generated Rust bytes, observed generated manifest and command/status logs are preserved.

This is actual execution of the pinned Rust transpiler and generated interpreter. It still trusts the transpilation and support-library implementation; no import correctness theorem was checked.

Basis: **execution**, source verification, fetch/build/generation status and generated-file manifests; **source**, exact manifests/scripts.

### 2. Compiler availability, incompatibility and semantic outcomes are different evidence

The first alternate-host attempt used rustc 1.99 with explicitly recorded `RUSTC_BOOTSTRAP=1`. Specr compiled, but libspecr failed with E0046: its unstable `Step` implementation lacks the newer required `forward_overflowing` and `backward_overflowing` methods. The build stopped before any core test ran. This is a compiler-API incompatibility for that pairing, not evidence that a MiniRust program is ill-formed, UB or unsupported.

A previously present nightly 2026-02-05 directory had Cargo but no rustc executable. Its version-check path stopped without compilation. This is toolchain availability, not a language result.

The requested nightly was then assembled privately from official rustc and host-stdlib archives, whose compressed sizes total96,323,496B. No rustc-dev/rust-src/LLVM-tools component was needed. The exact requested-nightly core build succeeded offline/locked with `RUSTC_BOOTSTRAP` unset. Observed core compilation took 10.43 s; the small transpiler/owned builds were also bounded. These single-host timings are reproduction facts, not performance benchmarks.

Basis: **execution**, separate compiler status/logs and official distribution manifest/archive hashes. Initial ordinary helper/parser errors and the unavailable compiler are not accepted semantic outcomes.

### 3. Selected upstream tests exercise the actual generated interpreter

| Upstream test filter | Passed | Interpretation |
| --- | ---: | --- |
| `tests::no_preserve_padding::no_preserve_padding` (exact) |1| A typed aggregate copy makes padding unavailable to a later integer load |
| `tests::no_preserve_prov::no_preserve_prov` (exact) |1| An integer-array rewrite strips reference provenance and later reference validity fails |
| `tests::bool::` |6| Boolean casts/logical operators follow the tested branches |
| `tests::enum_representation::` |15| Selected coherent and ill-formed enum representation cases |

All commands returned zero with zero test failures and no unexpected host panic. The tests expect some core programs to report semantic UB or ill-formedness; passing does not mean every input core program terminates normally.

These are sampled concrete machine executions, including BasicMemory allocation choices. Passing 23 tests does not prove universal safety over all allocation choices, targets or programs. The preserved command filters/counts prevent a zero-test invocation from being counted as success. The named Boolean tests concern operators; the separate owned Boolean transmutation cases below test invalid representation.

Basis: **execution**, four complete test logs and `selected-test-results.json`; **source**, retained source archive test files.

### 4. Actual scalar controls distinguish validity from mathematical values

The owned safe Rust harness constructs MiniRust ASTs and invokes the real generated `run_program::<BasicMem>` API. It never performs invalid native Rust operations.

| Owned core case | Observed result |
| --- | --- |
| u8 byte 1 transmuted to bool | MachineStop |
| u8 byte 2 transmuted to bool | semantic UB: transmuted value is not valid at new type |
| unchecked u8 addition 255+1 | semantic UB: overflow in unchecked add |

The result distinguishes MiniRust's mathematical semantic integers from bounded/unchecked operator requirements. It also supplies a real-core negative control for an importer that were to treat every initialized byte as a Boolean. It does not establish all cast or overflow semantics.

Basis: **execution**, `actual_core_probe.rs`, `actual-results.json`, `owned-run.log`.

### 5. The enum coherence counterexample is accepted and discriminates in the real core

The enum type has size/alignment 1, variants 0/1 with empty one-byte all-padding tuple payloads, u8 taggers writing 0/1, and `Discriminator::Known(0)`. The program constructs variant 1, stores it, typed-loads it into another enum local and branches on its discriminant.

The real core returns MachineStop when the expected discriminant is 0. The same type with a coherent tag-reading discriminator returns MachineStop when the expected discriminant is 1. Keeping the incoherent discriminator but expecting 1 reaches the deliberately placed core Unreachable branch and reports `Ub("reached unreachable code")`.

Thus the type/program pass the real core's well-formedness checks, yet the typed storage round trip changes the represented variant. This upgrades the earlier [source/fragment analysis](../minirust-representation-copy-provenance-laws-d821c6e/REPORT.md) with direct generated-interpreter evidence. The negative control ensures that the observed branch is consequential.

The finding is about arbitrary core types admitted by these checks. No real Rust enum layout or minimize-produced type is shown to be incoherent. A frontend may enforce a stronger invariant. Generic representation theorems must include that coherence invariant or strengthen the accepted type definition.

Basis: **execution**, three owned core cases; MiniRust representation/WF **source**; **derived**, theorem-domain implication.

### 6. Wide-pointer union chunk coverage changes actual core behavior

The second candidate uses a 16 B union containing one `*const [u8]` field on modeled x86_64, alignment 8. A raw wide pointer to an initialized local byte array carries length 3. The program transmutes pointer→union→pointer and checks metadata 3.

With chunks[(0,16)], the program reaches MachineStop. With identical fields/layout and chunks[(0,8)], the real core accepts the type/program but later reports `Ub("transmuted value is not valid at new type")`. Union encoding retains the first word and resets the metadata word to Uninit; the pointer decoder then lacks initialized metadata.

The companion memory investigation identifies a source-level candidate in minimize's pointer chunk marking. This execution validates the candidate core type's behavior, not the unexecuted Rust-to-MiniRust translation. The actual translator-output claim remains separate. No Tree Borrows or alias-model comparison follows from BasicMem acceptance.

Basis: **execution**, full-versus-short chunk controls; MiniRust union/wide-pointer **source**; **derived**, why a translator's chunk coverage matters.

### 7. A disagreement corpus must retain outcome classes and authority separately

The performed corpus demonstrates the following classification discipline:

| Evidence | What it establishes | Stronger inference not justified |
| --- | --- | --- |
| Host compile error or missing compiler | Configuration-specific tool failure | Semantic UB or unsupported object-language input |
| Core IllFormed result | Selected core WF rejection | Source Rust rejection or unsoundness |
| Core Ub result | One interpreter run reached a modeled UB branch | Every Rust/Miri/compiler execution has that outcome |
| Core MachineStop | One represented execution terminated normally | Universal safety under all choices |
| Coherent/incoherent control pair | The selected rule distinguishes these core ASTs | General source/core equivalence |
| Lean/Python fragment witness | The stated owned model property | Identity with generated interpreter unless separately related |

No implementation is treated as a normative oracle. MiniRust is the selected source for its own pinned core definitions; the Rust Reference, Miri and rustc have independent identities and authority boundaries. Disagreement with a source-stated generic law, as in the enum case, is an internal specification-consistency finding; it still needs an explicit account of the admitted type domain.

Basis: **derived**, using the actual preserved failures and discriminating executions. This report supplies performed validation and a concrete evidence corpus, not a new universal correspondence theorem.

## Boundaries

- **Established:** exact source verification/generation, requested-nightly actual-core build, 23 selected upstream test results, 8 owned actual-core outcomes and version-scoped compiler failure classification.
- **Unestablished:** MiniRust/Specr formal-import adequacy, a Rust-to-MiniRust source-safety theorem, all generic codec laws, actual minimize production of either candidate type, full memory-model compatibility or Miri equivalence.
- **Not run:** minimize, rustc-private translation, Miri, compiled invalid Rust, TreeBorrowsMemory cases, exposed `predict`, or multi-target/concurrent exhaustive execution. The sampler and unimplemented prediction limitations remain.
- **Known scope:** the modeled target is x86_64 and memory is BasicMem. Host aarch64 does not change that selected target. The tests are finite and their allocator choices are executable samples.
- **Reproduction cost:** the compiler/dependency artifacts are intentionally outside the report package; official hashes, source archives, lockfiles and portable preparation inputs are retained. A local build directory is not required to understand the evidence.

## Evidence

Acquired 2026-10-14. `source-evidence.json` and `support/status/` preserve exact source/toolchain/archive/lock/generated identities. `support/archives/` retains the small pinned source archives. `support/generated/` preserves the actual generated Rust files and observed manifest; `support/locks/` holds all three relevant lockfiles. Upstream source licenses are included.

The source entry points are [MiniRust pin](https://github.com/minirust/minirust/tree/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed), [Specr pin](https://github.com/minirust/specr/tree/15200eb5e676e2ee91f43bd79e674f8fc32e5348) and [requested nightly manifest](https://static.rust-lang.org/dist/2026-05-01/channel-rust-nightly.toml). Logs retain actual effective commands and results; absolute historical paths inside logs are provenance, not required replay paths.

Historical command, generated-manifest path and log strings are explicitly path-normalized for publication; `public-path-projection.json` records original and public hashes. Raw process statuses and technical outcomes are unchanged. Historical producer hashes refer to their original observations; the package file manifest binds the published bytes. The retained Rust/Lean program and source-archive bytes are unchanged.

## Revalidation

`support/prepare_replay.py --work <empty-task-directory>` verifies/extracts retained archives, copies unchanged test/helper sources and stages the retained generated interpreter plus owned probe. It performs no network/compiler execution. Preparation itself was run successfully. The owned eight-case corpus was then rebuilt and run offline/locked from this package-only prepared tree; every outcome matched the original corpus, with no unexpected panic.

Use the exact compiler described above, explicit task-private CARGO_HOME/CARGO_TARGET_DIR and installed Cargo. Fetch the prepared workspace's locked dependency closure as a separate step, then build/test with `--offline --locked`. Run the four recorded filters and the owned probe. A fresh environment needs the official rustc+host-stdlib components and registry dependencies; it needs no rustc-dev or global installation.

For a change to Specr, regenerate from exact source using an isolated config pointing to the pinned support library, then retain new output hashes and rerun the corpus. Filesystem enumeration can change declaration order, so byte equality of regenerated output is a separate check. For a proposed source-language discrepancy, execute and preserve the real lowering separately; these core fixtures cannot stand in for minimize output.

*Authored by an AI agent acting on joshlf's behalf.*

