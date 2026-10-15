# Caller-bound Rust capture with actual instances and generated owners

## Summary

An actual pinned `rustc_driver` observer captures a caller-selected configured Rust crate, including expanded local owners, typed MIR bodies, concrete trait/generic instances, evaluated scalar constants, closure bodies and generated Drop glue. The consumer independently repeats that compiler observation from its own request and compares the complete captured payload with an untrusted data candidate.

The final 34-control matrix matches every expected outcome: five alternate captures, six accepted candidate/request pairs and 23 rejections. A changed MIR operator with unchanged names/source hashes rejects, as does coherent removal of a Drop operation and its glue. Five valid native subjects also match their expected outputs on every u8 input. This is a bounded E04 capture prototype, with the compiler, observer and reader still trusted. It supplies no E10 Rust-source-safety theorem.

*Authored by an AI agent acting on joshlf's behalf.*

## Applicability

The compiler is task-private nightly 2026-05-01: rustc 1.97.0-nightly, commit `f53b654a8882fd5fc036c4ca7a4ff41ce32497a6`, LLVM 22.1.4, host/target `aarch64-apple-darwin`. rustc-dev and compiler sources are already installed. No Cargo, network, installation, external crate build or query-provider override is used. The exact compiler launcher, driver dylib and target core archive are bound in [the tool identity record](support/tool-identities.json); the observer binary is identified by SHA256 `656fb5eaac61cecbed4b59b90ff5842cf2594551310084d599d66c9af817f636`.

Requests admit edition 2021, target CPU `apple-m1`, opt-level 0, MIR opt-level 0, panic abort, and either no cfg feature or `feature="flip"`. The requested root is a nongeneric local function with u8 input/output; generic calls underneath that root are instantiated. One to four explicitly selected UTF-8/LF `.rs` files are copied to a fresh snapshot. The compiler remaps that snapshot to the caller-fixed `/owned-source` namespace. That remap is part of the configured compilation, including any path-sensitive meaning; no equivalence to an unremapped compilation is asserted.

Observed native execution uses the same compiler/configuration on Darwin kernel 27.0.0, arm64. The capture process stops after analysis and queries; it does not emit the final program binary. Native corroboration separately compiles the unchanged selected source as an rlib, links a small safe Rust observer, and calls the selected function on all 256 byte inputs. Compilation and those executions are observations, not proof-producing code generation.

## Findings

### F1. The caller request fixes the subject before candidate interpretation

Basis: owned source + execution.

[capture.py](support/capture.py) receives separate `--request` and `--candidate` paths. The request fixes source-file hashes, root file/item/signature, crate name, edition, target/CPU, cfg features, source namespace and trusted tool/observer identities. It admits the actual driver/core artifact locations rather than accepting an arbitrary file named by a purported identity. A changed driver-file selector is rejected even when its supplied digest correctly describes that other file.

The consumer checks/copies the selected source bytes, constructs the compiler argv itself and requires successful actual observation. It hashes tools before/after and checks snapshot bytes afterward. Compiler-reported source names/text must equal the complete requested graph; extra file/environment dependencies and unstable language/library features reject. The request is caller authority, not a statement supplied by the candidate producer. This assumes a trusted/cooperative caller and local filesystem; private directories, read-only file modes and hashes are not an OS sandbox against a malicious same-user process.

The candidate is JSON data, never a compiler command or executable. Duplicate keys, nonfinite numbers, unknown fields, malformed tags, invalid explicit local/block references and dangling/missing dependency edges reject. A well-shaped candidate must then equal the consumer's complete independently captured object. Reordering JSON object keys does not change its meaning. This is exact equality of the versioned compiler projection, not a semantic-equivalence certificate for an altered program.

### F2. The selected payload contains operations and resolved dependencies

Basis: pinned compiler source + actual query execution.

The observer implements only `after_analysis`; it does not replace borrow-checking/type-checking queries. At this pin, the driver runs analysis before the callback, and required analyses request unsafety/borrow checks. See [the callback gate](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_driver_impl/src/lib.rs#L321) and [required MIR checks](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_interface/src/passes.rs#L1139). No claim that these implementations are themselves verified follows.

The structured MIR projection retains each local's type/mutability and selected instantiated layout; every basic block and cleanup marker; StorageLive/Dead; assignments with places/operands/rvalues; branch destinations; calls and their resolved instances; Drop and its resolved glue; unwind information; required constants and evaluated scalar bits; argument/spread metadata; and source/expansion origins. Types, HIR, instance/aggregate kinds and some compiler enums remain exact pinned debug renderings. The reader does not prove a parser or denotation theorem for that debug syntax. It checks structural fields and compares every rendered field to the fresh trusted observation.

The compiler's [instance_mir](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_middle/src/ty/mod.rs#L1712) selects CTFE MIR for constant items, optimized MIR for functions, and actual generated MIR shims for Drop glue. Function observations are `Runtime(Optimized)` under explicit MIR opt-level 0; constant bodies include `Runtime(PostCleanup)`. Mandatory lowering/drop elaboration has occurred. This is not a claim to pre-optimization MIR merely because the option is zero.

Concrete call/constant instances use [try_resolve](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_middle/src/ty/instance.rs#L499), fully monomorphic typing environments, and [MIR substitution/normalization](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_middle/src/ty/instance.rs#L892). Drop uses [resolve_drop_in_place](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_middle/src/ty/instance.rs#L720). Region erasure in these APIs is explicit; the capture does not reestablish source lifetime/alias permissions.

The baseline has 24 expanded local definitions, 10 uninstantiated local body templates, 10 selected concrete/constant/glue bodies and 10 dependency edges. Its graph includes:

```text
root → generated, selected, generic<u8>, closure body, DropGlue<Guard>
generic<u8> → <u8 as Step>::step → <u8 as Step>::SHIFT → BIAS
DropGlue<Guard> → <Guard as Drop>::drop
```

Closure construction is separately linked to its body, in addition to the actual closure call. `SHIFT`'s CTFE dependency on BIAS and the evaluated value 3 are retained. The Drop glue body contains the call to the real local destructor. Imported crate metadata hashes and the selected core archive bind the observed external interface; compiler/runtime/imported semantics remain trusted.

### F3. Configured owners and the requested root closure are distinct

Basis: execution + compiler source.

All local definitions are collected after the selected queries, using [iter_local_def_id](https://github.com/rust-lang/rust/blob/f53b654a8882fd5fc036c4ca7a4ff41ce32497a6/compiler/rustc_middle/src/ty/context.rs#L1384). This includes the macro declaration and generated function, trait/implementation and associated constant, constructor/field/parameter definitions, closure owner and late-created lifetime parameter. The two cfg source alternatives yield one configured `selected` function. The generated function retains both macro definition-site and call-site information.

The uncalled decoy is present in the configured census and body templates even though absent from the root's selected instance graph. A candidate deleting that uncalled owner/template passes the relevant local shape checks but fails comparison to the independent complete observation. Omitting the macro-expanded generated-function owner rejects too; this control does not separately delete the macro declaration. A two-file module subject is accepted with both source files; a candidate omitting its module source rejects.

These are actual compiler-observed local owners and generated Drop/closure bodies for the admitted examples. They do not establish a proved, general configured-owner census for Cargo, build scripts, procedural macros, external crates or arbitrary coroutine/drop elaboration. Local DefIds/debug paths apply to the pinned configured compilation; they are not cross-version stable identities.

### F4. Changed subjects can be accepted only against their own selections

Basis: actual compiler captures + consumer execution + native observations.

| Caller-selected case | Definitions / templates / instances / edges | Native results on all byte inputs |
|---|---:|---|
| Baseline root | 24 / 10 / 10 / 10 | 4 |
| Cfg flip | 24 / 10 / 10 / 10 | 7 |
| Changed selected body | 24 / 10 / 10 / 10 | 1 |
| Generic call selecting the u16 implementation | 27 / 12 / 9 / 9 | 3 |
| Decoy as the requested root | 24 / 10 / 1 / 0 | `x ^ 9` |
| Two-file module | 7 / 3 / 3 / 2 | Native execution not requested for this case |

Every listed selection has an actual producer capture and successful independent consumer comparison. The baseline producer and consumer packets are byte-identical, SHA256 `83482423f40d6a6130d5190ae502a4c0913fe6fadd943f0a49f8f32702d9e6bc`; the physical source snapshots differ while the requested compiler namespace stays fixed. Five native subjects account for 1,280 calls, all returning the expected values. This corroborates discriminating source variants without proving general capture correctness or hardware/compiler soundness.

Actual alternate cfg/body/instance/root captures rebound to the old caller request reject. A same-label candidate changes only a captured generated function's operator from BitXor to BitOr: source bytes, selected item and request hashes remain unchanged, yet the consumer rejects after a fresh observation. Thus acceptance is not an ordinary name/hash roster comparison.

A second candidate rewrites the Drop terminator to its successor and removes the glue/destructor instances and associated edges, leaving a coherent reduced graph. It also rejects after fresh observation. This tests fidelity to the selected compiler representation. The destructor's store to its dead local Guard field is not observable in the retained return values; rejection is not evidence that every such erasure is unsafe or an invalid optimization. An equivalence-based pass would need a different checked contract.

### F5. Unsupported domains and process failure stay separate

Basis: actual execution + finite admission source.

The final matrix has 34 calls: 5 capture results, 6 accepted checks, 23 rejected cases. Sixteen rejections are candidate substitutions/omissions/reader controls. Five valid Rust subjects reach normal analysis and the observer then returns explicit unsupported status 65: an external `u8::wrapping_add` body; a floating-point owner; dynamic-trait type; coroutine/async type; and a generic requested root. Two request preflights reject edition 2024 and a wrong driver artifact without invoking the compiler. The wrapper records those as rejection, distinct from an operational compiler failure.

The matrix invokes the compiler 27 times: 22 exits zero and five unsupported exits 65. Actual statuses, complete stdout/stderr, snapshots, candidate bytes and independent captures are retained. No expected rejection is manufactured by running invalid Rust. No unexpected compiler/observer/native panic or assertion occurred. Two earlier observer-development builds rejected an incorrect FileName API spelling before final execution; their diagnostics are preserved separately and are not counted as source controls.

The 34 process-inclusive controller calls took 8.117 seconds in this serial warm-host sample. Recorded observer processes totaled 1.421 seconds, median 0.0468 seconds. These include tiny fixtures and process startup; wrapper costs also include file hashing/copying. They are not scaling, production frequency or comparative verifier measurements.

### F6. Observer loader placement and independent replay

The [independent review](support/independent-review.md) and [bounded result record](support/independent-review.json) bind the actual replay identities, results, operational diagnoses and trusted frontier.

The exact observer has a loader-placement premise: its LC_RPATH is `@loader_path/../toolchains/rustup/toolchains/nightly-2026-05-01-aarch64-apple-darwin/lib/rustlib/aarch64-apple-darwin/lib`. At its original location that resolves the actual driver to SHA256 `dcaea7cc1884046940eb55fcb783e6a86272cf4743600925431022332fa9d69d`, byte-identical to the separately selected `lib/librustc_driver-16d1e96e5b674978.dylib`. Hashing the observer and that selected file does not prove arbitrary relocated loader dependency closure; system/runtime libraries remain trusted.

The independent review first copied the unchanged observer into unrelated scratch and stopped on dyld exit −6 before analysis, because the relative library location was absent. That setup failure produced no semantic capture. An independent fixed-input harness then selected the unchanged observer at its original read-only location and reproduced all 34 expected outcomes: five captures, six accepted pairs and 23 rejections; 27 observer/compiler processes exited 22×0 and 5×65. Observer, selected driver/core and actual resolved driver identities were checked before and after every call. Separate replays of the five existing original native binaries reproduced all 1,280 values after source/wrapper/library/image checks; no new native compilation is claimed.

The historical `support/run_controls.py` and all archived implementation hashes are preserved unchanged. [The distinct explicit-observer helper](support/run_controls_explicit_observer.py) removes that helper's implicit `ROOT/observer` selector; [its source diff](support/replay-helper.diff) retains the fixed source/control grammar and records its own implementation identity. This new helper is source-reviewed and its CLI is checked, but its complete matrix has not been executed. The completed independent replay used a different fixed-input harness; its result is not attributed to the added helper. [REPLAY.md](support/REPLAY.md) states the loader prerequisites and distinguishes both helper identities.

## Boundaries

- **Trusted frontier:** the caller request, rustc parser/analysis/expansion/trait resolution/CTFE/MIR/shim queries, compiler metadata/runtime and this observer/reader. There is no kernel theorem linking these captures to Rust source semantics, first-bad-prefix safety or arbitrary clients. E10 remains open.
- **Finite support:** scalar integer/Boolean/character/unit and selected reference/local-struct/closure types; the explicit MIR tag subset in the code; scalar constants; direct resolved local instances and the represented generated glue. Bounds are four source files, 64 selected instances, 128 blocks/locals per body, bounded projection/type depth and bounded input JSON. Some represented constructors/shim paths are not exercised by these specimens; no broader result is inferred.
- **Unsupported or unexamined:** general target/edition/feature combinations, arbitrary generic roots, non-scalar/promoted allocation graphs, external executable bodies, indirect/virtual calls, foreign/assembly owners, coroutine/async bodies, rich arithmetic/assertion operations, static/TLS lifecycle, procedural macros/Cargo/build scripts and new imported-library interpretations. File/environment dependency guards exist; these are not a proved hostile-source admission filter. Only caller-owned valid fixture code was executed through the compiler.
- **Representation qualification:** debug-rendered HIR/types/enums and exact compiler queries are pinned interfaces. This is a checked equality against a trusted fresh observation, not a proved serializer/parser or semantic Rust-to-model translator. The graph is a conservative capture of represented references; it is not a minimal-runtime-reachability proof.
- **Protocol qualification:** fresh outputs and retained failures support this cooperative local experiment. No adversarial same-user isolation, concurrent publication, cancellation/crash recovery or authenticated producer-stage provenance is supplied. The consumer independently performs its compiler observation; a producer's status label does not establish that observation.

For the earlier research questions, this supplies actual source/configuration/instance capture and binding evidence relevant to P127, but does not certify a pre-optimization Rust fragment end to end: the selected function query is post-lowering and no source-semantics theorem is proved. It does not perform P131's actual memory-operation-to-bytes/initialization correspondence; the local Guard/destructor observation is not that theorem. Those stronger questions are not closed by this package.

## Evidence

All evidence was acquired 2026-10-14. [source-index.json](source-index.json) records exact pinned compiler files, symbols, coordinates and local source hashes. No compiler source mirror or tool cache is included.

[support/capture_observer.rs](support/capture_observer.rs), [capture.py](support/capture.py) and [packet_schema.py](support/packet_schema.py) are the exact final implementation; their hashes are bound in every final matrix row. The observer source SHA256 is `59a998fb395374b810e3e0a04884e0a5c6382ea06b951fda6f8aec5cf3b87f35`. [The baseline caller request](support/requests/base/request.json), [source](support/requests/base/probe.rs), [candidate](support/baseline-candidate.json), [final build record](support/observer-build.json) and [summary](evidence-summary.json) identify actual input/output subjects. The existing native observer is retained privately by the parent for hash-checked replay, not copied as a report binary.

[support/observations.tar.gz](support/observations.tar.gz) preserves 409 regular files: baseline production/consumer results; all final matrix requests, candidates, source snapshots, actual compiler/controller outputs and statuses; and native source wrappers, full 256-element outputs, compile/run receipts and identities. Native executables/rlibs and caches are omitted, with their hashes in the retained native results. The archive is 851,867 bytes, SHA256 `cdc469adfcbc809df3b7ce761cfd48227c318dee655bdfc651a13b782acb5fcf`; it is evidence, not instructions to run copied content.

[projection-receipts.json](projection-receipts.json) binds original/public bytes and replacement counts. Exact task-private compiler/scratch display prefixes are replaced in command/diagnostic metadata **and imported-core provenance strings inside semantic display packets**. The baseline has eight changed `origin.span`/`origin.call_site` fields; [projection-audit.json](projection-audit.json) records exact changed field paths. Source files, requests, MIR operations, statuses and native values are unchanged. The accepted raw baseline SHA256 is `83482423f40d6a6130d5190ae502a4c0913fe6fadd943f0a49f8f32702d9e6bc`; the public display copy is `6e4f164071da6e5c1019256fab8d17fa682e1e63408370387337a3495f0740f1`. They are different artifacts. The consumer compares every provenance field and does not accept the projected copy as those raw bytes. Original captured stream hash fields remain hashes of original streams. The compiler's `/owned-source` remap is separate: it is an explicit selected compilation option.

## Revalidation

Run `python3 -B support/check_evidence.py` for a static package/archive/schema/status audit; this is not a fresh compiler observation. For actual replay, provide the exact identified observer binary and toolchain explicitly:

```sh
python3 -B support/capture.py check \
  --request support/requests/base/request.json \
  --candidate "$RESTORED_OR_FRESH_ACTUAL_CANDIDATE" \
  --toolchain "$PINNED_TOOLCHAIN" --observer "$EXACT_OBSERVER" \
  --output "$FRESH_OUTPUT"
```

First restore the declared prefix with `support/restore_baseline.py` or produce a fresh actual local packet, as described in [support/REPLAY.md](support/REPLAY.md). The restoration helper verifies the exact historical prefix and raw packet hash; it does not run a compiler or establish acceptance. The consumer requires physical fresh output paths and verifies request/tool/source identities. No private tool-location fallback is embedded. A fresh observer build uses the preserved source, installed pinned rustc-dev libraries, `--sysroot`, edition 2021, opt-level/debuginfo zero and `-C rpath`; changing its binary hash requires a newly reviewed caller trust profile and new packet identity, rather than weakening an old check.

For the full matrix, unpack evidence into a new owned space, retain the baseline request/candidate, and use the distinct source-reviewed serial helper with an explicit toolchain and reviewed original observer path, as described in REPLAY.md. Replay native cases only on the selected compatible target; retain changed compiler/hardware identities and all values. A changed compiler/private API, projection schema, source/configuration, generic/trait target or generated owner requires comparing actual bodies and dependencies, not carrying forward the old roster or acceptance result. Parent owns integration, publication and cleanup.
