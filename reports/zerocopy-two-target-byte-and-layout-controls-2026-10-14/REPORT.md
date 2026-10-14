# Zerocopy byte validation and layout on arm64 and wasm32

## Summary

The same safe public zerocopy calls passed on native arm64 and wasm32: all 256 Boolean encodings, all 65,536 Boolean-pair encodings, eighteen width/ZST/endian/alignment/write controls, and two explicit wrapper-domain rejections. The wasm artifact has no imports and was executed through Node's WebAssembly engine. Observed layout depends on the target: usize is eight bytes on arm64 and four on wasm32, changing a C-layout aggregate and its packed variant.

These are real library/compiler/runtime observations with independent expected-result checks. They are not correspondence certificates, a Rust memory-safety theorem, or a benchmark of Anneal proof generation. They expose target binding and workload requirements for evaluating such certificates.

## Applicability

Source is the exact zerocopy Git archive from google/zerocopy cce761ad53785973ec2f4a6b13715b770b340c87. Both builds use Rust 1.99.0 b940084d7eb6a299eb4bfeb8e34901bc051e7ac4, LLVM 23.1.1, Cargo offline, default development optimization and the crate's default features. The native target is aarch64-apple-darwin on Darwin 27 arm64. The second target is wasm32-unknown-unknown, executed with Node 24.21.0/V8 13.6.233.17-node.53. No cross-target native emulator or global target installation was used.

The wasm standard-library component is the official Rust 1.99.0 artifact, SHA-256 b760b0c9b08a6843c05de0098bd6802e23178ff473c4715ae57c1d679125bf22,23152600 bytes. Its files were extracted with Python 3.14's data filter and copied into a temporary target-only sysroot. Its checksum was acquired from the official distribution endpoint before extraction. Host build scripts used the existing host toolchain; target rustflags selected the private wasm sysroot.

R005/P138 receive a concrete two-target library case and separated build/runtime observations. R095/P131 and R097/P130 receive additional byte/layout evidence. Full proof-generation/checking costs, target-specific Rust semantic adequacy and a realistic whole-verifier workload remain outside this experiment.

## Findings

### Invalid encodings remain in both tested input domains

Basis: **execution**, preserved native and wasm controls.

The wrapper calls bool::try_read_from_bytes for each byte 0–255. Success is compared with the independent rule that only 0/1 are valid; the returned Boolean is separately encoded and checked. The pair wrapper calls [bool;2]::try_read_from_bytes for every ordered pair. Exactly four encodings succeed, with each returned value checked. This avoids accepting only a decoder's already-valid values as the experiment's input domain.

Native Rust loops and separately written JavaScript loops compare the same exported API behavior with those predicates. The JavaScript harness compiles the emitted wasm, requires an empty import list and calls its exports. It does not substitute a handwritten model for zerocopy's implementation. Both wrappers explicitly return a distinct status for u32 inputs outside the selected byte domain; two such inputs are challenged on each target.

The result covers these finite domains and actual configured executions. A test of all byte values is not a proof that compiler execution conforms to a formal Rust semantics or that unrelated callers, allocations, races or API operations are safe.

### Eighteen controls retain representation and write boundaries

Basis: **execution**.

Each target checks four width/ZST conditions, two endian reads, successful prefix/suffix writes, a short-write rejection with destination preservation, and eight alignment-sensitive reference constructions. Rejected byte candidates are passed to safe APIs; the owned probe never constructs an invalid Boolean/reference or invokes an unsafe operation. Unsafe no_mangle attributes select export names and are not unsafe operations in the probe body.

The alignment expectation uses the actual safely accessible byte slice's address and align_of::<u16>(); it is not inferred from a numeric offset alone. Write controls compare the unchanged unselected bytes and unchanged destination after rejection. These observations exercise storage effects that a pure return-value comparison could omit.

### The two targets require different layout facts

Basis: **execution**, size_of/align_of/offset_of in the compiled subject.

| Observation | arm64 | wasm32 |
|---|---:|---:|
| usize size |8|4|
| repr(C) {u8,usize} size |16|8|
| repr(C) aggregate alignment |8|4|
| repr(C) word offset |8|4|
| repr(C,packed) aggregate size |9|5|
| Packed alignment |1|1|
| Packed word offset |1|1|

No unaligned reference is created to measure these offsets. A layout certificate specialized to the arm64 word width cannot simply be reused for wasm32. A parameterized certificate may instead retain width/alignment premises and instantiate them with justified target facts. Runtime observations can discriminate an incorrect instantiation, while a compiler-layout theorem is a separate assurance route.

The PR stack's pure layout tests already separate numerical layout from physical fields and access authority. These target observations supply concrete facts to challenge that seam; they do not prove the seam for every Rust representation, DST, enum, target or compiler version.

### Costs are separate observations rather than a backend ranking

Basis: **execution**, one sequential run.

| Phase | Observed elapsed time |
|---|---:|
| Native Cargo build |2.318s|
| Native process plus controls |0.062s|
| Native in-process case loop |0.0075s|
| Wasm Cargo build |1.884s|
| Node process plus wasm controls |0.104s|
| JavaScript loop and calls |0.0251s|

The debug wasm artifact is 2141436 bytes, SHA-256 retained in results.json. It is executable code, not a proof certificate. The native build preceded the wasm build in one private Cargo target, so host/build-script reuse and compilation order differ; process startup, interpreter/JIT behavior and loop implementations also differ. No variance, steady-state throughput, release optimization or superiority claim follows.

For future Anneal evaluation, additionally measure source capture, certificate generation, proof size, checking, dependency replay, rejected-candidate latency and reuse under the same claim/model/configuration. A tiny generated proof checked under a narrowed domain is incomparable with this full finite byte-domain workload.

### Compiler and execution trust remain explicit

Basis: **derived** from the experiment's endpoints.

The checks establish equal observed results under independently stated finite predicates. The Rust compiler, standard library, wasm code generation, Node/V8 and native hardware are not verified by this test. A source-level claim needs source/model correspondence and appropriate runtime or machine-model assumptions. A no-import wasm artifact narrows its external invocation interface but does not establish semantics preservation or absence of all environmental assumptions.

A useful certificate pilot can fix the common Rust API/domain and then separate target-independent validity rules from target-specific layout/representation facts. It should reject changed target facts, changed domains and a producer-generated expected predicate that is weakened with the implementation. Mathematical proof reuse and artifact reuse must remain independently applicable.

## Boundaries

This is a small real-library case, not a large zerocopy verification workload. There is no source-safety reflection proof, compiler verification, generated correspondence theorem, full ABI calling-convention audit or measured Anneal certificate cost. Allocation, provenance, concurrency, FFI, destructor obligations, enum/DST representations and every other target remain unexamined in this package.

The host rejected an attempted x86_64 execution probe with Bad CPU type and exit 1; no emulator was installed. That operational result does not imply x86_64 compilation or zerocopy support is absent. Wasm32 was selected as the second executable target, with its own recorded compiler/runtime boundary.

## Evidence

- **source/execution:** support/lib.rs, main.rs, check-wasm.mjs and run_cross.py; exact hashes, command statuses and archive identity in support/results.json.
- **execution:** complete stdout/stderr for Rust/Node version, native build/check and wasm build/check; both independent expected-result loops passed. The debug artifact hash/size is recorded without publishing generated binaries.
- **documentation/artifact identity:** [official wasm component checksum](https://static.rust-lang.org/dist/rust-std-1.99.0-wasm32-unknown-unknown.tar.xz.sha256) and [component artifact](https://static.rust-lang.org/dist/rust-std-1.99.0-wasm32-unknown-unknown.tar.xz), acquired2026-10-14; checksum/size retained above.
- **source:** exact [zerocopy implementation](https://github.com/google/zerocopy/tree/cce761ad53785973ec2f4a6b13715b770b340c87/zerocopy).
- **derived:** proposed common comparison protocol, applicability split and trust-accounting implications. These are not additional execution results.

## Revalidation

Acquire and verify the exact target component, then run `python3 support/run_cross.py /path/to/zerocopy-repo /path/to/rust-std-wasm32-component` in a disposable package copy. The second path is the component directory containing lib/rustlib/wasm32-unknown-unknown. Require all six command statuses, expected native/wasm outputs and empty wasm imports; retain failures rather than treating them as unsupported program behavior.

For another target/compiler, independently obtain its standard library/runtime and record the changed subject. Compare finite API results separately from layout. Extend the workload and produce actual correspondence/checking artifacts before using these timings as Anneal proof-cost evidence.

*Authored by an AI agent acting on joshlf's behalf.*
