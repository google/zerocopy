# Matched valid Rust observations on little-endian AArch64 and big-endian s390x

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

The same five valid Rust sources, compiled by Rust 1.89.0 / LLVM 20.1.7, passed
all 78 finite checks on native Linux AArch64 and on an s390x Linux ELF executed
by QEMU user mode. Both executions exited 0 with empty stderr. Native integer
bytes changed exactly with endianness. The selected layouts, defined numeric
results, trait-object calls, readiness decisions, valid wide-union copies and
normal-scope destructor counts agreed. Arithmetic NaN payload observations also
happened to agree; no portable payload rule was required or inferred.

This completes the declared E08 paired target/layout **experiment** for the
preserved cases. It provides observations, not E49's target-parametric numeric/
floating-point proof or importer correspondence.

## Applicability

Both subjects use Rust commit
`29483883eed69d5fb4db01964cdf2af4d86e9cb2`, release 1.89.0, LLVM 20.1.7,
edition 2021, `opt-level=0`, `overflow-checks=yes`, `codegen-units=1`, the same
source bytes and the release standard libraries for their named targets. The
compiler itself runs on `aarch64-unknown-linux-gnu`. The native execution is
Linux-arm64 inside the task's container/virtualized host environment; it is not
an aarch64 macOS execution. The second executable is genuinely ELF64 big-endian
IBM S/390, run with `qemu-s390x -L /usr/s390x-linux-gnu`. No physical s390x
machine was used.

The container was observed running with the assigned exact ID, one CPU,
1,073,741,824 bytes of memory and no mounts (`captures/01-container.*`). All
owned source, temporary compiler files and outputs were placed under a new
container-local directory. This report does not assert that the container
image, host kernel, emulator or complete dependency closure is verified.

Sources and `ORACLE.md` were fixed and hashed before compilation. The preserved
oracle's opening status and `case-plan.json.initial_status` are historical
**preparation** statements; `execution-status.json` and this report record the
subsequent actual runs. This is a fresh Rust 1.89 paired experiment. It is not
identified with an earlier May-nightly, Miri, MiniRust or generated-model subject.

## Findings

### F1. Compiler, target, source and executable binding

Basis: execution + owned source + derived comparison.

`02-rustc-version` binds the full commit, host and LLVM version. Target cfgs
(`03`/`04`) declare aarch64/little/64 and s390x/big/64. Every source was hashed
locally, copied individually, hashed again in the container before compilation,
and rechecked after execution (`preparation-manifest.json`, `21`, `34`). There
were no source edits between the paired builds. Compiler diagnostics were empty
and both compilations exited 0 (`22`/`23`). ELF headers and interpreter records
(`25`/`26`) independently distinguish the executable formats.

| Subject | SHA-256 |
|---|---|
| Rust compiler binary | `93c98482c1bdedf3789c2bd0a86ff82a7075a58528abbca2990066f4e8faedb7` |
| Native AArch64 ELF | `b693e1947614e60776d31994adcb6c67bb9e72fa700c7e49783dccc43287a055` |
| Big-endian s390x ELF | `06d1cb88a0300840e1bef51af0e0552aa090c39012cf4105b8f269e4b78099ab` |
| QEMU s390x binary | `f1796dc51e3dfdbca9ed24ea9b089b24d4827f07d0cdc34e06ae4fccb452fd58` |

Tool hashes include rustc's driver and LLVM libraries, both linker drivers,
linkers and `readelf` (`15`). The two target-library directories are hashed
entry by entry (`16`). ELF dependency names, target interpreters and selected
native/cross runtime-library hashes are retained (`26`, `32`, `33`). These are
concrete identities, not a theorem about the complete build/runtime TCB.

### F2. Defined integer operations distinguish value and native byte order

Basis: execution + `fixture/numeric.rs`.

For `0x0123456789abcdef_u64`, native AArch64 bytes were
`[239,205,171,137,103,69,35,1]`; native s390x bytes were
`[1,35,69,103,137,171,205,239]`. Explicit little/big byte APIs produced their
fixed arrays on both subjects, and native roundtrip preserved the scalar.
The `CRecord.word` scalar independently reversed its native byte sequence.

Both subjects passed the selected unsigned/signed wrapping and checked overflow
cases, checked division overflow/zero, in-range checked shift, rejected
out-of-range checked shift, masked wrapping shift, signed right shift and
narrowing/signedness casts. Plain overflowing arithmetic and ordinary
out-of-range shifts were not executed. The control distinguishes checked
failure from a wrapping result and rejects an endian-independent native-byte
oracle. This samples named finite rules; it does not quantify over integer
values, widths, operations, optimization levels or targets.

### F3. Floating-point bit preservation and permitted NaN choices are separate

Basis: execution + `fixture/numeric.rs`.

Eight f32 and six f64 patterns, including signed zero, tiny subnormal,
infinity and NaN encodings, survived `from_bits`/`to_bits` unchanged. The listed
exact binary addition, representable cross-width conversion, finite integer
truncation, unsigned saturation, NaN-to-zero and infinity-to-bound casts passed.
The subnormal case checks construction/classification, not general arithmetic
underflow or no-flush behavior.

| Observation | AArch64 bits | s390x/QEMU bits | Required oracle |
|---|---|---|---|
| f32 input-payload NaN plus 1 | `7fc01234` | `7fc01234` | NaN class |
| f64 input-payload NaN times 2 | `7ff8000000001234` | `7ff8000000001234` | NaN class |
| f64 input-payload NaN cast to f32 | `7fc00000` | `7fc00000` | NaN class |

The source uses `black_box` to discourage constant folding, but the report does
not claim to establish the emitted FP instruction sequence. It neither demands
arithmetic NaN payload preservation nor treats the coincident result as portable
canonicalization. Signaling/quiet NaN interpretation is not assumed portable.
Controls show that equal zero values can have different bits and NaN equality
is not reflexive. No transcendental operation, rounding-mode study, exhaustive
FP rule or formal IEEE-choice semantics was evaluated.

### F4. Layout and dynamic behavior agree for these instances despite distinct target layouts

Basis: execution + `fixture/layout.rs`.

The `repr(C)` record matches the field-order/alignment-rounding formula computed
from each target's primitive alignments. No padding bytes are read. The selected
array, safe slice view and final-field array-to-slice DST coercion preserve their
values, lengths and measured pointee layout. Safe matching recovers both data
enum payloads. The constructed `repr(u8)` fieldless enum values and the selected
documented Option niche sizes pass; no invalid/niche representation is transmuted.

| Measured type/value | Both observed subjects |
|---|---|
| `CRecord` | size 12, align 4, offsets 0/4/8 |
| `[u16;3]`; slice pointee | size 6, align 2, length 3 |
| slice reference | size 16, align 8 |
| sized/DST `Tail` pointee | size 16, align 4, payload offset 4, length 3 |
| fieldless/data enum | size/align 1/1 and 8/4 |
| `Option<NonZeroU16>`; `Option<&u8>` | size/align 2/2 and 8/8 |
| `Option<bool>` | observed size 1 |
| `&dyn Measure` | observed size 16, align 8 |
| dyn `Pair`; dyn `Byte` pointees | size/align 8/4 and 1/1, dispatch results 1007/18 |

Trait-object method behavior and dynamic pointee size/alignment are observed
through safe APIs. No vtable slots, contents, addresses, drop-entry shape or
stable trait-object ABI is inferred. The compiler may devirtualize calls.
The table reports selected instances, not ABI equality in general.

Separate LLVM-IR **emit-only controls** (`29`–`31`) expose the compiler's distinct
target data-layout strings:

```text
aarch64: e-m:e-p270:32:32-p271:32:32-p272:64:64-i8:8:32-i16:16:32-i64:64-i128:128-n32:64-S128-Fn32
s390x:   E-m:e-i1:8:16-i8:8:16-i64:64-f128:64-v128:64-a:8:16-n32:64
```

Those controls use the same sources/compiler/declared flags, but are separate
compilations; their IR is not claimed to be the captured exact link input of
either executed ELF. Only the narrow header and full IR hashes are retained.

### F5. Readiness ranges are checked metadata, not physical permission evidence

Basis: execution + `fixture/readiness.rs`.

The finite model conjoins initialized/readable/stable masks after checked range
addition and bounds checks. It accepts the ready prefix/suffix and empty range
at the allocation end, and rejects each denied mask, the whole denied range,
empty range outside, past-end span and `usize::MAX+1` overflow. Checked slice
access independently gates the concrete sum; denied metadata never causes an
actual invalid memory read. An empty allocation model accepts only the empty
in-bounds case. Both subjects make all ten decisions and additional checked-sum
controls agree.

All actual arrays are fully initialized. The masks are ordinary data: their
names do not establish Rust permissions, initialization tracking, lifetime/
provenance authority, interference stability or concurrency semantics. The
presence-versus-readiness control explicitly preserves that distinction.

### F6. Valid wide-union copying and normal-source Drop do not require invalid reads

Basis: execution + `fixture/wide_copy_drop.rs`.

Each of two unions is initialized only at a raw slice-pointer field and copied
through a non-inline source identity function. Reading that same field and
forming a shared view preserves the live source slice's pointer identity,
length 3 and values `[22,33,44]` on both subjects. The second union has an
additional `[usize;2]` field, which is **never read**. Both measured union layouts
and the raw slice pointer are size 16/align 8. No representation-size premise
is used to fabricate pointer metadata.

The only unsafe blocks read the initialized field and dereference the exact
live shared pointer while its source allocation/borrow is in scope. They do not
read inactive words or padding. These are ordinary valid Rust observations, not
a MiniRust lowering/run, validation disabling experiment or repair.

A separate safe `Cell` guard checks move-without-drop, explicit drop once,
absence of double drop after the move, and a second guard's normal scope exit.
The final count is exactly 2. This says nothing about unwinding, async cancel,
FFI destructors, allocator operations or dynamic destructor ABI.

### F7. The recorded outcome is agreement, not suppression of operational errors

Basis: captured process statuses + derived comparison.

`27-run-native` and `28-run-big` each contain 78 unique passing check keys,
one `SUMMARY checks=78 failures=0`, exit 0 and empty stderr. The stdout hashes
are respectively `007dbd2dc11f6845c210ba21062048e82dce7851e777b51dc609d9b3e780e507`
and `54d2039c8cf1f1143e76c9afbbf1afc5824928728a2e72712e1a3ed1e91ceeeb`.
Only four lines differ: architecture, endianness and the two predicted native
byte observations (`comparison.json`). No failing portable check, panic or
unexpected runtime status was observed. Each subject was executed once; this
is not a statistical stability or performance experiment.

Two earlier metadata/access events remain preserved: the initial sandbox could
not access the Docker socket (`00`), so no container operation began; after
authorized access, a query incorrectly named a guessed GCC14 package (`09`).
The actual GCC12 package was queried successfully (`12`) before source transfer.
Neither event is a Rust/target negative result. The initial PowerPC cross-linker
availability problem was reported by the parent; this worker selected no
PowerPC subject and makes no PowerPC support classification.

## Boundaries

- **Completed bounded experiment:** E08's relevant integer/FP/DST/niche/
  trait-dispatch/mask observations on the two exact subjects above. QEMU,
  compilation and native-container execution remain distinct evidence roles.
- **Not established:** E49's declared all-target semantic laws, bounded integer
  mechanization, full MiniRust FP extension, IEEE-choice formalization and
  importer correspondence. They require proofs beyond this finite experiment.
- **Not examined:** other Rust versions, optimization/overflow/panic modes,
  additional target ABIs/32-bit hosts, physical s390x, arbitrary vtable/layout
  structures, arbitrary FP operations/inputs, SIMD or concurrent interference.
- **Unknown:** whether broader source/target combinations preserve any sampled
  property; a passing finite observation does not resolve those combinations.
- **No unsupported-language claim:** there was no compiler/runtime refusal for
  the prepared subjects. Environment/package-query failures are kept separate.
- **No interrupted scope:** no MiniRust/Miri/build/lowering/model execution,
  E05 erasure experiment, invalid Rust, padding/uninitialized observation,
  allocator forgery or race was executed. E05/E06/E30 are not closed here.

## Evidence

Owned evidence is self-contained in this package:

- `fixture/*.rs`: five exact executed sources; `preparation-manifest.json`
  binds them and the original oracle before compilation. Its `main.rs` paths
  name the matching files under `fixture/` in this projection.
- `ORACLE.md`, `case-plan.json`: preserved pre-execution choices and finite
  invariants. `execution-status.json`, `comparison.json` and
  `observed-check-keys.json` record actual outcomes, not additional proofs.
- `captures/00`–`34` label the exact invocations, stdout, stderr and statuses;
  copy labels `200`–`204` are source transfers. See F1/F7 for roles.
- `normalization-receipts.json`: raw/current byte hashes for every projected
  capture/input. Only exact private workspace/client/socket prefixes were
  replaced with `@CASES@`, `@DOCKER@`, `@DOCKER_SOCKET@`; program outputs and
  all five source files are byte-identical. Public command tokens describe
  historical argv and are not an executable replay interface.
- `package-manifest.json`: all listed public file bytes; include the manifest
  itself when transporting the package. Tool binaries, standard-library files,
  ELF binaries, complete LLVM IR, caches and source mirrors are not embedded.

The compiler's immutable upstream identity is
[rust-lang/rust at 29483883eed69d5fb4db01964cdf2af4d86e9cb2](https://github.com/rust-lang/rust/tree/29483883eed69d5fb4db01964cdf2af4d86e9cb2).
This report's material findings are owned-source/execution/derived findings,
not a new normative specification or an audited proof of that implementation.

## Revalidation

Run `python3 -B verify_evidence.py --package CHOSEN_PACKAGE` to validate the
frozen projection and finite output comparison without invoking a compiler or
emulator. That checks evidence consistency only, not the truth of the compiler,
runtime, source safety argument or semantic oracle.

For fresh execution, the caller must select/prepare a bounded runtime and output
directory, recover the named compiler/target libraries/linker/emulator, compare
their exact identities, and compile `fixture/main.rs` with the recorded edition,
optimization, overflow and codegen-unit flags. Set the explicit native target;
for s390x use `--target=s390x-unknown-linux-gnu -C linker=s390x-linux-gnu-gcc`.
Run the AArch64 ELF on an appropriate Linux-arm64 host and the s390x ELF with
`qemu-s390x -L CHOSEN_S390X_SYSROOT`. Capture separate process statuses and raw
streams. Compare using `ORACLE.md`, not complete stdout equality or a fixed NaN
payload. The recorded `.json` commands give exact historical arguments but do
not supply personal absolute defaults or authorize a runtime.

On any changed version/flag/target, name a new observation subject. A failure
must retain the source/tool/executable identities and be diagnosed before
retrying; compiler infrastructure, emulator behavior, permitted FP choices,
target ABI differences and a violated portable check have different meanings.
