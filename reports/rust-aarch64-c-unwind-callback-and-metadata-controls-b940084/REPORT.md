# Native Rust C-unwind through an AArch64 assembly callback frame

## Summary

One actual macOS Arm64 process completed four valid cases: normal return and an exact typed Rust panic through a whole assembly C-unwind bounce, compared with the same cases through a pure Rust bounce. Both normal cases returned `0x336699cd00336699`. Every case called its callback once and dropped the callback and outer guards once, in that order. Both expected panics were caught outside the bounce; no unknown panic was accepted.

Actual object and final Mach-O bytes bind the 32-byte assembly function to its active linked DWARF FDE. A live platform unwind walk recorded the expected callback return PC inside that frame, and loaded-image offsets matched the static image. Three metadata-only negatives preserve the code and distinguish incorrect recovery using a bounded data interpreter. **No malformed frame or metadata mutant was executed.** This is bounded E40 experiment evidence; E41's universal recovery/personality/resource proof remains unestablished.

*Authored by an AI agent acting on joshlf's behalf.*

## Applicability

The compiler is actual Rust 1.99.0, commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, LLVM 23.1.1, `aarch64-apple-darwin`. The command uses edition 2024, Opt1, panic=unwind, debuginfo=0, one codegen unit, force-frame-pointers=yes and force-unwind-tables=yes. The inspecting Xcode tools separately report Apple LLVM 21.0.0. The native subject is standard Mach-O arm64, **not arm64e**. The recorded host context is macOS 27 Arm64; selected SDK headers are MacOSX27.0.sdk. This does not generalize to Windows unwind information, other architectures, pointer-authenticated frames, other compiler options or another unwind runtime.

[specimen.rs](support/specimen.rs) includes [bounce.s](support/bounce.s) with `global_asm!`. The external declaration and callback pointer both have ABI `extern "C-unwind"`. No ordinary function-scope `asm!` block calls the unwinding callback. The assembly accepts callback pointer in X0 and u64 argument in X1, calls once, and returns callback result plus one modulo 2^64. The callback is one of two known Rust functions. This is not an arbitrary-callback experiment.

The exact specimen sources, compiled object/final code and unwind metadata were reviewed, and the compiler identity was verified, before the one native run. The unchanged raw native image SHA-256 is `39fe9089fd8449dbe783bc1549daa67fc60d221982be1ecdf345c1b4a721cedf`, verified before and after execution. Public full-image specimens are **non-executable projected data copies**, with different declared whole-file hashes; none was executed. The identity distinction is explained under Evidence.

## Findings

### The whole-function interface permits the selected Rust panic

Basis: pinned normative Rust interface rules + platform documentation/header source + actual compilation and execution.

At Rust Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`, `items.fn.extern.unwind` distinguishes unwinding ABIs and panic strategies. With panic=unwind, the chosen C-unwind boundaries permit this Rust panic. `asm.scope.global_asm` places the assembly outside a Rust function, allowing an entire external function definition. In contrast, `asm.rules.unwind` prohibits unwinding out of ordinary `asm!`, even through a function it calls. The separate naked-block permission is not the interface used here. [Function unwind rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/items/functions.md#unwinding), [assembly rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/inline-assembly.md).

The eight assembly instructions save X29/X30 in a 16-byte aligned frame, set X29=SP, move the callback to caller-saved X16 and the value to X0, BLR, ADD1, restore X29/X30/SP, and RET. X18 and other callee-saved registers are unused. The function uses allocated stack space, not the red zone. Apple's official ABI article specifies X18 reservation, a valid X29 frame record, and 16-byte SP alignment. [Apple ARM64 ABI](https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms). This is the ABI basis for the source inspection, not a formal machine-state preservation theorem.

The assembly owns no Rust cleanup guard, so it has no personality or LSDA of its own. Surrounding Rust frames do. The actual Rust bounce also has a non-tail indirect call, ADD1 and an FP/LR save/restore frame; its callback transfer uses X8 instead of X16.

### Exact code, link metadata and CFI agree

Basis: actual object/image + independent LLVM dump + owned bounded byte/CFI reader.

| Bound fact | Actual value |
| --- | --- |
| Object SHA-256 | `360faff08c03863e69915ae1d5b6119b3986ae7c5be0ffd5052037e70dcd3128` |
| Object function VM / file range | `[0,32)` / `[1288,1320)` |
| Final function VM / file range | `[0x1000008c0,0x1000008e0)` / `[2240,2272)` |
| Actual callback return PC | `0x1000008d4`, start+20 |
| Active final unwind entry | Range `[0x8c0,0x8e0)`, regular second-level page, encoding `0x03000014` |
| Selected FDE | `__eh_frame` offset 0x14, final file offset 260188, length 52 |

The identical object/image code is:

```text
fd7bbfa9 fd030091 f00300aa e00301aa 00023fd6 00040091 fd7bc1a8 c0035fd6
```

Its SHA-256 is `ea698a8dbd4154d20a251e113a12debdbc2ac44fb57a323d87458d8ba1074cf4`. There is no object relocation in those 32 bytes. The explicit exported end label is start+32 in both artifacts. [Object disassembly](evidence/captures/object-bounce-disassembly.stdout), [final disassembly](evidence/captures/image-bounce-disassembly.stdout).

The final active entry chooses DWARF, not a guessed compact-frame encoding. Its CIE is DWARF32 version1, augmentation `zR`, code alignment 1, data alignment −8, return-address column 30 and PC-relative native64 pointer encoding 0x10. The FDE covers the exact function range and has these rows:

| Function PC offset | CFA | Caller FP / LR recovery |
| --- | --- | --- |
| 0 | SP | same / same |
| 4 | SP+16 | `[CFA−16]` / `[CFA−8]` |
| 8 | X29+16 | `[CFA−16]` / `[CFA−8]` |
| 28 | SP | same / same |

Let entry SP=S, FP=F and LR=R. After the prologue, SP=X29=S−16, memory[S−16]=F and memory[S−8]=R, so the body rule recovers CFA=S, FP=F, LR=R. The interpreter checks five supplied snapshots at offsets0,4,8,20,28. These are bounded mathematical witnesses; they are not an ISA or unwinder proof. LLVM's W29/W30/WSP labels are register-number spellings: AADWARF64 assigns the corresponding 64-bit registers in an `.eh_frame` context. [Actual final CFI](evidence/captures/image-eh-frame.stdout), [owned decoded results](evidence/metadata-results.json).

The object FDE initial-location field still has a subtractor/unsigned symbol-relocation pair. Its unrelocated dwarf display consequently prints a placeholder PC near `__eh_frame`; applying the pair resolves the object address to0. The linked FDE resolves to `0x1000008c0`. The SDK header's comment says DWARF mode is never used in object files, while this actual object contains fallback marker `0x03000000`; the linked encoding carries FDE offset 0x14. The observed marker and that descriptive comment are retained separately. Neither placeholder is silently treated as a linked address or a compact frame.

### Normal return and cleanup across the assembly frame actually ran

Basis: one native execution + source oracles + generated cleanup inspection.

The input is `0x1122334455667788`. The normal callback computes u64 wrapping multiplication by 3; both bounces add 1. An independent u128 calculation supplies the expected result. The panic callback uses `panic_any` with the exact owned `ExpectedPanic` type, marker `0x4534305f554e5744` and the same input value. The outer catch accepts only that type and both fields. Other payloads use the original panic hook and are resumed; they are not counted as success.

| Actual case | Observed exit from bounce | Callback calls / callback drops / outer drops | Drop order / expected hooks |
| --- | --- | --- | --- |
| Rust normal | `0x336699cd00336699` | 1 / 1 / 1 | 12 / 0 |
| Rust panic | Exact typed payload caught outside | 1 / 1 / 1 | 12 / 1 |
| Assembly normal | `0x336699cd00336699` | 1 / 1 / 1 | 12 / 0 |
| Assembly panic | Exact typed payload caught outside | 1 / 1 / 1 | 12 / 1 |

Drop-order encoding 12 means callback guard before outer guard. The guards' Drop implementation only updates atomic counters and uses wrapping arithmetic. The process exited zero in approximately0.097s. Stderr contains exactly two explicitly labeled expected-subject-panic lines. Stdout confirms both payloads and all four cases. No retry occurred. [Actual output](evidence/captures/native-positive.stdout), [panic diagnostics](evidence/captures/native-positive.stderr), [before/after image receipt](evidence/captures/native-positive.json).

Generated assembly supplies additional concrete evidence: panic callback lines1324–1392 have personality/LSDA and a callback-drop cleanup followed by `__Unwind_Resume`; normal callback lines1397–1489 have normal and exceptional drop paths. `run_case` lines1814–2589 associates both bounce calls with a landing block updating outer-drop counters before Rust catch cleanup. The object has personality/LSDA relocations, and the final image has the personality symbol and LSDA index. These inspected tables/code support the observed cleanup; they are not a validated general LSDA/personality semantics.

### Live frame walking and loaded-image offsets bind the running subject

Basis: actual platform `_Unwind_Backtrace`/`_Unwind_GetIP` calls and `dladdr` observations, compared with the linked image.

Each callback records a bounded walk through the positive frame before returning or raising the expected panic. The trace callback uses a live fixed-capacity Trace and the runtime's opaque context; it does not allocate or panic. All four walks return status 5, contain nine recorded PCs and are untruncated.

`dladdr` records main-image base `0x104034000`, assembly address `0x1040348c0` and image-relative offset 0x8c0. Both assembly walks contain `0x1040348d4`, the callback return PC at start+20. The Rust bounce offset 0x1f3c also matches its static symbol; its walks contain its own start+20. The platform walk function resolves to `_Unwind_Backtrace` in `/usr/lib/system/libunwind.dylib`.

This binds loaded code offsets to the static function/unwind range and demonstrates an actual platform walk and Rust panic traversing the positive chain. It is bounded registration/operational evidence. No internal lookup-route trace was instrumented: the result does not prove which lookup/fallback implementation was taken, nor the system library's source version or universal correctness. The SDK warns that `_Unwind_Find_FDE` does not cover compact-unwind functions; this experiment does not mistake a null FDE query for missing registration or use that query.

### Metadata-only negatives preserve return code but break selected recovery

Basis: actual linked-image data copies + owned decoding/arithmetic interpretation; **no native execution of negatives**.

| Data-only control | Actual edit | Body recovery discriminator |
| --- | --- | --- |
| wrong CFA | File 260222, offset operand 16→8 | Recovered SP=S−8; LR reads saved FP |
| wrong saved LR | File 260226, offset factor 1→2, i.e.−8→−16 | Recovered LR=F instead ofR |
| missing active FDE | Selected FDE length field at260188→zero | Selected DWARF entry has no admitted FDE; reader rejects |

All three preserve the complete bounce instructions. The owned interpreter separately computes the unchanged normal LDP/RET witness, restoring SP=0x1000, FP=0x3000 and return PC=0x8004. These addresses are mathematical data only. This contrasts ordinary return, which does not consult CFI, with recovery from the body snapshot. The missing-FDE result is the narrow reader/certificate lookup failure, not a prediction about a real unwinder's possible fallback on malformed input. [Data controls and original results](evidence/metadata-results.json).

## Boundaries

- **Bounded E40 result:** one known callback input, two known callback behaviors and one compiler/platform configuration; four actual cases, exact final-code/metadata binding, live frame walks and observed cleanup. No malformed frame, deliberately invalid Rust or metadata mutant was executed.
- **E41 unestablished:** no universal partial-prologue/body/epilogue recovery theorem, verified metadata producer/loader/registration/lookup, actual personality semantics, arbitrary callee/callback composition or restored Rust/MiniRust resource relation. Counters demonstrate selected guard cleanup, not all resource invariants. Neither the parser nor the data interpreter is verified.
- **Not examined:** foreign/C++ exceptions, forced unwind, nonlocal jumps, cancellation, signal/interrupt recovery, stack overflow, dynamic registration, arbitrary callbacks, arm64e/PAuth, Windows unwind or other optimization/target configurations. These are scope limits, not declarations that the platform cannot support them.
- **Runtime trust:** the system library image/symbol was observed, but its exact implementation source/binary hash and internal selected path were not proved. Actual unwind success is operational evidence, not a compiler/hardware/Rust adequacy theorem.
- **Public artifact limit:** projected image data has the original code and unwind sections, but is not the whole byte-identical executed file. No executable or signing/loading claim applies to public data copies.

## Evidence

All new observations date to 2026-10-14. [Current native results and static validation](native-results-and-static-validation.json) distinguish the completed run from [the historical pre-native checkpoint](evidence/historical-pre-native-STAGE-STATUS.json). The latter is an explicitly named historical snapshot; its pending-native state is not the current result. The metadata-reader record likewise describes its earlier data-only stage, not the whole task's eventual native-execution state.

[Projection receipts](projection-receipts.json) retain every raw/public hash and byte count. The positive image's raw execution hash is `39fe9089fd8449dbe783bc1549daa67fc60d221982be1ecdf345c1b4a721cedf`; the public non-executable data hash is `b3132adac0a809fba51315822a82df64383bc43d1d0483621eee80c145404387`. Exactly four N_OSO archive-name prefixes in each image copy were replaced with an equal-length padded portable label. Each replacement's byte range and prefix hash is recorded. Full file lengths, section maps, complete `__text`, `__eh_frame` and `__unwind_info` bytes/offsets are unchanged. The same projection is applied to positive/control copies, so their remaining differences are exactly the declared CFI edits. Text argv/output path normalization is recorded separately. Original captured stream hashes still refer to original streams, with public stream hashes in the projection receipts.

[Tool identities](evidence/tool-identities.json) bind rustc launcher SHA-256 `dd6f58440b3418aa9157ae3f05d71eecff741ca41bc4eec120e7e8f2d933b9a0` and driver SHA-256 `17b7b2520e11aaa79087493fb8ad1140382b959eed3f00c3e8635cc000b63a4d`. [Source identities](evidence/source-identities.json) bind the unchanged Rust/assembly sources, pinned Reference cache and exact selected SDK headers. The full object and generated assembly are byte-identical public copies. Tool binaries, sysroot libraries, caches and duplicate first-attempt artifacts are omitted.

Primary background includes [AADWARF64 2025Q1](https://github.com/ARM-software/abi-aa/blob/2025Q1/aadwarf64/aadwarf64.rst), register numbers/CFA, and [DWARF5](https://dwarfstd.org/doc/DWARF5.pdf), 13 February 2017 §6.4/6.4.2. The Apple article exposes no immutable revision; local SDK headers are separately hash-bound artifacts. They do not identify the runtime library's source version.

Two operational diagnostics are preserved. The first time-wrapper attempt failed on sandbox-denied `kern.clockrate` statistics, so its child compiler status was unknown; the direct unchanged compiler independently exited zero and produced identical artifacts. No peak-RSS result is claimed. The first owned metadata reader stopped on an unhandled regular pagekind 2; after reading the SDK's regular-page definition, it was extended to cover the actual regular first page and compressed second page. No positive source or machine artifact changed to obtain that result. [Wrapper diagnosis](evidence/first-wrapper-attempt.json), [reader diagnosis](evidence/reader-attempt01-diagnosis.json). These were diagnosed tool/data-domain failures, not unexpected native panics. The unnecessary-unsafe compiler warning was retained without source change.

## Revalidation

Run `python3 support/validate.py` in this package. It reads only declared public data: source/projection hashes, both code bindings, active FDE and CFI, five recovery contexts, three non-executable metadata controls, actual captured results and loaded-image offsets. It never compiles, links, loads or executes an image. It explicitly accounts for the raw executed image versus projected public-data identity. Verify the package manifest separately.

For a new operational replay, use fresh authorized scratch, copy `support/specimen.rs` and `support/bounce.s`, require the exact recorded compiler/target/options, then compile object/assembly/image with the preserved argv. Inspect actual code, metadata route/ranges, relocations and Rust cleanup before any positive execution; never assume another compiler emits the same FDE/compact format. [Historical actual command proposal](evidence/historical-commands-proposed.json) and individual capture receipts retain argv. Acquisition scripts are historical evidence, not instructions to execute the public data copies. Future native runs must preserve their own raw image identity, exact typed-panic checks and diagnostics. Unknown panics or metadata inconsistencies stop the path. Keep every negative strictly data-only. A passing replay still leaves E41's universal proof obligations open.
