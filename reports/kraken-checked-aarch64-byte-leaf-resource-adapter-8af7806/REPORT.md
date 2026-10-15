# Checked AArch64 byte leaf, access production and resource frame

*Authored by an AI agent acting on joshlf's behalf.*

## Summary

A byte-driven Lean certificate now connects the actual eight-byte `ldrb w0,[x0]; ret` leaf to Kraken's instruction steps, full modeled effect tree, exact access trace, return state and separated byte resource. The final proof covers arbitrary modeled registers, flags, memory frames, byte values and 64-bit data addresses. Compiled object and linked executable slices at optimization levels 0 and 3 match the certified bytes. Each native build passed 16,640 valid-reference calls.

This advances the admitted scalar portions of E28 and E30. It supplies a machine-side endpoint for E35. The Arm reference relation, verified file importer/loader and actual Rust/MiniRust resource correspondence remain open; E29 and E35 are not discharged.

## Applicability

The model is [Kraken 8af78062037bc237b341d20252aafd1797c1bcb7](https://github.com/AeneasVerif/kraken/tree/8af78062037bc237b341d20252aafd1797c1bcb7). Proofs used the existing dependency-free library built with Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`. Kraken requests `nightly-2026-09-21`; that nightly was not replayed here. The native target is `aarch64-apple-darwin`, rustc 1.99.0 commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, LLVM 23.1.1, with `panic=abort` and `strip=debuginfo`. The harness uses whole-function `naked_asm!` and a separate safe `&u8` wrapper.

The admitted machine encoding is A64 little-endian, fixed four-byte instructions. The decoder recognizes unsigned-immediate LDRB with base X0 and destination W0 for all 4,096 immediate values, and exact RET X30. The certified resource contract admits only immediate zero and exactly two instructions. The code address must be four-byte aligned, nonnegative as an Int64 and leave both instruction endpoints below the signed-address maximum. Data addresses retain all 64 bits. The one-byte span may end at `2^64`; no modular wrap is used to justify an access.

## Findings

### Byte decoding and layout are checked within an explicit fragment

[Adapter.lean](support/Adapter.lean) implements a little-endian word reader, a field-based instruction decoder, a leaf decoder and a layout/contract checker. `decode_load_iff` proves recognition equivalent to the independently stated immediate-field encoding equation for every natural-number word and offset. `decode_ret_iff` proves exact return recognition. `encodeLE_wordLE` proves byte reconstruction for every four-byte input. `accepted_iff_canonical` then proves that the zero-offset leaf contract accepts exactly `00004039c0035fd6`, for arbitrary input lists, rather than assuming a supplied AST equals the desired program.

`certificate_iff` ties accepted bytes to the generated Kraken executable and checked layout. The adapter supplies the four-byte sizes itself. There is no assembly-text parser, producer-supplied AST, source directive erasure or external instruction-size premise in this certificate. General assembly parsing, preprocessing, symbols, labels and relocations remain outside this admitted domain.

The encoding transcription was reviewed against the unsigned-offset LDRB diagram and RET entry in the [Arm A64 reference, March 2025](https://documentation-service.arm.com/static/67e40f3398aa3c3b6eea6a85), pages 518–519 and 751. That review is the connection to Arm's specification. The Lean theorem does not import or prove equivalence to formal Arm ASL/Sail definitions.

### Actual Kraken execution produces the complete scalar trace

`actual_effects` unfolds the actual Kraken semantics and proves equality to the entire effect tree:

```
execute [pc,pc+4)
read    [X0,X0+1)
execute [pc+4,pc+8)
return  X30, with X0 = zero-extended loaded byte
```

It is an effect-tree equality, not a final-state-only specification. `complete_trace` interprets that tree and proves the complete ordered list. `permission_iff` proves that the stricter interpreter requires exactly the two execution permissions, one readable byte and the chosen postcondition. It requires no write permission. Unsupported, nonmemory and unaligned-SP effects are rejected; its treatment of undefined choices is universal. The selected tree contains no such branch. `zero_writes` establishes the absence of a write request from the resulting trace.

`actual_load_step` and `actual_ret_step` also prove the two actual `Executable.step` trees individually. `layout_endpoints` relates their Int64 arithmetic to mathematical `pc+4` and `pc+8`, under the checked layout bounds. Thus instruction boundaries and return termination are exercised independently of straight-line interpretation. Kraken's default `Effects.All` still ignores access authority; this report's resource theorem uses the stricter interpreter.

### A real separated byte resource discharges the load

`resource_load` uses Kraken's actual `Mem.loadInt_sep`, with an arbitrary disjoint frame predicate `R`, to derive the load from `Eq(v.At base) ⋆ R`. `byte_value` handles all UInt8 values, including values with the high bit set: `Mem.loadInt` reconstructs an unsigned integer. `checked_resource_contract` combines the byte certificate, X0 argument-address equality, separated resource, execution permissions and the actual semantics.

Its postcondition specifies the entire modeled MachineData. Only X0 changes. X1–X30, SP, NZCV and the complete data-memory map are preserved; the result in X0 is the zero-extended original byte. The same separated byte and arbitrary frame survive. The per-instruction state equations identify the intermediate state and final state, and `result_preserves_resource` retains the resource in that intermediate/result state. There are no pointer returns, callbacks, stack accesses or unwind exits in this admitted path.

The resource is a concrete Kraken map-cell separation witness. It is not a MiniRust allocation, provenance or borrow predicate, and it is not a fractional shared-reference interpretation. The missing source arrow is a theorem deriving this machine witness and permissions from the actual live, initialized Rust/MiniRust allocation and borrow state, placing its address in X0, and returning the source-language value and valid continuation resources. No actual MiniRust transition definition is imported here.

### Compiled bytes and negative controls

[binding.json](logs/binding.json) records four actual slices: object and linked Mach-O for each optimization level. The bounded owned importer checks the arm64 thin Mach-O header, selected text symbol, section/file bounds, alignment and absence of relocations overlapping the eight-byte slice. It records the next symbol but makes no assertion that symbol extent equals eight bytes. For this selected path, the checked RET terminates execution before any trailing padding or next function.

[BindingCertificates.lean](support/BindingCertificates.lean) contains the four concrete imported byte lists and machine-checked acceptance results at their recorded addresses. This does not verify the Python importer, connect a file hash to a theorem inside Lean, or attest the OS loader/ASLR mapping. The report binds each observed file by SHA256 and preserves it for inspection.

Negative evidence includes:

- A universal theorem rejecting every byte list different from the accepted leaf, plus an arbitrary-wrong-length theorem.
- Eight checked named mutants: wider load, different base register, clobbered destination, offset one, different return register, inserted hidden load, inserted clobber and truncation.
- All 2,040 single-byte substitutions rejected by the independent executable data checker; one mutation in each actual file is reimported and separately rejected by Lean.
- Twelve truncated-file importer controls, an unaligned PC and a wrapping code layout rejected.
- Actual modeled zero-byte readable-span, wrong-return and wrong-X19-frame specifications refuted under explicit non-equality premises.

Mutants are data or proof subjects only. The native program executes the validated original leaf through references into live initialized arrays. For every byte value and each of 65 offsets, it compares the leaf result with an ordinary Rust dereference and checks the test buffer. Both builds return checksum `9369878136d25c80` for 16,640 cases. This finite native agreement does not prove compiler, caller or model adequacy.

## Boundaries

The complete access statement is about Kraken's actual `Effects` for this leaf. Arm's selected RET specification also performs a guarded-control-stack record access and pointer update when GCS is enabled, and updates branch-type state. Kraken's RET models neither. Consequently a hardware interpretation requires an explicit configuration excluding that extra GCS behavior, together with an appropriate normal-memory/address-translation/tag/fault relation. That relation has not been proved. This concrete omitted behavior prevents extending the no-additional-access claim to arbitrary Arm configurations. The state also omits FP/SIMD and system registers, so full modeled-state framing must not be described as a complete architectural-state theorem.

The selected [Rust naked-assembly rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/inline-assembly.md#rules-for-naked-inline-assembly) require ABI preservation, proper termination and FFI-valid memory access. [AAPCS64](https://github.com/ARM-software/abi-aa/blob/ec3e2fb69065768aa1caf298813a7808b50bc264/aapcs64/aapcs64.rst) supplies the reviewed X0 input/result, X30 return and callee-saved register roles. [Apple's platform rules](https://developer.apple.com/documentation/xcode/writing-arm64-code-for-apple-platforms) add platform-specific constraints. The modeled leaf preserves X18, X19–X29 and SP, and does not create a stack frame. The actual compiler-generated wrapper and linked caller remain outside the proof. No generic ABI classification, exception/unwind, speculative access, race, device, vector or physical side-channel theorem is claimed.

E28 remains open for general source/parser/preprocessor/printer and loader relations; E30 remains open for broader instruction coverage, vector widths and Rust/page authority; E35 remains open for actual MiniRust resources and continuation adequacy. E29 is unperformed, with the GCS counterconfiguration now concrete. The [separate requested-nightly replay](../kraken-requested-nightly-adapter-and-selected-closure-replay-8af7806/REPORT.md) checks the unchanged selected proof sources on the requested toolchain. Cross-foundation replays remain unperformed by this package; [prerequisites.md](prerequisites.md) gives the exact inspected prerequisites. The pinned s2n CI supplies a HOL Light revision and its OCaml/Camlp5 combination; that source clarification does not constitute a proof replay.

## Evidence

[replay-results.json](logs/replay-results.json) and [replay-commands.json](logs/replay-commands.json) record the successful owned replay: 40 audited declarations, six Rust compilation commands, two native executions and four bound slices. Every audited declaration's axiom closure is a subset of `propext`, `Classical.choice` and `Quot.sound`; no successful declaration depends on `sorryAx` or a native-evaluation axiom. See [adapter-proof.log](logs/adapter-proof.log) and [binding-proof.log](logs/binding-proof.log).

[source-evidence.json](source-evidence.json) records exact inspected primary paths, revisions and hashes. [development-status.json](development-status.json) distinguishes preserved failed elaboration/harness attempts from successful proofs. The replay harness initially resolved the rustc proxy symlink to rustup, which rejected compiler arguments; preserving the invocation name corrected that harness error. No unexpected panic, assertion failure or semantic/native disagreement occurred. No dependency installation or upstream build was performed.

## Revalidation

From the package directory, with existing compatible tools and the exact Kraken library:

```sh
python3 support/replay.py --lean /path/to/lean --rustc /path/to/rustc --kraken-lib /path/to/kraken/.lake/build/lib/lean
```

The helper rechecks the adapter, compiles only the owned harness, binds object/linked bytes, checks the generated Lean certificates and then executes the known leaf on valid inputs. It stops the affected path on a failed command, panic/assertion diagnostic, unexpected proof axiom or disagreement. Fresh binary file hashes may change with linker metadata; the leaf bytes, address bounds, relocation check, proof closures and native results must still satisfy the recorded checks. A different upstream source, toolchain, architecture, instruction or resource contract requires a new proof/review boundary.
