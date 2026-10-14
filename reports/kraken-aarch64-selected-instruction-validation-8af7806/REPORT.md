# Selected AArch64 instructions: reference review and native differential validation

## Summary

Actual Kraken execution, an independently written mathematical oracle, and native AArch64 assembly agree on all 1,290 selected register-only cases, including final NZCV. The native program was compiled and run at optimization levels 0 and 3. The seven instruction/width forms exercise addition carry and signed overflow, W-register zero-extension, variable-shift count masking, and byte reversal. Eight deliberately wrong semantic alternatives produce concrete distinguishing cases.

This is an executed finite validation result, with primary Arm instruction descriptions reviewed for the selected rules. It is not a universal equivalence theorem, execution of an independent formal ISA model, or proof that Kraken's AST denotes the native bytes. It closes the bounded AS04 instruction-validation investigation left by the companion closure and arithmetic-pilot reports while keeping those stronger outcomes separate.

## Applicability

The model is `AeneasVerif/kraken@8af78062037bc237b341d20252aafd1797c1bcb7`. The evaluator imports its actual AArch64 parser and semantics and uses the read-only library built from that source. Installed Lean 4.34.1, commit `5045d0056413266e57c625dcd7c365b10e377c52`, executes it. Kraken requests `nightly-2026-09-21`; this observation uses a different explicitly identified toolchain.

Native observations use Rust 1.99.0, commit `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, LLVM 23.1.1, on the observed `aarch64-apple-darwin` host running macOS 27.0.1. The instructions are base A64 integer/register operations. The harness does not dereference assembly pointers, execute privileged operations, access invalid Rust values, or depend on an external function ABI. `MRS NZCV` reads condition flags. The surrounding Rust process necessarily uses ordinary runtime memory; the tested inline blocks contain only register/flag instructions.

The reviewed Arm references have exact static URLs and version footers, but no whole-document content hash. Selected indexed primary entries were inspected for the large references; the full 15.3 MB March reference was rejected by the web tool's size limit and was not downloaded. The short Arm architecture guide was read through its extracted text. These limits are recorded in `support/primary-document-observations.json`. The environment denied a CPU model metadata query; no exact physical core model is claimed.

## Findings

### A concrete instruction corpus has three independent observations

`support/InstructionEval.lean` elaborates each source instruction through Kraken's real `parseAArch64` macro. `support/parsed-programs.log` records the resulting constructors and widths, including `ADDS_s` with LSL zero, `ADCS`, `ADD_s` W32, `LSLV` W32/W64, and `REV` W32/W64. Each program contains exactly one instruction, assigned address zero and declared size four. This supplied layout is consistent with the selected A64 instruction width; it is not a checked decoder witness.

| Instruction/width | Cases | Main discriminating boundary |
|---|---:|---|
| `adds x0,x1,x2` | 225 | Wrapping result, carry, signed overflow, N/Z |
| `adcs x0,x1,x2` | 450 | Both input-carry values and all resulting NZCV |
| `add w0,w1,w2` | 225 | Low-32-bit result and upper-half clearing |
| `lslv x0,x1,x2` | 180 | Count modulo 64 |
| `lslv w0,w1,w2` | 180 | Count modulo 32 and zero-extension |
| `rev x0,x1` | 15 | Eight-byte reversal |
| `rev w0,w1` | 15 | Four-byte reversal and zero-extension |

The arithmetic corpus uses every pair from 15 explicit edge words: zero, small values, byte/word/sign boundaries, both unsigned extremes, and two asymmetric byte patterns. ADCS repeats each pair with carry zero and one. Shift cases combine those words with counts `0,1,7,31,32,33,63,64,65,127,128,2^64−1`. REV uses the same 15 words. All exact inputs are preserved in `support/cases.tsv`; there is no random seed or undisclosed sampling.

The mathematical oracle in `support/validate.py` uses arbitrary-precision unsigned totals and signed range tests for flags, modular arithmetic for 32-bit addition and shifts, and byte-array conversion for reversal. It does not call Kraken, reuse Kraken's mask-and-swap implementation, or execute Arm pseudocode. N is the result sign bit, Z tests zero, C tests unsigned range overflow, and V tests the signed mathematical sum's range. NZCV is recorded as a four-bit integer with N at bit 3 and V at bit 0.

The native `support/native.rs` uses actual `ADDS`, `ADCS`, `ADD W`, `LSLV`, and `REV` inline assembly, followed by `MRS NZCV`. It initializes the nonflag instructions' flags to NZCV = 6 and the destination to all ones, making upper-half preservation observable. The model starts X0 at all ones as well. ADCS sets input C using `CMP carry,#1`; the model sets its C directly. Other initial flags may differ for ADCS, which overwrites them. All seven compiler-emitted blocks were inspected and are preserved for both optimization levels; the assembler prints LSLV using its `lsl` register alias.

For every case, both native builds and Kraken produce the exact oracle `(result,NZCV)` pair. The four output files—mathematical oracle, Kraken, native O0, native O3—are byte-identical, SHA256 `9962a3b19b153fd776679718fcb3a7f3aea897902d2c1a6decc8feb46a171c90`. Each ADDS/ADCS corpus exercises NZCV values `0,2,3,4,6,7,8,9,10`; the nonflag cases retain 6. This is a finite set of observed paths, not a claim that all theoretically possible flags are covered.

Basis: fresh model and native **execution**, independently authored oracle, recorded parsed **source** representation.

### The source and reference rules distinguish the tested seams

Kraken's `Reg64s.setRegOrZr` zero-extends W32 writes. `StatusFlags.adds` computes carry and overflow by comparing the mathematical sums with the truncated result's unsigned/signed interpretations; ADCS includes input C in both sums. LSLV explicitly reduces the count modulo width. REV uses staged byte/halfword/word exchanges, separately for 32 and 64 bits. These are the exact definitions executed by the imported model. [Pinned register writes](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/AArch64/Semantics.lean#L133), [flags](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/AArch64/Semantics.lean#L417), [ADCS](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/AArch64/Semantics.lean#L599), [REV and variable shifts](https://github.com/AeneasVerif/kraken/blob/8af78062037bc237b341d20252aafd1797c1bcb7/Kraken/AArch64/Semantics.lean#L769).

Arm's September 2025 ADCS entry uses both registers and PSTATE.C and updates destination and NZCV; ADDS shifted-register uses zero carry with the default LSL-zero operand. Its March 2025 LSLV entry specifies the count modulo register width; REV reverses byte order in the selected register. The short Arm guide independently describes W writes clearing the corresponding X register's upper half and distinguishes flag-setting S forms from ordinary ADD. These source-level rules explain why the selected cases discriminate the relevant seams. [ADCS p18 and ADDS p28, 2025-09](https://documentation-service.arm.com/static/68da52dfbd7cab51328c0622), [LSLV p626 and REV p758, 2025-03](https://documentation-service.arm.com/static/67e40f3398aa3c3b6eea6a85), [Arm guide Issue 1.1, sections 7.1 and 9.2](https://developer.arm.com/-/media/Arm%20Developer%20Community/PDF/Learn%20the%20Architecture/Armv8-A%20Instruction%20Set%20Architecture.pdf?revision=af73a2a4-620d-4f86-86b0-2987dc04e154).

The native output initialized before input consumption uses an early `out(reg)` to prevent overlap with live inputs. ADDS/ADCS output uses `lateout` only after the instruction consumes its inputs; the preserved O0 blocks actually reuse input registers. Every changed general register is an output, and the blocks allow flags to change. `nomem` and `nostack` describe the register-only blocks. This makes the chosen Rust probe meaningful, but does not prove every allocator instantiation or a general inline-assembly bridge. [Rust Reference operand and option rules](https://doc.rust-lang.org/reference/inline-assembly.html#operand-type).

Basis: primary architecture **documentation**, direct implementation **source**, observed compiler output, and the finite **execution** comparison. No Arm ASL/Sail transition relation was imported into Lean.

### The cases detect concrete wrong alternatives

The controls alter the expected semantic rule while retaining actual positive observations. They are discriminators derived from the completed three-way equality, rather than claims that Kraken was patched or that a proof checker rejected an ISA mutant.

| Wrong rule | Concrete distinguishing case | Actual result |
|---|---|---|
| Ignore ADCS carry input | `0+0`, C=1 | 1, NZCV 0 |
| Clear output carry | `1+(2^64−1)` | 0, NZCV 6 |
| Clear signed overflow | `1+(2^63−1)` | `2^63`, NZCV 9 |
| Preserve old W destination upper half | W addition `0+0`, old X0 all ones | X0 = 0 |
| Use unmasked 64-bit shift | `1 << 64` | 1 |
| Use unmasked 32-bit shift | `1 << 32` | 1 |
| Reverse bits instead of eight bytes | REV64 of 1 | `2^56` |
| Reverse bits instead of four bytes | REV32 of 1 | `2^24` |

The Kraken evaluator consumes exactly one execute request for `[0,4)`, requires final PC 4, and checks equality to the complete initial MachineData with only X0 and status replaced. It rejects all read/write/nonmemory/undefined/unaligned effects rather than selecting an arbitrary nondeterministic result. Nonflag status equality follows from comparison with the oracle's preserved initial flags. These checks rule out a silent modeled clobber or memory effect for these concrete states; native observation covers only the declared scalar and NZCV outputs.

Basis: finite **execution** plus explicitly **derived** mutant witnesses in `support/negative-controls.json`.

## Boundaries

- **Established:** selected-entry primary documentation review and actual 1,290-case three-way validation, including a concrete model frame and eight semantic discriminators. No real disagreement was found.
- **Unestablished stronger outcome:** a universal per-instruction equivalence/refinement theorem. Lean's interpreter, the independent oracle, compiler, hardware, and harness remain trusted for this experiment; no theorem axiom closure is claimed for runtime results.
- **Not examined:** an independently executed Arm ASL/Sail model, separate Kraken AST destination/source-overlap variants, memory alignment/fault behavior, X64 instruction correspondence, or SIMD/FP/system configuration. The native allocator's recorded overlap does not establish Kraken's untested overlapping-operand ASTs.
- **Not examined:** binary decoding/binding between these Kraken programs and native executables, source-level Rust semantics, contextual UB-freedom, or a general ABI theorem. Native assembly listings are execution provenance, not an artifact certificate.
- **Not examined:** a universal carry/REV proof, matched cross-foundation proof-production/repair costs, or the broader multiply/copy/pointer/helper/SIMD pilot suite. The timings are single-run harness/build observations, not a benchmark or an architecture ranking.

## Evidence

The package preserves inputs, all four exact result streams, parsed ASTs, native sources, complete gzip-compressed compiler assembly, extracted inline blocks, tool version text, command/status/timing records, source hashes, and all eight negative witnesses. Native executable hashes are recorded, but the local binaries are excluded from the public package. `source-manifest.json` pins Kraken files and identifies the exact primary documentation entries and access method. `coverage.json` separately identifies the completed bounded AS04 investigation, stronger unestablished outcomes, and actual unexamined research.

Development logs preserve four ordinary failed Lean elaboration/execution attempts before the successful smoke check: missing module mode, an underdetermined constructor pattern, a nonpublic main, and private imports in public declarations. A subsequent harness diagnostic stopped before native execution because it expected a different assembly-comment marker. Inspection showed Apple LLVM emits `InlineAsm Start/End`, with an unrelated empty runtime block. The corrected extractor selects the seven blocks that read NZCV. That failed result and diagnosis are preserved; no panic, assertion failure, semantic disagreement, or unsafe workaround occurred. Final complete replay passed after the AST description was added.

All displayed source argv and logs are relative to `support/`; tool labels and the external read-only library location are portable. Actual private invocation coordinates and native executables remain excluded owned scratch, while version/revision identities and hashes are retained here. All observations date to 2026-10-14.

## Revalidation

On an AArch64 host with the identified tools and an existing build of the pinned Kraken source, run `python3 support/validate.py --lean /path/to/lean --kraken-lib /path/to/build/lib/lean --rustc /path/to/rustc --artifact-dir /owned/scratch/native-build`. The runner performs no installs, network requests, or upstream build. It regenerates the exact corpus and oracle, executes Kraken, checks that comparison before proceeding, compiles/inspects/runs native O0/O3, and writes exact command statuses and disagreement details. A changed assembler marker may require a diagnosed extractor update; a real mismatch must be investigated before interpreting later results.

For a changed opcode/model, first compare the pinned source definitions and selected reference entry, then rerun the smallest edge witness that distinguishes the relevant rule. Preserve the finite-validation qualification even after a clean replay. A universal architectural claim requires a separately checked relation with an authoritative ISA transition system and explicit configuration assumptions.

*Authored by an AI agent acting on joshlf's behalf.*
