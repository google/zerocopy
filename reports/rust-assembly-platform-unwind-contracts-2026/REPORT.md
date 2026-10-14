# Rust assembly exits and selected platform unwind records

## Summary

Windows x64 unwind records describe recovery from an interrupted function state, which is a different obligation from executing its normal epilogue. A newly compiled nonleaf function has matching real `.pdata`/`.xdata` records for its RBP save, 80-byte allocation and frame establishment. An owned restricted context-recovery check succeeds at five prologue/body points. Three metadata-only object mutations preserve every instruction and normal-epilogue recovery while producing the wrong recovered caller state.

The Rust interface remains separate: unwinding out of ordinary `asm!` is undefined behavior, including through a called function. A whole-function unwinding ABI or `naked_asm!` has different rules and needs suitable platform metadata. A safe Rust `C-unwind` callback specimen was compiled for Apple AArch64 and its cleanup/personality/LSDA/resume assembly inspected. No native unwind, Windows code, deliberately invalid Rust or metadata mutant was executed.

## Applicability

Primary Windows rules are `MicrosoftDocs/cpp-docs@281a0a0eae55fe97f5decd244db18ed5096d4687`, `docs/build/exception-handling-x64.md` and `prolog-and-epilog.md`. The selected subset is Windows x64 version-1 unwind information with flags zero, one function, RBP frame register and three simple unwind operations. The source also points to newer APX/v3 work; this report does not treat its version-1 subset as the complete modern format.

Actual Windows-target output uses Apple clang 21.0.0, build `clang-2100.3.34.2`, `--target=x86_64-pc-windows-msvc -O1 -fno-omit-frame-pointer -funwind-tables`. It compiles a header-free C specimen to assembly and a relocatable COFF object on an Arm Mac. The external helper is unresolved; nothing is linked or run. This is a real cross-target compiler observation, not a Windows Rust compiler result or PE loader test.

Rust rules are pinned independently to Reference `2dafab96d919d6ab2884488e970bf95610ff83eb`. The safe Rust cleanup specimen uses rustc 1.99.0 `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, LLVM 23.1.1, `aarch64-apple-darwin`, edition 2024, optimization 1, panic=unwind. Its emitted Apple CFI/exception-table format is not identified with Windows x64 `.pdata`/`.xdata`. Every new process is compile-only or Python data interpretation; no process invokes either compiled function.

## Findings

### Windows recovery rules have a different subject from normal return

Basis: pinned primary platform **documentation**, with **derived** certificate implications.

Windows uses image-relative `RUNTIME_FUNCTION` entries identifying code bounds and unwind information. A missing entry triggers leaf-style recovery from current RSP. Unwind codes describe prologue effects, ordered by code offset; a partial-prologue context uses only operations already completed. Body recovery reverses the recorded effects. Epilogues are recognized from restricted instruction patterns rather than independent records for every exit. [Function records and recovery procedure](https://github.com/MicrosoftDocs/cpp-docs/blob/281a0a0eae55fe97f5decd244db18ed5096d4687/docs/build/exception-handling-x64.md).

The selected codes undo a nonvolatile push, a small stack allocation, and frame-pointer establishment. Frame offsets are scaled by 16; small allocation size is `8 × OpInfo + 8`. Handler/chained records have additional meanings. [Selected unwind operations](https://github.com/MicrosoftDocs/cpp-docs/blob/281a0a0eae55fe97f5decd244db18ed5096d4687/docs/build/exception-handling-x64.md#unwind-operation-code).

The prologue/epilogue rules restrict stack restoration and nonvolatile saves. Larger frames require stack-probe handling; legal epilogues use particular stack adjustment, pop and transfer sequences. Thus an arbitrary sequence with the correct eventual SP is not automatically a recognizable unwind epilogue. [Prologue and epilogue rules](https://github.com/MicrosoftDocs/cpp-docs/blob/281a0a0eae55fe97f5decd244db18ed5096d4687/docs/build/prolog-and-epilog.md).

For an assembly certificate, code identity must therefore bind the actual frame instructions, their instruction boundaries, PC ranges, metadata and link/load registration. A normal-return theorem can omit all metadata because RET does not consult it. A caller-context recovery claim cannot. Separately, a language personality must arrange the right cleanup actions and resource restoration; a valid stack walk alone does not prove those actions correct.

### An actual object carries matching fixed-frame records

Basis: fresh compile-only **execution**, byte inspection and owned decoder **execution**.

`support/specimen.c` preserves four local words across a call to an external helper. Its actual prologue is:

```text
push rbp                 ; completion offset 1
sub rsp,80               ; completion offset 5
lea rbp,[rsp+80]          ; completion offset 10
```

The assembly has corresponding `.seh_pushreg`, `.seh_stackalloc`, `.seh_setframe` and `.seh_endprologue` directives. The normal epilogue is `add rsp,80; pop rbp; ret`. The compiler also emits explicit epilogue markers; their presence is observed compiler output, not a claim that every such spelling is guaranteed by the pinned Rust inline-directive list.

The 77-byte `.text` SHA256 is `f8cb6d59576072def3548aaf1b5159a9e09561bfda362028efb4d43ffd169d39`. Actual `.xdata` bytes are `010a03550a03059201500000`, decoded as:

| Field | Actual value |
|---|---|
| Version / flags | 1 / 0 |
| Prologue size / code count | 10 bytes / 3 |
| Frame register / offset | RBP / 80 |
| Code offset 10 | SET_FPREG |
| Code offset 5 | ALLOC_SMALL, size 80 |
| Code offset 1 | PUSH_NONVOL RBP |

`.pdata` contains object addends `(0,77,0)` and three kind-3 relocations to `.text`, `.text` and `.xdata`. They are unresolved object records, not final image-relative addresses. `support/check_unwind.py` checks these bounds, section/symbol identities, prologue/epilogue byte patterns and the selected records. It is a narrow unverified reader, not a validated general COFF/PE parser or linker.

The owned state witness chooses entry RSP = `0x1008`, satisfying the selected call-entry alignment; the body RSP = entry−88 is 16-byte aligned, and RBP = entry−8. Memory separately records the caller's RBP and return address. The interpreter checks recovery at offsets 0, 1, 5, 10 and 43; offset 43 is the instruction boundary following the helper call. It recovers the same caller RIP, RBP and RSP = entry+8 in all five cases. No helper behavior, asynchronous hardware exception or real OS unwinder was exercised.

### Metadata-only controls preserve return instructions but break recovery

Basis: actual object **execution** as data, owned reconstruction and **derived** contrast with the epilogue.

| Mutant | Preserved fact | Incorrect recovery |
|---|---|---|
| Frame offset 80→64 | Entire `.text` unchanged | Reads caller state from the wrong stack positions |
| Allocation record 80→72 | Entire `.text` unchanged | Uses saved RBP as return address and recovers wrong RSP |
| Rename `.pdata` to `.gone` | Entire `.text` unchanged | Owned missing-table/leaf fallback reads a local stack slot as return address |

The mutated objects are preserved. The third control removes discoverability by the owned section reader; it is not an executed Windows link/strip operation or a prediction about a malformed PE loader. The model then explicitly applies the documented missing-entry fallback at the same body snapshot.

For every mutation, the exact recognized normal epilogue still restores the correct caller state under the same supplied stack witness because its instructions are untouched. Recovery from the middle of the frame instead fails the expected caller-state check. This isolates the metadata obligation without causing an invalid unwind in a native process. It does not prove that every possible metadata error is rejected or implement full epilogue scanning.

### Rust distinguishes ordinary inline unwind from whole-function ABI policy

Basis: pinned Rust **normative** rules and new compiler **execution**.

At the Reference pin, `asm.rules.unwind` forbids unwinding out of ordinary assembly, including from a function it calls. Wrapping such a block in `extern "C-unwind"` does not remove the block's rule. `asm.naked-rules.unwind` instead permits unwinding from a naked block when suitable metadata is emitted. The target-specific list separately guarantees selected `.seh_*` directives on structured-exception-handling targets; its DWARF list concerns supporting ELF targets. A source-level CFI example is not evidence of cross-platform interchangeability. [Assembly unwind and directive rules](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/inline-assembly.md#rules-for-naked-inline-assembly).

The function ABI and panic runtime determine the allowed boundary outcome. Rust and `-unwind` ABIs permit the specified unwind under panic=unwind. A Rust panic reaching a nonunwinding boundary aborts; native unforced unwind through that boundary is undefined behavior. Panic=abort has different outcomes. Forced unwinding is expressly excluded from the Reference table and remains a separate scope. [Function unwind table](https://github.com/rust-lang/reference/blob/2dafab96d919d6ab2884488e970bf95610ff83eb/src/items/functions.md#unwinding).

`support/cleanup.rs` is a safe function taking a safe `extern "C-unwind"` callback and owning a guard with a Drop action. Its actual Apple AArch64 output has `.cfi_personality`, `.cfi_lsda`, X29/X30 save rules, an indirect callback call, a normal Drop action and return, plus a cleanup Drop action followed by `__Unwind_Resume` and a `__gcc_except_tab` call-site table. The generated cleanup is substantive compiler evidence beyond the source ABI spelling. It is not a parser/semantic proof of those tables, a Windows emission, or a native callback/unwind test. The guard action uses a safe `black_box(7)` and the function is never invoked here.

The companion resource-linking and unwind reports retain callback/reentrancy, protector and exceptional-resource obligations. Neither correct machine-frame recovery nor the callback's ABI alone proves those resources are restored. Actual cleanup, personality/runtime identity and caller invariants must remain in the eventual language-linking theorem.

## Boundaries

- **Established:** exact selected Windows rules, actual COFF unwind metadata, five owned positive recovery contexts and three metadata-only discriminators; separately inspected actual Apple AArch64 Rust cleanup assembly and pinned Rust interface rules.
- **Unestablished stronger outcomes:** verified loader/unwinder/metadata producer, language-personality correctness, actual helper/callback assembly proof, universal unwind safety or a Rust/MiniRust/Kraken contextual theorem.
- **Not examined:** full epilogue recognition, large/chained/handler/XMM/machine-frame/APX-v3 records, dynamic frame variations, final PE linking/loading/table registration, forced unwinding or nonlocal jumps.
- **Not examined:** Apple compact-unwind/DWARF runtime interpretation, AArch64 Windows unwind metadata or Windows Rust code generation. Platform format differences are explicit configuration boundaries.
- **Not performed:** any native unwind, Windows execution, invalid Rust, full unwinder proof or stripped-metadata runtime test. Suggested verified-helper/CFI execution ports remain optional unperformed experiments, not silently completed outcomes.

## Evidence

All observations date to 2026-10-14. `source-evidence.json` identifies exact primary files, hashes, Git blobs and sections; the Microsoft source was independently fetched at the pin. Rust files were directly reread from the parent's hash-bound primary-source cache, without changing them. Full documentation prose remains in excluded source-reading cache, not copied into this report.

`support/execution.json` retains all six successful command statuses, relative argv, tool identity, source/output hashes and times. `specimen.s`, `specimen.obj`, `cleanup.s`, all three mutated objects, `unwind-results.json` and the portable scripts preserve the complete bounded experiment. No unexpected failure, panic, assertion, install, upstream build or native execution occurred. Object timestamps can change on replay; the semantic comparison checks the selected code/record structure rather than expecting a timeless whole-file hash.

## Revalidation

In a disposable package copy, run `python3 support/revalidate.py --clang /path/to/clang --rustc /path/to/rustc`. This compiles the Windows specimen and Apple AArch64 Rust specimen and executes only the Python data checker. It makes no network requests or installs. The recorded host/target compiler configuration is required; a different prologue, format version or emitted instruction pattern deliberately needs a reviewed checker update.

For a real supported unwind claim, bind the final code and metadata ranges, resolve/register the function table, prove all relevant partial-prologue/body/epilogue cases, connect the selected personality/runtime's cleanup protocol, and restore the Rust caller's resource relation on each permitted exit. Keep ordinary inline assembly's unwind prohibition intact.

*Authored by an AI agent acting on joshlf's behalf.*
