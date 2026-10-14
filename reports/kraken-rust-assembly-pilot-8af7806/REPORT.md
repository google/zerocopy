# AArch64 Rust/inline/naked addition: Kraken proofs and executable binding pilot

## Summary

This pilot connects several separately observed pieces of one small assembly-verification case. Unmodified Kraken source was built on Lean4.34.1. Two new theorems establish modular addition and returning-state preservation for actual parsed AArch64 programs, with only `propext`, `Classical.choice` and `Quot.sound` in their reported dependencies. Real Rust implementations using ordinary inline assembly and a whole naked C ABI function agree with `wrapping_add` on8,292 selected input pairs at optimization0 and3. Bounded read/store cases also pass. An owned Mach-O reader matches the naked leaf's bytes in the object and both linked executables, and rejects selected identity mutants.

These results do not establish the missing complete ISA, decoder, Rust source-import or resource-linking theorems. They identify exactly which parts of a future Anneal pipeline can be exercised together now, and which arrows remain assumptions or future proofs.

## Applicability

Kraken source: `8af78062037bc237b341d20252aafd1797c1bcb7`, public archive SHA256 `b2acfb541396a9cacec36bf4e954b9294ae4272d4d32e61f73c8716cf2de1d60`,148,757bytes. The source pins nightly2026-09-21; this experiment instead explicitly uses installed Lean4.34.1 `5045d0056413266e57c625dcd7c365b10e377c52`. Its manifest has no external packages. No source change was made to make it build. The reported build therefore does not establish the pinned nightly's behavior.

Rust source/codegen/execution:1.99.0 `b940084d7eb6a299eb4bfeb8e34901bc051e7ac4`, `aarch64-apple-darwin`, edition2024, panic abort, optimization0/3. Host execution is native arm64 macOS. ELF/COFF and native x86 execution are not part of this pilot. Companion reports supply ABI and alternative-foundation evidence.

Coverage: actual experiments for AS01/AS06/AS08–AS12/AS14/AS16/AS28; these bounded experiments supplement the broader literature/source findings rather than discharge each topic's production integration goals.

## Findings

### Actual source builds, but theorem closure is a separate observation

Basis: source + execution.

The unmodified `lake build Kraken KrakenAArch64` completed43jobs with the selected installed kernel. It built both Examples modules. Some upstream examples contain `sorry`; imported admitted declarations do not automatically contaminate every independently proved theorem. The new theorem dependencies were therefore inspected explicitly.

Upstream memory-tactic debug logging produced pretty-printer fallback messages concerning free variables. The inspected logging sites omit entry into the subgoal local context, which is a supported explanation for these fallbacks; a definitive Lean-level reproduction of their root cause was not performed. These messages are not evidence of a kernel rejection or acceptance defect. The pilot uses the simple register path and complete successful checker verdicts. The companion Kraken audit records the diagnostic limitation, selected upstream axioms and the difference between native reduction axioms and `sorryAx`.

### The two checked Kraken claims

Basis: source + machine-checked owned proofs.

`addBody` is the actual Kraken parse of `add x0, x0, x1`. For arbitrary `MachineData` and a layout, `addBody_correct` proves that `X0` becomes the UInt64 modular sum and modeled memory, SP and status remain unchanged.

`addReturn` parses that instruction followed by `ret`. `addReturn_correct` proves the entire resulting modeled `MachineData` equals the initial record with only `X0` updated, and the next instruction-pointer bits equal the initial `X30` bits. This includes all modeled non-output registers, not a sampled preserved-register list. The proof uses ordinary simplification after Kraken stepping; neither new theorem depends on `sorryAx` or a native arithmetic axiom.

These are actual Kraken statements over its parsed program, operational semantics and default `Effects.All`. That default interpretation does not itself enforce Rust/OS execution permissions. The caller-to-machine relation and all physical facts absent from the modeled state remain separate obligations. A universal theorem over modeled values is not a theorem that every arbitrary hardware state may legally enter a Rust function.

### Native Rust comparisons

Basis: execution.

`pilot.rs` contains:

- a pure-Rust `wrapping_add` C ABI function;
- a register-class `asm!` addition with a late output and conservative effects;
- a naked C ABI leaf containing `add x0,x0,x1; ret`;
- an inline byte load, called only on a live initialized byte;
- a naked `str x1,[x0]; ret` store, called only with an aligned exclusive `u64` slot.

Both optimization configurations pass100boundary pairs plus8,192 deterministic generated pairs, comparing both arithmetic assembly routes with the Rust result. Each also passes all256byte inputs with surrounding-byte checks, and10store inputs with surrounding `u64` checks. No deliberately invalid pointer, overlap, permission, option or invalid Rust value is executed.

The data tests do not prove universal correctness of the load/store routines or complete access traces. The arithmetic theorem is universal within Kraken; the native test is finite empirical agreement. The two forms of evidence complement rather than replace each other.

### Object and linked-byte observations

Basis: execution + owned parser/checker.

The optimization3 Rust object contains `_naked_add` bytes `0000018bc0035fd6` and `_naked_store` bytes `010000f9c0035fd6`. The same selected byte sequences occur under their named symbols in both native linked executables, although whole-artifact hashes and symbol file offsets differ.

`macho_binding.py` reads thin little-endian arm64 Mach-O64 headers, load commands, sections and symbol tables with bounded range checks. It binds each selected name to the expected8-byte range in `__TEXT,__text`. It rejects a one-byte addition mutation, three truncated inputs and a wrong expected-function pattern for each of the three observed artifacts. Full original artifact hashes and extracted-range hashes are retained in `binding-results.json`.

This is an owned executable data-binding check, not a verified Mach-O loader, a complete ISA decoder or a source-to-binary proof. The match is for these exact selected ranges. It does not prove dynamic loading, interposition, code patching, every linked symbol or all executable memory matches a certificate.

An actual compile-only upgrade control changes the naked leaf from ADD to SUB and recompiles it under the same settings. The old addition-byte claim fails while the unchanged store-byte claim still matches. No changed function is executed, and no new correctness proof is accepted by updating expected bytes. `upgrade-control/result.json` records source/object/range hashes and timing. This is build-specific invalidation evidence, not a verified general upgrade protocol.

### Binding across compilation, linking and deployment

Basis: primary documentation + performed binding controls + derived obligations.

The object is one intermediate subject. LLVM's [ThinLTO documentation](https://clang.llvm.org/docs/ThinLTO.html), observed2026-10-14, describes summary-driven importing followed by optimizing backends during linking. Thus a pre-LTO source/object association does not identify every final generated instance. LLD's [linker description](https://lld.llvm.org/NewLLD.html), observed the same date, explains identical-code folding and loader base relocations. The [RISC-V ABI relaxation specification](https://docs.riscv.org/reference/abi/riscv-elf-linker-relaxation.html) explicitly allows relaxation to delete bytes and requires relocation discipline for affected references. These are examples of real transformation mechanisms, not evidence that this Mach-O scalar leaf underwent all of them.

| Mechanism | What an assembly certificate must bind or prove |
|---|---|
| Symbols and code/data sections | Exact range, section interpretation, entry points and all code/data used by execution |
| Relocations, PIC, GOT/PLT and thunks | Resolved targets and environment, or a theorem parameterized by admitted relocation values; verify any generated thunk |
| Relaxation and instruction-size changes | Decode/layout after transformation, or proved preservation including shifted branches and data references |
| LTO, outlining, inlining and deduplication | Enumerate final instances and their contracts; shared bytes do not automatically identify one source context |
| Interposition and feature dispatch | Every reachable selected implementation and its feature/ABI domain; a proof for one branch cannot cover an unproved branch |
| Loading, patching and replacement | Runtime address/environment assumptions and code identity for the duration of the claim |

Three designs make different commitments. A relocation-parametric proof accepts a precisely defined environment and proves every admitted instantiation. Post-link validation identifies final decoded ranges, then checks their relation to proved programs. A restricted immutable deployment can prohibit dynamic replacement and accept a narrower loader assumption. None follows from a source hash alone. Rust's pinned `target_feature` rules additionally require the relevant supported CPU feature domain; the runtime dispatch decision and compiled function identity both matter.

This pilot exercises final named ranges, stale expected code, one-byte patches and wrong expected functions. The companion ELF experiment rejects relocations in its selected section rather than claiming to interpret them. General thunks, alternate dispatch branches, changed relocations, interposition and live patching were investigated as interface obligations, not executed or verified here. These are explicit boundaries for adopting the restricted checker.

### The precise remaining arrows

Basis: derived.

| Arrow | Evidence in this pilot | Remaining stronger conclusion |
|---|---|---|
| Rust function → emitted interfaces | Source, compiler revision, LLVM and assembly observations | Checked source/codegen correspondence |
| Kraken text → modeled arithmetic/return | Actual parsed definitions and universal closed proofs | Parser/specification faithfulness and complete real ISA relation |
| Selected symbol → object/linked bytes | Bounded Mach-O reader and mutants | Verified decoder/loader/link model |
| C ABI inputs → machine entry | Source signature, target witness and successful native calls | General checked ABI relation |
| Machine execution → Rust resource-safe continuation | Register-only model frame, valid native calls | Complete validity/provenance/borrow/environment linking theorem |

An Anneal certificate should expose this table's exact completed claims. Treating all rows as one green “assembly proof” would conceal the unproved interpretation boundaries. The small register-only domain is valuable because its memory-resource relation is simple, not because the general relation disappears.

### Costs and reproducibility

Basis: execution.

Native compile/run phase timings are retained separately in `native-results.json`. The initial observed compile times were approximately0.42s at optimization0 and0.14s at optimization3; each execution took approximately0.06s on this host. Those are single-run operational observations, not a comparative performance claim. The replay helper also records proof/checking and object-binding phases separately.

The source, proof, environment identities and expected selected bytes are public support material. Large executable/build caches are not needed in the report package. A recompile may change whole-file hashes or offsets; it must still re-establish symbol/range and selected-byte binding rather than trusting historical offsets.

## Boundaries

The pilot does not prove complete inline register-allocation correctness through rustc, all platform ABIs, all instruction encodings, arbitrary safe-client soundness or physical hardware faithfulness. The new proofs use Kraken's actual simplifications and default access interpretation. No pinned-nightly build, relaxed-memory proof, constant-time proof, callback, unwind, privileged code, vector implementation or full Rust extraction was performed here.

An initial owned proof attempt failed ordinary simplification; it was not accepted evidence. The final complete successful source and output are retained. No source-model or checker assumption was weakened to make a failed theorem pass; the final return theorem was strengthened to a full modeled-state frame.

## Evidence

- [Kraken source pin](https://github.com/AeneasVerif/kraken/tree/8af78062037bc237b341d20252aafd1797c1bcb7), its toolchain/manifest, AArch64 parser/semantics and proof modules.
- `support/KrakenPilot.lean`, checker output and exact source hash; both final theorem closures have only the stated foundational trio.
- `support/pilot.rs`, Rust version and commands, native phase results, generated optimization3 LLVM/assembly and selected symbol data.
- `support/macho_binding.py`, `binding-results.json` and selected object/linked-code identity mutants.
- `support/upgrade_control.py` and `support/upgrade-control/`: compile-only ADD-to-SUB source mutation and old-claim rejection; no replacement proof.
- `support/revalidate.py`: explicit caller-selected tools and Kraken library root; no toolchain installation or external source execution hidden in the helper.

## Revalidation

Acquire and inspect the exact Kraken source, build its libraries with the intended explicitly selected kernel, and run the retained proof through that library path. Check exit status and axioms. The supplied replay helper requires an explicit Kraken library root and runs the owned native code only on the recorded arm64 target; it never runs the false-contract specimens from the companion report.

Recompile at both optimization levels, compare the native outcomes, regenerate the LLVM/object witness and repeat byte-binding/mutation checks. On a new platform, write and justify a new ABI/representation domain before running a corresponding assembly function. Source or bytes changing invalidates the historical certificate; it is not a reason to update expected bytes without renewing the semantic proof.

*Authored by an AI agent acting on joshlf's behalf.*
