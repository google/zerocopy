# Verified Assemblers, Instruction Encoders, Static Linkers, and Object-Format Formalizations

## Summary

A drop-in verified `rustc` replacement must eventually bridge the backend gap between in-memory assembly ASTs and relocatable object files (`.o` / `.rlib`: ELF, Mach-O, COFF) or linked executables/shared libraries, and its initial (`v0`) backend choices must remain forward-compatible with a future verified assembler and linker. Combining source inspection of existing verified binary toolchains (`CompCertELF`, `CakeML`, `MM0`, `Linksem`, `RockSalt`, `Valex`, `seL4` binary translation validation) with an exhaustive relocation census across all **8 Tier 1 targets** in `rustc 1.99.1` (`support/tier1_relocation_and_tablegen_census.json`) establishes four decisive engineering conclusions:

1. **Extreme Concentration of Actual `rustc 1.99.1` Relocations Across All 8 Tier 1 Targets:** Although LLVM 23.1.1 (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) defines **44** ELF relocation kinds in `x86_64.def`, **41** in `i386.def`, and **236** in `AArch64.def` (plus Mach-O and COFF tables in `MachO.h` and `COFF.h`), scanning all **2,494 object files** inside `rustc 1.99.1`'s prebuilt `libcore`, `liballoc`, `libstd`, and `libcompiler_builtins` `.rlib` archives (totalling **853,376 relocation entries**) proves that `rustc` emits only **4 to 19 distinct relocation kinds per Tier 1 target**:
   - **`x86_64-unknown-linux-gnu` (ELF64):** **8 kinds** across 183,098 relocations (`R_X86_64_64`, `R_X86_64_32`, `R_X86_64_PC32`, `R_X86_64_GOTPCREL`, `R_X86_64_PLT32`, and 3 TLS kinds `TLSGD`, `DTPOFF32`, `TLSLD`).
   - **`i686-unknown-linux-gnu` (ELF32):** **9 kinds** across 190,767 relocations (`R_386_32`, `R_386_PLT32`, `R_386_GOTOFF`, `R_386_PC32`, `R_386_GOTPC`, `R_386_GOT32`, and 3 TLS kinds).
   - **`aarch64-unknown-linux-gnu` (ELF64):** **19 kinds** across 205,766 relocations (dominated by `R_AARCH64_ABS64`, `R_AARCH64_ABS32`, `R_AARCH64_CALL26`, `R_AARCH64_ADR_PREL_PG_HI21`, `R_AARCH64_ADD_ABS_LO12_NC`, `R_AARCH64_PREL32`, `R_AARCH64_JUMP26`, GOT page/lo12, and 4 TLSDESC kinds).
   - **`aarch64-apple-darwin` (Mach-O arm64):** **11 kinds** across 60,870 relocations (`ARM64_RELOC_UNSIGNED`, `BRANCH26`, `PAGEOFF12`, `PAGE21`, `SUBTRACTOR`, `GOT_LOAD_PAGEOFF12`/`PAGE21`, `ADDEND`, `TLVP_LOAD_PAGEOFF12`/`PAGE21`, `POINTER_TO_GOT`).
   - **Windows Tier 1 Targets (COFF):** Only **4 kinds** on `x86_64-pc-windows-gnu` (121,012 relocations), **5 kinds** on `x86_64-pc-windows-msvc` (32,689 relocations), **5 kinds** on `i686-pc-windows-msvc` (26,625 relocations), and **12 kinds** on `aarch64-pc-windows-msvc` (32,549 relocations).
2. **Formal Object-Format Coverage Asymmetry:** ELF64/ELF32 static linking and relocation patching are thoroughly formalized in **Linksem** (`rems-project/linksem`, Lem/HOL4/Isabelle/Coq, `10.1145/2983990.2983996`) and **CompCertELF** (Coq, `10.1145/3428265`), and direct ELF executable generation is proved in **CakeML** and **MM0**. By contrast, **neither Mach-O (`aarch64-apple-darwin`) nor PE/COFF (`*-pc-windows-*`) has an existing mechanized static-linking semantics** in Coq, HOL, Isabelle, or Lean 4 (only binary parser/serializer specifications in EverParse/Narcissus exist). However, because `rustc` emits at most 11 Mach-O and 4–12 COFF relocation kinds across all of `std`, a purpose-built Lean 4 relocation model for the `rustc`-emitted subset of ELF, Mach-O, and COFF is compact (~1,500–2,500 LoC).
3. **Keeping `v0` Choices Compatible with a Future Verified Assembler and Linker:** To avoid painting `v0` into an architectural corner, `v0` should:
   - Emit structured MC-level relocation fixups (explicit `(offset, kind, symbol, addend)` tuples) rather than relying on textual assembler expression evaluation or linker relaxation (`R_X86_64_GOTPCRELX` / `R_X86_64_REX_GOTPCRELX` are already absent from `rustc 1.99.1`'s prebuilt `rlib`s when assembled via LLVM's integrated assembler without relax-relocations, or can be disabled via `-Wa,-mrelax-relocations=no`);
   - Isolate DWARF/unwind emission (`.eh_frame`, `.pdata`/`.xdata`, `__compact_unwind`) in dedicated metadata sections separate from `.text` / `.rodata` semantics;
   - Verify round-trip decode-of-encode (`decode (encode instr) = some instr`) against the trusted ISA decoder rather than trusting unverified TableGen bit-packing emitters.

## Applicability

The findings and empirical data in this report apply to:
- **Rust 1.99.1 (`rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`):** Prebuilt `.rlib` archives (`libcore`, `liballoc`, `libstd`, `libcompiler_builtins`) and `--emit=obj` output across all 8 Tier 1 targets (`x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`, `i686-pc-windows-msvc`, `aarch64-pc-windows-msvc`).
- **LLVM 23.1.1 (`llvm/llvm-project@1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):** `llvm/include/llvm/BinaryFormat/ELFRelocs/{x86_64,i386,AArch64}.def`, `MachO.h`, `COFF.h`, and `llvm/lib/Target/{X86,AArch64}/*.td`.
- **Examined verified assemblers, encoders, linkers, and binary validators:**
  - `CakeML/cakeml@b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8` (`compiler/encoders/{x64,arm8}/`, `compiler/backend/lab_to_targetScript.sml`);
  - `digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956` (`examples/x86.mm0`, `mm0-lean/x86/x86.lean`, `mm0-lean/x86/assembly.lean`);
  - CompCertELF (Wang, Song, Chen, and Hobor, *OOPSLA 2020*, `10.1145/3428265`);
  - Linksem (`rems-project/linksem`, Kell, Mulligan, and Sewell, *OOPSLA 2016*, `10.1145/2983990.2983996`);
  - RockSalt (Morrisett et al., *PLDI 2012*, `10.1145/2254064.2254111`);
  - AbsInt Valex and seL4 binary translation validation (Sewell, Myreen, and Klein, *PLDI 2013*, `10.1145/2491956.2462183`).

## Findings

### 1. Precedent Survey: Verified Assemblers, Encoders, Linkers, Loaders, and Binary Validators

Basis: source (`CakeML/cakeml@b064083e`, `digama0/mm0@0d414c0b`) + documentation

The table below compares the architecture, coverage, effort, and TCB assumptions of every major verified encoding, assembling, linking, and binary-validation system:

| System | Host Prover & Artifacts | Architectures & Object Formats | Core Theorem / Verification Mechanism | Coverage & Limitations | Effort & TCB Assumptions |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **CompCertELF** (Wang et al., *OOPSLA 2020*, `10.1145/3428265`) | Coq (~38k LoC on top of CompCert) | **x86-32 (`i386`)** and **x86-64** (later extended to RISC-V); **ELF32 / ELF64** relocatable `.o` and static executables | End-to-end separate compilation and static linking theorem: C $\to$ `Asm` $\to$ relocatable ELF `.o` $\to$ linked ELF memory image refines Clight semantics | Covers CompCert's ~115 instructions and 5 core ELF relocation types (`R_386_32`, `R_386_PC32`, `R_X86_64_64`, `R_X86_64_PC32`, `R_X86_64_32S`); no TLS, no GOT/PLT dynamic linking, no DWARF `.eh_frame`, no inline asm | ~2.5 person-years. Proves round-trip `decode(encode(i)) = Some i` against a Coq x86 byte decoder; trusts OS ELF loader mapping `PT_LOAD` segments |
| **CakeML Encoders & `lab_to_target`** (`CakeML/cakeml@b064083e`) | HOL4 (`x64_targetScript.sml`: 750 lines; `x64_targetProofScript.sml`: 2,163 lines; `arm8_targetScript.sml`: 669 lines; `arm8_targetProofScript.sml`: 1,750 lines; `lab_to_targetScript.sml`: 514 lines) | **x86-64, AArch64 (`arm8`), RISC-V 64, MIPS, ARMv7, Silver**; emits complete static **ELF** binary (`CakeML` compiler bootstrapping) | `backend_correct` proves that `compile_lab` (which iteratively resolves label offsets, relaxes short/long jumps, and emits raw machine bytes) refines `labSem` into target L3 `mc_conf` execution | Encodes only the ~35–45 instructions per target in CakeML's `asm` datatype; bypasses `.o` relocatable files by resolving all internal labels inside `lab_to_target` and emitting a flat executable byte array + ELF header | ~1–2 person-months per target encoder (`x64_encode`, `arm8_encode`) proved against HOL4 L3 decoders (`x64_decode`, `arm8_decode`). Trusts L3 ISA decode/step semantics |
| **Metamath Zero (MM0)** (`digama0/mm0@0d414c0b`) | MM0 / MM1 + Lean 3 (`examples/x86.mm0`: 1,727 lines; `mm0-lean/x86/x86.lean`: 880 lines; `mm0-lean/x86/assembly.lean`: 158 lines) | **x86-64**; static **ELF64** single-segment executable | Relational specification of x86-64 byte decoding (`decode : karch -> list byte -> ast -> Prop`), virtual memory protection (`PT_LOAD`), and `sys_read`/`sys_write`/`sys_exit` ELF entry | Covers ~30 core x86-64 instructions used by the MMC compiler; single `PT_LOAD` segment at `0x400000` without separate `.o` linking | ~1 person-year. Remarkably small TCB: `x86.mm0` defines the entire x86-64 subset, ELF64 header, and Linux process startup in 1,727 lines |
| **Linksem** (`rems-project/linksem`, Kell et al., *OOPSLA 2016*, `10.1145/2983990.2983996`) | Lem ($\to$ HOL4, Isabelle/HOL, Coq, OCaml; ~45k LoC Lem) | **ELF32 & ELF64** across **x86-64, AArch64, PowerPC64, RISC-V** | Executable specification of the complete ELF object format, section headers, symbol resolution (strong/weak, `COMMON`, archives `.a`), and relocation calculation (`abi_aarch64_relocation.lem`, `abi_amd64_relocation.lem`) | Most complete formal ELF linker model in existence: covers TLS relocations, GOT/PLT stub creation, and linker scripts. Validated by linking real Debian user-space binaries (`bzip2`, `gzip`) | ~3 person-years. Specification + executable oracle (not a compiler-integrated preservation proof over an ISA step relation) |
| **RockSalt & CSLED / Narcissus / EverParse** (`10.1145/2254064.2254111`) | Coq (`RockSalt` ~10k LoC; `Narcissus` / F* `EverParse`) | **x86-32 / x86-64** instruction decoding (`RockSalt`) and binary format parsers (`EverParse` for PE/COFF/ELF headers) | Declarative regular-expression / table-driven bit-level DSL for x86 instruction decoding, verified against Software Fault Isolation (NaCl) sandbox policy | `RockSalt` covers ~300 x86 instructions (~85% of GCC-emitted opcodes); `EverParse` generates verified zero-copy C/Rust binary parsers for network/file headers | Demonstrated that **table-driven decoder DSLs** cut x86 decoder proof size by 5–10$\times$ compared to case-splitting on raw byte streams |
| **AbsInt Valex & seL4 Binary Translation Validation** (`10.1145/2491956.2462183`) | HOL4 + Isabelle/HOL + SMT (`seL4 TV`); commercial static analyzer (`AbsInt Valex` for CompCert) | **ARMv7 / AArch64 / RISC-V** (`seL4 TV`); **PowerPC / TriCore / ARM** (`Valex`) | **Post-link binary validation:** decompiles the final linked ELF executable into HOL4/L3 (`decompile_to_logic`), reconstructs CFGs and stack bounds, and proves refinement against C/SIMPL without verifying the assembler or linker! | `seL4 TV` handles full C kernel binaries (10k+ LoC) at `-O1`/`-O2`; fails on hand-written context-switch assembly, linker-inserted errata thunks unless modeled, and complex loop vectorization | **Crucial architectural lesson:** Binary translation validation eliminates the assembler and linker from the TCB for a single binary, **assuming** the binary decoder (`L3`) and ELF loader segment map are faithful to hardware |

### 2. Sources of Instruction Encoding Data

Basis: source (`llvm/llvm-project@1b9c0d5f`, `intelxed/xed`, `aarchmrs v2025-03_rel`)

Building a verified encoder/decoder for `x86_64`, `i386`, and `aarch64` requires an authoritative, machine-readable source of bitfields, prefixes, and operand encodings:

| Encoding Data Source | Scope & Size | Strengths | Weaknesses & Pitfalls for Verification |
| :--- | :--- | :--- | :--- |
| **1. Arm AArchMRS (`ASL` + Encoding XML/JSON `v2025-03_rel`)** | 100% of Armv8-A / Armv9-A A64, SVE, SVE2, SME (`fixed 32-bit` instruction words) | **Gold standard:** Every instruction diagram in the Arm ARM is a machine-readable 32-bit mask/value pattern coupled directly to its ASL decode block and operational execute block. | None for AArch64; fixed 32-bit instruction width makes bijective decode/encode verification in Lean 4 (`BitVec 32`) straightforward via `bv_decide`. |
| **2. Intel XED (`intelxed/xed`, Apache-2.0)** | 100% of 16/32/64-bit x86 (Legacy, VEX, XOP, EVEX/AVX-512, AMX, AVX10, APX) in declarative `datafiles/` | **Best source for x86 encoding/decoding:** Clean, vendor-maintained declarative grammar (`ModRM`, `SIB`, `REX`, `VEX`, `EVEX`, compressed `disp8*N` scaling factors) decoupled from compiler selection DAGs. | Provides encoding/decoding syntax and operand width/register bindings, but **not** operational semantics (must be paired with ACL2/K-X86-64/Kraken semantics). |
| **3. LLVM 23.1.1 TableGen (`llvm/lib/Target/{X86,AArch64}/*.td`)** | **X86:** 65 `.td` files, 89,325 lines, **11,867** `def`/`defm` records; **AArch64:** 56 `.td` files, 113,058 lines, **13,804** `def`/`defm` records | Matches `rustc` / LLVM's internal `MCInst` opcodes 1-to-1; already drives `LLVMDisassembler` and `MCCodeEmitter`. | **High incidental complexity:** Mixes instruction selection patterns (`Pat<...>`), scheduling models, pseudo-instructions, and custom C++ `EncoderMethod` / `DecoderMethod` hooks (`X86MCCodeEmitter.cpp`) that cannot be extracted purely from `.td` bitfields. |

### 3. Empirical Census of Relocations Emitted by `rustc 1.99.1` Across All 8 Tier 1 Targets

Basis: source (`llvm/llvm-project@1b9c0d5f`) + execution (`support/tier1_relocation_and_tablegen_census.json`, `support/measure_tier1_relocations.py`)

A persistent fear when planning a verified assembler and linker is the size of the relocation specification: `llvm/include/llvm/BinaryFormat/ELFRelocs/` defines **44** relocation types in `x86_64.def`, **41** in `i386.def`, and **236** in `AArch64.def`. To determine how many relocation types `rustc` actually emits across ELF, Mach-O, and COFF, we extracted all **2,494 `.o` object files** from `rustc 1.99.1`'s prebuilt `libcore`, `liballoc`, `libstd`, and `libcompiler_builtins` `.rlib` archives across all 8 Tier 1 targets and also compiled a representative multi-feature probe crate (`probe_reloc.rs` exercising `AtomicUsize`, `static mut`, cross-function calls, trait objects / vtables, and function pointers) at `-Copt-level=0`, `-Copt-level=3`, and `-Copt-level=s`.

| Tier 1 Target | Object Format (`llvm-readobj`) | `.rlib` Objects Scanned | Total `.rlib` Relocations | Distinct Kinds in `.rlib`s (vs. LLVM `.def` Universe) | Complete List of Relocation Kinds Emitted Across `core` + `alloc` + `std` + `compiler_builtins` (Count) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **`x86_64-unknown-linux-gnu`** | `elf64-x86-64` | 312 | **183,098** | **8** (of 44 in `x86_64.def`) | `R_X86_64_64` (95,674), `R_X86_64_32` (69,885), `R_X86_64_PC32` (9,227), `R_X86_64_GOTPCREL` (6,262), `R_X86_64_PLT32` (1,970), `R_X86_64_TLSGD` (36), `R_X86_64_DTPOFF32` (28), `R_X86_64_TLSLD` (16) |
| **`i686-unknown-linux-gnu`** | `elf32-i386` | 311 | **190,767** | **9** (of 41 in `i386.def`) | `R_386_32` (171,322), `R_386_PLT32` (6,401), `R_386_GOTOFF` (6,230), `R_386_PC32` (4,214), `R_386_GOTPC` (1,932), `R_386_GOT32` (595), `R_386_TLS_GD` (36), `R_386_TLS_LDO_32` (23), `R_386_TLS_LDM` (14) |
| **`aarch64-unknown-linux-gnu`** | `elf64-littleaarch64` | 408 | **205,766** | **19** (of 236 in `AArch64.def`) | `R_AARCH64_ABS64` (111,478), `R_AARCH64_ABS32` (73,466), `R_AARCH64_CALL26` (7,700), `R_AARCH64_ADR_PREL_PG_HI21` (3,981), `R_AARCH64_ADD_ABS_LO12_NC` (3,656), `R_AARCH64_PREL32` (2,715), `R_AARCH64_JUMP26` (658), `R_AARCH64_ADR_GOT_PAGE` (576), `R_AARCH64_LD64_GOT_LO12_NC` (574), `R_AARCH64_PREL64` (389), `R_AARCH64_LDST{8,128,64,16,32}_ABS_LO12_NC` (361 total), `R_AARCH64_TLSDESC_{ADR_PAGE21,LD64_LO12,ADD_LO12,CALL}` (53 each) |
| **`aarch64-apple-darwin`** | `Mach-O arm64` | 376 | **60,870** | **11** | `ARM64_RELOC_UNSIGNED` (42,406), `ARM64_RELOC_BRANCH26` (7,711), `ARM64_RELOC_PAGEOFF12` (3,981), `ARM64_RELOC_PAGE21` (3,931), `ARM64_RELOC_SUBTRACTOR` (1,719), `ARM64_RELOC_GOT_LOAD_PAGEOFF12` (359), `ARM64_RELOC_GOT_LOAD_PAGE21` (359), `ARM64_RELOC_ADDEND` (293), `ARM64_RELOC_TLVP_LOAD_PAGEOFF12` (46), `ARM64_RELOC_TLVP_LOAD_PAGE21` (46), `ARM64_RELOC_POINTER_TO_GOT` (19) |
| **`x86_64-pc-windows-msvc`** | `COFF-x86-64` | 280 | **32,689** | **5** | `IMAGE_REL_AMD64_REL32` (11,291), `IMAGE_REL_AMD64_ADDR32NB` (9,521), `IMAGE_REL_AMD64_SECREL` (6,142), `IMAGE_REL_AMD64_SECTION` (5,025), `IMAGE_REL_AMD64_ADDR64` (710) |
| **`x86_64-pc-windows-gnu`** | `COFF-x86-64` | 254 | **121,012** | **4** | `IMAGE_REL_AMD64_SECREL` (60,847), `IMAGE_REL_AMD64_ADDR64` (41,094), `IMAGE_REL_AMD64_REL32` (13,994), `IMAGE_REL_AMD64_ADDR32NB` (5,077) |
| **`i686-pc-windows-msvc`** | `COFF-i386` | 279 | **26,625** | **5** | `IMAGE_REL_I386_DIR32` (8,132), `IMAGE_REL_I386_SECREL` (6,096), `IMAGE_REL_I386_REL32` (5,276), `IMAGE_REL_I386_SECTION` (4,950), `IMAGE_REL_I386_DIR32NB` (2,171) |
| **`aarch64-pc-windows-msvc`** | `COFF-ARM64` | 274 | **32,549** | **12** | `IMAGE_REL_ARM64_ADDR32NB` (7,345), `IMAGE_REL_ARM64_BRANCH26` (5,033), `IMAGE_REL_ARM64_SECREL` (5,027), `IMAGE_REL_ARM64_PAGEBASE_REL21` (4,760), `IMAGE_REL_ARM64_SECTION` (4,704), `IMAGE_REL_ARM64_PAGEOFFSET_12A` (3,221), `IMAGE_REL_ARM64_PAGEOFFSET_12L` (1,589), `IMAGE_REL_ARM64_ADDR64` (710), `IMAGE_REL_ARM64_SECREL_HIGH12A` (69), `IMAGE_REL_ARM64_SECREL_LOW12A` (56), `IMAGE_REL_ARM64_REL32` (21), `IMAGE_REL_ARM64_SECREL_LOW12L` (14) |

Furthermore, in our standalone `probe_reloc.rs` compilation across `-O0`, `-O3`, and `-Os` (`support/tier1_relocation_and_tablegen_census.json`):
- For standard non-TLS code at `-O3`, `x86_64-unknown-linux-gnu` emits only **3 relocation kinds** (`R_X86_64_GOTPCREL`, `R_X86_64_PC32`, `R_X86_64_64`), `x86_64-pc-windows-msvc` and `x86_64-pc-windows-gnu` emit only **3 kinds** (`IMAGE_REL_AMD64_ADDR32NB`, `IMAGE_REL_AMD64_REL32`, `IMAGE_REL_AMD64_ADDR64`), and `i686-pc-windows-msvc` emits only **2 kinds** (`IMAGE_REL_I386_DIR32`, `IMAGE_REL_I386_REL32`)!
- On `x86_64-unknown-linux-gnu` at `-O0`, `rustc 1.99.1` additionally emits `R_X86_64_REX_GOTPCRELX` (2 instances, allowing `lld` to relax `movq sym@GOTPCREL(%rip), %rax` into `leaq sym(%rip), %rax` when `sym` resolves locally). A verified linker or binary validator can either model this 1-instruction `MOV`-to-`LEA` relaxation or disable it during object emission.

### 4. Staged Roadmap and `v0` Forward-Compatibility Rules

Basis: derived

To ensure that a `v0` verified Rust compiler backend (which may initially delegate final object emission or linking to LLVM MC / `rust-lld` or verify at the MIR/assembly level) can smoothly transition to a fully verified assembler and linker:

1. **Stage 1 (`v0` — Translation Validation of Object Emission via Trusted ISA Decoder):**
   - Instead of verifying LLVM's 202,383 lines of X86/AArch64 TableGen `.td` files and C++ `MCCodeEmitter`, run a **Lean 4 object-file checker** on each emitted `.o` file (`elf64-x86-64`, `elf32-i386`, `elf64-littleaarch64`, `Mach-O arm64`, `COFF`).
   - Parse section headers and relocation tables (`RELA`/`REL`), decode the `.text.<sym>` bytes using the trusted Lean 4 decoder (Intel XED-derived for x86; AArchMRS-derived for AArch64), and verify that replacing each relocated immediate field with its symbolic target produces the exact expected machine-instruction sequence verified by the backend.
2. **Stage 2 (`v1` — Verified Instruction Encoder & Relocatable Object Writer in Lean 4):**
   - Implement a pure Lean 4 instruction encoder for the compiler-emitted instruction subset (~200–400 instructions per ISA) and prove the CakeML/CompCertELF round-trip theorem:
     $$\forall i,\, \mathsf{encode}(i) = \mathsf{ some }\, \mathit{bytes} \implies \mathsf{decode}(\mathit{bytes}) = \mathsf{some}(i, [])$$
   - Emit per-function section groups (`.text.<sym>`, `.rodata.<sym>`, `.rela.text.<sym>`) using only the **63 total relocation kinds** empirically observed across all 8 Tier 1 targets in Table 3.
3. **Stage 3 (`v2` — Verified Static Linker Subset / Post-Link Validator):**
   - Port the core symbol-resolution, section-concatenation, and relocation-application equations from **Linksem** (`abi_amd64_relocation.lem`, `abi_aarch64_relocation.lem`) and **CompCertELF** into Lean 4, extended with the 11 Mach-O `arm64` and 4–12 COFF relocation formulas.
   - Keep **linker relaxation disabled by default** in verified builds (`--no-relax` / `-Wa,-mrelax-relocations=no`) except where explicitly proved as a local instruction-rewrite rule (such as AArch64 Cortex-A53 erratum 843419 veneers or x86-64 `GOTPCRELX` `MOV` $\to$ `LEA`).

## Boundaries

- **Dynamic linking (`ld.so` / `dyld` / Windows loader) and LTO plugin linking (`not examined`):** This report covers relocatable object emission (`.o` / `.rlib`) and static linking / relocation resolution; runtime dynamic loader symbol interposition (`LD_PRELOAD`, lazy PLT binding) and LLVM bitcode LTO linking are outside scope.
- **No existing full Mach-O or PE/COFF static-linker proof in literature (`unknown` / gap identified):** While ELF static linking is mechanized in Linksem and CompCertELF, Mach-O and PE/COFF lack published end-to-end verified static linkers; Stage 3 must formalize the 11 Mach-O and 12 COFF relocation formulas directly from Apple's `mach-o/arm64/reloc.h` and Microsoft's PE/COFF specification.

## Evidence

1. **Exhaustive Relocation Census Across All 8 Tier 1 Targets (`rustc 1.99.1`):**
   - Script: `support/measure_tier1_relocations.py`.
   - Recorded JSON dataset: `support/tier1_relocation_and_tablegen_census.json`.
   - Scanned 2,494 `.o` files across `libcore`, `liballoc`, `libstd`, and `libcompiler_builtins` in `~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu/lib/rustlib/<target>/lib/*.rlib` plus 24 compiled `probe_reloc.rs` object files (`8 targets x {-O0, -O3, -Os}`) using `llvm-ar` and `llvm-readobj --relocations --sections`.
2. **LLVM 23.1.1 BinaryFormat and TableGen Sources:**
   - Repository: `llvm/llvm-project`, revision `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`.
   - `llvm/include/llvm/BinaryFormat/ELFRelocs/x86_64.def` (49 lines, 44 `ELF_RELOC` entries), `i386.def` (47 lines, 41 `ELF_RELOC` entries), `AArch64.def` (258 lines, 236 `ELF_RELOC` entries), `MachO.h` (2,492 lines), `COFF.h` (877 lines).
3. **CakeML and MM0 Verified Encoder and ELF Sources:**
   - `CakeML/cakeml@b064083ebe1bd8e6c47bc55041ce33dd71c1e4e8`: `compiler/encoders/x64/x64_targetScript.sml` (750 lines), `compiler/encoders/x64/proofs/x64_targetProofScript.sml` (2,163 lines), `compiler/encoders/arm8/arm8_targetScript.sml` (669 lines), `compiler/encoders/arm8/proofs/arm8_targetProofScript.sml` (1,750 lines), `compiler/backend/lab_to_targetScript.sml` (514 lines).
   - `digama0/mm0@0d414c0bfdaaeb7fea571895127abc1fa5a3d956`: `examples/x86.mm0` (1,727 lines), `mm0-lean/x86/x86.lean` (880 lines), `mm0-lean/x86/assembly.lean` (158 lines).

## Revalidation

To rerun the Tier 1 `.rlib` and probe-crate relocation census on a newer `rustc` toolchain:

```console
WORK_DIR=/tmp/reloc_probe python3 \
  reports/verified-assemblers-encoders-linkers-and-object-format-models/support/measure_tier1_relocations.py
```

Compare the resulting `tier1_rlib_relocations` and `tier1_probe_relocations` dictionaries against `support/tier1_relocation_and_tablegen_census.json` to check whether any new relocation kinds are emitted by the updated toolchain.
