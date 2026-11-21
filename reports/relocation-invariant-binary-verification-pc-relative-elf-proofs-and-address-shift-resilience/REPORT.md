# Relocation-Invariant Binary Verification: PC-Relative ELF Proofs and Address-Shift Resilience

## Summary

Machine-code and assembly proofs keyed to concrete virtual addresses (hardcoded `PC` literals or post-link symbol constants) shatter globally whenever an unrelated edit inserts or deletes even one 4-byte instruction and shifts downstream functions, tables, or trap handlers. Relocation-resilient binary verification rests on four composable invariants:

1. **Base-Address-Parameterized Code Predicates**: Quantify machine-code separation-logic specs over an abstract section/module base `base : bv XLEN` (CakeML `semantics_compile`, bedrock2 `functions base finfo impls`, Islaris offset-parametric `instr_pre`), expressing internal targets as `(base + offset)`.
2. **Rigid-Shift Covariance of PC-Relative Semantics**: RISC-V `AUIPC + ADDI/LOAD/STORE` and `JAL`/`Bcc`, plus x86-64 `RIP`-relative addressing, are invariant under simultaneous byte shifts `(P + δ, S + δ)` across exact bitvector windows (`Δ ∈ [-0x80000800, +0x7ffff7ff]` for RV64 `AUIPC+I/S`, which is **asymmetric** and excludes `+0x7ffff800` despite fitting `int32_t`). Conversely, AArch64 `ADRP + ADD` clears `PC[11:0]` and is invariant **only** under page-aligned shifts (`δ ≡ 0 mod 4096`) unless relocations are re-evaluated.
3. **Two-Step Indirect ELF Relocation Resolution**: On RISC-V, `R_RISCV_PCREL_LO12_I` (24) and `R_RISCV_PCREL_LO12_S` (25) carry `r_addend = 0` and reference the *preceding `AUIPC` label* (`P_hi20`) rather than symbol `S`. Evaluating `LO12` relative to `P_lo12` causes an off-by-`±4096` page error when `(S + A - P_hi20) mod 4096` crosses `0x800` between the two instructions.
4. **Suppression or Accounting of Linker Relaxation (`R_RISCV_RELAX`)**: Size-shrinking relaxations (`AUIPC+JALR → JAL/C.J`, `R_RISCV_ALIGN` byte deletion) and `gp`/`x0` relaxations invalidate pre-link byte offsets and silently inject an unverified register precondition (`x3 == __global_pointer$`)—a privilege-escalation hazard for kernel trap vectors entered from U-mode. Sound proofs either suppress relaxation (`-mno-relax`, `-Wl,--no-relax`, `.option norelax`) or validate post-relaxation bytes against parameterized contracts.

## Applicability

This report applies to verification of bare-metal firmware, hypervisors, OS kernel trap handlers, and statically linked or position-independent executables (PIE) across **RV64GC/RV32GC**, **x86-64**, and **AArch64** ELF toolchains. The nine subjects in `REPORT.json` form a four-tier stack:

- **Normative ABI**: `riscv-non-isa/riscv-elf-psabi-doc` (`56561cb3e7330fe99a98fd27457229707b2786ae`) specifies ELF relocation formulas, `PCREL_HI20`/`LO12_*` indirection, and `R_RISCV_RELAX` rules.
- **Static Linkers**: `llvm/llvm-project` LLD (`25b1c803e1e1504f6dc11f7afd68e65ad3ee5964`) implements RISC-V relocation encoding and relaxation passes (`relaxCall`, `relaxHi20Lo12`, `relax`), while `rems-project/linksem` (`446412810661b91a39c86425c1e924e35661098c`, DOI `10.1145/2983990.2983996`) formalizes ELF static linking in Lem/Isabelle.
- **Verified Backends & Assemblers**: `CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`, DOI `10.1017/S0956796818000229`), `mit-plv/bedrock2` (`67b682a504041acd2cd678782ff2505983d7cd6f`, DOI `10.1145/3453483.3454065`), `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`), and `CompCertELF` (DOI `10.1145/3428265`) contrast symbolic assembler assumptions against verified object emission.
- **Binary & Translation Validators**: `rems-project/islaris` (`c978e10f50db5c40f0fdf113f5f76a779782c6f9`, DOI `10.1145/3519939.3523434`) verifies binaries against Sail ISA models (`pkvm_handler/wp.v`), whereas `seL4/graph-refine` (`33d94bbdd6448ada368d4d925935e8cfdf7d93b4`, DOI `10.1145/2491956.2462183`) validates concrete post-link ELFs.

Adjacent corpus packages cover `verified-assemblers-encoders-linkers-and-object-format-models`, `errata-aware-linkers-post-link-binary-validators-and-code-layout-relaxation`, `machine-code-verification-frameworks-and-assembly-contracts`, `post-link-executable-validator-relocations-veneers-erratum-843419-and-gcs`, and `object-files-linkers-loaders-and-separate-compilation-history`.

## Findings

### 1. Why Concrete-Address Binary Proofs Shatter Under +4 Byte Layout Edits

`Basis: source + derived`

Inserting one 4-byte instruction into `.text.boot` shifts downstream function and trap-handler virtual addresses by `+4` and breaks concrete-address binary proofs in five ways even without modifying downstream code:

1. **Literal PC Preconditions**: Specifications anchored to linked hex addresses (e.g., `instr_pre 0x0000000010300044` in `islaris/examples/binary_search_riscv64.v:181,262` or `objdump -t` addresses parsed by `seL4/graph-refine/objdump.py:13-43`) break on every internal branch, call return address, and jump table.
2. **Modular Alignment Breakage**: Direct `stvec`/`mtvec` trap vectors require 4-byte alignment (`base[1:0] = 00`), whereas AArch64 `VBAR_EL2` requires `2048`-byte alignment and Vectored/cache-aligned blocks require higher powers of two. Padding directives (`.align`) absorb shifts locally while altering distances between code before and after the directive.
3. **Asymmetric Cross-Section Drift**: When `.text` grows before `.rodata` (separated by alignment padding) or references fixed MMIO regions (`0x1000_0000`), intra-`.text` distances stay fixed while cross-section displacements change (`δ_S ≠ δ_P`).
4. **Low-12-Bit Carry Boundary & Page Masking**: Absolute `LUI+ADDI` fails under any data shift, and AArch64 `ADRP+ADD` fails whenever `(P mod 4096)` wraps across `0x1000`.
5. **Baked `.rodata` Pointers**: Post-link validators such as `seL4/graph-refine` (`objdump.py:46-97`) extract `.rodata` word tables (`target_objects.symbols`, `target_objects.sections`) into SMT constraints as concrete addresses, forcing full re-lifting and re-checking on every upstream size delta.

### 2. Base-Address-Parameterized Separation Logic Across Verification Frameworks

`Basis: documentation + source + derived`

Foundational machine-code proofs resist layout edits by quantifying over an abstract base address `base` (or symbolic relocation offset `δ`).

#### Myreen–Gordon Machine-Code Hoare Logic & CakeML (`lab_to_target`)

Myreen and Gordon (TACAS 2007, DOI `10.1007/978-3-540-71209-1_44`; Myreen POPL 2010, DOI `10.1145/1706299.1706313`) assert code ownership via `CODE_POOL instr_enc {(p + k, insn_k)}` parameterized by `p : word`. When branches use relative offsets `(target_off - cur_off)`, specifications are automatically covariant under shifts `p ↦ p + δ`.

`CakeML/cakeml` (`2874b664e10939a3ee462215b2e068c89c1f70eb`, DOI `10.1017/S0956796818000229`) scales this pattern across its verified backend:

- **Symbolic Start PC**: `targetSemScript.sml:55-115` fetches instructions via `bytes_in_memory pc (t.config.encode ...) ms.mem ms.mem_domain` for symbolic `pc = mc_conf.target.get_pc ms`.
- **Iterative Jump-Size Stabilization**: Because inserting code can push a jump past an immediate limit and widen its encoding—shifting subsequent labels—`lab_to_targetScript.sml:38-155` runs `enc_lines_again` iteratively until label positions stabilize (`ok = T`).
- **Base-Parametric Correctness**: `lab_to_targetProofScript.sml:11295-11351` (`Theorem semantics_compile`) proves behavioral refinement for *any* byte-aligned initial PC `mc_conf.target.get_pc ms` satisfying FFI table alignment (`L11306-11307`) and non-wraparound (`cbspace + LENGTH bytes + ffi_offset * (i + 3) < dimword (:'a)`, `L11314`).

#### bedrock2 (`FlatToRiscvFunctions`)

`mit-plv/bedrock2` (`67b682a504041acd2cd678782ff2505983d7cd6f`, DOI `10.1145/3453483.3454065`) compiles to RV32I/RV64I word streams (`ptsto_instr_compile4bytes`, `FlatToRiscvCommon.v:689-696`) using relative function offsets. `FlatToRiscvFunctions.v:99-115` (`Lemma functions_expose`) frames individual functions out of `functions base finfo impls` at `(Zmod.add base (bits.of_Z width pos))`:

```coq
iff1 (functions base finfo impls)
     (functions base finfo (map.remove impls f) *
      program iset (Zmod.add base (bits.of_Z width pos)) (compile_function finfo pos impl))%sep
```

Because `finfo : pos_map` records relative offsets from symbolic `base`, calls encode `(pos_callee - (pos_caller + off))` independently of `base`.

#### Islaris (`pkvm_handler/wp.v`)

`rems-project/islaris` (`c978e10f50db5c40f0fdf113f5f76a779782c6f9`, DOI `10.1145/3519939.3523434`) verifies binaries against Sail semantics in Iris/Coq. While `examples/binary_search_riscv64.v:124,181` pins concrete `0x10300044`, the Armv8-A pKVM exception-handler proof (`pkvm_handler/wp.v:270-301`) parameterizes specifications over symbolic `(stub_handler_addr offset : bv 64)`:

- `spec` asserts `0x77f8 ↦ₘ stub_handler_addr` alongside `instr_pre (bv_unsigned (bv_sub stub_handler_addr offset)) (stub_handler_spec param)` (`pkvm_handler/wp.v:292-295`).
- `theories/lifting.v:324-335` (`Lemma instr_pre_wand`) rewrites instruction preconditions modulo `bv_wrap 64`.

### 3. Bitvector Shift-Invariance Theorems and Exact Representability Windows

`Basis: normative + source + derived`

Let `sext_k(x)` be signed `k`-bit-to-64-bit extension and `u64(x) = x mod 2^64`. An addressing sequence at `P` targeting `S + A` is **rigidly shift-invariant** under `δ` iff `(P, S) ↦ (u64(P + δ), u64(S + δ))` preserves the encoded machine bits *and* still computes `u64(S + A + δ)`.

#### Exact RV64 `AUIPC + ADDI/LOAD/STORE` Arithmetic & Asymmetry Hazard

From `riscv-elf.adoc:1597-1599` and `lld/ELF/Arch/RISCV.cpp:615-640`:

```text
Δ    := sext_64(u64(S + A - P))
hi20 := ((Δ + 0x800) >> 12) mod 2^20
lo12 := sext_12(Δ mod 2^12)
```

`AUIPC` computes `u64(P + sext_32(hi20 << 12))` and `ADDI` adds `lo12`. Since `(S + A + δ) - (P + δ) ≡ S + A - P (mod 2^64)`, both `hi20` and `lo12` are invariant under arbitrary `δ` (including `+4`).

However, `lld/ELF/Arch/RISCV.cpp:616-617` applies `checkInt(ctx, loc, SignExtend64(val + 0x800, bits) >> 12, 20, rel)` to `Δ + 0x800`, not `Δ`. Because `hi20` spans `[-0x80000000, +0x7ffff000]` and `lo12` spans `[-0x800, +0x7ff]`, the exact valid displacement window is **asymmetric**:

```text
Δ ∈ [ -0x80000800, +0x7ffff7ff ]   =   [ -2^31 - 2048, +2^31 - 2049 ]
```

A proof checking `int32_t` (`-2^31 ≤ Δ ≤ 2^31 - 1`) accepts `Δ = +0x7ffff800`, where `Δ + 0x800 = +0x80000000` yields `hi20 = 0x80000`, `lo12 = -2048`, and RV64 sign-extension `sext_32(0x80000000) = -2^31`—landing at `P - 0x80000800`, off by **`-0x1_0000_0000` (`-4 GiB`)**! Conversely, `Δ = -0x80000800` lies outside `int32_t` yet evaluates accurately, while `-0x80000801` wraps by `+4 GiB`.

#### Cross-ISA Rigid-Shift Invariance Comparison (Without Re-Relocating)

| ISA & Sequence | Relocation Types | Exact Range | Rigid `+4B` Shift Invariant Without Re-Relocating? | Primary Source |
|---|---|---|---|---|
| **RV64 `AUIPC + I/S`** | `PCREL_HI20` + `PCREL_LO12_{I,S}` | `[-0x80000800, +0x7ffff7ff]` | **Yes** (`P + sext_32(hi20<<12) + sext_12(lo12)`) | `riscv-elf.adoc:1578-1603`, `RISCV.cpp:610-640` |
| **RISC-V `JAL`** | `R_RISCV_JAL` (17) | `[-2^20, +2^20 - 2]`, even | **Yes** (2B aligned) | `riscv-elf.adoc:1564-1565` |
| **RISC-V `Bcc`** | `R_RISCV_BRANCH` (16) | `[-4096, +4094]`, even | **Yes** (2B aligned) | `riscv-elf.adoc:1567-1568` |
| **x86-64 `RIP`-rel** | `R_X86_64_PC32` / `PLT32` | `[-2^31, +2^31 - 1]` | **Yes** (`P_insn + 4 + disp32`, `A = -4`) | SysV AMD64 ABI |
| **AArch64 `ADRP + ADD`** | `ADR_PREL_PG_HI21` + `ADD_ABS_LO12_NC` | `[-4 GiB, +4 GiB - 4 KiB]` pages | **No!** Clears `PC[11:0]`; breaks unless `δ ≡ 0 (mod 4096)` (fails by `0xff8` across page cross) | ARM64 ELF ABI + `verify_pcrel_reloc.py` |
| **RISC-V `LUI + ADDI`** | `R_RISCV_HI20` + `LO12_I` | `S + A ∈ [-0x80000800, +0x7ffff7ff]` | **No!** Breaks whenever `S` shifts (`δ_S ≠ 0`) | `riscv-elf.adoc:1376-1400` |
| **RISC-V `gp`-relaxed** | (Relaxed `HI20`/`PCREL`) | `|S + A - GP| ≤ 2047` | **No!** Requires `x3 == GP` and fixed `S - GP` | `riscv-elf.adoc:2492-2582`, `RISCV.cpp:1013-1033` |

Crucially, AArch64 `ADRP` masks `PC & ~0xfff` while `ADD` adds `S & 0xfff`. Rigidly copying relocated AArch64 bytes by `+8` across a 4 KiB boundary (`0x40000ff8 → 0x40001000`, `S: 0x40002000 → 0x40002008`) produces `0x40003000` instead of `0x40002008` (`+0xff8` error). RISC-V `AUIPC + ADDI` adds directly to full `P`, surviving sub-page shifts without re-relocating whenever code and target move together.

### 4. ELF Relocation Verification: Indirect `PCREL_LO12`, CompCert, CompCertELF, and Linksem

`Basis: normative + source + derived`

#### Indirect `R_RISCV_PCREL_LO12_{I,S}` Resolution

Per `riscv-elf.adoc:1183-1188, 1578-1620`, `R_RISCV_PCREL_HI20` (23) at `P_hi20` targets `(symbol, A)`, whereas `R_RISCV_PCREL_LO12_I` (24) and `R_RISCV_PCREL_LO12_S` (25) **must** set `r_addend == 0` and target the **same-section `AUIPC` label `P_hi20`**, allowing multiple non-adjacent loads/stores (`riscv-elf.adoc:1614-1620`) to share one `AUIPC` result. Both `HI20` and `LO12` compute `S + A - P_hi20` (`RISCV.cpp:509, 622-640`). A buggy applier evaluating `LO12` at `P_lo12 = P_hi20 + 8` errs by `4088` bytes (`4096 - 8`) whenever `(S + A - P_hi20) mod 4096 ∈ [0x800, 0x807]` (e.g., `S = P_hi20 + 0x802`).

#### CompCert, CompCertELF, and Linksem Comparison

- **CompCert (`AbsInt/CompCert`, `2685140bf72c959446981fb99b5e44a8975021bc`)**: `riscV/Asm.v:342-343, 546-548, 954-957` abstracts `Ploadsymbol`/`Ploadsymbol_high` behind `Genv.symbol_address` and `Axiom low_high_half: Val.offset_ptr (high_half ge id ofs) (low_half ge id ofs) = Genv.symbol_address ge id ofs`; `TargetPrinter.ml:504-508` emits `1: auipc rd, %pcrel_hi(...)` and trusts the external assembler/linker for `AUIPC` range checks and relocation emission.
- **CompCertELF (Wang et al., OOPSLA 2020, DOI `10.1145/3428265`)**: Closes the assembler/linker gap for x86-32 via a Coq verified assembler emitting ELF relocatable `.o` files and a syntactic-equivalence proof commuting symbol linking with ELF relocation patching.
- **Linksem (`rems-project/linksem`, `446412810661b91a39c86425c1e924e35661098c`, DOI `10.1145/2983990.2983996`)**: Formalizes ELF static linking in Lem/Isabelle (`src/link.lem:111-190`, `mark_fate_of_relocs`), classifying relocation sites into static patch, load-time `R_*_RELATIVE` emission, or overflow hazard (e.g., 32-bit PC-relative relocations in shared objects).

### 5. Linker Relaxation (`R_RISCV_RELAX`), `gp`-Anchoring Hazards, and Linker Divergence

`Basis: normative + source + derived`

RISC-V linker relaxation (`riscv-elf.adoc:2335-2936`, `lld/ELF/Arch/RISCV.cpp:932-1155`) mutates section sizes, deletes instructions, and alters ABI dependencies at link time:

1. **Code-Shrinking & Alignment Deletion (`relaxCall`, `R_RISCV_ALIGN`)**: `RISCV.cpp:933-961, 1067-1075` collapses 8-byte `auipc+jalr` into 4-byte `jal` (`±1 MiB`) or 2-byte `c.j`/`c.jal` (`±2 KiB`). `R_RISCV_ALIGN` deletes NOP padding bytes to restore alignment (`riscv-elf.adoc:1624-1682`, `RISCV.cpp:1050-1066`). Any pre-resolved intra-function jump without a relocation breaks (`riscv-elf.adoc:2349-2352`), and pre-link byte-step/size invariants no longer match the linked binary.
2. **Global-Pointer (`gp`/`x3`) Relaxation (`relaxHi20Lo12`)**: `riscv-elf.adoc:2492-2582` and `RISCV.cpp:1013-1033` delete `LUI`/`AUIPC` and rewrite `LO12` to `<off>(gp)` when `|S + A - GP| ≤ 2047` and `Tag_RISCV_x3_reg_usage ∈ {0, 1}`.
   - **Trap-Handler Soundness Hazard**: On trap entry (`stvec`/`mtvec`) from untrusted U-mode, `x3` holds user-controlled data, not `__global_pointer$`; any `gp`-relaxed instruction in a trap handler silently dereferences attacker-controlled `user_x3 + off`. Moreover, boot `gp` setup without `.option push; .option norelax` relaxes into `mv gp, gp` (`riscv-elf.adoc:2559-2574`).
3. **Zero-Page (`x0`) Relaxation**: `RISCV.cpp:995-1011, 642-650` folds addresses in `[-2048, +2047]` to `x0`-relative access (`riscv-elf.adoc:2657-2690`), breaking later PIE relocation away from `0`.
4. **Linker Divergence (`psABI`/GNU `ld` vs. `LLVM ld.lld`)**: `riscv-elf.adoc:2495-2496` includes `R_RISCV_PCREL_HI20` and `R_RISCV_PCREL_LO12_{I,S}` in `gp`-relaxation (performed by GNU BFD `ld`), whereas `lld/ELF/Arch/RISCV.cpp:1084-1089` dispatches only `R_RISCV_HI20`/`LO12_{I,S}` to `relaxHi20Lo12`.

| System | Verification Locus | Base Parameterization | Multi-Pass Length Changes? | Models ELF Relocs? | Fragility Under Upstream `+4B` Edit |
|---|---|---|---|---|---|
| **CakeML** | In-prover encoder | `mc_conf.target.get_pc ms` | Yes (`enc_lines_again`) | No (flat bytes) | Low (re-runs encoder; base-parametric) |
| **bedrock2** | In-prover compiler | `functions base finfo impls` | No (4B instructions) | No (`pos_map`) | Low (parametric in `base`) |
| **Islaris** | Lifted linked ELF | Optional (`stub_handler_addr - offset`) | N/A (post-link) | No | Low if offset-parametric; **high** if literal hex |
| **CompCert** | Abstract assembly | Symbolic `Genv.symbol_address` | External assembler | No (`low_high_half` axiom) | Low in Coq; unverified assembler/linker gap |
| **CompCertELF** | In-prover ELF `.o` | Section-relative + relocs | Fixed instruction size | Yes (x86-32 `.o`) | Low (relocations preserved) |
| **seL4 `graph-refine`** | Post-link ELF (`objdump`) | None (concrete hex addresses) | N/A (post-link) | No | **High** (re-lifts and re-proves all shifted addresses) |

**Prescriptive Rules**: Suppress relaxation on verified kernel/trap units (`-mno-relax`, `-Wl,--no-relax`, `.option norelax`), write separation-logic contracts parameterized by `(base : bv 64)` with alignment and `[-0x80000800, +0x7ffff7ff]` hypotheses, and isolate cross-section/MMIO pointers behind explicit interface tables rather than inline relocations.

## Boundaries

- **known not to apply**: Rigid sub-page byte shifts (`δ ≢ 0 mod 4096`) without re-applying ELF relocations are **known not to apply** to AArch64 `ADRP + ADD/LDR` (`PC[11:0]` masking causes up to `0xff8`-byte errors), RISC-V absolute `LUI + ADDI` or `gp`/`x0`-relaxed code, and cross-section references to fixed physical MMIO regions.
- **unsupported**: `llvm/llvm-project` LLD (`lld/ELF/Arch/RISCV.cpp:1084-1089` at `25b1c803e1e1504f6dc11f7afd68e65ad3ee5964`) leaves `gp`-relaxation of `R_RISCV_PCREL_HI20` / `R_RISCV_PCREL_LO12_{I,S}` **unsupported** (unlike GNU `ld`), and upstream `AbsInt/CompCert` (`2685140bf72c959446981fb99b5e44a8975021bc`) leaves binary ELF emission and linker relaxation **unsupported** inside Coq (`CompCertELF` targets x86-32 ELF `.o` files without RISC-V relaxation).
- **not examined**: Lazy PLT dynamic binding (`_dl_runtime_resolve`) under `LD_AUDIT` concurrency, Mach-O chained fixups / PE-COFF `.reloc` tables, and CHERI capability (`CapTable`/`PCC`) relocation proofs were **not examined**.
- **unknown**: Whether a mechanized proof of multi-pass RISC-V `R_RISCV_RELAX` convergence and semantic preservation holds for arbitrary ELF inputs—including `lld`'s pass-4 oscillation cutoff (`lld/ELF/Arch/RISCV.cpp:1069-1074`)—remains **unknown** from inspected sources and published literature as of `2026-11-20`.

## Evidence

### Primary Specifications, Papers, and Source Coordinates

| Subject | Exact Coordinate / Revision | Inspected Lines / Scope |
|---|---|---|
| **RISC-V ELF psABI** | `riscv-non-isa/riscv-elf-psabi-doc` @ `56561cb3e7330fe99a98fd27457229707b2786ae`, `riscv-elf.adoc` | L1169–1194, L1376–1400, L1521–1683 (`PCREL`, `ALIGN`), L2335–2690 (`Linker Relaxation`) |
| **LLVM LLD (RISC-V)** | `llvm/llvm-project` @ `25b1c803e1e1504f6dc11f7afd68e65ad3ee5964`, `lld/ELF/Arch/RISCV.cpp` | L609–640 (`SignExtend64(val+0x800, bits) >> 12`), L933–1033, L1035–1130 (`relax`) |
| **CakeML** | `CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`; DOI `10.1017/S0956796818000229` | `targetSemScript.sml:55-115`; `lab_to_targetScript.sml:38-155`; `lab_to_targetProofScript.sml:11295-11351` |
| **bedrock2** | `mit-plv/bedrock2` @ `67b682a504041acd2cd678782ff2505983d7cd6f`; DOI `10.1145/3453483.3454065` | `FlatToRiscvCommon.v:689-696`; `FlatToRiscvFunctions.v:99-115` (`functions_expose`) |
| **Islaris** | `rems-project/islaris` @ `c978e10f50db5c40f0fdf113f5f76a779782c6f9`; DOI `10.1145/3519939.3523434` | `pkvm_handler/wp.v:270-301`; `theories/lifting.v:324-335`; `examples/binary_search_riscv64.v:181,262` |
| **CompCert (RISC-V)** | `AbsInt/CompCert` @ `2685140bf72c959446981fb99b5e44a8975021bc` | `riscV/Asm.v:342-343, 546-548, 954-957`; `riscV/TargetPrinter.ml:504-508` |
| **CompCertELF** | Wang et al., PACMPL (OOPSLA 2020), DOI `10.1145/3428265` | Verified x86-32 ELF object emitter + linking commutation |
| **Linksem** | `rems-project/linksem` @ `446412810661b91a39c86425c1e924e35661098c`; DOI `10.1145/2983990.2983996` | `src/link.lem:111-190` (`mark_fate_of_relocs`) |
| **seL4 `graph-refine`** | `seL4/graph-refine` @ `33d94bbdd6448ada368d4d925935e8cfdf7d93b4`; DOI `10.1145/2491956.2462183` | `objdump.py:13-97` (`build_syms`, `build_rodata`) |
| **Machine Hoare Logic** | Myreen & Gordon, TACAS 2007 (`10.1007/978-3-540-71209-1_44`); Myreen, POPL 2010 (`10.1145/1706299.1706313`) | Parameterized `CODE_POOL` machine-code Hoare logic |

### Standalone Derived Bitvector Probe (`verify_pcrel_reloc.py`)

`Basis: derived` — executable Python 3 check of `riscv-elf.adoc:1597-1599`, `lld/ELF/Arch/RISCV.cpp:615-640`, and AArch64 `ADRP+ADD`:

```python
#!/usr/bin/env python3
MASK64, MASK32, MASK20, MASK12 = (1 << 64) - 1, (1 << 32) - 1, (1 << 20) - 1, (1 << 12) - 1

def sext(val: int, bits: int) -> int:
    val &= (1 << bits) - 1
    return val - (1 << bits) if (val & (1 << (bits - 1))) else val

def u64(x: int) -> int:
    return x & MASK64

def pcrel_hi20_lo12_eval(p_hi20: int, target: int, p_lo12: int | None = None):
    ref_lo = p_hi20 if p_lo12 is None else p_lo12
    hi20 = ((u64(target - p_hi20) + 0x800) >> 12) & MASK20
    lo12 = sext(u64(target - ref_lo) & MASK12, 12)
    auipc_val = u64(p_hi20 + sext((hi20 << 12) & MASK32, 32))
    return hi20, lo12, auipc_val, u64(auipc_val + lo12)

def aarch64_adrp_add_eval(p_adrp: int, target: int) -> int:
    imm21 = (((target & ~0xFFF) - (p_adrp & ~0xFFF)) >> 12) & ((1 << 21) - 1)
    return u64(u64((p_adrp & ~0xFFF) + sext(imm21 << 12, 33)) + (target & 0xFFF))

def main() -> None:
    deltas = [-0x80000800, -0x80000001, -0x80000000, -0x801, -0x800, -0x7FF, 0, 0x7FE, 0x7FF, 0x800, 0x801, 0x7FFFF7FF]
    pcs, shifts = [0x80000000, 0x80000800, 0xFFFFFFC000000004], [0, 4, 0xFFC, 0x1000, -4, 0x12345678]
    for p0 in pcs:
        for d in deltas:
            s0 = u64(p0 + d)
            hi0, lo0, _, v0 = pcrel_hi20_lo12_eval(p0, s0)
            assert v0 == s0
            for sh in shifts:
                hi1, lo1, _, v1 = pcrel_hi20_lo12_eval(u64(p0 + sh), u64(s0 + sh))
                assert v1 == u64(s0 + sh) and (hi1, lo1) == (hi0, lo0)
    print(f"PASS: RV64 AUIPC+ADDI shift covariance verified on {len(pcs) * len(deltas) * len(shifts)} cases")

    p_trap, d_bad = 0x80000000, 0x7FFFF800
    s_bad = u64(p_trap + d_bad)
    hi_bad, lo_bad, _, v_bad = pcrel_hi20_lo12_eval(p_trap, s_bad)
    err_bad = sext(u64(v_bad - s_bad), 64)
    print(f"BOUNDARY_FAIL: delta={d_bad:#x} (in s32={-2**31 <= d_bad < 2**31}) -> hi20={hi_bad:#x} lo12={lo_bad} err={err_bad:#x} ({err_bad})")
    assert err_bad == -0x100000000

    assert pcrel_hi20_lo12_eval(p_trap, u64(p_trap - 0x80000800))[3] == u64(p_trap - 0x80000800)
    err_min = sext(u64(pcrel_hi20_lo12_eval(p_trap, u64(p_trap - 0x80000801))[3] - u64(p_trap - 0x80000801)), 64)
    print(f"LOWER_BOUND: -0x80000800 valid=True; -0x80000801 err={err_min:#x} (+4 GiB)")
    assert err_min == 0x100000000

    p_hi, p_lo, s_carry = 0x80001000, 0x80001008, 0x80001802
    v_good, v_bug = pcrel_hi20_lo12_eval(p_hi, s_carry)[3], pcrel_hi20_lo12_eval(p_hi, s_carry, p_lo)[3]
    print(f"LO12_BUG: S=P_hi+0x802, P_lo=P_hi+8 -> good={v_good:#x}, buggy={v_bug:#x}, error={sext(u64(v_bug - v_good), 64)} bytes (4096 - 8)")
    assert sext(u64(v_bug - v_good), 64) == 4088

    p_a64, s_a64 = 0x40000FF8, 0x40002000
    assert aarch64_adrp_add_eval(p_a64, s_a64) == s_a64
    imm21 = ((s_a64 & ~0xFFF) - (p_a64 & ~0xFFF)) >> 12
    v_unreloc = (((p_a64 + 8) & ~0xFFF) + (imm21 << 12)) + (s_a64 & 0xFFF)
    print(f"AARCH64_SHIFT_BREAK: rigid +8B shift across page boundary without re-reloc -> got={v_unreloc:#x}, expected={s_a64 + 8:#x}, error={v_unreloc - (s_a64 + 8):#x}")
    assert v_unreloc - (s_a64 + 8) == 0xFF8

if __name__ == "__main__":
    main()
```

Observed output (`2026-11-20`, Python 3):

```text
PASS: RV64 AUIPC+ADDI shift covariance verified on 216 cases
BOUNDARY_FAIL: delta=0x7ffff800 (in s32=True) -> hi20=0x80000 lo12=-2048 err=-0x100000000 (-4294967296)
LOWER_BOUND: -0x80000800 valid=True; -0x80000801 err=0x100000000 (+4 GiB)
LO12_BUG: S=P_hi+0x802, P_lo=P_hi+8 -> good=0x80001802, buggy=0x800027fa, error=4088 bytes (4096 - 8)
AARCH64_SHIFT_BREAK: rigid +8B shift across page boundary without re-reloc -> got=0x40003000, expected=0x40002008, error=0xff8
```

## Revalidation

1. **Re-check ELF psABI Relocation & Relaxation Rules**:
   ```bash
   curl -fsSL https://raw.githubusercontent.com/riscv-non-isa/riscv-elf-psabi-doc/<NEW_SHA>/riscv-elf.adoc \
     | grep -n -E "R_RISCV_PCREL_HI20|R_RISCV_PCREL_LO12|gp-relax|__global_pointer\$"
   ```
2. **Re-check LLD RISC-V `relax()` Dispatch and `SignExtend64` Range Check**:
   ```bash
   curl -fsSL https://raw.githubusercontent.com/llvm/llvm-project/<NEW_SHA>/lld/ELF/Arch/RISCV.cpp \
     | sed -n '605,645p;1035,1125p'
   ```
3. **Re-check Upstream Verifier Parameterizations**: Inspect `semantics_compile` (`CakeML`), `functions_expose` (`bedrock2`), and `pkvm_handler/wp.v` (`Islaris`) for base/offset quantification.
4. **Re-run the Arithmetic Probe**: Save the `verify_pcrel_reloc.py` snippet from `## Evidence` to `/tmp/verify_pcrel_reloc.py` and run `python3 /tmp/verify_pcrel_reloc.py` (expect exit `0` and matching boundary outputs).
