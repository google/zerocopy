# Self-Attesting Inline-Assembly Operand Bindings, CGU Pure-Rust Containment, Cross-Crate `.rmeta` Monomorphization, and Post-Link Relaxation Soundness

## Summary

Verifying non-naked `core::arch::asm!` in an optimizing Rust library verifier without decompiling enclosing pure-Rust callers requires closing four architectural gaps between `Runtime(PostCleanup)` MIR, LLVM's `MCStreamer` codegen pipeline, cross-crate `.rmeta` monomorphization, and ELF static linking:

1. **Self-Attesting Operand-Register Bindings Close the Span-Only Register-Swap Soundness Hole:**
   - Recording only `(start_pc, end_pc, site_id)` in an `SHF_EXCLUDE` metadata section (`.anneal.asm_sites`) and verifying $\exists \sigma \in \text{ValidAlloc},\ \text{bytes} = \text{encode}(\text{template}, \sigma)$ is **unsound** (`existential_alloc_unsound_counterexample` in [`support/VerifiedSelfAttestingAsm.lean`](support/VerifiedSelfAttestingAsm.lean)): for `"sub {0}, {1}"` (`inout(reg) a, in(reg) b`), a swapped machine encoding `48 29 c6` (`sub rsi, rax` when LLVM allocated `{0 -> rax, 1 -> rsi}`) satisfies $\exists \sigma$ under `{0 -> rsi, 1 -> rax}`, clobbering caller-live `rsi` and leaving `rax` un-updated.
   - Because LLVM's `EmitInlineAsmStr` (`llvm/lib/CodeGen/AsmPrinter/AsmPrinterInlineAsm.cpp:140-334`) expands `$0`, `${0:q}`, `${1:c}`, `${2:l}`, and `${:uid}` character-by-character across the *entire* inline-asm string—including inside `.asciz "..."` directives—*after* register allocation, inlining, loop unrolling, and tail duplication, emitting a split two-section `SHF_EXCLUDE` table (`.anneal.asm_sites` fixed 8-byte-aligned records + `.anneal.asm_descs` byte-counted `.asciz` descriptors + typed `.quad` relocations for `sym` and `asm_goto` `label` operands) pairs every emitted `[start_pc, end_pc)` machine slice 1-to-1 with LLVM's exact physical register map $\sigma_i$, monomorphized `sym` symbol, and resolved `callbr` target PC (`je +10` $\to$ `.text.goto_caller_u32 + 0x18`), eliminating caller decompilation.
   - **Spoof Resistance:** Interpolating `sym` names textually into `.asciz` fails closed or breaks framing when `#[export_name = "evil\"|0=rax\n.popsection\n#"]` injects quotes/delimiters, whereas typed `.quad {sym}` and `.quad {lbl}` slots bind directly via `SHT_RELA` symbol indices. Fixed numeric boundary labels (`9996:`/`9997:`) are spoofable if user assembly redefines `9996:` mid-block (hiding `10 B` of rogue `mov qword ptr [rdi], 0xdead` prefix instructions from `[9996b, 9997b)`), whereas compiler-injected `.L__anneal_s_<NONCE>_${:uid}:` / `.L__anneal_e_<NONCE>_${:uid}:` labels combine a fresh per-compilation 128-bit nonce with `AsmPrinter::PrintSpecial` `${:uid}` (`AsmPrinterInlineAsm.cpp:439-450`) and `rustc`'s user `$` $\to$ `$$` escaping (`compiler/rustc_codegen_llvm/src/asm.rs:189-200`) to capture all `10 B` across `4×`-unrolled iterations (`uid=0..3`).

2. **`TargetInstrInfo::getInlineAsmLength` Codegen-Invariance Split (`x86_64` vs. `aarch64`):**
   - On **`x86_64`**, even a 10-line `.pushsection` wrapper produces **100% bit-for-bit SHA-256 identical `.text.*` sections** across `rel8` jump boundaries (`127 B`), inlining thresholds, and `16×` loop unrolling on both `rustc 1.99.1` and `1.102.0-nightly`, because: (i) `X86InstrInfo` omits `getInstSizeInBytes` (`X86InstrInfo.cpp:10591`) and resolves `rel8`/`rel32` jumps in `MCAssembler::layout` over real `.text` fragments; (ii) `InlineCost.cpp:145-147, 798-834` defaults `InlineAsmInstrCost` to `0` and skips `.pushsection`..`.popsection`, `.` directives, and `:` labels; and (iii) `CodeMetrics.cpp:166` counts `call asm` as 1 IR instruction.
   - On **`aarch64`** (and targets running `BranchRelaxation`), `AArch64InstrInfo::getInstSizeInBytes` (`AArch64InstrInfo.cpp:187-189`) calls `TargetInstrInfo::getInlineAsmLength` (`TargetInstrInfo.cpp:113-149`), which counts **every `\n`- or `;`-separated statement** (except `.space <int>`) as `MaxInstLength` (`4 B`), inflating a 9-statement wrapper to `36 B` (`9×`) and prematurely relaxing `tbz w0, #0, +0x12c4` into `tbnz + b` (`+4 B` `.text` drift) across `1,200` `asm!` sites (`4,800 B` actual $\ll 32\text{ KiB}$). A **zero-`;`, zero-`\n` per-site CGU wrapper macro** (`__aw <id>, {0}`)—or direct C++ `OutStreamer` emission in `AsmPrinter::emitInlineAsm`—restores exact `1 × 4 B` length and **100% bit-for-bit `.text` SHA-256 parity** even across `5,000` `asm!` sites (`20,092 B`, `5,000` attested records).

3. **Pure-Rust CGU Sibling Containment Across Three LLVM Streamer Modes (`MCObjectStreamer` vs. `MCAsmStreamer`):**
   - Under `-C codegen-units=1`, LLVM exhibits a **three-mode split** on `.macro` mnemonic hijacking of pure-Rust sibling functions (which contain zero `asm!`): (i) default `MCObjectStreamer` (`--emit=obj`) emits pure-Rust `MCInst`s directly without invoking `MCAsmParser::lookupMacro` (`pure_xor(10, 3) == 9`); (ii) default `MCAsmStreamer` (`--emit=asm`, `useIntegratedAssembler() == true`) still runs `MCAsmParser` on `asm!`/`global_asm!` (`AsmPrinterInlineAsm.cpp:90-137`), absorbing `.macro` into `MCContext::MacroMap` without writing it to `.s` (`pure_xor(10, 3) == 9`), while forwarding `.code16`/`.code32` via `emitAssemblerFlag` into `.s` and breaking subsequent 64-bit pure-Rust functions; and (iii) `-C llvm-args=-no-integrated-as` emits raw `.macro xorq` text into `.s`, **hijacking pure-Rust `10 ^ 3` into `10 - 3 == 7`**.
   - Critically, **even default `MCObjectStreamer` (`rustc -O -C codegen-units=1`) fails to isolate pure-Rust sibling functions from five assembly attacks in the same CGU:** (a) an uncalled `asm!(".weak a_pure_rust_auth")` emitted after a safe pure-Rust function downgrades its ELF binding from `STB_GLOBAL` to `STB_WEAK` (`MCELFStreamer.cpp:180-187`), allowing an external archive/C function to silently override it (`1` $\to$ `999`); (b) an uncalled `asm!(".type a_pure_victim, @gnu_indirect_function")` promotes a safe pure-Rust function from `STT_FUNC` (`2`) to `STT_GNU_IFUNC` (`10`) via `CombineSymbolTypes` (`MCELFStreamer.cpp:115-125, 201-204`) with **zero warnings**, executing it as a startup/call resolver (`7777`); (c) `.symver` aliases arbitrary symbols across sections; (d) `global_asm!(".cfi_sections .debug_frame")` strips `.eh_frame` CGU-wide, causing `std::panic::catch_unwind` in pure-Rust code to abort with `SIGABRT` (`_URC_END_OF_STACK = 5`); and (e) **trailing bare x86 prefix bytes** at the end of an inlined `asm!`—even when followed by `.pushsection .anneal.asm_sites ... .popsection`—append directly to the `.text` `MCFragment` ahead of LLVM's next pure-Rust `MCInst`: `.byte 0x66` desynchronizes `movl $0x12345678, %eax` (`b8 78 56 34 12`) into `movw $0x5678, %ax; xorb $0x12, %al` (`0x...566a`), `.byte 0x41` (`REX.B`) redirects `%eax` to `%r8d` leaving `%eax` uninitialized, `.byte 0xf0` (`LOCK`) triggers `SIGILL` (`#UD`) on pure-Rust `leaq`, and `.byte 0x64` (`FS:`) turns a safe reference read `*p` into `movq %fs:(%rdi), %rax`.

4. **Cross-Crate `.rlib`/`.rmeta` Deferred Monomorphization, Post-Link Relaxations, and Lean `v4.34.1` Soundness:**
   - Building an upstream `--crate-type=rlib` at `-C opt-level=3` emits `.o` machine bytes inside `libupstream.rlib` **only** for `#[inline(never)]` functions: generic `asm!` functions, `#[inline]`/`#[inline(always)]` functions, **and even unannotated non-generic `pub fn`s** (marked `cross_crate_inlinable` by `rustc`, `encoder.rs:1116-1120`) emit **zero `.o` bytes** in `libupstream.rlib` and lower from `lib.rmeta` inside downstream CGUs—where a downstream crate's `global_asm!(".macro sub ...")` **silently rewrites all four upstream `sub` functions (`20 - 5 == 15`) into `add` (`25`)**! Because self-attesting `.anneal.asm_sites` templates travel inside `lib.rmeta`, verifying `.anneal.asm_sites` on downstream CGU `.o` files catches `4/4` hijacked instantiations (`0x01` `ADD` vs. `0x29` `SUB`).
   - Between `.o` verification and the final executable, three post-link behaviors govern `options(preserves_flags)` and register clobbers: (a) `rustc` defaults to `-Z relax-elf-relocations=no`, emitting `R_X86_64_GOTPCREL` (`9`) inside `asm!`—which GNU `ld.bfd 2.47` relaxes to `leaq` while `rust-lld` keeps `movq` unless `-Z relax-elf-relocations=yes` emits `R_X86_64_REX_GOTPCRELX` (`42`, relaxed to `leaq` by both linkers, preserving `EFLAGS`); (b) **both `rust-lld` and `ld.bfd 2.47` unconditionally relax `R_X86_64_GOTTPOFF` (`IE -> LE`) even under `-Wl,--no-relax`**, preserving `ZF=1` on `%rax` (`leaq -8(%rax), %rax`) while clobbering `ZF=1 -> 0` on `%r12` (`addq $-8, %r12`); and (c) linking the **identical** `a64_thunk.o` (`sha256=95165eb4c0777329`) with `rust-lld` at `<128 MiB` vs. `>128 MiB` (`0x200000` $\to$ `0x10000000`) and executing under `qemu-aarch64` preserves live caller `x16 = 0x1122334455667788` (`rc=0`) when near, yet **silently overwrites `x16 = 0x0000000010000000` (`rc=42`)** via `__AArch64AbsLongThunk_*` when far unless `out("x16") _, out("x17") _` are declared or post-link `|S + A - P| < 128 MiB` is verified.
   - [`support/VerifiedSelfAttestingAsm.lean`](support/VerifiedSelfAttestingAsm.lean) mechanizes `SiteAttestation`, complete-slice prefix-bleed rejection, `RelocRelaxEnvelope`, and end-to-end post-link refinement + register/flag/stack/memory frame soundness in `567` lines of `Init.*`-only Lean `v4.34.1` (`6` theorems, `0` `sorry`, `1.55 s`, `[propext]` only).

## Applicability

This report applies to formal verification, binary translation validation, and compiler instrumentation of Rust `core::arch::asm!` and `core::arch::global_asm!` across the durable upstream subjects in `REPORT.json`, evaluated on `x86_64-unknown-linux-gnu` (`Debian rodete`) with cross-compilation and user-mode execution targeting `aarch64-unknown-linux-gnu`:

| Subject | Repository / Package | Pinned Revision / Version | Role in This Investigation |
| :--- | :--- | :--- | :--- |
| **`rustc` (stable)** | `rust-lang/rust` | `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`, `2026-10-13`) | Source inspection (`asm.rs`, `rmeta/encoder.rs`, `collector.rs`), `x86_64` + `aarch64` execution across all probe suites. |
| **`rustc` (nightly)** | `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`, `2026-11-11`) | Execution parity + unstable `#![feature(asm_const_ptr)]` and `-Z relax-elf-relocations=yes` verification. |
| **LLVM & `rust-lld`** | `rust-lang/llvm-project` | `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`23.1.1`) & `0a5579eb649d3634a9c30ac873300cc2944fa070` (`23.1.5`) | Primary source inspection (`AsmPrinterInlineAsm.cpp`, `TargetInstrInfo.cpp`, `InlineCost.cpp`, `X86InstrInfo.cpp`, `AArch64InstrInfo.cpp`, `MCObjectStreamer.cpp`, `MCELFStreamer.cpp`, `lld/ELF/{Arch/X86_64,Thunks}.cpp`) and live linking. |
| **Lean 4** | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Kernel-checked proof of `SiteAttestation` + `RelocRelaxEnvelope` soundness (`support/VerifiedSelfAttestingAsm.lean`). |
| **GNU Binutils** | `GNU Binutils for Debian` | `2.47` (`ld.bfd`, `readelf`) | Differential `ld.bfd` vs. `rust-lld` relaxation probes (`GOTPCREL`, `REX_GOTPCRELX`, `GOTTPOFF` with/without `--no-relax`). |
| **Clang / LLVM tools** | `Debian clang / llvm-tools` | `clang 19.1.7`, `llvm-mc` / `llvm-objdump 21.1.8` | LLVM IR `${:uid}` assembly, `MCAsmStreamer` `.s` assembly, and slice disassembly. |
| **QEMU user-mode** | `Debian qemu-user` | `qemu-aarch64 11.1.2` (`1:11.1.2+ds-2`) | Live execution of `<128 MiB` vs. `>128 MiB` `aarch64-unknown-linux-gnu` binaries demonstrating `x16` veneer clobber. |

### Shared vs. Version-Specific Behavior (`rustc 1.99.1` vs. `rustc 1.102.0-nightly`)
- **Identical across `1.99.1` and `1.102.0-nightly`:** `.anneal.asm_sites` / `.anneal.asm_descs` 1-to-1 operand-register/symbol/label binding across inlining, `4×` loop unrolling, and tail cloning; spoof matrix verdicts (`sym` quote breakout in `.asciz`, `.quad` immunity, numeric `9996:` `10 B` prefix hiding, `<NONCE>` + `${:uid}` defense); `100%` bit-for-bit `x86_64` `.text` SHA-256 invariance (`true_rel8`, `inline_caller`, `unroll_16`); all 12 CGU pure-Rust containment outcomes (`MCObjectStreamer` vs. `MCAsmStreamer`, `.weak`, `@gnu_indirect_function`, `.symver`, `.cfi_sections`, unbalanced `.section`, and `.byte 0x66`/`0x41`/`0xf0`/`0x64` prefix bleeds); cross-crate `.rlib`/`.rmeta` deferred codegen (`25, 25, 25, 25, 15`); and default `R_X86_64_GOTPCREL` (`9`) + `GOTTPOFF` `%rax`/`%r12` relaxation results.
- **Version-specific differences:** (1) `#![feature(asm_const_ptr)]` (`const (&CONST_PTR_TARGET).wrapping_add(4)` $\to$ `const_ptr=CONST_PTR_TARGET+4`) and `-Z relax-elf-relocations=yes` (`R_X86_64_GOTPCREL` `9` $\to$ `R_X86_64_REX_GOTPCRELX` `42`) require nightly (`1.102.0-nightly`); and (2) inside `all_reg_classes`, LLVM `23.1.1` (`1.99.1`) allocated `(xmm2, ymm1, zmm0)` whereas LLVM `23.1.5` (`1.102.0-nightly`) allocated `(xmm0, ymm2, zmm1)`—which the self-attesting `.anneal.asm_descs` record tracked automatically (`x=xmm2|y=ymm1|z=zmm0` vs. `x=xmm0|y=ymm2|z=zmm1`) without changing any verification rule.

### Relation to Adjacent Corpus Reports
This report advances directly beyond:
- `hermetic-ffi-build-graph-binding-linker-attestation-and-inlined-asm-tracking` (which introduced span-only `(start_pc, end_pc, site_id)` `.anneal.asm_sites` records paired with existential $\exists \sigma$ matching, leaving open the register-swap soundness hole, `getInlineAsmLength` perturbation, cross-crate `.rmeta` `asm!`, and spoof resistance);
- `rust-asm-goto-labels-sym-const-and-assembler-directive-hazards` (which tested `asm!`-to-`asm!` `.macro` hijacking, leaving open whether `asm!`/`global_asm!` can corrupt **pure-Rust** sibling functions under `MCObjectStreamer` vs. `MCAsmStreamer`);
- `gotpcrelx-tlsdesc-linker-relaxations-ifunc-ordering-and-linksem-slack` and `post-link-executable-validator-relocations-veneers-erratum-843419-and-gcs` (extending their C/linker relaxation analyses to non-naked Rust `asm!` `options(preserves_flags)` and live `qemu-aarch64` caller-register corruption across `>128 MiB` veneers); and
- `rustc-cross-crate-rmeta-provenance-and-foreign-mir-inlining` (extending `.rmeta` MIR provenance to cross-crate `asm!` monomorphization and downstream CGU `.macro` hijacking).

## Findings

### 1. Self-Attesting Operand-Register Bindings (`SiteAttestation`) and Unforgeable Framing

`Basis: source + execution + derived` (`rust-lang/llvm-project@1b9c0d5ff9`: `llvm/lib/CodeGen/AsmPrinter/AsmPrinterInlineAsm.cpp:140-334, 432-463`, `llvm/lib/Target/X86/X86AsmPrinter.cpp:757-864`, `llvm/lib/MC/MCAsmInfo.cpp:79-98`; `rust-lang/rust@58cf8f9c35`: `compiler/rustc_codegen_llvm/src/asm.rs:183-255`; [`support/probe_self_attesting_and_invariance.py`](support/probe_self_attesting_and_invariance.py), [`support/probe_1_2_results.json`](support/probe_1_2_results.json))

#### 1.1 Why Span-Only `.anneal.asm_sites` + Existential $\exists \sigma$ Matching Is Unsound

Suppose a verified MIR function executes `asm!("sub {0:r}, {1:r}", inout(reg) a, in(reg) b, options(pure, nomem, nostack))` with proved specification $a' = a - b$. If `.anneal.asm_sites` records only `(start_pc, end_pc, site_id)`, the object-level verifier knows the emitted bytes `[start_pc, end_pc)` (`48 29 c6` = `sub rsi, rax`) but does **not** know whether LLVM's register allocator assigned `(0 -> rax, 1 -> rsi)` or `(0 -> rsi, 1 -> rax)`. Because `{0 -> rsi, 1 -> rax}` is a legal distinct `reg` assignment, existential matching ($\exists \sigma \in \text{ValidAlloc},\ \text{encode}(\text{tmpl}, \sigma) = \text{slice}$) **falsely accepts** `swapped_sub_bug` (`site_id = 102` in `support/probe_1_2_results.json`), even though `0 -> rax, 1 -> rsi` was allocated—leaving `a` (`rax`) unchanged and corrupting `rsi`! Similarly, for a 1-operand instruction `"neg {0:r}"`, `neg rcx` passes $\exists \sigma$ even when `{0}` was allocated to `rax`, clobbering caller-live `rcx`.

#### 1.2 Mechanism: `EmitInlineAsmStr` Expansion Inside Split `SHF_EXCLUDE` Sections

In `llvm/lib/CodeGen/AsmPrinter/AsmPrinterInlineAsm.cpp:140-334, 368`, `AsmPrinter::emitInlineAsm(const MachineInstr *MI)` formats the *entire* `INLINEASM` / `INLINEASM_BR` template string through `EmitInlineAsmStr` into an in-memory `SmallString<256>` **before** constructing `MCAsmParser` (`lines 108-136`). `EmitInlineAsmStr` scans for `$` placeholders without lexing quotes, comments, or section directives, dispatching `${N:<mod>}` to `PrintAsmOperand` (`X86AsmPrinter.cpp:757-864`), `MO_MBB` / `MO_BlockAddress` (`callbr` labels) to `Sym->print(OS, MAI)` (`lines 304-312`), and `${:uid}` to `AsmPrinter::PrintSpecial` (`lines 439-450`), which increments `Counter` monotonically per `(MI, getFunctionNumber())` instance.

Consequently, wrapping each lowered `InlineAsm` in two `SHF_EXCLUDE` (`0x80000000`, `"e"`) sections cleanly separates fixed-alignment relocation records from variable-length register descriptors:

```asm
.L__anneal_s_<NONCE>_${:uid}:
    <lowered_asm_body>
.L__anneal_e_<NONCE>_${:uid}:
.pushsection .anneal.asm_descs,"e",@progbits
.L__anneal_d_<NONCE>_${:uid}:
    .asciz "<NONCE>|uid=${:uid}|0=${0:q}|1=${1:q}|..."
.L__anneal_de_<NONCE>_${:uid}:
.popsection
.pushsection .anneal.asm_sites,"e",@progbits
    .quad .L__anneal_s_<NONCE>_${:uid}
    .quad .L__anneal_e_<NONCE>_${:uid}
    .quad <site_id>
    .quad .L__anneal_d_<NONCE>_${:uid}
    .quad .L__anneal_de_<NONCE>_${:uid} - .L__anneal_d_<NONCE>_${:uid}
    .quad <num_reloc_targets>
    /* followed by <num_reloc_targets> .quad entries for every `sym` and `label` operand */
.popsection
```

Live execution at `-C opt-level=3 -C codegen-units=1` across `rustc 1.99.1` and `1.102.0-nightly` (`support/probe_1_2_results.json`) establishes **100% 1-to-1 self-attestation** across every optimization and operand class:

| Scenario (`-C opt-level=3`) | Section & `[start..end)` | Emitted `.text` Bytes & Disassembly | Self-Attested `.anneal.asm_descs` + `.rela.anneal.asm_sites` Targets | Verifier Verdict |
| :--- | :--- | :--- | :--- | :---: |
| **Simple caller** (`site=101`) | `.text.caller_simple[0x3..0x6]` | `48 29 f0` (`sub rax, rsi`) | `0=rax\|1=rsi` | **PASS** |
| **High-pressure caller, copy 1** (`site=101`) | `.text.caller_pressure[0xf..0x12]` | `48 29 d1` (`sub rcx, rdx`) | `0=rcx\|1=rdx` | **PASS** |
| **High-pressure caller, copy 2** (`site=101`) | `.text.caller_pressure[0x1d..0x20]` | `48 29 f2` (`sub rdx, rsi`) | `0=rdx\|1=rsi` | **PASS** |
| **Swapped-operand bug** (`site=102`) | `.text.swapped_sub_bug[0x3..0x6]` | `48 29 c6` (`sub rsi, rax`) | `0=rax\|1=rsi` (expects `sub rax, rsi` = `48 29 f0`!) | **REJECT** (caught!) |
| **CFG tail duplication** (`site=101`, 2 branches) | `.text.tail_cloned[0x7..0xa]` & `[0xb..0xe]` | `48 29 d0` (`sub rax, rdx`), `48 29 c8` (`sub rax, rcx`) | Branch 0: `0=rax\|1=rdx`; Branch 1: `0=rax\|1=rcx` | **PASS** (`2/2`) |
| **4× loop unrolling** (`#[inline(never)]`, `site=101`) | `.text.unrolled_4x` (`0xa`, `0xd`, `0x14`, `0x1b`) | `48 29 c8`, `48 29 d0`, `48 29 c8`, `48 29 c8` | Iters 0..3: `0=rax\|1=rcx`, `0=rax\|1=rdx`, `0=rax\|1=rcx`, `0=rax\|1=rcx` | **PASS** (`4/4`) |
| **`asm_goto` `callbr` + generic `sym` + `const`** (`site=201`, 2 callers) | `.text.goto_caller_u32[0x8..0x15]` (`13 B`) | `48 83 f9 07` (`cmp rcx, 7`); `74 0a` (`je +10` $\to$ `0xe + 0xa = 0x18`); `48 8d 0d 00 00 00 00` | `0=rcx\|imm=7\|lbl_txt=.LBB5_2`, `.quad` targets: `[generic_callee::<u32>+0x0, .text.goto_caller_u32+0x18]` (**exact `0x18` match!**) | **PASS** (`2/2`) |
| **All register classes** (`site=301`, `reg_abcd :h`, `reg_byte`, `xmm`/`ymm`/`zmm`, `kreg`, fixed `r10`) | `.text.all_reg_classes` (`28 B`) | `mov ah, 127 ; add sil, 1 ; vpaddd ... ; kmovw k1, ecx ; add r10, 1` | `1.99.1`: `abcd_h=ah\|abcd_r=rax\|rb=sil\|x=xmm2\|y=ymm1\|z=zmm0\|k=k1\|explicit=r10` (`nightly`: `xmm0, ymm2, zmm1`) | **PASS** |
| **`asm_const_ptr` provenance offset** (`site=501`, `1.102.0-nightly`) | `.text.test_const_ptr_site[0x0..0x7]` (`7 B`) | `48 8d 05 00 00 00 00` (`lea rax, [rip + CONST_PTR_TARGET+4]`) | `0=rax\|const_ptr=CONST_PTR_TARGET+4` | **PASS** |

> **x86-64 `:h` + `reg_byte` encoding hazard discovered during probing:** Combining `{abcd:h}` (`reg_abcd`, allocated `ah`) with `{rb}` (`reg_byte`, allocated `sil`) in a *single* instruction (`mov {abcd:h}, {rb}`) fails at assembly time (`error: can't encode 'ah' in an instruction requiring EVEX/REX2/REX prefix: mov ah, sil`), because `sil`/`dil`/`bpl`/`spl`/`r8b`–`r15b` require a `REX` prefix that forbids legacy high-byte registers `ah`–`dh`.

#### 1.3 Adversarial Spoof Matrix and Unforgeable Framing Rules

Live testing of four spoof vectors across `1.99.1` and `1.102.0-nightly` (`support/probe_1_2_results.json`) establishes four mandatory framing invariants:

1. **Never interpolate `sym` names into `.asciz` — bind `sym` and `label` exclusively via `.quad` relocations:** Passing `#[export_name = "evil\"|0=rax\n.popsection\n#"]` via `sym` into `.asciz "0=rax|sym={s}"` causes `MCSymbol::print` (`MCAsmInfo.cpp:79-98`) to emit quoted text that breaks out of `.asciz` (`error: unexpected token`), and choosing `$` or `.` as delimiter allows unquoted `#[export_name = "foo$0=rsi"]` (`MCAsmInfo::isAcceptableChar` admits `$` and `.` at `line 83`!) to inject fake key-value pairs! Placing `{sym}` and `{lbl}` in `.quad` slots inside `.anneal.asm_sites` emits typed `R_X86_64_64` / `R_AARCH64_ABS64` relocations (`sym_quote_in_quad_reloc_preserved: true`) while restricting `.asciz` strictly to compiler-controlled register/integer tokens `[a-z0-9%-]+`.
2. **Replace fixed numeric labels (`9996:`) with `<NONCE>` + `${:uid}` local symbols:** In `numeric_label_spoof`, a user template containing `"mov qword ptr [{p:r}], 0xdead\n9996:\nsub {a:r}, {b:r}"` causes `9996b` to bind to the *inner* `9996:`, shrinking the attested slice to `[0xa..0xd]` (`sub rax, rdx`, `3 B`) and **hiding `10 B` (`mov rax, rsi; mov qword ptr [rdi], 0xdead`)** under `options(nomem)`! Wrapping with `.L__anneal_s_<NONCE>_${:uid}:` / `.L__anneal_e_<NONCE>_${:uid}:` (`9f4a2c81d70e3b56`, `uid=0..3`) cannot be guessed by user code, cannot be forged with `${:uid}` in Rust `asm!` (because `rustc` escapes every user `$` to `$$` at `asm.rs:189-200`, rejected as `asm template modifier must be a single character` or neutralized), and exposes **all `10 B` (`48c707adde00004829c8`) across all `4` unrolled iterations**.
3. **Always prepend `\n` before the end label and enforce section-stack balance:** A trailing `#` or `//` line comment on the last user line terminates cleanly at `\n`, whereas an unclosed `/*` block comment or rogue `.popsection` inside `<body>` fails closed in `MCAsmParser` (`error: unexpected token` / `error: .popsection without corresponding .pushsection`).
4. **Verify descriptor byte length via label subtraction (`.L__anneal_de - .L__anneal_d`) and check nonce prefix:** Computing `desc_len` in `.anneal.asm_sites` prevents interior NUL truncation, and checking `start_sec == end_sec && start_off <= end_off` catches any unbalanced `.section` escape.

---

### 2. `TargetInstrInfo::getInlineAsmLength` and `InlineCost` Codegen-Invariance

`Basis: source + execution` (`rust-lang/llvm-project@1b9c0d5ff9`: `llvm/lib/CodeGen/TargetInstrInfo.cpp:113-149`, `llvm/lib/Analysis/InlineCost.cpp:145-147, 798-834`, `llvm/lib/Analysis/CodeMetrics.cpp:164-168`, `llvm/lib/Target/X86/X86InstrInfo.cpp:10590-10597`, `llvm/lib/Target/AArch64/AArch64InstrInfo.cpp:179-190`, `llvm/lib/CodeGen/BranchRelaxation.cpp:111-230`; [`support/probe_self_attesting_and_invariance.py`](support/probe_self_attesting_and_invariance.py), [`support/probe_1_2_results.json`](support/probe_1_2_results.json))

In LLVM 23 (`23.1.1` and `23.1.5`), `MCAsmInfo::getInlineAsmLength` resides at `TargetInstrInfo::getInlineAsmLength` (`llvm/lib/CodeGen/TargetInstrInfo.cpp:113-149`):

```cpp
unsigned TargetInstrInfo::getInlineAsmLength(
  const char *Str, const MCAsmInfo &MAI, const TargetSubtargetInfo *STI) const {
  bool AtInsnStart = true;
  unsigned Length = 0;
  const unsigned MaxInstLength = MAI.getMaxInstLength(STI);
  for (; *Str; ++Str) {
    if (*Str == '\n' || strncmp(Str, MAI.getSeparatorString(),
                                strlen(MAI.getSeparatorString())) == 0) {
      AtInsnStart = true;
    } else if (isAsmComment(Str, MAI)) {
      AtInsnStart = false;
    }
    if (AtInsnStart && !isSpace(static_cast<unsigned char>(*Str))) {
      unsigned AddLength = MaxInstLength;
      if (strncmp(Str, ".space", 6) == 0) { /* parses base-10 integer SpaceSize */ }
      Length += AddLength;
      AtInsnStart = false;
    }
  }
  return Length;
}
```

Combining source inspection with live differential compilation on `x86_64` and `aarch64` reveals a sharp architectural split:

1. **Why `x86_64` `.text` is 100% bit-for-bit SHA-256 invariant even under multi-line `.pushsection` wrappers (`1.99.1` & `1.102.0-nightly`):**
   - **LLVM IR Inliner (`InlineCost.cpp:145-147, 798-834`):** `InlineAsmInstrCost` (`-inline-asm-instr-cost`) defaults to **`0`**, and even when non-zero, `CallAnalyzer::onInlineAsm` explicitly increments/decrements `SectionLevel` on `.pushsection`/`.popsection` (`lines 818-825`) and skips lines starting with `.` or containing `:` (`line 827`).
   - **LLVM IR Loop Unroller (`CodeMetrics.cpp:164-168`):** Counts the entire `CallBase` as 1 IR instruction regardless of assembly string length.
   - **X86 Backend & `jmp rel8` Relaxation (`X86InstrInfo.cpp:10591`):** X86 does **not** implement `getInstSizeInBytes` or run `BranchRelaxation`; short `rel8` (`74 69`) vs. near `rel32` (`0f 84 ...`) jump selection happens inside `MCAssembler::layout` over actual `.text` `MCFragment` sizes, which are `0`-byte invariant to `.pushsection .anneal.asm_sites ... .popsection`. Across `true_rel8` (`35 × 3 B = 105 B` forward `je rel8`), `inline_caller` (`93 B`), and `unroll_16` (`115 B`), `uninstrumented`, `multiline_pushsection`, and `single_macro` produce **identical byte lengths and SHA-256 digests** (`706a762c24d64257`, `d2fc79e0991f3848`, `ea1b97376a8c6b26`).
2. **Why `aarch64` `BranchRelaxation` Perturbs `.text` Under Multi-Line Wrappers—and How to Eliminate It:**
   - `AArch64InstrInfo::getInstSizeInBytes` (`AArch64InstrInfo.cpp:187-189`) calls `getInlineAsmLength` (`MaxInstLength = 4 B`) on every `INLINEASM` / `INLINEASM_BR` instruction, feeding `BranchRelaxation` (`TBZ`/`TBNZ` range $\pm 32\text{ KiB}$). Because `getInlineAsmLength` does **not** ignore `.pushsection`..`.popsection` or labels, a 10-statement wrapper inflates each `4 B` instruction to **`40 B` (`10×`)**:

| `aarch64` `true_tbz` Count ($N$) | Actual `.text` Span | `uninstrumented` (`1×4 B`) | `multiline_pushsection` (`10×4 B`) | `two_stmt_macro` (`2×4 B`) | `zero_sep_site_macro` (`1×4 B`) |
| :---: | :---: | :--- | :--- | :--- | :--- |
| **`N = 1,200`** | `4,800 B` ($< 32\text{ KiB}$) | `4,892 B` (`002f8b70b1b5919b`, `tbz`) | **`4,896 B` (`7b691e929a18be1d`, `tbnz + b` `+4 B` DRIFT!)** | `4,892 B` (`002f8b70b1b5919b`, `tbz`) | `4,892 B` (`002f8b70b1b5919b`, `tbz`, `1,200` records) |
| **`N = 5,000`** | `20,000 B` ($< 32\text{ KiB}$) | `20,092 B` (`f9a7a2a218a43fb4`, `tbz`) | **`20,096 B` (`6e06b4438d5f5b3a`, `tbnz + b` `+4 B` DRIFT!)** | **`20,096 B` (`6e06b4438d5f5b3a`, `+4 B` DRIFT: `40,000 B > 32 KiB`!)** | **`20,092 B` (`f9a7a2a218a43fb4`, `tbz`, `5,000` records — EXACT PARITY!)** |

   - Defining a per-site macro in module assembly (`global_asm!`, which is never passed to `getInlineAsmLength`) so the `INLINEASM` string is a single statement `__aw <id>, {0}` with **zero `\n` and zero `;`** keeps `getInlineAsmLength == 4 B` (and for a $K$-statement user body, appending `; .space 0` $K - 1$ times or emitting `.anneal.asm_sites` directly on `OutStreamer` in C++ `AsmPrinter::emitInlineAsm` around `Parser->Run` preserves the **exact** un-instrumented `getInlineAsmLength` for all $K$).

---

### 3. Pure-Rust CGU Sibling Containment (`MCObjectStreamer` vs. `MCAsmStreamer`)

`Basis: source + execution` (`rust-lang/llvm-project@1b9c0d5ff9`: `llvm/lib/CodeGen/AsmPrinter/AsmPrinterInlineAsm.cpp:90-138`, `llvm/lib/MC/MCObjectStreamer.cpp:406-445, 667-701`, `llvm/lib/MC/MCELFStreamer.cpp:108-245`; [`support/probe_cgu_rmeta_and_relaxations.py`](support/probe_cgu_rmeta_and_relaxations.py), [`support/probe_3_4_results.json`](support/probe_3_4_results.json))

Under `-C codegen-units=1`, all functions in a crate (plus inlined/monomorphized upstream functions) share a single `MCContext` and `MCStreamer`. Testing 12 hijack vectors from **uncalled** `asm!` / `global_asm!` blocks against **100% safe pure-Rust sibling functions** (containing zero `asm!`) across `rustc 1.99.1` and `1.102.0-nightly` establishes the exact containment boundary:

| Attack Vector in Uncalled `asm!` / `global_asm!` | `MCObjectStreamer` (`--emit=obj`, Default `cargo build`) | `MCAsmStreamer` (`--emit=asm`, Default `IAS=true`) | `MCAsmStreamer` (`-C llvm-args=-no-integrated-as`) | Governing LLVM Mechanism & Verifier Rule |
| :--- | :--- | :--- | :--- | :--- |
| **1. `.macro xorq src, dst -> subq`** vs. pure-Rust `10 ^ 3` | **Immune (`9`)** — `emitInstruction` bypasses `MCAsmParser` | **Immune (`9`)** — `emitInlineAsm` runs `MCAsmParser`, absorbing `.macro` as blank lines in `.s`! | **HIJACKED (`7`)** — `emitRawText` writes `.macro` verbatim to `.s`! | Forbid `-no-integrated-as`; still reject `.macro` because it hijacks sibling/downstream *`asm!`* blocks. |
| **2. `.code16` / `.code32`** vs. pure-Rust `6 * 7 + 5` | **Immune (`47`)** — `AsmPrinter` passes 64-bit `MF->getSubtarget()` per `MCInst` | **Breaks compilation** — `emitAssemblerFlag` writes `.code16`/`.code32` to `.s`, failing 64-bit pure-Rust insns | **Breaks compilation** | Reject `.code16`/`.code32`/`.code64`. (Note: LLVM 23 `--emit=asm` also emits `.prefalign`, rejected by GNU `as 2.47` and `llvm-mc <= 21`.) |
| **3. `.intel_syntax noprefix`** (inside `options(att_syntax)`) | **Immune (`47`)** — fresh `MCAsmParser` per `emitInlineAsm` | **Immune (`47`)** — `MCAsmParser` does not emit dialect directive to `.s` | **Breaks compilation** — AT&T `%rdi` pure-Rust insns fail under Intel mode | Reject `.intel_syntax` / `.att_syntax` directives. |
| **4. `.weak <pure_rust_fn>`** emitted *after* pure-Rust fn | **HIJACKED (`1` $\to$ `999`, `rc=0`)!** Pure-Rust `STB_GLOBAL` silently becomes `STB_WEAK` (`bind=2`), overridden by C! (`.weak` *before* fails closed: `changed binding to STB_GLOBAL`) | **HIJACKED (`STB_WEAK`)** | **HIJACKED (`STB_WEAK`)** | `MCELFStreamer.cpp:180-187` only warns on `GLOBAL -> WEAK`! **Must audit final `.o`/ELF `.symtab` bindings of pure-Rust symbols!** |
| **5. `.type <pure_rust_fn>, @gnu_indirect_function`** | **HIJACKED (`IFUNC=7777`, `rc=0`, ZERO warnings)!** `CombineSymbolTypes(STT_FUNC, STT_GNU_IFUNC)` promotes pure-Rust fn to `STT_GNU_IFUNC` (`type=10`)! | **HIJACKED (`STT_GNU_IFUNC`)** | **HIJACKED (`STT_GNU_IFUNC`)** | `MCELFStreamer.cpp:115-125, 201-204` orders `STT_FUNC < STT_GNU_IFUNC`! **Must reject `STT_GNU_IFUNC` across `.symtab`/`.dynsym`!** |
| **6. `.symver evil_fn, pure_name@@@VER1`** | **HIJACKED (`rc=0`, zero warnings)** — creates `GLOBAL FUNC pure_name@@VER1` bound to `evil_fn`'s section | **HIJACKED** | **HIJACKED** | `MCELFStreamer.cpp:283-288`; reject `.symver` and audit `.symtab` `(name, shndx)` bijectivity. |
| **7. `.cfi_sections .debug_frame`** in `global_asm!` / `asm!` | **CORRUPTED (`SIGABRT`, `rc=-6`)!** Strips `.eh_frame` from entire CGU (`cgu_has_eh_frame: false`); pure-Rust `catch_unwind` aborts (`error 5`)! | **CORRUPTED** | **CORRUPTED** | Mutates `MCStreamer` CGU-wide; reject `.cfi_sections` and assert `.eh_frame` presence when unwinding is enabled. |
| **8. Unbalanced `.section .rodata.trap`** (`-C force-unwind-tables=no`) | • **Uncalled sibling:** `b_pure_sibling` survives (`488d472ac3`, `AsmPrinter` switches to `.text.b_*`)<br>• **Inlined gadget:** `c_caller` `.text` is **`""` (0 B)**; pure-Rust `lea rax, [rdi+99]; ret` (`488d4763c3`) lands inside non-exec `.rodata.trap`! | Same truncation into `.rodata.trap` | Same truncation into `.rodata.trap` | Reject unbalanced `.section`/`.text`/`.data`/`.rodata`; enforce `start_sec == end_sec` on every attested `asm!` span. |
| **9–12. Trailing bare x86 prefixes (`.byte 0x66`, `0x41`, `0xf0`, `0x64`)** at end of inlined `asm!` | **ALL 4 CORRUPT PURE-RUST INSTRUCTIONS IN `MCObjectStreamer` (`rc=0`):**<br>• `0x66`: `b8 78 56 34 12` $\to$ `66 b8 78 56; 34 12` (`movw $0x5678, %ax; xorb $0x12, %al` $\to$ low16 `0x566a` + leaked upper `%eax`!)<br>• `0x41` (`REX.B`): `41 b8 ...` (`movl $0x12345678, %r8d`, leaving `%eax` uninitialized!)<br>• `0xf0` (`LOCK`): `f0 48 8d 04 37` (`lock leaq`) $\to$ **`SIGILL` (`rc=-4`)**<br>• `0x64` (`FS:`): `64 48 8b 07` (`movq %fs:(%rdi), %rax` TLS read on safe `&u64`!) | Same byte-stream fusion | Same byte-stream fusion | **Crucial:** `.pushsection .anneal.asm_sites ... .popsection` after `.byte 0x66` emits `0 B` in `.text` and **does not stop prefix fusion**! Verifier's slice decoder **must reject any incomplete/standalone trailing prefix byte** inside `[start_pc, end_pc)` (`trailing_prefix_bleed_rejected`). |

---

### 4. Cross-Crate `.rlib`/`.rmeta` Deferred Monomorphization, Post-Link Relaxations, and Lean `v4.34.1` Mechanization

#### 4.1 Cross-Crate `.rlib`/`.rmeta` Codegen Deferral and Downstream `.macro` Hijacking

`Basis: source + execution` (`rust-lang/rust@58cf8f9c35`: `compiler/rustc_metadata/src/rmeta/encoder.rs:1101-1131`, `compiler/rustc_monomorphize/src/collector.rs:1410-1490`; [`support/probe_cgu_rmeta_and_relaxations.py`](support/probe_cgu_rmeta_and_relaxations.py), [`support/probe_3_4_results.json`](support/probe_3_4_results.json))

Compiling `libupstream.rlib` (`--crate-type=rlib -C opt-level=3 -C codegen-units=1`) with five `pub unsafe fn` variants computing `a - b` via `sub {0:r}, {1:r}` (`generic_sub<T, C>`, `#[inline] inline_sub`, `#[inline(always)] inline_always_sub`, unannotated `unannotated_pub_sub`, and `#[inline(never)] never_inline_sub`) reveals two critical architectural facts on both `1.99.1` and `1.102.0-nightly`:

1. **Zero `.o` bytes in `libupstream.rlib` even for unannotated `pub fn`s at `-C opt-level=3`:** Inspecting every `.rcgu.o` member inside `libupstream.rlib` recovers **only one** `.anneal.asm_sites` record: `["kind=never_inline|0=rax|1=rsi"]`! Not only `generic_sub`, `inline_sub`, and `inline_always_sub`, **but also `unannotated_pub_sub`** satisfied `tcx.cross_crate_inlinable(def_id)` at `-C opt-level=3`, causing `rustc` to serialize its `optimized_mir` into `lib.rmeta` (`encoder.rs:1116-1120`) and defer machine-code generation completely to downstream crates.
2. **Downstream `global_asm!` `.macro` hijacks upstream `.rmeta`-inlined `asm!` — and self-attesting `.anneal.asm_sites` catches 100% of hijacked sites:** When `downstream` defines `global_asm!(".macro sub dst, src\nadd \\dst, \\src\n.endm")` and calls all five upstream functions on `(20, 5)`, `never_inline_sub` returns **`15`** (protected inside `libupstream.rlib`'s `.rcgu.o`), whereas **`generic_sub`, `inline_sub`, `inline_always_sub`, and `unannotated_pub_sub` all return `25` (`20 + 5`)** because their `.rmeta` MIR bodies lower inside `downstream`'s `MCContext`! Crucially, because the `.anneal.asm_sites` wrapper is part of the `TerminatorKind::InlineAsm` template serialized in `lib.rmeta`, `downstream.o` emits `4` `.anneal.asm_sites` records whose `[start_pc, end_pc)` slices begin with `0x01` (`ADD`) instead of `0x29` (`SUB`), catching **`4/4` (`100%`)** hijacked instantiations during downstream `.o` verification.

#### 4.2 Post-Link Opcode Relaxations (`GOTPCREL` vs. `REX_GOTPCRELX`, `GOTTPOFF` `%rax`/`%r12`, and Live `qemu-aarch64` `>128 MiB` Thunk Clobber)

`Basis: source + execution` (`rust-lang/llvm-project@1b9c0d5ff9`: `lld/ELF/Arch/X86_64.cpp:870-928`, `lld/ELF/Thunks.cpp:638-755`; [`support/probe_cgu_rmeta_and_relaxations.py`](support/probe_cgu_rmeta_and_relaxations.py), [`support/probe_3_4_results.json`](support/probe_3_4_results.json))

1. **x86-64 `@GOTPCREL` inside Rust `asm!` (`R_X86_64_GOTPCREL` `9` vs. `R_X86_64_REX_GOTPCRELX` `42`):**
   - By default (`-Z relax-elf-relocations=no`), `rustc` (`1.99.1` and `1.102.0-nightly`) emits **`R_X86_64_GOTPCREL` (`9`)** for `mov {0:r}, qword ptr [rip + {s}@GOTPCREL]` (and AT&T `movq`). **GNU `ld.bfd 2.47` relaxes even type `9` (`48 8b 05` $\to$ `48 8d 05` `leaq`)** unless `-Wl,--no-relax` is passed, whereas **`rust-lld` leaves type `9` unrelaxed (`movq`)**! Passing `-Z relax-elf-relocations=yes` (`1.102.0-nightly`) emits `R_X86_64_REX_GOTPCRELX` (`42`), which **both** `rust-lld` and `ld.bfd 2.47` relax to `leaq` (`got_relaxed_to_lea: true`), preserving `EFLAGS` in all modes.
2. **x86-64 `R_X86_64_GOTTPOFF` (`TLS IE -> LE`) Unconditional Relaxation and `%rax` vs. `%r12` `EFLAGS` Split:**
   - Across **all 8 tested configurations** (`rust-lld` and `ld.bfd 2.47`, **both with and without `-Wl,--no-relax`**), linking an executable rewrites `add rax, qword ptr [rip + my_tls_slot@GOTTPOFF]` (`48 03 05 ...`) into `leaq -8(%rax), %rax` (`48 8d 80 f8 ff ff ff`, **`zf_rax = 1` preserved**), while rewriting `add r12, qword ptr [rip + my_tls_slot@GOTTPOFF]` (`4c 03 25 ...`) into `addq $-8, %r12` (`49 81 c4 f8 ff ff ff`, **`zf_r12 = 0` clobbered**, `X86_64.cpp:877-887`). Dynamic tests or post-link binary checks that happen to inspect an `%rax`-allocated site miss the `EFLAGS` clobber that fires when inlining allocates `%r12` or `%rsp`.
3. **AArch64 `>128 MiB` Range-Extension Thunk (`__AArch64AbsLongThunk_*`) Silent `x16` Clobber Verified Live Under `qemu-aarch64`:**
   - Compiling a single `a64_thunk.o` (`sha256_16 = 95165eb4c0777329`) where `caller_holding_x16` holds `0x1122334455667788` live in `x16` across `asm!("bl {callee}", inout("x0") val, out("x30") _, callee = sym far_leaf_helper, options(nomem, nostack, preserves_flags))` (`far_leaf_helper` executes `add x0, x0, #42; ret`, never touching `x16`) and linking with `rust-lld` under two layouts produces opposite runtime outcomes on `qemu-aarch64 11.1.2`:
     - **`near.elf` (`<128 MiB`):** `bl` calls `far_leaf_helper` directly $\to$ **`VAL=000000000000008e X16=1122334455667788` (`exit 0`)**.
     - **`far.elf` (`0x200000` $\to$ `0x10000000`, `254 MiB > 128 MiB`):** `rust-lld` redirects `R_AARCH64_CALL26` to `__AArch64AbsLongThunk_far_leaf_helper` (`ldr x16, #8; br x16; .xword 0x10000000`, `Thunks.cpp:667-682`) $\to$ **`VAL=000000000000008e X16=0000000010000000` (`exit 42` — live caller `x16` silently clobbered!)**.
   - Therefore, any `R_AARCH64_CALL26` / `R_AARCH64_JUMP26` relocation inside non-naked `asm!` **must** either declare `out("x16") _, out("x17") _` (`IP0`/`IP1` AAPCS64 intra-procedure-call scratch registers) at `.o` time or discharge `|S + A - P| < 2^{27}` post-link!

#### 4.3 Mechanized Soundness in Lean `v4.34.1` ([`support/VerifiedSelfAttestingAsm.lean`](support/VerifiedSelfAttestingAsm.lean))

`Basis: execution + derived` (`leanprover/lean4@5045d00564` `v4.34.1`, [`support/VerifiedSelfAttestingAsm.lean`](support/VerifiedSelfAttestingAsm.lean))

`support/VerifiedSelfAttestingAsm.lean` (`567` lines, `Init.*`-only, `0` `sorry`, verified in `1.55 s`, `#print axioms` = `[propext]` only) proves six kernel-checked theorems:
1. `trailing_prefix_bleed_rejected`: `decodeCompleteSlice (xs ++ [.barePrefix pfx]) = none` rejects any `[start_pc, end_pc)` slice ending in a standalone prefix byte (`0x66`, `0x41`, `0xf0`, `0x64`).
2. `existential_alloc_unsound_counterexample`: constructive proof that `[.inst (.subReg .rcx .rbx)]` passes `existsValidAlloc2Match`, corrupts `rcx`, and fails to update `rbx`, while `checkSelfAttestedSite` with `att.sigma = {0 -> rbx, 1 -> rcx}` returns `false`.
3. `gottpoff_r12_breaks_preserves_flags`: `tlsLeaRelax .rax` preserves `zf = true` while `tlsAddImmRelax .r12` flips `zf = false`, rejected by `relocRelaxEnvelope`.
4. `aarch64_call26_far_thunk_clobbers_x16`: `blDirectNear` preserves `x16 = 0x1122334455667788` while `blLongThunkIP0` overwrites `x16 = 0x10000000`, rejected by `relocRelaxEnvelope` when `{x16, x17}` are absent from `declaredClobbers` and `provenNear = false`.
5. `self_attested_site_refinement_and_frame_sound`: proves that `decodeCompleteSlice` match under `att.sigma` + `checkPreLinkFlagsWF` + `decide (att.sigma (destOpOf t) ∉ clobbers) = true` (register-allocator non-aliasing between `inout` outputs and scratch clobbers `x16`/`x30`, without which `blLongThunkIP0` could overwrite `inout(reg)` itself!) + `checkEnvelopeSubsumed` implies exact output refinement and register/flag/stack/memory frame preservation across **every** `ValidInstLink` post-link outcome.
6. `self_attested_prog_frame_sound` (`0` axioms): lifts single-instruction frame preservation by induction to arbitrary multi-instruction `execPostLinkProg` sequences.

## Boundaries

- **Mach-O (`__DATA,__anneal_sites`) and PE/COFF (`IMAGE_SCN_LNK_REMOVE`) live execution (`not examined`):** All live `SHF_EXCLUDE` (`.anneal.asm_sites,"e",@progbits`) compilation and linker tests ran on Linux ELF64 (`x86_64` and `aarch64`). Mach-O lacks an `SHF_EXCLUDE` section flag (requiring explicit `-Wl,-sectcreate` / post-link `strip` or debug-segment placement), and COFF uses `.pushsection .anneal$s,"n"` (`IMAGE_SCN_LNK_REMOVE`).
- **RISC-V length-shrinking relaxations (`R_RISCV_RELAX`) inside `.anneal.asm_sites` spans (`known not to apply` without `-mno-relax` or post-link span re-resolution):** Unlike x86-64 and AArch64 relaxations—which preserve instruction byte lengths (`7 B` `mov -> lea`, `4 B` `bl -> bl thunk`)—RISC-V `R_RISCV_RELAX` deletes bytes mid-section, shifting intra-span offsets unless `.option norelax` is enforced inside `asm!` or spans are re-checked post-link.
- **Assuming `.anneal.asm_sites` alone detects rogue `global_asm!` or unverified `.o` inputs (`known not to apply`):** Compiler-injected `.anneal.asm_sites` wraps every `TerminatorKind::InlineAsm` lowered by the trusted compiler, but cannot prevent CGU-level symbol attribute mutations (`.weak`, `.type @gnu_indirect_function`, `.symver`, `.cfi_sections`) unless paired with the static directive reject-list and post-compile `.symtab`/`.eh_frame` audit in Section 3.
- **Alternative `rustc` backends (`rustc_codegen_cranelift`, `rustc_codegen_gcc`) (`not examined`):** `${:uid}` and `EmitInlineAsmStr` modifier expansion (`${0:q}`, `${N:c}`, `${N:l}`) are specific to `rustc_codegen_llvm` + LLVM `AsmPrinter`.
- **Stabilization timeline of `-Z relax-elf-relocations` and `asm_const_ptr` (`unknown`):** Both flags remain nightly-only in `rustc 1.102.0-nightly` (`E0658` / `-Z` rejected on stable `1.99.1`).
- **GNU `as 2.47` / `llvm-mc 21.1.8` direct assembly of unmodified `rustc 1.99.1+ --emit=asm` output (`unsupported` without stripping `.prefalign`):** Because LLVM 23 emits `.prefalign 4, .Lfunc_endN, nop` (`MCObjectStreamer.cpp:694`), external assemblers older than LLVM 23 reject raw `rustc --emit=asm` output on `x86_64` unless `.prefalign` directives are stripped or assembled by LLVM 23's integrated `MCAsmParser`.

## Evidence

### 1. Primary Upstream Source Citations
- **`rust-lang/llvm-project`** (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` LLVM `23.1.1` & `0a5579eb649d3634a9c30ac873300cc2944fa070` LLVM `23.1.5`):
  - `llvm/lib/CodeGen/AsmPrinter/AsmPrinterInlineAsm.cpp:90-138, 140-334, 432-463`: `useIntegratedAssembler()` vs. `emitRawText` in `emitInlineAsm`, character-level `EmitInlineAsmStr` `$` expansion, `PrintSpecial` `${:uid}`, and `PrintSymbolOperand`.
  - `llvm/lib/Target/X86/X86AsmPrinter.cpp:757-864`: X86 `PrintAsmOperand` width/register modifiers (`b`, `h`, `w`, `k`, `q`, `V`, `x`, `t`, `g`, `c`).
  - `llvm/lib/MC/MCAsmInfo.cpp:79-98`: `isAcceptableChar` admitting `$` and `.` in unquoted symbol names while quoting `|` and `"`.
  - `llvm/lib/CodeGen/TargetInstrInfo.cpp:113-149`: `TargetInstrInfo::getInlineAsmLength` `\n`/`;` statement counting and `.space` fast path.
  - `llvm/lib/Analysis/InlineCost.cpp:145-147, 798-834` & `llvm/lib/Analysis/CodeMetrics.cpp:164-168`: `InlineAsmInstrCost = 0`, `.pushsection`/`.popsection` `SectionLevel` filtering, and 1-instruction IR loop-unroll cost.
  - `llvm/lib/Target/X86/X86InstrInfo.cpp:10590-10597` & `llvm/lib/Target/AArch64/AArch64InstrInfo.cpp:179-190`: absence of X86 `getInstSizeInBytes` vs. AArch64 `INLINEASM`/`INLINEASM_BR` delegation to `getInlineAsmLength`.
  - `llvm/lib/MC/MCObjectStreamer.cpp:406-445, 667-701` & `llvm/lib/MC/MCELFStreamer.cpp:108-245, 283-288`: shared `MCFragment` `emitBytes`/`emitInstToData` (trailing-prefix fusion), `.prefalign` emission, `CombineSymbolTypes` (`STT_FUNC < STT_GNU_IFUNC`), `MCSA_Weak` (`GLOBAL -> WEAK` warning-only downgrade), and `emitELFSymverDirective`.
  - `lld/ELF/Arch/X86_64.cpp:870-928` & `lld/ELF/Thunks.cpp:638-755`: `relaxTlsIeToLe` (`%rsp`/`%r12` `addq` vs. `leaq`) and `AArch64ABSLongThunk` / `AArch64ADRPThunk` `x16` (`IP0`) clobber.
- **`rust-lang/rust`** (`58cf8f9c35b355199727627d07ae34a4e2846d67` `1.99.1` & `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` `1.102.0-nightly`):
  - `compiler/rustc_codegen_llvm/src/asm.rs:183-255, 411-455`: user `$` $\to$ `$$` escaping, `${N:<mod>}`/`${N:c}`/`${N:l}` emission, and `codegen_global_asm`.
  - `compiler/rustc_metadata/src/rmeta/encoder.rs:1101-1131`: `should_encode_mir` encoding `optimized_mir` in `lib.rmeta` for generics and `cross_crate_inlinable` items.

### 2. Preserved Standalone Artifacts (`support/`, Observed `2026-11-21`)
- [`support/VerifiedSelfAttestingAsm.lean`](support/VerifiedSelfAttestingAsm.lean): `567`-line `Init.*`-only Lean `v4.34.1` mechanization (`6` theorems, `0` `sorry`, `1.55 s`).
- [`support/probe_self_attesting_and_invariance.py`](support/probe_self_attesting_and_invariance.py) $\to$ [`support/probe_1_2_results.json`](support/probe_1_2_results.json): Self-attesting `.anneal.asm_sites` + `.anneal.asm_descs` across inlining, `4×` unrolling, tail cloning, `asm_goto` `callbr`, all register classes, `asm_const_ptr`, swapped-`sub` rejection, 4-vector spoof matrix + `<NONCE>`/`${:uid}` IR defense, and `x86_64` + `aarch64` (`N=1,200` & `N=5,000`) `getInlineAsmLength` codegen-invariance checks.
- [`support/probe_cgu_rmeta_and_relaxations.py`](support/probe_cgu_rmeta_and_relaxations.py) $\to$ [`support/probe_3_4_results.json`](support/probe_3_4_results.json): 12-vector CGU pure-Rust containment matrix across 3 streamer modes, cross-crate `.rlib`/`.rmeta` downstream `.macro` hijacking + `4/4` `.anneal.asm_sites` detection, `rust-lld` vs. `ld.bfd 2.47` `GOTPCREL`/`REX_GOTPCRELX`/`GOTTPOFF` (`%rax` vs. `%r12`) matrix, and live `qemu-aarch64` `<128 MiB` vs. `>128 MiB` `x16` veneer clobber.

## Revalidation

From the package directory, re-verify the Lean `v4.34.1` proofs and rerun both self-contained Python 3.10+ probe suites (~20 seconds total; temporary directories are cleaned automatically via `tempfile.TemporaryDirectory()`):

```bash
lean support/VerifiedSelfAttestingAsm.lean
python3 -B support/probe_self_attesting_and_invariance.py --toolchains 1.99.1 nightly
python3 -B support/probe_cgu_rmeta_and_relaxations.py --toolchains 1.99.1 nightly
```

Key discriminating checks on future `rustc`, LLVM/`rust-lld`, or Binutils upgrades:
1. **`getInlineAsmLength` & `InlineCost`:** Check `exact_byte_parity_all_modes` (`x86_64`) and `N_5000.zero_sep_site_macro.entry_branch == "tbz_direct"` (`aarch64`) in `probe_1_2_results.json` to detect if X86 implements `getInstSizeInBytes` or `InlineCost` changes `InlineAsmInstrCost`.
2. **`MCELFStreamer` pure-Rust symbol protection:** Check `mc_object_streamer_symbol_hijacks` in `probe_3_4_results.json` to detect if LLVM upgrades `GLOBAL -> WEAK` (`MCELFStreamer.cpp:184`) or `STT_FUNC -> STT_GNU_IFUNC` (`CombineSymbolTypes`) to hard assembler errors.
3. **Cross-crate `.rlib` codegen & `-Z relax-elf-relocations`:** Check `upstream_rlib_descs` and `default_gotpcrel.prelink_got_reloc_type` in `probe_3_4_results.json` to detect if `rustc` enables `X86RelaxRelocations` (`42`) by default on stable `x86_64-unknown-linux-gnu`.
