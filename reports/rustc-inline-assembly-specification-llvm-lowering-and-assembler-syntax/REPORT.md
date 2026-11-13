# Operational Specification of Rust Inline Assembly (`asm!`, `naked_asm!`, `global_asm!`), LLVM Constraint Lowering, and Integrated Assembler Syntax

## Summary

Implementing or verifying `asm!`, `naked_asm!` (`#[unsafe(naked)]`), and
`global_asm!` in a drop-in replacement for `rustc 1.99.1`
(`58cf8f9c35b355199727627d07ae34a4e2846d67`) requires an exact specification of
four layers: (1) frontend macro validation and operand typing (`rustc_builtin_macros::asm`,
`rustc_target::asm`), (2) ABI clobber sets and reserved-register rules, (3)
lowering to LLVM inline-assembly constraint strings and call-site attributes
(`rustc_codegen_llvm::asm`), and (4) module-level assembly generation for naked
functions (`rustc_codegen_ssa::mir::naked_asm`) and LLVM MC integrated assembler
syntax (`AsmParser.cpp`, `X86AsmParser.cpp`, `AArch64AsmParser.cpp`):

1. **Complete register-class, type, feature-gate, and modifier tables (`28` `InlineAsmArch` variants):**
   `compiler/rustc_target/src/asm/mod.rs` defines **28 `InlineAsmArch` targets**.
   On **x86 / x86-64** (`compiler/rustc_target/src/asm/x86.rs`), there are **11
   register classes** (`reg`, `reg_abcd`, `reg_byte`, `xmm_reg`, `ymm_reg`,
   `zmm_reg`, `kreg`, `kreg0`, `mmx_reg`, `x87_reg`, `tmm_reg`), of which 4
   (`kreg0`, `mmx_reg`, `x87_reg`, `tmm_reg`) are clobber-only. On **AArch64 /
   Arm64EC** (`compiler/rustc_target/src/asm/aarch64.rs`), there are **4 register
   classes** (`reg`, `vreg`, `vreg_low16`, `preg`), of which `preg` (`p0`–`p15`,
   `ffr`) is clobber-only.
2. **Reserved registers and `clobber_abi` sets:**
   - On `x86` / `x86_64`, `bp`/`ebp`/`rbp` (frame pointer), `sp`/`esp`/`rsp`
     (stack pointer), and `ip`/`eip`/`rip` are unconditionally rejected as
     operands (`#error`). In addition, `rbx`/`ebx`/`bx`/`bl`/`bh` are rejected on
     `x86_64` (`"rbx is used internally by LLVM"`), `esi`/`si` are rejected on
     32-bit `x86` (`"esi is used internally by LLVM"`), and high-byte registers
     (`ah`, `bh`, `ch`, `dh`) are rejected on `x86_64`.
   - On `aarch64`, `x19`/`w19` (`"used internally by LLVM"`), `x29`/`fp` (frame
     pointer), `sp`/`wsp` (stack pointer), and `xzr`/`wzr` (zero register) are
     unconditionally rejected, while `x18`/`w18` is rejected on Android, Fuchsia,
     OpenHarmony, Darwin/macOS/iOS, Windows, or when `+reserve-x18` is set
     (`target_reserves_x18`, `aarch64.rs:74-84`). On `Arm64EC`, `x13`, `x14`,
     `x23`, `x24`, `x28`, `v16`–`v31`, `p0`–`p15`, and `ffr` are additionally
     forbidden.
   - `clobber_abi(...)` (`mod.rs:975-1423`) expands to explicit caller-saved
     register clobbers, including `xmm6`–`xmm15` on `X86_64Win` (because the
     upper bits of `ymm6`–`ymm15` are volatile even though the low 128-bit `xmm`
     halves are callee-saved in Win64!) and full `v8`–`v15` on `AArch64`
     (because inline assembly clobbers cannot express preserving only the low
     64-bit `d8`–`d15` halves while clobbering the upper 64 bits!).
3. **Exact lowering of `asm!` to LLVM IR (`compiler/rustc_codegen_llvm/src/asm.rs`):**
   - Early-clobber outputs (`out` / `inout`) emit `"=&<constraint>"`, whereas
     `lateout` / `inlateout` emit `"=<constraint>"`.
   - Tied `inout` operands on register classes emit `"<output_idx>"` as the
     input constraint, whereas `inlateout` on an explicit register duplicates
     the explicit register constraint (`"{rax}"`) to match Clang (`asm.rs:153-161`).
   - Unless `options(preserves_flags)` is set, `rustc` appends
     `~{dirflag},~{fpsr},~{flags}` on `x86`/`x86_64` and `~{cc}` on
     `aarch64`/`arm`. Unless `options(nomem)` is set, `rustc` appends `~{memory}`.
   - Option combinations map to LLVM call-site `MemoryEffects` attributes
     (`asm.rs:364-377`): `pure + nomem` $\to$ `memory(none) + willreturn`;
     `pure + readonly` $\to$ `memory(read) + willreturn`; `nomem` (without
     `pure`) $\to$ `memory(inaccessiblemem: readwrite)` + `sideeffect`;
     `readonly` (without `pure`) $\to$ `memory(read, inaccessiblemem: readwrite)` +
     `sideeffect`.
4. **Module-level lowering of `#[unsafe(naked)]` / `naked_asm!` (`compiler/rustc_codegen_ssa/src/mir/naked_asm.rs`):**
   In `rustc 1.99.1`, `#[unsafe(naked)]` functions are **not** lowered as LLVM
   IR functions with `@llvm.naked`; instead, `codegen_naked_asm` (`naked_asm.rs:18-58`)
   extracts the `TerminatorKind::InlineAsm` from `START_BLOCK`, wraps its
   template with target-format-specific assembly prologue/epilogue directives
   (`prefix_and_suffix`, `lines 142-411` for ELF, Mach-O, COFF, Wasm, and XCOFF),
   converts `const` and `sym` operands into `GlobalAsmOperandRef`s, and passes
   the result to `codegen_global_asm` (`llvm::append_module_inline_asm`)!

## Applicability

This specification applies to **Rust 1.99.1** (`58cf8f9c35b355199727627d07ae34a4e2846d67`),
**LLVM 23.1.1** (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), the **Rust
Reference** (`b96ad7f37eb5fcab7bd2ffd8f9fb4c20fa07c86b`, `src/inline-assembly.md`),
and **FLS 1.99** (`946eacae5a4a33a89af7832178504692439e7478`).

## Findings

### 1. Register classes, allowed types, feature gates, modifiers, and LLVM codes

Basis: normative (`reference/src/inline-assembly.md`, `fls/src/inline-assembly.rst`) + source (`compiler/rustc_target/src/asm/{x86.rs,aarch64.rs}`, `compiler/rustc_codegen_llvm/src/asm.rs:688-955`)

Table 1 specifies every register class on `x86` / `x86_64` and `aarch64` /
`arm64ec`, its allowed `InlineAsmType`s (and required `#[target_feature]`),
valid template modifiers, default modifier, Rust-to-LLVM constraint code, and
Rust-to-LLVM modifier mapping.

| Arch | Register Class | Allowed `InlineAsmType`s & Required Target Feature (`x86.rs` / `aarch64.rs`) | Valid Rust Modifiers | Default Modifier | LLVM Constraint Code (`reg_to_llvm`) | LLVM Modifier (`modifier_to_llvm`) |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86` / `x86_64` | `reg` | `x86_64`: `I16, I32, I64, F16, F32, F64` (unconditional)<br>`x86`: `I16, I32, F16, F32` (unconditional) | `x86_64`: `'l'`, `'x'`, `'e'`, `'r'`<br>`x86`: `'x'`, `'e'` | `x86_64`: `'r'` (`rax`)<br>`x86`: `'e'` (`eax`) | `"r"` | `None` $\to$ `'q'` (`x86_64`) / `'k'` (`x86`); `'l'`$\to$`'b'`, `'x'`$\to$`'w'`, `'e'`$\to$`'k'`, `'r'`$\to$`'q'` |
| `x86` / `x86_64` | `reg_abcd` | Same as `reg` (`ax`, `bx`, `cx`, `dx` only) | `x86_64`: `'l'`, `'h'`, `'x'`, `'e'`, `'r'`<br>`x86`: `'l'`, `'h'`, `'x'`, `'e'` | `x86_64`: `'r'` (`rax`)<br>`x86`: `'e'` (`eax`) | `"Q"` | Same as `reg`, plus `'h'` $\to$ `'h'` |
| `x86` / `x86_64` | `reg_byte` | `I8` (unconditional) | `[]` (none) | `None` | `"q"` | `None` |
| `x86` / `x86_64` | `xmm_reg` | `sse`: `I32, I64, I128, F16, F32, F64, F128, VecI8(16), VecI16(8), VecI32(4), VecI64(2), VecF16(8), VecF32(4), VecF64(2)` | `'x'`, `'y'`, `'z'` | `'x'` (`xmm0`) | `"x"` | `None` / `'x'` $\to$ `'x'`, `'y'` $\to$ `'t'`, `'z'` $\to$ `'g'` |
| `x86` / `x86_64` | `ymm_reg` | `avx`: All `xmm_reg` types + `VecI8(32), VecI16(16), VecI32(8), VecI64(4), VecF16(16), VecF32(8), VecF64(4)` | `'x'`, `'y'`, `'z'` | `'y'` (`ymm0`) | `"x"` | `None` / `'y'` $\to$ `'t'`, `'x'` $\to$ `'x'`, `'z'` $\to$ `'g'` |
| `x86` / `x86_64` | `zmm_reg` | `avx512f`: All `ymm_reg` types + `VecI8(64), VecI16(32), VecI32(16), VecI64(8), VecF16(32), VecF32(16), VecF64(8)` | `'x'`, `'y'`, `'z'` | `'z'` (`zmm0`) | `"v"` | `None` / `'z'` $\to$ `'g'`, `'x'` $\to$ `'x'`, `'y'` $\to$ `'t'` |
| `x86` / `x86_64` | `kreg` | `avx512f`: `I8, I16`; `avx512bw`: `I32, I64` (`k1`–`k7`) | `[]` | `None` | `"^Yk"` | `None` |
| `x86` / `x86_64` | `kreg0`, `mmx_reg`, `x87_reg`, `tmm_reg` | `[]` (**Clobber-only**: `out("st(0)") _` clobbers entire `~{st},~{st(1)}..~{st(7)}`) | `[]` | `None` | Clobber `~{...}` | N/A |
| `aarch64` / `arm64ec` | `reg` | `I8, I16, I32, I64, F16, F32, F64` (unconditional) | `'w'`, `'x'` | `'x'` (`x0`) | `"r"` | `'w'` $\to$ `'w'`, `'x'` $\to$ `'x'`, `None` $\to$ `None` |
| `aarch64` / `arm64ec` | `vreg` | `neon`: `I8, I16, I32, I64, F16, F32, F64, F128, VecI8(8/16), VecI16(4/8), VecI32(2/4), VecI64(1/2), VecF16(4/8), VecF32(2/4), VecF64(1/2)` | `'b'`, `'h'`, `'s'`, `'d'`, `'q'`, `'v'` | `'v'` (`v0`) | `"w"` | `'v'` $\to$ `None`; `'b'`, `'h'`, `'s'`, `'d'`, `'q'` unchanged |
| `aarch64` / `arm64ec` | `vreg_low16` | Same as `vreg` (`v0`–`v15` only) | `'b'`, `'h'`, `'s'`, `'d'`, `'q'`, `'v'` | `'v'` (`v0`) | `"x"` | Same as `vreg` |
| `aarch64` / `arm64ec` | `preg` | `[]` (**Clobber-only**: `p0`–`p15`, `ffr`) | `[]` | `None` | Clobber `~{...}` | N/A |

*(Note: Pointer types `*const T`, `*mut T`, `fn(...)`, and `Option<fn(...)>` and
`#[repr(transparent)]` wrappers around allowed types are mapped to their
underlying integer/SIMD `InlineAsmType` during HIR type checking in
`compiler/rustc_hir_analysis/src/check/intrinsic.rs`.)*

#### 1.1 LLVM input/output type fixups (`llvm_fixup_input` / `llvm_fixup_output`)

Because LLVM's inline-assembly constraint validator rejects certain scalar/vector
combinations that Rust allows, `compiler/rustc_codegen_llvm/src/asm.rs:1095-1340`
applies deterministic IR coercions before and after the `call asm` instruction:
- **AArch64 `vreg` with `i8`:** Coerced to `<8 x i8>` via `insertelement` at
  lane 0 (`asm.rs:1105-1112`).
- **AArch64 `vreg_low16` (`"x"` constraint):** Because LLVM's `"x"` constraint
  only accepts 128-bit vector types, scalar inputs (except `f128`) are widened to
  `<16/size x elem_ty>` via `insertelement`, and 64-bit SIMD vectors are doubled
  to 128-bit via `shufflevector` (`asm.rs:1113-1135`).
- **x86 `reg_abcd` with `f64`:** Bitcast to `i64` (`asm.rs:1136-1140`).
- **x86 `xmm_reg`/`ymm_reg`/`zmm_reg` without AVX-512:** When `f16` or `f128` is
  passed without `avx512fp16`/`avx512f`, `f16` is zero-extended to `i32` / `<4 x i16>`
  and `f128` is bitcast to `<2 x f64>` (`asm.rs:1155-1220`).
- **Explicit register `x30` on AArch64 and `r14` on Arm:** Emitted as `"{lr}"` in
  LLVM constraints because LLVM does not recognize `{x30}` or `{r14}`
  (`asm.rs:715-717, 742-745`).

---

### 2. Operand directions, `clobber_abi`, and option validation rules

Basis: source (`compiler/rustc_builtin_macros/src/asm.rs:39-263`, `compiler/rustc_target/src/asm/mod.rs:975-1424`)

Table 2 specifies the exact compile-time validation rules enforced by
`validate_asm_args` (`compiler/rustc_builtin_macros/src/asm.rs:39-263`) and
`rustc_passes`.

| Option / Construct | Allowed in `asm!` | Allowed in `naked_asm!` | Allowed in `global_asm!` | Mutual Exclusions & Mandatory Co-Occurrences (`rustc_builtin_macros/src/asm.rs`) | LLVM IR Lowering (`rustc_codegen_llvm/src/asm.rs`) |
| :--- | :---: | :---: | :---: | :--- | :--- |
| `pure` | Yes | No | No | Requires `nomem` or `readonly` (`line 189`); forbids `noreturn` (`line 183`); requires $\ge 1$ real output (`line 225`) | Clears `sideeffect` (`volatile = false`), adds `willreturn` + `memory(none)` or `memory(read)` |
| `nomem` | Yes | No | No | Mutually exclusive with `readonly` (`line 177`) | Omits `~{memory}` clobber; sets `memory(none)` (with `pure`) or `memory(inaccessiblemem: readwrite)` |
| `readonly` | Yes | No | No | Mutually exclusive with `nomem` (`line 177`) | Keeps `~{memory}`; sets `memory(read)` (with `pure`) or `memory(read, inaccessiblemem: readwrite)` |
| `preserves_flags` | Yes | No | No | Compatible with all `asm!` options | Omits `~{dirflag},~{fpsr},~{flags}` (`x86`) / `~{cc}` (`aarch64`/`arm`/`s390x`) |
| `noreturn` | Yes | No | No | Mutually exclusive with `pure` (`line 183`); forbids outputs unless `label` (`asm_goto`) is present (`line 228`) | Normal destination block is `TerminatorKind::Unreachable`; outputs written only along `label` edges |
| `nostack` | Yes | No | No | Compatible with all `asm!` options | Clears `alignstack` (`alignstack = false`) on `LLVMGetInlineAsm` |
| `may_unwind` | Yes | No | No | Mutually exclusive with `label` (`asm_goto`) operands (`line 236`) | Sets `canThrow = true` on `LLVMGetInlineAsm`; emits `invoke ... to label %normal unwind label %cleanup` |
| `att_syntax` | Yes (`x86`) | Yes (`x86`) | Yes (`x86`) | Only valid on `x86` / `x86_64` | Sets `llvm::AsmDialect::Att` (for `asm!`) or wraps module asm in `.att_syntax` (vs. `.intel_syntax` default) |
| `raw` | Yes | Yes | Yes | Disables `{}` format-string interpolation; incompatible with any operands (`in`, `out`, `sym`, `const`, `label`) | Passes template string verbatim (escaping `$` as `$$` in `asm!`, unescaped in `global_asm!`/`naked_asm!`) |
| `clobber_abi(...)` | Yes | No (`line 242`) | No (`line 242`) | Forbids generic register-class outputs (`out(reg) x`) unless marked `lateout(reg)` or explicit register (`line 252`) | Expands all caller-saved registers of the ABI into dummy outputs or `~{reg}` clobbers |
| `sym <path>` | Yes | Yes | Yes | Path must resolve to a `fn` or `static` item (including `#[thread_local]` statics) | Constraint `"s"`, template `${N:c}` (plus signed constant offset if promoted pointer has offset) |
| `const <expr>` | Yes | Yes | Yes | Integer scalar or promoted pointer expression | Integer scalar injected directly as decimal literal into template (`asm_const_to_str`); pointer lowered like `sym` |
| `label { ... }` | Yes | No | No | Mutually exclusive with `may_unwind` (`line 236`) | Constraint `"!i"`, template `${N:l}`, lowered via LLVM `callbr` with indirect destination basic blocks |

---

### 3. Module-level emission of `#[unsafe(naked)]` / `naked_asm!` across object formats

Basis: source (`compiler/rustc_codegen_ssa/src/mir/naked_asm.rs:142-411`, `compiler/rustc_codegen_llvm/src/asm.rs:411-511`)

Unlike regular functions (which lower to LLVM IR `Function` definitions), a
`#[unsafe(naked)]` function containing `naked_asm!(...)` is lowered by
`codegen_naked_asm` into a module-level assembly block (`LLVMAppendModuleInlineAsm`)
bracketed by `prefix_and_suffix`:

| Object Format (`BinaryFormat`) | Emitted Prologue (`begin`) Before `naked_asm!` Body (`naked_asm.rs:245-408`) | Emitted Epilogue (`end`) After `naked_asm!` Body | Default Alignment |
| :--- | :--- | :--- | :--- |
| **ELF** (`Linux`, etc.) | `.pushsection .text.<name>,"ax", @progbits` (or `.text`), `.balign 4`, `.globl <name>` (or `.weak`), `.hidden`/`.protected` (if applicable; always `.hidden` in `compiler_builtins`), `.type <name>, @function`, `<name>:` | `.Lfunc_end_<name>:\n.size <name>, . - <name>\n.popsection` | `4` bytes |
| **Mach-O** (`macOS`, `iOS`) | `.section __TEXT,__text,regular,pure_instructions` (or `.pushsection <custom>`), `.balign 4`, `.globl <name>` (plus `.weak_definition` if weak), `.private_extern <name>` (if hidden), `<name>:` | `.Lfunc_end_<name>:` (plus `.popsection` if custom section) | `4` bytes |
| **COFF** (`Windows` MSVC / GNU) | `.def <name>\n.scl 2\n.type 32\n.endef\n.section .text,"xr",one_only,<name>` (MSVC) or `.section .text$<name>,"xr",one_only,<name>` (GNU), `.globl <name>`, `.balign 16`, `<name>:` | (arm thumb/arm suffix if applicable) | **`16` bytes** |
| **Wasm** | `.section .text.<name>,"",@\n.globl <name>\n.type <name>, @function\n<name>:\n.functype <name> (<params>) -> (<rets>)` | `end_function\n.Lfunc_end_<name>:` | None |

Furthermore, on `x86` and `x86_64`, `codegen_global_asm` (`asm.rs:425-500`)
prepends `.intel_syntax\n` (unless `options(att_syntax)` is specified, in which
case it prepends `.att_syntax\n`) and appends `\n.att_syntax\n` at the end of
every `global_asm!` / `naked_asm!` block so module-level assembly always leaves
LLVM's integrated assembler in AT&T mode.

---

### 4. LLVM 23.1.1 integrated assembler syntax and directive inventory

Basis: source (`llvm/lib/MC/MCParser/AsmParser.cpp`, `llvm/lib/Target/X86/AsmParser/X86AsmParser.cpp`, `llvm/lib/Target/AArch64/AsmParser/AArch64AsmParser.cpp` in `support/inline_asm_spec.json`)

Parsing the directive dispatch tables in LLVM `23.1.1`'s MC layer identifies:
- **156 generic assembler directives** in `AsmParser.cpp` (`support/inline_asm_spec.json`),
  grouped into:
  - *Section control:* `.section`, `.pushsection`, `.popsection`, `.previous`,
    `.text`, `.data`, `.bss`, `.rodata`, `.subsection`.
  - *Symbol visibility & attributes:* `.globl`/`.global`, `.local`, `.weak`,
    `.weakref`, `.hidden`, `.protected`, `.internal`, `.private_extern`,
    `.weak_definition`, `.type`, `.size`, `.comm`, `.lcomm`, `.symver`, `.alt_entry`.
  - *Alignment & fill:* `.align`, `.balign`, `.balignw`, `.balignl`, `.p2align`,
    `.p2alignw`, `.p2alignl`, `.org`, `.space`, `.skip`, `.zero`, `.fill`.
  - *Data emission:* `.byte`, `.short`, `.hword`, `.value`, `.2byte`, `.int`,
    `.long`, `.4byte`, `.quad`, `.8byte`, `.octa`, `.ascii`, `.asciz`, `.string`,
    `.float`, `.single`, `.double`, `.uleb128`, `.sleb128`, `.incbin`, `.insn`.
  - *Macros, conditionals & repetition:* `.macro`/`.endm`/`.exitm`, `.purgem`,
    `.rept`/`.endr`, `.irp`/`.irpc`, `.if`/`.ifdef`/`.ifndef`/`.ifeqs`/`.elseif`/`.else`/`.endif`,
    `.equ`, `.equiv`, `.set`, `.altmacro`, `.noaltmacro`.
  - *DWARF CFI & debug:* `.cfi_startproc`, `.cfi_endproc`, `.cfi_def_cfa`,
    `.cfi_def_cfa_offset`, `.cfi_def_cfa_register`, `.cfi_adjust_cfa_offset`,
    `.cfi_offset`, `.cfi_rel_offset`, `.cfi_register`, `.cfi_restore`,
    `.cfi_undefined`, `.cfi_same_value`, `.cfi_remember_state`,
    `.cfi_restore_state`, `.cfi_escape`, `.cfi_personality`, `.cfi_lsda`,
    `.cfi_signal_frame`, `.cfi_return_column`, `.file`, `.loc`, `.cv_loc`.
- **38 x86-specific directives** in `X86AsmParser.cpp`, including
  `.intel_syntax`, `.att_syntax`, `.code16`, `.code16gcc`, `.code32`, `.code64`,
  and Windows x64 SEH unwind directives (`.seh_proc`, `.seh_endproc`,
  `.seh_pushreg`, `.seh_savereg`, `.seh_savexmm`, `.seh_setframe`,
  `.seh_stackalloc`, `.seh_endprologue`, `.seh_handler`, `.seh_handlerdata`).
- **74 AArch64-specific directives** in `AArch64AsmParser.cpp`, including
  `.arch`, `.arch_extension`, `.cpu`, `.inst`, `.req`/`.unreq`, `.ltorg`/`.pool`,
  `.cfi_b_key_frame`, `.cfi_mte_tagged_frame`, `.variant_pcs`, and Windows
  ARM64 SEH directives (`.seh_save_fplr`, `.seh_save_fplr_x`, `.seh_save_reg`,
  `.seh_save_regp`, `.seh_save_r19r20_x`, `.seh_save_next`, `.seh_nop`,
  `.seh_pac_sign_lr`).

## Boundaries

- **External assembler fallback (`-no-integrated-as`):** Only LLVM `23.1.1`'s
  integrated MC assembler (`MCAsmParser`), which `rustc` enables by default on
  all Tier 1 targets, was analyzed.
- **Unstable architectures (`spirv`, `nvptx`, `amdgpu`, `wasm`):** While their
  register classes and constraint codes are included in `support/inline_asm_spec.json`,
  full assembler grammar analysis is scoped to `x86` / `x86_64` and `aarch64`.

## Evidence

- **Rust 1.99.1 (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_target/src/asm/{mod.rs,x86.rs,aarch64.rs,arm.rs,riscv.rs}`.
  - `compiler/rustc_builtin_macros/src/asm.rs:1-672`.
  - `compiler/rustc_codegen_ssa/src/mir/naked_asm.rs:1-515`.
  - `compiler/rustc_codegen_llvm/src/asm.rs:1-1574`.
- **LLVM 23.1.1 (`rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
  - `llvm/lib/MC/MCParser/AsmParser.cpp`, `llvm/lib/Target/X86/AsmParser/X86AsmParser.cpp`,
    `llvm/lib/Target/AArch64/AsmParser/AArch64AsmParser.cpp`.
- **Normative specifications:**
  - `rust-lang/reference` (`b96ad7f37eb5fcab7bd2ffd8f9fb4c20fa07c86b`), `src/inline-assembly.md`.
  - `rust-lang/fls` (`946eacae5a4a33a89af7832178504692439e7478`, tag `1.99`), `src/inline-assembly.rst`.
- **Preserved support artifacts:**
  - `support/inline_asm_spec.json`: Complete extracted register classes,
    supported types, explicit register lists, reserved register reasons, and
    LLVM MC directive tables.
  - `support/probe_inline_asm.py`: Standalone extractor script.

## Revalidation

Run `python3 support/probe_inline_asm.py` against a newer `rust-lang/rust` and
`llvm-project` checkout to detect any new `InlineAsmArch` variants, register
classes, `clobber_abi` sets, or MC directives.
