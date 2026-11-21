# Inline Assembly (`asm!` / `naked_asm!` / `global_asm!`) Register/Clobber Framing and `compiler-builtins` Intrinsics Verification

## Summary

For a verified drop-in `rustc`, inline assembly (`asm!`, `naked_asm!`, `global_asm!`) and compiler runtime intrinsics (`compiler-builtins`) define the boundary between checked Rust/MIR semantics and unverified target machine execution. At `joshlf/anneal` revision `c131b320eeeb26ef692e5afd5ec8db49ee518613`, Anneal explicitly fails closed on inline assembly by mapping `TerminatorKind::InlineAsm` to `.unsupported` (`trusted/lean/Trusted/MirAst.lean:782-795`, `evalTerminator` `.fault .unsupported` in `trusted/lean/Trusted/MirSemantics.lean:1568-1569`), which `BodyVerified` rejects whenever reachable (`MirSemantics.lean:1748-1758`). Supporting stdlib, `core::arch`, and compiler-rt primitives under a drop-in verified `rustc` requires discharging two distinct Trusted Computing Base (TCB) contracts: (1) a multi-architecture operational frame contract governing `asm!` operand constraints (`=&r` early-clobber vs. `=r` late-out aliasing), `options(...)` effects (`pure`, `nomem`, `readonly`, `preserves_flags`, `nostack`, `noreturn`, `may_unwind`, `att_syntax`, `raw`), `clobber_abi(...)` sets, reserved registers, and module-level `naked_asm!`/`global_asm!` lowering; and (2) software runtime intrinsics (`__udivti3`, `__umodti3`, `__divti3`, `__multi3`, `__ashlti3`, `__lshrti3`, `memcpy`, `memmove`, `memset`, `memcmp`, `bcmp`) plus the `#![no_builtins]` attribute preventing LLVM's `LoopIdiomRecognize` pass from lowering a `memset` helper byte loop back into a self-recursive `jmpq *memset@GOTPCREL(%rip)` / `b memset`.

This package delivers: (i) a line-pinned primary-source audit across `rustc`, `compiler-builtins`, LLVM, and Anneal; (ii) an automated multi-target compiler and native execution probe (`support/probe_inline_asm_and_builtins.py` -> `support/probe_results.json`) confirming every operand constraint, `MemoryEffects` attribute, target reserved-register error, `branch-protection` attribute suppression on `naked_asm!`, `u128`/`i128` builtin call lowering, `CE1`/`CE2` sharpness miscompilations, and `#![no_builtins]` loop-idiom self-recursion on live `rustc 1.98.0-nightly (2026-05-31)` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`); and (iii) a standalone kernel-checked `Lean v4.34.1` formalization (`support/InlineAsmAndBuiltinsFraming.lean`) proving register-allocation/frame soundness, virtual-to-physical coalescing soundness, bidirectional `nostack` red-zone framing, both `CE1` and `CE2` sharpness theorems, constructive `HiLo64` `u128` `divmod128` correctness (`q * d + r = n ∧ r < d` for `0 < d`), and the `#![no_builtins]` `LoopIdiomRecognize` non-self-recursion invariant using only `Init` (`[propext]` and `[propext, Quot.sound]`, with zero `sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial def`, or `._unsafe_rec`).

## Applicability

These findings govern the interface between `rustc` HIR/MIR lowering, LLVM `InlineAsm` / `TargetLibraryInfo` lowering, the Rust sysroot `compiler-builtins` crate, and Lean 4 operational verification across the subjects identified in `REPORT.json`:

1. **Source reference subject (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**: Governs AST `InlineAsmOptions` / `InlineAsmOperand`, macro validation (`rustc_builtin_macros::asm`), HIR type checking (`rustc_hir_typeck::inline_asm`), target register/ABI definitions (`rustc_target::asm`), MIR construction (`TerminatorKind::InlineAsm`), SSA `codegen_naked_asm`, and LLVM IR lowering (`rustc_codegen_llvm::asm`, `attributes`).
2. **Executed compiler toolchain (`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (2026-05-31)`, LLVM `22.1.6`)**: Governs all compiled MIR, LLVM IR, assembly, `objdump` relocations, native x86-64 execution outputs (`CE1`, `CE2`), and the `2,878`-file sysroot scan recorded in `support/probe_results.json`.
3. **Runtime intrinsics subject (`rust-lang/compiler-builtins` @ `8fe310e552c1a24df0bd977e87756168fe396037`)**: Interprets `__udivti3` / `__umodti3` / `__udivmodti4` (`u128_div_rem`), `__multi3`, `__ashlti3` / `__lshrti3`, `#[mem_builtin]` (`memcpy`, `memmove`, `memset`, `memcmp`, `bcmp`), and `#![no_builtins]`.
4. **Backend lowering subject (`llvm/llvm-project` @ `984202b7bd448b1c8da65689ecd2dd27aa891175`)**: Governs `X86FrameLowering::has128ByteRedZone` and red-zone elimination, `PrologEpilogInserter` `Attribute::Naked` handling, `SelectionDAGBuilder::ExtraFlags`, and `TargetLibraryInfo` / `LoopIdiomRecognize` `"no-builtins"` gating.
5. **Verifier framework and theorem prover (`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613`, `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` `v4.34.1`)**: Defines how Anneal currently excludes `TerminatorKind::InlineAsm` at `Trusted/MirAst.lean` and establishes the Lean 4 mechanized model in `support/InlineAsmAndBuiltinsFraming.lean`.

Cross-target codegen observations directly cover `x86_64-unknown-linux-gnu` (ELF, SysV), `aarch64-unknown-linux-gnu` (ELF), `aarch64-apple-darwin` (Mach-O, reserved `x18`), `x86_64-pc-windows-msvc` (PE/COFF, Win64), and `riscv64gc-unknown-none-elf` (128-bit arithmetic lowering). Executable specimens (`CE1`, `CE2`) run natively on `x86_64-unknown-linux-gnu`; non-host targets are characterized via `rustc --emit=mir,llvm-ir,asm[,obj]` and upstream source inspection rather than hardware execution.

## Findings

### Layer Architecture Overview (`L1`–`L6`)

| Layer | Compiler / Runtime Boundary | Key Mechanism / Invariant | Primary Basis |
| :--- | :--- | :--- | :--- |
| `L1` | AST, macro expansion, HIR typeck, target reg validation | `InlineAsmOptions` 9-bit bitflags (`PURE`..`MAY_UNWIND`), mutual-exclusion checks, `clobber_abi` regclass output ban, target reserved-reg matrix (`rbp`, `rsp`, `rbx`, `ah`, `x19`, `x29`, `sp`, target-conditional `x18`) | source + execution |
| `L2` | Operand register constraints & coalescing (`out` vs. `lateout`) | `late = false` (`out`, `inout`) emits early-clobber `"=&"`; `late = true` (`lateout`, `inlateout`) emits `"="` allowing input/output register aliasing | normative + source + execution + derived |
| `L3` | `options(...)` effects, stack red zone, flags, memory, unwind | `alignstack` iff `!NOSTACK`; SysV `128`-byte red zone skipped only with `NoRedZone` or stack-touching frame; `MemoryEffects` lattice (`None`, `ReadOnly`, `InaccessibleMemOnly`, `ReadOnlyNotPure`) + `WillReturn` + implicit flag clobbers | source + execution |
| `L4` | `clobber_abi`, `#[unsafe(naked)]`, and `global_asm!` lowering | ABI volatile clobber expansion; `naked_asm!` compiles via `module asm` with no LLVM IR body, no `branch-target-enforcement` / PAC hints, and hidden visibility in `compiler_builtins` | source + execution |
| `L5` | `compiler-builtins` & `#![no_builtins]` idiom safety | Software `__udivti3`/`__umodti3`/`__divti3` libcalls vs. inlined `mul`/`shl`/`lshr`; `#![no_builtins]` emits LLVM `"no-builtins"` causing `TargetLibraryInfo` to disable `LoopIdiomRecognize` self-recursion | normative + source + execution |
| `L6` | Anneal TCB & MIR integration contract | `joshlf/anneal` maps `TerminatorKind::InlineAsm` to `.unsupported`; drop-in verification requires proving `L1`–`L5` framing and intrinsic equivalence (`divmod128_eq_div_mod`) across this cut | source + derived |

Basis: source + execution + derived

### `L1`: AST Options Lattice, Macro Validation, HIR Typeck, and Target Reserved Registers

`compiler/rustc_ast/src/ast.rs:2699-2720` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) defines `InlineAsmOptions(u16)` with nine flags: `PURE (1<<0)`, `NOMEM (1<<1)`, `READONLY (1<<2)`, `PRESERVES_FLAGS (1<<3)`, `NORETURN (1<<4)`, `NOSTACK (1<<5)`, `ATT_SYNTAX (1<<6)`, `RAW (1<<7)`, and `MAY_UNWIND (1<<8)`, restricting `GLOBAL_OPTIONS` and `NAKED_OPTIONS` identically to `ATT_SYNTAX | RAW`. At macro validation (`compiler/rustc_builtin_macros/src/asm.rs:177-259`), `rustc` statically enforces:

1. `NOMEM` and `READONLY` are mutually exclusive (`asm.rs:177-182`).
2. `PURE` and `NORETURN` are mutually exclusive (`asm.rs:183-188`).
3. `PURE` requires `NOMEM | READONLY` (`asm.rs:189-196`) and at least one concrete output (`have_real_output`, excluding discarded `_` outputs, `asm.rs:207, 225-227`).
4. `NORETURN` forbids outputs unless `Label` operands (`asm goto`) are present (`asm.rs:228-235`).
5. `MAY_UNWIND` forbids `Label` operands (`asm.rs:236-238`).
6. `clobber_abi(...)` is rejected in `global_asm!` / `naked_asm!` (`asm.rs:241-250`) and forbids reg-class outputs (`out(reg)`, `inout(reg)`, `lateout(reg)`, `inlateout(reg)`) in `asm!` (`asm.rs:251-259`) because automatic ABI register allocation conflicts with ABI-clobber expansion.

At HIR type checking (`compiler/rustc_hir_typeck/src/inline_asm.rs:450-460, 547-619`), every explicit named register passes through `reg.validate(...)`, while `const` operands are restricted to integers (`ty.is_integral()`, or thin pointers under `feature(asm_const_ptr)`) and `sym` operands must be `FnDef` (`SymFn`) or static (`SymStatic`). Across the target backends (`rustc_target/src/asm/{x86,aarch64,riscv}.rs`), specific registers are unconditionally or conditionally rejected so LLVM's frame pointer, stack pointer, base register, or platform ABI register cannot be corrupted. Live probe compilation (`support/probe_inline_asm_and_builtins.py`, section `compile_rejections`) reproduces all 11 diagnostics and the `aarch64` Linux-vs.-Darwin `x18` divergence:

| Probe Case | Target | Exit Code | Verbatim `rustc` Diagnostic (`support/probe_results.json`) / Source Rule |
| :--- | :--- | :---: | :--- |
| `x86_64_reserved_rbp` | `x86_64-unknown-linux-gnu` | `1` | `invalid register \`rbp\`: the frame pointer cannot be used as an operand for inline asm` (`x86.rs:341-342`) |
| `x86_64_reserved_rsp` | `x86_64-unknown-linux-gnu` | `1` | `invalid register \`rsp\`: the stack pointer cannot be used as an operand for inline asm` (`x86.rs:343-344`) |
| `x86_64_reserved_rbx` | `x86_64-unknown-linux-gnu` | `1` | `cannot use register \`bx\`: rbx is used internally by LLVM and cannot be used as an operand for inline asm` (`x86.rs:179-192`) |
| `x86_64_reserved_ah` | `x86_64-unknown-linux-gnu` | `1` | `cannot use register \`ah\`: high byte registers cannot be used as an operand on x86_64` (`x86.rs:166-176`) |
| `aarch64_reserved_x19` | `aarch64-unknown-linux-gnu` | `1` | `invalid register \`x19\`: x19 is used internally by LLVM and cannot be used as an operand for inline asm` |
| `aarch64_reserved_x29` | `aarch64-unknown-linux-gnu` | `1` | `invalid register \`x29\`: the frame pointer cannot be used as an operand for inline asm` |
| `aarch64_reserved_sp` | `aarch64-unknown-linux-gnu` | `1` | `invalid register \`sp\`: the stack pointer cannot be used as an operand for inline asm` |
| `aarch64_linux_x18_allowed` | `aarch64-unknown-linux-gnu` | `0` | Allowed (Linux does not reserve `x18` unless `+reserve-x18`, `aarch64.rs:74-98`) |
| `aarch64_darwin_x18_reserved` | `aarch64-apple-darwin` | `1` | `cannot use register \`x18\`: x18 is a reserved register on this target` (`aarch64.rs:81, 93-95`) |
| `clobber_abi_with_regclass_out` | `x86_64-unknown-linux-gnu` | `1` | `asm with \`clobber_abi\` must specify explicit registers for outputs` (`asm.rs:251-258`) |
| `pure_without_nomem_readonly` | `x86_64-unknown-linux-gnu` | `1` | `the \`pure\` option must be combined with either \`nomem\` or \`readonly\`` (`asm.rs:189-196`) |
| `nomem_and_readonly_conflict` | `x86_64-unknown-linux-gnu` | `1` | `the \`nomem\` and \`readonly\` options are mutually exclusive` (`asm.rs:177-182`) |

In the live toolchain sysroot scan (`rustc 1.98.0-nightly`, `2,878` non-test/vendor `.rs` files in `library/`), there are `370` asm invocations (`324` `asm!`, `17` `naked_asm!`, `29` `global_asm!`) distributed across `stdarch` (`197`), `compiler-builtins` (`135`), `std` (`29`), `std_detect` (`6`), `core` (`2`), and `unwind` (`1`), with option counts (`pure`: `193`, `nomem`: `192`, `readonly`: `25`, `preserves_flags`: `102`, `nostack`: `303`, `noreturn`: `4`, `may_unwind`: `0`, `att_syntax`: `19`, `raw`: `26`). This aligns closely with a baseline `1.99.1` census (`58cf8f9c35b355199727627d07ae34a4e2846d67`: `1,666` files, `330` total invocations: `272` `asm!`, `29` `naked_asm!`, `29` `global_asm!`, including `58` active `x86_64` Linux and `18` active `aarch64` Linux sites).

Basis: source + execution

### `L2` and `C1`/`C2` (`CE1`): Operand Early-Clobber (`out`) vs. Late-Out (`lateout`) Register Aliasing

In `compiler/rustc_codegen_llvm/src/asm.rs:106, 120` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), operand constraint strings directly encode whether an output may share a physical register with any input:

- **`Out` and `InOut` (`late == false`)**: `let prefix = if late { "=" } else { "=&" };`. The `"=&"` early-clobber modifier forbids LLVM's register allocator from assigning the output physical register to any live input operand, guaranteeing disjointness throughout the multi-instruction template. For `inout(reg)` (`!late`), the matching input constraint emits a tied index (`constraints.push(format!("{}", op_idx[&idx]))`, `asm.rs:160`), yielding `"=&r,0"`.
- **`LateOut` and `InLateOut` (`late == true`)**: Emits `"="` without `&` (`"=r"` or tied `"=r,0"` for regclass `inlateout(reg)`, `asm.rs:157-161`). For fixed register `inlateout("ax")` on `x86_64` or `inlateout("x0")` on `aarch64`, `rustc` explicitly duplicates the register constraint (`"={ax},{ax}"` and `"={x0},{x0}"`, `asm.rs:157-159`) rather than using a numeric back-reference, matching Clang's convention.
- **`const` and `sym` operands**: Compile-time scalar `ConstScalar::Int` values are formatted directly into the assembly template string without an LLVM input operand (`asm.rs:164`), whereas `ConstScalar::Ptr` and `sym helper_target` emit `"s"` input constraints (`"=&r,s"` with `${1:c}` on x86-64 ELF, `R_X86_64_PC32 helper_target-0x4` in object disassembly, and `@PAGE`/`@PAGEOFF` on `aarch64-apple-darwin`, confirmed in `probe_sym_and_const`).

Live `rustc` IR and native execution on `support/specimens/ce1_lateout_aliasing.rs` demonstrate **`CE1` (sharpness of early-clobber omission)** at both `-C opt-level=0` and `-C opt-level=2`:

| Specimen Function | Constraint String Emitted | x86-64 Machine Code (`support/specimens/ce1_lateout_aliasing.s`) | Native Runtime Output (`42` input) |
| :--- | :--- | :--- | :--- |
| `buggy_lateout_zero_add` (`lateout(reg)`) | `"=r,r,~{dirflag},~{fpsr},~{flags}"` | `movl $0, %eax; addl %eax, %eax` | `LATEOUT=0` (corrupted) |
| `safe_early_out_zero_add` (`out(reg)`) | `"=&r,r,~{dirflag},~{fpsr},~{flags}"` | `movl $0, %ecx; addl %eax, %ecx; movl %ecx, %eax` | `OUT=42` (preserved) |

In `support/InlineAsmAndBuiltinsFraming.lean`, theorem `virtual_to_physical_coalescing_soundness` (`lines 1003-1037`, `[propext, Quot.sound]`) proves that for any pure register body (`checkPureRegBody`) satisfying `checkInlineAsmContract` and distinct output allocations (`checkPairwiseDistinctPhys`), physical register execution agrees pointwise with unaliased virtual-register execution even when `lateOutRegs` coalesces onto `inRegs`—*provided* every coalesced pair `(lo, iv)` satisfies `readBeforeFirstWrite lo iv code = true` (every instruction reads `iv` strictly before any first write to `lo`). Theorem `ce1_lateout_aliasing_bug_and_earlyout_fix` (`lines 1075-1097`, `[propext, Quot.sound]`) formally establishes both sides: `readBeforeFirstWrite 1 0 ce1Code = false`, `ce1AllocBad` corrupts `42` into `0`, while `ce1EarlyOutContract` (`earlyOutRegs := [1]`) rejects `ce1AllocBad` and guarantees `(execInsns ce1Code alloc s).gpr (alloc 1) = val` for *all* valid allocations `alloc` and inputs `val`.

Basis: normative + source + execution + derived

### `L3` and `C2` (`CE2`): `options(...)` Effect Lattice, Implicit Clobbers, and SysV `128`-Byte Red-Zone Framing

Inspecting `compiler/rustc_codegen_llvm/src/asm.rs:258-377` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `llvm/lib/CodeGen/SelectionDAG/SelectionDAGBuilder.cpp:10371-10382`, and `llvm/lib/Target/X86/X86FrameLowering.cpp:1569-1577, 1882-1895` (`984202b7bd448b1c8da65689ecd2dd27aa891175`), alongside live IR outputs (`probe_opts_*`), establishes the exact semantics of every `options(...)` bit:

| `asm!` Options | LLVM `asm` Keywords & Implicit Clobbers (`x86_64` / `aarch64`) | LLVM Call Attributes (`asm.rs:364-377`) | Compiler Effect / CSE & Stack Frame Meaning |
| :--- | :--- | :--- | :--- |
| `(default)` | `asm sideeffect alignstack ... ~{dirflag},~{fpsr},~{flags},~{memory}` (`~{cc},~{memory}` on aarch64) | `{ nounwind }` (`no MemoryEffects`, no `willreturn`) | Prevents red-zone use (`sub rsp` in leaf callers if needed), acts as full memory/MMIO barrier, cannot be DCE/CSE eliminated |
| `options(nostack)` | Drops `alignstack`; keeps `sideeffect`, flags, `~{memory}` | `{ nounwind }` | Asserts asm does not read/write/modify stack/red zone; allows LLVM to place leaf locals in `[rsp - 128, rsp)` |
| `options(preserves_flags, nostack)` | Drops `~{dirflag},~{fpsr},~{flags}` (x86-64) and `~{cc}` (aarch64); keeps `~{memory}` | `{ nounwind }` | Caller condition/direction/FP status flags remain live across the asm block |
| `options(nomem, nostack)` | Drops `~{memory}`; retains `sideeffect` and flag clobbers | `memory(inaccessiblemem: readwrite)` (`InaccessibleMemOnly`) | Asserts no read/write of Rust-accessible memory, while still modeling non-memory I/O (`in`/`out`, syscalls) via `sideeffect` + `inaccessiblemem` |
| `options(readonly, nostack)` | Retains `~{memory}` string and `sideeffect` | `memory(read, inaccessiblemem: readwrite)` (`ReadOnlyNotPure`) | Permits reads of accessible memory while forbidding writes; retains `sideeffect` + `inaccessiblemem: readwrite` so it is not pure |
| `options(pure, readonly, nostack)` | Drops `sideeffect`; retains `~{memory}` | `willreturn memory(read)` | Safe for DCE if outputs unused and CSE across identical inputs; may still read memory |
| `options(pure, nomem, nostack)` | Drops `sideeffect` and `~{memory}`; only implicit flag clobbers remain | `willreturn memory(none)` | Pure functional expression (`probe_opts_pure_nomem_dce_cse`: 3 MIR `asm!` calls collapse to 1 LLVM `tail call` in IR and asm!) |
| `options(noreturn)` | Retains `sideeffect alignstack` | `noreturn` attr + MIR `-> unwind unreachable` | Never falls through to successor basic block |
| `options(may_unwind, nostack)` | Emits `invoke void asm sideeffect ... unwind "..."` in LLVM IR | MIR `-> [return: bb1, unwind: bb3]` + LSDA cleanup pad (`Drop`) | Unwinding from asm invokes Rust cleanup destructors |

On `x86_64` non-Win64 targets (`X86FrameLowering::has128ByteRedZone`, `X86FrameLowering.cpp:1569-1577, 1882-1895`), leaf functions without calls, stack probes, or stack realignment may store locals directly in `[rsp - 128, rsp)` without emitting `subq $N, %rsp`—unless stack frames force allocation or `alignstack` / stack objects require adjustment. When an `asm!` statement omits `nostack`, `rustc` passes `alignstack` (`asm.rs:333`, mapped to `InlineAsm::Extra_IsAlignStack` in `SelectionDAGBuilder.cpp:10375-10376`). On `support/specimens/ce2_redzone_nostack.rs` (`CE2`, `-C opt-level=2`):

- `leaf_with_nostack` (`options(nostack)` around `push {s}; push {s}; pop {t}; pop {t}`): omits stack allocation (`movq %rdi, -16(%rsp); movq %rsi, -8(%rsp)` followed directly by `pushq %rax`), causing the pushes to overwrite `[rsp - 8]` and `[rsp - 16]`.
- `leaf_without_nostack` (default `alignstack`): emits `subq $24, %rsp` before saving locals at `8(%rsp)` / `16(%rsp)`, isolating them below `rsp` so `pushq %rax` does not touch caller/local slots.
- Live execution stdout (`support/probe_results.json`): `EXPECTED=0x444444444444cccc NOSTACK=0x0 WITHOUT_NOSTACK=0x444444444444cccc CLOBBERED=true`.

Note an important precision on `CE2` framing established by our mechanization: LLVM's `alignstack` / `X86FrameLowering` prevents *leaf-local red-zone placement inside the containing function itself*; if `options(nostack)` were falsely asserted when inline asm pushes onto the stack (even balanced `push`/`pop`), the leaf function's red-zone locals `[rsp - 16]` / `[rsp - 8]` are overwritten. In `support/InlineAsmAndBuiltinsFraming.lean`:

- `registerAlloc_and_frame_soundness` (`lines 566-619`, `[propext, Quot.sound]`) proves that `checkInlineAsmContract c alloc = true` guarantees: (1) unwritten GPR preservation, (2) ABI-non-clobbered SIMD preservation, (3) flags preservation when `c.opts.preservesFlags = true`, (4) `rsp` and `128`-byte red-zone preservation when `c.opts.nostack = true`, (5) `rsp` and red-zone preservation under balanced stack pushes (`checkBalancedStack`) *when* the prologue allocates below the red zone (`execFramed true`), (6) `heapMem` preservation under `nomem ∨ readonly`, and (7) `hwCsrState` preservation under `pure ∧ nomem`.
- `nostack_redzone_iff_for_push_pop` (`lines 629-658`, `[propext]`) proves the sharp bidirectional equivalence: a leaf caller's `[rsp - 1]` red-zone word is preserved across `push rax; pop rax` *if and only if* `nostackFlag = false`.
- `ce2_nostack_redzone_clobber_and_default_fix` (`lines 1117-1135`, `[propext]`) proves that concrete `ce2State 100 0x444444444444cccc` evaluates to `0` (`0 ≠ ce2Canary`) when `nostack` is asserted (`execFramed false`), whereas omitting `nostack` (`execFramed true`) preserves `canary` for *every* `rsp0 ≥ 17` and `canary : Nat`.

Basis: source + execution + derived

### `L4`: `clobber_abi(...)`, `#[unsafe(naked)] naked_asm!`, and `global_asm!` Lowering

Inspection of `compiler/rustc_target/src/asm/mod.rs:1082-1215` (`58cf8f9c35b355199727627d07ae34a4e2846d67`), `compiler/rustc_codegen_ssa/src/mir/naked_asm.rs:18-166`, and `compiler/rustc_codegen_llvm/src/{asm.rs:410-505, attributes.rs:534-558}`, corroborated by cross-target IR probes (`probe_clobber_abi_*`, `aarch64_branch_protection_naked_vs_normal`), establishes four critical backend invariants:

1. **ABI Clobber Set Expansion and Vector Aliasing**:
   - `x86_64` SysV (`clobber_abi("C")` / `"sysv64"` on Linux): marks `lateout` on `{ax,cx,dx,si,di,r8..r11,xmm0..15}` and clobbers `~{xmm16..31},~{k0..7},~{st0..7},~{tmm0..7}` plus flags and `memory` (mirrored identically in MIR with `mm0..7`, `zmm16..31`, etc.).
   - `x86_64` Win64 (`clobber_abi("win64")`, or `"C"` on `x86_64-pc-windows-msvc`): excludes `di` and `si` (which are callee-saved on Win64), while *still* marking `xmm6..xmm15` as clobbered (`={xmm6}..={xmm15}`) because LLVM has no partial-clobber representation and the upper bits of `ymm6..ymm15` are volatile (`mod.rs:1128-1131`).
   - `aarch64`: Linux `clobber_abi("C")` clobbers `w0..w18,w30`, whereas `aarch64-apple-darwin` uses `AArch64NoX18` (`mod.rs:1161-1177`) omitting `={w18}` because `x18` is platform-reserved. Likewise `v0..v31` are marked clobbered in full (`={q0}..={q31}`) even though the low 64 bits of `v8..v15` are ABI-callee-saved (`mod.rs:1149-1150, 1167-1168`), safely over-approximating clobbers for verifier soundness.
2. **LLVM Identical Function Merging vs. `asm` IR**: Notice on `x86_64-unknown-linux-gnu` / `x86_64-pc-windows-msvc`, probes `probe_clobber_abi_c` and `probe_clobber_abi_sysv64` (on Linux) / `probe_clobber_abi_win64` (on Windows) resolve to the exact same constraint string; a verifier checking source semantics must inspect pre-opt/MIR or unmerged `InlineAsm` constraints rather than post-opt alias symbols.
3. **`#[unsafe(naked)]` + `naked_asm!` Compilation Path**: `codegen_naked_asm` (`naked_asm.rs:18-58`) does **not** lower through normal LLVM `Function` IR blocks (`attributes.rs:534-537`: `if codegen_fn_attrs.flags.contains(NAKED) { // do nothing ... LLVM's support for naked functions is not used }`). Instead, `rustc` wraps the body with symbol prefix/suffix directives (including forcing `Visibility::Hidden` when `tcx.is_compiler_builtins(LOCAL_CRATE)`, `naked_asm.rs:163-165`) and calls `codegen_global_asm`, emitting module-level inline assembly (`module asm "..."`) directly into the assembler. LLVM `PrologEpilogInserter.cpp:254-255` checks `Attribute::Naked` only when LLVM generates a function, whereas `rustc` bypasses LLVM's `Function` body generation altogether (`naked_id_llvm == {}` while `module_asm` emits `.pushsection .text.naked_id...` and `.globl naked_id`).
4. **CFI/Branch-Protection Hazard on `naked_asm!` and `global_asm!`**: Compiling with `-Z branch-protection=bti,pac-ret` emits `"branch-target-enforcement" "sign-return-address"="non-leaf" "sign-return-address-key"="a_key"` and `hint #34` (`BTI C`) on `normal_add1`, whereas `#[unsafe(naked)] naked_id` omits `hint #34` completely (`support/probe_results.json`, `aarch64_branch_protection_naked_vs_normal`), meaning indirect-call landing-pad BTI or PAC signing inside naked/global asm functions is solely the author's responsibility. Similarly, on `x86_64`/`x86`, `codegen_global_asm` wraps templates with `.intel_syntax\n ... \n.att_syntax\n` unless `options(att_syntax)` is specified (`asm.rs:425-500`), protecting subsequent codegen units from persistent syntax-mode corruption.

Basis: source + execution + derived

### `L5` and `C1`/`C2`: `compiler-builtins` Intrinsics (`__udivti3` / `__umodti3` / `mem*`) and `#![no_builtins]` LoopIdiom Self-Recursion

Across `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, and `riscv64gc-unknown-none-elf`, compiling `support/specimens/builtins_128bit_ops.rs` (`-C opt-level=2`) shows a sharp lowering split between software runtime calls and inlined target instructions (`support/probe_results.json`):

- **`u128` / `i128` Division & Remainder Lower to Runtime Calls**: `a / b` (`u128`), `a % b` (`u128`), and `a / b` (`i128`) lower on *all three* architectures to runtime symbols `__udivti3` (`R_X86_64_GOTPCREL __udivti3-0x4`, `bl __udivti3`, `call __udivti3`), `__umodti3`, and `__divti3` after generating inline zero-divisor (`panic_const_div_by_zero` / `panic_const_rem_by_zero`) and signed overflow (`MIN / -1`, `panic_const_div_overflow`) checks. In `rust-lang/compiler-builtins` (`8fe310e552c1a24df0bd977e87756168fe396037`, `compiler-builtins/src/int/udiv.rs:159-199`), `__udivti3`, `__umodti3`, and `__udivmodti4` delegate to `u128_div_rem(n, d)` (`specialized_div_rem/mod.rs:11-44, 170-217`), which selects `impl_asymmetric!` using inline `asm!("div {0}", in(reg) div, inlateout("rax") duo_lo => quo, inlateout("rdx") duo_hi => rem, options(pure, nomem, nostack))` when `x86_64` arch features are enabled, or `impl_trifecta!` / `impl_delegate!` otherwise.
- **`u128` Multiplication & Shifts Inline Directly**: On all three targets, `wrapping_mul`, `wrapping_shl`, and `wrapping_shr` emit zero calls to `__multi3`, `__ashlti3`, or `__lshrti3` (`llvm_calls == []`), lowering to `mulq`/`imulq`, `shldq`/`shlq`, `shrdq`/`shrq` (x86-64); `umulh`/`mul`, `lsr`/`lsl` (aarch64); and `mul`/`mulhu`, `sll`/`srl` (riscv64). Any verified drop-in `rustc` backend that emits library calls for `128`-bit arithmetic on targets without widening ops must treat `__multi3`/`__ashlti3`/`__lshrti3` (`int/mul.rs`, `int/shift.rs`) with the same formal specification as `__udivti3`/`__umodti3`.
- **Constructive Lean 4 `u128` Division-Remainder Verification**: In `support/InlineAsmAndBuiltinsFraming.lean`, `divmod128` (`lines 1138-1775`) implements a `128`-step MSB-to-LSB binary restoring division-remainder algorithm purely over bounded `64`-bit limb pairs `HiLo64` (`hi < 2^64 ∧ lo < 2^64`). Theorems `divmod128_sound` (`lines 1748-1764`) and `divmod128_eq_div_mod` (`lines 1765-1775`) prove kernel-checked (`[propext]` only): for every well-formed `n d : HiLo64` with `0 < d.toNat`, `(udivti3 n d)` and `(umodti3 n d)` remain well-formed `HiLo64` pairs satisfying `(udivti3 n d).toNat * d.toNat + (umodti3 n d).toNat = n.toNat`, `(umodti3 n d).toNat < d.toNat`, `(udivti3 n d).toNat = n.toNat / d.toNat`, and `(umodti3 n d).toNat = n.toNat % d.toNat`.
- **`#![no_builtins]` and LLVM `LoopIdiomRecognize` Self-Recursion Hazard**:
  In `llvm/lib/Transforms/Scalar/LoopIdiomRecognize.cpp:340-355` (`984202b7bd448b1c8da65689ecd2dd27aa891175`), LLVM checks `HasMemset = TLI->has(LibFunc_memset)` and `HasMemcpy = TLI->has(LibFunc_memcpy)`. In `llvm/include/llvm/Analysis/TargetLibraryInfo.h:298-299`, `if ((*F)->hasFnAttribute("no-builtins")) disableAllFunctions();`. Meanwhile, `rustc` propagates `CodegenFnAttrFlags::NO_BUILTINS` to LLVM `"no-builtins"` (`compiler/rustc_codegen_llvm/src/attributes.rs:517-519`), and `rust-lang/compiler-builtins` sets crate-root `#![no_builtins]` (`compiler-builtins/src/lib.rs:15`).
  Crucially, compiling our clean A/B specimens (`support/specimens/memcpy_without_no_builtins.rs` vs. `memcpy_with_no_builtins.rs`) proves empirically across both `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`:
  1. **Without `#![no_builtins]`**: `set_bytes_helper` (the helper called by `#[no_mangle] extern "C" fn memset`) lacks `"no-builtins"`, so LLVM's `LoopIdiomRecognize` replaces its byte-store loop with `@llvm.memset` (`llvm_calls_llvm_memset: true`), lowering in assembly to `jmpq *memset@GOTPCREL(%rip)` on x86-64 and a tail/direct `memset` branch on AArch64 (`asm_self_recursive_memset: true`, preserved in `support/specimens/memcpy_loop_idiom_hazard.s`). Calling `memset` would enter infinite self-recursion (`memset` -> `set_bytes_helper` -> `memset` -> stack/tail loop). (Fixed-count `4096`-byte `copy_forward_helper` instead unrolls/vectorizes into `movups` / `ldp+stp` in this specimen.)
  2. **With `#![no_builtins]`** (`#![feature(rustc_attrs)] #![no_builtins]`): Both `memset`/`memcpy` and internal helpers (`set_bytes_helper`, `copy_forward_helper`) receive LLVM string attribute `"no-builtins"` (`has_llvm_no_builtins_attr: true`, `has_helper_llvm_no_builtins_attr: true`), suppressing `@llvm.memset`/`@llvm.memcpy` recognition (`llvm_calls_llvm_memset: false`, `asm_self_recursive_memset: false`) and lowering the loop to vectorized `punpcklbw`/`movdqu` (x86-64) or `dup`/`stp q0, q0` (aarch64). Theorem `noBuiltins_prevents_idiom_self_recursion` (`support/InlineAsmAndBuiltinsFraming.lean:1798-1806`, `[propext]`) mechanizes this exact `LoopIdiomRecognize` guard invariant (`ctx.hasNoBuiltins = true → lirTransformsLoopToCall ctx = none`).

Basis: normative + source + execution + derived

### `L6`: Anneal Drop-In `rustc` Verification Integration Boundary

Inspecting `joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`:

- `trusted/lean/Trusted/MirAst.lean:782-795` explicitly collapses `TerminatorKind::InlineAsm` (alongside `UnwindTerminate`, `Drop`, indirect `Call`, `TailCall`, `Yield`, `CoroutineDrop`, `FalseEdge`, `FalseUnwind`) into `.unsupported`.
- `trusted/lean/Trusted/MirSemantics.lean:1568-1569` evaluates `.unsupported` to `.fault .unsupported`, causing `BodyVerified` (`lines 1748-1758`) to fail any safety proof where an `asm!` terminator is reachable.
- `trusted/rustc-capture/src/driver.rs:45-84` binds the compiler capture driver tightly to an exact `COMPILER_VERSION` string check before running `after_analysis`.

To extend a drop-in verified `rustc` without unsoundly widening the kernel TCB, three verifier requirements follow directly from `L1`–`L5`: (1) inline-assembly blocks must carry machine-checkable pre/post frame contracts preserving all disjoint `in`/`earlyOut`/`lateOut` constraints (with `readBeforeFirstWrite` verified whenever `lateout`/`inlateout` coalesces inputs), `clobber_abi` over-approximations, and `options(...)` side-effect bounds (`nostack` vs. red zone, `preserves_flags`, `nomem`/`readonly`/`pure`); (2) `naked_asm!` / `global_asm!` artifacts cannot rely on LLVM's function-level CFI/BTI/PAC attributes; and (3) any linked `compiler-builtins` crate or replacement intrinsics library must carry verified functional equivalence proofs (such as `divmod128_eq_div_mod` for `__udivti3`/`__umodti3`) AND be compiled with `"no-builtins"` (`#![no_builtins]` or `-C no-builtins`) across all helper modules so backend idiom passes cannot synthesize cyclic self-calls.

Basis: source + derived

## Boundaries

The following negative space and non-claims hold strictly from our examined evidence (`FORMAT.md` categories):

1. **Non-executed target ISAs (`riscv64`, `aarch64`, `x86_64-pc-windows-msvc`, `aarch64-apple-darwin`)**: **not examined** dynamically (compiled statically with `rustc --emit=mir,llvm-ir,asm[,obj]` on the `x86_64-unknown-linux-gnu` host; hardware/QEMU native binary execution was limited to `CE1` and `CE2` on `x86_64-unknown-linux-gnu`).
2. **Additional runtime intrinsics beyond `u128`/`i128` div-rem, mul/shift, and `mem*` (`__multi3`, `__udivsi3`, `__aeabi_*`, soft-float `float/*`, atomic/sync `sync/*`, `f16`/`f128`)**: **not examined** in Lean mechanization or cross-target IR probes; only `__udivti3` / `__umodti3` (with `mul`/`shl`/`lshr` and `mem*` `#![no_builtins]` probes) were probed and modeled formally here, and the upstream `u128` trifecta / asymmetric C/asm implementations themselves were **not examined** line-by-line beyond `mod.rs` + `udiv.rs`.
3. **Full x86/ARM ISA instruction semantics and asynchronous signals/interrupts**: **not examined** / **unsupported** in our Lean model (`InlineAsmAndBuiltinsFraming.lean` uses a structured `AsmInsn` core covering GPR moves/adds, stack `push`/`pop`, heap loads/stores, flag writes, CSR writes, and ABI clobber calls, plus a simplified word-addressed `128`-byte red zone `[rsp - 16, rsp)`, rather than full decoded x86-64/AArch64 machine-code instruction semantics or OS signal-handler stack framing).
4. **32-bit x86 `ah`/`ch`/`dh`/`bh`, `bx`, `esi` rules and Tier-2/Tier-3 architectures**: **not examined** by compilation probes on this host; `x86.rs:166-209` indicates `high_byte` and `rbx_reserved` return `Ok(())` on `InlineAsmArch::X86` while `esi_reserved` rejects `esi` on `X86`, which was observed in source only.
5. **`anneal` Lean MIR execution of `TerminatorKind::InlineAsm` today**: **unsupported** at `joshlf/anneal` `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`Trusted/MirAst.lean:782-795`, `Trusted/MirSemantics.lean:1568-1569`), where inline assembly maps to `.unsupported` and faults unconditionally.
6. **`pure` + `nomem` execution of instructions with visible side effects, or `options(nostack)` inside arbitrary non-leaf functions**: **known not to apply** — `CE2` (`leaf_with_nostack`) specifically exploits leaf red-zone placement (`X86FrameLowering::has128ByteRedZone`, `X86FrameLowering.cpp:1569-1577, 1882-1895`); on targets without a red zone (such as `x86_64-pc-windows-msvc` where `IsWin64CC` disables `has128ByteRedZone`, or `aarch64` ABI `sp` alignment faults if hardware `sp` becomes non-16-byte-aligned during interrupts/signals), failure mechanics differ.
7. **Arbitrary `rustc` LLVM IR optimization stability across unreleased nightlies (`1.98.0-nightly` vs. `1.99.1`)**: **unknown** whether future `LoopIdiomRecognize` thresholds or `SelectionDAG` heuristics alter fixed-size `4096`-byte unrolling vs. `@llvm.memcpy` emission across different pointer aliasing or array sizes.

## Evidence

### Upstream Primary Sources (Line-Pinned)

- **`joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`)**:
  - `trusted/lean/Trusted/MirAst.lean:782-795`: `.unsupported` doc and `TerminatorKind` inductive mapping (`InlineAsm`).
  - `trusted/lean/Trusted/MirSemantics.lean:1537-1569, 1730-1758`: `evalTerminator` fault `.unsupported`; `BodyStaticAdmitted` / `BodyVerified`.
  - `trusted/rustc-capture/src/driver.rs:25-152`: pinned `COMPILER_VERSION` guard and `after_analysis` callback.
- **`rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_ast/src/ast.rs:2699-2720, 2820-2840`: `InlineAsmOptions` bitflags (`GLOBAL_OPTIONS`, `NAKED_OPTIONS`) and `InlineAsmOperand`.
  - `compiler/rustc_builtin_macros/src/asm.rs:177-259`: option conflicts (`nomem`/`readonly`, `pure`/`noreturn`, `pure` without `nomem`/`readonly`), `noreturn` output check, `may_unwind` label check, `clobber_abi` ban on `global_asm!`/`naked_asm!` and regclass outputs.
  - `compiler/rustc_hir_typeck/src/inline_asm.rs:450-460, 547-620`: `reg.validate`, `const` integer/thin-ptr checks, `sym` fn/static checks.
  - `compiler/rustc_target/src/asm/x86.rs:166-215, 341-346`: `high_byte`, `rbx_reserved`, `#error` for `bp`/`sp`/`ip`.
  - `compiler/rustc_target/src/asm/aarch64.rs:74-98`: `target_reserves_x18` (`Android`, `Fuchsia`, `Ohos`, `is_like_darwin`, `is_like_windows`, `+reserve-x18`).
  - `compiler/rustc_target/src/asm/mod.rs:1082-1220`: `InlineAsmClobberAbi::clobbered_regs` for `X86`, `X86_64SysV`, `X86_64Win` (including `ymm6-ymm15` rationale for `xmm6-xmm15`), `AArch64`, `AArch64NoX18`, `Arm64EC`, `Arm`.
  - `compiler/rustc_codegen_ssa/src/mir/block.rs:230-332` and `naked_asm.rs:18-166`: `do_inlineasm`, `codegen_naked_asm`, `inline_to_global_operand`, `Visibility::Hidden` on `compiler_builtins` crates.
  - `compiler/rustc_codegen_llvm/src/asm.rs:95-175, 258-385, 410-505` and `attributes.rs:517-558`: `"="` vs. `"=&"`, fixed vs. regclass `inlateout`, implicit clobbers (`~{cc}`, `~{dirflag},~{fpsr},~{flags}`, `~{memory}`), `volatile`, `alignstack`, `MemoryEffects` + `WillReturn`, `codegen_global_asm` syntax wrapping, `"no-builtins"`, `NAKED` opt-out, AArch64 BTI/PAC attributes.
- **`rust-lang/compiler-builtins` (`8fe310e552c1a24df0bd977e87756168fe396037`)**:
  - `compiler-builtins/src/lib.rs:15`: crate-wide `#![no_builtins]`.
  - `compiler-builtins/src/int/udiv.rs:159-199` and `int/specialized_div_rem/mod.rs:11-44, 170-217`: `__udivti3`, `__umodti3`, `__udivmodti4`, `impl_asymmetric!` `u128_by_u64_div_rem` `asm!("div ...")`.
  - `compiler-builtins/src/int/{mul.rs:7-32,160-205, shift.rs:3-115}`: `__multi3`, `__ashlti3`, `__ashrti3`, `__lshrti3` implementations.
  - `compiler-builtins/src/mem/{mod.rs:17-60, impls.rs:22-85}`, `src/macros.rs:351-420`, `src/{x86_64.rs:6-30, aarch64.rs:1-17}`: `#[mem_builtin]`, weak unmangled wrappers, naked custom-ABI stack probes (`___chkstk_ms`, `__chkstk`).
- **`llvm/llvm-project` (`984202b7bd448b1c8da65689ecd2dd27aa891175`)**:
  - `llvm/lib/Transforms/Scalar/LoopIdiomRecognize.cpp:340-355, 526-535` & `llvm/include/llvm/Analysis/TargetLibraryInfo.h:293-306`: `"no-builtins"` -> `disableAllFunctions()` disabling `LibFunc_memset` / `LibFunc_memcpy` idiom lowering.
  - `llvm/lib/Target/X86/X86FrameLowering.cpp:1569-1577, 1882-1895, 2510-2539`: `has128ByteRedZone`, leaf red-zone subtraction, `X86_INTR` `CLD` emission for inline asm.
  - `llvm/lib/CodeGen/PrologEpilogInserter.cpp:254-255`: `if (!F.hasFnAttribute(Attribute::Naked)) insertPrologEpilogCode(MF);`.
  - `llvm/lib/CodeGen/SelectionDAG/SelectionDAGBuilder.cpp:10371-10382`: `ExtraFlags` propagating `hasSideEffects`, `isAlignStack`, `canThrow`, dialect.

### Package Support Material and Executed Verification Receipts (`2026-11-21`)

All probe scripts, Rust source specimens, extracted assembly excerpts, machine-readable probe results, and Lean 4 proofs are preserved inside this package:

1. **Multi-target compiler/execution probe (`support/probe_inline_asm_and_builtins.py` -> `support/probe_results.json`)**:
   - Host toolchain: `rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`), compiled with `--remap-path-prefix` for reproducible, workspace-independent output.
   - Specimens preserved in `support/specimens/`:
     - `constraint_and_options_matrix.rs`: cross-target operand, `options(...)`, `clobber_abi(...)`, `naked_asm!`, and `global_asm!` matrix compiled for `x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, plus AArch64 `-Z branch-protection=bti,pac-ret` naked-vs-normal probe.
     - `ce1_lateout_aliasing.rs` & `ce1_lateout_aliasing.s`: executes both `-C opt-level=0` and `-C opt-level=2` outputting `LATEOUT=0 OUT=42`.
     - `ce2_redzone_nostack.rs` & `ce2_redzone_nostack.s`: executes at `-C opt-level=2` outputting `EXPECTED=0x444444444444cccc NOSTACK=0x0 WITHOUT_NOSTACK=0x444444444444cccc CLOBBERED=true`.
     - `builtins_128bit_ops.rs`: verifies `__udivti3` / `__umodti3` / `__divti3` libcalls vs. inlined `mul`/`shl`/`lshr` across `x86_64`, `aarch64`, and `riscv64gc`.
     - `memcpy_without_no_builtins.rs`, `memcpy_with_no_builtins.rs`, and `memcpy_loop_idiom_hazard.s`: demonstrates `memset` -> `set_bytes_helper` self-recursion (`jmpq *memset@GOTPCREL(%rip)` / `b memset`) vs. suppression under `#![no_builtins]` (`has_llvm_no_builtins_attr: true`, `asm_self_recursive_memset: false`).
2. **Kernel-checked Lean 4 mechanization (`support/InlineAsmAndBuiltinsFraming.lean`, `1,815` lines, Lean `v4.34.1` @ `5045d0056413266e57c625dcd7c365b10e377c52`)**:
   - Verified with `lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/InlineAsmAndBuiltinsFraming.lean` (exit code `0`, `0` warnings).
   - Kernel `#print axioms` receipts:
     - `InlineAsmAndBuiltinsFraming.registerAlloc_and_frame_soundness`: `[propext, Quot.sound]`
     - `InlineAsmAndBuiltinsFraming.nostack_redzone_iff_for_push_pop`: `[propext]`
     - `InlineAsmAndBuiltinsFraming.virtual_to_physical_coalescing_soundness`: `[propext, Quot.sound]`
     - `InlineAsmAndBuiltinsFraming.ce1_lateout_aliasing_bug_and_earlyout_fix`: `[propext, Quot.sound]`
     - `InlineAsmAndBuiltinsFraming.ce2_nostack_redzone_clobber_and_default_fix`: `[propext]`
     - `InlineAsmAndBuiltinsFraming.divmod128_sound`: `[propext]`
     - `InlineAsmAndBuiltinsFraming.divmod128_eq_div_mod`: `[propext]`
     - `InlineAsmAndBuiltinsFraming.noBuiltins_prevents_idiom_self_recursion`: `[propext]`
   - Forbidden-axiom / forbidden-tactic scan confirms `0` occurrences anywhere in `support/InlineAsmAndBuiltinsFraming.lean` of `sorry`, `Classical.choice`, `omega`, `bv_decide`, `native_decide`, `partial def`, or `._unsafe_rec`.

## Revalidation

To revalidate every finding, empirical measurement, and Lean 4 proof in this report against a new `rustc`, `compiler-builtins`, LLVM, or Lean 4 revision:

1. **Re-run the live compiler & native execution probe** from this package directory:
   ```bash
   python3 support/probe_inline_asm_and_builtins.py
   ```
   Verify that `probe_results.json` preserves:
   - `CE1 O0` and `CE1 O2`: `LATEOUT=0 OUT=42` (`"=r,r..."` vs. `"=&r,r..."`);
   - `CE2 O2`: `EXPECTED=0x444444444444cccc NOSTACK=0x0 WITHOUT_NOSTACK=0x444444444444cccc CLOBBERED=true` (`leaf_with_nostack_has_sub_rsp: false`, `leaf_without_nostack_has_sub_rsp: true`);
   - `memcpy_loop_idiom`: `without_no_builtins` exhibits `asm_self_recursive_memset: true` while `with_no_builtins` emits `"no-builtins"` on both `memset` and `set_bytes_helper` with `asm_self_recursive_memset: false`;
   - `compile_rejections`: `11` error cases (`compile_rc: 1`) plus `aarch64_linux_x18_allowed` (`compile_rc: 0`).
2. **Re-verify the Lean 4 kernel proof bundle** (wrapping `lean` in host resource limits when configured):
   ```bash
   lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true support/InlineAsmAndBuiltinsFraming.lean
   ```
   Confirm exit code `0`, no `sorryAx`, `Classical.choice`, or `Lean.ofReduceBool` in `#print axioms` output, and confirm zero `sorry` / `Classical.choice` / `omega` / `bv_decide` / `native_decide` / `partial def` / `._unsafe_rec` tokens in source.
3. **Diff pinned upstream files if updating compiler versions**: inspect `compiler/rustc_codegen_llvm/src/asm.rs`, `compiler/rustc_target/src/asm/mod.rs`, `compiler/rustc_builtin_macros/src/asm.rs`, `compiler/rustc_codegen_ssa/src/mir/naked_asm.rs`, `compiler-builtins/src/lib.rs`, `llvm/lib/Transforms/Scalar/LoopIdiomRecognize.cpp`, and `joshlf/anneal`'s `trusted/lean/Trusted/MirAst.lean` (`TerminatorKind::InlineAsm` handling) for any newly added `InlineAsmOptions` bits, `InlineAsmClobberAbi` variants, or `compiler-builtins` libcalls.
