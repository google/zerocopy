# Rust Inline Assembly `asm_goto` Labels, `const`/`sym` Lowering, Assembler Directive Hazards, and Optimizer Contracts

## Summary

Verifying or compiling Rust `asm!`, `naked_asm!`, and `global_asm!` at
`Runtime(PostCleanup)` MIR and across LLVM codegen exposes four classes of
control-flow, symbol-resolution, assembler-state, and optimization hazards that
cannot be discharged by local instruction-level inspection alone:

1. **`asm_goto` (`label` operands, stabilized in Rust 1.87) and
   `asm_goto_with_outputs` (`unstable` through Rust 1.102):**
   - In `Runtime(PostCleanup)` MIR (`TerminatorKind::InlineAsm`), `targets[0]`
     is the fallthrough block *unless* `asm_macro == NakedAsm` or
     `InlineAsmOptions::NORETURN` is set, in which case `targets` begins
     directly with the first `label` (`target_index = 0`). Each `label { ... }`
     block starts a fresh safe context (`E0133` on unguarded `unsafe` calls),
     ends with `Goto(destination_block)` unless it diverges, and participates
     in MIR drop-flag elaboration across fallthrough vs. label edges.
   - Because `rustc_hir_typeck::check_expr_asm` checks each `label` block with
     `ExpectHasType(())`, a diverging tail expression **without** a trailing
     semicolon (`label { loop {} }`, `label { return 42 }`, `label { panic!() }`)
     coerces `! -> ()` and causes `asm!(..., options(noreturn))` to have type
     `()` rather than `!`; adding a trailing semicolon (`label { loop {}; }`,
     `label { return 42; }`) preserves type `!`.
   - `asm_goto_with_outputs` remains `unstable` across Rust `1.98`–`1.102`,
     gating only outputs that write a Rust place (`out(reg) x`, `inout`,
     `inout(...) a => x`); discarded outputs (`out("rax") _`, `clobber_abi("C")`,
     `inout(reg) a => _`) are **accepted on stable Rust**.
   - MIR models `InlineAsm` via `TerminatorEdges::AssignOnReturn`, treating all
     outputs as initialized along **every** `targets` edge (both fallthrough
     and every `label`). `Runtime(PostCleanup)` MIR still contains critical
     edges into `destination_block` (split only later in `Runtime(Optimized)`
     by `AddCallGuards::CriticalCallEdges`). In `rustc_codegen_llvm`, repeated
     template references to the same `label` operand emit duplicate `!i`
     constraints, duplicate `callbr` indirect targets, and duplicate output
     `store` instructions at the start of the label block; LLVM's
     `InlineAsmPrepare` later inserts `@llvm.callbr.landingpad` and merges
     identical critical edges. Multi-output `callbr` (`llvm#74483`) now passes
     at `-O0` and `-O3` on LLVM `22.1.6` and `23.1.5`. `X86InsertVZeroUpper`
     propagates dirty `YMM`/`ZMM` state across `callbr` label edges for typed
     vector outputs (`out("ymm0") _tmp`) but omits `vzeroupper` on both
     fallthrough and label edges for discarded outputs (`out("ymm0") _`).
2. **`const` and `sym` operands at `Runtime(PostCleanup)` MIR and RFC 3848
   (`asm_const_ptr`, introduced in Rust 1.99):**
   - At `Runtime(PostCleanup)` MIR, generic `const` operands remain unevaluated
     `Const::Unevaluated` references to separate anonymous const MIR bodies,
     generic `sym` functions remain parameterized `Const::Val(ZeroSized, FnDef)`,
     and all `sym` statics collapse uniformly into `InlineAsmOperand::SymStatic
     { def_id }` (requiring `tcx` queries for `static mut`, `#[thread_local]`,
     `#[link_name]`, or `#[linkage = "weak"]`).
   - Integer `const` operands format via `asm_const_to_str` as base-10 decimal
     strings (signed for `iN`/`isize`, unsigned for `uN`/`usize`, defaulting to
     `i32`); `i128`/`u128` values emit full 128-bit decimal literals that work
     in `.octa` but fail MC 64-bit instruction expression parsing.
   - Starting in Rust `1.99.0` (absent in `1.98.0-nightly`), `#![feature(asm_const_ptr)]`
     admits thin pointers (`*const T`, `*mut T`, `&T`, `fn(...)`) and coerces
     `FnDef` and non-capturing closures to `fn()`. `asm_const_ptr_clean`
     erases `TypeId` provenance and zero-sized `GlobalAlloc::Memory` allocations
     to bare unsigned decimal integers (substituting `alloc.align.bytes() +
     offset`, e.g., `16` for `&ZstAlign16`), whereas a ZST `static`
     (`GlobalAlloc::Static`) still emits a `"s"` symbol constraint (`${N:c}`).
   - `rustc_monomorphize::collector` unconditionally records `SymFn` (resolving
     `#[track_caller]` to its `reify` shim and hitting an ICE on compiler
     intrinsics like `core::intrinsics::black_box`) and `SymStatic` as live
     mono items even when referenced solely inside an assembly comment
     (`/* {0} */`).
3. **Assembler directives, CGU-wide state leakage, and filesystem/section escape
   hatches in LLVM MC:**
   - **Live `.init_array` constructor injection (all 4 toolchains):** An `asm!`
     block marked `options(pure, nomem, nostack, preserves_flags)` on a
     runtime-unexecuted branch can emit `.pushsection .init_array,"aw",@init_array;
     .quad {ctor}; .popsection` and execute arbitrary code **before `main()`**.
   - **Live `.include` / `.incbin` arbitrary host filesystem read (all 4
     toolchains):** LLVM's `AsmPrinter::emitInlineAsm` explicitly calls
     `sys::sandbox::scopedDisable()` and attaches `vfs::getRealFileSystem()`,
     allowing `.include` and `.incbin` in `asm!`, `naked_asm!`, and
     `global_asm!` to pull arbitrary host files into compiled code/data with
     **zero entries recorded in `rustc --emit=dep-info`**.
   - **Live cross-function `.macro` instruction hijacking (all 4 toolchains):**
     LLVM stores macros in CGU-wide `MCContext::MacroMap`. An uncalled function
     defining `.macro add dst, src; sub \dst, \src; .endm` silently rewrites
     `add` into `sub` inside an unrelated function's `asm!` in the same CGU
     (`10 + 3` evaluates to `7`). `.set` symbols similarly leak across `asm!`
     blocks.
   - **Unbalanced `.section` corruption:** Under default `-C force-unwind-tables=yes`,
     LLVM's `.cfi_advance_loc` catches unbalanced `.section` switches; under
     `-C force-unwind-tables=no -C panic=abort` (standard bare-metal/kernel
     flags), `rustc` succeeds and silently emits the Rust function's epilogue
     into non-executable `.rodata`, leaving `.text` truncated without `ret`.
   - **MASM integer vs. numeric-label dialect split (`llvm#99547`):** Default
     Intel-syntax `asm!` enables `setLexMasmIntegers(true)` (`101b == 5`,
     `0ffh == 255`, breaking `jb 10b` unless `binary_asm_labels` is heeded),
     whereas `options(att_syntax)` `asm!`, `naked_asm!`, `global_asm!`, and
     standalone `llvm-mc` do **not** enable MASM integers.
4. **Template syntax, modifiers, and `options(...)` optimization contracts:**
   - LLVM-internal modifiers (`:c`, `:l`) are rejected in Rust source templates;
     `{0:h}` on `reg_abcd` is accepted on `x86_64` even though explicit `ah`–`dh`
     operands are rejected; `clobber_abi(...)` rejects *all* register-class
     outputs including `lateout(reg)` and `out(reg) _`; `options(raw)` disables
     `{}` interpolation, rejects all operands, still runs `bad_asm_style`, and
     escapes `$` as `$$` in `asm!` (blocking `${:uid}` / `$0` injection).
   - At `-C opt-level=3`, `options(nomem)` alone (without `pure`) triggers
     dead-store elimination across a `sideeffect` `asm!` block; `options(pure,
     nomem)` triggers DCE, CSE, and guaranteed-execution LICM hoisting (while
     refusing speculative hoisting above a panicking bounds check, and never
     DCE-ing a `callbr` terminator); `options(pure, readonly)` enables CSE and
     LICM across loads while respecting intervening stores.

## Applicability

This report characterizes the interaction of `rustc` frontend validation,
`Runtime(PostCleanup)` and `Runtime(Optimized)` MIR, monomorphization, LLVM IR
lowering (`callbr`, `"s"`, `MemoryEffects`), and LLVM's integrated MC assembler
across four pinned `rust-lang/rust` toolchains on `x86_64-unknown-linux-gnu`,
paired with their exact pinned `rust-lang/llvm-project` submodules, the `Rust
Reference`, standalone `llvm-mc`, and GNU `binutils`:

| Toolchain / Subject | Pinned Upstream Revision | Bundled LLVM (`rust-lang/llvm-project`) | Key Version-Specific Behavior |
| :--- | :--- | :--- | :--- |
| `rustc 1.98.0-nightly` (`2026-05-31`) | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` | `22.1.6` (`08c84e69a84d95936296dfcab0e38b34100725d5`) | `asm_goto` stable; `asm_goto_with_outputs` unstable; **`asm_const_ptr` absent (`E0635`)**; `SymFn`/`SymStatic` lowered as distinct `InlineAsmOperandRef` variants |
| `rustc 1.99.1` (`2026-10-13`) | `58cf8f9c35b355199727627d07ae34a4e2846d67` | `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) | `asm_const_ptr` introduced (unstable, `E0658` on stable); `SymFn`/non-TLS `SymStatic` unified into `InlineAsmOperandRef::Const { Scalar::Ptr }` |
| `rustc 1.100.0` (`2026-11-09`) | `0ef1bc386059596dada8fb65b50425aab2ea637a` | `23.1.5` (`0a5579eb649d3634a9c30ac873300cc2944fa070`) | Same stable surface as `1.99.1`; `asm_goto_with_outputs` and `asm_const_ptr` remain unstable (`E0658`/`E0554`) |
| `rustc 1.102.0-nightly` (`2026-11-11`) | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` | `23.1.5` (`0a5579eb649d3634a9c30ac873300cc2944fa070`) | Full nightly execution of `#![feature(asm_goto_with_outputs)]`, `#![feature(asm_const_ptr)]`, `#![feature(asm_unwind)]`, `#![feature(thread_local)]`, `#![feature(linkage)]` |
| `rust-lang/reference` (`2026-11-17`) | `c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c` | — | Normative rules `r[asm.operand-type.*]`, `r[asm.abi-clobbers.*]`, `r[asm.options.*]`, `r[asm.directives.*]` |
| Standalone `llvm-mc` / GNU `binutils` | Debian `llvm-mc 21.1.8`, `objdump`/`readelf 2.47` | — | Differential MC encoding/disassembly and ELF section/symbol/relocation inspection |

**Shared across all four examined `rustc` versions:** `asm_goto` basic label
semantics, `asm_goto_with_outputs` instability and discarded-output exemption,
`noreturn` + `label` semicolon coercion, `may_unwind` + `label` mutual
exclusion, `.init_array` injection, `.include`/`.incbin` un-tracked host file
access, CGU-wide `.macro`/`.set` leakage and mnemonic hijacking, unbalanced
`.section` behavior under `-C force-unwind-tables=no`, `binary_asm_labels` /
`named_asm_labels` lints, and `options(...)` LLVM IR `MemoryEffects` +
optimization behavior.

**Relation to adjacent corpus reports:** This report builds on—without
duplicating—the register-class/constraint tables and MC directive inventory in
`rustc-inline-assembly-specification-llvm-lowering-and-assembler-syntax`, the
MIR-to-ISA state-bridge and discarded-`YMM` `vzeroupper` seam in
`rust-inline-asm-and-external-asm-abi-seams-in-formal-verifiers`, the
`library/` assembly census in
`rustc-sysroot-const-eval-select-and-inline-asm-ground-truth-census`, and the
`out`/`lateout` register-allocator quantifier and ELF/Mach-O relocation probes
in `rust-inline-assembly-contracts-relocations-and-simd-correspondence`.

## Findings

### 1. `asm_goto` (`label` Operands) and `asm_goto_with_outputs`: MIR, Drop Elaboration, and `callbr` Lowering

#### 1.1 Feature Status, Mutual Exclusions, and the `noreturn` Tail-Expression Coercion Quirk

Basis: `normative` (`rust-lang/reference@c9cc32825b`: `src/inline-assembly.md:442-458, 1289-1305`) + `source` (`rust-lang/rust@3ef0c22cdb`: `compiler/rustc_feature/src/{accepted.rs:67, unstable.rs:390}`, `compiler/rustc_builtin_macros/src/asm.rs:203-239`, `compiler/rustc_ast_lowering/src/asm.rs:493-521`, `compiler/rustc_hir_typeck/src/expr.rs:3780-3855`) + `execution` (`support/probe_asm_goto.py`)

Across all four examined toolchains (`1.98.0-nightly` through
`1.102.0-nightly`):

| Construct / Combination | `1.98-nightly` | `1.99.1` / `1.100.0` (Stable) | `1.102-nightly` | Governing Compiler Mechanism |
| :--- | :---: | :---: | :---: | :--- |
| `label { ... }` with no outputs | Accepted | Accepted | Accepted | `asm_goto` stabilized in Rust `1.87.0` |
| `label { ... }` + `out("rax") _` + `clobber_abi("C")` | Accepted | **Accepted** | Accepted | `rustc_ast_lowering/src/asm.rs:504-511` gates only `Out { expr: Some(_) }`, `InOut`, `SplitInOut { out_expr: Some(_) }` |
| `label { ... }` + `inout(reg) a => _` (discarded out) | Accepted | **Accepted** | Accepted | `SplitInOut { out_expr: None }` is exempt from `asm_goto_with_outputs` |
| `label { ... }` + `out(reg) x` / `inout(reg) x` / `lateout(reg) x` | `#![feature(asm_goto_with_outputs)]` | Rejected (`E0658`) | `#![feature(asm_goto_with_outputs)]` | Unstable across `1.98`–`1.102` (`rustc_feature/src/unstable.rs:390`) |
| `label { ... }` + `options(may_unwind)` | Rejected | Rejected | Rejected | Unconditionally forbidden (`rustc_builtin_macros/src/asm.rs:236-238`, `AsmMayUnwind`) |
| `label { ... }` + `options(pure, nomem)` (no output) | Rejected | Rejected | Rejected | `pure` requires `>= 1` non-discarded output (`asm.rs:225-227`) |
| `label { ... }` + `options(pure, nomem)` + `out(reg) x` | Accepted (feature) | Rejected (`E0554`) | Accepted (feature) | Valid under `#![feature(asm_goto_with_outputs)]`; lowers to `callbr` with `memory(none) willreturn` |
| `label { ext_unsafe(); }` (no inner `unsafe`) | Rejected (`E0133`) | Rejected (`E0133`) | Rejected (`E0133`) | `r[asm.operand-type.supported-operands-label]`: label block resets safety context |
| `options(noreturn)` + `label { a = 7; }` (unit block) | Type `()` | Type `()` | Type `()` | `check_expr_asm` (`expr.rs:3845`) clears `diverge = false` when any label returns `()` |
| `options(noreturn)` + `label { loop {} }` (no `;`) | **Type `()` (`E0308` for `-> !`)** | **Type `()` (`E0308`)** | **Type `()` (`E0308`)** | `check_expr_block(block, ExpectHasType(()))` coerces tail `! -> ()` before `ty.is_never()` check! |
| `options(noreturn)` + `label { loop {}; }` or `label { return 42; }` (with `;`) | **Type `!`** | **Type `!`** | **Type `!`** | Trailing semicolon keeps block type `!` without coercing tail to `()`, preserving `diverge = true` |

The `options(noreturn)` semicolon asymmetry arises directly from
`compiler/rustc_hir_typeck/src/expr.rs:3842-3846`:

```rust
let ty = self.check_expr_block(block, ExpectHasType(self.tcx.types.unit));
if !ty.is_never() {
    self.demand_suptype(block.span, self.tcx.types.unit, ty);
    diverge = false;
}
```

Passing `ExpectHasType(())` forces any diverging tail expression (`loop {}`,
`return 42`, `panic!()`, `unreachable_unchecked()`) without a trailing
semicolon to coerce to `()`, flipping `diverge = false` and assigning type
`()` to the entire `asm!` expression. Adding a trailing semicolon (`loop {};`,
`return 42;`) leaves the block's type as `!`, preserving `diverge = true`.

#### 1.2 Exact `Runtime(PostCleanup)` MIR Layout, `targets` Indexing, and Drop Elaboration

Basis: `source` (`rust-lang/rust@3ef0c22cdb`: `compiler/rustc_middle/src/mir/syntax.rs:940-972, 1060-1086`, `compiler/rustc_middle/src/mir/terminator.rs:714-738, 790-802`, `compiler/rustc_mir_build/src/builder/expr/into.rs:712-823`, `compiler/rustc_mir_transform/src/add_call_guards.rs:57-76`) + `execution` (`support/probe_asm_goto.py`)

In `rustc_middle::mir`, `TerminatorKind::InlineAsm` encodes CFG edges via a
single `targets: Box<[BasicBlock]>` slice and `InlineAsmOperand::Label {
target_index: usize }`:

1. **Fallthrough vs. `NORETURN` Indexing (`into.rs:721-723, 774-789`):**
   - When `!asm_macro.diverges(options)` (ordinary `asm!` without `noreturn`):
     `targets[0]` is `destination_block` (fallthrough). Each `label { ... }`
     allocates a fresh basic block `target`, assigns `target_index =
     targets.len()` (so labels occupy indices `1, 2, ...`), lowers the block
     body into `target`, and terminates non-diverging label bodies with
     `TerminatorKind::Goto { target: destination_block }`.
   - When `options(noreturn)` is set: `targets` starts empty (`vec![]`), so
     the first `label` receives **`target_index = 0`** (`targets[0]` is the
     first label, **not** fallthrough). If a label block returns `()`, it still
     terminates with `Goto(destination_block)`, making `destination_block`
     reachable exclusively via that label edge rather than via `targets[0]`.
     Verifiers capturing `Runtime(PostCleanup)` MIR **must** check
     `options.contains(NORETURN) || asm_macro == NakedAsm` before interpreting
     `targets[0]` as fallthrough.
2. **Dynamic Drop Elaboration Across Fallthrough vs. Label Edges:**
   In `mir_fallthrough_and_drop` (`support/probe_asm_goto.py`), moving a
   `DropGuard` inside `label { drop(g); res = 1; }` causes MIR drop elaboration
   to synthesize a boolean drop flag `_10` prior to `Runtime(PostCleanup)`:
   - Entry `bb0`: sets `_10 = true`, initializes `_2 = DropGuard(10)`, executes
     `asm!("test {0}, {0}\njnz {1}", in(reg) move _6, label 1, options()) ->
     [return: bb1, label: bb2, unwind unreachable]`.
   - Label block `bb2`: clears `_10 = false`, moves `_2` into
     `std::mem::drop`, unwinds to cleanup `bb5` if `drop` panics, and joins
     `bb1` (`destination_block`) via `goto -> bb1`.
   - Fallthrough/join block `bb1`: cleans up temporary operand storage
     (`StorageDead(_6)`), then branches on `switchInt(copy _10) -> [0: bb4,
     otherwise: bb6]` so `drop(_2)` runs if and only if execution fell through.
   - When a label block exits early via `return`, drop elaboration duplicates
     `StorageDead` and local drops along that label path directly (verified in
     `mir_dup_label_placeholder_with_out.runtime-post-cleanup.after.mir`).
   - Live execution confirms `drop_fall=(0, 0)` during/immediately after `asm!`
     (with drop running at function exit) and `drop_lbl=(101, 1)` (single drop
     inside the label block, zero double-drop at exit).
3. **Output Initialization Semantics Along Fallthrough vs. Label Edges:**
   - `TerminatorKind::InlineAsm::edges()` (`terminator.rs:790-802`) returns
     `TerminatorEdges::AssignOnReturn { return_: targets.iter().copied().collect(),
     cleanup: unwind.cleanup_block(), place: CallReturnPlaces::InlineAsm(operands) }`.
   - Because `return_` contains **every** element of `targets` (both
     fallthrough and all `label` blocks), borrowck and MIR initialization
     analysis treat every `out`, `lateout`, and `inout` place as **initialized
     upon entering every `label` block as well as upon fallthrough**.
   - Conversely, a Rust `out`/`lateout`/`inout` operand can never carry `Drop`
     glue: `rustc_hir_typeck` rejects even `#[repr(transparent)] struct
     DropU64(u64)` (`error: cannot use value of type 'DropU64' for inline
     assembly`), restricting register operands strictly to `Copy` primitives,
     pointers, and SIMD vectors.
   - Normative/semantic consequence (`derived` + `execution`): Under
     `asm_goto_with_outputs`, an `asm!` template that jumps to a `label` block
     without first writing all `out`/`lateout` registers delivers arbitrary
     register contents into those Rust locals (which is UB if the type has
     invalid bit patterns or violates downstream invariants).
4. **Critical Edges Between `Runtime(PostCleanup)` and `Runtime(Optimized)`:**
   In `mir_goto_with_outputs_critical` (`label {}, label {}, inout("eax") a`):
   - At `Runtime(PostCleanup)`, `bb0` targets `[return: bb1, label: bb2, label:
     bb3]`, while both `bb2` and `bb3` end in `goto -> bb1`. Thus `bb1` has
     **3 predecessors** (a critical edge on `bb0 -> bb1`), and `inout("eax")`
     is already canonicalized to base register `inout("ax") copy _1 => _1`.
   - Only later in `Runtime(Optimized)` does `AddCallGuards::CriticalCallEdges`
     (`compiler/rustc_mir_transform/src/add_call_guards.rs:57-76`) split every
     `InlineAsm` target with `pred_count[*target] > 1` when `has_outputs &&
     (has_labels || generates_invoke(unwind))`, producing disjoint trampoline
     blocks `[return: bb2, label: bb3, label: bb4]` each ending in `goto -> bb1`.
     Without this split, `rustc_codegen_llvm`'s store-on-every-target loop would
     emit stores inside a shared block reachable from another edge that already
     stored.

#### 1.3 LLVM `callbr` Lowering, Duplicate Label Placeholders, `llvm#74483`, `vzeroupper`, and Shrink-Wrapping

Basis: `source` (`rust-lang/rust@3ef0c22cdb`: `compiler/rustc_codegen_ssa/src/mir/block.rs:361-378, 1585-1607`, `compiler/rustc_codegen_llvm/src/asm.rs:254-258, 386-413, 584-586`; `rust-lang/llvm-project@0a5579eb64`: `llvm/lib/CodeGen/InlineAsmPrepare.cpp:141-208`, `llvm/lib/Target/X86/X86InsertVZeroUpper.cpp:147-275`) + `execution` (`support/probe_asm_goto.py`)

1. **Direct `callbr` Emission and Late `@llvm.callbr.landingpad` Insertion:**
   `rustc_codegen_llvm` does **not** emit `@llvm.callbr.landingpad` directly.
   Instead, `inline_asm_call` emits `callbr ... to label %default [label %lbl0, ...]`
   (using `fx.unreachable_block()` as `%default` when `options(noreturn)` is
   set, `block.rs:363-367`), and `asm.rs:391-413` iterates over `(if NORETURN
   { None } else { Some(dest) }).chain(labels)` to emit `extractvalue` +
   `store` directly from the `callbr` SSA value in every reachable target block.
   LLVM's backend pass `InlineAsmPrepare` (`InlineAsmPrepare.cpp:141-199`)
   subsequently splits remaining critical edges (including when an indirect
   target equals the default destination) and inserts `@llvm.callbr.landingpad`
   at the start of each indirect target block so register copies for `callbr`
   outputs occur along the indirect edge after the assembly jump.
2. **Duplicate `label` Placeholder Emission Defect/Quirk in `rustc_codegen_llvm`:**
   In `compiler/rustc_codegen_llvm/src/asm.rs:254-258`, every template
   placeholder referencing a `Label` operand appends a fresh `"!i"` constraint
   and pushes `label` onto `labels` without deduplication. Consequently,
   referencing `{lbl}` twice (`"jz {lbl}\njnz {lbl}"`) with
   `asm_goto_with_outputs` emits verbatim unoptimized LLVM IR:
   ```llvm
   %0 = callbr i64 asm sideeffect alignstack inteldialect
     "mov ${0:q}, ${1:q}\0Atest ${1:q}, ${1:q}\0Ajz ${2:l}\0Ajnz ${3:l}",
     "=&r,r,!i,!i,~{dirflag},~{fpsr},~{flags},~{memory}"(i64 %a)
     to label %bb1 [label %bb2, label %bb2]
   bb2:                                              ; preds = %start, %start
     store i64 %0, ptr %out, align 8
     store i64 %0, ptr %out, align 8
   ```
   LLVM's `InlineAsmPrepare` (`setMergeIdenticalEdges()` + `Visited.insert(IndDest)`)
   tolerates the duplicate indirect destination, and live execution (`goto_dup_label`)
   produces the expected values `(10, 15)` at `-O0` and `-O3`, but unoptimized IR
   carries redundant output stores and duplicated `!i` operands.
3. **Multi-Output `callbr` Codegen Status (`llvm/llvm-project#74483`):**
   Although `rust-lang/rust` (`3ef0c22cdb`, `tests/ui/asm/x86_64/goto.rs:89-119,
   156`) still comments out `goto_multi_out()` citing an `-O0` LLVM
   miscompilation on multiple `callbr` outputs (`llvm#74483`), live execution
   on both `rustc 1.98.0-nightly` (LLVM `22.1.6`) and `rustc 1.102.0-nightly`
   (LLVM `23.1.5`) passes both `goto_multi_out(11, 22) == 11` and a 5-output
   stress test `goto_5_outputs_both_edges` (`(65, 1065)`) at **both** `-O0` and
   `-O3`, as well as `lateout(reg)` read inside a `noreturn` label (`42`).
4. **`X86InsertVZeroUpper`, Flag Liveness, and Shrink-Wrapping Across `callbr`
   Label Edges:**
   - **Typed `YMM` output (`out("ymm0") _tmp`):** `X86InsertVZeroUpper` marks
     the `INLINEASM_BR` block `EXITS_DIRTY` and propagates dirty state across
     `MBB.successors()`, inserting `vzeroupper` on **both** the fallthrough path
     and the indirect label block `.LBB3_1` before calling `ext_sse_callee`.
   - **Discarded `YMM` output (`out("ymm0") _`):** Because `rustc` lowers
     discarded `out("ymm0") _` to `=&{xmm0}`, `X86InsertVZeroUpper` leaves the
     block `PASS_THROUGH` and omits `vzeroupper` on **both** fallthrough and
     label edges.
   - **Flags and Shrink-Wrapped Prologues:** Even with `options(preserves_flags)`,
     LLVM `22.1.6`/`23.1.5` re-materializes `cmpq %rsi, %rdi` in both successor
     blocks rather than carrying `EFLAGS` live across `INLINEASM_BR`. Moreover,
     LLVM shrink-wraps stack-alignment prologues (`pushq %rax` / `.cfi_def_cfa_offset 16`
     / `addq $8, %rsp`) directly into cold label blocks (`.LBB0_3`), requiring
     assembly code to restore `rsp` before jumping to any `label` just as on
     fallthrough.

---

### 2. `const` and `sym` Operands Across `Runtime(PostCleanup)` MIR, Monomorphization, and ELF Codegen

Basis: `normative` (`rust-lang/reference@c9cc32825b`: `src/inline-assembly.md:400-440`) + `source` (`rust-lang/rust@14210df0e2` vs. `@58cf8f9c35` vs. `@3ef0c22cdb`: `compiler/rustc_hir_typeck/src/{expr.rs:3798-3837, inline_asm.rs:585-656}`, `compiler/rustc_monomorphize/src/collector.rs:887-907, 1042`, `compiler/rustc_codegen_ssa/src/{common.rs:126-172, mir/block.rs:1536-1584}`, `compiler/rustc_codegen_llvm/src/asm.rs:170-185, 223-253`) + `execution` (`support/probe_const_and_sym.py`)

#### 2.1 Representation Split: `Runtime(PostCleanup)` MIR vs. Post-Monomorphization Lowering

In a generic function `pub unsafe fn generic_const_and_sym<T: Copy, const N: i32>()`,
`Runtime(PostCleanup)` MIR retains unmonomorphized operand structures:

- **`InlineAsmOperand::Const { value: Box<ConstOperand<'tcx>> }`:** Each
  `const <expr>` lowers to an unevaluated anonymous const body
  (`const generic_const_and_sym::<T, N>::{constant#0}`, `{constant#1}`). The
  anonymous const body itself has full MIR (including overflow `Assert` checks
  for `N + 1`). Evaluation occurs only post-monomorphization in
  `codegen_asm_terminator` via `self.eval_mir_constant(value)`.
- **`InlineAsmOperand::SymFn { value: Box<ConstOperand<'tcx>> }`:** Holds a
  zero-sized `ty::FnDef(def_id, args)` constant (e.g., `sym_fn generic_callee::<T>`),
  still carrying uninstantiated generic parameters `T`.
- **`InlineAsmOperand::SymStatic { def_id: DefId }`:** Collapses `static`,
  `static mut`, `#[thread_local] static`, `extern "C" { #[link_name = ...] static }`,
  and `#[linkage = "weak"] static` into the identical `SymStatic { def_id }`
  variant. A `Runtime(PostCleanup)` verifier cannot distinguish TLS, mutability,
  weak linkage, or link-name overrides from the MIR operand alone without
  inspecting `tcx` attributes for `def_id`.

#### 2.2 `const` Formatting Rules and RFC 3848 `asm_const_ptr` (`1.98` vs. `1.99`–`1.102`)

1. **Integer Formatting (`asm_const_to_str`, `common.rs:126-147`):**
   - Untyped integer literals default to `i32` (`const -1` $\to$ `"-1"`).
   - `u8`–`u128`/`usize` format as unsigned decimal strings (`u8::MAX` $\to$
     `"255"`, `u64::MAX` $\to$ `"18446744073709551615"`, `u128::MAX` $\to$
     `"340282366920938463463374607431768211455"`).
   - `i8`–`i128`/`isize` format as signed decimal strings (`i8::MIN` $\to$
     `"-128"`, `i64::MIN` $\to$ `"-9223372036854775808"`, `i128::MIN` $\to$
     `"-170141183460469231731687303715884105728"`).
   - Negative integers substitute raw `-N`, which LLVM MC accepts in both Intel
     (`add rax, -5`, `mov rax, [rdi + -8]`) and AT&T (`addq $-3, {x}`) templates.
   - **128-bit MC boundary:** `u128::MAX` fails inside `mov rax, {}` (`error:
     unknown token in expression` in LLVM MC's 64-bit expression parser), yet
     compiles cleanly inside `.octa {}`.
   - Non-integer non-pointer types (`const ()`, `const true`) are rejected
     across all versions (`error: invalid type for 'const' operand`).
2. **Version Transition — RFC 3848 `asm_const_ptr` (`1.99.0+`):**
   - In **`rustc 1.98.0-nightly` (`14210df0e2`)**, `asm_const_ptr` does not
     exist (`E0635: unknown feature 'asm_const_ptr'`), and passing any pointer
     to `const` fails with `error: invalid type for 'const' operand`.
   - In **`rustc 1.99.1` (`58cf8f9c35`)**, **`1.100.0` (`0ef1bc3860`)**, and
     **`1.102.0-nightly` (`3ef0c22cdb`)**, `#![feature(asm_const_ptr)]` accepts
     thin pointers (`*const T`, `*mut T`, `&T` where `is_thin_ptr_ty(T)` holds,
     i.e., `T: Sized` or `extern type`, plus `fn(...)`) and coerces `FnDef` and
     non-capturing closures to `fn()` (`expr.rs:3806-3819`), while rejecting
     wide pointers (`*const str`).
   - Exact lowering of every `asm_const_ptr` kind observed verbatim in
     `rustc 1.102.0-nightly` LLVM IR (`@const_ptr_kinds`,
     `support/probe_const_and_sym.py`):

| `const <expr>` Form (with `#![feature(asm_const_ptr)]`) | `asm_const_ptr_clean` Outcome (`common.rs:153-172`) | Emitted LLVM IR Template & Constraint |
| :--- | :--- | :--- |
| `0x1234usize as *const u8` (pointer without provenance) | `Scalar::Int(0x1234)` | Inline decimal `"4660"` (no constraint) |
| `&MY_ARR as *const [u8; 8]` (`GlobalAlloc::Static`) | `Scalar::Ptr(MY_ARR, +0)` | `"${0:c}"`, constraint `"s"`, arg `ptr @...MY_ARR` |
| `(&MY_ARR).cast::<u8>().wrapping_add(3)` | `Scalar::Ptr(MY_ARR, +3)` | `"${1:c}+3"`, constraint `"s"` |
| `(&MY_ARR).cast::<u8>().wrapping_sub(4)` | `Scalar::Ptr(MY_ARR, -4)` | `"${2:c}-4"`, constraint `"s"` (via `sign_extend_to_target_isize`) |
| `&ZstAlign16` (promoted ZST `GlobalAlloc::Memory`, `align == 16`) | **Erased to `Scalar::Int(16)`** (`align + offset`) | Inline decimal `"16"` (no symbol, no constraint!) |
| `&ZST_STATIC` (ZST `GlobalAlloc::Static`, `align == 16`) | **Preserved as `Scalar::Ptr(ZST_STATIC, +0)`** | `"${3:c}"`, constraint `"s"`, arg `ptr @...ZST_STATIC` |
| `&42u32` (promoted non-ZST `GlobalAlloc::Memory`) | `Scalar::Ptr(alloc, +0)` | `"${4:c}"`, constraint `"s"`, arg `ptr @alloc_...` |
| `target_fn` (`FnDef` coerced to `fn()`) | `Scalar::Ptr(fn_alloc, +0)` | `"${5:c}"`, constraint `"s"`, arg `ptr @...target_fn` |
| `|| {}` (non-capturing closure coerced to `fn()`) | `Scalar::Ptr(call_once_shim, +0)` | `"${6:c}"`, constraint `"s"`, arg `ptr @...FnOnce::call_once` |
| `GlobalAlloc::TypeId` provenance | Erased to `Scalar::from_u64(offset.bytes())` | Inline decimal offset (`common.rs:160-163`, `source`) |

   Note the sharp ZST asymmetry: a promoted ZST constant (`const &ZstAlign16`)
   loses its symbol identity and becomes its numeric alignment `16`, whereas a
   ZST `static` (`const &ZST_STATIC`) retains a real symbol relocation.

#### 2.3 `sym` Resolution, PIC/GOT/PLT/TLS ELF Relocations, Monomorphization Reachability, and Edge Cases

1. **Internal Lowering Unification (`1.98` vs. `1.99+`):** In `1.98.0-nightly`,
   `SymFn` and `SymStatic` stayed distinct `InlineAsmOperandRef::{SymFn,
   SymStatic}` variants. From `1.99.1` onward (`block.rs:1550-1584`), `SymFn`
   and non-TLS `SymStatic` unify into `InlineAsmOperandRef::Const { value:
   Scalar::Ptr(...) }`, leaving only `InlineAsmOperandRef::SymThreadLocalStatic`
   separate for `#[thread_local]` statics. All lower to LLVM `"s"` constraints
   with `${N:c}` template substitution (emitting the raw mangled or
   `#[export_name]`/`#[link_name]` symbol without automatic `@PLT`/`@GOTPCREL`).
2. **Verified PIC ELF Relocations (`-C relocation-model=pic`, `readelf -rW`):**
   - `call {exp}` (`#[unsafe(export_name = "exported_rust_fn")]`) $\to$ `R_X86_64_PLT32 exported_rust_fn - 4`
   - `add rax, qword ptr [rip + {st}]` (internal `static`) $\to$ `R_X86_64_PC32 _RNv...IMMUT_ST - 4`
   - `add rax, qword ptr fs:[{tls}@TPOFF]` (`#[thread_local] static`) $\to$ `R_X86_64_TPOFF32 _RNv...TLS_ST + 0`
   - `call {f}@PLT` (`extern "C"` with `#[link_name = "custom_ext_fn"]`) $\to$ `R_X86_64_PLT32 custom_ext_fn - 4`
   - `lea rax, [rip + {s}@GOTPCREL]` (`extern "C"` with `#[link_name = "custom_ext_sym"]`) $\to$ `R_X86_64_GOTPCREL custom_ext_sym - 4`
3. **Monomorphization Reachability & `sym` Target Edge Cases:**
   - In `compiler/rustc_monomorphize/src/collector.rs:887-907`, encountering
     `InlineAsmOperand::SymFn` invokes `visit_fn_use(..., /* is_direct_call */
     false)` and `InlineAsmOperand::SymStatic` pushes `MonoItem::Static(def_id)`.
     Live ELF symbol inspection (`support/probe_const_and_sym.py`) confirms that
     referencing a private generic function `private_generic_only_in_sym_comment::<[u8; 37]>`
     and a private static `PRIVATE_STATIC_ONLY_IN_SYM_COMMENT` **solely inside
     an assembly comment** (`/* {f} {s} */`, in either `asm!` or `global_asm!`)
     forces monomorphization and emission of both symbols into the object file.
   - `sym` accepts trait methods (`<u32 as T>::m`), ZST statics (`static Z: ()`),
     and `#[linkage = "weak"]`/`"extern_weak"` statics, while rejecting `const`
     items (`error: invalid 'sym' operand`).
   - **`#[track_caller]` shim indirection:** Because `SymFn` resolves via
     `Instance::resolve_for_fn_ptr` (`block.rs:1553`), `sym tc` for a
     `#[track_caller] fn tc()` resolves to the zero-argument `reify` shim
     (`@_RNSNv...2tc5reifyB3_`), **not** the underlying `tc(ptr %caller_loc)`
     function symbol.
   - **Compiler intrinsic ICE (`rustc 1.102.0-nightly`):** Because
     `rustc_hir_typeck/src/inline_asm.rs:635-654` checks only `ty::FnDef(..)`,
     `sym core::intrinsics::black_box::<u64>` passes typechecking and panics
     with an ICE (`exit 101`) in `compiler/rustc_monomorphize/src/collector.rs:1042:17`
     (`Instance { def: Intrinsic(...::black_box), args: [u64] } being reified`).

---

### 3. Assembler Directives, Macros, Sections, and Escape Hatches in `asm!`, `naked_asm!`, and `global_asm!`

Basis: `normative` (`rust-lang/reference@c9cc32825b`: `src/inline-assembly.md:1581-1728`) + `source` (`rust-lang/llvm-project@0a5579eb64`: `llvm/lib/CodeGen/AsmPrinter/AsmPrinterInlineAsm.cpp:99-138`, `llvm/lib/MC/MCParser/AsmParser.cpp:1921, 2064-2066, 4808-4819, 5217-5274`, `llvm/include/llvm/MC/MCContext.h:361, 846-854`; `rust-lang/rust@3ef0c22cdb`: `compiler/rustc_lint/src/builtin.rs:2734-3038`) + `execution` (`support/probe_directives_and_options.py`)

#### 3.1 Four Critical Template-Bypass Escape Hatches Verified Live Across Rust `1.98`–`1.102`

Because LLVM's `AsmPrinter::emitInlineAsm` invokes the full `MCAsmParser` over
the codegen unit's shared `MCContext` and `MCStreamer` with no directive
sandbox, four severe verification-bypass hazards work identically across
`1.98.0-nightly`, `1.99.1`, `1.100.0`, and `1.102.0-nightly`:

1. **`.init_array` Static Constructor Injection From a Never-Executed `asm!` Block:**
   Placing `.pushsection .init_array,"aw",@init_array; .quad {ctor}; .popsection`
   inside an `asm!` block marked `options(pure, nomem, nostack, preserves_flags)`
   inside an `if run_it` branch called with `black_box(false)` compiles cleanly
   and **executes `secret_ctor()` before `main()` starts** (`before_call=0xCAFEBABE
   dead_branch_ret=0` on all 4 toolchains). Section-switching directives create
   link-time/load-time effects completely divorced from CFG reachability and
   `options(...)` contracts.
2. **`.include` and `.incbin` Arbitrary Host Filesystem Read (Unsandboxed & Untracked):**
   In `llvm/lib/CodeGen/AsmPrinter/AsmPrinterInlineAsm.cpp:102-106`, LLVM
   explicitly disables sandboxing and mounts the real host filesystem:
   ```cpp
   SrcMgr.setVirtualFileSystem([] {
     // FIXME(sandboxing): Propagating vfs::FileSystem here is lots of work.
     auto BypassSandbox = sys::sandbox::scopedDisable();
     return vfs::getRealFileSystem();
   }());
   ```
   Live execution across all 4 toolchains proves that `.include "<path>"` and
   `.incbin "<path>"` succeed inside **`asm!`**, **`naked_asm!`**, and
   **`global_asm!`**, executing code from external `.s` files and embedding
   arbitrary host files into `.text`/`.rodata` (`inline_v=0x1111
   inline_magic=INCB naked_v=0x2222 global_str=INCBIN_OK_42`). Furthermore,
   `rustc --emit=dep-info` records **none** of the included files
   (`dep_tracked=(False, False, False)`), breaking both formal MIR inspection
   and build-system hermeticity/reproducibility.
3. **CGU-Wide `.macro` Instruction Mnemonic Hijacking and `.set` Symbol Leakage:**
   `MCContext` stores assembler macros in a single module-wide
   `StringMap<MCAsmMacro> MacroMap` (`MCContext.h:361, 850-854`), and
   `AsmParser::parseStatement` checks `getContext().lookupMacro(IDVal)`
   (`AsmParser.cpp:1921`) **before** target instruction parsing. In
   `support/probe_directives_and_options.py`, a never-called function
   `a_poison_mnemonic()` containing `.macro add dst, src\nsub \dst, \src\n.endm`
   emitted in the same CGU (`-C codegen-units=1`) silently hijacks `add {x}, {y}`
   in a separate function `b_victim_add(10, 3)` so it executes **`sub`** and
   returns **`7`** on all 4 toolchains! `.set` symbol definitions similarly
   persist across separate `asm!` blocks in the same CGU.
4. **Unbalanced `.section` Function-Body Truncation & Raw `.byte` Opcode Bypass:**
   - Under default `-C force-unwind-tables=yes`, switching sections with
     `.section .rodata.hijack` without `.popsection`/`.previous` fails during
     assembly with `error: invalid CFI advance_loc expression`. Under
     `-C force-unwind-tables=no -C panic=abort` (standard bare-metal/kernel
     settings), `rustc` exits `0` and silently emits the Rust epilogue
     (`mov eax, 42; pop rcx; ret`) into non-executable `.rodata.hijack` (with a
     preceding `.byte 0x41` fusing as a `REX.B` prefix to corrupt `mov eax, 42`
     into `mov r8d, 0x2a`!), leaving `.text.unbalanced_sec_no_uw` truncated
     immediately after `push rax`.
   - Raw byte directives (`.byte 0x48, 0xc7, 0x07, 0x2a, 0x00, 0x00, 0x00` =
     `mov qword ptr [rdi], 42`, verified via `llvm-mc --disassemble`) compile
     silently inside `options(nomem, nostack, preserves_flags)`, completely
     evading mnemonic-level template checks.

#### 3.2 Local Labels, Inlining Collisions, and the Intel/AT&T/Module-Asm MASM Asymmetry (`llvm#99547`)

- **Named labels vs. numeric directional labels:** Defining a named label
  (`.Lnon_unique_lbl:`, `asm_exported_global:`) inside `asm!` triggers the
  deny-by-default `named_asm_labels` lint (`rustc_lint/src/builtin.rs:2735`);
  under `#[allow(named_asm_labels)]`, `.globl`/`.weak`/`.hidden` export real
  `GLOBAL`/`WEAK`/`HIDDEN` ELF symbols from inside `asm!`, and inlining a
  named-label `asm!` twice fails with `error: symbol '.Lnon_unique_lbl' is
  already defined`. By contrast, numeric directional labels (`2:` / `2b` / `2f`)
  survive `#[inline(always)]` duplication cleanly because LLVM MC binds each
  reference to the nearest definition.
- **MASM binary-literal dialect split (`AsmPrinterInlineAsm.cpp:124-130`, `llvm#99547`):**
  On x86/x86-64, `AsmPrinter::emitInlineAsm` enables `setLexMasmIntegers(true)`
  **only** when `Dialect == InlineAsm::AD_Intel`—which applies to default
  Intel-syntax **`asm!`**, and **not** to `options(att_syntax)` `asm!`,
  **not** to `naked_asm!`, **not** to `global_asm!` (which lower via module
  inline asm starting with `.intel_syntax` under `AD_Att`), and **not** to
  standalone `llvm-mc -x86-asm-syntax=intel`. Live execution proves:
  - In Intel `asm!`: `mov {x}, 101b` and `mov {y}, 0ffh` evaluate to `5` and
    `255`, while `10:\n ... jb 10b` (under `#[allow(binary_asm_labels)]`) fails
    with `error: invalid operand for instruction` because `10b` lexes as integer
    `2` rather than a backward label! That is why `rustc` enables
    `#[deny(binary_asm_labels)]` on Intel x86 `asm!` (`builtin.rs:2785, 3018`).
  - In `options(att_syntax)` `asm!`: `jb 10b` assembles cleanly (`72 f6`),
    while `movq $101b, {x}` fails with `error: directional label undefined`.
  - In `naked_asm!`, `global_asm!`, and standalone `llvm-mc`: `mov rax, 101b`
    fails with `error: invalid reference to undefined symbol`, while `10:\njne 10b`
    assembles as a directional backward jump.

#### 3.3 Verifier Classification of Assembler Directives

Basis: `normative` + `source` + `execution` + `derived`

| Directive Family | Real Systems Use Case | Breaks Template-Only Verification? | Required Fail-Closed Verifier Policy |
| :--- | :--- | :--- | :--- |
| **Unconditional Reject (File/Macro/State Escape):** `.include`, `.incbin`, `.macro`/`.endm`/`.purgem`, `.altmacro`, `.set`/`.equ`/`.equiv`/`.eqv`, `.rept`/`.endr`, `.irp`/`.irpc`, `.if`/`.else`/`.endif` | Occasional macro sugar in legacy `.S` (almost never required in Rust `asm!`; `0` occurrences in Tier-1 Linux `library/`) | **Yes** — external unsandboxed host I/O, CGU-wide mnemonic/symbol poisoning, Turing-complete expansion | **Fail-closed reject** in `asm!`/`naked_asm!`/`global_asm!` (or expand + verify strictly post-assembly on the final object with zero CGU leakage) |
| **Unconditional Reject (Code-Stream / Init Injection):** `.init_array`, `.fini_array`, `.preinit_array`, `.ctors`, `.dtors`, `.section`/`.text`/`.data`/`.rodata`/`.bss` (unbalanced), `.code16`/`.code32`, `.intel_syntax`/`.att_syntax` | None in ordinary `asm!` (except explicit bare-metal boot stubs in `global_asm!`) | **Yes** — pre-`main` execution from dead branches; silent function truncation into `.rodata` | **Fail-closed reject** at template level **and** assert ELF section allowlist (`0` unexpected `.init_array`/relocs) post-assembly |
| **Post-Assembly Required (Structured Metadata Sections):** Balanced `.pushsection` + `.popsection` for Linux/Fuchsia `.extable` / `.altinstructions` / `.note.*` (`2b - .`, `3b - .` PC-relative fixups) | **Required** by OS kernels (Linux/Fuchsia user-copy fault tables, CPU alternatives) | **Yes** — cross-section `R_X86_64_PC32` relocations cannot be checked without assembling the function | **Allowlist only balanced pairs** targeting audited non-init sections, and **verify post-assembly** on the linked `.o` (`readelf -SW -rW`) |
| **Post-Assembly Required (Raw Encoding / Alignment):** `.byte`, `.short`, `.long`, `.quad`, `.octa`, `.ascii`/`.asciz`, `.insn`, `.inst`, `.balign`/`.p2align`/`.align`/`.nops` | **Required** for unsupported ISA encodings (e.g., new crypto/CPU opcodes), inline constant pools, and alignment | **Yes** — hides arbitrary machine instructions (`mov [rdi], 42`) from mnemonic parsers | **Reject** in template-only verifiers, or **decode and verify exact emitted machine bytes post-assembly** (`objdump`/ISA decoder) |
| **Context-Gated (Unwind Metadata):** `.cfi_adjust_cfa_offset`, `.cfi_def_cfa_*`, `.cfi_offset`, `.cfi_restore`, `.seh_*`; `.cfi_startproc`/`.cfi_endproc` | **Required** in `naked_asm!` (`__rust_probestack`) and stack-adjusting `asm!` | No instruction-semantics effect on normal path, but invalid `.cfi_startproc` in `asm!` fails assembly (`starting new .cfi frame`) and wrong CFI breaks unwinding | Allow frame-relative `.cfi_*` in `asm!` (forbid `.cfi_startproc`/`.cfi_endproc`), allow full `.cfi_startproc`..`.cfi_endproc` in `naked_asm!`/`global_asm!`, and validate `.eh_frame` FDEs post-assembly |
| **Context-Gated (Symbol Visibility):** `.globl`/`.global`, `.weak`, `.hidden`, `.local`, `.type`, `.size` | **Required** in `global_asm!` (automatic in `naked_asm!` prologue) | **Yes** in `asm!` — exports arbitrary ELF symbols and causes duplicate-symbol failures on inlining | **Reject** in `asm!` (and reject named labels); allow only in `global_asm!` with post-assembly symbol-table binding check |
| **Safe Local Control Flow:** Numeric directional labels `2:`–`9:` (`2f`/`2b`) | **Required** for local loops/branches (`compiler-builtins` `memcpy`, `__rust_probestack`) | Safe under inlining, **provided** multi-line blocks are assembled as a unit and digits `0`/`1`-only labels are forbidden on Intel x86 (`binary_asm_labels`) | **Accept** digits containing `>= 2` (or verify resolved displacements post-assembly) |

---

### 4. Template Syntax, Dialect, Modifiers, Operand Corner Cases, and `options(...)` LLVM Optimization Effects

Basis: `normative` (`rust-lang/reference@c9cc32825b`: `src/inline-assembly.md:150-263, 459-470, 908-978, 1024-1261`) + `source` (`rust-lang/rust@3ef0c22cdb`: `compiler/rustc_builtin_macros/src/asm.rs:203-276, 337-568`, `compiler/rustc_ast_lowering/src/asm.rs:253-332`, `compiler/rustc_codegen_llvm/src/asm.rs:195-262, 333-385`) + `execution` (`support/probe_directives_and_options.py`)

#### 4.1 Template Syntax, `raw`, Modifiers, Duplicate/Unused Operands, and `clobber_abi`

Live compilation probes on `rustc 1.102.0-nightly` and `rustc 1.99.1` confirm
nine exact boundary rules:

1. **`options(raw)` + `options(att_syntax)` + `$` escaping:** `options(raw)`
   skips format-string parsing (`builtin_macros/src/asm.rs:371-376`), allowing
   literal `{` and `}` without doubling (`/* {literal_braces} */`), and rejects
   any operand (`argument never used` because `used` stays `false`). In `asm!`,
   `codegen_llvm/src/asm.rs:196-200` still escapes every `$` as `$$`, so
   `movq $42, %rax` works under `options(raw, att_syntax)` while LLVM internal
   template expansions (`${:uid}`, `$0`) are neutralized into literal `$` text
   (verified in LLVM IR). `bad_asm_style` still fires on `.intel_syntax` /
   `.att_syntax` even under `options(raw)` (`builtin_macros/src/asm.rs:352-367`
   runs before the `RAW` early-continue).
2. **LLVM-internal modifiers rejected in Rust templates:** `{0:c}` on `sym` or
   `const` and `{0:l}` on `label` are hard compile errors
   (`rustc_ast_lowering/src/asm.rs:311-330`); `:c` and `:l` exist only in
   generated LLVM IR templates (`asm.rs:240, 252, 255`).
3. **High-byte `:h` modifier asymmetry on `x86_64`:** Explicit `in("ah") x` is
   rejected on `x86_64` (`high byte registers cannot be used as an operand on
   x86_64`), yet `asm!("mov {0:h}, 0xab", inout(reg_abcd) x)` **compiles
   cleanly** (`${0:h}` on constraint `=&Q`/`0`).
4. **Duplicate operand references & multi-modifier reuse:** The same register
   operand may be referenced repeatedly with different width modifiers
   (`"add {0:e}, {1:e}\nadd {0:r}, {1:r}"`), reusing a single LLVM operand
   index. The same `sym` reuses one `"s"` input; the same `const` is inlined
   textually at each placeholder; the same `label` duplicates `"!i"` and
   `callbr` targets (Section 1.3). Two distinct outputs targeting the same Rust
   place (`out(reg) y, out(reg) y`) compile cleanly and store left-to-right so
   the rightmost output wins (`r[asm.operand-type.left-to-right]`).
5. **Unused operands vs. explicit registers:** Every positional or named
   non-explicit-register operand (`in`, `out`, `inout`, `const`, `sym`, `label`)
   must appear at least once in the template (`error: [named] argument never
   used`, suggesting `"/* {0} */"`). Explicit register operands (`in("rax") x`,
   `out("rdx") _`) are pre-marked used (`builtin_macros/src/asm.rs:274-276`)
   and **forbidden** from being referenced by placeholder (`error: invalid
   reference to argument at index 0`).
6. **`clobber_abi(...)` forbids *all* register-class outputs (including
   `lateout(reg)` and `out(reg) _`):** Both `rustc 1.99.1` and `rustc
   1.102.0-nightly` reject `lateout(reg) x, clobber_abi("C")` and `out(reg) _,
   clobber_abi("C")` with `error: asm with 'clobber_abi' must specify explicit
   registers for outputs` (`builtin_macros/src/asm.rs:204-218, 252-257`,
   matching `r[asm.abi-clobbers.must-specify]`).

#### 4.2 `options(...)` $\to$ LLVM IR `MemoryEffects` and Observed `-C opt-level=3` Transformations

Empirical `-C opt-level=3 --emit=llvm-ir` probes on `rustc 1.98.0-nightly` and
`rustc 1.102.0-nightly` establish the exact compiler transformations permitted
by each option combination:

| Rust `asm!` Options | LLVM IR Flags & Call-Site Attributes (`asm.rs:333-384`) | DCE (Unused Out) | CSE (Duplicate Call) | DSE Across `asm!` (`*p = 1; asm!; *p = 2`) | LICM Hoisting Out of Loop |
| :--- | :--- | :---: | :---: | :---: | :---: |
| Default (`options()`) | `sideeffect alignstack`, `~{memory}`, `nounwind` | No | No | **No** (both stores kept) | No |
| `options(nostack)` | `sideeffect` (**no `alignstack`**), `~{memory}`, `nounwind` | No | No | No | No |
| `options(nomem)` | `sideeffect`, no `~{memory}`, `memory(inaccessiblemem: readwrite)` | No | No | **Yes — `*p = 1` deleted!** | No (`sideeffect` keeps loop) |
| `options(readonly)` | `sideeffect`, `~{memory}`, `memory(read, inaccessiblemem: readwrite)` | No | No | **No** (asm may read `*p`) | No (`sideeffect` keeps loop) |
| `options(pure, nomem)` | **no `sideeffect`**, `willreturn memory(none)` | **Yes** (whole `asm!` erased; **never** DCE'd if `callbr`) | **Yes** (`shl %0, 1`) | **Yes** | **Yes** when guaranteed to execute (`n != 0` preheader $\to$ `mul %0, %n`); **No** if preceded by panicking bounds check (not `speculatable`) |
| `options(pure, readonly)` | **no `sideeffect`**, `~{memory}`, `willreturn memory(read)` | **Yes** | **Yes** until intervening store; re-executes after `*p = 999` | **No** (asm may read `*p`) | **Yes** when loop writes no aliasing memory and executes unconditionally |

Key verification takeaway (`derived` + `execution`): Marking an `asm!` block
`options(nomem)` **even without `pure`** authorizes LLVM to perform dead-store
elimination and reorder Rust memory operations across the `asm!` block.
Conversely, `options(pure, nomem)` does **not** grant LLVM `speculatable`
permission to hoist `asm!` across a potentially trapping branch, and never
allows DCE of a `callbr` (`label`) terminator because `callbr` carries
control-flow edges.

## Boundaries

- **Not examined:**
  - Non-x86-64 codegen execution (`aarch64`, `riscv64`, `arm`, `s390x`,
    `powerpc64`) for `callbr`, `X86InsertVZeroUpper` equivalents, or
    target-specific assembler directives (`.arch_extension`, `.ltorg`, `.seh_*`,
    `.thumb`).
  - Alternative `rustc` codegen backends (`rustc_codegen_cranelift`,
    `rustc_codegen_gcc`), external GNU `as` (`-C llvm-args=-no-integrated-as`),
    or ThinLTO/FatLTO cross-module macro/section interactions.
  - Runtime behavior of `options(may_unwind)` unwinding through DWARF landing
    pads in `asm!` (without `label`).
- **Unknown:**
  - Whether upstream `rust-lang/rust` will stabilize `asm_goto_with_outputs` or
    `asm_const_ptr` in a future release beyond `1.102.0-nightly`, or deduplicate
    repeated `label` placeholders in `rustc_codegen_llvm/src/asm.rs:254-258`.
  - Whether upstream `llvm/llvm-project` will replace `sys::sandbox::scopedDisable()`
    in `AsmPrinterInlineAsm.cpp:102-106` or isolate `MCContext::MacroMap` per
    inline-assembly invocation.
  - Whether non-x86-64 targets still trigger multi-output `callbr` register
    allocator bugs analogous to `llvm#74483`.
- **Known not to apply:**
  - *Template-only or per-function verification of `asm!` is sound in the
    presence of arbitrary directives:* **Known not to apply** — proven false by
    live `.init_array` pre-`main` execution from dead branches, unsandboxed
    `.include`/`.incbin` reads, and CGU-wide `.macro` mnemonic hijacking across
    unrelated functions.
  - *`clobber_abi(...)` permits `lateout(reg)` or discarded `out(reg) _`
    register-class outputs:* **Known not to apply** — rejected on both `rustc
    1.99.1` and `rustc 1.102.0-nightly`.
  - *`asm_goto` on stable Rust forbids all `out`/`inout` operands:* **Known not
    to apply** — discarded outputs (`out("rax") _`, `clobber_abi("C")`,
    `inout(reg) a => _`) are accepted on stable Rust `1.99.1` and `1.100.0`.
  - *`options(noreturn)` with a `label { loop {} }` or `label { return 42 }`
    tail expression (without trailing semicolon) has type `!`:* **Known not to
    apply** — `check_expr_asm` coerces the tail expression to `()`.
  - *`naked_asm!` and `global_asm!` accept MASM integer literals (`101b`, `0ffh`)
    like default Intel `asm!`:* **Known not to apply** — module-level assembly
    does not enable `setLexMasmIntegers(true)`.
  - *`options(pure, nomem)` permits LLVM to speculate `asm!` above a panicking
    bounds check or DCE a `callbr` terminator:* **Known not to apply** —
    verified at `-C opt-level=3`.
- **Unsupported:**
  - `label` operands combined with `options(may_unwind)` (`AsmMayUnwind`).
  - `asm_const_ptr` on `rustc 1.98.0-nightly` (`E0635`) and on stable Rust
    `1.99.1`/`1.100.0` (`E0658`/`E0554`), and wide pointers (`*const str`) in
    `const` operands on all versions.
  - `sym` targeting `const` items (compile error) or compiler intrinsics such
    as `core::intrinsics::black_box` (monomorphization ICE in `collector.rs:1042`).
  - `.cfi_startproc`/`.cfi_endproc` inside function-scope `asm!` (assembler
    error: already inside compiler-emitted CFI frame).

## Evidence

### Primary Upstream Source Citations (Observed 2026-11-20)

- **`rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `1.102.0-nightly`; diffed against `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` `1.98.0-nightly` and `58cf8f9c35b355199727627d07ae34a4e2846d67` `1.99.1`):**
  - `compiler/rustc_feature/src/accepted.rs:61-67` (`asm_cfg` 1.93, `asm_const` 1.82, `asm_goto` 1.87) and `compiler/rustc_feature/src/unstable.rs:384-392` (`asm_const_ptr` 1.99, `asm_goto_with_outputs` 1.85, `asm_unwind` 1.58).
  - `compiler/rustc_builtin_macros/src/asm.rs:203-276, 337-568` (`validate_asm_args`, `clobber_abi` regclass-output check, `may_unwind` + `label` rejection, `raw`, `bad_asm_style`, unused/explicit-register rules).
  - `compiler/rustc_ast_lowering/src/asm.rs:253-332, 493-521` (template modifier validation rejecting `:c`/`:l` on `const`/`sym`/`label`; `asm_goto_with_outputs` gate ignoring discarded outputs).
  - `compiler/rustc_hir_typeck/src/expr.rs:3773-3855` (`check_expr_asm`, RFC 3848 `FnDef`/closure coercion for `const`, and `ExpectHasType(())` on `label` blocks causing the `noreturn` semicolon coercion quirk) and `compiler/rustc_hir_typeck/src/inline_asm.rs:585-656` (`asm_const_ptr` thin-pointer check, `SymFn` `ty::FnDef` check).
  - `compiler/rustc_middle/src/mir/syntax.rs:940-972, 1060-1086` (`TerminatorKind::InlineAsm`, `InlineAsmOperand`) and `compiler/rustc_middle/src/mir/terminator.rs:714-738, 790-802` (`TerminatorEdges::AssignOnReturn`).
  - `compiler/rustc_mir_build/src/builder/expr/into.rs:712-823` (`targets` construction with/without `NORETURN` and label-to-`destination_block` `Goto`).
  - `compiler/rustc_mir_transform/src/add_call_guards.rs:57-76` (`AddCallGuards::CriticalCallEdges` splitting `InlineAsm` critical edges).
  - `compiler/rustc_monomorphize/src/collector.rs:887-907, 1042` (`SymFn`/`SymStatic` reachability and intrinsic reification ICE).
  - `compiler/rustc_codegen_ssa/src/common.rs:126-172` (`asm_const_to_str` and `asm_const_ptr_clean`) and `compiler/rustc_codegen_ssa/src/mir/block.rs:361-378, 1536-1607` (`do_inlineasm`, `codegen_asm_terminator`).
  - `compiler/rustc_codegen_llvm/src/asm.rs:170-262, 333-414, 584-586` (const/sym/label lowering, duplicate `!i`/`labels` emission, `MemoryEffects`, `callbr` store loop).
  - `compiler/rustc_lint/src/builtin.rs:2734-3038` (`NAMED_ASM_LABELS` and `BINARY_ASM_LABELS` deny-by-default lints).
  - `tests/codegen-llvm/asm/{goto.rs, critical.rs}` and `tests/ui/asm/x86_64/goto.rs:89-159` (`llvm#74483`).
- **`rust-lang/llvm-project` (`0a5579eb649d3634a9c30ac873300cc2944fa070`, LLVM `23.1.5`):**
  - `llvm/lib/CodeGen/InlineAsmPrepare.cpp:12-33, 141-208` (`splitCriticalEdges`, `insertIntrinsicCalls`, `@llvm.callbr.landingpad`).
  - `llvm/lib/Target/X86/X86InsertVZeroUpper.cpp:147-275` (`hasYmmOrZmmReg`, `EXITS_DIRTY` successor propagation across `MBB.successors()`).
  - `llvm/lib/CodeGen/AsmPrinter/AsmPrinterInlineAsm.cpp:99-138` (`sys::sandbox::scopedDisable()`, `vfs::getRealFileSystem()`, `setLexMasmIntegers(true)` for `AD_Intel`).
  - `llvm/lib/MC/MCParser/AsmParser.cpp:1921, 2064-2066, 4808-4819, 5217-5274` (`lookupMacro`, `defineMacro`, `parseDirectiveInclude`, `parseDirectiveIncbin`) and `llvm/include/llvm/MC/MCContext.h:361, 846-854` (`MacroMap`).
- **`rust-lang/reference` (`c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c`):**
  - `src/inline-assembly.md:400-476, 1024-1318, 1581-1728`.

### Preserved Standalone Executable Probes (`support/`)

All probes clean up temporary directories via `tempfile.TemporaryDirectory()`
and were executed on `x86_64-unknown-linux-gnu` on `2026-11-20`:

1. `support/probe_asm_goto.py` — Validates the 15-case `asm_goto` /
   `asm_goto_with_outputs` / `noreturn` coercion matrix across all 4 toolchains,
   dumps `Runtime(PostCleanup)` and `Runtime(Optimized)` MIR (drop flags,
   critical edges, `NORETURN` target index `0`), dumps `callbr` LLVM IR
   (including duplicate label placeholders), runs `llvm#74483` (`goto_multi_out`)
   and 5-output stress binaries at `-O0`/`-O3`, and checks `X86InsertVZeroUpper`
   and shrink-wrapping across `callbr` edges.
2. `support/probe_const_and_sym.py` — Validates integer/128-bit/negative `const`
   formatting and the `1.98` vs. `1.99+` RFC 3848 `asm_const_ptr` matrix
   (including ZST const `16` vs. ZST static `${3:c}`), dumps generic `const`/`sym`
   `Runtime(PostCleanup)` MIR, inspects PIC ELF relocations (`R_X86_64_PLT32`,
   `PC32`, `TPOFF32`, `GOTPCREL`) via `readelf -rW`, verifies comment-only `sym`
   monomorphization reachability, and exercises `#[track_caller]` `reify` shims
   and the `core::intrinsics::black_box` ICE.
3. `support/probe_directives_and_options.py` — Executes live binaries proving
   `.init_array` pre-`main` injection from an unexecuted branch, `.include`/`.incbin`
   host reads with `dep-info` omission, CGU-wide `.macro` mnemonic hijacking
   (`victim_add(10, 3) == 7`), `llvm#99547` MASM binary literals vs. numeric
   labels across `asm!`/`att_syntax`/`naked_asm!`/`global_asm!`/`llvm-mc`,
   unbalanced `.section` `.rodata` epilogue corruption under
   `-C force-unwind-tables=no`, `.extable` relocations, `.cfi_*` rules, raw
   `.byte` opcode hiding, template modifier/`raw`/`clobber_abi` rules, and
   `-C opt-level=3` LLVM IR `MemoryEffects`/DCE/CSE/DSE/LICM transformations.

## Revalidation

With `rustup` toolchains `nightly-2026-06-01`, `1.99.1`, `1.100.0`, and
`nightly` plus `/usr/bin/llvm-mc`, `objdump`, and `readelf` installed, rerun
all three standalone probes from the package directory (~15 seconds total):

```bash
python3 support/probe_asm_goto.py
python3 support/probe_const_and_sym.py
python3 support/probe_directives_and_options.py
```

Key discriminating checks for future `rustc`/LLVM upgrades:

1. **Feature stabilization:** Check `validation_matrix` in `probe_asm_goto.py`
   and `const_matrix` in `probe_const_and_sym.py` on stable toolchains to detect
   stabilization of `asm_goto_with_outputs` or `asm_const_ptr`, or any change
   to `noreturn` + `label { loop {} }` type inference.
2. **`callbr` deduplication & `vzeroupper`:** Inspect
   `@mir_dup_label_placeholder_with_out` IR and `callbr_vzu_discarded_ymm`
   assembly in `probe_asm_goto.py` to detect whether `rustc` deduplicates
   repeated `label` placeholders or lowers discarded `out("ymm0") _` as `ymm0`.
3. **LLVM MC escape hatches:** Check `init_array_injection`,
   `include_and_incbin` (`dep_tracked`), and `macro_mnemonic_hijack`
   (`victim_add(10, 3)=7`) in `probe_directives_and_options.py`, or diff
   `AsmPrinterInlineAsm.cpp:102-130` and `MCContext.h:361` in newer LLVM
   revisions to see whether LLVM sandboxes inline-asm VFS access or isolates
   per-block macro tables.
