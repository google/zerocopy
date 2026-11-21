# C-Variadic Calling Conventions, Multi-Target `va_list` State Machines, and `#[unsafe(naked)]` Lowering in `rustc`

## Summary

C-style variadic functions (`...`), `core::ffi::VaList<'a>`, and `#[unsafe(naked)]` functions with `core::arch::naked_asm!` form the lowest-level ABI boundary in `rustc`, bypassing ordinary Rust argument passing, SSA MIR emission, and compiler-generated function prologues. Across primary-source audits of `rust-lang/rust` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`, `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`, and `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `rustc 1.98.0-nightly (14210df0e 2026-05-31)`), live compilation and Miri/GCC probes on `x86_64-unknown-linux-gnu` plus LLVM IR inspection across eight target triples, an audit of `joshlf/anneal` (`c131b320eeeb26ef692e5afd5ec8db49ee518613`), and a standalone kernel-checked Lean `v4.34.1` formalization (`221` theorems, `412` definitions, `18` inductive types; axioms restricted strictly to `[Quot.sound, propext]`), ten concrete invariants establish the exact trusted boundary:

1. **Rust `1.99.0` stabilizes `c_variadic`, `VaList`, `VaArgSafe`, and intrinsic `Clone`/`Drop`:** In `library/core/src/ffi/va_list.rs`, `VaList<'a>`, `Clone` (calling `va_copy`), `Drop` (calling `va_end`), and `VaList::next_arg::<T>()` carry `#[stable(feature = "c_variadic", since = "1.99.0")]`, replacing raw `va_list::va_arg` instability. Meanwhile, `VaArgSafe` transitions from `pub unsafe trait VaArgSafe: Copy + sealed::Sealed` to a `#[lang = "va_arg_safe"]` sealed lang-item trait (`pub impl(self) unsafe trait VaArgSafe {}`) that rejects C default-promoted types (`i8`, `u8`, `i16`, `u16`, `f32`, `bool`, `char`) on mainstream 32/64-bit targets, while keeping `i128`/`u128` behind `#![feature(c_variadic_int128)]`.
2. **Pre-`1.99.0` `va_copy` Miri bug fixed in `3ef0c22c`:** At `14210df0e2` (`1.98.0-nightly`), `sym::va_copy` in `compiler/rustc_const_eval/src/interpret/intrinsics.rs` allocates `copy_key` and writes only `va_list_key_field(dest)` without initializing the 24-byte `VaListInner` buffer. Live Miri execution proves `ap.clone()` aborts with `Undefined Behavior: constructing invalid value of type std::ffi::VaList<'_>: at .inner.gp_offset, encountered uninitialized memory, but expected an integer` (`rc = 1`), whereas `3ef0c22c` adds `write_bytes_ptr(dest.ptr(), zeros)?` so `VaList::clone` creates an independent valid cursor.
3. **`#[rustc_pass_indirectly_in_non_rustic_abis]` encodes C array-to-pointer decay without exposing `[__va_list_tag; 1]` in Rust:** On SysV `x86_64`, `s390x`, `powerpc` (32-bit), `xtensa`, and `hexagon-musl`, `VaListInner` carries `#[rustc_pass_indirectly_in_non_rustic_abis]`. On `x86_64` SysV, `compute_abi_info` decrements `int_regs` by `1` and calls `arg.make_indirect()`, lowering `ap: VaList<'_>` to `ptr dead_on_return noalias align 8 dereferenceable(24) %ap`. Live `gcc 15.2.0 -O2` <-> `rustc` linkage confirms exact bidirectional compatibility for direct variadic calls (`C_TO_RUST_VA=1220`), C-to-Rust `va_list` decay (`C_VA_LIST_DECAY=1220`), and Rust-to-C cloned `va_list` forwarding (`RUST_TO_C_VA_DECAY=600100`).
4. **System V AMD64 callers pass an exact XMM upper-bound in `%al`:** Disassembly of optimized Rust callers confirms `xorl %eax, %eax` for `0` XMM arguments, `movb $2, %al` for `2` `f64` arguments, and `movb $8, %al` when `9` `f64` arguments saturate `%xmm0..%xmm7` and spill the ninth float to `(%rsp)`. Under-reporting `%al` causes callee prologue skip/unsaved register-save-area reads, proved constructive UB (`ce1_underreported_al_reads_unsaved_xmm_slot_ub`).
5. **SysV `u128` variadic lowering diverges from AAPCS64 in both register alignment and register backfill:** On SysV `x86_64`, `emit_x86_64_sysv64_va_arg` checks `gp_offset <= 32` without rounding `gp_offset` to `16`; odd offsets (`gp_offset = 8`) use `copy_to_temporary_if_more_aligned` into an aligned stack `alloca`, spilling (`gp_offset = 40`) leaves `gp_offset` intact so a subsequent `u64` backfills `%r9`, and memory fallback calls `round_pointer_up_to_alignment` (`16`). All three cases hold under `gcc -O2` (`U128_ODD_GP_OK=1`, `U128_SPILL_R9_BACKFILL_OK=1`, `U128_OVERFLOW_ALIGN16_OK=1`) and are contrasted against AAPCS64 `emit_aapcs_va_arg` (`gr_offs` rounding to `-16` and exhausting `x7`).
6. **`VaList` sizes and lowering strategies span four distinct target families:** Across eight target triples (`--emit=llvm-ir -O`), `rustc` emits explicit struct cursor state machines for `24`-byte SysV (`x86_64-unknown-linux-gnu`, `x86_64-apple-darwin`) and `32`-byte AAPCS64 Linux (`gr_offs`/`vr_offs`), direct stack-pointer loads for `8`-byte pointer targets (`aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `powerpc64-unknown-linux-gnu` with big-endian `+4` word adjustment, `riscv64gc-unknown-none-elf`) and `4`-byte `i686-unknown-linux-gnu`, with zero `@llvm.va_arg` instructions and zero LLVM `byval` attributes.
7. **HIR call-site `E0617` has an explicit `_ => {}` omission for `char`:** `check_c_variadic_call` (`hir_typeck/src/fn_ctxt/checks.rs`) queries `VaArgSafe` (`va_arg_safe` lang item) and rejects `f32`, `i8|i16`, `bool`, `u8|u16`, and `FnDef` with `E0617`, yet falls through on `_ => {}`, accepting Rust `char` on variadic calls (`rc = 0`) despite `char` intentionally lacking `VaArgSafe`.
8. **Miri models `va_list` as an immutable-cursor heap handle (`AllocKind::VaList`):** Every `sym::va_arg` call deallocates the old heap entry and allocates a fresh `new_key`, making raw `ptr::copy_nonoverlapping` (`memcpy`) on `VaList` fail immediately on step 2 (`alloc154` UB). Miri enforces size equality, signed-to-unsigned negative-value rejection (`-1_i32` as `u32` -> UB, `42_i32` as `u32` -> `OK`), and `va_end` invalidation (`alloc153` UB).
9. **`#[unsafe(naked)]` bypasses LLVM IR function bodies via `module asm`, suppressing prologues and CFI/BTI landing pads:** `codegen_naked_asm` validates `TerminatorKind::InlineAsm` on `START_BLOCK` and lowers strictly via `codegen_global_asm` (`module asm`). Callers invoke an empty `declare` symbol with zero compiler prologue/epilogue and suppressed AArch64 `-Zbranch-protection=bti,pac-ret` landing pads (`hint #34` emitted for `normal_add1`, omitted for `naked_add1`).
10. **Anneal (`c131b320`) excludes both features at its trusted AST and admission boundary:** `Trusted.MirAst.TerminatorKind::InlineAsm` maps to `.unsupported`, `BodyStaticAdmitted` rejects compound `VaList<'_>` locals via `isSupportedScalarOrUnitTy`, and `evalTerminator` / `toMiriTerminatorForDispatch` fail closed on `.call` intrinsics (`va_start`/`va_arg`/`va_copy`). Integrating C-variadics or naked assembly into future verified `rustc` obligations requires extending MIR capture and `Trusted.MirSemantics` with explicit ABI contracts (`%al` bound, `SysVVaList` cursor separation, and stack-delta `0` naked contracts).

## Applicability

These findings govern:

| Subject | Exact Identity / Target | Role in Investigation |
| --- | --- | --- |
| Upstream `rustc` (stabilized `c_variadic`) | `rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`) | Audited primary source across `library/core`, `rustc_ast_passes`, `rustc_hir_typeck`, `rustc_const_eval`, `rustc_ty_utils`, `rustc_target`, `rustc_codegen_ssa`, `rustc_codegen_llvm`; preserved native & Miri receipt (`support/prior_run_nightly_2026_11_11.json`) |
| Executed `rustc` / Miri / LLVM toolchain | `rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly (14210df0e 2026-05-31)`, `LLVM 22.1.6`, `miri 0.1.0 (14210df0e2 2026-05-31)`) on `x86_64-unknown-linux-gnu` | Executed live probe suite (`support/probe_c_variadic_and_naked_asm.py`) and pre-`1.99.0` Miri `va_copy` comparison |
| System C compiler | `gcc (Debian 15.2.0-14) 15.2.0` on `x86_64-linux-gnu` | Compiled `-O2` C FFI variadic callers/callees and `__int128` (`u128`) probes linked against `rustc` staticlib (`--crate-type=staticlib`) |
| Anneal verification framework | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Inspected `Trusted.MirAst`, `Trusted.MirSemantics`, `Trusted.Correspondence`, and `trusted/rustc-capture/src/driver.rs` |
| Kernel theorem prover | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Checked `support/CVariadicVaListAndNakedAsmSoundness.lean` and `support/EnvironmentAudit.lean` (`-Ddebug.skipKernelTC=false -DwarningAsError=true`) |

Cross-target LLVM IR observations (`-Copt-level=2 --emit=llvm-ir`) apply across `x86_64-unknown-linux-gnu`, `x86_64-apple-darwin`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `i686-unknown-linux-gnu`, `powerpc64-unknown-linux-gnu`, and `riscv64gc-unknown-none-elf`. Native binary execution and `gcc` linkage apply specifically to `x86_64-unknown-linux-gnu`; non-x86_64 targets are established by LLVM IR inspection and compiler source audit (`compiler/rustc_codegen_llvm/src/va_arg.rs`) without cross-hardware execution. Pre-`1.99.0` toolchains (`14210df0e2`) require `#![feature(c_variadic)]` to compile `...` and `VaList`; `1.99.0+` (`3ef0c22c`) stabilizes `c_variadic` while leaving `c_variadic_int128` (`#155752`) and `c_variadic_naked_functions` (`#148767`) unstable.

## Findings

### 1. `core::ffi::VaList`, Stabilization in Rust `1.99.0`, and `VaArgSafe` Evolution

Between `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`) and `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`), `library/core/src/ffi/va_list.rs` stabilizes C-variadics (`#[stable(feature = "c_variadic", since = "1.99.0")]`) on `VaList<'a>`, `Debug`, `Clone`, `Drop`, and `VaList::next_arg`, while redesigning `VaArgSafe` to serve as a compiler-queried lang item.

In `1.98.0-nightly`, `VaArgSafe` is a normal supertrait-bounded marker trait (`pub unsafe trait VaArgSafe: Copy + sealed::Sealed`). In `3ef0c22c` (`library/core/src/ffi/va_list.rs:310-313`), it becomes an unimplementable lang-item trait without user-extensible supertraits:

```rust
#[lang = "va_arg_safe"]
#[unstable(feature = "c_variadic_va_arg_safe", issue = "162911", implied_by = "c_variadic")]
#[rustc_dyn_incompatible_trait]
pub impl(self) unsafe trait VaArgSafe {}
```

Both revisions encode C's "default argument promotions" (ISO C99/C17 §6.5.2.2p6-7) directly into target-conditional trait implementations (`va_list.rs:315-414`):

- **Default-promoted small integers (`i8`, `u8`, `i16`, `u16`):** `i8` and `u8` never implement `VaArgSafe` on any target. `i16` and `u16` implement `VaArgSafe` only when `any(target_arch = "avr", target_arch = "msp430")`, where `c_int`/`c_uint` are 16-bit (`va_list.rs:316-325`); on 32-bit and 64-bit targets they are excluded because C promotes them to `c_int`/`c_uint`.
- **Single-precision floats (`f32`):** `f32` implements `VaArgSafe` only on `target_arch = "avr"` (`va_list.rs:335-339`, where `c_double` is 32-bit IEEE binary32); elsewhere `f32` is promoted to `f64` (`c_double`) and excluded.
- **`bool`, `char`, and arrays/structs:** None implement `VaArgSafe` (`bool` promotes to `c_int` in C variadics; Rust `char` is a 4-byte Unicode scalar distinct from C `char`). Raw pointers (`*const T`, `*mut T`), `i32`, `u32`, `i64`, `u64`, `isize`, `usize`, and `f64` implement `VaArgSafe` unconditionally.
- **128-bit integers (`i128`, `u128`):** Gated on `#[unstable(feature = "c_variadic_int128", issue = "155752")]` across `wasm32`, `x86_64-x32`, and 64-bit targets where Clang/LLVM provides `__int128` (`aarch64`, `amdgpu`, `arm64ec`, `bpf`, `loongarch64`, `mips64`, `mips64r6`, `nvptx64`, `powerpc64`, `riscv64`, `s390x`, `sparc64`, `wasm64`, `x86_64`, `va_list.rs:375-405`). Attempting `ap.next_arg::<u128>()` without `#![feature(c_variadic_int128)]` fails at compile time with `E0277: the trait bound u128: VaArgSafe is not satisfied` (`probe_results.json`, `variadic_int128_probe`).

Across platforms, `VaList<'a>` (`#[repr(transparent)]`, `#[lang = "va_list"]`, `va_list.rs:219-225`) wraps one of seven `VaListInner` layouts (`va_list.rs:50-179`):

| Target Family | Inner Rust `VaListInner` Fields | Size / Align | `#[rustc_pass_indirectly_in_non_rustic_abis]` | LLVM Parameter ABI (`takes_valist`) |
| --- | --- | --- | --- | --- |
| `x86_64` SysV & Darwin (`x86_64-unknown-linux-gnu`, `x86_64-apple-darwin`) | `{ gp_offset: i32, fp_offset: i32, overflow_arg_area: *const c_void, reg_save_area: *const c_void }` | `24 B / 8 B` | **Yes** (`va_list.rs:114`) | `ptr dead_on_return noalias align 8 captures(none) dereferenceable(24) %ap` |
| `aarch64` non-Darwin / non-Windows (`aarch64-unknown-linux-gnu`) | `{ stack: *const c_void, gr_top: *const c_void, vr_top: *const c_void, gr_offs: i32, vr_offs: i32 }` | `32 B / 8 B` | **No** (struct > 16B passed indirectly by AAPCS64 rule) | `ptr dead_on_return noalias align 8 captures(none) dereferenceable(32) %ap` |
| `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `powerpc64-unknown-linux-gnu`, `riscv64gc-unknown-none-elf` | `{ ptr: *const c_void }` (fallback opaque pointer) | `8 B / 8 B` | **No** | `ptr noundef readonly captures(none) %0` (direct by-value pointer) |
| `i686-unknown-linux-gnu` | `{ ptr: *const c_void }` (fallback) | `4 B / 4 B` | **No** | `ptr noundef readonly captures(none) %0` |
| `s390x`, `powerpc` (32-bit), `xtensa`, `hexagon-musl` | `{ gpr, fpr, overflow_arg_area, reg_save_area }` (32B), `{ gpr, fpr, res, overflow_arg_area, reg_save_area }` (12B), `{ stk, reg, ndx }` (12B), `{ cur, end, overflow }` (12B) | `32 B` / `12 B` | **Yes** (`va_list.rs:74, 94, 133, 152`) | Indirect pointer in non-Rustic ABIs (`x86_64` SysV/s390x/ppc32/xtensa/hexagon) |

### 2. Modeling C `va_list` Array-to-Pointer Decay (`#[rustc_pass_indirectly_in_non_rustic_abis]`)

In C on System V AMD64, `va_list` is `typedef struct __va_list_tag va_list[1]`: declaring a parameter `va_list ap` causes C's parameter array-to-pointer decay, passing `struct __va_list_tag *` in a single GP register rather than passing a 24-byte struct across registers or by stack copy. Rust's `VaList<'a>` is a `#[repr(transparent)]` struct (not a `[T; 1]` array) so that `VaList<'a>` can own stack storage in locals, `impl Clone` (`va_copy`), and `impl Drop` (`va_end`).

To reconcile value semantics in `"Rust"` ABI with pointer decay in C ABIs, `rustc` attaches `#[rustc_pass_indirectly_in_non_rustic_abis]` to `VaListInner` on all targets where C `va_list` is a 1-element array (`va_list.rs:74, 94, 114, 133, 152`). In `compiler/rustc_target/src/callconv/x86_64.rs:231-235`:

```rust
if is_arg && arg.layout.pass_indirectly_in_non_rustic_abis(cx) {
    int_regs = int_regs.saturating_sub(1);
    arg.make_indirect();
    return;
}
```

Crucially, `arg.make_indirect()` passes `VaList` via an indirect pointer in `ArgAbi` (consuming 1 GP register from `int_regs`), **without** emitting LLVM `byval` on SysV targets (`uses_byval: false` across all 8 tested targets in `probe_results.json`, `part_d_cross_target_valist_matrix`). That preserves **mutability through the pointer**: when a callee or helper (`rust_vsum_indirect_valist(tag, ap)` or C `c_vsum_takes_valist(count, ap)`) advances `gp_offset`/`fp_offset`/`overflow_arg_area`, modifications mutate the caller's 24-byte `alloca` slot (or wait until `Clone::clone` copies it).

Live assembly and LLVM IR on `1.98.0-nightly` and `1.102.0-nightly` confirm the complete round-trip:

```llvm
define dso_local noundef i64 @rust_variadic_mixed(i64 noundef %tag_count, ...) unnamed_addr #3 {
start:
  %ap = alloca [24 x i8], align 8
  call void @llvm.lifetime.start.p0(ptr nonnull %ap)
  call void @llvm.va_start.p0(ptr nonnull %ap)
  %_0 = call noundef i64 @rust_vsum_indirect_valist(i64 noundef %tag_count, ptr noalias noundef nonnull align 8 captures(address) dereferenceable(24) %ap) #12
  call void @llvm.va_end.p0(ptr nonnull %ap)
  call void @llvm.lifetime.end.p0(ptr nonnull %ap)
  ret i64 %_0
}
```

Bidirectional linking with `gcc 15.2.0 -O2` (`c_rust_interop.c` + `rust_c_interop_lib.rs`) produces identical runtime totals across all three interop directions (`C_TO_RUST_VA=1220`, `C_VA_LIST_DECAY=1220`, `RUST_TO_C_VA_DECAY=600100`): C variadic calls into Rust `extern "C" fn(..., ...)`, C `va_list` decayed directly into Rust `VaList<'_>`, and Rust `VaList::clone()` passed into C `c_vsum_takes_valist(count, ap)` followed by Rust consuming the untouched original cursor.

### 3. Frontend AST and HIR Gates (`E0617` and the `char` Gap)

Two compiler passes enforce C-variadic syntax and call-site constraints:

1. **AST validation (`compiler/rustc_ast_passes/src/ast_validation.rs:980-1071`):** `check_c_variadic_type` checks target support (`supports_c_variadic_definitions`), requires `unsafe` safety, and requires explicit or implicit `extern`. `check_c_variadic_abi` permits non-`C` calling conventions (such as `extern "sysv64"`) only on `#[unsafe(naked)]` definitions gated behind `#![feature(c_variadic_naked_functions)]` (`#148767`), while unconditionally rejecting `extern "Rust"` variadic definitions even when `#![feature(naked_functions_rustic_abi)]` is requested (`naked_c_variadic_sysv64_probe` -> `E0658`, `naked_c_variadic_rust_abi_rejected` -> `error: ... is not supported for extern "Rust" naked functions`).
2. **HIR type-checking (`compiler/rustc_hir_typeck/src/fn_ctxt/checks.rs:481-544`):** At every call site to a `c_variadic` callee, `check_c_variadic_call` checks trailing arguments against `tcx.lang_items().va_arg_safe()`. If `arg_ty` implements `VaArgSafe`, the call passes silently; otherwise a hardcoded `match arg_ty.kind()` emits `E0617` ONLY for `f32`, `i8 | i16`, `bool`, `u8 | u16`, and `FnDef(..)`:

```rust
match arg_ty.kind() {
    ty::Float(ty::FloatTy::F32) => variadic_error(tcx.sess, arg.span, arg_ty, "c_double"),
    ty::Int(ty::IntTy::I8 | ty::IntTy::I16) | ty::Bool => {
        variadic_error(tcx.sess, arg.span, arg_ty, "c_int");
    }
    ty::Uint(ty::UintTy::U8 | ty::UintTy::U16) => {
        variadic_error(tcx.sess, arg.span, arg_ty, "c_uint");
    }
    ty::FnDef(..) => { /* PassFnItemToVariadicFunction */ }
    _ => {}
}
```

Because `check_c_variadic_call` falls through on `_ => {}` after failing the `VaArgSafe` check, passing Rust `char` (`'A'`, 4-byte Unicode scalar without `VaArgSafe`) or compound aggregates compiles cleanly (`variadic_call_char_allowed_by_hir_check`: `rc = 0`), creating an asymmetry between caller-side `E0617` enforcement and callee-side `VaArgSafe` rejection. Live probes verify `E0617` rejections (`rc = 1`) for `f32`, `i8`, `bool`, and `FnDef`, and silent acceptance (`rc = 0`) for `char`.

### 4. Multi-Target `emit_va_arg` State Machines, Caller `%al`, and `u128` Alignment Divergence

In `compiler/rustc_codegen_llvm/src/va_arg.rs`, `emit_va_arg` never lowers `VaList::next_arg` via LLVM's generic `va_arg` instruction (`uses_llvm_va_arg_instruction = false` in every LLVM IR probe across all 8 targets). Instead, `rustc_codegen_llvm` expands exact target-specific IR per ABI:

#### 4.1 System V AMD64 (`emit_x86_64_sysv64_va_arg`, `va_arg.rs:595-854`)

1. **Caller `%al` SSE/XMM count contract:** Before jumping to or calling a `c_variadic` callee, System V AMD64 callers place the upper bound `[0, 8]` on SSE registers holding variadic FP/vector arguments into `%al`. Real optimized `rustc` assembly (`variadic_sysv_probe.s`) demonstrates:
   - `call_zero_floats`: `xorl %eax, %eax` followed by tail-call `jmp rust_variadic_mixed` (`ZERO_FP=200`).
   - `call_two_floats_and_overflow`: puts 2 `f64`s in `%xmm0, %xmm1`, 5 GP variadic args in `%rsi..%r9`, spills the 6th GP variadic arg `1000` (`movq $1000, (%rsp)`), and emits `movb $2, %al` before `callq rust_variadic_mixed` (`MIXED_OVERFLOW=1220`). Note that on `1.102.0-nightly`, passing `u128` overflow pushes two quadwords (`pushq $0; pushq $1000`, `prior_run_nightly_2026_11_11.json`), yielding the exact same `MIXED_OVERFLOW=1220`.
   - `call_nine_floats`: populates `%xmm0..%xmm7`, emits `movb $8, %al`, and stores the 9th `f64` (`9.0` = `4621256167635550208`) at `(%rsp)` (`NINE_FP=45`).
2. **Register save area offsets & `%r9` backfill for `u128`:** `emit_x86_64_sysv64_va_arg` computes `num_gp_registers = bytes.div_ceil(8)` (`1` for scalars `<= 64b`, `2` for `i128`/`u128`) and tests unsigned `gp_offset <= 48 - num_gp * 8` (`gp_offset <= 40` for `u64`, `gp_offset <= 32` for `u128`). For `u64`/`f64`, the generated IR matches `rust_vsum_indirect_valist` (`icmp ult i32 %gp, 41`, `icmp ult i32 %fp, 161`). Crucially:
   - **SysV does NOT round `gp_offset` to `16` for 16-byte-aligned `u128`:** If `gp_offset = 8` (1 fixed `u64`, so `reg_save_area + 8` has alignment `8 mod 16`, NOT `16`), `u128` still reads `%rsi:%rdx` and calls `copy_to_temporary_if_more_aligned` (`va_arg.rs:693, 798-815`) into an aligned temporary stack `alloca`.
   - **Spilling `u128` does NOT increment `gp_offset`:** If `gp_offset = 40` (5 GP regs consumed, only `%r9` left), `gp_offset <= 32` is false, branching directly to `va_arg.in_mem` (`x86_64_sysv64_va_arg_from_memory`, `va_arg.rs:817-854`) without updating `gp_offset` (`va_arg.rs:769-781` sits strictly inside `in_reg`). Consequently, a *subsequent* `u64` argument finds `gp_offset == 40 <= 40` and **backfills from `%r9`**.
   - **Memory overflow aligns `overflow_arg_area` upward to `16` (`round_pointer_up_to_alignment`):** When `overflow_arg_area` precedes a stack `u128` after an odd stack slot (`u64`), `in_mem` rounds the stack cursor up by 16 (`andq $-16, %rdx` observed in `c_u128_sysv_probe.s`) before reading the 16-byte integer. Live `gcc -O2` execution verifies all three properties simultaneously: `U128_ODD_GP_OK=1 U128_SPILL_R9_BACKFILL_OK=1 U128_OVERFLOW_ALIGN16_OK=1`.

#### 4.2 AAPCS64 (`emit_aapcs_va_arg`, `va_arg.rs:196-285`) and Pointer-Based Targets

By direct contrast, on Linux `aarch64` (`aarch64-unknown-linux-gnu`), `emit_aapcs_va_arg` represents `va_list` as a 32-byte cursor using *negative* signed offsets from `gr_top` / `vr_top` (`gr_offs`, `vr_offs`). When loading `u128` (`gr_type && layout.align.bytes() > 8`), `va_arg.rs:252-263` executes:

```rust
if gr_type && layout.align.bytes() > 8 {
    reg_off_v = bx.add(reg_off_v, bx.const_i32(15));
    reg_off_v = bx.and(reg_off_v, bx.const_i32(-16));
}
let new_reg_off_v = bx.add(reg_off_v, bx.const_i32(slot_size as i32));
bx.store(new_reg_off_v, reg_off, offset_align);
```

When 7 GP registers are consumed (`gr_offs = -8`, only `x7` left), `(-8 + 15) & -16 = 0`, `new_reg_off_v = 16 > 0` is **written back to `gr_offs` before jumping to `on_stack`**, permanently exhausting `x7` so no subsequent `u64` can backfill `x7`—the exact opposite of SysV AMD64 `%r9` backfill.

On pointer-based ABIs (`aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `i686-unknown-linux-gnu`, `powerpc64-unknown-linux-gnu`, `riscv64gc-unknown-none-elf`), `VaListInner` is a single pointer `{ ptr: *const c_void }` and LLVM optimizes `takes_valist_reads_i32_f64` down to `10`–`11` lines of straight-line pointer GEP/loads (`probe_results.json`, `part_d_cross_target_valist_matrix`), with big-endian `powerpc64` offsetting the 32-bit `i32` load by `+4` bytes (`getelementptr inbounds nuw i8, ptr %0, i64 4`) to right-align `i32` in an 8-byte stack slot.

### 5. Const-Eval & Miri Operational Semantics (`AllocKind::VaList`) and `va_copy` Fix

In `compiler/rustc_const_eval/src/interpret/memory.rs:939-941, 1017-1052` and `intrinsics.rs:667-858`, Miri bypasses target register-save-area memory layouts altogether and models every live `VaList` via an abstract provenance table entry (`AllocKind::VaList` holding `VecDeque<MPlaceTy>`):

- **Allocation & cursor immutability:** Calling `sym::va_arg` (`intrinsics.rs:693-717`) calls `self.deallocate_va_list(key)?` *before* popping the next element, allocates a **brand-new** pointer key via `self.va_list_ptr(varargs)`, and stores the new key into `key_mplace`. Consequently:
  - Dropping (`va_end`, `intrinsics.rs:685-691`) deallocates `key`; subsequent reads trigger `invalid va_list ptr` UB (`miri_use_after_va_end_ub`: `using alloc153 as variable argument list pointer`, `rc = 1`).
  - Copying `VaList` with raw `ptr::copy_nonoverlapping` copies the stale integer pointer `key`; once either copy executes `next_arg`, the other holds a dangling `key` (`miri_raw_memcpy_after_step_ub`: `using alloc154 as variable argument list pointer`, `rc = 1`). Only `VaList::clone` (`sym::va_copy`) allocates an independent `copy_key` over `varargs.clone()`.
  - Reading past the end (`varargs.pop_front() == None`) yields `VaArgOutOfBounds` (`more C-variadic arguments read than were passed`, `rc = 1`).
- **Type and value compatibility (`validate_c_variadic_compatible_ty`, `intrinsics.rs:783-858`):** Miri accepts matching sizes with integer signed/unsigned mismatches (`CastIntTo`) **only when the runtime integer fits**; reading `-1_i32` as `u32` aborts (`va_arg value mismatch: value -1_i32 cannot be represented by type u32`, `rc = 1`), whereas reading `+42_i32` as `u32` succeeds (`COMPAT_I32_AS_U32=42`, `rc = 0`). Type mismatches (`f64` read as `u64`) abort identically on `1.98.0-nightly` and `1.102.0-nightly` (`va_arg type mismatch: requested u64 is incompatible with next argument of type f64`, `rc = 1`).
- **Fixed `va_copy` uninitialized-buffer UB (`1.98` -> `1.102`):** Comparing `const_eval_intrinsics_1_98.rs:726-736` (`14210df0e2`) against `const_eval_intrinsics.rs:667-683` (`3ef0c22c`) uncovers a concrete bug in pre-`1.99.0` Miri: `14210df0e2` allocates `dest` on the stack (`let mut ap_fork = ap.clone()`) and writes ONLY `copy_key_mplace` (`va_list_key_field` at offset `+16` / `overflow_arg_area` or key field), leaving `.inner.gp_offset` (`+0`) uninitialized! Under `1.98.0-nightly` Miri (`miri_va_copy_fork_probe`), `ap.clone()` immediately traps (`rc = 1`):

```text
error: Undefined Behavior: constructing invalid value of type std::ffi::VaList<'_>: at .inner.gp_offset, encountered uninitialized memory, but expected an integer
 --> src/main.rs:7:23
  |
7 |     let mut ap_fork = ap.clone();
  |                       ^^^^^^^^^^ Undefined Behavior occurred here
```

`3ef0c22c:676-679` closes this soundness gap by zeroing the full destination `VaList` layout (`self.write_bytes_ptr(dest.ptr(), zeros)?`) before writing `copy_key`.

### 6. `#[unsafe(naked)]`, `E0787`, `module asm` Lowering, and Prologue/BTI Suppression

`#[unsafe(naked)]` functions (`rustc_hir_typeck` naked checks, `hir_typeck_diagnostics.rs`, and `compiler/rustc_codegen_ssa/src/back/naked_functions.rs:18-60`) operate outside normal MIR/SSA lowering:

1. **HIR restrictions:** Parameter patterns (`naked_pattern_param`), referencing parameters inside non-asm Rust expressions (`naked_non_asm_and_param_ref`), using `asm!` instead of `naked_asm!` (`E0787`), emitting non-asm statements or multiple `naked_asm!` invocations (`E0787`), attaching `#[inline(...)]` (`E0736`), or passing non-const/non-sym operands (`in("rdi") x`) or stack-management options (`options(nostack)`) all fail at compile time (`compile_rejections`, 9 observed `rc = 1` diagnostics in `probe_results.json`). Meanwhile `extern "custom"` (`#140829`) is exclusively usable on foreign declarations or `#[unsafe(naked)]` definitions (`extern_custom_with_feature_without_naked` fails `rc = 1`).
2. **Backend bypass (`module asm`):** Instead of emitting an LLVM IR function definition with `Attribute::Naked`, `codegen_naked_asm` matches `TerminatorKind::InlineAsm` at `START_BLOCK` (`ssa_naked_asm.rs:32-43`) and wraps the user's `naked_asm!` template inside `.pushsection ...`, `.globl`, `.type ..., @function`, `.popsection` directly into **LLVM module-level global assembly (`module asm`)** (`codegen_global_asm`), leaving only an empty `declare` for callers (`naked_ok_module_asm_lines` in `probe_results.json`):

```llvm
module asm ".intel_syntax"
module asm ".pushsection .text.naked_add_mul,\"ax\", @progbits"
module asm ".balign 4"
module asm ".globl naked_add_mul"
module asm ".type naked_add_mul, @function"
module asm "naked_add_mul:"
module asm "lea rax, [rdi + rsi]"
module asm "imul rax, rdx"
module asm "ret"
...
declare noundef i64 @naked_add_mul(i64 noundef, i64 noundef, i64 noundef) unnamed_addr #4
```

3. **Zero prologue/epilogue & AArch64 BTI suppression:** Compiling `naked_aarch64_bti_compare.rs` for `aarch64-unknown-linux-gnu` with `-Zbranch-protection=bti,pac-ret` proves that `normal_add1` carries `attributes ... "branch-target-enforcement" "sign-return-address"="non-leaf"` and emits the `BTI C` landing pad **`hint #34`**, whereas `naked_add1` emits bare `add x0, x0, #1; ret` with **no `hint #34`** (`aarch64_bti_rc = 0`). The programmer bears sole responsibility for BTI landing pads, zero net `%rsp` delta at `ret`, and callee-saved register preservation.

### 7. Kernel-Checked Lean `v4.34.1` Mechanization & Environment Audit

`support/CVariadicVaListAndNakedAsmSoundness.lean` formalizes the full operational correspondence constructively in standalone `Init`-only Lean `v4.34.1` (`221` theorems, `412` definitions, `18` inductive types, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `._unsafe_rec`, `0` `WellFounded`, axioms strictly within `[Quot.sound, propext]`):

- **Main soundness theorems:**
  - `vaArgSafe_excludes_default_promoted_types`: For every target profile `prof` and primitive type `t`, `implementsVaArgSafe prof t = true -> cDefaultPromote prof t = t`.
  - `miri_vaCopy_non_interference`, `miri_use_after_vaEnd_is_ub`, `miri_raw_memcpy_after_step_is_ub`: Establish cursor-key freshness and monotonic handle invalidation in `MiriHeap`.
  - `sysv_pack_then_next_arg_exact`: Proves by structural induction over mixed `SysVArgVal` lists (`.gp64`, `.fp64`, `.int128`, with arbitrary fixed `fixedGp`/`fixedFp`, 6-GP / 8-XMM overflow, `%r9` backfill after spilled `u128`, and 16-byte overflow alignment) that `Nat.min (fixedFp + countFpArgs args) 8 <= callerAl` guarantees exact sequence recovery `sysvVaNextArgs (sysvPackVariadicCall fixedGp fixedFp callerAl args) (sysvInitVaList fixedGp fixedFp) (args.map SysVArgVal.ty) = .ok (args, ap')`.
  - `caller_al_ge_actualXmmUsed_prevents_unsaved_xmm_ub`: Eliminates `.unsavedXmmReadUB` whenever the `%al` bound holds.
  - `vaCopy_cursor_fork_non_interference`: Proves cursor replication yields identical observation streams on forked handles.
  - `passIndirectly_forces_indirect_on_sysv_x86_64`: Establishes `Indirect` vs `Direct` ABI pass modes matching `callconv/x86_64.rs:231-235`.
  - `nakedFnContract_sound`: Proves net stack delta `0` and untouched callee-saved registers preserve the return slot and `rspExit = rspEntry + 8`.
- **Constructive sharpness counterexamples (`ce1`–`ce4`) and AAPCS64 contrast (`aapcs64_gr_offs_contrasts_with_sysv_backfill`):**
  - `ce1_underreported_al_reads_unsaved_xmm_slot_ub`: Setting `callerAl = 0` with `1` `f64` triggers `.unsavedXmmReadUB`, whereas `callerAl = 1` succeeds.
  - `ce2_odd_gp_offset_u128_without_alignment_adjustment_corrupts_arg`: Demonstrates corrupted `u128` at `gpOffset = 40` without pair-room check, `16*k + 8` save-area non-alignment at `gpOffset = 8`, and unaligned overflow stack corruption after `u64` alongside `%r9` backfill recovery.
  - `ce3_c_default_promoted_f32_read_as_unpromoted_f32_type_mismatch_ub`: Exhibits `3.5f32` (`0x40600000`) promoted to `3.5f64` (`0x400c000000000000`), whose low 32-bit half is `0 /= 0x40600000`, caught by Miri (`vaArgTypeMismatchUB`) and statically prevented by `implementsVaArgSafe lp64SysV .f32 = false`.
  - `ce4_nonzero_stack_delta_in_naked_ret_corrupts_return`: Proves non-zero stack delta (`-8` with hardware stack invariant `8 <= rsp0`) jumps off the return slot (`sBad.rip /= retAddr`).

### 8. Consequences for Anneal's Trusted Boundary (`joshlf/anneal@c131b320`)

Inspecting `joshlf/anneal` at commit `c131b320eeeb26ef692e5afd5ec8db49ee518613` shows clean fail-closed isolation today along with exact requirements for any future FFI/inline-asm expansion:

1. **Static type admission blocks `VaList` locals:** `Trusted.MirSemantics.BodyStaticAdmitted` (`trusted/lean/Trusted/MirSemantics.lean:1730-1737`) enforces `body.locals.all isSupportedScalarOrUnitTy`. Because `VaList<'_>` wraps compound `VaListInner` (`24 B` / `32 B` structs or `*const c_void` with lifetime `PhantomCovariantLifetime<'_>`), any body referencing `VaList<'_>` fails static admission cleanly.
2. **`va_start` / `va_arg` / `va_copy` / `va_end` intrinsics fail closed:** Even in wrapper functions, `TerminatorKind.call` steps to `.fault .unsupported` in `evalTerminator` (`MirSemantics.lean:1568-1569`) and lowers to `.UnwindTerminate .Abi` in `Correspondence.toMiriTerminatorForDispatch` (`trusted/correspondence/Trusted/Correspondence.lean:2062-2063`). `Trusted.MirAst` and `trusted/rustc-capture/src/driver.rs` (`rustc 1.98.0-nightly (f8a08b688 2026-05-30)` callback gate) do not yet capture or tag variadic `FnAbi` signatures (`c_variadic`, `%al` argument counts).
3. **`#[unsafe(naked)]` is `.unsupported` by MIR definition and invisible at LLVM-IR body level:** `Trusted.MirAst.TerminatorKind` (`trusted/lean/Trusted/MirAst.lean:782-795`) explicitly folds `TerminatorKind::InlineAsm` into `.unsupported`. Because `codegen_naked_asm` emits `module asm` rather than an LLVM function body, Anneal cannot verify naked functions purely via MIR semantics; supporting `#[unsafe(naked)]` or `c_variadic` would require ISA-level assembly pre/post-conditions (`nakedFnContract_sound` / `%al >= countFp` / stack-delta `0` / BTI landing pads) anchored outside `Trusted.MirSemantics`.

## Boundaries

1. **Non-x86_64 execution:** Native binaries and `gcc -O2` FFI links were compiled and run exclusively on `x86_64-unknown-linux-gnu`. Behavior on `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`, `x86_64-apple-darwin`, `x86_64-pc-windows-msvc`, `i686-unknown-linux-gnu`, `powerpc64-unknown-linux-gnu`, and `riscv64gc-unknown-none-elf` was verified through `rustc --emit=llvm-ir` and direct compiler source inspection (`llvm/va_arg.rs`, `va_list.rs`), not bare-metal/QEMU execution.
2. **`va_arg.rs` sub-cases omitted from empirical probes:** `x86_64` x87 `f80`, `f128`, `ppcf128`, composite `ScalarPair { float, int }` heterogeneous register assembly (`llvm_va_arg.rs:729-754`), `s390x`, `powerpc` 32-bit, `hexagon`, and `xtensa` code paths were audited in upstream `rustc` source (`3ef0c22c`) but not dynamically executed.
3. **Host toolchain revision split:** The live probe run in this package executed on `rustc 1.98.0-nightly (14210df0e 2026-05-31)` / `miri 0.1.0 (14210df0e2 2026-05-31)`, where `#![feature(c_variadic)]` is still required and `VaList::clone` hits uninitialized `gp_offset` under Miri (`rc = 1`). Post-`1.99.0` runtime behavior (`rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)`) is evidenced by direct upstream source comparison (`3ef0c22c` `va_list.rs` and `const_eval_intrinsics.rs:676-679`) plus the preserved execution receipt `support/prior_run_nightly_2026_11_11.json` (`CLONE_FORK` / `va_copy` Miri probe was added specifically during the `1.98.0` run).
4. **Scope of the Lean 4 model:** `CVariadicVaListAndNakedAsmSoundness.lean` models abstract `UInt64`/`Nat`/`Int` register save slots and overflow slots rather than a full concrete byte-addressed x86-64 memory heap with pointer provenance, stack red zones, or hardware trap semantics. Similarly, `NakedAsmState` abstracts instruction sequences to their net stack pointer delta and callee-saved register preservation at `ret`.
5. **No `-Zsanitizer=cfi` x86_64 comparison run:** Only AArch64 `-Zbranch-protection=bti,pac-ret` (`hint #34` suppression) was compiled directly to compare hardware landing-pad generation in `naked_add1` vs `normal_add1`.

## Evidence

### Support Artifact Inventory (`support/`)

| Artifact | Purpose | Key Verification Summary |
| --- | --- | --- |
| `support/probe_c_variadic_and_naked_asm.py` | End-to-end driver for `rustc`, `cargo miri`, `gcc`, LLVM IR, and negative compile checks | Exits `0`; writes all `support/specimens/*` and `support/probe_results.json` (`35,510` bytes) |
| `support/probe_results.json` | Complete serialized JSON receipt from `1.98.0-nightly` / `LLVM 22.1.6` / `miri` / `gcc 15.2.0` | Captures all 5 probe parts (`part_a` through `part_e`, `17` rejection/acceptance compiler checks) |
| `support/prior_run_nightly_2026_11_11.json` | Preserved empirical receipt from `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11)` | Confirms post-`1.99.0` stabilized `ZERO_FP=200 MIXED_OVERFLOW=1220 VALIST_SZ=24`, Miri `u64` vs `f64` UB, `NAKED_OK=35` |
| `support/specimens/` (`11` files) | Minimal standalone Rust/C specimens plus emitted `.s` assembly | `variadic_sysv_probe.{rs,s}`, `variadic_clone_fork_probe.rs`, `rust_c_interop_lib.rs`, `c_rust_interop.c`, `c_u128_sysv_probe.{c,s}`, `cross_target_valist_matrix.rs`, `naked_ok.{rs,s}`, `naked_aarch64_bti_compare.rs` |
| `support/CVariadicVaListAndNakedAsmSoundness.lean` | Standalone `Init`-only Lean `v4.34.1` mechanization | Compiles under `-DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true` with `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide` |
| `support/EnvironmentAudit.lean` | Automated kernel environment check over every constant in the `.olean` | Audits `221` theorems, `412` definitions, `18` inductive types; verifies `0` `._unsafe_rec`, `0` `partial`, `0` `WellFounded`, axioms strictly `[Quot.sound, propext]` |

### Verbatim Empirical Receipts (`probe_results.json` & `prior_run_nightly_2026_11_11.json`)

| Check ID | Toolchain / Mode | Observed Output / Exit Code (`rc`) |
| --- | --- | --- |
| `part_a_c_variadic_sysv` | `rustc 1.98.0-nightly -O` native | `ZERO_FP=200 MIXED_OVERFLOW=1220 NINE_FP=45 VALIST_SZ=24 VALIST_ALIGN=8` (`rc=0`) |
| `part_a_c_variadic_sysv` | `rustc 1.102.0-nightly` preserved | `ZERO_FP=200 MIXED_OVERFLOW=1220 VALIST_SZ=24` (`rc=0`) |
| `clone_fork_native` | `rustc 1.98.0-nightly -O` native | `CLONE_FORK=110` (`rc=0`) |
| `part_a_miri` | `miri 0.1.0 (14210df0e2)` | `ZERO_FP=200 MIXED_OVERFLOW=1220 NINE_FP=45 VALIST_SZ=24 VALIST_ALIGN=8` (`rc=0`) |
| `part_b_c_rust_interop` | `gcc 15.2.0 -O2` + `rustc --crate-type=staticlib` | `C_TO_RUST_VA=1220 C_VA_LIST_DECAY=1220 RUST_TO_C_VA_DECAY=600100` (`rc=0`) |
| `part_b_c_u128_sysv` | `gcc 15.2.0 -O2` | `U128_ODD_GP_OK=1 U128_SPILL_R9_BACKFILL_OK=1 U128_OVERFLOW_ALIGN16_OK=1` (`rc=0`) |
| `miri_type_mismatch_ub` | `miri` (`f64` read as `u64`) | `rc=1`: `Undefined Behavior: va_arg type mismatch: requested u64 is incompatible with next argument of type f64` |
| `miri_signed_value_mismatch_ub` | `miri` (`-1_i32` read as `u32`) | `rc=1`: `Undefined Behavior: va_arg value mismatch: value -1_i32 cannot be represented by type u32` |
| `miri_signed_nonneg_compatible_ok` | `miri` (`42_i32` read as `u32`) | `rc=0`: `COMPAT_I32_AS_U32=42` |
| `miri_out_of_bounds_ub` | `miri` (read 2 from 1 arg) | `rc=1`: `Undefined Behavior: more C-variadic arguments read than were passed` |
| `miri_raw_memcpy_after_step_ub` | `miri` (`ptr::copy_nonoverlapping` copy) | `rc=1`: `Undefined Behavior: using alloc154 as variable argument list pointer but it does not point to a variable argument list` |
| `miri_use_after_va_end_ub` | `miri` (read after `drop(ap)`) | `rc=1`: `Undefined Behavior: using alloc153 as variable argument list pointer but it does not point to a variable argument list` |
| `miri_va_copy_fork_probe` | `miri 0.1.0 (14210df0e2)` (`ap.clone()`) | `rc=1`: `constructing invalid value of type std::ffi::VaList<'_>: at .inner.gp_offset, encountered uninitialized memory` (fixed at `3ef0c22c:676-679`) |
| `part_e_naked_ok` | `rustc 1.98.0-nightly -O` & `1.102.0-nightly` | `NAKED_OK=35` (`rc=0`); `naked_add_mul`: `leaq (%rdi,%rsi), %rax; imulq %rdx, %rax; retq` |
| `part_e_aarch64_bti` | `rustc --target=aarch64-unknown-linux-gnu -Zbranch-protection=bti,pac-ret` | `rc=0`: `normal_add1` has `hint #34`; `naked_add1` omits `hint #34` |
| `variadic_call_{f32,i8,bool,fndef}_e0617` | `rustc 1.98.0-nightly` | `rc=1`: `error[E0617]: can't pass ... to variadic function` |
| `variadic_call_char_allowed_by_hir_check` | `rustc 1.98.0-nightly` | `rc=0`: silently compiled due to `_ => {}` fallthrough in `check_c_variadic_call` |
| `variadic_int128_probe` | `rustc 1.98.0-nightly` (without feature) | `rc=1`: `error[E0277]: the trait bound u128: VaArgSafe is not satisfied` |
| `naked_{non_asm,uses_asm,pattern,in_op,nostack,e0736,e0658_sysv64,rust_abi}` | `rustc 1.98.0-nightly` | All expected rejections `rc=1` (`E0787`, `ParamsNotAllowed`, `E0736`, `#148767`, `extern "Rust"` variadic rejected); `naked_c_variadic_with_wild_probe` compiled cleanly (`rc=0`) |

### Verbatim Lean 4 `#print axioms` and `EnvironmentAudit` Output

```text
'CVariadicVaListAndNakedAsmSoundness.vaArgSafe_excludes_default_promoted_types' depends on axioms: [propext]
'CVariadicVaListAndNakedAsmSoundness.vaArgSafe_lp64_excludes_promoted' does not depend on any axioms
'CVariadicVaListAndNakedAsmSoundness.miri_vaCopy_non_interference' depends on axioms: [propext, Quot.sound]
'CVariadicVaListAndNakedAsmSoundness.miri_use_after_vaEnd_is_ub' depends on axioms: [propext, Quot.sound]
'CVariadicVaListAndNakedAsmSoundness.miri_raw_memcpy_after_step_is_ub' depends on axioms: [propext, Quot.sound]
'CVariadicVaListAndNakedAsmSoundness.sysv_pack_then_next_arg_exact' depends on axioms: [propext, Quot.sound]
'CVariadicVaListAndNakedAsmSoundness.vaCopy_cursor_fork_non_interference' does not depend on any axioms
'CVariadicVaListAndNakedAsmSoundness.caller_al_ge_actualXmmUsed_prevents_unsaved_xmm_ub' depends on axioms: [propext, Quot.sound]
'CVariadicVaListAndNakedAsmSoundness.ce1_underreported_al_reads_unsaved_xmm_slot_ub' depends on axioms: [propext, Quot.sound]
'CVariadicVaListAndNakedAsmSoundness.ce2_odd_gp_offset_u128_without_alignment_adjustment_corrupts_arg' depends on axioms: [propext, Quot.sound]
'CVariadicVaListAndNakedAsmSoundness.aapcs64_gr_offs_contrasts_with_sysv_backfill' does not depend on any axioms
'CVariadicVaListAndNakedAsmSoundness.ce3_c_default_promoted_f32_read_as_unpromoted_f32_type_mismatch_ub' depends on axioms: [propext]
'CVariadicVaListAndNakedAsmSoundness.passIndirectly_forces_indirect_on_sysv_x86_64' does not depend on any axioms
'CVariadicVaListAndNakedAsmSoundness.nakedFnContract_sound' depends on axioms: [propext, Quot.sound]
'CVariadicVaListAndNakedAsmSoundness.ce4_nonzero_stack_delta_in_naked_ret_corrupts_return' depends on axioms: [propext, Quot.sound]
module constants audited: 221 theorems, 412 definitions, 18 inductive types
axioms reachable from the module: [Quot.sound, propext]
audit passed: no axiom, opaque, unsafe or partial constant; no compiled recursion helper; no well-founded recursion; axioms within [propext, Quot.sound]
```

## Revalidation

To revalidate every empirical measurement, Lean 4 kernel theorem, environment audit check, and corpus metadata check from the report directory (`reports/rustc-c-variadic-va-list-abi-and-unsafe-naked-asm-lowering/`):

1. **Re-run all live `rustc`, `cargo miri`, `gcc -O2`, and cross-target LLVM IR probes:**
   ```bash
   python3 support/probe_c_variadic_and_naked_asm.py
   ```
   Verify exit code `0` and check that `support/probe_results.json` preserves all stdout strings (`ZERO_FP=200 MIXED_OVERFLOW=1220 NINE_FP=45 VALIST_SZ=24 VALIST_ALIGN=8`, `C_TO_RUST_VA=1220 C_VA_LIST_DECAY=1220 RUST_TO_C_VA_DECAY=600100`, `U128_ODD_GP_OK=1 U128_SPILL_R9_BACKFILL_OK=1 U128_OVERFLOW_ALIGN16_OK=1`, `NAKED_OK=35`). When re-running against `rustc 1.99.0+` (`>= 3ef0c22c`), confirm `miri_va_copy_fork_probe` flips from `rc = 1` (uninitialized `.inner.gp_offset`) to `rc = 0` (`CLONE_FORK=110`), while the `#![feature(c_variadic)]` negative probe `variadic_without_feature_gate_probe` becomes accepted on stable.
2. **Kernel-check and environment-audit the Lean `v4.34.1` formalization (writing `.olean` to a scratch directory and removing it afterwards):**
   ```bash
   AUDIT_TMP="$(mktemp -d)"
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     -R support -o "$AUDIT_TMP/CVariadicVaListAndNakedAsmSoundness.olean" \
     support/CVariadicVaListAndNakedAsmSoundness.lean
   LEAN_PATH="$AUDIT_TMP" lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     -R support support/EnvironmentAudit.lean
   rm -rf "$AUDIT_TMP"
   ```
   Confirm `audit passed` over `221 theorems, 412 definitions, 18 inductive types` with axioms within `[Quot.sound, propext]`.
3. **Validate corpus catalog and formatting from the corpus root:**
   ```bash
   python3 tools/reference.py catalog && python3 tools/reference.py check
   ```
