#!/usr/bin/env python3
"""Reproducible classifier and invariant checker for:
1. Production Rust FFI & inline-assembly workloads across four ecosystems
   (Fuchsia/Zircon/Starnix, Production Rust Cryptography, Linux Rust-for-Linux,
   and Mainstream Rust<->C Libraries) along six architectural axes.
2. Adversarial & reward-hacking bypass vectors under a bounded human-review
   threat model, partitioned into total mechanical defenses vs. explicit TCB /
   execution-environment assumptions.
"""

from __future__ import annotations

import collections
import json
import sys
from pathlib import Path
from typing import Any

VALID_MECHANISMS = {
    "asm!",
    "naked_asm!",
    "global_asm!",
    "external_.S/.asm",
    "compiled_C/C++",
    "target_feature_rust_simd",
    "rustc_intrinsic_asm",
}
VALID_DIRECTIONS = {
    "inline_in_frame",
    "rust_to_foreign",
    "foreign_to_rust",
    "reentrant_callback",
    "bidirectional_trampoline",
}
VALID_MEMORY_PROFILES = {
    "pure_nomem",
    "disjoint_slices",
    "in_place_overlapping",
    "overlapping_cyclic_heap",
    "mmio_volatile_or_dma",
    "faulting_user_memory",
    "kernel_or_process_state",
}
VALID_CONTROL_FLOW = {
    "normal_return",
    "asm_goto_label_and_patching",
    "trap_or_syscall",
    "non_call_context_switch",
    "pc_range_fault_recovery",
    "panic_catch_or_tunnel",
    "metadata_trap_section",
}
VALID_CONCURRENCY = {
    "sequential",
    "once_init_relaxed_atomic",
    "weak_memory_or_lkmm",
    "interrupts_or_preemption_or_mt",
}
VALID_VERIFICATION_TIERS = {
    "must_prove_mir_and_isa",
    "must_prove_with_binary_isa_model",
    "must_prove_ffi_boundary_plus_foreign_tcb",
    "kernel_or_vdso_tcb_assumption",
    "compiler_barrier_or_sidechannel_model",
}
VALID_DEFENSE_CLASSES = {
    "total_mechanical_defense",
    "explicit_tcb_or_env_assumption",
    "hybrid_mechanical_plus_tcb_assumption",
}

WORKLOADS: list[dict[str, Any]] = [
    # --- Ecosystem 1: Fuchsia / Zircon / Starnix ---
    {
        "id": "fuchsia-zx-vdso-syscalls",
        "ecosystem": "Fuchsia / Zircon / Starnix",
        "subject": "fuchsia.googlesource.com/fuchsia@fd31be1516bd2906c5b46be6c3ca3aa1adb162c0",
        "source_ref": "sdk/rust/zx-sys/src/definitions.rs:12-1104 (217 pub fn zx_*)",
        "mechanism": "compiled_C/C++",
        "direction": "rust_to_foreign",
        "memory_profile": "kernel_or_process_state",
        "control_flow": "trap_or_syscall",
        "concurrency": "interrupts_or_preemption_or_mt",
        "verification_tier": "kernel_or_vdso_tcb_assumption",
        "notes": "Zither-generated `#[link(name = \"zircon\")] unsafe extern \"C\"` vDSO bindings (channels, VMOs, clocks, futexes, restricted mode); kernel-provided dynamic vDSO.",
    },
    {
        "id": "starnix-restricted-enter-trampoline",
        "ecosystem": "Fuchsia / Zircon / Starnix",
        "subject": "fuchsia.googlesource.com/fuchsia@fd31be1516bd2906c5b46be6c3ca3aa1adb162c0",
        "source_ref": "src/starnix/kernel/syscall_loop/src/{lib.rs:51-145,trampoline_x64.S:13-160}; src/starnix/lib/extended_pstate/src/x86_64_asm.S:63-68",
        "mechanism": "external_.S/.asm",
        "direction": "bidirectional_trampoline",
        "memory_profile": "kernel_or_process_state",
        "control_flow": "non_call_context_switch",
        "concurrency": "interrupts_or_preemption_or_mt",
        "verification_tier": "must_prove_with_binary_isa_model",
        "notes": "Saves callee-saved regs + xrstor/xsave extended pstate, invokes `zx_restricted_enter` with `restricted_return_loop` vector entry, synthesizes 16 `.cfi_offset` directives from `zx_restricted_state_t`, calls back `restricted_exit_callback_c` with `#[allow(improper_ctypes)]` `*mut RestrictedEnterContext`.",
    },
    {
        "id": "starnix-hermetic-usercopy",
        "ecosystem": "Fuchsia / Zircon / Starnix",
        "subject": "fuchsia.googlesource.com/fuchsia@fd31be1516bd2906c5b46be6c3ca3aa1adb162c0",
        "source_ref": "src/starnix/lib/usercopy/src/lib.rs:11-90",
        "mechanism": "external_.S/.asm",
        "direction": "rust_to_foreign",
        "memory_profile": "faulting_user_memory",
        "control_flow": "pc_range_fault_recovery",
        "concurrency": "weak_memory_or_lkmm",
        "verification_tier": "must_prove_with_binary_isa_model",
        "notes": "PC-range-bounded `hermetic_copy`/`hermetic_zero`/`atomic_*_u32` pairs (`fn`..`fn_end`) redirected on page fault to `hermetic_copy_error`/`atomic_error` by Zircon exception handler.",
    },
    {
        "id": "fuchsia-fdf-driver-runtime-arena",
        "ecosystem": "Fuchsia / Zircon / Starnix",
        "subject": "fuchsia.googlesource.com/fuchsia@fd31be1516bd2906c5b46be6c3ca3aa1adb162c0",
        "source_ref": "sdk/lib/driver/runtime/rust/{fdf_sys/src/bindings.rs:87-202,channel/src/arena.rs:24-75}",
        "mechanism": "compiled_C/C++",
        "direction": "reentrant_callback",
        "memory_profile": "overlapping_cyclic_heap",
        "control_flow": "normal_return",
        "concurrency": "interrupts_or_preemption_or_mt",
        "verification_tier": "must_prove_ffi_boundary_plus_foreign_tcb",
        "notes": "Refcounted `fdf_arena_t` zero-copy shared heap allocations + C++ `fdf_dispatcher_t` async shutdown callbacks across co-located `driver_host` processes.",
    },
    # --- Ecosystem 2: Production Rust Cryptography ---
    {
        "id": "ring-perlasm-prefixed-kernels",
        "ecosystem": "Production Rust Cryptography",
        "subject": "briansmith/ring@b287c58f1dc2764e98c7c48583c2726ded52e6c7",
        "source_ref": "src/prefixed.rs:25-54; build/build/core.rs:36-75; src/aead/aes_gcm/vaesclmulavx2.rs:24-55; src/ec/curve25519/adx.rs:29-45",
        "mechanism": "external_.S/.asm",
        "direction": "rust_to_foreign",
        "memory_profile": "in_place_overlapping",
        "control_flow": "normal_return",
        "concurrency": "once_init_relaxed_atomic",
        "verification_tier": "must_prove_with_binary_isa_model",
        "notes": "Perlasm `.pl` -> `.S`/`.asm` + Fiat-Crypto `.S` linked with crate-versioned `#[link_name]` prefix (`ring_core_<ver>_*`); AES-GCM VAES passes `in_out` as both `*const u8` and `*mut u8`; CPUID gated by `OnceNonZeroU32` + `HIDDEN` `avx2_available`/`adx_bmi2_available` (`src/cpu/x86_64.rs:45-58,219-227,313-321`, `crypto/crypto.c:30-33`).",
    },
    {
        "id": "aws-lc-rs-perlasm-mlkem-ia32cap",
        "ecosystem": "Production Rust Cryptography",
        "subject": "aws/aws-lc-rs@104142736550c9860d0dfdb389e0d6c4c51e0005 (submodule aws/aws-lc@cd481c207e38f06aeb5766f4a1cdfce10a4c0af8)",
        "source_ref": "aws-lc-rs/src/kem.rs:48-103; aws-lc-sys/src/lib.rs:15-74; builder/cc_builder.rs:39-43; aws-lc/crypto/fipsmodule/{cpucap/cpu_intel.c:272-302,ml_kem/mlkem_native_backend.h:10-18}",
        "mechanism": "external_.S/.asm",
        "direction": "rust_to_foreign",
        "memory_profile": "disjoint_slices",
        "control_flow": "normal_return",
        "concurrency": "once_init_relaxed_atomic",
        "verification_tier": "must_prove_with_binary_isa_model",
        "notes": "Links AWS-LC FIPS/crypto C + Perlasm `.S`/`.asm` + native AVX2/AArch64 ML-KEM backends via `CcBuilder`/`CMakeBuilder`/`NasmBuilder`; retains shared mutable `OPENSSL_ia32cap_P[0..3]` overridable via `OPENSSL_ia32cap` env var.",
    },
    {
        "id": "zeroize-dse-asm-memory-barrier",
        "ecosystem": "Production Rust Cryptography",
        "subject": "RustCrypto/utils@0feca06cf87e61567033a333feb79ecf3c427fea",
        "source_ref": "zeroize/src/{barrier.rs:52-89,bulk.rs:6-60}",
        "mechanism": "asm!",
        "direction": "inline_in_frame",
        "memory_profile": "mmio_volatile_or_dma",
        "control_flow": "normal_return",
        "concurrency": "sequential",
        "verification_tier": "compiler_barrier_or_sidechannel_model",
        "notes": "Bulk erasure executes `write_bytes` followed by `asm!(\"# {}\", in(reg) ptr, options(readonly, preserves_flags, nostack))` on 9 `HAS_ASM` targets so LLVM MemorySSA treats the buffer as observed (falls back to `black_box` under `cfg(miri)`).",
    },
    {
        "id": "subtle-and-black-box-value-range-barriers",
        "ecosystem": "Production Rust Cryptography",
        "subject": "dalek-cryptography/subtle@369e7463e85921377a5f2df80aabcbbc6d57a930; rust-lang/rust@c7d5ba59d8e11ee2e2204b173458eec4cb41c973",
        "source_ref": "subtle/src/lib.rs:99-100,222-244; library/core/src/hint.rs:490-492; compiler/rustc_codegen_llvm/src/intrinsic.rs:52-84,594-603",
        "mechanism": "rustc_intrinsic_asm",
        "direction": "inline_in_frame",
        "memory_profile": "pure_nomem",
        "control_flow": "normal_return",
        "concurrency": "sequential",
        "verification_tier": "compiler_barrier_or_sidechannel_model",
        "notes": "`subtle::Choice::from(u8)` defeats LLVM boolean value-range inference via `#[inline(never)] read_volatile(&input)` (default) or `core::hint::black_box` (feature `core_hint_black_box`), which `rustc_codegen_llvm` lowers to empty side-effecting LLVM inline asm `\"\"` with constraints `\"r,~{memory}\"` (`\"~{memory}\"` for ZSTs).",
    },
    # --- Ecosystem 3: OS Kernels (Linux Rust-for-Linux) ---
    {
        "id": "linux-rfl-static-branch-asm-goto",
        "ecosystem": "OS Kernels (Linux Rust-for-Linux)",
        "subject": "torvalds/linux@5f22fb20497f4983094131f00a734362300d22d2",
        "source_ref": "rust/kernel/jump_label.rs:49-63; rust/kernel/generated_arch_static_branch_asm.rs.S:7; arch/x86/include/asm/jump_label.h:15-38",
        "mechanism": "asm!",
        "direction": "inline_in_frame",
        "memory_profile": "kernel_or_process_state",
        "control_flow": "asm_goto_label_and_patching",
        "concurrency": "interrupts_or_preemption_or_mt",
        "verification_tier": "kernel_or_vdso_tcb_assumption",
        "notes": "Uses Rust `asm_goto` (`l_yes = label { break 'my_label true; }`) with C-preprocessed `ARCH_STATIC_BRANCH_ASM` emitting 5-byte NOP + `.pushsection __jump_table, \"aw\"` for live kernel text patching.",
    },
    {
        "id": "linux-rfl-warn-bug-table-asm",
        "ecosystem": "OS Kernels (Linux Rust-for-Linux)",
        "subject": "torvalds/linux@5f22fb20497f4983094131f00a734362300d22d2",
        "source_ref": "rust/kernel/bug.rs:34-45,67-76; rust/kernel/generated_arch_warn_asm.rs.S:7; arch/x86/include/asm/bug.h:65-75",
        "mechanism": "asm!",
        "direction": "inline_in_frame",
        "memory_profile": "kernel_or_process_state",
        "control_flow": "metadata_trap_section",
        "concurrency": "interrupts_or_preemption_or_mt",
        "verification_tier": "kernel_or_vdso_tcb_assumption",
        "notes": "Emits `UD2`/`UD1` trap + `.pushsection __bug_table, \"aw\"` referencing `sym FILE`, `const line!()`, `const FLAGS` via `kernel::asm!` (`options(att_syntax)` wrapper in `rust/kernel/lib.rs:248-254`).",
    },
    {
        "id": "linux-rfl-c-inline-helpers-extable-altinstr-barriers",
        "ecosystem": "OS Kernels (Linux Rust-for-Linux)",
        "subject": "torvalds/linux@5f22fb20497f4983094131f00a734362300d22d2",
        "source_ref": "rust/helpers/{helpers.c:12-111,uaccess.c:5-29,barrier.c:5-48,atomic.c:14-90}; rust/kernel/sync/barrier.rs:45-78; arch/x86/include/asm/{asm.h:185-230,alternative.h:140-170}",
        "mechanism": "compiled_C/C++",
        "direction": "rust_to_foreign",
        "memory_profile": "faulting_user_memory",
        "control_flow": "pc_range_fault_recovery",
        "concurrency": "weak_memory_or_lkmm",
        "verification_tier": "must_prove_ffi_boundary_plus_foreign_tcb",
        "notes": "70 C helper files (`__rust_helper __always_inline` for Clang+Rust LTO) wrap C inline-asm macros including `_ASM_EXTABLE` (`.pushsection __ex_table`), `ALTERNATIVE` (`.altinstructions`/`.altinstr_replacement`), LKMM atomics, and hardware barriers; Rust itself emits `core::arch::asm!(\"\")` only for `barrier()`.",
    },
    {
        "id": "linux-rfl-file-operations-vtable-callbacks",
        "ecosystem": "OS Kernels (Linux Rust-for-Linux)",
        "subject": "torvalds/linux@5f22fb20497f4983094131f00a734362300d22d2",
        "source_ref": "rust/kernel/miscdevice.rs:153-160,234-446",
        "mechanism": "compiled_C/C++",
        "direction": "foreign_to_rust",
        "memory_profile": "overlapping_cyclic_heap",
        "control_flow": "normal_return",
        "concurrency": "interrupts_or_preemption_or_mt",
        "verification_tier": "must_prove_ffi_boundary_plus_foreign_tcb",
        "notes": "Const `bindings::file_operations` struct of `extern \"C\" fn` callbacks (`open`, `release`, `mmap`, `read_iter`, `write_iter`, `unlocked_ioctl`) storing `ForeignOwnable::into_foreign()` in `(*raw_file).private_data` (`void*`) and reclaiming via `from_foreign()` in `release`.",
    },
    # --- Ecosystem 4: Mainstream Rust<->C Libraries ---
    {
        "id": "rusqlite-opaque-handles-and-clientdata-callbacks",
        "ecosystem": "Mainstream Rust<->C Libraries",
        "subject": "rusqlite/rusqlite@388f5d40aab82b2cd40d3a2f94c06dc9e164382d",
        "source_ref": "src/{busy.rs:55-83,inner_connection.rs:344-454,error.rs:448-473}; libsqlite3-sys/build.rs:31-65",
        "mechanism": "compiled_C/C++",
        "direction": "reentrant_callback",
        "memory_profile": "overlapping_cyclic_heap",
        "control_flow": "panic_catch_or_tunnel",
        "concurrency": "interrupts_or_preemption_or_mt",
        "verification_tier": "must_prove_ffi_boundary_plus_foreign_tcb",
        "notes": "Opaque `*mut sqlite3`/`sqlite3_stmt`, `Box::into_raw` userdata registered via `sqlite3_set_clientdata` with `free_boxed_value::<T>` destructor, `catch_unwind` in `busy_handler_callback`, `sqlite3_errmsg`/`sqlite3_errcode` decoding, and runtime single-threaded mutex magic check (`8`).",
    },
    {
        "id": "flate2-cyclic-zstream-and-allocator-handoff",
        "ecosystem": "Mainstream Rust<->C Libraries",
        "subject": "rust-lang/flate2-rs@bda759ec690f52cb954a029dcf35749f6fcc8a59",
        "source_ref": "src/ffi/c.rs:25-115,188-207",
        "mechanism": "compiled_C/C++",
        "direction": "reentrant_callback",
        "memory_profile": "overlapping_cyclic_heap",
        "control_flow": "normal_return",
        "concurrency": "sequential",
        "verification_tier": "must_prove_ffi_boundary_plus_foreign_tcb",
        "notes": "`StreamWrapper` deliberately uses raw `*mut mz_stream` (not `Box<mz_stream>`) because C's `mz_internal_state` retains a cyclic back-pointer to `inner`; passes `extern \"C\" fn zalloc/zfree` prepending a `usize` layout header for Rust `alloc`/`dealloc`.",
    },
    {
        "id": "zlib-rs-c-abi-and-target-feature-dispatch",
        "ecosystem": "Mainstream Rust<->C Libraries",
        "subject": "trifectatechfoundation/zlib-rs@f6a2b3f097d02428ad4c7e5ddf4b54c3c271bf6d",
        "source_ref": "zlib-rs/src/{c_api.rs:64-95,allocate.rs:16-95,adler32.rs:19-47,adler32/avx2.rs:33-35}",
        "mechanism": "target_feature_rust_simd",
        "direction": "foreign_to_rust",
        "memory_profile": "disjoint_slices",
        "control_flow": "normal_return",
        "concurrency": "once_init_relaxed_atomic",
        "verification_tier": "must_prove_mir_and_isa",
        "notes": "Rust-implemented C-ABI `#[repr(C)] z_stream` with `posix_memalign` 64B alignment (`size == 0` guard against non-null dangling `malloc(0)`) and `#[target_feature(enable = \"avx2\")]` / `avx512` / `neon` runtime-dispatched SIMD kernels.",
    },
    {
        "id": "rust-openssl-exdata-callbacks-panic-tunnel-and-free",
        "ecosystem": "Mainstream Rust<->C Libraries",
        "subject": "rust-openssl/rust-openssl@dbc5ecad7dbfec35cdfee73c5337e3ee9b8d0f3f",
        "source_ref": "openssl/src/{ex_data.rs:8-32,error.rs:115-195,string.rs:11-96,ssl/callbacks.rs:42-112,ssl/mod.rs:3981-4015}",
        "mechanism": "compiled_C/C++",
        "direction": "reentrant_callback",
        "memory_profile": "overlapping_cyclic_heap",
        "control_flow": "panic_catch_or_tunnel",
        "concurrency": "interrupts_or_preemption_or_mt",
        "verification_tier": "must_prove_ffi_boundary_plus_foreign_tcb",
        "notes": "Opaque `SSL`/`SSL_CTX` pointers, typed `ex_data::Index<T, U>` closure lookup surviving SNI `SSL_set_SSL_CTX` swaps, `OPENSSL_free`/`CRYPTO_free` allocator handoff, thread-local `ERR_get_error_all` + `SSL_ERROR_SYSCALL` BIO `io::Error` retrieval, and BIO panic smuggling via `bio::take_panic` -> `resume_unwind`.",
    },
]

ADVERSARIAL_VECTORS: list[dict[str, Any]] = [
    # Category 1: Template / Directive Smuggling
    {
        "id": "V1.1",
        "category": "Template & Directive Smuggling",
        "name": "ELF/Mach-O constructor injection (`.section .init_array` / `.mod_init_func`)",
        "surfaces": ["asm!", "naked_asm!", "global_asm!", "external_.S/.asm"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "template_directive_smuggling_init_array",
        "defense": "Reject arbitrary section-switching directives in `asm!`/`naked_asm!`/`global_asm!` via closed directive allowlist AND audit final object/linked ELF/Mach-O/PE section tables (forbid unverified `.init_array`/`.preinit_array`/`.fini_array`/`.ctors`/`.CRT$XCU`).",
    },
    {
        "id": "V1.2",
        "category": "Template & Directive Smuggling",
        "name": "Assembler `.macro` instruction spoofing",
        "surfaces": ["asm!", "naked_asm!", "global_asm!", "external_.S/.asm"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "macro_byte_spoofing_and_set_symbol_aliasing",
        "defense": "Never trust pre-assembly text scanning of mnemonics; forbid `.macro`/`.irp`/`.rept` in inline asm AND decode/verify post-assembly machine bytes in the linked object/image.",
    },
    {
        "id": "V1.3",
        "category": "Template & Directive Smuggling",
        "name": "Raw byte/opcode smuggling (`.byte`/`.inst`/`.insn`) & trailing prefix bleed (`LOCK`/REX)",
        "surfaces": ["asm!", "naked_asm!", "global_asm!", "external_.S/.asm"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "macro_byte_spoofing_and_set_symbol_aliasing",
        "defense": "Verify decoded machine-code instruction stream emitted for the function body and ensure complete instruction boundaries at inline-asm exit (no dangling x86 prefix byte).",
    },
    {
        "id": "V1.4",
        "category": "Template & Directive Smuggling",
        "name": "Symbol aliasing & hijacking via `.set` / `.equiv` / `.symver`",
        "surfaces": ["asm!", "global_asm!", "external_.S/.asm"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "macro_byte_spoofing_and_set_symbol_aliasing",
        "defense": "Resolve every call target and symbol alias directly from the final object/linked symbol table (`st_value`, `st_size`, relocations), rejecting unverified symbol aliases.",
    },
    # Category 2: Option / Contract & Target-Feature Lies
    {
        "id": "V2.1",
        "category": "Option, Contract & Target-Feature Lies",
        "name": "False `options(nomem)` / `options(readonly)` / `options(pure)` effect promises",
        "surfaces": ["asm!"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "option_contract_lies_and_unguarded_target_feature",
        "defense": "Generate mandatory proof obligations from MIR `TerminatorKind::InlineAsm` options against a trace-observing ISA semantics (no memory read/write/sync events for `nomem`, no stores/sync for `readonly`, deterministic termination for `pure`).",
    },
    {
        "id": "V2.2",
        "category": "Option, Contract & Target-Feature Lies",
        "name": "False `options(preserves_flags)` / `options(nostack)` / `options(noreturn)`",
        "surfaces": ["asm!"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "hidden_hardware_abi_clobbers_df_redzone_cfi_vzeroupper",
        "defense": "Require ISA-level proof that status/FP/vector flags (`EFLAGS`/`MXCSR`/`NZCV`/`FPSR`/`fcsr`/`vtype`/`vl`) are preserved, stack pointer and red zone are untouched, and `noreturn` blocks never reach fallthrough.",
    },
    {
        "id": "V2.3",
        "category": "Option, Contract & Target-Feature Lies",
        "name": "False `lateout` / register-overlap contract",
        "surfaces": ["asm!"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": None,
        "defense": "Quantify source-level `asm!` proofs over all register assignments permitted by operand classes (including `lateout` aliasing `in`), or bind proof to the exact post-regalloc binary bytes.",
    },
    {
        "id": "V2.4",
        "category": "Option, Contract & Target-Feature Lies",
        "name": "Unverified `#[target_feature]` CPUID / OS XCR0 / `hwcap` guards",
        "surfaces": ["target_feature_rust_simd", "asm!", "external_.S/.asm"],
        "defense_class": "hybrid_mechanical_plus_tcb_assumption",
        "poc_verified": "option_contract_lies_and_unguarded_target_feature",
        "defense": "Mechanically require every call to a `#[target_feature]` or extended-ISA kernel to discharge a hardware-capability precondition; ground the `cpuid`/`xgetbv`/`getauxval` probe semantics (and errata like Intel SKD052) in the TCB audit log.",
    },
    # Category 3: Untyped .o / Linker & Build Hijacking
    {
        "id": "V3.1",
        "category": "Untyped Object, Linker & Build Hijacking",
        "name": "`#[link_name]` / `#[link_ordinal]` untyped signature mismatch or symbol redirection",
        "surfaces": ["compiled_C/C++", "external_.S/.asm", "global_asm!"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "untyped_object_and_linker_hijacking",
        "defense": "Bind verified Rust `DefId`s via `CodegenFnAttrs.symbol_name`/`link_ordinal` and `FnAbi`/`PassMode` directly to the resolved foreign symbol's machine/C signature in the linked artifact.",
    },
    {
        "id": "V3.2",
        "category": "Untyped Object, Linker & Build Hijacking",
        "name": "Weak symbol override & static archive-order shadowing (`.a` left-to-right resolution)",
        "surfaces": ["compiled_C/C++", "external_.S/.asm", "global_asm!"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "untyped_object_and_linker_hijacking",
        "defense": "Bind proofs to the final linked ELF/Mach-O/PE image (or enforce unique symbol binding across all archives/objects with duplicate-symbol rejection), never solely to individual unlinked `.o` files.",
    },
    {
        "id": "V3.3",
        "category": "Untyped Object, Linker & Build Hijacking",
        "name": "`LD_PRELOAD` / `DYLD_INSERT_LIBRARIES` / dynamic loader interposition",
        "surfaces": ["compiled_C/C++"],
        "defense_class": "explicit_tcb_or_env_assumption",
        "poc_verified": "untyped_object_and_linker_hijacking",
        "defense": "Cannot be prevented statically for dynamically linked libraries; static linking or `-Wl,-Bsymbolic` narrows intra-DSO interposition, while dynamic loader/OS integrity remains an explicit deployment/execution-environment TCB assumption.",
    },
    {
        "id": "V3.4",
        "category": "Untyped Object, Linker & Build Hijacking",
        "name": "Cross-language LLVM bitcode / LTO boundary evasion (`__always_inline` attribute mismatch)",
        "surfaces": ["compiled_C/C++"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": None,
        "defense": "Either forbid unverified foreign LLVM bitcode merging during verified compilation or verify the post-LTO IR / final linked machine code rather than pre-LTO MIR alone.",
    },
    {
        "id": "V3.5",
        "category": "Untyped Object, Linker & Build Hijacking",
        "name": "`build.rs` / proc-macro verify-vs-release divergence (environment fingerprinting)",
        "surfaces": ["compiled_C/C++", "external_.S/.asm", "asm!"],
        "defense_class": "hybrid_mechanical_plus_tcb_assumption",
        "poc_verified": "build_rs_verify_vs_release_divergence",
        "defense": "OS-sandbox `build.rs`/proc-macros (execution-environment assumption) AND mechanically bind verification to the exact cryptographic digest of the final shipped binary / generated artifacts (single build-and-verify artifact pipeline).",
    },
    # Category 4: Hidden Hardware & ABI Clobbers
    {
        "id": "V4.1",
        "category": "Hidden Hardware & ABI Clobbers",
        "name": "x86 Direction Flag (`DF=1`) exit clobber & x87 FPU stack leak (`EMMS`)",
        "surfaces": ["asm!", "naked_asm!", "global_asm!", "external_.S/.asm"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "hidden_hardware_abi_clobbers_df_redzone_cfi_vzeroupper",
        "defense": "Include `RFLAGS.DF == 0` and x87 tag-word emptiness (`0xffff` / TOS preservation) in the formal ISA postcondition required on every normal return from x86 assembly.",
    },
    {
        "id": "V4.2",
        "category": "Hidden Hardware & ABI Clobbers",
        "name": "AVX upper-YMM dirty state (missing `vzeroupper`), AArch64 `FPSR.QC`, RISC-V `vstart`/`vtype`",
        "surfaces": ["asm!", "naked_asm!", "global_asm!", "external_.S/.asm"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "hidden_hardware_abi_clobbers_df_redzone_cfi_vzeroupper",
        "defense": "Model architectural SIMD/FP/vector status state (`XINUSE`/YMM upper bits, `FPSR.QC`, `vstart == 0`, `vtype`/`vl`) in ISA postconditions; note x86 `vzeroupper` omission is a microarchitectural transition penalty rather than architectural state corruption on SysV, whereas `vstart != 0` and `FPSR` violate ABI invariants.",
    },
    {
        "id": "V4.3",
        "category": "Hidden Hardware & ABI Clobbers",
        "name": "SysV/Apple 128-byte red-zone corruption under false `options(nostack)`",
        "surfaces": ["asm!"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "hidden_hardware_abi_clobbers_df_redzone_cfi_vzeroupper",
        "defense": "Enforce strict memory-footprint disjointness in the ISA semantics so `options(nostack)` forbids any read/write at or below `SP` (including `[SP - 128, SP)` red zone).",
    },
    {
        "id": "V4.4",
        "category": "Hidden Hardware & ABI Clobbers",
        "name": "Missing/forged DWARF `.cfi_*` / `.eh_frame` or Win64 `.pdata`/`.xdata` unwind metadata",
        "surfaces": ["naked_asm!", "global_asm!", "external_.S/.asm"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "hidden_hardware_abi_clobbers_df_redzone_cfi_vzeroupper",
        "defense": "Mechanically verify emitted `.eh_frame` FDEs / `.pdata`+`.xdata` unwind programs at every potentially interrupting PC against the machine instruction frame transitions (or prohibit unwinding through unverified frames).",
    },
    {
        "id": "V4.5",
        "category": "Hidden Hardware & ABI Clobbers",
        "name": "Partial-vector callee-save clobbers (Win64 `xmm6..xmm15`, AAPCS64 low 64-bit `d8..d15`, Apple `x18`)",
        "surfaces": ["naked_asm!", "global_asm!", "external_.S/.asm", "asm!"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": None,
        "defense": "Parameterize ABI callee-save frame conditions by target triple (`xmm6..xmm15` full 128-bit on Win64, `v8..v15` lower 64 bits `d8..d15` on AAPCS64, reserved `x18` on Darwin/Windows ARM64) and require machine proof of preservation.",
    },
    # Category 5: Type, Validity, Aliasing & Control-Flow Laundering
    {
        "id": "V5.1",
        "category": "Type, Validity, Aliasing & Control-Flow Laundering",
        "name": "Writing invalid `bool` (`!= 0,1`), `NonZero*` (`0`), `char`, or enum discriminant bits in C/asm",
        "surfaces": ["compiled_C/C++", "asm!", "external_.S/.asm"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "validity_aliasing_and_longjmp_laundering",
        "defense": "Require FFI/asm boundary contracts (or runtime boundary sanitizers verified by proof) to prove Rust validity predicates on every return value and mutated output buffer before constructing typed Rust values.",
    },
    {
        "id": "V5.2",
        "category": "Type, Validity, Aliasing & Control-Flow Laundering",
        "name": "Breaking Tree Borrows / LLVM `noalias` protectors via reentrant FFI callback or cyclic C struct",
        "surfaces": ["compiled_C/C++", "external_.S/.asm", "global_asm!"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "validity_aliasing_and_longjmp_laundering",
        "defense": "Enforce reentrancy-aware borrow/aliasing contracts (disallow mutating memory protected by an active outer `&mut`/`&` during any foreign call; use `Opaque<T>`/`UnsafeCell`/raw pointers for cyclic C graphs like `flate2` `mz_stream` and Linux `file`).",
    },
    {
        "id": "V5.3",
        "category": "Type, Validity, Aliasing & Control-Flow Laundering",
        "name": "Pointer provenance stripping / integer-to-pointer forging across FFI/asm",
        "surfaces": ["compiled_C/C++", "asm!", "external_.S/.asm"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": None,
        "defense": "Track explicit provenance/allocation-capability tokens across the Rust-to-machine linking relation (`expose_provenance` / `without_provenance` discipline; forbid deriving Rust heap references from forged integers).",
    },
    {
        "id": "V5.4",
        "category": "Type, Validity, Aliasing & Control-Flow Laundering",
        "name": "C `setjmp`/`longjmp` or foreign exception crossing non-unwind Rust frames (skipping `Drop`)",
        "surfaces": ["compiled_C/C++", "external_.S/.asm"],
        "defense_class": "hybrid_mechanical_plus_tcb_assumption",
        "poc_verified": "validity_aliasing_and_longjmp_laundering",
        "defense": "Mechanically verify Rust-side ABI (`extern \"C-unwind\"` vs `extern \"C\"`, panic-catching wrappers) and prove absence of `longjmp`/forced unwind across Rust frames for verified foreign code; for unverified C libraries, log non-longjmp compliance explicitly in the TCB audit log.",
    },
    # Category 6: Spec-Surface Hiding
    {
        "id": "V6.1",
        "category": "Spec-Surface Hiding",
        "name": "Burying spec meaning inside C headers, `bindgen` generated code, or C macros",
        "surfaces": ["compiled_C/C++"],
        "defense_class": "total_mechanical_defense",
        "poc_verified": "spec_surface_hiding_via_c_header_or_bindgen",
        "defense": "Compute the complete transitive dependency closure of every stated specification (including `include!`d `OUT_DIR` bindings, constants, types, and predicates) and surface every transitively referenced definition on the human-reviewed specification surface (or reject opaque external spec dependencies).",
    },
    {
        "id": "V6.2",
        "category": "Spec-Surface Hiding",
        "name": "Hiding semantic assumptions in DWARF/BTF debug hints or unlogged dynamic libraries",
        "surfaces": ["compiled_C/C++", "external_.S/.asm"],
        "defense_class": "hybrid_mechanical_plus_tcb_assumption",
        "poc_verified": None,
        "defense": "Never admit non-normative DWARF/BTF hints as trusted verification premises; mechanically enumerate every `DT_NEEDED` DSO, `extern` symbol, and native link library into the TCB audit log so zero unlogged foreign code can exist silently.",
    },
]


def validate() -> dict[str, Any]:
    for w in WORKLOADS:
        assert w["mechanism"] in VALID_MECHANISMS, w
        assert w["direction"] in VALID_DIRECTIONS, w
        assert w["memory_profile"] in VALID_MEMORY_PROFILES, w
        assert w["control_flow"] in VALID_CONTROL_FLOW, w
        assert w["concurrency"] in VALID_CONCURRENCY, w
        assert w["verification_tier"] in VALID_VERIFICATION_TIERS, w

    for v in ADVERSARIAL_VECTORS:
        assert v["defense_class"] in VALID_DEFENSE_CLASSES, v
        for s in v["surfaces"]:
            assert s in VALID_MECHANISMS, (v["id"], s)

    eco_counts = collections.Counter(w["ecosystem"] for w in WORKLOADS)
    mech_counts = collections.Counter(w["mechanism"] for w in WORKLOADS)
    tier_counts = collections.Counter(w["verification_tier"] for w in WORKLOADS)
    cat_counts = collections.Counter(v["category"] for v in ADVERSARIAL_VECTORS)
    def_counts = collections.Counter(v["defense_class"] for v in ADVERSARIAL_VECTORS)
    poc_count = sum(1 for v in ADVERSARIAL_VECTORS if v["poc_verified"] is not None)

    return {
        "workload_count": len(WORKLOADS),
        "workloads_by_ecosystem": dict(eco_counts),
        "workloads_by_mechanism": dict(mech_counts),
        "workloads_by_verification_tier": dict(tier_counts),
        "adversarial_vector_count": len(ADVERSARIAL_VECTORS),
        "vectors_by_category": dict(cat_counts),
        "vectors_by_defense_class": dict(def_counts),
        "vectors_empirically_reproduced_in_pocs": poc_count,
        "workloads": WORKLOADS,
        "adversarial_vectors": ADVERSARIAL_VECTORS,
    }


def main() -> int:
    summary = validate()
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
