# Trusted-Component Inventory and Assumption Ledger of the Delivered Verified Rustc Toolchain

## Summary

Delivering a verified drop-in replacement for `rustc` requires an explicit, byte-accurate assumption ledger enumerating every hardware, operating-system, prover, compiler, assembler, linker, C runtime (CRT), unwinder, and standard-library component that remains trusted across the toolchain's execution and target-delivery modes. Direct inspection and cryptographic measurement of the pinned **Rust 1.99.1** toolchain (`rust-lang/rust` commit `58cf8f9c35b355199727627d07ae34a4e2846d67`, bundled **LLVM 23.1.1** commit `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), **Lean 4 v4.34.1** (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`, bundled **Clang/LLD 22.1.4** commit `35990504507d79e0b9deb809c8ee5e1b34ceef20`), **Anneal** (`joshlf/anneal` commit `7abf0691c404393e3e4fc26eb3d4094e3170b5c7`), external Lean 4 kernel checkers (`lean4export`, `lean4lean`, `nanoda_lib`), and all **8 Tier 1 target sysroots** establish six governing findings:

1. **Five-layer assumption-ledger taxonomy:** Every component in the delivered toolchain falls into one of five distinct trust strata:
   - **Layer 1 — Prover & Proof-Checking Core:** Lean 4 C++ kernel (`8,091 LOC`), `.olean` boundary auditor (`trusted/audit`, `4,206 LOC`), semantic specification (`trusted/lean`, `1,354 LOC`), and optional independent kernel checkers (`nanoda_lib` in Rust at `4,872 LOC`; `lean4lean` in Lean 4 at `9,418 LOC`, checked via `lean4export` at `748 LOC`).
   - **Layer 2 — Native Checker Execution Pipeline (when running a verified validator/compiler as native machine code rather than inside the kernel):** Lean's LCNF/IR compiler (`26,759 LOC`), C++ runtime (`libleanrt.a`, `21,885 LOC` including `mimalloc v3.4.4`), bundled `clang` and `ld.lld` `22.1.4` (`142.45 MiB` across `libLLVM.so.22.1` + `libclang-cpp.so.22.1` + `bin/ld.lld`), static **GMP 6.3.0** (`lib/libgmp.a`, `1,668,288 B`), `libuv v1.48.0`, `OpenSSL 3.6.0`, `libc++`/`libc++abi`/`libunwind`, and the NixOS 18.03 glibc `2.26` stub sysroot.
   - **Layer 3 — Frontend Capture & Pre-Verification Rustc Stages:** `rustc` (`648,536 B`) + `librustc_driver-7ed0375ae352bd75.so` (`158,240,640 B`) + `libLLVM.so.23.1-rust-1.99.1-stable` (`208,167,760 B`) when using `rustc` for parsing, macro expansion, typechecking, and MIR capture (`trusted/rustc-capture`), or until those stages are replaced or translation-validated.
   - **Layer 4 — Target Object Emission, Assembler, Linker, CRT Startup, Unwinder, Loader, and System Libc across 8 Tier 1 Targets:** Per-target MC/assembler (`LLVM MC` vs. verified binary emission), `rust-lld` (`11,879,600 B`, LLVM 23.1.1 LLD) or platform linkers (`ld.bfd`, `ld64`, `link.exe`), CRT startup/teardown objects (`Scrt1.o`, `crt1.o`, `crti.o`, `crtbeginS.o`, `crtendS.o`, `crtn.o`, `crt2.o`, `dllcrt2.o`, `rsbegin.o`, `rsend.o`, `msvcrt.lib`), target unwinders (`libgcc_s.so.1`, `libunwind.dylib`, Windows kernel RtlVirtualUnwind / SEH), OS program loaders (`ld-linux-x86-64.so.2`, `ld-linux-aarch64.so.1`, `ld-linux.so.2`, `dyld`, `ntdll.dll`), and target system libraries (`libc.so.6`, `libSystem.B.dylib`, `ucrtbase.dll` + `kernel32.dll`).
   - **Layer 5 — Host OS Kernel and Host/Target Hardware ISA:** Host Linux kernel (`7.1.6-1rodete1-amd64`), host glibc (`2.43`), host CPU (`Intel Xeon Family 6 Model 106 Stepping 6`, Ice Lake-SP), and target ISA silicon (x86-64, IA-32, AArch64) with their architectural errata and memory-ordering models.

2. **Concrete TCB size reduction across checker execution modes:**
   - **Mode A (Native-compiled Lean validator/compiler via `lean --c` + `leanc`):** Trusts **58,236 LOC** of Lean kernel + compiler + runtime source plus **Clang/LLD 22.1.4** (`~148 MiB` binaries), **GMP 6.3.0** (`1.67 MiB`), **mimalloc v3.4.4**, host glibc, and host OS/CPU.
   - **Mode B (In-kernel verification via `leanchecker --fresh` + `trusted/audit`):** Eliminates the 26,759-LOC LCNF compiler and bundled Clang/LLD from the per-compilation validation path, reducing the checker source TCB to the **8,091-LOC** Lean C++ kernel + **21,885-LOC** C++ runtime/GMP + **5,835-LOC** Anneal `trusted/` suite (**35,811 LOC** total), provided `trusted/audit` rejects `Lean.ofReduceBool`, `Lean.trustCompiler`, and custom `_native.*` axioms and validates `.olean` environment integrity.
   - **Mode C (Independent multi-kernel verification via `lean4export` + `nanoda_lib`):** Exporting the kernel environment via `lean4export` (`748 LOC`) and checking it in `nanoda_lib` (`4,872 LOC` of single-/multi-threaded Rust with zero dependencies on Lean's C++ runtime, `.olean` compact-region unpickler, or GMP) cross-checks the prover core across two independent implementations and languages.

3. **Target linker and assembler trust surface (`rust-lld` vs. host linkers):** In Rust `1.99.1`, `x86_64-unknown-linux-gnu` (`compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:19`) and `aarch64-unknown-linux-gnu` (`aarch64_unknown_linux_gnu.rs:17`) enable `LinkerFeatures::LLD` (`UseLld::Yes`) by default, invoking the bundled `rust-lld` (`11,879,600 B`, SHA-256 `9b6f51f9...`, dynamically linked against the 208.17 MiB `libLLVM.so.23.1-rust-1.99.1-stable`) via the `-fuse-ld=lld` `cc` driver wrapper. Even if a verified backend emits verified ELF/Mach-O/COFF `.o` files directly (bypassing LLVM's `MCAssembler`), `rust-lld` (or `ld.bfd`, `ld64`, `link.exe`) performs section merging, symbol resolution, relocation patching (`R_X86_64_PC32`, `R_X86_64_GOTPCREL`, `R_AARCH64_ADR_PREL_PG_HI21`), PLT/GOT synthesis, TLS relaxation (`R_X86_64_TPOFF32`, `R_X86_64_GOTTPOFF`), and dead-section garbage collection (`--gc-sections` / `-dead_strip` / `/OPT:REF`), keeping the linker inside the target binary TCB unless an output ELF/PE/Mach-O post-link validator is added.

4. **Pre-`main` and post-`main` CRT, unwinder, and dynamic loader code:** Every dynamically linked Rust executable runs unverified target machine code before `main` and during stack unwinding:
   - On Linux (`x86_64`, `aarch64`, `i686`), the kernel maps `/lib64/ld-linux-x86-64.so.2` (`230,200 B` on host), which relocates shared libraries and executes `.init_array` constructors before transferring control to `_start` in `Scrt1.o` (`1,640 B`) $\to$ `__libc_start_main` in `libc.so.6` (`2,018,344 B`) $\to$ Rust's `lang_start` $\to$ user `main`.
   - On Windows (`x86_64-pc-windows-gnu`), `rustc` ships its own 324-byte `rsbegin.o` (SHA-256 `4d04073d...`) and `rsend.o` (SHA-256 `244fd319...`) alongside MinGW-w64 `crt2.o`, `dllcrt2.o`, and `crtbegin.o`/`crtend.o` (`compiler/rustc_target/src/spec/base/windows_gnu.rs:34-80`).
   - Across all 8 Tier 1 targets, `libcompiler_builtins-<hash>.rlib` (`3.06–4.88 MiB` per target) provides software division/atomics/mem* intrinsics (`memcpy`, `memmove`, `memset`, `memcmp`, `__udivti3`), and `libunwind-<hash>.rlib` (`4.46–5.43 KiB`) bridges `panic!` unwinding into `libgcc_s.so.1` (`_Unwind_RaiseException`), macOS `libunwind.dylib`, or Windows SEH (`RtlRaiseException`).

5. **Complete cryptographic inventory across all 8 Tier 1 target sysroots:** Every binary, shared library, CRT object, `.rlib`, and `.rmeta` artifact in the pinned Rust `1.99.1` and Lean `v4.34.1` distributions is cataloged with exact byte sizes and SHA-256 digests in [`support/toolchain_tcb_inventory.json`](support/toolchain_tcb_inventory.json) (`1,998.88 MiB` across 689 target files for the 8 Tier 1 targets).

## Applicability

These findings govern:

- **Rust 1.99.1** (`rust-lang/rust` commit `58cf8f9c35b355199727627d07ae34a4e2846d67`), bundled **LLVM 23.1.1** (`rust-lang/llvm-project` commit `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), and the 8 official Tier 1 target sysroots (`aarch64-apple-darwin`, `aarch64-pc-windows-msvc`, `aarch64-unknown-linux-gnu`, `i686-pc-windows-msvc`, `i686-unknown-linux-gnu`, `x86_64-pc-windows-gnu`, `x86_64-pc-windows-msvc`, `x86_64-unknown-linux-gnu`).
- **Lean 4 v4.34.1** (`leanprover/lean4` commit `5045d0056413266e57c625dcd7c365b10e377c52`) and its bundled **LLVM/Clang/LLD 22.1.4** (`llvm/llvm-project` commit `35990504507d79e0b9deb809c8ee5e1b34ceef20`), **GMP 6.3.0**, **mimalloc v3.4.4**, **libuv v1.48.0**, **OpenSSL 3.6.0**, and **glibc 2.26** stub sysroot.
- **Anneal** (`joshlf/anneal` commit `7abf0691c404393e3e4fc26eb3d4094e3170b5c7`) and external Lean 4 checkers (`leanprover/lean4export` commit `df81913eee5519d5a88ae5b0fd701b5298cc29ab`, `digama0/lean4lean` commit `ef6be5b4cbbe993da60a27a4d5c9a71c5dd0da08`, `ammkrn/nanoda_lib` commit `511c72b5f7dc4de59c2ffe3e99e3d78d8bf6bf58`).
- **Reference Linux x86_64 Verification Host:** `Linux 7.1.6-1rodete1-amd64 x86_64`, Debian `GLIBC 2.43-7+gl1`, `Intel(R) Xeon(R) CPU @ 2.60GHz` (`GenuineIntel`, Family `6`, Model `106`, Stepping `6`).

## Findings

### 1. Prover, Compiler, and Auditor Component Inventory (Layers 1 & 2)

#### 1.1 Source Size and Verification Status of Prover & Auditor Subsystems

Basis: source + execution ([`support/toolchain_tcb_inventory.json`](support/toolchain_tcb_inventory.json), `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`, `joshlf/anneal` at `7abf0691c404393e3e4fc26eb3d4094e3170b5c7`).

| Component | Repository & Revision | Source Path | Files | LOC | Bytes | Audit / Verification Status |
| :--- | :--- | :--- | ---: | ---: | ---: | :--- |
| **Lean 4 C++ Kernel** | `leanprover/lean4` @ `5045d0056413` | `src/kernel/` | 37 | 8,091 | 344,132 | **Trusted Prover Core (Unverified C++):** Checks `ConstantInfo` declarations, definitional equality (`type_checker.cpp`), inductive positivity (`inductive.cpp`), and quotient soundness (`quot.cpp`). |
| **Lean 4 C++ Runtime & Headers** | `leanprover/lean4` @ `5045d0056413` | `src/runtime/` + `include/lean/` | 85 | 21,885 | 833,497 | **Trusted Runtime (Unverified C++/C):** Reference counting (`lean.h`), `compact.cpp` `.olean` unpickler, `mpz.cpp` GMP wrapper, `mimalloc v3.4.4`, `thread.cpp` task pool. Trusted whenever `lean` or `leanchecker` runs. |
| **Lean 4 LCNF & IR Compiler** | `leanprover/lean4` @ `5045d0056413` | `src/Lean/Compiler/` + `src/{LeanIR,Leanc}.lean` | 119 | 26,998 | 1,032,900 | **Conditionally Trusted (Unverified Lean 4):** Trusted **only** when executing compiled Lean code natively (`lean --c` + `leanc`) or via `native_decide` / `Lean.ofReduceBool`. Untrusted in pure kernel checking. |
| **Lean 4 C++ IR Interpreter** | `leanprover/lean4` @ `5045d0056413` | `src/library/ir_interpreter.{cpp,h}` | 2 | 1,259 | 67,454 | **Conditionally Trusted (Unverified C++):** Trusted only if `reduce_native` (`Lean.ofReduceBool`) or `evalConst` (`native_decide`) is permitted. |
| **Anneal Trusted Semantic Interface** | `joshlf/anneal` @ `7abf0691c404` | `trusted/lean/` (`Trusted.lean`, `TrustedBoundary.lean`) | 2 | 1,354 | 49,084 | **Human-Audited Specification Core:** Defines MIR syntax/semantics, `Compiler.Verified`, `VerificationResult`, and `Trusted.CrateTheorem`. |
| **Anneal `.olean` Boundary Auditor** | `joshlf/anneal` @ `7abf0691c404` | `trusted/audit/` | 6 | 4,206 | 158,382 | **Human-Audited Rust Inspector:** Parses `.olean` binary graphs directly, checks `Trusted.*` byte-for-byte against the reference stub, rejects `sorryAx` / `ofReduceBool` / `trustCompiler` / extra axioms, and invokes `leanchecker --fresh`. |
| **Anneal CLI & `rustc` MIR Capture** | `joshlf/anneal` @ `7abf0691c404` | `trusted/cargo-anneal/` + `trusted/rustc-capture/` | 5 | 275 | 9,058 | **Human-Audited Driver & Extractor:** Extracts `Runtime(PostCleanup)` MIR from `rustc` and orchestrates verification. |
| **`lean4export` (External Exporter)** | `leanprover/lean4export` @ `df81913eee55` | `Export.lean`, `Main.lean` | 2 | 748 | 24,812 | **Optional Cross-Check Bridge:** Exports `.olean` environments to line-oriented text format for independent checkers. |
| **`nanoda_lib` (External Rust Checker)** | `ammkrn/nanoda_lib` @ `511c72b5f7dc` | `src/` | 18 | 4,872 | 162,410 | **Optional Independent Kernel (Rust):** Checks exported Lean 4 environments in memory-safe Rust without C++, `.olean` mmap, or GMP (`num-bigint`). |
| **`lean4lean` (Formalized Kernel in Lean)** | `digama0/lean4lean` @ `ef6be5b4cbbe` | `Lean4Lean/` | 38 | 9,418 | 318,904 | **Mechanized Specification & Checker in Lean 4:** Formalizes Lean's typechecker (`TypeChecker.lean`) with soundness proofs against a formal Lean model. |

#### 1.2 Concrete Binary Identities and SHA-256 Digests for Lean `v4.34.1` (`lean-4.34.1-linux.tar.zst`)

Basis: execution ([`support/toolchain_tcb_inventory.json`](support/toolchain_tcb_inventory.json)).

| Binary / Library Path in Lean `v4.34.1` | Upstream Version & Commit | Size (Bytes) | SHA-256 Digest | Role in Toolchain Trust Boundary |
| :--- | :--- | ---: | :--- | :--- |
| `bin/lean` | Lean `v4.34.1` (`5045d0056413`) | 9,024 | `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550` | Elaborator, kernel driver, and `--c` C code emitter |
| `bin/leanchecker` | Lean `v4.34.1` (`5045d0056413`) | 51,080 | `ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe` | Standalone `.olean` kernel replay verifier (`--fresh`) |
| `bin/leanir` | Lean `v4.34.1` (`5045d0056413`) | 220,464 | `ccfab978605f2b346cc8b82374917468aa6bc02498337b0013737dec2cb194e9` | Separate-process LCNF-to-IR/C code generator |
| `bin/leanc` | Lean `v4.34.1` (`5045d0056413`) | 36,896 | `68a45f8329e2d79133cdcc7b1fa494e37844282d7b5f8908ce1deda7cfdf161a` | C compiler / linker wrapper driver |
| `bin/lake` | Lean `v4.34.1` (`5045d0056413`) | 13,840 | `6f53827dab18010d6c690d14c8401cacabc1db958edb3552a877ed4cf1dd995d` | Build orchestrator and package manager |
| `bin/clang` | LLVM `22.1.4` (`35990504507d`) | 119,320 | `9fcd5fc4baeea9c449bcc9ca4b9db7714465107669498b0056a853f22f5f4def` | Bundled C compiler for Lean native binaries |
| `bin/ld.lld` | LLVM `22.1.4` (`35990504507d`) | 6,001,368 | `d32d5121d96810b624306e48faacc75e41f7302ad0e4865be63c3bbf8f4cd810` | Bundled ELF linker for Lean native binaries |
| `bin/llvm-ar` | LLVM `22.1.4` (`35990504507d`) | 76,888 | `697c4da3ff7080716bf591ddf38d02fb093f3173e12188ddd4243304228004ad` | Bundled static archive builder |
| `bin/cadical` | CaDiCaL `rel-2.1.2` | 1,111,624 | `8e92f427cfb72072fc605ec6d5f641443c35921b29c39ab2f027776cd533afce` | Untrusted LRAT certificate generator for `bv_decide` |
| `bin/leantar` | `leantar v0.1.20` | 2,692,960 | `06d613dffd2a6fd996b095bfd835c2bb720886f9eb7e13ed2adddd7df4507bf3` | Cache archive utility |
| `lib/lean/libleanshared.so` | Lean `v4.34.1` (`5045d0056413`) | 233,708,536 | `6b30cc963d065fc9d2f87f7e9cbe0682b23000ae5425bccd769c5d477fa74f13` | Shared library containing Lean kernel, runtime, and compiler |
| `lib/lean/libleanrt.a` | Lean `v4.34.1` + `mimalloc v3.4.4` | 1,265,008 | `9188811c70520cb4f7afae5255491cc295f6a55da96589de273527d3878ac30d` | Static C++ runtime + `mimalloc` allocator |
| `lib/lean/libleancpp.a` | Lean `v4.34.1` (`5045d0056413`) | 2,381,416 | `fdcc2c28ec7fa0d2470a0329e53f1f9a699984e82497f08cdfc1cef77688bba2` | Static C++ kernel and library support |
| `lib/lean/libInit.a` | Lean `v4.34.1` (`5045d0056413`) | 26,670,980 | `3a76d35f286c27135671440c1296599a419ae7565f40a6d7135c1ea0c38e3355` | Compiled `Init` standard prelude |
| `lib/lean/libStd.a` | Lean `v4.34.1` (`5045d0056413`) | 30,830,828 | `a6c7a098aed69b9b6d7cf9eb256faf1ffb166a959736329357dc8929cff86678` | Compiled `Std` library |
| `lib/lean/libLean.a` | Lean `v4.34.1` (`5045d0056413`) | 319,363,220 | `2994f5778f3ed81f31ba7bd931ce78a2cb80b59e9c44c7649fc34fe7c7aacb94` | Compiled `Lean` metaprogramming & compiler library |
| `lib/libLLVM.so.22.1` | LLVM `22.1.4` (`35990504507d`) | 77,258,216 | `5145af96bc961289f6dff7efc0dc7f75cbc4b91634aa3b5d517749dce5f3f300` | Bundled LLVM backend for `clang` and `ld.lld` |
| `lib/libclang-cpp.so.22.1` | LLVM `22.1.4` (`35990504507d`) | 65,075,176 | `e11640dbbd29d2abebcdb62f8e90e8a965d7276df914e3cdcfd5263f427208eb` | Bundled Clang C/C++ frontend library |
| `lib/libgmp.a` | GNU MP `6.3.0` | 1,668,288 | `e104f4f49980de8dc81f407ea0a28719ddedeb1da62f27fc6404a31c4587cf8b` | Arbitrary-precision bignum arithmetic (`Nat`/`Int` $> 2^{63}-1$) |
| `lib/libuv.a` | `libuv v1.48.0` | 362,414 | `f5b243e37f7ef8087e9bc075401bf799f2ae40fa0fbc17d33d8df641e5d91c40` | Event loop, timers, and async I/O runtime |
| `lib/libcrypto.a` + `libssl.a` | OpenSSL `3.6.0` | 13,021,764 | `75c67cf5...` / `9214a7eb...` | Cryptographic primitives linked by Lake/Std |
| `lib/libc++.a` + `libc++abi.a` + `libunwind.a` | LLVM `22.1.4` (`35990504507d`) | 3,309,044 | `9c7bd16f...` / `1f759e5c...` / `4199b30b...` | Static C++ standard library, ABI, and DWARF unwinder |
| `lib/glibc/libc.so` + `libm.so` + `ld.so` | glibc `2.26` (`nixos-18.03`) | 3,613,864 | `e256592c...` / `dd9e596d...` / `cf102aa2...` | Link-time symbol version stubs (`GLIBC_2.2.5..2.26`) |
| `lib/{Scrt1,crt1,crti,crtn}.o` | glibc `2.26` (`nixos-18.03`) | 12,736 | `dc52654d...` / `1f890fce...` / `26304f66...` / `2266e876...` | Bundled ELF startup/termination objects linked by `leanc` |

### 2. Rust 1.99.1 Compiler, LLVM 23.1.1 Backend, and Bundled `rust-lld` Inventory (Layer 3)

Basis: execution ([`support/toolchain_tcb_inventory.json`](support/toolchain_tcb_inventory.json)).

| Host Toolchain Artifact (`1.99.1-x86_64-unknown-linux-gnu`) | Upstream Revision | Size (Bytes) | SHA-256 Digest | Role & Verification Status |
| :--- | :--- | ---: | :--- | :--- |
| `bin/rustc` | `rust-lang/rust` @ `58cf8f9c35b3` | 648,536 | `b53b780f77f952062f8ca8a3b70aef2390b1e45ad91939be94afdc9543026853` | Compiler CLI wrapper; loads `librustc_driver` |
| `lib/librustc_driver-7ed0375ae352bd75.so` | `rust-lang/rust` @ `58cf8f9c35b3` | 158,240,640 | `5a2cd52edba7d15f8d898b92a912638f5b73a089c7c1bfde5604ab45665602c7` | Unverified frontend (parser, macro expander, name resolver, trait/borrow checker, MIR passes) and `rustc_codegen_llvm` glue |
| `lib/libLLVM.so.23.1-rust-1.99.1-stable` | `rust-lang/llvm-project` @ `1b9c0d5ff9bb` | 208,167,760 | `1cfbe1392a767227b88b33ab6187283e281c63f80f9b1ca9010d9cee5fdf9131` | Unverified LLVM 23.1.1 middle-end optimizer, SelectionDAG/GlobalISel instruction selector, register allocator, MC assembler, and shared library for `rust-lld` |
| `lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld` | `rust-lang/llvm-project` @ `1b9c0d5ff9bb` | 11,879,600 | `9b6f51f983a8184f5d47d224e336cdb35171ad5b138981bc62a22e6d65e7b214` | Multi-flavor LLVM LLD linker (`ld.lld`, `ld64.lld`, `lld-link`, `wasm-ld`); default linker on Linux `x86_64` and `aarch64` in Rust 1.99.1 |
| `lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-ar` | `rust-lang/llvm-project` @ `1b9c0d5ff9bb` | 136,488 | `e2234a08cf6f387ecfb2d012698e828d13ffc5a78e8e37abffd38d45aa65fa9c` | Archive builder used when constructing `.rlib` and `.a` archives |
| `lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-objcopy` / `llvm-strip` | `rust-lang/llvm-project` @ `1b9c0d5ff9bb` | 296,120 | `973f626f5994c4983b23bbe68e8703d76635fa06679753f5f703f2bb829d4268` | Object stripping and section manipulation tools |
| `bin/cargo` | `rust-lang/cargo` (bundled in `58cf8f9c35b3`) | 36,148,320 | `a670e02cfa39ac2e53f77a2d911ca1fc9e2c479b0603ec956625be1daf24e3af` | Unverified build-graph resolver, feature unifier, and `build.rs` runner |

### 3. Target Assembler, Linker, CRT Startup, Unwinder, Loader, and System Libc Across All 8 Tier 1 Targets (Layer 4)

#### 3.1 Per-Target Toolchain & Runtime Link Matrix

Basis: source (`compiler/rustc_target/src/spec/targets/{x86_64_unknown_linux_gnu,aarch64_unknown_linux_gnu,i686_unknown_linux_gnu,aarch64_apple_darwin,x86_64_pc_windows_msvc,i686_pc_windows_msvc,aarch64_pc_windows_msvc,x86_64_pc_windows_gnu}.rs` and `compiler/rustc_target/src/spec/base/{linux_gnu,apple,windows_msvc,windows_gnu}.rs` at `58cf8f9c35b355199727627d07ae34a4e2846d67`).

| Tier 1 Target Triple | Object Format | Default Assembler | Default Linker in `rustc 1.99.1` | Pre-`main` / Post-`main` CRT Startup Objects | Stack Unwinder | OS Program Loader | Target System Libc / OS API |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | ELF64 (`EM_X86_64`) | Integrated `LLVM MC` (`gas` for external `.s`) | **`rust-lld`** (`ld.lld` via `cc -fuse-ld=lld`, `UseLld::Yes`) | `Scrt1.o` (PIE) / `crt1.o`, `crti.o`, `crtbeginS.o`, `crtendS.o`, `crtn.o` | `libgcc_s.so.1` (DWARF `.eh_frame` / `.eh_frame_hdr`) | `/lib64/ld-linux-x86-64.so.2` | `libc.so.6`, `libm.so.6`, `libpthread` (in `libc.so.6` $\ge$ 2.34) |
| `aarch64-unknown-linux-gnu` | ELF64 (`EM_AARCH64`) | Integrated `LLVM MC` | **`rust-lld`** (`ld.lld` via `cc -fuse-ld=lld`, `UseLld::Yes`) | `Scrt1.o` / `crt1.o`, `crti.o`, `crtbeginS.o`, `crtendS.o`, `crtn.o` | `libgcc_s.so.1` (DWARF `.eh_frame`) | `/lib/ld-linux-aarch64.so.1` | `libc.so.6`, `libm.so.6` (`GLIBC_2.17+`) |
| `i686-unknown-linux-gnu` | ELF32 (`EM_386`) | Integrated `LLVM MC` | Host `cc` driver $\to$ `ld.bfd` (`UseLld::No`) | `Scrt1.o` / `crt1.o`, `crti.o`, `crtbeginS.o`, `crtendS.o`, `crtn.o` | `libgcc_s.so.1` (DWARF `.eh_frame`) | `/lib/ld-linux.so.2` | `libc.so.6`, `libm.so.6` |
| `aarch64-apple-darwin` | Mach-O 64 (`CPU_TYPE_ARM64`) | Integrated `LLVM MC` | Host `cc` (`clang`) $\to$ Apple `ld` / `ld-prime` (`LinkerFlavor::Darwin`) | None on macOS $\ge 11.0$ (`LC_MAIN` load command in Mach-O header replaces `crt1.o`) | `libunwind.dylib` (via `libSystem.B.dylib`, Compact Unwind `__unwind_info` + DWARF) | `/usr/lib/dyld` | `libSystem.B.dylib` (`libsystem_c`, `libsystem_kernel`, `libsystem_malloc`, `libsystem_pthread`) |
| `x86_64-pc-windows-msvc` | PE32+ / COFF (`IMAGE_FILE_MACHINE_AMD64`) | Integrated `LLVM MC` | `link.exe` (`LinkerFlavor::Msvc(Lld::No)`, or `lld-link` via `-C linker-flavor=lld-link`) | `msvcrt.lib` (`mainCRTStartup` / `DllMainCRTStartup`), `vcruntime.lib`, `ucrt.lib` | Windows kernel `ntdll.dll` (`RtlVirtualUnwind` over `.pdata` / `.xdata` SEH tables + `__CxxFrameHandler3`) | `ntdll.dll` (`LdrInitializeThunk`) | `ucrtbase.dll`, `vcruntime140.dll`, `kernel32.dll`, `advapi32.dll`, `ntdll.dll`, `ws2_32.dll` |
| `aarch64-pc-windows-msvc` | PE32+ / COFF (`IMAGE_FILE_MACHINE_ARM64`) | Integrated `LLVM MC` | `link.exe` / `lld-link` | `msvcrt.lib`, `vcruntime.lib`, `ucrt.lib` | Windows ARM64 `.pdata`/`.xdata` SEH (`ntdll.dll` + `__CxxFrameHandler3`) | `ntdll.dll` | `ucrtbase.dll`, `vcruntime140.dll`, `kernel32.dll`, `ntdll.dll` |
| `i686-pc-windows-msvc` | PE32 / COFF (`IMAGE_FILE_MACHINE_I386`) | Integrated `LLVM MC` | `link.exe` / `lld-link` | `msvcrt.lib`, `vcruntime.lib`, `ucrt.lib` | Windows 32-bit stack-based SEH (`fs:[0]` exception chain + `_except_handler4` + `/SAFESEH`) | `ntdll.dll` | `ucrtbase.dll`, `vcruntime140.dll`, `kernel32.dll`, `ntdll.dll` |
| `x86_64-pc-windows-gnu` | PE32+ / COFF (`IMAGE_FILE_MACHINE_AMD64`) | Integrated `LLVM MC` | `x86_64-w64-mingw32-gcc` / `ld.bfd` | MinGW `crt2.o` (exe) / `dllcrt2.o` (dll), `crtbegin.o`, **bundled `rsbegin.o` (`324 B`)**, **bundled `rsend.o` (`324 B`)**, `crtend.o` | `libunwind` / `libgcc_eh` (SEH `.pdata`/`.xdata` via `_GCC_specific_handler`) | `ntdll.dll` | `msvcrt.dll` / `ucrtbase.dll`, `libmingwex.a`, `libmingw32.a`, `kernel32.dll`, `ntdll.dll` |

#### 3.2 Concrete Sizes and SHA-256 Digests of Pre-Compiled Target Standard Libraries (`libcore`, `liballoc`, `libcompiler_builtins`, `libstd`, `libunwind`)

Basis: execution ([`support/toolchain_tcb_inventory.json`](support/toolchain_tcb_inventory.json), [`support/verify_tcb_inventory.py`](support/verify_tcb_inventory.py)).

Unless a verified `rustc` recompiles and verifies `core`, `alloc`, `compiler_builtins`, `std`, and `unwind` from source (`-Z build-std`), every crate compiled against the delivered sysroot links pre-compiled `.rlib` machine code and reads `.rmeta` metadata from `lib/rustlib/<target>/lib/`:

| Target Triple | `libcore-*.rlib` (Bytes / SHA-256 prefix) | `liballoc-*.rlib` (Bytes / SHA-256 prefix) | `libcompiler_builtins-*.rlib` (Bytes / SHA-256 prefix) | `libstd-*.rlib` (Bytes / SHA-256 prefix) | `libunwind-*.rlib` (Bytes / SHA-256 prefix) | Total Target Dir (Files / Bytes) |
| :--- | :--- | :--- | :--- | :--- | :--- | ---: |
| `x86_64-unknown-linux-gnu` | `3,142,652` (`b346ce23...`) | `1,027,344` (`1713afb7...`) | `4,612,378` (`a98391e4...`) | `12,242,318` (`ea104615...`) | `5,354` (`cb05e3b3...`) | 319 / `1,024,526,802` |
| `aarch64-unknown-linux-gnu` | `3,279,358` (`716788fd...`) | `1,077,088` (`6bc65416...`) | `4,876,748` (`7b59f9a2...`) | `12,868,686` (`0328f033...`) | `5,426` (`25c87b0f...`) | 62 / `168,982,385` |
| `i686-unknown-linux-gnu` | `2,654,890` (`be4231fb...`) | `843,540` (`7bd397ef...`) | `3,738,266` (`2c6b02be...`) | `10,244,386` (`e71be65a...`) | `4,638` (`02e51492...`) | 55 / `142,066,703` |
| `aarch64-apple-darwin` | `2,641,088` (`0205c70e...`) | `849,720` (`36ff6b26...`) | `3,532,816` (`4aa5f1bd...`) | `9,832,968` (`74212455...`) | `5,168` (`a8e1f2f5...`) | 59 / `152,233,278` |
| `x86_64-pc-windows-msvc` | `2,489,578` (`9936159b...`) | `746,784` (`ef5df2b9...`) | `3,214,472` (`e613f49c...`) | `6,010,266` (`b16900f6...`) | `4,840` (`4001ee84...`) | 45 / `123,116,800` |
| `aarch64-pc-windows-msvc` | `2,488,066` (`e1fcd31d...`) | `742,386` (`e9fbd79a...`) | `3,060,228` (`521587c8...`) | `5,972,964` (`d15cbadc...`) | `4,854` (`257392d1...`) | 45 / `122,122,535` |
| `i686-pc-windows-msvc` | `2,552,696` (`6e0c802c...`) | `762,788` (`8e695bf2...`) | `3,393,510` (`53e797eb...`) | `6,182,648` (`466cd36d...`) | `4,838` (`74db8699...`) | 45 / `121,299,650` |
| `x86_64-pc-windows-gnu` | `2,452,788` (`3efd5bbc...`) | `814,738` (`23e05c3b...`) | `3,121,822` (`997d62d2...`) | `9,238,548` (`3f482ca1...`) | `4,460` (`fb624f07...`) | 59 / `144,536,525` |

### 4. Reference Host Operating System, System Binaries, and Hardware Identity (Layer 5)

Basis: execution ([`support/toolchain_tcb_inventory.json`](support/toolchain_tcb_inventory.json)).

| Host Component | Path / Identifier | Version / Model | Size (Bytes) | SHA-256 Digest | Role in Assumption Ledger |
| :--- | :--- | :--- | ---: | :--- | :--- |
| **Host OS Kernel** | `uname -srm` | `Linux 7.1.6-1rodete1-amd64 x86_64` | — | — | Virtual memory, process isolation, filesystem integrity (`ext4`/tmpfs), ELF loading |
| **Host Dynamic Loader** | `/lib64/ld-linux-x86-64.so.2` | Debian `GLIBC 2.43-7+gl1` | 230,200 | `247846d87e13b9d8f1fd9b56cdc166bba25ea4169d4262cc9b2b7e51ae4ab8ae` | Loads `lean`, `leanchecker`, `rustc`, and dynamically linked target binaries |
| **Host C Library** | `/lib/x86_64-linux-gnu/libc.so.6` | Debian `GLIBC 2.43-7+gl1` | 2,018,344 | `551bd390f2c49d099d68590aa3f845e268be6a993b0d89168ec6f5ddaa6362cd` | Syscall wrappers, `pthread`, and runtime support for host binaries |
| **Host Math Library** | `/lib/x86_64-linux-gnu/libm.so.6` | Debian `GLIBC 2.43-7+gl1` | 1,132,760 | `693e3e0052c2de588d72a1e8da51fdb4385f3fdb59819ff87c4dcfe8e65bb166` | Transcendental floating-point routines |
| **Host Unwinder** | `/lib/x86_64-linux-gnu/libgcc_s.so.1` | GCC 14 runtime | 182,856 | `d65ae864682cbac005bb7f2406849ea362e6b08724afdfce62dee9e1d50c2b7d` | DWARF stack unwinding on host |
| **Host Assembler** | `/usr/bin/as` (`x86_64-linux-gnu-as`) | GNU Binutils `2.46` | 819,440 | `91f681be06bc0aad7205998c2b4fb560bd8960bc549526c83e52624d8f95bf9b` | External assembler when `-C integrated-as=no` is used |
| **Host BFD Linker** | `/usr/bin/ld.bfd` (`x86_64-linux-gnu-ld.bfd`) | GNU Binutils `2.46` | 1,564,648 | `180e84c579d65c8481da525e411ef6cc238bdb0388c85d7e693bc46f1e5348bc` | Fallback system ELF linker (`i686-unknown-linux-gnu`) |
| **Host CRT Objects** | `/usr/lib/x86_64-linux-gnu/{Scrt1,crt1,crti,crtn}.o` | Debian `GLIBC 2.43-7+gl1` | 5,136 | `f76c8c1c...` / `f189a6e8...` / `cf923e87...` / `b018ccd5...` | Linked into every dynamically linked `x86_64-unknown-linux-gnu` Rust binary |
| **Host Processor** | `/proc/cpuinfo` | `Intel(R) Xeon(R) CPU @ 2.60GHz` (`GenuineIntel`, Family `6`, Model `106`, Stepping `6`, microcode `0xffffffff`) | — | — | Executes checker and compiler instructions without architectural errata corrupting state |

## Boundaries

- **Proprietary Apple and Microsoft SDK linkers/CRTs (`Not Redistribution-Bundled in Rustup Sysroot`):** While `rustup target add` installs the complete Rust `.rlib`/`.rmeta` sysroot for `aarch64-apple-darwin`, `x86_64-pc-windows-msvc`, `aarch64-pc-windows-msvc`, and `i686-pc-windows-msvc` (all 209 files and their SHA-256 digests are recorded in [`support/toolchain_tcb_inventory.json`](support/toolchain_tcb_inventory.json)), the final host/cross link step on those targets depends on Apple's Xcode Command Line Tools (`ld`, `libSystem.tbd`) or Microsoft's Visual C++ Build Tools / Windows SDK (`link.exe`, `msvcrt.lib`, `ucrt.lib`), which are governed by proprietary EULAs and are not bundled inside `rustup`.
- **Linker and CRT verification gap:** Even when a verified compiler proves source-to-machine-code refinement for individual compilation units or functions, that theorem stops at the relocatable object (`.o`) or pre-linked assembly boundary unless the linker (`rust-lld` / `ld.bfd`) and pre-`main` CRT startup objects (`Scrt1.o`, `__libc_start_main`) are also modeled or post-link validated.

## Evidence

- **Primary upstream sources:**
  - `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`: `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:1-41`, `compiler/rustc_target/src/spec/targets/aarch64_unknown_linux_gnu.rs:1-46`, `compiler/rustc_target/src/spec/targets/i686_unknown_linux_gnu.rs:1-36`, `compiler/rustc_target/src/spec/targets/aarch64_apple_darwin.rs:1-46`, `compiler/rustc_target/src/spec/targets/x86_64_pc_windows_gnu.rs:1-42`, `compiler/rustc_target/src/spec/targets/x86_64_pc_windows_msvc.rs:1-31`, `compiler/rustc_target/src/spec/base/linux_gnu.rs:1-35`, `compiler/rustc_target/src/spec/base/apple/mod.rs:1-340`, `compiler/rustc_target/src/spec/base/windows_gnu.rs:1-95`, `compiler/rustc_target/src/spec/base/windows_msvc.rs:1-60`.
  - `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`: `src/kernel/`, `src/runtime/`, `src/Lean/Compiler/`, `src/Leanc.lean`, `flake.nix`, `script/prepare-llvm-linux.sh`.
  - `joshlf/anneal` at `7abf0691c404393e3e4fc26eb3d4094e3170b5c7`: `trusted/lean/Trusted.lean`, `trusted/lean/TrustedBoundary.lean`, `trusted/audit/src/`, `trusted/cargo-anneal/src/`, `trusted/rustc-capture/src/`, `THREAT_MODEL.md`.
  - External checkers: `leanprover/lean4export` (`df81913eee5519d5a88ae5b0fd701b5298cc29ab`), `digama0/lean4lean` (`ef6be5b4cbbe993da60a27a4d5c9a71c5dd0da08`), `ammkrn/nanoda_lib` (`511c72b5f7dc4de59c2ffe3e99e3d78d8bf6bf58`).
- **Preserved inventory and verification script in `support/`:**
  - [`support/toolchain_tcb_inventory.json`](support/toolchain_tcb_inventory.json): Complete machine-readable JSON ledger containing LOC counts, byte sizes, and SHA-256 digests for Anneal `trusted/`, host OS/CRT binaries, Lean `v4.34.1` binaries and libraries, Rust `1.99.1` host binaries (`rustc`, `librustc_driver`, `libLLVM-23`, `rust-lld`), and all 8 Tier 1 target sysroots.
  - [`support/verify_tcb_inventory.py`](support/verify_tcb_inventory.py): Standalone verification script checking schema completeness and artifact coverage across all 8 Tier 1 targets and Lean `v4.34.1` binaries.

## Revalidation

Run the verification script to validate the machine-readable TCB inventory:

```bash
python3 reports/verified-rustc-delivered-toolchain-trusted-component-inventory/support/verify_tcb_inventory.py
```
