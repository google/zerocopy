# Compiler, ISA, and Platform SDK Licensing, Trademarks, and Upstream Governance

## Summary

Legal, licensing, trademark, and upstream-governance constraints across the 18
candidate compiler, ISA specification, formal-semantics, and prover codebases—as
well as platform SDK terms for Linux, macOS, and Windows—partition reuse options
for an Apache-2.0/MIT/BSD-3-Clause verified Rust compiler into three regimes:

1. **Permissively reusable code, IRs, and machine-readable ISA tables (direct
   linking, source adaptation, and mechanical translation to Lean 4 permitted
   with attribution):**
   - `rust-lang/rust` (`1.99.1`, `58cf8f9c35b355199727627d07ae34a4e2846d67`),
     including `rustc`, `cargo`, `std`, `rustc_codegen_ssa`,
     `rustc_codegen_cranelift`, and the in-tree `rustc_codegen_gcc` crate:
     **`Apache-2.0 OR MIT`** (with explicit third-party exceptions tracked in
     `REUSE.toml` and `license-metadata.json`, notably `Unicode-3.0` for
     `library/core/src/unicode/unicode_data.rs`, `Apache-2.0 WITH LLVM-exception`
     for `compiler/rustc_llvm/llvm-wrapper/`, and `OFL-1.1` for `rustdoc` fonts).
   - `llvm/llvm-project` (`23.1.1`, `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`),
     including `llvm`, `clang`, `lld`, `compiler-rt`, and all target TableGen
     (`.td`) instruction descriptions (`X86.td`, `AArch64.td`, `RISCV.td`), plus
     `bytecodealliance/wasmtime` (Cranelift / ISLE, `83166ba3`) and
     `bytecodealliance/regalloc2` (`969bad62`): **`Apache-2.0 WITH
     LLVM-exception`**.
   - Machine-readable ISA and formal semantics repositories: `rems-project/sail`
     and `rems-project/sail-arm` (`7d058164`, **`BSD-2-Clause`**), Arm's
     Machine-Readable Architecture (MRA XML/ASL, **`BSD-3-Clause`**) and ACLE
     (**`Apache-2.0 WITH LLVM-exception`** / **`BSD-3-Clause`**), Intel XED
     (`intelxed/xed`, **`Apache-2.0`**), `acl2/acl2` `books/projects/x86isa`
     (`9df88e94`, **`BSD-3-Clause`**), `rems-project/islaris` (`c978e10f`,
     **`BSD-2-Clause`**), `herd/herdtools7` (**`CeCILL-B`**, BSD-like with
     documentation attribution), `CakeML/cakeml` (`f7318949`,
     **`BSD-3-Clause`**), `AliveToolkit/alive2` (`adacbd51`, **`MIT`**), and
     `leanprover/lean4` (`v4.34.1`, `5045d005`) + `leanprover-community/mathlib4`
     (**`Apache-2.0`**).
2. **Copyleft or non-commercial restricted codebases (must NOT be linked,
   copied, or mechanically translated into a permissive compiler):**
   - `AbsInt/CompCert` (`v3.18`, `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`)
     and derivatives (`CompCert-KVX`, `CompCertO`, `CompCertSSA`): Top-level
     `LICENSE` is the **INRIA Non-Commercial License Agreement** (restricting use,
     modification, and redistribution of `backend/`, `scheduling/`, `x86/`,
     `aarch64/`, `riscv/`, and `driver/` strictly to non-commercial evaluation,
     research, and education unless commercially licensed from AbsInt). Even the
     subset of directories dual-licensed by INRIA (`lib/`, `common/`, `cfrontend/`,
     `flocq/`, `menhirLib/`, `runtime/`) is licensed under **`GPL-2.0-or-later OR
     CeCILL-C`**, both of which are copyleft. Any reuse of CompCert techniques
     must be a clean-room implementation from published academic papers.
   - `gcc` and `libgccjit` (`GPL-3.0-or-later`): Dynamically or statically linking
     `libgccjit.so` or adapting GCC C++ pass code triggers **GPLv3+** copyleft.
     Furthermore, the **GCC Runtime Library Exception v3.1** (`COPYING.RUNTIME`)
     grants permissive redistribution of target runtimes (`libgcc_s`, `libstdc++`)
     only when compiled via an *"Eligible Compilation Process"*, which explicitly
     excludes compilation pipelines that load proprietary or GPL-incompatible
     plugins or intermediate representations interacting with GCC internal data
     structures.
   - `vellvm/vellvm` (`506f1eb0`): Top-level **`BSD-3-Clause`**, but contains
     CompCert-derived library files (`lib/Coqlib.v`, `lib/Integers.v`,
     `lib/Maps.v`, `lib/Memory.v`) carrying CompCert's dual **`GPL-2.0-or-later OR
     CeCILL-C`** headers; file-level license auditing is mandatory before reusing
     any Vellvm Coq source.
3. **Platform SDK, runtime linking, and trademark boundaries:**
   - **Proprietary OS SDKs:** Apple's Xcode and macOS SDK Agreement and macOS SLA
     forbid running macOS or Xcode SDK components on non-Apple-branded hardware
     or redistributing Apple SDK headers/stubs (`*.tbd`). Microsoft's Visual
     Studio Build Tools and Windows SDK license terms restrict redistribution of
     non-`REDIST.TXT` SDK libraries (`kernel32.lib`, `ntdll.lib`, `ucrt.lib`) and
     forbid unauthenticated redistribution via third-party downloaders (`xwin`).
     Cross-compilation from Linux without click-through EULAs must target
     `*-pc-windows-gnullvm` (MinGW-w64 headers/import libs: **`ZPL-2.1` /
     Public Domain**) or consume user-supplied SDK sysroots at build time.
   - **Linux `glibc` static linking:** `glibc` (`LGPL-2.1-or-later WITH
     GCC-exception-2.0`) requires that statically linked executables (`+crt-static`
     on `*-unknown-linux-gnu`) provide relinkable object files or dynamic-linking
     capability to downstream recipients; fully static standalone Linux binaries
     without LGPL-2.1 relinking obligations require `musl` (**`MIT`**).
   - **Rust Foundation Trademark Policy:** Shipping a drop-in replacement binary
     invoked as `rustc` or `cargo` for build-system compatibility (`RUSTC=...`)
     is permitted, provided the distribution itself is branded under a distinct
     product name (following the precedents of **Ferrocene**, **`gccrs`**, and
     **`mrustc`**) and does not market itself as an official Rust Foundation
     distribution.

> *Disclaimer:* This report is an engineering reference cataloging exact upstream
> license texts, SPDX identifiers, and governance documents at pinned revisions.
> It is not legal advice; questions flagged with **`[COUNSEL REQUIRED]`** require
> formal legal review before external distribution.

## Applicability

This report governs component reuse, mechanical specification translation,
runtime library linking, cross-compilation CI provisioning, binary naming, and
upstream `rust-lang`/`llvm` coordination for a verified Rust compiler targeting
the `rustc` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) baseline.

- **Subject scope:** All 10 subject groups in `REPORT.json` are examined at their
  pinned git commits or release versions as of `2026-11-13`.
- **Target license compatibility baseline:** Compatibility is evaluated against a
  permissive open-source project license matching Anneal's tri-license
  (**`BSD-3-Clause OR Apache-2.0 OR MIT`**) or standard Rust ecosystem dual
  licensing (**`Apache-2.0 OR MIT`**), where neither copyleft reciprocity (GPL /
  LGPL / CeCILL-C) nor non-commercial field-of-use restrictions (INRIA
  Non-Commercial) are acceptable in distributed compiler binaries or Lean 4
  proof libraries.

## Findings

### 1. Component License Matrix at Pinned Revisions

`Basis: source + normative (repository LICENSE, COPYRIGHT, and REUSE.toml files)`

The table below records the exact SPDX license expression, dual-licensing splits,
and legal obligations for linking, algorithm porting, data translation into Lean 4,
and binary redistribution across all examined components. Machine-readable SHA-256
digests and metadata are preserved in `support/component_license_manifest.json`.

| Component & Pinned Revision | SPDX Identifier(s) | Linking & Redistribution Obligations | Porting Algorithms & Translating Data to Lean 4 | Counsel Flags & Trapdoors |
| :--- | :--- | :--- | :--- | :--- |
| **`rustc`, `std`, `cargo`, `rustc_codegen_ssa`, `rustc_codegen_cranelift`, `rustc_codegen_gcc`** (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`, `1.99.1`) | `Apache-2.0 OR MIT` (top-level); `REUSE.toml` overrides for specific subtrees | Permissive; preserve `COPYRIGHT`, `LICENSE-APACHE`, `LICENSE-MIT`, and `COPYRIGHT.html` / `COPYRIGHT-library.html` in binary distributions. | Full right to fork, modify, link `librustc_driver.so`, or translate MIR/type definitions into Lean 4. | Audit `REUSE.toml`: `unicode_data.rs` is `Unicode-3.0`; `llvm-wrapper/` is `Apache-2.0 WITH LLVM-exception`; `rustdoc` fonts are `OFL-1.1`. Note that linking `rustc_codegen_gcc` against `libgccjit.so` activates GPLv3+ via `libgccjit`. |
| **LLVM 23.1.1 (`llvm`, `clang`, `lld`, TableGen `.td`, `compiler-rt`)** (`llvm/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`) | `Apache-2.0 WITH LLVM-exception` (`compiler-rt` also dual-licensed `MIT OR NCSA`) | Permissive; `LLVM-exception` waives Apache-2.0 §4 binary notice requirements when `compiler-rt` or target libraries are linked into compiled outputs, and permits GPLv2 combination. | Translating `X86.td`, `AArch64.td`, `RISCV.td` TableGen files or porting LLVM passes into Lean 4 / Rust is fully permitted with attribution. | None for Apache-2.0/MIT projects. |
| **GCC 14.2 / 15 & `libgccjit`** (`gcc-mirror/gcc`) | `GPL-3.0-or-later` (compiler & `libgccjit.so`); `GPL-3.0-or-later WITH GCC-exception-3.1` (`libgcc_s`, `libstdc++`) | **Strong copyleft (`GPL-3.0-or-later`)** if linking `libgccjit.so` or GCC headers. Target `libgcc_s` linking is exempt *only* under an "Eligible Compilation Process". | Direct translation of GCC C++ passes is a GPLv3 derivative work. Studying published algorithm papers is permitted; clean-room rules apply. | **`[COUNSEL REQUIRED]`** Do not link `libgccjit` or load non-GPL plugins into GCC if claiming the GCC Runtime Library Exception v3.1. |
| **Cranelift (`cranelift-codegen`, ISLE) & `regalloc2`** (`wasmtime` @ `83166ba3`, `regalloc2` @ `969bad62`) | `Apache-2.0 WITH LLVM-exception` | Permissive; static/dynamic linking and binary redistribution require standard Apache-2.0 notice preservation. | Translating `.isle` term-rewriting rules or `regalloc2`'s `checker.rs` into Lean 4 is explicitly permitted. | None. |
| **CompCert 3.18 & derivatives (`CompCert-KVX`, `CompCertO`, `CompCertSSA`)** (`AbsInt/CompCert` @ `74cbdbf0`) | **Split license:** Top-level **INRIA Non-Commercial**; select subtrees (`lib/`, `common/`, `cfrontend/`, `flocq/`, `menhirLib/`, `runtime/`) dual-licensed `GPL-2.0-or-later OR CeCILL-C` | **Incompatible with commercial/permissive distribution.** `backend/`, `scheduling/` (KVX BTL), `x86/`, `aarch64/`, `riscv/`, and `driver/` forbid commercial use without an AbsInt license. Dual-licensed subtrees are copyleft (`GPLv2+` / `CeCILL-C`). | Mechanical or structural translation of `.v` proofs or `.ml` extractable code into Lean 4 creates a derivative work under copyright law. | **`[COUNSEL REQUIRED]`** Strict clean-room wall required: never copy or translate CompCert `.v` files; formalize from published papers (e.g., Leroy JAR 2009, Rideau & Leroy POPL 2010). |
| **CakeML (`f7318949`), Vellvm (`506f1eb0`), Alive2 (`adacbd51`)** | `BSD-3-Clause` (CakeML); `BSD-3-Clause` + CompCert-derived subset (Vellvm); `MIT` (Alive2) | CakeML and Alive2 are fully permissive (`BSD-3-Clause` / `MIT`). Vellvm's core `src/rocq/` is `BSD-3-Clause`, *except* files copied from CompCert (`Coqlib.v`, `Integers.v`, `Memory.v`). | CakeML HOL4 definitions and Alive2 C++/SMT encodings can be ported or translated into Lean 4 with BSD/MIT attribution. | Audit file headers before porting any Vellvm `.v` file; exclude CompCert-derived files (`GPL-2.0-or-later OR CeCILL-C`). |
| **Sail, `sail-arm` (`7d058164`), `sail-x86`, Arm MRA (XML/ASL), Arm ACLE** | `BSD-2-Clause` (`sail`, `sail-arm`); `BSD-3-Clause` (Arm MRA XML/ASL since 2020); `Apache-2.0 WITH LLVM-exception` / `BSD-3-Clause` (ACLE) | Permissive; preserve University of Cambridge REMS (`BSD-2-Clause`) and Arm Limited (`BSD-3-Clause`) copyright notices and disclaimers. | Mechanical translation of Arm MRA `.xml`/`.asl` or `sail-arm` `.sail` specifications into Lean 4 is permitted under `BSD-3-Clause` / `BSD-2-Clause`. | Verify the `BSD-3-Clause` `LICENSE` file in the pinned Arm A-Profile Architecture Exploration Tools archive (`ISA_A64_xml_A_profile-*`). |
| **Intel XED (`intelxed/xed`), Intel Intrinsics Guide XML, Intel SDM** | `Apache-2.0` (Intel XED); Intel Simplified / BSD-style (Clang/LLVM intrinsic headers); Proprietary Copyright (Intel SDM PDF) | Intel XED tables (`datafiles/`) and C library are `Apache-2.0`. Clang's `immintrin.h` / LLVM x86 intrinsic defs are `Apache-2.0 WITH LLVM-exception`. | Translating Intel XED `datafiles/` instruction tables into Lean 4 is permitted under `Apache-2.0`. | **`[COUNSEL REQUIRED]`** Do not bulk-scrape proprietary Intel SDM PDF prose/pseudocode; use Apache-2.0 Intel XED + BSD-3-Clause ACL2 `x86isa`. |
| **ACL2 `x86isa` (`9df88e94`), K x86-64 semantics, `herdtools7`, `Islaris` (`c978e10f`)** | `BSD-3-Clause` (`x86isa`); `NCSA` / `MIT` (K x86-64); `CeCILL-B` (`herdtools7`); `BSD-2-Clause` (`Islaris`) | All four are permissive. `CeCILL-B` (§5.3.4) requires citing the original authors/INRIA in documentation when redistributing or modifying `herdtools7` models. | Translating ACL2 `x86isa` instruction semantics, Islaris Iris rules, or `herd7` `.cat` memory models into Lean 4 is permitted with attribution. | Include explicit `CeCILL-B` attribution in documentation if shipping translated `.cat` models. |
| **Lean 4 (`v4.34.1`, `5045d005`), `mathlib4`, `rust-lang/fls` (`946eacae`)** | `Apache-2.0` (Lean 4 & `mathlib4`); `Apache-2.0 OR MIT` (FLS code/build) AND `CC-BY-4.0` (FLS specification prose) | Lean 4 and `mathlib4` are `Apache-2.0`. FLS specification text (`src/*.rst`) is `CC-BY-4.0` (requires attribution and indication of changes if redistributing specification text). | Importing Lean 4 / `mathlib4` and citing FLS paragraph IDs (`fls_*`) in Lean theorems Carry zero copyleft obligations. | If quoting or embedding substantial FLS prose in generated attestation reports, include the `CC-BY-4.0` attribution notice (`rust-lang/fls` `LICENSES/CC-BY-4.0.txt`). |

### 2. Deep-Dive: CompCert Dual-Licensing Boundary and Clean-Room Rules

`Basis: source (AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6 LICENSE and file headers)`

A common misconception is that CompCert is open-source under GPLv2+. Direct
inspection of `AbsInt/CompCert` at `v3.18`
(`74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`) shows a strict two-tier license
split:

1. **Top-level INRIA Non-Commercial Evaluation License (`LICENSE`):** Grants the
   right to use, modify, and redistribute CompCert *solely for non-commercial
   research, educational, or evaluation purposes*. Any commercial use, production
   deployment, or commercial distribution requires purchasing a commercial license
   from AbsInt Angewandte Informatik GmbH.
2. **Dual-licensed subset (`GPL-2.0-or-later OR CeCILL-C`):** Only files carrying
   the explicit header `"This file is distributed under the terms of the GNU
   General Public License as published by the Free Software Foundation, either
   version 2 of the License, or (at your option) any later version, or the
   CeCILL-C license"` are exempt from the non-commercial clause:
   - **Dual-licensed directories (`GPL-2.0-or-later OR CeCILL-C`):** `lib/`
     (`Coqlib.v`, `Maps.v`, `Integers.v`, `Floats.v`), `common/` (`AST.v`,
     `Values.v`, `Memdata.v`, `Memory.v`, `Events.v`, `Globalenvs.v`,
     `Smallstep.v`, `Behaviors.v`, `Separation.v`), `cfrontend/` (`Csyntax.v`,
     `Csem.v`, `Clight.v`, `Csharpminor.v`, `Cminor.v`), `flocq/` (`LGPL-3.0`),
     `menhirLib/` (`LGPL-3.0 WITH linking exception`), and `runtime/` (target
     runtime helpers, dual-licensed GPLv2+ / CeCILL-C).
   - **INRIA Non-Commercial ONLY directories (NOT dual-licensed):** `backend/`
     (`RTL.v`, `LTL.v`, `Linear.v`, `Mach.v`, `Selection.v`, `CSE.v`,
     `Constprop.v`, `Deadcode.v`, `Allocation.v`, `Linearize.v`, `Stacking.v`,
     `Asmgen.v`), `scheduling/` (CompCert-KVX BTL block translation validator and
     superblock scheduler), `x86/`, `aarch64/`, `arm/`, `ia32/`, `powerpc/`,
     `riscv/`, and `driver/`.

**Architectural consequence:** Neither tier is compatible with an
`Apache-2.0 OR MIT` compiler. Even the dual-licensed `common/Memory.v` and
`lib/Integers.v` files are governed by `GPL-2.0-or-later OR CeCILL-C`. Therefore,
a permissive Lean 4 verified Rust compiler must maintain a **strict clean-room
prohibition against copying or mechanically translating CompCert `.v` or `.ml`
files**. Mathematical ideas, simulation diagram structures, and memory-model
designs published in peer-reviewed papers (which are not copyrightable under 17
U.S.C. § 102(b)) may be implemented from scratch in Lean 4, or adapted from
permissively licensed projects (`CakeML` under `BSD-3-Clause`, `Alive2` under
`MIT`, `Cranelift`/`regalloc2` under `Apache-2.0 WITH LLVM-exception`, or `LLVM`
under `Apache-2.0 WITH LLVM-exception`).

### 3. Deep-Dive: Porting Algorithms vs. Translating Data Tables into Lean 4

`Basis: normative + derived (copyright derivative-work doctrine applied to repository licenses)`

1. **Translating declarative ISA and instruction tables into Lean 4:**
   - **LLVM TableGen (`X86.td`, `AArch64.td`, `RISCV.td`):** Governed by
     `Apache-2.0 WITH LLVM-exception`. Writing a generator that parses LLVM
     TableGen JSON dumps (`llvm-tblgen --dump-json`) and emits Lean 4 inductive
     types and encoding/decoding tables is an authorized derivative work under
     Apache-2.0 §2, requiring only retention of the LLVM attribution notice.
   - **Arm MRA (XML/ASL) and `rems-project/sail-arm`:** Arm Limited released the
     A-Profile Machine-Readable Architecture specification under `BSD-3-Clause`,
     and `sail-arm` (`7d0581642d0e3aaca367bbc5650aca7c53057543`) is
     `BSD-2-Clause`. Generating Lean 4 definitions from `sail-arm` or Arm XML/ASL
     requires preserving the Arm and Cambridge REMS copyright headers and
     disclaimers in the generated files and distribution documentation.
   - **Intel XED (`intelxed/xed`) vs. Intel SDM PDF:** Intel XED's machine-readable
     `datafiles/` describing x86-64 opcodes, ModRM/SIB rules, EVEX/VEX prefixes,
     and flag effects are licensed under `Apache-2.0`, and ACL2 `x86isa`
     (`9df88e94`) is `BSD-3-Clause`. By contrast, the Intel 64 and IA-32
     Architectures Software Developer's Manual (SDM) PDF carries a proprietary
     Intel copyright notice without an open-source license. Mechanically scraping
     SDM pseudocode blocks into Lean 4 raises copyright questions **`[COUNSEL
     REQUIRED]`**, whereas deriving x86-64 Lean 4 semantics from **Intel XED
     (`Apache-2.0`) + LLVM `X86.td` (`Apache-2.0 WITH LLVM-exception`) + ACL2
     `x86isa` (`BSD-3-Clause`)** is entirely covered by permissive open-source
     licenses.
2. **GCC Runtime Library Exception v3.1 (`COPYING.RUNTIME`) and `libgcc_s`:**
   - Target binaries on `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`
     dynamically link `libgcc_s.so.1` for stack unwinding (`_Unwind_RaiseException`,
     `_Unwind_Resume`). Under `COPYING.RUNTIME` §0–§1, linking `libgcc_s` into
     target code is unrestricted *unless* the target code was produced by a
     GCC-based compilation process that used GPL-incompatible plugins or passes.
     A standalone verified compiler that does *not* invoke GCC or `libgccjit`—or
     that links LLVM's `libunwind` / `compiler-rt` (`Apache-2.0 WITH
     LLVM-exception`)—avoids the GCC "Eligible Compilation Process" restriction.
   - However, if a compiler links `libgcc_s` statically or dynamically, downstream
     users who desire zero GPL/LGPL runtime files in their target image can select
     LLVM `compiler-rt` + `llvm-libunwind` (`Apache-2.0 WITH LLVM-exception`).

### 4. Platform SDK Terms, Cross-Compilation, and Runtime Linking

`Basis: normative + documentation (platform SDK license agreements and LGPL-2.1 / ZPL-2.1 terms)`

| Platform / Runtime | Governing License / Agreement | Host & Virtualization Constraints | Redistribution & Cross-Compilation Implications |
| :--- | :--- | :--- | :--- |
| **Apple Xcode & macOS SDK (`MacOSX.sdk`, `libSystem.tbd`)** | Apple Xcode and Apple SDKs Agreement + macOS Software License Agreement (SLA) | macOS SLA §2.B.iii permits running up to two additional copies or instances of macOS within virtualized environments **solely on Apple-branded hardware** that is already running macOS. Running macOS or Xcode in Linux/KVM containers on non-Apple hardware violates the SLA. | Redistributing Apple SDK headers or `.tbd` stub libraries (`libSystem.B.tbd`) outside Xcode is prohibited. Cross-compiling to `aarch64-apple-darwin` or `x86_64-apple-darwin` from Linux requires either (a) the end user supplying their own lawfully obtained `MacOSX.sdk` path (`-C link-arg=-sysroot=...`), or (b) running macOS CI jobs on Apple-branded builders. |
| **Microsoft Visual Studio Build Tools, MSVC (`vcruntime`), & Windows SDK (`kernel32.lib`, `ntdll.lib`, `ucrt.lib`)** | Microsoft Visual Studio Build Tools License Terms & Windows SDK License Agreement | Build Tools license grants rights to install and run the tools to design, develop, and test programs; automated downloading and repackaging of `.lib`/`.h` files via third-party tools (`xwin --accept-license`) bypasses Microsoft's click-through license acceptance and is prohibited without explicit authorization. | Only files listed in Microsoft's `REDIST.TXT` (`vcruntime140.dll`, `msvcp140.dll`) may be redistributed in binary form by licensees; static import libraries (`kernel32.lib`, `ntdll.lib`, `msvcrt.lib`) are **not** generally redistributable as standalone SDK bundles **`[COUNSEL REQUIRED]`**. |
| **MinGW-w64 (`*-pc-windows-gnu` / `*-pc-windows-gnullvm`)** | **`ZPL-2.1`** (Zope Public License 2.1) for `mingw-w64-crt` and headers; Public Domain / MIT-style additions | Zero host restrictions; runs natively on Linux cross-compilation hosts via `lld-link` or `ld.lld`. | Fully permissive open-source (`ZPL-2.1`). `rustup` distributes MinGW-w64 import libraries (`libkernel32.a`, `libntdll.a`, `libmsvcrt.a`) inside the `rust-std-*-pc-windows-gnu` and `*-pc-windows-gnullvm` components (`compiler/rustc_target/src/spec/targets/x86_64_pc_windows_gnullvm.rs`), enabling 100% EULA-free Windows PE32+ cross-compilation and `lld` linking on Linux! |
| **GNU C Library (`glibc`, `*-unknown-linux-gnu`)** | **`LGPL-2.1-or-later WITH GCC-exception-2.0`** | Unrestricted on Linux hosts. | Dynamic linking (`libc.so.6`) imposes no copyleft obligations on the compiled Rust binary (LGPL-2.1 §5). However, **static linking (`-C target-feature=+crt-static` against `libc.a`)** triggers LGPL-2.1 §6, requiring the distributor of the static binary to provide object files or relinking scripts so recipients can relink against a modified `glibc`. |
| **musl libc (`*-unknown-linux-musl`)** | **`MIT`** | Unrestricted on Linux hosts. | Fully permissive; static linking (`+crt-static`) produces standalone ELF executables with zero LGPL-2.1 relinking obligations. |

### 5. Rust Foundation Trademark Policy and Precedents

`Basis: normative + documentation (Rust Foundation Trademark Policy and Ferrocene / gccrs / mrustc naming precedents)`

The Rust Foundation owns the registered word marks **"Rust"** and **"Cargo"** and
the Rust gear logo:

1. **Product naming and branding rule:** Under the Rust Foundation Trademark
   Policy, an alternative compiler, custom fork, or verified toolchain
   distribution **must not** use `"Rust"` or `"Cargo"` as the primary product
   brand in a manner that implies official endorsement by or affiliation with the
   Rust Project or the Rust Foundation (for example, naming a commercial or
   standalone product *"Verified Rust"* or *"Official Safe Rust Compiler"*).
   Nominative fair use—stating truthfully in documentation that the compiler
   *"compiles the Rust programming language"* or *"is compatible with `rustc`
   1.99.1"*—is expressly permitted.
2. **Executable binary names (`rustc`, `cargo`) for drop-in CLI compatibility:**
   Build tools (`cargo`, `bazel`, `buck2`, `cmake`, `meson`) invoke the compiler
   either via `RUSTC=/path/to/binary` or by resolving a binary named `rustc` on
   `PATH`. Precedents across the ecosystem establish the standard compliance
   pattern:
   - **Ferrocene (Ferrous Systems / Critical Section GmbH):** Brands the qualified
     product as **Ferrocene** (with the CLI wrapper `criticalup`), while shipping
     the underlying drop-in compiler executable as `rustc` (and `cargo`) inside
     the managed toolchain sysroot so existing Cargo workspaces build unmodified,
     accompanied by explicit trademark attribution (`"Rust and Cargo are
     trademarks of the Rust Foundation"`).
   - **`rustc_codegen_cranelift` and `rustc_codegen_gcc`:** Ship as codegen backend
     plugins loaded via `-Zcodegen-backend=cranelift` or `-Zcodegen-backend=gcc`
     by `rustc` itself.
   - **`gccrs` and `mrustc`:** Use distinct project identifiers (`gccrs`,
     `mrustc`) while providing drop-in wrapper flags where needed.
   - **`[COUNSEL REQUIRED]`** Before publishing binary releases that include an
     executable named `rustc` outside an upstream `rustup` toolchain, confirm the
     exact trademark disclaimer wording with legal counsel under the current Rust
     Foundation Trademark Policy.

### 6. Upstream Coordination, Security Disclosure, and RFC / MCP Governance

`Basis: source + documentation (rust-lang/rfcs@7677feddd580f356f780cb7123aeda6a3708275a and rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67)`

1. **Vulnerability and soundness bug disclosure norms:**
   - **`rust-lang/rust`:** Security vulnerabilities (such as miscompilations in
     stable `rustc` reachable from safe code that violate memory safety or CVEs in
     `cargo`/`std`) are reported privately to `security@rust-lang.org` (or via the
     GitHub Security Advisory portal on `rust-lang/rust`) under embargo. Ordinary
     soundness bugs (`I-unsound` label, such as long-standing trait solver or
     lifetime edge cases already tracked publicly) are filed on the public tracker
     with a minimal, self-contained reproducer.
   - **`llvm/llvm-project`:** Security issues are reported via the LLVM Security
     Group (`security@llvm.org` / GitHub private vulnerability reporting); regular
     miscompilation bugs are filed as reduced LLVM IR (`opt` / `llc` reproducers,
     often minimized with `llvm-reduce` and validated with `Alive2`) on
     `github.com/llvm/llvm-project/issues`.
   - **GCC:** Bugs are reported on `gcc.gnu.org/bugzilla/` with preprocessed source
     (`-freport-bug`) and exact target flags; security issues go to
     `security@gcc.gnu.org`.
2. **Upstream change governance (`rust-lang/rfcs` at `7677fedd`):**
   - **Compiler Major Change Proposal (MCP):** Changes internal to `compiler/*`—
     such as extending `rustc_codegen_ssa::traits::BackendTypes`, adding a stable
     serialization hook for post-cleanup MIR (`Runtime(PostCleanup)`), or exposing
     additional layout/ABI invariants to `-Zcodegen-backend`—do **not** require a
     full RFC; they use the **Compiler Team MCP** process (a lightweight tracking
     issue on `rust-lang/compiler-team` approved via `@rfcbot fcp merge` or seconding
     by a `T-compiler` member).
   - **Full RFC (`rust-lang/rfcs`):** Required for user-visible language changes
     (`T-lang`), standard library API additions (`T-libs-api`), Cargo manifest or
     `.rlib`/crate format changes affecting the broader ecosystem (`T-cargo`), or
     adding/promoting a target tier (`text/3866-target-tier-policy-2.md` in
     `rust-lang/rfcs` at `7677feddd580f356f780cb7123aeda6a3708275a`).
   - **How `rustc_codegen_cranelift` and `rustc_codegen_gcc` coordinate upstream:**
     Both backends live directly inside the `rust-lang/rust` monorepo at
     `compiler/rustc_codegen_cranelift` and `compiler/rustc_codegen_gcc` and are
     gated in `src/bootstrap/` (`bootstrap.example.toml` `codegen-backends =
     ["llvm", "cranelift", "gcc"]`). Because they build in-tree on `rust-lang/rust`
     CI, any PR that changes `rustc_middle::ty`, `rustc_middle::mir`, or
     `rustc_codegen_ssa` is required by `bors` CI to update both backends in lockstep.

## Boundaries

- **Not legal advice (`unknown` without formal counsel review):** While SPDX
  identifiers, file hashes, and license texts are established facts, conclusions
  regarding clean-room sufficiency for algorithm porting, redistributability of
  static Windows SDK import libraries, and nominative trademark usage carry
  **`[COUNSEL REQUIRED]`** flags that only qualified legal counsel can formally
  clear.
- **Unexamined proprietary EULAs (`not examined` via click-through):** In
  compliance with repository guardrails, neither the Apple Xcode SLA nor the
  Microsoft Visual Studio / Windows SDK click-through installer EULAs were
  accepted or executed on this host; Windows cross-compilation findings rely on
  the permissive `*-pc-windows-gnullvm` (`ZPL-2.1` MinGW-w64) target already
  bundled in `rustup`.
- **Out-of-tree Cargo crate transitive licenses (`not examined` exhaustively):**
  Only the licenses of `rust-lang/rust` in-tree components (`REUSE.toml` and
  `COPYRIGHT`) and the 18 named compiler/ISA/verification repositories were
  audited; third-party crates fetched from `crates.io` by user workspaces must be
  audited separately (for example, via `cargo deny check licenses`).

## Evidence

1. **Rust `1.99.1` licensing and `REUSE.toml` annotations:**
   - Repository: `rust-lang/rust` at `58cf8f9c35b355199727627d07ae34a4e2846d67`
   - Files: `COPYRIGHT` (lines 1–34, SHA-256
     `172020dbfd5b53a226dfde77616190a48dcff519b0bc0e6deb91a8450782c4af`),
     `LICENSE-APACHE` (SHA-256
     `62c7a1e35f56406896d7aa7ca52d0cc0d272ac022b5d2796e7d6905db8a3636a`),
     `LICENSE-MIT` (SHA-256
     `b71bd43a069ca0641a9ecfe585ca7b3c53b5cc1608f8b68321168698e28b5ea1`), and
     `REUSE.toml` (lines 1–210, specifying `MIT OR Apache-2.0` default override
     plus `Apache-2.0 WITH LLVM-exception`, `Unicode-3.0`, `BSD-2-Clause`, and
     `OFL-1.1` subtree exceptions).
2. **Ferrocene Language Specification (`rust-lang/fls`) dual code/prose licensing:**
   - Repository: `rust-lang/fls` at `946eacae5a4a33a89af7832178504692439e7478`
   - Files: `LICENSES/Apache-2.0.txt` (SHA-256
     `074e6e32c86a4c0ef8b3ed25b721ca23aca83df277cd88106ef7177c354615ff`),
     `LICENSES/MIT.txt` (SHA-256
     `b85dcd3e453d05982552c52b5fc9e0bdd6d23c6f8e844b984a88af32570b0cc0`), and
     `LICENSES/CC-BY-4.0.txt` (SHA-256
     `d1a05b85d9371739ab03732814066b4668a01429fb56c4eaa9f5a343ef52a226`).
3. **Normative Rust Reference, MiniRust, and RFC repositories:**
   - `rust-lang/reference` at `bcd62f35e8bf480ec5b0fa569b6d12ea5924030c`
     (`LICENSE-MIT`, SHA-256
     `0621878e61f0d0fda054bcbe02df75192c28bde1ecc8289cbd86aeba2dd72720`).
   - `minirust/minirust` at `063d784186d3252bee242217f218223205c0b568`
     (`LICENSE-MIT`, SHA-256
     `23f18e03dc49df91622fe2a76176497404e46ced8a715d9d2b67a7446571cca3`).
   - `rust-lang/rfcs` at `7677feddd580f356f780cb7123aeda6a3708275a`
     (`text/3866-target-tier-policy-2.md`).
4. **Support artifacts preserved in this package:**
   - `support/component_license_manifest.json`: Structured license matrix and
     SHA-256 file digests across all 10 component groups.
   - `support/verify_licensing_manifest.py`: Revalidation script verifying the
     manifest schema and SHA-256 digests.

## Revalidation

1. **Verify the preserved license manifest and file digests:**
   ```bash
   python3 reports/compiler-isa-sdk-licensing-trademarks-and-upstream-governance/support/verify_licensing_manifest.py \
     --manifest reports/compiler-isa-sdk-licensing-trademarks-and-upstream-governance/support/component_license_manifest.json
   ```
2. **Re-check `rust-lang/rust` in-tree license overrides on a newer `rustc` tag:**
   Diff `COPYRIGHT`, `REUSE.toml`, and `license-metadata.json` between
   `58cf8f9c35b355199727627d07ae34a4e2846d67` (`1.99.1`) and the target release:
   ```bash
   git -C <rust-checkout> diff 58cf8f9c35b355199727627d07ae34a4e2846d67..<new-rev> -- COPYRIGHT REUSE.toml
   ```
   Confirm that no GPL, LGPL, or non-commercial annotation has been added to
   `compiler/**` or `library/**`.
