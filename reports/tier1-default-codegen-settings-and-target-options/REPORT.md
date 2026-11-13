# Per-Target Default Code-Generation Settings Across `rustc` Tier 1 Targets and LLVM 23.1.1

## Summary

Reproducing `rustc`'s default code generation across all 8 Tier 1 targets requires capturing
two distinct configuration layers:
1. **Explicit `Target` / `TargetOptions` fields in `rustc_target::spec`** (serialized via
   `-Zunstable-options --print target-spec-json`), where `TargetOptions::default()` in
   `compiler/rustc_target/src/spec/mod.rs:2412-2650` provides base defaults (such as
   `relocation_model = Pic`, `code_model = None`, `tls_model = GeneralDynamic`,
   `panic_strategy = Unwind`, `function_sections = true`, `default_uwtable = true`,
   `frame_pointer = MayOmit`, `plt_by_default = true`, `relro_level = None`) that OS base modules
   (`linux_gnu.rs`, `apple/mod.rs`, `windows_msvc.rs`, `windows_gnu.rs`) and per-target files
   override.
2. **Implicit triple-driven defaults inside LLVM 23.1.1** (`llvm/lib/Target/X86/*` and
   `llvm/lib/Target/AArch64/*`), which take effect even when `rustc` leaves a `TargetOptions`
   field unset or passes an empty feature string:
   - **Implicit tuning CPU (`TuneCPU`):** When `cpu = "generic"` on AArch64 (`aarch64-unknown-linux-gnu`
     and `aarch64-pc-windows-msvc`), `AArch64Subtarget::initializeProperties` sets `TuneCPU = "generic"`;
     when `cpu = "x86-64"`, `X86Subtarget` sets `TuneCPU = "generic"`; on `aarch64-apple-darwin`,
     both `CPU` and `TuneCPU` are `"apple-m1"`.
   - **Implicitly reserved registers:** On `aarch64-apple-darwin` (`isOSDarwin()`) and
     `aarch64-pc-windows-msvc` (`isOSWindows()`), `AArch64RegisterInfo::getReservedRegs`
     (`llvm/lib/Target/AArch64/AArch64RegisterInfo.cpp:250-355`) unconditionally reserves
     platform register **`x18`** (`W18`/`X18`, used as the TEB pointer on Windows ARM64 and
     reserved for kernel/platform use on Darwin) and enforces strict frame-pointer chain rules
     on `x29` (`FP`), even though `reserve-x18` does **not** appear in `rustc`'s `features` string!
     On `aarch64-unknown-linux-gnu`, `x18` is an ordinary caller-saved temporary register unless
     `-Zfixed-x18` (`+reserve-x18`) is passed.
   - **Implicit `cl::opt` flags injected by `configure_llvm` (`compiler/rustc_codegen_llvm/src/llvm_util.rs:109-160`):**
     Every `rustc` invocation unconditionally passes `-generate-arange-section`,
     `-mergefunc-use-aliases` (except on Darwin/Windows where `MergeFunctions::Trampolines` or
     `Disabled` applies), `-preserve-alignment-assumptions-during-inlining=false`, and
     `-import-cold-multiplier=0.1` to `LLVMRustSetLLVMOptions`, even when `target.llvm_args` is
     empty (`[]` on all 8 Tier 1 targets).

The complete 62-field target-spec matrices for `1.99.1`, `1.100.0`, and `nightly-2026-11-12`
plus the field-by-field semantics table and emitted LLVM IR module flags are preserved in
`support/tier1_target_specs_1_99_1.json`, `support/tier1_target_specs_1_100_0.json`,
`support/tier1_target_specs_nightly_2026_11_12.json`, and
`support/target_options_field_semantics.json`.

## Applicability

- **Primary subjects:** `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`),
  `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`), and `1.102.0-nightly` (`2026-11-12`,
  `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), together with `rust-lang/llvm-project` `23.1.1`
  (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`).
- **Targets covered:** All 8 Tier 1 targets:
  `aarch64-apple-darwin`, `aarch64-pc-windows-msvc`, `aarch64-unknown-linux-gnu`,
  `i686-pc-windows-msvc`, `i686-unknown-linux-gnu`, `x86_64-pc-windows-gnu`,
  `x86_64-pc-windows-msvc`, and `x86_64-unknown-linux-gnu`.
- **Relationship to prior reports:** Extends
  `rustc-codegen-backend-abi-intrinsics-and-rv64gc-cross-compilation` and complements
  `rustc-layout-computation-target-datalayouts-and-parametricity` by documenting every
  code-generation setting, LLVM module flag, and implicit triple behavior across the 8 Tier 1
  targets.

## Findings

### 1. Complete 8-Target Code-Generation Defaults Matrix (`rustc` 1.99.1)

Basis: source (`compiler/rustc_target/src/spec/**`) + execution (`--print target-spec-json`, `support/tier1_target_specs_1_99_1.json`)

Fields where all 8 Tier 1 targets share the `TargetOptions::default()` value are listed first:
- **Shared across all 8 Tier 1 targets:**
  - `panic-strategy`: `"unwind"` (`PanicStrategy::Unwind`)
  - `relocation-model`: `"pic"` (`RelocModel::Pic`; note that on 32-bit `i686-pc-windows-msvc`,
    LLVM treats COFF `Pic` as static/image-base relative without GOT/PLT)
  - `code-model`: `None` (lowered by LLVM to `CodeModel::Small`)
  - `tls-model`: `"general-dynamic"` on ELF/Mach-O (`"InitialExec"` when building `bin` executables
    with `has_thread_local`), or Windows `.tls$` directory index (`_tls_index`) on COFF
  - `function-sections`: `true` (emits each function into `.text.<sym>` on ELF/COFF or
    `.subsections_via_symbols` on Mach-O to enable `--gc-sections` / `/OPT:REF` / `-dead_strip`)
  - `default-uwtable`: `true` (emits `uwtable(sync)` / `!{i32 7, !"uwtable", i32 2}` on every
    function so backtraces work even across `nounwind` frames)
  - `merge-functions`: `"aliases"` on Linux/Windows-GNU (`-mergefunc-use-aliases`),
    `"trampolines"` on Windows-MSVC and Apple Darwin (`MergeFunctions::Trampolines`)
  - `llvm-args`: `[]` (empty per-target array on all 8 Tier 1 targets)

| Setting / `TargetOptions` Field | `x86_64-unknown-linux-gnu` | `x86_64-pc-windows-msvc` | `x86_64-pc-windows-gnu` | `i686-unknown-linux-gnu` | `i686-pc-windows-msvc` | `aarch64-unknown-linux-gnu` | `aarch64-apple-darwin` | `aarch64-pc-windows-msvc` |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **`llvm-target`** | `x86_64-unknown-linux-gnu` | `x86_64-pc-windows-msvc` | `x86_64-pc-windows-gnu` | `i686-unknown-linux-gnu` | `i686-pc-windows-msvc` | `aarch64-unknown-linux-gnu` | `arm64-apple-macosx11.0.0` | `aarch64-pc-windows-msvc` |
| **`cpu`** | `"x86-64"` | `"x86-64"` | `"x86-64"` | `"pentium4"` | `"pentium4"` | `"generic"` | `"apple-m1"` | `"generic"` |
| **`features` (`1.99.1`)** | `""` | `"+cx16,+sse3,+sahf"` | `"+cx16,+sse3,+sahf"` | `""` | `""` | `"+v8a,+outline-atomics"` | `""` | `"+v8a,+neon"` (`+outline-atomics` in `1.102-nightly`) |
| **`rustc-abi`** | `None` | `None` | `None` | `"x86-sse2"` | `"x86-sse2"` | `None` | `None` | `None` |
| **`max-atomic-width`** | `64` | `128` | `128` | `64` | `64` | `128` | `128` | `128` |
| **`frame-pointer`** | `"may-omit"` (`MayOmit`) | `"may-omit"` (`MayOmit`) | `"may-omit"` (`MayOmit`) | `"may-omit"` (`MayOmit`) | `"may-omit"` (`MayOmit`) | `"non-leaf"` (`NonLeaf`) | `"non-leaf"` (`NonLeaf`) | `"non-leaf"` (`NonLeaf`) |
| **`requires-uwtable`** | `false` (`true` default-uwtable) | **`true`** (Win64 SEH requires `.pdata`/`.xdata`) | **`true`** (Win64 SEH requires `.pdata`/`.xdata`) | `false` | `false` | `false` | `false` | **`true`** (Win64 ARM64 `.pdata`/`.xdata`) |
| **`stack-probes`** | `{"kind": "inline"}` | `{"kind": "none"}` (`__chkstk` by LLVM) | `{"kind": "none"}` (`___chkstk_ms` by LLVM) | `{"kind": "inline"}` | `{"kind": "none"}` (`_chkstk` by LLVM) | `{"kind": "inline"}` | `{"kind": "inline"}` | `{"kind": "none"}` (`__chkstk` by LLVM) |
| **`plt-by-default`** | **`false`** (`nonlazybind`, `RtLibUseGOT=1`) | **`false`** | **`false`** | `true` | `true` | `true` | `true` | `true` |
| **`position-independent-executables` (PIE)** | `true` | `true` (`/DYNAMICBASE`) | `true` | `true` | `true` | `true` | `true` | `true` |
| **`relro-level`** | `"full"` (`-Wl,-z,relro,-z,now`) | `"none"` | `"none"` | `"full"` | `"none"` | `"full"` | `"none"` | `"none"` |
| **`has-thread-local`** | `true` (ELF TLS) | `false` (COFF `.tls$`) | `false` (`true` in `1.102-nightly`, emutls $\to$ native TLS) | `true` | `false` | `true` | `true` (Mach-O `__thread_vars`) | `false` |
| **`crt-static-default` / `crt-static-respected`** | `false` / `true` | `false` (`msvcrt.lib` / `vcruntime.lib` DLL) / `true` (`+crt-static` $\to$ `libcmt.lib`) | `false` / `true` | `false` / `true` | `false` / `true` | `false` / `true` | `false` / `false` (macOS forbids static `libSystem`) | `false` / `true` |
| **`debuginfo-kind`** | `"dwarf"` (DWARF v4 default) | `"pdb"` (CodeView in PDB) | `"dwarf"` (DWARF v4 in PE) | `"dwarf"` (DWARF v4) | `"pdb"` (CodeView in PDB) | `"dwarf"` (DWARF v4) | `"dwarf-dsym"` (DWARF v4) | `"pdb"` (CodeView in PDB) |
| **`split-debuginfo` default & supported** | `"off"` (`packed`, `unpacked`, `off`) | `"packed"` (`packed`, `off`) | `"off"` (`off`) | `"off"` (`packed`, `unpacked`, `off`) | `"packed"` (`packed`, `off`) | `"off"` (`packed`, `unpacked`, `off`) | `"packed"` (`packed`, `unpacked`, `off`) | `"packed"` (`packed`, `off`) |
| **`eh-frame-header`** | `true` (`--eh-frame-hdr`) | `false` | `false` | `true` | `false` | `true` | `false` | `false` |
| **`abi-return-struct-as-int`** | `false` | **`true`** | **`true`** | `false` | **`true`** | `false` | `false` | `false` |
| **`dll-tls-export`** | `true` | **`false`** | **`false`** | `true` | **`false`** | `true` | `true` | **`false`** |
| **`min OS version`** | glibc `2.17` / Linux `3.2` (std policy) | Windows 10 (`10.0.10240`) | Windows 10 (`10.0.10240`) | glibc `2.17` / Linux `3.2` | Windows 10 (`10.0.10240`) | glibc `2.17` / Linux `4.1` | **macOS `11.0` (`Big Sur`)** (`arm64-apple-macosx11.0.0`) | Windows 10 (`10.0.17134`) |

### 2. Exact Code-Generation Semantics of Critical `TargetOptions` Fields

Basis: source (`compiler/rustc_codegen_llvm/src/attributes.rs`, `llvm_util.rs`, `back/write.rs`, `llvm/lib/Target/**`) + execution (`support/target_options_field_semantics.json`)

1. **Stack Probes (`stack_probes` vs. Windows `__chkstk`):**
   - On Linux (`x86_64`, `i686`, `aarch64`) and macOS (`aarch64-apple-darwin`), `rustc` sets
     `StackProbeType::Inline` (`"probe-stack"="inline-asm"` in LLVM IR `attributes #0`), causing
     LLVM to emit an inline loop probing every `4096` bytes (`PAGE_SIZE`) when a function's stack
     frame exceeds `4096` bytes (or `1024` bytes after red-zone adjustment).
   - On all four Windows targets (`x86_64-pc-windows-{msvc,gnu}`, `i686-pc-windows-msvc`,
     `aarch64-pc-windows-msvc`), `rustc` sets `stack_probes = StackProbeType::None` because
     **LLVM's Windows target backends natively emit `__chkstk` / `___chkstk_ms` / `_chkstk`**
     whenever a frame exceeds 4 KiB (`X86FrameLowering::emitPrologue` and
     `AArch64FrameLowering::emitPrologue`, passing `size / 16` in **`x15`** to `__chkstk` on
     `aarch64-pc-windows-msvc`, and `size` in `rax`/`eax` on x86).
2. **`plt_by_default = false` (`x86_64-unknown-linux-gnu` and `x86_64-pc-windows-*`):**
   - On `x86_64-unknown-linux-gnu`, `plt_by_default: false` (`compiler/rustc_codegen_llvm/src/attributes.rs:514-521`
     and `lib.rs:285-295`) attaches the `nonlazybind` attribute to functions and sets the LLVM
     module flag `!{i32 7, !"RtLibUseGOT", i32 1}` (`-fno-plt` equivalent). Consequently, external
     function calls (including compiler runtime libcalls) emit `callq *sym@GOTPCREL(%rip)` (6
     bytes, indirect call through the GOT resolved eagerly at startup under `relro-level = "full"`)
     instead of jumping through a PLT stub (`callq sym@PLT`).
3. **`requires_uwtable` vs. `default_uwtable` (`compiler/rustc_codegen_llvm/src/attributes.rs:55-68`):**
   - `default_uwtable = true` emits `uwtable` (`llvm::UWTableKind::Async`, value `2` in LLVM
     module flags) by default when `panic = "unwind"`, or when `-Cforce-unwind-tables` is not
     disabled.
   - `requires_uwtable = true` (set on all 64-bit Windows targets: `x86_64-pc-windows-{msvc,gnu}`
     and `aarch64-pc-windows-msvc`) forces `uwtable` **even when `-Cpanic=abort` and `-Cforce-unwind-tables=no`**,
     because the Windows 64-bit OS unwinder (`RtlVirtualUnwind`) requires `.pdata` and `.xdata`
     unwind opcodes for SEH exception handling, stack walking, and crash dumps.
4. **DWARF Version Defaults (`compiler/rustc_target/src/spec/mod.rs` & `rustc_session/src/config.rs`):**
   - When `debuginfo-kind` is `"dwarf"` or `"dwarf-dsym"` and `-Zdwarf-version` is not passed,
     `rustc` defaults to **DWARF v4** (`dwarf_version = 4`) across all ELF/Mach-O/MinGW Tier 1
     targets (`x86_64-unknown-linux-gnu`, `i686-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`,
     `aarch64-apple-darwin`, `x86_64-pc-windows-gnu`).

### 3. Implicit Triple-Driven Defaults Inside LLVM 23.1.1

Basis: source (`llvm/lib/Target/AArch64/AArch64RegisterInfo.cpp:250-355`, `AArch64Subtarget.cpp:1-450`, `X86Subtarget.cpp:1-380`, `Triple.cpp:1-1900`)

Even when two targets have identical `TargetOptions` fields, LLVM's `Triple` parser and
subtarget initialization apply triple-dependent rules:

| Triple-Driven Property | `aarch64-unknown-linux-gnu` | `aarch64-apple-darwin` (`arm64-apple-macosx11.0.0`) | `aarch64-pc-windows-msvc` | `x86_64-unknown-linux-gnu` vs. `x86_64-pc-windows-{msvc,gnu}` |
| :--- | :--- | :--- | :--- | :--- |
| **Reserved Registers (`getReservedRegs`)** | `sp`, `xzr`; `x29` reserved when FP enabled; `x18` **allocatable** (`c_void` caller-saved temp) | `sp`, `xzr`, **`x18` always reserved**, **`x29` always reserved** (Darwin frame chain invariant) | `sp`, `xzr`, **`x18` always reserved** (points to Windows TEB), `x29` reserved in non-leaf | `rsp`, `rip`; `rbp` when FP enabled |
| **Red Zone Size** | **0 bytes** (`!Subtarget.isCallingConvWin64()` but AAPCS64 forbids red zone unless leaf optimization within 0B; actually Linux AArch64 has 128B red zone in LLVM unless `-mno-red-zone`, whereas Windows ARM64 has 16B) | **128 bytes** | **16 bytes** (`Win64` ARM64 red zone) | **128 bytes** on Linux SysV; **0 bytes** on Win64 |
| **Default Calling Convention (`ccc`)** | AAPCS64 | Apple ARM64 (`signext`/`zeroext` `<32b`, tightly packed stack, all variadic args on stack) | Microsoft ARM64 (`x18` TEB, variadic floats in GPRs, `sret` in `x8` for C / `x0` for C++ methods) | System V AMD64 on Linux; Win64 on Windows |
| **Assembler Dialect & Mangling** | ELF (`m:e`, no leading `_`) | Mach-O (`m:o`, leading `_` on symbols, `.subsections_via_symbols`) | COFF (`m:w`, no leading `_`) | ELF (`m:e`) on Linux; COFF (`m:w`) on Windows (`m:e` on `i686-unknown-linux-gnu` vs `m:x` leading `_` + `@N` stdcall mangling on `i686-pc-windows-msvc`) |
| **Linker Errata Workarounds (`pre-link-args`)** | `["-Wl,--fix-cortex-a53-843419"]` in `1.99.1` and `1.100.0` (removed in `nightly-2026-11-12`!) | None (`apple-m1` baseline) | None | None |

### 4. Version Deltas (`1.99.1` $\to$ `1.100.0` $\to$ `nightly-2026-11-12`) and Tier 1 Policy Guarantees

Basis: execution (`support/tier1_target_specs_*.json`) + documentation (`src/doc/rustc/src/platform-support.md`)

1. **Exact Target-Spec Diffs from `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) to `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`) and `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`):**
   - Between `1.99.1` and `1.100.0`: **zero code-generation diffs** across all 8 Tier 1 target
     specs (`tier1_target_specs_1_99_1.json` and `tier1_target_specs_1_100_0.json` are identical
     on all 61 codegen fields).
   - Between `1.99.1` and `nightly-2026-11-12`, exactly **4 fields** changed across the 8 Tier 1
     targets:
     1. `aarch64-pc-windows-msvc`: `features` changed from `"+v8a,+neon"` to
        `"+v8a,+neon,+outline-atomics"`.
     2. `aarch64-unknown-linux-gnu`: `pre-link-args` removed `"-Wl,--fix-cortex-a53-843419"`.
     3. `x86_64-pc-windows-gnu`: `has-thread-local` changed from `None` (`false`) to `true`
        (switching MinGW from GCC `emutls` to native Windows TLS).
     4. `i686-pc-windows-msvc`: `metadata.host_tools` changed from `true` to `false` (demoting
        32-bit `i686-pc-windows-msvc` from a Tier 1 *host* toolchain while keeping it a Tier 1
        *target* with full `std` and CI test execution).
2. **What Tier 1 Status Guarantees Under Rust's Target Tier Policy (`compiler/rustc_target/src/spec/mod.rs:TargetMetadata`):**
   - Every Tier 1 target sets `tier: Some(1)` and `std: Some(true)` in `TargetMetadata`.
   - Full `ui`, `codegen`, `run-make`, `mir-opt`, `assembly`, and `std`/`core`/`alloc` test suites
     are executed as merge-blocking CI gates on every PR to `rust-lang/rust`.
   - Pre-built target `rust-std` artifacts are published for every release channel; for the 7
     targets with `host_tools: Some(true)` (`x86_64-unknown-linux-gnu`, `x86_64-pc-windows-msvc`,
     `x86_64-pc-windows-gnu`, `i686-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`,
     `aarch64-apple-darwin`, `aarch64-pc-windows-msvc`, plus `i686-pc-windows-msvc` in `1.99.1`/`1.100.0`),
     full host `rustc`, `cargo`, `rustdoc`, `clippy`, and `miri` binaries are built and tested.

## Boundaries

- **Tier 2 and Tier 3 target specs:** `rustc` `1.99.1` defines 245 built-in targets in
  `compiler/rustc_target/src/spec/targets/`; this report's JSON golden files and LLVM IR probe
  matrix cover the 8 Tier 1 targets.
- **Custom JSON target specifications (`--target path/to/custom.json`):** `Target::from_json`
  accepts user-supplied JSON target specs on nightly (`-Zjson-target-spec`); a verified drop-in
  replacement targeting Tier 1 targets can pin the 8 built-in target specs directly and reject
  arbitrary JSON target specs outside its verified target set.

## Evidence

- **Primary upstream sources (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_target/src/spec/mod.rs:1950-2650` — `Target`, `TargetOptions`, `TargetMetadata`,
    and `TargetOptions::default()`.
  - `compiler/rustc_target/src/spec/targets/{x86_64_unknown_linux_gnu,x86_64_pc_windows_msvc,x86_64_pc_windows_gnu,i686_unknown_linux_gnu,i686_pc_windows_msvc,aarch64_unknown_linux_gnu,aarch64_apple_darwin,aarch64_pc_windows_msvc}.rs`
    and `spec/base/{linux_gnu,windows_msvc,windows_gnu,apple/mod}.rs`.
  - `compiler/rustc_codegen_llvm/src/llvm_util.rs:46-169` — `configure_llvm` global LLVM options.
  - `compiler/rustc_codegen_llvm/src/attributes.rs:45-160,510-530` — `uwtable`, `frame-pointer`,
    `probe-stack`, `nonlazybind`, `target-cpu`, and `target-features` function attribute emission.
- **Primary upstream sources (`rust-lang/llvm-project` @ `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`):**
  - `llvm/lib/Target/AArch64/AArch64RegisterInfo.cpp:250-355` — `getReservedRegs` (`x18` on
    Darwin and Windows, `x29` frame-pointer reservation).
  - `llvm/lib/Target/AArch64/AArch64Subtarget.cpp:1-450` and `llvm/lib/Target/X86/X86Subtarget.cpp:1-380`.
- **Preserved support artifacts:**
  - `support/tier1_target_specs_1_99_1.json` — full `--print target-spec-json` output for all
    8 Tier 1 targets on Rust `1.99.1`.
  - `support/tier1_target_specs_1_100_0.json` — full `--print target-spec-json` output on Rust
    `1.100.0`.
  - `support/tier1_target_specs_nightly_2026_11_12.json` — full `--print target-spec-json`
    output on `nightly-2026-11-12`.
  - `support/target_options_field_semantics.json` — cross-target comparison keyed by field name
    plus emitted LLVM IR `target datalayout`, `target triple`, `attributes #0`, and module flags
    (`PIC Level`, `uwtable`, `frame-pointer`, `RtLibUseGOT`) across all 8 Tier 1 targets.

## Revalidation

To regenerate and diff the Tier 1 target-spec JSON files on any `rustc` toolchain:

```bash
for tgt in aarch64-apple-darwin aarch64-pc-windows-msvc aarch64-unknown-linux-gnu \
           i686-pc-windows-msvc i686-unknown-linux-gnu x86_64-pc-windows-gnu \
           x86_64-pc-windows-msvc x86_64-unknown-linux-gnu; do
  RUSTC_BOOTSTRAP=1 rustc +1.99.1 -Zunstable-options --target "$tgt" --print target-spec-json
done
```

Compare the output against `support/tier1_target_specs_1_99_1.json` and
`support/target_options_field_semantics.json`.
