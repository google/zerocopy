# Rust ELF64 Post-Link Relocation, TLS Relaxation, and `.eh_frame_hdr` Ground Truth (`GNU ld` vs. `rust-lld`)

## Summary

`Basis: execution + source + normative + derived`

Post-link binary verification for `rustc` on `x86_64-unknown-linux-gnu` cannot treat pre-link relocatable `.rlib` machine code as immutable bytes. Even before whole-program optimization, the static linker rewrites opcodes, shifts internal instruction boundaries, redirects GOT loads, pads inter-function gaps, and synthesizes exception-unwinding lookup tables. Through a live sysroot `.rlib` census across `rustc 1.98.0-nightly` and cross-checked baseline counts from `rustc 1.102.0-nightly`, upstream source inspection across `rust-lang/rust` and `llvm/llvm-project`, an 8-configuration `std` + 4-configuration `#![no_std]` live link probe comparing `GNU ld 2.47` against Rust's bundled `rust-lld 22.1.6`, and a kernel-checked `Lean v4.34.1` differential verifier ([Elf64PostLinkDifferentialCheck.lean](support/Elf64PostLinkDifferentialCheck.lean)), we establish six ground-truth findings:

1. **Sysroot `.rlib` relocation profile (`10` ELF64 types; `0` pure-Rust `GOTPCRELX`/`REX_GOTPCRELX`):** Across all `30` `x86_64-unknown-linux-gnu` sysroot `.rlib` archives in `rustc 1.98.0-nightly` (`320,016` relocations; cross-checked against `30` `.rlib`s / `350,943` relocations in `rustc 1.102.0-nightly`), pure-Rust crates emit zero `R_X86_64_GOTPCRELX` or `R_X86_64_REX_GOTPCRELX` relocations and instead emit **`15,787`** non-relaxable `R_X86_64_GOTPCREL` (`17,227` in `1.102.0-nightly`) because `x86_64_unknown_linux_gnu` sets `plt_by_default = false` (`RtLibUseGOT = 1`) while `TargetOptions::default()` keeps `relax_elf_relocations = false`. All **`84`** `R_X86_64_REX_GOTPCRELX` relocations in both toolchains originate solely in `libprofiler_builtins` (compiled from 18 C/C++ source files via `cc::Build`).
2. **Starker `GNU ld` vs. `rust-lld` divergence on legacy `R_X86_64_GOTPCREL` causes `#![no_std]` `-static-pie` `SIGSEGV`:** On `R_X86_64_GOTPCREL` data loads (`48 8b <modrm>`), `GNU ld 2.47` relaxes `mov` -> `lea` (`48 8d <modrm>`) in PIE and static-PIE binaries while leaving `call *got` (`ff 15`) unrelaxed, whereas `rust-lld 22.1.6` (`X86_64::adjustGotPcExpr`) leaves both unrelaxed unless `R_X86_64_[REX_]GOTPCRELX` (`-Z relax-elf-relocations=yes`) is present. Consequently, linking a freestanding `#![no_std] #![no_main] -nostdlib -static-pie` Rust binary without an explicit self-relocation stub succeeds (`EXIT_OK`, `0` dynamic relocations) under `GNU ld 2.47` and with `-Z relax-elf-relocations=yes` under `rust-lld`, yet **crashes with `SIGSEGV` (`-11`)** on default `rustc` + `rust-lld 22.1.6` (Rust's default `gnu-lld-cc` linker) due to an unresolved `R_X86_64_RELATIVE` GOT slot under ASLR.
3. **`--no-relax` suppresses GOT relaxation, NOT TLS relaxation:** Passing `-Wl,--no-relax` disables `GOTPCREL`/`GOTPCRELX`/`REX_GOTPCRELX` opcode rewrites on both linkers, yet **neither `GNU ld 2.47` nor `rust-lld 22.1.6` suppresses TLS `GD -> LE`, `LD -> LE`, or `IE -> LE` code-sequence transformations** in dynamic PIE binaries.
4. **Byte-exact TLS boundary shifts and register encodings:** In PIE and static-PIE outputs (both linkers), `TLSGD -> LE` (`22` B) keeps total window length unchanged while shifting the internal instruction boundary from `8B + 8B` (`data16 lea` + `data16 data16 rex.W call`) to `9B + 7B` (`64 48 8b 04 25 00 00 00 00` + `48 8d 80 <tpoff32>`). `TLSLD -> LE` shifts `7B + 5B + 7B` to `12B + 7B` (`66 66 66 64 48 8b 04 25 00 00 00 00` + `48 {8b,8d} 80 <tpoff32>`). `GOTTPOFF -> LE` rewrites both register-form `48 8b 05 -> 48 c7 c0` (`mov` -> `mov imm`), `%rax` add-form `48 03 05 -> 48 8d 80` (`add` -> `lea`), and extended-register add-form `4c 03 25 -> 49 81 c4` (`add %r12` -> `add $imm, %r12`). All three remain unrelaxed in `cdylib` (`R_X86_64_DTPMOD64`, `R_X86_64_TPOFF64`).
5. **`--rosegment` flips `.eh_frame_hdr` key polarity and inter-section `RIP` displacement signs:** `GNU ld 2.47` orders `.text < .rodata < .eh_frame_hdr < .eh_frame` (positive `lea` offsets into `.rodata`, `100%` negative `init_loc_rel` keys in `.eh_frame_hdr`, multi-byte `NOP` padding with `0` `int3`), whereas `rust-lld 22.1.6` places `.rodata < .eh_frame_hdr < .eh_frame < .text` (negative backward `lea` offsets into `.rodata`, `100%` positive `init_loc_rel` keys in `.eh_frame_hdr`, and `3,227`–`9,158` `0xCC` `int3` trap padding instructions). Both synthesize valid version-`1` `.eh_frame_hdr` tables (`enc=(0x1b, 0x03, 0x3b)`) with strictly sorted PC keys and `0` FDE base mismatches.
6. **Clean kernel-checked Lean `v4.34.1` differential verifier:** [Elf64PostLinkDifferentialCheck.lean](support/Elf64PostLinkDifferentialCheck.lean) (`788` LOC, `63` defs/types, `18` theorems) discharges `decodeI32LE_encodeI32LE`, TLS/GOT transition soundness, differential linker-policy verification (`GNU ld` vs. `rust-lld`), `.eh_frame_hdr` sortedness + FDE relocation checks, and negative tamper-rejection theorems in `4.721s` (`525.44 MiB` RSS) using only `[propext]` (and `0` axioms on `reject_truncated_tls_sequences`), with zero `sorry`, zero `omega`, zero `bv_decide`, and zero `native_decide`.

---

## Applicability

`Basis: source + execution`

This analysis applies to:

- **Target ABI & toolchain:** `rustc` targeting `x86_64-unknown-linux-gnu` across `rustc 1.98.0-nightly` (`rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, LLVM `22.1.6`) and `rustc 1.102.0-nightly` (`rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`), where `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs` sets `plt_by_default = false` and `compiler/rustc_target/src/spec/base/linux_gnu.rs` enables `LinkerFlavor::Gnu(Cc::Yes, Lld::Yes)` (defaulting to bundled `rust-lld` / `gcc-ld/ld.lld`) alongside `static_position_independent_executables = true`.
- **Linkers & modes:** `GNU ld (GNU Binutils for Debian) 2.47` and bundled `rust-lld` (`LLD 22.1.6`, `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5`, cross-checked against upstream `llvm/llvm-project@fc4aad7b5db3fff421df9a9637605b9ca5667881` and `llvm/llvm-project@392dfff97d29b59d77e5cac6d4b6ef2585fe7117`), across dynamic PIE (`-C relocation-model=pic`), static PIE (`-C target-feature=+crt-static`), `-Wl,--no-relax`, `cdylib`, and freestanding `#![no_std] -nostdlib -static-pie`.
- **Verifier design role:** Any verified Rust compiler backend, binary validator, or translation validator consuming post-link `x86_64` ELF64 images must account for linker-mutated opcode sequences, non-monotonic `.rodata`/`.text` ordering, `int3` inter-function padding, `.eh_frame_hdr` search-table synthesis, and the `rust-lld` legacy `R_X86_64_GOTPCREL` constraint.
- **Complementary scope note:** The sibling corpus report [`reports/gotpcrelx-tlsdesc-linker-relaxations-ifunc-ordering-and-linksem-slack/REPORT.md`](../gotpcrelx-tlsdesc-linker-relaxations-ifunc-ordering-and-linksem-slack/REPORT.md) examines C/GCC `GOTPCRELX`, `TLSDESC`, `STV_GNU_IFUNC`, and `linksem` slack; the present report specifically characterizes `rustc` sysroot `.rlib` output, head-to-head `rust-lld` vs. `GNU ld` linking, `.eh_frame_hdr` binary search invariants, `#![no_std]` static-PIE failure behavior, and Lean `v4.34.1` differential checking.

---

## Findings

### 1. Upstream `rustc` and LLVM/LLD Source Mechanics Behind Emit-Time Relocation Choices

`Basis: source + normative`

Direct source inspection across `rust-lang/rust` and `llvm/llvm-project` explains why stock `rustc` emits legacy `R_X86_64_GOTPCREL` in pure-Rust code, why `libprofiler_builtins` alone emits `R_X86_64_REX_GOTPCRELX`, and why `rust-lld` refuses GOT relaxation on legacy `R_X86_64_GOTPCREL`:

1. **`plt_by_default = false` + `relax_elf_relocations = false` (`rust-lang/rust`):**
   - `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:8` sets `base.plt_by_default = false;` (`1.102.0-nightly` and `1.98.0-nightly`).
   - `compiler/rustc_target/src/spec/base/linux.rs:11,13` enables `position_independent_executables: true` and `has_thread_local: true`.
   - `compiler/rustc_target/src/spec/base/linux_gnu.rs` configures `LinkerFlavor::Gnu(Cc::Yes, Lld::Yes)` (`L13` in `1.102.0-nightly`; `L9` in `1.98.0-nightly`) and explicitly declares `static_position_independent_executables: true` (`L6` in `1.102.0-nightly`).
   - `compiler/rustc_target/src/spec/mod.rs` (`L2315, 2398, 2547, 2559, 2755, 2781, 2835, 2838` in `1.102.0-nightly`; `L2406, 2489, 2633, 2645, 2837, 2863, 2916, 2919` in `1.98.0-nightly`) sets `TargetOptions::default()` with `tls_model: TlsModel::GeneralDynamic`, `plt_by_default: true`, `relax_elf_relocations: false`, and `eh_frame_header: true`.
   - `compiler/rustc_codegen_llvm/src/context.rs` (`L280-282` in `1.102.0-nightly`; `L279-280` in `1.98.0-nightly`) emits module flag `"RtLibUseGOT" = 1` whenever `!sess.needs_plt()`, routing calls/globals through GOT loads rather than PLT relocations.
   - `compiler/rustc_codegen_llvm/src/back/write.rs` (`L208-209` in `1.102.0-nightly`; `L230-231, 299` in `1.98.0-nightly`) forwards `relax_elf_relocations = sess.opts.unstable_opts.relax_elf_relocations.unwrap_or(sess.target.relax_elf_relocations)` (`false` by default) to `llvm::TargetOptions::RelaxELFRelocations`.
   - `compiler/rustc_codegen_ssa/src/back/linker.rs` (`L454, 923-924` in `1.102.0-nightly`; `L461, 928-929` in `1.98.0-nightly`) passes `-shared` for `dylib`/`cdylib` and `--eh-frame-hdr` in `add_eh_frame_header`; `compiler/rustc_codegen_ssa/src/back/link.rs` (`L2763-2767, 4141` in `1.102.0-nightly`; `L2345, 3610` in `1.98.0-nightly`) applies `RelroLevel::Full` and locates self-contained `gcc-ld`.
   - `library/profiler_builtins/build.rs:24-46,103` compiles 18 C/C++ compiler-rt profiling files (`InstrProfiling*.c`/`.cpp`) via `cc::Build` (`cfg.compile("profiler-rt")`), inheriting host C toolchain defaults (`-mrelax-relocations=yes`) rather than `rustc`'s `relax_elf_relocations = false`.
2. **LLVM MC and LLD `X86_64` gating (`llvm/llvm-project`):**
   - `llvm/lib/Target/X86/MCTargetDesc/X86ELFObjectWriter.cpp:215-237` (identical across `22.1.6` and `23.1.5`) downgrades `reloc_riprel_4byte_relax`, `reloc_riprel_4byte_relax_rex`, and `reloc_riprel_4byte_movq_load` strictly to `ELF::R_X86_64_GOTPCREL` whenever `!X86RelaxRelocations`, emitting `R_X86_64_GOTPCRELX` or `R_X86_64_REX_GOTPCRELX` only when `-relax-elf-relocations` is enabled.
   - `lld/ELF/Arch/X86_64.cpp`:
     * `trapInstr = {0xcc, 0xcc, 0xcc, 0xcc}; // 0xcc = INT3` (`22.1.6` `L93`, `23.1.5` `L99`).
     * `relaxTlsGdToLe` (`22.1.6` `L477-497`, `23.1.5` `L781-801`): writes `{0x64, 0x48, 0x8b, 0x04, 0x25, 0,0,0,0, 0x48, 0x8d, 0x80, 0,0,0,0}` (`9B + 7B`) and patches `val + 4` at `loc + 8`.
     * `relaxTlsIeToLe` (`22.1.6` `L571-670`, `23.1.5` `L870-971`): handles both `0x48 0x8b -> 0x48 0xc7` (`mov` to `mov imm`, with ModRM reg shifted to `0xc0 | reg`), `0x48 0x03 -> 0x48 0x8d` (`add` -> `lea`), and extended `%r12` (`0x4c 0x03 0x25 -> 0x49 0x81 0xc4`) / `%rsp` (`0x48 0x03 0x25 -> 0x48 0x81 0xc4`).
     * `relaxTlsLdToLe` (`22.1.6` `L674-712`, `23.1.5` `L973-1012`): overwrites the `7B + 5B` `lea + call __tls_get_addr` sequence with `12B` `{0x66, 0x66, 0x66, 0x64, 0x48, 0x8b, 0x04, 0x25, 0,0,0,0}` leaving the trailing `R_X86_64_DTPOFF32` `7B` instruction intact.
     * `adjustGotPcExpr` (`22.1.6` `L958-989`, `23.1.5` `L1257-1288`) & `relaxGot` (`22.1.6` `L1072-1110`, `23.1.5` `L1371-1410`): relaxes ONLY when `ctx.arg.relax && addend == -4 && type ∈ {R_X86_64_GOTPCRELX, R_X86_64_REX_GOTPCRELX, R_X86_64_CODE_4_GOTPCRELX}` (turning `0x8b -> 0x8d`, `ff 15 -> 67 e8`, `ff 25 -> e9 ... 90`). Legacy `R_X86_64_GOTPCREL` is **never** relaxed by LLD.
   - `lld/ELF/SyntheticSections.cpp` (`22.1.6` `L580-669`, `23.1.5` `L372-490`): emits `.eh_frame_hdr` with header `[1, 0x1b, 0x03, 0x3b]`, sorting entries via `llvm::stable_sort` + `llvm::unique` on `pcRel = pc - hdrVA`.

---

### 2. Sysroot `.rlib` ELF64 Relocation Census (`rustc 1.98.0-nightly` & `1.102.0-nightly`)

`Basis: execution (live readelf -rW census via probe_elf64_relaxation_lld_vs_ld.py; cross-checked against 1.102.0-nightly baseline)`

Scanning every ELF relocatable member across all `30` `x86_64-unknown-linux-gnu` sysroot `.rlib`s recovers an identical **10-type ELF64 relocation vocabulary** and an identical **6-crate relaxable footprint**:

| Relocation Type | `1.98.0-nightly` Total | `1.98.0` `.text` | `1.98.0` `.eh_frame` | `1.98.0` `.data`/`.rodata` | `1.98.0` `.debug_*` | `1.102.0-nightly` Total | Post-Link Opcode Behavior |
| :--- | ---: | ---: | ---: | ---: | ---: | ---: | :--- |
| `R_X86_64_64` | `163,252` | `0` | `0` | `3,548` | `159,704` | `182,041` | Data/DWARF pointer relocation (becomes `RELATIVE` in PIE `.data.rel.ro`) |
| `R_X86_64_32` | `103,781` | `0` | `0` | `0` | `103,781` | `113,289` | Non-ALLOC DWARF offsets only |
| `R_X86_64_PC32` | `28,916` | `14,367` | `5,845` | `8,704` | `0` | `28,992` | `100%` of `.eh_frame` FDE `initial_location`; `lea rel(%rip)` in `.text` |
| `R_X86_64_GOTPCREL` | `15,787` | `15,787` | `0` | `0` | `0` | `17,227` | `GNU ld`: relaxes `mov->lea` (not `call`); `rust-lld`: **never relaxes** |
| `R_X86_64_PLT32` | `7,868` | `7,868` | `0` | `0` | `0` | `8,894` | Direct/PLT `call`/`jmp` target + `__tls_get_addr-0x4` companion |
| `R_X86_64_TLSGD` | `168` | `168` | `0` | `0` | `0` | `178` | Relaxable: `GD -> LE` (`8B+8B -> 9B+7B`, even under `--no-relax`) |
| `R_X86_64_GOTTPOFF` | `116` | `116` | `0` | `0` | `0` | `198` | Relaxable: `IE -> LE` (`mov->mov imm`, `add->lea`, `%r12` `add->add imm`) |
| `R_X86_64_REX_GOTPCRELX` | `84` | `84` | `0` | `0` | `0` | `84` | Relaxable: `mov -> lea` on both linkers (`libprofiler_builtins` only) |
| `R_X86_64_DTPOFF32` | `28` | `28` | `0` | `0` | `0` | `25` | `TLSLD` trailing offset (paired with `TLSLD`, patched to `TPOFF32`) |
| `R_X86_64_TLSLD` | `16` | `16` | `0` | `0` | `0` | `15` | Relaxable: `LD -> LE` (`7B+5B+7B -> 12B+7B`) |
| **Total** | **`320,016`** | **`38,434`** | **`5,845`** | **`12,252`** | **`263,485`** | **`350,943`** | `475` relaxable in `1.102.0`; `384` relaxable in `1.98.0` |

Per-crate breakdown of opcode-mutating relocations (`384` in `1.98.0-nightly`, `475` in `1.102.0-nightly` across the exact same `6` `.rlib` stems):

| Sysroot Crate Stem | `1.98.0-nightly` Relaxable Relocs | `1.102.0-nightly` Relaxable Relocs | Representative Relocated Symbols Observed |
| :--- | :--- | :--- | :--- |
| `libproc_macro` | `119 R_X86_64_TLSGD` | `131 R_X86_64_TLSGD` | `proc_macro::bridge::client::state::BRIDGE_STATE`, `symbol::INTERNER`, `ALREADY_RUNNING_SAME_THREAD` |
| `libprofiler_builtins` | `84 R_X86_64_REX_GOTPCRELX` | `84 R_X86_64_REX_GOTPCRELX` | `stderr`, `lprofBufferWriter`, `free` (18 C/C++ compiler-rt TUs built via `cc::Build`) |
| `librustc_public` | `115 R_X86_64_GOTTPOFF` | `196 R_X86_64_GOTTPOFF` | `rustc_thread_pool::tlv::TLV`, `rustc_public::compiler_interface::TLV::FOO` |
| `librustc_public_bridge` | `1 R_X86_64_GOTTPOFF` | `2 R_X86_64_GOTTPOFF` | `rustc_thread_pool::tlv::TLV` |
| `libstd` | `36 R_X86_64_TLSGD`, `16 R_X86_64_TLSLD` | `36 R_X86_64_TLSGD`, `15 R_X86_64_TLSLD` | `std::thread::current::CURRENT`, `LOCAL_PANIC_COUNT`, `OUTPUT_CAPTURE`, `destructors::list::DTORS` |
| `libtest` | `13 R_X86_64_TLSGD` | `11 R_X86_64_TLSGD` | `RandomState::new::KEYS`, `SPAWN_HOOKS`, `current_thread_id::DUMMY` |

Notably, `.eh_frame` across the entire `30`-`.rlib` sysroot contains **`5,845 / 5,845` (`100%`) `R_X86_64_PC32`** relocations in `1.98.0-nightly`, confirming zero non-`PC32` relocation forms inside sysroot unwind frames.

---

### 3. Live Head-to-Head `GNU ld 2.47` vs. `rust-lld 22.1.6` Linking Probe

`Basis: execution (live compile/link/objdump/readelf/run via probe_elf64_relaxation_lld_vs_ld.py; results in elf64_postlink_probe_results.json)`

We compiled separate PIC `.o` specimens targeting every relaxation class (`tls_gd`, `tls_ld`, `tls_ie`, `got_strict` with default `R_X86_64_GOTPCREL`, `got_relaxable` with `-Z relax-elf-relocations=yes`, and a `panic=unwind` driver with `backward_leaf` -> `forward_unwinding_caller`) and linked all `8` linker/mode combinations. Every linked executable (`6/6`) exited with code `0` including live `catch_unwind` stack unwinding and `Drop` verification.

#### 3a. Macro Binary Layout, Dynamic Relocations, Padding, and Link Time

| Config (`linker` / `mode`) | Link Time (s) | Size (B) | Exec `rc` | `.text` VA / Size | `.rodata` VA / Size | Dynamic Relocs | Inter-Fn Padding (`int3` / `nop`) |
| :--- | ---: | ---: | ---: | :--- | :--- | :--- | :--- |
| `dyn_pie_gnu_ld` | `0.3318` | `4,317,776` | `0` | `0x5060` / `249,514` | `0x42000` / `29,952` | `RELATIVE: 530`, `GLOB_DAT: 67`, `JUMP_SLOT: 2` | `0` `int3` / `807` `nop` |
| `dyn_pie_rust_lld` | `0.1785` | `4,363,440` | `0` | `0x13b70` / `248,915` | `0x7590` / `21,720` | `RELATIVE: 552`, `GLOB_DAT: 67`, `JUMP_SLOT: 2` | `3,227` `int3` / `313` `nop` |
| `dyn_pie_norelax_gnu_ld` | `0.2854` | `4,317,776` | `0` | `0x5060` / `249,514` | `0x42000` / `29,952` | `RELATIVE: 555`, `GLOB_DAT: 67`, `JUMP_SLOT: 2` | `0` `int3` / `807` `nop` |
| `dyn_pie_norelax_rust_lld` | `0.1616` | `4,363,528` | `0` | `0x13bb0` / `248,915` | `0x75d0` / `21,720` | `RELATIVE: 555`, `GLOB_DAT: 67`, `JUMP_SLOT: 2` | `3,227` `int3` / `313` `nop` |
| `static_pie_gnu_ld` | `0.5955` | `5,360,224` | `0` | `0xc240` / `944,051` | `0xf3000` / `152,224` | `RELATIVE: 1913`, `IRELATIVE: 29`, `NONE: 1` | `0` `int3` / `7,286` `nop` |
| `static_pie_rust_lld` | `0.2363` | `5,300,136` | `0` | `0x45040` / `873,811` | `0xd360` / `139,352` | `RELATIVE: 1710`, `IRELATIVE: 24` | `9,158` `int3` / `5,359` `nop` |
| `cdylib_gnu_ld` | `0.3818` | `4,287,984` | N/A | `0x5060` / `230,483` | `0x3e000` / `27,280` | `RELATIVE: 460`, `GLOB_DAT: 63`, `DTPMOD64: 4`, `JUMP_SLOT: 2`, `TPOFF64: 1` | `0` `int3` / `725` `nop` |
| `cdylib_rust_lld` | `0.1987` | `4,327,976` | N/A | `0x11e60` / `230,467` | `0x6e30` / `18,176` | `RELATIVE: 480`, `GLOB_DAT: 63`, `DTPMOD64: 4`, `JUMP_SLOT: 3`, `TPOFF64: 1` | `2,927` `int3` / `284` `nop` |

#### 3b. Byte-Exact Pre-Link vs. Post-Link Instruction Transformations

| Probe Function / Reloc | Pre-Link `.o` Instruction Window | Post-Link `GNU ld 2.47` (PIE / `--no-relax` / Static-PIE) | Post-Link `rust-lld 22.1.6` (PIE / `--no-relax` / Static-PIE) | Post-Link `cdylib` (Both) |
| :--- | :--- | :--- | :--- | :--- |
| `get_tls_gd` (`R_X86_64_TLSGD` + `PLT32 __tls_get_addr`) | `66 48 8d 3d 00000000` (`8B`) \| `66 66 48 e8 00000000` (`8B`) | `64 48 8b 04 25 00000000` (`9B`) \| `48 8d 80 a8ffffff` (`7B`, `-0x58`; static-PIE `48ffffff`, `-0xb8`; **even under `--no-relax`**) | `64 48 8b 04 25 00000000` (`9B`) \| `48 8d 80 a8ffffff` (`7B`, `-0x58`; static-PIE `58ffffff`, `-0xa8`; **even under `--no-relax`**) | **Unrelaxed** (`__tls_get_addr@plt` + `DTPMOD64`) |
| `get_tls_ld` / `get_tls_ld_addr` (`TLSLD` + `PLT32` + `DTPOFF32`) | `48 8d 3d 00000000` (`7B`) \| `e8 00000000` (`5B`) \| `48 {8b,8d} 80 00000000` (`7B`) | `66 66 66 64 48 8b 04 25 00000000` (`12B`) \| `48 {8b,8d} 80 a0ffffff` (`7B`, `-0x60`; static-PIE `40ffffff`) | `66 66 66 64 48 8b 04 25 00000000` (`12B`) \| `48 {8b,8d} 80 a0ffffff` (`7B`, `-0x60`; static-PIE `50ffffff`) | **Unrelaxed** (`48 {8b,8d} 80 08 00 00 00`) |
| `get_tls_ie` (`GOTTPOFF` -> `%rax`) | `48 8b 05 00000000` (`mov`) | `48 c7 c0 98ffffff` (`mov $0xffffffffffffff98, %rax`; static-PIE `38ffffff`) | `48 c7 c0 98ffffff` (static-PIE `48ffffff`) | **Unrelaxed** (`mov %rip->got`) |
| `get_tls_ie_addr` (`GOTTPOFF` `add -> %rax`) | `48 03 05 00000000` (`add`) | `48 8d 80 98ffffff` (`lea -0x68(%rax), %rax`) | `48 8d 80 98ffffff` (`lea -0x68(%rax), %rax`) | **Unrelaxed** (`48 03 05 ...`) |
| `get_tls_ie_r12_asm` (`GOTTPOFF` `add -> %r12`) | `4c 03 25 00000000` (`add %r12`) | `49 81 c4 98ffffff` (`add $-0x68, %r12`) | `49 81 c4 98ffffff` (`add $-0x68, %r12`) | **Unrelaxed** (`4c 03 25 ...`) |
| `use_got_strict` (default `rustc` `R_X86_64_GOTPCREL`: `mov` + `call`) | `48 8b 1d 00000000` + `ff 15 00000000` | `dyn_pie`/`static_pie`: **`48 8d 1d` (`lea`, relaxed!) + `ff 15` (`call *got`, unrelaxed!)**<br>`--no-relax`: both stay `48 8b 1d` + `ff 15` | **ALL PIE/static-PIE configs stay `48 8b 1d` (`mov`, UNRELAXED) + `ff 15` (`call *got`)** | **Unrelaxed** (`48 8b 1d` + `ff 15`) |
| `use_got_relaxable` (`-Z relax-elf-relocations=yes`: `REX_GOTPCRELX` + `GOTPCRELX`) | `48 8b 1d 00000000` + `ff 15 00000000` | `dyn_pie`: **`48 8d 1d 48 79 03 00` (`+0x37948`) + `67 e8 cf fe ff ff`**<br>`--no-relax`: both stay `48 8b 1d` + `ff 15` | `dyn_pie`: **`48 8d 1d f8 35 ff ff` (`-0xca08` backward!) + `67 e8 cf fe ff ff`**<br>`--no-relax`: both stay `48 8b 1d` + `ff 15` | **Unrelaxed** (`48 8b 1d` + `ff 15`) |
| `forward_unwinding_caller` -> `backward_leaf` (`R_X86_64_PC32` / `GOTPCREL`) | `48 8d 05 00000000` (`lea 0x0(%rip), %rax`, `R_X86_64_PC32`) | `48 8d 05 11 ff ff ff` (`lea -0xef(%rip), %rax`; **`0xCC` count: `0`**, multi-byte `NOP`s between functions) | `48 8d 05 11 ff ff ff` (`lea -0xef(%rip), %rax`; trailing `0xCC` trap padding between functions) | GOT-indirect `mov`: `48 8b 05 d9 4d 04 00` (`GNU ld`) / `48 8b 05 c9 ab 03 00` (`rust-lld`) because exported `#[no_mangle]` `backward_leaf` is interposable in `cdylib` |

Two critical structural subtleties appear verbatim in the bytes above:

- **Inter-function `0xCC` padding vs. `NOP` sleds (`backward_leaf` -> `forward_unwinding_caller`):** Every `GNU ld` binary emits multi-byte NOPs (`66 2e 0f 1f 84 00 00 00 00 00`, `0f 1f 40 00`, `66 90`) between aligned `.text` functions (`0` `int3` across all `4` `GNU ld` binaries), whereas `rust-lld` fills alignment gaps with `0xCC` (`3,227` `int3` instructions in `dyn_pie`, `9,158` in `static_pie`, `2,927` in `cdylib`). Any linear disassembler that does not distinguish function bounds from trap padding sees `3,227+` extra `int3` instructions inside executable `.text`.
- **Negative backward `lea` displacement on `--rosegment`:** In `use_got_relaxable`, `GNU ld` relaxes `mov EXT_VAL_RELAXABLE@GOTPCREL(%rip), %rbx` to `lea +0x37948(%rip)` because `.text` (`0x5060`) precedes `.rodata` (`0x42000`), whereas `rust-lld` relaxes the identical `.o` to **`48 8d 1d f8 35 ff ff` (`lea -0xca08(%rip)`)** because `--rosegment` places `.rodata` (`0x7590`) at lower virtual addresses than `.text` (`0x13b70`). Signed two's-complement `i32` handling is therefore mandatory even for forward source references to `.rodata`.

---

### 4. Freestanding `#![no_std]` `-static-pie` `SIGSEGV` Matrix

`Basis: execution (live #![no_std] #![no_main] -nostdlib -static-pie binaries run under ASLR)`

To test whether the `GNU ld` vs. `rust-lld` `R_X86_64_GOTPCREL` divergence causes an observable runtime failure without `glibc`/`crt1.o`, we linked a minimal freestanding `#![no_std] #![no_main]` static-PIE binary (`_start` calls `helper(40)` summing an argument with a read-only `static GLOBAL_CONST: usize = 2` and invokes syscall `exit(0)`/`exit(1)` directly with **no `_DYNAMIC` self-relocator**):

| Binary Configuration | Compiler Reloc on `GLOBAL_CONST` | Post-Link `helper+0xa` Instruction | `.rela.dyn` Dynamic Relocs | Execution Outcome |
| :--- | :--- | :--- | :--- | :--- |
| `nostd_default_gotpcrel_gnu_ld` | `R_X86_64_GOTPCREL` | `48 8d 0d cf 0f 00 00` (`lea 0xfcf(%rip), %rcx` -> `0x2000`) | `{}` (**0 relocs!**) | **`EXIT_OK` (`rc = 0`)** |
| `nostd_default_gotpcrel_rust_lld` | `R_X86_64_GOTPCREL` | `48 8b 0d df 10 00 00` (`mov 0x10df(%rip), %rcx` -> GOT `0x2430`) | `{'R_X86_64_RELATIVE': 1}` | **`SIGSEGV` (`rc = -11`)** |
| `nostd_relax_elf_relocs_yes_gnu_ld` | `R_X86_64_REX_GOTPCRELX` | `48 8d 0d cf 0f 00 00` (`lea 0xfcf(%rip), %rcx` -> `0x2000`) | `{}` (**0 relocs!**) | **`EXIT_OK` (`rc = 0`)** |
| `nostd_relax_elf_relocs_yes_rust_lld` | `R_X86_64_REX_GOTPCRELX` | `48 8d 0d 57 ef ff ff` (`lea -0x10a9(%rip), %rcx` -> `0x298`) | `{}` (**0 relocs!**) | **`EXIT_OK` (`rc = 0`)** |

Because `rustc` defaults to `relax_elf_relocations = false` AND `linker-flavor=gnu-lld-cc` (`rust-lld`), any freestanding `#![no_std]` `-nostdlib -static-pie` Rust binary (kernels, hypervisors, bootloaders, minimal harnesses) that loads static data before self-relocating `.rela.dyn` leaves behind an unrelaxed `mov (%rip)->got` (`R_X86_64_RELATIVE: 1`) pointing to an unrelocated link-time address and **immediately segfaults at runtime**, even though the identical `.o` executes cleanly under `GNU ld 2.47`.

---

### 5. `.eh_frame_hdr` Binary-Search Index & FDE Relocation Synthesis

`Basis: execution + source + normative`

Every linked binary (`8/8`) contains a linker-synthesized `.eh_frame_hdr` immediately preceding `.eh_frame`, matching the LSB Core 12-byte header format (`version = 1`, `eh_frame_ptr_enc = 0x1b` [`DW_EH_PE_pcrel | DW_EH_PE_sdata4`], `fde_count_enc = 0x03` [`DW_EH_PE_udata4`], `table_enc = 0x3b` [`DW_EH_PE_datarel | DW_EH_PE_sdata4`]):

| Config | `hdr12` Hex (`version`, `encs`, `ptr_rel`, `fde_count`) | `.eh_frame` Match | `fde_count` | Sorted Strictly (`init_loc_rel`) | FDE Base Mismatches | Negative / Positive `init_loc_rel` Split | First -> Last Decoded Entry PC |
| :--- | :--- | :--- | ---: | :--- | ---: | :--- | :--- |
| `dyn_pie_gnu_ld` | `01 1b 03 3b 84 10 00 00 0f 02 00 00` | `True` (`0x4a588`) | `527` | `True` | `0` | **`527 neg / 0 pos`** (`-279,776` -> `-30,320`) | `0x5020` -> `0x41e90` |
| `dyn_pie_rust_lld` | `01 1b 03 3b 5c 10 00 00 0a 02 00 00` | `True` (`0xdac8`) | `522` | `True` | `0` | **`0 neg / 522 pos`** (`+28,936` -> `+277,832`) | `0x13b70` -> `0x507b0` |
| `dyn_pie_norelax_gnu_ld` | `01 1b 03 3b 84 10 00 00 0f 02 00 00` | `True` (`0x4a588`) | `527` | `True` | `0` | **`527 neg / 0 pos`** | `0x5020` -> `0x41e90` |
| `dyn_pie_norelax_rust_lld` | `01 1b 03 3b 5c 10 00 00 0a 02 00 00` | `True` (`0xdb08`) | `522` | `True` | `0` | **`0 neg / 522 pos`** | `0x13bb0` -> `0x507f0` |
| `static_pie_gnu_ld` | `01 1b 03 3b 44 3b 00 00 67 07 00 00` | `True` (`0x11be68`) | `1,895` | `True` | `0` | **`1,895 neg / 0 pos`** | `0xc020` -> `0xf29e0` |
| `static_pie_rust_lld` | `01 1b 03 3b 04 37 00 00 df 06 00 00` | `True` (`0x32b28`) | `1,759` | `True` | `0` | **`0 neg / 1,759 pos`** | `0x45040` -> `0x11a580` |
| `cdylib_gnu_ld` | `01 1b 03 3b 04 0f 00 00 df 01 00 00` | `True` (`0x45998`) | `479` | `True` | `0` | **`479 neg / 0 pos`** (`-260,720` -> `-30,192`) | `0x5020` -> `0x3d4a0` |
| `cdylib_rust_lld` | `01 1b 03 3b f4 0e 00 00 dd 01 00 00` | `True` (`0xc428`) | `477` | `True` | `0` | **`0 neg / 477 pos`** (`+27,120` -> `+257,376`) | `0x11f20` -> `0x4a290` |

Key invariants verified across every entry in all `8` binaries (`6,108` FDEs total across the 8 linked artifacts):
- Both `init_loc_rel = entry_pc - hdrVA` (relative to `.eh_frame_hdr`) and the target FDE's `fde_pc_begin_rel = entry_pc - (fde_va + 8)` resolve to the exact same `entry_pc` (`fde_pc_mismatches == 0`).
- Because `GNU ld` places `.text` before `.eh_frame_hdr`, `init_loc_rel` is uniformly negative (`-279,776` < ... < `-30,320`), whereas `rust-lld` places `.eh_frame_hdr` inside `--rosegment` before `.text`, making `init_loc_rel` uniformly positive (`+28,936` < ... < `+277,832`). Unwind-table verifiers must decode signed `sdata4` offsets (`DW_EH_PE_datarel | DW_EH_PE_sdata4`), never unsigned `u32`.

---

### 6. Kernel-Checked `Lean v4.34.1` Differential Verifier & Quantitative Scorecard

`Basis: execution + derived (kernel-checked with -DElab.async=false -Ddebug.skipKernelTC=false)`

[Elf64PostLinkDifferentialCheck.lean](support/Elf64PostLinkDifferentialCheck.lean) (`788` LOC, `63` defs/types, `18` theorems) formalizes the byte-level ELF64 relocation policy and `.eh_frame_hdr` search-table verifier in pure constructive Lean (`0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`, `0` `@[extern]`):

- **Constructive 32-bit signed LE round-trip (`decodeI32LE_encodeI32LE`, `decodeI32LE_encodeI32LE_bytes`):** Proves `decodeI32LEList (encodeI32LE x) = some x` for all `x ∈ [-2^31, 2^31 - 1]` without `omega` or `Classical.choice`.
- **TLS relaxation window soundness (`tlsgd_to_le_sound_and_shifts_boundary`, `tlsld_to_le_mov_and_lea_sound`, `gottpoff_to_le_sound`):** Proves semantic equivalence between pre-link TLS models and `Local-Exec` post-link windows while explicitly tracking the `TLSGD` `[1, 9] -> [1, 10]` and `TLSLD` `[1, 8, 13] -> [1, 13]` shifted internal instruction boundaries and `%rax`/`%r12` `GOTTPOFF` forms.
- **Differential linker policy & `#![no_std]` safety (`differential_gotpcrel_policy_and_aslr_sound`, `got_mov_to_lea_semantic_equiv`):** Proves that relaxing `GOTPCREL` `mov -> lea` preserves loaded address semantics *and* eliminates the dynamic `.got` dereference (`ASLR` / static-PIE safe without self-relocation), while rejecting `rust-lld` relaxation on non-`X` `GOTPCREL` and rejecting `GNU ld` relaxation on `call *got` or under `--no-relax`/`cdylib`.
- **`.eh_frame_hdr` binary-search soundness (`checkEhFrameHdr_sound`, `checkStrictlySortedPairs_head_lt_all`, `checkEntriesRelocated_all`):** Proves that `checkEhFrameHdr` guarantees exact `0x01, 0x1b, 0x03, 0x3b` framing, `.eh_frame` pointer recovery, pairwise strict sortedness over signed `init_loc_rel`, and FDE base-address agreement for all entries.
- **Verified positive and negative witnesses (`accept_live_tls_and_got_differential_witnesses`, `reject_gotpcrel_illegal_opcode_mutations`, `reject_truncated_tls_sequences`, `reject_corrupted_eh_frame_hdr`):** Kernel-checked against verbatim bytes extracted from [elf64_postlink_probe_results.json](support/elf64_postlink_probe_results.json), plus negative witnesses rejecting illegal `GOTPCREL -> call` / `rust-lld` `mov->lea` mutations, truncated TLS windows, unsorted `.eh_frame_hdr` keys, and wrong `.eh_frame` pointers. `#print axioms` prints `[propext]` on 10 of 11 top-level theorems and `does not depend on any axioms` on `reject_truncated_tls_sequences`.

#### Quantitative & Validation Scorecard (`L1`–`L6`, `C1`–`C2`, `V1`–`V4`)

| Dimension | Measured Value / Structural Guarantee | Basis |
| :--- | :--- | :--- |
| **`L1` Proof & Authoring Effort** | `Elf64PostLinkDifferentialCheck.lean`: `788` LOC (`63` defs/types, `18` theorems); probe harness `probe_elf64_relaxation_lld_vs_ld.py`: `32,392` B (`393,552` B captured JSON) | Source + Execution |
| **`L2` Toolchain Build / Check Time** | Lean `v4.34.1` synchronous kernel check: `4.721s` (`-DElab.async=false -Ddebug.skipKernelTC=false`); link times `0.1616s`–`0.2363s` (`rust-lld`) vs. `0.2854s`–`0.5955s` (`GNU ld`) across all `8` `std` configs | Execution (`lean`, `rustc`, `ld`, `lld`) |
| **`L3` Seed Compile Latency** | Constructive proof reduction on live `obs*` witnesses runs inside the single `4.721s` kernel check; isolated incremental per-function certificate streaming: **not measured** | Execution (Lean kernel) / scope boundary |
| **`L4` Generated Code Speed** | Dynamic execution across `6/6` `std` PIE/static-PIE executables exited `rc = 0` (`catch_unwind` + `Drop`); `#![no_std]` `-static-pie` exited `EXIT_OK (0)` vs. **`SIGSEGV (-11)`** on `rust-lld` default `GOTPCREL`; cycle/throughput microbenchmarking: **not measured** | Execution (`std` + `nostd` binaries) / boundary |
| **`L5` Checker Throughput & Cold Start** | Verified concrete witness checking over fixed byte slices (`accept_live_*`, `reject_*`) within `4.721s`; standalone C/Rust binary validator throughput (`MB/s` over full `.text`): **not measured** | Execution (Lean kernel) / scope boundary |
| **`L6` Footprint (RAM / Binary)** | Lean kernel max RSS: `525.44 MiB` (`538,048 KiB`); linked binary sizes `4,287,984`–`5,360,224` B (`GNU ld`) vs. `4,327,976`–`5,300,136` B (`rust-lld`) | Execution (`anneal-lean-run`, `os.stat`) |
| **`C1` Spec / TCB Auditability** | `0` `sorryAx`, `0` `Classical.choice`, `0` `Quot.sound`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial`, `0` `@[extern]` (`TrustedBoundary.lean` clean) | Execution (`#print axioms`) |
| **`C2` Orthogonality** | Separating linker-policy choice (`allowsGotOpcodeRelax` by `LinkerFlavor × LinkMode × relaxFlag`) from byte-transformation semantics (`got_mov_to_lea_semantic_equiv`) isolates ABI differences cleanly | Derived from Lean model |
| **`V1` Non-Vacuity / Negatives** | Verified both positive (`accept_live_tls_and_got_differential_witnesses`) and `3` negative theorem families (`reject_gotpcrel_illegal_opcode_mutations`, `reject_truncated_tls_sequences`, `reject_corrupted_eh_frame_hdr`) + live `SIGSEGV` runtime trap | Execution (Lean kernel + `nostd` trap) |
| **`V2` Differential Fuzzing** | Exhaustive differential probe across `2` linkers × `4` `std` modes (`8` builds, `6,108` FDEs checked) + `2 × 2` `#![no_std]` matrix + `30`-`.rlib` dual-toolchain census (`320,016` + `350,943` relocs); randomized property fuzzing: **not examined** | Execution (`probe_elf64_relaxation_lld_vs_ld.py`) |
| **`V3` Weak Memory / Leakage** | Single-thread sequential ELF relocation & unwinding semantics; multi-thread lazy TLS dynamic initialization races and microarchitectural side channels: **not examined** | Outside scope |
| **`V4` Held-Out Replay** | Verified on live `rustc 1.98.0-nightly`, `GNU ld 2.47`, `rust-lld 22.1.6`, and cross-checked `1.102.0-nightly` sysroot census; arbitrary crates.io whole-workspace replay & non-`x86_64` ISAs (`aarch64` `TLSDESC`/veneers): **unsupported / not examined** | Explicit scope boundary |

---

## Boundaries

`Basis: source + execution`

- **Non-x86-64 ISAs and `TLSDESC`:** `not examined`. All measurements and Lean models cover `x86_64-unknown-linux-gnu` ELF64 (`R_X86_64_*`). On this toolchain and target, neither `rustc` sysroot `.rlib`s nor default PIC/PIE compilation emit `R_X86_64_TLSDESC_CALL` (`-mtls-dialect=gnu` is the default). AArch64 relaxations and range-extension thunks/veneers are `unsupported` by this verifier.
- **LTO / ThinLTO / `R_X86_64_CODE_4_*` (APX) forms:** `not examined` in the live probe. Upstream `lld/ELF/Arch/X86_64.cpp` also recognizes `R_X86_64_CODE_4_GOTPCRELX` and `GOTTPOFF` APX/REX2 prefixes not exercised by our baseline x86-64-v1 `rustc` codegen.
- **`GNU ld` source-line citation:** `unknown` (line-by-line GNU Binutils `bfd/elf64-x86-64.c` source was not pinned to a 40-hex Binutils git commit; `GNU ld 2.47` behavior is reported strictly as empirical execution ground truth from binary output, flags, and `objdump`/`readelf`).
- **Lean kernel verifier scope vs. full ELF parser:** [Elf64PostLinkDifferentialCheck.lean](support/Elf64PostLinkDifferentialCheck.lean) mechanizes exact 32-bit signed LE codec soundness, local relocation instruction windows, differential GOT policy, and `.eh_frame_hdr` search-table/FDE validation on extracted byte windows and witness tables. A full in-kernel ELF64 program-header/DWARF CFA bytecode parser (`CIE`/`FDE` instruction execution during runtime unwinding) is `not examined` (`known not to apply` to pre-link reloc verification).
- **Host sysroot drift between `1.98.0-nightly` and `1.102.0-nightly`:** Live head-to-head linking probes ran on `rustc 1.98.0-nightly` (`14210df0e`); baseline `.rlib` counts from `1.102.0-nightly` (`3ef0c22cd`) show total `.rlib` relocations grew `320,016 -> 350,943` and `GOTTPOFF` in `librustc_public` grew `115 -> 196`, while preserving the identical `30` `.rlib`s, `10` relocation types, `6` relaxable crate stems, and `84` `libprofiler_builtins` `REX_GOTPCRELX` count.

---

## Evidence

`Basis: source + execution + normative + documentation`

1. **Primary Upstream Compiler Source (`Basis: source`):**
   - `rust-lang/rust@3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`1.102.0-nightly`): `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:8`, `compiler/rustc_target/src/spec/base/linux.rs:11,13`, `compiler/rustc_target/src/spec/base/linux_gnu.rs:6,13`, `compiler/rustc_target/src/spec/mod.rs:2315,2398,2547,2559,2755,2781,2835,2838`, `compiler/rustc_codegen_llvm/src/context.rs:280-282`, `compiler/rustc_codegen_llvm/src/back/write.rs:208-209`, `compiler/rustc_codegen_ssa/src/back/linker.rs:454,923-924`, `compiler/rustc_codegen_ssa/src/back/link.rs:2763-2767,4141`, `library/profiler_builtins/build.rs:24-46,103`.
   - `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`1.98.0-nightly`, live probe `rustc`): identical flags verified at `x86_64_unknown_linux_gnu.rs:8`, `linux.rs:11,13`, `linux_gnu.rs:9`, `spec/mod.rs:2406,2489,2633,2645,2837,2863,2916,2919`, `context.rs:279-280`, `back/write.rs:230-231,299`, `linker.rs:461,928-929`, `link.rs:2345,3610`, `profiler_builtins/build.rs:24-46,103`.
   - `rust-lang/llvm-project@08c84e69a84d95936296dfcab0e38b34100725d5` (`LLD 22.1.6` bundled in live `rust-lld`) and `llvm/llvm-project@fc4aad7b5db3fff421df9a9637605b9ca5667881` (`llvmorg-22.1.6`): `llvm/lib/Target/X86/MCTargetDesc/X86ELFObjectWriter.cpp:215-237`, `lld/ELF/Arch/X86_64.cpp:93,477-497,571-670,674-712,958-989,1072-1110`, `lld/ELF/SyntheticSections.cpp:580-669`.
   - `llvm/llvm-project@392dfff97d29b59d77e5cac6d4b6ef2585fe7117` (`llvmorg-23.1.5`): `llvm/lib/Target/X86/MCTargetDesc/X86ELFObjectWriter.cpp:215-237`, `lld/ELF/Arch/X86_64.cpp:99,781-801,870-971,973-1012,1257-1288,1371-1410`, `lld/ELF/SyntheticSections.cpp:372-490`.
   - `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) and `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`: `trusted/audit/TrustedBoundary.lean`.
2. **Normative ABI Specifications (`Basis: normative + documentation`):**
   - System V Application Binary Interface — AMD64 Architecture Processor Supplement (x86-64 psABI, H.J. Lu et al.): `R_X86_64_GOTPCREL`, `R_X86_64_GOTPCRELX`, `R_X86_64_REX_GOTPCRELX`, and GOT-to-`lea`/direct-`call` relaxation rules.
   - Ulrich Drepper, *"ELF Handling For Thread-Local Storage"* (`GD -> LE`, `LD -> LE`, `IE -> LE` x86-64 code transitions and `.tdata`/`.tbss` negative `TPOFF` layout).
   - Linux Standard Base (LSB) Core Specification, `.eh_frame_hdr` header encoding (`version = 1`, `DW_EH_PE_pcrel | DW_EH_PE_sdata4` = `0x1b`, `DW_EH_PE_udata4` = `0x03`, `DW_EH_PE_datarel | DW_EH_PE_sdata4` = `0x3b`).
3. **Live Execution Artifacts (`Basis: execution`, observed `2026-11-21`):**
   - Probe script: [probe_elf64_relaxation_lld_vs_ld.py](support/probe_elf64_relaxation_lld_vs_ld.py) (`32,392` B, SHA-256 `2fede709ab5e134469b76de05c7b4f7a384e263bbbcce766f1526aa67940bd8a`).
   - Full JSON trace (all `320,016` `1.98.0` / `350,943` `1.102.0` sysroot counts, `8` `std` configs, `6,108` `.eh_frame_hdr` FDE validations, and `4` `#![no_std]` binaries): [elf64_postlink_probe_results.json](support/elf64_postlink_probe_results.json) (`393,552` B, SHA-256 `a78c32f9cba4d7b27459632d1a945c7c2aeb7586cb9b33c5e4369b81f0838066`).
   - Lean `v4.34.1` formal verification artifact: [Elf64PostLinkDifferentialCheck.lean](support/Elf64PostLinkDifferentialCheck.lean) (`39,238` B, SHA-256 `960bd0cec17acc6c5e50926ed32f7388918e4ba5430e502c0953444d1b103e78`), kernel-checked via `lean -DElab.async=false -Ddebug.skipKernelTC=false` (`exit 0`, `4.721s`, `525.44 MiB` max RSS, `[propext]` / `[]` axioms only).

---

## Revalidation

`Basis: execution + source`

```bash
# 1. Re-run the live sysroot census, GNU ld vs. rust-lld head-to-head link matrix,
#    .eh_frame_hdr binary search table checks, and #![no_std] -static-pie SIGSEGV matrix:
python3 support/probe_elf64_relaxation_lld_vs_ld.py --out support/elf64_postlink_probe_results.json

# 2. Re-verify the Lean v4.34.1 differential checker synchronously through the Lean kernel:
lean -DElab.async=false -Ddebug.skipKernelTC=false support/Elf64PostLinkDifferentialCheck.lean

# 3. Verify upstream source pins cited in Evidence:
RUST_SHA="3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1"
curl --http1.1 -fsSL "https://raw.githubusercontent.com/rust-lang/rust/${RUST_SHA}/compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs" | grep -n "plt_by_default"
curl --http1.1 -fsSL "https://raw.githubusercontent.com/rust-lang/rust/${RUST_SHA}/compiler/rustc_codegen_llvm/src/back/write.rs" | grep -n "relax_elf_relocations"
LLVM_SHA="08c84e69a84d95936296dfcab0e38b34100725d5"
curl --http1.1 -fsSL "https://raw.githubusercontent.com/rust-lang/llvm-project/${LLVM_SHA}/lld/ELF/Arch/X86_64.cpp" | grep -nE "relaxTlsGdToLe|relaxTlsIeToLe|relaxTlsLdToLe|adjustGotPcExpr"

# 4. Re-run corpus validation from the repository root:
python3 tools/reference.py catalog && python3 tools/reference.py check && python3 -m unittest discover -s tests -v
```
