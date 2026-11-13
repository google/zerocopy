# Tier 1 Security Hardening and Mitigation Code Generation in `rustc` 1.99.1

## Summary

`rustc` 1.99.1 (`58cf8f9c35b355199727627d07ae34a4e2846d67`) divides binary
security mitigations across the 8 Tier 1 targets (`x86_64-unknown-linux-gnu`,
`i686-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `aarch64-apple-darwin`,
`x86_64-pc-windows-msvc`, `i686-pc-windows-msvc`, `aarch64-pc-windows-msvc`,
and `x86_64-pc-windows-gnu`) into **default-on baseline mitigations** and
**opt-in hardening flags**:

1. **Mitigations enabled by default across Tier 1**:
   - **Position-Independent Executables (PIE / ASLR)**: `position-independent-executables = true`
     and `relocation-model = "pic"` on all 8 Tier 1 targets; ELF links pass
     `-pie`, Mach-O sets `MH_PIE`, and Windows PE links pass `/DYNAMICBASE` +
     `/HIGHENTROPYVA` (on 64-bit) + `/NXCOMPAT` (`compiler/rustc_codegen_ssa/src/back/link.rs`).
   - **Full RELRO (`-Wl,-z,relro,-z,now`) and PLT elimination (`-Zplt=no`)**:
     All 3 Linux Tier 1 targets default to `relro-level = "full"`; all 3
     `x86_64` Tier 1 targets (`x86_64-unknown-linux-gnu`,
     `x86_64-pc-windows-msvc`, `x86_64-pc-windows-gnu`) set `plt-by-default =
     false`, emitting `NonLazyBind` and module flag `RtLibUseGOT = 1` so external
     calls use GOT-indirect `callq *sym@GOTPCREL(%rip)`.
   - **Non-executable stack (`PT_GNU_STACK` / `/NXCOMPAT`)**: Emitted via
     `.section .note.GNU-stack,"",@progbits` and linker flag `-Wl,-z,noexecstack`
     on all Linux targets and `/NXCOMPAT` on Windows targets.
   - **Stack clash probes (`probe-stack="inline-asm"` / `__chkstk`)**: Enabled by
     default on all 4 Unix Tier 1 targets (`stack-probes = {"kind": "inline"}` on
     Linux `x86_64`/`i686`/`aarch64` and `aarch64-apple-darwin`, emitting inline
     4096-byte page-touch loops for frames $\ge 4096$ bytes), while all 4 Windows
     Tier 1 targets use LLVM's built-in PE target `__chkstk` / `__chkstk_ms`
     prologue helper (`callq __chkstk` on frames $\ge 4096$ bytes).
   - **Windows 32-bit SafeSEH (`/SAFESEH`)**: Enabled on `i686-pc-windows-msvc`
     via `.safeseh _rust_eh_personality` directives in COFF objects and
     `/SAFESEH` at link time.
2. **Mitigations available on request (`-C` / `-Z` flags)**:
   - **Stack protectors (`-Zstack-protector=basic|strong|all`)**: Attaches LLVM
     `ssp`, `sspstrong`, or `sspreq` (`attributes.rs:371-380`), reading the TLS
     canary (`%fs:40` on x86_64 Linux) and branching to `callq __stack_chk_fail`
     on mismatch.
   - **Intel CET (`-Zcf-protection=branch|return|full`)**: Sets module flags
     `cf-protection-branch = 1` and `cf-protection-return = 1`
     (`context.rs:460-475`), emitting `endbr64` at indirect-call target entries
     and `.note.gnu.property` (`GNU_PROPERTY_X86_FEATURE_1_IBT | SHSTK`).
   - **AArch64 Branch Protection (`-Zbranch-protection=bti,pac-ret,leaf,pc,b-key,gcs`)**:
     Attaches function attributes (`branch-target-enforcement`,
     `sign-return-address="non-leaf"|"all"`, `sign-return-address-key="a_key"|"b_key"`,
     `branch-protection-pauth-lr`, `guarded-control-stack` in
     `attributes.rs:543-566`) and corresponding `Min`-merged module flags
     (`context.rs:408-457`), emitting `hint #34` (`bti c`), `hint #25`/`#27`
     (`paciasp`/`pacibsp`), `hint #29`/`#31` (`autiasp`/`autibsp`), and
     `hint #39` (`chkfeat x16` for GCS). **Checked by `rustc` as an ABI-affecting
     crate header flag** (mixing crates with and without `-Zbranch-protection` is
     rejected unless `-Cunsafe-allow-abi-mismatch=branch-protection` is passed).
   - **Spectre v2 Retpolines (`-Zretpoline`, `-Zretpoline-external-thunk`) and
     Return Thunks (`-Zfunction-return=thunk-extern`)**: Adds target features
     `+retpoline-indirect-calls,+retpoline-indirect-branches` (emitting COMDAT
     thunks `__llvm_retpoline_r11`) and `fn_ret_thunk_extern` (`jmp
     __x86_return_thunk`). **Also enforced as an ABI-mismatch error across crate
     boundaries** unless `-Cunsafe-allow-abi-mismatch=retpoline` is passed.
   - **Windows Control Flow Guard (`-Ccontrol-flow-guard=nochecks|checks`) and
     EH Continuation Guard (`-Zehcont-guard`)**: Sets module flags `cfguard = 1|2`
     and `ehcontguard = 1` (`context.rs:370-397, 487-489`), replacing indirect
     calls with `rex64 jmpq *__guard_dispatch_icall_fptr(%rip)` and emitting
     `.gfids$y` / `.giats$y` / `.gehcont$y` COFF tables plus `/GUARD:CF` /
     `/guard:ehcont` linker flags.

## Applicability

- **Primary baseline**: `rust-lang/rust` `1.99.1`
  (`58cf8f9c35b355199727627d07ae34a4e2846d67`) and `rust-lang/llvm-project`
  `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`), cross-checked against
  `1.100.0` (`0ef1bc386059596dada8fb65b50425aab2ea637a`) and
  `nightly-2026-11-12` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`).
- **Scope**: Default and opt-in security mitigations across all 8 Tier 1 targets,
  their lowering in `rustc_target`, `rustc_codegen_ssa`, and
  `rustc_codegen_llvm`, and backend implementation obligations for a drop-in
  verified compiler.

## Findings

### 1. Default Hardening Matrix Across All 8 Tier 1 Targets

`Basis: source + execution`

Extracted from `rustc +1.99.1 -Zunstable-options --print=target-spec-json` and
`compiler/rustc_codegen_ssa/src/back/link.rs`
(`support/v10_tier1_hardening_matrix.json`):

| Tier 1 Target | Default PIE / Reloc Model | Default RELRO (`relro-level`) | Default PLT (`plt-by-default`) | Default Stack Probes | Default Frame Pointer | Default NX Stack / ASLR Linker Flags |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `PIE` (`pic`, `PIE Level = 2`) | `full` (`-Wl,-z,relro,-z,now`) | `false` (`NonLazyBind` + `RtLibUseGOT=1`) | `inline` (`subq $4096, %rsp` probe loop) | `may-omit` | `.note.GNU-stack` + `-Wl,-z,noexecstack` + `-pie` |
| `i686-unknown-linux-gnu` | `PIE` (`pic`, `PIE Level = 2`) | `full` (`-Wl,-z,relro,-z,now`) | `true` | `inline` (4096B inline probe loop) | `may-omit` | `.note.GNU-stack` + `-Wl,-z,noexecstack` + `-pie` |
| `aarch64-unknown-linux-gnu` | `PIE` (`pic`, `PIE Level = 2`) | `full` (`-Wl,-z,relro,-z,now`) | `true` | `inline` (`sub sp, sp, #4096` probe loop) | `non-leaf` (`x29`/`x30` chain) | `.note.GNU-stack` + `-Wl,-z,noexecstack` + `-pie` |
| `aarch64-apple-darwin` | `PIE` (`pic`, `MH_PIE`) | `none` (Mach-O `__DATA_CONST` segment is read-only after dyld bind) | `true` | `inline` (`sub sp, sp, #4096` probe loop) | `non-leaf` (`x29`/`x30` chain) | Mach-O `MH_PIE` + non-executable `__DATA` by default |
| `x86_64-pc-windows-msvc` | `PIE` (`pic`) | `none` | `false` (`__imp_` IAT direct calls) | `none` in `TargetOptions` (**LLVM target emits `callq __chkstk` automatically for $\ge 4\text{ KiB}$**) | `may-omit` | `/NXCOMPAT` + `/DYNAMICBASE` + `/HIGHENTROPYVA` + `/DEFAULTLIB:msvcrt` |
| `i686-pc-windows-msvc` | `PIE` (`pic`) | `none` | `true` | `none` in `TargetOptions` (**LLVM emits `calll __chkstk`**) | `may-omit` | `/NXCOMPAT` + `/DYNAMICBASE` + `/SAFESEH` |
| `aarch64-pc-windows-msvc` | `PIE` (`pic`) | `none` | `true` | `none` in `TargetOptions` (**LLVM emits `bl __chkstk` for $\ge 4\text{ KiB}$**) | `non-leaf` | `/NXCOMPAT` + `/DYNAMICBASE` + `/HIGHENTROPYVA` |
| `x86_64-pc-windows-gnu` | `PIE` (`pic`) | `none` | `false` | `none` in `TargetOptions` (**LLVM emits `callq ___chkstk_ms`**) | `may-omit` | `--nxcompat` + `--dynamicbase` + `--high-entropy-va` |

**Subtle Windows stack-probe detail**: Although `rustc --print=target-spec-json`
reports `"stack-probes": {"kind": "none"}` on all four Windows Tier 1 targets,
LLVM's Windows x86/x86_64/AArch64 frame lowering unconditionally emits calls to
`__chkstk` (MSVC) or `___chkstk_ms` (MinGW) whenever a function's stack frame
exceeds the 4096-byte page guard (`empirical_assembly_probes` in
`support/v10_tier1_hardening_matrix.json`: `callq __chkstk; subq %rax, %rsp` on
`x86_64-pc-windows-msvc` and `calll __chkstk` on `i686-pc-windows-msvc`). Any
backend targeting Windows **must** emit `__chkstk` / `___chkstk_ms` calls on
frames $\ge 4096$ bytes, or stack allocations crossing the single-page Windows
guard page will trigger `STATUS_ACCESS_VIOLATION` instead of
`STATUS_STACK_OVERFLOW`!

---

### 2. Opt-In Hardening Mitigations, ABI-Mismatch Enforcement, and Empirical Assembly Verification

`Basis: source + execution`

We verified each opt-in mitigation by inspecting `compiler/rustc_codegen_llvm/src/{attributes.rs,context.rs,llvm_util.rs}`
and compiling `v10_probe.rs` (a function with a 4096-byte `[u8; 4096]` stack
buffer and an indirect function-pointer call `fptr(...)`) to assembly across the
Tier 1 targets (`support/v10_tier1_hardening_matrix.json`):

| Mitigation & CLI Flag | Target Scope | LLVM IR Lowering (`attributes.rs`, `context.rs`, `llvm_util.rs`) | Observed Machine Code & Object Artifacts (`support/v10_tier1_hardening_matrix.json`) | ABI-Mismatch Enforcement & Backend Cost |
| :--- | :--- | :--- | :--- | :--- |
| **Stack Protector (`-Zstack-protector=basic \| strong \| all`)** | All Tier 1 targets | Function attribute `ssp`, `sspstrong`, or `sspreq` (`attributes.rs:371-380`). | Reads stack canary (`movq %fs:40, %rax` on x86_64 Linux), stores at top of stack frame before local arrays, checks before `ret`, and calls `callq __stack_chk_fail@PLT` (`bl __stack_chk_fail` on AArch64) on mismatch. | Not ABI-breaking across crates. Requires frame layout ordering (arrays above canary) and target TLS/global canary access. |
| **Intel CET (`-Zcf-protection=branch \| return \| full`)** | `x86_64` / `i686` | Module flags `cf-protection-branch = 1` and `cf-protection-return = 1` (`context.rs:460-475`). `#[no_cf_check]` adds `nocf_check` (`AttributeKind::NoCfCheck`). | Inserts `endbr64` (4 bytes: `f3 0f 1e fa`) as the first instruction of every address-taken/exported function and emits `.note.gnu.property` with `GNU_PROPERTY_X86_FEATURE_1_IBT \| GNU_PROPERTY_X86_FEATURE_1_SHSTK`. | Not rejected by `rustc` ABI check, but hardware CET requires all linked objects to carry the `.note.gnu.property` bit for the OS loader to keep IBT/SHSTK active. |
| **AArch64 Branch Protection (`-Zbranch-protection=bti,pac-ret,leaf,pc,b-key,gcs`)** | `aarch64-*` | Function attributes `branch-target-enforcement`, `sign-return-address="non-leaf"\|"all"`, `sign-return-address-key="a_key"\|"b_key"`, `branch-protection-pauth-lr`, `guarded-control-stack` (`attributes.rs:543-566`) + 6 `Min`-merged module flags (`context.rs:408-457`). | Prologue emits `hint #34` (`bti c`), `hint #39` (GCS check), `hint #27` (`pacibsp`); epilogue emits `hint #31` (`autibsp`) before `ret`, plus `.note.gnu.property` (`GNU_PROPERTY_AARCH64_FEATURE_1_BTI \| PAC \| GCS`). | **Enforced by `rustc` as a crate ABI mismatch (`error: mixing -Zbranch-protection will cause an ABI mismatch`)** unless `-Cunsafe-allow-abi-mismatch=branch-protection` is passed. |
| **Spectre v2 Retpoline (`-Zretpoline`, `-Zretpoline-external-thunk`)** | `x86_64` / `i686` | Appends target features `+retpoline-indirect-calls,+retpoline-indirect-branches` (and `+retpoline-external-thunk`) in `llvm_util.rs`. | Replaces indirect `jmp *%r11` / `call *%r11` with `callq __llvm_retpoline_r11` and emits hidden weak COMDAT section `.text.__llvm_retpoline_r11` (`pause; lfence` capture loop). | **Enforced by `rustc` as a crate ABI mismatch (`error: mixing -Zretpoline will cause an ABI mismatch`)** unless `-Cunsafe-allow-abi-mismatch=retpoline` is passed. |
| **Spectre RSB / SLS Return Thunk (`-Zfunction-return=thunk-extern`)** | `x86_64` / `i686` | Function attribute `fn_ret_thunk_extern` (`AttributeKind::FnRetThunkExtern`, `attributes.rs:225-232`) + module flag `function_return_thunk_extern = 1` (`context.rs:491-501`). | Replaces `retq` with `jmp __x86_return_thunk` (for Linux kernel CONFIG_RETHUNK). | Requires external `__x86_return_thunk` symbol (used by Rust for Linux). |
| **Windows Control Flow Guard (`-Ccontrol-flow-guard=nochecks \| checks`)** | `*-pc-windows-msvc` (and `windows-gnu` with `llvm` ABI) | Module flag `cfguard = 1` (`nochecks`) or `cfguard = 2` (`checks`) (`context.rs:370-397`) + linker flag `/GUARD:CF` (`link.rs`). | Emits `.gfids$y` symbol-index table of address-taken functions; under `checks`, replaces indirect calls with `rex64 jmpq *__guard_dispatch_icall_fptr(%rip)` (or `callq *__guard_check_icall_fptr(%rip)`). | Under `nochecks` (`cfguard=1`), a backend only needs to emit `.gfids$y` address-taken function tables so MSVC `/GUARD:CF` binaries can call into Rust callbacks without failing the CFG bitmap check! |
| **Windows EH Continuation Guard (`-Zehcont-guard`)** | `x86_64-pc-windows-msvc` | Module flag `ehcontguard = 1` (`context.rs:487-489`) + linker flag `/guard:ehcont`. | Emits `.gehcont$y` section recording valid unwind landing-pad continuation RVA targets for Windows CET shadow-stack unwind validation. | Required only when linking with `/guard:ehcont`. |

---

### 3. Backend Implementation Costs and Normal-Compilation Scope

`Basis: derived + source + execution`

For a drop-in verified `rustc` backend targeting normal compilation (`cargo build`
/ `cargo test` with default flags):

1. **Mandatory for normal Tier 1 compilation (default-on)**:
   - **PIC/PIE code generation**: RIP/PC-relative addressing (`R_X86_64_PC32`,
     `R_X86_64_REX_GOTPCRELX`, `R_AARCH64_ADR_PREL_PG_HI21`,
     `ARM64_RELOC_PAGE21`) on all 8 Tier 1 targets.
   - **Stack clash probes on frames $\ge 4096$ bytes**: Inline 4096-byte probe
     loops on Linux (`x86_64`, `i686`, `aarch64`) and macOS (`aarch64`), and
     `__chkstk` / `___chkstk_ms` calls on all 4 Windows targets.
   - **Non-executable stack marker**: Emitting empty `.note.GNU-stack` section
     on ELF targets (`Cranelift` and `LLVM` both emit this; without it, GNU `ld`
     marks the entire stack `RWE`!).
   - **Non-leaf frame pointers (`x29`/`x30`) on all 3 `aarch64` Tier 1 targets**:
     `frame-pointer = "non-leaf"` is the default on `aarch64-unknown-linux-gnu`,
     `aarch64-apple-darwin`, and `aarch64-pc-windows-msvc`.
   - **32-bit Windows `.safeseh` directive**: Emitting `.safeseh
     _rust_eh_personality` on `i686-pc-windows-msvc` whenever an object defines
     or references an exception handler.
2. **Low-cost opt-in mitigations (trivial prologue/epilogue or section emission)**:
   - Intel CET IBT (`endbr64` at function entry + `.note.gnu.property`),
     AArch64 BTI/PAC-RET (`bti c`, `paciasp`/`autiasp` + `.note.gnu.property`),
     and Windows `-Ccontrol-flow-guard=nochecks` (`.gfids$y` symbol table).
3. **High-cost opt-in mitigations (require frame-layout or call-lowering changes)**:
   - Stack protectors (`-Zstack-protector`), retpolines (`-Zretpoline`), and
     checked CFG (`-Ccontrol-flow-guard=checks`).

## Boundaries

- **Sanitizer instrumentations (`-Zsanitizer=address|memory|thread|hwaddress|cfi|kcfi|memtag|safestack|realtime`)**:
  Scoped as diagnostic/sanitizer passes rather than normal production codegen;
  their per-target availability in `rustc` 1.99.1 is recorded in
  `support/v10_tier1_hardening_matrix.json` (`supported_sanitizers`).

## Evidence

- **Primary source citations (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`)**:
  - `compiler/rustc_codegen_llvm/src/attributes.rs:200-232, 338-380, 438-444, 543-566`
  - `compiler/rustc_codegen_llvm/src/context.rs:260-289, 370-524`
  - `compiler/rustc_codegen_llvm/src/llvm_util.rs` (retpoline target feature
    translation)
  - `compiler/rustc_codegen_ssa/src/back/link.rs` (RELRO, PIE, `/NXCOMPAT`,
    `/DYNAMICBASE`, `/HIGHENTROPYVA`, `/SAFESEH`, `/GUARD:CF`, `/guard:ehcont`).
- **Support artifacts**:
  - `support/v10_tier1_hardening_matrix.json`: Complete 8-target default
    hardening configuration matrix and empirical assembly verification excerpts.

## Revalidation

Run `rustc +1.99.1 -Zunstable-options --print=target-spec-json --target <triple>`
across all 8 Tier 1 targets and compile `v10_probe.rs` with `--emit=asm` to
verify that default and opt-in hardening instructions match
`support/v10_tier1_hardening_matrix.json`.
