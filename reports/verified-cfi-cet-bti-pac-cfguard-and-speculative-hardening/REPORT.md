# Mechanized Hardware Control-Flow Integrity (`CET`, `BTI`, `PAC-RET`, `GCS`, `CFGuard`, `EHCont`) and Speculative-Execution Hardening Across the 8 Tier 1 Targets

## Summary

Auditing `rustc 1.99.1` (`58cf8f9c35`) and LLVM `23.1.1` (`1b9c0d5ff9`) across all 8 Tier 1 targets (`support/verify_cfi_sections.py`, `support/cfi_hardening_obligations.json`) and mechanizing the hardware state machines and soundness theorems in Lean `4.34.1` (`support/VerifiedCfiAndHardening/VerifiedCfiAndHardening.lean`, `325` lines, `0` `sorry`, `0` `native_decide`) establishes the instruction, section, relocation, and operational-semantics obligations for hardware control-flow integrity and speculative-execution hardening in a verified `rustc` backend (`MiniMach`):

1. **Intel CET Indirect Branch Tracking (`IBT`) and Shadow Stack (`SHSTK`) on `x86_64` and `i686` (`-Zcf-protection=full`):**
   - `rustc 1.99.1` maps `-Zcf-protection={branch,return,full}` (`compiler/rustc_session/src/config.rs:1954-1968`, `compiler/rustc_codegen_llvm/src/attributes.rs:514-525`) to LLVM module flags `"cf-protection-branch" = 1` and `"cf-protection-return" = 1`.
   - On `x86_64-unknown-linux-gnu`, LLVM emits 4-byte `endbr64` (`f3 0f 1e fa`) at every indirect call/jump entry and `extern "C-unwind"` landing pad (`5` `endbr64` instructions in `support/verify_cfi_sections.py`), while on `i686-unknown-linux-gnu` it emits `endbr32` (`f3 0f 1e fb`). Both targets emit `.note.gnu.property` (`NT_GNU_PROPERTY_TYPE_0`) setting `GNU_PROPERTY_X86_FEATURE_1_IBT` (`0x1`) and `GNU_PROPERTY_X86_FEATURE_1_SHSTK` (`0x2`).
   - In `VerifiedCfiAndHardening.lean`, `cet_missing_endbr_faults` proves that omitting `endbr64` after an indirect call/jump immediately raises `#CP` (`cetFault_MissingEndbranch`) when `cetTracker = .waitForEndbranch`, while `cet_ibt_shstk_call_return_sound` proves that emitting `endbr64` at entry and preserving the top-of-stack return word against the parallel `shadowStack` guarantees fault-free execution across the call/return cycle.
2. **AArch64 `BTI`, `PAC-RET` (`PACIASP`/`AUTIASP`/`RETAA`/`PACIBSP`), and `GCS` (`-Zbranch-protection=bti,pac-ret,leaf,gcs`):**
   - `compiler/rustc_session/src/config.rs:1895-1952` parses `-Zbranch-protection=bti,pac-ret,leaf,b-key,gcs` and emits LLVM module metadata `branch-target-enforcement`, `sign-return-address`, `sign-return-address-all`, `sign-return-address-with-bkey`, and `guarded-control-stack`.
   - Across the three AArch64 Tier 1 targets, `rustc 1.99.1` lowers `PAC-RET` + `BTI` with three distinct target-specific prologue/epilogue sequences:
     - **`aarch64-unknown-linux-gnu`:** Prologue emits `paciasp` (`0xd503233f`, `hint #25`, which also satisfies `PSTATE.BTYPE ∈ {01, 11}` as an implicit `BTI c` landing pad without a separate `bti c` instruction), and epilogue emits `autiasp` (`0xd50323bf`, `hint #29`) followed by `ret` (`0xd65f03c0`), plus `.note.gnu.property` (`GNU_PROPERTY_AARCH64_FEATURE_1_BTI | GNU_PROPERTY_AARCH64_FEATURE_1_PAC | GNU_PROPERTY_AARCH64_FEATURE_1_GCS`).
     - **`aarch64-apple-darwin`:** Prologue emits `paciasp` (`0xd503233f`), epilogue emits the combined Armv8.3-A `retaa` (`0xd65f0bff`) instruction, and jump-table targets emit `bti j` (`0xd503249f`, `hint #36`).
     - **`aarch64-pc-windows-msvc`:** Prologue emits B-key `pacibsp` (`0xd503237f`, `hint #27`).
   - Executing a freestanding `-Zbranch-protection=bti,pac-ret,leaf -Ctarget-feature=+bti,+paca,+pacg` binary under `qemu-aarch64 -cpu max` (`support/verify_cfi_sections.py`) executes `paciasp` (`0xd503233f`) $\to$ `blr x8` (`0xd63f0100`) $\to$ `retaa` (`0xd65f0bff`) and exits with code `0`.
   - In `VerifiedCfiAndHardening.lean`, `aarch64_bti_c_rejects_jump_table_br` and `aarch64_bti_j_accepts_jump_table_br` prove the 2-bit `PSTATE.BTYPE` invariant (indirect `BR x8` jump tables set `BTYPE = 2` (`b10_jmp`), which faults on `BTI c` / `PACIASP` and requires `BTI j` or `BTI jc`), while `aarch64_pac_ret_and_gcs_sound` and `aarch64_pac_ret_detects_unbalanced_sp` prove that `PACIASP`/`AUTIASP` requires exact stack-pointer restoration (`sp_aut == sp_pac`) before `RET`.
3. **Windows Control Flow Guard (`-Ccontrol-flow-guard`) and EH Continuation Guard (`-Zehcont-guard`):**
   - On `x86_64-pc-windows-msvc`, `i686-pc-windows-msvc`, and `aarch64-pc-windows-msvc`, `-Ccontrol-flow-guard=checks` routes indirect calls through `*__guard_dispatch_icall_fptr(%rip)` (or `__guard_check_icall_fptr`) and emits COFF symbol-index tables `.gfids$y` (`.symidx cfi_target_a`, `.symidx cfi_target_b`, `.symidx __CxxFrameHandler3`), `.giats$y`, and `.gljmp$y`.
   - On `x86_64-pc-windows-msvc` with `-Zehcont-guard`, LLVM sets `@feat.00 = 18432` (`0x4800` = `0x0800` `IMAGE_DLLCHARACTERISTICS_GUARD_CF` | `0x4000` `IMAGE_DLLCHARACTERISTICS_EX_CET_COMPAT_EH_CONTINUATION`), compared to `@feat.00 = 2049` (`0x0801` = `GUARD_CF | SAFESEH` with `.sxdata`) on `i686-pc-windows-msvc`, `@feat.00 = 2048` (`0x0800`) on `aarch64-pc-windows-msvc`, and `@feat.00 = 0` on `x86_64-pc-windows-gnu` (where LLVM's MinGW COFF backend omits `.gfids$y` and `__guard_dispatch_icall_fptr`).
4. **Spectre v2 Retpoline (`-Zretpoline`), Return Thunks (`-Zfunction-return=thunk-extern`), and Stack Smashing Protection (`-Zstack-protector=all`):**
   - On `x86_64-unknown-linux-gnu`, `-Zretpoline -Zfunction-return=thunk-extern -Zstack-protector=all` replaces indirect calls with `movq %rdi, %r11; callq __llvm_retpoline_r11`, emits the COMDAT thunk `__llvm_retpoline_r11` (`callq 0x10; pause; lfence; jmp 0x5; movq %r11, (%rsp); retq`), replaces function `retq` with `jmp __x86_return_thunk`, and brackets the frame with `%fs:0x28` (`40`) canary load/compare against `__stack_chk_fail`.
   - `retpoline_thunk_architectural_eq` in `VerifiedCfiAndHardening.lean` proves that `runRetpolineR11` is architecturally equivalent to a direct indirect branch `rip := r11` with net stack displacement `rsp - 8 + 8` while trapping speculative execution in the `pause; lfence; jmp` loop.

## Applicability

- **Extends:** `tier1-calling-conventions-fnabi-and-llvm-lowering`, `target-features-implications-detection-and-abi-effects`, `stack-probes-and-frame-layout-across-tier1`
- **Subjects Examined:**
  - `rust-lang/rust` `1.99.1` (`58cf8f9c35b355199727627d07ae34a4e2846d67`);
  - `rust-lang/llvm-project` `23.1.1` (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145`);
  - `leanprover/lean4` `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`);
  - `qemu-aarch64` (`11.1.2`) with `-cpu max` (`+bti,+paca,+pacg`).

## Findings

### 1. Cross-Target Hardware CFI and Speculative Hardening Matrix (`rustc 1.99.1`)

`Basis: execution (support/verify_cfi_sections.py, support/cfi_hardening_obligations.json)`

| Target Triple | Compiler Flags | Entry / Landing-Pad Instruction | Return / Indirect Call Sequence | Object Metadata Section / `@feat.00` |
| :--- | :--- | :--- | :--- | :--- |
| `x86_64-unknown-linux-gnu` | `-Zcf-protection=full` | `endbr64` (`f3 0f 1e fa`) at fn entry + landing pad | `retq` (`SHSTK` checked by CPU) | `.note.gnu.property`: `IBT \| SHSTK` (`0x3`) |
| `i686-unknown-linux-gnu` | `-Zcf-protection=full` | `endbr32` (`f3 0f 1e fb`) at fn entry + landing pad | `retl` (`SHSTK` checked by CPU) | `.note.gnu.property`: `IBT \| SHSTK` (`0x3`) |
| `aarch64-unknown-linux-gnu` | `-Zbranch-protection=bti,pac-ret,leaf,gcs` | `paciasp` (`d503233f`, `hint #25`) or `bti c` (`d503245f`) | `autiasp` (`d50323bf`) + `ret` (`d65f03c0`); `retaa` (`d65f0bff`) with `+paca` | `.note.gnu.property`: `BTI \| PAC \| GCS` |
| `aarch64-apple-darwin` | `-Zbranch-protection=bti,pac-ret,leaf,gcs` | `paciasp` (`d503233f`); `bti j` (`d503249f`) at jump tables | `retaa` (`d65f0bff`) | Mach-O `__TEXT,__text` (no ELF note) |
| `aarch64-pc-windows-msvc` | `-Zbranch-protection=bti,pac-ret,leaf,gcs` | `pacibsp` (`d503237f`, B-key) | `autibsp` / `retab` | COFF `.xdata` / `.pdata` |
| `x86_64-pc-windows-msvc` | `-Ccontrol-flow-guard=checks -Zehcont-guard` | Address-taken fn symbols in `.gfids$y` | `callq *__guard_dispatch_icall_fptr(%rip)` | `.gfids$y`, `.giats$y`, `.gljmp$y`, `@feat.00 = 18432` (`0x4800`) |
| `i686-pc-windows-msvc` | `-Ccontrol-flow-guard=checks` | Address-taken fn symbols in `.gfids$y`, handlers in `.sxdata` | `calll *___guard_check_icall_fptr` | `.gfids$y`, `.giats$y`, `.gljmp$y`, `.sxdata`, `@feat.00 = 2049` (`0x0801`) |
| `aarch64-pc-windows-msvc` | `-Ccontrol-flow-guard=checks` | Address-taken fn symbols in `.gfids$y` | `blr` via `__guard_check_icall_fptr` | `.gfids$y`, `.giats$y`, `.gljmp$y`, `@feat.00 = 2048` (`0x0800`) |
| `x86_64-pc-windows-gnu` | `-Ccontrol-flow-guard=checks` | None (MinGW COFF ignores CFGuard) | Direct `callq *%rdi` | `@feat.00 = 0` (no `.gfids$y` emitted) |
| `x86_64-unknown-linux-gnu` | `-Zretpoline -Zfunction-return=thunk-extern -Zstack-protector=all` | `movq %fs:0x28, %rax` stack canary | `movq %rdi, %r11; callq __llvm_retpoline_r11`; exit via `jmp __x86_return_thunk` | `.text.__llvm_retpoline_r11` COMDAT |

---

### 2. Lean 4.34.1 Mechanization of Hardware CFI and Retpoline Soundness

`Basis: execution (support/VerifiedCfiAndHardening/VerifiedCfiAndHardening.lean)`

| Theorem Name | Hardware Mechanism Modeled | Mechanized Statement Summary | Proof Status |
| :--- | :--- | :--- | :---: |
| `cet_missing_endbr_faults` | Intel CET `IBT` (`CetTracker.waitForEndbranch`) | Executing `.callIndirect target retAddr` followed by `.bodyOp nextRip` without `.endbr64` transitions to `.cetFault_MissingEndbranch` (`#CP`). | Proved (`0` `sorry`) |
| `cet_ibt_shstk_call_return_sound` | Intel CET `IBT` + `SHSTK` (`shadowStack`) | `.callIndirect target retAddr` $\to$ `.endbr64` $\to$ `.bodyOp` $\to$ `.retNear` clears `waitForEndbranch`, matches `stackTop` against `shadowStack`, and restores `rip = retAddr`. | Proved (`0` `sorry`) |
| `aarch64_bti_c_rejects_jump_table_br` | Armv8.5-A `BTI` (`BType.b10_jmp` vs `.btiC`) | An indirect jump-table branch (`.brJumpTable target`, which sets `PSTATE.BTYPE = 2`) faulting when landing on `.btiC` (`hint #34`). | Proved (`0` `sorry`) |
| `aarch64_bti_j_accepts_jump_table_br` | Armv8.5-A `BTI` (`BType.b10_jmp` vs `.btiJ`) | `.brJumpTable target` landing on `.btiJ` (`0xd503249f`, `hint #36`) clears `btype := .b00` and advances `pc`. | Proved (`0` `sorry`) |
| `aarch64_pac_ret_and_gcs_sound` | Armv8.3-A `PAC-RET` + Armv9.4-A `GCS` | `.blrIndirect` $\to$ `.paciasp` $\to$ `.subSp frame` $\to$ `.bodyInsn` $\to$ `.addSp frame` $\to$ `.autiasp` $\to$ `.ret` satisfies `BTI`, verifies `(lr, sp - frame + frame)` signature, and pops `gcsStack`. | Proved (`0` `sorry`) |
| `aarch64_pac_ret_detects_unbalanced_sp` | Armv8.3-A `PAC-RET` (`SP` modifier check) | Calling `.autiasp` when `sp != signedSp` (`st.sp - 32 != st.sp`) immediately yields `.pacAuthFault`. | Proved (`0` `sorry`) |
| `windows_cfguard_ehcont_sound` | Windows COFF `.gfids$y` and `.gehcont$y` | Populating `CoffCfgTables` with all address-taken function symbols and unwind landing pads guarantees `checkWindowsIcall = true ∧ checkWindowsEhCont = true`. | Proved (`0` `sorry`) |
| `retpoline_thunk_architectural_eq` | Spectre v2 `__llvm_retpoline_r11` | `runRetpolineR11` (`call set_up_target; mov %r11, (%rsp); retq`) yields identical architectural `(rip, r11, stack, rsp)` state to `runDirectJmpR11`. | Proved (`0` `sorry`) |

## Boundaries

- **Kernel-Mode `IBT`/`SHSTK` and Windows Kernel CFG Bitmaps (`not examined` live):** User-mode ELF `.note.gnu.property`, COFF `.gfids$y`/`.giats$y`/`@feat.00`, and `qemu-aarch64 -cpu max` `PAC-RET`+`BTI` execution were verified; OS kernel page-table enforcement of `SHSTK` (`WRSS`/`INCSSP`) and Windows loader `ntdll!LdrpValidateUserCallTarget` bitmaps depend on the host OS kernel.
- **Armv9.4-A Guarded Control Stack (`GCS`) Dynamic Loader Handshake (`partial`):** While `-Zbranch-protection=bti,pac-ret,leaf,gcs` sets the ELF `.note.gnu.property` `GNU_PROPERTY_AARCH64_FEATURE_1_GCS` bit, standard function prologues/epilogues rely on hardware `BLR`/`RET` GCS pushes/pops rather than explicit `CHKFEAT x16` (`hint #40`) instructions inside ordinary Rust functions.

## Evidence

- **Primary Upstream Sources (`rust-lang/rust` @ `58cf8f9c35b355199727627d07ae34a4e2846d67`):**
  - `compiler/rustc_session/src/config.rs:1895-1968` (`BranchProtection`, `PacRet`, `CFProtection` parsing for `-Zbranch-protection` and `-Zcf-protection`).
  - `compiler/rustc_codegen_llvm/src/attributes.rs:480-565` (lowering `-Zcf-protection`, `-Zbranch-protection`, `-Zretpoline`, `-Zfunction-return`, `-Ccontrol-flow-guard`, and `-Zstack-protector` to LLVM attributes and module flags).
- **Preserved Support Artifacts:**
  - [`support/verify_cfi_sections.py`](support/verify_cfi_sections.py): 8-target object/assembly inspector and `qemu-aarch64 -cpu max` live `BTI` + `PAC-RET` execution harness.
  - [`support/cfi_hardening_obligations.json`](support/cfi_hardening_obligations.json): Recorded disassembly, `.note.gnu.property` flags, COFF `.gfids$y`/`.giats$y`/`@feat.00` values, and `qemu-aarch64` results.
  - [`support/VerifiedCfiAndHardening/VerifiedCfiAndHardening.lean`](support/VerifiedCfiAndHardening/VerifiedCfiAndHardening.lean): Self-contained Lean `4.34.1` formalization and proofs.

## Revalidation

```bash
python3 reports/verified-cfi-cet-bti-pac-cfguard-and-speculative-hardening/support/verify_cfi_sections.py
cd reports/verified-cfi-cet-bti-pac-cfguard-and-speculative-hardening/support/VerifiedCfiAndHardening && anneal-lean-run --mode build --concurrency 4 -- lake build
```

Verify that `verify_cfi_sections.py` exits with `0` (including `qemu_aarch64_live_bti_pac_execution.passed == true`) and `lake build` completes with zero warnings and zero `sorry`s.
