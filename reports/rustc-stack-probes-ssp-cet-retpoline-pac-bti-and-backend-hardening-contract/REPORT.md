# 2026 rustc Machine-Code Security Hardening and Inline Stack-Probe Contracts

## Summary

This report establishes the primary-source compiler implementation, empirical x86-64 and AArch64 machine-code output, and kernel-checked Lean `v4.34.1` soundness proofs for five low-level security hardening mechanisms in 2026 `rustc`: inline stack probes (`probe-stack="inline-asm"`), stack smash protection (`-Z stack-protector`), Intel Control-flow Enforcement Technology (`-Z cf-protection`), x86-64 Spectre v2 Retpoline (`-Z retpoline` / `-Z retpoline-external-thunk`), and AArch64 ARMv8.5-A BTI + Pointer Authentication (`-Z branch-protection`).

Seven load-bearing findings govern verified code generation and post-link binary attestation (`MiniMach` / Anneal trusted boundary):

1. **Shared `4,096 B` Inline Stack-Probe Guard Threshold, Divergent Unroll-to-Loop Cutoffs, and Two Silent Suppression Conditions (`LLVM` vs. `Cranelift`):** Both `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu` select `StackProbeType::Inline`, lowering in `rustc_codegen_llvm` to `"probe-stack"="inline-asm"` and in `rustc_codegen_cranelift` to `enable_probestack = true` + `probestack_strategy = "inline"` with `probestack_size_log2 = 12` (`4,096 B`). Both backends emit zero probes below `4,096 B` (`1,024 B`, `3,968 B`), unrolled `$0x1000` inline probes at `4,096..16,384 B`, inline loops at `65,536 B`, and zero `__rust_probestack` calls. However, their unroll-vs-loop cutoffs diverge by `2x`: Cranelift unrolls at most `4` pages (`PROBE_MAX_UNROLL = 4`, looping at `>= 20,480 B`, using 32-bit `movl $0x0, (%rsp)` and restoring `%rsp` via `add` before subtracting the frame), whereas LLVM unrolls up to `8` pages (`ProbeChunk = 8 * 4,096 = 32,768 B`, switching to a loop at total frame offset `> 32,768 B` — empirically pinned between `32,752 B` unrolled and `32,768 B` looped due to `16 B` prologue overhead — using monotonic 64-bit `movq $0x0, (%rsp)`). Critically, `rustc_codegen_llvm` silently omits `"probe-stack"` whenever `-Z sanitizer=address`, `-Z sanitizer=thread`, or `-C profile-generate` is active (`attributes.rs:370-377`).
2. **2026 `-Z stack-protector=basic` Removal and Partial-Mitigation Evolution:** Between `rustc 1.98.0-nightly` (`14210df0e`, `2026-05-31`) and `rustc 1.102.0-nightly` (`3ef0c22cd`, `2026-11-11`, which merged PR `#165812`), `StackProtector::Basic` was removed; `-Z stack-protector=basic` now fails with exit code `1` accepting only `none` (default), `strong`, or `all`. Concurrently, `DeniedPartialMitigationKind::StackProtector` (`#154613` / RFC 3855) transitioned from `EditionFuture` (opt-in error via `-Z deny-partial-mitigations=stack-protector`) to `Edition2015` (emitting the forward-compat `PARTIAL_STACK_PROTECTOR` crate warning by default whenever linking against unhardened `std`). Under `LLVM`, `strong` guards functions with stack arrays or address-taken stack slots (including `core::hint::black_box` stack spills) with `%fs:0x28` + `__stack_chk_fail` while leaving pure register-only scalar functions unguarded; `all` guards both.
3. **Intel CET (`-Z cf-protection=full`) Object Emission vs. Silent Link-Time Bitwise-AND Erasure:** Under `LLVM`, `-Z cf-protection=full` prefixes externally callable x86-64 functions with `endbr64` (`f3 0f 1e fa`) and emits `.note.gnu.property` `GNU_PROPERTY_X86_FEATURE_1_AND` carrying both `IBT` and `SHSTK` (`branch` emits `endbr64` + `IBT` only; `return` emits `SHSTK` only). Because `-Z cf-protection` is declared `[TRACKED]` without `TARGET_MODIFIER` or `MITIGATION` in `rustc_session/src/options.rs:2467`, linking a `-Z cf-protection=full` executable against stock unhardened `std` succeeds with `rc = 0` and zero warnings while the ELF linker bitwise-ANDs away both `IBT` and `SHSTK`, leaving the final binary with no `.note.gnu.property` CET protection.
4. **Retpoline (`-Z retpoline` / `-Z retpoline-external-thunk`) Target-Modifier Gating:** Under `LLVM`, `-Z retpoline` enables `+retpoline-indirect-branches` and `+retpoline-indirect-calls` and lowers indirect tail/non-tail calls to `jmp __llvm_retpoline_r11` (zero raw `call *%reg` / `jmp *%reg`). Because both `retpoline` and `retpoline_external_thunk` are `TARGET_MODIFIER` flags, linking against stock `std` fails unless `-C unsafe-allow-abi-mismatch=retpoline` is passed for `-Z retpoline`, or **both** `-C unsafe-allow-abi-mismatch=retpoline,retpoline-external-thunk` are passed for `-Z retpoline-external-thunk` (which lowers to `jmp __x86_indirect_thunk_r11`). Passing only `retpoline` or only `retpoline-external-thunk` fails with `rc = 1`.
5. **AArch64 `-Z branch-protection=bti,pac-ret,leaf` Dual Landing Pads and `br x16` Tail-Call Discipline:** Under `LLVM`, `-Z branch-protection=bti,pac-ret,leaf` emits `hint #25` (`paciasp`) at function entry, `hint #29` (`autiasp`) before return/tail-call, `.cfi_negate_ra_state` unwind annotations, and `.note.gnu.property` `AArch64 feature: BTI, PAC`. No separate `hint #34` (`bti c`) is emitted because ARMv8.5-A defines `paciasp` (and `pacibsp` / `hint #27` under `b-key`) as an implicit `BTI c` landing pad under `SCTLR_EL1.BT0/BT1 = 0`. However, because `paciasp` rejects `PSTATE.BTYPE = 0b11` (`br xN` for `n notin {16, 17}`), `LLVM` rewrites indirect tail calls from `br x2` to `br x16` (`BTYPE = 0b10`) and still emits explicit `hint #36` (`bti j`) at every indirect jump-table target block.
6. **Four-Flag Silent Fail-Open Gap in `rustc_codegen_cranelift`:** Exhaustive audit of all 45 `.rs` files in `compiler/rustc_codegen_cranelift/src/` at `3ef0c22cd` (and confirmed unchanged at `342d74463` HEAD and `rust-lang/rustc_codegen_cranelift@a69afc096`) establishes zero reads of `sanitizers()`, `stack_protector()`, `cf_protection`, `retpoline`, `retpoline_external_thunk`, or `branch_protection`. Empirical execution on `rustc 1.102.0-nightly` confirms that Cranelift compiles with `rc = 0` while silently dropping `-Z sanitizer=address`, `-Z stack-protector=all` (even while the backend-agnostic `rustc_metadata` frontend prints `#154613` partial-mitigation warnings!), `-Z cf-protection=full`, and `-Z retpoline` (emitting bare `call *%rsi`).
7. **Mechanized Lean `v4.34.1` Soundness & Post-Link Attestation Mandate:** `support/MachineHardeningAndStackProbeSoundness.lean` (`1,023` lines, `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`; axioms strictly subset of `[propext]`) proves guard-page catch safety for both LLVM and Cranelift inline probe sequences (`probed_frame_never_skips_guard_page`, `cranelift_probed_frame_never_skips_guard_page`), completeness and positive soundness of a fail-closed post-link binary hardening validator (`validator_catches_silent_backend_mitigation_drop`, `validateBinaryHardening_sound`, `cet_link_and_merge_drops_if_any_dep_unhardened`), ARMv8.5-A `paciasp` dual-landing-pad soundness (`paciasp_satisfies_both_pac_and_bti_c`), and three constructive counterexamples demonstrating why CLI flags and compiler exit status cannot be trusted without post-link machine-code verification.

## Applicability

This report characterizes machine-code security hardening and inline stack-probe contracts across nine pinned upstream subjects in `REPORT.json`, which stand in a **two-version comparison + backend/trusted-boundary interpretation** relationship:

- **Primary Compiler Comparison Pair (`rust-lang/rust`):**
  - `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`, bundled `LLVM 22.1.6`): directly executed live on `2026-11-22` via `support/probe_hardening_and_stack_probes.py` (producing `support/probe_results_rustc_1_98_live.json`) and inspected via its installed `rustc-src`.
  - `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`, bundled `LLVM 23.1.5` and `rustc_codegen_cranelift` / `cranelift-codegen 0.137.0`): inspected directly at full upstream source across all 45 `rustc_codegen_cranelift` `.rs` files plus `rustc_session`, `rustc_target`, `rustc_metadata`, and `rustc_codegen_llvm`, paired with the `2026-11-21` empirical LLVM-vs-Cranelift execution record preserved in `support/rustc_1_102_llvm_vs_cranelift_observations.json`.
  - `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`rust-lang/rust`, `2026-11-22`) and `rust-lang/rustc_codegen_cranelift@a69afc0967fddad0587b24fcd4c5534a5a7e60b9` (`2026-11-21`): source-diffed against `3ef0c22cd` to confirm continuity of the Cranelift fail-open gaps and `mitigation_coverage.rs` behavior.
- **Version-Shared vs. Version-Specific Behaviors:**
  - *Shared across `1.98.0-nightly` (`14210df0e`), `1.102.0-nightly` (`3ef0c22cd`), and `342d74463`:* `StackProbeType::Inline` on `x86_64-unknown-linux-gnu` and `aarch64-unknown-linux-gnu`, the `4,096 B` page threshold, LLVM's `8`-page (`32,768 B`) unroll cutoff vs. Cranelift's `4`-page (`16,384 B`) cutoff, LLVM's `probe-stack` suppression under ASan/TSan/`-C profile-generate`, `-Z stack-protector={none,strong,all}` `%fs:0x28` + `__stack_chk_fail` semantics, `-Z cf-protection={branch,return,full}` `endbr64` + `.note.gnu.property` lowering and absence of cross-crate target-modifier checks, `-Z retpoline` / `-Z retpoline-external-thunk` target-modifier enforcement and `__llvm_retpoline_r11` / `__x86_indirect_thunk_r11` thunks, AArch64 `-Z branch-protection` `hint #25`/`#29`/`#27`/`#31`/`#34`/`#36` + `br x16` lowering, and Cranelift's complete omission of all four security-hardening flags.
  - *Differs between `1.98.0-nightly` (`14210df0e`) and `1.102.0-nightly` (`3ef0c22cd`):*
    1. `-Z stack-protector=basic` is **accepted** on `14210df0e` (`attributes.rs:309`: `StackProtector::Basic => AttributeKind::StackProtect`) and **rejected with `rc = 1`** on `3ef0c22cd` (merged PR `#165812` in rollup `#165821`).
    2. `DeniedPartialMitigationKind::StackProtector` uses `EditionFuture` on `14210df0e` (`mitigation_coverage.rs:206`, silent unless `-Z deny-partial-mitigations=stack-protector` is passed, which hard-errors with `rc = 1`), whereas on `3ef0c22cd` (`mitigation_coverage.rs:204`, `creader.rs:564-567`) it uses `Edition2015` and emits the forward-compat `PARTIAL_STACK_PROTECTOR` warning referencing `#154613` by default on every edition.
- **Underlying Backend Implementations:** `llvm/llvm-project` at `392dfff97d29b59d77e5cac6d4b6ef2585fe7117` (`llvmorg-23.1.5`) and `fc4aad7b5db3fff421df9a9637605b9ca5667881` (`llvmorg-22.1.6`), plus `bytecodealliance/wasmtime` at `ebe5e8df1f4e12c5fc2f5954926881d8d61367d8` (`v50.0.0`, providing `cranelift-codegen 0.137.0`).
- **Verification & Trusted-Boundary Context:** `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613` (`trusted/audit/TrustedBoundary.lean`, `trusted/rustc-capture/src/driver.rs`, `trusted/lean/Trusted/MirSemantics.lean`) and `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`). Anneal's MIR capture verifies MIR-level semantics, leaving machine-code prologues, hardware CFI landing pads, retpoline thunks, and post-link `.note.gnu.property` preservation outside MIR and squarely inside the post-link binary attestation boundary (`MiniMach`).
- **Target Scope:** Directly examined targets are `x86_64-unknown-linux-gnu` (ELF, SysV AMD64 ABI, `-O` / `-C opt-level=3`, `--edition=2024`) and `aarch64-unknown-linux-gnu` (ELF, AAPCS64, `#![no_core]`, `-O`). Claims do **not** automatically extend to Windows (`x86_64-pc-windows-msvc` / `aarch64-pc-windows-msvc`, where Windows on Arm restricts PAC to Key B and Windows uses `__chkstk` / SEH), macOS Mach-O, or non-x86-64/AArch64 architectures except where specific target-spec source lines are cited.

## Findings

### 1. Inline Stack-Probe Contract (`probe-stack="inline-asm"`): LLVM vs. Cranelift

Basis: source + execution + derived

#### 1.1 Target Specification and Frontend-to-Backend Wiring

In `rust-lang/rust@3ef0c22cd`, both Tier-1 Linux targets configure inline stack probes unconditionally in their target specifications:

- `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:11`: `base.stack_probes = StackProbeType::Inline;`
- `compiler/rustc_target/src/spec/targets/aarch64_unknown_linux_gnu.rs:25`: `stack_probes: StackProbeType::Inline,`
- `compiler/rustc_target/src/spec/mod.rs:1118-1127`: defines `StackProbeType::{None, Inline, Call, InlineOrCall { min_llvm_version_for_inline }}` with default `StackProbeType::None` (`mod.rs:2814`).

The two codegen backends wire stack probes through completely distinct paths:

1. **`rustc_codegen_llvm` (`compiler/rustc_codegen_llvm/src/attributes.rs:366-397`, wired into every function at `attributes.rs:544`):**
   ```rust
   fn probestack_attr<'ll, 'tcx>(cx: &SimpleCx<'ll>, tcx: TyCtxt<'tcx>) -> Option<&'ll Attribute> {
       if tcx.sess.sanitizers().intersects(SanitizerSet::ADDRESS | SanitizerSet::THREAD) {
           return None;
       }
       if tcx.sess.opts.cg.profile_generate.enabled() {
           return None;
       }
       let attr_value = match tcx.sess.target.stack_probes {
           StackProbeType::None => return None,
           StackProbeType::Inline => "inline-asm",
           StackProbeType::Call => &mangle_internal_symbol(tcx, "__rust_probestack"),
           StackProbeType::InlineOrCall { min_llvm_version_for_inline } => { ... }
       };
       Some(llvm::CreateAttrStringValue(cx.llcx, "probe-stack", attr_value))
   }
   ```
   Two non-obvious suppression conditions directly verified in live `--emit=llvm-ir` execution (`support/probe_results_rustc_1_98_live.json`):
   - Default `-O` emits `"probe-stack"="inline-asm"` on every function (`llvm_ir_has_probe_stack_inline_asm = true`).
   - Passing **`-C profile-generate=<dir>`** silently strips `"probe-stack"` (`llvm_ir_profile_generate_retains_probe_stack = false`), leaving PGO-instrumented binaries without stack probes.
   - Passing **`-Z sanitizer=address`** (or `thread`) silently strips `"probe-stack"` (`llvm_ir_asan_retains_probe_stack = false`), relying on ASan's own stack instrumentation instead.

2. **`rustc_codegen_cranelift` (`compiler/rustc_codegen_cranelift/src/lib.rs:330-342`):**
   ```rust
   if let target_lexicon::Architecture::Aarch64(_)
   | target_lexicon::Architecture::Riscv64(_)
   | target_lexicon::Architecture::X86_64 = target_tuple.architecture
   {
       flags_builder.enable("enable_probestack").unwrap();
       flags_builder.set("probestack_strategy", "inline").unwrap();
   } else {
       flags_builder.set("enable_probestack", "false").unwrap();
   }
   ```
   Cranelift ignores `sess.target.stack_probes` altogether and keys inline probing solely on target architecture (`Aarch64`, `Riscv64`, `X86_64`). Cranelift's shared setting `probestack_size_log2` defaults to `12` (`1 << 12 = 4,096 B`) in `bytecodealliance/wasmtime@ebe5e8df` (`cranelift/codegen/meta/src/shared/settings.rs:262-272`).

#### 1.2 Exact Unroll-vs-Loop Cutoff and Machine-Code Lowering Differences

Source inspection of both backends explains every instruction observed in the empirical frame-size sweeps:

- **LLVM (`llvm/llvm-project@392dfff9`, `llvm/lib/Target/X86/X86FrameLowering.cpp:716-768, 821-862`):**
  - `StackProbeSize = TLI.getStackProbeSize(MF)` (`4,096 B` on Linux x86-64).
  - `ProbeChunk = StackProbeSize * 8` (`32,768 B` = `8` pages).
  - If `Offset <= 32,768`, `emitStackProbeInlineGenericBlock` unrolls `sub $0x1000, %rsp` + `movq $0x0, (%rsp)` (`X86::MOV64mi32`, 64-bit zero store) monotonically downward and finishes with `sub $(remainder), %rsp`.
  - If `Offset > 32,768`, `emitStackProbeInlineGenericLoop` sets `%r11 = %rsp - (pages * 0x1000)`, loops `sub $0x1000, %rsp; movq $0x0, (%rsp); cmp %r11, %rsp; jne <loop>`, and then subtracts the sub-page remainder (`sub $0x10, %rsp`).
- **Cranelift (`bytecodealliance/wasmtime@ebe5e8df`, `cranelift/codegen/src/isa/x64/abi.rs:27-68, 628-650` and `cranelift/codegen/src/isa/x64/inst/emit.rs:330-370`):**
  - `const PROBE_MAX_UNROLL: u32 = 4;` (`abi.rs:638`), chosen because the loop sequence is 38 bytes long and at most 4 unrolled probes fit in that code-size budget.
  - When `probe_count = frame_size / guard_size` satisfies `1 <= probe_count <= 4` (`4,096..16,384 B` payload, up to `< 20,480 B` frame), `gen_probestack_unroll` emits `probe_count` pairs of `sub $0x1000, %rsp` + `movl $0x0, (%rsp)` (32-bit `MOV32mi`), **restores `%rsp` with `add $(probe_count * 0x1000), %rsp`**, and then performs a single `sub $frame_size, %rsp` to allocate the frame.
  - When `probe_count > 4` (`>= 5` pages, `>= 20,480 B`), `gen_probestack_loop` emits `Inst::StackProbeLoop`, which computes `probe_count = align_to(frame_size, guard_size) / guard_size` (**rounding UP** in `emit.rs:341`, unlike unroll's floor division in `abi.rs:642`!). Thus for `frame_65536` (`frame_size = 0x10010`), Cranelift computes `align_to(0x10010, 0x1000) = 0x11000` (`17` pages = `69,632 B`), loops `sub $0x1000, %rsp; movl $0x0, (%rsp); cmp %rsp, %r11; jne`, restores `add $0x11000, %rsp`, and allocates `sub $0x10010, %rsp`.

#### 1.3 Empirical Stack-Probe Sweep Matrix (`LLVM 22.1.6`, `LLVM 23.1.5`, and `Cranelift 0.137.0`)

| Stack Array Size (B) | LLVM 22.1.6 (`1.98.0-nightly`, live `2026-11-22`) | LLVM 23.1.5 (`1.102.0-nightly`, `2026-11-21`) | Cranelift 0.137.0 (`1.102.0-nightly`, `2026-11-21`) | `__rust_probestack` Calls |
| ---: | :--- | :--- | :--- | ---: |
| `1,024` | `0` probes, unprobed (`sub $0x410`, 14 insns) | `0` probes, unprobed (`sub $0x410`, 15 insns) | `0` probes, unprobed (`sub $0x410`, 20 insns) | `0` |
| `3,968` | `0` probes, unprobed (`sub $0xf90`, 14 insns) | `0` probes, unprobed (`sub $0xf90`, 15 insns) | `0` probes, unprobed (`sub $0xf90`, 20 insns) | `0` |
| `4,096` | `1` unrolled `$0x1000` + `movq $0,(%rsp)` (16 insns) | `1` unrolled `$0x1000` + `movq $0,(%rsp)` (18 insns) | `1` unrolled `$0x1000` + `movl $0,(%rsp)` + `add $0x1000` + `sub $0x1010` (23 insns) | `0` |
| `4,097` | `1` unrolled `$0x1000` + `movq $0,(%rsp)` (16 insns) | `1` unrolled `$0x1000` + `movq $0,(%rsp)` (18 insns) | `1` unrolled `$0x1000` + `movl $0,(%rsp)` + `add $0x1000` + `sub $0x1020` (23 insns) | `0` |
| `8,192` | `2` unrolled `$0x1000` probes (18 insns) | `2` unrolled `$0x1000` probes (21 insns) | `2` unrolled `$0x1000` probes + `add $0x2000` + `sub $0x2010` (25 insns) | `0` |
| `16,384` | `4` unrolled `$0x1000` probes (22 insns) | `4` unrolled `$0x1000` probes (27 insns) | `4` unrolled `$0x1000` probes + `add $0x4000` + `sub $0x4010` (29 insns) | `0` |
| `20,480` | `5` unrolled `$0x1000` probes (24 insns) | *not in `1.102.0-nightly` 7-size sweep* | *not in `1.102.0-nightly` 7-size sweep* (source `abi.rs:638`: loops at `> 4` pages) | `0` |
| `32,752` | `8` unrolled `$0x1000` steps (`Offset = 0x8000 <= ProbeChunk`, 28 insns) | *not in `1.102.0-nightly` 7-size sweep* | *not in `1.102.0-nightly` 7-size sweep* | `0` |
| `32,768` | **Inline loop** (`sub $0x8000,%r11`, `Offset = 0x8010 > ProbeChunk`, 20 insns) | *not in `1.102.0-nightly` 7-size sweep* | *not in `1.102.0-nightly` 7-size sweep* | `0` |
| `36,864` | **Inline loop** (`sub $0x9000,%r11`, 20 insns) | *not in `1.102.0-nightly` 7-size sweep* | *not in `1.102.0-nightly` 7-size sweep* | `0` |
| `65,536` | **Inline loop** (`sub $0x10000,%r11`, `jne`, 20 insns) | **Inline loop** (`sub $0x10000,%r11`, `jne`, 22 insns) | **Inline loop** (`sub $0x11000,%r11`, `jne`, `add $0x11000`, `sub $0x10010`, 27 insns) | `0` |

Note the exact 16-byte transition pinned empirically on `LLVM 22.1.6` (`support/probe_results_rustc_1_98_live.json`): at array size `32,752 B` (`0x7ff0`), the `16 B` frame alignment/spill slot produces `Offset = 0x8000 = 32,768 B = ProbeChunk`, emitting `8` unrolled `subq $0x1000, %rsp` instructions; adding just `16 B` to `32,768 B` (`0x8000`) pushes `Offset = 0x8010 > 0x8000`, crossing `if (Offset > ProbeChunk)` into `emitStackProbeInlineGenericLoop`.

---

### 2. Stack Smash Protection (`-Z stack-protector`), `#165812`, and `#154613`

Basis: source + execution

#### 2.1 Removal of `-Z stack-protector=basic` (PR `#165812`)

In `rustc 1.98.0-nightly` (`14210df0e`), `StackProtector` had four variants (`None`, `Basic`, `Strong`, `All`) mapped in `compiler/rustc_codegen_llvm/src/attributes.rs:306-309` to `None`, `AttributeKind::StackProtect`, `AttributeKind::StackProtectStrong`, and `AttributeKind::StackProtectReq`. On `2026-11-11`, rollup `#165821` (`3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1`) merged **PR `#165812` (`Remove -Z stack-protector=basic`)**:

- `compiler/rustc_session/src/options.rs:948`:
  ```rust
  pub(crate) const parse_stack_protector: &str = "one of (`none` (default), `strong`, or `all`)";
  ```
- `compiler/rustc_codegen_llvm/src/attributes.rs:399-407`:
  ```rust
  fn stackprotector_attr<'ll>(cx: &SimpleCx<'ll>, sess: &Session) -> Option<&'ll Attribute> {
      let sspattr = match sess.stack_protector() {
          StackProtector::None => return None,
          StackProtector::All => AttributeKind::StackProtectReq,
          StackProtector::Strong => AttributeKind::StackProtectStrong,
      };
      Some(sspattr.create_attr(cx.llcx))
  }
  ```
- Executing `-Z stack-protector=basic` on `1.102.0-nightly` (`3ef0c22cd`) fails with `rc = 1` and exact stderr:
  ```text
  error: incorrect value `basic` for unstable option `stack-protector` - one of (`none` (default), `strong`, or `all`) was expected
  ```

#### 2.2 `strong` vs. `all` Coverage and the `black_box` Address-Taken Subtlety

On `x86_64-unknown-linux-gnu` (`glibc` TLS stack guard at `%fs:0x28`), `LLVM` enforces the following function-level coverage matrix (verified empirically on both `1.98.0-nightly` and `1.102.0-nightly`):

| Mode | `stack_buf` (`[u8; 64]` local array) | `scalar_only` (pure `u64` arithmetic) | `scalar_addr_taken` (`&mut x` / `black_box` spill) | LLVM IR Attribute |
| :--- | :---: | :---: | :---: | :--- |
| `none` | No (`%fs:0x28`: false, `__stack_chk_fail`: false) | No | No | *(none)* |
| `basic` (`1.98.0` only; `rc = 1` on `1.102.0`) | Yes (`%fs:0x28` + `__stack_chk_fail`) | No | Yes (`%fs:0x28` + `__stack_chk_fail`) | `ssp` |
| `strong` | **Yes** (`%fs:0x28` + `__stack_chk_fail`) | **No** | **Yes** (`%fs:0x28` + `__stack_chk_fail`) | `sspstrong` |
| `all` | **Yes** (`%fs:0x28` + `__stack_chk_fail`) | **Yes** (`%fs:0x28` + `__stack_chk_fail`) | **Yes** (`%fs:0x28` + `__stack_chk_fail`) | `sspreq` |

An empirical subtlety uncovered during live probe runs on `1.98.0-nightly`: wrapping a pure `u64` scalar expression inside `core::hint::black_box(...)` can lower to an `alloca` whose address is passed to an opaque inline-assembly barrier, causing LLVM's `StackProtectStrong` heuristic (which triggers on any address-taken stack local as well as local arrays) to emit `%fs:0x28` + `__stack_chk_fail` even on a scalar function. Separating `scalar_only` (pure register arithmetic `a.wrapping_mul(31).wrapping_add(b)`) from `scalar_addr_taken` cleanly discriminates `strong` from `all`.

#### 2.3 Cross-Crate Partial-Mitigation Enforcement (`#154613` / RFC 3855)

`compiler/rustc_session/src/options.rs:2949` annotates `stack_protector` with `{ MITIGATION: StackProtector }`, defined in `compiler/rustc_session/src/options/mitigation_coverage.rs:197-207`:

- On `14210df0e` (`1.98.0-nightly`, `mitigation_coverage.rs:206`): `(StackProtector, "stack-protector", EditionFuture, self.stack_protector())`. Linking against unhardened `std` succeeds silently (`rc = 0`, no warnings) unless `-Z deny-partial-mitigations=stack-protector` is explicitly passed, which fails with `rc = 1` (`error: your program uses the crate std, that is not compiled with stack-protector=all enabled`).
- On `3ef0c22cd` (`1.102.0-nightly`, `mitigation_coverage.rs:204`, identical at `342d74463`): `(StackProtector, "stack-protector", Edition2015, self.stack_protector())`, paired with `compiler/rustc_metadata/src/creader.rs:533-574`:
  ```rust
  if my_mitigation.kind == DeniedPartialMitigationKind::StackProtector {
      // make stack-protector only a forward-compat warning since it was
      // pretty widely used
      tcx.sess.psess.buffer_crate_lint(PARTIAL_STACK_PROTECTOR, diagnostic);
  } else {
      tcx.dcx().emit_err(diagnostic);
  }
  ```
  Consequently, compiling any `std`-linking crate with `-Z stack-protector={strong,all}` on `1.102.0-nightly` emits the `#154613` forward-compatibility warning naming `std` (and `core`/`alloc`), overrideable via `-Z allow-partial-mitigations=stack-protector` or promoted to a hard error via `-Z deny-partial-mitigations=stack-protector`. Crucially, because `CStore::report_incompatible_partial_mitigations` runs in `rustc_metadata` **before codegen backend dispatch**, it fires identically whether the backend is `LLVM` or `Cranelift`.

---

### 3. Intel CET (`-Z cf-protection`) and Link-Time `.note.gnu.property` Erasure

Basis: source + execution + derived

In `compiler/rustc_session/src/config.rs:90-102`, `CFProtection` takes four values: `None`, `Branch`, `Return`, and `Full`. `rustc_codegen_llvm` lowers these into LLVM module flags in `compiler/rustc_codegen_llvm/src/context.rs:452-468`:

- `Branch | Full` -> module flag `"cf-protection-branch" = 1` (`ModuleFlagMergeBehavior::Override`)
- `Return | Full` -> module flag `"cf-protection-return" = 1` (`ModuleFlagMergeBehavior::Override`)

Inside LLVM (`llvm/llvm-project@392dfff9`), two passes consume these flags:
- `llvm/lib/Target/X86/X86IndirectBranchTracking.cpp:56-65, 114-118`: inserts `endbr64` (`f3 0f 1e fa`) at the entry of every externally callable or address-taken function when `"cf-protection-branch"` is set.
- `llvm/lib/Target/X86/X86AsmPrinter.cpp:923-954`: emits an ELF `.note.gnu.property` (`NT_GNU_PROPERTY_TYPE_0`, `GNU_PROPERTY_X86_FEATURE_1_AND`) setting `GNU_PROPERTY_X86_FEATURE_1_IBT` (`0x1`) for `"cf-protection-branch"` and `GNU_PROPERTY_X86_FEATURE_1_SHSTK` (`0x2`) for `"cf-protection-return"`.

Live execution on `rustc 1.98.0-nightly` (`support/probe_results_rustc_1_98_live.json`) and `rustc 1.102.0-nightly` (`support/rustc_1_102_llvm_vs_cranelift_observations.json`) confirms exact object-file semantics:

| Flag | `indirect_call` First Instruction | `.o` `.note.gnu.property` `IBT` | `.o` `.note.gnu.property` `SHSTK` | Linked Executable (stock `std`) `IBT` / `SHSTK` |
| :--- | :--- | :---: | :---: | :---: |
| `-Z cf-protection=branch` | `endbr64` (`f3 0f 1e fa`) | **Yes** | No | *(not linked separately)* |
| `-Z cf-protection=return` | `movq %rdi, %rax` (no `endbr64`) | No | **Yes** | *(not linked separately)* |
| `-Z cf-protection=full` | `endbr64` (`f3 0f 1e fa`) | **Yes** | **Yes** | **No / No** (silently stripped by linker!) |

```asm
; indirect_call under -Z cf-protection=full (rustc 1.102.0-nightly, LLVM 23.1.5):
   0: f3 0f 1e fa    endbr64
   4: 48 89 f8       mov    %rdi,%rax
   7: 48 89 f7       mov    %rsi,%rdi
   a: ff e0          jmp    *%rax
```

**Critical Frontend & Link-Time Gap (Derived + Execution):** Unlike `stack_protector` (`MITIGATION`), `retpoline` (`TARGET_MODIFIER`), and `branch_protection` (`TARGET_MODIFIER`), `cf_protection` in `compiler/rustc_session/src/options.rs:2467` is marked **only `[TRACKED]`**:
```rust
cf_protection: CFProtection = (CFProtection::None, parse_cfprotection, [TRACKED],
    "instrument control-flow architecture protection"),
```
Because `rustc` performs **zero** cross-crate compatibility checking for `-Z cf-protection`, compiling a binary with `rustc -O -Z cf-protection=full` against stock unhardened `std` exits with `rc = 0` and zero warnings. Yet the ELF `GNU_PROPERTY_X86_FEATURE_1_AND` merge rule requires the linker to bitwise-AND the feature masks across every linked object; because `std` (and any unhardened C/Rust dependency) omits `IBT` and `SHSTK`, the linked executable loses `.note.gnu.property` CET markings completely (`linked_exe_retains_ibt = false`, `linked_exe_retains_shstk = false` in `support/probe_results_rustc_1_98_live.json`), causing the Linux kernel loader to disable hardware CET enforcement for the process silently. This bitwise-AND collapse is formalized in `cet_link_and_merge_drops_if_any_dep_unhardened` (`support/MachineHardeningAndStackProbeSoundness.lean:777`).

---

### 4. x86-64 Retpoline (`-Z retpoline` and `-Z retpoline-external-thunk`)

Basis: source + execution

In `compiler/rustc_codegen_ssa/src/target_features.rs:504-520` (called by `rustc_codegen_llvm/src/llvm_util.rs:680`):
- `-Z retpoline` (without `-Z retpoline-external-thunk`) adds `+retpoline-indirect-branches` and `+retpoline-indirect-calls`. LLVM's `X86IndirectThunks.cpp:45-46, 127-145` emits an internal COMDAT thunk `__llvm_retpoline_r11` (`callq .Lr11_call_target; .Lr11_capture_spec: pause; lfence; jmp .Lr11_capture_spec`) and rewrites indirect jumps/calls into `mov %rdi, %r11; ...; jmp __llvm_retpoline_r11` (relocation `R_X86_64_PLT32 __llvm_retpoline_r11-0x4`), leaving zero raw `call *%reg` or `jmp *%reg` instructions.
- `-Z retpoline-external-thunk` adds `+retpoline-external-thunk`, `+retpoline-indirect-branches`, and `+retpoline-indirect-calls`. LLVM lowers indirect calls to `R_X86_64_PLT32 __x86_indirect_thunk_r11-0x4` without emitting the thunk body (expecting the kernel or runtime linker to supply `__x86_indirect_thunk_r11`).

**Target-Modifier Cross-Crate Gate (Exact Diagnosis of the Two-Modifier Rule):** Both `retpoline` (`options.rs:2869`) and `retpoline_external_thunk` (`options.rs:2871`) carry `{ TARGET_MODIFIER: ... }` and are checked in `compiler/rustc_metadata/src/creader.rs:347-531`:
- Invoking `-Z retpoline` against stock `std` without override fails (`rc = 1`): `error: mixing -Zretpoline will cause an ABI mismatch`. Adding `-C unsafe-allow-abi-mismatch=retpoline` succeeds (`rc = 0`) and emits `jmp __llvm_retpoline_r11`.
- Invoking `-Z retpoline-external-thunk` implies `-Z retpoline=true` in the recorded target modifiers! Passing only `-C unsafe-allow-abi-mismatch=retpoline` fails (`rc = 1`, mismatch on `retpoline-external-thunk`, explaining the `rc = 1` result in `rustc_1_102_llvm_vs_cranelift_observations.json`), and passing only `-C unsafe-allow-abi-mismatch=retpoline-external-thunk` also fails (`rc = 1`, mismatch on `-Zretpoline=true`). Passing **both** (`-C unsafe-allow-abi-mismatch=retpoline,retpoline-external-thunk`) succeeds (`rc = 0`) and emits `R_X86_64_PLT32 __x86_indirect_thunk_r11-0x4` with zero raw indirect branches (`support/probe_results_rustc_1_98_live.json`).

---

### 5. AArch64 `-Z branch-protection` (BTI + PAC-RET + `leaf` + `b-key`)

Basis: normative + source + execution

In `compiler/rustc_session/src/options.rs:949, 2061-2085, 2461`, `-Z branch-protection` accepts a comma-separated combination of `bti`, `gcs`, `pac-ret` (with optional `pc`, `b-key`, `leaf` once `pac-ret` is set) and carries `{ TARGET_MODIFIER: BranchProtection }`. `rustc_codegen_llvm` lowers these both at module scope (`context.rs:401-446`: `branch-target-enforcement`, `sign-return-address`, `sign-return-address-all`, `sign-return-address-with-bkey`, `branch-protection-pauth-lr`, `guarded-control-stack`, all with `ModuleFlagMergeBehavior::Min`) and per non-naked function (`attributes.rs:579-602`: `"branch-target-enforcement"`, `"sign-return-address"="all"|"non-leaf"`, `"sign-return-address-key"="a_key"|"b_key"`).

#### 5.1 Dual PAC+BTI Landing Pad (`hint #25`) and Tail-Call `br x16` Register Discipline

In `llvm/llvm-project@392dfff9`, `llvm/lib/Target/AArch64/AArch64BranchTargets.cpp:117-121, 174-180` encodes two ARMv8.5-A architectural rules:

1. **Implicit `BTI c` Equivalence of `PACIASP`/`PACIBSP` (`AArch64BranchTargets.cpp:174-180`):**
   ```cpp
   // PACI[AB]SP are implicitly BTI c so insertion of a BTI can be skipped in
   // this case. Depending on the runtime value of SCTLR_EL1.BT[01], they are not
   // equivalent to a BTI jc, which still requires an additional BTI.
   if (MBBI != MBB.end() && ((HintNum & BTIMask) == BTIC) &&
       (MBBI->getOpcode() == AArch64::PACIASP ||
        MBBI->getOpcode() == AArch64::PACIBSP))
     return;
   ```
   Under default Linux/ELF `SCTLR_EL1.BT0/BT1 = 0`, `hint #25` (`paciasp`, Key A) and `hint #27` (`pacibsp`, Key B) serve simultaneously as return-address pointer signing instructions and as `BTI c` landing pads for `BLR` (`PSTATE.BTYPE = 0b01`) and `BR X16`/`BR X17` (`PSTATE.BTYPE = 0b10`). Crucially, because they are encoded in the ARMv8.0 `HINT` space, CPUs without PAC/BTI execute them as `NOP`s.
2. **Tail-Call Register Discipline (`br x16`) and Jump-Table `bti j` (`hint #36`):**
   On a BTI-guarded page (`GP = 1`), `BR Xn` for `n notin {16, 17}` sets `PSTATE.BTYPE = 0b11`, which **traps** if the target starts with `BTI c` or `PACIASP`/`PACIBSP`. Only `BR X16` (`IP0`) and `BR X17` (`IP1`) set `PSTATE.BTYPE = 0b10` (call-compatible). Consequently, when BTI is enabled, LLVM constrains indirect tail-call register allocation to `x16`/`x17`, while intra-function jump tables (`br x10`) still require explicit `hint #36` (`bti j`) at every switch-target basic block.

#### 5.2 Five-Configuration Empirical AArch64 Matrix (`aarch64-unknown-linux-gnu`, `#![no_core]`)

Measured live on `rustc 1.98.0-nightly` (`support/probe_results_rustc_1_98_live.json`) and cross-confirmed for `default` and `bti,pac-ret,leaf` on `rustc 1.102.0-nightly` (`support/rustc_1_102_llvm_vs_cranelift_observations.json`):

| `-Z branch-protection` | `arm_leaf` (no `x30` spill) | `arm_tailcall` (indirect tail call) | `arm_nonleaf_call` (spills `x30`) | `arm_jumptable` Targets | `.note.gnu.property` |
| :--- | :--- | :--- | :--- | :--- | :--- |
| *(default)* | `ret` | `mov x2,x0; mov x0,x1; br x2` | `stp x29,x30,...; ret` | `br x10` (no `bti`) | *(none)* |
| `bti` | `hint #34; ret` | `hint #34; mov x16,x0; mov x0,x1; br x16` | `hint #34; stp x29,x30,...` | Entry `hint #34`; targets `hint #36` (`bti j`) | `AArch64 feature: BTI` |
| `bti,pac-ret` | `hint #34; ret` (no PAC) | `hint #34; mov x16,x0; mov x0,x1; br x16` | `hint #25; stp ...; hint #29; ret` | Entry `hint #34`; targets `hint #36` | `AArch64 feature: BTI, PAC` |
| `bti,pac-ret,leaf` | `hint #25; hint #29; ret` | `hint #25; mov x16,x0; mov x0,x1; hint #29; br x16` | `hint #25; stp ...; hint #29; ret` | Entry `hint #25`; targets `hint #36; hint #29` | `AArch64 feature: BTI, PAC` |
| `bti,pac-ret,leaf,b-key` | `hint #27; hint #31; ret` | `hint #27; mov x16,x0; mov x0,x1; hint #31; br x16` | `hint #27; stp ...; hint #31; ret` | Entry `hint #27`; targets `hint #36; hint #31` | `AArch64 feature: BTI, PAC` |

Every `hint #25`/`#27` and `hint #29`/`#31` is paired with `.cfi_negate_ra_state` in DWARF CFI so unwinders know whether saved `x30` carries a PAC signature.

---

### 6. Four-Flag Silent Fail-Open Gap in `rustc_codegen_cranelift`

Basis: source + execution + derived

Exhaustive inspection of all `45` `.rs` source files under `compiler/rustc_codegen_cranelift/src/` at `rust-lang/rust@3ef0c22cd` (and verified unchanged against `rust-lang/rust@342d74463` and `rust-lang/rustc_codegen_cranelift@a69afc096`) establishes that `CraneliftCodegenBackend::init` (`lib.rs:131-162`) rejects only LTO (`-C lto`), `-C instrument-coverage`, and JIT-with-check. Across all 45 files, `rustc_codegen_cranelift` reads only **four** `unstable_opts` fields: `embed_source` (`debuginfo/mod.rs:76,87`), `function_sections` (`driver/aot.rs:62`), `force_intrinsic_fallback` (`intrinsics/mod.rs:280`), and `min_function_alignment` (`lib.rs:300`).

It contains **zero** references to `sess.sanitizers()`, `sess.stack_protector()`, `cf_protection`, `retpoline`, `retpoline_external_thunk`, or `branch_protection` (nor Cranelift's own AArch64 `sign_return_address` / `use_bti` settings).

#### 6.1 Empirical LLVM vs. Cranelift Hardening Matrix (`rustc 1.102.0-nightly`, `2026-11-21`)

| Security Hardening Flag | `LLVM 23.1.5` (`rc`, machine code, notes) | `Cranelift 0.137.0` (`rc`, machine code, notes) | Fail-Open Risk Mechanism |
| :--- | :--- | :--- | :--- |
| `-Z sanitizer=address` | `rc = 0`; `__asan_*` checks emitted (`1.98.0` live confirmed) | `rc = 0`; **0** `__asan_*` checks | `SanitizerSet::ADDRESS` is excluded from target-modifier mismatch (`options.rs:111`), and `cg_clif` never checks `sess.sanitizers()` |
| `-Z stack-protector=all` | `rc = 0`; `%fs:0x28` + `__stack_chk_fail` on both `stack_buf` & `scalar_only` | `rc = 0`; **emits `#154613` partial-mitigation warning for `std`**, yet emits **0** `%fs:0x28` and **0** `__stack_chk_fail` | Frontend `rustc_metadata/src/creader.rs:533-574` checks CLI flag vs. `std` metadata before backend dispatch, creating a **false-positive assurance trap** while `cg_clif` drops the flag |
| `-Z cf-protection=full` | `rc = 0`; `endbr64` entry + `.note.gnu.property` `IBT, SHSTK` | `rc = 0`; **0** `endbr64`, **0** `.note.gnu.property` `IBT`/`SHSTK`, bare `call *%rsi` | Neither frontend (`options.rs:2467`) nor `cg_clif` diagnoses or implements CET |
| `-Z retpoline` (`-C unsafe-allow-abi-mismatch=retpoline`) | `rc = 0`; `jmp __llvm_retpoline_r11`, **0** raw indirect branches | `rc = 0`; **0** retpoline thunks, emits bare `ff d6 call *%rsi` | Frontend enforces `TARGET_MODIFIER` (forcing user to pass `unsafe-allow-abi-mismatch=retpoline`), then `cg_clif` ignores `retpoline` completely |
| `-Z branch-protection=bti,pac-ret,leaf` *(derived from 45-file source audit)* | `rc = 0`; `hint #25`/`#29`, `br x16`, `.note.gnu.property` `BTI, PAC` | `0` source references to `branch_protection` / `use_bti` / `sign_return_address` across all 45 `cg_clif` files | Derived fifth silent fail-open gap on AArch64 when compiling with Cranelift (not executed on AArch64 Cranelift binary; see Boundaries) |

Look closely at the exact `indirect_call` disassembly emitted by `rustc_codegen_cranelift` under `-Z stack-protector=all`, `-Z cf-protection=full`, and `-Z retpoline` (`support/rustc_1_102_llvm_vs_cranelift_observations.json`):
```asm
; Byte-for-byte identical under clif_ssp_all, clif_cet_full, AND clif_retpoline:
   0: 55             push   %rbp
   1: 48 89 e5       mov    %rsp,%rbp
   4: 48 89 f0       mov    %rsi,%rax
   7: 48 89 fe       mov    %rdi,%rsi
   a: 48 89 c7       mov    %rax,%rdi
   d: ff d6          call   *%rsi
   f: 48 89 ec       mov    %rbp,%rsp
```
Zero `endbr64`, zero `%fs:0x28` canary, zero `__llvm_retpoline_r11`, and an unprotected indirect `call *%rsi` — while returning `rc = 0` in every case.

#### 6.2 Architectural Consequence for Anneal & Post-Link Binary Attestation (`MiniMach`)

In `joshlf/anneal@c131b320eeeb26ef692e5afd5ec8db49ee518613`, `trusted/rustc-capture/src/driver.rs` attaches at `Callbacks::after_analysis` (strictly pre-codegen) and `trusted/audit/TrustedBoundary.lean` enforces tactic/axiom/origin isolation on MIR-level proofs (`Trusted.MirSemantics`). Neither MIR semantics nor CLI flag recording can detect:
1. A codegen backend silently dropping `-Z stack-protector`, `-Z cf-protection`, `-Z retpoline`, `-Z sanitizer=address`, or `-Z branch-protection`;
2. `rustc_codegen_llvm` silently suppressing `"probe-stack"="inline-asm"` when `-C profile-generate` is enabled; or
3. An ELF linker bitwise-ANDing away `.note.gnu.property` `IBT`/`SHSTK` (or `BTI`/`PAC`) when linking against an unhardened `std` or C archive.

Therefore, any verified Rust toolchain claiming machine-code security hardening **must** place a fail-closed post-link binary validator (`MiniMach` attestation gate) after final linking to verify machine instructions, relocations, and ELF `.note.gnu.property` sections directly against the requested `HardeningPolicy`.

---

### 7. Kernel-Checked Lean `v4.34.1` Formalization (`MachineHardeningAndStackProbeSoundness.lean`)

Basis: source + execution (Lean `v4.34.1` kernel-checked with `-DwarningAsError=true`)

`support/MachineHardeningAndStackProbeSoundness.lean` (`1,023` lines, `44,065` bytes, SHA-256 `d6226aa921af93a554bc7e66218bed73a2e06b4cc5927d135f3b2cfe2c099a65`) formalizes both stack-probe guard-page safety and post-link hardening attestation with **strict constructive discipline**: `0` `sorry`, `0` `Classical.choice`, `0` `omega`, `0` `bv_decide`, `0` `native_decide`, `0` `partial def`, `0` `._unsafe_rec`. Every proved theorem depends solely on `[propext]` (and `ce1` depends on zero axioms `[]`).

#### 7.1 Core Definitions

- **Stack Operational Semantics (`lines 64-139`):**
  - `StackOutcome := running sp | trapGuardPage faultAddr | corruptedBelowGuard badAddr`
  - `StackOp := subSp delta | addSp delta | probeAtSp | subAndProbe step | touchBottom`
  - `execStackOps (guardLo pageSize : Nat) : List StackOp -> StackOutcome -> StackOutcome` (structurally total on `List StackOp`)
  - `mkLlvmInlineProbeSeq frameSize pageSize` (`frameSize / pageSize` steps of `subAndProbe pageSize`, then `subSp (frameSize % pageSize)`, then `touchBottom`)
  - `mkCraneliftInlineProbeSeq frameSize pageSize` (`k = frameSize / pageSize` steps of `subAndProbe pageSize`, then `addSp (k * pageSize)`, then `subSp frameSize`, then `touchBottom`)
  - `touchesEveryPage sp0 frameSize pageSize touched`: for every guard-page base `guardLo` with `guardLo + pageSize <= sp0` and `sp0 - frameSize < guardLo`, there exists `a in touched` with `guardLo <= a < guardLo + pageSize`.
- **Binary Hardening Predicates (`lines 317-629`):**
  - `hasCanaryPrologueEpilogue fn`: checks `movFs28CanaryLoad`, `cmpFs28CanaryCheck`, and `callStackChkFail`
  - `hasEndbrEntryAndGnuProperty img cet`: checks `endbr64` first instruction on externally callable functions + `gnuNote.x86Ibt` / `gnuNote.x86Shstk`
  - `noRawIndirectBranch fn mode`: rejects `callIndirectRaw` / `jmpIndirectRaw` and requires `jmpRetpolineR11` (`internalThunk`) or `jmpExternalThunkR11` (`externalThunk`) on functions with indirect sites
  - `hasPacBtiEntry fn bp note`: checks `btiAccepts .bt0_default .b01_blr` + `.b10_br_x16_17` at entry, forbids `brOther` (`br xN`, `n notin {16, 17}`) under BTI, checks `pacSignsLr` at entry and `pacAuthsLr` in body when `leaf || spillsLinkReg`, and verifies `note.armBti` / `note.armPac`
  - `GnuPropertyNote.linkAndMerge a b`: exact ELF bitwise-AND merge (`a.x86Ibt && b.x86Ibt`, etc.)
  - `validateBinaryHardening pol img`: conjunction of all policy gates across `img.gnuNote` and every `fn in img.functions`.

#### 7.2 Proved Theorems and Constructive Counterexamples

| Declaration | Line | Statement Summary | `#print axioms` |
| :--- | ---: | :--- | :--- |
| `probed_frame_never_skips_guard_page` | 256 | For any `pageSize > 0` and `frameSize >= pageSize`, `touchesEveryPage` holds for `inlineProbeAddrs`, and executing `mkLlvmInlineProbeSeq` from any `sp0 >= guardLo + pageSize` with `sp0 - frameSize < guardLo` terminates strictly in `.trapGuardPage faultAddr` with `guardLo <= faultAddr < guardLo + pageSize`. | `[propext]` |
| `cranelift_probed_frame_never_skips_guard_page` | 292 | Companion operational theorem for `mkCraneliftInlineProbeSeq`: because probe writes precede the `add`/`sub` frame allocation, Cranelift's inline probes also trap strictly on the guard page. | `[propext]` |
| `paciasp_satisfies_both_pac_and_bti_c` | 490 | Under `SCTLR_EL1.BT0 = 0`, `paciasp` satisfies `pacSignsLr .keyA`, `btiAccepts .b01_blr`, and `btiAccepts .b10_br_x16_17`, while rejecting `.b11_br_other` (necessitating `br x16` and `bti j`) and rejecting `.b10_br_x16_17` under strict `BT = 1`. | `[propext]` |
| `validator_catches_silent_backend_mitigation_drop` | 650 | For any `HardeningPolicy` with an active obligation (`PolicyHasActiveObligation pol img`) and any unhardened backend image (`IsUnhardenedImage img`, regardless of `exitCode = 0` or frontend warnings), `validateBinaryHardening pol img = false`. | `[propext]` |
| `cet_link_and_merge_drops_if_any_dep_unhardened` | 777 | Linking any local CET-full `.note.gnu.property` with a dependency lacking `x86Ibt`/`x86Shstk` produces `hasEndbrEntryAndGnuProperty linkedImg .full = false`. | `[propext]` |
| `validateBinaryHardening_sound` | 933 | Positive soundness: `validateBinaryHardening pol img = true` implies every requested CET, SSP, Retpoline, ASan, and AArch64 PAC+BTI invariant holds on every function in `img`. | `[propext]` |
| `ce1_unprobed_8kb_frame_skips_4kb_guard_page` | 801 | Constructive counterexample: with `guard = [4096, 8192)`, `sp0 = 8192`, `frameSize = 8192`, unprobed `mkUnprobedSeq 8192` reaches `.corruptedBelowGuard 0`, whereas both LLVM and Cranelift inline probe sequences hit `.trapGuardPage 4096`. | `[]` *(0 axioms)* |
| `ce2_cranelift_silent_drop_of_ssp_cet_retpoline_passes_frontend_fails_binary_validator` | 861 | Constructive counterexample: `craneliftSilentDropImage` has `exitCode = 0` (`frontendAccepted = true`) and carries a `#154613` warning, yet fails `validateBinaryHardening` for ASan, SSP-all, CET-full, Retpoline individually and jointly. | `[propext]` |
| `ce3_raw_indirect_call_violates_retpoline_policy` | 910 | Constructive counterexample: bare `call *%rsi` (`callIndirectRaw`) fails `noRawIndirectBranch` under both internal and external thunk modes and fails `validateBinaryHardening polRetpolineOnly`, while LLVM's `jmpRetpolineR11` passes (`= true`). | `[propext]` |
| `llvm_full_hardened_passes_validator` | 1018 | Non-vacuity witness: both a fully hardened x86-64 LLVM image (`polAllFourFlags`) and an AArch64 `bti,pac-ret,leaf` LLVM image satisfy `validateBinaryHardening = true`. | `[propext]` |

## Boundaries

To prevent over-generalization, negative space is explicitly categorized below:

- **Not examined:**
  - **Runtime execution of guard-page `SIGSEGV` faults or hardware CET/PAC/BTI traps on silicon:** All x86-64 and AArch64 empirical checks inspect compiled LLVM IR, ELF `.o`/executable disassembly, relocations, and `.note.gnu.property` sections; no process was intentionally faulted on CET Shadow Stack / IBT silicon or physical Armv8.5-A PAC/BTI hardware.
  - **Cranelift live execution on `1.98.0-nightly` and AArch64 Cranelift execution:** The local `1.98.0-nightly` (`14210df0e`) sysroot does not bundle the `rustc_codegen_cranelift` component (`cranelift_available: false` in `support/probe_results_rustc_1_98_live.json`). Cranelift x86-64 empirical execution is grounded in the `2026-11-21` `rustc 1.102.0-nightly` (`3ef0c22cd`) dataset (`support/rustc_1_102_llvm_vs_cranelift_observations.json`); Cranelift's AArch64 `-Z branch-protection` drop is **derived** from exhaustive 45-file source inspection (`0` hits) rather than AArch64 Cranelift binary execution.
  - **Other backends (`rustc_codegen_gcc`), Windows PE/SEH (`__chkstk`, Control Flow Guard `/guard:cf`, Windows on Arm Key B), macOS Mach-O (`arm64e`), and `-Z branch-protection=gcs` / `pc` (`FEAT_PAuth_LR`):** Source hooks for `gcs` and `pc` were observed in `rustc_codegen_llvm/src/context.rs:420-443` and `attributes.rs:584-590`, and `ControlFlowGuard` was observed in `mitigation_coverage.rs:205`, but none of these targets or sub-options were empirically executed.
  - **Dynamic `alloca` / variable-length stack allocations and `#[inline(never)]` assembly stubs (`asm!` / `global_asm!`):** The Lean stack-probe proof covers static constant-size frames (`frameSize : Nat`) and does not model inline assembly manually decrementing `%rsp` or variable-sized `alloca` loops.
  - **Instruction-byte decoding completeness in `MachineHardeningAndStackProbeSoundness.lean`:** The Lean formalization operates over typed abstract instruction streams (`List X86Insn`, `List AArch64Insn`) and structured `GnuPropertyNote` records rather than raw x86-64/AArch64 byte decoders or ELF binary parsers, and is standalone (not yet imported into `joshlf/anneal`'s `Trusted.MirSemantics`).
- **Unknown:**
  - **Exact runtime behavior of `SCTLR_EL1.BT0 = 1` / `BT1 = 1` kernels with `rustc` `-Z branch-protection=bti,pac-ret,leaf`:** Source inspection (`AArch64BranchTargets.cpp:175`) explicitly flags that `paciasp` is not equivalent to `BTI c` for `BR X16`/`BR X17` under `BT0/BT1 = 1`, which our Lean theorem captures (`btiAccepts .bt1_strict .b10_br_x16_17 .paciasp = false`), but whether any Linux distribution enables `SCTLR_EL1.BT0 = 1` in userspace was not investigated.
  - **Timeline for stabilizing `-Z stack-protector` or promoting `PARTIAL_STACK_PROTECTOR` (`#154613`) from warning to hard error:** The compiler diagnostic states it "will become a hard error in a future release," but no specific release date is established.
- **Known not to apply:**
  - **`-Z stack-protector=basic` on `rustc >= 1.102.0-nightly` (`3ef0c22cd`, `2026-11-11`+):** Known removed by PR `#165812`; claims or scripts relying on `-Z stack-protector=basic` do not apply post-`3ef0c22cd`.
  - **LLVM's `8`-page (`32,768 B`) unroll cutoff does NOT apply to Cranelift:** Cranelift's cutoff is `4` pages (`PROBE_MAX_UNROLL = 4`, `abi.rs:638`), and Cranelift's loop rounds `probe_count` **up** via `align_to` (`emit.rs:341`), whereas LLVM keeps monotonic `%rsp` descent and probes only whole `4,096 B` steps.
  - **Stack-probe presence under `-C profile-generate` or `-Z sanitizer=address` / `thread`:** Known not to hold under `rustc_codegen_llvm` (`attributes.rs:370-377`), verified empirically via `--emit=llvm-ir`.
  - **Object-level `.note.gnu.property` CET survival across linking with unhardened `std`:** Known not to survive link-time `GNU_PROPERTY_X86_FEATURE_1_AND` merging (`linked_exe_retains_ibt = false`, `linked_exe_retains_shstk = false`).
  - **Single target-modifier override for `-Z retpoline-external-thunk`:** Passing only `-C unsafe-allow-abi-mismatch=retpoline-external-thunk` (or only `retpoline`) is known to fail (`rc = 1`); both modifiers must be listed together.
  - **Frontend `#154613` diagnostics as evidence of emitted stack canaries:** Known not to guarantee codegen enforcement because `CStore::report_incompatible_partial_mitigations` runs independently of `rustc_codegen_cranelift`.
- **Unsupported:**
  - **`rustc_codegen_cranelift` support for `-Z sanitizer=address`, `-Z stack-protector`, `-Z cf-protection`, `-Z retpoline`, `-Z retpoline-external-thunk`, and `-Z branch-protection`:** None are implemented in `rustc_codegen_cranelift` (`3ef0c22cd` through `342d74463`), and unlike LTO (`-C lto`) or `-C instrument-coverage` (which fail closed with `sess.dcx().fatal` in `lib.rs:134-144`), these security flags are silently ignored with `rc = 0`.
  - **Inline stack probes in `rustc_codegen_cranelift` on architectures outside `{x86_64, aarch64, riscv64}`:** Explicitly disabled (`enable_probestack = false`) in `compiler/rustc_codegen_cranelift/src/lib.rs:338-342` because `__cranelift_probestack` is not provided.

## Evidence

### Primary Git Source Citations (All Commit SHAs Resolved Live via GitHub API on `2026-11-22`)

1. **`rust-lang/rust` @ `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`rustc 1.102.0-nightly`, `2026-11-11`, rollup `#165821` merging `#165812`):**
   - `compiler/rustc_target/src/spec/targets/x86_64_unknown_linux_gnu.rs:11` (`base.stack_probes = StackProbeType::Inline;`)
   - `compiler/rustc_target/src/spec/targets/aarch64_unknown_linux_gnu.rs:25` (`stack_probes: StackProbeType::Inline,`)
   - `compiler/rustc_target/src/spec/mod.rs:1118-1155, 2448, 2814` (`StackProbeType` enum and default)
   - `compiler/rustc_codegen_llvm/src/attributes.rs:366-407, 544-545, 579-602` (`probestack_attr` with ASan/TSan and `profile_generate` suppression; `stackprotector_attr` with only `None`/`All`/`Strong`; AArch64 `branch_protection` function attributes)
   - `compiler/rustc_codegen_llvm/src/context.rs:401-468` (AArch64 `branch-protection` module flags with `Min` merge; x86 `cf-protection-branch` and `cf-protection-return` with `Override` merge)
   - `compiler/rustc_codegen_llvm/src/llvm_util.rs:680-681` and `compiler/rustc_codegen_ssa/src/target_features.rs:504-527` (`retpoline_features_by_flags`, `sanitizer_features_by_flags`)
   - `compiler/rustc_session/src/options.rs:94-116, 948-949, 2053-2085, 2391-2392, 2418-2419, 2461, 2467, 2869-2876, 2948-2950` (option parsers, `TARGET_MODIFIER`, `MITIGATION`, absence of cross-crate check on `cf_protection`, exclusion of ASan/LSan from target-modifier mismatch)
   - `compiler/rustc_session/src/options/mitigation_coverage.rs:12-62, 197-241` (`DeniedPartialMitigationKind::StackProtector` at `Edition2015`, RFC 3855)
   - `compiler/rustc_metadata/src/creader.rs:347-387, 521-574` (`report_target_modifiers_extended`, `report_incompatible_partial_mitigations`, `PARTIAL_STACK_PROTECTOR` forward-compat lint)
   - `compiler/rustc_codegen_cranelift/src/lib.rs:131-162, 272-377` (`CraneliftCodegenBackend::init` fatal checks limited to LTO/coverage/JIT; `build_isa` inline probestack enablement; complete absence of SSP/CET/Retpoline/ASan/PAC/BTI handling across all 45 `.rs` files under `compiler/rustc_codegen_cranelift/src/`)
   - `compiler/rustc_codegen_cranelift/Cargo.toml:10-16` (`cranelift-codegen = "0.137.0"`)
2. **`rust-lang/rust` @ `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`rustc 1.98.0-nightly`, `2026-05-31`):**
   - `compiler/rustc_codegen_llvm/src/attributes.rs:306-309` (`StackProtector::Basic => AttributeKind::StackProtect` still present prior to `#165812`)
   - `compiler/rustc_session/src/options/mitigation_coverage.rs:206` (`(StackProtector, "stack-protector", EditionFuture, self.stack_protector())`)
3. **`rust-lang/rust` @ `342d74463af7dd3018ef6aa04dd5500c2deb5bd1` (`2026-11-22`) & `rust-lang/rustc_codegen_cranelift` @ `a69afc0967fddad0587b24fcd4c5534a5a7e60b9` (`2026-11-21`):**
   - Confirmed byte-for-byte identity of `mitigation_coverage.rs` vs. `3ef0c22cd`, and only non-hardening field renames (`replaced_intrinsics` -> `replaced_rustc_intrinsics`) in `compiler/rustc_codegen_cranelift/src/lib.rs`.
4. **`llvm/llvm-project` @ `392dfff97d29b59d77e5cac6d4b6ef2585fe7117` (`llvmorg-23.1.5`) & `fc4aad7b5db3fff421df9a9637605b9ca5667881` (`llvmorg-22.1.6`):**
   - `llvm/lib/Target/X86/X86FrameLowering.cpp:716-768, 821-862` (`ProbeChunk = StackProbeSize * 8 = 32,768`, `MOV64mi32` unrolled block vs. `%r11` loop)
   - `llvm/lib/Target/X86/X86IndirectBranchTracking.cpp:56-65, 114-118` (`ENDBR64` insertion)
   - `llvm/lib/Target/X86/X86AsmPrinter.cpp:923-954` (`.note.gnu.property` `GNU_PROPERTY_X86_FEATURE_1_AND` emission)
   - `llvm/lib/Target/X86/X86IndirectThunks.cpp:45-46, 127-145` (`__llvm_retpoline_r11` thunk body)
   - `llvm/lib/Target/AArch64/AArch64BranchTargets.cpp:114-196` (`BTI c`/`BTI j` insertion, `BR X16`/`X17` tail-call rule, `PACIASP`/`PACIBSP` implicit `BTI c` omission under `SCTLR_EL1.BT[01] = 0`)
5. **`bytecodealliance/wasmtime` @ `ebe5e8df1f4e12c5fc2f5954926881d8d61367d8` (`v50.0.0`, `cranelift-codegen 0.137.0`):**
   - `cranelift/codegen/meta/src/shared/settings.rs:255-284` (`enable_probestack`, `probestack_size_log2 = 12`, `probestack_strategy`)
   - `cranelift/codegen/src/isa/x64/abi.rs:27-68, 628-650` (`PROBE_MAX_UNROLL = 4`, floor `frame_size / guard_size`, `movl $0, (%rsp)`, `%rsp` restore via `add`)
   - `cranelift/codegen/src/isa/x64/inst/emit.rs:330-370` (`Inst::StackProbeLoop`, ceiling `align_to(frame_size, guard_size) / guard_size`, `%r11` loop, `add` restore)
6. **`joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` (`2026-11-19`) & `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`):**
   - `trusted/rustc-capture/src/driver.rs:75-84` (capture hook at `Callbacks::after_analysis`, strictly pre-codegen)
   - `trusted/audit/TrustedBoundary.lean:1-560` (tactic/attribute/origin isolation and kernel replay TCB contract pinned to Lean `v4.34.1`)

### Preserved Package Support Artifacts (`support/`)

| File | Observation Date | Size (B) | SHA-256 | Role |
| :--- | :---: | ---: | :--- | :--- |
| `support/probe_hardening_and_stack_probes.py` | `2026-11-22` | `28,451` | `906ba431d978fa96c9e73ef536dcb3aa739675731366a76a8d0a94566a0d81d3` | Standalone Python 3.10+ probe reproducing the 11-size x86-64 stack-probe sweep, IR suppression checks, SSP/CET/Retpoline/ASan/Cranelift matrix, CET link-time merge check, and 5-config AArch64 `#![no_core]` PAC+BTI matrix |
| `support/probe_results_rustc_1_98_live.json` | `2026-11-22` | `49,247` | `775dbdc207a40af4bf55d910eda661ddeb1d5d9a50c27923c9b88c1008ad05ac` | Scrubbed live execution record from `rustc 1.98.0-nightly (14210df0e 2026-05-31, LLVM 22.1.6)` + `aarch64-unknown-linux-gnu` (`llvm-objdump` + `readelf -n`) |
| `support/rustc_1_102_llvm_vs_cranelift_observations.json` | `2026-11-21` | `20,870` | `538d34cbc530dc5599a382397c39977c4cd1e565a0ad9c0e0654574ec3b2f7bc` | Scrubbed LLVM-vs-Cranelift execution record from `rustc 1.102.0-nightly (3ef0c22cd 2026-11-11, LLVM 23.1.5 + Cranelift 0.137.0)` + AArch64 `#![no_core]` |
| `support/MachineHardeningAndStackProbeSoundness.lean` | `2026-11-22` | `44,065` | `d6226aa921af93a554bc7e66218bed73a2e06b4cc5927d135f3b2cfe2c099a65` | Kernel-checked Lean `v4.34.1` formalization (`1,023` LOC, `10` proved theorems/counterexamples, `0` `sorry`/`Classical.choice`/`omega`/`bv_decide`/`native_decide`/`partial def`/`._unsafe_rec`, axioms subset of `[propext]`) |

## Revalidation

To cheaply revalidate these findings on a newer `rustc`, `LLVM`, `rustc_codegen_cranelift`, or `Lean` release without repeating the full audit:

1. **Re-run the empirical `rustc` probe** (takes ~5 seconds; automatically includes live Cranelift checks if the `rustc-codegen-cranelift-preview` component is installed in the target toolchain's sysroot, and AArch64 checks if the `aarch64-unknown-linux-gnu` target is installed):
   ```bash
   python3 support/probe_hardening_and_stack_probes.py --out /tmp/hardening_reval.json
   ```
   Key discriminating assertions to check in `/tmp/hardening_reval.json`:
   - `part_a_stack_probes.llvm_ir_has_probe_stack_inline_asm == true`, `frame_3968` unprobed, `frame_4096` probed, `frame_32752` unrolled (`8` steps) vs. `frame_32768` looped (`has_probe_loop_branch == true`), and whether `llvm_ir_profile_generate_retains_probe_stack` remains `false`.
   - `part_b_ssp_cet_retpoline_asan.llvm_ssp_basic.rc == 1` (confirming `#165812`), `llvm_ssp_strong` guards `stack_buf` & `scalar_addr_taken` but not `scalar_only`, `llvm_ssp_all` guards all three, `llvm_cet_full_linked_with_stock_std` still strips `IBT`/`SHSTK`, and `llvm_retpoline_external_thunk_both_overrides.has_external_thunk_symbol == true`.
   - When `cranelift_available == true`, check whether any of `clif_asan`, `clif_ssp_all`, `clif_cet_full`, or `clif_retpoline` now fails closed (`rc != 0`) or emits actual hardware protection.
   - `part_c_aarch64_pac_bti.configs.bti_pac_ret_leaf` still emits `hint #25`/`#29`, `br x16`, `hint #36` on jump-table targets, and `.note.gnu.property` `BTI, PAC`.

2. **Diff the narrow upstream decision points** against the pinned SHAs (`3ef0c22cd`, `392dfff9`, `ebe5e8df`):
   ```bash
   gh api repos/rust-lang/rust/commits/HEAD --jq .sha
   gh api repos/rust-lang/rustc_codegen_cranelift/commits/HEAD --jq .sha
   ```
   Inspect `compiler/rustc_codegen_cranelift/src/lib.rs` (for any new `sess.dcx().fatal(...)` guards or `settings::builder()` security flags), `compiler/rustc_session/src/options.rs` (for `cf_protection` gaining `TARGET_MODIFIER` or `MITIGATION`), `compiler/rustc_session/src/options/mitigation_coverage.rs` (for `#154613` promotion from lint to hard error), and `compiler/rustc_codegen_llvm/src/attributes.rs` (for `probestack_attr` suppression rules).

3. **Re-verify the Lean `v4.34.1` formalization and axiom footprint** (takes ~2 seconds):
   ```bash
   lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true \
     support/MachineHardeningAndStackProbeSoundness.lean
   ```
   Appending `#print axioms` on each of the 10 exported theorems in a temporary copy must report strictly `[]` or `[propext]` (zero `sorryAx`, zero `Classical.choice`, zero `Lean.ofReduceBool`). Note that a passing Lean check validates only the modeled operational semantics and validator properties; any real post-link `MiniMach` implementation still requires revalidating its machine-byte decoder and ELF parser against live `rustc` output.
