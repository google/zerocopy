<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# In-Process `rustc_driver` Inline-Assembly Attestation Injection Across Multi-CGU Builds, ThinLTO/FatLTO `GlobalScopeAsm` & `--icf` Containment, and `TyCtxt`-Driven `SpecConeHash`

## Summary

Scaling self-attesting inline-assembly verification (`SiteAttestation`) and two-surface reference-function equivalence (`SpecConeHash`) from single-CGU toy harnesses to Cargo's default multi-CGU builds (`-C codegen-units=16`), cross-crate `.rlib`/`.rmeta` graphs, LLVM Link-Time Optimization (`-C lto=thin`, `-C lto=fat`), and `rust-lld` Identical Code Folding (`--icf=safe`, `--icf=all`) exposes three load-bearing compiler/linker seams and resolves each with executable `rustc_driver` and Lean `v4.34.1` evidence:

1. **In-Process `rustc_driver` `override_queries` Injection Eliminates `codegen-units=16` Macro Crashes, `${:uid}` CGU Collisions, `$` Escaping, and Cross-ISA `getInlineAsmLength` Drift (`Basis: source + execution + derived`):**
   - Under `-C codegen-units=16 -C lto=off`, `MonoItem::GlobalAsm` (`compiler/rustc_monomorphize/src/partitioning.rs:700, 816-818`) is placed in **only one CGU (`cgu.0`)**, causing any `global_asm!(".macro __aw ...")` wrapper to fail across the remaining `15` CGUs (`15` `invalid instruction mnemonic '__aw'` errors in `1.98.0-nightly`, `rc=1` across `1.98.0-nightly`..`1.102.0-nightly`) and in every downstream `.rmeta` consumer (`rc=1`). Meanwhile, voluntary source macros are trivially bypassed by raw `core::arch::asm!`, `rustc_codegen_llvm/src/asm.rs:189-199` escapes every `$` in MIR `InlineAsmTemplatePiece::String` to `$$` (neutralizing `${:uid}` at MIR level), and LLVM's `${:uid}` counter resets to `0` in every CGU's `AsmPrinter` (`["cgu=0:uid=0", "cgu=1:uid=0"]`).
   - Hooking `providers.queries.optimized_mir` (or `mir_built`) via `interface::Config::override_queries` inside a standalone `rustc_driver` ([`support/anneal_driver_prototype.rs`](support/anneal_driver_prototype.rs)) rewrites every `TerminatorKind::InlineAsm` **in memory after macro/proc-macro expansion and after the AST `AsmLabels` lint pass** (`compiler/rustc_lint/src/builtin.rs:2797-3035`, `0` `named_asm_labels` / `binary_asm_labels` warnings even under `#![deny(named_asm_labels, binary_asm_labels)]`).
   - Testing four wrapper encodings across `x86_64`, `aarch64` (`N = 5,000` `asm!` sites inside a `20,020 B < 32 KiB` `tbz` span), and `riscv64gc` (`N = 900` `asm!` sites inside an `1,812 B < 4 KiB` `beqz` span) reveals that **inline `.ifndef` macros still perturb `aarch64` (`+4 B`: `tbz w0, #0, +0x4e2c` $\to$ `tbnz + b`) and `riscv64gc` (`0 B` size change, but SHA-256 drift `b85f3f2cce282b77` $\to$ `2d26595a9ab21703` as `beqz a0` relaxes to `c.bnez + c.j`!)** because `TargetInstrInfo::getInlineAsmLength` (`llvm/lib/CodeGen/TargetInstrInfo.cpp:113-149`) counts every `\n` inside `.ifndef ... .endif`. Conversely, exploiting the exact lexical asymmetry between `TargetInstrInfo::getInlineAsmLength` (which resets `AtInsnStart` **only** on `\n` or `;`, treating `.space 0 <cmt>` as `AddLength = 0` and `AtInsnStart = false`) and `AsmLexer::LexToken` / `LexLineComment` (`llvm/lib/MC/MCParser/AsmLexer.cpp:313, 898-906`, which treats bare carriage return `\r` as `AsmToken::EndOfStatement`), combined with post-expansion CSPRNG template-disjoint directional labels (`cr_zero_drift`), achieves **zero `global_asm!`, zero `.macro`, `16/16` CGU + cross-crate `.rmeta` dual-nonce survival, and `100%` bit-for-bit `.text` SHA-256 identity across `x86_64`, `aarch64` (`5,000` sites), and `riscv64gc` (`900` sites)** across all three toolchains.

2. **ThinLTO vs. FatLTO Cross-Crate `GlobalScopeAsm` (`IRMover`) Asymmetry and `rust-lld` `--icf={none,safe,all}` Containment (`Basis: source + execution + derived`):**
   - Executing a 36-cell `{lto=off, lto=thin, lto=fat} × {cgu=1, cgu=16}` cross-crate directive and ICF matrix ([`support/probe_lto_global_asm_and_icf.py`](support/probe_lto_global_asm_and_icf.py)) establishes a sharp three-tier LTO boundary governed by `llvm/lib/Linker/IRMover.cpp:1563-1582` and `compiler/rustc_codegen_llvm/src/back/lto.rs:247-325`:
     * **`-C lto=off`:** Upstream `#[inline(never)]` and non-leaf (`calls > 0`) functions remain pre-assembled inside `libupstream.rlib` (`20 - 5 == 15`, `catch_unwind` `rc=0`, `STT_GNU_IFUNC` `false`, `.weak` override rejected at link time `rc=1`).
     * **`-C lto=thin`:** `FunctionImporter` passes `IsPerformingImport = true` to `IRMover` (suppressing `ModuleInlineAsm` transfer except `.symver` at `IRMover.cpp:1572-1581`), keeping `#[inline(never)]` upstream functions isolated in their own `ThinModule` (`15`), **but importing non-leaf upstream `asm!` functions into downstream's `ThinModule` where downstream's `global_asm!(".macro sub ...")` rewrites `20 - 5 == 15` into `25`!**
     * **`-C lto=fat`:** `rustc` selects the costliest local CGU as `DstM` and links all local and upstream `.rlib` bitcode sorted alphabetically by module name (`lto.rs:301`) with `IsPerformingImport = false`, concatenating **every** crate's `ModuleInlineAsm` ahead of **every** function (`AsmPrinter.cpp:613-627`). Consequently, downstream—and **even an unrelated sibling `.rlib` (`z_sibling_dep`)**—corrupts upstream `#[inline(never)]` `asm!` (`15` $\to$ `25`), promotes upstream `#[inline(never)]` pure-Rust functions to `STT_GNU_IFUNC` (`type=10`) with zero warnings, strips `.eh_frame` across crates so upstream pure-Rust `catch_unwind` aborts (`SIGABRT`, `rc=-6`), and (when alphabetically ordered after `upstream_safe`) silently downgrades upstream `#[inline(never)]` pure-Rust `STB_GLOBAL` functions to `STB_WEAK` (`1` $\to$ `999`, `rc=0`)! Crucially, `.anneal.asm_sites` (`SHF_EXCLUDE`) **survives both ThinLTO and FatLTO bitcode merging into `.lto.rcgu.o`**, detecting `100%` of `.macro`-corrupted slices (`0x01` `ADD` vs. `0x29` `SUB`).
   - Across `rust-lld` vs. GNU `ld.bfd 2.47`: (i) `ld.bfd 2.47` rejects `--icf={none,safe,all}` (`rc=1`, unsupported option); (ii) `rustc` omits `.llvm_addrsig` (`SHT_LLVM_ADDRSIG`) by default (`has_llvm_addrsig_section: false`), causing `rust-lld --icf=safe` (`lld/ELF/Driver.cpp:2746-2750`) to conservatively mark **all** sections `keepUnique = true` (folding `0` `asm!` or `#[unsafe(naked)]` twins, whereas LLVM's in-compiler `MergeFunctions` pass folds pure-Rust twins even at `--icf=none`!); (iii) enabling `-C llvm-args=-addrsig` under `--icf=safe` keeps `#[no_mangle]` `asm!` twins distinct (`asm_folded: false`) **yet folds `#[unsafe(naked)]` twins (`naked_folded: true`) even when their function pointers are compared**, because `naked_asm!` lowers via `ModuleInlineAsm` (`naked_asm.rs:57`) outside `M.global_values()` (`AsmPrinter.cpp:3123-3129`); and (iv) `--icf=all` folds `naked_twin`, `asm_twin`, and `pure_twin` across all 6 LTO/CGU modes (`5` $\to$ `3` addresses, merging `.eh_frame` FDEs `537` $\to$ `515` / `401` $\to$ `388`) with zero interference from `.anneal.asm_sites`.

3. **`TyCtxt`-Driven `SpecConeHash` (`10/10` Tamper Recall, `0/4` False Positives) and Lean `v4.34.1` Non-Interference (`Basis: source + execution + derived`):**
   - Implementing `SpecConeCollector` inside [`support/anneal_driver_prototype.rs`](support/anneal_driver_prototype.rs) uncovered two live compiler traps: (a) on `--crate-type=rlib` at `-C opt-level >= 1` (even with `-Zno-codegen`), `rustc`'s `cross_crate_inlinable` analysis queries `optimized_mir` *before* `Callbacks::after_analysis`, **stealing `mir_drops_elaborated_and_const_checked` (`attempted to read from stolen value`)** unless `override_queries` arena-clones `Runtime(PostCleanup)` MIR at the top of `optimized_mir` (`-Zno-steal-mir` does not exist in `rustc 1.98+`); and (b) adding an unrelated `pub static` in another module increments `tcx`'s crate-global `AllocId` counter during `check_crate`, causing false-positive cache invalidations unless `GlobalAlloc` digests are hashed purely by content without raw `AllocId` indices.
   - Tested across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly` ([`support/probe_tyctxt_speccone_10vectors.py`](support/probe_tyctxt_speccone_10vectors.py)), `SpecConeCollector` detects **`10/10` (`100%`) indirect specification-tampering vectors** where `hot_ref`'s own Rust tokens remain `100%` byte-for-byte identical (2-hop callee body, `#[repr(C, packed)]` field offsets, uninitialized padding byte mask `IUUUIIII` $\to$ `IIIIIIII` at identical `size = 8, align = 4`, `NonZeroU8` niche `valid_range` `0..=255` $\to$ `1..=255` at identical `size = 1, align = 1`, implicit `TerminatorKind::Drop` glue, trait default-method override, `ConstAllocation` bytes, `Deref` coercion impl, callee ABI / `#[target_feature]`, and `promoted[0]` array constant) vs. `0/10` for source-token hashing, with **`0/4` (`0%`) false positives** across `hot_opt` `asm!` edits, unrelated modules/statics, 50-line shifts, and local-variable alpha-renaming.
   - [`support/MultiCguAttestationAndSpecCone.lean`](support/MultiCguAttestationAndSpecCone.lean) mechanizes all `9` soundness and counterexample theorems (`uid_only_key_collides_across_cgus`, `fatlto_global_asm_corrupts_prechecked_rlib_but_caught_on_lto_obj`, `multi_cgu_disjoint_nonce_union_sound`, `icf_all_pc_folding_sound_and_addr_counterexample`, `evalMir_cone_noninterference`, `specConeEq_preserves_totalMirAsmEquiv`, and the three constructive unsoundness witnesses when `initByteMask`, `Drop` glue, or niche `validRange` is omitted) in `Init.*`-only Lean `v4.34.1` with `0` `sorry`.
   - **Errata & v2 Extensions ([`postlink-gc-sections-debug-tombstone-attestation-and-speccone-pointee-closure`](../postlink-gc-sections-debug-tombstone-attestation-and-speccone-pointee-closure/REPORT.md)):** Subsequent testing of [`support/anneal_driver_prototype.rs`](support/anneal_driver_prototype.rs) identified and repaired three gaps in `anneal_driver_v2.rs`: (i) **Post-link `--gc-sections` `.debug_anneal_sites` tombstones & clobber quote sanitization:** dropping `SHF_EXCLUDE` on `.anneal.asm_sites,"",@progbits` fails under `-Wl,--gc-sections` (`ld.bfd 2.47` strips it to `0 B`; `rust-lld` and `ld.mold` resolve dead `STT_SECTION + r_addend` relocations to phantom `[0x4, 0x7)` / `[0x4, 0xc)` spans on `x86_64`/`aarch64`), and `Display` on `InlineAsmRegOrRegClass::Reg` emits literal `"` quotes that break `.asciz`—resolved by `.debug_anneal_sites,"",@progbits` DWARF `(0x0, 0x0)` tombstoning, live-symbol `--icf=all` coverage gating, and quote stripping; (ii) **Prebuilt sysroot `stdarch` `asm!` capture:** `providers.queries.optimized_mir` (`LocalDefId`) misses monomorphized cross-crate sysroot `libcore` `stdarch` `asm!` (`197` sites including `__writeeflags` `popfq` `RFLAGS.DF` UB)—resolved by also hooking `providers.extern_queries.optimized_mir` (`DefId`) with an idempotence guard; and (iii) **`SpecConeCollector` pointee & type-graph closure:** `v1`'s `Adt`-only recursion misses `8/8` pointee/compound/`FnPtr`/foreign-`Static`/`NonNull` tampering vectors (`&RefBoundedByte`, `&[SlicePair]`, `*const RawTarget`, `[ArrInner; 4]`, `(TupInner, u8, u8)`, `FnPtr` `PassMode`, `extern "C" { static ... }`, `NonNull<SmartTarget>`) and shifts on raw `DefId(0:NN)` indices when items are inserted earlier in the file—resolved in `SpecConeCollector` v2 (`ty.walk()` + `PlaceRef::ty` + `fn_abi_of_fn_ptr` + `GlobalAlloc::Static` + `DefIndex` scrubbing, achieving `18/18` recall and `0/5` false positives).

## Applicability

This report governs compiler-driver instrumentation (`rustc_driver`), multi-CGU and cross-crate build containment, ThinLTO/FatLTO and linker ICF soundness rules, and `TyCtxt`-level specification-cone hashing across the pinned upstream subjects in `REPORT.json`:

| Subject | Repository / Package | Pinned Revision / Version | Role in This Investigation |
| :--- | :--- | :--- | :--- |
| **`rustc` (`1.98.0-nightly`)** | `rust-lang/rust` | `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` (`2026-05-31`, LLVM `22.1.6`) | `rustc_driver` build & execution for Probe 1 (`cgu=16`, `.rmeta`, `x86_64`/`aarch64`/`riscv64gc` invariance) and Probe 3 (`SpecConeHash` 10-vector + 4-control suite). |
| **`rustc` (`1.99.1` stable)** | `rust-lang/rust` | `58cf8f9c35b355199727627d07ae34a4e2846d67` (`2026-10-13`, LLVM `23.1.1`) | Primary source inspection and full execution across Probes 1, 2 (36-cell LTO/ICF matrix), and 3 (`RUSTC_BOOTSTRAP=1` for `rustc_private`). |
| **`rustc` (`1.102.0-nightly`)** | `rust-lang/rust` | `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` (`2026-11-11`, LLVM `23.1.5`) | Source inspection (`compiler_entrypoint`, `BackendRepr`, `TerminatorKind`) and full execution across Probes 1, 2, and 3. |
| **LLVM & `rust-lld`** | `rust-lang/llvm-project` | `1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` (`23.1.1`) & `0a5579eb649d3634aead059efe6b11a7eeba145` (`23.1.5`) | Primary source inspection (`TargetInstrInfo.cpp`, `AsmLexer.cpp`, `AsmPrinter.cpp`, `IRMover.cpp`, `RISCVInstrInfo.cpp`, `lld/ELF/{ICF,Driver}.cpp`) and live `rust-lld` linking. |
| **Anneal Rust verifier** | `joshlf/anneal` | `c131b320eeeb26ef692e5afd5ec8db49ee518613` | Target `rustc_driver` architecture (`trusted/rustc-capture/src/driver.rs`) and two-surface threat model (`THREAT_MODEL.md`). |
| **Lean 4** | `leanprover/lean4` | `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Synchronous kernel checking (`-DElab.async=false -Ddebug.skipKernelTC=false`) of all 9 theorems in [`support/MultiCguAttestationAndSpecCone.lean`](support/MultiCguAttestationAndSpecCone.lean). |
| **GNU Binutils & LLVM 21 CLI** | Debian packages | `ld.bfd` / `readelf` `2.47`; `llc` / `llvm-mc` `21.1.8` | Differential `ld.bfd` `--icf` probing, `${:uid}` per-CGU LLVM IR assembly, and `.weak` override object assembly. |

### Shared vs. Version-Specific `rustc_private` & Codegen Behavior (`1.98.0-nightly` vs. `1.99.1` vs. `1.102.0-nightly`)
- **Identical across all three toolchains:** `Config::override_queries` (`DEFAULT_QUERY_PROVIDERS.queries.{optimized_mir, mir_built}`); `cr_zero_drift` `0 B` `.text` SHA-256 invariance across `x86_64`, `aarch64` (`N = 5,000`), and `riscv64gc` (`N = 900`); `+4 B` `aarch64` and opcode-swap `riscv64gc` drift under both `multiline_pushsection` and `ifndef_macro`; all 36 ThinLTO/FatLTO `GlobalScopeAsm` and `rust-lld` / `ld.bfd` ICF outcomes (`1.99.1` & `1.102.0-nightly`); `mir_drops_elaborated_and_const_checked` stealing during `rlib` `cross_crate_inlinable` analysis; and `10/10` tamper recall + `0/4` benign false positives in `SpecConeCollector`.
- **Five `rustc_private` API transitions across `1.98.0-nightly` $\to$ `1.99.1` $\to$ `1.102.0-nightly`:**
  1. `ty::EarlyBinder::bind(val)` (`1.98.0-nightly`) $\to$ `ty::EarlyBinder::bind(tcx, val)` (`1.99.1` and `1.102.0-nightly`).
  2. `rustc_abi::BackendRepr::ScalarPair(Scalar, Scalar)` (`1.98.0-nightly`) $\to$ `BackendRepr::ScalarPair { a: Scalar, b: Scalar, b_offset: Size }` (`1.99.1` and `1.102.0-nightly`, `rustc_abi/src/lib.rs:1801-1805`).
  3. `ty::FnDef(def_id, args)` where `args: GenericArgsRef<'tcx>` (`1.98.0-nightly`) $\to$ `args: ty::Binder<'tcx, GenericArgsRef<'tcx>>` requiring `.skip_binder()` (`1.99.1` and `1.102.0-nightly`).
  4. `layout.align.abi.bytes()` (`AbiAndPrefAlign` in `1.98.0-nightly` and `1.99.1`) $\to$ `layout.align.bytes()` (`Align` directly in `1.102.0-nightly`), alongside `TerminatorKind::Goto { target, loop_hint_attrs }` gaining `loop_hint_attrs` in `1.102.0-nightly`.
  5. `rustc_driver::run_compiler(&args, &mut callbacks)` (`1.98.0-nightly` and `1.99.1`) $\to$ `rustc_driver::compiler_entrypoint(&args, &mut callbacks)` (`1.102.0-nightly`, `compiler/rustc_driver_impl/src/lib.rs:172`).

### Scope Boundary Relative to Neighboring Corpus Reports
This package extends strictly without duplicating:
- [`self-attesting-inline-asm-register-bindings-rmeta-monomorphization-and-cgu-containment`](../self-attesting-inline-asm-register-bindings-rmeta-monomorphization-and-cgu-containment/REPORT.md), which evaluated single-CGU (`-C codegen-units=1`) `global_asm!` macros and hand-written source wrappers, leaving open the `codegen-units=16` `global_asm!` crash, `asm.rs:192` `$` escaping in MIR injection, `${:uid}` per-CGU reset, ThinLTO/FatLTO `GlobalScopeAsm` propagation, and `--icf`;
- [`rust-vs-inline-asm-behavioral-equivalence-for-verified-hot-loop-optimization`](../rust-vs-inline-asm-behavioral-equivalence-for-verified-hot-loop-optimization/REPORT.md), whose `Boundaries` section explicitly flagged that its text-based `-Z dump-mir` `SpecConeHash` script did not walk `TyCtxt` `AdtDef` layouts, `Drop` glue, or trait resolutions;
- [`rustc-postcleanup-mir-unevaluated-consts-promoted-bodies-and-alloc-decoding`](../rustc-postcleanup-mir-unevaluated-consts-promoted-bodies-and-alloc-decoding/REPORT.md), reusing its `ConstValue` / `GlobalAlloc` / `promoted_mir` invariants rather than re-deriving CTFE representation laws; and
- [`rustc-lto-mechanics-symbol-preservation-and-performance-value`](../rustc-lto-mechanics-symbol-preservation-and-performance-value/REPORT.md) and [`rustc-binary-origin-attribution-gc-sections-and-icf-soundness`](../rustc-binary-origin-attribution-gc-sections-and-icf-soundness/REPORT.md), extending their general LTO export-list and pure-Rust ICF analyses to adversarial `GlobalScopeAsm` directives, `SHF_EXCLUDE` `.anneal.asm_sites` survival, and `#[unsafe(naked)]` `.llvm_addrsig` omission.

## Findings

### 1. In-Process `rustc_driver` `override_queries` Injection Across Multi-CGU Builds and Three ISAs

`Basis: source + execution + derived` (`rust-lang/rust@58cf8f9c35`: `compiler/rustc_interface/src/passes.rs:898, 980-985`, `compiler/rustc_monomorphize/src/partitioning.rs:700, 816-818`, `compiler/rustc_lint/src/builtin.rs:2797-3035`, `compiler/rustc_codegen_llvm/src/asm.rs:85-125, 188-255`, `compiler/rustc_codegen_ssa/src/mir/naked_asm.rs:18-58`; `rust-lang/llvm-project@1b9c0d5ff9`: `llvm/lib/CodeGen/TargetInstrInfo.cpp:113-149`, `llvm/lib/MC/MCParser/AsmLexer.cpp:313, 349-372, 898-906`, `llvm/lib/Target/RISCV/RISCVInstrInfo.cpp:1988-1993`; [`support/anneal_driver_prototype.rs`](support/anneal_driver_prototype.rs), [`support/probe_driver_cgu_and_invariance.py`](support/probe_driver_cgu_and_invariance.py), [`support/probe_1_driver_cgu_results.json`](support/probe_1_driver_cgu_results.json))

#### 1.1 Three Structural Fractures of Source-Macro and `global_asm!` Wrappers Under `codegen-units = 16`

1. **`MonoItem::GlobalAsm` Single-CGU Partitioning Crash (`cgu16_global_asm_rc = 1`):**
   In `compiler/rustc_monomorphize/src/partitioning.rs:700, 816-818`, `MonoItem::GlobalAsm(item_id)` is assigned to the single CGU corresponding to its defining module. When Cargo's default `-C codegen-units=16` partitions 16 submodules across `cgu.0..15`, any `global_asm!(".macro __aw ...")` helper lands exclusively in `cgu.0`'s `MCContext`, causing `cgu.1..15` (`15` errors in `1.98.0-nightly`; immediate `rc=1` in `1.99.1` and `1.102.0-nightly`) and every downstream `.rmeta` consumer (`rmeta_consumer_failed_mnemonic: true`) to fail with `error: invalid instruction mnemonic '__aw'`.
2. **`rustc_codegen_llvm` `$` $\to$ `$$` Escaping and `${:uid}` Per-CGU `AsmPrinter` Reset:**
   Attempting to inject `${:uid}` via MIR `InlineAsmTemplatePiece::String` fails because `compiler/rustc_codegen_llvm/src/asm.rs:189-199` unconditionally rewrites every `'$'` character in `InlineAsmTemplatePiece::String` to `"$$"`, passing literal `${:uid}` to `MCAsmParser`. Furthermore, even at the LLVM IR level (`llc -filetype=obj` on `uid_cgu0.ll` and `uid_cgu1.ll`), `AsmPrinter`'s `${:uid}` counter (`AsmPrinterInlineAsm.cpp:439-450`) is local to each CGU's `AsmPrinter`, emitting `["cgu=0:uid=0", "cgu=1:uid=0"]` (`uid_resets_to_zero_across_cgus: true`). Keying attestation records by `(session_nonce, uid)` without a `DefPathHash`-derived `site_id` therefore collides across CGUs (`uid_only_key_collides_across_cgus` in [`support/MultiCguAttestationAndSpecCone.lean`](support/MultiCguAttestationAndSpecCone.lean)).
3. **`InlineAsmMacro::NakedAsm` vs. `InlineAsmMacro::Asm` Lowering Split and Clobber Indexing:**
   In `compiler/rustc_codegen_ssa/src/mir/naked_asm.rs:32-58`, `#[unsafe(naked)]` functions store `TerminatorKind::InlineAsm { asm_macro: InlineAsmMacro::NakedAsm, .. }` in MIR `START_BLOCK` and lower via `cx.codegen_global_asm` (`AsmPrinterInlineAsm.cpp:90-138` with `MI == nullptr`, bypassing `EmitInlineAsmStr`). Simultaneously, in `compiler/rustc_codegen_llvm/src/asm.rs:88-98`, discarded explicit-register clobbers (`Out { reg: InlineAsmRegOrRegClass::Reg(_), place: None }`, e.g. `out("r10") _`) `continue` before `op_idx.insert(idx, ...)`; emitting a `Placeholder { operand_idx: idx }` for such an operand panics on `op_idx[&operand_idx]`, so the MIR rewriter must serialize `Out { place: None }` statically as `clob{idx}={reg}` while emitting `Placeholder`s only for register-allocated/value operands.

#### 1.2 Eliminating `TargetInstrInfo::getInlineAsmLength` Drift Without `global_asm!` or `.macro` (`cr_zero_drift`)

When a `rustc_driver` rewrites `TerminatorKind::InlineAsm` inside `providers.queries.optimized_mir` (leaving `mir_drops_elaborated_and_const_checked` untouched for MIR capture while covering both local multi-CGU codegen and `.rmeta` serialization) after `AsmLabels` (`rustc_lint/src/builtin.rs:2797`), an inline `.ifndef __aw_<NONCE>_<SITE> ... .endif` macro fixes the `cgu=16` crash—**but still perturbs `aarch64` and `riscv64gc` machine code** because `TargetInstrInfo::getInlineAsmLength` (`TargetInstrInfo.cpp:113-149`) counts every `\n`- or `;`-separated line inside `.ifndef ... .endif` as `MaxInstLength` (`4 B`):

```cpp
// llvm/lib/CodeGen/TargetInstrInfo.cpp:120-145
for (; *Str; ++Str) {
  if (*Str == '\n' || strncmp(Str, MAI.getSeparatorString(),
                              strlen(MAI.getSeparatorString())) == 0) {
    AtInsnStart = true;
  } else if (isAsmComment(Str, MAI)) {
    AtInsnStart = false;
  }
  if (AtInsnStart && !isSpace(static_cast<unsigned char>(*Str))) {
    unsigned AddLength = MaxInstLength;
    if (strncmp(Str, ".space", 6) == 0) {
      ...
      if (*EStr == '\0' || *EStr == '\n' || isAsmComment(EStr, MAI))
        AddLength = SpaceSize;
    }
    Length += AddLength;
    AtInsnStart = false;
  }
}
```

Inspecting `TargetInstrInfo.cpp:120-145` alongside `llvm/lib/MC/MCParser/AsmLexer.cpp:313, 898-906` reveals an exact, architecture-universal zero-drift construction (`cr_zero_drift`):
1. `TargetInstrInfo::getInlineAsmLength` resets `AtInsnStart = true` **only** on `'\n'` (`0x0A`) and `MAI.getSeparatorString()` (`";"` on ELF), treating `'\r'` (`0x0D`) as ordinary whitespace (`isSpace('\r') == true`), whereas `AsmLexer::LexToken` (`case '\r': return AsmToken(AsmToken::EndOfStatement, ...)`) and `AsmLexer::LexLineComment` (`while (CurChar != '\n' && CurChar != '\r' ...)`) treat bare `'\r'` as a full statement terminator.
2. Prepending `".space 0 <CMT>\r<L_s>:\n"` (where `<CMT>` is `"//"` on `aarch64`, `"@"` on `arm`, and `"#"` on `x86_64`/`riscv64`) evaluates `strncmp(".space", 6) == 0` with `isAsmComment(EStr, MAI) == true`, adding **`0 B`**, keeping `AtInsnStart = false` across `\r<L_s>:`, and restoring `AtInsnStart = true` at `\n` immediately before `<USER_BODY>`. Appending `"\r.space 0 <CMT>\r<L_e>:\r.pushsection ..."` similarly contributes **`0 B`** even when `<USER_BODY>` is empty (`asm!("")`) or ends with `\n`/`;`, while `.space 0` emits zero bytes and zero fragments in `MCObjectStreamer`.
3. Deriving four distinct decimal directional label IDs `L_s, L_e, L_d, L_de ∈ [200_000_000, 899_999_999]` from `SHA-256(session_nonce || site_id || salt)` after verifying zero occurrences in `<USER_BODY>` (and rejecting `.macro`/`.altmacro`/`.rept`/`.irp`/`.irpc` in `<USER_BODY>`) avoids `$` escaping (`asm.rs:192`), avoids Intel-syntax binary-literal lexing (`AsmLexer.cpp:349-372`, since leading digit is `2..8`), and expands cleanly across `4×`/`16×` loop unrolling, inlining, `#[unsafe(naked)]`, `cgu=16`, and `.rmeta`.

Live differential execution across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly` (`support/probe_1_driver_cgu_results.json`, identical results on all three compilers) confirms exact `.text` SHA-256 parity across all three ISAs:

| Target & Branch-Relaxation Stress Test | `off` (Uninstrumented) | `multiline_pushsection` (`\n`) | `ifndef_macro` (Inline `.ifndef`) | `cr_zero_drift` (`\r` + `.space 0`) |
| :--- | :--- | :--- | :--- | :--- |
| **`x86_64`** (`35` sites inside `je rel8`, `150 B`) | `150 B`, `sha256_16 = 40bb058163bb27d1` (`0` sites) | `150 B`, `40bb058163bb27d1` (`35` sites, `0 B` delta) | `150 B`, `40bb058163bb27d1` (`35` sites, `0 B` delta) | **`150 B`, `40bb058163bb27d1` (`35` sites, EXACT)** |
| **`aarch64`** (`5,000` sites inside `tbz` $\pm 32\text{ KiB}$, `20,020 B`) | `20,020 B`, `4e81e5e467c69aa7`, head `60710236` (`tbz w0, #0, +0x4e2c`) | **`20,024 B` (`+4 B` DRIFT!)**, `1506d6095a7f1217`, head `40000037 8b130014` (`tbnz + b`) | **`20,024 B` (`+4 B` DRIFT!)**, `1506d6095a7f1217`, head `40000037 8b130014` (`tbnz + b`) | **`20,020 B`, `4e81e5e467c69aa7`, head `60710236` (`5,000` sites, EXACT!)** |
| **`riscv64gc`** (`900` `c.addi` sites inside `beqz` $\pm 4\text{ KiB}$, `1,812 B`) | `1,812 B`, `b85f3f2cce282b77`, head `63080570` (`beqz a0, +0x710`, `4 B`) | **`1,812 B` (`0 B` size delta, SHA-256 DRIFT!)**, `2d26595a9ab21703`, head `11e1 39a7` (`c.bnez + c.j`, `2+2 B`) | **`1,812 B` (`0 B` size delta, SHA-256 DRIFT!)**, `2d26595a9ab21703`, head `11e1 39a7` (`c.bnez + c.j`, `2+2 B`) | **`1,812 B`, `b85f3f2cce282b77`, head `63080570` (`900` sites, EXACT!)** |

> **Subtle RISC-V compressed-ISA (`RVC`) measurement trap:** On `riscv64gc`, `RISCVInstrInfo::getInstSizeInBytes` (`RISCVInstrInfo.cpp:1988-1993`) calls `getInlineAsmLength`, inflating `900` sites to `36,000 B > 4,096 B` under both `multiline_pushsection` and `ifndef_macro`. `BranchRelaxation` replaces the 4-byte B-type `beqz a0, +0x710` (`0x70050863`) with an inverted branch plus jump—which RVC subsequently compresses into 2-byte `c.bnez a0, +4` (`0xe111`) + 2-byte `c.j +0x70e` (`0xa739`), totaling **`4 B` (`0 B` section-length change!)** while silently altering executable opcodes! Only full `.text` SHA-256 hashing catches this perturbation, and `cr_zero_drift` eliminates it completely.

Across the 16-module `-C codegen-units=16` `rlib` + downstream `bin` pipeline (`driver_multi_cgu_and_rmeta` in `support/probe_1_driver_cgu_results.json`), `anneal_driver_prototype` compiled all `16/16` upstream `.rcgu.o` objects (`21` attested records across `16` CGUs, `0` lint warnings under `#![deny(named_asm_labels, binary_asm_labels)]`, matching `21` records under `mir_built_cr`) and all `4` downstream `.rcgu.o` objects (`5` attested records preserving **both** upstream session nonce `aa11bb22cc33dd44ee55ff6677889900` for `.rmeta`-monomorphized generics/inlined `sym` sites and downstream session nonce `11223344556677889900aabbccddeeff` for local `asm!`), executed `down_app` cleanly (`rc=0`), stripped `.anneal.*` (`SHF_EXCLUDE`) from the final ELF, and rejected `.macro` inside user `asm!`.

---

### 2. ThinLTO / FatLTO `GlobalScopeAsm` (`IRMover`) and `rust-lld` `--icf` Containment Matrix

`Basis: source + execution + derived` (`rust-lang/rust@58cf8f9c35`: `compiler/rustc_codegen_llvm/src/back/lto.rs:212-338`, `compiler/rustc_llvm/llvm-wrapper/Linker.cpp:25-43`; `rust-lang/llvm-project@1b9c0d5ff9`: `llvm/lib/Linker/IRMover.cpp:1563-1582`, `llvm/lib/CodeGen/AsmPrinter/AsmPrinter.cpp:613-627, 3120-3130`, `lld/ELF/ICF.cpp:161-235`, `lld/ELF/Driver.cpp:849-856, 2688-2752`; [`support/probe_lto_global_asm_and_icf.py`](support/probe_lto_global_asm_and_icf.py), [`support/probe_2_lto_icf_results.json`](support/probe_2_lto_icf_results.json))

#### 2.1 Cross-Crate `GlobalScopeAsm` Blast Radius Across `-C lto={off, thin, fat}`

In `llvm/lib/Linker/IRMover.cpp:1563-1582`, LLVM's bitcode mover branches on `IsPerformingImport`:

```cpp
if (!IsPerformingImport && !SrcM->getModuleInlineAsm().empty()) {
  for (const Module::GlobalAsmFragment &Frag : SrcM->getModuleInlineAsm()) {
    Module::GlobalAsmFragment NewFrag(Frag);
    NewFrag.Asm = adjustInlineAsm(NewFrag.Asm, SrcTriple);
    DstM.appendModuleInlineAsm(std::move(NewFrag));
  }
} else if (IsPerformingImport) {
  ModuleSymbolTable::CollectAsmSymvers(*SrcM, [&](StringRef Name, StringRef Alias) {
    if (DstM.getNamedValue(Name)) { ... DstM.appendModuleInlineAsm(std::string(S)); }
  });
}
```

In FatLTO (`compiler/rustc_codegen_llvm/src/back/lto.rs:247-325`), `rustc` picks the costliest local CGU as `DstM`, sorts all remaining local CGUs and upstream `.rlib` bitcode modules alphabetically by `CString` name (`serialized_modules.sort_by` at `line 301`), and links them via `LLVMRustLinkerAdd` (`IsPerformingImport == false`). When `AsmPrinter::doInitialization` (`AsmPrinter.cpp:613-627`) runs on the merged module, it executes **every** crate's `ModuleInlineAsm` in a single `MCStreamer` **before** emitting any function in the program. Executing all five cross-crate vectors on `rustc 1.99.1` and `1.102.0-nightly` (`support/probe_2_lto_icf_results.json`, identical across `cgu=1` and `cgu=16` and across both compilers) establishes the exact containment table:

| Cross-Crate Attack Against Verified `upstream_safe.rlib` | `-C lto=off` (`cgu=1, 16`) | `-C lto=thin` (`cgu=1, 16`) | `-C lto=fat` (`cgu=1, 16`) | Governing Mechanism & Mandatory Gate |
| :--- | :--- | :--- | :--- | :--- |
| **1. Downstream `global_asm!(".macro sub -> add")` vs. upstream `#[inline(never)]` `asm!("sub")`** | **Immune (`15`)** | **Immune (`15`)** (`noinline` stays in `upstream_safe`'s `ThinModule`) | **CORRUPTED (`25`)!** Merged into `DstM`; `.lto.rcgu.o` `.anneal.asm_sites` **SURVIVES (`2` sites) & CATCHES `0x01` `ADD`!** | Re-verify `.anneal.asm_sites` on `.lto.rcgu.o` whenever LTO is enabled; forbid `global_asm!` in untrusted crates. |
| **2. Downstream `global_asm!(".macro sub -> add")` vs. upstream non-leaf `asm!("sub")` (`calls > 0`)** | **Immune (`15`)** (non-leaf not MIR-inlined) | **CORRUPTED (`25`)!** `FunctionImporter` imports body into `downstream`'s `ThinModule`; `.lto.rcgu.o` **SURVIVES (`3` sites) & CATCHES `0x01`!** | **CORRUPTED (`25`)!** Caught in `.lto.rcgu.o` (`0x01`). | ThinLTO imports non-`noinline` upstream bitcode into the caller's `MCContext`; `.lto.rcgu.o` attestation is mandatory under `-C lto=thin`. |
| **3. Unrelated sibling `z_sibling_dep.rlib` `global_asm!(".macro sub -> add")` vs. `upstream_safe` `#[inline(never)]`** | **Immune (`15`)** | **Immune (`15`)** (`IsPerformingImport = true` blocks `.macro` export) | **CORRUPTED (`25`)!** `IRMover` appends `z_sibling_dep`'s `ModuleInlineAsm` into `DstM` before all `MachineFunction`s! | Under `-C lto=fat`, **any** crate in the dependency graph with `global_asm!` contaminates **every** crate's `asm!`. |
| **4. Downstream `global_asm!(".type upstream_pure_ifunc_target, @gnu_indirect_function")`** | **Immune (`false`)** | **Immune (`false`)** | **CORRUPTED (`true`, `STT_GNU_IFUNC = 10`, zero warnings)!** `CombineSymbolTypes` promotes upstream pure-Rust `#[inline(never)]` fn! | Audit final linked ELF `.symtab`/`.dynsym` for `STT_GNU_IFUNC` (`type == 10`). |
| **5. Uncalled `asm!(".weak upstream_pure_auth")` in `z_sibling_dep.rlib` + external override (`999`)** | **Rejected (`rc=1`, duplicate symbol)** | **Rejected (`rc=1`, duplicate symbol)** | **CORRUPTED (`rc=0`, returns `999`)!** `lto.rs:301` links `upstream_safe` before `z_sibling_dep`, so `.weak` runs *after* `STB_GLOBAL` and downgrades to `STB_WEAK`! | Audit final ELF `.symtab` bindings (`STB_GLOBAL` vs. `STB_WEAK`) on all verified pure-Rust symbols. |
| **6. Downstream `global_asm!(".cfi_sections .debug_frame")` vs. upstream pure-Rust `catch_unwind`** | **Immune (`rc=0`)** | **Immune (`rc=0`)** | **CORRUPTED (`SIGABRT`, `rc=-6`)!** Strips `.eh_frame` across the entire monolithic module! | Assert `.eh_frame` presence and FDE coverage on the linked binary when unwinding is enabled. |

#### 2.2 Linker `--icf={none, safe, all}` (`rust-lld` vs. `ld.bfd 2.47`) and the `#[unsafe(naked)]` `.llvm_addrsig` Gap

Testing identical twin pairs (`naked_twin_{a,b}`, `asm_twin_{a,b}`, `pure_twin_{a,b}`) whose function pointers are explicitly compared at runtime (`f_a as *const () as usize == f_b as *const () as usize`) across `1.99.1` and `1.102.0-nightly` (`support/probe_2_lto_icf_results.json`) establishes four invariants:

1. **GNU `ld.bfd 2.47` lacks `--icf` entirely (`rc=1` on `none`, `safe`, and `all`):** Identical Code Folding on Linux ELF is active only under `rust-lld` / `ld.lld` (or `mold`/`gold`).
2. **In-compiler LLVM `MergeFunctions` folds pure-Rust twins even at `--icf=none`, while sparing `asm!` and `#[unsafe(naked)]` twins:** Because `rustc` marks Rust functions `UnnamedAddr::Global`, LLVM's `MergeFunctions` pass aliases `pure_twin_a` and `pure_twin_b` (`pure_folded: true`) across all 18 `rust-lld` cells, whereas `asm_twin_{a,b}` (distinct `.anneal.asm_sites` IDs) and `naked_twin_{a,b}` (`ModuleInlineAsm`) remain distinct at `--icf=none` (`5` addresses).
3. **Default `rustc` omits `SHT_LLVM_ADDRSIG` (`has_llvm_addrsig_section: false`), making `--icf=safe` a no-op—while `-C llvm-args=-addrsig` exposes a `#[unsafe(naked)]` folding asymmetry:**
   - Without `.llvm_addrsig`, `lld/ELF/Driver.cpp:2746-2750` marks every symbol's section `keepUnique = true` under `--icf=safe`, so `--icf=safe` folds neither `asm_twin` nor `naked_twin` (`5` addresses).
   - When `-C llvm-args=-addrsig` emits `.llvm_addrsig` (`lto_off_cgu_1_icf_safe_addrsig`), `AsmPrinter::doFinalization` (`AsmPrinter.cpp:3120-3130`) iterates `M.global_values()` and emits `#[no_mangle]` `asm_twin_{a,b}` into `.llvm_addrsig` (`asm_folded: false`), **but omits `naked_twin_{a,b}` (`naked_folded: true`, `4` addresses, FDEs `537` $\to$ `536`) even though `naked_twin_a as usize == naked_twin_b as usize` was evaluated in `main`**, because `naked_asm!` defines its symbol inside `ModuleInlineAsm` rather than as a defined `GlobalValue` without `unnamed_addr`!
4. **`--icf=all` folds both `#[unsafe(naked)]` and self-attested `asm!` twins cleanly (`5` $\to$ `3` addresses, FDEs `537` $\to$ `515` at `lto=off`, `491` $\to$ `471` at `lto=thin`, `401` $\to$ `388` at `lto=fat`):** Because `.rela.anneal.asm_sites` relocations point *from* `.anneal.asm_sites` *into* `.text.*` (never the reverse), `.anneal.asm_sites` (`SHF_EXCLUDE`) introduces zero outgoing relocations on `.text.*` and never impedes `--icf=all`. Post-link binary validators must treat `PC -> VerifiedSpec` as a **many-to-1** relation and forbid verification obligations that assume `fn_a as usize != fn_b as usize` (`icf_all_pc_folding_sound_and_addr_counterexample`).

---

### 3. `TyCtxt`-Driven `SpecConeHash` Against 10 Indirect Tampering Vectors and Lean `v4.34.1` Mechanization

#### 3.1 Two Live `TyCtxt` Engineering Traps (`Steal<Body>` Under `rlib` Optimization and `AllocId` Shift)

`Basis: source + execution` ([`support/anneal_driver_prototype.rs`](support/anneal_driver_prototype.rs), [`support/probe_tyctxt_speccone_10vectors.py`](support/probe_tyctxt_speccone_10vectors.py), [`support/probe_3_speccone_results.json`](support/probe_3_speccone_results.json))

Building `SpecConeCollector` inside `Callbacks::after_analysis` exposed two critical implementation invariants:
1. **`mir_drops_elaborated_and_const_checked` is already stolen before `after_analysis` on `--crate-type=rlib` at `-C opt-level >= 1` (even with `-Zno-codegen`):** During reachability analysis, `tcx.cross_crate_inlinable` (`compiler/rustc_mir_transform/src/cross_crate_inline.rs:18-111`) queries `tcx.optimized_mir(def_id)` on small `pub fn` helpers, stealing `mir_drops_elaborated_and_const_checked` and panicking with `attempted to read from stolen value: rustc_middle::mir::Body` (`-Zno-steal-mir` is rejected as an unknown flag in `rustc 1.98+`). Intercepting `providers.queries.optimized_mir` in `override_queries` to arena-allocate `tcx.arena.alloc(steal.borrow().clone())` *before* delegating to `DEFAULT_QUERY_PROVIDERS.queries.optimized_mir` preserves un-inlined `Runtime(PostCleanup)` MIR across all optimization levels.
2. **Crate-global `AllocId` numbering shifts when unrelated `static` items are added (`C02_unrelated_module_and_types`):** Because `rustc_hir_analysis::check_crate` evaluates every `DefKind::Static` initializer in the crate before `after_analysis`, adding `pub static EXTRA_STATIC: u64 = 12345;` in an unrelated module bumps the `AllocId` integers assigned to `hot_ref`'s `ConstAllocation`s (`TABLE_DATA` and `promoted[0]`). Keying the master cone digest strictly on sorted **content-addressed** `GlobalAlloc` hashes (init-masked bytes + recursive provenance target digests, omitting raw `AllocId` numbers) eliminates the false positive while preserving 100% sensitivity to constant byte and provenance mutations.

#### 3.2 10-Vector Indirect Tampering + 4-Control Matrix (`1.98.0-nightly`, `1.99.1`, `1.102.0-nightly`)

Across all three toolchains (`baseline`: `18` `Instance`s, `40` normalized `Ty`s, `3` `GlobalAlloc`s), every `V01`–`V10` case keeps `hot_ref`'s Rust tokens **100% byte-for-byte identical** (`naive_token_hash_changed == false`):

| Scenario ID | Indirect Semantic Channel Mutated (or Benign Control) | `hot_ref` Tokens Identical? | Naive Token Hash Changed? | `TyCtxt` `SpecConeHash` Changed? (`1.98` / `1.99.1` / `1.102`) | `TyCtxt` Mechanism Catching (or Ignoring) the Edit |
| :--- | :--- | :---: | :---: | :---: | :--- |
| **`V01_transitive_callee_body`** | 2-hop helper `leaf_mix`: `wrapping_mul(31)` $\to$ `wrapping_mul(33)` | `true` | `false` (MISS) | **`true` (`3/3`)** | BFS `TerminatorKind::Call` $\to$ `Instance::try_resolve` $\to$ `Runtime(PostCleanup)` MIR |
| **`V02_adt_repr_packed_offsets`** | `PacketHdr`: `#[repr(C)]` (`8 B`, off `4`) $\to$ `#[repr(C, packed)]` (`5 B`, off `1`) | `true` | `false` (MISS) | **`true` (`3/3`)** | `tcx.layout_of` `size`, `align`, `FieldsShape::Arbitrary { offsets }` |
| **`V03_adt_uninit_padding_mask`** | `PaddedPair`: uninit gap (`8 B`, `IUUUIIII`) $\to$ `_explicit_pad: [u8; 3]` (`8 B`, `IIIIIIII`) | `true` | `false` (MISS) | **`true` (`3/3`)** | Recursive `compute_init_byte_mask` (`FieldsShape` $\times$ `Variants`) |
| **`V04_adt_niche_valid_range`** | `BoundedByte(u8)` (`1 B`, `0..=255`) $\to$ `BoundedByte(NonZeroU8)` (`1 B`, `1..=255`) | `true` | `false` (MISS) | **`true` (`3/3`)** | `layout.backend_repr` (`Scalar::Initialized { valid_range }`) |
| **`V05_implicit_drop_glue`** | `impl Drop for ScopeGuard`: `fetch_add(self.0)` $\to$ `fetch_add(self.0 * 2)` | `true` | `false` (MISS) | **`true` (`3/3`)** | `TerminatorKind::Drop` $\to$ `Instance::resolve_drop_glue(tcx, drop_ty)` |
| **`V06_trait_default_method_override`** | Override default `AccPolicy::combine` (`+` $\to$ `^`) on `impl AccPolicy for FastPolicy` | `true` | `false` (MISS) | **`true` (`3/3`)** | `Instance::try_resolve` shifts from trait default `DefId` to impl `DefId` |
| **`V07_const_allocation_bytes`** | `TABLE_DATA` behind `AccPolicy::TABLE: &'static [u32; 4]`: `[10,..]` $\to$ `[99,..]` | `true` | `false` (MISS) | **`true` (`3/3`)** | `ConstValue::Scalar(Ptr)` $\to$ `GlobalAlloc::Memory` init-masked bytes + provenance |
| **`V08_deref_coercion_impl`** | `<BufView as Deref>::deref`: `self.0` $\to$ `&self.0[1..]` (`18` $\to$ `22` instances) | `true` | `false` (MISS) | **`true` (`3/3`)** | Implicit `Deref::deref` call edge in `Runtime(PostCleanup)` MIR |
| **`V09_callee_abi_and_target_feature`** | `mix_step`: Rust ABI $\to$ `extern "C"` (+ `#[target_feature(enable = "sse4.2")]` sibling) | `true` | `false` (MISS) | **`true` (`3/3`)** | `tcx.fn_abi_of_instance` (`conv`, `can_unwind`, `PassMode`) + `codegen_instance_attrs` |
| **`V10_promoted_const_array_element`** | `PROMOTED_K0` inside `&[PROMOTED_K0, 2, 3, 4]`: `1` $\to$ `77` | `true` | `false` (MISS) | **`true` (`3/3`)** | `tcx.promoted_mir(local_def_id)` + `body.required_consts` evaluation |
| **`C01_optimize_hot_opt_asm`** | Rewrite `hot_opt` `asm!` + add private `opt_private_helper` | `true` | `false` | **`false` (`0/3` FP)** | Disjoint from `hot_ref`'s transitive `SpecCone` |
| **`C02_unrelated_module_and_types`** | Mutate `unrelated_helper` + add `extra_mod::{ExtraType, EXTRA_STATIC}` | `true` | `false` | **`false` (`0/3` FP)** | Content-addressed `GlobalAlloc` digests ignore shifted `AllocId` numbers |
| **`C03_comments_and_50_line_shift`** | Prepend 50 comment lines above crate items (shifting all `Span`s) | `true` | `false` | **`false` (`0/3` FP)** | Span-free MIR statement/terminator canonicalization |
| **`C04_local_variable_alpha_rename`** | Rename `acc`, `lut`, `slice`, `_g`, `pair` inside `hot_ref` | `false` | **`true` (FP!)** | **`false` (`0/3` FP)** | De-Bruijn `Local` index hashing omitting `var_debug_info` |

#### 3.3 Lean `v4.34.1` Mechanization ([`support/MultiCguAttestationAndSpecCone.lean`](support/MultiCguAttestationAndSpecCone.lean))

`Basis: execution + derived` (`leanprover/lean4@5045d00564` `v4.34.1`, [`support/MultiCguAttestationAndSpecCone.lean`](support/MultiCguAttestationAndSpecCone.lean))

`support/MultiCguAttestationAndSpecCone.lean` (`Init.*`-only, `0` `sorry`, checked with `-DElab.async=false -Ddebug.skipKernelTC=false`) establishes nine machine-checked theorems:
1. `uid_only_key_collides_across_cgus`: constructive collision on `uidOnlyKey` across `cgu.0` and `cgu.1` (`cguLocalUid = 0`) with distinct `SiteId`s and incompatible register maps.
2. `fatlto_global_asm_corrupts_prechecked_rlib_but_caught_on_lto_obj`: proves pre-LTO `.rlib` `verifySiteRecord` passes (`true`), FatLTO `.macro sub -> add` mutates the slice (`0x29` $\to$ `0x01`), and `.lto.rcgu.o` `verifySiteRecord` rejects (`false`).
3. `multi_cgu_disjoint_nonce_union_sound`: proves by induction over arbitrary multi-CGU / cross-crate `.rmeta` object lists that per-`.rcgu.o` `verifyCguObject` over authorized session nonces implies `ValidAttestedSlice` for every record in `unionCguRecords`.
4. `icf_all_pc_folding_sound_and_addr_counterexample`: proves `--icf=all` address aliasing simultaneously preserves `AddressObliviousSpec` for all folded `DefId`s while falsifying `symAddr 0 ≠ symAddr 1`.
5. `evalMir_cone_noninterference` & 6. `specConeEq_preserves_totalMirAsmEquiv`: proves step-indexed MIR operational non-interference (`WellClosedCone` + `SpecConeEq` $\implies$ `evalMir` equality and `TotalMirAsmEquiv` preservation across arbitrary out-of-cone and `rawAllocIds` mutations).
7. `omitted_padding_mask_unsound_counterexample`, 8. `omitted_drop_glue_unsound_counterexample`, & 9. `omitted_niche_range_unsound_counterexample`: constructive counterexamples proving that omitting `initByteMask`, implicit `Drop` glue, or scalar niche `validRange` from `SpecConeEq` allows a specification edit with byte-identical `hot_ref` source and identical `(size, align, field0Off)` to silently invalidate a previously proved `TotalMirAsmEquiv` theorem.

## Boundaries

- **Pre-link `SHF_EXCLUDE` vs. post-link `--gc-sections` `.debug_anneal_sites`, explicit-clobber quotes, and `extern_queries.optimized_mir` (`known not to apply` in v1 prototype; resolved in [`postlink-gc-sections-debug-tombstone-attestation-and-speccone-pointee-closure`](../postlink-gc-sections-debug-tombstone-attestation-and-speccone-pointee-closure/REPORT.md)):** `support/anneal_driver_prototype.rs` emits `SHF_EXCLUDE` `.anneal.asm_sites` on `.rcgu.o`/`.lto.rcgu.o`, hooks only `providers.queries.optimized_mir` (`LocalDefId`, missing prebuilt sysroot `libcore` `stdarch` `asm!`), and does not strip `"` from explicit `InlineAsmRegOrRegClass::Reg` clobber names inside `.asciz`. For post-link ELF attestation under `-Wl,--gc-sections`, `--icf=all`, and `stdarch` inlining, use `anneal_driver_v2.rs` (`.debug_anneal_sites,"",@progbits` + `extern_queries.optimized_mir` + `verifyLiveAsmSymbolCoverage`).
- **Pointee, compound-type, `FnPtr`-ABI, foreign-`Static`, and `DefIndex`-shift closure in v1 `SpecConeCollector` (`known not to apply` in v1 prototype; resolved in [`postlink-gc-sections-debug-tombstone-attestation-and-speccone-pointee-closure`](../postlink-gc-sections-debug-tombstone-attestation-and-speccone-pointee-closure/REPORT.md)):** `support/anneal_driver_prototype.rs` recurses only into `ty::Adt` field types (`10/18` recall across the expanded 18-vector suite) and leaves HIR `DefId(0:NN)` indices unscrubbed when unrelated items are inserted above the root function; `SpecConeCollector` v2 (`ty.walk()`, `PlaceRef::ty`, `fn_abi_of_fn_ptr`, `GlobalAlloc::Static` closure, and `DefIndex` scrubbing) closes all `18/18` vectors with `0/5` false positives.
- **Cross-language Linker-Plugin ThinLTO (`-C linker-plugin-lto` with Clang C/C++ bitcode) (`not examined`):** Probe 2 tested `rustc`'s in-process `-C lto=thin` and `-C lto=fat` across Rust `.rlib` graphs; when `-C linker-plugin-lto` defers bitcode compilation to `lld`'s `LTOBackend`, `.anneal.asm_sites` verification must run on `lld --save-temps` `.lto.o` outputs or post-link ELF sections rather than `rustc` `-C save-temps` `.rcgu.o` files.
- **Trait-object dynamic dispatch (`InstanceKind::Virtual` open-world vtables) inside `SpecConeHash` (`known not to apply` without closed-world whole-crate sealing):** When `hot_ref` invokes a method on `&dyn Trait`, `SpecConeCollector` hashes the `Virtual(def_id, vtable_idx)` call signature (`line 1158`), because the concrete implementor is caller-supplied at runtime rather than fixed by `hot_ref`'s static definition cone.
- **Relying on `rust-lld --icf=safe` to preserve `#[unsafe(naked)]` function-pointer inequality under `-C llvm-args=-addrsig` (`known not to apply`):** As established in Section 2.2 (`lto_off_cgu_1_icf_safe_addrsig`), `#[unsafe(naked)]` symbols lowered via `ModuleInlineAsm` are omitted from `.llvm_addrsig` and folded even under `--icf=safe` when `-addrsig` is active; programs requiring distinct naked-function addresses must pass `-Wl,--keep-unique,<symbol>` or `-Wl,--icf=none`.
- **GNU `ld.bfd 2.47` `--icf` support (`unsupported`):** `ld.bfd 2.47` rejects `--icf=none`, `--icf=safe`, and `--icf=all` with `unrecognized option`.
- **Mach-O (`SeparatorString = ";"`, Darwin `RISCVMCAsmInfoDarwin` `SeparatorString = "%%"`) and MSVC COFF `cr_zero_drift` behavior (`not examined`):** All `cr_zero_drift` `\r` + `.space 0 <CMT>` invariance measurements ran on ELF targets (`x86_64-unknown-linux-gnu`, `aarch64-unknown-linux-gnu`, `riscv64gc-unknown-linux-gnu`). While `TargetInstrInfo::getInlineAsmLength` and `AsmLexer::LexToken` (`case '\r'`) are target-independent in LLVM 22–23, Mach-O/COFF section flags replace `"e",@progbits` (`SHF_EXCLUDE`).
- **Future upstream `rustc_private` query/type churn beyond `1.102.0-nightly` (`unknown`):** Because `rustc_driver` interfaces are internal (`#![feature(rustc_private)]`), toolchain upgrades require re-checking the five version-gated shims documented under **Applicability**.

## Evidence

### 1. Primary Upstream Source Citations
- **`rust-lang/rust`** (`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65` `1.98.0-nightly`, `58cf8f9c35b355199727627d07ae34a4e2846d67` `1.99.1`, `3ef0c22cdb86ac42dc6b8f0f1ec36857daa6f2a1` `1.102.0-nightly`):
  - `compiler/rustc_interface/src/{interface.rs:39, 348, 476; passes.rs:898, 980-985}`: `Config::override_queries` and `DEFAULT_QUERY_PROVIDERS`.
  - `compiler/rustc_driver_impl/src/lib.rs:172` (`1.102.0-nightly`): `run_compiler` $\to$ `compiler_entrypoint` transition.
  - `compiler/rustc_lint/src/builtin.rs:2797-3035`: `AsmLabels` (`NAMED_ASM_LABELS`, `BINARY_ASM_LABELS`) AST lint pass running prior to MIR queries.
  - `compiler/rustc_monomorphize/src/partitioning.rs:700, 816-818`: single-CGU placement of `MonoItem::GlobalAsm`.
  - `compiler/rustc_codegen_llvm/src/asm.rs:85-125, 188-255`: explicit-clobber `op_idx` skipping (`Out { place: None }`) and `$` $\to$ `$$` escaping on `InlineAsmTemplatePiece::String`.
  - `compiler/rustc_codegen_ssa/src/mir/naked_asm.rs:18-58, 145-255`: `codegen_naked_asm` delegation to `cx.codegen_global_asm`.
  - `compiler/rustc_codegen_llvm/src/back/lto.rs:212-338` & `compiler/rustc_llvm/llvm-wrapper/Linker.cpp:25-43`: FatLTO `costliest_module` `DstM` selection, `serialized_modules.sort_by` alphabetical ordering (`line 301`), and `LLVMRustLinkerAdd`.
  - `compiler/rustc_abi/src/lib.rs:1644-1677, 1791-1820, 1970-2025` & `compiler/rustc_middle/src/ty/{instance.rs:562, 789; normalize_erasing_regions.rs:41-67}`: `FieldsShape`, `Variants`, `BackendRepr::ScalarPair` transition, `Instance::try_resolve`, and `Instance::resolve_drop_glue`.
- **`rust-lang/llvm-project`** (`1b9c0d5ff9bbe7634aead059efe6b11a7eeba145` LLVM `23.1.1` & `0a5579eb649d3634a9c30ac873300cc2944fa070` LLVM `23.1.5`):
  - `llvm/lib/CodeGen/TargetInstrInfo.cpp:113-149` & `llvm/lib/Target/RISCV/RISCVInstrInfo.cpp:1988-1993`: `getInlineAsmLength` `\n`/`;`/`.space` scanner and RISC-V `getInstSizeInBytes` delegation.
  - `llvm/lib/MC/MCParser/AsmLexer.cpp:313, 349-372, 898-906`: `\r` `EndOfStatement` lexing, `\r` comment termination, and `doHexLookAhead` decimal directional label parsing.
  - `llvm/lib/Linker/IRMover.cpp:1563-1582`: `!IsPerformingImport` `appendModuleInlineAsm` concatenation vs. ThinLTO `CollectAsmSymvers`.
  - `llvm/lib/CodeGen/AsmPrinter/AsmPrinter.cpp:613-627, 3120-3130`: `doInitialization` module-inline-asm emission ahead of all functions and `EmitAddrsig` `M.global_values()` traversal.
  - `lld/ELF/ICF.cpp:161-235` & `lld/ELF/Driver.cpp:849-856, 2688-2752`: `isEligible`, `markAddrsig` `SHF_EXECINSTR` bypass under `--icf=all`, and `addrsigSec == nullptr` fallback under `--icf=safe`.
- **`joshlf/anneal`** (`c131b320eeeb26ef692e5afd5ec8db49ee518613`): `trusted/rustc-capture/src/driver.rs:25-152` and `THREAT_MODEL.md:58-281`.

### 2. Preserved Standalone Artifacts (`support/`, Observed `2026-11-21` on Linux `x86_64`)

| Artifact Path | SHA-256 | Basis & Summary |
| :--- | :--- | :--- |
| [`support/anneal_driver_prototype.rs`](support/anneal_driver_prototype.rs) | `043adeae5acfcc0ff49ce2bf5beacb1ae4400332c104c1cf8aa3f8a8acb93a46` | **execution**: Zero-dependency `1,281`-line `rustc_driver` implementing both `override_queries` `InlineAsm` rewriting (`cr_zero_drift`, `ifndef_macro`, `multiline_pushsection`, `mir_built_cr`) and `TyCtxt` `SpecConeCollector` across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly`. |
| [`support/probe_driver_cgu_and_invariance.py`](support/probe_driver_cgu_and_invariance.py) | `6a958719d0bc3f930790aaa436d74d6b6e68973fe65d3560a0229794afdb953e` | **execution**: Reproduces `cgu=16` & `.rmeta` `global_asm!` crashes + `${:uid}` CGU reset, verifies `16`-CGU + dual-nonce `.rmeta` attestation, and runs the 3-ISA (`x86_64`, `aarch64` `N=5,000`, `riscv64gc` `N=900`) `.text` SHA-256 invariance suite. |
| [`support/probe_1_driver_cgu_results.json`](support/probe_1_driver_cgu_results.json) | `a0ef2267832c2db8d0c9b2a5e25602d7de45f2141954efa971badb00c3dba87c` | **execution**: Recorded JSON output across `1.98.0-nightly`, `1.99.1`, and `1.102.0-nightly`. |
| [`support/probe_lto_global_asm_and_icf.py`](support/probe_lto_global_asm_and_icf.py) | `4e141b0e9b8037bbfce53da69a03df72842c27e1a355a2712d2b6cc886fb9ff7` | **execution**: Runs the `{lto=off, thin, fat} × {cgu=1, 16}` cross-crate `GlobalScopeAsm` (`IRMover`) matrix and `{--icf=none, safe, all}` (`rust-lld` + `-addrsig` vs. `ld.bfd 2.47`) matrix. |
| [`support/probe_2_lto_icf_results.json`](support/probe_2_lto_icf_results.json) | `fc1a458c4e09937af81ebc02b53aa8f892fd4e639b4cc21b909faa58fa53aa36` | **execution**: Recorded JSON output across `1.99.1` and `1.102.0-nightly`. |
| [`support/probe_tyctxt_speccone_10vectors.py`](support/probe_tyctxt_speccone_10vectors.py) | `df413a62ebf5c20b4470f5d45bbdf95e2dfb9a1fe16379683579e273df0a58a1` | **execution**: Evaluates `SpecConeCollector` vs. naive token hashing across `V01`–`V10` indirect tampering vectors and `C01`–`C04` benign controls. |
| [`support/probe_3_speccone_results.json`](support/probe_3_speccone_results.json) | `5cc979d81f839cf49744c2bcd9b24c4112ecd267ac1f66677ed1c7863965ac18` | **execution**: Recorded JSON output (`10/10` recall, `0/4` false positives across all 3 toolchains). |
| [`support/MultiCguAttestationAndSpecCone.lean`](support/MultiCguAttestationAndSpecCone.lean) | `a45d3faa89a60730b301d5eb8777f5a16bc012dca12e31e98cf08e2aa87690e9` | **execution + derived**: `795`-line (`32.2 KB`) `Init.*`-only Lean `v4.34.1` mechanization of all 9 soundness and counterexample theorems (`0` `sorry`, `0` warnings, `1.46 s` warm elaboration; axioms strictly within `{propext, Quot.sound}`). |

## Revalidation

Run the following self-contained commands from the package directory (all temporary build artifacts use `tempfile.TemporaryDirectory()` and clean up automatically):

1. **Kernel-check all 9 Lean `v4.34.1` theorems (`0` `sorry`, synchronous kernel TC):**
   ```bash
   elan run leanprover/lean4:v4.34.1 lean -DElab.async=false -Ddebug.skipKernelTC=false \
     support/MultiCguAttestationAndSpecCone.lean
   ```
   Verify exit code `0` and confirm every `#print axioms` line lists only subset(s) of `{propext, Classical.choice, Quot.sound}` with zero `sorryAx`.
2. **Re-run Probe 1 (`rustc_driver` `cgu=16`, `.rmeta`, and 3-ISA `.text` SHA-256 invariance):**
   ```bash
   python3 -B support/probe_driver_cgu_and_invariance.py --toolchains nightly-2026-06-01 1.99.1 nightly
   ```
   Confirm `cr_zero_drift_exact_sha256_parity == true` across `x86_64`, `aarch64_N5000`, and `riscv64gc_N900`, `both_up_and_down_nonces_present == true`, and `upstream_lint_warnings == 0`.
3. **Re-run Probe 2 (ThinLTO / FatLTO `GlobalScopeAsm` and `rust-lld` / `ld.bfd` `--icf` matrix):**
   ```bash
   python3 -B support/probe_lto_global_asm_and_icf.py --toolchains 1.99.1 nightly
   ```
   Check whether future LLVM revisions isolate `ModuleInlineAsm` across FatLTO modules (`lto_fat_cgu_1.downstream_macro_vs_upstream_never_inline`) or emit `#[unsafe(naked)]` symbols into `.llvm_addrsig` (`lto_off_cgu_1_icf_safe_addrsig.naked_folded`).
4. **Re-run Probe 3 (`TyCtxt` `SpecConeHash` 10-vector tampering + 4-control suite):**
   ```bash
   python3 -B support/probe_tyctxt_speccone_10vectors.py --toolchains nightly-2026-06-01 1.99.1 nightly
   ```
   Confirm `tamper_detected == 10` and `benign_false_positives == 0` on every toolchain.
