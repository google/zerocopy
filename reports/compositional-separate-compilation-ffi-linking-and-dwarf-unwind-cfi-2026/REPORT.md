# Compositional Separate Compilation, FFI Trust Boundaries, Open-Module Contracts, and DWARF/LSDA Unwind CFI Verification

## Summary

Whole-program verification of a single closed Rust crate is insufficient for systems software: real deployments link multiple independently compiled Rust crates (`rlib`s), C FFI object files (verified by CompCert or VST), and shared runtime libraries (`core`, `alloc`, `compiler_builtins`), while relying on zero-cost stack unwinding (`panic = "unwind"`) across DWARF `.eh_frame` Call Frame Information (CFI) and `.gcc_except_table` Language-Specific Data Areas (LSDA), and interacting with external or opaque operations whose implementations lie outside the verified source translator. When a closed-crate refinement model defines a top-level theorem (`CrateTheorem`) over a flat list of verified functions (`VerifiedFn`) and models external calls via an unparameterized foreign bridge (`TCBItem.foreignBridge (name : String) (bridge : Compiler MirLang AsmLang)`) while omitting unwind landing pads (`UnwindAction`) from its MIR abstract syntax, it leaves multi-crate linking, foreign-function trust accounting, opaque-operation preservation, and stack unwinding unverified.

This report synthesizes five closely connected verification axes into a unified architectural reference and mechanized proof suite:

1. **Compositional Separate-Compilation & Multi-Language Linking (`OpenModule` and `Module.link`)**:
   Evaluating seven major compositional compiler-verification frameworks (`CompCert` `Linking.v`, `CompCertX`, `SepComp`, `Compositional CompCert`, `CompCertO`, `CCAL`, and `DimSum`), we design a lightweight open-module extension (`OpenModule`, `FnSig`, `Module.link`) mechanized in Lean 4.34.1 (`support/track8_compositional_and_unwind_cfi_probe.lean`) that avoids Kripke-world step-indexing while supporting **horizontal composition** across crates (`horizontal_refinement_composition`), **syntactic pass commutation** across lowering (`compile_link_commutes`), **end-to-end separate compilation** (`end_to_end_separate_compilation`), and **sound FFI linking** that discharges `TCBItem.foreignBridge` whenever a CompCert/VST C proof supplies the imported contract (`verified_c_bridge_discharges_tcb`). We also prove two negative linking canaries (`canaryA_unsound_refinement` for ABI register clobbers and `canaryB_unsound_refinement` for lifetime-violating FFI callbacks).
2. **Upstream Soundness Bug in `rustc_codegen_cranelift` (`UnwindAction::Terminate`) and the Two-Phase Itanium ABI Repair**:
   By inspecting `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`) at `compiler/rustc_codegen_cranelift/src/abi/mod.rs:910` and `compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:177-184`, we found that Cranelift tags `UnwindAction::Terminate(_)` (`Reason::Abi` at `nounwind` FFI boundaries and `Reason::InCleanup` inside destructors run during unwinding) with `EXCEPTION_HANDLER_CLEANUP` (`0`), emitting `cs_action_entry = 0` (`EHAction::Cleanup`) in `.gcc_except_table` instead of a negative filter (`ttype_index = -1`, `EHAction::Filter`). Under the two-phase Itanium C++ ABI (`_Unwind_RaiseException` + `rust_eh_personality` in `library/std/src/sys/personality/gcc.rs:212-275`), we prove in `cranelift_bug_phase1_misses_terminate_without_outer_catch` (`support/round2_track6_probe.lean`) that Phase 1 (`_UA_SEARCH_PHASE`) treats `cs_action_entry = 0` as a pure cleanup (`_URC_CONTINUE_UNWIND`) rather than a handler (`_URC_HANDLER_FOUND`). Consequently, when no outer `catch_unwind` frame exists on the stack, Phase 1 terminates with `_URC_END_OF_STACK` and **never runs Phase 2 (`_UA_CLEANUP_PHASE`)**, skipping intermediate `Drop` destructors and the `Terminate` landing pad. We formalize the two-phase Itanium unwinder (`runTwoPhaseUnwind`), repair Cranelift's LSDA emission via `EXCEPTION_HANDLER_TERMINATE_FILTER` (`ttypeFilter = -1` / `0x7f` SLEB128 pointing to a `0` entry in the TypeInfo table), and prove both single-phase and two-phase refinement soundness (`unwind_refinement_sound`, `repaired_filter_phase1_and_phase2_sound`) alongside a double-panic abort canary (`canaryC_unsound_refinement`).
3. **DWARF `.eh_frame` Call Frame Information (`CFI`) Verification on x86-64 and AArch64 (`PACIASP`/`AUTIASP`)**:
   We mechanize an executable DWARF `.eh_frame` CFI state machine (`CFIInstr`, `CFIRow`, `evalCFIStream`) covering x86-64 and AArch64 prologue/epilogue instructions, including ARMv8.3-A Pointer Authentication (`DW_CFA_AARCH64_negate_ra_state` for `PACIASP`/`AUTIASP`), pre-indexed `STP x29, x30, [sp, #-32]!`, callee-saved `STP x19, x20, [sp, #16]`, and post-indexed `LDP`. We prove that valid CFI tables reconstruct the exact caller `SP`, `FP`, `LR`, and callee-saved registers at every instruction boundary (`verify_cfi_table_sound`, `aarch64PrologueEpilogueCfi_sound`) and prove three negative canaries (`canaryD_cfi_rejects_mismatch`, `canary_missing_window_save_breaks_pac_cfi`, and `canary_corrupted_lr_detected_by_autiasp`).
4. **FFI Specification and Trust Patterns Across Rust, CompCert, and CakeML**:
   A foreign-function interface is not a single proof boundary, but a six-layer stack that must align: (i) the source-language declaration, (ii) the native symbol and calling convention, (iii) the abstract semantic contract, (iv) the frame and resource invariants the call must preserve, (v) the concrete foreign implementation proof or trust assumption, and (vi) the execution environment that binds and runs that implementation (`support/ffi-specification-trust-patterns-2019-2026/trust-layer-matrix.json`). Rust `extern` blocks provide unchecked import declarations without implementation bodies; CompCert 3.18 (`extcall_sem`, `extcall_properties`) and CakeML (`ffiScript.sml`, `basis_ffiScript.sml`, and the PLDI 2019 Silver verified-processor syscall refinement) demonstrate how to separate abstract relational/oracle contracts from concrete implementation refinement.
5. **Modular Foreign Contracts (`VeriFFI`, `RustCompCert`, `VST`), Artifact Admission (`Trivet`, `EquiVM`), and Semantic Preservation with Unsupported/Opaque Operations**:
   `CertiRocq/VeriFFI` (`7e8cd8e7b631be066407f86c82ff60b6fc63ae0b`) and `SJTU-PLV/CompCert` (`e3d03ed822a7aaf452b7022c347187ed1efc1c12`) separate pure functional models and isomorphism bridges from VST `semax_body` / `semax_prog_rule` proofs and open-simulation query/reply continuations. `Trivet` (`arXiv:2609.19583v1`) and `EquiVM` (`arXiv:2607.26306v1`, `argotorg/EquiVM@fc74a6466b92113a6fe16d577de0f553ee46f7cf`) expose critical artifact-admission boundaries around UB-erasing refinement directions, out-of-gas/revert allowances, and `native_decide` / `Trusted.lean` dependency closures. Finally, our analysis of unsupported and opaque operations (`support/semantic-preservation-unsupported-opaque-operations/technique-matrix.json`) establishes why "opaque" is not synonymous with an uninterpreted pure function and defines a four-case semantic policy (rejected, modeled relationally, assumed specification, or erased with an irrelevance theorem).

---

## Applicability

This report applies to the following pinned systems, formal developments, and primary publications:

- **Lean 4 (`leanprover/lean4`)** at `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) for the standalone mechanized compositional-linking, two-phase Itanium unwind, and DWARF `.eh_frame` CFI probes (`support/track8_compositional_and_unwind_cfi_probe.lean` and `support/round2_track6_probe.lean`). In these probes, the closed-crate baseline refinement model (`Language`, `Outcome`, `StepResult`, `Compiler`, `Compiler.SoundOn`, `Compiler.Verified`, `TCBItem`, `VerifiedFn`, `Crate`, `CrateTheorem`) and MIR terminator model (`Terminator`, `MirState`, `evalMirTerminator`) are defined self-contained inline.
- **Rust Compiler (`rust-lang/rust`)** at commits `58cf8f9c35b355199727627d07ae34a4e2846d67`, `8006091eb71ae7d9e9bccb66c6122c9d68af4466`, and `49d734536222bf28bb6d07d885b3a81d145981da`, specifically:
  - `compiler/rustc_middle/src/mir/terminator.rs` (`UnwindAction::Continue`, `UnwindAction::Unreachable`, `UnwindAction::Terminate(UnwindTerminateReason)`, `UnwindAction::Cleanup(BasicBlock)`).
  - `compiler/rustc_codegen_cranelift/src/abi/mod.rs:885-922` (lowering of `UnwindAction::Cleanup` and `UnwindAction::Terminate`).
  - `compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:14-210` (`EXCEPTION_HANDLER_CLEANUP`, `UnwindContext`, `.eh_frame` and `.gcc_except_table` emission via `gimli::write`).
  - `library/std/src/sys/personality/gcc.rs:1-315` (`rust_eh_personality`, `EHAction::None`, `EHAction::Cleanup`, `EHAction::Catch`, `EHAction::Filter`, `EHAction::Terminate`, `find_eh_action`).
  - `library/std/src/sys/personality/dwarf/eh.rs` (LSDA header, call-site table, and action-record decoding).
- **Rust Reference (`rust-lang/reference`)** at commit `ad35aca481751a06afeb23820a672b0f3b11a476` (paired with `rust-lang/rust@14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`, `nightly`), specifically `src/items/external-blocks.md` and `src/items/functions.md`.
- **Wasmtime & Cranelift (`bytecodealliance/wasmtime`)** at commit `87282b8fd77fa9fbba6caadb0be690bedec2dc64`, specifically `cranelift/codegen/src/isa/unwind/systemv.rs` and `cranelift/codegen/src/isa/aarch64/inst/unwind/systemv.rs`.
- **CompCert (`AbsInt/CompCert`)** version 3.18 at commit `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (`common/Linking.v`, `common/Smallstep.v`, `common/Events.v`, `common/AST.v`, `driver/Complements.v`).
- **CakeML (`CakeML/cakeml`)** at commit `31b72d0003620a2ee8c4374caa00a483e1e450ec` (`semantics/ffi/ffiScript.sml`, `basis/basis_ffiScript.sml`), together with Andreas Lööw et al., *Verified Compilation on a Verified Processor*, PLDI 2019 (`DOI 10.1145/3314221.3314622`).
- **VeriFFI (`CertiRocq/VeriFFI`)** at commit `7e8cd8e7b631be066407f86c82ff60b6fc63ae0b` (`README.md`, `library/modelled.v`, `generator/FnDesc.v`, `c/spec_int63.v`, `c/verif_int63.v`, `_CoqProject`, and submodule gitlinks to `CertiCoq/certicoq@f0e1554d57fa683829c253570995e71b70e0083f` and `CertiGraph/CertiGraph@a2db4cf823730a104ddbde7f170627a47fc2f1b7`), together with Joomy Korkut, Kathrin Stark, and Andrew W. Appel, *VeriFFI: Verified Foreign Function Interface for Coq*, POPL 2025 article 24 (`DOI 10.1145/3704860`).
- **RustCompCert (`SJTU-PLV/CompCert`)** at commit `e3d03ed822a7aaf452b7022c347187ed1efc1c12` (`common/Smallstep.v:1572-1603`, `driver/Compiler.v:1309-1315`) and **VST (`PrincetonUniversity/VST`)** at commit `3c37c2e2b574e23aee8fdd1684aa0ffed227491e` (`veric/semax_prog.v:1967-1989`).
- **Trivet (`arXiv:2609.19583v1`)** (Definition 2.1, §§3.1–3.4; author implementation artifact not identified in bounded retrieval) and **EquiVM** (`arXiv:2607.26306v1` and repository `argotorg/EquiVM@fc74a6466b92113a6fe16d577de0f553ee46f7cf`, declaring Lean `4.29.0` with resolved manifest pins `lefterislazar/EVMLean@fd4f5e6d6d6b4a18eb73f5a71ae2df909ac2b542` and `leanprover-community/mathlib4@8a178386ffc0f5fef0b77738bb5449d50efeea95`).

---

## Findings

### 1. Compositional Separate Compilation and Multi-Language FFI Linking

`Basis: analysis of CompCert Linking.v, CompCertX, SepComp, Compositional CompCert, CompCertO, CCAL, and DimSum + machine-checked proofs in support/track8_compositional_and_unwind_cfi_probe.lean`

#### 1.1 Comparison of Compositional Compiler Verification Architectures

To determine how a Rust-to-assembly verification framework should verify multi-crate Rust binaries and C FFI object linking without polluting its trusted core with heavy step-indexed Kripke machinery, Table 1 compares seven established compositional compilation frameworks.

| Framework | Core Mechanism | Cross-Module / Cross-Language Linking | Mutual Recursion & Callbacks | Proof Overhead & Fit |
| :--- | :--- | :--- | :--- | :--- |
| **CompCert 2.7+ (`Linking.v`)** | Syntactic `Linker` typeclass + pass-commutation diagram: $\mathcal{C}(M_1) \bowtie \mathcal{C}(M_2) \sqsupseteq \mathcal{C}(M_1 \bowtie M_2)$ | Homogeneous C / Asm modules compiled by the same pass pipeline | Full mutual recursion after syntactic link | **Very low overhead**: ideal for linking separately compiled crates that share the same backend |
| **CompCertX** (Gu et al., POPL 2015) | Per-function contextual refinement parameterized by abstract kernel state | Links C/Asm layers into verified OS kernels (CertiKOS) | Stratified layers only (**no callbacks** from callee to caller) | Too restrictive for Rust traits, closures, or FFI callbacks |
| **SepComp** (Beringer et al., ESOP 2014) | Interaction semantics (`AtExternal` / `AfterExternal` cores) + structured memory injections | Links CompCert C with VST separation-logic proofs | Supports callbacks via structured injection growth | Moderate complexity; requires threading CompCert block injections across every step |
| **Compositional CompCert** (Stewart et al., POPL 2015) | Interaction semantics + rely-guarantee memory protocols | Arbitrary CompCert-compatible languages | Full mutual recursion and reentrant callbacks | **High complexity**: broke backward simulation and required rewriting every pass proof |
| **CompCertO** (Koenig & Shao, POPL 2021) | Open simulations parameterized by Kripke **simulation conventions** ($\mathbb{R} : A \leftrightarrow B$) | Heterogeneous C + hand-written Asm with calling-convention adapters | Full mutual recursion via horizontal/vertical simulation composition | Clean algebraic structure; simplified non-Kripke variant fits an outcome-based `Language` record directly |
| **CCAL** (Gu et al., POPL 2018) | Certified Concurrent Abstraction Layers with thread-local rely-guarantee | Concurrent C + assembly primitives | Stratified concurrent layers | Best suited for low-level spinlocks/schedulers rather than general Rust crate graphs |
| **DimSum** (Sammler et al., POPL 2023) | Event-based angelic/demonic module transitions (`Spec` / `ModTrans`) | Truly heterogeneous (Rec + Asm + custom DSLs without shared memory type) | Arbitrary reentrant cross-language calls | **Direct match** for angelic/demonic `StepResult.choice (.angelic / .demonic)` semantics |

#### 1.2 The `OpenModule` and `Module.link` Architecture (`support/track8_compositional_and_unwind_cfi_probe.lean:45-615`)

When a verification framework models nondeterminism via an `Outcome` record (combining a demonic failure flag with an angelic value set) and `StepResult.choice (.angelic / .demonic)`, it can obtain the compositional benefits of `CompCertO` and `DimSum` with **~55 lines of pure definitions**:

1. **Typed Call-Boundary Contracts (`FnSig`, `CallEnv`)**:
   Every exported or imported symbol carries an ABI-aware contract specifying its argument precondition, postcondition over `(args, retVal, preMem, postMem)`, callee-saved register preservation invariant, and stack-frame disjointness.
2. **Open Modules (`OpenModule L`)**:
   An `OpenModule` over a language `L` declares:
   - `imports : List (String × FnSig)` — unresolved external symbols and their assumed contracts,
   - `exports : List (String × FnSig)` — symbols defined by this module and their guaranteed contracts, and
   - `defs : List (String × L.Prog)` — concrete function bodies.
   An `OpenModule` is verified (`OpenModule.Refines M`) when, assuming every imported symbol in `M.imports` satisfies its `FnSig` contract at external call points, every exported definition in `M.defs` satisfies its declared `FnSig` contract and is free of undefined behavior (`WellFormedOn`).
3. **Associative Symmetric Linking (`Module.link`)**:
   Linking two compatible modules $M_1 \bowtie M_2$ (`Module.link M₁ M₂`) unions their definitions and exports while discharging each module's imports that are satisfied by the other module's exports:
   $$\text{imports}(M_1 \bowtie M_2) = (\text{imports}(M_1) \setminus \text{exports}(M_2)) \cup (\text{imports}(M_2) \setminus \text{exports}(M_1))$$

In Sections 1–4 of `support/track8_compositional_and_unwind_cfi_probe.lean`, we machine-check five compositional theorems and two negative linking canaries:
- **`link_associative` (`lines 252-298`)**: Proves that `(M₁ ⋈ M₂) ⋈ M₃` and `M₁ ⋈ (M₂ ⋈ M₃)` produce equivalent linked modules.
- **`horizontal_refinement_composition` (`lines 310-375`)**: Proves that if `OpenModule.Refines M₁` and `OpenModule.Refines M₂` hold and their matching import/export signatures agree (`LinkCompatible M₁ M₂`), then `OpenModule.Refines (Module.link M₁ M₂)` holds automatically.
- **`compile_link_commutes` (`lines 390-445`)**: Proves CompCert's separate compilation diagram—compiling `M₁` and `M₂` independently to assembly and linking the resulting object files (`Module.link (compile M₁) (compile M₂)`) refines compiling the linked source module (`compile (Module.link M₁ M₂)`).
- **`end_to_end_separate_compilation` (`lines 455-510`)**: Combines per-module functional correctness (`OpenModule.Refines`), separate compilation (`Compiler.Verified`), and `compile_link_commutes` to discharge closed-program machine-code safety (`CrateTheorem`) when all imports are resolved (`imports = []`).
- **`verified_c_bridge_discharges_tcb` (`lines 515-555`)**: Shows how `TCBItem.foreignBridge` is eliminated from the TCB when an external C function is accompanied by a machine-checked proof of its `FnSig` against the lowered ABI (`System V AMD64` / `AAPCS64`).
- **Negative Linking Canaries (`lines 560-615`)**:
  - **`canaryA_unsound_refinement`**: Proves that an external C function that computes the right return value in `rax`/`x0` but clobbers a callee-saved register (`rbx`/`x19`) without restoring it violates the ABI boundary contract and corrupts the Rust caller's live local after returning.
  - **`canaryB_unsound_refinement`**: Proves that an FFI callee that stashes a borrowed pointer `&mut T` in a C global variable and dereferences it after the Rust lifetime ends violates frame disjointness and triggers a happens-before data race in `MemState`.

---

### 2. Upstream Soundness Bug in `rustc_codegen_cranelift` (`UnwindAction::Terminate`) and the Two-Phase Itanium ABI Repair

`Basis: direct source inspection of rust-lang/rust @ 58cf8f9c35b355199727627d07ae34a4e2846d67 + machine-checked proofs in support/track8_compositional_and_unwind_cfi_probe.lean and support/round2_track6_probe.lean`

#### 2.1 How Rust MIR Models Unwinding (`UnwindAction`)

In `compiler/rustc_middle/src/mir/terminator.rs`, every potentially unwinding MIR terminator (`TerminatorKind::Call`, `TerminatorKind::Drop`, `TerminatorKind::Assert`, `TerminatorKind::InlineAsm`) carries an `UnwindAction`:

```rust
pub enum UnwindAction {
    /// No action is to be taken. Continue unwinding to the caller.
    Continue,
    /// Unwinding is UB (e.g., `nounwind` guaranteed by callee).
    Unreachable,
    /// Terminate the execution (`core::panicking::panic_nounwind` / `panic_in_cleanup`).
    Terminate(UnwindTerminateReason),
    /// Clean up globals/locals by jumping to the given cleanup basic block.
    Cleanup(BasicBlock),
}
```

The two `UnwindAction::Terminate(reason)` cases are critical for safety:
1. `UnwindTerminateReason::Abi`: The call occurs inside an `extern "C"` (or other non-unwinding ABI) function where unwinding across the FFI boundary is undefined behavior; if a panic reaches this boundary, the runtime must catch it and abort the process (`panic_nounwind_fmt`).
2. `UnwindTerminateReason::InCleanup`: A `Drop::drop` call inside a cleanup landing pad itself panics during stack unwinding; Rust must immediately abort (`panic_in_cleanup`) rather than permitting double-unwinding.

#### 2.2 The Upstream Bug in `rustc_codegen_cranelift`

In `compiler/rustc_codegen_cranelift/src/abi/mod.rs:885-922` (at commit `58cf8f9c35b355199727627d07ae34a4e2846d67`), `rustc_codegen_cranelift` lowers both `UnwindAction::Cleanup(cleanup)` and `UnwindAction::Terminate(reason)` by creating a Cranelift landing-pad block rigged with the **exact same tag**, `EXCEPTION_HANDLER_CLEANUP` (`0`):

```rust
// compiler/rustc_codegen_cranelift/src/abi/mod.rs:889-915
UnwindAction::Cleanup(cleanup) => {
    let landing_pad = fx.bcx.create_block();
    ...
    fx.bcx.set_cold_block(landing_pad);
    fx.bcx.ins().landingpad(landing_pad, EXCEPTION_HANDLER_CLEANUP, &[]);
}
UnwindAction::Terminate(reason) => {
    let landing_pad = fx.bcx.create_block();
    ...
    // BUG: Uses EXCEPTION_HANDLER_CLEANUP (0) instead of a Terminate filter!
    fx.bcx.ins().landingpad(landing_pad, EXCEPTION_HANDLER_CLEANUP, &[]);
}
```

And in `compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:177-184`, when serializing the `.gcc_except_table` Language-Specific Data Area (LSDA) via `gimli::write`, `rustc_codegen_cranelift` emits a `CallSite` entry with no action record (`cs_action_entry = 0`) and an empty Action Table:

```rust
// compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:177-184
// Only cleanup landing pads are supported, so action is always 0.
```

#### 2.3 Why `cs_action_entry = 0` Breaks the Two-Phase Itanium Unwinder (`rust_eh_personality`)

To see why emitting `cs_action_entry = 0` (`EXCEPTION_HANDLER_CLEANUP`) for a `Terminate` landing pad is unsound, examine how `libunwind`'s `_Unwind_RaiseException` interacts with Rust's personality routine `rust_eh_personality` (`library/std/src/sys/personality/gcc.rs:212-275`):

1. **Phase 1 (`_UA_SEARCH_PHASE`)**:
   `_Unwind_RaiseException` walks the stack from top to bottom without modifying registers or running any landing-pad code, querying each frame's personality function (`rust_eh_personality`) to determine whether **any** frame on the stack will catch or terminate the exception (`_URC_HANDLER_FOUND`).
   - In `library/std/src/sys/personality/dwarf/eh.rs`, `find_eh_action` decodes the LSDA `CallSite` entry covering the return address (`ip - 1`).
   - When `cs_action_entry == 0`, `find_eh_action` returns `EHAction::Cleanup(lpad)`.
   - In `library/std/src/sys/personality/gcc.rs:235-248`, during `_UA_SEARCH_PHASE`:
     - `EHAction::None` and **`EHAction::Cleanup(lpad)`** both return **`_URC_CONTINUE_UNWIND`**!
     - Only `EHAction::Catch(lpad)`, `EHAction::Filter(lpad)`, and `EHAction::Terminate` return **`_URC_HANDLER_FOUND`**.
2. **What Happens When No Outer `catch_unwind` Exists on the Stack**:
   Suppose a thread (e.g., a C `pthread_create` worker, a bare-metal interrupt/FFI entry point, or `extern "C" fn` called from C) calls a Rust function compiled by `rustc_codegen_cranelift` that contains `Drop` cleanups and an `UnwindAction::Terminate(Reason::Abi)` guard, with **no** `std::panic::catch_unwind` (`EHAction::Catch`) higher on the stack.
   - Because `rustc_codegen_cranelift` encoded the `Terminate` landing pad with `cs_action_entry = 0` (`EHAction::Cleanup`), `rust_eh_personality` returns `_URC_CONTINUE_UNWIND` during Phase 1 (`_UA_SEARCH_PHASE`)!
   - `_Unwind_RaiseException` reaches the bottom of the stack without seeing `_URC_HANDLER_FOUND`, aborts Phase 1 with `_URC_END_OF_STACK`, and **never executes Phase 2 (`_UA_CLEANUP_PHASE`)**!
   - As a result, neither the intermediate `Drop` cleanup landing pads nor the `Terminate` landing pad itself (`panic_nounwind`) ever execute; control returns `_URC_END_OF_STACK` to `__cxa_throw` / `rust_panic`!

We mechanize this exact two-phase failure in Section 3 of `support/round2_track6_probe.lean`:
- **`cranelift_bug_phase1_misses_terminate_without_outer_catch` (`round2_track6_probe.lean:880-955`)**: Constructs a two-frame call stack where Frame 0 (`inner_fn`) has an active `Drop` cleanup (`UnwindAction::Cleanup`) and Frame 1 (`extern_c_entry`) has an `UnwindAction::Terminate(Reason::Abi)` boundary. When compiled with Cranelift's `cs_action_entry = 0`, Phase 1 search (`unwindPhase1Search`) returns `.noHandlerFound` (`_URC_END_OF_STACK`), skipping Phase 2 entirely (`ranCleanups = []`, `terminatedViaPad = false`), whereas the source MIR semantics runs Frame 0's `Drop` cleanup and terminates at Frame 1's `Terminate` pad.
- **`canaryC_unsound_refinement` (`track8_compositional_and_unwind_cfi_probe.lean:940-995`)**: Proves that if a destructor inside a cleanup landing pad panics and the landing pad's internal call is lowered as `Continue` or a non-terminating cleanup instead of `Terminate(Reason::InCleanup)`, the second exception escapes instead of triggering an immediate deterministic abort (`Outcome.terminated .abort`).

#### 2.4 The Verified Repair: `EXCEPTION_HANDLER_TERMINATE_FILTER` (`ttype_index = -1`)

How does LLVM (`rustc_codegen_llvm` / `llvm/lib/CodeGen/AsmPrinter/EHStreamer.cpp`) encode `UnwindAction::Terminate` in `.gcc_except_table` so that `rust_eh_personality` stops in Phase 1 (`_URC_HANDLER_FOUND`) and installs the `Terminate` landing pad in Phase 2 (`_URC_INSTALL_CONTEXT`)?
- In LLVM IR, `rustc_codegen_llvm` emits `landingpad { ptr, i32 } filter [0 x ptr] zeroinitializer`.
- In `.gcc_except_table`, the `CallSite` entry has `cs_action_entry = 1` (1-based byte offset into the Action Table), pointing to an `ActionRecord` with:
  - `ttype_index = -1` (encoded as `0x7f` in signed LEB128; negative values denote an exception **filter** spec rather than a positive `catch` clause),
  - `next_action = 0` (end of action chain),
  where the filter list in the TypeInfo table (`@TType`) begins with a `0` (null) entry indicating an empty allowed-exception list (`throw()`).
- In `library/std/src/sys/personality/dwarf/eh.rs`, `find_eh_action` sees `ttype_index < 0` and returns `EHAction::Filter(lpad)`.
- In `library/std/src/sys/personality/gcc.rs:242-265`:
  - During Phase 1 (`_UA_SEARCH_PHASE`), `EHAction::Filter(lpad)` returns **`_URC_HANDLER_FOUND`**!
  - During Phase 2 (`_UA_CLEANUP_PHASE`), `_Unwind_RaiseException` first visits every inner `EHAction::Cleanup` frame (`_URC_INSTALL_CONTEXT`), executing each `Drop` landing pad and resuming via `_Unwind_Resume`, and then reaches the `EHAction::Filter(lpad)` frame with `_UA_CLEANUP_PHASE | _UA_HANDLER_FRAME`, returning **`_URC_INSTALL_CONTEXT`** to jump directly to the `Terminate` landing pad (`core::panicking::panic_nounwind` / `panic_in_cleanup`).

We mechanize this repair and prove its soundness:
- **`repaired_filter_phase1_and_phase2_sound` (`round2_track6_probe.lean:960-1045`)**: Proves that lowering `UnwindAction::Cleanup` to `cs_action_entry = 0` (`EHAction::Cleanup`) and `UnwindAction::Terminate` to `cs_action_entry = 1` pointing to `ActionRecord { ttypeFilter = -1, nextActionOffset = 0 }` (`EHAction::Filter`) causes `runTwoPhaseUnwind` to succeed in Phase 1 (`_URC_HANDLER_FOUND`) and execute all inner `Drop` cleanups in LIFO order before installing the `Terminate` landing pad in Phase 2, exactly matching source MIR unwinding semantics.
- **`unwind_refinement_sound` (`track8_compositional_and_unwind_cfi_probe.lean:820-935`)**: Proves general simulation soundness between multi-frame MIR `UnwindAction` execution and `.gcc_except_table` LSDA unwinding across arbitrarily nested `Continue`, `Cleanup`, and `Terminate` frames.

---

### 3. DWARF `.eh_frame` Call Frame Information (`CFI`) and AArch64 `PACIASP`/`AUTIASP` Verification

`Basis: inspection of bytecodealliance/wasmtime cranelift/codegen/src/isa/unwind/systemv.rs @ 87282b8fd77fa9fbba6caadb0be690bedec2dc64 + machine-checked proofs in support/track8_compositional_and_unwind_cfi_probe.lean and support/round2_track6_probe.lean`

#### 3.1 Why `.gcc_except_table` LSDA Soundness Requires Verified `.eh_frame` CFI Tables

The two-phase Itanium unwinder (`_Unwind_RaiseException` and `_Unwind_Resume`) can only locate each caller frame's return address (`ip`) and restore callee-saved registers (`rbx`, `rbp`, `r12`–`r15` on x86-64; `x19`–`x29`, `x30` on AArch64) if the compiler's emitted `.eh_frame` Call Frame Information (CFI) table accurately describes the physical stack layout at **every potentially unwinding instruction offset (`PC`)**. If a single `DW_CFA_def_cfa_offset` or `DW_CFA_offset` directive is missing or off by 8 bytes, `_Unwind_RaiseException` reads a corrupted return address or restores a wrong callee-saved register, subverting both `Drop` safety and control-flow integrity.

#### 3.2 Executable DWARF `.eh_frame` CFI Verifier (`support/track8_compositional_and_unwind_cfi_probe.lean:1005-1560`)

In Section 7 of `support/track8_compositional_and_unwind_cfi_probe.lean`, we formalize the DWARF v4/v5 `.eh_frame` abstract machine:
- **CFA Rule (`CFADef`)**: `CFA = reg(cfaReg) + cfaOffset` (initially `rsp + 8` on x86-64 or `sp + 0` on AArch64).
- **Register Rules (`RegRule`)**: `.sameValue`, `.offset (d : Int)` (stored at memory address `CFA + d`), `.register r`, and `.negateRAState` for ARMv8.3-A Pointer Authentication (`PACIASP`/`AUTIASP`).
- **CFI Instructions (`CFIInstr`)**: `DW_CFA_advance_loc`, `DW_CFA_def_cfa`, `DW_CFA_def_cfa_register`, `DW_CFA_def_cfa_offset`, `DW_CFA_offset`, `DW_CFA_restore`, `DW_CFA_remember_state`, `DW_CFA_restore_state`, and `DW_CFA_AARCH64_negate_ra_state` (`DW_CFA_window_save`, opcode `0x2d`).

We define an executable validator `checkCFITable` that steps the abstract machine instruction-by-instruction across a compiled function's prologue, body, and epilogue, verifying that at every PC offset the DWARF `CFIRow` produced by `evalCFIStream` satisfies `CFIFrameConsistent`:
$$\text{evalCFA}(\text{row}, \text{regs}_{\text{curr}}) = \text{sp}_{\text{caller}} \;\wedge\; \forall r \in \text{CalleeSaved} \cup \{\text{RA}\},\; \text{recoverReg}(\text{row}, r, \text{regs}_{\text{curr}}, \text{mem}_{\text{curr}}) = \text{regs}_{\text{caller}}(r)$$

We prove two theorems in `support/track8_compositional_and_unwind_cfi_probe.lean`:
- **`verify_cfi_table_sound` (`lines 1365-1485`)**: Proves that whenever `checkCFITable prog cfiStream = true`, unwinding from any instruction PC in `prog` via `unwindStepWithCFI` recovers the exact caller stack pointer `callerSP`, return address `callerRA`, and all callee-saved registers.
- **`canaryD_cfi_rejects_mismatch` (`lines 1490-1560`)**: Proves that if a prologue pushes a register (`sub sp, sp, #16`) but the `.eh_frame` stream omits or misstates the `DW_CFA_def_cfa_offset` delta, `checkCFITable` returns `false` and `unwindStepWithCFI` reads from the wrong stack address.

#### 3.3 Multi-Block AArch64 `PACIASP`/`AUTIASP` Pointer Authentication + FP/LR CFI Verification (`support/round2_track6_probe.lean:1050-1420`)

On modern AArch64 targets (`aarch64-unknown-linux-gnu` and `aarch64-apple-darwin` with `-Zbranch-protection=pac-ret`), function prologues sign the link register `x30` (`LR`) using the stack pointer `sp` as a cryptographic modifier before pushing it to the stack (`PACIASP`), and authenticate `x30` against `sp` after popping it in the epilogue (`AUTIASP`):

| PC Offset | AArch64 Instruction | Architectural Effect | Required DWARF `.eh_frame` CFI Directives |
| :---: | :--- | :--- | :--- |
| `0` | `paciasp` | `x30 := signPAC(x30, sp)` (`ra_sign_state := 1`) | *(after `0`)* `DW_CFA_advance_loc 1; DW_CFA_AARCH64_negate_ra_state` |
| `1` | `stp x29, x30, [sp, #-32]!` | `sp := sp - 32; mem[sp] := x29; mem[sp+8] := x30` | *(after `1`)* `DW_CFA_advance_loc 1; DW_CFA_def_cfa_offset 32; DW_CFA_offset x29, -32; DW_CFA_offset x30, -24` |
| `2` | `mov x29, sp` | `x29 := sp` | *(after `2`)* `DW_CFA_advance_loc 1; DW_CFA_def_cfa_register x29` |
| `3` | `stp x19, x20, [sp, #16]` | `mem[sp+16] := x19; mem[sp+24] := x20` | *(after `3`)* `DW_CFA_advance_loc 1; DW_CFA_offset x19, -16; DW_CFA_offset x20, -8` |
| `4` | `bl callee_that_may_unwind` | Body execution (clobbers `x19`, `x20`, `x29`, `x30`) | *(same row)* |
| `5` | `ldp x19, x20, [sp, #16]` | `x19 := mem[sp+16]; x20 := mem[sp+24]` | *(after `5`)* `DW_CFA_advance_loc 2; DW_CFA_restore x19; DW_CFA_restore x20` |
| `6` | `ldp x29, x30, [sp], #32` | `x29 := mem[sp]; x30 := mem[sp+8]; sp := sp + 32` | *(after `6`)* `DW_CFA_advance_loc 1; DW_CFA_def_cfa sp, 0; DW_CFA_restore x29; DW_CFA_restore x30` |
| `7` | `autiasp` | `x30 := authPAC(x30, sp)` (`ra_sign_state := 0`) | *(after `7`)* `DW_CFA_advance_loc 1; DW_CFA_AARCH64_negate_ra_state` |
| `8` | `ret` | `pc := x30` (trap if `x30` PAC check failed) | *(at `8`)* `CFA = sp + 0`, `ra_sign_state = false` |

In Section 4 of `support/round2_track6_probe.lean`, we model the complete 9-PC AArch64 execution and DWARF CFI table (`aarch64PacFunc`, `aarch64PacCfiStream`) with cryptographic PAC tag signing/authentication (`signPac`, `authPac`, and `authPac_signPac_cancel`) and prove three theorems:
- **`aarch64PrologueEpilogueCfi_sound` (`round2_track6_probe.lean:1280-1350`)**: Proves that at every single PC offset `0..8` (before `paciasp`, after `paciasp`, after `stp x29, x30`, after `mov x29, sp`, during body execution with clobbered `x19`/`x20`/`x29`/`x30`, after `ldp x19, x20`, after `ldp x29, x30`, and after `autiasp`), the DWARF `.eh_frame` unwinder (`unwindAArch64FrameAtPc`) accurately strips the PAC signature when `raSigned = true` and recovers the exact caller `(sp, x29, x30, x19, x20)`.
- **`canary_missing_window_save_breaks_pac_cfi` (`round2_track6_probe.lean:1352-1385`)**: Proves that if the compiler emits `paciasp` in the prologue but omits `DW_CFA_AARCH64_negate_ra_state` in `.eh_frame`, the unwinder fails to strip the PAC tag from the saved `x30` word on the stack (`recoveredLR ≠ callerLR`), causing a fault when jumping to the caller's landing pad.
- **`canary_corrupted_lr_detected_by_autiasp` (`round2_track6_probe.lean:1387-1420`)**: Proves that if a stack buffer overflow overwrites the saved `x30` slot `[sp + 8]` with an attacker-chosen gadget address or if `sp` is pivoted before `autiasp`, `authPac` detects the tag mismatch and traps before `ret` executes.

---

### 4. FFI Specification and Trust Patterns Across Rust, CompCert, and CakeML

`Basis: Rust Reference normative text (rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476); CompCert 3.18 formal source (AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6); CakeML formal source (CakeML/cakeml@31b72d0003620a2ee8c4374caa00a483e1e450ec) and PLDI 2019 published proof architecture; structured matrix in support/ffi-specification-trust-patterns-2019-2026/trust-layer-matrix.json`

#### 4.1 Six Independent Layers of FFI Correctness

A durable FFI proof must answer at least six distinct questions, which can be discharged by different mechanisms and must remain separate in theorem statements and trust accounting (`support/ffi-specification-trust-patterns-2019-2026/trust-layer-matrix.json`):

1. **What does the verified-language program declare?** The declaration fixes the types and source-level permission boundary that the verified caller sees.
2. **Which native definition is actually invoked, and under which calling convention?** Source identity, native symbol identity (`#[link_name]`, Windows import ordinals), ABI (`"C"`, `"C-unwind"`), variadicness, and unwind convention are not interchangeable.
3. **What semantic behavior may the foreign operation exhibit?** This layer describes return values, state updates, observable events, failure, and divergence rather than merely byte transfer at the ABI boundary.
4. **Which resources must it preserve?** A call can return the expected value while corrupting unrelated memory or violating an ownership/frame invariant.
5. **Why does the concrete foreign implementation satisfy that semantic contract?** The answer may be a machine-checked proof, a translation validator, an audited shim, or an explicit trust premise. Omitting the answer does not make the obligation disappear.
6. **What environment connects the verified call site to that implementation?** Link/load resolution, operating-system behavior, device state, filesystem state, and deployment assumptions can remain outside the proved code even when the foreign routine itself has been verified.

#### 4.2 Rust's `extern` Declaration Proves No Foreign Implementation

The Rust Reference (`src/items/external-blocks.md`, blob `e1704556b5f000c019cd04df63e7e04692454c42`, and `src/items/functions.md`, blob `362b39b5733c385a18e20a928d75f960f1cd427e`) specifies that external blocks provide declarations of items not defined in the current crate and describes them as unchecked imports. Functions in an external block have no Rust body. Rust can therefore type-check and compile a call while possessing no implementation whose functional behavior could be proved from the declaration alone.

The declaration carries boundary metadata—whether calling requires an `unsafe` context, the foreign ABI string, unwind boundary semantics (`"C"` vs. `"C-unwind"`), and native-link overrides (`#[link_name]`, ordinal imports)—but not the foreign implementation's semantics. A verifier that imports `extern "C" fn f(x: i32) -> i32` as an arbitrary mathematical function `i32 -> i32` still needs to specify what state, memory, I/O, failure, divergence, and callback behavior the real `f` may exhibit. Furthermore, neither `unsafe` call syntax nor Rust 2024 `safe` foreign declarations inside `unsafe extern` blocks prove the foreign implementation: `safe` shifts responsibility to the declaration author so safe Rust may call it without an `unsafe` block, while the semantic contract still requires the six layers above.

#### 4.3 CompCert's Relational External Calls vs. CakeML's World/Oracle Refinement

CompCert 3.18 (`common/Events.v`, blob `ac8d1bb42e4e9d2e04bc6d7c1c27ea87fbc95564`) and CakeML (`semantics/ffi/ffiScript.sml`, blob `b40698d34360646ffb56e098e15571f99b99d9f4`, and `basis/basis_ffiScript.sml`, blob `4b98525f4f628392a0ec8710a1d4d1394acbffe9`) demonstrate two complementary patterns for making the semantic layer explicit:

- **CompCert (`extcall_sem` and `extcall_properties`)**: Models an external function as a relation over `(globalenv, args, pre_mem, trace, res, post_mem)` rather than a pure function, paired with `extcall_properties` constraining result typing, symbol-environment invariance, valid-block preservation, permission bounds, unchanged non-writable bytes, memory extension/injection commutation, bounded single-step traces, trace receptiveness, and determinism up to trace matching. This separates **the abstract relation describing allowed foreign behavior** from **the frame/simulation proof rules needed to compose that relation with compiler passes**.
- **CakeML (`call_FFI`, `basis_ffi_oracle`, and PLDI 2019 Verified Processor Refinement)**: Stores an `oracle`, an explicit FFI state, and accumulated I/O events in the semantic state. `basis_ffi_oracle` supplies formal behavior for standard calls (`read`, `write`, command-line access, `exit`) and delegates unknown calls to a parameterized `ext` oracle. In *Verified Compilation on a Verified Processor* (Lööw et al., PLDI 2019, Sections 5–6), the authors go one step further: starting from a top-level compiler theorem that assumes external calls behave according to the modeled filesystem, command line, and CakeML calling convention, they define a concrete machine-state-to-FFI-oracle relation and prove that concrete system-call machine code on the Silver processor refines the abstract `call_FFI` interference step. Moving the FFI contract from an assumption into a proved syscall refinement both shrinks the trusted boundary and exposed an inconsistency in an earlier assumption set.

#### 4.4 Orthogonality of ABI and Semantics, Frame Obligations, and Layered Edge Inventories

An ABI governs register/stack transfer, argument/result representation, cleanup, and unwind conventions, whereas semantic correctness governs return values, caller-owned memory preservation, I/O, callbacks, blocking, and divergence. Consequently, a verification architecture should avoid an overloaded "FFI supported" label and distinguish **representable/callable**, **semantically modeled**, and **implementation-validated or trusted**. For every foreign edge, durable evidence should record:
1. Source declaration identity and source-level safety contract;
2. Effective native symbol/binding identity (and reproducible artifact identity where practical);
3. ABI details affecting the call (including unwind and variadic behavior);
4. Abstract semantic contract (state, memory, I/O, failure, divergence);
5. Frame and resource preservation obligations;
6. Whether a concrete foreign implementation is proved/validated against that contract or remains trusted; and
7. Residual link, loader, OS, or deployment assumptions.

---

### 5. Modular Foreign Contracts (`VeriFFI`, `RustCompCert`, `VST`) and Open Execution

`Basis: VeriFFI POPL 2025 publication (DOI 10.1145/3704860) and source (CertiRocq/VeriFFI@7e8cd8e7b631be066407f86c82ff60b6fc63ae0b); RustCompCert source (SJTU-PLV/CompCert@e3d03ed822a7aaf452b7022c347187ed1efc1c12); VST source (PrincetonUniversity/VST@3c37c2e2b574e23aee8fdd1684aa0ffed227491e)`

#### 5.1 Pure Models, Representation Bridges, and C Specifications in `VeriFFI`

VeriFFI (POPL 2025 article 24) translates Coq/Gallina function and constructor types and pure functional models into Verifiable C (VST) function specifications; a user proves that C implementations satisfy those VST specifications, allowing functional clients to rely on their modeled behavior. Hybrid deep/shallow descriptions allow dependent structure to participate in interface generation.

In `CertiRocq/VeriFFI@7e8cd8e7b631be066407f86c82ff60b6fc63ae0b`:
- `library/modelled.v:11-31` (blob `5bfbeae5a773a0c3a4414857d7a752cb5b961881`) separates a primary/model type, a secondary/foreign type, a `Graph` representation predicate, and an `Isomorphism`, using `transparent` and `opaque` annotations to distinguish reflected model-function types from foreign-function types. This annotation defines the representation bridge; it does not eliminate the obligation to prove the C operation's behavior.
- `c/spec_int63.v` (blob `83f86d9968834e15a77b0333c00e8a9ab0473cdd`) defines tagged 63-bit integer encodings and VST function specifications, and `c/verif_int63.v:16,39` (blob `32ba449d0cbaf4decbb0f2ae800e8e7c97e86f99`) provides concrete `semax_body` proofs for addition and multiplication against those specifications.
- At the same time, `README.md` (blob `008e29f029b831407ea387854d09674c5f94c6b8`) explicitly notes that a fully foundational end-to-end connection proof remains work in progress, and `generator/FnDesc.v:88-89` (blob `074d71b74f7f3576e86f9e714a309627d0e72c66`) contains an active `Admitted` `InGraph_list` instance. Thus, the paper interface design, current generator status, local C body proofs, and complete runtime/GC/compiler composition (`CertiCoq/certicoq@f0e1554d57fa683829c253570995e71b70e0083f` and `CertiGraph/CertiGraph@a2db4cf823730a104ddbde7f170627a47fc2f1b7`) must be tracked as distinct evidence items.

#### 5.2 Open Simulations (`SJTU-PLV/CompCert`) and External Safety Propositions (`VST`)

- **Open Simulations Quantifying Over Compatible Foreign Interaction (`SJTU-PLV/CompCert`)**: In `common/Smallstep.v:1572-1603` (blob `027630ae27eaeb805bd1d4e86b2ef70a5bb8d77e`), backward-simulation obligations for open modules require that related calls agree on validity, initial states and final replies are related, and whenever a target state exposes an external call, a related safe source state reaches a matching external query under matching symbol environments; for every matched reply pair, the resumed continuations must re-establish the simulation state relation. `driver/Compiler.v:1309-1315` (blob `7e793bc9dced27222ae7091769f255289745ad6b`) states the Rustlight compilation theorem using this open source/target ordering.
- **VST External Specification Relativity (`PrincetonUniversity/VST`)**: In `veric/semax_prog.v:1967-1989` (blob `874d708d61f1d25c6ae2c1f7be263806cceec1f3`), `semax_prog_rule` concludes whole-program safety relative to `OK_spec Espec`, function-specification matching, and initial-memory conditions. Proving a callee body and proving that the deployment world satisfies `Espec` (or that a callback preserves caller invariants before returning) are separate obligations.

#### 5.3 Derived Requirements for Reusable Function Certificates and Cycle Closure

A reusable function certificate must bind the source and generated body, formal input/output representation, allowed failures, owned resources, import/caller assumptions, and the resumption proposition after each external query/reply:
- **Safe vs. Unsafe API Caller Coverage**: For a safe Rust API, every input obtainable from permitted safe callers must satisfy the certificate's precondition; shrinking the model domain with hidden alignment, initialization, lifetime, or disjointness assumptions is unsound. For an unsafe API, caller preconditions may appear in the contract, provided the caller's proof discharges them.
- **Specialization, Dynamic Dispatch, and Mutual Recursion**: At link time, each import—including implementations selected via trait dictionaries, vtables, function pointers, or specialization—must bind to a proved implementation under the same relation and ABI. Mutually recursive functions require a simultaneous induction or fixed-point proof principle; local certificates that circularly assume one another's safety do not form a closed proof.

---

### 6. `Trivet`, `EquiVM`, and Foreign-Interface Artifact Admission Boundaries

`Basis: Trivet primary paper (arXiv:2609.19583v1); EquiVM primary paper (arXiv:2607.26306v1) and repository source (argotorg/EquiVM@fc74a6466b92113a6fe16d577de0f553ee46f7cf); structured metadata in support/trivet-equvm-and-foreign-artifact-admission-boundaries/source-identities.json and support/trivet-equvm-and-foreign-artifact-admission-boundaries/publication-normalization.json`

#### 6.1 `Trivet`'s Refinement Policy vs. Source-Safety Reflection

`Trivet` (`arXiv:2609.19583v1`, Definition 2.1 and §§3.1–3.4) generates refinement and refutation scaffolds for LLVM IR using LLM-guided search outside the trusted kernel. Its acceptance policy requires Lean kernel checking with zero proof holes, standard axioms only, and unchanged source/target definitions and theorem statement (within a fragment that models integers while excluding `undef`, memory, and floating point, and restricting loops).

Crucially, `Trivet`'s LLVM refinement definition permits **any** target behavior after immediate source undefined behavior (UB) and permits more-defined target values after source `poison`. While standard for optimizing compilers, this refinement direction can accept a safe target program for an **unsafe** source program. Consequently, a source-safety verifier cannot infer source-Rust UB freedom merely from a target-refines-source LLVM translation validation certificate; source-safety certification requires a failure-reflecting refinement relation (where source failure is demonic and preserved backward from target verification). Note that the `Trivet` paper includes no public implementation URL, and bounded repository searches did not locate an author-published artifact.

#### 6.2 `EquiVM`'s `Stele` Refinement Relation, Out-of-Gas Allowance, and Dependency Closure

In `argotorg/EquiVM@fc74a6466b92113a6fe16d577de0f553ee46f7cf` (which names its specification language `Stele`, distinct from the `Sol⁻` name in `arXiv:2607.26306v1`):
- **Refinement Exceptions (`Stele/Refine.lean:82-118, 163-183, 221-233`)**: `runtimeRefinementFor` has two constructors: either (1) a concrete EVM execution paired with a related `Stele` execution and matching outcome (covering return values, account maps, revert/decoding/no-entry outcomes, invalid halt, and static-mode violations), **or** (2) **EVM out-of-gas (`OOG`) with no specification requirement**. `README.md:245-247` also documents that exact gas-cost accounting, event logs/substate, and revert-payload bytes are excluded from comparison. Thus, `runtimeRefinementFor` is a partial/conditional artifact refinement whose out-of-gas escape clause cannot be used to claim unconditional liveness or resource bounds.
- **ERC20 Capstone and TCB (`Examples/ERC20/Correct.lean:344, 953-961`, `Examples/ERC20/Bytecode.lean:299`, `Misc/prompt.md:235-251`)**: `Examples/ERC20/Correct.lean` packages constructor and runtime refinement for ERC20 against `lefterislazar/EVMLean@fd4f5e6d6d6b4a18eb73f5a71ae2df909ac2b542` and `leanprover-community/mathlib4@8a178386ffc0f5fef0b77738bb5449d50efeea95` (pinned in `lake-manifest.json`, whereas `lakefile.toml:47` names a moving branch). Its stated TCB (`README.md:228`) includes `native_decide` evaluation facts (`Examples/ERC20/Bytecode.lean:299`) and permits contract-specific assumptions isolated in `Trusted.lean` (`Misc/prompt.md:235-251`). Admitting any external proof artifact into a verification pipeline therefore requires freezing semantic definitions, auditing the built transitive axiom closure (`#print axioms`), and checking `native_decide` / `Trusted.lean` premises independently of prompt instructions.

---

### 7. Semantic Preservation with Unsupported and Opaque Operations

`Basis: CompCert 3.18 source (AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6, common/Events.v, common/AST.v, driver/Complements.v); CakeML source (CakeML/cakeml@31b72d0003620a2ee8c4374caa00a483e1e450ec) and PLDI 2019; structured comparison in support/semantic-preservation-unsupported-opaque-operations/technique-matrix.json`

#### 7.1 Why "Opaque" Is Not Synonymous with "Uninterpreted Pure Function"

A semantic-preservation theorem (`transf_c_program_preservation` in CompCert `driver/Complements.v`, blob `d3974c2f7c2e5d04f2a3293fa6cfdb1215e5a217`) relates target behaviors to formal source behaviors. When a source translator encounters an operation it does not reduce to a verified implementation, replacing that operation with an **uninterpreted mathematical function** `f : A -> B` is **not** a neutral or conservative choice:
- An uninterpreted function silently asserts **purity** (no memory mutation or I/O), **determinism** (equal inputs always yield equal outputs), **totality/termination** (no divergence or panic), and **context independence** (no dependence on hidden state or environment).
- If the real operation can return nondeterministic results (e.g., `0` or `1`), mutate memory, perform I/O, or diverge, a formal model that permits fewer behaviors than the real operation is an **under-approximation** that makes downstream safety proofs unsound. To transfer a safety theorem from a formal opaque model to real execution, the formal model must **over-approximate** (include all relevant behaviors of) the real operation.
- Conversely, CompCert's `common/AST.v` (blob `007d44afdb4f3262dc147865ed82721f1494d4a4`) explicitly warns that `EF_inline_asm` can invalidate CompCert's semantic-preservation theorem if inline assembly mutates machine state outside the abstract `inline_assembly_sem` interface: preserving a formal placeholder across compiler passes does not prove that the placeholder adequately models the concrete instruction sequence.

#### 7.2 Four-Case Policy for Unsupported and Opaque Operations

As cataloged in `support/semantic-preservation-unsupported-opaque-operations/technique-matrix.json`, a sound verification pipeline must classify every non-reduced or unsupported operation into one of four explicit semantic cases, recording the choice in durable pipeline diagnostics so orchestration cannot silently drop failures:

| Policy Case | Formal Representation | Soundness Requirement & Theorem Impact |
| :--- | :--- | :--- |
| **1. Rejected (Fail-Closed)** | Translation halts or emits a non-success verification result | CompCert's correctness theorem is conditioned on `transf_c_program p = OK tp`; rejecting unsupported constructs preserves full soundness on accepted programs |
| **2. Modeled Relationally** | Target retains an explicit relation/oracle over arguments, pre/post state, nondeterminism, failure, and traces (like `extcall_sem` or `call_FFI`) | Must satisfy frame/simulation laws (`extcall_properties`), and adequacy (behavioral inclusion of the real operation inside the formal relation) must be separately justified |
| **3. Assumed Specification** | Target theorem is parameterized by a named premise or trusted contract (`TCBItem` / `Espec`) | Sound conditional theorem; the undischarged premise must remain visible in the top-level theorem statement and trust inventory |
| **4. Erased or Placeholder-Replaced** | Operation is omitted or replaced by a weaker placeholder | Sound **only** when accompanied by a proof that the erased behavior is semantically irrelevant to the claimed property; otherwise a soundness bug |

---

## Boundaries

1. **Dynamic Linking (`dlopen` / PLT / GOT) vs. Static Relocatable Linking**:
   `Module.link` (`support/track8_compositional_and_unwind_cfi_probe.lean`) models static linking of separately compiled crates (`rlib`) and `.o` object files where symbol resolution is fixed prior to execution. Runtime dynamic loading (`dlopen`) and lazy PLT binding require runtime verification of the loaded shared object's exported `FnSig` table.
2. **Asynchronous Signals (`-fasynchronous-unwind-tables`) vs. Synchronous Call-Site Unwinding**:
   Our `.gcc_except_table` LSDA verifier requires unwind accuracy at synchronous unwind points (`Call`, `Drop`, `InlineAsm`), while our `.eh_frame` CFI verifier (`aarch64PrologueEpilogueCfi_sound`) verifies every instruction PC `0..8` in the prologue and epilogue. However, Rust's semantics does not support unwinding out of asynchronous POSIX signal handlers (`SIGSEGV` / `SIGALRM`) to run `Drop` destructors on interrupted basic-block interiors.
3. **Forced Unwinding (`_UA_FORCE_UNWIND`) and Foreign C++ Exceptions**:
   Our two-phase unwinder (`runTwoPhaseUnwind`) models standard Rust panics and Itanium C++ exceptions caught by `EHAction::Catch` or stopped by `EHAction::Filter` (`ttypeFilter = -1`). POSIX `pthread_cancel` forced unwinding (`_UA_FORCE_UNWIND`) bypasses `EHAction::Catch` in Phase 1 and must still be stopped at `UnwindAction::Terminate(Reason::Abi)` boundaries via `rust_eh_personality`'s `_UA_FORCE_UNWIND` check.
4. **External Framework Replay and Hardware/Concurrency Scope**:
   While `support/track8_compositional_and_unwind_cfi_probe.lean` and `support/round2_track6_probe.lean` were machine-checked in Lean `v4.34.1`, no fresh Coq/Rocq, HOL4, CompCert, CakeML, VST, VeriFFI, or EquiVM builds were executed during the external literature review; `Trivet`'s implementation artifact was not located in bounded retrieval (`not examined`), and `EquiVM`'s transitive axiom closure and `VeriFFI`'s submodule builds were inspected at source level only (`not examined`). Concurrent weak-memory FFI protocols, MMIO/DMA volatile hardware framing, and general dynamic-dispatch cycle checking remain outside the scope of the mechanized probes.

---

## Evidence

1. **Compositional Separate-Compilation and DWARF/LSDA Unwind CFI Lean 4.34.1 Mechanization (`support/track8_compositional_and_unwind_cfi_probe.lean`)**:
   - **Paths**: `support/track8_compositional_and_unwind_cfi_probe.lean` (also staged at `support/compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026/track8_compositional_and_unwind_cfi_probe.lean`).
   - **Lines**: 1,609 | **SHA-256**: `74360333b4f7e7bf0c6f17da95713ebb055471a6e5e17632806c779a62fb9633`.
   - **Key Verified Theorems**: `link_associative`, `horizontal_refinement_composition`, `compile_link_commutes`, `end_to_end_separate_compilation`, `verified_c_bridge_discharges_tcb`, `canaryA_unsound_refinement`, `canaryB_unsound_refinement`, `unwind_refinement_sound`, `canaryC_unsound_refinement`, `verify_cfi_table_sound`, `canaryD_cfi_rejects_mismatch`.
   - **Axiom Audit**: Verified via `#guard_msgs in #print axioms` to depend only on standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`), with zero `sorryAx` and zero custom axioms.
2. **Two-Phase Itanium Unwind Repair and AArch64 `PACIASP`/`AUTIASP` CFI Lean 4.34.1 Mechanization (`support/round2_track6_probe.lean`, Sections 3 & 4)**:
   - **Paths**: `support/round2_track6_probe.lean` (also staged at `support/compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026/round2_track6_probe.lean`).
   - **Lines**: 1,462 | **SHA-256**: `d5049314b0d824b19586324884f5c1a64e3172d391d35c8a4ebfaa52b1ef8771`.
   - **Key Verified Theorems**: `cranelift_bug_phase1_misses_terminate_without_outer_catch`, `repaired_filter_phase1_and_phase2_sound`, `authPac_signPac_cancel`, `aarch64PrologueEpilogueCfi_sound`, `canary_missing_window_save_breaks_pac_cfi`, `canary_corrupted_lr_detected_by_autiasp`.
   - **Axiom Audit**: Verified via `#guard_msgs in #print axioms` to depend only on standard Lean 4 axioms (`propext`, `Quot.sound`), with zero `sorryAx` and zero custom axioms.
3. **Structured Matrices and Source Maps (`support/`)**:
   - `support/ffi-specification-trust-patterns-2019-2026/trust-layer-matrix.json` and `support/ffi-specification-trust-patterns-2019-2026/source-map.json`: Six-layer FFI trust decomposition and exact git blob hashes for `rust-lang/reference@ad35aca481751a06afeb23820a672b0f3b11a476`, `AbsInt/CompCert@74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, and `CakeML/cakeml@31b72d0003620a2ee8c4374caa00a483e1e450ec`.
   - `support/trivet-equvm-and-foreign-artifact-admission-boundaries/source-identities.json` and `support/trivet-equvm-and-foreign-artifact-admission-boundaries/publication-normalization.json`: Exact source coordinates and dependency identities for `Trivet` (`arXiv:2609.19583v1`), `EquiVM` (`arXiv:2607.26306v1`, `argotorg/EquiVM@fc74a6466b92113a6fe16d577de0f553ee46f7cf`), and `CertiRocq/VeriFFI@7e8cd8e7b631be066407f86c82ff60b6fc63ae0b`.
   - `support/semantic-preservation-unsupported-opaque-operations/technique-matrix.json` and `support/semantic-preservation-unsupported-opaque-operations/source-map.json`: Four-case policy matrix and source blob mapping for unsupported and opaque operations across CompCert 3.18 and CakeML.

---

## Revalidation

To typecheck both standalone Lean 4.34.1 proof probes and verify all theorems and `#guard_msgs in #print axioms` checks with zero errors and zero warnings, run from the repository root using Lean `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`):

```bash
lean -j1 -M768 \
  reports/compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026/support/track8_compositional_and_unwind_cfi_probe.lean

lean -j1 -M768 \
  reports/compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026/support/round2_track6_probe.lean
```

Expected output: exit code `0` with empty stdout and stderr for both files.

To verify the SHA-256 digests of the preserved proof probes:

```bash
sha256sum \
  reports/compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026/support/track8_compositional_and_unwind_cfi_probe.lean \
  reports/compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026/support/round2_track6_probe.lean
# Expected:
# 74360333b4f7e7bf0c6f17da95713ebb055471a6e5e17632806c779a62fb9633  reports/compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026/support/track8_compositional_and_unwind_cfi_probe.lean
# d5049314b0d824b19586324884f5c1a64e3172d391d35c8a4ebfaa52b1ef8771  reports/compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026/support/round2_track6_probe.lean
```

When revalidating FFI contracts, external artifact admissions, or opaque-operation handling on updated toolchain pins:
1. Construct a boundary table matching `support/ffi-specification-trust-patterns-2019-2026/trust-layer-matrix.json` requiring an explicit entry for each of the six FFI layers.
2. Audit any external proof artifact (`EquiVM`, `VeriFFI`, `VST`, or `CompCert` bridges) by freezing semantic definitions, replaying the proof closure, and checking `#print axioms` / `Print Assumptions` for `native_decide`, `Admitted`, or contract-specific axioms.
3. Classify every non-reduced operation against the four-case policy in `support/semantic-preservation-unsupported-opaque-operations/technique-matrix.json` (rejected, modeled relationally with over-approximating adequacy, explicitly assumed in the top-level theorem, or erased with a formal irrelevance proof).
