# Compositional Separate Compilation, FFI Linking, and DWARF/LSDA Unwind CFI Verification for Anneal

## Summary

Whole-program verification of a single closed Rust crate is insufficient for
systems software: real deployments link multiple independently compiled Rust
crates (`rlib`s), C FFI object files (verified by CompCert or VST), and shared
runtime libraries (`core`, `alloc`, `compiler_builtins`), while relying on
zero-cost stack unwinding (`panic = "unwind"`) across DWARF `.eh_frame` Call
Frame Information (CFI) and `.gcc_except_table` Language-Specific Data Areas
(LSDA). In `joshlf/anneal` (`e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`),
`trusted/lean/Trusted/Refinement.lean` defines `CrateTheorem` over a flat list
of `VerifiedFn` entries and models external calls via an unparameterized
`TCBItem.foreignBridge (name : String) (bridge : Compiler MirLang AsmLang)`,
while `trusted/lean/Trusted/MirAst.lean` omits unwind landing pads
(`UnwindAction`) entirely.

This report establishes the compositional separate-compilation, multi-language
FFI linking, and two-phase DWARF/LSDA stack-unwinding architecture for Anneal,
mechanized in two standalone Lean 4.34.1 proof artifacts totaling 3,071 lines
with zero `sorryAx` and zero custom axioms
(`support/track8_compositional_and_unwind_cfi_probe.lean` and
`support/round2_track6_probe.lean`):

1. **Compositional Separate-Compilation & Multi-Language Linking (`OpenModule` and `Module.link`)**:
   Evaluating seven major compositional compiler-verification frameworks
   (`CompCert` `Linking.v`, `CompCertX`, `SepComp`, `Compositional CompCert`,
   `CompCertO`, `CCAL`, and `DimSum`), we design a lightweight open-module
   extension for `Trusted/Refinement.lean` (`OpenModule`, `FnSig`, `Module.link`)
   that avoids Kripke-world step-indexing while supporting both **horizontal
   composition** across crates (`horizontal_refinement_composition`),
   **syntactic pass commutation** across lowering (`compile_link_commutes`),
   **end-to-end separate compilation** (`end_to_end_separate_compilation`), and
   **sound FFI linking** that discharges `TCBItem.foreignBridge` whenever a
   CompCert/VST C proof supplies the imported contract
   (`verified_c_bridge_discharges_tcb`). We also prove two negative linking
   canaries (`canaryA_unsound_refinement` for ABI register clobbers and
   `canaryB_unsound_refinement` for lifetime-violating FFI callbacks).
2. **Upstream Soundness Bug Discovered in `rustc_codegen_cranelift` (`UnwindAction::Terminate`)**:
   By inspecting `rust-lang/rust` (`58cf8f9c35b355199727627d07ae34a4e2846d67`)
   at `compiler/rustc_codegen_cranelift/src/abi/mod.rs:910` and
   `compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:177-184`, we found
   that Cranelift tags `UnwindAction::Terminate(_)` (`Reason::Abi` at `nounwind`
   FFI boundaries and `Reason::InCleanup` inside destructors run during
   unwinding) with `EXCEPTION_HANDLER_CLEANUP` (`0`), emitting
   `cs_action_entry = 0` (`EHAction::Cleanup`) in `.gcc_except_table` instead of
   a negative filter (`ttype_index = -1`, `EHAction::Filter`). Under the
   two-phase Itanium C++ ABI (`_Unwind_RaiseException` + `rust_eh_personality`
   in `library/std/src/sys/personality/gcc.rs:212-275`), we prove in
   `cranelift_bug_phase1_misses_terminate_without_outer_catch` that Phase 1
   (`_UA_SEARCH_PHASE`) treats `cs_action_entry = 0` as a pure cleanup (`_URC_CONTINUE_UNWIND`)
   rather than a handler (`_URC_HANDLER_FOUND`). Consequently, when no outer
   `catch_unwind` frame exists on the stack, Phase 1 terminates with
   `_URC_END_OF_STACK` and **never runs Phase 2 (`_UA_CLEANUP_PHASE`)**,
   skipping intermediate `Drop` destructors and the `Terminate` landing pad!
3. **Mechanized Two-Phase Itanium Unwind Repair (`EXCEPTION_HANDLER_TERMINATE_FILTER`)**:
   We formalize the two-phase Itanium unwinder (`runTwoPhaseUnwind`), repair
   Cranelift's LSDA emission by introducing `EXCEPTION_HANDLER_TERMINATE_FILTER`
   (which emits an action record with `ttypeFilter = -1` / `0x7f` SLEB128
   pointing to a `0` entry in the TypeInfo table), and prove both single-phase
   and two-phase refinement soundness (`unwind_refinement_sound`,
   `repaired_filter_phase1_and_phase2_sound`) alongside a double-panic abort
   canary (`canaryC_unsound_refinement`).
4. **DWARF `.eh_frame` Call Frame Information (`CFI`) Verification on x86-64 and AArch64 (`PACIASP`/`AUTIASP`)**:
   We mechanize an executable DWARF `.eh_frame` CFI state machine (`CFIInstr`,
   `CFIRow`, `evalCFIStream`) covering x86-64 and AArch64 prologue/epilogue
   instructions, including ARMv8.3-A Pointer Authentication
   (`DW_CFA_AARCH64_negate_ra_state` for `PACIASP`/`AUTIASP`), pre-indexed
   `STP x29, x30, [sp, #-32]!`, callee-saved `STP x19, x20, [sp, #16]`, and
   post-indexed `LDP`. We prove that valid CFI tables reconstruct the exact
   caller `SP`, `FP`, `LR`, and callee-saved registers at every instruction
   boundary (`verify_cfi_table_sound`, `aarch64PrologueEpilogueCfi_sound`) and
   prove three negative canaries (`canaryD_cfi_rejects_mismatch`,
   `canary_missing_window_save_breaks_pac_cfi`, and
   `canary_corrupted_lr_detected_by_autiasp`).

---

## Applicability

This report applies to:

- **Anneal (`joshlf/anneal`)** at commit
  `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`, specifically:
  - `trusted/lean/Trusted/Refinement.lean` (`Language`, `Compiler`,
    `Compiler.SoundOn`, `Compiler.Verified`, `TCBItem`, `VerifiedFn`, `Crate`,
    `CrateTheorem`).
  - `trusted/lean/Trusted/MirAst.lean` and
    `trusted/lean/Trusted/MirSemantics.lean` (`Terminator`, `MirState`,
    `evalMirTerminator`).
- **Lean 4 (`leanprover/lean4`)** at `v4.34.1`
  (`5045d0056413266e57c625dcd7c365b10e377c52`).
- **Rust Compiler (`rust-lang/rust`)** at commits
  `58cf8f9c35b355199727627d07ae34a4e2846d67`,
  `8006091eb71ae7d9e9bccb66c6122c9d68af4466`, and
  `49d734536222bf28bb6d07d885b3a81d145981da`, specifically:
  - `compiler/rustc_middle/src/mir/terminator.rs` (`UnwindAction::Continue`,
    `UnwindAction::Unreachable`, `UnwindAction::Terminate(UnwindTerminateReason)`,
    `UnwindAction::Cleanup(BasicBlock)`).
  - `compiler/rustc_codegen_cranelift/src/abi/mod.rs:885-922` (lowering of
    `UnwindAction::Cleanup` and `UnwindAction::Terminate`).
  - `compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:14-210`
    (`EXCEPTION_HANDLER_CLEANUP`, `UnwindContext`, `.eh_frame` and
    `.gcc_except_table` emission via `gimli::write`).
  - `library/std/src/sys/personality/gcc.rs:1-315` (`rust_eh_personality`,
    `EHAction::None`, `EHAction::Cleanup`, `EHAction::Catch`,
    `EHAction::Filter`, `EHAction::Terminate`, `find_eh_action`).
  - `library/std/src/sys/personality/dwarf/eh.rs` (LSDA header, call-site table,
    and action-record decoding).
- **Wasmtime & Cranelift (`bytecodealliance/wasmtime`)** at commit
  `87282b8fd77fa9fbba6caadb0be690bedec2dc64`, specifically
  `cranelift/codegen/src/isa/unwind/systemv.rs` and
  `cranelift/codegen/src/isa/aarch64/inst/unwind/systemv.rs`.
- **CompCert (`AbsInt/CompCert`)** at commit
  `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6` (`common/Linking.v`,
  `common/Smallstep.v`).

---

## Findings

### 1. Compositional Separate Compilation and Multi-Language FFI Linking

`Basis: analysis of CompCert Linking.v, CompCertX, SepComp, Compositional CompCert, CompCertO, CCAL, and DimSum + machine-checked proofs in support/track8_compositional_and_unwind_cfi_probe.lean`

#### 1.1 Comparison of Compositional Compiler Verification Architectures

To determine how Anneal should verify multi-crate Rust binaries and C FFI object
linking without polluting `trusted/lean/Trusted/` with heavy step-indexed Kripke
machinery, Table 1 compares seven established compositional compilation
frameworks.

| Framework | Core Mechanism | Cross-Module / Cross-Language Linking | Mutual Recursion & Callbacks | Proof Overhead & Anneal Fit |
| :--- | :--- | :--- | :--- | :--- |
| **CompCert 2.7+ (`Linking.v`)** | Syntactic `Linker` typeclass + pass-commutation diagram: $\mathcal{C}(M_1) \bowtie \mathcal{C}(M_2) \sqsupseteq \mathcal{C}(M_1 \bowtie M_2)$ | Homogeneous C / Asm modules compiled by the same pass pipeline | Full mutual recursion after syntactic link | **Very low overhead**: ideal for linking separately compiled Anneal crates that share the same backend |
| **CompCertX** (Gu et al., POPL 2015) | Per-function contextual refinement parameterized by abstract kernel state | Links C/Asm layers into verified OS kernels (CertiKOS) | Stratified layers only (**no callbacks** from callee to caller) | Too restrictive for Rust traits, closures, or FFI callbacks |
| **SepComp** (Beringer et al., ESOP 2014) | Interaction semantics (`AtExternal` / `AfterExternal` cores) + structured memory injections | Links CompCert C with VST separation-logic proofs | Supports callbacks via structured injection growth | Moderate complexity; requires threading CompCert block injections across every step |
| **Compositional CompCert** (Stewart et al., POPL 2015) | Interaction semantics + rely-guarantee memory protocols | Arbitrary CompCert-compatible languages | Full mutual recursion and reentrant callbacks | **High complexity**: broke backward simulation and required rewriting every pass proof |
| **CompCertO** (Koenig & Shao, POPL 2021) | Open simulations parameterized by Kripke **simulation conventions** ($\mathbb{R} : A \leftrightarrow B$) | Heterogeneous C + hand-written Asm with calling-convention adapters | Full mutual recursion via horizontal/vertical simulation composition | Clean algebraic structure; simplified non-Kripke variant fits Anneal's `Language` record directly |
| **CCAL** (Gu et al., POPL 2018) | Certified Concurrent Abstraction Layers with thread-local rely-guarantee | Concurrent C + assembly primitives | Stratified concurrent layers | Best suited for low-level spinlocks/schedulers rather than general Rust crate graphs |
| **DimSum** (Sammler et al., POPL 2023) | Event-based angelic/demonic module transitions (`Spec` / `ModTrans`) | Truly heterogeneous (Rec + Asm + custom DSLs without shared memory type) | Arbitrary reentrant cross-language calls | **Direct match** for Anneal's `StepResult.choice (.angelic / .demonic)`! |

#### 1.2 Anneal's `OpenModule` and `Module.link` Architecture (`support/track8_compositional_and_unwind_cfi_probe.lean:45-615`)

Because Anneal's `Trusted/Refinement.lean` already models nondeterminism via
`Outcome` (demonic failure + angelic value set) and `StepResult.choice`, we
obtain the benefits of `CompCertO` and `DimSum` with **~55 lines of pure
definitions**:

1. **Typed Call-Boundary Contracts (`FnSig`, `CallEnv`)**:
   Every exported or imported symbol carries an ABI-aware contract specifying
   its argument precondition, postcondition over `(args, retVal, preMem, postMem)`,
   callee-saved register preservation invariant, and stack-frame disjointness.
2. **Open Modules (`OpenModule L`)**:
   An `OpenModule` over a language `L` declares:
   - `imports : List (String × FnSig)` — unresolved external symbols and their
     assumed contracts,
   - `exports : List (String × FnSig)` — symbols defined by this module and
     their guaranteed contracts, and
   - `defs : List (String × L.Prog)` — concrete function bodies.
   An `OpenModule` is verified (`OpenModule.Refines M`) when, assuming every
   imported symbol in `M.imports` satisfies its `FnSig` contract at external
   call points, every exported definition in `M.defs` satisfies its declared
   `FnSig` contract and is free of undefined behavior (`WellFormedOn`).
3. **Associative Symmetric Linking (`Module.link`)**:
   Linking two compatible modules $M_1 \bowtie M_2$ (`Module.link M₁ M₂`) unions
   their definitions and exports while discharging each module's imports that
   are satisfied by the other module's exports:
   $$\text{imports}(M_1 \bowtie M_2) = (\text{imports}(M_1) \setminus \text{exports}(M_2)) \cup (\text{imports}(M_2) \setminus \text{exports}(M_1))$$

In Sections 1–4 of `support/track8_compositional_and_unwind_cfi_probe.lean`, we
machine-check five compositional theorems and two negative linking canaries:
- **`link_associative` (`lines 252-298`)**: Proves that `(M₁ bowtie M₂) bowtie M₃`
  and `M₁ bowtie (M₂ bowtie M₃)` produce equivalent linked modules.
- **`horizontal_refinement_composition` (`lines 310-375`)**: Proves that if
  `OpenModule.Refines M₁` and `OpenModule.Refines M₂` hold and their matching
  import/export signatures agree (`LinkCompatible M₁ M₂`), then
  `OpenModule.Refines (Module.link M₁ M₂)` holds automatically.
- **`compile_link_commutes` (`lines 390-445`)**: Proves CompCert's separate
  compilation diagram—compiling `M₁` and `M₂` independently to assembly and
  linking the resulting object files (`Module.link (compile M₁) (compile M₂)`)
  refines compiling the linked source module (`compile (Module.link M₁ M₂)`).
- **`end_to_end_separate_compilation` (`lines 455-510`)**: Combines per-module
  functional correctness (`OpenModule.Refines`), separate compilation
  (`Compiler.Verified`), and `compile_link_commutes` to discharge closed-program
  machine-code safety (`CrateTheorem`) when all imports are resolved
  (`imports = []`).
- **`verified_c_bridge_discharges_tcb` (`lines 515-555`)**: Shows how
  `TCBItem.foreignBridge` is eliminated from the TCB when an external C function
  is accompanied by a machine-checked proof of its `FnSig` against the lowered
  ABI (`System V AMD64` / `AAPCS64`).
- **Negative Linking Canaries (`lines 560-615`)**:
  - **`canaryA_unsound_refinement`**: Proves that an external C function that
    computes the right return value in `rax`/`x0` but clobbers a callee-saved
    register (`rbx`/`x19`) without restoring it violates the ABI boundary
    contract and corrupts the Rust caller's live local after returning.
  - **`canaryB_unsound_refinement`**: Proves that an FFI callee that stashes a
    borrowed pointer `&mut T` in a C global variable and dereferences it after
    the Rust lifetime ends violates frame disjointness and triggers a
    happens-before data race in `MemState`.

---

### 2. Upstream Soundness Bug in `rustc_codegen_cranelift` (`UnwindAction::Terminate`) and the Two-Phase Itanium ABI Repair

`Basis: direct source inspection of rust-lang/rust @ 58cf8f9c35b355199727627d07ae34a4e2846d67 + machine-checked proofs in support/track8_compositional_and_unwind_cfi_probe.lean and support/round2_track6_probe.lean`

#### 2.1 How Rust MIR Models Unwinding (`UnwindAction`)

In `compiler/rustc_middle/src/mir/terminator.rs`, every potentially unwinding
MIR terminator (`TerminatorKind::Call`, `TerminatorKind::Drop`,
`TerminatorKind::Assert`, `TerminatorKind::InlineAsm`) carries an
`UnwindAction`:

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
1. `UnwindTerminateReason::Abi`: The call occurs inside an `extern "C"` (or
   other non-unwinding ABI) function where unwinding across the FFI boundary is
   undefined behavior; if a panic reaches this boundary, the runtime must catch
   it and abort the process (`panic_nounwind_fmt`).
2. `UnwindTerminateReason::InCleanup`: A `Drop::drop` call inside a cleanup
   landing pad itself panics during stack unwinding; Rust must immediately abort
   (`panic_in_cleanup`) rather than permitting double-unwinding.

#### 2.2 The Upstream Bug in `rustc_codegen_cranelift`

In `compiler/rustc_codegen_cranelift/src/abi/mod.rs:885-922` (at commit
`58cf8f9c35b355199727627d07ae34a4e2846d67`), `rustc_codegen_cranelift` lowers
both `UnwindAction::Cleanup(cleanup)` and `UnwindAction::Terminate(reason)` by
creating a Cranelift landing-pad block rigged with the **exact same tag**,
`EXCEPTION_HANDLER_CLEANUP` (`0`):

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

And in `compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:177-184`, when
serializing the `.gcc_except_table` Language-Specific Data Area (LSDA) via
`gimli::write`, `rustc_codegen_cranelift` emits a `CallSite` entry with no
action record (`cs_action_entry = 0`) and an empty Action Table:

```rust
// compiler/rustc_codegen_cranelift/src/debuginfo/unwind.rs:177-184
// Only cleanup landing pads are supported, so action is always 0.
```

#### 2.3 Why `cs_action_entry = 0` Breaks the Two-Phase Itanium Unwinder (`rust_eh_personality`)

To see why emitting `cs_action_entry = 0` (`EXCEPTION_HANDLER_CLEANUP`) for a
`Terminate` landing pad is unsound, examine how `libunwind`'s
`_Unwind_RaiseException` interacts with Rust's personality routine
`rust_eh_personality` (`library/std/src/sys/personality/gcc.rs:212-275`):

1. **Phase 1 (`_UA_SEARCH_PHASE`)**:
   `_Unwind_RaiseException` walks the stack from top to bottom without modifying
   registers or running any landing-pad code, querying each frame's personality
   function (`rust_eh_personality`) to determine whether **any** frame on the
   stack will catch or terminate the exception (`_URC_HANDLER_FOUND`).
   - In `library/std/src/sys/personality/dwarf/eh.rs`, `find_eh_action` decodes
     the LSDA `CallSite` entry covering the return address (`ip - 1`).
   - When `cs_action_entry == 0`, `find_eh_action` returns `EHAction::Cleanup(lpad)`.
   - In `library/std/src/sys/personality/gcc.rs:235-248`, during
     `_UA_SEARCH_PHASE`:
     - `EHAction::None` and **`EHAction::Cleanup(lpad)`** both return
       **`_URC_CONTINUE_UNWIND`**!
     - Only `EHAction::Catch(lpad)`, `EHAction::Filter(lpad)`, and
       `EHAction::Terminate` return **`_URC_HANDLER_FOUND`**.
2. **What Happens When No Outer `catch_unwind` Exists on the Stack**:
   Suppose a thread (e.g., a C `pthread_create` worker, a bare-metal interrupt/FFI
   entry point, or `extern "C" fn` called from C) calls a Rust function compiled
   by `rustc_codegen_cranelift` that contains `Drop` cleanups and an
   `UnwindAction::Terminate(Reason::Abi)` guard, with **no** `std::panic::catch_unwind`
   (`EHAction::Catch`) higher on the stack.
   - Because `rustc_codegen_cranelift` encoded the `Terminate` landing pad with
     `cs_action_entry = 0` (`EHAction::Cleanup`), `rust_eh_personality` returns
     `_URC_CONTINUE_UNWIND` during Phase 1 (`_UA_SEARCH_PHASE`)!
   - `_Unwind_RaiseException` reaches the bottom of the stack without seeing
     `_URC_HANDLER_FOUND`, aborts Phase 1 with `_URC_END_OF_STACK`, and **never
     executes Phase 2 (`_UA_CLEANUP_PHASE`)**!
   - As a result, neither the intermediate `Drop` cleanup landing pads nor the
     `Terminate` landing pad itself (`panic_nounwind`) ever execute; control returns
     `_URC_END_OF_STACK` to `__cxa_throw` / `rust_panic`!

We mechanize this exact two-phase failure in Section 3 of
`support/round2_track6_probe.lean`:
- **`cranelift_bug_phase1_misses_terminate_without_outer_catch`
  (`round2_track6_probe.lean:880-955`)**: Constructs a two-frame call stack where
  Frame 0 (`inner_fn`) has an active `Drop` cleanup (`UnwindAction::Cleanup`)
  and Frame 1 (`extern_c_entry`) has an `UnwindAction::Terminate(Reason::Abi)`
  boundary. When compiled with Cranelift's `cs_action_entry = 0`, Phase 1 search
  (`unwindPhase1Search`) returns `.noHandlerFound` (`_URC_END_OF_STACK`),
  skipping Phase 2 entirely (`ranCleanups = []`, `terminatedViaPad = false`),
  whereas the source MIR semantics runs Frame 0's `Drop` cleanup and terminates
  at Frame 1's `Terminate` pad.
- **`canaryC_unsound_refinement`
  (`track8_compositional_and_unwind_cfi_probe.lean:940-995`)**: Proves that if a
  destructor inside a cleanup landing pad panics and the landing pad's internal
  call is lowered as `Continue` or a non-terminating cleanup instead of
  `Terminate(Reason::InCleanup)`, the second exception escapes instead of
  triggering an immediate deterministic abort (`Outcome.terminated .abort`).

#### 2.4 The Verified Repair: `EXCEPTION_HANDLER_TERMINATE_FILTER` (`ttype_index = -1`)

How does LLVM (`rustc_codegen_llvm` / `llvm/lib/CodeGen/AsmPrinter/EHStreamer.cpp`)
encode `UnwindAction::Terminate` in `.gcc_except_table` so that
`rust_eh_personality` stops in Phase 1 (`_URC_HANDLER_FOUND`) and installs the
`Terminate` landing pad in Phase 2 (`_URC_INSTALL_CONTEXT`)?
- In LLVM IR, `rustc_codegen_llvm` emits `landingpad { ptr, i32 } filter [0 x ptr] zeroinitializer`.
- In `.gcc_except_table`, the `CallSite` entry has `cs_action_entry = 1`
  (1-based byte offset into the Action Table), pointing to an `ActionRecord` with:
  - `ttype_index = -1` (encoded as `0x7f` in signed LEB128; negative values
    denote an exception **filter** spec rather than a positive `catch` clause),
  - `next_action = 0` (end of action chain),
  where the filter list in the TypeInfo table (`@TType`) begins with a `0`
  (null) entry indicating an empty allowed-exception list (`throw()`).
- In `library/std/src/sys/personality/dwarf/eh.rs`, `find_eh_action` sees
  `ttype_index < 0` and returns `EHAction::Filter(lpad)`.
- In `library/std/src/sys/personality/gcc.rs:242-265`:
  - During Phase 1 (`_UA_SEARCH_PHASE`), `EHAction::Filter(lpad)` returns
    **`_URC_HANDLER_FOUND`**!
  - During Phase 2 (`_UA_CLEANUP_PHASE`), `_Unwind_RaiseException` first visits
    every inner `EHAction::Cleanup` frame (`_URC_INSTALL_CONTEXT`), executing
    each `Drop` landing pad and resuming via `_Unwind_Resume`, and then reaches
    the `EHAction::Filter(lpad)` frame with `_UA_CLEANUP_PHASE | _UA_HANDLER_FRAME`,
    returning **`_URC_INSTALL_CONTEXT`** to jump directly to the `Terminate`
    landing pad (`core::panicking::panic_nounwind` / `panic_in_cleanup`).

We mechanize this repair and prove its soundness:
- **`repaired_filter_phase1_and_phase2_sound`
  (`round2_track6_probe.lean:960-1045`)**: Proves that lowering
  `UnwindAction::Cleanup` to `cs_action_entry = 0` (`EHAction::Cleanup`) and
  `UnwindAction::Terminate` to `cs_action_entry = 1` pointing to
  `ActionRecord { ttypeFilter = -1, nextActionOffset = 0 }` (`EHAction::Filter`)
  causes `runTwoPhaseUnwind` to succeed in Phase 1 (`_URC_HANDLER_FOUND`) and
  execute all inner `Drop` cleanups in LIFO order before installing the
  `Terminate` landing pad in Phase 2, exactly matching source MIR unwinding
  semantics.
- **`unwind_refinement_sound`
  (`track8_compositional_and_unwind_cfi_probe.lean:820-935`)**: Proves general
  simulation soundness between multi-frame MIR `UnwindAction` execution and
  `.gcc_except_table` LSDA unwinding across arbitrarily nested `Continue`,
  `Cleanup`, and `Terminate` frames.

---

### 3. DWARF `.eh_frame` Call Frame Information (`CFI`) and AArch64 `PACIASP`/`AUTIASP` Verification

`Basis: inspection of bytecodealliance/wasmtime cranelift/codegen/src/isa/unwind/systemv.rs @ 87282b8fd77fa9fbba6caadb0be690bedec2dc64 + machine-checked proofs in support/track8_compositional_and_unwind_cfi_probe.lean and support/round2_track6_probe.lean`

#### 3.1 Why `.gcc_except_table` LSDA Soundness Requires Verified `.eh_frame` CFI Tables

The two-phase Itanium unwinder (`_Unwind_RaiseException` and `_Unwind_Resume`)
can only locate each caller frame's return address (`ip`) and restore
callee-saved registers (`rbx`, `rbp`, `r12`–`r15` on x86-64; `x19`–`x29`, `x30`
on AArch64) if the compiler's emitted `.eh_frame` Call Frame Information (CFI)
table accurately describes the physical stack layout at **every potentially
unwinding instruction offset (`PC`)**. If a single `DW_CFA_def_cfa_offset` or
`DW_CFA_offset` directive is missing or off by 8 bytes, `_Unwind_RaiseException`
reads a corrupted return address or restores a wrong callee-saved register,
subverting both `Drop` safety and control-flow integrity.

#### 3.2 Executable DWARF `.eh_frame` CFI Verifier (`support/track8_compositional_and_unwind_cfi_probe.lean:1005-1560`)

In Section 7 of `support/track8_compositional_and_unwind_cfi_probe.lean`, we
formalize the DWARF v4/v5 `.eh_frame` abstract machine:
- **CFA Rule (`CFADef`)**: `CFA = reg(cfaReg) + cfaOffset` (initially `rsp + 8`
  on x86-64 or `sp + 0` on AArch64).
- **Register Rules (`RegRule`)**: `.sameValue`, `.offset (d : Int)` (stored at
  memory address `CFA + d`), `.register r`, and (in Round 2) `.negateRAState`
  for ARMv8.3-A Pointer Authentication (`PACIASP`/`AUTIASP`).
- **CFI Instructions (`CFIInstr`)**: `DW_CFA_advance_loc`, `DW_CFA_def_cfa`,
  `DW_CFA_def_cfa_register`, `DW_CFA_def_cfa_offset`, `DW_CFA_offset`,
  `DW_CFA_restore`, `DW_CFA_remember_state`, `DW_CFA_restore_state`, and
  `DW_CFA_AARCH64_negate_ra_state` (`DW_CFA_window_save`, opcode `0x2d`).

We define an executable validator `checkCFITable` that steps the abstract machine
instruction-by-instruction across a compiled function's prologue, body, and
epilogue, verifying that at every PC offset the DWARF `CFIRow` produced by
`evalCFIStream` satisfies `CFIFrameConsistent`:
$$\text{evalCFA}(\text{row}, \text{regs}_{\text{curr}}) = \text{sp}_{\text{caller}} \;\wedge\; \forall r \in \text{CalleeSaved} \cup \{\text{RA}\},\; \text{recoverReg}(\text{row}, r, \text{regs}_{\text{curr}}, \text{mem}_{\text{curr}}) = \text{regs}_{\text{caller}}(r)$$

We prove two theorems in `support/track8_compositional_and_unwind_cfi_probe.lean`:
- **`verify_cfi_table_sound` (`lines 1365-1485`)**: Proves that whenever
  `checkCFITable prog cfiStream = true`, unwinding from any instruction PC in
  `prog` via `unwindStepWithCFI` recovers the exact caller stack pointer
  `callerSP`, return address `callerRA`, and all callee-saved registers.
- **`canaryD_cfi_rejects_mismatch` (`lines 1490-1560`)**: Proves that if a
  prologue pushes a register (`sub sp, sp, #16`) but the `.eh_frame` stream
  omits or misstates the `DW_CFA_def_cfa_offset` delta, `checkCFITable` returns
  `false` and `unwindStepWithCFI` reads from the wrong stack address.

#### 3.3 Multi-Block AArch64 `PACIASP`/`AUTIASP` Pointer Authentication + FP/LR CFI Verification (`support/round2_track6_probe.lean:1050-1420`)

On modern AArch64 targets (`aarch64-unknown-linux-gnu` and `aarch64-apple-darwin`
with `-Zbranch-protection=pac-ret`), function prologues sign the link register
`x30` (`LR`) using the stack pointer `sp` as a cryptographic modifier before
pushing it to the stack (`PACIASP`), and authenticate `x30` against `sp` after
popping it in the epilogue (`AUTIASP`):

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

In Section 4 of `support/round2_track6_probe.lean`, we model the complete 9-PC
AArch64 execution and DWARF CFI table (`aarch64PacFunc`, `aarch64PacCfiStream`)
with cryptographic PAC tag signing/authentication (`signPac`, `authPac`, and
`authPac_signPac_cancel`) and prove three theorems:
- **`aarch64PrologueEpilogueCfi_sound` (`round2_track6_probe.lean:1280-1350`)**:
  Proves that at every single PC offset `0..8` (before `paciasp`, after
  `paciasp`, after `stp x29, x30`, after `mov x29, sp`, during body execution
  with clobbered `x19`/`x20`/`x29`/`x30`, after `ldp x19, x20`, after
  `ldp x29, x30`, and after `autiasp`), the DWARF `.eh_frame` unwinder
  (`unwindAArch64FrameAtPc`) accurately strips the PAC signature when
  `raSigned = true` and recovers the exact caller `(sp, x29, x30, x19, x20)`.
- **`canary_missing_window_save_breaks_pac_cfi`
  (`round2_track6_probe.lean:1352-1385`)**: Proves that if the compiler emits
  `paciasp` in the prologue but omits `DW_CFA_AARCH64_negate_ra_state` in
  `.eh_frame`, the unwinder fails to strip the PAC tag from the saved `x30` word
  on the stack (`recoveredLR ≠ callerLR`), causing a fault when jumping to the
  caller's landing pad.
- **`canary_corrupted_lr_detected_by_autiasp`
  (`round2_track6_probe.lean:1387-1420`)**: Proves that if a stack buffer
  overflow overwrites the saved `x30` slot `[sp + 8]` with an attacker-chosen
  gadget address or if `sp` is pivoted before `autiasp`, `authPac` detects the
  tag mismatch and traps before `ret` executes.

---

## Boundaries

1. **Dynamic Linking (`dlopen` / PLT / GOT) vs. Static Relocatable Linking**:
   `Module.link` (`support/track8_compositional_and_unwind_cfi_probe.lean`)
   models static linking of separately compiled crates (`rlib`) and `.o` object
   files where symbol resolution is fixed prior to execution. Runtime dynamic
   loading (`dlopen`) and lazy PLT binding require runtime verification of the
   loaded shared object's exported `FnSig` table.
2. **Asynchronous Signals (`_fasynchronous-unwind-tables`) vs. Synchronous Call-Site Unwinding**:
   Our `.gcc_except_table` LSDA verifier requires unwind accuracy at synchronous
   unwind points (`Call`, `Drop`, `InlineAsm`), while our `.eh_frame` CFI
   verifier (`aarch64PrologueEpilogueCfi_sound`) verifies every instruction PC
   `0..8` in the prologue and epilogue. However, Rust's semantics does not
   support unwinding out of asynchronous POSIX signal handlers (`SIGSEGV` /
   `SIGALRM`) to run `Drop` destructors on interrupted basic-block interiors.
3. **Forced Unwinding (`_UA_FORCE_UNWIND`) and Foreign C++ Exceptions**:
   Our two-phase unwinder (`runTwoPhaseUnwind`) models standard Rust panics and
   Itanium C++ exceptions caught by `EHAction::Catch` or stopped by
   `EHAction::Filter` (`ttypeFilter = -1`). POSIX `pthread_cancel` forced
   unwinding (`_UA_FORCE_UNWIND`) bypasses `EHAction::Catch` in Phase 1 and must
   still be stopped at `UnwindAction::Terminate(Reason::Abi)` boundaries via
   `rust_eh_personality`'s `_UA_FORCE_UNWIND` check.

---

## Evidence

1. **Round 1 Track 8 Standalone Lean 4.34.1 Mechanization
   (`support/track8_compositional_and_unwind_cfi_probe.lean`)**:
   - **Path**:
     `reports/compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026/support/track8_compositional_and_unwind_cfi_probe.lean`
   - **Lines**: 1,609
   - **SHA-256**:
     `74360333b4f7e7bf0c6f17da95713ebb055471a6e5e17632806c779a62fb9633`
   - **Key Verified Theorems**:
     - `link_associative`
     - `horizontal_refinement_composition`
     - `compile_link_commutes`
     - `end_to_end_separate_compilation`
     - `verified_c_bridge_discharges_tcb`
     - `canaryA_unsound_refinement`, `canaryB_unsound_refinement`
     - `unwind_refinement_sound`, `canaryC_unsound_refinement`
     - `verify_cfi_table_sound`, `canaryD_cfi_rejects_mismatch`
   - **Axiom Audit**: Verified via `#guard_msgs in #print axioms` to depend only
     on standard Lean 4 axioms (`propext`, `Classical.choice`, `Quot.sound`),
     with zero `sorryAx` and zero custom axioms.
2. **Round 2 Track 6 Standalone Lean 4.34.1 Mechanization
   (`support/round2_track6_probe.lean`, Sections 3 & 4)**:
   - **Path**:
     `reports/compositional-separate-compilation-ffi-linking-and-dwarf-unwind-cfi-2026/support/round2_track6_probe.lean`
   - **Lines**: 1,462
   - **SHA-256**:
     `d5049314b0d824b19586324884f5c1a64e3172d391d35c8a4ebfaa52b1ef8771`
   - **Key Verified Theorems (Sections 3 & 4)**:
     - `cranelift_bug_phase1_misses_terminate_without_outer_catch`
     - `repaired_filter_phase1_and_phase2_sound`
     - `authPac_signPac_cancel`
     - `aarch64PrologueEpilogueCfi_sound`
     - `canary_missing_window_save_breaks_pac_cfi`
     - `canary_corrupted_lr_detected_by_autiasp`
   - **Axiom Audit**: Verified via `#guard_msgs in #print axioms` to depend only
     on standard Lean 4 axioms (`propext`, `Quot.sound`), with zero `sorryAx`
     and zero custom axioms.

---

## Revalidation

To typecheck both standalone Lean 4.34.1 proof probes and verify all theorems
and `#guard_msgs in #print axioms` checks with zero errors and zero warnings,
run from the repository root using Lean `v4.34.1`
(`5045d0056413266e57c625dcd7c365b10e377c52`):

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
# 74360333b4f7e7bf0c6f17da95713ebb055471a6e5e17632806c779a62fb9633  .../track8_compositional_and_unwind_cfi_probe.lean
# d5049314b0d824b19586324884f5c1a64e3172d391d35c8a4ebfaa52b1ef8771  .../round2_track6_probe.lean
```
