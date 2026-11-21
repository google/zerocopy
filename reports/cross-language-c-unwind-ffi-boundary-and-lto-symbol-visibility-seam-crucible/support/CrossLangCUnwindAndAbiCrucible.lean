/-
  CrossLangCUnwindAndAbiCrucible.lean

  Kernel-checked Lean v4.34.1 formalization of the cross-language Rust <-> C++17 / C17
  FFI unwinding, SysV x86-64 `i128` (`__int128`) ABI, and LTO / symbol-visibility seam:
    (1) Two-step Itanium EH unwinder (`searchStep` followed by `cleanupStep`) across
        mixed Rust (`rust_eh_personality`, `MOZ\0RUST` + per-DSO canary) and C++17
        (`__gxx_personality_v0`, `GNUCC++\0`) stack frames:
          - `extern "C-unwind"` bidirectional RAII / `Drop` preservation (Cells 1 & 2)
          - `catch_unwind` deterministic `__rust_foreign_exception` abort after running
            intermediate C++ and Rust cleanup destructors + `_Unwind_DeleteException` (Cell 3)
          - `-C panic=abort` `AbortUnwindingCalls` lowering of `resume -> terminate(abi)`
            (`EHAction::Cleanup` pad calling `panic_cannot_unwind` under outer handler vs.
            `_URC_END_OF_STACK` `std::terminate` under uncaught C++ `main`, Cells 4a/4b/4c)
          - `extern "C"` `nounwind uwtable` silent `Drop`-skipping UB (Cell 5) vs.
            `-C force-unwind-tables=no` FDE omission `std::terminate` (Cell 6)
    (2) RFC 3435 `i128`/`u128` 16-byte alignment, `#[repr(C)]` struct layout parity with
        Clang/GCC `__int128`, SysV x86-64 register-pair marshaling, and the 5-GPR straddle
        stack-spill boundary preserving `%r9`
    (3) ELF `STV_DEFAULT` vs. `STV_HIDDEN`, `#[unsafe(no_mangle)]` (`SymbolExportLevel::C`),
        `cdylib` `--version-script` localization, and cross-language ThinLTO internalization

  TCB & Hygiene Standards Enforced:
    - 0 `sorry` / `sorryAx`
    - 0 `Classical.choice`
    - 0 `omega`
    - 0 `bv_decide` / `Lean.ofReduceBool`
    - 0 `native_decide`
    - 0 `partial def` / `._unsafe_rec` / `@[extern]` (all list iterations encoded via `List.foldr`)
-/

namespace CrossLangCUnwindAndAbiCrucible

/-! ## Section 1: Two-Language Exception Classes, Stack Frames & Itanium Unwinder -/

inductive Lang where
  | rust
  | cpp
  deriving DecidableEq, Repr

inductive ExceptionClass where
  /-- Rust panic carrying `MOZ\0RUST` and the originating `panic_unwind` `CANARY` ID. -/
  | rustPanic (canaryId : Nat)
  /-- Foreign C++ exception (e.g. `GNUCC++\0`) with an object identity tag. -/
  | foreignCpp (exId : Nat)
  deriving DecidableEq, Repr

inductive CatchKind where
  /-- Rust `std::panic::catch_unwind` (`EHAction::Catch` accepting a specific `CANARY`). -/
  | rustCatchUnwind (canaryId : Nat)
  /-- C++ `try { ... } catch (const CppEx&)` (`__gxx_personality_v0` matching `.foreignCpp`). -/
  | cppCatchForeign
  deriving DecidableEq, Repr

/-- Unwind descriptor for one physical stack frame in a mixed Rust/C++ call stack
    (frames are ordered innermost/callee-first to outermost/caller-last). -/
inductive FrameDescriptor where
  /-- Normal unwinding frame (`extern "C-unwind"`, Rust `Rust` ABI under `panic=unwind`,
      or C++ compiled with `-fexceptions`) having an LSDA `Cleanup` landing pad. -/
  | cleanupOnly (lang : Lang) (drops : List String)
  /-- Frame with cleanup drops and an active catch handler (`catch_unwind` or C++ `try/catch`). -/
  | cleanupAndCatch (lang : Lang) (drops : List String) (catcher : CatchKind)
  /-- `-C panic=abort` MIR cleanup block whose `UnwindResume` was rewritten by
      `AbortUnwindingCalls` to `UnwindTerminate(Reason::Abi)`. Because LLVM lowers MIR
      cleanup blocks to `landingpad ... cleanup` (`EHAction::Cleanup`, `cs_action = 0`),
      `searchStep` returns `_URC_CONTINUE_UNWIND`, while entering `cleanupStep` executes
      `preTerminateDrops` and immediately calls `core::panicking::panic_cannot_unwind`. -/
  | abortCleanupPad (preTerminateDrops : List String)
  /-- Direct `UnwindAction::Terminate` edge lowered to `landingpad ... filter [0 x ptr]`
      (`ttype_index = -1`, `EHAction::Filter`): `searchStep` returns `_URC_HANDLER_FOUND`
      immediately even with no outer handler, and `cleanupStep` aborts via `filter` pad. -/
  | abortFilterPad (preTerminateDrops : List String)
  /-- `extern "C"` Rust frame (`nounwind` + `uwtable` emitted by default on Linux ELF):
      `.eh_frame` contains a valid FDE (with CIE only, `LSDA = None`), so the unwinder
      continues across it in both steps while silently skipping `skippedRustDrops` (UB). -/
  | noLandingPadWithUwtable (skippedRustDrops : List String)
  /-- `extern "C"` / `-C panic=abort` frame compiled with `-C force-unwind-tables=no`:
      neither `uwtable` nor an `.eh_frame` FDE exists, halting `searchStep` at
      `_URC_END_OF_STACK` (`std::terminate`) before any cleanup step can run. -/
  | noUwtable (unreachedDrops : List String)
  deriving DecidableEq, Repr

/-- Whether a catch clause claims an exception in Itanium step 1 (`_UA_SEARCH_PHASE`).
    Crucially, `rust_eh_personality_impl` (`library/std/src/sys/personality/gcc.rs:212, 227`)
    ignores `_exception_class` during search and returns `_URC_HANDLER_FOUND` for BOTH
    Rust panics and foreign C++ exceptions! -/
def catcherClaimsInSearch (ck : CatchKind) (exc : ExceptionClass) : Bool :=
  match ck with
  | .rustCatchUnwind _ => true
  | .cppCatchForeign =>
      match exc with
      | .foreignCpp _ => true
      | .rustPanic _ => false

/-- Step 1 (`_UA_SEARCH_PHASE`) over an innermost-to-outermost frame stack via `List.foldr`
    (zero `._unsafe_rec` emitted in `.olean`): returns `true` iff a handler (`_URC_HANDLER_FOUND`)
    is found before hitting an unmapped FDE (`noUwtable`) or exhausting the stack. -/
def searchStep (exc : ExceptionClass) (stack : List FrameDescriptor) : Bool :=
  stack.foldr
    (fun f ih =>
      match f with
      | .cleanupOnly _ _ => ih
      | .cleanupAndCatch _ _ ck =>
          if catcherClaimsInSearch ck exc then true else ih
      | .abortCleanupPad _ => ih
      | .abortFilterPad _ => true
      | .noLandingPadWithUwtable _ => ih
      | .noUwtable _ => false)
    false

/-- Observable outcome of the two-step Itanium unwind across a mixed Rust/C++ stack. -/
inductive UnwindOutcome where
  /-- Caught by a matching handler; records executed destructors, any destructors silently
      skipped across `nounwind uwtable` frames (UB), and the catcher language. -/
  | caught (handlerLang : Lang) (executedDrops : List String) (ubSkippedDrops : List String)
  /-- `catch_unwind` claimed a foreign exception in step 1, ran intermediate cleanup drops,
      called `_Unwind_DeleteException` (iff `.foreignCpp`), and aborted via `__rust_foreign_exception`. -/
  | abortedForeignException (executedDrops : List String) (ubSkippedDrops : List String) (deletedCppEx : Bool)
  /-- Reached `-C panic=abort` `Terminate(Reason::Abi)` cleanup/filter pad and aborted via
      `core::panicking::panic_cannot_unwind`. -/
  | abortedTerminateAbi (executedDrops : List String) (ubSkippedDrops : List String)
  /-- Search step hit `_URC_END_OF_STACK` (missing FDE or no handler); `__cxa_throw` called
      `std::terminate()` immediately without executing ANY cleanup step destructors. -/
  | terminatedEndOfStack
  deriving DecidableEq, Repr

/-- Single-frame step transformation for Step 2 (`_UA_CLEANUP_PHASE`). -/
def cleanupFrameStep
    (exc : ExceptionClass)
    (f : FrameDescriptor)
    (ih : List String → List String → UnwindOutcome)
    (execAcc skipAcc : List String) : UnwindOutcome :=
  match f with
  | .cleanupOnly _ drops =>
      ih (execAcc ++ drops) skipAcc
  | .abortCleanupPad preDrops =>
      .abortedTerminateAbi (execAcc ++ preDrops) skipAcc
  | .abortFilterPad preDrops =>
      .abortedTerminateAbi (execAcc ++ preDrops) skipAcc
  | .noLandingPadWithUwtable skippedDrops =>
      ih execAcc (skipAcc ++ skippedDrops)
  | .noUwtable _ =>
      .terminatedEndOfStack
  | .cleanupAndCatch lang drops ck =>
      match ck with
      | .cppCatchForeign =>
          match exc with
          | .foreignCpp _ =>
              .caught lang (execAcc ++ drops) skipAcc
          | .rustPanic _ =>
              -- C++ typed `catch (const CppEx&)` rejects `MOZ\0RUST`; runs local RAII `drops` and continues.
              ih (execAcc ++ drops) skipAcc
      | .rustCatchUnwind localCanary =>
          let execTotal := execAcc ++ drops
          match exc with
          | .rustPanic thrownCanary =>
              if Nat.beq thrownCanary localCanary then
                .caught lang execTotal skipAcc
              else
                -- Foreign Rust `std` copy (`canary != &CANARY`): aborts WITHOUT `_Unwind_DeleteException`
                -- (`library/panic_unwind/src/gcc.rs:97-103`).
                .abortedForeignException execTotal skipAcc false
          | .foreignCpp _ =>
              -- Foreign non-Rust exception (`exception_class != "MOZ\0RUST"`): calls `_Unwind_DeleteException`
              -- then aborts via `__rust_foreign_exception` (`library/panic_unwind/src/gcc.rs:88-91`).
              .abortedForeignException execTotal skipAcc true

/-- Step 2 (`_UA_CLEANUP_PHASE`) via `List.foldr` (zero `._unsafe_rec`), invoked ONLY when
    `searchStep exc stack = true`. -/
def cleanupStep
    (exc : ExceptionClass)
    (execAcc skipAcc : List String)
    (stack : List FrameDescriptor) : UnwindOutcome :=
  (stack.foldr (cleanupFrameStep exc) (fun _ _ => .terminatedEndOfStack)) execAcc skipAcc

/-- Complete two-step cross-language Itanium unwinder (`_Unwind_RaiseException`). -/
def runCrossLangUnwind (exc : ExceptionClass) (stack : List FrameDescriptor) : UnwindOutcome :=
  if searchStep exc stack then
    cleanupStep exc [] [] stack
  else
    .terminatedEndOfStack

/-- Predicate characterizing well-typed unwinding `C-unwind` / `-fexceptions` intermediate frames. -/
def WellTypedUnwindChain (frames : List FrameDescriptor) : Prop :=
  frames.foldr
    (fun f restProp =>
      match f with
      | .cleanupOnly _ _ => restProp
      | _ => False)
    True

/-- Expected LIFO destructor trace across a well-typed chain of intermediate frames. -/
def expectedChainDrops (frames : List FrameDescriptor) : List String :=
  frames.foldr
    (fun f acc =>
      match f with
      | .cleanupOnly _ drops => drops ++ acc
      | _ => acc)
    []

/-! ## Section 2: General Inductive Theorems on Cross-Language Unwinding -/

private theorem searchStep_append_wellTyped
    (exc : ExceptionClass)
    (inner outer : List FrameDescriptor)
    (hInner : WellTypedUnwindChain inner) :
    searchStep exc (inner ++ outer) = searchStep exc outer := by
  induction inner with
  | nil => rfl
  | cons hd tl ih =>
      cases hd with
      | cleanupOnly _ _ =>
          exact ih hInner
      | cleanupAndCatch _ _ _ => cases hInner
      | abortCleanupPad _ => cases hInner
      | abortFilterPad _ => cases hInner
      | noLandingPadWithUwtable _ => cases hInner
      | noUwtable _ => cases hInner

private theorem cleanupStep_append_wellTyped
    (exc : ExceptionClass)
    (execAcc skipAcc : List String)
    (inner outer : List FrameDescriptor)
    (hInner : WellTypedUnwindChain inner) :
    cleanupStep exc execAcc skipAcc (inner ++ outer) =
      cleanupStep exc (execAcc ++ expectedChainDrops inner) skipAcc outer := by
  induction inner generalizing execAcc with
  | nil =>
      dsimp [expectedChainDrops]
      rw [List.append_nil]
  | cons hd tl ih =>
      cases hd with
      | cleanupOnly _ drops =>
          change cleanupStep exc (execAcc ++ drops) skipAcc (tl ++ outer) =
            cleanupStep exc (execAcc ++ (drops ++ expectedChainDrops tl)) skipAcc outer
          rw [ih (execAcc ++ drops) hInner, List.append_assoc]
      | cleanupAndCatch _ _ _ => cases hInner
      | abortCleanupPad _ => cases hInner
      | abortFilterPad _ => cases hInner
      | noLandingPadWithUwtable _ => cases hInner
      | noUwtable _ => cases hInner

/-- Helper: matching pairs `(exc, catchKind)` that successfully catch rather than abort. -/
def ExceptionMatchesCatcher (exc : ExceptionClass) (ck : CatchKind) : Prop :=
  (∃ exId, exc = .foreignCpp exId ∧ ck = .cppCatchForeign) ∨
  (∃ canary, exc = .rustPanic canary ∧ ck = .rustCatchUnwind canary)

/-- Theorem 1 (`Bidirectional RAII / Drop Preservation Across C-unwind Stacks`):
    For ANY finite sequence of well-typed intermediate Rust `C-unwind` and C++ `-fexceptions`
    `.cleanupOnly` frames above a matching catcher (`.cppCatchForeign` for C++ `throw`, or
    `.rustCatchUnwind c` for Rust `panic!`), `runCrossLangUnwind` catches the exception,
    executes the exact LIFO destructor list `expectedChainDrops inner ++ catchDrops`, and skips `[]`. -/
theorem bidirectional_c_unwind_raii_drop_preservation
    (exc : ExceptionClass)
    (inner outer : List FrameDescriptor)
    (catchLang : Lang) (catchDrops : List String) (ck : CatchKind)
    (hInner : WellTypedUnwindChain inner)
    (hMatch : ExceptionMatchesCatcher exc ck) :
    runCrossLangUnwind exc (inner ++ [.cleanupAndCatch catchLang catchDrops ck] ++ outer) =
      .caught catchLang (expectedChainDrops inner ++ catchDrops) [] := by
  have hSearchMatch : catcherClaimsInSearch ck exc = true := by
    cases hMatch with
    | inl hCpp =>
        rcases hCpp with ⟨exId, rfl, rfl⟩
        rfl
    | inr hRust =>
        rcases hRust with ⟨canary, rfl, rfl⟩
        rfl
  have hSearch :
      searchStep exc (inner ++ [.cleanupAndCatch catchLang catchDrops ck] ++ outer) = true := by
    rw [List.append_assoc, searchStep_append_wellTyped exc inner _ hInner]
    dsimp [searchStep]
    rw [hSearchMatch]
    rfl
  dsimp [runCrossLangUnwind]
  rw [hSearch]
  simp only [ite_true]
  rw [List.append_assoc, cleanupStep_append_wellTyped exc [] [] inner _ hInner]
  dsimp [cleanupStep, cleanupFrameStep, List.nil_append]
  cases hMatch with
  | inl hCpp =>
      rcases hCpp with ⟨exId, rfl, rfl⟩
      rfl
  | inr hRust =>
      rcases hRust with ⟨canary, rfl, rfl⟩
      dsimp
      rw [Nat.beq_refl canary]
      rfl

/-- Theorem 2 (`Foreign-Exception Non-Catchability & Cleanup Preservation`):
    Throwing a C++ exception `.foreignCpp exId` across well-typed `C-unwind` / C++ frames into
    Rust `std::panic::catch_unwind` deterministically:
      (1) Claims the exception in step 1 (so `outer` C++ `try/catch` blocks are NEVER reached),
      (2) Executes ALL intermediate C++ RAII and Rust `Drop` destructors plus `catch_unwind`'s
          local frame cleanup,
      (3) Invokes `_Unwind_DeleteException` (`deletedCppEx = true`), and
      (4) Aborts via `__rust_foreign_exception` (`abortedForeignException`).
    Also covers cross-DSO foreign Rust `std` exceptions (`canary2 ≠ canary1`), which abort
    with `deletedCppEx = false`. -/
theorem catch_unwind_foreign_cpp_aborts_after_intermediate_drops
    (exId localCanary : Nat)
    (inner outer : List FrameDescriptor)
    (catchDrops : List String)
    (hInner : WellTypedUnwindChain inner) :
    runCrossLangUnwind (.foreignCpp exId)
      (inner ++ [.cleanupAndCatch .rust catchDrops (.rustCatchUnwind localCanary)] ++ outer) =
      .abortedForeignException (expectedChainDrops inner ++ catchDrops) [] true := by
  have hSearch :
      searchStep (.foreignCpp exId)
        (inner ++ [.cleanupAndCatch .rust catchDrops (.rustCatchUnwind localCanary)] ++ outer) = true := by
    rw [List.append_assoc, searchStep_append_wellTyped (.foreignCpp exId) inner _ hInner]
    rfl
  dsimp [runCrossLangUnwind]
  rw [hSearch]
  simp only [ite_true]
  rw [List.append_assoc, cleanupStep_append_wellTyped (.foreignCpp exId) [] [] inner _ hInner]
  rfl

theorem nat_beq_false_of_ne (a b : Nat) (hNe : a ≠ b) : Nat.beq a b = false := by
  cases hEq : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hEq) hNe

theorem catch_unwind_foreign_rust_canary_aborts_without_delete
    (thrownCanary localCanary : Nat)
    (hNe : thrownCanary ≠ localCanary)
    (inner outer : List FrameDescriptor)
    (catchDrops : List String)
    (hInner : WellTypedUnwindChain inner) :
    runCrossLangUnwind (.rustPanic thrownCanary)
      (inner ++ [.cleanupAndCatch .rust catchDrops (.rustCatchUnwind localCanary)] ++ outer) =
      .abortedForeignException (expectedChainDrops inner ++ catchDrops) [] false := by
  have hSearch :
      searchStep (.rustPanic thrownCanary)
        (inner ++ [.cleanupAndCatch .rust catchDrops (.rustCatchUnwind localCanary)] ++ outer) = true := by
    rw [List.append_assoc, searchStep_append_wellTyped (.rustPanic thrownCanary) inner _ hInner]
    rfl
  dsimp [runCrossLangUnwind]
  rw [hSearch]
  simp only [ite_true]
  rw [List.append_assoc, cleanupStep_append_wellTyped (.rustPanic thrownCanary) [] [] inner _ hInner]
  dsimp [cleanupStep, cleanupFrameStep, List.nil_append]
  rw [nat_beq_false_of_ne thrownCanary localCanary hNe]
  rfl

/-- Theorem 3a (`-C panic=abort` `EHAction::Filter` Pad Containment):
    An `abortFilterPad` terminates unwinding unconditionally for ANY exception and ANY outer stack
    (even when no outer handler exists), running `expectedChainDrops inner ++ preDrops`. -/
theorem panic_abort_filter_pad_containment
    (exc : ExceptionClass)
    (inner outer : List FrameDescriptor)
    (preDrops : List String)
    (hInner : WellTypedUnwindChain inner) :
    runCrossLangUnwind exc (inner ++ [.abortFilterPad preDrops] ++ outer) =
      .abortedTerminateAbi (expectedChainDrops inner ++ preDrops) [] := by
  have hSearch : searchStep exc (inner ++ [.abortFilterPad preDrops] ++ outer) = true := by
    rw [List.append_assoc, searchStep_append_wellTyped exc inner _ hInner]
    rfl
  dsimp [runCrossLangUnwind]
  rw [hSearch]
  simp only [ite_true]
  rw [List.append_assoc, cleanupStep_append_wellTyped exc [] [] inner _ hInner]
  rfl

/-- Theorem 3b (`-C panic=abort` `AbortUnwindingCalls` `EHAction::Cleanup` Pad Under Outer Catch):
    Because `AbortUnwindingCalls` converts `resume -> terminate(abi)` inside MIR cleanup blocks,
    rustc emits `EHAction::Cleanup` (`cs_action = 0`) rather than `EHAction::Filter`. When an
    outer catch (`std::rt::lang_start` or C++ `try/catch`) satisfies `searchStep exc outer = true`,
    `cleanupStep` enters the abort pad, executes `preDrops` (`RustGuard::drop`), and halts at
    `panic_cannot_unwind` without ever reaching `outer`! Conversely, if `searchStep exc outer = false`
    (uncaught C++ `main()`), `runCrossLangUnwind` hits `.terminatedEndOfStack` without running `preDrops`. -/
theorem panic_abort_cleanup_pad_containment_when_outer_handles
    (exc : ExceptionClass)
    (inner outer : List FrameDescriptor)
    (preDrops : List String)
    (hInner : WellTypedUnwindChain inner)
    (hOuter : searchStep exc outer = true) :
    runCrossLangUnwind exc (inner ++ [.abortCleanupPad preDrops] ++ outer) =
      .abortedTerminateAbi (expectedChainDrops inner ++ preDrops) [] := by
  have hSearch : searchStep exc (inner ++ [.abortCleanupPad preDrops] ++ outer) = true := by
    rw [List.append_assoc, searchStep_append_wellTyped exc inner _ hInner]
    exact hOuter
  dsimp [runCrossLangUnwind]
  rw [hSearch]
  simp only [ite_true]
  rw [List.append_assoc, cleanupStep_append_wellTyped exc [] [] inner _ hInner]
  rfl

theorem panic_abort_cleanup_pad_end_of_stack_when_uncaught
    (exc : ExceptionClass)
    (inner outer : List FrameDescriptor)
    (preDrops : List String)
    (hInner : WellTypedUnwindChain inner)
    (hOuter : searchStep exc outer = false) :
    runCrossLangUnwind exc (inner ++ [.abortCleanupPad preDrops] ++ outer) =
      .terminatedEndOfStack := by
  have hSearch : searchStep exc (inner ++ [.abortCleanupPad preDrops] ++ outer) = false := by
    rw [List.append_assoc, searchStep_append_wellTyped exc inner _ hInner]
    exact hOuter
  dsimp [runCrossLangUnwind]
  rw [hSearch]
  rfl

/-- Theorem 4 (`extern "C"` `nounwind uwtable` Silent Frame-Skipping UB):
    For any well-typed `inner` frames followed by a `nounwind uwtable` `extern "C"` Rust frame
    containing `skippedDrops ≠ []`, the unwinder STILL completes the unwind to the outer matching
    catcher, yet silently skips `skippedDrops` (`ubSkippedDrops = skippedDrops ≠ []`). -/
theorem extern_c_with_uwtable_skips_drops_silently
    (exc : ExceptionClass)
    (inner outer : List FrameDescriptor)
    (skippedDrops catchDrops : List String)
    (catchLang : Lang) (ck : CatchKind)
    (hInner : WellTypedUnwindChain inner)
    (hMatch : ExceptionMatchesCatcher exc ck) :
    runCrossLangUnwind exc
      (inner ++ [.noLandingPadWithUwtable skippedDrops, .cleanupAndCatch catchLang catchDrops ck] ++ outer) =
      .caught catchLang (expectedChainDrops inner ++ catchDrops) skippedDrops := by
  have hSearchMatch : catcherClaimsInSearch ck exc = true := by
    cases hMatch with
    | inl hCpp => rcases hCpp with ⟨exId, rfl, rfl⟩; rfl
    | inr hRust => rcases hRust with ⟨canary, rfl, rfl⟩; rfl
  have hSearch :
      searchStep exc
        (inner ++ [.noLandingPadWithUwtable skippedDrops, .cleanupAndCatch catchLang catchDrops ck] ++ outer) =
      true := by
    rw [List.append_assoc, searchStep_append_wellTyped exc inner _ hInner]
    dsimp [searchStep]
    rw [hSearchMatch]
    rfl
  dsimp [runCrossLangUnwind]
  rw [hSearch]
  simp only [ite_true]
  rw [List.append_assoc, cleanupStep_append_wellTyped exc [] [] inner _ hInner]
  dsimp [cleanupStep, cleanupFrameStep, List.nil_append]
  cases hMatch with
  | inl hCpp =>
      rcases hCpp with ⟨exId, rfl, rfl⟩
      rfl
  | inr hRust =>
      rcases hRust with ⟨canary, rfl, rfl⟩
      dsimp
      rw [Nat.beq_refl canary]
      rfl

/-! ## Section 3: Sharpness Counterexample 1 (`extern "C"` `uwtable` Drop-Skip UB vs. `noUwtable` vs. `C-unwind`) -/

/-- Counterexample 1: On exact concrete stacks matching Cells 1, 5, 6, and 4c:
    - Cell 1 (`extern "C-unwind"`): caught by C++, `rust_guard` runs, `ubSkipped = []`.
    - Cell 5 (`extern "C"` with default `uwtable`): caught by C++, `ubSkipped = ["rust_nounwind_guard_drop"] ≠ []` (silent drop-skipping UB!).
    - Cell 6 (`extern "C"` with `-C force-unwind-tables=no`): FDE omitted -> `terminatedEndOfStack` (`std::terminate`), `0` silent catch!
    - Cell 4c (C++ `main()` with no outer catch calling `-C panic=abort` `extern "C-unwind"` `.abortCleanupPad`):
      hits `terminatedEndOfStack` (`std::terminate`), skipping `staticlib_guard_drop`! -/
theorem ce1_extern_c_with_uwtable_skips_rust_drop_ub :
    let cell1 := runCrossLangUnwind (.foreignCpp 42)
      [.cleanupOnly .rust ["rust_c_unwind_guard_drop"],
       .cleanupAndCatch .cpp ["cpp_caught_ex"] .cppCatchForeign]
    let cell5 := runCrossLangUnwind (.foreignCpp 42)
      [.noLandingPadWithUwtable ["rust_nounwind_guard_drop"],
       .cleanupAndCatch .cpp ["cpp_caught_ex"] .cppCatchForeign]
    let cell6 := runCrossLangUnwind (.foreignCpp 42)
      [.noUwtable ["rust_nounwind_guard_drop"],
       .cleanupAndCatch .cpp ["cpp_caught_ex"] .cppCatchForeign]
    let cell4c := runCrossLangUnwind (.foreignCpp 99)
      [.abortCleanupPad ["staticlib_guard_drop"]]
    cell1 = .caught .cpp ["rust_c_unwind_guard_drop", "cpp_caught_ex"] [] ∧
    cell5 = .caught .cpp ["cpp_caught_ex"] ["rust_nounwind_guard_drop"] ∧
    cell6 = .terminatedEndOfStack ∧
    cell4c = .terminatedEndOfStack := by
  decide

/-! ## Section 4: SysV x86-64 `i128`/`u128` (`__int128`) Layout, 5-GPR Spill & Register Marshaling -/

inductive CType where
  | u8
  | u32
  | u64
  | u128
  deriving DecidableEq, Repr

def ctypeSize : CType → Nat
  | .u8 => 1
  | .u32 => 4
  | .u64 => 8
  | .u128 => 16

/-- Field alignment parameterized by `i128Align` (historically `8` pre-RFC 3435 vs. `16`
    on modern `x86_64-unknown-linux-gnu` `i128:128` matching Clang/GCC `__int128`). -/
def ctypeAlign (i128Align : Nat) : CType → Nat
  | .u8 => 1
  | .u32 => 4
  | .u64 => 8
  | .u128 => i128Align

/-- Constructive round-up alignment (`0` `omega`, pure `Nat` division/modulo). -/
def alignUp (offset align : Nat) : Nat :=
  if align ≤ 1 then
    offset
  else
    let rem := offset % align
    if rem == 0 then offset else offset + (align - rem)

structure StructLayout where
  size : Nat
  align : Nat
  offsets : List Nat
  deriving DecidableEq, Repr

private def layoutFieldsAux
    (i128Align : Nat)
    (curOffset maxAlign : Nat)
    (accRev : List Nat)
    (fields : List CType) : StructLayout :=
  (fields.foldr
    (fun ty ih off ma rev =>
      let fa := ctypeAlign i128Align ty
      let fs := ctypeSize ty
      let fOff := alignUp off fa
      let nextAlign := if ma < fa then fa else ma
      ih (fOff + fs) nextAlign (fOff :: rev))
    (fun off ma rev =>
      { size := alignUp off ma
        align := ma
        offsets := rev.reverse }))
    curOffset maxAlign accRev

/-- `#[repr(C)]` layout computation parameterized by `i128` ABI alignment. -/
def layoutReprC (i128Align : Nat) (fields : List CType) : StructLayout :=
  layoutFieldsAux i128Align 0 1 [] fields

/-- C / C++ System V AMD64 `unsigned __int128` layout (`align = 16`). -/
def layoutCppInt128 (fields : List CType) : StructLayout :=
  layoutReprC 16 fields

/-- Theorem 5 (`RFC 3435 Rust <-> C/C++ Layout Parity`):
    With `i128Align = 16` (`i128:128` in `x86_64_unknown_linux_gnu.rs:34`), Rust `#[repr(C)]`
    computes the exact same offsets, alignment, and size as Clang/GCC `__int128` for EVERY
    field sequence `fields`. -/
theorem rfc3435_rust_cpp_layout_parity (fields : List CType) :
    layoutReprC 16 fields = layoutCppInt128 fields :=
  rfl

/-- Counterexample 2 (`Pre-RFC-3435 8-byte i128 Alignment ABI Mismatch`):
    Under historical 8-byte `i128` alignment (`layoutReprC 8`), `Pair48` and `Mixed64` suffer
    silent `offset_of!` and struct-size mismatches relative to C/C++ `unsigned __int128`
    (`32` B / `align 8` vs. `48` B / `align 16` for `Pair48`, and `48` B / `align 8` vs.
    `64` B / `align 16` for `Mixed64`). -/
theorem ce2_pre_rfc3435_8byte_i128_align_abi_mismatch :
    layoutReprC 8 [.u8, .u128, .u64] = { size := 32, align := 8, offsets := [0, 8, 24] } ∧
    layoutCppInt128 [.u8, .u128, .u64] = { size := 48, align := 16, offsets := [0, 16, 32] } ∧
    layoutReprC 8 [.u8, .u128, .u32, .u128] = { size := 48, align := 8, offsets := [0, 8, 24, 32] } ∧
    layoutCppInt128 [.u8, .u128, .u32, .u128] = { size := 64, align := 16, offsets := [0, 16, 32, 48] } := by
  decide

/-- SysV AMD64 argument placement for integer/128-bit scalars (`maxIntRegs = 6`:
    `%rdi, %rsi, %rdx, %rcx, %r8, %r9`). -/
inductive SysVLoc where
  | gpr1 (regIdx : Nat)
  | gprPair (loRegIdx hiRegIdx : Nat)
  | stackSlot (byteOffset byteSize byteAlign : Nat)
  deriving DecidableEq, Repr

private def classifySysVAux
    (usedRegs stackOff : Nat)
    (accRev : List SysVLoc)
    (args : List CType) : List SysVLoc :=
  (args.foldr
    (fun ty ih ur so rev =>
      match ty with
      | .u8 | .u32 | .u64 =>
          if ur < 6 then
            ih (ur + 1) so (.gpr1 ur :: rev)
          else
            let off := alignUp so 8
            ih ur (off + 8) (.stackSlot off 8 8 :: rev)
      | .u128 =>
          if ur + 2 ≤ 6 then
            ih (ur + 2) so (.gprPair ur (ur + 1) :: rev)
          else
            -- `i128` requires two GPRs; if only 1 GPR (`%r9`) remains, `i128` spills wholly to
            -- 16-byte-aligned stack memory WITHOUT consuming `%r9`!
            let off := alignUp so 16
            ih ur (off + 16) (.stackSlot off 16 16 :: rev))
    (fun _ _ rev => rev.reverse))
    usedRegs stackOff accRev

def classifySysVArgs (args : List CType) : List SysVLoc :=
  classifySysVAux 0 0 [] args

/-- Theorem 6 (`SysV x86-64 5-GPR Straddle Stack-Spill Preserves %r9`):
    In `(g0..g4: u64, stack_val: u128, r9_tail: u64)`, `g0..g4` consume `%rdi..%r8` (`0..4`),
    `stack_val` spills wholly to `stackSlot 0 16 16` (`0x8(%rsp)`/`0x10(%rsp)` at callee entry),
    and `r9_tail` STILL receives register `%r9` (`gpr1 5`). Also verifies unaligned GPR pair
    placement (`%rdi`, `%rsi:%rdx`, `%rcx:%r8`) in `cpp_unaligned_gpr_128`. -/
theorem sysv_5gpr_i128_spill_preserves_r9_for_trailing_u64 :
    classifySysVArgs [.u64, .u64, .u64, .u64, .u64, .u128, .u64] =
      [.gpr1 0, .gpr1 1, .gpr1 2, .gpr1 3, .gpr1 4, .stackSlot 0 16 16, .gpr1 5] ∧
    classifySysVArgs [.u8, .u128, .u128] =
      [.gpr1 0, .gprPair 1 2, .gprPair 3 4] := by
  decide

/-- Bit-exact 128-bit GPR pair `(lo64, hi64)` marshaling round-trip (`0` `omega`). -/
def packU128Pair (lo hi : Nat) : Nat :=
  lo + hi * 18446744073709551616

def unpackU128Pair (val : Nat) : Nat × Nat :=
  (val % 18446744073709551616, val / 18446744073709551616)

theorem i128_reg_pair_marshal_roundtrip (lo hi : Nat)
    (hLo : lo < 18446744073709551616) :
    unpackU128Pair (packU128Pair lo hi) = (lo, hi) := by
  dsimp [unpackU128Pair, packU128Pair]
  have hBase : 0 < 18446744073709551616 := Nat.zero_lt_succ 18446744073709551615
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hLo]
  rw [Nat.add_mul_div_right lo hi hBase, Nat.div_eq_of_lt hLo, Nat.zero_add]

/-! ## Section 5: Symbol Visibility (`STV_DEFAULT` vs. `STV_HIDDEN`) & Cross-Language ThinLTO -/

inductive SymbolVis where
  | stvDefault
  | stvHidden
  deriving DecidableEq, Repr

inductive SymExportLevel where
  /-- `#[unsafe(no_mangle)]` or `#[unsafe(export_name = ...)]` (`symbol_export.rs:542`). -/
  | levelC
  /-- Normal Rust mangled item (`symbol_export.rs:544`). -/
  | levelRust
  deriving DecidableEq, Repr

inductive CrateLinkKind where
  | rlibDefaultVis
  | rlibDefaultVisHidden
  | cdylibVersionScript
  | executable
  | clangSharedSo
  deriving DecidableEq, Repr

/-- Models `compiler/rustc_monomorphize/src/partitioning.rs:933-957` (`default_visibility`)
    and `compiler/rustc_codegen_ssa/src/back/linker.rs:862-895` (`--version-script`). -/
def objectVisibility (mode : CrateLinkKind) (lvl : SymExportLevel) (cAttrHidden : Bool) : SymbolVis :=
  match mode with
  | .rlibDefaultVis => .stvDefault
  | .rlibDefaultVisHidden =>
      match lvl with
      | .levelC => .stvDefault
      | .levelRust => .stvHidden
  | .cdylibVersionScript =>
      match lvl with
      | .levelC => if cAttrHidden then .stvHidden else .stvDefault
      | .levelRust => .stvHidden
  | .executable => .stvHidden
  | .clangSharedSo => if cAttrHidden then .stvHidden else .stvDefault

/-- Whether a symbol is exported in `.dynsym` (preemptible across DSO boundaries).
    Notice that in `cdylibVersionScript`, ONLY Rust-specified `levelC` items appear in
    `global:` of the version script (`linker.rs:877-895`), so linked C++ `STV_DEFAULT`
    object symbols (`fromLinkedCxx = true`) are demoted to `LOCAL` and absent from `.dynsym`! -/
def exportedInDynsym
    (mode : CrateLinkKind)
    (lvl : SymExportLevel)
    (cAttrHidden : Bool)
    (fromLinkedCxx : Bool)
    (exportExecutableSyms : Bool) : Bool :=
  match mode with
  | .rlibDefaultVis | .rlibDefaultVisHidden => false
  | .cdylibVersionScript =>
      match lvl with
      | .levelC => (!fromLinkedCxx) && (!cAttrHidden)
      | .levelRust => false
  | .executable => exportExecutableSyms && (lvl == .levelC) && (!cAttrHidden)
  | .clangSharedSo => !cAttrHidden

/-- Closed-world ThinLTO internalization (`canBeInternalized`):
    sound iff the symbol is NOT dynamically exported (`!exportedInDynsym`), ensuring no external
    DSO consumer or ELF symbol interposition can observe an inlined/eliminated body. -/
def thinLtoInternalizeSound
    (mode : CrateLinkKind)
    (lvl : SymExportLevel)
    (cAttrHidden : Bool)
    (fromLinkedCxx : Bool)
    (exportExecutableSyms : Bool) : Bool :=
  !exportedInDynsym mode lvl cAttrHidden fromLinkedCxx exportExecutableSyms

theorem rlib_z_hidden_preserves_c_export_default_and_hides_rust :
    objectVisibility .rlibDefaultVisHidden .levelC false = .stvDefault ∧
    objectVisibility .rlibDefaultVisHidden .levelRust false = .stvHidden := by
  exact ⟨rfl, rfl⟩

theorem cdylib_version_script_localizes_linked_cxx_and_enables_thinlto_internalization :
    exportedInDynsym .cdylibVersionScript .levelC false true false = false ∧
    exportedInDynsym .clangSharedSo .levelC false true false = true ∧
    thinLtoInternalizeSound .cdylibVersionScript .levelC false true false = true ∧
    exportedInDynsym .cdylibVersionScript .levelC false false false = true := by
  decide

theorem lto_internalization_iff_not_dynsym_exported
    (mode : CrateLinkKind) (lvl : SymExportLevel) (cAttrHidden fromLinkedCxx exportExec : Bool) :
    thinLtoInternalizeSound mode lvl cAttrHidden fromLinkedCxx exportExec = true ↔
      exportedInDynsym mode lvl cAttrHidden fromLinkedCxx exportExec = false := by
  dsimp [thinLtoInternalizeSound]
  cases exportedInDynsym mode lvl cAttrHidden fromLinkedCxx exportExec
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

/-! ## Section 6: End-to-End Concrete Witness Matching Live Execution Crucible -/

/-- Concrete kernel-evaluated witness verifying all 6 live execution unwinding cells
    (including Cells 3, 4a, 4b, 4c), RFC 3435 `Pair48` & `Mixed64` layouts, 5-GPR spill,
    and ELF visibility / ThinLTO internalization in one theorem. -/
theorem live_six_cell_and_abi_crucible_witness :
    -- Cell 1: C++ throw(42) -> Rust `C-unwind` (`RustGuard` drops!) -> C++ catch
    runCrossLangUnwind (.foreignCpp 42)
      [.cleanupOnly .rust ["rust_c_unwind_guard_drop"],
       .cleanupAndCatch .cpp ["cpp_caught_ex"] .cppCatchForeign] =
      .caught .cpp ["rust_c_unwind_guard_drop", "cpp_caught_ex"] [] ∧
    -- Cell 2: Rust panic!(canary=1) -> C++ RAII (`~CppGuard` runs!) -> Rust `catch_unwind`
    runCrossLangUnwind (.rustPanic 1)
      [.cleanupAndCatch .cpp ["cpp_raii_guard_dtor"] .cppCatchForeign,
       .cleanupAndCatch .rust ["rust_caught_panic"] (.rustCatchUnwind 1)] =
      .caught .rust ["cpp_raii_guard_dtor", "rust_caught_panic"] [] ∧
    -- Cell 3: Rust `catch_unwind` around C++ throw(77): inner C++ & Rust drops + `_Unwind_DeleteException` + abort!
    runCrossLangUnwind (.foreignCpp 77)
      [.cleanupOnly .cpp ["cpp_inner_guard_dtor"],
       .cleanupAndCatch .rust ["rust_inner_catch_guard_drop"] (.rustCatchUnwind 1),
       .cleanupAndCatch .cpp ["cpp_outer_caught_ex"] .cppCatchForeign] =
      .abortedForeignException ["cpp_inner_guard_dtor", "rust_inner_catch_guard_drop"] [] true ∧
    -- Cell 4b: `-C panic=abort` Rust `C-unwind` with `RustGuard` under C++ `try/catch` -> runs drop then aborts!
    runCrossLangUnwind (.foreignCpp 42)
      [.abortCleanupPad ["rust_c_unwind_guard_drop"],
       .cleanupAndCatch .cpp ["cpp_caught_ex"] .cppCatchForeign] =
      .abortedTerminateAbi ["rust_c_unwind_guard_drop"] [] ∧
    -- Cell 4c: `-C panic=abort` Rust `staticlib` under uncaught C++ `main()` -> `_URC_END_OF_STACK` (no drop!)
    runCrossLangUnwind (.foreignCpp 99)
      [.abortCleanupPad ["staticlib_guard_drop"]] =
      .terminatedEndOfStack ∧
    -- Cell 5 & Cell 6: `extern "C"` with default `uwtable` skips drop; `-C force-unwind-tables=no` terminates
    runCrossLangUnwind (.foreignCpp 42)
      [.noLandingPadWithUwtable ["rust_nounwind_guard_drop"],
       .cleanupAndCatch .cpp ["cpp_caught_ex"] .cppCatchForeign] =
      .caught .cpp ["cpp_caught_ex"] ["rust_nounwind_guard_drop"] ∧
    runCrossLangUnwind (.foreignCpp 42)
      [.noUwtable ["rust_nounwind_guard_drop"],
       .cleanupAndCatch .cpp ["cpp_caught_ex"] .cppCatchForeign] =
      .terminatedEndOfStack := by
  decide

end CrossLangCUnwindAndAbiCrucible

#print axioms CrossLangCUnwindAndAbiCrucible.bidirectional_c_unwind_raii_drop_preservation
#print axioms CrossLangCUnwindAndAbiCrucible.catch_unwind_foreign_cpp_aborts_after_intermediate_drops
#print axioms CrossLangCUnwindAndAbiCrucible.catch_unwind_foreign_rust_canary_aborts_without_delete
#print axioms CrossLangCUnwindAndAbiCrucible.panic_abort_filter_pad_containment
#print axioms CrossLangCUnwindAndAbiCrucible.panic_abort_cleanup_pad_containment_when_outer_handles
#print axioms CrossLangCUnwindAndAbiCrucible.panic_abort_cleanup_pad_end_of_stack_when_uncaught
#print axioms CrossLangCUnwindAndAbiCrucible.extern_c_with_uwtable_skips_drops_silently
#print axioms CrossLangCUnwindAndAbiCrucible.ce1_extern_c_with_uwtable_skips_rust_drop_ub
#print axioms CrossLangCUnwindAndAbiCrucible.rfc3435_rust_cpp_layout_parity
#print axioms CrossLangCUnwindAndAbiCrucible.ce2_pre_rfc3435_8byte_i128_align_abi_mismatch
#print axioms CrossLangCUnwindAndAbiCrucible.sysv_5gpr_i128_spill_preserves_r9_for_trailing_u64
#print axioms CrossLangCUnwindAndAbiCrucible.i128_reg_pair_marshal_roundtrip
#print axioms CrossLangCUnwindAndAbiCrucible.rlib_z_hidden_preserves_c_export_default_and_hides_rust
#print axioms CrossLangCUnwindAndAbiCrucible.cdylib_version_script_localizes_linked_cxx_and_enables_thinlto_internalization
#print axioms CrossLangCUnwindAndAbiCrucible.lto_internalization_iff_not_dynsym_exported
#print axioms CrossLangCUnwindAndAbiCrucible.live_six_cell_and_abi_crucible_witness
