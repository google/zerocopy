<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Structural External Call Semantics, Open-World Callback Framing, and TCB Semantic Mutation Testing

## Summary

Anneal's Trusted Computing Base (TCB) checks each crate's `Trusted.CrateTheorem`
inside the Lean 4 kernel over the operational semantics in
`Anneal.Trusted.SemanticModel` and `Anneal.Trusted.MirSemantics` (or
`Anneal.Trusted.X86Semantics` on the `exp/mir-to-x86` branch). That architecture
prevents forged proofs inside `theory/`, but soundness still depends on two
semantic boundary properties inside `trusted/`: (1) whether the operational
model of external calls and library type invariants (`AdtInv` / `LibInv`) is
sound under open-world re-entrant callbacks, and (2) whether fail-open defects
or weakened guards inside the trusted evaluators are caught by negative
refutation canaries.

This report establishes four mechanized results, backed by the standalone
5,814-line Lean 4 development in
[`support/StructuralExternalCallAndCanaries.lean`](support/StructuralExternalCallAndCanaries.lean)
and two automated mutation harnesses:

1. **Entry/exit-only invariant framing is unsound under open-world re-entrant
   callbacks.** `EnsuresRetLibInv` (`Trusted/MirSemantics.lean:457-461` and
   `Trusted/X86Semantics.lean:338-343`) checks custom ADT invariants only at
   function entry and return. When an `unsafe` block temporarily invalidates a
   private ADT invariant on a stack slot whose `&mut` or `&` reference is
   reachable by an unknown external call, modeling the external call via
   unguarded post-call nondeterminism unsoundly verifies the caller while
   concrete linking against a re-entrant callback triggers Undefined Behavior
   (`canary_unchecked_callback_unsoundly_accepts_reentrantBuggyFn`,
   `naive_withTempInvalid_verified`, and
   `naive_reentrancy_exploit_triggers_ub`). In addition,
   `Trusted/X86Semantics.lean` declares `Reg64` (`L24-28`) and `BytePerm`
   (`L42-46`) without wiring either into `X86State` (`L84-90`), and both
   `MirVal.ref ⟨slot⟩` (`Trusted/MirSemantics.lean:81`) and
   `X86Val.stackPtr ⟨slot⟩` (`Trusted/X86Semantics.lean:62`) omit a call-frame
   identifier, allowing dereference operations in a callee to alias the
   active frame's slots by raw index.
2. **A first-class `StepResult.externalCall` constructor enforces call-site
   invariants and frame isolation while keeping all prefix-reachability
   theorems 100% constructive (`Classical.choice`-free).** Extending
   `StepResult` with `externalCall (boundaryInv : Bool) (next : State → Obs →
   Prop)` (`support/StructuralExternalCallAndCanaries.lean:148-153`) and
   `ReachesPrefix` with `externalCallFail`, `externalCallOk`, and
   `emptyExternalCall` (`L189-236`) separates caller-side invariant obligations
   (`boundaryInv = false` steps to `.failed .invariantViolation`) from
   callee-side post-call transitions (`CallerFramePreserved`,
   `CallerFrameIsolated`, and `X86AbiFramePreserved`). Encoding `boundaryInv`
   as `Bool` (populated via `decide P` for any `[Decidable P]`) rather than a
   dependent `(boundaryInv : Prop)` field with `[Decidable boundaryInv]`
   prevents Lean 4's generated `StepResult.noConfusion` eliminator from pulling
   in `Classical.choice`: all five core prefix-reachability theorems
   (`exists_reaches_prefix`, `non_vacuity_at_every_depth`,
   `reachesPrefix_of_step`, `reachesPrefix_of_terminated`, and
   `reachesPrefix_of_externalCall` at `L277-482`) depend on **zero axioms**.
   Under this discipline, mid-call invariant violations are refuted
   (`canary_reentrant_callback_rejected`,
   `withTempInvalid_rejected_under_guarded_call`,
   `structural_withTempInvalid_rejected`), safe callback patterns verify
   (`canary_safe_callback_verified`, `withRestoredBeforeCall_verified`,
   `structural_withRestoredBeforeCall_verified`,
   `withUnexposedPrivateTemp_verified`), and arbitrary-depth re-entrant
   callback composition is proved sound by straight-line induction on the fuel
   parameter `steps : Nat` (`open_world_callback_composition_sound` at
   `L5250-5295`) without step-indexed Iris logic or coinduction.
3. **Empirical semantic mutation testing shows that baseline canaries kill only
   20.83% (5/24) of TCB evaluator mutations, whereas the 24-canary negative
   refutation suite kills 100.0% (24/24) on both branches.** Across 24
   single-site semantic mutations (`M01`–`M24`) applied to
   `Trusted/MirSemantics.lean` (`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`)
   and 24 homologous mutations (`X01`–`X24`) applied to
   `Trusted/X86Semantics.lean` (`4f45f0a391a921ced9c9dc773b9a040dbc215d14`),
   the five baseline negative canary theorems in `theory/Anneal/MirLemmas.lean`
   and `theory/Anneal/X86Lemmas.lean` detect only 5 of 24 mutations (20.83%),
   leaving 19 of 24 fail-open evaluator mutations undetected. The augmented
   negative refutation suite (`canary_M01`–`canary_M24b` at
   `support/StructuralExternalCallAndCanaries.lean:1815-2515` and
   `canary_X01`–`canary_X24a` in
   [`support/run_trusted_mutation_audit.py`](support/run_trusted_mutation_audit.py))
   kills all 24/24 (100.0%) mutations on both branches
   ([`support/mutation_audit_results.json`](support/mutation_audit_results.json)).
4. **A proof-gated `BoundaryCanarySuite` typeclass achieves a 100.0% (13/13)
   kill rate across target-ISA and CTFE negative-polarity vacuity guards.**
   The `BoundaryCanarySuite (M : X86MachineModel) : Prop` typeclass
   (`support/StructuralExternalCallAndCanaries.lean:2570-2655`) bundles 11
   positive conformance witnesses and 10 negative refutation theorems across 10
   semantic guards (64-bit modular ALU wrap, `% 64` shift masking, `#DE`
   division-by-zero and `INT64_MIN / -1` traps, stack-frame slot bounds,
   16-byte `rsp` call alignment, System V AMD64 callee-saved register
   preservation, `transmute_copy` byte-size equality, `AdtInv` validity checks,
   and CTFE negative-polarity vacuity guards). The unfixed `currentX86Model` is
   provably refuted (`currentX86Model_fails_BoundaryCanarySuite` at
   `L2685-2694`), the repaired `fixedX86Model` instantiates the suite
   (`instBoundaryCanarySuiteFixedX86Model` at `L2771-2802`), and
   ([`support/run_guard_mutation_probe.py`](support/run_guard_mutation_probe.py))
   verifies that mutating any of the 13 annotated guard sites
   (`-- MUTATE_GUARD:`) causes Lean 4 kernel typechecking to fail (`13/13`
   killed,
   [`support/guard_mutation_results.json`](support/guard_mutation_results.json)).

## Applicability

This report applies to Anneal's TCB operational semantics, behavioral
refinement framework, and `.olean` boundary audit pipeline across the following
commits and components:

| Repository / Branch | Pinned Commit | Target Components |
| :--- | :--- | :--- |
| `trusted-core-experiment` | `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` | `trusted/lean/Anneal/Trusted/SemanticModel.lean`, `trusted/lean/Anneal/Trusted/MirSemantics.lean`, `theory/Anneal/MirLemmas.lean`, `trusted/audit/src/main.rs`, `trusted/cargo-anneal/src/main.rs` |
| `exp/mir-to-x86` | `4f45f0a391a921ced9c9dc773b9a040dbc215d14` | `trusted/lean/Anneal/Trusted/SemanticModel.lean`, `trusted/lean/Anneal/Trusted/X86Semantics.lean`, `theory/Anneal/X86Lemmas.lean` |
| Lean 4 Kernel / Toolchain | `leanprover/lean4:v4.34.1` | Standalone verification with `-DElab.async=false -Ddebug.skipKernelTC=false` |

The findings govern any extension of Anneal that (a) verifies functions making
indirect calls, trait-object dispatches, or FFI/unknown external calls while
maintaining private library invariants (`AdtInv` / `LibInv`), or (b) modifies
the trusted small-step evaluators (`MirSemantics.lean`, `X86Semantics.lean`) and
their accompanying boundary audit (`anneal-audit`).

## Findings

### Finding 1: Open-World Callback Re-Entrancy Exploit, Unwired ISA Types, and the Cross-Frame Pointer Aliasing Seam

#### 1.1 Why Entry/Exit-Only `EnsuresRetLibInv` Fails Across Callbacks

In both `Trusted/MirSemantics.lean:457-461` (`trusted-core-experiment`) and
`Trusted/X86Semantics.lean:338-343` (`exp/mir-to-x86`), library-defined type
invariants (`AdtInv` / `LibInv`) are enforced by assuming the invariant on
function arguments in `effectivePre` and asserting `EnsuresRetLibInv` on normal
return:

```lean
def EnsuresRetLibInv (libInv : LibInv) (retTy : X86Ty) : X86Lang.Behavior :=
  X86Lang.Spec (fun q out =>
    match out.outcome with
    | .terminated (.normal retVal) => libInv q.prog.tySizes retTy retVal
    | _ => True)
```

For a closed call graph of known internal functions, checking invariants at
entry and exit suffices because every internal call `.call dst calleeIdx args
target` steps directly into `q.prog.callees[calleeIdx]?`. When a function
invokes an unknown external function or user-supplied callback, however, the
callee's body is not statically known. If an external call is modeled simply by
havocking exposed mutable targets and jumping to the return continuation
without checking that active library invariants hold at the moment of the call,
the following re-entrancy exploit becomes verifiable:

1. A library defines an ADT with a private field and a safety invariant—for
   example, `BoundedIdx { val: usize }` with `boundedIdxInv : val < 4`
   (`support/StructuralExternalCallAndCanaries.lean:3466-3485`), or an ADT with
   `NonZeroAdtInv : field₀ ≠ 0` (`L547-558`).
2. The library provides a safe method `get_unchecked(&self) -> usize` that
   relies on `boundedIdxInv` to index a 4-element buffer without a dynamic
   bounds check. Under `effectivePre`, `naive_getUnchecked_verified`
   (`L3817-3999`) proves that `getUncheckedOpenBody` satisfies both
   `WellFormedOn` and `EnsuresOpenRetLibInv`.
3. A second safe function `with_temp_invalid(&mut self, cb: fn(&BoundedIdx))`
   temporarily writes an invalid value (`99 ≥ 4`, or `0` in `reentrantBuggyFn`
   at `L828-851`) into `*self`, invokes the unknown callback `cb(self)` while
   `*self` violates the invariant, and then restores `*self` to a valid value
   (`0 < 4`, or `1 ≠ 0`) before returning.
4. Under an unchecked external-call model that checks `EnsuresRetLibInv` only
   at function entry and return, `with_temp_invalid` **unsoundly verifies**:
   - At the MIR level,
     `canary_unchecked_callback_unsoundly_accepts_reentrantBuggyFn`
     (`L939-1000`) proves `UncheckedMirSem reentrantBuggyFn ≤
     UncheckedMirLang.WellFormedOn ...` and `EnsuresRetNonZeroAdt`.
   - At the x86-64 level, `naive_withTempInvalid_verified` (`L4002-4073`)
     proves that `withTempInvalidOpenBody` satisfies both `WellFormedOn` and
     `EnsuresOpenRetLibInv boundedIdxInv (.adt 0)`.
5. When `withTempInvalidOpenBody` is linked against a concrete callback that
   simply calls the already-verified `getUncheckedOpenBody` on the passed
   reference, concrete execution reaches `.failed .assertionFailure`
   (out-of-bounds indexing UB) in 7 steps, as proved by
   `naive_reentrancy_exploit_triggers_ub` (`L4152-4205`):

```lean
theorem naive_reentrancy_exploit_triggers_ub :
    ∃ s0, (LinkedMachine withTempInvalidOpenBody getUncheckedOpenBody).init
        withTempInvalidOpenBody s0 ∧
      ReachesPrefix (LinkedMachine withTempInvalidOpenBody getUncheckedOpenBody)
        withTempInvalidOpenBody 7 s0 [] (.failed .assertionFailure)
```

#### 1.2 Unwired ISA Declarations and the Cross-Frame Pointer Aliasing Seam

Auditing `Trusted/X86Semantics.lean` at commit
`4f45f0a391a921ced9c9dc773b9a040dbc215d14` alongside
`Trusted/MirSemantics.lean` at commit
`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` reveals three structural seams in
the trusted state representation:

| Seam | Location in `trusted/` | Architectural Defect | Consequence for Open-World Calls |
| :--- | :--- | :--- | :--- |
| Unwired `Reg64` and `isCalleeSaved` | `Trusted/X86Semantics.lean:24-35` vs. `X86State` (`L84-90`) | `Reg64` (`rax`, `rcx`, `rdx`, `rdi`, `rsi`, `r8`–`r11`, `rbx`, `rbp`, `r12`–`r15`, `rsp`) and `Reg64.isCalleeSaved` are defined in the TCB but never referenced in `X86State`, `evalX86Instr`, or `evalX86Term`. | System V AMD64 ABI register preservation (`rbx`, `rbp`, `r12`–`r15`, `rsp`) cannot be stated or checked across `.call` / `.ret` transitions. |
| Unwired `BytePerm` | `Trusted/X86Semantics.lean:42-46` vs. `X86State` (`L84-90`) | `BytePerm` (`unalloc`, `uninit`, `readOnly`, `writable`) is defined in the TCB, but `X86State` uses only `mem : Nat → Option X86Val` (`None` = uninit/dead, `Some v` = initialized) with no permission map. | Read-only shared borrows (`&T`, `BytePerm.readOnly`) cannot be distinguished from mutable borrows (`&mut T`, `BytePerm.writable`) during an external call. |
| Frame-less stack pointers (`MirVal.ref` / `X86Val.stackPtr`) | `Trusted/MirSemantics.lean:81,182-196` and `Trusted/X86Semantics.lean:62,163-177` | `MirVal.ref (target : LocalId)` and `X86Val.stackPtr (target : SlotId)` carry only a raw `Nat` slot index. On `.call`, `evalMirTerminator` / `evalX86Term` pushes the caller's `locals` / `mem` onto `callStack` and installs a fresh map for the callee, but `.derefCopy`, `.derefAssign`, `.derefLoad`, and `.derefStore` index the *currently active* `s.locals` / `s.mem`. | Passing `&local_k` from a caller to an internal callee causes dereferences inside the callee to read or overwrite the *callee's* slot `k` rather than the caller's slot `k`. |

In `OpenWorldCallbackFraming`
(`support/StructuralExternalCallAndCanaries.lean:3557-3669`), `OpenState` wires
both `regs : Reg64 → Nat` and `perms : Nat → BytePerm` directly into machine
execution (`checkWritableSlot` at `L3589-3594` gates every slot write and
`.derefStore` on `BytePerm.writable`, and `X86AbiFramePreserved` at
`L4241-4253` enforces preservation of every callee-saved register across
external calls).

---

### Finding 2: Constructive `StepResult.externalCall` and Frame-Isolated Open-World Call Semantics

#### 2.1 Extending `StepResult` and `ReachesPrefix` Without `Classical.choice`

To enforce library invariants at external call boundaries structurally inside
`SemanticModel.lean`, `StructuralExternalCall`
(`support/StructuralExternalCallAndCanaries.lean:148-236`) adds a fourth
constructor to `StepResult`:

```lean
inductive StepResult (State Obs Val : Type) where
  | step (next : State) (obs : Option Obs)
  | choice (kind : ChoiceKind) (branches : State → Obs → Prop)
  | externalCall (boundaryInv : Bool) (next : State → Obs → Prop)
  | terminated (kind : TerminationKind Val)
  | failed (kind : FailureKind)
```

Correspondingly, `ReachesPrefix` (`L189-236`) replaces unconstrained call
stepping with three explicit rules for `.externalCall boundaryInv next`:

- **`externalCallFail` (`L217-220`)**: When `boundaryInv = false`, the call
  immediately reaches `.failed .invariantViolation` in one step. This models
  the caller's obligation: invoking an external function while an exposed
  library invariant is broken is immediate Undefined Behavior.
- **`externalCallOk` (`L221-228`)**: When `boundaryInv = true`, every post-call
  state `(s', o)` satisfying `next s' o` (which encodes the callee's return
  guarantee and caller-frame preservation) continues execution for the
  remaining `n` fuel steps.
- **`emptyExternalCall` (`L229-235`)**: Analogous to `emptyDemonic` for
  `.choice .demonic`, if `boundaryInv = true` and `next` is uninhabited
  (`∀ s' o, ¬ next s' o`), execution reaches `.failed .impossibleBranch`,
  preventing an empty post-call transition relation from vacuously discharging
  universal path obligations.

**Why `boundaryInv` is typed as `Bool` rather than `Prop`:** A natural
alternative (explored in `StepResultExt` at `L5303-5308`) stores
`(boundaryInv : Prop)` inside `StepResult`. However, if an inductive type
stores both `(boundaryInv : Prop)` and a typeclass instance
`[Decidable boundaryInv]`, Lean 4's automatically generated `noConfusion`
eliminator performs dependent elimination over a type family indexed by a
`Prop`, which pulls `Classical.choice` into the kernel axiom footprint of
any theorem that discriminates constructors (such as `evalStmt_not_choice` or
`exists_reaches_prefix`). If `StepResultExt` instead omits `[Decidable
boundaryInv]`, proving `exists_reaches_prefix` for an arbitrary machine requires
`Classical.em boundaryInv` (and therefore `Classical.choice`).

By storing `(boundaryInv : Bool)` inside `StepResult.externalCall` and
evaluating decidable propositions at the call site via `decide P` (or a boolean
checker coupled with a reflection lemma `checkBoundaryInv ... = true ↔
BoundaryInvHolds ...` at `L570-588`), `StepResult` remains a first-order data
type in `Type`. As a result, all five foundational metatheorems in
`StructuralExternalCall` (`L277-482`) are **100% constructive** and depend on
**zero axioms** (`#print axioms` reports `[]`):

| Metatheorem | Lines in `StructuralExternalCallAndCanaries.lean` | Role | Axiom Footprint |
| :--- | :--- | :--- | :--- |
| `exists_reaches_prefix` | `L277-335` | Under `TotalStep M` and `InhabitedDemonic M`, every `(p, n, s)` has at least one reachable `PrefixOutcome`. | `[]` (zero axioms) |
| `non_vacuity_at_every_depth` | `L341-364` | `WellFormedOn` implies a safe reachable trace (`PrefixOutcome.isSafe`) at every fuel depth `n`. | `[]` (zero axioms) |
| `reachesPrefix_of_step` | `L370-397` | Unfolds `WellFormedOn` across a deterministic `.step` transition by incrementing fuel `n + 1`. | `[]` (zero axioms) |
| `reachesPrefix_of_terminated` | `L403-427` | Extracts postcondition obligations at `.terminated (.normal v)` with fuel `1`. | `[]` (zero axioms) |
| `reachesPrefix_of_externalCall` | `L435-482` | Proves from `WellFormedOn` at fuel `1` that `boundaryInv = true` holds at the call site, and propagates `WellFormedOn` and `SpecOn` to every post-call state `(s', o)` satisfying `next s' o`. | `[]` (zero axioms) |

#### 2.2 Frame Isolation, Re-Entrancy Refutation, and Straight-Line Fuel Induction

Both the MIR instantiation (`ExtMirMachine` at `L705-713`) and the x86-64
instantiations (`GuardedOpenMachine` at `L4396-4404` and
`StructuralOpenMachine` at `L5481-5490`) enforce two complementary properties
at every external call (`Terminator.externalCall` / `OpenTerm.externalCall`):

1. **Pre-call invariant guard (`BoundaryInvHolds` / `CallSiteSatisfiesLibInv`,
   `L570-588` and `L4216-4228`)**: Every exposed slot (shared or mutable) and
   every outbound argument must satisfy the library's `AdtInv` / `LibInv`
   before control leaves the current function.
2. **Post-call frame and ABI isolation (`CallerFramePreserved` at `L590-593`,
   `X86AbiFramePreserved` at `L4241-4253`, and `CallerFrameIsolated` at
   `L4255-4258`)**:
   - Unexposed caller locals/slots (`slot ∉ exposedMutSlots`) and read-only
     shared slots (`BytePerm.readOnly`) are preserved identically (`s'.mem slot
     = s.mem slot`).
   - All System V AMD64 callee-saved registers (`rbx`, `rbp`, `r12`–`r15`,
     `rsp`) and slot permissions (`s'.perms = s.perms`) are preserved.
   - Return destinations (`dstSlot`) and exposed mutable slots
     (`slot ∈ exposedMutSlots`) may take arbitrary new values provided those
     values satisfy `libInv`.

This separation yields four verified security and expressiveness guarantees:

- **Mid-call invariant violations are rejected:**
  `canary_reentrant_callback_rejected` (`L854-902`),
  `withTempInvalid_rejected_under_guarded_call` (`L4609-4635`), and
  `structural_withTempInvalid_rejected` (`L5581-5613`) prove `¬ (... ≤
  WellFormedOn ...)` because the pre-call guard evaluates to `false` on the
  temporarily corrupted slot (`0` or `99`), stepping directly to `.failed
  .invariantViolation`.
- **Safe callback callers that restore invariants before the call verify:**
  `canary_safe_callback_verified` (`L1034-1147`),
  `withRestoredBeforeCall_verified` (`L4637-4790`), and
  `structural_withRestoredBeforeCall_verified` (`L5615-5810`) prove full memory
  safety and return-invariant preservation when the caller restores the
  temporary mutation prior to `externalCall`.
- **Callers that keep temporary invariant violations in unexposed private slots
  verify across callbacks:** `withUnexposedPrivateTemp_verified` (`L4792-4983`)
  proves that a function may hold an invalid `BoundedIdx` (`99`) in a private,
  unexposed stack slot (`slot 2 ∉ exposedSlots`) across an `externalCall` and
  rely on `CallerFrameIsolated` to preserve its private slot across the call.
- **Multi-depth re-entrant composition requires only straight-line `Nat`
  induction:** Because `ReachesPrefix` is indexed by a finite step counter
  `steps : Nat`, `concrete_to_guarded_reachesPrefix` (`L5030-5248`) and
  `open_world_callback_composition_sound` (`L5250-5295`) prove by standard
  induction on `steps : Nat` that any concrete callback environment
  `cbEnv : CallbackEnv` satisfying `SoundCallbackEnv` refines
  `GuardedOpenMachine` (`ConcreteCallbackMachine cbEnv ≤ GuardedOpenMachine`).
  Every re-entrant callback invocation consumes at least one step of fuel,
  eliminating the semantic circularity that otherwise motivates step-indexed
  Iris logic or coinductive bisimulations.

---

### Finding 3: Empirical TCB Mutation Audit of `MirSemantics.lean` (`M01`–`M24`) and `X86Semantics.lean` (`X01`–`X24`)

#### 3.1 Baseline vs. Augmented Mutation Kill Rate

To measure whether Anneal's existing boundary canaries detect fail-open bugs in
the TCB evaluators,
[`support/run_trusted_mutation_audit.py`](support/run_trusted_mutation_audit.py)
injects 24 single-site semantic mutations (`M01`–`M24`) into
`trusted/lean/Anneal/Trusted/MirSemantics.lean` (commit
`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and 24 homologous mutations
(`X01`–`X24`) into `trusted/lean/Anneal/Trusted/X86Semantics.lean` (commit
`4f45f0a391a921ced9c9dc773b9a040dbc215d14`), re-running the Lean 4 kernel
(`-DElab.async=false -Ddebug.skipKernelTC=false`) on each mutant against both
the baseline theory lemmas (`MirLemmas.lean` / `X86Lemmas.lean`) and the
augmented 24-canary negative refutation suite:

| Target Branch & Evaluator | Total Mutants | Killed by Baseline Theory Suite | Survived Baseline Theory Suite | Baseline Kill Rate | Killed by Augmented 24-Canary Suite | Augmented Kill Rate |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `trusted-core-experiment` (`Trusted/MirSemantics.lean`, `M01`–`M24`) | 24 | 5 (`M04`, `M07`, `M13`, `M16`, `M17`) | 19 | **20.83%** | **24 / 24** | **100.0%** |
| `exp/mir-to-x86` (`Trusted/X86Semantics.lean`, `X01`–`X24`) | 24 | 5 (`X04`, `X07`, `X13`, `X16`, `X17`) | 19 | **20.83%** | **24 / 24** | **100.0%** |

Why do 19 of 24 mutations survive the baseline suite? Because positive
universal step lemmas in `MirLemmas.lean` (such as `step_assign_use`,
`step_ref`, or `step_return`) include hypotheses asserting that the instruction
is well-typed and its source operands are initialized (`s.locals src.idx = some
v`). When a fail-open mutation weakens a failure branch so that an invalid state
steps to a dummy value instead of `.failed`, the positive lemma's `some v`
hypothesis still selects the non-failing branch, so its proof continues to
typecheck. Only negative refutation theorems (`¬ (MirSem badBody ≤
MirLang.WellFormedOn ...)` or `¬ (MirSem badBody ≤ Spec ...)`) force the
evaluator through its failure branches and break when a failure branch is
weakened.

#### 3.2 Complete 24-Mutant Matrix for `Trusted/MirSemantics.lean` (`M01`–`M24`)

All 25 negative canary theorems for `MirSemantics` (`canary_M01` through
`canary_M24b`) are mechanized and kernel-verified in
`AnnealReference.TrustedMutationCanaries`
(`support/StructuralExternalCallAndCanaries.lean:1815-2515`):

| ID | Target Definition (`MirSemantics.lean`) | Injected Semantic Mutation | Baseline (`MirLemmas.lean`) | Augmented Suite (`StructuralExternalCallAndCanaries.lean`) |
| :--- | :--- | :--- | :---: | :--- |
| `M01` | `evalTyByteSize` (`L115`) | Mutate `.usize => 8` to `.usize => 4` | SURVIVED | **KILLED** (`canary_M01_sizeOf_usize_wrong_rejected`, `L1815`) |
| `M02` | `evalTyByteSize` (`L117`) | Mutate `.bool => 1` to `.bool => 0` | SURVIVED | **KILLED** (`canary_M02_sizeOf_bool_wrong_rejected`, `L1847`) |
| `M03` | `evalOperand` (`L199`) | Fail-open `.copy src`: return `some (.usize 0), locals` when `locals src.idx = none` | SURVIVED | **KILLED** (`canary_M03_uninit_copy_violates_wellFormed`, `L1879`) |
| `M04` | `evalOperand` (`L202`) | Omit destructive clear `updateLocal locals src.idx none` on `.move src` | KILLED (`canary_double_move_unsound`) | **KILLED** (`canary_M04_double_move_violates_wellFormed`, `L1901`) |
| `M05` | `evalOperand` (`L203`) | Fail-open `.move src`: return `some (.usize 0), locals` when `locals src.idx = none` | SURVIVED | **KILLED** (`canary_M05_uninit_move_violates_wellFormed`, `L1930`) |
| `M06` | `evalBinOp` (`L213`) | Invert `.eq` comparison `(a == b)` to `(a != b)` | SURVIVED | **KILLED** (`canary_M06_eq_distinct_usize_not_true`, `L1950`) |
| `M07` | `evalBinOp` (`L217`) | Fail-open ill-typed binary operation `_ => none` to `_ => some (.bool false)` | KILLED (`canary_ill_typed_binop_unsound`) | **KILLED** (`canary_M07_illTyped_binOp_violates_wellFormed`, `L1983`) |
| `M08` | `evalMirStmt` (`L226`) | Fail-open `.assign dst (.use op)` on `none` operand to no-op `.step { s with stmtIdx := s.stmtIdx + 1 } none` | SURVIVED | **KILLED** (`canary_M08_failed_use_assign_violates_wellFormed`, `L2004`) |
| `M09` | `evalMirStmt` (`L244`) | Fail-open `.aggregate`: substitute `.usize 0` when an operand evaluates to `none` | SURVIVED | **KILLED** (`canary_M09_uninit_aggregate_violates_wellFormed`, `L2031`) |
| `M10` | `evalMirStmt` (`L255`) | Fail-open `.field0` on non-ADT value: step with `.usize 0` instead of `.failed .typeMismatch` | SURVIVED | **KILLED** (`canary_M10_field0_non_adt_violates_wellFormed`, `L2058`) |
| `M11` | `evalMirStmt` (`L260-265`) | Remove `s.locals src.idx` initialization check on `.assign dst (.ref src)` | SURVIVED | **KILLED** (`canary_M11_ref_uninit_violates_wellFormed`, `L2085`) |
| `M12` | `evalMirStmt` (`L269-273`) | Remove target-liveness check `s.locals target.idx` on `.reborrow ptrLocal` | SURVIVED | **KILLED** (`canary_M12_reborrow_dead_target_violates_wellFormed`, `L2115`) |
| `M13` | `evalMirStmt` (`L301`) | Make `.storageDead localId` a no-op (leave `s.locals localId.idx` live) | KILLED (`canary_use_after_storage_dead_unsound`) | **KILLED** (`canary_M13_use_after_storageDead_violates_wellFormed`, `L2160`) |
| `M14` | `evalTransmuteCopy` (`L314`) | Remove outer byte-size equality check `evalTyByteSize tySizes srcTy == evalTyByteSize tySizes dstTy` | SURVIVED | **KILLED** (`canary_M14_transmute_size_mismatch_violates_wellFormed`, `L2198`) |
| `M15` | `evalTransmuteCopy` (`L326`) | Remove inner pointee byte-size check `evalTyByteSize tySizes srcInner == evalTyByteSize tySizes dstInner` on `.rawPtr` | SURVIVED | **KILLED** (`canary_M15_transmute_mismatched_pointee_bytes_violates_wellFormed`, `L2231`) |
| `M16` | `evalMirTerminator` (`L345`) | Fail-open `.return`: return `.terminated (.normal (.usize 0))` when `_0` is uninitialized | KILLED (`canary_uninitialized_return_unsound`) | **KILLED** (`canary_M16_uninit_return_violates_wellFormed`, `L2258`) |
| `M17` | `evalMirTerminator` (`L347`) | Mutate `.unreachable` from `.failed .unreachableExecuted` to `.terminated (.normal .unit)` | KILLED (`canary_unreachable_unsound`) | **KILLED** (`canary_M17_unreachable_violates_wellFormed`, `L2273`) |
| `M18` | `ConstSucceeds` (`L432`) | Weaken `ConstSucceeds` to `True` (admitting panicking CTFE constants) | SURVIVED | **KILLED** (`canary_M18_panicking_const_rejected_by_constSucceeds`, `L2288`) |
| `M19` | `evalMirTerminator` (`L356`) | Fail-open `.switchInt` on non-boolean operand: jump to `elseTarget` instead of `.failed .typeMismatch` | SURVIVED | **KILLED** (`canary_M19_switchInt_non_bool_violates_wellFormed`, `L2332`) |
| `M20` | `evalMirTerminator` (`L359-361`) | Fail-open out-of-bounds `.goto target`: terminate with `.unit` instead of `.failed .invalidControlFlow` | SURVIVED | **KILLED** (`canary_M20_oob_goto_violates_wellFormed`, `L2347`) |
| `M21` | `AdmissibleAdtInv` (`L454`) | Weaken `AdmissibleAdtInv` to `True` (allowing non-trivial invariants on all-`pubSafe` ADTs) | SURVIVED | **KILLED** (`canary_M21_pub_safe_fields_reject_nonzero_inv`, `L2370`) |
| `M22` | `EnsuresRetLibInv` (`L460`) | Weaken `.terminated (.normal retVal)` return invariant check to `True` | SURVIVED | **KILLED** (`canary_M22_buggy_zero_adt_return_rejected`, `L2385`) |
| `M23` | `defaultTrustPolicy` (`L479`) | Mutate `.userAxiom _ => False` to `True` (admitting unapproved user axioms) | SURVIVED | **KILLED** (`canary_M23_unapproved_userAxiom_rejected`, `L2422`) |
| `M24` | `CrateTheorem` (`L527-531`) | Drop `AllHold (fn.effectiveSpecs c.adtInv)` and `c.unsafeImpls.foldr ...` from `CrateTheorem` | SURVIVED | **KILLED** (`canary_M24a_unsound_unsafeImpl_rejected`, `L2439`; `canary_M24b_wrong_id_violates_ensures`, `L2454`) |

#### 3.3 Complete 24-Mutant Matrix for `Trusted/X86Semantics.lean` (`X01`–`X24`)

[`support/run_trusted_mutation_audit.py`](support/run_trusted_mutation_audit.py)
likewise verifies the 24 homologous x86-64 mutations (`X01`–`X24`) against
`Trusted/X86Semantics.lean`:

| ID | Target Definition (`X86Semantics.lean`) | Injected Semantic Mutation | Baseline (`X86Lemmas.lean`) | Augmented Suite (`canary_X01`–`canary_X24a`) |
| :--- | :--- | :--- | :---: | :--- |
| `X01` | `evalX86TyByteSize` (`L97`) | Mutate `.u64 => 8` to `.u64 => 4` | SURVIVED | **KILLED** (`canary_X01_sizeOf_u64_wrong_rejected`) |
| `X02` | `evalX86TyByteSize` (`L99`) | Mutate `.bool => 1` to `.bool => 0` | SURVIVED | **KILLED** (`canary_X02_sizeOf_bool_wrong_rejected`) |
| `X03` | `evalX86Operand` (`L136`) | Fail-open `.slotRead src`: return `some (.u64 0), mem` when `mem src.idx = none` | SURVIVED | **KILLED** (`canary_X03_uninit_slotRead_violates_wellFormed`) |
| `X04` | `evalX86Operand` (`L139`) | Omit destructive clear `updateSlot mem src.idx none` on `.slotTake src` | KILLED (`canary_double_slot_take_unsound`) | **KILLED** (`canary_X04_double_slotTake_violates_wellFormed`) |
| `X05` | `evalX86Operand` (`L140`) | Fail-open `.slotTake src`: return `some (.u64 0), mem` when `mem src.idx = none` | SURVIVED | **KILLED** (`canary_X05_uninit_slotTake_violates_wellFormed`) |
| `X06` | `evalX86BinOp` (`L150`) | Invert `.cmpEq` comparison `(a == b)` to `(a != b)` | SURVIVED | **KILLED** (`canary_X06_cmpEq_distinct_u64_not_true`) |
| `X07` | `evalX86BinOp` (`L160`) | Fail-open ill-typed binary operation `_ => none` to `_ => some (.bool false)` | KILLED (`canary_ill_typed_x86_binop_unsound`) | **KILLED** (`canary_X07_illTyped_binOp_violates_wellFormed`) |
| `X08` | `evalX86Instr` (`L169`) | Fail-open `.mov dst op` on `none` operand to no-op `.step { s with instrIdx := s.instrIdx + 1 } none` | SURVIVED | **KILLED** (`canary_X08_failed_mov_violates_wellFormed`) |
| `X09` | `evalX86Instr` (`L187`) | Fail-open `.packStruct`: substitute `.u64 0` when an operand evaluates to `none` | SURVIVED | **KILLED** (`canary_X09_uninit_packStruct_violates_wellFormed`) |
| `X10` | `evalX86Instr` (`L198`) | Fail-open `.extractField0` on non-ADT value: step with `.u64 0` instead of `.failed .typeMismatch` | SURVIVED | **KILLED** (`canary_X10_extractField0_non_adt_violates_wellFormed`) |
| `X11` | `evalX86Instr` (`L203-208`) | Remove `s.mem src.idx` initialization check on `.leaStack dst src` | SURVIVED | **KILLED** (`canary_X11_leaStack_uninit_violates_wellFormed`) |
| `X12` | `evalX86Instr` (`L212-216`) | Remove target-liveness check `s.mem target.idx` on `.reborrowPtr dst ptrSlot` | SURVIVED | **KILLED** (`canary_X12_reborrowPtr_dead_target_violates_wellFormed`) |
| `X13` | `evalX86Instr` (`L244`) | Make `.killSlot slotId` a no-op (leave `s.mem slotId.idx` live) | KILLED (`canary_use_after_kill_slot_unsound`) | **KILLED** (`canary_X13_use_after_killSlot_violates_wellFormed`) |
| `X14` | `evalRepMovsb` (`L257`) | Remove outer byte-size equality check `evalX86TyByteSize tySizes srcTy == evalX86TyByteSize tySizes dstTy` | SURVIVED | **KILLED** (`canary_X14_repMovsb_size_mismatch_violates_wellFormed`) |
| `X15` | `evalRepMovsb` (`L269`) | Remove inner pointee byte-size check `evalX86TyByteSize tySizes srcInner == evalX86TyByteSize tySizes dstInner` on `.rawPtr` | SURVIVED | **KILLED** (`canary_X15_repMovsb_mismatched_pointee_bytes_violates_wellFormed`) |
| `X16` | `evalX86Term` (`L288`) | Fail-open `.ret`: return `.terminated (.normal (.u64 0))` when slot `0` is uninitialized | KILLED (`canary_uninitialized_ret_unsound`) | **KILLED** (`canary_X16_uninit_ret_violates_wellFormed`) |
| `X17` | `evalX86Term` (`L290`) | Mutate `.ud2` from `.failed .unreachableExecuted` to `.terminated (.normal .unit)` | KILLED (`canary_ud2_unsound`) | **KILLED** (`canary_X17_ud2_violates_wellFormed`) |
| `X18` | `evalX86Term` (`L292`) | Mutate `.abort` from `.terminated .panicked` to `.terminated (.normal .unit)` | SURVIVED | **KILLED** (`canary_X18_abort_not_normal_return`) |
| `X19` | `evalX86Term` (`L299`) | Fail-open `.jccBool` on non-boolean operand: jump to `elseTarget` instead of `.failed .typeMismatch` | SURVIVED | **KILLED** (`canary_X19_jccBool_non_bool_violates_wellFormed`) |
| `X20` | `evalX86Term` (`L302-304`) | Fail-open out-of-bounds `.jmp target`: terminate with `.unit` instead of `.failed .invalidControlFlow` | SURVIVED | **KILLED** (`canary_X20_oob_jmp_violates_wellFormed`) |
| `X21` | `AdmissibleLibInv` (`L329`) | Weaken `AdmissibleLibInv` to `True` (allowing non-trivial invariants on all-`pubSafe` ADTs) | SURVIVED | **KILLED** (`canary_X21_pub_safe_fields_reject_nonzero_inv`) |
| `X22` | `EnsuresRetLibInv` (`L341`) | Weaken `.terminated (.normal retVal)` return invariant check to `True` | SURVIVED | **KILLED** (`canary_X22_buggy_zero_adt_return_rejected`) |
| `X23` | `evalX86Term` (`L307`) | Fail-open out-of-bounds `.call` `calleeIdx`: terminate with `.unit` instead of `.failed .invalidControlFlow` | SURVIVED | **KILLED** (`canary_X23_oob_callee_call_violates_wellFormed`) |
| `X24` | `evalX86Instr` (`L230`) | Fail-open `.derefLoad` on dead referent slot: step with `.u64 0` instead of `.failed .invalidMemoryAccess` | SURVIVED | **KILLED** (`canary_X24a_derefLoad_dead_slot_violates_wellFormed`) |

#### 3.4 Architectural Enforcement in `anneal-audit`

Currently, `trusted/audit/src/main.rs` inspects only the crate's target theorem
(`CrateTheorem`) and its transitive dependencies, which never traverse negative
canary theorems in `MirLemmas.lean` or `X86Lemmas.lean`. To make the 24-canary
suite a structural gate on the TCB:

1. Place `canary_M01`–`canary_M24b` (and `canary_X01`–`canary_X24a`) in a
   dedicated module (`Anneal.Theory.Canaries`) compiled alongside `MirLemmas` /
   `X86Lemmas`.
2. Extend `trusted/audit/src/main.rs` (`verify_environment`) with a required
   canary manifest check verifying that every `canary_M01`..`canary_M24b`
   constant is present in the compiled `.olean` environment, has its expected
   negative refutation type (`¬ ...`), and has an axiom footprint free of
   `sorryAx`.

---

### Finding 4: Proof-Gated `BoundaryCanarySuite` Typeclass and Automated 13-Guard Mutation Probe

Beyond fail-open evaluator bugs in the existing `MirSemantics` and
`X86Semantics` definitions, `Trusted/X86Semantics.lean` models 64-bit registers
using unbounded `Nat` arithmetic (`a + b` at `L212`, truncating `a - b` at
`L213`, unmasked shifts at `L221-222`) and unbounded stack slot maps (`Nat →
Option X86Val`). To prevent any target-ISA or CTFE polarity guard from being
omitted or weakened, `AnnealReference.BoundaryCanary`
(`support/StructuralExternalCallAndCanaries.lean:2523-2804`) defines the
`X86MachineModel` interface (`L2542-2568`) and the mandatory typeclass
`BoundaryCanarySuite (M : X86MachineModel) : Prop` (`L2570-2655`).

`BoundaryCanarySuite` requires 11 positive conformance witnesses and 10 negative
refutation theorems across 10 semantic guards:

- **Guard 1 (64-bit modular arithmetic wrap):** `canary_pos_add64_wrap`,
  `canary_neg_add64_no_unbounded_nat`, `canary_pos_sub64_wrap`, and
  `canary_neg_sub64_no_zero_truncation` enforce `2^64` modular wrapping on
  `(2^64 - 1) + 1 = 0` and `0 - 1 = 2^64 - 1`, refuting
  `Trusted/X86Semantics.lean:212-213`.
- **Guard 2 (`% 64` shift-count masking and `RFlags`):**
  `canary_pos_shl64_mask_and_flags`, `canary_pos_shr64_mask`, and
  `canary_neg_shift64_no_unmasked_count` enforce `cl & 0x3f` shift masking on
  `count = 64` (`1 <<< (64 % 64) = 1`), refuting unmasked shifts (`1 <<< 64 = 0`
  or `2^64`).
- **Guard 3 (`#DE` division traps):** `canary_pos_idiv64_valid`,
  `canary_neg_idiv64_div_zero_traps`, and
  `canary_neg_idiv64_intmin_overflow_traps` enforce hardware `#DE` traps on
  `divisor = 0` and `INT64_MIN / -1`.
- **Guard 4 (Stack-frame slot bounds):** `canary_pos_slot_write_in_bounds` and
  `canary_neg_slot_write_out_of_bounds_traps` enforce `slotIdx < slotCount`.
- **Guard 5 (System V AMD64 16-byte `rsp` call alignment):**
  `canary_pos_call_rsp_aligned16` and `canary_neg_call_rsp_misaligned_traps`
  enforce `rsp % 16 == 0` at `call`.
- **Guard 6 (System V AMD64 callee-saved register preservation):**
  `canary_pos_ret_callee_saved_preserved` and
  `canary_neg_ret_callee_saved_clobbered_traps` enforce `savedEntry ==
  savedExit` at `ret`.
- **Guard 7 (`transmute_copy` byte-size equality):**
  `canary_pos_transmute_copy_same_size` and
  `canary_neg_transmute_copy_size_mismatch_traps` enforce `srcSz == dstSz`.
- **Guard 8 (`AdtInv` validity check on typed loads):**
  `canary_pos_load_bool_valid` and
  `canary_neg_load_bool_invalid_discriminant_traps` enforce `byteVal < 2` when
  loading a `bool`.
- **Guards 9 & 10 (CTFE negative-polarity vacuity guards):**
  `canary_ctfe_polarity_guards` enforces three non-vacuity properties on
  `effectivePre`: (a) unmodeled CTFE instructions are rejected
  (`¬ (M.ctfeEval false true).noUnmodeled`), (b) well-behaved modeled CTFE
  functions are admitted (`(M.ctfeEval true true).monoAdmitted`), and (c)
  genuinely failing CTFE functions are excluded (`¬ (M.ctfeEval true
  false).monoAdmitted`).

In `support/StructuralExternalCallAndCanaries.lean`,
`currentX86Model_fails_BoundaryCanarySuite` (`L2685-2694`) proves `¬
BoundaryCanarySuite currentX86Model`, while
`instBoundaryCanarySuiteFixedX86Model` (`L2771-2802`) proves
`BoundaryCanarySuite fixedX86Model`. The automated probe
[`support/run_guard_mutation_probe.py`](support/run_guard_mutation_probe.py)
systematically mutates each of the 13 `-- MUTATE_GUARD:` sites in
`fixedX86Model` and confirms a **13/13 (100.0%)** kill rate
([`support/guard_mutation_results.json`](support/guard_mutation_results.json)):

| Mutation ID | Guard Tag (`-- MUTATE_GUARD:`) | Quadrant | Injected Guard Weakening | Expected Canary Failure | Kernel Result |
| :--- | :--- | :--- | :--- | :--- | :---: |
| `M01_alu_mod64_add_unbounded_nat` | `alu_mod64_add` | Quadrant 2 (Target ISA ALU) | `(va + vb).toNat` → `a + b` | `canary_pos_add64_wrap` | **KILLED** (`exit_code=1`, `L2773`) |
| `M02_alu_mod64_sub_truncating_nat` | `alu_mod64_sub` | Quadrant 2 (Target ISA ALU) | `(va - vb).toNat` → `a - b` | `canary_pos_sub64_wrap` | **KILLED** (`exit_code=1`, `L2775`) |
| `M03_shift_mask64_shl_unmasked` | `shift_mask64_check` | Quadrant 2 (Target ISA Shift/Flags) | `count % 64` → `count` on `shlq` | `canary_pos_shl64_mask_and_flags` | **KILLED** (`exit_code=1`, `L2777`) |
| `M04_shift_mask64_shr_unmasked` | `shift_mask64_shr_check` | Quadrant 2 (Target ISA Shift) | `count % 64` → `count` on `shrq` | `canary_neg_shift64_no_unmasked_count` | **KILLED** (`exit_code=1`, `L2780`) |
| `M05_div_zero_guard_disabled` | `div_zero_check` | Quadrant 1 / 2 (Division Trap) | `divisor == 0#64` → `false` | `canary_neg_idiv64_div_zero_traps` | **KILLED** (`exit_code=1`, `L2786`) |
| `M06_idiv_signed_overflow_guard_disabled` | `idiv_overflow_check` | Quadrant 1 / 2 (Signed Division Overflow) | `dividend == int64Min && divisor == negOne` → `false` | `canary_neg_idiv64_intmin_overflow_traps` | **KILLED** (`exit_code=1`, `L2787`) |
| `M07_slot_bounds_guard_disabled` | `slot_bounds_check` | Quadrant 2 (Stack-Frame Bounds) | `slotIdx < slotCount` → `true` | `canary_neg_slot_write_out_of_bounds_traps` | **KILLED** (`exit_code=1`, `L2789`) |
| `M08_rsp_align16_guard_disabled` | `rsp_align16_check` | Quadrant 2 (System V AMD64 ABI Alignment) | `rsp % 16 == 0` → `true` | `canary_neg_call_rsp_misaligned_traps` | **KILLED** (`exit_code=1`, `L2791`) |
| `M09_callee_saved_guard_disabled` | `callee_saved_check` | Quadrant 2 (System V AMD64 Callee-Saved) | `savedEntry == savedExit` → `true` | `canary_neg_ret_callee_saved_clobbered_traps` | **KILLED** (`exit_code=1`, `L2793`) |
| `M10_transmute_size_guard_disabled` | `transmute_size_check` | Quadrant 1 / 2 (Transmute Copy Size) | `srcSz == dstSz` → `true` | `canary_neg_transmute_copy_size_mismatch_traps` | **KILLED** (`exit_code=1`, `L2795`) |
| `M11_adt_inv_guard_disabled` | `adt_inv_check` | Quadrant 1 / 2 (ADT Validity Invariant) | `byteVal < 2` → `true` | `canary_neg_load_bool_invalid_discriminant_traps` | **KILLED** (`exit_code=1`, `L2797`) |
| `M12_ctfe_no_unmodeled_guard_disabled` | `ctfe_no_unmodeled_check` | Quadrant 4 (CTFE Negative-Polarity Vacuity) | `noUnmodeled := isModeled` → `true` | `canary_ctfe_polarity_guards` | **KILLED** (`exit_code=1`, `L2798`) |
| `M13_ctfe_mono_admitted_forced_false` | `ctfe_mono_admitted_check` | Quadrant 4 (Spurious CTFE Failure Vacuity) | `monoAdmitted := isModeled && constPassed` → `false` | `canary_ctfe_polarity_guards` | **KILLED** (`exit_code=1`, `L2798`) |

## Boundaries

To keep the scope of the mechanized artifacts clear, the following table
separates what is fully proved in this package from what remains a modeling
simplification or integration step for production `trusted/` deployment:

| Dimension | Mechanized in This Package (`support/`) | Remaining Production Integration Boundary |
| :--- | :--- | :--- |
| External call step & prefix semantics | `StepResult.externalCall (boundaryInv : Bool) (next : State → Obs → Prop)` and `ReachesPrefix` (`externalCallFail`, `externalCallOk`, `emptyExternalCall`) with 100% axiom-free metatheorems (`L148-482`), plus `StepResultExt` (`L5303-5420`). | Port `StepResult.externalCall` and `reachesPrefix_of_externalCall` into `trusted/lean/Anneal/Trusted/SemanticModel.lean` and emit `.externalCall` from `anneal-rustc-capture` for unresolved/indirect calls. |
| Frame isolation & pointer representation | `CallerFramePreserved` (`L590`), `CallerFrameIsolated` (`L4255`), `X86AbiFramePreserved` (`L4241`), and `BytePerm` write-gating (`checkWritableSlot` at `L3589`) over `OpenState` with explicit `exposedSlots` and `exposedMutSlots`. | Replace flat `LocalId`/`SlotId` pointers (`MirVal.ref ⟨slot⟩` / `X86Val.stackPtr ⟨slot⟩`) in `MirSemantics.lean` and `X86Semantics.lean` with frame-qualified `(FrameId × SlotId)` addresses so cross-frame references never alias callee slots. |
| Multi-depth callback soundness | `concrete_to_guarded_reachesPrefix` (`L5030`) and `open_world_callback_composition_sound` (`L5250`) proved by straight-line induction on `steps : Nat` for single-callee `CallbackEnv`. | Generalize `CallbackEnv` from single-callee arity to arbitrary mutually recursive callback tables and multi-argument System V AMD64 register/stack passing. |
| TCB mutation & guard canaries | 25 `MirSemantics` negative canaries (`canary_M01`–`canary_M24b`, `L1815-2515`), 24 `X86Semantics` negative canaries (`run_trusted_mutation_audit.py`), and `BoundaryCanarySuite` (`L2570-2802`) with 100% kill rates. | Wire the negative canary manifest check directly into `trusted/audit/src/main.rs` so `cargo anneal` rejects any `.olean` environment missing the canary theorems. |

## Evidence

### Package Support Files

All supporting code, proofs, and machine-readable mutation results reside in
[`support/`](support/):

| File | Lines | Bytes | SHA-256 | Role |
| :--- | ---: | ---: | :--- | :--- |
| [`support/StructuralExternalCallAndCanaries.lean`](support/StructuralExternalCallAndCanaries.lean) | 5,814 | 229,123 | `947ed4e2a2b75d7ed3c3cef8a521bd7364aed529bfc815a4f34113075ea1519d` | Self-contained Lean 4 (`v4.34.1`) formalization containing `StructuralExternalCall`, `TrustedMutationCanaries` (`canary_M01`–`canary_M24b`), `BoundaryCanary` (`BoundaryCanarySuite`), and `OpenWorldCallbackFraming`. Zero `sorryAx`, zero `Lean.ofReduceBool`. |
| [`support/run_trusted_mutation_audit.py`](support/run_trusted_mutation_audit.py) | 2,220 | 95,344 | `840af0363df7a6e13cc85255dbd2e3d20c35cbce3233385aa8727f15eca564af` | Automated 48-mutant semantic mutation harness (`M01`–`M24` on `MirSemantics.lean` and `X01`–`X24` on `X86Semantics.lean`). |
| [`support/mutation_audit_results.json`](support/mutation_audit_results.json) | 619 | 39,272 | `9650426598a00cce920f26a9e74f7c10cb295f7a0aa2a0bc525d66af5d1432a9` | Machine-readable output of `run_trusted_mutation_audit.py` recording baseline (`5/24` = `20.83%`) vs. augmented (`24/24` = `100.0%`) mutation kill results across both branches. |
| [`support/run_guard_mutation_probe.py`](support/run_guard_mutation_probe.py) | 256 | 12,116 | `4ff90255a58fe2cb71ee1a78c499cbaefa262b7f436b9761d4fb57d7f7f709db` | Automated 13-guard mutation probe testing `BoundaryCanarySuite` against all `-- MUTATE_GUARD:` markers in `StructuralExternalCallAndCanaries.lean`. |
| [`support/guard_mutation_results.json`](support/guard_mutation_results.json) | 140 | 6,547 | `446e6da675a24e0d38cf29ca3b51c72b87bbb402baa31ac5a4e8d7f93ed8c458` | Machine-readable output of `run_guard_mutation_probe.py` recording `13/13` (`100.0%`) killed guard mutations. |

### Key Mechanized Declarations in `support/StructuralExternalCallAndCanaries.lean`

| Namespace | Declaration | Lines | Summary |
| :--- | :--- | :--- | :--- |
| `StructuralExternalCall` | `StepResult` & `ReachesPrefix` | `L148-236` | Adds `.externalCall (boundaryInv : Bool) (next : State → Obs → Prop)` and constructors `externalCallFail`, `externalCallOk`, `emptyExternalCall`. |
| `StructuralExternalCall` | `exists_reaches_prefix` & `non_vacuity_at_every_depth` | `L277-364` | Constructive (`Classical.choice`-free) proof that `TotalStep` + `InhabitedDemonic` guarantees a reachable prefix outcome at every depth `n`. |
| `StructuralExternalCall` | `reachesPrefix_of_externalCall` | `L435-482` | Extracts `boundaryInv = true` at fuel `1` and propagates `WellFormedOn` / `SpecOn` across all post-call states `(s', o)`. |
| `StructuralExternalCall` | `extMir_totalStep` & `extMir_inhabitedDemonic` | `L767-822` | Discharges `TotalStep` and `InhabitedDemonic` for `ExtMirMachine`. |
| `StructuralExternalCall` | `canary_reentrant_callback_rejected` | `L854-902` | Refutes `reentrantBuggyFn` under `ExtMirMachine` when `NonZeroAdtInv` is violated at the external call site. |
| `StructuralExternalCall` | `canary_unchecked_callback_unsoundly_accepts_reentrantBuggyFn` | `L939-1000` | Proves that omitting the call-site invariant check (`UncheckedMirMachine`) unsoundly verifies `reentrantBuggyFn`. |
| `StructuralExternalCall` | `canary_safe_callback_verified` | `L1034-1147` | Verifies `safeCallbackFn` (which restores `NonZeroAdtInv` before calling out) under `ExtMirMachine`. |
| `TrustedMutationCanaries` | `canary_M01_sizeOf_usize_wrong_rejected` .. `canary_M24b_wrong_id_violates_ensures` | `L1815-2515` | 25 negative canary refutation theorems killing all 24 semantic mutations (`M01`–`M24`) of `Trusted/MirSemantics.lean`. |
| `BoundaryCanary` | `BoundaryCanarySuite` | `L2570-2655` | Proof-gated typeclass of 11 positive witnesses and 10 negative refutations across 10 target-ISA and CTFE polarity guards. |
| `BoundaryCanary` | `currentX86Model_fails_BoundaryCanarySuite` | `L2685-2694` | Refutes `currentX86Model` (unbounded `Nat` ALU/shifts, unguarded slot writes). |
| `BoundaryCanary` | `instBoundaryCanarySuiteFixedX86Model` | `L2771-2802` | Instantiates `BoundaryCanarySuite` for `fixedX86Model` (with 13 `-- MUTATE_GUARD:` markers). |
| `OpenWorldCallbackFraming` | `naive_getUnchecked_verified` & `naive_withTempInvalid_verified` | `L3817-4073` | Proves that under entry/exit-only `EnsuresOpenRetLibInv`, both `getUncheckedOpenBody` and `withTempInvalidOpenBody` verify in isolation. |
| `OpenWorldCallbackFraming` | `naive_reentrancy_exploit_triggers_ub` | `L4152-4205` | Proves that linking `withTempInvalidOpenBody` with `getUncheckedOpenBody` reaches `.failed .assertionFailure` in 7 steps. |
| `OpenWorldCallbackFraming` | `withTempInvalid_rejected_under_guarded_call` | `L4609-4635` | Refutes `withTempInvalidOpenBody` under `GuardedOpenMachine`. |
| `OpenWorldCallbackFraming` | `withRestoredBeforeCall_verified` & `withUnexposedPrivateTemp_verified` | `L4637-4983` | Verifies both restored-before-call and unexposed-private-slot callback patterns under `GuardedOpenMachine`. |
| `OpenWorldCallbackFraming` | `open_world_callback_composition_sound` | `L5250-5295` | Proves by straight-line induction on `steps : Nat` that linking against any `SoundCallbackEnv` preserves `WellFormedOn` and `EnsuresGuardedRetLibInv`. |
| `OpenWorldCallbackFraming` | `structural_withTempInvalid_rejected` & `structural_withRestoredBeforeCall_verified` | `L5581-5810` | Proves rejection of `withTempInvalidOpenBody` and verification of `withRestoredBeforeCallOpenBody` under `StructuralOpenMachine` (`StepResultExt`). |

## Revalidation

All verification commands below can be run from this package directory
(`reports/anneal-structural-external-calls-and-tcb-mutation-testing-2026/`).

### 1. Kernel-Verify `support/StructuralExternalCallAndCanaries.lean`

Requires Lean 4 `v4.34.1` (`lean` on `PATH` or under
`~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean`):

```bash
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/StructuralExternalCallAndCanaries.lean
```

Expected outcome: exit code `0`, zero warnings, zero `sorryAx`, zero
`Lean.ofReduceBool`, and `#print axioms` output confirming `[]` (zero axioms)
on `exists_reaches_prefix`, `non_vacuity_at_every_depth`,
`reachesPrefix_of_step`, `reachesPrefix_of_terminated`, and
`reachesPrefix_of_externalCall`.

### 2. Re-Run the 13-Guard Mutation Probe (`BoundaryCanarySuite`)

Runs entirely against `support/StructuralExternalCallAndCanaries.lean` with no
external repository checkout required:

```bash
python3 support/run_guard_mutation_probe.py \
  --target-file support/StructuralExternalCallAndCanaries.lean \
  --output-json support/guard_mutation_results.json
```

Expected outcome: exit code `0`, `Total guard mutations tested: 13`, `Killed by
BoundaryCanarySuite: 13`, `Survived: 0`, and `Mutation kill rate: 100.0%`.

### 3. Re-Run the 48-Mutant TCB Semantic Mutation Audit (`M01`–`M24` and `X01`–`X24`)

Requires checkouts of `trusted-core-experiment`
(`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and `exp/mir-to-x86`
(`4f45f0a391a921ced9c9dc773b9a040dbc215d14`):

```bash
python3 support/run_trusted_mutation_audit.py \
  --trusted-core-root /path/to/anneal-trusted-core-experiment \
  --mir-to-x86-root /path/to/anneal-mir-to-x86 \
  --out-dir support
```

Expected outcome: exit code `0`, regenerating
`support/mutation_audit_results.json` with `5/24` (`20.83%`) baseline kill rate
and `24/24` (`100.0%`) augmented canary kill rate across both `MirSemantics`
and `X86Semantics`.
