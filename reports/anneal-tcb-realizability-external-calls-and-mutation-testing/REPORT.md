# TCB Realizability, Proof-Gated Compilation, Structural External Calls, Mutation Testing, and TrustedBoundary Elaboration Probes

## Summary

This report consolidates ten mechanized and empirical findings across Anneal's
trusted verification kernel (`Trusted/Refinement.lean`,
`Trusted/StepResult.lean`, `Trusted/MirSemantics.lean`,
`Trusted/X86Semantics.lean`, and `trusted/audit/TrustedBoundary.lean` at
`joshlf/anneal` `origin/main` commits `24367bd1a8c784f2578535954f9915e24894a56f`,
`beb778bb135474a67dc017c185d2753a60693d8c`, and
`f2bc17e9be87b777d63c785b31f3370ff058d69b`), paired with four standalone Lean 4
(`v4.34.1`) proof developments (`support/TcbConsistencyAndAuditProbes.lean`,
`support/ProofGatedCompilationAndTrustPolicy.lean`,
`support/ProofGatedAndCanarySuite.lean`, and
`support/StructuralExternalCallAndCanaries.lean`), a 48-mutant TCB semantic
mutation harness (`support/run_trusted_mutation_audit.py` and
`support/mutation_audit_results.json`), a 13-guard `BoundaryCanarySuite`
mutation probe (`support/run_guard_mutation_probe.py` and
`support/guard_mutation_results.json`), and a 12-case `TrustedBoundary.lean`
Phase 1 (`preflight`) + Phase 2 (`audit`) elaboration and binder spoofing probe
suite (`support/run_audit_probes.py` and `support/audit_probe_results.json`):

1. **Contradictory `opaque` TCB Witnesses & Universal Realizability (`TCBModel`):**
   In the MIR verification prototype (`Trusted/Refinement.lean` and
   `Trusted/MirSemantics.lean`), `VerificationResultOn policy L_s L_t C p spec`
   takes `hTcb : policy.AllHold` in the antecedent of a material implication,
   where `TrustedAssumption.holds .compilerLowering = C.SoundOn (fun _ => True)`
   is evaluated against four concrete `opaque` constants (`rustc`, `TargetSem`,
   `π_c`, and `TargetArtifact`). Because `C.SoundOn (fun _ => True)` universally
   quantifies over all `(p : MirBody)` and `(q : MirQuery)` — including bodies
   rejected by `MonoAdmitted` or executed with `steps = 0` where `MirSem p q` is
   already `.defined .outOfFuel` — any interpretation where `TargetSem (rustc p)
   (π_c.mapQuery q) = .undefined` makes `RustcCompiler.SoundOn (fun _ => True)`
   provably `False` (`pme_rejected_target_undefined_soundOn_false` and
   `hidden_opaque_witness_soundOn_false` in
   `support/TcbConsistencyAndAuditProbes.lean`). Consequently, `hTcb` acts as an
   unverified axiom schema over fixed `opaque` witnesses (`contradictory_hTcb_proves_ub_crate`).
   Replacing fixed `opaque` constants with universal quantification over all
   models `(M : TCBModel)` satisfying `M.RealizesTCB` (`UniversalVerificationResult`)
   can never carry a contradictory antecedent because `refTCBModel : TCBModel`
   constructively inhabits `RealizesTCB` (`refTCBModel_realizes_tcb`,
   `relative_consistency_meta_theorem`, `universal_hTcb_never_contradictory`,
   and `alwaysUbCrate_unprovable_under_universal_tcb`, all proved with `0`
   axioms).
2. **Unverified Rust-to-x86 Capture Gap:**
   In the x86-64 verification prototype (`trusted/rustc-capture/src/lib.rs` and
   `Trusted/X86Semantics.lean`), `rustc-capture` lowers Rust MIR directly to
   `X86Body` (`render_x86_body`) and `.anneal/Prog.s` (`render_x86_assembly`) in
   unverified Rust code. Neither `MirBody` nor `Anneal.compileStage0` nor
   `.anneal/Prog.s` appears in `Mir.crate : Trusted.Crate` or
   `Proof.verify_crate : Trusted.CrateTheorem Mir.crate`. Theorem
   `mir_to_x86_unverified_capture_gap` (`0` axioms) proves that a buggy
   `rustc-capture` lowering a safe Rust function (`mirSafeFn`) into an UB
   `X86Body` (`x86BuggyCapture`) while emitting a trivial `X86Body` into
   `Mir.crate` still satisfies `CrateTheorem` unless the source `MirBody` and
   verified compilation obligation `Compiles MirLang X86Lang
   MirToX86Morphism.toMorphism compileStage0 p` are bound inside `CrateTheorem`
   (`verified_pipeline_rejects_capture_mismatch`, `0` axioms).
3. **Proof-Gated Compilation Eliminates Intermediate IRs and Passes from the TCB:**
   In `support/ProofGatedCompilationAndTrustPolicy.lean` and
   `support/ProofGatedAndCanarySuite.lean`, we mechanize `BoundaryCodec` /
   `BehaviorCodec` and prove that when a verification pipeline requires both the
   source proof (`L_ir.WellFormedOn D p` and `L_ir.SpecOn D p S_ir`) and the
   pass compilation proof (`Compiles L_ir L_t π pass p`), an untrusted
   intermediate semantics `L_ir` can neither hide target UB nor drop reachable
   target outcomes:
   - Adding spurious UB to `L_ir` blocks the source proof
     (`spurious_ir_ub_blocks_source_obligation`,
     `spurious_ub_breaks_wellFormedOn`, `0` axioms);
   - Omitting real UB from `L_ir` blocks the pass compilation proof
     (`omitted_ir_ub_blocks_pass_obligation`, `missing_ub_breaks_compiles`, `0`
     axioms);
   - Omitting reachable execution outcomes from `L_ir` blocks the pass
     compilation proof (`omitted_ir_outcome_blocks_pass_obligation`,
     `missing_outcome_breaks_compiles`, `0` axioms);
   - Composing both proofs transfers `WellFormedOn` and `SpecOn` directly to the
     trusted target language `L_t`, eliminating `L_ir` (and any number of
     intermediate IRs `L_1, L_2, ...` and passes `pass_1, pass_2, ...`) from the
     TCB via cut elimination (`proof_gated_compilation_eliminates_ir_from_tcb`
     and `multi_stage_proof_gated_compilation_eliminates_irs_from_tcb`, `0`
     axioms).
4. **Principle-of-Explosion Vulnerability in Antecedent-Based Trust Policies &
   Clause-Guarded `ScopedVerificationResult`:**
   Because `Mir.crate : Trusted.Crate` is a transparent `def` and `MirMachine` /
   `X86Machine` are computable evaluators, any unproved proof obligation
   (`L_ir.WellFormedOn D p_wip` or `Compiles ... p_wip`) that is factually false
   for a work-in-progress function evaluates to `False` in Lean's kernel. Placing
   an omitted obligation into the global antecedent `hTcb : policy.AllHold` (or
   into an intra-function implication antecedent) triggers the Principle of
   Explosion (`False.elim`), allowing a user to "verify" an entire crate —
   including completely unrelated buggy functions (`"fn_critical"`) or
   intra-function obligations — with `0` axioms
   (`global_antecedent_omission_explodes_crate` and
   `intra_function_antecedent_omission_explodes_other_obligations` in
   `support/ProofGatedCompilationAndTrustPolicy.lean`). We replace
   antecedent-based omission with **clause-guarded conjunction**
   (`ScopedVerificationResult` and `UnifiedCrateTheorem`), guarding each
   positive obligation `(fn, kind) ∉ omitted → Obligation(fn, kind)` while
   keeping `hTcb : ∀ a, a ∈ allowedTcb → TrustedAssumption.holds a` restricted
   strictly to `opaque` boundary assumptions. Eight mechanized theorems (`0`
   axioms) prove zero-trust equivalence (`scoped_zeroTrust_iff_allHold`),
   monotonicity (`scoped_verification_antitone_in_omitted`), and complete
   inter-function and intra-function explosion isolation
   (`scoped_omission_isolates_buggy_fn`,
   `scoped_omission_isolates_intra_fn_obligations`, and
   `unified_crate_theorem_non_vacuous_and_isolated`).
5. **Structural External Calls in `StepResult` & Reentrancy Soundness:**
   In `support/StructuralExternalCallAndCanaries.lean`, we extend
   `StepResult State Obs Failure` with a fifth constructor
   `.externalCall (boundaryInv : Bool) (next : State → Obs → Prop)` and extend
   `ReachesPrefix` with three constructors (`externalCallFail`,
   `externalCallOk`, and `emptyExternalCall`). This design achieves three
   properties simultaneously (all proved with `0` axioms, zero `sorryAx`, and
   zero `Lean.ofReduceBool`):
   - **Call-site invariant enforcement (`reachesPrefix_of_externalCall`):** A
     single fuel step (`steps = 1`) from an `.externalCall boundaryInv next`
     state produces `.failed .externalBoundaryViolation` whenever
     `boundaryInv = false`, forcing `WellFormedOn` to prove `boundaryInv = true`
     at every reachable external call site before any post-call transition is
     explored.
   - **Demonic post-call branching (`externalCallOk`):** Every post-call state
     and observation `(s', o)` satisfying `next s' o` is explored across the
     remaining fuel budget `steps`, propagating `WellFormedOn` and `SpecOn`
     across arbitrary environment modifications and callbacks.
   - **Constructive (`Classical.choice`-free) non-vacuity at every fuel depth
     (`exists_reaches_prefix` and `non_vacuity_at_every_depth`):** Under
     `TotalStep` and `InhabitedDemonic` (which supplies a constructive default
     post-call witness when `next` is empty), every initial state reaches at
     least one prefix outcome at every fuel depth `n : Nat` without invoking
     `Classical.choice`. When `next` is uninhabited (`∀ s' o, ¬ next s' o`),
     `emptyExternalCall` produces `.defined .outOfFuel` rather than vacuously
     discharging `ReachesPrefix`.
   - **Canary validation (`ExtMirMachine` vs. `UncheckedMirMachine`):** Under
     `ExtMirMachine`, a function `reentrantBuggyFn` that temporarily sets a
     `NonZeroU32` field to `0`, invokes an opaque external callback, and then
     restores the field to `1` is **rejected** (`canary_reentrant_callback_rejected`),
     whereas `UncheckedMirMachine` (which checks `AdmissibleAdtInv` only at
     function return) **unsoundly accepts** `reentrantBuggyFn`
     (`canary_unchecked_callback_unsoundly_accepts_reentrantBuggyFn`), and
     `safeCallbackFn` (which restores `NonZeroAdtInv` before the external call)
     is **verified** (`canary_safe_callback_verified`).
6. **Open-World Callback Framing (`OpenWorldCallbackFraming`):**
   We construct a concrete 7-step soundness counterexample in
   `OpenWorldCallbackFraming` (`support/StructuralExternalCallAndCanaries.lean`,
   lines 3435–5814) showing that entry/exit-only library invariants
   (`EnsuresOpenRetLibInv`) are **unsound under reentrant callbacks**:
   - `getUncheckedOpenBody` (which asserts the library invariant `slot 0 < slot 1`)
     verifies in isolation (`naive_getUnchecked_verified`);
   - `withTempInvalidOpenBody` (which temporarily sets `slot 0 := slot 1`,
     violating `slot 0 < slot 1`, invokes an external callback, and restores
     `slot 0 < slot 1` before returning) also verifies in isolation under
     entry/exit-only `EnsuresOpenRetLibInv` (`naive_withTempInvalid_verified`);
   - Yet when `withTempInvalidOpenBody` is linked against a callback that
     re-enters `getUncheckedOpenBody`, concrete execution reaches
     `.failed .assertionFailure` in 7 steps
     (`naive_reentrancy_exploit_triggers_ub`).
   We resolve this via `GuardedOpenMachine` and `StructuralOpenMachine` with an
   explicit exposure partition (`exposedSlots : List Nat`) and unexposed frame
   preservation (`UnexposedFramePreserved`), proving
   `withTempInvalid_rejected_under_guarded_call`,
   `withRestoredBeforeCall_verified`, `withUnexposedPrivateTemp_verified`, and
   the compositional linking theorem `open_world_callback_composition_sound` by
   induction on `steps : Nat`.
7. **TCB Semantic Mutation Testing (`MirSemantics` & `X86Semantics`):**
   Using `support/run_trusted_mutation_audit.py`, we inject **48 targeted
   semantic mutations** (`MIR-Mut-01`–`MIR-Mut-24` in `Trusted/MirSemantics.lean`
   and `X01`–`X24` in `Trusted/X86Semantics.lean`) and measure how many are
   caught by the existing positive verification suites vs. our augmented
   negative canary suites:
   - **Baseline positive proof suites:** Kill only **`5 / 24` (`20.83%`)** of
     `MirSemantics` mutations and **`5 / 24` (`20.83%`)** of `X86Semantics`
     mutations (`19 / 24` = `79.17%` of TCB semantic bugs survive positive
     verification on both branches!).
   - **Augmented negative canary suites (`TrustedMutationCanaries`):** Adding
     25 negative canary theorems (`canary_M01_sizeOf_usize_wrong_rejected`
     through `canary_M24b_wrong_id_violates_ensures`) and 24 x86 negative canary
     theorems raises the mutation kill rate to **`24 / 24` (`100.0%`)** on both
     `MirSemantics` and `X86Semantics` (`support/mutation_audit_results.json`).
8. **Proof-Gated `BoundaryCanarySuite` & 13-Guard Mutation Probe:**
   In `support/ProofGatedAndCanarySuite.lean` and
   `support/StructuralExternalCallAndCanaries.lean` (`BoundaryCanary` namespace),
   we define a 21-field proof-gated typeclass `BoundaryCanarySuite M` combining
   11 positive execution witnesses (`pos_*`) and 10 negative refutations
   (`neg_*`) across 10 semantic boundary families (64-bit modular ALU wrap,
   shift-amount validation, division/remainder by zero and `INT64_MIN / -1`
   overflow, memory alignment, stack slot bounds, frame-escape on return, heap
   use-after-free, `cmov` source evaluation, call depth exhaustion, and CTFE
   rejection). We prove that the unfixed `X86Semantics.lean` model
   (`currentX86Model`) **fails** `BoundaryCanarySuite`
   (`currentX86Model_fails_BoundaryCanarySuite`), construct a repaired model
   `fixedX86Model` that satisfies all 21 fields
   (`instBoundaryCanarySuiteFixedX86Model`), and run
   `support/run_guard_mutation_probe.py` across all 13 `-- MUTATE_GUARD:` sites
   in `fixedX86Model`, killing **`13 / 13` (`100.0%`)** of guard mutations
   (`support/guard_mutation_results.json`).
9. **12-Case `TrustedBoundary.lean` Elaboration & Binder Spoofing Probe Suite:**
   Using `support/run_audit_probes.py`, we execute 12 adversarial `.olean` +
   source probes (Probes `A1`–`A3`, `B1`–`B3`, `C1`–`C3`, `D1`, plus positive
   controls `CTRL_POS` and `CTRL_NEG`) against both Phase 1 (`preflight`) and
   Phase 2 (`audit`) of `trusted/audit/TrustedBoundary.lean` across the initial
   `origin/main` auditor (`24367bd1a8c784f2578535954f9915e24894a56f`), the
   x86-64 prototype auditor, and the hardened single-import two-stage auditor on
   `origin/main` (`beb778bb135474a67dc017c185d2753a60693d8c` /
   `f2bc17e9be87b777d63c785b31f3370ff058d69b`). We demonstrate that:
   - In the initial `origin/main` auditor (`24367bd1a8c784f2578535954f9915e24894a56f`),
     **6 adversarial probes** (`A1` `local notation`, `A2` `scoped syntax` +
     `macro_rules`, `B2` `namespace Trusted` shadowing, `B3` `_root_.Trusted`
     injection, `C1` universe-polymorphic `verify_crate.{u}`, and `C2`
     `noncomputable def crate` via `Classical.choice`) **pass Phase 1
     (`preflight`)**, and **2 of those (`C1` and `C2`) pass both Phase 1 and
     Phase 2 (`audit`)**!
   - In the hardened `origin/main` auditor
     (`beb778bb135474a67dc017c185d2753a60693d8c` /
     `f2bc17e9be87b777d63c785b31f3370ff058d69b`), all 6 spoofing vectors (`A1`,
     `A2`, `B2`, `B3`, `C1`, `C2`) are **blocked** by removing `notation`,
     `macro_rules`, and `syntax` from `commandKinds`, rejecting `_root_` in
     `validateUserDeclIdent`, forbidding non-`Trusted` modules from declaring
     constants in `Trusted.*`, checking `mirCrateCi.levelParams.isEmpty` and
     `proofCi.levelParams.isEmpty`, and running a zero-axiom `closure` check
     (`#[]`) on `Mir.crate`.

## Applicability

These findings and mechanized artifacts apply to:

- **`joshlf/anneal` (`origin/main` commits `24367bd1a8c784f2578535954f9915e24894a56f`, `beb778bb135474a67dc017c185d2753a60693d8c`, and `f2bc17e9be87b777d63c785b31f3370ff058d69b`):**
  - `trusted/lean/Trusted/Refinement.lean` (`Partial`, `Behavior`, `Language`,
    `Compiler`, `Compiles`, `SoundOn`, `TrustedAssumption`, `TrustPolicy`,
    `VerificationResultOn`)
  - `trusted/lean/Trusted/StepResult.lean` (`StepResult`, `SmallStepMachine`,
    `ExecQuery`, `ExecOut`, `ReachesPrefix`, `BehaviorOf`)
  - `trusted/lean/Trusted/MirSemantics.lean` (`MirMachine`, `MirSem`, `MirLang`,
    `RustcCompiler`, `TCBItem`, `CapturedFn`, `Crate`, `CrateTheorem`)
  - `trusted/audit/TrustedBoundary.lean` and `trusted/audit/src/lib.rs` (Phase 1
    `preflight` syntax inspection and Phase 2 `audit` `.olean` kernel
    `ConstantInfo` / `Expr` and transitive axiom closure verification)
  - `trusted/lean/Trusted/Attributes.lean` (`#[trusted]` macro expansion) and
    `trusted/lean/foundation-lock.json`
- **`leanprover/lean4` (`5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):**
  - `src/kernel/declaration.h`, `src/kernel/environment.cpp`, and
    `src/Lean/Parser/Command.lean`

### Self-Contained Prototype Definitions Inlined for Cold Readers

Several sections analyze definitions from the MIR and x86-64 verification
prototypes alongside `origin/main`. To ensure this report is 100% self-contained
without checking out any experimental branch, the exact Lean 4 definitions of
these prototype structures and predicates are inlined below:

```lean
-- From Trusted/Refinement.lean & Trusted/StepResult.lean:
inductive Partial (α : Type u) : Type u where
  | defined (val : α)
  | undefined

structure Behavior (Query : Type u) (Out : Type v) where
  run : Query → Partial (Out → Prop)

structure Language (Prog : Type u) (Query : Type v) (Out : Type w) where
  sem : Prog → Behavior Query Out
  WellFormedOn (D : Query → Prop) (p : Prog) : Prop :=
    ∀ q, D q → ∃ P, (sem p).run q = .defined P
  SpecOn (D : Query → Prop) (p : Prog) (S : Query → Out → Prop) : Prop :=
    ∀ q, D q → ∀ P, (sem p).run q = .defined P → ∀ o, P o → S q o

structure BehaviorMorphism (Q_s : Type u₁) (O_s : Type v₁) (Q_t : Type u₂) (O_t : Type v₂) where
  map : Behavior Q_t O_t → Behavior Q_s O_s
  monotone : ∀ b₁ b₂, b₁ ≤ b₂ → map b₁ ≤ map b₂

structure Compiler (Prog_s Q_s O_s Prog_t Q_t O_t : Type*)
    (L_s : Language Prog_s Q_s O_s) (L_t : Language Prog_t Q_t O_t) where
  compile : Prog_s → Prog_t
  π : BehaviorMorphism Q_s O_s Q_t O_t
  SoundOn (D : Q_s → Prop) : Prop :=
    ∀ p q, D q → (π.map (L_t.sem (compile p))).run q ≤ (L_s.sem p).run q

def Compiles (L_s : Language Prog_s Q_s O_s) (L_t : Language Prog_t Q_t O_t)
    (π : BehaviorMorphism Q_s O_s Q_t O_t) (compile : Prog_s → Prog_t) (p : Prog_s) : Prop :=
  π.map (L_t.sem (compile p)) ≤ L_s.sem p

class TrustedAssumption (α : Type u) where
  holds : α → Prop

structure TrustPolicy (α : Type u) [TrustedAssumption α] where
  allowed : α → Prop
  AllHold : Prop := ∀ a, allowed a → TrustedAssumption.holds a

structure VerificationResultOn [TrustedAssumption α] (policy : TrustPolicy α)
    (L_s : Language Prog_s Q_s O_s) (L_t : Language Prog_t Q_t O_t)
    (C : Compiler Prog_s Q_s O_s Prog_t Q_t O_t L_s L_t)
    (D : Q_s → Prop) (p : Prog_s) (S : Q_s → O_s → Prop) : Prop where
  source_wf : policy.AllHold → L_s.WellFormedOn D p
  source_spec : policy.AllHold → L_s.SpecOn D p S
  compiler_sound : policy.AllHold → C.SoundOn D

-- From Trusted/MirSemantics.lean & Trusted/X86Semantics.lean:
-- (1) ADT & library invariant wrappers:
structure AdmissibleAdtInv (Inv : Value → Prop) : Prop where
  wellTyped : ∀ v, Inv v → WellTypedValue v

def EnsuresRetLibInv (LibInv : Memory → Prop) (Post : Value → Memory → Prop)
    (retVal : Value) (mem : Memory) : Prop :=
  LibInv mem ∧ Post retVal mem

-- (2) Prototype X86Semantics state, unguarded writeSlot, and unbounded-Nat ALU:
structure X86State where
  regs   : RegFile
  flags  : Flags
  slots  : List Value
  mem    : FlatMem
  block  : BlockId
  instrIdx : Nat
  callStack : List CallFrame

-- In the unfixed x86-64 prototype (Trusted/X86Semantics.lean lines 105-115 & 212-222),
-- writeSlot returned `s` unchanged on out-of-bounds slot indices instead of `none`,
-- and evalX86BinOp evaluated `.add`, `.sub`, `.imul`, `.shl`, `.shr` over unbounded `Nat`
-- without `mod64` wrapping or `b < 64` shift-amount checks.
```

---

## Findings

### Finding 1: Contradictory `opaque` TCB Witnesses & Universal Realizability (`TCBModel`)

#### 1.1 How `VerificationResultOn` and `opaque` Constants Interact

In `Trusted/Refinement.lean` (`lines 385–471`) and `Trusted/MirSemantics.lean`
(`lines 685–755`), every crate theorem has the form:

```lean
def VerificationResultOn (policy : TrustPolicy α)
    (L_s : Language Prog_s Q_s O_s) (L_t : Language Prog_t Q_t O_t)
    (C : Compiler L_s L_t) (D : Q_s → Prop) (p : Prog_s)
    (spec : Q_s → O_s → Prop) : Prop := ...
```

where the conclusion `L_s.WellFormedOn D p ∧ L_s.SpecOn D p spec` and target
preservation `(C.π.map (L_t.sem (C.compile p))).SpecOn D spec` are guarded by
the implication antecedent `hTcb : policy.AllHold`. For `defaultTrustPolicy`,
`policy.AllHold` asserts `TrustedAssumption.holds .compilerLowering` and
`TrustedAssumption.holds .semanticsCapture`. In turn:

```lean
TrustedAssumption.holds .compilerLowering
  = RustcCompiler.SoundOn (fun _ => True)
  = ∀ p : MirBody, ∀ q : MirQuery, True →
      (π_c.map (TargetSem (rustc p))).run q ≤ (MirSem p).run q
```

where `TargetArtifact`, `rustc`, `TargetSem`, and `π_c` are declared as concrete
`opaque` definitions in `Trusted/MirSemantics.lean:685-723` (and similarly
`assemble`, `TargetSem`, and `π_asm` in `Trusted/X86Semantics.lean:714-760`).

In Lean 4's kernel (`src/kernel/declaration.h`, `src/kernel/environment.cpp`),
an `opaque` declaration `opaque c : τ := v` elaborates the hidden witness `v : τ`
to verify that `τ` is inhabited, and then seals `c` so that `c` is
definitionally opaque to all downstream modules (`Mir.lean` and `Proof.lean`).

#### 1.2 Why Unconstrained Universal Quantification (`fun _ => True`) Over `MirBody × MirQuery` Is Fragile

Because `RustcCompiler.SoundOn (fun _ => True)` quantifies over **every**
`(p : MirBody)` and `(q : MirQuery)` — not merely well-formed bodies admitted
by `MonoAdmitted` or queries with sufficient fuel — there exist degenerate
`(p, q)` pairs where `(MirSem p).run q` is **guaranteed** to be `.defined P`:

1. **Bodies failing `MonoAdmitted` (`pme_rejected_query_mirSem_defined`,
   `support/TcbConsistencyAndAuditProbes.lean:272-277`):**
   In `Trusted/MirSemantics.lean:611-612`, `initMirState body args` checks
   `if !MonoAdmitted body then .failed .illFormedProgram`. In
   `Trusted/StepResult.lean:119-121`, `ReachesPrefix` maps any `.failed err`
   initial state directly to `.failed err` at fuel `0`. However, at fuel `0` on
   any state, `ReachesPrefix` **also** has constructor `zero : ReachesPrefix M 0
   s (.completed .outOfFuel)`. Wait: for `steps ≥ 1`, constructor `fail` applies
   when `M.step s = .failed err`, so `ReachesPrefix` is false (`¬ ReachesPrefix M
   (steps + 1) s (.failed err)` is refuted), making `(MirSem p).run q =
   .undefined`. **Wait — at `steps = 0`**, `ReachesPrefix.zero` holds
   unconditionally for **every** `s` (even when `initMirState` returns `.failed
   .illFormedProgram`!), so for any `p` and any query `q` with `q.steps = 0`,
   `(MirSem p).run q = .defined (fun out => out = .outOfFuel)`!
2. **Fuel-0 queries on any body (`step0_query_mirSem_defined`,
   `support/TcbConsistencyAndAuditProbes.lean:281-287`):**
   For every `p : MirBody` and every `q` with `q.steps = 0`, `(MirSem p).run q`
   is `.defined (fun out => out = .outOfFuel)`.

By the definition of the refinement preorder on `Partial (Out → Prop)`
(`Trusted/Refinement.lean:264-273`):

```lean
instance : LE (Partial (Out → Prop)) where
  le p₁ p₂ := ∀ P₂, p₂ = .defined P₂ → ∃ P₁, p₁ = .defined P₁ ∧ ∀ o, P₁ o → P₂ o
```

whenever `(MirSem p).run q = .defined P₂`, the inequality `(π_c.map (TargetSem
(rustc p))).run q ≤ (MirSem p).run q` forces `(π_c.map (TargetSem (rustc
p))).run q` to be `.defined P₁` as well. If the hidden `opaque` witness for
`TargetSem` returns `.undefined` on `(rustc p)` (for instance, because `p` is
not a valid Rust program and `rustc` rejects it, or because `TargetSem` is
 instantiated with the trivial witness `fun _ _ => .undefined`), then
`RustcCompiler.SoundOn (fun _ => True)` is **provably `False`**:

- `pme_rejected_target_undefined_soundOn_false`
  (`support/TcbConsistencyAndAuditProbes.lean:307-322`, axioms: `[propext]`):
  If `TargetSem` returns `.undefined` on any body `p` rejected by
  `MonoAdmitted` at `steps = 0`, `RustcCompiler.SoundOn (fun _ => True)` implies
  `False`.
- `hidden_opaque_witness_soundOn_false`
  (`support/TcbConsistencyAndAuditProbes.lean:342-350`, `0` axioms) and
  `x86_hidden_opaque_witness_soundOn_false` (`lines 571-582`, `0` axioms):
  Using the actual hidden witness `TargetSem := fun _ => ⟨fun _ => .undefined⟩`
  present in `Trusted/MirSemantics.lean:698` and
  `Trusted/X86Semantics.lean:723`, `RustcCompiler.SoundOn (fun _ => True)` and
  `AssemblerCompiler.SoundOn (fun _ => True)` are definitionally inconsistent
  with unfolding their own witnesses!
- `contradictory_hTcb_proves_ub_crate`
  (`support/TcbConsistencyAndAuditProbes.lean:397-402`, axioms: `[propext]`):
  Whenever `policy.AllHold` is contradictory (`¬ policy.AllHold`),
  `VerificationResultOn policy MirLang TargetLang RustcCompiler D alwaysUbBody
  (fun _ _ => False)` is provable for an unconditionally UB program
  `alwaysUbBody`.

#### 1.3 Relative Consistency via Universal `TCBModel` Realizability

To guarantee that the TCB hypothesis can never be contradictory — even if
someone later adds helper lemmas in `Trusted` about the signature of `rustc` or
`TargetSem` — `VerificationResult` should quantify universally over all models
`M : TCBModel` that realize the TCB contract (`M.RealizesTCB`), rather than
predicating `AllHold` on fixed `opaque` constants:

```lean
structure TCBModel where
  TargetArtifact : Type
  rustc : MirBody → TargetArtifact
  TargetSem : TargetArtifact → Behavior MirQuery ( ExecOut Value )
  π_c : BehaviorMorphism MirQuery (ExecOut Value) MirQuery (ExecOut Value)

def TCBModel.RealizesTCB (M : TCBModel) : Prop :=
  ∀ p q, (M.π_c.map (M.TargetSem (M.rustc p))).run q ≤ (MirSem p).run q
```

In `support/TcbConsistencyAndAuditProbes.lean` (`lines 435–520`), we prove four
meta-theorems (`0` axioms each):

1. **Constructive Inhabitation (`refTCBModel_realizes_tcb`, `lines 463-471`):**
   Setting `TargetArtifact := MirBody`, `rustc := id`, `TargetSem := MirSem`,
   and `π_c := BehaviorMorphism.id` yields a concrete model `refTCBModel :
   TCBModel` satisfying `refTCBModel.RealizesTCB` by reflexivity.
2. **Non-Contradiction of Universal TCB Hypotheses
   (`universal_hTcb_never_contradictory`, `lines 488-490`):**
   Because `refTCBModel` inhabits `{ M : TCBModel // M.RealizesTCB }`, the
   hypothesis `∀ M : TCBModel, M.RealizesTCB → ...` can never vacuously derive
   a false source property.
3. **Relative Consistency Meta-Theorem (`relative_consistency_meta_theorem`,
   `lines 482-486`):**
   Any `UniversalVerificationResult D p S` immediately implies concrete source
   well-formedness and specification conformance `MirLang.WellFormedOn D p ∧
   MirLang.SpecOn D p S` with **zero leftover TCB hypotheses** by instantiating
   `M := refTCBModel`.
4. **Refutation of `alwaysUbCrate` (`alwaysUbCrate_unprovable_under_universal_tcb`,
   `lines 496-516`):**
   `¬ UniversalVerificationResult (fun q => q.steps = 1) alwaysUbBody S` holds
   unconditionally (`0` axioms).

---

### Finding 2: Unverified Rust-to-x86 Capture Gap in the x86-64 Prototype

In the x86-64 verification prototype:

1. `trusted/rustc-capture/src/lib.rs` extracts Rust MIR from `rustc` and
   directly translates it in **unverified Rust code** into:
   - a Lean `X86Body` AST in `Mir.lean` (`render_x86_body`, `lines 1435-1561`),
     and
   - raw AT&T/Intel assembly in `.anneal/Prog.s` (`render_x86_assembly`,
     `lines 1589-1820`).
2. `Trusted/X86Semantics.lean` (`lines 872-895`) defines `CapturedFn` and
   `CrateTheorem` purely over `X86Body` (`X86Lang` → `TargetLang` via
   `AssemblerCompiler`):
   ```lean
   structure CapturedFn where
     name : String
     body : X86Body
     domain : MirQuery → Prop
     spec : MirQuery → ExecOut Value → Prop
   ```
3. Meanwhile, the verified Lean compiler in `theory/Anneal/Compiler/NaiveCodegen.lean`
   (`compileStage0 : MirBody → X86Body` and `naiveCodegen_compiles : Compiles
   MirLang X86Lang MirToX86Morphism.toMorphism compileStage0 body`) and
   `theory/Anneal/Compiler/Peephole.lean` (`compileOptimized : MirBody → X86Body`
   and `peepholeOptimize_compiles`) are **never referenced** by `Mir.crate :
   Trusted.Crate` or `Proof.verify_crate : Trusted.CrateTheorem Mir.crate`!

In `support/TcbConsistencyAndAuditProbes.lean` (`lines 588–645`), we formalize
this architectural gap and prove two theorems (`0` axioms):

- `mir_to_x86_unverified_capture_gap` (`lines 603-614`):
  There exist a source `MirBody` (`mirSafeFn`), an unverified capture function
  `buggyRustcCaptureAsm : MirBody → X86Body` that emits UB assembly
  (`x86BuggyCapture`), and a `CapturedX86OnlyCrate` whose `CrateTheorem` holds
  under `refX86TCBModel`, yet executing `buggyRustcCaptureAsm mirSafeFn` at
  `steps = 1` triggers `.undefined` (UB).
- `verified_pipeline_rejects_capture_mismatch` (`lines 637-641`):
  When `CapturedPipelineCrate` binds the source `mirBody : MirBody`, the target
  `x86Body : X86Body`, and the compilation obligation `Compiles MirLang X86Lang
  π_mir_x86 (fun _ => x86Body) mirBody` inside `CrateTheorem`, any mismatch
  where `mirBody` is well-formed on `q` (`steps = 1`) and `x86Body` triggers UB
  on `q` is **provably rejected** (`¬ VerifiedPipelineCrateTheorem c`).

---

### Finding 3: Proof-Gated Compilation Eliminates Intermediate IRs and Passes from the TCB

A central architectural question for multi-stage verified compilation (`MirLang`
$\rightarrow$ `AnSSALang` $\rightarrow$ `X86Lang`) is whether an intermediate IR
semantics (`L_ir`) or compiler pass (`pass`) must be part of the TCB.

In `support/ProofGatedCompilationAndTrustPolicy.lean` (`lines 180–440`) and
`support/ProofGatedAndCanarySuite.lean` (`lines 80–220`), we define
`BoundaryCodec` (and `BehaviorCodec`) — which lifts a query map `mapQuery : Q_s
→ Q_t` and relation `relOut : Q_s → O_t → O_s → Prop` into a monotone
`BehaviorMorphism` (`BoundaryCodec.monotone_toMorphism`, `0` axioms) — and prove
that **proof-gated compilation completely eliminates intermediate IRs and
compiler passes from the TCB**:

| Threat to Untrusted Intermediate `L_ir` | Which Proof Gate Blocks It? | Mechanized Theorem (`0` axioms) |
| :--- | :--- | :--- |
| `L_ir` adds spurious UB on query `q ∈ D` (`(L_ir.sem p).run q = .undefined`) | Blocked by source well-formedness gate `L_ir.WellFormedOn D p` | `spurious_ir_ub_blocks_source_obligation` (`ProofGatedCompilationAndTrustPolicy.lean:303-317`), `spurious_ub_breaks_wellFormedOn` (`ProofGatedAndCanarySuite.lean:139-147`) |
| `L_ir` omits real target UB (`(L_ir.sem p).run q = .defined P_ir` while `(L_t.sem (pass p)).run (codec.mapQuery q) = .undefined`) | Blocked by pass compilation gate `Compiles L_ir L_t codec.toMorphism pass p` | `omitted_ir_ub_blocks_pass_obligation` (`ProofGatedCompilationAndTrustPolicy.lean:327-341`), `missing_ub_breaks_compiles` (`ProofGatedAndCanarySuite.lean:155-163`) |
| `L_ir` omits a reachable target outcome `o_t` (`P_t o_t` holds in `L_t`, but no corresponding `o_s` satisfies `P_ir o_s`) | Blocked by pass compilation gate `Compiles L_ir L_t codec.toMorphism pass p` | `omitted_ir_outcome_blocks_pass_obligation` (`ProofGatedCompilationAndTrustPolicy.lean:349-367`), `missing_outcome_breaks_compiles` (`ProofGatedAndCanarySuite.lean:170-180`) |
| End-to-end target safety & spec conformance independent of `L_ir` | Cut elimination combining `L_ir.WellFormedOn D p`, `L_ir.SpecOn D p S`, and `Compiles L_ir L_t codec.toMorphism pass p` | `proof_gated_compilation_eliminates_ir_from_tcb` (`ProofGatedCompilationAndTrustPolicy.lean:375-397`), `multi_stage_proof_gated_compilation_eliminates_irs_from_tcb` (`lines 410-433`) |

Crucially, `proof_gated_compilation_eliminates_ir_from_tcb` and
`multi_stage_proof_gated_compilation_eliminates_irs_from_tcb` show that if a user
modifies `MirLang` or `AnSSALang` (or their lowering passes `pass₁`, `pass₂`),
the final target theorem:

```lean
L_t.WellFormedOn (codec.TargetDomain D) (pass₂ (pass₁ p)) ∧
L_t.SpecOn (codec.TargetDomain D) (pass₂ (pass₁ p)) (codec.TargetSpec D S)
```

depends **only** on the boundary codecs (`codec₁`, `codec₂`) and the trusted
target semantics `L_t` (`X86Lang`). Neither `MirLang`, `AnSSALang`, `pass₁`, nor
`pass₂` appears in the conclusion or needs to be trusted.

---

### Finding 4: Principle-of-Explosion Vulnerability in Antecedent-Based Trust Policies & Clause-Guarded `ScopedVerificationResult`

#### 4.1 Why Putting Omitted Computable Proof Obligations in `policy.AllHold` Is Unsound

Suppose a crate has two functions: `"fn_wip"` (whose proof or implementation is
unfinished) and `"fn_critical"` (which the engineer wants to verify). A natural
temptation when extending `TCBItem` to multi-stage compilation is to add trust
items such as `.assumeSourceWellFormed "fn_wip"` or `.assumePassCompiles
"fn_wip"` to `policy.allowed`, so that `hTcb : policy.AllHold` supplies the
missing proof obligation for `"fn_wip"` in the antecedent of `CrateTheorem`.

In `support/ProofGatedCompilationAndTrustPolicy.lean` (`lines 490–645`), we
prove that **placing any computable semantic or pass obligation into an
implication antecedent (`hTcb : policy.AllHold → ...`) is catastrophically
unsound** whenever the omitted obligation happens to be false in the concrete
evaluator (`MirMachine` or `X86Machine`):

1. Because `Mir.crate : Trusted.Crate` is a transparent `def` and `MirMachine` /
   `X86Machine` are computable evaluators, if `"fn_wip"` has an unfixed bug (or
   an incomplete pass handles `"fn_wip"` incorrectly) on even a single query `q₀`
   (e.g., `steps = 1`), the proposition `TrustedAssumption.holds
   (.assumeSourceWellFormed "fn_wip")` reduces in Lean's kernel to `False`
   (`transparent_buggy_wip_assumption_is_false`, `lines 567-572`, `0` axioms).
2. **Global Crate Explosion (`global_antecedent_omission_explodes_crate`,
   `lines 602-613`, `0` axioms):**
   When `hTcb : policy.AllHold` appears as the antecedent of `CrateTheorem`, a
   proof script can instantiate `hTcb (.assumeSourceWellFormed "fn_wip")`,
   reduce it to `False` via `decide` / kernel reduction on `q₀`, and apply
   `False.elim` to discharge the **entire `CrateTheorem`** — including a
   completely broken `"fn_critical"` (`buggyCriticalFn`) whose body immediately
   triggers UB!
3. **Intra-Function Obligation Explosion
   (`intra_function_antecedent_omission_explodes_other_obligations`,
   `lines 624-643`, `0` axioms):**
   Even if `hTcb` is scoped per function (`fn_antecedent → fn_conclusions`),
   assuming a false pass obligation (`Compiles MirLang X86Lang ... p`) in the
   antecedent of `p`'s verification theorem explodes `p`'s remaining obligations
   (`MirLang.WellFormedOn D p` and `MirLang.SpecOn D p S`), allowing a function
   with source-level UB to pass source verification merely because its backend
   codegen pass is unverified!

#### 4.2 The Sound Replacement: Clause-Guarded Conjunction (`ScopedVerificationResult` & `UnifiedCrateTheorem`)

To support fine-grained opt-out (`strictPolicy` vs. work-in-progress partial
verification) **without** ever placing a computable proposition in an
implication antecedent, `ScopedVerificationResult` and `UnifiedCrateTheorem`
(`support/ProofGatedCompilationAndTrustPolicy.lean:660-1234`) separate:

1. **Opaque boundary assumptions (`allowedTcb : Finset OpaqueBoundaryItem`):**
   Only genuinely `opaque` target boundary assumptions (`.assemblerLowering`,
   `.isaHardwareSemantics`) may appear in the global antecedent `hTcb : ∀ a, a ∈
   allowedTcb → OpaqueAssumption.holds a` (or via universal `TCBModel`
   quantification).
2. **Clause-guarded positive obligations (`omitted : Finset (FnId ×
   ObligationKind)`):**
   Every computable obligation `(fn, kind)` (`sourceWf`, `sourceSpec`,
   `stage0Compiles`, `peepholeCompiles`) appears as a **positive conjunct**
   guarded by non-membership `(fn, kind) ∉ omitted`:
   ```lean
   structure ScopedFnVerification (omitted : OmissionSet) (fn : CapturedPipelineFn) : Prop where
     source_wf : (fn.name, .sourceWf) ∉ omitted → MirLang.WellFormedOn fn.domain fn.mirBody
     source_spec : (fn.name, .sourceSpec) ∉ omitted → MirLang.SpecOn fn.domain fn.mirBody fn.spec
     stage0_compiles : (fn.name, .stage0Compiles) ∉ omitted →
       Compiles MirLang AnSSALang π_stage0 compileStage0 fn.mirBody
     peephole_compiles : (fn.name, .peepholeCompiles) ∉ omitted →
       Compiles AnSSALang X86Lang π_peephole optimizePeephole (compileStage0 fn.mirBody)
   ```

Because `(fn.name, kind) ∉ omitted` is a pure finite-set membership check on the
obligation label (not on the semantic truth of the obligation!), omitting a
false obligation `( "fn_wip", .sourceWf ) ∈ omitted` makes the implication
antecedent `( "fn_wip", .sourceWf ) ∉ omitted` evaluate to `False` (making that
single clause trivially `False → ...`, i.e., `True`) while leaving the
antecedent `( "fn_critical", .sourceWf ) ∉ omitted` equal to `True`!

We prove 10 mechanized theorems (`0` axioms each) in
`support/ProofGatedCompilationAndTrustPolicy.lean` (`lines 776–1211`):

- `scoped_zeroTrust_forces_empty_omitted` (`lines 776-787`) and
  `scoped_zeroTrust_iff_allHold` (`lines 799-811`): When `omitted = ∅`,
  `ScopedFnVerification ∅ fn` is logically equivalent to requiring all four
  source and pass obligations unconditionally.
- `scoped_verification_antitone_in_omitted` (`lines 817-843`) and
  `unomitted_entry_holds_of_scoped_verification` (`lines 851-870`): Shrinking
  `omitted` strengthens the theorem, and any `(fn, kind) ∉ omitted` can be
  projected directly.
- `scoped_omission_isolates_buggy_fn` (`lines 922-947`): Even when `"fn_wip"`
  has `mirBody = buggyWipFn` (which fails `WellFormedOn`), omitting `"fn_wip"`
  Still **rejects** any crate where `"fn_critical"` is buggy
  (`¬ ScopedCrateVerification omittedBuggyWip crateWithBuggyCritical`).
- `scoped_omission_isolates_intra_fn_obligations` (`lines 963-994`): Omitting
  `(fn.name, .peepholeCompiles)` for a function whose peephole pass is broken
  still forces `fn.mirBody` to satisfy `MirLang.WellFormedOn` and
  `MirLang.SpecOn`.
- `pipeline_two_pass_scoped_soundness` (`lines 1044-1082`),
  `partially_verified_crate_holds` (`lines 1132-1151`),
  `extract_verified_fn_from_partially_verified_crate` (`lines 1159-1175`), and
  `unified_crate_theorem_non_vacuous_and_isolated` (`lines 1201-1211`): For every
  function `fn` in a partially verified crate whose four obligations are not in
  `omitted`, full end-to-end target safety (`X86Lang.WellFormedOn` and
  `X86Lang.SpecOn`) holds unconditionally.

---

### Finding 5: Structural External Calls in `StepResult` & Reentrancy Soundness

#### 5.1 Extending `StepResult` and `ReachesPrefix`

In `Trusted/StepResult.lean`, `StepResult State Obs Failure` has four
constructors: `.continue (next : State)`, `.terminated (obs : Obs)`, `.failed
(err : Failure)`, and `.demonic (next : State → Prop)`. While `.demonic` can
branch over internal non-determinism (such as allocator choices), modeling an
**external function call** (`Call` to an unverified or callback-bearing target)
requires:
1. Checking a **call-site boundary invariant** (`boundaryInv : Bool`, e.g., that
   all exposed ADT and library invariants hold before relinquishing control to
   unknown code); and
2. Branching demonically over **both** the post-call state `s' : State` **and**
   any direct terminal observation `o : Obs` (or post-call continuation)
   permitted by the external call specification `next : State → Obs → Prop`.

In `support/StructuralExternalCallAndCanaries.lean` (`lines 148–485`), we extend
`StepResult` and `ReachesPrefix` as follows:

```lean
inductive StepResult (State : Type u) (Obs : Type v) (Failure : Type w) where
  | continue (next : State)
  | terminated (obs : Obs)
  | failed (err : Failure)
  | demonic (next : State → Prop)
  | externalCall (boundaryInv : Bool) (next : State → Obs → Prop)

inductive ReachesPrefix (M : SmallStepMachine State Obs Failure) :
    Nat → State → PrefixOutcome Obs Failure → Prop where
  | zero (s : State) :
      ReachesPrefix M 0 s (.completed .outOfFuel)
  | step {n : Nat} {s s' : State} {out : PrefixOutcome Obs Failure} :
      M.step s = .continue s' →
      ReachesPrefix M n s' out →
      ReachesPrefix M (n + 1) s out
  | done {n : Nat} {s : State} {obs : Obs} :
      M.step s = .terminated obs →
      ReachesPrefix M (n + 1) s (.completed (.terminated obs))
  | fail {n : Nat} {s : State} {err : Failure} :
      M.step s = .failed err →
      ReachesPrefix M (n + 1) s (.failed err)
  | demonic {n : Nat} {s s' : State} {next : State → Prop}
      {out : PrefixOutcome Obs Failure} :
      M.step s = .demonic next →
      next s' →
      ReachesPrefix M n s' out →
      ReachesPrefix M (n + 1) s out
  | emptyDemonic {n : Nat} {s : State} {next : State → Prop} :
      M.step s = .demonic next →
      (∀ s', ¬ next s') →
      ReachesPrefix M (n + 1) s (.completed .outOfFuel)
  | externalCallFail {n : Nat} {s : State} {boundaryInv : Bool}
      {next : State → Obs → Prop} {err : Failure} :
      M.step s = .externalCall boundaryInv next →
      boundaryInv = false →
      err = M.boundaryViolationError →
      ReachesPrefix M (n + 1) s (.failed err)
  | externalCallOk {n : Nat} {s s' : State} {boundaryInv : Bool}
      {next : State → Obs → Prop} {o : Obs}
      {out : PrefixOutcome Obs Failure} :
      M.step s = .externalCall boundaryInv next →
      boundaryInv = true →
      next s' o →
      ReachesPrefix M n s' out →
      ReachesPrefix M (n + 1) s out
  | emptyExternalCall {n : Nat} {s : State} {boundaryInv : Bool}
      {next : State → Obs → Prop} :
      M.step s = .externalCall boundaryInv next →
      boundaryInv = true →
      (∀ s' o, ¬ next s' o) →
      ReachesPrefix M (n + 1) s (.completed .outOfFuel)
```

#### 5.2 Constructive Non-Vacuity & Inversion Lemmas (`0` Axioms)

A subtle pitfall with `.demonic` and `.externalCall` is **vacuity**: if `next`
is uninhabited (`∀ s' o, ¬ next s' o`), omitting `emptyExternalCall` would mean
no `ReachesPrefix` outcome exists at `n + 1`, causing `(BehaviorOf M).run q` to
become `.undefined` (or, under universal quantification over reachable outcomes,
vacuously true). Furthermore, proving that every state reaches at least one
outcome at every fuel depth `n` without invoking `Classical.choice` requires a
constructive witness for inhabited demonic branches.

We introduce two typeclasses (`lines 250–275`):
- `TotalStep M`: every state steps to a well-formed `StepResult`;
- `InhabitedDemonic M`: whenever `M.step s = .demonic next` or `.externalCall
  true next`, a constructive witness `(s₀, o₀)` (or proof of emptiness) is
  computably available.

We then prove (`lines 277–482`, `0` axioms, verified via `#print axioms`
producing `[]`):
- `exists_reaches_prefix` (`lines 277-335`): For every `n : Nat` and `s :
  State`, `∃ out, ReachesPrefix M n s out` holds constructively without
  `Classical.choice`.
- `non_vacuity_at_every_depth` (`lines 337-364`): If `(BehaviorOf M init).run q =
  .defined P`, then `∃ o, P o` holds at every fuel depth `q.steps`.
- `reachesPrefix_of_externalCall` (`lines 435-482`): If `M.step s =
  .externalCall boundaryInv next` and `(BehaviorOf M init).run q` is `.defined P`
  at `q.steps = n + 1` from `s`, then:
  1. `boundaryInv = true` (because `boundaryInv = false` triggers
     `externalCallFail`, making `(BehaviorOf M init).run q = .undefined`), and
  2. For every `(s', o)` satisfying `next s' o`, every `n`-step prefix outcome
     from `s'` is included in `P`.

#### 5.3 Canary Validation on Reentrant Callbacks (`ExtMirMachine` vs. `UncheckedMirMachine`)

In `support/StructuralExternalCallAndCanaries.lean` (`lines 750–1150`), we
instantiate `ExtMirMachine` (which emits `.externalCall (checkAdtInv s) ...` at
every external `Call`) and compare it against `UncheckedMirMachine` (which steps
over external calls using `.demonic` without checking `checkAdtInv s` until
function `Return`):

- `canary_reentrant_callback_rejected` (`lines 854-902`): `reentrantBuggyFn`
  writes `0` to a `NonZeroU32` slot, invokes an external callback, and writes
  `1` back to the `NonZeroU32` slot before returning. `ExtMirMachine` **rejects**
  `reentrantBuggyFn` at fuel `2` (`¬ ExtMirLang.WellFormedOn ...
  reentrantBuggyFn`).
- `canary_unchecked_callback_unsoundly_accepts_reentrantBuggyFn`
  (`lines 939-1000`): `UncheckedMirMachine` **unsoundly verifies**
  `reentrantBuggyFn` (`UncheckedMirLang.WellFormedOn ... reentrantBuggyFn` and
  `UncheckedMirLang.SpecOn ...`), exposing the broken `NonZeroU32 = 0` state to
  any reentrant callback!
- `canary_safe_callback_verified` (`lines 1034-1147`): `safeCallbackFn`, which
  restores the `NonZeroU32` invariant (`> 0`) **before** invoking the external
  callback, is **verified** for all fuel depths `n : Nat` under `ExtMirMachine`.

---

### Finding 6: Open-World Callback Framing (`OpenWorldCallbackFraming`)

When verifying a library module that maintains a private multi-slot invariant
`LibInv : Memory → Prop` (for example, `Vec.len ≤ Vec.cap` stored in `slot 0 <
slot 1`) and invokes an unknown user-supplied callback (`FnOnce` / `FnMut`),
entry/exit-only invariant checking (`EnsuresOpenRetLibInv`) is **unsound**.

In `OpenWorldCallbackFraming` (`support/StructuralExternalCallAndCanaries.lean`,
lines 3435–5814), we mechanize:

1. **Isolated Verification Under Entry/Exit-Only Invariants (`lines 3817-4073`):**
   - `getUncheckedOpenBody` assumes `LibInv` (`slot 0 < slot 1`) at entry and
     executes a runtime assertion `assert (slot 0 < slot 1)`. Under
     `EnsuresOpenRetLibInv`, `naive_getUnchecked_verified` proves that
     `getUncheckedOpenBody` is verified for all fuel depths `steps : Nat`.
   - `withTempInvalidOpenBody` assumes `LibInv` at entry, temporarily sets
     `slot 0 := slot 1` (violating `LibInv`), invokes an external callback `cb`,
     and then restores `slot 0 := 0` and `slot 1 := 1` (restoring `LibInv`)
     before returning. Under `EnsuresOpenRetLibInv` (which only checks `LibInv`
     at `Return`), `naive_withTempInvalid_verified` proves that
     `withTempInvalidOpenBody` **also** verifies in isolation for all `steps :
     Nat`!
2. **Concrete 7-Step Reentrancy Exploit (`naive_reentrancy_exploit_triggers_ub`,
   `lines 4152-4205`):**
   When `withTempInvalidOpenBody` is linked in a closed world where the callback
   `cb` invokes `getUncheckedOpenBody`, executing `withTempInvalidOpenBody` from
   initial memory `[0, 1]` (which satisfies `LibInv`) reaches `.failed
   .assertionFailure` in **7 steps**!
3. **Exposure-Partitioned Call-Site Guard & Unexposed Frame Preservation
   (`lines 4210-5814`):**
   We partition memory slots at each external call site into:
   - `exposedSlots : List Nat`: slots reachable by reentrant calls into the
     library, on which `ExposedLibInv` **must hold at the call site**; and
   - unexposed private frame slots (`slot ∉ exposedSlots`), which the external
     callback cannot read or mutate (`UnexposedFramePreserved s s'`) and on
     which the caller may temporarily break local invariants across the call.
   Under `GuardedOpenMachine` and `StructuralOpenMachine`:
   - `withTempInvalid_rejected_under_guarded_call` (`lines 4609-4635`) and
     `structural_withTempInvalid_rejected` (`lines 5581-5625`) **reject**
     `withTempInvalidOpenBody` because `slot 0` and `slot 1` are in
     `exposedSlots` and `ExposedLibInv` is false at the call site.
   - `withRestoredBeforeCall_verified` (`lines 4637-4810`) and
     `structural_withRestoredBeforeCall_verified` (`lines 5627-5810`) **verify**
     the repaired function that restores `ExposedLibInv` before invoking `cb`.
   - `withUnexposedPrivateTemp_verified` (`lines 4812-4983`) **verifies** a
     function that temporarily mutates an unexposed scratch slot (`slot 2 ∉
     exposedSlots`) across an external call while keeping `ExposedLibInv` true
     on `slot 0, slot 1`, recovering framing of `slot 2` after the call via
     `UnexposedFramePreserved`.
   - `open_world_callback_composition_sound` (`lines 5250-5295`) proves by
     induction on `steps : Nat` that linking any `GuardedOpenMachine`-verified
     caller against any `SoundCallbackEnv` preserves both `WellFormedOn` and
     `EnsuresGuardedRetLibInv` in the concrete linked machine.

---

### Finding 7: 48-Mutant TCB Semantic Mutation Audit (`MirSemantics` & `X86Semantics`)

Positive verification suites (`Proof/Verify.lean`) only test that *valid*
programs step to valid outcomes; if a TCB semantic rule in `MirSemantics.lean`
or `X86Semantics.lean` is accidentally weakened (e.g., dropping an alignment,
overflow, or liveness check so that `.failed` becomes `.continue`), every
existing positive proof continues to compile!

Using `support/run_trusted_mutation_audit.py` (results recorded in
`support/mutation_audit_results.json`), we inject **24 semantic mutations into
`Trusted/MirSemantics.lean` (`MIR-Mut-01`–`MIR-Mut-24`)** and **24 semantic
mutations into `Trusted/X86Semantics.lean` (`X01`–`X24`)**:

#### 7.1 `MirSemantics.lean` Mutation Audit (`MIR-Mut-01`–`MIR-Mut-24`)

| Mutant ID | Mutated Function in `Trusted/MirSemantics.lean` | Semantic Bug Injected | Killed by Baseline Positive Proofs? | Killed by Negative Canary Theorem (`TrustedMutationCanaries`) |
| :--- | :--- | :--- | :---: | :--- |
| `MIR-Mut-01` | `sizeOfType` | `.usize => 4` instead of `8` on 64-bit target | Survived | Killed (`canary_M01_sizeOf_usize_wrong_rejected`) |
| `MIR-Mut-02` | `alignOfType` | `.u64 => 4` instead of `8` | Survived | Killed (`canary_M02_alignOf_u64_wrong_rejected`) |
| `MIR-Mut-03` | `intBounds` | Off-by-one `i8` upper bound (`128` instead of `127`) | Survived | Killed (`canary_M03_intBounds_i8_off_by_one_rejected`) |
| `MIR-Mut-04` | `evalBinOp` (`.add` checked) | Drops signed overflow check on `.add` | **Killed** | Killed (`canary_M04_evalBinOp_add_overflow_accepted`) |
| `MIR-Mut-05` | `evalBinOp` (`.sub` checked) | Computes `a + b` instead of `a - b` | **Killed** | Killed (`canary_M05_evalBinOp_sub_wrong_value`) |
| `MIR-Mut-06` | `evalBinOp` (`.div`) | Allows `INT_MIN / -1` signed division overflow | Survived | Killed (`canary_M06_evalBinOp_div_min_neg1_accepted`) |
| `MIR-Mut-07` | `evalBinOp` (`.rem`) | Allows division/remainder by `0` | Survived | Killed (`canary_M07_evalBinOp_rem_zero_accepted`) |
| `MIR-Mut-08` | `evalBinOp` (`.shl`) | Allows shift amount `≥ bitWidth` (`b = 64`) | Survived | Killed (`canary_M08_evalBinOp_shl_overshift_accepted`) |
| `MIR-Mut-09` | `evalUnOp` (`.neg`) | Allows `-INT_MIN` signed negation overflow | Survived | Killed (`canary_M09_evalUnOp_neg_min_accepted`) |
| `MIR-Mut-10` | `readPlace` (`.deref`) | Skips dangling-pointer / liveness check on dereference | Survived | Killed (`canary_M10_readPlace_dangling_deref_accepted`) |
| `MIR-Mut-11` | `readPlace` (`.index`) | Changes bounds check `< len` to `≤ len` (off-by-one OOB read) | Survived | Killed (`canary_M11_readPlace_index_oob_accepted`) |
| `MIR-Mut-12` | `writePlace` (`.deref`) | Skips mutability/permission check on write through shared ref | Survived | Killed (`canary_M12_writePlace_immutable_deref_accepted`) |
| `MIR-Mut-13` | `evalRvalue` (`.cast`) | Skips truncation bounds check on narrowing integer cast | Survived | Killed (`canary_M13_evalRvalue_cast_oob_accepted`) |
| `MIR-Mut-14` | `evalRvalue` (`.ref`) | Creates mutable reference to dead/uninitialized local | Survived | Killed (`canary_M14_evalRvalue_ref_dead_local_accepted`) |
| `MIR-Mut-15` | `execStmt` (`StorageDead`) | Leaves local `.live` instead of marking `.dead` | Survived | Killed (`canary_M15_storageDead_no_op_accepted`) |
| `MIR-Mut-16` | `execStmt` (`Assign`) | Skips destination type compatibility check | Survived | Killed (`canary_M16_assign_type_mismatch_accepted`) |
| `MIR-Mut-17` | `execTerm` (`SwitchInt`) | Inverted branch condition (`0` vs. non-zero target swap) | **Killed** | Killed (`canary_M17_switchInt_inverted_branch`) |
| `MIR-Mut-18` | `execTerm` (`Assert`) | Ignores `cond != expected` (turns `Assert` into no-op jump) | Survived | Killed (`canary_M18_assert_noop_accepted`) |
| `MIR-Mut-19` | `execTerm` (`Return`) | Skips return-slot initialization check | **Killed** | Killed (`canary_M19_return_uninit_accepted`) |
| `MIR-Mut-20` | `execTerm` (`Drop`) | Allows double-drop of already-freed allocation | Survived | Killed (`canary_M20_double_drop_accepted`) |
| `MIR-Mut-21` | `execTerm` (`Call`) | Skips argument count / signature arity check | Survived | Killed (`canary_M21_call_arity_mismatch_accepted`) |
| `MIR-Mut-22` | `MonoAdmitted` | Accepts polymorphic/unsized body rejected by `MonoAdmitted` | Survived | Killed (`canary_M22_monoAdmitted_bypass_accepted`) |
| `MIR-Mut-23` | `initMirState` | Maps argument list in reverse order into locals `_1.._n` | **Killed** | Killed (`canary_M23_initMirState_reversed_args`) |
| `MIR-Mut-24` | `CapturedFn` / `Crate` | Allows wrong function ID or mismatched postcondition witness | Survived | Killed (`canary_M24a_missing_fn_rejected`, `canary_M24b_wrong_id_violates_ensures`) |

- **Baseline `MirSemantics` kill rate:** **`5 / 24` (`20.83%`)** (`19 / 24`
  mutations survive!).
- **Augmented `MirSemantics` kill rate (`TrustedMutationCanaries`):**
  **`24 / 24` (`100.0%`)**.

#### 7.2 `X86Semantics.lean` Mutation Audit (`X01`–`X24`)

Similarly, across the 24 semantic mutations `X01`–`X24` injected into
`Trusted/X86Semantics.lean` (covering 64-bit modular wrapping, flag updates,
`idiv` zero/overflow traps, shift masking, memory alignment, stack slot bounds,
return-address integrity, frame deallocation, and `cmov` source evaluation; full
per-mutant breakdown in `support/mutation_audit_results.json`):

- **Baseline `X86Semantics` kill rate:** **`5 / 24` (`20.83%`)** (`19 / 24`
  mutations survive!).
- **Augmented `X86Semantics` kill rate:** **`24 / 24` (`100.0%`)**.

---

### Finding 8: Proof-Gated `BoundaryCanarySuite` & 13-Guard Mutation Probe

In `support/ProofGatedAndCanarySuite.lean` (`lines 360–635`) and
`support/StructuralExternalCallAndCanaries.lean` (`lines 2520–2805`), we define
`BoundaryCanarySuite (M : X86MachineModel)` — a 21-field proof-gated typeclass
requiring every target machine model `M` to discharge **both** a positive
reachability theorem (`pos_*`, preventing trivial `step = .failed` models) and a
negative refutation theorem (`neg_*`, preventing overly permissive models) across
10 semantic boundary families:

1. **64-bit ALU modular wrapping (`pos_alu_mod64_wrap`, `neg_alu_unbounded_nat`):**
   `(2^64 - 1) + 1` must wrap to `0` (`mod 2^64`), never `2^64` in unbounded
   `Nat`.
2. **Shift-amount bounds (`pos_shift_in_bounds`, `neg_shift_overshift_64`):**
   `shl`/`shr` by `< 64` succeeds; shift by `≥ 64` fails (`none` / UB in the
   strict shift contract).
3. **Division/remainder traps (`pos_div_valid`, `neg_div_by_zero`,
   `neg_div_int64_min_neg1`):** Division by `0` and signed `INT64_MIN / -1`
   overflow both trap.
4. **Memory alignment (`pos_aligned_load_store`, `neg_misaligned_access`):**
   8-byte access at address `8` succeeds; access at unaligned address `3` fails.
5. **Stack slot bounds (`pos_slot_in_bounds`, `neg_slot_out_of_bounds`):**
   Writing to `slot < numSlots` succeeds; writing to `slot ≥ numSlots` fails
   (catching the `writeSlot` bug at `Trusted/X86Semantics.lean:105-115` where an
   out-of-bounds slot write silently returned `s` unchanged!).
6. **Stack frame escape on return (`pos_heap_return_ok`,
   `neg_stack_frame_escape_on_ret`):** Returning a pointer to the current stack
   frame fails on `ret`.
7. **Heap use-after-free (`pos_live_heap_read`, `neg_heap_use_after_free`):**
   Reading a freed heap allocation fails.
8. **Conditional move (`cmov`) source evaluation (`pos_cmov_true_branch`,
   `pos_cmov_false_valid_src`, `neg_cmov_false_invalid_src`):** Even when the
   condition is `false`, `cmov` reads its source operand in hardware; an invalid
   source operand must still trap.
9. **Call stack depth limit (`pos_call_within_depth`,
   `neg_call_depth_exhausted`):** Exceeding `maxCallDepth` traps.
10. **Compile-time function evaluation (`CTFE`) admission (`pos_ctfe_admitted`,
    `neg_ctfe_rejected`):** Non-CTFE-admissible bodies are rejected at admission.

We prove two theorems in both files:
- `currentX86Model_fails_BoundaryCanarySuite`: The unfixed `X86Semantics.lean`
  model (`currentX86Model`, which uses unbounded `Nat` in `evalX86BinOp` and
  silently ignores out-of-bounds `writeSlot`) **provably fails**
  `BoundaryCanarySuite` (`¬ Nonempty (BoundaryCanarySuite currentX86Model)`).
- `instBoundaryCanarySuiteFixedX86Model`: The repaired `fixedX86Model` satisfies
  all 21 fields of `BoundaryCanarySuite`.

To verify that `BoundaryCanarySuite` leaves zero slack in `fixedX86Model`, we
annotated all 13 guard conditions in `fixedX86Model` with `-- MUTATE_GUARD:
Guard-Mut-01` through `-- MUTATE_GUARD: Guard-Mut-13` and ran
`support/run_guard_mutation_probe.py`: every single guard mutation (`13 / 13` =
**`100.0%`**) causes `instBoundaryCanarySuiteFixedX86Model` to fail kernel
typechecking (`support/guard_mutation_results.json`).

---

### Finding 9: 12-Case `TrustedBoundary.lean` Elaboration & Binder Spoofing Probe Suite

In `support/run_audit_probes.py` (full execution output in
`support/audit_probe_results.json`), we test 12 concrete `.olean` + source
probes against Phase 1 (`preflight`, syntax command-kind allowlist) and Phase 2
(`audit`, kernel `ConstantInfo` / `Expr` and axiom closure inspection) of
`trusted/audit/TrustedBoundary.lean` across:
- **`origin/main` initial auditor (`24367bd1a8c784f2578535954f9915e24894a56f`)**
  and the x86-64 prototype auditor (which shares the same Phase 1 and Phase 2
  checks except for one line at line 207), and
- **`origin/main` hardened single-import two-stage auditor
  (`beb778bb135474a67dc017c185d2753a60693d8c` /
  `f2bc17e9be87b777d63c785b31f3370ff058d69b`)**.

#### 9.1 Summary Table of All 12 Probes

| Probe ID | Attack / Test Vector | Initial Auditor (`24367bd1a8c7`) Phase 1 (`preflight`) | Initial Auditor (`24367bd1a8c7`) Phase 2 (`audit`) | Hardened Auditor (`beb778bb1354` / `f2bc17e9be87`) Phase 1 (`preflight`) | Hardened Auditor (`beb778bb1354` / `f2bc17e9be87`) Phase 2 (`audit`) |
| :--- | :--- | :---: | :---: | :---: | :---: |
| `CTRL_POS` | Valid baseline `Mir.crate` and `Proof.verify_crate` | PASS | PASS | PASS | PASS |
| `CTRL_NEG` | `Proof.verify_crate` uses `sorry` (`sorryAx`) | PASS | **FAIL** (blocked) | PASS | **FAIL** (blocked) |
| `Probe A1` | `local notation "Trusted.CrateTheorem" => fun _ => True` in `Proof.lean` | **PASS (bypassed!)** | **FAIL** (`proofCi.type` mismatch) | **FAIL** (`notation` removed from `commandKinds`) | **FAIL** |
| `Probe A2` | `scoped syntax` + `macro_rules` overriding `Trusted.CrateTheorem` | **PASS (bypassed!)** | **FAIL** (`proofCi.type` mismatch) | **FAIL** (`syntax`/`macro_rules` removed) | **FAIL** |
| `Probe A3` | `local macro` overriding `Trusted.CrateTheorem` | **FAIL** (`macro` not in `commandKinds`) | **FAIL** | **FAIL** | **FAIL** |
| `Probe B1` | Implicit/auto-implicit binder `theorem verify_crate {Trusted.CrateTheorem : ...}` | **FAIL** (dot in binder ident rejected by parser) | **FAIL** | **FAIL** | **FAIL** |
| `Probe B2` | `namespace Trusted def CrateTheorem (_ : Crate) : Prop := True` inside `Proof.lean` | **PASS (bypassed!)** | **FAIL** (`Proof.Trusted.CrateTheorem` ≠ `Trusted.CrateTheorem`) | PASS | **FAIL** (`!isTrustedMod && isTrustedNamespace` check) |
| `Probe B3` | `def _root_.Trusted.CrateTheorem (_ : Trusted.Crate) : Prop := True` in `Proof.lean` (when `Trusted` omits `CrateTheorem`) | **PASS (bypassed!)** | **FAIL** (`origin env` / duplicate constant) | **FAIL** (`validateUserDeclIdent` rejects `_root_`) | **FAIL** (`isTrustedNamespace` + `trustedLocals.contains`) |
| `Probe C1` | Universe-polymorphic `theorem verify_crate.{u} : Trusted.CrateTheorem Mir.crate` | **PASS (bypassed!)** | **PASS (VULNERABLE!)** | PASS | **FAIL** (`proofCi.levelParams.isEmpty` check) |
| `Probe C2` | `noncomputable def crate : Trusted.Crate := (Classical.choice witness).val` in `Mir.lean` | **PASS (bypassed!)** | **PASS (VULNERABLE!)** | PASS | **FAIL** (`closure ... #[] #[`Mir.crate]` zero-axiom check) |
| `Probe C3` | `abbrev crate : Trusted.Crate` in `Mir.lean` | PASS | PASS (`ConstantInfo.defnInfo` benign) | PASS | PASS (`ConstantInfo.defnInfo` benign) |
| `Probe D1` | `#[trusted]` macro expansion (`Trusted.candidate`) injecting unverified axiom | **FAIL** (`#[trusted]` rejected outside `Trusted`) | **FAIL** | **FAIL** | **FAIL** |

#### 9.2 Detailed Analysis of Probes `C1` and `C2` (Full Phase 1 + Phase 2 Bypasses in `24367bd1a8c7`) and How `beb778bb1354` Closes Them

1. **Probe `C1` (`theorem verify_crate.{u} : Trusted.CrateTheorem Mir.crate`):**
   In Lean 4's kernel (`src/kernel/declaration.h`), universe parameters on a
   declaration are stored in `ConstantInfo.levelParams : List Name`, **not**
   inside `ConstantInfo.type : Expr`. When `Proof.verify_crate.{u}` declares an
   unused universe parameter `u` (or uses `u` only inside its proof term),
   `proofCi.type` is still `Expr.app (Expr.const `Trusted.CrateTheorem [])
   (Expr.const `Mir.crate [])`. Because the initial `origin/main` auditor
   (`24367bd1a8c784f2578535954f9915e24894a56f`, lines 945–958) checked
   `proofCi.type` without checking `proofCi.levelParams.isEmpty` or
   `mirCrateCi.levelParams.isEmpty`, `Probe C1` passed **both** Phase 1 and
   Phase 2! The hardened `origin/main` auditor
   (`beb778bb135474a67dc017c185d2753a60693d8c`, lines 1467–1468 and 1477–1478)
   explicitly checks `mirCrateCi.levelParams.isEmpty` and
   `proofCi.levelParams.isEmpty`, blocking `Probe C1`.
2. **Probe `C2` (`noncomputable def crate : Trusted.Crate := (Classical.choice witness).val`):**
   In the initial `origin/main` auditor
   (`24367bd1a8c784f2578535954f9915e24894a56f`, line 959), Phase 2 ran `closure`
   only once over the combined root set `#[`Mir.crate, `Proof.verify_crate]`
   using the full `axiomPolicy` (`#[`Classical.choice, `Quot.sound, `propext]`).
   Because `noncomputable` is permitted in `declModifiers` (line 277), `Mir.lean`
   could synthesize `Mir.crate : Trusted.Crate` nonconstructively using
   `Classical.choice` (for example, choosing a `CapturedFn` whose specification
   is trivially true by `Classical.choice`), and `Probe C2` passed **both**
   Phase 1 and Phase 2! The hardened `origin/main` auditor
   (`beb778bb135474a67dc017c185d2753a60693d8c`, line 1472) runs a separate
   zero-axiom closure check on `Mir.crate`:
   ```lean
   let _ ← closure lookup (origin env) #[] #[`Mir.crate]
   ```
   with an empty axiom allowlist `#[]`, rejecting any axiom (including
   `Classical.choice`, `propext`, and `Quot.sound`) in the transitive dependency
   cone of `Mir.crate` and blocking `Probe C2`.

---

## Boundaries

| Topic | Mechanized / Empirically Verified in This Package | Remaining Engineering Action / Out of Scope |
| :--- | :--- | :--- |
| Universal `TCBModel` realizability | `refTCBModel_realizes_tcb`, `relative_consistency_meta_theorem`, `universal_hTcb_never_contradictory`, and `alwaysUbCrate_unprovable_under_universal_tcb` proved (`0` axioms) in `support/TcbConsistencyAndAuditProbes.lean`. | Migrate `Trusted/Refinement.lean` and `Trusted/MirSemantics.lean` from fixed `opaque` constants to universal quantification over `(M : TCBModel)` satisfying `M.RealizesTCB`. |
| Proof-gated compilation & `ScopedVerificationResult` | 20 theorems (`0` axioms) in `support/ProofGatedCompilationAndTrustPolicy.lean` and 9 theorems in `support/ProofGatedAndCanarySuite.lean` proving IR cut elimination and clause-guarded explosion isolation. | Integrate `ScopedVerificationResult` and `CapturedPipelineFn` into `Trusted/Refinement.lean` so `rustc-capture` binds `MirBody` + `compileStage0` inside `CrateTheorem`. |
| Structural external calls & open-world callback framing | `StepResult.externalCall`, `ReachesPrefix` constructors, constructive `exists_reaches_prefix` (`0` axioms), and `open_world_callback_composition_sound` proved in `support/StructuralExternalCallAndCanaries.lean` (5,814 lines). | Generalize `CallbackEnv` from single-callee arity to mutually recursive callback tables and multi-argument System V AMD64 register/stack passing. |
| TCB semantic & guard mutation testing | 25 `MirSemantics` negative canaries (`canary_M01`–`canary_M24b`), 24 `X86Semantics` negative canaries (`support/run_trusted_mutation_audit.py`), and 13 `BoundaryCanarySuite` guard mutations (`support/run_guard_mutation_probe.py`), all achieving `100.0%` mutation kill rates. | Wire the negative canary manifest check directly into `trusted/audit/src/lib.rs` so `cargo anneal` rejects any `.olean` environment missing the canary theorems. |
| `TrustedBoundary.lean` elaboration & binder probes | 12-case probe suite (`support/run_audit_probes.py` and `support/audit_probe_results.json`) verifying that `beb778bb135474a67dc017c185d2753a60693d8c` / `f2bc17e9be87b777d63c785b31f3370ff058d69b` closes all 6 bypass vectors (`A1`, `A2`, `B2`, `B3`, `C1`, `C2`). | If `Mir.lean` is intended to forbid `abbrev crate` (`Probe C3`), restrict `Mir.lean` in Phase 1 `inspectFile` to `Lean.Parser.Command.definition` only. |

---

## Evidence

### 1. Preserved Package Support Artifacts

All ten support files from both constituent investigations are preserved in
`support/` within this package:

| Path | Lines | Bytes | SHA-256 Digest | Role |
| :--- | ---: | ---: | :--- | :--- |
| `support/StructuralExternalCallAndCanaries.lean` | 5,814 | 229,123 | `947ed4e2a2b75d7ed3c3cef8a521bd7364aed529bfc815a4f34113075ea1519d` | Self-contained Lean 4 (`v4.34.1`) formalization containing `StructuralExternalCall`, `TrustedMutationCanaries` (`canary_M01`–`canary_M24b`), `BoundaryCanary` (`BoundaryCanarySuite`), and `OpenWorldCallbackFraming` (`0` `sorryAx`, `0` `Lean.ofReduceBool`) |
| `support/run_trusted_mutation_audit.py` | 2,220 | 95,344 | `840af0363df7a6e13cc85255dbd2e3d20c35cbce3233385aa8727f15eca564af` | Automated 48-mutant semantic mutation harness (`MIR-Mut-01`–`MIR-Mut-24` on `MirSemantics.lean` and `X01`–`X24` on `X86Semantics.lean`) |
| `support/mutation_audit_results.json` | 619 | 39,272 | `9650426598a00cce920f26a9e74f7c10cb295f7a0aa2a0bc525d66af5d1432a9` | Machine-readable output of `support/run_trusted_mutation_audit.py` recording baseline (`5/24` = `20.83%`) vs. augmented (`24/24` = `100.0%`) mutation kill results |
| `support/run_guard_mutation_probe.py` | 256 | 12,116 | `4ff90255a58fe2cb71ee1a78c499cbaefa262b7f436b9761d4fb57d7f7f709db` | Automated 13-guard mutation probe testing `BoundaryCanarySuite` against all `-- MUTATE_GUARD:` markers in `support/StructuralExternalCallAndCanaries.lean` |
| `support/guard_mutation_results.json` | 140 | 6,547 | `446e6da675a24e0d38cf29ca3b51c72b87bbb402baa31ac5a4e8d7f93ed8c458` | Machine-readable output of `support/run_guard_mutation_probe.py` recording `13/13` (`100.0%`) killed guard mutations |
| `support/TcbConsistencyAndAuditProbes.lean` | 654 | 25,891 | `77fda98aac4ded60252c1938e937b6ee510dbd10e857b7c4ca64935a787dc143` | Standalone Lean 4 (`v4.34.1`) mechanization of `hTcb` vacuity, contradictory `opaque` witnesses, universal `TCBModel` realizability, and the Rust-to-x86 capture gap (10 `#print axioms` checks) |
| `support/ProofGatedCompilationAndTrustPolicy.lean` | 1,234 | 48,712 | `577b99d49ad8edd90273df309d98ab707cfa22347c960cf51bdc3fa5b023a040` | Standalone Lean 4 (`v4.34.1`) mechanization of `BoundaryCodec`, proof-gated IR cut elimination, antecedent Principle-of-Explosion counterexamples, `ScopedVerificationResult`, and `UnifiedCrateTheorem` (20 `#print axioms` checks, all `0` axioms) |
| `support/ProofGatedAndCanarySuite.lean` | 635 | 24,980 | `612b9afef16959e9f45c9dd0075ebb277f2dcdeeac3439a00c202ab4fb998e94` | Standalone Lean 4 (`v4.34.1`) mechanization of `BehaviorCodec`, `FineGrainedTCBItem`, `strictPolicy`, `BoundaryCanarySuite`, `currentX86Model` refutation, and `fixedX86Model` conformance (9 `#print axioms` checks) |
| `support/run_audit_probes.py` | 786 | 31,420 | `859c8636697719fee3f0838a18f41c27b4a78b9ac23d789e298f57d9cfa2c2a8` | Configurable Python 3 probe runner executing all 12 `TrustedBoundary.lean` elaboration and binder spoofing cases |
| `support/audit_probe_results.json` | 29,110 | 912,485 | `8bfec96dc980e5bc4d6492a03b0c97fbc55c076a3f1235695ec4ff4e1280f87d` | Complete JSON execution record (`returncode`, `stdout`, `stderr`, `result_json`) for all 12 probe cases |

### 2. Key Mechanized Declarations Across the Four `.lean` Developments

| File & Namespace | Declaration | Lines | Summary |
| :--- | :--- | :--- | :--- |
| `support/TcbConsistencyAndAuditProbes.lean` (`Anneal.TcbAuditProbes`) | `pme_rejected_target_undefined_soundOn_false` & `hidden_opaque_witness_soundOn_false` | `lines 307-350` | Proves that `RustcCompiler.SoundOn (fun _ => True)` is `False` under `.undefined` target witnesses on rejected/fuel-0 queries. |
| `support/TcbConsistencyAndAuditProbes.lean` (`Anneal.TcbAuditProbes`) | `refTCBModel_realizes_tcb`, `relative_consistency_meta_theorem`, `universal_hTcb_never_contradictory`, `alwaysUbCrate_unprovable_under_universal_tcb` | `lines 463-516` | Constructive inhabitation (`0` axioms) of `TCBModel.RealizesTCB` and relative consistency of `UniversalVerificationResult`. |
| `support/TcbConsistencyAndAuditProbes.lean` (`Anneal.TcbAuditProbes`) | `mir_to_x86_unverified_capture_gap` & `verified_pipeline_rejects_capture_mismatch` | `lines 603-641` | Formalizes the unverified `rustc-capture` gap and proves that binding `MirBody` + `Compiles` inside `CrateTheorem` rejects mismatches (`0` axioms). |
| `support/ProofGatedCompilationAndTrustPolicy.lean` (`Anneal.ProofGatedTrustPolicy`) | `spurious_ir_ub_blocks_source_obligation`, `omitted_ir_ub_blocks_pass_obligation`, `omitted_ir_outcome_blocks_pass_obligation`, `proof_gated_compilation_eliminates_ir_from_tcb`, `multi_stage_proof_gated_compilation_eliminates_irs_from_tcb` | `lines 303-433` | Proves that dual source + pass proof gates eliminate intermediate IRs (`MirLang`, `AnSSALang`) and compiler passes from the TCB (`0` axioms). |
| `support/ProofGatedCompilationAndTrustPolicy.lean` (`Anneal.ProofGatedTrustPolicy`) | `global_antecedent_omission_explodes_crate` & `intra_function_antecedent_omission_explodes_other_obligations` | `lines 602-643` | Proves that placing omitted computable obligations into an implication antecedent explodes the entire crate or intra-function theorem (`0` axioms). |
| `support/ProofGatedCompilationAndTrustPolicy.lean` (`Anneal.ProofGatedTrustPolicy`) | `scoped_zeroTrust_iff_allHold`, `scoped_omission_isolates_buggy_fn`, `scoped_omission_isolates_intra_fn_obligations`, `unified_crate_theorem_non_vacuous_and_isolated` | `lines 799-1211` | Proves that clause-guarded `ScopedVerificationResult` and `UnifiedCrateTheorem` isolate omitted work-in-progress obligations without explosion (`0` axioms). |
| `support/ProofGatedAndCanarySuite.lean` (`Anneal.ProofGatedAndCanarySuite`) | `strictPolicy_forbids_omitted_proofs`, `gated_pipeline_soundness`, `currentX86Model_fails_BoundaryCanarySuite`, `instBoundaryCanarySuiteFixedX86Model` | `lines 288-621` | Proves strict policy soundness, refutes `currentX86Model` against `BoundaryCanarySuite`, and instantiates `BoundaryCanarySuite` for `fixedX86Model`. |
| `support/StructuralExternalCallAndCanaries.lean` (`StructuralExternalCall`) | `exists_reaches_prefix`, `non_vacuity_at_every_depth`, `reachesPrefix_of_externalCall` | `lines 277-482` | Constructive (`Classical.choice`-free) proof of prefix reachability at every depth `n` and call-site `boundaryInv = true` enforcement (`0` axioms). |
| `support/StructuralExternalCallAndCanaries.lean` (`StructuralExternalCall`) | `canary_reentrant_callback_rejected`, `canary_unchecked_callback_unsoundly_accepts_reentrantBuggyFn`, `canary_safe_callback_verified` | `lines 854-1147` | Proves rejection of `reentrantBuggyFn` under `ExtMirMachine`, unsound acceptance under `UncheckedMirMachine`, and verification of `safeCallbackFn`. |
| `support/StructuralExternalCallAndCanaries.lean` (`TrustedMutationCanaries`) | `canary_M01_sizeOf_usize_wrong_rejected` .. `canary_M24b_wrong_id_violates_ensures` | `lines 1815-2515` | 25 negative canary refutation theorems killing all 24 semantic mutations (`MIR-Mut-01`–`MIR-Mut-24`) of `Trusted/MirSemantics.lean`. |
| `support/StructuralExternalCallAndCanaries.lean` (`OpenWorldCallbackFraming`) | `naive_getUnchecked_verified`, `naive_withTempInvalid_verified`, `naive_reentrancy_exploit_triggers_ub`, `open_world_callback_composition_sound` | `lines 3817-5295` | 7-step reentrancy counterexample to entry/exit-only library invariants and inductive soundness proof for exposure-partitioned `GuardedOpenMachine`. |

---

## Revalidation

All standalone verification commands below can be run directly from this package
directory (`reports/anneal-tcb-realizability-external-calls-and-mutation-testing/`).

### 1. Kernel-Verify All Four Standalone Lean 4 (`v4.34.1`) Proof Developments

Requires Lean 4 `v4.34.1` (`lean` on `PATH` or under
`~/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean`):

```bash
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/TcbConsistencyAndAuditProbes.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/ProofGatedCompilationAndTrustPolicy.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/ProofGatedAndCanarySuite.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/StructuralExternalCallAndCanaries.lean
```

Expected outcome: exit code `0` on all four files, zero warnings, zero
`sorryAx`, zero `Lean.ofReduceBool`, and all `#print axioms` checks confirming
the documented zero-axiom (`[]`) or `[propext]` footprints.

### 2. Re-Run the 13-Guard Mutation Probe (`BoundaryCanarySuite`)

Runs entirely against `support/StructuralExternalCallAndCanaries.lean` with no
external checkout required:

```bash
python3 support/run_guard_mutation_probe.py \
  --target-file support/StructuralExternalCallAndCanaries.lean \
  --output-json support/guard_mutation_results.json
```

Expected outcome: exit code `0`, `Total guard mutations tested: 13`, `Killed by
BoundaryCanarySuite: 13`, `Survived: 0`, and `Mutation kill rate: 100.0%`.

### 3. Re-Run the 48-Mutant TCB Semantic Mutation Audit and 12-Case `TrustedBoundary.lean` Probe Suite

To re-run the 48-mutant TCB semantic mutation harness (`MIR-Mut-01`–`MIR-Mut-24`
and `X01`–`X24`) and the 12-case `TrustedBoundary.lean` elaboration and binder
spoofing probe suite against an Anneal checkout:

```bash
python3 support/run_trusted_mutation_audit.py \
  --out-dir support
python3 support/run_audit_probes.py \
  --sysroot "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  --anneal-root /path/to/anneal
```

Expected outcome: exit code `0` on both scripts, regenerating
`support/mutation_audit_results.json` (`24/24` = `100.0%` augmented kill rate vs.
`5/24` = `20.83%` baseline kill rate) and `support/audit_probe_results.json`
(all 6 spoofing vectors `A1`, `A2`, `B2`, `B3`, `C1`, `C2` blocked in the
hardened `origin/main` auditor).
