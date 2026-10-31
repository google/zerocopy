<!-- Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms. -->

# Anneal TCB Realizability, Proof-Gated Compilation, Scoped Trust Policies, and Boundary Audit Probes

## Summary

Anneal's verification gate (`Trusted.CrateTheorem` checked by
`trusted/audit/TrustedBoundary.lean`) relies on four interacting invariants:

1. **Non-vacuity of environment and lowering hypotheses (`hTcb`):**
   In `trusted-core` (`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and
   `mir-to-x86` (`4f45f0a391a921ced9c9dc773b9a040dbc215d14`),
   `VerificationResultOn` (`Trusted/Refinement.lean:444-456`) places
   `AllHold (assumptions.map TrustedAssumption.meaning)` on the left-hand side
   of an implication (`→`). Any pointwise contradiction in `hTcb` at a single
   boundary query—such as a post-monomorphization error (PME) rejected layout
   query where `(MirSem body q₀).defined` holds vacuously, or a zero-step query
   (`q₀.steps = 0`) where `ReachesPrefix` is trivially `.running`—acts as an
   unchecked local axiom that proves `Trusted.CrateTheorem` for an arbitrary
   UB-triggering crate (`alwaysUbCrate`) with zero kernel axioms
   (`contradictory_hTcb_proves_ub_crate`). Moreover, the underlying witness
   terms supplied to `opaque TargetSem := fun _ _ => Partial.ub` and
   `opaque π_c := fun b => b` in `Trusted/MirSemantics.lean:690-716` and
   `Trusted/X86Semantics.lean:716-742` are themselves contradictory with
   `Compiler.SoundOn` at `steps = 0` (`hidden_opaque_witness_soundOn_false`,
   `x86_hidden_opaque_witness_soundOn_false`), and top-level `opaque`
   declarations prevent `theory/` from instantiating a consistent model.
   Packaging uninterpreted target symbols into a `TCBModel` structure and
   quantifying universally (`CrateTheoremUniversal c := ∀ M : TCBModel,
   CrateTheoremIn M c`) paired with a zero-axiom reference model `refTCBModel`
   proves constructive realizability (`refTCBModel_realizes_tcb`), rules out
   contradictory `hTcb` hypotheses (`universal_hTcb_never_contradictory`), and
   makes UB-triggering crates refutable
   (`alwaysUbCrate_unprovable_under_universal_tcb`).
2. **Bidirectional fail-closedness and relational cut elimination via
   proof-gated compilation:**
   When an intermediate language (`MirLang` or `AnSSALang` in `theory/`) is
   connected to the trusted target language (`X86Lang` in `trusted/`) via a
   boundary codec `codec : BoundaryCodec L_src L_tgt` (`decompileQuery`,
   `decompileOut`), requiring both the source obligation
   `L_src.sem s ≤ L_src.SpecOn pre post` and the pass refinement obligation
   `Compiles L_src L_tgt codec.toMorphism s t` sandwiches the untrusted
   intermediate semantics `L_src.sem s`. Spurious UB in `L_src` refutes the
   source obligation (`spurious_ir_ub_blocks_source_obligation`,
   `spurious_ub_breaks_wellFormedOn`), whereas omitted UB or omitted outcomes
   in `L_src` refute the pass obligation
   (`omitted_ir_ub_blocks_pass_obligation`,
   `omitted_ir_outcome_blocks_pass_obligation`, `missing_ub_breaks_compiles`,
   `missing_outcome_breaks_compiles`). When both obligations hold, `L_src.sem`
   cancels out by lattice transitivity (`Preorder.le_trans`), yielding a target
   specification theorem on `X86Lang` that does not mention `L_src.sem`
   (`BoundaryCodec.toMorphism_specOn`,
   `proof_gated_compilation_eliminates_ir_from_tcb`,
   `multi_stage_proof_gated_compilation_eliminates_irs_from_tcb`). In contrast,
   `mir-to-x86` (`4f45f0a391a9`) translates MIR to `X86Body` in unverified Rust
   (`trusted/rustc-capture/src/lib.rs:1435-1561`) and stores only `X86Body` in
   `Trusted.Crate`, leaving `MirBody`, `compileStage0`, and `.anneal/Prog.s`
   unbound in `Trusted.CrateTheorem` (`mir_to_x86_unverified_capture_gap`).
   Recording both `progMir` and `progX86` in `VerifiedCapturedFn` and requiring
   `Stage0Compiler.Compiles fn.progMir fn.progX86` closes that capture gap
   (`verified_pipeline_rejects_capture_mismatch`).
3. **Isolation of concrete-program proof omissions via positive per-obligation
   scoping (`ScopedVerificationResult`):**
   Unlike uninterpreted `TCBModel` hypotheses, `MirLang.sem` and `X86Lang.sem`
   are transparent, computable functions. Placing a concrete-program proof
   omission (`assumeSourceWellFormed "fn_wip" .ubAtBoundary` or
   `assumePassCompiles`) on the left of `→` causes a real UB bug at a single
   boundary input (`qBoundary`) in `"fn_wip"` to reduce its antecedent
   proposition to `False` (`transparent_buggy_wip_assumption_is_false`). By
   `False.elim`, this single omitted buggy function proves
   `CrateTheoremAntecedent` with zero axioms for an unexempted, unconditionally
   buggy function `"fn_critical"` in the same crate
   (`global_antecedent_omission_explodes_crate`) and explodes sibling
   obligations within a single function
   (`intra_function_antecedent_omission_explodes_other_obligations`). Replacing
   antecedent omissions with positive per-obligation masking on the consequent
   (`ObligationEntry.requiredProp omitted e` inside `ScopedVerificationResult`
   and `UnifiedCrateTheorem`) isolates omitted obligations across both
   functions and passes (`scoped_omission_isolates_buggy_fn`,
   `scoped_omission_isolates_intra_fn_obligations`) while preserving
   unconditional target guarantees for every unomitted function in a partially
   verified crate (`extract_verified_fn_from_partially_verified_crate`).
4. **Target-semantics guard canaries (`BoundaryCanarySuite`) and `.olean`
   boundary audit hardening (`TrustedBoundary.lean`):**
   Instantiating `BoundaryCanarySuite (M : X86MachineModel)` (11 positive
   conformance witnesses paired with 10 negative refutation theorems) refutes
   the unmasked `Nat` ALU and unchecked stack-slot model of `X86Semantics.lean`
   at `4f45f0a391a9` (`currentX86Model_fails_BoundaryCanarySuite`), validates
   `fixedX86Model` (`instBoundaryCanarySuiteFixedX86Model`), and kills 13/13
   (100%) guard mutations under Lean 4.34.1 kernel checking. At the `.olean`
   boundary, executing 12 adversarial elaboration and binder probes against
   `TrustedBoundary.lean` across `main` (`24367bd1a8c7`), `pr-65`
   (`76fad1a1befa`), and `mir-to-x86` (`4f45f0a391a9`) demonstrates that while
   all three versions reject auto-bound `variable` hypotheses (`Probes A1–A2`)
   and local `notation` (`Probe B1`), `main` and `mir-to-x86` allow four
   complete Phase 1 + Phase 2 bypasses: `namespace Trusted` spoofing in
   `Anneal.lean` (`Probe B2`), `_root_.Trusted.CrateTheorem` spoofing (`Probe
   B3`), universe-polymorphic `theorem verify_crate.{u}` (`Probe C1`), and
   `noncomputable def crate` via `Classical.choice` (`Probe C2`). All four
   bypasses are closed in `pr-65` (`76fad1a1befa`).

## Applicability

The findings and preserved artifacts in this package apply to the five pinned
subjects in `REPORT.json`:

| Subject | Repository & Revision | Examined Paths & Role |
| :--- | :--- | :--- |
| `main` | `joshlf/anneal` at `24367bd1a8c784f2578535954f9915e24894a56f` | `trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/lib.rs`, `trusted/lean/Trusted/Attributes.lean`, `trusted/lean/foundation-lock.json` (baseline `.olean` boundary auditor) |
| `pr-65` | `joshlf/anneal` at `76fad1a1befa2e4c038d88c3a1bbbe873acb1322` | `trusted/audit/TrustedBoundary.lean`, `trusted/audit/src/lib.rs`, `trusted/audit/tests/boundary_audit.rs` (hardened `.olean` boundary auditor closing namespace, `_root_`, `levelParams`, and `Mir.crate` axiom-closure gaps) |
| `trusted-core` | `joshlf/anneal` at `e6a0b2da5ec39a4c0cfd22bf323885022837b5dc` | `trusted/lean/Trusted/Refinement.lean`, `trusted/lean/Trusted/StepResult.lean`, `trusted/lean/Trusted/MirSemantics.lean`, `theory/Anneal/Refinement.lean`, `theory/Anneal/MirLemmas.lean` (core refinement lattice, `VerificationResultOn`, and MIR semantics) |
| `mir-to-x86` | `joshlf/anneal` at `4f45f0a391a921ced9c9dc773b9a040dbc215d14` | `trusted/lean/Trusted/Refinement.lean`, `trusted/lean/Trusted/X86Semantics.lean`, `theory/Anneal/Compiler/NaiveCodegen.lean`, `theory/Anneal/Compiler/Peephole.lean`, `theory/Anneal/MirLemmas.lean`, `trusted/rustc-capture/src/lib.rs`, `trusted/audit/TrustedBoundary.lean` (2-stage MIR-to-x86-64 pipeline and target ISA semantics) |
| Lean 4 Toolchain | `leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52` (`v4.34.1`) | Lean 4 kernel and elaborator invoked with `-DElab.async=false -Ddebug.skipKernelTC=false` |

The relationships among these subjects are:

- `trusted-core` (`e6a0b2da5ec3`) and `mir-to-x86` (`4f45f0a391a9`) share the
  refinement lattice and `VerificationResultOn` trust-gate definitions in
  `Trusted/Refinement.lean`; `mir-to-x86` extends `trusted-core` with
  `Trusted/X86Semantics.lean` and the verified compiler passes in
  `theory/Anneal/Compiler/`.
- `main` (`24367bd1a8c7`), `pr-65` (`76fad1a1befa`), and `mir-to-x86`
  (`4f45f0a391a9`) represent three comparative revisions of
  `trusted/audit/TrustedBoundary.lean` evaluated against the same 12
  adversarial probe modules under `leanprover/lean4:v4.34.1`.

## Findings

### Finding 1: Antecedent `hTcb` Vacuity and Contradictory `opaque` Witnesses

`Basis: source + execution + derived`

In `trusted-core` (`Trusted/Refinement.lean:444-456` and
`Trusted/MirSemantics.lean:859-865` at
`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`), `VerificationResultOn` is defined
as:

```lean
def VerificationResultOn {L_src L_tgt : Language} {α : Type} [TrustedAssumption α]
    (C : Compiler L_src L_tgt)
    (policy : TrustPolicy α)
    (assumptions : List α)
    (prog : L_src.Prog)
    (pre : L_src.Query → Prop)
    (specs : List (L_src.Behavior → Prop)) : Prop :=
  AllHold (assumptions.map policy.isAllowed) ∧
  (AllHold (assumptions.map TrustedAssumption.meaning) →
    AllHold ((L_src.WellFormedOn pre :: specs).map (C.Verified prog)))
```

`TrustedBoundary.lean` verifies that the kernel environment contains zero user
`axiom` declarations (`ci.isAxiom`) and only the standard foundation axioms
(`{Classical.choice, Quot.sound, propext}`). However, because
`AllHold (assumptions.map TrustedAssumption.meaning)` stands on the left-hand
side of an implication (`→`) inside `Trusted.CrateTheorem`, any contradiction
derivable from `hTcb : AllHold (c.tcb.map TrustedAssumption.meaning)` at a
single boundary query $q_0$ makes `Trusted.CrateTheorem c` provable via
`False.elim` with zero kernel axioms.

In `support/TcbConsistencyAndAuditProbes.lean` (Sections 1–2, lines 50–402),
two boundary domains of `MirSem` (`Trusted/MirSemantics.lean:662-663`, defined
via `BehaviorOf` in `Trusted/StepResult.lean:169-177`) are shown to make
`(MirSem body q₀).defined` unconditionally `True`:

1. **Rejected post-monomorphization queries
   (`¬ MonoAdmitted q₀.init.tySizes body`):**
   In `Trusted/MirSemantics.lean:611-612`, `initMirState body s` conjoins
   `initEntryState body s ∧ MonoAdmitted s.tySizes body`. When a query $q_0$
   supplies type-parameter sizes that violate `MonoAdmitted` (for example,
   `tySizes 0 = 4 ≠ 8 = tySizes 1` on a body containing a PME `const` size
   assertion), `initMirState body q₀.init` is `False`. Because
   `(MirSem body q₀).defined` is `initMirState body q₀.init → ∀ tr out, ...`,
   `(MirSem body q₀).defined` holds vacuously
   (`pme_rejected_query_mirSem_defined`, lines 273–277). Under forward
   refinement (`p₁ ≤ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, ...` in
   `Trusted/Refinement.lean:269-277`), `Compiler.SoundOn C body` requires
   `(L_tgt.sem p_tgt q₀).defined` whenever `(C.π (MirSem body) q₀).defined`
   holds. If a target model represents PME-rejected monomorphizations as target
   undefinedness (`(TargetSem (rustc body) q₀).defined ↔ MonoAdmitted ...`)
   under `C.π = id`, `Compiler.SoundOn C body` at that single rejected layout
   query $q_0$ derives `False` (`pme_rejected_target_undefined_soundOn_false`,
   lines 307–322).
2. **Zero-step queries (`q₀.steps = 0`):**
   In `Trusted/StepResult.lean:119-121`, `ReachesPrefix M p 0 s tr out` has a
   single constructor `.zero` with `out = .running ≠ .failed`. Therefore, for
   every `body : MirBody` (including `.alwaysUbAtStep1`, which unconditionally
   fails at step 1), `(MirSem body ⟨s, 0⟩).defined` is `True`
   (`step0_query_mirSem_defined`, lines 281–287).

Combining these facts, `contradictory_hTcb_proves_ub_crate` (lines 397–402)
proves `CrateTheoremFor PmeRejectingCompiler alwaysUbCrate`—including
`C.Verified .alwaysUbAtStep1 (MirLang.Spec (fun _ _ => False))` for a program
that fails at step 1—using zero user axioms.

Furthermore, in `Trusted/MirSemantics.lean:690-716`
(`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and
`Trusted/X86Semantics.lean:716-742`
(`4f45f0a391a921ced9c9dc773b9a040dbc215d14`), the target compiler symbols are
declared as top-level `opaque` constants with explicit witness terms:

```lean
@[candidate mir_semantics] opaque rustc : MirBody → TargetArtifact :=
  fun _ => { unit := () }

@[candidate mir_semantics] opaque TargetSem :
    TargetArtifact → ExecQuery MirState →
      Partial (ExecOut Unit MirVal → Prop) :=
  fun _ _ => Partial.ub

@[candidate mir_semantics] opaque π_c :
    MirLang.Behavior → TargetLang.Behavior :=
  fun b => b
```

Because `Partial.ub.defined = False` while `(MirSem body ⟨s₀, 0⟩).defined =
True` and `(X86Sem body ⟨s₀, 0⟩).defined = True`, evaluating `Compiler.SoundOn`
on the actual witness terms supplied to `opaque` in `MirSemantics.lean` and
`X86Semantics.lean` derives `False` for every `body : MirBody` and every
`body : X86Body` (`hidden_opaque_witness_soundOn_false` at lines 342–350 and
`x86_hidden_opaque_witness_soundOn_false` at lines 572–582 of
`support/TcbConsistencyAndAuditProbes.lean`). Only the kernel's opacity barrier
prevents `Proof.lean` from unfolding `TargetSem` and `π_c` to `Partial.ub` and
`id` and discharging `Trusted.CrateTheorem` for arbitrary crates. At the same
time, because `rustc`, `TargetSem`, and `π_c` are fixed top-level `opaque`
constants rather than model parameters, `theory/` cannot instantiate them with
a concrete reference model to prove inside Lean that `AllHold (c.tcb.map
TrustedAssumption.meaning)` is satisfiable.

### Finding 2: Universal `TCBModel` Quantification and Realizability Witnesses

`Basis: source + execution + derived`

In `support/TcbConsistencyAndAuditProbes.lean` (Section 3, lines 404–516),
replacing top-level `opaque` constants with an explicit `TCBModel` structure
and universal quantification eliminates `hTcb` vacuity:

```lean
structure TCBModel where
  TargetProg : Type
  rustc : MirBody → TargetProg
  TargetSem : TargetProg → ExecQuery MirState → Partial (ExecOut Unit Nat → Prop)
  π_c : MirLang.Behavior → Behavior (ExecQuery MirState) (ExecOut Unit Nat → Prop)

def CrateTheoremUniversal (c : Crate) : Prop :=
  ∀ M : TCBModel, CrateTheoremIn M c
```

Defining the constructive identity reference model `refTCBModel : TCBModel`
(`TargetProg := MirBody`, `rustc := id`, `TargetSem := MirSem`, `π_c := id`,
lines 445–449) yields three machine-checked theorems with **zero axioms**:

1. **Constructive Realizability (`refTCBModel_realizes_tcb` and
   `tcbModel_realizable`, lines 463–476):** For every crate `c : Crate`,
   `AllHold (c.tcb.map (TCBItem.meaningIn refTCBModel))` holds constructively,
   witnessing `∃ M : TCBModel, AllHold (c.tcb.map (TCBItem.meaningIn M))`.
2. **Relative-Consistency Meta-Theorem (`relative_consistency_meta_theorem` and
   `universal_hTcb_never_contradictory`, lines 483–490):** For any proposition
   `P : Prop`, if `∀ M : TCBModel, AllHold (c.tcb.map (TCBItem.meaningIn M)) →
   P`, instantiating `M := refTCBModel` proves `P` outright in Lean's base
   logic. Setting `P := False` proves
   `¬ (∀ M : TCBModel, AllHold (c.tcb.map (TCBItem.meaningIn M)) → False)`: no
   proof of `CrateTheoremUniversal c` can derive `False` from `hTcb`.
3. **Refutability of UB Crates (`alwaysUbCrate_unprovable_under_universal_tcb`,
   lines 497–516):** Whereas `alwaysUbCrate` was provable under a contradictory
   `hTcb` (Theorem 2.5), `¬ CrateTheoremUniversal alwaysUbCrate` is a theorem
   in Lean's base logic with zero axioms.

### Finding 3: Proof-Gated Compilation and Relational IR Cut Elimination

`Basis: source + execution + derived`

In `Trusted/Refinement.lean:367-370`, cross-language compilation is defined as a
single demonic refinement inequality in the target language's behavior lattice:

```lean
abbrev Compiles (L_src L_tgt : Language)
    (π_c : L_src.Behavior → L_tgt.Behavior)
    (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ π_c (L_src.sem s)
```

When `π_c` is induced by a trusted boundary codec `codec : BoundaryCodec L_src
L_tgt` (`decompileQuery : L_tgt.Query → L_src.Query` and `decompileOut :
L_tgt.Out → L_src.Out`, generalizing `π_stage0` in
`theory/Anneal/Compiler/NaiveCodegen.lean:268-280` and `MirToX86Morphism` in
`Trusted/X86Semantics.lean:865-894`), the developments in
`support/ProofGatedCompilationAndTrustPolicy.lean` (Sections 1–2, lines
218–434) and `support/ProofGatedAndCanarySuite.lean` (Sections 1–2, lines
116–214) establish two foundational properties:

1. **Monotonicity (`BoundaryCodec.monotone_toMorphism`, lines 239–245):**
   `b₁ ≤ b₂ → codec.toMorphism b₁ ≤ codec.toMorphism b₂`.
2. **Definitional Specification Pushforward (`BoundaryCodec.toMorphism_specOn`,
   lines 258–265):**
   ```lean
   theorem BoundaryCodec.toMorphism_specOn {L_src L_tgt : Language}
       (codec : BoundaryCodec L_src L_tgt)
       (pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop) :
       codec.toMorphism (L_src.SpecOn pre post) =
         L_tgt.SpecOn
           (fun q => pre (codec.decompileQuery q))
           (fun q out => post (codec.decompileQuery q) (codec.decompileOut out)) :=
     rfl
   ```
   The right-hand side of `BoundaryCodec.toMorphism_specOn` depends only on
   `L_tgt.SpecOn`, `codec.decompileQuery`, `codec.decompileOut`, `pre`, and
   `post`; it does not reference `L_src.sem`.

Consequently, when a function's verification requires both the source
specification obligation (`MirLang.sem s ≤ MirLang.SpecOn pre post`) and the
pass compilation obligation (`Compiles MirLang X86Lang codec.toMorphism s t`),
labeled `ProofGatedCompiled` in
`support/ProofGatedCompilationAndTrustPolicy.lean:289-294`, the untrusted
intermediate evaluator `MirLang.sem s` is sandwiched between two inequalities:

$$\underbrace{\text{X86Lang.sem } t}_{\text{trusted target}} \;\le\; \varphi(\underbrace{\text{MirLang.sem } s}_{\text{untrusted IR}}) \;\le\; \varphi(\text{MirLang.SpecOn } \text{pre } \text{post}) \;\equiv_{\text{rfl}}\; \underbrace{\text{X86Lang.SpecOn } \text{pre}_{\text{tgt}}\; \text{post}_{\text{tgt}}}_{\text{trusted target spec}}$$

This sandwich makes any untrusted intermediate language in `theory/`
bidirectionally fail-closed and eliminates it from the TCB:

- **Direction 1 — Spurious IR UB is fail-closed
  (`spurious_ir_ub_blocks_source_obligation`, lines 303–317, and
  `spurious_ub_breaks_wellFormedOn` in
  `support/ProofGatedAndCanarySuite.lean:139-147`):**
  If a bug in `MirLang.sem` makes `MirLang.sem s q₀` undefined
  (`¬ (MirLang.sem s q₀).defined`) on any valid query `h_pre : pre q₀`, then
  `MirLang.sem s ≤ MirLang.SpecOn pre post` (and `MirLang.WellFormedOn pre`) is
  uninhabited (`¬ ProofGatedCompiled ...`).
- **Direction 2a — Omitted IR UB is fail-closed
  (`omitted_ir_ub_blocks_pass_obligation`, lines 327–341, and
  `missing_ub_breaks_compiles` in
  `support/ProofGatedAndCanarySuite.lean:155-163`):**
  If a bug in `MirLang.sem` makes `MirLang.sem s (codec.decompileQuery q_tgt)`
  defined on a query where the trusted target machine traps
  (`¬ (X86Lang.sem t q_tgt).defined`), then `Compiles MirLang X86Lang
  codec.toMorphism s t` is uninhabited (`¬ ProofGatedCompiled ...`).
- **Direction 2b — Omitted IR outcome is fail-closed
  (`omitted_ir_outcome_blocks_pass_obligation`, lines 349–367, and
  `missing_outcome_breaks_compiles` in
  `support/ProofGatedAndCanarySuite.lean:170-180`):**
  If `X86Lang.sem t q_tgt` is defined and can produce `out_tgt`, but a bug in
  `MirLang.sem` omits `codec.decompileOut out_tgt` from `(MirLang.sem s
  (codec.decompileQuery q_tgt)).val`, then `Compiles MirLang X86Lang
  codec.toMorphism s t` is uninhabited (`¬ ProofGatedCompiled ...`).
- **Relational Cut Elimination
  (`proof_gated_compilation_eliminates_ir_from_tcb`, lines 375–397,
  `multi_stage_proof_gated_compilation_eliminates_irs_from_tcb`, lines 410–433,
  and `proof_gated_transfers_wellFormedOn` / `proof_gated_transfers_specOn` in
  `support/ProofGatedAndCanarySuite.lean:186-214`):**
  When both obligations hold, `Preorder.le_trans` and
  `BoundaryCodec.monotone_toMorphism` cancel `MirLang.sem` (and any intermediate
  IRs such as `AnSSALang.sem` in a multi-stage pipeline `MirLang → AnSSALang →
  X86Lang`), concluding `X86Lang.sem t ≤ X86Lang.SpecOn ...` and `X86Lang.sem t
  ≤ X86Lang.WellFormedOn ...` directly on the trusted target semantics with zero
  axioms.

However, inspecting `mir-to-x86` (`4f45f0a391a921ced9c9dc773b9a040dbc215d14`)
across `trusted/lean/Trusted/X86Semantics.lean:865-895`,
`trusted/rustc-capture/src/lib.rs:1435-1820`, and
`trusted/audit/TrustedBoundary.lean:207` reveals that `mir-to-x86` does **not**
yet wire this proof-gated compilation sandwich into `Trusted.CrateTheorem`:

- `Trusted.Crate` in `mir-to-x86` (`Trusted/X86Semantics.lean:865-870`) stores
  `CapturedFn` over `X86Body`, not `MirBody`.
- `trusted/rustc-capture/src/lib.rs:1435-1561` lowers `rustc` MIR directly to
  `Trusted.X86Body` in unverified Rust code when emitting `.anneal/Mir.lean`
  (`def crate : Trusted.Crate`), and separately formats `.anneal/Prog.s` via
  `render_x86_assembly` (`trusted/rustc-capture/src/lib.rs:1589-1820`).
- `trusted/audit/TrustedBoundary.lean` in `mir-to-x86` differs from `main` by a
  single line (`line 207`: replacing `` `mir_ast, `mir_semantics `` with
  `` `x86_ast, `x86_semantics ``). It never inspects `.anneal/Prog.s` and never
  requires `Mir.crate` or `Proof.verify_crate` to invoke `Anneal.compileStage0`.
- As proved in `mir_to_x86_unverified_capture_gap`
  (`support/TcbConsistencyAndAuditProbes.lean:603-613`) and confirmed by
  `probe_d1_mir_to_x86_artifact_disconnect` (`preflight=PASS | audit=PASS`), a
  crate whose captured `X86Body` in `Mir.lean` neither equals `compileStage0
  mirBody` nor matches `.anneal/Prog.s` passes both phases of
  `TrustedBoundary.lean`.
- `verified_pipeline_rejects_capture_mismatch`
  (`support/TcbConsistencyAndAuditProbes.lean:637-640`) demonstrates the
  required closure: `Mir.crate` must record the captured `progMir : MirBody`
  alongside `progX86 : X86Body` (`VerifiedCapturedFn`), and
  `Trusted.CrateTheorem` must require `Stage0Compiler.Compiles fn.progMir
  fn.progX86` so the Lean kernel checks that `progX86` refines `progMir`.

### Finding 4: Antecedent Omission Explosion and `ScopedVerificationResult`

`Basis: source + execution + derived`

In `Trusted/Refinement.lean:385-471` and `Trusted/MirSemantics.lean:859-865`,
`VerificationResultOn` places `AllHold (assumptions.map
TrustedAssumption.meaning)` on the left of `→` for all `TrustedAssumption`
items. When fine-grained partial-verification assumptions
(`.assumeSourceWellFormed`, `.assumeSourceSpec`, `.assumePassCompiles`) are
added so a developer can skip proving a work-in-progress function or compiler
pass (`support/ProofGatedAndCanarySuite.lean:219-351`), placing those
concrete-program propositions on the left of `→` introduces a cross-function
and intra-function Principle-of-Explosion vulnerability
(`support/ProofGatedCompilationAndTrustPolicy.lean`, Section 3, lines 435–643):

- Unlike uninterpreted model parameters (`∀ M : TCBModel`), `MirLang.sem` and
  `X86Lang.sem` are **transparent, computable definitions** in Lean.
- Suppose a crate contains two functions:
  1. `"fn_wip"`: an unfinished function (`ConcreteBody.ubAtBoundary`) that
     returns `0` for `arg < 255` but triggers UB (`Partial.ub`) at the boundary
     input `qBoundary` (`arg = 255`). The trust policy
     (`wipOnlyAntecedentPolicy`, lines 547–550) permits assumptions **only** on
     `"fn_wip"` and forbids any assumption on `"fn_critical"`
     (`wipOnlyAntecedentPolicy_forbids_critical`, lines 554–558).
  2. `"fn_critical"`: a safety-critical function (`ConcreteBody.alwaysUb`) that
     triggers UB on every input and claims the impossible postcondition
     `ConcreteMirLang.Spec (fun _ _ => False)`.
- When `[AntecedentOmissionItem.assumeSourceWellFormed "fn_wip" .ubAtBoundary]`
  is placed in `tcb`, its antecedent proposition
  `ConcreteMirLang.sem .ubAtBoundary ≤ ConcreteMirLang.WellFormed` is **provably
  false** (`transparent_buggy_wip_assumption_is_false`, lines 567–572):
  instantiating the universal quantifier at `qBoundary` reduces
  `(ConcreteMirLang.sem .ubAtBoundary qBoundary).defined` to `False` and
  `(ConcreteMirLang.WellFormed qBoundary).defined` to `True`, yielding
  `True → False`.
- Consequently, `global_antecedent_omission_explodes_crate` (lines 602–613)
  proves `CrateTheoremAntecedent wipOnlyAntecedentPolicy
  crateWithBuggyWipAndBuggyCritical` in four lines with **zero axioms**, using
  `False.elim` from `"fn_wip"`'s false antecedent to discharge `"fn_critical"`.
- Scoping antecedent assumptions per-function does not prevent explosion within
  a function: in `intra_function_antecedent_omission_explodes_other_obligations`
  (lines 624–643), omitting a broken compilation pass obligation
  (`.assumePassCompiles "fn_partial" "mir_to_x86" .retZero .ubAtBoundary`) on
  the left of `→` derives `False` at `qBoundary` and proves the false source
  specification `ConcreteMirLang.Spec (fun _ _ => False)` on `.retZero`.

Uninterpreted environment hypotheses and concrete-program proof omissions have
opposite logical polarities and must be separated:

| Concept | Nature of Proposition | Logical Polarity in `CrateTheorem` | Vacancy / Policy Guard |
| :--- | :--- | :--- | :--- |
| **Environment / ISA / ABI Model Hypotheses (`TCBModel`)** | Predicates over universally quantified model parameters `∀ M : Model` (`envAssumptions : Model → List Prop`) | **Negative (Antecedent of `→`):** `∀ M : Model, AllHold (envAssumptions M) → ...` | Constructive realizability witness `∃ M : Model, AllHold (envAssumptions M)` (`refTCBModel_realizes_tcb`) |
| **Concrete-Program Proof Omissions (`ObligationId`)** | Identifiers naming specific concrete obligations (`fnId`, `OmissionKind`) whose proofs are skipped | **Positive (Per-obligation mask on the consequent):** replaces `e.prop` with `True` iff `e.id.inList omitted = true` | Policy gate `AllHold (omitted.map policy.isAllowed)` (`ScopedTrustPolicy.zeroTrust` forces `omitted = []`) |

In `support/ProofGatedCompilationAndTrustPolicy.lean` (Sections 4–5, lines
645–1213), each atomic obligation is tagged with an `ObligationId` (`fnId` and
`OmissionKind`: `.assumeSourceWellFormed`, `.assumeSourceSpec specIdx`, or
`.assumePassCompiles passId`) and gated positively via
`ObligationEntry.requiredProp`:

```lean
def ObligationEntry.requiredProp (omitted : List ObligationId)
    (e : ObligationEntry) : Prop :=
  match e.id.inList omitted with
  | true  => True
  | false => e.prop

def ScopedVerificationResult
    (policy : ScopedTrustPolicy)
    (omitted : List ObligationId)
    (entries : List ObligationEntry) : Prop :=
  AllHold (omitted.map policy.isAllowed) ∧
  AllHold (entries.map (ObligationEntry.requiredProp omitted))
```

This positive per-obligation gating satisfies six zero-axiom theorems:

1. **Zero-Trust Equivalence (`scoped_zeroTrust_forces_empty_omitted` and
   `scoped_zeroTrust_iff_allHold`, lines 776–811, plus
   `strictPolicy_forbids_omitted_proofs` in
   `support/ProofGatedAndCanarySuite.lean:288-307`):** Under
   `ScopedTrustPolicy.zeroTrust` (`allowOmission _ := false`),
   `ScopedVerificationResult .zeroTrust omitted entries` holds iff
   `omitted = []` and `AllHold (entries.map (·.prop))`.
2. **Antitonicity in Omitted Obligations
   (`scoped_verification_antitone_in_omitted`, lines 817–843):** Shrinking the
   set of omitted obligations (`omitted₁ ⊆ omitted₂`) monotonically strengthens
   `ScopedVerificationResult`.
3. **Unomitted Obligation Extraction
   (`unomitted_entry_holds_of_scoped_verification`, lines 851–870):** Every
   entry `e ∈ entries` with `e.id.inList omitted = false` holds unconditionally
   (`e.prop`), regardless of whether other omitted entries in `entries` have
   false propositions.
4. **Universal Cross-Function Isolation (`scoped_omission_isolates_buggy_fn`,
   lines 922–947):** For the same `crateWithBuggyWipAndBuggyCritical` that
   exploded under `CrateTheoremAntecedent`, `¬ CrateTheoremScoped
   wipOnlyScopedPolicy omitted crateWithBuggyWipAndBuggyCritical.functions`
   holds for **every** `omitted : List ObligationId`.
5. **Universal Intra-Function Isolation
   (`scoped_omission_isolates_intra_fn_obligations`, lines 963–994):** Allowing
   and omitting `.assumePassCompiles "mir_to_x86"` on `"fn_partial"`
   (`fnPartialPassOnlyPolicy`) cannot rescue a false source specification
   `.assumeSourceSpec 0` on `"fn_partial"` for any `omitted : List
   ObligationId`.
6. **Multi-Pass Partial-Verification Soundness and `UnifiedCrateTheorem`
   (`pipeline_two_pass_scoped_soundness`, `partially_verified_crate_holds`,
   `extract_verified_fn_from_partially_verified_crate`, and
   `unified_crate_theorem_non_vacuous_and_isolated`, lines 1044–1211):** In a
   2-pass pipeline (`MirLang → AnSSALang → X86Lang`) on a crate
   `[fnWipPipeline, fnVerifiedPipeline]` where `"fn_wip"` has a real UB bug and
   omits its source obligation under `wipOnlyScopedPolicy`, the crate theorem
   holds constructively (`partially_verified_crate_holds`) and still extracts
   the unconditional `ConcreteX86Lang` specification and UB-freedom theorem for
   `"fn_verified"` (`extract_verified_fn_from_partially_verified_crate`).
   `UnifiedCrateTheorem` (lines 1184–1211) combines universally quantified
   `envAssumptions : Model → List Prop` on the left of `→` (backed by a
   realizability witness `M₀`) with `ScopedVerificationResult` on the right of
   `→`.

### Finding 5: `BoundaryCanarySuite` and Guard-Mutation Testing for Target ISA

`Basis: source + execution`

To prevent silent semantic bugs in trusted target language definitions (where
an overly permissive guard hides hardware traps or an overly restrictive guard
introduces vacuity), `support/ProofGatedAndCanarySuite.lean` (Sections 4–6,
lines 353–623) defines the `BoundaryCanarySuite (M : X86MachineModel)`
typeclass. It bundles 11 positive conformance witnesses with 10 negative
refutation theorems across 10 critical x86-64 and CTFE semantic guards:

1. **64-bit modular addition (`canary_pos_add64_wrap`,
   `canary_neg_add64_no_unbounded_nat`):** `(2^64 - 1) + 1` wraps modulo
   $2^{64}$ to `0` (`CF = true, ZF = true`) and does not equal unbounded
   $2^{64}$ (`X86Semantics.lean:212`).
2. **64-bit modular subtraction (`canary_pos_sub64_wrap`,
   `canary_neg_sub64_no_zero_truncation`):** `0 - 1` wraps modulo $2^{64}$ to
   $2^{64} - 1$ (`CF = true, SF = true`) and does not truncate to `0` as in
   `Nat` subtraction (`X86Semantics.lean:213`).
3. **64-bit shift-count masking (`canary_pos_shl64_mask_and_flags`,
   `canary_neg_shift64_no_unmasked_count`):** `shlq(1, 64)` and `shrq(1, 64)`
   mask the shift count by `63` (`64 % 64 = 0`), preserving incoming `RFlags`
   when the masked count is `0` (`X86Semantics.lean:221-222`).
4. **`idivq` divide-by-zero `#DE` trap (`canary_pos_idiv64_normal`,
   `canary_neg_idiv64_div_zero_traps`):** `idivq(42, 7)` yields `(6, 0)` while
   `idivq(42, 0)` is undefined (`¬ defined`).
5. **`idivq` signed-overflow `#DE` trap
   (`canary_neg_idiv64_intmin_overflow_traps`):** `idivq(INT64_MIN, -1)` is
   undefined (`¬ defined`).
6. **Stack-frame slot bounds (`canary_pos_slot_write_in_bounds`,
   `canary_neg_slot_write_out_of_bounds_traps`):** `writeSlot` succeeds when
   `slotIdx < slotCount` and is undefined when `slotIdx ≥ slotCount`
   (`X86Semantics.lean:105-115`).
7. **System V AMD64 16-byte `rsp` alignment at `call`
   (`canary_pos_call_rsp_aligned`, `canary_neg_call_rsp_misaligned_traps`):**
   `call` succeeds when `rsp % 16 == 0` and traps when `rsp % 16 == 8`.
8. **Callee-saved register preservation at `ret`
   (`canary_pos_ret_callee_saved_preserved`,
   `canary_neg_ret_callee_saved_clobbered_traps`):** `ret` traps when exit
   callee-saved registers differ from entry.
9. **`transmute_copy` byte-size equality (`canary_pos_transmute_copy_same_size`,
   `canary_neg_transmute_copy_size_mismatch_traps`):** `transmute_copy` traps
   when `srcSize ≠ dstSize`.
10. **`AdtInv` scalar/discriminant validity (`canary_pos_load_bool_valid`,
    `canary_neg_load_bool_invalid_discriminant_traps`) and CTFE non-vacuity
    (`canary_ctfe_polarity_guards`):** loading a `bool` byte `≥ 2` traps, and
    an unmodeled CTFE instruction (`isModeled = false`) sets
    `constNoUnmodeled = false` (`X86Semantics.lean:547-555`).

In `support/ProofGatedAndCanarySuite.lean:480-512`, `currentX86Model` (matching
`Trusted/X86Semantics.lean` at `4f45f0a391a921ced9c9dc773b9a040dbc215d14`)
provably fails `BoundaryCanarySuite`
(`currentX86Model_fails_BoundaryCanarySuite`), whereas `fixedX86Model` (lines
519–621) instantiates `BoundaryCanarySuite`
(`instBoundaryCanarySuiteFixedX86Model`). Mutating each of the 13 annotated
`-- MUTATE_GUARD:` sites in `fixedX86Model` produces a **13/13 (100.0%)**
mutation kill rate under `lean -DElab.async=false -Ddebug.skipKernelTC=false`:

| Mutant ID | Guard Mutated | Mutation Applied | Failing Canary in `BoundaryCanarySuite` | Kernel Exit Code | Status |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `M01` | `alu_mod64_add` | `(va + vb).toNat` → `a + b` (unbounded `Nat` add, `X86Semantics.lean:212`) | `canary_pos_add64_wrap` / `canary_neg_add64_no_unbounded_nat` | `1` | **KILLED** |
| `M02` | `alu_mod64_sub` | `(va - vb).toNat` → `a - b` (truncating `Nat` sub, `X86Semantics.lean:213`) | `canary_pos_sub64_wrap` / `canary_neg_sub64_no_zero_truncation` | `1` | **KILLED** |
| `M03` | `shift_mask64_check` | `b % 64` → `b` (unmasked `shlq`, `X86Semantics.lean:221`) | `canary_pos_shl64_mask_and_flags` | `1` | **KILLED** |
| `M04` | `shift_mask64_shr_check` | `b % 64` → `b` (unmasked `shrq`, `X86Semantics.lean:222`) | `canary_neg_shift64_no_unmasked_count` | `1` | **KILLED** |
| `M05` | `div_zero_check` | `divisor == 0#64` → `false` | `canary_neg_idiv64_div_zero_traps` | `1` | **KILLED** |
| `M06` | `idiv_overflow_check` | `INT64_MIN / -1` check → `false` | `canary_neg_idiv64_intmin_overflow_traps` | `1` | **KILLED** |
| `M07` | `slot_bounds_check` | `slotIdx < slotCount` → `true` (`X86Semantics.lean:105-115`) | `canary_neg_slot_write_out_of_bounds_traps` | `1` | **KILLED** |
| `M08` | `rsp_align16_check` | `rsp % 16 == 0` → `true` | `canary_neg_call_rsp_misaligned_traps` | `1` | **KILLED** |
| `M09` | `callee_saved_check` | `savedEntry == savedExit` → `true` | `canary_neg_ret_callee_saved_clobbered_traps` | `1` | **KILLED** |
| `M10` | `transmute_size_check` | `srcSz == dstSz` → `true` | `canary_neg_transmute_copy_size_mismatch_traps` | `1` | **KILLED** |
| `M11` | `adt_inv_check` | `byteVal < 2` → `true` | `canary_neg_load_bool_invalid_discriminant_traps` | `1` | **KILLED** |
| `M12` | `ctfe_no_unmodeled_check` | `noUnmodeled := isModeled` → `true` | `canary_ctfe_polarity_guards` | `1` | **KILLED** |
| `M13` | `ctfe_mono_admitted_check` | `monoAdmitted := ...` → `false` | `canary_ctfe_polarity_guards` | `1` | **KILLED** |

### Finding 6: Adversarial `TrustedBoundary.lean` Elaboration and Binder Probes

`Basis: source + execution`

Direct inspection of `trusted/audit/TrustedBoundary.lean` in `main`
(`24367bd1a8c7`, lines 180–340, 830–975), `pr-65` (`76fad1a1befa`, lines
180–520, 1340–1505), and `mir-to-x86` (`4f45f0a391a9`, lines 180–340, 830–975),
combined with execution of all 12 probe cases in `support/run_audit_probes.py`
(recorded in `support/audit_probe_results.json`), yields the following
comparative audit matrix on Lean 4.34.1:

| Probe ID | Attack Vector | `main` (`24367bd1`) | `pr-65` (`76fad1a1`) | `mir-to-x86` (`4f45f0a3`) |
| :--- | :--- | :--- | :--- | :--- |
| `baseline_valid` | Valid `Trusted`, `Anneal`, `Mir`, `Proof` | PF: `PASS` / AU: `PASS` | PF: `PASS` / AU: `PASS` | PF: `PASS` / AU: `PASS` |
| `probe_a1_variable_proof` | `variable (h : False)` auto-bound into `Proof.verify_crate` | PF: `PASS` / AU: `FAIL` (`proofCi.type` is `.forallE`) | PF: `PASS` / AU: `FAIL` (`proofCi.type` is `.forallE`) | PF: `PASS` / AU: `FAIL` (`proofCi.type` is `.forallE`) |
| `probe_a2_variable_implicit_mir` | `variable {h : False}` implicitly bound into `Mir.crate` | PF: `PASS` / AU: `FAIL` (`mirCrateCi.type` is `.forallE`) | PF: `PASS` / AU: `FAIL` (`mirCrateCi.type` is `.forallE`) | PF: `PASS` / AU: `FAIL` (`mirCrateCi.type` is `.forallE`) |
| `probe_a3_variable_unused_proof` | Unused `variable (h : False)` in `Proof.lean` | PF: `PASS` / AU: `PASS` (binder dropped by elaborator) | PF: `PASS` / AU: `PASS` (binder dropped by elaborator) | PF: `PASS` / AU: `PASS` (binder dropped by elaborator) |
| `probe_b1_local_notation` | `local notation` in `Proof.lean` | PF: `FAIL` (`unsupported command ...notation`) | PF: `FAIL` (`unsupported command ...notation`) | PF: `FAIL` (`unsupported command ...notation`) |
| `probe_b2_namespace_trusted_spoof_in_anneal` | `Anneal.lean` opens `namespace Trusted` and defines `Trusted.CrateTheorem` | **PF: `PASS` / AU: `PASS` (BYPASS)** | PF: `PASS` / AU: `FAIL` (`non-Trusted module Anneal cannot declare constant ... in Trusted namespace`) | **PF: `PASS` / AU: `PASS` (BYPASS)** |
| `probe_b3_root_ident_escape` | `Anneal.lean` defines `def _root_.Trusted.CrateTheorem` | **PF: `PASS` / AU: `PASS` (BYPASS)** | PF: `FAIL` (`invalid or reserved declaration name _root_...`) / AU: `FAIL` | **PF: `PASS` / AU: `PASS` (BYPASS)** |
| `probe_c1_universe_poly_verify_crate` | Universe-polymorphic `theorem verify_crate.{u}` (`levelParams = [`u]`) | **PF: `PASS` / AU: `PASS` (BYPASS)** | PF: `PASS` / AU: `FAIL` (`Proof.verify_crate must not have universe parameters`) | **PF: `PASS` / AU: `PASS` (BYPASS)** |
| `probe_c1b_universe_poly_mir_crate` | Universe-polymorphic `def crate.{u} : Trusted.Crate` | PF: `PASS` / AU: `FAIL` (`Mir.crate.{0}` in `proofCi.type`) | PF: `PASS` / AU: `FAIL` (`Mir.crate must not have universe parameters`) | PF: `PASS` / AU: `FAIL` (`Mir.crate.{0}` in `proofCi.type`) |
| `probe_c2_noncomputable_mir_crate_choice` | `noncomputable def crate := (Classical.choice witness).val` in `Mir.lean` | **PF: `PASS` / AU: `PASS` (BYPASS)** | PF: `PASS` / AU: `FAIL` (`unapproved axiom Classical.choice from Init.Prelude`) | **PF: `PASS` / AU: `PASS` (BYPASS)** |
| `probe_c3_abbrev_mir_crate` | `abbrev crate : Trusted.Crate` in `Mir.lean` | PF: `PASS` / AU: `PASS` (`.defnInfo`, `kind == "definition"`) | PF: `PASS` / AU: `PASS` (`.defnInfo`, `kind == "definition"`) | PF: `PASS` / AU: `PASS` (`.defnInfo`, `kind == "definition"`) |
| `probe_d1_mir_to_x86_artifact_disconnect` | `Mir.crate` `X86Body` disconnected from `compileStage0` and `Prog.s` | PF: `PASS` / AU: `PASS` | PF: `PASS` / AU: `PASS` | **PF: `PASS` / AU: `PASS` (GAP)** |

The four probe families behave as follows:

1. **Probes A1–A3 (`variable` Auto-Binding in `Proof.lean` and `Mir.lean`):**
   - In Phase 1 (`preflight`), `` `Lean.Parser.Command.variable `` is permitted
     in `commandKinds` (`main:181`, `pr-65:181`, `mir-to-x86:181`), and
     `inspectCommand` performs only generic term-tree syntax inspection on
     `variable` commands. Thus `variable (h : False)` and
     `variable {h : False}` pass Phase 1 (`preflight`) in all three versions.
   - In Lean 4.34.1, `elabTheorem` auto-includes a `variable` binder only when
     that variable is syntactic-ident-referenced in the theorem's **type** (if
     `h` appears only in the proof body `:= False.elim h`, Lean rejects the
     file with `Unknown identifier h` because `include` is excluded from
     `commandKinds`). By contrast, `elabDef` (`def crate : Trusted.Crate :=
     False.elim h` under `variable {h : False}`) auto-binds `{h : False}` even
     when `h` is referenced only in the definition body (`Probe A2`).
   - In Phase 2 (`audit`), whenever a `variable` binder is auto-bound into
     `Proof.verify_crate` (`Probe A1`) or `Mir.crate` (`Probe A2`), Lean's
     kernel records the binder as an outer `Expr.forallE` on `proofCi.type` or
     `mirCrateCi.type`. Phase 2 checks exact structural `Expr` equality (`==`):
     - `mirCrateCi.type == Expr.const `Trusted.Crate []` (`main:949`,
       `pr-65:1469`)
     - `proofCi.type == Expr.app (Expr.const `Trusted.CrateTheorem [])
       (Expr.const `Mir.crate [])` (`main:957`, `pr-65:1480`)
     Both `Probe A1` and `Probe A2` are therefore rejected in Phase 2 across
     all three versions.
2. **Probes B1–B3 (`notation`, `namespace Trusted`, and `_root_` Spoofing):**
   - `Probe B1` (`local notation`): Rejected in Phase 1 (`preflight`) across
     all three versions because `Lean.Parser.Command.notation` (along with
     `macro`, `syntax`, and `elab`) is absent from `commandKinds` (`line 180`).
   - `Probe B2` (`namespace Trusted` spoofing in `Anneal.lean`) and `Probe B3`
     (`_root_.Trusted.CrateTheorem` spoofing in `Anneal.lean`): In `main`
     (`24367bd1a8c7`) and `mir-to-x86` (`4f45f0a391a9`),
     `verifyAndCollectLocals` (`main:832-873`) only enforces the `Trusted.`
     prefix when `module == `Trusted` (`if isTrustedMod && !(isTrustedNamespace
     ci.name) then fail ...` at `main:850`), never forbidding non-`Trusted`
     modules (`Anneal`, `Mir`, `Proof`) from declaring constants inside
     `Trusted.*`. Moreover, `main:945-958` checks `origin env `Mir.crate ==
     some `Mir` and `origin env `Proof.verify_crate == some `Proof`, but never
     checks `origin env `Trusted.Crate == some `Trusted` or `origin env
     `Trusted.CrateTheorem == some `Trusted`. Consequently, in `main` and
     `mir-to-x86`, both `Probe B2` and `Probe B3` pass Phase 1 and Phase 2.
   - `pr-65` (`76fad1a1befa`) closes both vectors at three independent points:
     1. Phase 1 (`preflight`, `TrustedBoundary.lean:308-313`):
        `validateUserDeclIdent` rejects any declaration identifier containing
        `_root_` (`Probe B3` fails Phase 1).
     2. Phase 2 (`audit`, `TrustedBoundary.lean:1353-1356`):
        `if !isTrustedMod && isTrustedNamespace ci.name then fail s!"non-Trusted
        module {module} cannot declare constant {ci.name} in Trusted namespace"`
        (`Probe B2` and `Probe B3` fail Phase 2).
     3. Phase 2 (`audit`, `TrustedBoundary.lean:1459-1462`):
        `unless trustedLocals.contains `Trusted.Crate` and
        `unless trustedLocals.contains `Trusted.CrateTheorem` verify that both
        envelope constants originate in `Trusted.*`.
3. **Probes C1–C3 (Universe Polymorphism, `noncomputable` `Mir.crate`, and
   `abbrev`):**
   - `Probe C1` (`theorem verify_crate.{u} : Trusted.CrateTheorem Mir.crate`):
     In Lean's kernel, universe parameters on a declaration are stored in
     `ConstantInfo.levelParams : List Name`, not inside `ConstantInfo.type`.
     When `Proof.verify_crate.{u}` does not mention `u` in its proposition type
     (only in its proof term), `proofCi.type` remains structurally identical to
     `Expr.app (Expr.const `Trusted.CrateTheorem []) (Expr.const `Mir.crate
     [])`. Because `main` (`24367bd1a8c7:945-958`) and `mir-to-x86`
     (`4f45f0a391a9:945-958`) omit `proofCi.levelParams.isEmpty`, `Probe C1`
     passes both Phase 1 and Phase 2 in `main` and `mir-to-x86`. `pr-65`
     (`76fad1a1befa:1467-1468, 1477-1478`) checks both
     `mirCrateCi.levelParams.isEmpty` and `proofCi.levelParams.isEmpty`.
   - `Probe C2` (`noncomputable def crate : Trusted.Crate := (Classical.choice
     witness).val`): In `main` (`24367bd1a8c7:959`) and `mir-to-x86`
     (`4f45f0a391a9:959`), Phase 2 runs `closure` only once over all roots with
     the full `axiomPolicy` (`{Classical.choice, Quot.sound, propext}`).
     Because `noncomputable` is allowed in `declModifiers` (`line 277`),
     `Mir.lean` in `main` and `mir-to-x86` can synthesize `Mir.crate`
     nonconstructively using `Classical.choice` (`Probe C2` passes both Phase 1
     and Phase 2). `pr-65` (`76fad1a1befa:1472`) adds `let _ ← closure lookup
     (origin env) #[] #[`Mir.crate]` with an empty axiom allowlist `#[]`,
     rejecting any axiom (including `Classical.choice`, `propext`, and
     `Quot.sound`) in the transitive closure of `Mir.crate`.
   - `Probe C3` (`abbrev crate : Trusted.Crate`): Passes Phase 1 and Phase 2 in
     all three versions because `abbrev` elaborates to `ConstantInfo.defnInfo`
     (`kind == "definition"`) with `hints := ReducibilityHints.abbrev`. In
     Lean's kernel, `ReducibilityHints` only guides unfolding order during
     definitional equality checks and cannot introduce unsoundness; however, if
     `Mir.lean` is intended to permit only `def` (and not `abbrev` or
     `variable`), `inspectFile` in Phase 1 can restrict `Mir.lean` to
     `Lean.Parser.Command.definition` only.
4. **Complete Kernel `ConstantInfo` / `Expr` Closure Conditions:**
   Across `Trusted`, `Anneal`, `Mir`, and `Proof`, Phase 2 (`audit`) closes all
   elaboration, binder, namespace, universe-parameter, and noncomputable-crate
   spoofing vectors in Probes A–C when it enforces:
   1. `trustedLocals.contains `Trusted.Crate` and
      `trustedLocals.contains `Trusted.CrateTheorem`, and for every constant `c`
      in a non-`Trusted` module, `!isTrustedNamespace c.name`;
   2. `origin env `Mir.crate == some `Mir`, `kind mirCrateCi == "definition"`,
      `mirCrateCi.levelParams.isEmpty`, `mirCrateCi.type == Expr.const
      `Trusted.Crate []`, and `closure lookup (origin env) #[] #[`Mir.crate]`
      (zero axioms in `Mir.crate`);
   3. `origin env `Proof.verify_crate == some `Proof`,
      `kind proofCi == "theorem"`, `proofCi.levelParams.isEmpty`, and
      `proofCi.type == Expr.app (Expr.const `Trusted.CrateTheorem [])
      (Expr.const `Mir.crate [])`.
   All three conditions (1)–(3) are enforced in `pr-65`
   (`76fad1a1befa:1353-1356, 1459-1481`).

## Boundaries

- **Scope of Lean 4 Mechanizations (`not examined` for full instruction-set
  duplication):**
  `support/TcbConsistencyAndAuditProbes.lean`,
  `support/ProofGatedCompilationAndTrustPolicy.lean`, and
  `support/ProofGatedAndCanarySuite.lean` mechanize the exact `Partial`,
  `Behavior`, `Language`, `Compiler`, `VerificationResultOn`,
  `SmallStepMachine`, `ReachesPrefix`, and `BehaviorOf` definitions from
  `trusted-core` (`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`) and `mir-to-x86`
  (`4f45f0a391a921ced9c9dc773b9a040dbc215d14`) over minimal representative
  `MirBody`, `ConcreteBody`, and `X86MachineModel` ASTs. They do not duplicate
  the full 867-line `MirSemantics.lean` or 896-line `X86Semantics.lean`
  evaluators.
- **Trust-Boundary Placement of Intermediate Languages (`known not to apply`
  when target compilation is omitted):**
  By `proof_gated_compilation_eliminates_ir_from_tcb` and
  `multi_stage_proof_gated_compilation_eliminates_irs_from_tcb`, intermediate
  IRs (`MirLang`, `AnSSALang`, and compiler passes `NaiveCodegen.lean`,
  `Peephole.lean`) are eliminated from the TCB **only** for functions whose
  source and pass compilation obligations to the trusted target language
  (`X86Lang`) are discharged. If a verification workflow stops at `MirLang`
  without proving compilation to `X86Lang`, or omits `.assumePassCompiles`
  under a non-strict policy, `MirLang` remains in the trusted base for that
  omission.
- **Inter-Procedural Call-Graph Modularity (`not examined`):**
  `ScopedVerificationResult` isolates independent functions in a crate
  (`"fn_wip"` vs. `"fn_critical"`). When a verified caller invokes an omitted
  callee, modular isolation requires verifying the caller against a declared
  specification table (`SpecTable`) rather than unfolding the callee's
  transparent body directly; formalizing `SpecTable`-indexed call rules is
  outside the scope of this package.
- **Host-Side Filesystem and Cargo Manifest Auditing (`not examined`):**
  `support/run_audit_probes.py` exercises `TrustedBoundary.lean` (`preflight`
  and `audit` modes) on compiled `.olean` and `.ir` artifacts using
  `foundation-lock.json` under Lean 4.34.1. Host-side path and manifest checks
  in `trusted/audit/src/lib.rs` are not covered by these `.olean` elaboration
  probes.

## Evidence

### 1. Repository Source Locations Examined

- **`trusted-core` (`e6a0b2da5ec39a4c0cfd22bf323885022837b5dc`):**
  - `trusted/lean/Trusted/Refinement.lean`: lines 51–52 (`Monotone`), 254–285
    (`Partial`, `instPreorderPartial`, `Behavior`), 293–346 (`Language`,
    `SpecOn`, `WellFormedOn`, `Spec`), 345–388 (`Compiler`, `Compiles`,
    `SoundOn`, `Verified`), 385–471 (`TrustedAssumption`, `TrustPolicy`,
    `AllHold`, `VerificationResultOn`).
  - `trusted/lean/Trusted/StepResult.lean`: lines 41–59 (`StepResult`), 67–76
    (`SmallStepMachine`), 85–107 (`ExecQuery`, `ExecOut`), 116–143
    (`ReachesPrefix`), 169–177 (`BehaviorOf`).
  - `trusted/lean/Trusted/MirSemantics.lean`: lines 560–564 (`MonoAdmitted`),
    611–612 (`initMirState`), 656–669 (`MirMachine`, `MirSem`, `MirLang`),
    685–723 (`TargetArtifact`, `opaque rustc`, `opaque TargetSem`,
    `TargetLang`, `opaque π_c`, `RustcCompiler`), 735–755 (`TCBItem`,
    `instTrustedAssumptionTCBItem`, `defaultTrustPolicy`), 826–865
    (`CapturedFn`, `Crate`, `CrateTheorem`).
  - `theory/Anneal/Refinement.lean`: lines 169–286 (`Compiles` reflexivity and
    transitivity, `compiles_preserves_specOn`, `VerificationResultOn`
    weakening).
- **`main` (`24367bd1a8c784f2578535954f9915e24894a56f`):**
  - `trusted/audit/TrustedBoundary.lean`: lines 180–184 (`commandKinds`),
    187–191 (`declarationKinds`), 277 (`declModifiers`), 832–873
    (`verifyAndCollectLocals`), 944–960 (`Mir.crate` and `Proof.verify_crate`
    envelope checks in `audit`).
  - `trusted/lean/Trusted/Attributes.lean`: lines 63–139
    (`expandTrustDeclaration`, `Trusted.candidate`).
  - `trusted/lean/foundation-lock.json`: lines 1–1335.
- **`pr-65` (`76fad1a1befa2e4c038d88c3a1bbbe873acb1322`):**
  - `trusted/audit/TrustedBoundary.lean`: lines 180–184 (`commandKinds`),
    308–313 (`validateUserDeclIdent` rejecting `_root_`), 1353–1356 (forbidding
    non-`Trusted` modules from declaring constants in `Trusted.*`), 1459–1481
    (`trustedLocals.contains`, `levelParams.isEmpty`, `Mir.crate` zero-axiom
    `closure`, and `Proof.verify_crate` type check).
- **`mir-to-x86` (`4f45f0a391a921ced9c9dc773b9a040dbc215d14`):**
  - `trusted/lean/Trusted/X86Semantics.lean`: lines 105–115 (`writeSlot`),
    212–222 (`evalX86BinOp`), 547–555 (CTFE admission), 706–769
    (`TargetArtifact`, `opaque assemble`, `opaque TargetSem`, `opaque π_asm`,
    `AssemblerCompiler`, `TCBItem.assemblerLowering`), 852–895 (`X86Lang`,
    `MirToX86QueryMap`, `MirToX86OutMap`, `MirToX86Morphism`, `CapturedFn`,
    `Crate`, `CrateTheorem`).
  - `theory/Anneal/Compiler/NaiveCodegen.lean`: lines 201–215 (`compileStage0`),
    268–280 (`π_stage0`), 836–871 (`naiveCodegen_compiles`).
  - `theory/Anneal/Compiler/Peephole.lean`: lines 155–205 (`optimizePeephole`,
    `compileOptimized`, `peepholeOptimize_compiles`).
  - `theory/Anneal/MirLemmas.lean`: lines 475–565 (`compileStage0_compiles`,
    `compileOptimized_compiles`).
  - `trusted/rustc-capture/src/lib.rs`: lines 1435–1561 (`render_x86_body`),
    1589–1820 (`render_x86_assembly`).
  - `trusted/audit/TrustedBoundary.lean`: line 207 (1-line diff vs. `main`).

### 2. Preserved Package Support Artifacts

All five support artifacts are preserved in `support/` within this package:

| Path | Lines | SHA-256 Digest | Role |
| :--- | ---: | :--- | :--- |
| `support/TcbConsistencyAndAuditProbes.lean` | `654` | `77fda98aac4ded60252c1938e937b6ee510dbd10e857b7c4ca64935a787dc143` | Standalone Lean 4.34.1 mechanization of `hTcb` vacuity, contradictory `opaque` witnesses, universal `TCBModel` realizability, and the `mir-to-x86` capture gap (10 `#print axioms` checks) |
| `support/ProofGatedCompilationAndTrustPolicy.lean` | `1234` | `577b99d49ad8edd90273df309d98ab707cfa22347c960cf51bdc3fa5b023a040` | Standalone Lean 4.34.1 mechanization of `BoundaryCodec`, proof-gated IR cut elimination, antecedent Principle-of-Explosion counterexamples, `ScopedVerificationResult`, and `UnifiedCrateTheorem` (20 `#print axioms` checks, all 0 axioms) |
| `support/ProofGatedAndCanarySuite.lean` | `635` | `612b9afef16959e9f45c9dd0075ebb277f2dcdeeac3439a00c202ab4fb998e94` | Standalone Lean 4.34.1 mechanization of `BehaviorCodec`, `FineGrainedTCBItem`, `strictPolicy`, `BoundaryCanarySuite`, `currentX86Model` refutation, and `fixedX86Model` conformance (9 `#print axioms` checks) |
| `support/run_audit_probes.py` | `786` | `859c8636697719fee3f0838a18f41c27b4a78b9ac23d789e298f57d9cfa2c2a8` | Configurable Python 3 probe runner executing all 12 `TrustedBoundary.lean` elaboration and binder spoofing cases across `main`, `pr-65`, and `mir-to-x86` |
| `support/audit_probe_results.json` | `29110` | `8bfec96dc980e5bc4d6492a03b0c97fbc55c076a3f1235695ec4ff4e1280f87d` | Complete JSON execution record (`returncode`, `stdout`, `stderr`, `result_json`) for all 12 probe cases across `main`, `pr-65`, and `mir-to-x86` |

### 3. Summary of Mechanized Theorems Across Support `.lean` Files

1. **`support/TcbConsistencyAndAuditProbes.lean` (`Anneal.TcbAuditProbes`):**
   - `pme_rejected_query_mirSem_defined` (`lines 272-277`)
   - `step0_query_mirSem_defined` (`lines 281-287`)
   - `pme_rejected_target_undefined_soundOn_false` (`lines 307-322`,
     `[propext]`)
   - `hidden_opaque_witness_soundOn_false` (`lines 342-350`, `0` axioms)
   - `contradictory_hTcb_proves_ub_crate` (`lines 397-402`, `[propext]`)
   - `refTCBModel_realizes_tcb` (`lines 463-471`, `0` axioms)
   - `relative_consistency_meta_theorem` (`lines 482-486`, `0` axioms)
   - `universal_hTcb_never_contradictory` (`lines 488-490`, `0` axioms)
   - `alwaysUbCrate_unprovable_under_universal_tcb` (`lines 496-516`, `0`
     axioms)
   - `x86_hidden_opaque_witness_soundOn_false` (`lines 571-582`, `0` axioms)
   - `mir_to_x86_unverified_capture_gap` (`lines 603-614`, `0` axioms)
   - `verified_pipeline_rejects_capture_mismatch` (`lines 637-641`, `0` axioms)
2. **`support/ProofGatedCompilationAndTrustPolicy.lean`
   (`Anneal.ProofGatedTrustPolicy`, all 20 theorems `0` axioms):**
   - `BoundaryCodec.monotone_toMorphism` (`lines 239-245`)
   - `BoundaryCodec.toMorphism_specOn` (`lines 258-265`)
   - `spurious_ir_ub_blocks_source_obligation` (`lines 303-317`)
   - `omitted_ir_ub_blocks_pass_obligation` (`lines 327-341`)
   - `omitted_ir_outcome_blocks_pass_obligation` (`lines 349-367`)
   - `proof_gated_compilation_eliminates_ir_from_tcb` (`lines 375-397`)
   - `multi_stage_proof_gated_compilation_eliminates_irs_from_tcb`
     (`lines 410-433`)
   - `transparent_buggy_wip_assumption_is_false` (`lines 567-572`)
   - `global_antecedent_omission_explodes_crate` (`lines 602-613`)
   - `intra_function_antecedent_omission_explodes_other_obligations`
     (`lines 624-643`)
   - `scoped_zeroTrust_forces_empty_omitted` (`lines 776-787`)
   - `scoped_zeroTrust_iff_allHold` (`lines 799-811`)
   - `scoped_verification_antitone_in_omitted` (`lines 817-843`)
   - `unomitted_entry_holds_of_scoped_verification` (`lines 851-870`)
   - `scoped_omission_isolates_buggy_fn` (`lines 922-947`)
   - `scoped_omission_isolates_intra_fn_obligations` (`lines 963-994`)
   - `pipeline_two_pass_scoped_soundness` (`lines 1044-1082`)
   - `partially_verified_crate_holds` (`lines 1132-1151`)
   - `extract_verified_fn_from_partially_verified_crate` (`lines 1159-1175`)
   - `unified_crate_theorem_non_vacuous_and_isolated` (`lines 1201-1211`)
3. **`support/ProofGatedAndCanarySuite.lean`
   (`Anneal.ProofGatedAndCanarySuite`):**
   - `spurious_ub_breaks_wellFormedOn` (`lines 139-147`, `0` axioms)
   - `missing_ub_breaks_compiles` (`lines 155-163`, `0` axioms)
   - `missing_outcome_breaks_compiles` (`lines 170-180`, `0` axioms)
   - `proof_gated_transfers_wellFormedOn` (`lines 186-195`, `0` axioms)
   - `proof_gated_transfers_specOn` (`lines 201-213`, `0` axioms)
   - `strictPolicy_forbids_omitted_proofs` (`lines 288-307`, `0` axioms)
   - `gated_pipeline_soundness` (`lines 334-351`, `0` axioms)
   - `currentX86Model_fails_BoundaryCanarySuite` (`lines 508-512`, `[propext]`)
   - `instBoundaryCanarySuiteFixedX86Model` (`lines 594-621`, `[propext]`)

## Revalidation

Revalidate this package whenever any of the following change:

1. `Trusted/Refinement.lean`, `Trusted/MirSemantics.lean`, or
   `Trusted/X86Semantics.lean` modifies `VerificationResultOn`,
   `Compiler.SoundOn`, `TCBItem`, `opaque rustc` / `assemble` / `TargetSem` /
   `π_c`, or `Trusted.CrateTheorem`.
2. `trusted/audit/TrustedBoundary.lean` modifies `commandKinds`,
   `declarationKinds`, `validateUserDeclIdent`, `verifyAndCollectLocals`, or
   the `Mir.crate` and `Proof.verify_crate` checks in `audit`.
3. `mir-to-x86` updates `trusted/rustc-capture` or `Trusted/X86Semantics.lean`
   to bind `MirBody`, `Anneal.compileStage0`, or `.anneal/Prog.s` inside
   `Trusted.CrateTheorem` and `TrustedBoundary.lean`.
4. The pinned Lean toolchain in `trusted/lean/lean-toolchain` and
   `trusted/lean/foundation-lock.json` is upgraded from
   `leanprover/lean4:v4.34.1`.

To re-verify the three standalone Lean 4.34.1 proof developments directly from
this package:

```bash
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/TcbConsistencyAndAuditProbes.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/ProofGatedCompilationAndTrustPolicy.lean
lean -DElab.async=false -Ddebug.skipKernelTC=false \
  support/ProofGatedAndCanarySuite.lean
```

To re-run the 12-case `TrustedBoundary.lean` elaboration and binder probe suite
against an Anneal checkout:

```bash
python3 support/run_audit_probes.py \
  --sysroot "$HOME/.elan/toolchains/leanprover--lean4---v4.34.1" \
  --anneal-root /path/to/anneal
```
