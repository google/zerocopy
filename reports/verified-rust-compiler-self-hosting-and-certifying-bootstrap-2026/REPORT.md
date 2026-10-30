# Verified Rust Compiler Self-Hosting, Two-Step Equivalence, and Certifying Bootstrap in Anneal

## Summary

Discharging `TCBItem.rustcLowering` in Anneal (`Trusted/MirSemantics.lean`)
requires replacing the opaque `rustc : MirBody → TargetArtifact` assumption with
a verified compiler from `Runtime(PostCleanup)` MIR to a target instruction set
or intermediate representation (`IsaLang` / `HwIsaLang`). Because Anneal's
kernel-environment auditor (`trusted/audit/TrustedBoundary.lean`) replays all
proofs at `trustLevel := 0`, restricts axioms to
`{Classical.choice, Quot.sound, propext}`, and forbids both `Lean.ofReduceBool`
(`native_decide`) and `deriving` clauses, no single compiler implementation
strategy simultaneously optimizes proof ergonomics, Trusted Computing Base (TCB)
size, per-crate Lean kernel WHNF reduction latency, and standalone binary
execution.

Our investigation and end-to-end Lean 4.34.1 mechanizations in
`support/track2_self_hosted_compiler_probe.lean` (7,801 lines) and
`support/round2_track2_probe.lean` (4,586 lines) establish a **staged hybrid
architecture** combining three complementary compilation models and four
semantic extensions:

1. **Architecture A (Core Structural Lowering in Lean 4):** Writing structural
   lowering passes (`lowerMirBody`, `f_spec : MirBody → Option IsaProg`) directly
   in `theory/Anneal/` adds zero TCB items beyond target machine semantics
   (`IsaMachine.toLanguage`) and discharges `CrateTheorem` with an empty TCB
   log (`c.tcb = []`, mechanized in `CrateTheorem_transfers_to_IsaLang`).
   However, executing heavy optimization passes inside the Lean kernel via `rfl`
   without `native_decide` incurs $O(|P|^2\text{--}|P|^3)$ WHNF bytecode
   reduction overhead, while executing a Lean compiler outside the kernel trusts
   Lean's unverified C++ code generator and runtime.
2. **Architecture B (Self-Hosted Rust Subset $K$ via Two-Step Equivalence &
   Stage 1 $\to$ Stage 2 Bootstrap Fixed Point):** A compiler pass or
   certificate checker written in Rust Subset $K$ is captured as
   `compilerMirBody : MirBody`, extracted to a pure Lean function via
   `FunctionalTranslation.lean` (`translatePure (computePlan compilerMirBody)
   compilerMirBody`) by kernel `rfl`, proved to refine `f_spec`
   (`compilerMirBody_two_step_sound`), and compiled by `f_spec` to a target
   hardware binary `compilerIsaProg : IsaProg` (`f_spec_compilerMirBody_eq`).
   Theorem `self_hosted_bootstrap_sound` proves that running `compilerIsaProg`
   on `IsaMachine` hardware is free of undefined behavior and emits only sound
   target programs, while `self_hosted_stage2_reproducibility` proves that
   executing Stage 1 on its own descriptor reproduces the identical Stage 2
   binary (`decodeCompilerOut 6 outWord = some compilerIsaProg`), closing the
   *Reflections on Trusting Trust* loop inside `Trusted.CrateTheorem`.
3. **Architecture C (Untrusted Native Rust Optimizer + Verified $O(|P|)$
   Certificate Checker with Deterministic Fallback):** NP-hard and heuristic
   passes (graph-coloring register allocation, instruction scheduling, global
   value numbering) run at native speed in unverified Rust outside the TCB,
   emitting a candidate program and witness `(cand, cert)`. A verified linear
   validator `checkCert : MirBody → IsaProg → Cert → Bool` validates the witness
   inside the Lean kernel in $O(|P|)$ WHNF steps (or as a standalone Rust Subset
   $K$ binary via `checkerMirBody_two_step_sound` and
   `sliceCheckerMirBody_two_elem_sound`) and falls back to `f_spec` on
   rejection. Theorem `certifyingCompiler_verified` proves `Compiler.Verified`
   for every arbitrary `untrustedOpt : MirBody → IsaProg × Cert` with zero
   hypotheses on the optimizer.
4. **Extended `MirAst` and `FunctionalTranslation` for Slices, ADTs, Loops,
   Post-`#154341` `WithRetag`, Mutual Recursion, and `deriving`-Free `π_isa`:**
   In `support/round2_track2_probe.lean`, we resolve all four semantic gaps
   required to scale Architecture B and Architecture C beyond scalar descriptors:
   - **Immutable slices (`&[usize]`), struct/enum ADTs, and bounded loops:**
     Extends `MirAst` with `MirTy.refSliceUsize`, `MirVal.refSliceLoc loc len`,
     `MirVal.adtVal variant fields`, `PlaceElem` (`.deref`, `.field`, `.index`,
     `.downcast`), `Rvalue.{len, discriminant, aggregate, readPlace}`, and
     `Terminator.assertBoundsCheck`, proving symbolic execution soundness
     (`evalSym_slice_sound`) and verifying a 5-block slice-iterating certificate
     checker (`sliceCheckerMirBody_two_elem_sound`) and multi-variant enum
     checker (`evalSym_enumCert`) by kernel `rfl`.
   - **Post-PR `#154341` `Rvalue::Use(Operand, WithRetag)` lowering to `AnSSA`:**
     Models upstream `rustc` commit `e402c1edf047a23b0cfef40c6097d1caa294050b`
     by lowering `WithRetag::Yes` (`withRetag = true`) to an explicit
     side-effectful instruction `AnSSAStmt.retag` and `WithRetag::No` to a pure
     binding `AnSSAStmt.letCopy`, proving `retag_lowering_compiles`, the
     `!Unpin` / `UnsafePinned` exemption (`unsafePinned_retag_is_pure_copy`),
     post-retag SSA copy propagation (`retag_copy_prop_compiles`), and two
     negative soundness refutations (`duplicate_retag_refutes_compiles` and
     `erase_withRetag_refutes_compiles`).
   - **Fuel-indexed open `CallSpecTable` for mutual recursion:** Splits call
     contracts into a computable guard `hasSpec : FnSymbol → Nat → List MirVal →
     Bool` and relational postcondition `post : FnSymbol → Nat → List MirVal →
     MirVal → Prop`, proving the general step-indexed mutual induction theorem
     `mutual_recursion_callSpec_sound` and verifying mutually recursive
     `isEvenMirBody` / `isOddMirBody` (`is_even_is_odd_mutual_sound`).
   - **Cross-track 64-bit hardware projection $\pi_{\text{isa}}$ without
     `deriving`:** Defines `HwIsaMachine` (`regs : Fin 16 → BitVec 64`, `sp :
     BitVec 64`) and the non-identity projection $\pi_{\text{isa}} :
     \mathsf{MirLang.Behavior} \to \mathsf{HwIsaLang.Behavior}$, proving
     `monotone_π_isa`, `hwAddU64_compiles`, and `lowerMirToHwIsa_compiles` using
     explicit structural boolean equality checkers (`beqMirVal_eq_of_true`,
     `beqHwIsaProg_eq_of_true`) with zero `deriving` clauses.

---

## Applicability

The findings and mechanized proofs in this report govern the design of Anneal's
verified compiler backend, MIR semantics, functional translator, and trust
boundary auditor across the following subjects identified in `REPORT.json`:

| Subject | Revision / Digest | Relationship & Scope |
| :--- | :--- | :--- |
| `joshlf/anneal` | `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0` (skeleton worktree `e75556f5767705404404c0675c6d2d9bcee41d6f`) | Governs `trusted/audit/TrustedBoundary.lean` (lines 1–1014), `trusted/lean/Trusted/{Refinement,StepResult,MirAst,Memory,MirSemantics}.lean`, and `theory/Anneal/{Refinement,StepResult,MirLemmas,FunctionalTranslation}.lean`. |
| `rust-lang/rust` | `8006091eb71ae7d9e9bccb66c6122c9d68af4466` | Upstream `rustc_middle::mir::syntax` definitions for `ProjectionElem` (`Deref`, `Field`, `Index`, `Downcast`), `Rvalue` (`Len`, `Discriminant`, `Aggregate`), and `TerminatorKind::Assert` (`AssertKind::BoundsCheck`). |
| `rust-lang/rust` | `e402c1edf047a23b0cfef40c6097d1caa294050b` (PR `#154341`) | Upstream removal of `StatementKind::Retag` in favor of `Rvalue::Use(Operand, WithRetag)` and `rustc_codegen_ssa::mir::retag` `!Unpin` (`UnsafePinned`) and `MaybeDangling` filtering rules. |
| `rust-lang/rust` | `58cf8f9c35b355199727627d07ae34a4e2846d67` | Baseline `rustc` revision cited by Anneal's `Trusted/MirAst.lean` and `Trusted/MirSemantics.lean` for `Runtime(PostCleanup)` MIR semantics. |
| `rust-lang/reference` | `82da570bafd9efed421bdbae0f8603ede8dd308b` | Normative Rust Reference rules for wide slice reference layout (`src/types/slice.md#L6-L10`) and pointer/reference validity (`src/behavior-considered-undefined.md#L114-L147`). |
| `leanprover/lean4` | `v4.34.1` (`5045d0056413266e57c625dcd7c365b10e377c52`) | Kernel verification engine (`lean -j1 -M1024`) used to check both standalone mechanization probes with zero `sorryAx` and zero `Lean.ofReduceBool`. |
| `support/track2_self_hosted_compiler_probe.lean` | SHA-256 `f35d5e4a3d0c01dbce593ff10b94a4ff4666e0125fdfa88778e268002fe4a1ec` | Round 1 standalone 7,801-line Lean 4.34.1 mechanization of `IsaLang`, `VerifiedIsaCompiler`, `f_spec_sound`, `compilerMirBody_two_step_sound`, `certifyingCompiler_verified`, `checkerMirBody_two_step_sound`, `self_hosted_bootstrap_sound`, and `self_hosted_stage2_reproducibility`. |
| `support/round2_track2_probe.lean` | SHA-256 `11de1875983da8a6e8c3a3705d559d406938ad06fb7ea3b6e9d8cbebfaf136e4` | Round 2 standalone 4,586-line Lean 4.34.1 mechanization of immutable slices, struct/enum ADTs, `evalSym_slice_sound`, `sliceCheckerMirBody_two_elem_sound`, `WithRetag` (`retag_lowering_compiles`, `retag_copy_prop_compiles`, negative refutations), `CallSpecTable` (`mutual_recursion_callSpec_sound`), and `deriving`-free `HwIsaLang` (`monotone_π_isa`, `lowerMirToHwIsa_compiles`). |

---

## Findings

### Finding 1: Architectural Comparison — Compiler-in-Lean-4 (A) vs. Self-Hosted Compiler-in-Rust Subset $K$ (B) vs. Hybrid Certifying Lowering (C)

Basis: `source` + `execution` + `derived`

#### 1.1 The Four Competing Constraints on Anneal's Backend Compiler

In `joshlf/anneal@e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0`,
`trusted/lean/Trusted/MirSemantics.lean:778-872` models target compilation using
three `opaque` declarations and a per-function TCB item:

```lean
opaque rustc : MirBody → TargetArtifact
opaque TargetSem : TargetArtifact → ExecQuery MirState → Partial (ExecOut Unit MirVal → Prop)
opaque π_c : MirLang.Behavior → TargetLang.Behavior
```

Every verified function currently appends `TCBItem.rustcLowering fnName body`
(whose `TrustedAssumption.meaning` is `RustcCompiler.SoundOn body`) to the
crate's TCB assumption list `c.tcb`. Because `Compiler.SoundOn` in
`trusted/lean/Trusted/Refinement.lean:410-412` is defined as:

$$\mathsf{Compiler.SoundOn}(C, s) \;\triangleq\; \mathsf{Monotone}(C.\pi) \;\wedge\; \mathsf{Compiles}(L_{\mathrm{src}}, L_{\mathrm{tgt}}, C.\pi, s, C.\mathrm{compile}(s))$$

where $\mathsf{Compiles}(L_{\mathrm{src}}, L_{\mathrm{tgt}}, \pi_c, s, t)
\triangleq L_{\mathrm{tgt}}.\mathrm{sem}(t) \le \pi_c(L_{\mathrm{src}}.\mathrm{sem}(s))$,
eliminating `TCBItem.rustcLowering` requires supplying a concrete target
language `IsaLang` and a verified compiler whose soundness proof passes
`trusted/audit/TrustedBoundary.lean`.

However, `trusted/audit/TrustedBoundary.lean:38-42, 185-206, 495-520` imposes
strict kernel-level constraints on all declarations in `trusted/lean/` and
`theory/Anneal/`:

1. **Zero theorems in `trusted/lean/`:** Per `Trusted/Refinement.lean:193`,
   `trusted/lean/` states only primitive semantic definitions and `CrateTheorem`.
   All compiler passes, validators, and proofs must live in `theory/Anneal/`.
2. **Forbidden `Lean.ofReduceBool` (`native_decide`):** Phase 1 (`"preflight"`)
   and Phase 2 (`"audit"` at `trustLevel := 0`) restrict the axiom closure of
   every declaration to `{Classical.choice, Quot.sound, propext}`. Any use of
   `native_decide` or `decide +native` introduces `Lean.ofReduceBool` (trusting
   Lean's unverified C++ code generator and native evaluator) and is rejected.
   Consequently, any computation evaluated by `rfl` or `decide` inside a
   per-crate proof runs in the Lean kernel's pure WHNF term reducer.
3. **Closed command allowlist forbidding `deriving`:** Phase 1's syntax checker
   (`TrustedBoundary.lean:185-206`) rejects `deriving` clauses on `inductive`
   and `structure` declarations as well as standalone `deriving instance`
   commands.

| Architectural Dimension | Architecture A: Compiler in Lean 4 (`theory/Anneal/`) | Architecture B: Self-Hosted Compiler in Rust Subset $K$ Verified via Anneal | Architecture C: Untrusted Native Rust Optimizer + Verified Checker (`checkCert`) |
| :--- | :--- | :--- | :--- |
| **TCB Impact (`trusted/`)** | **Zero new compiler TCB**: only target `IsaLang` / `HwIsaLang` semantics belong in `trusted/lean/`. Compiler passes and proofs live in `theory/Anneal/`. | **Zero compiler TCB**: requires `MirAst` support for slices and ADTs (`round2_track2_probe.lean` §1) plus target `IsaLang` semantics in `trusted/lean/`. | **Zero optimizer TCB**: only target `IsaLang` semantics live in `trusted/lean/`. `checkCert`, fallback `f_spec`, and `checkCert_sound` live in `theory/Anneal/`; the Rust optimizer is completely untrusted. |
| **Proof Ergonomics** | **Highest for structural passes**: direct structural induction over inductive ASTs (`MirBody`, `BasicBlock`, `Stmt`) without intermediate operational encoding. | **High for bounded passes & validators**: Two-Step Equivalence (`translatePure` by `rfl` + pure refinement proof) decouples host MIR stepping from target semantics (`compilerMirBody_two_step_sound`). | **Highest for global/NP-hard passes**: eliminates correctness proofs for graph-coloring register allocation, coalescing, and scheduling; only the linear boolean validator `checkCert_sound` and fallback `f_spec_sound` require proof. |
| **Per-Crate Kernel WHNF Cost (`TrustedBoundary.lean`)** | **$O(|P|)$ for simple lowering, $O(|P|^2\text{--}|P|^3)$ for heavy passes**: complex analyses reduced by `rfl` in the kernel without `native_decide` bottleneck per-crate verification. | **$O(\text{steps}(\text{pass}))$ symbolic WHNF reduction**: `evalSym` / `translatePure` unfolds symbolic execution in the kernel once for the pass, or runs at hardware speed once bootstrapped. | **$O(|P|)$ linear certificate validation**: the untrusted Rust optimizer runs at native speed outside Lean, embeds `(cand, cert)` into the proof module, and the Lean kernel reduces only `checkCert body cand cert = true` in $O(|P|)$ steps. |
| **Executable & Bootstrap Endpoint** | **Requires external codegen or secondary bootstrap**: running a Lean compiler outside the kernel relies on Lean's unverified C++ compiler/runtime (~50k+ LOC). | **Closed self-hosted bootstrap (`self_hosted_bootstrap_sound`)**: `f_spec` compiles `compilerMirBody` to `compilerIsaProg : IsaProg`, proving hardware soundness and Stage 1 = Stage 2 reproducibility (`self_hosted_stage2_reproducibility`). | **Dual-use endpoint**: during per-crate kernel auditing, `checkCert` runs inside the Lean kernel (`trustLevel := 0`). For standalone CLI checking, `checkCert` is implemented in Rust Subset $K$ (`checkerMirBody` / `sliceCheckerMirBody`) and bootstrapped via Architecture B. |

#### 1.2 Discharging `TCBItem.rustcLowering` and Reconciling Partial vs. Total Compilation

In `support/track2_self_hosted_compiler_probe.lean:6558-6987`, we mechanize both
partial resource-bounded compilation (`f_spec : MirBody → Option IsaProg`) and
total `Trusted.Compiler` composition (`VerifiedIsaCompiler : Compiler MirLang
IsaLang`):

- **Partial Compilation with Hardware Resource Bounds (`f_spec_sound`, lines
  6909–6942):** Real target architectures reject functions that exceed physical
  limits (such as frame/register capacity or branch displacement). We define
  `checkIsaFits (body : MirBody) : Bool := !body.blocks.isEmpty && decide
  (body.localCount ≤ 64)` and `f_spec body := if checkIsaFits body then some
  (lowerMirBody body) else none`. Theorem `f_spec_sound` proves that whenever
  `f_spec body = some prog`:
  $$\mathsf{Compiles}(\mathsf{MirLang}, \mathsf{IsaLang}, \pi_{\mathrm{isa}}, \mathit{body}, \mathit{prog}) \;\wedge\; \mathit{prog}.\mathsf{localCount} \le 64 \;\wedge\; \mathit{prog}.\mathsf{blocks} \neq []$$
- **Zero-TCB `CrateTheorem` Transfer (`CrateTheorem_transfers_to_IsaLang`, lines
  6945–6987):** Packaging `lowerMirBody` into `VerifiedIsaCompiler : Compiler
  MirLang IsaLang` yields `VerifiedIsaCompiler_soundOn (body : MirBody) :
  VerifiedIsaCompiler.SoundOn body` and `VerifiedIsaCompiler_verified`, allowing
  `Compiler.SoundOn.verify` (`theory/Anneal/Refinement.lean:212-218`) to
  transfer any source-verified crate `c` (`c.tcb = []`) to `IsaCrateTheorem c`
  with **zero TCB assumptions**.

#### 1.3 Two-Step Equivalence for Self-Hosted Rust Subset $K$ Compiler Passes (`compilerMirBody_two_step_sound`)

Proving target semantic preservation (`Compiles MirLang IsaLang π_isa srcBody
outProg`) directly over the small-step operational semantics of a compiler
written in Rust (`ReachesPrefix MirMachine compilerMirBody ...`) entangles host
MIR operational stepping (local slot updates, basic-block jumps, overflow
assertions) with target ISA simulation.

**Two-Step Equivalence** (`support/track2_self_hosted_compiler_probe.lean:6990-7294`)
factors this proof into two independent stages across `FunctionalTranslation`:

```text
  Concrete Host MIR Execution of Rust Compiler Pass (`compilerMirBody`)
  ReachesPrefix MirMachine compilerMirBody q.init q.steps q.init tr (.terminated (.normal outVal))
        │
        │  Step 1: Universal Soundness of Functional Translation (`translate_sound`)
        │          + Kernel `rfl` Symbolic Specialization (`translatePure_compilerMirBody_rfl`)
        ▼
  Extracted Pure Functional Pass in Lean 4 (`pureCompilerPass`)
  outVal = .usize (pureCompilerPass regCount imm)
        │
        │  Step 2: Pure Refinement of Verified Specification (`pureCompilerPass_refines_f_spec`)
        │          + Specification Soundness (`f_spec_sound`)
        ▼
  Target ISA Semantic Refinement & Hardware Resource Compliance
  f_spec (decodeMirDesc regCount imm) = some isaProg  ∧
  Compiles MirLang IsaLang π_isa (decodeMirDesc regCount imm) isaProg  ∧
  isaProg.localCount ≤ 64  ∧  isaProg.blocks ≠ []
```

Specifically, for the 6-block branching pass `compilerMirBody` (lines
7017–7045):
1. **Step 1 (`translatePure_compilerMirBody_rfl` &
   `compilerMirBody_satisfies_ensures`, lines 7111–7225):** Specializing
   `translatePure (computePlan compilerMirBody) compilerMirBody [.usize
   regCount, .usize imm]` reduces by kernel `rfl` to nested `zipAeneasRes`
   branches. Discharging the checked-addition bound (`imm ≤ 1000 → imm + 1 ≤
   1001 ≤ usizeMax`) equates the symbolic output to `.ok (.usize
   (pureCompilerPass regCount imm))`. Composing with `translate_sound` yields
   `MirLang.sem compilerMirBody ≤ EnsuresCompilerMirBody`.
2. **Step 2 (`pureCompilerPass_refines_f_spec` &
   `compilerMirBody_two_step_sound`, lines 7239–7294):** Critically, the output
   decoder `decodeCompilerOut` performs **no** bounds validation (`0 ↦ none`,
   `imm + 1 ↦ some (lowerMirBody (decodeMirDesc regCount imm))`). Instead,
   `pureCompilerPass_refines_f_spec` extracts the branch guards enforced by
   `compilerMirBody` itself (`decide (regCount ≤ 64) = true` and `decide (imm ≤
   1000) = true`) to establish `checkIsaFits (decodeMirDesc regCount imm) =
   true`, proving `f_spec (decodeMirDesc regCount imm) = some isaProg` and
   `Compiles MirLang IsaLang π_isa (decodeMirDesc regCount imm) isaProg`.

#### 1.4 Hybrid Certifying Compilation (`certifyingCompiler_verified`) and Verified Rust Checkers (`checkerMirBody`)

In `support/track2_self_hosted_compiler_probe.lean:7296-7659`, we mechanize
Architecture C (`checkCert`, `certifyingCompileOpt`, `certifyingCompiler`, and
`checkerMirBody`):

- **Unconditional Optimizer Freedom (`certifyingCompiler_verified`, lines
  7407–7445):** Given any untrusted external optimizer `untrustedOpt : MirBody →
  IsaProg × Cert`, `certifyingCompiler untrustedOpt` inspects `let (cand, cert)
  := untrustedOpt body`: if `checkCert body cand cert = true`, it emits `cand`;
  otherwise it falls back deterministically to `VerifiedIsaCompiler.compile
  body` (`lowerMirBody body`). Theorem `certifyingCompiler_verified` proves that
  for **every** `untrustedOpt` (with zero preconditions on `untrustedOpt`),
  `MirLang.sem body ≤ spec → (certifyingCompiler untrustedOpt).Verified body
  spec`.
- **Two-Step Equivalence for a Rust Subset $K$ Certificate Checker
  (`checkerMirBody_two_step_sound`, lines 7458–7659):** We also implement the
  certificate validator itself as a 7-block Rust MIR body `checkerMirBody` taking
  `(regCount, imm, candWord)` and prove via `translatePure_checkerMirBody_rfl`
  and `checkerMirBody_two_step_sound` that whenever a concrete execution of
  `checkerMirBody` returns `.normal (.bool true)`, the candidate word `candWord`
  decodes to `some isaProg` satisfying `f_spec (decodeMirDesc regCount imm) =
  some isaProg` and `Compiles MirLang IsaLang π_isa (decodeMirDesc regCount imm)
  isaProg`.

---

### Finding 2: Stage 1 $\to$ Stage 2 Self-Hosted Bootstrap Fixed Point and Reflections on Trusting Trust

Basis: `execution` + `derived`

In Section 4 of `support/track2_self_hosted_compiler_probe.lean:7654-7770`, we
close the self-hosting loop by applying `f_spec` to `compilerMirBody` itself and
proving both hardware-level bootstrap soundness and Stage 1 $\to$ Stage 2 binary
reproducibility:

1. **Self-Compilation by Kernel `rfl` (`f_spec_compilerMirBody_eq`, line 7686):**
   Defining the Stage 1 target machine binary `compilerIsaProg : IsaProg :=
   lowerMirBody compilerMirBody`, the Lean 4 kernel verifies by pure `rfl` that
   `compilerMirBody` satisfies all hardware resource constraints (`localCount =
   6 ≤ 64`, `blocks.length = 6 ≠ 0`) and compiles to `compilerIsaProg`:
   ```lean
   theorem f_spec_compilerMirBody_eq :
       f_spec compilerMirBody = some compilerIsaProg := rfl
   ```
2. **End-to-End Hardware Bootstrap Soundness (`self_hosted_bootstrap_sound`,
   lines 7716–7738):** Proves the four-part bootstrap theorem connecting host
   MIR verification (`CrateTheorem`) to target `IsaMachine` hardware execution:
   - `f_spec compilerMirBody = some compilerIsaProg`,
   - `Compiles MirLang IsaLang π_isa compilerMirBody compilerIsaProg`,
   - `IsaLang.sem compilerIsaProg ≤ IsaLang.WellFormed` (every execution of the
     compiled compiler binary `compilerIsaProg` on `IsaMachine` hardware is free
     of undefined behavior and stuck states at all step budgets), and
   - For every hardware execution `ReachesPrefix IsaMachine compilerIsaProg
     q.init q.steps q.init tr (.terminated (.normal (.usize outWord)))` starting
     from an initial hardware state encoding `(regCount, imm)`, whenever
     `decodeCompilerOut regCount outWord = some isaOut`, the hardware-produced
     program `isaOut` satisfies `f_spec (decodeMirDesc regCount imm) = some
     isaOut` and `Compiles MirLang IsaLang π_isa (decodeMirDesc regCount imm)
     isaOut`.
3. **Stage 1 $\to$ Stage 2 Binary Fixed Point
   (`self_hosted_stage2_reproducibility`, lines 7748–7765):** Because
   `compilerMirBody` has `localCount = 6`, feeding `compilerMirBody`'s own
   source descriptor `(regCount := 6, imm := 1000)` (`compilerMirBody_self_descriptor_rfl :
   (decodeMirDesc 6 1000).localCount = compilerMirBody.localCount`) into the
   Stage 1 hardware binary `compilerIsaProg` running on `IsaMachine` guarantees
   that every normal hardware termination `.normal (.usize outWord)` decodes to
   the exact Stage 2 binary `compilerIsaProg`:
   ```lean
   theorem self_hosted_stage2_reproducibility
       (q : ExecQuery MirState) (tr : List Unit) (outWord : Nat)
       (h_args : q.init.locals 1 = some (.usize 6) ∧
                 q.init.locals 2 = some (.usize 1000))
       (h_init : initIsaState compilerIsaProg q.init)
       (h_exec : ReachesPrefix IsaMachine compilerIsaProg q.init q.steps
                   q.init tr (.terminated (.normal (.usize outWord)))) :
       ∃ stage2Prog : IsaProg,
         decodeCompilerOut 6 outWord = some stage2Prog ∧
         stage2Prog.localCount = compilerIsaProg.localCount ∧
         f_spec (decodeMirDesc 6 1000) = some stage2Prog ∧
         Compiles MirLang IsaLang π_isa (decodeMirDesc 6 1000) stage2Prog
   ```
4. **How `Trusted.CrateTheorem` Neutralizes Thompson's *Reflections on Trusting
   Trust* Attack:** In a conventional self-hosted bootstrap, even Diverse
   Double-Compiling (DDC) requires trusting that at least one reference compiler
   is independent, and a trojaned Stage 1 binary only needs to emit a trojaned
   Stage 2 binary on the compiler's own source. In Anneal, the primary artifact
   of compilation is not an unverified binary, but a machine-checked Lean 4
   proof of `Trusted.CrateTheorem` (audited at `trustLevel := 0` by
   `TrustedBoundary.lean`). Even if an untrusted host binary produces `cand :
   IsaProg` and `cert : Cert`, `certifyingCompiler_verified` checks
   `checkCert compilerMirBody cand cert = true` inside the Lean 4 kernel against
   the explicit source AST `compilerMirBody`, ensuring that `cand` refines
   `MirLang.sem compilerMirBody` before Stage 1 is ever executed.

---

### Finding 3: Extending `MirAst` and `FunctionalTranslation` with Immutable Slices (`&[usize]`), Struct/Enum ADTs, and Bounded Loops

Basis: `normative` + `source` + `execution`

#### 3.1 `rustc` MIR and Rust Reference Correspondence for Slices and ADTs

Round 1's `checkerMirBody` packed a 2-instruction candidate program into a
single `usize` word because `Trusted/MirAst.lean` at
`e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0` lacked slice types, projections, and
algebraic data types. In Section 1 of
`support/round2_track2_probe.lean:550-1410`, we extend `MirAst`, `MemState`, and
`MirSemantics` with exact primary-source correspondence to `rust-lang/rust`
commit `8006091eb71ae7d9e9bccb66c6122c9d68af4466` and `rust-lang/reference`
commit `82da570bafd9efed421bdbae0f8603ede8dd308b`:

- **Wide Slice References (`MirTy.refSliceUsize` and
  `MirVal.refSliceLoc loc len`, lines 588–628):** Per the Rust Reference
  (`src/types/slice.md#L6-L10`), a slice reference `&[T]` is a two-word wide
  pointer comprising a data pointer and an element length. `MemState` adds
  `naSlice : Nat → Option (List Nat)` (`round2_track2_probe.lean:990-1018`), and
  `MirVal.hasTyInMem` requires that `MirVal.refSliceLoc loc len` points to an
  allocated slice `elems` with `elems.length = len`.
- **Struct and Enum Algebraic Data Types (`MirTy.adt adtId` and
  `MirVal.adtVal variant fields`, lines 604–628):** Represents both single-variant
  `struct` / tuple values (`variant = 0`) and multi-variant `enum` values
  (`variant = v`) with scalar payload fields `fields : List ScalarVal`.
- **Projections (`PlaceElem` and `evalReadPlace`, lines 674–691, 1120–1155):**
  Matches `rustc_middle::mir::syntax::ProjectionElem` (`syntax.rs#L1163-L1283`):
  - `[.deref]` reads a shared scalar reference (`MirVal.refSharedLoc loc`).
  - `[.deref, .index idxLocal]` models Rust slice indexing `slice[idx]`: as
    documented in `syntax.rs#L1163-L1228`, `Runtime(PostCleanup)` MIR represents
    slice indexing as a dereference of the wide slice pointer followed by
    `ProjectionElem::Index(idxLocal)`. If `idxVal ≥ len` or the slice allocation
    is missing, `evalReadPlace` returns `none` (immediate undefined behavior).
  - `[.field idx]` projects field `idx` from a struct (`variant = 0`).
  - `[.downcast v, .field idx]` projects field `idx` from enum variant `v`
    (`ProjectionElem::Downcast` followed by `ProjectionElem::Field`), returning
    `none` (undefined behavior) if the runtime value's variant is not `v`.
- **Rvalues and Bounds-Check Terminators (`Rvalue` and `Terminator`, lines
  763–808, 1159–1377):**
  - `Rvalue.len src` extracts `len` from `MirVal.refSliceLoc loc len`
    (`UnOp::PtrMetadata` / `Rvalue::Len`, `syntax.rs#L1616-L1628`).
  - `Rvalue.discriminant src` reads `.usize variant` from `MirVal.adtVal variant
    fields` (`Rvalue::Discriminant`, `syntax.rs#L1458-L1471`).
  - `Rvalue.aggregate variant fields` evaluates `fields : List Operand`
    left-to-right and constructs `MirVal.adtVal variant svs`
    (`Rvalue::Aggregate`, `syntax.rs#L1473-L1501`).
  - `Terminator.assertBoundsCheck idx len target` models
    `TerminatorKind::Assert` with `AssertKind::BoundsCheck { len, index }`
    (`syntax.rs#L990-L1085`): when `idx < len`, execution steps to `target`;
    when `idx ≥ len`, execution terminates cleanly via `.terminated .unwind`
    (panic) rather than `.failed .ub`.

#### 3.2 Symbolic Execution Soundness for Slices, ADTs, and Loops (`evalSym_slice_sound`)

In Section 2 of `support/round2_track2_probe.lean:1430-2840`, we extend `SymVal`
with `.refSlice (elems : List Nat)` and `.adtVal (variant : Nat) (fields : List
ScalarVal)` and link concrete heap state to symbolic values via
`SymValMatchesInMem mem`:

```lean
def SymValMatchesInMem (mem : MemState) : MirVal → SymVal → Prop
  | .usize n, .usize m => n = m
  | .bool b₁, .bool b₂ => b₁ = b₂
  | .unit, .unit => True
  | .tupleUsizeBool n₁ b₁, .tupleUsizeBool n₂ b₂ => n₁ = n₂ ∧ b₁ = b₂
  | .refSharedLoc loc, .refShared n => mem.naLoc loc = some n
  | .refSliceLoc loc len, .refSlice elems =>
      mem.naSlice loc = some elems ∧ len = elems.length
  | .adtVal v₁ fs₁, .adtVal v₂ fs₂ => v₁ = v₂ ∧ fs₁ = fs₂
  | _, _ => False
```

We prove the universal step-indexed simulation theorem `evalSym_slice_sound`
(`support/round2_track2_probe.lean:2514-2663`): for any fuel budget `fuel :
Nat`, `body : MirBody`, basic block `bb`, symbolic environment `env : SymEnv`,
and return summary `retSym : SymVal`, if `evalSym fuel body bb env = some
(.normal retSym)` and `EnvMatches st env` holds at `st.pc = ⟨bb⟩`, then every
concrete `MirMachine` execution prefix `ReachesPrefix MirMachine body init steps
st tr out` is safe (`out.isSafe`, never reaching `.failed .ub`) and every
termination is a normal return matching `retSym` (`term = .normal retVal ∧
SymValMatches retVal retSym`).

#### 3.3 Multi-Instruction Slice-Iterating Certificate Checker (`sliceCheckerMirBody`)

Using `evalSym_slice_sound`, we mechanize `sliceCheckerMirBody`
(`support/round2_track2_probe.lean:2671-2798`), a 5-block loop CFG (`bb0 → bb1 →
bb2 → bb3 → bb1`, exiting to `bb4`) that takes an instruction slice `_1 :
&[usize]` and expected hash `_2 : usize`:

- **`bb0` (initialization):** Evaluates `_3 = Len(_1)`, `_4 = 0` (loop index),
  and `_5 = 0` (accumulator), then jumps to loop header `bb1`.
- **`bb1` (loop header):** Evaluates `_6 = (_4 < _3)` and branches via
  `switchInt` to `bb2` (in-loop) or `bb4` (exit).
- **`bb2` (compiler bounds check):** Executes `assertBoundsCheck(_4, _3) → bb3`.
- **`bb3` (loop body with slice indexing and ADT projection):** Reads element
  `_7 = (*_1)[_4]` via projection `[.deref, .index ⟨4⟩]`, packs a 2-field
  `StepFrame` struct `_8 = Aggregate(0, [_7, _5])`, projects `_9 = _8.0` and
  `_10 = _8.1`, updates `_5 = _10 ^ _9` and `_4 = _4 + 1` (checked addition),
  and jumps back to `bb1`.
- **`bb4` (return):** Evaluates `_0 = (_5 == _2)` and returns.

Because `evalSym` is purely structural, symbolic evaluation over universally
quantified 0-, 1-, 2-, and 3-element instruction slices reduces by kernel `rfl`
(`evalSym_sliceChecker_nil`, `evalSym_sliceChecker_one`,
`evalSym_sliceChecker_two`, `evalSym_sliceChecker_three`, lines 2718–2745), and
composing `evalSym_sliceChecker_two` with `evalSym_slice_sound` yields the
operational soundness theorem `sliceCheckerMirBody_two_elem_sound` (lines
2749–2798) with zero `Lean.ofReduceBool`. Similarly, `enumCertMirBody` and
`evalSym_enumCert` (lines 2805–2840) verify multi-variant enum construction,
`Rvalue.discriminant` switching, and `[.downcast 1, .field 0]` projection by
kernel `rfl`.

---

### Finding 4: Post-PR `#154341` `Rvalue::Use(Operand, WithRetag)` Semantics in `MirAst` and `AnSSA`

Basis: `source` + `execution` + `derived`

#### 4.1 Upstream `rustc` PR `#154341` Correspondence

In upstream `rust-lang/rust` commit `e402c1edf047a23b0cfef40c6097d1caa294050b`
(PR `#154341`, *Merge Retag statement into Use rvalue*), standalone
`StatementKind::Retag` was removed from `compiler/rustc_middle/src/mir/syntax.rs`
(`#L430-L503`) and merged into `Rvalue::Use(Operand<'tcx>, WithRetag)`
(`syntax.rs#L1365`):

- `WithRetag::No` (`withRetag = false`) is a pure value copy or move.
- `WithRetag::Yes` (`withRetag = true`) is emitted by `AddRetag` (`-Zmir-emit-retag`)
  at reference assignments and function-entry parameter initialization to
  assign fresh Stacked Borrows / Tree Borrows tags to reference and `Box` fields
  inside the copied value.
- Crucially, as implemented in `compiler/rustc_codegen_ssa/src/mir/retag.rs#L25-L240`
  (specifically `retag.rs#L78-L115`), `WithRetag::Yes` walks the type's fields
  and **skips** pointers wrapped in `MaybeDangling` or pointers to `!Unpin`
  types (`UnsafePinned` / interior-mutable pinned data) where unique retagging
  would invalidate aliased pointers.

#### 4.2 Why `AnSSA` Must Split `Rvalue::Use` into `AnSSAStmt.retag` and `AnSSAStmt.letCopy`

When lowering `MirAst` to an SSA intermediate representation (`AnSSA`), treating
`Rvalue::Use(op, WithRetag)` uniformly as either a pure SSA expression or an
erased no-op is unsound under borrow-tracker semantics (`BorrowState` in
`support/round2_track2_probe.lean:2873-3620`):

| Lowering Strategy / Optimization | Mechanized Theorem (`round2_track2_probe.lean`) | Semantic Outcome |
| :--- | :--- | :--- |
| **Split lowering (`lowerMirRetagStmt`):** `withRetag = true` $\mapsto$ `AnSSAStmt.retag dst src`; `withRetag = false` $\mapsto$ `AnSSAStmt.letCopy dst src` | `retag_lowering_compiles` (line 3159) | **Sound (`Compiles MirRetagLang AnSSABorrowLang id`):** Exact lockstep equivalence (`reachesPrefix_anSSA_iff_mirRetag`). |
| **`!Unpin` / `UnsafePinned` retag exemption:** `performRetag` on `.ptr addr tag .unsafePinned` | `unsafePinned_retag_is_pure_copy` (line 3171) | **Sound (`rfl`):** `AnSSAStmt.retag` on an `UnsafePinned` pointer is definitionally equal to `AnSSAStmt.letCopy`, preserving existing borrow tags and stacks. |
| **Post-retag SSA copy propagation:** `_2 = retag _1; _3 = letCopy _2; write *_2; read *_3` $\mapsto$ `_2 = retag _1; _3 = letCopy _2; write *_2; read *_2` | `retag_copy_prop_compiles` (line 3609) | **Sound (`Compiles AnSSABorrowLang AnSSABorrowLang id`):** Because `_3 = letCopy _2` (`WithRetag::No`) does not allocate a new tag, `_2` and `_3` share the same active tag (`CopyPropInv`), so substituting `_2` for `_3` preserves all behaviors. |
| **Unsound optimization 1 — Duplicating `retag` as if pure:** Replacing `_3 = letCopy _2` with `_3 = retag _2` (`duplicatedRetagProg`) | `duplicate_retag_refutes_compiles` (line 3237) | **Unsound (`¬ Compiles`):** The second `.retag` allocates a fresh exclusive tag `2` for `_3` that pops `_2`'s exclusive tag `1` from the borrow stack, causing the subsequent `writePtr 2 42` to fail with `.failed .ub`. |
| **Unsound optimization 2 — Erasing `withRetag = true`:** Lowering `_2 = assignUse 2 1 true` to `_2 = letCopy 2 1` (`erasedRetagProg`) | `erase_withRetag_refutes_compiles` (line 3324) | **Unsound (`¬ Compiles`):** When `_1` holds a stale tag `99` not present in the active borrow stack (`staleTagBorrowState`), true `retag` activates a fresh tag `1` and succeeds, whereas erasing `retag` leaves `_2` with stale tag `99` and fails with `.failed .ub`. |

---

### Finding 5: Fuel-Indexed Open `CallSpecTable` for Mutually Recursive Functions

Basis: `source` + `execution` + `derived`

#### 5.1 Constructive Domain-and-Relation Split (`hasSpec` + `post`)

In Round 1 (`Trusted/MirAst.lean:180-220, 8071-8314`), interprocedural calls
were restricted to `Terminator.callPure2 (callee : PureCallee2)`, a closed
inductive enumeration of two-argument `usize` functions. Supporting general
interprocedural calls and mutual recursion in `Trusted/MirSemantics.lean`
without pulling `Classical.propDecidable` or `Classical.choice` into the
executable step function `execTerminator` requires separating the decidable call
precondition from the relational postcondition.

In Section 4 of `support/round2_track2_probe.lean:826-830, 1281-1377, 3622-4172`,
we define `CallSpecTable`:

```lean
structure CallSpecTable where
  hasSpec : FnSymbol → Nat → List MirVal → Bool := fun _ _ _ => false
  post : FnSymbol → Nat → List MirVal → MirVal → Prop := fun _ _ _ _ => False
```

When `execTerminator` evaluates `Terminator.callFn callee args dest target` in
state `s` with `s.callFuel = fuel + 1`:
1. It evaluates `args` left-to-right to `argVals : List MirVal` in state `s'`.
2. It checks the boolean guard `body.callSpecs.hasSpec callee s'.callFuel
   argVals`: if `false`, it returns `.failed .ub` (unverified or out-of-domain
   call).
3. If `true`, it transitions via `.choice .demonic` over the set of next states:
   $$\left\{\, s_{\mathrm{next}} \;\middle|\; \exists \mathit{ret} : \mathsf{MirVal},\; \mathit{body}.\mathsf{callSpecs}.\mathsf{post}(\mathit{callee}, s'.\mathsf{callFuel}, \mathit{argVals}, \mathit{ret}) \;\wedge\; s_{\mathrm{next}} = (s'.\mathsf{writeLocal}(\mathit{dest}, \mathsf{some}\;\mathit{ret}))[\mathsf{pc} \mapsto \mathit{target}, \mathsf{callFuel} \mapsto \mathit{fuel}] \,\right\}$$
   And if `s'.callFuel = 0`, it halts safely via `.terminated .outOfFuel`
   (`PrefixOutcome.isSafe (.terminated .outOfFuel) = True`), avoiding spurious
   UB on fuel exhaustion.

#### 5.2 Step-Indexed Mutual Induction (`mutual_recursion_callSpec_sound`)

Because each `callFn` transition strictly decrements `callFuel` (`fuel < fuel +
1`), mutually recursive function pairs $(f, g)$ can be verified modularly
against their `CallSpecTable` entries without unfolding the callee's `MirBody`
inside the caller's proof. Theorem `mutual_recursion_callSpec_sound`
(`support/round2_track2_probe.lean:3678-3686`) establishes the general
strong-induction rule over `callFuel`:

```lean
theorem mutual_recursion_callSpec_sound {P Q : Nat → Prop}
    (hP : ∀ k, (∀ j, j < k → Q j) → P k)
    (hQ : ∀ k, (∀ j, j < k → P j) → Q k) :
    ∀ k, P k ∧ Q k
```

We instantiate this principle on the mutually recursive 4-block MIR bodies
`isEvenMirBody` (`fnIsEven = ⟨0⟩`, calling `fnIsOdd` on `n - 1`) and
`isOddMirBody` (`fnIsOdd = ⟨1⟩`, calling `fnIsEven` on `n - 1`) under
`evenOddCallSpecTable`, proving `validEven_at_fuel` (lines 3858–3982),
`validOdd_at_fuel` (lines 4038–4164), and the combined theorem
`is_even_is_odd_mutual_sound : ∀ k, ValidEven k ∧ ValidOdd k` (lines 4169–4172).

---

### Finding 6: Cross-Track 64-Bit Hardware Projection $\pi_{\text{isa}}$ and `deriving`-Free Structural Equality

Basis: `source` + `execution` + `derived`

#### 6.1 Non-Identity Behavior Projection $\pi_{\text{isa}} : \mathsf{MirLang.Behavior} \to \mathsf{HwIsaLang.Behavior}$

In Round 1's `support/track2_self_hosted_compiler_probe.lean`, `IsaMachine`
shared `MirState` as its state carrier so $\pi_{\text{isa}}$ could be `id`. To
connect `MirLang` (`State := MirState`, `Val := MirVal`) to a concrete 64-bit
register machine (`HwIsaMachine` in Section 5 of
`support/round2_track2_probe.lean:4175-4524`), we define `HwIsaState`:

```lean
structure HwIsaState where
  regs : Fin 16 → BitVec 64
  sp : BitVec 64
  pc : Nat
  mem : MemState
```

Following the System V x86-64 calling convention, argument locals `_1` and `_2`
reside in `regRdi = ⟨0, _⟩` and `regRsi = ⟨1, _⟩`, and the return register is
`regRax = ⟨2, _⟩`. The state lifting map `hwToMirState : HwIsaState → MirState`
maps `hst.regs regRdi` and `hst.regs regRsi` to `.usize (hst.regs regRdi).toNat`
and `.usize (hst.regs regRsi).toNat`, while `encodeMirVal64 : MirVal → BitVec 64`
encodes scalar return values as 64-bit bitvectors (`BitVec.ofNat 64 n`). The
behavior projection $\pi_{\text{isa}}$ is defined contravariantly on initial
states and covariantly on outcomes via `Partial.map`:

```lean
def π_isa (B_mir : MirLang.Behavior) : HwIsaLang.Behavior :=
  fun q_isa =>
    (B_mir ⟨hwToMirState q_isa.init, q_isa.steps⟩).map mapExecOut64
```

We prove:
- **`monotone_π_isa : Monotone π_isa` (lines 4404–4414):** Preserves the
  `Partial` refinement preorder (`B₁ ≤ B₂ → π_isa B₁ ≤ π_isa B₂`), satisfying
  the monotonicity obligation of `Trusted.Compiler.SoundOn` and
  `Trusted.Compiler.compose`.
- **`hwAddU64_compiles` (lines 4465–4513):** Proves `Compiles MirLang HwIsaLang
  π_isa mirAddU64Body hwAddU64Prog` for a 64-bit hardware program `add rax, rdi,
  rsi; ret` against `mirAddU64Body` under modular $2^{64}$ wrapping addition.

#### 6.2 `TrustedBoundary.lean`-Compliant Structural Equality Without `deriving`

Because `trusted/audit/TrustedBoundary.lean:185-206` forbids `deriving` clauses
in `trusted/lean/` and `theory/Anneal/`, `support/round2_track2_probe.lean`
contains **zero `deriving` clauses** across all 4,586 lines. Instead, we write
explicit structural boolean equality checkers and prove their soundness (`beq*
a b = true → a = b`) and reflexivity (`beq* a a = true`) by structural
induction:

- **`Trusted` AST & Value Equality (`round2_track2_probe.lean:854-979`):**
  `beqList`, `beqAtomicOrdering`, `beqScalarVal`, and `beqMirVal`, together with
  `beqMirVal_eq_of_true` and `beqMirVal_refl`.
- **`HwIsaProg` Certificate Equality (`round2_track2_probe.lean:4221-4298`):**
  `beqFin16`, `beqBitVec64`, `beqHwIsaStmt`, `beqHwIsaTerm`, `beqHwIsaBlock`,
  and `beqHwIsaProg`, together with `beqHwIsaProg_eq_of_true`.
- **Certificate-Validated Hardware Lowering (`lowerMirToHwIsa_compiles`, lines
  4518–4522):** Proves that any candidate 64-bit hardware program `hwProg :
  HwIsaProg` accepted by `beqHwIsaProg hwProg hwAddU64Prog = true` satisfies
  `Compiles MirLang HwIsaLang π_isa mirAddU64Body hwProg` without `deriving` or
  `Lean.ofReduceBool`.

---

## Boundaries

1. **`trusted/lean/` vs. `theory/Anneal/` Placement Boundary:**
   - Only the primitive AST/machine definitions (`MirAst`, `MirSemantics`,
     `HwIsaState`, `HwIsaMachine`, `HwIsaLang`, `π_isa`, and `CrateTheorem`)
     belong in `trusted/lean/`. Per `Trusted/Refinement.lean:193`, modules in
     `trusted/lean/` must contain zero theorems.
   - All lowering functions (`lowerMirBody`, `f_spec`), certificate checkers
     (`checkCert`, `beqHwIsaProg`), functional translation definitions
     (`evalSym`, `translatePure`), and soundness/bootstrap theorems belong
     strictly outside `trusted/` in `theory/Anneal/`.
2. **`deriving` Usage in Round 1 vs. Round 2 Probes:**
   - `support/track2_self_hosted_compiler_probe.lean` (Round 1) uses `deriving
     DecidableEq` on `IsaProg` (which elaborates to constructive decision
     procedures with zero extra axioms, confirmed by `#print axioms`), whereas
     `support/round2_track2_probe.lean` (Round 2) eliminates all `deriving`
     clauses completely to match `TrustedBoundary.lean` Phase 1 syntax rules.
     When migrating `IsaProg` or `HwIsaProg` into `theory/Anneal/`, follow the
     explicit `beq*` pattern from `support/round2_track2_probe.lean`.
3. **Scope of Mechanized Slice, ADT, and Hardware Models:**
   - **known not to apply / not yet modeled in `round2_track2_probe.lean`:**
     `MirVal.refSliceLoc` models shared immutable slices (`&[usize]`); mutable
     slices (`&mut [T]`) and growable `Vec<T>` buffers require extending
     `LoanEntry` backward lenses (`FunctionalTranslation.lean`) or spatial heap
     predicates (`MirLemmas.lean`) to indexed sub-slice ranges.
   - **known not to apply:** `hwToMirState` in `round2_track2_probe.lean:4373-4385`
     lifts 2 register arguments (`rdi`, `rsi`); functions with $>6$ integer
     arguments or stack-spilled `PassMode::Indirect` / `PassMode::Cast` frames
     require composing `π_isa` with the `FnAbi` and `MaskedWord` marshaling
     invariants established in the companion report
     `rustc-codegen-anneal-monomorphization-abi-and-intrinsics-2026`.

---

## Evidence

### 1. Primary Upstream and Repository Sources

- **Anneal Repository (`joshlf/anneal` at `e75556f57d76d09fd5fc84fc4bfca6a89c3b85e0` / `e75556f5767705404404c0675c6d2d9bcee41d6f`):**
  - `trusted/audit/TrustedBoundary.lean:1-1014`: Two-phase `"preflight"` and
    `"audit"` kernel-environment inspector enforcing closed syntax/attribute
    allowlists (forbidding `unsafe`, `partial`, `meta`, `axiom`, `native_decide`,
    and `deriving`), axiom-closure restriction to
    `{Classical.choice, Quot.sound, propext}`, and `Kernel.Environment.replay`
    at `trustLevel := 0`.
  - `trusted/lean/Trusted/Refinement.lean:200-532`: Layer 1A definitions of
    `Preorder`, `Partial`, `Behavior`, `Language`, `Compiles`, `Abstracts`,
    `Compiler`, `Compiler.SoundOn`, `Compiler.Verified`, and
    `VerificationResultOn`.
  - `trusted/lean/Trusted/StepResult.lean:62-196`: Layer 1B `SmallStepMachine`,
    `StepResult`, `ReachesPrefix`, `BehaviorOf`, and
    `SmallStepMachine.toLanguage`.
  - `trusted/lean/Trusted/MirAst.lean:45-381`,
    `trusted/lean/Trusted/Memory.lean:51-228`, and
    `trusted/lean/Trusted/MirSemantics.lean:44-872`: Layer 2A–2C `MirBody`,
    `MemState`, `MirMachine`, `MirLang`, `opaque rustc`, `TCBItem.rustcLowering`,
    and `CrateTheorem`.
  - `theory/Anneal/Refinement.lean:50-273`,
    `theory/Anneal/StepResult.lean:38-181`,
    `theory/Anneal/MirLemmas.lean:40-256, 960-997`, and
    `theory/Anneal/FunctionalTranslation.lean:66-8315`: Pass composition and
    plan-guided shallow functional translation (`TransPlan`, `SymPlan`,
    `computePlan`, `evalSym`, `translatePure`, `evalSym_sound`,
    `translate_sound`, `evalSymWith_sound`).
- **Upstream `rust-lang/rust` and `rust-lang/reference`:**
  - `rust-lang/rust@e402c1edf047a23b0cfef40c6097d1caa294050b` (PR `#154341`):
    `compiler/rustc_middle/src/mir/syntax.rs:430-503, 1365` (`Rvalue::Use(Operand,
    WithRetag)`) and `compiler/rustc_codegen_ssa/src/mir/retag.rs:25-240`
    (`!Unpin` / `UnsafePinned` and `MaybeDangling` filtering).
  - `rust-lang/rust@8006091eb71ae7d9e9bccb66c6122c9d68af4466`:
    `compiler/rustc_middle/src/mir/syntax.rs:990-1085` (`AssertKind::BoundsCheck`),
    `1163-1298` (`ProjectionElem::{Deref, Field, Index, Downcast}`), and
    `1354-1628` (`Rvalue::{Len, Discriminant, Aggregate}`).
  - `rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67`:
    `compiler/rustc_middle/src/mir/syntax.rs:1308-1339, 1562-1614`.
  - `rust-lang/reference@82da570bafd9efed421bdbae0f8603ede8dd308b`:
    `src/types/slice.md:6-10` and `src/behavior-considered-undefined.md:114-147`.

### 2. Complete Theorem Inventory for `support/track2_self_hosted_compiler_probe.lean`

Preserved at `support/track2_self_hosted_compiler_probe.lean` (7,801 lines,
SHA-256 `f35d5e4a3d0c01dbce593ff10b94a4ff4666e0125fdfa88778e268002fe4a1ec`),
built on verbatim copies of Anneal's Layer 1A–2C and `FunctionalTranslation`
infrastructure (lines 1–6531) followed by the Track 2 mechanization (lines
6532–7801):

| Declaration Name | Kind | Lines | Role & Guarantee Established | Axioms (`#print axioms`) |
| :--- | :--- | :---: | :--- | :--- |
| `IsaStmtInstr`, `IsaTermInstr`, `IsaBlock`, `IsaProg`, `IsaMachine`, `IsaLang`, `π_isa` | `inductive` / `structure` / `def` | 6558–6679 | Target register-machine instruction set, small-step operational semantics, and behavior projection $\pi_{\text{isa}}$. | — |
| `monotone_π_isa` | `theorem` | 6681–6682 | Proves `Monotone π_isa`. | `(none)` |
| `lowerStmt`, `lowerTerm`, `lowerBasicBlock`, `lowerMirBody`, `checkIsaFits`, `f_spec` | `def` | 6685–6740 | Structural MIR-to-ISA lowering pass and partial resource-bounded compiler `f_spec : MirBody → Option IsaProg` (`localCount ≤ 64`, `!blocks.isEmpty`). | — |
| `evalIsaStmt_lowerStmt_eq`, `evalIsaTerm_lowerTerm_eq`, `evalIsaStep_lowerMirBody_eq`, `initIsaState_lowerMirBody_iff` | `theorem` | 6742–6792 | Step-by-step and initial-state lockstep simulation lemmas between `MirMachine` and `IsaMachine`. | `[propext]` |
| `reachesPrefix_lowerMirBody_iff` | `theorem` | 6794–6893 | Bidirectional execution-prefix equivalence `ReachesPrefix IsaMachine (lowerMirBody body) ↔ ReachesPrefix MirMachine body`. | `[propext]` |
| `lowerMirBody_compiles` | `theorem` | 6896–6903 | Proves `Compiles MirLang IsaLang π_isa body (lowerMirBody body)` for all `body : MirBody`. | `[propext]` |
| `f_spec_sound` | `theorem` | 6909–6942 | **Architecture A Partial Compiler Soundness:** Whenever `f_spec body = some prog`, `Compiles MirLang IsaLang π_isa body prog ∧ prog.localCount ≤ 64 ∧ prog.blocks ≠ []`. | `[propext]` |
| `VerifiedIsaCompiler`, `VerifiedIsaCompiler_soundOn`, `VerifiedIsaCompiler_verified` | `def` / `theorem` | 6945–6956 | Packages `lowerMirBody` into `Compiler MirLang IsaLang` and proves `SoundOn` and `Verified`. | `[propext]` |
| `IsaCrateTheorem`, `CrateTheorem_transfers_to_IsaLang` | `def` / `theorem` | 6960–6987 | **Zero-TCB Crate Transfer:** Transfers `CrateTheorem c` (`c.tcb = []`) to `IsaCrateTheorem c` with zero TCB assumptions. | `[propext]` |
| `compilerMirBody`, `constImmMirBody`, `decodeMirDesc`, `decodeCompilerOut`, `pureCompilerPass` | `def` | 7017–7109 | 6-block branching Rust Subset $K$ compiler pass `compilerMirBody`, descriptor encoder/decoder, and extracted pure pass `pureCompilerPass`. | — |
| `translatePure_compilerMirBody_rfl`, `translatePure_compilerMirBody_eq` | `theorem` | 7111–7144 | **Step 1A (`rfl` Specialization):** Kernel `rfl` specialization of `translatePure (computePlan compilerMirBody) compilerMirBody` and equivalence to `.ok (.usize (pureCompilerPass regCount imm))`. | `[propext]` |
| `EnsuresCompilerMirBody`, `compilerMirBody_func_refines_ensures`, `compilerMirBody_satisfies_ensures`, `compilerMirBody_satisfies_wellFormed` | `def` / `theorem` | 7146–7235 | **Step 1B (`translate_sound` Bridge):** Proves `MirLang.sem compilerMirBody ≤ EnsuresCompilerMirBody` and unconditional UB-freedom `MirLang.sem compilerMirBody ≤ MirLang.WellFormed`. | `[propext]` |
| `pureCompilerPass_refines_f_spec` | `theorem` | 7239–7263 | **Step 2A (Pure Specification Refinement):** Proves that `decodeCompilerOut regCount (pureCompilerPass regCount imm) = some isaProg` implies `f_spec (decodeMirDesc regCount imm) = some isaProg`. | `[propext]` |
| `compilerMirBody_two_step_sound` | `theorem` | 7271–7294 | **Architecture B Two-Step Equivalence Theorem:** Connects concrete `MirMachine` execution of `compilerMirBody` to `f_spec` and `Compiles MirLang IsaLang π_isa`. | `[propext]` |
| `Cert`, `checkCert`, `checkCert_sound` | `structure` / `def` / `theorem` | 7313–7368 | Certificate structure, linear validator `checkCert`, and validator soundness theorem `checkCert body cand cert = true → Compiles MirLang IsaLang π_isa body cand`. | `[propext]` |
| `certifyingCompileOpt`, `certifyingCompileOpt_sound` | `def` / `theorem` | 7372–7404 | Partial certifying compiler wrapper and soundness proof. | `[propext]` |
| `certifyingCompiler`, `certifyingCompiler_soundOn`, `certifyingCompiler_verified` | `def` / `theorem` | 7407–7445 | **Architecture C Hybrid Certifying Compiler Theorem:** Proves `SoundOn` and `Verified` for `certifyingCompiler untrustedOpt` with **zero hypotheses** on `untrustedOpt : MirBody → IsaProg × Cert`. | `[propext]` |
| `checkerMirBody`, `pureCertChecker`, `translatePure_checkerMirBody_rfl`, `translatePure_checkerMirBody_eq`, `checkerMirBody_satisfies_ensures`, `checkerMirBody_two_step_sound` | `def` / `theorem` | 7458–7659 | **Rust Subset $K$ Certificate Validator:** 7-block `checkerMirBody` verified via Two-Step Equivalence (`checkerMirBody_two_step_sound`). | `[propext]` |
| `compilerIsaProg`, `f_spec_compilerMirBody_eq`, `compilerMirBody_self_descriptor_rfl`, `compilerIsaProg_verified` | `def` / `theorem` | 7682–7704 | Compiles `compilerMirBody` via `f_spec` by kernel `rfl` (`f_spec compilerMirBody = some compilerIsaProg`). | `[propext]` |
| `self_hosted_bootstrap_sound` | `theorem` | 7716–7738 | **Hardware-Level Bootstrap Soundness:** Proves that `compilerIsaProg` running on `IsaMachine` is UB-free and every decoded output compiles its source program under `f_spec`. | `[propext]` |
| `self_hosted_stage2_reproducibility` | `theorem` | 7748–7765 | **Stage 1 $\to$ Stage 2 Binary Fixed Point:** Executing Stage 1 `compilerIsaProg` on `IsaMachine` with its own descriptor `(6, 1000)` reproduces Stage 2 `compilerIsaProg`. | `[propext]` |

### 3. Complete Theorem Inventory for `support/round2_track2_probe.lean`

Preserved at `support/round2_track2_probe.lean` (4,586 lines, SHA-256
`11de1875983da8a6e8c3a3705d559d406938ad06fb7ea3b6e9d8cbebfaf136e4`), defined
with **zero `deriving` clauses** across the entire file:

| Declaration Name | Kind | Lines | Role & Guarantee Established | Axioms (`#print axioms`) |
| :--- | :--- | :---: | :--- | :--- |
| `compiles_refl`, `compiles_trans`, `verified_of_soundOn_and_spec`, `Trusted.Compiler.compose`, `compiler_compose_soundOn` | `def` / `theorem` | 436–485 | Layer 1A compiler composition and refinement transitivity infrastructure. | `[propext]` |
| `ScalarVal`, `MirTy`, `MirVal`, `PlaceElem`, `Place`, `Rvalue`, `Statement`, `Terminator`, `CallSpecTable`, `MirBody` | `inductive` / `structure` | 560–840 | Extended `MirAst` with `.refSliceUsize`, `.adt`, `.refSliceLoc`, `.adtVal`, `PlaceElem.{deref, field, index, downcast}`, `Rvalue.{use, len, discriminant, aggregate, readPlace}`, `Terminator.{assertBoundsCheck, callFn}`, and `CallSpecTable`. | — |
| `beqList_eq_of_true`, `beqAtomicOrdering_eq_of_true`, `beqScalarVal_eq_of_true`, `Trusted.beqMirVal_eq_of_true`, `beqMirVal_refl` | `theorem` | 859–979 | `deriving`-free recursive boolean equality soundness and reflexivity for `MirVal`. | `[propext, Quot.sound]` |
| `evalReadPlace`, `evalRvalue`, `execStatement`, `execTerminator`, `stepBlock`, `MirMachine`, `MirLang` | `def` | 1120–1407 | Small-step `Runtime(PostCleanup)` MIR operational semantics for slices, ADTs, bounds checks, and fuel-indexed `CallSpecTable` calls. | — |
| `SymVal`, `SymValMatchesInMem`, `SymValMatches`, `EnvMatches`, `evalSymReadPlace`, `evalSymRvalue`, `evalSymTerminator`, `evalSym` | `inductive` / `def` | 1435–1788 | Extended symbolic value domain and fuel-indexed functional evaluator `evalSym` for slices, structs, enums, and loops. | — |
| `evalSymOperand_sound`, `evalSymOperandList_sound`, `evalSymReadPlace_sound`, `evalSymRvalue_sound`, `execSymStatement_sound`, `execSymStatements_sound`, `evalSymTerminator_sound` | `theorem` | 1795–2508 | Per-construct symbolic-to-concrete simulation lemmas. | `[propext]` |
| `Anneal.evalSym_slice_sound` | `theorem` | 2514–2663 | **Universal Symbolic Execution Soundness:** Step-indexed simulation from `evalSym fuel body bb env = some (.normal retSym)` to `ReachesPrefix MirMachine` safety and postcondition matching. | `[propext]` |
| `sliceCheckerMirBody`, `evalSym_sliceChecker_nil`, `evalSym_sliceChecker_one`, `evalSym_sliceChecker_two`, `evalSym_sliceChecker_three` | `def` / `theorem` | 2671–2745 | 5-block slice-iterating certificate checker CFG and kernel `rfl` symbolic specializations for 0, 1, 2, and 3 slice elements. | `(none)` |
| `Anneal.sliceCheckerMirBody_two_elem_sound` | `theorem` | 2749–2798 | **Operational Slice Checker Soundness:** Proves safety and exact `(0 ^^^ w0 ^^^ w1) == target` return value for `sliceCheckerMirBody` over universally quantified 2-element slices `[w0, w1]`. | `[propext, Quot.sound]` |
| `enumCertMirBody`, `Anneal.evalSym_enumCert` | `def` / `theorem` | 2805–2840 | Multi-variant `CertKind` enum construction, `Rvalue.discriminant` branch, and `[.downcast 1, .field 0]` extraction verified by `rfl`. | `[propext]` |
| `RetagPermKind`, `BorrowVal`, `BorrowState`, `performRetag`, `MirRetagStmt`, `AnSSAStmt`, `lowerMirRetagProg` | `inductive` / `structure` / `def` | 2884–3032 | Post-PR `#154341` `Rvalue::Use(op, WithRetag)` borrow-tag model and lowering to `AnSSAStmt.retag` vs. `AnSSAStmt.letCopy`. | — |
| `Anneal.retag_lowering_compiles` | `theorem` | 3159–3166 | **Verified `WithRetag` Lowering:** Proves `Compiles MirRetagLang AnSSABorrowLang id p (lowerMirRetagProg p)`. | `[propext]` |
| `Anneal.unsafePinned_retag_is_pure_copy` | `theorem` | 3171–3176 | **`!Unpin` (`UnsafePinned`) Exemption:** Proves `AnSSAStmt.retag` on `.ptr addr tag .unsafePinned` equals `AnSSAStmt.letCopy`. | `[propext]` |
| `Anneal.duplicate_retag_refutes_compiles` | `theorem` | 3237–3307 | **Negative Canary 1:** Proves `¬ Compiles AnSSABorrowLang AnSSABorrowLang id copyAfterRetagProg duplicatedRetagProg` when `.retag` is duplicated. | `[propext]` |
| `Anneal.erase_withRetag_refutes_compiles` | `theorem` | 3324–3391 | **Negative Canary 2:** Proves `¬ Compiles MirRetagLang AnSSABorrowLang id ... erasedRetagProg` when `withRetag = true` is erased to `.letCopy`. | `[propext]` |
| `CopyPropInv`, `copyPropInv_preserved`, `Anneal.retag_copy_prop_compiles` | `def` / `theorem` | 3407–3619 | **Post-Retag Copy Propagation Soundness:** Proves `Compiles AnSSABorrowLang AnSSABorrowLang id copyAfterRetagProg copyPropagatedRetagProg`. | `[propext, Classical.choice, Quot.sound]` |
| `nat_strong_induction`, `Anneal.mutual_recursion_callSpec_sound` | `theorem` | 3650–3686 | **Fuel-Indexed Mutual Induction Principle:** Proves `∀ k, P k ∧ Q k` from mutually inductive step obligations over `callFuel`. | `[propext, Classical.choice, Quot.sound]` |
| `evenOddCallSpecTable`, `isEvenMirBody`, `isOddMirBody`, `ValidEven`, `ValidOdd`, `validEven_at_fuel`, `validOdd_at_fuel`, `Anneal.is_even_is_odd_mutual_sound` | `def` / `theorem` | 3700–4172 | End-to-end modular verification of mutually recursive `isEvenMirBody` and `isOddMirBody` across all `callFuel` budgets `k : Nat`. | `[propext, Classical.choice, Quot.sound]` |
| `HwIsaState`, `HwIsaStmt`, `HwIsaTerm`, `HwIsaBlock`, `HwIsaProg`, `HwIsaMachine`, `HwIsaLang` | `structure` / `inductive` / `def` | 4182–4330 | 64-bit 16-register hardware machine (`regs : Fin 16 → BitVec 64`, `sp : BitVec 64`). | — |
| `beqFin16_eq_of_true`, `beqBitVec64_eq_of_true`, `beqHwIsaStmt_eq_of_true`, `beqHwIsaTerm_eq_of_true`, `beqHwIsaBlock_eq_of_true`, `Anneal.beqHwIsaProg_eq_of_true` | `theorem` | 4224–4298 | `deriving`-free recursive boolean equality soundness for `HwIsaProg`. | `[propext, Quot.sound]` |
| `hwToMirState`, `encodeMirVal64`, `mapExecOut64`, `π_isa`, `Anneal.monotone_π_isa` | `def` / `theorem` | 4342–4414 | Cross-track behavior projection $\pi_{\text{isa}} : \mathsf{MirLang.Behavior} \to \mathsf{HwIsaLang.Behavior}$ and proof of `Monotone π_isa`. | `[propext, Quot.sound]` |
| `mirAddU64Body`, `hwAddU64Prog`, `hwAddU64_compiles`, `Anneal.lowerMirToHwIsa_compiles` | `def` / `theorem` | 4417–4522 | Cross-track hardware lowering refinement proof and `beqHwIsaProg`-validated compilation theorem. | `[propext, Quot.sound]` |

---

## Revalidation

To revalidate both standalone Lean 4.34.1 mechanization probes from the root of
this report package (`reports/verified-rust-compiler-self-hosting-and-certifying-bootstrap-2026/`)
and confirm exit code `0`, zero warnings, zero `sorryAx`, and zero
`Lean.ofReduceBool`, run:

```bash
lean -j1 -M1024 support/track2_self_hosted_compiler_probe.lean
lean -j1 -M1024 support/round2_track2_probe.lean
```

(using `leanprover/lean4:v4.34.1` at commit
`5045d0056413266e57c625dcd7c365b10e377c52`).

Revalidate this report and its probes whenever:
1. `trusted/lean/Trusted/Refinement.lean` or
   `trusted/lean/Trusted/MirSemantics.lean` modifies the signature of
   `Compiler`, `Compiler.SoundOn`, `Compiler.Verified`,
   `TCBItem.rustcLowering`, or `CrateTheorem`.
2. `trusted/audit/TrustedBoundary.lean` modifies its Phase 1 (`"preflight"`)
   command/attribute allowlists or Phase 2 (`"audit"`) axiom-closure rules.
3. Upstream `rust-lang/rust` alters `Rvalue::Use(Operand, WithRetag)`
   (`compiler/rustc_middle/src/mir/syntax.rs`) or the `!Unpin` / `MaybeDangling`
   traversal rules in `compiler/rustc_codegen_ssa/src/mir/retag.rs`.
