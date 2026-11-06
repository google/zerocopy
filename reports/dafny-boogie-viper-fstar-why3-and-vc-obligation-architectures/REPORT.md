# Dafny, Boogie, Viper, F*, Why3, Refinement/Horn Verifiers, C Resource Logics, and Compositional VC Architectures

## Summary

This report synthesizes eleven primary-source, historical-cohort, and executable-witness investigations spanning intermediate verification languages (Dafny, Boogie, Viper Silver/Silicon/Carbon/ViperServer), extensible proof-assistant automation and effect systems (F*, Meta-F*, Steel, PulseCore, Low*/KaRaMeL), durable proof-session persistence (Why3 0.70–1.8.2), Rust refinement and CHC verifiers (Flux, Thrust, RustHorn, Prusti), recursive contract inference and compositional overrides (Stainless, System FR, SAW/Crux MIR, MIRAI, Infer Bi-Abduction and Pulse, SeaHorn, SMACK), and C/systems separation-logic and compiler foundations (RefinedC/Lithium, CN/Cerberus, Fulminate, Bennet, VST, CompCert, Bedrock2):

1. **Dafny, Boogie, and Viper Obligation Boundaries (`2005–2026` & Current Source Review)**: Across `dafny-lang/dafny` (`5f717bf4`), `boogie-org/boogie` (`fcecf73a`), `viperproject/silver` (`da1c8993` / `b4094c37`), `viperproject/silicon` (`6ceff8be`), `viperproject/carbon` (`6421cfda`), and `viperproject/viperserver` (`4cc5bbbe`), source-to-IVL and IVL-to-SMT translations operate by encoding heap permissions, framing (`$_ModifiesFrame`, dynamic frames, or inhaling/exhaling fractional accessibility predicates), and control flow into unstructured Boogie blocks or SMT-LIB2 obligations without producing foundational proof terms by default. In Viper Silver (`VerificationResult.scala`), verification outcomes are structured algebraic types (`Success` vs. `Failure(errors : Seq[AbstractError])` with `AbstractVerificationError` and `ErrorReason`), while `BoogieGenerator.cs` in Dafny lowers `reads`/`modifies`/`decreases` clauses into Boogie `requires`/`ensures`/`assert` splits.
2. **Boogie and Viper Translation & VCG Certificate Validation (CAV 2021, PLDI 2024, & Failure-Reflection Witness)**: Parthasarathy et al. (CAV 2021 DOI `10.1007/978-3-030-81688-9_33`; PLDI 2024 DOI `10.1145/3656438`, Zenodo `10802176`) certify individual runs of Boogie's VCG (passive transformation + weakest precondition) and Viper-to-Boogie frontend translations in Isabelle/HOL by proving **backward soundness** (`sound_vc`: if the emitted SMT/Boogie obligation is valid, the source Viper/Boogie program is correct). An executable failure-reflection witness (`support/boogie-viper-failure-reflection-certificates-2021-2024/failure_witness.py` and `failure-results.json`) proves that forward/backward VCG soundness (`WpSound` = `True`) does **not** imply completeness (`WpComplete` = `False`) when an abstract `havoc` / coarse loop invariant over-approximates reachability, nor does it ensure that an SMT counterexample reflects a genuine source execution (`ReflectedFailureSound` = `False` under unverified error back-translation).
3. **F* and Meta-F* Extensible Proof Automation and Trust Boundaries (`2019–2026` & Release `2026.09.27` Source Review)**: At `FStarLang/FStar` `78bb239b54cc113be68fb1dc0cbdfeb19378766a` (`version.txt` `2026.09.27`, release tag `v2026.09.27` -> `7deb38a2`), Meta-F* tactics (`src/tactics/FStarC.Tactics.Monad.fst:45–128`) manipulate `proofstate` goals whose solutions are always re-checked by the core typechecker (`src/typechecker/FStarC.TypeChecker.Core.fst:980–1165`). However, residual subgoals (`smt_goals`) are discharged by an external Z3 process (`src/smtencoding/FStarC.SMTEncoding.Z3.fst`) without kernel proof reconstruction, and native reflection/norm steps (`--MLish`, native plugins, `admit`/`assume`) enlarge the TCB unless audited via `--report_assumes`.
4. **Why3 Durable Proof Sessions (`0.70` through `1.8.2`, `2011–2025`)**: Across 22 historical releases (`support/history-matrix.json`, VSTTE 2013 DOI `10.1007/978-3-642-54108-7_10`), Why3 persists verification state in `why3session.xml` (`why3session.dtd`: `file → theory → goal → proof_attempt | transf`) paired with `why3shapes` (structural goal shapes and CRC/SHA digests). When source code or specifications change, `Session_itp.merge_files` pairs old and new subgoals via shape similarity so unchanged proof attempts and interactive transformations survive code evolution, while `why3 replay` re-executes provers in batch mode to prevent stale `valid` flags.
5. **Rust Refinement Types, CHC Solvers, and Lean VC Boundaries (`2026`)**: Comparative source audit of **Flux** (`flux-rs/flux` `6769bb9c`, PLDI 2023), **Thrust** (`coord-e/thrust` `187a1e97`, PLDI 2025), **RustHorn** (`hopv/Rust-horn` `4823f8f9`, ESOP 2020), and **Prusti** (`prusti/prusti` `0d4a8d49`). Flux indexes immutable types (`i32[n]`) and strong references (`&strg T`) over a liquid-fixpoint / Z3 refinement constraint tree while marking raw-pointer internals `#[flux::trusted]`; Thrust and RustHorn reduce prophetic MIR executions to CHCs solved by Spacer/Hoice (`SAT`/`UNSAT`), where an `UNSAT`/`SAT` verdict provides no kernel proof term unless the synthesized inductive predicates are re-checked in Lean.
6. **Recursive Contract Inference and Verified Callee Lifecycles (`2026`)**: Examines **RustHorn** (`4823f8f9`), **Stainless** (`EPFL-LARA/stainless` `399c34a0`), **System FR** (`epfl-lara/SystemFR` `325bd745` & `90300f26`, OOPSLA 2019), and **SAW** (`GaloisInc/saw-script` `27a7ae98`). Distinguishes CHC predicate synthesis (where solver invariants must satisfy initiation, consecution, and safety clauses), Stainless unfolding measures (`MeasureInference.scala`), System FR reducibility candidates (`ReducibilityDefinition.v`), and SAW `mir_verify` vs. `mir_unsafe_assume_spec` override tables.
7. **RefinedC/Lithium, CN, Fulminate, and Bennet Result Interfaces (`2026`)**: Compares foundational vs. SMT/testing C verification in **RefinedC** (`iris/refinedc` `2e89846b`, PLDI 2021), **CN** (`rems-project/cn` `b4a2f009` + Cerberus `c8c085d4`, POPL 2023), **Fulminate** (POPL 2025 DOI `10.1145/3704879`, executable runtime separation-logic specification testing extracted from CN), and **Bennet** (`bennet.pdf`, randomized property-based generator synthesis from CN resource specifications).
8. **Resource Logics, Intrinsic Effects, and Compilation Interfaces (`VST`, `CompCert`, `Bedrock2`, `Low*`, `Steel`/`PulseCore`)**: Connects VST's `semax_prog` (`veric/semax_prog.v:1967–1989` at `3c37c2e2`) and CompCert's `transf_c_program_correct` (`driver/Compiler.v:446–452` at `74cbdbf0`, requiring source safety `safe L1` in `common/Smallstep.v:1298–1312`) with Bedrock2's `compiler_correct` (`compiler/src/compiler/Pipeline.v:682–730` at `757f17c6`), Low*'s $\lambda\text{Low}^*\to\text{C}^*\to\text{Clight}$ trace-preservation theorems (arXiv `1703.00053v6`, including the System V struct-padding ABI boundary in footnote 12), and F* PulseCore's stratified separation-logic semantics (`pulse/lib/core/PulseCore.Semantics.fst` at `e2b5042f`).
9. **Static/Abductive Inference and Compositional Result Meaning (`MIRAI`, `Infer`, `SeaHorn`, `SMACK`, `Viper`, `Prusti`, `SAW`)**: Maps exact result types across `MIRAI` (`aae0a56f`, where `is_incomplete` summaries are suppressed by default unless audited in verify mode), historical `Infer` bi-abduction (`99464c01`, POPL 2009 `BiAbd` missing-heap/frame inference `Δ * M ⊢ H * F`) vs. current `Infer` Pulse (`5aac32c0`, tracking latent errors and experimental Charon ULLBC-to-Textual Rust lowering), `SeaHorn` (`89278017`), `SMACK` (`0a644712`), and `SAW` (`27a7ae98`, where `Override.hs:314–339` asserts preconditions and assumes postconditions at call replacement without proving the callee).

---

## Applicability

| Ecosystem / Subsystem | Pinned Repositories & Revisions | Primary Artifacts in `support/` |
|---|---|---|
| Dafny, Boogie, & Viper (Silver, Silicon, Carbon, ViperServer) | `dafny` `5f717bf4`, `boogie` `fcecf73a`, `silver` `da1c8993` & `b4094c37`, `silicon` `6ceff8be`, `carbon` `6421cfda`, `viperserver` `4cc5bbbe` | `support/dafny-boogie-viper-obligation-boundaries-2005-2026/evidence-map.json`, `support/official-source-observation.json`, `support/snapshots/`, `support/matrix.json` |
| Boogie & Viper Certificates (CAV 2021, PLDI 2024) | DOIs `10.1007/978-3-030-81688-9_33`, `10.1145/3656438`, Zenodo `10802176` | `support/boogie-viper-failure-reflection-certificates-2021-2024/failure_witness.py` and `failure-results.json` |
| F*, Meta-F*, Steel, PulseCore, Low* | `FStarLang/FStar` `78bb239b` (`2026.09.27`, tag `v2026.09.27` -> `7deb38a2`) & `e2b5042f`, `smtcoq` `3187cf12`, DOIs `10.1007/978-3-030-17184-1_2`, `10.1145/3110261` | `support/fstar-extensible-proof-automation-trust-boundaries-2019-2026/evidence-map.json`, `support/fstar-20260927-current-source-review/official-source-identity.json` |
| Why3 Proof Sessions (`2011–2025`) | Why3 `0.70` through `1.8.2` (`2025-09-16`), VSTTE 2013 (`10.1007/978-3-642-54108-7_10`) | `support/history-matrix.json`, `support/source-map.json` (and `support/why3-durable-proof-sessions-2011-2025/`) |
| Flux, Thrust, RustHorn, Prusti | `flux` `6769bb9c`, `thrust` `187a1e97`, `Rust-horn` `4823f8f9`, `prusti` `0d4a8d49` | `support/refinement-horn-and-lean-vc-boundaries-2026/source-evidence.json`, `prusti-source-evidence.json`, `additional-source-evidence.json` |
| Stainless, System FR, SAW | `stainless` `399c34a0`, `SystemFR` `325bd745` & `90300f26`, `saw-script` `27a7ae98` | `support/recursive-inference-and-verified-callee-lifecycles-2026/source-identities.json`, `coverage.json` |
| RefinedC, CN, Cerberus, Fulminate, Bennet | `refinedc` `2e89846b`, `cn` `b4a2f009`, `cerberus` `c8c085d4`, DOIs `10.1145/3453483.3454036`, `10.1145/3704879` | `support/refinedc-lithium-and-cn-result-interfaces-2026/source-identities.json`, `coverage.json` |
| VST, CompCert, Bedrock2 | `VST` `3c37c2e2`, `CompCert` `74cbdbf0`, `bedrock2` `757f17c6` | Pinned GitHub blob hashes and line ranges in Section 8 and `REPORT.json` |
| MIRAI, Infer, SeaHorn, SMACK | `MIRAI` `aae0a56f`, `infer` `5aac32c0` & `99464c01`, `seahorn` `89278017`, `smack` `0a644712` | `support/inference-and-compositional-result-interfaces-2026/source-evidence.json`, `historical-infer-evidence.json`, `literature.json` |

---

## Findings

### 1. Dafny, Boogie, and Viper Obligation Boundaries (`2005–2026` & Current Source Review)

**Basis: source (`support/dafny-boogie-viper-obligation-boundaries-2005-2026/evidence-map.json`, `support/official-source-observation.json`, `support/snapshots/`, `support/check_matrix.py`, `support/matrix.json`).**

#### 1.1 Pinned Repository and Release-Tag Inventory
Direct inspection of official Git refs (`support/*-refs.txt`, `support/*-release-tag-refs.txt`, `support/official-source-observation.json`) establishes the current upstream baseline:

| Component | Upstream Repository | Observed `master` Revision | Latest Observed Release Tag | Core Inspected Interface Snapshot |
|---|---|---|---|---|
| **Dafny** | `dafny-lang/dafny` | `5f717bf447b19d38cad1b69b1bf9a9f102feccfb` | `v4.11.0` | `support/snapshots/dafny/Source/DafnyCore/Verifier/BoogieGenerator.cs` |
| **Boogie** | `boogie-org/boogie` | `fcecf73a49d11ad3ab16729abd03169e5ecfd938` | `v3.5.1` | `support/snapshots/boogie/README.md` (`VCGen`, `ExecutionEngine`) |
| **Viper Silver** | `viperproject/silver` | `da1c8993b66feb39976e3609e2580a4661137a0f` (also `b4094c37`) | `v.26.08-release` (prior `v.21.07-release`) | `support/snapshots/silver/src/main/scala/viper/silver/verifier/VerificationResult.scala` |
| **Viper Silicon** | `viperproject/silicon` | `6ceff8be6ba55d858b7d018fdfeb866b7e8aa0ed` | `v.26.08-release` | `support/snapshots/silicon/README.md` (symbolic execution backend) |
| **Viper Carbon** | `viperproject/carbon` | `6421cfda16d35f37cb9a7966f04fcd2d96abdda2` | `v.26.08-release` | `support/snapshots/carbon/README.md` (Boogie VC-generation backend) |
| **ViperServer** | `viperproject/viperserver` | `4cc5bbbe18d4a83e4b398da3904ba9696256611b` | `v.26.08-release` | `support/snapshots/viperserver/README.md` (HTTP/LSP caching server) |

#### 1.2 Architectural Obligation Lowering and Result Boundaries
1. **Dafny-to-Boogie (`BoogieGenerator.cs`)**: Dafny lowers dynamic-frame specifications (`reads`, `modifies`, `decreases`, `invariant`) into Boogie procedures over an explicit `$Heap` variable (`$_ModifiesFrame`, `$IsGoodHeap`, `$IsAllocBox`). Proof obligations are split into fine-grained Boogie `assert` statements (`Assert(tok, expr, description)`) and sent to Boogie's `ExecutionEngine`, which invokes Z3/CVC5. Dafny's soundness depends on the unverified C# translation in `BoogieGenerator.cs`, the consistency of Dafny's Boogie prelude (`DafnyPrelude.bpl`, including quantifier triggers), Boogie's VC generator, and the SMT solver.
2. **Boogie IVL (`boogie-org/boogie`)**: Transforms unstructured CFGs into DAGs, converts mutations into SSA form (passive transformation `assume x_1 == e`), and computes weakest preconditions (`VCGen`) exported as SMT-LIB2 queries.
3. **Viper Dual Backends (`silver`, `silicon`, `carbon`)**:
   - **Silver AST (`VerificationResult.scala`)**: Defines `sealed abstract class VerificationResult`, splitting into `case object Success` and `case class Failure(errors: Seq[AbstractError])`. Every `AbstractVerificationError` pairs an offending AST node (`offendingNode: ErrorNode`) with a structured `ErrorReason` (`InsufficientPermission`, `AssertionFalse`, `NegativePermission`, `MagicWandChunkNotFound`, etc.) and optional counterexample models.
   - **Silicon (`viperproject/silicon`)**: Evaluates Silver programs via small-step symbolic execution over heap chunks (`acc(x.f, p)`), querying Z3 along each path (`inhale` adds chunks/assumptions; `exhale` asserts and removes permission amounts).
   - **Carbon (`viperproject/carbon`)**: Compiles Silver programs into Boogie by maintaining explicit permission-mask maps (`Mask[Ref, Field] : Perm`) and heap maps (`Heap[Ref, Field] : Val`), delegating verification to Boogie + Z3.

---

### 2. Boogie and Viper Certificate Validation & Failure-Reflection Limits (CAV 2021, PLDI 2024)

**Basis: primary literature and executable Python/Z3-style witness (`support/boogie-viper-failure-reflection-certificates-2021-2024/failure_witness.py`, `support/boogie-viper-failure-reflection-certificates-2021-2024/failure-results.json`).**

#### 2.1 Forward Soundness vs. Failure Reflection
- **Boogie VCG Certificates (CAV 2021, DOI `10.1007/978-3-030-81688-9_33`)** and **Viper-to-Boogie Translation Certificates (PLDI 2024, DOI `10.1145/3656438`, Zenodo `10802176`)** instrument Boogie and Carbon to emit per-run certificates validated in Isabelle/HOL.
- The validated theorem is a **backward soundness implication**:
  $$\text{Valid}_{\text{Target}}(\text{VC}) \implies \text{Correct}_{\text{Source}}(P)$$
  Whenever the generated VC is proved valid in Isabelle/HOL, the source Boogie or Viper program satisfies its operational specification, removing the C#/Scala translator and VCG pass from the TCB for that verified program.

#### 2.2 Executable Witness of Incompleteness and Spurious Counterexamples (`failure_witness.py`)
What happens when verification **fails** (the VC is invalid/refuted by SMT)? Running `support/boogie-viper-failure-reflection-certificates-2021-2024/failure_witness.py` (`support/boogie-viper-failure-reflection-certificates-2021-2024/failure-results.json`) demonstrates three distinct mathematical boundaries over finite state transitions:
1. **`WpSound = True` vs. `WpComplete = False`**: When a loop or procedure call is abstracted by `havoc` + a coarse invariant/contract $I$ that holds initially and is inductive but omits a needed fact, the concrete program is safe (`ConcreteSafe = True`) while the abstract Boogie/Viper VC is invalid (`AbstractVCValid = False`).
2. **`SpuriousAbstractCounterexample = True`**: Because `havoc` over-approximates reachable states, an SMT counterexample model $\sigma_{\text{cex}} \in I \setminus \text{Reachable}$ refutes the VC without corresponding to any executable source trace.
3. **`ReflectedFailureSound = False` Under Buggy Error Back-Translation**: Even when a genuine abstract failure occurs, mapping a low-level Boogie assertion ID back to a source Viper/Rust error reason (`ErrorReason`) via an unverified lookup table can misattribute a permission failure (`InsufficientPermission`) as a functional postcondition failure (`PostconditionViolated`), proving that soundness certificates (`Valid(VC) => Safe(P)`) do not certify diagnostic failure reflection.

---

### 3. F* and Meta-F* Extensible Proof Automation and Trust Boundaries (`2019–2026` & `2026.09.27` Source Review)

**Basis: source (`support/fstar-extensible-proof-automation-trust-boundaries-2019-2026/evidence-map.json`, `support/fstar-20260927-current-source-review/official-source-identity.json`, `support/fstar-20260927-current-source-review/matrix.json`).**

#### 3.1 Pinned Source Identity (`FStarLang/FStar` `78bb239b`)
Direct inspection of `FStarLang/FStar` (`support/fstar-20260927-current-source-review/official-source-identity.json`) records:
- `master` head: `78bb239b54cc113be68fb1dc0cbdfeb19378766a` (`version.txt` = `2026.09.27`).
- Latest release tag: `v2026.09.27` (annotated tag object `48268f3522ec8da089bbeb5f4e1674d50280a9c7`, peeling to commit `7deb38a27c86990664c6b41e4b6093597acdebd4`).

#### 3.2 Meta-F* Tactic Architecture vs. Lean 4 and SMTCoq
Comparing F* (`78bb239b`, ESOP 2019 DOI `10.1007/978-3-030-17184-1_2`), Lean 4 (`3dc1a088`), and SMTCoq (`3187cf12`) isolates four distinct trust boundaries (`support/fstar-extensible-proof-automation-trust-boundaries-2019-2026/evidence-map.json`):

| Mechanism | F* (`FStarLang/FStar` `78bb239b`) | Lean 4 (`leanprover/lean4` `3dc1a088`) | SMTCoq (`smtcoq/smtcoq` `3187cf12`) |
|---|---|---|---|
| **Tactic State & Elaboration** | `FStarC.Tactics.Monad.fst`: tactics transform `proofstate` (`goals`, `smt_goals`); synthesized witnesses are typechecked by `FStarC.TypeChecker.Core.fst` | `Lean.Elab.Tactic`: tactics synthesize `Expr` metavariable assignments checked in full by the C++ kernel (`Lean.Kernel`) | Coq tactics invoke reflective vernacular/tactic checkers (`verit`, `zchaff`, `lfsc`) |
| **Residual SMT Subgoals** | `smt_goals` are encoded to first-order SMT-LIB2 (`FStarC.SMTEncoding.Encode.fst`) and sent to external Z3 (`Z3.fst`); **Z3's `UNSAT` verdict is trusted without kernel proof reconstruction** | External SAT/SMT solvers (`bv_decide` / LRAT) must emit a certificate re-checked by a verified Lean kernel reduction or tactic proof | External solver emits a resolution/clause certificate re-checked inside Coq by a verified boolean reflection checker (`Trace.v`) |
| **Reflection & Syntax Inspection** | `FStarC.Reflection.V2.Builtins.fst` exposes syntax `term_view` to user metaprograms, while abstract `term` constructors cannot forge typing judgments directly | `Expr` is inspectable and constructible in `MetaM`, with soundness enforced solely at kernel `addDecl` time | Terms are reified into deep-embedded Coq ASTs for reflective checking |
| **Native Plugins & Escape Hatches** | OCaml-extracted native tactics (`--load_cmxs`), `assume`, `admit`, and SMT axioms (`assume val`) bypass kernel checking; audited via `--report_assumes` | `@[implemented_by]`, `@[extern]`, `sorryAx`, and `lcProof` (when `trustCompiler` is used) are reported by `#print axioms` | `Admitted` / `Axiom` reported by `Print Assumptions` and `coqchk` |

---

### 4. Why3 Durable Proof Sessions (`0.70` through `1.8.2`, `2011–2025`)

**Basis: historical release and source survey (`support/history-matrix.json`, `support/source-map.json`, VSTTE 2013 DOI `10.1007/978-3-642-54108-7_10`).**

#### 4.1 Session Tree Schema and Shape-Based Proof Pairing
To keep automated and interactive proofs durable across source edits and prover upgrades, Why3 (`0.70` in 2011 through `1.8.2` on `2025-09-16`, `support/history-matrix.json`) separates volatile prover outputs from a version-controlled session tree (`src/session/session_itp.mli`, `share/why3session.dtd`):
1. **Hierarchical Session Tree (`why3session.xml`)**:
   - `file` $\to$ `theory` $\to$ `goal` $\to$ (`proof_attempt` | `transf` $\to$ child `goal`s).
   - Every `proof_attempt` records the exact prover identity `(name, version, alternative)`, resource limits `(timelimit, steplimit, memlimit)`, and outcome (`valid`, `invalid`, `timeout`, `outofmemory`, `steplimitexceeded`, `unknown`, `failure`, `highfailure`), plus an `obsolete` boolean attribute.
   - Every `transf` records a named transformation (`split_vc`, `inline_goal`, `introduce_premises`, `instantiate`, `induction_ty_lex`, or interactive script) so large VCs are decomposed into smaller, solver-friendly leaves before calling SMT.
2. **Goal Shapes and Checksums (`why3shapes`, `src/session/term_code.ml`)**:
   - **Checksum (CRC / SHA)**: Exact hash of the normalized goal formula and context; if unchanged after a source edit, the prior `proof_attempt` remains non-obsolete.
   - **Shape (`why3shapes`)**: A structural skeleton string capturing the logical connectives and predicate names of a goal while abstracting over variable renamings and minor constant shifts (VSTTE 2013, `hal-00875395`). When a user modifies a Rust/WhyML function and re-runs Why3, `Session_itp.merge_files` computes an edit-distance matching between old and new goal shapes, re-attaching existing `transf` trees and `proof_attempt` nodes to the corresponding updated goals and marking modified leaves `obsolete="true"` for targeted re-verification via `why3 replay`.

---

### 5. Rust Refinement Types, CHC Solvers, and Lean VC Boundaries (`2026`)

**Basis: source (`support/refinement-horn-and-lean-vc-boundaries-2026/source-evidence.json`, `support/refinement-horn-and-lean-vc-boundaries-2026/prusti-source-evidence.json`, `support/refinement-horn-and-lean-vc-boundaries-2026/additional-source-evidence.json`, `support/refinement-horn-and-lean-vc-boundaries-2026/coverage.json`).**

| Verifier & Pinned Commit | Core Specification Abstraction | VC Lowering & Backend | Explicit Trust & Escape-Hatch Boundary |
|---|---|---|---|
| **Flux (`flux-rs/flux` `6769bb9cbd1216380f542349494efafafd6104a3`, PLDI 2023)** | Index refinements (`i32[n]`, `RVec<T>[len]`), existential refinements (`i32{v: v > 0}`), and strong mutable references (`&strg T` updating type indices on exit) | `crates/flux-refineck/` builds a horn/refinement constraint tree (`KVar` liquid qualifiers) solved by `liquid-fixpoint` + Z3 (`crates/flux-fixpoint/`) | `#[flux::trusted]` skips body checking; `#[flux::assumed]` injects user axioms; raw-pointer stdlib wrappers (`RVec`) are trusted specs |
| **Thrust (`coord-e/thrust` `187a1e975edece50b896f1ee478ab665d7a1204e`, PLDI 2025)** | Dependent refinement types over prophetic borrows (`^r` future value in refinement predicates) | Compiles `rustc` MIR into higher-order / first-order Constrained Horn Clauses (`thrust-chc`) solved by Z3 Spacer or Hoice | Trusts MIR-to-CHC lowering, solver `SAT` verdict, and `#[thrust::trusted]` / `#[thrust::callable]` extern assumptions |
| **RustHorn (`hopv/Rust-horn` `4823f8f9c8e9e1deca71fdffe3c38061ae519c52`, ESOP 2020)** | First-order prophetic representation of safe mutable borrows (`<cur, final>` pairs) | Directly emits SMT-LIB2 `(set-logic HORN)` clauses from MIR CFG blocks (`src/chc.rs`, `src/mir_to_chc.rs`) | Restricted to safe Rust without raw pointers or interior mutability; trusts Spacer/Hoice CHC `SAT` model |
| **Prusti (`prusti/prusti` `0d4a8d497ac1e540d48ef50a031d53b4e3ae36e2`)** | `#[requires]`, `#[ensures]`, `#[pledge]` (on-expiry borrow postconditions), and `#[pure]` functions | Encodes MIR borrow lifetimes and places into Viper Silver (`prusti-viper/src/encoder/`) checked by Silicon or Carbon | `#[trusted]` functions, `#[assumed]` specifications, and unverified Rust-to-Viper encoding in `prusti-viper` |

**Implication for a Lean 4 VC Boundary**: Neither Flux (`liquid-fixpoint`), Thrust, nor RustHorn emits foundational proof certificates. However, when a CHC solver (`Spacer` / `Hoice`) returns `SAT` with an explicit model interpreting each uninterpreted relation symbol $P_i(\bar{x})$ as a closed first-order formula $\varphi_i(\bar{x})$, a Lean 4 verifier can **untust the CHC solver** by substituting $\varphi_i$ into the initiation, transition, and query clauses and discharging the resulting quantifier-free implications in Lean (`omega` / `bv_decide` / `simp`).

---

### 6. Recursive Contract Inference and Verified Callee Lifecycles (`2026`)

**Basis: source (`support/recursive-inference-and-verified-callee-lifecycles-2026/source-identities.json`, `support/recursive-inference-and-verified-callee-lifecycles-2026/coverage.json`).**

1. **RustHorn (`hopv/Rust-horn` `4823f8f9`)**: Assigns each function $f$ an uninterpreted CHC summary predicate $\text{Summary}_f(\text{args}, \text{prophs}, \text{ret})$. Recursive calls emit recursive Horn rule applications; the CHC solver infers the inductive summary automatically, but provides no termination guarantee (partial correctness only unless a ranking function is added).
2. **Stainless (`EPFL-LARA/stainless` `399c34a06df8e88679f0985131e8a59a28ab9b3f`)**: Verifies recursive Scala functions via unfolding (`unfold` tactic in `core/src/main/scala/stainless/verification/`) coupled with explicit or inferred lexicographic termination measures (`MeasureInference.scala`, `TerminationChecker.scala`). Once a callee's contract and measure are verified, callers may either use the opaque postcondition or unfold the definition up to a fuel bound.
3. **System FR (`epfl-lara/SystemFR` `325bd745` & `90300f26`, arXiv `1904.03482v2`)**: Mechanizes in Coq (`ReducibilityDefinition.v`, `Soundness.v`) a semantic reducibility-candidate model for terminating recursive refinement types, proving that call-by-value evaluation of well-typed recursive terms with decreasing measures satisfies their refinement types without getting stuck.
4. **SAW Compositional Callee Lifecycle (`GaloisInc/saw-script` `27a7ae98256544b55a7a3ce4ce620c1a7889713b`)**:
   - `mir_verify mod fn overrides sat_check spec` symbolically executes `fn` while replacing any call in `overrides` with its `MIRSpec` summary, and returns a proven `MIRSpec` handle.
   - `mir_unsafe_assume_spec mod fn spec` returns an identical `MIRSpec` type handle **without verifying `fn`**, allowing unverified specifications to be passed into `overrides` unless the build script tracks provenance of every `MIRSpec` token.

---

### 7. RefinedC/Lithium, CN, Fulminate, and Bennet Result Interfaces (`2026`)

**Basis: source (`support/refinedc-lithium-and-cn-result-interfaces-2026/source-identities.json`, `support/refinedc-lithium-and-cn-result-interfaces-2026/coverage.json`).**

| Tool & Pinned Identity | Verification Foundation | How Specifications & Resources Are Checked | Result Artifact & Trust Boundary |
|---|---|---|---|
| **RefinedC + Lithium (`iris/refinedc` `2e89846baeaa7f65cbe17e3ae7297a8ed5b4feca`, PLDI 2021)** | Foundational Rocq + Iris (`caesium` C semantics + `lithium` goal-directed solver) | Ownership & refinement annotations (`[[rc::...]]`) are lowered into Rocq obligations discharged by Lithium (`liRStep`), producing full Rocq `.vo` proof objects | Kernel-checked Rocq proof over Caesium C semantics; trusts the frontend C-to-Caesium AST generator |
| **CN (`rems-project/cn` `b4a2f009234d9c80380dbf95a9b2325e36a4705d` + Cerberus `c8c085d4`, POPL 2023)** | Linear resource-typing kernel over Cerberus Core + SMT (`Z3`/`CVC5`) | Infers resource spine and frame transformations (`Owned<T>`, `Block<T>`, iterated `each`), emitting pure quantifier-free SMT constraints for value refinements | Paper supplement (`popl23_defns.pdf`, `popl23_soundness.pdf`) proves soundness of the explicit kernel calculus; executable OCaml checker and SMT solver are trusted |
| **Fulminate (POPL 2025, DOI `10.1145/3704879`)** | Runtime executable specification testing from CN contracts | Compiles CN separation-logic pre/postconditions into C runtime ownership-tracking instrumentation (`fulminate`) that checks concrete test runs for memory/contract violations | Bug-finding / dynamic testing witness for unverified or foreign C callers/callees; not a static proof across all inputs |
| **Bennet (`bennet.pdf`, `sha256: d479fda5...`)** | Randomized property-based test-generator synthesis from CN specs | Synthesizes backtracking C input generators directly from CN spatial/pure preconditions to fuzz C functions under Fulminate/CN | Automated counterexample search before or alongside static proof; does not establish universal validity |

---

### 8. Resource Logics, Intrinsic Effects, and Compilation Interfaces (`VST`, `CompCert`, `Bedrock2`, `Low*`, `Steel`/`PulseCore`)

**Basis: source and primary literature (`PrincetonUniversity/VST` `3c37c2e2`, `AbsInt/CompCert` `74cbdbf0`, `mit-plv/bedrock2` `757f17c6`, `FStarLang/FStar` `e2b5042f`, Low* arXiv `1703.00053v6`).**

1. **VST (`PrincetonUniversity/VST` `3c37c2e2b574e23aee8fdd1684aa0ffed227491e`, `veric/semax_prog.v:1967–1989`)**:
   - `semax_prog_rule` connects a closed Verifiable C proof (`semax_prog Espec G prog V`) to step-indexed operational safety (`∀ n, jsafeN (@OK_spec Espec) ge n z c m`) over CompCert Clight (`Clight.semantics2`).
   - External functions are governed by `Espec : OracleKind`; a local C body proof does not verify foreign calls outside `Espec`.
2. **CompCert (`AbsInt/CompCert` `74cbdbf0e86ecbfa39a5ca8f248f77fb2f974cb6`, `driver/Compiler.v:446–452`, `common/Smallstep.v:1298–1312`)**:
   - `transf_c_program_correct` proves `backward_simulation (Csem.semantics p) (Asm.semantics tp)` whenever `transf_c_program p = OK tp`.
   - In `common/Smallstep.v:1298–1312`, the backward simulation diagram explicitly assumes `safe L1 s1` (that the source C configuration does not exhibit undefined behavior). CompCert preserves safety and trace refinement **only** after a source verification tool (such as VST) discharges source safety.
3. **Bedrock2 (`mit-plv/bedrock2` `757f17c6083bf8d43b5293a0db545c8d0aa32a13`, `compiler/src/compiler/Pipeline.v:682–730`)**:
   - `compiler_correct` and `compiler_correct_wp` (`line 764`) compose source weakest preconditions (`WeakestPrecondition.v`) with compilation to RISC-V machine code (`MetricRiscvMachine`), proving that if the source WP holds and the target machine has a valid aligned stack (`machine_ok`), the RISC-V machine `runsTo` a state satisfying the source memory/register postcondition and preserving non-caller-saved registers.
4. **Low* (`arXiv:1703.00053v6`, DOI `10.1145/3110261`)**:
   - Theorem D.6 and Theorem D.7 (PDF p. 37) establish safety preservation and bisimulation from the modeled $\lambda\text{Low}^*$ calculus (with stack frames and manual buffers) to $\text{C}^*$, and Theorem E.27 (PDF p. 66) preserves safe $\text{C}^*_2$ traces into CompCert Clight.
   - **Native ABI Caveat (Footnote 12, PDF p. 63)**: The paper notes that erasing ghost fields from passed-by-value structs alters physical struct layout relative to the System V x86 ABI (which passes byte sequences including padding).
5. **F* Steel and PulseCore (`FStarLang/FStar` `e2b5042ffd8272ad6287e4ad8748d8e52dadd93d`, `pulsecore.pdf`, `steel.pdf`)**:
   - Following migration of `FStarLang/pulse` (`c35460e0`) into the main `FStarLang/FStar` repository (`pulse/`), `pulse/lib/core/PulseCore.Semantics.fst:127–258` defines effectful computations `m` and `run_alt` indexed by stratified heap propositions (`slprop`), returning in F*'s divergence effect `Dv` while preserving the interpreted heap invariant.
   - `pulse/src/checker/Pulse.Checker.Base.fsti:208–235` threads universe, precondition, and postcondition equalities through the Pulse checker, which still relies on F*'s core typechecker and Z3 for SMT obligations.

---

### 9. Static/Abductive Inference and Compositional Result Meaning (`MIRAI`, `Infer`, `SeaHorn`, `SMACK`, `Viper`, `Prusti`, `SAW`)

**Basis: source (`support/inference-and-compositional-result-interfaces-2026/source-evidence.json`, `support/inference-and-compositional-result-interfaces-2026/historical-infer-evidence.json`, `support/inference-and-compositional-result-interfaces-2026/literature.json`, `support/inference-and-compositional-result-interfaces-2026/coverage.json`).**

| Tool & Pinned Revision | Inspected Source Modules | Exact Result / Summary Representation | Additional Obligations Before Using Output as a Sound Proof |
|---|---|---|---|
| **MIRAI (`endorlabs/MIRAI` `aae0a56f91d9a0a62073bb86e7b2c9793cefc24b`)** | `checker/src/summaries.rs`, `call_visitor.rs`, `documentation/Overview.md` | `Summary` (`is_computed`, `is_incomplete`, preconditions, side effects, postcondition). Default diagnostic policy suppresses incomplete-function warnings and treats incomplete branches as unreachable | Must reject any summary with `is_incomplete == true`, bound recursion widening, and discharge all assumed preconditions |
| **Historical Infer Bi-Abduction (`facebook/infer` `99464c01da5809e7159ed1a75ef10f60d34506a4`, POPL 2009)** | `infer/src/biabduction/Prover.mli`, `Tabulation.mli`, `Rearrange.mli`; POPL 2009 (`popl09.pdf`, Thms. 5 & 9) | `ImplOK` returns inferred missing anti-frame $M$ and leftover frame $F$ (`Δ * M ⊢ H * F`); `Tabulation.mli` separates call success, failed precondition, missing spec, and skipped callee | Independently check that $\Delta * M$ is satisfiable at function entry, verify entailment $\Delta * M \vdash H * F$ in a sound logic, and forbid skipped callees |
| **Current Infer Pulse & Rust (`facebook/infer` `5aac32c06952a2f3a6b7043e91457920f065833b`)** | `PulseSummary.mli`, `PulseExecutionDomain.mli`, `infer/src/rust/RustMir2Textual.ml` | Disjunctive pre/post summaries distinguishing `ContinueProgram`, `ExceptionRaised`, `ExitProgram`, `AbortProgram`, `LatentAbortProgram`, and `LatentInvalidAccess`. Rust frontend lowers Charon ULLBC to Textual and maps unsupported generic types to `Void` | Experimental bug-finding / latent-error summary only; does not cover full Rust type/borrow semantics |
| **SeaHorn (`seahorn/seahorn` `892780176731ec8e97bbb9f6b172fcacd77a8ff4`)** | `README.md`, `lib/seahorn/HornSolver.cc` | `SAT` / `UNSAT` / `UNKNOWN` over LLVM 14 CHCs under configurable memory precision (`reg`, `ptr`, `mem`), with optional invariant model extraction on `UNSAT` | Re-check extracted CHC invariant model on all initiation, consecution, and error clauses, and account for LLVM lowering / memory abstraction |
| **SMACK (`smackers/smack` `0a64471206645c250164e8df6027f5a5193e5e85`)** | `share/smack/top.py`, `README.md` | Outcome categories (`verified`, `assertion`, `deref`, `free`, `memleak`, `overflow`, `rust-panic`, `timeout`, `unknown`) parameterized by loop-unroll bound or `--modular` mode | Bounded verification holds only up to `--unroll` depth; modular mode requires checking Boogie contracts |
| **SAW / Crux MIR (`GaloisInc/saw-script` `27a7ae98256544b55a7a3ce4ce620c1a7889713b`)** | `crux-mir-comp/DESIGN.md`, `src/SAWScript/CruxMIR/Override.hs:314–339` | `gather_assumes` / `gather_asserts` build a `MIRSpec` (discarding assertions made during spec construction!). At call replacement, `Override.hs:314–339` **asserts** the spec's preconditions and **assumes** its postconditions | Installing an override verifies the caller *relative to* the spec; the callee itself must be separately verified via `mir_verify` (not `mir_unsafe_assume_spec`), and all mutated memory outside post-points-to clauses must be framed |

---

## Boundaries

1. **Source & Certificate Scope**: With the exception of the executable Boogie/Viper failure-reflection witness (`support/boogie-viper-failure-reflection-certificates-2021-2024/failure_witness.py`) and the matrix consistency checker (`support/check_matrix.py`), the external verifiers surveyed in this report (Dafny, Boogie, Viper, F*, Why3, Flux, Thrust, RustHorn, Prusti, Stainless, System FR, RefinedC, CN, VST, CompCert, Bedrock2, MIRAI, Infer, SeaHorn, SMACK, SAW) were inspected at their pinned source commits and published artifacts without executing full end-to-end tool builds in this environment.
2. **Forward VCG Soundness vs. Diagnostic Completeness**: Validating a Boogie or Viper translation certificate (CAV 2021, PLDI 2024) proves that a valid target VC implies source program correctness (`WpSound`), but does not guarantee VC completeness (`WpComplete`) or the absence of spurious abstract counterexamples when verification fails (`support/boogie-viper-failure-reflection-certificates-2021-2024/failure-results.json`).
3. **Historical vs. Current Infer**: The bi-abduction prover interface (`infer/src/biabduction/Prover.mli`) was inspected at historical Infer release `99464c01da5809e7159ed1a75ef10f60d34506a4` (`v0.17.0`); that directory is absent (HTTP `404`) at current Infer revision `5aac32c06952a2f3a6b7043e91457920f065833b`, which instead provides Pulse (`PulseSummary.mli`, `PulseExecutionDomain.mli`) and an experimental Charon-based Rust frontend (`RustMir2Textual.ml`).
4. **CN Kernel vs. Executable Tool**: CN's POPL 2023 soundness proof (`popl23_defns.pdf`, Appendix A sections 1 and 5; `popl23_soundness.pdf`, Appendix B sections 1, 9, and 10) covers the explicitly annotated, let-normalized kernel calculus assuming valid SMT entailments; it does not mechanically verify CN's OCaml spine-inference implementation or external Z3/CVC5 solver.

---

## Evidence

All source snapshots, commit/tag inventories, historical release matrices, and executable witnesses are stored in `support/`:

- **Dafny, Boogie, & Viper (`2005–2026` & Current Source Review)**:
  - `support/dafny-boogie-viper-obligation-boundaries-2005-2026/evidence-map.json`
  - `support/official-source-observation.json`, `support/matrix.json`, `support/check_matrix.py`, `support/frozen-cohort.csv`, `support/version-inventory-ebcdcad-581.csv`, `support/baseline-report-paths.txt`
  - Git ref logs: `support/dafny-refs.txt`, `support/dafny-release-tag-refs.txt`, `support/boogie-refs.txt`, `support/boogie-release-tag-refs.txt`, `support/silver-refs.txt`, `support/silver-release-tag-refs.txt`, `support/silicon-refs.txt`, `support/carbon-refs.txt`, `support/viperserver-refs.txt`, `support/viperserver-release-tag-refs.txt`
  - Pinned file snapshots: `support/snapshots/dafny/Source/DafnyCore/Verifier/BoogieGenerator.cs`, `support/snapshots/boogie/README.md`, `support/snapshots/silver/src/main/scala/viper/silver/verifier/VerificationResult.scala`, `support/snapshots/silicon/README.md`, `support/snapshots/carbon/README.md`, `support/snapshots/viperserver/README.md` (and `support/dafny-boogie-viper-current-source-review/`)
- **Boogie & Viper Certificate Failure-Reflection Witness (`2021–2024`)**:
  - `support/boogie-viper-failure-reflection-certificates-2021-2024/failure_witness.py` and `support/boogie-viper-failure-reflection-certificates-2021-2024/failure-results.json`
- **F* and Meta-F* (`2019–2026` & `2026.09.27` Source Review)**:
  - `support/fstar-extensible-proof-automation-trust-boundaries-2019-2026/evidence-map.json`
  - `support/fstar-20260927-current-source-review/official-source-identity.json`, `support/fstar-20260927-current-source-review/matrix.json`, `support/fstar-20260927-current-source-review/check_matrix.py`, `support/fstar-20260927-current-source-review/frozen-cohort.csv`, `support/fstar-20260927-current-source-review/version-inventory-ebcdcad-581.csv`, `support/fstar-20260927-current-source-review/baseline-report-paths.txt`, `support/official-source-identity.json`
- **Why3 Durable Proof Sessions (`2011–2025`)**:
  - `support/history-matrix.json` and `support/source-map.json` (also in `support/why3-durable-proof-sessions-2011-2025/`)
- **Refinement Types, CHC Solvers, & Recursive Callee Lifecycles (`2026`)**:
  - `support/refinement-horn-and-lean-vc-boundaries-2026/source-evidence.json`, `support/refinement-horn-and-lean-vc-boundaries-2026/prusti-source-evidence.json`, `support/refinement-horn-and-lean-vc-boundaries-2026/additional-source-evidence.json`, `support/refinement-horn-and-lean-vc-boundaries-2026/coverage.json`
  - `support/recursive-inference-and-verified-callee-lifecycles-2026/source-identities.json` and `support/recursive-inference-and-verified-callee-lifecycles-2026/coverage.json`
- **RefinedC/Lithium, CN, & Static/Abductive Inference (`2026`)**:
  - `support/refinedc-lithium-and-cn-result-interfaces-2026/source-identities.json` and `support/refinedc-lithium-and-cn-result-interfaces-2026/coverage.json`
  - `support/inference-and-compositional-result-interfaces-2026/source-evidence.json`, `support/inference-and-compositional-result-interfaces-2026/historical-infer-evidence.json`, `support/inference-and-compositional-result-interfaces-2026/literature.json`, and `support/inference-and-compositional-result-interfaces-2026/coverage.json`

---

## Revalidation

1. **Boogie/Viper Failure-Reflection Witness**:
   - Run `python3 support/boogie-viper-failure-reflection-certificates-2021-2024/failure_witness.py` and confirm output matches `support/boogie-viper-failure-reflection-certificates-2021-2024/failure-results.json` (`WpSound: true`, `WpComplete: false`, `SpuriousAbstractCounterexample: true`, `ReflectedFailureSound: false`).
2. **Dafny/Boogie/Viper and F* Source-Review Matrices**:
   - Run `python3 support/dafny-boogie-viper-current-source-review/check_matrix.py` and `python3 support/fstar-20260927-current-source-review/check_matrix.py` from their respective subdirectories (or verify `support/matrix.json` and `support/fstar-20260927-current-source-review/matrix.json` against `support/official-source-observation.json` and `support/fstar-20260927-current-source-review/official-source-identity.json`).
3. **Why3 Session Matrix & Pinned Source Identities**:
   - Validate all 22 release entries in `support/history-matrix.json` and verify the Git commit and blob SHA-1 hashes in `support/*/source-evidence.json` and `support/*/source-identities.json`.
