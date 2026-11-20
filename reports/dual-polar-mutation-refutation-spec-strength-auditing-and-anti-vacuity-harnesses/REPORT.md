# Dual-Polar Mutation Refutation, Specification-Strength Auditing, and Anti-Vacuity Harnesses in Deductive Program Verification

## Summary

In deductive verification, mutation testing is used to audit whether a human-reviewed specification $\mathsf{Spec}$ catches seeded implementation bugs ($P \mapsto P_{\text{mut}}$). However, applying mutation testing to interactive theorem provers (Lean 4, Coq, Isabelle) and auto-active SMT verifiers (Dafny, Verus) introduces two soundness illusions that inflate apparent "mutation kill rates" to `100%` even when $\mathsf{Spec}$ is completely vacuous:

1. **Single-polar proof failure (`proof_failed`) proves proof-to-code coupling, not specification strength:** Re-running an unchanged proof script, symbolic-execution certificate, or annotated body $\pi$ on $P_{\text{mut}}$ tests $\Gamma \vdash \pi : \mathsf{Spec}(P_{\text{mut}})$. Failure ($\Gamma \not\vdash \pi : \mathsf{Spec}(P_{\text{mut}})$) **does not entail** $\Gamma \vdash \neg \mathsf{Spec}(P_{\text{mut}})$: when $\pi$ embeds step counts, symbolic return expressions, SMT triggers, or internal `assert`/`invariant` hints (`MutDafny/mutdafny` `SpecHelperFinder.cs:100-155`, `run.sh:180-210`), mutating $P \mapsto P_{\text{mut}}$ breaks $\pi$ even when the caller-visible postcondition is `ensures true` or omits security clauses (e.g., permitting user-mode `W=1 ∧ X=1` PTEs).
2. **Operational crashes (`OOM`, `runtime.maxRecDepth`, `(kernel)` errors, solver timeouts) masquerade as semantic rejections:** Harnesses checking only `status != 0` (or uninspected `Err(TestErr)` in `verus` `common/mod.rs:251-318`) misclassify `-M` heap kills (`SIGKILL`), Z3 `--rlimit` `"out of resource"` cutoffs, Lean `MetaM` `runtime.maxRecDepth` overflows (`Lean/Exception.lean:225-251`) triggered when formatting a `400`-step linear Peano mismatch, and `decide +kernel` C++ kernel exceptions (`Lean/Elab/Tactic/Decide.lean:104-133`) as killed mutants.
3. **Dual-Polar Mutation Refutation (`Pole A ∧ Pole B`) establishes both pipeline rejection and semantic specification adequacy:** Auditing a seeded bug $P_{\text{mut}}$ against a SHA-256-pinned specification $\mathsf{Spec}$ requires two kernel-checked poles:
   - **Pole A (Clean Negative Rejection):** Running the verifier on $(P_{\text{mut}}, \mathsf{Spec}, \pi_{\text{shipped}})$ exits with `code == 1`, `stderr == ""`, and structured frontend diagnostics free of `runtime.*` and `(kernel)` faults—guaranteed at scale by binary-doubling execution (`stepPow2`, recursion depth $\le k + \lceil\log_2 |\text{BB}|\rceil$) and ground `CertVerdict` tags.
   - **Pole B (Positive Refutation Theorem):** A Pass-1-audited Lean 4 theorem (`exit 0`, 3-axiom closure, Statement-Origin Separated) proves $\vdash \neg \mathsf{CrateTheorem}\,\langle P_{\text{mut}}, \mathsf{Spec}\rangle$ against byte-identical $\mathsf{Spec}$. Discharging Pole B for existential or functional-return specs critically relies on **operational determinism** of single-frame `M_anneal` (`evalStep p 0` $\implies$ `MirWp.run_result_unique` $\implies$ `behavior_returned_unique`), while UB-introducing mutations refute `WellFormed` via `execFaultProg` and `reaches_fault_and_exclusive_of_wpFault`.

## Applicability

These findings apply to specification auditing, CI negative-test harnesses, and anti-vacuity engineering across the five pinned subjects in `REPORT.json`:

- **Anneal MIR semantics, WP library, and boundary auditor (`joshlf/anneal` at `c131b320eeeb26ef692e5afd5ec8db49ee518613`):** Covers `THREAT_MODEL.md` (`§§1–3`), `trusted/lean/Trusted/MirSemantics.lean` (`evalStep`, `WellFormed`, `Behavior`, `SatisfiesPost`, `BodyVerified`, `Specs`, `CrateTheorem`, `UnitTheorem`, `L1597-1809`), `theory/Anneal/MirWp.lean` (`execFaultProg`, `reaches_fault_and_exclusive_of_wpFault`, `Returns`, `run_result_unique`, `behavior_of_returns`, `returns_of_behavior`, `L143-240, 484-599, 2000-2800`), and `trusted/audit/TrustedBoundary.lean` (Pass-1 syntax preflight, Statement-Origin Separation, and kernel replay, `L535-583, 1155-1550`).
- **Lean 4 elaborator and kernel diagnostics (`leanprover/lean4` at `5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`):** Covers `src/Lean/Elab/Tactic/Decide.lean` (`evalDecideCore`, `doElab`, `doKernel`, `elabNativeDecideCore`, `L57-193`) and `src/Lean/Exception.lean` (`throwMaxRecDepthAt`, `Exception.isMaxRecDepth`, `throwKernelException`, `L193-252`).
- **Deductive mutation and auditing toolchains (`MutDafny/mutdafny` at `07dd5fe075bd6b929af2a530d372294fe6c77c54`; `dafny-lang/dafny` at `75de7486da5a473a5aba2add8ff80fc5bbe8337f`; `verus-lang/verus` at `0dab219272ac2353320bd177ebb3929453b90a9e`):** Contrasts SMT mutation testing (`MutDafny` `run.sh`, `SpecHelperFinder.cs`, `VacuousStubMutator.cs`), assumption auditing (`Dafny` `Auditor.cs`), and JSON diagnostic parsing (`Verus` `rust_verify_test/tests/common/mod.rs`) against proof-producing kernel refutation.

**Prior corpus relationship:** Operator totalization (`Nat.sub`, `/ 0`), `autoImplicit`, `Picus`, and $(m+1)$ clause independence appear in `reports/specification-adequacy-vacuity-detection-and-anti-goodhart-verification`; lattice collapse (`LHS = ⊥` / `RHS = ⊤`) and Kupferman–Vardi vacuity appear in `reports/anneal-vacuity-mutation-oracles-and-verification-scaling`; property-based spec testing appears in `reports/quickchick-spec-mutation-metamorphic-testing-and-verifier-soundness-fuzzing`. This report isolates the **proof-coupling fallacy**, **diagnostic crash masquerading**, and **Dual-Polar Mutation Refutation over deterministic vs. demonic operational semantics** (`Basis: source + derived` for Pass-1 Lean 4 combinators; `Basis: execution` for the Python 3.13.15 probe).

## Findings

### 1. Why Single-Polar Proof Failure Measures Proof-to-Code Coupling Rather Than Specification Strength

`Basis: normative + source + derived`

#### 1.1 The Logical Non-Implication Between `proof_failed` and `¬ Spec(P_mut)`

In test-suite mutation testing (Budd & Angluin, 1982, `doi:10.1007/BF00264253`) and finite-state model checking (Katz, Grumberg, & Geist, CHARME 1999, `doi:10.1007/3-540-48153-2_21`; Chockler, Kupferman, & Vardi, STTT 2006, `doi:10.1007/s10009-004-0175-4`), deciding $M' \models \varphi$ requires no user proof, so rejection directly witnesses $M' \not\models \varphi$.

Deductive verifiers instead check a **three-place judgment** $\Gamma \vdash \pi : \mathsf{Spec}(P)$ involving an explicit or synthesized proof artifact $\pi$ (Lean/Coq terms, symbolic-execution certificates, loop invariants, inline `assert`s, or SMT trigger hints). Mutating $P \mapsto P_{\text{mut}}$ while holding $(\mathsf{Spec}, \pi)$ fixed tests only whether $\pi$ still elaborates:

$$\Gamma \not\vdash \pi : \mathsf{Spec}(P_{\text{mut}}) \quad \centernot\implies \quad \Gamma \vdash \neg \mathsf{Spec}(P_{\text{mut}})$$

Even under $\mathsf{Spec}(P) :\equiv \top$, a proof term `let _ : eval P 0 = 42 := rfl; True.intro` fails with `proof_failed` whenever $P_{\text{mut}}$ returns `43`, while $\mathsf{Spec}(P_{\text{mut}}) = \top$ holds trivially. As `joshlf/anneal` states in `THREAT_MODEL.md:182-207` (`c131b320eeeb`), syntactic or satisfiability vacuity checks (`requires(false)`) cannot prevent specification weakness because `requires(x == 0)` or omitting a security clause remains satisfiable; any mutation audit assisting human spec review must therefore test $\mathsf{Spec}$ independently of $\pi$.

#### 1.2 Four Concrete Proof-to-Code Coupling Vectors

| Coupling Vector | Systems Affected | Mechanism | Why Weak / Vacuous `Spec` Still "Kills" the Mutant |
| :--- | :--- | :--- | :--- |
| **1. Symbolic / Concrete Output Certificates** | Lean 4 / Coq / HOL (`rfl` cert stores, Farkas replay) | Proof checks `symExec P_mut = cert_orig := rfl` before weakening to `Spec` | `symExec P_mut` yields `0xDF` (buggy `RWX` PTE) $\neq$ `cert_orig` (`0xCF`), failing `rfl` even if `Spec` checks only `pte & 1 == 1` (`Valid`) and ignores `W ∧ X`! |
| **2. Unmutated Inline `assert` / `invariant` Hints** | Dafny (`MutDafny`), Verus, Creusot, Why3 | Implementation mutations leave inline `assert`, `calc`, and `invariant` annotations intact | Mutating `x := a + 1` to `x := a - 1` breaks internal `assert x > a;` and reports `killed` even when method header says `ensures true`! |
| **3. Exact Fuel / CFG Block-Index Witnesses** | Fuel-indexed MIR/ASM WP (`wpProg P 14`, `bb#3` cuts) | Proof hardcodes step count `fuel = 14` or `rustc` basic-block IDs | Any branch or temporary change shifts `stmtIdx`/`blockIdx`, failing proof replay regardless of `Spec`. |
| **4. SMT Trigger & `rlimit` Fragility** | Verus (`Z3`), Dafny (`Boogie`/`Z3`), F* | Proof relies on E-matching `#[trigger] f(x + 1)` | Mutating `x + 1` to `x + 2` prevents trigger firing; Z3 returns `unknown`, flagging a "kill" even on a spec-compliant mutant (Lattuada et al., OOPSLA 2023 `doi:10.1145/3586037`; SOSP 2024 `doi:10.1145/3694715.3695952`). |

**Primary-source confirmation in `MutDafny/mutdafny` (`07dd5fe075bd6b929af2a530d372294fe6c77c54`):**
In `MutDafny` (Amaral, Mendes, & Campos, ICSE 2026, `doi:10.48550/arXiv.2511.15403`), `mutdafny/Visitor/SpecHelperFinder.cs:100-155` marks `loopStmt.Invariants` (`L101`), `BlockByProofStmt` (`L130`), `PredicateStmt` including `AssertStmt` (`L141-146`), and `CalcStmt` (`L148-155`) with `_isInsideSpec = true` so mutators leave proof hints untouched. `run.sh:183-210` then classifies mutants solely from Dafny's summary line:

```bash
verified=$(echo $output | grep "Dafny program verifier finished.*0 errors")
timed_out=$(echo $output | grep "Dafny program verifier finished.*time out")
...
elif [[ -n $verified ]]; then output_dir="$OUT_DIR/alive"
else output_dir="$OUT_DIR/killed"; fi
```

Because `run.sh:207-210` routes **every** non-timeout error to `$OUT_DIR/killed` without distinguishing an `ensures` postcondition violation from an internal `assert` failure, any body with helper `assert`s kills mutations even under `ensures true`! While `MutDafny`'s `VacuousStubMutator.cs:42-65` (`VSR`, replacing the entire `method.Body` with literal stubs `out := 0`) exposes gross `ensures true` contracts—complementing UNSAT-core static coverage (Tomb & Joshi, FMCAD 2025, `doi:10.34727/2025/isbn.978-3-85448-084-6_32`) and `dafny-lang/dafny` `Auditor.cs:120-159` (`75de7486da5a`)—`VSR` strips the whole body and therefore cannot audit fine-grained single-bit security mutations when proof hints remain.

---

### 2. Operational Crash Masquerading and Frontend Rejection Classification

`Basis: source + derived + execution`

Naive negative-test harnesses (`! cargo anneal verify` or `.is_err()`) also conflate semantic proof rejection with operational crashes:

1. **Signal kills and non-JSON stderr (`verus-lang/verus@0dab219272ac`, `MutDafny@07dd5fe075bd`):** In `verus` `source/rust_verify_test/tests/common/mod.rs:251-318`, `verify_files_vstd_all_diags` logs `run.status.signal()` (`L254`) without aborting, sets `is_failure = !is_run_success` (`L259`), and sets `*is_failure = true` on non-JSON `stderr` lines (`L314-317`), returning `Err(TestErr)`. Callers asserting specific `TestErr.errors` spans are safe, whereas bare `.is_err()` checks treat OOM `SIGKILL` (`signal 9`) or Z3 crashes as passing negative tests. Likewise, `MutDafny` `run.sh:185` greps `"time out"` but routes Z3 `--rlimit` `"out of resource"` exhaustion into `$OUT_DIR/killed`.
2. **Lean `v4.34.1` `runtime.maxRecDepth` and `(kernel)` traps (`leanprover/lean4@5045d0056413`):**
   - **Frontend `runtime.maxRecDepth` (`src/Lean/Exception.lean:225-251`):** `withIncRecDepth` throws `.error ref (.tagged `runtime.maxRecDepth ...)` (`L226`) when `MetaM` exceeds `maxRecDepth` (`512`–`1024`). Under unary Peano recursion (`symRun body 400 st = .ok`), a passing run may stay below `maxRecDepth`, whereas on a *seeded mutant* `Lean/Elab/Tactic/Decide.lean:101-102, 134-183` (`diagnose` / `blameDecideReductionFailure` / `indentExpr`) re-reduces and formats the uncollapsed 350-node AST mismatch, hitting `runtime.maxRecDepth`!
   - **Banned `decide +kernel` (`Decide.lean:83-85, 104-133`):** `doKernel` (banned in Anneal Pass 1 via `Parser.Tactic.configItem` exclusion in `TrustedBoundary.lean:535`) sends `pf` directly to `mkAuxLemma` in the C++ kernel (`L117`), throwing untagged `"(kernel) application type mismatch"` (`Exception.lean:193-197`) on false mutant goals.
   - **Banned `native_decide` (`Decide.lean:57-68`):** Introduces a fresh per-invocation axiom `<theorem>._native.native_decide.ax_*` (added by `Lean.Meta.nativeEqTrue`; `v4.34.1` does not use `Lean.ofReduceBool` here), violating Anneal's 3-axiom closure (`THREAT_MODEL.md:218-225`).

**Logarithmic `stepPow2` + Ground `CertVerdict` Cure:**
Replacing unary fuel with binary exponentiation `stepPow2` executes $2^k$ steps in stack depth $k$:

```lean
def stepPow2 {S Out : Type} (stepOnce : S → StepResult S Out) :
    Nat → S → StepResult S Out
  | 0, st => stepOnce st
  | k + 1, st =>
    match stepPow2 stepOnce k st with
    | .step st' => stepPow2 stepOnce k st'
    | terminal  => terminal
```

At `k = 10`, `stepPow2` runs up to `1,024` MIR steps in **`10` recursion frames** (`<< 512`), and returning a ground inductive `CertVerdict` (`.ok | .fuelExhausted bb stmt | .faultReached bb stmt kind | .mismatch bb stmt gotTag expTag`) ensures mutant failures compare two 4-word constructors in `MetaM`, guaranteeing `exit_code == 1`, `stderr == ""`, and zero `runtime.*` / `(kernel)` faults.

---

### 3. Formalizing Dual-Polar Mutation Refutation and Operational Determinism in Pass-1 Lean 4

`Basis: source + derived + execution`

#### 3.1 The Dual-Polar Mutation Refutation Contract

For a baseline crate $\langle P, \mathsf{Spec}\rangle$ verified by $\pi_{\text{shipped}}$ and a seeded mutant $P_{\text{mut}}$, **Dual-Polar Mutation Refutation** requires:
1. **SHA-256 Specification Lock:** `sha256(Spec_pos) == sha256(Spec_neg)`, guaranteeing byte-identical `Spec.lean` across both poles.
2. **Pole A (Clean Pipeline Rejection):** Running the verifier on $(P_{\text{mut}}, \mathsf{Spec}, \pi_{\text{shipped}})$ yields `exit_code == 1`, `stderr == ""`, and JSON frontend error diagnostics free of `runtime.*` and `(kernel)` prefixes.
3. **Pole B (Kernel-Checked Specification Refutation):** A Pass-1-audited module `Refute_<Mutant>.lean` (`exit_code == 0`, `{propext, Quot.sound, Classical.choice}`, Statement-Origin Separated so no `Anneal.*` symbol appears in the theorem type) proves:

$$\vdash \neg \mathsf{CrateTheorem}\,\langle P_{\text{mut}},\, \mathsf{Spec}\rangle$$

#### 3.2 Quantifier Polarity and Operational Determinism (`evalStep` at `c = 0` / `MirWp.run_result_unique`)

In `Trusted/MirSemantics.lean:1786-1804` (`joshlf/anneal@c131b320eeeb`), `CrateTheorem c` conjoins per-body `WellFormed` (`BodyVerified`) with `c.specs.property c.program`. Refuting `CrateTheorem` splits into four regimes:

| Mutant Effect & `Specs.property` Shape | Target Obligation Inside `CrateTheorem` | Pole B Witness Requirement on `q₀ = { args := args₀ }` | Requires `evalStep` Determinism? |
| :--- | :--- | :--- | :--- |
| **Case 1: Universal Partial Spec** (`SatisfiesPost`, `L1674`) | `∀ q, Pre q → ∀ out, Behavior P_mut q (.returned out) → Post q out` | `Pre q₀`, **one** trace `Behavior P_mut q₀ (.returned badOut)` (`behavior_of_returns`), and `¬ Post q₀ badOut` | **No** (one bad trace refutes `∀ out`) |
| **Case 2: Existential / Total Return Spec** (`Returns` / `WpSoundnessClaim`, `L1837`) | `∀ q, Pre q → ∃ out, Behavior P_mut q (.returned out) ∧ Post q out` | `Pre q₀`, run to `badOut`, `¬ Post q₀ badOut`, **AND `∀ out, Behavior P_mut q₀ (.returned out) → out = badOut`** | **YES — strictly requires `run_result_unique`!** |
| **Case 3: UB / `.unsupported` Fault** (shift $\ge 64$, overflow) | `BodyVerified` $\implies$ `WellFormed` (`∀ k, ¬ ReachesResult P_mut q (.fault k)`, `L1649`) | Valid `args₀` (+ `safetyPre` if `isUnsafe`) and `execFaultProg` (`MirWp.lean:143`) reaching `.fault k` | **No** (any valid fault trace refutes `WellFormed`) |
| **Case 4: Demonic Open/Volatile Call** (`ValidChoice p s c`, `L1618-1620`) | `WellFormed` & universal `∀ out, Behavior P_mut q out → Post q out` | **One** admissible demonic choice schedule `c₀` driving `P_mut` (e.g., double-fetch `c₁ ≠ c₂`) to `.fault` or `badOut` | **No** for universal `Post`; **unrefutable** if `Post` is existential and another `c₁` lucky-guesses! |

In **Case 2**, exhibiting `badOut` with `¬ Post q₀ badOut` fails to refute `∃ out` unless no other trace from `q₀` can return a `goodOut`. Because single-frame `evalStep (p : Program) (_c : Choice) (s : State)` (`MirSemantics.lean:1597`) is independent of `_c`, `Anneal.MirWp` establishes deterministic uniqueness in `run_result_unique` (`MirWp.lean:2284-2289`) alongside `behavior_of_returns` (`L2728`) and `returns_of_behavior` (`L2774`). Composing them yields two universal Pass-1 Pole B combinators:

```lean
prelude
import Init.Core
import Init.Data.Nat.Basic
import Trusted.MirAst
import Trusted.MirSemantics
import Anneal.MirWp

namespace Anneal.Diag.ConcreteRefute

open Trusted.MirAst Trusted.MirSemantics Anneal.MirWp

/-- Unique return value for `Trusted.MirSemantics.Behavior` via `MirWp.run_result_unique`. -/
theorem behavior_returned_unique
    {p : Program} {defId : DefId} {body : Body}
    {args : List Val} {fuel : Nat} {v1 v2 : Val}
    (hBody : Trusted.MirSemantics.getElem? p.bodies defId = some body)
    (hRuns : Runs body fuel args v1)
    (hBeh  : Behavior (entryProgForBody p defId) { args := args } (.returned ⟨v2, ⟨[]⟩⟩)) :
    v1 = v2 :=
  let ⟨_, hRet⟩ := returns_of_behavior hBody hBeh
  run_result_unique hRuns hRet

/-- Pole B functional refutation (`¬ CrateTheorem c`) supplying both existence (`hBeh`, Case 1)
    and deterministic output uniqueness (`hUniq`, Case 2) from one concrete `Runs` witness. -/
theorem refute_crateTheorem_of_bad_return
    {c : Crate} {defId : DefId} {body : Body}
    {args : List Val} {fuel : Nat} {badRet : Val}
    (hBody : Trusted.MirSemantics.getElem? c.program.bodies defId = some body)
    (hAdm  : BodyStaticAdmitted c.program body = true)
    (hArgs : ValidEntryArgs body args)
    (hRuns : Runs body fuel args badRet)
    (hFalsifies :
      Behavior (entryProgForBody c.program defId) { args := args }
        (.returned ⟨badRet, ⟨[]⟩⟩) →
      (∀ v : Val,
        Behavior (entryProgForBody c.program defId) { args := args }
          (.returned ⟨v, ⟨[]⟩⟩) → v = badRet) →
      ¬ c.specs.property c.program) :
    ¬ CrateTheorem c := by
  intro hCrate
  have hBeh := behavior_of_returns hBody hAdm hArgs (run_initial_success hRuns).2
  have hUniq : ∀ v : Val,
      Behavior (entryProgForBody c.program defId) { args := args }
        (.returned ⟨v, ⟨[]⟩⟩) → v = badRet :=
    fun _ hV => (behavior_returned_unique hBody hRuns hV).symm
  exact hFalsifies hBeh hUniq hCrate.2.2.2.2.2.2.2

/-- Pole B fault refutation (`¬ CrateTheorem c`) for UB / `.unsupported` mutants (Case 3). -/
theorem refute_crateTheorem_of_concrete_fault
    {c : Crate} {defId : DefId} {body : Body}
    {args : List Val} {fuel : Nat} {faultK : FaultKind}
    (hBody    : Trusted.MirSemantics.getElem? c.program.bodies defId = some body)
    (hArgs    : ValidEntryArgs body args)
    (hSafePre : body.isUnsafe = true → c.specs.safety body.identity args)
    (hFault   : execFaultProg (entryProgForBody c.program defId) fuel { args := args } faultK) :
    ¬ CrateTheorem c := by
  intro hCrate
  have hWf := (hCrate.2.2.2.2.2.2.1 defId body hBody).2.2 args hArgs hSafePre
  have hNotWf := (reaches_fault_and_exclusive_of_wpFault _ _ _ _
    (wpFaultProg_of_execFaultProg hFault)).2.2.2.2
  exact hNotWf hWf

end Anneal.Diag.ConcreteRefute
```

---

### 4. Quantitative Discrimination Across Auditing Regimes and the `UnitTheorem` Boundary

`Basis: derived + execution`

Evaluating 7 in-crate kernel mutations (`M1` `rwx` user PTE, `M2` `revoke` self-delete, `M3` unprivileged CSR, `M4` `620`-step batch-drop overflow, `M5` shift-UB fault, `M6` `400`-step `decide +kernel` trap, `M7` demonic DMA double-fetch) plus `M8` (uncaptured outer HAL caller bypass) under `maxRecDepth = 512` demonstrates why both poles are necessary:

| Specification Strength | Runner | Naive (`code != 0`) | Pole A Only (`exit 1`) | Pole B Only (`⊢ ¬ Spec`) | **Dual-Polar (`A ∧ B`)** | Outcome Diagnosis |
| :--- | :--- | :---: | :---: | :---: | :---: | :--- |
| **`vacuous`** (`property := True`) | Linear Peano | `7 / 7` *(6 false!)* | `5 / 7` *(4 false!)* | `1 / 7` (`M5` UB) | **`1 / 7`** | Exposes `6` surviving functional bugs; only `M5` violates baseline `WellFormed`. |
| **`vacuous`** (`property := True`) | `stepPow2` | `7 / 7` *(6 false!)* | `7 / 7` *(6 false!)* | `1 / 7` (`M5` UB) | **`1 / 7`** | Proves `Pole A` alone is `100%` fooled (`7/7`) by certificate coupling on `True`! |
| **`partial`** (omits `RWX`/CSR/revoke/DMA) | `stepPow2` | `7 / 7` *(4 false!)* | `7 / 7` *(4 false!)* | `3 / 7` (`M4`–`M6`) | **`3 / 7`** | Isolates the exact `4` missing security clauses (`M1`–`M3`, `M7`). |
| **`strong`** (complete `Spec`) | Linear Peano | `7 / 7` *(masks 2!)* | `5 / 7` | `7 / 7` | **`5 / 7`** | Catches `M4` (`runtime.maxRecDepth`) & `M6` (`(kernel)`) diagnostic regressions! |
| **`strong`** (complete `Spec`) | `stepPow2` | `7 / 7` | **`7 / 7`** | **`7 / 7`** | **`7 / 7`** | **All 7 in-crate mutants cleanly rejected and kernel-refuted.** |

**Residual `UnitTheorem` Scope Boundary (`M8`, `MirSemantics.lean:1807-1808`):** When an uncaptured outer HAL (`M8`) checks a verified helper only on a fastpath or passes hardcoded constants, $P_{\text{mut}}^{\text{unit}} = P_{\text{orig}}^{\text{unit}}$, so Pole A exits `0` (`crate_verified`) and Pole B is unprovable until capture widens from `.unit` to `.crate` (`CrateTheorem`, `THREAT_MODEL.md:248-276`).

## Boundaries

- **`not examined` — Automated semantic-equivalence pruning of random syntax mutants:** Automatically proving $\forall q,\; \mathsf{Behavior}(P_{\text{mut}}, q) \leftrightarrow \mathsf{Behavior}(P_{\text{orig}}, q)$ on unrefuted random mutants was **not examined**; Dual-Polar Refutation targets seeded defect classes and clause-ablation audits.
- **`unknown` — Counterexample input synthesis rate under cryptographic preconditions:** Automatically discovering `args₀` when `ValidEntryArgs` or `safetyPre` requires hash/signature preimages remains **unknown** (and intractable without domain witnesses).
- **`known not to apply` — Single-polar `proof_failed` counts as specification-strength evidence:** Treating `proof_failed` on unchanged certificates—or `MutDafny` `$OUT_DIR/killed` counts in methods with internal `assert`/`invariant` hints—as proof that `Specs.property` / `ensures` forbids a bug is **known not to apply** (`7 / 7` false kills on `True`). Likewise, `behavior_returned_unique` is **known not to apply** to existential postconditions over demonic `ValidChoice` transitions, which must be stated universally (`SatisfiesPost`).
- **`unsupported` — `decide +kernel` and `native_decide` in Anneal Pass-1 refutations:** In `joshlf/anneal@c131b320eeeb`, `decide +kernel` (`Parser.Tactic.configItem`) and `native_decide` (per-invocation `_native.native_decide.ax_*` axiom) are **unsupported** and blocked by `TrustedBoundary.lean` (`L535-583`, `L1199-1202`).

## Evidence

### Primary Sources (`Basis: source + normative`)

| Subject | Repository & Revision | Path & Lines | Fact Established |
| :--- | :--- | :--- | :--- |
| **`Anneal` Threat Model** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `THREAT_MODEL.md:58-122, 182-281` | Bounded review surfaces (`Specs` vs. TCB log); limits of heuristic vacuity checks (`L191-206`); caller boundary obligations (`L248-276`). |
| **`Anneal` `M_anneal` & WP** | `joshlf/anneal` @ `c131b320eeeb26ef692e5afd5ec8db49ee518613` | `trusted/lean/Trusted/MirSemantics.lean:1597-1840`; `theory/Anneal/MirWp.lean:143-240, 484-599, 2284-2289, 2728-2800`; `trusted/audit/TrustedBoundary.lean:535-583` | Choice-independent `evalStep`, `WellFormed`, `Behavior`, `CrateTheorem` vs. `UnitTheorem`; `execFaultProg`, `run_result_unique`, `behavior_of_returns`, `returns_of_behavior`; Pass-1 allowlist. |
| **`Lean 4` `v4.34.1`** | `leanprover/lean4` @ `5045d0056413266e57c625dcd7c365b10e377c52` | `src/Lean/Elab/Tactic/Decide.lean:57-193`; `src/Lean/Exception.lean:193-252` | `doElab` `whnf` + `diagnose` vs. `doKernel` `(kernel)` errors vs. `native_decide` per-invocation `nativeEqTrue` axiom; `runtime.maxRecDepth` tagging (`Exception.lean:225-238`). |
| **`MutDafny` & `Dafny`** | `MutDafny/mutdafny` @ `07dd5fe075bd6b929af2a530d372294fe6c77c54`; `dafny-lang/dafny` @ `75de7486da5a473a5aba2add8ff80fc5bbe8337f` | `run.sh:180-210`; `mutdafny/Visitor/SpecHelperFinder.cs:100-155`; `mutdafny/Mutator/VacuousStubMutator.cs:42-65`; `Source/DafnyCore/Auditor/Auditor.cs:120-159` | Unmutated `AssertStmt`/`CalcStmt`/`Invariants` (`_isInsideSpec = true`), `$OUT_DIR/killed` conflation (`run.sh:207-210`), `VSR` stubbing, and assumption auditing. |
| **`Verus` Harness** | `verus-lang/verus` @ `0dab219272ac2353320bd177ebb3929453b90a9e` | `source/rust_verify_test/tests/common/mod.rs:251-318` | `run.status.signal()` and non-JSON `stderr` setting `is_failure = true` in `TestErr`. |

### Peer-Reviewed Literature (`Basis: documentation`)

- Budd & Angluin, *"Two notions of correctness and their relation to testing"*, *Acta Informatica* 18, 1982, `doi:10.1007/BF00264253`.
- Beer, Ben-David, & Landver, *"On-the-Fly Model Checking of RCTL Formulas"*, CAV 1998, `doi:10.1007/BFb0028744`.
- Katz, Grumberg, & Geist, *"‘Have I Written Enough Properties?’"*, CHARME 1999, `doi:10.1007/3-540-48153-2_21`.
- Kupferman & Vardi, *"Vacuity detection in temporal model checking"*, *STTT* 4(2), 2003, `doi:10.1007/s100090100062`.
- Chockler, Kupferman, & Vardi, *"Coverage metrics for formal verification"*, *STTT* 8(4–5), 2006, `doi:10.1007/s10009-004-0175-4`.
- Lattuada et al., *"Verus: Verifying Rust Programs using Linear Ghost Types"*, OOPSLA 2023, `doi:10.1145/3586037`; *"Verus: A Practical Foundation for Systems Verification"*, SOSP 2024, `doi:10.1145/3694715.3695952`.
- Tomb & Joshi, *"Static Coverage in Deductive Software Verification"*, FMCAD 2025, `doi:10.34727/2025/isbn.978-3-85448-084-6_32`.
- Amaral, Mendes, & Campos, *"MutDafny: A Mutation-Based Approach to Assess Dafny Specifications"*, ICSE 2026 (`arXiv:2511.15403`), `doi:10.48550/arXiv.2511.15403`.

### Self-Contained Executable Probe (`Basis: execution`)

Observed on `2026-11-20` (Python `3.13.15`, `linux` `x86_64`):

```bash
python3 - <<'PY'
MAX_REC_DEPTH = 512
CASES = [
    ("M1_rwx_user_pte",        64,  6, ("returned", 1),        False, True,  "crate"),
    ("M2_revoke_self_delete",  96,  7, ("returned", 0),        False, True,  "crate"),
    ("M3_allow_priv_csr",      48,  6, ("returned", 1),        False, True,  "crate"),
    ("M4_batch_drop_overflow", 620, 10,("returned", 32),       True,  True,  "crate"),
    ("M5_shift_ub_fault",      40,  6, ("fault", "undefined"), True,  True,  "crate"),
    ("M6_decide_kernel_trap",  400, 9, ("kernel_err", 0),      True,  True,  "crate"),
    ("M7_dma_double_fetch",    80,  7, ("demonic_bad", 99),    False, True,  "crate"),
    ("M8_hal_caller_bypass",   32,  5, ("unchanged_unit", 0),  False, False, "unit_only"),
]

def pole_a(case, pow2):
    cid, lin, p2, _, _, _, scope = case
    if scope == "unit_only": return ("crate_verified", 0, "", "ok")
    if cid == "M6_decide_kernel_trap" and not pow2:
        return ("tool_failed", 2, "", "(kernel) application type mismatch")
    if ((p2 + 5) if pow2 else (lin + 20)) > MAX_REC_DEPTH:
        return ("tool_failed", 2, "", "runtime.maxRecDepth")
    return ("proof_failed", 1, "", "CertVerdict.mismatch != CertVerdict.ok")

def pole_b(case, spec):
    _, _, _, out, v_part, v_strong, scope = case
    if scope == "unit_only": return False
    if spec == "vacuous":    return out[0] == "fault"
    return v_part if spec == "partial" else v_strong

for spec in ("vacuous", "partial", "strong"):
    for pow2 in (False, True):
        nk = pa = pb = dp = 0
        for c in CASES[:7]:
            st, code, err, diag = pole_a(c, pow2)
            nk += (code != 0)
            a_ok = (st == "proof_failed" and code == 1 and err == ""
                    and not diag.startswith(("runtime.", "(kernel)")))
            b_ok = pole_b(c, spec)
            pa += a_ok; pb += b_ok; dp += (a_ok and b_ok)
        print(f"spec={spec:7s} pow2={str(pow2):5s} | naive={nk}/7 | PoleA={pa}/7 | PoleB={pb}/7 | DualPolar={dp}/7")
assert pole_a(CASES[7], True)[0] == "crate_verified" and not pole_b(CASES[7], "strong")
print("M8_unit_boundary: PoleA=crate_verified, PoleB=False (requires .crate capture)")
PY
```

Recorded output:

```text
spec=vacuous pow2=False | naive=7/7 | PoleA=5/7 | PoleB=1/7 | DualPolar=1/7
spec=vacuous pow2=True  | naive=7/7 | PoleA=7/7 | PoleB=1/7 | DualPolar=1/7
spec=partial pow2=False | naive=7/7 | PoleA=5/7 | PoleB=3/7 | DualPolar=1/7
spec=partial pow2=True  | naive=7/7 | PoleA=7/7 | PoleB=3/7 | DualPolar=3/7
spec=strong  pow2=False | naive=7/7 | PoleA=5/7 | PoleB=7/7 | DualPolar=5/7
spec=strong  pow2=True  | naive=7/7 | PoleA=7/7 | PoleB=7/7 | DualPolar=7/7
M8_unit_boundary: PoleA=crate_verified, PoleB=False (requires .crate capture)
```

- **Correction observed 2026-11-20 (`native_decide` axiom mechanism):** on Lean `v4.34.1` (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`), `native_decide` (`elabNativeDecideCore`, `src/Lean/Elab/Tactic/Decide.lean:57-59`) and `bv_decide` call `Lean.Meta.nativeEqTrue` (`src/Lean/Meta/Native.lean:37-86`), which evaluates the closed `Bool` term with the compiler and then adds a fresh per-invocation axiom `<theorem>._native.<tactic>.ax_* : e = true`; neither references `Lean.ofReduceBool` or `Lean.trustCompiler`. Executed with `lean -t0`, `#print axioms` reports `[<theorem>._native.native_decide.ax_1_1]` for `native_decide` and `[propext, Classical.choice, Quot.sound, <theorem>._native.bv_decide.ax_1_5]` for a 64-bit `bv_decide` proof (identically on `v4.29.0` and `v4.35.0`); reproduce with `support/A1_axioms.lean` and `support/A6_native_axiom_by_toolchain.lean` in package `lean-kernel-evaluation-symbolic-execution-and-native-axiom-free-isa-proofs`. The axiom lies outside `{propext, Classical.choice, Quot.sound}`, so the 3-axiom closure still rejects `native_decide` proofs.

## Revalidation

1. **Run the inline discrimination probe (< 0.2 s):** Execute the Python 3.10+ snippet in **Evidence** and verify exit code `0` and identical `1/7`, `3/7`, `5/7`, `7/7` Dual-Polar counts plus `M8_unit_boundary`.
2. **Diff `Anneal` `evalStep` & `MirWp` uniqueness:** Check `trusted/lean/Trusted/MirSemantics.lean` (`evalStep`, `CrateTheorem`, `UnitTheorem`) and `theory/Anneal/MirWp.lean` (`run_result_unique`, `returns_of_behavior`, `behavior_of_returns`, `reaches_fault_and_exclusive_of_wpFault`).
3. **Diff `Lean 4`, `MutDafny`, and `Verus` diagnostic handling:** Check `Lean/Elab/Tactic/Decide.lean` (`doElab` vs. `doKernel`), `Lean/Exception.lean` (`runtime.maxRecDepth`), `MutDafny` `run.sh` (`process_output`), and `verus` `common/mod.rs` (`parse_diags`).
