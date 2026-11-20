# Verified bidirectional and algorithmic type checkers versus elaborator–kernel splits: exact soundness/completeness statements, where completeness breaks, and trusted-base costs

## Summary

- **Completeness of a verified checker is always relative to an algorithmic presentation, and the bridge is usually bidirectional typing.** MetaRocq proves its PCUIC checker sound *and* complete by going through a bidirectional judgment: `infering_typing` (bidirectional ⇒ declarative) and `typing_infering` (`Σ ;;; Γ |- t : T -> ∑ T', Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ ⊢ T' ≤ T`), with checking defined as inference followed by cumulativity (`check_Cumul`). Its executable checker returns either a typing derivation or a *proof that no type exists* (`TypeError_comp (t : type_error) (a : A -> False)`). Termination, and therefore completeness of the executable function, is conditional on a strong-normalization hypothesis (`NormalizationIn`) that cannot be discharged inside Rocq for PCUIC itself.
- **CakeML's inferencer is sound and complete for Hindley–Milner because principal types exist**; Tan, Owens and Kumar name GADTs as a feature with "no solution for now", and the earlier CakeML paper verified soundness only. **Lean4Lean re-implements Lean's (non-bidirectional) kernel in Lean** and proves soundness-style `WF` theorems for `inferType`, `checkType`, and `isDefEq` against a formal typing judgment; completeness is not claimed ("Lean's typechecker is known to not be complete"), Lean is not strongly normalizing, and checking is fuel-bounded.
- **Production refinement/ownership checkers already split search from checking.** LiquidHaskell's `cconsE` (check) falls back to `consE` (synthesize) plus a deferred subtyping constraint solved by a Horn solver; Flux runs a shape pass, then a refinement pass that emits a constraint with Horn variables (κ), then the fixpoint solver (or an optional Lean backend), and inserts *ghost statements* (`Fold`, `Unfold`, `Unblock`, `PtrToRef`) from a separate points-to analysis before checking. Oxide's reference type checker decides borrow safety with a prefix-disjointness rule on places, letting shared–shared loans coexist and unique loans coexist only on disjoint places.
- **Measured on Lean 4 (v4.34.1): the trusted check is not always cheaper than the untrusted search.** For a small `omega` goal, the tactic took 2.97–3.65 ms while the kernel's check of the produced proof took 9.25–14.7 ms (6 measurements); for `simp` the order reversed (0.41–0.67 ms search vs 0.28–0.35 ms check). The elaborator supplies coercions and binder types (`def f1 := fun x => x` fails; `#print` shows `@Nat.cast Int instNatCastInt n` inserted), and the kernel independently rejects an ill-typed declaration handed to it directly.
- **Trusted-code size versus untrusted-code size (non-blank lines, pinned `main` of Lean 4):** kernel `src/kernel` 7,274 lines in 35 files versus `src/Lean/Elab` 71,635 and `src/Lean/Meta` 102,295. Lean4Lean's executable kernel core (`TypeChecker.lean` 863, `Inductive/` 805, `Primitive.lean` 561) is accompanied by 21,649 lines of verification and 6,079 of metatheory; MetaRocq's `safechecker/theories` is 16,965 non-blank lines on top of 88,217 in `pcuic/theories`.
- **Running Lean4Lean (pinned revision, Lean v4.33.0-rc2) on Lean's own `Init` library flagged 25 of 630 modules** with "constant has already been declared" for auxiliary constants (`congr_simp`, `eq_1`/`eq_2`, `eq_def`, `induct_unfolding`), while single-module checks of `Init.Prelude` (1,975 declarations), `Init.Core`, `Init.Data.List.Basic`, and `Lean4Lean.TypeChecker` succeeded in about 1–2 s each. The cause was not investigated; it is recorded as an observation about the replay harness at that revision, not as a kernel soundness result.

## Applicability

This report concerns **type checkers that are themselves verified (or re-implemented for verification) and the split between an untrusted elaborator/solver and a small trusted checker**, for dependent type theories (PCUIC/Rocq, Lean), ML (CakeML), and refinement/ownership type systems (LiquidHaskell, Flux, Oxide).

| Subject | Revision examined | Use |
| --- | --- | --- |
| `MetaRocq/metarocq` | `51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56` | source; line counts |
| `CakeML/cakeml` (`compiler/inference/`, `semantics/typeSystemScript.sml`) | `2874b664e10939a3ee462215b2e068c89c1f70eb` | source; line counts |
| `digama0/lean4lean` | `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` | source; line counts; built and executed (`lake build lean4lean`, toolchain `leanprover/lean4:v4.33.0-rc2`) |
| `leanprover/lean4` | `main` at `920a9e5f4f5e9b509f4d879d1b58a1f4d645f3d0` (line counts); `v4.34.1` at `5045d0056413266e57c625dcd7c365b10e377c52` (executed elaborator/kernel probe); `v4.33.0-rc2` at `d8b18978322de05a8f3dba51ef03cf5461676c17` (toolchain for executed Lean4Lean) | source counts; execution |
| `ucsd-progsys/liquidhaskell` | `7c809b687388dc837c53b9db29b0a70b7165b716` | source; line counts |
| `flux-rs/flux` | `ac24831e4f3dc570ad991751ff65bea0826ed446` | source; line counts |
| `aatxe/oxide` (OCaml reference checker) | `203e42936b273e7f1351ce1d0ea5bb8d1b0dc5c1` | source |

The subjects are compared, not combined. Papers (DOIs in `REPORT.json`) supply the theorem statements' published form and all performance figures not measured here. Execution host class: x86-64 Intel Xeon @ 2.60 GHz, 96 logical CPUs, ~236 GiB RAM, Debian; Lean runs were executed inside a systemd user scope with a memory cap and `LEAN_NUM_THREADS=96`. Timings are host-specific and single-digit repetitions.

Version scope: theorem statements and line ranges are exact for the pinned revisions only. The MetaRocq JACM paper describes "MetaCoq 1.2 for Coq 8.16"; numbers it reports (code size, slowdown) are not re-measured for the pinned revision. Lean4Lean paper figures were measured by its author on a different machine and Mathlib revision.

## Findings

### 1. Vocabulary that the statements below use

- **Soundness** of an algorithm A w.r.t. a declarative system D: A accepts ⇒ D derives. **Completeness**: D derives ⇒ A accepts (possibly up to a relation on the output, e.g. `T' ≤ T`). For bidirectional systems, Dunfield & Krishnaswami (ACM CSUR 54(5), 2021) define completeness as "every use of a rule in the type assignment system can be 'matched' by some rule in the bidirectional system" and note it "is sometimes called annotatability": "if Γ ⊢ e : A ..., then (1) there exists e′ ⊒ e such that Γ ⊢ e′ ⇐ A, and (2) there exists e′′ ⊒ e such that Γ ⊢ e′′ ⇒ A".
- **The Pfenning recipe:** "If the rule is an introduction rule, make the principal judgment checking. If the rule is an elimination rule, make the principal judgment synthesizing." Consequence: "an annotation is required on a subterm if and only if an introduction form meets an elimination form."
- **Completeness up to annotation erasure** (Dunfield & Krishnaswami, ICFP 2013, Theorem 1): "If Ψ ⊢ e : A then there exists e′ such that Ψ ⊢ e′ ⇒ A and |e′| = e"; their algorithmic completeness is Theorem 15. They restrict to predicative polymorphism because "the subtyping relation induced by instantiation is undecidable for impredicative polymorphism".
- **Partial completeness** (Pierce & Turner, TOPLAS 2000): "Since we are dealing with a partial type inference technique, we cannot expect a completeness property at this point"; Theorem 4.4.2 holds only for fully typed terms.
- **Relative completeness** (Rondon, Kawaguchi, Jhala, PLDI 2008, Theorem 2): "If Infer(Γ, e, Q) = Failure then there is no S s.t. Γ ⊢Q e : S" — completeness relative to the qualifier set Q, under "a conservative but decidable notion of subtyping".

Basis: documentation (papers cited under **Evidence**).

### 2. MetaRocq: bidirectional typing as the completeness bridge

**Bidirectional judgments.** `pcuic/theories/Bidirectional/BDTyping.v` defines mutually inductive `infering` (`Σ ;;; Γ |- t ▹ T`), `infering_sort` (`▹□`), `infering_prod` (`▹Π`), `infering_indu` (`▹{ind}`), and `checking` (`◃`) (lines 28–160). The *only* checking rule is the mode switch:

```coq
with checking `{checker_flags} (Σ : global_env_ext) (Γ : context) : term -> term -> Type :=
| check_Cumul t T T':
  Σ ;;; Γ |- t ▹ T ->
  Σ ;;; Γ |- T <= T' ->
  Σ ;;; Γ |- t ◃ T'
```

(lines 148–152). The three "constrained inference" judgments (`▹□`, `▹Π`, `▹{ind}`) are where reduction to a head form happens; Lennon-Bertrand (ITP 2021) introduced this intermediate "to handle the presence of computation in types".

**Exact theorems at the pinned revision:**

```coq
(* BDToPCUIC.v 411–412 : soundness of inference *)
Theorem infering_typing `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wf Σ) :
  wf_local Σ Γ -> Σ ;;; Γ |- t ▹ T -> Σ ;;; Γ |- t : T.
(* BDToPCUIC.v 419–420 : soundness of checking needs the target to be a type *)
Theorem checking_typing `{checker_flags} (Σ : global_env_ext) Γ t T (wfΣ : wf Σ) :
  wf_local Σ Γ -> isType Σ Γ T -> Σ ;;; Γ |- t ◃ T -> Σ ;;; Γ |- t : T.
(* BDFromPCUIC.v 391–392 : completeness *)
Lemma typing_infering `{checker_flags} {Σ : global_env_ext} {wfΣ : wf Σ} {Γ t T} :
  Σ ;;; Γ |- t : T -> ∑ T', Σ ;;; Γ |- t ▹ T' × Σ ;;; Γ ⊢ T' ≤ T.
(* BDUnique.v 311–313 : inferred types are unique up to joinable reduction *)
Theorem infering_unique `{checker_flags} {Σ} (wfΣ : wf Σ) {Γ} (wfΓ : wf_local Σ Γ) {t T T'} :
  Σ ;;; Γ |- t ▹ T -> Σ ;;; Γ |- t ▹ T' ->
  ∑ T'', Σ ;;; Γ ⊢ T ⇝ T'' × Σ ;;; Γ ⊢ T' ⇝ T''.
```

**Executable checker.** In `safechecker/theories/PCUICTypeChecker.v`, inference has type `typing_result_comp ({ A : term & forall Σ (wfΣ : abstract_env_ext_rel X Σ), ∥ Σ ;;; Γ |- t ▹ A ∥ })` (lines 337–338), and `bdcheck` is literally "infer, then check cumulativity" (lines 374–378). The result type makes completeness part of the interface (`PCUICErrors.v` lines 396–398):

```coq
Inductive typing_result_comp (A : Type) :=
| Checked_comp (a : A)
| TypeError_comp (t : type_error) (a : A -> False).
```

**The normalization hypothesis.** Every checking entry point is parameterized by `normalization_in : forall Σ, wf_ext Σ -> Σ ∼_ext X_ext -> NormalizationIn Σ` (e.g. `PCUICSafeChecker.v` lines 311–319; `PCUICTypeChecker.v` line 244), where `NormalizationIn Σ := forall Γ t, welltyped Σ Γ t -> Acc (cored Σ Γ) t` (`pcuic/theories/PCUICSN.v` lines 44–48). The JACM 2025 paper: "this is actually the only place where we need to use this axiom"; "the equivalence between the declarative and algorithmic presentations of PCUIC is axiom free."

**Explicit incompleteness left in the code.** Variance checking for cumulative inductive types: "Incompleteness: this is an underapproximation of cumulativity of the contexts: in general we should allow unfolding and reduction to happen before comparing the types of arguments. However in many cases it will be sufficient." (`PCUICSafeChecker.v` lines 1579–1582).

**What changed between the two MetaRocq papers.** "Coq Coq Correct!" (POPL 2020) proved soundness only: "However, we have not proven completeness of type inference." The JACM 2025 version adds "the proof of completeness, which is done by considering bidirectional type checking as an intermediate specification", excludes "the module system, template polymorphism and η-conversion", and notes decidability relies on "Church-style syntax, i.e., using annotated abstractions". Completeness work found real kernel bugs: an incompleteness bug in Coq's matching on cumulative inductives (Lennon-Bertrand 2021) and a bug that "affected cumulative inductive types from their introduction in Coq 8.11 until its discovery and fix in Coq 8.14" (JACM 2025).
Basis: source + documentation.

### 3. CakeML: complete inference because principal types exist

At the pinned revision, `compiler/inference/proofs/README.md` describes `inferCompleteScript.sml` as proving "if there is a type for the program, then the type inferencer will find a type (the most general type)". The statements (HOL4):

```sml
(* inferSoundScript.sml 1355–1360 *)
Theorem infer_prog_sound:
   !idecls ienv prog st1 idecls' ienv' st2 tenv.
    infer_prog idecls ienv prog st1 = (M_success (idecls',ienv'), st2) ∧
    env_rel tenv ienv
    ⇒
    type_prog T (convert_decls idecls) tenv prog (convert_decls idecls') (ienv_to_tenv ienv')
(* inferCompleteScript.sml 1430–1440 (conclusion abbreviated) *)
Theorem infer_ds_complete:
   type_ds T tenv ds ids tenv' ∧ env_rel tenv ienv ∧ ... ⇒
   ∃g mapped_tenv' ienv' st2.
     infer_ds ienv ds st1 = (M_success ienv', st2) ∧ tenv_equiv (remap_tenv g tenv') mapped_tenv' ∧ ...
```

Non-blank line counts at the pinned revision: inferencer `inferScript.sml` 1,317 and `unifyScript.sml` 2,908; declarative `semantics/typeSystemScript.sml` 994; proofs `inferPropsScript.sml` 4,116, `inferCompleteScript.sml` 1,807, `infer_eCompleteScript.sml` 2,876, `inferSoundScript.sml` 1,362, `infer_eSoundScript.sml` 1,209, `envRelScript.sml` 1,196, `type_dCanonScript.sml` 2,014, `type_eDetermScript.sml` 627. Derived: completeness-specific files (1,807 + 2,876 = 4,683) are 1.8× the soundness-specific files (1,362 + 1,209 = 2,571); the whole proof set (15,207, counting `inferPropsScript.sml`) is 3.6× the inferencer plus unifier (4,225).

Published qualifications (Tan, Owens, Kumar, IFL 2015): principal types are "the critical property that supports a complete inference algorithm"; "For other popular features, including GADTs, there is no solution for now, and one must be resigned to using the type inference algorithm as the most precise specification of the type system"; the value restriction interacts badly with the soundness induction. Kumar et al. (POPL 2014) verified soundness only ("we have not verified completeness of the inferencer"), giving low priority to completeness because "in practice, we find the inferencer does not fail on the programs we expect to have types."
Basis: source + execution (line counts) + derived + documentation.

### 4. Lean4Lean: a verified re-implementation of a non-bidirectional kernel

**Algorithm shape.** The checker is not bidirectional ("The kernel's typechecking algorithm is fairly straightforward. It is not bidirectional", Carneiro, TYPES 2025). Instead it has a *trust mode* flag: `inferType (e : Expr) (inferOnly := true)`; "If `inferOnly := false`, this function throws an error whenever `e` is not typeable according to Lean's algorithmic typing judgment ... Setting `inferOnly := true` optimizes to avoid unnecessary checks in the case that `e` is already known to be well-typed." (`Lean4Lean/TypeChecker.lean` lines 136–141). In the application case, checking mode infers the function and argument types and calls `isDefEq dType aType`; infer-only mode just walks the function type (`inferApp`) (lines 286–305). `isDefEq` "does not do any typechecking of its own" and relies on its inputs already being well typed (lines 172–180).

**What is proved** (`Lean4Lean/Verify/TypeChecker.lean`):

```lean
nonrec theorem inferType.WF {c : VContext} {s : VState} (he : c.TrExprS e e') :
    M.WF c s (inferType e inferOnly) fun ty _ => ∃ ty', c.TrTyping e ty e' ty'      -- 210–212
theorem checkType.WF {c : VContext} {s : VState} (h1 : e.FVarsIn (· ∈ c.vlctx.fvars)) :
    M.WF c s (checkType e) fun ty _ => ∃ e' ty', c.TrTyping e ty e' ty'            -- 215–216
nonrec theorem isDefEq.WF {c : VContext} {s : VState}
    (he₁ : c.TrExprS e₁ e₁') (he₂ : c.TrExprS e₂ e₂') :
    M.WF c s (isDefEq e₁ e₂) fun b _ => b → c.IsDefEqU e₁' e₂'                     -- 218–221
```

These are soundness statements (success ⇒ the translated term is typed / defeq in the formal theory). In infer-only mode the caller must supply the translation (`hinf : inferOnly = true → ∃ e', c.TrExprS e e'`, lines 202–208). The paper lists unfinished parts: inductive types and primitive projections, unique typing and injectivity, the level-equality algorithm, and environment modification (`addDecl`). At the pinned revision, `grep -rw sorry` finds 9 occurrences in `Lean4Lean/Theory` (21 files) and 18 in `Lean4Lean/Verify` (36 files).

**Deliberate divergences relevant to completeness** (`divergences.md` at the pinned revision): `reduceBool` is unsupported ("This would involve implementing verified compilation"; `TypeChecker.lean` lines 453–458 throw for `reduceBool`/`reduceNat` natives); Lean4Lean's level normalizer "decide[s] level equality and `≥` for *more* pairs than either the standard library or the kernel — it accepts declarations the kernel rejects for reasons of level incompleteness, never the other way around"; `unsafe`/`partial` bodies are checked with the constant added as an axiom, so it rejects e.g. `unsafe def foo : Nat := (fun (_ : foo = 1) => 1) rfl`, which the C++ kernel accepts. `bugs-found.md` lists three kernel problems found through the formalization: one Lean Zulip discussion ("Soundness bug: hasLooseBVars is not conservative") and two upstream issues, https://github.com/leanprover/lean4/issues/10475 and https://github.com/leanprover/lean4/issues/10511.

**Termination.** "the Lean type theory is known not to terminate" (Coquand–Abel counterexample to strong normalization); Lean4Lean bounds work with fuel (`FuelConfig`; `whnf'` throws `.deterministicTimeout` at zero fuel, lines 519–541). The paper: the fixed limit (1000) "turns out to be sufficient for checking all of Mathlib".
Basis: source + documentation.

**Execution (Lean4Lean at the pinned revision, `lake build lean4lean` then `lake env .lake/build/bin/lean4lean <MOD>`):**

| Target | Declarations | Wall s (3 runs) | Peak RSS (KiB) | Result |
| --- | --- | --- | --- | --- |
| `Init.Prelude` | 1,975 | 1.34 / 1.01 / 0.95 | 108,240 | ok |
| `Init.Core` | 1,035 | 0.95 / 0.90 / 0.90 | 110,064 | ok |
| `Init.Data.List.Basic` | 711 | 1.08 / 1.13 / 1.10 | 117,576 | ok |
| `Lean4Lean.TypeChecker` | 321 | 1.76 / 1.99 / 1.79 | 1,173,696 | ok |
| prefix `Init` (630 `.olean` modules, parallel tasks) | — | 30.82 (first run) | 24,151,560 | exit 1: 25 modules reported `(kernel) constant has already been declared` |

A bare invocation that fails immediately took 0.72 s, an upper bound on fixed `lake env` + wrapper startup included in each row. The 25 flagged names were auxiliary constants: 10 `congr_simp`, 6 `eq_2`, 5 `eq_1`, 3 `induct_unfolding`, 1 `eq_def` (e.g. `List.take.eq_2` in `Init.Data.List.Impl`). The error is raised by Lean4Lean's environment layer (`Lean4Lean/Environment/Basic.lean` line 57, `throw <| .alreadyDeclared env n`) while replaying a module's constants over its imports (`Lean4Lean/Replay.lean` lines 284–305). The tool also printed per-declaration timings above one second (maximum observed 2,059 ms for a proof in `Init.Data.Vector.Extract`). The build itself took 35.4 s wall including toolchain download and dependency clone.
Basis: execution.

Published performance (Carneiro, TYPES 2025, Figure 2, single-threaded, i7-1255U): lean4checker (C++ kernel) vs Lean4Lean — Lean 37.01 s vs 44.61 s (×1.21), Batteries 32.49 s vs 45.74 s (×1.40), Mathlib + Batteries + Lean 44.54 min vs 58.79 min (×1.32).

### 5. Lean 4: what the elaborator computes and the kernel re-checks (execution, v4.34.1)

| Probe | Observed |
| --- | --- |
| `def f1 := fun x => x` | `error(lean.inferBinderTypeFailed): Failed to infer type of binder x` |
| `def f2 : Nat → Nat := fun x => x` | accepted (expected type flows into the λ) |
| `#check (fun x => x) (0 : Nat)` | `(fun x => x) 0 : Nat` — the binder metavariable is solved by unification with the argument, so the elaborator is not purely bidirectional |
| `def g (n : Nat) : Int := n` with `pp.explicit` | `fun n => @Nat.cast Int instNatCastInt n`: the coercion and instance are elaborator output; the kernel sees only this term |
| `addDecl` of `bad : Nat := Bool.true` built directly as a `Declaration` (with `Elab.async false`) | `kernel rejected: (kernel) declaration type mismatch, 'bad' has type Bool but it is expected to have type Nat` |

With default asynchronous elaboration the same `try ... catch` printed its success message and the kernel error was reported separately for that command, i.e. the kernel check is decoupled from the elaboration control flow; with `set_option Elab.async false` the exception was caught synchronously.

Profiler (`set_option profiler true`, `profiler.threshold 0`), three runs:

| Theorem | Tactic search (ms) | Kernel "type checking" of the result (ms) |
| --- | --- | --- |
| `a < b → b < c → c + 3 ≤ d → a + 5 ≤ d` by `omega` (two copies × 3 runs) | 2.97–3.65 | 9.25–14.7 (plus a second check of 0.19–0.35) |
| `(xs ++ ys).length = ys.length + xs.length` by `simp [Nat.add_comm]` | 0.41–0.67 | 0.28–0.35 |
| `(List.range 50).foldl (· + ·) 0 = 1225` by `decide` | 3.08–5.16 | 2.52–4.18 |

(`List.range 200` with `decide` failed with "maximum recursion depth has been reached".) "Search is expensive, checking is cheap" therefore does not hold per declaration for `omega`-style certificates at this scale.
Basis: execution.

**Code sizes (non-blank lines, `leanprover/lean4` `main`):** `src/kernel` 7,274 (35 files: C++ sources and headers); `src/Lean/Elab` 71,635 (327 files); `src/Lean/Meta` 102,295 (511 files); all of `src/Lean` 275,174 (1,299 files). Derived: elaborator + meta-programming framework (173,930) is ≈ 24× the kernel directory. The kernel also links runtime and utility code outside `src/kernel`, not counted.
Basis: execution (counting script under **Evidence**) + derived.

### 6. Refinement and ownership checkers: what is searched and what is checked

**LiquidHaskell** (`liquidhaskell-boot/src/Language/Haskell/Liquid/Constraint/Generate.hs`): "Bidirectional Constraint Generation: CHECKING" `cconsE :: CGEnv -> CoreExpr -> SpecType -> CG ()` (lines 566–650) and "SYNTHESIS" `consE :: CGEnv -> CoreExpr -> CG SpecType` (lines 738–). The checking fallback is the mode switch, emitted as a constraint rather than decided:

```haskell
cconsE' γ e t
  = do
       when (warnOnTermHoles (getConfig γ))  maybeAddHole
       te  <- consE γ e
       te' <- instantiatePreds γ e te >>= addPost γ
       addC (SubC γ te' t) ("cconsE: " ++ ...)
```

(lines 639–644). The subtyping constraints (with unknown refinements) are solved afterwards by the Horn/fixpoint solver; the generator itself is "syntax-directed constraint generation" (lines 16–17). Published (Vazou et al., ICFP 2014): laziness makes "the classical translation of refinement types to verification conditions ... unsound", and checking 10,209 lines took 1080 s with 1.7 lines of termination annotation per 100 lines.

**Flux** (`crates/flux-refineck/src/lib.rs` lines 80–116): pass 1 "infer shape of `TypeEnv` at the entry of join points" (`run_in_shape_mode`, where "In shape mode we don't care about kvars", `checker.rs` lines 169–201); pass 2 "generate refinement tree constraint" (`run_in_refine_mode`, lines 204–235); pass 3 "invoke fixpoint on the constraint" — or `execute_lean_query` instead when Lean emission is enabled, or when the item is marked as proven externally and Lean checking is enabled. Before checking, `compute_ghost_statements` adds "statements that are not part of the original mir, but are added from information extracted from the compiler or some additional analysis" (`ghost_statements.rs` lines 1–2); the points-to analysis inserts `PtrToRef` statements at joins where `r` may point to `x` or `y`, converting `ptr(x)`/`ptr(y)` to a common `&mut` type (`ghost_statements/points_to.rs` lines 1–19). The checker consumes them in `check_ghost_statement` (`Fold`, `Unfold`, `Unblock`, `PtrToRef`; `checker.rs` lines 1945–1967) and handles `&mut`/shared borrows via `env.borrow(..., Mutability::Mut | Not, place)` (lines 1341–1348). Published (Lehmann et al., PLDI 2023): vs Prusti on the same benchmarks, spec lines 145 vs 315, no loop invariants vs 88 lines, total time 7.13 s vs 246.65 s; Flux "can assume programs satisfy Rust's borrowing rules, which our analysis relies on".

**Oxide** (`oxide/borrowck.ml`): `ownership_safe` implements O-UniqueSafety/O-SharedSafety; a loan conflicts unless both accesses are shared or the places are disjoint, with `disjoint pi1 pi2 = not (prefix_of pi1 pi2 || prefix_of pi2 pi1)` (lines 91–92, 105–150), and in a shared context only unique references are significant (`keep_if_ref`, lines 55–65). Published (Weiss et al., arXiv v4): type safety is a paper proof; on rustc's borrow-checker test suites "All 208 tests either type check when rustc does so, or produce an error corresponding to the error produced by rustc", with 407 tests out of scope (heap allocation/libraries 103, traits 93).
Basis: source + documentation.

### 7. Where completeness or decidability breaks

| Feature | Effect | Where observed |
| --- | --- | --- |
| Unannotated λ (Curry-style) | `(λ x.x) 0` "does not type-check against type N" in systems with unannotated λ; MetaRocq relies on Church-style annotated abstractions | Lennon-Bertrand 2021; JACM 2025; Lean `def f1` probe (§5) |
| Impredicative instantiation | instantiation subtyping undecidable → predicative restriction | Dunfield & Krishnaswami 2013 |
| Cumulativity / variance of inductives | needs constrained inference; variance check is an explicit under-approximation; past kernel bugs in Coq 8.11–8.14 | MetaRocq `PCUICSafeChecker.v` 1579–1582; papers |
| Strong normalization | assumed as a hypothesis (MetaRocq); false for Lean (fuel instead) | `PCUICSN.v` 44–48; Carneiro 2025 |
| Universe-level equality | Lean's kernel decides fewer `max`/`imax` equalities than Lean4Lean's complete procedure | `divergences.md` |
| Native reduction (`reduceBool`) | unsupported by the verified re-implementation | `TypeChecker.lean` 453–458 |
| GADTs, value restriction | no principal types → no complete inference | Tan, Owens, Kumar 2015 |
| Refinement inference | complete only relative to a qualifier set; decidability via conservative subtyping | Rondon et al. 2008 |
| Ownership/reborrows | Flux delegates borrow legality to rustc and adds ghost conversions from a may-points-to analysis; Oxide uses syntactic place disjointness | `points_to.rs`; `borrowck.ml` |

Basis: source + documentation.

### 8. Monolithic complete checker versus elaborator + witness checker

| Dimension | Monolithic checker proved sound and complete (MetaRocq, CakeML) | Untrusted elaborator/solver + small trusted checker (Lean kernel, Lean4Lean, Flux, LiquidHaskell) |
| --- | --- | --- |
| What the trusted part decides | full typing relation, including search for types (`infer`) and proofs of absence (`A -> False`) | only that the *elaborated* term (with explicit binders, coercions, instances, ghost statements) is well typed; search lives outside |
| Trusted code measured here | MetaRocq's extracted checker trusts Rocq's kernel, extraction, the OCaml toolchain, and the `NormalizationIn` hypothesis (their sizes: not measured); the checker's own proofs are checked, not trusted | Lean: C++ kernel directory 7,274 non-blank lines (trusted). Lean4Lean: executable core ≈ 2,229 lines (863 + 805 + 561) verified against 6,079 lines of theory |
| Proof effort recorded | MetaRocq "more than 300kloc of Coq code" (JACM 2025, whole project); "Coq Coq Correct!" "about 17kLoc of specifications, 30kLoc of proofs"; CakeML inference proofs 15,207 non-blank lines for a 4,225-line inferencer (derived ratio 3.6) | Lean4Lean `Verify/` 21,649 non-blank lines for ≈ 2,229 executable lines (derived ratio ≈ 9.7), with remaining `sorry`s and unfinished parts |
| Checker speed | MetaRocq checker "11.2 times longer than Coq's kernel" (JACM 2025); "Coq Coq Correct!" ≈ 0.015 s vs 0.002 s | Lean4Lean ×1.21–×1.40 of the C++ kernel (paper); measured 1–2 s per core module here |
| Expressiveness when the algorithm is incomplete | rejection comes with a proof that no derivation exists — a lockout is then a property of the *declarative* system, not the algorithm | lockout can come from the elaborator heuristics (e.g. `f1`), and is repaired by more annotations or a better elaborator without touching the trusted checker |
| Maintenance on a language change | must re-prove completeness (bidirectional bridge) | change elaborator freely; re-verify only if the kernel's judgment changes |

Derived conclusion: completeness proofs pay off when the *trusted* component must make decisions (e.g. a kernel that must not reject valid PCUIC terms); the split pays off when search (unification, instance resolution, Horn solving, points-to analysis) is large and changes often. The two compose: a split architecture whose trusted checker is proved complete for *explicitly annotated* terms (Church-style, as MetaRocq) needs no completeness argument about the elaborator.
Basis: derived from §§2–7 (numbers as cited).

### 9. The three lockout patterns in the examined systems

- **Shared (temporary read-only) reborrowing.** Oxide: shared–shared loans never conflict (`(omega <> Unique && omegaPrime <> Unique)` is non-conflicting, `borrowck.ml` lines 141–149). Flux: shared borrows go through `env.borrow(..., Mutability::Not, place)` and Rust's own borrow checker has already approved the program. Neither requires the programmer to annotate the reborrow.
- **Disjoint splits in branches / nested splits.** Oxide decides disjointness by place prefixes only (no arithmetic on indices). Flux handles "which location does this reference point to after a join" with an inferred `PtrToRef` ghost statement and strong references (`&strg T`), i.e. the split is computed by an untrusted analysis and checked by the refinement checker.
- **Guarded unboxing / value-range refinements.** LiquidHaskell and Flux propagate guards as path conditions (Flux `Guard::Pred`, `checker.rs` lines 157–166) into constraints solved by the Horn solver; the refinement *search* (κ solutions) is outside the checker; in Flux's `check_fn` at the pinned revision the fixpoint answer is consumed directly (`execute_fixpoint_query` then `report_fixpoint_errors`) with no separate re-check of the solution, except on the optional Lean path.
Basis: source + derived.

### 10. Performance and resource levels

| Level | Value | Basis |
| --- | --- | --- |
| L1 authoring | proof/code ratios: CakeML inference 3.6 (derived), Lean4Lean `Verify/` ÷ core ≈ 9.7 (derived); Liquid types cut annotations "from 31% of program text to under 1%"; Flux spec lines 145 vs Prusti 315; LiquidHaskell 1.7 lines/100 LoC termination hints; LLM token/turn budgets: not measured | derived; documentation |
| L2 toolchain build | Lean4Lean executable 35.4 s wall incl. downloads (this host); MetaRocq "around 15 min to compile" (JACM 2025, MetaCoq 1.2); "Coq Coq Correct!" ≈ 10 min; CakeML build: not measured | execution; documentation |
| L3 elaboration latency | Lean v4.34.1: `omega` 2.97–3.65 ms, `simp` 0.41–0.67 ms, `decide` 3.08–5.16 ms (§5); Flux benchmarks 7.13 s total; LiquidHaskell 1080 s for 10,209 lines; interactive LSP latency: not measured | execution; documentation |
| L4 generated code | not applicable to checkers; CakeML-generated code speed: not examined | — |
| L5 checking | Lean kernel per theorem 0.28–14.7 ms (§5); Lean4Lean 1–2 s per core module incl. ≤ 0.72 s startup (§4); Lean4Lean ×1.21–×1.40 vs C++ (paper); MetaRocq ×11.2 vs Coq kernel (paper) | execution; documentation |
| L6 memory | Lean4Lean peak RSS 108–118 MB (single `Init` modules), 1.17 GB (`Lean4Lean.TypeChecker`, loads the `Lean` library), 24.2 GB (all `Init`, parallel); `.olean` sizes: not measured | execution |

### 11. Human comprehensibility (C1) and conceptual simplicity (C2)

- **C1.** A complete checker gives the most legible failure: "no type exists" is a theorem, so diagnostics can blame the program, not the tool. In split architectures, failures arise in the elaborator (`Failed to infer type of binder`) whose rules users learn empirically; the kernel's errors (`declaration type mismatch`) are about terms users did not write (inserted coercions, `@Nat.cast ...`). Flux's ghost statements and LiquidHaskell's κ-variables are invisible to users unless a constraint fails, at which point the error is reported against a solver constraint rather than a source rule.
- **C2.** The single mode switch (`check_Cumul`: check = infer + subsume) recurs in MetaRocq, LiquidHaskell (`addC (SubC γ te' t)`), and Lean4Lean's application rule (`isDefEq dType aType`); the remaining distinctions are *where the subsumption is decided* (inline by conversion, deferred to a Horn solver, or skipped under `inferOnly`). A minimal universal abstraction is "elaboration emits a fully annotated term plus a set of side conditions; a small checker validates the term and discharges or re-checks the side conditions." Flux's ghost statements and Lean's elaborated `Expr` are instances; the hidden-complexity risk is the side-condition discharger (Horn solver) remaining outside the trusted base.
Basis: derived.

### 12. Validation of implementations and specifications (V1–V4)

- **V1 (specification adequacy).** MetaRocq checks its specification against Coq's real kernel only indirectly (bugs found in Coq 8.11–8.14 cumulative inductives); Lean4Lean documents every intended divergence and treats any other divergence from the C++ kernel as a bug; Oxide was validated against 208 in-scope rustc tests. No spec-mutation or mutant-kill rates were found: unknown.
- **V2 (checker soundness testing).** Independent re-checking of the same `.olean` artifacts by two kernels (C++ and Lean4Lean) is a differential test; the observed replay failures in §4 show such a harness can disagree for reasons unrelated to typing. Adversarial malformed-witness fuzzing of either kernel: not examined.
- **V3, V4.** Concurrency/crash validation does not apply to these checkers beyond Lean's parallel module checking (not examined); studies of user mental models of bidirectional annotation placement: not found.

## Boundaries

- **Not examined:** building or running MetaRocq, CakeML, LiquidHaskell, Flux, or Oxide; proof-checking times of their developments at the pinned revisions; Lean4Lean on `Std`, `Lean`, Batteries, or Mathlib (a run on `Std` exited with status 1 after 92.9 s wall and 52,967,832 KiB peak RSS; its failures were not captured and it is not used as evidence); comparison of Lean4Lean against the C++ kernel on this host; Agda, Idris, F*, Coq's own kernel code.
- **Unknown:** the cause of the 25 `alreadyDeclared` failures in §4 (a plausible but unverified explanation is that auxiliary constants generated on demand are present both in an imported module and in the replayed module's constant list); whether the pinned Lean4Lean revision is intended to replay Lean v4.33.0-rc2's `Init` without such failures; proof sizes of the pinned MetaRocq revision's completeness proof specifically (only whole-project figures were found).
- **Known not to apply:** MetaRocq's completeness theorem does not cover the module system, template polymorphism, or η-conversion; Lean4Lean's theorems are soundness-style and do not establish completeness or termination; CakeML's completeness does not extend to GADTs; Flux's soundness argument assumes rustc's borrow checking.
- **Unsupported (by the subject):** Lean4Lean does not support `reduceBool`/`reduceNat` native reduction.
- **Attractive conclusions not established:** (1) "kernel checking is always much cheaper than search" — contradicted per declaration for `omega` in §5; (2) "a verified kernel re-implementation is an independent implementation" — its README states it "likely shares some implementation bugs with" the C++ kernel; (3) "completeness proofs remove safe-program lockout" — they remove lockout relative to the declarative system only; programs the declarative system rejects remain rejected.

## Evidence

All evidence acquired 2026-11-20.

**Source (repository; revision; path; lines):**

- `MetaRocq/metarocq` @ `51b14e4bb5f4580f00f60208ff8dbf31f3ad6f56`: `pcuic/theories/Bidirectional/BDTyping.v` 28–160 (`check_Cumul` 148–152); `BDToPCUIC.v` 411–420; `BDFromPCUIC.v` 391–405; `BDUnique.v` 311–321; `pcuic/theories/PCUICSN.v` 44–48; `safechecker/theories/PCUICErrors.v` 391–398; `safechecker/theories/PCUICTypeChecker.v` 244, 337–341, 374–378; `safechecker/theories/PCUICSafeChecker.v` 289–319, 1579–1590; `safechecker/theories/README.md`.
- `CakeML/cakeml` @ `2874b664e10939a3ee462215b2e068c89c1f70eb`: `compiler/inference/proofs/README.md`; `compiler/inference/proofs/inferSoundScript.sml` 1355–1360; `compiler/inference/proofs/inferCompleteScript.sml` 1430–1444; file line counts as in §3.
- `digama0/lean4lean` @ `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`: `README.md`; `divergences.md`; `bugs-found.md`; `lean-toolchain` (`leanprover/lean4:v4.33.0-rc2`); `Lean4Lean/TypeChecker.lean` 136–141, 172–180, 263–306, 453–458, 519–541; `Lean4Lean/Verify/TypeChecker.lean` 202–252; `Lean4Lean/Environment/Basic.lean` 57; `Lean4Lean/Replay.lean` 284–305; `Main.lean` 87–150.
- `leanprover/lean4` @ `920a9e5f4f5e9b509f4d879d1b58a1f4d645f3d0`: directory line counts (`src/kernel`, `src/Lean/Elab`, `src/Lean/Meta`, `src/Lean`).
- `ucsd-progsys/liquidhaskell` @ `7c809b687388dc837c53b9db29b0a70b7165b716`: `liquidhaskell-boot/src/Language/Haskell/Liquid/Constraint/Generate.hs` 16–19, 566–650, 738–760.
- `flux-rs/flux` @ `ac24831e4f3dc570ad991751ff65bea0826ed446`: `crates/flux-refineck/src/lib.rs` 70–116; `crates/flux-refineck/src/checker.rs` 150–236, 321–331, 1341–1348, 1945–1967; `crates/flux-refineck/src/ghost_statements.rs` 1–2; `crates/flux-refineck/src/ghost_statements/points_to.rs` 1–19.
- `aatxe/oxide` @ `203e42936b273e7f1351ce1d0ea5bb8d1b0dc5c1`: `README.md`; `oxide/borrowck.ml` 55–65, 91–150.

**Line counts (execution):** non-blank lines of `.lean/.cpp/.h/.rs/.hs/.v` files under each path of GitHub tarballs (`https://codeload.github.com/<owner>/<repo>/tar.gz/<revision>`) at the revisions above, counted by a Python `os.walk` script summing `1 for line in file if line.strip()`. Results: Lean4Lean `TypeChecker.lean` 863, `Inductive` 805 (2 files), `Primitive.lean` 561, `Theory` 6,079 (21), `Verify` 21,649 (36), `Experimental` 11,875 (16), all `Lean4Lean` 44,149 (110); Lean 4 `src/kernel` 7,274 (35), `src/Lean/Elab` 71,635 (327), `src/Lean/Meta` 102,295 (511), `src/Lean` 275,174 (1,299); Flux `flux-refineck` 7,227 (12), `flux-infer` 9,110 (13), all `crates` 64,679 (125); LiquidHaskell `Constraint/` 4,670 (14), `Generate.hs` 1,359, `liquidhaskell-boot/src` 33,713 (99); MetaRocq `safechecker/theories` 16,965 (11), `pcuic/theories/Bidirectional` 2,985 (5), `pcuic/theories` 88,217 (99). CakeML counts via `grep -vc '^\s*$'` on raw files fetched at the pinned revision. Oxide `oxide/typeck.ml` 624, `oxide/borrowck.ml` 175.

**Executions:**

- Lean elaborator/kernel probe: `lean` "version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release" on a single file containing the declarations in §5 plus `set_option profiler true` and `set_option profiler.threshold 0`; three runs; output lines `tactic execution of Lean.Parser.Tactic.omega took ...ms` and `type checking took ...ms` transcribed in §5. The kernel-bypass declaration:

```lean
set_option Elab.async false in
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let decl := Declaration.defnDecl
    { name := `bad, levelParams := [], type := mkConst ``Nat,
      value := mkConst ``Bool.true, hints := .opaque, safety := .safe }
  try liftCoreM (addDecl decl); logInfo "kernel accepted (unexpected)"
  catch e => logInfo m!"kernel rejected: {e.toMessageData}"
```

- Lean4Lean: in a copy of the pinned tree, `lake build lean4lean` (59 jobs; elan installed `v4.33.0-rc2` = commit `d8b18978322de05a8f3dba51ef03cf5461676c17`; Lake cloned Batteries at the revision in `lake-manifest.json`); then `/usr/bin/time -f "... wall_s=%e maxrss_kib=%M ..." lake env .lake/build/bin/lean4lean <MOD>` for the targets in §4 (three runs for single modules; `--verbose` printed N + 2 lines for N reported declarations); `lake env .lake/build/bin/lean4lean Init` for the prefix run (failures listed from stderr).

**Literature (identity verified via Crossref/DataCite/arXiv/publisher pages on 2026-11-20):**

- M. Sozeau, S. Boulier, Y. Forster, N. Tabareau, T. Winterhalter, "Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq," PACMPL 4(POPL) 2020, Article 8, DOI 10.1145/3371076.
- M. Sozeau, A. Anand, S. Boulier, C. Cohen, Y. Forster, F. Kunze, G. Malecha, N. Tabareau, T. Winterhalter, "The MetaCoq Project," J. Automated Reasoning 64(5):947–999, 2020, DOI 10.1007/s10817-019-09540-0.
- M. Sozeau, Y. Forster, M. Lennon-Bertrand, J. B. Nielsen, N. Tabareau, T. Winterhalter, "Correct and Complete Type Checking and Certified Erasure for Coq, in Coq," J. ACM 72(1), Article 8, 2025, DOI 10.1145/3706056.
- M. Lennon-Bertrand, "Complete Bidirectional Typing for the Calculus of Inductive Constructions," ITP 2021, LIPIcs 193, 24:1–24:19, DOI 10.4230/LIPIcs.ITP.2021.24.
- Y. K. Tan, S. Owens, R. Kumar, "A Verified Type System for CakeML," IFL 2015, DOI 10.1145/2897336.2897344.
- R. Kumar, M. O. Myreen, M. Norrish, S. Owens, "CakeML: A Verified Implementation of ML," POPL 2014, pp. 179–191, DOI 10.1145/2535838.2535841.
- M. Carneiro, "Lean4Lean: Verifying a Typechecker for Lean, in Lean," TYPES 2025, LIPIcs 384, 2:1–2:23, DOI 10.4230/LIPIcs.TYPES.2025.2 (arXiv:2403.14064; v1 2024-03-21 had the title "Lean4Lean: Towards a formalized metatheory for the Lean theorem prover").
- J. Dunfield, N. Krishnaswami, "Bidirectional Typing," ACM Computing Surveys 54(5), Article 98, DOI 10.1145/3450952, arXiv:1908.05839.
- J. Dunfield, N. R. Krishnaswami, "Complete and Easy Bidirectional Typechecking for Higher-Rank Polymorphism," ICFP 2013, pp. 429–442, DOI 10.1145/2500365.2500582, arXiv:1306.6032.
- B. C. Pierce, D. N. Turner, "Local Type Inference," TOPLAS 22(1):1–44, 2000, DOI 10.1145/345099.345100.
- P. M. Rondon, M. Kawaguchi, R. Jhala, "Liquid Types," PLDI 2008, pp. 159–169, DOI 10.1145/1375581.1375602.
- N. Vazou, E. L. Seidel, R. Jhala, D. Vytiniotis, S. Peyton Jones, "Refinement Types for Haskell," ICFP 2014, pp. 269–282, DOI 10.1145/2628136.2628161.
- N. Lehmann, A. T. Geller, N. Vazou, R. Jhala, "Flux: Liquid Types for Rust," PACMPL 7(PLDI) 2023, pp. 1533–1557, DOI 10.1145/3591283, arXiv:2207.04034.
- A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, "Oxide: The Essence of Rust," arXiv:1903.00982 (v4, 2021; v2–v3 also list N. D. Matsakis).
- A. Abel, J. Öhman, A. Vezzosi, "Decidability of Conversion for Type Theory in Type Theory," PACMPL 2(POPL) 2018, Article 23, DOI 10.1145/3158111 (decidability of conversion proved from algorithmic completeness and soundness; ≈ 10,000 lines of Agda).
- L. de Moura, S. Ullrich, "The Lean 4 Theorem Prover and Programming Language," CADE-28, LNCS 12699, pp. 625–635, 2021, DOI 10.1007/978-3-030-79876-5_37 ("Lean has a relatively small trusted kernel ... implement their own reference checkers").

## Revalidation

- **MetaRocq statements:** grep the pinned theorem names (`infering_typing`, `checking_typing`, `typing_infering`, `infering_unique`, `typing_result_comp`, `NormalizationIn`) in a new revision and diff their statements; check whether the "Incompleteness" comment in `PCUICSafeChecker.v` survives.
- **CakeML:** diff `infer_prog_sound` and `infer_ds_complete` statements; recount the listed files with `grep -vc '^\s*$'`.
- **Lean4Lean:** `lake build lean4lean && lake env .lake/build/bin/lean4lean Init.Prelude` (expect 1,975 declarations on v4.33.0-rc2) and `lake env .lake/build/bin/lean4lean Init` (does it still report `alreadyDeclared` for auxiliary constants?); diff `Lean4Lean/Verify/TypeChecker.lean` theorem statements and recount `sorry` with `grep -rw sorry Lean4Lean/Theory Lean4Lean/Verify | wc -l`.
- **Lean elaborator vs kernel:** rerun the §5 file with the target toolchain; the `omega` row is the discriminator for "kernel check slower than search".
- **Flux/LiquidHaskell/Oxide:** diff the quoted ranges (`lib.rs` pass structure, `check_ghost_statement`, `cconsE'` fallback, `ownership_safe`).
- **Code sizes:** rerun the counting script on fresh tarballs; the kernel-vs-elaborator ratio is the quantity of interest.
