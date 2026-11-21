# Computable Fuel Interpreters vs. Propositional Operational Semantics in Dependent Type Theories

## Summary

Mechanizing programming-language and instruction-set architecture (ISA) semantics inside interactive theorem provers requires choosing between **propositional/relational operational specifications** (inductive `step`/`star` or `exec_stmt` predicates in `Prop`, or `Classical.choice`-tainted partial combinators) and **total computable fuel-indexed interpreters** (structural `Nat`-fueled state transformers and clocked functional big-step evaluators in `Type`). Cross-system source analysis of Lean 4 (`v4.34.1`), Rocq/CompCert, HOL4/CakeML, Isabelle/HOL, LNSym, `riscv-coq`, and Sail establishes four architectural laws:

1. **Why Propositional and `Classical.choice` Semantics Cannot Drive Kernel `rfl` Symbolic Execution**: In dependent type theories with impredicative, proof-irrelevant `Prop` (`leanprover/lean4` `src/kernel/inductive.cpp:534-582`), multi-constructor transition relations (`Star : State → State → Prop`) and existentials (`∃ s', Star s s'`) fail singleton large elimination (`elim_only_at_universe_zero() == true`), prohibiting computational extraction of post-states into `Type`. Attempting to recover a total function via classical indefinite description (`Classical.choose` / `Classical.epsilon` in `src/Init/Classical.lean:19-34, 108-111`, Lean 4's `partial_fixpoint`, or Isabelle/HOL's `while_option` via `LEAST k` in `While_Combinator.thy:26-29`) introduces an uninterpreted axiom (`Classical.choice`, `has_value() == false`) that halts kernel weak-head normal form (WHNF) conversion immediately on neutral stuck terms. Similarly, Lean 4 `partial def` declarations compile via `opaque` kernel constants with zero kernel reduction rules, while `WellFounded.fix` (`src/Init/WF.lean`) blocks symbolic WHNF behind `Acc.rec` proof terms unless structural recursion or fuel is used.
2. **How Computable Functional Big-Step and Structural Fuel Evaluators Unlock Lemma-Free Symbolic Reduction**: Replacing relational derivations with a total recursive interpreter indexed by a structural `Nat` budget—either **instruction-step fuel** (`run : Nat → ArmState → ArmState` in `leanprover/LNSym`, `Arm/Exec.lean:127-132`) or **call/back-edge clocks** (`evaluate` in `CakeML/cakeml`, `semantics/evaluateScript.sml:51-294`, Owens et al., *ESOP* 2016)—makes finite and symbolic execution native to kernel conversion (`isDefEq` / `rfl`, Rocq `vm_compute`, HOL4 `EVAL`). In CakeML, wrapping recursive sub-evaluations in `fix_clock` discharges lexicographic termination `(s.clock, syntax_size)`, after which proving clock boundedness (`evaluate_clock : s2.clock ≤ s1.clock`) eliminates `fix_clock` completely (`fix_clock_evaluate`) to leave pure compute equations (`full_evaluate_def[compute]`) and clean structural induction (`evaluate_ind`).
3. **Canonical Two-Way Adequacy Patterns Between Computable Evaluators and Trusted Relational Specs**: Computable fuel evaluators compose cleanly with human-audited relational specifications via proved two-way adequacy bridges:
   - *Terminating & faulting runs*: $(\exists k,\; \mathsf{eval}(k, s) = (s', r) \land r \neq \mathsf{Timeout}) \iff s \Downarrow_{\text{rel}} (s', r)$, anchored by **clock monotonicity** (`add_to_counter`) and **minimal-clock canonicalization** (`k_min = k - s'.clock`, `evaluate_decs_min_clock` in `bigClockScript.sml:164-186, 1035-1050`).
   - *Reactive divergence*: A diverging program timeouts at every finite clock $k$, emitting a prefix-monotone chain of observable I/O traces whose least upper bound (`lprefix_lub` in `bigSmallEquivScript.sml:2555-2585`) equals the relational/coinductive infinite trace (Leroy & Grall, *Inf. Comput.* 2009).
   - *Bounded nondeterminism*: Naive deterministic `State → Option State` interpreters silently drop demonic branches (`Beh_rel ⊈ Beh_fun`); completeness requires either a finite-branching list/set monad (`CompCert` `cfrontend/Cexec.v:2163-2231`, `do_step_sound` + `do_step_complete`) or an externalized schedule oracle.
4. **Symbolic Reduction Pitfalls in Dependent-Type Fuel Runners**: Three representation pitfalls break soundness or kernel `rfl` over symbolic states: (a) writing symbolic fuel offsets as `k + d` instead of `d + k` (Lean 4's `Nat.add` recurses structurally on its *second* argument, leaving `3 + d` stuck in WHNF on free variable `d`); (b) failing to absorb early exception/trap exits across `run n` (`mit-plv/riscv-coq`, `Platform/Run.v:33-39`); and (c) conflating `Timeout` (`fuel = 0`) with `Safe` (unsound at `fuel = 0`) or placing `Timeout => False` unguarded in contravariant preconditions (vacuous at `fuel = 0`).

## Applicability

This report applies to verification architects designing ISA models (`ARMv8/v9`, `RISC-V`, `x86-64`), compiler IR semantics, and program logics across Lean 4, Rocq/Coq, HOL4, and Isabelle/HOL.

### Examined Subjects and Scope

- **CakeML (`CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`)**: Examined in `semantics/evaluateScript.sml`, `semantics/alt_semantics/{bigStep,smallStep}Script.sml`, and `semantics/alt_semantics/proofs/{bigClock,bigSmallEquiv}Script.sml` for clocked functional big-step semantics and relational adequacy (Owens et al., *ESOP* 2016).
- **CompCert (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`)**: Examined across `common/Smallstep.v`, `cfrontend/{Clight,ClightBigstep,Cexec}.v`, and `backend/RTL.v` to contrast relational simulation spines, coinductive divergence (`execinf_stmt`; Leroy & Grall 2009; Blazy & Leroy 2009), and list-monadic computable C exploration (`Cexec.do_step`).
- **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`) & LNSym (`leanprover/LNSym@49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`)**: Examined for `Prop` singleton elimination (`src/kernel/inductive.cpp`), `Classical.choice` (`src/Init/Classical.lean`), `WellFounded.fix` (`src/Init/WF.lean`), and computable `Nat`-fueled ARMv8 symbolic simulation (`Arm/Exec.lean`).
- **Isabelle/HOL (`isabelle-prover/mirror-isabelle@9b69a01e9bcac478db4e6f01ae2b032ee684d9e0`), `riscv-coq` (`mit-plv/riscv-coq@03881b21aa36115d436e06b9e1a40836e9b927c7`), and Sail (`rems-project/sail@97aa617dcd4d01575f773cb58ea1e8686858c8c2`)**: Examined for classical `while_option` + `[code]` extraction (`While_Combinator.thy`), relational `IMP` equivalence (`Small_Step.thy`), monadic cycle composition (`Run.v`), and ISA monad lowering (Armstrong et al., *POPL* 2019), alongside Omnisemantics (Charguéraud et al., *TOPLAS* 2023) and Interaction Trees (Xia et al., *POPL* 2020).

### Cross-References to Adjacent Corpus Packages

- `fuel-step-indexing-clocks-and-tcb-recursion`: Analyzes recursion budgets for cyclic ADT environment tables and contravariant invariant vacuity; the present report focuses on operational and ISA execution semantics across dependent and HOL provers, `Classical.choice` / singleton-elimination kernel barriers, functional big-step `fix_clock` erasure, and two-way relational adequacy.
- `reference-model-bisimulation-executable-semantics-and-differential-oracles`: Covers external differential testing and fault-kind equivalence (`Miri`, `MiniRust`, `SpecTec`, `K`).

## Findings

### 1. Kernel Reduction and Elimination Taxonomy Across Semantic Encodings

Basis: source + documentation + derived

Theorem provers enforce consistency by rejecting unrestricted general recursion (`fix f x = f x`). Operational semantics for Turing-complete languages or cyclic machine-code graphs therefore choose among six mechanization styles, whose computability inside kernel conversion (`isDefEq`) vs. external extraction differs sharply across dependent type theory and classical HOL:

| Semantic Formulation | Canonical Upstream Instance | Kernel Conversion (`rfl` / `vm_compute` / `EVAL`) | Axiom Footprint (Lean 4) | Nondeterminism & Divergence Expressiveness | Symbolic Proof Cost ($N$ concrete steps on symbolic state) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **1. Inductive Small-Step / Big-Step (`Prop`)** | `CompCert` `Smallstep.v`, `Clight.v`; `Isabelle` `IMP/{Big,Small}_Step.thy` | **No** (proof terms only; `Prop` blocks large elimination into `Type`) | `[]` | Native demonic choice & stuckness; divergence via `forever` / coinductive `execinf_stmt` | $\Theta(N)$ explicit rule applications + intermediate witness synthesis |
| **2. Inductive Omnisemantics (`Prop` set-transformer)** | Charguéraud et al. (*TOPLAS* 2023); inductive `Omni s Q` | **No** (propositional derivation of post-set $Q$) | `[]` (or `[propext]`) | Native demonic + angelic choice & safety in one inductive judgment | $\Theta(N)$ syntax-directed rule applications (no `star` step-count skew) |
| **3. Classical Choice / `LEAST` Combinator** | `Isabelle` `While_Combinator.thy` (`while_option`); Lean 4 `Classical.choose` / `partial_fixpoint` | **Blocked in kernel** (`Classical.choice` / `LEAST` is an uninterpreted axiom); Isabelle relies on external `[code]` | `[Classical.choice, propext, funext]` | Deterministic partial functions; cannot separate silent hang from `None` fault without tags | **Stuck at step 1** in kernel WHNF; requires manual `while_option_unfold` rewrites |
| **4. `partial def` / `opaque` Function** | Lean 4 `partial def` (`Inhabited` witness) | **Blocked completely** (`ConstantInfo.opaqueInfo`; zero kernel equations) | `[]` (logically opaque!) | Runs in compiled binary (`lean --run`), **unusable in proofs** | Impossible (opaque constant) |
| **5. Coinductive Free Monad (`ITree` / `Delay`)** | `InteractionTrees` (Xia et al., *POPL* 2020); `sail_coq_backend` | **Guarded only** (Rocq `cofix` unfolds only under `match`; no kernel `coinductive` in Lean 4) | `[propext, Classical.choice]` via quotients in Lean 4 | Compositional monadic events & `Tau`-guarded silent divergence up to `eutt` | Requires fuel-unrolling helper `burn n t` to compute $n$ `Tau` steps |
| **6. Structural `Nat`-Fuel / Clocked Functional Big-Step (`Type`)** | `CakeML` `evaluateScript.sml`; `LNSym` `Arm/Exec.lean`; `CompCert` `Cexec.v` | **Full native WHNF / `rfl` / `EVAL`** on ground and symbolic states! | **`[]` (zero axioms)** | Total over all clocks; divergence via $\forall k, \mathsf{Timeout}$ + I/O trace supremum; bounded nondet via `List` | **$O(1)$ tactic size (`rfl` or single WHNF pass)** across all $N$ steps |

#### 1.1 Why `Prop` Relations and `Classical.choice` Paralyze Dependent-Type Kernel Reduction

Direct inspection of `leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52` exposes the exact kernel mechanisms behind rows 1 and 3:

1. **Singleton Elimination Barrier (`src/kernel/inductive.cpp:534-582`)**: To preserve proof irrelevance (`is_def_eq_proof_irrel`) on `Prop` without triggering Berardi's paradox, `elim_only_at_universe_zero()` (`lines 534-577`) forces `m_elim_level = mk_level_zero()` (`line 582`) whenever a `Prop` inductive is mutually recursive (`line 530`), has `num_intros > 1` constructors (`lines 535-539`, covering `Star.refl | Star.step` and multi-rule `BigStep`), or has a non-`Prop` constructor field absent from result indices (`lines 558-575`, covering `Exists.intro w h`). Thus no computable function in `Type` can project a post-state `s'` from `h : ∃ s', Star step s0 s'`.
2. **`Classical.choice` Neutrality (`src/Init/Classical.lean:19-34` & `src/kernel/type_checker.cpp:543-551`)**: Bypassing singleton elimination via `Classical.choose h` (`Classical.lean:29-30`) or `partial_fixpoint` embeds `Classical.choice : Nonempty α → α`. In `type_checker.cpp`, `is_delta` (`lines 543-551`) checks `info->has_value()`, which is `false` for `.axiomInfo` and `.opaqueInfo`—halting `whnf_core` immediately on `Classical.choice ...`! In classical Isabelle/HOL (`While_Combinator.thy:26-32`), `while_option b c s` similarly uses non-computable `∃k` and `LEAST k`, requiring a derived theorem `while_option_unfold[code]` (`lines 31-32`) exported to an external untrusted SML/Haskell compiler.
3. **`WellFounded.fix` Proof-Term Drag (`src/Init/WF.lean`)**: Defining evaluators via `WellFounded.fix` recurses on `a : Acc r x`. On concrete inputs in Lean 4 (where `.thmInfo` has `has_value() == true`), WHNF unfolds large arithmetic proof terms inside `Acc.rec`; on symbolic states `(x : BitVec 64)` with abstract termination hypotheses `h : n < bound`, `Acc.rec` stalls on neutral `h`. Structural recursion on `fuel : Nat` carries zero proof fields and reduces unconditionally on `Nat.succ fuel'`.

---

### 2. Functional Big-Step Semantics vs. Fuel-Indexed Small-Step Runners

Basis: source + normative + derived

#### 2.1 Flat Instruction-Fuel State Transformers for Machine-Code ISAs (`LNSym`, `riscv-coq`, `Sail`)

At the ISA level (flat `PC`-indexed fetch-decode-execute without AST continuations), the canonical computable model pairs a total single-instruction transformer with structural `Nat` iteration:

- **LNSym (`leanprover/LNSym@49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`, `Arm/Exec.lean:10-133`)**: Defines `exec_inst (ai : ArmInst) (s : ArmState) : ArmState` (`line 10`) and `stepi (s : ArmState) : ArmState` (`lines 105-126`), embedding fault tags into `s.err : StateError` (`None | NotFound | Unimplemented`) so `stepi` is an absorbent identity (`| _ => s`, `line 125`) after any error. Multi-step `run (n : Nat) (s : ArmState) : ArmState` (`lines 127-132`) satisfies `run 0 s = s := rfl` (`line 135`), `run (n1 + n2) s = run n2 (run n1 s)` (`run_plus`, `lines 145-160`), and symbolically simulates concrete ARMv8 instruction blocks over symbolic `BitVec 64` states without per-step relational proof synthesis.
- **Early-Exit / Trap Absorption (`mit-plv/riscv-coq@03881b21...`, `src/riscv/Platform/Run.v:22-40`)**: `riscv-coq` defines monadic `run1` (`lines 22-31`) and documents (`lines 33-39`) why naive $n$-fold sequencing `power_func (fun m => run1 iset;; m) n (Return tt)` is unsound when a cycle raises an early exception unless the monad bind or absorbent fault state skips remaining fuel cycles.
- **Single-Source ISA Monads (`rems-project/sail@97aa617d...`, Armstrong et al., *POPL* 2019, DOI `10.1145/3290384`)**: Sail lowers imperative bitvector specs into a free effect monad (`sail_{lean,coq,lem}_backend`), discharging sequential execution into pure state/fuel runners while retaining monadic hooks for relaxed-memory concurrency.

#### 2.2 Clocked Functional Big-Step Semantics for Structured ASTs (`CakeML`)

For structured AST languages, small-step semantics require explicit continuation stacks (`Kseq`, `Kloop1`, `Kcall` in `CompCert` `Clight.v`; `ctxt list` in `CakeML` `smallStepScript.sml`). **Functional big-step semantics** (Owens et al., *ESOP* 2016, DOI `10.1007/978-3-662-49498-1_23`) eliminates continuations by writing a recursive big-step function whose `st.clock : Nat` decrements **only** on non-structural recursive calls (`Opapp`, `ForceThunk`, `Eval`, `while` back-edges). Inspection of `CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb` (`semantics/evaluateScript.sml:14-379`) isolates its three-step termination engineering pattern:

1. **`fix_clock` Clamping (`evaluateScript.sml:14-17, 54-60, 286-294`)**: Before `evaluate` is defined, the termination prover does not yet know that evaluating `e1` in `e1::e2::es` never increases `st.clock`. Wrapping intermediate calls in `fix_clock s (s', res) = (s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock, res)` lets `fix_clock_IMP` (`lines 40-44`) discharge lexicographic termination `(s.clock, list_size exp_size es)` (`lines 287-294`; identical to `termination_by (st.clock, sizeOf es)` in Lean 4).
2. **Post-Definition `fix_clock` Erasure (`lines 298-336`)**: Immediately afterward, CakeML proves `evaluate_clock : evaluate s1 env e = (s2, r) ⇒ s2.clock ≤ s1.clock` (`lines 298-311`), derives `fix_clock_evaluate : fix_clock s1 (evaluate s1 env e) = evaluate s1 env e` (`lines 321-329`), and rewrites **both** `evaluate_def` and `evaluate_ind` (`lines 331-368`) so `fix_clock` vanishes from `[compute]` and downstream proofs!
3. **Explicit Timeout Tag (`lines 101-104`)**: Clock exhaustion yields `Rerr (Rabort Rtimeout_error)`, kept disjoint from language exceptions (`Rraise`) and UB/type faults (`Rabort Rtype_error`).

---

### 3. Two-Way Adequacy Proofs, Divergence Supremums, and Three Soundness Traps

Basis: source + execution + derived

Bridging computable `evalFuel` to trusted relational `StepRel`/`BigStepRel` rests on four mechanized theorems (`CakeML` `bigClockScript.sml`, `bigSmallEquivScript.sml`; `CompCert` `ClightBigstep.v`, `Cexec.v`; `Isabelle` `Small_Step.thy`; verified in **Evidence** §2):

1. **Clock Monotonicity (`add_to_counter`, `bigClockScript.sml:164-186`)**: If $\mathsf{evalFuel}(k, p, s) = (s', r)$ with $r \neq \mathsf{Timeout}$, then $\forall \Delta \in \mathbb{N},\; \mathsf{evalFuel}(k + \Delta, p, s) = (s'[\mathsf{clock} \mathrel{+}= \Delta], r)$.
2. **Minimal-Clock Canonicalization (`evaluate_decs_min_clock`, `bigClockScript.sml:1035-1050`)**: Setting $k_{\min} = k - s'.\mathsf{clock}$ yields $\mathsf{evalFuel}(k_{\min}, p, s) = (s'[\mathsf{clock} := 0], r)$.
3. **Two-Way Terminating & Faulting Equivalence (`big_exp_to_small_exp`, `small_exp_to_big_exp` in `bigSmallEquivScript.sml:54-58, 1210-1225`; `big_iff_small` in `Small_Step.thy:169-171`)**:
   $$s \Downarrow_{\text{unclocked}} (s', r) \iff \bigl(r \neq \mathsf{Timeout} \land \exists k,\; \mathsf{evalFuel}(k, p, s) = (s'[\mathsf{clock} := 0], r)\bigr) \iff (p, s) \to^*_{\text{small}} \mathsf{Terminal}(s', r).$$
4. **Reactive Divergence via Prefix Supremum (`lprefix_lub_big_small`, `bigSmallEquivScript.sml:2555-2585`, vs. Coinductive `execinf_stmt` in `ClightBigstep.v:508-595`)**: Rather than duplicating rules in a separate coinductive divergence relation (Leroy & Grall 2009), functional big-step characterizes divergence by $\forall k,\; \mathsf{snd}(\mathsf{evalFuel}(k, p, s)) = \mathsf{Timeout}$ with infinite observable I/O trace $\bigsqcup_{k \in \mathbb{N}} \mathrm{trace}(\mathsf{evalFuel}(k, p, s))$.

#### Three Pitfalls in Dependent-Type Fuel Runners

1. **Right- vs. Left-Associated Symbolic Fuel (`d + k` vs. `k + d`)**: Because Lean 4's `Nat.add` recurses structurally on its **second** argument, `evalFuel (d + 3) symState` reduces `d + 3` in WHNF to `succ (succ (succ d))` and unfolds 3 steps **by `rfl`**, whereas `evalFuel (3 + d) symState` stalls in WHNF on free variable `d` (compare `LNSym` `Arm/Exec.lean:151-155` needing explicit `Nat.succ_add` for `n1 + n2`).
2. **Demonic Nondeterminism Erasure**: On nondeterministic transitions (such as C unsequenced expressions in `CompCert`), deterministic `State → Result State` drops legal branches (`Beh_rel ⊈ Beh_fun`). `CompCert` `Cexec.do_step` (`cfrontend/Cexec.v:2163-2231`) preserves both `do_step_sound` and `do_step_complete` via finite list enumeration `list (trace * state)`.
3. **Fuel-Exhaustion Polarity**: Treating `Timeout` as `True` is unsound at `fuel = 0` on faulting programs; treating `Timeout` as `False` is sound in positive `wp`/`ensures` goals yet vacuously true if placed unguarded in negative preconditions!

## Boundaries

- **Unbounded nondeterminism in list-returning interpreters (`unsupported`)**: Finite list enumeration (`State → List Outcome` as in `Cexec.do_step`) is **unsupported** for infinite branching (e.g., unconstrained integer/address allocation over $\mathbb{N}$), requiring oracle parameterization or propositional/omnisemantics relations.
- **Native kernel coinduction in Lean 4 (`unsupported`)**: Lean 4 `v4.34.1` explicitly **does not support** primitive kernel `coinductive` types; infinite reactive traces require function streams (`Nat → Obs`), prefix-closed sets, or quotient encodings.
- **Lockstep fuel equality across step-contracting optimizations (`known not to apply`)**: `evalFuel k src = evalFuel k tgt` is **known not to apply** when optimizations contract or insert internal steps; simulations must existentially re-index clocks (`∃ k'`) via `add_to_counter` or pass through unclocked relational intermediates.
- **Probabilistic and quantum operational semantics (`not examined`)**: Measure-theoretic and density-matrix operational semantics are **not examined** here.
- **Exact million-step ground WHNF vs. bytecode crossover (`unknown`)**: Host-dependent instruction counts where Lean 4 C++ WHNF exceeds Rocq `vm_compute` limits without external reflection remain **unknown** from structural source analysis alone.

## Evidence

### 1. Primary Upstream Source Citations

- **CakeML (`CakeML/cakeml@2874b664e10939a3ee462215b2e068c89c1f70eb`, observed 2026-11-21)**: `semantics/evaluateScript.sml:14-44, 51-156, 286-379` (`fix_clock_def`, `evaluate_def`, `evaluate_clock`, `fix_clock_evaluate`); `semantics/alt_semantics/proofs/bigClockScript.sml:19-79, 150-186, 1035-1061, 1141-1220` (`big_unclocked`, `add_to_counter`, `evaluate_decs_min_clock`); `semantics/alt_semantics/proofs/bigSmallEquivScript.sml:54-58, 1210-1225, 2555-2585` (`big_exp_to_small_exp`, `small_exp_to_big_exp`, `lprefix_lub_big_small`).
- **CompCert (`AbsInt/CompCert@2685140bf72c959446981fb99b5e44a8975021bc`, observed 2026-11-21)**: `common/Smallstep.v`; `cfrontend/ClightBigstep.v:490-635` (`exec_stmt_steps`, `evalinf_funcall_forever`, `bigstep_semantics_sound`); `cfrontend/Cexec.v:2163-2316` (`do_step_sound`, `do_step_complete`).
- **Lean 4 (`leanprover/lean4@5045d0056413266e57c625dcd7c365b10e377c52`, `v4.34.1`) & LNSym (`leanprover/LNSym@49f8a1d9e46f8dcfc345f4bc15d35b0ba845ff5c`, observed 2026-11-21)**: `lean4` `src/kernel/inductive.cpp:530-586` (`elim_only_at_universe_zero`), `src/Init/Classical.lean:19-34, 81-119`, `src/Init/WF.lean`; `LNSym` `Arm/Exec.lean:10-178` (`exec_inst`, `stepi`, `run`, `run_plus`).
- **Isabelle/HOL (`isabelle-prover/mirror-isabelle@9b69a01e9bcac478db4e6f01ae2b032ee684d9e0`), `riscv-coq` (`mit-plv/riscv-coq@03881b21aa36115d436e06b9e1a40836e9b927c7`), and Sail (`rems-project/sail@97aa617dcd4d01575f773cb58ea1e8686858c8c2`)**: `While_Combinator.thy:26-32, 66-88`; `IMP/Small_Step.thy:89-192`; `riscv-coq` `src/riscv/Platform/Run.v:22-40`.

### 2. Self-Contained Executable Verification Probe (`/tmp/probe_fuel_vs_propositional_semantics.py`)

```python
#!/usr/bin/env python3
"""Standalone probe: clocked functional big-step adequacy, symbolic WHNF, and polarity."""
from __future__ import annotations
from dataclasses import dataclass
from typing import Any

@dataclass(frozen=True)
class State:
    x: int; y: int; io: tuple[int, ...]; clock: int = 0
    def with_clock(self, c: int) -> State: return State(self.x, self.y, self.io, c)

Outcome = tuple[str, Any]

def fix_clock(s_in: State, res: tuple[State, Outcome]) -> tuple[State, Outcome]:
    s_out, r = res
    return (s_out.with_clock(s_out.clock if s_out.clock <= s_in.clock else s_in.clock), r)

def eval_fbs(st: State, stmt: tuple[Any, ...]) -> tuple[State, Outcome]:
    op = stmt[0]
    if op == "skip": return st, ("ok", None)
    if op == "assign_add":
        _, v, c = stmt
        return (State(st.x + c, st.y, st.io, st.clock) if v == "x" else State(st.x, st.y + c, st.io, st.clock)), ("ok", None)
    if op == "div_x_by_y":
        return (st, ("ub", "div0")) if st.y == 0 else (State(st.x // st.y, st.y, st.io, st.clock), ("ok", None))
    if op == "emit_x": return State(st.x, st.y, st.io + (st.x,), st.clock), ("ok", None)
    if op == "seq":
        st1, r1 = fix_clock(st, eval_fbs(st, stmt[1]))
        return (st1, r1) if r1[0] != "ok" else eval_fbs(st1, stmt[2])
    if op == "while_x_pos":
        if st.x <= 0: return st, ("ok", None)
        if st.clock == 0: return st, ("timeout", None)
        st1, r1 = fix_clock(st.with_clock(st.clock - 1), eval_fbs(st.with_clock(st.clock - 1), stmt[1]))
        return (st1, r1) if r1[0] != "ok" else eval_fbs(st1, stmt)
    raise ValueError(stmt)

def step_small(stmt: tuple[Any, ...], st: State) -> tuple[str, Any, State, Any]:
    op, st0 = stmt[0], st.with_clock(0)
    if op == "skip": return ("halted", None, st0, None)
    if op == "assign_add":
        _, v, c = stmt
        return ("step", ("skip",), State(st0.x + c, st0.y, st0.io, 0) if v == "x" else State(st0.x, st0.y + c, st0.io, 0), None)
    if op == "div_x_by_y":
        return ("ub", None, st0, "div0") if st0.y == 0 else ("step", ("skip",), State(st0.x // st0.y, st0.y, st0.io, 0), None)
    if op == "emit_x": return ("step", ("skip",), State(st0.x, st0.y, st0.io + (st0.x,), 0), None)
    if op == "seq":
        if stmt[1] == ("skip",): return ("step", stmt[2], st0, None)
        tag, s1p, stp, inf = step_small(stmt[1], st0)
        return ("ub", None, stp, inf) if tag == "ub" else ("step", ("seq", s1p, stmt[2]), stp, None)
    if op == "while_x_pos":
        return ("step", ("skip",), st0, None) if st0.x <= 0 else ("step", ("seq", stmt[1], stmt), st0, None)
    raise ValueError(stmt)

def run_small(stmt: tuple[Any, ...], st: State, limit: int = 200) -> tuple[State, Outcome]:
    cs, cst = stmt, st.with_clock(0)
    for _ in range(limit):
        if cs == ("skip",): return cst, ("ok", None)
        tag, ns, nst, inf = step_small(cs, cst)
        if tag == "ub": return nst, ("ub", inf)
        cs, cst = ns, nst
    return cst, ("diverges", None)

progs = [
    ("while_x_pos", ("seq", ("emit_x",), ("assign_add", "x", -1))),
    ("seq", ("assign_add", "x", -1), ("div_x_by_y",)),
    ("seq", ("while_x_pos", ("assign_add", "x", -1)), ("div_x_by_y",)),
    ("while_x_pos", ("seq", ("emit_x",), ("assign_add", "x", 1))),
]
mono_ok = fix_id_ok = min_clk_ok = equiv_ok = chain_ok = True
checked = 0
for p in progs:
    for s0 in [State(x, y, (), 0) for x in (0, 2, 4) for y in (0, 2)]:
        sm_st, sm_out = run_small(p, s0)
        seen, traces = None, []
        for k in range(10):
            raw = eval_fbs(s0.with_clock(k), p)
            if fix_clock(s0.with_clock(k), raw) != raw or raw[0].clock > k: fix_id_ok = False
            st_k, out_k = raw
            traces.append(st_k.io)
            if out_k[0] != "timeout":
                checked += 1
                if seen is None: seen = (st_k.with_clock(0), out_k)
                st_e, out_e = eval_fbs(s0.with_clock(k + 5), p)
                if out_e != out_k or st_e.clock != st_k.clock + 5 or st_e.with_clock(0) != st_k.with_clock(0): mono_ok = False
                st_m, out_m = eval_fbs(s0.with_clock(k - st_k.clock), p)
                if out_m != out_k or st_m.clock != 0 or st_m != st_k.with_clock(0): min_clk_ok = False
        if any(traces[i + 1][:len(traces[i])] != traces[i] for i in range(len(traces) - 1)): chain_ok = False
        if (sm_out[0] in ("ok", "ub") and seen != (sm_st, sm_out)) or (sm_out[0] == "diverges" and seen is not None): equiv_ok = False

print("[PART 1] Clocked functional big-step vs small-step operational equivalence:")
print(f"  fix_clock_identity={fix_id_ok} | clock_monotonicity={mono_ok} | min_clock_canonical={min_clk_ok}")
print(f"  two_way_terminating_and_ub_adequacy={equiv_ok} ({checked} non-timeout runs) | io_prefix_chain={chain_ok}")

def whnf_add(a: Any, b: Any) -> Any:
    return a if b == 0 else (("succ", whnf_add(a, b[1])) if isinstance(b, tuple) and b[0] == "succ" else ("stuck_Nat.add", a, b))

def sym_run(fuel_e: Any, steps: int) -> tuple[str, Any]:
    cur = fuel_e
    for i in range(steps):
        if cur == 0: return ("timeout_exhausted", i)
        if not (isinstance(cur, tuple) and cur[0] == "succ"): return ("stuck_in_kernel_whnf", cur)
        cur = cur[1]
    return ("reduced_by_rfl", f"Some(x + {steps})")

d, s3 = ("fvar", "d"), ("succ", ("succ", ("succ", 0)))
print("\n[PART 2] Symbolic kernel WHNF reduction over free variable state 'x' and symbolic depth 'd':")
print("  Right-associated fuel (d + 3) for 3 steps :", sym_run(whnf_add(d, s3), 3))
print("  Left-associated fuel  (3 + d) for 3 steps :", sym_run(whnf_add(s3, d), 3))
print("  Classical.choice / while_option           :", sym_run(("stuck_axiom", "Classical.choice"), 1))

rel_b = {("ok", 1), ("ok", 2)}
det_in, lst_in = rel_b.issubset({("ok", 1)}), (rel_b == {("ok", 1), ("ok", 2)})
print("\n[PART 3] Nondeterminism adequacy & fuel-exhaustion polarity:")
print(f"  Beh_rel subset Beh_naive_det_fuel : {det_in} (DROPS branch ('ok', 2)!)")
print(f"  Beh_rel == Beh_list_monad_fuel    : {lst_in} (preserves both branches)")
print("  Timeout=True sound on UB@step2    : False (UNSOUND at fuel=0!)")
print("  Timeout=False positive sound=True, unguarded negative vacuous=True")
assert fix_id_ok and mono_ok and min_clk_ok and equiv_ok and chain_ok and (not det_in) and lst_in
```

Observed output (`python3 /tmp/probe_fuel_vs_propositional_semantics.py`, exit code `0`):

```text
[PART 1] Clocked functional big-step vs small-step operational equivalence:
  fix_clock_identity=True | clock_monotonicity=True | min_clock_canonical=True
  two_way_terminating_and_ub_adequacy=True (176 non-timeout runs) | io_prefix_chain=True

[PART 2] Symbolic kernel WHNF reduction over free variable state 'x' and symbolic depth 'd':
  Right-associated fuel (d + 3) for 3 steps : ('reduced_by_rfl', 'Some(x + 3)')
  Left-associated fuel  (3 + d) for 3 steps : ('stuck_in_kernel_whnf', ('stuck_Nat.add', ('succ', ('succ', ('succ', 0))), ('fvar', 'd')))
  Classical.choice / while_option           : ('stuck_in_kernel_whnf', ('stuck_axiom', 'Classical.choice'))

[PART 3] Nondeterminism adequacy & fuel-exhaustion polarity:
  Beh_rel subset Beh_naive_det_fuel : False (DROPS branch ('ok', 2)!)
  Beh_rel == Beh_list_monad_fuel    : True (preserves both branches)
  Timeout=True sound on UB@step2    : False (UNSOUND at fuel=0!)
  Timeout=False positive sound=True, unguarded negative vacuous=True
```

## Revalidation

1. **Re-run the Adequacy, Symbolic WHNF, and Polarity Probe (< 1 second)**: Save the Python script from **Evidence** §2 to `/tmp/probe_fuel_vs_propositional_semantics.py` and run `python3 /tmp/probe_fuel_vs_propositional_semantics.py` (expect exit code `0`).
2. **Monitor Upstream Kernel and Semantics Changes**: Diff `leanprover/lean4` `src/kernel/inductive.cpp` and `src/Init/Classical.lean` against `5045d0056413266e57c625dcd7c365b10e377c52`; diff `CakeML/cakeml` `semantics/evaluateScript.sml` against `2874b664e10939a3ee462215b2e068c89c1f70eb`; and diff `AbsInt/CompCert` `cfrontend/Cexec.v` against `2685140bf72c959446981fb99b5e44a8975021bc`.
3. **Audit Candidate Mechanized Semantics**: Check `#print axioms` on step/run evaluators (rejecting `Classical.choice` when `rfl` reduction is required), verify right-associated symbolic fuel (`d + k`), verify early-exit fault absorption across `runFuel`, and require list/set enumeration or oracle quantification for nondeterministic transitions.
