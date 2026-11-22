# Contract instrumentation: multi-exit `ensures` placement, check-erasure equivalence and flag scoping

## Summary

Lean project: `lean/` (library `ToyContracts`, namespace `Toy.Contracts`), Lean `v4.34.1`, core Lean (no Mathlib, no `Std` import). Every result below is a kernel-checked theorem: the project builds with no `sorry`, and an axiom audit over the built environment finds every declaration depending on at most `propext`, `Classical.choice` and `Quot.sound`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

**Scope.** Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, an open experiment), rustc, Ada, SPARK, JML, Eiffel or C++. Real systems appear in the modeling-bridge subsection of Findings as `derived (modeling bridge)` prose citing documented behaviour.

**Reading the results.** `Lowered g` and `NoChecks g` quantify over every block of `g`, reachable or not (`NoChecks g` also over the prologue); weakenings to reachable blocks are not established. In `UBRefinesAt c tgt src x` the first program (`tgt`) refines the second (`src`), and runs of `tgt` that do not halt are not compared. Placement (`Placement`, `Site`), flag resolution (`Resolution`) and compile-time evaluation (`CtfeMode`) are parameters of the toy, not findings about any compiler.

- **R1** (`run_instr_allExits_eq_instrObs_of_lowered`, theorem, T1): For every contract `c` and every function `g` with `Lowered g` (no block of `g`, reachable or not, ends in the source form `tryQ` of `?`), and for every argument `x` and every fuel `n`: `run c (instr .allExits g) x n = instrObs c x (run c g x n)`. That is, if `Req x` fails, the instrumented run ends with a `requires` failure and no events; otherwise it is the run of `g`, except that a normal return of a value `r` with `Ens x r` false becomes an `ensures` failure with the same events; panics, failed checks, UB, stuck runs and fuel exhaustion are unchanged.
- **R2** (`req_and_ens_of_halts_ret_instr_allExits_lower`, theorem, T1): For every contract `c`, every function `f` as written (no hypothesis on `f`: neither `Lowered f` nor `JumpsInRange f` is assumed), every argument `x`, event list `tr` and value `r`: if the all-exits instrumentation of the lowering, `instr .allExits (lower f)`, halts on `x` with events `tr` and a normal return of `r`, then `Req x` and `Ens x r` both hold.
- **R4** (`halts_lower_iff_of_jumpsInRange`, theorem, T1): For every contract `c`, every function `f` with `JumpsInRange f` (the entry and every jump target of every block, reachable or not, are block indices of `f`; a function with no blocks never satisfies it), every argument `x` and every observation `o`: `lower f` halts on `x` with `o` iff `f` halts on `x` with `o`.
- **R5** (`cex_tailOnly_misses_early_return`, counterexample, T1): There is a lowered function, `gEarly`, and an input, `0`, satisfying `Req` under `c1` (`requires x < 100`, `ensures r ≤ x`), such that: `gEarly` halts on `0` with no events and a normal return of `7` (its run takes the edge `ret .early (.lit 7)` of block `2`; the outcome `ret 7` itself records no provenance), `Ens 0 7` fails, the tail-only instrumentation `instr .tailOnly gEarly` halts with no events and a normal return of `7`, and the all-exits instrumentation `instr .allExits gEarly` halts with no events and an `ensures` failure.
- **R6** (`cex_tailOnly_misses_try_error_after_lowering`, counterexample, T1): There is a function with a `?`, `gTry` (`let y = x - 1` with truncated subtraction, then `y?` with error value `9`, then tail `y`), and an input, `1`, satisfying `Req` under `c1`, such that: `gTry` halts on `1` with no events and a normal return of `9` (the value of the `?` error path, taken because `1 - 1 = 0`), `Ens 1 9` fails, `lower gTry` is lowered, the tail-only instrumentation of `lower gTry` halts with no events and a normal return of `9`, and the all-exits instrumentation of `lower gTry` halts with no events and an `ensures` failure.
- **R7** (`cex_instr_before_lower_misses_try`, counterexample, T1): There is a function that is not lowered, `gTry`, such that at input `1` and fuel `1` under `c1` the all-exits instrumentation `instr .allExits gTry` gives no events and a normal return of `9`, while the contract wrapper `instrObs c1 1 (run c1 gTry 1 1)` gives no events and an `ensures` failure, so the equation of `run_instr_allExits_eq_instrObs_of_lowered` fails without `Lowered`; moreover the instrumented `gTry` halts on `1` with no events and a normal return of `9`, and `Ens 1 9` fails.
- **R8** (`erase_instr_eq_of_noChecks`, theorem, T1): For every placement `p` and every function `g` with `NoChecks g` (no `checkReq`, `checkEns` or `assumeReq` in its prologue or in any block, reachable or not): `erase (instr p g) = g`.
- **R24** (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`, characterization, T1): For every contract `c`, every function `g` with `Lowered g` (no block, reachable or not, ends in `tryQ`; contract statements in `g` are allowed, `NoChecks g` is not assumed) and every input `x` with `Req x`: the all-exits instrumentation `instr .allExits g` and `g` itself are fuel-exactly identical at `x` (`RunEqAt`: the same observation at every fuel, including the events emitted before the fuel runs out) iff every normal return of `g` on `x` satisfies `Ens` (`EnsOnReturnsAt c g x`); and the same iff holds with identity of halting observations (`HaltsEqAt`) in place of `RunEqAt`.
- **R9** (`erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`, characterization, T1): For every contract `c`, every function `g` with `Lowered g` and `NoChecks g` (no block, reachable or not, ends in `tryQ`; no contract statement in the prologue or in any block, reachable or not), and every input `x` with `Req x`: the erasure `erase (instr .allExits g)` and the all-exits instrumentation `instr .allExits g` are fuel-exactly identical at `x` (`RunEqAt`: the same observation at every fuel, including the events emitted before the fuel runs out) iff every normal return of `g` on `x` satisfies `Ens` (`EnsOnReturnsAt c g x`); and the same iff holds with identity of halting observations (`HaltsEqAt`) in place of `RunEqAt`.
- **R10** (`erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks`, characterization, T1): For every contract `c` and every function `g` with `Lowered g` and `NoChecks g` (both over every block, reachable or not; `NoChecks g` also over the prologue): the erasure `erase (instr .allExits g)` is fuel-exactly identical to the all-exits instrumentation at every input satisfying `Req` iff the static obligation `StaticObligation c g` holds (for every `x` with `Req x`, every normal return `r` of `g` on `x` satisfies `Ens x r`); and the same iff holds with `HaltsEqAt` in place of `RunEqAt`.
- **R11** (`not_haltsEqAt_erase_instr_of_req_false`, theorem, T1): For every contract `c`, placement `p`, function `g` (no hypothesis on `g` or `p`) and input `x` with `Req x` false: the instrumentation `instr p g` ends with a `requires` failure and no events at every fuel; the erasure `erase (instr p g)` contains no contract statement in its prologue or in any block, reachable or not (`NoChecks`), and its run never ends with a failed check, at any fuel; and the two do not have the same halting observations at `x`.
- **R12** (`run_assumeErase_eq_ite_req`, theorem, T0): For every contract `c`, every function `q`, input `x` and fuel `n`: running `assumeErase q` (the erasure of `q` with `assumeReq` first in the prologue) gives the same observation as running `erase q` if `Req x` holds, and gives UB with no events (`⟨[], .ub⟩`) if `Req x` fails. The instances of interest are `q = instr p g`.
- **R13** (`instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`, theorem, T0): For every contract `c`, every function `g` with `NoChecks g` (no contract statement in its prologue or in any block, reachable or not; `Lowered g` is not assumed) and every input `x` with `StaticObligationAt c g x` (if `Req x`, every normal return `r` of `g` on `x` satisfies `Ens x r`): the checked program `instr .allExits g` UB-refines the assume-erased program `assumeErase (instr .allExits g)` at `x` (`UBRefinesAt`, with the checked program as target and the assume-erased program as source): every halting observation of the checked program is a halting observation of the assume-erased program, or the assume-erased program halts with UB after a prefix of its events.
- **R14** (`not_assumeErase_ubRefinesAt_instr_of_req_false`, theorem, T0): For every contract `c`, placement `p`, function `g` (no hypothesis on `g` or `p`) and input `x` with `Req x` false: the assume-erased program `assumeErase (instr p g)` reaches UB with no events at every fuel; the checked program `instr p g` ends with a `requires` failure and no events at every fuel (so it never reaches UB); and the assume-erased program does not UB-refine the checked program at `x` (`UBRefinesAt`, with the assume-erased program as target and the checked program as source).
- **R15** (`callRun_eq_ite_governingFlag_of_lowered`, theorem, T1): For every flag assignment `fl`, placement `s`, resolution `res`, call site `cs`, contract `c`, callee `g` with `Lowered g` (no block, reachable or not, ends in `tryQ`), argument `x` and fuel `n`: the cross-crate call `callRun fl s res cs c g x n` (compilation in the defining crate, instantiation in the instantiating crate and the call in the calling crate, each step reading the flag of its own crate and no other; callee-side checks are inserted by `instr .allExits`) equals `instrObs c x (run c g x n)` if `fl (governingCrate s res cs)` is true and `run c g x n` if it is false. The governing crate is the calling crate for caller-side placement; under callee-side placement it is the defining crate when the flag test is resolved at definition or the callee is not generic, and the instantiating crate for a generic callee whose flag test is resolved at instantiation.
- **R16** (`detects_iff_governingFlag_of_lowered_of_noChecks_of_violation`, characterization, T1): For every flag assignment `fl`, placement `s`, resolution `res`, call site `cs`, contract `c`, callee `g` with `Lowered g` and `NoChecks g` (both over every block, reachable or not; `NoChecks g` also over the prologue), and argument `x` with `ViolationAt c g x` (`Req x` fails, or `Req x` holds and `g` halts on `x` with a normal return of a value violating `Ens`): the call (`callRun`, whose callee-side checks are inserted by `instr .allExits`) reports a failed check for some fuel (`Detects`) iff `fl (governingCrate s res cs)` is true.
- **R17** (`callRun_eq_run_of_not_violation`, theorem, T1): For every flag assignment `fl`, placement `s`, resolution `res`, call site `cs`, contract `c`, callee `g` (neither `Lowered g` nor `NoChecks g` assumed), argument `x` with `¬ ViolationAt c g x` (`Req x` holds and every normal return of `g` on `x` satisfies `Ens`) and fuel `n`: `callRun fl s res cs c g x n = run c g x n`.
- **R18** (`cex_same_flags_detection_depends_on_placement`, counterexample, T1): There is a call site, `cs1` (crate `0` calls a non-generic function defined in crate `1`), and a flag assignment, `flCallerOn` (crate `0` on, every other crate off), such that the violation of `gEarly` on `0` under `c1` is reported under caller-side placement and is not reported under callee-side placement, both with resolution at definition.
- **R19** (`cex_calleeSide_atInstantiation_definingFlag_on_undetected`, counterexample, T1): There is a call site, `csGen` (crate `0` calls a generic function defined in crate `1` and instantiated in crate `0`), and a flag assignment, `flDefOn` (crate `1` on, every other crate off), such that: the crate holding the callee-side check is the defining crate (`holder .calleeSide csGen = csGen.defCrate`), its flag is on, the flag of the instantiating crate `0` is off, and under callee-side placement (checks inserted by `instr .allExits`) with resolution at instantiation the violation of `gEarly` on `0` under `c1` is not reported; it is reported under resolution at definition, and for the non-generic call site `cs1` it is reported under resolution at instantiation.
- **R20** (`runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`, characterization, T1): For every contract `c`, every function `g` with `Lowered g` and `NoChecks g` (both over every block, reachable or not; `NoChecks g` also over the prologue), every argument `x` and value `r`: if compile-time evaluation that skips checks, applied to the all-exits instrumentation, produces the constant `r` (`CtfeConst .allExits .skipChecks c g x r`), then the all-exits runtime-checked call returns `r` (`RuntimeValue .allExits c g x r`) iff `Req x` and `Ens x r` both hold.
- **R21** (`runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`, characterization, T1): For every contract `c`, every function `g` with `Lowered g` and `NoChecks g` (both over every block, reachable or not; `NoChecks g` also over the prologue), every argument `x` with `Req x` and every value `r`: if compile-time evaluation that skips checks, applied to the all-exits instrumentation, produces the constant `r` (`CtfeConst .allExits .skipChecks c g x r`), then the all-exits runtime-checked call returns `r` (`RuntimeValue .allExits c g x r`) iff the static obligation holds at `x` (`StaticObligationAt c g x`).
- **R22** (`cex_ctfeSkip_requires_violation`, counterexample, T1): There is a lowered function without contract statements (in its prologue or in any block, reachable or not), `gEarly`, and an input, `100`, violating `Req` under `c1`, such that: check-skipping compile-time evaluation of the all-exits instrumentation yields the constant `100`; the static obligation at `100` holds vacuously; the all-exits runtime-checked call halts with a `requires` failure and no events at every fuel and returns no value at all (`∀ r, ¬ RuntimeValue .allExits c1 gEarly 100 r`); and check-evaluating compile-time evaluation of the all-exits instrumentation yields no constant at all.
- **R23** (`cex_ctfeSkip_ensures_violation`, counterexample, T1): There is a lowered function without contract statements (in its prologue or in any block, reachable or not), `gEarly`, and an input, `0`, satisfying `Req` under `c1`, such that: check-skipping compile-time evaluation of the all-exits instrumentation yields the constant `7`; `Ens 0 7` fails; the all-exits runtime-checked call halts with an `ensures` failure and no events and returns no value at all (`∀ r, ¬ RuntimeValue .allExits c1 gEarly 0 r`); and check-evaluating compile-time evaluation of the all-exits instrumentation yields no constant at all.

Card identifiers are labels local to this report; they are not consecutive (there is no R3, see Boundaries). Non-claims for every result are listed with its card under Findings and collected, result by result, under Boundaries.

## Applicability

**Model fidelity.** A toy control-flow-graph language, not a mirror of any compiler's data structures. A function has one immutable natural-number argument, a total zero-initialised store of natural-number locals, an event stream (`emit`), a prologue run once on entry, several return edges tagged with their source construct (tail expression, early `return`, the error path of `?`), and panics. A contract is a pair of Boolean-valued clauses; the contract statements `checkReq`, `checkEns o` and `assumeReq` carry no predicate of their own and evaluate the clauses of the contract under which the function runs. Instrumentation inserts statements (`checkReq` first in the prologue, `checkEns o` before the `ret` edges a placement selects); erasure deletes every contract statement; `assumeErase` additionally puts a UB-on-false assumption of `Req` first in the prologue. A cross-crate call is a pipeline of three per-crate steps (compilation in the defining crate, instantiation of a generic body in the instantiating crate, the call in the calling crate), each reading the flag of its own crate; compile-time evaluation runs the instrumentation with or without its contract statements. Placement, flag resolution and compile-time behaviour are explicit parameters. Truncated natural-number subtraction (`Rvalue.sub`, `3 - 5 = 0`) is used by `gTry`. Known gaps: no calls inside functions (so no body outlining), no memory or references, no mutable parameters, clauses cannot fail, diverge or have effects, no unwinding cleanup, no exceptional postconditions, no nondeterminism, and no timing.

**What the definitions are meant to capture.** The toy is meant to capture design choices for run-time contract checking in a compiler for a language with several kinds of function exit and separately compiled crates: where `ensures` checks are inserted (`Placement`: before every return edge, `.allExits`, or before the return edges of the tail expression, `.tailOnly`); whether `?` is lowered to an explicit return edge before instrumentation (`lower`); what deleting every check (`erase`) or replacing the checks by a UB-on-false assumption (`assumeErase`) does to the observable behaviour; which crate's flag decides whether a cross-crate call is checked (`Site`, `Resolution`, `CallSite`, `callRun`); and how compile-time evaluation that skips or evaluates checks (`CtfeMode`) relates to the runtime-checked call. The vocabulary (`requires`, `ensures`, `?`, crates, a compile-time flag) follows the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open); Ada 2012, SPARK, JML, Eiffel and C++ supply documented analogues. Placement, flag resolution and compile-time behaviour are parameters of the toy, not findings about any compiler.

**Scope.** Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature, rustc, Ada, SPARK, JML, Eiffel or C++. The connections drawn in the modeling-bridge subsection of Findings are analogies labelled `derived (modeling bridge)`, not proved relations.

**Subjects and how they relate.** `REPORT.json` lists: the Lean toolchain release that checks every theorem; rust-lang/rust at commit `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`, whose `library/core/src/contracts.rs` and unstable-book feature directory were examined for documentation of check placement, the enabling flag and compile-time evaluation (none was found, which is why these are toy parameters); the Ada 2012 Reference Manual, the JML Reference Manual, the SPARK Reference Manual 28.0w, the LLVM Language Reference, and WG21 documents P1774R8 and P2900R14, whose documented behaviour is compared with toy definitions in the modeling bridge; and the papers and books cited as prior art. Every theorem in the report is a statement about the toy model; it neither establishes nor refutes the corresponding claims about any listed subject. Each subject other than the toolchain is related to the toy model by analogy or citation, never by a proved relation.

**Versions.** Lean `leanprover/lean4:v4.34.1` with core Lean: no Mathlib, no `Std` import, no Lake dependencies. The SPARK Reference Manual and the LLVM Language Reference are moving documents without an immutable revision identifier; the quoted text was read on 2026-11-21. All other evidence was also acquired on 2026-11-21.

## Findings

Findings are organised as the model (each definition quoted with what it is meant to capture, and proved positive and negative examples), the result cards, the declarations the cards cite by name, and the modeling bridge. Every theorem quoted below has `Basis: execution (Lean kernel check)`: it builds under the pinned toolchain without `sorry`, and its axioms are listed under Evidence. Statements about real systems are confined to the modeling-bridge subsection, as separate claims with `Basis: derived (modeling bridge)`.

### 1. The model (toy) and what each definition captures

Model fidelity and known gaps are described under Applicability.

#### 1.1 Syntax (`lean/ToyContracts/Syntax.lean`)

`Operand`: Operands: the (single, immutable) argument, a literal, or a local.

```lean
-- lean/ToyContracts/Syntax.lean:12-16
inductive Operand where
  | arg
  | lit (n : Nat)
  | loc (i : Nat)
  deriving DecidableEq, Repr
```

`Rvalue`: Right-hand sides. `sub` is truncated natural-number subtraction (`3 - 5 = 0`).

```lean
-- lean/ToyContracts/Syntax.lean:19-23
inductive Rvalue where
  | use (o : Operand)
  | add (a b : Operand)
  | sub (a b : Operand)
  deriving DecidableEq, Repr
```

`CheckKind`: Which contract clause a failed runtime check belongs to.

```lean
-- lean/ToyContracts/Syntax.lean:26-29
inductive CheckKind where
  | pre
  | post
  deriving DecidableEq, Repr
```

`Stmt`: Statements. `checkReq` and `checkEns o` are runtime contract checks and `assumeReq` is the UB-on-false assumption of the `requires` clause (executing it when the clause is false is undefined behaviour). These three contract statements carry no predicate of their own: each evaluates a clause of the contract under which the function is run, so a contract statement written in a function as written tests the same clauses as the checks that instrumentation inserts.

```lean
-- lean/ToyContracts/Syntax.lean:36-42
inductive Stmt where
  | assign (i : Nat) (rv : Rvalue)
  | emit (o : Operand)
  | checkReq
  | checkEns (o : Operand)
  | assumeReq
  deriving DecidableEq, Repr
```

`ExitKind`: Provenance of a return edge, recorded by lowering: the tail expression, an explicit early `return`, or the error path of `?`.

```lean
-- lean/ToyContracts/Syntax.lean:46-50
inductive ExitKind where
  | tail
  | early
  | tryErr
  deriving DecidableEq, Repr
```

`Term`: Terminators. `branch o b₁ b₀` goes to `b₁` if `o ≠ 0` and to `b₀` if `o = 0`. `tryQ o e b` is the source form of `?`: if `o ≠ 0` it continues at `b`, and if `o = 0` it returns the value of `e` (the error path) without a separate return edge; `lower` turns it into a `branch` to a fresh block ending in `ret .tryErr e`. `ret k o` is a normal return of the value of `o` along a return edge of provenance `k`. `panic` ends the run with the outcome `panic`; it is not a normal return, and no unwinding or cleanup is modelled.

```lean
-- lean/ToyContracts/Syntax.lean:58-64
inductive Term where
  | goto (b : Nat)
  | branch (o : Operand) (b₁ b₀ : Nat)
  | tryQ (o : Operand) (e : Operand) (b : Nat)
  | ret (k : ExitKind) (o : Operand)
  | panic
  deriving DecidableEq, Repr
```

`Block`: A basic block: straight-line statements followed by one terminator.

```lean
-- lean/ToyContracts/Syntax.lean:67-70
structure Block where
  stmts : List Stmt
  term : Term
  deriving DecidableEq, Repr
```

`Fn`: A function: a prologue executed once on entry (any statement list; instrumentation puts the `requires` check first in it, and no theorem requires it to be empty), an entry block index, and the blocks, indexed by position in the list. A jump to an index outside the list makes the run `stuck`.

```lean
-- lean/ToyContracts/Syntax.lean:76-80
structure Fn where
  prologue : List Stmt
  entry : Nat
  blocks : List Block
  deriving DecidableEq, Repr
```

`Contract`: A contract: a decidable `requires` clause on the argument and a decidable `ensures` clause on the argument and the returned value, both represented as Boolean-valued functions.

```lean
-- lean/ToyContracts/Syntax.lean:84-86
structure Contract where
  req : Nat → Bool
  ens : Nat → Nat → Bool
```

`Outcome`: How a run ends. `ret r` is a normal return; `panic` a panic exit (the run ends; no unwinding is modelled); `checkFail k` a failed runtime contract check (an observable abort, not undefined behaviour); `ub` undefined behaviour (produced by a failing `assumeReq`; no other statement or terminator produces it); `stuck` a jump to a missing block; `fuelOut` means the fuel ran out before the run ended.

```lean
-- lean/ToyContracts/Syntax.lean:93-100
inductive Outcome where
  | ret (r : Nat)
  | panic
  | checkFail (k : CheckKind)
  | ub
  | stuck
  | fuelOut
  deriving DecidableEq, Repr
```

`Obs`: An observation: the emitted events (in order) and how the run ended.

```lean
-- lean/ToyContracts/Syntax.lean:103-106
structure Obs where
  events : List Nat
  outcome : Outcome
  deriving DecidableEq, Repr
```

#### 1.2 Reference semantics (`lean/ToyContracts/Semantics.lean`)

`Store`: The store of locals: total, zero-initialised.

```lean
-- lean/ToyContracts/Semantics.lean:15-15
abbrev Store := Nat → Nat
```

`Store.set`: Point update of a store.

```lean
-- lean/ToyContracts/Semantics.lean:18-18
def Store.set (σ : Store) (i v : Nat) : Store := fun j => if j = i then v else σ j
```

`evalOp`: Operand evaluation.

```lean
-- lean/ToyContracts/Semantics.lean:21-24
def evalOp (x : Nat) (σ : Store) : Operand → Nat
  | .arg => x
  | .lit n => n
  | .loc i => σ i
```

`evalRv`: Right-hand-side evaluation (`sub` is truncated subtraction).

```lean
-- lean/ToyContracts/Semantics.lean:27-30
def evalRv (x : Nat) (σ : Store) : Rvalue → Nat
  | .use o => evalOp x σ o
  | .add a b => evalOp x σ a + evalOp x σ b
  | .sub a b => evalOp x σ a - evalOp x σ b
```

`SR`: Result of executing a statement list: continue with a store and events, or stop with an outcome (a failed check or UB) and the events emitted so far.

```lean
-- lean/ToyContracts/Semantics.lean:34-36
inductive SR where
  | cont (σ : Store) (ev : List Nat)
  | stop (ev : List Nat) (o : Outcome)
```

`execStmts`: Execute a statement list. A `checkReq` (resp. `checkEns o`) whose clause is false stops with `checkFail .pre` (resp. `checkFail .post`); an `assumeReq` whose clause is false stops with `ub`.

```lean
-- lean/ToyContracts/Semantics.lean:40-49
def execStmts (c : Contract) (x : Nat) : List Stmt → Store → List Nat → SR
  | [], σ, ev => .cont σ ev
  | .assign i rv :: ss, σ, ev => execStmts c x ss (σ.set i (evalRv x σ rv)) ev
  | .emit o :: ss, σ, ev => execStmts c x ss σ (ev ++ [evalOp x σ o])
  | .checkReq :: ss, σ, ev =>
      if c.req x then execStmts c x ss σ ev else .stop ev (.checkFail .pre)
  | .checkEns o :: ss, σ, ev =>
      if c.ens x (evalOp x σ o) then execStmts c x ss σ ev else .stop ev (.checkFail .post)
  | .assumeReq :: ss, σ, ev =>
      if c.req x then execStmts c x ss σ ev else .stop ev .ub
```

`runFrom`: Run from block `b` with fuel `n`, store `σ` and events `ev`.

```lean
-- lean/ToyContracts/Semantics.lean:52-67
def runFrom (c : Contract) (f : Fn) (x : Nat) : Nat → Nat → Store → List Nat → Obs
  | 0, _, _, ev => ⟨ev, .fuelOut⟩
  | n + 1, b, σ, ev =>
    match f.blocks[b]? with
    | none => ⟨ev, .stuck⟩
    | some blk =>
      match execStmts c x blk.stmts σ ev with
      | .stop ev' o => ⟨ev', o⟩
      | .cont σ' ev' =>
        match blk.term with
        | .goto b' => runFrom c f x n b' σ' ev'
        | .branch o b₁ b₀ => runFrom c f x n (if evalOp x σ' o = 0 then b₀ else b₁) σ' ev'
        | .tryQ o e b' =>
            if evalOp x σ' o = 0 then ⟨ev', .ret (evalOp x σ' e)⟩ else runFrom c f x n b' σ' ev'
        | .ret _ o => ⟨ev', .ret (evalOp x σ' o)⟩
        | .panic => ⟨ev', .panic⟩
```

`run`: Run a function on argument `x` with fuel `n`: the prologue (no fuel), then the entry block.

```lean
-- lean/ToyContracts/Semantics.lean:70-73
def run (c : Contract) (f : Fn) (x n : Nat) : Obs :=
  match execStmts c x f.prologue (fun _ => 0) [] with
  | .stop ev o => ⟨ev, o⟩
  | .cont σ ev => runFrom c f x n f.entry σ ev
```

`Halts`: `f` halts on `x` with the final (non-`fuelOut`) observation `o`, for some fuel.

```lean
-- lean/ToyContracts/Semantics.lean:76-77
def Halts (c : Contract) (f : Fn) (x : Nat) (o : Obs) : Prop :=
  o.outcome ≠ .fuelOut ∧ ∃ n, run c f x n = o
```

`RunEqAt`: Fuel-exact observational identity at `x`: at every fuel the two runs give the same observation (final outcome with its events, or the events emitted before the fuel ran out).

```lean
-- lean/ToyContracts/Semantics.lean:81-82
def RunEqAt (c : Contract) (p q : Fn) (x : Nat) : Prop :=
  ∀ n, run c p x n = run c q x n
```

`HaltsEqAt`: Identity of final observations at `x`: the same halting observations (events and outcome).

```lean
-- lean/ToyContracts/Semantics.lean:85-86
def HaltsEqAt (c : Contract) (p q : Fn) (x : Nat) : Prop :=
  ∀ o, Halts c p x o ↔ Halts c q x o
```

#### 1.3 Lowering, instrumentation, erasure and obligations (`lean/ToyContracts/Instr.lean`)

`Term.isTryQ`: Is the terminator the source form of `?`?

```lean
-- lean/ToyContracts/Instr.lean:12-14
def Term.isTryQ : Term → Bool
  | .tryQ .. => true
  | _ => false
```

`Term.targets`: Jump targets of a terminator.

```lean
-- lean/ToyContracts/Instr.lean:17-22
def Term.targets : Term → List Nat
  | .goto b => [b]
  | .branch _ b₁ b₀ => [b₁, b₀]
  | .tryQ _ _ b => [b]
  | .ret .. => []
  | .panic => []
```

`lowerTerm`: Lowered terminator of block `i` when the function has `base` blocks: `?` becomes a `branch` whose zero side goes to the fresh block `base + i`.

```lean
-- lean/ToyContracts/Instr.lean:26-28
def lowerTerm (base i : Nat) : Term → Term
  | .tryQ o _ b => .branch o b (base + i)
  | t => t
```

`errBlock`: The fresh block placed at index `base + i` for block `i`: a `ret .tryErr e` return edge if block `i` ends in `tryQ _ e _`, and a `panic` block otherwise (no jump of a function whose jumps are all in range reaches it).

```lean
-- lean/ToyContracts/Instr.lean:33-36
def errBlock (blk : Block) : Block :=
  match blk.term with
  | .tryQ _ e _ => ⟨[], .ret .tryErr e⟩
  | _ => ⟨[], .panic⟩
```

`lower`: Lowering of `?` into explicit return edges: every `tryQ o e b` in block `i` becomes `branch o b (n + i)` (with `n` the number of blocks), and block `n + i` is `ret .tryErr e`. Lowering always appends exactly `n` blocks, one per original block (a `panic` block for every block that does not end in `?`), so `lower f ≠ f` whenever `f` has at least one block, even if `f` contains no `?`. Early returns are already explicit `ret .early` edges.

```lean
-- lean/ToyContracts/Instr.lean:43-47
def lower (f : Fn) : Fn :=
  { f with
    blocks := (f.blocks.mapIdx fun i blk =>
                { blk with term := lowerTerm f.blocks.length i blk.term })
              ++ f.blocks.map errBlock }
```

`Lowered`: `g` is lowered: no block of `g`, reachable or not, ends in the source form of `?`, so every normal return is a `ret` edge.

```lean
-- lean/ToyContracts/Instr.lean:51-52
def Lowered (g : Fn) : Prop :=
  g.blocks.all (fun blk => !blk.term.isTryQ) = true
```

`JumpsInRange`: Every jump target of every block, reachable or not, and the entry are block indices of `f`. A function with no blocks never satisfies it (its entry is not a block index).

```lean
-- lean/ToyContracts/Instr.lean:56-58
def JumpsInRange (f : Fn) : Prop :=
  f.entry < f.blocks.length ∧
    f.blocks.all (fun blk => blk.term.targets.all (· < f.blocks.length)) = true
```

```lean
-- lean/ToyContracts/Instr.lean:60-60
instance (g : Fn) : Decidable (Lowered g) := inferInstanceAs (Decidable (_ = true))
```

```lean
-- lean/ToyContracts/Instr.lean:61-61
instance (f : Fn) : Decidable (JumpsInRange f) := inferInstanceAs (Decidable (_ ∧ _))
```

`Placement`: Placement policy for `ensures` checks: at every return edge, or at the return edge of the tail expression only (the naive policy).

```lean
-- lean/ToyContracts/Instr.lean:67-70
inductive Placement where
  | allExits
  | tailOnly
  deriving DecidableEq, Repr
```

`Placement.selects`: Does the policy put an `ensures` check on a return edge of the given provenance?

```lean
-- lean/ToyContracts/Instr.lean:73-75
def Placement.selects : Placement → ExitKind → Bool
  | .allExits, _ => true
  | .tailOnly, k => k == .tail
```

`instrBlock`: Instrument one block: append `checkEns o` before a selected `ret k o`.

```lean
-- lean/ToyContracts/Instr.lean:78-81
def instrBlock (p : Placement) (blk : Block) : Block :=
  match blk.term with
  | .ret k o => if p.selects k then { blk with stmts := blk.stmts ++ [.checkEns o] } else blk
  | _ => blk
```

`instr`: Runtime contract instrumentation: a `requires` check first in the prologue, and an `ensures` check (on the returned value) immediately before every return edge the policy selects. Blocks keep their indices; panics and `?` terminators get no check.

```lean
-- lean/ToyContracts/Instr.lean:86-89
def instr (p : Placement) (g : Fn) : Fn :=
  { prologue := .checkReq :: g.prologue
    entry := g.entry
    blocks := g.blocks.map (instrBlock p) }
```

`Stmt.isContract`: Contract statements: runtime checks and the `requires` assumption.

```lean
-- lean/ToyContracts/Instr.lean:92-96
def Stmt.isContract : Stmt → Bool
  | .checkReq => true
  | .checkEns _ => true
  | .assumeReq => true
  | _ => false
```

`NoChecks`: `g` contains no contract statement (`checkReq`, `checkEns`, `assumeReq`) in its prologue or in any block, reachable or not.

```lean
-- lean/ToyContracts/Instr.lean:100-102
def NoChecks (g : Fn) : Prop :=
  g.prologue.all (fun s => !s.isContract) = true ∧
    g.blocks.all (fun blk => blk.stmts.all (fun s => !s.isContract)) = true
```

```lean
-- lean/ToyContracts/Instr.lean:104-104
instance (g : Fn) : Decidable (NoChecks g) := inferInstanceAs (Decidable (_ ∧ _))
```

`erase`: Erasure: delete every contract statement, whether instrumentation inserted it or the function as written already contained it.

```lean
-- lean/ToyContracts/Instr.lean:108-112
def erase (p : Fn) : Fn :=
  { prologue := p.prologue.filter (fun s => !s.isContract)
    entry := p.entry
    blocks := p.blocks.map fun blk =>
      { blk with stmts := blk.stmts.filter (fun s => !s.isContract) } }
```

`assumeErase`: Erasure plus an assumption of the `requires` clause on entry (UB when it is false).

```lean
-- lean/ToyContracts/Instr.lean:115-116
def assumeErase (p : Fn) : Fn :=
  { erase p with prologue := .assumeReq :: (erase p).prologue }
```

`wrapObs`: Post-check of a final value: a normal return of `r` stays a return if `Ens x r` holds and becomes `checkFail .post` (with the same events) otherwise; every other observation (panic, failed check, UB, stuck, fuel exhausted) is unchanged.

```lean
-- lean/ToyContracts/Instr.lean:123-125
def wrapObs (c : Contract) (x : Nat) : Obs → Obs
  | ⟨tr, .ret r⟩ => if c.ens x r then ⟨tr, .ret r⟩ else ⟨tr, .checkFail .post⟩
  | o => o
```

`instrObs`: The contract wrapper on observations: if `Req x` fails, a `requires` failure with no events; otherwise the post-check of the unchecked observation.

```lean
-- lean/ToyContracts/Instr.lean:129-130
def instrObs (c : Contract) (x : Nat) (o : Obs) : Obs :=
  if c.req x then wrapObs c x o else ⟨[], .checkFail .pre⟩
```

`EnsOnReturnsAt`: Every normal return of `g` on `x` (for some fuel) satisfies the `ensures` clause.

```lean
-- lean/ToyContracts/Instr.lean:135-136
def EnsOnReturnsAt (c : Contract) (g : Fn) (x : Nat) : Prop :=
  ∀ tr r, Halts c g x ⟨tr, .ret r⟩ → c.ens x r = true
```

`StaticObligationAt`: The static obligation at `x`: if `Req x`, every normal return of `g` on `x` satisfies `Ens`.

```lean
-- lean/ToyContracts/Instr.lean:139-140
def StaticObligationAt (c : Contract) (g : Fn) (x : Nat) : Prop :=
  c.req x = true → EnsOnReturnsAt c g x
```

`StaticObligation`: The static obligation: `∀ x, Req x → g x returns r → Ens x r`.

```lean
-- lean/ToyContracts/Instr.lean:143-144
def StaticObligation (c : Contract) (g : Fn) : Prop :=
  ∀ x, StaticObligationAt c g x
```

`UBRefinesAt`: UB-licensed refinement of halting observations at `x`, with `tgt` the refining (target) program and `src` the refined (source) program: every halting observation of `tgt` is one of `src`, or `src` reaches UB after a prefix of its events. Replacing `src` by `tgt` can thus remove UB but not add it. Runs of `tgt` that do not halt are not compared: a `tgt` with no halting observation at `x` refines every `src` at `x` (`ubRefinesAt_of_forall_not_halts`).

```lean
-- lean/ToyContracts/Instr.lean:151-153
def UBRefinesAt (c : Contract) (tgt src : Fn) (x : Nat) : Prop :=
  ∀ o, Halts c tgt x o →
    Halts c src x o ∨ ∃ tr, Halts c src x ⟨tr, .ub⟩ ∧ tr <+: o.events
```

#### 1.4 Crates and compile-time evaluation (`lean/ToyContracts/Crates.lean`)

`Site`: Where the checks of a call are placed: in the callee's body (compiled into it by the defining crate, or, for a generic callee whose flag test is resolved at instantiation, by the crate that instantiates it), or around the call in the caller.

```lean
-- lean/ToyContracts/Crates.lean:22-25
inductive Site where
  | calleeSide
  | callerSide
  deriving DecidableEq, Repr
```

`Resolution`: Where the flag test of a callee-side check is resolved: with the definition, or where a generic callee body is instantiated.

```lean
-- lean/ToyContracts/Crates.lean:29-32
inductive Resolution where
  | atDefinition
  | atInstantiation
  deriving DecidableEq, Repr
```

`CallSite`: A cross-crate call: the calling crate, the defining crate, the crate in which a generic callee body is instantiated (not used for a non-generic callee), and whether the callee is generic. Crates are named by natural numbers.

```lean
-- lean/ToyContracts/Crates.lean:37-42
structure CallSite where
  callerCrate : Nat
  defCrate : Nat
  instCrate : Nat
  generic : Bool
  deriving DecidableEq, Repr
```

`holder`: The crate whose source holds the check: the defining crate for callee-side placement, the calling crate for caller-side placement.

```lean
-- lean/ToyContracts/Crates.lean:46-48
def holder : Site → CallSite → Nat
  | .calleeSide, cs => cs.defCrate
  | .callerSide, cs => cs.callerCrate
```

`governingCrate`: The crate whose flag decides whether the call's checks run, as a function of placement, resolution and call site.

```lean
-- lean/ToyContracts/Crates.lean:52-55
def governingCrate : Site → Resolution → CallSite → Nat
  | .callerSide, _, cs => cs.callerCrate
  | .calleeSide, .atDefinition, cs => cs.defCrate
  | .calleeSide, .atInstantiation, cs => if cs.generic then cs.instCrate else cs.defCrate
```

`Exported`: What the defining crate exports for a callee: a compiled body, or a generic body that the instantiating crate compiles.

```lean
-- lean/ToyContracts/Crates.lean:59-62
inductive Exported where
  | compiled (body : Fn)
  | template (body : Fn)
  deriving DecidableEq, Repr
```

`compileInDefCrate`: Compilation of callee `g` (as written) in the defining crate, which reads its own flag `defFlag`. Under callee-side placement it compiles the all-exits instrumentation of `g` if its flag is on and `g` itself otherwise, except that a generic callee whose flag test is resolved at instantiation is exported uncompiled. Under caller-side placement the callee carries no checks.

```lean
-- lean/ToyContracts/Crates.lean:68-73
def compileInDefCrate (defFlag : Bool) (s : Site) (res : Resolution) (generic : Bool) (g : Fn) :
    Exported :=
  match s, res, generic with
  | .calleeSide, .atInstantiation, true => .template g
  | .calleeSide, _, _ => .compiled (if defFlag then instr .allExits g else g)
  | .callerSide, _, _ => .compiled g
```

`instantiateIn`: Instantiation in the instantiating crate, which reads its own flag `instFlag`: a compiled body is used as is; a generic body is compiled with the all-exits instrumentation if the flag is on.

```lean
-- lean/ToyContracts/Crates.lean:77-79
def instantiateIn (instFlag : Bool) : Exported → Fn
  | .compiled body => body
  | .template body => if instFlag then instr .allExits body else body
```

`callInCallerCrate`: The call in the calling crate, which reads its own flag `callerFlag`: under caller-side placement with the flag on, `Req` is checked before the call and `Ens` on the value the call returns (`instrObs`); otherwise the callee body runs unwrapped.

```lean
-- lean/ToyContracts/Crates.lean:84-87
def callInCallerCrate (callerFlag : Bool) (s : Site) (c : Contract) (body : Fn) (x n : Nat) : Obs :=
  match s with
  | .calleeSide => run c body x n
  | .callerSide => if callerFlag then instrObs c x (run c body x n) else run c body x n
```

`callRun`: Observation of a cross-crate call of callee `g` (as written) under per-crate flags `fl`, at fuel `n`: the three per-crate steps, each given the flag of its own crate.

```lean
-- lean/ToyContracts/Crates.lean:91-94
def callRun (fl : Nat → Bool) (s : Site) (res : Resolution) (cs : CallSite) (c : Contract)
    (g : Fn) (x n : Nat) : Obs :=
  callInCallerCrate (fl cs.callerCrate) s c
    (instantiateIn (fl cs.instCrate) (compileInDefCrate (fl cs.defCrate) s res cs.generic g)) x n
```

`ViolationAt`: A contract violation at `x`: `Req x` fails, or `Req x` holds and `g` returns (for some fuel) a value violating `Ens`.

```lean
-- lean/ToyContracts/Crates.lean:98-99
def ViolationAt (c : Contract) (g : Fn) (x : Nat) : Prop :=
  c.req x = false ∨ (c.req x = true ∧ ∃ tr r, Halts c g x ⟨tr, .ret r⟩ ∧ c.ens x r = false)
```

`Detects`: The call reports a failed check on `x` for some fuel (a `checkFail` outcome, whether it comes from an inserted check or from a contract statement already in `g`).

```lean
-- lean/ToyContracts/Crates.lean:103-105
def Detects (fl : Nat → Bool) (s : Site) (res : Resolution) (cs : CallSite) (c : Contract)
    (g : Fn) (x : Nat) : Prop :=
  ∃ n tr k, callRun fl s res cs c g x n = ⟨tr, .checkFail k⟩
```

`CtfeMode`: Compile-time evaluation mode: skip contract statements (run the erasure) or evaluate them.

```lean
-- lean/ToyContracts/Crates.lean:108-111
inductive CtfeMode where
  | skipChecks
  | evalChecks
  deriving DecidableEq, Repr
```

`ctfeRun`: Compile-time evaluation of a (possibly instrumented) function `p`.

```lean
-- lean/ToyContracts/Crates.lean:114-116
def ctfeRun : CtfeMode → Contract → Fn → Nat → Nat → Obs
  | .skipChecks, c, p, x, n => run c (erase p) x n
  | .evalChecks, c, p, x, n => run c p x n
```

`CtfeConst`: Compile-time evaluation in mode `m` of the instrumentation `instr p g` (placement `p`) on `x` produces the constant `r` (a normal return, for some fuel; events are ignored).

```lean
-- lean/ToyContracts/Crates.lean:120-121
def CtfeConst (p : Placement) (m : CtfeMode) (c : Contract) (g : Fn) (x r : Nat) : Prop :=
  ∃ n tr, ctfeRun m c (instr p g) x n = ⟨tr, .ret r⟩
```

`RuntimeValue`: The runtime-checked call with placement `p` (the instrumentation `instr p g`) on `x` returns `r` for some fuel.

```lean
-- lean/ToyContracts/Crates.lean:125-126
def RuntimeValue (p : Placement) (c : Contract) (g : Fn) (x r : Nat) : Prop :=
  ∃ tr, Halts c (instr p g) x ⟨tr, .ret r⟩
```

#### 1.5 Concrete programs and contracts (`lean/ToyContracts/Programs.lean`)

`c1`: `requires x < 100`, `ensures r ≤ x`.

```lean
-- lean/ToyContracts/Programs.lean:10-10
def c1 : Contract := ⟨fun x => decide (x < 100), fun x r => decide (r ≤ x)⟩
```

`cOne`: `requires x = 1`, `ensures r ≤ x` (a single admitted input).

```lean
-- lean/ToyContracts/Programs.lean:13-13
def cOne : Contract := ⟨fun x => x == 1, fun x r => decide (r ≤ x)⟩
```

`cThree`: `requires x = 3`, `ensures r ≤ x` (a single admitted input).

```lean
-- lean/ToyContracts/Programs.lean:16-16
def cThree : Contract := ⟨fun x => x == 3, fun x r => decide (r ≤ x)⟩
```

`gEarly`: Tail expression `x` (after emitting `x`) when `x ≠ 0`; early `return 7` when `x = 0`.

```lean
-- lean/ToyContracts/Programs.lean:19-24
def gEarly : Fn :=
  { prologue := []
    entry := 0
    blocks := [ ⟨[], .branch .arg 1 2⟩,
                ⟨[.emit .arg], .ret .tail .arg⟩,
                ⟨[], .ret .early (.lit 7)⟩ ] }
```

`gTry`: `let y = x - 1` (truncated subtraction); `y?` with error value `9` (taken when `y = 0`, i.e. `x ≤ 1`); tail expression `y`. Written with the source form `tryQ` of `?`.

```lean
-- lean/ToyContracts/Programs.lean:28-32
def gTry : Fn :=
  { prologue := []
    entry := 0
    blocks := [ ⟨[.assign 0 (.sub .arg (.lit 1))], .tryQ (.loc 0) (.lit 9) 1⟩,
                ⟨[], .ret .tail (.loc 0)⟩ ] }
```

`gGood`: Emit `x`, then return `x` as the tail expression.

```lean
-- lean/ToyContracts/Programs.lean:35-36
def gGood : Fn :=
  { prologue := [], entry := 0, blocks := [⟨[.emit .arg], .ret .tail .arg⟩] }
```

`gLoop`: A loop that emits `1` forever.

```lean
-- lean/ToyContracts/Programs.lean:39-40
def gLoop : Fn :=
  { prologue := [], entry := 0, blocks := [⟨[.emit (.lit 1)], .goto 0⟩] }
```

`gPanic`: Emit `x`, then panic.

```lean
-- lean/ToyContracts/Programs.lean:43-44
def gPanic : Fn :=
  { prologue := [], entry := 0, blocks := [⟨[.emit .arg], .panic⟩] }
```

`gStuck`: A function with no blocks: every run that gets past the prologue is `stuck`.

```lean
-- lean/ToyContracts/Programs.lean:47-47
def gStuck : Fn := { prologue := [], entry := 0, blocks := [] }
```

`gInt`: A function as written that already contains an `ensures` check on the constant `5`, then returns `x`.

```lean
-- lean/ToyContracts/Programs.lean:51-52
def gInt : Fn :=
  { prologue := [], entry := 0, blocks := [⟨[.checkEns (.lit 5)], .ret .tail .arg⟩] }
```

`gIntReq`: A function as written that already contains a `requires` check, then returns `x`.

```lean
-- lean/ToyContracts/Programs.lean:55-56
def gIntReq : Fn :=
  { prologue := [], entry := 0, blocks := [⟨[.checkReq], .ret .tail .arg⟩] }
```

`fOut`: A two-block function whose entry jumps to the missing index `3`; block `1` is a `?`. After lowering, index `3` is the fresh `ret .tryErr 5` block of block `1`.

```lean
-- lean/ToyContracts/Programs.lean:60-64
def fOut : Fn :=
  { prologue := []
    entry := 0
    blocks := [ ⟨[], .goto 3⟩,
                ⟨[], .tryQ .arg (.lit 5) 0⟩ ] }
```

`fBadEntry`: A one-block function whose entry is the missing index `1` (its one jump target, `0`, is in range); after lowering, index `1` is the fresh `ret .tryErr 5` block of block `0`.

```lean
-- lean/ToyContracts/Programs.lean:68-69
def fBadEntry : Fn :=
  { prologue := [], entry := 1, blocks := [⟨[], .tryQ .arg (.lit 5) 0⟩] }
```

`cs1`: A non-generic call from crate `0` to a function defined in crate `1`.

```lean
-- lean/ToyContracts/Programs.lean:72-72
def cs1 : CallSite := ⟨0, 1, 0, false⟩
```

`csGen`: A call from crate `0` to a generic function defined in crate `1` and instantiated in the calling crate `0`.

```lean
-- lean/ToyContracts/Programs.lean:76-76
def csGen : CallSite := ⟨0, 1, 0, true⟩
```

`csGen3`: A call from crate `0` to a generic function defined in crate `1` and instantiated in a third crate `2`.

```lean
-- lean/ToyContracts/Programs.lean:80-80
def csGen3 : CallSite := ⟨0, 1, 2, true⟩
```

`flCallerOn`: Flags: crate `0` (the caller) has checks on, every other crate off.

```lean
-- lean/ToyContracts/Programs.lean:83-83
def flCallerOn : Nat → Bool := fun k => k == 0
```

`flDefOn`: Flags: crate `1` (the defining crate) has checks on, every other crate off.

```lean
-- lean/ToyContracts/Programs.lean:86-86
def flDefOn : Nat → Bool := fun k => k == 1
```

`flTwoOn`: Flags: crate `2` has checks on, every other crate off.

```lean
-- lean/ToyContracts/Programs.lean:89-89
def flTwoOn : Nat → Bool := fun k => k == 2
```

`flZeroOneOn`: Flags: crates `0` and `1` have checks on, every other crate off.

```lean
-- lean/ToyContracts/Programs.lean:92-92
def flZeroOneOn : Nat → Bool := fun k => k == 0 || k == 1
```

#### 1.6 Definition examples, positive and negative (`lean/ToyContracts/Examples.lean`)

```lean
-- lean/ToyContracts/Examples.lean:11
theorem halts_gEarly_0 (o : Obs) : Halts c1 gEarly 0 o ↔ o = ⟨[], .ret 7⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:15
theorem halts_gEarly_100 (o : Obs) : Halts c1 gEarly 100 o ↔ o = ⟨[100], .ret 100⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:19
theorem halts_gGood (x : Nat) (o : Obs) : Halts c1 gGood x o ↔ o = ⟨[x], .ret x⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:23-24
theorem run_instr_gEarly_100 (p : Placement) (n : Nat) :
    run c1 (instr p gEarly) 100 n = ⟨[], .checkFail .pre⟩ := by …
```

```lean
-- lean/ToyContracts/Examples.lean:27-28
theorem halts_instr_gEarly_100 (p : Placement) (o : Obs) :
    Halts c1 (instr p gEarly) 100 o ↔ o = ⟨[], .checkFail .pre⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:32-33
theorem halts_instr_allExits_gEarly_0 (o : Obs) :
    Halts c1 (instr .allExits gEarly) 0 o ↔ o = ⟨[], .checkFail .post⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:37-38
theorem halts_instr_tailOnly_gEarly_0 (o : Obs) :
    Halts c1 (instr .tailOnly gEarly) 0 o ↔ o = ⟨[], .ret 7⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:42-43
theorem halts_assumeErase_instr_gEarly_0 (o : Obs) :
    Halts c1 (assumeErase (instr .allExits gEarly)) 0 o ↔ o = ⟨[], .ret 7⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:47-48
theorem halts_instr_allExits_gGood (x : Nat) (hx : x < 100) (o : Obs) :
    Halts c1 (instr .allExits gGood) x o ↔ o = ⟨[x], .ret x⟩ := by …
```

```lean
-- lean/ToyContracts/Examples.lean:57-58
theorem run_gTry_1 (c : Contract) (n : Nat) :
    run c gTry 1 (n + 1) = ⟨[], .ret 9⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:60
theorem halts_gTry_1 (c : Contract) (o : Obs) : Halts c gTry 1 o ↔ o = ⟨[], .ret 9⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:64
theorem halts_lower_gTry_1 (o : Obs) : Halts c1 (lower gTry) 1 o ↔ o = ⟨[], .ret 9⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:68-69
theorem halts_instr_allExits_gTry_1 (c : Contract) (hr : c.req 1 = true) (o : Obs) :
    Halts c (instr .allExits gTry) 1 o ↔ o = ⟨[], .ret 9⟩ := by …
```

```lean
-- lean/ToyContracts/Examples.lean:76-77
theorem halts_instr_allExits_gInt_3 (o : Obs) :
    Halts cThree (instr .allExits gInt) 3 o ↔ o = ⟨[], .checkFail .post⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:81
theorem halts_gInt_3 (o : Obs) : Halts cThree gInt 3 o ↔ o = ⟨[], .checkFail .post⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:85-86
theorem halts_assumeErase_instr_gInt_3 (o : Obs) :
    Halts cThree (assumeErase (instr .allExits gInt)) 3 o ↔ o = ⟨[], .ret 3⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:90
theorem halts_fOut (o : Obs) : Halts c1 fOut 0 o ↔ o = ⟨[], .stuck⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:94
theorem halts_lower_fOut (o : Obs) : Halts c1 (lower fOut) 0 o ↔ o = ⟨[], .ret 5⟩ := …
```

```lean
-- lean/ToyContracts/Examples.lean:98
theorem run_gLoop (x n : Nat) : run c1 gLoop x n = ⟨List.replicate n 1, .fuelOut⟩ := by …
```

`lower_fOut_returns_where_fOut_stuck`: Without `JumpsInRange`, a return of the instrumented lowering need not be a return of the function as written: on `5` under `c1`, `fOut` halts `stuck`, while `instr .allExits (lower fOut)` returns `5`, and `Req 5` and `Ens 5 5` hold.

```lean
-- lean/ToyContracts/Examples.lean:104-107
theorem lower_fOut_returns_where_fOut_stuck :
    ¬ JumpsInRange fOut ∧ Halts c1 fOut 5 ⟨[], .stuck⟩ ∧
    Halts c1 (instr .allExits (lower fOut)) 5 ⟨[], .ret 5⟩ ∧
    c1.req 5 = true ∧ c1.ens 5 5 = true := …
```

`lowered_gEarly`: `Lowered`: admits a function whose exits are all explicit `ret` edges.

```lean
-- lean/ToyContracts/Examples.lean:113
theorem lowered_gEarly : Lowered gEarly := by …
```

`not_lowered_gTry`: `Lowered`: rejects a function still containing the source form of `?`.

```lean
-- lean/ToyContracts/Examples.lean:115
theorem not_lowered_gTry : ¬ Lowered gTry := by …
```

`lowered_lower_gTry`: `lower` produces a lowered function.

```lean
-- lean/ToyContracts/Examples.lean:117
theorem lowered_lower_gTry : Lowered (lower gTry) := by …
```

`jumpsInRange_gEarly`: `JumpsInRange`: admits `gEarly`.

```lean
-- lean/ToyContracts/Examples.lean:120
theorem jumpsInRange_gEarly : JumpsInRange gEarly := by …
```

`not_jumpsInRange_fOut`: `JumpsInRange`: rejects `fOut`, whose entry jumps to the missing index `3`.

```lean
-- lean/ToyContracts/Examples.lean:122
theorem not_jumpsInRange_fOut : ¬ JumpsInRange fOut := by …
```

`not_jumpsInRange_gStuck_and_lower_eq`: `JumpsInRange`: rejects the function with no blocks (its entry is not a block index), although lowering leaves it unchanged.

```lean
-- lean/ToyContracts/Examples.lean:125
theorem not_jumpsInRange_gStuck_and_lower_eq : ¬ JumpsInRange gStuck ∧ lower gStuck = gStuck := …
```

`noChecks_gEarly`: `NoChecks`: admits a function as written without contract statements.

```lean
-- lean/ToyContracts/Examples.lean:129
theorem noChecks_gEarly : NoChecks gEarly := by …
```

`not_noChecks_gInt`: `NoChecks`: rejects a function containing an `ensures` check.

```lean
-- lean/ToyContracts/Examples.lean:131
theorem not_noChecks_gInt : ¬ NoChecks gInt := by …
```

`not_noChecks_instr_gEarly`: `NoChecks`: rejects an instrumented function.

```lean
-- lean/ToyContracts/Examples.lean:133
theorem not_noChecks_instr_gEarly : ¬ NoChecks (instr .allExits gEarly) := by …
```

`selects_allExits_early`: `Placement.selects`: all-exits selects early returns.

```lean
-- lean/ToyContracts/Examples.lean:136
theorem selects_allExits_early : Placement.allExits.selects .early = true := …
```

`not_selects_tailOnly_early_tryErr`: `Placement.selects`: tail-only does not select early returns or `?` error paths.

```lean
-- lean/ToyContracts/Examples.lean:138-139
theorem not_selects_tailOnly_early_tryErr :
    Placement.tailOnly.selects .early = false ∧ Placement.tailOnly.selects .tryErr = false := …
```

`instr_allExits_gEarly_block2`: `instr .allExits` puts an `ensures` check before the early return of `gEarly`.

```lean
-- lean/ToyContracts/Examples.lean:143-144
theorem instr_allExits_gEarly_block2 :
    (instr .allExits gEarly).blocks[2]? = some ⟨[.checkEns (.lit 7)], .ret .early (.lit 7)⟩ := by …
```

`instr_tailOnly_gEarly_block2`: `instr .tailOnly` leaves the early return of `gEarly` unchecked.

```lean
-- lean/ToyContracts/Examples.lean:147-148
theorem instr_tailOnly_gEarly_block2 :
    (instr .tailOnly gEarly).blocks[2]? = some ⟨[], .ret .early (.lit 7)⟩ := by …
```

`instr_allExits_gPanic_blocks`: `instr` puts no `ensures` check on a panic path.

```lean
-- lean/ToyContracts/Examples.lean:150
theorem instr_allExits_gPanic_blocks : (instr .allExits gPanic).blocks = gPanic.blocks := by …
```

`instr_gEarly_prologue`: `instr` puts the `requires` check first in the prologue.

```lean
-- lean/ToyContracts/Examples.lean:153
theorem instr_gEarly_prologue : (instr .allExits gEarly).prologue = [.checkReq] := …
```

`erase_instr_allExits_gEarly`: `erase` undoes instrumentation of a function without contract statements.

```lean
-- lean/ToyContracts/Examples.lean:156
theorem erase_instr_allExits_gEarly : erase (instr .allExits gEarly) = gEarly := by …
```

`erase_gInt_ne`: `erase` also deletes contract statements present in the function as written.

```lean
-- lean/ToyContracts/Examples.lean:158
theorem erase_gInt_ne : erase gInt ≠ gInt := by …
```

`assumeErase_instr_gEarly_prologue`: `assumeErase`: the prologue is exactly the `requires` assumption.

```lean
-- lean/ToyContracts/Examples.lean:161-162
theorem assumeErase_instr_gEarly_prologue :
    (assumeErase (instr .allExits gEarly)).prologue = [.assumeReq] := by …
```

`assumeErase_instr_gEarly_blocks`: `assumeErase`: no `ensures` check remains.

```lean
-- lean/ToyContracts/Examples.lean:164-165
theorem assumeErase_instr_gEarly_blocks :
    (assumeErase (instr .allExits gEarly)).blocks = gEarly.blocks := by …
```

`lower_gTry_blocks`: `lower`: the `?` of `gTry` becomes a branch to the fresh `ret .tryErr 9` block `2`.

```lean
-- lean/ToyContracts/Examples.lean:168-171
theorem lower_gTry_blocks :
    (lower gTry).blocks.take 3 =
      [⟨[.assign 0 (.sub .arg (.lit 1))], .branch (.loc 0) 1 2⟩, ⟨[], .ret .tail (.loc 0)⟩,
       ⟨[], .ret .tryErr (.lit 9)⟩] := by …
```

`lower_gEarly_take`: `lower`: blocks without `?` keep their terminators (here: all of `gEarly`).

```lean
-- lean/ToyContracts/Examples.lean:173
theorem lower_gEarly_take : (lower gEarly).blocks.take 3 = gEarly.blocks := by …
```

`lower_gEarly_ne`: `lower`: blocks are appended even when there is no `?` (three dead `panic` blocks for `gEarly`), so the lowering differs from the function.

```lean
-- lean/ToyContracts/Examples.lean:176
theorem lower_gEarly_ne : lower gEarly ≠ gEarly ∧ (lower gEarly).blocks.length = 6 := by …
```

`run_gEarly_0_eq`: `run`: `gEarly` on `0` takes the early return `7`.

```lean
-- lean/ToyContracts/Examples.lean:181
theorem run_gEarly_0_eq : run c1 gEarly 0 2 = ⟨[], .ret 7⟩ := …
```

`run_fOut_eq`: `run`: a jump to a missing block is `stuck`.

```lean
-- lean/ToyContracts/Examples.lean:183
theorem run_fOut_eq : run c1 fOut 0 2 = ⟨[], .stuck⟩ := …
```

`run_gPanic_eq`: `run`: a panic ends the run with outcome `panic`, not a return.

```lean
-- lean/ToyContracts/Examples.lean:185
theorem run_gPanic_eq : run c1 gPanic 4 1 = ⟨[4], .panic⟩ := …
```

`halts_gGood_5`: `Halts`: `gGood` halts on `5` with events `[5]` and return `5`.

```lean
-- lean/ToyContracts/Examples.lean:188
theorem halts_gGood_5 : Halts c1 gGood 5 ⟨[5], .ret 5⟩ := …
```

`not_halts_fuelOut`: `Halts`: excludes fuel exhaustion.

```lean
-- lean/ToyContracts/Examples.lean:190
theorem not_halts_fuelOut : ¬ Halts c1 gGood 5 ⟨[], .fuelOut⟩ := …
```

`not_halts_gLoop`: `Halts`: the emitting loop has no halting observation.

```lean
-- lean/ToyContracts/Examples.lean:192
theorem not_halts_gLoop (x : Nat) (o : Obs) : ¬ Halts c1 gLoop x o := by …
```

`runEqAt_erase_instr_gGood_5`: `RunEqAt`: erasure and instrumentation of `gGood` agree at `5` at every fuel.

```lean
-- lean/ToyContracts/Examples.lean:198-199
theorem runEqAt_erase_instr_gGood_5 :
    RunEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 5 := by …
```

`not_runEqAt_erase_instr_gGood_100`: `RunEqAt`: they differ at `100`, where `Req` fails.

```lean
-- lean/ToyContracts/Examples.lean:202-203
theorem not_runEqAt_erase_instr_gGood_100 :
    ¬ RunEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 100 := by …
```

`not_haltsEqAt_gGood_gEarly_0`: `HaltsEqAt`: `gGood` and `gEarly` differ at `0`.

```lean
-- lean/ToyContracts/Examples.lean:206
theorem not_haltsEqAt_gGood_gEarly_0 : ¬ HaltsEqAt c1 gGood gEarly 0 := by …
```

`haltsEqAt_not_runEqAt_lower_gTry_1`: `HaltsEqAt` without `RunEqAt`: `lower gTry` and `gTry` have the same halting observations on `1` but differ at fuel `1` (the lowered `?` error exit takes one more block execution).

```lean
-- lean/ToyContracts/Examples.lean:213-214
theorem haltsEqAt_not_runEqAt_lower_gTry_1 :
    HaltsEqAt c1 (lower gTry) gTry 1 ∧ ¬ RunEqAt c1 (lower gTry) gTry 1 := by …
```

`wrapObs_keep`: `wrapObs`: keeps a return satisfying `Ens`.

```lean
-- lean/ToyContracts/Examples.lean:222
theorem wrapObs_keep : wrapObs c1 5 ⟨[5], .ret 5⟩ = ⟨[5], .ret 5⟩ := by …
```

`wrapObs_fail`: `wrapObs`: turns a return violating `Ens` into an `ensures` failure with the same events.

```lean
-- lean/ToyContracts/Examples.lean:224
theorem wrapObs_fail : wrapObs c1 0 ⟨[3], .ret 7⟩ = ⟨[3], .checkFail .post⟩ := by …
```

`wrapObs_panic`: `wrapObs`: leaves a panic unchanged.

```lean
-- lean/ToyContracts/Examples.lean:226
theorem wrapObs_panic : wrapObs c1 0 ⟨[0], .panic⟩ = ⟨[0], .panic⟩ := by …
```

`instrObs_req_false`: `instrObs`: a `requires` failure with no events when `Req` fails.

```lean
-- lean/ToyContracts/Examples.lean:228
theorem instrObs_req_false : instrObs c1 100 ⟨[100], .ret 100⟩ = ⟨[], .checkFail .pre⟩ := by …
```

`ensOnReturnsAt_gGood`: `EnsOnReturnsAt`: holds for `gGood` on every `x`.

```lean
-- lean/ToyContracts/Examples.lean:234
theorem ensOnReturnsAt_gGood (x : Nat) : EnsOnReturnsAt c1 gGood x := by …
```

`not_ensOnReturnsAt_gEarly_0`: `EnsOnReturnsAt`: fails for `gEarly` on `0` (early return `7 > 0`).

```lean
-- lean/ToyContracts/Examples.lean:240
theorem not_ensOnReturnsAt_gEarly_0 : ¬ EnsOnReturnsAt c1 gEarly 0 := by …
```

`staticObligation_gGood`: `StaticObligation`: holds for `gGood`.

```lean
-- lean/ToyContracts/Examples.lean:245
theorem staticObligation_gGood : StaticObligation c1 gGood := …
```

`not_staticObligation_gEarly`: `StaticObligation`: fails for `gEarly`.

```lean
-- lean/ToyContracts/Examples.lean:247
theorem not_staticObligation_gEarly : ¬ StaticObligation c1 gEarly := …
```

`staticObligationAt_gEarly_100`: `StaticObligationAt`: holds vacuously where `Req` fails.

```lean
-- lean/ToyContracts/Examples.lean:250
theorem staticObligationAt_gEarly_100 : StaticObligationAt c1 gEarly 100 := by …
```

`staticObligationAt_gGood_5`: `StaticObligationAt`: holds non-vacuously for `gGood` at `5`, where `Req` holds.

```lean
-- lean/ToyContracts/Examples.lean:253
theorem staticObligationAt_gGood_5 : c1.req 5 = true ∧ StaticObligationAt c1 gGood 5 := …
```

`not_staticObligationAt_gEarly_0`: `StaticObligationAt`: fails for `gEarly` at `0`.

```lean
-- lean/ToyContracts/Examples.lean:256
theorem not_staticObligationAt_gEarly_0 : ¬ StaticObligationAt c1 gEarly 0 := …
```

`ubRefinesAt_instr_assumeErase_gGood_5`: `UBRefinesAt`: the checked `gGood` refines its assume-erasure at `5`.

```lean
-- lean/ToyContracts/Examples.lean:260-261
theorem ubRefinesAt_instr_assumeErase_gGood_5 :
    UBRefinesAt c1 (instr .allExits gGood) (assumeErase (instr .allExits gGood)) 5 := …
```

`not_ubRefinesAt_instr_assumeErase_gEarly_0`: `UBRefinesAt`: the checked `gEarly` does not refine its assume-erasure at `0` (it ends with an `ensures` failure, which the assume-erasure neither produces nor licenses by UB).

```lean
-- lean/ToyContracts/Examples.lean:266-267
theorem not_ubRefinesAt_instr_assumeErase_gEarly_0 :
    ¬ UBRefinesAt c1 (instr .allExits gEarly) (assumeErase (instr .allExits gEarly)) 0 := by …
```

`ubRefinesAt_gLoop_gGood_5`: `UBRefinesAt` compares halting runs of the target only: the non-halting `gLoop` refines `gGood` at `5`, although `gGood` halts there with a return and no UB.

```lean
-- lean/ToyContracts/Examples.lean:274-275
theorem ubRefinesAt_gLoop_gGood_5 :
    UBRefinesAt c1 gLoop gGood 5 ∧ Halts c1 gGood 5 ⟨[5], .ret 5⟩ ∧ (∀ o, ¬ Halts c1 gLoop 5 o) := …
```

`holder_cs1`: `holder`: callee-side checks are held by the defining crate, caller-side by the caller.

```lean
-- lean/ToyContracts/Examples.lean:281
theorem holder_cs1 : holder .calleeSide cs1 = 1 ∧ holder .callerSide cs1 = 0 := …
```

`governingCrate_csGen_atInstantiation`: `governingCrate`: at instantiation, a generic callee's callee-side check is governed by the instantiating crate (here the calling crate `0`).

```lean
-- lean/ToyContracts/Examples.lean:284-285
theorem governingCrate_csGen_atInstantiation :
    governingCrate .calleeSide .atInstantiation csGen = 0 := …
```

`governingCrate_cs1_atInstantiation`: `governingCrate`: at instantiation, a non-generic callee's check is still governed by the defining crate.

```lean
-- lean/ToyContracts/Examples.lean:288-289
theorem governingCrate_cs1_atInstantiation :
    governingCrate .calleeSide .atInstantiation cs1 = 1 := …
```

`governingCrate_csGen3_atInstantiation`: `governingCrate`: for a generic callee instantiated in a third crate, resolution at instantiation selects that crate, which is neither the calling nor the defining crate.

```lean
-- lean/ToyContracts/Examples.lean:292-295
theorem governingCrate_csGen3_atInstantiation :
    governingCrate .calleeSide .atInstantiation csGen3 = 2 ∧
    governingCrate .calleeSide .atInstantiation csGen3 ≠ csGen3.callerCrate ∧
    governingCrate .calleeSide .atInstantiation csGen3 ≠ csGen3.defCrate := by …
```

`callRun_gEarly_0_examples`: `callRun`: with the caller's flag on, caller-side placement turns `gEarly`'s early return `7` on `0` into an `ensures` failure, while callee-side placement (defining crate's flag off) returns `7`.

```lean
-- lean/ToyContracts/Examples.lean:300-302
theorem callRun_gEarly_0_examples :
    callRun flCallerOn .callerSide .atDefinition cs1 c1 gEarly 0 2 = ⟨[], .checkFail .post⟩ ∧
    callRun flCallerOn .calleeSide .atDefinition cs1 c1 gEarly 0 2 = ⟨[], .ret 7⟩ := …
```

`violationAt_gEarly_0`: `ViolationAt`: an `ensures` violation (`gEarly` on `0`).

```lean
-- lean/ToyContracts/Examples.lean:305
theorem violationAt_gEarly_0 : ViolationAt c1 gEarly 0 := …
```

`violationAt_gEarly_100`: `ViolationAt`: a `requires` violation (`gEarly` on `100`).

```lean
-- lean/ToyContracts/Examples.lean:308
theorem violationAt_gEarly_100 : ViolationAt c1 gEarly 100 := …
```

`not_violationAt_gGood_5`: `ViolationAt`: no violation for `gGood` on `5`.

```lean
-- lean/ToyContracts/Examples.lean:310
theorem not_violationAt_gGood_5 : ¬ ViolationAt c1 gGood 5 := by …
```

`detects_callerOn_callerSide_gEarly_0`: `Detects`: the caller-side check (caller flag on) reports `gEarly`'s violation on `0`.

```lean
-- lean/ToyContracts/Examples.lean:316-317
theorem detects_callerOn_callerSide_gEarly_0 :
    Detects flCallerOn .callerSide .atDefinition cs1 c1 gEarly 0 := …
```

`not_detects_gGood_5`: `Detects`: nothing is reported for `gGood` on `5` even with every flag on.

```lean
-- lean/ToyContracts/Examples.lean:319-320
theorem not_detects_gGood_5 :
    ¬ Detects (fun _ => true) .calleeSide .atDefinition cs1 c1 gGood 5 := by …
```

`not_detects_calleeSide_off_gEarly_0`: With the governing crate's flag off, callee-side placement never reports `gEarly`'s violation on `0`.

```lean
-- lean/ToyContracts/Examples.lean:328-330
theorem not_detects_calleeSide_off_gEarly_0 (fl : Nat → Bool) (res : Resolution) (cs : CallSite)
    (h : fl (governingCrate .calleeSide res cs) = false) :
    ¬ Detects fl .calleeSide res cs c1 gEarly 0 := by …
```

`detects_csGen3_follows_instCrate`: `Detects` for a generic callee instantiated in a third crate, under callee-side placement with resolution at instantiation: `gEarly`'s violation on `0` is reported when the instantiating crate's flag alone is on, and not reported when the calling and defining crates' flags are on and the instantiating crate's flag is off.

```lean
-- lean/ToyContracts/Examples.lean:343-346
theorem detects_csGen3_follows_instCrate :
    Detects flTwoOn .calleeSide .atInstantiation csGen3 c1 gEarly 0 ∧
    flZeroOneOn csGen3.callerCrate = true ∧ flZeroOneOn csGen3.defCrate = true ∧
    ¬ Detects flZeroOneOn .calleeSide .atInstantiation csGen3 c1 gEarly 0 := …
```

`ctfeRun_gEarly_100_examples`: `ctfeRun`: on `100` (where `Req` fails), check-skipping evaluation of the instrumented `gEarly` returns `100` and check-evaluating evaluation fails the `requires` check.

```lean
-- lean/ToyContracts/Examples.lean:351-353
theorem ctfeRun_gEarly_100_examples :
    ctfeRun .skipChecks c1 (instr .allExits gEarly) 100 2 = ⟨[100], .ret 100⟩ ∧
    ctfeRun .evalChecks c1 (instr .allExits gEarly) 100 2 = ⟨[], .checkFail .pre⟩ := …
```

`ctfeConst_skip_gEarly_100`: `CtfeConst`: check-skipping compile-time evaluation of `gEarly` on `100` gives `100`.

```lean
-- lean/ToyContracts/Examples.lean:356
theorem ctfeConst_skip_gEarly_100 : CtfeConst .allExits .skipChecks c1 gEarly 100 100 := …
```

`not_ctfeConst_eval_gEarly_100`: `CtfeConst`: check-evaluating compile-time evaluation gives no constant there.

```lean
-- lean/ToyContracts/Examples.lean:359-360
theorem not_ctfeConst_eval_gEarly_100 (r : Nat) :
    ¬ CtfeConst .allExits .evalChecks c1 gEarly 100 r := by …
```

`runtimeValue_gGood_5`: `RuntimeValue`: the checked `gGood` returns `5` on `5`.

```lean
-- lean/ToyContracts/Examples.lean:365
theorem runtimeValue_gGood_5 : RuntimeValue .allExits c1 gGood 5 5 := …
```

`not_runtimeValue_gEarly_100`: `RuntimeValue`: the checked `gEarly` returns nothing on `100`.

```lean
-- lean/ToyContracts/Examples.lean:368
theorem not_runtimeValue_gEarly_100 (r : Nat) : ¬ RuntimeValue .allExits c1 gEarly 100 r := by …
```

`runtimeValue_gEarly_0_placement`: `RuntimeValue` depends on the placement: the tail-only checked `gEarly` returns `7` on `0`, the all-exits checked `gEarly` returns no value there.

```lean
-- lean/ToyContracts/Examples.lean:374-375
theorem runtimeValue_gEarly_0_placement (r : Nat) :
    RuntimeValue .tailOnly c1 gEarly 0 7 ∧ ¬ RuntimeValue .allExits c1 gEarly 0 r := by …
```

### 2. Cards

Each card quotes its theorem (proof elided); explicit forms are Lean terms that elaborate in the theorem's context and are definitionally equal to the quoted conclusion; prose renderings are labelled as such.

#### R1. `run_instr_allExits_eq_instrObs_of_lowered` (theorem)

```lean
-- lean/ToyContracts/Results.lean:15-17
theorem run_instr_allExits_eq_instrObs_of_lowered (c : Contract) (g : Fn) (hg : Lowered g)
    (x n : Nat) :
    run c (instr .allExits g) x n = instrObs c x (run c g x n) := by …
```

Unfolded (prose):

```text
`instrObs c x o` is `if c.req x then wrapObs c x o else ⟨[], .checkFail .pre⟩`, and `wrapObs c x` maps `⟨tr, .ret r⟩` to itself if `c.ens x r` and to `⟨tr, .checkFail .post⟩` otherwise, leaving every other observation unchanged.
```

- **Plain claim:** For every contract `c` and every function `g` with `Lowered g` (no block of `g`, reachable or not, ends in the source form `tryQ` of `?`), and for every argument `x` and every fuel `n`: `run c (instr .allExits g) x n = instrObs c x (run c g x n)`. That is, if `Req x` fails, the instrumented run ends with a `requires` failure and no events; otherwise it is the run of `g`, except that a normal return of a value `r` with `Ens x r` false becomes an `ensures` failure with the same events; panics, failed checks, UB, stuck runs and fuel exhaustion are unchanged.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: run-time checking of preconditions at entry and postconditions at every normal return, and the effect of disabling checks, are classical (Ada 2012 RM 6.1.1, JML, Eiffel); proofs for other formalisms exist on paper (Ly et al. 2024); no mechanized statement for a CFG with several return edges was found.
- **Hypothesis ledger:**
  - `hg : Lowered g`: no block of `g`, reachable or not, ends in the source form `tryQ` of `?`; such a terminator returns without a `ret` edge, so no `ensures` check is inserted on it. **tight** — counterexample `cex_instr_before_lower_misses_try`; witness class: a two-block function (`gTry`) with exactly one `?`, at input `1`, fuel `1`, contract `c1`.
- **Depth:** shallow. Induction on fuel generalised over block, store and events (`runFrom_instr_allExits_eq_wrapObs`); the inserted check is the last statement before `ret`, so it sees the store in which the returned operand is evaluated, and a stop inside a block is a failed check or UB, which `wrapObs` leaves unchanged.
- **Non-vacuity witness:** `gEarly` (a tail return and an early return) is lowered. (`nonvacuity_run_instr_allExits`)
- **Non-claims:**
  - Lowering precedes instrumentation in this theorem: there is a function still containing `tryQ` (`gTry`, at input `1` and fuel `1` under `c1`) for which the equation fails (`cex_instr_before_lower_misses_try`). Tightness does not mean the equation fails for every unlowered function; for example it is expected to hold when every `tryQ` block is unreachable (not proved here).
  - Body outlining is not modelled: `Fn` has no calls inside functions, so checking `Ens` once at a single wrapper call site (in the style of `instrObs`, or of the wrapper methods of the JML runtime assertion checker cited under prior art), or routing every exit through one shared return block, is not a transformation of this toy. The theorem says that per-edge insertion on a lowered function has the same observations as that wrapper; it says nothing about the cost or code size of either.
  - Panic paths: the instrumented run panics with the same events as `g` and `Ens` is not evaluated; a panic ends the run with outcome `panic`, there is no exceptional postcondition, and unwinding cleanup is not modelled (see the corpus package on panic safety and unwinding cited under prior art). The `?` error path is a normal return of a value (outcome `ret`) and so is subject to `Ens`; this models value-based error propagation, not exception propagation, which Ada 2012 6.1.1(35/3) and JML §9.9.3 exempt from normal postconditions.
  - Contract clauses are total Boolean functions of the immutable argument (and of the returned value); evaluating a clause cannot panic, diverge, have side effects or read mutable state. Mutable parameters and clauses over memory or over entry-time (`old`) values are not modelled.
  - A failed check is the distinct outcome `checkFail k`; whether a real failed check panics, unwinds or aborts is not modelled, and a failed check is never undefined behaviour in the toy.
  - `Lowered g` inspects every block of `g`, reachable or not; the natural weakening that restricts it to blocks reachable from the entry is not established here.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012 (Ada 2012), §6.1.1 'Preconditions and Postconditions', paragraphs 31/3–36/3 (online edition http://www.ada-auth.org/standards/12rm/html/RM-6-1-1.html, accessed 2026-11-21). 6.1.1(35/3): 'Upon successful return from a call of the subprogram or entry, prior to copying back any by-copy in out or out parameters, the postcondition check is performed.' 6.1.1(36/3): a failed check raises the exception at the point of the call. Checks on every successful return correspond to the all-exits policy; the paragraph imposes no check on exception propagation.
  - G. T. Leavens et al., JML Reference Manual (draft), HTML edition generated 2013-05-31, §9.9.3 'Ensures Clauses' (https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_9.html, accessed 2026-11-21): 'An ensures clause specifies a normal postcondition, i.e., a property that is guaranteed to hold at the end of the method (or constructor) invocation in the case that this method (or constructor) invocation returns without throwing an exception.'
  - Y. Cheon and G. T. Leavens, 'A Runtime Assertion Checker for the Java Modeling Language (JML)', in H. R. Arabnia and Y. Mun (eds.), Proceedings of the International Conference on Software Engineering Research and Practice (SERP '02), Las Vegas, CSREA Press, June 2002, pp. 322–328; technical-report version Iowa State University TR #02-05a (March 2002, revised April 2002), http://www.cs.ucf.edu/~leavens/tech-reports/ISU/TR02-05/TR.pdf, accessed 2026-11-21: 'The original method becomes a private method with a new name; it is replaced by a wrapper method that is automatically generated. The wrapper method delegates client method calls to the original method with appropriate assertion checks.' A wrapper of this kind checks `Ens` once at the return of the call (the toy's `instrObs`) rather than on each return edge of the body.
  - B. Meyer, Object-Oriented Software Construction, 2nd edition, Prentice Hall, 1997, ISBN 0-13-629155-4, chapter 11 'Design by Contract: building reliable software' (p. 331 in the book's table of contents, https://archive.eiffel.com/doc/manuals/technology/oosc/ACROBAT/oosc-tab.pdf, accessed 2026-11-21); cited at chapter level for the notions of precondition and postcondition.
  - Corpus package panic-safety-unwinding-through-broken-invariants-leak-amplification-and-safe-forget (google/zerocopy branch reference at commit 95e95c2fbada69bc95437324bf4462759bd738a4): unwinding and panic safety in a toy model; cited for unwinding exits, not repeated.
- **Design question:** Where should `ensures` checks be placed so that every exit (tail expression, early `return`, `?`) is covered?

#### R2. `req_and_ens_of_halts_ret_instr_allExits_lower` (theorem)

```lean
-- lean/ToyContracts/Results.lean:28-30
theorem req_and_ens_of_halts_ret_instr_allExits_lower (c : Contract) (f : Fn) (x : Nat)
    (tr : List Nat) (r : Nat) (h : Halts c (instr .allExits (lower f)) x ⟨tr, .ret r⟩) :
    c.req x = true ∧ c.ens x r = true := by …
```

Unfolded (prose):

```text
`Halts c p x o` means `o.outcome ≠ .fuelOut ∧ ∃ n, run c p x n = o`; `lower f` replaces every `tryQ o e b` in block `i` by `branch o b (n + i)` and appends one block per original block, the block for a `?` being `ret .tryErr e`.
```

- **Plain claim:** For every contract `c`, every function `f` as written (no hypothesis on `f`: neither `Lowered f` nor `JumpsInRange f` is assumed), every argument `x`, event list `tr` and value `r`: if the all-exits instrumentation of the lowering, `instr .allExits (lower f)`, halts on `x` with events `tr` and a normal return of `r`, then `Req x` and `Ens x r` both hold.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: run-time checking of preconditions at entry and postconditions at every normal return, and the effect of disabling checks, are classical (Ada 2012 RM 6.1.1, JML, Eiffel); proofs for other formalisms exist on paper (Ly et al. 2024); no mechanized statement for a CFG with several return edges was found.
- **Hypothesis ledger:**
  - `h : Halts c (instr .allExits (lower f)) x ⟨tr, .ret r⟩`: the premise: a normal return of the instrumented lowering. **tight** — counterexample `cex_req_and_ens_premise`; witness class: a lowered three-block function (`gEarly`) at input `0` and value `7` under `c1`.
- **Depth:** shallow. From `run_instr_allExits_eq_instrObs_of_lowered` applied to `lower f`, which is lowered for every `f` (`lowered_lower`), and `instrObs_eq_ret`.
- **Non-vacuity witness:** The premise holds for `gTry` on `5` (the instrumented lowering returns `4`). (`nonvacuity_req_and_ens_lower`)
- **Non-claims:**
  - A normal return of `instr .allExits (lower f)` need not be a normal return of `f`: without `JumpsInRange f`, `lower f` can return where `f` is `stuck` (`lower_fOut_returns_where_fOut_stuck`: on `5` under `c1`, `fOut` halts `stuck` while `instr .allExits (lower fOut)` returns `5`, and `Req 5` and `Ens 5 5` hold). Correspondence of the halting observations of `lower f` and `f` is `halts_lower_iff_of_jumpsInRange`, which assumes `JumpsInRange f`.
  - The theorem concerns normal returns; it does not say that every violation is reported (a run may diverge, panic or get stuck instead).
  - Lowering is applied before instrumentation; instrumenting `gTry` without lowering returns `9` on `1` under `c1` although `Ens 1 9` fails (`cex_instr_before_lower_misses_try`).
  - Contract clauses are total Boolean functions of the immutable argument (and of the returned value); evaluating a clause cannot panic, diverge, have side effects or read mutable state. Mutable parameters and clauses over memory or over entry-time (`old`) values are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012 (Ada 2012), §6.1.1 'Preconditions and Postconditions', paragraphs 31/3–36/3 (online edition http://www.ada-auth.org/standards/12rm/html/RM-6-1-1.html, accessed 2026-11-21). 6.1.1(35/3): 'Upon successful return from a call of the subprogram or entry, prior to copying back any by-copy in out or out parameters, the postcondition check is performed.' 6.1.1(36/3): a failed check raises the exception at the point of the call. Checks on every successful return correspond to the all-exits policy; the paragraph imposes no check on exception propagation.
  - G. T. Leavens et al., JML Reference Manual (draft), HTML edition generated 2013-05-31, §9.9.3 'Ensures Clauses' (https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_9.html, accessed 2026-11-21): 'An ensures clause specifies a normal postcondition, i.e., a property that is guaranteed to hold at the end of the method (or constructor) invocation in the case that this method (or constructor) invocation returns without throwing an exception.'
  - D. Ly, N. Kosmatov, F. Loulergue and J. Signoles, 'Sound Runtime Assertion Checking for Memory Properties via Program Transformation', Formal Aspects of Computing 36(1), Article 4, 2024, DOI 10.1145/3605951 (author version https://hal.science/hal-04065774/file/main.pdf, accessed 2026-11-21): for an E-ACSL-style instrumentation of a C-like language it proves semantic preservation while no annotation is violated (its Theorem 5.7) and soundness of the runtime assertion checker (its Corollary 5.10), with paper proofs ('A machine-checked Coq proof of these results is left as future work').
- **Design question:** Is a value returned by the all-exits instrumented lowering guaranteed to satisfy the contract?

#### R4. `halts_lower_iff_of_jumpsInRange` (theorem)

```lean
-- lean/ToyContracts/Results.lean:38-39
theorem halts_lower_iff_of_jumpsInRange (c : Contract) (f : Fn) (hf : JumpsInRange f) (x : Nat)
    (o : Obs) : Halts c (lower f) x o ↔ Halts c f x o := by …
```

Explicit form, with `Halts` unfolded:

```lean
(o.outcome ≠ .fuelOut ∧ ∃ n, run c (lower f) x n = o) ↔
  (o.outcome ≠ .fuelOut ∧ ∃ n, run c f x n = o)
```

- **Plain claim:** For every contract `c`, every function `f` with `JumpsInRange f` (the entry and every jump target of every block, reachable or not, are block indices of `f`; a function with no blocks never satisfies it), every argument `x` and every observation `o`: `lower f` halts on `x` with `o` iff `f` halts on `x` with `o`.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: correctness of lowering `?` to an explicit return edge is folklore; stated here for the toy CFG.
- **Hypothesis ledger:**
  - `hf : JumpsInRange f`: lowering appends fresh blocks at indices `n + i` (`n` the number of blocks); a jump of `f` to such an index, or an entry at such an index, is `stuck` in `f` but reaches a fresh block in `lower f`. **tight** — counterexample `cex_lower_jumpsInRange`, `cex_lower_entry_out_of_range`; witness class: a two-block function (`fOut`) whose entry block jumps to index `3`; and a one-block function (`fBadEntry`) whose entry index `1` is out of range while its one jump target is in range.
- **Depth:** substantive. Two simulations by fuel induction from in-range blocks: a halting run of `f` at fuel `n` is a halting run of `lower f` at fuel `n + 1` (one extra block execution when the run ends at a `?` error exit; `runFrom_lower_of_fin`), and a halting run of `lower f` at fuel `n` is a halting run of `f` at the same fuel `n` (`runFrom_of_lower_fin`); index lemmas for `mapIdx` and the appended blocks (`lower_blocks_lt`, `lower_blocks_add`).
- **Non-vacuity witness:** `gTry` satisfies `JumpsInRange`. (`nonvacuity_halts_lower`)
- **Non-claims:**
  - Halting observations are compared: fuel-exact runs differ (a run that ends at a lowered `?` error exit takes one more block execution; `haltsEqAt_not_runEqAt_lower_gTry_1`), and the events of runs that exhaust their fuel are not compared.
  - The natural weakening of `JumpsInRange f` to 'no reachable jump out of range' is not established.
  - Degenerate edge: a function with no blocks fails `JumpsInRange` although `lower` leaves it unchanged (`not_jumpsInRange_gStuck_and_lower_eq`), so the theorem does not cover it.
  - Lowering appends one block per original block, so `lower f` differs from `f` whenever `f` has a block, even without `?` (`lower_gEarly_ne`); the theorem is about halting observations, not syntax.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - No specific prior statement found; lowering `?` to an explicit early return is folklore.
- **Design question:** Can instrumentation be defined on lowered functions without changing the halting behaviour of the function as written?

#### R5. `cex_tailOnly_misses_early_return` (counterexample)

```lean
-- lean/ToyContracts/Counterexamples.lean:30-33
theorem cex_tailOnly_misses_early_return :
    Lowered gEarly ∧ c1.req 0 = true ∧ Halts c1 gEarly 0 ⟨[], .ret 7⟩ ∧ c1.ens 0 7 = false ∧
    Halts c1 (instr .tailOnly gEarly) 0 ⟨[], .ret 7⟩ ∧
    Halts c1 (instr .allExits gEarly) 0 ⟨[], .checkFail .post⟩ := …
```

- **Plain claim:** There is a lowered function, `gEarly`, and an input, `0`, satisfying `Req` under `c1` (`requires x < 100`, `ensures r ≤ x`), such that: `gEarly` halts on `0` with no events and a normal return of `7` (its run takes the edge `ret .early (.lit 7)` of block `2`; the outcome `ret 7` itself records no provenance), `Ens 0 7` fails, the tail-only instrumentation `instr .tailOnly gEarly` halts with no events and a normal return of `7`, and the all-exits instrumentation `instr .allExits gEarly` halts with no events and an `ensures` failure.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: folklore (a check attached to the tail expression misses other exits); made precise here with a concrete toy instance.
- **Hypothesis ledger:**
  - (no hypotheses)
- **Depth:** definitional. Evaluation of concrete runs.
- **Non-vacuity witness:** the stated instance is itself the witness.
- **Non-claims:**
  - One concrete instance; it is not a statement about every function, input or flag assignment.
  - It does not say that tail-only placement misses a violation for functions whose every return edge is the tail edge (not proved here).
  - Checking the returned value once at a wrapper call site (`instrObs`), or routing every exit through one return block that carries the tail edge, would also catch this return (not modelled as a transformation here).
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012 (Ada 2012), §6.1.1 'Preconditions and Postconditions', paragraphs 31/3–36/3 (online edition http://www.ada-auth.org/standards/12rm/html/RM-6-1-1.html, accessed 2026-11-21). 6.1.1(35/3): 'Upon successful return from a call of the subprogram or entry, prior to copying back any by-copy in out or out parameters, the postcondition check is performed.' 6.1.1(36/3): a failed check raises the exception at the point of the call. Checks on every successful return correspond to the all-exits policy; the paragraph imposes no check on exception propagation.
  - G. T. Leavens et al., JML Reference Manual (draft), HTML edition generated 2013-05-31, §9.9.3 'Ensures Clauses' (https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_9.html, accessed 2026-11-21): 'An ensures clause specifies a normal postcondition, i.e., a property that is guaranteed to hold at the end of the method (or constructor) invocation in the case that this method (or constructor) invocation returns without throwing an exception.'
- **Design question:** Where should `ensures` checks be placed so that every exit (tail expression, early `return`, `?`) is covered?

#### R6. `cex_tailOnly_misses_try_error_after_lowering` (counterexample)

```lean
-- lean/ToyContracts/Counterexamples.lean:41-44
theorem cex_tailOnly_misses_try_error_after_lowering :
    c1.req 1 = true ∧ Halts c1 gTry 1 ⟨[], .ret 9⟩ ∧ c1.ens 1 9 = false ∧ Lowered (lower gTry) ∧
    Halts c1 (instr .tailOnly (lower gTry)) 1 ⟨[], .ret 9⟩ ∧
    Halts c1 (instr .allExits (lower gTry)) 1 ⟨[], .checkFail .post⟩ := …
```

- **Plain claim:** There is a function with a `?`, `gTry` (`let y = x - 1` with truncated subtraction, then `y?` with error value `9`, then tail `y`), and an input, `1`, satisfying `Req` under `c1`, such that: `gTry` halts on `1` with no events and a normal return of `9` (the value of the `?` error path, taken because `1 - 1 = 0`), `Ens 1 9` fails, `lower gTry` is lowered, the tail-only instrumentation of `lower gTry` halts with no events and a normal return of `9`, and the all-exits instrumentation of `lower gTry` halts with no events and an `ensures` failure.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: folklore (a check attached to the tail expression misses other exits); made precise here with a concrete toy instance.
- **Hypothesis ledger:**
  - (no hypotheses)
- **Depth:** definitional. Evaluation of concrete runs.
- **Non-vacuity witness:** the stated instance is itself the witness.
- **Non-claims:**
  - One concrete instance; it is not a statement about every function, input or flag assignment.
  - Lowering does not make tail-only placement complete in this instance; whether some other lowering (for example one that routes every exit through the tail edge) would, is not examined.
  - The `?` error path is a normal return of a value here (value-based error propagation), unlike an exception, which Ada 2012 6.1.1(35/3) and JML §9.9.3 exempt from normal postconditions.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012 (Ada 2012), §6.1.1 'Preconditions and Postconditions', paragraphs 31/3–36/3 (online edition http://www.ada-auth.org/standards/12rm/html/RM-6-1-1.html, accessed 2026-11-21). 6.1.1(35/3): 'Upon successful return from a call of the subprogram or entry, prior to copying back any by-copy in out or out parameters, the postcondition check is performed.' 6.1.1(36/3): a failed check raises the exception at the point of the call. Checks on every successful return correspond to the all-exits policy; the paragraph imposes no check on exception propagation.
  - G. T. Leavens et al., JML Reference Manual (draft), HTML edition generated 2013-05-31, §9.9.3 'Ensures Clauses' (https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_9.html, accessed 2026-11-21): 'An ensures clause specifies a normal postcondition, i.e., a property that is guaranteed to hold at the end of the method (or constructor) invocation in the case that this method (or constructor) invocation returns without throwing an exception.'
  - No specific prior statement found; lowering `?` to an explicit early return is folklore.
- **Design question:** Where should `ensures` checks be placed so that every exit (tail expression, early `return`, `?`) is covered?

#### R7. `cex_instr_before_lower_misses_try` (counterexample)

```lean
-- lean/ToyContracts/Counterexamples.lean:52-57
theorem cex_instr_before_lower_misses_try :
    ¬ Lowered gTry ∧
    run c1 (instr .allExits gTry) 1 1 = ⟨[], .ret 9⟩ ∧
    instrObs c1 1 (run c1 gTry 1 1) = ⟨[], .checkFail .post⟩ ∧
    run c1 (instr .allExits gTry) 1 1 ≠ instrObs c1 1 (run c1 gTry 1 1) ∧
    Halts c1 (instr .allExits gTry) 1 ⟨[], .ret 9⟩ ∧ c1.ens 1 9 = false := …
```

- **Plain claim:** There is a function that is not lowered, `gTry`, such that at input `1` and fuel `1` under `c1` the all-exits instrumentation `instr .allExits gTry` gives no events and a normal return of `9`, while the contract wrapper `instrObs c1 1 (run c1 gTry 1 1)` gives no events and an `ensures` failure, so the equation of `run_instr_allExits_eq_instrObs_of_lowered` fails without `Lowered`; moreover the instrumented `gTry` halts on `1` with no events and a normal return of `9`, and `Ens 1 9` fails.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: folklore (instrumentation keyed to return statements misses implicit exits); made precise here with a concrete toy instance.
- **Hypothesis ledger:**
  - (no hypotheses)
- **Depth:** definitional. Evaluation of concrete runs.
- **Non-vacuity witness:** the stated instance is itself the witness.
- **Non-claims:**
  - One concrete instance; it is not a statement about every function, input or flag assignment.
  - Instrumenting the source form `tryQ` directly (adding a check on its error path), or checking at a wrapper call site, would also avoid this miss; neither is modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012 (Ada 2012), §6.1.1 'Preconditions and Postconditions', paragraphs 31/3–36/3 (online edition http://www.ada-auth.org/standards/12rm/html/RM-6-1-1.html, accessed 2026-11-21). 6.1.1(35/3): 'Upon successful return from a call of the subprogram or entry, prior to copying back any by-copy in out or out parameters, the postcondition check is performed.' 6.1.1(36/3): a failed check raises the exception at the point of the call. Checks on every successful return correspond to the all-exits policy; the paragraph imposes no check on exception propagation.
  - G. T. Leavens et al., JML Reference Manual (draft), HTML edition generated 2013-05-31, §9.9.3 'Ensures Clauses' (https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_9.html, accessed 2026-11-21): 'An ensures clause specifies a normal postcondition, i.e., a property that is guaranteed to hold at the end of the method (or constructor) invocation in the case that this method (or constructor) invocation returns without throwing an exception.'
- **Design question:** Where should `ensures` checks be placed so that every exit (tail expression, early `return`, `?`) is covered?

#### R8. `erase_instr_eq_of_noChecks` (theorem)

```lean
-- lean/ToyContracts/Results.lean:69-70
theorem erase_instr_eq_of_noChecks (p : Placement) (g : Fn) (hg : NoChecks g) :
    erase (instr p g) = g := by …
```

Unfolded (prose):

```text
`NoChecks g` says that no statement of `g.prologue` and no statement of any block of `g.blocks` is a contract statement; `erase` filters out every contract statement.
```

- **Plain claim:** For every placement `p` and every function `g` with `NoChecks g` (no `checkReq`, `checkEns` or `assumeReq` in its prologue or in any block, reachable or not): `erase (instr p g) = g`.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: that deleting the inserted checks restores the uninstrumented program is folklore; no mechanized statement for runtime checks was found (ghost-code erasure is proved safe on paper by Filliâtre et al. 2016).
- **Hypothesis ledger:**
  - `hg : NoChecks g`: no contract statement in the prologue or in any block of `g`, reachable or not; `erase` deletes every contract statement, including any already in `g`, so without the hypothesis the erasure can differ from `g`. **tight** — counterexample `cex_erase_instr_noChecks`; witness class: a one-block function (`gInt`) containing one `ensures` check.
- **Depth:** shallow. List-filter identities on the prologue and on each block (`map_erase_instrBlock`).
- **Non-vacuity witness:** `gEarly` has no contract statements. (`nonvacuity_erase_instr`)
- **Non-claims:**
  - A syntactic identity; it says nothing about observations by itself.
  - Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
  - `NoChecks g` inspects the prologue and every block of `g`, reachable or not; the natural weakening that restricts it to blocks reachable from the entry is not established here.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012, §6.1.1 paragraph 19/3 and §11.4.2 'Pragmas Assert and Assertion_Policy', paragraphs 10/3 and 10.3/3 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html, accessed 2026-11-21). 6.1.1(19/3): pre- and postcondition expressions are enabled if checks are required by the assertion policies 'in effect at the point of a corresponding aspect specification'. 11.4.2(10/3): policy Ignore 'requires that the assertion expression not be evaluated at these points, and the run-time checks not be performed'. 11.4.2(10.3/3): 'If a pragma Assertion_Policy applies to a generic_instantiation, then the pragma Assertion_Policy applies to the entire instance.'
  - J.-C. Filliâtre, L. Gondelman and A. Paskevich, 'The Spirit of Ghost Code', Formal Methods in System Design 48(3):152–174, 2016, DOI 10.1007/s10703-016-0243-x (https://hal.science/hal-01396864, accessed 2026-11-21): defines erasure of ghost code and proves it safe by a bisimulation for a small ML-like language; related erasure result for specification-only code, not for runtime checks.
- **Design question:** When is running with checks disabled observationally identical to running with checks?

#### R24. `instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req` (characterization)

```lean
-- lean/ToyContracts/Results.lean:80-83
theorem instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req (c : Contract) (g : Fn)
    (hg : Lowered g) (x : Nat) (hreq : c.req x = true) :
    (RunEqAt c (instr .allExits g) g x ↔ EnsOnReturnsAt c g x) ∧
    (HaltsEqAt c (instr .allExits g) g x ↔ EnsOnReturnsAt c g x) := by …
```

Explicit form, with `RunEqAt`, `HaltsEqAt` and `EnsOnReturnsAt` unfolded:

```lean
((∀ n, run c (instr .allExits g) x n = run c g x n) ↔
    ∀ tr r, Halts c g x ⟨tr, .ret r⟩ → c.ens x r = true) ∧
  ((∀ o, Halts c (instr .allExits g) x o ↔ Halts c g x o) ↔
    ∀ tr r, Halts c g x ⟨tr, .ret r⟩ → c.ens x r = true)
```

- **Plain claim:** For every contract `c`, every function `g` with `Lowered g` (no block, reachable or not, ends in `tryQ`; contract statements in `g` are allowed, `NoChecks g` is not assumed) and every input `x` with `Req x`: the all-exits instrumentation `instr .allExits g` and `g` itself are fuel-exactly identical at `x` (`RunEqAt`: the same observation at every fuel, including the events emitted before the fuel runs out) iff every normal return of `g` on `x` satisfies `Ens` (`EnsOnReturnsAt c g x`); and the same iff holds with identity of halting observations (`HaltsEqAt`) in place of `RunEqAt`.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: run-time checking of preconditions at entry and postconditions at every normal return, and the effect of disabling checks, are classical (Ada 2012 RM 6.1.1, JML, Eiffel); proofs for other formalisms exist on paper (Ly et al. 2024); no mechanized statement for a CFG with several return edges was found.
- **Hypothesis ledger:**
  - `hg : Lowered g`: no block of `g`, reachable or not, ends in the source form `tryQ` of `?`; without it a `?` exit returns unchecked, so the two runs can agree while `Ens` fails. **tight** — counterexample `cex_instrSelf_lowered`; witness class: a two-block function with one `?` (`gTry`) at input `1` under `cOne`.
  - `hreq : c.req x = true`: off `Req` the instrumentation fails its `requires` check while `g` runs. **tight** — counterexample `cex_instrSelf_req`; witness class: a one-block function (`gGood`) at input `100` under `c1`.
- **Depth:** shallow. From `run_instr_allExits_eq_instrObs_of_lowered` and `instrObs_run_eq_of_req_of_ensOnReturnsAt`; the converse direction reads `Ens` off a halting return via `instrObs_eq_ret`.
- **Non-vacuity witness:** `gGood` on `5` (both sides hold), `gEarly` on `0` (both sides fail), and `gInt` on `3` under `cThree` (all hypotheses hold although `NoChecks gInt` fails). (`nonvacuity_instrSelf`)
- **Non-claims:**
  - This compares checking with running `g` as written, which is what a call does when its governing flag is off (`callRun_eq_ite_governingFlag_of_lowered`). The comparison with the erasure `erase (instr .allExits g)` is `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`, which assumes `NoChecks g`; that hypothesis is tight there (`cex_erasure_noChecks`: `gInt` at input `3` under `cThree`) because `erase` also deletes contract statements of `g`.
  - Diverging runs are compared by `RunEqAt` through their partial event traces; `HaltsEqAt` ignores them.
  - `Lowered g` inspects every block of `g`, reachable or not; the natural weakening that restricts it to blocks reachable from the entry is not established here.
  - Contract clauses are total Boolean functions of the immutable argument (and of the returned value); evaluating a clause cannot panic, diverge, have side effects or read mutable state. Mutable parameters and clauses over memory or over entry-time (`old`) values are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012, §6.1.1 paragraph 19/3 and §11.4.2 'Pragmas Assert and Assertion_Policy', paragraphs 10/3 and 10.3/3 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html, accessed 2026-11-21). 6.1.1(19/3): pre- and postcondition expressions are enabled if checks are required by the assertion policies 'in effect at the point of a corresponding aspect specification'. 11.4.2(10/3): policy Ignore 'requires that the assertion expression not be evaluated at these points, and the run-time checks not be performed'. 11.4.2(10.3/3): 'If a pragma Assertion_Policy applies to a generic_instantiation, then the pragma Assertion_Policy applies to the entire instance.'
  - D. Ly, N. Kosmatov, F. Loulergue and J. Signoles, 'Sound Runtime Assertion Checking for Memory Properties via Program Transformation', Formal Aspects of Computing 36(1), Article 4, 2024, DOI 10.1145/3605951 (author version https://hal.science/hal-04065774/file/main.pdf, accessed 2026-11-21): for an E-ACSL-style instrumentation of a C-like language it proves semantic preservation while no annotation is violated (its Theorem 5.7) and soundness of the runtime assertion checker (its Corollary 5.10), with paper proofs ('A machine-checked Coq proof of these results is left as future work').
- **Design question:** When is running with checks disabled observationally identical to running with checks?

#### R9. `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req` (characterization)

```lean
-- lean/ToyContracts/Results.lean:98-101
theorem erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req (c : Contract) (g : Fn)
    (hg : Lowered g) (hnc : NoChecks g) (x : Nat) (hreq : c.req x = true) :
    (RunEqAt c (erase (instr .allExits g)) (instr .allExits g) x ↔ EnsOnReturnsAt c g x) ∧
    (HaltsEqAt c (erase (instr .allExits g)) (instr .allExits g) x ↔ EnsOnReturnsAt c g x) := by …
```

Explicit form, with `RunEqAt`, `HaltsEqAt` and `EnsOnReturnsAt` unfolded:

```lean
((∀ n, run c (erase (instr .allExits g)) x n = run c (instr .allExits g) x n) ↔
    ∀ tr r, Halts c g x ⟨tr, .ret r⟩ → c.ens x r = true) ∧
  ((∀ o, Halts c (erase (instr .allExits g)) x o ↔ Halts c (instr .allExits g) x o) ↔
    ∀ tr r, Halts c g x ⟨tr, .ret r⟩ → c.ens x r = true)
```

- **Plain claim:** For every contract `c`, every function `g` with `Lowered g` and `NoChecks g` (no block, reachable or not, ends in `tryQ`; no contract statement in the prologue or in any block, reachable or not), and every input `x` with `Req x`: the erasure `erase (instr .allExits g)` and the all-exits instrumentation `instr .allExits g` are fuel-exactly identical at `x` (`RunEqAt`: the same observation at every fuel, including the events emitted before the fuel runs out) iff every normal return of `g` on `x` satisfies `Ens` (`EnsOnReturnsAt c g x`); and the same iff holds with identity of halting observations (`HaltsEqAt`) in place of `RunEqAt`.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: run-time checking of preconditions at entry and postconditions at every normal return, and the effect of disabling checks, are classical (Ada 2012 RM 6.1.1, JML, Eiffel); proofs for other formalisms exist on paper (Ly et al. 2024); no mechanized statement for a CFG with several return edges was found.
- **Hypothesis ledger:**
  - `hg : Lowered g`: no block of `g`, reachable or not, ends in the source form `tryQ` of `?`; without it a `?` exit returns unchecked, so erasure and instrumentation can agree while `Ens` fails. **tight** — counterexample `cex_erasure_lowered`; witness class: a two-block function with one `?` (`gTry`) at input `1` under `cOne`.
  - `hnc : NoChecks g`: no contract statement in the prologue or in any block of `g`, reachable or not; `erase` also deletes contract statements already in `g`, so the erasure can differ from `g` and the right-hand side no longer describes it. **tight** — counterexample `cex_erasure_noChecks`; witness class: a one-block function containing a failing `ensures` check (`gInt`) at input `3` under `cThree`.
  - `hreq : c.req x = true`: off `Req` the instrumentation fails its `requires` check while the erasure runs. **tight** — counterexample `cex_erasure_req`; witness class: a one-block function (`gGood`) at input `100` under `c1`.
- **Depth:** shallow. From `erase_instr_eq_of_noChecks` and `instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`.
- **Non-vacuity witness:** `gGood` on `5` (both sides hold) and `gEarly` on `0` (both sides fail) satisfy all hypotheses. (`nonvacuity_erasure_pointwise`)
- **Non-claims:**
  - Termination plays no role: `RunEqAt` compares partial event traces of runs that exhaust their fuel; `HaltsEqAt` ignores diverging runs.
  - The theorem is stated for the all-exits placement. With tail-only placement there is an instance at which its forward direction fails (`cex_erasure_tailOnly`: for `gEarly` on `0` under `c1` the erasure of the tail-only instrumentation is fuel-exactly identical to it while `Ens 0 7` fails).
  - Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
  - `Lowered g` and `NoChecks g` inspect every block of `g`, reachable or not (`NoChecks g` also the prologue); the natural weakenings that restrict them to blocks reachable from the entry are not established here.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012, §6.1.1 paragraph 19/3 and §11.4.2 'Pragmas Assert and Assertion_Policy', paragraphs 10/3 and 10.3/3 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html, accessed 2026-11-21). 6.1.1(19/3): pre- and postcondition expressions are enabled if checks are required by the assertion policies 'in effect at the point of a corresponding aspect specification'. 11.4.2(10/3): policy Ignore 'requires that the assertion expression not be evaluated at these points, and the run-time checks not be performed'. 11.4.2(10.3/3): 'If a pragma Assertion_Policy applies to a generic_instantiation, then the pragma Assertion_Policy applies to the entire instance.'
  - SPARK Reference Manual, release 28.0w (development documentation at https://docs.adacore.com/spark2014-docs/html/lrm/introduction.html, accessed 2026-11-21; no immutable revision identifier is published). §1: 'The run-time checking of assertion expressions may be suppressed by using the Ada pragma Assertion_Policy but the static analysis and proof tools always use the assertion expressions whatever the assertion policy.' §1.4.1 'Further Details on Formal Verification': 'In addition, the generation of verification conditions is unaffected by the suppression of checks (e.g., via pragma Suppress) or the disabling of assertions (e.g., via pragma Assertion_Policy).'
  - D. Ly, N. Kosmatov, F. Loulergue and J. Signoles, 'Sound Runtime Assertion Checking for Memory Properties via Program Transformation', Formal Aspects of Computing 36(1), Article 4, 2024, DOI 10.1145/3605951 (author version https://hal.science/hal-04065774/file/main.pdf, accessed 2026-11-21): for an E-ACSL-style instrumentation of a C-like language it proves semantic preservation while no annotation is violated (its Theorem 5.7) and soundness of the runtime assertion checker (its Corollary 5.10), with paper proofs ('A machine-checked Coq proof of these results is left as future work').
- **Design question:** When is running with checks disabled observationally identical to running with checks?

#### R10. `erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks` (characterization)

```lean
-- lean/ToyContracts/Results.lean:111-116
theorem erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks (c : Contract) (g : Fn)
    (hg : Lowered g) (hnc : NoChecks g) :
    ((∀ x, c.req x = true → RunEqAt c (erase (instr .allExits g)) (instr .allExits g) x) ↔
        StaticObligation c g) ∧
    ((∀ x, c.req x = true → HaltsEqAt c (erase (instr .allExits g)) (instr .allExits g) x) ↔
        StaticObligation c g) := by …
```

Explicit form, with `RunEqAt`, `HaltsEqAt` and `StaticObligation` unfolded:

```lean
((∀ x, c.req x = true →
      ∀ n, run c (erase (instr .allExits g)) x n = run c (instr .allExits g) x n) ↔
    ∀ x, c.req x = true → ∀ tr r, Halts c g x ⟨tr, .ret r⟩ → c.ens x r = true) ∧
  ((∀ x, c.req x = true →
      ∀ o, Halts c (erase (instr .allExits g)) x o ↔ Halts c (instr .allExits g) x o) ↔
    ∀ x, c.req x = true → ∀ tr r, Halts c g x ⟨tr, .ret r⟩ → c.ens x r = true)
```

- **Plain claim:** For every contract `c` and every function `g` with `Lowered g` and `NoChecks g` (both over every block, reachable or not; `NoChecks g` also over the prologue): the erasure `erase (instr .allExits g)` is fuel-exactly identical to the all-exits instrumentation at every input satisfying `Req` iff the static obligation `StaticObligation c g` holds (for every `x` with `Req x`, every normal return `r` of `g` on `x` satisfies `Ens x r`); and the same iff holds with `HaltsEqAt` in place of `RunEqAt`.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: run-time checking of preconditions at entry and postconditions at every normal return, and the effect of disabling checks, are classical (Ada 2012 RM 6.1.1, JML, Eiffel); proofs for other formalisms exist on paper (Ly et al. 2024); no mechanized statement for a CFG with several return edges was found.
- **Hypothesis ledger:**
  - `hg : Lowered g`: no block of `g`, reachable or not, ends in the source form `tryQ` of `?`; as in the pointwise form. **tight** — counterexample `cex_erasure_global_lowered`; witness class: `gTry` under `cOne` (whose `Req` admits exactly the input `1`).
  - `hnc : NoChecks g`: no contract statement in the prologue or in any block of `g`, reachable or not; as in the pointwise form. **tight** — counterexample `cex_erasure_global_noChecks`; witness class: `gInt` under `cThree` (whose `Req` admits exactly the input `3`).
- **Depth:** shallow. Pointwise from `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`.
- **Non-vacuity witness:** `gGood` (obligation holds) and `gEarly` (obligation fails) satisfy the hypotheses. (`nonvacuity_erasure_global`)
- **Non-claims:**
  - Equivalence is claimed on `Req` inputs; off `Req` erasure and instrumentation never have the same halting observations (`not_haltsEqAt_erase_instr_of_req_false`).
  - Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
  - `Lowered g` and `NoChecks g` inspect every block of `g`, reachable or not (`NoChecks g` also the prologue); the natural weakenings that restrict them to blocks reachable from the entry are not established here.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012, §6.1.1 paragraph 19/3 and §11.4.2 'Pragmas Assert and Assertion_Policy', paragraphs 10/3 and 10.3/3 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html, accessed 2026-11-21). 6.1.1(19/3): pre- and postcondition expressions are enabled if checks are required by the assertion policies 'in effect at the point of a corresponding aspect specification'. 11.4.2(10/3): policy Ignore 'requires that the assertion expression not be evaluated at these points, and the run-time checks not be performed'. 11.4.2(10.3/3): 'If a pragma Assertion_Policy applies to a generic_instantiation, then the pragma Assertion_Policy applies to the entire instance.'
  - SPARK Reference Manual, release 28.0w (development documentation at https://docs.adacore.com/spark2014-docs/html/lrm/introduction.html, accessed 2026-11-21; no immutable revision identifier is published). §1: 'The run-time checking of assertion expressions may be suppressed by using the Ada pragma Assertion_Policy but the static analysis and proof tools always use the assertion expressions whatever the assertion policy.' §1.4.1 'Further Details on Formal Verification': 'In addition, the generation of verification conditions is unaffected by the suppression of checks (e.g., via pragma Suppress) or the disabling of assertions (e.g., via pragma Assertion_Policy).'
  - D. Ly, N. Kosmatov, F. Loulergue and J. Signoles, 'Sound Runtime Assertion Checking for Memory Properties via Program Transformation', Formal Aspects of Computing 36(1), Article 4, 2024, DOI 10.1145/3605951 (author version https://hal.science/hal-04065774/file/main.pdf, accessed 2026-11-21): for an E-ACSL-style instrumentation of a C-like language it proves semantic preservation while no annotation is violated (its Theorem 5.7) and soundness of the runtime assertion checker (its Corollary 5.10), with paper proofs ('A machine-checked Coq proof of these results is left as future work').
- **Design question:** When is running with checks disabled observationally identical to running with checks?

#### R11. `not_haltsEqAt_erase_instr_of_req_false` (theorem)

```lean
-- lean/ToyContracts/Results.lean:134-138
theorem not_haltsEqAt_erase_instr_of_req_false (c : Contract) (p : Placement) (g : Fn) (x : Nat)
    (h : c.req x = false) :
    (∀ n, run c (instr p g) x n = ⟨[], .checkFail .pre⟩) ∧ NoChecks (erase (instr p g)) ∧
    (∀ n k, (run c (erase (instr p g)) x n).outcome ≠ .checkFail k) ∧
    ¬ HaltsEqAt c (erase (instr p g)) (instr p g) x := by …
```

Unfolded (prose):

```text
`HaltsEqAt c p q x` means `∀ o, Halts c p x o ↔ Halts c q x o`; `NoChecks` is as for `erase_instr_eq_of_noChecks`.
```

- **Plain claim:** For every contract `c`, placement `p`, function `g` (no hypothesis on `g` or `p`) and input `x` with `Req x` false: the instrumentation `instr p g` ends with a `requires` failure and no events at every fuel; the erasure `erase (instr p g)` contains no contract statement in its prologue or in any block, reachable or not (`NoChecks`), and its run never ends with a failed check, at any fuel; and the two do not have the same halting observations at `x`.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: that disabling a precondition check changes behaviour on inputs violating the precondition is folklore (Ada 2012 11.4.2(10/3)); no mechanized statement was found.
- **Hypothesis ledger:**
  - `h : c.req x = false`: makes the entry check fail. **tight** — counterexample `cex_not_haltsEq_req_true`; witness class: `gGood` at input `5` under `c1`.
- **Depth:** shallow. The entry check fails before any fuel is used; the erasure never fails a check by a fuel induction (`run_no_checkFail_of_noChecks`, with `noChecks_erase`).
- **Non-vacuity witness:** `Req 100` fails under `c1`. (`nonvacuity_req_false`)
- **Positive control:** at an input where `Req` holds, the conclusion fails: `cex_not_haltsEq_req_true` proves `c1.req 5 = true` and the negation of the theorem's conclusion for `gGood` at `5` with placement `.allExits` (it is also the counterexample for `h` above).
- **Non-claims:**
  - The theorem's hypothesis is an input with `c.req x = false`. For a contract whose `requires` clause is identically true there is none, and in a whole program whose calls all pass arguments satisfying `Req`, such inputs never reach `g` (whole-program call contexts are not modelled).
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012, §6.1.1 paragraph 19/3 and §11.4.2 'Pragmas Assert and Assertion_Policy', paragraphs 10/3 and 10.3/3 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html, accessed 2026-11-21). 6.1.1(19/3): pre- and postcondition expressions are enabled if checks are required by the assertion policies 'in effect at the point of a corresponding aspect specification'. 11.4.2(10/3): policy Ignore 'requires that the assertion expression not be evaluated at these points, and the run-time checks not be performed'. 11.4.2(10.3/3): 'If a pragma Assertion_Policy applies to a generic_instantiation, then the pragma Assertion_Policy applies to the entire instance.'
- **Design question:** When is running with checks disabled observationally identical to running with checks?

#### R12. `run_assumeErase_eq_ite_req` (theorem)

```lean
-- lean/ToyContracts/Results.lean:147-148
theorem run_assumeErase_eq_ite_req (c : Contract) (q : Fn) (x n : Nat) :
    run c (assumeErase q) x n = if c.req x then run c (erase q) x n else ⟨[], .ub⟩ := by …
```

Unfolded (prose):

```text
`assumeErase q` is `erase q` with `.assumeReq` prepended to its prologue; `assumeReq` stops with `ub` when `c.req x` is false and does nothing otherwise.
```

- **Plain claim:** For every contract `c`, every function `q`, input `x` and fuel `n`: running `assumeErase q` (the erasure of `q` with `assumeReq` first in the prologue) gives the same observation as running `erase q` if `Req x` holds, and gives UB with no events (`⟨[], .ub⟩`) if `Req x` fails. The instances of interest are `q = instr p g`.
- **Basis:** execution (Lean kernel check).
- **Tier:** T0. T0: the documented semantics of a UB-on-false assumption (LLVM `llvm.assume`, C++ `[[assume]]`), restated for an assumption placed first in the prologue.
- **Hypothesis ledger:**
  - (no hypotheses)
- **Depth:** shallow. Unfolding the prologue, plus a fuel induction showing that runs from a block depend on the blocks only (`runFrom_congr_blocks`), since `assumeErase q` and `erase q` differ in their prologue.
- **Non-vacuity witness:** Both branches occur: `Req 5` holds and `Req 100` fails under `c1`. (`nonvacuity_assumeErase`)
- **Non-claims:**
  - UB is an outcome of the toy (`ub`); what an optimizer may do with it is captured here by the refinement relation `UBRefinesAt` and by nothing else.
  - The assumption is placed first in the prologue; assumptions at other program points are not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - LLVM Language Reference Manual, intrinsic 'llvm.assume' (https://llvm.org/docs/LangRef.html#llvm-assume-intrinsic, accessed 2026-11-21), Semantics: 'If the condition is violated during execution, the behavior is undefined.' (A moving document; no revision is pinned.)
  - T. Doumler, 'Portable assumptions', ISO/IEC JTC1/SC22/WG21 document P1774R8, 2022-06-14 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2022/p1774r8.pdf, accessed 2026-11-21). Proposed wording for `[[assume(expression)]]`: 'If the converted expression would evaluate to true at the point where the assumption appears, the assumption has no effect. Otherwise, the behavior is undefined.'
  - Corpus package zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume (google/zerocopy branch reference at commit 95e95c2fbada69bc95437324bf4462759bd738a4): `assume c` as a UB-on-false compiler assumption, and UB-erasing transformations as forward refinements (UB-bearing program as source) that are not equivalences; cited, not repeated.
- **Design question:** What does erasing checks while assuming `Req` do to a run?

#### R13. `instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt` (theorem)

```lean
-- lean/ToyContracts/Results.lean:161-163
theorem instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt (c : Contract)
    (g : Fn) (hnc : NoChecks g) (x : Nat) (hob : StaticObligationAt c g x) :
    UBRefinesAt c (instr .allExits g) (assumeErase (instr .allExits g)) x := by …
```

Explicit form, with `UBRefinesAt` unfolded:

```lean
∀ o, Halts c (instr .allExits g) x o →
  Halts c (assumeErase (instr .allExits g)) x o ∨
    ∃ tr, Halts c (assumeErase (instr .allExits g)) x ⟨tr, .ub⟩ ∧ tr <+: o.events
```

- **Plain claim:** For every contract `c`, every function `g` with `NoChecks g` (no contract statement in its prologue or in any block, reachable or not; `Lowered g` is not assumed) and every input `x` with `StaticObligationAt c g x` (if `Req x`, every normal return `r` of `g` on `x` satisfies `Ens x r`): the checked program `instr .allExits g` UB-refines the assume-erased program `assumeErase (instr .allExits g)` at `x` (`UBRefinesAt`, with the checked program as target and the assume-erased program as source): every halting observation of the checked program is a halting observation of the assume-erased program, or the assume-erased program halts with UB after a prefix of its events.
- **Basis:** execution (Lean kernel check).
- **Tier:** T0. T0: that undefined behaviour of the source licenses every target behaviour, so that defined checking refines a UB-on-false assumption and not conversely, is the standard UB-refinement order (Alive2; mechanized for monadic programs by Lammich's Refine_Monadic, where a failing assertion is the top element); restated for the toy.
- **Hypothesis ledger:**
  - `hnc : NoChecks g`: no contract statement in the prologue or in any block of `g`, reachable or not; a contract statement already in `g` can fail in the checked program while `erase` deletes it from the assume-erased program. **tight** — counterexample `cex_ubRefines_noChecks`; witness class: `gInt` at input `3` under `cThree`.
  - `hob : StaticObligationAt c g x`: an `ensures` failure of the checked program is neither an observation of the assume-erased program nor licensed by UB there. **tight** — counterexample `cex_ubRefines_obligation`; witness class: `gEarly` at input `0` under `c1`.
- **Depth:** shallow. Off `Req` the source halts with UB and no events; on `Req`, every inserted check passes wherever it is placed (`run_instr_eq_of_req_of_ensOnReturnsAt`, a fuel induction), and `run_assumeErase_eq_ite_req` with `erase_instr_eq_of_noChecks` identifies the source run with the run of `g`.
- **Non-vacuity witness:** `gGood` on `5` (lowered) and the unlowered `gTry` on `5` satisfy all hypotheses. (`nonvacuity_ubRefines`)
- **Non-claims:**
  - Direction: in `UBRefinesAt c tgt src x` the first program refines the second. This theorem has the checked program as `tgt`. It does not say that the assume-erased program refines the checked program; that fails at every input where `Req` fails (`not_assumeErase_ubRefinesAt_instr_of_req_false`), so this theorem does not justify replacing checks by `assume Req` as a UB-refining transformation of the checked program.
  - `UBRefinesAt` compares halting observations of the target: a target that does not halt at `x` refines every source at `x` (`ubRefinesAt_of_forall_not_halts`; instance `ubRefinesAt_gLoop_gGood_5`, where the non-halting `gLoop` refines `gGood` at `5` although `gGood` returns `5` without UB). Divergence and the events of diverging runs are not constrained by this theorem.
  - Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
  - `NoChecks g` inspects the prologue and every block of `g`, reachable or not; the natural weakening that restricts it to blocks reachable from the entry is not established here.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu and J. Regehr, 'Alive2: Bounded Translation Validation for LLVM', PLDI 2021, pp. 65–79, DOI 10.1145/3453483.3454030 (https://users.cs.utah.edu/~regehr/alive2-pldi21.pdf, accessed 2026-11-21): a final source state that is undefined is refined by every target state (rule final-state-ub, its Fig. 4); `UBRefinesAt` is the halting-observation analogue, with a prefix condition on events.
  - P. Lammich, 'Refinement for Monadic Programs', Archive of Formal Proofs, January 2012, ISSN 2150-914x (https://www.isa-afp.org/entries/Refine_Monadic.html, accessed 2026-11-21): a mechanized (Isabelle/HOL) refinement calculus in which `ASSERT Φ` is `return ()` if `Φ` holds and the top element otherwise, and `ASSUME Φ` is `return ()` if `Φ` holds and the bottom element otherwise. The toy's failing `assumeReq` (UB, refined by every behaviour) plays the role of that top element.
  - R.-J. Back and J. von Wright, Refinement Calculus: A Systematic Introduction, Springer, 1998, ISBN 978-0-387-98417-9, DOI 10.1007/978-1-4612-1674-2: statements as predicate transformers, including assertions and guards, ordered by refinement.
  - X. Leroy, 'Formal verification of a realistic compiler', Communications of the ACM 52(7):107–115, July 2009, DOI 10.1145/1538788.1538814: compiler correctness stated as preservation of program behaviours, mechanized in Coq; cited for the notion of semantic preservation that `UBRefinesAt` specializes.
  - T. Doumler, 'Portable assumptions', ISO/IEC JTC1/SC22/WG21 document P1774R8, 2022-06-14 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2022/p1774r8.pdf, accessed 2026-11-21). Proposed wording for `[[assume(expression)]]`: 'If the converted expression would evaluate to true at the point where the assumption appears, the assumption has no effect. Otherwise, the behavior is undefined.'
  - Corpus package zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume (google/zerocopy branch reference at commit 95e95c2fbada69bc95437324bf4462759bd738a4): `assume c` as a UB-on-false compiler assumption, and UB-erasing transformations as forward refinements (UB-bearing program as source) that are not equivalences; cited, not repeated.
- **Design question:** Is replacing runtime checks by erasure plus `assume Req` an equivalence, a refinement in one direction, or neither?

#### R14. `not_assumeErase_ubRefinesAt_instr_of_req_false` (theorem)

```lean
-- lean/ToyContracts/Results.lean:179-183
theorem not_assumeErase_ubRefinesAt_instr_of_req_false (c : Contract) (p : Placement) (g : Fn)
    (x : Nat) (h : c.req x = false) :
    (∀ n, run c (assumeErase (instr p g)) x n = ⟨[], .ub⟩) ∧
    (∀ n, run c (instr p g) x n = ⟨[], .checkFail .pre⟩) ∧
    ¬ UBRefinesAt c (assumeErase (instr p g)) (instr p g) x := by …
```

Unfolded (prose):

```text
`UBRefinesAt c tgt src x` means: for every `o` with `Halts c tgt x o`, either `Halts c src x o` or there is `tr` with `Halts c src x ⟨tr, .ub⟩` and `tr` a prefix of `o.events`. Here `tgt` is the assume-erased program.
```

- **Plain claim:** For every contract `c`, placement `p`, function `g` (no hypothesis on `g` or `p`) and input `x` with `Req x` false: the assume-erased program `assumeErase (instr p g)` reaches UB with no events at every fuel; the checked program `instr p g` ends with a `requires` failure and no events at every fuel (so it never reaches UB); and the assume-erased program does not UB-refine the checked program at `x` (`UBRefinesAt`, with the assume-erased program as target and the checked program as source).
- **Basis:** execution (Lean kernel check).
- **Tier:** T0. T0: that undefined behaviour of the source licenses every target behaviour, so that defined checking refines a UB-on-false assumption and not conversely, is the standard UB-refinement order (Alive2; mechanized for monadic programs by Lammich's Refine_Monadic, where a failing assertion is the top element); restated for the toy.
- **Hypothesis ledger:**
  - `h : c.req x = false`: makes the assumption fail. **tight** — counterexample `cex_not_ubRefines_req_true`; witness class: `gGood` at input `5` under `c1`.
- **Depth:** definitional. Both prologues stop at their first statement before any fuel is used; the refinement fails at the UB observation.
- **Non-vacuity witness:** `Req 100` fails under `c1`. (`nonvacuity_req_false`)
- **Positive control:** at an input where `Req` holds, the conclusion fails: `cex_not_ubRefines_req_true` proves `c1.req 5 = true`, that the assume-erased `gGood` UB-refines the checked `gGood` at `5` with placement `.allExits`, and the negation of the theorem's conclusion there (it is also the counterexample for `h` above).
- **Non-claims:**
  - Together with `instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`, this shows that erasure plus `assume Req` is not equivalent to checking in the toy: the checked program UB-refines the assume-erased program (under that theorem's hypotheses), and the assume-erased program does not UB-refine the checked program at inputs where `Req` fails. Replacing checks by `assume Req` adds UB there.
  - At an input with `Req x` true the conclusion can fail: for `gGood` at `5` under `c1` the assume-erased program UB-refines the checked program (`cex_not_ubRefines_req_true`); a caller that guarantees `Req` at every call is not modelled.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu and J. Regehr, 'Alive2: Bounded Translation Validation for LLVM', PLDI 2021, pp. 65–79, DOI 10.1145/3453483.3454030 (https://users.cs.utah.edu/~regehr/alive2-pldi21.pdf, accessed 2026-11-21): a final source state that is undefined is refined by every target state (rule final-state-ub, its Fig. 4); `UBRefinesAt` is the halting-observation analogue, with a prefix condition on events.
  - P. Lammich, 'Refinement for Monadic Programs', Archive of Formal Proofs, January 2012, ISSN 2150-914x (https://www.isa-afp.org/entries/Refine_Monadic.html, accessed 2026-11-21): a mechanized (Isabelle/HOL) refinement calculus in which `ASSERT Φ` is `return ()` if `Φ` holds and the top element otherwise, and `ASSUME Φ` is `return ()` if `Φ` holds and the bottom element otherwise. The toy's failing `assumeReq` (UB, refined by every behaviour) plays the role of that top element.
  - LLVM Language Reference Manual, intrinsic 'llvm.assume' (https://llvm.org/docs/LangRef.html#llvm-assume-intrinsic, accessed 2026-11-21), Semantics: 'If the condition is violated during execution, the behavior is undefined.' (A moving document; no revision is pinned.)
  - T. Doumler, 'Portable assumptions', ISO/IEC JTC1/SC22/WG21 document P1774R8, 2022-06-14 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2022/p1774r8.pdf, accessed 2026-11-21). Proposed wording for `[[assume(expression)]]`: 'If the converted expression would evaluate to true at the point where the assumption appears, the assumption has no effect. Otherwise, the behavior is undefined.'
  - Corpus package zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume (google/zerocopy branch reference at commit 95e95c2fbada69bc95437324bf4462759bd738a4): `assume c` as a UB-on-false compiler assumption, and UB-erasing transformations as forward refinements (UB-bearing program as source) that are not equivalences; cited, not repeated.
- **Design question:** Is replacing runtime checks by erasure plus `assume Req` an equivalence, a refinement in one direction, or neither?

#### R15. `callRun_eq_ite_governingFlag_of_lowered` (theorem)

```lean
-- lean/ToyContracts/Results.lean:196-199
theorem callRun_eq_ite_governingFlag_of_lowered (fl : Nat → Bool) (s : Site) (res : Resolution)
    (cs : CallSite) (c : Contract) (g : Fn) (hg : Lowered g) (x n : Nat) :
    callRun fl s res cs c g x n =
      if fl (governingCrate s res cs) then instrObs c x (run c g x n) else run c g x n := by …
```

Unfolded (prose):

```text
`callRun fl s res cs c g x n` is `callInCallerCrate (fl cs.callerCrate) s c (instantiateIn (fl cs.instCrate) (compileInDefCrate (fl cs.defCrate) s res cs.generic g)) x n`; `governingCrate` is the crate named in the case analysis of the plain claim.
```

- **Plain claim:** For every flag assignment `fl`, placement `s`, resolution `res`, call site `cs`, contract `c`, callee `g` with `Lowered g` (no block, reachable or not, ends in `tryQ`), argument `x` and fuel `n`: the cross-crate call `callRun fl s res cs c g x n` (compilation in the defining crate, instantiation in the instantiating crate and the call in the calling crate, each step reading the flag of its own crate and no other; callee-side checks are inserted by `instr .allExits`) equals `instrObs c x (run c g x n)` if `fl (governingCrate s res cs)` is true and `run c g x n` if it is false. The governing crate is the calling crate for caller-side placement; under callee-side placement it is the defining crate when the flag test is resolved at definition or the callee is not generic, and the instantiating crate for a generic callee whose flag test is resolved at instantiation.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: per-unit assertion policies scoped to the declaration or to a generic instance are documented for Ada 2012 (RM 6.1.1(19/3), 11.4.2(10.3/3)); no mechanized statement was found; stated here for a toy pipeline of per-crate steps.
- **Hypothesis ledger:**
  - `hg : Lowered g`: no block of `g`, reachable or not, ends in the source form `tryQ` of `?`; callee-side placement instruments the callee body, and a `?` exit gets no check. **tight** — counterexample `cex_callRun_lowered`; witness class: callee-side placement with every flag on, for `gTry` at input `1` and fuel `1` under `cOne`.
- **Depth:** shallow. Case analysis on placement, resolution, genericity and the three flags; the callee-side cases use `run_instr_allExits_eq_instrObs_of_lowered`. `callRun` does not mention `governingCrate`; the theorem derives it.
- **Non-vacuity witness:** `gEarly` is lowered. (`nonvacuity_callRun`)
- **Non-claims:**
  - `callRun` is a toy pipeline of three per-crate steps (`compileInDefCrate`, `instantiateIn`, `callInCallerCrate`), each of which reads the flag of its own crate and no other; it is not derived from a compilation, monomorphization or linking semantics of any real toolchain. Where a real compiler resolves a flag test (`Resolution`) and where checks are placed (`Site`) are parameters, not findings, and callee-side checks in `callRun` always use the all-exits placement.
  - Policies that check `requires` at the caller and `ensures` in the callee, or that check whenever either crate's flag is on, are not modelled; nor are indirect calls through function pointers or trait objects, or a generic callee instantiated in more than one crate.
  - Under resolution at definition the governing crate is the crate holding the check (`governingCrate_atDefinition`); under resolution at instantiation it can differ (`cex_calleeSide_atInstantiation_definingFlag_on_undetected`).
  - `Lowered g` inspects every block of `g`, reachable or not; the natural weakening that restricts it to blocks reachable from the entry is not established here.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012, §6.1.1 paragraph 19/3 and §11.4.2 'Pragmas Assert and Assertion_Policy', paragraphs 10/3 and 10.3/3 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html, accessed 2026-11-21). 6.1.1(19/3): pre- and postcondition expressions are enabled if checks are required by the assertion policies 'in effect at the point of a corresponding aspect specification'. 11.4.2(10/3): policy Ignore 'requires that the assertion expression not be evaluated at these points, and the run-time checks not be performed'. 11.4.2(10.3/3): 'If a pragma Assertion_Policy applies to a generic_instantiation, then the pragma Assertion_Policy applies to the entire instance.'
  - R. B. Findler and M. Felleisen, 'Contracts for Higher-Order Functions', ICFP 2002, pp. 48–59, DOI 10.1145/581478.581484: contracts monitored at module boundaries; cited for the distinction between the calling and the defining side of a contract.
  - Corpus package monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets (google/zerocopy branch reference at commit 95e95c2fbada69bc95437324bf4462759bd738a4): a toy model of whole-program monomorphization in which generic bodies are instantiated by substitution; cited for instantiation of generic bodies, not repeated.
  - Corpus package call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations (google/zerocopy branch reference at commit 95e95c2fbada69bc95437324bf4462759bd738a4): a toy model of call-site inlining, including a counterexample showing that a condition proved for an inlined callee need not establish the callee's contract from its own entry; cited as related work on caller-side versus callee-side reasoning, not repeated.
- **Design question:** What happens when the defining, instantiating and calling crates use different flag settings?

#### R16. `detects_iff_governingFlag_of_lowered_of_noChecks_of_violation` (characterization)

```lean
-- lean/ToyContracts/Results.lean:209-212
theorem detects_iff_governingFlag_of_lowered_of_noChecks_of_violation (fl : Nat → Bool)
    (s : Site) (res : Resolution) (cs : CallSite) (c : Contract) (g : Fn) (hg : Lowered g)
    (hnc : NoChecks g) (x : Nat) (hv : ViolationAt c g x) :
    Detects fl s res cs c g x ↔ fl (governingCrate s res cs) = true := by …
```

Explicit form, with `Detects` unfolded:

```lean
(∃ n tr k, callRun fl s res cs c g x n = ⟨tr, .checkFail k⟩) ↔
  fl (governingCrate s res cs) = true
```

- **Plain claim:** For every flag assignment `fl`, placement `s`, resolution `res`, call site `cs`, contract `c`, callee `g` with `Lowered g` and `NoChecks g` (both over every block, reachable or not; `NoChecks g` also over the prologue), and argument `x` with `ViolationAt c g x` (`Req x` fails, or `Req x` holds and `g` halts on `x` with a normal return of a value violating `Ens`): the call (`callRun`, whose callee-side checks are inserted by `instr .allExits`) reports a failed check for some fuel (`Detects`) iff `fl (governingCrate s res cs)` is true.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: per-unit assertion policies scoped to the declaration or to a generic instance are documented for Ada 2012 (RM 6.1.1(19/3), 11.4.2(10.3/3)); no mechanized statement was found; stated here for a toy pipeline of per-crate steps.
- **Hypothesis ledger:**
  - `hg : Lowered g`: no block of `g`, reachable or not, ends in the source form `tryQ` of `?`; otherwise callee-side checks can miss a `?` exit. **tight** — counterexample `cex_detects_lowered`; witness class: `gTry` at input `1` under `cOne`, every flag on, callee-side placement.
  - `hnc : NoChecks g`: no contract statement in the prologue or in any block of `g`, reachable or not; `Detects` counts every failed check, including one already in `g`, which can fail with every flag off. **tight** — counterexample `cex_detects_noChecks`; witness class: `gIntReq` (containing its own `requires` check) at input `100` under `c1`, every flag off.
  - `hv : ViolationAt c g x`: under the other two hypotheses, nothing is reported without a violation, even with the flag on. **tight** — counterexample `cex_detects_violation`; witness class: `gGood` at input `5` under `c1`, every flag on.
- **Depth:** shallow. From `callRun_eq_ite_governingFlag_of_lowered`, `run_no_checkFail_of_noChecks`, and evaluation of `instrObs` at the violating return.
- **Non-vacuity witness:** `gEarly` on `0` (an `ensures` violation) and on `100` (a `requires` violation). (`nonvacuity_detects`)
- **Non-claims:**
  - When `Req x` holds, a call of a callee without contract statements (in its prologue or in any block, reachable or not) that never returns normally on `x` (it panics, diverges or gets stuck) reports nothing under any flags (`not_detects_of_noChecks_of_req_of_no_ret`). Without `Req x` that conclusion fails: `gPanic` panics on `100` under `c1` and its callee-side call with every flag on reports a failed check (`refuted_no_report_for_panicking_call_with_flag_on`, a proved refutation of an earlier candidate statement that omitted `Req x`). When `Req x` fails and the governing flag is on, the call ends with a `requires` failure and no events at every fuel, whatever `g` does (`callRun_eq_checkFail_pre_of_req_false_of_governingFlag`).
  - `Detects` counts every `checkFail` outcome and cannot tell an inserted check from a contract statement already in `g`; `NoChecks g` is tight for that reason (`cex_detects_noChecks`).
  - Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs. In-body assertions with predicates of their own are not modelled.
  - `callRun` is a toy pipeline of three per-crate steps (`compileInDefCrate`, `instantiateIn`, `callInCallerCrate`), each of which reads the flag of its own crate and no other; it is not derived from a compilation, monomorphization or linking semantics of any real toolchain. Where a real compiler resolves a flag test (`Resolution`) and where checks are placed (`Site`) are parameters, not findings, and callee-side checks in `callRun` always use the all-exits placement.
  - Policies that check `requires` at the caller and `ensures` in the callee, or that check whenever either crate's flag is on, are not modelled; nor are indirect calls through function pointers or trait objects, or a generic callee instantiated in more than one crate.
  - `Lowered g` and `NoChecks g` inspect every block of `g`, reachable or not (`NoChecks g` also the prologue); the natural weakenings that restrict them to blocks reachable from the entry are not established here.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012, §6.1.1 paragraph 19/3 and §11.4.2 'Pragmas Assert and Assertion_Policy', paragraphs 10/3 and 10.3/3 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html, accessed 2026-11-21). 6.1.1(19/3): pre- and postcondition expressions are enabled if checks are required by the assertion policies 'in effect at the point of a corresponding aspect specification'. 11.4.2(10/3): policy Ignore 'requires that the assertion expression not be evaluated at these points, and the run-time checks not be performed'. 11.4.2(10.3/3): 'If a pragma Assertion_Policy applies to a generic_instantiation, then the pragma Assertion_Policy applies to the entire instance.'
  - R. B. Findler and M. Felleisen, 'Contracts for Higher-Order Functions', ICFP 2002, pp. 48–59, DOI 10.1145/581478.581484: contracts monitored at module boundaries; cited for the distinction between the calling and the defining side of a contract.
- **Design question:** What happens when the defining, instantiating and calling crates use different flag settings?

#### R17. `callRun_eq_run_of_not_violation` (theorem)

```lean
-- lean/ToyContracts/Results.lean:231-233
theorem callRun_eq_run_of_not_violation (fl : Nat → Bool) (s : Site) (res : Resolution)
    (cs : CallSite) (c : Contract) (g : Fn) (x : Nat) (hv : ¬ ViolationAt c g x) (n : Nat) :
    callRun fl s res cs c g x n = run c g x n := by …
```

Unfolded (prose):

```text
`ViolationAt c g x` means `c.req x = false ∨ (c.req x = true ∧ ∃ tr r, Halts c g x ⟨tr, .ret r⟩ ∧ c.ens x r = false)`.
```

- **Plain claim:** For every flag assignment `fl`, placement `s`, resolution `res`, call site `cs`, contract `c`, callee `g` (neither `Lowered g` nor `NoChecks g` assumed), argument `x` with `¬ ViolationAt c g x` (`Req x` holds and every normal return of `g` on `x` satisfies `Ens`) and fuel `n`: `callRun fl s res cs c g x n = run c g x n`.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: per-unit assertion policies scoped to the declaration or to a generic instance are documented for Ada 2012 (RM 6.1.1(19/3), 11.4.2(10.3/3)); no mechanized statement was found; stated here for a toy pipeline of per-crate steps.
- **Hypothesis ledger:**
  - `hv : ¬ ViolationAt c g x`: with a violation, an enabled check can change the observation. **tight** — counterexample `cex_callRun_violation`; witness class: `gEarly` at input `0` under `c1`, every flag on.
- **Depth:** shallow. Every inserted check passes wherever it is placed (`run_instr_eq_of_req_of_ensOnReturnsAt`, a fuel induction), and the wrapper is the identity (`instrObs_run_eq_of_req_of_ensOnReturnsAt`); case analysis on the pipeline.
- **Non-vacuity witness:** `gGood` on `5` under `c1` has no violation. (`nonvacuity_not_violation`)
- **Non-claims:**
  - Unobservability of the flags on such inputs relies on contract clauses being pure, total Boolean functions in the toy; where evaluating a passing clause can have side effects, allocate, diverge or raise, enabling checks can be observable without any violation (not modelled).
  - `callRun` is a toy pipeline of three per-crate steps (`compileInDefCrate`, `instantiateIn`, `callInCallerCrate`), each of which reads the flag of its own crate and no other; it is not derived from a compilation, monomorphization or linking semantics of any real toolchain. Where a real compiler resolves a flag test (`Resolution`) and where checks are placed (`Site`) are parameters, not findings, and callee-side checks in `callRun` always use the all-exits placement.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012, §6.1.1 paragraph 19/3 and §11.4.2 'Pragmas Assert and Assertion_Policy', paragraphs 10/3 and 10.3/3 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html, accessed 2026-11-21). 6.1.1(19/3): pre- and postcondition expressions are enabled if checks are required by the assertion policies 'in effect at the point of a corresponding aspect specification'. 11.4.2(10/3): policy Ignore 'requires that the assertion expression not be evaluated at these points, and the run-time checks not be performed'. 11.4.2(10.3/3): 'If a pragma Assertion_Policy applies to a generic_instantiation, then the pragma Assertion_Policy applies to the entire instance.'
- **Design question:** What happens when the defining, instantiating and calling crates use different flag settings?

#### R18. `cex_same_flags_detection_depends_on_placement` (counterexample)

```lean
-- lean/ToyContracts/Counterexamples.lean:327-331
theorem cex_same_flags_detection_depends_on_placement :
    flCallerOn cs1.callerCrate = true ∧ flCallerOn cs1.defCrate = false ∧
    ViolationAt c1 gEarly 0 ∧
    Detects flCallerOn .callerSide .atDefinition cs1 c1 gEarly 0 ∧
    ¬ Detects flCallerOn .calleeSide .atDefinition cs1 c1 gEarly 0 := …
```

- **Plain claim:** There is a call site, `cs1` (crate `0` calls a non-generic function defined in crate `1`), and a flag assignment, `flCallerOn` (crate `0` on, every other crate off), such that the violation of `gEarly` on `0` under `c1` is reported under caller-side placement and is not reported under callee-side placement, both with resolution at definition.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: per-unit assertion policies scoped to the declaration or to a generic instance are documented for Ada 2012 (RM 6.1.1(19/3), 11.4.2(10.3/3)); no mechanized statement was found; stated here for a toy pipeline of per-crate steps.
- **Hypothesis ledger:**
  - (no hypotheses)
- **Depth:** definitional. Evaluation of concrete runs.
- **Non-vacuity witness:** the stated instance is itself the witness.
- **Non-claims:**
  - One concrete instance; it is not a statement about every function, input or flag assignment.
  - `callRun` is a toy pipeline of three per-crate steps (`compileInDefCrate`, `instantiateIn`, `callInCallerCrate`), each of which reads the flag of its own crate and no other; it is not derived from a compilation, monomorphization or linking semantics of any real toolchain. Where a real compiler resolves a flag test (`Resolution`) and where checks are placed (`Site`) are parameters, not findings, and callee-side checks in `callRun` always use the all-exits placement.
  - Policies that check `requires` at the caller and `ensures` in the callee, or that check whenever either crate's flag is on, are not modelled; nor are indirect calls through function pointers or trait objects, or a generic callee instantiated in more than one crate.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012, §6.1.1 paragraph 19/3 and §11.4.2 'Pragmas Assert and Assertion_Policy', paragraphs 10/3 and 10.3/3 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html, accessed 2026-11-21). 6.1.1(19/3): pre- and postcondition expressions are enabled if checks are required by the assertion policies 'in effect at the point of a corresponding aspect specification'. 11.4.2(10/3): policy Ignore 'requires that the assertion expression not be evaluated at these points, and the run-time checks not be performed'. 11.4.2(10.3/3): 'If a pragma Assertion_Policy applies to a generic_instantiation, then the pragma Assertion_Policy applies to the entire instance.'
  - R. B. Findler and M. Felleisen, 'Contracts for Higher-Order Functions', ICFP 2002, pp. 48–59, DOI 10.1145/581478.581484: contracts monitored at module boundaries; cited for the distinction between the calling and the defining side of a contract.
  - Corpus package call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations (google/zerocopy branch reference at commit 95e95c2fbada69bc95437324bf4462759bd738a4): a toy model of call-site inlining, including a counterexample showing that a condition proved for an inlined callee need not establish the callee's contract from its own entry; cited as related work on caller-side versus callee-side reasoning, not repeated.
- **Design question:** What happens when the defining, instantiating and calling crates use different flag settings?

#### R19. `cex_calleeSide_atInstantiation_definingFlag_on_undetected` (counterexample)

```lean
-- lean/ToyContracts/Counterexamples.lean:340-346
theorem cex_calleeSide_atInstantiation_definingFlag_on_undetected :
    holder .calleeSide csGen = csGen.defCrate ∧
    flDefOn (holder .calleeSide csGen) = true ∧ flDefOn csGen.instCrate = false ∧
    ViolationAt c1 gEarly 0 ∧
    ¬ Detects flDefOn .calleeSide .atInstantiation csGen c1 gEarly 0 ∧
    Detects flDefOn .calleeSide .atDefinition csGen c1 gEarly 0 ∧
    Detects flDefOn .calleeSide .atInstantiation cs1 c1 gEarly 0 := …
```

- **Plain claim:** There is a call site, `csGen` (crate `0` calls a generic function defined in crate `1` and instantiated in crate `0`), and a flag assignment, `flDefOn` (crate `1` on, every other crate off), such that: the crate holding the callee-side check is the defining crate (`holder .calleeSide csGen = csGen.defCrate`), its flag is on, the flag of the instantiating crate `0` is off, and under callee-side placement (checks inserted by `instr .allExits`) with resolution at instantiation the violation of `gEarly` on `0` under `c1` is not reported; it is reported under resolution at definition, and for the non-generic call site `cs1` it is reported under resolution at instantiation.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: per-unit assertion policies scoped to the declaration or to a generic instance are documented for Ada 2012 (RM 6.1.1(19/3), 11.4.2(10.3/3)); no mechanized statement was found; stated here for a toy pipeline of per-crate steps.
- **Hypothesis ledger:**
  - (no hypotheses)
- **Depth:** definitional. Evaluation of concrete runs.
- **Non-vacuity witness:** the stated instance is itself the witness.
- **Non-claims:**
  - One concrete instance; it is not a statement about every function, input or flag assignment.
  - For a generic callee instantiated in a third crate, the governing crate under resolution at instantiation is that crate (`governingCrate_csGen3_atInstantiation`), and detection follows its flag (`detects_csGen3_follows_instCrate`: reported with crate `2`'s flag alone on; not reported with the calling and defining crates' flags on and crate `2`'s off). Ada 2012 11.4.2(10.3/3) attaches the policy of a generic instantiation to the instance; whether a given compiler resolves a flag test at definition or at instantiation is not asserted.
  - Policies that check `requires` at the caller and `ensures` in the callee, or that check whenever either crate's flag is on, are not modelled; nor are indirect calls through function pointers or trait objects, or a generic callee instantiated in more than one crate.
  - `callRun` is a toy pipeline of three per-crate steps (`compileInDefCrate`, `instantiateIn`, `callInCallerCrate`), each of which reads the flag of its own crate and no other; it is not derived from a compilation, monomorphization or linking semantics of any real toolchain. Where a real compiler resolves a flag test (`Resolution`) and where checks are placed (`Site`) are parameters, not findings, and callee-side checks in `callRun` always use the all-exits placement.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - Ada Reference Manual, ISO/IEC 8652:2012, §6.1.1 paragraph 19/3 and §11.4.2 'Pragmas Assert and Assertion_Policy', paragraphs 10/3 and 10.3/3 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html, accessed 2026-11-21). 6.1.1(19/3): pre- and postcondition expressions are enabled if checks are required by the assertion policies 'in effect at the point of a corresponding aspect specification'. 11.4.2(10/3): policy Ignore 'requires that the assertion expression not be evaluated at these points, and the run-time checks not be performed'. 11.4.2(10.3/3): 'If a pragma Assertion_Policy applies to a generic_instantiation, then the pragma Assertion_Policy applies to the entire instance.'
  - Corpus package monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets (google/zerocopy branch reference at commit 95e95c2fbada69bc95437324bf4462759bd738a4): a toy model of whole-program monomorphization in which generic bodies are instantiated by substitution; cited for instantiation of generic bodies, not repeated.
- **Design question:** Does callee-side placement by itself make the defining crate's flag decisive?

#### R20. `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst` (characterization)

```lean
-- lean/ToyContracts/Results.lean:255-258
theorem runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst (c : Contract)
    (g : Fn) (hg : Lowered g) (hnc : NoChecks g) (x r : Nat)
    (hk : CtfeConst .allExits .skipChecks c g x r) :
    RuntimeValue .allExits c g x r ↔ c.req x = true ∧ c.ens x r = true := by …
```

Explicit form, with `RuntimeValue` unfolded:

```lean
(∃ tr, Halts c (instr .allExits g) x ⟨tr, .ret r⟩) ↔ c.req x = true ∧ c.ens x r = true
```

- **Plain claim:** For every contract `c`, every function `g` with `Lowered g` and `NoChecks g` (both over every block, reachable or not; `NoChecks g` also over the prologue), every argument `x` and value `r`: if compile-time evaluation that skips checks, applied to the all-exits instrumentation, produces the constant `r` (`CtfeConst .allExits .skipChecks c g x r`), then the all-exits runtime-checked call returns `r` (`RuntimeValue .allExits c g x r`) iff `Req x` and `Ens x r` both hold.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: that evaluation without checks can produce values the checked run rejects is folklore (C++ proposals P1774R8 §4.6 and P2900R14 §3.5.12 discuss assumptions and contract assertions during constant evaluation); no mechanized statement of this condition was found.
- **Hypothesis ledger:**
  - `hg : Lowered g`: no block of `g`, reachable or not, ends in the source form `tryQ` of `?`; otherwise a `?` exit returns unchecked at run time. **tight** — counterexample `cex_runtimeValue_lowered`; witness class: `gTry` at input `1` under `c1`.
  - `hnc : NoChecks g`: no contract statement in the prologue or in any block of `g`, reachable or not; a contract statement already in `g` can fail at run time while check-skipping evaluation deletes it. **tight** — counterexample `cex_runtimeValue_noChecks`; witness class: `gInt` at input `3` under `cThree`.
  - `hk : CtfeConst .allExits .skipChecks c g x r`: ties `r` to the value that the erasure `erase (instr .allExits g)` returns on `x`, which is the value `g` returns on `x` when `NoChecks g` holds (`erase_instr_eq_of_noChecks`); without it the runtime value need not be `r`. **tight** — counterexample `cex_runtimeValue_ctfeConst`; witness class: `gGood` at input `5` and value `4` under `c1`.
- **Depth:** shallow. From `run_instr_allExits_eq_instrObs_of_lowered` and `erase_instr_eq_of_noChecks`; no determinism argument is needed.
- **Non-vacuity witness:** `gEarly` on `0` (constant `7`) and on `5` (constant `5`). (`nonvacuity_ctfe`)
- **Non-claims:**
  - `CtfeConst` and `RuntimeValue` take a `Placement` parameter and the theorem is stated for `.allExits`. With `.tailOnly` in both places the equivalence fails at one proved instance (`cex_runtimeValue_tailOnly`: for `gEarly` on `0` under `c1`, check-skipping evaluation of the tail-only instrumentation gives `7`, the tail-only checked call returns `7`, and `Ens 0 7` fails).
  - Compile-time evaluation is a toy parameter (`CtfeMode`); nothing is asserted about which mode any compiler implements, and `CtfeConst` ignores events.
  - Concrete reference instances: `cex_ctfeSkip_requires_violation` (the `Req x` false case) and `cex_ctfeSkip_ensures_violation` (the `Ens x r` false case).
  - Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
  - `Lowered g` and `NoChecks g` inspect every block of `g`, reachable or not (`NoChecks g` also the prologue); the natural weakenings that restrict them to blocks reachable from the entry are not established here.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - T. Doumler, 'Portable assumptions', WG21 P1774R8, 2022-06-14 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2022/p1774r8.pdf, accessed 2026-11-21), §4.6 'Behaviour of assumptions during constant evaluation': an assumption that would not evaluate to true during constant evaluation makes it implementation-defined whether the program is ill-formed, and an assumption that cannot be evaluated at compile time is ignored.
  - J. Berne, T. Doumler, A. Krzemieński et al., 'Contracts for C++', WG21 P2900R14, 2025-02-13 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p2900r14.pdf, accessed 2026-11-21): one non-checking evaluation semantic (ignore) and three checking ones (observe, enforce, quick-enforce); §3.5.12 'Constant Evaluation' says that under ignore 'Nothing happens during constant evaluation', and that the semantic of a manifestly constant-evaluated contract assertion is chosen in an implementation-defined manner. The toy's `skipChecks` and `evalChecks` correspond loosely to ignore and to a checking semantic.
  - Rust contracts experiment: tracking issue https://github.com/rust-lang/rust/issues/128044 ('Tracking Issue for Contracts', open), cited as context in prose and not as a specification. At rust-lang/rust commit c7d5ba59d8e11ee2e2204b173458eec4cb41c973, library/core/src/contracts.rs does not document check placement, the enabling flag or compile-time evaluation.
- **Design question:** What happens when evaluation at compile time skips checks?

#### R21. `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst` (characterization)

```lean
-- lean/ToyContracts/Results.lean:274-277
theorem runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst
    (c : Contract) (g : Fn) (hg : Lowered g) (hnc : NoChecks g) (x r : Nat)
    (hreq : c.req x = true) (hk : CtfeConst .allExits .skipChecks c g x r) :
    RuntimeValue .allExits c g x r ↔ StaticObligationAt c g x := by …
```

Explicit form, with `RuntimeValue` and `StaticObligationAt` unfolded:

```lean
(∃ tr, Halts c (instr .allExits g) x ⟨tr, .ret r⟩) ↔
  (c.req x = true → ∀ tr' r', Halts c g x ⟨tr', .ret r'⟩ → c.ens x r' = true)
```

- **Plain claim:** For every contract `c`, every function `g` with `Lowered g` and `NoChecks g` (both over every block, reachable or not; `NoChecks g` also over the prologue), every argument `x` with `Req x` and every value `r`: if compile-time evaluation that skips checks, applied to the all-exits instrumentation, produces the constant `r` (`CtfeConst .allExits .skipChecks c g x r`), then the all-exits runtime-checked call returns `r` (`RuntimeValue .allExits c g x r`) iff the static obligation holds at `x` (`StaticObligationAt c g x`).
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: that evaluation without checks can produce values the checked run rejects is folklore (C++ proposals P1774R8 §4.6 and P2900R14 §3.5.12 discuss assumptions and contract assertions during constant evaluation); no mechanized statement of this condition was found.
- **Hypothesis ledger:**
  - `hg : Lowered g`: no block of `g`, reachable or not, ends in the source form `tryQ` of `?`; as for the previous characterization. **tight** — counterexample `cex_runtimeValue_obl_lowered`; witness class: `gTry` at input `1` under `c1`.
  - `hnc : NoChecks g`: no contract statement in the prologue or in any block of `g`, reachable or not; as for the previous characterization. **tight** — counterexample `cex_runtimeValue_obl_noChecks`; witness class: `gInt` at input `3` under `cThree`.
  - `hreq : c.req x = true`: off `Req` the static obligation holds vacuously while the runtime call fails its `requires` check. **tight** — counterexample `cex_runtimeValue_obl_req`; witness class: `gEarly` at input `100` under `c1`.
  - `hk : CtfeConst .allExits .skipChecks c g x r`: ties `r` to the value that the erasure `erase (instr .allExits g)` returns on `x`, which is the value `g` returns on `x` when `NoChecks g` holds. **tight** — counterexample `cex_runtimeValue_obl_ctfeConst`; witness class: `gGood` at input `5` and value `4` under `c1`.
- **Depth:** shallow. From `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst` and determinism of halting runs (`halts_unique`, from fuel monotonicity `run_mono`), which identifies every normal return of `g` on `x` with `r`.
- **Non-vacuity witness:** `gEarly` on `0` (constant `7`). (`nonvacuity_ctfe_req`)
- **Non-claims:**
  - The equivalence between an existential statement (`RuntimeValue`: some checked return of `r`) and a universal one (`StaticObligationAt`: every normal return satisfies `Ens`) relies on determinism of `run` (`halts_unique`); for a nondeterministic semantics it is not established.
  - There is an input violating `Req` (`gEarly` on `100` under `c1`) at which the equivalence fails (`cex_runtimeValue_obl_req`): the static obligation holds vacuously there, but the runtime call fails its `requires` check.
  - `CtfeConst` and `RuntimeValue` take a `Placement` parameter and the theorem is stated for `.allExits`. With `.tailOnly` in both places the equivalence fails at one proved instance (`cex_runtimeValue_obl_tailOnly`: for `gEarly` on `0` under `c1`, `Req 0` holds, check-skipping evaluation of the tail-only instrumentation gives `7`, the tail-only checked call returns `7`, and the static obligation at `0` fails).
  - Compile-time evaluation is a toy parameter (`CtfeMode`); nothing is asserted about which mode any compiler implements, and `CtfeConst` ignores events.
  - Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
  - `Lowered g` and `NoChecks g` inspect every block of `g`, reachable or not (`NoChecks g` also the prologue); the natural weakenings that restrict them to blocks reachable from the entry are not established here.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - T. Doumler, 'Portable assumptions', WG21 P1774R8, 2022-06-14 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2022/p1774r8.pdf, accessed 2026-11-21), §4.6 'Behaviour of assumptions during constant evaluation': an assumption that would not evaluate to true during constant evaluation makes it implementation-defined whether the program is ill-formed, and an assumption that cannot be evaluated at compile time is ignored.
  - J. Berne, T. Doumler, A. Krzemieński et al., 'Contracts for C++', WG21 P2900R14, 2025-02-13 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p2900r14.pdf, accessed 2026-11-21): one non-checking evaluation semantic (ignore) and three checking ones (observe, enforce, quick-enforce); §3.5.12 'Constant Evaluation' says that under ignore 'Nothing happens during constant evaluation', and that the semantic of a manifestly constant-evaluated contract assertion is chosen in an implementation-defined manner. The toy's `skipChecks` and `evalChecks` correspond loosely to ignore and to a checking semantic.
  - Rust contracts experiment: tracking issue https://github.com/rust-lang/rust/issues/128044 ('Tracking Issue for Contracts', open), cited as context in prose and not as a specification. At rust-lang/rust commit c7d5ba59d8e11ee2e2204b173458eec4cb41c973, library/core/src/contracts.rs does not document check placement, the enabling flag or compile-time evaluation.
- **Design question:** What happens when evaluation at compile time skips checks?

#### R22. `cex_ctfeSkip_requires_violation` (counterexample)

```lean
-- lean/ToyContracts/Counterexamples.lean:357-362
theorem cex_ctfeSkip_requires_violation :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 100 = false ∧
    CtfeConst .allExits .skipChecks c1 gEarly 100 100 ∧ StaticObligationAt c1 gEarly 100 ∧
    (∀ n, run c1 (instr .allExits gEarly) 100 n = ⟨[], .checkFail .pre⟩) ∧
    (∀ r, ¬ RuntimeValue .allExits c1 gEarly 100 r) ∧
    (∀ r, ¬ CtfeConst .allExits .evalChecks c1 gEarly 100 r) := …
```

- **Plain claim:** There is a lowered function without contract statements (in its prologue or in any block, reachable or not), `gEarly`, and an input, `100`, violating `Req` under `c1`, such that: check-skipping compile-time evaluation of the all-exits instrumentation yields the constant `100`; the static obligation at `100` holds vacuously; the all-exits runtime-checked call halts with a `requires` failure and no events at every fuel and returns no value at all (`∀ r, ¬ RuntimeValue .allExits c1 gEarly 100 r`); and check-evaluating compile-time evaluation of the all-exits instrumentation yields no constant at all.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: that evaluation without checks can produce values the checked run rejects is folklore (C++ proposals P1774R8 §4.6 and P2900R14 §3.5.12 discuss assumptions and contract assertions during constant evaluation); no mechanized statement of this condition was found.
- **Hypothesis ledger:**
  - (no hypotheses)
- **Depth:** definitional. Evaluation of concrete runs.
- **Non-vacuity witness:** the stated instance is itself the witness.
- **Non-claims:**
  - Reference instance of the `Req x` false case of `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`, and of the tightness of `Req x` in `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`.
  - One concrete instance; it is not a statement about every function, input or flag assignment.
  - Compile-time evaluation is a toy parameter (`CtfeMode`); nothing is asserted about which mode any compiler implements, and `CtfeConst` ignores events.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - T. Doumler, 'Portable assumptions', WG21 P1774R8, 2022-06-14 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2022/p1774r8.pdf, accessed 2026-11-21), §4.6 'Behaviour of assumptions during constant evaluation': an assumption that would not evaluate to true during constant evaluation makes it implementation-defined whether the program is ill-formed, and an assumption that cannot be evaluated at compile time is ignored.
  - J. Berne, T. Doumler, A. Krzemieński et al., 'Contracts for C++', WG21 P2900R14, 2025-02-13 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p2900r14.pdf, accessed 2026-11-21): one non-checking evaluation semantic (ignore) and three checking ones (observe, enforce, quick-enforce); §3.5.12 'Constant Evaluation' says that under ignore 'Nothing happens during constant evaluation', and that the semantic of a manifestly constant-evaluated contract assertion is chosen in an implementation-defined manner. The toy's `skipChecks` and `evalChecks` correspond loosely to ignore and to a checking semantic.
  - Rust contracts experiment: tracking issue https://github.com/rust-lang/rust/issues/128044 ('Tracking Issue for Contracts', open), cited as context in prose and not as a specification. At rust-lang/rust commit c7d5ba59d8e11ee2e2204b173458eec4cb41c973, library/core/src/contracts.rs does not document check placement, the enabling flag or compile-time evaluation.
- **Design question:** What happens when evaluation at compile time skips checks?

#### R23. `cex_ctfeSkip_ensures_violation` (counterexample)

```lean
-- lean/ToyContracts/Counterexamples.lean:371-376
theorem cex_ctfeSkip_ensures_violation :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 0 = true ∧ c1.ens 0 7 = false ∧
    CtfeConst .allExits .skipChecks c1 gEarly 0 7 ∧
    Halts c1 (instr .allExits gEarly) 0 ⟨[], .checkFail .post⟩ ∧
    (∀ r, ¬ RuntimeValue .allExits c1 gEarly 0 r) ∧
    (∀ r, ¬ CtfeConst .allExits .evalChecks c1 gEarly 0 r) := by …
```

- **Plain claim:** There is a lowered function without contract statements (in its prologue or in any block, reachable or not), `gEarly`, and an input, `0`, satisfying `Req` under `c1`, such that: check-skipping compile-time evaluation of the all-exits instrumentation yields the constant `7`; `Ens 0 7` fails; the all-exits runtime-checked call halts with an `ensures` failure and no events and returns no value at all (`∀ r, ¬ RuntimeValue .allExits c1 gEarly 0 r`); and check-evaluating compile-time evaluation of the all-exits instrumentation yields no constant at all.
- **Basis:** execution (Lean kernel check).
- **Tier:** T1. T1: that evaluation without checks can produce values the checked run rejects is folklore (C++ proposals P1774R8 §4.6 and P2900R14 §3.5.12 discuss assumptions and contract assertions during constant evaluation); no mechanized statement of this condition was found.
- **Hypothesis ledger:**
  - (no hypotheses)
- **Depth:** definitional. Evaluation of concrete runs.
- **Non-vacuity witness:** the stated instance is itself the witness.
- **Non-claims:**
  - Reference instance of the `Ens x r` false case of `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`.
  - One concrete instance; it is not a statement about every function, input or flag assignment.
  - Compile-time evaluation is a toy parameter (`CtfeMode`); nothing is asserted about which mode any compiler implements, and `CtfeConst` ignores events.
  - Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++.
- **Prior art:**
  - T. Doumler, 'Portable assumptions', WG21 P1774R8, 2022-06-14 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2022/p1774r8.pdf, accessed 2026-11-21), §4.6 'Behaviour of assumptions during constant evaluation': an assumption that would not evaluate to true during constant evaluation makes it implementation-defined whether the program is ill-formed, and an assumption that cannot be evaluated at compile time is ignored.
  - J. Berne, T. Doumler, A. Krzemieński et al., 'Contracts for C++', WG21 P2900R14, 2025-02-13 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p2900r14.pdf, accessed 2026-11-21): one non-checking evaluation semantic (ignore) and three checking ones (observe, enforce, quick-enforce); §3.5.12 'Constant Evaluation' says that under ignore 'Nothing happens during constant evaluation', and that the semantic of a manifestly constant-evaluated contract assertion is chosen in an implementation-defined manner. The toy's `skipChecks` and `evalChecks` correspond loosely to ignore and to a checking semantic.
  - Rust contracts experiment: tracking issue https://github.com/rust-lang/rust/issues/128044 ('Tracking Issue for Contracts', open), cited as context in prose and not as a specification. At rust-lang/rust commit c7d5ba59d8e11ee2e2204b173458eec4cb41c973, library/core/src/contracts.rs does not document check placement, the enabling flag or compile-time evaluation.
- **Design question:** What happens when evaluation at compile time skips checks?

### 3. Declarations cited by name

#### 3.1 Counterexamples and closed-form facts used by them (`lean/ToyContracts/Counterexamples.lean`)

`cex_req_and_ens_premise`: Tightness of the premise of `req_and_ens_of_halts_ret_instr_allExits_lower`: for `gEarly`, input `0` and value `7` under `c1`, the instrumented lowered function does not halt with a return of `7`, and `Req 0 ∧ Ens 0 7` fails.

```lean
-- lean/ToyContracts/Counterexamples.lean:17-19
theorem cex_req_and_ens_premise :
    ¬ Halts c1 (instr .allExits (lower gEarly)) 0 ⟨[], .ret 7⟩ ∧
    ¬ (c1.req 0 = true ∧ c1.ens 0 7 = true) := by …
```

`cex_lower_jumpsInRange`: Tightness of `JumpsInRange` in `halts_lower_iff_of_jumpsInRange` (out-of-range jump target): `fOut` jumps to the missing index `3`; `lower fOut` halts on `0` with a return of `5` (index `3` is now the fresh block of the `?` in block `1`), while `fOut` does not.

```lean
-- lean/ToyContracts/Counterexamples.lean:63-64
theorem cex_lower_jumpsInRange :
    ¬ JumpsInRange fOut ∧ Halts c1 (lower fOut) 0 ⟨[], .ret 5⟩ ∧ ¬ Halts c1 fOut 0 ⟨[], .ret 5⟩ := by …
```

`cex_lower_entry_out_of_range`: Tightness of `JumpsInRange` in `halts_lower_iff_of_jumpsInRange` (out-of-range entry, every jump target in range): `lower fBadEntry` halts on `0` with a return of `5`, while `fBadEntry` does not.

```lean
-- lean/ToyContracts/Counterexamples.lean:72-75
theorem cex_lower_entry_out_of_range :
    ¬ JumpsInRange fBadEntry ∧
    fBadEntry.blocks.all (fun blk => blk.term.targets.all (· < fBadEntry.blocks.length)) = true ∧
    Halts c1 (lower fBadEntry) 0 ⟨[], .ret 5⟩ ∧ ¬ Halts c1 fBadEntry 0 ⟨[], .ret 5⟩ := by …
```

`cex_erase_instr_noChecks`: Tightness of `NoChecks` in `erase_instr_eq_of_noChecks`.

```lean
-- lean/ToyContracts/Counterexamples.lean:82
theorem cex_erase_instr_noChecks : ¬ NoChecks gInt ∧ erase (instr .allExits gInt) ≠ gInt := by …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:85-86
theorem runEqAt_erase_instr_gTry_1 (c : Contract) (hr : c.req 1 = true) :
    RunEqAt c (erase (instr .allExits gTry)) (instr .allExits gTry) 1 := by …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:93-94
theorem runEqAt_instr_gTry_1 (c : Contract) (hr : c.req 1 = true) :
    RunEqAt c (instr .allExits gTry) gTry 1 := by …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:100
theorem not_ensOnReturnsAt_gTry_1 : ¬ EnsOnReturnsAt cOne gTry 1 := by …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:105-106
theorem runEqAt_erase_instr_gInt_ne : ¬ RunEqAt cThree (erase (instr .allExits gInt))
    (instr .allExits gInt) 3 := by …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:109
theorem ensOnReturnsAt_gInt_3 : EnsOnReturnsAt cThree gInt 3 := by …
```

`cex_instrSelf_lowered`: Tightness of `Lowered` in `instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`: for `gTry` on `1` under `cOne`, the all-exits instrumentation is fuel-exactly identical to `gTry` (the `?` exit is unchecked) while `Ens 1 9` fails at a normal return.

```lean
-- lean/ToyContracts/Counterexamples.lean:117-120
theorem cex_instrSelf_lowered :
    ¬ Lowered gTry ∧ cOne.req 1 = true ∧
    ¬ ((RunEqAt cOne (instr .allExits gTry) gTry 1 ↔ EnsOnReturnsAt cOne gTry 1) ∧
       (HaltsEqAt cOne (instr .allExits gTry) gTry 1 ↔ EnsOnReturnsAt cOne gTry 1)) := by …
```

`cex_instrSelf_req`: Tightness of `Req x` in `instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`: for `gGood` on `100` (where `Req` fails) every normal return satisfies `Ens`, yet the instrumentation and `gGood` differ at fuel `0`.

```lean
-- lean/ToyContracts/Counterexamples.lean:127-130
theorem cex_instrSelf_req :
    Lowered gGood ∧ c1.req 100 = false ∧
    ¬ ((RunEqAt c1 (instr .allExits gGood) gGood 100 ↔ EnsOnReturnsAt c1 gGood 100) ∧
       (HaltsEqAt c1 (instr .allExits gGood) gGood 100 ↔ EnsOnReturnsAt c1 gGood 100)) := by …
```

`cex_erasure_lowered`: Tightness of `Lowered` in `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`: for `gTry` on `1` under `cOne`, erasure is fuel-exactly identical to the all-exits instrumentation (the `?` exit is unchecked) while `Ens 1 9` fails at a normal return.

```lean
-- lean/ToyContracts/Counterexamples.lean:138-143
theorem cex_erasure_lowered :
    ¬ Lowered gTry ∧ NoChecks gTry ∧ cOne.req 1 = true ∧
    ¬ ((RunEqAt cOne (erase (instr .allExits gTry)) (instr .allExits gTry) 1 ↔
          EnsOnReturnsAt cOne gTry 1) ∧
       (HaltsEqAt cOne (erase (instr .allExits gTry)) (instr .allExits gTry) 1 ↔
          EnsOnReturnsAt cOne gTry 1)) := by …
```

`cex_erasure_noChecks`: Tightness of `NoChecks` in `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`: `gInt` already contains a failing `ensures` check; on `3` under `cThree` it never returns (so the right-hand side holds vacuously), while erasure returns `3` and instrumentation fails.

```lean
-- lean/ToyContracts/Counterexamples.lean:150-155
theorem cex_erasure_noChecks :
    Lowered gInt ∧ ¬ NoChecks gInt ∧ cThree.req 3 = true ∧
    ¬ ((RunEqAt cThree (erase (instr .allExits gInt)) (instr .allExits gInt) 3 ↔
          EnsOnReturnsAt cThree gInt 3) ∧
       (HaltsEqAt cThree (erase (instr .allExits gInt)) (instr .allExits gInt) 3 ↔
          EnsOnReturnsAt cThree gInt 3)) := by …
```

`cex_erasure_req`: Tightness of `Req x` in `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`: for `gGood` on `100` (where `Req` fails) every normal return satisfies `Ens`, yet erasure and instrumentation differ.

```lean
-- lean/ToyContracts/Counterexamples.lean:162-167
theorem cex_erasure_req :
    Lowered gGood ∧ NoChecks gGood ∧ c1.req 100 = false ∧
    ¬ ((RunEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 100 ↔
          EnsOnReturnsAt c1 gGood 100) ∧
       (HaltsEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 100 ↔
          EnsOnReturnsAt c1 gGood 100)) := by …
```

`cex_erasure_tailOnly`: With tail-only placement the forward direction of `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req` fails: for `gEarly` on `0` under `c1` (lowered, without contract statements, `Req 0` holds), the erasure of the tail-only instrumentation is fuel-exactly identical to it, while the early return `7` violates `Ens`.

```lean
-- lean/ToyContracts/Counterexamples.lean:175-178
theorem cex_erasure_tailOnly :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 0 = true ∧
    RunEqAt c1 (erase (instr .tailOnly gEarly)) (instr .tailOnly gEarly) 0 ∧
    ¬ EnsOnReturnsAt c1 gEarly 0 := by …
```

`cex_erasure_global_lowered`: Tightness of `Lowered` in `erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks`: `gTry` under `cOne` (whose `Req` admits exactly the input `1`).

```lean
-- lean/ToyContracts/Counterexamples.lean:185-192
theorem cex_erasure_global_lowered :
    ¬ Lowered gTry ∧ NoChecks gTry ∧
    ¬ (((∀ x, cOne.req x = true →
            RunEqAt cOne (erase (instr .allExits gTry)) (instr .allExits gTry) x) ↔
          StaticObligation cOne gTry) ∧
       ((∀ x, cOne.req x = true →
            HaltsEqAt cOne (erase (instr .allExits gTry)) (instr .allExits gTry) x) ↔
          StaticObligation cOne gTry)) := by …
```

`cex_erasure_global_noChecks`: Tightness of `NoChecks` in `erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks`: `gInt` under `cThree` (whose `Req` admits exactly the input `3`).

```lean
-- lean/ToyContracts/Counterexamples.lean:205-212
theorem cex_erasure_global_noChecks :
    Lowered gInt ∧ ¬ NoChecks gInt ∧
    ¬ (((∀ x, cThree.req x = true →
            RunEqAt cThree (erase (instr .allExits gInt)) (instr .allExits gInt) x) ↔
          StaticObligation cThree gInt) ∧
       ((∀ x, cThree.req x = true →
            HaltsEqAt cThree (erase (instr .allExits gInt)) (instr .allExits gInt) x) ↔
          StaticObligation cThree gInt)) := by …
```

`cex_not_haltsEq_req_true`: Tightness of `Req x = false` in `not_haltsEqAt_erase_instr_of_req_false`: on `5`, where `Req` holds, the conclusion fails for `gGood` (erasure and instrumentation have the same halting observations, and the instrumentation does not end with a `requires` failure).

```lean
-- lean/ToyContracts/Counterexamples.lean:224-229
theorem cex_not_haltsEq_req_true :
    c1.req 5 = true ∧
    ¬ ((∀ n, run c1 (instr .allExits gGood) 5 n = ⟨[], .checkFail .pre⟩) ∧
       NoChecks (erase (instr .allExits gGood)) ∧
       (∀ n k, (run c1 (erase (instr .allExits gGood)) 5 n).outcome ≠ .checkFail k) ∧
       ¬ HaltsEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 5) := …
```

`cex_ubRefines_noChecks`: Tightness of `NoChecks` in `instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`: `gInt` on `3` under `cThree`.

```lean
-- lean/ToyContracts/Counterexamples.lean:235-237
theorem cex_ubRefines_noChecks :
    ¬ NoChecks gInt ∧ StaticObligationAt cThree gInt 3 ∧
    ¬ UBRefinesAt cThree (instr .allExits gInt) (assumeErase (instr .allExits gInt)) 3 := by …
```

`cex_ubRefines_obligation`: Tightness of the static obligation in `instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`: `gEarly` on `0`.

```lean
-- lean/ToyContracts/Counterexamples.lean:245-247
theorem cex_ubRefines_obligation :
    NoChecks gEarly ∧ ¬ StaticObligationAt c1 gEarly 0 ∧
    ¬ UBRefinesAt c1 (instr .allExits gEarly) (assumeErase (instr .allExits gEarly)) 0 := …
```

`cex_not_ubRefines_req_true`: Tightness of `Req x = false` in `not_assumeErase_ubRefinesAt_instr_of_req_false`: on `5`, where `Req` holds, the conclusion fails for `gGood` (the assume-erased `gGood` UB-refines the checked one, and neither run is UB or a `requires` failure).

```lean
-- lean/ToyContracts/Counterexamples.lean:253-258
theorem cex_not_ubRefines_req_true :
    c1.req 5 = true ∧
    UBRefinesAt c1 (assumeErase (instr .allExits gGood)) (instr .allExits gGood) 5 ∧
    ¬ ((∀ n, run c1 (assumeErase (instr .allExits gGood)) 5 n = ⟨[], .ub⟩) ∧
       (∀ n, run c1 (instr .allExits gGood) 5 n = ⟨[], .checkFail .pre⟩) ∧
       ¬ UBRefinesAt c1 (assumeErase (instr .allExits gGood)) (instr .allExits gGood) 5) := by …
```

`cex_callRun_lowered`: Tightness of `Lowered` in `callRun_eq_ite_governingFlag_of_lowered`: callee-side placement with every flag on, for the unlowered `gTry` on `1` under `cOne`, at fuel `1`.

```lean
-- lean/ToyContracts/Counterexamples.lean:272-276
theorem cex_callRun_lowered :
    ¬ Lowered gTry ∧
    callRun (fun _ => true) .calleeSide .atDefinition cs1 cOne gTry 1 1 ≠
      (if (fun _ => true) (governingCrate .calleeSide .atDefinition cs1)
        then instrObs cOne 1 (run cOne gTry 1 1) else run cOne gTry 1 1) := by …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:279-280
theorem not_detects_gTry_1 :
    ¬ Detects (fun _ => true) .calleeSide .atDefinition cs1 cOne gTry 1 := by …
```

`cex_detects_lowered`: Tightness of `Lowered` in `detects_iff_governingFlag_of_lowered_of_noChecks_of_violation`: `gTry` on `1` under `cOne` violates `Ens` through `?`; with every flag on, callee-side placement reports nothing.

```lean
-- lean/ToyContracts/Counterexamples.lean:294-297
theorem cex_detects_lowered :
    ¬ Lowered gTry ∧ NoChecks gTry ∧ ViolationAt cOne gTry 1 ∧
    ¬ (Detects (fun _ => true) .calleeSide .atDefinition cs1 cOne gTry 1 ↔
        (fun _ => true) (governingCrate .calleeSide .atDefinition cs1) = true) := …
```

`cex_detects_noChecks`: Tightness of `NoChecks` in `detects_iff_governingFlag_of_lowered_of_noChecks_of_violation`: `gIntReq` contains its own `requires` check; on `100` (where `Req` fails) a failed check is reported with every flag off.

```lean
-- lean/ToyContracts/Counterexamples.lean:304-307
theorem cex_detects_noChecks :
    Lowered gIntReq ∧ ¬ NoChecks gIntReq ∧ ViolationAt c1 gIntReq 100 ∧
    ¬ (Detects (fun _ => false) .calleeSide .atDefinition cs1 c1 gIntReq 100 ↔
        (fun _ => false) (governingCrate .calleeSide .atDefinition cs1) = true) := …
```

`cex_detects_violation`: Tightness of `ViolationAt` in `detects_iff_governingFlag_of_lowered_of_noChecks_of_violation`: `gGood` on `5` has no violation; with every flag on nothing is reported.

```lean
-- lean/ToyContracts/Counterexamples.lean:312-315
theorem cex_detects_violation :
    Lowered gGood ∧ NoChecks gGood ∧ ¬ ViolationAt c1 gGood 5 ∧
    ¬ (Detects (fun _ => true) .calleeSide .atDefinition cs1 c1 gGood 5 ↔
        (fun _ => true) (governingCrate .calleeSide .atDefinition cs1) = true) := …
```

`cex_callRun_violation`: Tightness of `¬ ViolationAt` in `callRun_eq_run_of_not_violation`: `gEarly` on `0`.

```lean
-- lean/ToyContracts/Counterexamples.lean:319-321
theorem cex_callRun_violation :
    ViolationAt c1 gEarly 0 ∧
    callRun (fun _ => true) .calleeSide .atDefinition cs1 c1 gEarly 0 2 ≠ run c1 gEarly 0 2 := …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:384
theorem ctfeConst_skip_gTry_1 : CtfeConst .allExits .skipChecks c1 gTry 1 9 := …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:386
theorem runtimeValue_gTry_1 : RuntimeValue .allExits c1 gTry 1 9 := …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:389
theorem not_runtimeValue_gInt_3 : ¬ RuntimeValue .allExits cThree gInt 3 3 := by …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:394
theorem not_runtimeValue_gGood_5_4 : ¬ RuntimeValue .allExits c1 gGood 5 4 := by …
```

```lean
-- lean/ToyContracts/Counterexamples.lean:399
theorem not_ctfeConst_skip_gGood_5_4 : ¬ CtfeConst .allExits .skipChecks c1 gGood 5 4 := by …
```

`cex_runtimeValue_lowered`: Tightness of `Lowered` in `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`: `gTry` on `1` returns `9` through the unchecked `?` at run time although `Ens 1 9` fails.

```lean
-- lean/ToyContracts/Counterexamples.lean:406-408
theorem cex_runtimeValue_lowered :
    ¬ Lowered gTry ∧ NoChecks gTry ∧ CtfeConst .allExits .skipChecks c1 gTry 1 9 ∧
    ¬ (RuntimeValue .allExits c1 gTry 1 9 ↔ c1.req 1 = true ∧ c1.ens 1 9 = true) := …
```

`cex_runtimeValue_noChecks`: Tightness of `NoChecks` in `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`: `gInt` on `3` under `cThree`.

```lean
-- lean/ToyContracts/Counterexamples.lean:415-417
theorem cex_runtimeValue_noChecks :
    Lowered gInt ∧ ¬ NoChecks gInt ∧ CtfeConst .allExits .skipChecks cThree gInt 3 3 ∧
    ¬ (RuntimeValue .allExits cThree gInt 3 3 ↔ cThree.req 3 = true ∧ cThree.ens 3 3 = true) := …
```

`cex_runtimeValue_ctfeConst`: Tightness of the compile-time constant hypothesis in `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`: for `gGood` on `5` and the value `4` (which `gGood` does not return), the constant hypothesis fails, `Req 5` and `Ens 5 4` hold, but the runtime value is not `4`.

```lean
-- lean/ToyContracts/Counterexamples.lean:424-426
theorem cex_runtimeValue_ctfeConst :
    Lowered gGood ∧ NoChecks gGood ∧ ¬ CtfeConst .allExits .skipChecks c1 gGood 5 4 ∧
    ¬ (RuntimeValue .allExits c1 gGood 5 4 ↔ c1.req 5 = true ∧ c1.ens 5 4 = true) := …
```

`cex_runtimeValue_tailOnly`: The all-exits placement in `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst` cannot be replaced by tail-only placement: for `gEarly` on `0`, check-skipping compile-time evaluation of the tail-only instrumentation gives `7`, the tail-only runtime-checked call returns `7`, and `Ens 0 7` fails.

```lean
-- lean/ToyContracts/Counterexamples.lean:434-436
theorem cex_runtimeValue_tailOnly :
    Lowered gEarly ∧ NoChecks gEarly ∧ CtfeConst .tailOnly .skipChecks c1 gEarly 0 7 ∧
    ¬ (RuntimeValue .tailOnly c1 gEarly 0 7 ↔ c1.req 0 = true ∧ c1.ens 0 7 = true) := …
```

`cex_runtimeValue_obl_lowered`: Tightness of `Lowered` in `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`.

```lean
-- lean/ToyContracts/Counterexamples.lean:442-445
theorem cex_runtimeValue_obl_lowered :
    ¬ Lowered gTry ∧ NoChecks gTry ∧ c1.req 1 = true ∧
    CtfeConst .allExits .skipChecks c1 gTry 1 9 ∧
    ¬ (RuntimeValue .allExits c1 gTry 1 9 ↔ StaticObligationAt c1 gTry 1) := by …
```

`cex_runtimeValue_obl_noChecks`: Tightness of `NoChecks` in `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`.

```lean
-- lean/ToyContracts/Counterexamples.lean:452-455
theorem cex_runtimeValue_obl_noChecks :
    Lowered gInt ∧ ¬ NoChecks gInt ∧ cThree.req 3 = true ∧
    CtfeConst .allExits .skipChecks cThree gInt 3 3 ∧
    ¬ (RuntimeValue .allExits cThree gInt 3 3 ↔ StaticObligationAt cThree gInt 3) := …
```

`cex_runtimeValue_obl_req`: Tightness of `Req x` in `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst` (without `Req x`, the static obligation at `x` is not equivalent to the runtime value): `gEarly` on `100`.

```lean
-- lean/ToyContracts/Counterexamples.lean:462-465
theorem cex_runtimeValue_obl_req :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 100 = false ∧
    CtfeConst .allExits .skipChecks c1 gEarly 100 100 ∧
    ¬ (RuntimeValue .allExits c1 gEarly 100 100 ↔ StaticObligationAt c1 gEarly 100) := …
```

`cex_runtimeValue_obl_ctfeConst`: Tightness of the compile-time constant hypothesis in `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`.

```lean
-- lean/ToyContracts/Counterexamples.lean:471-474
theorem cex_runtimeValue_obl_ctfeConst :
    Lowered gGood ∧ NoChecks gGood ∧ c1.req 5 = true ∧
    ¬ CtfeConst .allExits .skipChecks c1 gGood 5 4 ∧
    ¬ (RuntimeValue .allExits c1 gGood 5 4 ↔ StaticObligationAt c1 gGood 5) := …
```

`cex_runtimeValue_obl_tailOnly`: The all-exits placement in `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst` cannot be replaced by tail-only placement: for `gEarly` on `0` under `c1` (lowered, without contract statements, `Req 0` holds), check-skipping compile-time evaluation of the tail-only instrumentation gives `7`, the tail-only runtime-checked call returns `7`, and the static obligation at `0` fails.

```lean
-- lean/ToyContracts/Counterexamples.lean:484-487
theorem cex_runtimeValue_obl_tailOnly :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 0 = true ∧
    CtfeConst .tailOnly .skipChecks c1 gEarly 0 7 ∧
    ¬ (RuntimeValue .tailOnly c1 gEarly 0 7 ↔ StaticObligationAt c1 gEarly 0) := …
```

#### 3.2 Non-vacuity witnesses (`lean/ToyContracts/NonVacuity.lean`)

`nonvacuity_run_instr_allExits`: `run_instr_allExits_eq_instrObs_of_lowered`: `gEarly` (a tail return and an early return) is lowered.

```lean
-- lean/ToyContracts/NonVacuity.lean:11
theorem nonvacuity_run_instr_allExits : Lowered gEarly := by …
```

`nonvacuity_req_and_ens_lower`: `req_and_ens_of_halts_ret_instr_allExits_lower`: its hypothesis holds for `gTry` on `5` (returns `4`).

```lean
-- lean/ToyContracts/NonVacuity.lean:15-16
theorem nonvacuity_req_and_ens_lower :
    Halts c1 (instr .allExits (lower gTry)) 5 ⟨[], .ret 4⟩ := …
```

`nonvacuity_halts_lower`: `halts_lower_iff_of_jumpsInRange`: `gTry` has all jumps in range.

```lean
-- lean/ToyContracts/NonVacuity.lean:19
theorem nonvacuity_halts_lower : JumpsInRange gTry := by …
```

`nonvacuity_erase_instr`: `erase_instr_eq_of_noChecks`: `gEarly` has no contract statements.

```lean
-- lean/ToyContracts/NonVacuity.lean:22
theorem nonvacuity_erase_instr : NoChecks gEarly := by …
```

`nonvacuity_instrSelf`: `instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`: two instances satisfying all hypotheses, one where both sides hold (`gGood` on `5`) and one where both fail (`gEarly` on `0`), and one satisfying them although `NoChecks` fails (`gInt` on `3` under `cThree`).

```lean
-- lean/ToyContracts/NonVacuity.lean:27-30
theorem nonvacuity_instrSelf :
    (Lowered gGood ∧ c1.req 5 = true ∧ EnsOnReturnsAt c1 gGood 5) ∧
    (Lowered gEarly ∧ c1.req 0 = true ∧ ¬ EnsOnReturnsAt c1 gEarly 0) ∧
    (Lowered gInt ∧ ¬ NoChecks gInt ∧ cThree.req 3 = true) := …
```

`nonvacuity_erasure_pointwise`: `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`: two instances satisfying all hypotheses, one where both sides hold (`gGood` on `5`) and one where both fail (`gEarly` on `0`).

```lean
-- lean/ToyContracts/NonVacuity.lean:36-39
theorem nonvacuity_erasure_pointwise :
    (Lowered gGood ∧ NoChecks gGood ∧ c1.req 5 = true ∧ EnsOnReturnsAt c1 gGood 5 ∧
      RunEqAt c1 (erase (instr .allExits gGood)) (instr .allExits gGood) 5) ∧
    (Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 0 = true ∧ ¬ EnsOnReturnsAt c1 gEarly 0) := …
```

`nonvacuity_erasure_global`: `erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks`: `gGood` (obligation holds) and `gEarly` (obligation fails) both satisfy the hypotheses.

```lean
-- lean/ToyContracts/NonVacuity.lean:45-47
theorem nonvacuity_erasure_global :
    (Lowered gGood ∧ NoChecks gGood ∧ StaticObligation c1 gGood) ∧
    (Lowered gEarly ∧ NoChecks gEarly ∧ ¬ StaticObligation c1 gEarly) := …
```

`nonvacuity_req_false`: `not_haltsEqAt_erase_instr_of_req_false` and `not_assumeErase_ubRefinesAt_instr_of_req_false`: `Req 100` fails under `c1`.

```lean
-- lean/ToyContracts/NonVacuity.lean:53
theorem nonvacuity_req_false : c1.req 100 = false := …
```

`nonvacuity_assumeErase`: `run_assumeErase_eq_ite_req`: both branches occur (`Req 5` holds, `Req 100` fails).

```lean
-- lean/ToyContracts/NonVacuity.lean:56
theorem nonvacuity_assumeErase : c1.req 5 = true ∧ c1.req 100 = false := …
```

`nonvacuity_ubRefines`: `instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`: `gGood` on `5` (lowered), and the unlowered `gTry` on `5`.

```lean
-- lean/ToyContracts/NonVacuity.lean:60-62
theorem nonvacuity_ubRefines :
    (NoChecks gGood ∧ c1.req 5 = true ∧ StaticObligationAt c1 gGood 5) ∧
    (¬ Lowered gTry ∧ NoChecks gTry ∧ c1.req 5 = true ∧ StaticObligationAt c1 gTry 5) := by …
```

`nonvacuity_callRun`: `callRun_eq_ite_governingFlag_of_lowered`: `gEarly` is lowered.

```lean
-- lean/ToyContracts/NonVacuity.lean:69
theorem nonvacuity_callRun : Lowered gEarly := by …
```

`nonvacuity_detects`: `detects_iff_governingFlag_of_lowered_of_noChecks_of_violation`: `gEarly` on `0` (an `ensures` violation) and on `100` (a `requires` violation).

```lean
-- lean/ToyContracts/NonVacuity.lean:73-74
theorem nonvacuity_detects :
    Lowered gEarly ∧ NoChecks gEarly ∧ ViolationAt c1 gEarly 0 ∧ ViolationAt c1 gEarly 100 := …
```

`nonvacuity_not_violation`: `callRun_eq_run_of_not_violation`: `gGood` on `5`.

```lean
-- lean/ToyContracts/NonVacuity.lean:78
theorem nonvacuity_not_violation : ¬ ViolationAt c1 gGood 5 := …
```

`nonvacuity_ctfe`: `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`: `gEarly` on `0` (constant `7`) and on `5` (constant `5`).

```lean
-- lean/ToyContracts/NonVacuity.lean:82-84
theorem nonvacuity_ctfe :
    (Lowered gEarly ∧ NoChecks gEarly ∧ CtfeConst .allExits .skipChecks c1 gEarly 0 7) ∧
    CtfeConst .allExits .skipChecks c1 gEarly 5 5 := …
```

`nonvacuity_ctfe_req`: `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`: `gEarly` on `0`.

```lean
-- lean/ToyContracts/NonVacuity.lean:89-91
theorem nonvacuity_ctfe_req :
    Lowered gEarly ∧ NoChecks gEarly ∧ c1.req 0 = true ∧
    CtfeConst .allExits .skipChecks c1 gEarly 0 7 := …
```

#### 3.3 Auxiliary lemmas (`lean/ToyContracts/Lemmas.lean`, `lean/ToyContracts/Consequences.lean`)

`halts_iff_of_run_const`: Halting observations of a run that is `fuelOut` below fuel `k` and constant (and final) from fuel `k` on: exactly that constant.

```lean
-- lean/ToyContracts/Lemmas.lean:13-15
theorem halts_iff_of_run_const {c : Contract} {p : Fn} {x : Nat} (k : Nat) (o₀ : Obs)
    (hk : ∀ m, run c p x (m + k) = o₀) (hlt : ∀ n, n < k → (run c p x n).outcome = .fuelOut)
    (hfin : o₀.outcome ≠ .fuelOut) (o : Obs) : Halts c p x o ↔ o = o₀ := by …
```

`haltsEqAt_of_runEqAt`: Fuel-exact identity implies identity of halting observations.

```lean
-- lean/ToyContracts/Lemmas.lean:26-27
theorem haltsEqAt_of_runEqAt {c : Contract} {p q : Fn} {x : Nat} (h : RunEqAt c p q x) :
    HaltsEqAt c p q x := by …
```

`ubRefinesAt_of_forall_not_halts`: A target with no halting observation at `x` UB-refines every source at `x` (`UBRefinesAt` compares halting runs of the target only).

```lean
-- lean/ToyContracts/Lemmas.lean:35-36
theorem ubRefinesAt_of_forall_not_halts {c : Contract} {tgt : Fn} {x : Nat}
    (h : ∀ o, ¬ Halts c tgt x o) (src : Fn) : UBRefinesAt c tgt src x := …
```

```lean
-- lean/ToyContracts/Lemmas.lean:41-46
theorem execStmts_append (c : Contract) (x : Nat) (ss₁ ss₂ : List Stmt) (σ : Store)
    (ev : List Nat) :
    execStmts c x (ss₁ ++ ss₂) σ ev =
      match execStmts c x ss₁ σ ev with
      | .stop ev' o => .stop ev' o
      | .cont σ' ev' => execStmts c x ss₂ σ' ev' := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:57-59
theorem execStmts_stop_outcome {c : Contract} {x : Nat} {ss : List Stmt} {σ : Store}
    {ev ev' : List Nat} {o : Outcome} (h : execStmts c x ss σ ev = .stop ev' o) :
    (∃ k, o = .checkFail k) ∨ o = .ub := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:79-81
theorem wrapObs_of_execStmts_stop {c : Contract} {x : Nat} {ss : List Stmt} {σ : Store}
    {ev ev' : List Nat} {o : Outcome} (h : execStmts c x ss σ ev = .stop ev' o) :
    wrapObs c x ⟨ev', o⟩ = ⟨ev', o⟩ := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:84-86
theorem execStmts_no_stop_of_all {c : Contract} {x : Nat} {ss : List Stmt}
    (hnc : ss.all (fun s => !s.isContract) = true) (σ : Store) (ev : List Nat) :
    ∃ σ' ev', execStmts c x ss σ ev = .cont σ' ev' := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:98-101
theorem runFrom_no_checkFail_of_blocks {c : Contract} {f : Fn}
    (hb : f.blocks.all (fun blk => blk.stmts.all (fun s => !s.isContract)) = true)
    (x n b : Nat) (σ : Store) (ev : List Nat) (k : CheckKind) :
    (runFrom c f x n b σ ev).outcome ≠ .checkFail k := by …
```

`run_no_checkFail_of_noChecks`: A function without contract statements never ends with a failed check.

```lean
-- lean/ToyContracts/Lemmas.lean:122-123
theorem run_no_checkFail_of_noChecks {c : Contract} {f : Fn} (hnc : NoChecks f)
    (x n : Nat) (k : CheckKind) : (run c f x n).outcome ≠ .checkFail k := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:131-133
theorem runFrom_instr_allExits_eq_wrapObs (c : Contract) (g : Fn) (hg : Lowered g)
    (x n b : Nat) (σ : Store) (ev : List Nat) :
    runFrom c (instr .allExits g) x n b σ ev = wrapObs c x (runFrom c g x n b σ ev) := by …
```

`runFrom_instr_eq_of_ens`: If every normal return reachable from block `b` satisfies `Ens`, instrumentation with any placement (inserted checks at arbitrary `ret` edges, `?` exits unchecked) does not change the run from `b`.

```lean
-- lean/ToyContracts/Lemmas.lean:172-175
theorem runFrom_instr_eq_of_ens (c : Contract) (p : Placement) (g : Fn) (x n b : Nat)
    (σ : Store) (ev : List Nat)
    (hens : ∀ m tr r, runFrom c g x m b σ ev = ⟨tr, .ret r⟩ → c.ens x r = true) :
    runFrom c (instr p g) x n b σ ev = runFrom c g x n b σ ev := by …
```

`run_instr_eq_of_req_of_ensOnReturnsAt`: On an input with `Req x` at which every normal return of `g` satisfies `Ens`, instrumentation with any placement does not change the run, at every fuel (no `Lowered` or `NoChecks` needed).

```lean
-- lean/ToyContracts/Lemmas.lean:225-227
theorem run_instr_eq_of_req_of_ensOnReturnsAt (c : Contract) (p : Placement) (g : Fn) (x : Nat)
    (hreq : c.req x = true) (hens : EnsOnReturnsAt c g x) (n : Nat) :
    run c (instr p g) x n = run c g x n := by …
```

`run_instr_of_req_false`: Off `Req`, every instrumentation stops at its first prologue statement with a `requires` failure and no events, at every fuel.

```lean
-- lean/ToyContracts/Lemmas.lean:237-238
theorem run_instr_of_req_false (c : Contract) (p : Placement) (g : Fn) (x : Nat)
    (h : c.req x = false) (n : Nat) : run c (instr p g) x n = ⟨[], .checkFail .pre⟩ := by …
```

`instrObs_run_eq_of_req_of_ensOnReturnsAt`: On an input with `Req x` at which every normal return of `g` satisfies `Ens`, the contract wrapper leaves the run of `g` unchanged, at every fuel.

```lean
-- lean/ToyContracts/Lemmas.lean:243-245
theorem instrObs_run_eq_of_req_of_ensOnReturnsAt (c : Contract) (g : Fn) (x : Nat)
    (hreq : c.req x = true) (hens : EnsOnReturnsAt c g x) (n : Nat) :
    instrObs c x (run c g x n) = run c g x n := by …
```

`instrObs_eq_ret`: If the contract wrapper of a run of `g` is a normal return of `r`, then `Req x`, `Ens x r`, and the run of `g` itself is that return.

```lean
-- lean/ToyContracts/Lemmas.lean:255-256
theorem instrObs_eq_ret {c : Contract} {x : Nat} {o : Obs} {tr : List Nat} {r : Nat}
    (h : instrObs c x o = ⟨tr, .ret r⟩) : c.req x = true ∧ c.ens x r = true ∧ o = ⟨tr, .ret r⟩ := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:272-274
theorem runFrom_mono {c : Contract} {f : Fn} {x n m b : Nat} {σ : Store} {ev : List Nat}
    (hfin : (runFrom c f x n b σ ev).outcome ≠ .fuelOut) (hle : n ≤ m) :
    runFrom c f x m b σ ev = runFrom c f x n b σ ev := by …
```

`run_mono`: Fuel monotonicity: once a run has ended (not `fuelOut`), more fuel gives the same observation.

```lean
-- lean/ToyContracts/Lemmas.lean:303-305
theorem run_mono {c : Contract} {f : Fn} {x n m : Nat}
    (hfin : (run c f x n).outcome ≠ .fuelOut) (hle : n ≤ m) :
    run c f x m = run c f x n := by …
```

`halts_unique`: Determinism: a function has at most one halting observation on each input.

```lean
-- lean/ToyContracts/Lemmas.lean:312-313
theorem halts_unique {c : Contract} {f : Fn} {x : Nat} {o₁ o₂ : Obs}
    (h₁ : Halts c f x o₁) (h₂ : Halts c f x o₂) : o₁ = o₂ := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:322
theorem lowered_lower (f : Fn) : Lowered (lower f) := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:334-336
theorem lower_blocks_lt (f : Fn) {b : Nat} (hb : b < f.blocks.length) :
    (lower f).blocks[b]? =
      (f.blocks[b]?).map (fun blk => { blk with term := lowerTerm f.blocks.length b blk.term }) := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:340-341
theorem lower_blocks_add (f : Fn) (b : Nat) :
    (lower f).blocks[f.blocks.length + b]? = (f.blocks[b]?).map errBlock := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:346-360
theorem runFrom_succ (c : Contract) (f : Fn) (x n b : Nat) (σ : Store) (ev : List Nat) :
    runFrom c f x (n + 1) b σ ev =
      match f.blocks[b]? with
      | none => ⟨ev, .stuck⟩
      | some blk =>
        match execStmts c x blk.stmts σ ev with
        | .stop ev' o => ⟨ev', o⟩
        | .cont σ' ev' =>
          match blk.term with
          | .goto b' => runFrom c f x n b' σ' ev'
          | .branch o b₁ b₀ => runFrom c f x n (if evalOp x σ' o = 0 then b₀ else b₁) σ' ev'
          | .tryQ o e b' =>
              if evalOp x σ' o = 0 then ⟨ev', .ret (evalOp x σ' e)⟩ else runFrom c f x n b' σ' ev'
          | .ret _ o => ⟨ev', .ret (evalOp x σ' o)⟩
          | .panic => ⟨ev', .panic⟩ := …
```

`runFrom_lower_of_fin`: A halting run of `f` from an in-range block at fuel `n` is reproduced by `lower f` at fuel `n + 1` (one extra block execution for a final `?` error exit).

```lean
-- lean/ToyContracts/Lemmas.lean:364-368
theorem runFrom_lower_of_fin {c : Contract} {f : Fn}
    (htgt : f.blocks.all (fun blk => blk.term.targets.all (· < f.blocks.length)) = true)
    (x n : Nat) {b : Nat} (hb : b < f.blocks.length) (σ : Store) (ev : List Nat)
    (hfin : (runFrom c f x n b σ ev).outcome ≠ .fuelOut) :
    runFrom c (lower f) x (n + 1) b σ ev = runFrom c f x n b σ ev := by …
```

`runFrom_of_lower_fin`: A halting run of `lower f` from an in-range block at fuel `n` is already a halting run of `f` at fuel `n`.

```lean
-- lean/ToyContracts/Lemmas.lean:414-418
theorem runFrom_of_lower_fin {c : Contract} {f : Fn}
    (htgt : f.blocks.all (fun blk => blk.term.targets.all (· < f.blocks.length)) = true)
    (x n : Nat) {b : Nat} (hb : b < f.blocks.length) (σ : Store) (ev : List Nat)
    (hfin : (runFrom c (lower f) x n b σ ev).outcome ≠ .fuelOut) :
    runFrom c f x n b σ ev = runFrom c (lower f) x n b σ ev := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:467-469
theorem filter_not_isContract_of_all {ss : List Stmt}
    (h : ss.all (fun s => !s.isContract) = true) :
    ss.filter (fun s => !s.isContract) = ss := …
```

```lean
-- lean/ToyContracts/Lemmas.lean:472-473
theorem filter_checkReq_cons (ss : List Stmt) :
    (.checkReq :: ss).filter (fun s => !s.isContract) = ss.filter (fun s => !s.isContract) := …
```

```lean
-- lean/ToyContracts/Lemmas.lean:475-476
theorem filter_checkEns_singleton (o : Operand) :
    ([Stmt.checkEns o]).filter (fun s => !s.isContract) = [] := …
```

```lean
-- lean/ToyContracts/Lemmas.lean:478-481
theorem erase_instrBlock_eq {blk : Block} (p : Placement)
    (h : blk.stmts.all (fun s => !s.isContract) = true) :
    { (instrBlock p blk) with
        stmts := (instrBlock p blk).stmts.filter (fun s => !s.isContract) } = blk := by …
```

```lean
-- lean/ToyContracts/Lemmas.lean:498-501
theorem map_erase_instrBlock {blks : List Block} (p : Placement)
    (hb : blks.all (fun blk => blk.stmts.all (fun s => !s.isContract)) = true) :
    (blks.map (instrBlock p)).map
        (fun blk => { blk with stmts := blk.stmts.filter (fun s => !s.isContract) }) = blks := by …
```

`noChecks_erase`: The erasure of any function contains no contract statement.

```lean
-- lean/ToyContracts/Lemmas.lean:509
theorem noChecks_erase (p : Fn) : NoChecks (erase p) := by …
```

`runFrom_congr_blocks`: Runs from a block depend on the blocks of the function and not on its prologue or entry.

```lean
-- lean/ToyContracts/Lemmas.lean:517-519
theorem runFrom_congr_blocks (c : Contract) (f₁ f₂ : Fn) (hb : f₁.blocks = f₂.blocks)
    (x n b : Nat) (σ : Store) (ev : List Nat) :
    runFrom c f₁ x n b σ ev = runFrom c f₂ x n b σ ev := by …
```

`runFrom_gLoop`: A run of the emitting loop `gLoop` never ends: at fuel `n` it has emitted `n` ones.

```lean
-- lean/ToyContracts/Lemmas.lean:542-543
theorem runFrom_gLoop (x : Nat) : ∀ n σ ev,
    runFrom c1 gLoop x n 0 σ ev = ⟨ev ++ List.replicate n 1, .fuelOut⟩ := by …
```

`governingCrate_atDefinition`: Under resolution at the definition, the governing crate is the crate holding the check.

```lean
-- lean/ToyContracts/Lemmas.lean:554-555
theorem governingCrate_atDefinition (s : Site) (cs : CallSite) :
    governingCrate s .atDefinition cs = holder s cs := by …
```

`ctfeRun_evalChecks_eq`: Compile-time evaluation that evaluates checks runs the function itself.

```lean
-- lean/ToyContracts/Lemmas.lean:559-560
theorem ctfeRun_evalChecks_eq (c : Contract) (p : Fn) (x n : Nat) :
    ctfeRun .evalChecks c p x n = run c p x n := …
```

`not_detects_of_noChecks_of_req_of_no_ret`: When `Req x` holds, a call of a callee without contract statements that never returns normally on `x` (it panics, diverges or gets stuck) reports nothing, under every flag assignment, placement, resolution and call site.

```lean
-- lean/ToyContracts/Consequences.lean:12-15
theorem not_detects_of_noChecks_of_req_of_no_ret (fl : Nat → Bool) (s : Site) (res : Resolution)
    (cs : CallSite) (c : Contract) (g : Fn) (hnc : NoChecks g) (x : Nat)
    (hreq : c.req x = true) (hnoret : ∀ tr r, ¬ Halts c g x ⟨tr, .ret r⟩) :
    ¬ Detects fl s res cs c g x := by …
```

`callRun_eq_checkFail_pre_of_req_false_of_governingFlag`: When `Req x` fails and the governing crate's flag is on, every call ends with a `requires` failure and no events at every fuel, whatever the callee does (no hypothesis on `g`).

```lean
-- lean/ToyContracts/Consequences.lean:26-29
theorem callRun_eq_checkFail_pre_of_req_false_of_governingFlag (fl : Nat → Bool) (s : Site)
    (res : Resolution) (cs : CallSite) (c : Contract) (g : Fn) (x : Nat) (h : c.req x = false)
    (hfl : fl (governingCrate s res cs) = true) (n : Nat) :
    callRun fl s res cs c g x n = ⟨[], .checkFail .pre⟩ := by …
```

`refuted_no_report_for_panicking_call_with_flag_on` (refutation of an earlier candidate statement): The unqualified reading "a call of a lowered callee without contract statements that panics reports nothing even with the governing flag on" is false: `gPanic` (lowered, without contract statements) panics on `100` as written, yet with every flag on its callee-side call reports a failed check, because `Req 100` fails under `c1`.

```lean
-- lean/ToyContracts/Consequences.lean:41-44
theorem refuted_no_report_for_panicking_call_with_flag_on :
    Lowered gPanic ∧ NoChecks gPanic ∧ c1.req 100 = false ∧
    Halts c1 gPanic 100 ⟨[100], .panic⟩ ∧
    Detects (fun _ => true) .calleeSide .atDefinition cs1 c1 gPanic 100 := …
```

### 4. Modeling bridge

Basis: derived (modeling bridge). Each bullet compares documented behaviour of a real system with a toy definition and states the comparison; no theorem of this package relates the toy to any of these systems (model–system relation: none proved), so each bullet is an analogy whose reasoning is given in the bullet itself.

- *Rust.* The experiment is tracked in https://github.com/rust-lang/rust/issues/128044 (open). At rust-lang/rust commit `c7d5ba59d8e11ee2e2204b173458eec4cb41c973` the module documentation of `library/core/src/contracts.rs` reads (`library/core/src/contracts.rs@c7d5ba59d8e11ee2e2204b173458eec4cb41c973:1-1`): `//! Unstable module containing the unstable contracts lang items and attribute macros.` The file does not document check placement, the enabling flag or compile-time evaluation, and `src/doc/unstable-book/src/language-features/` at that commit has no page for the feature. These behaviours are therefore toy parameters here.
- *Ada 2012.* Postcondition checks are performed upon successful return (RM 6.1.1(35/3)): the analogue of the all-exits policy, with no check on exception propagation (the toy's panics). Enablement follows the assertion policy at the point of the aspect specification (6.1.1(19/3)): the analogue of resolution at definition. A pragma `Assertion_Policy` applying to a generic instantiation applies to the entire instance (11.4.2(10.3/3)): the analogue of resolution at instantiation, with the instantiating unit in the role of the toy's instantiating crate. Policy `Ignore` does not evaluate the assertion (11.4.2(10/3)): the analogue of erasure. These are analogies, not proved relations.
- *JML.* An `ensures` clause is a normal postcondition, guaranteed when the invocation returns without throwing (§9.9.3): the analogue of not checking `Ens` on panic paths. The JML runtime assertion checker of Cheon and Leavens (SERP '02) wraps the original method and checks postconditions around the call: the analogue of the contract wrapper `instrObs`.
- *SPARK.* Proof tools use assertion expressions whatever the assertion policy, and verification-condition generation is unaffected by disabling assertions (SPARK RM 28.0w §1 and §1.4.1): the analogue of erasing checks after the static obligation has been discharged.
- *C++ and LLVM.* `[[assume(e)]]` (WG21 P1774R8) and `llvm.assume` give undefined behaviour when the condition does not hold: the analogue of `assumeReq`. P1774R8 §4.6 and P2900R14 §3.5.12 discuss assumptions and contract assertions during constant evaluation: the analogue of the toy's `CtfeMode`.

## Boundaries

### Non-claims, result by result

Applies to every result: Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature (tracking issue https://github.com/rust-lang/rust/issues/128044, open), rustc, Ada, SPARK, JML, Eiffel or C++. Each card under Findings repeats this line.

**R1** (`run_instr_allExits_eq_instrObs_of_lowered`, theorem):

- Lowering precedes instrumentation in this theorem: there is a function still containing `tryQ` (`gTry`, at input `1` and fuel `1` under `c1`) for which the equation fails (`cex_instr_before_lower_misses_try`). Tightness does not mean the equation fails for every unlowered function; for example it is expected to hold when every `tryQ` block is unreachable (not proved here).
- Body outlining is not modelled: `Fn` has no calls inside functions, so checking `Ens` once at a single wrapper call site (in the style of `instrObs`, or of the wrapper methods of the JML runtime assertion checker cited under prior art), or routing every exit through one shared return block, is not a transformation of this toy. The theorem says that per-edge insertion on a lowered function has the same observations as that wrapper; it says nothing about the cost or code size of either.
- Panic paths: the instrumented run panics with the same events as `g` and `Ens` is not evaluated; a panic ends the run with outcome `panic`, there is no exceptional postcondition, and unwinding cleanup is not modelled (see the corpus package on panic safety and unwinding cited under prior art). The `?` error path is a normal return of a value (outcome `ret`) and so is subject to `Ens`; this models value-based error propagation, not exception propagation, which Ada 2012 6.1.1(35/3) and JML §9.9.3 exempt from normal postconditions.
- Contract clauses are total Boolean functions of the immutable argument (and of the returned value); evaluating a clause cannot panic, diverge, have side effects or read mutable state. Mutable parameters and clauses over memory or over entry-time (`old`) values are not modelled.
- A failed check is the distinct outcome `checkFail k`; whether a real failed check panics, unwinds or aborts is not modelled, and a failed check is never undefined behaviour in the toy.
- `Lowered g` inspects every block of `g`, reachable or not; the natural weakening that restricts it to blocks reachable from the entry is not established here.

**R2** (`req_and_ens_of_halts_ret_instr_allExits_lower`, theorem):

- A normal return of `instr .allExits (lower f)` need not be a normal return of `f`: without `JumpsInRange f`, `lower f` can return where `f` is `stuck` (`lower_fOut_returns_where_fOut_stuck`: on `5` under `c1`, `fOut` halts `stuck` while `instr .allExits (lower fOut)` returns `5`, and `Req 5` and `Ens 5 5` hold). Correspondence of the halting observations of `lower f` and `f` is `halts_lower_iff_of_jumpsInRange`, which assumes `JumpsInRange f`.
- The theorem concerns normal returns; it does not say that every violation is reported (a run may diverge, panic or get stuck instead).
- Lowering is applied before instrumentation; instrumenting `gTry` without lowering returns `9` on `1` under `c1` although `Ens 1 9` fails (`cex_instr_before_lower_misses_try`).
- Contract clauses are total Boolean functions of the immutable argument (and of the returned value); evaluating a clause cannot panic, diverge, have side effects or read mutable state. Mutable parameters and clauses over memory or over entry-time (`old`) values are not modelled.

**R4** (`halts_lower_iff_of_jumpsInRange`, theorem):

- Halting observations are compared: fuel-exact runs differ (a run that ends at a lowered `?` error exit takes one more block execution; `haltsEqAt_not_runEqAt_lower_gTry_1`), and the events of runs that exhaust their fuel are not compared.
- The natural weakening of `JumpsInRange f` to 'no reachable jump out of range' is not established.
- Degenerate edge: a function with no blocks fails `JumpsInRange` although `lower` leaves it unchanged (`not_jumpsInRange_gStuck_and_lower_eq`), so the theorem does not cover it.
- Lowering appends one block per original block, so `lower f` differs from `f` whenever `f` has a block, even without `?` (`lower_gEarly_ne`); the theorem is about halting observations, not syntax.

**R5** (`cex_tailOnly_misses_early_return`, counterexample):

- One concrete instance; it is not a statement about every function, input or flag assignment.
- It does not say that tail-only placement misses a violation for functions whose every return edge is the tail edge (not proved here).
- Checking the returned value once at a wrapper call site (`instrObs`), or routing every exit through one return block that carries the tail edge, would also catch this return (not modelled as a transformation here).

**R6** (`cex_tailOnly_misses_try_error_after_lowering`, counterexample):

- One concrete instance; it is not a statement about every function, input or flag assignment.
- Lowering does not make tail-only placement complete in this instance; whether some other lowering (for example one that routes every exit through the tail edge) would, is not examined.
- The `?` error path is a normal return of a value here (value-based error propagation), unlike an exception, which Ada 2012 6.1.1(35/3) and JML §9.9.3 exempt from normal postconditions.

**R7** (`cex_instr_before_lower_misses_try`, counterexample):

- One concrete instance; it is not a statement about every function, input or flag assignment.
- Instrumenting the source form `tryQ` directly (adding a check on its error path), or checking at a wrapper call site, would also avoid this miss; neither is modelled.

**R8** (`erase_instr_eq_of_noChecks`, theorem):

- A syntactic identity; it says nothing about observations by itself.
- Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
- `NoChecks g` inspects the prologue and every block of `g`, reachable or not; the natural weakening that restricts it to blocks reachable from the entry is not established here.

**R24** (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`, characterization):

- This compares checking with running `g` as written, which is what a call does when its governing flag is off (`callRun_eq_ite_governingFlag_of_lowered`). The comparison with the erasure `erase (instr .allExits g)` is `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`, which assumes `NoChecks g`; that hypothesis is tight there (`cex_erasure_noChecks`: `gInt` at input `3` under `cThree`) because `erase` also deletes contract statements of `g`.
- Diverging runs are compared by `RunEqAt` through their partial event traces; `HaltsEqAt` ignores them.
- `Lowered g` inspects every block of `g`, reachable or not; the natural weakening that restricts it to blocks reachable from the entry is not established here.
- Contract clauses are total Boolean functions of the immutable argument (and of the returned value); evaluating a clause cannot panic, diverge, have side effects or read mutable state. Mutable parameters and clauses over memory or over entry-time (`old`) values are not modelled.

**R9** (`erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req`, characterization):

- Termination plays no role: `RunEqAt` compares partial event traces of runs that exhaust their fuel; `HaltsEqAt` ignores diverging runs.
- The theorem is stated for the all-exits placement. With tail-only placement there is an instance at which its forward direction fails (`cex_erasure_tailOnly`: for `gEarly` on `0` under `c1` the erasure of the tail-only instrumentation is fuel-exactly identical to it while `Ens 0 7` fails).
- Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
- `Lowered g` and `NoChecks g` inspect every block of `g`, reachable or not (`NoChecks g` also the prologue); the natural weakenings that restrict them to blocks reachable from the entry are not established here.

**R10** (`erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks`, characterization):

- Equivalence is claimed on `Req` inputs; off `Req` erasure and instrumentation never have the same halting observations (`not_haltsEqAt_erase_instr_of_req_false`).
- Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
- `Lowered g` and `NoChecks g` inspect every block of `g`, reachable or not (`NoChecks g` also the prologue); the natural weakenings that restrict them to blocks reachable from the entry are not established here.

**R11** (`not_haltsEqAt_erase_instr_of_req_false`, theorem):

- The theorem's hypothesis is an input with `c.req x = false`. For a contract whose `requires` clause is identically true there is none, and in a whole program whose calls all pass arguments satisfying `Req`, such inputs never reach `g` (whole-program call contexts are not modelled).

**R12** (`run_assumeErase_eq_ite_req`, theorem):

- UB is an outcome of the toy (`ub`); what an optimizer may do with it is captured here by the refinement relation `UBRefinesAt` and by nothing else.
- The assumption is placed first in the prologue; assumptions at other program points are not modelled.

**R13** (`instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`, theorem):

- Direction: in `UBRefinesAt c tgt src x` the first program refines the second. This theorem has the checked program as `tgt`. It does not say that the assume-erased program refines the checked program; that fails at every input where `Req` fails (`not_assumeErase_ubRefinesAt_instr_of_req_false`), so this theorem does not justify replacing checks by `assume Req` as a UB-refining transformation of the checked program.
- `UBRefinesAt` compares halting observations of the target: a target that does not halt at `x` refines every source at `x` (`ubRefinesAt_of_forall_not_halts`; instance `ubRefinesAt_gLoop_gGood_5`, where the non-halting `gLoop` refines `gGood` at `5` although `gGood` returns `5` without UB). Divergence and the events of diverging runs are not constrained by this theorem.
- Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
- `NoChecks g` inspects the prologue and every block of `g`, reachable or not; the natural weakening that restricts it to blocks reachable from the entry is not established here.

**R14** (`not_assumeErase_ubRefinesAt_instr_of_req_false`, theorem):

- Together with `instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`, this shows that erasure plus `assume Req` is not equivalent to checking in the toy: the checked program UB-refines the assume-erased program (under that theorem's hypotheses), and the assume-erased program does not UB-refine the checked program at inputs where `Req` fails. Replacing checks by `assume Req` adds UB there.
- At an input with `Req x` true the conclusion can fail: for `gGood` at `5` under `c1` the assume-erased program UB-refines the checked program (`cex_not_ubRefines_req_true`); a caller that guarantees `Req` at every call is not modelled.

**R15** (`callRun_eq_ite_governingFlag_of_lowered`, theorem):

- `callRun` is a toy pipeline of three per-crate steps (`compileInDefCrate`, `instantiateIn`, `callInCallerCrate`), each of which reads the flag of its own crate and no other; it is not derived from a compilation, monomorphization or linking semantics of any real toolchain. Where a real compiler resolves a flag test (`Resolution`) and where checks are placed (`Site`) are parameters, not findings, and callee-side checks in `callRun` always use the all-exits placement.
- Policies that check `requires` at the caller and `ensures` in the callee, or that check whenever either crate's flag is on, are not modelled; nor are indirect calls through function pointers or trait objects, or a generic callee instantiated in more than one crate.
- Under resolution at definition the governing crate is the crate holding the check (`governingCrate_atDefinition`); under resolution at instantiation it can differ (`cex_calleeSide_atInstantiation_definingFlag_on_undetected`).
- `Lowered g` inspects every block of `g`, reachable or not; the natural weakening that restricts it to blocks reachable from the entry is not established here.

**R16** (`detects_iff_governingFlag_of_lowered_of_noChecks_of_violation`, characterization):

- When `Req x` holds, a call of a callee without contract statements (in its prologue or in any block, reachable or not) that never returns normally on `x` (it panics, diverges or gets stuck) reports nothing under any flags (`not_detects_of_noChecks_of_req_of_no_ret`). Without `Req x` that conclusion fails: `gPanic` panics on `100` under `c1` and its callee-side call with every flag on reports a failed check (`refuted_no_report_for_panicking_call_with_flag_on`, a proved refutation of an earlier candidate statement that omitted `Req x`). When `Req x` fails and the governing flag is on, the call ends with a `requires` failure and no events at every fuel, whatever `g` does (`callRun_eq_checkFail_pre_of_req_false_of_governingFlag`).
- `Detects` counts every `checkFail` outcome and cannot tell an inserted check from a contract statement already in `g`; `NoChecks g` is tight for that reason (`cex_detects_noChecks`).
- Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs. In-body assertions with predicates of their own are not modelled.
- `callRun` is a toy pipeline of three per-crate steps (`compileInDefCrate`, `instantiateIn`, `callInCallerCrate`), each of which reads the flag of its own crate and no other; it is not derived from a compilation, monomorphization or linking semantics of any real toolchain. Where a real compiler resolves a flag test (`Resolution`) and where checks are placed (`Site`) are parameters, not findings, and callee-side checks in `callRun` always use the all-exits placement.
- Policies that check `requires` at the caller and `ensures` in the callee, or that check whenever either crate's flag is on, are not modelled; nor are indirect calls through function pointers or trait objects, or a generic callee instantiated in more than one crate.
- `Lowered g` and `NoChecks g` inspect every block of `g`, reachable or not (`NoChecks g` also the prologue); the natural weakenings that restrict them to blocks reachable from the entry are not established here.

**R17** (`callRun_eq_run_of_not_violation`, theorem):

- Unobservability of the flags on such inputs relies on contract clauses being pure, total Boolean functions in the toy; where evaluating a passing clause can have side effects, allocate, diverge or raise, enabling checks can be observable without any violation (not modelled).
- `callRun` is a toy pipeline of three per-crate steps (`compileInDefCrate`, `instantiateIn`, `callInCallerCrate`), each of which reads the flag of its own crate and no other; it is not derived from a compilation, monomorphization or linking semantics of any real toolchain. Where a real compiler resolves a flag test (`Resolution`) and where checks are placed (`Site`) are parameters, not findings, and callee-side checks in `callRun` always use the all-exits placement.

**R18** (`cex_same_flags_detection_depends_on_placement`, counterexample):

- One concrete instance; it is not a statement about every function, input or flag assignment.
- `callRun` is a toy pipeline of three per-crate steps (`compileInDefCrate`, `instantiateIn`, `callInCallerCrate`), each of which reads the flag of its own crate and no other; it is not derived from a compilation, monomorphization or linking semantics of any real toolchain. Where a real compiler resolves a flag test (`Resolution`) and where checks are placed (`Site`) are parameters, not findings, and callee-side checks in `callRun` always use the all-exits placement.
- Policies that check `requires` at the caller and `ensures` in the callee, or that check whenever either crate's flag is on, are not modelled; nor are indirect calls through function pointers or trait objects, or a generic callee instantiated in more than one crate.

**R19** (`cex_calleeSide_atInstantiation_definingFlag_on_undetected`, counterexample):

- One concrete instance; it is not a statement about every function, input or flag assignment.
- For a generic callee instantiated in a third crate, the governing crate under resolution at instantiation is that crate (`governingCrate_csGen3_atInstantiation`), and detection follows its flag (`detects_csGen3_follows_instCrate`: reported with crate `2`'s flag alone on; not reported with the calling and defining crates' flags on and crate `2`'s off). Ada 2012 11.4.2(10.3/3) attaches the policy of a generic instantiation to the instance; whether a given compiler resolves a flag test at definition or at instantiation is not asserted.
- Policies that check `requires` at the caller and `ensures` in the callee, or that check whenever either crate's flag is on, are not modelled; nor are indirect calls through function pointers or trait objects, or a generic callee instantiated in more than one crate.
- `callRun` is a toy pipeline of three per-crate steps (`compileInDefCrate`, `instantiateIn`, `callInCallerCrate`), each of which reads the flag of its own crate and no other; it is not derived from a compilation, monomorphization or linking semantics of any real toolchain. Where a real compiler resolves a flag test (`Resolution`) and where checks are placed (`Site`) are parameters, not findings, and callee-side checks in `callRun` always use the all-exits placement.

**R20** (`runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`, characterization):

- `CtfeConst` and `RuntimeValue` take a `Placement` parameter and the theorem is stated for `.allExits`. With `.tailOnly` in both places the equivalence fails at one proved instance (`cex_runtimeValue_tailOnly`: for `gEarly` on `0` under `c1`, check-skipping evaluation of the tail-only instrumentation gives `7`, the tail-only checked call returns `7`, and `Ens 0 7` fails).
- Compile-time evaluation is a toy parameter (`CtfeMode`); nothing is asserted about which mode any compiler implements, and `CtfeConst` ignores events.
- Concrete reference instances: `cex_ctfeSkip_requires_violation` (the `Req x` false case) and `cex_ctfeSkip_ensures_violation` (the `Ens x r` false case).
- Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
- `Lowered g` and `NoChecks g` inspect every block of `g`, reachable or not (`NoChecks g` also the prologue); the natural weakenings that restrict them to blocks reachable from the entry are not established here.

**R21** (`runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`, characterization):

- The equivalence between an existential statement (`RuntimeValue`: some checked return of `r`) and a universal one (`StaticObligationAt`: every normal return satisfies `Ens`) relies on determinism of `run` (`halts_unique`); for a nondeterministic semantics it is not established.
- There is an input violating `Req` (`gEarly` on `100` under `c1`) at which the equivalence fails (`cex_runtimeValue_obl_req`): the static obligation holds vacuously there, but the runtime call fails its `requires` check.
- `CtfeConst` and `RuntimeValue` take a `Placement` parameter and the theorem is stated for `.allExits`. With `.tailOnly` in both places the equivalence fails at one proved instance (`cex_runtimeValue_obl_tailOnly`: for `gEarly` on `0` under `c1`, `Req 0` holds, check-skipping evaluation of the tail-only instrumentation gives `7`, the tail-only checked call returns `7`, and the static obligation at `0` fails).
- Compile-time evaluation is a toy parameter (`CtfeMode`); nothing is asserted about which mode any compiler implements, and `CtfeConst` ignores events.
- Contract statements (`checkReq`, `checkEns`, `assumeReq`) carry no predicate of their own: each evaluates a clause of the contract `c` under which the function runs, and `erase` deletes every contract statement, including any already present in the function as written. `NoChecks g` is tight for that reason; the comparison of `g` itself with `instr .allExits g` at inputs satisfying `Req` is characterized under `Lowered g` without assuming `NoChecks g` (`instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req`). In-body assertions with predicates of their own are not modelled.
- `Lowered g` and `NoChecks g` inspect every block of `g`, reachable or not (`NoChecks g` also the prologue); the natural weakenings that restrict them to blocks reachable from the entry are not established here.

**R22** (`cex_ctfeSkip_requires_violation`, counterexample):

- Reference instance of the `Req x` false case of `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`, and of the tightness of `Req x` in `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst`.
- One concrete instance; it is not a statement about every function, input or flag assignment.
- Compile-time evaluation is a toy parameter (`CtfeMode`); nothing is asserted about which mode any compiler implements, and `CtfeConst` ignores events.

**R23** (`cex_ctfeSkip_ensures_violation`, counterexample):

- Reference instance of the `Ens x r` false case of `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst`.
- One concrete instance; it is not a statement about every function, input or flag assignment.
- Compile-time evaluation is a toy parameter (`CtfeMode`); nothing is asserted about which mode any compiler implements, and `CtfeConst` ignores events.

### General boundaries

- **Model–system relation: none proved.** These are statements about the toy model; they neither establish nor refute the corresponding claims about the experimental Rust contracts feature, rustc, Ada, SPARK, JML, Eiffel or C++.
- **Parameters, not findings.** Placement (`Placement`, `Site`), flag resolution (`Resolution`) and compile-time evaluation (`CtfeMode`) are parameters; nothing here says which option a real compiler implements. `callRun` is a toy pipeline of three per-crate steps, not a model of any real compilation, monomorphization or linking pipeline.
- **Not modelled (not examined).** Calls inside functions and therefore body outlining or wrapper functions; a shared single return block; policies that check `requires` at the caller and `ensures` in the callee, or that check whenever either crate's flag is on; indirect calls; a generic callee instantiated in more than one crate; whole-program call contexts in which every caller establishes `Req`.
- **Unwinding (not examined).** `Ens` is not evaluated on panic paths and there is no exceptional postcondition; panics end the run without cleanup. The `?` error path is a normal return of a value and is subject to `Ens`.
- **Clauses (not examined).** Clauses are total, side-effect-free Boolean functions of the immutable argument and the result; failing, diverging or effectful clause evaluation, mutable parameters, memory and entry-time (`old`) values are outside the model. Contract statements carry no predicate of their own; in-body assertions with independent predicates are not modelled.
- **Observations.** `RunEqAt` is fuel-exact relative to an accounting in which contract statements cost no fuel; `HaltsEqAt` and `UBRefinesAt` compare halting observations and do not compare diverging runs (a target with no halting observation UB-refines every source: `ubRefinesAt_of_forall_not_halts`); `CtfeConst` ignores events. The semantics is deterministic, and `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst` relies on that.
- **Direction of refinement.** The checked program UB-refines the assume-erased program under the static obligation and `NoChecks` (`instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt`); the assume-erased program does not UB-refine the checked program at any input where `Req` fails (`not_assumeErase_ubRefinesAt_instr_of_req_false`). No result here justifies replacing checks by `assume Req` as a UB-refining transformation of the checked program.
- **Unestablished weakenings.** `JumpsInRange` cannot be weakened to reachable jumps on the strength of this package; `Lowered` and `NoChecks` are required of every block, reachable or not, and their weakenings to reachable blocks are not established.
- **Bounded search.** `support/RandomCheck.lean` is a bounded search over a finite sample; it cross-checks the statements and does not prove them.

### Escape hatches

- The two negative results, `not_haltsEqAt_erase_instr_of_req_false` and `not_assumeErase_ubRefinesAt_instr_of_req_false`, are defeated by dropping their one hypothesis `c.req x = false`: at an input where `Req` holds, each conclusion fails, for `gGood` on `5` under `c1` with placement `.allExits` (`cex_not_haltsEq_req_true`; `cex_not_ubRefines_req_true`, which also proves that there the assume-erased program UB-refines the checked one). Neither result applies to a contract whose `requires` clause is identically true, or to a whole program whose calls all pass arguments satisfying `Req` (whole-program call contexts are not modelled).
- The counterexample cards (R5, R6, R7, R18, R19, R22, R23) each exhibit one concrete instance. The tail-only failures of R5 and R6 both take a return edge other than the tail edge (`ret .early` in `gEarly`, and `ret .tryErr` in `lower gTry`); for lowered functions whose every return edge is the tail edge, tail-only placement is expected to catch every violation (not proved here). Checking `Ens` once at a wrapper call site (`instrObs`) or routing every exit through one return block would also catch the returns of R5 and R6 (not modelled as transformations here).
- Every hypothesis of every main result is `tight`, with a named counterexample in its hypothesis ledger; the witness class of each counterexample is recorded there. Whether `Lowered g`, `NoChecks g` or `JumpsInRange f` can be weakened to reachable blocks is not established here.

### Tightness status `unknown`

None: no hypothesis of any card has tightness `unknown` or `harmless`.

### Disproved or dropped statements

- No statement of this package was found false.
- `refuted_no_report_for_panicking_call_with_flag_on` is a proved refutation of an earlier candidate statement: the reading "a call of a lowered callee without contract statements that panics reports nothing even with the governing flag on", which omits `Req x`. Counterexample: `gPanic` panics on `100` under `c1`, and with every flag on its callee-side call reports a failed check because `Req 100` fails. The corrected statements are `not_detects_of_noChecks_of_req_of_no_ret` (with `Req x`) and `callRun_eq_checkFail_pre_of_req_false_of_governingFlag` (without it), both quoted under Findings.
- R3, a special case of R1 for functions with at most two exit edges, is not stated: R1 is proved for every lowered function and subsumes it.

## Evidence

### Kernel-check record

- Toolchain: Lean `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52` of leanprover/lean4), core Lean without Mathlib. Library `ToyContracts` (namespace `Toy.Contracts`) in `lean/`, with a `lakefile.toml` declaring one `lean_lib` and no dependencies.
- `lake build` in `lean/` succeeds with no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declaration in the sources.
- Axiom audit: `Lean.collectAxioms` over all 820 declarations of the library (every constant of the library's modules whose name is not marked internal): every declaration depends on at most `propext`, `Classical.choice` and `Quot.sound` (axioms occurring: `Classical.choice`, `Quot.sound`, `propext`). Per-declaration lists are in `audit/axioms.json`.
- Statement hashes: for each of the 279 names recorded in `results.json` (fields `lean` and `lean_names`, plus counterexamples, non-vacuity witnesses and positive controls), `audit/statements.json` records the SHA-256 of the Lean `repr` of its type (statement hash) and the SHA-256 of its definition closure: the sorted list, joined by newlines, of `name : repr type` (followed by ` := repr value` for non-theorems) for every package-local constant reachable from the statement, theorem bodies excluded (closure hash; the closure size is in parentheses below). Changing a definition that a statement depends on changes its closure hash.

Per result: the result theorem, the counterexample of each `tight` hypothesis, the non-vacuity witness and the positive control (the remaining recorded names, definitions and auxiliary lemmas, are in `audit/statements.json`).

| Card | Role | Theorem | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- | :--- |
| R1 | result | `run_instr_allExits_eq_instrObs_of_lowered` | Quot.sound, propext | `b4ac00b91c92e7aaae36c4f3f5e423426b0620c460c1604b5ea0a0baea81c1b1` | `23a3054e232832abe2c6388da01bf5aa1348e6e4a417db5152955a642402b349` (109) |
| R1 | counterexample | `cex_instr_before_lower_misses_try` | Quot.sound, propext | `2ddf3cc85be3c930a5ccd7ac6a725b5fb5edec38875754448b7c9deed8f108d5` | `2dbc15bda0c9397a353d4671f2af7121776a3d30fb2fb44a63a545b1b68eec11` (113) |
| R1 | non-vacuity | `nonvacuity_run_instr_allExits` | propext | `87d0d5e66fcfedd0474a009d32cb222e8e270d39ef33c38f1f27a38b5b054fe4` | `6410e62ca9600465b8841a585893919d3224beeef76f006f928c6cf86134c539` (38) |
| R2 | result | `req_and_ens_of_halts_ret_instr_allExits_lower` | Classical.choice, Quot.sound, propext | `d0d2b6b51a9ee3fc9496223146ed71061c107bda7ee429bdb01c04377758b0b3` | `a58370c31ddf0b24d9ed2461fc12b5c89c758c3c7ca17ad9325d26d6dfddb655` (103) |
| R2 | counterexample | `cex_req_and_ens_premise` | propext | `784841726b9fabe00bdd4785b5a2244603a9eba033bba322d136f107bf548cb4` | `805639ae50132eca1b158a621afddf4d9beefab078dfacc01df6308925d39ed7` (105) |
| R2 | non-vacuity | `nonvacuity_req_and_ens_lower` | propext | `99b8c9e266c24af43feda9b223461edcee6f4232622c38322fa4b86bdc308aa5` | `e97735210354acaede673a36c9336ca1b0aecf82bfb162de96fab747b8f45a0e` (105) |
| R4 | result | `halts_lower_iff_of_jumpsInRange` | Classical.choice, Quot.sound, propext | `344c769dfd18af679bc34c8442050a5ae6d0ea987b89ddbae5f6d849451e4c61` | `2bf7876da2e5e96a8693516d4b159251c176f4a17f8e62b75965e7ec46285742` (89) |
| R4 | counterexample | `cex_lower_jumpsInRange` | Quot.sound, propext | `ff06cccacc643e153d46653b39aab5c9a220129bc88d14b15a61f630aa4dc73d` | `dad3f7551bfc24d9fc2321b197b1e54fc7526ae2cff8175df33285890a20c37d` (91) |
| R4 | counterexample | `cex_lower_entry_out_of_range` | propext | `9b33e27d66aecba43fe9dcc9aef85d1a6afa5936dbd3d4d81ae2f3d1da5de0df` | `f5e872df55fef5d7c00027a1af37196e341b3c77c9864f48ac187fb8cc035550` (91) |
| R4 | non-vacuity | `nonvacuity_halts_lower` | none | `6b4f224a5eef5c0008860b55e8d9f62fff235366460f2c8ee27d3263a3007f1b` | `cf3510e69abd47e189a98589eb17bce9d286d6a02d317db60a934befb2f91ed7` (37) |
| R5 | result | `cex_tailOnly_misses_early_return` | Quot.sound, propext | `1202662df8f1e8c57c37598dd0b8f832736cd8f1f2318efcc06cc18def85d741` | `758a51310d0c8db82272d162c302eb1b5203ff8720b09bb4a27b8203abee6e14` (104) |
| R6 | result | `cex_tailOnly_misses_try_error_after_lowering` | Quot.sound, propext | `22d6f0c42b6ddf7e0cf282d49144e0eae95b237d3215a952636c995e5bb60b27` | `9f4715048a3ad683642985fe076113b4330c76ece56c5d47cecc0e29481c18be` (107) |
| R7 | result | `cex_instr_before_lower_misses_try` | Quot.sound, propext | `2ddf3cc85be3c930a5ccd7ac6a725b5fb5edec38875754448b7c9deed8f108d5` | `2dbc15bda0c9397a353d4671f2af7121776a3d30fb2fb44a63a545b1b68eec11` (113) |
| R8 | result | `erase_instr_eq_of_noChecks` | Quot.sound, propext | `0c4eb3d26a25f95673d2d2da84b3ad74b11686147fc5413dcdc91f5dcf1153e6` | `6a41053b9f284ff36e7fa325cc488019538bcf5f5ea13cc39227c57df556a0a3` (61) |
| R8 | counterexample | `cex_erase_instr_noChecks` | propext | `8eca39830ee30addc286cafe1fd4791d57d76a7cdf51aeeac8a0595b2ec60ae1` | `8d2e14f284e1371211cee6b01a5b05997d00df3233f3acc0835d458e77e2a71e` (62) |
| R8 | non-vacuity | `nonvacuity_erase_instr` | propext | `54acca8ed5dbf5351f16fcaab36d18231dbe42d6d04444cbf720f289d2667e0b` | `08de66ee43cbff73e893475e2bd45738352d6d4f85dcb63e7d76e325325a1d81` (39) |
| R24 | result | `instr_allExits_obsEq_self_iff_ensOnReturnsAt_of_lowered_of_req` | Quot.sound, propext | `005bf07b4fdb57d13b32898f2cf39e310a34695ad48ceb4bc745baaa815c3b97` | `1244b9ffbce0e1b852f5643c338b0c38a935d18d58913217545c5eaa14022890` (105) |
| R24 | counterexample | `cex_instrSelf_lowered` | Quot.sound, propext | `403e7915c20848e2e6d42f6ec5f1a06a023893820aa6618b2fdb43e577785a01` | `1c8691a7b41e522946489c1bd173361f8ce39cde1ac1153988296325b3a5366c` (107) |
| R24 | counterexample | `cex_instrSelf_req` | Quot.sound, propext | `6627ad5f5d154b9d5bd993ac7ad23ebcc941aef85736dd588daf75ea66e940e5` | `5eef6f0f62c021a4de67c6ef87e3dbd012b41a565c7ecaf294229ff2fcb0cb83` (107) |
| R24 | non-vacuity | `nonvacuity_instrSelf` | Quot.sound, propext | `03ce7f5a69a91078efac2bddf2c9b91532bbcbe05a0068122e986a678185fd7c` | `187aabd345df1ddea557bf3740437f61e97795059cc64977ca0c1e765557d660` (96) |
| R9 | result | `erasure_obsEq_iff_ensOnReturnsAt_of_lowered_of_noChecks_of_req` | Quot.sound, propext | `9875a76458edaacd51917eb788a72339938da540dd84a9c09e86a0268b3bc24a` | `c9913b9a5f8da5a3d2bc3210e10258b66a6472b74cf3a0ef25147cc52ff00f7a` (111) |
| R9 | counterexample | `cex_erasure_lowered` | Quot.sound, propext | `ce9cd3fbe0c0f5d0e0bfa96b592030455a37654ce70e27cdfcf88e38b7cc8a65` | `fe7a28a1302ea1ed8f78107833f2a14c5110bd0934db0105612699e13a380389` (113) |
| R9 | counterexample | `cex_erasure_noChecks` | Quot.sound, propext | `e5ce65585c67ed47612f3ec7c2ba660b0a130b90cdbf3bc14a831285b37322d1` | `d41cd93bb73238aae8ead8cb80effafdad59b459782319017c55fb02b9fcb796` (113) |
| R9 | counterexample | `cex_erasure_req` | Quot.sound, propext | `7de8e59e6ee7bc36dba05fcf5fc1140e028a0f60c0ecdbeaf4482270b9e62f1f` | `5af9d4cb76604fc81432319e535eaa75f6883766323903fe258e374ee22325a6` (113) |
| R9 | non-vacuity | `nonvacuity_erasure_pointwise` | Quot.sound, propext | `846342724f51512d59ff0f25d458e83d08d099da07c5c6dd93718ad71352aa23` | `f9e0983e4dd564709ed9fee2d7c5b8a0a0b30401e9abd2e7f77077ec61c8a716` (113) |
| R10 | result | `erasure_obsEq_onReq_iff_staticObligation_of_lowered_of_noChecks` | Quot.sound, propext | `cc0808ec9c06fe90b2a49d13ddef3a2869982aee832bf1cc4adb2198713009d8` | `5d6660e8d1785b0a0439dcada69f9901d70fe8a1996ed326db57d1d8e210b013` (113) |
| R10 | counterexample | `cex_erasure_global_lowered` | Quot.sound, propext | `f371cdbd60bb3dece4898554c20c8b9270f9923be70b908e9e4a1346c2636564` | `9981af5622f1d370f2fc227612c6c2d1a94b6682b7b692b050731ec8f93bd135` (115) |
| R10 | counterexample | `cex_erasure_global_noChecks` | Quot.sound, propext | `bd4ad68c5942b9f3ccbba5b4c63bd9ae6736003026940a7a7ade40f26a764691` | `41dbaaf77507e43d93d11c233db5806cfa2c645c31c155973806c0faba8799e0` (115) |
| R10 | non-vacuity | `nonvacuity_erasure_global` | Quot.sound, propext | `862e8072bc5561cf9afe602e28fe4c7ebbed5234503c37ffe9b41928412e7250` | `400a8c6a53a5a99d8c80bc5dcb97b0496875da7219ad9f6f95962f0f864a6bea` (96) |
| R11 | result | `not_haltsEqAt_erase_instr_of_req_false` | Quot.sound, propext | `fca00120b1de400fe073956996962e71a85958454f9b988dae1d57dde1e3ffe4` | `038dfe23996a09065f7a19aee48055e5f3233c831f529155be213d329527ad1f` (105) |
| R11 | counterexample | `cex_not_haltsEq_req_true` | propext | `0baa44296cfc59a1e574f663a98d0e02323eb979b994af7ae6f464c50f00ca55` | `0be41dccf5a82349d33be9462f80b12c329a622e0f36194a56951f9834ed5f2a` (107) |
| R11 | non-vacuity | `nonvacuity_req_false` | none | `e1b5c185eb4fd27d5b5cb257a4e9b3634c7674489dce54c17232335f151fa30c` | `80e766349bb53c719d77ad2a591fbdd3ddfdc37eb5c4110779f1706c147814ff` (4) |
| R11 | positive control | `cex_not_haltsEq_req_true` | propext | `0baa44296cfc59a1e574f663a98d0e02323eb979b994af7ae6f464c50f00ca55` | `0be41dccf5a82349d33be9462f80b12c329a622e0f36194a56951f9834ed5f2a` (107) |
| R12 | result | `run_assumeErase_eq_ite_req` | propext | `97521ee77a50926517b8a02a2233a91d779e3e8eb2a7e5e257ea905e52607ff6` | `5e192c305f1333ebd69049243138418582d4e0132f9865c27c9debadd0afb697` (84) |
| R12 | non-vacuity | `nonvacuity_assumeErase` | none | `322889a6cccb77e124996e6bb1f520d090e6edd9daeeec15e4d1c2cb46670648` | `80e766349bb53c719d77ad2a591fbdd3ddfdc37eb5c4110779f1706c147814ff` (4) |
| R13 | result | `instr_allExits_ubRefinesAt_assumeErase_of_noChecks_of_staticObligationAt` | Quot.sound, propext | `3f6b3dfa40f684c97526f059ee8054606c56a11da6c49997e7bb4a0a681d3adc` | `3eff23a4d331d1ed7e2ebb4916e25797e169a0c09c5d965a146ed6b89cfd4216` (109) |
| R13 | counterexample | `cex_ubRefines_noChecks` | Quot.sound, propext | `e3ce23088b02ca5fff7542b934b5910baed45dfca60d935c15ff43d9c8e6acfe` | `5c9dbbb61a409fede02e88da71e7722c44e62afa6d79a6f783d5a3d565521cde` (111) |
| R13 | counterexample | `cex_ubRefines_obligation` | Quot.sound, propext | `5b33d66b46844276df17599d6aeb8e34454db10ebbe066c201ccf0b55f36fefa` | `6e973cb2a402a116f5dbce680aad619a975d0df2559ed2cc2b620808b4b896da` (111) |
| R13 | non-vacuity | `nonvacuity_ubRefines` | Quot.sound, propext | `7886cda61f822ebbd9bc32aa6adaf09c9c74bd5a25c14d618dd0af48ca7993a0` | `e145c286f45cf089c456143a11f07f62a15ee55ceb682396c9ad4ab7ac3339cc` (95) |
| R14 | result | `not_assumeErase_ubRefinesAt_instr_of_req_false` | propext | `cc9f754b2005a5e175f5dc6eb3cbb4647df2094ce7efc8dd9783e7fbcd0ff165` | `f1a81dc6cc7aefb12f926c4034830596a5bedffe8d306039b94377bdeb6e388d` (106) |
| R14 | counterexample | `cex_not_ubRefines_req_true` | propext | `91f258042a298e07922228102687bf832d677bed671c21bddfc90dd944abcbfc` | `29bf42b0525715b82cec25a881f318467a34ae31ff836f43d1fc89eafd1db3b2` (108) |
| R14 | non-vacuity | `nonvacuity_req_false` | none | `e1b5c185eb4fd27d5b5cb257a4e9b3634c7674489dce54c17232335f151fa30c` | `80e766349bb53c719d77ad2a591fbdd3ddfdc37eb5c4110779f1706c147814ff` (4) |
| R14 | positive control | `cex_not_ubRefines_req_true` | propext | `91f258042a298e07922228102687bf832d677bed671c21bddfc90dd944abcbfc` | `29bf42b0525715b82cec25a881f318467a34ae31ff836f43d1fc89eafd1db3b2` (108) |
| R15 | result | `callRun_eq_ite_governingFlag_of_lowered` | Quot.sound, propext | `1a558aa8877465f30d63fc2023041ec86a0ffb29e0ff7cd6843abdc87b4668e4` | `f2052fbf10a0c36047e81c3585d5557e96e07daa5cbfaca3e0de6d50b5e97aaa` (142) |
| R15 | counterexample | `cex_callRun_lowered` | propext | `4c42dc3c14ca65fe051052283788c979921c8c8112e5649b652a37579ad6a78f` | `dd9678d4802d934478918d785a22221ec3e05b45a43c52083e10f4624fa174ef` (145) |
| R15 | non-vacuity | `nonvacuity_callRun` | propext | `87d0d5e66fcfedd0474a009d32cb222e8e270d39ef33c38f1f27a38b5b054fe4` | `6410e62ca9600465b8841a585893919d3224beeef76f006f928c6cf86134c539` (38) |
| R16 | result | `detects_iff_governingFlag_of_lowered_of_noChecks_of_violation` | Quot.sound, propext | `584fd505619726a41a70548f77ceb1f8f8cb602c26fd65207f0ba6b4fd6f5c44` | `64fffb14a4ed5c5b2d632d0875fc7160b35632f584145e047adda25bbea86fa4` (151) |
| R16 | counterexample | `cex_detects_lowered` | Classical.choice, Quot.sound, propext | `4afcbcdbd98405c9dc0ae38625d827c0cc33822f5c99a29547c39ff0cbfd660e` | `396ed482fa4fa17ac464abf5425cb7179672bfc2ef512ca049400edab48897ac` (154) |
| R16 | counterexample | `cex_detects_noChecks` | propext | `166607c8e9e9a304f084be26435a2779a6fa04b4a8af8ef44f3e8efa85e4d9c8` | `3275b8a5e636385ca40784a98b00a3600daa3697677c80a9c40149f825147404` (154) |
| R16 | counterexample | `cex_detects_violation` | Quot.sound, propext | `e43f3e1efeb43e07c03cac65cbcea42129e31b7e949447037bb09c2cab994187` | `665fda61d437a94100c19239378a0ed36a54f900a2280e38bce86646bc1c1145` (154) |
| R16 | non-vacuity | `nonvacuity_detects` | Quot.sound, propext | `dc17035853000ffdb1fd373ed945d05fdf46ceaa3c0c8d8545d5a1026a584f95` | `0f9ec957b41e558b5cf9a14c4031944796f3f3a6b305d4b23c3213036c98a530` (93) |
| R17 | result | `callRun_eq_run_of_not_violation` | Quot.sound, propext | `94467f88ae739420e457e62269568c2bc762d9bc894cd10566c45b8b11dc922b` | `0b4e47e89773f0d2be74a5a56ba6eac4bd64ae9cda83ea82b499748b15cb7071` (139) |
| R17 | counterexample | `cex_callRun_violation` | Quot.sound, propext | `558b95f6d62c67be93f192ea47d9f7ed5679b460c83aa227ffbf630121ab21a8` | `cadc1c948370261a94cd1dbc97a083401e137afd09431269ba4fae1bfcf54c1b` (142) |
| R17 | non-vacuity | `nonvacuity_not_violation` | Quot.sound, propext | `9b1d0117a1c645329fcdfc7a0221329dba8fdc3f31495a50162d19555fed570f` | `70e80997a92585f0bd28a2049be959c9383d176ca85b5aea60b423c582123c26` (83) |
| R18 | result | `cex_same_flags_detection_depends_on_placement` | Quot.sound, propext | `86429578e0db4ee3733330a74a86ae423333e2defbdb19fff2ad75714d004567` | `46b6009e471a59f5b92b8edc63f2b1ead8c5a6955d8996707d895500328b2470` (144) |
| R19 | result | `cex_calleeSide_atInstantiation_definingFlag_on_undetected` | Quot.sound, propext | `a7af2675ab53b0b94df061b3d062a2e54fb031152ae77723e1c92e23c99b22a4` | `0b4bdfcaf406ab0225539f7e76325deca7900a4ada847fe693e28292990c4f63` (147) |
| R20 | result | `runtimeValue_iff_req_and_ens_of_lowered_of_noChecks_of_ctfeSkipConst` | Quot.sound, propext | `0d8ab585e69e96e5b9126726081f9073d5aa6806bad18179d60dda6f4db599bb` | `62fe8fcb2ca34c8a5a7a5122d34b95a8486839267822c0b6b0fe946baff5d270` (117) |
| R20 | counterexample | `cex_runtimeValue_lowered` | Quot.sound, propext | `ae32fc9e638cb34edcd1e3e97644237c7589f355ce7a86ae55933a32585f5080` | `5a67f4311d9249c820c2634b59820627b7408ac03a200730ebb9f28b9e74e9c3` (119) |
| R20 | counterexample | `cex_runtimeValue_noChecks` | Quot.sound, propext | `cc9a9d52d4e15839ef9e7fbca0bd32dbc9a77ed4611ed67ef21df88b60aef66b` | `b8fb8462292e85cd49a594a2f023047db11ea9dcb0fdf54e6016a12d98e4be5d` (119) |
| R20 | counterexample | `cex_runtimeValue_ctfeConst` | Quot.sound, propext | `09544bf27faca8805484a5158897107e504913af8b7f4dcb34c07666d08c36e9` | `73137c78c5bfb3af21756b0d7531a26db929607508f6c3319e4c426db48e381f` (119) |
| R20 | non-vacuity | `nonvacuity_ctfe` | propext | `f07b0598b917381ed44673280d802d24d515a059f27f9071d448ddee21b166f8` | `53bf4f311f072772fcab25c158fada451113483f9215e1df25e23a2a650e0d46` (116) |
| R21 | result | `runtimeValue_iff_staticObligationAt_of_lowered_of_noChecks_of_req_of_ctfeSkipConst` | Quot.sound, propext | `6456fb97ff3f3b328f8636dfcdd5cd5046a1ef9e0d65aaaaf2594674c61cfc2f` | `f453b478ef54fcfbfe3998f3b1582ffa1be380e90a3d558238111769196b7456` (119) |
| R21 | counterexample | `cex_runtimeValue_obl_lowered` | Quot.sound, propext | `32c1cb0ba8d9794f085bf075e832f4426b5c40753ef5a0d53685c052515e2014` | `a78ddf069d94b4f59de2f1e7a2fb3fea90bcf74fb860daf37fad1300d3915d37` (121) |
| R21 | counterexample | `cex_runtimeValue_obl_noChecks` | Quot.sound, propext | `df4c9f1dca0bafc8afa09adb11a27248c568c2252b935cad071ff768623ff51e` | `c5098903d636f7b83439749915449a5d6fca35cd8e288a0acb01cb88f18aff65` (121) |
| R21 | counterexample | `cex_runtimeValue_obl_req` | Quot.sound, propext | `9121a1dd91d697d28c3677cee57c15d6cc093c253a142f056d22c5abc05e48ad` | `5f4f7e80e12baf1b30348c2e3c1f6faf8a5419644d416fe726e599e64a46ee6b` (121) |
| R21 | counterexample | `cex_runtimeValue_obl_ctfeConst` | Quot.sound, propext | `3df53178d82fcaf8f0de74ac36e4e2684091ba88c5182e0d5bd85d9d11c2644a` | `e860d05fd7b1ddc70657d5bc92d5689fef71818e6edff0c43771044885234558` (121) |
| R21 | non-vacuity | `nonvacuity_ctfe_req` | propext | `24505a07c618544ed4ec34669f76e683804dceedcd10427e6bd545145b0f36a6` | `53bf4f311f072772fcab25c158fada451113483f9215e1df25e23a2a650e0d46` (116) |
| R22 | result | `cex_ctfeSkip_requires_violation` | Quot.sound, propext | `d25c3be7949f24c10b7dab1e8c30bce9d27f8c30a2b661c837590c1579741e6c` | `5f4f7e80e12baf1b30348c2e3c1f6faf8a5419644d416fe726e599e64a46ee6b` (121) |
| R23 | result | `cex_ctfeSkip_ensures_violation` | Quot.sound, propext | `05555043e94ae618fa97453e72e2f0fd02bd4f4b7b0d2f5f8446da53f7bfea67` | `28a3260478df2935ff948a6331fb31d5111851dfb6a000dfe63ab72263846282` (119) |

### Bounded search (cross-check, not proof)

`support/RandomCheck.lean` (`[bounded search]`, run with `lake env lean ../support/RandomCheck.lean` from `lean/` after `lake build`): 400 pseudo-random functions from a fixed seed (1–4 blocks; contract statements `checkReq` and `checkEns` allowed in a third of them; `tryQ` terminators allowed in half of them; jump targets up to one past the last block, so out-of-range jumps occur; entry always in range, so out-of-range entries are not sampled and are covered by the kernel-checked `cex_lower_entry_out_of_range`), 4 fixed contracts, inputs `0..4`, fuel `0..7`, except fuel `0..15` in the R2 check and fuel `0..11` for the runtime-halting search in the R20 check (the R4 check also runs `lower f` at fuel `n + 1`, so up to 8). It checks bounded forms of R1, R2, R4 (including the `n + 1` fuel shift of lowering), R8, R9, R11, R12, R13, R15, R16, R17, R20 and R24, and fuel monotonicity of `run`, and prints the number of failures per check and the number of generated functions that satisfy `Lowered`. Re-run on 2026-11-21 against the packaged sources: zero failures for every check (344 of the 400 functions satisfy `Lowered`). This is a bounded search over a finite sample: it does not establish any statement; the kernel-checked theorems are the evidence.

### Primary sources

All accessed 2026-11-21. Exact records, quotes and the cards citing each are under each card's **Prior art** and in the modeling bridge.

- Lean 4 toolchain: leanprover/lean4 tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52` (resolved through the GitHub API).
- rust-lang/rust commit `c7d5ba59d8e11ee2e2204b173458eec4cb41c973`: `library/core/src/contracts.rs`, line 1 quoted in the modeling bridge (`library/core/src/contracts.rs@c7d5ba59d8e11ee2e2204b173458eec4cb41c973:1-1`); directory listing of `src/doc/unstable-book/src/language-features/`. The tracking issue https://github.com/rust-lang/rust/issues/128044 (open) is context, not a specification.
- Ada Reference Manual, ISO/IEC 8652:2012: §6.1.1 (http://www.ada-auth.org/standards/12rm/html/RM-6-1-1.html), paragraphs 19/3, 35/3, 36/3; §11.4.2 (http://www.ada-auth.org/standards/12rm/html/RM-11-4-2.html), paragraphs 10/3, 10.3/3.
- JML Reference Manual (draft), HTML edition generated 2013-05-31, §9.9.3 (https://www.cs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_9.html).
- Y. Cheon and G. T. Leavens, SERP '02, pp. 322–328; technical report Iowa State University TR #02-05a (http://www.cs.ucf.edu/~leavens/tech-reports/ISU/TR02-05/TR.pdf).
- SPARK Reference Manual, release 28.0w, §1 and §1.4.1 (https://docs.adacore.com/spark2014-docs/html/lrm/introduction.html; no immutable revision identifier).
- LLVM Language Reference Manual, `llvm.assume` (https://llvm.org/docs/LangRef.html#llvm-assume-intrinsic; moving document, no revision pinned).
- WG21 P1774R8, 'Portable assumptions', 2022-06-14 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2022/p1774r8.pdf).
- WG21 P2900R14, 'Contracts for C++', 2025-02-13 (https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2025/p2900r14.pdf).
- D. Ly, N. Kosmatov, F. Loulergue, J. Signoles, Formal Aspects of Computing 36(1), 2024, DOI 10.1145/3605951.
- J.-C. Filliâtre, L. Gondelman, A. Paskevich, Formal Methods in System Design 48(3), 2016, DOI 10.1007/s10703-016-0243-x.
- N. P. Lopes, J. Lee, C.-K. Hur, Z. Liu, J. Regehr, PLDI 2021, DOI 10.1145/3453483.3454030.
- X. Leroy, Communications of the ACM 52(7), 2009, DOI 10.1145/1538788.1538814.
- R. B. Findler and M. Felleisen, ICFP 2002, DOI 10.1145/581478.581484.
- R.-J. Back and J. von Wright, Refinement Calculus, Springer, 1998, DOI 10.1007/978-1-4612-1674-2.
- P. Lammich, 'Refinement for Monadic Programs', Archive of Formal Proofs, 2012 (https://www.isa-afp.org/entries/Refine_Monadic.html).
- B. Meyer, Object-Oriented Software Construction, 2nd edition, 1997, ISBN 0-13-629155-4 (table of contents at https://archive.eiffel.com/doc/manuals/technology/oosc/ACROBAT/oosc-tab.pdf).
- Related corpus packages, cited by slug at google/zerocopy branch `reference`, commit `95e95c2fbada69bc95437324bf4462759bd738a4`: zero-sized-access-elimination-ub-erasure-and-unreachable-switch-pruning-with-assume; monomorphization-reachability-lazy-shim-synthesis-and-closed-verification-targets; call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations; panic-safety-unwinding-through-broken-invariants-leak-amplification-and-safe-forget. They are context, not dependencies: no definition or theorem of theirs is used.
- Crossref records for the DOIs above and the commit records for both repositories were re-checked on 2026-11-21.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. All commands run from the package directory (the directory containing this file).

1. Full check (primary):

   ```sh
   python3 support/revalidate.py .
   ```

   It copies `lean/` to a temporary directory (the package is not modified), runs `lake build`, rejects any Lean source containing `sorry`, `admit` or `native_decide` or declaring an `axiom`, computes `Lean.collectAxioms` for every declaration of the library and fails if any depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, and recomputes, for every Lean name referenced by `results.json`, the statement hash and the definition-closure hash described under Evidence, comparing them with `audit/statements.json`. Exit status 0 means every check passed. The script's docstring states exactly what is hashed.

2. Build and axiom audit by hand:

   ```sh
   cd lean
   lake build
   lake env lean RevalidationAudit.lean
   ```

   `lean/RevalidationAudit.lean` is outside the library target (it is not built by `lake build`); it runs `#print axioms` for the result theorem of every card, and each printed list must contain at most `propext`, `Classical.choice` and `Quot.sound`.

3. Bounded search (optional; a cross-check, not a proof): from `lean/`, after `lake build`, run `lake env lean ../support/RandomCheck.lean`; the program prints its failures (expected: none).

What to re-examine after a change:
- A new Lean toolchain: rerun step 1; a changed statement or closure hash means the corresponding `repr` changed and the card's quoted statement must be re-read against the source.
- The modeling bridge: if the Rust contracts feature documents check placement, its enabling flag or its compile-time behaviour (in `library/core/src/contracts.rs` or the unstable book), the analogy in the modeling bridge must be re-derived; no theorem here depends on it.
