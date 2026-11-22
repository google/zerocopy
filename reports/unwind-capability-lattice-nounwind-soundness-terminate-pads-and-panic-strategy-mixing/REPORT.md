# Unwind capability: non-unwinding classification soundness, terminate pads, panic-strategy mixing and mixed landing-pad backends (toy models)

## Summary

A Lean 4 formalization of two toy models of unwinding: a multi-crate program model in which each crate classifies functions as possibly unwinding or non-unwinding through a precedence function (an ordered list of rules modelled on rustc's `fn_can_unwind`), with landing-pad actions, a toy pass that inserts terminate pads, panic strategies, a per-crate panic-in-drop setting and per-function landing-pad capabilities; and a call-chain model of one unwind through frames compiled by backends with (`full`) or without (`none`) landing pads. Lean project: `lean/` (library `ToyUnwindCap`, namespace `Toy.UnwindCap`), Lean `v4.34.1`, core Lean without Mathlib. All 18 results (25 main theorems) are kernel-checked, together with their counterexamples, non-vacuity witnesses, positive control and the definition examples; every declaration of the library depends on at most the axioms `propext`, `Classical.choice` and `Quot.sound` (Evidence).

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Model–system relation: none proved. These are statements about two toy models (a program model and a call-chain model); they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules, any compiler backend or any Rust toolchain. Backend landing-pad capabilities (`Pads`) are toy parameters; no capability or defect of any real backend is asserted.

* **R1** (theorem) — For every precedence function `cu` and every toy program `p`: if `p` satisfies `Enforced cu p` (at every function index, reachable or not: if the function is non-foreign and its own crate classifies it as non-unwinding, then every call in its body to a callee that this crate classifies as possibly unwinding carries a stopping pad, `catchPad` or `terminate`, and, when the panic handler is `unwind`, every panic point in its body carries a stopping pad), `ForeignCovered cu p` (every foreign function that may unwind is classified as possibly unwinding by its declaring crate) and `SiteAgreement cu p` (at every function index, reachable or not, at every call site without a stopping pad in a non-foreign function: if the caller's crate classifies the callee as non-unwinding, so does the callee's own crate), then no finite run produced by the evaluator `runFn` (no `Exec cu p f t o`) of any function `f` has outcome `ub`. Because the semantics records an unwind leaving a function that its own crate classifies as non-unwinding as `ub` (`boundary`), under these hypotheses no such unwind occurs.
* **R2** (theorem) — For every toy program `p` satisfying `ForeignHonest p` (every foreign function that may unwind is declared with the `cUnwind` ABI and without the never-unwind attribute) and `ForeignNotGlue p` (no foreign function is drop glue), the standard precedence function `stdCanUnwind` (ordered rules: never-unwind attribute, then `abort` strategy for non-foreign functions, then drop glue under panic-in-drop `abort`, then the ABI) satisfies `ForeignCovered stdCanUnwind p`.
* **R3** (characterization) — For every precedence function `cu`: `PrecForeignSound cu` (in every program satisfying `ForeignHonest` and `ForeignNotGlue`, `cu` classifies every foreign function that may unwind as possibly unwinding) holds iff `cu c i = true` for every crate setting `c` and every static-facts value `i : FnInfo` that is foreign, has the `cUnwind` ABI, lacks the never-unwind attribute and is not drop glue.
* **R4** (theorem) — `stdCanUnwind` and `abiFirstCanUnwind` (the same rules with the ABI rule consulted before the strategy rule) both satisfy `PrecForeignSound`; for every crate setting `c` and every `i : FnInfo`, if `abiFirstCanUnwind c i = false` then `stdCanUnwind c i = false`; and for `rustDefinedCUnwind` (a Rust-defined `extern "C-unwind"` function) classified from `abortCfg` (strategy `abort`), `stdCanUnwind` returns `false` while `abiFirstCanUnwind` returns `true`.
* **R5** (counterexample) — `abortAllCanUnwind` (the standard order with the `abort`-strategy rule applied to foreign functions as well) does not satisfy `PrecForeignSound` (`abortAllCanUnwind_not_foreignSound`); and the program `progAbortImportPlain` (an `abort` crate whose Rust function calls a foreign `"C-unwind"` import that may unwind, with a plain call; handler `abort`) satisfies `LinkOK`, `Enforced abortAllCanUnwind`, `SiteAgreement abortAllCanUnwind`, `ForeignHonest` and `ForeignNotGlue`, and its function 0 has a run with outcome `ub` under `abortAllCanUnwind` (`abortAll_progAbortImportPlain_ub`).
* **R6** (theorem) — For every precedence function `cu` and every toy program `p`: (i) `insertPads cu p` satisfies `Enforced cu` (`insertPads_enforced`); (ii) for every function index `g`, the body of `g` in `insertPads cu p` is `g`'s body with `padStmt cu p g` applied to every statement if `g` is non-foreign and classified as non-unwinding by its own crate, and is `g`'s body unchanged otherwise (`insertPads_body`); (iii) `padStmt cu p g` turns a call `.call f act` into `.call f .terminate` if `p.viewMay cu g f = true` and `act.Stops = false`, and leaves it unchanged otherwise (`padStmt_call`); (iv) `padStmt cu p g` turns a panic point `.raise act` into `.raise .terminate` if `p.handler = .unwind` and `act.Stops = false`, and leaves it unchanged otherwise (`padStmt_raise`); (v) if `p` satisfies `ForeignCovered cu p` then so does `insertPads cu p` (`insertPads_foreignCovered`), and if `p` satisfies `SiteAgreement cu p` (reachable or not, as in R1) then so does `insertPads cu p` (`insertPads_siteAgreement`); (vi) for every function `f`, trace `t` and outcome `o ≠ ub`, if `Exec cu p f t o` (a finite run produced by `runFn`) then `Exec cu (insertPads cu p) f t o` (`exec_insertPads_of_exec_of_ne_ub`). By (ii)-(iv), a `cleanup ds` action at a replaced site becomes `terminate` and its drop list `ds` is lost.
* **R7** (theorem) — Corollary of R1 and R6. For every precedence function `cu` and every toy program `p` satisfying `ForeignCovered cu p` and `SiteAgreement cu p` (reachable or not, as in R1), no finite run produced by `runFn` (no `Exec cu (insertPads cu p) f t o`) of any function of `insertPads cu p` has outcome `ub`.
* **R8** (theorem) — For every precedence function `cu`, toy program `p`, and function `g` that is non-foreign, is classified as non-unwinding by its own crate, and whose body is `.call f act :: rest` (the call is the first statement) with `act.Stops = false` (`act` is `none` or a cleanup pad): if `f` has a finite run produced by `runFn` (`Exec cu p f t .unwind`) with trace `t` that unwinds, then there is a trace `t'` such that `Exec cu p g t' .ub`; this holds whichever way `g`'s crate classifies `f`.
* **R9** (theorem) — For `stdCanUnwind` and every toy program `p` satisfying `LinkOK p` (if `p` is potentially unwinding, that is, it uses the `unwind` panic handler or some non-foreign function of an `unwind`-strategy crate has a call, reachable or not, to a `cUnwind` function, then every crate in `p.crates` uses the `unwind` strategy), `Enforced stdCanUnwind p` (reachable or not, as in R1), `ForeignHonest p`, `ForeignNotGlue p`, and, in case `p` is potentially unwinding, `GlueAgreement p` (at every call site, reachable or not, without a stopping pad that calls drop glue from a crate with panic-in-drop `abort`, the glue instance's crate has panic-in-drop `abort`): no finite run produced by `runFn` of any function of `p` has outcome `ub`. `SiteAgreement` is not assumed.
* **R10** (characterization) — In the drop-glue program with exactly two crates, `glueProg cc cg act body` (crate 0, with settings `cc`, holds the caller, function 0, whose body consists of exactly one call to function 1 with action `act`; crate 1, with settings `cg`, compiled the drop-glue instance, function 1, whose body is `body`; panic handler `unwind`), for all `cc`, `cg` and `act`: `GlueSiteSound cc cg act` (for every glue body `body`, calls included, for which the program satisfies `Enforced stdCanUnwind` at every function index and statement, reachable or not, no finite run of the caller produced by `runFn` has outcome `ub`) holds iff, whenever `stdCanUnwind cc glueInfo = false` (the caller's crate treats the glue as non-unwinding), `stdCanUnwind cg glueInfo = false` (the glue instance's own crate does too) or `act` is a stopping pad (`catchPad` or `terminate`).
* **R11** (characterization) — Corollary of R10. For all caller-crate settings `cc`, glue-crate settings `cg` and actions `act`: if the caller's crate has strategy `abort` or panic-in-drop `abort` (so it treats drop glue as non-unwinding) and the glue instance's crate has strategy `unwind`, then `GlueSiteSound cc cg act` holds iff the glue instance's crate has panic-in-drop `abort` or `act` is a stopping pad (`catchPad` or `terminate`).
* **R12** (theorem) — Reference point. For every lawful toy ABI `A` (`A.dec (A.enc v) = v` for every `v`), every backend `b0` of the innermost callee and every chain of frames `frs`: if `b0` and the backend of every frame in `frs` conform to `A` (each uses exactly `A`'s encoding and decoding, as functions on all of `Nat`), then `compRet b0 frs v = specRet frs v` for every value `v`, that is, normal returns through the mixed chain give the specified result.
* **R13** (characterization) — For every call chain `c` (frames listed innermost first, each with the landing-pad capability `pads` of the backend that compiled it and the landing-pad action of its active call site) that satisfies `NoReachedNoneTerminate c` (no frame that the specified unwind reaches, up to and including the first frame whose action stops it, is a `pads = none` frame with a terminate pad; frames after that one are unconstrained): the compiled unwind `compUnwind c` (frames compiled with `pads = none` perform no landing-pad action) equals the specified unwind `specUnwind c` (same events, tagged with frame positions, and same outcome) iff `ObligationsFull c` (every frame that the specified unwind reaches, up to and including the first frame whose action stops it, and that has a non-empty cleanup pad, a catch pad or a terminate pad, was compiled with `pads = full`). The direction from `ObligationsFull c` holds without `NoReachedNoneTerminate c` and is stated separately as R18.
* **R18** (theorem) — Companion of R13 (stated as its own card). For every call chain `c` that satisfies `ObligationsFull c` (every frame that the specified unwind reaches, up to and including the first frame whose action stops it, and that has a non-empty cleanup pad, a catch pad or a terminate pad, was compiled with `pads = full`), the compiled unwind `compUnwind c` equals the specified unwind `specUnwind c`. No condition on `pads = none` terminate frames is assumed.
* **R14** (characterization) — For every call chain `c`: the compiled and specified unwinds agree on every chain `c'` with `SameShape c c'` (the same backend capability frame by frame and the same actions at every `pads = full` frame, any actions at `pads = none` frames) iff `Shielded c`, that is, scanning from the innermost frame, every frame is compiled with `pads = full` up to and including the first frame whose action stops the unwind (`catchPad` or `terminate`), or up to the end of the chain if no frame stops it.
* **R15** (theorem) — Corollary of R14. For every call chain `c` with `TerminateShielded c` (scanning from the innermost frame, every frame is compiled with `pads = full` up to and including the first frame with a terminate pad, or up to the end of the chain if there is none), the compiled and specified unwinds agree on every chain `c'` with `SameShape c c'`.
* **R16** (theorem) — For every precedence function `cu`, toy program `p` and backend assignment `pads` (functions compiled with `pads = none` lose every landing pad, giving `p.withPads pads`): if every non-foreign function `g < p.fns.length` with `pads g = none` (reachable or not) is classified as non-unwinding by its own crate, and the compiled program `p.withPads pads` satisfies `EnforcedAt cu (p.withPads pads) g` (the per-function condition of `Enforced` in R1: if `g` is non-foreign and classified as non-unwinding by its own crate, then every call in its compiled body to a callee that this crate classifies as possibly unwinding carries a stopping pad, and, when the panic handler is `unwind`, every panic point in that body carries a stopping pad) and `SiteAgreementAt cu (p.withPads pads) g` (the per-function condition of `SiteAgreement` in R1) at every function index `g` with `pads g = none` (reachable or not), then every function has exactly the same finite runs produced by `runFn` (traces and outcomes) in `p.withPads pads` as in `p`. It is derived from R17.
* **R17** (theorem) — For every precedence function `cu`, toy program `p` and backend assignment `pads`: if, in every non-foreign function `g < p.fns.length` with `pads g = none` (reachable or not), every panic point has an action without an obligation (`Action.obligation`: `none` or `cleanup []`) when the panic handler is `unwind` (`hraise`), and every call whose action has an obligation (a non-empty cleanup pad, a catch pad or a terminate pad) calls a callee `f` classified as non-unwinding by `f`'s own crate (`hcall`), then every function has exactly the same finite runs produced by `runFn` (traces and outcomes) in `p.withPads pads` as in `p`. Calls without an obligation are unconstrained, so an unwind may pass through a `pads = none` function that has no landing-pad obligation.

Each bullet is the result's plain claim. The non-claims of every result are listed under Boundaries, result by result; each result must be read together with them.

## Applicability

**Model fidelity.** Both models are toy models; neither mirrors any compiler's data structures.

* *Program model* (`lean/ToyUnwindCap/Basic.lean`). Crates carry a panic strategy and a panic-in-drop setting. Functions carry an ABI (`rust`, `c`, `cUnwind`), a foreign flag, a never-unwind attribute flag, a drop-glue flag, the index of their defining (or, for foreign functions, declaring) crate, a straight-line body, and for foreign functions a `throws` flag saying whether the foreign code may unwind. A precedence function (`Prec`) classifies a function from the point of view of a crate (the crate that compiles the definition, or the crate of a caller). Statements are panic points (`raise`) and calls, each with a landing-pad action: `none` (plain call), `cleanup ds`, `catchPad`, `terminate`. The evaluator `runFn` returns every finite run (event trace, outcome) at a given fuel; `Exec` is "some fuel produces this run". An unwind arriving at a statement whose action is not a stopping pad is `ub` if the caller's crate classified the callee as non-unwinding; an unwind leaving a function that its own crate classified as non-unwinding is `ub` (`boundary`). A terminate pad aborts (observable, not `ub`). The panic handler is artifact-wide: under the `abort` handler a panic point aborts at once, without unwinding. A function compiled by a backend without landing pads (`pads = none`) keeps its frame unwindable: an unwind reaching one of its call sites passes through to its caller.
* *Chain model* (`lean/ToyUnwindCap/Chain.lean`). A call chain is the list of frames live when one unwind starts (innermost first); each frame records the landing-pad capability of the backend that compiled it (`full` or `none`) and the action of its active call site. Normal returns pass toy natural-number values through toy ABI encodings (`AbiCodec`).

The definitions are meant to capture: the rule order of rustc's `fn_can_unwind` and the two codegen consequences its documentation states (calls to non-unwinding callees ignore unwinding cleanup; calls to possibly-unwinding callees from non-unwinding functions get an aborting landing pad); RFC 2945's minimal aborting landing pad for `"C-unwind"` calls under `panic=abort`; the Rust Reference's restriction on linking crates with different panic strategies (`link.unwinding`, two of its three potentially-unwinding clauses); per-crate panic-in-drop settings; and code generators that emit frame-unwind information but no landing pads. Each correspondence is a separate `derived (modeling bridge)` claim (Findings, "Sources and modeling bridge").

Known gaps: function bodies are straight-line (no branches or loops; recursion through calls is allowed); three ABIs (`rust`, `c`, `cUnwind`), and no other ABI is modelled; no indirect calls through function pointers, no inline assembly, no forced unwinding, no panics during cleanup (a cleanup pad atomically records its drop events), no asynchronous exceptions; the third clause of the Reference's potentially-unwinding definition (separate runtime copies) and dynamically loaded code are not modelled; one precedence function is used for all crates; a stopping pad at a call site is executed even when the caller's crate classified the callee as non-unwinding; `catchPad` stops every unwind, including foreign unwinds and unwinds inside `abort`-strategy crates; the toy pass replaces a `cleanup ds` action at a padded site by `terminate` and drops `ds` (rustc's pass keeps the cleanup block, B3); out-of-range function and crate indices denote `FnDef.dummy` and `CrateCfg.dflt`; `Exec` contains finite runs only; chains are not derived from programs; values are natural numbers with one return value per frame; code that cannot be unwound through at all (no frame-unwind information) corresponds to no `Pads` value.

Model–system relation: none proved. These are statements about two toy models (a program model and a call-chain model); they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules, any compiler backend or any Rust toolchain. Backend landing-pad capabilities (`Pads`) are toy parameters; no capability or defect of any real backend is asserted.

**Toolchain.** Lean `v4.34.1` (`leanprover/lean4`, tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean and `Std` without Mathlib; the Lake project in `lean/` has no `require` and builds on its own.

**Subjects and their relation.** The Lean toolchain is the checker of every theorem in this package. The `rust-lang/rust`, `rust-lang/rfcs`, `rust-lang/reference` and `llvm/llvm-project` revisions listed under Evidence are sources of source and documentation text quoted verbatim in the modeling bridge (Findings); nothing from them was executed or measured, and they are related to the toy definitions only by the design correspondences stated there. The papers and the WG21 paper listed under Evidence are prior art cited by the result cards; none of them is a dependency of any proof. Other reports of the same corpus are cited by name as related work; none is a dependency.

**Modules.** `Basic.lean` (program model, hypotheses, toy pass, backends), `Chain.lean` (chain model), `Decide.lean` (Boolean checkers with soundness lemmas, used to establish facts about concrete programs by `decide`), `Results.lean` (the main theorems of R1–R11, R16 and R17, except `abortAll_progAbortImportPlain_ub` of R5, which is in `Counterexamples.lean`; and lemmas), `ChainResults.lean` (R12–R15, R18), `Examples.lean` (definition examples and example programs), `Counterexamples.lean` (counterexamples, non-vacuity witnesses, positive control, refutations). Declarations not cited in this report are proof support.

The package name says "unwind-capability lattice" informally: the toy has a two-valued classification (possibly unwinding or non-unwinding), ordered rule lists that compute it, and a two-valued landing-pad capability (`full`, `none`); no order-theoretic lattice is formalized.

## Findings

### The model

Every block is a verbatim quote of the Lean source with its `file:A-B` range; a theorem quote ends with an elided proof (`:= …` or `:= by …`). Every theorem quoted in this report is fully proved.

#### Settings, static facts, precedence functions

```lean
-- lean/ToyUnwindCap/Basic.lean:33-36
inductive Strategy where
  | unwind
  | abort
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:39-41
def Strategy.unwinds : Strategy → Bool
  | .unwind => true
  | .abort => false
```

```lean
-- lean/ToyUnwindCap/Basic.lean:45-49
inductive Abi where
  | rust
  | c
  | cUnwind
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:52-55
structure CrateCfg where
  panic : Strategy
  panicInDrop : Strategy
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:60-65
structure FnInfo where
  abi : Abi
  foreign : Bool
  neverUnwind : Bool
  dropGlue : Bool
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:70-70
abbrev Prec := CrateCfg → FnInfo → Bool
```

```lean
-- lean/ToyUnwindCap/Basic.lean:76-79
def abiCanUnwind (c : CrateCfg) : Abi → Bool
  | .rust => c.panic.unwinds
  | .c => false
  | .cUnwind => true
```

```lean
-- lean/ToyUnwindCap/Basic.lean:82-82
abbrev Rule := CrateCfg → FnInfo → Option Bool
```

```lean
-- lean/ToyUnwindCap/Basic.lean:85-85
def ruleAttr : Rule := fun _ i => if i.neverUnwind then some false else none
```

```lean
-- lean/ToyUnwindCap/Basic.lean:88-89
def ruleAbortNonForeign : Rule := fun c i =>
  if !c.panic.unwinds && !i.foreign then some false else none
```

```lean
-- lean/ToyUnwindCap/Basic.lean:92-93
def ruleDropGlue : Rule := fun c i =>
  if i.dropGlue && !c.panicInDrop.unwinds then some false else none
```

```lean
-- lean/ToyUnwindCap/Basic.lean:96-96
def ruleAbi : Rule := fun c i => some (abiCanUnwind c i.abi)
```

```lean
-- lean/ToyUnwindCap/Basic.lean:100-100
def ruleAbortAll : Rule := fun c _ => if !c.panic.unwinds then some false else none
```

```lean
-- lean/ToyUnwindCap/Basic.lean:104-109
def evalRules : List Rule → Prec
  | [], c, i => abiCanUnwind c i.abi
  | r :: rs, c, i =>
    match r c i with
    | some b => b
    | none => evalRules rs c i
```

```lean
-- lean/ToyUnwindCap/Basic.lean:113-113
def stdOrder : List Rule := [ruleAttr, ruleAbortNonForeign, ruleDropGlue, ruleAbi]
```

*Intent of `stdCanUnwind`:* Captures the ordered rule list of rustc's `fn_can_unwind` (attribute → abort-and-not-foreign → drop glue under panic-in-drop = abort → ABI), restricted to three ABIs.

```lean
-- lean/ToyUnwindCap/Basic.lean:116-116
def stdCanUnwind : Prec := evalRules stdOrder
```

```lean
-- lean/ToyUnwindCap/Basic.lean:119-119
def abiFirstOrder : List Rule := [ruleAttr, ruleAbi, ruleAbortNonForeign, ruleDropGlue]
```

```lean
-- lean/ToyUnwindCap/Basic.lean:122-122
def abiFirstCanUnwind : Prec := evalRules abiFirstOrder
```

```lean
-- lean/ToyUnwindCap/Basic.lean:125-125
def abortAllOrder : List Rule := [ruleAttr, ruleAbortAll, ruleDropGlue, ruleAbi]
```

```lean
-- lean/ToyUnwindCap/Basic.lean:128-128
def abortAllCanUnwind : Prec := evalRules abortAllOrder
```

#### Programs

```lean
-- lean/ToyUnwindCap/Basic.lean:135-140
inductive Action where
  | none
  | cleanup (locals : List Nat)
  | catchPad
  | terminate
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:143-146
def Action.Stops : Action → Bool
  | .catchPad => true
  | .terminate => true
  | _ => false
```

```lean
-- lean/ToyUnwindCap/Basic.lean:157-160
inductive Stmt where
  | raise (act : Action)
  | call (f : Nat) (act : Action)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:165-170
structure FnDef where
  info : FnInfo
  crate : Nat
  body : List Stmt
  throws : Bool
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:174-178
structure Prog where
  crates : List CrateCfg
  fns : List FnDef
  handler : Strategy
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:182-184
def FnDef.dummy : FnDef :=
  { info := { abi := .rust, foreign := false, neverUnwind := false, dropGlue := false },
    crate := 0, body := [], throws := false }
```

```lean
-- lean/ToyUnwindCap/Basic.lean:187-187
def CrateCfg.dflt : CrateCfg := ⟨.unwind, .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Basic.lean:190-190
def Prog.fn (p : Prog) (f : Nat) : FnDef := p.fns.getD f FnDef.dummy
```

```lean
-- lean/ToyUnwindCap/Basic.lean:193-193
theorem Prog.fn_of_ge (p : Prog) {g : Nat} (h : p.fns.length ≤ g) : p.fn g = FnDef.dummy := by …
```

```lean
-- lean/ToyUnwindCap/Basic.lean:199-199
def Prog.crateOf (p : Prog) (f : Nat) : CrateCfg := p.crates.getD (p.fn f).crate CrateCfg.dflt
```

```lean
-- lean/ToyUnwindCap/Basic.lean:203-203
def Prog.selfMay (p : Prog) (cu : Prec) (f : Nat) : Bool := cu (p.crateOf f) (p.fn f).info
```

```lean
-- lean/ToyUnwindCap/Basic.lean:206-206
def Prog.viewMay (p : Prog) (cu : Prec) (g f : Nat) : Bool := cu (p.crateOf g) (p.fn f).info
```

#### Semantics

```lean
-- lean/ToyUnwindCap/Basic.lean:212-215
inductive Event where
  | drop (fn x : Nat)
  | caught (fn : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:219-224
inductive Outcome where
  | ret
  | unwind
  | abort
  | ub
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:227-227
abbrev Run := List Event × Outcome
```

```lean
-- lean/ToyUnwindCap/Basic.lean:230-230
def prependRuns (t : List Event) (rs : List Run) : List Run := rs.map fun r => (t ++ r.1, r.2)
```

```lean
-- lean/ToyUnwindCap/Basic.lean:235-240
def onUnwind (g : Nat) (assumed : Bool) (act : Action) (k : List Run) : List Run :=
  match act with
  | .terminate => [([], .abort)]
  | .catchPad => prependRuns [Event.caught g] k
  | .none => if assumed then [([], .ub)] else [([], .unwind)]
  | .cleanup ds => if assumed then [([], .ub)] else [(ds.map (Event.drop g), .unwind)]
```

```lean
-- lean/ToyUnwindCap/Basic.lean:243-255
def execBody (cu : Prec) (p : Prog) (callee : Nat → List Run) (g : Nat) : List Stmt → List Run
  | [] => [([], .ret)]
  | .raise act :: rest =>
    match p.handler with
    | .abort => [([], .abort)]
    | .unwind => onUnwind g false act (execBody cu p callee g rest)
  | .call f act :: rest =>
    (callee f).flatMap fun r =>
      match r.2 with
      | .ret => prependRuns r.1 (execBody cu p callee g rest)
      | .unwind => prependRuns r.1 (onUnwind g (!p.viewMay cu g f) act (execBody cu p callee g rest))
      | .abort => [(r.1, .abort)]
      | .ub => [(r.1, .ub)]
```

```lean
-- lean/ToyUnwindCap/Basic.lean:259-262
def boundary (cu : Prec) (p : Prog) (f : Nat) (r : Run) : Run :=
  match r.2 with
  | .unwind => if p.selfMay cu f then r else (r.1, .ub)
  | _ => r
```

*Intent of `runFn`:* Executable semantics: every finite run with call depth below the fuel.

```lean
-- lean/ToyUnwindCap/Basic.lean:266-271
def runFn (cu : Prec) (p : Prog) : Nat → Nat → List Run
  | 0, _ => []
  | n + 1, f =>
    if (p.fn f).info.foreign then
      ([], .ret) :: (if (p.fn f).throws then [boundary cu p f ([], .unwind)] else [])
    else (execBody cu p (runFn cu p n) f (p.fn f).body).map (boundary cu p f)
```

```lean
-- lean/ToyUnwindCap/Basic.lean:275-276
def Exec (cu : Prec) (p : Prog) (f : Nat) (t : List Event) (o : Outcome) : Prop :=
  ∃ n, (t, o) ∈ runFn cu p n f
```

#### Hypotheses

*Intent of `EnforcedAt` and `Enforced`:* Capture the obligation that a compiler pass such as rustc's abort-on-unwind insertion discharges: a function classified as non-unwinding stops every unwinding source it knows of. Panic points are constrained under the `unwind` handler, and are not constrained under the `abort` handler, where they abort without unwinding. `Enforced` quantifies over every function index, reachable or not.

```lean
-- lean/ToyUnwindCap/Basic.lean:285-288
def EnforcedAt (cu : Prec) (p : Prog) (g : Nat) : Prop :=
  (p.fn g).info.foreign = false → p.selfMay cu g = false →
    (p.handler = .unwind → ∀ act, Stmt.raise act ∈ (p.fn g).body → act.Stops = true) ∧
    (∀ f act, Stmt.call f act ∈ (p.fn g).body → p.viewMay cu g f = true → act.Stops = true)
```

```lean
-- lean/ToyUnwindCap/Basic.lean:291-291
def Enforced (cu : Prec) (p : Prog) : Prop := ∀ g, EnforcedAt cu p g
```

```lean
-- lean/ToyUnwindCap/Basic.lean:295-296
def ForeignCovered (cu : Prec) (p : Prog) : Prop :=
  ∀ f, (p.fn f).info.foreign = true → (p.fn f).throws = true → p.selfMay cu f = true
```

*Intent of `SiteAgreementAt` and `SiteAgreement`:* Capture cross-crate agreement: a caller's "callee cannot unwind" assumption is backed by the callee's own classification. `SiteAgreement` quantifies over every function index and call site, reachable or not.

```lean
-- lean/ToyUnwindCap/Basic.lean:301-303
def SiteAgreementAt (cu : Prec) (p : Prog) (g : Nat) : Prop :=
  ∀ f act, (p.fn g).info.foreign = false → Stmt.call f act ∈ (p.fn g).body →
    act.Stops = false → p.viewMay cu g f = false → p.selfMay cu f = false
```

```lean
-- lean/ToyUnwindCap/Basic.lean:306-306
def SiteAgreement (cu : Prec) (p : Prog) : Prop := ∀ g, SiteAgreementAt cu p g
```

```lean
-- lean/ToyUnwindCap/Basic.lean:310-312
def ForeignHonest (p : Prog) : Prop :=
  ∀ f, (p.fn f).info.foreign = true → (p.fn f).throws = true →
    (p.fn f).info.abi = .cUnwind ∧ (p.fn f).info.neverUnwind = false
```

```lean
-- lean/ToyUnwindCap/Basic.lean:315-316
def ForeignNotGlue (p : Prog) : Prop :=
  ∀ f, (p.fn f).info.foreign = true → (p.fn f).info.dropGlue = false
```

```lean
-- lean/ToyUnwindCap/Basic.lean:321-322
def PrecForeignSound (cu : Prec) : Prop :=
  ∀ p, ForeignHonest p → ForeignNotGlue p → ForeignCovered cu p
```

```lean
-- lean/ToyUnwindCap/Basic.lean:329-332
def PotentiallyUnwinding (p : Prog) : Prop :=
  p.handler = .unwind ∨
  ∃ g f act, (p.fn g).info.foreign = false ∧ (p.crateOf g).panic = .unwind ∧
    Stmt.call f act ∈ (p.fn g).body ∧ (p.fn f).info.abi = .cUnwind
```

*Intent of `LinkOK`:* Toy reading of the Reference's `link.unwinding` rule (two of its three potentially-unwinding clauses).

```lean
-- lean/ToyUnwindCap/Basic.lean:336-337
def LinkOK (p : Prog) : Prop :=
  PotentiallyUnwinding p → ∀ c ∈ p.crates, c.panic = .unwind
```

*Intent of `GlueAgreement`:* Captures agreement of per-crate panic-in-drop settings at drop-glue call sites that omit unwind handling.

```lean
-- lean/ToyUnwindCap/Basic.lean:342-345
def GlueAgreement (p : Prog) : Prop :=
  ∀ g f act, (p.fn g).info.foreign = false → Stmt.call f act ∈ (p.fn g).body →
    (p.fn f).info.dropGlue = true → act.Stops = false →
    (p.crateOf g).panicInDrop = .abort → (p.crateOf f).panicInDrop = .abort
```

#### Toy codegen and backends

```lean
-- lean/ToyUnwindCap/Basic.lean:354-356
def padStmt (cu : Prec) (p : Prog) (g : Nat) : Stmt → Stmt
  | .raise act => .raise (if p.handler.unwinds && !act.Stops then .terminate else act)
  | .call f act => .call f (if p.viewMay cu g f && !act.Stops then .terminate else act)
```

```lean
-- lean/ToyUnwindCap/Basic.lean:360-363
def padFn (cu : Prec) (p : Prog) (g : Nat) (d : FnDef) : FnDef :=
  if !d.info.foreign && !cu (p.crates.getD d.crate CrateCfg.dflt) d.info then
    { d with body := d.body.map (padStmt cu p g) }
  else d
```

```lean
-- lean/ToyUnwindCap/Basic.lean:367-368
def insertPads (cu : Prec) (p : Prog) : Prog :=
  { p with fns := p.fns.mapIdx (padFn cu p) }
```

```lean
-- lean/ToyUnwindCap/Basic.lean:378-381
inductive Pads where
  | full
  | none
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:384-386
def Stmt.unpadded : Stmt → Stmt
  | .raise _ => .raise .none
  | .call f _ => .call f .none
```

*Intent of `Prog.withPads`:* The program as compiled when `pads = none` backends cannot emit landing pads.

```lean
-- lean/ToyUnwindCap/Basic.lean:390-394
def Prog.withPads (p : Prog) (pads : Nat → Pads) : Prog :=
  { p with fns := p.fns.mapIdx fun g d =>
      match pads g with
      | .full => d
      | .none => { d with body := d.body.map Stmt.unpadded } }
```

#### Drop-glue family

```lean
-- lean/ToyUnwindCap/Results.lean:682-682
def glueInfo : FnInfo := { abi := .rust, foreign := false, neverUnwind := false, dropGlue := true }
```

```lean
-- lean/ToyUnwindCap/Results.lean:685-685
def rustInfo : FnInfo := { abi := .rust, foreign := false, neverUnwind := false, dropGlue := false }
```

```lean
-- lean/ToyUnwindCap/Results.lean:690-694
def glueProg (cc cg : CrateCfg) (act : Action) (body : List Stmt) : Prog :=
  { crates := [cc, cg],
    fns := [{ info := rustInfo, crate := 0, body := [.call 1 act], throws := false },
            { info := glueInfo, crate := 1, body := body, throws := false }],
    handler := .unwind }
```

```lean
-- lean/ToyUnwindCap/Results.lean:699-701
def GlueSiteSound (cc cg : CrateCfg) (act : Action) : Prop :=
  ∀ body, Enforced stdCanUnwind (glueProg cc cg act body) →
    ∀ t o, Exec stdCanUnwind (glueProg cc cg act body) 0 t o → o ≠ .ub
```

```lean
-- lean/ToyUnwindCap/Results.lean:229-229
def abortCfg : CrateCfg := ⟨.abort, .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Results.lean:232-232
def rustDefinedCUnwind : FnInfo := ⟨.cUnwind, false, false, false⟩
```

#### Chain model

```lean
-- lean/ToyUnwindCap/Chain.lean:28-30
structure AbiCodec where
  enc : Nat → Nat
  dec : Nat → Nat
```

```lean
-- lean/ToyUnwindCap/Chain.lean:33-33
def AbiCodec.Lawful (a : AbiCodec) : Prop := ∀ v, a.dec (a.enc v) = v
```

```lean
-- lean/ToyUnwindCap/Chain.lean:36-36
def Conforms (b A : AbiCodec) : Prop := b.enc = A.enc ∧ b.dec = A.dec
```

```lean
-- lean/ToyUnwindCap/Chain.lean:40-42
structure RetFrame where
  backend : AbiCodec
  k : Nat → Nat
```

```lean
-- lean/ToyUnwindCap/Chain.lean:46-48
def specRet : List RetFrame → Nat → Nat
  | [], v => v
  | fr :: rest, v => specRet rest (fr.k v)
```

```lean
-- lean/ToyUnwindCap/Chain.lean:53-55
def compRet : AbiCodec → List RetFrame → Nat → Nat
  | _, [], v => v
  | b, fr :: rest, v => compRet fr.backend rest (fr.k (fr.backend.dec (b.enc v)))
```

```lean
-- lean/ToyUnwindCap/Chain.lean:61-64
structure UFrame where
  pads : Pads
  act : Action
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Chain.lean:68-71
inductive UEvent where
  | drop (frame x : Nat)
  | caught (frame : Nat)
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Chain.lean:74-76
def UEvent.frame : UEvent → Nat
  | .drop i _ => i
  | .caught i => i
```

```lean
-- lean/ToyUnwindCap/Chain.lean:80-84
inductive UOut where
  | escapes
  | caught (frame : Nat)
  | aborted
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyUnwindCap/Basic.lean:150-154
def Action.obligation : Action → Bool
  | .none => false
  | .cleanup ds => !ds.isEmpty
  | .catchPad => true
  | .terminate => true
```

```lean
-- lean/ToyUnwindCap/Chain.lean:89-92
def UFrame.effAct (fr : UFrame) : Action :=
  match fr.pads with
  | .full => fr.act
  | .none => .none
```

```lean
-- lean/ToyUnwindCap/Chain.lean:95-104
def unwindWith (actOf : UFrame → Action) : Nat → List UFrame → List UEvent × UOut
  | _, [] => ([], .escapes)
  | i, fr :: rest =>
    match actOf fr with
    | .none => unwindWith actOf (i + 1) rest
    | .cleanup ds =>
      let r := unwindWith actOf (i + 1) rest
      (ds.map (UEvent.drop i) ++ r.1, r.2)
    | .catchPad => ([.caught i], .caught i)
    | .terminate => ([], .aborted)
```

```lean
-- lean/ToyUnwindCap/Chain.lean:107-107
def specUnwind (c : List UFrame) : List UEvent × UOut := unwindWith UFrame.act 0 c
```

*Intent of `compUnwind`:* Compiled unwind through a chain: `pads = none` frames perform no landing-pad action.

```lean
-- lean/ToyUnwindCap/Chain.lean:110-110
def compUnwind (c : List UFrame) : List UEvent × UOut := unwindWith UFrame.effAct 0 c
```

```lean
-- lean/ToyUnwindCap/Chain.lean:114-117
def ObligationsFull : List UFrame → Prop
  | [] => True
  | fr :: rest =>
    (fr.act.obligation = true → fr.pads = .full) ∧ (fr.act.Stops = false → ObligationsFull rest)
```

*Intent of `NoReachedNoneTerminate`:* The side condition of the characterization of compiled unwinds: no frame that the specified unwind reaches is a `pads = none` frame with a terminate pad.

```lean
-- lean/ToyUnwindCap/Chain.lean:122-126
def NoReachedNoneTerminate : List UFrame → Prop
  | [] => True
  | fr :: rest =>
    (fr.pads = .none → fr.act ≠ .terminate) ∧
    (fr.act.Stops = false → NoReachedNoneTerminate rest)
```

```lean
-- lean/ToyUnwindCap/Chain.lean:131-133
def Shielded : List UFrame → Prop
  | [] => True
  | fr :: rest => fr.pads = .full ∧ (fr.act.Stops = true ∨ Shielded rest)
```

```lean
-- lean/ToyUnwindCap/Chain.lean:138-140
def TerminateShielded : List UFrame → Prop
  | [] => True
  | fr :: rest => fr.pads = .full ∧ (fr.act = .terminate ∨ TerminateShielded rest)
```

```lean
-- lean/ToyUnwindCap/Chain.lean:144-147
def SameShape : List UFrame → List UFrame → Prop
  | [], [] => True
  | a :: as, b :: bs => a.pads = b.pads ∧ (a.pads = .full → a.act = b.act) ∧ SameShape as bs
  | _, _ => False
```

#### Definition examples (all fully proved)

```lean
-- lean/ToyUnwindCap/Examples.lean:91-92
theorem stdCanUnwind_positive :
    stdCanUnwind unwindCfg rustInfo = true ∧ stdCanUnwind abortCfg foreignCUnwind = true := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:98-100
theorem stdCanUnwind_negative :
    stdCanUnwind abortCfg rustDefinedCUnwind = false ∧ stdCanUnwind unwindCfg cFn = false ∧
    stdCanUnwind pidAbortCfg glueInfo = false ∧ stdCanUnwind unwindCfg attrFn = false := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:105-107
theorem abiFirstCanUnwind_examples :
    abiFirstCanUnwind abortCfg rustDefinedCUnwind = true ∧
    abiFirstCanUnwind abortCfg rustInfo = false := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:112-114
theorem abortAllCanUnwind_examples :
    abortAllCanUnwind abortCfg foreignCUnwind = false ∧
    abortAllCanUnwind unwindCfg rustInfo = true := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:121-122
theorem exec_progUnwindCatch :
    Exec stdCanUnwind progUnwindCatch 0 [.drop 1 7, .caught 0] .ret := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:125-126
theorem exec_progUnwindCatch_fn1 :
    Exec stdCanUnwind progUnwindCatch 1 [.drop 1 7] .unwind := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:129-130
theorem exec_progAbortImportPadded_abort :
    Exec stdCanUnwind progAbortImportPadded 0 [] .abort := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:133-134
theorem exec_progAbortImportPlain_ub :
    Exec stdCanUnwind progAbortImportPlain 0 [] .ub := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:138-138
theorem enforced_progAbortImportPadded : Enforced stdCanUnwind progAbortImportPadded := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:143-143
theorem not_enforced_progAbortImportPlain : ¬ Enforced stdCanUnwind progAbortImportPlain := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:148-149
theorem foreignCovered_progAbortImportPadded :
    ForeignCovered stdCanUnwind progAbortImportPadded := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:154-154
theorem not_foreignCovered_progThrowingC : ¬ ForeignCovered stdCanUnwind progThrowingC := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:158-158
theorem siteAgreement_progUnwindCatch : SiteAgreement stdCanUnwind progUnwindCatch := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:163-164
theorem not_siteAgreement_progAbortCallsUnwind :
    ¬ SiteAgreement stdCanUnwind progAbortCallsUnwind := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:168-168
theorem foreignHonest_progAbortImportPadded : ForeignHonest progAbortImportPadded := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:171-171
theorem not_foreignHonest_progThrowingC : ¬ ForeignHonest progThrowingC := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:175-175
theorem foreignNotGlue_progAbortImportPadded : ForeignNotGlue progAbortImportPadded := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:178-178
theorem not_foreignNotGlue_progForeignGlue : ¬ ForeignNotGlue progForeignGlue := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:183-183
theorem potentiallyUnwinding_progUnwindCatch : PotentiallyUnwinding progUnwindCatch := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:188-191
theorem potentiallyUnwinding_unwindCrateCallsCUnwind :
    PotentiallyUnwinding
      ⟨[unwindCfg], [⟨rustInfo, 0, [.call 1 .terminate], false⟩, ⟨foreignCUnwind, 0, [], true⟩],
        .abort⟩ := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:194-194
theorem not_potentiallyUnwinding_progMixedLinkOK : ¬ PotentiallyUnwinding progMixedLinkOK := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:197-197
theorem linkOK_progMixedLinkOK : LinkOK progMixedLinkOK := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:202-202
theorem not_linkOK_progAbortCallsUnwind : ¬ LinkOK progAbortCallsUnwind := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:206-206
theorem glueAgreement_matching : GlueAgreement (glueProg pidAbortCfg pidAbortCfg .none []) := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:209-209
theorem not_glueAgreement_progGlueMismatch : ¬ GlueAgreement progGlueMismatch := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:215-216
theorem precForeignSound_examples :
    PrecForeignSound stdCanUnwind ∧ ¬ PrecForeignSound abortAllCanUnwind := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:222-223
theorem insertPads_progAbortImportPlain :
    insertPads stdCanUnwind progAbortImportPlain = progAbortImportPadded := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:227-228
theorem insertPads_progAbortCallsUnwind :
    insertPads stdCanUnwind progAbortCallsUnwind = progAbortCallsUnwind := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:236-239
theorem withPads_progUnwindCatch :
    (progUnwindCatch.withPads padsNoneAt0).fns.head? =
      some ⟨rustInfo, 0, [.call 1 .none], false⟩ ∧
    (progUnwindCatch.withPads padsNoneAt0).fns.tail = progUnwindCatch.fns.tail := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:243-244
def progAbortHandlerRaisePlain : Prog :=
  ⟨[abortCfg], [⟨rustInfo, 0, [.raise .none], false⟩], .abort⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:249-251
theorem enforced_handler_examples :
    Enforced stdCanUnwind progAbortHandlerRaisePlain ∧
    ¬ Enforced stdCanUnwind { progAbortHandlerRaisePlain with handler := .unwind } := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:258-261
theorem padStmt_raise_examples :
    padStmt stdCanUnwind progAbortHandlerRaisePlain 0 (.raise .none) = .raise .none ∧
    padStmt stdCanUnwind progPlainCallFromNounwind 0 (.raise (.cleanup [7])) =
      .raise .terminate := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:266-267
theorem glueSiteSound_examples :
    GlueSiteSound pidAbortCfg pidAbortCfg .none ∧ ¬ GlueSiteSound pidAbortCfg unwindCfg .none := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:285-285
theorem lawful_examples : idCodec.Lawful ∧ shiftCodec.Lawful ∧ ¬ truncCodec.Lawful := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:290-290
theorem conforms_examples : Conforms idCodec idCodec ∧ ¬ Conforms shiftCodec idCodec := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:297-301
theorem unwind_chain_example :
    compUnwind [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩] =
      ([.drop 0 1, .caught 2], .caught 2) ∧
    specUnwind [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩] =
      ([.drop 0 1, .caught 2], .caught 2) := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:304-306
theorem unwind_chain_skip_example :
    compUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] = ([.caught 1], .caught 1) ∧
    specUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] = ([.drop 0 1, .caught 1], .caught 1) := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:309-311
theorem obligationsFull_examples :
    ObligationsFull [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩, ⟨.none, .catchPad⟩] ∧
    ¬ ObligationsFull [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:314-317
theorem shielded_examples :
    Shielded [⟨.full, .catchPad⟩, ⟨.none, .none⟩] ∧ ¬ Shielded [⟨.none, .none⟩] ∧
    TerminateShielded [⟨.full, .none⟩, ⟨.full, .terminate⟩, ⟨.none, .none⟩] ∧
    ¬ TerminateShielded [⟨.full, .catchPad⟩, ⟨.none, .none⟩] := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:327-329
theorem sameShape_examples :
    SameShape [⟨.full, .catchPad⟩, ⟨.none, .none⟩] [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] ∧
    ¬ SameShape [⟨.full, .catchPad⟩] [⟨.full, .terminate⟩] := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:322-324
theorem noReachedNoneTerminate_examples :
    NoReachedNoneTerminate [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] ∧
    ¬ NoReachedNoneTerminate [⟨.none, .terminate⟩, ⟨.full, .terminate⟩] := by …
```

#### Example programs, settings and chains

```lean
-- lean/ToyUnwindCap/Examples.lean:17-17
def unwindCfg : CrateCfg := ⟨.unwind, .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:20-20
def pidAbortCfg : CrateCfg := ⟨.unwind, .abort⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:23-23
def cFn : FnInfo := ⟨.c, false, false, false⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:26-26
def foreignCUnwind : FnInfo := ⟨.cUnwind, true, false, false⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:29-29
def foreignC : FnInfo := ⟨.c, true, false, false⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:32-32
def attrFn : FnInfo := ⟨.rust, false, true, false⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:38-40
def progAbortImportPadded : Prog :=
  ⟨[abortCfg], [⟨rustInfo, 0, [.call 1 .terminate], false⟩, ⟨foreignCUnwind, 0, [], true⟩],
    .abort⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:43-44
def progAbortImportPlain : Prog :=
  ⟨[abortCfg], [⟨rustInfo, 0, [.call 1 .none], false⟩, ⟨foreignCUnwind, 0, [], true⟩], .abort⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:48-50
def progPlainCallFromNounwind : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 .none], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:53-53
def progThrowingC : Prog := ⟨[unwindCfg], [⟨foreignC, 0, [], true⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:57-59
def progAbortCallsUnwind : Prog :=
  ⟨[abortCfg, unwindCfg],
    [⟨rustInfo, 0, [.call 1 .none], false⟩, ⟨rustInfo, 1, [.raise .none], false⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:63-63
def progForeignGlue : Prog := ⟨[pidAbortCfg], [⟨⟨.cUnwind, true, false, true⟩, 0, [], true⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:67-67
def progGlueMismatch : Prog := glueProg pidAbortCfg unwindCfg .none [.raise .none]
```

```lean
-- lean/ToyUnwindCap/Examples.lean:74-78
def progMixedLinkOK : Prog :=
  ⟨[abortCfg, unwindCfg],
    [⟨rustInfo, 0, [.call 2 .terminate, .call 3 .none], false⟩,
      ⟨rustInfo, 1, [.call 0 .none], false⟩, ⟨foreignCUnwind, 0, [], true⟩,
      ⟨rustInfo, 1, [.raise .none], false⟩], .abort⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:82-85
def progUnwindCatch : Prog :=
  ⟨[unwindCfg],
    [⟨rustInfo, 0, [.call 1 .catchPad], false⟩, ⟨rustInfo, 0, [.call 2 (.cleanup [7])], false⟩,
      ⟨rustInfo, 0, [.raise .none], false⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:232-232
def padsNoneAt0 : Nat → Pads := fun g => if g = 0 then .none else .full
```

```lean
-- lean/ToyUnwindCap/Examples.lean:276-276
def idCodec : AbiCodec := ⟨id, id⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:279-279
def shiftCodec : AbiCodec := ⟨fun v => v + 1, fun w => w - 1⟩
```

```lean
-- lean/ToyUnwindCap/Examples.lean:283-283
def truncCodec : AbiCodec := ⟨fun v => v % 256, id⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:145-147
def progTerminateFromNounwind : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 .terminate], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:162-163
def progNounwindCallee : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 .none], false⟩, ⟨cFn, 0, [], false⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:178-180
def progForeignWithBody : Prog :=
  ⟨[unwindCfg], [⟨foreignC, 0, [.call 1 .none], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:194-196
def progUnreachableCall : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.raise .terminate, .call 1 .none], false⟩,
    ⟨rustInfo, 0, [.raise .none], false⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:517-519
def progPadsNonvac : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 (.cleanup [3])], false⟩, ⟨cFn, 0, [.call 2 .terminate], false⟩,
    ⟨rustInfo, 0, [.raise .none], false⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:575-577
def progPadsMayUnwind : Prog :=
  ⟨[unwindCfg], [⟨rustInfo, 0, [.call 1 (.cleanup [0])], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:613-615
def progPadsTerminate : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 .terminate], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:641-643
def progPadsAgree : Prog :=
  ⟨[abortCfg, unwindCfg], [⟨rustInfo, 0, [.call 1 .terminate], false⟩,
    ⟨rustInfo, 1, [.raise .none], false⟩], .unwind⟩
```

### Sources and modeling bridge

Retrieved 2026-11-21 (the LLVM excerpt on 2026-11-22) and compared again with the files at the pinned revisions on 2026-11-22. Each block is a verbatim copy of the cited line range. The evidence role of each source is given in parentheses.

**rustc `fn_can_unwind`** (source: implementation and its documentation comment; not normative).

`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/ty/layout.rs:1247-1264`

```rust
/// Rust functions are classified whether or not they can unwind based on the
/// active "panic strategy". In other words Rust functions are considered to
/// unwind in `-Cpanic=unwind` mode and cannot unwind in `-Cpanic=abort` mode.
/// Note that Rust supports intermingling panic=abort and panic=unwind code, but
/// only if the final panic mode is panic=abort. In this scenario any code
/// previously compiled assuming that a function can unwind is still correct, it
/// just never happens to actually unwind at runtime.
///
/// This function's answer to whether or not a function can unwind is quite
/// impactful throughout the compiler. This affects things like:
///
/// * Calling a function which can't unwind means codegen simply ignores any
///   associated unwinding cleanup.
/// * Calling a function which can unwind from a function which can't unwind
///   causes the `abort_unwinding_calls` MIR pass to insert a landing pad that
///   aborts the process.
/// * This affects whether functions have the LLVM `nounwind` attribute, which
///   affects various optimizations and codegen.
```

`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/ty/layout.rs:1267-1291`

```rust
pub fn fn_can_unwind(tcx: TyCtxt<'_>, fn_def_id: Option<DefId>, abi: ExternAbi) -> bool {
    if let Some(did) = fn_def_id {
        // Special attribute for functions which can't unwind.
        if tcx.codegen_fn_attrs(did).flags.contains(CodegenFnAttrFlags::NEVER_UNWIND) {
            return false;
        }

        // With `-C panic=abort`, all non-FFI functions are required to not unwind.
        //
        // Note that this is true regardless ABI specified on the function -- a `extern "C-unwind"`
        // function defined in Rust is also required to abort.
        if !tcx.sess.panic_strategy().unwinds() && !tcx.is_foreign_item(did) {
            return false;
        }

        // With -Z panic-in-drop=abort, `drop_glue` never unwinds.
        //
        // This is not part of `codegen_fn_attrs` as it can differ between crates
        // and therefore cannot be computed in core.
        if !tcx.sess.opts.unstable_opts.panic_in_drop.unwinds()
            && tcx.is_lang_item(did, LangItem::DropGlue)
        {
            return false;
        }
    }
```

`rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe:compiler/rustc_middle/src/ty/layout.rs:1326-1330`

```rust
        Rust | RustCall | RustCold | RustPreserveNone | RustTail => {
            tcx.sess.panic_strategy().unwinds()
        }
    }
}
```

**RFC 2945 ("C-unwind" ABI, merged)** (normative design document).

`rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/2945-c-unwind-abi.md:205-209`

```markdown
### Interaction with `panic=abort`

If a non-forced foreign unwind would enter a Rust frame via an `extern
"C-unwind"` ABI boundary, but the Rust code is compiled with `panic=abort`, the
unwind will be caught and the process aborted.
```

`rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/2945-c-unwind-abi.md:230-235`

```markdown
| panic runtime  | ABI          | `panic`-unwind                        | Unforced foreign unwind |
| -------------- | ------------ | ------------------------------------- | ----------------------- |
| `panic=unwind` | `"C-unwind"` | unwind                                | unwind                  |
| `panic=unwind` | `"C"`-like   | abort                                 | UB                      |
| `panic=abort`  | `"C-unwind"` | `panic!` aborts                       | abort                   |
| `panic=abort`  | `"C"`-like   | `panic!` aborts (no unwinding occurs) | UB                      |
```

`rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/2945-c-unwind-abi.md:366-375`

```markdown
#### Optimization with panic=abort

Using this proposal, the compiler is **almost always** able to reduce
overhead related to unwinding when using panic=abort. The one
exception is that invoking a "C-unwind" ABI still requires some kind
of minimal landing pad to trigger an abort. The expectation is that
very few functions will use the "C-unwind" boundary unless they truly
intend to unwind -- and, in that case, those functions are likely
using panic=unwind anyway, so this is not expected to make much
difference in practice.
```

**The Rust Reference** (documentation).

`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/panic.md:97-101`

```markdown
> [!NOTE]
> When compiling code with the `abort` panic strategy, the optimizer may assume that unwinding across Rust frames is impossible, which can result in both code-size and runtime speed improvements.

> [!NOTE]
> See [link.unwinding] for restrictions on linking crates with different panic strategies. An implication is that crates built with the `unwind` strategy can use the `abort` panic handler, but the `abort` strategy cannot use the `unwind` panic handler.
```

`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/panic.md:109-110`

```markdown
r[panic.unwind.destruction]
When a panic occurs, the `unwind` handler "unwinds" Rust frames, just as C++'s `throw` unwinds C++ frames, until the panic reaches the point of recovery (for instance at a thread boundary). This means that as the panic traverses Rust frames, live objects in those frames that [implement `Drop`][destructors] will have their `drop` methods called. Thus, when normal execution resumes, no-longer-accessible objects will have been "cleaned up" just as if they had gone out of scope normally.
```

`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/panic.md:124-128`

```markdown
r[panic.unwind.ffi.undefined]
Unwinding with the wrong ABI is undefined behavior:

* Causing an unwind into Rust code from a foreign function that was called via a function declaration or pointer declared with a non-unwinding ABI, such as `"C"`, `"system"`, etc. (For example, this case occurs when such a function written in C++ throws an exception that is uncaught and propagates to Rust.)
* Calling a Rust `extern` function that unwinds (with `extern "C-unwind"` or another ABI that permits unwinding) from code that does not support unwinding, such as code compiled with GCC or Clang using `-fno-exceptions`
```

`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/linkage.md:154-176`

```markdown
r[link.unwinding]
### Prohibited linkage and unwinding

r[link.unwinding.intro]
Panic unwinding can only be used if the binary is built consistently according to the following rules.

r[link.unwinding.potential]
A Rust artifact is called *potentially unwinding* if any of the following conditions is met:
- The artifact uses the [`unwind` panic handler][panic.panic_handler].
- The artifact contains a crate built with the `unwind` [panic strategy] that makes a call to a function using a `-unwind` ABI.
- The artifact makes a `"Rust"` ABI call to code running in another Rust artifact that has a separate copy of the Rust runtime, and that other artifact is potentially unwinding.

> [!NOTE]
> This definition captures whether a `"Rust"` ABI call inside a Rust artifact can ever unwind.

r[link.unwinding.prohibited]
If a Rust artifact is potentially unwinding, then all its crates must be built with the `unwind` [panic strategy]. Otherwise, unwinding can cause undefined behavior.

> [!NOTE]
> If you are using `rustc` to link, these rules are enforced automatically. If you are *not* using `rustc` to link, you must take care to ensure that unwinding is handled consistently across the entire binary. Linking without `rustc` includes using `dlopen` or similar facilities where linking is done by the system runtime without `rustc` being involved. This can only happen when mixing code with different [`-C panic`] flags, so most users do not have to be concerned about this.

> [!NOTE]
> To guarantee that a library will be sound (and linkable with `rustc`) regardless of the panic runtime used at link-time, the [`ffi_unwind_calls` lint] may be used. The lint flags any calls to `-unwind` foreign functions or function pointers.
```

**RFC 1513 ("Less unwinding", merged)** (normative design document).

`rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/1513-less-unwinding.md:108-111`

```text
* `unwind` - this is what the compiler implements by default today via the
  `invoke` LLVM instruction.
* `abort` - this will implement that `-Z no-landing-pads` does today, which is
  to disable the `invoke` instruction and use `call` instead everywhere.
```

`rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4:text/1513-less-unwinding.md:142-146`

```text
* Finally, the compiler will ensure that panic runtimes and compilation modes
  are not mismatched. For a final product (outputs that aren't rlibs) the
  `-C panic` mode of the panic runtime must match the final product itself. If
  the panic mode is `abort`, then no other validation is performed, but
  otherwise all crates in the DAG must have the same value of `-C panic`.
```

**The Rust Reference, catching foreign unwinds** (documentation).

`rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c:src/panic.md:130-134`

```text
r[panic.unwind.ffi.catch-foreign]
Catching a foreign unwinding operation (such as a C++ exception) using [`std::panic::catch_unwind`], [`std::thread::JoinHandle::join`], or by letting it propagate beyond the Rust `main()` function or thread root will have one of two behaviors, and it is unspecified which will occur:

* The process aborts.
* The function returns a [`Result::Err`] containing an opaque type.
```

**WG21 N3050** (D. Abrahams, R. Sharoni, D. Gregor, "Allowing Move Constructors to Throw (Rev. 1)", 2010-03-12, open-std.org/jtc1/sc22/wg21/docs/papers/2010/n3050.html; consulted 2026-11-21): proposes the C++ `noexcept` specification, with wording changes to `[except.spec]` and to `[except.terminate]` (`std::terminate`). Cited as prose; no excerpt is relied on.

**LLVM Language Reference Manual, `nounwind`** (documentation).

`llvm/llvm-project@a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4:llvm/docs/LangRef.rst:2177-2183` (tag `llvmorg-19.1.0`)

```text
``nounwind``
    This function attribute indicates that the function never raises an
    exception. If the function does raise an exception, its runtime
    behavior is undefined. However, functions marked nounwind may still
    trap or generate asynchronous exceptions. Exception handling schemes
    that are recognized by LLVM to handle asynchronous exceptions, such
    as SEH, will still provide their implementation defined semantics.
```

**Derived (modeling bridge) B1, rule order, linking restriction and `nounwind`.** The toy `stdCanUnwind` mirrors the order of the four rules in `fn_can_unwind` above (attribute, `abort` strategy for non-foreign functions, drop glue under panic-in-drop `abort`, ABI), with the ABI rule restricted to `rust`, `c` and `cUnwind`. The source evaluates the strategy and panic-in-drop rules with the settings of the session doing the classifying (`tcx.sess`), which is why the toy precedence function takes the classifying crate's settings and why a caller's crate and a callee's crate can disagree (`SiteAgreement`, `GlueAgreement`); the comment at layout.rs:1284-1285 states that the panic-in-drop setting "can differ between crates". The doc comment at layout.rs:1258-1262 states the two codegen consequences that the toy semantics encodes: calls to non-unwinding callees ignore unwinding cleanup, and calls to possibly-unwinding callees from non-unwinding functions get an aborting landing pad. The RFC's statement that invoking a "C-unwind" function under `panic=abort` still requires a minimal landing pad is what the toy terminate pad models (R6, positive control of R5). `LinkOK` is a toy reading of the Reference's `link.unwinding.potential` and `link.unwinding.prohibited` (its first two clauses; the third is not modelled). The LLVM sentence above is the reason the toy semantics records an unwind out of a non-unwinding function as `ub`. These are design correspondences, not proved relations: Model–system relation: none proved.

**Derived (modeling bridge) B2, RFC 1513 and the `abort` handler.** RFC 1513 describes the `abort` strategy as using `call` instead of `invoke` everywhere and states the final-product validation quoted above. The toy `abort` handler models a final product whose panics abort: a panic point then aborts without unwinding, so `Enforced` and `padStmt` do not constrain or change panic points under it, and `LinkOK` allows `abort` and `unwind` crates to be mixed in an artifact that is not potentially unwinding. Model–system relation: none proved.

**Derived (modeling bridge) B3, cleanup before abort.** The corpus report `rustc-cleanup-post-borrowck-false-edges-and-abort-unwinding-mir-lowering` documents that rustc's `AbortUnwindingCalls` keeps a cleanup block and turns its final resume into a terminate, so local destructors run before the abort. The toy `padStmt` instead replaces a `cleanup ds` action by `terminate` and drops `ds`; the toy codegen is therefore not a model of that pass's drop behaviour (R6 non-claims). Model–system relation: none proved.

**Derived (modeling bridge) B4, backends without landing pads.** `pads = none` models a backend that omits landing pads while the frame remains unwindable (frame-unwind information present). The Reference text quoted above (`src/panic.md:124-128`) makes unwinding into code compiled without unwinding support (for example `-fno-exceptions`) undefined behaviour; such code corresponds to no `Pads` value of the toy. Model–system relation: none proved.

**Derived (modeling bridge) B5, `catchPad` and `catch_unwind`.** In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`, quoted above); and RFC 1513 (lines 108-111, quoted above) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect. The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`. Model–system relation: none proved.

### Results

Each card gives the plain claim, kind and tier, the verbatim Lean statement, a prose rendering with the key definitions expanded, the hypothesis ledger (every hypothesis with its tightness, a kernel-checked counterexample stating that all other hypotheses hold and the conclusion fails, and the class of the witness), the depth, the non-vacuity witness, a positive control where applicable, prior art and the design question it informs. The non-claims of each card are under Boundaries.

#### R1. `noUB_of_enforced_of_foreignCovered_of_siteAgreement` (theorem)

**Plain claim.** For every precedence function `cu` and every toy program `p`: if `p` satisfies `Enforced cu p` (at every function index, reachable or not: if the function is non-foreign and its own crate classifies it as non-unwinding, then every call in its body to a callee that this crate classifies as possibly unwinding carries a stopping pad, `catchPad` or `terminate`, and, when the panic handler is `unwind`, every panic point in its body carries a stopping pad), `ForeignCovered cu p` (every foreign function that may unwind is classified as possibly unwinding by its declaring crate) and `SiteAgreement cu p` (at every function index, reachable or not, at every call site without a stopping pad in a non-foreign function: if the caller's crate classifies the callee as non-unwinding, so does the callee's own crate), then no finite run produced by the evaluator `runFn` (no `Exec cu p f t o`) of any function `f` has outcome `ub`. Because the semantics records an unwind leaving a function that its own crate classifies as non-unwinding as `ub` (`boundary`), under these hypotheses no such unwind occurs.

**Kind / tier.** theorem / T1. The underlying rules are documented (see prior art); this is a toy-model mechanization. The corpus report on rustc's MIR passes mechanizes `fn_can_unwind` and `AbortUnwindingCalls` for single bodies; no mechanized counterpart of this statement was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). `Enforced` is a toy reading of the aborting landing pads that rustc's `fn_can_unwind` documentation assigns to calls of possibly-unwinding callees from non-unwinding functions, and the `ub` outcome of an unwind leaving a non-unwinding function follows the LLVM `nounwind` text (B1); the reading of `catchPad` is limited by B5. No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:177-179
theorem noUB_of_enforced_of_foreignCovered_of_siteAgreement (cu : Prec) (p : Prog)
    (henf : Enforced cu p) (hfc : ForeignCovered cu p) (hsa : SiteAgreement cu p) :
    ∀ f t o, Exec cu p f t o → o ≠ .ub := by …
```

**Unfolded (prose):** `Enforced cu p` ≡ for every `g`, `EnforcedAt cu p g`, i.e. if `(p.fn g).info.foreign = false` and `p.selfMay cu g = false`, then (when `p.handler = .unwind`) every `Stmt.raise act` in `(p.fn g).body` has `act.Stops = true`, and every `Stmt.call f act` in that body with `p.viewMay cu g f = true` has `act.Stops = true`. `ForeignCovered cu p` ≡ for every `f`, `(p.fn f).info.foreign = true` and `(p.fn f).throws = true` imply `p.selfMay cu f = true`. `SiteAgreement cu p` ≡ for every `g`, `SiteAgreementAt cu p g`, i.e. for every `f` and `act`, if `(p.fn g).info.foreign = false`, `Stmt.call f act ∈ (p.fn g).body`, `act.Stops = false` and `p.viewMay cu g f = false`, then `p.selfMay cu f = false`. Here `p.selfMay cu f` is `cu (p.crateOf f) (p.fn f).info` (the classification of `f` by its own crate), `p.viewMay cu g f` is `cu (p.crateOf g) (p.fn f).info` (the classification of `f` by `g`'s crate), and `act.Stops` is true exactly for `catchPad` and `terminate`. `Exec cu p f t o` ≡ there is a fuel `n` with `(t, o) ∈ runFn cu p n f`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `henf : Enforced cu p` | a function classified as non-unwinding stops, with a catch or terminate pad, every unwinding source it knows of (the obligation the toy codegen discharges) | tight: counterexample `noUB_fails_without_enforced` (witness class: a 1-crate, 2-function program under `stdCanUnwind` (`progPlainCallFromNounwind`, handler `unwind`)) |
| `hfc : ForeignCovered cu p` | an unwind leaving a foreign function classified as non-unwinding by its declaring crate cannot be stopped by any pad inside that function | tight: counterexample `noUB_fails_without_foreignCovered` (witness class: a 1-crate program whose single function is a foreign `c`-ABI import that unwinds (`progThrowingC`)) |
| `hsa : SiteAgreement cu p` | a caller that omits unwind handling because its crate classifies the callee as non-unwinding relies on the callee's own classification (and hence on the callee's enforcement) | tight: counterexample `noUB_fails_without_siteAgreement` (witness class: a 2-crate, 2-function program with an `abort` crate calling an `unwind` crate under the `unwind` handler (`progAbortCallsUnwind`)) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:31-34
theorem noUB_fails_without_enforced :
    ForeignCovered stdCanUnwind progPlainCallFromNounwind ∧
    SiteAgreement stdCanUnwind progPlainCallFromNounwind ∧
    Exec stdCanUnwind progPlainCallFromNounwind 0 [] .ub := …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:38-40
theorem noUB_fails_without_foreignCovered :
    Enforced stdCanUnwind progThrowingC ∧ SiteAgreement stdCanUnwind progThrowingC ∧
    Exec stdCanUnwind progThrowingC 0 [] .ub := …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:44-47
theorem noUB_fails_without_siteAgreement :
    Enforced stdCanUnwind progAbortCallsUnwind ∧
    ForeignCovered stdCanUnwind progAbortCallsUnwind ∧
    Exec stdCanUnwind progAbortCallsUnwind 0 [] .ub := …
```

**Depth.** shallow.

**Non-vacuity witness.** progUnwindCatch (one unwind crate: a panic unwinds through a cleanup pad dropping local 7 and is caught; run [drop 1 7, caught 0] / ret) and progAbortImportPadded (abort crate calling a foreign C-unwind import through a terminate pad; run [] / abort) satisfy all three hypotheses under stdCanUnwind.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:16-19
theorem noUB_hypotheses_hold_progUnwindCatch :
    Enforced stdCanUnwind progUnwindCatch ∧ ForeignCovered stdCanUnwind progUnwindCatch ∧
    SiteAgreement stdCanUnwind progUnwindCatch ∧
    Exec stdCanUnwind progUnwindCatch 0 [.drop 1 7, .caught 0] .ret := …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:23-27
theorem noUB_hypotheses_hold_progAbortImportPadded :
    Enforced stdCanUnwind progAbortImportPadded ∧
    ForeignCovered stdCanUnwind progAbortImportPadded ∧
    SiteAgreement stdCanUnwind progAbortImportPadded ∧
    Exec stdCanUnwind progAbortImportPadded 0 [] .abort := …
```

**Non-claims.** Listed under Boundaries, R1; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- llvm/llvm-project@a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4 (tag llvmorg-19.1.0) llvm/docs/LangRef.rst:2177-2183 (`nounwind` function attribute: the function never raises an exception, and if it does its runtime behaviour is undefined; quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/1513-less-unwinding.md:108-111 (the `abort` strategy replaces `invoke` by `call`) and 142-146 (final-product validation: if the panic mode is `abort` no other validation is performed, otherwise all crates must agree) (RFC 1513, merged; quoted verbatim in REPORT.md)
- D. Abrahams, R. Sharoni, D. Gregor, "Allowing Move Constructors to Throw (Rev. 1)", ISO/IEC JTC1/SC22/WG21 N3050, 2010-03-12 (open-std.org/jtc1/sc22/wg21/docs/papers/2010/n3050.html): proposes the C++ `noexcept` specification together with wording changes to `[except.spec]` and `[except.terminate]` (`std::terminate`); the C++ analogue of enforcing a non-unwinding declaration by termination. No mechanized semantics.
- Corpus report `rustc-cleanup-post-borrowck-false-edges-and-abort-unwinding-mir-lowering`: documents rustc's MIR passes between analysis and runtime MIR, including `AbortUnwindingCalls`, at pinned rustc revisions, and contains a kernel-checked Lean v4.34.1 mechanization (`support/CleanupPostBorrowckAndAbortCalls.lean`) of intra-procedural MIR semantics, `fn_can_unwind` and `AbortUnwindingCalls` (which keeps cleanup blocks and turns their final resume into a terminate) with end-to-end lowering theorems; by its own scope note it does not model linker-level cross-crate panic-strategy checks. This package does not depend on it; its additions are precedence functions as parameters, cross-crate classification disagreement (`SiteAgreement`), the linking restriction, per-crate panic-in-drop, and mixed landing-pad capabilities.
- Related reports of the same corpus (Lean formalizations), cited and not repeated (descriptions checked against their REPORT.md): `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction` (drop elaboration with drop flags, cleanup edges and the double-panic rule), `panic-safety-unwinding-through-broken-invariants-leak-amplification-and-safe-forget` (panic-safety obligations of unsafe collection code under unwinding), `call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations` (call-site inlining in a MIR-like language, including unwind actions and cleanup), `cfg-dwarf-cfi-state-stack-and-lsda-landing-pad-unwinding-soundness` (DWARF-style call-frame information and LSDA-style call-site tables over a given frame list), `explicit-tail-calls-frame-reuse-pre-jump-drop-order-stack-borrow-rejection-and-inlining` (a frame-stack machine with guaranteed tail calls, destructors and frame reuse). None of them treats whether a function may unwind as a classification made by a crate.
- Novelty search (2026-11-21, web search, not exhaustive): no mechanized soundness statement for a non-unwinding classification with terminate-pad placement and cross-crate agreement conditions was found; tier T1 (documented rules, made precise in a toy model).

**Design question.** When may a compiler omit landing pads at call sites inside functions it classifies as non-unwinding, and which program-wide facts (foreign code honouring its declared ABI, cross-crate agreement of classifications) make that sound?

#### R2. `foreignCovered_std_of_foreignHonest_of_foreignNotGlue` (theorem)

**Plain claim.** For every toy program `p` satisfying `ForeignHonest p` (every foreign function that may unwind is declared with the `cUnwind` ABI and without the never-unwind attribute) and `ForeignNotGlue p` (no foreign function is drop glue), the standard precedence function `stdCanUnwind` (ordered rules: never-unwind attribute, then `abort` strategy for non-foreign functions, then drop glue under panic-in-drop `abort`, then the ABI) satisfies `ForeignCovered stdCanUnwind p`.

**Kind / tier.** theorem / T0. A known fact restated in the package's vocabulary (see prior art); kept as a reference point.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). `stdCanUnwind` mirrors the order of the four rules of the quoted `fn_can_unwind` source, with three ABIs (B1). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:194-195
theorem foreignCovered_std_of_foreignHonest_of_foreignNotGlue (p : Prog)
    (hh : ForeignHonest p) (hng : ForeignNotGlue p) : ForeignCovered stdCanUnwind p := by …
```

**Unfolded (prose):** `ForeignHonest p` ≡ for every `f`, if `(p.fn f).info.foreign = true` and `(p.fn f).throws = true` then `(p.fn f).info.abi = .cUnwind` and `(p.fn f).info.neverUnwind = false`. `ForeignNotGlue p` ≡ for every `f`, `(p.fn f).info.foreign = true` implies `(p.fn f).info.dropGlue = false`. `stdCanUnwind c i` evaluates four rules in order and returns the verdict of the first one that applies: the never-unwind attribute gives `false`; strategy `abort` of `c` for a non-foreign `i` gives `false`; drop glue under panic-in-drop `abort` of `c` gives `false`; otherwise the ABI decides (`rust` gives `c.panic.unwinds`, `c` gives `false`, `cUnwind` gives `true`). `ForeignCovered` is as in R1.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hh : ForeignHonest p` | a foreign function declared `c` (or with the never-unwind attribute) that unwinds is classified as non-unwinding by `stdCanUnwind` | tight: counterexample `foreignCovered_std_fails_without_foreignHonest` (witness class: a 1-crate program whose single function is a foreign `c`-ABI import that unwinds (`progThrowingC`)) |
| `hng : ForeignNotGlue p` | well-formedness; the drop-glue rule would otherwise classify a foreign function as non-unwinding | tight: counterexample `foreignCovered_std_fails_without_foreignNotGlue` (witness class: a 1-crate, 1-function toy encoding whose function is both foreign and drop glue (`progForeignGlue`); an encoding artifact, since real drop glue is not a foreign item) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:57-58
theorem foreignCovered_std_fails_without_foreignHonest :
    ForeignNotGlue progThrowingC ∧ ¬ ForeignCovered stdCanUnwind progThrowingC := …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:61-62
theorem foreignCovered_std_fails_without_foreignNotGlue :
    ForeignHonest progForeignGlue ∧ ¬ ForeignCovered stdCanUnwind progForeignGlue := by …
```

**Depth.** definitional.

**Non-vacuity witness.** progAbortImportPadded (a throwing foreign C-unwind import) satisfies both hypotheses.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:53-54
theorem foreignCovered_std_hypotheses_hold_progAbortImportPadded :
    ForeignHonest progAbortImportPadded ∧ ForeignNotGlue progAbortImportPadded := …
```

**Non-claims.** Listed under Boundaries, R2; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)
- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c src/panic.md:86-101 (`panic.strategy`), 103-116 (`panic.unwind`), 124-128 (`panic.unwind.ffi.undefined`), 130-134 (`panic.unwind.ffi.catch-foreign`)

**Design question.** When may a compiler omit landing pads at call sites inside functions it classifies as non-unwinding, and which program-wide facts (foreign code honouring its declared ABI, cross-crate agreement of classifications) make that sound?

#### R3. `precForeignSound_iff` (characterization)

**Plain claim.** For every precedence function `cu`: `PrecForeignSound cu` (in every program satisfying `ForeignHonest` and `ForeignNotGlue`, `cu` classifies every foreign function that may unwind as possibly unwinding) holds iff `cu c i = true` for every crate setting `c` and every static-facts value `i : FnInfo` that is foreign, has the `cUnwind` ABI, lacks the never-unwind attribute and is not drop glue.

**Kind / tier.** characterization / T1. The underlying rules are documented (see prior art); this is a toy-model mechanization. The corpus report on rustc's MIR passes mechanizes `fn_can_unwind` and `AbortUnwindingCalls` for single bodies; no mechanized counterpart of this statement was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). Precedence functions are toy counterparts of orderings of the `fn_can_unwind` rules (B1). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:203-206
theorem precForeignSound_iff (cu : Prec) :
    PrecForeignSound cu ↔
      ∀ c i, i.foreign = true → i.abi = .cUnwind → i.neverUnwind = false → i.dropGlue = false →
        cu c i = true := by …
```

**Unfolded (prose):** `PrecForeignSound cu` ≡ for every program `p`, `ForeignHonest p` and `ForeignNotGlue p` imply `ForeignCovered cu p` (definitions as in R1 and R2). The right-hand side quantifies over all crate settings `c : CrateCfg` and all static facts `i : FnInfo`.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** stdCanUnwind satisfies the right-hand side; abortAllCanUnwind violates it at (abortCfg, foreignCUnwind).

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:70-74
theorem precForeignSound_iff_instances :
    (∀ c i, i.foreign = true → i.abi = .cUnwind → i.neverUnwind = false → i.dropGlue = false →
        stdCanUnwind c i = true) ∧
    ¬ (∀ c i, i.foreign = true → i.abi = .cUnwind → i.neverUnwind = false →
        i.dropGlue = false → abortAllCanUnwind c i = true) := by …
```

**Non-claims.** Listed under Boundaries, R3; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)

**Design question.** Is the order of the non-unwinding classification rules a free implementation choice among sound orders?

#### R4. `std_and_abiFirst_foreignSound_but_differ` (theorem)

**Plain claim.** `stdCanUnwind` and `abiFirstCanUnwind` (the same rules with the ABI rule consulted before the strategy rule) both satisfy `PrecForeignSound`; for every crate setting `c` and every `i : FnInfo`, if `abiFirstCanUnwind c i = false` then `stdCanUnwind c i = false`; and for `rustDefinedCUnwind` (a Rust-defined `extern "C-unwind"` function) classified from `abortCfg` (strategy `abort`), `stdCanUnwind` returns `false` while `abiFirstCanUnwind` returns `true`.

**Kind / tier.** theorem / T1. The underlying rules are documented (see prior art); this is a toy-model mechanization. The corpus report on rustc's MIR passes mechanizes `fn_can_unwind` and `AbortUnwindingCalls` for single bodies; no mechanized counterpart of this statement was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). `stdCanUnwind` mirrors the order of the quoted `fn_can_unwind` source; `abiFirstCanUnwind` is a toy alternative order that corresponds to no cited implementation (B1). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:238-242
theorem std_and_abiFirst_foreignSound_but_differ :
    PrecForeignSound stdCanUnwind ∧ PrecForeignSound abiFirstCanUnwind ∧
    (∀ c i, abiFirstCanUnwind c i = false → stdCanUnwind c i = false) ∧
    stdCanUnwind abortCfg rustDefinedCUnwind = false ∧
    abiFirstCanUnwind abortCfg rustDefinedCUnwind = true := by …
```

**Unfolded (prose):** `abiFirstCanUnwind` evaluates the same four rules as `stdCanUnwind` (R2) in the order attribute, ABI, `abort` strategy for non-foreign functions, drop glue; since the ABI rule always applies, the last two rules are never consulted. `abortCfg` is `⟨.abort, .unwind⟩` (strategy `abort`, panic-in-drop `unwind`); `rustDefinedCUnwind` is `⟨.cUnwind, false, false, false⟩` (ABI `cUnwind`, non-foreign, no never-unwind attribute, not drop glue). `PrecForeignSound` is as in R3.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Depth.** definitional.

**Non-vacuity witness.** Closed statement; its witnesses abortCfg and rustDefinedCUnwind are named in it.

**Non-claims.** Listed under Boundaries, R4; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)

**Design question.** Is the order of the non-unwinding classification rules a free implementation choice among sound orders?

#### R5. `abortAllCanUnwind_not_foreignSound`, `abortAll_progAbortImportPlain_ub` (counterexample)

**Plain claim.** `abortAllCanUnwind` (the standard order with the `abort`-strategy rule applied to foreign functions as well) does not satisfy `PrecForeignSound` (`abortAllCanUnwind_not_foreignSound`); and the program `progAbortImportPlain` (an `abort` crate whose Rust function calls a foreign `"C-unwind"` import that may unwind, with a plain call; handler `abort`) satisfies `LinkOK`, `Enforced abortAllCanUnwind`, `SiteAgreement abortAllCanUnwind`, `ForeignHonest` and `ForeignNotGlue`, and its function 0 has a run with outcome `ub` under `abortAllCanUnwind` (`abortAll_progAbortImportPlain_ub`).

**Kind / tier.** counterexample / T1. The underlying rules are documented (see prior art); this is a toy-model mechanization. The corpus report on rustc's MIR passes mechanizes `fn_can_unwind` and `AbortUnwindingCalls` for single bodies; no mechanized counterpart of this statement was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). `abortAllCanUnwind` is a toy alternative order that corresponds to no cited implementation; the positive control's terminate pad is the toy counterpart of RFC 2945's minimal aborting landing pad (B1). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:255-255
theorem abortAllCanUnwind_not_foreignSound : ¬ PrecForeignSound abortAllCanUnwind := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:83-86
theorem abortAll_progAbortImportPlain_ub :
    LinkOK progAbortImportPlain ∧ Enforced abortAllCanUnwind progAbortImportPlain ∧
    SiteAgreement abortAllCanUnwind progAbortImportPlain ∧ ForeignHonest progAbortImportPlain ∧
    ForeignNotGlue progAbortImportPlain ∧ Exec abortAllCanUnwind progAbortImportPlain 0 [] .ub := …
```

**Unfolded (prose):** `abortAllCanUnwind` evaluates, in order, the never-unwind attribute rule, a rule that gives `false` whenever the classifying crate's strategy is `abort` (for foreign and non-foreign functions alike), the drop-glue rule and the ABI rule. `LinkOK p` ≡ `PotentiallyUnwinding p` implies that every crate setting in `p.crates` has strategy `unwind` (`PotentiallyUnwinding` as in R9). `Enforced`, `SiteAgreement`, `ForeignHonest`, `ForeignNotGlue` and `PrecForeignSound` are as in R1–R3.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** progAbortImportPlain under abortAllCanUnwind (all listed conditions hold; run [] / ub).

**Positive control.** A nearby setting in which the failure goes away: under `stdCanUnwind` instead of `abortAllCanUnwind`, the toy pass turns `progAbortImportPlain` into `progAbortImportPadded` (a terminate pad at the call of the foreign `cUnwind` import), and function 0 of that program has no run with outcome `ub`.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:93-95
theorem std_progAbortImportPlain_padded_noUB :
    insertPads stdCanUnwind progAbortImportPlain = progAbortImportPadded ∧
    ∀ t o, Exec stdCanUnwind progAbortImportPadded 0 t o → o ≠ .ub := …
```

**Non-claims.** Listed under Boundaries, R5; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)

**Design question.** Is the order of the non-unwinding classification rules a free implementation choice among sound orders?

#### R6. `insertPads_enforced`, `insertPads_body`, `padStmt_call`, `padStmt_raise`, `insertPads_foreignCovered`, `insertPads_siteAgreement`, `exec_insertPads_of_exec_of_ne_ub` (theorem)

**Plain claim.** For every precedence function `cu` and every toy program `p`: (i) `insertPads cu p` satisfies `Enforced cu` (`insertPads_enforced`); (ii) for every function index `g`, the body of `g` in `insertPads cu p` is `g`'s body with `padStmt cu p g` applied to every statement if `g` is non-foreign and classified as non-unwinding by its own crate, and is `g`'s body unchanged otherwise (`insertPads_body`); (iii) `padStmt cu p g` turns a call `.call f act` into `.call f .terminate` if `p.viewMay cu g f = true` and `act.Stops = false`, and leaves it unchanged otherwise (`padStmt_call`); (iv) `padStmt cu p g` turns a panic point `.raise act` into `.raise .terminate` if `p.handler = .unwind` and `act.Stops = false`, and leaves it unchanged otherwise (`padStmt_raise`); (v) if `p` satisfies `ForeignCovered cu p` then so does `insertPads cu p` (`insertPads_foreignCovered`), and if `p` satisfies `SiteAgreement cu p` (reachable or not, as in R1) then so does `insertPads cu p` (`insertPads_siteAgreement`); (vi) for every function `f`, trace `t` and outcome `o ≠ ub`, if `Exec cu p f t o` (a finite run produced by `runFn`) then `Exec cu (insertPads cu p) f t o` (`exec_insertPads_of_exec_of_ne_ub`). By (ii)-(iv), a `cleanup ds` action at a replaced site becomes `terminate` and its drop list `ds` is lost.

**Kind / tier.** theorem / T1. The corpus report on rustc's MIR passes mechanizes rustc's `AbortUnwindingCalls` and `fn_can_unwind` for single bodies, with lowering-soundness theorems (see prior art); this statement differs in being parametric in the precedence function and stated for multi-crate programs with a toy pass. No mechanized counterpart of it was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). `insertPads` is a toy counterpart of the aborting landing pads described in the `fn_can_unwind` documentation (B1); it differs from rustc's pass in discarding cleanup at padded sites (B3); the reading of `catchPad` is limited by B5. No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:380-380
theorem insertPads_enforced (cu : Prec) (p : Prog) : Enforced cu (insertPads cu p) := by …
```

```lean
-- lean/ToyUnwindCap/Results.lean:286-290
theorem insertPads_body (cu : Prec) (p : Prog) (g : Nat) :
    ((insertPads cu p).fn g).body =
      if (p.fn g).info.foreign = false ∧ p.selfMay cu g = false then
        (p.fn g).body.map (padStmt cu p g)
      else (p.fn g).body := by …
```

```lean
-- lean/ToyUnwindCap/Results.lean:313-315
theorem padStmt_call (cu : Prec) (p : Prog) (g f : Nat) (act : Action) :
    padStmt cu p g (.call f act) =
      .call f (if p.viewMay cu g f = true ∧ act.Stops = false then .terminate else act) := by …
```

```lean
-- lean/ToyUnwindCap/Results.lean:326-328
theorem padStmt_raise (cu : Prec) (p : Prog) (g : Nat) (act : Action) :
    padStmt cu p g (.raise act) =
      .raise (if p.handler = .unwind ∧ act.Stops = false then .terminate else act) := by …
```

```lean
-- lean/ToyUnwindCap/Results.lean:418-419
theorem insertPads_foreignCovered (cu : Prec) (p : Prog) (h : ForeignCovered cu p) :
    ForeignCovered cu (insertPads cu p) := by …
```

```lean
-- lean/ToyUnwindCap/Results.lean:426-427
theorem insertPads_siteAgreement (cu : Prec) (p : Prog) (h : SiteAgreement cu p) :
    SiteAgreement cu (insertPads cu p) := by …
```

```lean
-- lean/ToyUnwindCap/Results.lean:1154-1155
theorem exec_insertPads_of_exec_of_ne_ub (cu : Prec) (p : Prog) :
    ∀ f t o, o ≠ .ub → Exec cu p f t o → Exec cu (insertPads cu p) f t o := by …
```

**Unfolded (prose):** `insertPads cu p` keeps `p.crates` and `p.handler` and maps the function `d` at each index `g` of `p.fns` to `d` with its body mapped by `padStmt cu p g` when `d.info.foreign = false` and `cu` applied to `d`'s crate setting (`CrateCfg.dflt` for an out-of-range crate index) and `d.info` is `false`, and to `d` unchanged otherwise. `padStmt cu p g (.raise act)` is `.raise (if p.handler.unwinds && !act.Stops then .terminate else act)` and `padStmt cu p g (.call f act)` is `.call f (if p.viewMay cu g f && !act.Stops then .terminate else act)`, where `p.handler.unwinds` is true exactly for the `unwind` handler. `Enforced`, `ForeignCovered`, `SiteAgreement` and `Exec` are as in R1.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h : ForeignCovered cu p (in insertPads_foreignCovered)` | the pass does not change classifications, so it cannot repair a misclassified foreign function | tight: counterexample `insertPads_foreignCovered_fails_without_foreignCovered` (witness class: the 1-crate, 1-function program `progThrowingC` under `stdCanUnwind`) |
| `h : SiteAgreement cu p (in insertPads_siteAgreement)` | the pass inserts no pad at a call whose callee the caller's crate classifies as non-unwinding | tight: counterexample `insertPads_siteAgreement_fails_without_siteAgreement` (witness class: the 2-crate, 2-function program `progAbortCallsUnwind` under `stdCanUnwind`) |
| `o ≠ .ub (in exec_insertPads_of_exec_of_ne_ub)` | there is a `ub` run that the pass removes | tight: counterexample `exec_insertPads_fails_without_ne_ub` (witness class: the 1-crate, 2-function program `progAbortImportPlain` under `stdCanUnwind`) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:812-813
theorem insertPads_foreignCovered_fails_without_foreignCovered :
    ¬ ForeignCovered stdCanUnwind (insertPads stdCanUnwind progThrowingC) := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:819-820
theorem insertPads_siteAgreement_fails_without_siteAgreement :
    ¬ SiteAgreement stdCanUnwind (insertPads stdCanUnwind progAbortCallsUnwind) := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:825-827
theorem exec_insertPads_fails_without_ne_ub :
    Exec stdCanUnwind progAbortImportPlain 0 [] .ub ∧
    ¬ Exec stdCanUnwind (insertPads stdCanUnwind progAbortImportPlain) 0 [] .ub := by …
```

**Depth.** shallow.

**Non-vacuity witness.** insertPads stdCanUnwind progAbortImportPlain = progAbortImportPadded (a pad is inserted); insertPads stdCanUnwind progAbortCallsUnwind = progAbortCallsUnwind (no pad at a call whose callee the caller's crate classifies as non-unwinding); progAbortImportPlain satisfies ForeignCovered and SiteAgreement; the non-ub run [drop 1 7, caught 0] / ret of progUnwindCatch is kept.

```lean
-- lean/ToyUnwindCap/Examples.lean:222-223
theorem insertPads_progAbortImportPlain :
    insertPads stdCanUnwind progAbortImportPlain = progAbortImportPadded := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:227-228
theorem insertPads_progAbortCallsUnwind :
    insertPads stdCanUnwind progAbortCallsUnwind = progAbortCallsUnwind := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:838-842
theorem insertPads_hypotheses_hold :
    ForeignCovered stdCanUnwind progAbortImportPlain ∧
    SiteAgreement stdCanUnwind progAbortImportPlain ∧
    Outcome.ret ≠ Outcome.ub ∧ Exec stdCanUnwind progUnwindCatch 0 [.drop 1 7, .caught 0] .ret ∧
    Exec stdCanUnwind (insertPads stdCanUnwind progUnwindCatch) 0 [.drop 1 7, .caught 0] .ret := …
```

**Non-claims.** Listed under Boundaries, R6; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/1513-less-unwinding.md:108-111 (the `abort` strategy replaces `invoke` by `call`) and 142-146 (final-product validation: if the panic mode is `abort` no other validation is performed, otherwise all crates must agree) (RFC 1513, merged; quoted verbatim in REPORT.md)
- D. Abrahams, R. Sharoni, D. Gregor, "Allowing Move Constructors to Throw (Rev. 1)", ISO/IEC JTC1/SC22/WG21 N3050, 2010-03-12 (open-std.org/jtc1/sc22/wg21/docs/papers/2010/n3050.html): proposes the C++ `noexcept` specification together with wording changes to `[except.spec]` and `[except.terminate]` (`std::terminate`); the C++ analogue of enforcing a non-unwinding declaration by termination. No mechanized semantics.
- Corpus report `rustc-cleanup-post-borrowck-false-edges-and-abort-unwinding-mir-lowering`: documents rustc's MIR passes between analysis and runtime MIR, including `AbortUnwindingCalls`, at pinned rustc revisions, and contains a kernel-checked Lean v4.34.1 mechanization (`support/CleanupPostBorrowckAndAbortCalls.lean`) of intra-procedural MIR semantics, `fn_can_unwind` and `AbortUnwindingCalls` (which keeps cleanup blocks and turns their final resume into a terminate) with end-to-end lowering theorems; by its own scope note it does not model linker-level cross-crate panic-strategy checks. This package does not depend on it; its additions are precedence functions as parameters, cross-crate classification disagreement (`SiteAgreement`), the linking restriction, per-crate panic-in-drop, and mixed landing-pad capabilities.
- T. Ramananandro, G. Dos Reis, X. Leroy, "A mechanized semantics for C++ object construction and destruction, with applications to resource management", POPL 2012, doi:10.1145/2103621.2103718: a Coq semantics of C++ object construction and destruction order (resource management); it does not treat unwind classifications or landing-pad placement.

**Design question.** Where does a function classified as non-unwinding need terminate pads for enforcement to be sound, and what does a classification-driven pass insert?

#### R7. `noUB_insertPads_of_foreignCovered_of_siteAgreement` (theorem)

**Plain claim.** Corollary of R1 and R6. For every precedence function `cu` and every toy program `p` satisfying `ForeignCovered cu p` and `SiteAgreement cu p` (reachable or not, as in R1), no finite run produced by `runFn` (no `Exec cu (insertPads cu p) f t o`) of any function of `insertPads cu p` has outcome `ub`.

**Kind / tier.** theorem / T1. The corpus report on rustc's MIR passes mechanizes rustc's `AbortUnwindingCalls` and `fn_can_unwind` for single bodies, with lowering-soundness theorems (see prior art); this statement differs in being parametric in the precedence function and stated for multi-crate programs with a toy pass. No mechanized counterpart of it was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge), as for R6 (B1, B3, B5). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:453-455
theorem noUB_insertPads_of_foreignCovered_of_siteAgreement (cu : Prec) (p : Prog)
    (hfc : ForeignCovered cu p) (hsa : SiteAgreement cu p) :
    ∀ f t o, Exec cu (insertPads cu p) f t o → o ≠ .ub := …
```

**Unfolded (prose):** With `Enforced`, `ForeignCovered`, `SiteAgreement` and `Exec` as in R1 and `insertPads` as in R6: from `ForeignCovered cu p` and `SiteAgreement cu p`, for every `f`, `t` and `o`, `Exec cu (insertPads cu p) f t o` implies `o ≠ .ub`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hfc : ForeignCovered cu p` | no pad inside the program can stop an unwind leaving a misclassified foreign function itself | tight: counterexample `noUB_insertPads_fails_without_foreignCovered` (witness class: the 1-crate, 1-function program `progThrowingC` under `stdCanUnwind`) |
| `hsa : SiteAgreement cu p` | the pass inserts no pad where the caller's crate classifies the callee as non-unwinding | tight: counterexample `noUB_insertPads_fails_without_siteAgreement` (witness class: the 2-crate, 2-function program `progAbortCallsUnwind` under `stdCanUnwind`) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:110-112
theorem noUB_insertPads_fails_without_foreignCovered :
    SiteAgreement stdCanUnwind progThrowingC ∧
    Exec stdCanUnwind (insertPads stdCanUnwind progThrowingC) 0 [] .ub := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:117-119
theorem noUB_insertPads_fails_without_siteAgreement :
    ForeignCovered stdCanUnwind progAbortCallsUnwind ∧
    Exec stdCanUnwind (insertPads stdCanUnwind progAbortCallsUnwind) 0 [] .ub := by …
```

**Depth.** definitional.

**Non-vacuity witness.** progAbortImportPlain satisfies both hypotheses under stdCanUnwind.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:104-106
theorem noUB_insertPads_hypotheses_hold_progAbortImportPlain :
    ForeignCovered stdCanUnwind progAbortImportPlain ∧
    SiteAgreement stdCanUnwind progAbortImportPlain := …
```

**Non-claims.** Listed under Boundaries, R7; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/1513-less-unwinding.md:108-111 (the `abort` strategy replaces `invoke` by `call`) and 142-146 (final-product validation: if the panic mode is `abort` no other validation is performed, otherwise all crates must agree) (RFC 1513, merged; quoted verbatim in REPORT.md)
- D. Abrahams, R. Sharoni, D. Gregor, "Allowing Move Constructors to Throw (Rev. 1)", ISO/IEC JTC1/SC22/WG21 N3050, 2010-03-12 (open-std.org/jtc1/sc22/wg21/docs/papers/2010/n3050.html): proposes the C++ `noexcept` specification together with wording changes to `[except.spec]` and `[except.terminate]` (`std::terminate`); the C++ analogue of enforcing a non-unwinding declaration by termination. No mechanized semantics.
- Corpus report `rustc-cleanup-post-borrowck-false-edges-and-abort-unwinding-mir-lowering`: documents rustc's MIR passes between analysis and runtime MIR, including `AbortUnwindingCalls`, at pinned rustc revisions, and contains a kernel-checked Lean v4.34.1 mechanization (`support/CleanupPostBorrowckAndAbortCalls.lean`) of intra-procedural MIR semantics, `fn_can_unwind` and `AbortUnwindingCalls` (which keeps cleanup blocks and turns their final resume into a terminate) with end-to-end lowering theorems; by its own scope note it does not model linker-level cross-crate panic-strategy checks. This package does not depend on it; its additions are precedence functions as parameters, cross-crate classification disagreement (`SiteAgreement`), the linking restriction, per-crate panic-in-drop, and mixed landing-pad capabilities.

**Design question.** Where does a function classified as non-unwinding need terminate pads for enforcement to be sound, and what does a classification-driven pass insert?

#### R8. `ub_of_selfNonUnwinding_of_unguarded_head_call_of_callee_unwinds` (theorem)

**Plain claim.** For every precedence function `cu`, toy program `p`, and function `g` that is non-foreign, is classified as non-unwinding by its own crate, and whose body is `.call f act :: rest` (the call is the first statement) with `act.Stops = false` (`act` is `none` or a cleanup pad): if `f` has a finite run produced by `runFn` (`Exec cu p f t .unwind`) with trace `t` that unwinds, then there is a trace `t'` such that `Exec cu p g t' .ub`; this holds whichever way `g`'s crate classifies `f`.

**Kind / tier.** theorem / T1. The underlying rules are documented (see prior art); this is a toy-model mechanization. The corpus report on rustc's MIR passes mechanizes `fn_can_unwind` and `AbortUnwindingCalls` for single bodies; no mechanized counterpart of this statement was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). The `ub` outcome of an unwind leaving a non-unwinding function follows the LLVM `nounwind` text (B1); the reading of `catchPad` is limited by B5. No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:464-468
theorem ub_of_selfNonUnwinding_of_unguarded_head_call_of_callee_unwinds (cu : Prec) (p : Prog)
    (g f : Nat) (act : Action)
    (rest : List Stmt) (t : List Event) (hg : (p.fn g).info.foreign = false)
    (hgself : p.selfMay cu g = false) (hbody : (p.fn g).body = .call f act :: rest)
    (hact : act.Stops = false) (hf : Exec cu p f t .unwind) : ∃ t', Exec cu p g t' .ub := by …
```

**Unfolded (prose):** `p.selfMay cu g = false` ≡ `cu (p.crateOf g) (p.fn g).info = false` (`g`'s own crate classifies `g` as non-unwinding); `act.Stops = false` ≡ `act` is `.none` or `.cleanup ds` for some `ds`; `Exec cu p f t .unwind` ≡ there is a fuel `n` with `(t, .unwind) ∈ runFn cu p n f`. The conclusion is that there are a trace `t'` and a fuel `n'` with `(t', .ub) ∈ runFn cu p n' g`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hg : (p.fn g).info.foreign = false` | the body field of a foreign function is not executed | tight: counterexample `ub_of_unguarded_call_fails_without_nonForeign` (witness class: a 1-crate, 2-function toy encoding whose function 0 is a foreign `c` import with a non-empty body field (`progForeignWithBody`); an encoding artifact, since real foreign items have no body) |
| `hgself : p.selfMay cu g = false` | an unwind may leave a function classified as possibly unwinding | tight: counterexample `ub_of_unguarded_call_fails_without_selfNonUnwinding` (witness class: the 1-crate, 3-function program `progUnwindCatch`) |
| `hbody : (p.fn g).body = .call f act :: rest` | the call is reached; tight against the weakening "the call occurs somewhere in the body" | tight: counterexample `ub_of_unguarded_call_fails_without_callFirst` (witness class: a 1-crate, 2-function program whose call follows a panic point with a terminate pad (`progUnreachableCall`)) |
| `hact : act.Stops = false` | a catch or terminate pad stops the unwind | tight: counterexample `ub_of_unguarded_call_fails_without_nonStopping` (witness class: a 1-crate, 2-function program (`progTerminateFromNounwind`)) |
| `hf : Exec cu p f t .unwind` | the callee actually unwinds; there is a program whose callee has no unwinding run and whose caller has no `ub` run | tight: counterexample `ub_of_unguarded_call_fails_without_calleeUnwinds` (witness class: a 1-crate, 2-function program whose callee never panics (`progNounwindCallee`)) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:183-187
theorem ub_of_unguarded_call_fails_without_nonForeign :
    progForeignWithBody.selfMay stdCanUnwind 0 = false ∧
    (progForeignWithBody.fn 0).body = [.call 1 .none] ∧ Action.none.Stops = false ∧
    Exec stdCanUnwind progForeignWithBody 1 [] .unwind ∧
    ¬ ∃ t', Exec stdCanUnwind progForeignWithBody 0 t' .ub := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:134-138
theorem ub_of_unguarded_call_fails_without_selfNonUnwinding :
    (progUnwindCatch.fn 1).info.foreign = false ∧
    (progUnwindCatch.fn 1).body = [.call 2 (.cleanup [7])] ∧ (Action.cleanup [7]).Stops = false ∧
    Exec stdCanUnwind progUnwindCatch 2 [] .unwind ∧
    ¬ ∃ t', Exec stdCanUnwind progUnwindCatch 1 t' .ub := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:200-205
theorem ub_of_unguarded_call_fails_without_callFirst :
    (progUnreachableCall.fn 0).info.foreign = false ∧
    progUnreachableCall.selfMay stdCanUnwind 0 = false ∧
    Stmt.call 1 .none ∈ (progUnreachableCall.fn 0).body ∧ Action.none.Stops = false ∧
    Exec stdCanUnwind progUnreachableCall 1 [] .unwind ∧
    ¬ ∃ t', Exec stdCanUnwind progUnreachableCall 0 t' .ub := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:150-155
theorem ub_of_unguarded_call_fails_without_nonStopping :
    (progTerminateFromNounwind.fn 0).info.foreign = false ∧
    progTerminateFromNounwind.selfMay stdCanUnwind 0 = false ∧
    (progTerminateFromNounwind.fn 0).body = [.call 1 .terminate] ∧
    Exec stdCanUnwind progTerminateFromNounwind 1 [] .unwind ∧
    ¬ ∃ t', Exec stdCanUnwind progTerminateFromNounwind 0 t' .ub := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:167-171
theorem ub_of_unguarded_call_fails_without_calleeUnwinds :
    (progNounwindCallee.fn 0).info.foreign = false ∧
    progNounwindCallee.selfMay stdCanUnwind 0 = false ∧
    (progNounwindCallee.fn 0).body = [.call 1 .none] ∧ Action.none.Stops = false ∧
    ¬ ∃ t', Exec stdCanUnwind progNounwindCallee 0 t' .ub := by …
```

**Depth.** shallow.

**Non-vacuity witness.** progPlainCallFromNounwind: a Rust-defined extern "C" function calls a panicking Rust function with a plain call.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:125-129
theorem ub_of_unguarded_call_hypotheses_hold_progPlainCallFromNounwind :
    (progPlainCallFromNounwind.fn 0).info.foreign = false ∧
    progPlainCallFromNounwind.selfMay stdCanUnwind 0 = false ∧
    (progPlainCallFromNounwind.fn 0).body = [.call 1 .none] ∧ Action.none.Stops = false ∧
    Exec stdCanUnwind progPlainCallFromNounwind 1 [] .unwind := …
```

**Non-claims.** Listed under Boundaries, R8; a reader of this result must read them with it.

**Prior art.**

- llvm/llvm-project@a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4 (tag llvmorg-19.1.0) llvm/docs/LangRef.rst:2177-2183 (`nounwind` function attribute: the function never raises an exception, and if it does its runtime behaviour is undefined; quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- D. Abrahams, R. Sharoni, D. Gregor, "Allowing Move Constructors to Throw (Rev. 1)", ISO/IEC JTC1/SC22/WG21 N3050, 2010-03-12 (open-std.org/jtc1/sc22/wg21/docs/papers/2010/n3050.html): proposes the C++ `noexcept` specification together with wording changes to `[except.spec]` and `[except.terminate]` (`std::terminate`); the C++ analogue of enforcing a non-unwinding declaration by termination. No mechanized semantics.

**Design question.** Where does a function classified as non-unwinding need terminate pads for enforcement to be sound, and what does a classification-driven pass insert?

#### R9. `noUB_std_of_linkOK_of_enforced_of_foreignHonest_of_foreignNotGlue_of_glueAgreement` (theorem)

**Plain claim.** For `stdCanUnwind` and every toy program `p` satisfying `LinkOK p` (if `p` is potentially unwinding, that is, it uses the `unwind` panic handler or some non-foreign function of an `unwind`-strategy crate has a call, reachable or not, to a `cUnwind` function, then every crate in `p.crates` uses the `unwind` strategy), `Enforced stdCanUnwind p` (reachable or not, as in R1), `ForeignHonest p`, `ForeignNotGlue p`, and, in case `p` is potentially unwinding, `GlueAgreement p` (at every call site, reachable or not, without a stopping pad that calls drop glue from a crate with panic-in-drop `abort`, the glue instance's crate has panic-in-drop `abort`): no finite run produced by `runFn` of any function of `p` has outcome `ub`. `SiteAgreement` is not assumed.

**Kind / tier.** theorem / T1. The underlying rules are documented (see prior art); this is a toy-model mechanization. The corpus report on rustc's MIR passes mechanizes `fn_can_unwind` and `AbortUnwindingCalls` for single bodies; no mechanized counterpart of this statement was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). `LinkOK` is a toy reading of two of the three clauses of the Reference's `link.unwinding` rules (B1), and the `abort` handler models a final product whose panics abort (B2); the per-crate panic-in-drop setting follows the `fn_can_unwind` source comment that it can differ between crates (B1); the reading of `catchPad` is limited by B5. No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:650-653
theorem noUB_std_of_linkOK_of_enforced_of_foreignHonest_of_foreignNotGlue_of_glueAgreement
    (p : Prog) (hlink : LinkOK p) (henf : Enforced stdCanUnwind p) (hh : ForeignHonest p)
    (hng : ForeignNotGlue p) (hglue : PotentiallyUnwinding p → GlueAgreement p) :
    ∀ f t o, Exec stdCanUnwind p f t o → o ≠ .ub := by …
```

**Unfolded (prose):** `PotentiallyUnwinding p` ≡ `p.handler = .unwind`, or there are `g`, `f` and `act` with `(p.fn g).info.foreign = false`, `(p.crateOf g).panic = .unwind`, `Stmt.call f act ∈ (p.fn g).body` and `(p.fn f).info.abi = .cUnwind`. `LinkOK p` ≡ `PotentiallyUnwinding p` implies that every crate setting in `p.crates` has strategy `unwind`. `GlueAgreement p` ≡ for every `g`, `f` and `act`, if `(p.fn g).info.foreign = false`, `Stmt.call f act ∈ (p.fn g).body`, `(p.fn f).info.dropGlue = true`, `act.Stops = false` and `(p.crateOf g).panicInDrop = .abort`, then `(p.crateOf f).panicInDrop = .abort`. The hypothesis `hglue` is the implication `PotentiallyUnwinding p → GlueAgreement p`, not `GlueAgreement p` itself. `Enforced` is as in R1 (with `cu = stdCanUnwind`), `ForeignHonest` and `ForeignNotGlue` as in R2.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hlink : LinkOK p` | an `abort` crate treats Rust-ABI callees as non-unwinding; that is sound when nothing in the artifact unwinds through Rust frames | tight: counterexample `noUB_std_fails_without_linkOK` (witness class: the 2-crate, 2-function mixed-strategy program `progAbortCallsUnwind` (handler `unwind`)) |
| `henf : Enforced stdCanUnwind p` | a function classified as non-unwinding stops its known unwinding sources | tight: counterexample `noUB_std_fails_without_enforced` (witness class: the 1-crate, 2-function program `progPlainCallFromNounwind`) |
| `hh : ForeignHonest p` | foreign code that unwinds is declared `cUnwind` without the never-unwind attribute | tight: counterexample `noUB_std_fails_without_foreignHonest` (witness class: the 1-crate, 1-function program `progThrowingC`) |
| `hng : ForeignNotGlue p` | well-formedness (toy-encoding artifact) | tight: counterexample `noUB_std_fails_without_foreignNotGlue` (witness class: a 1-crate, 1-function toy encoding whose function is both foreign and drop glue (`progForeignGlue`)) |
| `hglue : PotentiallyUnwinding p → GlueAgreement p` | the strategy-level linking restriction does not cover per-crate panic-in-drop settings | tight: counterexample `noUB_std_fails_without_glueAgreement` (witness class: the 2-crate drop-glue program `progGlueMismatch` (handler `unwind`, hence potentially unwinding)) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:277-281
theorem noUB_std_fails_without_linkOK :
    Enforced stdCanUnwind progAbortCallsUnwind ∧ ForeignHonest progAbortCallsUnwind ∧
    ForeignNotGlue progAbortCallsUnwind ∧
    (PotentiallyUnwinding progAbortCallsUnwind → GlueAgreement progAbortCallsUnwind) ∧
    Exec stdCanUnwind progAbortCallsUnwind 0 [] .ub := …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:287-291
theorem noUB_std_fails_without_enforced :
    LinkOK progPlainCallFromNounwind ∧ ForeignHonest progPlainCallFromNounwind ∧
    ForeignNotGlue progPlainCallFromNounwind ∧
    (PotentiallyUnwinding progPlainCallFromNounwind → GlueAgreement progPlainCallFromNounwind) ∧
    Exec stdCanUnwind progPlainCallFromNounwind 0 [] .ub := …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:297-300
theorem noUB_std_fails_without_foreignHonest :
    LinkOK progThrowingC ∧ Enforced stdCanUnwind progThrowingC ∧ ForeignNotGlue progThrowingC ∧
    (PotentiallyUnwinding progThrowingC → GlueAgreement progThrowingC) ∧
    Exec stdCanUnwind progThrowingC 0 [] .ub := …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:306-310
theorem noUB_std_fails_without_foreignNotGlue :
    LinkOK progForeignGlue ∧ Enforced stdCanUnwind progForeignGlue ∧
    ForeignHonest progForeignGlue ∧
    (PotentiallyUnwinding progForeignGlue → GlueAgreement progForeignGlue) ∧
    Exec stdCanUnwind progForeignGlue 0 [] .ub := …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:316-319
theorem noUB_std_fails_without_glueAgreement :
    LinkOK progGlueMismatch ∧ Enforced stdCanUnwind progGlueMismatch ∧
    ForeignHonest progGlueMismatch ∧ ForeignNotGlue progGlueMismatch ∧
    Exec stdCanUnwind progGlueMismatch 0 [] .ub := …
```

**Depth.** shallow.

**Non-vacuity witness.** progMixedLinkOK (an abort crate and an unwind crate, panic handler abort; the abort crate calls a throwing foreign C-unwind import through a terminate pad and calls a panicking Rust function of the unwind crate with a plain call; SiteAgreement fails; a run aborts), progUnwindCatch (all crates unwind), progMixedAbortBothCallsGlue (an abort crate with panic-in-drop abort calls drop glue of an unwind crate with a plain call under the abort handler; GlueAgreement itself fails) and progAbortHandlerRaisePlain (a panic point without a landing pad under the abort handler) satisfy all five hypotheses.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:220-225
theorem noUB_std_of_linkOK_hypotheses_hold_progMixedLinkOK :
    LinkOK progMixedLinkOK ∧ Enforced stdCanUnwind progMixedLinkOK ∧
    ForeignHonest progMixedLinkOK ∧ ForeignNotGlue progMixedLinkOK ∧
    (PotentiallyUnwinding progMixedLinkOK → GlueAgreement progMixedLinkOK) ∧
    ¬ SiteAgreement stdCanUnwind progMixedLinkOK ∧
    Exec stdCanUnwind progMixedLinkOK 1 [] .abort := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:231-234
theorem noUB_std_of_linkOK_hypotheses_hold_progUnwindCatch :
    LinkOK progUnwindCatch ∧ Enforced stdCanUnwind progUnwindCatch ∧
    ForeignHonest progUnwindCatch ∧ ForeignNotGlue progUnwindCatch ∧
    (PotentiallyUnwinding progUnwindCatch → GlueAgreement progUnwindCatch) := …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:252-258
theorem noUB_std_hypotheses_hold_progMixedAbortBothCallsGlue :
    LinkOK progMixedAbortBothCallsGlue ∧ Enforced stdCanUnwind progMixedAbortBothCallsGlue ∧
    ForeignHonest progMixedAbortBothCallsGlue ∧ ForeignNotGlue progMixedAbortBothCallsGlue ∧
    (PotentiallyUnwinding progMixedAbortBothCallsGlue →
      GlueAgreement progMixedAbortBothCallsGlue) ∧
    ¬ GlueAgreement progMixedAbortBothCallsGlue ∧
    Exec stdCanUnwind progMixedAbortBothCallsGlue 0 [] .abort := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:267-272
theorem noUB_std_hypotheses_hold_progAbortHandlerRaisePlain :
    LinkOK progAbortHandlerRaisePlain ∧ Enforced stdCanUnwind progAbortHandlerRaisePlain ∧
    ForeignHonest progAbortHandlerRaisePlain ∧ ForeignNotGlue progAbortHandlerRaisePlain ∧
    (PotentiallyUnwinding progAbortHandlerRaisePlain →
      GlueAgreement progAbortHandlerRaisePlain) ∧
    Exec stdCanUnwind progAbortHandlerRaisePlain 0 [] .abort := …
```

**Non-claims.** Listed under Boundaries, R9; a reader of this result must read them with it.

**Prior art.**

- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c src/linkage.md:154-176 (`link.unwinding`: potentially unwinding artifacts and the all-crates-unwind rule)
- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c src/panic.md:86-101 (`panic.strategy`), 103-116 (`panic.unwind`), 124-128 (`panic.unwind.ffi.undefined`), 130-134 (`panic.unwind.ffi.catch-foreign`)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/1513-less-unwinding.md:108-111 (the `abort` strategy replaces `invoke` by `call`) and 142-146 (final-product validation: if the panic mode is `abort` no other validation is performed, otherwise all crates must agree) (RFC 1513, merged; quoted verbatim in REPORT.md)
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)
- Corpus report `rust-no-std-panic-abort-eh-personality-and-cross-crate-unwinding-abi-contracts` (no Lean mechanization): documents rustc's panic-strategy linking rules from source and experiments, including a check that the `-Z panic-in-drop` setting agrees across linked crates (it cites `dependency_format.rs:495-505` at the revision it pins). This package does not re-examine that check.

**Design question.** What must hold when crates compiled with different panic strategies are linked into one artifact?

#### R10. `glueSiteSound_iff` (characterization)

**Plain claim.** In the drop-glue program with exactly two crates, `glueProg cc cg act body` (crate 0, with settings `cc`, holds the caller, function 0, whose body consists of exactly one call to function 1 with action `act`; crate 1, with settings `cg`, compiled the drop-glue instance, function 1, whose body is `body`; panic handler `unwind`), for all `cc`, `cg` and `act`: `GlueSiteSound cc cg act` (for every glue body `body`, calls included, for which the program satisfies `Enforced stdCanUnwind` at every function index and statement, reachable or not, no finite run of the caller produced by `runFn` has outcome `ub`) holds iff, whenever `stdCanUnwind cc glueInfo = false` (the caller's crate treats the glue as non-unwinding), `stdCanUnwind cg glueInfo = false` (the glue instance's own crate does too) or `act` is a stopping pad (`catchPad` or `terminate`).

**Kind / tier.** characterization / T1. The underlying rules are documented (see prior art); this is a toy-model mechanization. The corpus report on rustc's MIR passes mechanizes `fn_can_unwind` and `AbortUnwindingCalls` for single bodies; no mechanized counterpart of this statement was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). The per-crate panic-in-drop setting follows the `fn_can_unwind` source comment that it can differ between crates (B1); the reading of `catchPad` is limited by B5. No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:715-718
theorem glueSiteSound_iff (cc cg : CrateCfg) (act : Action) :
    GlueSiteSound cc cg act ↔
      (stdCanUnwind cc glueInfo = false →
        stdCanUnwind cg glueInfo = false ∨ act.Stops = true) := by …
```

**Unfolded (prose):** `GlueSiteSound cc cg act` ≡ for every glue body `body`, if `Enforced stdCanUnwind (glueProg cc cg act body)` then for all `t` and `o`, `Exec stdCanUnwind (glueProg cc cg act body) 0 t o` implies `o ≠ .ub`. `glueProg cc cg act body` has crates `[cc, cg]`, function 0 with static facts `rustInfo` in crate 0 with body `[.call 1 act]`, function 1 with static facts `glueInfo` in crate 1 with body `body` (neither throws), and handler `unwind`. `glueInfo` describes a non-foreign `rust`-ABI drop-glue function without the never-unwind attribute, so `stdCanUnwind c glueInfo` is decided by the strategy rule (`false` when `c.panic = .abort`), then by the drop-glue rule (`false` when `c.panicInDrop = .abort`), and otherwise by the ABI rule (`c.panic.unwinds`). `act.Stops = true` ≡ `act` is `catchPad` or `terminate`.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** Both sides are instantiated: (pidAbortCfg, unwindCfg, none) makes them false; (pidAbortCfg, pidAbortCfg, none) makes them true.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:328-332
theorem glueSiteSound_iff_instances :
    ¬ (stdCanUnwind pidAbortCfg glueInfo = false →
        stdCanUnwind unwindCfg glueInfo = false ∨ Action.none.Stops = true) ∧
    (stdCanUnwind pidAbortCfg glueInfo = false →
        stdCanUnwind pidAbortCfg glueInfo = false ∨ Action.none.Stops = true) := by …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:266-267
theorem glueSiteSound_examples :
    GlueSiteSound pidAbortCfg pidAbortCfg .none ∧ ¬ GlueSiteSound pidAbortCfg unwindCfg .none := by …
```

**Non-claims.** Listed under Boundaries, R10; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- Corpus report `rust-no-std-panic-abort-eh-personality-and-cross-crate-unwinding-abi-contracts` (no Lean mechanization): documents rustc's panic-strategy linking rules from source and experiments, including a check that the `-Z panic-in-drop` setting agrees across linked crates (it cites `dependency_format.rs:495-505` at the revision it pins). This package does not re-examine that check.

**Design question.** When may a caller treat drop glue as non-unwinding when panic-in-drop is a per-crate setting?

#### R11. `glueSiteSound_iff_panicInDrop` (characterization)

**Plain claim.** Corollary of R10. For all caller-crate settings `cc`, glue-crate settings `cg` and actions `act`: if the caller's crate has strategy `abort` or panic-in-drop `abort` (so it treats drop glue as non-unwinding) and the glue instance's crate has strategy `unwind`, then `GlueSiteSound cc cg act` holds iff the glue instance's crate has panic-in-drop `abort` or `act` is a stopping pad (`catchPad` or `terminate`).

**Kind / tier.** characterization / T1. The underlying rules are documented (see prior art); this is a toy-model mechanization. The corpus report on rustc's MIR passes mechanizes `fn_can_unwind` and `AbortUnwindingCalls` for single bodies; no mechanized counterpart of this statement was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge), as for R10 (B1, B5). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:909-911
theorem glueSiteSound_iff_panicInDrop (cc cg : CrateCfg) (act : Action)
    (hview : cc.panic = .abort ∨ cc.panicInDrop = .abort) (hcg : cg.panic = .unwind) :
    GlueSiteSound cc cg act ↔ (cg.panicInDrop = .abort ∨ act.Stops = true) := by …
```

**Unfolded (prose):** `GlueSiteSound` is as in R10. From `cc.panic = .abort ∨ cc.panicInDrop = .abort` and `cg.panic = .unwind`: `GlueSiteSound cc cg act` holds iff `cg.panicInDrop = .abort` or `act.Stops = true`.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hview : cc.panic = .abort ∨ cc.panicInDrop = .abort` | without it the caller treats glue as possibly unwinding, and then every site is sound by `glueSiteSound_iff` | tight: counterexample `glueSiteSound_iff_panicInDrop_fails_without_view` (witness class: the crate-settings pair (`unwindCfg`, `unwindCfg`) with action `none`) |
| `hcg : cg.panic = .unwind` | glue compiled in an `abort`-strategy crate is non-unwinding by the strategy rule whatever its panic-in-drop setting | tight: counterexample `glueSiteSound_iff_panicInDrop_fails_without_glueCrateUnwind` (witness class: the crate-settings pair (`pidAbortCfg`, `abortCfg`) with action `none`) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:341-343
theorem glueSiteSound_iff_panicInDrop_fails_without_view :
    unwindCfg.panic = .unwind ∧ GlueSiteSound unwindCfg unwindCfg .none ∧
    ¬ (unwindCfg.panicInDrop = .abort ∨ Action.none.Stops = true) := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:348-351
theorem glueSiteSound_iff_panicInDrop_fails_without_glueCrateUnwind :
    (pidAbortCfg.panic = .abort ∨ pidAbortCfg.panicInDrop = .abort) ∧
    GlueSiteSound pidAbortCfg abortCfg .none ∧
    ¬ (abortCfg.panicInDrop = .abort ∨ Action.none.Stops = true) := by …
```

**Depth.** definitional.

**Non-vacuity witness.** cc = pidAbortCfg with cg = unwindCfg (both sides false) or cg = pidAbortCfg (both sides true).

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:335-337
theorem glueSiteSound_iff_panicInDrop_hypotheses_hold :
    (pidAbortCfg.panic = .abort ∨ pidAbortCfg.panicInDrop = .abort) ∧
    unwindCfg.panic = .unwind ∧ pidAbortCfg.panic = .unwind := by …
```

**Non-claims.** Listed under Boundaries, R11; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- Corpus report `rust-no-std-panic-abort-eh-personality-and-cross-crate-unwinding-abi-contracts` (no Lean mechanization): documents rustc's panic-strategy linking rules from source and experiments, including a check that the `-Z panic-in-drop` setting agrees across linked crates (it cites `dependency_format.rs:495-505` at the revision it pins). This package does not re-examine that check.

**Design question.** When may a caller treat drop glue as non-unwinding when panic-in-drop is a per-crate setting?

#### R12. `compRet_eq_specRet_of_conforms` (theorem)

**Plain claim.** Reference point. For every lawful toy ABI `A` (`A.dec (A.enc v) = v` for every `v`), every backend `b0` of the innermost callee and every chain of frames `frs`: if `b0` and the backend of every frame in `frs` conform to `A` (each uses exactly `A`'s encoding and decoding, as functions on all of `Nat`), then `compRet b0 frs v = specRet frs v` for every value `v`, that is, normal returns through the mixed chain give the specified result.

**Kind / tier.** theorem / T0. A known fact restated in the package's vocabulary (see prior art); kept as a reference point.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): none claimed. Toy ABI encodings correspond to no cited system; the result is a reference point.

**Statement.**

```lean
-- lean/ToyUnwindCap/ChainResults.lean:15-17
theorem compRet_eq_specRet_of_conforms (A : AbiCodec) (hA : A.Lawful) (b0 : AbiCodec)
    (frs : List RetFrame) (v : Nat) (h0 : Conforms b0 A)
    (hfrs : ∀ fr ∈ frs, Conforms fr.backend A) : compRet b0 frs v = specRet frs v := by …
```

**Unfolded (prose):** `A.Lawful` ≡ for every `v`, `A.dec (A.enc v) = v`. `Conforms b A` ≡ `b.enc = A.enc` and `b.dec = A.dec` (equality of functions on all of `Nat`). `specRet [] v = v` and `specRet (fr :: rest) v = specRet rest (fr.k v)`; `compRet b [] v = v` and `compRet b (fr :: rest) v = compRet fr.backend rest (fr.k (fr.backend.dec (b.enc v)))`: each frame decodes, with its own backend, the value its callee encoded with the callee's backend.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hA : A.Lawful` | there is a lossy common ABI for which even a single-backend chain differs from the specification | tight: counterexample `compRet_fails_without_lawful` (witness class: a 1-frame chain over `truncCodec` (encoding modulo 256, the floor-division remainder)) |
| `h0 : Conforms b0 A` | there is a self-consistent callee backend with a different encoding whose return value a conforming caller misreads | tight: counterexample `compRet_fails_without_calleeConforms` (witness class: a 1-frame chain whose callee uses `shiftCodec`) |
| `hfrs : ∀ fr ∈ frs, Conforms fr.backend A` | there is a self-consistent caller backend that misreads a conforming callee | tight: counterexample `compRet_fails_without_framesConform` (witness class: a 1-frame chain whose caller uses `shiftCodec` (decoding by truncated subtraction)) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:419-422
theorem compRet_fails_without_lawful :
    Conforms truncCodec truncCodec ∧
    (∀ fr ∈ [(⟨truncCodec, id⟩ : RetFrame)], Conforms fr.backend truncCodec) ∧
    compRet truncCodec [⟨truncCodec, id⟩] 300 ≠ specRet [⟨truncCodec, id⟩] 300 := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:430-433
theorem compRet_fails_without_calleeConforms :
    idCodec.Lawful ∧ shiftCodec.Lawful ∧
    (∀ fr ∈ [(⟨idCodec, id⟩ : RetFrame)], Conforms fr.backend idCodec) ∧
    compRet shiftCodec [⟨idCodec, id⟩] 5 ≠ specRet [⟨idCodec, id⟩] 5 := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:441-443
theorem compRet_fails_without_framesConform :
    idCodec.Lawful ∧ Conforms idCodec idCodec ∧ shiftCodec.Lawful ∧
    compRet idCodec [⟨shiftCodec, id⟩] 5 ≠ specRet [⟨shiftCodec, id⟩] 5 := …
```

**Depth.** shallow.

**Non-vacuity witness.** idCodec with the chain [(idCodec, +1), (idCodec, *2)] from 3 gives 8.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:410-413
theorem compRet_hypotheses_hold :
    idCodec.Lawful ∧ Conforms idCodec idCodec ∧
    (∀ fr ∈ [(⟨idCodec, (· + 1)⟩ : RetFrame), ⟨idCodec, (· * 2)⟩], Conforms fr.backend idCodec) ∧
    compRet idCodec [⟨idCodec, (· + 1)⟩, ⟨idCodec, (· * 2)⟩] 3 = 8 := by …
```

**Non-claims.** Listed under Boundaries, R12; a reader of this result must read them with it.

**Prior art.**

- J. Matthews, R. B. Findler, "Operational semantics for multi-language programs", ACM TOPLAS 31(3):12, 2009, doi:10.1145/1498926.1498930: general background on semantics of boundaries between languages; it does not treat ABI value encodings.
- Related report of the same corpus (a Lean formalization) `codec-round-trip-laws-and-partial-isomorphisms` (round-trip laws of total-encoder, fallible-decoder codecs, including the decode-after-encode law `DecEnc`); the composition argument here is the elementary instance of such a law.

**Design question.** What can be guaranteed when one call chain mixes functions compiled by backends with different landing-pad capabilities?

#### R13. `compUnwind_eq_specUnwind_iff_obligationsFull_of_noReachedNoneTerminate` (characterization)

**Plain claim.** For every call chain `c` (frames listed innermost first, each with the landing-pad capability `pads` of the backend that compiled it and the landing-pad action of its active call site) that satisfies `NoReachedNoneTerminate c` (no frame that the specified unwind reaches, up to and including the first frame whose action stops it, is a `pads = none` frame with a terminate pad; frames after that one are unconstrained): the compiled unwind `compUnwind c` (frames compiled with `pads = none` perform no landing-pad action) equals the specified unwind `specUnwind c` (same events, tagged with frame positions, and same outcome) iff `ObligationsFull c` (every frame that the specified unwind reaches, up to and including the first frame whose action stops it, and that has a non-empty cleanup pad, a catch pad or a terminate pad, was compiled with `pads = full`). The direction from `ObligationsFull c` holds without `NoReachedNoneTerminate c` and is stated separately as R18.

**Kind / tier.** characterization / T1. Mechanized exception propagation through frames exists in other formalisms (see prior art); no mechanized statement about mixed landing-pad capabilities was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). `pads = none` frames model code generators that emit frame-unwind information but no landing pads (B4); the reading of `catchPad` is limited by B5. No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/ChainResults.lean:222-224
theorem compUnwind_eq_specUnwind_iff_obligationsFull_of_noReachedNoneTerminate (c : List UFrame)
    (hterm : NoReachedNoneTerminate c) :
    compUnwind c = specUnwind c ↔ ObligationsFull c := …
```

**Unfolded (prose):** `specUnwind c` and `compUnwind c` walk the chain from frame 0, using `fr.act` and `fr.effAct` respectively as the action of frame `fr`, where `fr.effAct` is `fr.act` if `fr.pads = .full` and `.none` otherwise: action `none` passes to the next frame; `cleanup ds` emits `drop i x` for every `x` in `ds` (with `i` the frame position) and passes on; `catchPad` emits `caught i` and ends with outcome `caught i`; `terminate` ends with outcome `aborted` and no event; the end of the chain gives outcome `escapes`. `ObligationsFull []` holds, and `ObligationsFull (fr :: rest)` ≡ (`fr.act.obligation = true → fr.pads = .full`) ∧ (`fr.act.Stops = false → ObligationsFull rest`), where `Action.obligation` is `false` for `none` and `cleanup []` and `true` otherwise. `NoReachedNoneTerminate []` holds, and `NoReachedNoneTerminate (fr :: rest)` ≡ (`fr.pads = .none → fr.act ≠ .terminate`) ∧ (`fr.act.Stops = false → NoReachedNoneTerminate rest`).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hterm : NoReachedNoneTerminate c` | there is a chain in which an abort skipped by a reached `pads = none` frame is performed by a later frame with no observable difference, because the outcome `aborted` carries no frame position (unlike drop events and catches) | tight: counterexample `compUnwind_iff_fails_without_noReachedNoneTerminate` (witness class: a 2-frame chain `[⟨none, terminate⟩, ⟨full, terminate⟩]`) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:475-478
theorem compUnwind_iff_fails_without_noReachedNoneTerminate :
    compUnwind [⟨.none, .terminate⟩, ⟨.full, .terminate⟩] =
      specUnwind [⟨.none, .terminate⟩, ⟨.full, .terminate⟩] ∧
    ¬ ObligationsFull [⟨.none, .terminate⟩, ⟨.full, .terminate⟩] := by …
```

**Depth.** shallow.

**Non-vacuity witness.** [(full, cleanup [1]), (none, none), (full, catchPad)]: a pads = none frame is unwound through and both sides hold; [(none, cleanup [1]), (full, catchPad)]: both sides fail; [(full, catchPad), (none, terminate)]: the pads = none terminate frame is not reached, the hypothesis holds and both sides hold.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:450-459
theorem compUnwind_iff_hypotheses_hold :
    NoReachedNoneTerminate [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩] ∧
    compUnwind [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩] =
      specUnwind [⟨.full, .cleanup [1]⟩, ⟨.none, .none⟩, ⟨.full, .catchPad⟩] ∧
    NoReachedNoneTerminate [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] ∧
    compUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] ≠
      specUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] ∧
    NoReachedNoneTerminate [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] ∧
    compUnwind [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] =
      specUnwind [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] := by …
```

**Non-claims.** Listed under Boundaries, R13; a reader of this result must read them with it.

**Prior art.**

- G. Klein, T. Nipkow, "A machine-checked model for a Java-like language, virtual machine, and compiler", ACM TOPLAS 28(4):619-695, 2006, doi:10.1145/1146809.1146811: Isabelle/HOL semantics of a Java-like language with exceptions, a JVM-like machine and a verified compiler; mechanized exception propagation through frames, without cleanup obligations or backends lacking landing pads.
- T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", PACMPL 3(OOPSLA):146, 2019, doi:10.1145/3360572: validation and synthesis of DWARF `.eh_frame` unwind tables, the frame-unwind information that the `pads = none` modelling assumption presupposes.
- T. Ramananandro, G. Dos Reis, X. Leroy, "A mechanized semantics for C++ object construction and destruction, with applications to resource management", POPL 2012, doi:10.1145/2103621.2103718: a Coq semantics of C++ object construction and destruction order (resource management); it does not treat unwind classifications or landing-pad placement.
- rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c src/panic.md:86-101 (`panic.strategy`), 103-116 (`panic.unwind`), 124-128 (`panic.unwind.ffi.undefined`), 130-134 (`panic.unwind.ffi.catch-foreign`)
- Related reports of the same corpus (Lean formalizations), cited and not repeated (descriptions checked against their REPORT.md): `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction` (drop elaboration with drop flags, cleanup edges and the double-panic rule), `panic-safety-unwinding-through-broken-invariants-leak-amplification-and-safe-forget` (panic-safety obligations of unsafe collection code under unwinding), `call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations` (call-site inlining in a MIR-like language, including unwind actions and cleanup), `cfg-dwarf-cfi-state-stack-and-lsda-landing-pad-unwinding-soundness` (DWARF-style call-frame information and LSDA-style call-site tables over a given frame list), `explicit-tail-calls-frame-reuse-pre-jump-drop-order-stack-borrow-rejection-and-inlining` (a frame-stack machine with guaranteed tail calls, destructors and frame reuse). None of them treats whether a function may unwind as a classification made by a crate.

**Design question.** What can be guaranteed when one call chain mixes functions compiled by backends with different landing-pad capabilities?

#### R18. `compUnwind_eq_specUnwind_of_obligationsFull` (theorem)

**Plain claim.** Companion of R13 (stated as its own card). For every call chain `c` that satisfies `ObligationsFull c` (every frame that the specified unwind reaches, up to and including the first frame whose action stops it, and that has a non-empty cleanup pad, a catch pad or a terminate pad, was compiled with `pads = full`), the compiled unwind `compUnwind c` equals the specified unwind `specUnwind c`. No condition on `pads = none` terminate frames is assumed.

**Kind / tier.** theorem / T1. Mechanized exception propagation through frames exists in other formalisms (see prior art); no mechanized statement about mixed landing-pad capabilities was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge), as for R13 (B4, B5). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/ChainResults.lean:229-230
theorem compUnwind_eq_specUnwind_of_obligationsFull (c : List UFrame) (h : ObligationsFull c) :
    compUnwind c = specUnwind c := …
```

**Unfolded (prose):** `ObligationsFull`, `compUnwind` and `specUnwind` are as in R13; the conclusion is equality of the pairs (event list, outcome).

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h : ObligationsFull c` | there is a chain with a reached `pads = none` frame carrying a cleanup pad whose drop event the compiled unwind loses | tight: counterexample `compUnwind_of_obligationsFull_fails_without_obligationsFull` (witness class: a 2-frame chain `[⟨none, cleanup [1]⟩, ⟨full, catchPad⟩]`) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:484-487
theorem compUnwind_of_obligationsFull_fails_without_obligationsFull :
    ¬ ObligationsFull [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] ∧
    compUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] ≠
      specUnwind [⟨.none, .cleanup [1]⟩, ⟨.full, .catchPad⟩] := …
```

**Depth.** shallow.

**Non-vacuity witness.** [(full, catchPad), (none, terminate)] satisfies ObligationsFull (its pads = none terminate frame is not reached).

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:466-469
theorem compUnwind_eq_specUnwind_of_obligationsFull_hypotheses_hold :
    ObligationsFull [⟨.full, .catchPad⟩, ⟨.none, .terminate⟩] ∧
    ¬ (∀ fr ∈ [(⟨.full, .catchPad⟩ : UFrame), ⟨.none, .terminate⟩],
      fr.pads = .none → fr.act ≠ .terminate) := by …
```

**Non-claims.** Listed under Boundaries, R18; a reader of this result must read them with it.

**Prior art.**

- G. Klein, T. Nipkow, "A machine-checked model for a Java-like language, virtual machine, and compiler", ACM TOPLAS 28(4):619-695, 2006, doi:10.1145/1146809.1146811: Isabelle/HOL semantics of a Java-like language with exceptions, a JVM-like machine and a verified compiler; mechanized exception propagation through frames, without cleanup obligations or backends lacking landing pads.
- T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", PACMPL 3(OOPSLA):146, 2019, doi:10.1145/3360572: validation and synthesis of DWARF `.eh_frame` unwind tables, the frame-unwind information that the `pads = none` modelling assumption presupposes.
- T. Ramananandro, G. Dos Reis, X. Leroy, "A mechanized semantics for C++ object construction and destruction, with applications to resource management", POPL 2012, doi:10.1145/2103621.2103718: a Coq semantics of C++ object construction and destruction order (resource management); it does not treat unwind classifications or landing-pad placement.
- Related reports of the same corpus (Lean formalizations), cited and not repeated (descriptions checked against their REPORT.md): `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction` (drop elaboration with drop flags, cleanup edges and the double-panic rule), `panic-safety-unwinding-through-broken-invariants-leak-amplification-and-safe-forget` (panic-safety obligations of unsafe collection code under unwinding), `call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations` (call-site inlining in a MIR-like language, including unwind actions and cleanup), `cfg-dwarf-cfi-state-stack-and-lsda-landing-pad-unwinding-soundness` (DWARF-style call-frame information and LSDA-style call-site tables over a given frame list), `explicit-tail-calls-frame-reuse-pre-jump-drop-order-stack-borrow-rejection-and-inlining` (a frame-stack machine with guaranteed tail calls, destructors and frame reuse). None of them treats whether a function may unwind as a classification made by a crate.

**Design question.** What can be guaranteed when one call chain mixes functions compiled by backends with different landing-pad capabilities?

#### R14. `robust_iff_shielded` (characterization)

**Plain claim.** For every call chain `c`: the compiled and specified unwinds agree on every chain `c'` with `SameShape c c'` (the same backend capability frame by frame and the same actions at every `pads = full` frame, any actions at `pads = none` frames) iff `Shielded c`, that is, scanning from the innermost frame, every frame is compiled with `pads = full` up to and including the first frame whose action stops the unwind (`catchPad` or `terminate`), or up to the end of the chain if no frame stops it.

**Kind / tier.** characterization / T1. Mechanized exception propagation through frames exists in other formalisms (see prior art); no mechanized statement about mixed landing-pad capabilities was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge), as for R13 (B4, B5). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/ChainResults.lean:239-240
theorem robust_iff_shielded (c : List UFrame) :
    (∀ c', SameShape c c' → compUnwind c' = specUnwind c') ↔ Shielded c := …
```

**Unfolded (prose):** `SameShape [] []` holds; `SameShape (a :: as) (b :: bs)` ≡ `a.pads = b.pads` ∧ (`a.pads = .full → a.act = b.act`) ∧ `SameShape as bs`; lists of different lengths are never `SameShape`. `Shielded []` holds, and `Shielded (fr :: rest)` ≡ `fr.pads = .full` ∧ (`fr.act.Stops = true` ∨ `Shielded rest`). `compUnwind` and `specUnwind` are as in R13.

**Hypothesis ledger.** No hypotheses beyond the universally quantified variables.

**Depth.** shallow.

**Non-vacuity witness.** [(full, catchPad), (none, none)] is Shielded (by a catch pad) but not TerminateShielded; [(none, none)] is not Shielded.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:494-497
theorem shielded_not_terminateShielded :
    Shielded [⟨.full, .catchPad⟩, ⟨.none, .none⟩] ∧
    ¬ TerminateShielded [⟨.full, .catchPad⟩, ⟨.none, .none⟩] ∧
    ∀ c', SameShape [⟨.full, .catchPad⟩, ⟨.none, .none⟩] c' → compUnwind c' = specUnwind c' := …
```

```lean
-- lean/ToyUnwindCap/Examples.lean:314-317
theorem shielded_examples :
    Shielded [⟨.full, .catchPad⟩, ⟨.none, .none⟩] ∧ ¬ Shielded [⟨.none, .none⟩] ∧
    TerminateShielded [⟨.full, .none⟩, ⟨.full, .terminate⟩, ⟨.none, .none⟩] ∧
    ¬ TerminateShielded [⟨.full, .catchPad⟩, ⟨.none, .none⟩] := by …
```

**Non-claims.** Listed under Boundaries, R14; a reader of this result must read them with it.

**Prior art.**

- G. Klein, T. Nipkow, "A machine-checked model for a Java-like language, virtual machine, and compiler", ACM TOPLAS 28(4):619-695, 2006, doi:10.1145/1146809.1146811: Isabelle/HOL semantics of a Java-like language with exceptions, a JVM-like machine and a verified compiler; mechanized exception propagation through frames, without cleanup obligations or backends lacking landing pads.
- T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", PACMPL 3(OOPSLA):146, 2019, doi:10.1145/3360572: validation and synthesis of DWARF `.eh_frame` unwind tables, the frame-unwind information that the `pads = none` modelling assumption presupposes.
- Related reports of the same corpus (Lean formalizations), cited and not repeated (descriptions checked against their REPORT.md): `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction` (drop elaboration with drop flags, cleanup edges and the double-panic rule), `panic-safety-unwinding-through-broken-invariants-leak-amplification-and-safe-forget` (panic-safety obligations of unsafe collection code under unwinding), `call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations` (call-site inlining in a MIR-like language, including unwind actions and cleanup), `cfg-dwarf-cfi-state-stack-and-lsda-landing-pad-unwinding-soundness` (DWARF-style call-frame information and LSDA-style call-site tables over a given frame list), `explicit-tail-calls-frame-reuse-pre-jump-drop-order-stack-borrow-rejection-and-inlining` (a frame-stack machine with guaranteed tail calls, destructors and frame reuse). None of them treats whether a function may unwind as a classification made by a crate.

**Design question.** What can be guaranteed when one call chain mixes functions compiled by backends with different landing-pad capabilities?

#### R15. `robust_of_terminateShielded` (theorem)

**Plain claim.** Corollary of R14. For every call chain `c` with `TerminateShielded c` (scanning from the innermost frame, every frame is compiled with `pads = full` up to and including the first frame with a terminate pad, or up to the end of the chain if there is none), the compiled and specified unwinds agree on every chain `c'` with `SameShape c c'`.

**Kind / tier.** theorem / T1. Mechanized exception propagation through frames exists in other formalisms (see prior art); no mechanized statement about mixed landing-pad capabilities was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge), as for R13 (B4, B5); terminate shielding is the toy counterpart of RFC 2945's aborting landing pad (B1). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/ChainResults.lean:256-257
theorem robust_of_terminateShielded (c : List UFrame) (h : TerminateShielded c) :
    ∀ c', SameShape c c' → compUnwind c' = specUnwind c' := …
```

**Unfolded (prose):** `TerminateShielded []` holds, and `TerminateShielded (fr :: rest)` ≡ `fr.pads = .full` ∧ (`fr.act = .terminate` ∨ `TerminateShielded rest`). `SameShape`, `compUnwind` and `specUnwind` are as in R13 and R14.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `h : TerminateShielded c` | otherwise an unwind can reach a `pads = none` frame with an obligation; sufficient, and not necessary for the conclusion (`shielded_not_terminateShielded`) | tight: counterexample `robust_fails_without_terminateShielded` (witness class: the 1-frame chain `[⟨none, cleanup [1]⟩]`) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:507-509
theorem robust_fails_without_terminateShielded :
    SameShape [⟨.none, .cleanup [1]⟩] [⟨.none, .cleanup [1]⟩] ∧
    compUnwind [⟨.none, .cleanup [1]⟩] ≠ specUnwind [⟨.none, .cleanup [1]⟩] := …
```

**Depth.** definitional.

**Non-vacuity witness.** [(full, none), (full, terminate), (none, none)].

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:501-502
theorem robust_of_terminateShielded_hypotheses_hold :
    TerminateShielded [⟨.full, .none⟩, ⟨.full, .terminate⟩, ⟨.none, .none⟩] := …
```

**Non-claims.** Listed under Boundaries, R15; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)
- D. Abrahams, R. Sharoni, D. Gregor, "Allowing Move Constructors to Throw (Rev. 1)", ISO/IEC JTC1/SC22/WG21 N3050, 2010-03-12 (open-std.org/jtc1/sc22/wg21/docs/papers/2010/n3050.html): proposes the C++ `noexcept` specification together with wording changes to `[except.spec]` and `[except.terminate]` (`std::terminate`); the C++ analogue of enforcing a non-unwinding declaration by termination. No mechanized semantics.

**Design question.** What can be guaranteed when one call chain mixes functions compiled by backends with different landing-pad capabilities?

#### R16. `withPads_exec_iff_of_padsNone_nonunwinding_of_enforcedAt_of_siteAgreementAt` (theorem)

**Plain claim.** For every precedence function `cu`, toy program `p` and backend assignment `pads` (functions compiled with `pads = none` lose every landing pad, giving `p.withPads pads`): if every non-foreign function `g < p.fns.length` with `pads g = none` (reachable or not) is classified as non-unwinding by its own crate, and the compiled program `p.withPads pads` satisfies `EnforcedAt cu (p.withPads pads) g` (the per-function condition of `Enforced` in R1: if `g` is non-foreign and classified as non-unwinding by its own crate, then every call in its compiled body to a callee that this crate classifies as possibly unwinding carries a stopping pad, and, when the panic handler is `unwind`, every panic point in that body carries a stopping pad) and `SiteAgreementAt cu (p.withPads pads) g` (the per-function condition of `SiteAgreement` in R1) at every function index `g` with `pads g = none` (reachable or not), then every function has exactly the same finite runs produced by `runFn` (traces and outcomes) in `p.withPads pads` as in `p`. It is derived from R17.

**Kind / tier.** theorem / T1. Mechanized exception propagation through frames exists in other formalisms (see prior art); no mechanized statement about mixed landing-pad capabilities was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge). `p.withPads pads` models functions compiled by code generators without landing pads whose frames stay unwindable (B4). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:1116-1122
theorem withPads_exec_iff_of_padsNone_nonunwinding_of_enforcedAt_of_siteAgreementAt (cu : Prec)
    (p : Prog) (pads : Nat → Pads)
    (hnone : ∀ g, g < p.fns.length → pads g = .none → (p.fn g).info.foreign = false →
      p.selfMay cu g = false)
    (henf : ∀ g, pads g = .none → EnforcedAt cu (p.withPads pads) g)
    (hsa : ∀ g, pads g = .none → SiteAgreementAt cu (p.withPads pads) g) :
    ∀ f t o, Exec cu (p.withPads pads) f t o ↔ Exec cu p f t o := by …
```

**Unfolded (prose):** `p.withPads pads` keeps `p.crates` and `p.handler`, keeps the function at every index `g` of `p.fns` with `pads g = .full`, and maps every statement of the body of a function with `pads g = .none` by `Stmt.unpadded` (`.raise _` becomes `.raise .none`, `.call f _` becomes `.call f .none`). `EnforcedAt` and `SiteAgreementAt` are the per-index conditions of R1, here applied to the compiled program `p.withPads pads` at the indices with `pads g = .none`; `p.selfMay cu g` and `Exec` are as in R1. The conclusion is that for every `f`, `t` and `o`, `Exec cu (p.withPads pads) f t o` holds iff `Exec cu p f t o` holds.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hnone : ∀ g, g < p.fns.length → pads g = .none → (p.fn g).info.foreign = false → p.selfMay cu g = false` | there is a possibly-unwinding `pads = none` function that is unwound through and loses a cleanup pad | tight: counterexample `withPads_fails_without_padsNoneNonUnwinding` (witness class: a 1-crate, 2-function program whose `pads = none` function is a possibly-unwinding Rust function (`progPadsMayUnwind`)) |
| `henf : ∀ g, pads g = .none → EnforcedAt cu (p.withPads pads) g` | enforcement after pads are removed; tight against the weakening to the source program (the counterexample satisfies `Enforced cu p` program-wide) | tight: counterexample `withPads_fails_without_enforcedCompiled` (witness class: a 1-crate, 2-function program whose `pads = none` function calls a panicking function through a terminate pad (`progPadsTerminate`)) |
| `hsa : ∀ g, pads g = .none → SiteAgreementAt cu (p.withPads pads) g` | agreement after pads are removed; tight against the weakening to the source program (the counterexample satisfies `SiteAgreement cu p` program-wide) | tight: counterexample `withPads_fails_without_siteAgreementCompiled` (witness class: a 2-crate, 2-function mixed-strategy program (`progPadsAgree`)) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:600-606
theorem withPads_fails_without_padsNoneNonUnwinding :
    (∀ g, padsNoneAt0 g = .none →
      EnforcedAt stdCanUnwind (progPadsMayUnwind.withPads padsNoneAt0) g) ∧
    (∀ g, padsNoneAt0 g = .none →
      SiteAgreementAt stdCanUnwind (progPadsMayUnwind.withPads padsNoneAt0) g) ∧
    Exec stdCanUnwind progPadsMayUnwind 0 [.drop 0 0] .unwind ∧
    ¬ Exec stdCanUnwind (progPadsMayUnwind.withPads padsNoneAt0) 0 [.drop 0 0] .unwind := …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:620-628
theorem withPads_fails_without_enforcedCompiled :
    (∀ g, g < progPadsTerminate.fns.length → padsNoneAt0 g = .none →
      (progPadsTerminate.fn g).info.foreign = false →
        progPadsTerminate.selfMay stdCanUnwind g = false) ∧
    (∀ g, padsNoneAt0 g = .none →
      SiteAgreementAt stdCanUnwind (progPadsTerminate.withPads padsNoneAt0) g) ∧
    Enforced stdCanUnwind progPadsTerminate ∧
    Exec stdCanUnwind (progPadsTerminate.withPads padsNoneAt0) 0 [] .ub ∧
    ¬ Exec stdCanUnwind progPadsTerminate 0 [] .ub := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:648-655
theorem withPads_fails_without_siteAgreementCompiled :
    (∀ g, g < progPadsAgree.fns.length → padsNoneAt0 g = .none →
      (progPadsAgree.fn g).info.foreign = false → progPadsAgree.selfMay stdCanUnwind g = false) ∧
    (∀ g, padsNoneAt0 g = .none →
      EnforcedAt stdCanUnwind (progPadsAgree.withPads padsNoneAt0) g) ∧
    SiteAgreement stdCanUnwind progPadsAgree ∧
    Exec stdCanUnwind (progPadsAgree.withPads padsNoneAt0) 0 [] .ub ∧
    ¬ Exec stdCanUnwind progPadsAgree 0 [] .ub := by …
```

**Depth.** definitional.

**Non-vacuity witness.** progPadsNonvac: a pads = none extern "C" function calls a pads = full extern "C" function, which calls a panicking Rust function through a terminate pad; both programs abort. progPadsFullUnenforced: the hypotheses hold although the compiled program violates Enforced and SiteAgreement at pads = full functions.

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:521-529
theorem withPads_hypotheses_hold_progPadsNonvac :
    (∀ g, g < progPadsNonvac.fns.length → padsNoneAt0 g = .none →
      (progPadsNonvac.fn g).info.foreign = false → progPadsNonvac.selfMay stdCanUnwind g = false) ∧
    (∀ g, padsNoneAt0 g = .none →
      EnforcedAt stdCanUnwind (progPadsNonvac.withPads padsNoneAt0) g) ∧
    (∀ g, padsNoneAt0 g = .none →
      SiteAgreementAt stdCanUnwind (progPadsNonvac.withPads padsNoneAt0) g) ∧
    Exec stdCanUnwind (progPadsNonvac.withPads padsNoneAt0) 0 [] .abort ∧
    Exec stdCanUnwind progPadsNonvac 0 [] .abort := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:550-559
theorem withPads_hypotheses_hold_progPadsFullUnenforced :
    (∀ g, g < progPadsFullUnenforced.fns.length → padsNoneAt0 g = .none →
      (progPadsFullUnenforced.fn g).info.foreign = false →
        progPadsFullUnenforced.selfMay stdCanUnwind g = false) ∧
    (∀ g, padsNoneAt0 g = .none →
      EnforcedAt stdCanUnwind (progPadsFullUnenforced.withPads padsNoneAt0) g) ∧
    (∀ g, padsNoneAt0 g = .none →
      SiteAgreementAt stdCanUnwind (progPadsFullUnenforced.withPads padsNoneAt0) g) ∧
    ¬ Enforced stdCanUnwind (progPadsFullUnenforced.withPads padsNoneAt0) ∧
    ¬ SiteAgreement stdCanUnwind (progPadsFullUnenforced.withPads padsNoneAt0) := by …
```

**Non-claims.** Listed under Boundaries, R16; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)
- rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe compiler/rustc_middle/src/ty/layout.rs:1225-1330 (`fn_can_unwind`: doc comment 1225-1264, ordered rules 1267-1330; excerpts quoted verbatim in REPORT.md)
- D. Abrahams, R. Sharoni, D. Gregor, "Allowing Move Constructors to Throw (Rev. 1)", ISO/IEC JTC1/SC22/WG21 N3050, 2010-03-12 (open-std.org/jtc1/sc22/wg21/docs/papers/2010/n3050.html): proposes the C++ `noexcept` specification together with wording changes to `[except.spec]` and `[except.terminate]` (`std::terminate`); the C++ analogue of enforcing a non-unwinding declaration by termination. No mechanized semantics.
- T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", PACMPL 3(OOPSLA):146, 2019, doi:10.1145/3360572: validation and synthesis of DWARF `.eh_frame` unwind tables, the frame-unwind information that the `pads = none` modelling assumption presupposes.
- Related reports of the same corpus (Lean formalizations), cited and not repeated (descriptions checked against their REPORT.md): `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction` (drop elaboration with drop flags, cleanup edges and the double-panic rule), `panic-safety-unwinding-through-broken-invariants-leak-amplification-and-safe-forget` (panic-safety obligations of unsafe collection code under unwinding), `call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations` (call-site inlining in a MIR-like language, including unwind actions and cleanup), `cfg-dwarf-cfi-state-stack-and-lsda-landing-pad-unwinding-soundness` (DWARF-style call-frame information and LSDA-style call-site tables over a given frame list), `explicit-tail-calls-frame-reuse-pre-jump-drop-order-stack-borrow-rejection-and-inlining` (a frame-stack machine with guaranteed tail calls, destructors and frame reuse). None of them treats whether a function may unwind as a classification made by a crate.

**Design question.** What can be guaranteed when one call chain mixes functions compiled by backends with different landing-pad capabilities?

#### R17. `withPads_exec_iff_of_padsNone_obligationFreeRaises_of_obligationCalleesNonUnwinding` (theorem)

**Plain claim.** For every precedence function `cu`, toy program `p` and backend assignment `pads`: if, in every non-foreign function `g < p.fns.length` with `pads g = none` (reachable or not), every panic point has an action without an obligation (`Action.obligation`: `none` or `cleanup []`) when the panic handler is `unwind` (`hraise`), and every call whose action has an obligation (a non-empty cleanup pad, a catch pad or a terminate pad) calls a callee `f` classified as non-unwinding by `f`'s own crate (`hcall`), then every function has exactly the same finite runs produced by `runFn` (traces and outcomes) in `p.withPads pads` as in `p`. Calls without an obligation are unconstrained, so an unwind may pass through a `pads = none` function that has no landing-pad obligation.

**Kind / tier.** theorem / T1. Mechanized exception propagation through frames exists in other formalisms (see prior art); no mechanized statement about mixed landing-pad capabilities was found in the recorded search.

**Proof status.** kernel-checked (no `sorry`; axioms of every declaration under Evidence).

Basis: execution (Lean kernel check).

Basis (relation to real systems): derived (modeling bridge), as for R16 (B4). No relation is proved.

**Statement.**

```lean
-- lean/ToyUnwindCap/Results.lean:1026-1032
theorem withPads_exec_iff_of_padsNone_obligationFreeRaises_of_obligationCalleesNonUnwinding
    (cu : Prec) (p : Prog) (pads : Nat → Pads)
    (hraise : ∀ g, g < p.fns.length → pads g = .none → (p.fn g).info.foreign = false →
      p.handler = .unwind → ∀ a, Stmt.raise a ∈ (p.fn g).body → a.obligation = false)
    (hcall : ∀ g, g < p.fns.length → pads g = .none → (p.fn g).info.foreign = false →
      ∀ f a, Stmt.call f a ∈ (p.fn g).body → a.obligation = true → p.selfMay cu f = false) :
    ∀ f t o, Exec cu (p.withPads pads) f t o ↔ Exec cu p f t o := by …
```

**Unfolded (prose):** `Action.obligation` is `false` for `none` and for `cleanup []`, and `true` for `cleanup ds` with non-empty `ds`, for `catchPad` and for `terminate`. `p.withPads pads` is as in R16; `p.selfMay cu f` and `Exec` are as in R1. The hypotheses constrain the bodies of the non-foreign functions with index below `p.fns.length` and `pads g = .none`, and no other function; `hraise` constrains panic points when `p.handler = .unwind` and is vacuous otherwise.

**Hypothesis ledger.**

| Hypothesis | Why it is there | Tightness |
| :--- | :--- | :--- |
| `hraise : ∀ g, g < p.fns.length → pads g = .none → (p.fn g).info.foreign = false → p.handler = .unwind → ∀ a, Stmt.raise a ∈ (p.fn g).body → a.obligation = false` | there is a program in which a panic point of a `pads = none` function loses its cleanup pad and a drop event disappears | tight: counterexample `withPads_local_fails_without_obligationFreeRaises` (witness class: a 1-crate, 1-function program whose `pads = none` function has a panic point with a cleanup pad dropping one local (`progPadsRaiseCleanup`)) |
| `hcall : ∀ g, g < p.fns.length → pads g = .none → (p.fn g).info.foreign = false → ∀ f a, Stmt.call f a ∈ (p.fn g).body → a.obligation = true → p.selfMay cu f = false` | there is a program in which an unwind from a callee reaches a call site of a `pads = none` function whose cleanup pad is lost | tight: counterexample `withPads_local_fails_without_obligationCalleesNonUnwinding` (witness class: a 1-crate, 2-function program whose `pads = none` function calls a panicking function through a cleanup pad dropping one local (`progPadsMayUnwind`)) |

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:775-781
theorem withPads_local_fails_without_obligationFreeRaises :
    (∀ g, g < progPadsRaiseCleanup.fns.length → padsNoneAt0 g = .none →
      (progPadsRaiseCleanup.fn g).info.foreign = false →
        ∀ f a, Stmt.call f a ∈ (progPadsRaiseCleanup.fn g).body → a.obligation = true →
          progPadsRaiseCleanup.selfMay stdCanUnwind f = false) ∧
    Exec stdCanUnwind progPadsRaiseCleanup 0 [.drop 0 0] .unwind ∧
    ¬ Exec stdCanUnwind (progPadsRaiseCleanup.withPads padsNoneAt0) 0 [.drop 0 0] .unwind := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:797-802
theorem withPads_local_fails_without_obligationCalleesNonUnwinding :
    (∀ g, g < progPadsMayUnwind.fns.length → padsNoneAt0 g = .none →
      (progPadsMayUnwind.fn g).info.foreign = false → progPadsMayUnwind.handler = .unwind →
        ∀ a, Stmt.raise a ∈ (progPadsMayUnwind.fn g).body → a.obligation = false) ∧
    Exec stdCanUnwind progPadsMayUnwind 0 [.drop 0 0] .unwind ∧
    ¬ Exec stdCanUnwind (progPadsMayUnwind.withPads padsNoneAt0) 0 [.drop 0 0] .unwind := by …
```

**Depth.** shallow.

**Non-vacuity witness.** progPadsNonvac (the pads = none function calls a non-unwinding extern "C" function through a cleanup pad); progAbortPadsRaise (a pads = none function with a panic point under the abort handler); progPadsPlainUnwindThrough (a possibly-unwinding pads = none Rust function calls a panicking function with a plain call, and the unwind passes through it); progPadsRaisePlain (a pads = none function whose panic point has no landing pad, under the unwind handler).

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:668-675
theorem withPads_local_hypotheses_hold_progPadsNonvac :
    (∀ g, g < progPadsNonvac.fns.length → padsNoneAt0 g = .none →
      (progPadsNonvac.fn g).info.foreign = false → progPadsNonvac.handler = .unwind →
        ∀ a, Stmt.raise a ∈ (progPadsNonvac.fn g).body → a.obligation = false) ∧
    (∀ g, g < progPadsNonvac.fns.length → padsNoneAt0 g = .none →
      (progPadsNonvac.fn g).info.foreign = false →
        ∀ f a, Stmt.call f a ∈ (progPadsNonvac.fn g).body → a.obligation = true →
          progPadsNonvac.selfMay stdCanUnwind f = false) := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:694-702
theorem withPads_local_hypotheses_hold_progAbortPadsRaise :
    (∀ g, g < progAbortPadsRaise.fns.length → padsNoneAt0 g = .none →
      (progAbortPadsRaise.fn g).info.foreign = false → progAbortPadsRaise.handler = .unwind →
        ∀ a, Stmt.raise a ∈ (progAbortPadsRaise.fn g).body → a.obligation = false) ∧
    (∀ g, g < progAbortPadsRaise.fns.length → padsNoneAt0 g = .none →
      (progAbortPadsRaise.fn g).info.foreign = false →
        ∀ f a, Stmt.call f a ∈ (progAbortPadsRaise.fn g).body → a.obligation = true →
          progAbortPadsRaise.selfMay stdCanUnwind f = false) ∧
    Exec stdCanUnwind (progAbortPadsRaise.withPads padsNoneAt0) 0 [] .abort := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:718-728
theorem withPads_local_hypotheses_hold_progPadsPlainUnwindThrough :
    (∀ g, g < progPadsPlainUnwindThrough.fns.length → padsNoneAt0 g = .none →
      (progPadsPlainUnwindThrough.fn g).info.foreign = false →
        progPadsPlainUnwindThrough.handler = .unwind →
        ∀ a, Stmt.raise a ∈ (progPadsPlainUnwindThrough.fn g).body → a.obligation = false) ∧
    (∀ g, g < progPadsPlainUnwindThrough.fns.length → padsNoneAt0 g = .none →
      (progPadsPlainUnwindThrough.fn g).info.foreign = false →
        ∀ f a, Stmt.call f a ∈ (progPadsPlainUnwindThrough.fn g).body → a.obligation = true →
          progPadsPlainUnwindThrough.selfMay stdCanUnwind f = false) ∧
    Exec stdCanUnwind (progPadsPlainUnwindThrough.withPads padsNoneAt0) 0 [] .unwind ∧
    progPadsPlainUnwindThrough.selfMay stdCanUnwind 0 = true := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:749-757
theorem withPads_local_hypotheses_hold_progPadsRaisePlain :
    (∀ g, g < progPadsRaisePlain.fns.length → padsNoneAt0 g = .none →
      (progPadsRaisePlain.fn g).info.foreign = false → progPadsRaisePlain.handler = .unwind →
        ∀ a, Stmt.raise a ∈ (progPadsRaisePlain.fn g).body → a.obligation = false) ∧
    (∀ g, g < progPadsRaisePlain.fns.length → padsNoneAt0 g = .none →
      (progPadsRaisePlain.fn g).info.foreign = false →
        ∀ f a, Stmt.call f a ∈ (progPadsRaisePlain.fn g).body → a.obligation = true →
          progPadsRaisePlain.selfMay stdCanUnwind f = false) ∧
    Exec stdCanUnwind (progPadsRaisePlain.withPads padsNoneAt0) 0 [] .unwind := by …
```

**Non-claims.** Listed under Boundaries, R17; a reader of this result must read them with it.

**Prior art.**

- rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 text/2945-c-unwind-abi.md:205-209, 230-235 and 366-375 (RFC 2945, the "C-unwind" ABI, merged; quoted verbatim in REPORT.md)
- T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and fast DWARF-based stack unwinding", PACMPL 3(OOPSLA):146, 2019, doi:10.1145/3360572: validation and synthesis of DWARF `.eh_frame` unwind tables, the frame-unwind information that the `pads = none` modelling assumption presupposes.
- Related reports of the same corpus (Lean formalizations), cited and not repeated (descriptions checked against their REPORT.md): `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction` (drop elaboration with drop flags, cleanup edges and the double-panic rule), `panic-safety-unwinding-through-broken-invariants-leak-amplification-and-safe-forget` (panic-safety obligations of unsafe collection code under unwinding), `call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations` (call-site inlining in a MIR-like language, including unwind actions and cleanup), `cfg-dwarf-cfi-state-stack-and-lsda-landing-pad-unwinding-soundness` (DWARF-style call-frame information and LSDA-style call-site tables over a given frame list), `explicit-tail-calls-frame-reuse-pre-jump-drop-order-stack-borrow-rejection-and-inlining` (a frame-stack machine with guaranteed tail calls, destructors and frame reuse). None of them treats whether a function may unwind as a classification made by a crate.

**Design question.** What can be guaranteed when one call chain mixes functions compiled by backends with different landing-pad capabilities?

### Auxiliary declarations cited by name

Every package-local declaration that this report mentions by name and does not quote elsewhere (definitions, example programs, lemmas, the abort-handler escape hatch of R10 and the refutations of earlier candidate statements).

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:942-946
theorem abiFirst_insertPads_lets_foreign_unwind_leave_abort_crate :
    insertPads abiFirstCanUnwind progAbortCUnwindExport = progAbortCUnwindExport ∧
    Exec abiFirstCanUnwind progAbortCUnwindExport 0 [] .unwind ∧
    ((insertPads stdCanUnwind progAbortCUnwindExport).fn 0).body = [.call 1 .terminate] ∧
    Exec stdCanUnwind (insertPads stdCanUnwind progAbortCUnwindExport) 0 [] .abort := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:240-240
def abortBothCfg : CrateCfg := ⟨.abort, .abort⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:954-956
theorem compRet_nil_and_linkOK_of_no_crates (b0 : AbiCodec) (v : Nat) (fns : List FnDef)
    (h : Strategy) :
    compRet b0 [] v = v ∧ specRet [] v = v ∧ LinkOK ⟨[], fns, h⟩ := …
```

```lean
-- lean/ToyUnwindCap/Results.lean:640-641
theorem crateOf_unwind_of_linkOK_of_potentiallyUnwinding (p : Prog) (hlink : LinkOK p)
    (hpu : PotentiallyUnwinding p) (g : Nat) : (p.crateOf g).panic = .unwind := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:357-359
theorem glueProg_abort_handler_noUB (cc cg : CrateCfg) (act : Action) (body : List Stmt) :
    ∀ f t o, Exec stdCanUnwind { glueProg cc cg act body with handler := .abort } f t o →
      o ≠ .ub := by …
```

```lean
-- lean/ToyUnwindCap/Results.lean:367-370
theorem insertPads_body_ne_iff (cu : Prec) (p : Prog) (g : Nat) :
    ((insertPads cu p).fn g).body ≠ (p.fn g).body ↔
      ((p.fn g).info.foreign = false ∧ p.selfMay cu g = false) ∧
        ∃ s ∈ (p.fn g).body, padStmt cu p g s ≠ s := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:919-922
theorem insertPads_pad_without_unwinding_callee :
    progCalmCallee.viewMay stdCanUnwind 0 1 = true ∧
    ((insertPads stdCanUnwind progCalmCallee).fn 0).body = [.call 1 .terminate] ∧
    ¬ (∃ t, Exec stdCanUnwind progCalmCallee 1 t .unwind) := by …
```

```lean
-- lean/ToyUnwindCap/Results.lean:334-336
theorem padStmt_call_ne_iff (cu : Prec) (p : Prog) (g f : Nat) (act : Action) :
    padStmt cu p g (.call f act) ≠ .call f act ↔
      (p.viewMay cu g f = true ∧ act.Stops = false) := by …
```

```lean
-- lean/ToyUnwindCap/Results.lean:342-344
theorem padStmt_raise_ne_iff (cu : Prec) (p : Prog) (g : Nat) (act : Action) :
    padStmt cu p g (.raise act) ≠ .raise act ↔
      (p.handler = .unwind ∧ act.Stops = false) := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:935-937
def progAbortCUnwindExport : Prog :=
  ⟨[abortCfg], [⟨rustDefinedCUnwind, 0, [.call 1 .none], false⟩, ⟨foreignCUnwind, 0, [], true⟩],
    .abort⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:689-690
def progAbortPadsRaise : Prog :=
  ⟨[abortCfg], [⟨rustInfo, 0, [.raise .terminate], false⟩], .abort⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:914-915
def progCalmCallee : Prog :=
  ⟨[unwindCfg], [⟨cFn, 0, [.call 1 .none], false⟩, ⟨rustInfo, 0, [], false⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:883-886
def progCleanupOverwritten : Prog :=
  ⟨[unwindCfg],
    [⟨cFn, 0, [.call 2 (.cleanup [7])], false⟩, ⟨cFn, 0, [.raise (.cleanup [7])], false⟩,
     ⟨rustInfo, 0, [.raise .none], false⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:245-247
def progMixedAbortBothCallsGlue : Prog :=
  ⟨[abortBothCfg, unwindCfg],
    [⟨rustInfo, 0, [.call 1 .none], false⟩, ⟨glueInfo, 1, [.raise .none], false⟩], .abort⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:542-546
def progPadsFullUnenforced : Prog :=
  ⟨[unwindCfg, abortCfg],
    [⟨cFn, 0, [.call 1 (.cleanup [3])], false⟩, ⟨cFn, 0, [.raise .none], false⟩,
     ⟨rustInfo, 1, [.call 3 .none], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:710-712
def progPadsPlainUnwindThrough : Prog :=
  ⟨[unwindCfg], [⟨rustInfo, 0, [.call 1 .none], false⟩, ⟨rustInfo, 0, [.raise .none], false⟩],
    .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:771-772
def progPadsRaiseCleanup : Prog :=
  ⟨[unwindCfg], [⟨rustInfo, 0, [.raise (.cleanup [0])], false⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:743-744
def progPadsRaisePlain : Prog :=
  ⟨[unwindCfg], [⟨rustInfo, 0, [.raise .none], false⟩], .unwind⟩
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:851-854
theorem refuted_insertPads_changes_exactly_nonunwinding_bodies :
    ¬ ∀ (cu : Prec) (p : Prog) (g : Nat),
      ((insertPads cu p).fn g).body ≠ (p.fn g).body ↔
        ((p.fn g).info.foreign = false ∧ p.selfMay cu g = false) := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:891-899
theorem refuted_insertPads_keeps_cleanup_pads :
    (¬ ∀ (cu : Prec) (p : Prog) (g f : Nat) (ds : List Nat),
      Stmt.call f (.cleanup ds) ∈ (p.fn g).body →
        Stmt.call f (.cleanup ds) ∈ ((insertPads cu p).fn g).body) ∧
    (¬ ∀ (cu : Prec) (p : Prog) (g : Nat) (ds : List Nat),
      Stmt.raise (.cleanup ds) ∈ (p.fn g).body →
        Stmt.raise (.cleanup ds) ∈ ((insertPads cu p).fn g).body) ∧
    ((insertPads stdCanUnwind progCleanupOverwritten).fn 0).body = [.call 2 .terminate] ∧
    ((insertPads stdCanUnwind progCleanupOverwritten).fn 1).body = [.raise .terminate] := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:862-865
theorem refuted_padStmt_call_terminate_exactly :
    ¬ ∀ (cu : Prec) (p : Prog) (g f : Nat) (act : Action),
      padStmt cu p g (.call f act) = .call f .terminate ↔
        (p.viewMay cu g f = true ∧ act.Stops = false) := by …
```

```lean
-- lean/ToyUnwindCap/Counterexamples.lean:873-875
theorem refuted_padStmt_raise_terminate_exactly :
    ¬ ∀ (cu : Prec) (p : Prog) (g : Nat) (act : Action),
      padStmt cu p g (.raise act) = .raise .terminate ↔ act.Stops = false := by …
```

```lean
-- lean/ToyUnwindCap/Results.lean:997-998
theorem runFn_unwind_selfMay (cu : Prec) (p : Prog) :
    ∀ n f, ∀ r ∈ runFn cu p n f, r.2 = .unwind → p.selfMay cu f = true := by …
```

## Boundaries

### Non-claims, by result

Read these first. Each list belongs to the result named in its heading.

#### R1. `noUB_of_enforced_of_foreignCovered_of_siteAgreement` (theorem)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- `Exec` collects the finite runs produced by the fuel-indexed evaluator `runFn`; diverging executions are not represented, and nothing is claimed about them.
- Function bodies are straight-line statement lists: there are no branches or loops inside a body (recursion through calls is allowed).
- Not modelled: indirect calls through function pointers (for which rustc's `fn_can_unwind` consults the ABI alone, layout.rs:1229-1232), inline assembly that may unwind, forced unwinding, panics during cleanup (a cleanup pad atomically records its drop events and cannot itself panic), asynchronous exceptions, and the third clause of the Reference's potentially-unwinding definition (separate runtime copies).
- `Enforced`, `SiteAgreement`, `GlueAgreement` and `PotentiallyUnwinding` quantify over every function index and every statement of its body, reachable or not; the natural behavioural weakenings that restrict them to reachable functions or reachable call sites are not established here.
- Out-of-range function indices `f ≥ p.fns.length` denote `FnDef.dummy` (an empty non-foreign Rust function in crate 0), and out-of-range crate indices denote `CrateCfg.dflt` (strategy and panic-in-drop `unwind`); no theorem here checks index bounds separately.
- `Enforced` constrains panic points when the panic handler is `unwind` and does not constrain them when it is `abort`, because under the `abort` handler `execBody` aborts at a panic point without unwinding and without consulting its action.
- In the toy semantics a stopping pad (`catchPad` or `terminate`) at a call site is executed even when the caller's crate classified the callee as non-unwinding (`onUnwind` with `assumed = true`); a lowering that emits no landing pad at such sites is not modelled.
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.
- The theorem holds for every precedence function `cu`; it does not say which precedence functions make the hypotheses true. `ForeignCovered stdCanUnwind` is a separate result (R2); `Enforced` and `SiteAgreement` are established for particular programs by R6 and R9.
- Each counterexample shows that there is a program satisfying the other hypotheses that has a `ub` run; it does not show that every program violating a hypothesis has a `ub` run.
- Absence of `ub` says nothing about destructor completeness or leak freedom.

#### R2. `foreignCovered_std_of_foreignHonest_of_foreignNotGlue` (theorem)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- `ForeignHonest` is an assumption about foreign code, not something the toy compiler checks; nothing is claimed about programs whose foreign code violates its declaration other than the counterexample.
- It does not establish `Enforced` or `SiteAgreement`, and hence not freedom from `ub`, for any program.
- Tier T0: the result restates, for the toy rule list, the behaviour that rustc's `fn_can_unwind` documents for foreign `"C-unwind"` items.

#### R3. `precForeignSound_iff` (characterization)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- `PrecForeignSound` concerns the foreign-code obligation; a precedence function satisfying it can still yield programs that violate `SiteAgreement` or `Enforced`.
- The characterization quantifies over the toy `FnInfo` values (ABI among `rust`, `c`, `cUnwind`); other ABIs are not modelled.

#### R4. `std_and_abiFirst_foreignSound_but_differ` (theorem)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- Both orders being foreign-sound does not make either one yield `ub`-free programs; `Enforced` and `SiteAgreement` are separate obligations.
- `PrecForeignSound` is a condition on the classification of honest, non-glue foreign imports (through `ForeignCovered`); satisfying it does not mean that an order makes Rust-defined exports of `abort` crates abort on foreign unwinds. Under `abiFirstCanUnwind`, `insertPads` inserts no terminate pad in the Rust-defined `extern "C-unwind"` function of `progAbortCUnwindExport` (an `abort` crate), and a foreign unwind leaves it, whereas under `stdCanUnwind` the same unwind aborts (`abiFirst_insertPads_lets_foreign_unwind_leave_abort_crate`); compare RFC 2945's table, quoted in REPORT.md, in which a foreign unwind reaching a `panic=abort` `"C-unwind"` boundary aborts.
- Every result of this package uses one precedence function `cu` for all crates; programs whose crates use different precedence functions are not modelled (whether mixing orders breaks `SiteAgreement` is not proved here).
- It does not rank the two orders (code size, optimisation) and does not claim that no other order is foreign-sound. "More conservative" refers to the stated implication between `false` verdicts and to nothing else.

#### R5. `abortAllCanUnwind_not_foreignSound`, `abortAll_progAbortImportPlain_ub` (counterexample)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- It refutes one specific rule order in the toy; it does not say any real compiler uses that order.
- Escape hatch: `ForeignCovered` is a condition on the foreign functions with `throws = true`; on a program with no foreign function that may unwind, `ForeignCovered abortAllCanUnwind p` holds (immediate from the definition of `ForeignCovered`), so the failure needs a foreign function that may unwind.
- The positive control shows that under `stdCanUnwind` the toy codegen turns the same program into one without `ub` runs; it does not show that every program is repaired this way.

#### R6. `insertPads_enforced`, `insertPads_body`, `padStmt_call`, `padStmt_raise`, `insertPads_foreignCovered`, `insertPads_siteAgreement`, `exec_insertPads_of_exec_of_ne_ub` (theorem)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- Function bodies are straight-line statement lists: there are no branches or loops inside a body (recursion through calls is allowed).
- `Enforced`, `SiteAgreement`, `GlueAgreement` and `PotentiallyUnwinding` quantify over every function index and every statement of its body, reachable or not; the natural behavioural weakenings that restrict them to reachable functions or reachable call sites are not established here.
- `insertPads` follows classifications, not behaviour: it inserts a terminate pad at a call to a callee that the caller's crate classifies as possibly unwinding even when that callee has no unwinding run (`insertPads_pad_without_unwinding_callee`), and at statements that no run reaches. Minimality of the inserted pads with respect to behaviour is not claimed; whether a pad is needed at a given site is the subject of R8 and R7.
- `insertPads` keeps every `catchPad` and `terminate` action and keeps `cleanup ds` actions except at the replaced sites of (iii) and (iv), where `ds` is discarded. It does not model running local destructors before aborting, as rustc's `AbortUnwindingCalls` pass does by keeping a cleanup block and turning its final resume into a terminate (see the corpus report cited under prior art). (vi) keeps every run that is not `ub`; the runs of `insertPads cu p` that are not runs of `p` are not characterized here.
- Under the `abort` handler `padStmt` leaves panic points unchanged; `execBody` aborts at a panic point there without consulting its action.
- Refutations of earlier candidate statements: the following candidate readings of this result are false, and each is refuted by a proved theorem (see Boundaries, "Disproved or dropped statements"): "`insertPads` changes the bodies of exactly the non-foreign functions classified as non-unwinding by their own crate" (`refuted_insertPads_changes_exactly_nonunwinding_bodies`; the correct characterization is `insertPads_body_ne_iff`); "`padStmt` gives a call site a terminate pad exactly when the caller's crate classifies the callee as possibly unwinding and the site has no stopping pad" (`refuted_padStmt_call_terminate_exactly`; correct: `padStmt_call`, `padStmt_call_ne_iff`); "`padStmt` gives a panic point a terminate pad exactly when it has no stopping pad" (`refuted_padStmt_raise_terminate_exactly`; correct: `padStmt_raise`, `padStmt_raise_ne_iff`); "the pass keeps existing cleanup pads" (`refuted_insertPads_keeps_cleanup_pads`).
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.

#### R7. `noUB_insertPads_of_foreignCovered_of_siteAgreement` (theorem)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- `Exec` collects the finite runs produced by the fuel-indexed evaluator `runFn`; diverging executions are not represented, and nothing is claimed about them.
- Function bodies are straight-line statement lists: there are no branches or loops inside a body (recursion through calls is allowed).
- Not modelled: indirect calls through function pointers (for which rustc's `fn_can_unwind` consults the ABI alone, layout.rs:1229-1232), inline assembly that may unwind, forced unwinding, panics during cleanup (a cleanup pad atomically records its drop events and cannot itself panic), asynchronous exceptions, and the third clause of the Reference's potentially-unwinding definition (separate runtime copies).
- `Enforced`, `SiteAgreement`, `GlueAgreement` and `PotentiallyUnwinding` quantify over every function index and every statement of its body, reachable or not; the natural behavioural weakenings that restrict them to reachable functions or reachable call sites are not established here.
- It establishes the absence of `ub` runs of `insertPads cu p`; it does not say that drop events are kept: at replaced sites a `cleanup ds` action becomes `terminate` and `ds` is lost (R6).
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.

#### R8. `ub_of_selfNonUnwinding_of_unguarded_head_call_of_callee_unwinds` (theorem)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- `Exec` collects the finite runs produced by the fuel-indexed evaluator `runFn`; diverging executions are not represented, and nothing is claimed about them.
- It requires an actual unwinding run of the callee; a callee merely classified as possibly unwinding but without such a run is not covered.
- Escape hatches, each witnessed by a proved counterexample: a stopping pad at the call (`ub_of_unguarded_call_fails_without_nonStopping`), a callee without an unwinding run (`ub_of_unguarded_call_fails_without_calleeUnwinds`), and an earlier statement of `g` that aborts before the call (`ub_of_unguarded_call_fails_without_callFirst`) each avoid `ub`. Under the `abort` handler a panic point aborts (definition of `execBody`), so a callee whose unwinding sources are all panic points has no unwinding run there.
- The call is the first statement of the body (`hbody`); a call preceded by other statements is not covered by this theorem, even when it is reached.
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.

#### R9. `noUB_std_of_linkOK_of_enforced_of_foreignHonest_of_foreignNotGlue_of_glueAgreement` (theorem)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- `Exec` collects the finite runs produced by the fuel-indexed evaluator `runFn`; diverging executions are not represented, and nothing is claimed about them.
- Function bodies are straight-line statement lists: there are no branches or loops inside a body (recursion through calls is allowed).
- Not modelled: indirect calls through function pointers (for which rustc's `fn_can_unwind` consults the ABI alone, layout.rs:1229-1232), inline assembly that may unwind, forced unwinding, panics during cleanup (a cleanup pad atomically records its drop events and cannot itself panic), asynchronous exceptions, and the third clause of the Reference's potentially-unwinding definition (separate runtime copies).
- `Enforced`, `SiteAgreement`, `GlueAgreement` and `PotentiallyUnwinding` quantify over every function index and every statement of its body, reachable or not; the natural behavioural weakenings that restrict them to reachable functions or reachable call sites are not established here.
- Out-of-range function indices `f ≥ p.fns.length` denote `FnDef.dummy` (an empty non-foreign Rust function in crate 0), and out-of-range crate indices denote `CrateCfg.dflt` (strategy and panic-in-drop `unwind`); no theorem here checks index bounds separately.
- `Enforced` constrains panic points when the panic handler is `unwind` and does not constrain them when it is `abort`, because under the `abort` handler `execBody` aborts at a panic point without unwinding and without consulting its action.
- `LinkOK` is modelled on two of the three clauses of the Reference's potentially-unwinding definition; the clause about calls into another artifact with a separate runtime copy is not modelled.
- Setting the panic handler to `abort` does not by itself make an artifact satisfy `LinkOK`: an artifact with the `abort` handler in which an `unwind`-strategy crate calls a `cUnwind` function is potentially unwinding (`potentiallyUnwinding_unwindCrateCallsCUnwind`).
- `noUB_std_fails_without_glueAgreement` shows that `LinkOK` does not imply `GlueAgreement` in the toy. When `LinkOK p` and `PotentiallyUnwinding p` hold, every crate setting `p.crateOf g` uses the `unwind` strategy (`crateOf_unwind_of_linkOK_of_potentiallyUnwinding`), so weakening the conclusion of `GlueAgreement` to "the glue instance's crate has strategy `abort` or panic-in-drop `abort`" would not change this hypothesis.
- Degenerate edge: a program with no crates satisfies `LinkOK` (`compRet_nil_and_linkOK_of_no_crates`); all its functions use `CrateCfg.dflt`.
- Whether and how any real toolchain checks `LinkOK` or `GlueAgreement` is not examined here (see the corpus report on panic-strategy linking cited under prior art).
- The panic handler is one artifact-wide setting; dynamically loaded code is not modelled.
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.

#### R10. `glueSiteSound_iff` (characterization)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- `Exec` collects the finite runs produced by the fuel-indexed evaluator `runFn`; diverging executions are not represented, and nothing is claimed about them.
- The program family is fixed: exactly one caller with exactly one call site, the `unwind` panic handler, a caller with the static facts `rustInfo`, and `stdCanUnwind`. Glue bodies may contain calls (to the caller, to the glue itself, or to out-of-range indices, which denote `FnDef.dummy`).
- In the toy semantics a stopping pad (`catchPad` or `terminate`) at a call site is executed even when the caller's crate classified the callee as non-unwinding (`onUnwind` with `assumed = true`); a lowering that emits no landing pad at such sites is not modelled. The `act.Stops = true` alternative depends on this choice.
- Escape hatch: the direction from `GlueSiteSound cc cg act` to the right-hand side uses the fixed `unwind` handler of `glueProg`. With the handler changed to `abort`, no finite run of any function of the family has outcome `ub`, for all settings, actions and glue bodies (`glueProg_abort_handler_noUB`), so the right-hand side does not characterize soundness of that variant.
- "The glue instance actually called" is the function in crate 1 of the family; how a real toolchain chooses or shares drop-glue instances across crates is not examined, and nothing is asserted about whether any toolchain enforces agreement.
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.

#### R11. `glueSiteSound_iff_panicInDrop` (characterization)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- Inherits the program-family restrictions and the stopping-pad modelling choice of `glueSiteSound_iff` (R10).
- A catch pad also suffices in the toy; the per-crate panic-in-drop form is not specific to terminate pads.
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.

#### R12. `compRet_eq_specRet_of_conforms` (theorem)

- Model–system relation: none proved. These are statements about the toy chain model; they neither establish nor refute the corresponding claims about any real compiler backend or unwinder. Backend capabilities are toy parameters; no capability or defect of any real backend is asserted.
- Values are toy natural numbers with one return value per frame; argument passing, multiple registers and layout are not modelled.
- `Conforms b A` equates `b.dec` and `A.dec` on every `Nat`, including values outside the range of `A.enc` (for `shiftCodec`, whose decoding uses truncated subtraction `w - 1`, both `0` and `1` decode to `0`). Neither the weakening to agreement on the range of `A.enc` nor the weakening to pairwise caller-callee inversion without one common ABI is examined.
- Degenerate edge: on the empty chain `compRet b0 [] v = specRet [] v = v` whatever `b0` (`compRet_nil_and_linkOK_of_no_crates`); for a non-empty chain the outermost frame's result is observed directly, without an encoding.

#### R13. `compUnwind_eq_specUnwind_iff_obligationsFull_of_noReachedNoneTerminate` (characterization)

- Model–system relation: none proved. These are statements about the toy chain model; they neither establish nor refute the corresponding claims about any real compiler backend or unwinder. Backend capabilities are toy parameters; no capability or defect of any real backend is asserted.
- A `pads = none` function or frame is assumed to be unwindable: an unwind that reaches it without a landing pad passes through to its caller (`Stmt.unpadded`, `UFrame.effAct`). This models a backend that emits frame-unwind information but no landing pads. Code that cannot be unwound through at all (compare the Reference's `src/panic.md:124-128` on code compiled with `-fno-exceptions`) is not modelled, and nothing here applies to it.
- A chain is the stack at the moment one unwind starts; the model does not derive chains from programs, and the relation to the program model is informal (not proved here).
- Frames without obligations may be compiled with `pads = none` and unwound through without any difference; the result does not require every unwound frame to be `pads = full`.
- Events and catches are tagged with frame positions; a model whose observations cannot distinguish frames is not covered.
- `NoReachedNoneTerminate` constrains every frame reached by the specified unwind; whether it can be weakened further (for example to reached frames whose skipped abort is not repeated by a later frame) is not examined.
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.

#### R18. `compUnwind_eq_specUnwind_of_obligationsFull` (theorem)

- Model–system relation: none proved. These are statements about the toy chain model; they neither establish nor refute the corresponding claims about any real compiler backend or unwinder. Backend capabilities are toy parameters; no capability or defect of any real backend is asserted.
- A `pads = none` function or frame is assumed to be unwindable: an unwind that reaches it without a landing pad passes through to its caller (`Stmt.unpadded`, `UFrame.effAct`). This models a backend that emits frame-unwind information but no landing pads. Code that cannot be unwound through at all (compare the Reference's `src/panic.md:124-128` on code compiled with `-fno-exceptions`) is not modelled, and nothing here applies to it.
- `ObligationsFull c` is sufficient, and is not necessary for `compUnwind c = specUnwind c`: there is a chain, `[⟨none, terminate⟩, ⟨full, terminate⟩]`, whose compiled and specified unwinds are equal although `ObligationsFull` fails (`compUnwind_iff_fails_without_noReachedNoneTerminate`); under `NoReachedNoneTerminate c` the converse holds (R13).
- A chain is the stack at the moment one unwind starts; the model does not derive chains from programs (not proved here).
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.

#### R14. `robust_iff_shielded` (characterization)

- Model–system relation: none proved. These are statements about the toy chain model; they neither establish nor refute the corresponding claims about any real compiler backend or unwinder. Backend capabilities are toy parameters; no capability or defect of any real backend is asserted.
- A `pads = none` function or frame is assumed to be unwindable: an unwind that reaches it without a landing pad passes through to its caller (`Stmt.unpadded`, `UFrame.effAct`). This models a backend that emits frame-unwind information but no landing pads. Code that cannot be unwound through at all (compare the Reference's `src/panic.md:124-128` on code compiled with `-fno-exceptions`) is not modelled, and nothing here applies to it.
- Robustness quantifies over the actions of `pads = none` frames; capabilities and the actions of `pads = full` frames are held fixed.
- `Shielded` holds for a chain without `pads = none` frames even if no frame stops the unwind (for example `[⟨full, none⟩]`).
- It does not say that a `pads = none` frame is classified as non-unwinding in any program; the program-level counterparts are R16 and R17.
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.

#### R15. `robust_of_terminateShielded` (theorem)

- Model–system relation: none proved. These are statements about the toy chain model; they neither establish nor refute the corresponding claims about any real compiler backend or unwinder. Backend capabilities are toy parameters; no capability or defect of any real backend is asserted.
- A `pads = none` function or frame is assumed to be unwindable: an unwind that reaches it without a landing pad passes through to its caller (`Stmt.unpadded`, `UFrame.effAct`). This models a backend that emits frame-unwind information but no landing pads. Code that cannot be unwound through at all (compare the Reference's `src/panic.md:124-128` on code compiled with `-fno-exceptions`) is not modelled, and nothing here applies to it.
- Abort shielding is sufficient, not necessary: there is a chain shielded by a catch pad that is robust but not `TerminateShielded` (`shielded_not_terminateShielded`).
- `TerminateShielded` holds for a chain without `pads = none` frames even if it has no terminate pad (for example `[⟨full, catchPad⟩]`).
- In the toy semantics `catchPad` stops every unwind, including unwinds started by foreign code and unwinds inside `abort`-strategy crates. In documented Rust, catching a foreign unwind with `std::panic::catch_unwind` either aborts or returns `Err`, and which one is unspecified (Reference `src/panic.md:130-134`); and RFC 1513 (lines 108-111) describes the `abort` strategy as using `call` instead of `invoke` everywhere, so code compiled with that strategy has no landing pad at which a catch could take effect (derived (modeling bridge)). The toy results about `catchPad` neither establish nor refute the corresponding claims about `std::panic::catch_unwind`.

#### R16. `withPads_exec_iff_of_padsNone_nonunwinding_of_enforcedAt_of_siteAgreementAt` (theorem)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- `Exec` collects the finite runs produced by the fuel-indexed evaluator `runFn`; diverging executions are not represented, and nothing is claimed about them.
- Function bodies are straight-line statement lists: there are no branches or loops inside a body (recursion through calls is allowed).
- A `pads = none` function or frame is assumed to be unwindable: an unwind that reaches it without a landing pad passes through to its caller (`Stmt.unpadded`, `UFrame.effAct`). This models a backend that emits frame-unwind information but no landing pads. Code that cannot be unwound through at all (compare the Reference's `src/panic.md:124-128` on code compiled with `-fno-exceptions`) is not modelled, and nothing here applies to it.
- Out-of-range function indices `f ≥ p.fns.length` denote `FnDef.dummy` (an empty non-foreign Rust function in crate 0), and out-of-range crate indices denote `CrateCfg.dflt` (strategy and panic-in-drop `unwind`); no theorem here checks index bounds separately.
- `henf` and `hsa` constrain the function indices `g` with `pads g = none`; `pads = full` functions need not satisfy `EnforcedAt` or `SiteAgreementAt` (`withPads_hypotheses_hold_progPadsFullUnenforced`).
- Equality of runs does not by itself exclude `ub`; with `Enforced cu (p.withPads pads)`, `ForeignCovered cu p` and `SiteAgreement cu (p.withPads pads)` program-wide, R1 applied to `p.withPads pads` does.
- `hnone` excludes `pads = none` functions classified as possibly unwinding even when they have no landing-pad obligation; R17 covers such functions (`withPads_local_hypotheses_hold_progPadsPlainUnwindThrough`).
- Under the `unwind` handler a `pads = none` function that satisfies the hypotheses has no panic points in the compiled program, and every callee it calls is classified as non-unwinding by the callee's own crate; abort enforcement then sits in `pads = full` functions below it.

#### R17. `withPads_exec_iff_of_padsNone_obligationFreeRaises_of_obligationCalleesNonUnwinding` (theorem)

- Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc, LLVM, the Rust Reference's rules or any Rust toolchain.
- `Exec` collects the finite runs produced by the fuel-indexed evaluator `runFn`; diverging executions are not represented, and nothing is claimed about them.
- Function bodies are straight-line statement lists: there are no branches or loops inside a body (recursion through calls is allowed).
- A `pads = none` function or frame is assumed to be unwindable: an unwind that reaches it without a landing pad passes through to its caller (`Stmt.unpadded`, `UFrame.effAct`). This models a backend that emits frame-unwind information but no landing pads. Code that cannot be unwound through at all (compare the Reference's `src/panic.md:124-128` on code compiled with `-fno-exceptions`) is not modelled, and nothing here applies to it.
- Out-of-range function indices `f ≥ p.fns.length` denote `FnDef.dummy` (an empty non-foreign Rust function in crate 0), and out-of-range crate indices denote `CrateCfg.dflt` (strategy and panic-in-drop `unwind`); no theorem here checks index bounds separately.
- The hypotheses quantify over every `pads = none` function index below `p.fns.length` and every statement of its body, reachable or not; a weakening to reachable statements is not established.
- The two conditions are sufficient for equality of runs; they are not claimed to characterize it. Each is tight in the stated witness class, and no weaker sufficient condition is examined.
- `hcall` concerns the callee's own classification (`selfMay`), not behaviour: a callee classified as non-unwinding by its own crate never unwinds out of itself in the toy (`runFn_unwind_selfMay`), possibly producing `ub` instead; equality of runs includes such `ub` runs.

### Escape hatches

For the results that show a failure, and for the sufficient conditions whose converse fails, the nearby settings in which the failure goes away, as far as they are proved here:

* R5 (`abortAllCanUnwind` is not foreign-sound; `progAbortImportPlain` has a `ub` run under it): under `stdCanUnwind` the toy pass turns the same program into `progAbortImportPadded`, which has no `ub` run from function 0 (positive control `std_progAbortImportPlain_padded_noUB`). The failure needs a foreign function that may unwind: `ForeignCovered` is a condition on the foreign functions with `throws = true`, so on a program with no foreign function that may unwind `ForeignCovered abortAllCanUnwind p` holds (immediate from the definition of `ForeignCovered`; no separate theorem).
* R8 (a missing stopping pad at the head call of a non-unwinding function gives `ub` once the callee unwinds): each of the following avoids `ub` on a proved instance: a stopping pad at the call (`ub_of_unguarded_call_fails_without_nonStopping`), a callee without an unwinding run (`ub_of_unguarded_call_fails_without_calleeUnwinds`), an earlier statement that aborts before the call (`ub_of_unguarded_call_fails_without_callFirst`), and a function classified as possibly unwinding by its own crate (`ub_of_unguarded_call_fails_without_selfNonUnwinding`).
* R10 and R11 (unsound drop-glue sites under the `unwind` handler): with the handler of `glueProg` changed to `abort`, no finite run of any function of the family has outcome `ub`, for all settings, actions and glue bodies (`glueProg_abort_handler_noUB`).
* R13 and R18 (`ObligationsFull` is sufficient for `compUnwind c = specUnwind c`, R18; necessary under `NoReachedNoneTerminate c`, R13): without `NoReachedNoneTerminate`, there is a chain, `[⟨none, terminate⟩, ⟨full, terminate⟩]`, whose compiled and specified unwinds are equal although `ObligationsFull` fails (`compUnwind_iff_fails_without_noReachedNoneTerminate`).
* R15 (`TerminateShielded` is sufficient for robustness): it is not necessary; there is a chain, `[⟨full, catchPad⟩, ⟨none, none⟩]`, that is robust and `Shielded` but not `TerminateShielded` (`shielded_not_terminateShielded`); the exact robust condition is `Shielded` (R14).

### Hypotheses with unknown tightness

None: every hypothesis of every result is `tight`, and its ledger names a kernel-checked counterexample in which all other hypotheses hold and the conclusion fails, with the class of the witness.

### Disproved or dropped statements

No result of this package is disproved or dropped: every result listed in the Summary is kernel-checked with the statement quoted in its card.

Refutations of earlier candidate statements. Four candidate statements of the toy pass's syntactic action, considered for R6 and replaced by the exact statements `insertPads_body`, `padStmt_call` and `padStmt_raise`, are false; each refutation is a kernel-checked theorem quoted under "Auxiliary declarations cited by name":

* "`insertPads` changes the bodies of exactly the non-foreign functions classified as non-unwinding by their own crate" — refuted by `refuted_insertPads_changes_exactly_nonunwinding_bodies` (function 0 of `progAbortCallsUnwind` is non-foreign and classified as non-unwinding by its own crate, and its body is unchanged); the correct characterization is `insertPads_body_ne_iff`.
* "`padStmt` gives a call site a terminate pad exactly when the caller's crate classifies the callee as possibly unwinding and the site has no stopping pad" — refuted by `refuted_padStmt_call_terminate_exactly` (a site that already has a `terminate` action keeps it); correct: `padStmt_call` and `padStmt_call_ne_iff`.
* "`padStmt` gives a panic point a terminate pad exactly when it has no stopping pad" — refuted by `refuted_padStmt_raise_terminate_exactly` (a panic point that already has a `terminate` action keeps it); correct: `padStmt_raise` and `padStmt_raise_ne_iff`.
* "The pass keeps existing cleanup pads" — refuted by `refuted_insertPads_keeps_cleanup_pads` (on the program named in that theorem, a call site and a panic point with action `cleanup [7]` inside non-unwinding functions both become `terminate`).

### Not examined

* Behavioural weakenings of `Enforced`, `SiteAgreement`, `GlueAgreement` and `PotentiallyUnwinding` (and of R17's hypotheses) that restrict them to reachable functions or reachable statements.
* Whether `NoReachedNoneTerminate` (R13) can be weakened further; weakenings of R12's `Conforms` to agreement on the range of the encoding or to pairwise caller-callee inversion without one common ABI.
* Crates that use different precedence functions in one program; ABIs other than `rust`, `c` and `cUnwind`; indirect calls; branches and loops inside bodies; diverging executions.
* A derivation of call chains from programs (the chain model and the program model are related only informally).
* How a real toolchain chooses or shares drop-glue instances across crates, and whether and how any toolchain checks `LinkOK` or `GlueAgreement`.
* Any execution or measurement of rustc, LLVM or any other compiler or backend.

## Evidence

### Kernel-check record

Toolchain: `leanprover/lean4` `v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean without Mathlib. Basis of every theorem below: execution (Lean kernel check), observed on 2026-11-22 (fresh build without artifact cache). The table lists every declaration that a card names (results, witnesses, counterexamples, positive control and the auxiliary lemmas and definitions cited by name), with the axioms it depends on (`#print axioms`, computed with Lean's `collectAxioms`), the SHA-256 of its statement (the Lean `repr` of its type) and the SHA-256 of its definition closure (types and values of every package-local constant reachable from the statement; theorem bodies excluded), with the number of constants in the closure. For a definition, the statement is its type, so its own body is fixed by the closure hashes of the results whose statements use it rather than by its own row; for the declarations whose type is `Type` (the inductive types and structures, and the abbreviation `Prec`) the recorded closure is empty (size 0), and their definitions, including the constructors of inductive types, are likewise fixed by the closure hashes of the declarations that use them. The same data are in `audit/axioms.json` (all 795 declarations of the library) and `audit/statements.json`.

| declaration | axioms | statement SHA-256 | definition-closure SHA-256 (size) |
| --- | --- | --- | --- |
| `Toy.UnwindCap.AbiCodec` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.Action` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.Action.obligation` | none | `95818384306bfdeae09a1373b10119b883bb7902c6093ed2b0ba15d2817c7c93` | `33e16edca07f6e979cef165023bc6ebe8a1ce938a8761e1998be153b8aaf74c9` (5) |
| `Toy.UnwindCap.Conforms` | none | `be8267da257d0509b6839e15a3aef7664bf802de47fc385346c2c4627f54b75e` | `7c985c267d17a0800f2c67d505a46660917492240007d4088480394808883022` (2) |
| `Toy.UnwindCap.CrateCfg` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.CrateCfg.dflt` | none | `d5c7d8060346dbec3e3f42f12544a4ebfec60bfbf150b7cb51bf3c5d1c9ac150` | `7eabc0376e8dccbcc01e9eb245f76095c9f094c5ab62af7d17e42215a2bd48f4` (5) |
| `Toy.UnwindCap.Enforced` | `propext` | `1e3eb971b5112f324c2f46e2a0247924f5320815bde1401c9a2deeac599f316b` | `a55a9ae2a60da899cf814e3594bf0a1ee770df2a13bfd176bd3fb118d9c05090` (24) |
| `Toy.UnwindCap.EnforcedAt` | `propext` | `0d1b797509924c486a218b2b18c88d86dce94eb547d870bd3a270f3110492e8a` | `a55a9ae2a60da899cf814e3594bf0a1ee770df2a13bfd176bd3fb118d9c05090` (24) |
| `Toy.UnwindCap.Event` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.Exec` | `propext` | `e2524488a0db50c2026dd80de5103a3728030c560ba8da1cf69017824509d4ff` | `18be93db74f8714dbe715e9aa1c56c6c79f3043a40cc1d5d583ba6ce78fa8005` (32) |
| `Toy.UnwindCap.FnDef.dummy` | none | `190780de60eef5e600d858ad962d4eb74fc0d2ab566495513903131b32829009` | `9aeadd444606d510e788b9ef712fefe704145729ba5d4bf1b4e0b59d96bab601` (16) |
| `Toy.UnwindCap.FnInfo` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.ForeignCovered` | `propext` | `1e3eb971b5112f324c2f46e2a0247924f5320815bde1401c9a2deeac599f316b` | `a55a9ae2a60da899cf814e3594bf0a1ee770df2a13bfd176bd3fb118d9c05090` (24) |
| `Toy.UnwindCap.ForeignHonest` | `propext` | `0c0d5bd5f53ceb8bdb1b2112e2023cd4e74dfb8caece0d1fb7f98ab3e86c01f4` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.ForeignNotGlue` | `propext` | `0c0d5bd5f53ceb8bdb1b2112e2023cd4e74dfb8caece0d1fb7f98ab3e86c01f4` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.GlueAgreement` | `propext` | `0c0d5bd5f53ceb8bdb1b2112e2023cd4e74dfb8caece0d1fb7f98ab3e86c01f4` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.GlueSiteSound` | `propext` | `5d33e5c59b1751ede7bfcc0014f09fc5bf7f2018ccb1a27d199690c77b7648c8` | `48e46d7970eda2d7f7fe7dd6452d9753f8fad523e6931aadb812895f99defa6b` (10) |
| `Toy.UnwindCap.LinkOK` | `propext` | `0c0d5bd5f53ceb8bdb1b2112e2023cd4e74dfb8caece0d1fb7f98ab3e86c01f4` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.NoReachedNoneTerminate` | `propext` | `285d4d0a3ba5e74a675c6cc6a516a1f43c695529b901eca28c6242bc997faf1a` | `9e0d5cf985e64b87926f5ecbaaf5819f79bef525537dc33459dd00b35e93be2c` (10) |
| `Toy.UnwindCap.ObligationsFull` | `propext` | `285d4d0a3ba5e74a675c6cc6a516a1f43c695529b901eca28c6242bc997faf1a` | `9e0d5cf985e64b87926f5ecbaaf5819f79bef525537dc33459dd00b35e93be2c` (10) |
| `Toy.UnwindCap.Pads` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.PotentiallyUnwinding` | `propext` | `0c0d5bd5f53ceb8bdb1b2112e2023cd4e74dfb8caece0d1fb7f98ab3e86c01f4` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.Prec` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.PrecForeignSound` | `propext` | `5c834a125110d894aecc5cd82b7fd75efb90dd5e4387e56dca0186a239dd39cd` | `868bd8a5fe764b4539c05664d594d21901b21ed3f8d51f26308ea4e7dd5d08a3` (12) |
| `Toy.UnwindCap.Prog` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.Prog.withPads` | none | `a814e3092c337cc31fa9186b426f3e1195e24e75e0e928669d1ea64983529da8` | `7b830034b80ecddcb0d3512c831949e9a022bf708f12ebd01e0a1d209bf37d8f` (26) |
| `Toy.UnwindCap.RetFrame` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.SameShape` | `propext` | `7fc04092e85a1e3f167eb0b80b2e72589ddbe08b8531a0757e4d21af7e09fb1c` | `9e0d5cf985e64b87926f5ecbaaf5819f79bef525537dc33459dd00b35e93be2c` (10) |
| `Toy.UnwindCap.Shielded` | `propext` | `285d4d0a3ba5e74a675c6cc6a516a1f43c695529b901eca28c6242bc997faf1a` | `9e0d5cf985e64b87926f5ecbaaf5819f79bef525537dc33459dd00b35e93be2c` (10) |
| `Toy.UnwindCap.SiteAgreement` | `propext` | `1e3eb971b5112f324c2f46e2a0247924f5320815bde1401c9a2deeac599f316b` | `a55a9ae2a60da899cf814e3594bf0a1ee770df2a13bfd176bd3fb118d9c05090` (24) |
| `Toy.UnwindCap.SiteAgreementAt` | `propext` | `0d1b797509924c486a218b2b18c88d86dce94eb547d870bd3a270f3110492e8a` | `a55a9ae2a60da899cf814e3594bf0a1ee770df2a13bfd176bd3fb118d9c05090` (24) |
| `Toy.UnwindCap.Stmt` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.Stmt.unpadded` | none | `a791c7de8e68fe7195d00ca629c67e5f3ddb282bfefcbdecfc6ff9513a5f5f33` | `08c57f9783556aac42c3ae360d96833f2da6ef79a39fb1c09ed9811a35a31259` (8) |
| `Toy.UnwindCap.TerminateShielded` | none | `285d4d0a3ba5e74a675c6cc6a516a1f43c695529b901eca28c6242bc997faf1a` | `9e0d5cf985e64b87926f5ecbaaf5819f79bef525537dc33459dd00b35e93be2c` (10) |
| `Toy.UnwindCap.UFrame` | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Toy.UnwindCap.UFrame.effAct` | none | `ea7436af120d218f7f30676e0bfc6d312d7baa42366fa59abd4096ef5cb8e82c` | `9e0d5cf985e64b87926f5ecbaaf5819f79bef525537dc33459dd00b35e93be2c` (10) |
| `Toy.UnwindCap.abiFirstCanUnwind` | none | `9434f74e5f6883c8f7128e90100acdf37a316bbc27d39f935e0d1ee1358f4161` | `868bd8a5fe764b4539c05664d594d21901b21ed3f8d51f26308ea4e7dd5d08a3` (12) |
| `Toy.UnwindCap.abiFirst_insertPads_lets_foreign_unwind_leave_abort_crate` | `propext` | `9cee7c31743cf17911a149719f1b1ede9f90191f19fcf096e2f59e31dd1b04f5` | `a11ea4d3c6ba5cecfeb4ab8f8b19c9f39cc5d771bbad60dde30126e51fea399a` (107) |
| `Toy.UnwindCap.abortAllCanUnwind` | none | `9434f74e5f6883c8f7128e90100acdf37a316bbc27d39f935e0d1ee1358f4161` | `868bd8a5fe764b4539c05664d594d21901b21ed3f8d51f26308ea4e7dd5d08a3` (12) |
| `Toy.UnwindCap.abortAllCanUnwind_not_foreignSound` | `propext` | `d10382b6354aa064b0ed1fd1b86f41dc22dcd3a9a01a1a8f51309cec1e50c1b1` | `6e8528e0ff86dd941b45d15293b8d2a5932e58cc95cc34d27a341ee6dc4a34ba` (63) |
| `Toy.UnwindCap.abortAll_progAbortImportPlain_ub` | `Quot.sound`, `propext` | `46a22b360d8d75babce30513a5e1a5fc111162cafbf2616b258203ba5dddb27c` | `727eb1aa60f807fd264af9aff2cea6c543988e19be04be971b7ee60a3b1541d1` (109) |
| `Toy.UnwindCap.abortCfg` | none | `d5c7d8060346dbec3e3f42f12544a4ebfec60bfbf150b7cb51bf3c5d1c9ac150` | `7eabc0376e8dccbcc01e9eb245f76095c9f094c5ab62af7d17e42215a2bd48f4` (5) |
| `Toy.UnwindCap.boundary` | `propext` | `a822c9a72bdc43963cd9b27d75b7d4abe4852873dea4002dc2214d2f6c021dd1` | `59ef1c9fb75021e5a7b5eb09215cdc9b40e2b6c9af64c8a463f4ae1ea838808e` (33) |
| `Toy.UnwindCap.compRet` | none | `95f9ebef2fac3b9818fbf9884f5c590301513ff0d430d0dcb161005f5cadcc97` | `f69d930f66cd3afcb328d265d8b78876823b02d50db22a4f3969bdc579b13a40` (4) |
| `Toy.UnwindCap.compRet_eq_specRet_of_conforms` | none | `b8dad01298e9e4e3400937fd7865fa39bd092fbc72f11ee4d03452d50661f113` | `564fe2b240dcf423f29a0619b11976b7c3faa0300f87d55578123deac80da124` (16) |
| `Toy.UnwindCap.compRet_fails_without_calleeConforms` | `propext` | `9b331a55d0caeae2f3a7385848fa00ff2a685b930b0f03ada182fee32bd31b9a` | `65fd912b8e42ac25529e3308f84013ef0a20893c7fe8a9d3502d7cc91ff93abb` (18) |
| `Toy.UnwindCap.compRet_fails_without_framesConform` | `propext` | `b437f19d49ed5f3c842f2bb2e64a47ac9dd6d292918f53f0da09e4099f4e0a25` | `65fd912b8e42ac25529e3308f84013ef0a20893c7fe8a9d3502d7cc91ff93abb` (18) |
| `Toy.UnwindCap.compRet_fails_without_lawful` | `propext` | `a067bfa1e499562cba55f0f14d70b6572d9195aa692bb0667369caf4f9a51fbd` | `18c374e13acb6f0374c6d7f4300a5cef8aec72e59065b12597d0d34b43b851d4` (16) |
| `Toy.UnwindCap.compRet_hypotheses_hold` | `propext` | `711140c57f96cd9d4e44d2041d69328b7041aeeb0385917c158b21b101c6e876` | `20db5a5fa1e168f8d9856d1bc31ccabbe3cfd227e1893fb6f34446ed6ec2479b` (14) |
| `Toy.UnwindCap.compRet_nil_and_linkOK_of_no_crates` | `propext` | `c17c17872a34f300422c2a1aedb547ffb73ff9cb745a3bb92be6157c9f7d14ab` | `fe460d4faa98c6a8ebc99aa0731efc413df6b0ff75f3b74b0e0c75a3f56a3aa0` (52) |
| `Toy.UnwindCap.compUnwind` | none | `197cb8cf7afc353b11100c892de8494fea584a3ed432916a9fea751ea3ddc878` | `a8cf194289fa2333a686baab73c4a6261e7f7865f1c1b0c8caa05ca0d7be6508` (17) |
| `Toy.UnwindCap.compUnwind_eq_specUnwind_iff_obligationsFull_of_noReachedNoneTerminate` | `Quot.sound`, `propext` | `2b5a18d0a5d9ea223857ff9cafd53ff9838a37b68b6f1ad9aeb7caf9f06af489` | `d73b248e3a31f0bad190f4546e570cf81daf911ada00ead73658fac30abe010a` (42) |
| `Toy.UnwindCap.compUnwind_eq_specUnwind_of_obligationsFull` | `propext` | `0265ada621c92e2f00db6dbc1feb76d55aac7730faa3a9659213f1f812e07d26` | `44cc9486cc4b3622b13b29933dd25daf91afd5002218a0394cdc333f9f175e2c` (40) |
| `Toy.UnwindCap.compUnwind_eq_specUnwind_of_obligationsFull_hypotheses_hold` | `propext` | `72b39d386b29615023857542e2d7e88b920198fe430ec7b0583f9a4058d465c8` | `67aee655c1b182a14201bdd44bcdf55a5e17714f040793bada1bd3a80c6bc21e` (23) |
| `Toy.UnwindCap.compUnwind_iff_fails_without_noReachedNoneTerminate` | `propext` | `135a60cb6508b07c5b5b2aa32bb4fc3dc7baf00bc2bcb564cc95dbdaff9caacf` | `44cc9486cc4b3622b13b29933dd25daf91afd5002218a0394cdc333f9f175e2c` (40) |
| `Toy.UnwindCap.compUnwind_iff_hypotheses_hold` | `propext` | `4b1e6d3cd85458ed6085af8848a7ce65e22b79fdce1df40b8d0117148db7d0ec` | `2bf157dff7ffe335565d3eb3d88e147d7a7d04ba7495c96ae70359c2a5980ecb` (38) |
| `Toy.UnwindCap.compUnwind_of_obligationsFull_fails_without_obligationsFull` | `propext` | `53ae153197e96965bf10cde178cfdd354ef002dab266bc8c061b17d57a4a0eef` | `44cc9486cc4b3622b13b29933dd25daf91afd5002218a0394cdc333f9f175e2c` (40) |
| `Toy.UnwindCap.crateOf_unwind_of_linkOK_of_potentiallyUnwinding` | `propext` | `629a30dc6ab95ce22cf534a64ce10ad59088ebc6a16948cf182a06cb6e7482c4` | `2d1ed81df711b98734ad9819b1aa6a450abac09efc6076063a504a0e0f42c0f2` (38) |
| `Toy.UnwindCap.execBody` | `propext` | `2e7ee1b7dafbfff95af74425539412c966a183c5d90e817f2819f604f32fb73f` | `59ef1c9fb75021e5a7b5eb09215cdc9b40e2b6c9af64c8a463f4ae1ea838808e` (33) |
| `Toy.UnwindCap.exec_insertPads_fails_without_ne_ub` | `Quot.sound`, `propext` | `5066db3e874391e43703c6414c499c76128f05247e8b3384e9a71cf2c5ba58b1` | `23f4c82ef546e278aa705e59893b9f99c8e1cbb199385c59906f6b23ec38728e` (105) |
| `Toy.UnwindCap.exec_insertPads_of_exec_of_ne_ub` | `Classical.choice`, `Quot.sound`, `propext` | `9a6993311fe3a5ead6a1e2a0ff52acb62eb44804a597f17982ef2fd089ee7b4b` | `bc4bb49f8d1da77639e8cc18d38842f5ea468034994c85055ffb2dc2b345c001` (81) |
| `Toy.UnwindCap.foreignCUnwind` | none | `64de140e04314756adbeb207189b920ff9afb7db02323b16744914e77b1cd436` | `9ce71d3cdfb00d54a22feaa6ac7918e59c693a8a513d75b562be400720028495` (6) |
| `Toy.UnwindCap.foreignCovered_std_fails_without_foreignHonest` | `Quot.sound`, `propext` | `6f239a576b1e45ceebc6fe62ff07a07ee5573b7b411c94660b790faaa1d12cac` | `ef170496ef430de01d825dbc7225b95fb6ab58b3c4a3d45f7efe82c14a6e1842` (64) |
| `Toy.UnwindCap.foreignCovered_std_fails_without_foreignNotGlue` | `Quot.sound`, `propext` | `b8edbeef2fdc66650dcf76f5b1e012c1fe9530d5e73b09e2644dcf7264092105` | `e99053351b0b4e451d81d41b0ac2343e882f62cd8695d58fe6c5e0c89a06f575` (63) |
| `Toy.UnwindCap.foreignCovered_std_hypotheses_hold_progAbortImportPadded` | `Quot.sound`, `propext` | `300f62a0861c20aa181e957a714cc4dcd0c369c21c327af4e8547e465a1aa9fa` | `f6146343d891782a49a342777872d6bdf42fd9d7a5a82968311c674464477d93` (38) |
| `Toy.UnwindCap.foreignCovered_std_of_foreignHonest_of_foreignNotGlue` | `propext` | `4cd5e19dd7381c39ed85c09c354a7f8e4943701fb351a59060d1bc3be2278d62` | `7f712601c3bf9e8b61282dcb3fac06c6f8c5c487bcc2830f59a37ae391466342` (62) |
| `Toy.UnwindCap.glueInfo` | none | `64de140e04314756adbeb207189b920ff9afb7db02323b16744914e77b1cd436` | `9ce71d3cdfb00d54a22feaa6ac7918e59c693a8a513d75b562be400720028495` (6) |
| `Toy.UnwindCap.glueProg` | none | `df2addbe44059a65f9a75a11ac8b521fc3a406c015c693a550acf40fbd1443a8` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.glueProg_abort_handler_noUB` | `Quot.sound`, `propext` | `55b6d01ca22b97245dc1425b75eeb63d25749dc81d0df62eada77d0e776a3614` | `4128e59adc1f5dd44169b1cf42a1e1682e70588f9091e9dade95fef884f35f6b` (96) |
| `Toy.UnwindCap.glueSiteSound_examples` | `Quot.sound`, `propext` | `367aff23ed32fdf333d5b3610e4a1398e4b83ae75d88fe40209a808516a30234` | `a1132fe8bbf34080dce42845d4bc5b60efa5a3bf04cc403bc598f764a31d101d` (105) |
| `Toy.UnwindCap.glueSiteSound_iff` | `Quot.sound`, `propext` | `2c1aae0b1f48468d2d4fbb2de75bd44872680295b946e2158f12e9cd5476a810` | `aeae024f88c83f9f2681d178676320f9043efed979adfb8171d58fd624c4397d` (103) |
| `Toy.UnwindCap.glueSiteSound_iff_instances` | `propext` | `b4b54e5c57844582c75f96e3d7a6d547193c421c8ca1fc1ad8080af51a4ed649` | `2a16b34eb8d794fda70d390533d2ee9ad94dcaa831fe5bd25e835d0e705f4b4c` (51) |
| `Toy.UnwindCap.glueSiteSound_iff_panicInDrop` | `Quot.sound`, `propext` | `f23db99bb07462cc130be340a54d71b07c5b49db3b8832c56b8c1e6427ca46b2` | `aeae024f88c83f9f2681d178676320f9043efed979adfb8171d58fd624c4397d` (103) |
| `Toy.UnwindCap.glueSiteSound_iff_panicInDrop_fails_without_glueCrateUnwind` | `Quot.sound`, `propext` | `09aa9a00c7496d473fc4b8bc6705419a8f97fc32482fd2ba339fdeb0ac7885ac` | `3a2b18244cac914b3f2064a3e5526e3d61417f82ab2dbe98c44e2f3311292934` (105) |
| `Toy.UnwindCap.glueSiteSound_iff_panicInDrop_fails_without_view` | `Quot.sound`, `propext` | `f92e1db6302a65bb8af3b4909a604407add3111f51575cf6d5661b2933d1f656` | `0210b8bae346a2b18868c5d41af29901874198f5d51d2a13861baed40a4cf19a` (104) |
| `Toy.UnwindCap.glueSiteSound_iff_panicInDrop_hypotheses_hold` | none | `e7505ba6f3f3f6f948833852f573912e08513bb13a7b04963a054f45332b374b` | `b776641ef028b31a56329dbf04eba723bc7b214d401e75b00e90fb947aa17690` (9) |
| `Toy.UnwindCap.idCodec` | none | `4a39e80f5ca90e32507fed07f069ad0ef3f55fd275a5f04bf15bc38e540011c9` | `7c985c267d17a0800f2c67d505a46660917492240007d4088480394808883022` (2) |
| `Toy.UnwindCap.insertPads` | `propext` | `9a2b22f8af6b03160360ad934b563df6b7b89ad76db2438f34312015569a8a2e` | `a55a9ae2a60da899cf814e3594bf0a1ee770df2a13bfd176bd3fb118d9c05090` (24) |
| `Toy.UnwindCap.insertPads_body` | `Classical.choice`, `Quot.sound`, `propext` | `a0fd1f16d25328fdde9ed2166241a33d69f9bf8e5a632d5f2793c5ddd070dd4a` | `1e5a95d1395d6ad935ae48ecbf1096e9d1e84f635dea20f45a7d2c2e99e6cc47` (54) |
| `Toy.UnwindCap.insertPads_body_ne_iff` | `Classical.choice`, `Quot.sound`, `propext` | `0d672c6016d82d801d5b2eb0a6016e02c08481b780b6ee807821e10771ffff87` | `1e5a95d1395d6ad935ae48ecbf1096e9d1e84f635dea20f45a7d2c2e99e6cc47` (54) |
| `Toy.UnwindCap.insertPads_enforced` | `Classical.choice`, `Quot.sound`, `propext` | `9ea24206d2ddb3ad1832a8b9941a8489cbd2e0b61dfc299ac5f4eaa8445f5710` | `3552be10e7c0f9e66b74a5321c723b7003550c98644ce20b1848ccbae253e02a` (56) |
| `Toy.UnwindCap.insertPads_foreignCovered` | `Classical.choice`, `Quot.sound`, `propext` | `8e6bc8b7c86a343bdd59ee499e4184e39ae69fe1d78e3bb3fae460d8f5e7fa59` | `047a525a0134fc6dbc1b7119ce7e5b13032907a93c2c25bcfe7985a4fd1e1c28` (55) |
| `Toy.UnwindCap.insertPads_foreignCovered_fails_without_foreignCovered` | `propext` | `7c699fa60bcc796cdb50cb46965233c9d0c3e3427b2c74412babb64e0037ef1c` | `f6d3079623889f2a7b95fff2ac4934e6c85778360fb402c30c8ca48105530281` (78) |
| `Toy.UnwindCap.insertPads_hypotheses_hold` | `Classical.choice`, `Quot.sound`, `propext` | `135816bb72e7a0ab55d2d4c10dfbcfc6ba4737d79a2a3f2a4cacb4f9ea1f47de` | `4c004123cccc4a019689908aa8d30a6a75f9ca5bed6ea27fd30fe36a87897a24` (110) |
| `Toy.UnwindCap.insertPads_pad_without_unwinding_callee` | `propext` | `47373a65a76ca5adb10efa96ef6f904f972c157d1d759070f9ade1e5f78fbd92` | `ba792cfda30fd511f68e34ec343a3ad8a9008e285148090f65e255c13884b9f7` (105) |
| `Toy.UnwindCap.insertPads_progAbortCallsUnwind` | `propext` | `381a792de0ea39c99107664fa1c335eefda63f7b6057ed4f8186b66eff8b2741` | `45d95dbdeaba883e06f050143245af9a0375c2a1bcd1ab0a6d5d7a6745da4953` (77) |
| `Toy.UnwindCap.insertPads_progAbortImportPlain` | `propext` | `2d456bab3c6226a387889cb38befe44a5907d98353d5fb8d7e0c2a188fd919ed` | `db1bbb7de706ee9bf52fcdfe7ea032798b9745a764a78800fd43281d6f7385b0` (78) |
| `Toy.UnwindCap.insertPads_siteAgreement` | `Classical.choice`, `Quot.sound`, `propext` | `05bc083588917030eceef0ce5d92eeb637e820f2edae78ea5ed9ea193b817ce3` | `8d9b155596ba8d21ad35c66763614d56576da0b24ed8403d83dec98fe181c768` (56) |
| `Toy.UnwindCap.insertPads_siteAgreement_fails_without_siteAgreement` | `propext` | `05442d1963e299724d0d218b6b169b77e35960672a66ff3be184c1954a896e7f` | `d5f8e5706f538565ccb82ca0571369547bdf8178268fe618022a5402af295884` (80) |
| `Toy.UnwindCap.noUB_fails_without_enforced` | `Quot.sound`, `propext` | `3d7a48da7113bf70d715c5b72fcc867178c3f7c861d4726816a41381c1cfbeaf` | `ace84825e56b18b8841ef2025ff8025c85e25b1973ffc3c1052d6d6bdd6616ca` (104) |
| `Toy.UnwindCap.noUB_fails_without_foreignCovered` | `Quot.sound`, `propext` | `12a406bdd2e8d5be8608e06ec6abd1b24d1b38d2ae5fefcbee1094b47d5fa094` | `48b8719fa842da23c1c209bb414daaa27680089d6d4a31e7d574952de6b7951b` (104) |
| `Toy.UnwindCap.noUB_fails_without_siteAgreement` | `Quot.sound`, `propext` | `9b95b1be39f7888464f342de8b39ed9cdd7b593c1061659b0b0cf1a0df599599` | `8e1eb26ee6302e6658a03d76f8dc035e3be40fea14d5735e9645e281f71b17b1` (104) |
| `Toy.UnwindCap.noUB_hypotheses_hold_progAbortImportPadded` | `Quot.sound`, `propext` | `08f72af0831e35b2038d7290b43b1a2abb12f14dcd642831cda6e1f213f62f59` | `c71dbaea94673323b45165a621d153b2e867dda31e1c928d1f77d8a3028be4e0` (106) |
| `Toy.UnwindCap.noUB_hypotheses_hold_progUnwindCatch` | `Quot.sound`, `propext` | `0790de6a6adcbe317a7a6739cff50db0f9cc8d0497352eb3494857cb4b21dc45` | `af0c4f004058a3a3e82d009c1d9fad08af4dfdd0dacee1a8a4be846ab9542ce0` (105) |
| `Toy.UnwindCap.noUB_insertPads_fails_without_foreignCovered` | `Quot.sound`, `propext` | `e92b56c72bf322bef637c764f285a3c779e5d4241da7e92b97e2f37b40b3f9a4` | `39c187f876d9f6ca97be9e128094056a11e693824f5f263c11dcada1fcac3a8e` (106) |
| `Toy.UnwindCap.noUB_insertPads_fails_without_siteAgreement` | `Quot.sound`, `propext` | `86ad1c26017ba3eeace7b4e38e216fc6720d3d8f897adbb5a04c65d3e1a097bd` | `b50cc2aacdc407f79e6125c3cd0d0d69f928af996d392204bccb38c37e95c489` (106) |
| `Toy.UnwindCap.noUB_insertPads_hypotheses_hold_progAbortImportPlain` | `Quot.sound`, `propext` | `a780412a449e547569790fbee9edf2dbf4ff7f0e436f8c32852fc7f31f01cef9` | `1e3a71203cdbffd8b6ac79a30670593b21eb6512e3a6b0fffb5516a51028f31c` (74) |
| `Toy.UnwindCap.noUB_insertPads_of_foreignCovered_of_siteAgreement` | `Classical.choice`, `Quot.sound`, `propext` | `46cf87ee8d5f4db2ff68b8bdd8b288888bcf9eeb357d4c5b6601dc2cc7da94e3` | `57ad61c49e8a55fddb87c1746a46542dbad0eda3d30ea2e6e658b46dfee67267` (84) |
| `Toy.UnwindCap.noUB_of_enforced_of_foreignCovered_of_siteAgreement` | `Quot.sound`, `propext` | `ed41d7ee411535b7af58603bae14b4b15b3912689b00e3c8b3abb6383d1a748a` | `f727c109b3f14cf345160b30bc965a49718f7b5231f7e3827bc95c9525883d03` (80) |
| `Toy.UnwindCap.noUB_std_fails_without_enforced` | `Quot.sound`, `propext` | `b40bde19ca8e520a976d910fabbbb92991f1afbe36ea28e2b1e2a1ff600b5214` | `88ea20d62bfcfc48004999a9e87fb7fc73d1f672793b89f92f3b8f2196ad24d9` (106) |
| `Toy.UnwindCap.noUB_std_fails_without_foreignHonest` | `Quot.sound`, `propext` | `93d6bdc737c2663eaf2ca4057e2d775b9f94a10c510cdf6d0ae44ecd7d6442c4` | `f32ab270b591b257e8f6f93338ea7238dc95832d582dc88c891162129fe2754a` (106) |
| `Toy.UnwindCap.noUB_std_fails_without_foreignNotGlue` | `Quot.sound`, `propext` | `f93dcc48b7da411a59ad78afc2356fe6a8305f52a61ba450dc1aae391bb0675b` | `3a8db43186571ebb8c87c040c9008218730700ad2f773ac9df31b31eb5f059b8` (105) |
| `Toy.UnwindCap.noUB_std_fails_without_glueAgreement` | `Quot.sound`, `propext` | `d9dd5e83cd05915351c63fba78cdaa44316e9a71842562ac020e8860bbf6e55e` | `9b5a3b36b85c72c60250b27b2c57b0c5499e92bac8d264e89234bfa4df1f01f3` (109) |
| `Toy.UnwindCap.noUB_std_fails_without_linkOK` | `Quot.sound`, `propext` | `440f9c3e1a2f33484c1b24597f0c450611321440e7d808d51b810729bef177c0` | `13fdaaecc4bca653e85512b4b1a2701e80aed6232e1202ba5295c9052d9d94b5` (107) |
| `Toy.UnwindCap.noUB_std_hypotheses_hold_progAbortHandlerRaisePlain` | `Quot.sound`, `propext` | `2406db9c3f4b49c2386157e675adc2029207c6ebdbcdf712324c429a7666472e` | `36d54946a09904dbccb14a9f4f395257c22346bac051924c6d43018749c0f6ec` (107) |
| `Toy.UnwindCap.noUB_std_hypotheses_hold_progMixedAbortBothCallsGlue` | `Quot.sound`, `propext` | `c4c642b46170b848459abd598503b39e4e9a888daa8d262b986c44abdf2805ca` | `51434f6e7fbc276c3afba227910975cf6b4db0349287e4ac501cd6bfb20732f4` (109) |
| `Toy.UnwindCap.noUB_std_of_linkOK_hypotheses_hold_progMixedLinkOK` | `Quot.sound`, `propext` | `d0c67c6ead516fd17b87952e746201f431a70ffe9cba6080dad7db5457881f4c` | `fec58a8abf7dd72a1741351b18fe3cc159255990c59d851f47e97bfe77d402e1` (111) |
| `Toy.UnwindCap.noUB_std_of_linkOK_hypotheses_hold_progUnwindCatch` | `Quot.sound`, `propext` | `4587e956157dc604577189bb0995ea427508eb00b7001c799f2ff629ce6bae27` | `37016ec1c360266e618c38b100eaf30fe7bee029243a894db8b9e7590d9dd3fa` (78) |
| `Toy.UnwindCap.noUB_std_of_linkOK_of_enforced_of_foreignHonest_of_foreignNotGlue_of_glueAgreement` | `Classical.choice`, `Quot.sound`, `propext` | `94beaa0b2dab200969dd1ed124a927981303fdc34f07bd74697e0761c6503495` | `4eb083410a70a4a97d2e4c75b925f24986c9e7d2f28e9dbeee0e00c9974c5c3b` (104) |
| `Toy.UnwindCap.onUnwind` | none | `e4cc333b70b016bdf3eeeeadb84542a6b98dd1baa796a3ee0254d2d471eee6c6` | `09d451d9e4c5d68bc48226ca7a6937a5b83b746968f40ce98cb6c2bec61fb7b9` (14) |
| `Toy.UnwindCap.padStmt` | `propext` | `842adcbda7418f6002e31657aa1c70b67802b7620f77df36af564e7fd12c1cdd` | `a55a9ae2a60da899cf814e3594bf0a1ee770df2a13bfd176bd3fb118d9c05090` (24) |
| `Toy.UnwindCap.padStmt_call` | `propext` | `23adccfa2e3d474489565eb49be5da2d3a84d70b1ae62a8b4ab747b3cb7989ce` | `e778a9247d3ef8ef664232195bffe5d4ab1650a367f7ff3850995cde1662ca61` (48) |
| `Toy.UnwindCap.padStmt_call_ne_iff` | `propext` | `302b786e597bfe2574800bb015626a94d8d3edf08721f458c65d4358c7373f62` | `e778a9247d3ef8ef664232195bffe5d4ab1650a367f7ff3850995cde1662ca61` (48) |
| `Toy.UnwindCap.padStmt_raise` | `propext` | `9962ba820593d7eb49c1476f4c64fbe6bcabd1cfabf87bd505ad52d6e0cd9d55` | `db4ba6b2dc3a530ee43c3d8cdb35cfb88e8d557d7da2495418241cdb17b1937b` (52) |
| `Toy.UnwindCap.padStmt_raise_ne_iff` | `propext` | `995aa08e7042057e0c443dac0aab7dc3cafe73f7648b2e1eaf1d1e60941b653b` | `e778a9247d3ef8ef664232195bffe5d4ab1650a367f7ff3850995cde1662ca61` (48) |
| `Toy.UnwindCap.pidAbortCfg` | none | `d5c7d8060346dbec3e3f42f12544a4ebfec60bfbf150b7cb51bf3c5d1c9ac150` | `7eabc0376e8dccbcc01e9eb245f76095c9f094c5ab62af7d17e42215a2bd48f4` (5) |
| `Toy.UnwindCap.potentiallyUnwinding_unwindCrateCallsCUnwind` | `propext` | `4393bf8a8c6f73b11c33d5239c2a4a5f59e164a9298eca46499f7b149d986375` | `8c841d5a597559cecca31b79e6d118578ca60d54b8dc554b24539c9b34509b62` (40) |
| `Toy.UnwindCap.precForeignSound_iff` | `propext` | `8173a0d09169b140af820c41987231fd63b7e905c38f96c11155785a1b9d0efa` | `c9e15fe08e81217125268318286fc7a6c6403075b57fc419a0613ab2038a20df` (42) |
| `Toy.UnwindCap.precForeignSound_iff_instances` | `propext` | `17d37939fefbb8ef7d3adc8cbce00c3dee5164d9138e411796a294d1cbab9603` | `bef7675dab3aef5b390229a451e3b06f56166b8e937546400624783248336ae7` (40) |
| `Toy.UnwindCap.progAbortCUnwindExport` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progAbortCallsUnwind` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progAbortHandlerRaisePlain` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progAbortImportPadded` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progAbortImportPlain` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progAbortPadsRaise` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progForeignGlue` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progForeignWithBody` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progGlueMismatch` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progMixedAbortBothCallsGlue` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progMixedLinkOK` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progNounwindCallee` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progPadsAgree` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progPadsFullUnenforced` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progPadsMayUnwind` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progPadsNonvac` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progPadsPlainUnwindThrough` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progPadsRaiseCleanup` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progPadsRaisePlain` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progPadsTerminate` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progPlainCallFromNounwind` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progTerminateFromNounwind` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progThrowingC` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progUnreachableCall` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.progUnwindCatch` | none | `2aafcc86a9066dd27404fd11620532a097c5c92585d29f8c3ad1d4567fe51634` | `ef6e3fd91f8dac92623fd4e130c1f030fba1d529f1b0c3fca495f8e1176a9f4b` (23) |
| `Toy.UnwindCap.refuted_insertPads_changes_exactly_nonunwinding_bodies` | `propext` | `b7f6c0ddbd32b45e0bf6666126613af74e55eee1ed346e9f478d223931929c37` | `1e5a95d1395d6ad935ae48ecbf1096e9d1e84f635dea20f45a7d2c2e99e6cc47` (54) |
| `Toy.UnwindCap.refuted_insertPads_keeps_cleanup_pads` | `propext` | `75021a2d756bbfe5e213616418442e486a16c9b7fba337c610a4bbb5f1a5473e` | `5ef0aaa33b0300c8a7e9040e776e4053ab7da6e9eb9977bb75b0fb7d2321ef40` (77) |
| `Toy.UnwindCap.refuted_padStmt_call_terminate_exactly` | `propext` | `dcf3a703c33811d8680d78dc46d8f6bcc08e3361dc0914943c4d590ac572c231` | `e778a9247d3ef8ef664232195bffe5d4ab1650a367f7ff3850995cde1662ca61` (48) |
| `Toy.UnwindCap.refuted_padStmt_raise_terminate_exactly` | `propext` | `0f4b116920fb14f2a885f1ae804d386a87878a96cce26b017d945c7cf5cec006` | `e778a9247d3ef8ef664232195bffe5d4ab1650a367f7ff3850995cde1662ca61` (48) |
| `Toy.UnwindCap.robust_fails_without_terminateShielded` | `propext` | `526a5e8a695cff6df9386cd514889bf4da201b22c0ffb75dfc1637b94f5f6647` | `1dd9929940f291150b4b639d85cd2d1e2424bba74d35d9fda2aef140f7b76f67` (36) |
| `Toy.UnwindCap.robust_iff_shielded` | `Quot.sound`, `propext` | `807eae845d1efbdaf51a9ff685188be43d0a2c947d531ed955fd07b8bebe7d2a` | `42d28153c82d07d352fd948e241fa505cd04e077533d44f817da70ef4c4000a6` (43) |
| `Toy.UnwindCap.robust_of_terminateShielded` | `Quot.sound`, `propext` | `dab79ae1beb8fe6d37c15e8a07188c0c5875d169de2f68c164f5ecffae2868bc` | `066c5dac46459a71aa2003f47084a96d9dc6481189228c26b1d72b9388106db2` (39) |
| `Toy.UnwindCap.robust_of_terminateShielded_hypotheses_hold` | `propext` | `e9690feb5aff07eaaa76744dfbef1713d503952f45cbab884bde04aeb7da93a7` | `e7af25c27506852607847d9d5498421f285544b05f05b0116ab2e35708094e05` (15) |
| `Toy.UnwindCap.runFn` | `propext` | `0e28d45b26fb1fde6854eaee014458e8c3eaee0766fce936e15e6c226f3e742f` | `59ef1c9fb75021e5a7b5eb09215cdc9b40e2b6c9af64c8a463f4ae1ea838808e` (33) |
| `Toy.UnwindCap.runFn_unwind_selfMay` | `Quot.sound`, `propext` | `be1842e4014b28c896c303d28bd5a12142acf4ac305cfb3f4e0acd336a7089df` | `35f0e231f46ef779eea08ddd92467c337c03cd5545aad0c45cb030dbdcb15216` (70) |
| `Toy.UnwindCap.rustDefinedCUnwind` | none | `64de140e04314756adbeb207189b920ff9afb7db02323b16744914e77b1cd436` | `9ce71d3cdfb00d54a22feaa6ac7918e59c693a8a513d75b562be400720028495` (6) |
| `Toy.UnwindCap.rustInfo` | none | `64de140e04314756adbeb207189b920ff9afb7db02323b16744914e77b1cd436` | `9ce71d3cdfb00d54a22feaa6ac7918e59c693a8a513d75b562be400720028495` (6) |
| `Toy.UnwindCap.shielded_examples` | `propext` | `f05d539e3db50e80466aa8e87bfbd57407c3252d0ae15b2ebb210b339033e242` | `63fa421a4aff75beef6bcdf12a5c8dab6f400401c0e3c1fcce8f71d79a0489f6` (23) |
| `Toy.UnwindCap.shielded_not_terminateShielded` | `Quot.sound`, `propext` | `6168b133cb1b186b914475c68cf16600712caa4165e159009fc3f4e6b211f580` | `68e9d9f262bcc14ad5f857ea3388f4ed5a921f8651a96c1839c275067618835a` (45) |
| `Toy.UnwindCap.shiftCodec` | none | `4a39e80f5ca90e32507fed07f069ad0ef3f55fd275a5f04bf15bc38e540011c9` | `7c985c267d17a0800f2c67d505a46660917492240007d4088480394808883022` (2) |
| `Toy.UnwindCap.specRet` | none | `a508c518def09eb0020d705faa21ce17e3ed4d6ba312ca8393dc0f6835347cb9` | `f69d930f66cd3afcb328d265d8b78876823b02d50db22a4f3969bdc579b13a40` (4) |
| `Toy.UnwindCap.specUnwind` | none | `197cb8cf7afc353b11100c892de8494fea584a3ed432916a9fea751ea3ddc878` | `a8cf194289fa2333a686baab73c4a6261e7f7865f1c1b0c8caa05ca0d7be6508` (17) |
| `Toy.UnwindCap.stdCanUnwind` | none | `9434f74e5f6883c8f7128e90100acdf37a316bbc27d39f935e0d1ee1358f4161` | `868bd8a5fe764b4539c05664d594d21901b21ed3f8d51f26308ea4e7dd5d08a3` (12) |
| `Toy.UnwindCap.std_and_abiFirst_foreignSound_but_differ` | `propext` | `0c9ec4bdd3093b5c118188c38d407df8c782b409a328e5f502ff662d5b360dfc` | `912f638577aba0b88b06cf695464cd3606ffb72c28786cf1a1a731df1838cab1` (67) |
| `Toy.UnwindCap.std_progAbortImportPlain_padded_noUB` | `Quot.sound`, `propext` | `d2f82d3d8ad28ac7ab34e3664e08a224cfb753c254f512cac53d142b12ab81be` | `201f51e1f38446b7f4a1dc1936f20b39c65420dd40a3a6ff3997bbd12fe511ef` (106) |
| `Toy.UnwindCap.truncCodec` | none | `4a39e80f5ca90e32507fed07f069ad0ef3f55fd275a5f04bf15bc38e540011c9` | `7c985c267d17a0800f2c67d505a46660917492240007d4088480394808883022` (2) |
| `Toy.UnwindCap.ub_of_selfNonUnwinding_of_unguarded_head_call_of_callee_unwinds` | `Quot.sound`, `propext` | `4936f94d53eacec17754e1171f2a781972f34073ec674b12c81fa302380ca963` | `f7329194fe5d10672349bf1ffab98811ae89ea8925dbabcace1ff48dcebc4f18` (75) |
| `Toy.UnwindCap.ub_of_unguarded_call_fails_without_callFirst` | `propext` | `a5c8efba31f0c3764f8542ca1da50c39ba44a4d313e880957179cc9825852c74` | `70bce613c7e26167c8f02a131c69b54accc92f60fcc33a97bc981f2d3f0c36da` (101) |
| `Toy.UnwindCap.ub_of_unguarded_call_fails_without_calleeUnwinds` | `Quot.sound`, `propext` | `0da532c503be78384e54216a4a70f0bc87f318b084539e6b3c39a6d21ae27390` | `636cd4d0e186de9a72df21631364f84b891e3382031a345b41cc2700dd68ee5d` (100) |
| `Toy.UnwindCap.ub_of_unguarded_call_fails_without_nonForeign` | `Quot.sound`, `propext` | `1a73fad19ec2ad2f7cb693f43edfd1d05747db6eeaccf81cfbab37a6804364ae` | `86bd61b0f5238eb3f2ed4c5a5307e2d808e5ffe217286547fe8a068373a8121c` (101) |
| `Toy.UnwindCap.ub_of_unguarded_call_fails_without_nonStopping` | `Quot.sound`, `propext` | `3d831162a5df290032aff5d73bffe7ad3960fdbd1b3c8aecf58db9263cf49d4d` | `8c2af32ebce9de89b4c706884355714d72b408afb7670877299a7f387d2d64fb` (97) |
| `Toy.UnwindCap.ub_of_unguarded_call_fails_without_selfNonUnwinding` | `Quot.sound`, `propext` | `5b26b11be3d248b403a92be8536b272b149aa2118d28837482d404c23cac4426` | `71ff1837f28f0e3e6a3bf993af9d9e17e7730198dc294e701d3e6b4ff68438ad` (100) |
| `Toy.UnwindCap.ub_of_unguarded_call_hypotheses_hold_progPlainCallFromNounwind` | `propext` | `d0ca9d8d924d0b431cb0457700888f056370658cb29a614a8af50a78e378ed50` | `dd813e3663a8473eb131e93cc66095baa7781fb5586cf0e2fbf8f563e5ea5a86` (101) |
| `Toy.UnwindCap.unwindCfg` | none | `d5c7d8060346dbec3e3f42f12544a4ebfec60bfbf150b7cb51bf3c5d1c9ac150` | `7eabc0376e8dccbcc01e9eb245f76095c9f094c5ab62af7d17e42215a2bd48f4` (5) |
| `Toy.UnwindCap.withPads_exec_iff_of_padsNone_nonunwinding_of_enforcedAt_of_siteAgreementAt` | `Classical.choice`, `Quot.sound`, `propext` | `7427e8862429c43240c9d7c54b8ebba5d519d675ddaf659b605503088402b20b` | `1bdeffe611238435786918d095d3b475eef8db1e14b4c66f1874fbe93f6db632` (86) |
| `Toy.UnwindCap.withPads_exec_iff_of_padsNone_obligationFreeRaises_of_obligationCalleesNonUnwinding` | `Classical.choice`, `Quot.sound`, `propext` | `31391534f4f795d1c8b305fc37465a3d7a99498586e17f4b3e81f6906e584423` | `431a4de201995ac862fbf3e7ba25929df57b77552ed0a2a10623a7d60456d658` (82) |
| `Toy.UnwindCap.withPads_fails_without_enforcedCompiled` | `Quot.sound`, `propext` | `7f43525cdd9403527a2a71a5e3924c694c8b7d0b18caf5586051280b7c6a1d23` | `818a60c2503796c932b475b9d7395da68a2b8677570e0d2cbf3dbf737713f004` (114) |
| `Toy.UnwindCap.withPads_fails_without_padsNoneNonUnwinding` | `Quot.sound`, `propext` | `9524199440bfadfee287a37d074dc867ee82044a729248a045d8fdbf6dd208ce` | `09af1394fdd14f08c39bc45e700e18e4cba42d2dabef52d48f6fdaaf036de158` (112) |
| `Toy.UnwindCap.withPads_fails_without_siteAgreementCompiled` | `Quot.sound`, `propext` | `d1776b228fcefc1f298cf5935f1848a1e8c941f2b20d4f0749073537012f8320` | `1822921ee72147a8963023291e10be6c479515adb439f4d83ef0c441dccc7e7e` (114) |
| `Toy.UnwindCap.withPads_hypotheses_hold_progPadsFullUnenforced` | `Quot.sound`, `propext` | `a7d196c0bb7076e288210de17bfaaa30f634219f2b605bd23041e6bcf0e952cb` | `d7f527f03274046e97b98b851bd0c85fae78481925f60723d0caf2d1e712078b` (89) |
| `Toy.UnwindCap.withPads_hypotheses_hold_progPadsNonvac` | `Quot.sound`, `propext` | `b98224b135c8930867426327b402e74c8365ecec40b28b250a97d9e2706217de` | `5a7529c4b70fa73fe1404a03cd619998e6b877362788c6bc8d24fe71562a68e3` (113) |
| `Toy.UnwindCap.withPads_local_fails_without_obligationCalleesNonUnwinding` | `Quot.sound`, `propext` | `6d766541d6837b408dcbf0ae42b40260e9b5146177ca4e03b99c39b9a0b65d5a` | `6cb1b5e3bb25f97c235438686b309ae04100fce47df5282b1c5ed9dcace9c283` (108) |
| `Toy.UnwindCap.withPads_local_fails_without_obligationFreeRaises` | `propext` | `3b71a77ba2871329fc435d23a90d547b10d8088f99d483a4c172013b4fbf46e9` | `07f562fe61ca04db2ace64b70a38a816bd11cb38e5d4758678e4b82a1b7926b5` (108) |
| `Toy.UnwindCap.withPads_local_hypotheses_hold_progAbortPadsRaise` | `propext` | `2800e131fedcd456a76f0f045e6a4e6693696f843de879bde6279230bfe8a214` | `040581006d7605d663b609dca2ae2d1eea3a9b0af17bb803c2d272caa1db9cc4` (108) |
| `Toy.UnwindCap.withPads_local_hypotheses_hold_progPadsNonvac` | `propext` | `fe40c0b572d2c6f6fe400bdab94467db6568b63b4726adabde05a9566b77bff8` | `51687e1c5ac82b5fc2235d7956f4d48cfc70c2c4e8693e8955ae751316f298e3` (72) |
| `Toy.UnwindCap.withPads_local_hypotheses_hold_progPadsPlainUnwindThrough` | `propext` | `9affe585554f4170da2da5014c611d67f528e3be0eb2dad5550756a9c494cfbb` | `28cf577fc988b5c6d931b16aff1e0232385edf1335142e5595924dbd2fb5b635` (108) |
| `Toy.UnwindCap.withPads_local_hypotheses_hold_progPadsRaisePlain` | `propext` | `9bb71736c2246ffef8e8cf52deb28b184387b5fe8afbc9c8cf4f75a67c343fae` | `d8a523819e7c6a0acaff98f1da575a127b640e4e8f392b020fdee4e42a739c1b` (108) |

### Proof status of the main theorems

Every main theorem below is kernel-checked without `sorry`; its axioms are in the table above (at most `propext`, `Classical.choice` and `Quot.sound`).

* R1: `Toy.UnwindCap.noUB_of_enforced_of_foreignCovered_of_siteAgreement`
* R2: `Toy.UnwindCap.foreignCovered_std_of_foreignHonest_of_foreignNotGlue`
* R3: `Toy.UnwindCap.precForeignSound_iff`
* R4: `Toy.UnwindCap.std_and_abiFirst_foreignSound_but_differ`
* R5: `Toy.UnwindCap.abortAllCanUnwind_not_foreignSound`, `Toy.UnwindCap.abortAll_progAbortImportPlain_ub`
* R6: `Toy.UnwindCap.insertPads_enforced`, `Toy.UnwindCap.insertPads_body`, `Toy.UnwindCap.padStmt_call`, `Toy.UnwindCap.padStmt_raise`, `Toy.UnwindCap.insertPads_foreignCovered`, `Toy.UnwindCap.insertPads_siteAgreement`, `Toy.UnwindCap.exec_insertPads_of_exec_of_ne_ub`
* R7: `Toy.UnwindCap.noUB_insertPads_of_foreignCovered_of_siteAgreement`
* R8: `Toy.UnwindCap.ub_of_selfNonUnwinding_of_unguarded_head_call_of_callee_unwinds`
* R9: `Toy.UnwindCap.noUB_std_of_linkOK_of_enforced_of_foreignHonest_of_foreignNotGlue_of_glueAgreement`
* R10: `Toy.UnwindCap.glueSiteSound_iff`
* R11: `Toy.UnwindCap.glueSiteSound_iff_panicInDrop`
* R12: `Toy.UnwindCap.compRet_eq_specRet_of_conforms`
* R13: `Toy.UnwindCap.compUnwind_eq_specUnwind_iff_obligationsFull_of_noReachedNoneTerminate`
* R18: `Toy.UnwindCap.compUnwind_eq_specUnwind_of_obligationsFull`
* R14: `Toy.UnwindCap.robust_iff_shielded`
* R15: `Toy.UnwindCap.robust_of_terminateShielded`
* R16: `Toy.UnwindCap.withPads_exec_iff_of_padsNone_nonunwinding_of_enforcedAt_of_siteAgreementAt`
* R17: `Toy.UnwindCap.withPads_exec_iff_of_padsNone_obligationFreeRaises_of_obligationCalleesNonUnwinding`

### Primary sources

Source and documentation text (each excerpt quoted verbatim, with its line range, under Findings, "Sources and modeling bridge"; retrieved 2026-11-21, the LLVM excerpt on 2026-11-22, and all compared again with the files at the pinned revisions on 2026-11-22):

* rust-lang/rust@26bfbf28f5f79dff333ce5a232f131b496ec9cfe `compiler/rustc_middle/src/ty/layout.rs`:1247-1264, 1267-1291, 1326-1330 (`fn_can_unwind`; the cards also cite its doc comment 1225-1264 and lines 1229-1232, 1258-1262 and 1284-1285 inside the quoted or cited ranges) [source].
* rust-lang/rfcs@f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4 `text/2945-c-unwind-abi.md`:205-209, 230-235, 366-375 (RFC 2945) and `text/1513-less-unwinding.md`:108-111, 142-146 (RFC 1513) [normative design documents, merged].
* rust-lang/reference@c9cc32825b03fc206d9c6fe73e9ca6a2f3576d6c `src/panic.md`:97-101, 109-110, 124-128, 130-134 and `src/linkage.md`:154-176 [documentation]; the cards also cite `src/panic.md`:86-101 and 103-116 by range.
* llvm/llvm-project@a4bf6cd7cfb1a1421ba92bca9d017b49936c55e4 (tag `llvmorg-19.1.0`) `llvm/docs/LangRef.rst`:2177-2183 (`nounwind`) [documentation].

Related reports of the same corpus, cited by name in the cards (not dependencies, not subjects): `rustc-cleanup-post-borrowck-false-edges-and-abort-unwinding-mir-lowering`, `rust-no-std-panic-abort-eh-personality-and-cross-crate-unwinding-abi-contracts`, `drop-flag-elaboration-partial-moves-and-unwind-cleanup-exactly-once-destruction`, `panic-safety-unwinding-through-broken-invariants-leak-amplification-and-safe-forget`, `call-site-inlining-slot-renaming-cleanup-splicing-capability-guards-and-caller-locations`, `cfg-dwarf-cfi-state-stack-and-lsda-landing-pad-unwinding-soundness`, `explicit-tail-calls-frame-reuse-pre-jump-drop-order-stack-borrow-rejection-and-inlining` and `codec-round-trip-laws-and-partial-isomorphisms`.

Papers (bibliographic metadata of each DOI checked against the Crossref record on 2026-11-22; descriptions in the cards are limited to what the abstracts state):

* T. Ramananandro, G. Dos Reis, X. Leroy, "A Mechanized Semantics for C++ Object Construction and Destruction, with Applications to Resource Management", POPL 2012 (ACM SIGPLAN Notices 47(1)), pp. 521-532, doi:10.1145/2103621.2103718.
* G. Klein, T. Nipkow, "A Machine-Checked Model for a Java-Like Language, Virtual Machine, and Compiler", ACM TOPLAS 28(4), 2006, pp. 619-695, doi:10.1145/1146809.1146811.
* T. Bastian, S. Kell, F. Zappa Nardelli, "Reliable and Fast DWARF-Based Stack Unwinding", Proc. ACM Program. Lang. 3 (OOPSLA), Article 146, 2019, doi:10.1145/3360572.
* J. Matthews, R. B. Findler, "Operational Semantics for Multi-Language Programs", ACM TOPLAS 31(3), Article 12, 2009, doi:10.1145/1498926.1498930.
* D. Abrahams, R. Sharoni, D. Gregor, "Allowing Move Constructors to Throw (Rev. 1)", ISO/IEC JTC1/SC22/WG21 N3050, 2010-03-12, https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2010/n3050.html (title, authors and date checked at that URL on 2026-11-22; cited as prose, no excerpt relied on).

## Revalidation

Requirements: `elan` (so that `lake` selects the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

`support/revalidate.py` copies `lean/` to a temporary directory (the package is not modified) and checks: (1) `lake build` succeeds; (2) no Lean source contains `sorry`, `admit` or `native_decide`, or declares an `axiom`; (3) every declaration of the `ToyUnwindCap` library depends on no axiom other than `propext`, `Classical.choice` and `Quot.sound` (Lean's `collectAxioms`); (4) for every Lean name in `results.json` (fields `lean`, `lean_names`, `nonvacuity_witness_lean`, `positive_control_lean` and the hypotheses' `counterexample`), the SHA-256 of the statement (Lean `repr` of its type) and of its definition closure (types and values of every package-local constant reachable from the statement; theorem bodies excluded) equals the value recorded in `audit/statements.json`. The script contains the exact Lean program that computes what is hashed. It exits with status 0 if and only if all four checks pass.

A manual check of the build and of the axioms of the 25 main theorems, without the script:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean
```

`lean/RevalidationAudit.lean` (outside the library target) runs `#print axioms` on each of the 25 main theorems; each reported axiom list must contain no axiom other than `propext`, `Classical.choice` and `Quot.sound`. A change to any definition in `Basic.lean`, `Chain.lean`, `Results.lean`, `ChainResults.lean`, `Examples.lean` or `Counterexamples.lean` changes the recorded closure hashes of the results that depend on it, and step (4) of the script reports which ones.
