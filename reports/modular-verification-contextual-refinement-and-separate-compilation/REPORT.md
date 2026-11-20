# Modular verification, contextual refinement, and separate compilation in a toy first-order module language (Lean 4)

## Summary

This package is a Lean 4 mechanization, in a deliberately small model, of which per-module guarantees compose into whole-program guarantees under linking. The model has stateless first-order modules of single-argument integer functions, disjoint linking, a call-depth-indexed ("fuel") big-step semantics with binary nondeterministic choice, Hoare-style function contracts, and per-module compiler passes. Every result below is kernel-checked under `leanprover/lean4:v4.34.1` with no Mathlib and only the axioms `propext`, `Classical.choice`, `Quot.sound`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

Two facts frame every result. **Behaviour is fuel-indexed:** the refinement relations (`EntryRefines`, `StandaloneRefines`, `CtxRefines`) compare the sets of outcomes `val v`, `undefinedCall`, `outOfFuel` at the *same* call-depth bound, so they do observe divergence (as `outOfFuel` at every fuel) and they fix call depth; only the partial-correctness notions ignore divergence. **The model has no private symbols:** every function a module defines is exported and callable by any context, so contextual refinement forces equal domains.

One sentence per result (the key hypotheses are part of each sentence):

1. **ctx-refines-refl** (reference point): every module contextually refines itself, `CtxRefines M M`; no hypotheses.
2. **ctx-refines-trans**: if `CtxRefines M₁ M₂` and `CtxRefines M₂ M₃`, then `CtxRefines M₁ M₃`, with no extra domain or linkability hypothesis on the middle module.
3. **ctx-refines-precongruence-link**: if `CtxRefines M₁ M₁'`, `CtxRefines M₂ M₂'` and the source modules are disjoint (`Linkable M₁ M₂`), then `CtxRefines (link M₁ M₂) (link M₁' M₂')`; disjointness of the targets is derived.
4. **ctx-refines-forces-same-domain**: `CtxRefines M M'` implies that `M` and `M'` define exactly the same function names, so (in this model, where every definition is exported and calling an undefined name is the observable outcome `undefinedCall`) adding, deleting, or renaming any function breaks contextual refinement.
5. **cex-add-or-delete-function-not-contextual** (counterexample): deleting an exported function that no in-module code calls, or adding an unused function, preserves refinement in both directions at entry `0` of a closed module but is not a contextual refinement, purely because the domain changes.
6. **ctx-refines-closed-collapse**: if the source or the target module is closed (`ClosedModule M ∨ ClosedModule M'`), then `CtxRefines M M'` is equivalent to standalone refinement at every entry point (`StandaloneRefines M M'`).
7. **cex-closed-main-entry-refinement-not-contextual** (counterexample): specializing exported function `1` of a closed module to the argument its only in-module caller passes preserves refinement in both directions at entry `0`, with equal domains, but fails refinement at entry `1` with no context, hence is not a contextual refinement.
8. **cex-open-specialization-standalone-refinement-not-contextual** (counterexample): for two open modules (an import supplied by the context), standalone refinement in both directions at every entry, plus refinement at entry `0` of the one program they ship in, does not imply contextual refinement: an entry-`1` call in that program and a context whose import calls back into the module separate them.
9. **ctx-refines-reflects-may-divergence**: if `CtxRefines M M'` and the context `C` is disjoint from `M`, then wherever `link C M'` may diverge (`outOfFuel` at every fuel) so may `link C M`; contextual refinement observes divergence.
10. **cex-ctx-refines-fixes-call-depth** (counterexample): two modules with equal domains that evaluate identically at every entry and argument once fuel is at least `2`, but differ by one call on a path, are unrelated by `CtxRefines` in both directions; contextual refinement fixes call depth.
11. **ag-partial-correctness**: if every function with a satisfiable precondition is defined in `P` (`SpecsImplemented P S`) and every body of `P` satisfies its contract assuming every callee satisfies its contract (`ModuleVerifiedPartial P S S`), then `P` is partially correct for `S`, with no termination measure; the linked-module form takes the two module obligations separately.
12. **cex-ag-total-circular-unsound** (counterexample): the self-loop `[(0, call 0 var)]` implements the contract "`0` returns `0`" and satisfies the circular partial-correctness obligation, yet is not totally correct; circular reasoning is unsound for termination.
13. **ag-total-correctness-wf-measure**: if `rel` is well-founded, `P` implements every satisfiable precondition of `S`, and every body establishes its contract while every call strictly decreases one shared call measure `μ` under `rel` and meets the callee precondition (`ModuleVerifiedTotal rel μ P S S`), then `P` is totally correct for `S` (one finite fuel bound per argument); the linked-module form requires the same `(rel, μ)` for both modules.
14. **spec-refinement-link-composition**: if a caller module `M` is verified for its guarantee `G` assuming `G` for calls to its own functions and an interface `S` for all other calls, and a disjoint callee module `N` is partially correct on its own for a spec `S'` that refines `S` at every name `M` does not define (weaker precondition, postcondition strengthened under the precondition), then every function of `M` is partially correct for `G` in `link M N`; `M` may be recursive.
15. **cex-spec-refinement-incomparable-callee** (counterexample): a verified caller linked with a callee that is correct for a spec whose precondition is weaker than assumed but whose postcondition is also weaker than assumed (so neither spec refines the other) violates the caller's guarantee.
16. **separate-compilation-preserves-verifiability**: if `M₁`, `M₂` are verified against the interface `S`, `link M₁ M₂` implements `S`, and a per-module pass preserves verification against `S` and keeps every defined name, then the separately compiled linked program is partially correct for `S`; no behavioural relation to the source program is claimed.
17. **separate-compilation-behavioural-refinement**: if a per-module pass is a contextual refinement on every module (`PassCtxRefines compile`) and `M₁`, `M₂` are disjoint, then `link (compile M₁) (compile M₂)` contextually refines `link M₁ M₂`; a corollary with the additional premise that the source link is partially correct for `S` transfers that partial correctness to the compiled link.
18. **cex-verifiability-preservation-not-behavioural** (counterexample): a pass that replaces every body by `lit 0` preserves verification against the interface "`0` returns a non-negative value" and keeps every name, so all hypotheses of the verifiability theorem hold, yet the compiled program returns `0` where the source returns `1`.
19. **cex-separate-compilation-callee-dependent-rewrite** (counterexample): a per-module rewrite of a caller that is valid only for one particular callee body is a contextual equivalence in that whole program, but it is neither a per-module contextual refinement nor verifiable against the shared interface, and it breaks when the callee is replaced by another implementation of the same interface.

What these results do *not* show is listed first under **Boundaries** (non-claims per result, then escape hatches and the parts of the design space that were not examined).

## Applicability

**Model fidelity: this is a toy model.** All definitions are in the Lake project under `lean/` (library `ToyLink`, namespace `Toy.Link`); the key ones are quoted under **Findings**. The definitions are meant to capture, in miniature:

- *compilation units and static linking:* a module is a finite association list from function names (`Nat`) to bodies; `link M₁ M₂ = M₁ ++ M₂` under the disjointness condition `Linkable`; calls to names no linked module defines are not a link-time error but yield the run-time outcome `undefinedCall` when executed;
- *per-function modular verification* as done by contract-based program verifiers: each body is checked against its own contract assuming only the contracts of the functions it calls (`wpPartial`, `wpCallDec`);
- *separate compilation:* a per-module pass `compile : Module → Module` applied to each module before linking.

Known gaps between the model and real systems (each is also recorded as a non-claim where it matters):

- no memory, state, pointers, address-taking, I/O, exceptions, or concurrency; contexts interact with a module only through calls and return values (including callbacks);
- every definition is exported: there is no `static`/private symbol, no symbol hiding, no scoped name resolution; adding, deleting, or renaming any function is observable;
- functions take one unbounded integer argument and return one unbounded integer; contracts relate that argument and result only (no frames, auxiliary variables, or adaptation rules);
- nondeterminism is finite and binary (`choose`); results about uniform fuel bounds depend on this;
- a single source language: no change of language, memory model, or calling convention between source and compiled modules;
- linking never fails, and `undefinedCall` is an ordinary observable outcome that a source program does not "license" to be refined arbitrarily (unlike the going-wrong relaxation of whole-program compiler correctness);
- the refinement relations compare outcomes in lockstep call depth; a refinement notion insensitive to call depth (for example, comparing outcomes at some sufficiently large fuel) is a different design and is not studied.

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`), core library only; no Mathlib, no Lake dependencies (`lakefile.toml` declares one `[[lean_lib]]`, `ToyLink`, with `autoImplicit = false`). The bibliographic subjects in `REPORT.json` are prior-art sources: they are cited for what the toy theorems re-derive or contrast with; no claim of this package is a claim about their formal developments.

**Private helper definitions.** Some witness modules and specifications are `private` in the Lean source (they are kept `private` because the published statement hashes of the theorems that mention them include their internal names). Their full definitions are printed under **Findings / Concrete modules and specifications**, so every statement in this report can be read without consulting the source.

## Findings

### Definitions

Quoted from `lean/ToyLink/Defs.lean` and `lean/ToyLink/Spec.lean` (doc comments omitted; `evalExprWith` abbreviated as described).

```lean
abbrev Fname := Nat

inductive Expr : Type where
  | lit (n : Int) | var
  | add (e₁ e₂ : Expr) | sub (e₁ e₂ : Expr) | mul (e₁ e₂ : Expr)
  | ifLe (e₁ e₂ eThen eElse : Expr)     -- if e₁ ≤ e₂ then eThen else eElse
  | choose (e₁ e₂ : Expr)               -- binary nondeterministic choice
  | call (fn : Fname) (arg : Expr)

inductive Outcome : Type where
  | val (v : Int) | undefinedCall | outOfFuel

abbrev Module := List (Fname × Expr)    -- every definition is exported

def Module.lookup : Module → Fname → Option Expr
  | [], _ => none
  | (k, body) :: rest, fn => if k = fn then some body else lookup rest fn
def Module.Defines (M : Module) (fn : Fname) : Prop := (M.lookup fn).isSome = true
def SameDom (M₁ M₂ : Module) : Prop := ∀ fn, M₁.Defines fn ↔ M₂.Defines fn
def Linkable (M₁ M₂ : Module) : Prop := ∀ fn, ¬ (M₁.Defines fn ∧ M₂.Defines fn)
def link (M₁ M₂ : Module) : Module := M₁ ++ M₂
def ClosedModule (M : Module) : Prop :=
  ∀ fn body, M.lookup fn = some body → body.CalleesIn M.Defines
  -- CalleesIn P e : every `call fn _` occurring syntactically in e has P fn

-- evalExprWith callFn x e : List Outcome evaluates e with parameter value x; arithmetic and
-- `ifLe` act on `val` outcomes and propagate any other outcome unchanged; `choose e₁ e₂`
-- appends both outcome lists; `call fn e` runs `callFn fn v` for every value v of e.
def eval : Nat → Module → Fname → Int → List Outcome
  | 0, _, _, _ => [.outOfFuel]
  | fuel + 1, P, fn, arg =>
      match P.lookup fn with
      | none => [.undefinedCall]
      | some body => evalExprWith (eval fuel P) arg body

def HasBehavior (entry : Fname) (P : Module) (fuel : Nat) (arg : Int) (out : Outcome) : Prop :=
  out ∈ eval fuel P entry arg
def EntryRefines (entry : Fname) (P P' : Module) : Prop :=
  ∀ fuel arg out, HasBehavior entry P' fuel arg out → HasBehavior entry P fuel arg out
def StandaloneRefines (M M' : Module) : Prop := ∀ entry, EntryRefines entry M M'
def CtxRefines (M M' : Module) : Prop :=
  ∀ C, Linkable C M → Linkable C M' → ∀ entry, EntryRefines entry (link C M) (link C M')
def MayDiverge (P : Module) (entry : Fname) (arg : Int) : Prop :=
  ∀ fuel, HasBehavior entry P fuel arg .outOfFuel
```

Fully unfolded, `CtxRefines M M'` is

```lean
∀ C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) → (∀ fn, ¬ (C.Defines fn ∧ M'.Defines fn)) →
  ∀ entry fuel arg out, out ∈ eval fuel (link C M') entry arg → out ∈ eval fuel (link C M) entry arg
```

(`M'` is the refined, "target" module and `M` the "source"; the entry may be a name of `C`, of the module, or of neither; contexts need not close the program.)

```lean
structure FnSpec where
  pre : Int → Prop
  post : Int → Int → Prop
abbrev SpecEnv := Fname → FnSpec

def FnPartialCorrect (P : Module) (fn : Fname) (spec : FnSpec) : Prop :=
  ∀ fuel x out, spec.pre x → HasBehavior fn P fuel x out →
    out = .outOfFuel ∨ ∃ v, out = .val v ∧ spec.post x v
def ProgramPartialCorrect (P : Module) (S : SpecEnv) : Prop := ∀ fn, FnPartialCorrect P fn (S fn)
def FnTotalCorrect (P : Module) (fn : Fname) (spec : FnSpec) : Prop :=
  ∀ x, spec.pre x → ∃ fuel, ∀ out, HasBehavior fn P fuel x out → ∃ v, out = .val v ∧ spec.post x v
def ProgramTotalCorrect (P : Module) (S : SpecEnv) : Prop := ∀ fn, FnTotalCorrect P fn (S fn)
def SpecsImplemented (P : Module) (S : SpecEnv) : Prop := ∀ fn x, (S fn).pre x → P.Defines fn

def wpPartial (A : SpecEnv) (x : Int) : Expr → (Int → Prop) → Prop
  | .lit n, Q => Q n
  | .var, Q => Q x
  | .add e₁ e₂, Q => wpPartial A x e₁ (fun v₁ => wpPartial A x e₂ (fun v₂ => Q (v₁ + v₂)))
  -- .sub, .mul: likewise with v₁ - v₂, v₁ * v₂
  | .ifLe e₁ e₂ eThen eElse, Q =>
      wpPartial A x e₁ (fun v₁ => wpPartial A x e₂ (fun v₂ =>
        (v₁ ≤ v₂ → wpPartial A x eThen Q) ∧ (¬ v₁ ≤ v₂ → wpPartial A x eElse Q)))
  | .choose e₁ e₂, Q => wpPartial A x e₁ Q ∧ wpPartial A x e₂ Q
  | .call fn eArg, Q =>
      wpPartial A x eArg (fun vArg => (A fn).pre vArg ∧ ∀ vRes, (A fn).post vArg vRes → Q vRes)
def BodyVerifiedPartial (A : SpecEnv) (body : Expr) (spec : FnSpec) : Prop :=
  ∀ x, spec.pre x → wpPartial A x body (spec.post x)
def ModuleVerifiedPartial (M : Module) (A G : SpecEnv) : Prop :=
  ∀ fn body, M.lookup fn = some body → BodyVerifiedPartial A body (G fn)

-- wpCallDec rel μ A cur x e Q: as wpPartial, except that the call case also requires the
-- measure of the callee to decrease:
--   | .call fn eArg, Q => wpCallDec rel μ A cur x eArg (fun vArg =>
--         rel (μ fn vArg) cur ∧ (A fn).pre vArg ∧ ∀ vRes, (A fn).post vArg vRes → Q vRes)
def BodyVerifiedTotal {α : Type} (rel : α → α → Prop) (μ : Fname → Int → α)
    (A : SpecEnv) (fn : Fname) (body : Expr) (spec : FnSpec) : Prop :=
  ∀ x, spec.pre x → wpCallDec rel μ A (μ fn x) x body (spec.post x)
def ModuleVerifiedTotal {α : Type} (rel : α → α → Prop) (μ : Fname → Int → α)
    (M : Module) (A G : SpecEnv) : Prop :=
  ∀ fn body, M.lookup fn = some body → BodyVerifiedTotal rel μ A fn body (G fn)

def WeakensPre (spec spec' : FnSpec) : Prop := ∀ x, spec.pre x → spec'.pre x
def StrengthensPostUnderPre (spec spec' : FnSpec) : Prop :=
  ∀ x v, spec.pre x → spec'.post x v → spec.post x v
def mixEnv (M : Module) (G S : SpecEnv) : SpecEnv := fun g => if M.Defines g then G g else S g

def PreservesVerifiedPartial (compile : Module → Module) (S : SpecEnv) : Prop :=
  ∀ M, ModuleVerifiedPartial M S S → ModuleVerifiedPartial (compile M) S S
def PreservesDefines (compile : Module → Module) : Prop := ∀ M fn, M.Defines fn → (compile M).Defines fn
def PassCtxRefines (compile : Module → Module) : Prop := ∀ M, CtxRefines M (compile M)
```

Every core definition has proved intended positive and negative examples in `lean/ToyLink/Examples.lean` (`*_pos`, `*_neg`, for example `standaloneRefines_pos`/`standaloneRefines_neg`, `mayDiverge_pos`/`mayDiverge_neg`, `mixEnv_pos`, `mixEnv_pos_external`, `mixEnv_neg`, `passCtxRefines_pos`/`passCtxRefines_neg`). `lean/ToyLink/Unfolded.lean` restates each main theorem with these wrappers unfolded and checks each restatement against the folded statement by `Iff.rfl`; `Toy.Link.Unfolded.ctxRefines_sameDom_unfolded_iff` (in `lean/ToyLink/Supplement.lean`) does the same for `ctxRefines_sameDom`.

Proof lemmas of `lean/ToyLink/Basic.lean` that the results below name by short name in depth justifications, unfolded-statement notes and non-claims (statements only; no card references them, and their proofs are in that file):

```lean
-- lean/ToyLink/Basic.lean (namespace Toy.Link)
theorem Toy.Link.lookup_link_comm {M₁ M₂ : Module} (h : Linkable M₁ M₂) (fn : Fname) :
    (link M₁ M₂).lookup fn = (link M₂ M₁).lookup fn

theorem Toy.Link.lookup_link_assoc (M₁ M₂ M₃ : Module) (fn : Fname) :
    (link (link M₁ M₂) M₃).lookup fn = (link M₁ (link M₂ M₃)).lookup fn

theorem Toy.Link.eval_one_undefinedCall_iff (P : Module) (fn : Fname) (arg : Int) :
    .undefinedCall ∈ eval 1 P fn arg ↔ ¬ P.Defines fn

theorem Toy.Link.eval_link_right_of_no_undefinedCall {M N : Module} (hLink : Linkable M N) :
    ∀ fuel fn arg, .undefinedCall ∉ eval fuel N fn arg →
      eval fuel (link M N) fn arg = eval fuel N fn arg

theorem Toy.Link.eval_stabilizes_of_no_outOfFuel {P : Module} :
    ∀ fuel₁ fuel₂, fuel₁ ≤ fuel₂ → ∀ fn arg,
      .outOfFuel ∉ eval fuel₁ P fn arg →
      eval fuel₂ P fn arg = eval fuel₁ P fn arg

theorem Toy.Link.wpPartial_sound_evalExprWith {A : SpecEnv} {callFn : Fname → Int → List Outcome}
    (hCalls : ∀ g vArg o, (A g).pre vArg → o ∈ callFn g vArg →
      o = .outOfFuel ∨ ∃ vRes, o = .val vRes ∧ (A g).post vArg vRes)
    {x : Int} {e : Expr} {Q : Int → Prop}
    (hwp : wpPartial A x e Q) :
    ∀ out ∈ evalExprWith callFn x e, out = .outOfFuel ∨ ∃ v, out = .val v ∧ Q v

theorem Toy.Link.moduleVerifiedPartial_link {M₁ M₂ : Module} {A G : SpecEnv}
    (h₁ : ModuleVerifiedPartial M₁ A G) (h₂ : ModuleVerifiedPartial M₂ A G) :
    ModuleVerifiedPartial (link M₁ M₂) A G

theorem Toy.Link.eval_link_superset_non_undefinedCall {C M : Module} (hC : Linkable C M) :
    ∀ fuel fn arg out, out ∈ eval fuel M fn arg → out ≠ .undefinedCall →
      out ∈ eval fuel (link C M) fn arg

theorem Toy.Link.eval_link_closed {C M : Module} (hC : Linkable C M) (hM : ClosedModule M) :
    ∀ n g v, M.Defines g → eval n (link C M) g v = eval n M g v

theorem Toy.Link.closedModule_no_undefinedCall {M : Module} (hM : ClosedModule M) :
    ∀ fuel fn arg, M.Defines fn → .undefinedCall ∉ eval fuel M fn arg

theorem Toy.Link.sameDom_of_standaloneRefines {M M' : Module} (h : StandaloneRefines M M') :
    SameDom M M'

theorem Toy.Link.standaloneRefines_of_ctxRefines {M M' : Module} (h : CtxRefines M M') :
    StandaloneRefines M M'

theorem Toy.Link.entryRefines_preserves_fnPartialCorrect {P P' : Module} {fn : Fname}
    {spec : FnSpec} (hRef : EntryRefines fn P P') (hP : FnPartialCorrect P fn spec) :
    FnPartialCorrect P' fn spec
```

### Concrete modules and specifications

Bodies are written in constructor syntax (`call 1 var` is `Expr.call 1 Expr.var`, `lit 0` is `Expr.lit 0`). Specifications that are not stated otherwise have an unsatisfiable precondition (`pre := fun _ => False`) at every name not listed.

Public definitions (`lean/ToyLink/Examples.lean`, `lean/ToyLink/Counterexamples.lean`, `lean/ToyLink/Supplement.lean`):

```lean
-- lean/ToyLink/Examples.lean (namespace Toy.Link.Examples)
def idMod : Module := [(0, .var)]
def twoFnMod : Module := [(0, .lit 1), (1, .lit 2)]
def addTenMod : Module := [(1, .add .var (.lit 10))]
def openCallerMod : Module := [(0, .call 1 .var)]
def choose01Mod : Module := [(0, .choose (.lit 0) (.lit 1))]
def choose012Mod : Module := [(0, .choose (.lit 0) (.choose (.lit 1) (.lit 2)))]
def const0Mod : Module := [(0, .lit 0)]
def const1Mod : Module := [(0, .lit 1)]
def selfLoopMod : Module := [(0, .call 0 .var)]
def falseSpec : SpecEnv := fun _ => { pre := fun _ => False, post := fun _ _ => False }
def trivZeroSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ _ => True }
  else { pre := fun _ => False, post := fun _ _ => False }
def idZeroSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun x v => v = x }
  else { pre := fun _ => False, post := fun _ _ => False }
def zeroOutSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else { pre := fun _ => False, post := fun _ _ => False }
def foldAdd (a b : Expr) : Expr :=
  if a = .lit 0 then b else if b = .lit 0 then a else .add a b
def constFoldExpr : Expr → Expr
  | .lit n => .lit n
  | .var => .var
  | .add e₁ e₂ => foldAdd (constFoldExpr e₁) (constFoldExpr e₂)
  | .sub e₁ e₂ => .sub (constFoldExpr e₁) (constFoldExpr e₂)
  | .mul e₁ e₂ => .mul (constFoldExpr e₁) (constFoldExpr e₂)
  | .ifLe e₁ e₂ eT eE =>
    .ifLe (constFoldExpr e₁) (constFoldExpr e₂) (constFoldExpr eT) (constFoldExpr eE)
  | .choose e₁ e₂ => .choose (constFoldExpr e₁) (constFoldExpr e₂)
  | .call fn eArg => .call fn (constFoldExpr eArg)
def constFoldPass (M : Module) : Module :=
  M.map fun (fn, body) => (fn, constFoldExpr body)
def zeroBodies (M : Module) : Module := M.map fun p => (p.1, Expr.lit 0)
def evenMod : Module := [(0, .ifLe .var (.lit 0) (.lit 1) (.call 1 (.sub .var (.lit 1))))]
def oddMod : Module := [(1, .ifLe .var (.lit 0) (.lit 0) (.call 0 (.sub .var (.lit 1))))]
def evenOddProg : Module := link evenMod oddMod
def evenOddSpec : SpecEnv := fun fn =>
  if fn = 0 then
    { pre := fun x => x ≥ 0
      post := fun x v => (x % 2 = 0 ∧ v = 1) ∨ (x % 2 = 1 ∧ v = 0) }
  else if fn = 1 then
    { pre := fun x => x ≥ 0
      post := fun x v => (x % 2 = 1 ∧ v = 1) ∨ (x % 2 = 0 ∧ v = 0) }
  else
    { pre := fun _ => False, post := fun _ _ => False }
def recCaller : Module :=
  [(0, .ifLe .var (.lit 0) (.call 1 .var) (.call 0 (.sub .var (.lit 1))))]
def tenLib : Module := [(1, .lit 10)]
def recGuar : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v ≥ 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
def recAssumed : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun x => x ≤ 0, post := fun _ v => v ≥ 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
def tenActual : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun _ => True, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
def countdownMod : Module :=
  [(0, .ifLe .var (.lit 0) (.lit 0) (.call 0 (.sub .var (.lit 1))))]
def openChooseMod : Module := [(0, .choose (.lit 1) (.call 5 .var))]
def chooseLoopMod : Module := [(0, .choose (.call 0 .var) (.lit 0))]

-- lean/ToyLink/Counterexamples.lean (namespace Toy.Link.Cex)
def specSrc : Module := [(0, .call 1 (.lit 5)), (1, .var)]
def specTgt : Module := [(0, .call 1 (.lit 5)), (1, .lit 5)]
def openSpecSrc : Module := [(0, .call 1 (.lit 3)), (1, .call 5 .var)]
def openSpecTgt : Module := [(0, .call 1 (.lit 3)), (1, .call 5 (.lit 3))]
def identityImport : Module := [(5, .var)]
def callbackImport : Module := [(5, .ifLe .var (.lit 3) (.call 1 (.lit 9)) .var)]
def deadSrc : Module := [(0, .lit 42), (1, .lit 7)]
def deadTgt : Module := [(0, .lit 42)]
def termSrc : Module := [(0, .call 1 .var), (1, .lit 0)]
def divTgt : Module := [(0, .call 1 .var), (1, .call 1 .var)]
def directMod : Module := [(0, .lit 0), (1, .lit 0)]
def viaCallMod : Module := [(0, .call 1 .var), (1, .lit 0)]
def incCaller : Module := [(0, .call 1 (.lit 0))]
def incCallee : Module := [(1, .lit 11)]
def incGuar : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
def incAssumed : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun x => x ≥ 0, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
def incActual : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun _ => True, post := fun _ v => v ≥ 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
def inlSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v ≥ 1 }
  else if fn = 1 then { pre := fun _ => True, post := fun _ v => v ≥ 1 }
  else { pre := fun _ => False, post := fun _ _ => False }
def inlCaller : Module := [(0, .call 1 .var)]
def inlCallerOpt : Module := [(0, .sub (.add (.call 1 .var) (.call 1 .var)) (.lit 2))]
def inlCallee1 : Module := [(1, .lit 2)]
def inlCallee2 : Module := [(1, .lit 1)]
def inlPass (M : Module) : Module := if M = inlCaller then inlCallerOpt else M
def zSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v ≥ 0 }
  else { pre := fun _ => False, post := fun _ _ => False }
-- lean/ToyLink/Supplement.lean (namespaces: Toy.Link.Examples for deadImportTgt, scMod1, scMod2, scSpec; Toy.Link.Cex for pingMod, pongMod, pingPongSpec; Toy.Link.Unfolded for ctxRefines_sameDom_unfolded)
def deadImportTgt : Module := [(0, .ifLe (.lit 1) (.lit 0) (.call 5 .var) (.lit 1))]
def scMod1 : Module := [(0, .add (.call 1 .var) (.lit 0))]
def scMod2 : Module := [(1, .add (.lit 0) .var)]
def scSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun x v => v = x }
  else if fn = 1 then { pre := fun _ => True, post := fun x v => v = x }
  else { pre := fun _ => False, post := fun _ _ => False }
def pingMod : Module := [(0, .call 1 .var)]
def pongMod : Module := [(1, .call 0 .var)]
def pingPongSpec : SpecEnv := fun fn =>
  if fn = 0 ∨ fn = 1 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else { pre := fun _ => False, post := fun _ _ => False }
def ctxRefines_sameDom_unfolded (M M' : Module) : Prop :=
  (∀ C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) →
        (∀ fn, ¬ (C.Defines fn ∧ M'.Defines fn)) →
        ∀ entry fuel arg out, out ∈ eval fuel (link C M') entry arg →
          out ∈ eval fuel (link C M) entry arg) →
  (∀ fn, M.Defines fn ↔ M'.Defines fn)
```

`private` definitions (printed in full because a reader cannot refer to them by name):

```lean
-- lean/ToyLink/Examples.lean (namespace Toy.Link.Examples)
private def nonNegSpec : FnSpec := { pre := fun x => x ≥ 0, post := fun x v => v ≥ x }
private def allAddTenSpec : FnSpec := { pre := fun _ => True, post := fun x v => v = x + 10 }
private def geTenSpec : FnSpec := { pre := fun x => x ≥ 10, post := fun x v => v = x + 10 }
private def modA : Module := [(0, .call 1 .var)]
private def modB : Module := [(1, .choose (.lit 0) (.lit 1))]
private def modB' : Module := [(1, .lit 0)]
private def sepMod1 : Module := [(0, .add (.call 1 .var) (.lit 0))]
private def sepMod2 : Module := [(1, .add (.lit 0) .var)]
private def sepSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun x v => v = x }
  else if fn = 1 then { pre := fun _ => True, post := fun x v => v = x }
  else { pre := fun _ => False, post := fun _ _ => False }
private def expSrc : Module := [(0, .call 1 (.lit 5)), (1, .add .var (.lit 0))]
private def expTgt : Module := [(0, .call 1 (.lit 5)), (1, .var)]
private def ctrlSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun x => x ≥ 0, post := fun _ v => v ≥ 0 }
  else if fn = 1 then { pre := fun x => x ≥ 0, post := fun _ v => v ≥ 0 }
  else { pre := fun _ => False, post := fun _ _ => False }
private def ctrlCaller : Module := [(0, .add (.call 1 .var) (.lit 0))]
private def ctrlCallee1 : Module := [(1, .add .var (.lit 1))]
private def ctrlCallee2 : Module := [(1, .lit 0)]

-- lean/ToyLink/Counterexamples.lean (namespace Toy.Link.Cex)
private def const2Mod : Module := [(0, .lit 2)]
private def oneZeroMod : Module := [(1, .lit 0)]
private def ipMod1 : Module := [(0, .lit 99)]
private def ipMod2 : Module := [(0, .lit 10), (1, .call 0 .var), (2, .lit 10)]
private def ipMod2' : Module := [(0, .lit 10), (1, .call 2 .var), (2, .lit 10)]
private def ipLoopCtx : Module := [(0, .call 0 .var)]
private def ipPass (M : Module) : Module := if M = ipMod2 then ipMod2' else M
private def twoZeroSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else if fn = 1 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else { pre := fun _ => False, post := fun _ _ => False }
private def tenZeroSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
private def tenOneSpec : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun _ => True, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
private def lkCaller : Module := [(0, .call 1 .var), (2, .lit 7)]
private def lkCallee : Module := [(1, .call 2 .var), (2, .lit 10)]
private def lkGuar : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 10 }
  else if fn = 2 then { pre := fun _ => True, post := fun _ v => v = 7 }
  else { pre := fun _ => False, post := fun _ _ => False }
private def badCaller : Module := [(0, .lit 999)]
private def goodCallee : Module := [(1, .lit 10)]
private def badCallee : Module := [(1, .lit 999)]
private def preZeroCallee : Module := [(1, .ifLe .var (.lit 9) (.lit 999) (.lit 10))]
private def weakPreAssumed : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun x => x ≥ 0, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
private def weakPreActual : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun x => x ≥ 10, post := fun _ v => v = 10 }
  else { pre := fun _ => False, post := fun _ _ => False }
private def trivOneSpec : SpecEnv := fun fn =>
  if fn = 1 then { pre := fun _ => True, post := fun _ _ => True }
  else { pre := fun _ => False, post := fun _ _ => False }
private def scZero : Module := [(0, .lit 0)]
private def scOne : Module := [(1, .lit 0)]
private def scZeroBad : Module := [(0, .lit 1)]
private def scOneBad : Module := [(1, .lit 1)]
private def scZeroCalls2 : Module := [(0, .call 2 .var)]
private def threeZeroSpec : SpecEnv := fun fn =>
  if fn = 0 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else if fn = 1 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else if fn = 2 then { pre := fun _ => True, post := fun _ v => v = 0 }
  else { pre := fun _ => False, post := fun _ _ => False }
private def badBodyCompile (M : Module) : Module :=
  M.map fun (fn, _) => (fn, .lit 1)
private def dropCompile (_ : Module) : Module := []
```

The card-referenced theorems whose statements mention these `private` definitions are: `Toy.Link.Cex.cex_ag_partial_without_specsImplemented`, `Toy.Link.Cex.cex_ag_total_without_specsImplemented`, `Toy.Link.Cex.cex_ctxRefines_trans_without_second`, `Toy.Link.Cex.cex_link_congr_without_first_refines`, `Toy.Link.Cex.cex_link_congr_without_linkable`, `Toy.Link.Cex.cex_link_congr_without_second_refines`, `Toy.Link.Cex.cex_reflects_mayDiverge_without_linkable`, `Toy.Link.Cex.cex_sep_comp_ctx_without_linkable`, `Toy.Link.Cex.cex_sep_comp_without_first_verified`, `Toy.Link.Cex.cex_sep_comp_without_preservesDefines`, `Toy.Link.Cex.cex_sep_comp_without_preservesVerified`, `Toy.Link.Cex.cex_sep_comp_without_second_verified`, `Toy.Link.Cex.cex_sep_comp_without_specsImplemented`, `Toy.Link.Cex.cex_spec_refinement_without_callee_correct`, `Toy.Link.Cex.cex_spec_refinement_without_caller_verified`, `Toy.Link.Cex.cex_spec_refinement_without_linkable`, `Toy.Link.Cex.cex_spec_refinement_without_strengthensPost`, `Toy.Link.Cex.cex_spec_refinement_without_weakensPre`, `Toy.Link.Examples.nonvacuous_ctxRefines_link_congr`, `Toy.Link.Examples.nonvacuous_separate_compilation`, `Toy.Link.Examples.nonvacuous_separate_compilation_ctxRefines`, `Toy.Link.Examples.positive_control_in_place_export_optimization`, `Toy.Link.Examples.positive_control_interface_only_optimization_survives_replacement`.

In addition, four definition examples in `lean/ToyLink/Examples.lean` that no card references mention `nonNegSpec`, `allAddTenSpec` and `geTenSpec`:

```lean
theorem Toy.Link.Examples.weakensPre_pos : WeakensPre nonNegSpec allAddTenSpec
theorem Toy.Link.Examples.weakensPre_neg : ¬ WeakensPre nonNegSpec geTenSpec
theorem Toy.Link.Examples.strengthensPostUnderPre_pos : StrengthensPostUnderPre nonNegSpec allAddTenSpec
theorem Toy.Link.Examples.strengthensPostUnderPre_neg : ¬ StrengthensPostUnderPre allAddTenSpec nonNegSpec
```


### Results

#### 1. `ctx-refines-refl` (theorem)

- **Tier:** T0. Reference point: reflexivity of contextual approximation is immediate from its definition (contextual equivalence originates with J. H. Morris Jr. 1968).
- **Plain claim:** Every module contextually refines itself (`CtxRefines M M`); this is a reference point, immediate from the definition.
- **Lean:** `Toy.Link.ctxRefines_refl`; supporting declarations: `Toy.Link.Examples.cex_ctxRefines_not_symm`

```lean
theorem Toy.Link.ctxRefines_refl (M : Module) : CtxRefines M M
```

Unfolded: `∀ C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) → (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) → ∀ entry fuel arg out, out ∈ eval fuel (link C M) entry arg → out ∈ eval fuel (link C M) entry arg` (`Toy.Link.Unfolded.ctxRefines_refl_unfolded_iff`).

**Hypothesis ledger.** No hypotheses (a closed statement about concrete modules or a reference point).

- **Depth:** `definitional`. The identity map on `HasBehavior entry (link C M) fuel arg out`.
- **Non-vacuity witness:** The open module `openCallerMod` (`0` calls the import `1`) contextually refines itself. (`Toy.Link.Examples.nonvacuous_ctxRefines_refl`)
- **Prior art:**
  - James Hiram Morris Jr., 'Lambda-calculus models of programming languages', PhD thesis, Massachusetts Institute of Technology (MIT Project MAC report MAC-TR-57, 1968; the MIT DSpace record, hdl:1721.1/64850, dates the degree 1969): origin of contextual (observational) equivalence. The thesis record and secondary accounts were checked; the page of the definition was not.
- **Design question:** Which per-module guarantees compose into whole-program guarantees under linking, which apparently natural per-module notions do not, and what extra structure (fuel or a well-founded measure, spec refinement, interface-only assumptions) is genuinely needed? (Reference point.)

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_ctxRefines_refl : CtxRefines openCallerMod openCallerMod

theorem Toy.Link.Examples.cex_ctxRefines_not_symm :
    CtxRefines choose01Mod const0Mod ∧ ¬ CtxRefines const0Mod choose01Mod
```

Basis: execution (Lean kernel check) — `Toy.Link.ctxRefines_refl`, `Toy.Link.Examples.nonvacuous_ctxRefines_refl`, `Toy.Link.Examples.cex_ctxRefines_not_symm`.

#### 2. `ctx-refines-trans` (theorem)

- **Tier:** T0. Transitivity of contextual approximation; the only non-immediate step is that `Linkable C M₂` follows from `Linkable C M₁` because `CtxRefines` forces equal domains (`ctxRefines_sameDom`).
- **Plain claim:** If `CtxRefines M₁ M₂` and `CtxRefines M₂ M₃`, then `CtxRefines M₁ M₃`, with no extra domain or linkability hypothesis on the middle module `M₂`.
- **Lean:** `Toy.Link.ctxRefines_trans`

```lean
theorem Toy.Link.ctxRefines_trans {M₁ M₂ M₃ : Module}
    (h₁₂ : CtxRefines M₁ M₂) (h₂₃ : CtxRefines M₂ M₃) : CtxRefines M₁ M₃
```

Unfolded form with every `CtxRefines` expanded as in **Definitions**: `Toy.Link.Unfolded.ctxRefines_trans_unfolded_iff`. Contexts for `M₁`/`M₃` need not be stated disjoint from `M₂`: this follows from `ctxRefines_sameDom`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `CtxRefines M₁ M₂` | first refinement step; also gives `SameDom M₁ M₂`, so every context disjoint from `M₁` is disjoint from `M₂`. Tightness is immediate for any relation that is not total (the counterexample takes `M₂ = M₃`). | tight: counterexample `Toy.Link.Cex.cex_ctxRefines_trans_without_first` |
| `CtxRefines M₂ M₃` | second refinement step | tight: counterexample `Toy.Link.Cex.cex_ctxRefines_trans_without_second` |

- **Depth:** `shallow`. Derives `Linkable C M₂` via `ctxRefines_sameDom`, then chains the two outcome inclusions.
- **Non-vacuity witness:** Strict chain `choose {0,1,2}` (`choose012Mod`) ⊑ `choose {0,1}` (`choose01Mod`) ⊑ `0` (`const0Mod`). (`Toy.Link.Examples.nonvacuous_ctxRefines_trans`)
- **Prior art:**
  - Daniel Patterson and Amal Ahmed, 'The next 700 compiler correctness theorems (functional pearl)', PACMPL 3(ICFP), Article 85, 29 pp., 2019, doi:10.1145/3341689 (§5.4, p. 85:18, 'Digression: Vertical Compositionality vs. Transitivity').
  - Youngju Song, Minki Cho, Dongjoo Kim, Yonghyun Kim, Jeehoon Kang, and Chung-Kil Hur, 'CompCertM: CompCert with C-assembly linking and lightweight modular verification', PACMPL 4(POPL), Article 23, 31 pp., 2020, doi:10.1145/3371091 (§2.3, Theorem 2.1, `VerComp`: vertical composition of refinement).
  - Jérémie Koenig and Zhong Shao, 'CompCertO: compiling certified open C components', PLDI '21, pp. 1095-1109, 2021, doi:10.1145/3453483.3454097 (§3.3, Theorem 3.7: open forward simulations compose vertically).
- **Design question:** Which per-module guarantees compose into whole-program guarantees under linking, which apparently natural per-module notions do not, and what extra structure (fuel or a well-founded measure, spec refinement, interface-only assumptions) is genuinely needed?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_ctxRefines_trans :
    CtxRefines choose012Mod choose01Mod ∧ CtxRefines choose01Mod const0Mod

theorem Toy.Link.Cex.cex_ctxRefines_trans_without_first :
    ¬ CtxRefines const0Mod const1Mod ∧
    CtxRefines const1Mod const1Mod

theorem Toy.Link.Cex.cex_ctxRefines_trans_without_second :
    CtxRefines choose01Mod const0Mod ∧
    ¬ CtxRefines const0Mod const2Mod ∧
    ¬ CtxRefines choose01Mod const2Mod
```

Basis: execution (Lean kernel check) — `Toy.Link.ctxRefines_trans`, `Toy.Link.Examples.nonvacuous_ctxRefines_trans`, `Toy.Link.Cex.cex_ctxRefines_trans_without_first`, `Toy.Link.Cex.cex_ctxRefines_trans_without_second`.

#### 3. `ctx-refines-precongruence-link` (theorem)

- **Tier:** T0. Contextual approximation is a precongruence by construction: a context for `link M₁ M₂` is re-associated as a context for each component.
- **Plain claim:** If `CtxRefines M₁ M₁'`, `CtxRefines M₂ M₂'`, and `Linkable M₁ M₂`, then `CtxRefines (link M₁ M₂) (link M₁' M₂')`; `Linkable M₁' M₂'` is derived, not assumed.
- **Lean:** `Toy.Link.ctxRefines_link_congr`, `Toy.Link.ctxRefines_link_left`, `Toy.Link.ctxRefines_link_right`

```lean
theorem Toy.Link.ctxRefines_link_congr {M₁ M₁' M₂ M₂' : Module}
    (h₁ : CtxRefines M₁ M₁') (h₂ : CtxRefines M₂ M₂') (hLink : Linkable M₁ M₂) :
    CtxRefines (link M₁ M₂) (link M₁' M₂')

theorem Toy.Link.ctxRefines_link_left {M₁ M₁' M₂ : Module}
    (h₁ : CtxRefines M₁ M₁') (hLink : Linkable M₁ M₂) :
    CtxRefines (link M₁ M₂) (link M₁' M₂)

theorem Toy.Link.ctxRefines_link_right {M₁ M₂ M₂' : Module}
    (h₂ : CtxRefines M₂ M₂') (hLink : Linkable M₁ M₂) :
    CtxRefines (link M₁ M₂) (link M₁ M₂')
```

Unfolded: `Toy.Link.Unfolded.ctxRefines_link_congr_unfolded_iff`. The left and right forms are the instances with `CtxRefines M₂ M₂` and `CtxRefines M₁ M₁` supplied by reflexivity.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `CtxRefines M₁ M₁'` | contextual refinement of the left module (also gives `SameDom M₁ M₁'`) | tight: counterexample `Toy.Link.Cex.cex_link_congr_without_first_refines` |
| `CtxRefines M₂ M₂'` | contextual refinement of the right module (also gives `SameDom M₂ M₂'`) | tight: counterexample `Toy.Link.Cex.cex_link_congr_without_second_refines` |
| `Linkable M₁ M₂` | disjointness: without it, `M₁` can shadow a name that `M₂` uses internally (symbol interposition), and `CtxRefines M₂ M₂'` only quantifies over disjoint contexts | tight: counterexample `Toy.Link.Cex.cex_link_congr_without_linkable` |

- **Depth:** `shallow`. Re-associates and commutes the disjoint contexts `link C M₂'` and `link C M₁` (`lookup_link_assoc`, `lookup_link_comm`) and applies each hypothesis once.
- **Non-vacuity witness:** Caller `[(0, call 1 var)]` linked with `[(1, choose (lit 0) (lit 1))]`, refined to the same caller linked with `[(1, lit 0)]`. (`Toy.Link.Examples.nonvacuous_ctxRefines_link_congr`)
- **Prior art:**
  - Daniel Patterson and Amal Ahmed, 'The next 700 compiler correctness theorems (functional pearl)', PACMPL 3(ICFP), Article 85, 29 pp., 2019, doi:10.1145/3341689 (§5.2, p. 85:14, 'Digression: Horizontal Compositionality vs. Source-Independent Linking').
  - Youngju Song et al., 'CompCertM', PACMPL 4(POPL), Article 23, 2020, doi:10.1145/3371091 (§2.3, Theorem 2.1, `HorComp`, stated for self-related modules).
  - Jérémie Koenig and Zhong Shao, 'CompCertO', PLDI '21, pp. 1095-1109, 2021, doi:10.1145/3453483.3454097 (§3.3, Theorem 3.4: horizontal composition of simulations).
- **Design question:** Which per-module guarantees compose into whole-program guarantees under linking, which apparently natural per-module notions do not, and what extra structure (fuel or a well-founded measure, spec refinement, interface-only assumptions) is genuinely needed?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_ctxRefines_link_congr :
    CtxRefines modA modA ∧ CtxRefines modB modB' ∧ Linkable modA modB

theorem Toy.Link.Cex.cex_link_congr_without_first_refines :
    ¬ CtxRefines const0Mod const1Mod ∧
    CtxRefines oneZeroMod oneZeroMod ∧
    Linkable const0Mod oneZeroMod ∧
    ¬ CtxRefines (link const0Mod oneZeroMod) (link const1Mod oneZeroMod)

theorem Toy.Link.Cex.cex_link_congr_without_second_refines :
    CtxRefines oneZeroMod oneZeroMod ∧
    ¬ CtxRefines const0Mod const1Mod ∧
    Linkable oneZeroMod const0Mod ∧
    ¬ CtxRefines (link oneZeroMod const0Mod) (link oneZeroMod const1Mod)

theorem Toy.Link.Cex.cex_link_congr_without_linkable :
    CtxRefines ipMod1 ipMod1 ∧
    CtxRefines ipMod2 ipMod2' ∧
    ¬ Linkable ipMod1 ipMod2 ∧
    ¬ CtxRefines (link ipMod1 ipMod2) (link ipMod1 ipMod2')
```

Basis: execution (Lean kernel check) — `Toy.Link.ctxRefines_link_congr`, `Toy.Link.ctxRefines_link_left`, `Toy.Link.ctxRefines_link_right`, `Toy.Link.Examples.nonvacuous_ctxRefines_link_congr`, `Toy.Link.Cex.cex_link_congr_without_first_refines`, `Toy.Link.Cex.cex_link_congr_without_second_refines`, `Toy.Link.Cex.cex_link_congr_without_linkable`.

Basis: derived (modeling bridge) — In a language whose modules interact only through calls and returns, and whose linking is a disjoint union of symbol tables, a per-module contextual refinement can be applied to each module independently. Reasoning: the proof only re-associates disjoint contexts; it uses no property of the language beyond that. With shared memory or calling conventions, the analogous statement is a horizontal-composition theorem about simulations (CompCertO Theorem 3.4, CompCertM `HorComp`), which this package does not establish.

#### 4. `ctx-refines-forces-same-domain` (theorem)

- **Tier:** T1. Folklore (contextual equivalence presupposes a common interface) made precise: here equal domains are derived, because a call to an undefined name is observable as `undefinedCall` even with the empty context.
- **Plain claim:** If `CtxRefines M M'`, then `M` and `M'` define exactly the same function names (`SameDom M M'`); hence adding, deleting, or renaming any function breaks contextual refinement in this model.
- **Lean:** `Toy.Link.ctxRefines_sameDom`

```lean
theorem Toy.Link.ctxRefines_sameDom {M M' : Module} (h : CtxRefines M M') : SameDom M M'
```

Unfolded (`Toy.Link.Unfolded.ctxRefines_sameDom_unfolded_iff`): `(∀ C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) → (∀ fn, ¬ (C.Defines fn ∧ M'.Defines fn)) → ∀ entry fuel arg out, out ∈ eval fuel (link C M') entry arg → out ∈ eval fuel (link C M) entry arg) → ∀ fn, M.Defines fn ↔ M'.Defines fn`. The proof probes each name with the empty context at fuel `1`, where a defined name never yields `undefinedCall` and an undefined name always does (`eval_one_undefinedCall_iff`).

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `CtxRefines M M'` | the empty context at fuel `1` distinguishes a defined from an undefined name | tight: counterexample `Toy.Link.Cex.cex_delete_unused_export_not_ctxRefines` |

- **Depth:** `shallow`. Probe each name with the empty context at fuel `1` (`eval_one_undefinedCall_iff`).
- **Non-vacuity witness:** `CtxRefines choose01Mod const0Mod`. (`Toy.Link.Examples.nonvacuous_ctxRefines_sameDom`)
- **Prior art:**
  - Xavier Leroy, 'Formal verification of a realistic compiler', Communications of the ACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814 (§2.1: whole-program semantic preservation; going-wrong source behaviours relax preservation, unlike here).
- **Design question:** Which apparently natural per-module transformations (deleting unused exports, introducing helpers) fail contextual refinement, and why?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_ctxRefines_sameDom : CtxRefines choose01Mod const0Mod

theorem Toy.Link.Cex.cex_delete_unused_export_not_ctxRefines :
    ClosedModule deadSrc ∧
    ClosedModule deadTgt ∧
    EntryRefines 0 deadSrc deadTgt ∧
    EntryRefines 0 deadTgt deadSrc ∧
    ¬ SameDom deadSrc deadTgt ∧
    ¬ EntryRefines 1 deadSrc deadTgt ∧
    ¬ CtxRefines deadSrc deadTgt
```

Basis: execution (Lean kernel check) — `Toy.Link.ctxRefines_sameDom`, `Toy.Link.Examples.nonvacuous_ctxRefines_sameDom`, `Toy.Link.Cex.cex_delete_unused_export_not_ctxRefines`.

Basis: derived (modeling bridge) — For toolchains in which every function is exported, removing or renaming any function changes what some linking context can observe, so it cannot be a contextual refinement. Reasoning: the empty context already probes each name. The model differs from real linkers in two places. A missing definition is a run-time `undefinedCall` here, but typically a link-time error in practice. Real languages have non-exported (static) symbols, and this result says nothing about them.

#### 5. `cex-add-or-delete-function-not-contextual` (counterexample)

- **Tier:** T1. Instances of `ctxRefines_sameDom`; no source states these particular transformations, so labelled folklore made precise.
- **Plain claim:** Deleting an exported function that no in-module code calls, or adding an unused helper function, preserves refinement (both directions) at the designated entry `0` of a closed module, yet fails `CtxRefines` because the domain changes; this is domain observability, not a context-interaction phenomenon.
- **Lean:** `Toy.Link.Cex.cex_delete_unused_export_not_ctxRefines`, `Toy.Link.Cex.cex_add_fresh_helper_not_ctxRefines`

```lean
theorem Toy.Link.Cex.cex_delete_unused_export_not_ctxRefines :
    ClosedModule deadSrc ∧
    ClosedModule deadTgt ∧
    EntryRefines 0 deadSrc deadTgt ∧
    EntryRefines 0 deadTgt deadSrc ∧
    ¬ SameDom deadSrc deadTgt ∧
    ¬ EntryRefines 1 deadSrc deadTgt ∧
    ¬ CtxRefines deadSrc deadTgt

theorem Toy.Link.Cex.cex_add_fresh_helper_not_ctxRefines :
    EntryRefines 0 [(0, .lit 0)] [(0, .lit 0), (7, .lit 0)] ∧
    EntryRefines 0 [(0, .lit 0), (7, .lit 0)] [(0, .lit 0)] ∧
    ¬ SameDom [(0, .lit 0)] [(0, .lit 0), (7, .lit 0)] ∧
    ¬ CtxRefines [(0, .lit 0)] [(0, .lit 0), (7, .lit 0)]
```

Modules: `deadSrc = [(0, lit 42), (1, lit 7)]`, `deadTgt = [(0, lit 42)]`; the second theorem uses the literal modules `[(0, lit 0)]` and `[(0, lit 0), (7, lit 0)]`.

**Hypothesis ledger.** No hypotheses (a closed statement about concrete modules or a reference point).

- **Depth:** `definitional`. Entry-0 refinement by fuel case split; `¬ SameDom` by `decide`; `¬ CtxRefines` from `ctxRefines_sameDom`.
- **Non-vacuity witness:** `deadSrc = [(0, lit 42), (1, lit 7)]` vs `deadTgt = [(0, lit 42)]`; `[(0, lit 0)]` vs `[(0, lit 0), (7, lit 0)]`. (`Toy.Link.Cex.cex_delete_unused_export_not_ctxRefines`)
- **Positive control** (a nearby setting where the negative conclusion fails): `Toy.Link.Examples.positive_control_in_place_export_optimization`.
- **Prior art:**
  - Daniel Patterson and Amal Ahmed, 'The next 700 compiler correctness theorems (functional pearl)', PACMPL 3(ICFP), Article 85, 2019, doi:10.1145/3341689 (§2, p. 85:3: the whole-program theorem 'says absolutely nothing about what (if anything) the compiler does for partial programs').
- **Design question:** Which apparently natural per-module transformations fail contextual refinement, and is the failure due to contexts or merely to the interface?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.positive_control_in_place_export_optimization :
    CtxRefines expSrc expTgt ∧ SameDom expSrc expTgt ∧ EntryRefines 0 expSrc expTgt
```

Basis: execution (Lean kernel check) — `Toy.Link.Cex.cex_delete_unused_export_not_ctxRefines`, `Toy.Link.Cex.cex_add_fresh_helper_not_ctxRefines`, `Toy.Link.Examples.positive_control_in_place_export_optimization`.

#### 6. `ctx-refines-closed-collapse` (characterization)

- **Tier:** T1. Folklore that contexts matter only through the interactions they can have with a module, made precise for stateless first-order modules; no source states this exact equivalence.
- **Plain claim:** If the source module or the target module is closed (`ClosedModule M ∨ ClosedModule M'`), then contextual refinement coincides with standalone refinement at every entry point (`CtxRefines M M' ↔ StandaloneRefines M M'`); contexts can only matter when both modules are open.
- **Lean:** `Toy.Link.ctxRefines_iff_standaloneRefines_of_closed_source_or_target`

```lean
theorem Toy.Link.ctxRefines_iff_standaloneRefines_of_closed_source_or_target {M M' : Module}
    (hClosed : ClosedModule M ∨ ClosedModule M') :
    CtxRefines M M' ↔ StandaloneRefines M M'
```

Unfolded (`Toy.Link.Unfolded.ctxRefines_iff_standaloneRefines_of_closed_source_or_target_unfolded_iff`): `((∀ fn body, M.lookup fn = some body → body.CalleesIn M.Defines) ∨ (∀ fn body, M'.lookup fn = some body → body.CalleesIn M'.Defines)) → ((∀ C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) → (∀ fn, ¬ (C.Defines fn ∧ M'.Defines fn)) → ∀ entry fuel arg out, out ∈ eval fuel (link C M') entry arg → out ∈ eval fuel (link C M) entry arg) ↔ (∀ entry fuel arg out, out ∈ eval fuel M' entry arg → out ∈ eval fuel M entry arg))`. `ClosedModule` is syntactic: every call in every body targets a name the module defines.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `ClosedModule M ∨ ClosedModule M'` | if the target is closed, a disjoint context neither changes the target's own functions nor removes any outcome of the source other than `undefinedCall`; if the source is closed, standalone refinement forces the target never to reach an unresolved name from a defined entry, so the context cannot affect it. Either disjunct alone suffices. | tight: counterexample `Toy.Link.Cex.cex_collapse_without_closed_side` |

- **Depth:** `shallow`. Induction on fuel over the context's entries, using `eval_link_closed`, `eval_link_right_of_no_undefinedCall`, `closedModule_no_undefinedCall` and the monotonicity lemma `eval_link_superset_non_undefinedCall`.
- **Non-vacuity witness:** Open source `[(0, choose (lit 1) (call 5 var))]` and closed target `const1Mod`: standalone refinement holds, so the theorem yields `CtxRefines` (removing a branch that calls an import). Closed-source disjunct: closed source `const1Mod = [(0, lit 1)]` and syntactically open target `deadImportTgt = [(0, ifLe (lit 1) (lit 0) (call 5 var) (lit 1))]` (the external call is dead): standalone refinement holds, and so `CtxRefines` holds. (`Toy.Link.Examples.nonvacuous_collapse_closed_target`, `Toy.Link.Examples.closed_source_open_target_collapse_witness`)
- **Prior art:**
  - Gordon Stewart, Lennart Beringer, Santiago Cuellar, and Andrew W. Appel, 'Compositional CompCert', POPL '15, pp. 275-287, 2015, doi:10.1145/2676726.2676985 (§1: CompCert's original correctness statement is limited to whole programs; §3, Definition 1: contextual equivalence as equitermination under all contexts).
  - Daniel Patterson and Amal Ahmed, 'The next 700 compiler correctness theorems (functional pearl)', PACMPL 3(ICFP), Article 85, 2019, doi:10.1145/3341689 (§2, p. 85:3).
- **Design question:** When does a whole-program (closed) refinement check suffice for contextual refinement, and when is genuine context quantification needed?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_collapse_closed_target :
    ¬ ClosedModule openChooseMod ∧ ClosedModule const1Mod ∧
    (ClosedModule openChooseMod ∨ ClosedModule const1Mod) ∧
    StandaloneRefines openChooseMod const1Mod

theorem Toy.Link.Examples.closed_source_open_target_collapse_witness :
    ClosedModule const1Mod ∧ ¬ ClosedModule deadImportTgt ∧
    StandaloneRefines const1Mod deadImportTgt ∧
    CtxRefines const1Mod deadImportTgt

theorem Toy.Link.Cex.cex_collapse_without_closed_side :
    ¬ (ClosedModule openSpecSrc ∨ ClosedModule openSpecTgt) ∧
    ¬ (CtxRefines openSpecSrc openSpecTgt ↔ StandaloneRefines openSpecSrc openSpecTgt)
```

Basis: execution (Lean kernel check) — `Toy.Link.ctxRefines_iff_standaloneRefines_of_closed_source_or_target`, `Toy.Link.Examples.nonvacuous_collapse_closed_target`, `Toy.Link.Examples.closed_source_open_target_collapse_witness`, `Toy.Link.Cex.cex_collapse_without_closed_side`.

Basis: derived (modeling bridge) — For whole programs whose modules have no shared state, checking refinement at every exported entry with no context suffices for contextual refinement. Reasoning: in the model a context can only call the module or be called by it, and a closed module never calls out. With shared state, pointers, or address-taking this argument fails, because contexts can distinguish closed modules through memory.

#### 7. `cex-closed-main-entry-refinement-not-contextual` (counterexample)

- **Tier:** T1. Folklore that whole-program refinement at `main` says nothing about other exported entries, made precise; the cited sources state the general gap, not this transformation.
- **Plain claim:** Specializing an exported function `1` of a closed module to the argument `5` used by its only in-module caller preserves refinement in both directions at the designated entry `0` (with equal domains), but already fails refinement at entry `1` with no context, so it is not a contextual refinement.
- **Lean:** `Toy.Link.Cex.cex_closed_main_entry_refines_not_ctxRefines`

```lean
theorem Toy.Link.Cex.cex_closed_main_entry_refines_not_ctxRefines :
    ClosedModule specSrc ∧
    ClosedModule specTgt ∧
    SameDom specSrc specTgt ∧
    EntryRefines 0 specSrc specTgt ∧
    EntryRefines 0 specTgt specSrc ∧
    ¬ EntryRefines 1 specSrc specTgt ∧
    ¬ CtxRefines specSrc specTgt
```

Modules: `specSrc = [(0, call 1 (lit 5)), (1, var)]`, `specTgt = [(0, call 1 (lit 5)), (1, lit 5)]`; at entry `1`, fuel `1`, argument `9`, the target returns `5` and the source `9`.

**Hypothesis ledger.** No hypotheses (a closed statement about concrete modules or a reference point).

- **Depth:** `shallow`. Fuel case split for entry `0`; `decide` at entry `1`, fuel `1`; `¬ CtxRefines` via `standaloneRefines_of_ctxRefines`.
- **Non-vacuity witness:** `specSrc = [(0, call 1 (lit 5)), (1, var)]`, `specTgt = [(0, call 1 (lit 5)), (1, lit 5)]`; entry `1` on argument `9` returns `9` vs `5`. (`Toy.Link.Cex.cex_closed_main_entry_refines_not_ctxRefines`)
- **Positive control** (a nearby setting where the negative conclusion fails): `Toy.Link.Examples.positive_control_in_place_export_optimization`.
- **Prior art:**
  - F. Lockwood Morris, 'Advice on structuring compilers and proving them correct', POPL '73, pp. 144-152, 1973, doi:10.1145/512927.512941 (whole-program semantics-preservation diagram, as summarized by Patterson and Ahmed 2019, §2, pp. 85:3-85:4; primary text not checked).
  - Xavier Leroy, 'Formal verification of a realistic compiler', CACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814 (§2.1: semantic preservation for whole programs).
  - Daniel Patterson and Amal Ahmed, PACMPL 3(ICFP), Article 85, 2019, doi:10.1145/3341689 (§2, p. 85:3).
- **Design question:** Which per-module guarantees compose into whole-program guarantees under linking, and which apparently natural per-module notions do not?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.positive_control_in_place_export_optimization :
    CtxRefines expSrc expTgt ∧ SameDom expSrc expTgt ∧ EntryRefines 0 expSrc expTgt
```

Basis: execution (Lean kernel check) — `Toy.Link.Cex.cex_closed_main_entry_refines_not_ctxRefines`, `Toy.Link.Examples.positive_control_in_place_export_optimization`.

#### 8. `cex-open-specialization-standalone-refinement-not-contextual` (counterexample)

- **Tier:** T1. Folklore (refinement checked in one program, or with imports unresolved, does not survive other linking contexts) made precise with an open module whose import is supplied by the context.
- **Plain claim:** For open modules `openSpecSrc = [(0, call 1 (lit 3)), (1, call 5 var)]` and its specialization `openSpecTgt` (`1` forwards the constant `3` used by its only in-module caller to the import `5`), refinement holds in both directions at every entry when the modules run standalone, and at the designated entry `0` of the program `link identityImport _` they ship in; yet in that program calling `1(9)` separates them, a context whose import `5` calls back into `1` separates them even at entry `0`, and `CtxRefines` fails.
- **Lean:** `Toy.Link.Cex.cex_open_specialization_standalone_refines_not_ctxRefines`

```lean
theorem Toy.Link.Cex.cex_open_specialization_standalone_refines_not_ctxRefines :
    ¬ ClosedModule openSpecSrc ∧ ¬ ClosedModule openSpecTgt ∧
    SameDom openSpecSrc openSpecTgt ∧
    StandaloneRefines openSpecSrc openSpecTgt ∧
    StandaloneRefines openSpecTgt openSpecSrc ∧
    Linkable identityImport openSpecSrc ∧ Linkable identityImport openSpecTgt ∧
    EntryRefines 0 (link identityImport openSpecSrc) (link identityImport openSpecTgt) ∧
    EntryRefines 0 (link identityImport openSpecTgt) (link identityImport openSpecSrc) ∧
    ¬ EntryRefines 1 (link identityImport openSpecSrc) (link identityImport openSpecTgt) ∧
    Linkable callbackImport openSpecSrc ∧ Linkable callbackImport openSpecTgt ∧
    ¬ EntryRefines 0 (link callbackImport openSpecSrc) (link callbackImport openSpecTgt) ∧
    ¬ CtxRefines openSpecSrc openSpecTgt
```

Modules: `openSpecSrc = [(0, call 1 (lit 3)), (1, call 5 var)]`, `openSpecTgt = [(0, call 1 (lit 3)), (1, call 5 (lit 3))]`, `identityImport = [(5, var)]`, `callbackImport = [(5, ifLe var (lit 3) (call 1 (lit 9)) var)]`. Separations: in `link identityImport _`, entry `1` on `9` returns `9` (source) vs `3` (target); in `link callbackImport _`, entry `0` at fuel `5` returns `9` in the source while the target runs out of fuel.

**Hypothesis ledger.** No hypotheses (a closed statement about concrete modules or a reference point).

- **Depth:** `shallow`. Equal evaluation lists by fuel case analysis; separating behaviours by `decide` at fuel `2` (entry `1`) and fuel `5` (callback context, entry `0`).
- **Non-vacuity witness:** Identity import `[(5, var)]`: entry `1` on `9` returns `9` vs `3`. Callback import `[(5, ifLe var (lit 3) (call 1 (lit 9)) var)]`: entry `0` at fuel `5` returns `9` vs out of fuel (the specialized module loops through the callback). (`Toy.Link.Cex.cex_open_specialization_standalone_refines_not_ctxRefines`)
- **Positive control** (a nearby setting where the negative conclusion fails): `Toy.Link.Examples.collapse_closed_target_ctxRefines`.
- **Prior art:**
  - Gordon Stewart, Lennart Beringer, Santiago Cuellar, and Andrew W. Appel, 'Compositional CompCert', POPL '15, pp. 275-287, 2015, doi:10.1145/2676726.2676985 (§1; §3, Definition 1).
  - Daniel Patterson and Amal Ahmed, PACMPL 3(ICFP), Article 85, 2019, doi:10.1145/3341689 (§2, p. 85:3).
- **Design question:** Which per-module guarantees compose into whole-program guarantees under linking, which apparently natural per-module notions do not, and when is quantification over contexts genuinely needed?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.collapse_closed_target_ctxRefines : CtxRefines openChooseMod const1Mod
```

Basis: execution (Lean kernel check) — `Toy.Link.Cex.cex_open_specialization_standalone_refines_not_ctxRefines`, `Toy.Link.Examples.collapse_closed_target_ctxRefines`.

#### 9. `ctx-refines-reflects-may-divergence` (theorem)

- **Tier:** T1. Folklore (fuel-indexed refinement observes non-termination) made precise for this definition.
- **Plain claim:** If `CtxRefines M M'` and the context `C` is disjoint from `M`, then whenever `link C M'` may diverge at an entry and argument (`outOfFuel` at every fuel), so may `link C M`.
- **Lean:** `Toy.Link.ctxRefines_reflects_mayDiverge`

```lean
theorem Toy.Link.ctxRefines_reflects_mayDiverge {M M' C : Module} {entry : Fname} {arg : Int}
    (h : CtxRefines M M') (hC : Linkable C M) :
    MayDiverge (link C M') entry arg → MayDiverge (link C M) entry arg
```

Unfolded (`Toy.Link.Unfolded.ctxRefines_reflects_mayDiverge_unfolded_iff`; the `C`, `entry` and `arg` bound inside the parenthesized expansion of `CtxRefines M M'` are local to it): `(∀ C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) → (∀ fn, ¬ (C.Defines fn ∧ M'.Defines fn)) → ∀ entry fuel arg out, out ∈ eval fuel (link C M') entry arg → out ∈ eval fuel (link C M) entry arg) → (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) → (∀ fuel, Outcome.outOfFuel ∈ eval fuel (link C M') entry arg) → (∀ fuel, Outcome.outOfFuel ∈ eval fuel (link C M) entry arg)`. `Linkable C M'` is not assumed; it follows from `ctxRefines_sameDom`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `CtxRefines M M'` | outcomes, including `outOfFuel`, are compared at every fuel | tight: counterexample `Toy.Link.Cex.cex_ctxRefines_rejects_new_divergence` |
| `Linkable C M` | `CtxRefines` quantifies only over disjoint contexts; an overlapping context can shadow a name that one module uses. (`Linkable C M'` is derived from it via `ctxRefines_sameDom`.) | tight: counterexample `Toy.Link.Cex.cex_reflects_mayDiverge_without_linkable` |

- **Depth:** `definitional`. Instantiate `CtxRefines` with the outcome `outOfFuel` at each fuel.
- **Non-vacuity witness:** `chooseLoopMod = [(0, choose (call 0 var) (lit 0))]` ⊑ `selfLoopMod = [(0, call 0 var)]` with the empty context; the target may diverge. (`Toy.Link.Examples.nonvacuous_ctxRefines_reflects_mayDiverge`)
- **Prior art:**
  - Tobias Nipkow, 'Hoare logics for recursive procedures and unbounded nondeterminism', CSL 2002, LNCS 2471, pp. 103-119, Springer, 2002, doi:10.1007/3-540-45793-3_8 (§2: semantics indexed by 'at most n nested procedure invocations', the same call-depth index as the fuel here).
- **Design question:** What exactly does fuel-indexed contextual refinement observe about non-termination and call structure?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_ctxRefines_reflects_mayDiverge :
    CtxRefines chooseLoopMod selfLoopMod ∧ Linkable [] chooseLoopMod ∧
    MayDiverge (link [] selfLoopMod) 0 0

theorem Toy.Link.Cex.cex_ctxRefines_rejects_new_divergence :
    SameDom termSrc divTgt ∧
    Linkable [] termSrc ∧
    MayDiverge (link [] divTgt) 0 0 ∧
    ¬ MayDiverge (link [] termSrc) 0 0 ∧
    ¬ CtxRefines termSrc divTgt

theorem Toy.Link.Cex.cex_reflects_mayDiverge_without_linkable :
    CtxRefines ipMod2' ipMod2 ∧
    ¬ Linkable ipLoopCtx ipMod2' ∧
    MayDiverge (link ipLoopCtx ipMod2) 1 0 ∧
    ¬ MayDiverge (link ipLoopCtx ipMod2') 1 0
```

Basis: execution (Lean kernel check) — `Toy.Link.ctxRefines_reflects_mayDiverge`, `Toy.Link.Examples.nonvacuous_ctxRefines_reflects_mayDiverge`, `Toy.Link.Cex.cex_ctxRefines_rejects_new_divergence`, `Toy.Link.Cex.cex_reflects_mayDiverge_without_linkable`.

Basis: derived (modeling bridge) — A compiler correctness notion modelled on `CtxRefines` (outcomes compared at equal call-depth bound) rejects transformations that introduce non-termination. It also rejects transformations that change call depth (see `cex-ctx-refines-fixes-call-depth`). Reasoning: `outOfFuel` is compared like any other outcome. Whether that strictness is desirable for a real compiler is a design question this package does not settle.

#### 10. `cex-ctx-refines-fixes-call-depth` (counterexample)

- **Tier:** T1. Folklore consequence of lockstep fuel indexing, made precise.
- **Plain claim:** `directMod = [(0, lit 0), (1, lit 0)]` and `viaCallMod = [(0, call 1 var), (1, lit 0)]` have equal domains and evaluate identically at every entry and argument once fuel is at least `2`, yet neither contextually refines the other: `CtxRefines` forbids both adding and removing a call on a path.
- **Lean:** `Toy.Link.Cex.cex_ctxRefines_fixes_call_depth`

```lean
theorem Toy.Link.Cex.cex_ctxRefines_fixes_call_depth :
    SameDom directMod viaCallMod ∧
    (∀ fuel e a, 2 ≤ fuel → eval fuel directMod e a = eval fuel viaCallMod e a) ∧
    ¬ CtxRefines directMod viaCallMod ∧
    ¬ CtxRefines viaCallMod directMod
```

Modules: `directMod = [(0, lit 0), (1, lit 0)]`, `viaCallMod = [(0, call 1 var), (1, lit 0)]`. At fuel `1`, entry `0`: `directMod` returns `0`, `viaCallMod` runs out of fuel.

**Hypothesis ledger.** No hypotheses (a closed statement about concrete modules or a reference point).

- **Depth:** `shallow`. Evaluation at fuel `n + 2` by `simp`; separations at fuel `1` by `decide`.
- **Non-vacuity witness:** At fuel `1`, `viaCallMod` is out of fuel at entry `0` and `directMod` returns `0`. (`Toy.Link.Cex.cex_ctxRefines_fixes_call_depth`)
- **Positive control** (a nearby setting where the negative conclusion fails): `Toy.Link.Examples.passCtxRefines_pos`.
- **Prior art:**
  - Tobias Nipkow, CSL 2002, LNCS 2471, pp. 103-119, doi:10.1007/3-540-45793-3_8 (§2: call-depth-indexed semantics).
- **Design question:** What exactly does fuel-indexed contextual refinement observe, and which optimizations does it therefore exclude?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.passCtxRefines_pos : PassCtxRefines constFoldPass
```

Basis: execution (Lean kernel check) — `Toy.Link.Cex.cex_ctxRefines_fixes_call_depth`, `Toy.Link.Examples.passCtxRefines_pos`.

#### 11. `ag-partial-correctness` (theorem)

- **Tier:** T0. The rule of recursive invocation for partial correctness (Hoare 1971), proved sound by induction on call depth as in Nipkow 2002 §§2-3; mechanized in Isabelle/HOL by Nipkow and in Schirmer's Simpl.
- **Plain claim:** If every function with a satisfiable precondition is defined in `P` (`SpecsImplemented P S`) and every body satisfies its contract assuming all callees satisfy theirs (`ModuleVerifiedPartial P S S`), then `P` is partially correct for `S`, with no termination measure.
- **Lean:** `Toy.Link.ag_partial_correctness`; supporting declarations: `Toy.Link.link_ag_partial_correctness`

```lean
theorem Toy.Link.ag_partial_correctness {P : Module} {S : SpecEnv}
    (hImpl : SpecsImplemented P S)
    (hVer : ModuleVerifiedPartial P S S) :
    ProgramPartialCorrect P S
```

Unfolded (`Toy.Link.Unfolded.ag_partial_correctness_unfolded_iff`): `(∀ fn x, (S fn).pre x → P.Defines fn) → (∀ fn body, P.lookup fn = some body → ∀ x, (S fn).pre x → wpPartial S x body ((S fn).post x)) → ∀ fn fuel x out, (S fn).pre x → out ∈ eval fuel P fn x → out = .outOfFuel ∨ ∃ v, out = .val v ∧ (S fn).post x v`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `SpecsImplemented P S` | rules out `undefinedCall` at calls permitted by `S` | tight: counterexample `Toy.Link.Cex.cex_ag_partial_without_specsImplemented` |
| `ModuleVerifiedPartial P S S` | each body establishes its postcondition under `wpPartial S`, assuming callees satisfy `S` | tight: counterexample `Toy.Link.Cex.cex_ag_partial_without_moduleVerified` |

- **Depth:** `shallow`. Induction on fuel lifting the already proved one-frame soundness lemma `wpPartial_sound_evalExprWith`; about fifteen lines.
- **Non-vacuity witness:** Mutually recursive `even`/`odd` program `evenOddProg` with parity contract `evenOddSpec`. Applying the theorem yields `ProgramPartialCorrect evenOddProg evenOddSpec` (`Toy.Link.Examples.evenOddProg_partial_correct`). (`Toy.Link.Examples.nonvacuous_ag_partial_correctness`, `Toy.Link.Examples.evenOddProg_partial_correct`)
- **Prior art:**
  - C. A. R. Hoare, 'Procedures and parameters: An axiomatic approach', Symposium on Semantics of Algorithmic Languages, LNM 188, pp. 102-116, Springer, 1971, doi:10.1007/BFb0059696 (rule of recursive invocation; the page of the rule was not checked).
  - Tobias Nipkow, 'Hoare logics for recursive procedures and unbounded nondeterminism', CSL 2002, LNCS 2471, pp. 103-119, Springer, 2002, doi:10.1007/3-540-45793-3_8 (§2: semantics with 'at most n nested procedure invocations'; §3: soundness of partial correctness proved by induction on the call depth; mechanized in Isabelle/HOL; checked against the author's preprint, whose pagination differs from the LNCS pages).
  - Norbert Schirmer, 'A Sequential Imperative Programming Language: Syntax, Semantics, Hoare Logics and Verification Environment', Archive of Formal Proofs, 2008 (Simpl: sound and complete Hoare logics for partial and total correctness with mutually recursive procedures, in Isabelle/HOL).
  - Martín Abadi and Leslie Lamport, 'Conjoining specifications', ACM TOPLAS 17(3):507-535, 1995, doi:10.1145/203095.201069 (analogy only: circular assume-guarantee composition is sound for safety, where the guarantee must hold one step longer than the assumption (§2.2, p. 513; §5.2, p. 529); here the fuel decrement at calls plays that role).
- **Design question:** What extra structure (fuel or a well-founded measure) is genuinely needed for circular modular verification to compose?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_ag_partial_correctness :
    SpecsImplemented evenOddProg evenOddSpec ∧
    ModuleVerifiedPartial evenOddProg evenOddSpec evenOddSpec

theorem Toy.Link.Examples.evenOddProg_partial_correct : ProgramPartialCorrect evenOddProg evenOddSpec

theorem Toy.Link.Cex.cex_ag_partial_without_specsImplemented :
    ¬ SpecsImplemented openCallerMod twoZeroSpec ∧
    ModuleVerifiedPartial openCallerMod twoZeroSpec twoZeroSpec ∧
    ¬ ProgramPartialCorrect openCallerMod twoZeroSpec

theorem Toy.Link.Cex.cex_ag_partial_without_moduleVerified :
    SpecsImplemented const1Mod zeroOutSpec ∧
    ¬ ModuleVerifiedPartial const1Mod zeroOutSpec zeroOutSpec ∧
    ¬ ProgramPartialCorrect const1Mod zeroOutSpec

theorem Toy.Link.link_ag_partial_correctness {M₁ M₂ : Module} {S : SpecEnv}
    (hImpl : SpecsImplemented (link M₁ M₂) S)
    (hVer₁ : ModuleVerifiedPartial M₁ S S)
    (hVer₂ : ModuleVerifiedPartial M₂ S S) :
    ProgramPartialCorrect (link M₁ M₂) S
```

Basis: execution (Lean kernel check) — `Toy.Link.ag_partial_correctness`, `Toy.Link.Examples.nonvacuous_ag_partial_correctness`, `Toy.Link.Examples.evenOddProg_partial_correct`, `Toy.Link.Cex.cex_ag_partial_without_specsImplemented`, `Toy.Link.Cex.cex_ag_partial_without_moduleVerified`, `Toy.Link.link_ag_partial_correctness`.

Basis: derived (modeling bridge) — Contract-based verifiers that check each function body against its callees' contracts are sound for partial correctness of the linked program without termination measures, provided every called function with a satisfiable precondition is linked in. Reasoning: the theorem's obligations are exactly the per-body checks, and fuel induction mirrors induction on call depth. The model omits state, frames, and auxiliary variables, so this is the shape of the argument, not a soundness proof for any particular verifier.

#### 12. `cex-ag-total-circular-unsound` (counterexample)

- **Tier:** T0. The classical failure of the circular rule for termination, in the procedure-contract setting; Abadi and Lamport give the analogous failure of circular assume-guarantee for liveness.
- **Plain claim:** The closed module `selfLoopMod = [(0, call 0 var)]` implements `zeroOutSpec` and satisfies the circular partial-correctness obligation (verified to return `0` assuming it returns `0`), yet is not totally correct.
- **Lean:** `Toy.Link.Cex.cex_ag_total_unsound_without_measure`

```lean
theorem Toy.Link.Cex.cex_ag_total_unsound_without_measure :
    ClosedModule selfLoopMod ∧
    SpecsImplemented selfLoopMod zeroOutSpec ∧
    ModuleVerifiedPartial selfLoopMod zeroOutSpec zeroOutSpec ∧
    (zeroOutSpec 0).pre 0 ∧
    (∃ v, (zeroOutSpec 0).post 0 v) ∧
    ¬ ProgramTotalCorrect selfLoopMod zeroOutSpec
```

Module and contract: `selfLoopMod = [(0, call 0 var)]`; `zeroOutSpec 0 = {pre := True, post := fun _ v => v = 0}` (unsatisfiable precondition elsewhere). `eval fuel selfLoopMod 0 0 = [outOfFuel]` for every fuel.

**Hypothesis ledger.** No hypotheses (a closed statement about concrete modules or a reference point).

- **Depth:** `shallow`. `eval fuel selfLoopMod 0 0 = [outOfFuel]` for every fuel, by induction.
- **Non-vacuity witness:** `selfLoopMod` with `zeroOutSpec` (`pre = True`, `post = (v = 0)`). (`Toy.Link.Cex.cex_ag_total_unsound_without_measure`)
- **Positive control** (a nearby setting where the negative conclusion fails): `Toy.Link.Examples.positive_control_ag_total_with_wf_measure`.
- **Prior art:**
  - Martín Abadi and Leslie Lamport, 'Conjoining specifications', ACM TOPLAS 17(3):507-535, 1995, doi:10.1145/203095.201069 (§2.2, 'Composing Open Systems', pp. 510-513: circular composition succeeds for the safety example 'c always equals 0' and fails for the liveness example 'c eventually equals 1'; an analogy in TLA over reactive systems, not a statement about procedures).
- **Design question:** What extra structure (a well-founded measure) is genuinely needed for circular modular verification of total correctness?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.positive_control_ag_total_with_wf_measure :
    WellFounded Nat.lt ∧
    SpecsImplemented countdownMod zeroOutSpec ∧
    ModuleVerifiedTotal Nat.lt (fun _ x => x.toNat) countdownMod zeroOutSpec zeroOutSpec ∧
    ProgramTotalCorrect countdownMod zeroOutSpec
```

Basis: execution (Lean kernel check) — `Toy.Link.Cex.cex_ag_total_unsound_without_measure`, `Toy.Link.Examples.positive_control_ag_total_with_wf_measure`.

#### 13. `ag-total-correctness-wf-measure` (theorem)

- **Tier:** T0. Soundness of the total-correctness rule for mutually recursive procedures with a well-founded relation (Nipkow 2002, §§4-5), here with finite branching.
- **Plain claim:** If `rel` is well-founded, `P` implements all satisfiable preconditions of `S`, and every body establishes its contract in `wpCallDec rel μ S` (every call strictly decreases the call measure `μ` and meets the callee precondition), then `P` is totally correct for `S` (a uniform finite fuel bound per argument).
- **Lean:** `Toy.Link.ag_total_correctness_of_wf_call_measure`; supporting declarations: `Toy.Link.link_ag_total_correctness_of_wf_call_measure`, `Toy.Link.Cex.independent_measures_do_not_compose`, `Toy.Link.Examples.empty_module_ag_total`

```lean
theorem Toy.Link.ag_total_correctness_of_wf_call_measure {α : Type} {rel : α → α → Prop}
    {μ : Fname → Int → α} {P : Module} {S : SpecEnv}
    (hwf : WellFounded rel)
    (hImpl : SpecsImplemented P S)
    (hVer : ModuleVerifiedTotal rel μ P S S) :
    ProgramTotalCorrect P S
```

Unfolded (`Toy.Link.Unfolded.ag_total_correctness_of_wf_call_measure_unfolded_iff`): `WellFounded rel → (∀ fn x, (S fn).pre x → P.Defines fn) → (∀ fn body, P.lookup fn = some body → ∀ x, (S fn).pre x → wpCallDec rel μ S (μ fn x) x body ((S fn).post x)) → ∀ fn x, (S fn).pre x → ∃ fuel, ∀ out, out ∈ eval fuel P fn x → ∃ v, out = .val v ∧ (S fn).post x v`. The measure `μ fn x` depends only on the callee name and its argument and is shared by all functions of `P`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `WellFounded rel` | forbids infinite descending call chains | tight: counterexample `Toy.Link.Cex.cex_ag_total_without_wf` |
| `SpecsImplemented P S` | rules out `undefinedCall` at calls permitted by `S` | tight: counterexample `Toy.Link.Cex.cex_ag_total_without_specsImplemented` |
| `ModuleVerifiedTotal rel μ P S S` | each body meets its postcondition while every call decreases `μ` and meets the callee precondition | tight: counterexample `Toy.Link.Cex.cex_ag_total_without_moduleVerifiedTotal` |

- **Depth:** `substantive`. Well-founded induction on `μ fn x` with an inner structural induction on bodies, fuel stabilization (`eval_stabilizes_of_no_outOfFuel`) and a maximum over finitely many branches.
- **Non-vacuity witness:** `evenOddProg` with `WellFounded Nat.lt` and `μ _ x := x.toNat`. Applying the theorem yields `ProgramTotalCorrect evenOddProg evenOddSpec` (`Toy.Link.Examples.evenOddProg_total_correct`); the empty module with the unsatisfiable `falseSpec` is a degenerate instance (`Toy.Link.Examples.empty_module_ag_total`). (`Toy.Link.Examples.nonvacuous_ag_total_correctness`, `Toy.Link.Examples.evenOddProg_total_correct`)
- **Prior art:**
  - Tobias Nipkow, 'Hoare logics for recursive procedures and unbounded nondeterminism', CSL 2002, LNCS 2471, pp. 103-119, Springer, 2002, doi:10.1007/3-540-45793-3_8 (§4: total correctness with well-founded relations; §5.2: CALL rule with a well-founded relation for mutually recursive procedures; mechanized in Isabelle/HOL).
  - K. R. Apt and G. D. Plotkin, 'Countable nondeterminism and random assignment', Journal of the ACM 33(4):724-767, 1986, doi:10.1145/6490.6494 (countable nondeterminism breaks continuity; total-correctness proofs need countable ordinals).
  - Norbert Schirmer, Simpl, Archive of Formal Proofs, 2008 (total-correctness Hoare logic with recursive procedures and unbounded nondeterminism, in Isabelle/HOL).
- **Design question:** What extra structure (a well-founded measure) is genuinely needed for circular modular verification of total correctness?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_ag_total_correctness :
    WellFounded Nat.lt ∧
    SpecsImplemented evenOddProg evenOddSpec ∧
    ModuleVerifiedTotal Nat.lt (fun _ x => x.toNat) evenOddProg evenOddSpec evenOddSpec

theorem Toy.Link.Examples.evenOddProg_total_correct : ProgramTotalCorrect evenOddProg evenOddSpec

theorem Toy.Link.Cex.cex_ag_total_without_wf :
    ¬ WellFounded (fun _ _ : Unit => True) ∧
    SpecsImplemented selfLoopMod zeroOutSpec ∧
    ModuleVerifiedTotal (fun _ _ : Unit => True) (fun _ _ => ()) selfLoopMod zeroOutSpec zeroOutSpec ∧
    ¬ ProgramTotalCorrect selfLoopMod zeroOutSpec

theorem Toy.Link.Cex.cex_ag_total_without_specsImplemented :
    WellFounded Nat.lt ∧
    ¬ SpecsImplemented openCallerMod twoZeroSpec ∧
    ModuleVerifiedTotal Nat.lt (fun fn _ => if fn = 0 then 1 else 0)
      openCallerMod twoZeroSpec twoZeroSpec ∧
    ¬ ProgramTotalCorrect openCallerMod twoZeroSpec

theorem Toy.Link.Cex.cex_ag_total_without_moduleVerifiedTotal :
    WellFounded Nat.lt ∧
    SpecsImplemented selfLoopMod zeroOutSpec ∧
    ¬ ModuleVerifiedTotal Nat.lt (fun _ _ => 0) selfLoopMod zeroOutSpec zeroOutSpec ∧
    ¬ ProgramTotalCorrect selfLoopMod zeroOutSpec

theorem Toy.Link.link_ag_total_correctness_of_wf_call_measure {α : Type} {rel : α → α → Prop}
    {μ : Fname → Int → α} {M₁ M₂ : Module} {S : SpecEnv}
    (hwf : WellFounded rel)
    (hImpl : SpecsImplemented (link M₁ M₂) S)
    (hVer₁ : ModuleVerifiedTotal rel μ M₁ S S)
    (hVer₂ : ModuleVerifiedTotal rel μ M₂ S S) :
    ProgramTotalCorrect (link M₁ M₂) S

theorem Toy.Link.Cex.independent_measures_do_not_compose :
    Linkable pingMod pongMod ∧
    SpecsImplemented (link pingMod pongMod) pingPongSpec ∧
    WellFounded Nat.lt ∧
    ModuleVerifiedTotal Nat.lt (fun fn _ => if fn = 0 then 1 else 0)
      pingMod pingPongSpec pingPongSpec ∧
    ModuleVerifiedTotal Nat.lt (fun fn _ => if fn = 1 then 1 else 0)
      pongMod pingPongSpec pingPongSpec ∧
    ¬ ProgramTotalCorrect (link pingMod pongMod) pingPongSpec

theorem Toy.Link.Examples.empty_module_ag_total :
    ProgramTotalCorrect ([] : Module) falseSpec
```

Basis: execution (Lean kernel check) — `Toy.Link.ag_total_correctness_of_wf_call_measure`, `Toy.Link.Examples.nonvacuous_ag_total_correctness`, `Toy.Link.Examples.evenOddProg_total_correct`, `Toy.Link.Cex.cex_ag_total_without_wf`, `Toy.Link.Cex.cex_ag_total_without_specsImplemented`, `Toy.Link.Cex.cex_ag_total_without_moduleVerifiedTotal`, `Toy.Link.link_ag_total_correctness_of_wf_call_measure`, `Toy.Link.Cex.independent_measures_do_not_compose`, `Toy.Link.Examples.empty_module_ag_total`.

Basis: derived (modeling bridge) — For termination, modular verifiers need one global well-founded measure, or an equivalent agreement, covering every call across module boundaries. Reasoning: the theorem requires a single `(rel, μ)` for the whole program, and `Toy.Link.Cex.independent_measures_do_not_compose` shows two separately verified modules with their own measures can loop forever when linked.

#### 14. `spec-refinement-link-composition` (theorem)

- **Tier:** T0. The rule of recursive invocation for the caller's own functions combined with the consequence rule (refinement-calculus ordering) for imports.
- **Plain claim:** If a caller module `M` is verified for its guarantee `G` assuming `G` for calls to its own functions and `S` for all other calls (`ModuleVerifiedPartial M (mixEnv M G S) G`), and a disjoint callee module `N` is partially correct for a spec `S'` that refines `S` at every name `M` does not define (weaker precondition, postcondition strengthened under the precondition), then every function of `M` is partially correct for `G` in `link M N`; `M` may be recursive.
- **Lean:** `Toy.Link.verified_recursive_caller_links_with_refined_callee`; supporting declarations: `Toy.Link.verified_flat_caller_links_with_refined_callee`, `Toy.Link.caller_spec_unsat_on_own_symbols`, `Toy.Link.Cex.flat_spec_refinement_inapplicable_to_recursive_caller`

```lean
theorem Toy.Link.verified_recursive_caller_links_with_refined_callee
    {M N : Module} {S S' G : SpecEnv}
    (hLink : Linkable M N)
    (hVerM : ModuleVerifiedPartial M (mixEnv M G S) G)
    (hSatN : ProgramPartialCorrect N S')
    (hWeak : ∀ g, ¬ M.Defines g → WeakensPre (S g) (S' g))
    (hStrong : ∀ g, ¬ M.Defines g → StrengthensPostUnderPre (S g) (S' g)) :
    ∀ f, M.Defines f → FnPartialCorrect (link M N) f (G f)
```

Unfolded (`Toy.Link.Unfolded.verified_recursive_caller_links_with_refined_callee_unfolded_iff`): `(∀ fn, ¬ (M.Defines fn ∧ N.Defines fn)) → (∀ fn body, M.lookup fn = some body → ∀ x, (G fn).pre x → wpPartial (fun g => if M.Defines g then G g else S g) x body ((G fn).post x)) → (∀ fn fuel x out, (S' fn).pre x → out ∈ eval fuel N fn x → out = .outOfFuel ∨ ∃ v, out = .val v ∧ (S' fn).post x v) → (∀ g, ¬ M.Defines g → ∀ x, (S g).pre x → (S' g).pre x) → (∀ g, ¬ M.Defines g → ∀ x v, (S g).pre x → (S' g).post x v → (S g).post x v) → ∀ f, M.Defines f → ∀ fuel x out, (G f).pre x → out ∈ eval fuel (link M N) f x → out = .outOfFuel ∨ ∃ v, out = .val v ∧ (G f).post x v`. The flat variant `verified_flat_caller_links_with_refined_callee` (assumption `S` for every call, refinement at every name) is derived from it; its hypotheses force `(S f).pre` to be unsatisfiable at every `f` that `M` defines (`caller_spec_unsat_on_own_symbols`), so it can never apply to a caller that calls itself (`Cex.flat_spec_refinement_inapplicable_to_recursive_caller`).

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `Linkable M N` | without disjointness, a call inside `N` can be captured by `M`'s definition of the same name (symbol interposition) | tight: counterexample `Toy.Link.Cex.cex_spec_refinement_without_linkable` |
| `ModuleVerifiedPartial M (mixEnv M G S) G` | `M`'s bodies satisfy `G`, assuming `G` for internal calls and `S` for external calls | tight: counterexample `Toy.Link.Cex.cex_spec_refinement_without_caller_verified` |
| `ProgramPartialCorrect N S'` | `N` satisfies `S'` on its own (and therefore implements every name with a satisfiable `S'` precondition) | tight: counterexample `Toy.Link.Cex.cex_spec_refinement_without_callee_correct` |
| `∀ g, ¬ M.Defines g → WeakensPre (S g) (S' g)` | every external call argument allowed by the assumed precondition is allowed by the callee's precondition | tight: counterexample `Toy.Link.Cex.cex_spec_refinement_without_weakensPre` |
| `∀ g, ¬ M.Defines g → StrengthensPostUnderPre (S g) (S' g)` | every result the callee may return (under the assumed precondition) satisfies the assumed postcondition | tight: counterexample `Toy.Link.Cex.cex_spec_refinement_without_strengthensPost` |

- **Depth:** `shallow`. Induction on fuel; internal calls use the induction hypothesis at `G`, external calls use `eval_link_right_of_no_undefinedCall` and the refinement of `S` by `S'`; one-frame soundness `wpPartial_sound_evalExprWith`.
- **Non-vacuity witness:** Recursive caller `recCaller = [(0, ifLe var (lit 0) (call 1 var) (call 0 (sub var (lit 1))))]` (reachable internal call to `0`, external call to `1`) with guarantee `v ≥ 10`, assuming `1` returns at least `10` on `x ≤ 0`, linked with `tenLib = [(1, lit 10)]` satisfying the strictly stronger spec `pre True, post v = 10`. Applying the theorem yields `FnPartialCorrect (link recCaller tenLib) 0 (recGuar 0)` (`Toy.Link.Examples.positive_control_spec_refinement_link`). (`Toy.Link.Examples.nonvacuous_recursive_spec_refinement`, `Toy.Link.Examples.positive_control_spec_refinement_link`)
- **Prior art:**
  - C. A. R. Hoare, 'Procedures and parameters: An axiomatic approach', LNM 188, pp. 102-116, Springer, 1971, doi:10.1007/BFb0059696 (rule of recursive invocation; the page of the rule was not checked).
  - C. A. R. Hoare, 'An axiomatic basis for computer programming', Communications of the ACM 12(10):576-580, 1969, doi:10.1145/363235.363259 (rule of consequence).
  - Carroll Morgan, Programming from Specifications, 2nd ed., Prentice Hall International, 1994 (checked in the author's 1998 reissue): Law 1.2 'weaken precondition' and Law 5.1 'strengthen postcondition' (if pre[w\w0] ∧ post' ⇛ post then w:[pre, post] ⊑ w:[pre, post']), which is exactly the `WeakensPre` / `StrengthensPostUnderPre` ordering.
  - Barbara H. Liskov and Jeannette M. Wing, 'A behavioral notion of subtyping', ACM TOPLAS 16(6):1811-1841, 1994, doi:10.1145/197320.197383 (Fig. 4, p. 1823: precondition rule and an unconditional postcondition rule, a stricter precursor of the ordering used here).
- **Design question:** What spec-refinement structure lets a verified caller, including one with internal recursive calls, be linked with any callee implementation satisfying a refining spec?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_recursive_spec_refinement :
    Linkable recCaller tenLib ∧
    ModuleVerifiedPartial recCaller (mixEnv recCaller recGuar recAssumed) recGuar ∧
    ProgramPartialCorrect tenLib tenActual ∧
    (∀ g, ¬ recCaller.Defines g → WeakensPre (recAssumed g) (tenActual g)) ∧
    (∀ g, ¬ recCaller.Defines g → StrengthensPostUnderPre (recAssumed g) (tenActual g)) ∧
    ¬ WeakensPre (tenActual 1) (recAssumed 1) ∧
    ¬ StrengthensPostUnderPre (tenActual 1) (recAssumed 1)

theorem Toy.Link.Examples.positive_control_spec_refinement_link :
    ∀ f, recCaller.Defines f → FnPartialCorrect (link recCaller tenLib) f (recGuar f)

theorem Toy.Link.Cex.cex_spec_refinement_without_linkable :
    ¬ Linkable lkCaller lkCallee ∧
    ModuleVerifiedPartial lkCaller (mixEnv lkCaller lkGuar tenOneSpec) lkGuar ∧
    ProgramPartialCorrect lkCallee tenOneSpec ∧
    (∀ g, ¬ lkCaller.Defines g → WeakensPre (tenOneSpec g) (tenOneSpec g)) ∧
    (∀ g, ¬ lkCaller.Defines g → StrengthensPostUnderPre (tenOneSpec g) (tenOneSpec g)) ∧
    ¬ (∀ f, lkCaller.Defines f → FnPartialCorrect (link lkCaller lkCallee) f (lkGuar f))

theorem Toy.Link.Cex.cex_spec_refinement_without_caller_verified :
    Linkable badCaller goodCallee ∧
    ¬ ModuleVerifiedPartial badCaller (mixEnv badCaller tenZeroSpec tenOneSpec) tenZeroSpec ∧
    ProgramPartialCorrect goodCallee tenOneSpec ∧
    (∀ g, ¬ badCaller.Defines g → WeakensPre (tenOneSpec g) (tenOneSpec g)) ∧
    (∀ g, ¬ badCaller.Defines g → StrengthensPostUnderPre (tenOneSpec g) (tenOneSpec g)) ∧
    ¬ (∀ f, badCaller.Defines f → FnPartialCorrect (link badCaller goodCallee) f (tenZeroSpec f))

theorem Toy.Link.Cex.cex_spec_refinement_without_callee_correct :
    Linkable openCallerMod badCallee ∧
    ModuleVerifiedPartial openCallerMod (mixEnv openCallerMod tenZeroSpec tenOneSpec)
      tenZeroSpec ∧
    ¬ ProgramPartialCorrect badCallee tenOneSpec ∧
    (∀ g, ¬ openCallerMod.Defines g → WeakensPre (tenOneSpec g) (tenOneSpec g)) ∧
    (∀ g, ¬ openCallerMod.Defines g → StrengthensPostUnderPre (tenOneSpec g) (tenOneSpec g)) ∧
    ¬ (∀ f, openCallerMod.Defines f →
        FnPartialCorrect (link openCallerMod badCallee) f (tenZeroSpec f))

theorem Toy.Link.Cex.cex_spec_refinement_without_weakensPre :
    Linkable incCaller preZeroCallee ∧
    ModuleVerifiedPartial incCaller (mixEnv incCaller tenZeroSpec weakPreAssumed) tenZeroSpec ∧
    ProgramPartialCorrect preZeroCallee weakPreActual ∧
    ¬ (∀ g, ¬ incCaller.Defines g → WeakensPre (weakPreAssumed g) (weakPreActual g)) ∧
    (∀ g, ¬ incCaller.Defines g →
        StrengthensPostUnderPre (weakPreAssumed g) (weakPreActual g)) ∧
    ¬ (∀ f, incCaller.Defines f →
        FnPartialCorrect (link incCaller preZeroCallee) f (tenZeroSpec f))

theorem Toy.Link.Cex.cex_spec_refinement_without_strengthensPost :
    Linkable openCallerMod badCallee ∧
    ModuleVerifiedPartial openCallerMod (mixEnv openCallerMod tenZeroSpec tenOneSpec)
      tenZeroSpec ∧
    ProgramPartialCorrect badCallee trivOneSpec ∧
    (∀ g, ¬ openCallerMod.Defines g → WeakensPre (tenOneSpec g) (trivOneSpec g)) ∧
    ¬ (∀ g, ¬ openCallerMod.Defines g →
        StrengthensPostUnderPre (tenOneSpec g) (trivOneSpec g)) ∧
    ¬ (∀ f, openCallerMod.Defines f →
        FnPartialCorrect (link openCallerMod badCallee) f (tenZeroSpec f))

theorem Toy.Link.verified_flat_caller_links_with_refined_callee {M N : Module} {S S' G : SpecEnv}
    (hLink : Linkable M N)
    (hVerM : ModuleVerifiedPartial M S G)
    (hSatN : ProgramPartialCorrect N S')
    (hWeak : ∀ g, WeakensPre (S g) (S' g))
    (hStrong : ∀ g, StrengthensPostUnderPre (S g) (S' g)) :
    ∀ f, M.Defines f → FnPartialCorrect (link M N) f (G f)

theorem Toy.Link.caller_spec_unsat_on_own_symbols {M N : Module} {S S' : SpecEnv}
    (hLink : Linkable M N) (hSatN : ProgramPartialCorrect N S')
    (hWeak : ∀ g, WeakensPre (S g) (S' g)) :
    ∀ f, M.Defines f → ∀ x, ¬ (S f).pre x

theorem Toy.Link.Cex.flat_spec_refinement_inapplicable_to_recursive_caller :
    ∀ (N : Module) (S S' : SpecEnv),
      ¬ (Linkable recCaller N ∧ ModuleVerifiedPartial recCaller S recGuar ∧
         ProgramPartialCorrect N S' ∧ (∀ g, WeakensPre (S g) (S' g)))
```

Basis: execution (Lean kernel check) — `Toy.Link.verified_recursive_caller_links_with_refined_callee`, `Toy.Link.Examples.nonvacuous_recursive_spec_refinement`, `Toy.Link.Examples.positive_control_spec_refinement_link`, `Toy.Link.Cex.cex_spec_refinement_without_linkable`, `Toy.Link.Cex.cex_spec_refinement_without_caller_verified`, `Toy.Link.Cex.cex_spec_refinement_without_callee_correct`, `Toy.Link.Cex.cex_spec_refinement_without_weakensPre`, `Toy.Link.Cex.cex_spec_refinement_without_strengthensPost`, `Toy.Link.verified_flat_caller_links_with_refined_callee`, `Toy.Link.caller_spec_unsat_on_own_symbols`, `Toy.Link.Cex.flat_spec_refinement_inapplicable_to_recursive_caller`.

Basis: derived (modeling bridge) — A caller verified against an interface for its imports may be linked with any implementation that satisfies a refining contract (weaker precondition, stronger postcondition under the assumed precondition) at those imports, provided the implementation is correct on its own and does not call back into the caller. Reasoning: these are exactly the hypotheses of the theorem, and each is shown necessary by a counterexample.

#### 15. `cex-spec-refinement-incomparable-callee` (counterexample)

- **Tier:** T0. Direct instance showing that a callee spec better on the precondition side but not refining on the postcondition side does not protect the caller.
- **Plain claim:** The caller `incCaller = [(0, call 1 (lit 0))]`, verified for `v = 10` assuming `1` satisfies `pre x ≥ 0, post v = 10`, linked with `incCallee = [(1, lit 11)]`, which satisfies the incomparable spec `pre True, post v ≥ 10` (the precondition side refines, the postcondition side does not, and the assumed spec does not refine it either), violates the caller's guarantee.
- **Lean:** `Toy.Link.Cex.cex_link_fails_for_incomparable_callee_spec`

```lean
theorem Toy.Link.Cex.cex_link_fails_for_incomparable_callee_spec :
    Linkable incCaller incCallee ∧
    ModuleVerifiedPartial incCaller (mixEnv incCaller incGuar incAssumed) incGuar ∧
    ProgramPartialCorrect incCallee incActual ∧
    (∀ g, ¬ incCaller.Defines g → WeakensPre (incAssumed g) (incActual g)) ∧
    ¬ StrengthensPostUnderPre (incAssumed 1) (incActual 1) ∧
    ¬ WeakensPre (incActual 1) (incAssumed 1) ∧
    ¬ (∀ f, incCaller.Defines f → FnPartialCorrect (link incCaller incCallee) f (incGuar f))
```

Modules and specs: `incCaller = [(0, call 1 (lit 0))]`, `incCallee = [(1, lit 11)]`; guarantee `incGuar 0 = {pre := True, post := v = 10}`; assumed `incAssumed 1 = {pre := x ≥ 0, post := v = 10}`; actual `incActual 1 = {pre := True, post := v ≥ 10}`.

**Hypothesis ledger.** No hypotheses (a closed statement about concrete modules or a reference point).

- **Depth:** `shallow`. Concrete evaluation at fuel `2` by `decide`; spec facts by `simp`.
- **Non-vacuity witness:** `link incCaller incCallee` returns `11` at entry `0`. (`Toy.Link.Cex.cex_link_fails_for_incomparable_callee_spec`)
- **Positive control** (a nearby setting where the negative conclusion fails): `Toy.Link.Examples.positive_control_spec_refinement_link`.
- **Prior art:**
  - Carroll Morgan, Programming from Specifications, 2nd ed., Prentice Hall International, 1994 (Law 5.1 'strengthen postcondition').
  - Barbara H. Liskov and Jeannette M. Wing, ACM TOPLAS 16(6):1811-1841, 1994, doi:10.1145/197320.197383 (Fig. 4, p. 1823, postcondition rule).
- **Design question:** Which spec relations between assumed and actual callee specs are needed for linking a verified caller?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.positive_control_spec_refinement_link :
    ∀ f, recCaller.Defines f → FnPartialCorrect (link recCaller tenLib) f (recGuar f)
```

Basis: execution (Lean kernel check) — `Toy.Link.Cex.cex_link_fails_for_incomparable_callee_spec`, `Toy.Link.Examples.positive_control_spec_refinement_link`.

#### 16. `separate-compilation-preserves-verifiability` (theorem)

- **Tier:** T0. A corollary of the assume-guarantee rule (`ag-partial-correctness`) applied to compiled modules: specification preservation in the sense of Leroy 2009, §2.1, property (4), at module granularity; compare certificate translation (Barthe et al. 2009). Semantic separate-compilation results (CompCertM, CompCertO, Patterson and Ahmed) are a contrast, not the source.
- **Plain claim:** If `M₁` and `M₂` are verified against the interface `S`, `link M₁ M₂` implements `S`, and a per-module pass `compile` preserves verification against `S` (`PreservesVerifiedPartial`) and keeps every defined name (`PreservesDefines`), then the separately compiled linked program `link (compile M₁) (compile M₂)` is partially correct for `S`; no behavioural relation to the source is claimed.
- **Lean:** `Toy.Link.separate_compilation_partial_correct_of_preserves_verified`; supporting declarations: `Toy.Link.Cex.inlPass_not_preservesVerified`

```lean
theorem Toy.Link.separate_compilation_partial_correct_of_preserves_verified
    {M₁ M₂ : Module} {S : SpecEnv} {compile : Module → Module}
    (hVer₁ : ModuleVerifiedPartial M₁ S S)
    (hVer₂ : ModuleVerifiedPartial M₂ S S)
    (hImpl : SpecsImplemented (link M₁ M₂) S)
    (hPresVer : PreservesVerifiedPartial compile S)
    (hPresDef : PreservesDefines compile) :
    ProgramPartialCorrect (link (compile M₁) (compile M₂)) S
```

Unfolded (`Toy.Link.Unfolded.separate_compilation_partial_correct_of_preserves_verified_unfolded_iff`): the two module obligations `∀ fn body, Mᵢ.lookup fn = some body → ∀ x, (S fn).pre x → wpPartial S x body ((S fn).post x)`, `∀ fn x, (S fn).pre x → (link M₁ M₂).Defines fn`, `∀ M, (module obligation for M) → (module obligation for compile M)`, `∀ M fn, M.Defines fn → (compile M).Defines fn`; conclusion `∀ fn fuel x out, (S fn).pre x → out ∈ eval fuel (link (compile M₁) (compile M₂)) fn x → out = .outOfFuel ∨ ∃ v, out = .val v ∧ (S fn).post x v`. The proof is `link_ag_partial_correctness` applied to `compile M₁`, `compile M₂`.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `ModuleVerifiedPartial M₁ S S` | first module verified against `S` before compilation | tight: counterexample `Toy.Link.Cex.cex_sep_comp_without_first_verified` |
| `ModuleVerifiedPartial M₂ S S` | second module verified against `S` before compilation | tight: counterexample `Toy.Link.Cex.cex_sep_comp_without_second_verified` |
| `SpecsImplemented (link M₁ M₂) S` | every name with a satisfiable precondition exists in the source link | tight: counterexample `Toy.Link.Cex.cex_sep_comp_without_specsImplemented` |
| `PreservesVerifiedPartial compile S` | the pass maps `S`-verified modules to `S`-verified modules, looking at no other module. Only its instances at `M₁` and `M₂` are used; the universal pass property is stronger than needed. | tight: counterexample `Toy.Link.Cex.cex_sep_comp_without_preservesVerified` |
| `PreservesDefines compile` | the pass keeps the names that `SpecsImplemented` needs. Only its instances at `M₁` and `M₂` are used. | tight: counterexample `Toy.Link.Cex.cex_sep_comp_without_preservesDefines` |

- **Depth:** `definitional`. Definitional given `ag_partial_correctness`: it is `link_ag_partial_correctness` applied to `compile M₁` and `compile M₂`, with the two pass hypotheses producing its premises.
- **Non-vacuity witness:** `sepMod1 = [(0, add (call 1 var) (lit 0))]` and `sepMod2 = [(1, add (lit 0) var)]`, verified against `sepSpec` (functions `0` and `1` accept every argument and return it; every other name has an unsatisfiable precondition), compiled by the non-identity constant folder `constFoldPass` (which rewrites `e + 0` and `0 + e` to `e`). The three helper definitions are `private` in the Lean source and are printed in REPORT.md. (`Toy.Link.Examples.nonvacuous_separate_compilation`)
- **Prior art:**
  - Xavier Leroy, 'Formal verification of a realistic compiler', Communications of the ACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814 (§2.1, property (4): the compiler preserves the fact that the source satisfies a specification; stated for whole programs).
  - Gilles Barthe, Benjamin Grégoire, César Kunz, and Tamara Rezk, 'Certificate translation for optimizing compilers', ACM TOPLAS 31(5), 45 pp., 2009, doi:10.1145/1538917.1538919 (transforming proofs of source-program properties into certificates for the compiled program).
  - Youngju Song et al., 'CompCertM', PACMPL 4(POPL), Article 23, 2020, doi:10.1145/3371091 (§4.2, verification against specification modules; contrast: semantic refinement, not established here).
- **Design question:** What does separate compilation preserve when passes are only required to preserve per-module verifiability against interface specs?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_separate_compilation :
    constFoldPass sepMod1 ≠ sepMod1 ∧
    ModuleVerifiedPartial sepMod1 sepSpec sepSpec ∧
    ModuleVerifiedPartial sepMod2 sepSpec sepSpec ∧
    SpecsImplemented (link sepMod1 sepMod2) sepSpec ∧
    PreservesVerifiedPartial constFoldPass sepSpec ∧
    PreservesDefines constFoldPass

theorem Toy.Link.Cex.cex_sep_comp_without_first_verified :
    ¬ ModuleVerifiedPartial scZeroBad twoZeroSpec twoZeroSpec ∧
    ModuleVerifiedPartial scOne twoZeroSpec twoZeroSpec ∧
    SpecsImplemented (link scZeroBad scOne) twoZeroSpec ∧
    PreservesVerifiedPartial id twoZeroSpec ∧
    PreservesDefines id ∧
    ¬ ProgramPartialCorrect (link (id scZeroBad) (id scOne)) twoZeroSpec

theorem Toy.Link.Cex.cex_sep_comp_without_second_verified :
    ModuleVerifiedPartial scZero twoZeroSpec twoZeroSpec ∧
    ¬ ModuleVerifiedPartial scOneBad twoZeroSpec twoZeroSpec ∧
    SpecsImplemented (link scZero scOneBad) twoZeroSpec ∧
    PreservesVerifiedPartial id twoZeroSpec ∧
    PreservesDefines id ∧
    ¬ ProgramPartialCorrect (link (id scZero) (id scOneBad)) twoZeroSpec

theorem Toy.Link.Cex.cex_sep_comp_without_specsImplemented :
    ModuleVerifiedPartial scZeroCalls2 threeZeroSpec threeZeroSpec ∧
    ModuleVerifiedPartial scOne threeZeroSpec threeZeroSpec ∧
    ¬ SpecsImplemented (link scZeroCalls2 scOne) threeZeroSpec ∧
    PreservesVerifiedPartial id threeZeroSpec ∧
    PreservesDefines id ∧
    ¬ ProgramPartialCorrect (link (id scZeroCalls2) (id scOne)) threeZeroSpec

theorem Toy.Link.Cex.cex_sep_comp_without_preservesVerified :
    ModuleVerifiedPartial scZero twoZeroSpec twoZeroSpec ∧
    ModuleVerifiedPartial scOne twoZeroSpec twoZeroSpec ∧
    SpecsImplemented (link scZero scOne) twoZeroSpec ∧
    ¬ PreservesVerifiedPartial badBodyCompile twoZeroSpec ∧
    PreservesDefines badBodyCompile ∧
    ¬ ProgramPartialCorrect (link (badBodyCompile scZero) (badBodyCompile scOne)) twoZeroSpec

theorem Toy.Link.Cex.cex_sep_comp_without_preservesDefines :
    ModuleVerifiedPartial scZero twoZeroSpec twoZeroSpec ∧
    ModuleVerifiedPartial scOne twoZeroSpec twoZeroSpec ∧
    SpecsImplemented (link scZero scOne) twoZeroSpec ∧
    PreservesVerifiedPartial dropCompile twoZeroSpec ∧
    ¬ PreservesDefines dropCompile ∧
    ¬ ProgramPartialCorrect (link (dropCompile scZero) (dropCompile scOne)) twoZeroSpec

theorem Toy.Link.Cex.inlPass_not_preservesVerified :
    ¬ PreservesVerifiedPartial inlPass inlSpec ∧ ¬ PassCtxRefines inlPass
```

Basis: execution (Lean kernel check) — `Toy.Link.separate_compilation_partial_correct_of_preserves_verified`, `Toy.Link.Examples.nonvacuous_separate_compilation`, `Toy.Link.Cex.cex_sep_comp_without_first_verified`, `Toy.Link.Cex.cex_sep_comp_without_second_verified`, `Toy.Link.Cex.cex_sep_comp_without_specsImplemented`, `Toy.Link.Cex.cex_sep_comp_without_preservesVerified`, `Toy.Link.Cex.cex_sep_comp_without_preservesDefines`, `Toy.Link.Cex.inlPass_not_preservesVerified`.

Basis: derived (modeling bridge) — A compiler pass that only guarantees "verified-against-interface in, verified-against-interface out" yields interface-correct linked programs and nothing more. Reasoning: the theorem's conclusion mentions only `S`, and `cex-verifiability-preservation-not-behavioural` exhibits a pass meeting both hypotheses that changes observable results.

#### 17. `separate-compilation-behavioural-refinement` (theorem)

- **Tier:** T0. Separate compilation correctness from per-module contextual refinement, in the shape of Patterson and Ahmed's Corollary 4.3, here immediate from the precongruence of `CtxRefines`.
- **Plain claim:** If a per-module pass is a contextual refinement on every module (`PassCtxRefines compile`, behaviour relation `CtxRefines`) and `M₁`, `M₂` are disjoint, then `link (compile M₁) (compile M₂)` contextually refines `link M₁ M₂`; in particular partial correctness of the source link transfers to the compiled link.
- **Lean:** `Toy.Link.separate_compilation_ctxRefines_of_pass_ctxRefines`, `Toy.Link.separate_compilation_preserves_partial_correctness_of_pass_ctxRefines`

```lean
theorem Toy.Link.separate_compilation_ctxRefines_of_pass_ctxRefines
    {M₁ M₂ : Module} {compile : Module → Module}
    (hPass : PassCtxRefines compile) (hLink : Linkable M₁ M₂) :
    CtxRefines (link M₁ M₂) (link (compile M₁) (compile M₂))

theorem Toy.Link.separate_compilation_preserves_partial_correctness_of_pass_ctxRefines
    {M₁ M₂ : Module} {S : SpecEnv} {compile : Module → Module}
    (hPass : PassCtxRefines compile) (hLink : Linkable M₁ M₂)
    (hSrc : ProgramPartialCorrect (link M₁ M₂) S) :
    ProgramPartialCorrect (link (compile M₁) (compile M₂)) S
```

Unfolded (`Toy.Link.Unfolded.separate_compilation_ctxRefines_of_pass_ctxRefines_unfolded_iff`): `(∀ M C, (∀ fn, ¬ (C.Defines fn ∧ M.Defines fn)) → (∀ fn, ¬ (C.Defines fn ∧ (compile M).Defines fn)) → ∀ entry fuel arg out, out ∈ eval fuel (link C (compile M)) entry arg → out ∈ eval fuel (link C M) entry arg) → (∀ fn, ¬ (M₁.Defines fn ∧ M₂.Defines fn)) → (the same inclusion for link M₁ M₂ and link (compile M₁) (compile M₂) under every context disjoint from both)`. The corollary `separate_compilation_preserves_partial_correctness_of_pass_ctxRefines` has the third premise `hSrc : ProgramPartialCorrect (link M₁ M₂) S`, which is part of the hypothesis ledger below.

**Hypothesis ledger.**

| Hypothesis | Why it is needed | Tightness |
| :--- | :--- | :--- |
| `PassCtxRefines compile` | explicit behaviour relation: each compiled module contextually refines its source (only the instances at `M₁` and `M₂` are used); used by both theorems; the named counterexample refutes the conclusion `CtxRefines (link M₁ M₂) (link (compile M₁) (compile M₂))` of the primary theorem `separate_compilation_ctxRefines_of_pass_ctxRefines`, not the corollary's conclusion `ProgramPartialCorrect (link (compile M₁) (compile M₂)) S` (its other conjuncts discharge every hypothesis of `separate_compilation_partial_correct_of_preserves_verified`, so its compiled link is partially correct for `zSpec`); the package does not exhibit a counterexample to the corollary without this premise | tight: counterexample `Toy.Link.Cex.cex_verifiability_preservation_not_behavioural` |
| `Linkable M₁ M₂` | disjointness, as in the precongruence theorem; an overlapping module can shadow names the other relies on; used by both theorems; the named counterexample refutes the conclusion `CtxRefines (link M₁ M₂) (link (compile M₁) (compile M₂))` of the primary theorem, not the corollary's partial-correctness conclusion; the package does not exhibit a counterexample to the corollary without this premise | tight: counterexample `Toy.Link.Cex.cex_sep_comp_ctx_without_linkable` |
| `ProgramPartialCorrect (link M₁ M₂) S` | third premise (`hSrc`) of the corollary `separate_compilation_preserves_partial_correctness_of_pass_ctxRefines` only: the property that is transferred to the compiled link; the corollary produces no correctness fact that the source link does not already have | tight: counterexample `Toy.Link.Cex.cex_sep_comp_behavioural_corollary_without_hSrc` |

- **Depth:** `definitional`. Definitional given `ctxRefines_link_congr`; the corollary uses `entryRefines_preserves_fnPartialCorrect`.
- **Non-vacuity witness:** The constant folder `constFoldPass` is a contextual refinement on every module (it does not change any outcome list), with the disjoint modules `sepMod1 = [(0, add (call 1 var) (lit 0))]` and `sepMod2 = [(1, add (lit 0) var)]` (`Toy.Link.Examples.nonvacuous_separate_compilation_ctxRefines`). For all three premises of the corollary: the same pass with the public copies `scMod1 = [(0, add (call 1 var) (lit 0))]`, `scMod2 = [(1, add (lit 0) var)]` and the interface `scSpec` (functions `0` and `1` return their argument), whose source link is partially correct; the corollary then gives partial correctness of the compiled link (`Toy.Link.Examples.nonvacuous_sep_comp_behavioural_corollary`). (`Toy.Link.Examples.nonvacuous_separate_compilation_ctxRefines`, `Toy.Link.Examples.nonvacuous_sep_comp_behavioural_corollary`)
- **Prior art:**
  - Daniel Patterson and Amal Ahmed, 'The next 700 compiler correctness theorems (functional pearl)', PACMPL 3(ICFP), Article 85, 2019, doi:10.1145/3341689 (§4.1, Theorem 4.1 (CCC), p. 85:8; §4.2, Corollary 4.3 'CCC Implies Correct Separate Compilation', p. 85:9).
  - Jérémie Koenig and Zhong Shao, 'CompCertO', PLDI '21, pp. 1095-1109, 2021, doi:10.1145/3453483.3454097 (§3.4, Theorem 3.8: compositional correctness of CompCertO).
  - Jeehoon Kang, Yoonseung Kim, Chung-Kil Hur, Derek Dreyer, and Viktor Vafeiadis, 'Lightweight verification of separate compilation', POPL '16, pp. 178-190, 2016, doi:10.1145/2837614.2837642 (separate compilation correctness for modules compiled by the same compiler).
- **Design question:** What does separate compilation preserve when passes are required to be per-module behavioural refinements?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.nonvacuous_separate_compilation_ctxRefines :
    PassCtxRefines constFoldPass ∧ Linkable sepMod1 sepMod2 ∧ constFoldPass sepMod1 ≠ sepMod1

theorem Toy.Link.Examples.nonvacuous_sep_comp_behavioural_corollary :
    PassCtxRefines constFoldPass ∧
    Linkable scMod1 scMod2 ∧
    constFoldPass scMod1 ≠ scMod1 ∧
    ProgramPartialCorrect (link scMod1 scMod2) scSpec ∧
    ProgramPartialCorrect (link (constFoldPass scMod1) (constFoldPass scMod2)) scSpec

theorem Toy.Link.Cex.cex_verifiability_preservation_not_behavioural :
    PreservesVerifiedPartial zeroBodies zSpec ∧
    PreservesDefines zeroBodies ∧
    ModuleVerifiedPartial const1Mod zSpec zSpec ∧
    ModuleVerifiedPartial ([] : Module) zSpec zSpec ∧
    SpecsImplemented (link const1Mod []) zSpec ∧
    Linkable const1Mod [] ∧
    ¬ PassCtxRefines zeroBodies ∧
    ¬ EntryRefines 0 (link const1Mod []) (link (zeroBodies const1Mod) (zeroBodies [])) ∧
    ¬ CtxRefines (link const1Mod []) (link (zeroBodies const1Mod) (zeroBodies []))

theorem Toy.Link.Cex.cex_sep_comp_ctx_without_linkable :
    PassCtxRefines ipPass ∧
    ¬ Linkable ipMod1 ipMod2 ∧
    ¬ CtxRefines (link ipMod1 ipMod2) (link (ipPass ipMod1) (ipPass ipMod2))

theorem Toy.Link.Cex.cex_sep_comp_behavioural_corollary_without_hSrc :
    PassCtxRefines id ∧
    Linkable const1Mod ([] : Module) ∧
    ¬ ProgramPartialCorrect (link const1Mod []) zeroOutSpec ∧
    ¬ ProgramPartialCorrect (link (id const1Mod) (id [])) zeroOutSpec
```

Basis: execution (Lean kernel check) — `Toy.Link.separate_compilation_ctxRefines_of_pass_ctxRefines`, `Toy.Link.separate_compilation_preserves_partial_correctness_of_pass_ctxRefines`, `Toy.Link.Examples.nonvacuous_separate_compilation_ctxRefines`, `Toy.Link.Examples.nonvacuous_sep_comp_behavioural_corollary`, `Toy.Link.Cex.cex_verifiability_preservation_not_behavioural`, `Toy.Link.Cex.cex_sep_comp_ctx_without_linkable`, `Toy.Link.Cex.cex_sep_comp_behavioural_corollary_without_hSrc`.

Basis: derived (modeling bridge) — If each per-module pass is a contextual refinement in a language without shared state, separately compiled modules may be linked and the result refines the linked source. Reasoning: this is the precongruence theorem instantiated at the pass. Passes that change call depth, inline, or introduce helpers are not contextual refinements in this model, so they are outside its scope.

#### 18. `cex-verifiability-preservation-not-behavioural` (counterexample)

- **Tier:** T1. Folklore distinction between specification preservation and semantic preservation, made precise with a two-line pass.
- **Plain claim:** The pass `zeroBodies` (replace every body by `lit 0`) preserves verification against the interface `zSpec` (`0` returns a non-negative value) and keeps every name, and all hypotheses of `separate-compilation-preserves-verifiability` hold for `const1Mod` and the empty module; yet the compiled program returns `0` where the source returns `1`, so it neither refines the source at entry `0` nor contextually, and `zeroBodies` is not a contextually refining pass.
- **Lean:** `Toy.Link.Cex.cex_verifiability_preservation_not_behavioural`

```lean
theorem Toy.Link.Cex.cex_verifiability_preservation_not_behavioural :
    PreservesVerifiedPartial zeroBodies zSpec ∧
    PreservesDefines zeroBodies ∧
    ModuleVerifiedPartial const1Mod zSpec zSpec ∧
    ModuleVerifiedPartial ([] : Module) zSpec zSpec ∧
    SpecsImplemented (link const1Mod []) zSpec ∧
    Linkable const1Mod [] ∧
    ¬ PassCtxRefines zeroBodies ∧
    ¬ EntryRefines 0 (link const1Mod []) (link (zeroBodies const1Mod) (zeroBodies [])) ∧
    ¬ CtxRefines (link const1Mod []) (link (zeroBodies const1Mod) (zeroBodies []))
```

Pass and spec: `zeroBodies M = M.map fun p => (p.1, lit 0)`; `zSpec 0 = {pre := True, post := v ≥ 0}`; source `const1Mod = [(0, lit 1)]` linked with the empty module.

**Hypothesis ledger.** No hypotheses (a closed statement about concrete modules or a reference point).

- **Depth:** `shallow`. Pass properties by a lookup lemma for `zeroBodies`; separation by `decide` at fuel `1`.
- **Non-vacuity witness:** Source `const1Mod = [(0, lit 1)]` returns `1`; compiled `[(0, lit 0)]` returns `0`. (`Toy.Link.Cex.cex_verifiability_preservation_not_behavioural`)
- **Positive control** (a nearby setting where the negative conclusion fails): `Toy.Link.Examples.positive_control_constFold_verifiable_and_behavioural`.
- **Prior art:**
  - Xavier Leroy, CACM 52(7):107-115, 2009, doi:10.1145/1538788.1538814 (§2.1: semantic preservation versus property (4), preservation of specifications).
- **Design question:** What does separate compilation preserve when passes are only required to preserve per-module verifiability?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.positive_control_constFold_verifiable_and_behavioural (S : SpecEnv) :
    PreservesVerifiedPartial constFoldPass S ∧ PreservesDefines constFoldPass ∧
    PassCtxRefines constFoldPass
```

Basis: execution (Lean kernel check) — `Toy.Link.Cex.cex_verifiability_preservation_not_behavioural`, `Toy.Link.Examples.positive_control_constFold_verifiable_and_behavioural`.

#### 19. `cex-separate-compilation-callee-dependent-rewrite` (counterexample)

- **Tier:** T1. Folklore hazard (a per-module optimization justified by another module's body rather than its interface) made into a minimal mechanized witness; no mechanized witness of this kind was found.
- **Plain claim:** Rewriting the caller `inlCaller = [(0, call 1 var)]` to `inlCallerOpt = [(0, (call 1 var + call 1 var) - 2)]` is a contextual equivalence in the whole program with `inlCallee1 = [(1, lit 2)]`, but it is not a per-module contextual refinement and not verifiable against the shared interface `inlSpec`; replacing `inlCallee1` by `inlCallee2 = [(1, lit 1)]`, which also satisfies `inlSpec` and keeps the original program correct, makes the rewritten program return `0`, violating `inlSpec` and refinement.
- **Lean:** `Toy.Link.Cex.cex_callee_dependent_rewrite_breaks_under_spec_callee_replacement`; supporting declarations: `Toy.Link.Cex.inlPass_not_preservesVerified`

```lean
theorem Toy.Link.Cex.cex_callee_dependent_rewrite_breaks_under_spec_callee_replacement :
    Linkable inlCaller inlCallee1 ∧
    Linkable inlCaller inlCallee2 ∧
    ModuleVerifiedPartial inlCaller inlSpec inlSpec ∧
    ModuleVerifiedPartial inlCallee1 inlSpec inlSpec ∧
    ModuleVerifiedPartial inlCallee2 inlSpec inlSpec ∧
    FnPartialCorrect inlCallee2 1 (inlSpec 1) ∧
    ProgramPartialCorrect (link inlCaller inlCallee2) inlSpec ∧
    CtxRefines (link inlCaller inlCallee1) (link inlCallerOpt inlCallee1) ∧
    CtxRefines (link inlCallerOpt inlCallee1) (link inlCaller inlCallee1) ∧
    ¬ ModuleVerifiedPartial inlCallerOpt inlSpec inlSpec ∧
    ¬ CtxRefines inlCaller inlCallerOpt ∧
    ¬ ProgramPartialCorrect (link inlCallerOpt inlCallee2) inlSpec ∧
    ¬ EntryRefines 0 (link inlCaller inlCallee2) (link inlCallerOpt inlCallee2)
```

Modules and spec: `inlCaller = [(0, call 1 var)]`, `inlCallerOpt = [(0, sub (add (call 1 var) (call 1 var)) (lit 2))]`, `inlCallee1 = [(1, lit 2)]`, `inlCallee2 = [(1, lit 1)]`; `inlSpec` gives `0` and `1` the contract `{pre := True, post := v ≥ 1}`; `inlPass M = if M = inlCaller then inlCallerOpt else M`.

**Hypothesis ledger.** No hypotheses (a closed statement about concrete modules or a reference point).

- **Depth:** `shallow`. Contextual equivalence under `inlCallee1` by fuel induction; separations by `decide` at fuel `2`.
- **Non-vacuity witness:** With `1 ↦ 2`: `2 + 2 - 2 = 2`; with `1 ↦ 1`: `1 + 1 - 2 = 0 < 1`. (`Toy.Link.Cex.cex_callee_dependent_rewrite_breaks_under_spec_callee_replacement`)
- **Positive control** (a nearby setting where the negative conclusion fails): `Toy.Link.Examples.positive_control_interface_only_optimization_survives_replacement`.
- **Prior art:**
  - Jeehoon Kang, Yoonseung Kim, Chung-Kil Hur, Derek Dreyer, and Viktor Vafeiadis, 'Lightweight verification of separate compilation', POPL '16, pp. 178-190, 2016, doi:10.1145/2837614.2837642 (§5.3: intra-module inlining stays valid after linking because the inlined definitions remain in the linked environment; contrast with a rewrite that depends on another module).
  - Daniel Patterson and Amal Ahmed, PACMPL 3(ICFP), Article 85, 2019, doi:10.1145/3341689 (§3: compiler correctness theorems differ in what code a compiled module may be linked with).
- **Design question:** Which per-module transformations are compatible with interface-only (spec-based) separate compilation?

Statements of the witnesses, controls, counterexamples and supporting declarations named above:

```lean
theorem Toy.Link.Examples.positive_control_interface_only_optimization_survives_replacement :
    ModuleVerifiedPartial ctrlCaller ctrlSpec ctrlSpec ∧
    ModuleVerifiedPartial ctrlCallee1 ctrlSpec ctrlSpec ∧
    ModuleVerifiedPartial ctrlCallee2 ctrlSpec ctrlSpec ∧
    ModuleVerifiedPartial (constFoldPass ctrlCaller) ctrlSpec ctrlSpec ∧
    ProgramPartialCorrect (link (constFoldPass ctrlCaller) ctrlCallee1) ctrlSpec ∧
    ProgramPartialCorrect (link (constFoldPass ctrlCaller) ctrlCallee2) ctrlSpec

theorem Toy.Link.Cex.inlPass_not_preservesVerified :
    ¬ PreservesVerifiedPartial inlPass inlSpec ∧ ¬ PassCtxRefines inlPass
```

Basis: execution (Lean kernel check) — `Toy.Link.Cex.cex_callee_dependent_rewrite_breaks_under_spec_callee_replacement`, `Toy.Link.Examples.positive_control_interface_only_optimization_survives_replacement`, `Toy.Link.Cex.inlPass_not_preservesVerified`.

Basis: derived (modeling bridge) — A per-module optimization justified by the body of another module, rather than by its interface, can be invalidated by relinking with a different implementation of the same interface. Reasoning: the counterexample is exactly this situation. It does not affect link-time optimization performed after all bodies are fixed.

## Boundaries

### Non-claims

Each result's non-claims, as recorded in `results.json`. These are what a reader must not infer.

**1. `ctx-refines-refl`**

- `CtxRefines`/`EntryRefines` compare outcome sets at the same call-depth fuel, and `outOfFuel` is one of the compared outcomes. They therefore do constrain divergence: a target that may fail to terminate where the source terminates does not refine it (`Toy.Link.Cex.cex_ctxRefines_rejects_new_divergence`). They imply inclusion of may-divergence in the sense of `MayDiverge` (`Toy.Link.ctxRefines_reflects_mayDiverge`; with binary `choose`, `MayDiverge` coincides with the existence of an infinite call chain, an equivalence not formalized here), and they are strictly finer than inclusion of eventual results or of divergence-sensitive behaviour because they also fix call depth (`Toy.Link.Cex.cex_ctxRefines_fixes_call_depth`). 'Divergence is not observed' applies only to the partial-correctness results.
- Every function a module defines is exported and can be called by a context, and `CtxRefines M M'` implies `SameDom M M'` (`Toy.Link.ctxRefines_sameDom`). So contextual refinement here forbids adding, removing or renaming any function, including compiler-introduced helpers (clones, outlined code) and dead internal helpers. The model has no private or static symbols, so it says nothing about transformations of non-exported code.
- Does not make `CtxRefines` symmetric: `choose01Mod ⊑ const0Mod` holds while the converse fails (`Toy.Link.Examples.cex_ctxRefines_not_symm`).
- Toy model: stateless first-order functions of one unbounded integer argument, modules as finite association lists, no memory and no concurrency; says nothing directly about C, Rust, or assembly linking.

**2. `ctx-refines-trans`**

- `CtxRefines` compares outcome sets at the same call-depth fuel, including `outOfFuel`; it constrains divergence and fixes call depth (`Toy.Link.Cex.cex_ctxRefines_rejects_new_divergence`, `Toy.Link.Cex.cex_ctxRefines_fixes_call_depth`). Transformations that add or remove a call on some path fail `CtxRefines` even when they compute the same results.
- Every defined function is exported; `CtxRefines` forces equal domains (`Toy.Link.ctxRefines_sameDom`). The model has no private symbols.
- Unlike Patterson and Ahmed's discussion of vertical compositionality (which they distinguish from transitivity), this result relates modules of one language only; it says nothing about multi-pass compilers between different languages.

**3. `ctx-refines-precongruence-link`**

- Precongruence is close to definitional here: contexts are stateless first-order modules and compose by linking. Unlike CompCertO Theorem 3.4 and CompCertM HorComp (which needs self-related modules), it says nothing about simulation-based compiler correctness, where horizontal composition is a substantive theorem about memory and rely/guarantee conventions.
- Does not hold for non-disjoint (shadowing) linking (`Toy.Link.Cex.cex_link_congr_without_linkable`).
- `CtxRefines` constrains divergence and fixes call depth (`Toy.Link.Cex.cex_ctxRefines_fixes_call_depth`); per-module passes that add or remove calls are not contextual refinements, so this theorem does not cover them. Specification-based separate compilation (`separate-compilation-preserves-verifiability`) admits such passes but gives no behavioural relation.
- Every defined function is exported; `CtxRefines` forces equal domains. The model has no private symbols.

**4. `ctx-refines-forces-same-domain`**

- Depends on two modelling choices: `undefinedCall` is an ordinary observable outcome, and contexts need not close the program (the entry may be any name, including one neither module defines). Linking never fails: unresolved references are allowed and fail only at run time, so deleting an exported function is modelled as a change of run-time behaviour, whereas in real toolchains it is typically a link-time error. A source `undefinedCall` does not license arbitrary target behaviour (contrast Leroy 2009, §2.1).
- The model has no private or static symbols: every definition is an export. The result says nothing about adding or removing non-exported helpers in a language with symbol hiding.
- Does not say that equal domains suffice for contextual refinement.

**5. `cex-add-or-delete-function-not-contextual`**

- This is an immediate consequence of `ctxRefines_sameDom`; calling the deleted function with the empty context already separates the pair. It does not exhibit callbacks, shared memory, or pointer leakage.
- The model has no private symbols. In a language where the helper or the deleted function is static (not exported), these transformations may well be contextual refinements; nothing here speaks to that.
- `undefinedCall` is observable and linking never fails; in real toolchains deleting a referenced export is typically a link-time error.

**6. `ctx-refines-closed-collapse`**

- For closed modules the only gap between refinement at a designated entry and contextual refinement is the other exported entries (`Toy.Link.Cex.cex_closed_main_entry_refines_not_ctxRefines`); no context is needed to exhibit it.
- Relies on the absence of state, memory, and pointers: contexts can interact with a module only through calls and return values. In languages with shared state or address-taking, closed modules can still be distinguished by contexts.
- `CtxRefines` compares outcomes in lockstep call depth and every definition is exported (`Toy.Link.ctxRefines_sameDom`); so does `StandaloneRefines` (by `sameDom_of_standaloneRefines`).
- With both modules open the equivalence fails (`Toy.Link.Cex.cex_collapse_without_closed_side`).

**7. `cex-closed-main-entry-refinement-not-contextual`**

- For closed modules, contextual refinement in this model coincides with standalone refinement at every entry point (`Toy.Link.ctxRefines_iff_standaloneRefines_of_closed_source_or_target`). This counterexample is already witnessed by calling function `1` directly with the empty context. It shows only that refinement at one designated entry does not imply refinement at all exported entries. It does not exhibit any context-interaction phenomenon such as callbacks, shared memory or pointer leakage; for a counterexample in which the context supplies behaviour, see `cex-open-specialization-standalone-refinement-not-contextual`.
- Every definition is exported; specialization via a fresh private clone cannot be expressed (a clone is a new export and fails `CtxRefines` by `Toy.Link.ctxRefines_sameDom`).
- Does not claim that every optimization of an exported body fails: an in-place `x + 0 ↦ x` rewrite is a contextual refinement (`Toy.Link.Examples.positive_control_in_place_export_optimization`).

**8. `cex-open-specialization-standalone-refinement-not-contextual`**

- Both modules are open, and this is necessary: if either were closed, standalone refinement would imply `CtxRefines` (`Toy.Link.ctxRefines_iff_standaloneRefines_of_closed_source_or_target`).
- Does not show that refinement at entry `0` fails under every context: in the shipped program it holds. It shows that neither standalone refinement at all entries nor refinement at the designated entry of one particular program implies contextual refinement.
- The interaction is first-order (calls and return values, including callbacks); there is no shared memory or pointer leakage in the model.
- `CtxRefines` constrains divergence: the callback separation at entry `0` is a newly introduced divergence.

**9. `ctx-refines-reflects-may-divergence`**

- `MayDiverge` is 'out of fuel at every fuel'. That this coincides with an infinite execution relies on finite (binary) branching and is not formalized here.
- Does not say `CtxRefines` is a divergence-sensitive refinement in the usual sense: it is strictly finer, because it also fixes call depth (`Toy.Link.Cex.cex_ctxRefines_fixes_call_depth`).
- Partial-correctness notions (`FnPartialCorrect`, `ProgramPartialCorrect`) accept `outOfFuel` and therefore do not observe divergence; this theorem is about the refinement relations only.

**10. `cex-ctx-refines-fixes-call-depth`**

- Shows that `CtxRefines` is strictly finer than inclusion of eventual results; it does not claim that real compilers must preserve call depth. A refinement relation insensitive to call depth (e.g. comparing outcomes for some sufficiently large fuel) is a different design not studied here.
- Passes that keep the call structure, such as constant folding of `x + 0`, are contextual refinements (`Toy.Link.Examples.passCtxRefines_pos`).

**11. `ag-partial-correctness`**

- Partial correctness only: `outOfFuel` is always accepted, so divergence is not observed; a diverging loop is partially correct for any postcondition (`Toy.Link.Cex.cex_ag_total_unsound_without_measure`).
- Contracts are on a single integer argument and result; no state, frames, auxiliary variables or adaptation rules are modelled; integers are unbounded.
- Each call is assumed independently via `(S fn).post`, so cross-call facts (e.g. `f(x) - f(x) = 0`) are not available unless the postcondition determines the result.

**12. `cex-ag-total-circular-unsound`**

- Does not refute the circular rule for partial correctness (`ag-partial-correctness`).
- Escape hatch: a well-founded measure decreasing across every call restores total correctness (`Toy.Link.Examples.positive_control_ag_total_with_wf_measure`, `ag-total-correctness-wf-measure`).
- Non-termination appears as `outOfFuel` at every fuel; there is no separate infinite-trace semantics.

**13. `ag-total-correctness-wf-measure`**

- The uniform fuel bound per argument depends on finite (binary) branching; with unbounded nondeterminism a uniform finite bound can fail even when every execution terminates, and total-correctness proofs need countable ordinals (Apt and Plotkin 1986).
- Contracts are on a single integer argument and result; no state, frames, auxiliary variables or adaptation rules are modelled; integers are unbounded; every call (recursive or not) must decrease the measure, which depends only on the callee and its argument.
- If `S` is too weak to establish the measure decrease for a later call, `wpCallDec` is unprovable even for terminating code (incompleteness of this particular rule is not studied).
- One measure `(rel, μ)` must be shared by every function of the program, including across linked modules (`Toy.Link.link_ag_total_correctness_of_wf_call_measure` takes the same `rel` and `μ` for both modules). Modules verified separately with their own well-founded measures do not compose: `pingMod = [(0, call 1 var)]` and `pongMod = [(1, call 0 var)]` are each verified for total correctness over `Nat.lt` with measures `μ₁ fn _ = if fn = 0 then 1 else 0` and `μ₂ fn _ = if fn = 1 then 1 else 0`, their link implements the interface, and the linked program is not totally correct (`Toy.Link.Cex.independent_measures_do_not_compose`).

**14. `spec-refinement-link-composition`**

- The callee `N` must be partially correct for `S'` on its own: it may not call back into `M` (an unresolved call is `undefinedCall`, which `ProgramPartialCorrect` forbids). Mutually recursive caller/callee pairs need `link_ag_partial_correctness` with a shared interface.
- The flat variant `Toy.Link.verified_flat_caller_links_with_refined_callee` (assumptions `S` for every call, refinement at every name) follows from this theorem but applies only to callers that make no verifiable call to their own functions: its hypotheses force `(S f).pre` to be unsatisfiable at every `f` that `M` defines (`Toy.Link.caller_spec_unsat_on_own_symbols`, `Toy.Link.Cex.flat_spec_refinement_inapplicable_to_recursive_caller`).
- Partial correctness only: divergence is not observed; no termination or behavioural refinement is established.
- Contracts are on a single integer argument and result; no state, frames, auxiliary variables or adaptation rules are modelled; integers are unbounded.

**15. `cex-spec-refinement-incomparable-callee`**

- The failure here is due to the postcondition side alone (`WeakensPre` holds at every external name). The precondition side is witnessed separately by `Toy.Link.Cex.cex_spec_refinement_without_weakensPre`.
- Does not claim that every incomparable spec causes a failure: only a caller that relies on the part of `S` that `S'` does not guarantee is unprotected.
- Partial correctness only; toy contracts on one integer argument and result.

**16. `separate-compilation-preserves-verifiability`**

- The theorem relates no behaviour of the compiled program to the source program. `PreservesVerifiedPartial compile S` mentions only `S`, so a pass satisfying both preservation hypotheses may replace every body by any code meeting `S`. Example: with interface `v ≥ 0`, the pass `zeroBodies` rewrites `1` to `0`, satisfies both hypotheses, but breaks `EntryRefines` with the source (`Toy.Link.Cex.cex_verifiability_preservation_not_behavioural`). The guarantee is `S`-correctness of the compiled program, not semantic preservation; for behavioural refinement see `separate-compilation-behavioural-refinement`.
- This result is `link_ag_partial_correctness` applied to the compiled modules; `compile` enters only through the two preservation hypotheses.
- Partial correctness only: not total correctness, timing, or divergence behaviour.
- Does not assume `Linkable M₁ M₂`: `moduleVerifiedPartial_link` only checks bodies reachable via `lookup (link M₁ M₂)`, although real linkers reject duplicate definitions.
- A pass whose correctness depends on another module's implementation, not just on `S`, violates `PreservesVerifiedPartial` (`Toy.Link.Cex.inlPass_not_preservesVerified`).

**17. `separate-compilation-behavioural-refinement`**

- The behaviour relation is `CtxRefines`, which compares outcomes in lockstep call depth, includes `outOfFuel`, and forces equal domains; passes that add or remove calls, inline, or introduce helpers are not covered (`Toy.Link.Cex.cex_ctxRefines_fixes_call_depth`, `Toy.Link.ctxRefines_sameDom`).
- Same-language, stateless, first-order modules only: unlike CompCertO Theorem 3.8 or Patterson and Ahmed's Corollary 4.3, there is no change of language, memory model, or calling convention.
- Behavioural refinement preserves partial correctness for the same specs; verifiability preservation does not imply behavioural refinement (`Toy.Link.Cex.cex_verifiability_preservation_not_behavioural`).

**18. `cex-verifiability-preservation-not-behavioural`**

- Does not say verifiability-preserving passes are useless: the compiled program is still `S`-correct. It says that `S`-correctness is all they guarantee.
- A pass may satisfy both properties (`Toy.Link.Examples.positive_control_constFold_verifiable_and_behavioural`).

**19. `cex-separate-compilation-callee-dependent-rewrite`**

- The transformation is not inlining; it is an algebraic rewrite valid only for the specific callee body, and it keeps both calls.
- Does not invalidate link-time optimization when all participating bodies are fixed together; it shows that a per-module rewrite justified by another module's body is neither a per-module contextual refinement nor verification-preserving (`Toy.Link.Cex.inlPass_not_preservesVerified`), so neither separate-compilation theorem covers it.
- The positive control covers two concrete spec-compliant callees; the statement for every spec-compliant callee is `link_ag_partial_correctness`.

### Attractive stronger conclusions that are not established

- **known not to apply:** "Contextual refinement ignores divergence." The refinement relations compare `outOfFuel` at every fuel; they reject newly introduced divergence (`Toy.Link.Cex.cex_ctxRefines_rejects_new_divergence`) and reflect may-divergence (`Toy.Link.ctxRefines_reflects_mayDiverge`). Only the partial-correctness notions ignore divergence.
- **known not to apply:** "Contextual refinement here is the usual divergence-sensitive refinement." It is strictly finer, because it also fixes call depth (`Toy.Link.Cex.cex_ctxRefines_fixes_call_depth`).
- **not examined:** "Removing or adding non-exported helpers is (or is not) a contextual refinement." The model has no private symbols, so it cannot express the question.
- **known not to apply:** "Separately verified modules with their own termination measures compose." They do not (`Toy.Link.Cex.independent_measures_do_not_compose`); `ag_total_correctness_of_wf_call_measure` needs one measure `(rel, μ)` shared by every function of the linked program.
- **known not to apply:** "A verifiability-preserving pass is semantics-preserving." See `Toy.Link.Cex.cex_verifiability_preservation_not_behavioural`.
- **not examined:** "The results transfer to C, Rust, assembly, or any language with memory." Every theorem is about the toy language; the modeling-bridge lines under **Findings** give only the reasoning that would have to be redone.

### Escape hatches

These are the hypotheses or modelling choices whose removal or change defeats a negative result.

- `cex-ag-total-circular-unsound`: a well-founded measure that decreases across every call restores total correctness (`Toy.Link.Examples.positive_control_ag_total_with_wf_measure`, `Toy.Link.ag_total_correctness_of_wf_call_measure`). Independent per-module measures are not enough (`Toy.Link.Cex.independent_measures_do_not_compose`).
- `cex-add-or-delete-function-not-contextual`, `ctx-refines-forces-same-domain`: both depend on every definition being exported and on `undefinedCall` being observable. In a model with symbol hiding, or with link-time failure of unresolved references, these conclusions need not hold. Neither variant is modelled.
- `cex-closed-main-entry-refinement-not-contextual`: specialization through a fresh non-exported clone would avoid the failure in a language with symbol hiding, but it cannot be expressed here. An in-place rewrite of an exported body that keeps its outcomes is a contextual refinement (`Toy.Link.Examples.positive_control_in_place_export_optimization`).
- `cex-open-specialization-standalone-refinement-not-contextual`: if either module is closed, standalone refinement already implies contextual refinement (`Toy.Link.ctxRefines_iff_standaloneRefines_of_closed_source_or_target`; positive control `Toy.Link.Examples.collapse_closed_target_ctxRefines`).
- `cex-ctx-refines-fixes-call-depth`: a refinement notion that ignores call depth would relate the two modules; such a notion is not studied here. Passes that keep the call structure, such as constant folding, are contextual refinements (`Toy.Link.Examples.passCtxRefines_pos`).
- `cex-spec-refinement-incomparable-callee`: if the actual callee spec also strengthens the postcondition under the assumed precondition, `Toy.Link.verified_recursive_caller_links_with_refined_callee` applies (`Toy.Link.Examples.positive_control_spec_refinement_link`).
- `cex-verifiability-preservation-not-behavioural`: requiring the pass to be a contextual refinement (`PassCtxRefines`) gives behavioural refinement (`Toy.Link.separate_compilation_ctxRefines_of_pass_ctxRefines`). Constant folding satisfies both pass properties (`Toy.Link.Examples.positive_control_constFold_verifiable_and_behavioural`).
- `cex-separate-compilation-callee-dependent-rewrite`: an optimization justified by the interface alone survives callee replacement (`Toy.Link.Examples.positive_control_interface_only_optimization_survives_replacement`). Whole-program optimization after all bodies are fixed is not addressed.

### Hypotheses with `unknown` tightness

None. Every hypothesis of every result is `tight`, with a fully proved counterexample in which all other hypotheses hold and the conclusion fails. In particular, the third premise of the behavioural corollary is shown tight by `Toy.Link.Cex.cex_sep_comp_behavioural_corollary_without_hSrc`. A few counterexamples are degenerate in a way their purpose notes already state. For transitivity, the first-step counterexample takes `M₂ = M₃`, and tightness is immediate for any relation that is not total. For the pass hypotheses of the separate-compilation theorems, only their instances at `M₁` and `M₂` are used, so the universally quantified pass forms are stronger than the proofs need.

### Disproved or dropped statements

None. No statement considered for this package was found false, and none was left unproved or omitted.

### Not examined

- Private (static) symbols and scoped name resolution; link-time failure of unresolved references.
- Memory, state, pointers, I/O, exceptions, concurrency, and interaction with contexts through anything other than calls and returns.
- Unbounded or countable nondeterminism. The uniform fuel bound in `ProgramTotalCorrect` relies on binary `choose` (see Apt and Plotkin 1986).
- The equivalence between `MayDiverge` (out of fuel at every fuel) and the existence of an infinite call chain, which holds by König's lemma for binary branching but is not formalized.
- Completeness of the `wpPartial` and `wpCallDec` rules.
- Compilation between different languages, memory models, or calling conventions, and multi-pass vertical composition across languages.
- Refinement notions that are insensitive to call depth.

## Evidence

**Kernel-check record.** Every declaration of the `ToyLink` library (572 non-internal declarations) depends only on axioms in `{propext, Classical.choice, Quot.sound}` (full list in `audit/axioms.json`). The library contains no `sorry`, `admit`, `native_decide`, `axiom`, `opaque`, `implemented_by`, `extern`, or `unsafe`. Toolchain: `leanprover/lean4:v4.34.1` (commit `5045d0056413266e57c625dcd7c365b10e377c52`). Observation date of all evidence: 2026-11-20.

Per referenced theorem: axioms (`Lean.collectAxioms`), statement hash (SHA-256 of `repr` of the type), closure hash (SHA-256 of the sorted, newline-joined lines `name : repr(type)[ := repr(value)]` over every `ToyLink` constant reachable from the type through types, non-theorem definition bodies and constructors; theorem proofs excluded) and closure size, all as recorded in `audit/statements.json`.

| Theorem | Axioms | Statement SHA-256 | Closure SHA-256 | Closure size |
| :--- | :--- | :--- | :--- | ---: |
| `Toy.Link.Cex.cex_add_fresh_helper_not_ctxRefines` | Quot.sound, propext | `f46695db754ba7d24762c0bca9af27a17a8abcd54b1cb5b21253e38fde83975d` | `8154dbaa282477e431c66c9758a3abaf870cff31075c40cf78e3004923ea8583` | 42 |
| `Toy.Link.Cex.cex_ag_partial_without_moduleVerified` | propext | `f02098348eb558755c37f6775d619134ee41cebfb0d57d92f8888a83b3cd401e` | `71c2d44c7ccecdbcf3ee62c55b0539eaa809182337fc4f1349c8f3c510d66d96` | 52 |
| `Toy.Link.Cex.cex_ag_partial_without_specsImplemented` | Quot.sound, propext | `25863459d16374f63cbfe08f6fcfea8a8cfe9fd97c27e2549baa089405d985f4` | `596d7a17286254e90b28531a2bf2a5519c5dc2ed593cf2c6e8d6f9d5b799318a` | 52 |
| `Toy.Link.Cex.cex_ag_total_unsound_without_measure` | Quot.sound, propext | `5ec167f793cc71012fcf7d90b1271346aeed86b83c586301ad929f8ca64f8092` | `f73f4cdbb97048031434a57fd2df5855177994828276ab010e6632ecc6440af3` | 55 |
| `Toy.Link.Cex.cex_ag_total_without_moduleVerifiedTotal` | Quot.sound, propext | `7c2e6afe0c982ffeef871453d08d3b3965cb67d0bd69f596e1afa36a62025470` | `305999b08be86db06299194e4116d95f2b73b23a24e87509f44b9ff1f30baebf` | 52 |
| `Toy.Link.Cex.cex_ag_total_without_specsImplemented` | Quot.sound, propext | `a1d466d9bcf5ceca8a63585a51e79c5276b3f1ccb20d549895e5649c8645218e` | `d108b2cad03e26ab0d4d67e9a5fb674250554b84428967396ae9469a2ff3dbe0` | 52 |
| `Toy.Link.Cex.cex_ag_total_without_wf` | Quot.sound, propext | `e0048011a63d436b3d363c8ddb8e42c52ef99642eec8ce822f9f9b91feaf6c5a` | `305999b08be86db06299194e4116d95f2b73b23a24e87509f44b9ff1f30baebf` | 52 |
| `Toy.Link.Cex.cex_callee_dependent_rewrite_breaks_under_spec_callee_replacement` | Quot.sound, propext | `646305b61531b6c001d2d6c72b8a7789c55f961266a10dde4bd5e2d91b5fde71` | `ed8a334fb7b5c5bfa52ff1348cfddf670c79a1f95ac784cd0f4bc92a58c3a338` | 58 |
| `Toy.Link.Cex.cex_closed_main_entry_refines_not_ctxRefines` | Quot.sound, propext | `dfbcc1a37c4aa079e4c2e2d903ba6c9f1541410ac9e2a4c7a55e2bd5e96e182d` | `95159afd61631ab84b0ad992f701714b777552f796cc537d18b8050e49e0d3f9` | 47 |
| `Toy.Link.Cex.cex_collapse_without_closed_side` | Quot.sound, propext | `34816d517f74ea23469f1997db1905786f8f63033bbbb89e09b4374c731a3480` | `6b78061e3644a64212f24e449a60f0e9024e91629397f98052e00f8175e266f4` | 47 |
| `Toy.Link.Cex.cex_ctxRefines_fixes_call_depth` | Quot.sound, propext | `f91e7257af88defce6a2b867d2e0aa17399ec922f5eeb2a453145724372eff6e` | `54d5fb8c92d7d43fa3ebfecf24a24ee24f1ea87a21d820ced57608715160094a` | 44 |
| `Toy.Link.Cex.cex_ctxRefines_rejects_new_divergence` | Quot.sound, propext | `e4caf5aab083d5c6caa02813d6f6ea2234e7ec811bfb5ce3fe9b52eb16913e0c` | `9b46f6640136c596628d5b135e0801cd542f17650b997b2e976620e3fa9fb337` | 45 |
| `Toy.Link.Cex.cex_ctxRefines_trans_without_first` | Quot.sound, propext | `46f1092ce63e1b270e7137eac0669ade1192fa907622c015e399db091a7a0f7d` | `675bee57df8bbd103f2cd65de2457a744214088461f7f0078bd60f43d1ec3585` | 43 |
| `Toy.Link.Cex.cex_ctxRefines_trans_without_second` | Quot.sound, propext | `7d04722bd5995ab5b6e21667cccffe23f0cbfbfa01313fed86f3e056e0c31d5c` | `3fbb0017025d7fad3dc4f34f4c10f697ff7c9a2b38e6bd0def4f566d433e3aac` | 44 |
| `Toy.Link.Cex.cex_delete_unused_export_not_ctxRefines` | Quot.sound, propext | `b8b04338bd48c3d6cf307f4ce1953d4d68d86831f545b7f40c1218ef965b479b` | `33288f1f4fce31d34db9207fde6fd671f36f11b3a9b5c437c8d01c5cdee515f7` | 47 |
| `Toy.Link.Cex.cex_link_congr_without_first_refines` | Quot.sound, propext | `3fca7c2ad88d8a9754e50595822415ac7996c370ebf82cec2640b6edbfc60c7f` | `3a33d4d5326ccdf4f5c4a154ab412bf469c79151d021fde7079598c8071e32f2` | 44 |
| `Toy.Link.Cex.cex_link_congr_without_linkable` | Quot.sound, propext | `434bffb4d9b5856ef602166516e6bc939f613bcd26bf58ae3c46c05085256fba` | `c0c43ab763ffd20f73eab72dfd129286227fee6a0810710ce3663a1db061176c` | 44 |
| `Toy.Link.Cex.cex_link_congr_without_second_refines` | Quot.sound, propext | `973bc0f732519a208d4ab288d27017d8246e30af4007a05abd888bdf41479623` | `3a33d4d5326ccdf4f5c4a154ab412bf469c79151d021fde7079598c8071e32f2` | 44 |
| `Toy.Link.Cex.cex_link_fails_for_incomparable_callee_spec` | Quot.sound, propext | `730526dfcc309c75003721f5e8d5ce36bdc6d80baa51a9eddc63aeac521e63a0` | `1e36ae49240a11b66e2ad9dd9266f370f8f728ae5cc3899d393d148ef83945b3` | 61 |
| `Toy.Link.Cex.cex_open_specialization_standalone_refines_not_ctxRefines` | Quot.sound, propext | `ab31fd26ce14348f6ea42b95a8bf27922729425fa1c562bfe1545d75fe37540e` | `2f977e4a9ba1b6224542d3d00dd480cf15c47908ae9abaed6112c6093be83d34` | 50 |
| `Toy.Link.Cex.cex_reflects_mayDiverge_without_linkable` | Quot.sound, propext | `58d45afbdfb6f489b799d23627e870403371d0ffb4578f45ab0a255b94c2cad7` | `61b98782528155a0d425c077bb708cf011d19656f3588eaf950f45ec485492d8` | 45 |
| `Toy.Link.Cex.cex_sep_comp_behavioural_corollary_without_hSrc` | Quot.sound, propext | `449ac28dfc79fd919490757fcdf76d1162872b4d18c9486b2c4a0113848eb6a8` | `0e71dc50cf3764ece244c6bfe3d0b81d1fb98a76db50ac58265ceada7ed4570c` | 51 |
| `Toy.Link.Cex.cex_sep_comp_ctx_without_linkable` | Quot.sound, propext | `a242d4e8cffdf31690b719664189e43f51b8b509d9fc3218ed6b993ec87c401d` | `9249c8e1ed2b2c2574cf825b8a8a758b1a01100e10ada4f65eed9cb37cd3b355` | 70 |
| `Toy.Link.Cex.cex_sep_comp_without_first_verified` | propext | `07edf2eef21daef61ea5a01e75eb1b12cf21ccbd05b6fa4ffeb2b8068d7914e6` | `5820d917822b090eaccaab61c6d43b4050d5e83049664102643bbe3f7a153443` | 56 |
| `Toy.Link.Cex.cex_sep_comp_without_preservesDefines` | propext | `ce8b61e6d2f9dc73878c73b14680b9084807a2d5fdb65cc9b01847755f54edff` | `62b5df29583b9d6a88477484b7afa9213122d5d382cd58039c98f4e1a89f142d` | 57 |
| `Toy.Link.Cex.cex_sep_comp_without_preservesVerified` | propext | `2810b1f968a8467572ad686d8f5041583e478b39e33def37f1dbb521e23f3cec` | `ae618170799aa152c220dc57a102f43307a1fc9259696489b79299ac3359ef48` | 58 |
| `Toy.Link.Cex.cex_sep_comp_without_second_verified` | propext | `b51f3b19029b2af62e0620fef3527ab04c774f08fba5ae9bac25b52b0d6fef6b` | `9ade4fa38342e25d1ecb684932d8c703b656ed0d98ae47ba7da531526fa89701` | 56 |
| `Toy.Link.Cex.cex_sep_comp_without_specsImplemented` | Quot.sound, propext | `963e5bee3677197d3bba36b3e6e28187810ab0ac658c72c9dc40d709aec0148d` | `f026718bf29220f0906c46b3980e8b8a46ceea139ba9d0280fbf33339eebcad2` | 56 |
| `Toy.Link.Cex.cex_spec_refinement_without_callee_correct` | Quot.sound, propext | `81854690a216a7dd0d4fe4cd8f8099d588bb854c57956d1149a2802fc7fcf79e` | `da02d20e9cd2ea7e96e3adf3eb3fa437d89edc06f3362043050afe1e535dc60f` | 60 |
| `Toy.Link.Cex.cex_spec_refinement_without_caller_verified` | Quot.sound, propext | `2a6957c7935c8596a2c69a0cc6d55c91bca2a5a0ed3f0e5d0f43e533d5e44c2a` | `bbd67474b25204d39fe9e1b7f389f8a933784c649dde67c0d2c2fe35357c8704` | 60 |
| `Toy.Link.Cex.cex_spec_refinement_without_linkable` | Quot.sound, propext | `a5b4d23f758d29b7aeb9b0ae769592b74931263f27647a26bb6337c99d478772` | `154c2b394ff4bb0261a90318580c85aeec643102f341a077976033b6c206ec0a` | 60 |
| `Toy.Link.Cex.cex_spec_refinement_without_strengthensPost` | Quot.sound, propext | `abf0380ae315b43072c3b5b43c1e80cc3f8d85639451ccb2229e80f6a3a44d78` | `270ee4794f274ee01e9bf0f5993ecc44b0dc0af577258a7b1cc64b9c153d66e7` | 61 |
| `Toy.Link.Cex.cex_spec_refinement_without_weakensPre` | Quot.sound, propext | `a9f661aeffaae8db89bfef90b2ea48b3d3d2944beda7ed966313016592814e5b` | `24dbaf60a4cf163bbde947007a1541343bae1aa198df6c78c4472859c96bf153` | 61 |
| `Toy.Link.Cex.cex_verifiability_preservation_not_behavioural` | Quot.sound, propext | `db881dbe955d19dfc850ab5f7359b24d4bcf1791db6550b549b9ea5ddd780f8e` | `24895af7bd1011b1349d6b66fa3f812b32db7ea43f4d367a9a600e29b243bb3e` | 58 |
| `Toy.Link.Cex.flat_spec_refinement_inapplicable_to_recursive_caller` | Quot.sound, propext | `35be4e753ae20eea68678772a176a67f022c112b0e544bb0fcaad85d48b1290d` | `81bcde976722ec05360fa9fd38eaf0dd487ff1e9f1c3453f49fcf355b72724a5` | 53 |
| `Toy.Link.Cex.independent_measures_do_not_compose` | Quot.sound, propext | `5cae26965c00919caefd3ad4e699ff910a79b4b94af165830513a6056418c07e` | `499ca66d174c20db498205f679636022e2525cda0da468cfe8a4efd285f05543` | 55 |
| `Toy.Link.Cex.inlPass_not_preservesVerified` | Quot.sound, propext | `c1c2bcd0a5d2558ca0126c6910a35e6a48f6148a67c6cee5551251794106963d` | `a0fe51adf223a54a19a26db0993d5a518fb7c87c5e6df6369895786470e5e774` | 81 |
| `Toy.Link.Examples.cex_ctxRefines_not_symm` | Quot.sound, propext | `09ffdd26dd20f40a33436a6988205a37f3fd6a14029e7427422552acfa89b71c` | `a668f9ca51c0655d7a0682e69d8827c8085a229cbb859f63704668279ada9e9e` | 43 |
| `Toy.Link.Examples.closed_source_open_target_collapse_witness` | Quot.sound, propext | `a83595b1beb7f9cc1a0bde85cadb47871147074826d824fe853d490313cb2524` | `3fb4b27dbec67fec7658996c1e3eec8e941a0d543c6108e6006f106e243fb785` | 47 |
| `Toy.Link.Examples.collapse_closed_target_ctxRefines` | Quot.sound, propext | `78fd5a3c67d9a5a99b6d5b55d30be4b3bd01a3589ab6687d29bce8b408ee6e12` | `4a854a880c30e4ec6863f05263b5cd1fa822c82116dc91ac9c4aefecc02a47ef` | 43 |
| `Toy.Link.Examples.empty_module_ag_total` | Quot.sound, propext | `c18ffca628b138b7edbd1fe09adb9b5a80722d15fe4a9a7c523ffe63a6194cd8` | `66c844470f68df7c24036a2bb643aae8b10bb6dd6702c7630ed26980e34f2f87` | 44 |
| `Toy.Link.Examples.evenOddProg_partial_correct` | Quot.sound, propext | `49ffd9e9f85d0f1faea1d9d8f5a3d184a5b9e37220e818b4073e654ffc6f0d27` | `74de6325b48e333dfde2636134dce0521136117549cd86f9d4434985b7d622a0` | 48 |
| `Toy.Link.Examples.evenOddProg_total_correct` | Quot.sound, propext | `a0c3eab441c4948913ed1e816c0bce4d9a7884f8dffc1ba795ace5fb91c8ff45` | `1ba6cf4f7317393358e281526296219e553bb23ae12eb90daf4b4add6f438a43` | 48 |
| `Toy.Link.Examples.nonvacuous_ag_partial_correctness` | Quot.sound, propext | `1f27d44bc7b7ce48e78e8590aff2070ad9bfb9a942b960741157084dc37d9641` | `c8ec515da78a7fb9b6e6e8dd9d66b98064d7d620c458e92bd87726e309e2a8ae` | 36 |
| `Toy.Link.Examples.nonvacuous_ag_total_correctness` | Quot.sound, propext | `a4abb55b039131b4fee50440988e3aec1f180e995318f4d82aaef1c3e0ed8fb7` | `f1652c508e7326f4fb716a25b005a6fa49e2f957d3ec1d785e9f52cfb494d53f` | 36 |
| `Toy.Link.Examples.nonvacuous_collapse_closed_target` | Quot.sound, propext | `faad50cb2f055a623cd0a6a4a96a2d757ed7aad3085b6fc7f2a5b2612f01ec8d` | `48261ac410d7ec4de4e6a0ba367b383a7a74c8c7f3f7f443acea7ef22d7705f8` | 44 |
| `Toy.Link.Examples.nonvacuous_ctxRefines_link_congr` | Quot.sound, propext | `0637a5c1de04c83ca70fc63aeea3c451abe081474c13155dbec83a8ccb9050d2` | `e7579fc30d8d1c5c2af5f1de268282875f335c5b90bde8a96ffb61816a4088d7` | 44 |
| `Toy.Link.Examples.nonvacuous_ctxRefines_refl` | propext | `b620355fceb3c73edc4352ac74f9f605e622904628963679f0f0ac780823f97d` | `f4d45b2be1d331dcdfbbb1b0febf77782cd0f0dd2d81d395e48f7d61379c8434` | 42 |
| `Toy.Link.Examples.nonvacuous_ctxRefines_reflects_mayDiverge` | Quot.sound, propext | `fd8a964fc456bd9f8051a646bf871a9f7e984eee0f46d38f560cf48e8fadcf9d` | `114dd679436c5ae1f866229b1e39cbb9d9faa4ed9827427086244286b7299523` | 44 |
| `Toy.Link.Examples.nonvacuous_ctxRefines_sameDom` | Quot.sound, propext | `f5a2264ea5e2a780f024875c28c96b1a92fa886e994f6298de02fc4a388f0b11` | `a668f9ca51c0655d7a0682e69d8827c8085a229cbb859f63704668279ada9e9e` | 43 |
| `Toy.Link.Examples.nonvacuous_ctxRefines_trans` | Quot.sound, propext | `ee45dd151834ed8507de003682677ee44eafd24f9d6c07a8de9bdfe4438bf4c1` | `93464afeca245549b577ff854b533402091f21749899f28eabeb8f7e6b88704f` | 44 |
| `Toy.Link.Examples.nonvacuous_recursive_spec_refinement` | Quot.sound, propext | `fed1783169950c0dd3bc146855d0ea0bf7e4c1e4a06aeffa553b96ea9e1fddf0` | `8418f6640aa0ddc4d8b884d60844198f886c99653eb474bbdf78c2ef1c2f06e7` | 60 |
| `Toy.Link.Examples.nonvacuous_sep_comp_behavioural_corollary` | Quot.sound, propext | `1ba10def81dac90e2613d090f2213015a0088c7ce33d8259b8d12f822f62e909` | `480cb7430b9e99bb97ad823efadac25bdaeb1ac2779020e4b662da1ad021733f` | 82 |
| `Toy.Link.Examples.nonvacuous_separate_compilation` | Quot.sound, propext | `02e3cccb16daa0dacc7a70e5a376adf9f1c1fd9c1b547406b50068917eb6048a` | `0ba1064b8ac68d198a1588e8c3305182c78ed0d15beefe061ce2bceff3a4ecb9` | 67 |
| `Toy.Link.Examples.nonvacuous_separate_compilation_ctxRefines` | Quot.sound, propext | `c85f3f4e7654acb19d2cf97b79aa2518518312ab92fc5ef9bed68de32dba550a` | `61661d1d30eb0b344695ebe478ae64d22bba942cca4f06aeb3881f52d239310f` | 74 |
| `Toy.Link.Examples.passCtxRefines_pos` | Quot.sound, propext | `d2159661c8f82261a18c15d8cec2c7c6a5c4f35499c24e600a1a2424e0d0f4b7` | `d8da6b8fda6631338f4075a02f4b9c81e6d6ea127200d9cb3af81d31e13b8b07` | 72 |
| `Toy.Link.Examples.positive_control_ag_total_with_wf_measure` | Classical.choice, Quot.sound, propext | `b55ea89bd3d2b275ca206c06bb2979f63a1fdc7a82ea173f4a88c5833134cbf7` | `2575a8b7b44367e690f5f65304e2a4ece304ca415eecdfa8496d9fa8ab32e605` | 52 |
| `Toy.Link.Examples.positive_control_constFold_verifiable_and_behavioural` | Quot.sound, propext | `5b0a56238153abd3da0aeb7d3fc28cc7edad110f96e1797d9f0aaa26ad5d0786` | `21ca406bed88a981de15277cc2601ea173baa12d01cd3c89dfb3ef4130966dc0` | 84 |
| `Toy.Link.Examples.positive_control_in_place_export_optimization` | Quot.sound, propext | `bc89f6ebb372d56c080f7b9287dd592d4720be402e37e9ef9bbcfd9528423c82` | `d85d76b3ab4cd91ac55b999e986a2733d02333ec7649ad48ce37be6666ec1cd6` | 44 |
| `Toy.Link.Examples.positive_control_interface_only_optimization_survives_replacement` | Quot.sound, propext | `11b3809fd443781210ab2d805c77ed0a7af3ef61ad1de41f4a6e3cec29d32034` | `fe2b6049a66fc9a86f8678e42ec53a3c712d02e9a482e37a708db9cbd7242224` | 83 |
| `Toy.Link.Examples.positive_control_spec_refinement_link` | Quot.sound, propext | `c9e1f34110ece3aaa047f0def8f1db62aa458cc59d6c687ff4be7e68e66222a9` | `b72bc8b67f77a7779c9446f4694d278272828e2e38b04491543887ca50aae956` | 47 |
| `Toy.Link.ag_partial_correctness` | Quot.sound, propext | `1cb961793c39243c3bb62cd00bf3f93944aad64ebafe57839c59339922478971` | `8f774fe5183ad4982db0bfd17a0ac4b40661d83d91300d00d0193b184566f644` | 50 |
| `Toy.Link.ag_total_correctness_of_wf_call_measure` | Quot.sound, propext | `485ffcecfaa5f7dcfa3efc7270f31096c4a6920a1fc299ea9cd686f8df8b08ed` | `5bd68062be48c4d68d1abf2163d2272c49d0ec0193090d4bf08322ef9a6cbf4f` | 50 |
| `Toy.Link.caller_spec_unsat_on_own_symbols` | Quot.sound, propext | `b434bd15372835dc9d6659ff3664faac64939bf9677c93d4963bfb4477f5fff7` | `fec00f0f1ab44dfc2cc223c45d26347838f065b3a243d99f9d499399555fd3f1` | 46 |
| `Toy.Link.ctxRefines_iff_standaloneRefines_of_closed_source_or_target` | Quot.sound, propext | `cf7fced9b030f3cd199642c721ad2c4ad904d32147aca10bae9c07d9bc65e89b` | `9b07d0192d775047edef7902aa46effab38eb956bd350b1da35f4f88ef9b1b7b` | 45 |
| `Toy.Link.ctxRefines_link_congr` | Quot.sound, propext | `e58630dac30cfef310036cc41a390dc87de74e863b801fc0615715683e836693` | `216ad460896ccf49707cc8a611d3832950dfca4681736260556a524a8fc79a44` | 41 |
| `Toy.Link.ctxRefines_link_left` | Quot.sound, propext | `c4c440284f4de9e475abb697613a39f6b32634daf05e1ed8b515664b25ebcdf6` | `216ad460896ccf49707cc8a611d3832950dfca4681736260556a524a8fc79a44` | 41 |
| `Toy.Link.ctxRefines_link_right` | Quot.sound, propext | `c49039ada940fea60eaf716cbb3a2de07234bedff1326a0ae49a516b03fd790b` | `216ad460896ccf49707cc8a611d3832950dfca4681736260556a524a8fc79a44` | 41 |
| `Toy.Link.ctxRefines_refl` | propext | `b08c17c1bc41556003b43cbb290fbde01b6952ea9f01eeb62251254ea9fb4f11` | `216ad460896ccf49707cc8a611d3832950dfca4681736260556a524a8fc79a44` | 41 |
| `Toy.Link.ctxRefines_reflects_mayDiverge` | Quot.sound, propext | `d78a8bdd04e80953d08ab729b4af8c0439eae89548203ca0289aac7f0be2e0d0` | `82800f4d248f1f9426584cd47f96252aa5a8666d50d1eb2821d9e13a9fb734a5` | 42 |
| `Toy.Link.ctxRefines_sameDom` | Quot.sound, propext | `85914fda601d548c7c6e6a8114f25720ea49e3434296c336874e31651f534ee9` | `8154dbaa282477e431c66c9758a3abaf870cff31075c40cf78e3004923ea8583` | 42 |
| `Toy.Link.ctxRefines_trans` | Quot.sound, propext | `4a1775271e3ef4dbecf00126d8be0594891f36fb995a4608a4f349ed73f728cb` | `216ad460896ccf49707cc8a611d3832950dfca4681736260556a524a8fc79a44` | 41 |
| `Toy.Link.link_ag_partial_correctness` | Quot.sound, propext | `89f9205541bf8ecdd5ff2d03becd11ca3e976ae40c267b8a8e39039bc95582ad` | `4f5d23730554a8d890b7688b0dc1138828bf3732e0352d550f9082d86d035d46` | 51 |
| `Toy.Link.link_ag_total_correctness_of_wf_call_measure` | Quot.sound, propext | `668dbab39621923a86fab9ff375f9f17f401b301cd2e3f6c6834790428dbaf34` | `c6b618bf5e53591880389647e30e799c3eb8f5f7f9ace6bac821c64f2661ccdd` | 51 |
| `Toy.Link.separate_compilation_ctxRefines_of_pass_ctxRefines` | Quot.sound, propext | `8f100749b4b17c281f17eca9a58d4f8ef5e90cd47a785cfe3c1393cabc4cc584` | `7d5ed76620beb7170afc65bcb67caa53e492dd13f9dc113ffc1792393bf02e0e` | 42 |
| `Toy.Link.separate_compilation_partial_correct_of_preserves_verified` | Quot.sound, propext | `4356b2ebd43035abeeabc387cc4cae880c9f69515a2c5f263727f45e378a80ae` | `1dfa002a985970bf0f83262041f79cf8f209c8ad8c44e9f44ad0c61be6794696` | 53 |
| `Toy.Link.separate_compilation_preserves_partial_correctness_of_pass_ctxRefines` | Quot.sound, propext | `d9e0740aa2e2df7cb0ba07f4256a3272748f4cd02c995f4030fdd9ece18059f0` | `56fc8390be6c4da83a480b4966ad1c40e7b1330cd84607e70d545a62b2d1d35a` | 49 |
| `Toy.Link.verified_flat_caller_links_with_refined_callee` | Quot.sound, propext | `5118e7f1673b0dc155a5f708ada53151fbc3071810f5929965647424173c38d8` | `cf838b4047c088ff393e5de875572399a5f2d2ce1972f99ca2a036732c9a3447` | 53 |
| `Toy.Link.verified_recursive_caller_links_with_refined_callee` | Quot.sound, propext | `f9ed02d9c83d6e7c5d8e5a4153b7eefe7c0dbe5ebe3f6c3b3dbd2ef814ab5ab0` | `5fb463ce1630a114ee5e23692a879c58510cc4d0690c18615d187897a3f15a14` | 56 |

**Primary sources.** These records were checked against Crossref metadata (DOI, title, year) on 2026-11-20. The section, page, and theorem locators in the cards were checked against the full texts or author versions named in each card. Where a primary text was not checked, the card says so.

- C. A. R. Hoare, "An axiomatic basis for computer programming", Communications of the ACM 12(10):576–580, 1969. doi:10.1145/363235.363259.
- C. A. R. Hoare, "Procedures and parameters: An axiomatic approach", Symposium on Semantics of Algorithmic Languages, LNM 188, pp. 102–116, Springer, 1971. doi:10.1007/BFb0059696. The page of the rule of recursive invocation was not checked.
- Tobias Nipkow, "Hoare logics for recursive procedures and unbounded nondeterminism", CSL 2002, LNCS 2471, pp. 103–119, Springer, 2002. doi:10.1007/3-540-45793-3_8. Checked against the author's preprint, whose pagination differs from the LNCS pages.
- K. R. Apt and G. D. Plotkin, "Countable nondeterminism and random assignment", Journal of the ACM 33(4):724–767, 1986. doi:10.1145/6490.6494.
- Norbert Schirmer, "A Sequential Imperative Programming Language: Syntax, Semantics, Hoare Logics and Verification Environment", Archive of Formal Proofs, 2008. https://www.isa-afp.org/entries/Simpl.html (entry page checked).
- Martín Abadi and Leslie Lamport, "Conjoining specifications", ACM TOPLAS 17(3):507–535, 1995. doi:10.1145/203095.201069.
- Carroll Morgan, *Programming from Specifications*, 2nd ed., Prentice Hall International, 1994 (checked in the author's 1998 reissue; Law 1.2 "weaken precondition", Law 5.1 "strengthen postcondition"). ISBN 978-0-13-123274-7 (no DOI); it is listed as a subject in `REPORT.json` under this ISBN.
- Barbara H. Liskov and Jeannette M. Wing, "A behavioral notion of subtyping", ACM TOPLAS 16(6):1811–1841, 1994. doi:10.1145/197320.197383.
- James Hiram Morris Jr., "Lambda-calculus models of programming languages", PhD thesis, MIT (Project MAC report MAC-TR-57, 1968; DSpace record hdl:1721.1/64850, which dates the degree 1969). The record was checked; the page of the definition was not.
- F. Lockwood Morris, "Advice on structuring compilers and proving them correct", POPL '73, pp. 144–152, 1973. doi:10.1145/512927.512941. Cited as summarized by Patterson and Ahmed 2019, §2; the primary text was not checked.
- Xavier Leroy, "Formal verification of a realistic compiler", Communications of the ACM 52(7):107–115, 2009. doi:10.1145/1538788.1538814.
- Gilles Barthe, Benjamin Grégoire, César Kunz, and Tamara Rezk, "Certificate translation for optimizing compilers", ACM TOPLAS 31(5), 2009. doi:10.1145/1538917.1538919.
- Gordon Stewart, Lennart Beringer, Santiago Cuellar, and Andrew W. Appel, "Compositional CompCert", POPL '15, pp. 275–287, 2015. doi:10.1145/2676726.2676985.
- Jeehoon Kang, Yoonseung Kim, Chung-Kil Hur, Derek Dreyer, and Viktor Vafeiadis, "Lightweight verification of separate compilation", POPL '16, pp. 178–190, 2016. doi:10.1145/2837614.2837642.
- Daniel Patterson and Amal Ahmed, "The next 700 compiler correctness theorems (functional pearl)", PACMPL 3(ICFP), Article 85, 2019. doi:10.1145/3341689.
- Youngju Song, Minki Cho, Dongjoo Kim, Yonghyun Kim, Jeehoon Kang, and Chung-Kil Hur, "CompCertM: CompCert with C-assembly linking and lightweight modular verification", PACMPL 4(POPL), Article 23, 2020. doi:10.1145/3371091.
- Jérémie Koenig and Zhong Shao, "CompCertO: compiling certified open C components", PLDI '21, pp. 1095–1109, 2021. doi:10.1145/3453483.3454097.

**Novelty.** No result is claimed novel. Tiers are `T0` (re-derivation) or `T1` (folklore made precise), with a justification on each card.

**Package material.** `lean/` holds the Lake project: `ToyLink/Defs.lean`, `Spec.lean`, `Basic.lean`, `Statements.lean`, `Unfolded.lean`, `Examples.lean`, `Counterexamples.lean`, `Supplement.lean`, and the root `ToyLink.lean`. `lean/RevalidationAudit.lean` is the audit program; it is not part of the library target. `results.json` holds the machine-readable cards. `audit/axioms.json` and `audit/statements.json` hold the recorded axiom and hash audit. `support/revalidate.py` is the revalidation script.

## Revalidation

**Requirements:** `elan`, which provides `lake` and installs the toolchain pinned in `lean/lean-toolchain`, and `python3`. No network access is needed beyond the first toolchain download.

**Primary command,** run from the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory, so the package is never modified, and then runs four checks:

1. `lake build` succeeds.
2. No Lean source contains `sorry`, `admit`, or `native_decide`, or declares an `axiom`.
3. Every declaration of the `ToyLink` library depends only on `propext`, `Classical.choice`, and `Quot.sound`, as computed by `Lean.collectAxioms`.
4. For every name referenced by `results.json`, and every name recorded in `audit/statements.json`, the statement hash and the closure hash equal the recorded values.

The statement hash is the SHA-256 of the `repr` of the declaration's type. The closure hash is the SHA-256 of the newline-joined, sorted lines `name : repr(type)` (followed by ` := repr(value)` for non-theorems). It covers every `ToyLink` constant reachable from the type through types, definition bodies, and constructors; theorem proofs are not hashed. The script prints `REVALIDATED` and exits with status 0 if and only if all checks pass.

**The same checks by hand,** using only `lake` and `python3`, from the package directory:

```sh
cd lean
lake build
lake env lean RevalidationAudit.lean > ../audit_out.txt
cd ..
python3 - <<'EOF'
import hashlib, json, re
a = json.loads(re.search(r"AUDIT_JSON (\{.*\})", open("audit_out.txt").read()).group(1))
rec = json.load(open("audit/statements.json"))["statements"]
bad = [d["name"] for d in a["decls"] if set(d["axioms"]) - {"propext", "Classical.choice", "Quot.sound"}]
mism = [s["name"] for s in a["stmts"] if s.get("missing") or rec[s["name"]] != {
    "statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
    "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
    "closure_size": len(s["closure"])}]
print(len(a["decls"]), "declarations;", "axioms ok" if not bad else bad, ";",
      len(a["stmts"]), "hashed names;", "hashes ok" if not mism else mism)
EOF
```

The expected output is `572 declarations; axioms ok ; 79 hashed names; hashes ok`. `lean/RevalidationAudit.lean` prints, for every `ToyLink` declaration, its axioms, and for every recorded name, the exact text that is hashed. Inspect `audit_out.txt` to see what each hash covers. To view the axioms of a single theorem interactively, add `#print axioms Toy.Link.ag_total_correctness_of_wf_call_measure` after `import ToyLink` in a scratch file and run it with `lake env lean`.

**What a passing run establishes.** It establishes that the published statements, and the definitions they depend on, are byte-for-byte those recorded here, and that the statements are kernel-checked under the pinned toolchain with the standard axioms. It does not re-check the prose, the modeling-bridge arguments, or the citations. A change to any definition in a statement's closure changes that statement's closure hash. If the hashes differ under a newer Lean release, the cause may be a change in `repr` output rather than in the mathematics; rebuilding under the pinned toolchain distinguishes the two.
