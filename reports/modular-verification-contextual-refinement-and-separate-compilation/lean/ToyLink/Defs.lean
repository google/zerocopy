/-!
# Toy language, modules, linking, and fuel-indexed refinement

Defines a minimal first-order module language (`Expr`, `Module`), disjoint-domain
linking (`Linkable`, `link`), a computable call-depth-indexed big-step semantics
(`eval`, `HasBehavior`), single-entry refinement (`EntryRefines`), standalone
refinement at every entry (`StandaloneRefines`), contextual refinement (`CtxRefines`),
and may-divergence (`MayDiverge`).
-/

namespace Toy.Link

/-- Function symbol identifier. Captures linker symbol names across modules. -/
abbrev Fname := Nat

/-- Expressions in a tiny first-order integer language with bounded choice and named calls.
Captures single-argument pure arithmetic, conditionals, finite nondeterminism
(`choose`, modeling underspecification or choice), and static named function calls. -/
inductive Expr : Type where
  | lit (n : Int)
  | var
  | add (e₁ e₂ : Expr)
  | sub (e₁ e₂ : Expr)
  | mul (e₁ e₂ : Expr)
  | ifLe (e₁ e₂ eThen eElse : Expr)
  | choose (e₁ e₂ : Expr)
  | call (fn : Fname) (arg : Expr)
  deriving DecidableEq, Repr

/-- Possible outcomes of evaluating a call of a closed or open program up to a call-depth
bound ("fuel"). Captures normal return (`val`), calling a function that no linked module
defines (`undefinedCall`; linking never fails, unresolved names fail only when called),
and exhausting the call-depth bound (`outOfFuel`).
There is no separate divergence outcome; instead `outOfFuel` is an ordinary outcome that
refinement relations compare at every fuel. A call that may run forever yields
`outOfFuel` at every fuel (`MayDiverge`), and a terminating call yields `outOfFuel`
exactly at the fuels below its call depth. -/
inductive Outcome : Type where
  | val (v : Int)
  | undefinedCall
  | outOfFuel
  deriving DecidableEq, Repr

/-- A module is an association list from function names to single-parameter bodies,
viewed as a finite partial map via first-match lookup (`Module.lookup`).
Captures one compilation unit with definitions and unresolved external calls (imports).
Every definition is exported: the model has no private (static) symbols, so any context
can call any function a module defines. -/
abbrev Module := List (Fname × Expr)

/-- Partial map lookup in a module (first entry wins).
Captures static symbol resolution within a linked or unlinked module. -/
def Module.lookup : Module → Fname → Option Expr
  | [], _ => none
  | (k, body) :: rest, fn => if k = fn then some body else lookup rest fn

/-- `M.Defines fn` holds when function `fn` has a body in module `M`.
Captures the exported symbol domain of a module. -/
def Module.Defines (M : Module) (fn : Fname) : Prop :=
  (M.lookup fn).isSome = true

instance (M : Module) (fn : Fname) : Decidable (M.Defines fn) :=
  inferInstanceAs (Decidable ((M.lookup fn).isSome = true))

/-- Two modules define the exact same set of function names.
Captures interface domain equality between source and transformed modules. -/
def SameDom (M₁ M₂ : Module) : Prop :=
  ∀ fn, M₁.Defines fn ↔ M₂.Defines fn

/-- Two modules have disjoint defined function domains and can therefore be linked
without symbol collision. Captures separate-compilation disjointness of exported symbols. -/
def Linkable (M₁ M₂ : Module) : Prop :=
  ∀ fn, ¬ (M₁.Defines fn ∧ M₂.Defines fn)

/-- Computable decision procedure for `Linkable`. -/
def linkableBool (M₁ M₂ : Module) : Bool :=
  M₁.all (fun p => !(M₂.lookup p.1).isSome)

private theorem defines_of_mem {M : Module} {p : Fname × Expr} (hp : p ∈ M) :
    M.Defines p.1 := by
  induction M with
  | nil => cases hp
  | cons hd tl ih =>
    rcases hd with ⟨k, body⟩
    simp only [List.mem_cons] at hp
    by_cases hk : k = p.1
    · simp [Module.Defines, Module.lookup, hk]
    · rcases hp with rfl | htl
      · exact absurd rfl hk
      · have := ih htl
        simpa [Module.Defines, Module.lookup, hk] using this

private theorem mem_lookup_some {M : Module} {fn : Fname} {body : Expr}
    (hl : M.lookup fn = some body) : (fn, body) ∈ M := by
  induction M with
  | nil => simp [Module.lookup] at hl
  | cons hd tl ih =>
    rcases hd with ⟨k, b⟩
    simp only [Module.lookup] at hl
    by_cases hk : k = fn
    · subst hk
      simp only [ite_true, Option.some.injEq] at hl
      subst hl
      exact List.Mem.head _
    · simp only [hk, ite_false] at hl
      exact List.Mem.tail _ (ih hl)

theorem linkable_iff_linkableBool (M₁ M₂ : Module) :
    Linkable M₁ M₂ ↔ linkableBool M₁ M₂ = true := by
  constructor
  · intro h
    simp only [linkableBool, List.all_eq_true]
    intro p hp
    have h1 : M₁.Defines p.1 := defines_of_mem hp
    have h2 : ¬ M₂.Defines p.1 := fun hd => h p.1 ⟨h1, hd⟩
    cases hlu : M₂.lookup p.1 with
    | none => simp
    | some _ =>
      exfalso
      apply h2
      simp [Module.Defines, hlu]
  · intro h fn ⟨h1, h2⟩
    simp only [Module.Defines] at h1 h2
    cases hlu : M₁.lookup fn with
    | none => simp [hlu] at h1
    | some b₁ =>
      have hmem := mem_lookup_some hlu
      simp only [linkableBool, List.all_eq_true, Bool.not_eq_true'] at h
      have hb := h (fn, b₁) hmem
      simp [hb] at h2

instance (M₁ M₂ : Module) : Decidable (Linkable M₁ M₂) :=
  decidable_of_iff (linkableBool M₁ M₂ = true) (linkable_iff_linkableBool M₁ M₂).symm

/-- Link two modules by combining their symbol tables (`M₁ ++ M₂`).
Intended for use under `Linkable M₁ M₂`, where symbol lookup is independent of order.
Captures static linking of two disjoint compilation units. -/
def link (M₁ M₂ : Module) : Module := M₁ ++ M₂

/-- Every function called syntactically inside `e` satisfies predicate `P`. -/
def Expr.CalleesIn (P : Fname → Prop) : Expr → Prop
  | .lit _ => True
  | .var => True
  | .add e₁ e₂ => e₁.CalleesIn P ∧ e₂.CalleesIn P
  | .sub e₁ e₂ => e₁.CalleesIn P ∧ e₂.CalleesIn P
  | .mul e₁ e₂ => e₁.CalleesIn P ∧ e₂.CalleesIn P
  | .ifLe e₁ e₂ eThen eElse =>
      e₁.CalleesIn P ∧ e₂.CalleesIn P ∧ eThen.CalleesIn P ∧ eElse.CalleesIn P
  | .choose e₁ e₂ => e₁.CalleesIn P ∧ e₂.CalleesIn P
  | .call fn arg => P fn ∧ arg.CalleesIn P

/-- Boolean checker for `Expr.CalleesIn`. -/
def Expr.calleesInBool (P : Fname → Bool) : Expr → Bool
  | .lit _ => true
  | .var => true
  | .add e₁ e₂ => e₁.calleesInBool P && e₂.calleesInBool P
  | .sub e₁ e₂ => e₁.calleesInBool P && e₂.calleesInBool P
  | .mul e₁ e₂ => e₁.calleesInBool P && e₂.calleesInBool P
  | .ifLe e₁ e₂ eThen eElse =>
      e₁.calleesInBool P && e₂.calleesInBool P && eThen.calleesInBool P && eElse.calleesInBool P
  | .choose e₁ e₂ => e₁.calleesInBool P && e₂.calleesInBool P
  | .call fn arg => P fn && arg.calleesInBool P

theorem Expr.calleesIn_iff_bool {P : Fname → Prop} {p : Fname → Bool}
    (hp : ∀ fn, P fn ↔ p fn = true) (e : Expr) :
    e.CalleesIn P ↔ e.calleesInBool p = true := by
  induction e with
  | lit _ => simp [Expr.CalleesIn, Expr.calleesInBool]
  | var => simp [Expr.CalleesIn, Expr.calleesInBool]
  | add e₁ e₂ ih₁ ih₂ =>
    simp [Expr.CalleesIn, Expr.calleesInBool, ih₁, ih₂]
  | sub e₁ e₂ ih₁ ih₂ =>
    simp [Expr.CalleesIn, Expr.calleesInBool, ih₁, ih₂]
  | mul e₁ e₂ ih₁ ih₂ =>
    simp [Expr.CalleesIn, Expr.calleesInBool, ih₁, ih₂]
  | ifLe e₁ e₂ eThen eElse ih₁ ih₂ ihT ihE =>
    simp [Expr.CalleesIn, Expr.calleesInBool, ih₁, ih₂, ihT, ihE, and_assoc]
  | choose e₁ e₂ ih₁ ih₂ =>
    simp [Expr.CalleesIn, Expr.calleesInBool, ih₁, ih₂]
  | call fn arg ih =>
    simp [Expr.CalleesIn, Expr.calleesInBool, hp fn, ih]

/-- A module is syntactically closed if every call inside every reachable definition
targets a function defined in the same module.
Captures a complete self-contained program with no unresolved external symbols. -/
def ClosedModule (M : Module) : Prop :=
  ∀ fn body, M.lookup fn = some body → body.CalleesIn M.Defines

/-- Boolean checker for `ClosedModule`. -/
def closedModuleBool (M : Module) : Bool :=
  M.all (fun p =>
    match M.lookup p.1 with
    | some body => body.calleesInBool (fun fn => (M.lookup fn).isSome)
    | none => true)

theorem closedModule_iff_bool (M : Module) :
    ClosedModule M ↔ closedModuleBool M = true := by
  have hp : ∀ fn, M.Defines fn ↔ (M.lookup fn).isSome = true := fun _ => Iff.rfl
  constructor
  · intro h
    simp only [closedModuleBool, List.all_eq_true]
    intro p _
    cases hlu : M.lookup p.1 with
    | none => simp
    | some body =>
      exact (Expr.calleesIn_iff_bool hp body).1 (h p.1 body hlu)
  · intro h fn body hlu
    simp only [closedModuleBool, List.all_eq_true] at h
    have hb := h (fn, body) (mem_lookup_some hlu)
    simp only [hlu] at hb
    exact (Expr.calleesIn_iff_bool hp body).2 hb

instance (M : Module) : Decidable (ClosedModule M) :=
  decidable_of_iff (closedModuleBool M = true) (closedModule_iff_bool M).symm

/-- Structural evaluator for expressions given a parameter value `x` and a call handler
`callFn`. Captures one intra-procedural big-step evaluation phase parameterized by
callee evaluation. -/
def evalExprWith (callFn : Fname → Int → List Outcome) (x : Int) : Expr → List Outcome
  | .lit n => [.val n]
  | .var => [.val x]
  | .add e₁ e₂ =>
      (evalExprWith callFn x e₁).flatMap fun
        | .val v₁ =>
            (evalExprWith callFn x e₂).map fun
              | .val v₂ => .val (v₁ + v₂)
              | o => o
        | o => [o]
  | .sub e₁ e₂ =>
      (evalExprWith callFn x e₁).flatMap fun
        | .val v₁ =>
            (evalExprWith callFn x e₂).map fun
              | .val v₂ => .val (v₁ - v₂)
              | o => o
        | o => [o]
  | .mul e₁ e₂ =>
      (evalExprWith callFn x e₁).flatMap fun
        | .val v₁ =>
            (evalExprWith callFn x e₂).map fun
              | .val v₂ => .val (v₁ * v₂)
              | o => o
        | o => [o]
  | .ifLe e₁ e₂ eThen eElse =>
      (evalExprWith callFn x e₁).flatMap fun
        | .val v₁ =>
            (evalExprWith callFn x e₂).flatMap fun
              | .val v₂ =>
                  if v₁ ≤ v₂ then evalExprWith callFn x eThen
                  else evalExprWith callFn x eElse
              | o => [o]
        | o => [o]
  | .choose e₁ e₂ =>
      evalExprWith callFn x e₁ ++ evalExprWith callFn x e₂
  | .call fn eArg =>
      (evalExprWith callFn x eArg).flatMap fun
        | .val vArg => callFn fn vArg
        | o => [o]

/-- Fuel-indexed big-step evaluator for a module call `fn(arg)`.
At fuel `0`, any call immediately returns `[.outOfFuel]`. At fuel `fuel + 1`, calling
an undefined function returns `[.undefinedCall]`; otherwise the function body is
evaluated with callee calls decremented to `fuel`.
Captures bounded call-depth operational semantics of a module. -/
def eval : Nat → Module → Fname → Int → List Outcome
  | 0, _, _, _ => [.outOfFuel]
  | fuel + 1, P, fn, arg =>
      match P.lookup fn with
      | none => [.undefinedCall]
      | some body => evalExprWith (eval fuel P) arg body

/-- `HasBehavior entry P fuel arg out` means `out` is a possible outcome when calling
function `entry` on argument `arg` in module `P` with call-depth fuel `fuel`.
Captures the observable finite-fuel behaviour relation of a program. -/
def HasBehavior (entry : Fname) (P : Module) (fuel : Nat) (arg : Int) (out : Outcome) : Prop :=
  out ∈ eval fuel P entry arg

instance (entry : Fname) (P : Module) (fuel : Nat) (arg : Int) (out : Outcome) :
    Decidable (HasBehavior entry P fuel arg out) :=
  inferInstanceAs (Decidable (out ∈ eval fuel P entry arg))

/-- Single-entry refinement of a possibly open program: at every fuel and argument, every
outcome of `P'` at `entry` is also an outcome of `P` at `entry`, at the *same* fuel.
`P` and `P'` need not be closed: a call to a name neither defines yields `undefinedCall`.
Captures backward behaviour inclusion (reduction of nondeterminism) observed in lockstep
call depth; `outOfFuel` and `undefinedCall` are compared like any other outcome. -/
def EntryRefines (entry : Fname) (P P' : Module) : Prop :=
  ∀ fuel arg out, HasBehavior entry P' fuel arg out → HasBehavior entry P fuel arg out

/-- Standalone refinement: `M'` refines `M` at every entry point when both are run on
their own, with no other module linked (unresolved names yield `undefinedCall`).
Captures "the transformed module, viewed as a whole program, refines the original" at all
of its entry points. For closed modules this is the natural notion of closed-program
refinement; for open modules it ignores everything an importing context could supply. -/
def StandaloneRefines (M M' : Module) : Prop :=
  ∀ entry, EntryRefines entry M M'

/-- Contextual refinement of modules: for every context module `C` that is disjoint from
both `M` and `M'`, and every entry name `entry` (defined by `C`, by the module, or by
neither), `link C M'` refines `link C M` at `entry` (`EntryRefines`).
Contexts are arbitrary modules: they need not close the program, they may call any
function of the module, and the module may call theirs (callbacks).
Properties of this particular definition (each proved in this package): outcomes are
compared in lockstep call depth, so `CtxRefines` constrains divergence and fixes call
depth; every defined function is observable, so `CtxRefines M M'` forces equal domains
(`ctxRefines_sameDom`) and there are no private helper functions; `undefinedCall` is an
ordinary observable outcome. -/
def CtxRefines (M M' : Module) : Prop :=
  ∀ C, Linkable C M → Linkable C M' → ∀ entry, EntryRefines entry (link C M) (link C M')

/-- `MayDiverge P entry arg`: calling `entry` on `arg` in `P` can exceed every call-depth
bound, i.e. `outOfFuel` is a possible outcome at every fuel. Because `choose` branching is
binary, by König's lemma this is equivalent to the existence of an infinite chain of
nested calls in some execution (that equivalence is not formalized here).
Captures may-divergence of a call. -/
def MayDiverge (P : Module) (entry : Fname) (arg : Int) : Prop :=
  ∀ fuel, HasBehavior entry P fuel arg .outOfFuel

end Toy.Link
