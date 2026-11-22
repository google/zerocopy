/-!
# Law-dependent rewrites after capture: language, semantics, rewrites, laws

A toy model of the following situation. A verifier *captures* a program (fixes the
semantics it reasons about) at some point of a compilation pipeline. After the
capture point, the compiler runs a *rewrite* whose correctness depends on a
user-implementable trait obeying a law: for example, replacing a call of a `Copy`
type's `clone` method by a bitwise copy. The captured semantics calls the user's
impl; the compiled program runs the law-justified replacement code instead.

* Programs are straight-line lists of statements over a store of natural-number
  variables. A trait-method call `call i dst src` is resolved to the user impl of
  *instance* `i`, an arbitrary function from the argument value to a list of
  observable effects (emitted values) and a returned value.
* Every instance has a *contract*: the behaviour its trait law prescribes, and a
  safety mark. For a safe trait a violated law is defined behaviour; for an
  unsafe trait a violated law is undefined behaviour (UB) at the point where an
  execution relies on it (`relies` point, before or after the impl runs).
* Behaviours are traces of emitted values ending normally or in UB. Refinement
  treats UB as top, either prefix-preserving (the events emitted before the UB must
  be preserved) or whole-trace (UB permits any behaviour).

Everything here is a toy; no definition mirrors a real compiler's IR.
-/

namespace Toy.LawRewrite

/-- Values are natural numbers. -/
abbrev Val := Nat
/-- Variables are named by natural numbers. -/
abbrev Var := Nat
/-- Trait instances (one method each) are named by natural numbers. -/
abbrev Inst := Nat

/-- A store maps every variable to a value. -/
abbrev Store := Var → Val

/-- `σ.upd x v`: the store `σ` with variable `x` set to `v`. -/
def Store.upd (σ : Store) (x : Var) (v : Val) : Store :=
  fun y => if y = x then v else σ y

/-- An implementation of a one-method trait for one instance: from the argument
value, the list of observable effects it emits (in order) and the value it returns.
Impls are deterministic and total; they model user code, which may have effects
(for example, logging inside a `Clone` impl). -/
abbrev Impl := Val → List Val × Val

/-- A bitwise copy: no effect, returns its argument. The law of `Clone` for a `Copy`
type prescribes this behaviour. -/
def copyImpl : Impl := fun v => ([], v)

/-- The safety mark of a trait (`safeTrait` or `unsafeTrait`). For a safe trait the law is a "should": an impl
violating it is defined behaviour. For an unsafe trait the law is a proof
obligation of the implementer: an execution that relies on a violated law is UB. -/
inductive Safety where
  | safeTrait
  | unsafeTrait
  deriving DecidableEq

/-- Where the captured semantics of a call of an unsafe instance places the point at
which the execution relies on the law: `before` the impl runs (so a violation is UB
before any of the impl's effects) or `after` it (the impl's effects are emitted, then
the UB occurs). -/
inductive RelyPos where
  | before
  | after
  deriving DecidableEq

/-- The trait environment. `impl i` is the user impl of instance `i`; `contract i` is
the single-call pointwise behaviour the contract of `i`'s trait prescribes (the trait's
contract holds at `v` when `impl i v = contract i v`); `safety i` is the safety mark of
`i`'s trait. -/
structure Env where
  impl : Inst → Impl
  contract : Inst → Impl
  safety : Inst → Safety

/-- Statements.
* `set x v`: `x := v`.
* `out x`: emit the value of `x` (an observable event).
* `prim f dst src`: inline code with semantics `f`: emit `(f (σ src)).1`, then
  `dst := (f (σ src)).2`. Rewrites produce these; `prim copyImpl dst src` is a copy.
* `call i dst src`: `dst :=` the method of instance `i` applied to the value of `src`.
* `ub`: undefined behaviour. -/
inductive Stmt where
  | set (x : Var) (v : Val)
  | out (x : Var)
  | prim (f : Impl) (dst src : Var)
  | call (i : Inst) (dst src : Var)
  | ub

/-- A program is a straight-line list of statements. -/
abbrev Prog := List Stmt

/-- A behaviour: normal termination after emitting the trace `t`, or UB after
emitting `t`. -/
inductive Beh where
  | done (t : List Val)
  | ub (t : List Val)
  deriving DecidableEq

/-- The trace of a behaviour. -/
def Beh.trace : Beh → List Val
  | .done t => t
  | .ub t => t

/-- Prepend events to the trace of a behaviour. -/
def Beh.prepend (e : List Val) : Beh → Beh
  | .done t => .done (e ++ t)
  | .ub t => .ub (e ++ t)

/-- The possible results of one execution of a call: return after emitting effects
(`ret (effects, value)`), or emit some effects and then reach UB (`ubAfter effects`). -/
inductive CallRes where
  | ret (res : List Val × Val)
  | ubAfter (effs : List Val)
  deriving DecidableEq

/-- Execution of a program, parametric in the meaning of calls: `calls i v` lists the
possible results of a call of instance `i` with argument value `v` (more than one
result means nondeterministic choice). `exec calls p σ` lists every behaviour of `p`
from store `σ`. -/
def exec (calls : Inst → Val → List CallRes) : Prog → Store → List Beh
  | [], _ => [.done []]
  | .set x v :: p, σ => exec calls p (σ.upd x v)
  | .out x :: p, σ => (exec calls p σ).map (Beh.prepend [σ x])
  | .prim f dst src :: p, σ =>
      (exec calls p (σ.upd dst (f (σ src)).2)).map (Beh.prepend (f (σ src)).1)
  | .call i dst src :: p, σ =>
      (calls i (σ src)).flatMap fun
        | .ret r => (exec calls p (σ.upd dst r.2)).map (Beh.prepend r.1)
        | .ubAfter e => [.ub e]
  | .ub :: _, _ => [.ub []]

/-! ## Rewrites -/

/-- A law-dependent rewrite: every call of an instance `i` with `targets i = true` is
replaced by inline code `prim (repl i)`. Example: clone→copy on the instances of
`Copy` types, with `repl i = copyImpl`. -/
structure Rewrite where
  targets : Inst → Bool
  repl : Inst → Impl

/-- The rewrite of one statement. -/
def Rewrite.rwStmt (ρ : Rewrite) : Stmt → Stmt
  | .call i dst src => if ρ.targets i then .prim (ρ.repl i) dst src else .call i dst src
  | s => s

/-- Apply a rewrite at every call site. -/
def Rewrite.apply (ρ : Rewrite) (p : Prog) : Prog := p.map ρ.rwStmt

/-- Apply a rewrite at the selected sites: statement number `k` (counting from
the start index) is rewritten iff `S k = true`. With `S` constantly `true` this is
`Rewrite.apply`; with `S` constantly `false` it is the identity. -/
def Rewrite.applyAt (ρ : Rewrite) (S : Nat → Bool) : Nat → Prog → Prog
  | _, [] => []
  | k, s :: p => (if S k then ρ.rwStmt s else s) :: ρ.applyAt S (k + 1) p

/-- Apply a sequence of rewrites, first to last. -/
def applySeq (ρs : List Rewrite) (p : Prog) : Prog :=
  ρs.foldl (fun q ρ => ρ.apply q) p

/-! ## The meanings of calls: compiled, direct capture, relational capture -/

/-- Compiled code: a call runs the impl; nothing checks any law. -/
def compiledCalls (env : Env) : Inst → Val → List CallRes :=
  fun i v => [.ret (env.impl i v)]

/-- Direct capture: a call runs the impl. For an unsafe instance, the captured
semantics explicitly encodes reliance on the trait's contract at the call: if the impl
violates `env.contract` at the argument, the call is UB, placed before the impl's
effects (`before`) or after them (`after`). A verifier whose captured semantics runs
the user impl without encoding the unsafe contract as a relies-point UB check is in the
`compiledCalls` / `safeTrait` regime rather than this `unsafeTrait` regime. -/
def directCalls (env : Env) (pos : RelyPos) : Inst → Val → List CallRes :=
  fun i v =>
    match env.safety i with
    | .safeTrait => [.ret (env.impl i v)]
    | .unsafeTrait =>
      if env.impl i v = env.contract i v then [.ret (env.impl i v)]
      else
        match pos with
        | .before => [.ubAfter []]
        | .after => [.ubAfter (env.impl i v).1]

/-- Relational capture for a list of rewrites: a call of instance `i` may run the impl,
or the replacement of any listed rewrite that targets `i` (nondeterministic choice,
made independently at each call). Like `compiledCalls`, this semantics is law-free: it
ignores `env.safety` and `env.contract` and performs no relies-point UB check. -/
def relCalls (env : Env) (ρs : List Rewrite) : Inst → Val → List CallRes :=
  fun i v =>
    .ret (env.impl i v) ::
      ρs.filterMap (fun ρ => if ρ.targets i then some (.ret (ρ.repl i v)) else none)

/-- Behaviours of compiled code. -/
def compiled (env : Env) (p : Prog) (σ : Store) : List Beh :=
  exec (compiledCalls env) p σ

/-- Behaviours under the direct captured semantics. -/
def capDirect (env : Env) (pos : RelyPos) (p : Prog) (σ : Store) : List Beh :=
  exec (directCalls env pos) p σ

/-- Behaviours under the relational captured semantics for the rewrites `ρs`. -/
def capRel (env : Env) (ρs : List Rewrite) (p : Prog) (σ : Store) : List Beh :=
  exec (relCalls env ρs) p σ

/-! ## Refinement and verification -/

/-- Prefix-preserving improvement: the target behaviour `bt` equals the source
behaviour `bs`, or `bs` is UB after a prefix of `bt`'s trace. -/
def ImprovesPP (bt bs : Beh) : Prop :=
  bt = bs ∨ ∃ t, bs = .ub t ∧ t <+: bt.trace

/-- Whole-trace improvement: `bt = bs`, or `bs` is UB (after any trace). -/
def ImprovesWT (bt bs : Beh) : Prop :=
  bt = bs ∨ ∃ t, bs = .ub t

/-- `RefinesPP src tgt`: every target behaviour improves some source behaviour
(prefix-preserving). -/
def RefinesPP (src tgt : List Beh) : Prop :=
  ∀ bt ∈ tgt, ∃ bs ∈ src, ImprovesPP bt bs

/-- `RefinesWT src tgt`: every target behaviour improves some source behaviour
(whole-trace). -/
def RefinesWT (src tgt : List Beh) : Prop :=
  ∀ bt ∈ tgt, ∃ bs ∈ src, ImprovesWT bt bs

/-- `Sat bs spec`: every behaviour in `bs` satisfies `spec`. A verifier proving `spec`
of a captured program establishes `Sat` of its captured behaviours. -/
def Sat (bs : List Beh) (spec : Beh → Prop) : Prop :=
  ∀ b ∈ bs, spec b

/-- A specification that no UB behaviour satisfies. -/
def UBFreeSpec (spec : Beh → Prop) : Prop :=
  ∀ t, ¬ spec (.ub t)

instance instDecidableImprovesPP (bt bs : Beh) : Decidable (ImprovesPP bt bs) :=
  match bs with
  | .done t =>
    decidable_of_iff (bt = .done t) (by
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨u, hu, _⟩)
        · exact h
        · cases hu)
  | .ub t =>
    decidable_of_iff (t <+: bt.trace) (by
      constructor
      · intro h; exact Or.inr ⟨t, rfl, h⟩
      · rintro (h | ⟨u, hu, hp⟩)
        · subst h; exact List.prefix_refl _
        · cases hu; exact hp)

instance instDecidableImprovesWT (bt bs : Beh) : Decidable (ImprovesWT bt bs) :=
  match bs with
  | .done t =>
    decidable_of_iff (bt = .done t) (by
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨u, hu⟩)
        · exact h
        · cases hu)
  | .ub t =>
    decidable_of_iff True (by
      constructor
      · intro _; exact Or.inr ⟨t, rfl⟩
      · intro _; trivial)

instance instDecidableRefinesPP (src tgt : List Beh) : Decidable (RefinesPP src tgt) := by
  unfold RefinesPP; infer_instance

instance instDecidableRefinesWT (src tgt : List Beh) : Decidable (RefinesWT src tgt) := by
  unfold RefinesWT; infer_instance

instance instDecidableSat (bs : List Beh) (spec : Beh → Prop) [DecidablePred spec] :
    Decidable (Sat bs spec) := by
  unfold Sat; infer_instance

/-! ## Laws and the calls an execution reaches -/

/-- `LawAt env ρ i v`: at argument `v`, the impl of instance `i` agrees with the
replacement code that `ρ` substitutes for its calls (same effects, same returned
value). For clone→copy (`ρ.repl i = copyImpl`) this is the `Clone` law of a `Copy`
type at `v`: the clone has no effect and returns its argument. -/
def LawAt (env : Env) (ρ : Rewrite) (i : Inst) (v : Val) : Prop :=
  env.impl i v = ρ.repl i v

/-- `Reaches env p σ i v`: the execution of `p` from `σ` in which every call runs its
impl (compiled code, no law checked) reaches a call of instance `i` whose argument
has value `v`. The execution stops at `ub`. -/
def Reaches (env : Env) : Prog → Store → Inst → Val → Prop
  | [], _, _, _ => False
  | .set x v :: p, σ, i, w => Reaches env p (σ.upd x v) i w
  | .out _ :: p, σ, i, w => Reaches env p σ i w
  | .prim f dst src :: p, σ, i, w => Reaches env p (σ.upd dst (f (σ src)).2) i w
  | .call j dst src :: p, σ, i, w =>
      (j = i ∧ σ src = w) ∨ Reaches env p (σ.upd dst (env.impl j (σ src)).2) i w
  | .ub :: _, _, _, _ => False

/-- The law of `ρ` holds at every call of a targeted instance that the execution of
`p` from `σ` reaches (`Reaches`), at the argument it reaches it with. -/
def LawOnReached (env : Env) (ρ : Rewrite) (p : Prog) (σ : Store) : Prop :=
  ∀ i v, ρ.targets i = true → Reaches env p σ i v → LawAt env ρ i v

/-- The law of `ρ` holds at every targeted instance and every argument. -/
def LawOnTargets (env : Env) (ρ : Rewrite) : Prop :=
  ∀ i, ρ.targets i = true → ∀ v, LawAt env ρ i v

/-- `ContextSafeAt env pos ρ i v`: replacing a call of instance `i` with argument `v`
by `ρ`'s code cannot be observed against the direct capture with relies position
`pos`: either the law holds at `v`, or `i` is unsafe, its impl violates the
contract at `v` (so the direct capture is UB at that call), and that UB precedes every
divergence: the relies point is `before`, or it is `after` and the impl's effects at
`v` are a prefix of the replacement's effects at `v`. -/
def ContextSafeAt (env : Env) (pos : RelyPos) (ρ : Rewrite) (i : Inst) (v : Val) : Prop :=
  LawAt env ρ i v ∨
    (env.safety i = .unsafeTrait ∧ env.impl i v ≠ env.contract i v ∧
      (pos = .before ∨ (env.impl i v).1 <+: (ρ.repl i v).1))

/-- Every instance that `ρ` targets belongs to an unsafe trait. -/
def TargetsUnsafe (env : Env) (ρ : Rewrite) : Prop :=
  ∀ i, ρ.targets i = true → env.safety i = .unsafeTrait

/-- `ρ` substitutes, at every targeted instance, exactly the behaviour the contract of
that instance prescribes. -/
def ReplIsContract (env : Env) (ρ : Rewrite) : Prop :=
  ∀ i, ρ.targets i = true → ρ.repl i = env.contract i

/-- No instance is targeted by both rewrites. -/
def TargetsDisjoint (ρ₁ ρ₂ : Rewrite) : Prop :=
  ∀ i, ρ₁.targets i = true → ρ₂.targets i = false

/-- Every replacement that `ρ` can substitute is among the replacements of the
rewrites `ρs` at the same instance. -/
def CoveredBy (ρs : List Rewrite) (ρ : Rewrite) : Prop :=
  ∀ i, ρ.targets i = true → ∃ ρ' ∈ ρs, ρ'.targets i = true ∧ ρ'.repl i = ρ.repl i

/-- The probe context for instance `i` at argument `v`: set variable `0` to `v`, call
`i` on it into variable `1`, emit variable `1`. -/
def probe (i : Inst) (v : Val) : Prog :=
  [.set 0 v, .call i 1 0, .out 1]

/-- `callsSome R p`: some statement of `p` is a call of an instance `i` with
`R i = true`. -/
def callsSome (R : Inst → Bool) (p : Prog) : Bool :=
  p.any fun
    | .call i _ _ => R i
    | _ => false

end Toy.LawRewrite
