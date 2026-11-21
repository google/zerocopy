/-!
# Store laws: definitions

A self-contained toy theory of the simplest effectful interface: one mutable
cell holding a value of type `S`, accessed through `get` and `put`.

* `Prog S V` is the free program syntax (the free monad on the signature
  `get` (arity `S`) and `put s` (arity 1)); `Prog.ret v` plays the role of a
  variable or returned value.
* `run` is the intended semantics: a program denotes a state transformer
  `S → V × S` (final value and final cell content, from each initial cell
  content).
* A `Model S X` is an algebra for the signature on an arbitrary carrier `X`:
  any interpretation of `get` and `put`.  Every monad with `get`/`put`
  operations yields such algebras (`get k := getM >>= k`, `put s x := putM s >> x`),
  so algebras are the most permissive notion of model.  The carrier is
  everything an external observer of a model (its `run`) can see.
* The four standard laws (get–get, get–put, put–get, put–put) are separate
  named `Prop`s about a model, required to hold as equations in the carrier
  (strict satisfaction).  `GetGetVia` etc. are the weaker observational
  versions, required to hold only after an observation map `obs : X → O`:
  each compares the two sides of a law instance at top level after applying
  `obs`.  This is not behavioral (contextual) satisfaction, which compares
  the two sides in every observable context; for a constant `obs` every model
  satisfies all four `...Via` laws (`laws_via_const_hold`).
* `Derivable L` is equational derivability between programs from the laws in
  the law set `L` (least congruence containing every instance of those laws).
* `ExtDerivable p₀ q₀` is derivability from all four laws plus every
  substitution instance of the extra equation `p₀ = q₀`.

Each law or property is a separate named `Prop`, so theorems can name exactly
the hypotheses they use.
-/

namespace Toy.StoreLaws

/-! ## Program syntax -/

/-- Programs over one mutable cell of type `S`, returning a value of type `V`.

* `ret v` returns `v` (equivalently: a variable `v` in equational reasoning);
* `get k` reads the cell and continues with `k s` where `s` is the value read;
* `put s p` overwrites the cell with `s` and continues with `p`.

This is the free monad on the `get`/`put` signature: programs are already in
bind-normal form, so the monad laws hold as literal equalities of programs
(`Prog.bind_ret`, `Prog.ret_bind`, `Prog.bind_assoc`). -/
inductive Prog (S V : Type) : Type where
  | ret : V → Prog S V
  | get : (S → Prog S V) → Prog S V
  | put : S → Prog S V → Prog S V

namespace Prog

variable {S V W : Type}

/-- Monadic bind (substitution of programs for returned values / variables). -/
def bind : Prog S V → (V → Prog S W) → Prog S W
  | ret v, f => f v
  | get k, f => get (fun s => bind (k s) f)
  | put s p, f => put s (bind p f)

end Prog

open Prog

/-- The intended semantics of a program: from initial cell content `s`, the
returned value and the final cell content. -/
def run {S V : Type} : Prog S V → S → V × S
  | .ret v, s => (v, s)
  | .get k, s => run (k s) s
  | .put t p, _ => run p t

/-- Observational equivalence: same returned value and same final cell
content, from every initial cell content, in the intended semantics. -/
def ObsEq {S V : Type} (p q : Prog S V) : Prop := run p = run q

/-- The canonical program `get (fun s => put (f s) (ret (g s)))`: read once,
write once, return. -/
def canon {S V : Type} (f : S → S) (g : S → V) : Prog S V :=
  .get (fun s => .put (f s) (.ret (g s)))

/-- The canonical program whose intended semantics is the observation `o`
(final cell content `(o s).2`, result `(o s).1`). -/
def nf {S V : Type} (o : S → V × S) : Prog S V :=
  canon (fun s => (o s).2) (fun s => (o s).1)

/-! ## Models -/

/-- A model of the `get`/`put` signature on carrier `X`: an arbitrary
interpretation of `get` (an `S`-indexed choice) and of `put s` (a unary
operation).  No law is assumed. -/
structure Model (S X : Type) where
  /-- Interpretation of reading the cell. -/
  get : (S → X) → X
  /-- Interpretation of writing `s` to the cell. -/
  put : S → X → X

/-- Interpretation of programs in a model, given a valuation `ρ` of returned
values (variables) in the carrier. -/
def Model.interp {S X V : Type} (M : Model S X) (ρ : V → X) : Prog S V → X
  | .ret v => ρ v
  | .get k => M.get (fun s => M.interp ρ (k s))
  | .put s p => M.put s (M.interp ρ p)

/-- The intended model: carrier `S → V × S`, `get` passes the current cell
content to the continuation, `put t` replaces it. -/
def intended (S V : Type) : Model S (S → V × S) where
  get k := fun s => k s s
  put t x := fun _ => x t

/-- The valuation used with `intended`: return `v` without touching the cell. -/
def intendedRet {S V : Type} (v : V) : S → V × S := fun s => (v, s)

/-! ## The four laws (strict satisfaction: equations in the carrier) -/

/-- get–get: two consecutive reads see the same value. -/
def GetGet {S X : Type} (M : Model S X) : Prop :=
  ∀ k : S → S → X, M.get (fun s => M.get (fun s' => k s s')) = M.get (fun s => k s s)

/-- get–put: reading the cell and writing the value read back is a no-op. -/
def GetPut {S X : Type} (M : Model S X) : Prop :=
  ∀ x : X, M.get (fun s => M.put s x) = x

/-- put–get: a read right after `put s` sees `s`. -/
def PutGet {S X : Type} (M : Model S X) : Prop :=
  ∀ (s : S) (k : S → X), M.put s (M.get k) = M.put s (k s)

/-- put–put: of two consecutive writes, only the second matters. -/
def PutPut {S X : Type} (M : Model S X) : Prop :=
  ∀ (s s' : S) (x : X), M.put s (M.put s' x) = M.put s' x

/-- A model satisfying all four laws strictly. -/
def Lawful {S X : Type} (M : Model S X) : Prop :=
  GetGet M ∧ GetPut M ∧ PutGet M ∧ PutPut M

/-- Names of the four laws. -/
inductive Law where
  | getGet
  | getPut
  | putGet
  | putPut
  deriving DecidableEq, Repr

/-- The strict law named by `l`. -/
def Law.Holds {S X : Type} : Law → Model S X → Prop
  | .getGet, M => GetGet M
  | .getPut, M => GetPut M
  | .putGet, M => PutGet M
  | .putPut, M => PutPut M

/-- A set of laws. -/
abbrev LawSet := Law → Prop

/-- All four laws. -/
def allLaws : LawSet := fun _ => True

/-- All laws except `l`. -/
abbrev lawsExcept (l : Law) : LawSet := fun l' => l' ≠ l

/-- `M` satisfies (strictly) every law in `L`. -/
def SatisfiesAll {S X : Type} (L : LawSet) (M : Model S X) : Prop :=
  ∀ l, L l → l.Holds M

/-- Semantic entailment among laws for one-cell models with `S = Bool`:
every model (on any carrier) that satisfies all laws in `Γ` satisfies `l`. -/
def EntailsBool (Γ : LawSet) (l : Law) : Prop :=
  ∀ (X : Type) (M : Model Bool X), SatisfiesAll Γ M → l.Holds M

/-! ## Observational satisfaction (laws checked through `obs`)

Each `...Via obs M` requires the two sides of every instance of a law to have
the same image under `obs`.  The comparison is at top level: the two sides are
not placed in further contexts before observing.  For an injective `obs` this is
equivalent to strict satisfaction; for a constant `obs` it holds for every model
(`laws_via_const_hold`); for a non-injective `obs` the `...Via` laws need not
obey the entailments of the strict laws
(`getGetVia_not_entailed_by_getPutVia_putGetVia`). -/

/-- get–get, checked only through the observation `obs`. -/
def GetGetVia {S X O : Type} (obs : X → O) (M : Model S X) : Prop :=
  ∀ k : S → S → X,
    obs (M.get (fun s => M.get (fun s' => k s s'))) = obs (M.get (fun s => k s s))

/-- get–put, checked only through the observation `obs`. -/
def GetPutVia {S X O : Type} (obs : X → O) (M : Model S X) : Prop :=
  ∀ x : X, obs (M.get (fun s => M.put s x)) = obs x

/-- put–get, checked only through the observation `obs`. -/
def PutGetVia {S X O : Type} (obs : X → O) (M : Model S X) : Prop :=
  ∀ (s : S) (k : S → X), obs (M.put s (M.get k)) = obs (M.put s (k s))

/-- put–put, checked only through the observation `obs`. -/
def PutPutVia {S X O : Type} (obs : X → O) (M : Model S X) : Prop :=
  ∀ (s s' : S) (x : X), obs (M.put s (M.put s' x)) = obs (M.put s' x)

/-! ## Equational derivability between programs -/

/-- `Derivable L p q`: the equation `p = q` is derivable from the laws in `L`
by equational reasoning: reflexivity, symmetry, transitivity, congruence under
`get` (pointwise in the value read) and `put s`, and every instance of each law
in `L` with arbitrary continuations.  Closure under substitution (`bind`) is a
lemma (`Derivable.bind_left`), not a rule. -/
inductive Derivable {S V : Type} (L : LawSet) : Prog S V → Prog S V → Prop where
  | refl (p : Prog S V) : Derivable L p p
  | symm {p q : Prog S V} : Derivable L p q → Derivable L q p
  | trans {p q r : Prog S V} : Derivable L p q → Derivable L q r → Derivable L p r
  | get_congr {k k' : S → Prog S V} :
      (∀ s, Derivable L (k s) (k' s)) → Derivable L (.get k) (.get k')
  | put_congr (s : S) {p q : Prog S V} :
      Derivable L p q → Derivable L (.put s p) (.put s q)
  | getGet (h : L .getGet) (k : S → S → Prog S V) :
      Derivable L (.get fun s => .get fun s' => k s s') (.get fun s => k s s)
  | getPut (h : L .getPut) (p : Prog S V) :
      Derivable L (.get fun s => .put s p) p
  | putGet (h : L .putGet) (s : S) (k : S → Prog S V) :
      Derivable L (.put s (.get k)) (.put s (k s))
  | putPut (h : L .putPut) (s s' : S) (p : Prog S V) :
      Derivable L (.put s (.put s' p)) (.put s' p)

/-- `ExtDerivable p₀ q₀ p q`: `p = q` is derivable from the four laws together
with every substitution instance `p₀.bind σ = q₀.bind σ` (`σ : V → Prog S V`)
of the extra equation `p₀ = q₀`, closed under symmetry, transitivity and
congruence.  This is the equational theory obtained by adding the axiom
`p₀ = q₀` (with its values read as variables) to the four laws. -/
inductive ExtDerivable {S V : Type} (p₀ q₀ : Prog S V) : Prog S V → Prog S V → Prop where
  | of_derivable {p q : Prog S V} : Derivable allLaws p q → ExtDerivable p₀ q₀ p q
  | inst (σ : V → Prog S V) : ExtDerivable p₀ q₀ (p₀.bind σ) (q₀.bind σ)
  | symm {p q : Prog S V} : ExtDerivable p₀ q₀ p q → ExtDerivable p₀ q₀ q p
  | trans {p q r : Prog S V} :
      ExtDerivable p₀ q₀ p q → ExtDerivable p₀ q₀ q r → ExtDerivable p₀ q₀ p r
  | get_congr {k k' : S → Prog S V} :
      (∀ s, ExtDerivable p₀ q₀ (k s) (k' s)) → ExtDerivable p₀ q₀ (.get k) (.get k')
  | put_congr (s : S) {p q : Prog S V} :
      ExtDerivable p₀ q₀ p q → ExtDerivable p₀ q₀ (.put s p) (.put s q)

/-- Control relation for `ExtDerivable`: derivability from the four laws together
with the single extra equation `p₀ = q₀` itself (no substitution instances
`p₀.bind σ = q₀.bind σ`), closed under symmetry, transitivity and congruence.
It differs from `ExtDerivable` exactly in replacing the rule `inst` by `base`. -/
inductive ExtDerivableNoSubst {S V : Type} (p₀ q₀ : Prog S V) : Prog S V → Prog S V → Prop where
  | of_derivable {p q : Prog S V} : Derivable allLaws p q → ExtDerivableNoSubst p₀ q₀ p q
  | base : ExtDerivableNoSubst p₀ q₀ p₀ q₀
  | symm {p q : Prog S V} : ExtDerivableNoSubst p₀ q₀ p q → ExtDerivableNoSubst p₀ q₀ q p
  | trans {p q r : Prog S V} :
      ExtDerivableNoSubst p₀ q₀ p q → ExtDerivableNoSubst p₀ q₀ q r →
        ExtDerivableNoSubst p₀ q₀ p r
  | get_congr {k k' : S → Prog S V} :
      (∀ s, ExtDerivableNoSubst p₀ q₀ (k s) (k' s)) →
        ExtDerivableNoSubst p₀ q₀ (.get k) (.get k')
  | put_congr (s : S) {p q : Prog S V} :
      ExtDerivableNoSubst p₀ q₀ p q → ExtDerivableNoSubst p₀ q₀ (.put s p) (.put s q)

/-! ## Comparison maps out of the intended observations -/

/-- The comparison map from intended observations to a model `M` under the
valuation `ρ`: interpret the canonical program of the observation. -/
def Model.fromObs {S X V : Type} (M : Model S X) (ρ : V → X) (o : S → V × S) : X :=
  M.get (fun s => M.put (o s).2 (ρ (o s).1))

/-- `h` is a homomorphism from the intended model on `V` (with returns
`intendedRet`) to `M` (with returns `ρ`): it maps returns to `ρ` and commutes
with `get` and `put`. -/
def IsHom {S X V : Type} (M : Model S X) (ρ : V → X) (h : (S → V × S) → X) : Prop :=
  (∀ v : V, h (intendedRet v) = ρ v) ∧
  (∀ k : S → S → V × S, h ((intended S V).get k) = M.get (fun s => h (k s))) ∧
  (∀ (t : S) (o : S → V × S), h ((intended S V).put t o) = M.put t (h o))

end Toy.StoreLaws
