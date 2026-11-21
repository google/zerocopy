# Store laws for one mutable cell: derived get–get, normal forms, Hilbert–Post completeness, and lawful but unfaithful models

## Summary

This package formalizes the four laws of a single mutable cell (get–get, get–put, put–get, put–put) in Lean 4 (`v4.34.1`, core Lean, no Mathlib). Programs `Prog S V` are trees of `get` and `put` operations over a cell of an arbitrary type `S`, returning values of type `V`; their intended meaning is the state-passing function `run`. A model `Model S X` interprets `get` and `put` on an arbitrary carrier type `X`, and a law holds *strictly* when it holds as an equation in `X` for all carrier elements. Laws compared after an observation `obs : X → O` (the `...Via` variants) are named as such wherever they occur.

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any concrete monad, programming language, library, storage device or verification tool.

What a reader should retain, one sentence per result (each sentence keeps the result's hypotheses; the full cards are under Findings):

1. `getGet_of_getPut_of_putGet`: for every cell type `S`, carrier `X` and model `M : Model S X`, if `M` satisfies get–put and put–get strictly, then `M` satisfies get–get strictly.
2. `getPut_putGet_putPut_independent_bool`: on a Boolean cell with Boolean results, with strict laws, the change-log model satisfies get–get, get–put and put–get and violates put–put; the writes-ignored model satisfies get–get, get–put and put–put and violates put–get; and the dirty-bit model satisfies get–get, put–get and put–put and violates get–put.
3. `getGet_not_entailed_by_pairs_with_putPut_bool`: on a Boolean cell with Boolean results, with strict laws, the read-to-clear model (reading resets the cell to false) satisfies get–put and put–put and violates get–get, and the faulting read-counter model (counts reads, every write faults) satisfies put–get and put–put and violates get–get.
4. `entailsBool_iff`: for models on a Boolean cell (any carrier, strict laws), a set Γ of the four laws entails a law `l` iff `l` is in Γ, or `l` is get–get and both get–put and put–get are in Γ.
5. `derivable_nf_of_getPut_putGet_putPut`: for every cell type `S`, result type `V` and law set `L` containing get–put, put–get and put–put, every program `p : Prog S V` is derivably equal from `L` to its canonical program `nf (run p)`, which reads once, writes `(run p s).2` and returns `(run p s).1`.
6. `canon_eq_of_derivable`: for every cell type `S`, result type `V` and law set `L`, if `canon f g` and `canon f' g'` are derivably equal from `L`, then `f = f'` and `g = g'`.
7. `derivable_iff_obsEq_of_getPut_putGet_putPut`: for every cell type `S`, result type `V` and law set `L` containing get–put, put–get and put–put, two programs `p q : Prog S V` are derivably equal from `L` iff `run p = run q`.
8. `interp_eq_fromObs_run_of_getPut_putGet_putPut`: for every model `M` on a carrier `X` that satisfies get–put, put–get and put–put strictly, every valuation `ρ : V → X` and every program `p`, `M.interp ρ p = M.fromObs ρ (run p)`, so the interpretation of `p` is determined by `run p` and `ρ`.
9. `interp_eq_of_obsEq_of_getPut_putGet_putPut`: for every model `M` that satisfies get–put, put–get and put–put strictly, every valuation `ρ` and all programs `p`, `q` with `run p = run q`, `M.interp ρ p = M.interp ρ q`.
10. `fromObs_isHom_unique_of_getPut_putGet_putPut`: for every model `M` that satisfies get–put, put–get and put–put strictly and every valuation `ρ : V → X`, `M.fromObs ρ` is a homomorphism from the intended model to `M` that sends `intendedRet v` to `ρ v`, and every such homomorphism equals it.
11. `getPut_putGet_putPut_iff_exists_surjective_isHom`: for every cell type `S`, carrier `X` and model `M : Model S X`, `M` satisfies get–put, put–get and put–put strictly iff some map from intended observations `S → X × S` to `X` is a homomorphism from the intended model with result type `X` to `M`, sends `intendedRet x` to `x`, and is surjective (the surjectivity condition is implied by the others: `isHom_id_surjective`).
12. `lawful_not_faithful`: on a Boolean cell with Boolean results, the value-only model satisfies all four laws strictly and, under the valuation `valueOnlyRet`, interprets `ret true` and `ret false` differently but `put true (ret true)` and `put false (ret true)` equally, although these two programs are not observationally equivalent; and the one-point model satisfies all four laws strictly and interprets `ret true` and `ret false` equally, although they are not observationally equivalent.
13. `forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial`: for every model `M : Model S X` that satisfies get–put, put–get and put–put strictly, if `X` has two distinct elements, then for all programs `p q : Prog S V`, `M` interprets `p` and `q` equally under every valuation `ρ : V → X` iff `run p = run q`.
14. `extDerivable_total_of_not_derivable`: for every cell type `S`, result type `V` and programs `p₀ q₀ : Prog S V` such that `p₀ = q₀` is not derivable from the four laws, the four laws together with every substitution instance `p₀.bind σ = q₀.bind σ` (`σ : V → Prog S V`) make every two programs of type `Prog S V` derivably equal.
15. `writeLog_via_distinguishes_obsEq`: on a Boolean cell with Boolean results, the write-log model satisfies all four laws when both sides of each law instance are compared after the log-forgetting observation `dropLog`, and under the valuation `logRet` it interprets `put true (put false (ret true))` and `put false (ret true)` differently, although they are observationally equivalent.
16. `writeLog_strict_profile_bool`: on a Boolean cell with Boolean results, the write-log model satisfies get–get and put–get strictly and violates get–put and put–put.
17. `readCounter_strict_profile_bool`: on a Boolean cell with Boolean results, the read-counter model satisfies put–put strictly and violates get–get, get–put and put–get.
18. `inertHidden_interp_eq`: for all types `S`, `H`, `V`, the inert-hidden model satisfies all four laws strictly, and under the valuation `pairRet` every program `p` started from `(s, h)` returns `(run p s).1` and ends in the state `((run p s).2, h)`.
19. `derivable_lawsExcept_getGet_iff`: for every cell type `S`, result type `V` and programs `p q : Prog S V`, `p = q` is derivable from get–put, put–get and put–put iff it is derivable from all four laws.
20. `drop_law_loses_nf`: on a Boolean cell with Boolean results, `ret true` is not derivably equal to its canonical program from the laws other than get–put, `put true (get ret)` is not from the laws other than put–get, and `put true (put false (ret true))` is not from the laws other than put–put; in each case the two programs are observationally equivalent.

Non-claims are listed under Boundaries, before anything else in that section; several of them block tempting stronger readings of the results above (for example, Results 12 and 15 show that "lawful" does not mean "faithful" at a fixed valuation, and that laws checked through an observation need not have the consequences of strict laws).

An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.

## Applicability

**Model fidelity: toy model.** One mutable cell of an arbitrary type `S`. Programs are the free monad on `get` and `put`: well-founded trees in which every path reaches a `ret` leaf after finitely many steps (the height can be unbounded when `S` is infinite), with no recursion, no other effects and no second cell. Models are algebras on Lean types, so carriers are set-like. Laws are imposed strictly unless a `...Via obs` variant is named. Lean `leanprover/lean4:v4.34.1` with its core library; no Mathlib and no Lake dependencies.

The definitions are meant to capture the equational specification of a single mutable location as it appears in monadic interfaces (the `MonadState` laws of Gibbons–Hinze), in algebraic theories of global state (Plotkin–Power), and in handlers for state effects. The weird models are toy renderings of instrumented stores and devices: a store that logs writes, a log of value-changing writes, a device that drops writes, a modified flag set by every write, a read-to-clear register, a read counter, a store whose writes fault, and stores with a hidden component. Known gaps: no aliasing between several locations, no concurrency, no nontermination, no exceptions or other effects interacting with state, and continuations are arbitrary Lean functions rather than finitary program syntax.

Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about any concrete monad, programming language, library, storage device or verification tool.

**Subjects.** `REPORT.json` lists the Lean toolchain release used for the kernel checks and the primary sources whose results are re-derived or used as background. The Lean development does not depend on the sources: it restates their results in the vocabulary below and proves them from scratch.

### Key definitions

All quotes are verbatim from the package's Lean sources (namespace `Toy.StoreLaws`, with `open Prog` in the result files). Proved positive and negative examples for every definition are in `lean/Toy/StoreLaws/Examples.lean`.

**Programs and their intended meaning.** `Prog S V` captures pure, terminating, first-order programs over one cell: a `get` node branches on the value read, a `put` node records a write, and `ret` returns a value. `Prog.bind` is substitution of programs for returned values (it is declared as `bind` inside `namespace Prog`, so its quote below begins `def bind`). `run` is the intended state-passing semantics, and `ObsEq` (observational equivalence) compares final value and final cell content from every initial content. `canon f g` is the read-once, write-once, return program with write map `f` and result map `g`; `nf o` is the canonical program of an observation `o : S → V × S`.

```lean
-- Toy/StoreLaws/Defs.lean:48-51
inductive Prog (S V : Type) : Type where
  | ret : V → Prog S V
  | get : (S → Prog S V) → Prog S V
  | put : S → Prog S V → Prog S V
```

```lean
-- Toy/StoreLaws/Defs.lean:58-61
def bind : Prog S V → (V → Prog S W) → Prog S W
  | ret v, f => f v
  | get k, f => get (fun s => bind (k s) f)
  | put s p, f => put s (bind p f)
```

```lean
-- Toy/StoreLaws/Defs.lean:69-72
def run {S V : Type} : Prog S V → S → V × S
  | .ret v, s => (v, s)
  | .get k, s => run (k s) s
  | .put t p, _ => run p t
```

```lean
-- Toy/StoreLaws/Defs.lean:76
def ObsEq {S V : Type} (p q : Prog S V) : Prop := run p = run q
```

```lean
-- Toy/StoreLaws/Defs.lean:80-81
def canon {S V : Type} (f : S → S) (g : S → V) : Prog S V :=
  .get (fun s => .put (f s) (.ret (g s)))
```

```lean
-- Toy/StoreLaws/Defs.lean:85-86
def nf {S V : Type} (o : S → V × S) : Prog S V :=
  canon (fun s => (o s).2) (fun s => (o s).1)
```

**Models and strict laws.** A `Model S X` interprets reading and writing the cell on a carrier `X`; `Model.interp M ρ` interprets programs, sending returned values through the valuation `ρ : V → X`. The intended model `intended S V` is the state-transformer model on `S → V × S`, with returns `intendedRet`; it satisfies all four laws strictly (`intended_lawful`). The four laws are equations in the carrier quantified over all carrier elements, and `Lawful` is their conjunction.

```lean
-- Toy/StoreLaws/Defs.lean:93-97
structure Model (S X : Type) where
  /-- Interpretation of reading the cell. -/
  get : (S → X) → X
  /-- Interpretation of writing `s` to the cell. -/
  put : S → X → X
```

```lean
-- Toy/StoreLaws/Defs.lean:101-104
def Model.interp {S X V : Type} (M : Model S X) (ρ : V → X) : Prog S V → X
  | .ret v => ρ v
  | .get k => M.get (fun s => M.interp ρ (k s))
  | .put s p => M.put s (M.interp ρ p)
```

```lean
-- Toy/StoreLaws/Defs.lean:108-110
def intended (S V : Type) : Model S (S → V × S) where
  get k := fun s => k s s
  put t x := fun _ => x t
```

```lean
-- Toy/StoreLaws/Defs.lean:113
def intendedRet {S V : Type} (v : V) : S → V × S := fun s => (v, s)
```

```lean
-- Toy/StoreLaws/Defs.lean:118-119
def GetGet {S X : Type} (M : Model S X) : Prop :=
  ∀ k : S → S → X, M.get (fun s => M.get (fun s' => k s s')) = M.get (fun s => k s s)
```

```lean
-- Toy/StoreLaws/Defs.lean:122-123
def GetPut {S X : Type} (M : Model S X) : Prop :=
  ∀ x : X, M.get (fun s => M.put s x) = x
```

```lean
-- Toy/StoreLaws/Defs.lean:126-127
def PutGet {S X : Type} (M : Model S X) : Prop :=
  ∀ (s : S) (k : S → X), M.put s (M.get k) = M.put s (k s)
```

```lean
-- Toy/StoreLaws/Defs.lean:130-131
def PutPut {S X : Type} (M : Model S X) : Prop :=
  ∀ (s s' : S) (x : X), M.put s (M.put s' x) = M.put s' x
```

```lean
-- Toy/StoreLaws/Defs.lean:134-135
def Lawful {S X : Type} (M : Model S X) : Prop :=
  GetGet M ∧ GetPut M ∧ PutGet M ∧ PutPut M
```

**Law sets and entailment on a Boolean cell.** `Law` names the four laws, `LawSet` is a set of them, and `EntailsBool Γ l` says that every model on a Boolean cell (any carrier) satisfying every law in `Γ` satisfies `l`.

```lean
-- Toy/StoreLaws/Defs.lean:138-143
inductive Law where
  | getGet
  | getPut
  | putGet
  | putPut
  deriving DecidableEq, Repr
```

```lean
-- Toy/StoreLaws/Defs.lean:146-150
def Law.Holds {S X : Type} : Law → Model S X → Prop
  | .getGet, M => GetGet M
  | .getPut, M => GetPut M
  | .putGet, M => PutGet M
  | .putPut, M => PutPut M
```

```lean
-- Toy/StoreLaws/Defs.lean:153
abbrev LawSet := Law → Prop
```

```lean
-- Toy/StoreLaws/Defs.lean:156
def allLaws : LawSet := fun _ => True
```

```lean
-- Toy/StoreLaws/Defs.lean:159
abbrev lawsExcept (l : Law) : LawSet := fun l' => l' ≠ l
```

```lean
-- Toy/StoreLaws/Defs.lean:162-163
def SatisfiesAll {S X : Type} (L : LawSet) (M : Model S X) : Prop :=
  ∀ l, L l → l.Holds M
```

```lean
-- Toy/StoreLaws/Defs.lean:167-168
def EntailsBool (Γ : LawSet) (l : Law) : Prop :=
  ∀ (X : Type) (M : Model Bool X), SatisfiesAll Γ M → l.Holds M
```

**Laws through an observation.** The `...Via obs` variants compare the two sides of each law instance after applying `obs`, at top level. They capture laws checked through what an observer extracts from the carrier; they are not behavioral satisfaction, which compares the two sides in every observable context.

```lean
-- Toy/StoreLaws/Defs.lean:181-183
def GetGetVia {S X O : Type} (obs : X → O) (M : Model S X) : Prop :=
  ∀ k : S → S → X,
    obs (M.get (fun s => M.get (fun s' => k s s'))) = obs (M.get (fun s => k s s))
```

```lean
-- Toy/StoreLaws/Defs.lean:186-187
def GetPutVia {S X O : Type} (obs : X → O) (M : Model S X) : Prop :=
  ∀ x : X, obs (M.get (fun s => M.put s x)) = obs x
```

```lean
-- Toy/StoreLaws/Defs.lean:190-191
def PutGetVia {S X O : Type} (obs : X → O) (M : Model S X) : Prop :=
  ∀ (s : S) (k : S → X), obs (M.put s (M.get k)) = obs (M.put s (k s))
```

```lean
-- Toy/StoreLaws/Defs.lean:194-195
def PutPutVia {S X O : Type} (obs : X → O) (M : Model S X) : Prop :=
  ∀ (s s' : S) (x : X), obs (M.put s (M.put s' x)) = obs (M.put s' x)
```

**Derivability.** `Derivable L` is the least congruence on programs that contains every instance of the laws in `L`; closure under substitution is the lemma `Derivable.bind_left`. `ExtDerivable p₀ q₀` adds every substitution instance of the equation `p₀ = q₀`. `ExtDerivableNoSubst p₀ q₀` adds the single equation `p₀ = q₀` without its substitution instances and serves as a control for Result 14. Rule `get_congr` has one premise per value of `S`, so for infinite `S` these are infinitary proof systems.

```lean
-- Toy/StoreLaws/Defs.lean:204-219
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
```

```lean
-- Toy/StoreLaws/Defs.lean:226-235
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
```

```lean
-- Toy/StoreLaws/Defs.lean:241-252
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
```

**Homomorphisms from the intended model.** `M.fromObs ρ` sends an intended observation `o` to the canonical program of `o` interpreted in `M`; `IsHom M ρ h` says that `h` sends `intendedRet v` to `ρ v` and commutes with `get` and `put`.

```lean
-- Toy/StoreLaws/Defs.lean:258-259
def Model.fromObs {S X V : Type} (M : Model S X) (ρ : V → X) (o : S → V × S) : X :=
  M.get (fun s => M.put (o s).2 (ρ (o s).1))
```

```lean
-- Toy/StoreLaws/Defs.lean:264-267
def IsHom {S X V : Type} (M : Model S X) (ρ : V → X) (h : (S → V × S) → X) : Prop :=
  (∀ v : V, h (intendedRet v) = ρ v) ∧
  (∀ k : S → S → V × S, h ((intended S V).get k) = M.get (fun s => h (k s))) ∧
  (∀ (t : S) (o : S → V × S), h ((intended S V).put t o) = M.put t (h o))
```

### Concrete models and valuations

`valueOnly` forgets the final cell content; `unitModel` is the one-point model; `writeLog` logs every write; `changeLog` logs writes that change the cell (it assumes decidable equality on `S`); `writesIgnored` drops writes; `dirtyBit` sets a flag on every write, including writes of the value already held; `readToClear` resets the cell to `d` on every read; `faultingCounter` counts reads and faults on every write; `readCounter` counts reads; `inertHidden` carries a hidden component that no operation touches; `coupledHidden` flips a hidden bit whenever a write changes the cell; `fstViaModel` is a model whose laws are compared through `Prod.fst`. The `...Ret` definitions and `pairRet`, `pairFlipRet` are valuations. In `faultingCounter` and `readCounter` the count is an unbounded natural number (no wrapping).

```lean
-- Toy/StoreLaws/Models.lean:32-34
def valueOnly (S V : Type) : Model S (S → V) where
  get k := fun s => k s s
  put t x := fun _ => x t
```

```lean
-- Toy/StoreLaws/Models.lean:37
def valueOnlyRet {S V : Type} (v : V) : S → V := fun _ => v
```

```lean
-- Toy/StoreLaws/Models.lean:40-42
def unitModel (S : Type) : Model S Unit where
  get _ := ()
  put _ _ := ()
```

```lean
-- Toy/StoreLaws/Models.lean:47-49
def writeLog (S V : Type) : Model S (S → V × S × List S) where
  get k := fun s => k s s
  put t x := fun _ => ((x t).1, (x t).2.1, t :: (x t).2.2)
```

```lean
-- Toy/StoreLaws/Models.lean:52
def logRet {S V : Type} (v : V) : S → V × S × List S := fun s => (v, s, [])
```

```lean
-- Toy/StoreLaws/Models.lean:55-56
def dropLog {S V : Type} (x : S → V × S × List S) : S → V × S :=
  fun s => ((x s).1, (x s).2.1)
```

```lean
-- Toy/StoreLaws/Models.lean:60-62
def changeLog (S V : Type) [DecidableEq S] : Model S (S → V × S × List S) where
  get k := fun s => k s s
  put t x := fun s₀ => ((x t).1, (x t).2.1, if t = s₀ then (x t).2.2 else t :: (x t).2.2)
```

```lean
-- Toy/StoreLaws/Models.lean:65-67
def writesIgnored (S V : Type) : Model S (S → V × S) where
  get k := fun s => k s s
  put _ x := x
```

```lean
-- Toy/StoreLaws/Models.lean:71-73
def dirtyBit (S V : Type) : Model S (S × Bool → V × (S × Bool)) where
  get k := fun st => k st.1 st
  put t x := fun _ => x (t, true)
```

```lean
-- Toy/StoreLaws/Models.lean:76
def pairRet {S H V : Type} (v : V) : S × H → V × (S × H) := fun st => (v, st)
```

```lean
-- Toy/StoreLaws/Models.lean:80-82
def readToClear (S V : Type) (d : S) : Model S (S → V × S) where
  get k := fun s => k s d
  put t x := fun _ => x t
```

```lean
-- Toy/StoreLaws/Models.lean:86-88
def faultingCounter (S V : Type) : Model S (S → Option (V × S × Nat)) where
  get k := fun s => (k s s).map (fun r => (r.1, r.2.1, r.2.2 + 1))
  put _ _ := fun _ => none
```

```lean
-- Toy/StoreLaws/Models.lean:91
def faultingRet {S V : Type} (v : V) : S → Option (V × S × Nat) := fun s => some (v, s, 0)
```

```lean
-- Toy/StoreLaws/Models.lean:94-96
def readCounter (S V : Type) : Model S (S → V × S × Nat) where
  get k := fun s => ((k s s).1, (k s s).2.1, (k s s).2.2 + 1)
  put t x := fun _ => x t
```

```lean
-- Toy/StoreLaws/Models.lean:99
def counterRet {S V : Type} (v : V) : S → V × S × Nat := fun s => (v, s, 0)
```

```lean
-- Toy/StoreLaws/Models.lean:104-106
def inertHidden (S H V : Type) : Model S (S × H → V × (S × H)) where
  get k := fun st => k st.1 st
  put t x := fun st => x (t, st.2)
```

```lean
-- Toy/StoreLaws/Models.lean:110-111
def pairFlipRet {S V : Type} (v : V) : S × Bool → V × (S × Bool) :=
  fun st => (v, (st.1, !st.2))
```

```lean
-- Toy/StoreLaws/Models.lean:116-118
def coupledHidden (V : Type) : Model Bool (Bool × Bool → V × (Bool × Bool)) where
  get k := fun st => k st.1 st
  put t x := fun st => x (t, xor (xor st.1 t) st.2)
```

```lean
-- Toy/StoreLaws/Models.lean:124-126
def fstViaModel : Model Bool ((Bool → Bool) × (Bool → Bool)) where
  get k := (fun s => (k s).2 (!s), fun s => (k s).2 s)
  put t x := (fun _ => x.2 t, fun s => x.1 (!s))
```

**Law profiles.** ✓ means that the law holds strictly, by the named hypothesis-free theorem, for all `S` and `V` (all `H` for `inertHidden`, all `d` for `readToClear`; `changeLog` assumes decidable equality on `S`; `coupledHidden` is defined for the cell type `Bool` and all `V`). Each ✓ is non-vacuous: at the instance `S = V = Bool` the carrier is inhabited, so the law has instances. ✗ means that the named theorem proves that the law fails for `S = V = Bool` (for `readToClear`, with `d = false`). All named theorems are quoted under Findings › Auxiliary lemmas cited by name.

| model | get–get | get–put | put–get | put–put |
| :--- | :--- | :--- | :--- | :--- |
| `intended` | ✓ `intended_lawful` | ✓ `intended_lawful` | ✓ `intended_lawful` | ✓ `intended_lawful` |
| `valueOnly` | ✓ `valueOnly_lawful` | ✓ `valueOnly_lawful` | ✓ `valueOnly_lawful` | ✓ `valueOnly_lawful` |
| `unitModel` | ✓ `unitModel_lawful` | ✓ `unitModel_lawful` | ✓ `unitModel_lawful` | ✓ `unitModel_lawful` |
| `inertHidden` | ✓ `inertHidden_lawful` | ✓ `inertHidden_lawful` | ✓ `inertHidden_lawful` | ✓ `inertHidden_lawful` |
| `coupledHidden` (cell `Bool`) | ✓ `coupledHidden_lawful` | ✓ `coupledHidden_lawful` | ✓ `coupledHidden_lawful` | ✓ `coupledHidden_lawful` |
| `writeLog` | ✓ `writeLog_getGet` | ✗ `writeLog_not_getPut` | ✓ `writeLog_putGet` | ✗ `writeLog_not_putPut` |
| `changeLog` (decidable equality on `S`) | ✓ `changeLog_getGet` | ✓ `changeLog_getPut` | ✓ `changeLog_putGet` | ✗ `changeLog_not_putPut` |
| `writesIgnored` | ✓ `writesIgnored_getGet` | ✓ `writesIgnored_getPut` | ✗ `writesIgnored_not_putGet` | ✓ `writesIgnored_putPut` |
| `dirtyBit` | ✓ `dirtyBit_getGet` | ✗ `dirtyBit_not_getPut` | ✓ `dirtyBit_putGet` | ✓ `dirtyBit_putPut` |
| `readToClear` (✗ at `d = false`) | ✗ `readToClear_not_getGet` | ✓ `readToClear_getPut` | ✗ `readToClear_not_putGet` | ✓ `readToClear_putPut` |
| `faultingCounter` | ✗ `faultingCounter_not_getGet` | ✗ `faultingCounter_not_getPut` | ✓ `faultingCounter_putGet` | ✓ `faultingCounter_putPut` |
| `readCounter` | ✗ `readCounter_not_getGet` | ✗ `readCounter_not_getPut` | ✗ `readCounter_not_putGet` | ✓ `readCounter_putPut` |

The ✗ entries are proved for a Boolean cell with Boolean results. With an empty cell type or an empty result type, `writeLog` and `readCounter` satisfy all four laws strictly (`writeLog_lawful_of_empty_cell`, `writeLog_lawful_of_empty_result`, `readCounter_lawful_of_empty_cell`, `readCounter_lawful_of_empty_result`); other inhabited types are not examined.

### Modeling bridge

These two claims connect the toy model to real interfaces. They are reasoned, not formalized.

- Basis: derived (modeling bridge). A monad `m` with operations `get : m S` and `put : S → m Unit` (the `MonadState` interface of Gibbons–Hinze 2011, Section 6) yields, for each result type `V`, a model `Model S (m V)` with `get k := get >>= k` and `put s x := put s >> x`. Reasoning, assuming the monad laws (left and right unit and associativity of `>>=`, at all result types): Gibbons–Hinze put–put and get–put, composed with an arbitrary continuation, give `PutPut` and `GetPut` for these models, and conversely `PutPut` and `GetPut` at `V = Unit` with continuation `return ()` give them back; Gibbons–Hinze put–get (`put s >> get = put s >> return s`), composed with a continuation, gives `PutGet`, and conversely `PutGet` at `V = S` with continuation `return` gives it back; Gibbons–Hinze get–get is stated with an arbitrary continuation `k : S → S → m A` and corresponds to `GetGet` at `V = A`. For monads that violate the monad laws these correspondences are not established. `Prog` trees represent the pure, terminating, first-order programs built from `get`, `put`, `return` and `>>=`; recursive programs and programs that use other effects are not represented. Model–system relation: none proved. These are statements about the toy model; they neither establish nor refute the corresponding claims about a particular monad implementation.
- Basis: derived (modeling bridge). The weird models are named after behaviors of instrumented stores and devices; the names are illustrations. Model–system relation: none proved. These are statements about the toy models; they neither establish nor refute the corresponding claims about any particular device, library or verification tool.

## Findings

Each card gives the plain claim, kind, tier and depth, the verbatim Lean statement, a hypothesis ledger, a non-vacuity witness, a positive control where the result is an impossibility, prior art and the design question it informs. Non-claims for every card are collected under Boundaries. `Basis: execution (Lean kernel check)` means that the statement was checked by the Lean kernel of the toolchain above, with the axioms recorded under Evidence; a claim about real systems carries a separate `Basis: derived (modeling bridge)` line with its reasoning. In a hypothesis ledger, "tight" means that a kernel-checked counterexample, in the stated class of instances, satisfies all the other hypotheses while the conclusion fails.

### Result 1. `getGet_of_getPut_of_putGet`

**Plain claim.** For every cell type S, every carrier X and every model M : Model S X, if M satisfies get–put and put–get as equations in X, then M satisfies get–get as an equation in X.

**Kind / tier / depth.** theorem / T0 / shallow. Tier rationale: The derivation of get–get from get–put and put–get is published (Kidney–Yang–Wu 2024, with a proof in the authors' Agda repository; Matache et al. 2025; Hillerström 2021); restated here for models on arbitrary carriers.

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:54-55
theorem getGet_of_getPut_of_putGet {S X : Type} (M : Model S X) (hGP : GetPut M)
    (hPG : PutGet M) : GetGet M := …
```

**Hypothesis ledger.**

- `hGP : GetPut M` — Gives x = M.get (fun t => M.put t x) for every x : X, which places a write of the value just read in front of both sides of get–get. Tightness: tight — counterexample `getGet_of_tight_getPut` (a model on a Boolean cell with Boolean results (`faultingCounter`: counts reads, every write faults) satisfying put–get): all other hypotheses hold and the conclusion fails.
- `hPG : PutGet M` — Resolves the reads after that inserted write to the written value, collapsing both sides to M.get (fun t => M.put t (k t t)). Tightness: tight — counterexample `getGet_of_tight_putGet` (a model on a Boolean cell with Boolean results (`readToClear`: reading resets the cell to false) satisfying get–put): all other hypotheses hold and the conclusion fails.

**Non-vacuity witness.** `inertHidden Bool Bool Bool` (an ordinary cell next to an untouched hidden component) satisfies get–put and put–get. (`nv_getGet_of_getPut_of_putGet`)

**Prior art.** [PP02], [GH11], [KYW24], [MLMSWY25], [Hil21], [Loc17] (exact records and what each source states: Evidence › Primary sources).

**Design question.** When an interface is specified by the four state laws, which of them must be stated and checked? Under strict satisfaction, get–get need not be checked separately once get–put and put–get hold; a model that violates get–get (e.g. a destructive or counting read) violates get–put or put–get.

**Non-claims.** Boundaries › Non-claims › Result 1; read them before relying on this result.

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). For a monad `m` that satisfies the monad laws and whose operations satisfy Gibbons–Hinze get–put and put–get, the bridge under Applicability gives `GetPut` and `PutGet` for the models `Model S (m V)`; this theorem then gives `GetGet` for them, which at `V = A` is Gibbons–Hinze get–get for continuations `k : S → S → m A`. The bridge is not formalized (model–system relation: none proved).

### Result 2. `getPut_putGet_putPut_independent_bool`

**Plain claim.** For a Boolean cell with Boolean results, with laws as carrier equations: the change-log model satisfies get–get, get–put and put–get and violates put–put; the writes-ignored model satisfies get–get, get–put and put–put and violates put–get; the dirty-bit model satisfies get–get, put–get and put–put and violates get–put.

**Kind / tier / depth.** counterexample / T1 / shallow. Tier rationale: Independence of these three laws is folklore-level; the specific countermodels and a mechanization were not located in the sources checked.

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:67-73
theorem getPut_putGet_putPut_independent_bool :
    (GetGet (changeLog Bool Bool) ∧ GetPut (changeLog Bool Bool) ∧
      PutGet (changeLog Bool Bool) ∧ ¬ PutPut (changeLog Bool Bool)) ∧
    (GetGet (writesIgnored Bool Bool) ∧ GetPut (writesIgnored Bool Bool) ∧
      PutPut (writesIgnored Bool Bool) ∧ ¬ PutGet (writesIgnored Bool Bool)) ∧
    (GetGet (dirtyBit Bool Bool) ∧ PutGet (dirtyBit Bool Bool) ∧
      PutPut (dirtyBit Bool Bool) ∧ ¬ GetPut (dirtyBit Bool Bool)) := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Closed statement (no hypotheses).

**Prior art.** [PP02], [GH11] (exact records and what each source states: Evidence › Primary sources). The specific independence models were not located in the sources checked.

**Design question.** For a Boolean cell, which lawful-looking behaviors does each law rule out, and does each law rule out something the other three allow? On a Boolean cell, each of get–put, put–get and put–put is violated by a natural model of the other three: a log of value-changing writes (`changeLog`) violates put–put, a device that drops writes (`writesIgnored`) violates put–get, and a flag set by every write, including writes of the value already held (`dirtyBit`), violates get–put.

**Non-claims.** Boundaries › Non-claims › Result 2; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 3. `getGet_not_entailed_by_pairs_with_putPut_bool`

**Plain claim.** For a Boolean cell with Boolean results, with laws as carrier equations: the read-to-clear model (reading resets the cell to false) satisfies get–put and put–put and violates get–get; the faulting read-counter model (counts reads, every write faults) satisfies put–get and put–put and violates get–get.

**Kind / tier / depth.** counterexample / T1 / shallow. Tier rationale: Folklore-level; the specific countermodels were not located in the sources checked.

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:81-85
theorem getGet_not_entailed_by_pairs_with_putPut_bool :
    (GetPut (readToClear Bool Bool false) ∧ PutPut (readToClear Bool Bool false) ∧
      ¬ GetGet (readToClear Bool Bool false)) ∧
    (PutGet (faultingCounter Bool Bool) ∧ PutPut (faultingCounter Bool Bool) ∧
      ¬ GetGet (faultingCounter Bool Bool)) := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Closed statement (no hypotheses).

**Prior art.** [GH11] (exact records and what each source states: Evidence › Primary sources). The specific models were not located in the sources checked.

**Design question.** Under strict satisfaction on a Boolean cell, when is get–get worth stating separately? It is implied once both get–put and put–get are present (`getGet_of_getPut_of_putGet`), and it is not implied by either of them together with put–put; so stating it matters for law sets that lack get–put or put–get.

**Non-claims.** Boundaries › Non-claims › Result 3; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 4. `entailsBool_iff`

**Plain claim.** For models on a Boolean cell (any carrier, laws as carrier equations), a set Γ of the four laws entails a law l (every model satisfying every law in Γ satisfies l) iff l is in Γ, or l is get–get and both get–put and put–get are in Γ.

**Kind / tier / depth.** characterization / T1 / shallow. Tier rationale: The get–get direction is published (see prior art); the complete characterization for a Boolean cell and its mechanization were not located in the sources checked.

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:92-93
theorem entailsBool_iff (Γ : LawSet) (l : Law) :
    EntailsBool Γ l ↔ (Γ l ∨ (l = .getGet ∧ Γ .getPut ∧ Γ .putGet)) := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Both sides are inhabited: {get–put, put–get} entails get–get, and the three laws other than put–put do not entail put–put. (`nv_entailsBool_iff`)

**Prior art.** [PP02], [GH11], [KYW24], [MLMSWY25], [Hil21] (exact records and what each source states: Evidence › Primary sources). The complete entailment characterization for a Boolean cell was not located in the sources checked.

**Design question.** Complete tightness ledger for the law set on a Boolean cell: Γ ⊨ l with l not in Γ holds exactly when l = get–get and get–put, put–get are in Γ.

**Non-claims.** Boundaries › Non-claims › Result 4; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 5. `derivable_nf_of_getPut_putGet_putPut`

**Plain claim.** For every cell type S, result type V and law set L containing get–put, put–get and put–put, every program p : Prog S V is derivable from L to be equal to get (fun s => put (run p s).2 (ret (run p s).1)), the canonical program of its intended observation run p.

**Kind / tier / depth.** theorem / T0 / substantive. Tier rationale: Normal forms for global state are standard (see prior art).

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:157-158
theorem derivable_nf_of_getPut_putGet_putPut {S V : Type} (L : LawSet) (hGP : L .getPut)
    (hPG : L .putGet) (hPP : L .putPut) (p : Prog S V) : Derivable L p (nf (run p)) := …
```

**Hypothesis ledger.**

- `hGP : L .getPut` — Introduces the leading read for returns (ret v = get (fun s => put s (ret v))) and removes a read whose continuation ignores the value. Tightness: tight — counterexample `dropGetPut_loses_nf` (L = all laws but get–put, Boolean cell, Boolean results, p = ret true): all other hypotheses hold and the conclusion fails.
- `hPG : L .putGet` — Resolves a read after a write (put t (get k) = put t (k t)); with get–put also derives get–get. Tightness: tight — counterexample `dropPutGet_loses_nf` (L = all laws but put–get, Boolean cell, Boolean results, p = put true (get ret)): all other hypotheses hold and the conclusion fails.
- `hPP : L .putPut` — Merges consecutive writes into the last one. Tightness: tight — counterexample `dropPutPut_loses_nf` (L = all laws but put–put, Boolean cell, Boolean results, p = put true (put false (ret true))): all other hypotheses hold and the conclusion fails.

**Non-vacuity witness.** L = `lawsExcept` .getGet (get–put, put–get, put–put without get–get) satisfies all three hypotheses. (`nv_derivable_nf`)

**Prior art.** [PP02], [GH11], [Loc17] (exact records and what each source states: Evidence › Primary sources).

**Design question.** Does the law set pin down program equality? Get–put, put–get and put–put bring every program to a read-once, write-once, return form determined by its intended observation.

**Non-claims.** Boundaries › Non-claims › Result 5; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 6. `canon_eq_of_derivable`

**Plain claim.** For every cell type S, result type V and law set L, if canon f g and canon f' g' are derivably equal from L, then f = f' and g = g'.

**Kind / tier / depth.** theorem / T0 / shallow. Tier rationale: Uniqueness of normal forms by soundness in the intended model is standard.

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:172-173
theorem canon_eq_of_derivable {S V : Type} {L : LawSet} {f f' : S → S} {g g' : S → V}
    (h : Derivable L (canon f g) (canon f' g')) : f = f' ∧ g = g' := …
```

**Hypothesis ledger.**

- `h : Derivable L (canon f g) (canon f' g')` — The premise; it transfers to equality of intended observations by soundness (the intended model satisfies every law). Tightness: tight — counterexample `canon_eq_tight` (S = V = Bool: write maps fun s => s and fun s => !s, result maps both fun s => s; without the premise the conclusion fails for these maps): all other hypotheses hold and the conclusion fails.

**Non-vacuity witness.** Reflexivity: `Derivable` `allLaws` (canon (fun s => !s) (fun s => s)) (canon (fun s => !s) (fun s => s)). (`nv_canon_eq_of_derivable`)

**Prior art.** [PP02] (exact records and what each source states: Evidence › Primary sources).

**Design question.** Is the canonical form a faithful representative? Yes: distinct (write map, result map) pairs are never derivably equal.

**Non-claims.** Boundaries › Non-claims › Result 6; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 7. `derivable_iff_obsEq_of_getPut_putGet_putPut`

**Plain claim.** For every cell type S, result type V and law set L containing get–put, put–get and put–put, two programs p, q : Prog S V are derivably equal from L iff they are observationally equivalent (run p = run q).

**Kind / tier / depth.** characterization / T0 / shallow. Tier rationale: Completeness of the state laws is standard.

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:181-183
theorem derivable_iff_obsEq_of_getPut_putGet_putPut {S V : Type} (L : LawSet)
    (hGP : L .getPut) (hPG : L .putGet) (hPP : L .putPut) (p q : Prog S V) :
    Derivable L p q ↔ ObsEq p q := …
```

**Hypothesis ledger.**

- `hGP : L .getPut` — Used for completeness (right-to-left). Tightness: tight — counterexample `dropGetPut_loses_nf` (L = all laws but get–put, Boolean cell, Boolean results): all other hypotheses hold and the conclusion fails.
- `hPG : L .putGet` — Used for completeness (right-to-left). Tightness: tight — counterexample `dropPutGet_loses_nf` (L = all laws but put–get, Boolean cell, Boolean results): all other hypotheses hold and the conclusion fails.
- `hPP : L .putPut` — Used for completeness (right-to-left). Tightness: tight — counterexample `dropPutPut_loses_nf` (L = all laws but put–put, Boolean cell, Boolean results): all other hypotheses hold and the conclusion fails.

**Non-vacuity witness.** L = `lawsExcept` .getGet satisfies all three hypotheses. (`nv_derivable_nf`)

**Prior art.** [PP02], [GH11] (exact records and what each source states: Evidence › Primary sources).

**Design question.** Is reasoning with the laws complete for the intended semantics? For one cell, yes: every observationally equivalent pair (same final value and final cell content from every initial content, `ObsEq`) is derivably equal from any law set containing get–put, put–get and put–put.

**Non-claims.** Boundaries › Non-claims › Result 7; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 8. `interp_eq_fromObs_run_of_getPut_putGet_putPut`

**Plain claim.** For every model M on a carrier X satisfying get–put, put–get and put–put as equations in X, every valuation ρ : V → X and every program p, M.interp ρ p = M.get (fun s => M.put (run p s).2 (ρ (run p s).1)); that is, the interpretation of p in M is determined by its intended observation run p and by ρ.

**Kind / tier / depth.** theorem / T0 / shallow. Tier rationale: A consequence of freeness of the state monad (Plotkin–Power).

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:199-201
theorem interp_eq_fromObs_run_of_getPut_putGet_putPut {S X V : Type} (M : Model S X)
    (hGP : GetPut M) (hPG : PutGet M) (hPP : PutPut M) (ρ : V → X) (p : Prog S V) :
    M.interp ρ p = M.fromObs ρ (run p) := …
```

**Hypothesis ledger.**

- `hGP : GetPut M` — Used through normal-form existence and soundness. Tightness: tight — counterexample `interp_factor_tight_getPut` (`dirtyBit` on a Boolean cell with Boolean results (satisfies put–get, put–put)): all other hypotheses hold and the conclusion fails.
- `hPG : PutGet M` — Used through normal-form existence and soundness. Tightness: tight — counterexample `interp_factor_tight_putGet` (`writesIgnored` on a Boolean cell with Boolean results (satisfies get–put, put–put)): all other hypotheses hold and the conclusion fails.
- `hPP : PutPut M` — Used through normal-form existence and soundness. Tightness: tight — counterexample `interp_factor_tight_putPut` (`changeLog` on a Boolean cell with Boolean results (satisfies get–put, put–get)): all other hypotheses hold and the conclusion fails.

**Non-vacuity witness.** `inertHidden Bool Bool Bool` satisfies get–put, put–get and put–put. (`nv_interp_factor`)

**Prior art.** [PP02], [PlPr09] (exact records and what each source states: Evidence › Primary sources).

**Design question.** What can a strictly lawful model reveal about a program beyond its intended semantics? Nothing beyond its intended observation and the valuation.

**Non-claims.** Boundaries › Non-claims › Result 8; read them before relying on this result.

Basis: execution (Lean kernel check).

Basis: derived (modeling bridge). For a monad `m` that satisfies the monad laws and whose operations satisfy Gibbons–Hinze get–put, put–get and put–put, the bridge models `Model S (m V)` satisfy the three laws strictly; with the valuation `return`, the interpretation of a `Prog` program is the monadic program built from it, so by this theorem that program equals `get >>= fun s => put (run p s).2 >> return (run p s).1`. The bridge is not formalized (model–system relation: none proved).

### Result 9. `interp_eq_of_obsEq_of_getPut_putGet_putPut`

**Plain claim.** For every model M on a carrier X satisfying get–put, put–get and put–put as equations in X, every valuation ρ, and all programs p, q with run p = run q, M.interp ρ p = M.interp ρ q: no such model distinguishes observationally equivalent programs.

**Kind / tier / depth.** impossibility / T0 / shallow. Tier rationale: A direct corollary of the factorization.

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:208-210
theorem interp_eq_of_obsEq_of_getPut_putGet_putPut {S X V : Type} (M : Model S X)
    (hGP : GetPut M) (hPG : PutGet M) (hPP : PutPut M) (ρ : V → X) {p q : Prog S V}
    (h : ObsEq p q) : M.interp ρ p = M.interp ρ q := …
```

**Hypothesis ledger.**

- `hGP : GetPut M` — Excludes, e.g., a flag set by every write. Tightness: tight — counterexample `interp_factor_tight_getPut` (`dirtyBit`, Boolean cell, Boolean results): all other hypotheses hold and the conclusion fails.
- `hPG : PutGet M` — Excludes, e.g., dropped writes. Tightness: tight — counterexample `interp_factor_tight_putGet` (`writesIgnored`, Boolean cell, Boolean results): all other hypotheses hold and the conclusion fails.
- `hPP : PutPut M` — Excludes, e.g., logging overwritten value-changing writes. Tightness: tight — counterexample `interp_factor_tight_putPut` (`changeLog`, Boolean cell, Boolean results): all other hypotheses hold and the conclusion fails.
- `h : ObsEq p q` — The premise. Tightness: tight — counterexample `interp_eq_tight_obsEq` (the intended model on a Boolean cell with p = ret true, q = ret false): all other hypotheses hold and the conclusion fails.

**Non-vacuity witness.** `inertHidden Bool Bool Bool` satisfies get–put, put–get and put–put, and put true (put false (ret true)) and put false (ret true) are observationally equivalent. (`nv_interp_eq_of_obsEq`)

**Positive control.** `writeLog_via_distinguishes_obsEq` (statements under Witness statements).

**Prior art.** [PP02] (exact records and what each source states: Evidence › Primary sources).

**Design question.** Can a strictly lawful model expose hidden write logs or counters through get and put? Not ones that differ between observationally equivalent programs: under strict laws, what such a model assigns to a program is fixed by the program's intended observation and the valuation. Effects carried by the valuation are not constrained by the laws.

**Non-claims.** Boundaries › Non-claims › Result 9; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 10. `fromObs_isHom_unique_of_getPut_putGet_putPut`

**Plain claim.** For every model M on a carrier X satisfying get–put, put–get and put–put as equations in X and every valuation ρ : V → X, the map o ↦ M.get (fun s => M.put (o s).2 (ρ (o s).1)) from intended observations S → V × S to X is a homomorphism from the intended model to M (it sends `intendedRet v` to ρ v and commutes with get and put), and every such homomorphism equals it.

**Kind / tier / depth.** characterization / T0 / shallow. Tier rationale: Freeness of the state monad (Plotkin–Power Theorem 1).

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:220-222
theorem fromObs_isHom_unique_of_getPut_putGet_putPut {S X V : Type} (M : Model S X)
    (hGP : GetPut M) (hPG : PutGet M) (hPP : PutPut M) (ρ : V → X) :
    IsHom M ρ (M.fromObs ρ) ∧ ∀ h, IsHom M ρ h → h = M.fromObs ρ := …
```

**Hypothesis ledger.**

- `hGP : GetPut M` — Used for the return clause of the homomorphism. Tightness: tight — counterexample `fromObs_tight_getPut` (`dirtyBit`, Boolean cell, Boolean results, ρ = `pairRet`): all other hypotheses hold and the conclusion fails.
- `hPG : PutGet M` — Used for the put clause (and, with get–put, the get clause). Tightness: tight — counterexample `fromObs_tight_putGet` (`writesIgnored`, Boolean cell, Boolean results, ρ = `intendedRet`): all other hypotheses hold and the conclusion fails.
- `hPP : PutPut M` — Used for the put clause. Tightness: tight — counterexample `fromObs_tight_putPut` (`changeLog`, Boolean cell, Boolean results, ρ = `logRet`): all other hypotheses hold and the conclusion fails.

**Non-vacuity witness.** `valueOnly Bool Bool` satisfies get–put, put–get and put–put. (`nv_fromObs_isHom`)

**Prior art.** [PP02], [PP03], [PlPr09] (exact records and what each source states: Evidence › Primary sources).

**Design question.** Freeness: for a strictly lawful model M and any valuation ρ : V → X, there is exactly one structure-preserving map from the intended model on V to M that extends ρ, namely M.fromObs ρ; the program interpretations under ρ are its image.

**Non-claims.** Boundaries › Non-claims › Result 10; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 11. `getPut_putGet_putPut_iff_exists_surjective_isHom`

**Plain claim.** For every cell type S, every carrier X and every model M : Model S X, M satisfies get–put, put–get and put–put as equations in X iff there is a map h from intended observations S → X × S to X that is a homomorphism from the intended model with result type X (returns `intendedRet`) to M sending `intendedRet x` to x, and that is surjective onto X.

**Kind / tier / depth.** characterization / T0 / shallow. Tier rationale: Every model is a quotient of a free model (standard universal algebra; Plotkin–Power Theorem 1 for global state).

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:256-258
theorem getPut_putGet_putPut_iff_exists_surjective_isHom {S X : Type} (M : Model S X) :
    (GetPut M ∧ PutGet M ∧ PutPut M) ↔
      ∃ h : (S → X × S) → X, IsHom M id h ∧ ∀ x : X, ∃ o, h o = x := …
```

Remark. The last conjunct, `∀ x : X, ∃ o, h o = x`, adds no condition: the first clause of `IsHom M id h` gives `h (intendedRet x) = x` for every `x : X`. The companion lemmas below record this; the second one is the same characterization with the surjectivity conjunct omitted.

```lean
-- Toy/StoreLaws/Companions.lean:36-37
theorem isHom_id_surjective {S X : Type} (M : Model S X) (h : (S → X × S) → X)
    (hh : IsHom M id h) : ∀ x : X, ∃ o, h o = x := …
```

```lean
-- Toy/StoreLaws/Companions.lean:44-45
theorem getPut_putGet_putPut_iff_exists_isHom {S X : Type} (M : Model S X) :
    (GetPut M ∧ PutGet M ∧ PutPut M) ↔ ∃ h : (S → X × S) → X, IsHom M id h := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Both sides are inhabited: `inertHidden Bool Bool Bool` has such a surjective homomorphism, and `dirtyBit Bool Bool` has none. (`nv_getPut_putGet_putPut_iff_exists_surjective_isHom`)

**Prior art.** [PP02], [PS04], [Met04] (exact records and what each source states: Evidence › Primary sources).

**Design question.** Representation theorem: the models satisfying get–put, put–get and put–put strictly are exactly the homomorphic images (quotients) of the intended model with result type X on their own carrier X, via a homomorphism that sends `intendedRet x` to x. Such a homomorphism is automatically surjective (`isHom_id_surjective`).

**Non-claims.** Boundaries › Non-claims › Result 11; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 12. `lawful_not_faithful`

**Plain claim.** On a Boolean cell with Boolean results, the value-only model (carrier Bool → Bool; final cell content not observed) satisfies all four laws as carrier equations, and under the valuation `valueOnlyRet` (return v whatever the cell holds) it interprets ret true and ret false differently but interprets put true (ret true) and put false (ret true) equally, although they are not observationally equivalent. The one-point model satisfies all four laws and, under its unique valuation, interprets ret true and ret false equally, although they are not observationally equivalent.

**Kind / tier / depth.** counterexample / T0 / shallow. Tier rationale: Standard observation that models of an equational theory need not be free; the instances are elementary.

**Lean statements** (verbatim source quotes; proofs elided):

```lean
-- Toy/StoreLaws/Results.lean:294-300
theorem valueOnly_lawful_not_faithful :
    Lawful (valueOnly Bool Bool) ∧
    ¬ ObsEq (put true (ret true) : Prog Bool Bool) (put false (ret true)) ∧
    (valueOnly Bool Bool).interp valueOnlyRet (put true (ret true) : Prog Bool Bool) =
      (valueOnly Bool Bool).interp valueOnlyRet (put false (ret true)) ∧
    (valueOnly Bool Bool).interp valueOnlyRet (ret true : Prog Bool Bool) ≠
      (valueOnly Bool Bool).interp valueOnlyRet (ret false) := …
```

```lean
-- Toy/StoreLaws/Results.lean:325-329
theorem unitModel_lawful_not_faithful :
    Lawful (unitModel Bool) ∧
    ¬ ObsEq (ret true : Prog Bool Bool) (ret false) ∧
    (unitModel Bool).interp (fun _ => ()) (ret true : Prog Bool Bool) =
      (unitModel Bool).interp (fun _ => ()) (ret false) := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Closed statement (no hypotheses).

**Prior art.** Standard observation that models of an equational theory need not be free; the specific instances here are elementary.

**Design question.** Does satisfying the laws make a model equivalent to the intended one? No: at a fixed valuation, lawful models can forget information (the final cell content, or everything).

**Non-claims.** Boundaries › Non-claims › Result 12; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 13. `forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial`

**Plain claim.** For every cell type S, carrier X, result type V and model M : Model S X satisfying get–put, put–get and put–put as equations in X, if X has two distinct elements, then for all programs p, q : Prog S V: M interprets p and q equally under every valuation ρ : V → X iff p and q are observationally equivalent.

**Kind / tier / depth.** characterization / T0 / substantive. Tier rationale: The model-theoretic counterpart of Hilbert–Post (equational) completeness, a known property of the state theory (see prior art).

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:339-342
theorem forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial {S X V : Type}
    (M : Model S X) (hGP : GetPut M) (hPG : PutGet M) (hPP : PutPut M)
    (hnt : ∃ x y : X, x ≠ y) (p q : Prog S V) :
    (∀ ρ : V → X, M.interp ρ p = M.interp ρ q) ↔ ObsEq p q := …
```

**Hypothesis ledger.**

- `hGP : GetPut M` — Used through the factorization and to recover carrier elements from writes. Tightness: tight — counterexample `forall_interp_tight_getPut` (`dirtyBit` on a Boolean cell with Boolean results (two distinct carrier elements), p = ret true and its canonical program): all other hypotheses hold and the conclusion fails.
- `hPG : PutGet M` — Used through the factorization and to resolve the separating read. Tightness: tight — counterexample `forall_interp_tight_putGet` (`writesIgnored` on a Boolean cell with Boolean results, p = put true (get ret) and its canonical program): all other hypotheses hold and the conclusion fails.
- `hPP : PutPut M` — Used through the factorization and to merge writes. Tightness: tight — counterexample `forall_interp_tight_putPut` (`changeLog` on a Boolean cell with Boolean results, p = put true (put false (ret true)) and its canonical program): all other hypotheses hold and the conclusion fails.
- `hnt : ∃ x y : X, x ≠ y` — Excludes subsingleton carriers, the empty carrier as well as one-point carriers. On a one-point carrier every two programs are identified; on the empty carrier there is no valuation ρ : V → X when V is inhabited, so the left-hand side holds vacuously. Tightness: tight — counterexamples, in each of which all other hypotheses hold and the conclusion fails: `forall_interp_tight_nontrivial` (the one-point model on a Boolean cell with Boolean results, p = ret true, q = ret false) and `empty_carrier_breaks_forall_interp_iff` (a model on a Boolean cell with the empty carrier, same p and q).

**Non-vacuity witness.** `valueOnly Bool Bool` satisfies get–put, put–get and put–put, and its carrier Bool → Bool has two distinct elements. (`nv_forall_interp_eq_iff_obsEq`)

**Prior art.** [PP02], [KS55], [DDR13] (exact records and what each source states: Evidence › Primary sources).

**Design question.** When do strictly lawful models pin down program equality? When the carrier has two distinct elements and all valuations are considered: then the model identifies exactly the observationally equivalent programs.

**Non-claims.** Boundaries › Non-claims › Result 13; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 14. `extDerivable_total_of_not_derivable`

**Plain claim.** For every cell type S, result type V and programs p₀, q₀ : Prog S V such that p₀ = q₀ is not derivable from the four laws, the theory generated by the four laws together with every substitution instance p₀.bind σ = q₀.bind σ (σ : V → Prog S V) equates every two programs of type Prog S V.

**Kind / tier / depth.** theorem / T0 / substantive. Tier rationale: Hilbert–Post completeness of single-location global state is published (Pretnar 2010, as attested by Dumas–Duval–Reynaud 2013; Dumas–Duval–Reynaud 2013 in a decorated logic, with a Coq-checked key proposition).

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:390-391
theorem extDerivable_total_of_not_derivable {S V : Type} (p₀ q₀ : Prog S V)
    (h : ¬ Derivable allLaws p₀ q₀) (p q : Prog S V) : ExtDerivable p₀ q₀ p q := …
```

**Hypothesis ledger.**

- `h : ¬ Derivable allLaws p₀ q₀` — Excludes adding an equation already in the theory. Tightness: tight — counterexample `extDerivable_tight` (S = Bool, V = Bool, p₀ = q₀ = ret true): all other hypotheses hold and the conclusion fails.

**Non-vacuity witness.** p₀ = ret true, q₀ = ret false (S = V = Bool) is not derivable. (`nv_extDerivable_total`)

**Positive control.** `extDerivable_tight`, `extDerivableNoSubst_not_total` (statements under Witness statements).

**Prior art.** [PP02], [Pre10], [DDR13], [DDEP13], [DDEPR16], [KS55], [Sta10] (exact records and what each source states: Evidence › Primary sources).

**Design question.** Is the law set Hilbert–Post complete? For one cell, yes in this sense: within a fixed program type Prog S V, with the added equation closed under substitution and the usual congruence rules, every equation not already derivable from the four laws makes every two programs derivably equal.

**Non-claims.** Boundaries › Non-claims › Result 14; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 15. `writeLog_via_distinguishes_obsEq`

**Plain claim.** For a Boolean cell with Boolean results, the write-log model satisfies get–get, get–put, put–get and put–put when the two sides of each law instance are compared after applying the log-forgetting observation `dropLog`, and under the valuation `logRet` it interprets put true (put false (ret true)) and put false (ret true) differently, although they are observationally equivalent.

**Kind / tier / depth.** counterexample / T0 / shallow. Tier rationale: Elementary; satisfaction through an observation versus strict satisfaction is a standard distinction (see prior art).

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:466-471
theorem writeLog_via_distinguishes_obsEq :
    (GetGetVia dropLog (writeLog Bool Bool) ∧ GetPutVia dropLog (writeLog Bool Bool) ∧
      PutGetVia dropLog (writeLog Bool Bool) ∧ PutPutVia dropLog (writeLog Bool Bool)) ∧
    ObsEq (put true (put false (ret true)) : Prog Bool Bool) (put false (ret true)) ∧
    (writeLog Bool Bool).interp logRet (put true (put false (ret true)) : Prog Bool Bool) ≠
      (writeLog Bool Bool).interp logRet (put false (ret true)) := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Closed statement (no hypotheses).

**Prior art.** [GM00] (exact records and what each source states: Evidence › Primary sources). The write-log instance is elementary; it was not located as a stated result.

**Design question.** Do the laws exclude hidden write logs? Not if they are checked through an observation that forgets the log, such as `dropLog`. Imposed strictly, as equations in the carrier, they exclude logs that distinguish observationally equivalent programs (`interp_eq_of_obsEq_of_getPut_putGet_putPut`).

**Non-claims.** Boundaries › Non-claims › Result 15; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 16. `writeLog_strict_profile_bool`

**Plain claim.** For a Boolean cell with Boolean results, the write-log model (carrier Bool → Bool × Bool × List Bool, every put logged) satisfies get–get and put–get as carrier equations and violates get–put and put–put.

**Kind / tier / depth.** counterexample / T1 / shallow. Tier rationale: That a logging store is unlawful is folklore; this profile and a mechanization were not located in the sources checked.

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:478-480
theorem writeLog_strict_profile_bool :
    GetGet (writeLog Bool Bool) ∧ PutGet (writeLog Bool Bool) ∧
    ¬ GetPut (writeLog Bool Bool) ∧ ¬ PutPut (writeLog Bool Bool) := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Closed statement (no hypotheses).

**Prior art.** Not located as a stated result; elementary.

**Design question.** Is a full write log compatible with the strict laws? On a Boolean cell with Boolean results, no: it violates strict get–put (writing back the value just read is logged) and strict put–put (overwritten writes are logged).

**Non-claims.** Boundaries › Non-claims › Result 16; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 17. `readCounter_strict_profile_bool`

**Plain claim.** For a Boolean cell with Boolean results, the read-counter model (carrier Bool → Bool × Bool × Nat; every read increments the count) satisfies put–put as a carrier equation and violates get–get, get–put and put–get.

**Kind / tier / depth.** counterexample / T1 / shallow. Tier rationale: That a read counter is unlawful is folklore; this profile and a mechanization were not located in the sources checked.

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:486-488
theorem readCounter_strict_profile_bool :
    PutPut (readCounter Bool Bool) ∧ ¬ GetGet (readCounter Bool Bool) ∧
    ¬ GetPut (readCounter Bool Bool) ∧ ¬ PutGet (readCounter Bool Bool) := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Closed statement (no hypotheses).

**Prior art.** Not located as a stated result; elementary.

**Design question.** Which laws does counting reads break? On a Boolean cell with Boolean results, strictly, all but put–put: get–get (two reads count twice), get–put (the read in a read-then-write-back is counted) and put–get (the read after a write is counted).

**Non-claims.** Boundaries › Non-claims › Result 17; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 18. `inertHidden_interp_eq`

**Plain claim.** For all types S, H, V, the inert-hidden model (carrier S × H → V × (S × H); get reads the first component, put overwrites it) satisfies all four laws as carrier equations, and under the valuation `pairRet` (return v, leave the state) for every program p, cell content s and hidden value h, interpreting p from (s, h) returns (run p s).1 with final state ((run p s).2, h).

**Kind / tier / depth.** theorem / T0 / shallow. Tier rationale: Constant-complement / product-state construction; elementary.

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:495-498
theorem inertHidden_interp_eq {S H V : Type} :
    Lawful (inertHidden S H V) ∧
    ∀ (p : Prog S V) (s : S) (h : H),
      (inertHidden S H V).interp pairRet p (s, h) = ((run p s).1, ((run p s).2, h)) := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Closed statement (no hypotheses); the instance S = H = V = Bool is `nv_inertHidden_interp_eq`.

**Prior art.** Constant-complement / product-state construction; elementary.

**Design question.** Is hidden state per se excluded by the laws? No: hidden state is compatible with all four laws even strictly. In `inertHidden` under `pairRet`, programs neither observe nor change it; under other valuations, or in other strictly lawful models, it can change, but never in a way that distinguishes observationally equivalent programs (`interp_eq_of_obsEq_of_getPut_putGet_putPut`).

**Non-claims.** Boundaries › Non-claims › Result 18; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 19. `derivable_lawsExcept_getGet_iff`

**Plain claim.** For every cell type S, result type V and programs p, q : Prog S V, p = q is derivable from get–put, put–get and put–put iff it is derivable from all four laws.

**Kind / tier / depth.** characterization / T0 / shallow. Tier rationale: The derivation of get–get from get–put and put–get is published (see prior art).

**Lean statement** (verbatim source quote; proof elided):

```lean
-- Toy/StoreLaws/Results.lean:541-542
theorem derivable_lawsExcept_getGet_iff {S V : Type} (p q : Prog S V) :
    Derivable (lawsExcept .getGet) p q ↔ Derivable allLaws p q := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Both sides are inhabited: a get–get instance is derivable from the laws other than get–get, and ret true = ret false is derivable from neither (Boolean cell). (`nv_derivable_lawsExcept_getGet_iff`)

**Prior art.** [KYW24], [MLMSWY25], [Hil21] (exact records and what each source states: Evidence › Primary sources).

**Design question.** Dropping get–get from the four laws changes no derivable equation; it is a derived law.

**Non-claims.** Boundaries › Non-claims › Result 19; read them before relying on this result.

Basis: execution (Lean kernel check).

### Result 20. `drop_law_loses_nf`

**Plain claim.** For a Boolean cell with Boolean results: from the laws other than get–put, ret true is not derivably equal to its canonical program get (fun s => put s (ret true)); from the laws other than put–get, put true (get ret) is not derivably equal to its canonical program; from the laws other than put–put, put true (put false (ret true)) is not derivably equal to its canonical program; in each case the two programs are observationally equivalent.

**Kind / tier / depth.** counterexample / T1 / shallow. Tier rationale: Folklore-level; the specific non-derivability witnesses and a mechanization were not located in the sources checked.

**Lean statements** (verbatim source quotes; proofs elided):

```lean
-- Toy/StoreLaws/Results.lean:592-595
theorem dropGetPut_loses_nf :
    lawsExcept .getPut .putGet ∧ lawsExcept .getPut .putPut ∧
    ObsEq (ret true : Prog Bool Bool) (nf (run (ret true))) ∧
    ¬ Derivable (lawsExcept .getPut) (ret true : Prog Bool Bool) (nf (run (ret true))) := …
```

```lean
-- Toy/StoreLaws/Results.lean:610-614
theorem dropPutGet_loses_nf :
    lawsExcept .putGet .getPut ∧ lawsExcept .putGet .putPut ∧
    ObsEq (put true (get ret) : Prog Bool Bool) (nf (run (put true (get ret)))) ∧
    ¬ Derivable (lawsExcept .putGet) (put true (get ret) : Prog Bool Bool)
      (nf (run (put true (get ret)))) := …
```

```lean
-- Toy/StoreLaws/Results.lean:629-634
theorem dropPutPut_loses_nf :
    lawsExcept .putPut .getPut ∧ lawsExcept .putPut .putGet ∧
    ObsEq (put true (put false (ret true)) : Prog Bool Bool)
      (nf (run (put true (put false (ret true))))) ∧
    ¬ Derivable (lawsExcept .putPut) (put true (put false (ret true)) : Prog Bool Bool)
      (nf (run (put true (put false (ret true))))) := …
```

**Hypothesis ledger.**

- No hypotheses: the statement is closed, or quantifies universally over its parameters without side conditions.

**Non-vacuity witness.** Closed statements (no hypotheses).

**Prior art.** Not located as stated results; elementary.

**Design question.** On a Boolean cell, each of get–put, put–get and put–put is tight for the normal-form and completeness theorems: without it, an observationally equivalent pair is not derivably equal.

**Non-claims.** Boundaries › Non-claims › Result 20; read them before relying on this result.

Basis: execution (Lean kernel check).


### Witness statements

Tightness counterexamples (each states that all other hypotheses hold and the conclusion fails), non-vacuity witnesses (each states that all hypotheses hold for a concrete instance) and positive controls, quoted verbatim.

```lean
-- Toy/StoreLaws/Witnesses.lean:19-20
theorem getGet_of_tight_getPut :
    PutGet (faultingCounter Bool Bool) ∧ ¬ GetGet (faultingCounter Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:24-25
theorem getGet_of_tight_putGet :
    GetPut (readToClear Bool Bool false) ∧ ¬ GetGet (readToClear Bool Bool false) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:30-31
theorem nv_getGet_of_getPut_of_putGet :
    GetPut (inertHidden Bool Bool Bool) ∧ PutGet (inertHidden Bool Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:38-40
theorem nv_entailsBool_iff :
    EntailsBool (fun l => l = .getPut ∨ l = .putGet) .getGet ∧
    ¬ EntailsBool (lawsExcept .putPut) .putPut := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:53-54
theorem nv_derivable_nf :
    lawsExcept .getGet .getPut ∧ lawsExcept .getGet .putGet ∧ lawsExcept .getGet .putPut := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:77-78
theorem canon_eq_tight :
    ¬ ((fun s : Bool => s) = (fun s => !s) ∧ (fun s : Bool => s) = (fun s => s)) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:70-72
theorem nv_canon_eq_of_derivable :
    Derivable allLaws (canon (fun s : Bool => !s) (fun s => s))
      (canon (fun s : Bool => !s) (fun s => s)) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:89-95
theorem interp_factor_tight_getPut :
    PutGet (dirtyBit Bool Bool) ∧ PutPut (dirtyBit Bool Bool) ∧
    ObsEq (ret true : Prog Bool Bool) (nf (run (ret true))) ∧
    (dirtyBit Bool Bool).interp pairRet (ret true : Prog Bool Bool) ≠
      (dirtyBit Bool Bool).interp pairRet (nf (run (ret true : Prog Bool Bool))) ∧
    (dirtyBit Bool Bool).interp pairRet (ret true : Prog Bool Bool) ≠
      (dirtyBit Bool Bool).fromObs pairRet (run (ret true : Prog Bool Bool)) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:103-111
theorem interp_factor_tight_putGet :
    GetPut (writesIgnored Bool Bool) ∧ PutPut (writesIgnored Bool Bool) ∧
    ObsEq (put true (get ret) : Prog Bool Bool) (nf (run (put true (get ret)))) ∧
    (writesIgnored Bool Bool).interp intendedRet (put true (get ret) : Prog Bool Bool) ≠
      (writesIgnored Bool Bool).interp intendedRet
        (nf (run (put true (get ret) : Prog Bool Bool))) ∧
    (writesIgnored Bool Bool).interp intendedRet (put true (get ret) : Prog Bool Bool) ≠
      (writesIgnored Bool Bool).fromObs intendedRet
        (run (put true (get ret) : Prog Bool Bool)) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:119-128
theorem interp_factor_tight_putPut :
    GetPut (changeLog Bool Bool) ∧ PutGet (changeLog Bool Bool) ∧
    ObsEq (put true (put false (ret true)) : Prog Bool Bool)
      (nf (run (put true (put false (ret true))))) ∧
    (changeLog Bool Bool).interp logRet (put true (put false (ret true)) : Prog Bool Bool) ≠
      (changeLog Bool Bool).interp logRet
        (nf (run (put true (put false (ret true)) : Prog Bool Bool))) ∧
    (changeLog Bool Bool).interp logRet (put true (put false (ret true)) : Prog Bool Bool) ≠
      (changeLog Bool Bool).fromObs logRet
        (run (put true (put false (ret true)) : Prog Bool Bool)) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:136-138
theorem nv_interp_factor :
    GetPut (inertHidden Bool Bool Bool) ∧ PutGet (inertHidden Bool Bool Bool) ∧
    PutPut (inertHidden Bool Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:155-158
theorem interp_eq_tight_obsEq :
    GetPut (intended Bool Bool) ∧ PutGet (intended Bool Bool) ∧ PutPut (intended Bool Bool) ∧
    (intended Bool Bool).interp intendedRet (ret true : Prog Bool Bool) ≠
      (intended Bool Bool).interp intendedRet (ret false) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:145-148
theorem nv_interp_eq_of_obsEq :
    GetPut (inertHidden Bool Bool Bool) ∧ PutGet (inertHidden Bool Bool Bool) ∧
    PutPut (inertHidden Bool Bool Bool) ∧
    ObsEq (put true (put false (ret true)) : Prog Bool Bool) (put false (ret true)) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:167-169
theorem fromObs_tight_getPut :
    PutGet (dirtyBit Bool Bool) ∧ PutPut (dirtyBit Bool Bool) ∧
    ¬ IsHom (dirtyBit Bool Bool) pairRet ((dirtyBit Bool Bool).fromObs (V := Bool) pairRet) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:176-179
theorem fromObs_tight_putGet :
    GetPut (writesIgnored Bool Bool) ∧ PutPut (writesIgnored Bool Bool) ∧
    ¬ IsHom (writesIgnored Bool Bool) intendedRet
      ((writesIgnored Bool Bool).fromObs (V := Bool) intendedRet) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:186-188
theorem fromObs_tight_putPut :
    GetPut (changeLog Bool Bool) ∧ PutGet (changeLog Bool Bool) ∧
    ¬ IsHom (changeLog Bool Bool) logRet ((changeLog Bool Bool).fromObs (V := Bool) logRet) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:194-195
theorem nv_fromObs_isHom :
    GetPut (valueOnly Bool Bool) ∧ PutGet (valueOnly Bool Bool) ∧ PutPut (valueOnly Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:216-218
theorem nv_getPut_putGet_putPut_iff_exists_surjective_isHom :
    (∃ h, IsHom (inertHidden Bool Bool Bool) id h ∧ ∀ x, ∃ o, h o = x) ∧
    ¬ (∃ h, IsHom (dirtyBit Bool Bool) id h ∧ ∀ x, ∃ o, h o = x) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:249-255
theorem forall_interp_tight_getPut :
    PutGet (dirtyBit Bool Bool) ∧ PutPut (dirtyBit Bool Bool) ∧
    (∃ x y : Bool × Bool → Bool × (Bool × Bool), x ≠ y) ∧
    ¬ ((∀ ρ : Bool → (Bool × Bool → Bool × (Bool × Bool)),
          (dirtyBit Bool Bool).interp ρ (ret true : Prog Bool Bool) =
            (dirtyBit Bool Bool).interp ρ (nf (run (ret true : Prog Bool Bool)))) ↔
        ObsEq (ret true : Prog Bool Bool) (nf (run (ret true)))) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:264-271
theorem forall_interp_tight_putGet :
    GetPut (writesIgnored Bool Bool) ∧ PutPut (writesIgnored Bool Bool) ∧
    (∃ x y : Bool → Bool × Bool, x ≠ y) ∧
    ¬ ((∀ ρ : Bool → (Bool → Bool × Bool),
          (writesIgnored Bool Bool).interp ρ (put true (get ret) : Prog Bool Bool) =
            (writesIgnored Bool Bool).interp ρ
              (nf (run (put true (get ret) : Prog Bool Bool)))) ↔
        ObsEq (put true (get ret) : Prog Bool Bool) (nf (run (put true (get ret))))) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:280-288
theorem forall_interp_tight_putPut :
    GetPut (changeLog Bool Bool) ∧ PutGet (changeLog Bool Bool) ∧
    (∃ x y : Bool → Bool × Bool × List Bool, x ≠ y) ∧
    ¬ ((∀ ρ : Bool → (Bool → Bool × Bool × List Bool),
          (changeLog Bool Bool).interp ρ (put true (put false (ret true)) : Prog Bool Bool) =
            (changeLog Bool Bool).interp ρ
              (nf (run (put true (put false (ret true)) : Prog Bool Bool)))) ↔
        ObsEq (put true (put false (ret true)) : Prog Bool Bool)
          (nf (run (put true (put false (ret true)))))) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:238-242
theorem forall_interp_tight_nontrivial :
    GetPut (unitModel Bool) ∧ PutGet (unitModel Bool) ∧ PutPut (unitModel Bool) ∧
    ¬ ((∀ ρ : Bool → Unit, (unitModel Bool).interp ρ (ret true : Prog Bool Bool) =
          (unitModel Bool).interp ρ (ret false)) ↔
        ObsEq (ret true : Prog Bool Bool) (ret false)) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:229-231
theorem nv_forall_interp_eq_iff_obsEq :
    GetPut (valueOnly Bool Bool) ∧ PutGet (valueOnly Bool Bool) ∧
    PutPut (valueOnly Bool Bool) ∧ ∃ x y : Bool → Bool, x ≠ y := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:304-306
theorem extDerivable_tight :
    Derivable allLaws (ret true : Prog Bool Bool) (ret true) ∧
    ¬ ExtDerivable (ret true : Prog Bool Bool) (ret true) (ret true) (ret false) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:297
theorem nv_extDerivable_total : ¬ Derivable allLaws (ret true : Prog Bool Bool) (ret false) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:317-320
theorem extDerivableNoSubst_not_total :
    ¬ Derivable allLaws (ret true : Prog Bool Bool) (ret false) ∧
    ¬ ExtDerivableNoSubst (ret true : Prog Bool Bool) (ret false)
        (put true (ret true)) (put false (ret true)) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:60-63
theorem nv_derivable_lawsExcept_getGet_iff :
    Derivable (lawsExcept .getGet)
      (get fun s => get fun s' => ret (s, s') : Prog Bool (Bool × Bool)) (get fun s => ret (s, s)) ∧
    ¬ Derivable (lawsExcept .getGet) (ret true : Prog Bool Bool) (ret false) := …
```

```lean
-- Toy/StoreLaws/Companions.lean:57-61
theorem empty_carrier_breaks_forall_interp_iff :
    ∃ M : Model Bool Empty, GetPut M ∧ PutGet M ∧ PutPut M ∧
      ¬ ((∀ ρ : Bool → Empty, M.interp ρ (ret true : Prog Bool Bool) =
            M.interp ρ (ret false)) ↔
          ObsEq (ret true : Prog Bool Bool) (ret false)) := …
```

```lean
-- Toy/StoreLaws/Companions.lean:108-111
theorem nv_inertHidden_interp_eq :
    Lawful (inertHidden Bool Bool Bool) ∧
    ∀ (p : Prog Bool Bool) (s h : Bool),
      (inertHidden Bool Bool Bool).interp pairRet p (s, h) = ((run p s).1, ((run p s).2, h)) := …
```

### Auxiliary lemmas cited by name

Supporting theorems named in the cards, the law-profile table, the non-claims or the escape hatches, quoted verbatim.

```lean
-- Toy/StoreLaws/Lemmas.lean:83
theorem intended_lawful : Lawful (intended S V) := …
```

```lean
-- Toy/StoreLaws/Lemmas.lean:96-98
theorem laws_via_const_hold (M : Model S X) :
    GetGetVia (fun _ : X => ()) M ∧ GetPutVia (fun _ : X => ()) M ∧
    PutGetVia (fun _ : X => ()) M ∧ PutPutVia (fun _ : X => ()) M := …
```

```lean
-- Toy/StoreLaws/Lemmas.lean:111-112
theorem isHom_eq_fromObs {V : Type} (M : Model S X) (ρ : V → X) (h : (S → V × S) → X)
    (hh : IsHom M ρ h) : h = M.fromObs ρ := …
```

```lean
-- Toy/StoreLaws/Lemmas.lean:167-168
theorem Derivable.getGet_of (hGP : L .getPut) (hPG : L .putGet) (k : S → S → Prog S V) :
    Derivable L (.get fun s => .get fun s' => k s s') (.get fun s => k s s) := …
```

```lean
-- Toy/StoreLaws/Lemmas.lean:194-195
theorem Derivable.bind_left {W : Type} {p q : Prog S V} (h : Derivable L p q)
    (σ : V → Prog S W) : Derivable L (p.bind σ) (q.bind σ) := …
```

```lean
-- Toy/StoreLaws/Lemmas.lean:274-275
theorem unit_cell_putPut_of_getPut_putGet {X : Type} (M : Model Unit X)
    (hGP : GetPut M) (hPG : PutGet M) : PutPut M := …
```

```lean
-- Toy/StoreLaws/Lemmas.lean:281-282
theorem unit_cell_lawful_of_getPut_putPut {X : Type} (M : Model Unit X)
    (hGP : GetPut M) (hPP : PutPut M) : Lawful M := …
```

```lean
-- Toy/StoreLaws/Lemmas.lean:307-308
theorem empty_cell_lawful_of_getPut {X : Type} (M : Model Empty X) (hGP : GetPut M) :
    Lawful M := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:19
theorem valueOnly_lawful : Lawful (valueOnly S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:22
theorem unitModel_lawful : Lawful (unitModel S) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:25
theorem inertHidden_lawful : Lawful (inertHidden S H V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:32
theorem writeLog_getGet {S V : Type} : GetGet (writeLog S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:34
theorem writeLog_putGet {S V : Type} : PutGet (writeLog S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:36
theorem writeLog_not_getPut : ¬ GetPut (writeLog Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:41
theorem writeLog_not_putPut : ¬ PutPut (writeLog Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:50
theorem changeLog_getGet {S V : Type} [DecidableEq S] : GetGet (changeLog S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:52
theorem changeLog_getPut {S V : Type} [DecidableEq S] : GetPut (changeLog S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:57
theorem changeLog_putGet {S V : Type} [DecidableEq S] : PutGet (changeLog S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:60
theorem changeLog_not_putPut : ¬ PutPut (changeLog Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:69
theorem writesIgnored_getGet {S V : Type} : GetGet (writesIgnored S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:71
theorem writesIgnored_getPut {S V : Type} : GetPut (writesIgnored S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:73
theorem writesIgnored_putPut {S V : Type} : PutPut (writesIgnored S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:75
theorem writesIgnored_not_putGet : ¬ PutGet (writesIgnored Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:84
theorem dirtyBit_getGet {S V : Type} : GetGet (dirtyBit S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:86
theorem dirtyBit_putGet {S V : Type} : PutGet (dirtyBit S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:88
theorem dirtyBit_putPut {S V : Type} : PutPut (dirtyBit S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:90
theorem dirtyBit_not_getPut : ¬ GetPut (dirtyBit Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:99
theorem readToClear_getPut {S V : Type} (d : S) : GetPut (readToClear S V d) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:101
theorem readToClear_putPut {S V : Type} (d : S) : PutPut (readToClear S V d) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:104
theorem readToClear_not_getGet : ¬ GetGet (readToClear Bool Bool false) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:109
theorem readToClear_not_putGet : ¬ PutGet (readToClear Bool Bool false) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:118
theorem faultingCounter_putGet {S V : Type} : PutGet (faultingCounter S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:120
theorem faultingCounter_putPut {S V : Type} : PutPut (faultingCounter S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:123
theorem faultingCounter_not_getGet : ¬ GetGet (faultingCounter Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:128
theorem faultingCounter_not_getPut : ¬ GetPut (faultingCounter Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:137
theorem readCounter_putPut {S V : Type} : PutPut (readCounter S V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:139
theorem readCounter_not_getGet : ¬ GetGet (readCounter Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:144
theorem readCounter_not_getPut : ¬ GetPut (readCounter Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:149
theorem readCounter_not_putGet : ¬ PutGet (readCounter Bool Bool) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:159
theorem coupledHidden_lawful {V : Type} : Lawful (coupledHidden V) := …
```

```lean
-- Toy/StoreLaws/Profiles.lean:171-173
theorem getGetVia_not_entailed_by_getPutVia_putGetVia :
    GetPutVia Prod.fst fstViaModel ∧ PutGetVia Prod.fst fstViaModel ∧
    ¬ GetGetVia Prod.fst fstViaModel := …
```

```lean
-- Toy/StoreLaws/Results.lean:241-243
theorem fromObs_range_eq_interp_range {S X V : Type} (M : Model S X)
    (hGP : GetPut M) (hPG : PutGet M) (hPP : PutPut M) (ρ : V → X) (x : X) :
    (∃ o : S → V × S, M.fromObs ρ o = x) ↔ (∃ p : Prog S V, M.interp ρ p = x) := …
```

```lean
-- Toy/StoreLaws/Results.lean:312-318
theorem valueOnly_separates_other_valuation_and_substitution :
    (valueOnly Bool Bool).interp (fun _ s => s) (put true (ret true) : Prog Bool Bool) ≠
      (valueOnly Bool Bool).interp (fun _ s => s) (put false (ret true)) ∧
    (valueOnly Bool Bool).interp valueOnlyRet
        ((put true (ret true) : Prog Bool Bool).bind (fun _ => get ret)) ≠
      (valueOnly Bool Bool).interp valueOnlyRet
        ((put false (ret true) : Prog Bool Bool).bind (fun _ => get ret)) := …
```

```lean
-- Toy/StoreLaws/Results.lean:441
theorem empty_cell_all_derivable {V : Type} (p q : Prog Empty V) : Derivable allLaws p q := …
```

```lean
-- Toy/StoreLaws/Results.lean:447
theorem unit_cell_unit_result_all_derivable (p q : Prog Unit Unit) : Derivable allLaws p q := …
```

```lean
-- Toy/StoreLaws/Results.lean:455-457
theorem writeLog_laws_via_dropLog {S V : Type} :
    GetGetVia dropLog (writeLog S V) ∧ GetPutVia dropLog (writeLog S V) ∧
    PutGetVia dropLog (writeLog S V) ∧ PutPutVia dropLog (writeLog S V) := …
```

```lean
-- Toy/StoreLaws/Results.lean:508-511
theorem inertHidden_pairFlipRet_changes_hidden :
    Lawful (inertHidden Bool Bool Bool) ∧
    (inertHidden Bool Bool Bool).interp pairFlipRet (ret true : Prog Bool Bool) (false, false) =
      (true, (false, true)) := …
```

```lean
-- Toy/StoreLaws/Results.lean:518-521
theorem coupledHidden_lawful_changes_hidden :
    Lawful (coupledHidden Bool) ∧
    (coupledHidden Bool).interp pairRet (put true (ret true) : Prog Bool Bool) (false, false) =
      (true, (true, true)) := …
```

```lean
-- Toy/StoreLaws/Results.lean:530-533
theorem intended_leafLog_lawful_and_logs :
    Lawful (intended Bool (Bool × List Bool)) ∧
    (intended Bool (Bool × List Bool)).interp (fun v s => ((v, [true]), s))
      (put true (ret false) : Prog Bool Bool) false = ((false, [true]), true) := …
```

```lean
-- Toy/StoreLaws/Results.lean:561-564
theorem getGet_not_derivable_from_getPut_putPut :
    ObsEq (get fun _ => get fun s' => ret s' : Prog Bool Bool) (get fun s => ret s) ∧
    ¬ Derivable (fun l => l = .getPut ∨ l = .putPut)
      (get fun _ => get fun s' => ret s' : Prog Bool Bool) (get fun s => ret s) := …
```

```lean
-- Toy/StoreLaws/Results.lean:576-579
theorem getGet_not_derivable_from_putGet_putPut :
    ObsEq (get fun _ => get fun s' => ret s' : Prog Bool Bool) (get fun s => ret s) ∧
    ¬ Derivable (fun l => l = .putGet ∨ l = .putPut)
      (get fun _ => get fun s' => ret s' : Prog Bool Bool) (get fun s => ret s) := …
```

```lean
-- Toy/StoreLaws/Witnesses.lean:202-205
theorem fromObs_not_surjective_inertHidden :
    Lawful (inertHidden Bool Bool Bool) ∧
    ∃ x : Bool × Bool → Bool × (Bool × Bool),
      ∀ o : Bool → Bool × Bool, (inertHidden Bool Bool Bool).fromObs pairRet o ≠ x := …
```

```lean
-- Toy/StoreLaws/Companions.lean:70-71
theorem empty_cell_getPut_not_nontrivial {X : Type} (M : Model Empty X)
    (hGP : GetPut M) : ¬ ∃ x y : X, x ≠ y := …
```

```lean
-- Toy/StoreLaws/Companions.lean:77
theorem writeLog_lawful_of_empty_cell {V : Type} : Lawful (writeLog Empty V) := …
```

```lean
-- Toy/StoreLaws/Companions.lean:85
theorem writeLog_lawful_of_empty_result {S : Type} : Lawful (writeLog S Empty) := …
```

```lean
-- Toy/StoreLaws/Companions.lean:93
theorem readCounter_lawful_of_empty_cell {V : Type} : Lawful (readCounter Empty V) := …
```

```lean
-- Toy/StoreLaws/Companions.lean:101
theorem readCounter_lawful_of_empty_result {S : Type} : Lawful (readCounter S Empty) := …
```

## Boundaries

### Non-claims (read first)

#### Shared non-claims (apply to every result)

- Model–system relation: none proved. These are statements about the toy model (one cell, free program syntax, set-like carriers); they neither establish nor refute the corresponding claims about any concrete monad, programming language, library, storage device or verification tool.
- Satisfaction is strict unless a `...Via` variant is named: a law is an equation in the carrier for all carrier elements. Satisfaction through an observation compares the two sides of each law instance at top level after the observation; it is neither strict nor behavioral satisfaction.
- One cell. Laws relating several locations, aliasing, concurrency, recursion, nontermination and other effects are not examined.
- `Prog.get` takes an arbitrary Lean function `S → Prog S V` as its continuation, and rule `get_congr` of `Derivable` has one premise per value of `S`. No result gives a decision procedure, a terminating rewrite system or a statement about finitary program syntax.
- Several proofs use classical logic; `Classical.choice` appears in the axiom record. Constructive versions are not examined.

#### Result 1. `getGet_of_getPut_of_putGet`

- Concerns strict satisfaction (laws as equations in the carrier, for arbitrary carrier elements as continuations). Satisfaction through an observation (`GetGetVia`, `GetPutVia`, `PutGetVia`, `PutPutVia`) is a different notion: through a non-injective observation the strict entailments need not hold (`getGetVia_not_entailed_by_getPutVia_putGetVia`).
- Does not say get–get follows from either law alone: each hypothesis is tight on a Boolean cell (`getGet_of_tight_getPut`, `getGet_of_tight_putGet`).
- Does not say get–get is redundant together with put–put and one of the other two laws: `getGet_not_entailed_by_pairs_with_putPut_bool` gives Boolean-cell models of {get–put, put–put} and of {put–get, put–put} violating get–get.
- The syntactic counterpart, derivability of every get–get instance from get–put and put–get instances, is the supporting lemma `Derivable.getGet_of`.
- Models here take get and put with explicit continuations. For a monadic interface (get : m S, put : S → m Unit) the translation to these models relies on the monad laws (see the modeling bridge under Applicability); monads that violate them are not examined.
- Concerns one cell; laws relating reads of different locations in multi-location state are not examined.
- The shared non-claims above apply.

#### Result 2. `getPut_putGet_putPut_independent_bool`

- Does not provide a model satisfying get–put, put–get and put–put and violating get–get; none exists (`getGet_of_getPut_of_putGet`).
- The violations are proved for S = Bool and V = Bool. The positive law facts of the three models are proved for all S and V (`changeLog_getGet`, `changeLog_getPut`, `changeLog_putGet`, `writesIgnored_getGet`, `writesIgnored_getPut`, `writesIgnored_putPut`, `dirtyBit_getGet`, `dirtyBit_putGet`, `dirtyBit_putPut`; `changeLog` assumes decidable equality on S).
- The result is stated for a Boolean cell. It does not carry over to cells with at most one value: on a one-element cell, get–put and put–get imply put–put (`unit_cell_putPut_of_getPut_putGet`) and get–put and put–put imply all four laws (`unit_cell_lawful_of_getPut_putPut`); on an empty cell, get–put alone implies all four laws (`empty_cell_lawful_of_getPut`). Cells with three or more values are not examined.
- The models are toy renderings of a change log, a read-only device and a modified flag.
- The shared non-claims above apply.

#### Result 3. `getGet_not_entailed_by_pairs_with_putPut_bool`

- Does not contradict `getGet_of_getPut_of_putGet`: `readToClear` violates put–get and `faultingCounter` violates get–put (`readToClear_not_putGet`, `faultingCounter_not_getPut`).
- Proved for S = Bool, V = Bool. On a one-element cell, get–put and put–put imply get–get (`unit_cell_lawful_of_getPut_putPut`), so the read-to-clear countermodel has no one-element analogue; other cell types are not examined.
- Concerns strict satisfaction (laws as equations in the carrier, for arbitrary carrier elements as continuations). Satisfaction through an observation (`GetGetVia`, `GetPutVia`, `PutGetVia`, `PutPutVia`) is a different notion: through a non-injective observation the strict entailments need not hold (`getGetVia_not_entailed_by_getPutVia_putGetVia`).
- The shared non-claims above apply.

#### Result 4. `entailsBool_iff`

- The result is stated for a Boolean cell. It does not carry over to cells with at most one value: on a one-element cell, get–put and put–get imply put–put (`unit_cell_putPut_of_getPut_putGet`) and get–put and put–put imply all four laws (`unit_cell_lawful_of_getPut_putPut`); on an empty cell, get–put alone implies all four laws (`empty_cell_lawful_of_getPut`). Cells with three or more values are not examined.
- Concerns entailment of single laws by sets of laws, with models on carriers in Type; entailment of other equations is not characterized here.
- The syntactic counterpart is stated for the four law sets that omit one law (`derivable_lawsExcept_getGet_iff`, `dropGetPut_loses_nf`, `dropPutGet_loses_nf`, `dropPutPut_loses_nf`) and for get–get from the two-law sets {get–put, put–put} and {put–get, put–put} (`getGet_not_derivable_from_getPut_putPut`, `getGet_not_derivable_from_putGet_putPut`); other law sets are not examined syntactically.
- Concerns strict satisfaction (laws as equations in the carrier, for arbitrary carrier elements as continuations). Satisfaction through an observation (`GetGetVia`, `GetPutVia`, `PutGetVia`, `PutPutVia`) is a different notion: through a non-injective observation the strict entailments need not hold (`getGetVia_not_entailed_by_getPutVia_putGetVia`).
- The shared non-claims above apply.

#### Result 5. `derivable_nf_of_getPut_putGet_putPut`

- Does not require get–get in L; it is derivable from get–put and put–get (`Derivable.getGet_of`), and including it is harmless.
- Normal forms are relative to the free-monad syntax Prog, where the monad laws hold as literal equalities of programs; a syntax with an explicit bind constructor (where monad laws are extra axioms) is not covered.
- `Derivable` contains the congruence rule get_congr with one premise per value of S; for infinite S this is an infinitary proof system (as with the infinitary lookup operation of Plotkin–Power), and the theorem gives no decision procedure for derivability.
- Prog.get takes an arbitrary Lean function S → Prog S V as its continuation, and the canonical program nf (run p) uses arbitrary functions S → S and S → V. In a programming language whose programs are finitary syntax these functions need not be definable, so the theorem says nothing about normal forms within such a syntax.
- Establishes that a derivation exists in the equational relation `Derivable L`; it is not a terminating or confluent rewrite system and gives no normalization algorithm.
- Says nothing about several cells, recursion, or other effects.
- The shared non-claims above apply.

#### Result 6. `canon_eq_of_derivable`

- Uniqueness up to derivability holds for every law set L. Existence of canonical forms is proved from get–put, put–get and put–put (`derivable_nf_of_getPut_putGet_putPut`); on a Boolean cell with Boolean results each of these three is tight for existence (`dropGetPut_loses_nf`, `dropPutGet_loses_nf`, `dropPutPut_loses_nf`).
- Says nothing about uniqueness up to equality in a model other than the intended one: at a fixed valuation, lawful models may identify different canonical programs (`valueOnly_lawful_not_faithful`).
- The shared non-claims above apply.

#### Result 7. `derivable_iff_obsEq_of_getPut_putGet_putPut`

- Left-to-right (soundness) holds for every law set; the hypotheses are used for right-to-left (completeness).
- Observational equivalence here observes final value and final cell content from every initial content; weaker observations (e.g. observing the final value alone) are not characterized here.
- For infinite S, `Derivable L` is an infinitary proof system (get_congr has one premise per value of S) and `ObsEq` is extensional equality of functions on S; the theorem gives no decision procedure for either relation.
- The shared non-claims above apply.

#### Result 8. `interp_eq_fromObs_run_of_getPut_putGet_putPut`

- Weakening strict satisfaction to satisfaction through a non-injective observation defeats the factorization: the write log satisfies all four laws through `dropLog` and distinguishes observationally equivalent programs (`writeLog_via_distinguishes_obsEq`).
- Does not say the factor map is injective: at a fixed valuation, lawful models may identify different observations (`valueOnly_lawful_not_faithful`, `unitModel_lawful_not_faithful`).
- The factorization is per valuation ρ; how M.interp depends on ρ is not constrained beyond this formula.
- Does not exclude effects carried by the valuation: the strictly lawful intended model with results Bool × List Bool records a log supplied by the valuation (`intended_leafLog_lawful_and_logs`), and the strictly lawful `inertHidden` model changes its hidden component under the valuation `pairFlipRet` (`inertHidden_pairFlipRet_changes_hidden`). The laws constrain get and put; how these toy models relate to monad transformers such as a state monad over a writer monad is not proved here.
- The shared non-claims above apply.

#### Result 9. `interp_eq_of_obsEq_of_getPut_putGet_putPut`

- Weakening strict satisfaction to satisfaction through the log-forgetting observation defeats the conclusion: the write log satisfies all four laws through `dropLog` and distinguishes put true (put false (ret true)) from put false (ret true) (`writeLog_via_distinguishes_obsEq`).
- Does not say lawful models are faithful at a fixed valuation (`valueOnly_lawful_not_faithful`); faithfulness across all valuations for models with two distinct carrier elements is `forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial`.
- Does not exclude hidden state that no operation touches (`inertHidden_interp_eq`), nor hidden state that put changes as a function of the cell contents (`coupledHidden_lawful_changes_hidden`).
- Does not exclude effects carried by the valuation: the strictly lawful intended model with results Bool × List Bool records a log supplied by the valuation (`intended_leafLog_lawful_and_logs`), and the strictly lawful `inertHidden` model changes its hidden component under the valuation `pairFlipRet` (`inertHidden_pairFlipRet_changes_hidden`). The laws constrain get and put; how these toy models relate to monad transformers such as a state monad over a writer monad is not proved here.
- The shared non-claims above apply.

#### Result 10. `fromObs_isHom_unique_of_getPut_putGet_putPut`

- The uniqueness half holds for every model M; it uses none of the laws (`isHom_eq_fromObs`).
- Does not say M.fromObs ρ is surjective onto the carrier X: for the strictly lawful `inertHidden Bool Bool Bool` and ρ = `pairRet` it is not (`fromObs_not_surjective_inertHidden`). Its image is exactly the set of program interpretations under ρ (`fromObs_range_eq_interp_range`). That every strictly lawful model is a homomorphic image of the intended model on its own carrier is `getPut_putGet_putPut_iff_exists_surjective_isHom`.
- Does not say the homomorphism is injective (`valueOnly_lawful_not_faithful`).
- Freeness is stated for set-like carriers (Lean types) and one cell; the categorical generality of Plotkin–Power (categories with countable products and coproducts, several locations) is not formalized.
- The shared non-claims above apply.

#### Result 11. `getPut_putGet_putPut_iff_exists_surjective_isHom`

- The surjectivity conjunct adds no condition: `IsHom M id h` already implies it, since its return clause sends `intendedRet x` to x for every x : X (`isHom_id_surjective`); the characterization with the conjunct omitted is `getPut_putGet_putPut_iff_exists_isHom`.
- The intended model here has result type X, the carrier itself. For another result type V and valuation ρ the comparison map need not be surjective (`fromObs_not_surjective_inertHidden`).
- Does not say M is isomorphic to an intended model; at a fixed valuation strictly lawful models can be unfaithful (`valueOnly_lawful_not_faithful`).
- Get–get is not among the conditions; it follows from get–put and put–get (`getGet_of_getPut_of_putGet`).
- Concerns strict satisfaction (laws as equations in the carrier, for arbitrary carrier elements as continuations). Satisfaction through an observation (`GetGetVia`, `GetPutVia`, `PutGetVia`, `PutPutVia`) is a different notion: through a non-injective observation the strict entailments need not hold (`getGetVia_not_entailed_by_getPutVia_putGetVia`).
- The shared non-claims above apply.

#### Result 12. `lawful_not_faithful`

- Refutes 'lawful implies faithful at a given valuation'; it does not refute 'lawful implies homomorphic image', which holds (`interp_eq_fromObs_run_of_getPut_putGet_putPut`, `getPut_putGet_putPut_iff_exists_surjective_isHom`).
- The unfaithfulness of `valueOnly Bool Bool` depends on the valuation: under the valuation fun _ s => s, and for the substitution instance with get ret in place of each returned value, it separates put true (ret true) from put false (ret true) (`valueOnly_separates_other_valuation_and_substitution`). Across all valuations every strictly lawful model with two distinct carrier elements is faithful (`forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial`); the one-point model is the trivial case.
- The shared non-claims above apply.

#### Result 13. `forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial`

- Quantifies over all valuations ρ : V → X. At a fixed valuation a strictly lawful model with two distinct carrier elements can still identify observationally distinct programs (`valueOnly_lawful_not_faithful`).
- The proof uses classical logic (case distinctions on equality of cell contents and of returned values).
- Says nothing about models that satisfy the laws through an observation (`writeLog_via_distinguishes_obsEq`).
- On an empty cell (S = Empty) the hypotheses hGP and hnt cannot hold together (`empty_cell_getPut_not_nontrivial`), so the theorem has no instances there.
- The shared non-claims above apply.

#### Result 14. `extDerivable_total_of_not_derivable`

- 'Collapse' means: all programs of the fixed type Prog S V are identified, including ret v₁ = ret v₂ when V has two values. For a one-element result type it identifies programs that differ in their final cell content; there are no distinct return values to identify. Theories spanning several result types are not formalized.
- Closure under substitution is built into the extended theory (rule `ExtDerivable.inst`). Without it the extension need not collapse: adding ret true = ret false alone (`ExtDerivableNoSubst`) does not identify put true (ret true) with put false (ret true) (`extDerivableNoSubst_not_total`).
- The proof uses classical logic: it builds a continuation that branches on whether the cell holds a given value and a substitution that branches on equality of returned values. Prog.get accepts arbitrary Lean functions as continuations; whether the result holds for a syntax restricted to computable or finitary continuations, or constructively without decidable equality on S and V, is not examined.
- Does not contradict `valueOnly_lawful_not_faithful`: `valueOnly Bool Bool` validates put true (ret true) = put false (ret true) under the valuation `valueOnlyRet` but not under the valuation fun _ s => s, and not for the substitution instance with get ret in place of each returned value (`valueOnly_separates_other_valuation_and_substitution`), so it is not a model of the theory extended by that equation.
- On an empty cell, and on a one-element cell with one-element results, every two programs are already derivably equal (`empty_cell_all_derivable`, `unit_cell_unit_result_all_derivable`), so the hypothesis cannot be met there.
- Concerns extensions by equations between programs. Extensions by inequations, conditional equations, new operations, or several cells are not examined.
- The shared non-claims above apply.

#### Result 15. `writeLog_via_distinguishes_obsEq`

- `GetGetVia`, `GetPutVia`, `PutGetVia` and `PutPutVia` compare the two sides of each law instance at top level after applying the observation; they are not behavioral satisfaction, which compares the sides in every observable context. Through a constant observation they hold for every model (`laws_via_const_hold`), and through a non-injective observation they need not obey the entailments of the strict laws (`getGetVia_not_entailed_by_getPutVia_putGetVia`).
- Strictly, the write log violates get–put and put–put (`writeLog_strict_profile_bool`).
- Through `dropLog` the four laws hold for every cell type and result type (`writeLog_laws_via_dropLog`); the distinguishing pair is shown for S = V = Bool.
- The shared non-claims above apply.

#### Result 16. `writeLog_strict_profile_bool`

- The violations are proved for S = V = Bool, and they depend on inhabited cell and result types: with an empty cell type or an empty result type the write-log model satisfies all four laws strictly (`writeLog_lawful_of_empty_cell`, `writeLog_lawful_of_empty_result`). Other inhabited types are not examined. Get–get and put–get hold for all S, V (`writeLog_getGet`, `writeLog_putGet`).
- The shared non-claims above apply.

#### Result 17. `readCounter_strict_profile_bool`

- The violations are proved for S = V = Bool, and they depend on inhabited cell and result types: with an empty cell type or an empty result type the read-counter model satisfies all four laws strictly (`readCounter_lawful_of_empty_cell`, `readCounter_lawful_of_empty_result`). Other inhabited types are not examined. Put–put holds for all S, V (`readCounter_putPut`).
- A read counter does not isolate get–get: no model satisfies get–put, put–get and put–put and violates get–get (`getGet_of_getPut_of_putGet`).
- The shared non-claims above apply.

#### Result 18. `inertHidden_interp_eq`

- Preservation of the hidden component depends on the valuation `pairRet`: under `pairFlipRet` the same strictly lawful model changes the hidden component (`inertHidden_pairFlipRet_changes_hidden`).
- Does not say strictly lawful hidden state must be left untouched by put: `coupledHidden` flips a hidden bit whenever a write changes the cell and satisfies all four laws strictly (`coupledHidden_lawful_changes_hidden`). The general constraint is the factorization `interp_eq_fromObs_run_of_getPut_putGet_putPut`.
- Does not classify the strictly lawful models with hidden state.
- The correspondence between strictly lawful state-transformer models and very well-behaved lenses is not formalized here; lens laws are outside the scope of this package.
- The shared non-claims above apply.

#### Result 19. `derivable_lawsExcept_getGet_iff`

- Does not say any other law can be dropped from the four: on a Boolean cell, dropping get–put, put–get or put–put loses equations (`dropGetPut_loses_nf`, `dropPutGet_loses_nf`, `dropPutPut_loses_nf`).
- Dropping get–get is harmless when get–put and put–get are both present. It is not harmless from {get–get, get–put, put–put} or {get–get, put–get, put–put}: on a Boolean cell, a get–get instance is derivable neither from {get–put, put–put} nor from {put–get, put–put} (`getGet_not_derivable_from_getPut_putPut`, `getGet_not_derivable_from_putGet_putPut`).
- The shared non-claims above apply.

#### Result 20. `drop_law_loses_nf`

- Each non-derivability is shown by soundness in one model of the remaining three laws (`dirtyBit`, `writesIgnored`, `changeLog` respectively); other pairs of programs lost by dropping a law are not enumerated.
- Proved for S = V = Bool. On a one-element cell the model-level independence behind these witnesses fails (`unit_cell_putPut_of_getPut_putGet`, `unit_cell_lawful_of_getPut_putPut`); whether the syntactic non-derivability results hold on other cell types is not examined.
- The shared non-claims above apply.


### Escape hatches

Which hypotheses, if dropped or weakened, defeat a result (each defeat is a kernel-checked theorem):

- Result 9 (`interp_eq_of_obsEq_of_getPut_putGet_putPut`, the impossibility result). Dropping get–put, put–get or put–put defeats it on a Boolean cell with Boolean results (`interp_factor_tight_getPut`, `interp_factor_tight_putGet`, `interp_factor_tight_putPut`); replacing strict satisfaction by satisfaction through the log-forgetting observation `dropLog` defeats it (`writeLog_via_distinguishes_obsEq`); dropping the premise `ObsEq p q` defeats it (`interp_eq_tight_obsEq`). Effects supplied by the valuation are not constrained by the laws (`intended_leafLog_lawful_and_logs`, `inertHidden_pairFlipRet_changes_hidden`).
- Result 8 (`interp_eq_fromObs_run_of_getPut_putGet_putPut`) and Result 10 (`fromObs_isHom_unique_of_getPut_putGet_putPut`). Dropping any one of the three laws defeats them on a Boolean cell with Boolean results (`interp_factor_tight_getPut`, `interp_factor_tight_putGet`, `interp_factor_tight_putPut`; `fromObs_tight_getPut`, `fromObs_tight_putGet`, `fromObs_tight_putPut`).
- Result 13 (`forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial`). Fixing one valuation instead of quantifying over all valuations defeats faithfulness (`valueOnly_lawful_not_faithful`); a subsingleton carrier defeats it, whether one-point (`forall_interp_tight_nontrivial`) or empty (`empty_carrier_breaks_forall_interp_iff`).
- Result 14 (`extDerivable_total_of_not_derivable`). Without closure of the added equation under substitution the extension need not collapse: adding `ret true = ret false` alone does not identify `put true (ret true)` with `put false (ret true)` (`extDerivableNoSubst_not_total`). An equation that is already derivable adds nothing (`extDerivable_tight`).
- Results 2, 3, 4 and 20 (Boolean cell). On a cell with at most one value the independence pattern changes: on a one-element cell get–put and put–get imply put–put (`unit_cell_putPut_of_getPut_putGet`), and get–put and put–put imply all four laws (`unit_cell_lawful_of_getPut_putPut`); on an empty cell get–put alone implies all four laws (`empty_cell_lawful_of_getPut`).
- Results 16 and 17 (Boolean cell, Boolean results). With an empty cell type or an empty result type the violations disappear (`writeLog_lawful_of_empty_cell`, `writeLog_lawful_of_empty_result`, `readCounter_lawful_of_empty_cell`, `readCounter_lawful_of_empty_result`).

### Hypotheses whose tightness is unknown

None. Every hypothesis of every result is tight, with a kernel-checked counterexample in the class stated in its ledger entry.

### Not examined

- Cells with three or more values, for Results 2, 3, 4 and 20 (proved for a Boolean cell).
- Violations of the write-log and read-counter models for inhabited cell or result types other than `Bool`.
- State with several locations, arrays or heaps, and local state (the local-state completeness result of Staton 2010 is background, not re-derived).
- Lens laws and the correspondence between strictly lawful state-transformer models and very well-behaved lenses.
- Hilbert–Post completeness for theories that span several result types.

### Disproved or dropped statements

None. Every result listed in this report is kernel-checked as stated; no statement of the package was found false, and none was left unproved.

## Evidence

### Kernel check

- Toolchain: `leanprover/lean4:v4.34.1` (tag `v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`), with its core library and no other dependencies; `lean/lakefile.toml` declares one library, `Toy`, and no dependencies. Observed on 2026-11-21: `lake build` succeeds, and the sources contain no `sorry`, `admit`, `native_decide`, `axiom` or `opaque` declarations, `implemented_by`, `extern` or `unsafe`.
- Axioms: every declaration of the library's modules (366 declarations, computed with Lean's `collectAxioms`) depends on a subset of `propext`, `Classical.choice` and `Quot.sound`; the per-declaration lists are in `audit/axioms.json`.
- Hashes: for every Lean name referenced by `results.json`, `audit/statements.json` records the SHA-256 of its statement (the Lean `repr` of its type) and of its definition closure (the types and values of every package constant reachable from the statement, theorem bodies excluded, one line per constant, sorted). The table lists them with the axioms of each name.

### Per-declaration record

| Name | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `getGet_of_getPut_of_putGet` | main result | `Quot.sound`, `propext` | `8e8dde1eb9ea2f90457f5a89d5031258474696249056e14bfda705b19e7558e8` | `dcc481ecbc4cf2390de3740f2156eab647a77b6028d7d3a0ff279485725b863d` (7) |
| `getPut_putGet_putPut_independent_bool` | main result | `Quot.sound`, `propext` | `9cc9b8571d7d2c994b8b8d9289ffb8d737cdc07dcf53029a125c0d3ba798368c` | `91208c7b725226ba4e71fe871e2f2a2829a2e2dbb6cf5b302a1aa7f7c10cfded` (11) |
| `getGet_not_entailed_by_pairs_with_putPut_bool` | main result | none | `bb4554734a6608e7636a7e2cc7b94753b403b32f2595cea26bf7019d33d64a12` | `4be27ae3e9ad420377e73893ca41ca4096110b519f7ab1c56402b8de1e4ca474` (10) |
| `entailsBool_iff` | main result | `Classical.choice`, `Quot.sound`, `propext` | `cf2b08ea77c1919ad34bc610a5a6676243dcc4dac08b3b753c931844bc22fed4` | `d652cd2eabaf3b82094f97c87eb2276512b842a564d5c0af1e27bfd308dd1ac0` (20) |
| `derivable_nf_of_getPut_putGet_putPut` | main result | none | `396c020eb5cefe013fe92935c4c1fac72b820f90a0b0de7dd34cc2284345e02e` | `99ba5abde757e1d12a63cc0adede952a76d8230f33b6d6cce26fb5e033c3cac3` (30) |
| `canon_eq_of_derivable` | main result | `Quot.sound` | `8d5fc62cf6fb231ce9c565daef1c5498e307801e8e0fa33138203900426e9146` | `10dce37b77a3b60e2c4d3a9b6a609998030a451704e7d83ff2f9d194bba398bd` (21) |
| `derivable_iff_obsEq_of_getPut_putGet_putPut` | main result | `Quot.sound` | `955bd329b969446401d1f59be0a50bb74ff4161aa9216d62fc748abebffa2d99` | `f110c0bb7b7bef22b9517db2e9e9dfa23e3db8ab766d14342f11cd0426f35f3a` (29) |
| `interp_eq_fromObs_run_of_getPut_putGet_putPut` | main result | `Quot.sound`, `propext` | `a0b183b223e53d3c849e95202782b709dcc24c3a5729ae25c7c93b0bb9179b06` | `1997acfceff5e9ad08b0837e64819ff9ef31c20c5e3eb127b1de4fde423591e4` (23) |
| `interp_eq_of_obsEq_of_getPut_putGet_putPut` | main result | `Quot.sound`, `propext` | `cd24ac99ac70375b6c7415d2c8159aa56a0819081797787e0a8d40dc1610084d` | `d54c143298db0394a7b1ad2f6465db60f39fb6872b5089af965166ecd82065b7` (23) |
| `fromObs_isHom_unique_of_getPut_putGet_putPut` | main result | `Quot.sound`, `propext` | `20adb26a2c9290c564070658fd430ede96eaa304337682dbe70ee4e74087f741` | `0ef9bd3c86fec92a29880f66e7ae38b41cfc4526985391f3f8431d83f3d13ab7` (11) |
| `getPut_putGet_putPut_iff_exists_surjective_isHom` | main result | `Quot.sound`, `propext` | `6c296b8c725ae78754996180a01a4bb7d22fb67368bb3bdd5994cbc4ddd410cc` | `ab63185e56ca159da9b5116301e5bd55d2403945f4e3e287d8f62781cd1f92dd` (10) |
| `valueOnly_lawful_not_faithful` | main result | none | `dcaab0b742d74e58f3fa004e719ca458b7491388ca1807d278262f99ffdaa24a` | `8007c1a884fab9013583b14bd33cc03ca1f7478830998c47bf1744af89436331` (27) |
| `unitModel_lawful_not_faithful` | main result | none | `a1f35ca2a9f104bf88952400ba310b264fe3455bb6c0e5c451910d4ece9a5b0c` | `b9201e6263930117376a8d1d8e026c2a04bf9712d6e552cf38247567877ba84d` (26) |
| `forall_interp_eq_iff_obsEq_of_getPut_putGet_putPut_of_nontrivial` | main result | `Classical.choice`, `Quot.sound`, `propext` | `821d46b27bf74747283f24893a5ec70439c3ac63bb58498a65d74a6fc1c6ee7b` | `d54c143298db0394a7b1ad2f6465db60f39fb6872b5089af965166ecd82065b7` (23) |
| `extDerivable_total_of_not_derivable` | main result | `Classical.choice`, `Quot.sound`, `propext` | `c3b02b6661689cd4eb6e8feafdf52734fe07046296f6351ea89d2efcb11a6622` | `e07d87b3b73643f8612089e54a0076009a8bce7a6cd5f07d0a0aa7246d94fe03` (36) |
| `writeLog_via_distinguishes_obsEq` | main result | none | `79e1a451944a8545e88f13666e6119856b8de9e780b56dadcc395e1ea2a31449` | `0b05562abb0dc9f11b3e2e4971303df2424409d42f18e026c9b8f6e6ab60a8d8` (27) |
| `writeLog_strict_profile_bool` | main result | none | `0b37c0ffb4b910933408027dfd5215d1a8eee7b3d16795d84cdd4fc1932424c4` | `bd578dead3f1816e3a867dcc2dbf39f973846df93c9bf534d46a4afc6eabf5c0` (9) |
| `readCounter_strict_profile_bool` | main result | none | `4ee3d70cae767c77556c9047853923ff63f1ce142c66d9676c0fea03f8533a0a` | `ebd1d5b5122d8249736704e10d0819a970149de759fdb45c64137e6ba5d47dec` (9) |
| `inertHidden_interp_eq` | main result | none | `7961f38c82dcc1ea8dbb7fce812082e2773421ce36d79b07ad20cce9a0c15a82` | `0f07c917a97cc16a821093928791dd661f2cc9c666c6ae81f853b23d72cc236b` (26) |
| `derivable_lawsExcept_getGet_iff` | main result | none | `8a579caf258b013341a1aad6c375768a35cc9370e70695ae23215eebafaebd99` | `01fc3e9b63e020f2bf4268b378fca785a43d2c49a22ccdb359e29c66bfe15e94` (22) |
| `dropGetPut_loses_nf` | main result | `Quot.sound` | `646241f5b8472a2e987980b5b2def8dc661e8dae73d90a81846bb3e52abd4aa2` | `b2983f7750f236ece04fff457a9baeae2d2a9de82f75f3a983dfdabe3c14283d` (32) |
| `dropPutGet_loses_nf` | main result | `Quot.sound` | `d88f5fcd2ff40141766f81f2306ca7f81cabda57c774d908bd9bd447026a880f` | `b2983f7750f236ece04fff457a9baeae2d2a9de82f75f3a983dfdabe3c14283d` (32) |
| `dropPutPut_loses_nf` | main result | `Quot.sound`, `propext` | `292041e22a7a64479e7465f60e1a3314eefae2cdcc349ea1ecdd0805c857d633` | `b2983f7750f236ece04fff457a9baeae2d2a9de82f75f3a983dfdabe3c14283d` (32) |
| `Derivable` | definition | none | `eb11374907d1eb16ce8cb73169e1e7b5fad14449e3879036f9b0dd175ad247b6` | `396caa5b7c3c08e78d4e399c5fd8ce6a5f2f302714415a3121db5574e97578d8` (10) |
| `Derivable.bind_left` | auxiliary lemma | none | `a5cc0eaab74e22c89da43b298cf45f3a911a9144ba723db8095ed1133d380ffa` | `f9c0c58cdb723ee6e6c947feb97bd03b2079ecc99770d5bcdc084cbf864bf071` (28) |
| `Derivable.getGet_of` | auxiliary lemma | none | `f8cf096f77c45c1c3d3c7919f95b888aaadb37febb9c2c38c3f9f62d6c394ff3` | `572b19a3a16ad07991d2bc982d6b8aaab9981516f47a983f4e3697a5fb98ad0d` (20) |
| `Derivable.get_congr` | definition (constructor) | none | `db263273888da01ab1c387b16acaaf10b42645a71e32847e759cb16740a99a06` | `572b19a3a16ad07991d2bc982d6b8aaab9981516f47a983f4e3697a5fb98ad0d` (20) |
| `EntailsBool` | definition | none | `eaa45f14ddd73e3a67c016efabfc67acd0b7ac54db181e6cf3511aa32892f9a9` | `1b322cc6ca87a8a415c41aa5d7580eefb8ce720a2687239806ce3b908d5ff080` (6) |
| `ExtDerivable` | definition | none | `0773b98290d577cf5496ac2a2525ca28c886008a9d92ef9555aa9cba867806ff` | `72ce3d133810d0a4fea071493fb606c3069d489f0da5fa41a91558c23b3c74d0` (4) |
| `ExtDerivable.get_congr` | definition (constructor) | none | `4c0e680e607f051a7505766eb6741af1e0b44d01f8f8da2b7872083624e46a4c` | `e07d87b3b73643f8612089e54a0076009a8bce7a6cd5f07d0a0aa7246d94fe03` (36) |
| `ExtDerivable.inst` | definition (constructor) | none | `4cf5b23ea7a9f708e5542244a4ea694b4e6e3eba482130b8d0ce2f56c10aea92` | `e07d87b3b73643f8612089e54a0076009a8bce7a6cd5f07d0a0aa7246d94fe03` (36) |
| `ExtDerivableNoSubst` | definition | none | `0773b98290d577cf5496ac2a2525ca28c886008a9d92ef9555aa9cba867806ff` | `72ce3d133810d0a4fea071493fb606c3069d489f0da5fa41a91558c23b3c74d0` (4) |
| `ExtDerivableNoSubst.get_congr` | definition (constructor) | none | `04583efa67ae0a67975669fb00dd56f0df468f1fc51eaaf817dd004e57c54dd5` | `89ff33b9a436895e6089d64ce16e247fdcd119a1237ff74f2861b8533afe536e` (28) |
| `GetGet` | definition | none | `3751f09ad673760fb5ca368c81af68ae30c2856e86c0ca6747de0a39830bc47d` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `GetGetVia` | definition | none | `1ae9865ae9d24346b778db3d478c568574a4952a192d369d45ce529219359326` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `GetPut` | definition | none | `3751f09ad673760fb5ca368c81af68ae30c2856e86c0ca6747de0a39830bc47d` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `GetPutVia` | definition | none | `1ae9865ae9d24346b778db3d478c568574a4952a192d369d45ce529219359326` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `IsHom` | definition | none | `1499c616b5b5ae4c10e5dca79b2dea7793ef54d8d1d6303691e30462493210c4` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `Law` | definition | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Law.Holds` | definition | none | `8dce651e65397497d0c6d9170b335c4ec9ce8240555607f07cd0d528077dc0c4` | `19338f84aed1450918fb461c96c5a0543630802156ae8d37c6af03021dd9d86e` (7) |
| `LawSet` | definition | none | `b4611575b2b62eb57ff8b514cf96bf01666158b035ac2fcc89065136260d1e05` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Lawful` | definition | none | `3751f09ad673760fb5ca368c81af68ae30c2856e86c0ca6747de0a39830bc47d` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `Model` | definition | none | `d4856b8e9efb289ec87c088cd04eae3c6d7968f7567bd6cacfe23d681773953b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Model.fromObs` | definition | none | `7a1f17c98fe9ed96cffa54cb0a55e858a960c3fb5339a678f540ca1793d58d5b` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `Model.interp` | definition | none | `ecdd06a0923aee6af595e3f10fee55a5e0c965e0dbaeaae3313a4793ef25236a` | `a9687f431806c60351bf86ce03907c494c804f6cc9ab3807893a304085e2c66f` (6) |
| `ObsEq` | definition | none | `4d8ba7af8446da54f7f6087729afc54632c5603a9e2103e1e1a004c0802c7ea6` | `72ce3d133810d0a4fea071493fb606c3069d489f0da5fa41a91558c23b3c74d0` (4) |
| `Prog` | definition | none | `f55b335e889a1a8947e2d48e605428bd8dd9e06ee11bbec38c787d5a186de3c4` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `Prog.bind` | definition | none | `d66d0598728535f5dee688a1dea29f014818660f0ffddd59329b02c5ca91c015` | `72ce3d133810d0a4fea071493fb606c3069d489f0da5fa41a91558c23b3c74d0` (4) |
| `Prog.get` | definition (constructor) | none | `965f0e433c289b0e8a72afa92a228e563f81c5566ee4e0b81bbff01f330d7fd1` | `72ce3d133810d0a4fea071493fb606c3069d489f0da5fa41a91558c23b3c74d0` (4) |
| `Prog.put` | definition (constructor) | none | `29ba3559683ec28464a7bf01de05f976270a702364019a774b50068b3bfa4c13` | `72ce3d133810d0a4fea071493fb606c3069d489f0da5fa41a91558c23b3c74d0` (4) |
| `Prog.ret` | definition (constructor) | none | `25870e1fc807b7299dbe04d26931e587890facb599a472d9580b6ad97ea6dbd3` | `72ce3d133810d0a4fea071493fb606c3069d489f0da5fa41a91558c23b3c74d0` (4) |
| `PutGet` | definition | none | `3751f09ad673760fb5ca368c81af68ae30c2856e86c0ca6747de0a39830bc47d` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `PutGetVia` | definition | none | `1ae9865ae9d24346b778db3d478c568574a4952a192d369d45ce529219359326` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `PutPut` | definition | none | `3751f09ad673760fb5ca368c81af68ae30c2856e86c0ca6747de0a39830bc47d` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `PutPutVia` | definition | none | `1ae9865ae9d24346b778db3d478c568574a4952a192d369d45ce529219359326` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `SatisfiesAll` | definition | none | `1055f9ba0773b344f33fd71b10cc9eea0aef48b46df5bdbbdc1aada0158ae345` | `e85ba3ddd1907fad4df6f4215c86a33e07a6e8d0c4e22387e3d5a197c55d6575` (8) |
| `allLaws` | definition | none | `9514d0446c99a40fe4097bfb547e3f953aa29ee8f5d1cbc26ca195b703de5b4f` | `1b322cc6ca87a8a415c41aa5d7580eefb8ce720a2687239806ce3b908d5ff080` (6) |
| `canon` | definition | none | `652f7ac8e24e070475e58962efcb8ebe25610d9e9fd34164988d1f65b68a1590` | `72ce3d133810d0a4fea071493fb606c3069d489f0da5fa41a91558c23b3c74d0` (4) |
| `canon_eq_tight` | tightness counterexample | none | `fd57b88b3edb096a81215a16bfd8dadc1233dee4584d0bcd7372bdcc7a9108db` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `changeLog` | definition | none | `c1d165dbf6cd07f6003f39a15338d71017484a20624ec437add0ded90cbb1ef2` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `changeLog_getGet` | auxiliary lemma | none | `4c16aefa05b826401e3bbc8b1b92c7a2a3b9729a0f50bd8bf10faae820665b3e` | `d8c40e38fbc38b33d3bc3cce2f60c82e19e827af1c1dc06ad32b5fe60296c7c4` (5) |
| `changeLog_getPut` | auxiliary lemma | `Quot.sound`, `propext` | `f475d01e8ee241bedd83c6a2a74bf7f82c7cd48a630d4ddea21c387f66aef32a` | `a188304e295e124cecb7ca41a861e1a10097436d21eca4af3a9c17d6bc38062b` (6) |
| `changeLog_not_putPut` | auxiliary lemma | none | `09937c7ad4662921462d9419c2b11de49715afc6ea216fe3aa822812dd3135bb` | `6370ecd9471554bb0856f8cbfe15efe608305d1c2ab8c8d0e54aa46b01666bb6` (5) |
| `changeLog_putGet` | auxiliary lemma | none | `debe8324eabe9780d86756956f4419e703a5e7745228e01f73f27123059a7c0d` | `866d0213a51832ee7a1882ad894f41c6f9696954f2726e843fc48f878acb7f7f` (6) |
| `counterRet` | definition | none | `503814a18e3f12ec2687ac479af5f35259077e900295f3ea74bdf05ff7e18374` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `coupledHidden` | definition | none | `5b7df8af182aad93b145a63d122f46da7201e5dd23d7f9d21e0d54ccdc8cd438` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `coupledHidden_lawful` | auxiliary lemma | `Quot.sound` | `2354d297b8d7c589faea8831698c9cd5e10dd623a14a0cb01faad74e797134e3` | `a1d96ff5546dc24c320591670bb83788309a42285afb262b9693037ee7d02207` (10) |
| `coupledHidden_lawful_changes_hidden` | auxiliary lemma | `Quot.sound` | `927e3dc21b9cf5602cae06c6f11a4934a48e72f8419fdf327a76eb0b75dd01d8` | `adcd5824566c385aad2b3600011c0d706bcc577b5ee36f2cc09006767c5bf8da` (23) |
| `dirtyBit` | definition | none | `48ee5d1e01241107a82d3842dd2560f7bf4d28ac75963696370bf378d45310df` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `dirtyBit_getGet` | auxiliary lemma | none | `ba50adf11264e9311d7e38d0510230bcb7e4cd9fe90df84021faa15c0663da8b` | `3bda59695cee82db5851c3527e84239ff70d05dbd24498d6353f86e3e808ac0a` (5) |
| `dirtyBit_not_getPut` | auxiliary lemma | none | `f5e7823ef10cf0b4d2afc4012c3832d66bfcd720c20d166859a56d1ec9072a1b` | `6ff22d2e28dfafba507ccc039ccf79c3c774f7b298a6c262f1f41b6ca742a1c3` (6) |
| `dirtyBit_putGet` | auxiliary lemma | none | `21cbfb713c7e51c9f85dd365dae1f2d7f8fcd4de2cf129b27c8e55f93688189c` | `3e2e868b9f6d7fc74aa8ae4ced4b096b91fe491575bc2089773f4a5a829efb30` (6) |
| `dirtyBit_putPut` | auxiliary lemma | none | `a744d9cc346a2278a358dd061a13d42592c3c756174215a14623ae49d4c2bed1` | `01cd2aba1663e6e8ff1d843b730038b0114ef9818f543a1b573983fe57e0fa19` (5) |
| `dropLog` | definition | none | `a5546c24ab62e4c9ec356113d65c9172c0a2cce5a775af09fe783fbdda18522b` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `empty_carrier_breaks_forall_interp_iff` | tightness counterexample | none | `fe66b9bf6ed59b4910e0a70ecfb559ee1fe20e2272dff8d533b451c66f486ad8` | `d54c143298db0394a7b1ad2f6465db60f39fb6872b5089af965166ecd82065b7` (23) |
| `empty_cell_all_derivable` | auxiliary lemma | `Quot.sound` | `672307a3ac95b620958d78490ef7b48a0240dd7d779e7a6ad309de210e4cd014` | `0d6cfc62d7f2b33fda9d5f2a2bb98e111ccda5f6e51ebeeeed0bdd62a98a79ca` (21) |
| `empty_cell_getPut_not_nontrivial` | auxiliary lemma | `Quot.sound` | `3e84ddcce43ede404547e0399a39e0d89a42cc46381ecd074e69c263e8005b04` | `800ac3d416be923462afdfade50b8922d3f7e5dbf4c0e83417419431afaf2bb6` (5) |
| `empty_cell_lawful_of_getPut` | auxiliary lemma | `Quot.sound` | `019eaedd9d902237e69f4394219afad13301067c50284d7e9d5424a293ec551c` | `b5a93d9e4bdf16d81db550b4b3ed79012345ac03c27b5069d1f3d27ed596ee0a` (9) |
| `extDerivableNoSubst_not_total` | positive control | `Quot.sound` | `23083d01a45361615f7e3c31fa566f96ba3729d18c030486b9e6765e6a6a7913` | `89ff33b9a436895e6089d64ce16e247fdcd119a1237ff74f2861b8533afe536e` (28) |
| `extDerivable_tight` | tightness counterexample / positive control | `Quot.sound` | `d8b5ae210598353d573fab0193dbd545de973ef583d0f4b9b64653cdf0cd3ed2` | `e07d87b3b73643f8612089e54a0076009a8bce7a6cd5f07d0a0aa7246d94fe03` (36) |
| `faultingCounter` | definition | none | `6d39cfe3b1e5a5a09776b55e8e3b517718e70b3ae56bb0d78bb1a4a16ba482cf` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `faultingCounter_not_getGet` | auxiliary lemma | none | `c8cbfbea6ac63ad12af095b61969432df3cbdd30eb85e06271bb5e29271c8006` | `fbcdd4b0604d0ef9bedd10a84336009bd95cd85ee375c9734d07097a957cac76` (5) |
| `faultingCounter_not_getPut` | auxiliary lemma | none | `d5f39e9e4840bcc38f395be40223261d51eaeeff292136ce6a52b3be6087bb7a` | `6b213098e36f7b808522075986a600bbe10d29c454982d3cf235eab2c3eab66a` (6) |
| `faultingCounter_putGet` | auxiliary lemma | none | `309387162a0238f1f1d4581eee9ac2ddb2c783ae799fa6706acb0a8dd08be6f7` | `0492388051d0002b92e3eebaa00476c1483803d090de7cd2dc11f53979f4d0c8` (6) |
| `faultingCounter_putPut` | auxiliary lemma | none | `e43e0eb153f18a7ac7479af79edb190c681c636c0bbc00fd55a22337e98c434c` | `89e9f63428fbe83ceec924392b3aee73d9071956dbf9e5230a68cc6fcff4abc8` (5) |
| `faultingRet` | definition | none | `c0f23b5866fe6c7b21e754846b514bde277cca867085ba2664303d402937eace` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `forall_interp_tight_getPut` | tightness counterexample | none | `3e10a999d9a4c58cc0ec644fedf0e7d9dc4672532fac97d53e5e1b3be801c9ff` | `1e5b06cb94b455ddd62924589926c518b60c7447989c3d11d196d44816053294` (25) |
| `forall_interp_tight_nontrivial` | tightness counterexample | none | `2082e5d4c9bf6c3b4b95bda07922b7b14fb7dc6039d6e0792e8895848e578a4c` | `76b6ccb71c8b332e13c7da8b02f39926464e042884e6870dec07583dfa836eaf` (24) |
| `forall_interp_tight_putGet` | tightness counterexample | none | `0c46dac287ce18ec9a213f2b8bf5909263ed32c773961fb3db49e8b3a449c770` | `25159abd4ca44c2c4cb232757d930eeded1a23a015007615f9f2a5bae5a24071` (25) |
| `forall_interp_tight_putPut` | tightness counterexample | `Quot.sound`, `propext` | `45516c2001b6be4921d1bbd2fda10d8e1963a29249d2a1647702e7edd8e0e78c` | `bb01dc022c5965593f8c41ae431431237ea1f0e86b7dbc8a498d12210860f600` (25) |
| `fromObs_not_surjective_inertHidden` | auxiliary lemma | `propext` | `22dcfcbb996f3f221a589469639878fb27cc539fbf5983e14e8d1e651721d14a` | `5dedc6a43de02a8c8636205e0b5570e78f6faba2974deae0382b092fb8830370` (12) |
| `fromObs_range_eq_interp_range` | auxiliary lemma | `Quot.sound`, `propext` | `865ec2cb0b2a348759f2124baa04e2e6a4774787152fefd5948cb533e7e935bf` | `be7b846b1917d1feeba8a47a619e594fdc6561ddd0b489a7f670577b4fca962e` (20) |
| `fromObs_tight_getPut` | tightness counterexample | none | `c72dda0324c1ad1c2aa4d0c8adac91d17a9ed59519d8d81744706f5aaa0cb5b4` | `a8e559ff08f218419adb40be3e736a106464467d9f1944b6c7f1f55079278511` (12) |
| `fromObs_tight_putGet` | tightness counterexample | none | `1ea898699c2fde15482ab923089b01ed993703cad21cd197461deedc11c944f8` | `44a377875c1c80da6a5301ce0be96e8ef12cbd353230348fc6e0bf78c31f0366` (11) |
| `fromObs_tight_putPut` | tightness counterexample | `Quot.sound`, `propext` | `26ea6c63a9237eccc3b9457a40b7ee559ffc7c92430d2b35be9f515651f73048` | `353a1972939aa6e4b248d6cb462525f442520930f6709ceedf2d7bd9c7d9ec78` (12) |
| `fstViaModel` | definition | none | `265ce2bf68298eb53a226988d7604bcfecc5e6801c6877f4e400fc6c41bdda2f` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `getGetVia_not_entailed_by_getPutVia_putGetVia` | auxiliary lemma | `Quot.sound` | `cffae700f69bc5086b75a771cbc6b22752e5a0fb346cbf08eb3f71d148715484` | `5feee90a6b27d0b7bca23aa3da83d037bdf24db3c03bac49af0b2ed2f596917e` (8) |
| `getGet_not_derivable_from_getPut_putPut` | auxiliary lemma | `Quot.sound` | `bc603e411492ee474985cc70bcd317f2747bbe1cd26ecc73e879b9c8c40f6e1b` | `f110c0bb7b7bef22b9517db2e9e9dfa23e3db8ab766d14342f11cd0426f35f3a` (29) |
| `getGet_not_derivable_from_putGet_putPut` | auxiliary lemma | `Quot.sound` | `fcb07c5f906e5e059691e534151a1da88a1b51023ba49f37a9f655ae216c35fd` | `f110c0bb7b7bef22b9517db2e9e9dfa23e3db8ab766d14342f11cd0426f35f3a` (29) |
| `getGet_of_tight_getPut` | tightness counterexample | none | `fb2220ee92de3db6f888294b1e929f2ac0222bb05770b914225d454341a61630` | `851f399f2a9b92d1cd2c50bd5cf27ec3785723b69a3af1089ae44dda56c1332b` (7) |
| `getGet_of_tight_putGet` | tightness counterexample | none | `150d1d7ca3d3d3be660f16332f33781ab6b9091e3b8b47c223280706454d265f` | `403f3321166a7cbe7990b2c8fdad3a579bb78eb2f1c80423158a9ff3a85b0954` (7) |
| `getPut_putGet_putPut_iff_exists_isHom` | auxiliary lemma | `Quot.sound`, `propext` | `8c171244bea20cc50328ffbb90201d6e7f89ddae54445eb19b2c18e3aa34e65c` | `ab63185e56ca159da9b5116301e5bd55d2403945f4e3e287d8f62781cd1f92dd` (10) |
| `inertHidden` | definition | none | `de3a9cce36b38a441a61b1d0aaac66e836b13933fef33eeef3946eab19417424` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `inertHidden_lawful` | auxiliary lemma | none | `d18bac58f4d0560c2e7d6e47bc03a9a7e404c705e822e68a6f78c47d91b9b227` | `6914fee44c1f1e5fba098f91eef6ad4d0673fd0f845fc2675e01024395ed412b` (10) |
| `inertHidden_pairFlipRet_changes_hidden` | auxiliary lemma | none | `2e838797f4ad5c2f860b958901069ff22642b00610d2550ee0a63226ec79444a` | `268393f8c08866636f42975dbd682b43fc9bab7e6deb0bea418e7dfc3347ee4f` (23) |
| `intended` | definition | none | `4d52e5c1658769dc3715e91ae7e08cd1d670860d4c7293aaedd6b2bb19e98064` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `intendedRet` | definition | none | `fcbdc9844859a026370d3b3e8c524ed2aba26425441e5d4c38c4491a278f3d18` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `intended_lawful` | auxiliary lemma | none | `fdf475e3fdeb51d184575be93bd5a2ea877ee6d644f8cc6e92fa1128e337be4b` | `64562a2365ef516845ef91ac525fb552d68ed3705955441b0b299a0c13f1d6c0` (10) |
| `intended_leafLog_lawful_and_logs` | auxiliary lemma | none | `de46e2b46efdadb9c3e18bc6a3e4c954022243372d187a28069934741fd010a4` | `828adb6db0c4ce865a4dba2af745acd16d05d03c8f6c5cf96595cbd931ed002f` (22) |
| `interp_eq_tight_obsEq` | tightness counterexample | none | `5d218626c3f0763ef8c275349ded941a9ddae35ac806a0ad6f73d4f2cbd9ec57` | `139eca32164c30212288fd9bb4f0429d4f8bb4fccfd8337ed4c013278ba6bcab` (21) |
| `interp_factor_tight_getPut` | tightness counterexample | none | `d61466151f83ba4d6ada1a6949692e24f1ccc26608f93d3cf9cdf09377f8ee95` | `66a961f8fb3ebf6a266b40d26038115e39a9a3c576fa3f1d34a3c18be6880166` (27) |
| `interp_factor_tight_putGet` | tightness counterexample | none | `935c6a6deaa5234823fb6e5c7d02363e7e7ba4f9fb52d1364f46a6dbc39d8be7` | `743d26dd4f9edbc0c39d02fff301073209cdf90e38ad43e99280137cf858c76a` (27) |
| `interp_factor_tight_putPut` | tightness counterexample | `Quot.sound`, `propext` | `4f2435646f1d6a0cdd20d98e9962bdb59221385f5bdbc9a261050dfa8f7ddab1` | `270b19f919b732739ee62e6a9f3f71e4657a518169cb2bb95a6d01827ab9ad18` (27) |
| `isHom_eq_fromObs` | auxiliary lemma | `Quot.sound`, `propext` | `57e39ecde24fa2c3f67841436dd2a334805173fa23e2ad64b9e7b7bbac96adb2` | `6af9c583f7b2938b848101b58b86395b82c2e5b40ff2a2209e63668e552932c8` (8) |
| `isHom_id_surjective` | auxiliary lemma | none | `b886321dd609b80cd807329bc0a0afd11112f541f0d7ddc65da8ac15b483c2e6` | `09a19163c2574f43983055c4c556743105082052ee80900305a0bde317aee120` (7) |
| `lawsExcept` | definition | none | `c7e40dad2b7503797952e2d68586c2c0ed33e9204be6e3f1c9acd00c96a11c52` | `1b322cc6ca87a8a415c41aa5d7580eefb8ce720a2687239806ce3b908d5ff080` (6) |
| `laws_via_const_hold` | auxiliary lemma | none | `ffca24cc7f8fe9e29595c311eff9cbfc72ba671cf394e3ac39884cee49e92c90` | `2a1f8194da7fe8aa3075690fadb695302f7c4cf27dca49c32402e2cba9a32c82` (8) |
| `logRet` | definition | none | `cb0bcd98493986c2029d609f6be4adfce79db02ea6947632b98ba2b8d9d29a42` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `nf` | definition | none | `763b92dc56f2618fcc5e2d4589bdfc0bfed3ae9344ed8d3c874d747b4768aaff` | `72ce3d133810d0a4fea071493fb606c3069d489f0da5fa41a91558c23b3c74d0` (4) |
| `nv_canon_eq_of_derivable` | non-vacuity witness | none | `4341791dade0a49b65c09b3f7d5597ee18500005a33b2bc9d81677763707ed72` | `7e1e908b225eaff49f243d1baa2a18ad93c448c8e2f675408d34634dedbe3570` (22) |
| `nv_derivable_lawsExcept_getGet_iff` | non-vacuity witness | `Quot.sound` | `b7cfc007fccf44166e627e5c462b4be853bbb32cead061de9ebfa74c0bc1751f` | `2da74f5396ce93a844c75ed4f94bde28a12ab43138a7f7eae046687bff4dd2f9` (21) |
| `nv_derivable_nf` | non-vacuity witness | none | `b3012fa661a40af1771e91d86cfeab04dfc2e2d00175af7bbffcb7844473d011` | `fe2eee169f96073526c7d1b5b4427cadc4186c24c0b14c66a52849136042f7fa` (7) |
| `nv_entailsBool_iff` | non-vacuity witness | `Classical.choice`, `Quot.sound`, `propext` | `e0e6b823ae609150825668632d21f853c8dc612b60692975e66677fa69c3809d` | `3e1df37bcef14ba8efebc980515f100d4643a9a705e4c80d7d0e36b8bc55c3d4` (21) |
| `nv_extDerivable_total` | non-vacuity witness | `Quot.sound` | `bd4019ad3672c1376bae63a5e84e537963bee88bdec62c6859f5f95e9ad766db` | `0d6cfc62d7f2b33fda9d5f2a2bb98e111ccda5f6e51ebeeeed0bdd62a98a79ca` (21) |
| `nv_forall_interp_eq_iff_obsEq` | non-vacuity witness | none | `854fd26f3156cfe80f76309ef679c2c5a591bc9a696d1bd537aa606c4c140a8c` | `a3af1e32a6f1e09ec372de64dc831ab23ebf6ba6d0d2126e392ed191708da0ff` (8) |
| `nv_fromObs_isHom` | non-vacuity witness | none | `d7eeb156ab69c75471b3f7850e34db948e57b62ea840efe55e8d4e08a6af0e99` | `a3af1e32a6f1e09ec372de64dc831ab23ebf6ba6d0d2126e392ed191708da0ff` (8) |
| `nv_getGet_of_getPut_of_putGet` | non-vacuity witness | none | `89c200b24e97ab542aeebdd8765eea81ed2b08c3f4bb323803e1cc8530e71d73` | `3b6b2ab69f298b6321288f400e8243d87b60163e1785c6f67a2d130cd54d2591` (7) |
| `nv_getPut_putGet_putPut_iff_exists_surjective_isHom` | non-vacuity witness | `Quot.sound`, `propext` | `98e580c6c21ed95800cff1d35db68aea78bf70a55e63981b32f487d73527f02e` | `c180182e01f5ae9b85498a939318a178595a9ba7351f59b53883b83a84c7ed1d` (9) |
| `nv_inertHidden_interp_eq` | non-vacuity witness | none | `f38c99c9e1147eb68f85ca961f8b86e8a1cebcb4a0ab101eac967657fb9ec578` | `0f07c917a97cc16a821093928791dd661f2cc9c666c6ae81f853b23d72cc236b` (26) |
| `nv_interp_eq_of_obsEq` | non-vacuity witness | none | `eaa6987ec42bd5225eb8a93fd94d92eda93500c710fdb63531f19f398bdf606e` | `cc0e00677572457a59bf10bbfde920499b5db47968b052131652267c5aeb6477` (21) |
| `nv_interp_factor` | non-vacuity witness | none | `e185979d379004c587cc5b3214e6f64461b7468b770867bbe55fab8f52c2597c` | `2b518d5e8e669c25a9fa8c81d4391885f62615cd2a57bbd425d659ec0ff69607` (8) |
| `pairFlipRet` | definition | none | `c26d350b942a64cf6811a505f569e81e765d3d81933376df0d5d33f487b94fa8` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `pairRet` | definition | none | `014466812d2f3884fa8a7e72a3e78b6d74ead0e8488395ac7d11eedd8876c920` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `readCounter` | definition | none | `e8e3ddd5794eca37e7e28a400bc32cceeb8a95eb713227f16515f01d22c8492a` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `readCounter_lawful_of_empty_cell` | auxiliary lemma | `Quot.sound` | `87a14e56e3e68ca6e13b8cfd2da3c33ab0f06612b5955ce64cb890fd6d49a7e6` | `7230019009df47164f847f0abdb144db9c16b6403d682a6dcac1d8b11ac3d93e` (10) |
| `readCounter_lawful_of_empty_result` | auxiliary lemma | `Quot.sound` | `771197d823079b09725e896c110e082fb66b33abd6cd28df64a5680bbbcc3344` | `7230019009df47164f847f0abdb144db9c16b6403d682a6dcac1d8b11ac3d93e` (10) |
| `readCounter_not_getGet` | auxiliary lemma | none | `8830ae71ce235dfa7112da8c65bf5de76d3a317956bcdbe144a2348c6750c872` | `149768eab585904b3d113f298abce03c9beca2000465a6559006544489249ebc` (5) |
| `readCounter_not_getPut` | auxiliary lemma | none | `7aac9f1a2e874ff450ea57a9ee506ef6001dd3155465462ff89fea8f2cf23dac` | `f331b8bf2a22ba253ba7dd2595ac2be98eee324646e8b7afa86c90c1939531f8` (6) |
| `readCounter_not_putGet` | auxiliary lemma | none | `ae5cfacd342e22f95c797f54693f9338ee5942cf6e87b8ab9e791a1636474aab` | `e25a2c514261d132d1e0b84ba7c54c5edc0eb7bcf1e4c40cebc11921b592dfba` (6) |
| `readCounter_putPut` | auxiliary lemma | none | `b38b810950bbdd8ccdde101d3e57c3f59c3e0d9d16515983e7e0c42b73fce2fc` | `ae0b55091a16ec0b3a590e71abc70253c68dd7c07f1105d0f495347d46157fcb` (5) |
| `readToClear` | definition | none | `062b7ec5bd68eefe9671a492fd103f5df013465f378c2ea4fdaa38cf38af07e2` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `readToClear_getPut` | auxiliary lemma | none | `ba6a4d5aeffab561a6b2dbfa202a92d5a3b51e3b5d82b91a6f0a3e2c923990ca` | `f10efff11300bc02472ef8b269eef67c6faf81e06bb8a00e4194474e4c59aa14` (6) |
| `readToClear_not_getGet` | auxiliary lemma | none | `1a8a71584c7967940111e744a94a61d6d247086a748cd2653372754cd2543ba6` | `a90e19d51c5f94658fad55cc4bed8158aeab258eb0607d857176cd474fb33fda` (5) |
| `readToClear_not_putGet` | auxiliary lemma | none | `8347d591dae38d340f672cbd94d729548c7f175b84a623f7198bc94ff40f41bc` | `9c309ce0123c2b7eea6f7c7a5cdf6fdbe5d13a6350331545d6dd2bffc60569fc` (6) |
| `readToClear_putPut` | auxiliary lemma | none | `7c71dc1d9fbba45890b99253d84cf5b683a6ec048019e122f5ae724221f5d3e7` | `5666c6487b9de5b22ab65528c677bdf7bf94a04bd90df0764c27ffce427d84f4` (5) |
| `run` | definition | none | `592624222343c9ebf1714a38cd9aa15a56a46f889a7c685249b4ce6e9b521fc4` | `72ce3d133810d0a4fea071493fb606c3069d489f0da5fa41a91558c23b3c74d0` (4) |
| `unitModel` | definition | none | `e9609b28822a9191464d2dce427479787ffeb173e67a02734f022e26dfb9a573` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `unitModel_lawful` | auxiliary lemma | none | `ea79c92fbe6f159b73d422e1919fa88d832dfe9a9fe31706425573b5df090e85` | `b4f346962be273f952f2ee739cbd7603403b578c773e5ec26029813689ba05ae` (10) |
| `unit_cell_lawful_of_getPut_putPut` | auxiliary lemma | `Quot.sound`, `propext` | `006ec79cfa29c50cef6bad04400876542a4f1ea6e2c907618f905a5f32d367d2` | `b5a93d9e4bdf16d81db550b4b3ed79012345ac03c27b5069d1f3d27ed596ee0a` (9) |
| `unit_cell_putPut_of_getPut_putGet` | auxiliary lemma | none | `926fe81be6b77ab52ae31da6dcd27ff784a3337c09bc472cfe489849a2e71157` | `cfc9c0ace7dd94b4ad34debe16e916a207b3da890dd1d059a6c797ca3bddec77` (7) |
| `unit_cell_unit_result_all_derivable` | auxiliary lemma | `Quot.sound` | `4ede4ee46669c68c2d3c89dc79218e12f9f1453cfc30d96d1c67eb42e6634381` | `0d6cfc62d7f2b33fda9d5f2a2bb98e111ccda5f6e51ebeeeed0bdd62a98a79ca` (21) |
| `valueOnly` | definition | none | `7bc0009b1d220ea520539776a2cb2d7e0018ea2bd3b97d42a46b2a6ca78b02ab` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `valueOnlyRet` | definition | none | `7a37e0dc3b77f8c84110a42f3877f8fdcf8d394caf44c831758e2df8e449e43e` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` (0) |
| `valueOnly_lawful` | auxiliary lemma | none | `1abeb5f70c52704585237926b72e772048a9b2928bb81c00d84646deabb50ef1` | `0560d60a7e8fa3ef7c2899a4737a6a1697fbc43e659b746cb1b25099891380aa` (10) |
| `valueOnly_separates_other_valuation_and_substitution` | auxiliary lemma | none | `4aa2709338fb13314e6afa6b02f27d31538d423ea0c0f1ec204f1cd5e2abc7ee` | `9494c697eeb36bc3c4ca01c28b5aab141773efb738c1e7fcfc790a95d3be4401` (21) |
| `writeLog` | definition | none | `59541ee5279040db7d5dbc12f765a0b17109af20c52f1f1238bd7aebdda7253f` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `writeLog_getGet` | auxiliary lemma | none | `25e841595d9a196fcd860376dff75040cc613148a2cc9ff9864f0bd7858c5bd7` | `81ab3cde1255a911c30a3f8aefe1a6d59d41fc8238d1ea05a2a88064b4812716` (5) |
| `writeLog_lawful_of_empty_cell` | auxiliary lemma | `Quot.sound` | `49c5cf0ed3caee01947b4e4b9bfab3e4a75265761492b4b86e6d4a7b0b466489` | `92727d1a536e9e87f718ddfbb129a85196354c56452f1bae2badedd04887f6c5` (10) |
| `writeLog_lawful_of_empty_result` | auxiliary lemma | `Quot.sound` | `0be11a63cd1e604226e8e1591780daf3423c02fba221997f8cd9defe476bffa8` | `92727d1a536e9e87f718ddfbb129a85196354c56452f1bae2badedd04887f6c5` (10) |
| `writeLog_laws_via_dropLog` | auxiliary lemma | none | `47d52956585fabf1da6608681d1f8e20c6d58c946b7239c6a3b57723cb140da5` | `cd77d1d8bda951253a12d6807753387e1b13712277bb51ff42a0df17b5ba3125` (10) |
| `writeLog_not_getPut` | auxiliary lemma | none | `814de40c6d47c885f5bb4e8e0e1804d27945f789b96780af2a8a1e12647785a8` | `48beb538d58221bb9f76b441fdcc5ba0719cd5166a9be83830e5cf8dca3f985c` (6) |
| `writeLog_not_putPut` | auxiliary lemma | none | `1691006599bdc0a9a1cb4825a1f713bb68bd79c2d7f16242e13f196e4af12034` | `b2e8b320adace7587aa2a2736019295dc72b3c1ea3bae7f55df7f6913a09c701` (5) |
| `writeLog_putGet` | auxiliary lemma | none | `e1da23b8f557e3b73c4065e8907e5d02eb469ad400938fdf91627c8c6dbfc24f` | `bac82ad34d67133035c1162f0463447c91059b373f728b433dfe2e6ce6eb1dbb` (6) |
| `writesIgnored` | definition | none | `4d52e5c1658769dc3715e91ae7e08cd1d670860d4c7293aaedd6b2bb19e98064` | `74fe9deb0c688f5cacead58a20427ca5ac5387de2e2ca319a45dd2ba4d7f6253` (2) |
| `writesIgnored_getGet` | auxiliary lemma | none | `9649988aa2ca6d30fd9d6192e57be2c55e7d342419b8c9190f4635743211b35e` | `ec3ebf9dbdbc54b20e026535fa745f05e5acd79e9c81de702b5f19cfb0d19257` (5) |
| `writesIgnored_getPut` | auxiliary lemma | none | `4c262ed9c432875814e68bd8f670b6169a1b5f865fd9450b8d3e4dcdf5d3cfa6` | `627dd844a58cfd130ce281d99d0d160ab150ccf2544ceb8cf836e6c030690bd5` (6) |
| `writesIgnored_not_putGet` | auxiliary lemma | none | `63ccf6d8056ad1cbcd38bf538c744c1e52a655a86bba55ef00dc585621545393` | `7bbbf660e8fe663bef5ac7a5e0a30c934bb13f27cb6d8f13e4f1196e79356991` (6) |
| `writesIgnored_putPut` | auxiliary lemma | none | `82253019b8c618d636e23aaa0cc4a72fefbfa47157cb0560f4784b16b4ec2bc2` | `60bf2d6e9e8ffdfab6d07773f84367593c287fcab4627782272aebd20c29719d` (5) |

### Primary sources

Exact records for the prior art cited in the cards, with what each source states; the extent to which each was consulted is recorded in its entry ("observed in the source; not type-checked here", "bibliographic record checked; content not consulted", "as attested by").

- [PP02] G. D. Plotkin and J. Power, 'Notions of Computation Determine Monads', FoSSaCS 2002, Lecture Notes in Computer Science, Springer, pp. 342-356, DOI 10.1007/3-540-45931-6_24. Section 3: seven axiom schemas for global state; for one location, axioms 1-4 are get–put, get–get (stated as an axiom), put–put, put–get; Theorem 1: the category of models is monadic with monad (S ⊗ -)^S, which is (S × -)^S over sets (finite set of locations, countable set of values); the paper states without proof: 'It can be shown that this axiom system is Hilbert-Post complete, meaning that it has no equationally consistent extensions'.
- [PP03] G. D. Plotkin and J. Power, 'Algebraic Operations and Generic Effects', Applied Categorical Structures 11(1):69-94, 2003, DOI 10.1023/A:1023064908962. Global state via lookup/update operations and the corresponding generic effects.
- [GH11] J. Gibbons and R. Hinze, 'Just do it: simple monadic equational reasoning', ICFP 2011, ACM, pp. 2-14, DOI 10.1145/2034773.2034777. Section 6 states the four MonadState axioms put–put, put–get, get–put (get >>= put = skip) and get–get.
- [KYW24] D. O. Kidney, Z. Yang and N. Wu, 'Algebraic Effects Meet Hoare Logic in Cubical Agda', Proc. ACM Program. Lang. 8 (POPL), Article 56, 2024, DOI 10.1145/3632898. Section 3, Eq. (12): the theory of mutable state with the three laws put–put, put–get, get–put; the text states that get–get 'in fact follows from the equations above'. The authors' public Agda repository (github.com/oisdk/algebraic-free-monads-agda at commit 09f6fa1e9304732acfc72b4f8f2b9a52756361de, file Effects/State.agda) contains a proof of get–get from put–get and get–put (observed in the source; not type-checked here).
- [MLMSWY25] C. Matache, S. Lindley, S. K. Moss, S. Staton, N. Wu and Z. Yang, 'Scoped Effects, Scoped Operations, and Parameterized Algebraic Theories', ACM Trans. Program. Lang. Syst. 47(2), Article 8, 2025, DOI 10.1145/3731678 (earlier preprint, the extended version of the ESOP 2024 paper, as 'Scoped Effects as Parameterized Algebraic Theories', arXiv:2402.03103). Example 2.8: for the state of a single bit, with equations for put–get, put–put and get–put, 'the conspicuously missing equation for a get after a get ... can be derived', followed by a five-step derivation.
- [Hil21] D. Hillerström, 'Foundations for Programming and Implementing Effect Handlers', PhD thesis, The University of Edinburgh, 2021; Edinburgh Research Archive record (dated 2022), DOI 10.7488/era/2122, handle 1842/38868 (author's copy, to which the page numbers below refer: dhil.net/research/papers/thesis.pdf). Section 1.2.2 (pp. 9-10) remarks that get–get is derivable from get–put and put–get; Appendix B ('Get get is redundant', p. 271) gives the derivation.
- [Loc17] A. Lochbihler, 'Effect Polymorphism in Higher-Order Logic (Proof Pearl)', ITP 2017, Lecture Notes in Computer Science, Springer, pp. 389-409, DOI 10.1007/978-3-319-66107-0_25; journal version J. Automated Reasoning 63(2):439-462, 2019, DOI 10.1007/s10817-018-9476-2; Archive of Formal Proofs entry Monomorphic_Monad (2017), isa-afp.org/entries/Monomorphic_Monad.html. The Isabelle locale monad_state uses the same continuation-style signature get : (s ⇒ m) ⇒ m, put : s ⇒ m ⇒ m and assumes put_get, get_get, put_put, get_put and get_const as axioms, together with bind_get and bind_put, which relate get and put to the monad's bind. The locale text was read in the current version of the entry as of 2026-11-21; no immutable identifier for the entry was located, so it is identified by name and URL.
- [PlPr09] G. D. Plotkin and M. Pretnar, 'Handlers of Algebraic Effects', ESOP 2009, Lecture Notes in Computer Science, Springer, pp. 80-94, DOI 10.1007/978-3-642-00590-9_7; journal version 'Handling Algebraic Effects', Logical Methods in Computer Science 9(4:23), 2013, DOI 10.2168/LMCS-9(4:23)2013. Handlers are models of the effect theory, and handling is the homomorphism induced by the universal property of the free model.
- [PS04] J. Power and O. Shkaravska, 'From Comodels to Coalgebras: State and Arrays', Electronic Notes in Theoretical Computer Science 106 (2004), 297-314, DOI 10.1016/j.entcs.2004.02.041. Models and comodels of the theory of state (related background).
- [Met04] F. Métayer, 'State monads and their algebras', arXiv:math/0407251, 2004. Investigates the algebras of state monads in cartesian closed categories (related background).
- [KS55] J. Kalicki and D. Scott, 'Equational completeness of abstract algebras', Indagationes Mathematicae 17 (1955), 650-659 (publisher record: Indagationes Mathematicae (Proceedings) 58, DOI 10.1016/S1385-7258(55)50089-8). Equational completeness in universal algebra (bibliographic record checked; content not consulted).
- [DDR13] J.-G. Dumas, D. Duval and J.-C. Reynaud, 'Patterns for computational effects arising from a monad or a comonad', arXiv:1310.0605, 2013. Section 3.3, Theorem 3.4: 'The theory for state is Hilbert-Post complete', for a single location, in a decorated logic whose axiomatization is not the four plain get/put equations; Appendix A, Proposition A.5: the key proposition, whose proof 'has been checked with the Coq proof assistant'.
- [DDEP13] J.-G. Dumas, D. Duval, B. Ekici and D. Pous, 'Formal verification in Coq of program properties involving the global state effect', arXiv:1310.0794, 2013. The Coq framework for decorated global state; its conclusion reports that the framework was used to check the Hilbert-Post completeness proof of arXiv:1310.0605.
- [DDEPR16] J.-G. Dumas, D. Duval, B. Ekici, D. Pous and J.-C. Reynaud, 'Relative Hilbert-Post Completeness for Exceptions', MACIS 2015 (proceedings published 2016), Lecture Notes in Computer Science, Springer, pp. 596-610, DOI 10.1007/978-3-319-32859-1_51; preprint titled 'Hilbert-Post completeness for the state and the exception effects', arXiv:1503.00948. Introduces relative Hilbert-Post completeness; its abstract describes the application to state as a generalization of Pretnar's work.
- [Pre10] M. Pretnar, 'Logic and handling of algebraic effects', PhD thesis, University of Edinburgh, 2010, http://hdl.handle.net/1842/4611. Hilbert-Post completeness is defined in Definition 2.8 and proved for single-location global state in Proposition 2.40, as attested by arXiv:1310.0605, Section 3.3; the thesis text itself was not consulted.
- [Sta10] S. Staton, 'Completeness for Algebraic Theories of Local State', FoSSaCS 2010, Lecture Notes in Computer Science, Springer, pp. 48-63, DOI 10.1007/978-3-642-12032-9_5. Completeness for local (not global) state; related background.
- [GM00] J. Goguen and G. Malcolm, 'A hidden agenda', Theoretical Computer Science 245(1):55-101, 2000, DOI 10.1016/S0304-3975(99)00275-3. Behavioral satisfaction: an algebra behaviorally satisfies t = t' iff it satisfies c[t] = c[t'] for every observable context c (Definition 5 in the authors' preprint); the ...Via laws of this package compare at top level.

### Source layout

- `lean/Toy/StoreLaws/Defs.lean`: syntax, intended semantics, models, laws, derivability.
- `lean/Toy/StoreLaws/Lemmas.lean`: monad laws of `Prog.bind`, soundness, derived laws, substitution closure, degenerate cells.
- `lean/Toy/StoreLaws/Models.lean` and `lean/Toy/StoreLaws/Profiles.lean`: the concrete models and valuations, and their law profiles.
- `lean/Toy/StoreLaws/Results.lean`: the main results and the supporting lemmas stated next to them.
- `lean/Toy/StoreLaws/Witnesses.lean`: tightness counterexamples, non-vacuity witnesses and positive controls.
- `lean/Toy/StoreLaws/Companions.lean`: companion lemmas on the redundancy of surjectivity in Result 11, subsingleton carriers and empty cells in Result 13, empty types in Results 16 and 17, and an instance of Result 18.
- `lean/Toy/StoreLaws/Examples.lean`: positive and negative examples for every definition.
- `support/revalidate.py`, `support/PrintAxioms.lean`: revalidation (below).

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. From the package directory:

```sh
python3 support/revalidate.py .
```

The script copies the Lean project to a temporary directory (the package is not modified) and checks that (1) `lake build` succeeds; (2) no Lean source contains `sorry`, `admit` or `native_decide`, or declares an `axiom`; (3) no declaration of the library depends on axioms other than `propext`, `Classical.choice` and `Quot.sound` (computed with Lean's `collectAxioms` by an audit program embedded in the script); and (4) for every Lean name referenced by `results.json`, the SHA-256 of the statement (the Lean `repr` of its type) and of its definition closure (types and values of every package constant reachable from the statement; theorem bodies excluded) equals the value recorded in `audit/statements.json`. It prints `REVALIDATED` and exits with status 0 iff all checks pass.

A direct axiom check of the main results, without Python:

```sh
cd lean
lake build
lake env lean ../support/PrintAxioms.lean
```

Each `#print axioms` line must list a subset of `propext`, `Classical.choice` and `Quot.sound` (or report that the declaration depends on no axioms).

To re-check a single card after a change to the sources, compare its quoted line ranges with the source and rerun `python3 support/revalidate.py .`: a changed statement or a changed definition in its closure changes a recorded hash. A passing run establishes what these checks check: the statements as quoted are kernel-checked with standard axioms. It does not re-examine the prior-art records or the modeling bridge.
