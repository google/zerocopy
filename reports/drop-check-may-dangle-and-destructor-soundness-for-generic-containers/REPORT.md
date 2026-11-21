# Drop check, `#[may_dangle]` and destructor soundness for generic containers

## Summary

Lean project: `lean/` (library `ToyDropck`, namespace `Toy.Dropck`), Lean `v4.34.1`, core Lean without Mathlib and without `[[require]]`. Every theorem in the project, including the general results R1, R3, R4c, R7 and R8, is fully proved, with no `sorry`; the axiom audit reports at most `propext` and `Quot.sound`.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*

**Scope.** These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]`, RFCs 769/1238/1327/2094 or the Rust standard library. Model–system relation: none proved. Every connection to Rust is a separate `derived (modeling bridge)` claim, collected under Findings in "Modeling bridges".

* **R1** (theorem). In the toy model, for every implementation table satisfying `GlueVisible`, every drop order and every scope satisfying `ValuesHaveTypes` and `LifetimesInScope`: if the strict checker `acceptsStrict` accepts the scope for that order, then dropping its locals in that order never observes a dead or nonexistent local (`DropSafe`), where a local counts as dead from the moment its own drop begins.
* **R2** (counterexample). In the toy model, for the container scope `pContainer` (`let mut v = Vec::new(); let x = 0; v.push(&x);`) and the single table `mkTbl vecMD` (a `#[may_dangle]` `Vec` whose destructor drops its elements without otherwise using them), with `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `ValuesHaveTypes` and `LifetimesInScope` holding: the drops in reverse declaration order are safe, the strict checker rejects the scope for that order, and the `may_dangle` checker accepts it.
* **R3** (theorem). In the toy model, for every implementation table satisfying `MayDangleHonest`, `OwnsDeclared` and `GlueVisible`, every drop order and every scope satisfying `ValuesHaveTypes` and `LifetimesInScope`: if the `may_dangle` checker `accepts` accepts the scope for that order, then `DropSafe` holds for that order.
* **R4a** (counterexample). In the toy model, for the scope `pOwnedReader` (`Vec<D<&x>>` declared before `x`, `D`'s destructor using `&x`) and the table `mkTbl vecMD`, with `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `ValuesHaveTypes` and `LifetimesInScope` holding: the relaxation `noUseSuffices` (no check on the drop of a `#[may_dangle]` parameter's values) accepts the scope for reverse declaration order, and its drops in that order observe a dead local.
* **R4b** (counterexample). In the toy model, for the scope `pNestedReader` (`Vec<W<D<&x>>>` declared before `x`) and the table `mkTbl vecMD`, with `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `ValuesHaveTypes` and `LifetimesInScope` holding: the relaxation `headNoDrop` ("`T: !Drop`" checked on `T`'s outermost type constructor, with the outlives requirement as fallback) accepts the scope for reverse declaration order, and its drops in that order observe a dead local.
* **R4c** (theorem). In the toy model, for every implementation table satisfying `MayDangleHonest` and `GlueVisible`, every drop order and every scope satisfying `ValuesHaveTypes` and `LifetimesInScope`: if the `deepNoDrop` checker ("`T: !Drop`" checked through the whole type, with the outlives requirement as fallback) accepts the scope for that order, then `DropSafe` holds for that order; `OwnsDeclared` is not assumed.
* **R5** (counterexample). In the toy model, for `pReaderAfter` (`let x = 0; let d = D(&x);`) and the table `mkTbl vecMD`, with `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `ValuesHaveTypes` and `LifetimesInScope` holding: the `may_dangle` checker accepts the scope for reverse declaration order and those drops are safe, while drops in declaration order observe a dead local and the checker given declaration order rejects.
* **R6** (counterexample). In the toy model, for `pEmptyOwnedReader` (an empty `Vec<D<&x>>` declared before `x`) and the table `mkTbl vecMD`, with `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `ValuesHaveTypes` and `LifetimesInScope` holding: the drops in reverse declaration order are safe, but the `may_dangle` checker rejects the scope for that order.
* **R7** (theorem). In the toy model, for every implementation table, drop order and scope, with no other hypotheses: acceptance by `acceptsStrict` implies acceptance under every policy; acceptance under `deepNoDrop` implies acceptance under `ownsRecurse` (`accepts`) and under `headNoDrop`; acceptance under any policy implies acceptance under `noUseSuffices`.
* **R8** (theorem). In the toy model, for every policy, every implementation table satisfying `MayDangleHonest`, `MayDangleDropsNothing` and `GlueVisible`, every drop order and every scope satisfying `ValuesHaveTypes` and `LifetimesInScope`: if the checker under that policy accepts the scope for that order, then `DropSafe` holds for that order.

Each result's non-claims are listed with its card under Findings and collected under Boundaries; they bound what each sentence above may be taken to mean.

## Applicability

**Model fidelity.** A toy model, not a mirror of rustc's data structures. It captures one block scope at the moment it exits: locals `0 … n-1` declared in that order, each holding a value whose references may point at any local (earlier or later, modelling late initialization such as `v.push(&x)` after `let x`); a drop order `ord`; generic container type constructors with exactly one type parameter, no lifetime parameters and optional `Drop` impls; and a type-based, decidable drop checker following the shape of the RFC 1327 rule with RFC 769's ownership recursion (strict outlives for parameters of `Drop` impls; `#[may_dangle]` parameters exempt; recursion into owned element types). The checker compares lifetimes against one fixed drop order, in the style of the scope-based "strictly outlives" formulation of RFCs 769 and 1327, rather than the liveness-based formulation of RFC 2094. Known gaps are listed under Boundaries; "What the one-parameter model can express" under Findings states precisely what the one-parameter restriction implies.

**Subjects and how they relate.** `REPORT.json` lists the Lean 4 toolchain release that checks every proof, and the documentary sources whose descriptions the definitions follow: Rust RFCs 769, 1238, 1327, 1857 and 2094 (rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4), the Rustonomicon chapters 'Drop Check' and 'PhantomData', the rustc-dev-guide chapter 'Drop Check', the Rust Reference chapter 'Destructors', and the RustBelt paper. The model is defined in Lean from these descriptions; none of these sources is formalized, and rustc itself was not examined or executed. The open, unmerged pull request rust-lang/rfcs#3417 (https://github.com/rust-lang/rfcs/pull/3417) is not a subject: it is a proposal that has not been accepted, and it is cited as design discussion (prior art of R3, R4a and R8, the R8 tier note and bridge B3); no definition, result or modeling bridge relies on it as a description of Rust. Model–system relation: none proved (no embedding, abstraction or simulation between the toy model and rustc is established). These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]`, RFCs 769/1238/1327/2094 or the Rust standard library. Each connection to Rust is a separate `derived (modeling bridge)` claim (B1–B7 under Findings).

**Lean.** `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`), core Lean without Mathlib and without `[[require]]` dependencies. Library `ToyDropck` (modules `Basic`, `Checker`, `Examples`, `Lemmas`, `Inclusions`, `Collapse`, `Results`, `Companions`), namespace `Toy.Dropck`; every package-local Lean name in this report is in that namespace.

**Input classes and edge cases.** The general theorems (R1, R3, R4c, R7, R8) quantify over every implementation table (a function from container indices to `DropImpl`), every drop order `ord : List Nat` (including the empty list and lists with repeated or out-of-range indices, which `runDrops` skips) and every scope `p` (including the scope with no locals). Locals, containers and lifetimes are natural-number indices compared by equality and `<`; no result relies on truncated subtraction, floor division or modulo, and there is no fixed-width arithmetic. The counterexample results (R2, R4a, R4b, R5, R6) are single concrete instances.

## Findings

Basis: execution (Lean kernel check) for every Lean statement quoted below; the modeling bridges B1–B7 at the end of this section are derived (modeling bridge). Every statement block is a verbatim quote of the Lean source with its `file:line` range; proofs are elided (`:= …`).

### The model and what each definition captures

#### Syntax (`ToyDropck/Basic.lean`)

```lean
-- lean/ToyDropck/Basic.lean:27-31
inductive Ty where
  | int : Ty
  | ref (j : Nat) : Ty
  | app (c : Nat) (t : Ty) : Ty
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropck/Basic.lean:35-38
inductive Val where
  | int (n : Nat) : Val
  | ref (j : Nat) : Val
  | obj (c : Nat) (elems : List Val) : Val
```

* `Ty`: `int` (plain data, no drop glue); `ref j`, a shared reference whose lifetime is local `j`'s storage (the toy identifies a lifetime with its referent local, records no referent type, and has no lifetime subtyping); `app c t`, container type constructor `c` applied to element type `t`.
* `Val`: integers, references to locals, and container instances `obj c elems`.

```lean
-- lean/ToyDropck/Basic.lean:46-50
structure DropBehavior where
  hasDrop : Bool
  usesT : Bool
  dropsElems : Bool
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropck/Basic.lean:58-61
structure DropDecl where
  mayDangle : Bool
  ownsT : Bool
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropck/Basic.lean:64-67
structure DropImpl where
  beh : DropBehavior
  decl : DropDecl
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropck/Basic.lean:70
abbrev ImplTable := Nat → DropImpl
-- lean/ToyDropck/Basic.lean:73
def behOf (impls : ImplTable) : Nat → DropBehavior := fun c => (impls c).beh
```

* `DropBehavior` is what happens at run time: whether a `Drop` impl exists (`hasDrop`), whether that destructor uses (reads, writes, calls methods on) its `T` elements (`usesT`), and whether dropping the container drops its elements (`dropsElems`). The model gives a destructor no other action on its parameter.
* `DropDecl` is what the checker is told beyond `hasDrop`: `#[may_dangle]` on `T` (`mayDangle`), and dropck-visible ownership of `T` (`ownsT`: a by-value `T` field or `PhantomData<T>`). Keeping behaviour and declarations apart is what lets the honesty conditions below relate them.

#### Runtime semantics

```lean
-- lean/ToyDropck/Basic.lean:75-88
mutual
/-- `observe L v`: using the value `v` (for instance printing it through a trait method). It
recurses through container values to every reference inside `v` and, for a reference `ref j`,
checks that local `j` is live according to `L`; it does not read local `j`'s own value (there is
no second dereference). It is defined (`true`) iff every local so referenced is live. -/
def observe (L : Nat → Bool) : Val → Bool
  | .int _ => true
  | .ref j => L j
  | .obj _ vs => observeAll L vs
/-- `observe` on every element of a list. -/
def observeAll (L : Nat → Bool) : List Val → Bool
  | [] => true
  | v :: vs => observe L v && observeAll L vs
end
```

```lean
-- lean/ToyDropck/Basic.lean:90-106
mutual
/-- `dropVal beh L v`: running the drop of value `v` while the live locals are `L` is defined
(`true`) or reaches undefined behaviour (`false`). References and integers have no drop glue. For
`obj c vs`: first the destructor of `c` runs, observing the elements if it uses them; then, if `c`
drops its elements, each element is dropped in turn. The live set `L` does not change during one
value's drop. -/
def dropVal (beh : Nat → DropBehavior) (L : Nat → Bool) : Val → Bool
  | .int _ => true
  | .ref _ => true
  | .obj c vs =>
    (!((beh c).hasDrop && (beh c).usesT) || observeAll L vs) &&
    (!(beh c).dropsElems || dropAll beh L vs)
/-- `dropVal` on every element of a list, in list order. -/
def dropAll (beh : Nat → DropBehavior) (L : Nat → Bool) : List Val → Bool
  | [] => true
  | v :: vs => dropVal beh L v && dropAll beh L vs
end
```

```lean
-- lean/ToyDropck/Basic.lean:110-111
structure Prog where
  locals : List (Ty × Val)
```

```lean
-- lean/ToyDropck/Basic.lean:114-115
def live (n : Nat) (dead : List Nat) (j : Nat) : Bool :=
  decide (j < n) && !dead.contains j
```

```lean
-- lean/ToyDropck/Basic.lean:122-130
def runDrops (beh : Nat → DropBehavior) (p : Prog) : List Nat → List Nat → Bool
  | [], _ => true
  | k :: ks, dead =>
    if dead.contains k then runDrops beh p ks dead
    else
      match p.locals[k]? with
      | none => runDrops beh p ks dead
      | some (_, v) =>
        dropVal beh (live p.locals.length (k :: dead)) v && runDrops beh p ks (k :: dead)
```

```lean
-- lean/ToyDropck/Basic.lean:136-137
def DropSafe (impls : ImplTable) (ord : List Nat) (p : Prog) : Prop :=
  runDrops (behOf impls) p ord [] = true
```

```lean
-- lean/ToyDropck/Basic.lean:143
def revDeclOrder (n : Nat) : List Nat := (List.range n).reverse
```

```lean
-- lean/ToyDropck/Basic.lean:146
def declOrder (n : Nat) : List Nat := List.range n
```

* `observe L v` is the toy's notion of *using* a value: it recurses through nested containers to every reference inside `v` and checks that the referenced local is live; it does not read that local's own value. Reading a reference to a dead or nonexistent local is undefined behaviour (`false`).
* `dropVal`: the destructor runs first (observing the elements iff `hasDrop && usesT`), then, iff `dropsElems`, the elements are dropped in list order. The live set does not change while one value is dropped.
* `runDrops` / `DropSafe` (the semantic property, "no destructor observes a dead value"): locals are dropped in the order `ord`; a local counts as dead from the moment its own drop begins (`runDrops` drops its value with the local already in the dead set) and stays dead; indices already dead or naming no local are skipped. `DropSafe impls ord p` iff no drop reaches undefined behaviour.
* `revDeclOrder n = [n-1, …, 0]` is Rust's scope-exit order for locals; `declOrder n = [0, …, n-1]`.

Examples (all proved):

```lean
-- lean/ToyDropck/Examples.lean:113
theorem revDeclOrder_three : revDeclOrder 3 = [2, 1, 0] := …
-- lean/ToyDropck/Examples.lean:114
theorem declOrder_three : declOrder 3 = [0, 1, 2] := …
```

```lean
-- lean/ToyDropck/Examples.lean:117
theorem live_pos : live 2 [1] 0 = true := …
-- lean/ToyDropck/Examples.lean:118
theorem live_neg_dead : live 2 [1] 1 = false := …
-- lean/ToyDropck/Examples.lean:119
theorem live_neg_absent : live 2 [] 2 = false := …
```

```lean
-- lean/ToyDropck/Examples.lean:122
theorem observe_pos : observe (live 2 [1]) (.obj 1 [.ref 0]) = true := …
-- lean/ToyDropck/Examples.lean:123
theorem observe_neg : observe (live 2 [1]) (.obj 1 [.ref 1]) = false := …
```

```lean
-- lean/ToyDropck/Examples.lean:126-127
theorem dropVal_pos_ignoring :
    dropVal (behOf (mkTbl vecMD)) (live 2 [1]) (.obj 0 [.ref 1]) = true := …
-- lean/ToyDropck/Examples.lean:128-129
theorem dropVal_neg_using :
    dropVal (behOf (mkTbl vecMD)) (live 2 [1]) (.obj 1 [.ref 1]) = false := …
-- lean/ToyDropck/Examples.lean:130-131
theorem dropVal_neg_glue :
    dropVal (behOf (mkTbl vecMD)) (live 2 [1]) (.obj 0 [.obj 1 [.ref 1]]) = false := …
```

```lean
-- lean/ToyDropck/Examples.lean:134
theorem dropSafe_pos : DropSafe (mkTbl vecMD) (revDeclOrder 2) pContainer := …
-- lean/ToyDropck/Examples.lean:135
theorem dropSafe_neg : ¬ DropSafe (mkTbl liar) (revDeclOrder 2) pContainer := …
-- lean/ToyDropck/Examples.lean:137
theorem dropSafe_neg_self : ¬ DropSafe (mkTbl vecMD) (revDeclOrder 1) pSelfReader := …
-- lean/ToyDropck/Examples.lean:139
theorem dropSafe_ignores_undropped : DropSafe (mkTbl liar) [] pContainer := …
```

#### Honesty conditions (relating declarations to behaviour)

```lean
-- lean/ToyDropck/Basic.lean:152-153
def MayDangleHonest (d : DropImpl) : Prop :=
  d.beh.hasDrop = true → d.decl.mayDangle = true → d.beh.usesT = false
```

```lean
-- lean/ToyDropck/Basic.lean:157-158
def OwnsDeclared (d : DropImpl) : Prop :=
  d.beh.hasDrop = true → d.decl.mayDangle = true → d.beh.dropsElems = true → d.decl.ownsT = true
```

```lean
-- lean/ToyDropck/Basic.lean:164-165
def GlueVisible (d : DropImpl) : Prop :=
  d.beh.hasDrop = false → d.beh.dropsElems = true → d.decl.ownsT = true
```

```lean
-- lean/ToyDropck/Basic.lean:169-170
def MayDangleDropsNothing (d : DropImpl) : Prop :=
  d.beh.hasDrop = true → d.decl.mayDangle = true → d.beh.dropsElems = false
```

* `MayDangleHonest` models RFC 1327's assertion for `#[may_dangle] T`: the destructor does nothing with values of type `T` except move or drop them. (Dropping them may still run their own destructors.) Positive: `vecMD`; negative: `liar`.
* `OwnsDeclared` models the ownership (`PhantomData<T>`) condition: a `may_dangle` impl that drops its `T` elements tells the checker that it owns `T`. Positive: `vecMD`; negative: `vecNoOwn`.
* `GlueVisible`: a type without `Drop` impl whose glue drops its elements declares that it owns them. In the toy it is a separate condition on the table; the corresponding property of Rust's drop glue is the modeling bridge B6. Positive: `wrap`; negative: `hiddenGlue`.
* `MayDangleDropsNothing`: a `may_dangle` impl does not drop its `T` elements (it may still free its own storage), as for a raw buffer handle. Positive: `rawVec`; negative: `vecMD`.

```lean
-- lean/ToyDropck/Examples.lean:142
theorem mayDangleHonest_pos : MayDangleHonest vecMD := …
-- lean/ToyDropck/Examples.lean:143
theorem mayDangleHonest_neg : ¬ MayDangleHonest liar := …
-- lean/ToyDropck/Examples.lean:144
theorem ownsDeclared_pos : OwnsDeclared vecMD := …
-- lean/ToyDropck/Examples.lean:145
theorem ownsDeclared_neg : ¬ OwnsDeclared vecNoOwn := …
-- lean/ToyDropck/Examples.lean:146
theorem glueVisible_pos : GlueVisible wrap := …
-- lean/ToyDropck/Examples.lean:147
theorem glueVisible_neg : ¬ GlueVisible hiddenGlue := …
-- lean/ToyDropck/Examples.lean:148
theorem mayDangleDropsNothing_pos : MayDangleDropsNothing rawVec := …
-- lean/ToyDropck/Examples.lean:149
theorem mayDangleDropsNothing_neg : ¬ MayDangleDropsNothing vecMD := …
```

#### Typing and the checker (`ToyDropck/Checker.lean`)

```lean
-- lean/ToyDropck/Checker.lean:15-18
def lifetimes : Ty → List Nat
  | .int => []
  | .ref j => [j]
  | .app _ t => lifetimes t
```

```lean
-- lean/ToyDropck/Checker.lean:20-32
mutual
/-- `hasTy v t`: value `v` has type `t`. A reference `ref j` has exactly the type `ref j`; a
container value `obj c vs` has type `app c t` iff every element has type `t`. -/
def hasTy : Val → Ty → Bool
  | .int _, .int => true
  | .ref j, .ref k => j == k
  | .obj c vs, .app d t => c == d && hasTyAll vs t
  | _, _ => false
/-- `hasTy` for every element of a list. -/
def hasTyAll : List Val → Ty → Bool
  | [], _ => true
  | v :: vs, t => hasTy v t && hasTyAll vs t
end
```

```lean
-- lean/ToyDropck/Checker.lean:35-36
def ValuesHaveTypes (p : Prog) : Prop :=
  p.locals.all (fun e => hasTy e.2 e.1) = true
```

```lean
-- lean/ToyDropck/Checker.lean:40-41
def LifetimesInScope (p : Prog) : Prop :=
  p.locals.all (fun e => (lifetimes e.1).all (fun j => decide (j < p.locals.length))) = true
```

```lean
-- lean/ToyDropck/Checker.lean:50-51
def outlives (ord : List Nat) (i j : Nat) : Bool :=
  j != i && !(ord.takeWhile (· != i)).contains j
```

```lean
-- lean/ToyDropck/Checker.lean:64-69
inductive DanglePolicy where
  | ownsRecurse
  | noUseSuffices
  | headNoDrop
  | deepNoDrop
  deriving DecidableEq, Repr
```

```lean
-- lean/ToyDropck/Checker.lean:72-74
def headHasNoDrop (impls : ImplTable) : Ty → Bool
  | .app c _ => !(impls c).beh.hasDrop
  | _ => true
```

```lean
-- lean/ToyDropck/Checker.lean:77-79
def deepHasNoDrop (impls : ImplTable) : Ty → Bool
  | .app c t => !(impls c).beh.hasDrop && deepHasNoDrop impls t
  | _ => true
```

```lean
-- lean/ToyDropck/Checker.lean:88-100
def dropckP (pol : DanglePolicy) (impls : ImplTable) (ok : Nat → Bool) : Ty → Bool
  | .int => true
  | .ref _ => true
  | .app c t =>
    if (impls c).beh.hasDrop && (impls c).decl.mayDangle then
      match pol with
      | .ownsRecurse => !(impls c).decl.ownsT || dropckP pol impls ok t
      | .noUseSuffices => true
      | .headNoDrop => headHasNoDrop impls t || (lifetimes t).all ok
      | .deepNoDrop => deepHasNoDrop impls t || (lifetimes t).all ok
    else
      (!(impls c).beh.hasDrop || (lifetimes t).all ok) &&
      (!(impls c).decl.ownsT || dropckP pol impls ok t)
```

```lean
-- lean/ToyDropck/Checker.lean:103-107
def acceptsFrom (pol : DanglePolicy) (impls : ImplTable) (ord : List Nat) :
    Nat → List (Ty × Val) → Bool
  | _, [] => true
  | i, (t, _) :: rest =>
    (!ord.contains i || dropckP pol impls (outlives ord i) t) && acceptsFrom pol impls ord (i + 1) rest
```

```lean
-- lean/ToyDropck/Checker.lean:112-113
def acceptsP (pol : DanglePolicy) (impls : ImplTable) (ord : List Nat) (p : Prog) : Bool :=
  acceptsFrom pol impls ord 0 p.locals
```

```lean
-- lean/ToyDropck/Checker.lean:116-117
def accepts (impls : ImplTable) (ord : List Nat) (p : Prog) : Bool :=
  acceptsP .ownsRecurse impls ord p
```

```lean
-- lean/ToyDropck/Checker.lean:120-121
def stripDangle (impls : ImplTable) : ImplTable :=
  fun c => ⟨(impls c).beh, ⟨false, (impls c).decl.ownsT⟩⟩
```

```lean
-- lean/ToyDropck/Checker.lean:125-126
def acceptsStrict (impls : ImplTable) (ord : List Nat) (p : Prog) : Bool :=
  accepts (stripDangle impls) ord p
```

* `outlives ord i j`: local `j` is not `i` and is not dropped before the first occurrence of `i` in `ord`. The checker consults it for locals `i` that occur in `ord` (`acceptsFrom` skips the others); for such `i` and an existing local `j` it says that `j` strictly outlives `i`'s drop. (`outlives` does not know the number of locals; for an `i` absent from `ord` it scans the whole list.)
* `dropckP pol impls ok t` (the drop-check judgment for dropping a value of type `t` when exactly the lifetimes satisfying `ok` strictly outlive the drop). For `app c t`: if `c` has a `Drop` impl with `#[may_dangle]`, the policy decides; otherwise a `Drop` impl requires every lifetime of `t` to satisfy `ok` (the strict rule), and declared ownership of `T` recurses into `t`. Once every lifetime of `t` satisfies `ok`, every policy accepts `t` (`dropckP_of_lifetimes_ok`), so the recursion conjunct of the strict branch never rejects on its own.
* Policies for a `#[may_dangle]` parameter `T`: `ownsRecurse` (`T`'s lifetimes are exempt; if `T` is declared owned, the drop of `T` is checked recursively: RFC 1327's `#[may_dangle]` with RFC 769's ownership recursion); `noUseSuffices` (exempt, nothing else checked); `headNoDrop` (exempt when `T`'s outermost type constructor has no `Drop` impl, otherwise every lifetime of `T` must satisfy `ok`); `deepNoDrop` (exempt when no type constructor in `T` has a `Drop` impl, otherwise every lifetime of `T` must satisfy `ok`). R7 orders them: `acceptsStrict` ⊆ `deepNoDrop` ⊆ `ownsRecurse` ⊆ `noUseSuffices` and `deepNoDrop` ⊆ `headNoDrop` ⊆ `noUseSuffices`, all strict, with `headNoDrop` and `ownsRecurse` incomparable.
* `accepts` (the `may_dangle` checker) is `acceptsP .ownsRecurse`; `acceptsStrict` erases every `#[may_dangle]` first. Locals that `ord` never drops are not constrained.
* Distinct names: `DropSafe` is the semantic property; `accepts`, `acceptsStrict`, `acceptsP` are checker verdicts.

Examples (all proved):

```lean
-- lean/ToyDropck/Examples.lean:152
theorem hasTy_pos : hasTy (.obj 0 [.ref 1, .ref 1]) (.app 0 (.ref 1)) = true := …
-- lean/ToyDropck/Examples.lean:153
theorem hasTy_neg : hasTy (.obj 0 [.ref 1]) (.app 0 (.ref 0)) = false := …
-- lean/ToyDropck/Examples.lean:154
theorem valuesHaveTypes_pos : ValuesHaveTypes pContainer := …
-- lean/ToyDropck/Examples.lean:155
theorem valuesHaveTypes_neg : ¬ ValuesHaveTypes pIllTyped := …
-- lean/ToyDropck/Examples.lean:156
theorem lifetimesInScope_pos : LifetimesInScope pContainer := …
-- lean/ToyDropck/Examples.lean:157
theorem lifetimesInScope_neg : ¬ LifetimesInScope pOutOfScope := …
```

```lean
-- lean/ToyDropck/Examples.lean:161
theorem outlives_pos : outlives (revDeclOrder 2) 1 0 = true := …
-- lean/ToyDropck/Examples.lean:162
theorem outlives_neg : outlives (revDeclOrder 2) 0 1 = false := …
-- lean/ToyDropck/Examples.lean:163
theorem outlives_neg_self : outlives (revDeclOrder 2) 0 0 = false := …
-- lean/ToyDropck/Examples.lean:164
theorem outlivesNonStrict_self : outlivesNonStrict (revDeclOrder 2) 0 0 = true := …
```

```lean
-- lean/ToyDropck/Examples.lean:167
theorem headHasNoDrop_pos : headHasNoDrop (mkTbl vecMD) (.app 2 (.app 1 (.ref 1))) = true := …
-- lean/ToyDropck/Examples.lean:168
theorem headHasNoDrop_neg : headHasNoDrop (mkTbl vecMD) (.app 1 (.ref 1)) = false := …
-- lean/ToyDropck/Examples.lean:169
theorem deepHasNoDrop_pos : deepHasNoDrop (mkTbl vecMD) (.app 2 (.ref 1)) = true := …
-- lean/ToyDropck/Examples.lean:170
theorem deepHasNoDrop_neg : deepHasNoDrop (mkTbl vecMD) (.app 2 (.app 1 (.ref 1))) = false := …
```

```lean
-- lean/ToyDropck/Examples.lean:174-175
theorem dropck_pos :
    dropckP .ownsRecurse (mkTbl vecMD) (outlives (revDeclOrder 2) 0) (.app 0 (.ref 1)) = true := …
-- lean/ToyDropck/Examples.lean:177-178
theorem dropck_neg :
    dropckP .ownsRecurse (mkTbl vecMD) (outlives (revDeclOrder 2) 0) (.app 1 (.ref 1)) = false := …
-- lean/ToyDropck/Examples.lean:180-182
theorem dropck_noUseSuffices_pos :
    dropckP .noUseSuffices (mkTbl vecMD) (outlives (revDeclOrder 2) 0)
      (.app 0 (.app 1 (.ref 1))) = true := …
-- lean/ToyDropck/Examples.lean:184-186
theorem dropck_headNoDrop_pos :
    dropckP .headNoDrop (mkTbl vecMD) (outlives (revDeclOrder 2) 0)
      (.app 0 (.app 2 (.app 1 (.ref 1)))) = true := …
-- lean/ToyDropck/Examples.lean:188-190
theorem dropck_headNoDrop_neg :
    dropckP .headNoDrop (mkTbl vecMD) (outlives (revDeclOrder 2) 0)
      (.app 0 (.app 1 (.ref 1))) = false := …
-- lean/ToyDropck/Examples.lean:193-194
theorem dropck_deepNoDrop_exempt :
    dropckP .deepNoDrop (mkTbl vecMD) (outlives (revDeclOrder 2) 0) (.app 0 (.ref 1)) = true := …
-- lean/ToyDropck/Examples.lean:197-199
theorem dropck_deepNoDrop_fallback :
    dropckP .deepNoDrop (mkTbl vecMD) (outlives (revDeclOrder 2) 1)
      (.app 0 (.app 1 (.ref 0))) = true := …
-- lean/ToyDropck/Examples.lean:202-204
theorem dropck_deepNoDrop_neg :
    dropckP .deepNoDrop (mkTbl vecMD) (outlives (revDeclOrder 2) 0)
      (.app 0 (.app 2 (.app 1 (.ref 1)))) = false := …
```

```lean
-- lean/ToyDropck/Examples.lean:208
theorem accepts_pos : accepts (mkTbl vecMD) (revDeclOrder 2) pContainer = true := …
-- lean/ToyDropck/Examples.lean:209
theorem accepts_neg : accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false := …
-- lean/ToyDropck/Examples.lean:210
theorem acceptsStrict_pos : acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pReferentFirst = true := …
-- lean/ToyDropck/Examples.lean:212
theorem acceptsStrict_neg : acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pContainer = false := …
-- lean/ToyDropck/Examples.lean:214
theorem stripDangle_erases : stripDangle (mkTbl vecMD) 0 = vecStrict := …
-- lean/ToyDropck/Examples.lean:216
theorem accepts_ignores_undropped : accepts (mkTbl vecStrict) [] pContainer = true := …
```

#### Concrete container types and scopes (`ToyDropck/Examples.lean`)

```lean
-- lean/ToyDropck/Examples.lean:19
def vecMD : DropImpl := ⟨⟨true, false, true⟩, ⟨true, true⟩⟩
-- lean/ToyDropck/Examples.lean:21
def vecStrict : DropImpl := ⟨⟨true, false, true⟩, ⟨false, true⟩⟩
-- lean/ToyDropck/Examples.lean:23
def reader : DropImpl := ⟨⟨true, true, true⟩, ⟨false, true⟩⟩
-- lean/ToyDropck/Examples.lean:25
def wrap : DropImpl := ⟨⟨false, false, true⟩, ⟨false, true⟩⟩
-- lean/ToyDropck/Examples.lean:28
def vecNoOwn : DropImpl := ⟨⟨true, false, true⟩, ⟨true, false⟩⟩
-- lean/ToyDropck/Examples.lean:30
def liar : DropImpl := ⟨⟨true, true, true⟩, ⟨true, true⟩⟩
-- lean/ToyDropck/Examples.lean:33
def hiddenGlue : DropImpl := ⟨⟨false, false, true⟩, ⟨false, false⟩⟩
-- lean/ToyDropck/Examples.lean:35
def plain : DropImpl := ⟨⟨false, false, false⟩, ⟨false, false⟩⟩
-- lean/ToyDropck/Examples.lean:38
def rawVec : DropImpl := ⟨⟨true, false, false⟩, ⟨true, false⟩⟩
-- lean/ToyDropck/Examples.lean:40
def liarRaw : DropImpl := ⟨⟨true, true, false⟩, ⟨true, false⟩⟩
```

```lean
-- lean/ToyDropck/Examples.lean:44-48
def mkTbl (v : DropImpl) : ImplTable
  | 0 => v
  | 1 => reader
  | 2 => wrap
  | _ => plain
```

```lean
-- lean/ToyDropck/Examples.lean:53
def pContainer : Prog := ⟨[(.app 0 (.ref 1), .obj 0 [.ref 1]), (.int, .int 0)]⟩
-- lean/ToyDropck/Examples.lean:56
def pReferentFirst : Prog := ⟨[(.int, .int 0), (.app 0 (.ref 0), .obj 0 [.ref 0])]⟩
-- lean/ToyDropck/Examples.lean:59-60
def pOwnedReader : Prog :=
  ⟨[(.app 0 (.app 1 (.ref 1)), .obj 0 [.obj 1 [.ref 1]]), (.int, .int 0)]⟩
-- lean/ToyDropck/Examples.lean:64-65
def pNestedReader : Prog :=
  ⟨[(.app 0 (.app 2 (.app 1 (.ref 1))), .obj 0 [.obj 2 [.obj 1 [.ref 1]]]), (.int, .int 0)]⟩
-- lean/ToyDropck/Examples.lean:69-70
def pEmptyOwnedReader : Prog :=
  ⟨[(.app 0 (.app 1 (.ref 1)), .obj 0 []), (.int, .int 0)]⟩
-- lean/ToyDropck/Examples.lean:73-74
def pOwnedReaderAfter : Prog :=
  ⟨[(.int, .int 0), (.app 0 (.app 1 (.ref 0)), .obj 0 [.obj 1 [.ref 0]])]⟩
-- lean/ToyDropck/Examples.lean:78-79
def pNestedVec : Prog :=
  ⟨[(.app 0 (.app 0 (.ref 1)), .obj 0 [.obj 0 [.ref 1]]), (.int, .int 0)]⟩
-- lean/ToyDropck/Examples.lean:83-84
def pManuallyDropReader : Prog :=
  ⟨[(.app 0 (.app 3 (.app 1 (.ref 1))), .obj 0 [.obj 3 [.obj 1 [.ref 1]]]), (.int, .int 0)]⟩
-- lean/ToyDropck/Examples.lean:87
def pReaderAfter : Prog := ⟨[(.int, .int 0), (.app 1 (.ref 0), .obj 1 [.ref 0])]⟩
-- lean/ToyDropck/Examples.lean:90
def pSelfReader : Prog := ⟨[(.app 1 (.ref 0), .obj 1 [.ref 0])]⟩
-- lean/ToyDropck/Examples.lean:94-95
def pRefToRef : Prog :=
  ⟨[(.ref 2, .ref 2), (.app 1 (.ref 0), .obj 1 [.ref 0]), (.int, .int 0)]⟩
-- lean/ToyDropck/Examples.lean:98
def pIllTyped : Prog := ⟨[(.int, .obj 1 [.ref 1]), (.int, .int 0)]⟩
-- lean/ToyDropck/Examples.lean:101
def pOutOfScope : Prog := ⟨[(.ref 5, .ref 5)]⟩
-- lean/ToyDropck/Examples.lean:104
def pOutOfScopeReader : Prog := ⟨[(.app 1 (.ref 5), .obj 1 [.ref 5])]⟩
```

```lean
-- lean/ToyDropck/Examples.lean:108-109
def outlivesNonStrict (ord : List Nat) (i j : Nat) : Bool :=
  !(ord.takeWhile (· != i)).contains j
```

```lean
-- lean/ToyDropck/Examples.lean:222-223
theorem mkTbl_all {P : DropImpl → Prop} (v : DropImpl) (hv : P v) (hr : P reader) (hw : P wrap)
    (hp : P plain) : ∀ c, P (mkTbl v c) := …
```

```lean
-- lean/ToyDropck/Examples.lean:232-234
theorem honest_vecMD :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) := …
```

```lean
-- lean/ToyDropck/Examples.lean:240-242
theorem honest_vecStrict :
    (∀ c, MayDangleHonest (mkTbl vecStrict c)) ∧ (∀ c, OwnsDeclared (mkTbl vecStrict c)) ∧
      (∀ c, GlueVisible (mkTbl vecStrict c)) := …
```

```lean
-- lean/ToyDropck/Examples.lean:248-250
theorem honest_rawVec :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) := …
```

```lean
-- lean/ToyDropck/Examples.lean:256
theorem behOf_mkTbl_vecMD_eq_vecStrict : behOf (mkTbl vecMD) = behOf (mkTbl vecStrict) := …
```

Container `1` (`reader`, a `D<T>` whose destructor uses its element) and `2` (`wrap`, a plain struct `W<T>`) are fixed; container `0` varies; container `3` (`plain`) serves as a `ManuallyDrop<T>`-like wrapper. In every scope, local 0 is the first declared. The Rust glosses in the doc comments describe the intended reading of each scope at scope exit.

#### What the one-parameter model can express (`ToyDropck/Collapse.lean`)

```lean
-- lean/ToyDropck/Collapse.lean:16
theorem lifetimes_length_le_one : ∀ t : Ty, (lifetimes t).length ≤ 1
  -- (proof by structural recursion, elided)
```

```lean
-- lean/ToyDropck/Collapse.lean:23-27
def eraseMayDangle (impls : ImplTable) : ImplTable := fun c =>
  if (impls c).beh.hasDrop && (impls c).decl.mayDangle then
    ⟨⟨false, (impls c).beh.usesT, (impls c).beh.dropsElems⟩, ⟨false, (impls c).decl.ownsT⟩⟩
  else
    impls c
```

```lean
-- lean/ToyDropck/Collapse.lean:50-51
theorem accepts_eq_acceptsStrict_eraseMayDangle (impls : ImplTable) (ord : List Nat) (p : Prog) :
    accepts impls ord p = acceptsStrict (eraseMayDangle impls) ord p := …
```

```lean
-- lean/ToyDropck/Collapse.lean:98-100
theorem dropSafe_eraseMayDangle_iff {impls : ImplTable} (hmd : ∀ c, MayDangleHonest (impls c))
    (ord : List Nat) (p : Prog) :
    DropSafe (eraseMayDangle impls) ord p ↔ DropSafe impls ord p := …
```

```lean
-- lean/ToyDropck/Collapse.lean:105-107
theorem glueVisible_eraseMayDangle_iff (impls : ImplTable) :
    (∀ c, GlueVisible (eraseMayDangle impls c)) ↔
      (∀ c, OwnsDeclared (impls c)) ∧ (∀ c, GlueVisible (impls c)) := …
```

```lean
-- lean/ToyDropck/Inclusions.lean:15-16
theorem dropckP_of_lifetimes_ok (pol : DanglePolicy) (impls : ImplTable) (ok : Nat → Bool) :
    ∀ t : Ty, (lifetimes t).all ok = true → dropckP pol impls ok t = true
  -- (proof by structural recursion, elided)
```

Every type mentions at most one lifetime, and the model gives a destructor two possible actions on its parameter: using it and dropping it. Under `MayDangleHonest` an honest `#[may_dangle]` impl therefore does nothing observable before dropping its elements, and replacing it by a type without `Drop` impl with the same `dropsElems` and `ownsT` (`eraseMayDangle`) changes neither the `may_dangle` checker's verdict (it becomes the strict verdict on the erased table) nor the drop loop. In particular R3 follows from R1 in this model (the proof of R3 does exactly this). The model cannot express a `#[may_dangle]` destructor that still uses another, non-eyepatched parameter (RFC 1327's `Vec<T, A: Allocator>` and `CheckedHashMap<K, V>` examples), nor distinguish RFC 1327's per-parameter attribute from RFC 1238's all-parameters attribute.

### Results

#### R1 — Soundness of the strict rule

**Kind:** theorem. **Tier:** T1 — The Rustonomicon states that the strict rule is sufficient for soundness; RFC 769 states the rule; no mechanized statement was found.

Basis: execution (Lean kernel check), for the statement and for every Lean fact quoted in this card.

Basis: derived (modeling bridge), for any reading of this result as a statement about Rust: bridges B5 (strict rule), B6 (`GlueVisible`) and B7 (a local is dead during its own drop) under "Modeling bridges" below; argued by correspondence of definitions, not proved.

**Plain claim.** In the toy model, for every implementation table satisfying `GlueVisible` (types without a Drop impl declare ownership of the elements their glue drops), every drop order `ord`, and every scope `p` satisfying `ValuesHaveTypes` and `LifetimesInScope`: if the strict checker `acceptsStrict` (no `#[may_dangle]`; every type parameter of every Drop impl must strictly outlive the dropped value; declared-owned element types are checked recursively) accepts `p` for `ord`, then `DropSafe impls ord p`: dropping the locals of `p` in the order `ord` never observes a dead or nonexistent local, where a local counts as dead from the moment its own drop begins.

**Statement.**

```lean
-- lean/ToyDropck/Results.lean:27-30
theorem acceptsStrict_sound_of_glueVisible (impls : ImplTable) (ord : List Nat) (p : Prog)
    (hglue : ∀ c, GlueVisible (impls c)) (hval : ValuesHaveTypes p)
    (hscope : LifetimesInScope p) (hacc : acceptsStrict impls ord p = true) :
    DropSafe impls ord p := …
```

Unfolded (prose): For every `impls`, `ord`, `p`: if every container without a `Drop` impl declares ownership of the elements its glue drops, `p`'s values have their declared types, every lifetime in `p`'s declared types is a local of `p`, and the checker with all `#[may_dangle]` erased accepts `p` for `ord`, then running the drops of `p` in the order `ord` never reads a dead or nonexistent local.

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hglue : ∀ c, GlueVisible (impls c)` | a type without Drop impl whose glue drops its T elements must declare that it owns T, so that the checker's ownership recursion sees those drops | tight: counterexample `acceptsStrict_unsound_without_glueVisible` (witness class: a two-local scope with a Drop-less container whose glue drops an undeclared `D<&x>` element (a toy configuration chosen to violate `GlueVisible`)) |
| `hval : ValuesHaveTypes p` | the checker inspects declared types, never values; values must agree with them | tight: counterexample `acceptsStrict_unsound_without_valuesHaveTypes` (witness class: a two-local scope whose local declared `int` holds `D(&x)`) |
| `hscope : LifetimesInScope p` | the checker can judge a lifetime that names no local to outlive the drop (whenever it does not occur earlier in `ord`), while the runtime treats the nonexistent local as dead | tight: counterexample `acceptsStrict_unsound_without_lifetimesInScope` (witness class: a one-local scope holding `D(&local5)`) |
| `hacc : acceptsStrict impls ord p = true` | the checker verdict whose soundness is claimed | tight: counterexample `acceptsStrict_rejects_unsafe_pOwnedReader` (witness class: a two-local scope `Vec<D<&x>>` declared before `x`) |

**Depth:** shallow — `dropSafe_of_acceptsP` applied to the table with every `#[may_dangle]` erased (`stripDangle`), which the drop loop does not read (`dropSafe_stripDangle`): a structural induction on declared types (`dropVal_of_dropckP`) plus a prefix invariant for the drop loop (`runDrops_of_each`).

**Non-vacuity witness:** `pReferentFirst` (`let x = 0; let v = vec![&x];`) with table `mkTbl vecStrict` and order `revDeclOrder 2` satisfies all hypotheses. (`acceptsStrict_sound_hypotheses_hold_pReferentFirst`)

```lean
-- lean/ToyDropck/Results.lean:37-40
theorem acceptsStrict_sound_hypotheses_hold_pReferentFirst :
    (∀ c, GlueVisible (mkTbl vecStrict c)) ∧ ValuesHaveTypes pReferentFirst ∧
      LifetimesInScope pReferentFirst ∧
      acceptsStrict (mkTbl vecStrict) (revDeclOrder 2) pReferentFirst = true := …
```

**Counterexamples and companion facts (fully proved):**

```lean
-- lean/ToyDropck/Results.lean:45-49
theorem acceptsStrict_unsound_without_glueVisible :
    ¬ (∀ c, GlueVisible (mkTbl hiddenGlue c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsStrict (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader := …
```

```lean
-- lean/ToyDropck/Results.lean:53-57
theorem acceptsStrict_unsound_without_valuesHaveTypes :
    (∀ c, GlueVisible (mkTbl vecStrict c)) ∧ ¬ ValuesHaveTypes pIllTyped ∧
      LifetimesInScope pIllTyped ∧
      acceptsStrict (mkTbl vecStrict) (revDeclOrder 2) pIllTyped = true ∧
      ¬ DropSafe (mkTbl vecStrict) (revDeclOrder 2) pIllTyped := …
```

```lean
-- lean/ToyDropck/Results.lean:61-65
theorem acceptsStrict_unsound_without_lifetimesInScope :
    (∀ c, GlueVisible (mkTbl vecStrict c)) ∧ ValuesHaveTypes pOutOfScopeReader ∧
      ¬ LifetimesInScope pOutOfScopeReader ∧
      acceptsStrict (mkTbl vecStrict) (revDeclOrder 1) pOutOfScopeReader = true ∧
      ¬ DropSafe (mkTbl vecStrict) (revDeclOrder 1) pOutOfScopeReader := …
```

```lean
-- lean/ToyDropck/Results.lean:69-73
theorem acceptsStrict_rejects_unsafe_pOwnedReader :
    (∀ c, GlueVisible (mkTbl vecStrict c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsStrict (mkTbl vecStrict) (revDeclOrder 2) pOwnedReader = false ∧
      ¬ DropSafe (mkTbl vecStrict) (revDeclOrder 2) pOwnedReader := …
```

```lean
-- lean/ToyDropck/Results.lean:80-88
theorem nonStrictOutlives_accepts_unsafe_pSelfReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pSelfReader ∧
      LifetimesInScope pSelfReader ∧
      dropckP .ownsRecurse (mkTbl vecMD) (outlivesNonStrict (revDeclOrder 1) 0)
        (.app 1 (.ref 0)) = true ∧
      acceptsStrict (mkTbl vecMD) (revDeclOrder 1) pSelfReader = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 1) pSelfReader = false ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 1) pSelfReader := …
```

```lean
-- lean/ToyDropck/Results.lean:95-101
theorem pRefToRef_accepted_and_dropSafe :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pRefToRef ∧
      LifetimesInScope pRefToRef ∧
      acceptsStrict (mkTbl vecMD) (revDeclOrder 3) pRefToRef = true ∧
      accepts (mkTbl vecMD) (revDeclOrder 3) pRefToRef = true ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 3) pRefToRef := …
```

**Non-claims.**

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* Does not say that the strict rule is necessary for safety: R2 (`acceptsStrict_rejects_dropSafe_pContainer`) exhibits a safe scope that the strict checker rejects.
* `GlueVisible` is a toy-level condition on the table; whether Rust's drop glue satisfies an analogue of it is a separate derived (modeling bridge) claim (B6), not a theorem here.
* Soundness is relative to the drop order: the checker is given the same `ord` that the drop loop executes (see R5, `dropOrder_matters_pReaderAfter`).
* A local counts as dead from the moment its own drop begins (`runDrops` drops the value with the local already in the dead set), so a destructor that observes its own local through a stored reference is undefined behaviour in the toy (`dropSafe_neg_self`). This is a modeling choice. Under it, replacing `outlives` by its non-strict variant `outlivesNonStrict` (without `j != i`) makes the per-local judgment accept an unsafe scope (`nonStrictOutlives_accepts_unsafe_pSelfReader`). Aliasing rules for `&mut self` are not modelled.
* `observe` recurses through nested container values and, on a reference `ref j`, checks that local `j` is live without reading local `j`'s own value. `Ty.ref j` records the referent local and not the referent's type, so no condition relates the lifetimes of a reference to a reference. Consequently a destructor that holds a reference to a live local whose own value is a reference to a dead local is accepted by both checkers and is `DropSafe` in the toy (`pRefToRef_accepted_and_dropSafe`); soundness under a semantics that dereferences transitively is not addressed (not proved either way).
* References (`Val.ref j`) always target top-level locals, and `dropAll` keeps the live set fixed while the elements of one value are dropped. References between elements of the same container (such as the cyclic structures discussed in RFC 1238) and fields that refer to earlier-dropped fields of the same value are not modelled; the results neither validate nor rule them out.
* `ord` is an arbitrary list, not required to be a permutation of the locals: repeated and out-of-range indices are skipped, and locals that `ord` never names are never dropped (a leak), on which neither the checkers nor `DropSafe` impose anything (`accepts_ignores_undropped`, `dropSafe_ignores_undropped`). The results do not assert that every local is dropped.
* One-parameter model: every type mentions at most one lifetime (`lifetimes_length_le_one`), and the model gives a destructor two possible actions on its parameter: using its values (`usesT`) and dropping them (`dropsElems`). Hence, under `MayDangleHonest`, a `#[may_dangle]` `Drop` impl is interchangeable with a type without `Drop` impl, both for the `may_dangle` checker (`accepts_eq_acceptsStrict_eraseMayDangle`) and for the drop loop (`dropSafe_eraseMayDangle_iff`). The results say nothing about a destructor that keeps using another, non-eyepatched parameter or field while `T` dangles (the multi-parameter situation that motivates RFC 1327), and the toy cannot distinguish RFC 1327's per-parameter `#[may_dangle]` from RFC 1238's all-parameters `#[unsafe_destructor_blind_to_params]`.
* The table conditions quantify over every container in the table, including containers that `p` never mentions; whether conditions restricted to the containers a scope mentions suffice is not proved here.
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).
* Undefined behaviour in the toy arises from observing a dead or nonexistent local and from nothing else; a destructor's use of its elements is all-or-nothing (`usesT`).

**Prior art.**

* F. S. Klock II, RFC 769 'Sound Generic Drop' (PR rust-lang/rfcs#769, opened 2015-01-29; text/0769-sound-generic-drop.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4): states the drop-check rule (a lifetime 'a reachable from owned data whose type has a lifetime- or type-parametric Drop impl must strictly outlive the value, with parametricity-based exemptions), defines type ownership by recursive descent ('When does one type own another', line 380) and adds the special case 'If E is PhantomData<T>, then recurse on T' (line 453); partially superseded by RFC 1238 (2015-09-18).
* The Rustonomicon, 'Drop Check' (rust-lang/nomicon, src/dropck.md at commit 3c17036782395893fdc639185da1783065ec4571): 'For a generic type to soundly implement drop, its generics arguments must strictly outlive it.' (lines 128-129); obeying this rule 'is sufficient but not necessary to be sound' (lines 132-133); for a self-borrowing struct, 'You can try changing the order of fields or use a tuple instead of the struct, it'll still not compile.' (lines 113-114).
* N. D. Matsakis, RFC 2094 'non-lexical lifetimes' (PR rust-lang/rfcs#2094, opened 2017-08-02; text/2094-nll.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, section 'Layer 3: Accommodating dropck', line 1338): when a variable may be dropped later, 'all of the lifetimes in its type except those marked as may-dangle are live'. The toy instead checks one scope's fixed drop order against a 'strictly outlives' relation.
* Rust Compiler Development Guide, 'Drop Check' (rust-lang/rustc-dev-guide, src/borrow-check/drop-check.md at commit 5ac3dc3cc93fcb4c04bdf0821dc17282ee614089): dropck_outlives requires the generic arguments of an explicit Drop impl to be live 'unless they are marked with #[may_dangle] in which case they are fully ignored' (line 125), recurses into all owned types, considers PhantomData<U> to own U and ManuallyDrop<U> not to own U (lines 132-133), and states 'We only rely on dropck_outlives if Ty::needs_drop for the containing local returned true' (line 138); its opening example is a Vec holding a reference to a shorter-lived String, and it shows that dropck still requires a local to be live after the local has been moved out.
* R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), article 66, 2018, doi:10.1145/3158154, Section 9 (Conclusion): 'We proved safety of the destructors of the verified libraries, but do not handle automatic destruction'.
* Novelty search: web searches for mechanized soundness proofs of dropck or #[may_dangle]; RustBelt Section 9 (Conclusion); the full texts of Oxide (A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, 'Oxide: The Essence of Rust', arXiv:1903.00982) and RefinedRust (L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, PACMPL 8(PLDI), 2024, doi:10.1145/3656422) contain neither 'dropck' nor 'may_dangle'; bibliographic records of D. J. Pearce, 'A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust' (ACM TOPLAS 43(1), 2021, doi:10.1145/3443420), and RustHornBelt (Y. Matsushita, X. Denis, J.-H. Jourdan, D. Dreyer, PLDI 2022, doi:10.1145/3519939.3523704) were checked at the DOI registry but their full texts were not searched; Patina (E. C. Reed, technical report UW-CSE-15-03-02, 2015) is listed from a search summary and was not verified at the source; region-based memory management (M. Tofte, J.-P. Talpin, Information and Computation 132(2):109-176, 1997, doi:10.1006/inco.1996.2613) deallocates whole regions without per-object destructors. No mechanized treatment of dropck or #[may_dangle] was found; tier T1 is claimed, not T3.

**Design question.** When is it sound to let a generic container's destructor run after some of its type parameters' lifetimes have ended, what does `#[may_dangle]` assert, and which plausible relaxations are not enough? (Baseline: the conservative rule is sound.)

#### R2 — The strict rule rejects the container pattern

**Kind:** counterexample. **Tier:** T1 — The single-parameter container pattern is the opening example of the Rustonomicon's PhantomData discussion of `#[may_dangle]` and of the rustc-dev-guide 'Drop Check' chapter; here it is a kernel-checked instance in the toy.

Basis: execution (Lean kernel check), for the statement and for every Lean fact quoted in this card.

Basis: derived (modeling bridge), for any reading of this result as a statement about Rust: bridges B1 (checker shape), B3 (`PhantomData<T>`) and B5 (strict rule) under "Modeling bridges" below; argued by correspondence of definitions, not proved.

**Plain claim.** In the toy model, for the scope `pContainer` (`let mut v = Vec::new(); let x = 0; v.push(&x);`, so `v` is dropped after `x` in reverse declaration order) and the single table `mkTbl vecMD` (a `Vec` whose Drop impl carries `#[may_dangle]` and drops its elements without otherwise using them): `MayDangleHonest`, `OwnsDeclared` and `GlueVisible` hold; the table's runtime behaviour equals that of `mkTbl vecStrict` (the same `Vec` without `#[may_dangle]`); `ValuesHaveTypes` and `LifetimesInScope` hold; the drops in reverse declaration order are safe (`DropSafe`); the strict checker `acceptsStrict` rejects the scope for that order; and the `may_dangle` checker `accepts` accepts it.

**Statement.**

```lean
-- lean/ToyDropck/Results.lean:113-120
theorem acceptsStrict_rejects_dropSafe_pContainer :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧
      behOf (mkTbl vecMD) = behOf (mkTbl vecStrict) ∧
      ValuesHaveTypes pContainer ∧ LifetimesInScope pContainer ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 2) pContainer ∧
      acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pContainer = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pContainer = true := …
```

Hypothesis ledger: none (a statement about one concrete instance; every hypothesis of the related theorems is stated as a conjunct and proved).

**Depth:** definitional — Evaluation of decidable propositions on one concrete instance (`decide`).

**Non-vacuity witness:** The statement is about the concrete instance `pContainer` with the table `mkTbl vecMD` and order `revDeclOrder 2`. (`acceptsStrict_rejects_dropSafe_pContainer`)

**Counterexamples and companion facts (fully proved):**

```lean
-- lean/ToyDropck/Results.lean:126-128
theorem acceptsStrict_accepts_pReferentFirst :
    acceptsStrict (mkTbl vecStrict) (revDeclOrder 2) pReferentFirst = true ∧
      DropSafe (mkTbl vecStrict) (revDeclOrder 2) pReferentFirst := …
```

**Non-claims.**

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* `acceptsStrict (mkTbl vecMD)` is by definition the `may_dangle` checker on `stripDangle (mkTbl vecMD)`, whose entry `0` is `vecStrict` (`stripDangle_erases`); the strict verdict is thus the verdict for the `Vec` without `#[may_dangle]`.
* The scope `let x = 0; let v = vec![&x];` (referent declared first) is not an instance of this pattern: there `v` is dropped first and the strict checker already accepts (`acceptsStrict_accepts_pReferentFirst`).
* Says nothing about how often the pattern occurs or about other patterns that the strict rule rejects.
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).

**Prior art.**

* The Rustonomicon, 'PhantomData' (rust-lang/nomicon, src/phantom-data.md at commit 84f9ba51efd903d5d46c44274be6f98d528e8d66): with a classical impl<T> Drop for Vec<T>, the scope 'let mut v: Vec<&str> = Vec::new(); let s: String = ...; v.push(&s); drop(s);' is denied (lines 135-144); with #[may_dangle] T, 'T may dangle provided it not be involved in some transitive drop glue', and #[may_dangle] is disabled when the generic parameter is held in an owned fashion by the fields of the struct (lines 192-196); the PrintOnDrop<'s> element example; the standard library's Vec<T> keeps a _owns_T: PhantomData<T> field (line 220).
* Rust Compiler Development Guide, 'Drop Check' (rust-lang/rustc-dev-guide, src/borrow-check/drop-check.md at commit 5ac3dc3cc93fcb4c04bdf0821dc17282ee614089): dropck_outlives requires the generic arguments of an explicit Drop impl to be live 'unless they are marked with #[may_dangle] in which case they are fully ignored' (line 125), recurses into all owned types, considers PhantomData<U> to own U and ManuallyDrop<U> not to own U (lines 132-133), and states 'We only rely on dropck_outlives if Ty::needs_drop for the containing local returned true' (line 138); its opening example is a Vec holding a reference to a shorter-lived String, and it shows that dropck still requires a local to be live after the local has been moved out.
* The Rustonomicon, 'Drop Check' (rust-lang/nomicon, src/dropck.md at commit 3c17036782395893fdc639185da1783065ec4571): 'For a generic type to soundly implement drop, its generics arguments must strictly outlive it.' (lines 128-129); obeying this rule 'is sufficient but not necessary to be sound' (lines 132-133); for a self-borrowing struct, 'You can try changing the order of fields or use a tuple instead of the struct, it'll still not compile.' (lines 113-114).
* The Rust Reference, 'Destructors' (rust-lang/reference, src/destructors.md at commit 84dc36ff4712fad6829b6063cd4acbcaf5381708): the variables of a drop scope are dropped 'in reverse order of declaration' (line 59); the fields of a struct are dropped in declaration order (line 12).
* F. S. Klock II, RFC 1327 (PR rust-lang/rfcs#1327 'Dropck Eyepatch RFC.', opened 2015-10-19; text/1327-dropck-param-eyepatch.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4; feature dropck_eyepatch, tracking issue rust-lang/rust#34761): introduces per-parameter #[may_dangle]; on a type parameter 'the programmer is asserting the only uses of values of that type will be to move or drop them' (lines 250-252); its motivating examples are multi-parameter types (CheckedHashMap<K, V>, line 66; Vec<T, A: Allocator>, line 88), and its unresolved questions state 'We have not proven any previous variation of the rule sound' (lines 599-600).

**Design question.** When is it sound to let a generic container's destructor run after some of its type parameters' lifetimes have ended, what does `#[may_dangle]` assert, and which plausible relaxations are not enough? (In the toy model: one container scope whose drops in reverse declaration order are safe but which the strict rule rejects for that order.)

#### R3 — Soundness of `#[may_dangle]` with the ownership condition

**Kind:** theorem. **Tier:** T1 — RFC 769 (ownership recursion, `PhantomData<T>`), RFC 1327 (`#[may_dangle]`) and the Rustonomicon PhantomData chapter state the rule and its ownership condition informally; RFC 1327 records that no variation of the rule has been proven sound; RustBelt does not handle automatic destruction; no mechanized statement was found.

Basis: execution (Lean kernel check), for the statement and for every Lean fact quoted in this card.

Basis: derived (modeling bridge), for any reading of this result as a statement about Rust: bridges B1 (checker shape), B2 (`MayDangleHonest`), B3 (`OwnsDeclared`) and B6 (`GlueVisible`) under "Modeling bridges" below; argued by correspondence of definitions, not proved.

**Plain claim.** In the toy model, for every implementation table satisfying `MayDangleHonest` (a Drop impl that claims `#[may_dangle]` on `T` does not use its `T` elements), `OwnsDeclared` (such an impl that drops its `T` elements declares that it owns `T`) and `GlueVisible` (types without a Drop impl declare ownership of the elements their glue drops), every drop order `ord`, and every scope `p` satisfying `ValuesHaveTypes` and `LifetimesInScope`: if the `may_dangle` checker `accepts` (a `#[may_dangle]` parameter is exempt from the strict-outlives requirement, and if the type declares that it owns `T`, the drop of `T` itself is checked recursively) accepts `p` for `ord`, then `DropSafe impls ord p`: dropping the locals of `p` in the order `ord` never observes a dead or nonexistent local.

**Statement.**

```lean
-- lean/ToyDropck/Results.lean:141-146
theorem accepts_sound_of_mayDangleHonest_ownsDeclared_glueVisible (impls : ImplTable)
    (ord : List Nat) (p : Prog)
    (hmd : ∀ c, MayDangleHonest (impls c)) (hown : ∀ c, OwnsDeclared (impls c))
    (hglue : ∀ c, GlueVisible (impls c)) (hval : ValuesHaveTypes p)
    (hscope : LifetimesInScope p) (hacc : accepts impls ord p = true) :
    DropSafe impls ord p := …
```

Unfolded (prose): For every `impls`, `ord`, `p`: if (i) no destructor claiming `#[may_dangle]` uses its elements, (ii) every such destructor that drops its elements declares ownership of `T`, (iii) every container without a `Drop` impl declares ownership of the elements its glue drops, (iv) `p`'s values have their declared types, (v) every lifetime in `p`'s declared types is a local of `p`, and (vi) the `ownsRecurse` checker accepts `p` for `ord`, then running the drops of `p` in the order `ord` never reads a dead or nonexistent local.

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hmd : ∀ c, MayDangleHonest (impls c)` | the unchecked `#[may_dangle]` promise must be true: the destructor does not use its T elements | tight: counterexample `accepts_unsound_without_mayDangleHonest` (witness class: the two-local scope `pContainer` with a `may_dangle` Vec whose destructor uses its elements) |
| `hown : ∀ c, OwnsDeclared (impls c)` | the ownership (`PhantomData<T>`) condition: a `may_dangle` impl that drops its T elements declares that it owns T, so that the drop of T itself is checked | tight: counterexample `accepts_unsound_without_ownsDeclared` (witness class: the two-local scope `pOwnedReader` (`Vec<D<&x>>`, `D`'s destructor dereferencing `&x`) with a truthful `may_dangle` Vec that drops its elements without declaring ownership) |
| `hglue : ∀ c, GlueVisible (impls c)` | a type without Drop impl whose glue drops its T elements must declare that it owns T, so that the checker's ownership recursion sees those drops | tight: counterexample `accepts_unsound_without_glueVisible` (witness class: the two-local scope `pOwnedReader` with a Drop-less container whose glue drops an undeclared element (a toy configuration chosen to violate `GlueVisible`)) |
| `hval : ValuesHaveTypes p` | the checker inspects declared types, never values; values must agree with them | tight: counterexample `accepts_unsound_without_valuesHaveTypes` (witness class: a two-local scope whose local declared `int` holds `D(&x)`) |
| `hscope : LifetimesInScope p` | the checker can judge a lifetime that names no local to outlive the drop (whenever it does not occur earlier in `ord`), while the runtime treats the nonexistent local as dead | tight: counterexample `accepts_unsound_without_lifetimesInScope` (witness class: a one-local scope holding `D(&local5)`) |
| `hacc : accepts impls ord p = true` | the checker verdict whose soundness is claimed | tight: counterexample `accepts_rejects_unsafe_pOwnedReader` (witness class: the two-local scope `pOwnedReader` with the honest `may_dangle` Vec, which the checker rejects) |

**Depth:** shallow — In this one-parameter model R3 is proved from R1: `accepts_eq_acceptsStrict_eraseMayDangle`, `dropSafe_eraseMayDangle_iff` and `glueVisible_eraseMayDangle_iff` replace every honest `#[may_dangle]` impl by a Drop-less type with the same element drops and ownership declaration (`eraseMayDangle`); conversely R1 is the special case of R3 without `#[may_dangle]`. The content lies in the definitions.

**Non-vacuity witness:** `pContainer` with table `mkTbl vecMD` (a `may_dangle` Vec with `PhantomData<T>`) and order `revDeclOrder 2` satisfies all hypotheses. (`accepts_sound_hypotheses_hold_pContainer`)

```lean
-- lean/ToyDropck/Results.lean:153-157
theorem accepts_sound_hypotheses_hold_pContainer :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pContainer ∧
      LifetimesInScope pContainer ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pContainer = true := …
```

**Counterexamples and companion facts (fully proved):**

```lean
-- lean/ToyDropck/Results.lean:161-166
theorem accepts_unsound_without_mayDangleHonest :
    ¬ (∀ c, MayDangleHonest (mkTbl liar c)) ∧ (∀ c, OwnsDeclared (mkTbl liar c)) ∧
      (∀ c, GlueVisible (mkTbl liar c)) ∧ ValuesHaveTypes pContainer ∧
      LifetimesInScope pContainer ∧
      accepts (mkTbl liar) (revDeclOrder 2) pContainer = true ∧
      ¬ DropSafe (mkTbl liar) (revDeclOrder 2) pContainer := …
```

```lean
-- lean/ToyDropck/Results.lean:174-179
theorem accepts_unsound_without_ownsDeclared :
    (∀ c, MayDangleHonest (mkTbl vecNoOwn c)) ∧ ¬ (∀ c, OwnsDeclared (mkTbl vecNoOwn c)) ∧
      (∀ c, GlueVisible (mkTbl vecNoOwn c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      accepts (mkTbl vecNoOwn) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl vecNoOwn) (revDeclOrder 2) pOwnedReader := …
```

```lean
-- lean/ToyDropck/Results.lean:186-191
theorem accepts_unsound_without_glueVisible :
    (∀ c, MayDangleHonest (mkTbl hiddenGlue c)) ∧ (∀ c, OwnsDeclared (mkTbl hiddenGlue c)) ∧
      ¬ (∀ c, GlueVisible (mkTbl hiddenGlue c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      accepts (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader := …
```

```lean
-- lean/ToyDropck/Results.lean:198-203
theorem accepts_unsound_without_valuesHaveTypes :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ¬ ValuesHaveTypes pIllTyped ∧
      LifetimesInScope pIllTyped ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pIllTyped = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pIllTyped := …
```

```lean
-- lean/ToyDropck/Results.lean:207-212
theorem accepts_unsound_without_lifetimesInScope :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pOutOfScopeReader ∧
      ¬ LifetimesInScope pOutOfScopeReader ∧
      accepts (mkTbl vecMD) (revDeclOrder 1) pOutOfScopeReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 1) pOutOfScopeReader := …
```

```lean
-- lean/ToyDropck/Results.lean:217-222
theorem accepts_rejects_unsafe_pOwnedReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pOwnedReader := …
```

**Non-claims.**

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* Does not say that rustc implements `accepts`, nor that the standard library's `#[may_dangle]` impls satisfy `MayDangleHonest` or `OwnsDeclared`; those are separate derived (modeling bridge) claims (B1-B3).
* Does not say that the checker is complete: R6 (`accepts_incomplete_pEmptyOwnedReader`) exhibits a safe scope that it rejects.
* The table conditions quantify over every container in the table, including containers that `p` never mentions; whether conditions restricted to the containers a scope mentions suffice is not proved here.
* Soundness is relative to the drop order: the checker is given the same `ord` that the drop loop executes (see R5, `dropOrder_matters_pReaderAfter`).
* One-parameter model: every type mentions at most one lifetime (`lifetimes_length_le_one`), and the model gives a destructor two possible actions on its parameter: using its values (`usesT`) and dropping them (`dropsElems`). Hence, under `MayDangleHonest`, a `#[may_dangle]` `Drop` impl is interchangeable with a type without `Drop` impl, both for the `may_dangle` checker (`accepts_eq_acceptsStrict_eraseMayDangle`) and for the drop loop (`dropSafe_eraseMayDangle_iff`). The results say nothing about a destructor that keeps using another, non-eyepatched parameter or field while `T` dangles (the multi-parameter situation that motivates RFC 1327), and the toy cannot distinguish RFC 1327's per-parameter `#[may_dangle]` from RFC 1238's all-parameters `#[unsafe_destructor_blind_to_params]`.
* According to the rustc-dev-guide ('Drop Check'), rustc consults `dropck_outlives` for a local when `Ty::needs_drop` holds for the local's type ('We only rely on `dropck_outlives` if `Ty::needs_drop` for the containing local returned `true`'), and treats `PhantomData<U>` as owning `U` in `dropck_outlives` but not in `Ty::needs_drop`; `dropckP` has no such gate and always recurses into a declared-owned parameter. `PhantomData<T>` also affects variance and auto traits, which are not modelled.
* A local counts as dead from the moment its own drop begins (`runDrops` drops the value with the local already in the dead set), so a destructor that observes its own local through a stored reference is undefined behaviour in the toy (`dropSafe_neg_self`). This is a modeling choice. Under it, replacing `outlives` by its non-strict variant `outlivesNonStrict` (without `j != i`) makes the per-local judgment accept an unsafe scope (`nonStrictOutlives_accepts_unsafe_pSelfReader`). Aliasing rules for `&mut self` are not modelled.
* `observe` recurses through nested container values and, on a reference `ref j`, checks that local `j` is live without reading local `j`'s own value. `Ty.ref j` records the referent local and not the referent's type, so no condition relates the lifetimes of a reference to a reference. Consequently a destructor that holds a reference to a live local whose own value is a reference to a dead local is accepted by both checkers and is `DropSafe` in the toy (`pRefToRef_accepted_and_dropSafe`); soundness under a semantics that dereferences transitively is not addressed (not proved either way).
* References (`Val.ref j`) always target top-level locals, and `dropAll` keeps the live set fixed while the elements of one value are dropped. References between elements of the same container (such as the cyclic structures discussed in RFC 1238) and fields that refer to earlier-dropped fields of the same value are not modelled; the results neither validate nor rule them out.
* `ord` is an arbitrary list, not required to be a permutation of the locals: repeated and out-of-range indices are skipped, and locals that `ord` never names are never dropped (a leak), on which neither the checkers nor `DropSafe` impose anything (`accepts_ignores_undropped`, `dropSafe_ignores_undropped`). The results do not assert that every local is dropped.
* `GlueVisible` is a toy-level condition on the table; whether Rust's drop glue satisfies an analogue of it is a separate derived (modeling bridge) claim (B6), not a theorem here.
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).
* Undefined behaviour in the toy arises from observing a dead or nonexistent local and from nothing else; a destructor's use of its elements is all-or-nothing (`usesT`).

**Prior art.**

* F. S. Klock II, RFC 1327 (PR rust-lang/rfcs#1327 'Dropck Eyepatch RFC.', opened 2015-10-19; text/1327-dropck-param-eyepatch.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4; feature dropck_eyepatch, tracking issue rust-lang/rust#34761): introduces per-parameter #[may_dangle]; on a type parameter 'the programmer is asserting the only uses of values of that type will be to move or drop them' (lines 250-252); its motivating examples are multi-parameter types (CheckedHashMap<K, V>, line 66; Vec<T, A: Allocator>, line 88), and its unresolved questions state 'We have not proven any previous variation of the rule sound' (lines 599-600).
* F. S. Klock II, RFC 769 'Sound Generic Drop' (PR rust-lang/rfcs#769, opened 2015-01-29; text/0769-sound-generic-drop.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4): states the drop-check rule (a lifetime 'a reachable from owned data whose type has a lifetime- or type-parametric Drop impl must strictly outlive the value, with parametricity-based exemptions), defines type ownership by recursive descent ('When does one type own another', line 380) and adds the special case 'If E is PhantomData<T>, then recurse on T' (line 453); partially superseded by RFC 1238 (2015-09-18).
* F. S. Klock II, RFC 1238 'Nonparametric dropck' (PR rust-lang/rfcs#1238, opened 2015-08-05; text/1238-nonparametric-dropck.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4): drops RFC 769's reliance on parametricity ('cannot-assume-parametricity') and adds the unsafe attribute #[unsafe_destructor_blind_to_params] ('unguarded-escape-hatch'), which covers all type parameters of a destructor at once.
* The Rustonomicon, 'PhantomData' (rust-lang/nomicon, src/phantom-data.md at commit 84f9ba51efd903d5d46c44274be6f98d528e8d66): with a classical impl<T> Drop for Vec<T>, the scope 'let mut v: Vec<&str> = Vec::new(); let s: String = ...; v.push(&s); drop(s);' is denied (lines 135-144); with #[may_dangle] T, 'T may dangle provided it not be involved in some transitive drop glue', and #[may_dangle] is disabled when the generic parameter is held in an owned fashion by the fields of the struct (lines 192-196); the PrintOnDrop<'s> element example; the standard library's Vec<T> keeps a _owns_T: PhantomData<T> field (line 220).
* Rust Compiler Development Guide, 'Drop Check' (rust-lang/rustc-dev-guide, src/borrow-check/drop-check.md at commit 5ac3dc3cc93fcb4c04bdf0821dc17282ee614089): dropck_outlives requires the generic arguments of an explicit Drop impl to be live 'unless they are marked with #[may_dangle] in which case they are fully ignored' (line 125), recurses into all owned types, considers PhantomData<U> to own U and ManuallyDrop<U> not to own U (lines 132-133), and states 'We only rely on dropck_outlives if Ty::needs_drop for the containing local returned true' (line 138); its opening example is a Vec holding a reference to a shorter-lived String, and it shows that dropck still requires a local to be live after the local has been moved out.
* N. D. Matsakis, RFC 2094 'non-lexical lifetimes' (PR rust-lang/rfcs#2094, opened 2017-08-02; text/2094-nll.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, section 'Layer 3: Accommodating dropck', line 1338): when a variable may be dropped later, 'all of the lifetimes in its type except those marked as may-dangle are live'. The toy instead checks one scope's fixed drop order against a 'strictly outlives' relation.
* rust-lang/rust#76367 'Soundness issue in Drop for SyncOnceCell' (https://github.com/rust-lang/rust/issues/76367, opened 2020-09-05, closed): the issue states that #[may_dangle] on T in the Drop implementation of SyncOnceCell is correct for simple types such as T = &str but, when T's Drop implementation accesses borrowed data, might lead to accessing already dropped data; rust-lang/rust#99408 'Too lenient #[may_dangle] on BTreeMap; misses PhantomData for dropck' (https://github.com/rust-lang/rust/issues/99408, opened 2022-07-18, closed). The second is a standard-library instance of the failure that accepts_unsound_without_ownsDeclared models (derived (modeling bridge), not proved); the open, unmerged pull request rust-lang/rfcs#3417 cites both as motivation.
* lcnr, PR rust-lang/rfcs#3417 'improve #[may_dangle] for type parameters' (https://github.com/rust-lang/rfcs/pull/3417, opened 2023-04-17; an open, unmerged pull request as of 2026-11-21, so a proposal rather than an accepted RFC or a description of current Rust; text/3417-dropck-eyepatch-v3.md at the pull request's head commit 8f8303a6ac0fb86b8611b91d7047bd72b825cbe9 in the contributor fork lcnr/rfcs): proposes #[may_dangle(droppable)] (the impl recursively drops values of T) and #[may_dangle(must_not_use)] (it does not), and that dropck ignore PhantomData; the split parallels the toy's distinction between #[may_dangle] impls that drop their elements (R3, R4a) and impls that do not (R8). It is cited as design discussion; no definition, result or modeling bridge relies on it.
* R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), article 66, 2018, doi:10.1145/3158154, Section 9 (Conclusion): 'We proved safety of the destructors of the verified libraries, but do not handle automatic destruction'.
* R. Jung, 'Formalizing Rust', blog post, 2015-10-12, https://www.ralfj.de/blog/2015/10/12/formalizing-rust.html: the first version of the RustBelt formalization would not cover the Drop trait and dropck; 'dropck may well be the most subtle part of the type system'.
* Novelty search: web searches for mechanized soundness proofs of dropck or #[may_dangle]; RustBelt Section 9 (Conclusion); the full texts of Oxide (A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, 'Oxide: The Essence of Rust', arXiv:1903.00982) and RefinedRust (L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, PACMPL 8(PLDI), 2024, doi:10.1145/3656422) contain neither 'dropck' nor 'may_dangle'; bibliographic records of D. J. Pearce, 'A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust' (ACM TOPLAS 43(1), 2021, doi:10.1145/3443420), and RustHornBelt (Y. Matsushita, X. Denis, J.-H. Jourdan, D. Dreyer, PLDI 2022, doi:10.1145/3519939.3523704) were checked at the DOI registry but their full texts were not searched; Patina (E. C. Reed, technical report UW-CSE-15-03-02, 2015) is listed from a search summary and was not verified at the source; region-based memory management (M. Tofte, J.-P. Talpin, Information and Computation 132(2):109-176, 1997, doi:10.1006/inco.1996.2613) deallocates whole regions without per-object destructors. No mechanized treatment of dropck or #[may_dangle] was found; tier T1 is claimed, not T3.

**Design question.** When is it sound to let a generic container's destructor run after some of its type parameters' lifetimes have ended, what does `#[may_dangle]` assert, and which plausible relaxations are not enough? (In the toy model: for implementation tables satisfying `MayDangleHonest` (the `#[may_dangle]` assertion that the destructor does not use its `T` elements), `OwnsDeclared` (the ownership condition) and `GlueVisible`, and for scopes satisfying `ValuesHaveTypes` and `LifetimesInScope`, acceptance by `accepts` for a drop order implies `DropSafe` for that order; each of these hypotheses has a single-instance counterexample in the ledger.)

#### R4a — "The destructor never uses `T`" without the ownership recursion is unsound

**Kind:** counterexample. **Tier:** T1 — The Rustonomicon PhantomData chapter describes this failure informally (`PrintOnDrop<'s>` elements); here it is a kernel-checked instance.

Basis: execution (Lean kernel check), for the statement and for every Lean fact quoted in this card.

Basis: derived (modeling bridge), for any reading of this result as a statement about Rust: bridges B2 (`MayDangleHonest`) and B3 (`OwnsDeclared`) under "Modeling bridges" below; argued by correspondence of definitions, not proved.

**Plain claim.** In the toy model, the relaxation `noUseSuffices` (a `#[may_dangle]` type parameter is exempt from the outlives requirement and nothing about the drop of its values is checked) is unsound: for the scope `pOwnedReader` (`let mut v = Vec::new(); let x = 0; v.push(D(&x));`, `D`'s destructor using `&x`) and the table `mkTbl vecMD`, `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `ValuesHaveTypes` and `LifetimesInScope` hold, the `noUseSuffices` checker accepts the scope for reverse declaration order, and its drops in that order observe a dead local.

**Statement.**

```lean
-- lean/ToyDropck/Results.lean:231-236
theorem noUseSuffices_accepts_unsafe_pOwnedReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .noUseSuffices (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pOwnedReader := …
```

Hypothesis ledger: none (a statement about one concrete instance; every hypothesis of the related theorems is stated as a conjunct and proved).

**Depth:** definitional — Evaluation on one concrete instance (`decide`).

**Non-vacuity witness:** The concrete instance `pOwnedReader`, `mkTbl vecMD`, `revDeclOrder 2`. (`noUseSuffices_accepts_unsafe_pOwnedReader`)

**Positive control:** `noUseSuffices_accepts_safe_pOwnedReader_rawVec`, `sound_policies_reject_pOwnedReader_pNestedReader`.

**Counterexamples and companion facts (fully proved):**

```lean
-- lean/ToyDropck/Results.lean:241-246
theorem noUseSuffices_accepts_safe_pOwnedReader_rawVec :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .noUseSuffices (mkTbl rawVec) (revDeclOrder 2) pOwnedReader = true ∧
      DropSafe (mkTbl rawVec) (revDeclOrder 2) pOwnedReader := …
```

```lean
-- lean/ToyDropck/Results.lean:264-268
theorem sound_policies_reject_pOwnedReader_pNestedReader :
    accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pNestedReader = false ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = false := …
```

**Non-claims.**

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* Refutes the soundness of one specific relaxed checker in the toy; it does not show that every checker ignoring element drops is unsound in every language.
* The unsafety is caused by the element type's own destructor (`D`), not by the container's destructor, which here satisfies `MayDangleHonest`.
* Escape hatch: the counterexample relies on the `#[may_dangle]` container dropping its elements (`dropsElems = true`). When no `#[may_dangle]` impl drops its elements (`MayDangleDropsNothing`), every policy, including `noUseSuffices` and `headNoDrop`, is sound in the toy under the other hypotheses of R8 (`MayDangleHonest`, `GlueVisible`, `ValuesHaveTypes`, `LifetimesInScope`; R8, `acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible`); the same scope with such a container is accepted by `noUseSuffices` and safe (`noUseSuffices_accepts_safe_pOwnedReader_rawVec`).
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).

**Prior art.**

* The Rustonomicon, 'PhantomData' (rust-lang/nomicon, src/phantom-data.md at commit 84f9ba51efd903d5d46c44274be6f98d528e8d66): with a classical impl<T> Drop for Vec<T>, the scope 'let mut v: Vec<&str> = Vec::new(); let s: String = ...; v.push(&s); drop(s);' is denied (lines 135-144); with #[may_dangle] T, 'T may dangle provided it not be involved in some transitive drop glue', and #[may_dangle] is disabled when the generic parameter is held in an owned fashion by the fields of the struct (lines 192-196); the PrintOnDrop<'s> element example; the standard library's Vec<T> keeps a _owns_T: PhantomData<T> field (line 220).
* F. S. Klock II, RFC 1327 (PR rust-lang/rfcs#1327 'Dropck Eyepatch RFC.', opened 2015-10-19; text/1327-dropck-param-eyepatch.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4; feature dropck_eyepatch, tracking issue rust-lang/rust#34761): introduces per-parameter #[may_dangle]; on a type parameter 'the programmer is asserting the only uses of values of that type will be to move or drop them' (lines 250-252); its motivating examples are multi-parameter types (CheckedHashMap<K, V>, line 66; Vec<T, A: Allocator>, line 88), and its unresolved questions state 'We have not proven any previous variation of the rule sound' (lines 599-600).
* lcnr, PR rust-lang/rfcs#3417 'improve #[may_dangle] for type parameters' (https://github.com/rust-lang/rfcs/pull/3417, opened 2023-04-17; an open, unmerged pull request as of 2026-11-21, so a proposal rather than an accepted RFC or a description of current Rust; text/3417-dropck-eyepatch-v3.md at the pull request's head commit 8f8303a6ac0fb86b8611b91d7047bd72b825cbe9 in the contributor fork lcnr/rfcs): proposes #[may_dangle(droppable)] (the impl recursively drops values of T) and #[may_dangle(must_not_use)] (it does not), and that dropck ignore PhantomData; the split parallels the toy's distinction between #[may_dangle] impls that drop their elements (R3, R4a) and impls that do not (R8). It is cited as design discussion; no definition, result or modeling bridge relies on it.

**Design question.** When is it sound to let a generic container's destructor run after some of its type parameters' lifetimes have ended, what does `#[may_dangle]` assert, and which plausible relaxations are not enough? (In the toy model: for one scope whose `#[may_dangle]` container drops its elements (`dropsElems = true`), with `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `ValuesHaveTypes` and `LifetimesInScope` holding, the relaxation `noUseSuffices`, which checks nothing about the drop of the eyepatched parameter's values, accepts the scope for reverse declaration order and its drops observe a dead local.)

#### R4b — "`T: !Drop`" checked shallowly is unsound

**Kind:** counterexample. **Tier:** T1 — Folklore (the Rustonomicon speaks of 'transitive drop glue'); here a kernel-checked instance.

Basis: execution (Lean kernel check), for the statement and for every Lean fact quoted in this card.

Basis: derived (modeling bridge), for any reading of this result as a statement about Rust: bridges B1 (checker shape), B2 (`MayDangleHonest`) and B3 (`OwnsDeclared`) under "Modeling bridges" below; argued by correspondence of definitions, not proved.

**Plain claim.** In the toy model, the relaxation `headNoDrop` (a `#[may_dangle]` type parameter `T` is exempt from the outlives requirement when the outermost type constructor of `T` has no Drop impl, and otherwise every lifetime of `T` must strictly outlive the drop; no ownership recursion below a `#[may_dangle]` impl) is unsound: for the scope `pNestedReader` (`let mut v = Vec::new(); let x = 0; v.push(W(D(&x)));`, `W` a plain struct without Drop impl, `D`'s destructor using `&x`) and the table `mkTbl vecMD`, `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `ValuesHaveTypes` and `LifetimesInScope` hold, the `headNoDrop` checker accepts the scope for reverse declaration order, and its drops in that order observe a dead local.

**Statement.**

```lean
-- lean/ToyDropck/Results.lean:254-259
theorem headNoDrop_accepts_unsafe_pNestedReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pNestedReader ∧
      LifetimesInScope pNestedReader ∧
      acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pNestedReader := …
```

Hypothesis ledger: none (a statement about one concrete instance; every hypothesis of the related theorems is stated as a conjunct and proved).

**Depth:** definitional — Evaluation on one concrete instance (`decide`).

**Non-vacuity witness:** The concrete instance `pNestedReader`, `mkTbl vecMD`, `revDeclOrder 2`. (`headNoDrop_accepts_unsafe_pNestedReader`)

**Positive control:** `acceptsP_deepNoDrop_sound_of_mayDangleHonest_glueVisible`, `sound_policies_reject_pOwnedReader_pNestedReader`, `headNoDrop_accepts_safe_pNestedReader_rawVec`.

**Companion facts (fully proved):**

```lean
-- lean/ToyDropck/Companions.lean:19-24
theorem headNoDrop_accepts_safe_pNestedReader_rawVec :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ValuesHaveTypes pNestedReader ∧
      LifetimesInScope pNestedReader ∧
      acceptsP .headNoDrop (mkTbl rawVec) (revDeclOrder 2) pNestedReader = true ∧
      DropSafe (mkTbl rawVec) (revDeclOrder 2) pNestedReader := …
```

**Non-claims.**

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* `headNoDrop` is a relaxation of the strict checker (R7, `acceptsP_of_acceptsStrict`); the result does not refute "`T: !Drop`" checked deeply, which is sound in the toy under the hypotheses of R4c (`acceptsP_deepNoDrop_sound_of_mayDangleHonest_glueVisible`).
* Does not refute the shallow check combined with the ownership recursion; the refuted checker replaces the recursion by the shallow check (with the outlives requirement as fallback).
* Escape hatch: the counterexample relies on the `#[may_dangle]` container dropping its elements (`dropsElems = true`). When no `#[may_dangle]` impl drops its elements (`MayDangleDropsNothing`), every policy, including `noUseSuffices` and `headNoDrop`, is sound in the toy under the other hypotheses of R8 (`MayDangleHonest`, `GlueVisible`, `ValuesHaveTypes`, `LifetimesInScope`; R8, `acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible`); with such a container (`mkTbl rawVec`), the scope of this result, `pNestedReader`, is accepted by `headNoDrop` and its drops in reverse declaration order are safe (`headNoDrop_accepts_safe_pNestedReader_rawVec`).
* The names `headNoDrop` and `deepNoDrop` refer to the toy tests `headHasNoDrop` and `deepHasNoDrop`, not to a Rust trait bound: in Rust, whether a type has a `Drop` impl is a property of its outermost type constructor, while whether it has drop glue (`core::mem::needs_drop`) also depends on its fields. `deepHasNoDrop` inspects every type constructor in `T`, including ones whose drop does nothing, so the `deepNoDrop` checker rejects the safe scope `pManuallyDropReader` (`deepNoDrop_rejects_accepted_safe_pManuallyDropReader`).
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).

**Prior art.**

* The Rustonomicon, 'PhantomData' (rust-lang/nomicon, src/phantom-data.md at commit 84f9ba51efd903d5d46c44274be6f98d528e8d66): with a classical impl<T> Drop for Vec<T>, the scope 'let mut v: Vec<&str> = Vec::new(); let s: String = ...; v.push(&s); drop(s);' is denied (lines 135-144); with #[may_dangle] T, 'T may dangle provided it not be involved in some transitive drop glue', and #[may_dangle] is disabled when the generic parameter is held in an owned fashion by the fields of the struct (lines 192-196); the PrintOnDrop<'s> element example; the standard library's Vec<T> keeps a _owns_T: PhantomData<T> field (line 220).
* F. S. Klock II, RFC 1327 (PR rust-lang/rfcs#1327 'Dropck Eyepatch RFC.', opened 2015-10-19; text/1327-dropck-param-eyepatch.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4; feature dropck_eyepatch, tracking issue rust-lang/rust#34761): introduces per-parameter #[may_dangle]; on a type parameter 'the programmer is asserting the only uses of values of that type will be to move or drop them' (lines 250-252); its motivating examples are multi-parameter types (CheckedHashMap<K, V>, line 66; Vec<T, A: Allocator>, line 88), and its unresolved questions state 'We have not proven any previous variation of the rule sound' (lines 599-600).
* Rust Compiler Development Guide, 'Drop Check' (rust-lang/rustc-dev-guide, src/borrow-check/drop-check.md at commit 5ac3dc3cc93fcb4c04bdf0821dc17282ee614089): dropck_outlives requires the generic arguments of an explicit Drop impl to be live 'unless they are marked with #[may_dangle] in which case they are fully ignored' (line 125), recurses into all owned types, considers PhantomData<U> to own U and ManuallyDrop<U> not to own U (lines 132-133), and states 'We only rely on dropck_outlives if Ty::needs_drop for the containing local returned true' (line 138); its opening example is a Vec holding a reference to a shorter-lived String, and it shows that dropck still requires a local to be live after the local has been moved out.

**Design question.** When is it sound to let a generic container's destructor run after some of its type parameters' lifetimes have ended, what does `#[may_dangle]` assert, and which plausible relaxations are not enough? (In the toy model: with `MayDangleHonest`, `OwnsDeclared` and `GlueVisible` holding, checking "T: !Drop" at the head of `T` in place of the ownership recursion accepts an unsafe scope (R4b); under `MayDangleHonest` and `GlueVisible`, for scopes satisfying `ValuesHaveTypes` and `LifetimesInScope`, checking it through the whole type is sound (R4c).)

#### R4c — "`T: !Drop`" checked deeply is sound (positive control for R4b)

**Kind:** theorem. **Tier:** T1 — The Rustonomicon's '`T` may dangle provided it not be involved in some transitive drop glue' (with `#[may_dangle]` disabled otherwise) states the idea informally; no mechanized statement was found.

Basis: execution (Lean kernel check), for the statement and for every Lean fact quoted in this card.

Basis: derived (modeling bridge), for any reading of this result as a statement about Rust: bridges B2 (`MayDangleHonest`) and B6 (`GlueVisible`) under "Modeling bridges" below; argued by correspondence of definitions, not proved.

**Plain claim.** In the toy model, for every implementation table satisfying `MayDangleHonest` and `GlueVisible`, every drop order `ord`, and every scope `p` satisfying `ValuesHaveTypes` and `LifetimesInScope`: if the `deepNoDrop` checker (a `#[may_dangle]` type parameter `T` is exempt from the outlives requirement when no type constructor occurring in `T` has a Drop impl, and otherwise every lifetime of `T` must strictly outlive the drop; no ownership recursion below a `#[may_dangle]` impl) accepts `p` for `ord`, then `DropSafe impls ord p`: dropping the locals of `p` in the order `ord` never observes a dead or nonexistent local; `OwnsDeclared` is not assumed.

**Statement.**

```lean
-- lean/ToyDropck/Results.lean:276-280
theorem acceptsP_deepNoDrop_sound_of_mayDangleHonest_glueVisible (impls : ImplTable)
    (ord : List Nat) (p : Prog)
    (hmd : ∀ c, MayDangleHonest (impls c)) (hglue : ∀ c, GlueVisible (impls c))
    (hval : ValuesHaveTypes p) (hscope : LifetimesInScope p)
    (hacc : acceptsP .deepNoDrop impls ord p = true) : DropSafe impls ord p := …
```

Unfolded (prose): For every `impls`, `ord`, `p`: if (i) no destructor claiming `#[may_dangle]` uses its elements, (ii) every container without a `Drop` impl declares ownership of the elements its glue drops, (iii) `p`'s values have their declared types, (iv) every lifetime in `p`'s declared types is a local of `p`, and (v) the `deepNoDrop` checker accepts `p` for `ord`, then running the drops of `p` in the order `ord` never reads a dead or nonexistent local.

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hmd : ∀ c, MayDangleHonest (impls c)` | the unchecked `#[may_dangle]` promise must be true: the destructor does not use its T elements | tight: counterexample `deepNoDrop_unsound_without_mayDangleHonest` (witness class: the two-local scope `pContainer` with a `may_dangle` Vec whose destructor uses its `&x` elements (T = `&x` has no Drop impl anywhere)) |
| `hglue : ∀ c, GlueVisible (impls c)` | a type without Drop impl whose glue drops its T elements must declare that it owns T, so that the checker's ownership recursion sees those drops | tight: counterexample `deepNoDrop_unsound_without_glueVisible` (witness class: the two-local scope `pOwnedReader` with a Drop-less container whose glue drops an undeclared element (a toy configuration chosen to violate `GlueVisible`)) |
| `hval : ValuesHaveTypes p` | the checker inspects declared types, never values; values must agree with them | tight: counterexample `deepNoDrop_unsound_without_valuesHaveTypes` (witness class: a two-local scope whose local declared `int` holds `D(&x)`) |
| `hscope : LifetimesInScope p` | the checker can judge a lifetime that names no local to outlive the drop (whenever it does not occur earlier in `ord`), while the runtime treats the nonexistent local as dead | tight: counterexample `deepNoDrop_unsound_without_lifetimesInScope` (witness class: a one-local scope holding `D(&local5)`) |
| `hacc : acceptsP .deepNoDrop impls ord p = true` | the checker verdict whose soundness is claimed | tight: counterexample `deepNoDrop_rejects_unsafe_pNestedReader` (witness class: the two-local scope `pNestedReader`, rejected by the deep check) |

**Depth:** shallow — `dropSafe_of_acceptsP` with the `deepNoDrop` policy: in the `#[may_dangle]` case either no type constructor in `T` has a Drop impl, so dropping a value of type `T` observes nothing (`dropVal_of_deepHasNoDrop`), or every lifetime of `T` outlives the drop (`dropVal_of_lifetimes_live`).

**Non-vacuity witness:** `pContainer` with table `mkTbl vecNoOwn` (a `may_dangle` Vec without ownership declaration, violating `OwnsDeclared`) and order `revDeclOrder 2` satisfies all hypotheses. (`deepNoDrop_sound_hypotheses_hold_pContainer_vecNoOwn`)

```lean
-- lean/ToyDropck/Results.lean:284-288
theorem deepNoDrop_sound_hypotheses_hold_pContainer_vecNoOwn :
    (∀ c, MayDangleHonest (mkTbl vecNoOwn c)) ∧ (∀ c, GlueVisible (mkTbl vecNoOwn c)) ∧
      ValuesHaveTypes pContainer ∧ LifetimesInScope pContainer ∧
      acceptsP .deepNoDrop (mkTbl vecNoOwn) (revDeclOrder 2) pContainer = true ∧
      ¬ (∀ c, OwnsDeclared (mkTbl vecNoOwn c)) := …
```

**Counterexamples and companion facts (fully proved):**

```lean
-- lean/ToyDropck/Results.lean:294-298
theorem deepNoDrop_unsound_without_mayDangleHonest :
    ¬ (∀ c, MayDangleHonest (mkTbl liar c)) ∧ (∀ c, GlueVisible (mkTbl liar c)) ∧
      ValuesHaveTypes pContainer ∧ LifetimesInScope pContainer ∧
      acceptsP .deepNoDrop (mkTbl liar) (revDeclOrder 2) pContainer = true ∧
      ¬ DropSafe (mkTbl liar) (revDeclOrder 2) pContainer := …
```

```lean
-- lean/ToyDropck/Results.lean:304-308
theorem deepNoDrop_unsound_without_glueVisible :
    (∀ c, MayDangleHonest (mkTbl hiddenGlue c)) ∧ ¬ (∀ c, GlueVisible (mkTbl hiddenGlue c)) ∧
      ValuesHaveTypes pOwnedReader ∧ LifetimesInScope pOwnedReader ∧
      acceptsP .deepNoDrop (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader := …
```

```lean
-- lean/ToyDropck/Results.lean:314-318
theorem deepNoDrop_unsound_without_valuesHaveTypes :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, GlueVisible (mkTbl vecMD c)) ∧
      ¬ ValuesHaveTypes pIllTyped ∧ LifetimesInScope pIllTyped ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pIllTyped = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pIllTyped := …
```

```lean
-- lean/ToyDropck/Results.lean:322-326
theorem deepNoDrop_unsound_without_lifetimesInScope :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, GlueVisible (mkTbl vecMD c)) ∧
      ValuesHaveTypes pOutOfScopeReader ∧ ¬ LifetimesInScope pOutOfScopeReader ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 1) pOutOfScopeReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 1) pOutOfScopeReader := …
```

```lean
-- lean/ToyDropck/Results.lean:330-334
theorem deepNoDrop_rejects_unsafe_pNestedReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, GlueVisible (mkTbl vecMD c)) ∧
      ValuesHaveTypes pNestedReader ∧ LifetimesInScope pNestedReader ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = false ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pNestedReader := …
```

```lean
-- lean/ToyDropck/Results.lean:339-343
theorem deepNoDrop_rejects_accepted_safe_pNestedVec :
    ValuesHaveTypes pNestedVec ∧ LifetimesInScope pNestedVec ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pNestedVec = true ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedVec = false ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 2) pNestedVec := …
```

```lean
-- lean/ToyDropck/Results.lean:348-352
theorem deepNoDrop_rejects_accepted_safe_pManuallyDropReader :
    ValuesHaveTypes pManuallyDropReader ∧ LifetimesInScope pManuallyDropReader ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pManuallyDropReader = true ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pManuallyDropReader = false ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 2) pManuallyDropReader := …
```

**Non-claims.**

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* Does not say that "`T: !Drop`" alone suffices: `deepNoDrop_unsound_without_mayDangleHonest` shows that a destructor using `T` is unsafe even when `T` has no Drop impl anywhere.
* Every scope that the `deepNoDrop` checker accepts is accepted by the `may_dangle` checker (R7, `accepts_of_acceptsP_deepNoDrop`), but not conversely: `deepNoDrop_rejects_accepted_safe_pNestedVec` (a `Vec<Vec<&x>>` declared before `x`) and `deepNoDrop_rejects_accepted_safe_pManuallyDropReader` are safe scopes that the deep check rejects and the ownership recursion accepts.
* The names `headNoDrop` and `deepNoDrop` refer to the toy tests `headHasNoDrop` and `deepHasNoDrop`, not to a Rust trait bound: in Rust, whether a type has a `Drop` impl is a property of its outermost type constructor, while whether it has drop glue (`core::mem::needs_drop`) also depends on its fields. `deepHasNoDrop` inspects every type constructor in `T`, including ones whose drop does nothing, so the `deepNoDrop` checker rejects the safe scope `pManuallyDropReader` (`deepNoDrop_rejects_accepted_safe_pManuallyDropReader`).
* One-parameter model: every type mentions at most one lifetime (`lifetimes_length_le_one`), and the model gives a destructor two possible actions on its parameter: using its values (`usesT`) and dropping them (`dropsElems`). Hence, under `MayDangleHonest`, a `#[may_dangle]` `Drop` impl is interchangeable with a type without `Drop` impl, both for the `may_dangle` checker (`accepts_eq_acceptsStrict_eraseMayDangle`) and for the drop loop (`dropSafe_eraseMayDangle_iff`). The results say nothing about a destructor that keeps using another, non-eyepatched parameter or field while `T` dangles (the multi-parameter situation that motivates RFC 1327), and the toy cannot distinguish RFC 1327's per-parameter `#[may_dangle]` from RFC 1238's all-parameters `#[unsafe_destructor_blind_to_params]`.
* A local counts as dead from the moment its own drop begins (`runDrops` drops the value with the local already in the dead set), so a destructor that observes its own local through a stored reference is undefined behaviour in the toy (`dropSafe_neg_self`). This is a modeling choice. Under it, replacing `outlives` by its non-strict variant `outlivesNonStrict` (without `j != i`) makes the per-local judgment accept an unsafe scope (`nonStrictOutlives_accepts_unsafe_pSelfReader`). Aliasing rules for `&mut self` are not modelled.
* `observe` recurses through nested container values and, on a reference `ref j`, checks that local `j` is live without reading local `j`'s own value. `Ty.ref j` records the referent local and not the referent's type, so no condition relates the lifetimes of a reference to a reference. Consequently a destructor that holds a reference to a live local whose own value is a reference to a dead local is accepted by both checkers and is `DropSafe` in the toy (`pRefToRef_accepted_and_dropSafe`); soundness under a semantics that dereferences transitively is not addressed (not proved either way).
* References (`Val.ref j`) always target top-level locals, and `dropAll` keeps the live set fixed while the elements of one value are dropped. References between elements of the same container (such as the cyclic structures discussed in RFC 1238) and fields that refer to earlier-dropped fields of the same value are not modelled; the results neither validate nor rule them out.
* `ord` is an arbitrary list, not required to be a permutation of the locals: repeated and out-of-range indices are skipped, and locals that `ord` never names are never dropped (a leak), on which neither the checkers nor `DropSafe` impose anything (`accepts_ignores_undropped`, `dropSafe_ignores_undropped`). The results do not assert that every local is dropped.
* `GlueVisible` is a toy-level condition on the table; whether Rust's drop glue satisfies an analogue of it is a separate derived (modeling bridge) claim (B6), not a theorem here.
* Soundness is relative to the drop order: the checker is given the same `ord` that the drop loop executes (see R5, `dropOrder_matters_pReaderAfter`).
* The table conditions quantify over every container in the table, including containers that `p` never mentions; whether conditions restricted to the containers a scope mentions suffice is not proved here.
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).
* Undefined behaviour in the toy arises from observing a dead or nonexistent local and from nothing else; a destructor's use of its elements is all-or-nothing (`usesT`).

**Prior art.**

* The Rustonomicon, 'PhantomData' (rust-lang/nomicon, src/phantom-data.md at commit 84f9ba51efd903d5d46c44274be6f98d528e8d66): with a classical impl<T> Drop for Vec<T>, the scope 'let mut v: Vec<&str> = Vec::new(); let s: String = ...; v.push(&s); drop(s);' is denied (lines 135-144); with #[may_dangle] T, 'T may dangle provided it not be involved in some transitive drop glue', and #[may_dangle] is disabled when the generic parameter is held in an owned fashion by the fields of the struct (lines 192-196); the PrintOnDrop<'s> element example; the standard library's Vec<T> keeps a _owns_T: PhantomData<T> field (line 220).
* F. S. Klock II, RFC 1327 (PR rust-lang/rfcs#1327 'Dropck Eyepatch RFC.', opened 2015-10-19; text/1327-dropck-param-eyepatch.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4; feature dropck_eyepatch, tracking issue rust-lang/rust#34761): introduces per-parameter #[may_dangle]; on a type parameter 'the programmer is asserting the only uses of values of that type will be to move or drop them' (lines 250-252); its motivating examples are multi-parameter types (CheckedHashMap<K, V>, line 66; Vec<T, A: Allocator>, line 88), and its unresolved questions state 'We have not proven any previous variation of the rule sound' (lines 599-600).
* Rust Compiler Development Guide, 'Drop Check' (rust-lang/rustc-dev-guide, src/borrow-check/drop-check.md at commit 5ac3dc3cc93fcb4c04bdf0821dc17282ee614089): dropck_outlives requires the generic arguments of an explicit Drop impl to be live 'unless they are marked with #[may_dangle] in which case they are fully ignored' (line 125), recurses into all owned types, considers PhantomData<U> to own U and ManuallyDrop<U> not to own U (lines 132-133), and states 'We only rely on dropck_outlives if Ty::needs_drop for the containing local returned true' (line 138); its opening example is a Vec holding a reference to a shorter-lived String, and it shows that dropck still requires a local to be live after the local has been moved out.
* Novelty search: web searches for mechanized soundness proofs of dropck or #[may_dangle]; RustBelt Section 9 (Conclusion); the full texts of Oxide (A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, 'Oxide: The Essence of Rust', arXiv:1903.00982) and RefinedRust (L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, PACMPL 8(PLDI), 2024, doi:10.1145/3656422) contain neither 'dropck' nor 'may_dangle'; bibliographic records of D. J. Pearce, 'A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust' (ACM TOPLAS 43(1), 2021, doi:10.1145/3443420), and RustHornBelt (Y. Matsushita, X. Denis, J.-H. Jourdan, D. Dreyer, PLDI 2022, doi:10.1145/3519939.3523704) were checked at the DOI registry but their full texts were not searched; Patina (E. C. Reed, technical report UW-CSE-15-03-02, 2015) is listed from a search summary and was not verified at the source; region-based memory management (M. Tofte, J.-P. Talpin, Information and Computation 132(2):109-176, 1997, doi:10.1006/inco.1996.2613) deallocates whole regions without per-object destructors. No mechanized treatment of dropck or #[may_dangle] was found; tier T1 is claimed, not T3.

**Design question.** When is it sound to let a generic container's destructor run after some of its type parameters' lifetimes have ended, what does `#[may_dangle]` assert, and which plausible relaxations are not enough? (In the toy model: a policy proved sound without `OwnsDeclared`, under `MayDangleHonest` and `GlueVisible` and for scopes satisfying `ValuesHaveTypes` and `LifetimesInScope`.)

#### R5 — Drop order matters

**Kind:** counterexample. **Tier:** T1 — That dropck reasons relative to the language's drop order is folklore; here a kernel-checked instance.

Basis: execution (Lean kernel check), for the statement and for every Lean fact quoted in this card.

Basis: derived (modeling bridge), for any reading of this result as a statement about Rust: bridges B4 (reverse declaration order) under "Modeling bridges" below; argued by correspondence of definitions, not proved.

**Plain claim.** In the toy model, for the scope `pReaderAfter` (`let x = 0; let d = D(&x);`, `D`'s destructor using `&x`) and the table `mkTbl vecMD` (whose entry `0` does not occur in the scope), with `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `ValuesHaveTypes` and `LifetimesInScope` holding: the `may_dangle` checker accepts the scope for reverse declaration order and the drops in that order are safe, the drops in declaration order observe a dead local, and the checker, given declaration order, rejects the scope.

**Statement.**

```lean
-- lean/ToyDropck/Results.lean:362-369
theorem dropOrder_matters_pReaderAfter :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pReaderAfter ∧
      LifetimesInScope pReaderAfter ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pReaderAfter = true ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 2) pReaderAfter ∧
      ¬ DropSafe (mkTbl vecMD) (declOrder 2) pReaderAfter ∧
      accepts (mkTbl vecMD) (declOrder 2) pReaderAfter = false := …
```

Hypothesis ledger: none (a statement about one concrete instance; every hypothesis of the related theorems is stated as a conjunct and proved).

**Depth:** definitional — Evaluation on one concrete instance (`decide`).

**Non-vacuity witness:** The concrete instance `pReaderAfter`, `mkTbl vecMD`, orders `revDeclOrder 2` and `declOrder 2`. (`dropOrder_matters_pReaderAfter`)

**Non-claims.**

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* Refutes the order-free reading "accepted for reverse declaration order implies safe for every order"; it does not refute R3 (`accepts_sound_of_mayDangleHonest_ownsDeclared_glueVisible`), which gives the checker the executed order.
* Says nothing about which order Rust uses; that locals drop in reverse declaration order and struct fields in declaration order is quoted from the Rust Reference and RFC 1857 as background, not proved.
* Does not say that rustc's drop checker exploits struct-field drop order: in the toy `outlives` inspects the exact drop sequence `ord`, whereas the Rustonomicon's 'Drop Check' chapter shows a self-borrowing struct of which it says: 'You can try changing the order of fields or use a tuple instead of the struct, it'll still not compile.'
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).

**Prior art.**

* The Rust Reference, 'Destructors' (rust-lang/reference, src/destructors.md at commit 84dc36ff4712fad6829b6063cd4acbcaf5381708): the variables of a drop scope are dropped 'in reverse order of declaration' (line 59); the fields of a struct are dropped in declaration order (line 12).
* A. Ochagavía, RFC 1857 'Stabilize drop order' (PR rust-lang/rfcs#1857, opened 2017-01-19; text/1857-stabilize-drop-order.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4): stabilizes that struct, tuple and enum-variant fields are dropped in declaration order and slice and Vec elements first to last, and refers to local variables as destroyed in LIFO order.
* F. S. Klock II, RFC 769 'Sound Generic Drop' (PR rust-lang/rfcs#769, opened 2015-01-29; text/0769-sound-generic-drop.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4): states the drop-check rule (a lifetime 'a reachable from owned data whose type has a lifetime- or type-parametric Drop impl must strictly outlive the value, with parametricity-based exemptions), defines type ownership by recursive descent ('When does one type own another', line 380) and adds the special case 'If E is PhantomData<T>, then recurse on T' (line 453); partially superseded by RFC 1238 (2015-09-18).
* The Rustonomicon, 'Drop Check' (rust-lang/nomicon, src/dropck.md at commit 3c17036782395893fdc639185da1783065ec4571): 'For a generic type to soundly implement drop, its generics arguments must strictly outlive it.' (lines 128-129); obeying this rule 'is sufficient but not necessary to be sound' (lines 132-133); for a self-borrowing struct, 'You can try changing the order of fields or use a tuple instead of the struct, it'll still not compile.' (lines 113-114).

**Design question.** When is it sound to let a generic container's destructor run after some of its type parameters' lifetimes have ended, what does `#[may_dangle]` assert, and which plausible relaxations are not enough? (Soundness of a drop checker is stated relative to a drop order.)

#### R6 — The checker is incomplete

**Kind:** counterexample. **Tier:** T1 — The Rustonomicon notes that the strict rule is not necessary for soundness and the rustc-dev-guide shows a value-insensitive rejection; here a kernel-checked instance for the `may_dangle` checker.

Basis: execution (Lean kernel check), for the statement and for every Lean fact quoted in this card.

Basis: derived (modeling bridge), for any reading of this result as a statement about Rust: bridges B1 (checker shape) under "Modeling bridges" below; argued by correspondence of definitions, not proved.

**Plain claim.** In the toy model, the `may_dangle` checker is incomplete for the semantic property `DropSafe`: for the scope `pEmptyOwnedReader` (`let mut v = Vec::new(); let x = 0; v.push(D(&x)); v.clear();`, so that at scope exit an empty vector of type `Vec<D<&x>>` is declared before `x`) and the table `mkTbl vecMD`, with `MayDangleHonest`, `OwnsDeclared`, `GlueVisible`, `ValuesHaveTypes` and `LifetimesInScope` holding, the drops in reverse declaration order are safe, but `accepts` rejects the scope for that order.

**Statement.**

```lean
-- lean/ToyDropck/Results.lean:377-382
theorem accepts_incomplete_pEmptyOwnedReader :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ (∀ c, OwnsDeclared (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pEmptyOwnedReader ∧
      LifetimesInScope pEmptyOwnedReader ∧
      DropSafe (mkTbl vecMD) (revDeclOrder 2) pEmptyOwnedReader ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pEmptyOwnedReader = false := …
```

Hypothesis ledger: none (a statement about one concrete instance; every hypothesis of the related theorems is stated as a conjunct and proved).

**Depth:** definitional — Evaluation on one concrete instance (`decide`).

**Non-vacuity witness:** The concrete instance `pEmptyOwnedReader`, `mkTbl vecMD`, `revDeclOrder 2`. (`accepts_incomplete_pEmptyOwnedReader`)

**Non-claims.**

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* Shows one source of incompleteness (the checker sees types, not values); it does not classify all safe scopes that the checker rejects, and it does not say how much any type-based checker must reject.
* The soundness half of 'sound but incomplete' is R3 (`accepts_sound_of_mayDangleHonest_ownsDeclared_glueVisible`), a separate theorem.
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).

**Prior art.**

* The Rustonomicon, 'Drop Check' (rust-lang/nomicon, src/dropck.md at commit 3c17036782395893fdc639185da1783065ec4571): 'For a generic type to soundly implement drop, its generics arguments must strictly outlive it.' (lines 128-129); obeying this rule 'is sufficient but not necessary to be sound' (lines 132-133); for a self-borrowing struct, 'You can try changing the order of fields or use a tuple instead of the struct, it'll still not compile.' (lines 113-114).
* Rust Compiler Development Guide, 'Drop Check' (rust-lang/rustc-dev-guide, src/borrow-check/drop-check.md at commit 5ac3dc3cc93fcb4c04bdf0821dc17282ee614089): dropck_outlives requires the generic arguments of an explicit Drop impl to be live 'unless they are marked with #[may_dangle] in which case they are fully ignored' (line 125), recurses into all owned types, considers PhantomData<U> to own U and ManuallyDrop<U> not to own U (lines 132-133), and states 'We only rely on dropck_outlives if Ty::needs_drop for the containing local returned true' (line 138); its opening example is a Vec holding a reference to a shorter-lived String, and it shows that dropck still requires a local to be live after the local has been moved out.
* F. S. Klock II, RFC 1327 (PR rust-lang/rfcs#1327 'Dropck Eyepatch RFC.', opened 2015-10-19; text/1327-dropck-param-eyepatch.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4; feature dropck_eyepatch, tracking issue rust-lang/rust#34761): introduces per-parameter #[may_dangle]; on a type parameter 'the programmer is asserting the only uses of values of that type will be to move or drop them' (lines 250-252); its motivating examples are multi-parameter types (CheckedHashMap<K, V>, line 66; Vec<T, A: Allocator>, line 88), and its unresolved questions state 'We have not proven any previous variation of the rule sound' (lines 599-600).

**Design question.** When is it sound to let a generic container's destructor run after some of its type parameters' lifetimes have ended, what does `#[may_dangle]` assert, and which plausible relaxations are not enough? (One way a type-based drop checker can reject a safe scope.)

#### R7 — Inclusions among the checker policies

**Kind:** theorem. **Tier:** T0 — A monotonicity property of the toy's own checker definitions; that `#[may_dangle]` relaxes the strict rule is the design intent of RFC 1327.

Basis: execution (Lean kernel check), for the statement and for every Lean fact quoted in this card.

Basis: derived (modeling bridge), for any reading of this result as a statement about Rust: bridges B1 (checker shape) under "Modeling bridges" below; argued by correspondence of definitions, not proved.

**Plain claim.** In the toy model, for every implementation table `impls`, every drop order `ord` and every scope `p`, with no other hypotheses: (i) for every policy `pol`, if the strict checker `acceptsStrict` accepts `p` for `ord`, then `acceptsP pol` accepts it, in particular the `may_dangle` checker `accepts` does; (ii) if `acceptsP .deepNoDrop` accepts, `accepts` accepts; (iii) if `acceptsP .deepNoDrop` accepts, `acceptsP .headNoDrop` accepts; (iv) for every policy `pol`, if `acceptsP pol` accepts, `acceptsP .noUseSuffices` accepts.

**Statement.**

```lean
-- lean/ToyDropck/Results.lean:389-390
theorem acceptsP_of_acceptsStrict (pol : DanglePolicy) (impls : ImplTable) (ord : List Nat)
    (p : Prog) (h : acceptsStrict impls ord p = true) : acceptsP pol impls ord p = true := …
-- lean/ToyDropck/Results.lean:395-396
theorem accepts_of_acceptsStrict (impls : ImplTable) (ord : List Nat) (p : Prog)
    (h : acceptsStrict impls ord p = true) : accepts impls ord p = true := …
-- lean/ToyDropck/Results.lean:401-402
theorem accepts_of_acceptsP_deepNoDrop (impls : ImplTable) (ord : List Nat) (p : Prog)
    (h : acceptsP .deepNoDrop impls ord p = true) : accepts impls ord p = true := …
-- lean/ToyDropck/Results.lean:406-407
theorem acceptsP_headNoDrop_of_deepNoDrop (impls : ImplTable) (ord : List Nat) (p : Prog)
    (h : acceptsP .deepNoDrop impls ord p = true) : acceptsP .headNoDrop impls ord p = true := …
-- lean/ToyDropck/Results.lean:411-413
theorem acceptsP_noUseSuffices_of_acceptsP (pol : DanglePolicy) (impls : ImplTable)
    (ord : List Nat) (p : Prog) (h : acceptsP pol impls ord p = true) :
    acceptsP .noUseSuffices impls ord p = true := …
```

Unfolded (prose): For every `impls`, `ord`, `p`: acceptance by the checker with all `#[may_dangle]` erased implies acceptance under every policy; acceptance under `deepNoDrop` implies acceptance under `ownsRecurse` and under `headNoDrop`; acceptance under any policy implies acceptance under `noUseSuffices`.

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `h : acceptsStrict impls ord p = true` (in `acceptsP_of_acceptsStrict` and `accepts_of_acceptsStrict`) | the premise of inclusion (i) | tight: counterexample `accepts_of_acceptsStrict_counterexample_pOwnedReader` (witness class: the two-local scope `pOwnedReader` with `mkTbl vecMD`, rejected by the strict and by the `may_dangle` checker (conclusion of (i) fails for `pol = ownsRecurse`)) |
| `h : acceptsP .deepNoDrop impls ord p = true` (in `accepts_of_acceptsP_deepNoDrop` and `acceptsP_headNoDrop_of_deepNoDrop`) | the premise of inclusions (ii) and (iii) | tight: counterexample `deepNoDrop_inclusions_counterexample_pOwnedReader` (witness class: the two-local scope `pOwnedReader` with `mkTbl vecMD`, rejected by `deepNoDrop`, `ownsRecurse` and `headNoDrop`) |
| `h : acceptsP pol impls ord p = true` (in `acceptsP_noUseSuffices_of_acceptsP`) | the premise of inclusion (iv) | tight: counterexample `noUseSuffices_inclusion_counterexample_pReaderAfter` (witness class: the two-local scope `pReaderAfter` in declaration order with `mkTbl vecMD`, rejected by `ownsRecurse` and by `noUseSuffices`; for `pol = ownsRecurse`, both the premise and the conclusion fail) |

**Depth:** shallow — Induction on types (`dropckP_mono`, `dropckP_of_strip`, `dropckP_of_lifetimes_ok`, `dropckP_ownsRecurse_of_deepNoDrop`, `dropckP_headNoDrop_of_deepNoDrop`, `dropckP_noUseSuffices_of_dropckP`) lifted to the list of locals (`acceptsFrom_mono`).

**Non-vacuity witness:** With `mkTbl vecMD` and `revDeclOrder 2`: the strict checker accepts `pReferentFirst`; `deepNoDrop` and `ownsRecurse` accept `pContainer`. (`policy_inclusion_premises_hold`)

```lean
-- lean/ToyDropck/Results.lean:417-420
theorem policy_inclusion_premises_hold :
    acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pReferentFirst = true ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pContainer = true ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pContainer = true := …
```

**Counterexamples and companion facts (fully proved):**

```lean
-- lean/ToyDropck/Results.lean:428-439
theorem policy_separations_mkTbl_vecMD :
    (acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pContainer = false ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pContainer = true) ∧
    (accepts (mkTbl vecMD) (revDeclOrder 2) pNestedVec = true ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedVec = false ∧
      acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedVec = false) ∧
    (acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = true ∧
      acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pNestedReader = false) ∧
    (acceptsP .noUseSuffices (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = true ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false) := …
```

```lean
-- lean/ToyDropck/Results.lean:444-446
theorem accepts_of_acceptsStrict_counterexample_pOwnedReader :
    acceptsStrict (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false := …
```

```lean
-- lean/ToyDropck/Results.lean:451-454
theorem deepNoDrop_inclusions_counterexample_pOwnedReader :
    acceptsP .deepNoDrop (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      accepts (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false ∧
      acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = false := …
```

```lean
-- lean/ToyDropck/Results.lean:459-461
theorem noUseSuffices_inclusion_counterexample_pReaderAfter :
    accepts (mkTbl vecMD) (declOrder 2) pReaderAfter = false ∧
      acceptsP .noUseSuffices (mkTbl vecMD) (declOrder 2) pReaderAfter = false := …
```

**Non-claims.**

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* Says nothing about safety by itself: safety of accepted scopes is R1, R3, R4c and R8 under their hypotheses, and `noUseSuffices` and `headNoDrop` accept unsafe scopes (R4a, R4b).
* The converses of (i)-(iv) fail on the single table `mkTbl vecMD`, and `headNoDrop` and `ownsRecurse` are incomparable (`policy_separations_mkTbl_vecMD`).
* One-parameter model: every type mentions at most one lifetime (`lifetimes_length_le_one`), and the model gives a destructor two possible actions on its parameter: using its values (`usesT`) and dropping them (`dropsElems`). Hence, under `MayDangleHonest`, a `#[may_dangle]` `Drop` impl is interchangeable with a type without `Drop` impl, both for the `may_dangle` checker (`accepts_eq_acceptsStrict_eraseMayDangle`) and for the drop loop (`dropSafe_eraseMayDangle_iff`). The results say nothing about a destructor that keeps using another, non-eyepatched parameter or field while `T` dangles (the multi-parameter situation that motivates RFC 1327), and the toy cannot distinguish RFC 1327's per-parameter `#[may_dangle]` from RFC 1238's all-parameters `#[unsafe_destructor_blind_to_params]`.
* `ord` is an arbitrary list, not required to be a permutation of the locals: repeated and out-of-range indices are skipped, and locals that `ord` never names are never dropped (a leak), on which neither the checkers nor `DropSafe` impose anything (`accepts_ignores_undropped`, `dropSafe_ignores_undropped`). The results do not assert that every local is dropped.
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).

**Prior art.**

* F. S. Klock II, RFC 1327 (PR rust-lang/rfcs#1327 'Dropck Eyepatch RFC.', opened 2015-10-19; text/1327-dropck-param-eyepatch.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4; feature dropck_eyepatch, tracking issue rust-lang/rust#34761): introduces per-parameter #[may_dangle]; on a type parameter 'the programmer is asserting the only uses of values of that type will be to move or drop them' (lines 250-252); its motivating examples are multi-parameter types (CheckedHashMap<K, V>, line 66; Vec<T, A: Allocator>, line 88), and its unresolved questions state 'We have not proven any previous variation of the rule sound' (lines 599-600).
* F. S. Klock II, RFC 1238 'Nonparametric dropck' (PR rust-lang/rfcs#1238, opened 2015-08-05; text/1238-nonparametric-dropck.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4): drops RFC 769's reliance on parametricity ('cannot-assume-parametricity') and adds the unsafe attribute #[unsafe_destructor_blind_to_params] ('unguarded-escape-hatch'), which covers all type parameters of a destructor at once.

**Design question.** When is it sound to let a generic container's destructor run after some of its type parameters' lifetimes have ended, what does `#[may_dangle]` assert, and which plausible relaxations are not enough? (In the toy model, for every table, drop order and scope: if the checker accepts the scope with every `#[may_dangle]` annotation erased (`acceptsStrict`), then every policy accepts it with the annotations present; and how the relaxations compare.)

#### R8 — Every policy is sound when no `#[may_dangle]` impl drops its elements

**Kind:** theorem. **Tier:** T1 — RFC 1327's `RawVec<T>` destructor ('Frees the memory owned by the RawVec *without* trying to Drop its contents') describes this case informally, and the open, unmerged pull request rust-lang/rfcs#3417 proposes, without having been adopted, a `#[may_dangle(must_not_use)]` annotation for it; no mechanized statement was found.

Basis: execution (Lean kernel check), for the statement and for every Lean fact quoted in this card.

Basis: derived (modeling bridge), for any reading of this result as a statement about Rust: bridges B2 (`MayDangleHonest`), B3 (the split between `#[may_dangle]` impls that drop their elements and impls that do not) and B6 (`GlueVisible`) under "Modeling bridges" below; argued by correspondence of definitions, not proved.

**Plain claim.** In the toy model, for every checker policy `pol`, every implementation table satisfying `MayDangleHonest`, `MayDangleDropsNothing` (a Drop impl that claims `#[may_dangle]` on `T` does not drop its `T` elements) and `GlueVisible`, every drop order `ord`, and every scope `p` satisfying `ValuesHaveTypes` and `LifetimesInScope`: if `acceptsP pol` accepts `p` for `ord`, then `DropSafe impls ord p`: dropping the locals of `p` in the order `ord` never observes a dead or nonexistent local.

**Statement.**

```lean
-- lean/ToyDropck/Results.lean:471-476
theorem acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible (pol : DanglePolicy)
    (impls : ImplTable) (ord : List Nat) (p : Prog)
    (hmd : ∀ c, MayDangleHonest (impls c)) (hnodrop : ∀ c, MayDangleDropsNothing (impls c))
    (hglue : ∀ c, GlueVisible (impls c)) (hval : ValuesHaveTypes p)
    (hscope : LifetimesInScope p) (hacc : acceptsP pol impls ord p = true) :
    DropSafe impls ord p := …
```

Unfolded (prose): For every `pol`, `impls`, `ord`, `p`: if (i) no destructor claiming `#[may_dangle]` uses its elements, (ii) no such destructor drops its elements, (iii) every container without a `Drop` impl declares ownership of the elements its glue drops, (iv) `p`'s values have their declared types, (v) every lifetime in `p`'s declared types is a local of `p`, and (vi) the checker under `pol` accepts `p` for `ord`, then running the drops of `p` in the order `ord` never reads a dead or nonexistent local.

| Hypothesis | Purpose | Tightness |
| :--- | :--- | :--- |
| `hmd : ∀ c, MayDangleHonest (impls c)` | the unchecked `#[may_dangle]` promise must be true: the destructor does not use its T elements | tight: counterexample `dropsNothing_unsound_without_mayDangleHonest` (witness class: the two-local scope `pContainer` with a `may_dangle` container that drops nothing but uses its `&x` elements, under `noUseSuffices`) |
| `hnodrop : ∀ c, MayDangleDropsNothing (impls c)` | a `#[may_dangle]` impl that drops its elements runs their destructors, which `noUseSuffices` and `headNoDrop` do not check, and which `ownsRecurse` does not check when the impl does not declare ownership of `T` (`OwnsDeclared` is not assumed here); the policy `deepNoDrop` does not need this hypothesis (R4c, `acceptsP_deepNoDrop_sound_of_mayDangleHonest_glueVisible`) | tight: counterexample `dropsNothing_unsound_without_mayDangleDropsNothing` (witness class: the two-local scope `pOwnedReader` with the honest `may_dangle` Vec that drops its elements, under `noUseSuffices` (the instance of R4a); further counterexamples of the same form for the policy `headNoDrop` (`dropsNothing_unsound_without_mayDangleDropsNothing_headNoDrop`, the instance of R4b) and for the policy `ownsRecurse` (`dropsNothing_unsound_without_mayDangleDropsNothing_ownsRecurse`, `mkTbl vecNoOwn` on `pOwnedReader`)) |
| `hglue : ∀ c, GlueVisible (impls c)` | a type without Drop impl whose glue drops its T elements must declare that it owns T, so that the checker's ownership recursion sees those drops | tight: counterexample `dropsNothing_unsound_without_glueVisible` (witness class: the two-local scope `pOwnedReader` with a Drop-less container whose glue drops an undeclared element (a toy configuration chosen to violate `GlueVisible`), under `noUseSuffices`) |
| `hval : ValuesHaveTypes p` | the checker inspects declared types, never values; values must agree with them | tight: counterexample `dropsNothing_unsound_without_valuesHaveTypes` (witness class: a two-local scope whose local declared `int` holds `D(&x)`, under `noUseSuffices`) |
| `hscope : LifetimesInScope p` | the checker can judge a lifetime that names no local to outlive the drop (whenever it does not occur earlier in `ord`), while the runtime treats the nonexistent local as dead | tight: counterexample `dropsNothing_unsound_without_lifetimesInScope` (witness class: a one-local scope holding `D(&local5)`, under `noUseSuffices`) |
| `hacc : acceptsP pol impls ord p = true` | the checker verdict whose soundness is claimed | tight: counterexample `dropsNothing_rejects_unsafe_pReaderAfter` (witness class: the two-local scope `pReaderAfter` in declaration order, rejected by `noUseSuffices`) |

**Depth:** shallow — `dropSafe_of_acceptsP` in its third case: a `#[may_dangle]` impl that neither uses nor drops its elements does nothing observable with them, and every other branch of `dropckP` is the same for all policies. Equivalently, in this one-parameter model R8 follows from R1 and R7 (iv): under `MayDangleHonest` and `MayDangleDropsNothing`, replacing every `#[may_dangle]` impl by `plain` (`eraseMayDangleToPlain`) does not change `DropSafe` (`dropSafe_eraseMayDangleToPlain_iff`), preserves `GlueVisible` (`glueVisible_eraseMayDangleToPlain`), and turns acceptance by `noUseSuffices` into acceptance by the strict checker (`acceptsStrict_eraseMayDangleToPlain_of_noUseSuffices`); `acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible_via_acceptsStrict` proves R8's statement this way. The content lies in the definitions.

**Non-vacuity witness:** `pOwnedReader` with table `mkTbl rawVec` (a `may_dangle` handle that drops nothing), policy `noUseSuffices` and order `revDeclOrder 2` satisfies all hypotheses. (`dropsNothing_sound_hypotheses_hold_pOwnedReader_rawVec`)

```lean
-- lean/ToyDropck/Results.lean:481-485
theorem dropsNothing_sound_hypotheses_hold_pOwnedReader_rawVec :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .noUseSuffices (mkTbl rawVec) (revDeclOrder 2) pOwnedReader = true := …
```

**Counterexamples and companion facts (fully proved):**

```lean
-- lean/ToyDropck/Results.lean:490-495
theorem dropsNothing_unsound_without_mayDangleHonest :
    ¬ (∀ c, MayDangleHonest (mkTbl liarRaw c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl liarRaw c)) ∧
      (∀ c, GlueVisible (mkTbl liarRaw c)) ∧ ValuesHaveTypes pContainer ∧
      LifetimesInScope pContainer ∧
      acceptsP .noUseSuffices (mkTbl liarRaw) (revDeclOrder 2) pContainer = true ∧
      ¬ DropSafe (mkTbl liarRaw) (revDeclOrder 2) pContainer := …
```

```lean
-- lean/ToyDropck/Results.lean:503-508
theorem dropsNothing_unsound_without_mayDangleDropsNothing :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ ¬ (∀ c, MayDangleDropsNothing (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .noUseSuffices (mkTbl vecMD) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pOwnedReader := …
```

```lean
-- lean/ToyDropck/Results.lean:512-518
theorem dropsNothing_unsound_without_glueVisible :
    (∀ c, MayDangleHonest (mkTbl hiddenGlue c)) ∧
      (∀ c, MayDangleDropsNothing (mkTbl hiddenGlue c)) ∧
      ¬ (∀ c, GlueVisible (mkTbl hiddenGlue c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .noUseSuffices (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl hiddenGlue) (revDeclOrder 2) pOwnedReader := …
```

```lean
-- lean/ToyDropck/Results.lean:525-530
theorem dropsNothing_unsound_without_valuesHaveTypes :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ¬ ValuesHaveTypes pIllTyped ∧
      LifetimesInScope pIllTyped ∧
      acceptsP .noUseSuffices (mkTbl rawVec) (revDeclOrder 2) pIllTyped = true ∧
      ¬ DropSafe (mkTbl rawVec) (revDeclOrder 2) pIllTyped := …
```

```lean
-- lean/ToyDropck/Results.lean:534-539
theorem dropsNothing_unsound_without_lifetimesInScope :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ValuesHaveTypes pOutOfScopeReader ∧
      ¬ LifetimesInScope pOutOfScopeReader ∧
      acceptsP .noUseSuffices (mkTbl rawVec) (revDeclOrder 1) pOutOfScopeReader = true ∧
      ¬ DropSafe (mkTbl rawVec) (revDeclOrder 1) pOutOfScopeReader := …
```

```lean
-- lean/ToyDropck/Results.lean:544-549
theorem dropsNothing_rejects_unsafe_pReaderAfter :
    (∀ c, MayDangleHonest (mkTbl rawVec c)) ∧ (∀ c, MayDangleDropsNothing (mkTbl rawVec c)) ∧
      (∀ c, GlueVisible (mkTbl rawVec c)) ∧ ValuesHaveTypes pReaderAfter ∧
      LifetimesInScope pReaderAfter ∧
      acceptsP .noUseSuffices (mkTbl rawVec) (declOrder 2) pReaderAfter = false ∧
      ¬ DropSafe (mkTbl rawVec) (declOrder 2) pReaderAfter := …
```

```lean
-- lean/ToyDropck/Companions.lean:31-36
theorem dropsNothing_unsound_without_mayDangleDropsNothing_headNoDrop :
    (∀ c, MayDangleHonest (mkTbl vecMD c)) ∧ ¬ (∀ c, MayDangleDropsNothing (mkTbl vecMD c)) ∧
      (∀ c, GlueVisible (mkTbl vecMD c)) ∧ ValuesHaveTypes pNestedReader ∧
      LifetimesInScope pNestedReader ∧
      acceptsP .headNoDrop (mkTbl vecMD) (revDeclOrder 2) pNestedReader = true ∧
      ¬ DropSafe (mkTbl vecMD) (revDeclOrder 2) pNestedReader := …
```

```lean
-- lean/ToyDropck/Companions.lean:42-48
theorem dropsNothing_unsound_without_mayDangleDropsNothing_ownsRecurse :
    (∀ c, MayDangleHonest (mkTbl vecNoOwn c)) ∧
      ¬ (∀ c, MayDangleDropsNothing (mkTbl vecNoOwn c)) ∧
      (∀ c, GlueVisible (mkTbl vecNoOwn c)) ∧ ValuesHaveTypes pOwnedReader ∧
      LifetimesInScope pOwnedReader ∧
      acceptsP .ownsRecurse (mkTbl vecNoOwn) (revDeclOrder 2) pOwnedReader = true ∧
      ¬ DropSafe (mkTbl vecNoOwn) (revDeclOrder 2) pOwnedReader := …
```

R8 from R1 and R7 (iv), through `eraseMayDangleToPlain`:

```lean
-- lean/ToyDropck/Companions.lean:58-59
def eraseMayDangleToPlain (impls : ImplTable) : ImplTable := fun c =>
  if (impls c).beh.hasDrop && (impls c).decl.mayDangle then plain else impls c
```

```lean
-- lean/ToyDropck/Companions.lean:114-117
theorem dropSafe_eraseMayDangleToPlain_iff {impls : ImplTable}
    (hmd : ∀ c, MayDangleHonest (impls c)) (hnodrop : ∀ c, MayDangleDropsNothing (impls c))
    (ord : List Nat) (p : Prog) :
    DropSafe (eraseMayDangleToPlain impls) ord p ↔ DropSafe impls ord p := …
```

```lean
-- lean/ToyDropck/Companions.lean:122-123
theorem glueVisible_eraseMayDangleToPlain {impls : ImplTable}
    (hglue : ∀ c, GlueVisible (impls c)) : ∀ c, GlueVisible (eraseMayDangleToPlain impls c) := …
```

```lean
-- lean/ToyDropck/Companions.lean:132-134
theorem acceptsStrict_eraseMayDangleToPlain_of_noUseSuffices (impls : ImplTable)
    (ord : List Nat) (p : Prog) (h : acceptsP .noUseSuffices impls ord p = true) :
    acceptsStrict (eraseMayDangleToPlain impls) ord p = true := …
```

```lean
-- lean/ToyDropck/Companions.lean:159-164
theorem acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible_via_acceptsStrict
    (pol : DanglePolicy) (impls : ImplTable) (ord : List Nat) (p : Prog)
    (hmd : ∀ c, MayDangleHonest (impls c)) (hnodrop : ∀ c, MayDangleDropsNothing (impls c))
    (hglue : ∀ c, GlueVisible (impls c)) (hval : ValuesHaveTypes p)
    (hscope : LifetimesInScope p) (hacc : acceptsP pol impls ord p = true) :
    DropSafe impls ord p := …
```

**Non-claims.**

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* `MayDangleDropsNothing` excludes every `#[may_dangle]` container that drops its elements, such as `vecMD`; for those, the toy proves the ownership recursion (R3) and the deep check (R4c) sound under their respective hypotheses, and refutes `noUseSuffices` (R4a) and `headNoDrop` (R4b).
* In the toy, a container satisfying `MayDangleDropsNothing` never drops its elements at all, so their destructors never run (the elements are leaked); the toy does not model another path through which such elements would be dropped later.
* One-parameter model: every type mentions at most one lifetime (`lifetimes_length_le_one`), and the model gives a destructor two possible actions on its parameter: using its values (`usesT`) and dropping them (`dropsElems`). Hence, under `MayDangleHonest`, a `#[may_dangle]` `Drop` impl is interchangeable with a type without `Drop` impl, both for the `may_dangle` checker (`accepts_eq_acceptsStrict_eraseMayDangle`) and for the drop loop (`dropSafe_eraseMayDangle_iff`). The results say nothing about a destructor that keeps using another, non-eyepatched parameter or field while `T` dangles (the multi-parameter situation that motivates RFC 1327), and the toy cannot distinguish RFC 1327's per-parameter `#[may_dangle]` from RFC 1238's all-parameters `#[unsafe_destructor_blind_to_params]`.
* A local counts as dead from the moment its own drop begins (`runDrops` drops the value with the local already in the dead set), so a destructor that observes its own local through a stored reference is undefined behaviour in the toy (`dropSafe_neg_self`). This is a modeling choice. Under it, replacing `outlives` by its non-strict variant `outlivesNonStrict` (without `j != i`) makes the per-local judgment accept an unsafe scope (`nonStrictOutlives_accepts_unsafe_pSelfReader`). Aliasing rules for `&mut self` are not modelled.
* `observe` recurses through nested container values and, on a reference `ref j`, checks that local `j` is live without reading local `j`'s own value. `Ty.ref j` records the referent local and not the referent's type, so no condition relates the lifetimes of a reference to a reference. Consequently a destructor that holds a reference to a live local whose own value is a reference to a dead local is accepted by both checkers and is `DropSafe` in the toy (`pRefToRef_accepted_and_dropSafe`); soundness under a semantics that dereferences transitively is not addressed (not proved either way).
* References (`Val.ref j`) always target top-level locals, and `dropAll` keeps the live set fixed while the elements of one value are dropped. References between elements of the same container (such as the cyclic structures discussed in RFC 1238) and fields that refer to earlier-dropped fields of the same value are not modelled; the results neither validate nor rule them out.
* `ord` is an arbitrary list, not required to be a permutation of the locals: repeated and out-of-range indices are skipped, and locals that `ord` never names are never dropped (a leak), on which neither the checkers nor `DropSafe` impose anything (`accepts_ignores_undropped`, `dropSafe_ignores_undropped`). The results do not assert that every local is dropped.
* `GlueVisible` is a toy-level condition on the table; whether Rust's drop glue satisfies an analogue of it is a separate derived (modeling bridge) claim (B6), not a theorem here.
* Soundness is relative to the drop order: the checker is given the same `ord` that the drop loop executes (see R5, `dropOrder_matters_pReaderAfter`).
* The table conditions quantify over every container in the table, including containers that `p` never mentions; whether conditions restricted to the containers a scope mentions suffice is not proved here.
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).
* Undefined behaviour in the toy arises from observing a dead or nonexistent local and from nothing else; a destructor's use of its elements is all-or-nothing (`usesT`).

**Prior art.**

* F. S. Klock II, RFC 1327 (PR rust-lang/rfcs#1327 'Dropck Eyepatch RFC.', opened 2015-10-19; text/1327-dropck-param-eyepatch.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4; feature dropck_eyepatch, tracking issue rust-lang/rust#34761): introduces per-parameter #[may_dangle]; on a type parameter 'the programmer is asserting the only uses of values of that type will be to move or drop them' (lines 250-252); its motivating examples are multi-parameter types (CheckedHashMap<K, V>, line 66; Vec<T, A: Allocator>, line 88), and its unresolved questions state 'We have not proven any previous variation of the rule sound' (lines 599-600).
* lcnr, PR rust-lang/rfcs#3417 'improve #[may_dangle] for type parameters' (https://github.com/rust-lang/rfcs/pull/3417, opened 2023-04-17; an open, unmerged pull request as of 2026-11-21, so a proposal rather than an accepted RFC or a description of current Rust; text/3417-dropck-eyepatch-v3.md at the pull request's head commit 8f8303a6ac0fb86b8611b91d7047bd72b825cbe9 in the contributor fork lcnr/rfcs): proposes #[may_dangle(droppable)] (the impl recursively drops values of T) and #[may_dangle(must_not_use)] (it does not), and that dropck ignore PhantomData; the split parallels the toy's distinction between #[may_dangle] impls that drop their elements (R3, R4a) and impls that do not (R8). It is cited as design discussion; no definition, result or modeling bridge relies on it.
* Rust Compiler Development Guide, 'Drop Check' (rust-lang/rustc-dev-guide, src/borrow-check/drop-check.md at commit 5ac3dc3cc93fcb4c04bdf0821dc17282ee614089): dropck_outlives requires the generic arguments of an explicit Drop impl to be live 'unless they are marked with #[may_dangle] in which case they are fully ignored' (line 125), recurses into all owned types, considers PhantomData<U> to own U and ManuallyDrop<U> not to own U (lines 132-133), and states 'We only rely on dropck_outlives if Ty::needs_drop for the containing local returned true' (line 138); its opening example is a Vec holding a reference to a shorter-lived String, and it shows that dropck still requires a local to be live after the local has been moved out.
* Novelty search: web searches for mechanized soundness proofs of dropck or #[may_dangle]; RustBelt Section 9 (Conclusion); the full texts of Oxide (A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, 'Oxide: The Essence of Rust', arXiv:1903.00982) and RefinedRust (L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, PACMPL 8(PLDI), 2024, doi:10.1145/3656422) contain neither 'dropck' nor 'may_dangle'; bibliographic records of D. J. Pearce, 'A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust' (ACM TOPLAS 43(1), 2021, doi:10.1145/3443420), and RustHornBelt (Y. Matsushita, X. Denis, J.-H. Jourdan, D. Dreyer, PLDI 2022, doi:10.1145/3519939.3523704) were checked at the DOI registry but their full texts were not searched; Patina (E. C. Reed, technical report UW-CSE-15-03-02, 2015) is listed from a search summary and was not verified at the source; region-based memory management (M. Tofte, J.-P. Talpin, Information and Computation 132(2):109-176, 1997, doi:10.1006/inco.1996.2613) deallocates whole regions without per-object destructors. No mechanized treatment of dropck or #[may_dangle] was found; tier T1 is claimed, not T3.

**Design question.** When is it sound to let a generic container's destructor run after some of its type parameters' lifetimes have ended, what does `#[may_dangle]` assert, and which plausible relaxations are not enough? (In the toy model: for implementation tables satisfying `MayDangleHonest`, `MayDangleDropsNothing` (no `#[may_dangle]` impl drops its elements) and `GlueVisible`, and for scopes satisfying `ValuesHaveTypes` and `LifetimesInScope`, acceptance for a drop order under every policy, including `noUseSuffices`, which checks nothing about the drop of the eyepatched parameter's values, implies `DropSafe` for that order.)

### Modeling bridges (`derived (modeling bridge)`; prose, not proved)

Basis: derived (modeling bridge). Each item argues by correspondence of definitions with the cited documentation; none is a theorem.

* B1. *The `ownsRecurse` checker follows the shape of the RFC 1327 rule with RFC 769's ownership recursion.* RFC 769 defines when a type owns data of another type by recursive descent, including the special case `PhantomData<T>`; RFC 1238 removes RFC 769's parametricity reasoning in favour of an unsafe attribute; RFC 1327 replaces that attribute by per-parameter `#[may_dangle]`, whose eyepatched parameters are replaced by `'static` / `()` before asking whether owned data can reach a reference of lifetime `'a`. `dropckP .ownsRecurse` mirrors this for one-parameter containers: the strict branch requires every lifetime in `t` to strictly outlive the drop; the `may_dangle` branch places no requirement on `T`'s lifetimes but still recurses into `T` when it is declared owned. The rustc-dev-guide describes the same shape for today's `dropck_outlives`. Gaps: rustc works on regions and, since RFC 2094, on drop-liveness rather than one fixed drop order; lifetime parameters and multi-parameter impls are absent, so RFC 1327 and RFC 1238 cannot be told apart ("What the one-parameter model can express" under Findings); rustc gates `dropck_outlives` on `Ty::needs_drop`.
* B2. *`MayDangleHonest` models the `#[may_dangle] T` assertion.* RFC 1327: "the programmer is asserting the only uses of values of that type will be to move or drop them". The toy's `usesT` collapses all non-drop uses into one bit.
* B3. *`OwnsDeclared` models the `PhantomData<T>` condition.* The Rustonomicon (PhantomData chapter) explains that the standard library's `Vec<T>` keeps `_owns_T: PhantomData<T>` because `#[may_dangle] T` is sound "provided it not be involved in some transitive drop glue", and gives the `PrintOnDrop<'s>` example, which `accepts_unsound_without_ownsDeclared` and R4a model; rust-lang/rust#99408 (https://github.com/rust-lang/rust/issues/99408, 'Too lenient `#[may_dangle]` on `BTreeMap`; misses `PhantomData` for dropck') reports a standard-library type whose `#[may_dangle]` impl lacked the `PhantomData` for dropck. The toy's split between `#[may_dangle]` impls that drop their `T` elements (`dropsElems = true`; R3, R4a) and impls that do not (`MayDangleDropsNothing`; R8) corresponds to the difference between the standard library's `Vec<T>`, whose destructor 'does have to transitively drop each `T` item when it has drop glue' (Rustonomicon, 'PhantomData', lines 186-187), and RFC 1327's `RawVec<T>` destructor, which 'Frees the memory owned by the RawVec *without* trying to Drop its contents' (line 47). The open, unmerged pull request rust-lang/rfcs#3417 (https://github.com/rust-lang/rfcs/pull/3417) proposes the same split as `#[may_dangle(droppable)]` / `#[may_dangle(must_not_use)]`; it is a proposal, not adopted Rust semantics, and this bridge does not rely on it.
* B4. *Reverse declaration order.* The Rust Reference states that a drop scope's variables are dropped in reverse order of declaration and that struct fields are dropped in declaration order; RFC 1857 stabilized the field and element orders. R5 shows that a checker's verdict is meaningful relative to the order it assumes; rustc's drop checker does not use field order to accept self-borrowing structs (Rustonomicon, 'Drop Check').
* B5. *Strict rule.* The Rustonomicon's "Big Rule" (generic arguments must strictly outlive) corresponds to `acceptsStrict`; its remark that the rule is sufficient but not necessary is mirrored by R1 and R2.
* B6. *`GlueVisible`.* In Rust, drop glue drops the fields a type owns, and dropck sees those fields; the rustc-dev-guide lists `ManuallyDrop<U>` as not owning `U`, and union fields are not dropped (RFC 1857: '`union` types never drop their contents', line 154). The toy's `GlueVisible` approximates the fact that drop glue of a `Drop`-less type is visible to dropck; its tightness counterexamples use `hiddenGlue`, a toy configuration chosen to violate it.
* B7. *A local is dead during its own drop.* The toy forbids observing a local through a stored reference once that local's drop has begun. In Rust, `Drop::drop` receives `&mut self`, and a destructor first calls `Drop::drop` and then runs the destructors of the fields (The Rust Reference, 'Destructors'), which is the intuition behind the strict (`j != i`) outlives requirement; the toy does not model the aliasing rules themselves.
None of B1–B7 is proved; each is an argument by correspondence of definitions.

### Auxiliary lemmas cited by name

```lean
-- lean/ToyDropck/Lemmas.lean:292-293
theorem dropSafe_stripDangle (impls : ImplTable) (ord : List Nat) (p : Prog) :
    DropSafe (stripDangle impls) ord p ↔ DropSafe impls ord p := …
```

```lean
-- lean/ToyDropck/Lemmas.lean:273-278
theorem dropSafe_of_acceptsP {pol : DanglePolicy} {impls : ImplTable} {ord : List Nat} {p : Prog}
    (hpol : (pol = .ownsRecurse ∧ ∀ c, OwnsDeclared (impls c)) ∨ pol = .deepNoDrop ∨
      (∀ c, MayDangleDropsNothing (impls c)))
    (hmd : ∀ c, MayDangleHonest (impls c)) (hglue : ∀ c, GlueVisible (impls c))
    (hval : ValuesHaveTypes p) (hscope : LifetimesInScope p)
    (hacc : acceptsP pol impls ord p = true) : DropSafe impls ord p := …
```

```lean
-- lean/ToyDropck/Lemmas.lean:100-106
theorem dropVal_of_dropckP {pol : DanglePolicy} {impls : ImplTable} {ok L : Nat → Bool} {n : Nat}
    (hpol : (pol = .ownsRecurse ∧ ∀ c, OwnsDeclared (impls c)) ∨ pol = .deepNoDrop ∨
      (∀ c, MayDangleDropsNothing (impls c)))
    (hmd : ∀ c, MayDangleHonest (impls c)) (hglue : ∀ c, GlueVisible (impls c))
    (hokL : ∀ j, j < n → ok j = true → L j = true) :
    ∀ (t : Ty) (v : Val), hasTy v t = true → (∀ j ∈ lifetimes t, j < n) →
      dropckP pol impls ok t = true → dropVal (behOf impls) L v = true
  -- (proof by structural recursion, elided)
```

```lean
-- lean/ToyDropck/Lemmas.lean:205-211
theorem runDrops_of_each {beh : Nat → DropBehavior} {p : Prog} {ord : List Nat}
    (hone : ∀ (k : Nat) (t : Ty) (v : Val) (dead : List Nat), p.locals[k]? = some (t, v) →
      ord.contains k = true →
      (∀ j, outlives ord k j = true → j < p.locals.length → j ∉ k :: dead) →
      dropVal beh (live p.locals.length (k :: dead)) v = true) :
    ∀ (ks pre dead : List Nat), ord = pre ++ ks →
      (∀ j, j ∈ dead ↔ (j ∈ pre ∧ j < p.locals.length)) → runDrops beh p ks dead = true
  -- (proof by structural recursion, elided)
```

```lean
-- lean/ToyDropck/Lemmas.lean:63-65
theorem dropVal_of_lifetimes_live {beh : Nat → DropBehavior} {L : Nat → Bool} :
    ∀ (t : Ty) (v : Val), hasTy v t = true → (∀ j ∈ lifetimes t, L j = true) →
      dropVal beh L v = true
  -- (proof by structural recursion, elided)
```

```lean
-- lean/ToyDropck/Lemmas.lean:82-84
theorem dropVal_of_deepHasNoDrop {impls : ImplTable} {L : Nat → Bool} :
    ∀ (t : Ty) (v : Val), hasTy v t = true → deepHasNoDrop impls t = true →
      dropVal (behOf impls) L v = true
  -- (proof by structural recursion, elided)
```

```lean
-- lean/ToyDropck/Inclusions.lean:30-35
theorem dropckP_mono {p q : DanglePolicy} {impls : ImplTable} {ok : Nat → Bool}
    (hbranch : ∀ (c : Nat) (t : Ty), (impls c).beh.hasDrop = true →
      (impls c).decl.mayDangle = true →
      (dropckP p impls ok t = true → dropckP q impls ok t = true) →
      dropckP p impls ok (.app c t) = true → dropckP q impls ok (.app c t) = true) :
    ∀ t : Ty, dropckP p impls ok t = true → dropckP q impls ok t = true
  -- (proof by structural recursion, elided)
```

```lean
-- lean/ToyDropck/Inclusions.lean:49-53
theorem acceptsFrom_mono {p q : DanglePolicy} {impls impls' : ImplTable} {ord : List Nat}
    (h : ∀ (i : Nat) (t : Ty), dropckP p impls (outlives ord i) t = true →
      dropckP q impls' (outlives ord i) t = true) :
    ∀ (l : List (Ty × Val)) (i : Nat), acceptsFrom p impls ord i l = true →
      acceptsFrom q impls' ord i l = true
  -- (proof by structural recursion, elided)
```

```lean
-- lean/ToyDropck/Inclusions.lean:60-61
theorem dropckP_of_strip (pol : DanglePolicy) {impls : ImplTable} {ok : Nat → Bool} :
    ∀ t : Ty, dropckP .ownsRecurse (stripDangle impls) ok t = true → dropckP pol impls ok t = true
  -- (proof by structural recursion, elided)
```

```lean
-- lean/ToyDropck/Inclusions.lean:103-104
theorem dropckP_ownsRecurse_of_deepNoDrop {impls : ImplTable} {ok : Nat → Bool} :
    ∀ t : Ty, dropckP .deepNoDrop impls ok t = true → dropckP .ownsRecurse impls ok t = true := …
```

```lean
-- lean/ToyDropck/Inclusions.lean:112-113
theorem dropckP_headNoDrop_of_deepNoDrop {impls : ImplTable} {ok : Nat → Bool} :
    ∀ t : Ty, dropckP .deepNoDrop impls ok t = true → dropckP .headNoDrop impls ok t = true := …
```

```lean
-- lean/ToyDropck/Inclusions.lean:119-121
theorem dropckP_noUseSuffices_of_dropckP (pol : DanglePolicy) {impls : ImplTable}
    {ok : Nat → Bool} :
    ∀ t : Ty, dropckP pol impls ok t = true → dropckP .noUseSuffices impls ok t = true := …
```

## Boundaries

### Non-claims (all results)

Each card under Findings repeats the non-claims that apply to it.

* These are statements about the toy model; they neither establish nor refute the corresponding claims about rustc's drop checker, `#[may_dangle]` or the Rust standard library. Model–system relation: none proved.
* Not modelled: borrow checking and region inference (a lifetime is identified with its referent local and a reference type carries it exactly, without subtyping); lifetime parameters and `#[may_dangle]` on them; `Drop` impls with several type parameters or with trait bounds; trait objects; specialization; panics or unwinding during drops; moves and partial moves; double drops; use of moved values; temporaries; interior mutability and writes that change liveness; struct-field drop order (drop orders are arbitrary lists `ord` of local indices).
* Undefined behaviour in the toy arises from observing a dead or nonexistent local and from nothing else; a destructor's use of its elements is all-or-nothing (`usesT`).
* One-parameter model: every type mentions at most one lifetime (`lifetimes_length_le_one`), and the model gives a destructor two possible actions on its parameter: using its values (`usesT`) and dropping them (`dropsElems`). Hence, under `MayDangleHonest`, a `#[may_dangle]` `Drop` impl is interchangeable with a type without `Drop` impl, both for the `may_dangle` checker (`accepts_eq_acceptsStrict_eraseMayDangle`) and for the drop loop (`dropSafe_eraseMayDangle_iff`). The results say nothing about a destructor that keeps using another, non-eyepatched parameter or field while `T` dangles (the multi-parameter situation that motivates RFC 1327), and the toy cannot distinguish RFC 1327's per-parameter `#[may_dangle]` from RFC 1238's all-parameters `#[unsafe_destructor_blind_to_params]`.
* `observe` recurses through nested container values and, on a reference `ref j`, checks that local `j` is live without reading local `j`'s own value. `Ty.ref j` records the referent local and not the referent's type, so no condition relates the lifetimes of a reference to a reference. Consequently a destructor that holds a reference to a live local whose own value is a reference to a dead local is accepted by both checkers and is `DropSafe` in the toy (`pRefToRef_accepted_and_dropSafe`); soundness under a semantics that dereferences transitively is not addressed (not proved either way).
* References (`Val.ref j`) always target top-level locals, and `dropAll` keeps the live set fixed while the elements of one value are dropped. References between elements of the same container (such as the cyclic structures discussed in RFC 1238) and fields that refer to earlier-dropped fields of the same value are not modelled; the results neither validate nor rule them out.
* `ord` is an arbitrary list, not required to be a permutation of the locals: repeated and out-of-range indices are skipped, and locals that `ord` never names are never dropped (a leak), on which neither the checkers nor `DropSafe` impose anything (`accepts_ignores_undropped`, `dropSafe_ignores_undropped`). The results do not assert that every local is dropped.
* A local counts as dead from the moment its own drop begins (`runDrops` drops the value with the local already in the dead set), so a destructor that observes its own local through a stored reference is undefined behaviour in the toy (`dropSafe_neg_self`). This is a modeling choice. Under it, replacing `outlives` by its non-strict variant `outlivesNonStrict` (without `j != i`) makes the per-local judgment accept an unsafe scope (`nonStrictOutlives_accepts_unsafe_pSelfReader`). Aliasing rules for `&mut self` are not modelled.
* Soundness is relative to the drop order: the checker is given the same `ord` that the drop loop executes (see R5, `dropOrder_matters_pReaderAfter`).
* The table conditions quantify over every container in the table, including containers that `p` never mentions; whether conditions restricted to the containers a scope mentions suffice is not proved here.
* `GlueVisible` is a toy-level condition on the table; whether Rust's drop glue satisfies an analogue of it is a separate derived (modeling bridge) claim (B6), not a theorem here.
* According to the rustc-dev-guide ('Drop Check'), rustc consults `dropck_outlives` for a local when `Ty::needs_drop` holds for the local's type ('We only rely on `dropck_outlives` if `Ty::needs_drop` for the containing local returned `true`'), and treats `PhantomData<U>` as owning `U` in `dropck_outlives` but not in `Ty::needs_drop`; `dropckP` has no such gate and always recurses into a declared-owned parameter. `PhantomData<T>` also affects variance and auto traits, which are not modelled.
* The names `headNoDrop` and `deepNoDrop` refer to the toy tests `headHasNoDrop` and `deepHasNoDrop`, not to a Rust trait bound: in Rust, whether a type has a `Drop` impl is a property of its outermost type constructor, while whether it has drop glue (`core::mem::needs_drop`) also depends on its fields. `deepHasNoDrop` inspects every type constructor in `T`, including ones whose drop does nothing, so the `deepNoDrop` checker rejects the safe scope `pManuallyDropReader` (`deepNoDrop_rejects_accepted_safe_pManuallyDropReader`).
* Counterexample results (R2, R4a, R4b, R5, R6) are single concrete instances; they refute the universal statements they target and say nothing about frequency.

### Escape hatches

* The counterexamples R4a and R4b rely on the `#[may_dangle]` container dropping its elements (`dropsElems = true` in `vecMD`). When no `#[may_dangle]` impl drops its elements (`MayDangleDropsNothing`) and `MayDangleHonest` and `GlueVisible` hold, every policy, including `noUseSuffices` and `headNoDrop`, is sound in the toy for scopes satisfying `ValuesHaveTypes` and `LifetimesInScope` (R8, `acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible`); on the scopes of R4a and R4b with `mkTbl rawVec`, the relaxed checkers accept and the drops are safe (`noUseSuffices_accepts_safe_pOwnedReader_rawVec`, `headNoDrop_accepts_safe_pNestedReader_rawVec`).
* The checker refuted by R4b (`headNoDrop_accepts_unsafe_pNestedReader`) tests the outermost type constructor of `T` in place of the ownership recursion; testing every type constructor of `T` (`deepNoDrop`) is sound under `MayDangleHonest` and `GlueVisible`, without `OwnsDeclared`, for scopes satisfying `ValuesHaveTypes` and `LifetimesInScope` (R4c, `acceptsP_deepNoDrop_sound_of_mayDangleHonest_glueVisible`).
* Each hypothesis of the soundness theorems R1, R3, R4c and R8 is tight: for each, a concrete instance satisfies all the other hypotheses, violates that one, and is not `DropSafe` (the counterexamples named in each ledger; for the acceptance hypothesis `hacc` the instance is an unsafe scope that the checker rejects). For instance, without `OwnsDeclared` the `may_dangle` checker `accepts` accepts an unsafe scope (`accepts_unsound_without_ownsDeclared`).

### Hypotheses with `unknown` tightness

None. Every hypothesis of R1, R3, R4c, R7 and R8 is marked `tight`, with a proved counterexample stating that all other hypotheses hold and the conclusion fails; the counterexample results R2, R4a, R4b, R5 and R6 have no hypotheses.

### Attractive stronger conclusions that are not established

* That rustc's drop checker (any version) is sound, or that it implements `accepts`: not established (Model–system relation: none proved).
* That the standard library's `#[may_dangle]` impls satisfy `MayDangleHonest`, `OwnsDeclared` or `MayDangleDropsNothing`: not established; bridges B2 and B3 are prose.
* That honesty conditions restricted to the containers a scope mentions suffice for soundness: not proved here.
* That the soundness results extend to `Drop` impls with several type parameters, to lifetime parameters, to struct-field drop order, or to a semantics that dereferences references transitively: not addressed (not proved either way).
* How many safe scopes `accepts` rejects, or whether every type-based checker must reject the scope of R6: not addressed (not proved either way).

### Disproved or dropped statements

None. Every statement in this package is proved as stated.

## Evidence

### Kernel-check record

Basis: execution (Lean kernel check), observed 2026-11-21 with `leanprover/lean4:v4.34.1` (tag commit `5045d0056413266e57c625dcd7c365b10e377c52`). Names are in the namespace `Toy.Dropck`. "Axioms" is the output of `Lean.collectAxioms` (what `#print axioms` prints). The statement hash is the SHA-256 of the `repr` of the declaration's type; the closure hash is the SHA-256 of the sorted, newline-joined list of the types and values of every package-local constant reachable from the statement (theorem bodies excluded), as recomputed by `support/revalidate.py`. `audit/axioms.json` records the axioms of all 466 declarations of the library (union: `Quot.sound`, `propext`); `audit/statements.json` records the hashes of all 212 names referenced by `results.json`, including the definitions and auxiliary lemmas. The table lists every theorem that a card uses as a result, non-vacuity witness, positive control or counterexample.

| Name | Role | Axioms | Statement SHA-256 | Closure SHA-256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `acceptsStrict_sound_of_glueVisible` | R1 result | Quot.sound, propext | `c1e68e1830538d3abbd3ebef8ecd49e6ec46ee9a22b335798cb8ba5d2fbc6e48` | `1d8217d54a7883192989567dabfbf44c8092342f5aa5ae73bf2ec9c5e0c9f43f` (91) |
| `acceptsStrict_sound_hypotheses_hold_pReferentFirst` | R1 non-vacuity | propext | `27103097c9e021a3a257306250331dc3e4aefea8e22e8ad8b88b5c5da96e1f8a` | `5169a8c1e63a4925cf232f67ce42fc737ae5c740e2de519e083841d8a4b7e824` (81) |
| `acceptsStrict_unsound_without_glueVisible` | R1 counterexample (`hglue`) | propext | `4f089da574a3749063a2e399ec1746972d369e6975957a84212846cc7c2f45f9` | `790237590194c9c8c6820c5e57bd23b7827fff8a906edd86966d358c1f6cfef8` (99) |
| `acceptsStrict_unsound_without_valuesHaveTypes` | R1 counterexample (`hval`) | propext | `e162a2c8566874536a662c056f53bff582f0ed9762504b79e0f04a7a74969821` | `00c7c69667ac8c4af46a51860a476b30dc9b515c1f814fd25539cbdb5f458477` (99) |
| `acceptsStrict_unsound_without_lifetimesInScope` | R1 counterexample (`hscope`) | propext | `acdf523dbbbd547ab7463c28a23c92b4b23fe173fec941d54ee80cb2c8460efb` | `1db682431cd0f75178d0ea351184c3c359954677d1ba81670e23aa8bee564076` (99) |
| `acceptsStrict_rejects_unsafe_pOwnedReader` | R1 counterexample (`hacc`) | propext | `9f731d7781c6d12e0577645ddaf8b3ffb3e30be53d7b6664586a10b4036a6f37` | `0200f7b767e4b5088db1132191586e38527e21d3b64aa37443b95cb8103609f4` (99) |
| `acceptsStrict_rejects_dropSafe_pContainer` | R2 result; R2 non-vacuity | Quot.sound, propext | `57f939d6202fd6d6afcc8d42c65472d7024c4c6f11c72d8e3ce11657ebc7a1f8` | `3d3a71194aaf64a06a05acd7053b823847cf94237cc126f082b36d8885a878b3` (102) |
| `accepts_sound_of_mayDangleHonest_ownsDeclared_glueVisible` | R3 result | Quot.sound, propext | `21f76482f58b95096498de5b2586f94570b2f64b9fd6e89c39e0a141a79627e6` | `c0d143f94f47354c9e32fddac3fd1fb856b5a00593adf67a613e20b913848b67` (91) |
| `accepts_sound_hypotheses_hold_pContainer` | R3 non-vacuity | propext | `4ac55ccc012291b3ee36a32f6b3338fb1a21b008b28a5756b4eb9a2cf46ce508` | `7161b66824cc0b1c89dd5a2310b3dc331f1487fbf9a1512c530b9a5ef1f9585b` (82) |
| `accepts_unsound_without_mayDangleHonest` | R3 counterexample (`hmd`) | propext | `b5d0709a87fe6163dcdd175745b2f18eb8b54058543114be1cc7ba82ca1524fd` | `107d76c041851d7457b88c2b7d9e2c9bb0f3100e6781cde019522dc94a5096c7` (99) |
| `accepts_unsound_without_ownsDeclared` | R3 counterexample (`hown`) | propext | `309a54b110a4b362eb32cef41c10d03b4467964c1a14440ee47ed180d9e8a17d` | `416166e4d4d14fdfd033e4a06a9ac6f242e7931d37f97a24db6bf5f3b6ca9d8a` (99) |
| `accepts_unsound_without_glueVisible` | R3 counterexample (`hglue`) | propext | `ad1ddd2497987903bc5f743deea5c6c885a4afe31aeef558ede6025ecc934129` | `13c81b1b5a509b264cea32c2567ed9c91ce89581123a550fe80dcce308e6a1c1` (99) |
| `accepts_unsound_without_valuesHaveTypes` | R3 counterexample (`hval`) | propext | `3b343e208ed224268e7913c84ba02c9842bdbfab24c7d42a421a0d129255d5c2` | `a50147c40966a7ccabc4f27796be4fc01eca151b7dd6e0396b9c5b1b392a302b` (99) |
| `accepts_unsound_without_lifetimesInScope` | R3 counterexample (`hscope`) | propext | `15f6562de16b22e71891eafc4f496b23f14817730beb6956693b00e9b9754af8` | `a3aac1af9e101c5ed7c48c18b04deaa06af4c0a1aa6fce5b7cfe290f5a884786` (99) |
| `accepts_rejects_unsafe_pOwnedReader` | R3 counterexample (`hacc`) | propext | `baf0937f4b95b588121c337eba3d9d0cb5323fb59edf7b856597e774cdc1eb37` | `3840013fd3411e2a5c2961e8aa3641e13189fbef608c37cf8beeb4ed75215cec` (99) |
| `noUseSuffices_accepts_unsafe_pOwnedReader` | R4a result; R4a non-vacuity | propext | `0db30241095c0568045377a159e2e24c8acaac2eb8cbda4687f5188381478820` | `41c1f015b47fa1bab044ce7531c111a047a0fdfff12e8e95928893eac5cc4d9b` (98) |
| `noUseSuffices_accepts_safe_pOwnedReader_rawVec` | R4a positive control | propext | `ff0015956327e9c8b8aa11651cc252a1db009cd4acedf09eda6cef658262ad85` | `e8ac8aa4865961c709df28d8e1e1cc8be7ed5e3a6e3f1a997208f29a5bc78810` (98) |
| `sound_policies_reject_pOwnedReader_pNestedReader` | R4a positive control; R4b positive control | propext | `be3a1ebb8c2e04408cf722dfa2996c5b87fdb1324dd3f8646869f0a8ac6dba04` | `9ee8832a999f454757afb5421fab1e664d412fd79439c0fb11eec1a03e1edc68` (62) |
| `headNoDrop_accepts_unsafe_pNestedReader` | R4b result; R4b non-vacuity | propext | `29eb62735f0d5f2b48619519e6e1938ff7ca07c9c10fdcdcb0cef646c64d5beb` | `65331842c141db4cf394a08cfd966d10157be58cd1e518b32556160bed61400f` (98) |
| `acceptsP_deepNoDrop_sound_of_mayDangleHonest_glueVisible` | R4b positive control; R4c result | Quot.sound, propext | `3bcc7cd9e07ab85e3ed2df181eaa6df275932d97cf91b0ffbc6df3d837a3f382` | `ca821fa4e845cce943c9d1683e55860bb7cc8f2d5d9fe0d73652daeab922f009` (89) |
| `headNoDrop_accepts_safe_pNestedReader_rawVec` | R4b positive control | propext | `476f51eed16ea019145ee466f608b47b366d0aa8880802aaf86f09803fdd38d5` | `5b084f5fe8cd15c99a3adfa9d5df47efbc6b1018bf4d057fc246eb41302d4f24` (98) |
| `deepNoDrop_sound_hypotheses_hold_pContainer_vecNoOwn` | R4c non-vacuity | propext | `9a81db7276c78d62d60cc1a190fdf424d6217e4450c0f7c75f4d155c87117d4f` | `92fe1184d1143df7bab465c008387df42088f1303a9800d03ebd127bdea9bb08` (81) |
| `deepNoDrop_unsound_without_mayDangleHonest` | R4c counterexample (`hmd`) | propext | `06abc83656a37d3ab71b5251678d7fc070e24b1c899922f6ecf5334131892359` | `14ad928e848591c6d0aae2475cfc5447273e45f8243b198eaada5cbf753e8295` (97) |
| `deepNoDrop_unsound_without_glueVisible` | R4c counterexample (`hglue`) | propext | `9b6e2d3a5e69b5fdf617b94082f3286f5cc5ab0a5d0781c0d5376d9a3ab06c52` | `f18893fdbb5eb62cf4589c079031306b34bfb0e9ab7830d596dabda17832928a` (97) |
| `deepNoDrop_unsound_without_valuesHaveTypes` | R4c counterexample (`hval`) | propext | `ff8bd188b53126348cf6389b57372a86844a513fd1fd5ce414e793be4d199fa6` | `86c62ec8e0cb7c1b0e26f39de789c731b8799becbb45cfebbfd4a9f357a2309d` (97) |
| `deepNoDrop_unsound_without_lifetimesInScope` | R4c counterexample (`hscope`) | propext | `922b7ef5d5dd3d53828f34eb051a56be86d770dc288e7b090c18fdcdc6aaaa8a` | `678a718c766f3db818b4e52200356115b8bd6f02f7a1301e1caa03f2896506a7` (97) |
| `deepNoDrop_rejects_unsafe_pNestedReader` | R4c counterexample (`hacc`) | propext | `c678163e56cfe6b0a0684675fe74c76bcd7fee85c1c425aa68167872b34ba144` | `ed7903463b0e4c503f31b06e1de88ceae3a2c90a1b8d6127c3a4c81e3d3d27dd` (97) |
| `dropOrder_matters_pReaderAfter` | R5 result; R5 non-vacuity | propext | `f547235db05fb73af58834962965d65b2350ee6224d72bff4f3dc8eaaf53f19f` | `fbc718d269dcd01721fa6659922c7fe76228807b11fb8c04c3a690b664bdc06e` (100) |
| `accepts_incomplete_pEmptyOwnedReader` | R6 result; R6 non-vacuity | propext | `6f8f71875bde1a3081fa881a9b45c1a3b00024c019a0b9367696daf4baff27f3` | `e3dcf76f3a0be862bb7ecd9fabc9e473c1d19b139338e8ef588a2811812a77d5` (99) |
| `acceptsP_of_acceptsStrict` | R7 result | Quot.sound, propext | `df228780d34577b796a59d231908d537460b2811a294ebeabd53c7579bb501ba` | `ed3cef79c06de7c68552485ad72702440bf9d2e3d44a4d4747fdedaeff564903` (55) |
| `accepts_of_acceptsStrict` | R7 result | Quot.sound, propext | `3771be237748db0fb896fd9e43303e84df3a12888e90112073bcda5b72af065a` | `ed3cef79c06de7c68552485ad72702440bf9d2e3d44a4d4747fdedaeff564903` (55) |
| `accepts_of_acceptsP_deepNoDrop` | R7 result | Quot.sound, propext | `9013a6cfe5de1d1a06277c6af7561012e49a6af3b7a6ef71430c6a93a3e0d8f3` | `8e322f852923780c408aec9c1892d8e974a44b9c9e3b94645723a5ea8c93d642` (53) |
| `acceptsP_headNoDrop_of_deepNoDrop` | R7 result | propext | `c8e77a5ef3b36d35d41b5fc5b3d89df0e160fe38da56b4d140ade128ba7ac56d` | `b0af56addc6c81780b0e6af103adc32a8f9ebe40bf457c3a76b2845bee6127f0` (52) |
| `acceptsP_noUseSuffices_of_acceptsP` | R7 result | propext | `f7e4a4eb0b2e13e2f26c0e0de9fc54bd490460d9e2ac0ec4d84a1faa180257fc` | `b0af56addc6c81780b0e6af103adc32a8f9ebe40bf457c3a76b2845bee6127f0` (52) |
| `policy_inclusion_premises_hold` | R7 non-vacuity | propext | `9356c63e9e3919083942f7f52225ef63df8a1756f60fe0ddaf306b2df3533d31` | `57456e89d9f4d8f39904e816e746ee3cb9dc760e4da0e801a99476cb58937973` (64) |
| `accepts_of_acceptsStrict_counterexample_pOwnedReader` | R7 counterexample (`h`) | propext | `bcd9a676b9c6e54bce57f4c172f7102c3269c2b862d0ae1636b13a091bfcbf16` | `4e335a3242b9623dcb17efb7a960972614cd289952e6368688aa0fd093b7d75f` (63) |
| `deepNoDrop_inclusions_counterexample_pOwnedReader` | R7 counterexample (`h`) | propext | `d8be7f4a90e47a1df26956adf879e1088469bad432eea6cf4d997c1a74916de6` | `98e1325c3383716114e837e8e1124d0562a42502d219bbe60109bd4310a532ca` (61) |
| `noUseSuffices_inclusion_counterexample_pReaderAfter` | R7 counterexample (`h`) | propext | `37ea27809f14dedbc83e969756b2b8e72ea120c5e43ed434677447a7e8fed64e` | `cbcc2c3b603822654873ab0244693639a64af2e0a210f8a5725328e0f58f21af` (61) |
| `acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible` | R8 result | Quot.sound, propext | `e807e5b3479d592aea2c6cd8276d09e64e1d7202c02d0ab0429a7acbc7028d10` | `d94809b9159ccf594dfc3015a270c98f586f6d0041865adf443aaac4a4948ffa` (90) |
| `dropsNothing_sound_hypotheses_hold_pOwnedReader_rawVec` | R8 non-vacuity | propext | `b0f7991f132d46ddf67b8c5ce08bd40b203f7778a00e0b74bd7633f7c01d2879` | `f09ee8dad58644469035ab7b9ca09a6ec072e31f13c11f9ff4981ca53c7c66c1` (81) |
| `dropsNothing_unsound_without_mayDangleHonest` | R8 counterexample (`hmd`) | propext | `0accdaa5d784a51682f76afd927729badbeac96387c89a2618ddd36ea47c4259` | `aa0180d44a8039625e6ec08680d418d37c4c542d2f2087cc6889e4f04365b76e` (98) |
| `dropsNothing_unsound_without_mayDangleDropsNothing` | R8 counterexample (`hnodrop`) | propext | `56b788790b074c1b14932f18b175f458cc104c5e8750eae80235a3a9e67686c3` | `1806b08b5edefc7ad73e725999134bab62d1688cc1152f57da7d4f0805188c3c` (98) |
| `dropsNothing_unsound_without_glueVisible` | R8 counterexample (`hglue`) | propext | `d8889d8434c99b2a5ad2745fd9d5e5b4f4e753a000bddd6787f8728affe7402d` | `4040e5f30ecc46a42b363799b2be2a687120dc576c378908f0a4e0358f5d83ea` (98) |
| `dropsNothing_unsound_without_valuesHaveTypes` | R8 counterexample (`hval`) | propext | `2c62939936a9c233f9b1f4c9f7c4aedc29d0707ffabc59801f346ea1f63a6d3f` | `ee91bd19dc71b9a366b8500df257c355da8ff03265ea4d07893247a0eb0dade7` (98) |
| `dropsNothing_unsound_without_lifetimesInScope` | R8 counterexample (`hscope`) | propext | `a816a7d6e8d7c8e81c6a72c3749aa98c09cff6709613dca8102a4acc1d954cfd` | `63f3cb5626e69c5287352de22861b829d0d1984734b12a72b57e0c2ef814a068` (98) |
| `dropsNothing_rejects_unsafe_pReaderAfter` | R8 counterexample (`hacc`) | propext | `59927a8138570e219eaf0e73d7aeeedfbe003d8a6a4219d0cee6cfee778b8066` | `eb8910005f5fd052e1dee76a61d572d7b59d1d94b17928d3a57a95125daaeabe` (98) |
| `dropsNothing_unsound_without_mayDangleDropsNothing_headNoDrop` | R8 counterexample (`hnodrop`, `headNoDrop`) | propext | `2b5fe6bbe641aeb6a15dd8084e348bd50a01a1165d7bdc83614ecc0fd36d5fc5` | `bc001839604086daee47e52d384bf7ae714605850998a0a7a45fde60b06458e6` (98) |
| `dropsNothing_unsound_without_mayDangleDropsNothing_ownsRecurse` | R8 counterexample (`hnodrop`, `ownsRecurse`) | propext | `f395d0a1d6b1bcff7280e42c1ec414bf93a53b692b78ae1f6b99edf0d42a9022` | `c4cdc94c093ad2cfce68d61349af82f5b33fd49ea2d08346031789f3214244ea` (98) |
| `acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible_via_acceptsStrict` | R8 alternative proof | Quot.sound, propext | `e807e5b3479d592aea2c6cd8276d09e64e1d7202c02d0ab0429a7acbc7028d10` | `d94809b9159ccf594dfc3015a270c98f586f6d0041865adf443aaac4a4948ffa` (90) |

### Primary sources

The quoted passages and line numbers refer to the files at the pinned commits. The pinned commits, the state of pull request rust-lang/rfcs#3417 and the metadata of the rust-lang/rust issues below were fetched from the GitHub API on 2026-11-21.

* F. S. Klock II, RFC 769 'Sound Generic Drop' (PR rust-lang/rfcs#769, opened 2015-01-29; text/0769-sound-generic-drop.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4): states the drop-check rule (a lifetime 'a reachable from owned data whose type has a lifetime- or type-parametric Drop impl must strictly outlive the value, with parametricity-based exemptions), defines type ownership by recursive descent ('When does one type own another', line 380) and adds the special case 'If E is PhantomData<T>, then recurse on T' (line 453); partially superseded by RFC 1238 (2015-09-18).
* F. S. Klock II, RFC 1238 'Nonparametric dropck' (PR rust-lang/rfcs#1238, opened 2015-08-05; text/1238-nonparametric-dropck.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4): drops RFC 769's reliance on parametricity ('cannot-assume-parametricity') and adds the unsafe attribute #[unsafe_destructor_blind_to_params] ('unguarded-escape-hatch'), which covers all type parameters of a destructor at once.
* F. S. Klock II, RFC 1327 (PR rust-lang/rfcs#1327 'Dropck Eyepatch RFC.', opened 2015-10-19; text/1327-dropck-param-eyepatch.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4; feature dropck_eyepatch, tracking issue rust-lang/rust#34761): introduces per-parameter #[may_dangle]; on a type parameter 'the programmer is asserting the only uses of values of that type will be to move or drop them' (lines 250-252); its motivating examples are multi-parameter types (CheckedHashMap<K, V>, line 66; Vec<T, A: Allocator>, line 88), and its unresolved questions state 'We have not proven any previous variation of the rule sound' (lines 599-600).
* A. Ochagavía, RFC 1857 'Stabilize drop order' (PR rust-lang/rfcs#1857, opened 2017-01-19; text/1857-stabilize-drop-order.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4): stabilizes that struct, tuple and enum-variant fields are dropped in declaration order and slice and Vec elements first to last, and refers to local variables as destroyed in LIFO order.
* N. D. Matsakis, RFC 2094 'non-lexical lifetimes' (PR rust-lang/rfcs#2094, opened 2017-08-02; text/2094-nll.md, rust-lang/rfcs at commit f17e8623ee2e2854570dcdb936a9f4ab08c0fcd4, section 'Layer 3: Accommodating dropck', line 1338): when a variable may be dropped later, 'all of the lifetimes in its type except those marked as may-dangle are live'. The toy instead checks one scope's fixed drop order against a 'strictly outlives' relation.
* lcnr, PR rust-lang/rfcs#3417 'improve #[may_dangle] for type parameters' (https://github.com/rust-lang/rfcs/pull/3417, opened 2023-04-17; an open, unmerged pull request as of 2026-11-21, so a proposal rather than an accepted RFC or a description of current Rust; text/3417-dropck-eyepatch-v3.md at the pull request's head commit 8f8303a6ac0fb86b8611b91d7047bd72b825cbe9 in the contributor fork lcnr/rfcs): proposes #[may_dangle(droppable)] (the impl recursively drops values of T) and #[may_dangle(must_not_use)] (it does not), and that dropck ignore PhantomData; the split parallels the toy's distinction between #[may_dangle] impls that drop their elements (R3, R4a) and impls that do not (R8). It is cited as design discussion; no definition, result or modeling bridge relies on it.
* Rust Compiler Development Guide, 'Drop Check' (rust-lang/rustc-dev-guide, src/borrow-check/drop-check.md at commit 5ac3dc3cc93fcb4c04bdf0821dc17282ee614089): dropck_outlives requires the generic arguments of an explicit Drop impl to be live 'unless they are marked with #[may_dangle] in which case they are fully ignored' (line 125), recurses into all owned types, considers PhantomData<U> to own U and ManuallyDrop<U> not to own U (lines 132-133), and states 'We only rely on dropck_outlives if Ty::needs_drop for the containing local returned true' (line 138); its opening example is a Vec holding a reference to a shorter-lived String, and it shows that dropck still requires a local to be live after the local has been moved out.
* The Rustonomicon, 'Drop Check' (rust-lang/nomicon, src/dropck.md at commit 3c17036782395893fdc639185da1783065ec4571): 'For a generic type to soundly implement drop, its generics arguments must strictly outlive it.' (lines 128-129); obeying this rule 'is sufficient but not necessary to be sound' (lines 132-133); for a self-borrowing struct, 'You can try changing the order of fields or use a tuple instead of the struct, it'll still not compile.' (lines 113-114).
* The Rustonomicon, 'PhantomData' (rust-lang/nomicon, src/phantom-data.md at commit 84f9ba51efd903d5d46c44274be6f98d528e8d66): with a classical impl<T> Drop for Vec<T>, the scope 'let mut v: Vec<&str> = Vec::new(); let s: String = ...; v.push(&s); drop(s);' is denied (lines 135-144); with #[may_dangle] T, 'T may dangle provided it not be involved in some transitive drop glue', and #[may_dangle] is disabled when the generic parameter is held in an owned fashion by the fields of the struct (lines 192-196); the PrintOnDrop<'s> element example; the standard library's Vec<T> keeps a _owns_T: PhantomData<T> field (line 220).
* The Rust Reference, 'Destructors' (rust-lang/reference, src/destructors.md at commit 84dc36ff4712fad6829b6063cd4acbcaf5381708): the variables of a drop scope are dropped 'in reverse order of declaration' (line 59); the fields of a struct are dropped in declaration order (line 12).
* rust-lang/rust#76367 'Soundness issue in Drop for SyncOnceCell' (https://github.com/rust-lang/rust/issues/76367, opened 2020-09-05, closed): the issue states that #[may_dangle] on T in the Drop implementation of SyncOnceCell is correct for simple types such as T = &str but, when T's Drop implementation accesses borrowed data, might lead to accessing already dropped data; rust-lang/rust#99408 'Too lenient #[may_dangle] on BTreeMap; misses PhantomData for dropck' (https://github.com/rust-lang/rust/issues/99408, opened 2022-07-18, closed). The second is a standard-library instance of the failure that accepts_unsound_without_ownsDeclared models (derived (modeling bridge), not proved); the open, unmerged pull request rust-lang/rfcs#3417 cites both as motivation.
* R. Jung, J.-H. Jourdan, R. Krebbers, D. Dreyer, 'RustBelt: Securing the Foundations of the Rust Programming Language', Proc. ACM Program. Lang. 2(POPL), article 66, 2018, doi:10.1145/3158154, Section 9 (Conclusion): 'We proved safety of the destructors of the verified libraries, but do not handle automatic destruction'.
* R. Jung, 'Formalizing Rust', blog post, 2015-10-12, https://www.ralfj.de/blog/2015/10/12/formalizing-rust.html: the first version of the RustBelt formalization would not cover the Drop trait and dropck; 'dropck may well be the most subtle part of the type system'.
* Novelty search: web searches for mechanized soundness proofs of dropck or #[may_dangle]; RustBelt Section 9 (Conclusion); the full texts of Oxide (A. Weiss, O. Gierczak, D. Patterson, A. Ahmed, 'Oxide: The Essence of Rust', arXiv:1903.00982) and RefinedRust (L. Gäher, M. Sammler, R. Jung, R. Krebbers, D. Dreyer, PACMPL 8(PLDI), 2024, doi:10.1145/3656422) contain neither 'dropck' nor 'may_dangle'; bibliographic records of D. J. Pearce, 'A Lightweight Formalism for Reference Lifetimes and Borrowing in Rust' (ACM TOPLAS 43(1), 2021, doi:10.1145/3443420), and RustHornBelt (Y. Matsushita, X. Denis, J.-H. Jourdan, D. Dreyer, PLDI 2022, doi:10.1145/3519939.3523704) were checked at the DOI registry but their full texts were not searched; Patina (E. C. Reed, technical report UW-CSE-15-03-02, 2015) is listed from a search summary and was not verified at the source; region-based memory management (M. Tofte, J.-P. Talpin, Information and Computation 132(2):109-176, 1997, doi:10.1006/inco.1996.2613) deallocates whole regions without per-object destructors. No mechanized treatment of dropck or #[may_dangle] was found; tier T1 is claimed, not T3.
* rust-lang/rust#26656 'dropck can be bypassed via a trait object method' (https://github.com/rust-lang/rust/issues/26656, opened 2015-06-29, closed), rust-lang/rust#34761 '`#[may_dangle]`, a refined dropck escape hatch (tracking issue for RFC 1327)' (https://github.com/rust-lang/rust/issues/34761, open) and rust-lang/rust#110288 'stop adding dropck outlives requirements for `[T; 0]`' (https://github.com/rust-lang/rust/issues/110288, opened 2023-04-13, closed) are related issues; none is modelled.

## Revalidation

Requirements: `elan` (so that `lake` uses the toolchain pinned in `lean/lean-toolchain`) and `python3`. Run from the package directory.

1. Full revalidation (build, banned-token scan, axiom audit, statement and closure hashes):

   ```bash
   python3 support/revalidate.py .
   ```

   The script copies `lean/` to a temporary directory and runs `lake build`; scans the Lean sources for `sorry`, `admit`, `native_decide` and `axiom` declarations; generates a small Lean audit program that computes `Lean.collectAxioms` for every declaration of the library and, for every Lean name referenced by `results.json` or recorded in `audit/statements.json`, prints the `repr` of its type and its definition closure (types and values of every package-local constant reachable from the statement; theorem bodies excluded). It then checks that only `propext`, `Classical.choice` and `Quot.sound` occur and that the SHA-256 of each statement and closure equals the value in `audit/statements.json`, prints `REVALIDATED` and exits 0 on success.

2. Manual build and axiom spot-check of the results, without the script:

   ```bash
   cd lean
   lake build
   cat > /tmp/toydropck_axioms.lean <<'EOF'
   import ToyDropck
   #print axioms Toy.Dropck.acceptsStrict_sound_of_glueVisible
   #print axioms Toy.Dropck.acceptsStrict_rejects_dropSafe_pContainer
   #print axioms Toy.Dropck.accepts_sound_of_mayDangleHonest_ownsDeclared_glueVisible
   #print axioms Toy.Dropck.noUseSuffices_accepts_unsafe_pOwnedReader
   #print axioms Toy.Dropck.headNoDrop_accepts_unsafe_pNestedReader
   #print axioms Toy.Dropck.acceptsP_deepNoDrop_sound_of_mayDangleHonest_glueVisible
   #print axioms Toy.Dropck.dropOrder_matters_pReaderAfter
   #print axioms Toy.Dropck.accepts_incomplete_pEmptyOwnedReader
   #print axioms Toy.Dropck.acceptsP_of_acceptsStrict
   #print axioms Toy.Dropck.accepts_of_acceptsStrict
   #print axioms Toy.Dropck.accepts_of_acceptsP_deepNoDrop
   #print axioms Toy.Dropck.acceptsP_headNoDrop_of_deepNoDrop
   #print axioms Toy.Dropck.acceptsP_noUseSuffices_of_acceptsP
   #print axioms Toy.Dropck.acceptsP_sound_of_mayDangleHonest_dropsNothing_glueVisible
   EOF
   lake env lean /tmp/toydropck_axioms.lean
   ```

   Each line must report a subset of `[propext, Classical.choice, Quot.sound]`.

3. Cheapest check after an upstream change. The results are about the Lean model, not about rustc, so a new Rust or rustc release does not change them. To re-check the modeling bridges, compare the rustc-dev-guide chapter 'Drop Check' (`src/borrow-check/drop-check.md`) and the Rustonomicon chapters 'Drop Check' and 'PhantomData' at the new revision with `dropckP`, `accepts` and the honesty conditions quoted above. To re-check the results under a new Lean release, change `lean/lean-toolchain` and rerun step 1; statement hashes may change with a different `repr`, in which case compare the quoted statements instead.
