# Prophecy variables and backward functions for mutable borrows: a mechanized toy comparison

## Summary

This package defines, in Lean 4 without Mathlib, a toy imperative language with
Rust-style mutable borrows (borrows of integer locals, borrows whose lender is
selected at run time, nested reborrows, writes through borrows, explicit borrow
ends, and calls that take one borrow and return a borrow derived from it), and
three semantics for it: an address-based reference semantics (the ground truth),
a backward-function translation in the style described for Aeneas, and a
prophecy translation in the style described for RustHorn and Creusot. A static
checker defines five separate parts of a borrow discipline.
Model–system relation: none proved (`back-sound`, `agreement` and `proph-sound`
relate the package's own three semantics to one another, not to those tools).
Every result below is a kernel-checked theorem about this toy model; these
theorems neither establish nor refute the corresponding claims about Aeneas,
RustHorn, Creusot or Rust's borrow checker, and the `Basis: derived (modeling
bridge)` paragraphs under **Findings** argue each connection to those systems
separately.

- **`back-sound`** — For every program that has no access to lent locals, no
  access to reborrowed borrows, no use of a borrow after its end, fresh borrow
  names, and every borrow ended by the end, and every initial store, the
  backward-function translation computes exactly the reference outcome: the same
  final store, or stuck exactly when the reference semantics is stuck.
- **`agreement`** — Under the same five hypotheses, the final stores admitted by
  the prophecy translation (standard resolution policy, over all prophecy
  assignments satisfying every resolution constraint) are exactly the
  backward-function translation's result: that store if it succeeds, none if it
  is stuck.
- **`proph-sound`** — Under the same five hypotheses, the prophecy translation
  admits exactly the reference outcome (derived from the two results above).
- **`proph-inclusion`** — For every program with no lent access, no frozen
  access, no use after end and fresh borrow names (ending every borrow is *not*
  assumed), whenever the reference semantics produces a final store, the
  prophecy translation admits it.
- **`omission-monotone`** — For every program and borrow name `r`, with no
  discipline hypothesis, leaving every main-program `endBorrow r` unresolved only
  adds admitted stores.
- **`omission-keeps-real`** — For programs satisfying the four hypotheses of
  `proph-inclusion`, leaving every main-program `endBorrow r` unresolved still
  admits the reference outcome.
- **`resolution-necessary`** — On the disciplined program
  `r0 = &mut x0; *r0 = 5; end r0; x1 = x0` started from the zero store, omitting
  the resolution of `r0` admits a final store the program cannot produce.
- **`premature-resolution`** — On the disciplined program
  `r0 = &mut x0; *r0 = 5; end r0` started from the zero store, resolving `r0`
  right after its creation makes every admitted store (there is at least one)
  have `x0 = 0`, while the only real outcome has `x0 = 5`.
- **`callee-exit-resolution`** — On a disciplined program calling a callee that
  returns a reborrow two levels below its parameter, started from `x ↦ x`,
  dropping the resolutions emitted at callee exit admits a store the program
  cannot produce; with them, the admitted stores are exactly the outcome.
- **`callee-back-projection`** (reference point) — For every scoped callee that
  binds every borrow name at most once, the backward function of its backward
  summary is the projection: `calleeBack f a v = v`.
- **`callee-summary-agreement`** — For every callee with no frozen access, no use
  after end and no rebinding (scoping not assumed), its prophecy contract with
  argument value `a`, argument prophecy `pf` and returned borrow `(c, rf)` holds
  exactly when `calleeFwd f a = some c` and `pf = calleeBack f a rf`.
- **`selection-correct`** (reference check) — On the run-time selection example
  `r0 = if x2 != 0 { &mut x0 } else { &mut x1 }; *r0 = *r0 + 1; end r0` and every
  initial store, the backward translation computes the reference outcome and the
  prophecy translation admits exactly it.
- **`selection-shapes`** — On that example both translations contain the same
  condition-dependent lender map, which no condition-independent map can
  replace; the backward translation applies it to the final value at the end, the
  prophecy translation applies it to one fresh prophecy at creation.

What these results do **not** show is listed first under **Boundaries**; above
all, nothing here is a statement about Aeneas, RustHorn, Creusot or Rust's borrow
checker, and the discipline is a package-specific checker that constrains a
program only up to its first scoping error.

*An agent relying on a result from this package must quote its plain-language claim and the relevant hypotheses and non-claims, not just its name or a paraphrase.*
## Applicability

**Model fidelity: toy model.** The definitions are written for this package and
mirror no production code base. The language is straight-line code over
unbounded integer locals (`Var := Nat`, `Store := Var → Int`) with mutable
borrows of whole locals, reborrows, borrows whose lender is chosen at run time
between two locals, writes through borrows, explicit `endBorrow` statements, and
calls `s = f(&mut *r)` to callees that take exactly one borrow (reference
variable `0` of their frame), have no locals, make no calls, and return one
borrow derived from their parameter. There are no loops, no branches other than
the run-time choice of a lender, no shared borrows, no two-phase borrows, no
compound values or pair components, no panics, divergence or early exits, no
intermediate assertions, no unsafe code, no interior mutability and no
concurrency.

**What the definitions are meant to capture.**

- `refSem` is an address-based ground truth: a borrow *is* the address of a
  local, writes update the store in place, ending a borrow has no run-time effect,
  and no borrow checking is performed.
- `backSem` imitates backward functions as described for Aeneas: a live borrow
  is a current value plus a backward function from the borrow's final value to
  the new values of its lenders, applied when the borrow ends. Known gaps: Aeneas
  ends borrows lazily on demand and translates to pure functions, whereas
  `backSem` is a small-step interpreter over a mutable environment of borrow
  slots that applies a backward function exactly at an explicit `endBorrow`.
- The prophecy translation (`runP`, `ProphOutcome`) imitates the
  (current, final) encoding described for RustHorn and Creusot: creating a borrow
  draws a fresh prophecy and hands it to the lender, and ending a borrow emits the
  resolution constraint `cur = fin`; admitted final stores are those of runs
  under prophecy assignments that satisfy every constraint emitted during the
  whole run. Resolution policies (`ResPolicy`) model omitted, misplaced or
  callee-exit resolutions. Known gaps: constraints are checked only at the end of
  a completed run (no intermediate assertions), and callee specifications are
  computed from callee bodies, not written by a user.
- The borrow discipline (`violations`, with the five properties
  `NoLentAccess`, `NoFrozenAccess`, `NoUseAfterEnd`, `FreshBindings`,
  `AllEndedAtExit`, and the callee properties `CalleeNoFrozenAccess`,
  `CalleeNoUseAfterEnd`, `CalleeFreshBindings`, `CalleeScoped`) is a static,
  explicit-end checker chosen for this package. It is not Rust's borrow checker:
  it does not infer lifetimes, it lends both candidates of a run-time selected
  borrow until the borrow ends, it requires syntactically fresh borrow names
  (also forbidding reuse of the name of an ended borrow), and it stops at the
  first scoping error.

**Subjects.** The Lean 4 toolchain `v4.34.1` (`leanprover/lean4`, commit
`5045d0056413266e57c625dcd7c365b10e377c52`) is the system directly exercised:
every result is a theorem checked by its kernel. The listed papers are the
sources whose encodings the toy definitions imitate; no tool implementation was
run or inspected, and every connection to a real system is labeled
`Basis: derived (modeling bridge)` with its reasoning. The Lake project in
`lean/` (library `ToyProphecy`, namespace `Toy.Prophecy`) has no dependencies
and does not use Mathlib.
## Findings

All definitions and statements live in `lean/ToyProphecy/` (namespace
`Toy.Prophecy`). The definitions are summarized first with the key Lean text
quoted. Then come the exact Lean statements (proofs omitted) of the main
results, of the concrete results of the counterexample cards with their
positive controls, of the selection facts and of every boundary fact in
`Boundaries.lean`; the tightness counterexamples and the definition examples are
named and summarized there rather than quoted (Sections 2.1 and 1.7). Then
comes the structure of the proofs of the general results, and finally one card
per result.

### Definitions

#### 1.1 Syntax (`ToyProphecy/Syntax.lean`)

```lean
abbrev Var := Nat        -- integer locals
abbrev RefVar := Nat     -- borrow names (separate namespace)
abbrev Store := Var → Int
def Store.set (σ : Store) (x : Var) (v : Int) : Store := fun y => if y = x then v else σ y

inductive Expr | lit (n : Int) | var (x : Var) | deref (r : RefVar) | add (a b : Expr)

inductive Op
  | assign (x : Var) (e : Expr)                   -- x = e
  | borrow (r : RefVar) (x : Var)                 -- r = &mut x
  | borrowSel (r : RefVar) (c : Expr) (x y : Var) -- r = if c ≠ 0 { &mut x } else { &mut y }
  | reborrow (s r : RefVar)                       -- s = &mut *r
  | write (r : RefVar) (e : Expr)                 -- *r = e
  | endBorrow (r : RefVar)                        -- end of r's lifetime

structure Callee where body : List Op; ret : RefVar   -- parameter = borrow name 0
inductive Stmt | op (o : Op) | call (s : RefVar) (f : Callee) (r : RefVar)  -- s = f(&mut *r)
abbrev Prog := List Stmt
```

Callee frames have no locals: `assign`, `borrow`, `borrowSel` and `var` inside a
callee body are stuck in every semantics. Callees make no calls.

#### 1.2 Reference semantics (`RefSem.lean`) — the ground truth

State: `store : Store`, `refs : RefVar → Option Var` (a borrow *is* an address).

| statement | effect |
| :--- | :--- |
| `assign x e` | `store := store.set x ⟦e⟧` |
| `borrow r x` | `refs r := x` |
| `borrowSel r c x y` | `refs r := if ⟦c⟧ ≠ 0 then x else y` |
| `reborrow t r` | `refs t := refs r` |
| `write r e` | `store := store.set (refs r) ⟦e⟧` (in place) |
| `endBorrow r` | no effect (requires `r` bound) |
| `call t f r` | run `f.body` on the shared store with frame `{0 ↦ refs r}`; `refs t :=` the address held by `f.ret` |

`⟦deref r⟧ = store (refs r)`. Stuck (`none`) only on scoping errors (unbound
name; local operation in a callee; callee returns an unbound name). No borrow
checking. `refSem P σ : Option Store` is the final store.

#### 1.3 Backward-function translation (`Backward.lean`)

A live borrow is `BRef = { cur : Int, back : Int → List (Target × Int) }` where
`Target = loc x | ref q`; `back v` lists the lender assignments to perform when the
borrow ends with final value `v`. Lent locals keep their old value until the end.

| statement | effect |
| :--- | :--- |
| `borrow r x` | `r := ⟨σ x, fun v => [(loc x, v)]⟩` |
| `borrowSel r c x y` (`b := ⟦c⟧ ≠ 0`) | `r := ⟨if b then σ x else σ y, selBack b x y (σ x) (σ y)⟩` with `selBack b x y x0 y0 v = if b then [(loc y, y0), (loc x, v)] else [(loc x, x0), (loc y, v)]` |
| `reborrow t r` | `t := ⟨r.cur, fun v => [(ref r, v)]⟩` |
| `write r e` | `r.cur := ⟦e⟧` |
| `endBorrow r` | perform `r.back r.cur` (`loc x, v` sets `x := v`; `ref q, v` sets `q.cur := v`) |
| `call t f r` | `t := ⟨calleeFwd f r.cur, fun v => [(ref r, calleeBack f r.cur v)]⟩` |

Callee *backward summary*, computed from the body alone: run the body from a frame
`{0 ↦ ⟨a, fun _ => []⟩}`; `calleeFwd f a` = current value of `f.ret`;
`calleeBack f a v` = the parameter's current value after setting `f.ret`'s current
value to `v` and ending the borrows along the parent chain from `f.ret` up to the
parameter (composition of the backward functions). The partial version
`calleeBack?` is `none` when the callee body is stuck, when `f.ret` is unbound at
the end of the body, or when the chain does not reach the parameter within
`f.body.length + 1` steps (e.g. a cycle); the total version `calleeBack` defaults
to `0` there. `backSem P σ : Option Store`.

#### 1.4 Prophecy translation (`Prophecy.lean`)

A live borrow is `PRef = { cur fin : Int, done : Bool }`; parameterised by a
prophecy assignment `φ : Nat → Int` and a counter `next`.

| statement | effect (`k := next`, then `next := k+1` when a prophecy is drawn) |
| :--- | :--- |
| `borrow r x` | `r := (σ x, φ k)`; `x := φ k` |
| `borrowSel r c x y` | `r := (if b then σ x else σ y, φ k)`; `if b then x := φ k else y := φ k` |
| `reborrow t r` | `t := (r.cur, φ k)`; `r.cur := φ k` |
| `write r e` | `r.cur := ⟦e⟧` |
| `endBorrow r` | emit `(r.cur, r.fin)` (if the policy resolves `r` at its end); `r.done := true` |
| `call t f r` | parameter `(r.cur, φ k)`, `r.cur := φ k`; run the body's prophecy translation from index `k+1`; at callee exit emit `(p.cur, p.fin)` for every callee borrow `p ≠ f.ret` still bound and not done; `t :=` the returned pair |

`Sat cs := ∀ c ∈ cs, c.1 = c.2`.

```lean
structure ResPolicy where
  atEnd : RefVar → Bool        -- main program: resolve r when it ends
  atCalleeExit : Bool          -- resolve remaining callee borrows at callee exit
  early : Nat → List RefVar    -- main program: also resolve these after statement i
def ResPolicy.std := { atEnd := fun _ => true, atCalleeExit := true, early := fun _ => [] }
def ResPolicy.omitAtEnd r := { std with atEnd := fun r' => decide (r' ≠ r) }
  -- keyed by the name r: every main-program `endBorrow r` is unresolved; callees unaffected
def ResPolicy.omitAtCalleeExit := { std with atCalleeExit := false }
def ResPolicy.resolveAfter i r := { atEnd := fun r' => decide (r' ≠ r), atCalleeExit := true,
                                    early := fun j => if j = i then [r] else [] }

def ProphOutcomeWith (pol : ResPolicy) (P : Prog) (σ σ' : Store) : Prop :=
  ∃ φ s, runP pol φ 0 (PState.init σ) P = some s ∧ Sat s.cs ∧ s.store = σ'
def ProphOutcome := ProphOutcomeWith ResPolicy.std

def ProphContract (f : Callee) (a c pf rf : Int) : Prop :=
  ∃ φ s, calleeRunP true φ f a pf 0 = some s ∧ Sat s.cs ∧
    ∃ q, s.refs f.ret = some q ∧ q.cur = c ∧ q.fin = rf
```

Reading for verification: a postcondition is established when it holds of every
admitted store. *Inclusion* (the real store is admitted) makes that sound;
*precision* (nothing else is admitted) makes it complete.

#### 1.5 Borrow discipline (`Discipline.lean`)

A static checker over statuses (`unborn | active | frozen | ended` per name; lent
flag per local; lender link per name). `borrowSel` lends **both** candidates until
the borrow ends. `reborrow t r` and `call t f r` freeze `r` until `t` ends (ending
`t` unfreezes the borrow its lender link points to). Returning from a callee
counts as a use of the returned name. Callee violations count as program
violations. Scoping errors (a reference variable that was never bound, a local
operation in a callee, a callee returning a name that was never bound) are not
violations, and the checker stops at the first one: once stuck it records no
further violation (`checkStmts_of_stuck`, `checkOps_of_stuck`), and `unendedAtExit` is not reported for a stuck program. So a
program with a scoping error satisfies each `Avoids k` as soon as no violation of
kind `k` is recorded before the checker gets stuck, whatever follows (`stuckProg_satisfies_all_avoids`); likewise
for callees (`stuckCallee_satisfies_all_avoids`).

Binding a name that is already bound, in any status including `ended`, is a
`rebind` violation. The borrow previously held under that name is then *leaked*:
it never ends, so a local it lends stays lent and a borrow it reborrows stays
frozen for the rest of the frame. At the rebinding, every lender link `.ref r` of
another name (which referred to the leaked borrow) is dropped, so ending such a
reborrow later cannot unfreeze the new borrow held under `r`
(`rebindThenFrozenRead_violations`). A leaked borrow is reported only as
`rebind`, not as `unendedAtExit`.

```lean
def bindRef (c : CState) (r : RefVar) : CState :=
  if c.status r = .unborn then { c with bound := c.bound ++ [r] }
  else
    let c := c.addV .rebind
    { c with bound := c.bound ++ [r],
             lender := fun q => if c.lender q = some (.ref r) then none else c.lender q }
```
`violations P : List Violation`, and for each kind a separate property:

```lean
def Avoids (k : Violation) (P : Prog) : Prop := k ∉ violations P
abbrev NoLentAccess   P := Avoids .lentAccess P    -- no read/assign/borrow of a lent local
abbrev NoFrozenAccess P := Avoids .frozenAccess P  -- no use of a reborrowed borrow (incl. end, call, return)
abbrev NoUseAfterEnd  P := Avoids .useAfterEnd P   -- no use after end (incl. a second end)
abbrev FreshBindings  P := Avoids .rebind P        -- every binding uses a name never bound before in its frame
abbrev AllEndedAtExit P := Avoids .unendedAtExit P -- no main-program borrow live at the end
def CalleeAvoids (k) (f : Callee) : Prop := k ∉ calleeViolations f
  -- only .frozenAccess, .useAfterEnd, .rebind can occur (calleeAvoids_lentAccess_unendedAtExit)
abbrev CalleeNoFrozenAccess f := CalleeAvoids .frozenAccess f
abbrev CalleeNoUseAfterEnd  f := CalleeAvoids .useAfterEnd f
abbrev CalleeFreshBindings  f := CalleeAvoids .rebind f      -- also rejects reuse of an ended name
def CalleeScoped (f : Callee) : Prop := (checkCallee f).stuck = false
  -- body and returned name f.ret: no never-bound name, no local; f.ret is the parameter or bound in the body
```

#### 1.6 Selection shapes (`Selection.lean`)

```lean
def selLenders (b : Bool) (x0 y0 v : Int) : Int × Int := if b then (v, y0) else (x0, v)
def SelBackSpec (b) (x0 y0 cur : Int) (back : Int → Int × Int) : Prop :=
  cur = (if b then x0 else y0) ∧ ∀ v, back v = selLenders b x0 y0 v
def SelProphSpec (b) (x0 y0 cur fin x' y' : Int) : Prop :=
  cur = (if b then x0 else y0) ∧ (x', y') = selLenders b x0 y0 fin
def backLenders01 (σ : Store) (q : BRef) (v : Int) : Int × Int :=   -- lenders after q.back v
  ((applyBack { store := σ, refs := fun _ => none } (q.back v)).map
    fun s => (s.store 0, s.store 1)).getD (0, 0)
```

#### 1.7 Definition examples (`Examples.lean`, all proved)

| definition | positive | negative |
| :--- | :--- | :--- |
| `Store.set`, `fupd` | `store_set_pos`, `fupd_pos` | `store_set_neg`, `fupd_neg` |
| `refSem` | `refSem_pos_nested` (111), `refSem_pos_in_place` (writes visible before end) | `refSem_neg_unbound`, `refSem_neg_callee_local` (stuck) |
| `backSem` | `backSem_pos_nested`, `backSem_pos_call` | `backSem_neg_not_in_place` (lender not updated before end), `backSem_neg_unbound` |
| `applyBack`, `selBack` | `applyBack_pos`, `selBack_pos_degenerate` (`x = y`) | `applyBack_neg`, `selBack_neg` |
| `calleeFwd`, `calleeBack` | `calleeFwd_pos`, `calleeBack_pos` | `calleeFwd_neg` (stuck callee), `calleeBack_neg` (cyclic chain) |
| `backLenders01` | `backLenders01_pos` | `backLenders01_neg` (stuck: default `(0, 0)`) |
| `Sat` | `sat_pos` | `sat_neg` |
| policies | `std_pos`, `omitAtEnd_pos`, `resolveAfter_pos`, `calleeExit_pos` | `omitAtEnd_neg`, `resolveAfter_neg`, `calleeExit_neg` |
| `ProphOutcome` | `prophOutcome_pos` | `prophOutcome_neg` |
| `ProphContract` | `prophContract_pos` | `prophContract_neg` |
| discipline | `discipline_pos` | `borrowSel_lends_both`, `end_parent_first_neg`, `rebind_ended_neg`, `rebindThenFrozenRead_violations`, `rebindThenFrozenUse_violations` (rebinding does not hide a frozen access), `cx*_violations`; `unbound_not_violation` (scoping is not a violation) |
| callee checks | `calleeAvoids_pos_neg`, `calleeDiscipline_pos_neg`, `calleeScoped_pos_neg` (positive halves), `calleeAvoids_lentAccess_unendedAtExit` | (negative halves); `emptyBody_unboundRet_not_scoped` (`CalleeScoped` also checks `f.ret`); `reuseEndedCallee_harmless` (`CalleeFreshBindings` rejects reuse of an ended name) |
| selection shapes | `selLenders_pos`, `selBackSpec_pos`, `selProphSpec_pos` | `selLenders_neg`, `selBackSpec_neg`, `selProphSpec_neg` |

Further facts about the definitions: `rebindEnded_harmless` (reusing an ended
name is a `rebind` violation but harmless for both translations on that
example), `rebindThenFrozenRead_real_excluded` (why the frozen access there must
be rejected), `endParentFirst_prophecy_exact_backward_lossy` and
`endParentFirstChildUnended_imprecise` (ending a reborrowed parent first),
`cxRebind_real_outcome_admitted` (a leaked borrow does not exclude the real
outcome in that example), `cxCalleeEndedRebind_cycle` (in a callee with a frozen
access, reusing an ended name can close a cycle of parents, so `FreshBindings`
cannot simply allow it).

Boundary examples (`Boundaries.lean`, all proved): the checker stops at the first
scoping error (`checkOps_of_stuck`, `checkStmts_of_stuck`, `stuckProg_satisfies_all_avoids`, `stuckCallee_satisfies_all_avoids`,
`cxCalleeLocal_avoids_all_no_contract`); `CalleeScoped` covers the returned name
(`emptyBody_unboundRet_not_scoped`); reuse of an ended name in a callee
(`reuseEndedCallee_harmless`); `calleeBack` totalizes `calleeBack?`
(`calleeBack_masks_none_at_zero`, `calleeBackOpt_eq_some_of_calleeBack_eq_of_ne_zero`);
`ResPolicy.omitAtEnd` leaves callee frames resolved
(`callDeep_omitAtEnd0_callee_still_resolved`); edge cases `emptyProg_edge_case`,
`emptyCallee_edge_case`, `selSameLocal_edge_case`.


### Statements (exact Lean text)

Exact Lean text (copied from the sources, proofs omitted) of every main
statement, of the concrete results and positive controls of the counterexample
cards, of the selection facts and of every boundary fact in `Boundaries.lean`,
together with the definitions of the named example programs and callees that
these statements or the result cards use. The six tightness counterexample
programs `cxLent`, `cxFrozen`, `cxAfterEnd`, `cxAfterEndUnsat`, `cxRebind` and
`cxUnended` are given in surface syntax in Section 2.1 instead; the tightness
counterexample theorems are named there, and the definition examples are listed
in Section 1.7.

```lean
-- named programs (ToyProphecy/Programs.lean, Resolution.lean), `open Expr Op Stmt`
def zeroStore : Store := fun _ => 0
def idStore : Store := fun x => (x : Int)
def writeThenRead : Prog :=
  [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0), op (assign 1 (var 0))]
def writeOnce : Prog := [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0)]
def reborrowOnce : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (write 1 (lit 7)), op (endBorrow 1), op (endBorrow 0)]
def deepCallee : Callee :=
  { body := [reborrow 1 0, write 1 (add (deref 1) (lit 2)), endBorrow 1,
             write 0 (add (deref 0) (lit 3)), reborrow 2 0, reborrow 3 2], ret := 3 }
def callDeep : Prog :=
  [op (borrow 0 0), call 1 deepCallee 0, op (write 1 (add (deref 1) (lit 10))),
   op (endBorrow 1), op (assign 1 (deref 0)), op (endBorrow 0)]
def callDeepOut : Store := (idStore.set 0 15).set 1 15
def endParentFirst : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (write 1 (lit 7)), op (endBorrow 0), op (endBorrow 1)]
def endParentFirstChildUnended : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (write 1 (lit 7)), op (endBorrow 0)]
def selIncr : Prog :=
  [op (borrowSel 0 (var 2) 0 1), op (write 0 (add (deref 0) (lit 1))), op (endBorrow 0)]
-- callees (Calls.lean, Boundaries.lean)
def cxCalleeLocal : Callee := { body := [assign 0 (lit 1)], ret := 0 }
def cxCalleeRebind : Callee := { body := [reborrow 1 0, reborrow 2 1, reborrow 1 2], ret := 1 }
def emptyBodyUnboundRet : Callee := { body := [], ret := 1 }
def reuseEndedCallee : Callee :=
  { body := [ reborrow 1 0, write 1 (add (deref 1) (lit 2)), endBorrow 1,
              write 0 (add (deref 0) (lit 3)), reborrow 1 0 ]
    ret := 1 }
def stuckCalleeWithViolations : Callee :=
  { body := [assign 0 (lit 1), reborrow 1 0, write 0 (lit 5), endBorrow 1,
             write 1 (lit 6), reborrow 1 0]
    ret := 1 }
-- stuck program (Boundaries.lean): `r0 = &mut x0; *r99 = 1; x1 = x0; r1 = &mut *r0; *r0 = 2; end r0; end r0; r0 = &mut x1`
def stuckProgWithViolations : Prog :=
  [ op (borrow 0 0),
    op (write 99 (lit 1)),
    op (assign 1 (var 0)),
    op (reborrow 1 0),
    op (write 0 (lit 2)),
    op (endBorrow 0),
    op (endBorrow 0),
    op (borrow 0 1) ]
-- non-vacuity program (NonVacuity.lean)
def richProg : Prog :=
  [op (borrowSel 0 (var 2) 0 1), op (reborrow 1 0), op (write 1 (add (deref 1) (lit 1))),
   op (reborrow 2 1), op (write 2 (add (deref 2) (lit 10))), op (endBorrow 2), op (endBorrow 1),
   call 3 deepCallee 0, op (write 3 (add (deref 3) (lit 100))), op (endBorrow 3),
   op (write 0 (add (deref 0) (lit 1000))), op (endBorrow 0), op (assign 2 (var 0))]
-- definition examples (Examples.lean)
def rebindEnded : Prog :=
  [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0), op (borrow 0 1), op (write 0 (lit 9)),
   op (endBorrow 0)]
def rebindThenFrozenRead : Prog :=
  [op (borrow 0 0), op (reborrow 1 0), op (borrow 0 1), op (reborrow 2 0), op (endBorrow 1),
   op (assign 2 (deref 0)), op (write 2 (lit 9)), op (endBorrow 2), op (endBorrow 0)]
-- tightness callees (Calls.lean)
def cxCalleeFrozen : Callee := { body := [reborrow 1 0, write 0 (lit 5), write 1 (lit 6)], ret := 1 }
def cxCalleeAfterEnd : Callee := { body := [reborrow 1 0, endBorrow 1, reborrow 2 1], ret := 2 }
def cxCalleeEndedRebind : Callee :=
  { body := [reborrow 1 0, reborrow 2 1, endBorrow 1, reborrow 1 2], ret := 1 }
-- edge-case program and callee (Boundaries.lean)
def emptyCallee : Callee := { body := [], ret := 0 }
def selSameLocal : Prog :=
  [op (borrowSel 0 (var 2) 0 0), op (write 0 (add (deref 0) (lit 1))), op (endBorrow 0)]
```

```lean
-- lean/ToyProphecy/Results.lean:33-36
-- (Results.lean)
theorem backSem_eq_refSem_of_discipline (P : Prog) (σ : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) :
    backSem P σ = refSem P σ

-- lean/ToyProphecy/Results.lean:46-49
-- (Results.lean)
theorem prophOutcome_iff_backSem_of_discipline (P : Prog) (σ : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) :
    ∀ σ', ProphOutcome P σ σ' ↔ backSem P σ = some σ'

-- lean/ToyProphecy/Results.lean:60-63
-- (Results.lean; derived from the statements above)
theorem prophOutcome_iff_refSem_of_discipline (P : Prog) (σ : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) :
    ∀ σ', ProphOutcome P σ σ' ↔ refSem P σ = some σ'

-- lean/ToyProphecy/Results.lean:76-80
-- (Results.lean)
theorem prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings
    (P : Prog) (σ σ' : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P)
    (h : refSem P σ = some σ') : ProphOutcome P σ σ'

-- lean/ToyProphecy/Results.lean:89-90
-- (Results.lean)
theorem prophOutcomeWith_omitAtEnd_of_prophOutcome (r : RefVar) (P : Prog) (σ σ' : Store)
    (h : ProphOutcome P σ σ') : ProphOutcomeWith (ResPolicy.omitAtEnd r) P σ σ'

-- lean/ToyProphecy/Results.lean:104-108
-- (Results.lean; derived from the statements above)
theorem prophOutcomeWith_omitAtEnd_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings
    (r : RefVar) (P : Prog) (σ σ' : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P)
    (h : refSem P σ = some σ') : ProphOutcomeWith (ResPolicy.omitAtEnd r) P σ σ'

-- lean/ToyProphecy/Results.lean:121-123
-- (Results.lean)
theorem calleeBack_eq_final_of_calleeScoped_of_calleeFreshBindings (f : Callee)
    (hS : CalleeScoped f) (hB : CalleeFreshBindings f) :
    ∀ a v, calleeBack f a v = v

-- lean/ToyProphecy/Results.lean:133-137
-- (Results.lean)
theorem prophContract_iff_backwardSummary_of_calleeNoFrozenAccess_of_calleeNoUseAfterEnd_of_calleeFreshBindings
    (f : Callee)
    (hF : CalleeNoFrozenAccess f) (hE : CalleeNoUseAfterEnd f)
    (hB : CalleeFreshBindings f) :
    ∀ a c pf rf, ProphContract f a c pf rf ↔ (calleeFwd f a = some c ∧ pf = calleeBack f a rf)

-- lean/ToyProphecy/Resolution.lean:59-63
-- (Resolution.lean)
theorem omitting_resolution_admits_unproducible_store :
    NoLentAccess writeThenRead ∧ NoFrozenAccess writeThenRead ∧ NoUseAfterEnd writeThenRead ∧
    FreshBindings writeThenRead ∧ AllEndedAtExit writeThenRead ∧
    ∃ σ', ProphOutcomeWith (ResPolicy.omitAtEnd 0) writeThenRead zeroStore σ' ∧
      σ' 0 = 7 ∧ σ' 1 = 7 ∧ refSem writeThenRead zeroStore ≠ some σ'

-- lean/ToyProphecy/Resolution.lean:33-34
-- (positive control) (Resolution.lean)
theorem prophOutcome_writeThenRead_iff (σ' : Store) :
    ProphOutcome writeThenRead zeroStore σ' ↔ refSem writeThenRead zeroStore = some σ'

-- lean/ToyProphecy/Resolution.lean:88-93
-- (Resolution.lean)
theorem premature_resolution_excludes_real_store :
    NoLentAccess writeOnce ∧ NoFrozenAccess writeOnce ∧ NoUseAfterEnd writeOnce ∧
    FreshBindings writeOnce ∧ AllEndedAtExit writeOnce ∧
    (∀ σ', ProphOutcomeWith (ResPolicy.resolveAfter 0 0) writeOnce zeroStore σ' → σ' 0 = 0) ∧
    (∃ σ', ProphOutcomeWith (ResPolicy.resolveAfter 0 0) writeOnce zeroStore σ') ∧
    (refSem writeOnce zeroStore).map (· 0) = some 5

-- lean/ToyProphecy/Resolution.lean:106-108
-- (positive control) (Resolution.lean)
theorem resolution_after_last_write_exact (σ' : Store) :
    ProphOutcomeWith (ResPolicy.resolveAfter 1 0) writeOnce zeroStore σ' ↔
      refSem writeOnce zeroStore = some σ'

-- lean/ToyProphecy/Resolution.lean:136-138
-- (positive control) (Resolution.lean)
theorem parent_resolution_while_reborrow_live_exact (σ' : Store) :
    ProphOutcomeWith (ResPolicy.resolveAfter 1 0) reborrowOnce zeroStore σ' ↔
      refSem reborrowOnce zeroStore = some σ'

-- lean/ToyProphecy/Resolution.lean:168-173
-- (Resolution.lean)
theorem omitting_callee_exit_resolution_admits_unproducible_store :
    NoLentAccess callDeep ∧ NoFrozenAccess callDeep ∧ NoUseAfterEnd callDeep ∧
    FreshBindings callDeep ∧ AllEndedAtExit callDeep ∧
    (refSem callDeep idStore).map (fun σ => (σ 0, σ 1)) = some (15, 15) ∧
    ∃ σ', ProphOutcomeWith ResPolicy.omitAtCalleeExit callDeep idStore σ' ∧
      σ' 0 = 7 ∧ σ' 1 = 7 ∧ refSem callDeep idStore ≠ some σ'

-- lean/ToyProphecy/Resolution.lean:207-208
-- (positive control) (Resolution.lean)
theorem callDeep_prophOutcome_iff (σ' : Store) :
    ProphOutcome callDeep idStore σ' ↔ refSem callDeep idStore = some σ'

-- lean/ToyProphecy/Resolution.lean:232-233
-- (Resolution.lean)
theorem callDeep_omitAtCalleeExit_admits_real :
    ProphOutcomeWith ResPolicy.omitAtCalleeExit callDeep idStore callDeepOut

-- lean/ToyProphecy/Resolution.lean:250-254
-- (Resolution.lean)
theorem endParentFirst_prophecy_exact_backward_lossy :
    violations endParentFirst = [.frozenAccess] ∧
    (refSem endParentFirst zeroStore).map (· 0) = some 7 ∧
    (backSem endParentFirst zeroStore).map (· 0) = some 0 ∧
    ∀ σ', ProphOutcome endParentFirst zeroStore σ' ↔ refSem endParentFirst zeroStore = some σ'

-- lean/ToyProphecy/Resolution.lean:287-291
-- (Resolution.lean)
theorem endParentFirstChildUnended_imprecise :
    violations endParentFirstChildUnended = [.frozenAccess, .unendedAtExit] ∧
    (refSem endParentFirstChildUnended zeroStore).map (· 0) = some 7 ∧
    (∃ σ', ProphOutcome endParentFirstChildUnended zeroStore σ' ∧ σ' 0 = 7) ∧
    (∃ σ', ProphOutcome endParentFirstChildUnended zeroStore σ' ∧ σ' 0 = 8)

-- lean/ToyProphecy/Selection.lean:55-57
-- (Selection.lean)
theorem selIncr_both_translations_correct (σ : Store) :
    backSem selIncr σ = refSem selIncr σ ∧
    ∀ σ', ProphOutcome selIncr σ σ' ↔ refSem selIncr σ = some σ'

-- lean/ToyProphecy/Selection.lean:102-112
-- (Selection.lean)
theorem selIncr_backward_shape (σ : Store) :
    (∃ s q, runB (BState.init σ) [op (borrowSel 0 (var 2) 0 1)] = some s ∧
      s.refs 0 = some q ∧ s.store = σ ∧
      SelBackSpec (decide (σ 2 ≠ 0)) (σ 0) (σ 1) q.cur (backLenders01 σ q) ∧
      ∀ (τ : Store) (refs : RefVar → Option BRef) (v : Int),
        (applyBack { store := τ, refs := refs } (q.back v)).map
            (fun s' => (s'.store 0, s'.store 1)) =
          some (selLenders (decide (σ 2 ≠ 0)) (σ 0) (σ 1) v)) ∧
    (∃ s, runB (BState.init σ) selIncr = some s ∧
      (s.store 0, s.store 1) =
        selLenders (decide (σ 2 ≠ 0)) (σ 0) (σ 1) ((if σ 2 ≠ 0 then σ 0 else σ 1) + 1))

-- lean/ToyProphecy/Selection.lean:124-129
-- (Selection.lean)
theorem selIncr_prophecy_shape (σ : Store) (φ : Nat → Int) :
    (∃ s q, runP ResPolicy.std φ 0 (PState.init σ) [op (borrowSel 0 (var 2) 0 1)] = some s ∧
      s.next = 1 ∧ s.cs = [] ∧ s.refs 0 = some q ∧ q.fin = φ 0 ∧
      SelProphSpec (decide (σ 2 ≠ 0)) (σ 0) (σ 1) q.cur q.fin (s.store 0) (s.store 1)) ∧
    (∃ s, runP ResPolicy.std φ 0 (PState.init σ) selIncr = some s ∧ s.next = 1 ∧
      s.cs = [((if σ 2 ≠ 0 then σ 0 else σ 1) + 1, φ 0)])

-- lean/ToyProphecy/Selection.lean:140-141
-- (Selection.lean)
theorem selLenders_depends_on_condition (x0 y0 : Int) :
    ¬ ∃ g : Int → Int × Int, ∀ b v, g v = selLenders b x0 y0 v

-- lean/ToyProphecy/Boundaries.lean:41-42
-- (boundary fact) (Boundaries.lean)
theorem checkOps_of_stuck (L : Bool) (c : CState) (h : c.stuck = true) :
    ∀ os, checkOps L c os = c

-- lean/ToyProphecy/Boundaries.lean:51-52
-- (boundary fact) (Boundaries.lean)
theorem checkStmts_of_stuck (c : CState) (h : c.stuck = true) :
    ∀ P, checkStmts c P = c

-- lean/ToyProphecy/Boundaries.lean:79-88
-- (boundary fact) (Boundaries.lean)
theorem stuckProg_satisfies_all_avoids :
    NoLentAccess stuckProgWithViolations ∧
    NoFrozenAccess stuckProgWithViolations ∧
    NoUseAfterEnd stuckProgWithViolations ∧
    FreshBindings stuckProgWithViolations ∧
    AllEndedAtExit stuckProgWithViolations ∧
    refSem stuckProgWithViolations zeroStore = none ∧
    backSem stuckProgWithViolations zeroStore = none ∧
    (∀ φ, runP ResPolicy.std φ 0 (PState.init zeroStore) stuckProgWithViolations = none) ∧
    (∀ σ', ¬ ProphOutcome stuckProgWithViolations zeroStore σ')

-- lean/ToyProphecy/Boundaries.lean:105-109
-- (boundary fact) (Boundaries.lean)
theorem stuckCallee_satisfies_all_avoids :
    ¬ CalleeScoped stuckCalleeWithViolations ∧
    CalleeNoFrozenAccess stuckCalleeWithViolations ∧
    CalleeNoUseAfterEnd stuckCalleeWithViolations ∧
    CalleeFreshBindings stuckCalleeWithViolations

-- lean/ToyProphecy/Boundaries.lean:115-118
-- (boundary fact) (Boundaries.lean)
theorem cxCalleeLocal_avoids_all_no_contract :
    CalleeNoFrozenAccess cxCalleeLocal ∧ CalleeNoUseAfterEnd cxCalleeLocal ∧
    CalleeFreshBindings cxCalleeLocal ∧ (∀ a, calleeFwd cxCalleeLocal a = none) ∧
    ∀ a c pf rf, ¬ ProphContract cxCalleeLocal a c pf rf

-- lean/ToyProphecy/Boundaries.lean:33-35
-- (boundary fact) (Boundaries.lean)
theorem emptyBody_unboundRet_not_scoped :
    emptyBodyUnboundRet.body = [] ∧ CalleeFreshBindings emptyBodyUnboundRet ∧
    ¬ CalleeScoped emptyBodyUnboundRet ∧ calleeBack emptyBodyUnboundRet 0 5 = 0

-- lean/ToyProphecy/Boundaries.lean:137-144
-- (boundary fact) (Boundaries.lean)
theorem reuseEndedCallee_harmless :
    CalleeScoped reuseEndedCallee ∧
    CalleeNoFrozenAccess reuseEndedCallee ∧
    CalleeNoUseAfterEnd reuseEndedCallee ∧
    ¬ CalleeFreshBindings reuseEndedCallee ∧
    (∀ a v, calleeBack reuseEndedCallee a v = v) ∧
    (∀ a c pf rf, ProphContract reuseEndedCallee a c pf rf ↔
      (calleeFwd reuseEndedCallee a = some c ∧ pf = calleeBack reuseEndedCallee a rf))

-- lean/ToyProphecy/Boundaries.lean:195-196
-- (boundary fact) (Boundaries.lean)
theorem calleeBack_masks_none_at_zero :
    calleeBack? cxCalleeRebind 0 0 = none ∧ calleeBack cxCalleeRebind 0 0 = 0

-- lean/ToyProphecy/Boundaries.lean:201-202
-- (boundary fact) (Boundaries.lean)
theorem calleeBackOpt_eq_some_of_calleeBack_eq_of_ne_zero (f : Callee) (a v : Int)
    (h : calleeBack f a v = v) (hv : v ≠ 0) : calleeBack? f a v = some v

-- lean/ToyProphecy/Boundaries.lean:219-220
-- (boundary fact) (Boundaries.lean)
theorem callDeep_omitAtEnd0_callee_still_resolved :
    ∀ σ', ProphOutcomeWith (ResPolicy.omitAtEnd 0) callDeep idStore σ' → σ' 1 = 15

-- lean/ToyProphecy/Boundaries.lean:240-241
-- (boundary fact) (Boundaries.lean)
theorem callDeep_std_excludes_spurious :
    ¬ ∃ σ', ProphOutcome callDeep idStore σ' ∧ σ' 0 = 7 ∧ σ' 1 = 7

-- lean/ToyProphecy/Boundaries.lean:253-257
-- (boundary fact, edge case) (Boundaries.lean)
theorem emptyProg_edge_case (σ : Store) :
    NoLentAccess [] ∧ NoFrozenAccess [] ∧ NoUseAfterEnd [] ∧
    FreshBindings [] ∧ AllEndedAtExit [] ∧
    backSem [] σ = refSem [] σ ∧
    (∀ σ', ProphOutcome [] σ σ' ↔ backSem [] σ = some σ')

-- lean/ToyProphecy/Boundaries.lean:274-281
-- (boundary fact, edge case) (Boundaries.lean)
theorem emptyCallee_edge_case :
    CalleeScoped emptyCallee ∧
    CalleeNoFrozenAccess emptyCallee ∧
    CalleeNoUseAfterEnd emptyCallee ∧
    CalleeFreshBindings emptyCallee ∧
    (∀ a v, calleeBack emptyCallee a v = v) ∧
    (∀ a c pf rf, ProphContract emptyCallee a c pf rf ↔
      (calleeFwd emptyCallee a = some c ∧ pf = calleeBack emptyCallee a rf))

-- lean/ToyProphecy/Boundaries.lean:307-311
-- (boundary fact, edge case) (Boundaries.lean)
theorem selSameLocal_edge_case (σ : Store) :
    NoLentAccess selSameLocal ∧ NoFrozenAccess selSameLocal ∧ NoUseAfterEnd selSameLocal ∧
    FreshBindings selSameLocal ∧ AllEndedAtExit selSameLocal ∧
    backSem selSameLocal σ = refSem selSameLocal σ ∧
    (∀ σ', ProphOutcome selSameLocal σ σ' ↔ refSem selSameLocal σ = some σ')
```

#### 2.1 Tightness counterexamples (all proved, canonical form: the other hypotheses hold and the conclusion fails)

| program | violates only | ref | back | proph (admitted, standard policy) |
| :--- | :--- | :--- | :--- | :--- |
| `cxLent` = `r0=&mut x0; *r0=5; x1=x0; *r0=9; end r0` | lent access | x0=9, x1=5 | x1=0 | x1=9 only (with r0 unresolved: x0=x1 only) |
| `cxFrozen` = `r0=&mut x0; r1=&mut *r0; *r1=7; x1=*r0; *r1=9; end r1; end r0` | frozen access | x1=7 | x1=0 | x1=9 only (also with r0 unresolved) |
| `cxAfterEnd` = `r0=&mut x0; r1=&mut *r0; end r1; *r1=4; end r0` | use after end | x0=4 | x0=0 | x0=0 |
| `cxAfterEndUnsat` = `r0=&mut x0; r1=&mut *r0; end r1; *r1=*r0+1; end r1; end r0` | use after end (twice) | x0=1 | x0=1 | **none** (constraints unsatisfiable, also with r0 unresolved) |
| `cxRebind` = `r0=&mut x0; *r0=5; r0=&mut x1; end r0` | rebind | x0=5 | x0=0 | any x0 (the real store is among them) |
| `cxUnended` = `r0=&mut x0; *r0=5` | unended at exit | x0=5 | x0=0 | any x0 (the real store is among them) |

- `back-sound`: `backSem_eq_refSem_tight_{noLentAccess, noFrozenAccess, noUseAfterEnd, freshBindings, allEndedAtExit}`.
- `agreement`: `prophOutcome_iff_backSem_tight_*` (use after end via `cxAfterEndUnsat`).
- `proph-sound`: `prophOutcome_iff_refSem_tight_*`.
- `proph-inclusion`: `prophOutcome_of_refSem_tight_{noLentAccess, noFrozenAccess, noUseAfterEnd}`
  (each also states `FreshBindings`); `FreshBindings` has tightness *unknown*.
- `omission-keeps-real`: `prophOutcomeWith_omitAtEnd_of_refSem_tight_{noLentAccess, noFrozenAccess, noUseAfterEnd}`
  with the omitted name `r = 0` (the borrow the program uses); `FreshBindings` unknown.
- `callee-summary-agreement`: `prophContract_iff_tight_{frozenAccess, useAfterEnd, rebind}`
  (callees `cxCalleeFrozen`, `cxCalleeAfterEnd`, `cxCalleeRebind`).
- `callee-back-projection`: `calleeBack_eq_final_tight_{scoped, rebind}` (callees `cxCalleeLocal`, `cxCalleeRebind`).

Non-vacuity: `richProg_nonvacuous`, `richProg_nonvacuous_other_branch`,
`inclusion_nonvacuous`, `omission_keeps_real_nonvacuous`, `deepCallee_nonvacuous`,
`prophOutcome_pos`.

### How the general results are proved

Basis: execution (Lean kernel check) for every statement in this subsection.
The proofs are in `lean/ToyProphecy/Sim/`; the five general statements of
`ToyProphecy/Results.lean` that are not derived from others are proved there.

- **The checker gets stuck exactly where the semantics do.** While the checker
  is not stuck, its `unborn` names are exactly the unbound reference variables of
  each semantic state (`BRel`), whatever violations occur. A checker step that
  gets stuck (a never-bound name, a local operation in a callee, an unscoped
  callee) makes the reference, backward and prophecy steps stuck as well
  (`runR_none_of_stuck`, `runB_none_of_stuck`, `runP_none_of_stuck`). So when the
  checker gets stuck, `refSem = none`, `backSem = none` and no store is admitted.
- **Clean steps.** The four hypotheses `NoLentAccess`, `NoFrozenAccess`,
  `NoUseAfterEnd`, `FreshBindings` together imply that the checker records no
  violation at all (`viol_nil_of_discipline`; `unendedAtExit` is only added by
  `violations` at the end). The `clean_*` lemmas give the exact checker state
  after each violation-free step.
- **Callee frames** (`Sim/CalleeBack.lean`, `Sim/Callee.lean`,
  `Sim/CalleeRun.lean`). For `calleeBack_eq_final_…`, an invariant assigns each
  bound borrow a depth greater than that of its parent (parameter at depth 0), so following parents from
  `f.ret` reaches the parameter within `f.body.length + 1` steps and every
  backward function forwards its argument unchanged. For
  `prophContract_iff_…`, the live borrows of a clean callee form one chain from
  the parameter to the active borrow (`CRel`); the returned name is the top of
  the chain, all names have the argument's address, and callee-exit resolutions
  force every prophecy of the chain to equal the parameter's prophecy. The
  existence direction chooses each new prophecy as the value its borrow will
  have when it ends (or the parameter's prophecy if it is still live at exit),
  read off the reference semantics of the remaining operations (`FVc`).
- **Main programs** (`Sim/MainDefs.lean` … `Sim/MainExist.lean`). The live
  borrows with address `x` form one chain whose bottom borrowed `x` directly and
  whose top is the only active borrow at `x` (`MRel`, chains listed by `ch x`).
  The relation ties the three semantic states together: locals with no chain
  have the same value in all three; the top of a chain has the reference value at
  its address as current value in both translations; each reborrow link stores
  the child's prophecy as the parent's current value and a backward function
  writing the parent; each chain bottom records its lender and, for a run-time
  selection, the value to restore in the candidate that was not chosen. Calls use
  the callee results above (`callee_summary`). Soundness (`m_run_sound`) follows
  any satisfying prophecy assignment; inclusion (`m_run_exist`) constructs one by
  choosing each new prophecy as the reference value of its borrow at its end, or
  at the end of the program if it never ends (`FVm`). With `AllEndedAtExit`
  there is no live borrow at the end, so all chains are empty and the three final
  stores coincide.

### Result cards

#### `back-sound` — theorem, T1, substantive

**Lean:** `Toy.Prophecy.backSem_eq_refSem_of_discipline`

**Plain claim.** For every toy program that obeys all five parts of the borrow discipline (no access to lent locals, no access to reborrowed borrows, no use after end, fresh borrow names, every borrow ended by the end) and every initial store, the backward-function translation computes exactly the reference semantics' outcome: the same final store, or stuck exactly when the reference semantics is stuck.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Results.lean:33-36
-- lean/ToyProphecy/Results.lean
theorem backSem_eq_refSem_of_discipline (P : Prog) (σ : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) :
    backSem P σ = refSem P σ
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def refSem (P : Prog) (σ : Store) : Option Store := (runR (RState.init σ) P).map (·.store)
def backSem (P : Prog) (σ : Store) : Option Store := (runB (BState.init σ) P).map (·.store)
def ProphOutcomeWith (pol : ResPolicy) (P : Prog) (σ σ' : Store) : Prop :=
  ∃ φ : Nat → Int, ∃ s : PState,
    runP pol φ 0 (PState.init σ) P = some s ∧ Sat s.cs ∧ s.store = σ'
def ProphOutcome (P : Prog) (σ σ' : Store) : Prop := ProphOutcomeWith ResPolicy.std P σ σ'
def Sat (cs : List (Int × Int)) : Prop := ∀ c ∈ cs, c.1 = c.2
def Avoids (k : Violation) (P : Prog) : Prop := k ∉ violations P
abbrev NoLentAccess (P : Prog) : Prop := Avoids .lentAccess P
abbrev NoFrozenAccess (P : Prog) : Prop := Avoids .frozenAccess P
abbrev NoUseAfterEnd (P : Prog) : Prop := Avoids .useAfterEnd P
abbrev FreshBindings (P : Prog) : Prop := Avoids .rebind P
abbrev AllEndedAtExit (P : Prog) : Prop := Avoids .unendedAtExit P
def violations (P : Prog) : List Violation :=
  let c := checkStmts CState.init P
  if !c.stuck && c.bound.any (fun r => c.status r = .active || c.status r = .frozen) then
    c.viol ++ [.unendedAtExit]
  else c.viol
```

**Tier.** T1 — Folklore made precise: the Aeneas papers present backward functions as a functional translation of borrow-checked code and leave a proof of correctness of the translation to future work. Literature search (bibliographic data via publisher metadata, HAL and arXiv; content via arXiv, HAL and author copies; mechanized developments searched in public Iris/Coq, Isabelle AFP and Lean repositories): no mechanized or paper statement relating backward-function and prophecy encodings of mutable borrows was found; RustHorn proves its CHC representation correct on paper and RustHornBelt mechanizes soundness of RustHorn-style verification, each for its own calculus; the Aeneas papers leave correctness of the functional translation to future work.

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness |
| :--- | :--- | :--- |
| `hL : NoLentAccess P` | A lent local is neither read, assigned, nor borrowed until its borrow ends. The backward translation leaves a lent local at its old value until the borrow ends, while the reference semantics updates it in place, so a read of the lent local differs (cxLent). | tight: counterexample `Toy.Prophecy.backSem_eq_refSem_tight_noLentAccess` |
| `hF : NoFrozenAccess P` | A reborrowed borrow is not used until the reborrow ends. In the backward translation its current value is stale until the reborrow's backward function writes it back, while the reference semantics reads the shared address (cxFrozen). | tight: counterexample `Toy.Prophecy.backSem_eq_refSem_tight_noFrozenAccess` |
| `hE : NoUseAfterEnd P` | A borrow is not used after its end. In the backward translation a write after the end changes only the ended borrow's slot and is never written back, while the reference semantics performs it (cxAfterEnd). | tight: counterexample `Toy.Prophecy.backSem_eq_refSem_tight_noUseAfterEnd` |
| `hB : FreshBindings P` | Every borrow-creating statement binds a name not bound before in its frame (syntactic single assignment of borrow names per frame). This also rejects reusing the name of a borrow that has already ended, which is stricter than forbidding the overwrite of a live borrow; on the example rebindEnded that reuse is harmless for both translations (rebindEnded_harmless). Rebinding a live name leaks that borrow, whose backward function is then never applied (cxRebind). | tight: counterexample `Toy.Prophecy.backSem_eq_refSem_tight_freshBindings` |
| `hX : AllEndedAtExit P` | Every borrow of the main program has ended when the program ends. An unended borrow's backward function is never applied, so its lender keeps its old value, while the reference semantics has updated it in place (cxUnended). | tight: counterexample `Toy.Prophecy.backSem_eq_refSem_tight_allEndedAtExit` |

**Depth.** substantive — Requires a simulation invariant relating address-based states to backward states across nested reborrows, run-time selection, and calls (each call composing a callee summary).

**Non-vacuity.** richProg (run-time selection, two nested reborrows, a call returning a reborrow two levels deep, writes after reborrow ends, a read of the lender after the end) satisfies all five properties; from x |-> x both semantics end with (x0, x1, x2) = (1116, 1, 1116), and from the zero store with (0, 1116, 0). (`Toy.Prophecy.richProg_nonvacuous`, `Toy.Prophecy.richProg_nonvacuous_other_branch`)

**Prior art.** [S1] Son Ho, Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), Article 116, pp. 711-741, 2022, doi:10.1145/3547647 (long version arXiv:2206.07185v2); [S2] Son Ho, Aymeric Fromherz, Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024, doi:10.1145/3674640 (long version arXiv:2404.02680); [S3] Son Ho. Formal Verification of Rust Programs by Functional Translation. PhD thesis, Université PSL (prepared at Inria Paris), defended 9 December 2024, HAL tel-05004605; [S4] Sebastian Ullrich. Simple Verification of Rust Programs via Functional Purification. Master's thesis, Karlsruhe Institute of Technology (KIT), 2016. Full records and what each source says are under Evidence.

**Design question.** Is a backward-function (functional) translation of mutable borrows sound for straight-line code with nested reborrows, run-time selection, and calls returning borrows, and which parts of the borrow discipline does it rely on?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the toy `backSem` follows the description of backward functions in [S1] (one backward function per borrow, applied when the borrow ends, returning the new lender values from the borrow's final value). The theorem therefore suggests, but does not establish, that such translations behave as stated for the corresponding fragment of Rust under a borrow discipline at least as strict as the hypotheses; the gaps listed under Applicability (lazy borrow ending, inferred lifetimes, shared borrows, loops and branches, compound values, unsafe code) are not covered.

---

#### `agreement` — theorem, T1, substantive

**Lean:** `Toy.Prophecy.prophOutcome_iff_backSem_of_discipline`

**Plain claim.** For every toy program obeying all five parts of the borrow discipline and every initial store, the final stores admitted by the prophecy translation (over all prophecy assignments satisfying every resolution constraint, standard resolution policy) are exactly the backward-function translation's result: exactly that store if it succeeds, none if it is stuck.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Results.lean:46-49
-- lean/ToyProphecy/Results.lean
theorem prophOutcome_iff_backSem_of_discipline (P : Prog) (σ : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) :
    ∀ σ', ProphOutcome P σ σ' ↔ backSem P σ = some σ'
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def refSem (P : Prog) (σ : Store) : Option Store := (runR (RState.init σ) P).map (·.store)
def backSem (P : Prog) (σ : Store) : Option Store := (runB (BState.init σ) P).map (·.store)
def ProphOutcomeWith (pol : ResPolicy) (P : Prog) (σ σ' : Store) : Prop :=
  ∃ φ : Nat → Int, ∃ s : PState,
    runP pol φ 0 (PState.init σ) P = some s ∧ Sat s.cs ∧ s.store = σ'
def ProphOutcome (P : Prog) (σ σ' : Store) : Prop := ProphOutcomeWith ResPolicy.std P σ σ'
def Sat (cs : List (Int × Int)) : Prop := ∀ c ∈ cs, c.1 = c.2
def Avoids (k : Violation) (P : Prog) : Prop := k ∉ violations P
abbrev NoLentAccess (P : Prog) : Prop := Avoids .lentAccess P
abbrev NoFrozenAccess (P : Prog) : Prop := Avoids .frozenAccess P
abbrev NoUseAfterEnd (P : Prog) : Prop := Avoids .useAfterEnd P
abbrev FreshBindings (P : Prog) : Prop := Avoids .rebind P
abbrev AllEndedAtExit (P : Prog) : Prop := Avoids .unendedAtExit P
def violations (P : Prog) : List Violation :=
  let c := checkStmts CState.init P
  if !c.stuck && c.bound.any (fun r => c.status r = .active || c.status r = .frozen) then
    c.viol ++ [.unendedAtExit]
  else c.viol
```

**Tier.** T1 — That a prophecy stands for the value at which the borrow's backward function is eventually applied is informal folklore: the cited papers present the two encodings as alternatives, and none states their agreement. Literature search (bibliographic data via publisher metadata, HAL and arXiv; content via arXiv, HAL and author copies; mechanized developments searched in public Iris/Coq, Isabelle AFP and Lean repositories): no mechanized or paper statement relating backward-function and prophecy encodings of mutable borrows was found; RustHorn proves its CHC representation correct on paper and RustHornBelt mechanizes soundness of RustHorn-style verification, each for its own calculus; the Aeneas papers leave correctness of the functional translation to future work.

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness |
| :--- | :--- | :--- |
| `hL : NoLentAccess P` | Reading a lent local sees the borrow's prophecy (its final value) in the prophecy translation and the lender's old value in the backward translation (cxLent). | tight: counterexample `Toy.Prophecy.prophOutcome_iff_backSem_tight_noLentAccess` |
| `hF : NoFrozenAccess P` | Reading a reborrowed borrow sees the reborrow's prophecy in the prophecy translation and a stale current value in the backward translation (cxFrozen). | tight: counterexample `Toy.Prophecy.prophOutcome_iff_backSem_tight_noFrozenAccess` |
| `hE : NoUseAfterEnd P` | Ending a borrow a second time emits a second resolution constraint; after an intervening write the two constraints contradict each other, so the prophecy translation admits no store while the backward translation succeeds (cxAfterEndUnsat). A single write after the end (cxAfterEnd) is lost by both translations and does not by itself break agreement. | tight: counterexample `Toy.Prophecy.prophOutcome_iff_backSem_tight_noUseAfterEnd` |
| `hB : FreshBindings P` | Every borrow-creating statement binds a name not bound before in its frame (syntactic single assignment of borrow names per frame). This also rejects reusing the name of a borrow that has already ended, which is stricter than forbidding the overwrite of a live borrow; on the example rebindEnded that reuse is harmless for both translations (rebindEnded_harmless). Rebinding a live name leaks a borrow: its prophecy is never resolved, so the prophecy translation admits extra stores, while the backward translation never writes the leaked borrow back (cxRebind). | tight: counterexample `Toy.Prophecy.prophOutcome_iff_backSem_tight_freshBindings` |
| `hX : AllEndedAtExit P` | An unended borrow's prophecy is never resolved, so the prophecy translation admits extra stores, while the backward translation leaves its lender at the old value (cxUnended). | tight: counterexample `Toy.Prophecy.prophOutcome_iff_backSem_tight_allEndedAtExit` |

**Depth.** substantive — Needs both existence (an assignment, namely each prophecy's resolved value, that satisfies all constraints and yields the backward result) and uniqueness of the final store over all satisfying assignments, through chains of equalities between prophecies created at callee exit.

**Non-vacuity.** richProg satisfies all five properties; the backward result from x |-> x is (1116, 1, 1116) and the prophecy translation admits a store with these values (prophecy assignment [1116, 11, 11, 116, 13, 116, 116]). (`Toy.Prophecy.richProg_nonvacuous`)

**Prior art.** [S1] Son Ho, Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), Article 116, pp. 711-741, 2022, doi:10.1145/3547647 (long version arXiv:2206.07185v2); [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205; [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878); [S7] Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, Derek Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022, pp. 841-856, doi:10.1145/3519939.3523704 (HAL hal-03777103); [S8] Vytautas Astrauskas, Peter Müller, Federico Poli, Alexander J. Summers. Leveraging Rust Types for Modular Specification and Verification. Proc. ACM Program. Lang. 3(OOPSLA), Article 147, 2019, doi:10.1145/3360573; [S9] Martín Abadi, Leslie Lamport. The Existence of Refinement Mappings. Theoretical Computer Science 82(2), pp. 253-284, 1991, doi:10.1016/0304-3975(91)90224-P (abridged version: LICS 1988, pp. 165-175, doi:10.1109/LICS.1988.5115). Full records and what each source says are under Evidence.

**Design question.** When do the backward-function and prophecy encodings of mutable borrows agree, and under exactly which parts of the borrow discipline?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the toy `backSem` follows the description of backward functions in [S1] (one backward function per borrow, applied when the borrow ends, returning the new lender values from the borrow's final value) and the toy prophecy translation follows the (current, final) encoding with resolution at the end of the borrow described in [S5] and [S6]. The theorem therefore suggests, but does not establish, that such translations behave as stated for the corresponding fragment of Rust under a borrow discipline at least as strict as the hypotheses; the gaps listed under Applicability (lazy borrow ending, inferred lifetimes, shared borrows, loops and branches, compound values, unsafe code) are not covered.

---

#### `proph-sound` — theorem, T1, shallow

**Lean:** `Toy.Prophecy.prophOutcome_iff_refSem_of_discipline`

**Plain claim.** For every toy program obeying all five parts of the borrow discipline and every initial store, the prophecy translation (standard policy) admits exactly the reference semantics' outcome: that store and no other if the program succeeds, nothing if it is stuck.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Results.lean:60-63
-- lean/ToyProphecy/Results.lean
theorem prophOutcome_iff_refSem_of_discipline (P : Prog) (σ : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P) (hX : AllEndedAtExit P) :
    ∀ σ', ProphOutcome P σ σ' ↔ refSem P σ = some σ'
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def refSem (P : Prog) (σ : Store) : Option Store := (runR (RState.init σ) P).map (·.store)
def backSem (P : Prog) (σ : Store) : Option Store := (runB (BState.init σ) P).map (·.store)
def ProphOutcomeWith (pol : ResPolicy) (P : Prog) (σ σ' : Store) : Prop :=
  ∃ φ : Nat → Int, ∃ s : PState,
    runP pol φ 0 (PState.init σ) P = some s ∧ Sat s.cs ∧ s.store = σ'
def ProphOutcome (P : Prog) (σ σ' : Store) : Prop := ProphOutcomeWith ResPolicy.std P σ σ'
def Sat (cs : List (Int × Int)) : Prop := ∀ c ∈ cs, c.1 = c.2
def Avoids (k : Violation) (P : Prog) : Prop := k ∉ violations P
abbrev NoLentAccess (P : Prog) : Prop := Avoids .lentAccess P
abbrev NoFrozenAccess (P : Prog) : Prop := Avoids .frozenAccess P
abbrev NoUseAfterEnd (P : Prog) : Prop := Avoids .useAfterEnd P
abbrev FreshBindings (P : Prog) : Prop := Avoids .rebind P
abbrev AllEndedAtExit (P : Prog) : Prop := Avoids .unendedAtExit P
def violations (P : Prog) : List Violation :=
  let c := checkStmts CState.init P
  if !c.stuck && c.bound.any (fun r => c.status r = .active || c.status r = .frozen) then
    c.viol ++ [.unendedAtExit]
  else c.viol
```

**Tier.** T1 — RustHorn proves correctness of its CHC representation for its core calculus on paper and RustHornBelt mechanizes soundness of RustHorn-style verification; this is the same idea restated over this toy language and its reference semantics, which is not one of theirs.

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness |
| :--- | :--- | :--- |
| `hL : NoLentAccess P` | Reading a lent local sees the borrow's prophecy (its final value) in the prophecy translation, but the present value in the reference semantics (cxLent). | tight: counterexample `Toy.Prophecy.prophOutcome_iff_refSem_tight_noLentAccess` |
| `hF : NoFrozenAccess P` | Reading a reborrowed borrow sees the reborrow's prophecy instead of the present value of the shared address (cxFrozen). | tight: counterexample `Toy.Prophecy.prophOutcome_iff_refSem_tight_noFrozenAccess` |
| `hE : NoUseAfterEnd P` | A write after the end comes after the resolution: the reference semantics performs it, while the lender's admitted value ignores it (cxAfterEnd). | tight: counterexample `Toy.Prophecy.prophOutcome_iff_refSem_tight_noUseAfterEnd` |
| `hB : FreshBindings P` | Every borrow-creating statement binds a name not bound before in its frame (syntactic single assignment of borrow names per frame). This also rejects reusing the name of a borrow that has already ended, which is stricter than forbidding the overwrite of a live borrow; on the example rebindEnded that reuse is harmless for both translations (rebindEnded_harmless). A leaked borrow (a live name rebound) is never resolved, so the prophecy translation admits stores other than the real one (cxRebind). | tight: counterexample `Toy.Prophecy.prophOutcome_iff_refSem_tight_freshBindings` |
| `hX : AllEndedAtExit P` | An unended borrow is never resolved, so the prophecy translation admits stores other than the real one (cxUnended). | tight: counterexample `Toy.Prophecy.prophOutcome_iff_refSem_tight_allEndedAtExit` |

**Depth.** shallow — Two rewrites from back-sound and agreement; all substance is in those two statements.

**Non-vacuity.** richProg (run-time selection, two nested reborrows, a call returning a reborrow two levels deep, writes after reborrow ends, a read of the lender after the end) satisfies all five properties; from x |-> x the reference semantics ends with (x0, x1, x2) = (1116, 1, 1116) and the prophecy translation admits a store with these values (prophecy assignment [1116, 11, 11, 116, 13, 116, 116]). (`Toy.Prophecy.richProg_nonvacuous`)

**Prior art.** [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205; [S7] Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, Derek Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022, pp. 841-856, doi:10.1145/3519939.3523704 (HAL hal-03777103); [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878); [S9] Martín Abadi, Leslie Lamport. The Existence of Refinement Mappings. Theoretical Computer Science 82(2), pp. 253-284, 1991, doi:10.1016/0304-3975(91)90224-P (abridged version: LICS 1988, pp. 165-175, doi:10.1109/LICS.1988.5115); [S10] Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers, Derek Dreyer. RefinedRust: A Type System for High-Assurance Verification of Rust Programs. Proc. ACM Program. Lang. 8(PLDI), Article 192, pp. 1115-1139, 2024, doi:10.1145/3656422; [S11] Sacha-Élie Ayoun, Xavier Denis, Petar Maksimović, Philippa Gardner. A Hybrid Approach to Semi-automated Rust Verification. Proc. ACM Program. Lang. 9(PLDI), pp. 970-992, 2025, doi:10.1145/3729289 (extended version arXiv:2403.15122); [S12] Hiromi Ogawa, Taro Sekiyama, Hiroshi Unno. Thrust: A Prophecy-Based Refinement Type System for Rust. Proc. ACM Program. Lang. 9(PLDI), Article 230, pp. 2056-2080, 2025, doi:10.1145/3729333. Full records and what each source says are under Evidence.

**Design question.** Is a prophecy encoding of mutable borrows sound and precise for straight-line code with nested reborrows, run-time selection, and calls returning borrows?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the toy prophecy translation follows the (current, final) encoding with resolution at the end of the borrow described in [S5] and [S6], and the comparison is with the toy reference semantics `refSem`, not with the backward-function translation. The theorem therefore suggests, but does not establish, that such translations behave as stated for the corresponding fragment of Rust under a borrow discipline at least as strict as the hypotheses; the gaps listed under Applicability (lazy borrow ending, inferred lifetimes, shared borrows, loops and branches, compound values, unsafe code) are not covered.

---

#### `proph-inclusion` — theorem, T1, substantive

**Lean:** `Toy.Prophecy.prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`

**Plain claim.** For every toy program with no access to lent locals, no access to reborrowed borrows, no use of a borrow after its end, and fresh borrow names, and every initial store: if the reference semantics produces a final store, the prophecy translation (standard policy) admits that store; ending every borrow by the end of the program is not assumed.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Results.lean:76-80
-- lean/ToyProphecy/Results.lean
theorem prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings
    (P : Prog) (σ σ' : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P)
    (h : refSem P σ = some σ') : ProphOutcome P σ σ'
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def refSem (P : Prog) (σ : Store) : Option Store := (runR (RState.init σ) P).map (·.store)
def backSem (P : Prog) (σ : Store) : Option Store := (runB (BState.init σ) P).map (·.store)
def ProphOutcomeWith (pol : ResPolicy) (P : Prog) (σ σ' : Store) : Prop :=
  ∃ φ : Nat → Int, ∃ s : PState,
    runP pol φ 0 (PState.init σ) P = some s ∧ Sat s.cs ∧ s.store = σ'
def ProphOutcome (P : Prog) (σ σ' : Store) : Prop := ProphOutcomeWith ResPolicy.std P σ σ'
def Sat (cs : List (Int × Int)) : Prop := ∀ c ∈ cs, c.1 = c.2
def Avoids (k : Violation) (P : Prog) : Prop := k ∉ violations P
abbrev NoLentAccess (P : Prog) : Prop := Avoids .lentAccess P
abbrev NoFrozenAccess (P : Prog) : Prop := Avoids .frozenAccess P
abbrev NoUseAfterEnd (P : Prog) : Prop := Avoids .useAfterEnd P
abbrev FreshBindings (P : Prog) : Prop := Avoids .rebind P
abbrev AllEndedAtExit (P : Prog) : Prop := Avoids .unendedAtExit P
def violations (P : Prog) : List Violation :=
  let c := checkStmts CState.init P
  if !c.stuck && c.bound.any (fun r => c.status r = .active || c.status r = .frozen) then
    c.viol ++ [.unendedAtExit]
  else c.viol
```

**Tier.** T1 — That an unresolved prophecy only adds behaviours, so that leaving a borrow unended cannot exclude real executions, is implicit in assume-based encodings; no statement separating the parts of the discipline needed for inclusion from those needed for precision was found. Literature search (bibliographic data via publisher metadata, HAL and arXiv; content via arXiv, HAL and author copies; mechanized developments searched in public Iris/Coq, Isabelle AFP and Lean repositories): no mechanized or paper statement relating backward-function and prophecy encodings of mutable borrows was found; RustHorn proves its CHC representation correct on paper and RustHornBelt mechanizes soundness of RustHorn-style verification, each for its own calculus; the Aeneas papers leave correctness of the functional translation to future work.

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness |
| :--- | :--- | :--- |
| `hL : NoLentAccess P` | Otherwise a read of a lent local sees the borrow's final value (its prophecy), which differs from the present value the program reads (cxLent). | tight: counterexample `Toy.Prophecy.prophOutcome_of_refSem_tight_noLentAccess` |
| `hF : NoFrozenAccess P` | Otherwise a read through a reborrowed borrow sees the reborrow's final value (cxFrozen). | tight: counterexample `Toy.Prophecy.prophOutcome_of_refSem_tight_noFrozenAccess` |
| `hE : NoUseAfterEnd P` | Otherwise a second end of a borrow can contradict its first resolution, so that no store at all is admitted (cxAfterEndUnsat). | tight: counterexample `Toy.Prophecy.prophOutcome_of_refSem_tight_noUseAfterEnd` |
| `hB : FreshBindings P` | Every borrow-creating statement binds a name not bound before in its frame (syntactic single assignment of borrow names per frame). This also rejects reusing the name of a borrow that has already ended, which is stricter than forbidding the overwrite of a live borrow; on the example rebindEnded that reuse is harmless for both translations (rebindEnded_harmless). So no borrow is leaked by rebinding. Tightness unknown: no program is known that satisfies the other three hypotheses, violates this one, and has its real outcome excluded. Rebinding can hide a frozen access from a checker that keeps lender links by name across the rebinding; this checker drops those links, so such a program is rejected for its frozen access (rebindThenFrozenRead_violations), and for that program the real outcome is indeed excluded (rebindThenFrozenRead_real_excluded). In one example with a leaked borrow the real outcome is admitted (cxRebind_real_outcome_admitted). | unknown |
| `h : refSem P σ = some σ'` | The premise: the store being included is the program's outcome. | harmless |

**Depth.** substantive — Needs a witness assignment for prophecies that are never resolved (borrows that never end) and an invariant that such prophecies sit only in places the discipline makes unobservable.

**Non-vacuity.** richProg satisfies all four hypotheses (and AllEndedAtExit); cxUnended (a borrow never ended) satisfies the four hypotheses but not AllEndedAtExit. For both, the real outcome is admitted. (`Toy.Prophecy.inclusion_nonvacuous`)

**Prior art.** [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205; [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878); [S7] Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, Derek Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022, pp. 841-856, doi:10.1145/3519939.3523704 (HAL hal-03777103); [S9] Martín Abadi, Leslie Lamport. The Existence of Refinement Mappings. Theoretical Computer Science 82(2), pp. 253-284, 1991, doi:10.1016/0304-3975(91)90224-P (abridged version: LICS 1988, pp. 165-175, doi:10.1109/LICS.1988.5115). Full records and what each source says are under Evidence.

**Design question.** What does a prophecy encoding need in order not to exclude real executions (verification soundness), as opposed to admitting nothing else (precision)? In particular, what goes wrong if a prophecy is never resolved because its borrow never ends?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the toy prophecy translation follows the (current, final) encoding with resolution at the end of the borrow described in [S5] and [S6], and the comparison is with the toy reference semantics `refSem`, not with the backward-function translation. The theorem therefore suggests, but does not establish, that such translations behave as stated for the corresponding fragment of Rust under a borrow discipline at least as strict as the hypotheses; the gaps listed under Applicability (lazy borrow ending, inferred lifetimes, shared borrows, loops and branches, compound values, unsafe code) are not covered.

---

#### `omission-monotone` — theorem, T0, shallow

**Lean:** `Toy.Prophecy.prophOutcomeWith_omitAtEnd_of_prophOutcome`

**Plain claim.** For every toy program, initial store, and borrow name r, every final store admitted by the prophecy translation under the standard policy is still admitted when no `endBorrow r` statement of the main program emits its resolution constraint (every end of the name r is unresolved, callee frames unaffected); no discipline hypothesis is needed.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Results.lean:89-90
-- lean/ToyProphecy/Results.lean
theorem prophOutcomeWith_omitAtEnd_of_prophOutcome (r : RefVar) (P : Prog) (σ σ' : Store)
    (h : ProphOutcome P σ σ') : ProphOutcomeWith (ResPolicy.omitAtEnd r) P σ σ'
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def ResPolicy.std : ResPolicy :=
  { atEnd := fun _ => true, atCalleeExit := true, early := fun _ => [] }
def ResPolicy.omitAtEnd (r : RefVar) : ResPolicy :=
  { ResPolicy.std with atEnd := fun r' => decide (r' ≠ r) }
-- ProphOutcome, refSem and the discipline properties as in the definitions above
```

**Tier.** T0 — Re-derivation: dropping an assumed equation can only enlarge the set of admitted executions.

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness |
| :--- | :--- | :--- |
| `h : ProphOutcome P σ σ'` | The premise: the store is admitted under the standard policy. | harmless |

**Depth.** shallow — Same runs under the same prophecy assignment, with the emitted constraints a sub-collection (proved by a step-by-step simulation, runP_omitAtEnd_sim).

**Non-vacuity.** writeThenRead: its outcome is admitted under the standard policy and still admitted with r0's resolution omitted. (`Toy.Prophecy.prophOutcome_pos`, `Toy.Prophecy.omitting_resolution_keeps_real_store_writeThenRead`)

**Prior art.** [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878). Full records and what each source says are under Evidence.

**Design question.** What goes wrong if a prophecy is never resolved: can it make the encoding unsound, or only imprecise?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the resolution policies model where a prophecy-based verifier inserts the equation `final = current` ([S5] Sec. 3.2, [S6] Sec. 3.2); `ResPolicy.omitAtEnd r` models leaving out that equation (the end-of-borrow assumption) at every `endBorrow r` of the main program. The theorem shows that in this toy model, for every program, leaving out those assumptions can only enlarge the set of admitted stores, never remove one; it is evidence about verifiers built that way only by analogy, not a statement about any implementation.

---

#### `omission-keeps-real` — theorem, T1, shallow

**Lean:** `Toy.Prophecy.prophOutcomeWith_omitAtEnd_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings`

**Plain claim.** For every toy program with no access to lent locals, no access to reborrowed borrows, no use after end, and fresh borrow names, every initial store, and every borrow name r: if the reference semantics produces a final store, the prophecy translation still admits it when no `endBorrow r` statement of the main program emits its resolution constraint (ResPolicy.omitAtEnd r, keyed by the name r; callee bodies and callee-exit resolutions are unaffected); so for such programs omitting the end-of-borrow resolutions of a main-program borrow name never excludes the real outcome.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Results.lean:104-108
-- lean/ToyProphecy/Results.lean
theorem prophOutcomeWith_omitAtEnd_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings
    (r : RefVar) (P : Prog) (σ σ' : Store)
    (hL : NoLentAccess P) (hF : NoFrozenAccess P) (hE : NoUseAfterEnd P)
    (hB : FreshBindings P)
    (h : refSem P σ = some σ') : ProphOutcomeWith (ResPolicy.omitAtEnd r) P σ σ'
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def ResPolicy.std : ResPolicy :=
  { atEnd := fun _ => true, atCalleeExit := true, early := fun _ => [] }
def ResPolicy.omitAtEnd (r : RefVar) : ResPolicy :=
  { ResPolicy.std with atEnd := fun r' => decide (r' ≠ r) }
-- ProphOutcome, refSem and the discipline properties as in the definitions above
```

**Tier.** T1 — Folklore made precise: in assume-based prophecy encodings an omitted resolution is a missing assumption; this combines the inclusion statement (proph-inclusion) with the omission statement (omission-monotone) for the toy language.

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness |
| :--- | :--- | :--- |
| `hL : NoLentAccess P` | Otherwise a read of a lent local sees the borrow's final value. With the resolution of r0 omitted, cxLent (which reads x0 while r0 lends it) admits only stores with x0 = x1, while the program ends with x0 = 9, x1 = 5. | tight: counterexample `Toy.Prophecy.prophOutcomeWith_omitAtEnd_of_refSem_tight_noLentAccess` |
| `hF : NoFrozenAccess P` | Otherwise a read through a reborrowed borrow sees the reborrow's final value. With the resolution of r0 omitted, cxFrozen admits only stores with x1 = 9, while the program ends with x1 = 7. | tight: counterexample `Toy.Prophecy.prophOutcomeWith_omitAtEnd_of_refSem_tight_noFrozenAccess` |
| `hE : NoUseAfterEnd P` | Otherwise a second end of a borrow can contradict its first resolution. With the resolution of r0 omitted, cxAfterEndUnsat still has contradictory constraints (from the two ends of r1) and admits no store. | tight: counterexample `Toy.Prophecy.prophOutcomeWith_omitAtEnd_of_refSem_tight_noUseAfterEnd` |
| `hB : FreshBindings P` | Every borrow-creating statement binds a name not bound before in its frame (syntactic single assignment of borrow names per frame). This also rejects reusing the name of a borrow that has already ended, which is stricter than forbidding the overwrite of a live borrow; on the example rebindEnded that reuse is harmless for both translations (rebindEnded_harmless). So no borrow is leaked by rebinding. Tightness unknown: no program is known that satisfies the other three hypotheses, violates this one, and has its real outcome excluded with some name's end-of-borrow resolutions omitted. Because omission only adds admitted stores (omission-monotone, proved), such a program would also have its real outcome excluded under the standard policy, so it would also show that the inclusion statement (proph-inclusion) needs FreshBindings, which is open as well. | unknown |
| `h : refSem P σ = some σ'` | The premise: the store being included is the program's outcome. | harmless |

**Depth.** shallow — One-line composition of proph-inclusion and omission-monotone.

**Non-vacuity.** With r = 0: writeThenRead satisfies the four hypotheses (and AllEndedAtExit) and cxUnended satisfies them but not AllEndedAtExit; for both, the real outcome is admitted when r0's resolution is omitted. (`Toy.Prophecy.omission_keeps_real_nonvacuous`)

**Prior art.** [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878); [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205. Full records and what each source says are under Evidence.

**Design question.** What goes wrong if a prophecy is never resolved: can it make the encoding unsound, or only imprecise?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the resolution policies model where a prophecy-based verifier inserts the equation `final = current` ([S5] Sec. 3.2, [S6] Sec. 3.2); `ResPolicy.omitAtEnd r` models leaving out that equation (the end-of-borrow assumption) at every `endBorrow r` of the main program. The theorem shows that in this toy model, for programs satisfying the four hypotheses (ending every borrow is not assumed), leaving out those assumptions never excludes the real outcome; it is evidence about verifiers built that way only by analogy, not a statement about any implementation.

---

#### `resolution-necessary` — counterexample, T1, shallow

**Lean:** `Toy.Prophecy.omitting_resolution_admits_unproducible_store`

**Plain claim.** The program `r0 = &mut x0; *r0 = 5; end r0; x1 = x0` obeys all five parts of the borrow discipline, yet, started from the zero store, if the resolution of r0 at its end is omitted, the prophecy translation admits a final store with x0 = x1 = 7, which the program (whose only outcome from the zero store has x0 = x1 = 5) cannot produce.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Resolution.lean:59-63
-- lean/ToyProphecy/Resolution.lean
theorem omitting_resolution_admits_unproducible_store :
    NoLentAccess writeThenRead ∧ NoFrozenAccess writeThenRead ∧ NoUseAfterEnd writeThenRead ∧
    FreshBindings writeThenRead ∧ AllEndedAtExit writeThenRead ∧
    ∃ σ', ProphOutcomeWith (ResPolicy.omitAtEnd 0) writeThenRead zeroStore σ' ∧
      σ' 0 = 7 ∧ σ' 1 = 7 ∧ refSem writeThenRead zeroStore ≠ some σ'
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def zeroStore : Store := fun _ => 0
def idStore : Store := fun x => (x : Int)
def writeThenRead : Prog :=   -- r0 = &mut x0; *r0 = 5; end r0; x1 = x0
  [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0), op (assign 1 (var 0))]
def writeOnce : Prog := [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0)]
def deepCallee : Callee :=
  { body := [reborrow 1 0, write 1 (add (deref 1) (lit 2)), endBorrow 1,
             write 0 (add (deref 0) (lit 3)), reborrow 2 0, reborrow 3 2], ret := 3 }
def callDeep : Prog :=
  [op (borrow 0 0), call 1 deepCallee 0, op (write 1 (add (deref 1) (lit 10))),
   op (endBorrow 1), op (assign 1 (deref 0)), op (endBorrow 0)]
def ResPolicy.omitAtEnd (r : RefVar) : ResPolicy :=
  { ResPolicy.std with atEnd := fun r' => decide (r' ≠ r) }
def ResPolicy.omitAtCalleeExit : ResPolicy := { ResPolicy.std with atCalleeExit := false }
def ResPolicy.resolveAfter (i : Nat) (r : RefVar) : ResPolicy :=
  { atEnd := fun r' => decide (r' ≠ r), atCalleeExit := true,
    early := fun j => if j = i then [r] else [] }
```

**Tier.** T1 — Folklore made precise: the cited prophecy encodings resolve every borrow when it ends; this is a concrete mechanized instance of what goes wrong without it.

**Hypothesis ledger.** None: a concrete statement about named programs.

**Depth.** shallow — Evaluation of a four-statement program under two prophecy assignments.

**Non-vacuity.** The counterexample is itself concrete; the program's real outcome is still admitted with omission (omitting_resolution_keeps_real_store_writeThenRead). (`Toy.Prophecy.omitting_resolution_keeps_real_store_writeThenRead`)

**Positive control.** Under the standard policy the same program's admitted stores from the zero store are exactly its outcome. (`Toy.Prophecy.prophOutcome_writeThenRead_iff`)

**Prior art.** [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878); [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205; [S13] Ralf Jung, Rodolphe Lepigre, Gaurav Parthasarathy, Marianna Rapoport, Amin Timany, Derek Dreyer, Bart Jacobs. The Future is Ours: Prophecy Variables in Separation Logic. Proc. ACM Program. Lang. 4(POPL), Article 45, 2020, doi:10.1145/3371113; [S9] Martín Abadi, Leslie Lamport. The Existence of Refinement Mappings. Theoretical Computer Science 82(2), pp. 253-284, 1991, doi:10.1016/0304-3975(91)90224-P (abridged version: LICS 1988, pp. 165-175, doi:10.1109/LICS.1988.5115). Full records and what each source says are under Evidence.

**Design question.** What goes wrong if a prophecy is never resolved?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the resolution policies model where a prophecy-based verifier inserts the equation `final = current` ([S5] Sec. 3.2, [S6] Sec. 3.2). The example shows what goes wrong in this toy model when that equation is omitted or moved; it is evidence about verifiers built that way only by analogy, not a statement about any implementation.

---

#### `premature-resolution` — counterexample, T1, shallow

**Lean:** `Toy.Prophecy.premature_resolution_excludes_real_store`

**Plain claim.** For `r0 = &mut x0; *r0 = 5; end r0` (which obeys all five parts of the discipline) started from the zero store, resolving r0 right after its creation instead of at its end makes every admitted final store have x0 = 0, the admitted set is non-empty, and the program's only outcome has x0 = 5; so a verifier quantifying over admitted stores would establish the false postcondition x0 = 0.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Resolution.lean:88-93
-- lean/ToyProphecy/Resolution.lean
theorem premature_resolution_excludes_real_store :
    NoLentAccess writeOnce ∧ NoFrozenAccess writeOnce ∧ NoUseAfterEnd writeOnce ∧
    FreshBindings writeOnce ∧ AllEndedAtExit writeOnce ∧
    (∀ σ', ProphOutcomeWith (ResPolicy.resolveAfter 0 0) writeOnce zeroStore σ' → σ' 0 = 0) ∧
    (∃ σ', ProphOutcomeWith (ResPolicy.resolveAfter 0 0) writeOnce zeroStore σ') ∧
    (refSem writeOnce zeroStore).map (· 0) = some 5
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def zeroStore : Store := fun _ => 0
def idStore : Store := fun x => (x : Int)
def writeThenRead : Prog :=   -- r0 = &mut x0; *r0 = 5; end r0; x1 = x0
  [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0), op (assign 1 (var 0))]
def writeOnce : Prog := [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0)]
def deepCallee : Callee :=
  { body := [reborrow 1 0, write 1 (add (deref 1) (lit 2)), endBorrow 1,
             write 0 (add (deref 0) (lit 3)), reborrow 2 0, reborrow 3 2], ret := 3 }
def callDeep : Prog :=
  [op (borrow 0 0), call 1 deepCallee 0, op (write 1 (add (deref 1) (lit 10))),
   op (endBorrow 1), op (assign 1 (deref 0)), op (endBorrow 0)]
def ResPolicy.omitAtEnd (r : RefVar) : ResPolicy :=
  { ResPolicy.std with atEnd := fun r' => decide (r' ≠ r) }
def ResPolicy.omitAtCalleeExit : ResPolicy := { ResPolicy.std with atCalleeExit := false }
def ResPolicy.resolveAfter (i : Nat) (r : RefVar) : ResPolicy :=
  { atEnd := fun r' => decide (r' ≠ r), atCalleeExit := true,
    early := fun j => if j = i then [r] else [] }
```

**Tier.** T1 — The Creusot paper justifies resolution by the borrowed value no longer changing at that point; this is a mechanized instance of the failure when that justification is absent. The second positive control (resolving a reborrowed parent while its reborrow is live is exact) is, in our reading, a toy instance of what RustHornBelt's rule proph-resolve permits: resolving a prophecy to a value that depends on a still-unresolved prophecy.

**Hypothesis ledger.** None: a concrete statement about named programs.

**Depth.** shallow — Evaluation with a symbolic prophecy assignment.

**Non-vacuity.** The admitted set under premature resolution is non-empty (conjunct in the statement). (`Toy.Prophecy.premature_resolution_excludes_real_store`)

**Positive control.** Resolving r0 right after its last write (before its end) is exact on the same program; and in `r0 = &mut x0; r1 = &mut *r0; *r1 = 7; end r1; end r0`, resolving r0 right after the reborrow, while r1 is live and before r1's write, is also exact, because r0's current value is then r1's prophecy and r1 is resolved at its end. (`Toy.Prophecy.resolution_after_last_write_exact`, `Toy.Prophecy.parent_resolution_while_reborrow_live_exact`)

**Prior art.** [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878); [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205; [S7] Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, Derek Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022, pp. 841-856, doi:10.1145/3519939.3523704 (HAL hal-03777103); [S14] Xavier Denis. Vérification déductive de programmes Rust (English title: Deductive Verification of Rust Programs). PhD thesis, Université Paris-Saclay, 2023, HAL tel-04517581; and Xavier Denis, Jacques-Henri Jourdan, C. Marché. The CREUSOT Environment for the Deductive Verification of Rust Programs. Inria Research Report RR-9448, 2021, HAL hal-03526634. Extended descriptions of Creusot; only their bibliographic records were examined, so where they place resolutions is not summarized here. Full records and what each source says are under Evidence.

**Design question.** Where may a prophecy be resolved: what must hold at the resolution point for the encoding to stay sound?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the resolution policies model where a prophecy-based verifier inserts the equation `final = current` ([S5] Sec. 3.2, [S6] Sec. 3.2). The example shows what goes wrong in this toy model when that equation is omitted or moved; it is evidence about verifiers built that way only by analogy, not a statement about any implementation.

---

#### `callee-exit-resolution` — counterexample, T1, shallow

**Lean:** `Toy.Prophecy.omitting_callee_exit_resolution_admits_unproducible_store`

**Plain claim.** The program callDeep (a call to a callee that returns a reborrow two levels below its parameter, followed by a write through the result and a read of the argument) obeys all five parts of the discipline and from x |-> x produces x0 = x1 = 15, but without the resolutions emitted at callee exit the prophecy translation admits a final store with x0 = x1 = 7, which is not the program's outcome.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Resolution.lean:168-173
-- lean/ToyProphecy/Resolution.lean
theorem omitting_callee_exit_resolution_admits_unproducible_store :
    NoLentAccess callDeep ∧ NoFrozenAccess callDeep ∧ NoUseAfterEnd callDeep ∧
    FreshBindings callDeep ∧ AllEndedAtExit callDeep ∧
    (refSem callDeep idStore).map (fun σ => (σ 0, σ 1)) = some (15, 15) ∧
    ∃ σ', ProphOutcomeWith ResPolicy.omitAtCalleeExit callDeep idStore σ' ∧
      σ' 0 = 7 ∧ σ' 1 = 7 ∧ refSem callDeep idStore ≠ some σ'
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def zeroStore : Store := fun _ => 0
def idStore : Store := fun x => (x : Int)
def writeThenRead : Prog :=   -- r0 = &mut x0; *r0 = 5; end r0; x1 = x0
  [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0), op (assign 1 (var 0))]
def writeOnce : Prog := [op (borrow 0 0), op (write 0 (lit 5)), op (endBorrow 0)]
def deepCallee : Callee :=
  { body := [reborrow 1 0, write 1 (add (deref 1) (lit 2)), endBorrow 1,
             write 0 (add (deref 0) (lit 3)), reborrow 2 0, reborrow 3 2], ret := 3 }
def callDeep : Prog :=
  [op (borrow 0 0), call 1 deepCallee 0, op (write 1 (add (deref 1) (lit 10))),
   op (endBorrow 1), op (assign 1 (deref 0)), op (endBorrow 0)]
def ResPolicy.omitAtEnd (r : RefVar) : ResPolicy :=
  { ResPolicy.std with atEnd := fun r' => decide (r' ≠ r) }
def ResPolicy.omitAtCalleeExit : ResPolicy := { ResPolicy.std with atCalleeExit := false }
def ResPolicy.resolveAfter (i : Nat) (r : RefVar) : ResPolicy :=
  { atEnd := fun r' => decide (r' ≠ r), atCalleeExit := true,
    early := fun j => if j = i then [r] else [] }
```

**Tier.** T1 — Folklore made precise: in the cited encodings a callee's borrows are resolved when they go out of use; the parameter of a callee returning a reborrow is resolved while the reborrow lives on, which in our reading is again a resolution to a value depending on a still-unresolved prophecy (RustHornBelt, rule proph-resolve).

**Hypothesis ledger.** None: a concrete statement about named programs.

**Depth.** shallow — Evaluation under one prophecy assignment; the positive control evaluates under a symbolic one.

**Non-vacuity.** Concrete program and assignment. (`Toy.Prophecy.omitting_callee_exit_resolution_admits_unproducible_store`)

**Positive control.** Under the standard policy (callee-exit resolution included) the stores admitted for callDeep from x |-> x are exactly the program's outcome, so the spurious store with x0 = x1 = 7 is excluded. (`Toy.Prophecy.callDeep_prophOutcome_iff`)

**Prior art.** [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878); [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205; [S7] Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, Derek Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022, pp. 841-856, doi:10.1145/3519939.3523704 (HAL hal-03777103). Full records and what each source says are under Evidence.

**Design question.** For calls returning a borrow, which resolutions link the caller's argument to the returned borrow in a prophecy encoding?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the resolution policies model where a prophecy-based verifier inserts the equation `final = current` ([S5] Sec. 3.2, [S6] Sec. 3.2). The example shows what goes wrong in this toy model when that equation is omitted or moved; it is evidence about verifiers built that way only by analogy, not a statement about any implementation.

---

#### `callee-back-projection` — characterization, T0, shallow

**Lean:** `Toy.Prophecy.calleeBack_eq_final_of_calleeScoped_of_calleeFreshBindings`

**Plain claim.** Reference point: for every callee that is scoped (its body uses no reference variable that was never bound and no local, and its returned reference variable f.ret is the parameter or is bound by the body) and binds every borrow name at most once (including names of ended borrows), the backward function of its backward summary returns the final value of the returned borrow whatever the argument: calleeBack f a v = v.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Results.lean:121-123
-- lean/ToyProphecy/Results.lean
theorem calleeBack_eq_final_of_calleeScoped_of_calleeFreshBindings (f : Callee)
    (hS : CalleeScoped f) (hB : CalleeFreshBindings f) :
    ∀ a v, calleeBack f a v = v
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def CalleeAvoids (k : Violation) (f : Callee) : Prop := k ∉ calleeViolations f
def calleeViolations (f : Callee) : List Violation := (checkCallee f).viol
abbrev CalleeNoFrozenAccess (f : Callee) : Prop := CalleeAvoids .frozenAccess f
abbrev CalleeNoUseAfterEnd (f : Callee) : Prop := CalleeAvoids .useAfterEnd f
abbrev CalleeFreshBindings (f : Callee) : Prop := CalleeAvoids .rebind f
def CalleeScoped (f : Callee) : Prop := (checkCallee f).stuck = false
def calleeFwd (f : Callee) (a : Int) : Option Int :=
  (calleeRunB f a).bind fun s => (s.refs f.ret).map (·.cur)
def calleeBack? (f : Callee) (a v : Int) : Option Int := do
  let s ← calleeRunB f a
  let q ← s.refs f.ret
  unwindB { s with refs := fupd s.refs f.ret (some { q with cur := v }) } (f.body.length + 1) f.ret
def calleeBack (f : Callee) (a v : Int) : Int := (calleeBack? f a v).getD 0
def ProphContract (f : Callee) (a c pf rf : Int) : Prop :=
  ∃ φ : Nat → Int, ∃ s : PState,
    calleeRunP true φ f a pf 0 = some s ∧ Sat s.cs ∧
    ∃ q : PRef, s.refs f.ret = some q ∧ q.cur = c ∧ q.fin = rf
```

**Tier.** T0 — Reference point delimiting the model: for a function from one integer borrow to a borrow derived from it, the argument's final value is the returned borrow's final value; this is folklore, restated in this package's vocabulary.

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness |
| :--- | :--- | :--- |
| `hS : CalleeScoped f` | Scoping of the body and of the returned reference variable f.ret. A stuck callee has no summary; the total backward function then returns its default 0 (cxCalleeLocal, which uses a local; likewise the callee with empty body returning the never-bound name 1, emptyBody_unboundRet_not_scoped). | tight: counterexample `Toy.Prophecy.calleeBack_eq_final_tight_scoped` |
| `hB : CalleeFreshBindings f` | Each borrow name is bound at most once in the callee frame (syntactic single assignment; the parameter counts as bound), including names of ended borrows. Rebinding a live name can make the chain of parents a cycle that never reaches the parameter (cxCalleeRebind). Reusing an ended name cannot simply be allowed here: this statement does not assume the absence of frozen accesses, and in a callee with a frozen access reusing an ended name can close a cycle of parents (cxCalleeEndedRebind_cycle). | tight: counterexample `Toy.Prophecy.calleeBack_eq_final_tight_rebind` |

**Depth.** shallow — Induction along the chain of parents of the returned borrow, each step a reborrow whose backward function writes its argument into the parent.

**Non-vacuity.** deepCallee (returns a reborrow two levels below the parameter after an intermediate reborrow has ended): calleeBack deepCallee 4 20 = 20. (`Toy.Prophecy.deepCallee_nonvacuous`)

**Prior art.** [S1] Son Ho, Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), Article 116, pp. 711-741, 2022, doi:10.1145/3547647 (long version arXiv:2206.07185v2). Full records and what each source says are under Evidence.

**Design question.** Reference point: how much information does a backward function carry across a call that returns a reborrow, in the simplest setting?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the backward summary models a backward function of a callee returning a borrow ([S1]). In this single-borrow model the summary carries no information beyond the projection; nothing is claimed about callees with several borrows, compound values, or user-written specifications.

---

#### `callee-summary-agreement` — characterization, T1, substantive

**Lean:** `Toy.Prophecy.prophContract_iff_backwardSummary_of_calleeNoFrozenAccess_of_calleeNoUseAfterEnd_of_calleeFreshBindings`

**Plain claim.** For every callee with no frozen access, no use after end, and no rebinding (including reuse of the name of an ended borrow) in its body or at its return (as reported by the callee checker, which stops at the first scoping error), and all integers a, c, pf, rf: the callee's prophecy contract (argument current value a, argument prophecy pf, returned borrow (c, rf), for some satisfying assignment of the callee's internal prophecies including its callee-exit resolutions) holds exactly when c is the forward value of its backward summary at a and pf = calleeBack f a rf. In this single-borrow model calleeBack f a rf = rf for every scoped callee with fresh names (card callee-back-projection), so for such callees the contract says c = forward value and pf = rf. Scoping is not assumed.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Results.lean:133-137
-- lean/ToyProphecy/Results.lean
theorem prophContract_iff_backwardSummary_of_calleeNoFrozenAccess_of_calleeNoUseAfterEnd_of_calleeFreshBindings
    (f : Callee)
    (hF : CalleeNoFrozenAccess f) (hE : CalleeNoUseAfterEnd f)
    (hB : CalleeFreshBindings f) :
    ∀ a c pf rf, ProphContract f a c pf rf ↔ (calleeFwd f a = some c ∧ pf = calleeBack f a rf)
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def CalleeAvoids (k : Violation) (f : Callee) : Prop := k ∉ calleeViolations f
def calleeViolations (f : Callee) : List Violation := (checkCallee f).viol
abbrev CalleeNoFrozenAccess (f : Callee) : Prop := CalleeAvoids .frozenAccess f
abbrev CalleeNoUseAfterEnd (f : Callee) : Prop := CalleeAvoids .useAfterEnd f
abbrev CalleeFreshBindings (f : Callee) : Prop := CalleeAvoids .rebind f
def CalleeScoped (f : Callee) : Prop := (checkCallee f).stuck = false
def calleeFwd (f : Callee) (a : Int) : Option Int :=
  (calleeRunB f a).bind fun s => (s.refs f.ret).map (·.cur)
def calleeBack? (f : Callee) (a v : Int) : Option Int := do
  let s ← calleeRunB f a
  let q ← s.refs f.ret
  unwindB { s with refs := fupd s.refs f.ret (some { q with cur := v }) } (f.body.length + 1) f.ret
def calleeBack (f : Callee) (a v : Int) : Int := (calleeBack? f a v).getD 0
def ProphContract (f : Callee) (a c pf rf : Int) : Prop :=
  ∃ φ : Nat → Int, ∃ s : PState,
    calleeRunP true φ f a pf 0 = some s ∧ Sat s.cs ∧
    ∃ q : PRef, s.refs f.ret = some q ∧ q.cur = c ∧ q.fin = rf
```

**Tier.** T1 — Callee-level counterpart of agreement; folklore made precise.

**Hypothesis ledger.**

| hypothesis | why it is needed | tightness |
| :--- | :--- | :--- |
| `hF : CalleeNoFrozenAccess f` | Writing the parameter while it is reborrowed decouples the parameter's resolution from the returned borrow (cxCalleeFrozen). | tight: counterexample `Toy.Prophecy.prophContract_iff_tight_frozenAccess` |
| `hE : CalleeNoUseAfterEnd f` | Reborrowing an ended borrow leaves the returned borrow's prophecy unlinked to the parameter's (cxCalleeAfterEnd). | tight: counterexample `Toy.Prophecy.prophContract_iff_tight_useAfterEnd` |
| `hB : CalleeFreshBindings f` | Each borrow name is bound at most once in the callee frame (syntactic single assignment; the parameter counts as bound). This also rejects reusing the name of a borrow that has already ended, which on reuseEndedCallee is harmless (reuseEndedCallee_harmless). Rebinding a live name can cut the link and break the backward summary (cycle of parents, cxCalleeRebind). | tight: counterexample `Toy.Prophecy.prophContract_iff_tight_rebind` |

**Depth.** substantive — Needs an invariant over the callee body linking internal prophecies to the backward functions along the reborrow chain, plus the callee-exit resolutions.

**Non-vacuity.** deepCallee satisfies all three; ProphContract deepCallee 4 9 20 20 holds, calleeFwd deepCallee 4 = some 9 and calleeBack deepCallee 4 20 = 20. (`Toy.Prophecy.deepCallee_nonvacuous`)

**Prior art.** [S1] Son Ho, Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), Article 116, pp. 711-741, 2022, doi:10.1145/3547647 (long version arXiv:2206.07185v2); [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205; [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878); [S7] Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, Derek Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022, pp. 841-856, doi:10.1145/3519939.3523704 (HAL hal-03777103). Full records and what each source says are under Evidence.

**Design question.** For calls returning a borrow, does the callee's backward summary relate the same values as the callee's prophecy contract?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the backward summary models a backward function of a callee returning a borrow ([S1]); the prophecy contract models a callee specification over the argument's prophecy and the returned borrow's prophecy ([S5], [S6]). In this single-borrow model the summary carries no information beyond the projection; nothing is claimed about callees with several borrows, compound values, or user-written specifications.

---

#### `selection-correct` — theorem, T0, shallow

**Lean:** `Toy.Prophecy.selIncr_both_translations_correct`

**Plain claim.** Reference check: for every initial store, on the example `r0 = if x2 != 0 { &mut x0 } else { &mut x1 }; *r0 = *r0 + 1; end r0` the backward-function translation computes the reference semantics' outcome and the prophecy translation admits exactly that outcome.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Selection.lean:55-57
-- lean/ToyProphecy/Selection.lean
theorem selIncr_both_translations_correct (σ : Store) :
    backSem selIncr σ = refSem selIncr σ ∧
    ∀ σ', ProphOutcome selIncr σ σ' ↔ refSem selIncr σ = some σ'
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def selIncr : Prog :=   -- r0 = if x2 != 0 { &mut x0 } else { &mut x1 }; *r0 = *r0 + 1; end r0
  [op (borrowSel 0 (var 2) 0 1), op (write 0 (add (deref 0) (lit 1))), op (endBorrow 0)]
def selLenders (b : Bool) (x0 y0 : Int) (v : Int) : Int × Int := if b then (v, y0) else (x0, v)
def SelBackSpec (b : Bool) (x0 y0 cur : Int) (back : Int → Int × Int) : Prop :=
  cur = (if b then x0 else y0) ∧ ∀ v, back v = selLenders b x0 y0 v
def SelProphSpec (b : Bool) (x0 y0 cur fin x' y' : Int) : Prop :=
  cur = (if b then x0 else y0) ∧ (x', y') = selLenders b x0 y0 fin
```

**Tier.** T0 — Reference check: both encodings handle run-time selected borrows in the cited papers (RustHorn take_max, Creusot pick, Aeneas choose); this is a mechanized evaluation on one toy example, an instance of back-sound and proph-sound proved directly.

**Hypothesis ledger.** None: a concrete statement about named programs.

**Depth.** shallow — Case split on the condition and evaluation.

**Non-vacuity.** No hypotheses; the statement holds for every initial store, in particular for both branches (x2 = 0 and x2 != 0). (`Toy.Prophecy.selIncr_both_translations_correct`)

**Prior art.** [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205; [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878); [S1] Son Ho, Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), Article 116, pp. 711-741, 2022, doi:10.1145/3547647 (long version arXiv:2206.07185v2). Full records and what each source says are under Evidence.

**Design question.** Reference check: do both encodings handle a borrow chosen at run time between two locals on the simplest example?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the example is the toy analogue of the run-time selection examples choose/take_max/pick in [S1], [S5] and [S6]; it informs how specifications of such functions are shaped in the two styles, not how any tool generates them.

---

#### `selection-shapes` — characterization, T0, definitional

**Lean:** `Toy.Prophecy.selIncr_backward_shape`, `Toy.Prophecy.selIncr_prophecy_shape`, `Toy.Prophecy.selLenders_depends_on_condition`

**Plain claim.** On the selection example selIncr, both translations contain the same condition-dependent map selLenders b x0 y0 (the chosen lender gets the value, the other keeps its own), which no condition-independent map can replace. The backward-function translation stores it as the borrow's backward function, specified by an equation quantified over all final values (SelBackSpec), whose lender assignments succeed on every state and set the lenders to exactly selLenders b x0 y0 v, and applies it at the end to the final value (chosen lender's value) + 1. The prophecy translation applies it at creation to the single fresh prophecy φ 0, specified by a quantifier-free equation in that prophecy (SelProphSpec); after the whole program exactly one prophecy has been drawn and the only constraint is the resolution emitted at `end r0`, whose syntactic form (current value, φ 0) is the same in both branches and whose left side evaluates to (if x2 != 0 then x0 else x1) + 1.

**Lean statement** (proof omitted):

```lean
-- lean/ToyProphecy/Selection.lean:102-112
-- lean/ToyProphecy/Selection.lean
theorem selIncr_backward_shape (σ : Store) :
    (∃ s q, runB (BState.init σ) [op (borrowSel 0 (var 2) 0 1)] = some s ∧
      s.refs 0 = some q ∧ s.store = σ ∧
      SelBackSpec (decide (σ 2 ≠ 0)) (σ 0) (σ 1) q.cur (backLenders01 σ q) ∧
      ∀ (τ : Store) (refs : RefVar → Option BRef) (v : Int),
        (applyBack { store := τ, refs := refs } (q.back v)).map
            (fun s' => (s'.store 0, s'.store 1)) =
          some (selLenders (decide (σ 2 ≠ 0)) (σ 0) (σ 1) v)) ∧
    (∃ s, runB (BState.init σ) selIncr = some s ∧
      (s.store 0, s.store 1) =
        selLenders (decide (σ 2 ≠ 0)) (σ 0) (σ 1) ((if σ 2 ≠ 0 then σ 0 else σ 1) + 1))
-- lean/ToyProphecy/Selection.lean:124-129
-- lean/ToyProphecy/Selection.lean
theorem selIncr_prophecy_shape (σ : Store) (φ : Nat → Int) :
    (∃ s q, runP ResPolicy.std φ 0 (PState.init σ) [op (borrowSel 0 (var 2) 0 1)] = some s ∧
      s.next = 1 ∧ s.cs = [] ∧ s.refs 0 = some q ∧ q.fin = φ 0 ∧
      SelProphSpec (decide (σ 2 ≠ 0)) (σ 0) (σ 1) q.cur q.fin (s.store 0) (s.store 1)) ∧
    (∃ s, runP ResPolicy.std φ 0 (PState.init σ) selIncr = some s ∧ s.next = 1 ∧
      s.cs = [((if σ 2 ≠ 0 then σ 0 else σ 1) + 1, φ 0)])
-- lean/ToyProphecy/Selection.lean:140-141
-- lean/ToyProphecy/Selection.lean
theorem selLenders_depends_on_condition (x0 y0 : Int) :
    ¬ ∃ g : Int → Int × Int, ∀ b v, g v = selLenders b x0 y0 v
```

Key definitions it unfolds to (quoted from the sources; see Definitions for the semantics):

```lean
def selIncr : Prog :=   -- r0 = if x2 != 0 { &mut x0 } else { &mut x1 }; *r0 = *r0 + 1; end r0
  [op (borrowSel 0 (var 2) 0 1), op (write 0 (add (deref 0) (lit 1))), op (endBorrow 0)]
def selLenders (b : Bool) (x0 y0 : Int) (v : Int) : Int × Int := if b then (v, y0) else (x0, v)
def SelBackSpec (b : Bool) (x0 y0 cur : Int) (back : Int → Int × Int) : Prop :=
  cur = (if b then x0 else y0) ∧ ∀ v, back v = selLenders b x0 y0 v
def SelProphSpec (b : Bool) (x0 y0 cur fin x' y' : Int) : Prop :=
  cur = (if b then x0 else y0) ∧ (x', y') = selLenders b x0 y0 fin
```

**Tier.** T0 — Re-derivation: the case-split specifications appear in the cited papers (Aeneas choose_back; Creusot pick; RustHorn take_max clauses); this restates their exact shapes on one toy example in this package's vocabulary.

**Hypothesis ledger.** None: a concrete statement about named programs.

**Depth.** definitional — Evaluation of the example in each translation and a two-point argument for the condition dependence.

**Non-vacuity.** No hypotheses; the three statements hold for every initial store and every prophecy assignment. (`Toy.Prophecy.selIncr_backward_shape`, `Toy.Prophecy.selIncr_prophecy_shape`, `Toy.Prophecy.selLenders_depends_on_condition`)

**Prior art.** [S1] Son Ho, Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), Article 116, pp. 711-741, 2022, doi:10.1145/3547647 (long version arXiv:2206.07185v2); [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878); [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205; [S4] Sebastian Ullrich. Simple Verification of Rust Programs via Functional Purification. Master's thesis, Karlsruhe Institute of Technology (KIT), 2016; [S8] Vytautas Astrauskas, Peter Müller, Federico Poli, Alexander J. Summers. Leveraging Rust Types for Modular Specification and Verification. Proc. ACM Program. Lang. 3(OOPSLA), Article 147, 2019, doi:10.1145/3360573. Full records and what each source says are under Evidence.

**Design question.** Where do the specification shapes of the two encodings differ for borrows selected at run time?

Basis: execution (Lean kernel check) — the Lean statement above is proved; axioms and statement hashes are recorded under Evidence.

Basis: derived (modeling bridge) — the example is the toy analogue of the run-time selection examples choose/take_max/pick in [S1], [S5] and [S6]; it informs how specifications of such functions are shaped in the two styles, not how any tool generates them.

## Boundaries

### Non-claims

Non-claims come first. They are taken from the cards; a non-claim shared by
several results is listed once with the results it applies to.

#### Non-claims shared by several results

- (`back-sound`, `agreement`, `proph-sound`, `proph-inclusion`, `omission-monotone`, `omission-keeps-real`, `resolution-necessary`, `premature-resolution`, `callee-exit-resolution`, `callee-back-projection`, `callee-summary-agreement`, `selection-correct`, `selection-shapes`) Toy model: straight-line code over unbounded integer locals; mutable borrows of whole integer locals only (no pair components, no compound values, no shared borrows, no two-phase borrows); explicit `endBorrow` instead of inferred (non-lexical) lifetimes; callees take exactly one borrow, have no locals, make no calls, and return a borrow derived from their parameter; no branches other than run-time selection of a borrow, no loops, no panics, divergence or early exits, no intermediate assertions, no unsafe code, no interior mutability, no concurrency. These are statements about this toy model; they neither establish nor refute the corresponding claims about Rust's borrow checker or about Aeneas, RustHorn and Creusot.
- (`back-sound`, `agreement`, `proph-sound`, `proph-inclusion`, `omission-keeps-real`, `resolution-necessary`, `premature-resolution`, `callee-exit-resolution`, `callee-summary-agreement`, `selection-correct`, `selection-shapes`) Nothing is proved about Aeneas, RustHorn, Creusot or any other implementation; the two translations are toy models in the style their papers describe. Any connection to a real tool is a modeling bridge stated in prose, not a kernel-checked fact.
- (`back-sound`, `agreement`, `proph-sound`, `proph-inclusion`, `omission-keeps-real`) The discipline (`violations`) is a static, explicit-end checker chosen for this package, not Rust's borrow checker; in particular it lends both candidates of a run-time selected borrow until the borrow ends, and it does not model non-lexical lifetimes or two-phase borrows. It keeps statuses per borrow name; rebinding a name leaks the borrow previously held under it (reported only as `rebind`). It stops at the first scoping error (a reference variable that was never bound, a local operation in a callee, a callee returning a name that was never bound): once stuck it records no further violation (`checkStmts_of_stuck`), and `unendedAtExit` is not reported for a stuck program. So a program with a scoping error satisfies each discipline property as soon as no violation of that kind is recorded before the checker gets stuck, whatever follows (`stuckProg_satisfies_all_avoids`: a program with a lent access, frozen accesses, a use after end, a rebinding and live borrows after its scoping error satisfies all five).
- (`back-sound`, `agreement`, `proph-sound`, `proph-inclusion`, `omission-keeps-real`) `FreshBindings` and `AllEndedAtExit` are artifacts of explicit `endBorrow` without inferred (non-lexical) lifetimes: in Rust the borrow checker infers where a borrow ends, so reassigning a reference variable or leaving its scope needs no explicit end. `FreshBindings` also rejects reusing the name of a borrow that has already ended; on the example `rebindEnded` that reuse is harmless for both translations (`rebindEnded_harmless`), and no general statement about it is made. Tightness of `FreshBindings` and `AllEndedAtExit` here does not mean that a verifier for Rust must forbid reassigning reference variables or require explicit ends.
- (`back-sound`, `agreement`) `backSem` is a small-step interpreter over a mutable environment of borrow slots (`RefVar → Option BRef`) in which a reborrow's backward function writes the parent borrow's slot (`Target.ref q`) at an explicit `endBorrow`; it is not a syntactic translation into pure functions without slot state, and it does not model the lazy, on-demand ending of borrows described for Aeneas.
- (`agreement`, `proph-sound`, `proph-inclusion`, `omission-monotone`, `omission-keeps-real`, `resolution-necessary`, `premature-resolution`) Admitted stores are filtered by the constraints accumulated over the whole run, and only completed runs are considered; there are no intermediate assertions and no panics, divergence or early exits. A verifier that assumed every resolution constraint of a run while checking an earlier assertion would accept any such assertion on a run whose later constraints are unsatisfiable (as for `cxAfterEndUnsat`); a forward verifier that checks an assertion before a borrow is resolved sees that borrow's prophecy unconstrained. Neither placement of assertions is modeled.
- (`agreement`, `premature-resolution`) Ending a borrow while it is reborrowed is a frozen access, so the general statements say nothing about it. On the example `endParentFirst` (`r0 = &mut x0; r1 = &mut *r0; *r1 = 7; end r0; end r1`), the prophecy translation is exact while the backward-function translation loses the write through `r1` (`endParentFirst_prophecy_exact_backward_lossy`); the prophecy side is exact there only because `r1` is resolved later (`endParentFirstChildUnended_imprecise`). These are examples, not a general asymmetry theorem.
- (`proph-sound`, `proph-inclusion`, `omission-monotone`, `omission-keeps-real`, `resolution-necessary`) Reading for verification: a postcondition Q is established by the prophecy translation when Q holds of every admitted store. Inclusion (the real store is admitted) is what makes this sound; precision (nothing else is admitted) is what makes it complete. This reading uses the admitted set as an over-approximation. Uses in the other direction (concluding that a behaviour is possible because some admitted store exhibits it, or using a prophecy-derived fact where an under-approximation is required) are not covered; for those, extra admitted stores, for example from an omitted resolution, are unsound rather than merely incomplete.
- (`proph-sound`, `omission-keeps-real`, `resolution-necessary`, `callee-exit-resolution`) `endBorrow` marks the end of a borrow's lifetime in this toy; it is not the execution of a destructor (`Drop::drop`), and nothing here relates resolution to destructors. Where the prior-art summaries below say that a borrow is dropped, they use the cited paper's own terminology.
- (`proph-inclusion`, `omission-keeps-real`) Says nothing when the reference semantics is stuck (`refSem P σ = none`); the premise then fails.
- (`callee-back-projection`, `callee-summary-agreement`) The callee checker also stops at the first scoping error (`checkOps_of_stuck`): a callee with a scoping error satisfies each callee discipline property as soon as no violation of that kind is recorded before the checker gets stuck, whatever follows (`stuckCallee_satisfies_all_avoids`: a frozen access, a use after end and a rebinding after a local operation are not reported).

#### Non-claims of individual results

`back-sound`:

- Programs on which the reference semantics is stuck (`refSem P σ = none`, e.g. on a scoping error) are covered only in that the statement then says `backSem P σ = none` as well, and conversely. Because the checker stops at the first scoping error, such programs may contain arbitrary violations after the error and still satisfy all five hypotheses (`stuckProg_satisfies_all_avoids`); nothing else is said about them.
- Soundness here is equality of final stores of deterministic semantics; it is not a statement about refinement of nondeterministic or effectful programs.
- The callee summary used at call sites is computed from the callee body; nothing is claimed about summaries supplied by a user or an external specification.

`agreement`:

- When the backward-function translation is stuck (`backSem P σ = none`, e.g. on a scoping error), the statement says only that no store is admitted (`∀ σ', ¬ ProphOutcome P σ σ'`). That conclusion does not distinguish a prophecy run that is itself stuck (`runP … = none`) from a completed run whose resolution constraints are unsatisfiable (`¬ Sat s.cs`, as for `cxAfterEndUnsat`, which violates the discipline). Because the checker stops at the first scoping error, such programs may contain arbitrary violations after the error and still satisfy all five hypotheses (`stuckProg_satisfies_all_avoids`, on which the prophecy run itself is stuck).
- The statement does not expose or characterize the satisfying prophecy assignment; it only says which final stores are admitted.
- Agreement is stated for the standard policy (resolve each borrow when it ends, resolve callee borrows at callee exit); other policies are treated only by the resolution cards.

`proph-sound`:

- When the reference semantics is stuck (`refSem P σ = none`, e.g. on a scoping error), the statement says only that no store is admitted (`∀ σ', ¬ ProphOutcome P σ σ'`). That conclusion does not distinguish a prophecy run that is itself stuck (`runP … = none`) from a completed run whose resolution constraints are unsatisfiable (`¬ Sat s.cs`, as for `cxAfterEndUnsat`, which violates the discipline). Because the checker stops at the first scoping error, such programs may contain arbitrary violations after the error and still satisfy all five hypotheses (`stuckProg_satisfies_all_avoids`, on which the prophecy run itself is stuck).
- Of the five hypotheses, AllEndedAtExit is not needed for inclusion of the real outcome (card proph-inclusion, which still assumes the other four). Whether FreshBindings is needed for inclusion is open: its tightness there is unknown.

`proph-inclusion`:

- Inclusion only: other stores may also be admitted (they are, for cxUnended). It gives no completeness.
- Whether inclusion holds without FreshBindings is open (tightness unknown). A randomized search over generated programs whose only violations are rebinding or unended borrows found no failure; that is weak evidence: with a checker that keeps lender links across a rebinding, the same generator also reports no failure, although rebindThenFrozenRead is a counterexample for such a checker.

`omission-monotone`:

- The policy is keyed by the name r: without FreshBindings and NoUseAfterEnd the name may be bound and ended several times, and every one of those ends is unresolved. Callee bodies and callee-exit resolutions are unaffected, even when r is also the name of a callee's parameter (`callDeep_omitAtEnd0_callee_still_resolved`).
- Omission is only of resolutions at the end of main-program borrows (`omitAtEnd`); omitting callee-exit resolutions or moving resolutions earlier is a different policy, not covered.
- The converse is false: omission can admit stores the standard policy does not (card resolution-necessary).

`omission-keeps-real`:

- `ResPolicy.omitAtEnd r` is keyed by the name r: every `endBorrow r` statement of the main program emits no resolution constraint. Callee bodies and callee-exit resolutions are unaffected, even when r is also the name of a callee's parameter: under `ResPolicy.omitAtEnd 0`, the callee of `callDeep` (whose parameter is also named 0) still emits its callee-exit resolutions, and every admitted store still has x1 = 15 (`callDeep_omitAtEnd0_callee_still_resolved`). Omitting callee-exit resolutions (card callee-exit-resolution) or moving resolutions earlier (card premature-resolution) is a different policy, not covered.
- The tightness counterexamples omit the resolution of the borrow the program actually uses (r = 0); they show that each hypothesis is needed for the conclusion, but in all three the real outcome is excluded already under the standard policy (card proph-inclusion), so they show nothing specific to omission.
- Omission can still make a verifier incomplete (card resolution-necessary).
- Whether the conclusion holds without FreshBindings is open.

`resolution-necessary`:

- Omitting a resolution causes imprecision (spurious admitted stores), not exclusion of the real store: for programs with no lent access, no frozen access, no use after end and fresh borrow names, the real outcome stays admitted (card omission-keeps-real). In the reading where a postcondition is established when it holds of every admitted store, omission makes the encoding incomplete, not unsound.
- The spurious value appears in the lender x0 of the final store and in x1, which reads the lender after the end. Which observations reveal an omitted resolution in general (e.g. when the lender is never observed again) is not characterized.
- What makes a prophecy encoding unsound in this toy is resolving before the last mutation (card premature-resolution) or violating the discipline (e.g. cxAfterEndUnsat, whose constraints are unsatisfiable).

`premature-resolution`:

- Shown on one program; no general characterization of safe resolution points is proved. The natural general condition (resolve only after the borrow's current value can no longer change: no later write through it, reborrow of it, or call with it) is stated in prose only.
- The positive controls show two specific early points are harmless; they do not show that resolving at the last use is always sound. The second one relies on the reborrow r1 being resolved later.

`callee-exit-resolution`:

- Only imprecision is shown. On this program the real store is still admitted without callee-exit resolution (callDeep_omitAtCalleeExit_admits_real); no general statement about omitting callee-exit resolution is made.
- The callee-exit resolutions equate the parameter's prophecy with the returned borrow's prophecy through the chain of reborrows; nothing is claimed about callees whose returned borrow is not derived from the parameter.

`callee-back-projection`:

- Because callees in this model take one integer borrow, allocate no locals, and return a borrow derived from that parameter, every scoped callee with fresh names has the identity backward function `calleeBack f a rf = rf` (this card), and for a stuck callee `calleeFwd f a = none` (e.g. `calleeFwd_neg`). Multi-borrow backward functions (such as Aeneas's `choose`) and projections into compound values (a borrow of one field of a pair) are not exercised.
- `calleeBack` is the total version of the partial `calleeBack?`, with default 0 where `calleeBack?` is undefined (stuck callee, f.ret never bound, or a chain of parents that does not reach the parameter). At v = 0 the conclusion cannot distinguish an undefined `calleeBack?` from the value 0 (`calleeBack_masks_none_at_zero`: `calleeBack? cxCalleeRebind 0 0 = none` while `calleeBack cxCalleeRebind 0 0 = 0`); for v ≠ 0, `calleeBack f a v = v` does imply `calleeBack? f a v = some v` (`calleeBackOpt_eq_some_of_calleeBack_eq_of_ne_zero`). No statement about `calleeBack?` at v = 0 is made.
- This is an artifact of integer-valued borrows returned by single-borrow callees: in the cited Aeneas paper, backward functions of functions taking several borrows (choose) or returning a borrow into part of a compound value are not projections. Those cases are not examined.
- Frozen access and use after end are not hypotheses here: the backward function is a projection even for callees violating them (the summary agreement card needs them).

`callee-summary-agreement`:

- Because callees in this model take one integer borrow, allocate no locals, and return a borrow derived from that parameter, every scoped callee with fresh names has the identity backward function `calleeBack f a rf = rf` (card callee-back-projection), and for a stuck callee `calleeFwd f a = none` (e.g. `calleeFwd_neg`). Multi-borrow backward functions (such as Aeneas's `choose`) and projections into compound values (a borrow of one field of a pair) are not exercised.
- The statement is about one callee in isolation; it does not mention call sites. Caller-level agreement for programs containing calls is part of the agreement card, not of this one.
- Scoping is not a hypothesis. A callee with a scoping error satisfies all three hypotheses whenever no such violation is recorded before its error, whatever follows (`stuckCallee_satisfies_all_avoids`); the statement still asserts the equivalence for it, which, when the forward value is undefined, says that the contract never holds (on `cxCalleeLocal`, a callee stuck on a local operation, both sides are false for all arguments: `cxCalleeLocal_avoids_all_no_contract`).
- `CalleeFreshBindings` (`CalleeAvoids .rebind`) is syntactic single assignment of borrow names in the callee frame: it also rejects reusing the name of a borrow that has already ended. On `reuseEndedCallee` that reuse is harmless: the callee violates only `CalleeFreshBindings`, and both the projection and this agreement hold for it (`reuseEndedCallee_harmless`). Whether the statement holds with a weaker hypothesis that forbids only rebinding a live name is not claimed. The checker does not allow reuse of ended names in general because, in a callee with a frozen access, reusing an ended name can close a cycle of parents, so that the backward summary is undefined (`cxCalleeEndedRebind_cycle`).
- In a callee only frozen access, use after end and rebinding can be reported (`calleeAvoids_lentAccess_unendedAtExit`), which is why only those three appear.

`selection-correct`:

- One example only; general programs with selection are covered by the general cards (back-sound, agreement, proph-sound). This card is proved directly and does not depend on them.
- The example's discipline lends both candidates for the borrow's whole life; programs that touch the unchosen local while the borrow is live are rejected by the checker (borrowSel_lends_both) even when that would be harmless at run time.

`selection-shapes`:

- It is not true in this toy that the prophecy side avoids a case split: the case split moves from the end of the borrow (backward) to its creation (prophecy), and the resolution's left side still depends on the condition. Claims of the form 'prophecies need no case split' are not supported.
- One example only; nothing is claimed about specification size or prover effort in real tools.
- SelBackSpec and SelProphSpec describe the shapes for this example; they are not general specification languages.

### Escape hatches

- `back-sound`, `agreement`, `proph-sound`: each of the five discipline
  properties is tight; dropping any one defeats the conclusion, witnessed by a
  proved counterexample program that violates only that property (cards and
  Evidence list the theorem names; programs `cxLent`, `cxFrozen`, `cxAfterEnd`,
  `cxAfterEndUnsat`, `cxRebind`, `cxUnended`).
- `proph-inclusion`, `omission-keeps-real`: `NoLentAccess`, `NoFrozenAccess`
  and `NoUseAfterEnd` are tight; `AllEndedAtExit` is not needed
  (`inclusion_nonvacuous` uses `cxUnended`).
- `callee-back-projection`: `CalleeScoped` and `CalleeFreshBindings` are tight
  (`cxCalleeLocal`, `cxCalleeRebind`); frozen accesses and uses after end in the
  callee do not affect it.
- `callee-summary-agreement`: `CalleeNoFrozenAccess`, `CalleeNoUseAfterEnd`
  and `CalleeFreshBindings` are tight (`cxCalleeFrozen`, `cxCalleeAfterEnd`,
  `cxCalleeRebind`); scoping is not assumed (for an unscoped callee both sides
  are false).
- `resolution-necessary`, `premature-resolution`, `callee-exit-resolution`
  (concrete counterexamples): the failure disappears under the standard policy
  (`prophOutcome_writeThenRead_iff`, `callDeep_prophOutcome_iff`) or when the
  borrow is resolved after its last write, including while a reborrow of it is
  live (`resolution_after_last_write_exact`,
  `parent_resolution_while_reborrow_live_exact`).

### Hypotheses whose tightness is unknown

- `FreshBindings` in `proph-inclusion` and `omission-keeps-real`: **unknown**.
  No counterexample is known for this checker. Informal argument for the
  stronger statement without it: a leaked borrow's prophecy appears only in its
  lender, which stays lent (a local) or frozen (a parent) for the rest of the
  frame, so it is unobservable and can be chosen to be the real value; callee
  frames add callee-exit resolutions, which only identify such free values with
  each other. This argument is not mechanized. A checker that, unlike this one,
  keeps lender links by name across a rebinding would let the program
  `rebindThenFrozenRead` pass the other properties; its real outcome is excluded
  by the prophecy translation (`rebindThenFrozenRead_real_excluded`), and this
  checker rejects it for a frozen access (`rebindThenFrozenRead_violations`).
  A randomized search over small generated programs whose only violations were
  rebinding or unended borrows found no inclusion failure; that search is not
  part of this package's evidence and is weak (it also missed that program).

### Disproved or dropped statements

None. All thirteen results are proved as stated; no statement was found false,
weakened or dropped while proving.

### Not examined

Loops and general branching, shared borrows, two-phase borrows, borrows of
compound values or their components, callees with several borrow parameters,
locals or nested calls, programs with intermediate assertions or panics, and
any real verification tool or real Rust program.
## Evidence

**Toolchain.** Lean `leanprover/lean4:v4.34.1` (tag commit
`5045d0056413266e57c625dcd7c365b10e377c52`, as reported by the GitHub API for
`refs/tags/v4.34.1` and by `lean --version`), no Mathlib, no Lake dependencies.

**Kernel check.** `lake build` of `lean/` succeeds with no `sorry`, `admit`,
`native_decide`, `axiom` or `opaque` in the sources. Lean's `collectAxioms` over
all 1193 declarations of the library reports only: Classical.choice, Quot.sound, propext. Per-declaration
axioms are recorded in `audit/axioms.json`; statement and definition-closure
hashes in `audit/statements.json` (what is hashed is described under
Revalidation). Observed 2026-11-20.

Basis: execution (Lean kernel check).

| | |
| :--- | :--- |
| Main results | `lean/ToyProphecy/Results.lean`, `Resolution.lean`, `Selection.lean` |
| Proofs of the general results | `lean/ToyProphecy/Sim/*.lean` |
| Counterexamples | `lean/ToyProphecy/Counterexamples.lean`, `Calls.lean` |
| Non-vacuity witnesses | `lean/ToyProphecy/NonVacuity.lean`, `Calls.lean`, `Examples.lean`, `Resolution.lean` |
| Definition examples and boundary facts | `lean/ToyProphecy/Examples.lean`, `Boundaries.lean` |

| result | theorem | axioms | statement sha256 | closure sha256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `back-sound` | `Toy.Prophecy.backSem_eq_refSem_of_discipline` | Classical.choice, Quot.sound, propext | `fb6fb97421122208bb78f484e03b4f11f5fe64e7d7d8b59b7336d61a172bf2e1` | `2df85e7cce42adc1e554fbeac62a13f2d54acda3f17729ebc7c09a8b24c28eff` (178) |
| `agreement` | `Toy.Prophecy.prophOutcome_iff_backSem_of_discipline` | Classical.choice, Quot.sound, propext | `b6ea12953dde0171a38adb29442ffb11acdd2872a58567dcdda5595c3767445e` | `34f1136e6466c6ff85e24c839a2bdf3006e4513dacf03cff5b36bd74bfd3ad1a` (202) |
| `proph-sound` | `Toy.Prophecy.prophOutcome_iff_refSem_of_discipline` | Classical.choice, Quot.sound, propext | `9d86ba81f020909ddea59fd2964baf52db346f5da15688ff4adfb15e25a66414` | `29bfcaa56daf48cd91b8afd205bb25eaf7045fa9b27967c528374120c4d639b2` (177) |
| `proph-inclusion` | `Toy.Prophecy.prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings` | Classical.choice, Quot.sound, propext | `e222a8da7b08473deece4cc1c97699fa16c856016ea147134fd2110d6165ba4b` | `371f93b76afca305f1ae82c9f660a0ce0340830a9f7b52ed8f850c41fd872148` (176) |
| `omission-monotone` | `Toy.Prophecy.prophOutcomeWith_omitAtEnd_of_prophOutcome` | Quot.sound, propext | `f1a4510e8bbbb3455a9e66771175ae3c26d7b07f04067889a8cd4a9cb3736a0a` | `96c846c9adec26b55814dabcfc11a3cb49a3fe2e8bc2bb2d12385ba02bfa2c6c` (80) |
| `omission-keeps-real` | `Toy.Prophecy.prophOutcomeWith_omitAtEnd_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings` | Classical.choice, Quot.sound, propext | `7e65f42e35d71ef42e2c686831efc20a1a0c584fb1afca96fcad3312f568c0ae` | `7d2e92e55c13662ac079023eab84ca71bd585347fa1e2772f43a2dc950982254` (176) |
| `resolution-necessary` | `Toy.Prophecy.omitting_resolution_admits_unproducible_store` | propext | `90d29ce80c3765b879ea35a96dec8830ca8990684701c67236b05c9145e5c3ae` | `d64e26590636a85b49c9fcaaa88ec14cfa43d3b9b0a9d71bc6e6732b7b255865` (179) |
| `premature-resolution` | `Toy.Prophecy.premature_resolution_excludes_real_store` | Quot.sound, propext | `36a0ce9816b2b7643d2a08cccd0a020920aefde570d077189490d0b979f49ab4` | `8a94692f525197f6e13d21d86654bc7c235d221627e8473da0798766c0812d08` (178) |
| `callee-exit-resolution` | `Toy.Prophecy.omitting_callee_exit_resolution_admits_unproducible_store` | propext | `03db2199eae442105c511924e4f1cb979746f481afb465d35333bc6632dae37a` | `ff3c7da5bd25bd6fb61e3799c0e95c7dc93d2f16c7a91cb5c8cbaec18ab9629c` (180) |
| `callee-back-projection` | `Toy.Prophecy.calleeBack_eq_final_of_calleeScoped_of_calleeFreshBindings` | Classical.choice, Quot.sound, propext | `8c294aac71037934d10f14a4e3fd2467618fd9d94591c8021174e59df2ddc83d` | `9a8e27ca08a4e5ee794209b073ad97ebf8121becf9f4f45cb11bb5202a51cb9c` (135) |
| `callee-summary-agreement` | `Toy.Prophecy.prophContract_iff_backwardSummary_of_calleeNoFrozenAccess_of_calleeNoUseAfterEnd_of_calleeFreshBindings` | Classical.choice, Quot.sound, propext | `33f2c65c49cfb9c4db637646be8803a5b71f1af5f6b868ea93bacc5d1cf010f5` | `79d4d6e6820add82f9a5c2c369f7415fc0ff3a3d93eb73727b592abb1fdaa4f8` (167) |
| `selection-correct` | `Toy.Prophecy.selIncr_both_translations_correct` | Quot.sound, propext | `57ec429a8804c1c44969c8c9d408bd60327a719f342bd85d6709f075d1fa9bf5` | `04b744fb380cfbcd4f6a5cb5ba61252abbda0c81a537e964d277e89bfe1eed12` (145) |
| `selection-shapes` | `Toy.Prophecy.selIncr_backward_shape` | Quot.sound, propext | `0a1daca8a404c3bad3fd395e5bc1ac33fe985090114a5ef3140b4fe7686b02e5` | `0e25261a0161eca4d878f74cccaafdbe1dd93dc5f669cec52cdad6dcf54ce50c` (83) |
| `selection-shapes` | `Toy.Prophecy.selIncr_prophecy_shape` | Quot.sound, propext | `10144b0c0c389561897bc85bcbcf0bb609d20c0164f973dc242a607241e7bc21` | `a945f823bb2d813bb9edaa2155da9c65f72fbd639e5148b72cc07a9c21ba9874` (79) |
| `selection-shapes` | `Toy.Prophecy.selLenders_depends_on_condition` | Quot.sound, propext | `bae9022102a02a9e6fbd48e7ca9f5e25c7572f4f91b79840e46226d51062d9e2` | `0b8f6048dfe0e8302e11a317115f18afcda1040f135b09287f9733a32258fe8a` (1) |

Counterexamples, non-vacuity witnesses and positive controls referenced by the cards:

| theorem | role | axioms | statement sha256 | closure sha256 (size) |
| :--- | :--- | :--- | :--- | :--- |
| `Toy.Prophecy.backSem_eq_refSem_tight_allEndedAtExit` | counterexample (back-sound, hX) | propext | `844dad1f5fe08a2ba4e560ab562f80ddc89d0dafbf4148db9461e8ec30b259cb` | `22259e123c070273b0d5718420a984de45fab9b18179cb8c9a03ed29881da74b` (180) |
| `Toy.Prophecy.backSem_eq_refSem_tight_freshBindings` | counterexample (back-sound, hB) | propext | `e4af4ededaaeae7616d335703534b9779860f44602fee4946f68ba8429b5ac60` | `e58c0e92d56662589f789ba05b8bcbb86ede9c3966394ce215c03da729de94b1` (180) |
| `Toy.Prophecy.backSem_eq_refSem_tight_noFrozenAccess` | counterexample (back-sound, hF) | propext | `9f3dbc805b2da3c033f3955e4a2c60d36894c631a266aa4ab16f1c8e44a78ae9` | `9c989a2b4f12c811d8fdfaa903e863ea85f56fd1177b585f5f2082daaf1f648c` (180) |
| `Toy.Prophecy.backSem_eq_refSem_tight_noLentAccess` | counterexample (back-sound, hL) | propext | `35a3393a0676f1bbb9a41085628b029bff4e0a1cf2192741c669fb8e4f7bcb24` | `334f2ea9fef15d52f78862e88ad417681185762dc8c7549cb25d4ea8b40a1eee` (180) |
| `Toy.Prophecy.backSem_eq_refSem_tight_noUseAfterEnd` | counterexample (back-sound, hE) | propext | `71f0f2bd55b7b524ce0d10d29a1ba72634f81883c6e31fbf6883f00d6d2dac48` | `7430b0adb87cf174612aba9473aa169295bd1ce2e53f4513e255449b77ec2f19` (180) |
| `Toy.Prophecy.callDeep_prophOutcome_iff` | positive control (callee-exit-resolution) | Quot.sound, propext | `1b4ed996a35e335e8229505f529fec646564d90ca951c4c42758fb33051aff3e` | `398a85be96384cec2a7cc6828ab5c78d084596e2e680de70ccaa2dd92bf4c355` (102) |
| `Toy.Prophecy.calleeBack_eq_final_tight_rebind` | counterexample (callee-back-projection, hB) | propext | `1f3d5fc2bf344a919dbf22139adbb5bbacde3aff26cead10218dc0afd7828ac2` | `a7cf88d30bb19bde7cc663a22081843cb5eae49fb8f3be70532d46aeebf7aaed` (136) |
| `Toy.Prophecy.calleeBack_eq_final_tight_scoped` | counterexample (callee-back-projection, hS) | propext | `75772a1382c8fa835722bdc7bbf5a06cee73eafed1ef7958e872f4ef0073bb96` | `34981bce890f4223eb341b4b11df30ea80bc8991eeda3701446a3d723127d231` (136) |
| `Toy.Prophecy.deepCallee_nonvacuous` | non-vacuity (callee-back-projection); non-vacuity (callee-summary-agreement) | propext | `81c4460ee4a10a8537a8f8a033260f52864b3b5cdb278ebfa8750f970a30d44f` | `18917c1fef710b7b0166cd8a41916d8409b4dacd79b519514fccb2ec2ca16292` (169) |
| `Toy.Prophecy.inclusion_nonvacuous` | non-vacuity (proph-inclusion) | Quot.sound, propext | `ca77ab3ad3219fcbfcdfc03d67b7687319e36ddeb33699985597ecddeddf85ca` | `c120a74692ee939ad7596570cbe9f3008ee0045e7b04befebebef6c80250d4a4` (182) |
| `Toy.Prophecy.omission_keeps_real_nonvacuous` | non-vacuity (omission-keeps-real) | Quot.sound, propext | `b72a848ae0f1e8c77edac3ba778842275ac05b12337a293084cfe821c32cd1b9` | `0ea412987bdc92f839a612961265c1a1306217b4a333035bfa25e8b240ca688f` (180) |
| `Toy.Prophecy.omitting_callee_exit_resolution_admits_unproducible_store` | non-vacuity (callee-exit-resolution) | propext | `03db2199eae442105c511924e4f1cb979746f481afb465d35333bc6632dae37a` | `ff3c7da5bd25bd6fb61e3799c0e95c7dc93d2f16c7a91cb5c8cbaec18ab9629c` (180) |
| `Toy.Prophecy.omitting_resolution_keeps_real_store_writeThenRead` | non-vacuity (omission-monotone); non-vacuity (resolution-necessary) | Quot.sound, propext | `7b289e0cbe5e9befb11514d99886816bb09adb4b9b750fbc32e7fc904d6f456c` | `3d4a00b002962b4eba8497ab820e528405ab900f83518244402e3c449917d81f` (82) |
| `Toy.Prophecy.parent_resolution_while_reborrow_live_exact` | positive control (premature-resolution) | Quot.sound, propext | `4cce629f9cb02e601a11bc763b71926afcebcf54c2552d08f0bc36bb260a2c1f` | `32e2cad452eaa7a19b8cae242398b580e9d613fb38550b9952ea82ff661732bd` (100) |
| `Toy.Prophecy.premature_resolution_excludes_real_store` | non-vacuity (premature-resolution) | Quot.sound, propext | `36a0ce9816b2b7643d2a08cccd0a020920aefde570d077189490d0b979f49ab4` | `8a94692f525197f6e13d21d86654bc7c235d221627e8473da0798766c0812d08` (178) |
| `Toy.Prophecy.prophContract_iff_tight_frozenAccess` | counterexample (callee-summary-agreement, hF) | propext | `480cb0b760091bb1c27f344fec83affec98d1cf24a730c494f93fb5a957c889d` | `ef7b1857ba9a879af89d415ed362d93aefe7850217912b944a00de92c6213ab7` (168) |
| `Toy.Prophecy.prophContract_iff_tight_rebind` | counterexample (callee-summary-agreement, hB) | propext | `37141dfad97b8629c8d88f3bbb5bf10cecdde5d82dd303d810a988f1eceb50aa` | `4e21d7702cd016aa5fd37ff2c1f842ce0a8799cfca48297829ece383d34ae67e` (168) |
| `Toy.Prophecy.prophContract_iff_tight_useAfterEnd` | counterexample (callee-summary-agreement, hE) | propext | `ddf46029008c3f64bd77b2322d291bfbddb11c991f0290f8d9a1282695f0b3ca` | `4bdfe2e159971773ecac6a341d6d8533e4b5aaf0f898af6ed35d3b8c8d237714` (168) |
| `Toy.Prophecy.prophOutcomeWith_omitAtEnd_of_refSem_tight_noFrozenAccess` | counterexample (omission-keeps-real, hF) | Quot.sound, propext | `34d40d4bd6490b0d802ba3cc376b838c1582e8f03c3cf6bdcadae0331e59e018` | `c471291f6c893017f91b0f89db1008c32fe573204cf83b9c673924a4f4295b7b` (178) |
| `Toy.Prophecy.prophOutcomeWith_omitAtEnd_of_refSem_tight_noLentAccess` | counterexample (omission-keeps-real, hL) | Quot.sound, propext | `eda99f3526ad326529d2fa6e278fe5ef0fe4c410bafb69938807d8c032c46c9e` | `fba9d9195b6399f0244e4de7809daaadde51c84de0d7ecf0eca14f84e9ced806` (178) |
| `Toy.Prophecy.prophOutcomeWith_omitAtEnd_of_refSem_tight_noUseAfterEnd` | counterexample (omission-keeps-real, hE) | Quot.sound, propext | `67104cea67ac1a705fa4a5744e8f77ba0b140d806678e7c24a653361553e6c40` | `91e26ea96b9a50a5f65cb3cb7f3bd068a2c14aae2cb1b4c84f394df6df902c09` (178) |
| `Toy.Prophecy.prophOutcome_iff_backSem_tight_allEndedAtExit` | counterexample (agreement, hX) | propext | `d9a19f9675b61d9507a64023f7f4539e709b9a681d21b5b7eae731345b4c9248` | `afe854a59b820ca568f026568c00ffaca154524e1c7c48fcdcea1aeb520a7b2f` (204) |
| `Toy.Prophecy.prophOutcome_iff_backSem_tight_freshBindings` | counterexample (agreement, hB) | propext | `8548908f3e767b5cf5d854dee5bf9ffdd9afc8fd6f7f15261c12e5eb574cbdb8` | `b3682f3cabd9670bfe3ad17776007bcee5962ca869af24da35cffd2f1108cd0e` (204) |
| `Toy.Prophecy.prophOutcome_iff_backSem_tight_noFrozenAccess` | counterexample (agreement, hF) | propext | `00f8d25e48c3be204645234adb07d338e42256ad1c3c27927fc7c1806ac8b5a9` | `499e41f47eaf173d0a5753a61b49fa60c70f884789d50c2a7277b7bac78761eb` (204) |
| `Toy.Prophecy.prophOutcome_iff_backSem_tight_noLentAccess` | counterexample (agreement, hL) | propext | `da4e5a74f9d61787c48d3d38951729e593a28cabfc2588ecc6aa2788ed912fd0` | `f709d7602647bf0a85c9e833e1f8bfde3a774524d4d76628cbdd7ba7f7b6233a` (204) |
| `Toy.Prophecy.prophOutcome_iff_backSem_tight_noUseAfterEnd` | counterexample (agreement, hE) | Quot.sound, propext | `a71c5843aa65f34e0e3814057dbd9004cb92bc83d13ca0b640d9b8d828829a7b` | `936e60b7969d56f6fa10268a858a88863fabd57c60bd5c70e624b443e1c79998` (204) |
| `Toy.Prophecy.prophOutcome_iff_refSem_tight_allEndedAtExit` | counterexample (proph-sound, hX) | propext | `16501c9a2e09b86a38f47ad3d9d841ff3c45981dbdd55e24be94db7b8c0d6a88` | `91ad3b94904a7ed6497bd51343c46dfecb0bc8f638f3a6749af8edbfc3ae3fa5` (179) |
| `Toy.Prophecy.prophOutcome_iff_refSem_tight_freshBindings` | counterexample (proph-sound, hB) | propext | `647e0f205275f207cab1432ff4da5303602c17f6c8af5cb74e2eb7e873f35421` | `f3fffda68bdf16256f4f9b488ef405fd3b7f765df0642450d658552b18c1c34a` (179) |
| `Toy.Prophecy.prophOutcome_iff_refSem_tight_noFrozenAccess` | counterexample (proph-sound, hF) | propext | `d56cfadacfdb6856118e61290e9575224fff7b376df0d16d9c1da32b518e432f` | `7c3ffb5105d48e2767bba68ad748e029910f181653de0ab9c89676d3b5ad5a77` (179) |
| `Toy.Prophecy.prophOutcome_iff_refSem_tight_noLentAccess` | counterexample (proph-sound, hL) | propext | `1cc0e78b5501efdefe6500d22292fba156ce33ab853f22f2af76837d901bbe24` | `19333bdc06d527f115de8d2d476c53604c42f703c02b7bc9c02880d0e11d75f9` (179) |
| `Toy.Prophecy.prophOutcome_iff_refSem_tight_noUseAfterEnd` | counterexample (proph-sound, hE) | propext | `9cec26fe96032001a80ca5bc02ee704473cabd0648f5a1ddda22e49358d9daa1` | `dc2c56db1ee51e73ba60b4c989e84a1a17c5b4bebe0fc76e361dbed4aa35a582` (179) |
| `Toy.Prophecy.prophOutcome_of_refSem_tight_noFrozenAccess` | counterexample (proph-inclusion, hF) | Quot.sound, propext | `cf01a22b7398e853886642ab483e6b215984dc9d73194b356908c03db1f3ea92` | `65b308b4f0e551586650c5c58a7d390f5c1444b65c714991fc9dea659bf75989` (178) |
| `Toy.Prophecy.prophOutcome_of_refSem_tight_noLentAccess` | counterexample (proph-inclusion, hL) | Quot.sound, propext | `d43baa718601b3df5734c5878e3701b80b3409e7683b342d0830fb1d06a9db20` | `69862be90de87595b6ca4e101b3c7accaca4552e8675751c09d51c4f2d84ac56` (178) |
| `Toy.Prophecy.prophOutcome_of_refSem_tight_noUseAfterEnd` | counterexample (proph-inclusion, hE) | Quot.sound, propext | `ac6088b0ed2ade72034861214b977b6bbb4aaad4b3b818cc44fdf58974b1320e` | `c41ff77ffc997ed7b6c4e6423ba50046aba2a8337e2ed8353cd02869412ae312` (178) |
| `Toy.Prophecy.prophOutcome_pos` | non-vacuity (omission-monotone) | Quot.sound, propext | `ebeb294462424b453d9fa2f03d04c1fdf00d193b4939b35fb9ee361907982f51` | `e051ca0f4ad5ad15ef21bdaadcdfa407a59c6d09e2ce23a6b0808d7f44a58be3` (82) |
| `Toy.Prophecy.prophOutcome_writeThenRead_iff` | positive control (resolution-necessary) | Quot.sound, propext | `1ec28d97dedd427bfc75ba7166e0dbd355e1a0932788d8f2b360287dffbc0baf` | `461e0a1edb8a8ffee8729150382542cbf9e8e4f4b8139712981e03bbc4b22d5d` (101) |
| `Toy.Prophecy.resolution_after_last_write_exact` | positive control (premature-resolution) | Quot.sound, propext | `fca3d5dad14ddaf487cad90f8c72b4b710f240df41fdf1d61a8e885121cf0453` | `8206acc5eddf15fedba663cb045f2cd7b3a478b235852a8079083fb3317737b4` (100) |
| `Toy.Prophecy.richProg_nonvacuous` | non-vacuity (agreement); non-vacuity (back-sound); non-vacuity (proph-sound) | propext | `3907a635a756cc6b49e366127fce63a31f055614af554d963e83badb74d2b305` | `9fad5cdaab18c42fedffd16d8d1013daa5e0c178e285424de1a26fa6530ee2e1` (225) |
| `Toy.Prophecy.richProg_nonvacuous_other_branch` | non-vacuity (back-sound) | propext | `24ad684f39a61f46ec66ecf7d0d21372dacfa251fa5dad8b89109c4eb84889a1` | `c5bb0287ff94b6898cd96a4d1e0e9589a36f3ed2d000038b35446523a5f0b856` (103) |
| `Toy.Prophecy.selIncr_backward_shape` | non-vacuity (selection-shapes) | Quot.sound, propext | `0a1daca8a404c3bad3fd395e5bc1ac33fe985090114a5ef3140b4fe7686b02e5` | `0e25261a0161eca4d878f74cccaafdbe1dd93dc5f669cec52cdad6dcf54ce50c` (83) |
| `Toy.Prophecy.selIncr_both_translations_correct` | non-vacuity (selection-correct) | Quot.sound, propext | `57ec429a8804c1c44969c8c9d408bd60327a719f342bd85d6709f075d1fa9bf5` | `04b744fb380cfbcd4f6a5cb5ba61252abbda0c81a537e964d277e89bfe1eed12` (145) |
| `Toy.Prophecy.selIncr_prophecy_shape` | non-vacuity (selection-shapes) | Quot.sound, propext | `10144b0c0c389561897bc85bcbcf0bb609d20c0164f973dc242a607241e7bc21` | `a945f823bb2d813bb9edaa2155da9c65f72fbd639e5148b72cc07a9c21ba9874` (79) |
| `Toy.Prophecy.selLenders_depends_on_condition` | non-vacuity (selection-shapes) | Quot.sound, propext | `bae9022102a02a9e6fbd48e7ca9f5e25c7572f4f91b79840e46226d51062d9e2` | `0b8f6048dfe0e8302e11a317115f18afcda1040f135b09287f9733a32258fe8a` (1) |

**Primary sources.** Bibliographic records (title, venue, pages, year) of every
DOI below were checked against Crossref metadata on 2026-11-20. Each entry says,
in our words, what the cited part of the source states, and at which copy it was
read (publisher version, arXiv long version, HAL record or author copy); where
only a bibliographic record or abstract was examined, the entry says so. None of
these sources states a result relating backward-function and prophecy encodings
of mutable borrows; no such statement, on paper or mechanized, was found.

- [S1] Son Ho, Jonathan Protzenko. Aeneas: Rust Verification by Functional Translation. Proc. ACM Program. Lang. 6(ICFP), Article 116, pp. 711-741, 2022, doi:10.1145/3547647 (long version arXiv:2206.07185v2; section numbers below refer to it). In our words: a Rust function is translated to a pure forward function and backward functions; a backward function is called when a region ends and returns the new values of the borrowed inputs given the final values of the borrows handed out, which the paper presents as obviating the need for prophecy variables (Sec. 1); for the choose example (Sec. 2) the generated backward function is `choose_back b x y ret = if b then (ret, y) else (x, ret)`; borrows are ended lazily ('we reorganize borrows in a lazy fashion'); programs relying on interior mutability or unsafe code are out of scope (abstract); a proof of soundness of the semantics and translation is stated as the next unit of work (Sec. 7). Sec. 8 states that Electrolysis relies on lenses to model mutable borrows, so that functions may only return borrows to their first argument, and has no formal model.
- [S2] Son Ho, Aymeric Fromherz, Jonathan Protzenko. Sound Borrow-Checking for Rust via Symbolic Semantics. Proc. ACM Program. Lang. 8(ICFP), pp. 426-454, 2024, doi:10.1145/3674640 (long version arXiv:2404.02680). In our words: proves LLBC sound with respect to a low-level pointer-based language, LLBC's symbolic semantics a correct abstraction of LLBC, and symbolically checked programs free of getting stuck on a heap-and-addresses model (abstract); the correctness of the Aeneas functional translation is left to future work (Sec. 1); unsafe code is not considered.
- [S3] Son Ho. Formal Verification of Rust Programs by Functional Translation. PhD thesis, Université PSL (prepared at Inria Paris), defended 9 December 2024, HAL tel-05004605. In our words (HAL abstract): presents the Aeneas toolchain, which translates Rust programs that do not rely on interior mutability or unsafe code to a pure lambda-calculus. Only the bibliographic record and abstract were examined; the abstract does not say whether the functional translation is proved correct.
- [S4] Sebastian Ullrich. Simple Verification of Rust Programs via Functional Purification. Master's thesis, Karlsruhe Institute of Technology (KIT), 2016. In our words: shallowly embeds a substantial part of Rust into the purely functional language of the Lean theorem prover (abstract), modeling mutable references by lenses (Ch. 6). RustHorn (Sec. 5) states that this lens-based static tracking of addresses does not support dynamic selection of mutable references such as take_max; Aeneas (Sec. 8 of its long version) states that functions may only return borrows to their first argument.
- [S5] Yusuke Matsushita, Takeshi Tsukada, Naoki Kobayashi. RustHorn: CHC-Based Verification for Rust Programs. ESOP 2020, pp. 484-514, doi:10.1007/978-3-030-44914-8_18 (full version arXiv:2002.09002v2); extended journal version: ACM TOPLAS 43(4), Article 15, 2021, doi:10.1145/3462205. In our words (from the arXiv full version): a mutable reference is represented as a pair of the current target value and the target value at the end of the borrow, an idea the authors relate to prophecy variables (Sec. 1.2); in the core calculus COR every release of a variable is an explicit `drop x` (Sec. 2.1); in the CHC translation (Sec. 3.2) a mutable (re)borrow introduces a fresh variable for the value at the end of the borrow and hands it to the lender (for a reborrow, the parent's current value becomes that fresh variable), and when a mutable reference is dropped its prophesied value is equated with its current value; Theorem 1 states correctness of the CHC representation for COR, proved on paper; COR does not support unsafe code. Its take_max example (Sec. 1.2) specifies a borrow selected at run time by two clauses, one per branch, in which the released borrow's prophecy is constrained to its current value. Sec. 5 states that Electrolysis's lens-based static tracking of addresses does not support dynamic selection of mutable references such as take_max.
- [S6] Xavier Denis, Jacques-Henri Jourdan, C. Marché. Creusot: A Foundry for the Deductive Verification of Rust Programs. ICFEM 2022, Lecture Notes in Computer Science, Springer, pp. 90-105, doi:10.1007/978-3-031-17244-1_6 (author version HAL hal-03737878). In our words (author version): a borrow is translated to a Why3 record {current; final} (Sec. 3.2); creating `let y = &mut x` sets y to {current = x; final = any t} and immediately sets the lender x to y.final, which the paper justifies by the lender not being observable before the lifetime's end; when a borrow is dropped, the resolution `assume { y.final = y.current }` is inserted, which the paper explains as 'at this point the value pointed to by the borrow will not change'. The pick example (Figs. 2 and 3) specifies a run-time selected borrow with a case-split postcondition (if t then result = a and b.final = b.current, else symmetrically). Sec. 6 contrasts Creusot's final operator, which makes prophecies first-class in specifications, with Prusti's pledges. The paper states that Creusot does not permit the verification of unsafe code (Sec. 1).
- [S7] Yusuke Matsushita, Xavier Denis, Jacques-Henri Jourdan, Derek Dreyer. RustHornBelt: A Semantic Foundation for Functional Verification of Rust Programs with Unsafe Code. PLDI 2022, pp. 841-856, doi:10.1145/3519939.3523704 (HAL hal-03777103). In our words (full text): a machine-checked proof, in the Iris framework, of soundness of RustHorn-style verification, supporting first-order specifications of safe APIs implemented with unsafe code; its key mechanism is parametric prophecies (Sec. 3.2). Values that depend on prophecies live in the clairvoyant monad Clair A = ProphAsn -> A over prophecy assignments; the rule proph-resolve resolves a prophecy exactly once to a clairvoyant value that may depend on other prophecies provided those are still unresolved, which the paper needs for borrow subdivision and nested borrows, and which rules out the paradox of resolving x to y and then y to x + 1; the rule proph-sat states that the observations made are satisfied by some prophecy assignment (Sec. 3.2, pp. 848-850). The paper explains that the earlier Iris prophecy variables of Jung et al. do not allow resolving a prophecy to a value that mentions other, unresolved prophecies (Sec. 1, Sec. 5).
- [S8] Vytautas Astrauskas, Peter Müller, Federico Poli, Alexander J. Summers. Leveraging Rust Types for Modular Specification and Verification. Proc. ACM Program. Lang. 3(OOPSLA), Article 147, 2019, doi:10.1145/3360573. In our words: proposes pledges, a specification construct for functions that return mutable borrows: assertions in the postcondition about the borrowed-from places that are guaranteed to hold when the borrow expires (Sec. 6). This is a third specification style, besides backward functions and prophecies; it is not modeled here.
- [S9] Martín Abadi, Leslie Lamport. The Existence of Refinement Mappings. Theoretical Computer Science 82(2), pp. 253-284, 1991, doi:10.1016/0304-3975(91)90224-P (abridged version: LICS 1988, pp. 165-175, doi:10.1109/LICS.1988.5115). In our words: introduces prophecy variables, auxiliary variables that are the mirror image of history variables, so that refinement mappings exist when a specification makes a nondeterministic choice earlier than its implementation. The definition of a prophecy variable includes the condition that to every state of the original specification there corresponds a finite, non-zero number of states of the augmented one (condition P6 in the SRC Research Report 29 version of the paper; the label in the journal version was not checked). Cited for the origin of prophecy variables and for that non-emptiness requirement, which plays the role that inclusion (every real outcome is admitted by some prophecy assignment) plays here; the settings differ.
- [S10] Lennard Gäher, Michael Sammler, Ralf Jung, Robbert Krebbers, Derek Dreyer. RefinedRust: A Type System for High-Assurance Verification of Rust Programs. Proc. ACM Program. Lang. 8(PLDI), Article 192, pp. 1115-1139, 2024, doi:10.1145/3656422. In our words (abstract): a refinement type system, proven sound in Coq, for semi-automated functional correctness verification of both safe and unsafe Rust. Cited as related work; its treatment of mutable borrows was not examined here.
- [S11] Sacha-Élie Ayoun, Xavier Denis, Petar Maksimović, Philippa Gardner. A Hybrid Approach to Semi-automated Rust Verification. Proc. ACM Program. Lang. 9(PLDI), pp. 970-992, 2025, doi:10.1145/3729289 (extended version arXiv:2403.15122). In our words (abstract): Gillian-Rust automates a separation logic for Rust that embeds the lifetime logic of RustBelt and the parametric prophecies of RustHornBelt, and is linked with Creusot through an encoding of specifications of unsafe code that Creusot can use but cannot verify.
- [S12] Hiromi Ogawa, Taro Sekiyama, Hiroshi Unno. Thrust: A Prophecy-Based Refinement Type System for Rust. Proc. ACM Program. Lang. 9(PLDI), Article 230, pp. 2056-2080, 2025, doi:10.1145/3729333. In our words (abstract): a dependent refinement type system for Rust with refinement type inference based on Constrained Horn Clause solvers, which propagates update information to the original owner when a mutable borrow is released by means of a prophecy variable.
- [S13] Ralf Jung, Rodolphe Lepigre, Gaurav Parthasarathy, Marianna Rapoport, Amin Timany, Derek Dreyer, Bart Jacobs. The Future is Ours: Prophecy Variables in Separation Logic. Proc. ACM Program. Lang. 4(POPL), Article 45, 2020, doi:10.1145/3371113. In our words: prophecy variables in the Iris separation logic, aimed at logical atomicity of concurrent algorithms rather than at Rust borrows. Ownership of a prophecy assertion is exclusive and resolving the prophecy consumes it, which the paper uses to guarantee that a prophecy is resolved at most once (Sec. 1.2, Sec. 2.2); a prophecy predicts the value it will be resolved to if it is resolved at all (Sec. 1.2). In our reading this is a soundness concern about resolving twice, the counterpart of use after end here (cxAfterEndUnsat), not about omitting a resolution, which here costs only precision. RustHornBelt (Sec. 1, Sec. 5) explains why these prophecies are not directly usable for RustHorn-style borrows.
- [S14] Xavier Denis. Vérification déductive de programmes Rust (English title: Deductive Verification of Rust Programs). PhD thesis, Université Paris-Saclay, 2023, HAL tel-04517581; and Xavier Denis, Jacques-Henri Jourdan, C. Marché. The CREUSOT Environment for the Deductive Verification of Rust Programs. Inria Research Report RR-9448, 2021, HAL hal-03526634. Extended descriptions of Creusot; only their bibliographic records were examined, so where they place resolutions is not summarized here.

## Revalidation

**Requirements:** `elan` (so that `lake` uses the toolchain pinned in
`lean/lean-toolchain`) and `python3`. No network access is needed after the
toolchain is installed.

**Primary check**, run from the package directory:

```sh
python3 support/revalidate.py .
```

It copies `lean/` to a temporary directory (the package is not modified), runs
`lake build`, rejects `sorry`, `admit`, `native_decide` and `axiom` declarations
in the sources, then writes and runs a small Lean program that (1) computes
`collectAxioms` for every declaration of the library and fails if any axiom
other than `propext`, `Classical.choice`, `Quot.sound` occurs, and (2) for every
Lean name referenced by `results.json` or recorded in `audit/statements.json`,
recomputes two SHA-256 hashes and compares them with `audit/statements.json`:

- the *statement hash*: SHA-256 of `toString (repr ci.type)`, the `repr` of the
  declaration's type;
- the *closure hash*: SHA-256 of the newline-joined, sorted list of lines
  `name : repr(type) := repr(value)` (value omitted for theorems) for every
  constant of the library reachable from the statement's type through types,
  definition values and inductive constructors; `closure_size` is the number of
  lines.

A pass prints `ok   lake build`, `ok   axioms (… declarations)`,
`ok   statement hashes (52 hashed names; …)` and `REVALIDATED`. A changed
definition anywhere in a statement's closure changes its closure hash.

**Manual commands** (same toolchain):

```sh
cd lean
lake build
cat > /tmp/AxiomCheck.lean <<'EOF'
import ToyProphecy
#print axioms Toy.Prophecy.backSem_eq_refSem_of_discipline
#print axioms Toy.Prophecy.prophOutcome_iff_backSem_of_discipline
#print axioms Toy.Prophecy.prophOutcome_iff_refSem_of_discipline
#print axioms Toy.Prophecy.prophOutcome_of_refSem_of_noLentAccess_of_noFrozenAccess_of_noUseAfterEnd_of_freshBindings
#print axioms Toy.Prophecy.calleeBack_eq_final_of_calleeScoped_of_calleeFreshBindings
#print axioms Toy.Prophecy.prophContract_iff_backwardSummary_of_calleeNoFrozenAccess_of_calleeNoUseAfterEnd_of_calleeFreshBindings
EOF
lake env lean /tmp/AxiomCheck.lean
```

Each line should report a subset of `[propext, Classical.choice, Quot.sound]`.
The hash comparison is the program embedded in `support/revalidate.py`; it uses
only `lake env lean` and Python's `hashlib`.

A passing check establishes that the recorded statements are kernel-checked
under this toolchain; it says nothing about the modeling bridges, which must be
re-argued if the cited tools or papers are re-examined.
