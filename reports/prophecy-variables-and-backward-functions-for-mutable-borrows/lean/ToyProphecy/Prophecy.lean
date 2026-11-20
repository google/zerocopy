import ToyProphecy.Backward

/-!
# Prophecy translation

The translation in the style of prophecy-based encodings of mutable borrows: a
live mutable borrow is a pair `(cur, fin)` of its current value and a *prophecy*
`fin` standing for its final value. Creating a borrow draws a fresh prophecy
`φ k` and hands it to the lender (the lent local, or the parent borrow's current
value); ending the borrow emits the *resolution constraint* `cur = fin`. The
translation is parameterised by an assignment `φ : Nat → Int` of values to
prophecy indices and returns a final state together with the list of emitted
constraints; the admitted outcomes are those produced by assignments that
satisfy every constraint (`ProphOutcome`).

A call `s = f(&mut *r)` passes a reborrow `(cur_r, φ k)` of `r` as the callee's
parameter, runs the callee body's own prophecy translation in a fresh frame
(drawing further prophecies from the same counter), and on return resolves
every borrow of the callee frame that is still live other than the returned one
(in a disciplined callee these are exactly the parameter and the reborrows
between it and the returned borrow). The caller's `s` is the returned pair.

Which resolutions are emitted is controlled by a `ResPolicy`; the standard
policy `ResPolicy.std` resolves each borrow exactly when it ends and resolves
callee borrows at callee exit. The other policies exist to state precisely what
goes wrong when resolution is omitted or misplaced.

The translation performs no borrow checking.
-/

namespace Toy.Prophecy

/-- A live borrow in the prophecy translation: current value, prophecy of its
final value, and whether it has already been resolved (used at callee exit). -/
structure PRef where
  cur : Int
  fin : Int
  done : Bool
  deriving Repr, DecidableEq

/-- State of the prophecy translation. `next` is the next fresh prophecy index;
`cs` the resolution constraints emitted so far (each pair means `lhs = rhs`). -/
structure PState where
  store : Store
  refs : RefVar → Option PRef
  next : Nat
  cs : List (Int × Int)

/-- A list of resolution constraints is satisfied when both sides of every pair
are equal. -/
def Sat (cs : List (Int × Int)) : Prop := ∀ c ∈ cs, c.1 = c.2

instance (cs : List (Int × Int)) : Decidable (Sat cs) :=
  inferInstanceAs (Decidable (∀ c ∈ cs, c.1 = c.2))

/-- Where resolution constraints are emitted. -/
structure ResPolicy where
  /-- main program: emit `cur = fin` for `r` when `r` ends -/
  atEnd : RefVar → Bool
  /-- emit `cur = fin` for every still-live, non-returned callee borrow at callee exit -/
  atCalleeExit : Bool
  /-- main program: after statement `i`, additionally emit `cur = fin` for these borrows -/
  early : Nat → List RefVar

/-- The standard policy: resolve each borrow exactly when it ends, and resolve the
callee's remaining borrows at callee exit. -/
def ResPolicy.std : ResPolicy :=
  { atEnd := fun _ => true, atCalleeExit := true, early := fun _ => [] }

/-- The standard policy except that no `endBorrow r` statement of the main
program emits a resolution constraint. The policy is keyed by the *name* `r`:
if the main program binds and ends `r` several times, every one of those ends is
unresolved. Callee frames are unaffected (callee bodies and callee-exit
resolution always use the standard rule). -/
def ResPolicy.omitAtEnd (r : RefVar) : ResPolicy :=
  { ResPolicy.std with atEnd := fun r' => decide (r' ≠ r) }

/-- The standard policy except that callee borrows are not resolved at callee
exit. -/
def ResPolicy.omitAtCalleeExit : ResPolicy :=
  { ResPolicy.std with atCalleeExit := false }

/-- Borrow `r` of the main program is resolved right after statement `i` instead
of when it ends. -/
def ResPolicy.resolveAfter (i : Nat) (r : RefVar) : ResPolicy :=
  { atEnd := fun r' => decide (r' ≠ r), atCalleeExit := true,
    early := fun j => if j = i then [r] else [] }

/-- Expression evaluation: reading through a borrow reads its current value;
reading a lent local reads whatever the local holds (the lender's prophecy). -/
def evalP (L : Bool) (s : PState) : Expr → Option Int
  | .lit n => some n
  | .var x => if L then some (s.store x) else none
  | .deref r => (s.refs r).map (·.cur)
  | .add a b => do
      let u ← evalP L s a
      let v ← evalP L s b
      pure (u + v)

/-- One basic operation in the prophecy translation. `res r` says whether ending
`r` emits its resolution constraint. -/
def stepOpP (L : Bool) (res : RefVar → Bool) (φ : Nat → Int) (s : PState) : Op → Option PState
  | .assign x e =>
      if L then (evalP L s e).map fun v => { s with store := s.store.set x v } else none
  | .borrow r x =>
      if L then
        some { s with
          refs := fupd s.refs r (some { cur := s.store x, fin := φ s.next, done := false })
          store := s.store.set x (φ s.next)
          next := s.next + 1 }
      else none
  | .borrowSel r c x y =>
      if L then (evalP L s c).map fun cv =>
        if cv ≠ 0 then
          { s with
            refs := fupd s.refs r (some { cur := s.store x, fin := φ s.next, done := false })
            store := s.store.set x (φ s.next)
            next := s.next + 1 }
        else
          { s with
            refs := fupd s.refs r (some { cur := s.store y, fin := φ s.next, done := false })
            store := s.store.set y (φ s.next)
            next := s.next + 1 }
      else none
  | .reborrow t r => (s.refs r).map fun q =>
      { s with
        refs := fupd (fupd s.refs r (some { q with cur := φ s.next }))
                  t (some { cur := q.cur, fin := φ s.next, done := false })
        next := s.next + 1 }
  | .write r e => do
      let q ← s.refs r
      let v ← evalP L s e
      pure { s with refs := fupd s.refs r (some { q with cur := v }) }
  | .endBorrow r => (s.refs r).map fun q =>
      { s with
        refs := fupd s.refs r (some { q with done := true })
        cs := if res r then s.cs ++ [(q.cur, q.fin)] else s.cs }

/-- Run a list of basic operations in the prophecy translation. -/
def runOpsP (L : Bool) (res : RefVar → Bool) (φ : Nat → Int) : PState → List Op → Option PState
  | s, [] => some s
  | s, o :: os => (stepOpP L res φ s o).bind fun s' => runOpsP L res φ s' os

/-- The reference variable bound by a basic operation, if any. -/
def Op.binds : Op → Option RefVar
  | .borrow r _ => some r
  | .borrowSel r _ _ _ => some r
  | .reborrow t _ => some t
  | _ => none

/-- The reference variables of a callee frame: the parameter and every reference
variable bound in the body. -/
def Callee.refNames (f : Callee) : List RefVar :=
  (Callee.param :: f.body.filterMap Op.binds).eraseDups

/-- The callee frame at entry: the parameter is `(a, pf)`; fresh prophecies are
drawn from index `n` on. -/
def calleeInitP (a pf : Int) (n : Nat) : PState :=
  { store := fun _ => 0
    refs := fupd (fun _ => none) Callee.param (some { cur := a, fin := pf, done := false })
    next := n
    cs := [] }

/-- Resolution at callee exit: emit `cur = fin` for every reference variable of
the frame, other than the returned one, that is bound and not yet resolved. -/
def calleeExitCs (f : Callee) (s : PState) : List (Int × Int) :=
  (f.refNames.filter fun j => j ≠ f.ret).filterMap fun j =>
    match s.refs j with
    | some p => if p.done then none else some (p.cur, p.fin)
    | none => none

/-- Run a callee body in the prophecy translation from parameter `(a, pf)`,
drawing prophecies from index `n`, then (if `exitRes`) append the callee-exit
resolutions. -/
def calleeRunP (exitRes : Bool) (φ : Nat → Int) (f : Callee) (a pf : Int) (n : Nat) :
    Option PState :=
  (runOpsP false (fun _ => true) φ (calleeInitP a pf n) f.body).map fun s =>
    { s with cs := if exitRes then s.cs ++ calleeExitCs f s else s.cs }

/-- Emit the early resolutions scheduled after statement `i`. -/
def earlyCs (pol : ResPolicy) (i : Nat) (s : PState) : List (Int × Int) :=
  (pol.early i).filterMap fun r => (s.refs r).map fun q => (q.cur, q.fin)

/-- One main-program statement (with index `i`) in the prophecy translation. -/
def stepP (pol : ResPolicy) (φ : Nat → Int) (i : Nat) (s : PState) (c : Stmt) : Option PState :=
  let s1 : Option PState := match c with
    | .op o => stepOpP true pol.atEnd φ s o
    | .call t f r => do
        let q ← s.refs r
        let k := s.next
        let fr ← calleeRunP pol.atCalleeExit φ f q.cur (φ k) (k + 1)
        let ret ← fr.refs f.ret
        pure { s with
          refs := fupd (fupd s.refs r (some { q with cur := φ k }))
                    t (some { cur := ret.cur, fin := ret.fin, done := false })
          next := fr.next
          cs := s.cs ++ fr.cs }
  s1.map fun s' => { s' with cs := s'.cs ++ earlyCs pol i s' }

/-- Run a main program in the prophecy translation; `i` is the index of the
first statement. -/
def runP (pol : ResPolicy) (φ : Nat → Int) : Nat → PState → Prog → Option PState
  | _, s, [] => some s
  | i, s, c :: cs => (stepP pol φ i s c).bind fun s' => runP pol φ (i + 1) s' cs

/-- The initial state: store `σ`, no borrow, prophecy counter `0`, no constraint. -/
def PState.init (σ : Store) : PState :=
  { store := σ, refs := fun _ => none, next := 0, cs := [] }

/-- `σ'` is a final store admitted by the prophecy translation of `P` from `σ`
under resolution policy `pol`: some prophecy assignment runs the translation to
completion, satisfies every emitted resolution constraint, and ends in `σ'`. -/
def ProphOutcomeWith (pol : ResPolicy) (P : Prog) (σ σ' : Store) : Prop :=
  ∃ φ : Nat → Int, ∃ s : PState,
    runP pol φ 0 (PState.init σ) P = some s ∧ Sat s.cs ∧ s.store = σ'

/-- Admitted final stores under the standard resolution policy. -/
def ProphOutcome (P : Prog) (σ σ' : Store) : Prop := ProphOutcomeWith ResPolicy.std P σ σ'

/-- The prophecy contract of a callee: argument current value `a`, argument
prophecy (final value) `pf`, returned borrow `(c, rf)`, for some assignment of the
callee's internal prophecies satisfying the callee's resolution constraints
(including those emitted at callee exit). Internal prophecies are drawn from
index `0` of the existentially quantified assignment. -/
def ProphContract (f : Callee) (a c pf rf : Int) : Prop :=
  ∃ φ : Nat → Int, ∃ s : PState,
    calleeRunP true φ f a pf 0 = some s ∧ Sat s.cs ∧
    ∃ q : PRef, s.refs f.ret = some q ∧ q.cur = c ∧ q.fin = rf

end Toy.Prophecy
