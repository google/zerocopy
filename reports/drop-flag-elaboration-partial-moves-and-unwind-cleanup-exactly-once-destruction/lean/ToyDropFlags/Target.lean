import ToyDropFlags.Source

/-!
# Target language and its semantics

The target language is the source language plus explicit drops, boolean drop flags, flag
updates and flag tests. Labels are arbitrary (`L`), so elaborated programs can use structured
labels. Memory is **not** cleared by moves: after a move the moved-from units still hold the old
(now stale) value ids, as in non-zeroing dynamic drop. A `drop a` runs the drop glue of atom
`a` blindly on the memory contents: it logs one destructor call per unit inside `a` (or
`garbage` for a unit that was never written).

Choices are supplied by an input stream of booleans, consumed one per choice point: a `branch`
picks its successor, a `call` panics or returns, and a `drop` decides whether the destructor
(the drop glue of the atom, as a whole) panics after running. An exhausted input reads `false`.
Drop glue is treated as one step: a panic in it happens after all of the atom's units have been
destroyed (glue-internal cleanup always completes).

Panics. A panic in a call or in a destructor transfers control to the instruction's unwind
successor and sets the unwinding mode. A destructor panic *while already unwinding* is a double
panic and is resolved by the `PanicRule`: `abort` terminates (the double-panic rule) and
`continueUnwind` treats it like any other panic. A panicking instruction without an unwind
successor exits the frame (the panic propagates to the caller): the run ends with outcome
`unwound`, exactly like `resume`.
-/

namespace Toy.DropFlags

/-- Target instructions over labels `L`. `setFlags` assigns drop flags; `test a l₁ l₂` branches
on the drop flag of atom `a`; `drop a next unwind` runs the drop glue of atom `a`; `unwind = none`
means no landing pad (a panic leaves the frame). `stuck` marks an ill-formed program point (for
example a jump to a node index outside the source program); a run reaching it ends with outcome
`stuck`, which does not count as termination. -/
inductive TNode (L : Type) where
  | init (p : Place) (next : L)
  | move (p : Place) (next : L)
  | call (args : List Place) (dest : Option Place) (next unwind : L)
  | branch (l₁ l₂ : L)
  | goto (l : L)
  | setFlags (us : List (Place × Bool)) (next : L)
  | test (a : Place) (ifSet ifClear : L)
  | drop (a : Place) (next : L) (unwind : Option L)
  | ret
  | resume
  | abort
  | stuck
  deriving Repr

/-- A target program: locals, entry label, and the node at each label. -/
structure TProg (L : Type) where
  locals : List Ty
  entry : L
  node : L → TNode L

/-- What happens when a destructor panics while the frame is already unwinding. -/
inductive PanicRule where
  | abort
  | continueUnwind
  deriving DecidableEq, Repr

/-- How a run ends. `returned`: normal return. `unwound`: a completed unwind (the panic left the
frame). `aborted`: process abort (an explicit `abort` instruction, or a destructor panic during
unwinding under `PanicRule.abort`). `stuck`: the run reached an ill-formed program point
(`TNode.stuck`). `outOfFuel`: the step bound was exhausted. Only the first three count as
termination (`Outcome.terminated`). -/
inductive Outcome where
  | returned
  | unwound
  | aborted
  | stuck
  | outOfFuel
  deriving DecidableEq, Repr

/-- The result of a run: its outcome and its event log (in chronological order). -/
structure Result where
  outcome : Outcome
  log : List Event
  deriving DecidableEq, Repr

/-- Machine state. `mem` maps each unit to the id of the value last written there (stale after a
move); `flags` maps atoms to drop-flag values (all `false` initially). -/
structure Mach (L : Type) where
  pc : L
  unwinding : Bool
  mem : Place → Option Nat
  flags : Place → Bool
  fresh : Nat
  log : List Event

/-- Write fresh ids into the given units, logging creations. -/
def writeFresh : List Place → (Place → Option Nat) → Nat → List Event →
    (Place → Option Nat) × Nat × List Event
  | [], mem, n, log => (mem, n, log)
  | u :: us, mem, n, log =>
      writeFresh us (fun q => if q = u then some n else mem q) (n + 1) (log ++ [.create n])

/-- Destruction events for the given units, built with `mk` (`.consume` or `.drop`). -/
def destroyEvents (mk : Nat → Event) (mem : Place → Option Nat) (us : List Place) :
    List Event :=
  us.map fun u => match mem u with
    | some v => mk v
    | none => .garbage

/-- Apply flag assignments (later assignments win). -/
def applyFlags : List (Place × Bool) → (Place → Bool) → (Place → Bool)
  | [], f => f
  | (a, b) :: us, f => applyFlags us (fun q => if q = a then b else f q)

/-- Choice points consume one input bit. -/
def TNode.isChoice {L : Type} : TNode L → Bool
  | .call .. | .branch .. | .drop .. => true
  | _ => false

/-- One step: either the run ends or a new machine state. `b` is the choice bit (ignored at
non-choice nodes). -/
inductive Step (L : Type) where
  | done (r : Result)
  | next (m : Mach L)

/-- The one-step semantics. -/
def step {L : Type} (rule : PanicRule) (P : TProg L) (m : Mach L) (b : Bool) : Step L :=
  match P.node m.pc with
  | .init p nx =>
      let w := writeFresh (unitsUnder P.locals p) m.mem m.fresh m.log
      .next { m with pc := nx, mem := w.1, fresh := w.2.1, log := w.2.2 }
  | .move p nx =>
      .next { m with pc := nx,
                     log := m.log ++ destroyEvents .consume m.mem (unitsUnder P.locals p) }
  | .call args dest nx un =>
      let log₁ := m.log ++
        args.flatMap (fun p => destroyEvents .consume m.mem (unitsUnder P.locals p))
      if b then .next { m with pc := un, unwinding := true, log := log₁ }
      else
        match dest with
        | none => .next { m with pc := nx, log := log₁ }
        | some d =>
            let w := writeFresh (unitsUnder P.locals d) m.mem m.fresh log₁
            .next { m with pc := nx, mem := w.1, fresh := w.2.1, log := w.2.2 }
  | .branch l₁ l₂ => .next { m with pc := if b then l₁ else l₂ }
  | .goto l => .next { m with pc := l }
  | .setFlags us nx => .next { m with pc := nx, flags := applyFlags us m.flags }
  | .test a l₁ l₂ => .next { m with pc := if m.flags a then l₁ else l₂ }
  | .drop a nx un =>
      let log₁ := m.log ++ destroyEvents .drop m.mem (unitsUnder P.locals a)
      if !b then .next { m with pc := nx, log := log₁ }
      else if m.unwinding && rule == .abort then .done ⟨.aborted, log₁⟩
      else
        match un with
        | some l => .next { m with pc := l, unwinding := true, log := log₁ }
        | none => .done ⟨.unwound, log₁⟩
  | .ret => .done ⟨.returned, m.log⟩
  | .resume => .done ⟨.unwound, m.log⟩
  | .abort => .done ⟨.aborted, m.log⟩
  | .stuck => .done ⟨.stuck, m.log⟩

/-- Initial machine state. -/
def initMach {L : Type} (P : TProg L) : Mach L :=
  { pc := P.entry, unwinding := false, mem := fun _ => none, flags := fun _ => false,
    fresh := 0, log := [] }

/-- Run with fuel and an input stream. -/
def runAux {L : Type} (rule : PanicRule) (P : TProg L) : Nat → List Bool → Mach L → Result
  | 0, _, m => ⟨.outOfFuel, m.log⟩
  | k + 1, inp, m =>
      if (P.node m.pc).isChoice then
        match step rule P m (inp.headD false) with
        | .done r => r
        | .next m' => runAux rule P k inp.tail m'
      else
        match step rule P m false with
        | .done r => r
        | .next m' => runAux rule P k inp m'

/-- Run a target program from its entry. -/
def run {L : Type} (rule : PanicRule) (P : TProg L) (fuel : Nat) (inp : List Bool) : Result :=
  runAux rule P fuel inp (initMach P)

/-! ## Exhaustive exploration -/

/-- All runs as a binary decision tree over the choice bits. -/
inductive RunTree where
  | leaf (r : Result)
  | node (ifTrue ifFalse : RunTree)
  deriving DecidableEq, Repr

/-- The run selected by an input stream. -/
def RunTree.follow : RunTree → List Bool → Result
  | .leaf r, _ => r
  | .node _ f, [] => f.follow []
  | .node t f, b :: bs => (if b then t else f).follow bs

/-- Every run in the tree satisfies `p`. -/
def RunTree.all (p : Result → Bool) : RunTree → Bool
  | .leaf r => p r
  | .node t f => t.all p && f.all p

/-- Some run in the tree satisfies `p`. -/
def RunTree.any (p : Result → Bool) : RunTree → Bool
  | .leaf r => p r
  | .node t f => t.any p || f.any p

/-- Build the tree of all runs. -/
def exploreAux {L : Type} (rule : PanicRule) (P : TProg L) : Nat → Mach L → RunTree
  | 0, m => .leaf ⟨.outOfFuel, m.log⟩
  | k + 1, m =>
      let cont : Step L → RunTree := fun
        | .done r => .leaf r
        | .next m' => exploreAux rule P k m'
      if (P.node m.pc).isChoice then .node (cont (step rule P m true)) (cont (step rule P m false))
      else cont (step rule P m false)

/-- The tree of all runs of a target program. -/
def explore {L : Type} (rule : PanicRule) (P : TProg L) (fuel : Nat) : RunTree :=
  exploreAux rule P fuel (initMach P)

theorem runAux_eq_follow {L : Type} (rule : PanicRule) (P : TProg L) :
    ∀ (k : Nat) (inp : List Bool) (m : Mach L),
      runAux rule P k inp m = (exploreAux rule P k m).follow inp := by
  intro k
  induction k with
  | zero => intro inp m; simp [runAux, exploreAux, RunTree.follow]
  | succ k ih =>
    intro inp m
    by_cases hc : (P.node m.pc).isChoice = true
    · cases inp with
      | nil =>
        simp only [runAux, exploreAux, hc, ite_true, List.headD_nil, List.tail_nil,
          RunTree.follow]
        cases step rule P m false with
        | done r => simp [RunTree.follow]
        | next m' => simp [ih]
      | cons b bs =>
        simp only [runAux, exploreAux, hc, ite_true, List.headD_cons, List.tail_cons,
          RunTree.follow]
        cases b with
        | true =>
          cases step rule P m true with
          | done r => simp [RunTree.follow]
          | next m' => simp [ih]
        | false =>
          cases step rule P m false with
          | done r => simp [RunTree.follow]
          | next m' => simp [ih]
    · have hc' : (P.node m.pc).isChoice = false := by simpa using hc
      simp only [runAux, exploreAux, hc']
      cases step rule P m false with
      | done r => simp [RunTree.follow]
      | next m' => simp [ih]

/-- Running with any input equals following that input through the exploration tree. -/
theorem run_eq_follow {L : Type} (rule : PanicRule) (P : TProg L) (fuel : Nat)
    (inp : List Bool) : run rule P fuel inp = (explore rule P fuel).follow inp :=
  runAux_eq_follow rule P fuel inp (initMach P)

theorem RunTree.follow_of_all (p : Result → Bool) :
    ∀ (t : RunTree) (inp : List Bool), t.all p = true → p (t.follow inp) = true := by
  intro t
  induction t with
  | leaf r => intro inp h; simpa [RunTree.all, RunTree.follow] using h
  | node t f iht ihf =>
    intro inp h
    simp only [RunTree.all, Bool.and_eq_true] at h
    cases inp with
    | nil => simpa [RunTree.follow] using ihf [] h.2
    | cons b bs =>
      cases b
      · simpa [RunTree.follow] using ihf bs h.2
      · simpa [RunTree.follow] using iht bs h.1

/-- Checking every run of the exploration tree checks every input. -/
theorem forall_run_of_explore_all {L : Type} (rule : PanicRule) (P : TProg L) (fuel : Nat)
    (p : Result → Bool) (h : (explore rule P fuel).all p = true) :
    ∀ inp, p (run rule P fuel inp) = true := by
  intro inp
  rw [run_eq_follow]
  exact RunTree.follow_of_all p _ inp h

/-- Equal exploration trees give equal runs on every input. -/
theorem run_eq_of_explore_eq {L L' : Type} (rule : PanicRule) (P : TProg L) (Q : TProg L')
    (fuel fuel' : Nat) (h : explore rule P fuel = explore rule Q fuel') :
    ∀ inp, run rule P fuel inp = run rule Q fuel' inp := by
  intro inp
  rw [run_eq_follow, run_eq_follow, h]

/-! ## Exactly-once -/

/-- A run is *complete* if it ends in a normal return or a completed unwind. -/
def Outcome.complete : Outcome → Bool
  | .returned | .unwound => true
  | _ => false

/-- A run *terminates* if it returns, completes an unwind, or aborts. -/
def Outcome.terminated : Outcome → Bool
  | .returned | .unwound | .aborted => true
  | _ => false

/-- **ExactlyOnce** for one run: NoDoubleDrop on the log (whatever the outcome), and NoLeak if the
run is complete (returned or unwound). Runs with outcome `aborted`, `stuck` or `outOfFuel` are
exempt from NoLeak; for the latter two this is why `ElabCorrect` separately requires
termination. -/
def ExactlyOnce (r : Result) : Prop :=
  NoDoubleDrop r.log ∧ (r.outcome.complete = true → NoLeak r.log)

instance (r : Result) : Decidable (ExactlyOnce r) := by unfold ExactlyOnce; exact inferInstance

/-- Boolean form of `ExactlyOnce ∧ terminated`, for exhaustive checking. -/
def goodRun (r : Result) : Bool := decide (ExactlyOnce r) && r.outcome.terminated

theorem goodRun_iff (r : Result) :
    goodRun r = true ↔ ExactlyOnce r ∧ r.outcome.terminated = true := by
  simp [goodRun]

end Toy.DropFlags
