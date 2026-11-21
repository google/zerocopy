import ToyDropFlags.Target

/-!
# Drop elaboration

Elaboration keeps the source CFG and inserts:

* flag maintenance: after an `init` the flags of its atoms are set; after a `move` they are
  cleared; before a call the flags of the arguments' atoms are cleared (so both the normal and
  the cleanup edge see them cleared); on a call's normal edge the destination's flags are set;
* at each drop point (`ret`/`resume`), a **drop ladder** over all atoms (in reverse atom order):
  per atom, an unconditional drop, nothing, or a flag test guarding a drop, chosen by a
  *decision map*;
* for a normal return, every drop in the ladder gets an unwind successor: a cleanup ladder that
  drops the atoms not yet visited (same decisions) and then resumes. Drops in cleanup code
  (the ladder at a `resume`, and these cleanup ladders) have **no** unwind successor (as cleanup
  drops in MIR have no cleanup of their own).

The decision map is a parameter; the standard map is computed from the analyses. The flag
maintenance has three knobs (`FlagConfig`) whose non-default values are the defects studied in
the tightness counterexamples.
-/

namespace Toy.DropFlags

/-- What elaboration does with one atom at one drop point. -/
inductive Decision where
  | drop
  | skip
  | test
  deriving DecidableEq, Repr

/-- The standard rule (as in rustc's classification of drop styles): not may-init → nothing;
must-init → unconditional drop; may-init but not must-init → flag test. -/
def stdDecision (may must : Bool) : Decision :=
  if !may then .skip else if must then .drop else .test

/-- The standard decision map at granularity `g`. -/
def stdMap (s : SProg) (g : Granularity) : Nat → Place → Decision :=
  fun i a => stdDecision (mayInit s g i a) (mustInit s g i a)

/-- Override one entry of a decision map. -/
def overrideAt (d : Nat → Place → Decision) (i : Nat) (a : Place) (x : Decision) :
    Nat → Place → Decision :=
  fun j b => if j = i ∧ b = a then x else d j b

/-- Flag-maintenance configuration. Defaults are the correct choices. `gran`: the granularity of
the flag updates performed at moves and call arguments. `clearArgsBeforeCall`: clear the flags
of call arguments before the call (`false`: only on the normal edge). `initSetsFlags i`: whether
the `init` at source node `i` sets its atoms' flags. -/
structure FlagConfig where
  gran : Granularity := .fine
  clearArgsBeforeCall : Bool := true
  initSetsFlags : Nat → Bool := fun _ => true

/-- The correct flag maintenance. -/
def FlagConfig.std : FlagConfig := {}

/-- Labels of elaborated programs: `src i` is the elaborated source node `i`; `pre`/`post`/`unw`
hold inserted flag updates around node `i`; `lad i k`/`dropAt i k` are the drop ladder at drop
point `i`, step `k`; `ulad i k`/`udropAt i k` the cleanup ladder entered when the drop at step
`k - 1` of the normal-return ladder at `i` panics. -/
inductive Lbl where
  | src (i : Nat)
  | pre (i : Nat)
  | post (i : Nat)
  | unw (i : Nat)
  | lad (i k : Nat)
  | dropAt (i k : Nat)
  | ulad (i k : Nat)
  | udropAt (i k : Nat)
  deriving DecidableEq, Repr

/-- Drop order of atoms at a drop point: reverse atom order (later locals first). -/
def dropOrder (ls : List Ty) : List Place := (allAtoms ls).reverse

/-- Flag assignments for a list of atoms. -/
def flagsFor (ps : List Place) (b : Bool) : List (Place × Bool) := ps.map fun a => (a, b)

/-- Atoms whose flags a call clears for its arguments. -/
def argKill (ls : List Ty) (g : Granularity) (args : List Place) : List Place :=
  args.flatMap (killSet ls g)

/-- Atoms of an optional destination. -/
def destAtoms (ls : List Ty) : Option Place → List Place
  | some d => atomsOf ls d
  | none => []

/-- The drop instruction for step `k` of a ladder at node `i`. -/
def ladderDrop (s : SProg) (i k : Nat) (cleanup : Bool) (a : Place) : TNode Lbl :=
  let normalRet := s.node i == .ret && !cleanup
  .drop a (if cleanup then .ulad i (k + 1) else .lad i (k + 1))
    (if normalRet then some (.ulad i (k + 1)) else none)

/-- Step `k` of the ladder at node `i` (`cleanup = true` for the cleanup ladder). -/
def ladderStep (d : Nat → Place → Decision) (s : SProg) (i k : Nat) (cleanup : Bool) :
    TNode Lbl :=
  match (dropOrder s.locals)[k]? with
  | none => if s.node i == .ret && !cleanup then .ret else .resume
  | some a =>
      match d i a with
      | .drop => ladderDrop s i k cleanup a
      | .skip => .goto (if cleanup then .ulad i (k + 1) else .lad i (k + 1))
      | .test => .test a (if cleanup then .udropAt i k else .dropAt i k)
                         (if cleanup then .ulad i (k + 1) else .lad i (k + 1))

/-- The guarded drop after a successful flag test at step `k` (`stuck` for an index past the
ladder, which no well-formed label reaches). -/
def ladderGuarded (s : SProg) (i k : Nat) (cleanup : Bool) : TNode Lbl :=
  match (dropOrder s.locals)[k]? with
  | none => .stuck
  | some a => ladderDrop s i k cleanup a

/-- The elaborated node at each label. A source index outside the program, and the inserted
labels at nodes of the wrong kind (which no well-formed run reaches), are `stuck`. -/
def elabNode (fc : FlagConfig) (d : Nat → Place → Decision) (s : SProg) : Lbl → TNode Lbl
  | .src i =>
      if i < s.nodes.length then
        match s.node i with
        | .init p _ => .init p (.post i)
        | .move p _ => .move p (.post i)
        | .branch a b => .branch (.src a) (.src b)
        | .call args _ _ _ =>
            .setFlags (if fc.clearArgsBeforeCall then flagsFor (argKill s.locals fc.gran args) false
                       else []) (.pre i)
        | .ret | .resume => .goto (.lad i 0)
        | .abort => .abort
      else .stuck
  | .pre i =>
      match s.node i with
      | .call args dest _ _ => .call args dest (.post i) (.unw i)
      | _ => .stuck
  | .post i =>
      match s.node i with
      | .init p nx =>
          .setFlags (if fc.initSetsFlags i then flagsFor (atomsOf s.locals p) true else []) (.src nx)
      | .move p nx => .setFlags (flagsFor (killSet s.locals fc.gran p) false) (.src nx)
      | .call args dest nx _ =>
          .setFlags ((if fc.clearArgsBeforeCall then []
                      else flagsFor (argKill s.locals fc.gran args) false) ++
                     flagsFor (destAtoms s.locals dest) true) (.src nx)
      | _ => .stuck
  | .unw i =>
      match s.node i with
      | .call _ _ _ un => .goto (.src un)
      | _ => .stuck
  | .lad i k => ladderStep d s i k false
  | .dropAt i k => ladderGuarded s i k false
  | .ulad i k => ladderStep d s i k true
  | .udropAt i k => ladderGuarded s i k true

/-- The elaborated program for flag configuration `fc` and decision map `d`. -/
def elaborate (fc : FlagConfig) (d : Nat → Place → Decision) (s : SProg) : TProg Lbl :=
  { locals := s.locals, entry := .src 0, node := elabNode fc d s }

/-- The standard elaboration: correct flag maintenance and the standard decision map. -/
def stdElab (s : SProg) : TProg Lbl := elaborate .std (stdMap s .fine) s

/-- Fuel for elaborated programs: enough for one visit of every source node (at most three
target steps each) and two ladders (at most two steps per atom plus one each). -/
def fuelFor (s : SProg) : Nat := 3 * s.nodes.length + 4 * (allAtoms s.locals).length + 4

/-- Run an elaborated program. -/
def runElab (rule : PanicRule) (fc : FlagConfig) (d : Nat → Place → Decision) (s : SProg)
    (inp : List Bool) : Result :=
  run rule (elaborate fc d s) (fuelFor s) inp

/-- **ElabCorrect** ("elaboration-correct"): on every input, the run of the elaborated program
terminates (returns, completes an unwind, or aborts; not `stuck`, not out of fuel) *and*
satisfies `ExactlyOnce`. Strictly stronger than `∀ inp, ExactlyOnce (runElab rule fc d s inp)`,
which a run that never terminates satisfies vacuously for NoLeak. -/
def ElabCorrect (rule : PanicRule) (fc : FlagConfig) (d : Nat → Place → Decision) (s : SProg) :
    Prop :=
  ∀ inp, ExactlyOnce (runElab rule fc d s inp) ∧ (runElab rule fc d s inp).outcome.terminated

/-- Drop points: `ret` and `resume` nodes. -/
def isDropPoint (s : SProg) (i : Nat) : Bool :=
  s.node i == .ret || s.node i == .resume

/-- A decision is *compatible* with the analyses at a point: a flag test always is; an
unconditional drop only where the atom is must-init; nothing only where it is not may-init. -/
def Compatible (may must : Bool) : Decision → Bool
  | .test => true
  | .drop => must
  | .skip => !may

/-- Some static decision (unconditional drop or nothing) is compatible exactly when the atom is
not "may-init but not must-init". -/
theorem staticChoice_compatible_iff (may must : Bool) :
    (Compatible may must .drop = true ∨ Compatible may must .skip = true) ↔
      ¬ (may = true ∧ must = false) := by
  cases may <;> cases must <;> decide

/-- Every decision at every forward-reachable drop point is compatible with the fine analyses.
Decisions at drop points that are not forward-reachable are unconstrained. -/
def AllCompatible (s : SProg) (d : Nat → Place → Decision) : Prop :=
  ∀ i < s.nodes.length, isDropPoint s i = true → ForwardReachable s i = true →
    ∀ a ∈ allAtoms s.locals, Compatible (mayInit s .fine i a) (mustInit s .fine i a) (d i a) = true

instance (s : SProg) (d : Nat → Place → Decision) : Decidable (AllCompatible s d) := by
  unfold AllCompatible; exact inferInstance

/-- The flag set of a decision map: the atoms (in atom order) that `d` tests at some
forward-reachable drop point. This counts flag *tests*; the elaboration maintains a flag for
every atom regardless (flag stores are free in this model). -/
def flagSet (s : SProg) (d : Nat → Place → Decision) : List Place :=
  (allAtoms s.locals).filter fun a =>
    (List.range s.nodes.length).any fun i =>
      isDropPoint s i && ForwardReachable s i && d i a == .test

/-- The decisions of the standard map are always compatible. -/
theorem stdDecision_compatible (may must : Bool) :
    Compatible may must (stdDecision may must) = true := by
  cases may <;> cases must <;> rfl

/-- A drop point is an in-range node (out-of-range indices read as `abort`). -/
theorem lt_of_isDropPoint (s : SProg) (i : Nat) (h : isDropPoint s i = true) :
    i < s.nodes.length := by
  apply Classical.byContradiction
  intro hlt
  have hnode : s.node i = .abort := by
    simp only [SProg.node, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega)]
    rfl
  simp [isDropPoint, hnode] at h

end Toy.DropFlags
