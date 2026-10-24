import AnnealResearch.PrefixTransfer

/-!
Owned two-field cleanup elaboration, not a Rust frontend or full MiniRust.
The source binding, constructor temporaries, ABI/layout and actual destructor
bodies remain the audited English obligations in docs/rust-opsem/cleanup-elaboration.md. Double panic
has an explicit owned abort policy; Rust coverage excludes that case.
-/
namespace AnnealResearch.CleanupElaboration

open Execution PrefixTransfer

inductive Field where | first | second deriving DecidableEq, Repr
inductive Mode where | normal | unwinding deriving DecidableEq, Repr
inductive Code where | ret | unwind | read | spin deriving DecidableEq, Repr
inductive Event where
  | built (f : Field) | ctorUnwind (f : Field) | moved (f : Field)
  | entered (f : Field) | returned (f : Field) | unwound (f : Field)
  | read (f : Field) | bad (f : Field) | spinning (f : Field)
  | normalExit | unwindExit | loop | abort
  deriving DecidableEq, Repr

structure Flags where
  first : Bool := false
  second : Bool := false
  deriving DecidableEq, Repr
def Flags.get (b : Flags) : Field → Bool
  | .first => b.first | .second => b.second
def Flags.set (b : Flags) (f : Field) (v : Bool) : Flags :=
  match f with | .first => { b with first := v } | .second => { b with second := v }

structure Data where
  owed : Flags := {} -- An obligation is not byte initialization.
  payload : Flags := {} -- Destructor-readable payload stays present at call entry.
  trace : List Event := []
  deriving DecidableEq, Repr
def Data.emit (d : Data) (e : Event) : Data := { d with trace := d.trace ++ [e] }
def Data.build (d : Data) (f : Field) : Data :=
  { d with owed := d.owed.set f true, payload := d.payload.set f true } |>.emit (.built f)
def Data.consume (d : Data) (f : Field) : Data := { d with owed := d.owed.set f false }
def Data.finish (d : Data) (f : Field) : Data := { d with payload := d.payload.set f false }
def Data.moveSecond (d : Data) : Data :=
  { d with owed := d.owed.set .second false, payload := d.payload.set .second false }
    |>.emit (.moved .second)

structure Plan where
  ctor : Field → Bool := fun _ => true -- false means actual unwind, not UB.
  drop : Field → Code := fun _ => .ret
  readable : Flags := ⟨true, true⟩ -- Abstract pointee-read premise, not MiniRust memory.
  takeSecond : Bool := false
  bodyPanics : Bool := false
def fields : List Field := [.first, .second]
def preparedBody (p : Plan) (d : Data) : Data := if p.takeSecond then d.moveSecond else d
def Movable (p : Plan) (d : Data) : Prop := p.takeSecond = true → d.owed.second = true
def canRead (p : Plan) (d : Data) (f : Field) : Bool :=
  d.payload.get f && p.readable.get f

inductive HighControl where
  | construct (f : Field) | body | clean (remaining : List Field) (mode : Mode)
  | running (f : Field) (remaining : List Field) (mode : Mode) (code : Code)
  | spin | done | bad | abort | aborted
  deriving DecidableEq, Repr
structure HighState where
  control : HighControl
  data : Data
  deriving DecidableEq, Repr
def afterCtor : Field → HighControl
  | .first => .construct .second | .second => .body

/-- Source cleanup selects the remaining owned values directly. -/
inductive HighStep (p : Plan) : HighState → HighState → Prop where
  | ctorReturn (d f) (ok : p.ctor f = true) :
      HighStep p ⟨.construct f, d⟩ ⟨afterCtor f, d.build f⟩
  | ctorUnwind (d f) (fails : p.ctor f = false) :
      HighStep p ⟨.construct f, d⟩ ⟨.clean fields .unwinding, d.emit (.ctorUnwind f)⟩
  | bodyNormal (d) (normal : p.bodyPanics = false) (move : Movable p d) :
      HighStep p ⟨.body, d⟩ ⟨.clean fields .normal, preparedBody p d⟩
  | bodyUnwind (d) (panics : p.bodyPanics = true) (move : Movable p d) :
      HighStep p ⟨.body, d⟩ ⟨.clean fields .unwinding, preparedBody p d⟩
  | skip (d f rest m) (absent : d.owed.get f = false) :
      HighStep p ⟨.clean (f :: rest) m, d⟩ ⟨.clean rest m, d⟩
  | enter (d f rest m) (present : d.owed.get f = true) :
      HighStep p ⟨.clean (f :: rest) m, d⟩
        ⟨.running f rest m (p.drop f), (d.consume f).emit (.entered f)⟩
  | returned (d f rest m) :
      HighStep p ⟨.running f rest m .ret, d⟩
        ⟨.clean rest m, (d.finish f).emit (.returned f)⟩
  | unwound (d f rest) :
      HighStep p ⟨.running f rest .normal .unwind, d⟩
        ⟨.clean rest .unwinding, (d.finish f).emit (.unwound f)⟩
  | doublePanicOwnedAbort (d f rest) :
      HighStep p ⟨.running f rest .unwinding .unwind, d⟩
        ⟨.abort, (d.finish f).emit (.unwound f)⟩
  | readGood (d f rest m) (valid : canRead p d f = true) :
      HighStep p ⟨.running f rest m .read, d⟩
        ⟨.running f rest m .ret, d.emit (.read f)⟩
  | readBad (d f rest m) (invalid : canRead p d f = false) :
      HighStep p ⟨.running f rest m .read, d⟩ ⟨.bad, d.emit (.bad f)⟩
  | spinBody (d f rest m) :
      HighStep p ⟨.running f rest m .spin, d⟩
        ⟨.running f rest m .spin, d.emit (.spinning f)⟩
  | normalExit (d) : HighStep p ⟨.clean [] .normal, d⟩ ⟨.spin, d.emit .normalExit⟩
  | unwindExit (d) : HighStep p ⟨.clean [] .unwinding, d⟩ ⟨.done, d.emit .unwindExit⟩
  | loop (d) : HighStep p ⟨.spin, d⟩ ⟨.spin, d.emit .loop⟩
  | abort (d) : HighStep p ⟨.abort, d⟩ ⟨.aborted, d.emit .abort⟩

inductive PC where
  | construct (f : Field) | body | test (rest : List Field) (mode : Mode)
  | clear (f : Field) (rest : List Field) (mode : Mode)
  | invoke (f : Field) (rest : List Field) (mode : Mode) | spin | abort
  deriving DecidableEq, Repr
inductive Instr where
  | construct (f : Field) (normal unwind : PC) | body (normal unwind : PC)
  | test (f : Field) (yes no : PC) | clear (f : Field) (next : PC)
  | call (f : Field) (normal unwind : PC) | exit (mode : Mode) | spin | abort
  deriving DecidableEq, Repr
def unwindNext (rest : List Field) : Mode → PC
  | .normal => .test rest .unwinding | .unwinding => .abort
def ctorNext : Field → PC | .first => .construct .second | .second => .body

/-- Static suffix labels give the emitted CFG for any finite declaration list.
No HighStep constructor is used by this lookup or the low-level interpreter. -/
def program : PC → Instr
  | .construct f => .construct f (ctorNext f) (.test fields .unwinding)
  | .body => .body (.test fields .normal) (.test fields .unwinding)
  | .test [] m => .exit m
  | .test (f :: rest) m => .test f (.clear f rest m) (.test rest m)
  | .clear f rest m => .clear f (.invoke f rest m)
  | .invoke f rest m => .call f (.test rest m) (unwindNext rest m)
  | .spin => .spin | .abort => .abort
inductive LowControl where
  | at (pc : PC) | running (f : Field) (code : Code) (normal unwind : PC)
  | done | bad | aborted
  deriving DecidableEq, Repr
structure LowState where
  control : LowControl
  data : Data
  deriving DecidableEq, Repr

/-- Independent instruction execution. Flag clear and destructor call are
separate transitions; calls retain literal normal/unwind continuation labels. -/
inductive LowStep (p : Plan) : LowState → LowState → Prop where
  | ctorReturn (d pc f n u) (ins : program pc = .construct f n u) (ok : p.ctor f = true) :
      LowStep p ⟨.at pc, d⟩ ⟨.at n, d.build f⟩
  | ctorUnwind (d pc f n u) (ins : program pc = .construct f n u) (fails : p.ctor f = false) :
      LowStep p ⟨.at pc, d⟩ ⟨.at u, d.emit (.ctorUnwind f)⟩
  | bodyNormal (d pc n u) (ins : program pc = .body n u)
      (normal : p.bodyPanics = false) (move : Movable p d) :
      LowStep p ⟨.at pc, d⟩ ⟨.at n, preparedBody p d⟩
  | bodyUnwind (d pc n u) (ins : program pc = .body n u)
      (panics : p.bodyPanics = true) (move : Movable p d) :
      LowStep p ⟨.at pc, d⟩ ⟨.at u, preparedBody p d⟩
  | testTrue (d pc f y n) (ins : program pc = .test f y n) (present : d.owed.get f = true) :
      LowStep p ⟨.at pc, d⟩ ⟨.at y, d⟩
  | testFalse (d pc f y n) (ins : program pc = .test f y n) (absent : d.owed.get f = false) :
      LowStep p ⟨.at pc, d⟩ ⟨.at n, d⟩
  | clear (d pc f next) (ins : program pc = .clear f next) :
      LowStep p ⟨.at pc, d⟩ ⟨.at next, d.consume f⟩
  | invoke (d pc f n u) (ins : program pc = .call f n u) :
      LowStep p ⟨.at pc, d⟩ ⟨.running f (p.drop f) n u, d.emit (.entered f)⟩
  | returned (d f n u) : LowStep p ⟨.running f .ret n u, d⟩
      ⟨.at n, (d.finish f).emit (.returned f)⟩
  | unwound (d f n u) : LowStep p ⟨.running f .unwind n u, d⟩
      ⟨.at u, (d.finish f).emit (.unwound f)⟩
  | readGood (d f n u) (valid : canRead p d f = true) :
      LowStep p ⟨.running f .read n u, d⟩ ⟨.running f .ret n u, d.emit (.read f)⟩
  | readBad (d f n u) (invalid : canRead p d f = false) :
      LowStep p ⟨.running f .read n u, d⟩ ⟨.bad, d.emit (.bad f)⟩
  | spinBody (d f n u) : LowStep p ⟨.running f .spin n u, d⟩
      ⟨.running f .spin n u, d.emit (.spinning f)⟩
  | normalExit (d pc) (ins : program pc = .exit .normal) :
      LowStep p ⟨.at pc, d⟩ ⟨.at .spin, d.emit .normalExit⟩
  | unwindExit (d pc) (ins : program pc = .exit .unwinding) :
      LowStep p ⟨.at pc, d⟩ ⟨.done, d.emit .unwindExit⟩
  | loop (d pc) (ins : program pc = .spin) :
      LowStep p ⟨.at pc, d⟩ ⟨.at pc, d.emit .loop⟩
  | abort (d pc) (ins : program pc = .abort) :
      LowStep p ⟨.at pc, d⟩ ⟨.aborted, d.emit .abort⟩

def compile (s : HighState) : LowState :=
  ⟨match s.control with
    | .construct f => .at (.construct f) | .body => .at .body
    | .clean rest m => .at (.test rest m)
    | .running f rest m code => .running f code (.test rest m) (unwindNext rest m)
    | .spin => .at .spin | .done => .done | .bad => .bad
    | .abort => .at .abort | .aborted => .aborted, s.data⟩
def highBad (s : HighState) : Prop := s.control = .bad
def lowBad (s : LowState) : Prop := s.control = .bad
def Related (s : HighState) (t : LowState) : Prop := t = compile s
private theorem one {X : Type} {R : X → X → Prop} {a b : X} (edge : R a b) : Reach R a b :=
  Reach.tail (Reach.refl _) edge

theorem simulation (p : Plan) :
    StutteringSimulation (HighStep p) (LowStep p) highBad lowBad Related := by
  constructor
  · intro s s' t related edge
    rcases related with rfl
    refine ⟨compile s', ?_, rfl⟩
    cases edge with
    | ctorReturn d f ok => cases f <;> exact one (LowStep.ctorReturn _ _ _ _ _ rfl ok)
    | ctorUnwind d f fails => exact one (LowStep.ctorUnwind _ _ _ _ _ rfl fails)
    | bodyNormal d normal move => exact one (LowStep.bodyNormal _ _ _ _ rfl normal move)
    | bodyUnwind d panics move => exact one (LowStep.bodyUnwind _ _ _ _ rfl panics move)
    | skip d f rest m absent => exact one (LowStep.testFalse _ _ _ _ _ rfl absent)
    | enter d f rest m present =>
      exact Reach.tail
        (Reach.tail (one (LowStep.testTrue _ _ _ _ _ rfl present))
          (LowStep.clear _ _ _ _ rfl)) (LowStep.invoke _ _ _ _ _ rfl)
    | returned d f rest m => exact one (LowStep.returned _ _ _ _)
    | unwound d f rest => exact one (LowStep.unwound _ _ _ _)
    | doublePanicOwnedAbort d f rest => exact one (LowStep.unwound _ _ _ _)
    | readGood d f rest m valid => exact one (LowStep.readGood _ _ _ _ valid)
    | readBad d f rest m invalid => exact one (LowStep.readBad _ _ _ _ invalid)
    | spinBody d f rest m => exact one (LowStep.spinBody _ _ _ _)
    | normalExit d => exact one (LowStep.normalExit _ _ rfl)
    | unwindExit d => exact one (LowStep.unwindExit _ _ rfl)
    | loop d => exact one (LowStep.loop _ _ rfl)
    | abort d => exact one (LowStep.abort _ _ rfl)
  · intro s t related bad
    rcases related with rfl
    rcases s with ⟨control, d⟩
    change control = .bad at bad
    cases bad
    rfl

/-- Whole-execution target NoUB entails source NoUB for every initial state,
not merely equality of successful cleanup outputs. -/
theorem safety_transfer (p : Plan) (s : HighState)
    (safe : NoUB (LowStep p) lowBad (compile s)) : NoUB (HighStep p) highBad s :=
  PrefixTransfer.sourceSafety (simulation p) rfl safe

theorem finite_prefix_trace (p : Plan) {s s' : HighState} (path : Reach (HighStep p) s s') :
    ∃ t, Reach (LowStep p) (compile s) t ∧ t = compile s' ∧ t.data.trace = s'.data.trace := by
  obtain ⟨t, reached, same⟩ := PrefixTransfer.reachable_coverage (simulation p) rfl path
  exact ⟨t, reached, same, by rw [same]; rfl⟩

theorem clear_before_call_keeps_payload (d : Data) (f : Field) :
    (d.consume f).owed.get f = false ∧ (d.consume f).payload = d.payload := by
  cases f <;> exact ⟨rfl, rfl⟩

def initial : HighState := ⟨.construct .first, {}⟩
def firstBuilt : Data := ({} : Data).build .first
def bothBuilt : Data := firstBuilt.build .second
theorem constructors_return (p : Plan) (a : p.ctor .first = true) (b : p.ctor .second = true) :
    Reach (HighStep p) initial ⟨.body, bothBuilt⟩ :=
  Reach.tail (one (HighStep.ctorReturn {} .first a)) (HighStep.ctorReturn firstBuilt .second b)

def ordinary : Plan := {}
def constructorFailure : Plan := { ctor := fun f => match f with | .first => true | .second => false }
def movedSecond : Plan := { takeSecond := true }
def firstDropUnwinds : Plan := { drop := fun f => match f with | .first => .unwind | .second => .ret }
def unsafeRead : Plan := { drop := fun _ => .read, readable := ⟨false, true⟩ }
def entered (d : Data) (f : Field) : Data := (d.consume f).emit (.entered f)
def returned (d : Data) (f : Field) : Data := (d.finish f).emit (.returned f)

theorem ordinary_cleanup_order :
    ∃ t, Reach (LowStep ordinary) (compile initial) t ∧ t.control = .at .spin ∧
      t.data.trace = [.built .first, .built .second, .entered .first, .returned .first,
        .entered .second, .returned .second, .normalExit] := by
  let a := entered bothBuilt .first
  let b := returned a .first
  let c := entered b .second
  let d := returned c .second
  have h : Reach (HighStep ordinary) initial ⟨.spin, d.emit .normalExit⟩ := by
    exact (constructors_return ordinary rfl rfl).trans
      ((one (HighStep.bodyNormal bothBuilt rfl (by intro h; cases h))).trans
        ((one (HighStep.enter bothBuilt .first [.second] .normal rfl)).trans
          ((one (HighStep.returned a .first [.second] .normal)).trans
            ((one (HighStep.enter b .second [] .normal rfl)).trans
              ((one (HighStep.returned c .second [] .normal)).trans
                (one (HighStep.normalExit d)))))))
  obtain ⟨t, path, same, trace⟩ := finite_prefix_trace ordinary h
  exact ⟨t, path, by rw [same]; rfl, by rw [trace]; rfl⟩

theorem second_constructor_unwind_cleans_only_first :
    ∃ t, Reach (LowStep constructorFailure) (compile initial) t ∧ t.control = .done ∧
      t.data.trace = [.built .first, .ctorUnwind .second, .entered .first,
        .returned .first, .unwindExit] := by
  let a := firstBuilt.emit (.ctorUnwind .second)
  let b := entered a .first
  let c := returned b .first
  have h : Reach (HighStep constructorFailure) initial ⟨.done, c.emit .unwindExit⟩ := by
    exact (one (HighStep.ctorReturn {} .first rfl)).trans
      ((one (HighStep.ctorUnwind firstBuilt .second rfl)).trans
        ((one (HighStep.enter a .first [.second] .unwinding rfl)).trans
          ((one (HighStep.returned b .first [.second] .unwinding)).trans
            ((one (HighStep.skip c .second [] .unwinding rfl)).trans
              (one (HighStep.unwindExit c))))))
  obtain ⟨t, path, same, trace⟩ := finite_prefix_trace constructorFailure h
  exact ⟨t, path, by rw [same]; rfl, by rw [trace]; rfl⟩

theorem partial_move_skips_second :
    ∃ t, Reach (LowStep movedSecond) (compile initial) t ∧
      t.data.trace = [.built .first, .built .second, .moved .second,
        .entered .first, .returned .first, .normalExit] := by
  let a := bothBuilt.moveSecond
  let b := entered a .first
  let c := returned b .first
  have h : Reach (HighStep movedSecond) initial ⟨.spin, c.emit .normalExit⟩ := by
    exact (constructors_return movedSecond rfl rfl).trans
      ((one (HighStep.bodyNormal bothBuilt rfl (by intro _; rfl))).trans
        ((one (HighStep.enter a .first [.second] .normal rfl)).trans
          ((one (HighStep.returned b .first [.second] .normal)).trans
            ((one (HighStep.skip c .second [] .normal rfl)).trans
              (one (HighStep.normalExit c))))))
  obtain ⟨t, path, _, trace⟩ := finite_prefix_trace movedSecond h
  exact ⟨t, path, by rw [trace]; rfl⟩

theorem panicking_drop_is_not_retried :
    ∃ t, Reach (LowStep firstDropUnwinds) (compile initial) t ∧ t.control = .done ∧
      t.data.trace = [.built .first, .built .second, .entered .first, .unwound .first,
        .entered .second, .returned .second, .unwindExit] := by
  let a := entered bothBuilt .first
  let b := (a.finish .first).emit (.unwound .first)
  let c := entered b .second
  let d := returned c .second
  have h : Reach (HighStep firstDropUnwinds) initial ⟨.done, d.emit .unwindExit⟩ := by
    exact (constructors_return firstDropUnwinds rfl rfl).trans
      ((one (HighStep.bodyNormal bothBuilt rfl (by intro h; cases h))).trans
        ((one (HighStep.enter bothBuilt .first [.second] .normal rfl)).trans
          ((one (HighStep.unwound a .first [.second])).trans
            ((one (HighStep.enter b .second [] .unwinding rfl)).trans
              ((one (HighStep.returned c .second [] .unwinding)).trans
                (one (HighStep.unwindExit d)))))))
  obtain ⟨t, path, same, trace⟩ := finite_prefix_trace firstDropUnwinds h
  exact ⟨t, path, by rw [same]; rfl, by rw [trace]; rfl⟩

theorem destructor_bad_prefix_before_later_loop :
    (∃ t, Reach (LowStep unsafeRead) (compile initial) t ∧ lowBad t ∧
      t.data.trace = [.built .first, .built .second, .entered .first, .bad .first]) ∧
    ¬ NoUB (LowStep unsafeRead) lowBad (compile initial) := by
  let a := entered bothBuilt .first
  have h : Reach (HighStep unsafeRead) initial ⟨.bad, a.emit (.bad .first)⟩ := by
    exact (constructors_return unsafeRead rfl rfl).trans
      ((one (HighStep.bodyNormal bothBuilt rfl (by intro h; cases h))).trans
        ((one (HighStep.enter bothBuilt .first [.second] .normal rfl)).trans
          (one (HighStep.readBad a .first [.second] .normal rfl))))
  obtain ⟨t, path, same, trace⟩ := finite_prefix_trace unsafeRead h
  have bad : lowBad t := by rw [same]; rfl
  exact ⟨⟨t, path, bad, by rw [trace]; rfl⟩, bad_prefix_not_noUB path bad⟩

theorem low_destructor_spin_safe (p : Plan) (d : Data) (f : Field) (n u : PC) :
    NoUB (LowStep p) lowBad ⟨.running f .spin n u, d⟩ := by
  apply invariant_noUB (Invariant := fun s => s.control = .running f .spin n u) rfl
  · intro s t invariant edge
    cases edge <;> simp_all
  · intro s invariant bad
    change s.control = .bad at bad
    rw [invariant] at bad
    cases bad

theorem destructor_spin_safe (p : Plan) (d : Data) (f : Field) (rest : List Field) (m : Mode) :
    NoUB (HighStep p) highBad ⟨.running f rest m .spin, d⟩ :=
  safety_transfer p _ (low_destructor_spin_safe p d f _ _)

def spinData (d : Data) (f : Field) : Nat → Data
  | 0 => d | n + 1 => (spinData d f n).emit (.spinning f)
theorem destructor_spin_infinite (p : Plan) (d : Data) (f : Field) (rest : List Field) (m : Mode) :
    ∀ n, HighStep p ⟨.running f rest m .spin, spinData d f n⟩
      ⟨.running f rest m .spin, spinData d f (n + 1)⟩ := by
  intro n
  exact HighStep.spinBody _ _ _ _

#print axioms simulation
#print axioms safety_transfer
#print axioms finite_prefix_trace
#print axioms ordinary_cleanup_order
#print axioms second_constructor_unwind_cleans_only_first
#print axioms partial_move_skips_second
#print axioms panicking_drop_is_not_retried
#print axioms destructor_bad_prefix_before_later_loop
#print axioms low_destructor_spin_safe
#print axioms destructor_spin_safe
#print axioms destructor_spin_infinite

end AnnealResearch.CleanupElaboration
