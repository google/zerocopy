import Std
namespace Effects
structure State where
  byte : Nat
  writable : Bool
  deriving DecidableEq, Repr
inductive Op where
  | read
  | write (byte : Nat)
  deriving DecidableEq, Repr

-- A read models an interacting alias effect: a sibling writer loses authority.
def direct : Op → State → Option State
  | .read, s => some {s with writable := false}
  | .write n, s => if s.writable then some {s with byte := n} else none

def permissionEvent : Op → State → Option State
  | .read, s => some {s with writable := false}
  | .write _, s => if s.writable then some s else none

def byteEvent : Op → State → State
  | .read, s => s
  | .write n, s => {s with byte := n}

def handled (op : Op) (s : State) : Option State :=
  (permissionEvent op s).map (byteEvent op)

theorem event_agreement (op : Op) (s : State) :
    handled op s = direct op s := by
  cases op with
  | read => rfl
  | write n =>
    simp only [handled, permissionEvent, direct]
    split <;> simp_all [byteEvent]

def run (step : Op → State → Option State) : List Op → State → Option State
  | [], s => some s
  | op :: rest, s => (step op s).bind (run step rest)

theorem trace_agreement (ops : List Op) (s : State) :
    run handled ops s = run direct ops s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
    simp only [run, event_agreement]
    cases direct op s <;> simp_all

def readonlyApprox : Op → State → Option State
  | .read, s => some s
  | .write n, s => if s.writable then some {s with byte := n} else none

theorem read_effect_matters :
    run direct [.read, .write 1] ⟨0,true⟩ = none ∧
    run readonlyApprox [.read, .write 1] ⟨0,true⟩ = some ⟨1,true⟩ := by decide

#print axioms event_agreement
#print axioms trace_agreement
#print axioms read_effect_matters
end Effects

