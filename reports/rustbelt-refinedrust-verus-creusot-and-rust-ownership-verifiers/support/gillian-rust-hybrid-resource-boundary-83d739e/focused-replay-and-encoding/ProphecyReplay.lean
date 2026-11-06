import Std
namespace Replay
structure Resource where
  future : Nat
  current : Nat
  observer : Bool
  controller : Bool
  deriving DecidableEq
inductive Action where
  | assign (value : Nat)
  | consumeObserver
  | restoreObserver (value : Nat)
  deriving DecidableEq

def apply (a : Action) (s : Resource) : Option Resource :=
  match a with
  | .assign v => if s.observer && s.controller then some {s with current := v} else none
  | .consumeObserver => if s.observer then some {s with observer := false} else none
  | .restoreObserver v =>
    if !s.observer && (!s.controller || decide (s.current = v)) then
      some {s with observer := true, current := v} else none

inductive Primitive : Action → Resource → Resource → Prop where
  | assign (s : Resource) (v : Nat) (ho : s.observer = true) (hc : s.controller = true) :
      Primitive (.assign v) s {s with current := v}
  | consume (s : Resource) (ho : s.observer = true) :
      Primitive .consumeObserver s {s with observer := false}
  | restore (s : Resource) (v : Nat) (ho : s.observer = false)
      (he : s.controller = false ∨ s.current = v) :
      Primitive (.restoreObserver v) s {s with observer := true, current := v}

theorem apply_sound (a : Action) (s t : Resource) (h : apply a s = some t) : Primitive a s t := by
  cases a with
  | assign v =>
    simp only [apply] at h
    split at h
    · rename_i g
      have hs : s.observer = true ∧ s.controller = true := by simpa using g
      have ho := hs.1
      have hc := hs.2
      cases Option.some.inj h
      exact Primitive.assign s v ho hc
    · contradiction
  | consumeObserver =>
    simp only [apply] at h
    split at h
    · rename_i g
      cases Option.some.inj h
      exact Primitive.consume s g
    · contradiction
  | restoreObserver v =>
    simp only [apply] at h
    split at h
    · rename_i g
      have hs : s.observer = false ∧ (s.controller = false ∨ s.current = v) := by
        simpa using g
      cases Option.some.inj h
      exact Primitive.restore s v hs.1 hs.2
    · contradiction

def run : List Action → Resource → Option Resource
  | [], s => some s
  | a::tail, s => (apply a s).bind (run tail)
inductive Trace : Resource → Resource → Prop where
  | nil (s) : Trace s s
  | cons (a s u t) : Primitive a s u → Trace u t → Trace s t

theorem run_sound (plan : List Action) (s t : Resource) (h : run plan s = some t) : Trace s t := by
  induction plan generalizing s with
  | nil => cases Option.some.inj h; exact Trace.nil _
  | cons a tail ih =>
    simp only [run] at h
    cases he : apply a s with
    | none => simp [he] at h
    | some u =>
      simp only [he, Option.bind_some] at h
      exact Trace.cons a s u t (apply_sound a s u he) (ih u h)

theorem primitive_frame (a s t) (h : Primitive a s t) : t.future = s.future := by cases h <;> rfl
theorem trace_frame (s t) (h : Trace s t) : t.future = s.future := by
  induction h with
  | nil => rfl
  | cons a s u t hp ht ih => exact ih.trans (primitive_frame a s u hp)

def check (plan : List Action) (input output : Resource) : Bool := decide (run plan input = some output)
theorem check_sound (plan input output) (h : check plan input output = true) :
    Trace input output ∧ output.future = input.future := by
  have ht := run_sound plan input output (of_decide_eq_true h)
  exact ⟨ht, trace_frame input output ht⟩

def initial : Resource := ⟨17, 7, true, true⟩
def target : Resource := ⟨17, 12, true, true⟩
def good := [Action.consumeObserver, .restoreObserver 7, .assign 12]
example : check good initial target = true := by decide
example : check [.consumeObserver, .assign 12] initial target = false := by decide
example : check [.restoreObserver 7] initial initial = false := by decide
example : check [.consumeObserver, .restoreObserver 9, .assign 12] initial target = false := by decide
example : check [.assign 12] {initial with observer := false} target = false := by decide
example : check good initial {target with future := 18} = false := by decide
#print axioms apply_sound
#print axioms run_sound
#print axioms check_sound
#print axioms trace_frame
end Replay
