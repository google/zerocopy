/-!
# A While language with an observable `emit` effect

Syntax of the toy language used throughout `Toy.Progress`: natural-number
expressions, and commands with assignment, `emit`, sequencing, conditionals and
`while` loops. Every loop carries a Boolean *progress flag*; the flag is consulted
only by the per-loop ("mixed") semantics `Toy.Progress.MixedBeh`, and is ignored by
the divergence-observable and forward-progress semantics.
-/

namespace Toy.Progress

/-- Program variables are named by natural numbers. -/
abbrev Var := Nat

/-- Values are natural numbers; `0` is false and every other value is true. -/
abbrev Val := Nat

/-- A program state assigns a value to every variable. -/
abbrev State := Var → Val

/-- Pointwise update of a state. -/
def State.update (s : State) (x : Var) (v : Val) : State :=
  fun y => if y = x then v else s y

/-- Side-effect-free expressions. `lt` and `eq` return `1` for true and `0` for false;
`sub` is truncated subtraction. -/
inductive Exp where
  | num (n : Nat)
  | var (x : Var)
  | add (a b : Exp)
  | sub (a b : Exp)
  | lt (a b : Exp)
  | eq (a b : Exp)
  deriving DecidableEq, Repr

/-- Expression evaluation. -/
def Exp.eval (s : State) : Exp → Val
  | .num n => n
  | .var x => s x
  | .add a b => a.eval s + b.eval s
  | .sub a b => a.eval s - b.eval s
  | .lt a b => if a.eval s < b.eval s then 1 else 0
  | .eq a b => if a.eval s = b.eval s then 1 else 0

/-- The variables an expression reads. -/
def Exp.vars : Exp → List Var
  | .num _ => []
  | .var x => [x]
  | .add a b | .sub a b | .lt a b | .eq a b => a.vars ++ b.vars

/-- Commands. `loop mp b body` is `while b do body`; `mp` is the loop's progress flag
(meaningful only under `MixedBeh`). `emit e` is the only observable effect. -/
inductive Cmd where
  | skip
  | assign (x : Var) (e : Exp)
  | emit (e : Exp)
  | seq (c₁ c₂ : Cmd)
  | ite (b : Exp) (c₁ c₂ : Cmd)
  | loop (mp : Bool) (b : Exp) (body : Cmd)
  deriving DecidableEq, Repr

/-- The variables a command may assign. A loop's condition is an expression and
writes nothing. -/
def Cmd.writes : Cmd → List Var
  | .skip | .emit _ => []
  | .assign x _ => [x]
  | .seq c₁ c₂ | .ite _ c₁ c₂ => c₁.writes ++ c₂.writes
  | .loop _ _ c => c.writes

/-- Syntactic check that a command contains no `emit` statement. -/
def Cmd.noEmit : Cmd → Bool
  | .skip | .assign _ _ => true
  | .emit _ => false
  | .seq c₁ c₂ | .ite _ c₁ c₂ => c₁.noEmit && c₂.noEmit
  | .loop _ _ c => c.noEmit

/-- `EmitFree c`: the command `c` contains no `emit` statement anywhere (syntactically).
This is the toy's notion of a *side-effect-free* command: assignments to program
variables are not observable effects. -/
def EmitFree (c : Cmd) : Prop := c.noEmit = true

instance (c : Cmd) : Decidable (EmitFree c) :=
  inferInstanceAs (Decidable (c.noEmit = true))

/-- `c.markAll m` sets the progress flag of every loop in `c` to `m`. A function body
compiled under a per-function progress attribute `m` is modelled as `body.markAll m`. -/
def Cmd.markAll (m : Bool) : Cmd → Cmd
  | .seq c₁ c₂ => .seq (c₁.markAll m) (c₂.markAll m)
  | .ite b c₁ c₂ => .ite b (c₁.markAll m) (c₂.markAll m)
  | .loop _ b c => .loop m b (c.markAll m)
  | c => c

/-- `while 1 do skip` with progress flag `mp`: the canonical side-effect-free infinite
loop. -/
def spin (mp : Bool) : Cmd := .loop mp (.num 1) .skip

/-! ### Examples -/

/-- Positive example: a loop that only assigns is emit-free. -/
theorem emitFree_example_pos :
    EmitFree (.loop false (.eq (.var 0) (.num 0)) (.assign 0 (.num 1))) := by decide

/-- Negative example: an `emit` nested inside a conditional inside a loop is detected. -/
theorem emitFree_example_neg :
    ¬ EmitFree (.loop false (.num 1) (.ite (.var 0) (.emit (.num 7)) .skip)) := by decide

/-- Positive example: `writes` collects assignment targets in loop bodies and branches. -/
theorem writes_example :
    (Cmd.seq (.assign 3 (.num 0))
      (.loop false (.var 3) (.ite (.var 1) (.assign 4 (.num 1)) (.emit (.var 5))))).writes
      = [3, 4] := by decide

/-- Negative example: reading a variable is not writing it. -/
theorem writes_example_neg : 5 ∉ (Cmd.emit (.var 5)).writes := by decide

/-- Positive example: `markAll` reaches nested loops. -/
theorem markAll_example :
    (Cmd.seq (spin false) (.loop false (.var 0) (spin false))).markAll true
      = .seq (spin true) (.loop true (.var 0) (spin true)) := by decide

/-- Negative example: `markAll` changes nothing but flags (the condition is kept). -/
theorem markAll_example_neg :
    (spin false).markAll true ≠ .loop true (.num 0) .skip := by decide

end Toy.Progress
