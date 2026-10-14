module
public import Lean
public import ArithmeticModel
import all ArithmeticModel
public section
open Lean ArithmeticPrototype
namespace NativeChecker
def selectedSource : Source := .wrappingAdd
 (.wrappingMul (.wrappingAdd .input (.literal 3)) (.literal 5)) (.literal 7)
def selectedIR : IR := .addByte (.mulByte (.addByte .parameter (.immediate 3)) (.immediate 5)) (.immediate 7)
def validate (p : IR) : Bool := checkPosthoc selectedSource p
theorem validate_sound (p : IR) (h : validate p = true) :
 ∀ x : Byte, evalIR p x = evalSource selectedSource x := posthoc_sound selectedSource p h
theorem selected_accepted : validate selectedIR = true := by decide
theorem wrong_op_rejected :
 validate (.mulByte (.mulByte (.addByte .parameter (.immediate 3)) (.immediate 5)) (.immediate 7)) = false := by decide
theorem wrong_literal_rejected :
 validate (.addByte (.mulByte (.addByte .parameter (.immediate 4)) (.immediate 5)) (.immediate 7)) = false := by decide
def parseIR : Nat → Json → Except String IR
 | 0, _ => .error "depth-limit"
 | fuel + 1, j => do
  let items ← j.getArr?
  match items.toList with
  | [.str "param"] => pure .parameter
  | [.str "imm", n] =>
    let n ← n.getNat?
    if h : n < 256 then pure (.immediate ⟨n,h⟩) else .error "literal-out-of-byte-range"
  | [.str "add", a, b] => pure (.addByte (← parseIR fuel a) (← parseIR fuel b))
  | [.str "mul", a, b] => pure (.mulByte (← parseIR fuel a) (← parseIR fuel b))
  | _ => .error "unsupported-IR-node"
def answer (line : String) : String :=
 match Json.parse line >>= parseIR 32 with
 | .error msg => (Json.mkObj [("accepted",.bool false),("reason",.str msg)]).compress
 | .ok ir => (Json.mkObj [("accepted",.bool (validate ir)),("reason",.str "checked-selected-statement")]).compress
partial def loop (input output : IO.FS.Stream) : IO Unit := do
 let line ← input.getLine
 if line.isEmpty then pure () else
  output.putStrLn (answer line)
  loop input output
end NativeChecker
def main : IO Unit := do
 NativeChecker.loop (← IO.getStdin) (← IO.getStdout)
