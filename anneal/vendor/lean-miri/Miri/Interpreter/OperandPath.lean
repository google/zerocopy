/-! Structural operand coordinates within one source MIR instruction envelope.
These identify source positions, never operand values, source spans, or an
execution counter. The body and location are read from the current frame at
actual constant evaluation. -/
namespace Miri.Interpreter
inductive OperandPathElement where
  | field (name : String)
  | index (value : Nat)
  deriving Repr, DecidableEq
abbrev OperandPath := Array OperandPathElement
namespace OperandPath
def instruction (field : String) : OperandPath := #[.field "kind", .field field]
def rvalue (field : String) : OperandPath := #[.field "kind", .field "rvalue", .field field]
def aggregate (index : Nat) : OperandPath := (rvalue "operands").push (.index index)
def argument (index : Nat) : OperandPath :=
  #[.field "kind", .field "args", .index index, .field "operand"]
def assertion (field : String) : OperandPath :=
  #[.field "kind", .field "message", .field field]
end OperandPath
end Miri.Interpreter
