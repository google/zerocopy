import Miri.Interpreter.UnixFd
import Miri.Interpreter.ExecutionChoices

/-! Source `unix/fd.rs::read_from_fd` and `write_to_fd` each draw a fresh
`rng.random()` only after the global short-I/O flag, descriptor opt-in, and
minimum-length guards. `UnixFd.transfer` owns those guards and calls this hook
at that exact point. This adapter consumes one Boolean from the persistent
choice tape per reached source draw; it does not select random payload bytes. -/
namespace Miri.Interpreter.UnixFdChoices
open Miri.Interpreter.ExecutionChoices

set_option autoImplicit false in
def randomShort {S : Type} (choices : ExecutionChoices.Access S) :
    EStateM StepError S Bool :=
  ExecutionChoices.boolean choices .shortFdOperation

set_option autoImplicit false in
def bind {S H D O E Metadata : Type} (choices : ExecutionChoices.Access S)
    (base : UnixFd.Hooks S H D O E Metadata) :
    UnixFd.Hooks S H D O E Metadata :=
  { base with randomShort := randomShort choices }

end Miri.Interpreter.UnixFdChoices
