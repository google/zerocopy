import Miri.Concurrency.GlobalState

/-! Race tracking available to the interpreter. Vector-clock storage remains in the canonical machine state. -/
namespace Miri.Interpreter.RaceMode
inductive Selection (B : Type) where
  | none | vclocks
inductive Handler (B : Type) where
  | none | vclocks (global : Miri.Concurrency.GlobalState)
end Miri.Interpreter.RaceMode
