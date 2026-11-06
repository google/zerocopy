-- anneal-trust-tier: vetted
prelude
import Init.Core
import Init.Notation

namespace Trusted

structure Crate where
  entryReturnVal : Nat
  expectedVal    : Nat

def SafeExec (c : Crate) : Bool :=
  Nat.beq c.entryReturnVal c.expectedVal

def CrateTheorem (c : Crate) : Prop :=
  SafeExec c = true

end Trusted
