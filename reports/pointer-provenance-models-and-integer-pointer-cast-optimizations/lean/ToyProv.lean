import ToyProv.Basic
import ToyProv.Transform
import ToyProv.Lemmas
import ToyProv.Exec
import ToyProv.FlatInv
import ToyProv.DeadCast
import ToyProv.Disjoint
import ToyProv.Erasure
import ToyProv.MonoSim
import ToyProv.Examples
import ToyProv.OnePast
import ToyProv.IntEq
import ToyProv.RoundTrip
import ToyProv.Forwarding
import ToyProv.Bytes
import ToyProv.Ordering
import ToyProv.Monotone
import ToyProv.EqProvDecode
import ToyProv.LedgerWitnesses

/-!
# Pointer provenance models and integer-pointer cast optimizations (toy)

Library root. See `ToyProv.Basic` for the semantics, `ToyProv.Transform` for transformations,
and the result modules `OnePast`, `IntEq`, `RoundTrip`, `Forwarding`, `Bytes`, `Ordering`.
`LedgerWitnesses` holds supporting tightness witnesses for the R4a, R4b and R5b ledgers.
-/
