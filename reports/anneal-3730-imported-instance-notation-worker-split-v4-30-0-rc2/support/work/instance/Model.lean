class Carrier where
  number : Nat
instance : Carrier := ⟨9⟩
def selected : Nat := Carrier.number
