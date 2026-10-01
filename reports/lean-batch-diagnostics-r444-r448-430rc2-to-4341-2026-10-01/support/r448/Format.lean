-- Adapted from the exact pinned ppOneline and ppUnicode test expressions.
#check [1,2,3,4,5,6,7,8,9,10]
#check fun x1 x2 x3 => (x1 + x2 + x3 : Nat)
#check fun x => x
#check True ∧ False
#check True → False
#check fun x : Nat => let y := x + 1; let z := y + 2; z + x

-- A positioned error exercises the text/JSON location envelope.
#check missingForDiagnosticPosition
