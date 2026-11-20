-- Spot check of one probe finding: the default rendering of `UInt64.neg_one_eq`
-- re-elaborates (with no expected type) as a statement about `Int`.
#check @UInt64.neg_one_eq
set_option pp.numericTypes true in
#check @UInt64.neg_one_eq
-- What the printed text means when elaborated in a fresh context:
set_option pp.numericTypes true in
#check (-1 = 18446744073709551615)
-- ... and that reading is false:
example : ¬ ((-1 : Int) = 18446744073709551615) := by decide
-- The same text-identical rendering for `Int.one_ne_zero`:
#check @Int.one_ne_zero
set_option pp.numericTypes true in
#check (1 ≠ 0)
