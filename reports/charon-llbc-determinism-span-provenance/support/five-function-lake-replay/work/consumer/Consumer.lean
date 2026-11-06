import Probe
theorem add_one_self (x : Aeneas.Std.U32) : i148_corpus.add_one x = i148_corpus.add_one x := by rfl
theorem choose_self (x : Aeneas.Std.U32) : i148_corpus.choose true x x = i148_corpus.choose true x x := by rfl
theorem pair_sum_self (x : Aeneas.Std.U32) : i148_corpus.pair_sum {left := x, right := x} = i148_corpus.pair_sum {left := x, right := x} := by rfl
theorem make_pair_self (x : Aeneas.Std.U32) : i148_corpus.make_pair x x = i148_corpus.make_pair x x := by rfl
theorem combine_self (x : Aeneas.Std.U32) : i148_corpus.combine true x x = i148_corpus.combine true x x := by rfl
#print axioms combine_self
