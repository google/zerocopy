def some_def := 1
def some_rdef : Nat → Nat
  | 0 => 42
  | n + 1 => some_rdef n

example : 0 < some_def := by simp -failIfUnchanged [some_rdef]
