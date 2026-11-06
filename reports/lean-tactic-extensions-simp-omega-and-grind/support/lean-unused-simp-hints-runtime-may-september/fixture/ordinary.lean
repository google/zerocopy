set_option linter.unusedVariables false

def some_def := 1

example : True := by simp [some_def]
example : 0 < some_def := by simp [some_def]
example : 0 < some_def := by simp [some_def, some_def]

-- Two separate occurrences have separate source ranges.
example : True := by simp [some_def]
