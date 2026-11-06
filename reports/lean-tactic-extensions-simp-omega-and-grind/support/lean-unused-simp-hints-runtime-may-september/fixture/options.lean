set_option linter.unusedVariables false

def some_def := 1

set_option linter.all false in
example : True := by simp [some_def]

set_option linter.all false in
set_option linter.unusedSimpArgs true in
example : True := by simp [some_def]

set_option linter.unusedSimpArgs false in
example : True := by simp [some_def]

set_option tactic.simp.trace true in
example : True := by simp [some_def]
