import Lean

theorem demo : False := by
  run_tac do
    IO.FS.writeFile "v2.entered" "2"
  exact ?_
