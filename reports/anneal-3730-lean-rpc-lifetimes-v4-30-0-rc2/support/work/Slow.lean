import Lean
theorem demo : True := by
  run_tac do
    IO.FS.writeFile "gate.entered" "1"
    while !(← (System.FilePath.mk "gate.release").pathExists) do
      IO.sleep 10
  exact ?_
