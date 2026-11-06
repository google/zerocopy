import Lean

theorem demo : True := by
  run_tac do
    IO.FS.writeFile "v1.entered" "1"
    while !(← (System.FilePath.mk "v1.release").pathExists) do
      IO.sleep 10
  trivial
