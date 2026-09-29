import Lean
theorem slow : True := by
  run_tac do
    IO.FS.writeFile "slow.entered" "entered"
    while !(← (System.FilePath.mk "slow.release").pathExists) do
      IO.sleep 10
  exact ?_
