import Cancel.A
import Lean
theorem gate : True := by
  run_tac do
    IO.FS.writeFile "gate.entered" "1"
    while !(← (System.FilePath.mk "gate.release").pathExists) do
      IO.sleep 10
  exact True.intro
def chosen : Nat := seed + 1
