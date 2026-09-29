import Lean
run_cmd do
  IO.FS.writeFile "batch.entered" "entered"
  IO.sleep 500
theorem batch_ok : True := by trivial
