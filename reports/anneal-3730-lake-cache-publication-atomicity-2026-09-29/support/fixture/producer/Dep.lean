import Lean
run_cmd do
  let opt ← IO.getEnv "PROBE_MARKER"
  if let some marker := opt then
    IO.FS.writeFile marker "entered"
    IO.sleep 1500
def depValue : Nat := 7
