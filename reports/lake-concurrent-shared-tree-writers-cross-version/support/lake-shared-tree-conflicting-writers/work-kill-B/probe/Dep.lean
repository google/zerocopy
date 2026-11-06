import Lean
run_cmd do
  let marker ← IO.getEnv "WRITER_MARKER"
  let release ← IO.getEnv "WRITER_RELEASE"
  if let some marker := marker then
    IO.FS.writeFile marker "entered"
    if let some release := release then
      while !(← (System.FilePath.mk release).pathExists) do
        IO.sleep 10
def depValue : Nat := 9
