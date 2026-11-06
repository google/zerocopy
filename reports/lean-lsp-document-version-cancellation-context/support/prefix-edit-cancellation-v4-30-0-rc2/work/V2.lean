import Lean
open Lean Elab Command
run_cmd do
  let p := "markers.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "A\n")
def generated : Nat := 2
run_cmd do
  liftIO <| IO.FS.writeFile "gate.entered" "entered"
  while !(← (System.FilePath.mk "gate.release").pathExists) do
    liftIO <| IO.sleep 10
run_cmd do
  let p := "markers.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "B2\n")
theorem target : generated = 1 := by decide
run_cmd do
  let p := "markers.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "C2\n")
