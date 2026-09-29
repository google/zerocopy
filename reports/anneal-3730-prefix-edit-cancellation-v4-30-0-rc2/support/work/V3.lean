import Lean
open Lean Elab Command
run_cmd do
  let p := "markers.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "A\n")
def generated : Nat := 3
run_cmd do
  let p := "markers.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "B3\n")
theorem target : generated = 3 := by decide
run_cmd do
  let p := "markers.txt"
  let old ← liftIO <| IO.FS.readFile p <|> pure ""
  liftIO <| IO.FS.writeFile p (old ++ "C3\n")
