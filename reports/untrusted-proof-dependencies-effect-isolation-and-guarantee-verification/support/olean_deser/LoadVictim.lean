import Lean

open Lean

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot) [System.FilePath.mk "."]
  let modName := match args.head? with
    | some s => s.toName
    | none => `ValidMod
  IO.println s!"[LoadVictim] attempting importModules on {modName} with trustLevel := 0, loadExts := false"
  let env ← importModules #[{ module := modName }] {} (trustLevel := 0) (plugins := #[]) (loadExts := false)
  IO.println s!"[LoadVictim] succeeded! num constants = {env.constants.map₁.size}"
