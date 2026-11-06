import Lean

open Lean

def main : IO Unit := do
  initSearchPath (← findSysroot) [System.FilePath.mk "."]
  IO.println "=== Case A: importModules (loadExts := false) without enableInitializersExecution ==="
  let envA ← importModules #[{ module := `M }] {} (trustLevel := 0) (loadExts := false)
  IO.println s!"Case A succeeded: contains M.pureHook = {envA.contains `pureHook}"

  IO.println "=== Case B: importModules (loadExts := true) without enableInitializersExecution ==="
  try
    let _ ← importModules #[{ module := `M }] {} (trustLevel := 0) (loadExts := true)
    IO.println "Case B unexpectedly succeeded"
  catch e =>
    IO.println s!"Case B threw expected error: {e}"

  IO.println "=== Case C: enableInitializersExecution + importModules (loadExts := true) ==="
  unsafe enableInitializersExecution
  let envC ← importModules #[{ module := `M }] {} (trustLevel := 0) (loadExts := true)
  IO.println s!"Case C succeeded: contains M.pureHook = {envC.contains `pureHook}"
