import Lean

open Lean

def kindStr : ConstantInfo → String
  | .axiomInfo _  => "axiomInfo"
  | .defnInfo _   => "defnInfo"
  | .thmInfo _    => "thmInfo"
  | .opaqueInfo _ => "opaqueInfo"
  | _             => "other"

def main : IO Unit := do
  let parts ← readModuleDataParts #[
    System.FilePath.mk "Dep.olean",
    System.FilePath.mk "Dep.olean.server",
    System.FilePath.mk "Dep.olean.private"
  ]
  let names := #["Dep.olean (.exported)", "Dep.olean.server (.server)", "Dep.olean.private (.private)"]
  for h : i in [:parts.size] do
    let data := parts[i].1
    IO.println s!"=== Part {i}: {names[i]!} (constants={data.constants.size}, entries={data.entries.size}) ==="
    for c in data.constants do
      if #[`depPublicVal, `depUnexposedVal, `depPublicThm, `depSimpLemma].contains c.name ||
         c.name.toString.endsWith "depPrivateHelper" then
        IO.println s!"  {c.name} : {kindStr c}"
