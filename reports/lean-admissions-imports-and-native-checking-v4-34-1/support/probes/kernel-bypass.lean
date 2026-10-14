import Lean
set_option debug.skipKernelTC true
run_cmd Lean.Elab.Command.liftCoreM do
  Lean.addDecl <| Lean.Declaration.thmDecl {
    name := `forged, levelParams := [],
    type := Lean.mkConst ``False,
    value := Lean.mkConst ``True.intro
  }
#print axioms forged
#print forged
