/-
Probe: what does a Sail-emitted unmeasured `while` loop (as in generated
`Functions.loop`, LeanRV64D/Step.lean:497) put in the kernel cone?
Run: <lean-4.34.1>/bin/lean WhileLoopCone.lean   (expected output: WhileLoopCone.out)
-/
import Lean
open Lean Meta

def spin : StateM Nat Unit := do
  let mut i := 0
  while i < 10 do
    i := i + 1
  set i

#print axioms spin

/-- Walk the constant cone of `root` and report every `opaque` / partial / unsafe constant. -/
partial def walk (env : Environment) (todo : List Name) (seen : NameSet) (acc : Array String) : Array String :=
  match todo with
  | [] => acc
  | n :: rest =>
    if seen.contains n then walk env rest seen acc else
    let seen := seen.insert n
    match env.find? n with
    | none => walk env rest seen acc
    | some ci =>
      let acc := match ci with
        | .opaqueInfo v => acc.push s!"opaque {n} (unsafe={v.isUnsafe}, isPartial={ci.isPartial})"
        | .defnInfo v => if v.safety != .safe then acc.push s!"def {n} safety={repr v.safety}" else acc
        | _ => acc
      let cs := ci.type.getUsedConstants ++ (ci.value?.map (·.getUsedConstants)).getD #[]
      walk env (cs.toList ++ rest) seen acc

#eval show MetaM Unit from do
  let env ← getEnv
  for s in walk env [``spin] {} #[] do IO.println s
