import Miri.Input.CompilerNamedConstants

/-! Exact `helpers.rs::eval_windows` ValueNS constants. The compiler query
identity is `std::sys::pal::windows::<module>::<name>`; the adapter validates
the complete path before reusing the canonical named-constant decoder. -/
namespace Miri.Input.CompilerWindowsConstants
open Lean Miri.Memory Miri.Interpreter

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key

private def exactPath (record : Json) (module name : String) : Except String Unit := do
  let parts ← (← field record "path").getArr?
  unless parts.size == 6 do throw "Windows compiler constant path must have six components"
  let some p0 := parts[0]? | throw "Windows compiler constant path is missing component 0"
  let some p1 := parts[1]? | throw "Windows compiler constant path is missing component 1"
  let some p2 := parts[2]? | throw "Windows compiler constant path is missing component 2"
  let some p3 := parts[3]? | throw "Windows compiler constant path is missing component 3"
  let some p4 := parts[4]? | throw "Windows compiler constant path is missing module"
  let some p5 := parts[5]? | throw "Windows compiler constant path is missing name"
  unless (← p0.getStr?) == "std" && (← p1.getStr?) == "sys" &&
      (← p2.getStr?) == "pal" && (← p3.getStr?) == "windows" &&
      (← p4.getStr?) == module && (← p5.getStr?) == name do
    throw "Windows compiler constant path does not match the demanded source path"
  unless (← (← field record "name").getStr?) == name do
    throw "Windows compiler constant row name does not match its path"

/-- Resolve the exact source path and retain the named constant decoder's
compiler status, target layout, width, and scalar validation. -/
def scalar (prepared : CompilerNamedConstants.Prepared) (module name : String) :
    Except String (Scalar Provenance) := do
  let records ← (← prepared.program.input.raw.getObjVal? "compiler_named_constants").getArr?
  let mut found := #[]
  for record in records do
    let path? := (record.getObjVal? "path").toOption
    if let some path := path? then
      if let .ok parts := path.getArr? then
        if parts.size == 6 then
          let component (index : Nat) := parts[index]?.bind fun value => (value.getStr?).toOption
          if component 0 == some "std" && component 1 == some "sys" &&
              component 2 == some "pal" && component 3 == some "windows" &&
              component 4 == some module && component 5 == some name then
            exactPath record module name
            found := found.push record
  unless found.size == 1 do
    throw s!"missing or duplicate exact Windows compiler constant query std::sys::pal::windows::{module}::{name}"
  CompilerNamedConstants.scalar prepared name

end Miri.Input.CompilerWindowsConstants
