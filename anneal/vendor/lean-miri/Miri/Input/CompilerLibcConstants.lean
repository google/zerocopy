import Miri.Input.CompilerNamedConstants

/-! Exact libc `eval_path_scalar` constants. The original compiler row carries
the full `libc::<name>` ValueNS path; this adapter requires that identity at
the demand site before decoding the compiler value. -/
namespace Miri.Input.CompilerLibcConstants
open Lean Miri.Memory Miri.Interpreter

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key

private def exactPath (record : Json) (name : String) : Except String Unit := do
  let parts ← (← field record "path").getArr?
  unless parts.size == 2 do throw "libc compiler constant path must have two components"
  let some root := parts[0]? | throw "libc compiler constant path is missing its root"
  let some item := parts[1]? | throw "libc compiler constant path is missing its name"
  unless (← root.getStr?) == "libc" && (← item.getStr?) == name do
    throw "libc compiler constant path does not match the demanded source path"
  unless (← (← field record "name").getStr?) == name do
    throw "libc compiler constant row name does not match its path"

/-- Resolve `eval_libc(name)` by the exact two-component compiler path, then
retain all canonical constant, target layout, and scalar-width checks. -/
private def exactRecord (prepared : CompilerNamedConstants.Prepared) (name : String) :
    Except String Json := do
  let records ← (← prepared.program.input.raw.getObjVal? "compiler_named_constants").getArr?
  let mut found := #[]
  for record in records do
    let path? := (record.getObjVal? "path").toOption
    if let some path := path? then
      if let .ok parts := path.getArr? then
        if parts.size == 2 then
          let root := (parts[0]?.bind fun value => (value.getStr?).toOption)
          let item := (parts[1]?.bind fun value => (value.getStr?).toOption)
          if root == some "libc" && item == some name then
            exactPath record name
            found := found.push record
  unless found.size == 1 do throw s!"missing or duplicate exact libc compiler constant query libc::{name}"
  let some record := found[0]? | throw s!"missing exact libc compiler constant query libc::{name}"
  pure record

def scalar (prepared : CompilerNamedConstants.Prepared) (name : String) :
    Except String (Scalar P) := do
  let _ ← exactRecord prepared name
  CompilerNamedConstants.scalar prepared name

/-- Integer helpers preserve the canonical named-constant conversion after
checking the exact source path, for source wrappers using `eval_libc_i32`. -/
def i32 (prepared : CompilerNamedConstants.Prepared) (name : String) :
    Except String Int32 := do
  let _ ← exactRecord prepared name
  CompilerNamedConstants.i32 prepared name

end Miri.Input.CompilerLibcConstants
