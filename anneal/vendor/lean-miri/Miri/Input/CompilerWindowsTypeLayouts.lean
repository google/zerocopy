import Miri.Input.RuntimeMetadata

/-! Exact source `helpers.rs::windows_ty_layout` queries. Windows shim
aggregates resolve only through rustc's `std::sys::pal::windows::c` TypeNS
catalog; neither target spelling nor layout coincidence is used as a fallback.
-/
namespace Miri.Input.CompilerWindowsTypeLayouts
open Lean Miri.ABI

private def typeRef (entry : Json) : Except String TypeId := do
  unless (← (← entry.getObjVal? "status").getStr?) == "supported" do
    throw s!"compiler Windows type/layout query unavailable: {((entry.getObjVal? "reason").bind Json.getStr?).toOption}"
  let value ← entry.getObjVal? "value"
  (← value.getObjVal? "type_id").getNat?

/-- Resolve one exact source Windows C type and return its compiler-derived
layout. This intentionally stays demand-local so unused Windows structures do
not become a startup prerequisite. -/
def layout (runtime : RuntimeMetadata) (name : String) : Except String (TyAndLayout TypeId) := do
  let catalog ← runtime.source.raw.getObjVal? "compiler_windows_type_layouts"
  unless (← (← catalog.getObjVal? "crate_path").getArr?) ==
      #[toJson ("std" : String),toJson ("sys" : String),toJson ("pal" : String),
        toJson ("windows" : String),toJson ("c" : String)] do
    throw "compiler Windows type query has wrong canonical crate path"
  unless (← (← catalog.getObjVal? "namespace").getStr?) == "TypeNS" do
    throw "compiler Windows type query has wrong namespace"
  unless (← (← catalog.getObjVal? "typing_env").getStr?) == "fully_monomorphized" do
    throw "compiler Windows type query has wrong typing environment"
  let entries ← catalog.getObjVal? "entries"
  let entry ← entries.getObjVal? name
  let id ← typeRef entry
  runtime.lookup id |>.mapError toString

end Miri.Input.CompilerWindowsTypeLayouts
