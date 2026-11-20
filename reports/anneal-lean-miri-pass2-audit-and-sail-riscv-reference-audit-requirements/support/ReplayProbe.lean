/-
Probe: Anneal-style standalone kernel replay + purity census of a vendored
library (here: rems-project/lean-sail), mimicking the Pass 2 mechanism in
joshlf/anneal@c131b320 trusted/audit/TrustedBoundary.lean
(`importCorrEnv`, `verifyAndCollectCorrLocals`, `replayCorrAndVendor`).

Run (after `lake build` of the vendored library), from the library root:
  LEAN_PATH=.lake/build/lib/lean lean --run <this file> <Prefix> <RootModule>...
-/
import Lean.Replay
import Lean.Util.CollectAxioms
import Lean.CoreM
open Lean

def forbidden : List Name :=
  [`Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.trustCompiler, `Lean.reduceBool, `Lean.reduceNat]

def refs (ci : ConstantInfo) : List Name :=
  let f (e : Expr) : List Name := e.getUsedConstants.toList
  f ci.type ++ ((ci.value? (allowOpaque := true)).map f |>.getD [])

def main (args : List String) : IO UInt32 := do
  let pfx :: roots := args | IO.eprintln "usage: <Prefix> <Root>..."; return 2
  let pfxN := pfx.toName
  initSearchPath (← findSysroot)
  let env ← importModules (roots.toArray.map fun r => { module := r.toName }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let mut vendor : Std.HashMap Name ConstantInfo := {}
  let mut baseMods : Array Name := #[]
  let mut nPartial := 0; let mut nUnsafe := 0; let mut nOpaque := 0
  let mut nAxiom := 0; let mut nSorry := 0; let mut nForbidden := 0
  let mut nVendorMods := 0
  let mut partials : Array Name := #[]
  let mut opaques : Array Name := #[]
  for m in env.header.modules, data in env.header.moduleData do
    if pfxN.isPrefixOf m.module then
      nVendorMods := nVendorMods + 1
      for ci in data.constants do
        if ci.isPartial then nPartial := nPartial + 1; partials := partials.push ci.name
        if ci.isUnsafe then nUnsafe := nUnsafe + 1
        if ci matches .opaqueInfo _ then nOpaque := nOpaque + 1; opaques := opaques.push ci.name
        if ci.isAxiom then nAxiom := nAxiom + 1
        if ci.type.hasSorry || ((ci.value? true).any Expr.hasSorry) then nSorry := nSorry + 1
        if (refs ci).any forbidden.contains then nForbidden := nForbidden + 1
        if !(vendor.contains ci.name) then vendor := vendor.insert ci.name ci
    else
      baseMods := baseMods.push m.module
  IO.println s!"vendor modules={nVendorMods} constants={vendor.size} partial={nPartial} unsafe={nUnsafe} opaque={nOpaque} axiom={nAxiom} sorryRefs={nSorry} compilerReflRefs={nForbidden}"
  IO.println s!"partial: {partials.toList}"
  IO.println s!"opaque: {opaques.toList.take 10}"
  -- axiom census over every non-partial, non-unsafe vendor constant
  let names := vendor.fold (init := #[]) fun acc n ci =>
    if ci.isPartial || ci.isUnsafe then acc else acc.push n
  let run : CoreM NameSet := do
    let mut axs : NameSet := {}
    for n in names do
      for a in (← collectAxioms n) do axs := axs.insert a
    return axs
  let ctx : Core.Context := { fileName := "<replay-probe>", fileMap := default }
  let (axs, _) ← run.toIO ctx { env }
  IO.println s!"axioms reachable from non-partial/unsafe vendor constants: {axs.toList}"
  -- standalone replay onto a clean base (non-vendor modules only)
  let baseEnv ← importModules (baseMods.map fun r => { module := r }) {}
    (trustLevel := 0) (plugins := #[]) (loadExts := false) (level := .private)
  let replayMap := vendor.fold (init := ({} : Std.HashMap Name ConstantInfo))
    fun acc n ci => if ci.isPartial || ci.isUnsafe then acc else acc.insert n ci
  let t0 ← IO.monoMsNow
  let replayed ← baseEnv.toKernelEnv.replay replayMap
  let t1 ← IO.monoMsNow
  let cnt := replayMap.fold (init := 0) fun acc n _ => if (replayed.find? n).isSome then acc + 1 else acc
  IO.println s!"replayed {cnt}/{replayMap.size} vendor constants onto {baseMods.size}-module base in {t1 - t0} ms"
  return 0
