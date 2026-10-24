-- Generated from pinned archived Cargo records; metadata labels are not live paths.
import AnnealResearch.CargoLeanCostCold2Data
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 3200000
namespace AnnealResearch.CargoLeanCost
open AnnealResearch.Post96LifecycleInterface
open AnnealResearch.Post96NativeConsumer
open AnnealResearch.Post96Consumer
open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration
open AnnealResearch.PR86AuditRepairs
open AnnealResearch.StatefulGenericLibraryH3H7
theorem cold_2_binding : checkArchivedBinding cold_2Expected cold_2 = true := by
  unfold checkArchivedBinding
  have hbinding : (cold_2.binding == cold_2Expected.binding) = true := beq_iff_eq.mpr rfl
  rw [hbinding]
  decide
end AnnealResearch.CargoLeanCost
