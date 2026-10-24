import AnnealResearch.PR86AuditRepairs

set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace AnnealResearch.CharonNativeAndControlsR3R4

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration
open AnnealResearch.StatefulGenericLibraryH3H7
open AnnealResearch.StatefulGenericLibraryH3H7Controls
open AnnealResearch.PR86AuditRepairs

/-!
# `R3` & `R4` (`U2`, `U6`, `#89` §§10–11): Native Single-Artifact Strongest-Flags Charon `0.1.210` Closure & Generated `.amir` v3 Control Equality

1. **`R3` (`U2`, `#89` §10) — Native Single-Artifact Strongest-Flags Charon `0.1.210` Closures**:
   - Verifies `charonNativeClientInspectorClosureAmirBytes` (`1,019` B) and
     `charonNativeClientContractClosureAmirBytes` (`418` B) translated directly from each client's
     own `.ullbc` artifact (`client_direct_mir_inspector_strongest.ullbc` and
     `client_contract_user_strongest.ullbc`) without concatenating `stateful_generic_lib_strongest.ullbc`.
2. **`R4` (`U6`, `#89` §11) — Generated `.amir` v3 Control Byte Equality & Operational Proofs**:
   - Connects all 7 generated Charon `.amir` v3 control files (`charonCtrl1..charonCtrl5`) by
     `decodePackageBodies` equality directly to the Lean body lists and proves their admission
     and operational refutation/preservation properties.
-/

def charonNativeClientInspectorClosureAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 75, 10, 10, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64, 2, 1, 1, 3, 9, 2, 7, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 4, 16, 0, 0, 131, 0, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 2, 1, 68, 0, 129, 1, 1, 0, 65, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 4, 3, 71, 0, 129, 16, 1, 0, 65, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 6, 5, 70, 0, 72, 0, 1, 0, 65, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 16, 0, 0, 131, 0, 64, 3, 2, 1, 3, 6, 1, 3, 1, 22, 1, 6, 3, 6, 0, 8, 32, 5, 16, 0, 0, 131, 0, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 2, 1, 67, 0, 68, 0, 1, 0, 65, 0, 4, 33, 4, 33, 3, 33, 2, 16, 0, 0, 131, 0, 64, 4, 3, 1, 3, 6, 2, 7, 3, 2, 3, 2, 19, 3, 0, 2, 32, 3, 17, 3, 0, 1, 0, 69, 67, 0, 0, 2, 1, 0, 1, 32, 4, 74, 26, 4, 0, 4, 3, 131, 2, 0, 3, 33, 3, 32, 5, 17, 5, 0, 2, 0, 75, 20, 0, 0, 6, 5, 69, 0, 129, 100, 1, 0, 65, 0, 0, 74, 27, 0, 0, 255, 3, 131, 2, 1, 0, 65, 0, 1, 33, 5, 64, 5, 63, 1, 3, 12, 3, 12, 4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19, 0, 2, 32, 9, 32, 10, 73, 37, 10, 0, 8, 7, 1, 0, 65, 0, 3, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 75, 1, 5, 0, 4, 3, 70, 0, 129, 4, 1, 0, 65, 0, 6, 33, 6, 33, 5, 32, 7, 17, 7, 0, 3, 0, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 6, 5, 71, 0, 72, 0, 1, 0, 65, 0, 3, 33, 8, 33, 7, 33, 4, 64, 0, 0, 67, 0, 1, 21, 9, 0, 5, 74, 0, 130, 0, 69, 73, 0, 0, 10, 9, 0, 4, 33, 10, 33, 9, 48, 2, 4, 32, 4, 73, 38, 4, 0, 2, 1, 0, 2, 33, 10, 32, 11, 74, 26, 11, 0, 11, 7, 131, 2, 0, 0, 74, 27, 0, 0, 255, 7, 131, 2, 6, 65, 1, 3, 20, 3, 16, 3, 6, 6, 2, 8, 6, 8, 6, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 19, 32, 17, 32, 18, 32, 19, 17, 18, 0, 128, 0, 17, 19, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 18, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 19, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 17, 8, 0, 3, 0, 69, 72, 0, 0, 4, 1, 0, 4, 32, 9, 32, 10, 16, 17, 0, 4, 2, 19, 10, 0, 1, 17, 4, 75, 1, 9, 0, 3, 2, 74, 0, 129, 10, 0, 0, 69, 19, 0, 0, 6, 5, 0, 6, 33, 10, 33, 9, 32, 11, 32, 12, 17, 18, 0, 128, 0, 17, 12, 0, 68, 0, 74, 24, 11, 0, 7, 2, 76, 0, 0, 4, 33, 8, 32, 13, 32, 14, 17, 14, 0, 3, 0, 75, 3, 13, 0, 8, 2, 78, 0, 129, 5, 0, 0, 71, 6, 0, 7, 6, 9, 0, 0, 69, 18, 0, 0, 11, 10, 0, 2, 33, 12, 33, 11, 68, 4, 0, 5, 33, 14, 32, 15, 32, 16, 17, 19, 0, 128, 0, 17, 16, 0, 70, 0, 74, 24, 15, 0, 12, 2, 80, 0, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 11, 13, 1, 0, 65, 0, 6, 33, 16, 33, 15, 17, 0, 0, 13, 0, 33, 13, 17, 19, 0, 128, 0, 33, 6, 69, 18, 0, 0, 15, 14, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 15, 11, 0, 2, 17, 18, 0, 128, 0, 33, 4, 64, 7, 7, 2, 3, 4, 1, 3, 1, 22, 22, 1, 0, 4, 32, 2, 32, 3, 16, 0, 0, 131, 0, 19, 2, 0, 1, 1, 4, 74, 2, 3, 0, 2, 1, 66, 0, 1, 0, 65, 0, 0, 64, 8, 24, 3, 3, 2, 1, 3, 1, 8, 0, 1, 16, 0, 0, 131, 0, 71, 1, 0, 7, 2, 1, 1, 0, 65, 0, 0, 64, 98, 37, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 99, 38, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64]

def charonNativeClientContractClosureAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 135, 100, 5, 1, 66, 1, 3, 9, 3, 5, 4, 6, 5, 4, 4, 6, 5, 4, 4, 0, 7, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 32, 6, 17, 6, 0, 2, 0, 32, 7, 17, 7, 0, 3, 0, 76, 63, 4, 0, 2, 1, 69, 0, 70, 0, 71, 0, 1, 0, 65, 0, 5, 33, 7, 33, 6, 33, 5, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 4, 3, 72, 0, 130, 8, 1, 0, 65, 0, 2, 33, 8, 33, 4, 64, 2, 1, 1, 3, 9, 2, 7, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 4, 16, 0, 0, 131, 0, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 2, 1, 68, 0, 129, 1, 1, 0, 65, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 4, 3, 71, 0, 129, 16, 1, 0, 65, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 6, 5, 70, 0, 72, 0, 1, 0, 65, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 16, 0, 0, 131, 0, 64, 3, 63, 1, 3, 12, 3, 12, 4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19, 0, 2, 32, 9, 32, 10, 73, 37, 10, 0, 8, 7, 1, 0, 65, 0, 3, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 75, 1, 5, 0, 4, 3, 70, 0, 129, 4, 1, 0, 65, 0, 6, 33, 6, 33, 5, 32, 7, 17, 7, 0, 3, 0, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 6, 5, 71, 0, 72, 0, 1, 0, 65, 0, 3, 33, 8, 33, 7, 33, 4, 64, 0, 0, 67, 0, 1, 21, 9, 0, 5, 74, 0, 130, 0, 69, 73, 0, 0, 10, 9, 0, 4, 33, 10, 33, 9, 48, 2, 4, 32, 4, 73, 38, 4, 0, 2, 1, 0, 2, 33, 10, 32, 11, 74, 26, 11, 0, 11, 7, 131, 2, 0, 0, 74, 27, 0, 0, 255, 7, 131, 2, 98, 37, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 99, 38, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64]

def charonCtrl1UnlinkedInspectorAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 29, 2, 1, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64]

def charonCtrl2aCallU64InspectorAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 222, 28, 1, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 93, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64]

def charonCtrl2WrongLibInstanceAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 6, 34, 10, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64, 2, 1, 1, 3, 9, 2, 7, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 4, 16, 0, 0, 131, 0, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 2, 1, 68, 0, 129, 1, 1, 0, 65, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 4, 3, 71, 0, 129, 16, 1, 0, 65, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 6, 5, 70, 0, 72, 0, 1, 0, 65, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 16, 0, 0, 131, 0, 64, 3, 2, 1, 3, 6, 1, 3, 1, 22, 1, 6, 3, 6, 0, 8, 32, 5, 16, 0, 0, 131, 0, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 2, 1, 67, 0, 68, 0, 1, 0, 65, 0, 4, 33, 4, 33, 3, 33, 2, 16, 0, 0, 131, 0, 64, 4, 3, 1, 3, 6, 2, 7, 3, 2, 3, 2, 19, 3, 0, 2, 32, 3, 17, 3, 0, 1, 0, 69, 67, 0, 0, 2, 1, 0, 1, 32, 4, 74, 26, 4, 0, 4, 3, 131, 2, 0, 3, 33, 3, 32, 5, 17, 5, 0, 2, 0, 75, 20, 0, 0, 6, 5, 69, 0, 129, 100, 1, 0, 65, 0, 0, 74, 27, 0, 0, 255, 3, 131, 2, 1, 0, 65, 0, 1, 33, 5, 64, 5, 63, 1, 3, 12, 3, 12, 4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19, 0, 2, 32, 9, 32, 10, 73, 37, 10, 0, 8, 7, 1, 0, 65, 0, 3, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 75, 1, 5, 0, 4, 3, 70, 0, 129, 4, 1, 0, 65, 0, 6, 33, 6, 33, 5, 32, 7, 17, 7, 0, 3, 0, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 6, 5, 71, 0, 72, 0, 1, 0, 65, 0, 3, 33, 8, 33, 7, 33, 4, 64, 0, 0, 67, 0, 1, 21, 9, 0, 5, 74, 0, 130, 0, 69, 73, 0, 0, 10, 9, 0, 4, 33, 10, 33, 9, 48, 2, 4, 32, 4, 73, 38, 4, 0, 2, 1, 0, 2, 33, 10, 32, 11, 74, 26, 11, 0, 11, 7, 131, 2, 0, 0, 74, 27, 0, 0, 255, 7, 131, 2, 6, 65, 1, 3, 20, 3, 16, 3, 6, 6, 2, 8, 6, 8, 6, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 19, 32, 17, 32, 18, 32, 19, 17, 18, 0, 128, 0, 17, 19, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 18, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 19, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 17, 8, 0, 3, 0, 69, 72, 0, 0, 4, 1, 0, 4, 32, 9, 32, 10, 16, 17, 0, 4, 2, 19, 10, 0, 1, 17, 4, 75, 1, 9, 0, 3, 2, 74, 0, 129, 10, 0, 0, 69, 19, 0, 0, 6, 5, 0, 6, 33, 10, 33, 9, 32, 11, 32, 12, 17, 18, 0, 128, 0, 17, 12, 0, 68, 0, 74, 24, 11, 0, 7, 2, 76, 0, 0, 4, 33, 8, 32, 13, 32, 14, 17, 14, 0, 3, 0, 75, 3, 13, 0, 8, 2, 78, 0, 129, 5, 0, 0, 71, 6, 0, 7, 6, 9, 0, 0, 69, 18, 0, 0, 11, 10, 0, 2, 33, 12, 33, 11, 68, 4, 0, 5, 33, 14, 32, 15, 32, 16, 17, 19, 0, 128, 0, 17, 16, 0, 70, 0, 74, 24, 15, 0, 12, 2, 80, 0, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 11, 13, 1, 0, 65, 0, 6, 33, 16, 33, 15, 17, 0, 0, 13, 0, 33, 13, 17, 19, 0, 128, 0, 33, 6, 69, 18, 0, 0, 15, 14, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 15, 11, 0, 2, 17, 18, 0, 128, 0, 33, 4, 64, 7, 7, 2, 3, 4, 1, 3, 1, 22, 22, 1, 0, 4, 32, 2, 32, 3, 16, 0, 0, 131, 0, 19, 2, 0, 1, 1, 4, 74, 2, 3, 0, 2, 1, 66, 0, 1, 0, 65, 0, 0, 64, 8, 24, 3, 3, 2, 1, 3, 1, 8, 0, 1, 16, 0, 0, 131, 0, 71, 1, 0, 7, 2, 1, 1, 0, 65, 0, 0, 64, 98, 37, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64, 99, 38, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 8, 64]

def charonCtrl3UnspecializedDestructAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 165, 222, 10, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64, 2, 1, 1, 3, 9, 2, 7, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 4, 16, 0, 0, 131, 0, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 2, 1, 68, 0, 129, 1, 1, 0, 65, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 4, 3, 71, 0, 129, 16, 1, 0, 65, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 6, 5, 70, 0, 72, 0, 1, 0, 65, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 16, 0, 0, 131, 0, 64, 3, 2, 1, 3, 6, 1, 3, 1, 22, 1, 6, 3, 6, 0, 8, 32, 5, 16, 0, 0, 131, 0, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 2, 1, 67, 0, 68, 0, 1, 0, 65, 0, 4, 33, 4, 33, 3, 33, 2, 16, 0, 0, 131, 0, 64, 4, 3, 1, 3, 6, 2, 7, 3, 2, 3, 2, 19, 3, 0, 2, 32, 3, 17, 3, 0, 1, 0, 69, 67, 0, 0, 2, 1, 0, 1, 32, 4, 74, 26, 4, 0, 4, 3, 131, 2, 0, 3, 33, 3, 32, 5, 17, 5, 0, 2, 0, 75, 20, 0, 0, 6, 5, 69, 0, 129, 100, 1, 0, 65, 0, 0, 74, 27, 0, 0, 255, 3, 131, 2, 1, 0, 65, 0, 1, 33, 5, 64, 5, 63, 1, 3, 12, 3, 12, 4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19, 0, 2, 32, 9, 32, 10, 73, 37, 10, 0, 8, 7, 1, 0, 65, 0, 3, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 75, 1, 5, 0, 4, 3, 70, 0, 129, 4, 1, 0, 65, 0, 6, 33, 6, 33, 5, 32, 7, 17, 7, 0, 3, 0, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 6, 5, 71, 0, 72, 0, 1, 0, 65, 0, 3, 33, 8, 33, 7, 33, 4, 64, 0, 0, 67, 0, 1, 21, 9, 0, 5, 74, 0, 130, 0, 69, 73, 0, 0, 10, 9, 0, 4, 33, 10, 33, 9, 48, 2, 4, 32, 4, 73, 38, 4, 0, 2, 1, 0, 2, 33, 10, 32, 11, 74, 26, 11, 0, 11, 7, 131, 2, 0, 0, 74, 27, 0, 0, 255, 7, 131, 2, 6, 65, 1, 3, 20, 3, 16, 3, 6, 6, 2, 8, 6, 8, 6, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 19, 32, 17, 32, 18, 32, 19, 17, 18, 0, 128, 0, 17, 19, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 18, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 19, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 17, 8, 0, 3, 0, 69, 72, 0, 0, 4, 1, 0, 4, 32, 9, 32, 10, 16, 17, 0, 4, 2, 19, 10, 0, 1, 17, 4, 75, 1, 9, 0, 3, 2, 74, 0, 129, 10, 0, 0, 69, 19, 0, 0, 6, 5, 0, 6, 33, 10, 33, 9, 32, 11, 32, 12, 17, 18, 0, 128, 0, 17, 12, 0, 68, 0, 74, 24, 11, 0, 7, 2, 76, 0, 0, 4, 33, 8, 32, 13, 32, 14, 17, 14, 0, 3, 0, 75, 3, 13, 0, 8, 2, 78, 0, 129, 5, 0, 0, 71, 6, 0, 7, 6, 9, 0, 0, 69, 18, 0, 0, 11, 10, 0, 2, 33, 12, 33, 11, 68, 4, 0, 5, 33, 14, 32, 15, 32, 16, 17, 19, 0, 128, 0, 17, 16, 0, 70, 0, 74, 24, 15, 0, 12, 2, 80, 0, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 11, 13, 1, 0, 65, 0, 6, 33, 16, 33, 15, 17, 0, 0, 13, 0, 33, 13, 17, 19, 0, 128, 0, 33, 6, 69, 18, 0, 0, 15, 14, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 15, 11, 0, 2, 17, 18, 0, 128, 0, 33, 4, 64, 7, 7, 2, 3, 4, 1, 3, 1, 22, 22, 1, 0, 4, 32, 2, 32, 3, 16, 0, 0, 131, 0, 19, 2, 0, 1, 1, 4, 74, 2, 3, 0, 2, 1, 66, 0, 1, 0, 65, 0, 0, 64, 8, 24, 3, 3, 2, 1, 3, 1, 8, 0, 1, 16, 0, 0, 131, 0, 71, 1, 0, 91, 2, 1, 1, 0, 65, 0, 0, 64, 98, 37, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 99, 38, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64]

def charonCtrl3bOmittedDropFlagClearAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 216, 197, 10, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64, 2, 1, 1, 3, 9, 2, 7, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 4, 16, 0, 0, 131, 0, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 2, 1, 68, 0, 129, 1, 1, 0, 65, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 4, 3, 71, 0, 129, 16, 1, 0, 65, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 6, 5, 70, 0, 72, 0, 1, 0, 65, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 16, 0, 0, 131, 0, 64, 3, 2, 1, 3, 6, 1, 3, 1, 22, 1, 6, 3, 6, 0, 8, 32, 5, 16, 0, 0, 131, 0, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 2, 1, 67, 0, 68, 0, 1, 0, 65, 0, 4, 33, 4, 33, 3, 33, 2, 16, 0, 0, 131, 0, 64, 4, 3, 1, 3, 6, 2, 7, 3, 2, 3, 2, 19, 3, 0, 2, 32, 3, 17, 3, 0, 1, 0, 69, 67, 0, 0, 2, 1, 0, 1, 32, 4, 74, 26, 4, 0, 4, 3, 131, 2, 0, 3, 33, 3, 32, 5, 17, 5, 0, 2, 0, 75, 20, 0, 0, 6, 5, 69, 0, 129, 100, 1, 0, 65, 0, 0, 74, 27, 0, 0, 255, 3, 131, 2, 1, 0, 65, 0, 1, 33, 5, 64, 5, 63, 1, 3, 12, 3, 12, 4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19, 0, 2, 32, 9, 32, 10, 73, 37, 10, 0, 8, 7, 1, 0, 65, 0, 3, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 75, 1, 5, 0, 4, 3, 70, 0, 129, 4, 1, 0, 65, 0, 6, 33, 6, 33, 5, 32, 7, 17, 7, 0, 3, 0, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 6, 5, 71, 0, 72, 0, 1, 0, 65, 0, 3, 33, 8, 33, 7, 33, 4, 64, 0, 0, 67, 0, 1, 21, 9, 0, 5, 74, 0, 130, 0, 69, 73, 0, 0, 10, 9, 0, 4, 33, 10, 33, 9, 48, 2, 4, 32, 4, 73, 38, 4, 0, 2, 1, 0, 2, 33, 10, 32, 11, 74, 26, 11, 0, 11, 7, 131, 2, 0, 0, 74, 27, 0, 0, 255, 7, 131, 2, 6, 65, 1, 3, 20, 3, 16, 3, 6, 6, 2, 8, 6, 8, 6, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 19, 32, 17, 32, 18, 32, 19, 17, 18, 0, 128, 0, 17, 19, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 18, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 19, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 17, 8, 0, 3, 0, 69, 72, 0, 0, 4, 1, 0, 4, 32, 9, 32, 10, 16, 17, 0, 4, 2, 19, 10, 0, 1, 17, 4, 75, 1, 9, 0, 3, 2, 74, 0, 129, 10, 0, 0, 69, 19, 0, 0, 6, 5, 0, 6, 33, 10, 33, 9, 32, 11, 32, 12, 17, 18, 0, 128, 1, 17, 12, 0, 68, 0, 74, 24, 11, 0, 7, 2, 76, 0, 0, 4, 33, 8, 32, 13, 32, 14, 17, 14, 0, 3, 0, 75, 3, 13, 0, 8, 2, 78, 0, 129, 5, 0, 0, 71, 6, 0, 7, 6, 9, 0, 0, 69, 18, 0, 0, 11, 10, 0, 2, 33, 12, 33, 11, 68, 4, 0, 5, 33, 14, 32, 15, 32, 16, 17, 19, 0, 128, 0, 17, 16, 0, 70, 0, 74, 24, 15, 0, 12, 2, 80, 0, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 11, 13, 1, 0, 65, 0, 6, 33, 16, 33, 15, 17, 0, 0, 13, 0, 33, 13, 17, 19, 0, 128, 0, 33, 6, 69, 18, 0, 0, 15, 14, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 15, 11, 0, 2, 17, 18, 0, 128, 0, 33, 4, 64, 7, 7, 2, 3, 4, 1, 3, 1, 22, 22, 1, 0, 4, 32, 2, 32, 3, 16, 0, 0, 131, 0, 19, 2, 0, 1, 1, 4, 74, 2, 3, 0, 2, 1, 66, 0, 1, 0, 65, 0, 0, 64, 8, 24, 3, 3, 2, 1, 3, 1, 8, 0, 1, 16, 0, 0, 131, 0, 71, 1, 0, 7, 2, 1, 1, 0, 65, 0, 0, 64, 98, 37, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 99, 38, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64]

def charonCtrl4PrivateEvent9AmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 98, 55, 10, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64, 2, 1, 1, 3, 9, 2, 7, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 4, 16, 0, 0, 131, 0, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 2, 1, 68, 0, 129, 1, 1, 0, 65, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 4, 3, 71, 0, 129, 16, 1, 0, 65, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 6, 5, 70, 0, 72, 0, 1, 0, 65, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 16, 0, 0, 131, 0, 64, 3, 2, 1, 3, 6, 1, 3, 1, 22, 1, 6, 3, 6, 0, 8, 32, 5, 16, 0, 0, 131, 0, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 2, 1, 67, 0, 68, 0, 1, 0, 65, 0, 4, 33, 4, 33, 3, 33, 2, 16, 0, 0, 131, 0, 64, 4, 3, 1, 3, 6, 2, 7, 3, 2, 3, 2, 19, 3, 0, 2, 32, 3, 17, 3, 0, 1, 0, 69, 67, 0, 0, 2, 1, 0, 1, 32, 4, 74, 26, 4, 0, 4, 3, 131, 2, 0, 3, 33, 3, 32, 5, 17, 5, 0, 2, 0, 75, 20, 0, 0, 6, 5, 69, 0, 129, 100, 1, 0, 65, 0, 0, 74, 27, 0, 0, 255, 3, 131, 2, 1, 0, 65, 0, 1, 33, 5, 64, 5, 63, 1, 3, 12, 3, 12, 4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19, 0, 2, 32, 9, 32, 10, 73, 37, 10, 0, 8, 7, 1, 0, 65, 0, 3, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 75, 1, 5, 0, 4, 3, 70, 0, 129, 9, 1, 0, 65, 0, 6, 33, 6, 33, 5, 32, 7, 17, 7, 0, 3, 0, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 6, 5, 71, 0, 72, 0, 1, 0, 65, 0, 3, 33, 8, 33, 7, 33, 4, 64, 0, 0, 67, 0, 1, 21, 9, 0, 5, 74, 0, 130, 0, 69, 73, 0, 0, 10, 9, 0, 4, 33, 10, 33, 9, 48, 2, 4, 32, 4, 73, 38, 4, 0, 2, 1, 0, 2, 33, 10, 32, 11, 74, 26, 11, 0, 11, 7, 131, 2, 0, 0, 74, 27, 0, 0, 255, 7, 131, 2, 6, 65, 1, 3, 20, 3, 16, 3, 6, 6, 2, 8, 6, 8, 6, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 19, 32, 17, 32, 18, 32, 19, 17, 18, 0, 128, 0, 17, 19, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 18, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 19, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 17, 8, 0, 3, 0, 69, 72, 0, 0, 4, 1, 0, 4, 32, 9, 32, 10, 16, 17, 0, 4, 2, 19, 10, 0, 1, 17, 4, 75, 1, 9, 0, 3, 2, 74, 0, 129, 10, 0, 0, 69, 19, 0, 0, 6, 5, 0, 6, 33, 10, 33, 9, 32, 11, 32, 12, 17, 18, 0, 128, 0, 17, 12, 0, 68, 0, 74, 24, 11, 0, 7, 2, 76, 0, 0, 4, 33, 8, 32, 13, 32, 14, 17, 14, 0, 3, 0, 75, 3, 13, 0, 8, 2, 78, 0, 129, 5, 0, 0, 71, 6, 0, 7, 6, 9, 0, 0, 69, 18, 0, 0, 11, 10, 0, 2, 33, 12, 33, 11, 68, 4, 0, 5, 33, 14, 32, 15, 32, 16, 17, 19, 0, 128, 0, 17, 16, 0, 70, 0, 74, 24, 15, 0, 12, 2, 80, 0, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 11, 13, 1, 0, 65, 0, 6, 33, 16, 33, 15, 17, 0, 0, 13, 0, 33, 13, 17, 19, 0, 128, 0, 33, 6, 69, 18, 0, 0, 15, 14, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 15, 11, 0, 2, 17, 18, 0, 128, 0, 33, 4, 64, 7, 7, 2, 3, 4, 1, 3, 1, 22, 22, 1, 0, 4, 32, 2, 32, 3, 16, 0, 0, 131, 0, 19, 2, 0, 1, 1, 4, 74, 2, 3, 0, 2, 1, 66, 0, 1, 0, 65, 0, 0, 64, 8, 24, 3, 3, 2, 1, 3, 1, 8, 0, 1, 16, 0, 0, 131, 0, 71, 1, 0, 7, 2, 1, 1, 0, 65, 0, 0, 64, 98, 37, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 99, 38, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64]

def charonCtrl5ValidAdminChangeAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 206, 217, 10, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64, 2, 1, 1, 3, 9, 2, 7, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 4, 16, 0, 0, 131, 0, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 2, 1, 68, 0, 129, 1, 1, 0, 65, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 4, 3, 71, 0, 129, 16, 1, 0, 65, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 6, 5, 70, 0, 72, 0, 1, 0, 65, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 16, 0, 0, 131, 0, 64, 3, 2, 1, 3, 6, 1, 3, 1, 22, 1, 6, 3, 6, 0, 8, 32, 5, 16, 0, 0, 131, 0, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 2, 1, 67, 0, 68, 0, 1, 0, 65, 0, 4, 33, 4, 33, 3, 33, 2, 16, 0, 0, 131, 0, 64, 4, 3, 1, 3, 6, 2, 7, 3, 2, 3, 2, 19, 3, 0, 2, 32, 3, 17, 3, 0, 1, 0, 69, 67, 0, 0, 2, 1, 0, 1, 32, 4, 74, 26, 4, 0, 4, 3, 131, 2, 0, 3, 33, 3, 32, 5, 17, 5, 0, 2, 0, 75, 20, 0, 0, 6, 5, 69, 0, 129, 100, 1, 0, 65, 0, 0, 74, 27, 0, 0, 255, 3, 131, 2, 1, 0, 65, 0, 1, 33, 5, 64, 5, 63, 1, 3, 12, 3, 12, 4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19, 0, 2, 32, 9, 32, 10, 73, 37, 10, 0, 8, 7, 1, 0, 65, 0, 3, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 75, 1, 5, 0, 4, 3, 70, 0, 129, 4, 1, 0, 65, 0, 6, 33, 6, 33, 5, 32, 7, 17, 7, 0, 3, 0, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 6, 5, 71, 0, 72, 0, 1, 0, 65, 0, 3, 33, 8, 33, 7, 33, 4, 64, 0, 0, 67, 0, 1, 21, 9, 0, 5, 74, 0, 130, 0, 69, 73, 0, 0, 10, 9, 0, 4, 33, 10, 33, 9, 48, 2, 4, 32, 4, 73, 38, 4, 0, 2, 1, 0, 2, 33, 10, 32, 11, 74, 26, 11, 0, 11, 7, 131, 2, 0, 0, 74, 27, 0, 0, 255, 7, 131, 2, 6, 65, 1, 3, 20, 3, 16, 3, 6, 6, 2, 8, 6, 8, 6, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 19, 32, 17, 32, 18, 32, 19, 17, 18, 0, 128, 0, 17, 19, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 18, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 19, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 17, 8, 0, 3, 0, 69, 72, 0, 0, 4, 1, 0, 4, 32, 9, 32, 10, 16, 17, 0, 4, 2, 19, 10, 0, 1, 17, 4, 75, 1, 9, 0, 3, 2, 74, 0, 129, 10, 0, 0, 69, 19, 0, 0, 6, 5, 0, 6, 33, 10, 33, 9, 32, 11, 32, 12, 17, 18, 0, 128, 0, 17, 12, 0, 68, 0, 74, 24, 11, 0, 7, 2, 76, 0, 0, 6, 32, 17, 33, 17, 33, 8, 32, 13, 32, 14, 17, 14, 0, 3, 0, 75, 3, 13, 0, 8, 2, 78, 0, 129, 5, 0, 0, 71, 6, 0, 7, 6, 9, 0, 0, 69, 18, 0, 0, 11, 10, 0, 2, 33, 12, 33, 11, 68, 4, 0, 5, 33, 14, 32, 15, 32, 16, 17, 19, 0, 128, 0, 17, 16, 0, 70, 0, 74, 24, 15, 0, 12, 2, 80, 0, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 11, 13, 1, 0, 65, 0, 6, 33, 16, 33, 15, 17, 0, 0, 13, 0, 33, 13, 17, 19, 0, 128, 0, 33, 6, 69, 18, 0, 0, 15, 14, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 15, 11, 0, 2, 17, 18, 0, 128, 0, 33, 4, 64, 7, 7, 2, 3, 4, 1, 3, 1, 22, 22, 1, 0, 4, 32, 2, 32, 3, 16, 0, 0, 131, 0, 19, 2, 0, 1, 1, 4, 74, 2, 3, 0, 2, 1, 66, 0, 1, 0, 65, 0, 0, 64, 8, 24, 3, 3, 2, 1, 3, 1, 8, 0, 1, 16, 0, 0, 131, 0, 71, 1, 0, 7, 2, 1, 1, 0, 65, 0, 0, 64, 98, 37, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 99, 38, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64]

def charonNativeInspectorBodies : List WireBody :=
  decodePackageBodies charonNativeClientInspectorClosureAmirBytes

def mutateCharonNativeWrongAlign8 (bs : List WireBody) : List WireBody :=
  bs.map (fun b =>
    if b.symId == 37 || b.symId == 38 then
      { b with blocks :=
          [ { isCleanup := false
            , stmts := [ .assignUseRetagYes { localIdx := 0, proj := .here } (.constUsize 8) ]
            , term := .ret } ] }
    else b)

def mutateCharonNativeOmitDropFlagClearInBb3 (bs : List WireBody) : List WireBody :=
  bs.map (fun b =>
    if b.symId == 65 then
      { b with blocks := mutateCharonBlocksOmitDropFlagClearInBb3 0 b.blocks }
    else b)

def mutateCharonNativeAdminInBb4 (bs : List WireBody) : List WireBody :=
  bs.map (fun b =>
    if b.symId == 65 then
      { b with blocks := mutateCharonBlocksAdminInBb4 0 b.blocks }
    else b)

theorem r3_native_inspector_closure_verified :
    isAdmittedPackageBytes charonNativeClientInspectorClosureAmirBytes = true ∧
    checkRuntimeClosedBodies (decodePackageBodies charonNativeClientInspectorClosureAmirBytes) = true ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonNativeClientInspectorClosureAmirBytes) 60 true false =
      .normalReturn 105 (2, 65) (1, 2) [4, 2, 1] ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonNativeClientInspectorClosureAmirBytes) 60 true true =
      .unwoundWithCleanup (3, 1185) (1, 2) [4, 10, 1, 2] ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonNativeClientInspectorClosureAmirBytes) 60 false false =
      .failed .ub := by
  decide

theorem r3_native_contract_closure_verified :
    isAdmittedPackageBytes charonNativeClientContractClosureAmirBytes = true ∧
    checkRuntimeClosedBodies (decodePackageBodies charonNativeClientContractClosureAmirBytes) = true ∧
    evalClientEntryLinkedOperational (decodePackageBodies charonNativeClientContractClosureAmirBytes) 22 false 16 =
      (.ub, 0) ∧
    evalClientEntryLinkedOperational (decodePackageBodies charonNativeClientContractClosureAmirBytes) 22 true 16 =
      (.returned (.scalar 28), 1) := by
  decide

theorem r3_charon_native_single_artifact_closures_satisfy_contract_and_inspector_endpoints :
    (isAdmittedPackageBytes charonNativeClientInspectorClosureAmirBytes = true ∧
     checkRuntimeClosedBodies (decodePackageBodies charonNativeClientInspectorClosureAmirBytes) = true ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonNativeClientInspectorClosureAmirBytes) 60 true false =
       .normalReturn 105 (2, 65) (1, 2) [4, 2, 1] ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonNativeClientInspectorClosureAmirBytes) 60 true true =
       .unwoundWithCleanup (3, 1185) (1, 2) [4, 10, 1, 2] ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonNativeClientInspectorClosureAmirBytes) 60 false false =
       .failed .ub) ∧
    (isAdmittedPackageBytes charonNativeClientContractClosureAmirBytes = true ∧
     checkRuntimeClosedBodies (decodePackageBodies charonNativeClientContractClosureAmirBytes) = true ∧
     evalClientEntryLinkedOperational (decodePackageBodies charonNativeClientContractClosureAmirBytes) 22 false 16 =
       (.ub, 0) ∧
     evalClientEntryLinkedOperational (decodePackageBodies charonNativeClientContractClosureAmirBytes) 22 true 16 =
       (.returned (.scalar 28), 1)) :=
  ⟨r3_native_inspector_closure_verified, r3_native_contract_closure_verified⟩

theorem r4_ctrl1_unlinked_inspector_verified :
    decodePackageBodies charonCtrl1UnlinkedInspectorAmirBytes = charonClientDirectMirInspectorBodies ∧
    isAdmittedPackageBytes charonCtrl1UnlinkedInspectorAmirBytes = false ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl1UnlinkedInspectorAmirBytes) 55 true false =
      .failed (.missingBody 63) := by
  decide

theorem r4_ctrl2a_call_u64_inspector_verified :
    checkBodiesClosure
      (decodePackageBodies charonCtrl2aCallU64InspectorAmirBytes ++ charonStatefulGenericLibBodies)
      (decodePackageBodies charonCtrl2aCallU64InspectorAmirBytes ++ charonStatefulGenericLibBodies) = false ∧
    evalClientDirectMirInspectorWithFuel
      (decodePackageBodies charonCtrl2aCallU64InspectorAmirBytes ++ charonStatefulGenericLibBodies) 55 true false =
      .failed (.missingBody 93) := by
  decide

theorem r4_ctrl2_wrong_lib_instance_decode :
    isAdmittedPackageBytes charonCtrl2WrongLibInstanceAmirBytes = true ∧
    decodePackageBodies charonCtrl2WrongLibInstanceAmirBytes =
      mutateCharonNativeWrongAlign8 charonNativeInspectorBodies := by
  decide

theorem r4_ctrl2_wrong_lib_instance_eval :
    evalClientDirectMirInspectorWithFuel (mutateCharonNativeWrongAlign8 charonNativeInspectorBodies) 55 true false =
      evalClientDirectMirInspectorWithFuel charonLinkedWrongAlignInstanceBodies 55 true false ∧
    evalClientDirectMirInspectorWithFuel (mutateCharonNativeWrongAlign8 charonNativeInspectorBodies) 55 true false =
      .normalReturn 0 (2, 65) (1, 2) [4, 2, 1] := by
  decide

theorem r4_ctrl2_wrong_lib_instance_verified :
    isAdmittedPackageBytes charonCtrl2WrongLibInstanceAmirBytes = true ∧
    decodePackageBodies charonCtrl2WrongLibInstanceAmirBytes =
      mutateCharonNativeWrongAlign8 charonNativeInspectorBodies ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl2WrongLibInstanceAmirBytes) 55 true false =
      evalClientDirectMirInspectorWithFuel charonLinkedWrongAlignInstanceBodies 55 true false ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl2WrongLibInstanceAmirBytes) 55 true false =
      .normalReturn 0 (2, 65) (1, 2) [4, 2, 1] := by
  have ⟨h1, h2⟩ := r4_ctrl2_wrong_lib_instance_decode
  have ⟨h3, h4⟩ := r4_ctrl2_wrong_lib_instance_eval
  rw [h2]
  exact ⟨h1, rfl, h3, h4⟩

theorem r4_ctrl3_unspecialized_destruct_verified :
    isAdmittedPackageBytes charonCtrl3UnspecializedDestructAmirBytes = false := by
  decide

theorem r4_ctrl3b_omitted_drop_flag_clear_decode :
    isAdmittedPackageBytes charonCtrl3bOmittedDropFlagClearAmirBytes = true ∧
    decodePackageBodies charonCtrl3bOmittedDropFlagClearAmirBytes =
      mutateCharonNativeOmitDropFlagClearInBb3 charonNativeInspectorBodies := by
  decide

theorem r4_ctrl3b_omitted_drop_flag_clear_eval :
    evalClientDirectMirInspectorWithFuel (mutateCharonNativeOmitDropFlagClearInBb3 charonNativeInspectorBodies) 65 true true =
      evalClientDirectMirInspectorWithFuel charonLinkedOmittedCleanupBodies 65 true true ∧
    evalClientDirectMirInspectorWithFuel (mutateCharonNativeOmitDropFlagClearInBb3 charonNativeInspectorBodies) 65 true true =
      .unwoundWithCleanup (4, 18961) (1, 2) [4, 10, 1, 2, 1] := by
  decide

theorem r4_ctrl3b_omitted_drop_flag_clear_verified :
    isAdmittedPackageBytes charonCtrl3bOmittedDropFlagClearAmirBytes = true ∧
    decodePackageBodies charonCtrl3bOmittedDropFlagClearAmirBytes =
      mutateCharonNativeOmitDropFlagClearInBb3 charonNativeInspectorBodies ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl3bOmittedDropFlagClearAmirBytes) 65 true true =
      evalClientDirectMirInspectorWithFuel charonLinkedOmittedCleanupBodies 65 true true ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl3bOmittedDropFlagClearAmirBytes) 65 true true =
      .unwoundWithCleanup (4, 18961) (1, 2) [4, 10, 1, 2, 1] := by
  have ⟨h1, h2⟩ := r4_ctrl3b_omitted_drop_flag_clear_decode
  have ⟨h3, h4⟩ := r4_ctrl3b_omitted_drop_flag_clear_eval
  rw [h2]
  exact ⟨h1, rfl, h3, h4⟩

theorem r4_ctrl4_private_event9_decode :
    isAdmittedPackageBytes charonCtrl4PrivateEvent9AmirBytes = true ∧
    decodePackageBodies charonCtrl4PrivateEvent9AmirBytes =
      charonNativeInspectorBodies.map mutateStepGenericEventTagTo9 := by
  decide

theorem r4_ctrl4_private_event9_eval :
    evalClientDirectMirInspectorWithFuel (charonNativeInspectorBodies.map mutateStepGenericEventTagTo9) 55 true false =
      evalClientDirectMirInspectorWithFuel charonLinkedEvent9Bodies 55 true false ∧
    evalClientDirectMirInspectorWithFuel (charonNativeInspectorBodies.map mutateStepGenericEventTagTo9) 55 true false =
      .normalReturn 105 (2, 145) (1, 2) [9, 2, 1] := by
  decide

theorem r4_ctrl4_private_event9_verified :
    isAdmittedPackageBytes charonCtrl4PrivateEvent9AmirBytes = true ∧
    decodePackageBodies charonCtrl4PrivateEvent9AmirBytes =
      charonNativeInspectorBodies.map mutateStepGenericEventTagTo9 ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl4PrivateEvent9AmirBytes) 55 true false =
      evalClientDirectMirInspectorWithFuel charonLinkedEvent9Bodies 55 true false ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl4PrivateEvent9AmirBytes) 55 true false =
      .normalReturn 105 (2, 145) (1, 2) [9, 2, 1] := by
  have ⟨h1, h2⟩ := r4_ctrl4_private_event9_decode
  have ⟨h3, h4⟩ := r4_ctrl4_private_event9_eval
  rw [h2]
  exact ⟨h1, rfl, h3, h4⟩

theorem r4_ctrl5_valid_admin_change_decode :
    isAdmittedPackageBytes charonCtrl5ValidAdminChangeAmirBytes = true ∧
    decodePackageBodies charonCtrl5ValidAdminChangeAmirBytes =
      mutateCharonNativeAdminInBb4 charonNativeInspectorBodies ∧
    charonCtrl5ValidAdminChangeAmirBytes ≠ charonNativeClientInspectorClosureAmirBytes := by
  decide

theorem r4_ctrl5_valid_admin_change_eval :
    evalClientDirectMirInspectorWithFuel (mutateCharonNativeAdminInBb4 charonNativeInspectorBodies) 60 true false =
      .normalReturn 105 (2, 65) (1, 2) [4, 2, 1] ∧
    evalClientDirectMirInspectorWithFuel (mutateCharonNativeAdminInBb4 charonNativeInspectorBodies) 60 true true =
      .unwoundWithCleanup (3, 1185) (1, 2) [4, 10, 1, 2] ∧
    evalClientDirectMirInspectorWithFuel (mutateCharonNativeAdminInBb4 charonNativeInspectorBodies) 60 false false =
      .failed .ub := by
  decide

theorem r4_ctrl5_valid_admin_change_verified :
    isAdmittedPackageBytes charonCtrl5ValidAdminChangeAmirBytes = true ∧
    decodePackageBodies charonCtrl5ValidAdminChangeAmirBytes =
      mutateCharonNativeAdminInBb4 charonNativeInspectorBodies ∧
    charonCtrl5ValidAdminChangeAmirBytes ≠ charonNativeClientInspectorClosureAmirBytes ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl5ValidAdminChangeAmirBytes) 60 true false =
      .normalReturn 105 (2, 65) (1, 2) [4, 2, 1] ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl5ValidAdminChangeAmirBytes) 60 true true =
      .unwoundWithCleanup (3, 1185) (1, 2) [4, 10, 1, 2] ∧
    evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl5ValidAdminChangeAmirBytes) 60 false false =
      .failed .ub := by
  have ⟨h1, h2, h3⟩ := r4_ctrl5_valid_admin_change_decode
  have ⟨h4, h5, h6⟩ := r4_ctrl5_valid_admin_change_eval
  rw [h2]
  exact ⟨h1, rfl, h3, h4, h5, h6⟩

theorem r4_all_seven_charon_generated_amir_controls_connected_and_verified :
    (decodePackageBodies charonCtrl1UnlinkedInspectorAmirBytes = charonClientDirectMirInspectorBodies ∧
     isAdmittedPackageBytes charonCtrl1UnlinkedInspectorAmirBytes = false ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl1UnlinkedInspectorAmirBytes) 55 true false =
       .failed (.missingBody 63)) ∧
    (checkBodiesClosure
       (decodePackageBodies charonCtrl2aCallU64InspectorAmirBytes ++ charonStatefulGenericLibBodies)
       (decodePackageBodies charonCtrl2aCallU64InspectorAmirBytes ++ charonStatefulGenericLibBodies) = false ∧
     evalClientDirectMirInspectorWithFuel
       (decodePackageBodies charonCtrl2aCallU64InspectorAmirBytes ++ charonStatefulGenericLibBodies) 55 true false =
       .failed (.missingBody 93)) ∧
    (isAdmittedPackageBytes charonCtrl2WrongLibInstanceAmirBytes = true ∧
     decodePackageBodies charonCtrl2WrongLibInstanceAmirBytes =
       mutateCharonNativeWrongAlign8 charonNativeInspectorBodies ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl2WrongLibInstanceAmirBytes) 55 true false =
       evalClientDirectMirInspectorWithFuel charonLinkedWrongAlignInstanceBodies 55 true false ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl2WrongLibInstanceAmirBytes) 55 true false =
       .normalReturn 0 (2, 65) (1, 2) [4, 2, 1]) ∧
    isAdmittedPackageBytes charonCtrl3UnspecializedDestructAmirBytes = false ∧
    (isAdmittedPackageBytes charonCtrl3bOmittedDropFlagClearAmirBytes = true ∧
     decodePackageBodies charonCtrl3bOmittedDropFlagClearAmirBytes =
       mutateCharonNativeOmitDropFlagClearInBb3 charonNativeInspectorBodies ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl3bOmittedDropFlagClearAmirBytes) 65 true true =
       evalClientDirectMirInspectorWithFuel charonLinkedOmittedCleanupBodies 65 true true ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl3bOmittedDropFlagClearAmirBytes) 65 true true =
       .unwoundWithCleanup (4, 18961) (1, 2) [4, 10, 1, 2, 1]) ∧
    (isAdmittedPackageBytes charonCtrl4PrivateEvent9AmirBytes = true ∧
     decodePackageBodies charonCtrl4PrivateEvent9AmirBytes =
       charonNativeInspectorBodies.map mutateStepGenericEventTagTo9 ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl4PrivateEvent9AmirBytes) 55 true false =
       evalClientDirectMirInspectorWithFuel charonLinkedEvent9Bodies 55 true false ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl4PrivateEvent9AmirBytes) 55 true false =
       .normalReturn 105 (2, 145) (1, 2) [9, 2, 1]) ∧
    (isAdmittedPackageBytes charonCtrl5ValidAdminChangeAmirBytes = true ∧
     decodePackageBodies charonCtrl5ValidAdminChangeAmirBytes =
       mutateCharonNativeAdminInBb4 charonNativeInspectorBodies ∧
     charonCtrl5ValidAdminChangeAmirBytes ≠ charonNativeClientInspectorClosureAmirBytes ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl5ValidAdminChangeAmirBytes) 60 true false =
       .normalReturn 105 (2, 65) (1, 2) [4, 2, 1] ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl5ValidAdminChangeAmirBytes) 60 true true =
       .unwoundWithCleanup (3, 1185) (1, 2) [4, 10, 1, 2] ∧
     evalClientDirectMirInspectorWithFuel (decodePackageBodies charonCtrl5ValidAdminChangeAmirBytes) 60 false false =
       .failed .ub) :=
  ⟨r4_ctrl1_unlinked_inspector_verified,
   r4_ctrl2a_call_u64_inspector_verified,
   r4_ctrl2_wrong_lib_instance_verified,
   r4_ctrl3_unspecialized_destruct_verified,
   r4_ctrl3b_omitted_drop_flag_clear_verified,
   r4_ctrl4_private_event9_verified,
   r4_ctrl5_valid_admin_change_verified⟩

#print axioms r3_charon_native_single_artifact_closures_satisfy_contract_and_inspector_endpoints
#print axioms r4_all_seven_charon_generated_amir_controls_connected_and_verified

/-! ## 3. `Q6` (`F6`, `#93` §11): Enforceable Charon Adapter Domain & ULLBC Local-Type Mutation Control (`charonCtrl6LocalU64TypeMismatchAmirBytes`) -/

/-- Generated `.amir` v3 control from `extract_and_link_charon_h3.py` (`charon_h3_ctrl6_local_u64_type_mismatch.amir`,
    `1,019` B, `fp16 = [96, 237]`), produced by mutating `locals[0].ty` of `inspect_and_commit_slot`
    (`symId = 67`) from `U32` to `U64` in the parsed ULLBC JSON AST and translating through the
    repaired `extract_ullbc_local_type_tags` adapter. -/
def charonCtrl6LocalU64TypeMismatchAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 96, 237, 10, 1, 67, 1, 3, 14, 4, 8, 4, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64, 2, 1, 1, 3, 9, 2, 7, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 4, 16, 0, 0, 131, 0, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 2, 1, 68, 0, 129, 1, 1, 0, 65, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 4, 3, 71, 0, 129, 16, 1, 0, 65, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 6, 5, 70, 0, 72, 0, 1, 0, 65, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 16, 0, 0, 131, 0, 64, 3, 2, 1, 3, 6, 1, 3, 1, 22, 1, 6, 3, 6, 0, 8, 32, 5, 16, 0, 0, 131, 0, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 2, 1, 67, 0, 68, 0, 1, 0, 65, 0, 4, 33, 4, 33, 3, 33, 2, 16, 0, 0, 131, 0, 64, 4, 3, 1, 3, 6, 2, 7, 3, 2, 3, 2, 19, 3, 0, 2, 32, 3, 17, 3, 0, 1, 0, 69, 67, 0, 0, 2, 1, 0, 1, 32, 4, 74, 26, 4, 0, 4, 3, 131, 2, 0, 3, 33, 3, 32, 5, 17, 5, 0, 2, 0, 75, 20, 0, 0, 6, 5, 69, 0, 129, 100, 1, 0, 65, 0, 0, 74, 27, 0, 0, 255, 3, 131, 2, 1, 0, 65, 0, 1, 33, 5, 64, 5, 63, 1, 3, 12, 3, 12, 4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19, 0, 2, 32, 9, 32, 10, 73, 37, 10, 0, 8, 7, 1, 0, 65, 0, 3, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 75, 1, 5, 0, 4, 3, 70, 0, 129, 4, 1, 0, 65, 0, 6, 33, 6, 33, 5, 32, 7, 17, 7, 0, 3, 0, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 6, 5, 71, 0, 72, 0, 1, 0, 65, 0, 3, 33, 8, 33, 7, 33, 4, 64, 0, 0, 67, 0, 1, 21, 9, 0, 5, 74, 0, 130, 0, 69, 73, 0, 0, 10, 9, 0, 4, 33, 10, 33, 9, 48, 2, 4, 32, 4, 73, 38, 4, 0, 2, 1, 0, 2, 33, 10, 32, 11, 74, 26, 11, 0, 11, 7, 131, 2, 0, 0, 74, 27, 0, 0, 255, 7, 131, 2, 6, 65, 1, 3, 20, 3, 16, 3, 6, 6, 2, 8, 6, 8, 6, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 19, 32, 17, 32, 18, 32, 19, 17, 18, 0, 128, 0, 17, 19, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 18, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 19, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 17, 8, 0, 3, 0, 69, 72, 0, 0, 4, 1, 0, 4, 32, 9, 32, 10, 16, 17, 0, 4, 2, 19, 10, 0, 1, 17, 4, 75, 1, 9, 0, 3, 2, 74, 0, 129, 10, 0, 0, 69, 19, 0, 0, 6, 5, 0, 6, 33, 10, 33, 9, 32, 11, 32, 12, 17, 18, 0, 128, 0, 17, 12, 0, 68, 0, 74, 24, 11, 0, 7, 2, 76, 0, 0, 4, 33, 8, 32, 13, 32, 14, 17, 14, 0, 3, 0, 75, 3, 13, 0, 8, 2, 78, 0, 129, 5, 0, 0, 71, 6, 0, 7, 6, 9, 0, 0, 69, 18, 0, 0, 11, 10, 0, 2, 33, 12, 33, 11, 68, 4, 0, 5, 33, 14, 32, 15, 32, 16, 17, 19, 0, 128, 0, 17, 16, 0, 70, 0, 74, 24, 15, 0, 12, 2, 80, 0, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 11, 13, 1, 0, 65, 0, 6, 33, 16, 33, 15, 17, 0, 0, 13, 0, 33, 13, 17, 19, 0, 128, 0, 33, 6, 69, 18, 0, 0, 15, 14, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 15, 11, 0, 2, 17, 18, 0, 128, 0, 33, 4, 64, 7, 7, 2, 3, 4, 1, 3, 1, 22, 22, 1, 0, 4, 32, 2, 32, 3, 16, 0, 0, 131, 0, 19, 2, 0, 1, 1, 4, 74, 2, 3, 0, 2, 1, 66, 0, 1, 0, 65, 0, 0, 64, 8, 24, 3, 3, 2, 1, 3, 1, 8, 0, 1, 16, 0, 0, 131, 0, 71, 1, 0, 7, 2, 1, 1, 0, 65, 0, 0, 64, 98, 37, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 99, 38, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64]

def mutateCharonNativeLocal0ToUsizeIn67 (bs : List WireBody) : List WireBody :=
  bs.map (fun b =>
    if b.symId == 67 then
      match b.localTypes with
      | _ :: rest => { b with localTypes := .usize :: rest }
      | [] => b
    else b)

def getLocalTypeAtQ6 : List MirTypeTag → Nat → Option MirTypeTag
  | [], _ => none
  | t :: _, 0 => some t
  | _ :: ts, n + 1 => getLocalTypeAtQ6 ts n

/-- Enforceable Charon adapter domain validator (`Q6` / `F6`, `#93` §11):
    Verifies that the ULLBC-extracted local type tags on `symId = 67` (`inspect_and_commit_slot`),
    `symId = 63` (`step_generic_slot`), `symId = 65` (`transactional_step`), and `symId = 24`
    (`core::mem::drop::<Guard>`) match the declared 32-bit `u32` / `usize` / `Guard` domain. -/
def checkCharonNativeInspectorDomainTypesQ6 (bodies : List WireBody) : Bool :=
  match findBodyBySym bodies 67, findBodyBySym bodies 63, findBodyBySym bodies 65, findBodyBySym bodies 24 with
  | some b67, some b63, some b65, some b24 =>
      (getLocalTypeAtQ6 b67.localTypes 0 == some .u32) &&
      (getLocalTypeAtQ6 b67.localTypes 3 == some .rawPtrU32) &&
      (getLocalTypeAtQ6 b67.localTypes 5 == some .usize) &&
      (getLocalTypeAtQ6 b67.localTypes 8 == some .u32) &&
      (getLocalTypeAtQ6 b63.localTypes 0 == some .usize) &&
      (getLocalTypeAtQ6 b65.localTypes 0 == some .u32) &&
      (b24.localTypes == [.unit, .guard])
  | _, _, _, _ => false

def verifyCharonNativeInspectorClosureQ6 (pkgBytes : List Nat) : Bool :=
  isAdmittedPackageBytes pkgBytes &&
  let bodies := decodePackageBodies pkgBytes
  checkRuntimeClosedBodies bodies &&
  checkCharonNativeInspectorDomainTypesQ6 bodies

theorem q6_ctrl6_decode :
    isAdmittedPackageBytes charonCtrl6LocalU64TypeMismatchAmirBytes = true ∧
    decodePackageBodies charonCtrl6LocalU64TypeMismatchAmirBytes =
      mutateCharonNativeLocal0ToUsizeIn67 charonNativeInspectorBodies ∧
    charonCtrl6LocalU64TypeMismatchAmirBytes ≠ charonNativeClientInspectorClosureAmirBytes := by
  decide

theorem q6_ctrl6_domain_check :
    verifyCharonNativeInspectorClosureQ6 charonNativeClientInspectorClosureAmirBytes = true ∧
    checkCharonNativeInspectorDomainTypesQ6 (mutateCharonNativeLocal0ToUsizeIn67 charonNativeInspectorBodies) = false ∧
    verifyCharonNativeInspectorClosureQ6 charonCtrl6LocalU64TypeMismatchAmirBytes = false := by
  decide

theorem q6_charon_adapter_domain_accepts_native_closure_and_rejects_local_u64_type_mismatch :
    verifyCharonNativeInspectorClosureQ6 charonNativeClientInspectorClosureAmirBytes = true ∧
    isAdmittedPackageBytes charonCtrl6LocalU64TypeMismatchAmirBytes = true ∧
    decodePackageBodies charonCtrl6LocalU64TypeMismatchAmirBytes =
      mutateCharonNativeLocal0ToUsizeIn67 charonNativeInspectorBodies ∧
    charonCtrl6LocalU64TypeMismatchAmirBytes ≠ charonNativeClientInspectorClosureAmirBytes ∧
    checkCharonNativeInspectorDomainTypesQ6 (decodePackageBodies charonCtrl6LocalU64TypeMismatchAmirBytes) = false ∧
    verifyCharonNativeInspectorClosureQ6 charonCtrl6LocalU64TypeMismatchAmirBytes = false := by
  have ⟨h1, h2, h3⟩ := q6_ctrl6_decode
  have ⟨h4, h5, h6⟩ := q6_ctrl6_domain_check
  rw [h2]
  exact ⟨h4, h1, rfl, h3, h5, h6⟩

#print axioms q6_charon_adapter_domain_accepts_native_closure_and_rejects_local_u64_type_mismatch

/-! ## 4. `C2` (`D4`, `#95` §5 `D4` & Companion §C): Complete 10-Body Local-Type Vector Gate & Rejection of `fun_decls[4]` (`EffectLog::record`) Local 2 Mutation -/

/-- Generated `.amir` v3 control from `portable_pr94_control.py`
    (`artifacts/charon_h3_ctrl7_unchecked_local_u64_mutant.amir`, `1,019` B, `fp16 = [74, 91]`,
    SHA-256 `5342601cf574a1aa4dbc93ed73857f63de8d54e9f6ef125506222e2b0922e66a`), produced by
    mutating `fun_decls[4]` (`EffectLog::record`, `symId = 1`), `local 2`, from `U32` to `U64`
    in the ULLBC AST when `strict_domain_check=False`. -/
def charonCtrl7UncheckedLocalMutantAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 74, 91, 10, 1, 67, 1, 3, 14, 4, 8, 3, 6, 6, 5, 2, 4, 6, 5, 3, 6, 6, 2, 2, 4, 0, 5, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 32, 7, 17, 7, 0, 3, 0, 76, 63, 5, 0, 2, 1, 70, 0, 71, 0, 130, 16, 1, 0, 65, 0, 9, 33, 7, 33, 6, 32, 8, 32, 9, 19, 9, 0, 1, 1, 4, 32, 10, 19, 10, 0, 1, 2, 4, 32, 11, 17, 11, 0, 4, 0, 76, 65, 8, 0, 4, 3, 73, 0, 74, 0, 75, 0, 1, 0, 65, 0, 7, 33, 11, 33, 10, 33, 9, 32, 12, 32, 13, 17, 13, 0, 5, 0, 21, 12, 0, 1, 77, 0, 130, 20, 69, 76, 0, 0, 6, 5, 0, 2, 33, 13, 17, 0, 0, 8, 0, 68, 7, 0, 2, 33, 13, 17, 0, 0, 129, 0, 68, 7, 0, 3, 33, 12, 33, 8, 33, 5, 64, 2, 1, 1, 3, 9, 2, 7, 1, 6, 4, 3, 3, 3, 3, 3, 3, 0, 4, 16, 0, 0, 131, 0, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 2, 1, 68, 0, 129, 1, 1, 0, 65, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 4, 3, 71, 0, 129, 16, 1, 0, 65, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 6, 5, 70, 0, 72, 0, 1, 0, 65, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 16, 0, 0, 131, 0, 64, 3, 2, 1, 3, 6, 1, 3, 1, 22, 1, 6, 3, 6, 0, 8, 32, 5, 16, 0, 0, 131, 0, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 2, 1, 67, 0, 68, 0, 1, 0, 65, 0, 4, 33, 4, 33, 3, 33, 2, 16, 0, 0, 131, 0, 64, 4, 3, 1, 3, 6, 2, 7, 3, 2, 3, 2, 19, 3, 0, 2, 32, 3, 17, 3, 0, 1, 0, 69, 67, 0, 0, 2, 1, 0, 1, 32, 4, 74, 26, 4, 0, 4, 3, 131, 2, 0, 3, 33, 3, 32, 5, 17, 5, 0, 2, 0, 75, 20, 0, 0, 6, 5, 69, 0, 129, 100, 1, 0, 65, 0, 0, 74, 27, 0, 0, 255, 3, 131, 2, 1, 0, 65, 0, 1, 33, 5, 64, 5, 63, 1, 3, 12, 3, 12, 4, 6, 5, 4, 4, 1, 6, 4, 4, 2, 4, 19, 0, 2, 32, 9, 32, 10, 73, 37, 10, 0, 8, 7, 1, 0, 65, 0, 3, 32, 5, 32, 6, 19, 6, 0, 1, 1, 4, 75, 1, 5, 0, 4, 3, 70, 0, 129, 4, 1, 0, 65, 0, 6, 33, 6, 33, 5, 32, 7, 17, 7, 0, 3, 0, 32, 8, 17, 8, 0, 4, 0, 75, 40, 0, 0, 6, 5, 71, 0, 72, 0, 1, 0, 65, 0, 3, 33, 8, 33, 7, 33, 4, 64, 0, 0, 67, 0, 1, 21, 9, 0, 5, 74, 0, 130, 0, 69, 73, 0, 0, 10, 9, 0, 4, 33, 10, 33, 9, 48, 2, 4, 32, 4, 73, 38, 4, 0, 2, 1, 0, 2, 33, 10, 32, 11, 74, 26, 11, 0, 11, 7, 131, 2, 0, 0, 74, 27, 0, 0, 255, 7, 131, 2, 6, 65, 1, 3, 20, 3, 16, 3, 6, 6, 2, 8, 6, 8, 6, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 19, 32, 17, 32, 18, 32, 19, 17, 18, 0, 128, 0, 17, 19, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 18, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 19, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 17, 8, 0, 3, 0, 69, 72, 0, 0, 4, 1, 0, 4, 32, 9, 32, 10, 16, 17, 0, 4, 2, 19, 10, 0, 1, 17, 4, 75, 1, 9, 0, 3, 2, 74, 0, 129, 10, 0, 0, 69, 19, 0, 0, 6, 5, 0, 6, 33, 10, 33, 9, 32, 11, 32, 12, 17, 18, 0, 128, 0, 17, 12, 0, 68, 0, 74, 24, 11, 0, 7, 2, 76, 0, 0, 4, 33, 8, 32, 13, 32, 14, 17, 14, 0, 3, 0, 75, 3, 13, 0, 8, 2, 78, 0, 129, 5, 0, 0, 71, 6, 0, 7, 6, 9, 0, 0, 69, 18, 0, 0, 11, 10, 0, 2, 33, 12, 33, 11, 68, 4, 0, 5, 33, 14, 32, 15, 32, 16, 17, 19, 0, 128, 0, 17, 16, 0, 70, 0, 74, 24, 15, 0, 12, 2, 80, 0, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 11, 13, 1, 0, 65, 0, 6, 33, 16, 33, 15, 17, 0, 0, 13, 0, 33, 13, 17, 19, 0, 128, 0, 33, 6, 69, 18, 0, 0, 15, 14, 1, 0, 66, 2, 0, 0, 71, 4, 0, 7, 15, 11, 0, 2, 17, 18, 0, 128, 0, 33, 4, 64, 7, 7, 2, 3, 4, 1, 3, 1, 22, 22, 1, 0, 4, 32, 2, 32, 3, 16, 0, 0, 131, 0, 19, 2, 0, 1, 1, 4, 74, 2, 3, 0, 2, 1, 66, 0, 1, 0, 65, 0, 0, 64, 8, 24, 3, 3, 2, 1, 3, 1, 8, 0, 1, 16, 0, 0, 131, 0, 71, 1, 0, 7, 2, 1, 1, 0, 65, 0, 0, 64, 98, 37, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64, 99, 38, 3, 4, 1, 0, 1, 4, 0, 1, 17, 0, 0, 130, 4, 64]

def mutateCharonNativeLocal2ToUsizeInSym1 (bs : List WireBody) : List WireBody :=
  bs.map (fun b =>
    if b.symId == 1 then
      match b.localTypes with
      | t0 :: t1 :: _ :: rest => { b with localTypes := t0 :: t1 :: .usize :: rest }
      | _ => b
    else b)

/-- Complete 10-body expected local-type vectors (`C2` / `D4`, `#95` §5 `D4`), matching
    `EXPECTED_H3_NATIVE_INSPECTOR_LOCAL_TYPES` in `extract_and_link_charon_h3.py:692–703`. -/
def checkCharonNativeInspectorAllBodyLocalTypesC2 (bodies : List WireBody) : Bool :=
  (bodies.length == 10) &&
  match findBodyBySym bodies 67, findBodyBySym bodies 1, findBodyBySym bodies 2,
        findBodyBySym bodies 3, findBodyBySym bodies 63, findBodyBySym bodies 65,
        findBodyBySym bodies 7, findBodyBySym bodies 24, findBodyBySym bodies 37,
        findBodyBySym bodies 38 with
  | some b67, some b1, some b2, some b3, some b63, some b65, some b7, some b24, some b37, some b38 =>
      (b67.localTypes == [.u32, .refMutEffectLog, .refMutEffectLog, .rawPtrU32, .bool, .usize,
        .refMutEffectLog, .rawPtrU32, .u32, .refMutEffectLog, .refMutEffectLog, .bool, .bool, .usize]) &&
      (b1.localTypes == [.unit, .refMutEffectLog, .u32, .u32, .u32, .u32, .u32, .u32, .u32]) &&
      (b2.localTypes == [.unit, .refGuard, .unit, .refMutEffectLog, .u32, .refMutEffectLog]) &&
      (b3.localTypes == [.u32, .bool, .u32, .bool, .panicOrNever, .u32]) &&
      (b63.localTypes == [.usize, .refMutEffectLog, .rawPtrU32, .usize, .usize, .unit, .refMutEffectLog,
        .usize, .usize, .bool, .usize, .panicOrNever]) &&
      (b65.localTypes == [.u32, .refMutEffectLog, .refMutEffectLog, .bool, .guard, .refMutEffectLog,
        .guard, .refMutEffectLog, .bool, .unit, .refMutEffectLog, .unit, .guard, .u32, .bool,
        .unit, .guard, .refMutEffectLog, .bool, .bool]) &&
      (b7.localTypes == [.unit, .refGuard, .refGuard, .unit]) &&
      (b24.localTypes == [.unit, .guard]) &&
      (b37.localTypes == [.usize]) &&
      (b38.localTypes == [.usize])
  | _, _, _, _, _, _, _, _, _, _ => false

/-- Repaired complete-vector Charon native inspector closure validator (`C2` / `D4`, `#95` §5 `D4`):
    Enforces full package admission (`isAdmittedPackageBytes`), runtime closure (`checkRuntimeClosedBodies`),
    and complete 10-body local-type vector agreement (`checkCharonNativeInspectorAllBodyLocalTypesC2`). -/
def verifyCharonNativeInspectorClosureCompleteC2 (pkgBytes : List Nat) : Bool :=
  isAdmittedPackageBytes pkgBytes &&
  let bodies := decodePackageBodies pkgBytes
  checkRuntimeClosedBodies bodies &&
  checkCharonNativeInspectorAllBodyLocalTypesC2 bodies

theorem c2_d4_ctrl7_decode :
    isAdmittedPackageBytes charonCtrl7UncheckedLocalMutantAmirBytes = true ∧
    decodePackageBodies charonCtrl7UncheckedLocalMutantAmirBytes =
      mutateCharonNativeLocal2ToUsizeInSym1 charonNativeInspectorBodies ∧
    charonCtrl7UncheckedLocalMutantAmirBytes ≠ charonNativeClientInspectorClosureAmirBytes := by
  decide

theorem c2_d4_complete_domain_check :
    verifyCharonNativeInspectorClosureCompleteC2 charonNativeClientInspectorClosureAmirBytes = true ∧
    verifyCharonNativeInspectorClosureCompleteC2 charonCtrl6LocalU64TypeMismatchAmirBytes = false ∧
    verifyCharonNativeInspectorClosureCompleteC2 charonCtrl7UncheckedLocalMutantAmirBytes = false ∧
    verifyCharonNativeInspectorClosureQ6 charonCtrl7UncheckedLocalMutantAmirBytes = true := by
  decide

theorem c2_d4_complete_charon_local_domain_gate_rejects_both_ctrl6_and_ctrl7_unchecked_local_mutant :
    verifyCharonNativeInspectorClosureCompleteC2 charonNativeClientInspectorClosureAmirBytes = true ∧
    isAdmittedPackageBytes charonCtrl7UncheckedLocalMutantAmirBytes = true ∧
    decodePackageBodies charonCtrl7UncheckedLocalMutantAmirBytes =
      mutateCharonNativeLocal2ToUsizeInSym1 charonNativeInspectorBodies ∧
    charonCtrl7UncheckedLocalMutantAmirBytes ≠ charonNativeClientInspectorClosureAmirBytes ∧
    verifyCharonNativeInspectorClosureQ6 charonCtrl7UncheckedLocalMutantAmirBytes = true ∧
    verifyCharonNativeInspectorClosureCompleteC2 charonCtrl6LocalU64TypeMismatchAmirBytes = false ∧
    verifyCharonNativeInspectorClosureCompleteC2 charonCtrl7UncheckedLocalMutantAmirBytes = false := by
  have ⟨h1, h2, h3⟩ := c2_d4_ctrl7_decode
  have ⟨h4, h5, h6, h7⟩ := c2_d4_complete_domain_check
  exact ⟨h4, h1, h2, h3, h7, h5, h6⟩

#print axioms c2_d4_complete_charon_local_domain_gate_rejects_both_ctrl6_and_ctrl7_unchecked_local_mutant

end AnnealResearch.CharonNativeAndControlsR3R4
