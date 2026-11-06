import AnnealResearch.PR86AuditRepairs

set_option Elab.async false
set_option maxRecDepth 131072
set_option maxHeartbeats 1600000

namespace AnnealResearch.BuiltPhaseControlsR1

open AnnealResearch.SubstantiveMirByteParser
open AnnealResearch.SemanticVerticalSlice
open AnnealResearch.CargoWorkspaceIntegration
open AnnealResearch.StatefulGenericLibraryH3H7
open AnnealResearch.StatefulGenericLibraryH3H7Controls
open AnnealResearch.PR86AuditRepairs

/-!
# `R1` (`U1`, `#89` §8): Parser-Translated `MirPhase::Built` Controls (`extract_and_link_charon_h3.py`)

Verifies all 5 parser-generated `.amir` v3 control artifacts (`r1BuiltEvent9AmirBytes`,
`r1BuiltSwappedDropAmirBytes`, `r1BuiltDeletedPlaceMentionAmirBytes`,
`r1PostCleanupWrongCfgAmirBytes`, and `r1BuiltAdminNopAmirBytes`) produced by
`parse_built_body_from_rustc_json` in `extract_and_link_charon_h3.py`.
-/

def r1BuiltEvent9AmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 1, 11, 236, 169, 8, 1, 1, 1, 1, 9, 2, 5, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 4, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 4, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 4, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 1, 0, 65, 2, 2, 1, 1, 5, 1, 3, 1, 22, 1, 6, 3, 0, 5, 32, 2, 32, 3, 19, 3, 0, 1, 1, 6, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 2, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 1, 0, 65, 3, 3, 1, 1, 10, 2, 6, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 5, 131, 2, 0, 0, 74, 27, 7, 0, 255, 5, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 5, 73, 0, 129, 100, 0, 1, 33, 9, 64, 1, 0, 65, 4, 63, 1, 1, 10, 3, 5, 4, 6, 5, 4, 1, 4, 1, 6, 4, 4, 0, 5, 32, 4, 17, 4, 0, 131, 0, 33, 4, 48, 2, 4, 32, 5, 73, 38, 5, 0, 1, 4, 0, 4, 34, 32, 6, 32, 7, 19, 7, 0, 1, 1, 4, 75, 1, 6, 0, 2, 4, 71, 0, 129, 9, 0, 6, 33, 7, 33, 6, 32, 8, 17, 8, 0, 3, 0, 32, 9, 17, 9, 0, 5, 0, 75, 40, 0, 0, 3, 4, 72, 0, 73, 0, 0, 3, 33, 9, 33, 8, 33, 5, 64, 1, 0, 65, 5, 64, 1, 1, 7, 3, 3, 4, 6, 5, 4, 6, 5, 4, 0, 6, 32, 4, 19, 4, 0, 1, 1, 4, 32, 5, 17, 5, 0, 2, 0, 32, 6, 17, 6, 0, 3, 0, 76, 63, 0, 0, 1, 2, 68, 0, 69, 0, 70, 0, 0, 3, 33, 6, 33, 5, 33, 4, 64, 1, 0, 65, 6, 65, 1, 1, 18, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 1, 6, 1, 8, 3, 2, 1, 8, 0, 15, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 34, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 34, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 3, 32, 10, 32, 11, 19, 11, 0, 1, 4, 2, 75, 1, 10, 0, 2, 12, 75, 0, 129, 10, 0, 5, 33, 11, 33, 10, 32, 12, 32, 13, 17, 13, 0, 68, 0, 74, 24, 12, 0, 3, 11, 77, 0, 0, 3, 33, 13, 33, 12, 17, 8, 0, 131, 0, 68, 5, 0, 1, 17, 8, 0, 131, 0, 68, 5, 0, 5, 33, 9, 33, 8, 32, 14, 32, 15, 17, 15, 0, 3, 0, 75, 3, 14, 0, 6, 12, 79, 0, 129, 5, 0, 5, 33, 15, 34, 32, 16, 32, 17, 17, 17, 0, 70, 0, 74, 24, 16, 0, 7, 10, 81, 0, 0, 4, 33, 17, 33, 16, 17, 0, 0, 14, 0, 33, 14, 71, 6, 0, 7, 8, 13, 0, 1, 33, 6, 71, 4, 0, 7, 9, 14, 0, 1, 33, 4, 64, 1, 0, 71, 17, 0, 7, 12, 255, 1, 0, 71, 13, 0, 7, 12, 255, 1, 0, 71, 6, 0, 7, 13, 255, 1, 0, 71, 4, 0, 7, 14, 255, 1, 0, 65, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

def r1BuiltSwappedDropAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 1, 11, 174, 62, 8, 1, 1, 1, 1, 9, 2, 5, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 4, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 4, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 4, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 1, 0, 65, 2, 2, 1, 1, 5, 1, 3, 1, 22, 1, 6, 3, 0, 5, 32, 2, 32, 3, 19, 3, 0, 1, 1, 6, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 2, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 1, 0, 65, 3, 3, 1, 1, 10, 2, 6, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 5, 131, 2, 0, 0, 74, 27, 7, 0, 255, 5, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 5, 73, 0, 129, 100, 0, 1, 33, 9, 64, 1, 0, 65, 4, 63, 1, 1, 10, 3, 5, 4, 6, 5, 4, 1, 4, 1, 6, 4, 4, 0, 5, 32, 4, 17, 4, 0, 131, 0, 33, 4, 48, 2, 4, 32, 5, 73, 38, 5, 0, 1, 4, 0, 4, 34, 32, 6, 32, 7, 19, 7, 0, 1, 1, 4, 75, 1, 6, 0, 2, 4, 71, 0, 129, 4, 0, 6, 33, 7, 33, 6, 32, 8, 17, 8, 0, 3, 0, 32, 9, 17, 9, 0, 5, 0, 75, 40, 0, 0, 3, 4, 72, 0, 73, 0, 0, 3, 33, 9, 33, 8, 33, 5, 64, 1, 0, 65, 5, 64, 1, 1, 7, 3, 3, 4, 6, 5, 4, 6, 5, 4, 0, 6, 32, 4, 19, 4, 0, 1, 1, 4, 32, 5, 17, 5, 0, 2, 0, 32, 6, 17, 6, 0, 3, 0, 76, 63, 0, 0, 1, 2, 68, 0, 69, 0, 70, 0, 0, 3, 33, 6, 33, 5, 33, 4, 64, 1, 0, 65, 6, 65, 1, 1, 18, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 1, 6, 1, 8, 3, 2, 1, 8, 0, 15, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 34, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 34, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 3, 32, 10, 32, 11, 19, 11, 0, 1, 4, 2, 75, 1, 10, 0, 2, 12, 75, 0, 129, 10, 0, 5, 33, 11, 33, 10, 32, 12, 32, 13, 17, 13, 0, 68, 0, 74, 24, 12, 0, 3, 11, 77, 0, 0, 3, 33, 13, 33, 12, 17, 8, 0, 131, 0, 68, 5, 0, 1, 17, 8, 0, 131, 0, 68, 5, 0, 5, 33, 9, 33, 8, 32, 14, 32, 15, 17, 15, 0, 3, 0, 75, 3, 14, 0, 6, 12, 79, 0, 129, 5, 0, 5, 33, 15, 34, 32, 16, 32, 17, 17, 17, 0, 68, 0, 74, 24, 16, 0, 7, 10, 81, 0, 0, 4, 33, 17, 33, 16, 17, 0, 0, 14, 0, 33, 14, 71, 6, 0, 7, 8, 13, 0, 1, 33, 6, 71, 4, 0, 7, 9, 14, 0, 1, 33, 4, 64, 1, 0, 71, 17, 0, 7, 12, 255, 1, 0, 71, 13, 0, 7, 12, 255, 1, 0, 71, 6, 0, 7, 13, 255, 1, 0, 71, 4, 0, 7, 14, 255, 1, 0, 65, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

def r1BuiltDeletedPlaceMentionAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 1, 11, 252, 46, 8, 1, 1, 1, 1, 9, 2, 5, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 4, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 4, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 4, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 1, 0, 65, 2, 2, 1, 1, 5, 1, 3, 1, 22, 1, 6, 3, 0, 5, 32, 2, 32, 3, 19, 3, 0, 1, 1, 6, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 2, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 1, 0, 65, 3, 3, 1, 1, 10, 2, 6, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 5, 131, 2, 0, 0, 74, 27, 7, 0, 255, 5, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 5, 73, 0, 129, 100, 0, 1, 33, 9, 64, 1, 0, 65, 4, 63, 1, 1, 10, 3, 5, 4, 6, 5, 4, 1, 4, 1, 6, 4, 4, 0, 5, 32, 4, 17, 4, 0, 131, 0, 33, 4, 32, 4, 32, 5, 73, 38, 5, 0, 1, 4, 0, 4, 34, 32, 6, 32, 7, 19, 7, 0, 1, 1, 4, 75, 1, 6, 0, 2, 4, 71, 0, 129, 4, 0, 6, 33, 7, 33, 6, 32, 8, 17, 8, 0, 3, 0, 32, 9, 17, 9, 0, 5, 0, 75, 40, 0, 0, 3, 4, 72, 0, 73, 0, 0, 3, 33, 9, 33, 8, 33, 5, 64, 1, 0, 65, 5, 64, 1, 1, 7, 3, 3, 4, 6, 5, 4, 6, 5, 4, 0, 6, 32, 4, 19, 4, 0, 1, 1, 4, 32, 5, 17, 5, 0, 2, 0, 32, 6, 17, 6, 0, 3, 0, 76, 63, 0, 0, 1, 2, 68, 0, 69, 0, 70, 0, 0, 3, 33, 6, 33, 5, 33, 4, 64, 1, 0, 65, 6, 65, 1, 1, 18, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 1, 6, 1, 8, 3, 2, 1, 8, 0, 15, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 34, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 34, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 3, 32, 10, 32, 11, 19, 11, 0, 1, 4, 2, 75, 1, 10, 0, 2, 12, 75, 0, 129, 10, 0, 5, 33, 11, 33, 10, 32, 12, 32, 13, 17, 13, 0, 68, 0, 74, 24, 12, 0, 3, 11, 77, 0, 0, 3, 33, 13, 33, 12, 17, 8, 0, 131, 0, 68, 5, 0, 1, 17, 8, 0, 131, 0, 68, 5, 0, 5, 33, 9, 33, 8, 32, 14, 32, 15, 17, 15, 0, 3, 0, 75, 3, 14, 0, 6, 12, 79, 0, 129, 5, 0, 5, 33, 15, 34, 32, 16, 32, 17, 17, 17, 0, 70, 0, 74, 24, 16, 0, 7, 10, 81, 0, 0, 4, 33, 17, 33, 16, 17, 0, 0, 14, 0, 33, 14, 71, 6, 0, 7, 8, 13, 0, 1, 33, 6, 71, 4, 0, 7, 9, 14, 0, 1, 33, 4, 64, 1, 0, 71, 17, 0, 7, 12, 255, 1, 0, 71, 13, 0, 7, 12, 255, 1, 0, 71, 6, 0, 7, 13, 255, 1, 0, 71, 4, 0, 7, 14, 255, 1, 0, 65, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

def r1PostCleanupWrongCfgAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 9, 61, 171, 8, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 3, 1, 3, 10, 2, 5, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 252, 131, 2, 0, 0, 74, 27, 7, 0, 255, 252, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 252, 73, 0, 129, 100, 0, 1, 33, 9, 64, 4, 63, 1, 3, 10, 3, 4, 4, 6, 5, 4, 1, 4, 1, 6, 4, 4, 0, 4, 32, 4, 17, 4, 0, 131, 0, 33, 4, 32, 5, 73, 38, 5, 0, 1, 252, 0, 3, 32, 6, 32, 7, 19, 7, 0, 1, 1, 4, 75, 1, 6, 0, 2, 252, 71, 0, 129, 4, 0, 6, 33, 7, 33, 6, 32, 8, 17, 8, 0, 3, 0, 32, 9, 17, 9, 0, 5, 0, 75, 40, 0, 0, 3, 252, 72, 0, 73, 0, 0, 3, 33, 9, 33, 8, 33, 5, 64, 5, 64, 1, 3, 7, 3, 2, 4, 6, 5, 4, 6, 5, 4, 0, 6, 32, 4, 19, 4, 0, 1, 1, 4, 32, 5, 17, 5, 0, 2, 0, 32, 6, 17, 6, 0, 3, 0, 76, 63, 0, 0, 1, 252, 68, 0, 69, 0, 70, 0, 0, 3, 33, 6, 33, 5, 33, 4, 64, 6, 65, 1, 3, 21, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 1, 6, 1, 8, 3, 2, 1, 8, 6, 2, 2, 0, 17, 17, 19, 0, 128, 0, 17, 20, 0, 128, 0, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 17, 19, 0, 128, 1, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 17, 20, 0, 128, 1, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 4, 32, 10, 32, 11, 16, 18, 0, 4, 2, 19, 11, 0, 1, 18, 4, 75, 1, 10, 0, 2, 13, 75, 0, 129, 10, 0, 6, 33, 11, 33, 10, 32, 12, 32, 13, 17, 19, 0, 128, 0, 17, 13, 0, 68, 0, 74, 24, 12, 0, 3, 13, 77, 0, 0, 3, 33, 13, 33, 12, 17, 8, 0, 131, 0, 68, 5, 0, 1, 17, 8, 0, 131, 0, 68, 5, 0, 5, 33, 9, 33, 8, 32, 14, 32, 15, 17, 15, 0, 3, 0, 75, 3, 14, 0, 6, 13, 79, 0, 129, 5, 0, 5, 33, 15, 32, 16, 32, 17, 17, 20, 0, 128, 0, 17, 17, 0, 70, 0, 74, 24, 16, 0, 7, 13, 81, 0, 0, 6, 33, 17, 33, 16, 17, 0, 0, 14, 0, 33, 14, 17, 20, 0, 128, 0, 33, 6, 69, 19, 0, 0, 8, 11, 0, 2, 17, 19, 0, 128, 0, 33, 4, 64, 1, 0, 69, 19, 0, 0, 10, 14, 1, 0, 65, 0, 0, 71, 4, 0, 7, 8, 10, 1, 0, 71, 6, 0, 7, 9, 255, 1, 0, 69, 20, 0, 0, 9, 12, 1, 0, 71, 4, 0, 7, 10, 255, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

def r1BuiltAdminNopAmirBytes : List Nat :=
  [65, 77, 73, 82, 3, 1, 11, 49, 103, 8, 1, 1, 1, 1, 9, 2, 5, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 4, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 4, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 4, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 1, 0, 65, 2, 2, 1, 1, 5, 1, 3, 1, 22, 1, 6, 3, 0, 5, 32, 2, 32, 3, 19, 3, 0, 1, 1, 6, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 2, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 1, 0, 65, 3, 3, 1, 1, 10, 2, 6, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 5, 131, 2, 0, 0, 74, 27, 7, 0, 255, 5, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 5, 73, 0, 129, 100, 0, 1, 33, 9, 64, 1, 0, 65, 4, 63, 1, 1, 10, 3, 5, 4, 6, 5, 4, 1, 4, 1, 6, 4, 4, 0, 5, 32, 4, 17, 4, 0, 131, 0, 33, 4, 48, 2, 4, 32, 5, 73, 38, 5, 0, 1, 4, 0, 4, 34, 32, 6, 32, 7, 19, 7, 0, 1, 1, 4, 75, 1, 6, 0, 2, 4, 71, 0, 129, 4, 0, 6, 33, 7, 33, 6, 32, 8, 17, 8, 0, 3, 0, 32, 9, 17, 9, 0, 5, 0, 75, 40, 0, 0, 3, 4, 72, 0, 73, 0, 0, 3, 33, 9, 33, 8, 33, 5, 64, 1, 0, 65, 5, 64, 1, 1, 7, 3, 3, 4, 6, 5, 4, 6, 5, 4, 0, 6, 32, 4, 19, 4, 0, 1, 1, 4, 32, 5, 17, 5, 0, 2, 0, 32, 6, 17, 6, 0, 3, 0, 76, 63, 0, 0, 1, 2, 68, 0, 69, 0, 70, 0, 0, 3, 33, 6, 33, 5, 33, 4, 64, 1, 0, 65, 6, 65, 1, 1, 18, 3, 15, 3, 6, 6, 2, 8, 6, 8, 6, 1, 2, 1, 6, 1, 8, 3, 2, 1, 8, 0, 15, 32, 4, 32, 5, 19, 5, 0, 1, 1, 4, 25, 4, 0, 1, 129, 1, 69, 0, 33, 5, 34, 32, 6, 32, 7, 19, 7, 0, 1, 2, 4, 25, 6, 0, 1, 129, 2, 71, 0, 33, 7, 34, 32, 8, 32, 9, 17, 9, 0, 3, 0, 69, 73, 0, 0, 4, 1, 0, 3, 32, 10, 32, 11, 19, 11, 0, 1, 4, 2, 75, 1, 10, 0, 2, 12, 75, 0, 129, 10, 0, 5, 33, 11, 33, 10, 32, 12, 32, 13, 17, 13, 0, 68, 0, 74, 24, 12, 0, 3, 11, 77, 0, 0, 3, 33, 13, 33, 12, 17, 8, 0, 131, 0, 68, 5, 0, 2, 34, 17, 8, 0, 131, 0, 68, 5, 0, 5, 33, 9, 33, 8, 32, 14, 32, 15, 17, 15, 0, 3, 0, 75, 3, 14, 0, 6, 12, 79, 0, 129, 5, 0, 5, 33, 15, 34, 32, 16, 32, 17, 17, 17, 0, 70, 0, 74, 24, 16, 0, 7, 10, 81, 0, 0, 4, 33, 17, 33, 16, 17, 0, 0, 14, 0, 33, 14, 71, 6, 0, 7, 8, 13, 0, 1, 33, 6, 71, 4, 0, 7, 9, 14, 0, 1, 33, 4, 64, 1, 0, 71, 17, 0, 7, 12, 255, 1, 0, 71, 13, 0, 7, 12, 255, 1, 0, 71, 6, 0, 7, 13, 255, 1, 0, 71, 4, 0, 7, 14, 255, 1, 0, 65, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

def r1BuiltEvent9BindingRec : CargoInvocationBindingRecord :=
  { statefulGenericLibBuiltBindingRec with expectedFp16 := (236, 169) }

def r1BuiltSwappedDropBindingRec : CargoInvocationBindingRecord :=
  { statefulGenericLibBuiltBindingRec with expectedFp16 := (174, 62) }

def r1BuiltDeletedPlaceMentionBindingRec : CargoInvocationBindingRecord :=
  { statefulGenericLibBuiltBindingRec with expectedFp16 := (252, 46) }

def r1PostCleanupWrongCfgRealBindingRec : CargoInvocationBindingRecord :=
  { statefulGenericLibBindingRec with
    cfgFlags := ["wrong_cfg_probe"]
    preserveUb := false
    svhFingerprintLo := 14553614784242614353
    expectedFp16 := (61, 171) }

def r1BuiltAdminNopBindingRec : CargoInvocationBindingRecord :=
  { statefulGenericLibBuiltBindingRec with expectedFp16 := (49, 103) }

theorem r1_ctrl1_built_event9_verified :
    isAdmittedPackageBytes r1BuiltEvent9AmirBytes = true ∧
    r1BuiltEvent9AmirBytes ≠ realStatefulGenericLibBuiltAmirBytes ∧
    evalBuiltStepGenericSlotFromGraph (decodePackageBodies r1BuiltEvent9AmirBytes ++ u32LayoutCalleeBodies) 0 0 true 16 =
      (.returned (.scalar 20), { stepCount := 1, traceAcc := 9 }, [9]) ∧
    validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      r1BuiltEvent9BindingRec statefulGenericLibBindingRec
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      r1BuiltEvent9AmirBytes realStatefulGenericLibAmirBytes
      statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false := by
  decide

theorem r1_ctrl2_built_swapped_drop_verified :
    isAdmittedPackageBytes r1BuiltSwappedDropAmirBytes = true ∧
    evalBuiltTransactionalStepFromGraph (decodePackageBodies r1BuiltSwappedDropAmirBytes ++ u32LayoutCalleeBodies) false =
      .normalReturn 105 (1, 1) (1, 2) [1, 2] ∧
    validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      r1BuiltSwappedDropBindingRec statefulGenericLibBindingRec
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      r1BuiltSwappedDropAmirBytes realStatefulGenericLibAmirBytes
      statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false := by
  decide

theorem r1_ctrl3_built_deleted_place_mention_verified :
    isAdmittedPackageBytes r1BuiltDeletedPlaceMentionAmirBytes = true ∧
    evalBuiltStepGenericSlotFromGraph (decodePackageBodies r1BuiltDeletedPlaceMentionAmirBytes ++ u32LayoutCalleeBodies) 0 0 false 16 =
      (.returned (.scalar 20), { stepCount := 1, traceAcc := 4 }, [4]) ∧
    validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      r1BuiltDeletedPlaceMentionBindingRec statefulGenericLibBindingRec
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      r1BuiltDeletedPlaceMentionAmirBytes realStatefulGenericLibAmirBytes
      statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false := by
  decide

theorem r1_ctrl4_postcleanup_wrong_cfg_verified :
    isAdmittedPackageBytes r1PostCleanupWrongCfgAmirBytes = true ∧
    checkTwoPhaseCompilationIdentity statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec r1PostCleanupWrongCfgRealBindingRec statefulGenericLibCrateBytes
      realStatefulGenericLibBuiltAmirBytes r1PostCleanupWrongCfgAmirBytes statefulGenericLibLayoutTable = false ∧
    validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      statefulGenericLibBuiltBindingRec r1PostCleanupWrongCfgRealBindingRec
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      realStatefulGenericLibBuiltAmirBytes r1PostCleanupWrongCfgAmirBytes
      statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false := by
  decide

theorem r1_ctrl5_built_admin_nop_verified :
    isAdmittedPackageBytes r1BuiltAdminNopAmirBytes = true ∧
    r1BuiltAdminNopAmirBytes ≠ realStatefulGenericLibBuiltAmirBytes ∧
    validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
      r1BuiltAdminNopBindingRec statefulGenericLibBindingRec
      statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
      r1BuiltAdminNopAmirBytes realStatefulGenericLibAmirBytes
      statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = true := by
  decide

theorem r1_all_five_parsed_built_phase_controls_verified :
    (isAdmittedPackageBytes r1BuiltEvent9AmirBytes = true ∧
     r1BuiltEvent9AmirBytes ≠ realStatefulGenericLibBuiltAmirBytes ∧
     evalBuiltStepGenericSlotFromGraph (decodePackageBodies r1BuiltEvent9AmirBytes ++ u32LayoutCalleeBodies) 0 0 true 16 =
       (.returned (.scalar 20), { stepCount := 1, traceAcc := 9 }, [9]) ∧
     validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
       r1BuiltEvent9BindingRec statefulGenericLibBindingRec
       statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
       r1BuiltEvent9AmirBytes realStatefulGenericLibAmirBytes
       statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false) ∧
    (isAdmittedPackageBytes r1BuiltSwappedDropAmirBytes = true ∧
     evalBuiltTransactionalStepFromGraph (decodePackageBodies r1BuiltSwappedDropAmirBytes ++ u32LayoutCalleeBodies) false =
       .normalReturn 105 (1, 1) (1, 2) [1, 2] ∧
     validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
       r1BuiltSwappedDropBindingRec statefulGenericLibBindingRec
       statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
       r1BuiltSwappedDropAmirBytes realStatefulGenericLibAmirBytes
       statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false) ∧
    (isAdmittedPackageBytes r1BuiltDeletedPlaceMentionAmirBytes = true ∧
     evalBuiltStepGenericSlotFromGraph (decodePackageBodies r1BuiltDeletedPlaceMentionAmirBytes ++ u32LayoutCalleeBodies) 0 0 false 16 =
       (.returned (.scalar 20), { stepCount := 1, traceAcc := 4 }, [4]) ∧
     validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
       r1BuiltDeletedPlaceMentionBindingRec statefulGenericLibBindingRec
       statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
       r1BuiltDeletedPlaceMentionAmirBytes realStatefulGenericLibAmirBytes
       statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false) ∧
    (isAdmittedPackageBytes r1PostCleanupWrongCfgAmirBytes = true ∧
     checkTwoPhaseCompilationIdentity statefulGenericLibExpectedCtx
       statefulGenericLibBuiltBindingRec r1PostCleanupWrongCfgRealBindingRec statefulGenericLibCrateBytes
       realStatefulGenericLibBuiltAmirBytes r1PostCleanupWrongCfgAmirBytes statefulGenericLibLayoutTable = false ∧
     validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
       statefulGenericLibBuiltBindingRec r1PostCleanupWrongCfgRealBindingRec
       statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
       realStatefulGenericLibBuiltAmirBytes r1PostCleanupWrongCfgAmirBytes
       statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = false) ∧
    (isAdmittedPackageBytes r1BuiltAdminNopAmirBytes = true ∧
     r1BuiltAdminNopAmirBytes ≠ realStatefulGenericLibBuiltAmirBytes ∧
     validateBuiltToPostCleanupFailClosed .strictPrefixTracePreserving statefulGenericLibExpectedCtx
       r1BuiltAdminNopBindingRec statefulGenericLibBindingRec
       statefulGenericLibCrateBytes x86_64LinuxTargetTripleBytes statefulGenericLibEntriesFp16
       r1BuiltAdminNopAmirBytes realStatefulGenericLibAmirBytes
       statefulGenericLibLayoutTable x86_64LinuxTargetTripleBytes = true) :=
  ⟨r1_ctrl1_built_event9_verified,
   r1_ctrl2_built_swapped_drop_verified,
   r1_ctrl3_built_deleted_place_mention_verified,
   r1_ctrl4_postcleanup_wrong_cfg_verified,
   r1_ctrl5_built_admin_nop_verified⟩

#print axioms r1_all_five_parsed_built_phase_controls_verified

end AnnealResearch.BuiltPhaseControlsR1
