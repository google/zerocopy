/-
  Experiment: experiments/opsem/substantive-mir-byte-parser
  Task FD-02 (FE-F4) / Milestone C1 & R1 Controls:
  5-Boundary Separation, Exact 32-Block Bound vs. 33-Block Rejection,
  Package Admission Closure (Stage B2b), Payload Fingerprint Recomputation (Stage B3b),
  and Endorsed Compilation / Subject / Flag / Completion Binding Controls (Stage B3c).
-/

import AnnealResearch.SubstantiveMirByteParser

set_option autoImplicit false
set_option maxRecDepth 65536

namespace AnnealResearch.SubstantiveMirByteParserControls

open AnnealResearch.SubstantiveMirByteParser

/-! ## Exact 32-Block Positive Boundary vs. 33-Block Structural Rejection -/

def realLimit32PositiveBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 119, 60, 1, 1, 60, 1, 3, 41, 1, 32, 3, 3, 3, 1, 2, 3, 3, 3, 1, 2, 3, 3, 3, 1, 2, 3, 3, 3, 1, 2, 3, 3, 3, 1, 2, 3, 3, 3, 1, 2, 3, 3, 3, 1, 2, 3, 3, 3, 1, 2, 3, 0, 7, 32, 2, 17, 2, 0, 1, 0, 32, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 21, 4, 0, 1, 69, 0, 129, 0, 69, 68, 0, 0, 3, 1, 0, 4, 33, 5, 32, 6, 32, 7, 17, 7, 0, 2, 0, 75, 20, 6, 0, 2, 252, 71, 0, 129, 1, 0, 4, 33, 7, 17, 2, 0, 70, 0, 33, 6, 17, 3, 0, 131, 0, 68, 4, 0, 2, 33, 5, 17, 3, 0, 131, 0, 68, 4, 0, 7, 33, 4, 33, 3, 32, 8, 32, 9, 32, 10, 17, 10, 0, 2, 0, 21, 9, 0, 1, 74, 0, 129, 1, 69, 73, 0, 0, 7, 5, 0, 4, 33, 10, 32, 11, 32, 12, 17, 12, 0, 2, 0, 75, 20, 11, 0, 6, 252, 76, 0, 129, 1, 0, 4, 33, 12, 17, 2, 0, 75, 0, 33, 11, 17, 8, 0, 131, 0, 68, 8, 0, 2, 33, 10, 17, 8, 0, 131, 0, 68, 8, 0, 7, 33, 9, 33, 8, 32, 13, 32, 14, 32, 15, 17, 15, 0, 2, 0, 21, 14, 0, 1, 79, 0, 129, 2, 69, 78, 0, 0, 11, 9, 0, 4, 33, 15, 32, 16, 32, 17, 17, 17, 0, 2, 0, 75, 20, 16, 0, 10, 252, 81, 0, 129, 1, 0, 4, 33, 17, 17, 2, 0, 80, 0, 33, 16, 17, 13, 0, 131, 0, 68, 12, 0, 2, 33, 15, 17, 13, 0, 131, 0, 68, 12, 0, 7, 33, 14, 33, 13, 32, 18, 32, 19, 32, 20, 17, 20, 0, 2, 0, 21, 19, 0, 1, 84, 0, 129, 3, 69, 83, 0, 0, 15, 13, 0, 4, 33, 20, 32, 21, 32, 22, 17, 22, 0, 2, 0, 75, 20, 21, 0, 14, 252, 86, 0, 129, 1, 0, 4, 33, 22, 17, 2, 0, 85, 0, 33, 21, 17, 18, 0, 131, 0, 68, 16, 0, 2, 33, 20, 17, 18, 0, 131, 0, 68, 16, 0, 7, 33, 19, 33, 18, 32, 23, 32, 24, 32, 25, 17, 25, 0, 2, 0, 21, 24, 0, 1, 89, 0, 129, 4, 69, 88, 0, 0, 19, 17, 0, 4, 33, 25, 32, 26, 32, 27, 17, 27, 0, 2, 0, 75, 20, 26, 0, 18, 252, 91, 0, 129, 1, 0, 4, 33, 27, 17, 2, 0, 90, 0, 33, 26, 17, 23, 0, 131, 0, 68, 20, 0, 2, 33, 25, 17, 23, 0, 131, 0, 68, 20, 0, 7, 33, 24, 33, 23, 32, 28, 32, 29, 32, 30, 17, 30, 0, 2, 0, 21, 29, 0, 1, 94, 0, 129, 5, 69, 93, 0, 0, 23, 21, 0, 4, 33, 30, 32, 31, 32, 32, 17, 32, 0, 2, 0, 75, 20, 31, 0, 22, 252, 96, 0, 129, 1, 0, 4, 33, 32, 17, 2, 0, 95, 0, 33, 31, 17, 28, 0, 131, 0, 68, 24, 0, 2, 33, 30, 17, 28, 0, 131, 0, 68, 24, 0, 7, 33, 29, 33, 28, 32, 33, 32, 34, 32, 35, 17, 35, 0, 2, 0, 21, 34, 0, 1, 99, 0, 129, 6, 69, 98, 0, 0, 27, 25, 0, 4, 33, 35, 32, 36, 32, 37, 17, 37, 0, 2, 0, 75, 20, 36, 0, 26, 252, 101, 0, 129, 1, 0, 4, 33, 37, 17, 2, 0, 100, 0, 33, 36, 17, 33, 0, 131, 0, 68, 28, 0, 2, 33, 35, 17, 33, 0, 131, 0, 68, 28, 0, 7, 33, 34, 33, 33, 32, 38, 32, 39, 32, 40, 17, 40, 0, 2, 0, 21, 39, 0, 1, 104, 0, 129, 7, 69, 103, 0, 0, 30, 29, 0, 3, 33, 40, 17, 2, 0, 129, 8, 17, 38, 0, 131, 0, 68, 31, 0, 2, 33, 40, 17, 38, 0, 131, 0, 68, 31, 0, 4, 33, 39, 33, 38, 17, 0, 0, 2, 0, 33, 2, 64]

theorem real_limit_32_positive_bytes_accepted_at_exact_32_block_bound :
    acceptedPackageSummary realLimit32PositiveBytes =
      some { bodyCount := 1
            , preserveUb := true
            , bodies :=
              [ { symId := 60, originKind := .localOwner, mirPhase := .runtimePostCleanup, blockCount := 32, localCount := 41, hasDerefCopy := false, hasPlaceMention := false }
              ] } ∧
    isAdmittedPackageBytes realLimit32PositiveBytes = true := by
  refine ⟨rfl, rfl⟩

/-! ## Boundary 1 & Boundary 2 Negative Controls (`.amir` v3) -/

def realControlB1TruncatedBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 62, 110, 3, 1, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 3, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 2, 9, 1, 3, 6, 2, 4, 3, 5, 2, 1, 1, 2, 0, 7, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 3, 10, 1, 3, 4, 1, 1, 3, 5, 1, 1, 0, 8, 32, 2, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 17, 2, 0, 131, 0, 33, 2, 17, 0, 0, 129]

def realControlB1TrailingBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 62, 110, 3, 1, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 3, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 2, 9, 1, 3, 6, 2, 4, 3, 5, 2, 1, 1, 2, 0, 7, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 3, 10, 1, 3, 4, 1, 1, 3, 5, 1, 1, 0, 8, 32, 2, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 17, 2, 0, 131, 0, 33, 2, 17, 0, 0, 129, 0, 64, 153]

def realControlB1UnsupportedOpBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 62, 110, 3, 1, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 3, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 2, 9, 1, 3, 6, 2, 4, 3, 5, 2, 1, 1, 2, 0, 7, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 3, 10, 1, 3, 4, 1, 1, 3, 5, 1, 1, 0, 8, 32, 2, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 17, 2, 0, 131, 0, 33, 2, 17, 0, 0, 129, 0, 224]

def realControlB2OobLocalBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 62, 110, 3, 1, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 6, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 2, 9, 1, 3, 6, 2, 4, 3, 5, 2, 1, 1, 2, 0, 7, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 3, 10, 1, 3, 4, 1, 1, 3, 5, 1, 1, 0, 8, 32, 2, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 17, 2, 0, 131, 0, 33, 2, 17, 0, 0, 129, 0, 64]

def realControlB2DuplicateSymIdBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 62, 110, 3, 1, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 3, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 2, 6, 1, 3, 6, 2, 4, 3, 5, 2, 1, 1, 2, 0, 7, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 3, 10, 1, 3, 4, 1, 1, 3, 5, 1, 1, 0, 8, 32, 2, 32, 3, 48, 1, 4, 17, 3, 0, 131, 0, 33, 3, 17, 2, 0, 131, 0, 33, 2, 17, 0, 0, 129, 0, 64]

def realControlB2MissingRequiredBodyBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 167, 56, 8, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 3, 1, 3, 10, 2, 5, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 252, 131, 2, 0, 0, 74, 27, 7, 0, 255, 252, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 252, 73, 0, 129, 100, 0, 1, 33, 9, 64, 4, 4, 1, 3, 22, 4, 17, 3, 2, 2, 6, 6, 9, 8, 6, 8, 6, 1, 2, 8, 1, 6, 1, 8, 3, 2, 6, 2, 2, 0, 20, 17, 21, 0, 128, 0, 17, 20, 0, 128, 0, 32, 5, 32, 6, 32, 7, 19, 7, 0, 1, 3, 4, 25, 6, 0, 1, 129, 1, 71, 0, 33, 7, 32, 8, 32, 9, 19, 9, 0, 1, 4, 4, 25, 8, 0, 1, 129, 2, 73, 0, 33, 9, 17, 20, 0, 128, 1, 25, 5, 0, 2, 70, 0, 72, 0, 33, 8, 33, 6, 32, 10, 32, 11, 17, 11, 0, 1, 0, 69, 75, 0, 0, 4, 1, 0, 8, 32, 12, 17, 20, 0, 128, 0, 17, 21, 0, 128, 1, 17, 12, 0, 69, 1, 32, 13, 32, 14, 16, 19, 0, 12, 2, 19, 14, 0, 1, 19, 4, 75, 1, 13, 0, 2, 13, 78, 0, 129, 10, 0, 6, 33, 14, 33, 13, 32, 15, 32, 16, 17, 21, 0, 128, 0, 17, 16, 0, 76, 0, 74, 24, 15, 0, 3, 13, 80, 0, 0, 5, 33, 16, 33, 15, 17, 10, 0, 131, 0, 17, 21, 0, 128, 0, 33, 12, 68, 5, 0, 1, 17, 10, 0, 131, 0, 68, 5, 0, 5, 33, 11, 33, 10, 32, 17, 32, 18, 17, 18, 0, 2, 0, 75, 3, 17, 0, 6, 16, 82, 0, 129, 5, 0, 3, 33, 18, 17, 0, 0, 17, 0, 33, 17, 69, 20, 0, 0, 10, 11, 1, 0, 65, 0, 2, 17, 20, 0, 128, 0, 33, 5, 64, 1, 0, 71, 5, 2, 7, 7, 255, 0, 0, 71, 5, 2, 7, 8, 7, 0, 0, 71, 5, 1, 7, 10, 9, 1, 0, 71, 12, 0, 7, 16, 255, 1, 0, 69, 21, 0, 0, 16, 12, 1, 0, 71, 5, 2, 7, 7, 255, 1, 0, 71, 5, 1, 7, 14, 255, 1, 0, 69, 20, 0, 0, 14, 15, 5, 5, 1, 3, 24, 3, 9, 3, 2, 6, 6, 9, 8, 6, 8, 6, 8, 1, 6, 6, 1, 8, 3, 2, 8, 6, 6, 6, 6, 6, 2, 0, 22, 17, 23, 0, 128, 0, 32, 4, 32, 5, 32, 6, 19, 6, 0, 1, 2, 4, 25, 5, 0, 1, 129, 1, 70, 0, 33, 6, 32, 7, 32, 8, 19, 8, 0, 1, 3, 4, 25, 7, 0, 1, 129, 2, 72, 0, 33, 8, 25, 4, 0, 2, 69, 0, 71, 0, 33, 7, 33, 5, 32, 9, 17, 23, 0, 128, 1, 17, 9, 0, 68, 1, 32, 10, 32, 11, 16, 21, 0, 9, 2, 19, 11, 0, 1, 21, 4, 75, 1, 10, 0, 1, 8, 75, 0, 129, 10, 0, 9, 33, 11, 33, 10, 32, 12, 16, 22, 0, 9, 2, 19, 12, 0, 3, 22, 4, 32, 13, 32, 14, 17, 23, 0, 128, 0, 17, 14, 0, 73, 0, 74, 25, 13, 0, 2, 8, 78, 0, 0, 5, 33, 14, 33, 13, 32, 15, 32, 16, 17, 16, 0, 1, 0, 75, 3, 15, 0, 3, 8, 80, 0, 129, 7, 0, 19, 33, 16, 32, 17, 32, 18, 32, 19, 32, 20, 19, 20, 0, 1, 12, 4, 19, 19, 0, 1, 20, 4, 19, 18, 0, 1, 19, 4, 25, 17, 0, 1, 129, 3, 82, 0, 33, 18, 17, 4, 1, 81, 0, 33, 17, 33, 20, 33, 19, 17, 0, 0, 15, 0, 33, 15, 33, 12, 17, 23, 0, 128, 0, 33, 9, 71, 4, 0, 8, 4, 6, 0, 1, 33, 4, 64, 1, 0, 71, 4, 2, 7, 6, 255, 1, 0, 65, 1, 0, 71, 9, 0, 7, 5, 255, 1, 0, 69, 23, 0, 0, 5, 7, 6, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 3, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 8, 2, 4, 2, 1, 5, 1, 23, 0, 0, 71, 1, 5, 7, 4, 3, 1, 0, 65, 0, 0, 64, 1, 0, 71, 1, 6, 7, 1, 255, 0, 0, 71, 1, 6, 7, 2, 252]

/-- Boundary 1a: Non-physical byte (`256 > 255`) is rejected with `.rejectedNonPhysicalByte`. -/
theorem control_b1_non_physical_byte_rejected :
    parseWirePackage (256 :: realControlB1TruncatedBytes) = .rejectedNonPhysicalByte := by
  rfl

/-- Boundary 1b: Truncated byte stream (`control_b1_truncated.amir`, 192 bytes)
    is rejected with `.rejectedMalformedSyntax`. -/
theorem control_b1_truncated_rejected :
    parseWirePackage realControlB1TruncatedBytes = .rejectedMalformedSyntax := by
  rfl

/-- Boundary 1c: Trailing unconsumed byte (`control_b1_trailing.amir`, 195 bytes)
    is rejected with `.rejectedTrailingBytes 1`. -/
theorem control_b1_trailing_bytes_rejected :
    parseWirePackage realControlB1TrailingBytes = .rejectedTrailingBytes 1 := by
  rfl

/-- Boundary 1d: Valid byte framing containing an unsupported `InlineAsm` terminator
    tag (`0xE0 = 224` in `control_b1_unsupported_op.amir`) is rejected with
    `.rejectedUnsupportedFeature 224`. -/
theorem control_b1_unsupported_inline_asm_rejected :
    parseWirePackage realControlB1UnsupportedOpBytes = .rejectedUnsupportedFeature 224 := by
  rfl

/-- Boundary 2a: Structurally malformed body (`control_b2_oob_local.amir`, where
    `StorageLive(6)` has `6 <= 63` so Boundary 1 raw syntax framing succeeds with `rest = []`,
    but `6 >= localCount = 6` so Boundary 2a rejects it with `.rejectedIllFormedBody`). -/
theorem control_b2_out_of_bounds_local_rejected :
    (match parseRawPackageBytes realControlB2OobLocalBytes with
     | .ok (_, rest) => some rest.length
     | .error _ => none) = some 0 ∧
    parseWirePackage realControlB2OobLocalBytes = .rejectedIllFormedBody := by
  refine ⟨rfl, rfl⟩

/-- Boundary 2b Control 1 (Duplicate `symId`):
    `realControlB2DuplicateSymIdBytes` passes Boundary 1 raw syntax framing and Boundary 2a
    per-body well-formedness (`parseWirePackage` accepts it with `checkBodiesWellFormed = true`),
    but contains duplicate `symId = 6` across two bodies and is rejected at Boundary 2b
    (`isAdmittedPackageBytes = false`, `checkUniqueSymIds = false`). -/
theorem control_b2b_duplicate_sym_id_rejected :
    (match parseWirePackage realControlB2DuplicateSymIdBytes with
     | .accepted pkg => some (checkBodiesWellFormed pkg.bodies, checkUniqueSymIds pkg.bodies)
     | _ => none) = some (true, false) ∧
    isAdmittedPackageBytes realControlB2DuplicateSymIdBytes = false := by
  refine ⟨rfl, rfl⟩

/-- Boundary 2b Control 2 (Missing Required Callee/Drop-Glue Body):
    `realControlB2MissingRequiredBodyBytes` omits `core::mem::drop::<Guard>` (`symId = 24`)
    while `partial_init_move_cleanup` (`symId = 4`) invokes `calleeSym = 24`. It passes
    Boundary 1 raw syntax framing and Boundary 2a per-body well-formedness, but is rejected
    at Boundary 2b (`isAdmittedPackageBytes = false`, `checkBodiesClosure = false`). -/
theorem control_b2b_missing_required_body_rejected :
    (match parseWirePackage realControlB2MissingRequiredBodyBytes with
     | .accepted pkg =>
         some (checkBodiesWellFormed pkg.bodies, checkBodiesClosure pkg.bodies pkg.bodies)
     | _ => none) = some (true, false) ∧
    isAdmittedPackageBytes realControlB2MissingRequiredBodyBytes = false := by
  refine ⟨rfl, rfl⟩

/-! ## Boundary 3: Header Filtering (Stage 3a), Payload Fingerprint Recomputation (Stage 3b),
    and Endorsed Compilation / Subject / Flag / Completion Binding (Stage 3c) -/

/-- UTF-8 byte lists of the target crate names (`"cleanup_subject"` and `"place_mention_probe"`). -/
def cleanupSubjectCrateBytes : List Nat :=
  [99, 108, 101, 97, 110, 117, 112, 95, 115, 117, 98, 106, 101, 99, 116]

def placeMentionProbeCrateBytes : List Nat :=
  [112, 108, 97, 99, 101, 95, 109, 101, 110, 116, 105, 111, 110, 95, 112, 114, 111, 98, 101]

/-- Exact 16-bit payload fingerprint recomputation over the crate name bytes and canonical
    body byte stream (`bytes.drop 10`), matching lines 1777–1787 of `direct_mir_driver_v4.rs`. -/
def fp16CrateLoop (acc : Nat) : List Nat → Nat
  | [] => acc
  | b :: bs => fp16CrateLoop (((acc * 31) + b) % 65536) bs

def fp16PayloadLoop (acc : Nat) : List Nat → Nat
  | [] => acc
  | b :: bs => fp16PayloadLoop (((acc * 131) + b) % 65536) bs

def recomputePayloadFp16 (crateNameBytes : List Nat) (payload : List Nat) : Nat × Nat :=
  let acc0 := fp16CrateLoop 0x5A3C crateNameBytes
  let acc := fp16PayloadLoop acc0 payload
  ((acc / 256) % 256, acc % 256)

/-- Stage 3b: Verify that the package header's `(fpHi, fpLo)` matches the 16-bit
    fingerprint recomputed directly from the crate name bytes and encoded body payload. -/
def checkStage3bPayloadFp16 (crateNameBytes : List Nat) (pkg : WirePackage) (rawBytes : List Nat) : Bool :=
  let (hi, lo) := recomputePayloadFp16 crateNameBytes (rawBytes.drop 10)
  Nat.beq pkg.fpHi hi && Nat.beq pkg.fpLo lo

structure CompilationBindingSpec where
  expectedFpHi : Nat
  expectedFpLo : Nat
  requireMonoComplete : Bool
  requirePreserveUb : Bool
  expectedBodyCount : Nat
  requiredEntrySymId : Nat
  deriving DecidableEq, Repr

def cleanupPreserveUbBindingSpec : CompilationBindingSpec :=
  { expectedFpHi := 167
  , expectedFpLo := 56
  , requireMonoComplete := true
  , requirePreserveUb := true
  , expectedBodyCount := 9
  , requiredEntrySymId := 4 }

def placeMentionPreserveUbBindingSpec : CompilationBindingSpec :=
  { expectedFpHi := 62
  , expectedFpLo := 110
  , requireMonoComplete := true
  , requirePreserveUb := true
  , expectedBodyCount := 3
  , requiredEntrySymId := 6 }

def bodiesContainSym (sym : Nat) : List WireBody → Bool
  | [] => false
  | b :: bs => bif Nat.beq b.symId sym then true else bodiesContainSym sym bs

/-- Stage 3a: Header-only metadata filter (necessary but not sufficient for compilation binding). -/
def checkStage3aHeaderFilter (spec : CompilationBindingSpec) (pkg : WirePackage) : Bool :=
  Nat.beq pkg.fpHi spec.expectedFpHi &&
  Nat.beq pkg.fpLo spec.expectedFpLo &&
  (bif spec.requireMonoComplete then pkg.monoComplete else true) &&
  (bif spec.requirePreserveUb then pkg.preserveUb else true) &&
  Nat.beq pkg.bodies.length spec.expectedBodyCount &&
  bodiesContainSym spec.requiredEntrySymId pkg.bodies

/-- Stage 3c: Endorsed external compilation record carrying crate identity, source digest ID,
    compiler revision ID, semantic flag vector, crate SVH ID, completion status, output-write status,
    and the exact emitted `.amir` byte stream. -/
structure EndorsedCompilationRecord where
  crateNameBytes : List Nat
  sourceDigestId : Nat
  compilerRevId : Nat
  mirPreserveUbFlag : Bool
  alwaysEncodeMirFlag : Bool
  crateSvhId : Nat
  compilationCompleted : Bool
  outputWriteSucceeded : Bool
  headerSpec : CompilationBindingSpec
  endorsedBytes : List Nat
  deriving DecidableEq, Repr

/-- Explicit conditional premise stating that an external `EndorsedCompilationRecord` was
    produced by a completed, fail-closed `direct_mir_driver_v4` invocation over the named
    source and compiler configuration. -/
def TrustedProducerPremise (rec : EndorsedCompilationRecord) : Prop :=
  rec.compilationCompleted = true ∧
  rec.outputWriteSucceeded = true ∧
  ∃ pkg : WirePackage,
    parseWirePackage rec.endorsedBytes = .accepted pkg ∧
    checkPackageAdmissionClosure pkg = true ∧
    checkStage3aHeaderFilter rec.headerSpec pkg = true ∧
    checkStage3bPayloadFp16 rec.crateNameBytes pkg rec.endorsedBytes = true

def boolBeq (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

theorem boolBeq_eq_true {a b : Bool} (h : boolBeq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

/-- Stage 3c full compilation-binding check: verifies that the external compilation record
    completed and wrote its output cleanly, that the requested crate/source/compiler/flags/SVH
    match the record, that the candidate bytes parse, satisfy Stage B2b package admission closure,
    and satisfy Stage 3a + Stage 3b payload fingerprint recomputation, and that the candidate
    byte stream matches the endorsed artifact. -/
def checkEndorsedCompilationBinding
    (rec : EndorsedCompilationRecord)
    (expectedCrateBytes : List Nat)
    (expectedSourceDigestId : Nat)
    (expectedCompilerRevId : Nat)
    (expectedPreserveUb : Bool)
    (expectedSvhId : Nat)
    (candidateBytes : List Nat) : Bool :=
  rec.compilationCompleted &&
  rec.outputWriteSucceeded &&
  listNatBeq rec.crateNameBytes expectedCrateBytes &&
  Nat.beq rec.sourceDigestId expectedSourceDigestId &&
  Nat.beq rec.compilerRevId expectedCompilerRevId &&
  boolBeq rec.mirPreserveUbFlag expectedPreserveUb &&
  rec.alwaysEncodeMirFlag &&
  Nat.beq rec.crateSvhId expectedSvhId &&
  listNatBeq candidateBytes rec.endorsedBytes &&
  match parseWirePackage candidateBytes with
  | .accepted pkg =>
      checkPackageAdmissionClosure pkg &&
      checkStage3aHeaderFilter rec.headerSpec pkg &&
      checkStage3bPayloadFp16 rec.crateNameBytes pkg candidateBytes
  | _ => false

theorem endorsed_compilation_binding_sound_under_trusted_producer
    (rec : EndorsedCompilationRecord)
    (expectedCrateBytes : List Nat)
    (expectedSourceDigestId expectedCompilerRevId : Nat)
    (expectedPreserveUb : Bool)
    (expectedSvhId : Nat)
    (candidateBytes : List Nat)
    (_hTrusted : TrustedProducerPremise rec)
    (hBind : checkEndorsedCompilationBinding rec expectedCrateBytes expectedSourceDigestId
      expectedCompilerRevId expectedPreserveUb expectedSvhId candidateBytes = true) :
    candidateBytes = rec.endorsedBytes ∧
    rec.compilationCompleted = true ∧
    rec.outputWriteSucceeded = true ∧
    rec.crateNameBytes = expectedCrateBytes ∧
    rec.sourceDigestId = expectedSourceDigestId ∧
    rec.compilerRevId = expectedCompilerRevId ∧
    rec.mirPreserveUbFlag = expectedPreserveUb ∧
    rec.crateSvhId = expectedSvhId := by
  unfold checkEndorsedCompilationBinding at hBind
  cases h1 : rec.compilationCompleted <;> rw [h1] at hBind <;> try contradiction
  cases h2 : rec.outputWriteSucceeded <;> rw [h2] at hBind <;> try contradiction
  cases h3 : listNatBeq rec.crateNameBytes expectedCrateBytes <;> rw [h3] at hBind <;> try contradiction
  cases h4 : Nat.beq rec.sourceDigestId expectedSourceDigestId <;> rw [h4] at hBind <;> try contradiction
  cases h5 : Nat.beq rec.compilerRevId expectedCompilerRevId <;> rw [h5] at hBind <;> try contradiction
  cases h6 : boolBeq rec.mirPreserveUbFlag expectedPreserveUb <;> rw [h6] at hBind <;> try contradiction
  cases h7 : rec.alwaysEncodeMirFlag <;> rw [h7] at hBind <;> try contradiction
  cases h8 : Nat.beq rec.crateSvhId expectedSvhId <;> rw [h8] at hBind <;> try contradiction
  cases h9 : listNatBeq candidateBytes rec.endorsedBytes <;> rw [h9] at hBind <;> try contradiction
  exact ⟨listNatBeq_eq_true h9, rfl, rfl, listNatBeq_eq_true h3,
         Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5,
         boolBeq_eq_true h6, Nat.eq_of_beq_eq_true h8⟩

def cleanupPreserveUbEndorsedRecord : EndorsedCompilationRecord :=
  { crateNameBytes := cleanupSubjectCrateBytes
  , sourceDigestId := 1001
  , compilerRevId := 1980
  , mirPreserveUbFlag := true
  , alwaysEncodeMirFlag := true
  , crateSvhId := 5001
  , compilationCompleted := true
  , outputWriteSucceeded := true
  , headerSpec := cleanupPreserveUbBindingSpec
  , endorsedBytes := realCleanupSubjectPreserveUbBytes }

def placeMentionPreserveUbEndorsedRecord : EndorsedCompilationRecord :=
  { crateNameBytes := placeMentionProbeCrateBytes
  , sourceDigestId := 1002
  , compilerRevId := 1980
  , mirPreserveUbFlag := true
  , alwaysEncodeMirFlag := true
  , crateSvhId := 5002
  , compilationCompleted := true
  , outputWriteSucceeded := true
  , headerSpec := placeMentionPreserveUbBindingSpec
  , endorsedBytes := realPlaceMentionPreserveUbBytes }

def incompleteStopAfterAnalysisRecord : EndorsedCompilationRecord :=
  { cleanupPreserveUbEndorsedRecord with
    compilationCompleted := false }

def failedOutputWriteRecord : EndorsedCompilationRecord :=
  { cleanupPreserveUbEndorsedRecord with
    outputWriteSucceeded := false }

/-- Spoofed-header payload mutation (`control_b3_spoofed_header_payload.amir`):
    `g2.log` in `partial_init_move_cleanup` is mutated from `_4` to `_3` while keeping
    the original header bytes `fp16 = (167, 56)`. -/
def realControlB3SpoofedHeaderPayloadBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 167, 56, 9, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 3, 1, 3, 10, 2, 5, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 252, 131, 2, 0, 0, 74, 27, 7, 0, 255, 252, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 252, 73, 0, 129, 100, 0, 1, 33, 9, 64, 4, 4, 1, 3, 22, 4, 17, 3, 2, 2, 6, 6, 9, 8, 6, 8, 6, 1, 2, 8, 1, 6, 1, 8, 3, 2, 6, 2, 2, 0, 20, 17, 21, 0, 128, 0, 17, 20, 0, 128, 0, 32, 5, 32, 6, 32, 7, 19, 7, 0, 1, 3, 4, 25, 6, 0, 1, 129, 1, 71, 0, 33, 7, 32, 8, 32, 9, 19, 9, 0, 1, 3, 4, 25, 8, 0, 1, 129, 2, 73, 0, 33, 9, 17, 20, 0, 128, 1, 25, 5, 0, 2, 70, 0, 72, 0, 33, 8, 33, 6, 32, 10, 32, 11, 17, 11, 0, 1, 0, 69, 75, 0, 0, 4, 1, 0, 8, 32, 12, 17, 20, 0, 128, 0, 17, 21, 0, 128, 1, 17, 12, 0, 69, 1, 32, 13, 32, 14, 16, 19, 0, 12, 2, 19, 14, 0, 1, 19, 4, 75, 1, 13, 0, 2, 13, 78, 0, 129, 10, 0, 6, 33, 14, 33, 13, 32, 15, 32, 16, 17, 21, 0, 128, 0, 17, 16, 0, 76, 0, 74, 24, 15, 0, 3, 13, 80, 0, 0, 5, 33, 16, 33, 15, 17, 10, 0, 131, 0, 17, 21, 0, 128, 0, 33, 12, 68, 5, 0, 1, 17, 10, 0, 131, 0, 68, 5, 0, 5, 33, 11, 33, 10, 32, 17, 32, 18, 17, 18, 0, 2, 0, 75, 3, 17, 0, 6, 16, 82, 0, 129, 5, 0, 3, 33, 18, 17, 0, 0, 17, 0, 33, 17, 69, 20, 0, 0, 10, 11, 1, 0, 65, 0, 2, 17, 20, 0, 128, 0, 33, 5, 64, 1, 0, 71, 5, 2, 7, 7, 255, 0, 0, 71, 5, 2, 7, 8, 7, 0, 0, 71, 5, 1, 7, 10, 9, 1, 0, 71, 12, 0, 7, 16, 255, 1, 0, 69, 21, 0, 0, 16, 12, 1, 0, 71, 5, 2, 7, 7, 255, 1, 0, 71, 5, 1, 7, 14, 255, 1, 0, 69, 20, 0, 0, 14, 15, 5, 5, 1, 3, 24, 3, 9, 3, 2, 6, 6, 9, 8, 6, 8, 6, 8, 1, 6, 6, 1, 8, 3, 2, 8, 6, 6, 6, 6, 6, 2, 0, 22, 17, 23, 0, 128, 0, 32, 4, 32, 5, 32, 6, 19, 6, 0, 1, 2, 4, 25, 5, 0, 1, 129, 1, 70, 0, 33, 6, 32, 7, 32, 8, 19, 8, 0, 1, 3, 4, 25, 7, 0, 1, 129, 2, 72, 0, 33, 8, 25, 4, 0, 2, 69, 0, 71, 0, 33, 7, 33, 5, 32, 9, 17, 23, 0, 128, 1, 17, 9, 0, 68, 1, 32, 10, 32, 11, 16, 21, 0, 9, 2, 19, 11, 0, 1, 21, 4, 75, 1, 10, 0, 1, 8, 75, 0, 129, 10, 0, 9, 33, 11, 33, 10, 32, 12, 16, 22, 0, 9, 2, 19, 12, 0, 3, 22, 4, 32, 13, 32, 14, 17, 23, 0, 128, 0, 17, 14, 0, 73, 0, 74, 25, 13, 0, 2, 8, 78, 0, 0, 5, 33, 14, 33, 13, 32, 15, 32, 16, 17, 16, 0, 1, 0, 75, 3, 15, 0, 3, 8, 80, 0, 129, 7, 0, 19, 33, 16, 32, 17, 32, 18, 32, 19, 32, 20, 19, 20, 0, 1, 12, 4, 19, 19, 0, 1, 20, 4, 19, 18, 0, 1, 19, 4, 25, 17, 0, 1, 129, 3, 82, 0, 33, 18, 17, 4, 1, 81, 0, 33, 17, 33, 20, 33, 19, 17, 0, 0, 15, 0, 33, 15, 33, 12, 17, 23, 0, 128, 0, 33, 9, 71, 4, 0, 8, 4, 6, 0, 1, 33, 4, 64, 1, 0, 71, 4, 2, 7, 6, 255, 1, 0, 65, 1, 0, 71, 9, 0, 7, 5, 255, 1, 0, 69, 23, 0, 0, 5, 7, 6, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 3, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 8, 2, 4, 2, 1, 5, 1, 23, 0, 0, 71, 1, 5, 7, 4, 3, 1, 0, 65, 0, 0, 64, 1, 0, 71, 1, 6, 7, 1, 255, 0, 0, 71, 1, 6, 7, 2, 252, 9, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

/-- Recomputed-header payload mutation (`mutant_wrong_log_target.amir`):
    same payload mutation (`g2.log` mutated from `_4` to `_3`), with header `fp16`
    recomputed to `(24, 221)` so Stage 3b payload fingerprint consistency passes. -/
def realControlB3RecomputedHeaderMutantBytes : List Nat :=
  [65, 77, 73, 82, 3, 3, 11, 24, 221, 9, 1, 1, 1, 3, 9, 2, 4, 1, 6, 3, 3, 3, 3, 3, 3, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 5, 75, 20, 3, 0, 1, 252, 68, 0, 129, 1, 0, 7, 33, 4, 17, 1, 5, 67, 0, 33, 3, 32, 5, 32, 6, 32, 7, 17, 7, 0, 1, 6, 75, 21, 6, 0, 2, 252, 71, 0, 129, 16, 0, 3, 33, 7, 32, 8, 17, 8, 0, 2, 0, 75, 20, 5, 0, 3, 252, 70, 0, 72, 0, 0, 5, 33, 8, 33, 6, 17, 1, 6, 69, 0, 33, 5, 17, 0, 0, 131, 0, 64, 2, 2, 1, 3, 6, 1, 2, 1, 22, 1, 6, 3, 6, 0, 6, 32, 2, 32, 3, 16, 5, 0, 1, 6, 19, 3, 0, 1, 5, 4, 32, 4, 17, 4, 0, 1, 5, 75, 1, 2, 0, 1, 252, 67, 0, 68, 0, 0, 4, 33, 4, 33, 3, 33, 2, 17, 0, 0, 131, 0, 64, 3, 3, 1, 3, 10, 2, 5, 3, 2, 3, 1, 2, 19, 19, 19, 19, 3, 0, 3, 32, 3, 32, 4, 17, 4, 0, 1, 0, 69, 68, 0, 0, 3, 1, 0, 2, 32, 7, 32, 8, 74, 26, 8, 0, 2, 252, 131, 2, 0, 0, 74, 27, 7, 0, 255, 252, 72, 0, 0, 5, 17, 3, 0, 131, 0, 33, 4, 33, 3, 32, 9, 17, 9, 0, 2, 0, 75, 20, 0, 0, 4, 252, 73, 0, 129, 100, 0, 1, 33, 9, 64, 4, 4, 1, 3, 22, 4, 17, 3, 2, 2, 6, 6, 9, 8, 6, 8, 6, 1, 2, 8, 1, 6, 1, 8, 3, 2, 6, 2, 2, 0, 20, 17, 21, 0, 128, 0, 17, 20, 0, 128, 0, 32, 5, 32, 6, 32, 7, 19, 7, 0, 1, 3, 4, 25, 6, 0, 1, 129, 1, 71, 0, 33, 7, 32, 8, 32, 9, 19, 9, 0, 1, 3, 4, 25, 8, 0, 1, 129, 2, 73, 0, 33, 9, 17, 20, 0, 128, 1, 25, 5, 0, 2, 70, 0, 72, 0, 33, 8, 33, 6, 32, 10, 32, 11, 17, 11, 0, 1, 0, 69, 75, 0, 0, 4, 1, 0, 8, 32, 12, 17, 20, 0, 128, 0, 17, 21, 0, 128, 1, 17, 12, 0, 69, 1, 32, 13, 32, 14, 16, 19, 0, 12, 2, 19, 14, 0, 1, 19, 4, 75, 1, 13, 0, 2, 13, 78, 0, 129, 10, 0, 6, 33, 14, 33, 13, 32, 15, 32, 16, 17, 21, 0, 128, 0, 17, 16, 0, 76, 0, 74, 24, 15, 0, 3, 13, 80, 0, 0, 5, 33, 16, 33, 15, 17, 10, 0, 131, 0, 17, 21, 0, 128, 0, 33, 12, 68, 5, 0, 1, 17, 10, 0, 131, 0, 68, 5, 0, 5, 33, 11, 33, 10, 32, 17, 32, 18, 17, 18, 0, 2, 0, 75, 3, 17, 0, 6, 16, 82, 0, 129, 5, 0, 3, 33, 18, 17, 0, 0, 17, 0, 33, 17, 69, 20, 0, 0, 10, 11, 1, 0, 65, 0, 2, 17, 20, 0, 128, 0, 33, 5, 64, 1, 0, 71, 5, 2, 7, 7, 255, 0, 0, 71, 5, 2, 7, 8, 7, 0, 0, 71, 5, 1, 7, 10, 9, 1, 0, 71, 12, 0, 7, 16, 255, 1, 0, 69, 21, 0, 0, 16, 12, 1, 0, 71, 5, 2, 7, 7, 255, 1, 0, 71, 5, 1, 7, 14, 255, 1, 0, 69, 20, 0, 0, 14, 15, 5, 5, 1, 3, 24, 3, 9, 3, 2, 6, 6, 9, 8, 6, 8, 6, 8, 1, 6, 6, 1, 8, 3, 2, 8, 6, 6, 6, 6, 6, 2, 0, 22, 17, 23, 0, 128, 0, 32, 4, 32, 5, 32, 6, 19, 6, 0, 1, 2, 4, 25, 5, 0, 1, 129, 1, 70, 0, 33, 6, 32, 7, 32, 8, 19, 8, 0, 1, 3, 4, 25, 7, 0, 1, 129, 2, 72, 0, 33, 8, 25, 4, 0, 2, 69, 0, 71, 0, 33, 7, 33, 5, 32, 9, 17, 23, 0, 128, 1, 17, 9, 0, 68, 1, 32, 10, 32, 11, 16, 21, 0, 9, 2, 19, 11, 0, 1, 21, 4, 75, 1, 10, 0, 1, 8, 75, 0, 129, 10, 0, 9, 33, 11, 33, 10, 32, 12, 16, 22, 0, 9, 2, 19, 12, 0, 3, 22, 4, 32, 13, 32, 14, 17, 23, 0, 128, 0, 17, 14, 0, 73, 0, 74, 25, 13, 0, 2, 8, 78, 0, 0, 5, 33, 14, 33, 13, 32, 15, 32, 16, 17, 16, 0, 1, 0, 75, 3, 15, 0, 3, 8, 80, 0, 129, 7, 0, 19, 33, 16, 32, 17, 32, 18, 32, 19, 32, 20, 19, 20, 0, 1, 12, 4, 19, 19, 0, 1, 20, 4, 19, 18, 0, 1, 19, 4, 25, 17, 0, 1, 129, 3, 82, 0, 33, 18, 17, 4, 1, 81, 0, 33, 17, 33, 20, 33, 19, 17, 0, 0, 15, 0, 33, 15, 33, 12, 17, 23, 0, 128, 0, 33, 9, 71, 4, 0, 8, 4, 6, 0, 1, 33, 4, 64, 1, 0, 71, 4, 2, 7, 6, 255, 1, 0, 65, 1, 0, 71, 9, 0, 7, 5, 255, 1, 0, 69, 23, 0, 0, 5, 7, 6, 6, 1, 3, 6, 2, 4, 3, 5, 2, 3, 1, 2, 0, 7, 32, 3, 17, 3, 0, 1, 4, 48, 3, 0, 33, 3, 32, 4, 32, 5, 17, 5, 0, 2, 0, 69, 69, 0, 0, 2, 1, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 1, 17, 4, 0, 131, 0, 68, 3, 0, 3, 33, 5, 33, 4, 17, 0, 0, 129, 0, 64, 7, 7, 2, 4, 4, 1, 2, 1, 22, 22, 1, 0, 1, 17, 2, 0, 1, 0, 74, 2, 3, 0, 1, 252, 66, 0, 0, 0, 64, 8, 8, 2, 4, 2, 1, 5, 1, 23, 0, 0, 71, 1, 5, 7, 4, 3, 1, 0, 65, 0, 0, 64, 1, 0, 71, 1, 6, 7, 1, 255, 0, 0, 71, 1, 6, 7, 2, 252, 9, 24, 3, 4, 2, 1, 2, 1, 8, 0, 0, 71, 1, 0, 7, 1, 252, 0, 0, 64]

/-- Boundary 3 Control 1 (Payload Mutation with Spoofed Matching Header Bytes):
    `realControlB3SpoofedHeaderPayloadBytes` passes Boundary 1 and Boundary 2 (`parseWirePackage`
    accepts it, `checkPackageAdmissionClosure = true`) AND passes Stage 3a
    `checkStage3aHeaderFilter` (`true`, because the header still claims `fp16 = (167, 56)`),
    but is rejected at Stage 3b `checkStage3bPayloadFp16` (`false`, because recomputing `fp16`
    over `"cleanup_subject"` + payload yields `(24, 221) ≠ (167, 56)`). -/
theorem control_b3_spoofed_header_payload_passes_stage3a_and_rejected_at_stage3b :
    (match parseWirePackage realControlB3SpoofedHeaderPayloadBytes with
     | .accepted pkg =>
         some (checkPackageAdmissionClosure pkg,
               checkStage3aHeaderFilter cleanupPreserveUbBindingSpec pkg,
               checkStage3bPayloadFp16 cleanupSubjectCrateBytes pkg realControlB3SpoofedHeaderPayloadBytes)
     | _ => none) = some (true, true, false) ∧
    (match parseWirePackage realCleanupSubjectPreserveUbBytes with
     | .accepted pkg =>
         some (checkPackageAdmissionClosure pkg,
               checkStage3aHeaderFilter cleanupPreserveUbBindingSpec pkg,
               checkStage3bPayloadFp16 cleanupSubjectCrateBytes pkg realCleanupSubjectPreserveUbBytes)
     | _ => none) = some (true, true, true) := by
  refine ⟨rfl, rfl⟩

/-- Boundary 3 Control 2 (Recomputed-Header Payload Mutation):
    `realControlB3RecomputedHeaderMutantBytes` passes Boundary 1, Boundary 2, AND Stage 3b
    `checkStage3bPayloadFp16` (`true`, because its header `fp16 = (24, 221)` matches its
    recomputed payload fingerprint), but is rejected by Stage 3c `checkEndorsedCompilationBinding`
    against `cleanupPreserveUbEndorsedRecord`. -/
theorem control_b3_recomputed_header_mutant_passes_stage3b_and_rejected_at_stage3c :
    (match parseWirePackage realControlB3RecomputedHeaderMutantBytes with
     | .accepted pkg =>
         some (checkPackageAdmissionClosure pkg,
               checkStage3bPayloadFp16 cleanupSubjectCrateBytes pkg realControlB3RecomputedHeaderMutantBytes)
     | _ => none) = some (true, true) ∧
    checkEndorsedCompilationBinding cleanupPreserveUbEndorsedRecord
      cleanupSubjectCrateBytes 1001 1980 true 5001
      realControlB3RecomputedHeaderMutantBytes = false ∧
    checkEndorsedCompilationBinding cleanupPreserveUbEndorsedRecord
      cleanupSubjectCrateBytes 1001 1980 true 5001
      realCleanupSubjectPreserveUbBytes = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- Boundary 3 Control 3 (Subject Substitution):
    `realPlaceMentionPreserveUbBytes` is a well-formed, canonical `.amir` v3 package
    that passes Boundary 1, Boundary 2, and Stage 3b `checkStage3bPayloadFp16`, but fails
    Stage 3c `checkEndorsedCompilationBinding` when substituted for `cleanup_subject`. -/
theorem control_b3_wrong_subject_passes_b1_b2_and_rejected_at_b3 :
    (match parseWirePackage realPlaceMentionPreserveUbBytes with
     | .accepted pkg =>
         some (checkPackageAdmissionClosure pkg,
               checkStage3bPayloadFp16 placeMentionProbeCrateBytes pkg realPlaceMentionPreserveUbBytes)
     | _ => none) = some (true, true) ∧
    checkEndorsedCompilationBinding cleanupPreserveUbEndorsedRecord
      cleanupSubjectCrateBytes 1001 1980 true 5001
      realPlaceMentionPreserveUbBytes = false := by
  refine ⟨rfl, rfl⟩

/-- Boundary 3 Control 4 (Compilation Flag / Configuration Substitution):
    `realPlaceMentionDefaultBytes` (`-Z mir-preserve-ub` omitted, `fp16 = [26, 248]`)
    passes Boundary 1, Boundary 2, and Stage 3b `checkStage3bPayloadFp16`, but fails
    Stage 3c `checkEndorsedCompilationBinding` when `mirPreserveUbFlag = true` is required. -/
theorem control_b3_wrong_flag_config_passes_b1_b2_and_rejected_at_b3 :
    (match parseWirePackage realPlaceMentionDefaultBytes with
     | .accepted pkg =>
         some (checkPackageAdmissionClosure pkg,
               checkStage3bPayloadFp16 placeMentionProbeCrateBytes pkg realPlaceMentionDefaultBytes)
     | _ => none) = some (true, true) ∧
    checkEndorsedCompilationBinding placeMentionPreserveUbEndorsedRecord
      placeMentionProbeCrateBytes 1002 1980 true 5002
      realPlaceMentionDefaultBytes = false ∧
    checkEndorsedCompilationBinding placeMentionPreserveUbEndorsedRecord
      placeMentionProbeCrateBytes 1002 1980 true 5002
      realPlaceMentionPreserveUbBytes = true := by
  refine ⟨rfl, rfl, rfl⟩

/-- Boundary 3 Control 5 (Incomplete Compilation / Failed Output Write Rejection):
    Even if a stale or candidate `.amir` byte stream is presented on disk, Stage 3c
    `checkEndorsedCompilationBinding` rejects any invocation record where `after_analysis`
    stopped early (`compilationCompleted = false`) or output writing failed
    (`outputWriteSucceeded = false`). -/
theorem control_b3_incomplete_or_failed_write_rejected_at_stage3c :
    checkEndorsedCompilationBinding incompleteStopAfterAnalysisRecord
      cleanupSubjectCrateBytes 1001 1980 true 5001
      realCleanupSubjectPreserveUbBytes = false ∧
    checkEndorsedCompilationBinding failedOutputWriteRecord
      cleanupSubjectCrateBytes 1001 1980 true 5001
      realCleanupSubjectPreserveUbBytes = false := by
  refine ⟨rfl, rfl⟩

/-- Boundary 3 Untrusted Metadata Contrast: Sidecar human-readable strings (owner names,
    source spans, `LocalInfo` display labels) cannot alter the operational AST parsed
    from the verified `.amir` byte stream. -/
structure UntrustedSidecarEnvelope where
  rawBytes : List Nat
  untrustedOwnerLabel : String
  untrustedSourceSpan : String
  deriving DecidableEq, Repr

def parseOperationalFromEnvelope (env : UntrustedSidecarEnvelope) : ParseOutcome WirePackage :=
  parseWirePackage env.rawBytes

theorem control_b3_untrusted_metadata_cannot_alter_accepted_ast
    (b : List Nat) (lbl₁ lbl₂ span₁ span₂ : String) :
    parseOperationalFromEnvelope { rawBytes := b, untrustedOwnerLabel := lbl₁, untrustedSourceSpan := span₁ } =
    parseOperationalFromEnvelope { rawBytes := b, untrustedOwnerLabel := lbl₂, untrustedSourceSpan := span₂ } := by
  rfl

/-! ## Boundary 5: Property / Source-Semantics Adequacy vs. Boundary 1–3 Admission -/

def bodiesAllAdequateForRawPtrProbes : List WireBody → Bool
  | [] => true
  | b :: bs =>
      bif (bodyHasDerefCopyAssign b.blocks || bodyHasPlaceMention b.blocks) then
        bodiesAllAdequateForRawPtrProbes bs
      else
        false

def boundary5AdequateForRawPtrProbes (bytes : List Nat) : Bool :=
  match parseWirePackage bytes with
  | .accepted pkg =>
      pkg.preserveUb && bodiesAllAdequateForRawPtrProbes pkg.bodies
  | _ => false

theorem control_b5_default_mir_passes_b1_b2_but_fails_raw_ptr_adequacy :
    (match parseWirePackage realPlaceMentionDefaultBytes with
     | .accepted _ => true
     | _ => false) = true ∧
    boundary5AdequateForRawPtrProbes realPlaceMentionDefaultBytes = false ∧
    boundary5AdequateForRawPtrProbes realPlaceMentionPreserveUbBytes = true := by
  refine ⟨rfl, rfl, rfl⟩

#print axioms real_limit_32_positive_bytes_accepted_at_exact_32_block_bound
#print axioms control_b1_non_physical_byte_rejected
#print axioms control_b1_truncated_rejected
#print axioms control_b1_trailing_bytes_rejected
#print axioms control_b1_unsupported_inline_asm_rejected
#print axioms control_b2_out_of_bounds_local_rejected
#print axioms control_b2b_duplicate_sym_id_rejected
#print axioms control_b2b_missing_required_body_rejected
#print axioms endorsed_compilation_binding_sound_under_trusted_producer
#print axioms control_b3_spoofed_header_payload_passes_stage3a_and_rejected_at_stage3b
#print axioms control_b3_recomputed_header_mutant_passes_stage3b_and_rejected_at_stage3c
#print axioms control_b3_wrong_subject_passes_b1_b2_and_rejected_at_b3
#print axioms control_b3_wrong_flag_config_passes_b1_b2_and_rejected_at_b3
#print axioms control_b3_incomplete_or_failed_write_rejected_at_stage3c
#print axioms control_b3_untrusted_metadata_cannot_alter_accepted_ast
#print axioms control_b5_default_mir_passes_b1_b2_but_fails_raw_ptr_adequacy

end AnnealResearch.SubstantiveMirByteParserControls
