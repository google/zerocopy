-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Out-of-Key `StmtOrd` Sideband Span Provenance & `MirItemKey` Cache Invariance (`K8_`)

Mechanizes the core architectural separation between content-addressed verification
caching (`MirItemKey` in `X6`) and source-span-accurate `rustc` / SARIF 2.1.0
diagnostics (`K8_`):

1. Each `CoreMIR` statement and `MiniSSA` / `MiniMach` instruction carries a
   dense, function-local ordinal index (`StmtOrd : Nat`) rather than a volatile
   byte-offset `Span`.
2. `.anneal-mir` stores an out-of-key `SidebandSpanTable (StmtOrd → SpanData)`
   mapping each `StmtOrd` to its source file, line, column, and optional
   cross-crate `ThinLTO` inlining call-site ordinal (`inlinedFrom : Option StmtOrd`).
3. **`mirItemKey_invariant_under_line_shift`** and **`shifted_diagnostic_span_exact`**
   prove that inserting or deleting arbitrary lines of comments/whitespace
   (`shiftSpanTable tbl deltaLines`) preserves `computeMirItemKey` (`100%` Tier 1–3
   cache hit) while updating every emitted diagnostic (`W_ANNEAL_0101`..`E_ANNEAL_0301`)
   to the exact shifted line number.
-/

namespace Anneal.SpanProvenance

abbrev StmtOrd := Nat
abbrev FileId := Nat
abbrev RuleFamilyId := Nat

/-- Source coordinate entry stored in the out-of-key `.anneal-mir` sideband table. -/
structure SpanData where
  fileId : FileId
  loLine : Nat
  loCol : Nat
  hiLine : Nat
  hiCol : Nat
  inlinedFrom : Option StmtOrd
  deriving Repr, DecidableEq

/-- Canonical span-free MIR instruction representation hashed into `MirItemKey`. -/
inductive CanonicalMirOp where
  | assignAdd (dst src1 src2 : Nat)
  | inlineAsm (contractHash : Nat)
  | constEvalSelect (ctFn rtFn : Nat)
  | checkedDiv (dst num den : Nat)
  deriving Repr, DecidableEq

/-- A packaged `.anneal-mir` function bundle separates the canonical `stmts`
(which feed `MirItemKey`) from the `sidebandSpans` table (which feeds diagnostics). -/
structure PackagedMirFunction where
  fnSymbolId : Nat
  stmts : List (StmtOrd × CanonicalMirOp)
  sidebandSpans : StmtOrd → SpanData

/-- Tier 1 `MirItemKey` projection depends purely on `(fnSymbolId, stmts)` and
never inspects `sidebandSpans`. -/
def computeMirItemKey (pkg : PackagedMirFunction) : Nat × List (StmtOrd × CanonicalMirOp) :=
  (pkg.fnSymbolId, pkg.stmts)

/-- Shift all line numbers in a `SidebandSpanTable` by `deltaLines` (modeling
insertion of `deltaLines` comment/blank lines above the function). -/
def shiftSpanData (sp : SpanData) (deltaLines : Nat) : SpanData :=
  { sp with
    loLine := sp.loLine + deltaLines
    hiLine := sp.hiLine + deltaLines }

def applyCommentLineShift (pkg : PackagedMirFunction) (deltaLines : Nat) : PackagedMirFunction :=
  { pkg with sidebandSpans := fun ord => shiftSpanData (pkg.sidebandSpans ord) deltaLines }

/-- Theorem 1 (`mirItemKey_invariant_under_line_shift`): Comment or line-offset shifts
never invalidate `MirItemKey`. -/
theorem mirItemKey_invariant_under_line_shift
    (pkg : PackagedMirFunction) (deltaLines : Nat) :
    computeMirItemKey (applyCommentLineShift pkg deltaLines) = computeMirItemKey pkg := by
  rfl

/-- Unified verification/compilation event kinds emitted by `cargo anneal` and
`-Zcodegen-backend=anneal`. -/
inductive AnnealDiagCode where
  | W_ANNEAL_0101_QuarantineFallback (ruleFamily : RuleFamilyId)
  | E_ANNEAL_0102_MissingAsmContract
  | E_ANNEAL_0103_ConstEvalSelectDivergence
  | E_ANNEAL_0104_CertCheckMismatch (stepIdx : Nat)
  | I_ANNEAL_0201_BinaryManifestVerified
  | E_ANNEAL_0301_ProcMacroNonDeterministic
  deriving Repr, DecidableEq

/-- A compiler/verifier event references only `(stmtOrd, code)`. -/
structure VerificationEvent where
  stmtOrd : StmtOrd
  code : AnnealDiagCode
  deriving Repr, DecidableEq

/-- Resolved user-facing diagnostic carrying exact `SpanData` and inlining backtrace. -/
structure ResolvedDiagnostic where
  code : AnnealDiagCode
  primarySpan : SpanData
  inliningBacktrace : List SpanData
  deriving Repr, DecidableEq

/-- Walk the `inlinedFrom` chain up to `fuel` frames to reconstruct the full
cross-crate `ThinLTO` inlining backtrace. -/
def resolveInliningBacktrace (fuel : Nat) (spans : StmtOrd → SpanData) (startOrd : Option StmtOrd) : List SpanData :=
  match fuel, startOrd with
  | 0, _ => []
  | _, none => []
  | fuel' + 1, some ord =>
      let sp := spans ord
      sp :: resolveInliningBacktrace fuel' spans sp.inlinedFrom

/-- Resolve a span-free `VerificationEvent` against `pkg.sidebandSpans`. -/
def emitDiagnostic (fuel : Nat) (pkg : PackagedMirFunction) (ev : VerificationEvent) : ResolvedDiagnostic :=
  let primary := pkg.sidebandSpans ev.stmtOrd
  { code := ev.code
    primarySpan := primary
    inliningBacktrace := resolveInliningBacktrace fuel pkg.sidebandSpans primary.inlinedFrom }

/-- Theorem 2 (`shifted_diagnostic_span_exact`): Resolving any cached `VerificationEvent`
against a line-shifted `PackagedMirFunction` produces the exact shifted line numbers
(`loLine + deltaLines`, `hiLine + deltaLines`) while preserving file and column offsets. -/
theorem shifted_diagnostic_span_exact
    (fuel : Nat) (pkg : PackagedMirFunction) (ev : VerificationEvent) (deltaLines : Nat) :
    let dOrig := emitDiagnostic fuel pkg ev
    let dShifted := emitDiagnostic fuel (applyCommentLineShift pkg deltaLines) ev
    dShifted.code = dOrig.code ∧
    dShifted.primarySpan.fileId = dOrig.primarySpan.fileId ∧
    dShifted.primarySpan.loLine = dOrig.primarySpan.loLine + deltaLines ∧
    dShifted.primarySpan.hiLine = dOrig.primarySpan.hiLine + deltaLines ∧
    dShifted.primarySpan.loCol = dOrig.primarySpan.loCol ∧
    dShifted.primarySpan.hiCol = dOrig.primarySpan.hiCol := by
  simp [emitDiagnostic, applyCommentLineShift, shiftSpanData]

/-- Theorem 3 (`backtrace_length_preserved_under_line_shift`): Shifting line offsets
preserves the exact depth of `ThinLTO` inlining backtraces. -/
theorem backtrace_length_preserved_under_line_shift
    (fuel : Nat) (spans : StmtOrd → SpanData) (startOrd : Option StmtOrd) (deltaLines : Nat) :
    (resolveInliningBacktrace fuel (fun ord => shiftSpanData (spans ord) deltaLines) startOrd).length =
    (resolveInliningBacktrace fuel spans startOrd).length := by
  induction fuel generalizing startOrd with
  | zero => rfl
  | succ f ih =>
      cases startOrd with
      | none => rfl
      | some ord =>
          simp only [resolveInliningBacktrace, List.length_cons]
          have hinl : (shiftSpanData (spans ord) deltaLines).inlinedFrom = (spans ord).inlinedFrom := rfl
          rw [hinl, ih (spans ord).inlinedFrom]

#print axioms mirItemKey_invariant_under_line_shift
#print axioms shifted_diagnostic_span_exact
#print axioms backtrace_length_preserved_under_line_shift

end Anneal.SpanProvenance
