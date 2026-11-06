import AnnealResearch.MiniRustFactored
import AnnealResearch.ReferenceInvariants

/-!
Named joint admission invariant for the factored metadata/cell representation.
It checks metadata geometry/domain/separation together with byte provenance in
the corresponding allocated cells. Cells at absent metadata entries are not
observable through reify and impose no additional admission requirement.

These are structural theorems. They do not assume or conclude NoUB, liveness,
in-bounds operands, aligned access addresses, or correct free metadata. The
all-state primitive bridge is independent of this invariant; here it transfers
the separately proved reference admission/preservation results.
-/

namespace AnnealResearch.MemoryInvariants

open MiniRustReference (Byte Ptr Kind AlignWF PtrWF BytesWF)

def targetWF (target : MiniRustFactored.State) : Prop :=
  MiniRustReference.StateWF (MiniRustFactored.reify target)

theorem encode_targetWF {source : MiniRustReference.State}
    (wf : MiniRustReference.StateWF source) :
    targetWF (MiniRustFactored.encode source) := by
  simpa [targetWF, MiniRustFactored.reify_encode] using wf

theorem encode_related (source : MiniRustReference.State) :
    MiniRustFactored.Related source (MiniRustFactored.encode source) :=
  (MiniRustFactored.reify_encode source).symm

theorem targetWF_of_related {source : MiniRustReference.State}
    {target : MiniRustFactored.State} (related : MiniRustFactored.Related source target)
    (wf : MiniRustReference.StateWF source) : targetWF target := by
  change source = MiniRustFactored.reify target at related
  change MiniRustReference.StateWF (MiniRustFactored.reify target)
  exact related ▸ wf

theorem empty_targetWF : targetWF MiniRustFactored.empty := by
  change MiniRustReference.StateWF MiniRustReference.empty
  exact MiniRustReference.emptyStateWF

theorem target_load_not_unsupported {state : MiniRustFactored.State} {pointer : Ptr}
    (length align : Nat) (wf : targetWF state)
    (pointerWF : PtrWF (MiniRustFactored.reify state) pointer) (alignWF : AlignWF align) :
    MiniRustFactored.load state pointer length align ≠ .unsupported := by
  intro unsupported
  have sourceUnsupported :
      MiniRustReference.load (MiniRustFactored.reify state) pointer length align =
        .unsupported := by
    simpa only [unsupported, MiniRustFactored.resultMap_unsupported] using
      MiniRustFactored.load_reify state pointer length align
  exact MiniRustReference.load_not_unsupported length align wf pointerWF alignWF
    sourceUnsupported

theorem target_store_not_unsupported {state : MiniRustFactored.State} {pointer : Ptr}
    (bytes : List Byte) (align : Nat) (wf : targetWF state)
    (pointerWF : PtrWF (MiniRustFactored.reify state) pointer) (alignWF : AlignWF align) :
    MiniRustFactored.store state pointer bytes align ≠ .unsupported := by
  intro unsupported
  have sourceUnsupported :
      MiniRustReference.store (MiniRustFactored.reify state) pointer bytes align =
        .unsupported := by
    simpa only [unsupported, MiniRustFactored.resultMap_unsupported] using
      MiniRustFactored.store_reify state pointer bytes align
  exact MiniRustReference.store_not_unsupported bytes align wf pointerWF alignWF
    sourceUnsupported

/-- Free has no requested-Align admission check. Its exact size/alignment/kind
comparisons can still produce UB. No AlignWF premise is needed to exclude the
unsupported forged-ID case. -/
theorem target_free_not_unsupported {state : MiniRustFactored.State} {pointer : Ptr}
    (kind : Kind) (size align : Nat) (wf : targetWF state)
    (pointerWF : PtrWF (MiniRustFactored.reify state) pointer) :
    MiniRustFactored.free state pointer kind size align ≠ .unsupported := by
  intro unsupported
  have sourceUnsupported :
      MiniRustReference.free (MiniRustFactored.reify state) pointer kind size align =
        .unsupported := by
    simpa only [unsupported, MiniRustFactored.resultMap_unsupported] using
      MiniRustFactored.free_reify state pointer kind size align
  exact MiniRustReference.free_not_unsupported kind size align wf pointerWF
    sourceUnsupported

theorem target_store_preserves_WF {state after : MiniRustFactored.State}
    {pointer : Ptr} {bytes : List Byte} {align : Nat} (wf : targetWF state)
    (bytesWF : BytesWF (MiniRustFactored.reify state) bytes)
    (success : MiniRustFactored.store state pointer bytes align = .ok after) :
    targetWF after := by
  have sourceSuccess :
      MiniRustReference.store (MiniRustFactored.reify state) pointer bytes align =
        .ok (MiniRustFactored.reify after) := by
    simpa only [success, MiniRustFactored.resultMap_ok] using
      MiniRustFactored.store_reify state pointer bytes align
  exact MiniRustReference.store_preserves_StateWF wf bytesWF sourceSuccess

theorem target_free_preserves_WF {state after : MiniRustFactored.State}
    {pointer : Ptr} {kind : Kind} {size align : Nat} (wf : targetWF state)
    (success : MiniRustFactored.free state pointer kind size align = .ok after) :
    targetWF after := by
  have sourceSuccess :
      MiniRustReference.free (MiniRustFactored.reify state) pointer kind size align =
        .ok (MiniRustFactored.reify after) := by
    simpa only [success, MiniRustFactored.resultMap_ok] using
      MiniRustFactored.free_reify state pointer kind size align
  exact MiniRustReference.free_preserves_StateWF wf sourceSuccess

theorem target_allocateAt_preserves_WF {state after : MiniRustFactored.State}
    {pointer : Ptr} {kind : Kind} {size align address : Nat} (wf : targetWF state)
    (alignWF : AlignWF align)
    (success : MiniRustFactored.allocateAt state kind size align address = .ok (pointer, after)) :
    targetWF after := by
  have sourceSuccess :
      MiniRustReference.allocateAt (MiniRustFactored.reify state) kind size align address =
        .ok (pointer, MiniRustFactored.reify after) := by
    simpa only [success, MiniRustFactored.resultMap_ok] using
      MiniRustFactored.allocateAt_reify state kind size align address
  exact MiniRustReference.allocateAt_preserves_StateWF wf alignWF sourceSuccess

#print axioms encode_targetWF
#print axioms encode_related
#print axioms targetWF_of_related
#print axioms empty_targetWF
#print axioms target_load_not_unsupported
#print axioms target_store_not_unsupported
#print axioms target_free_not_unsupported
#print axioms target_store_preserves_WF
#print axioms target_free_preserves_WF
#print axioms target_allocateAt_preserves_WF

end AnnealResearch.MemoryInvariants
