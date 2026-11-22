-- Mechanized Lean 4 (v4.34.1) probe for discharging NoDma & OpaqueMmio:
--   1. Counterexamples: stale-IOTLB DMA corruption on premature frame retyping,
--      posted-MMIO W1C IRQ-ack race without read-back flush, relaxed doorbell
--      reordering without dma_wmb, R2C status clobbering on unsafe read-back,
--      and non-coherent DMA missing post-DMA cache invalidation.
--   2. Safe protocol & refinement: DmaEpoch + MmioBus state machine with
--      proven invariant preservation, per-frame NoDma discharge theorem,
--      posted-MMIO read-back flush refinement theorem, and coherent /
--      non-coherent roundtrip ownership-transfer theorems.
--
-- Discipline: constructive Type 0, `prelude` + `Init.*` only, zero `sorry`,
-- zero custom `axiom`, zero `unsafe`/`partial`/`opaque`, zero `Classical.choice`,
-- zero `Lean.ofReduceBool`/`._unsafe_rec`.
prelude
import Init.Core
import Init.Data.Nat.Basic
import Init.Data.List.Basic

namespace DmaIotlbMmioDischarge

/-! ## 1. Core Hardware Domain Types -/

inductive DmaTier where
  | coherentIommu     -- Tier 1: Hardware-coherent bus + strict synchronous IOMMU
  | nonCoherentCache  -- Tier 2: Software cache-managed (DC CIVAC/CVAC/IVAC, Zicbom, CLFLUSHOPT)
  | byzantineIsolated -- Tier 3: Untrusted peripheral (strict IOTLB+ATC sync + page isolation)

inductive FramePhase where
  | cpuOwned (epoch : Nat)
  | dmaCleanPending (epoch : Nat)
  | deviceMapped (epoch : Nat)
  | revokingPendingIotlbSync (epoch : Nat)
  | postDmaInvalPending (epoch : Nat)

inductive MmioWriteOp where
  | w1cAck
  | doorbell

inductive ReadPortKind where
  | roIdempotent -- Side-effect-free RO/RW register (safe for PCIe read-back flush)
  | r2cStatus    -- Read-to-Clear status port (destructive on read!)

structure FrameState where
  tier        : DmaTier
  phase       : FramePhase
  dram        : Nat
  cpuCache    : Option Nat
  cacheDirty  : Bool
  pteValid    : Bool
  iotlbValid  : Bool
  inFlightDma : Bool

structure MmioBusState where
  postedQueue        : List MmioWriteOp
  w1cIrqPending      : Bool
  r2cEventPending    : Bool
  roDeviceId         : Nat
  doorbellCount      : Nat
  cpuIrqUnmasked     : Bool
  storeBufDirty      : Bool
  storeBufVal        : Nat
  lastDeviceSeenDesc : Nat

structure HwSystemState where
  frame : FrameState
  mmio  : MmioBusState

/-- What the CPU observes when reading the physical frame.
    On a non-coherent tier, a cached entry shadows DRAM until invalidated. -/
def cpuReadFrame (f : FrameState) : Nat :=
  match f.tier, f.cpuCache with
  | .nonCoherentCache, some v => v
  | _, _ => f.dram

/-- Pre-DMA cache clean helper (`DC CVAC`/`DC CIVAC` or `cbo.flush` + barrier). -/
def flushedDramVal (f : FrameState) : Nat :=
  match f.cacheDirty, f.cpuCache with
  | true, some v => v
  | _, _ => f.dram

/-- Post-IOTLB-sync next phase: non-coherent still requires post-DMA invalidate. -/
def nextPhaseAfterIotlbSync (t : DmaTier) (e : Nat) : FramePhase :=
  match t with
  | .nonCoherentCache => FramePhase.postDmaInvalPending e
  | _ => FramePhase.cpuOwned (e + 1)

/-- CPU write helper for `cpuOwned` frames. -/
def cpuWriteFrame (f : FrameState) (v : Nat) : FrameState :=
  match f.tier with
  | .nonCoherentCache => { f with cpuCache := some v, cacheDirty := true }
  | _ => { f with dram := v }

/-- Apply a single drained posted MMIO write at the peripheral endpoint. -/
def applyPostedWrite (dramVal : Nat) (m : MmioBusState) (op : MmioWriteOp) : MmioBusState :=
  match op with
  | .w1cAck =>
      { m with w1cIrqPending := false }
  | .doorbell =>
      { m with
        doorbellCount := m.doorbellCount + 1
        lastDeviceSeenDesc := dramVal }

/-- Drain all buffered posted MMIO writes in FIFO order (PCIe Rule A2a:
    posted writes with RO=0 do not pass earlier posted writes). -/
def drainAllPosted (dramVal : Nat) : List MmioWriteOp → MmioBusState → MmioBusState
  | [], m => m
  | op :: rest, m => drainAllPosted dramVal rest (applyPostedWrite dramVal m op)

/-- Perform a synchronous non-posted MMIO read to a chosen port kind.
    Under PCIe ordering (NPR cannot pass prior PMW), the read first drains all
    prior posted writes to the endpoint before reading the target port. -/
def mmioReadPort (dramVal : Nat) (m : MmioBusState) (port : ReadPortKind) : Nat × MmioBusState :=
  let drained := drainAllPosted dramVal m.postedQueue { m with postedQueue := [] }
  match port with
  | .roIdempotent =>
      (drained.roDeviceId, drained)
  | .r2cStatus =>
      let bit := if drained.r2cEventPending then 1 else 0
      (bit, { drained with r2cEventPending := false })

/-! ## 2. Concrete Counterexample Witnesses (Part A) -/

/-- Counterexample 1: Premature physical-frame revocation & retyping before
    IOTLB invalidation sync (`CMD_SYNC` / `QI_IWD` / `IOFENCE.C`) completes.
    The OS clears the IOMMU PTE (`pteValid := false`) and immediately retypes
    the frame to `cpuOwned` with CPU payload `0xAA`, leaving `iotlbValid = true`.
    A live peripheral DMA write hits the stale IOTLB entry and corrupts DRAM
    to `0xDE`, violating CPU-owned memory integrity (`NoDma`). -/
def buggyReclaimWithoutIotlbSync (f : FrameState) (newCpuVal : Nat) : FrameState :=
  { f with
    phase := FramePhase.cpuOwned 1
    pteValid := false
    dram := newCpuVal } -- BUG: `iotlbValid` left true!

def hwDmaWriteStep (f : FrameState) (dmaVal : Nat) : FrameState :=
  if f.pteValid || f.iotlbValid || f.inFlightDma then
    { f with dram := dmaVal }
  else
    f

def cx1Init : FrameState :=
  { tier := DmaTier.coherentIommu
    phase := FramePhase.deviceMapped 0
    dram := 0x11
    cpuCache := none
    cacheDirty := false
    pteValid := true
    iotlbValid := true
    inFlightDma := false }

theorem stale_iotlb_corrupts_retyped_cpu_frame :
    let afterBuggyReclaim := buggyReclaimWithoutIotlbSync cx1Init 0xAA
    let afterStaleDma := hwDmaWriteStep afterBuggyReclaim 0xDE
    afterBuggyReclaim.phase = FramePhase.cpuOwned 1 ∧
    afterBuggyReclaim.pteValid = false ∧
    afterBuggyReclaim.dram = 0xAA ∧
    afterStaleDma.phase = FramePhase.cpuOwned 1 ∧
    afterStaleDma.dram = 0xDE ∧
    afterStaleDma.dram ≠ 0xAA := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro h
  cases h

/-- Counterexample 2: Posted MMIO `W1C` IRQ-ack without a synchronous
    non-posted read-back flush allows CPU IRQ unmask / EOI to race with the
    still-buffered write, leaving `cpuIrqUnmasked = true ∧ w1cIrqPending = true`
    (spurious / duplicate interrupt re-entry). -/
def cx2Init : MmioBusState :=
  { postedQueue := []
    w1cIrqPending := true
    r2cEventPending := true
    roDeviceId := 0x1AF4
    doorbellCount := 0
    cpuIrqUnmasked := false
    storeBufDirty := false
    storeBufVal := 0
    lastDeviceSeenDesc := 0 }

def buggyAckAndImmediateUnmask (m : MmioBusState) : MmioBusState :=
  let m1 := { m with postedQueue := m.postedQueue ++ [MmioWriteOp.w1cAck] }
  { m1 with cpuIrqUnmasked := true } -- BUG: no read-back flush before unmask!

theorem posted_mmio_irq_ack_without_readback_races :
    let m' := buggyAckAndImmediateUnmask cx2Init
    m'.cpuIrqUnmasked = true ∧
    m'.w1cIrqPending = true ∧
    m'.postedQueue = [MmioWriteOp.w1cAck] :=
  ⟨rfl, rfl, rfl⟩

/-- Counterexample 3a: Relaxed MMIO doorbell (`writel_relaxed` omitting
    `dma_wmb()` / `__io_bw()`) lets the doorbell drain to the device while the
    CPU's descriptor store `0x42` is still buffered (`dram = 0x00`), so the
    device observes stale descriptor bytes (`0x00 ≠ 0x42`). -/
def buggyRelaxedDoorbell (dramInit newDesc : Nat) (m : MmioBusState) : MmioBusState :=
  let mBuffered := { m with storeBufDirty := true, storeBufVal := newDesc }
  let mPosted := { mBuffered with postedQueue := mBuffered.postedQueue ++ [MmioWriteOp.doorbell] }
  drainAllPosted dramInit mPosted.postedQueue { mPosted with postedQueue := [] }

theorem relaxed_doorbell_without_wmb_reads_stale_desc :
    let m' := buggyRelaxedDoorbell 0x00 0x42 cx2Init
    m'.doorbellCount = 1 ∧
    m'.storeBufDirty = true ∧
    m'.lastDeviceSeenDesc = 0x00 ∧
    m'.lastDeviceSeenDesc ≠ 0x42 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  cases h

/-- Counterexample 3b: Using a Read-to-Clear (`R2C`) status register as the
    PCIe read-back flush target drains the posted write but destructively
    clobbers `r2cEventPending` (`true → false`), whereas reading a side-effect-
    free `RO` register drains the posted write while preserving `r2cEventPending`. -/
theorem r2c_readback_clobbers_pending_status :
    let mPosted := { cx2Init with postedQueue := [MmioWriteOp.w1cAck] }
    let rBad := (mmioReadPort 0 mPosted ReadPortKind.r2cStatus).2
    let rGood := (mmioReadPort 0 mPosted ReadPortKind.roIdempotent).2
    rBad.w1cIrqPending = false ∧
    rBad.r2cEventPending = false ∧
    rGood.w1cIrqPending = false ∧
    rGood.r2cEventPending = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Counterexample 4: Non-coherent DMA (`DMA_FROM_DEVICE`) reclaiming a frame
    without post-DMA cache invalidation (`DC IVAC` / `cbo.inval`) after a
    speculatively prefetched clean cache line (`some 0x11`) causes the CPU to
    read stale `0x11` even though DRAM holds device payload `0xBB`. -/
def cx4AfterDma : FrameState :=
  { tier := DmaTier.nonCoherentCache
    phase := FramePhase.postDmaInvalPending 0
    dram := 0xBB
    cpuCache := some 0x11
    cacheDirty := false
    pteValid := false
    iotlbValid := false
    inFlightDma := false }

def buggyReclaimWithoutPostInval (f : FrameState) : FrameState :=
  { f with phase := FramePhase.cpuOwned 1 } -- BUG: skipped `DC IVAC` / `cbo.inval`!

theorem noncoherent_missing_post_inval_reads_stale_cache :
    let f' := buggyReclaimWithoutPostInval cx4AfterDma
    f'.phase = FramePhase.cpuOwned 1 ∧
    f'.dram = 0xBB ∧
    cpuReadFrame f' = 0x11 ∧
    cpuReadFrame f' ≠ f'.dram := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro h
  cases h

/-! ## 3. Guarded `DmaEpoch` + `MmioBus` Protocol & Invariant (Part B) -/

/-- No doorbell is queued in `q` while the CPU store buffer is still dirty. -/
def QueueDoorbellSafe (storeBufDirty : Bool) : List MmioWriteOp → Prop
  | [] => True
  | .w1cAck :: rest => QueueDoorbellSafe storeBufDirty rest
  | .doorbell :: rest => storeBufDirty = false ∧ QueueDoorbellSafe storeBufDirty rest

/-- Core hardware-software safety invariant across both DMA/IOTLB and MMIO seams. -/
structure HwSafeInv (s : HwSystemState) : Prop where
  frameInv :
    match s.frame.phase with
    | .cpuOwned _ =>
        s.frame.pteValid = false ∧
        s.frame.iotlbValid = false ∧
        s.frame.inFlightDma = false ∧
        (s.frame.tier = DmaTier.nonCoherentCache →
          s.frame.cacheDirty = false →
          match s.frame.cpuCache with
          | none => True
          | some v => v = s.frame.dram)
    | .dmaCleanPending _ =>
        s.frame.pteValid = false ∧
        s.frame.iotlbValid = false ∧
        s.frame.inFlightDma = false
    | .deviceMapped _ =>
        s.frame.pteValid = true ∧
        (s.frame.tier = DmaTier.nonCoherentCache → s.frame.cacheDirty = false)
    | .revokingPendingIotlbSync _ =>
        s.frame.pteValid = false ∧
        (s.frame.tier = DmaTier.nonCoherentCache → s.frame.cacheDirty = false)
    | .postDmaInvalPending _ =>
        s.frame.pteValid = false ∧
        s.frame.iotlbValid = false ∧
        s.frame.inFlightDma = false ∧
        (s.frame.tier = DmaTier.nonCoherentCache → s.frame.cacheDirty = false)
  mmioIrqInv :
    s.mmio.cpuIrqUnmasked = true →
      s.mmio.postedQueue = [] ∧ s.mmio.w1cIrqPending = false
  mmioDoorbellInv :
    QueueDoorbellSafe s.mmio.storeBufDirty s.mmio.postedQueue

/-- Guarded hardware + software transitions for `DmaEpoch` + `MmioBus`. -/
inductive SafeStep : HwSystemState → HwSystemState → Prop where
  | cpuStoreOwned (s : HwSystemState) (e v : Nat)
      (hOwned : s.frame.phase = FramePhase.cpuOwned e)
      (hNoQueuedDb : QueueDoorbellSafe true s.mmio.postedQueue) :
      SafeStep s
        { frame := cpuWriteFrame s.frame v
          mmio := { s.mmio with storeBufDirty := true, storeBufVal := v } }

  | cpuDmaWmb (s : HwSystemState) :
      SafeStep s { s with mmio := { s.mmio with storeBufDirty := false } }

  | dmaMapCoherent (s : HwSystemState) (e : Nat)
      (hOwned : s.frame.phase = FramePhase.cpuOwned e)
      (hNotNonCoh : s.frame.tier ≠ DmaTier.nonCoherentCache)
      (hCleanSb : s.mmio.storeBufDirty = false) :
      SafeStep s
        { s with frame := { s.frame with phase := FramePhase.deviceMapped e, pteValid := true } }

  | dmaPrepareNonCoherent (s : HwSystemState) (e : Nat)
      (hOwned : s.frame.phase = FramePhase.cpuOwned e)
      (hNonCoh : s.frame.tier = DmaTier.nonCoherentCache) :
      SafeStep s
        { s with frame := { s.frame with phase := FramePhase.dmaCleanPending e } }

  | dmaPreCleanAndMap (s : HwSystemState) (e : Nat)
      (hPend : s.frame.phase = FramePhase.dmaCleanPending e)
      (hNonCoh : s.frame.tier = DmaTier.nonCoherentCache) :
      SafeStep s
        { s with
          frame :=
            { s.frame with
              phase := FramePhase.deviceMapped e
              dram := flushedDramVal s.frame
              cpuCache := none
              cacheDirty := false
              pteValid := true } }

  | hwIotlbFill (s : HwSystemState)
      (hPte : s.frame.pteValid = true) :
      SafeStep s { s with frame := { s.frame with iotlbValid := true } }

  | hwSpecPrefetch (s : HwSystemState)
      (hNonCoh : s.frame.tier = DmaTier.nonCoherentCache)
      (hNotDirty : s.frame.cacheDirty = false) :
      SafeStep s { s with frame := { s.frame with cpuCache := some s.frame.dram } }

  | hwDmaWrite (s : HwSystemState) (dmaVal : Nat)
      (hAuth : s.frame.pteValid = true ∨ s.frame.iotlbValid = true ∨ s.frame.inFlightDma = true) :
      SafeStep s
        { s with frame := { s.frame with dram := dmaVal, inFlightDma := true } }

  | dmaClearPte (s : HwSystemState) (e : Nat)
      (hMapped : s.frame.phase = FramePhase.deviceMapped e) :
      SafeStep s
        { s with frame := { s.frame with phase := FramePhase.revokingPendingIotlbSync e, pteValid := false } }

  | dmaIotlbSync (s : HwSystemState) (e : Nat)
      (hRev : s.frame.phase = FramePhase.revokingPendingIotlbSync e) :
      SafeStep s
        { s with
          frame :=
            { s.frame with
              phase := nextPhaseAfterIotlbSync s.frame.tier e
              iotlbValid := false
              inFlightDma := false } }

  | dmaPostInval (s : HwSystemState) (e : Nat)
      (hPost : s.frame.phase = FramePhase.postDmaInvalPending e)
      (hNonCoh : s.frame.tier = DmaTier.nonCoherentCache) :
      SafeStep s
        { s with
          frame :=
            { s.frame with
              phase := FramePhase.cpuOwned (e + 1)
              cpuCache := none
              cacheDirty := false } }

  | mmioPostW1cAck (s : HwSystemState)
      (hMasked : s.mmio.cpuIrqUnmasked = false) :
      SafeStep s
        { s with mmio := { s.mmio with postedQueue := s.mmio.postedQueue ++ [MmioWriteOp.w1cAck] } }

  | mmioPostDoorbell (s : HwSystemState)
      (hMasked : s.mmio.cpuIrqUnmasked = false)
      (hCleanSb : s.mmio.storeBufDirty = false) :
      SafeStep s
        { s with mmio := { s.mmio with postedQueue := s.mmio.postedQueue ++ [MmioWriteOp.doorbell] } }

  | hwMmioDrainOne (s : HwSystemState) (op : MmioWriteOp) (rest : List MmioWriteOp)
      (hQueue : s.mmio.postedQueue = op :: rest) :
      SafeStep s
        { s with
          mmio := applyPostedWrite s.frame.dram { s.mmio with postedQueue := rest } op }

  | mmioReadBackFlushRo (s : HwSystemState) :
      SafeStep s
        { s with mmio := (mmioReadPort s.frame.dram s.mmio ReadPortKind.roIdempotent).2 }

  | cpuUnmaskIrq (s : HwSystemState)
      (hEmpty : s.mmio.postedQueue = [])
      (hCleared : s.mmio.w1cIrqPending = false) :
      SafeStep s { s with mmio := { s.mmio with cpuIrqUnmasked := true } }

  | cpuMaskIrq (s : HwSystemState) :
      SafeStep s { s with mmio := { s.mmio with cpuIrqUnmasked := false } }

/-- Reflexive-transitive closure of `SafeStep`. -/
inductive SafeSteps : HwSystemState → HwSystemState → Prop where
  | refl (s : HwSystemState) : SafeSteps s s
  | step {s1 s2 s3 : HwSystemState} : SafeStep s1 s2 → SafeSteps s2 s3 → SafeSteps s1 s3

/-! ## 4. Helper Lemmas -/

theorem queueDoorbellSafe_false (q : List MmioWriteOp) :
    QueueDoorbellSafe false q := by
  induction q with
  | nil => trivial
  | cons op rest ih =>
    cases op with
    | w1cAck => exact ih
    | doorbell => exact ⟨rfl, ih⟩

theorem queueDoorbellSafe_append_w1c (b : Bool) (q : List MmioWriteOp)
    (h : QueueDoorbellSafe b q) :
    QueueDoorbellSafe b (q ++ [MmioWriteOp.w1cAck]) := by
  induction q with
  | nil => trivial
  | cons op rest ih =>
    cases op with
    | w1cAck => exact ih h
    | doorbell => exact ⟨h.1, ih h.2⟩

theorem queueDoorbellSafe_append_doorbell (q : List MmioWriteOp)
    (h : QueueDoorbellSafe false q) :
    QueueDoorbellSafe false (q ++ [MmioWriteOp.doorbell]) := by
  induction q with
  | nil => exact ⟨rfl, trivial⟩
  | cons op rest ih =>
    cases op with
    | w1cAck => exact ih h
    | doorbell => exact ⟨h.1, ih h.2⟩

theorem drainAllPosted_preserves_queue (dramVal : Nat) (q : List MmioWriteOp) (m : MmioBusState) :
    (drainAllPosted dramVal q m).postedQueue = m.postedQueue := by
  induction q generalizing m with
  | nil => rfl
  | cons op rest ih =>
    unfold drainAllPosted
    rw [ih]
    cases op <;> rfl

theorem drainAllPosted_preserves_unmasked (dramVal : Nat) (q : List MmioWriteOp) (m : MmioBusState) :
    (drainAllPosted dramVal q m).cpuIrqUnmasked = m.cpuIrqUnmasked := by
  induction q generalizing m with
  | nil => rfl
  | cons op rest ih =>
    unfold drainAllPosted
    rw [ih]
    cases op <;> rfl

theorem drainAllPosted_preserves_r2c (dramVal : Nat) (q : List MmioWriteOp) (m : MmioBusState) :
    (drainAllPosted dramVal q m).r2cEventPending = m.r2cEventPending := by
  induction q generalizing m with
  | nil => rfl
  | cons op rest ih =>
    unfold drainAllPosted
    rw [ih]
    cases op <;> rfl

theorem drainAllPosted_w1c_clears (dramVal : Nat) (q : List MmioWriteOp) (m : MmioBusState) :
    (drainAllPosted dramVal (q ++ [MmioWriteOp.w1cAck]) m).w1cIrqPending = false := by
  induction q generalizing m with
  | nil => rfl
  | cons op rest ih =>
    exact ih (applyPostedWrite dramVal m op)

theorem drainAllPosted_preserves_w1c_false (dramVal : Nat) (q : List MmioWriteOp) (m : MmioBusState)
    (h : m.w1cIrqPending = false) :
    (drainAllPosted dramVal q m).w1cIrqPending = false := by
  induction q generalizing m with
  | nil => exact h
  | cons op rest ih =>
    apply ih
    cases op with
    | w1cAck => rfl
    | doorbell => exact h

/-! ## 5. Main Preservation, `NoDma` Discharge, and `OpaqueMmio` Refinement Theorems -/

theorem safeStep_preserves_inv {s1 s2 : HwSystemState}
    (hInv : HwSafeInv s1) (hStep : SafeStep s1 s2) :
    HwSafeInv s2 := by
  cases hStep with
  | cpuStoreOwned e v hOwned hNoQueuedDb =>
    have hF := hInv.frameInv
    rw [hOwned] at hF
    apply HwSafeInv.mk
    case frameInv =>
      unfold cpuWriteFrame
      cases hTier : s1.frame.tier with
      | coherentIommu =>
        dsimp; rw [hOwned]; dsimp
        refine ⟨hF.1, hF.2.1, hF.2.2.1, ?_⟩
        intro hNC; cases hNC
      | nonCoherentCache =>
        dsimp; rw [hOwned]; dsimp
        refine ⟨hF.1, hF.2.1, hF.2.2.1, ?_⟩
        intro _ hClean; cases hClean
      | byzantineIsolated =>
        dsimp; rw [hOwned]; dsimp
        refine ⟨hF.1, hF.2.1, hF.2.2.1, ?_⟩
        intro hNC; cases hNC
    case mmioIrqInv => exact hInv.mmioIrqInv
    case mmioDoorbellInv => exact hNoQueuedDb
  | cpuDmaWmb =>
    exact ⟨hInv.frameInv, hInv.mmioIrqInv, queueDoorbellSafe_false s1.mmio.postedQueue⟩
  | dmaMapCoherent e hOwned hNotNonCoh hCleanSb =>
    have hF := hInv.frameInv
    rw [hOwned] at hF
    refine ⟨?_, hInv.mmioIrqInv, hInv.mmioDoorbellInv⟩
    refine ⟨rfl, ?_⟩
    intro hNC
    exact False.elim (hNotNonCoh hNC)
  | dmaPrepareNonCoherent e hOwned hNonCoh =>
    have hF := hInv.frameInv
    rw [hOwned] at hF
    exact ⟨⟨hF.1, hF.2.1, hF.2.2.1⟩, hInv.mmioIrqInv, hInv.mmioDoorbellInv⟩
  | dmaPreCleanAndMap e hPend hNonCoh =>
    exact ⟨⟨rfl, fun _ => rfl⟩, hInv.mmioIrqInv, hInv.mmioDoorbellInv⟩
  | hwIotlbFill hPte =>
    have hF := hInv.frameInv
    refine ⟨?_, hInv.mmioIrqInv, hInv.mmioDoorbellInv⟩
    cases hPh : s1.frame.phase with
    | cpuOwned e => rw [hPh] at hF; rw [hF.1] at hPte; cases hPte
    | dmaCleanPending e => rw [hPh] at hF; rw [hF.1] at hPte; cases hPte
    | deviceMapped e => rw [hPh] at hF; exact hF
    | revokingPendingIotlbSync e => rw [hPh] at hF; rw [hF.1] at hPte; cases hPte
    | postDmaInvalPending e => rw [hPh] at hF; rw [hF.1] at hPte; cases hPte
  | hwSpecPrefetch hNonCoh hNotDirty =>
    have hF := hInv.frameInv
    refine ⟨?_, hInv.mmioIrqInv, hInv.mmioDoorbellInv⟩
    cases hPh : s1.frame.phase with
    | cpuOwned e =>
      rw [hPh] at hF
      exact ⟨hF.1, hF.2.1, hF.2.2.1, fun _ _ => rfl⟩
    | dmaCleanPending e => rw [hPh] at hF; exact hF
    | deviceMapped e => rw [hPh] at hF; exact hF
    | revokingPendingIotlbSync e => rw [hPh] at hF; exact hF
    | postDmaInvalPending e => rw [hPh] at hF; exact hF
  | hwDmaWrite dmaVal hAuth =>
    have hF := hInv.frameInv
    refine ⟨?_, hInv.mmioIrqInv, hInv.mmioDoorbellInv⟩
    cases hPh : s1.frame.phase with
    | cpuOwned e =>
      rw [hPh] at hF
      cases hAuth with
      | inl h1 => rw [hF.1] at h1; cases h1
      | inr h23 =>
        cases h23 with
        | inl h2 => rw [hF.2.1] at h2; cases h2
        | inr h3 => rw [hF.2.2.1] at h3; cases h3
    | dmaCleanPending e =>
      rw [hPh] at hF
      cases hAuth with
      | inl h1 => rw [hF.1] at h1; cases h1
      | inr h23 =>
        cases h23 with
        | inl h2 => rw [hF.2.1] at h2; cases h2
        | inr h3 => rw [hF.2.2] at h3; cases h3
    | deviceMapped e => rw [hPh] at hF; exact hF
    | revokingPendingIotlbSync e => rw [hPh] at hF; exact hF
    | postDmaInvalPending e =>
      rw [hPh] at hF
      cases hAuth with
      | inl h1 => rw [hF.1] at h1; cases h1
      | inr h23 =>
        cases h23 with
        | inl h2 => rw [hF.2.1] at h2; cases h2
        | inr h3 => rw [hF.2.2.1] at h3; cases h3
  | dmaClearPte e hMapped =>
    have hF := hInv.frameInv
    rw [hMapped] at hF
    exact ⟨⟨rfl, hF.2⟩, hInv.mmioIrqInv, hInv.mmioDoorbellInv⟩
  | dmaIotlbSync e hRev =>
    have hF := hInv.frameInv
    rw [hRev] at hF
    refine ⟨?_, hInv.mmioIrqInv, hInv.mmioDoorbellInv⟩
    dsimp
    unfold nextPhaseAfterIotlbSync
    cases hTier : s1.frame.tier with
    | coherentIommu =>
      dsimp
      refine ⟨hF.1, rfl, rfl, ?_⟩
      intro hBad; cases hBad
    | nonCoherentCache =>
      dsimp
      exact ⟨hF.1, rfl, rfl, fun _ => hF.2 hTier⟩
    | byzantineIsolated =>
      dsimp
      refine ⟨hF.1, rfl, rfl, ?_⟩
      intro hBad; cases hBad
  | dmaPostInval e hPost hNonCoh =>
    have hF := hInv.frameInv
    rw [hPost] at hF
    exact ⟨⟨hF.1, hF.2.1, hF.2.2.1, fun _ _ => trivial⟩, hInv.mmioIrqInv, hInv.mmioDoorbellInv⟩
  | mmioPostW1cAck hMasked =>
    refine ⟨hInv.frameInv, ?_, queueDoorbellSafe_append_w1c _ _ hInv.mmioDoorbellInv⟩
    intro hUnm; dsimp at hUnm; rw [hMasked] at hUnm; cases hUnm
  | mmioPostDoorbell hMasked hCleanSb =>
    have hQ := hInv.mmioDoorbellInv
    rw [hCleanSb] at hQ
    apply HwSafeInv.mk
    case frameInv => exact hInv.frameInv
    case mmioIrqInv =>
      intro hUnm; dsimp at hUnm; rw [hMasked] at hUnm; cases hUnm
    case mmioDoorbellInv =>
      dsimp; rw [hCleanSb]; exact queueDoorbellSafe_append_doorbell _ hQ
  | hwMmioDrainOne op rest hQueue =>
    have hQ := hInv.mmioDoorbellInv
    rw [hQueue] at hQ
    apply HwSafeInv.mk
    case frameInv => exact hInv.frameInv
    case mmioIrqInv =>
      intro hUnm
      have hPrev : s1.mmio.cpuIrqUnmasked = true := by
        cases op <;> exact hUnm
      have hEmpty := (hInv.mmioIrqInv hPrev).1
      rw [hQueue] at hEmpty
      cases hEmpty
    case mmioDoorbellInv =>
      cases op with
      | w1cAck => exact hQ
      | doorbell => exact hQ.2
  | mmioReadBackFlushRo =>
    apply HwSafeInv.mk
    case frameInv => exact hInv.frameInv
    case mmioIrqInv =>
      intro hUnm
      dsimp at hUnm
      unfold mmioReadPort at hUnm
      dsimp at hUnm
      rw [drainAllPosted_preserves_unmasked] at hUnm
      have hPrev := hInv.mmioIrqInv hUnm
      dsimp
      unfold mmioReadPort
      dsimp
      exact ⟨drainAllPosted_preserves_queue _ _ _, drainAllPosted_preserves_w1c_false _ _ _ hPrev.2⟩
    case mmioDoorbellInv =>
      dsimp
      unfold mmioReadPort
      dsimp
      rw [drainAllPosted_preserves_queue]
      trivial
  | cpuUnmaskIrq hEmpty hCleared =>
    exact ⟨hInv.frameInv, fun _ => ⟨hEmpty, hCleared⟩, hInv.mmioDoorbellInv⟩
  | cpuMaskIrq =>
    refine ⟨hInv.frameInv, ?_, hInv.mmioDoorbellInv⟩
    intro h; cases h

theorem safeSteps_preserves_inv {s1 s2 : HwSystemState}
    (hInv : HwSafeInv s1) (hSteps : SafeSteps s1 s2) :
    HwSafeInv s2 := by
  induction hSteps with
  | refl _ => exact hInv
  | step h1 _ ih => exact ih (safeStep_preserves_inv hInv h1)

/-- **Theorem 1 — Per-Frame `NoDma` Discharge:**
    Under `HwSafeInv`, whenever a physical frame is in `cpuOwned e`, no
    hardware DMA write (`hwDmaWrite`) or IOTLB fill (`hwIotlbFill`) is even
    enabled on that frame. Thus `NoDma` is *discharged* from the global TCB
    for every `cpuOwned` frame without assuming DMA hardware is absent! -/
theorem discharge_noDma_blocks_hwDmaWrite {s1 : HwSystemState} {e : Nat}
    (hInv : HwSafeInv s1)
    (hOwned : s1.frame.phase = FramePhase.cpuOwned e)
    (hAuth : s1.frame.pteValid = true ∨ s1.frame.iotlbValid = true ∨ s1.frame.inFlightDma = true) :
    False := by
  have hF := hInv.frameInv
  rw [hOwned] at hF
  cases hAuth with
  | inl h1 => rw [hF.1] at h1; cases h1
  | inr h23 =>
    cases h23 with
    | inl h2 => rw [hF.2.1] at h2; cases h2
    | inr h3 => rw [hF.2.2.1] at h3; cases h3

/-- Hardware-autonomous transitions (DMA, IOTLB fill, speculative prefetch,
    posted-MMIO fabric drain). -/
inductive HwAutonomousStep : HwSystemState → HwSystemState → Prop where
  | iotlbFill (s : HwSystemState) (h : s.frame.pteValid = true) :
      HwAutonomousStep s { s with frame := { s.frame with iotlbValid := true } }
  | dmaWrite (s : HwSystemState) (v : Nat)
      (h : s.frame.pteValid = true ∨ s.frame.iotlbValid = true ∨ s.frame.inFlightDma = true) :
      HwAutonomousStep s { s with frame := { s.frame with dram := v, inFlightDma := true } }
  | specPrefetch (s : HwSystemState)
      (hNC : s.frame.tier = DmaTier.nonCoherentCache) (hClean : s.frame.cacheDirty = false) :
      HwAutonomousStep s { s with frame := { s.frame with cpuCache := some s.frame.dram } }
  | mmioDrain (s : HwSystemState) (op : MmioWriteOp) (rest : List MmioWriteOp)
      (hQ : s.mmio.postedQueue = op :: rest) :
      HwAutonomousStep s
        { s with mmio := applyPostedWrite s.frame.dram { s.mmio with postedQueue := rest } op }

/-- Every hardware-autonomous transition preserves `phase`, `dram`, and
    `cpuReadFrame` on any `cpuOwned` frame under `HwSafeInv`. -/
theorem discharge_noDma_cpuOwned_view_invariant {s1 s2 : HwSystemState} {e : Nat}
    (hInv : HwSafeInv s1)
    (hOwned : s1.frame.phase = FramePhase.cpuOwned e)
    (hHw : HwAutonomousStep s1 s2) :
    s2.frame.phase = FramePhase.cpuOwned e ∧
    s2.frame.dram = s1.frame.dram ∧
    cpuReadFrame s2.frame = cpuReadFrame s1.frame := by
  have hF := hInv.frameInv
  rw [hOwned] at hF
  cases hHw with
  | iotlbFill hPte =>
    rw [hF.1] at hPte; cases hPte
  | dmaWrite v hAuth =>
    exact False.elim (discharge_noDma_blocks_hwDmaWrite hInv hOwned hAuth)
  | specPrefetch hNC hClean =>
    have hMatch := hF.2.2.2 hNC hClean
    refine ⟨hOwned, rfl, ?_⟩
    unfold cpuReadFrame
    dsimp
    rw [hNC]
    cases hC : s1.frame.cpuCache with
    | none => rfl
    | some cv =>
      rw [hC] at hMatch
      exact hMatch.symm
  | mmioDrain op rest hQ =>
    exact ⟨hOwned, rfl, rfl⟩

/-- **Theorem 2 — `OpaqueMmio` Discharge via Posted-Write + `RO` Read-Back Flush Refinement:**
    From any safe state with masked CPU IRQ, executing the concrete 3-step PCIe
    protocol (`mmioPostW1cAck` → `mmioReadBackFlushRo` → `cpuUnmaskIrq`)
    is a valid `SafeSteps` trace that:
      (1) drains `postedQueue` to `[]`,
      (2) clears `w1cIrqPending` to `false` at the endpoint,
      (3) unmasks CPU IRQ safely (`HwSafeInv sFinal`), AND
      (4) preserves `r2cEventPending` untouched (no `R2C` clobbering!). -/
theorem discharge_opaqueMmio_w1c_readback_refinement (s : HwSystemState)
    (hInv : HwSafeInv s)
    (hMasked : s.mmio.cpuIrqUnmasked = false) :
    Exists (fun sFinal : HwSystemState =>
      SafeSteps s sFinal ∧
      HwSafeInv sFinal ∧
      sFinal.mmio.postedQueue = [] ∧
      sFinal.mmio.w1cIrqPending = false ∧
      sFinal.mmio.cpuIrqUnmasked = true ∧
      sFinal.mmio.r2cEventPending = s.mmio.r2cEventPending) := by
  let s1 : HwSystemState :=
    { s with mmio := { s.mmio with postedQueue := s.mmio.postedQueue ++ [MmioWriteOp.w1cAck] } }
  let s2 : HwSystemState :=
    { s1 with mmio := (mmioReadPort s1.frame.dram s1.mmio ReadPortKind.roIdempotent).2 }
  let s3 : HwSystemState :=
    { s2 with mmio := { s2.mmio with cpuIrqUnmasked := true } }
  have hStep1 : SafeStep s s1 := SafeStep.mmioPostW1cAck s hMasked
  have hStep2 : SafeStep s1 s2 := SafeStep.mmioReadBackFlushRo s1
  have hEmpty2 : s2.mmio.postedQueue = [] := by
    show (drainAllPosted s1.frame.dram s1.mmio.postedQueue { s1.mmio with postedQueue := [] }).postedQueue = []
    exact drainAllPosted_preserves_queue _ _ _
  have hClr2 : s2.mmio.w1cIrqPending = false := by
    show (drainAllPosted s.frame.dram (s.mmio.postedQueue ++ [MmioWriteOp.w1cAck]) { s1.mmio with postedQueue := [] }).w1cIrqPending = false
    exact drainAllPosted_w1c_clears _ _ _
  have hR2c2 : s2.mmio.r2cEventPending = s.mmio.r2cEventPending := by
    show (drainAllPosted s.frame.dram (s.mmio.postedQueue ++ [MmioWriteOp.w1cAck]) { s1.mmio with postedQueue := [] }).r2cEventPending = s.mmio.r2cEventPending
    exact drainAllPosted_preserves_r2c _ _ _
  have hStep3 : SafeStep s2 s3 := SafeStep.cpuUnmaskIrq s2 hEmpty2 hClr2
  have hTrace : SafeSteps s s3 :=
    SafeSteps.step hStep1 (SafeSteps.step hStep2 (SafeSteps.step hStep3 (SafeSteps.refl s3)))
  exact Exists.intro s3 ⟨hTrace, safeSteps_preserves_inv hInv hTrace, hEmpty2, hClr2, rfl, hR2c2⟩

/-- **Theorem 3 — End-to-End Non-Coherent DMA Epoch Roundtrip (`cpuOwned e →* cpuOwned (e + 1)`):**
    Even when hardware performs an IOTLB fill, an asynchronous DMA write
    `dmaPayload`, and a speculative clean cache prefetch mid-transfer, the
    guarded Tier-2 lifecycle (`dmaPrepareNonCoherent → dmaPreCleanAndMap →
    hwIotlbFill → hwDmaWrite → dmaClearPte → hwSpecPrefetch → dmaIotlbSync →
    dmaPostInval`) re-establishes `HwSafeInv`, advances the epoch to `e + 1`,
    re-discharges `NoDma`, and guarantees `cpuReadFrame = dmaPayload`. -/
theorem noncoherent_dma_epoch_roundtrip (s : HwSystemState) (e dmaPayload : Nat)
    (hInv : HwSafeInv s)
    (hOwned : s.frame.phase = FramePhase.cpuOwned e)
    (hNonCoh : s.frame.tier = DmaTier.nonCoherentCache) :
    Exists (fun sFinal : HwSystemState =>
      SafeSteps s sFinal ∧
      HwSafeInv sFinal ∧
      sFinal.frame.phase = FramePhase.cpuOwned (e + 1) ∧
      sFinal.frame.pteValid = false ∧
      sFinal.frame.iotlbValid = false ∧
      sFinal.frame.inFlightDma = false ∧
      cpuReadFrame sFinal.frame = dmaPayload) := by
  let s1 := { s with frame := { s.frame with phase := FramePhase.dmaCleanPending e } }
  let s2 :=
    { s1 with
      frame :=
        { s1.frame with
          phase := FramePhase.deviceMapped e
          dram := flushedDramVal s1.frame
          cpuCache := none
          cacheDirty := false
          pteValid := true } }
  let s3 := { s2 with frame := { s2.frame with iotlbValid := true } }
  let s4 := { s3 with frame := { s3.frame with dram := dmaPayload, inFlightDma := true } }
  let s5 := { s4 with frame := { s4.frame with phase := FramePhase.revokingPendingIotlbSync e, pteValid := false } }
  let s6 := { s5 with frame := { s5.frame with cpuCache := some s5.frame.dram } }
  let s7 :=
    { s6 with
      frame :=
        { s6.frame with
          phase := nextPhaseAfterIotlbSync s6.frame.tier e
          iotlbValid := false
          inFlightDma := false } }
  let s8 :=
    { s7 with
      frame :=
        { s7.frame with
          phase := FramePhase.cpuOwned (e + 1)
          cpuCache := none
          cacheDirty := false } }
  have h1 : SafeStep s s1 := SafeStep.dmaPrepareNonCoherent s e hOwned hNonCoh
  have h2 : SafeStep s1 s2 := SafeStep.dmaPreCleanAndMap s1 e rfl hNonCoh
  have h3 : SafeStep s2 s3 := SafeStep.hwIotlbFill s2 rfl
  have h4 : SafeStep s3 s4 := SafeStep.hwDmaWrite s3 dmaPayload (Or.inl rfl)
  have h5 : SafeStep s4 s5 := SafeStep.dmaClearPte s4 e rfl
  have h6 : SafeStep s5 s6 := SafeStep.hwSpecPrefetch s5 hNonCoh rfl
  have h7 : SafeStep s6 s7 := SafeStep.dmaIotlbSync s6 e rfl
  have hPh7 : s7.frame.phase = FramePhase.postDmaInvalPending e := by
    change nextPhaseAfterIotlbSync s.frame.tier e = FramePhase.postDmaInvalPending e
    unfold nextPhaseAfterIotlbSync
    rw [hNonCoh]
  have h8 : SafeStep s7 s8 := SafeStep.dmaPostInval s7 e hPh7 hNonCoh
  have hTrace : SafeSteps s s8 :=
    SafeSteps.step h1 (SafeSteps.step h2 (SafeSteps.step h3 (SafeSteps.step h4
      (SafeSteps.step h5 (SafeSteps.step h6 (SafeSteps.step h7 (SafeSteps.step h8
        (SafeSteps.refl s8))))))))
  have hView : cpuReadFrame s8.frame = dmaPayload := by
    unfold cpuReadFrame
    change (match s.frame.tier, (none : Option Nat) with
            | DmaTier.nonCoherentCache, some v => v
            | _, _ => dmaPayload) = dmaPayload
    rw [hNonCoh]
  exact Exists.intro s8 ⟨hTrace, safeSteps_preserves_inv hInv hTrace, rfl, rfl, rfl, rfl, hView⟩

/-- **Theorem 4 — End-to-End Coherent IOMMU DMA Epoch Roundtrip (`cpuOwned e →* cpuOwned (e + 1)`):**
    Tier 1 / Tier 3 coherent DMA skips cache maintenance (`dmaPreClean`/`dmaPostInval`)
    but MUST execute `dma_wmb`, `dmaClearPte`, and synchronous `dmaIotlbSync`
    before reclaiming the frame to `cpuOwned (e + 1)`. -/
theorem coherent_dma_epoch_roundtrip (s : HwSystemState) (e dmaPayload : Nat)
    (hInv : HwSafeInv s)
    (hOwned : s.frame.phase = FramePhase.cpuOwned e)
    (hCoh : s.frame.tier = DmaTier.coherentIommu) :
    Exists (fun sFinal : HwSystemState =>
      SafeSteps s sFinal ∧
      HwSafeInv sFinal ∧
      sFinal.frame.phase = FramePhase.cpuOwned (e + 1) ∧
      sFinal.frame.pteValid = false ∧
      sFinal.frame.iotlbValid = false ∧
      sFinal.frame.inFlightDma = false ∧
      cpuReadFrame sFinal.frame = dmaPayload) := by
  let s1 := { s with mmio := { s.mmio with storeBufDirty := false } }
  let s2 := { s1 with frame := { s1.frame with phase := FramePhase.deviceMapped e, pteValid := true } }
  let s3 := { s2 with frame := { s2.frame with iotlbValid := true } }
  let s4 := { s3 with frame := { s3.frame with dram := dmaPayload, inFlightDma := true } }
  let s5 := { s4 with frame := { s4.frame with phase := FramePhase.revokingPendingIotlbSync e, pteValid := false } }
  let s6 :=
    { s5 with
      frame :=
        { s5.frame with
          phase := nextPhaseAfterIotlbSync s5.frame.tier e
          iotlbValid := false
          inFlightDma := false } }
  have hNotNC : s1.frame.tier ≠ DmaTier.nonCoherentCache := by
    intro h; change s.frame.tier = DmaTier.nonCoherentCache at h; rw [hCoh] at h; cases h
  have h1 : SafeStep s s1 := SafeStep.cpuDmaWmb s
  have h2 : SafeStep s1 s2 := SafeStep.dmaMapCoherent s1 e hOwned hNotNC rfl
  have h3 : SafeStep s2 s3 := SafeStep.hwIotlbFill s2 rfl
  have h4 : SafeStep s3 s4 := SafeStep.hwDmaWrite s3 dmaPayload (Or.inl rfl)
  have h5 : SafeStep s4 s5 := SafeStep.dmaClearPte s4 e rfl
  have h6 : SafeStep s5 s6 := SafeStep.dmaIotlbSync s5 e rfl
  have hTrace : SafeSteps s s6 :=
    SafeSteps.step h1 (SafeSteps.step h2 (SafeSteps.step h3 (SafeSteps.step h4
      (SafeSteps.step h5 (SafeSteps.step h6 (SafeSteps.refl s6))))))
  have hPh6 : s6.frame.phase = FramePhase.cpuOwned (e + 1) := by
    change nextPhaseAfterIotlbSync s.frame.tier e = FramePhase.cpuOwned (e + 1)
    unfold nextPhaseAfterIotlbSync
    rw [hCoh]
  have hView : cpuReadFrame s6.frame = dmaPayload := by
    unfold cpuReadFrame
    change (match s.frame.tier, s.frame.cpuCache with
            | DmaTier.nonCoherentCache, some v => v
            | _, _ => dmaPayload) = dmaPayload
    rw [hCoh]
  exact Exists.intro s6 ⟨hTrace, safeSteps_preserves_inv hInv hTrace, hPh6, rfl, rfl, rfl, hView⟩

end DmaIotlbMmioDischarge

#print axioms DmaIotlbMmioDischarge.stale_iotlb_corrupts_retyped_cpu_frame
#print axioms DmaIotlbMmioDischarge.posted_mmio_irq_ack_without_readback_races
#print axioms DmaIotlbMmioDischarge.relaxed_doorbell_without_wmb_reads_stale_desc
#print axioms DmaIotlbMmioDischarge.r2c_readback_clobbers_pending_status
#print axioms DmaIotlbMmioDischarge.noncoherent_missing_post_inval_reads_stale_cache
#print axioms DmaIotlbMmioDischarge.safeStep_preserves_inv
#print axioms DmaIotlbMmioDischarge.safeSteps_preserves_inv
#print axioms DmaIotlbMmioDischarge.discharge_noDma_blocks_hwDmaWrite
#print axioms DmaIotlbMmioDischarge.discharge_noDma_cpuOwned_view_invariant
#print axioms DmaIotlbMmioDischarge.discharge_opaqueMmio_w1c_readback_refinement
#print axioms DmaIotlbMmioDischarge.noncoherent_dma_epoch_roundtrip
#print axioms DmaIotlbMmioDischarge.coherent_dma_epoch_roundtrip
