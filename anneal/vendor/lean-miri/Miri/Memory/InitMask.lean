import Lean
import Miri.Memory.AllocRange

/-! Checked Lean model of the pinned rustc allocation initialization mask. -/

namespace Miri.Memory
open Miri.ABI

abbrev InitMaskError := MemoryError

private def maxSizeBytes : Nat := 18446744073709551615
private def wordMask : Nat := 18446744073709551615
private def blockSize : Nat := 64
private def sizeBytes (size : Size) : Nat := size.bytes.toNat

private def sizeFromNat (n : Nat) : Except InitMaskError Size :=
  if n ≤ maxSizeBytes then .ok (Size.ofBytes (UInt64.ofNat n))
  else .error (.sizeFromNatOverflow n)

private def bitAt (word bit : Nat) : Bool := Nat.testBit word bit

private def setWordRange (word lo hi : Nat) (state : Bool) : UInt64 :=
  let mask := (2 ^ hi - 1) - (2 ^ lo - 1)
  UInt64.ofNat (if state then Nat.lor word mask else Nat.land word (wordMask - mask))

structure InitMaskMaterialized where
  blocks : Array UInt64
  deriving DecidableEq, Repr

inductive InitMaskBlocks where
  | Lazy (state : Bool)
  | Materialized (blocks : InitMaskMaterialized)
  deriving DecidableEq, Repr

structure InitMask where
  blocks : InitMaskBlocks
  len : Size
  deriving DecidableEq, Repr

inductive InitChunk where
  | Init (start finish : Size)
  | Uninit (start finish : Size)
  deriving DecidableEq, Repr

structure InitChunkIter where
  initMask : InitMask
  isInit : Bool
  start : Size
  finish : Size

structure InitCopy where
  initial : Bool
  ranges : Array UInt64
  deriving DecidableEq, Repr

namespace InitMaskMaterialized

def bitIndex (offset : Size) : Nat × Nat :=
  let bytes := sizeBytes offset
  (bytes / blockSize, bytes % blockSize)

private def sizeFromBitIndex (block bit : Nat) : Except InitMaskError Size :=
  sizeFromNat (block * blockSize + bit)

private def getBlock (self : InitMaskMaterialized) (block : Nat) :
    Except InitMaskError UInt64 :=
  match self.blocks[block]? with
  | some word => .ok word
  | none => .error (.blockIndexOutOfBounds block self.blocks.size)

private def setBlock (blocks : Array UInt64) (index : Nat) (word : UInt64) :
    Except InitMaskError (Array UInt64) :=
  if h : index < blocks.size then
    .ok (blocks.set index word h)
  else
    .error (.blockIndexOutOfBounds index blocks.size)

private def get (self : InitMaskMaterialized) (offset : Size) :
    Except InitMaskError Bool := do
  let (block, bit) := bitIndex offset
  let word ← getBlock self block
  return bitAt word.toNat bit

private def setRangeInbounds (self : InitMaskMaterialized) (start finish : Size)
    (newState : Bool) : Except InitMaskError InitMaskMaterialized := do
  let (blockA, bitA) := bitIndex start
  let (blockB, bitB) := bitIndex finish
  let mut words := self.blocks
  if blockA == blockB then
    let endBit := if bitB == 0 then 64 else bitB
    let word ← getBlock ⟨words⟩ blockA
    words ← setBlock words blockA (setWordRange word.toNat bitA endBit newState)
  else if newState then
    let wordA ← getBlock ⟨words⟩ blockA
    words ← setBlock words blockA (setWordRange wordA.toNat bitA 64 true)
    if bitB != 0 then
      let wordB ← getBlock ⟨words⟩ blockB
      words ← setBlock words blockB (setWordRange wordB.toNat 0 bitB true)
    for block in [blockA + 1:blockB] do
      words ← setBlock words block (UInt64.ofNat wordMask)
  else
    let wordA ← getBlock ⟨words⟩ blockA
    words ← setBlock words blockA (setWordRange wordA.toNat bitA 64 false)
    if bitB != 0 then
      let wordB ← getBlock ⟨words⟩ blockB
      words ← setBlock words blockB (setWordRange wordB.toNat 0 bitB false)
    for block in [blockA + 1:blockB] do
      words ← setBlock words block 0
  return ⟨words⟩

private def grow (self : InitMaskMaterialized) (len amount : Size)
    (newState : Bool) : Except InitMaskError InitMaskMaterialized := do
  let amountBytes := sizeBytes amount
  if amountBytes == 0 then return self
  let lenBytes := sizeBytes len
  let capacity := self.blocks.size * blockSize
  if capacity < lenBytes then
    throw (.blockCapacityTooSmall lenBytes capacity)
  let unusedTrailingBits := capacity - lenBytes
  let mut words := self.blocks
  if amountBytes > unusedTrailingBits then
    let additionalBlocks := amountBytes / blockSize + 1
    let word := if newState then UInt64.ofNat wordMask else 0
    words := words ++ Array.replicate additionalBlocks word
  if unusedTrailingBits > 0 then
    let tailEnd ← sizeFromNat (lenBytes + unusedTrailingBits)
    let grown ← setRangeInbounds ⟨words⟩ len tailEnd newState
    words := grown.blocks
  return ⟨words⟩

private def firstSetBit (word startBit : Nat) : Option Nat :=
  ((List.range (64 - startBit)).find? fun offset =>
    bitAt word (startBit + offset)).map (· + startBit)

private def searchBlock (word : UInt64) (block startBit : Nat)
    (isInit : Bool) : Except InitMaskError (Option Size) := do
  let bits := if isInit then word.toNat else wordMask - word.toNat
  match firstSetBit bits startBit with
  | none => return none
  | some bit => return some (← sizeFromBitIndex block bit)

private def findBitFast (self : InitMaskMaterialized) (start finish : Size)
    (isInit : Bool) : Except InitMaskError (Option Size) := do
  let startBytes := sizeBytes start
  let finishBytes := sizeBytes finish
  if startBytes >= finishBytes then return none
  let (startBlock, startBit) := bitIndex start
  let endInclusive ← sizeFromNat (finishBytes - 1)
  let (endBlockInclusive, _) := bitIndex endInclusive
  let first ← searchBlock (← getBlock self startBlock) startBlock startBit isInit
  match first with
  | some index =>
    if sizeBytes index < finishBytes then return some index else return none
  | none =>
    if startBlock < endBlockInclusive then
      for block in [startBlock + 1:endBlockInclusive + 1] do
        match ← searchBlock (← getBlock self block) block 0 isInit with
        | some index =>
          if sizeBytes index < finishBytes then return some index else return none
        | none => pure ()
    return none

private def findBit (self : InitMaskMaterialized) (start finish : Size)
    (isInit : Bool) : Except InitMaskError (Option Size) :=
  findBitFast self start finish isInit

end InitMaskMaterialized

namespace InitChunk

def isInit : InitChunk → Bool
  | .Init _ _ => true
  | .Uninit _ _ => false

def range (chunk : InitChunk) : Except InitMaskError AllocRange := do
  match chunk with
  | .Init start finish | .Uninit start finish => AllocRange.fromEndpoints start finish

end InitChunk

namespace InitChunkIter

def next? (iter : InitChunkIter) :
    Except InitMaskError (Option (InitChunk × InitChunkIter)) := do
  if iter.start.bytes > iter.finish.bytes ||
      iter.finish.bytes > iter.initMask.len.bytes then
    throw (.invalidChunkIterator iter.start iter.finish)
  if sizeBytes iter.start >= sizeBytes iter.finish then return none
  match iter.initMask.blocks with
  | .Lazy state =>
    if state != iter.isInit then
      throw (.invalidChunkIterator iter.start iter.finish)
  | .Materialized _ => pure ()
  let chunkEnd ← do
    match iter.initMask.blocks with
    | .Lazy _ => pure iter.finish
    | .Materialized blocks => do
      let found ← blocks.findBit iter.start iter.finish (!iter.isInit)
      pure (found.getD iter.finish)
  if chunkEnd.bytes ≤ iter.start.bytes then
    throw (.invalidChunkIterator iter.start iter.finish)
  let chunk := if iter.isInit then InitChunk.Init iter.start chunkEnd
    else InitChunk.Uninit iter.start chunkEnd
  return some (chunk, { iter with isInit := !iter.isInit, start := chunkEnd })

end InitChunkIter

namespace InitCopy

def noBytesInit (defined : InitCopy) : Bool :=
  !defined.initial && defined.ranges.size == 1

end InitCopy

namespace InitMask

def new (size : Size) (state : Bool) : InitMask :=
  ⟨.Lazy state, size⟩

def materializedBlockCount (self : InitMask) : Nat :=
  match self.blocks with
  | .Lazy _ => 0
  | .Materialized blocks => blocks.blocks.size

def materializedWords (self : InitMask) : Option (Array UInt64) :=
  match self.blocks with
  | .Lazy _ => none
  | .Materialized blocks => some blocks.blocks

private def materialize (self : InitMask) :
    Except InitMaskError InitMaskMaterialized := do
  match self.blocks with
  | .Lazy state => InitMaskMaterialized.grow ⟨#[]⟩ (Size.ofBytes 0) self.len state
  | .Materialized blocks => return blocks

def get (self : InitMask) (index : Size) : Except InitMaskError Bool := do
  match self.blocks with
  | .Lazy state => return state
  | .Materialized blocks => blocks.get index

def isRangeInitialized (self : InitMask) (range : AllocRange) :
    Except InitMaskError (Except AllocRange Unit) := do
  let finish ← range.endExclusive
  if finish.bytes > self.len.bytes then
    return .error (← AllocRange.fromEndpoints self.len finish)
  match self.blocks with
  | .Lazy state =>
    if state then return .ok () else return .error range
  | .Materialized blocks =>
    match ← blocks.findBit range.start finish false with
    | none => return .ok ()
    | some uninitStart =>
      let uninitEnd := (← blocks.findBit uninitStart finish true).getD finish
      return .error (← AllocRange.fromEndpoints uninitStart uninitEnd)

def setRange (self : InitMask) (range : AllocRange)
    (newState : Bool) : Except InitMaskError InitMask := do
  let start := range.start
  let finish ← range.endExclusive
  let fullOverwrite := start.bytes = 0 ∧ self.len.bytes ≤ finish.bytes
  match self.blocks with
  | .Lazy state =>
    if fullOverwrite then return ⟨.Lazy newState, finish⟩
    else if state == newState then
      if finish.bytes > self.len.bytes then return ⟨.Lazy state, finish⟩
      else return self
    else
      let blocks ← materialize self
      if finish.bytes ≤ self.len.bytes then
        return ⟨.Materialized (← blocks.setRangeInbounds start finish newState), self.len⟩
      else
        let firstPart ← if start.bytes < self.len.bytes then
          blocks.setRangeInbounds start self.len newState else pure blocks
        let amount ← (Size.sub finish self.len).mapError MemoryError.sizeError
        return ⟨.Materialized (← firstPart.grow self.len amount newState), finish⟩
  | .Materialized oldBlocks =>
    if fullOverwrite then return ⟨.Lazy newState, finish⟩
    else if finish.bytes ≤ self.len.bytes then
      return ⟨.Materialized (← oldBlocks.setRangeInbounds start finish newState), self.len⟩
    else
      let firstPart ← if start.bytes < self.len.bytes then
        oldBlocks.setRangeInbounds start self.len newState else pure oldBlocks
      let amount ← (Size.sub finish self.len).mapError MemoryError.sizeError
      return ⟨.Materialized (← firstPart.grow self.len amount newState), finish⟩

def rangeAsInitChunks (self : InitMask) (range : AllocRange) :
    Except InitMaskError InitChunkIter := do
  let finish ← range.endExclusive
  if finish.bytes > self.len.bytes then
    throw (.rangeOutOfBounds finish self.len)
  let isInit ← if range.start.bytes < finish.bytes then self.get range.start else pure false
  return ⟨self, isInit, range.start, finish⟩

private def collectChunksAux (iter : InitChunkIter) (fuel : Nat) :
    Except InitMaskError (Array InitChunk) := do
  match fuel with
  | 0 =>
    match ← iter.next? with
    | none => return #[]
    | some _ => throw (.invalidChunkIterator iter.start iter.finish)
  | fuel + 1 =>
    match ← iter.next? with
    | none => return #[]
    | some (chunk, next) =>
      return #[chunk] ++ (← collectChunksAux next fuel)
termination_by fuel

def collectChunks (iter : InitChunkIter) :
    Except InitMaskError (Array InitChunk) :=
  collectChunksAux iter (sizeBytes iter.finish - sizeBytes iter.start + 1)

def prepareCopy (self : InitMask) (range : AllocRange) :
    Except InitMaskError InitCopy := do
  if range.size.bytes == 0 then throw .emptyCopyRange
  let chunks ← collectChunks (← rangeAsInitChunks self range)
  match chunks[0]? with
  | none => throw .emptyCopyRange
  | some first =>
    let mut runs := #[]
    for chunk in chunks do
      let chunkRange ← chunk.range
      runs := runs.push chunkRange.size.bytes
    return ⟨first.isInit, runs⟩

private def applyCopyRuns (blocks : InitMaskMaterialized) (runs : Array UInt64)
    (index : Nat) (cursor : Size) (state : Bool) :
    Except InitMaskError (InitMaskMaterialized × Size) := do
  if index >= runs.size then return (blocks, cursor)
  match runs[index]? with
  | none => throw (.blockIndexOutOfBounds index runs.size)
  | some byteCount =>
    let next ← (Size.add cursor (Size.ofBytes byteCount)).mapError MemoryError.sizeError
    let blocks ← blocks.setRangeInbounds cursor next state
    applyCopyRuns blocks runs (index + 1) next (!state)
termination_by runs.size - index

private def applyCopyRepeats (blocks : InitMaskMaterialized) (defined : InitCopy)
    (range : AllocRange) (iteration repeatCount : Nat) :
    Except InitMaskError InitMaskMaterialized := do
  if iteration >= repeatCount then return blocks
  let offset ← (Size.mul range.size (UInt64.ofNat iteration)).mapError MemoryError.sizeError
  let cursor ← (Size.add range.start offset).mapError MemoryError.sizeError
  let (blocks, _) ← applyCopyRuns blocks defined.ranges 0 cursor defined.initial
  applyCopyRepeats blocks defined range (iteration + 1) repeatCount
termination_by repeatCount - iteration

def applyCopy (self : InitMask) (defined : InitCopy) (range : AllocRange)
    (repeatCount : UInt64) : Except InitMaskError InitMask := do
  if defined.ranges.isEmpty || defined.ranges.any (· == 0) then
    throw .invalidCopyEncoding
  if defined.ranges.size ≤ 1 then
    let total ← (Size.mul range.size repeatCount).mapError MemoryError.sizeError
    return ← self.setRange (allocRange range.start total) defined.initial
  let blocks ← materialize self
  let blocks ← applyCopyRepeats blocks defined range 0 repeatCount.toNat
  return ⟨.Materialized blocks, self.len⟩

end InitMask

namespace InitMask

theorem new_has_no_materialized_blocks (size : Size) (state : Bool) :
    (InitMask.new size state).materializedBlockCount = 0 := by
  rfl

theorem lazy_get (size index : Size) (state : Bool) :
    (InitMask.new size state).get index = .ok state := by
  rfl

theorem lazy_initialized_query (size : Size) (range : AllocRange) (finish : Size)
    (hEnd : range.endExclusive = .ok finish)
    (hInBounds : finish.bytes ≤ size.bytes) :
    (InitMask.new size true).isRangeInitialized range = .ok (.ok ()) := by
  have hOut : ¬ size.bytes < finish.bytes := UInt64.not_lt.mpr hInBounds
  simp only [InitMask.isRangeInitialized, InitMask.new, hEnd]
  change (if size.bytes < finish.bytes then
    (Except.error <$> AllocRange.fromEndpoints size finish)
    else (Except.ok (Except.ok ()))) = Except.ok (Except.ok ())
  simp [hOut]

theorem lazy_uninitialized_query (size : Size) (range : AllocRange) (finish : Size)
    (hEnd : range.endExclusive = .ok finish)
    (hInBounds : finish.bytes ≤ size.bytes) :
    (InitMask.new size false).isRangeInitialized range = .ok (.error range) := by
  have hOut : ¬ size.bytes < finish.bytes := UInt64.not_lt.mpr hInBounds
  simp only [InitMask.isRangeInitialized, InitMask.new, hEnd]
  change (if size.bytes < finish.bytes then
    (Except.error <$> AllocRange.fromEndpoints size finish)
    else (Except.ok (Except.error range))) = Except.ok (Except.error range)
  simp [hOut]

theorem full_overwrite_stays_lazy (size finish : Size) (oldState newState : Bool)
    (range : AllocRange)
    (hEnd : range.endExclusive = .ok finish)
    (hStart : range.start.bytes = 0)
    (hFull : size.bytes ≤ finish.bytes) :
    (InitMask.new size oldState).setRange range newState =
      .ok (InitMask.new finish newState) := by
  have hFullOverwrite : range.start.bytes = 0 ∧ size.bytes ≤ finish.bytes := ⟨hStart, hFull⟩
  simp only [InitMask.setRange, InitMask.new, hEnd]
  change (if range.start.bytes = 0 ∧ size.bytes ≤ finish.bytes then
    Except.ok (InitMask.new finish newState)
    else _) = Except.ok (InitMask.new finish newState)
  simp [hFullOverwrite]

end InitMask

end Miri.Memory

namespace Miri.Memory.InitMask.WriteProof
open Miri.ABI Miri.Memory
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
variable {ε α β : Type}
private abbrev getBlock := @Miri.Memory.InitMaskMaterialized.getBlock
private abbrev setBlock := @Miri.Memory.InitMaskMaterialized.setBlock
private abbrev setRangeInbounds := @Miri.Memory.InitMaskMaterialized.setRangeInbounds
private abbrev materialize := @Miri.Memory.InitMask.materialize
private abbrev setWordRange := @Miri.Memory.setWordRange
private abbrev wordMask := @Miri.Memory.wordMask
private theorem get_block_ok (words : Array UInt64) (index : Nat) (inBounds : index < words.size) :
    getBlock ⟨words⟩ index = .ok words[index] := by
  unfold getBlock
  unfold Miri.Memory.InitMaskMaterialized.getBlock
  simp [Array.getElem?_eq_getElem inBounds]

private theorem set_block_ok (words : Array UInt64) (index : Nat) (word : UInt64) (inBounds : index < words.size) :
    setBlock words index word = .ok (words.set index word) := by
  unfold setBlock
  unfold Miri.Memory.InitMaskMaterialized.setBlock
  simp [inBounds]

private def write_step (word : UInt64) (index : Nat) (words : Array UInt64) :
    Except InitMaskError (ForInStep (Array UInt64)) := do
  let updated ← setBlock words index word
  pure (.yield updated)

private theorem write_list_exists (indices : List Nat) (words : Array UInt64) (word : UInt64)
    (inBounds : ∀ index ∈ indices, index < words.size) :
    ∃ updated, forIn indices words (write_step word) = .ok updated ∧ updated.size = words.size := by
  induction indices generalizing words with
  | nil => exact ⟨words, rfl, rfl⟩
  | cons first rest ih =>
    have firstBound := inBounds first (by simp)
    have restBound : ∀ index ∈ rest, index < (words.set first word).size := by
      intro index member
      simpa using inBounds index (by simp [member])
    obtain ⟨updated, tailOk, sizeOk⟩ := ih (words.set first word) restBound
    refine ⟨updated, ?_, by simpa using sizeOk⟩
    simp only [List.forIn_cons, write_step, set_block_ok words first word firstBound,
      Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact tailOk

private theorem write_range_exists (lower upper : Nat) (words : Array UInt64) (word : UInt64)
    (inBounds : ∀ index, lower ≤ index → index < upper → index < words.size) :
    ∃ updated, (forIn (Std.Legacy.Range.mk lower upper 1 (by decide)) words (write_step word)) = .ok updated ∧ updated.size = words.size := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply write_list_exists
  intro index member
  obtain ⟨i, bound, rfl⟩ := List.mem_range'.mp member
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_zero, Nat.sub_self, Nat.div_one, Nat.one_mul] at bound ⊢
  apply inBounds <;> omega


private def update_word (words : Array UInt64) (index : Nat) (transform : UInt64 → UInt64) :
    Except InitMaskError (Array UInt64) := do
  let word ← getBlock ⟨words⟩ index
  setBlock words index (transform word)

private theorem update_word_exists (words : Array UInt64) (index : Nat) (transform : UInt64 → UInt64)
    (inBounds : index < words.size) :
    ∃ updated, update_word words index transform = .ok updated ∧ updated.size = words.size := by
  refine ⟨words.set index (transform words[index]), ?_, by simp⟩
  simp [update_word, get_block_ok words index inBounds, set_block_ok, inBounds,
    Bind.bind, Except.bind]

private def set_range_words (words : Array UInt64) (blockA bitA blockB bitB : Nat) (state : Bool) :
    Except InitMaskError (Array UInt64) := do
  if blockA == blockB then
    update_word words blockA (fun word => setWordRange word.toNat bitA (if bitB == 0 then 64 else bitB) state)
  else
    let initial ← update_word words blockA (fun word => setWordRange word.toNat bitA 64 state)
    let middle ← if bitB != 0 then update_word initial blockB (fun word => setWordRange word.toNat 0 bitB state) else pure initial
    forIn (Std.Legacy.Range.mk (blockA + 1) blockB 1 (by decide)) middle
      (write_step (if state then UInt64.ofNat wordMask else 0))

private theorem set_range_words_exists (words : Array UInt64) (blockA bitA blockB bitB : Nat) (state : Bool)
    (firstBound : blockA < words.size)
    (lastBound : bitB ≠ 0 → blockB < words.size)
    (middleBound : ∀ index, blockA + 1 ≤ index → index < blockB → index < words.size) :
    ∃ updated, set_range_words words blockA bitA blockB bitB state = .ok updated ∧ updated.size = words.size := by
  by_cases same : blockA == blockB
  · exact update_word_exists words blockA _ firstBound |>.imp (by intro updated props; simpa [set_range_words, same] using props)
  · obtain ⟨initial, initialOk, initialSize⟩ := update_word_exists words blockA
      (fun word => setWordRange word.toNat bitA 64 state) firstBound
    have obtainMiddle : ∃ middle,
        (if bitB != 0 then update_word initial blockB (fun word => setWordRange word.toNat 0 bitB state) else pure initial) = .ok middle ∧ middle.size = words.size := by
      by_cases tail : bitB = 0
      · exact ⟨initial, by simp [tail, Pure.pure, Except.pure], initialSize⟩
      · obtain ⟨middle, middleOk, middleSize⟩ := update_word_exists initial blockB
          (fun word => setWordRange word.toNat 0 bitB state) (by rw [initialSize]; exact lastBound tail)
        exact ⟨middle, by simpa [tail] using middleOk, middleSize.trans initialSize⟩
    obtain ⟨middle, middleOk, middleSize⟩ := obtainMiddle
    obtain ⟨updated, loopOk, updatedSize⟩ := write_range_exists (blockA + 1) blockB middle
      (if state then UInt64.ofNat wordMask else 0) (by simpa only [middleSize] using middleBound)
    refine ⟨updated, ?_, updatedSize.trans middleSize⟩
    simp only [set_range_words, same, Bool.false_eq_true, ↓reduceIte, initialOk, Bind.bind, Except.bind]
    by_cases tail : bitB != 0
    all_goals simp only [tail, Bool.false_eq_true, ↓reduceIte] at middleOk ⊢
    all_goals rw [middleOk]
    all_goals exact loopOk

private theorem bind_if (p : Prop) [Decidable p] (yes no : Except ε α) (next : α → Except ε β) :
    ((if p then yes else no) >>= next) = (if p then yes >>= next else no >>= next) := by
  split <;> rfl

private theorem set_range_inbounds_reduces (self : InitMaskMaterialized) (start finish : Size) (state : Bool) :
    setRangeInbounds self start finish state = do
      let words ← set_range_words self.blocks (start.bytes.toNat / 64) (start.bytes.toNat % 64)
        (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state
      return ⟨words⟩ := by
  unfold setRangeInbounds
  unfold Miri.Memory.InitMaskMaterialized.setRangeInbounds
  unfold set_range_words update_word write_step getBlock setBlock setWordRange wordMask
  unfold InitMaskMaterialized.bitIndex
  unfold Miri.Memory.sizeBytes
  unfold Miri.Memory.blockSize
  cases state <;> simp only [Bool.false_eq_true, Bool.true_eq, ↓reduceIte, bind_if, bind_assoc, pure_bind]


private theorem set_range_inbounds_exists (self : InitMaskMaterialized) (start finish : Size) (state : Bool)
    (nonempty : start.bytes.toNat < finish.bytes.toNat)
    (capacity : finish.bytes.toNat ≤ self.blocks.size * 64) :
    ∃ updated, setRangeInbounds self start finish state = .ok updated ∧ updated.blocks.size = self.blocks.size := by
  have firstBound : start.bytes.toNat / 64 < self.blocks.size := by omega
  have lastBound : finish.bytes.toNat % 64 ≠ 0 → finish.bytes.toNat / 64 < self.blocks.size := by omega
  have middleBound : ∀ index, start.bytes.toNat / 64 + 1 ≤ index → index < finish.bytes.toNat / 64 → index < self.blocks.size := by
    intro index lower upper
    omega
  obtain ⟨words, wordsOk, wordsSize⟩ := set_range_words_exists self.blocks
    (start.bytes.toNat / 64) (start.bytes.toNat % 64) (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state
    firstBound lastBound middleBound
  refine ⟨⟨words⟩, ?_, wordsSize⟩
  rw [set_range_inbounds_reduces, wordsOk]
  rfl

def WellFormed (mask : InitMask) : Prop :=
  match mask.blocks with
  | .Lazy _ => True
  | .Materialized blocks => mask.len.bytes.toNat ≤ blocks.blocks.size * 64

private theorem materialized_set_range_exists (blocks : InitMaskMaterialized) (len : Size) (range : AllocRange) (finish : Size) (state : Bool)
    (maskCapacity : len.bytes.toNat ≤ blocks.blocks.size * 64)
    (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ len.bytes.toNat) :
    ∃ updated, (InitMask.mk (.Materialized blocks) len).setRange range state = .ok updated ∧ updated.len = len ∧ WellFormed updated := by
  by_cases full : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes
  · have equal : finish = len := by
      have lower := UInt64.le_iff_toNat_le.mp full.2
      have equalBytes : finish.bytes = len.bytes := UInt64.toNat_inj.mp (by omega)
      exact congrArg Size.ofBytes equalBytes
    refine ⟨⟨.Lazy state, len⟩, ?_, rfl, trivial⟩
    simp [InitMask.setRange, endpoint, full, equal, Pure.pure, Except.pure, Bind.bind, Except.bind]
  · obtain ⟨updated, updatedOk, sizeOk⟩ := set_range_inbounds_exists blocks range.start finish state nonempty (by omega)
    refine ⟨⟨.Materialized updated, len⟩, ?_, rfl, ?_⟩
    · unfold InitMask.setRange
      simp only [endpoint, Bind.bind, Except.bind]
      simp only [full, ↓reduceIte, show finish.bytes ≤ len.bytes from UInt64.le_iff_toNat_le.mpr inBounds]
      unfold setRangeInbounds at updatedOk
      rw [updatedOk]
      rfl
    · simp only [WellFormed]
      omega

private theorem materialize_lazy_nonzero (len : Size) (state : Bool) (nonzero : len.bytes.toNat ≠ 0) :
    materialize (InitMask.new len state) = .ok ⟨Array.replicate (len.bytes.toNat / 64 + 1) (if state then UInt64.ofNat 18446744073709551615 else 0)⟩ := by
  unfold materialize
  unfold Miri.Memory.InitMask.materialize
  unfold InitMask.new
  dsimp only
  unfold Miri.Memory.InitMaskMaterialized.grow
  unfold Miri.Memory.sizeBytes
  unfold Miri.Memory.blockSize
  unfold Miri.Memory.wordMask
  simp [nonzero, Size.ofBytes, Array.empty_append, Pure.pure, Except.pure, Bind.bind, Except.bind]

theorem set_range_exists (mask : InitMask) (range : AllocRange) (finish : Size) (state : Bool)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    ∃ updated, mask.setRange range state = .ok updated ∧ updated.len = mask.len ∧ WellFormed updated := by
  cases mask with
  | mk blocks len =>
    cases blocks with
    | Materialized blocks => exact materialized_set_range_exists blocks len range finish state valid endpoint nonempty inBounds
    | Lazy initial =>
      dsimp only at inBounds
      by_cases full : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes
      · have lower := UInt64.le_iff_toNat_le.mp full.2
        have equalBytes : finish.bytes = len.bytes := UInt64.toNat_inj.mp (by omega)
        have equal : finish = len := congrArg Size.ofBytes equalBytes
        refine ⟨⟨.Lazy state, len⟩, ?_, rfl, trivial⟩
        simp [InitMask.setRange, endpoint, full, equal, Pure.pure, Except.pure, Bind.bind, Except.bind]
      · by_cases same : initial == state
        · refine ⟨⟨.Lazy initial, len⟩, ?_, rfl, trivial⟩
          have notGrow : ¬finish.bytes > len.bytes := by simpa [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
          simp [InitMask.setRange, endpoint, full, same, notGrow, Pure.pure, Except.pure, Bind.bind, Except.bind]
        · have lenNonzero : len.bytes.toNat ≠ 0 := by omega
          let words := Array.replicate (len.bytes.toNat / 64 + 1) (if initial then UInt64.ofNat 18446744073709551615 else 0)
          have materialized := materialize_lazy_nonzero len initial lenNonzero
          have capacity : finish.bytes.toNat ≤ words.size * 64 := by simp only [words, Array.size_replicate]; omega
          obtain ⟨updated, updatedOk, sizeOk⟩ := set_range_inbounds_exists ⟨words⟩ range.start finish state nonempty capacity
          refine ⟨⟨.Materialized updated, len⟩, ?_, rfl, ?_⟩
          · unfold InitMask.setRange
            simp only [endpoint, Bind.bind, Except.bind, full, ↓reduceIte, same, Bool.false_eq_true]
            change (materialize (InitMask.new len initial) >>= _) = _
            rw [materialized]
            simp only [Bind.bind, Except.bind, show finish.bytes ≤ len.bytes from UInt64.le_iff_toNat_le.mpr inBounds, ↓reduceIte]
            unfold setRangeInbounds at updatedOk
            rw [updatedOk]
            rfl
          · simp only [WellFormed]
            change updated.blocks.size = words.size at sizeOk
            simp only [words, Array.size_replicate] at sizeOk
            omega



private theorem if_pos_eq {α : Type} {c : Prop} [Decidable c] {t e : α} (h : c) :
    (if c then t else e) = t := by
  split
  · rfl
  · next hn => exact absurd h hn

private theorem if_neg_eq {α : Type} {c : Prop} [Decidable c] {t e : α} (h : ¬c) :
    (if c then t else e) = e := by
  split
  · next hp => exact absurd hp h
  · rfl

private theorem testBit_wordMask (bit : Nat) (h : bit < 64) :
    Nat.testBit wordMask bit = true := by
  have hm : wordMask = 2 ^ 64 - 1 := by decide
  rw [hm, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true h

private theorem setWordRange_testBit (word lo hi bit : Nat) (state : Bool)
    (h_lo_hi : lo ≤ hi) (h_hi : hi ≤ 64) (h_bit : bit < 64) :
    Nat.testBit (setWordRange word lo hi state).toNat bit =
      if lo ≤ bit ∧ bit < hi then state else Nat.testBit word bit := by
  let mask := (2 ^ hi - 1) - (2 ^ lo - 1)
  have h_pow_lo : 1 ≤ 2 ^ lo := Nat.one_le_two_pow
  have h_pow_diff : 1 ≤ 2 ^ (hi - lo) := Nat.one_le_two_pow
  have h_sum : mask = (2 ^ (hi - lo) - 1) <<< lo := by
    have h_eq : hi = lo + (hi - lo) := by omega
    have h_pow : 2 ^ hi = 2 ^ lo * 2 ^ (hi - lo) := by
      conv => lhs; rw [h_eq]
      exact Nat.pow_add 2 lo (hi - lo)
    have h_mul : 2 ^ lo * (2 ^ (hi - lo) - 1) = 2 ^ lo * 2 ^ (hi - lo) - 2 ^ lo := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    rw [Nat.shiftLeft_eq, Nat.mul_comm]
    dsimp only [mask]
    omega
  have h_mask_lt : mask < 2 ^ 64 := by
    have : 2 ^ hi ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) h_hi
    dsimp only [mask]
    omega
  have h_mask_bit : Nat.testBit mask bit = decide (lo ≤ bit ∧ bit < hi) := by
    rw [h_sum, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
    by_cases h_ge : lo ≤ bit
    · by_cases h_lt : bit < hi
      · have : bit - lo < hi - lo := by omega
        simp [h_ge, h_lt, this]
      · have : ¬(bit - lo < hi - lo) := by omega
        simp [h_ge, h_lt, this]
    · simp [h_ge]
  have h_inv : Nat.testBit (Miri.Memory.wordMask - mask) bit = !Nat.testBit mask bit := by
    have h_wm : Miri.Memory.wordMask = 2 ^ 64 - 1 := rfl
    rw [h_wm]
    have h_bv : BitVec.ofNat 64 (2 ^ 64 - 1 - mask) = ~~~(BitVec.ofNat 64 mask) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_not]
      omega
    have h1 := congrArg (fun b : BitVec 64 => b.getLsbD bit) h_bv
    simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_not, h_bit, decide_true, Bool.true_and] at h1
    exact h1
  unfold setWordRange Miri.Memory.setWordRange
  dsimp only
  cases state
  · simp only [Bool.false_eq_true, ↓reduceIte, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow,
      h_bit, decide_true, Bool.true_and]
    change (word &&& (Miri.Memory.wordMask - mask)).testBit bit = _
    rw [Nat.testBit_and, h_inv, h_mask_bit]
    by_cases h_in : lo ≤ bit ∧ bit < hi <;> simp [h_in]
  · simp only [↓reduceIte, UInt64.toNat_ofNat', Nat.testBit_mod_two_pow,
      h_bit, decide_true, Bool.true_and]
    change (word ||| mask).testBit bit = _
    rw [Nat.testBit_or, h_mask_bit]
    by_cases h_in : lo ≤ bit ∧ bit < hi <;> simp [h_in]

private theorem write_list_getElem? (indices : List Nat) (words : Array UInt64) (word : UInt64)
    (updated : Array UInt64)
    (h_ok : forIn indices words (write_step word) = .ok updated) :
    updated.size = words.size ∧
      ∀ k, updated[k]? = if k ∈ indices then some word else words[k]? := by
  induction indices generalizing words with
  | nil =>
    simp only [List.forIn_nil, Pure.pure, Except.pure, Except.ok.injEq] at h_ok
    subst h_ok
    exact ⟨rfl, fun _ => by simp⟩
  | cons first rest ih =>
    simp only [List.forIn_cons, write_step, Miri.Memory.InitMaskMaterialized.setBlock,
      setBlock, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    by_cases h_first : first < words.size
    · simp only [h_first, ↓reduceDIte] at h_ok
      obtain ⟨h_sz, h_elem⟩ := ih (words.set first word h_first) h_ok
      have h_wsz : (words.set first word h_first).size = words.size := Array.size_set ..
      refine ⟨h_sz.trans h_wsz, fun k => ?_⟩
      rw [h_elem k]
      by_cases h_rest : k ∈ rest
      · simp [h_rest]
      · simp only [h_rest, ↓reduceIte, List.mem_cons, or_false]
        by_cases h_eq : k = first
        · subst h_eq; simp [Array.getElem?_set_self, h_first]
        · simp [Array.getElem?_set, Ne.symm h_eq, h_eq]
    · simp [h_first] at h_ok

private theorem write_range_getElem? (lower upper : Nat) (words : Array UInt64) (word : UInt64)
    (updated : Array UInt64)
    (h_ok : forIn (Std.Legacy.Range.mk lower upper 1 (by decide)) words (write_step word) = .ok updated) :
    updated.size = words.size ∧
      ∀ k, updated[k]? = if lower ≤ k ∧ k < upper then some word else words[k]? := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h_ok
  obtain ⟨h_sz, h_elem⟩ := write_list_getElem? _ words word updated h_ok
  refine ⟨h_sz, fun k => ?_⟩
  rw [h_elem k]
  have h_mem : (k ∈ List.range' [lower:upper].start [lower:upper].size [lower:upper].step) ↔
      (lower ≤ k ∧ k < upper) := by
    simp only [List.mem_range', Std.Legacy.Range.size, Nat.div_one, Nat.one_mul, Nat.sub_zero, Nat.add_zero]
    constructor
    · rintro ⟨i, hi, rfl⟩; omega
    · intro ⟨h1, h2⟩; exact ⟨k - lower, by omega, by omega⟩
  by_cases h_in : lower ≤ k ∧ k < upper
  · have hm : k ∈ List.range' [lower:upper].start [lower:upper].size [lower:upper].step := h_mem.mpr h_in
    rw [if_pos_eq (hm), if_pos_eq (h_in)]
  · have hm : k ∉ List.range' [lower:upper].start [lower:upper].size [lower:upper].step := fun h => h_in (h_mem.mp h)
    rw [if_neg_eq (hm), if_neg_eq (h_in)]

private theorem update_word_getElem? (words : Array UInt64) (index : Nat)
    (transform : UInt64 → UInt64) (updated : Array UInt64)
    (h_ok : update_word words index transform = .ok updated) :
    index < words.size ∧ updated.size = words.size ∧
      ∀ k, updated[k]? = if k = index then words[index]?.map transform else words[k]? := by
  unfold update_word getBlock Miri.Memory.InitMaskMaterialized.getBlock
    setBlock Miri.Memory.InitMaskMaterialized.setBlock at h_ok
  dsimp only at h_ok
  by_cases h_idx : index < words.size
  · have h_get : words[index]? = some words[index] := Array.getElem?_eq_getElem h_idx
    simp only [h_get, Bind.bind, Except.bind, h_idx, ↓reduceDIte, Except.ok.injEq] at h_ok
    subst h_ok
    refine ⟨h_idx, Array.size_set .., fun k => ?_⟩
    by_cases h_eq : k = index
    · subst h_eq; simp [h_get, h_idx]
    · simp [Array.getElem?_set, Ne.symm h_eq, h_eq]
  · have h_get : words[index]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt h_idx)
    simp [h_get, Bind.bind, Except.bind] at h_ok


private theorem set_range_words_bit_gen (words : Array UInt64) (bA rA bB rB : Nat) (state : Bool)
    (updated : Array UInt64)
    (h_rA : rA < 64) (h_rB : rB < 64)
    (h_nonempty : bA * 64 + rA < bB * 64 + rB)
    (h_ok : set_range_words words bA rA bB rB state = .ok updated) :
    updated.size = words.size ∧
      ∀ (k bit : Nat), k < words.size → bit < 64 →
        ∃ w oldW,
          updated[k]? = some w ∧
          words[k]? = some oldW ∧
          Nat.testBit w.toNat bit =
            if bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB then
              state
            else
              Nat.testBit oldW.toNat bit := by
  unfold set_range_words at h_ok
  by_cases h_same : bA == bB
  · simp only [h_same, ↓reduceIte] at h_ok
    have h_bA_eq : bA = bB := eq_of_beq h_same
    have h_rB_nz : rB ≠ 0 := by omega
    obtain ⟨_, h_sz, h_elem⟩ := update_word_getElem? words bA _ updated h_ok
    refine ⟨h_sz, fun k bit h_ib h_bit => ?_⟩
    have h_old : words[k]? = some (words[k]'h_ib) := Array.getElem?_eq_getElem h_ib
    by_cases h_k : k = bA
    · subst h_k
      refine ⟨setWordRange (words[k]'h_ib).toNat rA (if rB == 0 then 64 else rB) state,
        words[k]'h_ib, ?_, h_old, ?_⟩
      · have he := h_elem k
        rw [if_pos_eq rfl, h_old] at he
        exact he
      · have h_rB_beq : (rB == 0) = false := beq_false_of_ne h_rB_nz
        simp only [h_rB_beq, Bool.false_eq_true, ↓reduceIte]
        have h_lo_hi : rA ≤ rB := by omega
        have h_hi : rB ≤ 64 := by omega
        rw [setWordRange_testBit _ rA rB bit state h_lo_hi h_hi h_bit]
        have h_iff : (rA ≤ bit ∧ bit < rB) ↔ (k * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by omega
        by_cases h1 : rA ≤ bit ∧ bit < rB
        · rw [if_pos_eq h1, if_pos_eq (h_iff.mp h1)]
        · rw [if_neg_eq h1, if_neg_eq (fun h2 => h1 (h_iff.mpr h2))]
    · refine ⟨words[k]'h_ib, words[k]'h_ib, ?_, h_old, ?_⟩
      · have he := h_elem k
        rw [if_neg_eq h_k] at he
        exact he.trans h_old
      · have h_out : ¬(bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by omega
        rw [if_neg_eq h_out]
  · simp only [h_same, Bool.false_eq_true, ↓reduceIte] at h_ok
    have h_lt_div : bA < bB := by
      have h_ne : bA ≠ bB := fun h => h_same (beq_iff_eq.mpr h)
      omega
    cases h_init : update_word words bA (fun word => setWordRange word.toNat rA 64 state) with
    | error e => simp [h_init, Bind.bind, Except.bind] at h_ok
    | ok initial =>
      obtain ⟨_, h_init_sz, h_init_elem⟩ := update_word_getElem? words bA _ initial h_init
      have h_mid_step : ∃ middle,
          forIn (Std.Legacy.Range.mk (bA + 1) bB 1 (by decide)) middle
            (write_step (if state then UInt64.ofNat wordMask else 0)) = .ok updated ∧
          middle.size = words.size ∧
          ∀ k, middle[k]? =
            if rB ≠ 0 ∧ k = bB then initial[bB]?.map (fun word => setWordRange word.toNat 0 rB state)
            else initial[k]? := by
        by_cases h_rB_zero : rB = 0
        · subst h_rB_zero
          simp only [h_init, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
          exact ⟨initial, h_ok, h_init_sz, fun k => by simp⟩
        · have h_bne : (rB != 0) = true := bne_iff_ne.mpr h_rB_zero
          simp only [h_init, h_bne, ↓reduceIte, Bind.bind, Except.bind] at h_ok
          cases h_m : update_word initial bB (fun word => setWordRange word.toNat 0 rB state) with
          | error e => simp [h_m] at h_ok
          | ok mid =>
            simp only [h_m] at h_ok
            obtain ⟨_, h_mid_sz, h_mid_elem⟩ := update_word_getElem? initial bB _ mid h_m
            refine ⟨mid, h_ok, h_mid_sz.trans h_init_sz, fun k => ?_⟩
            rw [h_mid_elem k]
            by_cases hk : k = bB
            · rw [if_pos_eq hk, if_pos_eq ⟨h_rB_zero, hk⟩]
            · rw [if_neg_eq hk, if_neg_eq (fun h => hk h.2)]
      obtain ⟨middle, h_loop, h_mid_sz, h_mid_elem⟩ := h_mid_step
      let fillWord : UInt64 := if state then UInt64.ofNat wordMask else 0
      obtain ⟨h_upd_sz, h_upd_elem⟩ := write_range_getElem? (bA + 1) bB middle fillWord updated h_loop
      refine ⟨h_upd_sz.trans h_mid_sz, fun k bit h_ib h_bit => ?_⟩
      have h_old : words[k]? = some (words[k]'h_ib) := Array.getElem?_eq_getElem h_ib
      have h_fill_bit : Nat.testBit fillWord.toNat bit = state := by
        dsimp only [fillWord]
        cases state
        · simp
        · simp only [↓reduceIte]
          have h_wm : (UInt64.ofNat wordMask).toNat = wordMask := by decide
          rw [h_wm, testBit_wordMask bit h_bit]
      by_cases h_in_mid : bA + 1 ≤ k ∧ k < bB
      · refine ⟨fillWord, words[k]'h_ib, ?_, h_old, ?_⟩
        · have he := h_upd_elem k
          rw [if_pos_eq h_in_mid] at he
          exact he
        · have h_in_idx : bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB := by omega
          rw [if_pos_eq h_in_idx, h_fill_bit]
      · have he_upd := h_upd_elem k
        rw [if_neg_eq h_in_mid, h_mid_elem k] at he_upd
        by_cases h_k_bB : rB ≠ 0 ∧ k = bB
        · obtain ⟨h_rB_nz, h_eq_bB⟩ := h_k_bB
          subst h_eq_bB
          have h_init_bB : initial[k]? = words[k]? := by
            have hi := h_init_elem k
            have hne : k ≠ bA := by omega
            rw [if_neg_eq hne] at hi
            exact hi
          rw [if_pos_eq ⟨h_rB_nz, rfl⟩, h_init_bB, h_old] at he_upd
          refine ⟨setWordRange (words[k]'h_ib).toNat 0 rB state, words[k]'h_ib, he_upd, h_old, ?_⟩
          have h_hi : rB ≤ 64 := by omega
          rw [setWordRange_testBit _ 0 rB bit state (Nat.zero_le _) h_hi h_bit]
          have h_iff : (0 ≤ bit ∧ bit < rB) ↔ (bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < k * 64 + rB) := by omega
          by_cases h1 : 0 ≤ bit ∧ bit < rB
          · rw [if_pos_eq h1, if_pos_eq (h_iff.mp h1)]
          · rw [if_neg_eq h1, if_neg_eq (fun h2 => h1 (h_iff.mpr h2))]
        · rw [if_neg_eq h_k_bB, h_init_elem k] at he_upd
          by_cases h_k_bA : k = bA
          · subst h_k_bA
            rw [if_pos_eq rfl, h_old] at he_upd
            refine ⟨setWordRange (words[k]'h_ib).toNat rA 64 state, words[k]'h_ib, he_upd, h_old, ?_⟩
            have h_lo_hi : rA ≤ 64 := by omega
            rw [setWordRange_testBit _ rA 64 bit state h_lo_hi (Nat.le_refl 64) h_bit]
            have h_iff : (rA ≤ bit ∧ bit < 64) ↔ (k * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by omega
            by_cases h1 : rA ≤ bit ∧ bit < 64
            · rw [if_pos_eq h1, if_pos_eq (h_iff.mp h1)]
            · rw [if_neg_eq h1, if_neg_eq (fun h2 => h1 (h_iff.mpr h2))]
          · rw [if_neg_eq h_k_bA] at he_upd
            refine ⟨words[k]'h_ib, words[k]'h_ib, he_upd.trans h_old, h_old, ?_⟩
            have h_out : ¬(bA * 64 + rA ≤ k * 64 + bit ∧ k * 64 + bit < bB * 64 + rB) := by omega
            rw [if_neg_eq h_out]


theorem get_ok_of_wellFormed (mask : InitMask) (idx : Size)
    (valid : WellFormed mask) (inBounds : idx.bytes.toNat < mask.len.bytes.toNat) :
    ∃ b, mask.get idx = .ok b := by
  cases mask with
  | mk blocks len =>
    cases blocks with
    | Lazy state => exact ⟨state, rfl⟩
    | Materialized blocks =>
      dsimp only [WellFormed] at valid
      dsimp only at inBounds
      have h_ib : idx.bytes.toNat / 64 < blocks.blocks.size := by omega
      refine ⟨Nat.testBit (blocks.blocks[idx.bytes.toNat / 64]'h_ib).toNat (idx.bytes.toNat % 64), ?_⟩
      unfold InitMask.get Miri.Memory.InitMaskMaterialized.get
        Miri.Memory.InitMaskMaterialized.getBlock
        InitMaskMaterialized.bitIndex Miri.Memory.sizeBytes Miri.Memory.blockSize
        Miri.Memory.bitAt
      dsimp only
      rw [Array.getElem?_eq_getElem h_ib]
      rfl

theorem set_range_get (mask updated : InitMask) (range : AllocRange) (finish idx : Size)
    (state : Bool)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (idxInBounds : idx.bytes.toNat < mask.len.bytes.toNat)
    (h_set : mask.setRange range state = .ok updated) :
    updated.get idx =
      if range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat then
        .ok state
      else
        mask.get idx := by

  cases mask with
  | mk blocks len =>
    dsimp only at inBounds idxInBounds
    cases blocks with
    | Materialized oldBlocks =>
      dsimp only [WellFormed] at valid
      unfold InitMask.setRange at h_set
      simp only [endpoint, Bind.bind, Except.bind] at h_set
      by_cases full : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes
      · rw [if_pos_eq full] at h_set
        injection h_set with h_upd
        subst h_upd
        have h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat := by
          have := UInt64.le_iff_toNat_le.mp full.2
          have h0 : range.start.bytes.toNat = 0 := by simp [full.1]
          omega
        rw [if_pos_eq h_in]
        rfl
      · rw [if_neg_eq full] at h_set
        have h_fin_le : finish.bytes ≤ len.bytes := UInt64.le_iff_toNat_le.mpr inBounds
        rw [if_pos_eq h_fin_le] at h_set
        have h_red := set_range_inbounds_reduces oldBlocks range.start finish state
        unfold setRangeInbounds at h_red
        rw [h_red] at h_set
        cases h_words : set_range_words oldBlocks.blocks
            (range.start.bytes.toNat / 64) (range.start.bytes.toNat % 64)
            (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state with
        | error e => simp [h_words, Bind.bind, Except.bind] at h_set
        | ok newWords =>
          simp only [h_words, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at h_set
          subst h_set
          have h_rA : range.start.bytes.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
          have h_rB : finish.bytes.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
          have h_ne_mul : (range.start.bytes.toNat / 64) * 64 + range.start.bytes.toNat % 64 <
              (finish.bytes.toNat / 64) * 64 + finish.bytes.toNat % 64 := by omega
          obtain ⟨_, h_bit⟩ := set_range_words_bit_gen oldBlocks.blocks _ _ _ _ state newWords
            h_rA h_rB h_ne_mul h_words
          have h_ib : idx.bytes.toNat / 64 < oldBlocks.blocks.size := by omega
          obtain ⟨w, oldW, hw, holdW, h_tb⟩ := h_bit (idx.bytes.toNat / 64) (idx.bytes.toNat % 64)
            h_ib (Nat.mod_lt _ (by decide))
          have h_iff : ((range.start.bytes.toNat / 64) * 64 + range.start.bytes.toNat % 64 ≤
                (idx.bytes.toNat / 64) * 64 + idx.bytes.toNat % 64 ∧
              (idx.bytes.toNat / 64) * 64 + idx.bytes.toNat % 64 <
                (finish.bytes.toNat / 64) * 64 + finish.bytes.toNat % 64) ↔
              (range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat) := by omega
          unfold InitMask.get Miri.Memory.InitMaskMaterialized.get
            Miri.Memory.InitMaskMaterialized.getBlock
            InitMaskMaterialized.bitIndex Miri.Memory.sizeBytes Miri.Memory.blockSize
            Miri.Memory.bitAt
          dsimp only
          rw [hw, holdW]
          simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
          rw [h_tb]
          by_cases h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat
          · rw [if_pos_eq (h_iff.mpr h_in), if_pos_eq h_in]
          · rw [if_neg_eq (fun h => h_in (h_iff.mp h)), if_neg_eq h_in]
    | Lazy initial =>
      unfold InitMask.setRange at h_set
      simp only [endpoint, Bind.bind, Except.bind] at h_set
      by_cases full : range.start.bytes = 0 ∧ len.bytes ≤ finish.bytes
      · rw [if_pos_eq full] at h_set
        injection h_set with h_upd
        subst h_upd
        have h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat := by
          have := UInt64.le_iff_toNat_le.mp full.2
          have h0 : range.start.bytes.toNat = 0 := by simp [full.1]
          omega
        rw [if_pos_eq h_in]
        rfl
      · rw [if_neg_eq full] at h_set
        by_cases same : initial == state
        · have h_eq_st : initial = state := eq_of_beq same
          subst h_eq_st
          rw [if_pos_eq (beq_self_eq_true initial)] at h_set
          have notGrow : ¬finish.bytes > len.bytes := by
            simpa [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
          rw [if_neg_eq notGrow] at h_set
          injection h_set with h_upd
          subst h_upd
          by_cases h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat
          · rw [if_pos_eq h_in]; rfl
          · rw [if_neg_eq h_in]
        · rw [if_neg_eq same] at h_set
          have lenNonzero : len.bytes.toNat ≠ 0 := by omega
          have matEq := materialize_lazy_nonzero len initial lenNonzero
          unfold materialize InitMask.new at matEq
          rw [matEq] at h_set
          have h_fin_le : finish.bytes ≤ len.bytes := UInt64.le_iff_toNat_le.mpr inBounds
          simp only [Bind.bind, Except.bind] at h_set
          rw [if_pos_eq h_fin_le] at h_set
          let initWords := Array.replicate (len.bytes.toNat / 64 + 1)
            (if initial then UInt64.ofNat 18446744073709551615 else 0)
          have h_red := set_range_inbounds_reduces ⟨initWords⟩ range.start finish state
          unfold setRangeInbounds at h_red
          dsimp only [initWords] at h_red
          rw [h_red] at h_set
          cases h_words : set_range_words initWords
              (range.start.bytes.toNat / 64) (range.start.bytes.toNat % 64)
              (finish.bytes.toNat / 64) (finish.bytes.toNat % 64) state with
          | error e =>
            dsimp only [initWords] at h_words
            rw [h_words] at h_set
            cases h_set
          | ok newWords =>
            have h_words_unf := h_words
            dsimp only [initWords] at h_words_unf
            rw [h_words_unf] at h_set
            simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at h_set
            subst h_set
            have h_rA : range.start.bytes.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
            have h_rB : finish.bytes.toNat % 64 < 64 := Nat.mod_lt _ (by decide)
            have h_ne_mul : (range.start.bytes.toNat / 64) * 64 + range.start.bytes.toNat % 64 <
                (finish.bytes.toNat / 64) * 64 + finish.bytes.toNat % 64 := by omega
            obtain ⟨_, h_bit⟩ := set_range_words_bit_gen initWords _ _ _ _ state newWords
              h_rA h_rB h_ne_mul h_words
            have h_ib : idx.bytes.toNat / 64 < initWords.size := by
              simp only [initWords, Array.size_replicate]; omega
            obtain ⟨w, oldW, hw, holdW, h_tb⟩ := h_bit (idx.bytes.toNat / 64) (idx.bytes.toNat % 64)
              h_ib (Nat.mod_lt _ (by decide))
            have h_oldW_eq : oldW = (if initial then UInt64.ofNat 18446744073709551615 else 0) := by
              have h_ib_len : idx.bytes.toNat / 64 < len.bytes.toNat / 64 + 1 := by omega
              have h_rep : initWords[idx.bytes.toNat / 64]? =
                  some (if initial then UInt64.ofNat 18446744073709551615 else 0) := by
                simp [initWords, Array.getElem?_replicate, h_ib_len]
              exact Option.some.inj (holdW.symm.trans h_rep)
            have h_old_bit : Nat.testBit oldW.toNat (idx.bytes.toNat % 64) = initial := by
              rw [h_oldW_eq]
              cases initial
              · simp
              · simp only [↓reduceIte]
                have h_wm : (UInt64.ofNat 18446744073709551615).toNat = wordMask := by decide
                rw [h_wm, testBit_wordMask _ (Nat.mod_lt _ (by decide))]
            have h_iff : ((range.start.bytes.toNat / 64) * 64 + range.start.bytes.toNat % 64 ≤
                  (idx.bytes.toNat / 64) * 64 + idx.bytes.toNat % 64 ∧
                (idx.bytes.toNat / 64) * 64 + idx.bytes.toNat % 64 <
                  (finish.bytes.toNat / 64) * 64 + finish.bytes.toNat % 64) ↔
                (range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat) := by omega
            unfold InitMask.get Miri.Memory.InitMaskMaterialized.get
              Miri.Memory.InitMaskMaterialized.getBlock
              InitMaskMaterialized.bitIndex Miri.Memory.sizeBytes Miri.Memory.blockSize
              Miri.Memory.bitAt
            dsimp only
            rw [hw]
            simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
            rw [h_tb, h_old_bit]
            by_cases h_in : range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat
            · rw [if_pos_eq (h_iff.mpr h_in), if_pos_eq h_in]
            · rw [if_neg_eq (fun h => h_in (h_iff.mp h)), if_neg_eq h_in]


private theorem firstSetBit_spec_none (bits startBit : Nat) :
    Miri.Memory.InitMaskMaterialized.firstSetBit bits startBit = none ↔
      ∀ b, startBit ≤ b → b < 64 → Nat.testBit bits b = false := by
  unfold Miri.Memory.InitMaskMaterialized.firstSetBit Miri.Memory.bitAt
  simp only [Option.map_eq_none_iff, List.find?_eq_none, List.mem_range, Bool.not_eq_true]
  constructor
  · intro h b h_lo h_hi
    have h_off : b - startBit < 64 - startBit := by omega
    have h_eq : startBit + (b - startBit) = b := by omega
    simpa [h_eq] using h (b - startBit) h_off
  · intro h off h_off
    exact h (startBit + off) (by omega) (by omega)

private theorem firstSetBit_spec_some (bits startBit res : Nat)
    (h_some : Miri.Memory.InitMaskMaterialized.firstSetBit bits startBit = some res) :
    startBit ≤ res ∧ res < 64 ∧ Nat.testBit bits res = true ∧
      ∀ b, startBit ≤ b → b < res → Nat.testBit bits b = false := by
  unfold Miri.Memory.InitMaskMaterialized.firstSetBit Miri.Memory.bitAt at h_some
  rw [Option.map_eq_some_iff] at h_some
  obtain ⟨off, h_find, rfl⟩ := h_some
  have h_mem : off ∈ List.range (64 - startBit) := List.mem_of_find?_eq_some h_find
  rw [List.mem_range] at h_mem
  obtain ⟨h_true, xs, ys, h_eq_list, h_all_false⟩ := List.find?_eq_some_iff_append.mp h_find
  refine ⟨by omega, by omega, by simpa [Nat.add_comm] using h_true, fun b h_lo h_lt => ?_⟩
  have h_pw : List.Pairwise (· < ·) (List.range (64 - startBit)) := List.pairwise_lt_range
  rw [h_eq_list, List.pairwise_append, List.pairwise_cons] at h_pw
  obtain ⟨_, ⟨h_lt_ys, _⟩, _⟩ := h_pw
  have h_b_mem : b - startBit ∈ List.range (64 - startBit) := by
    rw [List.mem_range]; omega
  rw [h_eq_list, List.mem_append, List.mem_cons] at h_b_mem
  rcases h_b_mem with h_in_xs | h_eq_off | h_in_ys
  · have hf := h_all_false (b - startBit) h_in_xs
    have h_sum : startBit + (b - startBit) = b := by omega
    simpa [Bool.not_eq_true, h_sum] using hf
  · omega
  · have := h_lt_ys (b - startBit) h_in_ys
    omega

private theorem testBit_wordMask_sub (w : UInt64) (bit : Nat) (h_bit : bit < 64) :
    Nat.testBit (wordMask - w.toNat) bit = !Nat.testBit w.toNat bit := by
  have h_wm : wordMask = 2 ^ 64 - 1 := by decide
  rw [h_wm]
  have h_lt := w.toNat_lt
  have h_bv : BitVec.ofNat 64 (2 ^ 64 - 1 - w.toNat) = ~~~(BitVec.ofNat 64 w.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_not]
    omega
  have h1 := congrArg (fun b : BitVec 64 => b.getLsbD bit) h_bv
  simp only [BitVec.getLsbD_ofNat, BitVec.getLsbD_not, h_bit, decide_true, Bool.true_and] at h1
  exact h1

private theorem searchBlock_spec (word : UInt64) (block startBit : Nat) (isInit : Bool)
    (h_block_fits : block * 64 + 63 ≤ 18446744073709551615) :
    ∃ res?, Miri.Memory.InitMaskMaterialized.searchBlock word block startBit isInit = .ok res? ∧
      match res? with
      | none => ∀ b, startBit ≤ b → b < 64 → Nat.testBit word.toNat b = !isInit
      | some idx =>
        ∃ bit, startBit ≤ bit ∧ bit < 64 ∧ idx.bytes.toNat = block * 64 + bit ∧
          Nat.testBit word.toNat bit = isInit ∧
          ∀ b, startBit ≤ b → b < bit → Nat.testBit word.toNat b = !isInit := by
  let bits := if isInit then word.toNat else wordMask - word.toNat
  have h_bits_tb : ∀ b, b < 64 → (Nat.testBit bits b = true ↔ Nat.testBit word.toNat b = isInit) := by
    intro b hb
    dsimp only [bits]
    cases isInit
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [testBit_wordMask_sub word b hb]
      cases word.toNat.testBit b <;> simp
    · simp
  have h_bits_false : ∀ b, b < 64 → (Nat.testBit bits b = false ↔ Nat.testBit word.toNat b = !isInit) := by
    intro b hb
    dsimp only [bits]
    cases isInit
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [testBit_wordMask_sub word b hb]
      cases word.toNat.testBit b <;> simp
    · simp
  cases h_fsb : Miri.Memory.InitMaskMaterialized.firstSetBit bits startBit with
  | none =>
    refine ⟨none, ?_, ?_⟩
    · unfold Miri.Memory.InitMaskMaterialized.searchBlock
      dsimp only [bits] at h_fsb
      unfold wordMask at h_fsb
      simp [h_fsb, Pure.pure, Except.pure]
    · intro b h_lo h_hi
      have hf := (firstSetBit_spec_none bits startBit).mp h_fsb b h_lo h_hi
      exact (h_bits_false b h_hi).mp hf
  | some bit =>
    obtain ⟨h_lo, h_hi, h_tb, h_prev⟩ := firstSetBit_spec_some bits startBit bit h_fsb
    have h_fits : block * 64 + bit ≤ Miri.Memory.maxSizeBytes := by
      unfold Miri.Memory.maxSizeBytes; omega
    have h_lt264 : block * 64 + bit < 2 ^ 64 := by omega
    let idx := Size.ofBytes (UInt64.ofNat (block * 64 + bit))
    have h_sfi : Miri.Memory.InitMaskMaterialized.sizeFromBitIndex block bit = .ok idx := by
      unfold Miri.Memory.InitMaskMaterialized.sizeFromBitIndex Miri.Memory.sizeFromNat Miri.Memory.blockSize
      rw [if_pos_eq h_fits]
    refine ⟨some idx, ?_, bit, h_lo, h_hi, ?_, (h_bits_tb bit h_hi).mp h_tb, ?_⟩
    · unfold Miri.Memory.InitMaskMaterialized.searchBlock
      dsimp only [bits] at h_fsb
      unfold wordMask at h_fsb
      simp [h_fsb, h_sfi, Bind.bind, Except.bind, Pure.pure, Except.pure]
    · simp [idx, Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h_lt264]
    · intro b hb_lo hb_lt
      exact (h_bits_false b (by omega)).mp (h_prev b hb_lo hb_lt)


private theorem search_blocks_list_spec (self : InitMaskMaterialized) (finish : Size) (isInit : Bool)
    (blocksList : List Nat)
    (h_sorted : List.Pairwise (· < ·) blocksList)
    (h_blocks_in : ∀ blk ∈ blocksList, blk < self.blocks.size)
    (h_blocks_fits : ∀ blk ∈ blocksList, blk * 64 + 63 ≤ 18446744073709551615) :
    ∃ out,
      forIn blocksList (none, ⟨⟩) (fun (block : Nat) (_ : Option (Option Size) × PUnit) =>
        (do
          match ← Miri.Memory.InitMaskMaterialized.searchBlock (← getBlock self block) block 0 isInit with
          | some index =>
            if Miri.Memory.sizeBytes index < Miri.Memory.sizeBytes finish then
              pure (ForInStep.done (some (some index), ⟨⟩))
            else
              pure (ForInStep.done (some none, ⟨⟩))
          | none => pure (ForInStep.yield (none, ⟨⟩)) :
          Except InitMaskError (ForInStep (Option (Option Size) × PUnit)))) = .ok (out, ⟨⟩) ∧
      match out with
      | none | some none =>
        ∀ blk (h_mem : blk ∈ blocksList) (b : Nat), b < 64 → blk * 64 + b < finish.bytes.toNat →
          Nat.testBit (self.blocks[blk]'(h_blocks_in blk h_mem)).toNat b = !isInit
      | some (some idx) =>
        ∃ blk, ∃ (h_mem : blk ∈ blocksList), ∃ bit, bit < 64 ∧
          idx.bytes.toNat = blk * 64 + bit ∧
          idx.bytes.toNat < finish.bytes.toNat ∧
          Nat.testBit (self.blocks[blk]'(h_blocks_in blk h_mem)).toNat bit = isInit ∧
          ∀ blk' (h_mem' : blk' ∈ blocksList) (b : Nat), b < 64 →
            blk' * 64 + b < idx.bytes.toNat →
            Nat.testBit (self.blocks[blk']'(h_blocks_in blk' h_mem')).toNat b = !isInit := by
  induction blocksList with
  | nil =>
    refine ⟨none, rfl, fun _ h => False.elim (List.not_mem_nil h)⟩
  | cons blk rest ih =>
    rw [List.pairwise_cons] at h_sorted
    obtain ⟨h_lt_rest, h_pw_rest⟩ := h_sorted
    have h_ib : blk < self.blocks.size := h_blocks_in blk (List.mem_cons_self ..)
    have h_fits : blk * 64 + 63 ≤ 18446744073709551615 := h_blocks_fits blk (List.mem_cons_self ..)
    have h_gb : getBlock self blk = .ok (self.blocks[blk]'h_ib) := get_block_ok self.blocks blk h_ib
    obtain ⟨res?, h_sb, h_sb_prop⟩ := searchBlock_spec (self.blocks[blk]'h_ib) blk 0 isInit h_fits
    cases res? with
    | none =>
      obtain ⟨tailOut, h_tail, h_tail_prop⟩ := ih h_pw_rest
        (fun x hx => h_blocks_in x (List.mem_cons_of_mem _ hx))
        (fun x hx => h_blocks_fits x (List.mem_cons_of_mem _ hx))
      refine ⟨tailOut, ?_, ?_⟩
      · simp only [List.forIn_cons, h_gb, h_sb, Bind.bind, Except.bind, Pure.pure, Except.pure]
        exact h_tail
      · cases tailOut with
        | none =>
          intro x hx b hb h_lt_fin
          rcases List.mem_cons.mp hx with rfl | hx_rest
          · exact h_sb_prop b (Nat.zero_le _) hb
          · exact h_tail_prop x hx_rest b hb h_lt_fin
        | some inner =>
          cases inner with
          | none =>
            intro x hx b hb h_lt_fin
            rcases List.mem_cons.mp hx with rfl | hx_rest
            · exact h_sb_prop b (Nat.zero_le _) hb
            · exact h_tail_prop x hx_rest b hb h_lt_fin
          | some idx =>
            obtain ⟨x, hx_rest, bit, hbit, h_idx_eq, h_lt_fin, h_tb, h_prev_rest⟩ := h_tail_prop
            refine ⟨x, List.mem_cons_of_mem _ hx_rest, bit, hbit, h_idx_eq, h_lt_fin, h_tb, ?_⟩
            intro x' hx' b hb h_lt_idx
            rcases List.mem_cons.mp hx' with rfl | hx'_rest
            · exact h_sb_prop b (Nat.zero_le _) hb
            · exact h_prev_rest x' hx'_rest b hb h_lt_idx
    | some idx =>
      obtain ⟨bit, _, hbit, h_idx_eq, h_tb, h_prev⟩ := h_sb_prop
      by_cases h_lt_fin : Miri.Memory.sizeBytes idx < Miri.Memory.sizeBytes finish
      · refine ⟨some (some idx), ?_, blk, List.mem_cons_self .., bit, hbit, h_idx_eq, ?_, h_tb, ?_⟩
        · simp [List.forIn_cons, h_gb, h_sb, h_lt_fin, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · simpa [Miri.Memory.sizeBytes] using h_lt_fin
        · intro x' hx' b hb h_lt_idx
          rcases List.mem_cons.mp hx' with rfl | hx'_rest
          · exact h_prev b (Nat.zero_le _) (by omega)
          · have := h_lt_rest x' hx'_rest
            omega
      · refine ⟨some none, ?_, ?_⟩
        · simp [List.forIn_cons, h_gb, h_sb, h_lt_fin, Bind.bind, Except.bind, Pure.pure, Except.pure]
        · have h_ge_fin : finish.bytes.toNat ≤ blk * 64 + bit := by
            simp only [Miri.Memory.sizeBytes] at h_lt_fin
            omega
          intro x hx b hb h_lt
          rcases List.mem_cons.mp hx with rfl | hx_rest
          · exact h_prev b (Nat.zero_le _) (by omega)
          · have := h_lt_rest x hx_rest
            omega

private theorem findBit_spec (self : InitMaskMaterialized) (start finish : Size) (isInit : Bool)
    (h_cap : finish.bytes.toNat ≤ self.blocks.size * 64) :
    ∃ res?, Miri.Memory.InitMaskMaterialized.findBit self start finish isInit = .ok res? ∧
      match res? with
      | none =>
        ∀ (idx : Size), start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < finish.bytes.toNat →
          Miri.Memory.InitMaskMaterialized.get self idx = .ok (!isInit)
      | some found =>
        start.bytes.toNat ≤ found.bytes.toNat ∧ found.bytes.toNat < finish.bytes.toNat ∧
          Miri.Memory.InitMaskMaterialized.get self found = .ok isInit ∧
          ∀ (idx : Size), start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < found.bytes.toNat →
            Miri.Memory.InitMaskMaterialized.get self idx = .ok (!isInit) := by
  unfold Miri.Memory.InitMaskMaterialized.findBit
    Miri.Memory.InitMaskMaterialized.findBitFast
  have h_fin_u64 := finish.bytes.toNat_lt
  by_cases h_empty : Miri.Memory.sizeBytes start ≥ Miri.Memory.sizeBytes finish
  · refine ⟨none, ?_, ?_⟩
    · simp [h_empty, Pure.pure, Except.pure]
    · intro idx h1 h2
      simp only [Miri.Memory.sizeBytes] at h_empty
      omega
  · rw [if_neg_eq h_empty]
    have h_lt_sf : start.bytes.toNat < finish.bytes.toNat := by
      simp only [Miri.Memory.sizeBytes] at h_empty; omega
    let startBlock := start.bytes.toNat / 64
    let startBit := start.bytes.toNat % 64
    let endIncNat := finish.bytes.toNat - 1
    have h_end_fits : endIncNat ≤ Miri.Memory.maxSizeBytes := by
      unfold Miri.Memory.maxSizeBytes; omega
    have h_sfn : Miri.Memory.sizeFromNat (finish.bytes.toNat - 1) =
        .ok (Size.ofBytes (UInt64.ofNat endIncNat)) := by
      unfold Miri.Memory.sizeFromNat
      dsimp only [endIncNat] at h_end_fits ⊢
      rw [if_pos_eq h_end_fits]
    have h_endInc_bytes : (Size.ofBytes (UInt64.ofNat endIncNat)).bytes.toNat = endIncNat := by
      simp [Size.ofBytes, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : endIncNat < 2 ^ 64)]
    let endBlock := endIncNat / 64
    have h_sb_ib : startBlock < self.blocks.size := by dsimp only [startBlock]; omega
    have h_eb_ib : endBlock < self.blocks.size := by dsimp only [endBlock, endIncNat]; omega
    have h_sb_fits : startBlock * 64 + 63 ≤ 18446744073709551615 := by
      dsimp only [startBlock]; omega
    have h_gb0 : Miri.Memory.InitMaskMaterialized.getBlock self startBlock = .ok (self.blocks[startBlock]'h_sb_ib) :=
      get_block_ok self.blocks startBlock h_sb_ib
    obtain ⟨first?, h_sb0, h_sb0_prop⟩ := searchBlock_spec (self.blocks[startBlock]'h_sb_ib) startBlock startBit isInit h_sb_fits
    have h_get_eq : ∀ (idx : Size) (h_ib : idx.bytes.toNat / 64 < self.blocks.size),
        Miri.Memory.InitMaskMaterialized.get self idx =
          .ok (Nat.testBit (self.blocks[idx.bytes.toNat / 64]'h_ib).toNat (idx.bytes.toNat % 64)) := by
      intro idx h_ib
      unfold Miri.Memory.InitMaskMaterialized.get Miri.Memory.InitMaskMaterialized.getBlock
        InitMaskMaterialized.bitIndex Miri.Memory.sizeBytes Miri.Memory.blockSize Miri.Memory.bitAt
      dsimp only
      rw [Array.getElem?_eq_getElem h_ib]
      rfl
    simp only [InitMaskMaterialized.bitIndex, Miri.Memory.sizeBytes, Miri.Memory.blockSize]
    rw [h_sfn]
    simp only [Bind.bind, Except.bind, h_endInc_bytes]
    dsimp only [startBlock, startBit, endBlock] at h_gb0 h_sb0 ⊢
    rw [h_gb0]
    simp only
    rw [h_sb0]
    simp only
    cases first? with
    | some firstIdx =>
      obtain ⟨bit, h_lo, h_hi, h_f_eq, h_tb, h_prev⟩ := h_sb0_prop
      by_cases h_lt_f : firstIdx.bytes.toNat < finish.bytes.toNat
      · refine ⟨some firstIdx, ?_, ?_⟩
        · simp [h_lt_f, Pure.pure, Except.pure]
        · have h_div : firstIdx.bytes.toNat / 64 = startBlock := by omega
          have h_mod : firstIdx.bytes.toNat % 64 = bit := by omega
          refine ⟨by dsimp only [startBlock, startBit] at h_lo h_f_eq; omega, h_lt_f, ?_, ?_⟩
          · rw [h_get_eq firstIdx (by omega)]
            simpa [h_div, h_mod] using h_tb
          · intro idx h_idx_lo h_idx_lt
            have h_idx_div : idx.bytes.toNat / 64 = startBlock := by
              dsimp only [startBlock, startBit] at h_lo h_f_eq; omega
            rw [h_get_eq idx (by omega)]
            have h_p := h_prev (idx.bytes.toNat % 64)
              (by dsimp only [startBlock, startBit] at h_idx_div ⊢; omega)
              (by dsimp only [startBlock] at h_idx_div h_f_eq; omega)
            simpa [h_idx_div] using h_p
      · refine ⟨none, ?_, ?_⟩
        · simp [h_lt_f, Pure.pure, Except.pure]
        · intro idx h_idx_lo h_idx_lt
          have h_idx_div : idx.bytes.toNat / 64 = startBlock := by
            dsimp only [startBlock, startBit] at h_f_eq h_lt_f; omega
          rw [h_get_eq idx (by omega)]
          have h_p := h_prev (idx.bytes.toNat % 64)
            (by dsimp only [startBlock, startBit] at h_idx_div ⊢; omega)
            (by dsimp only [startBlock] at h_idx_div h_f_eq h_lt_f; omega)
          simpa [h_idx_div] using h_p
    | none =>
      by_cases h_more : startBlock < endBlock
      · dsimp only [startBlock, endBlock, endIncNat] at h_more
        rw [if_pos_eq h_more]
        rw [Std.Legacy.Range.forIn_eq_forIn_range']
        let rngList := List.range' [startBlock + 1:endBlock + 1].start
          [startBlock + 1:endBlock + 1].size [startBlock + 1:endBlock + 1].step
        have h_mem_rng : ∀ x, x ∈ rngList ↔ (startBlock + 1 ≤ x ∧ x ≤ endBlock) := by
          intro x
          simp only [rngList, List.mem_range', Std.Legacy.Range.size, Nat.div_one, Nat.one_mul, Nat.sub_zero, Nat.add_zero]
          constructor
          · rintro ⟨i, hi, rfl⟩; omega
          · intro ⟨h1, h2⟩; exact ⟨x - (startBlock + 1), by omega, by omega⟩
        have h_pw_rng : List.Pairwise (· < ·) rngList := List.pairwise_lt_range'
        have h_in_rng : ∀ x ∈ rngList, x < self.blocks.size := by
          intro x hx; have := (h_mem_rng x).mp hx; omega
        have h_fits_rng : ∀ x ∈ rngList, x * 64 + 63 ≤ 18446744073709551615 := by
          intro x hx; have := (h_mem_rng x).mp hx
          dsimp only [endBlock, endIncNat] at this; omega
        obtain ⟨loopOut, h_loop, h_loop_prop⟩ := search_blocks_list_spec self finish isInit
          rngList h_pw_rng h_in_rng h_fits_rng
        unfold Miri.Memory.sizeBytes getBlock at h_loop
        dsimp only [rngList, startBlock, endBlock, endIncNat] at h_loop
        simp only [Bind.bind, Except.bind] at h_loop ⊢
        rw [h_loop]
        simp only [Pure.pure, Except.pure]
        cases loopOut with
        | none =>
          refine ⟨none, rfl, ?_⟩
          intro idx h_idx_lo h_idx_lt
          by_cases hk : idx.bytes.toNat / 64 = startBlock
          · rw [h_get_eq idx (by omega)]
            have h_p := h_sb0_prop (idx.bytes.toNat % 64)
              (by dsimp only [startBlock, startBit] at hk ⊢; omega)
              (Nat.mod_lt _ (by decide))
            simpa [hk] using h_p
          · have h_in_l : idx.bytes.toNat / 64 ∈ rngList :=
              (h_mem_rng _).mpr (by dsimp only [startBlock, endBlock, endIncNat] at hk ⊢; omega)
            rw [h_get_eq idx (h_in_rng _ h_in_l)]
            exact congrArg Except.ok
              (h_loop_prop (idx.bytes.toNat / 64) h_in_l (idx.bytes.toNat % 64)
                (Nat.mod_lt _ (by decide)) (by omega))
        | some inner =>
          cases inner with
          | none =>
            refine ⟨none, rfl, ?_⟩
            intro idx h_idx_lo h_idx_lt
            by_cases hk : idx.bytes.toNat / 64 = startBlock
            · rw [h_get_eq idx (by omega)]
              have h_p := h_sb0_prop (idx.bytes.toNat % 64)
                (by dsimp only [startBlock, startBit] at hk ⊢; omega)
                (Nat.mod_lt _ (by decide))
              simpa [hk] using h_p
            · have h_in_l : idx.bytes.toNat / 64 ∈ rngList :=
                (h_mem_rng _).mpr (by dsimp only [startBlock, endBlock, endIncNat] at hk ⊢; omega)
              rw [h_get_eq idx (h_in_rng _ h_in_l)]
              exact congrArg Except.ok
                (h_loop_prop (idx.bytes.toNat / 64) h_in_l (idx.bytes.toNat % 64)
                  (Nat.mod_lt _ (by decide)) (by omega))
          | some found =>
            obtain ⟨blk, h_blk_mem, bit, hbit, h_f_eq, h_f_lt, h_f_tb, h_f_prev⟩ := h_loop_prop
            have h_blk_bounds := (h_mem_rng blk).mp h_blk_mem
            have h_f_div : found.bytes.toNat / 64 = blk := by omega
            have h_f_mod : found.bytes.toNat % 64 = bit := by omega
            refine ⟨some found, rfl, ?_, h_f_lt, ?_, ?_⟩
            · dsimp only [startBlock] at h_blk_bounds; omega
            · rw [h_get_eq found (by omega)]
              simpa [h_f_div, h_f_mod] using h_f_tb
            · intro idx h_idx_lo h_idx_lt
              by_cases hk : idx.bytes.toNat / 64 = startBlock
              · rw [h_get_eq idx (by omega)]
                have h_p := h_sb0_prop (idx.bytes.toNat % 64)
                  (by dsimp only [startBlock, startBit] at hk ⊢; omega)
                  (Nat.mod_lt _ (by decide))
                simpa [hk] using h_p
              · have h_in_l : idx.bytes.toNat / 64 ∈ rngList := (h_mem_rng _).mpr (by
                  dsimp only [startBlock, endBlock, endIncNat] at hk h_blk_bounds ⊢; omega)
                rw [h_get_eq idx (h_in_rng _ h_in_l)]
                exact congrArg Except.ok
                  (h_f_prev (idx.bytes.toNat / 64) h_in_l (idx.bytes.toNat % 64)
                    (Nat.mod_lt _ (by decide)) (by omega))
      · dsimp only [startBlock, endBlock, endIncNat] at h_more
        rw [if_neg_eq h_more]
        refine ⟨none, rfl, ?_⟩
        intro idx h_idx_lo h_idx_lt
        have h_idx_div : idx.bytes.toNat / 64 = startBlock := by
          dsimp only [startBlock] at h_more ⊢; omega
        rw [h_get_eq idx (by omega)]
        have h_p := h_sb0_prop (idx.bytes.toNat % 64)
          (by dsimp only [startBlock, startBit] at h_idx_div ⊢; omega)
          (Nat.mod_lt _ (by decide))
        simpa [h_idx_div] using h_p

private theorem fromEndpoints_ok_of_le (a b : Size) (h : a.bytes.toNat ≤ b.bytes.toNat) :
    ∃ r, AllocRange.fromEndpoints a b = .ok r ∧ r.start = a ∧
      r.size.bytes.toNat = b.bytes.toNat - a.bytes.toNat := by
  have h_le : a.bytes ≤ b.bytes := UInt64.le_iff_toNat_le.mpr h
  have h_not_lt : ¬(b.bytes < a.bytes) := UInt64.not_lt.mpr h_le
  refine ⟨⟨a, Size.ofBytes (b.bytes - a.bytes)⟩, ?_, rfl, ?_⟩
  · unfold AllocRange.fromEndpoints Size.sub
    simp [h_not_lt, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure]
  · simp [Size.ofBytes, UInt64.toNat_sub_of_le _ _ h_le]

theorem isRangeInitialized_nonempty_iff (mask : InitMask) (range : AllocRange) (finish : Size)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat) :
    (mask.isRangeInitialized range = .ok (.ok ()) ↔
      ∀ (idx : Size), range.start.bytes.toNat ≤ idx.bytes.toNat → idx.bytes.toNat < finish.bytes.toNat →
        mask.get idx = .ok true) ∧
    ((∃ idx : Size, range.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < finish.bytes.toNat ∧
        mask.get idx = .ok false) →
      ∃ bad : AllocRange, mask.isRangeInitialized range = .ok (.error bad)) := by
  have h_not_oob : ¬(finish.bytes > mask.len.bytes) := by
    simpa [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
  cases mask with
  | mk blocks len =>
    dsimp only at inBounds h_not_oob
    cases blocks with
    | Lazy state =>
      unfold InitMask.isRangeInitialized InitMask.get
      simp only [endpoint, Bind.bind, Except.bind, h_not_oob, ↓reduceIte, Pure.pure, Except.pure]
      cases state
      · simp only [Bool.false_eq_true, ↓reduceIte]
        constructor
        · constructor
          · intro h; cases h
          · intro h_all
            have h_start := h_all range.start (Nat.le_refl _) nonempty
            cases h_start
        · intro _
          exact ⟨range, rfl⟩
      · simp only [↓reduceIte]
        constructor
        · constructor
          · intro _ _ _ _; trivial
          · intro _; trivial
        · rintro ⟨_, _, _, hf⟩
          cases hf
    | Materialized mat =>
      dsimp only [WellFormed] at valid
      have h_cap : finish.bytes.toNat ≤ mat.blocks.size * 64 := by omega
      obtain ⟨uninit?, h_fb0, h_fb0_prop⟩ := findBit_spec mat range.start finish false h_cap
      unfold InitMask.isRangeInitialized InitMask.get
      simp only [endpoint, Bind.bind, Except.bind, h_not_oob, ↓reduceIte, h_fb0]
      cases uninit? with
      | none =>
        dsimp only at h_fb0_prop ⊢
        simp only [Pure.pure, Except.pure, Bool.not_false] at h_fb0_prop ⊢
        constructor
        · constructor
          · intro _ idx h1 h2; exact h_fb0_prop idx h1 h2
          · intro _; trivial
        · rintro ⟨idx, h1, h2, hf⟩
          have ht : Miri.Memory.InitMaskMaterialized.get mat idx = .ok true := h_fb0_prop idx h1 h2
          rw [ht] at hf
          cases hf
      | some uninitStart =>
        dsimp only at h_fb0_prop ⊢
        obtain ⟨h_us_lo, h_us_lt, h_us_get, _⟩ := h_fb0_prop
        obtain ⟨end?, h_fb1, h_fb1_prop⟩ := findBit_spec mat uninitStart finish true h_cap
        rw [h_fb1]
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
        have h_end_ge : uninitStart.bytes.toNat ≤ (end?.getD finish).bytes.toNat := by
          cases end? with
          | none => exact Nat.le_of_lt h_us_lt
          | some e => exact h_fb1_prop.1
        obtain ⟨bad, h_bad, _, _⟩ := fromEndpoints_ok_of_le uninitStart (end?.getD finish) h_end_ge
        rw [h_bad]
        simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
        constructor
        · constructor
          · intro h; cases h
          · intro h_all
            have ht := h_all uninitStart h_us_lo h_us_lt
            rw [h_us_get] at ht
            cases ht
        · intro _
          exact ⟨bad, rfl⟩


theorem isRangeInitialized_after_setRange_true (mask updated : InitMask)
    (range : AllocRange) (finish : Size)
    (valid : WellFormed mask) (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (h_set : mask.setRange range true = .ok updated) :
    updated.isRangeInitialized range = .ok (.ok ()) := by
  obtain ⟨u, h_u, h_len, h_wf⟩ := set_range_exists mask range finish true valid endpoint nonempty inBounds
  have h_eq : u = updated := Except.ok.inj (h_u.symm.trans h_set)
  subst h_eq
  rw [(isRangeInitialized_nonempty_iff u range finish h_wf endpoint nonempty (by rw [h_len]; exact inBounds)).1]
  intro idx h_lo h_hi
  have h_idx_ib : idx.bytes.toNat < mask.len.bytes.toNat := by omega
  rw [set_range_get mask u range finish idx true valid endpoint nonempty inBounds h_idx_ib h_u]
  rw [if_pos_eq ⟨h_lo, h_hi⟩]

theorem isRangeInitialized_frame (mask updated : InitMask)
    (writeRange queryRange : AllocRange) (writeFinish queryFinish : Size) (state : Bool)
    (valid : WellFormed mask)
    (wEnd : writeRange.endExclusive = .ok writeFinish)
    (qEnd : queryRange.endExclusive = .ok queryFinish)
    (wNonempty : writeRange.start.bytes.toNat < writeFinish.bytes.toNat)
    (qNonempty : queryRange.start.bytes.toNat < queryFinish.bytes.toNat)
    (wInBounds : writeFinish.bytes.toNat ≤ mask.len.bytes.toNat)
    (qInBounds : queryFinish.bytes.toNat ≤ mask.len.bytes.toNat)
    (disjoint : writeFinish.bytes.toNat ≤ queryRange.start.bytes.toNat ∨
      queryFinish.bytes.toNat ≤ writeRange.start.bytes.toNat)
    (h_set : mask.setRange writeRange state = .ok updated) :
    (updated.isRangeInitialized queryRange = .ok (.ok ()) ↔
      mask.isRangeInitialized queryRange = .ok (.ok ())) := by
  obtain ⟨u, h_u, h_len, h_wf⟩ := set_range_exists mask writeRange writeFinish state valid wEnd wNonempty wInBounds
  have h_eq : u = updated := Except.ok.inj (h_u.symm.trans h_set)
  subst h_eq
  rw [(isRangeInitialized_nonempty_iff u queryRange queryFinish h_wf qEnd qNonempty (by rw [h_len]; exact qInBounds)).1]
  rw [(isRangeInitialized_nonempty_iff mask queryRange queryFinish valid qEnd qNonempty qInBounds).1]
  constructor
  · intro h idx h_lo h_hi
    have h_out : ¬(writeRange.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < writeFinish.bytes.toNat) := by
      omega
    have h_get := set_range_get mask u writeRange writeFinish idx state valid wEnd wNonempty wInBounds (by omega) h_u
    rw [if_neg_eq h_out] at h_get
    exact h_get.symm.trans (h idx h_lo h_hi)
  · intro h idx h_lo h_hi
    have h_out : ¬(writeRange.start.bytes.toNat ≤ idx.bytes.toNat ∧ idx.bytes.toNat < writeFinish.bytes.toNat) := by
      omega
    have h_get := set_range_get mask u writeRange writeFinish idx state valid wEnd wNonempty wInBounds (by omega) h_u
    rw [if_neg_eq h_out] at h_get
    exact h_get.trans (h idx h_lo h_hi)

private theorem endExclusive_size_eq (range : AllocRange) (finish : Size)
    (endpoint : range.endExclusive = .ok finish) :
    finish.bytes.toNat = range.start.bytes.toNat + range.size.bytes.toNat ∧
      finish.bytes - range.start.bytes = range.size.bytes := by
  unfold AllocRange.endExclusive AllocRange.end Size.add at endpoint
  by_cases h_wrap : range.start.bytes + range.size.bytes < range.start.bytes
  · simp [h_wrap, Except.mapError] at endpoint
  · simp only [h_wrap, ↓reduceIte, Except.mapError, Except.ok.injEq] at endpoint
    subst endpoint
    have h_nw : ¬((range.start.bytes + range.size.bytes).toNat < range.start.bytes.toNat) := by
      simpa [UInt64.lt_iff_toNat_lt] using h_wrap
    have h1 := range.start.bytes.toNat_lt
    have h2 := range.size.bytes.toNat_lt
    have h_fits : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64 := by
      by_cases h_lt : range.start.bytes.toNat + range.size.bytes.toNat < 2 ^ 64
      · exact h_lt
      · have h_mod : (range.start.bytes + range.size.bytes).toNat =
            range.start.bytes.toNat + range.size.bytes.toNat - 2 ^ 64 := by
          rw [UInt64.toNat_add]; omega
        omega
    constructor
    · simp [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]
    · apply UInt64.toNat_inj.mp
      have h_le : range.start.bytes ≤ (Size.ofBytes (range.start.bytes + range.size.bytes)).bytes := by
        simp [Size.ofBytes, UInt64.le_iff_toNat_le, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]
      rw [UInt64.toNat_sub_of_le _ _ h_le]
      simp [Size.ofBytes, UInt64.toNat_add, Nat.mod_eq_of_lt h_fits]

theorem prepareCopy_of_uniform (mask : InitMask) (range : AllocRange) (finish : Size) (state : Bool)
    (valid : WellFormed mask)
    (endpoint : range.endExclusive = .ok finish)
    (nonempty : range.start.bytes.toNat < finish.bytes.toNat)
    (inBounds : finish.bytes.toNat ≤ mask.len.bytes.toNat)
    (uniform : ∀ (idx : Size), range.start.bytes.toNat ≤ idx.bytes.toNat →
      idx.bytes.toNat < finish.bytes.toNat → mask.get idx = .ok state) :
    mask.prepareCopy range = .ok ⟨state, #[range.size.bytes]⟩ := by
  obtain ⟨h_fin_eq, h_sub_eq⟩ := endExclusive_size_eq range finish endpoint
  have h_sz_pos : 0 < range.size.bytes.toNat := by omega
  have h_sz_nz : range.size.bytes ≠ 0 := fun h0 => by
    have : range.size.bytes.toNat = 0 := by simp [h0]
    omega
  have h_sz_beq : (range.size.bytes == 0) = false := beq_false_of_ne h_sz_nz
  have h_not_oob : ¬(finish.bytes > mask.len.bytes) := by
    simpa [UInt64.lt_iff_toNat_lt] using Nat.not_lt.mpr inBounds
  have h_lt_u64 : range.start.bytes < finish.bytes := UInt64.lt_iff_toNat_lt.mpr nonempty
  have h_not_gt_sf : ¬(range.start.bytes > finish.bytes) :=
    UInt64.not_lt.mpr (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt nonempty))
  have h_not_le_fs : ¬(finish.bytes ≤ range.start.bytes) :=
    UInt64.not_le.mpr h_lt_u64
  have h_get_start : mask.get range.start = .ok state := uniform range.start (Nat.le_refl _) nonempty
  have h_raic : mask.rangeAsInitChunks range = .ok ⟨mask, state, range.start, finish⟩ := by
    unfold InitMask.rangeAsInitChunks
    simp [endpoint, h_not_oob, h_lt_u64, h_get_start, Bind.bind, Except.bind, Pure.pure, Except.pure]
  let chunk0 : InitChunk := if state then .Init range.start finish else .Uninit range.start finish
  have h_next0 : (⟨mask, state, range.start, finish⟩ : InitChunkIter).next? =
      .ok (some (chunk0, ⟨mask, !state, finish, finish⟩)) := by
    unfold InitChunkIter.next? Miri.Memory.sizeBytes
    have h_not_ge : ¬(range.start.bytes.toNat ≥ finish.bytes.toNat) := by omega
    cases mask with
    | mk blocks len =>
      dsimp only at inBounds h_not_oob h_get_start ⊢
      cases blocks with
      | Lazy s =>
        have h_s_eq : s = state := Except.ok.inj h_get_start
        subst h_s_eq
        simp [h_not_gt_sf, h_not_oob, h_not_ge, h_not_le_fs, chunk0,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
      | Materialized mat =>
        dsimp only [WellFormed] at valid
        obtain ⟨found?, h_fb, h_fb_prop⟩ := findBit_spec mat range.start finish (!state) (by omega)
        have h_found_none : found? = none := by
          cases found? with
          | none => rfl
          | some f =>
            obtain ⟨h_lo, h_hi, h_f_get, _⟩ := h_fb_prop
            have h_u := uniform f h_lo h_hi
            unfold InitMask.get at h_u
            dsimp only at h_u
            rw [h_f_get] at h_u
            cases state <;> cases h_u
        subst h_found_none
        simp [h_not_gt_sf, h_not_oob, h_not_ge, h_fb, h_not_le_fs, chunk0,
          Bind.bind, Except.bind, Pure.pure, Except.pure]
  have h_next1 : (⟨mask, !state, finish, finish⟩ : InitChunkIter).next? = .ok none := by
    unfold InitChunkIter.next? Miri.Memory.sizeBytes
    have h_not_ff : ¬(finish.bytes > finish.bytes) := UInt64.lt_irrefl _
    simp [h_not_ff, h_not_oob, Pure.pure, Except.pure]
  have h_fuel_eq : Miri.Memory.sizeBytes finish - Miri.Memory.sizeBytes range.start + 1 =
      (finish.bytes.toNat - range.start.bytes.toNat - 1) + 1 + 1 := by
    unfold Miri.Memory.sizeBytes; omega
  have h_collect : InitMask.collectChunks ⟨mask, state, range.start, finish⟩ = .ok #[chunk0] := by
    unfold InitMask.collectChunks
    rw [h_fuel_eq]
    unfold Miri.Memory.InitMask.collectChunksAux
    rw [h_next0]
    simp only [Bind.bind, Except.bind]
    unfold Miri.Memory.InitMask.collectChunksAux
    rw [h_next1]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure]
  have h_chunk_isInit : chunk0.isInit = state := by
    dsimp only [chunk0]; cases state <;> rfl
  have h_chunk_range : chunk0.range = .ok ⟨range.start, range.size⟩ := by
    dsimp only [chunk0]
    have h_le : range.start.bytes ≤ finish.bytes := UInt64.le_of_lt h_lt_u64
    have h_not_lt : ¬(finish.bytes < range.start.bytes) := UInt64.not_lt.mpr h_le
    cases state <;> {
      unfold InitChunk.range AllocRange.fromEndpoints Size.sub
      simp [h_not_lt, h_sub_eq, Size.ofBytes, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure]
    }
  unfold InitMask.prepareCopy
  simp only [h_sz_beq, Bool.false_eq_true, ↓reduceIte, h_raic, Bind.bind, Except.bind, h_collect]
  rw [← Array.forIn_toList]
  simp [List.forIn_cons, List.forIn_nil, h_chunk_range, h_chunk_isInit,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem applyCopy_singleton (destMask : InitMask) (destStart srcSize total : Size)
    (repeatCount : UInt64) (state : Bool)
    (nonzero : srcSize.bytes ≠ 0)
    (h_mul : Size.mul srcSize repeatCount = .ok total) :
    destMask.applyCopy ⟨state, #[srcSize.bytes]⟩ (allocRange destStart srcSize) repeatCount =
      destMask.setRange (allocRange destStart total) state := by
  unfold InitMask.applyCopy
  simp [nonzero, allocRange, h_mul, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]


end Miri.Memory.InitMask.WriteProof

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "Miri.Memory.InitMask.WriteProof.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mask write axiom {dependency} in {name}"
