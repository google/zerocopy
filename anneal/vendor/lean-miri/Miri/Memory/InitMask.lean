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


end Miri.Memory.InitMask.WriteProof

open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "Miri.Memory.InitMask.WriteProof.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved mask write axiom {dependency} in {name}"
