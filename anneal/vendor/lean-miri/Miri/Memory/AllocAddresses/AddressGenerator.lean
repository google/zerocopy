import Miri.ABI.Size
import Miri.ABI.Align

/-! A checked, source-shaped port of Miri's allocation `AddressGenerator`.
The source RNG's `0..16` sample is represented by `Fin 16`, rather than by a
fixed seed or a chosen pseudo-random stream. -/

namespace Miri.Memory.AllocAddresses

open Miri.ABI

structure AddressRange where
  start : UInt64
  stop : UInt64
  deriving DecidableEq, Repr, Inhabited

structure AddressGenerator where
  nextBaseAddr : UInt64
  endAddr : UInt64
  deriving DecidableEq, Repr, Inhabited

inductive AddressGeneratorError where
  | invalidAlignment (error : AlignError)
  | zeroAlignment
  | slackAdditionOverflow (address : UInt64) (slack : UInt64)
  | alignmentRoundingOverflow (address align : UInt64)
  | allocationEndOverflow (address length : UInt64)
  | addressSpaceFull (next endAddr : UInt64)
  deriving DecidableEq, Repr

instance : ToString AddressGeneratorError where
  toString
    | .invalidAlignment error => toString error
    | .zeroAlignment => "AddressGenerator.alignAddr received a zero alignment"
    | .slackAdditionOverflow address slack =>
        s!"AddressGenerator: {address} + slack {slack} overflows u64"
    | .alignmentRoundingOverflow address align =>
        s!"AddressGenerator: aligning {address} to {align} overflows u64"
    | .allocationEndOverflow address length =>
        s!"AddressGenerator: allocation at {address} with length {length} overflows u64"
    | .addressSpaceFull next endAddr =>
        s!"AddressGenerator: next address {next} exceeds address-space end {endAddr}"

structure AddressGenerationResult where
  state : AddressGenerator
  outcome : Except AddressGeneratorError UInt64

namespace AddressGenerator

def new (start stop : UInt64) : AddressGenerator := ⟨start, stop⟩

def getRemaining (generator : AddressGenerator) : AddressRange :=
  ⟨generator.nextBaseAddr, generator.endAddr⟩

/-- The source sample is from the half-open range `0..16`. -/
def legalSlack (slack : Fin 16) : Prop := slack.val < 16

theorem slack_is_legal (slack : Fin 16) : legalSlack slack := slack.isLt

/-- Source `align_addr`, with the `strict_add` overflow made explicit. This
preserves the source's evaluation order: it adds the whole alignment before
subtracting the remainder. -/
def alignAddr (address alignment : UInt64) : Except AddressGeneratorError UInt64 := do
  if alignment == 0 then
    throw .zeroAlignment
  let remainder := address % alignment
  if remainder == 0 then
    return address
  let added := address + alignment
  if added < address then
    throw (.alignmentRoundingOverflow address alignment)
  return added - remainder

/-- Execute one source generation step using a legal source random choice.
The state includes the source mutation made before its final address-space
check, including the updated next address on an exhaustion error. -/
def generate (generator : AddressGenerator) (size : Size) (align : Align)
    (slack : Fin 16) : AddressGenerationResult := Id.run do
  let alignment ← match Align.bytes align with
    | .ok value => pure value
    | .error error =>
        return { state := generator, outcome := .error (.invalidAlignment error) }
  match Align.fromBytes alignment with
  | .error error =>
      return { state := generator, outcome := .error (.invalidAlignment error) }
  | .ok normalized =>
      if normalized != align then
        return { state := generator, outcome := .error (.invalidAlignment (.tooLarge alignment)) }
  let address := generator.nextBaseAddr
  let slackBytes := UInt64.ofNat slack.val
  let withSlack := address + slackBytes
  if withSlack < address then
    return { state := generator, outcome := .error (.slackAdditionOverflow address slackBytes) }
  let baseAddr ← match alignAddr withSlack alignment with
    | .ok value => pure value
    | .error error => return { state := generator, outcome := .error error }
  let allocationLength := if size.bytes < 1 then 1 else size.bytes
  let nextBaseAddr := baseAddr + allocationLength
  if nextBaseAddr < baseAddr then
    return { state := generator, outcome := .error (.allocationEndOverflow baseAddr allocationLength) }
  let nextGenerator := { generator with nextBaseAddr }
  if nextBaseAddr > generator.endAddr then
    return { state := nextGenerator, outcome := .error (.addressSpaceFull nextBaseAddr generator.endAddr) }
  return { state := nextGenerator, outcome := .ok baseAddr }

end AddressGenerator

end Miri.Memory.AllocAddresses
