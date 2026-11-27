-- Zone-2 public-safe proof spec for Asterinas `ostd::mm::frame::meta::mapping::frame_to_meta`

prelude
import Trusted.MirSemantics

namespace Spec

open Trusted.MirAst Trusted.MirSemantics

def frameToMetaIdentity : String := "rust-path-v1::frame_to_meta"

def frameMetadataBase : Nat := 18446708889337462784 -- 0xffff_e000_0000_0000
def pageSize : Nat := 4096
def metaSlotSize : Nat := 64
def maxSafePaddr : Nat := 2251799813685248 -- 2^51: base + (paddr / 4096) * 64 < 2^64

def expectedMetaVaddr (paddr : Nat) : Nat :=
  frameMetadataBase + (paddr / pageSize) * metaSlotSize

/-- Total specification allowing overflow panic-abort above `maxSafePaddr` (`>= 2^51`)
and proving exact affine metadata mapping below `maxSafePaddr`. -/
def frameToMetaAllowAbort : SafeContractV2 := {
  behaviorPre := fun _ => True
  effects := { allowAbort := true }
  postReturn := fun q out =>
    match q.args with
    | [.scalar p] =>
      p.bits.toNat < maxSafePaddr ∧
      out.ret = .scalar ⟨.isize, false, BitVec.ofNat 128 (expectedMetaVaddr p.bits.toNat)⟩ ∧
      out.callerMem = q.callerMem
    | _ => False
  postAbort := fun q cm =>
    match q.args with
    | [.scalar p] =>
      maxSafePaddr ≤ p.bits.toNat ∧ cm = q.callerMem
    | _ => False
}

/-- Non-panicking specification under the Asterinas physical-address bound `paddr < 2^51`
(which covers all 48-bit physical memory addresses). -/
def frameToMetaNoAbort : SafeContractV2 := {
  behaviorPre := fun q =>
    match q.args with
    | [.scalar p] => p.bits.toNat < maxSafePaddr
    | _ => False
  effects := EffectMaskV2.noAbort
  postReturn := frameToMetaAllowAbort.postReturn
}

def property (p : Program) : Prop :=
  p.overflowChecks = true ∧
  p.panicStrategy = .abort ∧
  match Trusted.MirSemantics.getElem? p.bodies 0 with
  | some body0 =>
    body0.identity = frameToMetaIdentity ∧
    body0.isUnsafe = false ∧
    BodySatisfiesSafeContractV2 p 0 body0 frameToMetaAllowAbort ∧
    BodySatisfiesSafeContractV2 p 0 body0 frameToMetaNoAbort
  | none => False

def specs : SpecsV2 := ⟨fun _ _ => True, property⟩

end Spec
