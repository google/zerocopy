import ToyUnwindCap.Basic

/-!
# Mixed-backend call chains

A separate, smaller toy model for composing functions compiled by backends with different
landing-pad capabilities.

* Normal returns: each frame of a call chain receives its callee's return value through an
  ABI encoding chosen by the callee's backend and a decoding chosen by its own backend
  (`compRet`), compared with the value-level specification (`specRet`).
* Unwinding: a chain is the list of frames live when an unwind starts, innermost first. Each
  frame records the capability of the backend that compiled it and the landing-pad action of
  its active call site. The specified unwind (`specUnwind`) performs every frame's action; the
  compiled unwind (`compUnwind`) performs no action in a frame compiled with `pads = none`.
  Events and catch outcomes are tagged with the frame's position in the chain.

This model is not derived from the program semantics of `ToyUnwindCap.Basic`; the two are
related informally (not proved here).
-/

namespace Toy.UnwindCap

/-! ## Normal returns through an ABI -/

/-- A backend's ABI encoding of a return value (`enc`) and decoding of a received one
(`dec`), over a toy value domain `Nat`. -/
structure AbiCodec where
  enc : Nat → Nat
  dec : Nat → Nat

/-- An ABI round-trips: decoding an encoded value gives the value back. -/
def AbiCodec.Lawful (a : AbiCodec) : Prop := ∀ v, a.dec (a.enc v) = v

/-- Backend `b` conforms to the platform ABI `A`: it uses `A`'s encoding and decoding. -/
def Conforms (b A : AbiCodec) : Prop := b.enc = A.enc ∧ b.dec = A.dec

/-- A frame on the normal-return path: the backend that compiled it and what it computes from
its callee's return value. -/
structure RetFrame where
  backend : AbiCodec
  k : Nat → Nat

/-- Specified result of a chain (frames listed callee to caller) whose innermost callee returns
`v`. -/
def specRet : List RetFrame → Nat → Nat
  | [], v => v
  | fr :: rest, v => specRet rest (fr.k v)

/-- Compiled result: the callee (compiled by backend `b`) encodes its return value with `b.enc`;
the caller decodes it with its own backend's `dec`. The outermost frame's result is observed
directly. -/
def compRet : AbiCodec → List RetFrame → Nat → Nat
  | _, [], v => v
  | b, fr :: rest, v => compRet fr.backend rest (fr.k (fr.backend.dec (b.enc v)))

/-! ## Unwinding through a chain -/

/-- One frame of a chain at the moment an unwind starts: the capability of the backend that
compiled it and the landing-pad action of its active call site. -/
structure UFrame where
  pads : Pads
  act : Action
  deriving DecidableEq, Repr

/-- Chain events: a destructor of local `x` in the frame at position `frame` ran, or that frame
caught the unwind. -/
inductive UEvent where
  | drop (frame x : Nat)
  | caught (frame : Nat)
  deriving DecidableEq, Repr

/-- The frame position an event is tagged with. -/
def UEvent.frame : UEvent → Nat
  | .drop i _ => i
  | .caught i => i

/-- Outcome of an unwind through a chain: it leaves the outermost frame, is caught by the frame
at position `frame`, or aborts. -/
inductive UOut where
  | escapes
  | caught (frame : Nat)
  | aborted
  deriving DecidableEq, Repr

/-- The action a frame's landing pad performs when compiled: a `pads = none` frame performs
none, and the unwind then continues to the next frame (the frame is assumed to be unwindable, as
with frame-unwind tables but no landing pads). -/
def UFrame.effAct (fr : UFrame) : Action :=
  match fr.pads with
  | .full => fr.act
  | .none => .none

/-- Unwind through a chain starting at position `i`, performing `actOf fr` in each frame. -/
def unwindWith (actOf : UFrame → Action) : Nat → List UFrame → List UEvent × UOut
  | _, [] => ([], .escapes)
  | i, fr :: rest =>
    match actOf fr with
    | .none => unwindWith actOf (i + 1) rest
    | .cleanup ds =>
      let r := unwindWith actOf (i + 1) rest
      (ds.map (UEvent.drop i) ++ r.1, r.2)
    | .catchPad => ([.caught i], .caught i)
    | .terminate => ([], .aborted)

/-- The specified unwind: every frame performs its action. -/
def specUnwind (c : List UFrame) : List UEvent × UOut := unwindWith UFrame.act 0 c

/-- The compiled unwind: frames compiled with `pads = none` perform no action. -/
def compUnwind (c : List UFrame) : List UEvent × UOut := unwindWith UFrame.effAct 0 c

/-- Every frame that the specified unwind reaches (up to and including the first frame whose
action stops it) and that has an obligation was compiled with `pads = full`. -/
def ObligationsFull : List UFrame → Prop
  | [] => True
  | fr :: rest =>
    (fr.act.obligation = true → fr.pads = .full) ∧ (fr.act.Stops = false → ObligationsFull rest)

/-- No frame that the specified unwind reaches (up to and including the first frame whose action
stops it) is a `pads = none` frame with a terminate pad. Frames after the first stopping frame are
not constrained. -/
def NoReachedNoneTerminate : List UFrame → Prop
  | [] => True
  | fr :: rest =>
    (fr.pads = .none → fr.act ≠ .terminate) ∧
    (fr.act.Stops = false → NoReachedNoneTerminate rest)

/-- Scanning from the innermost frame, every frame is compiled with `pads = full` until a frame
whose action stops the unwind (or the end of the chain): no `pads = none` frame can be reached
by the unwind. -/
def Shielded : List UFrame → Prop
  | [] => True
  | fr :: rest => fr.pads = .full ∧ (fr.act.Stops = true ∨ Shielded rest)

/-- Like `Shielded`, but with terminate pads: scanning from the innermost frame, every frame is
compiled with `pads = full` up to and including the first frame with a terminate pad (or up to the
end of the chain if there is none). -/
def TerminateShielded : List UFrame → Prop
  | [] => True
  | fr :: rest => fr.pads = .full ∧ (fr.act = .terminate ∨ TerminateShielded rest)

/-- Two chains with the same backends frame by frame and the same actions at every
`pads = full` frame (actions at `pads = none` frames may differ). -/
def SameShape : List UFrame → List UFrame → Prop
  | [], [] => True
  | a :: as, b :: bs => a.pads = b.pads ∧ (a.pads = .full → a.act = b.act) ∧ SameShape as bs
  | _, _ => False

end Toy.UnwindCap
