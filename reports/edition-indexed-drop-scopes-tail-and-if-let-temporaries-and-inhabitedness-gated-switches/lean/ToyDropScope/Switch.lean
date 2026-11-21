/-
Toy switch-on-discriminant model and the inhabitedness-gated specialization.

These are definitions of a toy model. They are meant to capture (a) a `SwitchInt` terminator
that branches on the value produced by a discriminant read; (b) two candidate semantics for reading
the discriminant of a value whose tag denotes an uninhabited variant (`UninhabitedRead`), both kept
open because the documentation of `Rvalue::Discriminant` says the validity requirements of that
read are undecided; (c) for tags that denote no variant, the rejecting read and a synthetic
`passThrough` read (`InvalidRead`), which is a modeling boundary used to show that rejecting such
tags is separately needed for soundness on all tags, and is not presented as a semantics under
consideration for Rust; and (d) the rewrite documented in the source comments of an
unreachable-enum-branching pass. They are not the compiler's definitions.
-/

namespace Toy.DropScope

/-- A switch arm target: `unreachable` (reaching it is undefined behaviour), `goto k`
(continue normally, observably as `k`), or `usePayload k` (read the payload of the variant
denoted by the tag, then continue as `k`). -/
inductive Arm where
  | unreachable
  | goto (k : Nat)
  | usePayload (k : Nat)
  deriving DecidableEq, Repr

/-- A switch on an integer: explicit `arms` (value, target), searched in order, and the
wildcard target `otherwise`. -/
structure Switch where
  arms : List (Nat × Arm)
  otherwise : Arm
  deriving DecidableEq, Repr

/-- Outcomes: undefined behaviour, or normal continuation observed as `k`. -/
inductive Outcome where
  | ub
  | ret (k : Nat)
  deriving DecidableEq, Repr

/-- The target selected for switch value `t`: the first explicit arm with value `t`, else the
wildcard target. -/
def Switch.target (sw : Switch) (t : Nat) : Arm :=
  match sw.arms.find? (fun a => a.1 == t) with
  | some a => a.2
  | none => sw.otherwise

/-- Running a target on tag `t`; `payloadOK t` says whether the tag denotes a variant whose
payload can be used. -/
def runArm (payloadOK : Nat → Bool) (t : Nat) : Arm → Outcome
  | .unreachable => .ub
  | .goto k => .ret k
  | .usePayload k => if payloadOK t then .ret k else .ub

/-- Executing "read the discriminant of a value with tag `t`, then switch on it":
`readUB t` says whether the discriminant read itself is undefined behaviour; otherwise the read
returns `t` and the switch dispatches on it. -/
def exec (readUB payloadOK : Nat → Bool) (sw : Switch) (t : Nat) : Outcome :=
  if readUB t then .ub else runArm payloadOK t (sw.target t)

/-- Outcome refinement: the target outcome `tgt` refines the source outcome `src` if the source
is undefined behaviour or the two are equal. -/
def Refines (tgt src : Outcome) : Prop :=
  src = .ub ∨ tgt = src

/-- The allowed-tag test used by the specialization: tag `t` is one of the `n` variant tags and
the allowed-set predicate `A` holds of it. -/
def allowedTag (n : Nat) (A : Nat → Bool) (t : Nat) : Bool :=
  decide (t < n) && A t

/-- Shape 1 of the specialization: every explicit arm whose value is not an allowed tag is
retargeted to `unreachable`. -/
def pruneArms (n : Nat) (A : Nat → Bool) (sw : Switch) : Switch :=
  { sw with arms := sw.arms.map fun a => if allowedTag n A a.1 then a else (a.1, .unreachable) }

/-- The allowed tags that have no explicit arm, in increasing order. -/
def remainingAllowed (n : Nat) (A : Nat → Bool) (sw : Switch) : List Nat :=
  (List.range n).filter fun i => A i && !(sw.arms.any fun a => a.1 == i)

/-- Shape 2 of the specialization (wildcard narrowing when at most one allowed tag lacks an
explicit arm; named after its one-remaining case, "the last remaining variant takes the wildcard
target"). Two branches change the switch: if zero allowed tags lack an explicit arm, the wildcard
becomes `unreachable`; if exactly one allowed tag `j` lacks an explicit arm, an arm `j ↦ otherwise`
is appended and the wildcard becomes `unreachable`. If two or more allowed tags lack an explicit
arm, nothing changes. -/
def lastVariantTakesWildcard (n : Nat) (A : Nat → Bool) (sw : Switch) : Switch :=
  match remainingAllowed n A sw with
  | [] => { sw with otherwise := .unreachable }
  | [j] => { arms := sw.arms ++ [(j, sw.otherwise)], otherwise := .unreachable }
  | _ :: _ :: _ => sw

/-- The full specialization: shape 1, then shape 2 (shape 1 keeps every arm value, so the
remaining allowed tags are computed from the original arm values). -/
def specializeSwitch (n : Nat) (A : Nat → Bool) (sw : Switch) : Switch :=
  lastVariantTakesWildcard n A (pruneArms n A sw)

/-- A toy enum: the list of variants, each `true` (inhabited) or `false` (uninhabited).
Variant `i` has tag `i`; tags `t ≥ length` denote no variant (invalid tags). -/
abbrev Enum := List Bool

/-- Tag `t` denotes an inhabited variant of `E` (false for invalid tags). -/
def Enum.inhabitedTag (E : Enum) (t : Nat) : Bool :=
  E.getD t false

/-- Candidate semantics for a discriminant read of a value whose tag denotes an uninhabited
variant: `rejectUninhabited` (the read is undefined behaviour) or `permissive` (the read
returns the tag; undefined behaviour arises when the payload is used, and not from the read). -/
inductive UninhabitedRead where
  | rejectUninhabited
  | permissive
  deriving DecidableEq, Repr

/-- Choices for a discriminant read of a value whose tag denotes no variant: `rejectInvalid` (the
read is undefined behaviour) or `passThrough` (the read returns the stored value; a switch whose
explicit arms are all variant tags then takes the wildcard). `passThrough` is a modeling boundary of
this package, not a candidate semantics drawn from Rust documentation. -/
inductive InvalidRead where
  | rejectInvalid
  | passThrough
  deriving DecidableEq, Repr

/-- A discriminant-read semantics: one choice for uninhabited-variant tags and one for invalid
tags. -/
structure DiscrSem where
  uninh : UninhabitedRead
  invalid : InvalidRead
  deriving DecidableEq, Repr

/-- Whether reading the discriminant of a value of enum `E` with tag `t` is undefined behaviour
under `D`. -/
def readUB (D : DiscrSem) (E : Enum) (t : Nat) : Bool :=
  if t < E.length then D.uninh == .rejectUninhabited && !E.inhabitedTag t
  else D.invalid == .rejectInvalid

/-- Running a switch on a value of enum `E` with tag `t` under the discriminant semantics `D`;
payload use is defined exactly for inhabited-variant tags. -/
def runSwitch (D : DiscrSem) (E : Enum) (sw : Switch) (t : Nat) : Outcome :=
  exec (readUB D E) E.inhabitedTag sw t

/-- The specialization instantiated as an unreachable-enum-branching pass does it: the allowed
tags are the inhabited variants' tags. -/
def specializeEnum (E : Enum) (sw : Switch) : Switch :=
  specializeSwitch E.length E.inhabitedTag sw

/-- A toy niche encoding (no wrapping): a stored tag value `v` with `v ≥ nicheStart` decodes to
variant index `v - nicheStart + nicheLo` (truncated subtraction, guarded by `v ≥ nicheStart`) if
that index is at most `nicheHi`; every other stored value decodes to the untagged variant.
Degenerate edge: if `nicheLo > nicheHi`, every stored value decodes to the untagged variant. -/
structure NicheEnc where
  untagged : Nat
  nicheLo : Nat
  nicheHi : Nat
  nicheStart : Nat
  deriving DecidableEq, Repr

/-- Decoding a stored tag value with a toy niche encoding (see `NicheEnc`). -/
def NicheEnc.decode (N : NicheEnc) (v : Nat) : Nat :=
  if N.nicheStart ≤ v ∧ v - N.nicheStart + N.nicheLo ≤ N.nicheHi then v - N.nicheStart + N.nicheLo
  else N.untagged

end Toy.DropScope
