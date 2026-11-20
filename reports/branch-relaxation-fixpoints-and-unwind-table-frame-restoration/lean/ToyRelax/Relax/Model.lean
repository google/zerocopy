/-!
# Toy model of span-dependent branch relaxation

A program is a list of instructions.  Each branch instruction names a target
instruction *index* and is encoded either `short` or `long`.  A short branch
has a bounded reach: the absolute byte distance between the start address of
the branch and the start address of its target must be at most `reach`.  A
long branch reaches everywhere.  Addresses are prefix sums of instruction
sizes, so the reach of every branch depends on the encodings chosen for all
other branches.  Alignment directives pad to the next multiple of their
argument; their size depends on the address they are placed at.

Modeling conventions (fixed for the whole package):
* displacements are measured from the *start* of the branch instruction to the
  *start* of the target instruction;
* an assignment of encodings is a total function `Nat → Bool` (`true` = long);
  the layout reads it only at branch positions, but values at other positions
  are carried along unchanged by the relaxation steps and are compared by the
  order `Asg.Le`;
* relaxation updates all branches simultaneously from one layout (Jacobi
  style), as in a loop that lays out the whole section and then relaxes every
  fragment that does not fit.
-/

namespace Toy.Relax

/-- Encoding parameters of the toy instruction set: the size of a short branch,
the size of a long branch, and the maximal absolute displacement `reach` of a
short branch. -/
structure Params where
  shortSize : Nat
  longSize : Nat
  reach : Nat
deriving Repr, DecidableEq

/-- Toy instructions.  `fixed s` is any instruction of fixed size `s`;
`branch t` is a span-dependent branch to instruction index `t`; `align k`
pads with the minimal number of bytes that makes the next address a multiple
of `k` (`align 0` pads nothing). -/
inductive Instr where
  | fixed (size : Nat)
  | branch (target : Nat)
  | align (k : Nat)
deriving Repr, DecidableEq

/-- Is this instruction a span-dependent branch? -/
def Instr.isBranch : Instr → Bool
  | .branch _ => true
  | _ => false

/-- Is this instruction an alignment directive? -/
def Instr.isAlign : Instr → Bool
  | .align _ => true
  | _ => false

/-- A program: a list of instructions, addressed by list index. -/
abbrev Prog := List Instr

/-- An assignment of encodings to instruction positions: `true` means the
branch at that position is encoded long, `false` short.  Values at
non-branch positions (and at indices `≥ p.length`) do not affect the layout,
but `step`, `stepGS` and `relax` carry them along unchanged and `Asg.Le`
compares them. -/
abbrev Asg := Nat → Bool

/-- The pointwise order `false < true` on assignments, at **every** index
`i : Nat`: every position that is `true` in `a` is `true` in `b`.  This
includes non-branch positions and indices `≥ p.length`, where the value has no
effect on the layout; `Asg.LeOnBranches` is the order restricted to branch
positions. -/
def Asg.Le (a b : Asg) : Prop := ∀ i, a i = true → b i = true

/-- The all-short assignment (the usual starting point of relaxation). -/
def allShort : Asg := fun _ => false

/-- Promote position `j` to long, leaving every other position unchanged. -/
def promote (a : Asg) (j : Nat) : Asg := fun i => if i = j then true else a i

/-- Force position `j` to short, leaving every other position unchanged. -/
def setShort (a : Asg) (j : Nat) : Asg := fun i => if i = j then false else a i

/-- Padding needed to bring address `addr` up to a multiple of `k`. -/
def padTo (k addr : Nat) : Nat := if k = 0 then 0 else (k - addr % k) % k

/-- Size of an instruction placed at address `base`, with encoding bit `long`
(only relevant for branches). -/
def instrSize (prm : Params) (base : Nat) (long : Bool) : Instr → Nat
  | .fixed s => s
  | .branch _ => if long then prm.longSize else prm.shortSize
  | .align k => padTo k base

/-- Start address of instruction index `k` under assignment `a`: the sum of the
sizes of instructions `0, …, k-1`.  For `k ≥ p.length` this is the end address
of the program. -/
def addr (prm : Params) (p : Prog) (a : Asg) : Nat → Nat
  | 0 => 0
  | k + 1 =>
    let b := addr prm p a k
    b + (match p[k]? with
         | some ins => instrSize prm b (a k) ins
         | none => 0)

/-- Size of instruction index `k` under assignment `a` (0 past the end). -/
def size (prm : Params) (p : Prog) (a : Asg) (k : Nat) : Nat :=
  match p[k]? with
  | some ins => instrSize prm (addr prm p a k) (a k) ins
  | none => 0

theorem addr_succ (prm : Params) (p : Prog) (a : Asg) (k : Nat) :
    addr prm p a (k + 1) = addr prm p a k + size prm p a k := rfl

/-- Absolute displacement between the start of instruction `i` (the branch) and
the start of instruction `t` (its target). -/
def dist (prm : Params) (p : Prog) (a : Asg) (i t : Nat) : Nat :=
  if i ≤ t then addr prm p a t - addr prm p a i else addr prm p a i - addr prm p a t

/-- Position `i` holds a branch that is currently short and whose target is out
of short reach under the layout of `a`. -/
def outOfReach (prm : Params) (p : Prog) (a : Asg) (i : Nat) : Bool :=
  match p[i]? with
  | some (.branch t) => !a i && decide (prm.reach < dist prm p a i t)
  | _ => false

/-- An assignment is *valid* if every short branch reaches its target. -/
def Valid (prm : Params) (p : Prog) (a : Asg) : Prop :=
  ∀ i, i < p.length → outOfReach prm p a i = false

instance (prm : Params) (p : Prog) (a : Asg) : Decidable (Valid prm p a) :=
  inferInstanceAs (Decidable (∀ i, i < p.length → outOfReach prm p a i = false))

/-- One *grow-only* relaxation step: promote every short branch that is out of
reach under the current layout; never demote. -/
def step (prm : Params) (p : Prog) (a : Asg) : Asg :=
  fun i => a i || outOfReach prm p a i

/-- Number of branch instructions in the program. -/
def numBranches (p : Prog) : Nat := p.countP Instr.isBranch

/-- `iter f n a` applies `f` to `a` exactly `n` times. -/
def iter (f : Asg → Asg) : Nat → Asg → Asg
  | 0, a => a
  | n + 1, a => iter f n (f a)

/-- The grow-only relaxation result from start `a`: `numBranches p` iterations
of `step` (Kleene iteration). -/
def relax (prm : Params) (p : Prog) (a : Asg) : Asg :=
  iter (step prm p) (numBranches p) a

/-- Does a relaxation pass over `a` change anything? -/
def changed (prm : Params) (p : Prog) (a : Asg) : Bool :=
  (List.range p.length).any (outOfReach prm p a)

/-- The relaxation loop as an assembler runs it, with an explicit bound on the
number of passes: each pass lays out the program, stops with `some a` if no
branch needs promotion, and otherwise promotes and repeats.  `none` means the
pass budget ran out. -/
def relaxLoop (prm : Params) (p : Prog) : Nat → Asg → Option Asg
  | 0, _ => none
  | n + 1, a => if changed prm p a then relaxLoop prm p n (step prm p a) else some a

/-- One *grow-and-shrink* step: every branch `i` is re-decided from the
*counterfactual* layout `setShort a i`, in which branch `i` itself is
tentatively short and every other position is as in `a`; it becomes long
exactly when that short encoding would be out of reach, and short otherwise.
This is not the same as reading the distance from the current layout `a`:
under the start-of-instruction convention a forward long branch's own size
lies in its span (see `stepGS_decides_from_counterfactual_layout` and the
contrast definition `stepGSCurrent`).  Long branches may be demoted. -/
def stepGS (prm : Params) (p : Prog) (a : Asg) : Asg :=
  fun i => match p[i]? with
    | some (.branch t) => decide (prm.reach < dist prm p (setShort a i) i t)
    | _ => a i

/-- Contrast definition, not used by any main result: a grow-and-shrink step
that reads every branch's distance from the *current* layout `a` itself (so a
long forward branch counts its own long size in its span) instead of from the
counterfactual layout `setShort a i` used by `stepGS`.  The two steps differ
(`alignOsc_counterfactual_vs_current`), and on the aligned instance of
Result 3c this variant stops at a valid fixpoint
(`alignOsc_stepGSCurrent_reaches_valid_fixpoint`). -/
def stepGSCurrent (prm : Params) (p : Prog) (a : Asg) : Asg :=
  fun i => match p[i]? with
    | some (.branch t) => decide (prm.reach < dist prm p a i t)
    | _ => a i

/-- Total size of the program under `a`. -/
def totalSize (prm : Params) (p : Prog) (a : Asg) : Nat := addr prm p a p.length

/-- Distances of branches are monotone in the assignment: making more branches
long never shortens any branch's span.  This is the property under which the
grow-only fixpoint is the least valid assignment. -/
def DistMonotone (prm : Params) (p : Prog) : Prop :=
  ∀ a b, Asg.Le a b → ∀ i t, p[i]? = some (.branch t) → dist prm p a i t ≤ dist prm p b i t

/-- Every instruction size is monotone in the assignment. -/
def SizesMonotone (prm : Params) (p : Prog) : Prop :=
  ∀ a b, Asg.Le a b → ∀ k, size prm p a k ≤ size prm p b k

/-- The program contains no alignment directive. -/
def NoAlign (p : Prog) : Prop := ∀ ins ∈ p, ins.isAlign = false

instance (p : Prog) : Decidable (NoAlign p) :=
  inferInstanceAs (Decidable (∀ ins ∈ p, ins.isAlign = false))

/-- Every instruction inside the program has strictly positive size under every
assignment.  Because `align k` is an instruction whose size is its padding,
this excludes every program in which some assignment places an `align k`
(`k > 1`) at a multiple of `k`; `SizesPositiveAt` is the per-layout form. -/
def AllSizesPositive (prm : Params) (p : Prog) : Prop :=
  ∀ a k, k < p.length → 0 < size prm p a k

/-- Every instruction inside the program has strictly positive size under the
single assignment `c`, so that distinct instruction indices `≤ p.length` have
distinct start addresses in layout `c`. -/
def SizesPositiveAt (prm : Params) (p : Prog) (c : Asg) : Prop :=
  ∀ k, k < p.length → 0 < size prm p c k

instance (prm : Params) (p : Prog) (c : Asg) : Decidable (SizesPositiveAt prm p c) :=
  inferInstanceAs (Decidable (∀ k, k < p.length → 0 < size prm p c k))

/-- The signed displacement between the start of instruction `i` and the start
of instruction `t` under layout `a`.  This is unbounded arithmetic: it does not
check that position `i` holds a branch or that a short branch can encode it
(see `emitDisp`). -/
def disp (prm : Params) (p : Prog) (a : Asg) (i t : Nat) : Int :=
  (addr prm p a t : Int) - (addr prm p a i : Int)

/-- Under layout `a`, a branch at `i` carrying displacement `d` lands at the
start address of instruction index `k`. -/
def JumpsTo (prm : Params) (p : Prog) (a : Asg) (i : Nat) (d : Int) (k : Nat) : Prop :=
  (addr prm p a i : Int) + d = (addr prm p a k : Int)

instance (prm : Params) (p : Prog) (a : Asg) (i : Nat) (d : Int) (k : Nat) :
    Decidable (JumpsTo prm p a i d k) :=
  inferInstanceAs (Decidable ((addr prm p a i : Int) + d = (addr prm p a k : Int)))

/-- The displacement an assembler can actually encode for position `i` under
layout `a`: if `i` holds a branch to `t` that is long, or short and within
reach, its displacement `disp prm p a i t`; otherwise (a short branch out of
reach, or no branch at `i`) `none`. -/
def emitDisp (prm : Params) (p : Prog) (a : Asg) (i : Nat) : Option Int :=
  match p[i]? with
  | some (.branch t) =>
    if a i || decide (dist prm p a i t ≤ prm.reach) then some (disp prm p a i t) else none
  | _ => none

/-- Under layout `c`, the branch at `i` (with target `t`) has an encodable
displacement, and that displacement lands on an instruction index
`k ≤ p.length` exactly when `k = min t p.length` (targets past the end mean the
end of the program). -/
def LandsExactly (prm : Params) (p : Prog) (c : Asg) (i t : Nat) : Prop :=
  ∃ d, emitDisp prm p c i = some d ∧
    ∀ k, k ≤ p.length → (JumpsTo prm p c i d k ↔ k = min t p.length)

/-- Does position `i` hold a branch? -/
def isBranchAt (p : Prog) (i : Nat) : Bool :=
  match p[i]? with
  | some ins => ins.isBranch
  | none => false

/-- The pointwise order restricted to branch positions of `p`: every branch
of `p` that is long in `a` is long in `b`. -/
def Asg.LeOnBranches (p : Prog) (a b : Asg) : Prop :=
  ∀ i, isBranchAt p i = true → a i = true → b i = true

end Toy.Relax
