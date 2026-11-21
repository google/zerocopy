/-
Bounded `#eval` checks (not part of the `Toy` library; not proofs).

Exhaustive evaluations, in small formats, of the claims proved in general in
`Toy.FloatTier`: the truncation interval theorems, exactness of the range
check, `TwoPowFits`, the folklore guard's exactness by width, congruence of
`primSet` up to `ValEq` and up to NaN collapse, tier soundness, and quiet
outputs. Run with `lake env lean checks/BoundedChecks.lean`; every line should
print `true` (or the listed tables).
-/
import Toy.FloatTier
open Toy.FloatTier

namespace BoundedChecks

def F43 : Fmt := ⟨4, 3, by decide, by decide⟩
def F34 : Fmt := ⟨3, 4, by decide, by decide⟩

def allFP (f : Fmt) : List (FP f) :=
  [.nan, .inf false, .inf true] ++
  ([false, true].flatMap fun s => (List.finRange f.expCount).flatMap fun E =>
    (List.finRange f.fracCount).map fun M => FP.fin s E M)

def allV (f : Fmt) : List (V f) :=
  ([false, true].flatMap fun s => (List.finRange f.payCount).map fun k => V.qnan s k) ++
  ([false, true].flatMap fun s => (List.finRange (f.payCount - 1)).map fun k => V.snan s k) ++
  [.inf false, .inf true] ++
  ([false, true].flatMap fun s => (List.finRange f.expCount).flatMap fun E =>
    (List.finRange f.fracCount).map fun M => V.fin s E M)

-- trunc theorem
def chkTruncU (f : Fmt) : Bool := (allFP f).all fun x => (List.range 8).all fun W =>
  !x.isFinite || (decide (0 ≤ trunc x ∧ trunc x ≤ 2 ^ W - 1) == decide (InOpenU W x))
def chkTruncS (f : Fmt) : Bool := (allFP f).all fun x => (List.range 8).all fun k =>
  !x.isFinite || (decide (-(2 ^ k) ≤ trunc x ∧ trunc x ≤ 2 ^ k - 1) == decide (InOpenS k x))
#eval (chkTruncU F33, chkTruncU F32, chkTruncU F23, chkTruncS F33, chkTruncS F32, chkTruncS F43)

-- range check exact
def chkRange (f : Fmt) : Bool := (allFP f).all fun x => (List.range 12).all fun W =>
  rangeCheckU (twoPowRound f W) x == (cvtU W x).isSome
#eval (chkRange F33, chkRange F32, chkRange F23, chkRange F43, chkRange F34)
def chkFits (f : Fmt) : List (Nat × Bool × Bool) := (List.range 12).map fun W =>
  (W, decide (TwoPowFits f W), (twoPowRound f W).isFinite)
#eval chkFits F33
-- naive check exactness survey: (W, exact?)
def naiveExact (f : Fmt) : List (Nat × Bool) := (List.range 12).map fun W =>
  (W, (allFP f).all fun x => naiveCheckU W x == (cvtU W x).isSome)
#eval (naiveExact F33, naiveExact F32, naiveExact F34, naiveExact F23)
-- InOpenU / InOpenS are false on NaN and infinities
def chkOpenNonFinite (f : Fmt) : Bool := (allFP f).all fun x => (List.range 8).all fun W =>
  x.isFinite || (!decide (InOpenU W x) && !decide (InOpenS W x))
#eval (chkOpenNonFinite F33, chkOpenNonFinite F32, chkOpenNonFinite F23)
-- saturating conversions: the seven conjuncts at every value
def chkSatU (f : Fmt) : Bool := (allFP f).all fun x => (List.range 8).all fun W =>
  decide (0 ≤ satU W x ∧ satU W x ≤ 2 ^ W - 1) &&
  (match cvtU W x with | some t => satU W x == t | none => true) &&
  (x.isFinite || satU W x == (match x with | .inf false => 2 ^ W - 1 | _ => 0)) &&
  (!decide (x.uval ≤ -((2 : Int) ^ f.qneg)) || satU W x == 0) &&
  (!decide ((2 : Int) ^ W * 2 ^ f.qneg ≤ x.uval) || satU W x == 2 ^ W - 1)
#eval (chkSatU F33, chkSatU F32, chkSatU F23)
-- signed lower-bound guards: strict `x > (-2^k - 1 as float)` and `x >= -2^k`, exactness by k
def signedStrictExact (f : Fmt) : List (Nat × Bool) := (List.range 8).map fun k =>
  (k, (allFP f).all fun x =>
    (lt (round f true ((2 ^ k + 1) * 2 ^ f.qneg) 0) x && lt x (twoPowRound f k)) == (cvtS k x).isSome)
def signedGeExact (f : Fmt) : List (Nat × Bool) := (List.range 8).map fun k =>
  (k, (allFP f).all fun x =>
    (le (round f true (2 ^ k * 2 ^ f.qneg) 0) x && lt x (twoPowRound f k)) == (cvtS k x).isSome)
#eval (signedStrictExact F33, signedGeExact F33)
#eval (naiveCheckU 3 (twoPowRound F32 3), cvtU 3 (twoPowRound F32 3), trunc (twoPowRound F32 3), roundNat F32 7 == twoPowRound F32 3)

-- trunc examples in F33: 3.5 = 56 units (qneg = 4)
#eval (F33.qneg, F33.maxUnits, F32.qneg, F32.maxUnits, F23.qneg, F23.maxUnits, F23.payCount)

-- primSet congruence under ValEq (exhaustive on F23)
def sset (X : Extra f) (p : Prim) (x y : V f) (all : List (V f)) : List (V f) :=
  all.filter fun r => decide (primSet X p x y r)
def chkCongr (f : Fmt) (X : Extra f) : Bool :=
  let all := allV f
  [Prim.add, .sub, .mul, .min, .max].all fun p =>
  all.all fun x1 => all.all fun y1 =>
  let s1 := sset X p x1 y1 all
  (all.filter fun x2 => decide (ValEq x1 x2)).all fun x2 =>
  (all.filter fun y2 => decide (ValEq y1 y2)).all fun y2 =>
  let s2 := sset X p x2 y2 all
  s1.all fun r1 => s2.all fun r2 => decide (ValEq r1 r2)
#eval chkCongr F23 noExtra
#eval chkCongr F23 (fun _ _ _ => true)
-- nonempty sets & tier soundness
def chkSound (f : Fmt) (X : Extra f) (τ : Tier f) : Bool :=
  let all := allV f
  [Prim.add, .sub, .mul, .min, .max].all fun p => all.all fun x => all.all fun y =>
    decide (primSet X p x y (τ p x y))
#eval (chkSound F23 noExtra tierCtfe, chkSound F23 noExtra tierRunA, chkSound F33 noExtra tierRunA)
-- no snan output when no snan input
def chkQuiet (f : Fmt) : Bool :=
  let all := allV f
  [Prim.add, .sub, .mul, .min, .max].all fun p => all.all fun x => all.all fun y =>
   (sset noExtra p x y all).all fun r => !(r.isNaN && !r.isQuiet) || (x.isNaN && !x.isQuiet) || (y.isNaN && !y.isQuiet)
#eval chkQuiet F23
-- NaN-collapse congruence for arithmetic (for min/max-free determinism)
def chkCongrNaN (f : Fmt) : Bool :=
  let all := allV f
  [Prim.add, .sub, .mul].all fun p =>
  all.all fun x1 => all.all fun y1 =>
  let s1 := sset noExtra p x1 y1 all
  (all.filter fun x2 => x1.toFP == x2.toFP).all fun x2 =>
  (all.filter fun y2 => y1.toFP == y2.toFP).all fun y2 =>
  let s2 := sset noExtra p x2 y2 all
  s1.all fun r1 => s2.all fun r2 => r1.toFP == r2.toFP
#eval chkCongrNaN F23
#eval ((sset noExtra .min (V.zero F23 false) (V.zero F23 true) (allV F23)).length)

end BoundedChecks
