/-
Bounded evidence by evaluation (not a proof; not part of the `SchedAdequacy` library target).

Run from the package's `lean/` directory after `lake build`:

    lake env lean ../support/BoundedEvidence.lean

Expected output (three `#eval` lines):

    (275, 252, 0, 23, 23, true)
    [(0, 0, false), (1, 1, false), (2, 1, false), (3, 2, true), (4, 1, false), (5, 2, true), (6, 2, true), (7, 3, true)]
    true

Line 1: program shapes with 1 to 5 actions (leaves labelled 0, 1, ... from left to right, so labels are
pairwise distinct); how many contain a parallel composition; how many of those satisfy
"truncating the oracle to its first `schedPoints p - 1` bits never changes the run of `runPerStep`"
(checked over all oracles of length at most `schedPoints p`, which suffices by `perStep_oracleBounded`);
how many shapes have no parallel composition; how many of those satisfy the same check; and whether
all labels are pairwise distinct.

Lines 2-3: for `0 ∥ (1 ∥ 2)` (the shape of `a ∥ (b ∥ c)`), each of the 8 symmetric irreflexive relations
on three labels (bit 0: pair {0,1}, bit 1: pair {0,2}, bit 2: pair {1,2}) with its number of related
pairs and whether every interleaving is reachable by related adjacent swaps from some run of
`runShared` (runs enumerated over all oracles of length at most `schedPoints`, which suffices by
`shared_oracleBounded`); then whether "meets every class" coincides with "at least two pairs related"
on these 8 relations.
-/
import SchedAdequacy
open Toy.SchedAdequacy Prog

/-- All program shapes with `n` leaves, leaves labelled `k, k+1, …` left to right. -/
partial def shapes : Nat → Nat → List (Prog Nat)
  | 1, k => [.act k]
  | n, k => (List.range (n - 1)).flatMap fun i =>
      let l := i + 1
      (shapes l k).flatMap fun p => (shapes (n - l) (k + l)).flatMap fun q => [.seq p q, .par p q]

def boundedAt (p : Prog Nat) (n : Nat) : Bool :=
  (oraclesUpTo (schedPoints p)).all fun o => runPerStep (o.take n) p == runPerStep o p

#eval
  let all := (List.range 5).flatMap fun i => shapes (i + 1) 0
  let withPar := all.filter (·.hasPar)
  let bad := withPar.filter fun p => boundedAt p (schedPoints p - 1)
  let noPar := all.filter (fun p => !p.hasPar)
  let noParBounded := noPar.filter fun p => boundedAt p (schedPoints p - 1)
  (all.length, withPar.length, bad.length, noPar.length, noParBounded.length,
   all.all fun p => p.actions.Nodup)

/-! Relations on `{a, b, c}` = labels 0,1,2: subsets of the pairs {ab, ac, bc}. -/
def related (m : Nat) (x y : Nat) : Bool :=
  let pr := fun i j => (x == i && y == j) || (x == j && y == i)
  (m % 2 == 1 && pr 0 1) || ((m / 2) % 2 == 1 && pr 0 2) || ((m / 4) % 2 == 1 && pr 1 2)

def swaps (m : Nat) (t : List Nat) : List (List Nat) :=
  (List.range (t.length - 1)).filterMap fun i =>
    match t[i]?, t[i+1]? with
    | some x, some y => if related m x y then some (t.take i ++ y :: x :: t.drop (i + 2)) else none
    | _, _ => none

def closure (m : Nat) : Nat → List (List Nat) → List (List Nat)
  | 0, acc => acc
  | f + 1, acc =>
      let nxt := acc ++ (acc.flatMap (swaps m)).filter (fun u => !acc.contains u)
      closure m f nxt.eraseDups

def prog3 : Prog Nat := .par (.act 0) (.par (.act 1) (.act 2))

def meets (m : Nat) : Bool :=
  let runs := (oraclesUpTo (schedPoints prog3)).map fun o => runShared o prog3
  (Interleavings prog3).all fun t => runs.any fun r => (closure m 6 [r]).contains t

def npairs (m : Nat) : Nat := m % 2 + (m / 2) % 2 + (m / 4) % 2

#eval (List.range 8).map fun m => (m, npairs m, meets m)
#eval (List.range 8).all fun m => meets m == decide (npairs m ≥ 2)
