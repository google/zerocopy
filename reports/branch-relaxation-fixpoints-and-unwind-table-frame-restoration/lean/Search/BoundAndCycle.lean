import ToyRelax.Relax.Model
open Toy.Relax

def instrs : List Instr :=
  [.fixed 1, .fixed 2, .fixed 3, .align 2, .align 4]

def asgOfList (l : List Bool) : Asg := fun i => l.getD i false
def mat (n : Nat) (a : Asg) : Asg := asgOfList ((List.range n).map a)

def allAsgs : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (allAsgs n).flatMap (fun l => [l ++ [false], l ++ [true]])

def le (n : Nat) (a b : Asg) : Bool := (List.range n).all (fun i => !a i || b i)
def eqA (n : Nat) (a b : Asg) : Bool := (List.range n).all (fun i => a i == b i)

/-- All programs of exactly `n` instructions over `instrs` and
`branch t` for every target `t ≤ N` (index `N` is the end of the program). -/
def progsUpTo (N : Nat) : Nat → List Prog
  | 0 => [[]]
  | n+1 => (progsUpTo N n).flatMap (fun p =>
      (instrs ++ ((List.range (N+1)).map Instr.branch)).map (fun i => p ++ [i]))

/-- All programs of exactly `n` instructions; every branch may target any
index `0 … n`. -/
def progs (n : Nat) : List Prog := progsUpTo n n

def stepL (prm : Params) (p : Prog) (l : List Bool) : List Bool :=
  (List.range p.length).map (step prm p (asgOfList l))
def gsL (prm : Params) (p : Prog) (l : List Bool) : List Bool :=
  (List.range p.length).map (stepGS prm p (asgOfList l))
def iterL (f : List Bool → List Bool) : Nat → List Bool → List Bool
  | 0, l => l
  | k+1, l => iterL f k (f l)
def fastRelaxL (prm : Params) (p : Prog) (a : Asg) : List Bool :=
  iterL (stepL prm p) (numBranches p) ((List.range p.length).map a)
def fastRelax (prm : Params) (p : Prog) (a : Asg) : Asg := asgOfList (fastRelaxL prm p a)

def leastFail (prm : Params) (p : Prog) : Option (List Bool) :=
  let r := fastRelax prm p allShort
  (allAsgs p.length).find? (fun l =>
    let b := asgOfList l
    decide (Valid prm p b) && !(le p.length r b))

def optFail (prm : Params) (p : Prog) : Option (List Bool) :=
  let r := fastRelax prm p allShort
  (allAsgs p.length).find? (fun l =>
    let b := asgOfList l
    decide (Valid prm p b) && decide (totalSize prm p b < totalSize prm p r))

-- grow-and-shrink from allShort: does it differ from grow-only at some iterate ≤ 2^n+2?
def gsTrace (prm : Params) (p : Prog) (k : Nat) : List (List Bool) :=
  let n := p.length
  let rec go : Nat → List Bool → List (List Bool)
    | 0, _ => []
    | m+1, l => l :: go m (gsL prm p l)
  go k ((List.range n).map allShort)

def oscillates (prm : Params) (p : Prog) : Bool :=
  let tr := gsTrace prm p 12
  let last := tr.getLast!
  let prev := tr.getD (tr.length - 2) []
  last != prev

def paramsList : List Params :=
  [⟨1,2,1⟩, ⟨1,2,2⟩, ⟨1,2,3⟩, ⟨1,3,2⟩, ⟨1,3,3⟩, ⟨2,4,3⟩, ⟨2,4,4⟩, ⟨1,4,4⟩, ⟨2,3,2⟩, ⟨2,3,3⟩]

def searchWith (n : Nat) (f : Params → Prog → Option (List Bool)) : List (Params × Prog × List Bool) :=
  (progs n).flatMap fun p =>
    if numBranches p = 0 then [] else
    paramsList.filterMap fun prm =>
      (f prm p).map fun l => (prm, p, l)

def searchOsc (n : Nat) : List (Params × Prog) :=
  (progs n).flatMap fun p =>
    if numBranches p = 0 then [] else
    paramsList.filterMap fun prm => if oscillates prm p then some (prm, p) else none

-- passes needed by grow-only from allShort (number of steps with change)
def passes (prm : Params) (p : Prog) : Nat :=
  let rec go : Nat → List Bool → Nat
    | 0, _ => 0
    | m+1, l => let l' := stepL prm p l; if l' == l then 0 else 1 + go m l'
  go 10 ((List.range p.length).map allShort)
def searchTight (n : Nat) : List (Params × Prog) :=
  (progs n).flatMap fun p =>
    if numBranches p < 2 then [] else
    if (p.any Instr.isAlign) then [] else
    paramsList.filterMap fun prm => if passes prm p = numBranches p then some (prm, p) else none
#eval (searchTight 3).take 3
#eval (searchTight 4).take 3
#eval gsTrace ⟨1,2,2⟩ [.fixed 1, .branch 3, .branch 0] 1
def gsFrom (prm : Params) (p : Prog) (l : List Bool) (k : Nat) : List (List Bool) :=
  let rec go : Nat → List Bool → List (List Bool)
    | 0, _ => []
    | m+1, l => l :: go m (gsL prm p l)
  go k l
#eval gsFrom ⟨1,2,2⟩ [.fixed 1, .branch 3, .branch 0] [false, true, false] 5
#eval (searchOsc 4).take 4
