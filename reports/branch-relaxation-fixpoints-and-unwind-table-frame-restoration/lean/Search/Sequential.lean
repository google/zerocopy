import ToyRelax.Relax.Results2
open Toy.Relax

/-!
Support check (not part of the library target): a sequential (Gauss–Seidel)
grow-only pass, which re-lays out the program after each promotion, can stop
at a different valid assignment than the simultaneous (Jacobi) passes of
`step`/`relax` when an alignment directive is present.
-/

/-- One sequential grow-only pass: visit positions `0, …, p.length - 1` in
order and promote a position if it is out of reach in the layout produced by
the promotions made so far in this pass. -/
def seqPass (prm : Params) (p : Prog) (a : Asg) : Asg :=
  (List.range p.length).foldl (fun a i => if outOfReach prm p a i then promote a i else a) a

/-- `numBranches p` sequential passes from `a`. -/
def seqRelax (prm : Params) (p : Prog) (a : Asg) : Asg :=
  iter (seqPass prm p) (numBranches p) a

def seqProg : Prog := [.branch 3, .branch 3, .align 4]

/-- On `[branch 3, branch 3, align 4]` (short 1, long 2, reach 2) both
procedures end valid; the simultaneous one promotes both branches, the
sequential one only branch 0 (after it, the padding shrinks and branch 1
fits). -/
example :
    Valid alignPrm seqProg (relax alignPrm seqProg allShort) ∧
    Valid alignPrm seqProg (seqRelax alignPrm seqProg allShort) ∧
    relax alignPrm seqProg allShort 0 = true ∧ relax alignPrm seqProg allShort 1 = true ∧
    seqRelax alignPrm seqProg allShort 0 = true ∧ seqRelax alignPrm seqProg allShort 1 = false := by
  decide
