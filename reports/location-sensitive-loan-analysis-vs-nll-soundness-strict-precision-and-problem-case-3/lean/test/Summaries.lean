import ToyLoanFlow
open Toy.LoanFlow
instance {m : Nat} : Inhabited (Stmt m) := ⟨.nop⟩
def mk (n m : Nat) (h : 0 < n) (succ : List (List Nat)) (st : List (Stmt m)) (ty : List (List Mutbl)) : Prog n m :=
  ⟨⟨0, h⟩, fun q => (succ[q.val]!).filterMap (fun j => if h : j < n then some ⟨j, h⟩ else none), fun q => st[q.val]!, fun v => ty[v.val]!⟩
def summary {n m : Nat} (p : Prog n m) : String :=
  s!"wt={decide (WellTyped p)} unsafe={unsafeB p} nll={nllAcceptsB .inv p} nllcov={nllAcceptsB .cov p} ls={lsAcceptsB .overwrite .inv p} lsNoKill={lsAcceptsB .none .inv p} lsCopyKill={lsAcceptsB .overwriteAndCopySrc .inv p} lsCov={lsAcceptsB .overwrite .cov p}"
-- CE-A: x c c2 pp t
def ceA : Prog 5 5 := mk 5 5 (by decide) [[1],[2],[3],[4],[]]
  [.borrow .shr 1 0, .borrow .shr 3 1, .borrow .shr 3 2, .access .wr 0, .copy 4 3]
  [[], [.shr], [.shr], [.shr, .shr], [.shr, .shr]]
-- CE-B: x y c d s
def ceB : Prog 6 5 := mk 6 5 (by decide) [[1],[2],[3],[4],[5],[]]
  [.borrow .shr 2 0, .borrow .mut 3 2, .borrow .shr 4 1, .borrow .mut 3 4, .access .wr 0, .deref .rd 4]
  [[], [], [.shr], [.mut, .shr], [.shr]]
-- copy then store through copy: x y c p t s
def ceC : Prog 7 6 := mk 7 6 (by decide) [[1],[2],[3],[4],[5],[6],[]]
  [.borrow .shr 2 0, .borrow .mut 3 2, .copy 4 3, .borrow .shr 5 1, .store 4 5, .access .wr 1, .deref .rd 2]
  [[], [], [.shr], [.mut, .shr], [.mut, .shr], [.shr]]
#eval summary pc3
#eval summary pc3Loop
#eval summary pReassign
#eval summary pCopyThenUse
#eval summary pVariance
#eval summary pUntypedHolder
#eval summary pUntypedStore
#eval summary ceA
#eval summary ceB
#eval summary ceC
