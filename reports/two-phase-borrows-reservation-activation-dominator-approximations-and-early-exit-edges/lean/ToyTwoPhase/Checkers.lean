import ToyTwoPhase.Semantics

/-!
# Toy borrow checkers, the forward may-analysis, and the repairs

Every checker flags (1) every `writeX` under a live loan, (2) every read of `x` (`readX`,
`borrowShared`) under a live loan that its phase test calls active, and (3) the activation `A`
if some shared reference is live there (the activation check of RFC 2025). The checkers share
everything except the phase test: `MaybeActive` (the exact-phase checker; a walk-defined specification),
`dfMaybeActive` (the iterative dataflow checker; the result of a fixed number of iterations of a
forward may-analysis), or `IsActiveDom` (the dominator checker).
-/

namespace Toy.TwoPhase

variable {n : Nat}

/-- `Flagged p phase L`: the checker with phase test `phase` reports an error at node `L`. -/
def Flagged (p : Prog n) (phase : Fin n → Prop) (L : Fin n) : Prop :=
  (p.op L = .writeX ∧ LoanLive p L) ∨
  ((p.op L).isRead = true ∧ LoanLive p L ∧ phase L) ∨
  (L = p.A ∧ (SharedLive p .s0 p.A ∨ SharedLive p .s1 p.A))

/-- The checker with phase test `phase` accepts `p`: no node is flagged. -/
def Accepts (p : Prog n) (phase : Fin n → Prop) : Prop :=
  ∀ L : Fin n, ¬ Flagged p phase L

instance (p : Prog n) (phase : Fin n → Prop) [DecidablePred phase] (L : Fin n) :
    Decidable (Flagged p phase L) := by
  unfold Flagged; infer_instance

instance (p : Prog n) (phase : Fin n → Prop) [DecidablePred phase] :
    Decidable (Accepts p phase) := by
  unfold Accepts; infer_instance

/-- The exact-phase checker: phase test `MaybeActive` (the walk-defined meet-over-paths phase
fact; not an iterative computation). -/
def ExactPhaseAccepts (p : Prog n) : Prop := Accepts p (MaybeActive p)

/-- The dominator checker: phase test `IsActiveDom` (rustc's shape). -/
def DominatorAccepts (p : Prog n) : Prop := Accepts p (IsActiveDom p)

/-- The checker without two-phase borrows: every loan counts as active everywhere. -/
def AlwaysActiveAccepts (p : Prog n) : Prop := Accepts p (fun _ => True)

instance (p : Prog n) : Decidable (ExactPhaseAccepts p) := by
  unfold ExactPhaseAccepts; infer_instance
instance (p : Prog n) : Decidable (DominatorAccepts p) := by unfold DominatorAccepts; infer_instance
instance (p : Prog n) : Decidable (AlwaysActiveAccepts p) := by
  unfold AlwaysActiveAccepts; infer_instance

/-! ## The forward may-analysis -/

/-- Out-fact of node `P` given its in-fact: generate at `A`, kill at `R` and `endLoan`. -/
def dfOut (p : Prog n) (P : Fin n) (inFact : Bool) : Bool :=
  match p.op P with
  | .activate => true
  | .reserve | .endLoan => false
  | _ => inFact

/-- One iteration of the analysis: the in-fact at `L` is the disjunction of the out-facts of its
predecessors (along all edges); the entry has no other incoming fact. The set of nodes whose
in-fact is `true` is represented as a sublist of `List.finRange n`. -/
def dfStep (p : Prog n) (S : List (Fin n)) : List (Fin n) :=
  (List.finRange n).filter fun L =>
    (List.finRange n).any fun P => (p.edges P).contains L && dfOut p P (S.contains P)

/-- `k` iterations from the bottom element (all facts `false`). -/
def dfIter (p : Prog n) : Nat → List (Fin n)
  | 0 => []
  | k + 1 => dfStep p (dfIter p k)

/-- The analysis result after `n` iterations (the in-fact at `L`). That `n` iterations reach the
least fixpoint is part of what R1a proves. -/
def dfMaybeActive (p : Prog n) (L : Fin n) : Bool := (dfIter p n).contains L

/-- The iterative dataflow checker: phase test `dfMaybeActive`. -/
def IterDataflowAccepts (p : Prog n) : Prop := Accepts p (fun L => dfMaybeActive p L = true)

instance (p : Prog n) : Decidable (IterDataflowAccepts p) := by
  unfold IterDataflowAccepts; infer_instance

/-! ## Repairs -/

/-- The decidable CFG precondition under which the dominator test is proved sound (R2b):
`ReentryFree`, `ActivationStaysReachable`, and no unwinding edges. -/
def DomGuard (p : Prog n) : Prop := ReentryFree p ∧ ActivationStaysReachable p ∧ NoUnwind p

instance (p : Prog n) : Decidable (DomGuard p) := by unfold DomGuard; infer_instance

/-- Repair (b): the dominator test when `DomGuard` holds; otherwise every loan counts as
active. -/
def guardedDomPhase (p : Prog n) (L : Fin n) : Prop :=
  if DomGuard p then IsActiveDom p L else True

instance (p : Prog n) : DecidablePred (guardedDomPhase p) := by
  intro L; unfold guardedDomPhase; infer_instance

def RepairBAccepts (p : Prog n) : Prop := Accepts p (guardedDomPhase p)

/-- Repair (c): reject every program violating `DomGuard` (a node other than `R` reached from `R`
without `A` from which `A` is unreachable without `R`, re-entry into `A` without `R`, unwinding
edges);
otherwise the dominator checker. -/
def RepairCAccepts (p : Prog n) : Prop := DomGuard p ∧ DominatorAccepts p

/-- The literal form of repair (b): guarded by `A` post-dominating `R` (normal edges) alone. -/
def literalPdomPhase (p : Prog n) (L : Fin n) : Prop :=
  if PDom p.succ p.A p.R then IsActiveDom p L else True

instance (p : Prog n) : DecidablePred (literalPdomPhase p) := by
  intro L; unfold literalPdomPhase; infer_instance

def LiteralRepairBAccepts (p : Prog n) : Prop := Accepts p (literalPdomPhase p)

instance (p : Prog n) : Decidable (RepairBAccepts p) := by unfold RepairBAccepts; infer_instance
instance (p : Prog n) : Decidable (RepairCAccepts p) := by unfold RepairCAccepts; infer_instance
instance (p : Prog n) : Decidable (LiteralRepairBAccepts p) := by
  unfold LiteralRepairBAccepts; infer_instance

end Toy.TwoPhase
