import ToyLoanFlow
set_option autoImplicit false
namespace Toy.LoanFlow
variable {n m : Nat}

-- explicit rendering of `safe_of_wellTyped_of_nllAccepts`
example : (∀ (p : Prog n m), (∀ q : Fin n, StmtWellTyped p (p.stmt q)) →
    (∀ l q : Fin n, Conflicts p l q → ¬ NLL.InScope .inv p l q) →
    ∀ π : List (Fin n), IsWalk p.succ π → π.head? = some p.entry →
      (run p RState.init π).isUB = false) =
    (∀ (p : Prog n m), WellTyped p → NLLAccepts p → Safe p) := rfl

-- explicit rendering of `safe_of_wellTyped_of_lsAccepts`
example : (∀ (p : Prog n m), (∀ q : Fin n, StmtWellTyped p (p.stmt q)) →
    (∀ l q : Fin n, Conflicts p l q →
      ¬ ∃ (o : Origin m) (q₀ : Fin n),
        LS.Holds .overwrite .inv p l o q₀ ∧ q ∈ p.succ q₀ ∧ LiveAt p o.1 q) →
    ∀ π : List (Fin n), IsWalk p.succ π → π.head? = some p.entry →
      (run p RState.init π).isUB = false) =
    (∀ (p : Prog n m), WellTyped p → LSAccepts p → Safe p) := rfl

-- explicit rendering of `lsAccepts_of_wellTyped_of_nllAccepts`
example : (∀ (vm : VarMode) (p : Prog n m), (∀ q : Fin n, StmtWellTyped p (p.stmt q)) →
    (∀ l q : Fin n, Conflicts p l q → ¬ NLL.InScope vm p l q) →
    ∀ l q : Fin n, Conflicts p l q →
      ¬ ∃ (o : Origin m) (q₀ : Fin n),
        LS.Holds .overwrite vm p l o q₀ ∧ q ∈ p.succ q₀ ∧ LiveAt p o.1 q) =
    (∀ (vm : VarMode) (p : Prog n m), WellTyped p → NLL.Accepts vm p →
      LS.Accepts .overwrite vm p) := rfl

-- explicit rendering of `lsAccepts_overwrite_iff_liveAccepts`
example : (∀ (vm : VarMode) (p : Prog n m),
    (∀ l q : Fin n, Conflicts p l q →
      ¬ ∃ (o : Origin m) (q₀ : Fin n),
        LS.Holds .overwrite vm p l o q₀ ∧ q ∈ p.succ q₀ ∧ LiveAt p o.1 q) ↔
    (∀ l q : Fin n, Conflicts p l q →
      ¬ ∃ (o : Origin m) (q₀ : Fin n),
        LS.LiveHolds vm p l o q₀ ∧ q ∈ p.succ q₀ ∧ LiveAt p o.1 q)) =
    (∀ (vm : VarMode) (p : Prog n m), LS.Accepts .overwrite vm p ↔ LS.LiveAccepts vm p) := rfl

end Toy.LoanFlow
