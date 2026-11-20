import ToySemType.Syntax

/-!
# The syntactic type system

`HasType Γ e τ` is a standard simple type system for the safe fragment.
It has **no rule for `cast`** (the unsafe primitive) and **no rule for
`loc`** (references only arise at run time, from `alloc`). Contexts are lists
of types indexed by de Bruijn index.

`HasTypeStore W Γ e τ` extends `HasType` with a store typing (a rule for runtime
references `loc l` with `l < W`); it types intermediate configurations and is
used only by the syntactic-typability value interpretation `SynVal`.
-/

namespace Toy.SemType

open Expr

/-- Syntactic typing of source programs (Curry-style: `lam` is unannotated).
There is deliberately no rule for `cast` and none for runtime references `loc`. -/
inductive HasType : List Ty → Expr → Ty → Prop where
  | var {Γ : List Ty} {i : Nat} {τ : Ty} : Γ[i]? = some τ → HasType Γ (.var i) τ
  | lam {Γ : List Ty} {σ τ : Ty} {b : Expr} :
      HasType (σ :: Γ) b τ → HasType Γ (.lam b) (.arrow σ τ)
  | app {Γ : List Ty} {σ τ : Ty} {f a : Expr} :
      HasType Γ f (.arrow σ τ) → HasType Γ a σ → HasType Γ (.app f a) τ
  | num {Γ : List Ty} {n : Nat} : HasType Γ (.num n) .int
  | lt {Γ : List Ty} {a b : Expr} :
      HasType Γ a .int → HasType Γ b .int → HasType Γ (.lt a b) .int
  | ifz {Γ : List Ty} {τ : Ty} {c t e : Expr} :
      HasType Γ c .int → HasType Γ t τ → HasType Γ e τ → HasType Γ (.ifz c t e) τ
  | size {Γ : List Ty} : HasType Γ .size .int
  | alloc {Γ : List Ty} {a : Expr} : HasType Γ a .int → HasType Γ (.alloc a) .ref
  | read {Γ : List Ty} {a : Expr} : HasType Γ a .ref → HasType Γ (.read a) .int
  | write {Γ : List Ty} {a b : Expr} :
      HasType Γ a .ref → HasType Γ b .int → HasType Γ (.write a b) .int

/-- Syntactically typed expressions do not contain the unsafe primitive. -/
theorem HasType.castFree {Γ : List Ty} {e : Expr} {τ : Ty} (h : HasType Γ e τ) :
    e.castFree = true := by
  induction h <;> simp_all [Expr.castFree]

/-- Syntactically typed expressions are closed relative to their context. -/
theorem HasType.closedAt {Γ : List Ty} {e : Expr} {τ : Ty} (h : HasType Γ e τ) :
    e.closedAt Γ.length = true := by
  induction h with
  | var hi =>
    simp only [Expr.closedAt, decide_eq_true_eq]
    exact (List.getElem?_eq_some_iff.mp hi).1
  | lam _ ih => simpa [Expr.closedAt] using ih
  | _ => simp_all [Expr.closedAt]

/-- An expression containing `cast` has no syntactic type in any context. -/
theorem not_hasType_of_not_castFree {e : Expr} (h : e.castFree = false) (Γ : List Ty) (τ : Ty) :
    ¬ HasType Γ e τ := by
  intro ht
  have := ht.castFree
  simp_all

/-- Syntactic typing of *runtime* terms under a store typing: `HasTypeStore W Γ e τ`
is `HasType` plus one rule typing a runtime reference `loc l` at `ref` when the
address is allocated in world `W` (`l < W`). Since every cell holds a word, the
store typing is just the number `W` of allocated cells. This is the typing
judgment of intermediate configurations used by syntactic (progress and
preservation) soundness proofs for languages with references. There is still
no rule for `cast`. -/
inductive HasTypeStore (W : Nat) : List Ty → Expr → Ty → Prop where
  | var {Γ : List Ty} {i : Nat} {τ : Ty} : Γ[i]? = some τ → HasTypeStore W Γ (.var i) τ
  | lam {Γ : List Ty} {σ τ : Ty} {b : Expr} :
      HasTypeStore W (σ :: Γ) b τ → HasTypeStore W Γ (.lam b) (.arrow σ τ)
  | app {Γ : List Ty} {σ τ : Ty} {f a : Expr} :
      HasTypeStore W Γ f (.arrow σ τ) → HasTypeStore W Γ a σ → HasTypeStore W Γ (.app f a) τ
  | num {Γ : List Ty} {n : Nat} : HasTypeStore W Γ (.num n) .int
  | lt {Γ : List Ty} {a b : Expr} :
      HasTypeStore W Γ a .int → HasTypeStore W Γ b .int → HasTypeStore W Γ (.lt a b) .int
  | ifz {Γ : List Ty} {τ : Ty} {c t e : Expr} :
      HasTypeStore W Γ c .int → HasTypeStore W Γ t τ → HasTypeStore W Γ e τ →
      HasTypeStore W Γ (.ifz c t e) τ
  | size {Γ : List Ty} : HasTypeStore W Γ .size .int
  | alloc {Γ : List Ty} {a : Expr} : HasTypeStore W Γ a .int → HasTypeStore W Γ (.alloc a) .ref
  | read {Γ : List Ty} {a : Expr} : HasTypeStore W Γ a .ref → HasTypeStore W Γ (.read a) .int
  | write {Γ : List Ty} {a b : Expr} :
      HasTypeStore W Γ a .ref → HasTypeStore W Γ b .int → HasTypeStore W Γ (.write a b) .int
  | loc {Γ : List Ty} {l : Nat} : l < W → HasTypeStore W Γ (.loc l) .ref

/-- Store-typed expressions do not contain the unsafe primitive either. -/
theorem HasTypeStore.castFree {W : Nat} {Γ : List Ty} {e : Expr} {τ : Ty}
    (h : HasTypeStore W Γ e τ) : e.castFree = true := by
  induction h <;> simp_all [Expr.castFree]

/-- Every source typing derivation is a store-typing derivation in every world. -/
theorem HasType.toStore {Γ : List Ty} {e : Expr} {τ : Ty} (h : HasType Γ e τ) (W : Nat) :
    HasTypeStore W Γ e τ := by
  induction h with
  | var hi => exact .var hi
  | lam _ ih => exact .lam ih
  | app _ _ ihf iha => exact .app ihf iha
  | num => exact .num
  | lt _ _ iha ihb => exact .lt iha ihb
  | ifz _ _ _ ihc iht ihe => exact .ifz ihc iht ihe
  | size => exact .size
  | alloc _ ih => exact .alloc ih
  | read _ ih => exact .read ih
  | write _ _ iha ihb => exact .write iha ihb

end Toy.SemType
