import ToyUnify.Algorithm

/-!
# Positive and negative examples for the core definitions

Every definition of `ToyUnify.Term` and `ToyUnify.Algorithm` is exercised here by at least one
instance it must admit and one it must reject.
-/

namespace Toy.Unify

/-! ## Terms -/

/-- `Term` equality is decided structurally: `Box<u8>` and `Box<u8>` are equal. -/
theorem term_eq_example : box u8 = box u8 := by decide
/-- `Box<u8>` and `Box<u32>` are different terms. -/
theorem term_ne_example : box u8 ≠ box u32 := by decide
/-- A symbol used at two argument counts gives distinct terms (arity mismatch). -/
theorem term_arity_ne_example : (Term.con 4 [u8] : Term) ≠ pair u8 u8 := by decide

/-! ## `Term.vars`, `Term.ctors`, `occurs` -/

theorem vars_example : (pair (.var 0) (box (.var 5))).vars = [0, 5] := by decide
theorem vars_ground_example : (vec u8).vars = [] := by decide
theorem ctors_example : (pair (.var 0) (box u8)).ctors = [4, 2, 0] := by decide
theorem ctors_var_example : (Term.var 3).ctors = [] := by decide
theorem occurs_example : occurs 0 (box (pair u8 (.var 0))) = true := by decide
theorem not_occurs_example : occurs 1 (box (pair u8 (.var 0))) = false := by decide

/-! ## `IsGround`, `VarsDisjoint` -/

theorem isGround_example : IsGround (pair u8 (vec u32)) := by decide
theorem not_isGround_example : ¬ IsGround (vec (.var 0)) := by decide
theorem varsDisjoint_example : VarsDisjoint (pair (.var 0) u8) (vec (.var 1)) := by decide
theorem not_varsDisjoint_example : ¬ VarsDisjoint (pair (.var 0) u8) (vec (.var 0)) := by decide

/-! ## `substVar`, `subst`, `iterSubst` -/

theorem substVar_first_binding_example : substVar [(0, u8), (0, u32)] 0 = u8 := by decide
theorem substVar_unbound_example : substVar [(0, u8)] 1 = .var 1 := by decide
theorem subst_example :
    subst [(0, u8), (1, box (.var 0))] (pair (.var 0) (.var 1)) = pair u8 (box (.var 0)) := by
  decide
theorem subst_ne_example :
    subst [(0, u8)] (pair (.var 0) (.var 1)) ≠ pair (.var 0) (.var 1) := by decide
theorem iterSubst_example :
    iterSubst [(0, box (.var 0))] 3 (.var 0) = box (box (box (.var 0))) := by decide
theorem iterSubst_ne_example :
    iterSubst [(0, box (.var 0))] 2 (.var 0) ≠ box (box (box (.var 0))) := by decide

theorem comp_example :
    subst (Subst.comp [(1, u8)] [(0, box (.var 1))]) (pair (.var 0) (.var 1)) =
      pair (box u8) u8 := by decide
/-- Composition is not commutative: applying `[Y ↦ u8]` first leaves `Box Y` from `X`. -/
theorem comp_order_example :
    subst (Subst.comp [(0, box (.var 1))] [(1, u8)]) (.var 0) ≠ box u8 := by decide

/-! ## `Unifies`, `Unifiable` -/

theorem unifies_example : Unifies [(0, u8)] (pair (.var 0) u8) (pair u8 (.var 0)) := by decide
theorem not_unifies_example : ¬ Unifies [(0, u32)] (pair (.var 0) u8) (pair u8 (.var 0)) := by
  decide

theorem unifiable_example : Unifiable (pair (.var 0) u8) (pair u32 (.var 1)) :=
  ⟨[(0, u32), (1, u8)], by decide⟩

theorem not_unifiable_u8_u32 : ¬ Unifiable u8 u32 := by
  rintro ⟨σ, h⟩
  simp [Unifies, u8, u32, subst_con] at h

/-- A term is never equal to `Box` applied to itself (finite terms). -/
theorem ne_box_self (t : Term) : t ≠ box t := by
  intro h
  have := congrArg sizeOf h
  simp [box] at this
  omega

/-- `X =? Box(X)` has no unifier over finite terms. -/
theorem not_unifiable_var_box : ¬ Unifiable (.var 0) (box (.var 0)) := by
  rintro ⟨σ, h⟩
  have h' : subst σ (.var 0) = box (subst σ (.var 0)) := by
    simpa [Unifies, box, subst_con] using h
  exact ne_box_self _ h'

/-! ## `Idempotent` -/

theorem idempotent_example : Idempotent [(0, pair (.var 1) u8)] := by
  intro t
  refine (subst_comp_of_vars t (fun x _ => ?_)).symm
  by_cases hx : x = 0
  · subst hx; decide
  · simp [substVar_cons, hx, substVar_nil, subst_var]

theorem not_idempotent_example : ¬ Idempotent [(0, box (.var 0))] := by
  intro h
  have := h (.var 0)
  revert this
  decide

/-! ## `MoreGeneral` -/

theorem moreGeneral_example : MoreGeneral [(0, .var 1)] [(0, u8), (1, u8)] := by
  refine ⟨[(1, u8)], fun t => subst_comp_of_vars t (fun x _ => ?_)⟩
  by_cases h0 : x = 0
  · subst h0; decide
  · by_cases h1 : x = 1
    · subst h1; decide
    · simp [substVar_cons, h0, h1, substVar_nil, subst_var]

theorem not_moreGeneral_example : ¬ MoreGeneral [(0, u8)] [(0, .var 1)] := by
  rintro ⟨ρ, h⟩
  have := h (.var 0)
  simp [subst_var, substVar_cons, u8, subst_con] at this

/-! ## `decomp`, `decompAll` -/

theorem decomp_example :
    decomp (pair (.var 0) u8) (pair (box (.var 1)) (.var 2)) = some [(0, box (.var 1)), (2, u8)] := by
  decide
theorem decomp_clash_example : decomp (pair (.var 0) u8) (pair (.var 1) u32) = none := by decide
theorem decomp_arity_clash_example : decomp (Term.con 4 [u8]) (pair u8 u8) = none := by decide
theorem decompAll_example :
    decompAll [(.var 0, .var 0), (box (.var 1), box u8)] = some [(1, u8)] := by decide

/-! ## `run`, `unify`, `unifyNoOC`, `numVars` -/

theorem numVars_example : numVars [(pair (.var 0) (.var 1), pair (.var 1) (.var 0))] = 2 := by
  decide

/-- Repeated variables are counted once. -/
theorem numVars_dedup_example : numVars [(.var 0, pair (.var 0) (.var 0))] = 1 := by decide

theorem unify_example :
    unify (pair (.var 0) u8) (pair u32 (.var 1)) = some [(1, u8), (0, u32)] := by decide
theorem unify_clash_example : unify u8 u32 = none := by decide
theorem unify_occurs_example : unify (.var 0) (box (.var 0)) = none := by decide
theorem unifyNoOC_example :
    unifyNoOC (pair (.var 0) u8) (pair u32 (.var 1)) = some [(1, u8), (0, u32)] := by decide
theorem unifyNoOC_clash_example : unifyNoOC u8 u32 = none := by decide
theorem run_outOfFuel_example : run true 0 [(.var 0, u8)] [] = .outOfFuel := by decide

/-! ## `eqUpTo` -/

theorem eqUpTo_example : eqUpTo 1 (box u8) (box u32) = true := by decide
theorem eqUpTo_ne_example : eqUpTo 2 (box u8) (box u32) = false := by decide
/-- Argument counts are compared at every position of depth `< n`, including the root. -/
theorem eqUpTo_arity_ne_example : eqUpTo 1 (Term.con 4 [u8]) (pair u8 u8) = false := by decide

end Toy.Unify
