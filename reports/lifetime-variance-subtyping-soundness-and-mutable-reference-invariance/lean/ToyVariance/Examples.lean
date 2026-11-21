import ToyVariance.Basic
import ToyVariance.Alg
import ToyVariance.Lang
import ToyVariance.Programs

/-!
# Positive and negative examples for every definition
-/

namespace Toy.Variance

/-! ## Lifetimes -/

theorem Lft.live_till_example : (Lft.till 3).live 3 = true := rfl
theorem Lft.not_live_till_example : (Lft.till 3).live 4 = false := rfl

theorem Lft.static_outlives_till : Lft.static.outlives (.till 3) = true := rfl
theorem Lft.till_not_outlives_static : (Lft.till 3).outlives .static = false := rfl
theorem Lft.till_not_outlives_longer : (Lft.till 3).outlives (.till 4) = false := rfl

/-- Adequacy: `outlives` is exactly "live whenever the other is live". -/
theorem Lft.outlives_iff_live_imp (a b : Lft) :
    a.outlives b = true ↔ ∀ t, b.live t = true → a.live t = true := by
  cases a with
  | static => simp [Lft.outlives, Lft.live]
  | till n =>
    cases b with
    | static =>
      simp only [Lft.outlives, Lft.live, Bool.false_eq_true, forall_const, false_iff]
      intro h
      have := h (n + 1)
      simp at this
      omega
    | till m =>
      simp only [Lft.outlives, Lft.live, decide_eq_true_eq]
      constructor
      · intro h t ht; omega
      · intro h; exact h m (Nat.le_refl m)

/-! ## Variances -/

theorem Variance.inv_le_co : Variance.inv.le .co = true := rfl
theorem Variance.co_le_bi : Variance.co.le .bi = true := rfl
theorem Variance.co_not_le_contra : Variance.co.le .contra = false := rfl
theorem Variance.bi_not_le_co : Variance.bi.le .co = false := rfl

theorem Variance.meet_co_contra : Variance.co.meet .contra = .inv := rfl
theorem Variance.meet_co_co_ne_inv : Variance.co.meet .co ≠ .inv := by decide

theorem Variance.comp_contra_contra : Variance.contra.comp .contra = .co := rfl
theorem Variance.comp_inv_bi : Variance.inv.comp .bi = .bi := rfl
theorem Variance.comp_contra_co_ne_co : Variance.contra.comp .co ≠ .co := by decide

theorem Variance.rel_inv_example : Variance.Rel .inv (fun a b : Nat => a = b) 1 1 :=
  ⟨fun _ => rfl, fun _ => rfl⟩
theorem Variance.not_rel_co_example : ¬ Variance.Rel .co (fun a b : Nat => a < b) 2 1 := by
  intro h; have := h.1 rfl; omega
theorem Variance.rel_bi_anything : Variance.Rel .bi (fun _ _ : Nat => False) 2 1 :=
  ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

theorem LRel.co_static_sh : LRel .co .static sh :=
  ⟨fun _ => rfl, fun h => Bool.noConfusion h⟩
theorem LRel.not_co_sh_static : ¬ LRel .co sh .static := by
  intro h; exact Bool.noConfusion (h.1 rfl)

/-! ## Tables -/

theorem rustTable_refMutTy : rustTable .refMutTy = .inv := rfl
theorem rustTable_fnArg_ne_co : rustTable .fnArg ≠ .co := by decide

theorem Table.set_example : (rustTable.set .refMutTy .co) .refMutTy = .co := rfl
theorem Table.set_other_example : (rustTable.set .refMutTy .co) .cell = .inv := rfl

theorem rustTable_le_safeTable : Table.le rustTable safeTable := by
  intro p; cases p <;> rfl
theorem not_safeTable_le_rustTable : ¬ Table.le safeTable rustTable := by
  intro h; exact Bool.noConfusion (h .phantom)

/-! ## Types -/

theorem Ty.subst_example : (Ty.prod .param (.cell .param)).subst .nat = .prod .nat (.cell .nat) := rfl
theorem Ty.subst_closed_example : (Ty.ref .static .nat).subst .unit = .ref .static .nat := rfl

theorem Ty.closed_rs : rs.closed = true := rfl
theorem Ty.not_closed_param : (Ty.ref .static .param).closed = false := rfl

theorem Ty.allStatic_rs : rs.allStatic = true := rfl
theorem Ty.not_allStatic_rsh : rsh.allStatic = false := rfl

theorem Ty.liveIn_example : rsh.liveIn (Lft.live 0) = true := rfl
theorem Ty.not_liveIn_example : rsh.liveIn (Lft.live 1) = false := rfl

theorem Ty.phantomFree_example : (Ty.fn .param (.cell .param)).phantomFree = true := rfl
theorem Ty.not_phantomFree_example : (Ty.prod .nat (.phantom .param)).phantomFree = false := rfl

/-! ## Generated subtyping -/

theorem subGen_rust_rs_rsh : SubGen rustTable NoAx rs rsh :=
  (subGen_iff_subAlg _ _ _).2 (by decide)

theorem not_subGen_rust_rsh_rs : ¬ SubGen rustTable NoAx rsh rs := by
  rw [subGen_iff_subAlg]; decide

/-- Invariance of `&mut T` in `T` under `rustTable`. -/
theorem not_subGen_rust_refMut_shrink :
    ¬ SubGen rustTable NoAx (.refMut .static rs) (.refMut .static rsh) := by
  rw [subGen_iff_subAlg]; decide

/-- Contravariance of `fn` in its argument under `rustTable`. -/
theorem subGen_rust_fn_contra : SubGen rustTable NoAx (.fn rsh .unit) (.fn rs .unit) :=
  (subGen_iff_subAlg _ _ _).2 (by decide)

theorem not_subGen_rust_fn_co : ¬ SubGen rustTable NoAx (.fn rs .unit) (.fn rsh .unit) := by
  rw [subGen_iff_subAlg]; decide

theorem subAlg_example : subAlg rustTable true (.cell rs) (.cell rs) = true := rfl
theorem subAlg_neg_example : subAlg rustTable true (.cell rs) (.cell rsh) = false := rfl

/-! ## Variance inference -/

theorem inferVar_fn_arg : inferVar rustTable (.fn .param .unit) = .contra := rfl
theorem inferVar_struct_example :
    inferVar rustTable (.prod (.ref sh .param) (.prod (.cell .param) .unit)) = .inv := rfl
theorem inferVar_phantom : inferVar rustTable (.phantom .param) = .co := rfl
theorem inferVar_unused : inferVar rustTable (.prod .nat (.refMut .static .nat)) = .bi := rfl
theorem inferVar_fn_fn : inferVar rustTable (.fn (.fn .param .unit) .unit) = .co := rfl
theorem inferVar_refMut_ne_co : inferVar rustTable (.refMut .static .param) ≠ .co := by decide

/-- The variance composition `Variance::xform` of rustc (`compiler/rustc_type_ir/src/lib.rs`,
"Figure 1" of Altidor, Huang and Smaragdakis, PLDI 2011), transcribed: an outer `inv` gives
`inv` and an outer `bi` gives `bi`, whatever the inner variance. -/
def Variance.xform : Variance → Variance → Variance
  | .co, w => w
  | .contra, .co => .contra
  | .contra, .contra => .co
  | .contra, .inv => .inv
  | .contra, .bi => .bi
  | .inv, _ => .inv
  | .bi, _ => .bi

/-- `comp` and `xform` agree whenever the inner variance is not `bi`. -/
theorem Variance.comp_eq_xform_of_ne_bi (v w : Variance) (hw : w ≠ .bi) : v.comp w = v.xform w := by
  cases v <;> cases w <;> first | rfl | exact absurd rfl hw

/-- `inferVar` with `xform` in place of `comp` (bottom-up over the whole body). -/
def inferVarXform (tbl : Table) : Ty → Variance
  | .unit => .bi
  | .nat => .bi
  | .ref _ T => (tbl .refTy).xform (inferVarXform tbl T)
  | .refMut _ T => (tbl .refMutTy).xform (inferVarXform tbl T)
  | .cell T => (tbl .cell).xform (inferVarXform tbl T)
  | .fn T U => ((tbl .fnArg).xform (inferVarXform tbl T)).meet ((tbl .fnRes).xform (inferVarXform tbl U))
  | .prod T U => ((tbl .prodL).xform (inferVarXform tbl T)).meet ((tbl .prodR).xform (inferVarXform tbl U))
  | .phantom T => (tbl .phantom).xform (inferVarXform tbl T)
  | .param => .co

/-- The two recursions differ on a parameter-free subterm under an invariant constructor:
for `(Cell<()>, T)`, `inferVar` gives `co` and `inferVarXform` gives `inv`. -/
theorem inferVar_vs_inferVarXform :
    inferVar rustTable (.prod (.cell .unit) .param) = .co ∧
      inferVarXform rustTable (.prod (.cell .unit) .param) = .inv :=
  ⟨rfl, rfl⟩

theorem bodyAx_example : BodyAx (.prod .param .unit) .co (.prod rs .unit) (.prod rsh .unit) :=
  ⟨rs, rsh, rfl, rfl, rfl, rfl, fun _ => subGen_rust_rs_rsh, fun h => Bool.noConfusion h⟩

theorem not_bodyAx_example : ¬ BodyAx (.cell .param) .inv (.cell rs) (.cell rsh) := by
  rintro ⟨A, B, _, _, hA, hB, hrel⟩
  simp only [Ty.subst, Ty.cell.injEq] at hA hB
  subst hA; subst hB
  exact not_subGen_rust_rsh_rs (hrel.2 rfl)

theorem Ty.dataBody_example :
    (Ty.prod (.ref sh (.cell .param)) (.prod (.refMut .static .param) .unit)).dataBody = true := rfl
theorem Ty.not_dataBody_bare_cell : (Ty.prod (.cell .param) .unit).dataBody = false := rfl
theorem Ty.not_dataBody_refMut_cell : (Ty.refMut .static (.cell .param)).dataBody = false := rfl
theorem Ty.not_dataBody_fn : (Ty.fn (.fn .param .unit) .unit).dataBody = false := rfl
theorem Ty.not_dataBody_phantom : (Ty.phantom .param).dataBody = false := rfl

/-! ## Programs, typing, safety -/

/-- A small safe program: read a `'static` reference before and after ending `'sh`. -/
def progOk : List Stmt :=
  prelude ++ [.read 6 2, .read 7 5, .endRegion 0, .read 8 2]

theorem progOk_typed : Typed (SubGen rustTable NoAx) progOk :=
  typed_of_checks 20 (by decide)

theorem progOk_safe : Safe progOk := by
  intro fuel
  rcases fuel with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | fuel <;> rfl

/-- Reading the short reference after its region ended is rejected for every oracle. -/
def progUseAfterEnd : List Stmt :=
  prelude ++ [.endRegion 0, .read 6 5]

theorem progUseAfterEnd_not_typed (R : Ty → Ty → Prop) : ¬ Typed R progUseAfterEnd := by
  rintro ⟨sub, _, fuel, h⟩
  rcases fuel with _ | _ | _ | _ | _ | _ | _ | _ | _ | fuel <;>
    simp [Checks, chk, progUseAfterEnd, prelude, Mode.get, Mode.lv, Ctx.set,
      Ty.liveIn, Lft.live] at h

theorem progUseAfterEnd_not_safe : ¬ Safe progUseAfterEnd := by
  intro h; have := h 20; revert this; decide

/-- A program whose only copy uses the proper coercion `&'static nat ≤ &'sh nat`. -/
def progCoerceShrink : List Stmt :=
  prelude ++ [.copy 6 2 rsh, .read 7 6, .endRegion 0, .read 8 2]

theorem progCoerceShrink_typed : Typed (SubGen rustTable NoAx) progCoerceShrink :=
  typed_of_checks 20 (by decide)

/-- Bare `Cell` values: the contents of `c : &'static Cell<nat>` are copied out by `read` at type
`Cell<nat>`, paired, projected, boxed with `alloc`, and overwritten through `&mut`. -/
def progBareCellAccess : List Stmt :=
  [.nat 0 42, .newCell 1 .static 0, .read 2 1, .unit 3, .pair 4 2 3, .fst 5 4,
   .alloc 6 .static 5, .write 6 2]

theorem progBareCellAccess_typed_and_not_stuck :
    Typed (SubGen rustTable NoAx) progBareCellAccess ∧
      (exec 20 St.init Env.empty progBareCellAccess).isStuck = false :=
  ⟨typed_of_checks 20 (by decide), by decide⟩

/-- Positive example of `AdmitsDanglingAccess`: with `&mut` covariant in `T`, `progRefMutCo`. -/
theorem admitsDanglingAccess_example :
    AdmitsDanglingAccess (SubGen (rustTable.set .refMutTy .co) NoAx) :=
  ⟨progRefMutCo, typed_of_checks 40 (by decide), 40, by decide⟩

end Toy.Variance
