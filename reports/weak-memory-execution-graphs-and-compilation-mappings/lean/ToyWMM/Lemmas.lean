import ToyWMM.Exec

/-!
# Basic lemmas about the derived relations
-/

namespace Toy.WMM

namespace Exec

variable {n : Nat} (X : Exec n)

theorem uniprocRel_of_rf {a b : Fin n} (h : X.rf a b = true) : X.uniprocRel a b = true := by
  simp [uniprocRel, h]

theorem uniprocRel_of_co {a b : Fin n} (h : X.co a b = true) : X.uniprocRel a b = true := by
  simp [uniprocRel, h]

theorem uniprocRel_of_fr {a b : Fin n} (h : X.fr a b = true) : X.uniprocRel a b = true := by
  simp [uniprocRel, h]

theorem fr_iff {a b : Fin n} : X.fr a b = true ↔ ∃ w, X.rf w a = true ∧ X.co w b = true := by
  simp [fr]

theorem sameLoc_symm {a b : Fin n} (h : X.sameLoc a b = true) : X.sameLoc b a = true := by
  simp only [sameLoc, beq_iff_eq] at h ⊢; exact h.symm

theorem sameLoc_trans {a b c : Fin n} (h₁ : X.sameLoc a b = true) (h₂ : X.sameLoc b c = true) :
    X.sameLoc a c = true := by
  simp only [sameLoc, beq_iff_eq] at h₁ h₂ ⊢; exact h₁.trans h₂

theorem sameThread_symm {a b : Fin n} (h : X.sameThread a b = true) :
    X.sameThread b a = true := by
  simp only [sameThread, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at h ⊢
  exact ⟨⟨h.1.2, h.1.1⟩, h.2.symm⟩

/-- Under SC per location, a `po`-total thread orders every same-location, same-thread
`rf`/`co`/`fr` edge between accesses along `po`. -/
theorem po_of_uniproc_edge {a b : Fin n} (hloc : X.PerLocSC) (htot : X.PoTotal)
    (h : X.uniprocRel a b = true) (hsl : X.sameLoc a b = true)
    (ha : (X.ev a).isAccess = true) (hb : (X.ev b).isAccess = true)
    (hst : X.sameThread a b = true) : X.po a b = true := by
  have hne : a ≠ b := by
    rintro rfl
    exact hloc a (Rel.Path.single h)
  rcases htot a b hne hst with h' | h'
  · exact h'
  · exfalso
    have hba : X.uniprocRel b a = true := by
      simp [uniprocRel, poLoc, h', X.sameLoc_symm hsl, ha, hb]
    exact hloc a (Rel.Path.tail (Rel.Path.single h) hba)

/-- A `po` edge between memory accesses is a TSO edge when every `po` write→read pair is
fenced. -/
theorem tsoRel_of_po_of_fenced {a b : Fin n} (h : X.po a b = true)
    (ha : (X.ev a).isAccess = true) (hb : (X.ev b).isAccess = true)
    (hf : (X.ev a).isWrite = true → (X.ev b).isRead = true → X.fenceOrd a b = true) :
    X.tsoRel a b = true := by
  cases hw : (X.ev a).isWrite <;> cases hr : (X.ev b).isRead <;>
    simp_all [tsoRel, ppo]

/-- Every `ppo`, `rfe`, `fence` edge is an SC path, so the SC relation is at least as strong
as the TSO relation (no well-formedness needed). -/
theorem path_scRel_of_tsoRel {a b : Fin n} (h : X.tsoRel a b = true) : Rel.Path X.scRel a b := by
  simp only [tsoRel, Bool.or_eq_true] at h
  rcases h with (((h | h) | h) | h) | h
  · simp only [ppo, Bool.and_eq_true] at h
    exact Rel.Path.single (by simp [scRel, h.1.1.1])
  · simp only [rfe, Bool.and_eq_true] at h
    exact Rel.Path.single (by simp [scRel, h.1])
  · exact Rel.Path.single (by simp [scRel, h])
  · exact Rel.Path.single (by simp [scRel, h])
  · simp only [fenceOrd, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨_, f, h₁, _, h₂⟩ := h
    exact Rel.Path.tail (b := f) (Rel.Path.single (by simp [scRel, h₁])) (by simp [scRel, h₂])

end Exec

end Toy.WMM
