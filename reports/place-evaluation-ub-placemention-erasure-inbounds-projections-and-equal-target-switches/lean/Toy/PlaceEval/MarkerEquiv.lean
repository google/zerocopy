import Toy.PlaceEval.MarkerRev
import Toy.PlaceEval.ConstProv

/-!
# Storage-marker erasure is an equivalence (fresh addresses, no address observation, UB-free)

The forward direction is the forward simulation with a large address shift `D` (a multiple of
every positive alignment occurring in the program and larger than every address of a pointer
constant of the program): with that shift every non-zero-size access through a pointer
constant fails in the source. The reverse direction places the source's allocation of `x` at
`X0` and every other source allocation at the target's address shifted by `D`.
-/

namespace Toy.PlaceEval

/-! ## Alignments and constant addresses occurring in a program -/

def Operand.aligns : Operand → List Nat
  | .copy _ τ => [τ.align]
  | .const _ => []

def Rvalue.aligns : Rvalue → List Nat
  | .use o => o.aligns
  | .rawRef _ => []
  | .ref _ L => [L.align]
  | .ptrEq a b => a.aligns ++ b.aligns
  | .addrOf a => a.aligns

def Stmt.aligns : Stmt → List Nat
  | .assign _ τ rv => τ.align :: rv.aligns
  | .emit rv => rv.aligns
  | _ => []

def Term.aligns : Term → List Nat
  | .switchInt o _ _ => o.aligns
  | _ => []

/-- Every alignment occurring in `P`, together with `ptrAlign`. -/
def Prog.aligns (P : Prog) : List Nat :=
  ptrAlign :: (P.locals.map (·.align) ++
    P.blocks.flatMap fun b => b.stmts.flatMap Stmt.aligns ++ b.term.aligns)

def Operand.caddrs : Operand → List Nat
  | .const (.ptr q) => [q.addr]
  | _ => []

def Rvalue.caddrs : Rvalue → List Nat
  | .use o => o.caddrs
  | .ptrEq a b => a.caddrs ++ b.caddrs
  | .addrOf a => a.caddrs
  | _ => []

def Stmt.caddrs : Stmt → List Nat
  | .assign _ _ rv => rv.caddrs
  | .emit rv => rv.caddrs
  | _ => []

def Term.caddrs : Term → List Nat
  | .switchInt o _ _ => o.caddrs
  | _ => []

/-- The addresses of the pointer constants of `P`. -/
def Prog.caddrs (P : Prog) : List Nat :=
  P.blocks.flatMap fun b => b.stmts.flatMap Stmt.caddrs ++ b.term.caddrs

/-- The product of the alignments, with `0` counted as `1`. -/
def posProd : List Nat → Nat
  | [] => 1
  | a :: l => max a 1 * posProd l

theorem posProd_pos : ∀ l : List Nat, 0 < posProd l
  | [] => Nat.one_pos
  | a :: l => Nat.mul_pos (by omega) (posProd_pos l)

theorem dvd_posProd : ∀ {l : List Nat} {a : Nat}, a ∈ l → 0 < a → a ∣ posProd l
  | b :: l, a, h, ha => by
    simp only [posProd]
    rcases List.mem_cons.1 h with rfl | h'
    · rw [Nat.max_eq_left ha]; exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (dvd_posProd h' ha) (Nat.dvd_mul_left _ _)

/-- The bound on constant addresses. -/
def Prog.cbound (P : Prog) : Nat := P.caddrs.foldr max 0

/-- The shift used for the equivalence. -/
def Prog.shiftD (P : Prog) (x : Local) : Nat :=
  (P.cbound + 1 + (P.layout x).align * (P.cbound + 1) + (P.layout x).size) * posProd P.aligns

section Conds

variable {P : Prog}

theorem mem_aligns_of_stmt {b : Block} (hb : b ∈ P.blocks) {s : Stmt} (hs : s ∈ b.stmts) {a : Nat}
    (ha : a ∈ s.aligns) : a ∈ P.aligns := by
  simp only [Prog.aligns, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr (Or.inr ⟨b, hb, Or.inl ⟨s, hs, ha⟩⟩)

theorem mem_aligns_of_term {b : Block} (hb : b ∈ P.blocks) {a : Nat} (ha : a ∈ b.term.aligns) :
    a ∈ P.aligns := by
  simp only [Prog.aligns, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_map]
  exact Or.inr (Or.inr ⟨b, hb, Or.inr ha⟩)

theorem le_cbound_of_stmt {b : Block} (hb : b ∈ P.blocks) {s : Stmt} (hs : s ∈ b.stmts) {a : Nat}
    (ha : a ∈ s.caddrs) : a ≤ P.cbound :=
  le_foldr_max (by
    simp only [Prog.caddrs, List.mem_flatMap, List.mem_append]
    exact ⟨b, hb, Or.inl ⟨s, hs, ha⟩⟩)

theorem le_cbound_of_term {b : Block} (hb : b ∈ P.blocks) {a : Nat} (ha : a ∈ b.term.caddrs) :
    a ≤ P.cbound :=
  le_foldr_max (by
    simp only [Prog.caddrs, List.mem_flatMap, List.mem_append]
    exact ⟨b, hb, Or.inr ha⟩)

theorem alOK_of_mem {D : Nat} (hD : posProd P.aligns ∣ D) {a : Nat} (ha : a ∈ P.aligns) :
    AlOK D a := fun hpos => Nat.dvd_trans (dvd_posProd ha hpos) hD

theorem opOK_of {D A : Nat} {o : Operand} (hal : ∀ a ∈ o.aligns, AlOK D a)
    (hc : ∀ c ∈ o.caddrs, c ≤ A) : OpOK D (JA A) o := by
  cases o with
  | copy p τ => exact hal _ (by simp [Operand.aligns])
  | const v =>
    cases v with
    | int _ => trivial
    | ptr q => exact Or.inr (hc _ (by simp [Operand.caddrs]))

theorem opOK2_of {A : Nat} {o : Operand} (hc : ∀ c ∈ o.caddrs, c ≤ A) : OpOK2 (JA A) o := by
  cases o with
  | copy p τ => trivial
  | const v =>
    cases v with
    | int _ => trivial
    | ptr q => exact Or.inr (hc _ (by simp [Operand.caddrs]))

theorem rvOK_of {D A : Nat} {rv : Rvalue} (hal : ∀ a ∈ rv.aligns, AlOK D a)
    (hc : ∀ c ∈ rv.caddrs, c ≤ A) (hobs : rv.observesAddr = false) : RvOK D (JA A) rv := by
  cases rv with
  | use o => exact opOK_of hal hc
  | rawRef _ => trivial
  | ref _ L => exact hal _ (by simp [Rvalue.aligns])
  | ptrEq _ _ => simp [Rvalue.observesAddr] at hobs
  | addrOf _ => simp [Rvalue.observesAddr] at hobs

theorem rvOK2_of {A : Nat} {rv : Rvalue} (hc : ∀ c ∈ rv.caddrs, c ≤ A)
    (hobs : rv.observesAddr = false) : RvOK2 (JA A) rv := by
  cases rv with
  | use o => exact opOK2_of hc
  | rawRef _ => trivial
  | ref _ _ => trivial
  | ptrEq _ _ => simp [Rvalue.observesAddr] at hobs
  | addrOf _ => simp [Rvalue.observesAddr] at hobs

theorem progOK_of_noAddrObs {D : Nat} (hobs : NoAddrObs P) (hD : posProd P.aligns ∣ D) :
    ProgOK D (JA P.cbound) P := by
  intro b hb
  refine ⟨fun s hs => ?_, ?_⟩
  · have hal : ∀ a ∈ s.aligns, AlOK D a := fun a ha => alOK_of_mem hD (mem_aligns_of_stmt hb hs ha)
    have hc : ∀ c ∈ s.caddrs, c ≤ P.cbound := fun c hc => le_cbound_of_stmt hb hs hc
    cases s with
    | assign dst τ rv =>
      exact ⟨hal _ (by simp [Stmt.aligns]),
        rvOK_of (fun a ha => hal a (by simp [Stmt.aligns, ha])) (fun c h => hc c (by simpa [Stmt.caddrs] using h))
          (hobs b hb _ hs rv rfl)⟩
    | emit rv =>
      exact rvOK_of (fun a ha => hal a (by simpa [Stmt.aligns] using ha))
        (fun c h => hc c (by simpa [Stmt.caddrs] using h)) (hobs b hb _ hs rv rfl)
    | _ => trivial
  · cases ht : b.term with
    | switchInt o _ _ =>
      exact opOK_of (fun a ha => alOK_of_mem hD (mem_aligns_of_term hb (by simpa [ht, Term.aligns] using ha)))
        (fun c h => le_cbound_of_term hb (by simpa [ht, Term.caddrs] using h))
    | _ => trivial

theorem progOK2_of_noAddrObs (hobs : NoAddrObs P) : ProgOK2 (JA P.cbound) P := by
  intro b hb
  refine ⟨fun s hs => ?_, ?_⟩
  · have hc : ∀ c ∈ s.caddrs, c ≤ P.cbound := fun c hc => le_cbound_of_stmt hb hs hc
    cases s with
    | assign dst τ rv =>
      exact rvOK2_of (fun c h => hc c (by simpa [Stmt.caddrs] using h)) (hobs b hb _ hs rv rfl)
    | emit rv =>
      exact rvOK2_of (fun c h => hc c (by simpa [Stmt.caddrs] using h)) (hobs b hb _ hs rv rfl)
    | _ => trivial
  · cases ht : b.term with
    | switchInt o _ _ =>
      exact opOK2_of (fun c h => le_cbound_of_term hb (by simpa [ht, Term.caddrs] using h))
    | _ => trivial

theorem layout_align_pos (hwf : ∀ L ∈ P.locals, 1 ≤ L.align) (y : Local) :
    0 < (P.layout y).align := by
  by_cases hy : y < P.locals.length
  · have : P.layout y = P.locals[y] := by
      simp [Prog.layout, List.getD_eq_getElem?_getD, hy]
    rw [this]
    exact hwf _ (List.getElem_mem hy)
  · rw [layout_ge (Nat.le_of_not_lt hy)]; exact Nat.one_pos

theorem layout_align_mem (y : Local) (hy : y < P.locals.length) : (P.layout y).align ∈ P.aligns := by
  have : P.layout y = P.locals[y] := by simp [Prog.layout, List.getD_eq_getElem?_getD, hy]
  rw [this]
  simp only [Prog.aligns, List.mem_cons, List.mem_append, List.mem_map]
  exact Or.inr (Or.inl ⟨_, List.getElem_mem hy, rfl⟩)

theorem layout_align_dvd (hwf : ∀ L ∈ P.locals, 1 ≤ L.align) (x y : Local) :
    (P.layout y).align ∣ P.shiftD x := by
  by_cases hy : y < P.locals.length
  · exact Nat.dvd_trans (dvd_posProd (layout_align_mem y hy) (layout_align_pos hwf y))
      (Nat.dvd_mul_left _ _)
  · rw [layout_ge (Nat.le_of_not_lt hy)]; exact Nat.one_dvd _

end Conds

end Toy.PlaceEval

namespace Toy.PlaceEval

/-- `eraseMarkers_fresh_equivPP_of_alignPos_of_noAddrObs_of_ubFree`, proved by the forward and
reverse simulations with the shift `P.shiftD x`. -/
theorem eraseMarkers_fresh_equivPP_proof (P : Prog) (x : Local)
    (hwf : ∀ L ∈ P.locals, 1 ≤ L.align) (hobs : NoAddrObs P) (hub : UBFree .fresh P) :
    EquivPP .fresh P (eraseMarkers P x) := by
  have hD : posProd P.aligns ∣ P.shiftD x := Nat.dvd_mul_left _ _
  have hS : P.cbound + 1 + (P.layout x).align * (P.cbound + 1) + (P.layout x).size ≤ P.shiftD x :=
    Nat.le_mul_of_pos_right _ (posProd_pos _)
  have hX : P.cbound + 1 ≤ (P.layout x).align * (P.cbound + 1) :=
    Nat.le_mul_of_pos_left _ (layout_align_pos hwf x)
  refine ⟨?_, ?_⟩
  · refine eraseMarkers_refinesPP_shift .fresh P x (P.shiftD x) (JA P.cbound)
      ⟨fun _ => Or.inl rfl, fun p hp => hp.elim Or.inl (fun h => Or.inr (by omega))⟩
      (alOK_of_mem hD (by simp [Prog.aligns]))
      (fun ωt => Or.inr ⟨rfl, ⟨ωt, rfl⟩, fun y =>
        ⟨layout_align_dvd hwf x y, Or.inr (layout_align_pos hwf y)⟩⟩)
      (progOK_of_noAddrObs hobs hD)
  · exact eraseMarkers_rev_refinesPP_param P x (P.shiftD x) ((P.layout x).align * (P.cbound + 1))
      P.cbound (by omega) (by omega) (by omega) rfl (layout_align_pos hwf)
      (layout_align_dvd hwf x) (progOK2_of_noAddrObs hobs) hub

end Toy.PlaceEval
