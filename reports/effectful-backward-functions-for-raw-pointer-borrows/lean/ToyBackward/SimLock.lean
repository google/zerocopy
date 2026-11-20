import ToyBackward.Simulation

/-!
# Simulation lemmas for the borrow-locking translation

Auxiliary definitions and lemmas used only inside the proofs of `lock-complete` and
`lock-success-in-window`: a lockstep relation between the unchecked write-back target (`trun`) and
the borrow-locking target (`lrun`) on placements inside the window, and an invariant of successful
borrow-locking runs from which the four placement conditions are read off.
-/

namespace Toy.Backward.Sim

open Toy.Backward

/-! ## Lockstep relation between `trun` and `lrun` -/

/-- Relation between an unchecked target state `t` and a borrow-locking state `l` at source point
`k`; `O i` says that region `i` has not been ended yet. -/
structure LockRel (P : Prog) (k : Nat) (O : Nat → Prop) (t : TState) (l : LState) : Prop where
  heap : l.heap = t.heap
  vars : l.vars = t.vars
  tslots : ∀ i, (t.slots i).map Prod.fst = refOf P k i
  lopen : ∀ i, O i → l.slots i = t.slots i
  lclosed : ∀ i, ¬ O i → l.slots i = none
  lent : ∀ p, l.lent p = true ↔ ∃ i v, l.slots i = some (p, v)
  uniq : ∀ i j p v w, l.slots i = some (p, v) → l.slots j = some (p, w) → i = j
  count : l.openCount = cnt l.slots P.length

theorem tslot_some {P : Prog} {k : Nat} {t : TState} (htr : ∀ i, (t.slots i).map Prod.fst = refOf P k i)
    {i : Nat} {p : Ptr} {v : Int} (h : t.slots i = some (p, v)) : i < k ∧ regionPtr P i = some p := by
  have := htr i
  rw [h] at this
  exact refOf_some this.symm

theorem tslot_none {P : Prog} {k : Nat} {t : TState} (htr : ∀ i, (t.slots i).map Prod.fst = refOf P k i)
    {i : Nat} (h : refOf P k i = none) : t.slots i = none := by
  have := htr i
  rw [h] at this
  cases hs : t.slots i with
  | none => rfl
  | some _ => rw [hs] at this; cases this

theorem tslot_of_ref {P : Prog} {k : Nat} {t : TState} (htr : ∀ i, (t.slots i).map Prod.fst = refOf P k i)
    {i : Nat} {p : Ptr} (h : refOf P k i = some p) : ∃ v, t.slots i = some (p, v) := by
  have := htr i
  rw [h] at this
  cases hs : t.slots i with
  | none => rw [hs] at this; cases this
  | some pv =>
    rw [hs] at this
    obtain ⟨q, v⟩ := pv
    simp only [Option.map_some, Option.some.injEq] at this
    subst this
    exact ⟨v, rfl⟩

theorem LockRel.lslot_some {P k O t l} (hR : LockRel P k O t l) {i p v}
    (h : l.slots i = some (p, v)) : O i ∧ t.slots i = some (p, v) := by
  by_cases hO : O i
  · exact ⟨hO, (hR.lopen i hO).symm.trans h⟩
  · rw [hR.lclosed i hO] at h; cases h

theorem LockRel.lslot_none {P k O t l} (hR : LockRel P k O t l) {i} (h : t.slots i = none) :
    l.slots i = none := by
  by_cases hO : O i
  · rw [hR.lopen i hO, h]
  · exact hR.lclosed i hO

theorem LockRel.congr {P k O O' t l} (hR : LockRel P k O t l)
    (h : ∀ i, (t.slots i).isSome = true → (O i ↔ O' i)) : LockRel P k O' t l where
  heap := hR.heap
  vars := hR.vars
  tslots := hR.tslots
  lopen := by
    intro i hO'
    cases hs : t.slots i with
    | none => exact hR.lslot_none hs
    | some pv => rw [← hs]; exact hR.lopen i ((h i (by simp [hs])).2 hO')
  lclosed := by
    intro i hO'
    cases hs : t.slots i with
    | none => exact hR.lslot_none hs
    | some pv => exact hR.lclosed i (fun hO => hO' ((h i (by simp [hs])).1 hO))
  lent := hR.lent
  uniq := hR.uniq
  count := hR.count

theorem lockRel_back {P : Prog} {k : Nat} {O : Nat → Prop} {t : TState} {l : LState} {i : Nat}
    {p : Ptr} {v : Int} (hR : LockRel P k O t l) (hs : t.slots i = some (p, v)) (hO : O i) :
    ∃ t' l', tstep t (.back i) = some t' ∧ lstep l (.back i) = some l' ∧
      LockRel P k (fun j => O j ∧ j ≠ i) t' l' := by
  have hl : l.slots i = some (p, v) := (hR.lopen i hO).trans hs
  have hiN : i < P.length := regionPtr_lt (tslot_some hR.tslots hs).2
  refine ⟨{ t with heap := upd t.heap p v },
    { l with heap := upd l.heap p v, slots := upd l.slots i none, lent := upd l.lent p false,
             openCount := l.openCount - 1 }, by simp [tstep, hs], by simp [lstep, hl], ?_⟩
  refine ⟨by simp [hR.heap], hR.vars, hR.tslots, ?_, ?_, ?_, ?_, ?_⟩
  · intro j ⟨hOj, hji⟩
    show upd l.slots i none j = t.slots j
    rw [upd_ne _ _ hji]; exact hR.lopen j hOj
  · intro j hj
    show upd l.slots i none j = none
    by_cases hji : j = i
    · subst hji; exact upd_same _ _ _
    · rw [upd_ne _ _ hji]; exact hR.lclosed j (fun hOj => hj ⟨hOj, hji⟩)
  · intro q
    show upd l.lent p false q = true ↔ ∃ j w, upd l.slots i none j = some (q, w)
    by_cases hqp : q = p
    · subst hqp
      rw [upd_same]
      simp only [Bool.false_eq_true, false_iff, not_exists]
      intro j w hj
      by_cases hji : j = i
      · subst hji; rw [upd_same] at hj; cases hj
      · rw [upd_ne _ _ hji] at hj
        exact hji (hR.uniq j i q w v hj hl)
    · rw [upd_ne _ _ hqp, hR.lent q]
      constructor
      · rintro ⟨j, w, hj⟩
        have hji : j ≠ i := by
          intro e; subst e; rw [hl] at hj
          simp only [Option.some.injEq, Prod.mk.injEq] at hj
          exact hqp hj.1.symm
        exact ⟨j, w, by rw [upd_ne _ _ hji]; exact hj⟩
      · rintro ⟨j, w, hj⟩
        have hji : j ≠ i := by
          intro e; subst e; rw [upd_same] at hj; cases hj
        rw [upd_ne _ _ hji] at hj
        exact ⟨j, w, hj⟩
  · intro j₁ j₂ q w₁ w₂ h₁ h₂
    change upd l.slots i none j₁ = some (q, w₁) at h₁
    change upd l.slots i none j₂ = some (q, w₂) at h₂
    have h1i : j₁ ≠ i := by intro e; subst e; rw [upd_same] at h₁; cases h₁
    have h2i : j₂ ≠ i := by intro e; subst e; rw [upd_same] at h₂; cases h₂
    rw [upd_ne _ _ h1i] at h₁
    rw [upd_ne _ _ h2i] at h₂
    exact hR.uniq _ _ _ _ _ h₁ h₂
  · show l.openCount - 1 = cnt (upd l.slots i none) P.length
    have := cnt_upd l.slots i none P.length hiN
    rw [hl] at this
    simp only [Option.isSome_some, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at this
    rw [hR.count]
    omega

theorem lockRel_backs {P : Prog} {k : Nat} :
    ∀ (L : List Nat) (O : Nat → Prop) (t : TState) (l : LState), L.Nodup →
      (∀ i ∈ L, O i ∧ (t.slots i).isSome = true) → LockRel P k O t l →
      ∃ t' l', trun (L.map TStmt.back) t = some t' ∧ lrun (L.map TStmt.back) l = some l' ∧
        LockRel P k (fun j => O j ∧ j ∉ L) t' l'
  | [], O, t, l, _, _, hR => ⟨t, l, rfl, rfl, hR.congr (fun j _ => by simp)⟩
  | i :: L, O, t, l, hnd, hL, hR => by
    obtain ⟨hOi, hsi⟩ := hL i (by simp)
    cases hs : t.slots i with
    | none => rw [hs] at hsi; cases hsi
    | some pv =>
      obtain ⟨p, v⟩ := pv
      obtain ⟨t1, l1, ht1, hl1, hR1⟩ := lockRel_back hR hs hOi
      have hnd' := List.nodup_cons.mp hnd
      obtain ⟨t', l', ht', hl', hR'⟩ := lockRel_backs L (fun j => O j ∧ j ≠ i) t1 l1 hnd'.2
        (fun j hj => by
          refine ⟨⟨(hL j (by simp [hj])).1, fun e => hnd'.1 (e ▸ hj)⟩, ?_⟩
          have h1 : t1.slots = t.slots := by
            simp only [tstep, hs, Option.some.injEq] at ht1
            rw [← ht1]
          rw [h1]; exact (hL j (by simp [hj])).2)
        hR1
      refine ⟨t', l', ?_, ?_, hR'.congr (fun j _ => ?_)⟩
      · rw [List.map_cons, trun_cons, ht1]; exact ht'
      · rw [List.map_cons, lrun_cons, hl1]; exact hl'
      · simp only [List.mem_cons, not_or]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

theorem slots_upd_ptr {S : Nat → Option (Ptr × Int)} {r : Nat} {p : Ptr} {v : Int}
    (h : S r = some (p, v)) (v' : Int) (q : Ptr) :
    (∃ i w, upd S r (some (p, v')) i = some (q, w)) ↔ ∃ i w, S i = some (q, w) := by
  constructor
  · rintro ⟨i, w, hi⟩
    by_cases hir : i = r
    · subst hir; rw [upd_same] at hi
      simp only [Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact ⟨i, v, h⟩
    · rw [upd_ne _ _ hir] at hi; exact ⟨i, w, hi⟩
  · rintro ⟨i, w, hi⟩
    by_cases hir : i = r
    · subst hir; rw [h] at hi
      simp only [Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact ⟨i, v', upd_same _ _ _⟩
    · exact ⟨i, w, by rw [upd_ne _ _ hir]; exact hi⟩

theorem slots_upd_uniq {S : Nat → Option (Ptr × Int)} {r : Nat} {p : Ptr} {v : Int}
    (h : S r = some (p, v)) (v' : Int)
    (hu : ∀ i j q w w', S i = some (q, w) → S j = some (q, w') → i = j) :
    ∀ i j q w w', upd S r (some (p, v')) i = some (q, w) →
      upd S r (some (p, v')) j = some (q, w') → i = j := by
  have key : ∀ i q w, upd S r (some (p, v')) i = some (q, w) → ∃ w₀, S i = some (q, w₀) := by
    intro i q w hi
    by_cases hir : i = r
    · subst hir; rw [upd_same] at hi
      simp only [Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact ⟨v, h⟩
    · rw [upd_ne _ _ hir] at hi; exact ⟨w, hi⟩
  intro i j q w w' hi hj
  obtain ⟨a, ha⟩ := key i q w hi
  obtain ⟨b, hb⟩ := key j q w' hj
  exact hu _ _ _ _ _ ha hb

theorem cnt_upd_some_of_some {S : Nat → Option (Ptr × Int)} {r : Nat} {p : Ptr} {v : Int}
    (h : S r = some (p, v)) (b : Ptr × Int) (n : Nat) : cnt (upd S r (some b)) n = cnt S n :=
  cnt_congr n (fun i _ => by
    by_cases hir : i = r
    · subst hir; rw [upd_same, h]; rfl
    · rw [upd_ne _ _ hir])

theorem lockRel_noLent {P : Prog} {π : Placement} (ho : EndsByNextOwnerAccess P π) {k : Nat} {c : Stmt}
    (hk : P[k]? = some c) {t : TState} {l : LState} (hR : LockRel P k (fun j => k < π j) t l) {p : Ptr}
    (hp : c.touchesOwner p = true) : l.lent p = false := by
  cases hl : l.lent p with
  | false => rfl
  | true =>
    obtain ⟨i, v, hi⟩ := (hR.lent p).1 hl
    obtain ⟨hO, hti⟩ := hR.lslot_some hi
    have hO' : k < π i := hO
    obtain ⟨hik, hreg⟩ := tslot_some hR.tslots hti
    have := ho i (regionPtr_lt hreg) k (List.getElem?_eq_some_iff.mp hk).1
      (ownerAccessAfter_of hreg hik hk hp)
    omega

section Lock

variable {P : Prog} {π : Placement}

theorem lockRel_stmt (hc : EndsAfterCreation P π) (hu : EndsAfterLastUse P π)
    (ho : EndsByNextOwnerAccess P π) {k : Nat} {c : Stmt} (hk : P[k]? = some c) {t : TState}
    {l : LState} (hR : LockRel P k (fun j => k < π j) t l) :
    (tstep t (trStmt k c) = none → lstep l (trStmt k c) = none) ∧
    (∀ t', tstep t (trStmt k c) = some t' → ∃ l', lstep l (trStmt k c) = some l' ∧
      LockRel P (k + 1) (fun j => k < π j) t' l') := by
  have hkN : k < P.length := (List.getElem?_eq_some_iff.mp hk).1
  cases c with
  | asMut p =>
    have hrp : regionPtr P k = some p := regionPtr_of_get hk
    have hlent := lockRel_noLent ho hk hR (p := p) (by simp [Stmt.touchesOwner])
    have hno : ∀ i v, l.slots i ≠ some (p, v) := fun i v h => by
      have := (hR.lent p).2 ⟨i, v, h⟩; rw [hlent] at this; cases this
    have htk : t.slots k = none := tslot_none hR.tslots (refOf_self P k)
    have hlk : l.slots k = none := hR.lslot_none htk
    have hπk : k < π k := hc k hkN ((isRegion_iff P k).2 ⟨p, hrp⟩)
    refine ⟨fun h => by simp [trStmt, tstep] at h, ?_⟩
    intro t' ht'
    simp only [trStmt, tstep, Option.some.injEq] at ht'
    subst ht'
    refine ⟨{ l with slots := upd l.slots k (some (p, l.heap p)), lent := upd l.lent p true,
                     openCount := l.openCount + 1 }, by simp [trStmt, lstep, hlent], ?_⟩
    refine ⟨hR.heap, hR.vars, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      show ((upd t.slots k (some (p, t.heap p))) i).map Prod.fst = refOf P (k + 1) i
      rw [refOf_succ_asMut hrp]
      by_cases hik : i = k
      · subst hik; rw [upd_same, upd_same]; rfl
      · rw [upd_ne _ _ hik, upd_ne _ _ hik]; exact hR.tslots i
    · intro i hO
      show upd l.slots k (some (p, l.heap p)) i = upd t.slots k (some (p, t.heap p)) i
      by_cases hik : i = k
      · subst hik; rw [upd_same, upd_same, hR.heap]
      · rw [upd_ne _ _ hik, upd_ne _ _ hik]; exact hR.lopen i hO
    · intro i hO
      show upd l.slots k (some (p, l.heap p)) i = none
      by_cases hik : i = k
      · subst hik; exact absurd hπk hO
      · rw [upd_ne _ _ hik]; exact hR.lclosed i hO
    · intro q
      show upd l.lent p true q = true ↔ ∃ i v, upd l.slots k (some (p, l.heap p)) i = some (q, v)
      by_cases hqp : q = p
      · subst hqp
        rw [upd_same]
        simp only [true_iff]
        exact ⟨k, l.heap q, upd_same _ _ _⟩
      · rw [upd_ne _ _ hqp, hR.lent q]
        constructor
        · rintro ⟨i, v, hi⟩
          have hik : i ≠ k := by intro e; subst e; rw [hlk] at hi; cases hi
          exact ⟨i, v, by rw [upd_ne _ _ hik]; exact hi⟩
        · rintro ⟨i, v, hi⟩
          by_cases hik : i = k
          · subst hik; rw [upd_same] at hi
            simp only [Option.some.injEq, Prod.mk.injEq] at hi
            exact absurd hi.1.symm hqp
          · rw [upd_ne _ _ hik] at hi; exact ⟨i, v, hi⟩
    · intro i j q v w hi hj
      change upd l.slots k (some (p, l.heap p)) i = some (q, v) at hi
      change upd l.slots k (some (p, l.heap p)) j = some (q, w) at hj
      by_cases hik : i = k
      · by_cases hjk : j = k
        · rw [hik, hjk]
        · subst hik; rw [upd_same] at hi; rw [upd_ne _ _ hjk] at hj
          simp only [Option.some.injEq, Prod.mk.injEq] at hi
          rw [← hi.1] at hj; exact absurd hj (hno j w)
      · by_cases hjk : j = k
        · subst hjk; rw [upd_same] at hj; rw [upd_ne _ _ hik] at hi
          simp only [Option.some.injEq, Prod.mk.injEq] at hj
          rw [← hj.1] at hi; exact absurd hi (hno i v)
        · rw [upd_ne _ _ hik] at hi; rw [upd_ne _ _ hjk] at hj
          exact hR.uniq _ _ _ _ _ hi hj
    · show l.openCount + 1 = cnt (upd l.slots k (some (p, l.heap p))) P.length
      have := cnt_upd l.slots k (some (p, l.heap p)) P.length hkN
      rw [hlk] at this
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.isSome_some] at this
      rw [hR.count]; omega
  | read x r =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    have huse : usesAt P k r = true := usesAt_of hk (by simp [Stmt.usesRef])
    constructor
    · intro h
      cases hs : t.slots r with
      | none => simp [trStmt, lstep, hR.lslot_none hs]
      | some pv => obtain ⟨p, v⟩ := pv; simp [trStmt, tstep, hs] at h
    · intro t' ht'
      cases hs : t.slots r with
      | none => simp [trStmt, tstep, hs] at ht'
      | some pv =>
        obtain ⟨p, v⟩ := pv
        simp only [trStmt, tstep, hs, Option.some.injEq] at ht'
        subst ht'
        obtain ⟨hrk', hreg⟩ := tslot_some hR.tslots hs
        have hO : k < π r := hu r (regionPtr_lt hreg) ((isRegion_iff P r).2 ⟨p, hreg⟩) k hkN huse
        have hl : l.slots r = some (p, v) := (hR.lopen r hO).trans hs
        refine ⟨{ l with vars := upd l.vars x v }, by simp [trStmt, lstep, hl], ?_⟩
        refine ⟨hR.heap, by simp [hR.vars], ?_, hR.lopen, hR.lclosed, hR.lent, hR.uniq, hR.count⟩
        intro i; rw [refOf_succ_of_ne hrk]; exact hR.tslots i
  | write r e =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    have huse : usesAt P k r = true := usesAt_of hk (by simp [Stmt.usesRef])
    constructor
    · intro h
      cases hs : t.slots r with
      | none => simp [trStmt, lstep, hR.lslot_none hs]
      | some pv => obtain ⟨p, v⟩ := pv; simp [trStmt, tstep, hs] at h
    · intro t' ht'
      cases hs : t.slots r with
      | none => simp [trStmt, tstep, hs] at ht'
      | some pv =>
        obtain ⟨p, v⟩ := pv
        simp only [trStmt, tstep, hs, Option.some.injEq] at ht'
        subst ht'
        obtain ⟨hrk', hreg⟩ := tslot_some hR.tslots hs
        have hO : k < π r := hu r (regionPtr_lt hreg) ((isRegion_iff P r).2 ⟨p, hreg⟩) k hkN huse
        have hl : l.slots r = some (p, v) := (hR.lopen r hO).trans hs
        refine ⟨{ l with slots := upd l.slots r (some (p, e.eval l.vars)) },
          by simp [trStmt, lstep, hl], ?_⟩
        refine ⟨hR.heap, hR.vars, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i
          show (upd t.slots r (some (p, e.eval t.vars)) i).map Prod.fst = refOf P (k + 1) i
          rw [refOf_succ_of_ne hrk]
          by_cases hir : i = r
          · subst hir; rw [upd_same, ← hR.tslots i, hs]; rfl
          · rw [upd_ne _ _ hir]; exact hR.tslots i
        · intro i hOi
          show upd l.slots r (some (p, e.eval l.vars)) i = upd t.slots r (some (p, e.eval t.vars)) i
          by_cases hir : i = r
          · subst hir; rw [upd_same, upd_same, hR.vars]
          · rw [upd_ne _ _ hir, upd_ne _ _ hir]; exact hR.lopen i hOi
        · intro i hOi
          show upd l.slots r (some (p, e.eval l.vars)) i = none
          by_cases hir : i = r
          · subst hir; exact absurd hO hOi
          · rw [upd_ne _ _ hir]; exact hR.lclosed i hOi
        · intro q
          show l.lent q = true ↔ ∃ i w, upd l.slots r (some (p, e.eval l.vars)) i = some (q, w)
          rw [slots_upd_ptr hl, hR.lent q]
        · exact slots_upd_uniq hl _ hR.uniq
        · show l.openCount = cnt (upd l.slots r (some (p, e.eval l.vars))) P.length
          rw [cnt_upd_some_of_some hl, hR.count]
  | rawRead x p =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    have hlent := lockRel_noLent ho hk hR (p := p) (by simp [Stmt.touchesOwner])
    refine ⟨fun h => by simp [trStmt, tstep] at h, ?_⟩
    intro t' ht'
    simp only [trStmt, tstep, Option.some.injEq] at ht'
    subst ht'
    refine ⟨{ l with vars := upd l.vars x (l.heap p) }, by simp [trStmt, lstep, hlent], ?_⟩
    refine ⟨hR.heap, by simp [hR.vars, hR.heap], ?_, hR.lopen, hR.lclosed, hR.lent, hR.uniq, hR.count⟩
    intro i; rw [refOf_succ_of_ne hrk]; exact hR.tslots i
  | rawWrite p e =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    have hlent := lockRel_noLent ho hk hR (p := p) (by simp [Stmt.touchesOwner])
    refine ⟨fun h => by simp [trStmt, tstep] at h, ?_⟩
    intro t' ht'
    simp only [trStmt, tstep, Option.some.injEq] at ht'
    subst ht'
    refine ⟨{ l with heap := upd l.heap p (e.eval l.vars) }, by simp [trStmt, lstep, hlent], ?_⟩
    refine ⟨by simp [hR.vars, hR.heap], hR.vars, ?_, hR.lopen, hR.lclosed, hR.lent, hR.uniq, hR.count⟩
    intro i; rw [refOf_succ_of_ne hrk]; exact hR.tslots i

theorem lock_main (hc : EndsAfterCreation P π) (hu : EndsAfterLastUse P π)
    (ho : EndsByNextOwnerAccess P π) (he : EndsByProgramEnd P π) :
    ∀ (cs : List Stmt) (k : Nat) (t : TState) (l : LState),
      k + cs.length = P.length → (∀ j, P[k + j]? = cs[j]?) →
      LockRel P k (fun j => k ≤ π j) t l →
      (trun (translateFrom P π k cs ++ backsAt P π P.length) t = none →
        lrun (translateFrom P π k cs ++ backsAt P π P.length) l = none) ∧
      (∀ t', trun (translateFrom P π k cs ++ backsAt P π P.length) t = some t' →
        ∃ l', lrun (translateFrom P π k cs ++ backsAt P π P.length) l = some l' ∧
          l'.heap = t'.heap ∧ l'.vars = t'.vars ∧ l'.openCount = 0)
  | [], k, t, l, hk, _, hR => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    obtain ⟨t1, l1, ht1, hl1, hR1⟩ := lockRel_backs (backsList P π P.length) _ t l
      (backsList_nodup _ _ _)
      (fun i hi => by
        obtain ⟨hiN, hreg, hπ⟩ := mem_backsList.mp hi
        obtain ⟨p, hp⟩ := (isRegion_iff P i).1 hreg
        refine ⟨by show P.length ≤ π i; omega, ?_⟩
        obtain ⟨v, hv⟩ := tslot_of_ref hR.tslots
          (show refOf P P.length i = some p by simp [refOf, hiN, hp])
        simp [hv]) hR
    rw [show translateFrom P π P.length [] = [] from rfl, List.nil_append, backsAt_eq, ht1, hl1]
    refine ⟨fun h => (by cases h), fun t' ht' => ?_⟩
    cases Option.some.inj ht'
    refine ⟨l1, rfl, hR1.heap, hR1.vars, ?_⟩
    rw [hR1.count]
    apply cnt_eq_zero_of
    intro i hi
    cases hs : t1.slots i with
    | none => exact hR1.lslot_none hs
    | some pv =>
      obtain ⟨p, v⟩ := pv
      obtain ⟨_, hreg⟩ := tslot_some hR1.tslots hs
      have hreg' := (isRegion_iff P i).2 ⟨p, hreg⟩
      apply hR1.lclosed
      rintro ⟨h1, h2⟩
      exact h2 (mem_backsList.mpr ⟨hi, hreg', by have := he i hi hreg'; omega⟩)
  | c :: cs, k, t, l, hk, hP, hR => by
    have hck : P[k]? = some c := get_head hP
    obtain ⟨t1, l1, ht1, hl1, hR1⟩ := lockRel_backs (backsList P π k) _ t l (backsList_nodup _ _ _)
      (fun i hi => by
        obtain ⟨hiN, hreg, hπ⟩ := mem_backsList.mp hi
        obtain ⟨p, hp⟩ := (isRegion_iff P i).1 hreg
        have hik : i < k := by have := hc i hiN hreg; omega
        refine ⟨by show k ≤ π i; omega, ?_⟩
        obtain ⟨v, hv⟩ := tslot_of_ref hR.tslots (show refOf P k i = some p by simp [refOf, hik, hp])
        simp [hv]) hR
    have hR1' : LockRel P k (fun j => k < π j) t1 l1 := hR1.congr (fun i hi => by
      cases hs : t1.slots i with
      | none => rw [hs] at hi; cases hi
      | some pv =>
        obtain ⟨p, v⟩ := pv
        obtain ⟨hik, hreg⟩ := tslot_some hR1.tslots hs
        have hreg' : isRegion P i = true := (isRegion_iff P i).2 ⟨p, hreg⟩
        have hiN := regionPtr_lt hreg
        simp only [mem_backsList, not_and]
        constructor
        · rintro ⟨h1, h2⟩
          have : π i ≠ k := fun e => h2 hiN hreg' e
          omega
        · intro h; exact ⟨by omega, fun _ _ e => by omega⟩)
    obtain ⟨hnone, hsome⟩ := lockRel_stmt hc hu ho hck hR1'
    rw [translateFrom_cons, List.append_assoc, trun_append (backsAt P π k),
      lrun_append (backsAt P π k), backsAt_eq, ht1, hl1, List.cons_append]
    simp only [Option.bind, trun_cons, lrun_cons]
    cases hs : tstep t1 (trStmt k c) with
    | none => rw [hnone hs]; exact ⟨fun _ => rfl, fun t' h => by cases h⟩
    | some t2 =>
      obtain ⟨l2, hl2, hR2⟩ := hsome t2 hs
      rw [hl2]
      exact lock_main hc hu ho he cs (k + 1) t2 l2 (by simp at hk; omega) (get_tail hP)
        (hR2.congr (fun _ _ => Iff.rfl))

/-- The borrow-locking translation agrees with the unchecked write-back translation on placements
inside the window. -/
theorem lockSem_eq_effSem (P : Prog) (π : Placement) (h : Heap)
    (hc : EndsAfterCreation P π) (hu : EndsAfterLastUse P π)
    (ho : EndsByNextOwnerAccess P π) (he : EndsByProgramEnd P π) :
    lockSem P π h = effSem P π h := by
  have hR0 : LockRel P 0 (fun j => 0 ≤ π j) (TState.init h) (LState.init h) :=
    ⟨rfl, rfl, fun i => by rw [refOf_zero]; rfl, fun _ _ => rfl,
      fun _ hO => absurd (Nat.zero_le _) hO, fun p => by simp [LState.init],
      fun _ _ _ _ _ h => by simp [LState.init] at h, by simp [LState.init, cnt_none]⟩
  obtain ⟨hn, hs⟩ := lock_main hc hu ho he P 0 (TState.init h) (LState.init h) (by simp)
    (fun j => by simp) hR0
  unfold lockSem effSem translate
  cases ht : trun (translateFrom P π 0 P ++ backsAt P π P.length) (TState.init h) with
  | none => rw [hn ht]; rfl
  | some t' =>
    obtain ⟨l', hl', h1, h2, h3⟩ := hs t' ht
    rw [hl']
    simp [h3, h1, h2, TState.obs]

end Lock

/-! ## An invariant of successful borrow-locking runs -/

theorem isRegion_lt {P : Prog} {i : Nat} (h : isRegion P i = true) : i < P.length := by
  obtain ⟨p, hp⟩ := (isRegion_iff P i).1 h
  exact regionPtr_lt hp

theorem ownerAccessAfter_inv {P : Prog} {i k : Nat} (h : ownerAccessAfter P i k = true) :
    ∃ q c, regionPtr P i = some q ∧ i < k ∧ P[k]? = some c ∧ c.touchesOwner q = true := by
  unfold ownerAccessAfter at h
  split at h
  · rename_i q c hi hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨q, c, regionPtr_of_get hi, h.1, hk, h.2⟩
  · simp at h

theorem isRegion_false_of_get {P : Prog} {k : Nat} {c : Stmt} (hk : P[k]? = some c)
    (hc : ∀ p, c ≠ .asMut p) : isRegion P k = false := by
  cases h : isRegion P k with
  | false => rfl
  | true =>
    obtain ⟨p, hp⟩ := (isRegion_iff P k).1 h
    rw [get_of_regionPtr hp] at hk
    exact absurd (Option.some.inj hk).symm (hc p)

/-- Invariant of a borrow-locking state at source point `k`; `O i` says that the backward call of
region `i` has not run yet. -/
structure LInv (P : Prog) (k : Nat) (O : Nat → Prop) (l : LState) : Prop where
  slots : ∀ i, (l.slots i).isSome = true ↔ (i < k ∧ isRegion P i = true ∧ O i)
  ptr : ∀ i p v, l.slots i = some (p, v) → regionPtr P i = some p
  lent : ∀ p, l.lent p = true ↔ ∃ i v, l.slots i = some (p, v)
  uniq : ∀ i j p v w, l.slots i = some (p, v) → l.slots j = some (p, w) → i = j
  count : l.openCount = cnt l.slots P.length
  fut : ∀ i, isRegion P i = true → k ≤ i → O i

theorem LInv.congr {P k O O' l} (hI : LInv P k O l) (h : ∀ i, isRegion P i = true → (O i ↔ O' i)) :
    LInv P k O' l where
  slots := fun i => by
    rw [hI.slots i]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (h i h2).1 h3⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, (h i h2).2 h3⟩
  ptr := hI.ptr
  lent := hI.lent
  uniq := hI.uniq
  count := hI.count
  fut := fun i hr hk => (h i hr).1 (hI.fut i hr hk)

theorem linv_back {P : Prog} {k : Nat} {O : Nat → Prop} {l l' : LState} {i : Nat}
    (hI : LInv P k O l) (hl : lstep l (.back i) = some l') :
    i < k ∧ O i ∧ LInv P k (fun j => O j ∧ j ≠ i) l' := by
  cases hs : l.slots i with
  | none => simp [lstep, hs] at hl
  | some pv =>
    obtain ⟨p, v⟩ := pv
    simp only [lstep, hs, Option.some.injEq] at hl
    subst hl
    obtain ⟨hik, hreg, hO⟩ := (hI.slots i).1 (by simp [hs])
    have hiN : i < P.length := isRegion_lt hreg
    have hne : ∀ j q w, upd l.slots i none j = some (q, w) → j ≠ i ∧ l.slots j = some (q, w) := by
      intro j q w hj
      have hji : j ≠ i := by intro e; subst e; rw [upd_same] at hj; cases hj
      rw [upd_ne _ _ hji] at hj
      exact ⟨hji, hj⟩
    refine ⟨hik, hO, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      show (upd l.slots i none j).isSome = true ↔ _
      by_cases hji : j = i
      · subst hji; rw [upd_same]; simp
      · rw [upd_ne _ _ hji, hI.slots j]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, h3, hji⟩
        · rintro ⟨h1, h2, h3, _⟩; exact ⟨h1, h2, h3⟩
    · intro j q w hj
      exact hI.ptr j q w (hne j q w hj).2
    · intro q
      show upd l.lent p false q = true ↔ ∃ j w, upd l.slots i none j = some (q, w)
      by_cases hqp : q = p
      · subst hqp
        rw [upd_same]
        simp only [Bool.false_eq_true, false_iff, not_exists]
        intro j w hj
        obtain ⟨hji, hj'⟩ := hne j q w hj
        exact hji (hI.uniq j i q w v hj' hs)
      · rw [upd_ne _ _ hqp, hI.lent q]
        constructor
        · rintro ⟨j, w, hj⟩
          have hji : j ≠ i := by
            intro e; subst e; rw [hs] at hj
            simp only [Option.some.injEq, Prod.mk.injEq] at hj
            exact hqp hj.1.symm
          exact ⟨j, w, by rw [upd_ne _ _ hji]; exact hj⟩
        · rintro ⟨j, w, hj⟩
          exact ⟨j, w, (hne j q w hj).2⟩
    · intro j₁ j₂ q w₁ w₂ h₁ h₂
      exact hI.uniq _ _ _ _ _ (hne _ _ _ h₁).2 (hne _ _ _ h₂).2
    · show l.openCount - 1 = cnt (upd l.slots i none) P.length
      have := cnt_upd l.slots i none P.length hiN
      rw [hs] at this
      simp only [Option.isSome_some, ↓reduceIte, Option.isSome_none, Bool.false_eq_true] at this
      rw [hI.count]
      omega
    · intro j hr hkj
      exact ⟨hI.fut j hr hkj, by omega⟩

theorem linv_backs {P : Prog} {k : Nat} :
    ∀ (L : List Nat) (O : Nat → Prop) (l l' : LState), L.Nodup → LInv P k O l →
      lrun (L.map TStmt.back) l = some l' →
      (∀ i ∈ L, i < k) ∧ LInv P k (fun j => O j ∧ j ∉ L) l'
  | [], O, l, l', _, hI, hl => by
    cases Option.some.inj hl
    exact ⟨fun _ h => (by cases h), hI.congr (fun j _ => by simp)⟩
  | i :: L, O, l, l', hnd, hI, hl => by
    rw [List.map_cons, lrun_cons] at hl
    cases hs : lstep l (.back i) with
    | none => rw [hs] at hl; cases hl
    | some l1 =>
      rw [hs] at hl
      obtain ⟨hik, _, hI1⟩ := linv_back hI hs
      obtain ⟨hL, hI'⟩ := linv_backs L _ l1 l' (List.nodup_cons.mp hnd).2 hI1 hl
      refine ⟨fun j hj => ?_, hI'.congr (fun j _ => ?_)⟩
      · simp only [List.mem_cons] at hj
        rcases hj with rfl | hj
        · exact hik
        · exact hL j hj
      · simp only [List.mem_cons, not_or]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

section LockSucc

variable {P : Prog} {π : Placement}

theorem linv_noOwner {k : Nat} {c : Stmt} (hk : P[k]? = some c) {l : LState}
    (hI : LInv P k (fun j => k < π j) l)
    (hc : ∀ p, c.touchesOwner p = true → l.lent p = false) :
    ∀ i, ownerAccessAfter P i k = true → π i ≤ k := by
  intro i h
  obtain ⟨q, c', hreg, hik, hk', hq⟩ := ownerAccessAfter_inv h
  rw [hk] at hk'
  cases Option.some.inj hk'
  apply Nat.le_of_not_lt
  intro hlt
  have hsome := (hI.slots i).2 ⟨hik, (isRegion_iff P i).2 ⟨q, hreg⟩, hlt⟩
  cases hs : l.slots i with
  | none => rw [hs] at hsome; cases hsome
  | some pv =>
    obtain ⟨q', v⟩ := pv
    have hq' := hI.ptr i q' v hs
    rw [hreg] at hq'
    cases Option.some.inj hq'
    have := (hI.lent q).2 ⟨i, v, hs⟩
    rw [hc q hq] at this
    cases this

theorem linv_same {k : Nat} {c : Stmt} (hk : P[k]? = some c) (hc : ∀ p, c ≠ .asMut p)
    {l l' : LState} (hI : LInv P k (fun j => k < π j) l)
    (hptr : ∀ j p, (∃ v, l'.slots j = some (p, v)) ↔ (∃ v, l.slots j = some (p, v)))
    (hlent : l'.lent = l.lent) (hcnt : l'.openCount = l.openCount) :
    LInv P (k + 1) (fun j => k < π j) l' := by
  have hsome : ∀ j, (l'.slots j).isSome = (l.slots j).isSome := by
    intro j
    cases h1 : l'.slots j with
    | none =>
      cases h2 : l.slots j with
      | none => rfl
      | some pv =>
        obtain ⟨p, v⟩ := pv
        obtain ⟨w, hw⟩ := (hptr j p).2 ⟨v, h2⟩
        rw [h1] at hw; cases hw
    | some pv =>
      obtain ⟨p, v⟩ := pv
      obtain ⟨w, hw⟩ := (hptr j p).1 ⟨v, h1⟩
      rw [hw]; rfl
  have hrk := isRegion_false_of_get hk hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hsome j, hI.slots j]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h2, h3⟩
      have : j ≠ k := by intro e; subst e; rw [hrk] at h2; cases h2
      omega
  · intro j p v h
    obtain ⟨w, hw⟩ := (hptr j p).1 ⟨v, h⟩
    exact hI.ptr j p w hw
  · intro q
    rw [hlent, hI.lent q]
    constructor
    · rintro ⟨j, v, h⟩
      obtain ⟨w, hw⟩ := (hptr j q).2 ⟨v, h⟩
      exact ⟨j, w, hw⟩
    · rintro ⟨j, v, h⟩
      obtain ⟨w, hw⟩ := (hptr j q).1 ⟨v, h⟩
      exact ⟨j, w, hw⟩
  · intro i j p v w hi hj
    obtain ⟨a, ha⟩ := (hptr i p).1 ⟨v, hi⟩
    obtain ⟨b, hb⟩ := (hptr j p).1 ⟨w, hj⟩
    exact hI.uniq _ _ _ _ _ ha hb
  · rw [hcnt, hI.count]
    exact cnt_congr _ (fun j _ => (hsome j).symm)
  · intro j hr hj
    exact hI.fut j hr (by omega)

theorem linv_stmt {k : Nat} {c : Stmt} (hk : P[k]? = some c) {l l' : LState}
    (hI : LInv P k (fun j => k < π j) l) (hl : lstep l (trStmt k c) = some l') :
    (∀ i, ownerAccessAfter P i k = true → π i ≤ k) ∧ (∀ i, usesAt P k i = true → k < π i) ∧
      LInv P (k + 1) (fun j => k < π j) l' := by
  have hkN : k < P.length := (List.getElem?_eq_some_iff.mp hk).1
  cases c with
  | asMut p =>
    cases hlent : l.lent p with
    | true => simp [trStmt, lstep, hlent] at hl
    | false =>
      simp only [trStmt, lstep, hlent, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hl
      subst hl
      have hrp : regionPtr P k = some p := regionPtr_of_get hk
      have hreg : isRegion P k = true := (isRegion_iff P k).2 ⟨p, hrp⟩
      have hπk : k < π k := hI.fut k hreg (Nat.le_refl _)
      have hlk : l.slots k = none := by
        cases h : l.slots k with
        | none => rfl
        | some _ => have := (hI.slots k).1 (by simp [h]); omega
      have hno : ∀ i v, l.slots i ≠ some (p, v) := fun i v h => by
        have := (hI.lent p).2 ⟨i, v, h⟩; rw [hlent] at this; cases this
      refine ⟨linv_noOwner hk hI (fun q hq => ?_), fun i h => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [Stmt.touchesOwner, beq_iff_eq] at hq
        subst hq; exact hlent
      · unfold usesAt at h; rw [hk] at h; simp [Stmt.usesRef] at h
      · intro i
        show (upd l.slots k (some (p, l.heap p)) i).isSome = true ↔ _
        by_cases hik : i = k
        · subst hik; rw [upd_same]; simp [hreg, hπk]
        · rw [upd_ne _ _ hik, hI.slots i]
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
          · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, h2, h3⟩
      · intro i q v hi
        change upd l.slots k (some (p, l.heap p)) i = some (q, v) at hi
        by_cases hik : i = k
        · subst hik; rw [upd_same] at hi
          simp only [Option.some.injEq, Prod.mk.injEq] at hi
          rw [← hi.1]; exact hrp
        · rw [upd_ne _ _ hik] at hi; exact hI.ptr i q v hi
      · intro q
        show upd l.lent p true q = true ↔ ∃ i v, upd l.slots k (some (p, l.heap p)) i = some (q, v)
        by_cases hqp : q = p
        · subst hqp
          rw [upd_same]
          simp only [true_iff]
          exact ⟨k, l.heap q, upd_same _ _ _⟩
        · rw [upd_ne _ _ hqp, hI.lent q]
          constructor
          · rintro ⟨i, v, hi⟩
            have hik : i ≠ k := by intro e; subst e; rw [hlk] at hi; cases hi
            exact ⟨i, v, by rw [upd_ne _ _ hik]; exact hi⟩
          · rintro ⟨i, v, hi⟩
            by_cases hik : i = k
            · subst hik; rw [upd_same] at hi
              simp only [Option.some.injEq, Prod.mk.injEq] at hi
              exact absurd hi.1.symm hqp
            · rw [upd_ne _ _ hik] at hi; exact ⟨i, v, hi⟩
      · intro i j q v w hi hj
        change upd l.slots k (some (p, l.heap p)) i = some (q, v) at hi
        change upd l.slots k (some (p, l.heap p)) j = some (q, w) at hj
        by_cases hik : i = k
        · by_cases hjk : j = k
          · rw [hik, hjk]
          · subst hik; rw [upd_same] at hi; rw [upd_ne _ _ hjk] at hj
            simp only [Option.some.injEq, Prod.mk.injEq] at hi
            rw [← hi.1] at hj; exact absurd hj (hno j w)
        · by_cases hjk : j = k
          · subst hjk; rw [upd_same] at hj; rw [upd_ne _ _ hik] at hi
            simp only [Option.some.injEq, Prod.mk.injEq] at hj
            rw [← hj.1] at hi; exact absurd hi (hno i v)
          · rw [upd_ne _ _ hik] at hi; rw [upd_ne _ _ hjk] at hj
            exact hI.uniq _ _ _ _ _ hi hj
      · show l.openCount + 1 = cnt (upd l.slots k (some (p, l.heap p))) P.length
        have := cnt_upd l.slots k (some (p, l.heap p)) P.length hkN
        rw [hlk] at this
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Option.isSome_some] at this
        rw [hI.count]; omega
      · intro j hr hj
        exact hI.fut j hr (by omega)
  | read x r =>
    cases hs : l.slots r with
    | none => simp [trStmt, lstep, hs] at hl
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [trStmt, lstep, hs, Option.some.injEq] at hl
      subst hl
      refine ⟨linv_noOwner hk hI (fun q hq => by simp [Stmt.touchesOwner] at hq), fun i h => ?_,
        linv_same hk (by intro p h; cases h) hI (fun j q => Iff.rfl) rfl rfl⟩
      unfold usesAt at h; rw [hk] at h
      simp only [Stmt.usesRef, beq_iff_eq] at h
      subst h
      exact ((hI.slots r).1 (by simp [hs])).2.2
  | write r e =>
    cases hs : l.slots r with
    | none => simp [trStmt, lstep, hs] at hl
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [trStmt, lstep, hs, Option.some.injEq] at hl
      subst hl
      refine ⟨linv_noOwner hk hI (fun q hq => by simp [Stmt.touchesOwner] at hq), fun i h => ?_,
        linv_same hk (by intro p h; cases h) hI (fun j q => ?_) rfl rfl⟩
      · unfold usesAt at h; rw [hk] at h
        simp only [Stmt.usesRef, beq_iff_eq] at h
        subst h
        exact ((hI.slots r).1 (by simp [hs])).2.2
      · show (∃ w, upd l.slots r (some (p, e.eval l.vars)) j = some (q, w)) ↔ _
        by_cases hjr : j = r
        · subst hjr; rw [upd_same, hs]
          simp
        · rw [upd_ne _ _ hjr]
  | rawRead x p =>
    cases hlent : l.lent p with
    | true => simp [trStmt, lstep, hlent] at hl
    | false =>
      simp only [trStmt, lstep, hlent, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hl
      subst hl
      refine ⟨linv_noOwner hk hI (fun q hq => ?_), fun i h => ?_,
        linv_same hk (by intro p h; cases h) hI (fun j q => Iff.rfl) rfl rfl⟩
      · simp only [Stmt.touchesOwner, beq_iff_eq] at hq
        subst hq; exact hlent
      · unfold usesAt at h; rw [hk] at h; simp [Stmt.usesRef] at h
  | rawWrite p e =>
    cases hlent : l.lent p with
    | true => simp [trStmt, lstep, hlent] at hl
    | false =>
      simp only [trStmt, lstep, hlent, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hl
      subst hl
      refine ⟨linv_noOwner hk hI (fun q hq => ?_), fun i h => ?_,
        linv_same hk (by intro p h; cases h) hI (fun j q => Iff.rfl) rfl rfl⟩
      · simp only [Stmt.touchesOwner, beq_iff_eq] at hq
        subst hq; exact hlent
      · unfold usesAt at h; rw [hk] at h; simp [Stmt.usesRef] at h

theorem lock_succ_main :
    ∀ (cs : List Stmt) (k : Nat) (l l' : LState),
      k + cs.length = P.length → (∀ j, P[k + j]? = cs[j]?) →
      LInv P k (fun j => k ≤ π j) l →
      lrun (translateFrom P π k cs ++ backsAt P π P.length) l = some l' → l'.openCount = 0 →
      (∀ i, isRegion P i = true → k ≤ π i → i < π i) ∧
      (∀ i j, k ≤ j → j < P.length → usesAt P j i = true → j < π i) ∧
      (∀ i k', k ≤ k' → k' < P.length → ownerAccessAfter P i k' = true → π i ≤ k') ∧
      (∀ i, i < P.length → isRegion P i = true → π i ≤ P.length)
  | [], k, l, l', hk, _, hI, hl, h0 => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    rw [show translateFrom P π P.length [] = [] from rfl, List.nil_append, backsAt_eq] at hl
    obtain ⟨_, hI'⟩ := linv_backs _ _ l l' (backsList_nodup _ _ _) hI hl
    refine ⟨fun i hr _ => by have := isRegion_lt hr; omega, fun _ _ h1 h2 => by omega,
      fun _ _ h1 h2 => by omega, fun i hi hr => ?_⟩
    apply Nat.le_of_not_lt
    intro hlt
    have hz := cnt_eq_zero (f := l'.slots) P.length (by rw [← hI'.count]; exact h0) i hi
    have hsome := (hI'.slots i).2 ⟨hi, hr, by omega, fun hm => by
      have := (mem_backsList.mp hm).2.2; omega⟩
    rw [hz] at hsome
    cases hsome
  | c :: cs, k, l, l', hk, hP, hI, hl, h0 => by
    have hck : P[k]? = some c := get_head hP
    rw [translateFrom_cons, List.append_assoc, lrun_append (backsAt P π k), backsAt_eq] at hl
    cases hb : lrun ((backsList P π k).map TStmt.back) l with
    | none => rw [hb] at hl; cases hl
    | some l1 =>
      rw [hb] at hl
      simp only [Option.bind, List.cons_append, lrun_cons] at hl
      obtain ⟨hlt, hI1⟩ := linv_backs _ _ l l1 (backsList_nodup _ _ _) hI hb
      have hI1' : LInv P k (fun j => k < π j) l1 := hI1.congr (fun i hr => by
        simp only [mem_backsList, not_and]
        constructor
        · rintro ⟨h1, h2⟩
          have : π i ≠ k := h2 (isRegion_lt hr) hr
          omega
        · intro h; exact ⟨by omega, fun _ _ e => by omega⟩)
      cases hs : lstep l1 (trStmt k c) with
      | none => rw [hs] at hl; cases hl
      | some l2 =>
        rw [hs] at hl
        obtain ⟨hown, huse, hI2⟩ := linv_stmt hck hI1' hs
        obtain ⟨C1, C2, C3, C4⟩ := lock_succ_main cs (k + 1) l2 l' (by simp at hk; omega)
          (get_tail hP) (hI2.congr (fun _ _ => Iff.rfl)) hl h0
        refine ⟨fun i hr hki => ?_, fun i j hkj hj hu => ?_, fun i k' hkk hk' ho => ?_, C4⟩
        · by_cases he : π i = k
          · have := hlt i (mem_backsList.mpr ⟨isRegion_lt hr, hr, he⟩)
            omega
          · exact C1 i hr (by omega)
        · by_cases he : j = k
          · subst he; exact huse i hu
          · exact C2 i j (by omega) hj hu
        · by_cases he : k' = k
          · subst he; exact hown i ho
          · exact C3 i k' (by omega) hk' ho

/-- `lock-success-in-window`, proved: a successful borrow-locking run forces a liveness-respecting
placement. -/
theorem respectsLiveness_of_lockSem (P : Prog) (π : Placement) (h : Heap) (o : Obs)
    (hl : lockSem P π h = some o) : RespectsLiveness P π := by
  unfold lockSem translate at hl
  cases hr : lrun (translateFrom P π 0 P ++ backsAt P π P.length) (LState.init h) with
  | none => rw [hr] at hl; cases hl
  | some s =>
    rw [hr] at hl
    have h0 : s.openCount = 0 := by
      by_cases hz : s.openCount = 0
      · exact hz
      · simp [hz] at hl
    have hI0 : LInv P 0 (fun j => 0 ≤ π j) (LState.init h) :=
      ⟨fun i => by simp [LState.init], fun _ _ _ h => by simp [LState.init] at h,
        fun p => by simp [LState.init], fun _ _ _ _ _ h => by simp [LState.init] at h,
        by simp [LState.init, cnt_none], fun _ _ _ => Nat.zero_le _⟩
    obtain ⟨C1, C2, C3, C4⟩ := lock_succ_main (π := π) P 0 (LState.init h) s (by simp)
      (fun j => by simp) hI0 hr h0
    exact ⟨fun i _ hr => C1 i hr (Nat.zero_le _),
      fun i _ _ j hj hu => C2 i j (Nat.zero_le _) hj hu,
      fun i _ k hk ho => C3 i k (Nat.zero_le _) hk ho,
      fun i hi hr => C4 i hi hr⟩

end LockSucc

end Toy.Backward.Sim
