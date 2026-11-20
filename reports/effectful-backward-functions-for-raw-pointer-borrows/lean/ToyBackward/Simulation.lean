import ToyBackward.Liveness

/-!
# Simulation lemmas

Auxiliary definitions and lemmas used only inside the proofs of the main results: run
decomposition, the source-indexed structure of `translate`, reference tables, a finite count of
bound slots, and the simulation invariant relating the heap semantics to the unchecked write-back
translation (`effSem`), which proves `endpoint-window-last-write`. The borrow-locking translation
and the prophecy encoding are treated in `ToyBackward/SimLock.lean` and `ToyBackward/SimProph.lean`.
-/

namespace Toy.Backward.Sim

open Toy.Backward

/-! ## Point updates -/

theorem upd_same {α : Type} (f : Nat → α) (k : Nat) (v : α) : upd f k v k = v := by
  simp [upd]

theorem upd_ne {α : Type} (f : Nat → α) {k j : Nat} (v : α) (h : j ≠ k) : upd f k v j = f j := by
  simp [upd, h]

/-! ## Runs of concatenated programs -/

theorem trun_append (A B : List TStmt) (t : TState) :
    trun (A ++ B) t = (trun A t).bind (trun B) := by
  induction A generalizing t with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, trun]
    cases tstep t c with
    | none => rfl
    | some t' => exact ih t'

theorem lrun_append (A B : List TStmt) (t : LState) :
    lrun (A ++ B) t = (lrun A t).bind (lrun B) := by
  induction A generalizing t with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, lrun]
    cases lstep t c with
    | none => rfl
    | some t' => exact ih t'

theorem prun_append (φ : Nat → Int) (A B : List TStmt) (t : PState) :
    prun φ (A ++ B) t = (prun φ A t).bind (prun φ B) := by
  induction A generalizing t with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, prun]
    cases pstep φ t c with
    | none => rfl
    | some t' => exact ih t'

theorem hrun_cons (k : Nat) (c : Stmt) (cs : List Stmt) (s : HState) :
    hrun k (c :: cs) s = (hstep k s c).bind (hrun (k + 1) cs) := by
  simp only [hrun]
  cases hstep k s c <;> rfl

theorem trun_cons (c : TStmt) (cs : List TStmt) (t : TState) :
    trun (c :: cs) t = (tstep t c).bind (trun cs) := by
  simp only [trun]
  cases tstep t c <;> rfl

theorem lrun_cons (c : TStmt) (cs : List TStmt) (t : LState) :
    lrun (c :: cs) t = (lstep t c).bind (lrun cs) := by
  simp only [lrun]
  cases lstep t c <;> rfl

theorem prun_cons (φ : Nat → Int) (c : TStmt) (cs : List TStmt) (t : PState) :
    prun φ (c :: cs) t = (pstep φ t c).bind (prun φ cs) := by
  simp only [prun]
  cases pstep φ t c <;> rfl

/-! ## Regions and reference tables -/

/-- The pointer of the region created at `i`, if statement `i` is an `asMut`. -/
def regionPtr (P : Prog) (i : Nat) : Option Ptr :=
  match P[i]? with
  | some (.asMut p) => some p
  | _ => none

/-- The reference table of the heap semantics after the first `k` statements. -/
def refOf (P : Prog) (k i : Nat) : Option Ptr :=
  if i < k then regionPtr P i else none

theorem isRegion_iff (P : Prog) (i : Nat) : isRegion P i = true ↔ ∃ p, regionPtr P i = some p := by
  unfold isRegion regionPtr
  split <;> simp_all

theorem regionPtr_lt {P : Prog} {i : Nat} {p : Ptr} (h : regionPtr P i = some p) : i < P.length := by
  unfold regionPtr at h
  split at h
  · rename_i q hq
    exact (List.getElem?_eq_some_iff.mp hq).1
  · cases h

theorem regionPtr_of_get {P : Prog} {i : Nat} {p : Ptr} (h : P[i]? = some (.asMut p)) :
    regionPtr P i = some p := by
  unfold regionPtr; rw [h]

theorem regionPtr_of_get_ne {P : Prog} {k : Nat} {c : Stmt} (h : P[k]? = some c)
    (hc : ∀ p, c ≠ .asMut p) : regionPtr P k = none := by
  unfold regionPtr; rw [h]
  cases c <;> simp_all

theorem get_of_regionPtr {P : Prog} {i : Nat} {p : Ptr} (h : regionPtr P i = some p) :
    P[i]? = some (.asMut p) := by
  unfold regionPtr at h
  split at h
  · rename_i q hq
    cases h; exact hq
  · cases h

theorem ownerAccessAfter_of {P : Prog} {i k : Nat} {p : Ptr} {c : Stmt}
    (hi : regionPtr P i = some p) (hik : i < k) (hk : P[k]? = some c) (hc : c.touchesOwner p = true) :
    ownerAccessAfter P i k = true := by
  unfold ownerAccessAfter
  rw [get_of_regionPtr hi, hk]
  simp [hik, hc]

theorem usesAt_of {P : Prog} {j r : Nat} {c : Stmt} (hj : P[j]? = some c) (hc : c.usesRef r = true) :
    usesAt P j r = true := by
  unfold usesAt; rw [hj]; exact hc

theorem writesAt_of {P : Prog} {j r : Nat} {c : Stmt} (hj : P[j]? = some c) (hc : c.writesRef r = true) :
    writesAt P j r = true := by
  unfold writesAt; rw [hj]; exact hc

theorem refOf_zero (P : Prog) (i : Nat) : refOf P 0 i = none := by
  simp [refOf]

theorem refOf_succ_of_ne {P : Prog} {k : Nat} (hk : regionPtr P k = none) (i : Nat) :
    refOf P (k + 1) i = refOf P k i := by
  unfold refOf
  by_cases h1 : i < k
  · simp [h1, Nat.lt_succ_of_lt h1]
  · by_cases h2 : i = k
    · subst h2; simp [hk]
    · have : ¬ i < k + 1 := by omega
      simp [h1, this]

theorem refOf_succ_asMut {P : Prog} {k : Nat} {p : Ptr} (hk : regionPtr P k = some p) :
    refOf P (k + 1) = upd (refOf P k) k (some p) := by
  funext i
  unfold refOf upd
  by_cases h2 : i = k
  · subst h2; simp [hk]
  · simp only [h2, ↓reduceIte]
    by_cases h1 : i < k
    · simp [h1, Nat.lt_succ_of_lt h1]
    · have : ¬ i < k + 1 := by omega
      simp [h1, this]

theorem refOf_some {P : Prog} {k i : Nat} {p : Ptr} (h : refOf P k i = some p) :
    i < k ∧ regionPtr P i = some p := by
  unfold refOf at h
  split at h
  · exact ⟨by assumption, h⟩
  · cases h

theorem refOf_self (P : Prog) (k : Nat) : refOf P k k = none := by
  simp [refOf]

/-! ## Backward calls scheduled at a point -/

/-- The regions whose backward call is scheduled immediately before statement `k`. -/
def backsList (P : Prog) (π : Placement) (k : Nat) : List Nat :=
  (List.range P.length).filter fun i => isRegion P i && π i == k

theorem backsAt_eq (P : Prog) (π : Placement) (k : Nat) :
    backsAt P π k = (backsList P π k).map TStmt.back := rfl

theorem mem_backsList {P : Prog} {π : Placement} {k i : Nat} :
    i ∈ backsList P π k ↔ i < P.length ∧ isRegion P i = true ∧ π i = k := by
  simp [backsList]

theorem backsList_nodup (P : Prog) (π : Placement) (k : Nat) : (backsList P π k).Nodup :=
  (List.nodup_range).filter _

/-! ## Source-indexed decomposition -/

theorem translateFrom_cons (P : Prog) (π : Placement) (k : Nat) (c : Stmt) (cs : List Stmt) :
    translateFrom P π k (c :: cs) = backsAt P π k ++ trStmt k c :: translateFrom P π (k + 1) cs :=
  rfl

theorem get_head {P : Prog} {k : Nat} {c : Stmt} {cs : List Stmt}
    (hP : ∀ j, P[k + j]? = (c :: cs)[j]?) : P[k]? = some c := by
  have := hP 0
  simpa using this

theorem get_tail {P : Prog} {k : Nat} {c : Stmt} {cs : List Stmt}
    (hP : ∀ j, P[k + j]? = (c :: cs)[j]?) : ∀ j, P[k + 1 + j]? = cs[j]? := by
  intro j
  have := hP (j + 1)
  rw [show k + (j + 1) = k + 1 + j by omega] at this
  simpa using this

theorem lt_of_head {P : Prog} {k : Nat} {c : Stmt} {cs : List Stmt}
    (hk : k + (c :: cs).length = P.length) : k < P.length := by
  simp at hk; omega

/-! ## A finite count of bound slots -/

/-- Number of indices `i < n` with `f i` bound. -/
def cnt {α : Type} (f : Nat → Option α) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt f n + (if (f n).isSome then 1 else 0)

theorem cnt_congr {α : Type} {f g : Nat → Option α} : ∀ n, (∀ i, i < n → (f i).isSome = (g i).isSome) →
    cnt f n = cnt g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [cnt]
    rw [cnt_congr n (fun i hi => h i (by omega)), h n (by omega)]

theorem cnt_upd {α : Type} (f : Nat → Option α) (i : Nat) (b : Option α) : ∀ n, i < n →
    cnt (upd f i b) n + (if (f i).isSome then 1 else 0) = cnt f n + (if b.isSome then 1 else 0)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    simp only [cnt]
    by_cases hin : i < n
    · have ih := cnt_upd f i b n hin
      have : upd f i b n = f n := upd_ne f b (by omega)
      rw [this]
      omega
    · have hi : i = n := by omega
      subst hi
      have hc : cnt (upd f i b) i = cnt f i :=
        cnt_congr i (fun j hj => by rw [upd_ne f b (by omega)])
      rw [hc, upd_same]
      omega

theorem cnt_eq_zero {α : Type} {f : Nat → Option α} : ∀ n, cnt f n = 0 → ∀ i, i < n → f i = none
  | 0, _, i, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h, i, hi => by
    simp only [cnt] at h
    by_cases hin : i < n
    · exact cnt_eq_zero n (by omega) i hin
    · have : i = n := by omega
      subst this
      cases hf : f i with
      | none => rfl
      | some _ => simp [hf] at h

theorem cnt_none {α : Type} : ∀ n, cnt (fun _ : Nat => (none : Option α)) n = 0
  | 0 => rfl
  | n + 1 => by simp [cnt, cnt_none n]

theorem cnt_eq_zero_of {α : Type} {f : Nat → Option α} : ∀ n, (∀ i, i < n → f i = none) → cnt f n = 0
  | 0, _ => rfl
  | n + 1, h => by
    simp only [cnt]
    rw [cnt_eq_zero_of n (fun i hi => h i (by omega)), h n (by omega)]
    rfl


/-! ## The unchecked write-back translation simulates the heap semantics -/

/-- Simulation relation between a heap-semantics state `s` and an `effSem` target state `t` at
source point `k`; `O i` says that region `i` has not been ended yet. -/
structure EffRel (P : Prog) (k : Nat) (O : Nat → Prop) (s : HState) (t : TState) : Prop where
  vars : t.vars = s.vars
  refs : ∀ i, s.refs i = refOf P k i
  slots : ∀ i, (t.slots i).map Prod.fst = s.refs i
  vals : ∀ i p v, t.slots i = some (p, v) → (O i ∨ ∃ j, k ≤ j ∧ usesAt P j i = true) → v = s.heap p
  heap : ∀ p, (∀ i, s.refs i = some p → ¬ O i) → t.heap p = s.heap p

theorem EffRel.refs_of_slot {P k O s t} (hR : EffRel P k O s t) {i p v}
    (h : t.slots i = some (p, v)) : s.refs i = some p := by
  rw [← hR.slots i, h]; rfl

theorem EffRel.slot_of_refs {P k O s t} (hR : EffRel P k O s t) {i p} (h : s.refs i = some p) :
    ∃ v, t.slots i = some (p, v) := by
  have := hR.slots i
  rw [h] at this
  cases hs : t.slots i with
  | none => rw [hs] at this; cases this
  | some pv =>
    rw [hs] at this
    obtain ⟨q, v⟩ := pv
    simp only [Option.map_some, Option.some.injEq] at this
    subst this
    exact ⟨v, rfl⟩

theorem EffRel.slot_none {P k O s t} (hR : EffRel P k O s t) {i} (h : s.refs i = none) :
    t.slots i = none := by
  have := hR.slots i
  rw [h] at this
  cases hs : t.slots i with
  | none => rfl
  | some _ => rw [hs] at this; cases this

theorem EffRel.congr {P k O O' s t} (hR : EffRel P k O s t)
    (h : ∀ i, s.refs i ≠ none → (O i ↔ O' i)) : EffRel P k O' s t where
  vars := hR.vars
  refs := hR.refs
  slots := hR.slots
  vals := by
    intro i p v hs hc
    apply hR.vals i p v hs
    rcases hc with hc | hc
    · left
      have hr : s.refs i ≠ none := by rw [hR.refs_of_slot hs]; simp
      exact (h i hr).2 hc
    · exact Or.inr hc
  heap := by
    intro p hp
    apply hR.heap p
    intro i hi hO
    exact hp i hi ((h i (by rw [hi]; simp)).1 hO)

theorem effRel_back {P : Prog} {k : Nat} {O : Nat → Prop} {s : HState} {t : TState} {i : Nat}
    {p : Ptr} {v : Int} (hR : EffRel P k O s t) (hs : t.slots i = some (p, v)) (hO : O i) :
    tstep t (.back i) = some { t with heap := upd t.heap p v } ∧
    EffRel P k (fun j => O j ∧ j ≠ i) s { t with heap := upd t.heap p v } := by
  refine ⟨by simp [tstep, hs], ?_⟩
  refine ⟨hR.vars, hR.refs, hR.slots, ?_, ?_⟩
  · intro j q w hj hc
    apply hR.vals j q w hj
    rcases hc with hc | hc
    · exact Or.inl hc.1
    · exact Or.inr hc
  · intro q hq
    show upd t.heap p v q = s.heap q
    by_cases hqp : q = p
    · subst hqp
      rw [upd_same]
      exact hR.vals i q v hs (Or.inl hO)
    · rw [upd_ne _ _ hqp]
      apply hR.heap q
      intro j hj hOj
      by_cases hji : j = i
      · subst hji
        rw [hR.refs_of_slot hs] at hj
        exact hqp (Option.some.inj hj).symm
      · exact hq j hj ⟨hOj, hji⟩

theorem effRel_backs {P : Prog} {k : Nat} {s : HState} :
    ∀ (L : List Nat) (O : Nat → Prop) (t : TState), L.Nodup →
      (∀ i ∈ L, O i ∧ s.refs i ≠ none) → EffRel P k O s t →
      ∃ t', trun (L.map TStmt.back) t = some t' ∧ EffRel P k (fun j => O j ∧ j ∉ L) s t'
  | [], O, t, _, _, hR => ⟨t, rfl, hR.congr (fun j _ => by simp)⟩
  | i :: L, O, t, hnd, hL, hR => by
    obtain ⟨hOi, hri⟩ := hL i (by simp)
    cases hp : s.refs i with
    | none => exact absurd hp hri
    | some p =>
      obtain ⟨v, hv⟩ := hR.slot_of_refs hp
      obtain ⟨h1, hR1⟩ := effRel_back hR hv hOi
      have hnd' := List.nodup_cons.mp hnd
      obtain ⟨t', ht', hR'⟩ := effRel_backs L (fun j => O j ∧ j ≠ i) _ hnd'.2
        (fun j hj => ⟨⟨(hL j (by simp [hj])).1, fun e => hnd'.1 (e ▸ hj)⟩, (hL j (by simp [hj])).2⟩)
        hR1
      refine ⟨t', ?_, hR'.congr (fun j _ => ?_)⟩
      · rw [List.map_cons, trun_cons, h1]
        exact ht'
      · simp only [List.mem_cons, not_or]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

section Eff

variable {P : Prog} {π : Placement}

theorem effRel_stmt (hw : EndsAfterLastWrite P π) (ho : EndsByNextOwnerAccess P π)
    (had : AliasingDiscipline P) {k : Nat} {c : Stmt} (hk : P[k]? = some c) {s : HState}
    {t : TState} (hR : EffRel P k (fun j => k < π j) s t) :
    (hstep k s c = none → tstep t (trStmt k c) = none) ∧
    (∀ s', hstep k s c = some s' → ∃ t', tstep t (trStmt k c) = some t' ∧
      EffRel P (k + 1) (fun j => k < π j) s' t') := by
  have hkN : k < P.length := (List.getElem?_eq_some_iff.mp hk).1
  have hown : ∀ q, c.touchesOwner q = true → ∀ i, s.refs i = some q → ¬ k < π i := by
    intro q hq i hi hlt
    obtain ⟨hik, hreg⟩ := refOf_some ((hR.refs i).symm.trans hi)
    have := ho i (regionPtr_lt hreg) k hkN (ownerAccessAfter_of hreg hik hk hq)
    omega
  cases c with
  | asMut p =>
    have hrp : regionPtr P k = some p := regionPtr_of_get hk
    refine ⟨fun h => by simp [hstep] at h, ?_⟩
    intro s' hs'
    simp only [hstep, Option.some.injEq] at hs'
    subst hs'
    refine ⟨{ t with slots := upd t.slots k (some (p, t.heap p)) }, rfl, ?_⟩
    have hheap : t.heap p = s.heap p := hR.heap p (hown p (by simp [Stmt.touchesOwner]))
    refine ⟨hR.vars, ?_, ?_, ?_, ?_⟩
    · intro i
      show upd s.refs k (some p) i = refOf P (k + 1) i
      rw [refOf_succ_asMut hrp]
      by_cases hik : i = k
      · subst hik; rw [upd_same, upd_same]
      · rw [upd_ne _ _ hik, upd_ne _ _ hik]; exact hR.refs i
    · intro i
      show ((upd t.slots k (some (p, t.heap p))) i).map Prod.fst = upd s.refs k (some p) i
      by_cases hik : i = k
      · subst hik; rw [upd_same, upd_same]; rfl
      · rw [upd_ne _ _ hik, upd_ne _ _ hik]; exact hR.slots i
    · intro i q v hi hcond
      show v = s.heap q
      change upd t.slots k (some (p, t.heap p)) i = some (q, v) at hi
      by_cases hik : i = k
      · subst hik
        rw [upd_same] at hi
        simp only [Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        exact hheap
      · rw [upd_ne _ _ hik] at hi
        apply hR.vals i q v hi
        rcases hcond with h | ⟨j, hj1, hj2⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, hj2⟩
    · intro q hq
      show t.heap q = s.heap q
      apply hR.heap q
      intro i hi hlt
      have hik : i ≠ k := by
        intro e; subst e; rw [hR.refs, refOf_self] at hi; cases hi
      apply hq i _ hlt
      show upd s.refs k (some p) i = some q
      rw [upd_ne _ _ hik]; exact hi
  | read x r =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    have huse : usesAt P k r = true := usesAt_of hk (by simp [Stmt.usesRef])
    constructor
    · intro h
      simp only [hstep] at h
      split at h
      · cases h
      · rename_i hnone
        simp only [trStmt, tstep, hR.slot_none hnone]
    · intro s' hs'
      simp only [hstep] at hs'
      split at hs'
      · rename_i p hp
        cases hs'
        obtain ⟨v, hv⟩ := hR.slot_of_refs hp
        have hval : v = s.heap p := hR.vals r p v hv (Or.inr ⟨k, Nat.le_refl _, huse⟩)
        refine ⟨{ t with vars := upd t.vars x v }, by simp [trStmt, tstep, hv], ?_⟩
        refine ⟨?_, ?_, hR.slots, ?_, hR.heap⟩
        · show upd t.vars x v = upd s.vars x (s.heap p)
          rw [hR.vars, hval]
        · intro i; rw [refOf_succ_of_ne hrk]; exact hR.refs i
        · intro i q w hi hcond
          apply hR.vals i q w hi
          rcases hcond with h | ⟨j, hj1, hj2⟩
          · exact Or.inl h
          · exact Or.inr ⟨j, by omega, hj2⟩
      · cases hs'
  | write r e =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    have huse : usesAt P k r = true := usesAt_of hk (by simp [Stmt.usesRef])
    have hwr : writesAt P k r = true := writesAt_of hk (by simp [Stmt.writesRef])
    constructor
    · intro h
      simp only [hstep] at h
      split at h
      · cases h
      · rename_i hnone
        simp only [trStmt, tstep, hR.slot_none hnone]
    · intro s' hs'
      simp only [hstep] at hs'
      split at hs'
      · rename_i p hp
        cases hs'
        obtain ⟨v, hv⟩ := hR.slot_of_refs hp
        obtain ⟨hrk', hreg⟩ := refOf_some ((hR.refs r).symm.trans hp)
        have hopen : k < π r :=
          hw r (regionPtr_lt hreg) ((isRegion_iff P r).2 ⟨p, hreg⟩) k hkN hwr
        refine ⟨{ t with slots := upd t.slots r (some (p, e.eval t.vars)) },
          by simp [trStmt, tstep, hv], ?_⟩
        refine ⟨hR.vars, ?_, ?_, ?_, ?_⟩
        · intro i; rw [refOf_succ_of_ne hrk]; exact hR.refs i
        · intro i
          show (upd t.slots r (some (p, e.eval t.vars)) i).map Prod.fst = s.refs i
          by_cases hir : i = r
          · subst hir; rw [upd_same, hp]; rfl
          · rw [upd_ne _ _ hir]; exact hR.slots i
        · intro i q w hi hcond
          show w = upd s.heap p (e.eval s.vars) q
          change upd t.slots r (some (p, e.eval t.vars)) i = some (q, w) at hi
          by_cases hir : i = r
          · subst hir
            rw [upd_same] at hi
            simp only [Option.some.injEq, Prod.mk.injEq] at hi
            obtain ⟨rfl, rfl⟩ := hi
            rw [upd_same, hR.vars]
          · rw [upd_ne _ _ hir] at hi
            by_cases hqp : q = p
            · subst hqp
              exfalso
              have hiq := hR.refs_of_slot hi
              obtain ⟨hik, hregi⟩ := refOf_some ((hR.refs i).symm.trans hiq)
              rcases Nat.lt_or_gt_of_ne hir with hlt | hlt
              · have hoa := ownerAccessAfter_of hregi hlt (get_of_regionPtr hreg)
                  (by simp [Stmt.touchesOwner])
                have h1 := ho i (regionPtr_lt hregi) r (regionPtr_lt hreg) hoa
                rcases hcond with h | ⟨j, hj1, hj2⟩
                · have h' : k < π i := h
                  omega
                · have := had i (regionPtr_lt hregi) j (lt_length_of_usesAt hj2) r
                    (regionPtr_lt hreg) hj2 hoa
                  omega
              · have hoa := ownerAccessAfter_of hreg hlt (get_of_regionPtr hregi)
                  (by simp [Stmt.touchesOwner])
                have := had r (regionPtr_lt hreg) k hkN i (regionPtr_lt hregi) huse hoa
                omega
            · rw [upd_ne _ _ hqp]
              apply hR.vals i q w hi
              rcases hcond with h | ⟨j, hj1, hj2⟩
              · exact Or.inl h
              · exact Or.inr ⟨j, by omega, hj2⟩
        · intro q hq
          show t.heap q = upd s.heap p (e.eval s.vars) q
          by_cases hqp : q = p
          · subst hqp; exact absurd hopen (hq r hp)
          · rw [upd_ne _ _ hqp]
            exact hR.heap q hq
      · cases hs'
  | rawRead x p =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    have hheap : t.heap p = s.heap p := hR.heap p (hown p (by simp [Stmt.touchesOwner]))
    refine ⟨fun h => by simp [hstep] at h, ?_⟩
    intro s' hs'
    simp only [hstep, Option.some.injEq] at hs'
    subst hs'
    refine ⟨{ t with vars := upd t.vars x (t.heap p) }, rfl, ?_⟩
    refine ⟨?_, ?_, hR.slots, ?_, hR.heap⟩
    · show upd t.vars x (t.heap p) = upd s.vars x (s.heap p)
      rw [hR.vars, hheap]
    · intro i; rw [refOf_succ_of_ne hrk]; exact hR.refs i
    · intro i q w hi hcond
      apply hR.vals i q w hi
      rcases hcond with h | ⟨j, hj1, hj2⟩
      · exact Or.inl h
      · exact Or.inr ⟨j, by omega, hj2⟩
  | rawWrite p e =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    have hno := hown p (by simp [Stmt.touchesOwner])
    refine ⟨fun h => by simp [hstep] at h, ?_⟩
    intro s' hs'
    simp only [hstep, Option.some.injEq] at hs'
    subst hs'
    refine ⟨{ t with heap := upd t.heap p (e.eval t.vars) }, rfl, ?_⟩
    refine ⟨hR.vars, ?_, hR.slots, ?_, ?_⟩
    · intro i; rw [refOf_succ_of_ne hrk]; exact hR.refs i
    · intro i q w hi hcond
      show w = upd s.heap p (e.eval s.vars) q
      by_cases hqp : q = p
      · subst hqp
        exfalso
        have hiq := hR.refs_of_slot hi
        obtain ⟨hik, hregi⟩ := refOf_some ((hR.refs i).symm.trans hiq)
        have hoa := ownerAccessAfter_of hregi hik hk (by simp [Stmt.touchesOwner])
        rcases hcond with h | ⟨j, hj1, hj2⟩
        · exact hno i hiq h
        · have := had i (regionPtr_lt hregi) j (lt_length_of_usesAt hj2) k hkN hj2 hoa
          omega
      · rw [upd_ne _ _ hqp]
        apply hR.vals i q w hi
        rcases hcond with h | ⟨j, hj1, hj2⟩
        · exact Or.inl h
        · exact Or.inr ⟨j, by omega, hj2⟩
    · intro q hq
      show upd t.heap p (e.eval t.vars) q = upd s.heap p (e.eval s.vars) q
      by_cases hqp : q = p
      · subst hqp; rw [upd_same, upd_same, hR.vars]
      · rw [upd_ne _ _ hqp, upd_ne _ _ hqp]; exact hR.heap q hq

theorem eff_main (hc : EndsAfterCreation P π) (hw : EndsAfterLastWrite P π)
    (ho : EndsByNextOwnerAccess P π) (he : EndsByProgramEnd P π) (had : AliasingDiscipline P) :
    ∀ (cs : List Stmt) (k : Nat) (s : HState) (t : TState),
      k + cs.length = P.length → (∀ j, P[k + j]? = cs[j]?) →
      EffRel P k (fun j => k ≤ π j) s t →
      (hrun k cs s).map (fun s => (⟨s.heap, s.vars⟩ : Obs)) =
        (trun (translateFrom P π k cs ++ backsAt P π P.length) t).map TState.obs
  | [], k, s, t, hk, _, hR => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    obtain ⟨t', ht', hR'⟩ := effRel_backs (backsList P π P.length) _ t (backsList_nodup _ _ _)
      (fun i hi => by
        obtain ⟨hiN, hreg, hπ⟩ := mem_backsList.mp hi
        obtain ⟨p, hp⟩ := (isRegion_iff P i).1 hreg
        refine ⟨by show P.length ≤ π i; omega, ?_⟩
        rw [hR.refs i]; simp [refOf, hiN, hp]) hR
    have hheap : t'.heap = s.heap := by
      funext p
      apply hR'.heap p
      intro i hi hO
      obtain ⟨hiN, hreg⟩ := refOf_some ((hR.refs i).symm.trans hi)
      have hreg' : isRegion P i = true := (isRegion_iff P i).2 ⟨p, hreg⟩
      have h1 := he i hiN hreg'
      have h2 : P.length ≤ π i := hO.1
      exact hO.2 (mem_backsList.mpr ⟨hiN, hreg', by omega⟩)
    rw [show translateFrom P π P.length [] = [] from rfl, List.nil_append, backsAt_eq, ht']
    simp [hrun, TState.obs, hheap, hR'.vars]
  | c :: cs, k, s, t, hk, hP, hR => by
    have hck : P[k]? = some c := get_head hP
    obtain ⟨t1, ht1, hR1⟩ := effRel_backs (backsList P π k) _ t (backsList_nodup _ _ _)
      (fun i hi => by
        obtain ⟨hiN, hreg, hπ⟩ := mem_backsList.mp hi
        obtain ⟨p, hp⟩ := (isRegion_iff P i).1 hreg
        have hik : i < k := by have := hc i hiN hreg; omega
        refine ⟨by show k ≤ π i; omega, ?_⟩
        rw [hR.refs i]; simp [refOf, hik, hp]) hR
    have hR1' : EffRel P k (fun j => k < π j) s t1 := hR1.congr (fun i hi => by
      cases hp : s.refs i with
      | none => exact absurd hp hi
      | some p =>
        obtain ⟨hik, hreg⟩ := refOf_some ((hR.refs i).symm.trans hp)
        have hreg' : isRegion P i = true := (isRegion_iff P i).2 ⟨p, hreg⟩
        have hiN := regionPtr_lt hreg
        simp only [mem_backsList, not_and]
        constructor
        · rintro ⟨h1, h2⟩
          have : π i ≠ k := fun e => h2 hiN hreg' e
          omega
        · intro h; exact ⟨by omega, fun _ _ e => by omega⟩)
    obtain ⟨hnone, hsome⟩ := effRel_stmt hw ho had hck hR1'
    rw [hrun_cons, translateFrom_cons, List.append_assoc, trun_append (backsAt P π k), backsAt_eq,
      ht1, List.cons_append]
    simp only [Option.bind, trun_cons]
    cases hs : hstep k s c with
    | none => rw [hnone hs]; rfl
    | some s' =>
      obtain ⟨t', ht', hR'⟩ := hsome s' hs
      rw [ht']
      exact eff_main hc hw ho he had cs (k + 1) s' t' (by simp at hk; omega) (get_tail hP)
        (hR'.congr (fun _ _ => Iff.rfl))

/-- `endpoint-window-last-write`, proved. -/
theorem effSem_eq_heapSem (P : Prog) (π : Placement) (h : Heap)
    (hc : EndsAfterCreation P π) (hw : EndsAfterLastWrite P π) (ho : EndsByNextOwnerAccess P π)
    (he : EndsByProgramEnd P π) (had : AliasingDiscipline P) :
    effSem P π h = heapSem P h := by
  have := eff_main hc hw ho he had P 0 (HState.init h) (TState.init h) (by simp) (fun j => by simp)
    ⟨rfl, fun i => (refOf_zero P i).symm, fun _ => rfl, fun _ _ _ h => (by cases h), fun _ _ => rfl⟩
  exact this.symm

end Eff

end Toy.Backward.Sim
