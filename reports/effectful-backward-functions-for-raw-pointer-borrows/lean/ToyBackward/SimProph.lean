import ToyBackward.SimLock

/-!
# Simulation lemmas for the prophecy encoding

Auxiliary definitions and lemmas used only inside the proofs of `prophecy-agreement` and
`prophecy-sound-wider-window`: successful unchecked runs end regions after their creation; the
prophecy encoding gets stuck exactly when the unchecked target does; a lockstep relation between
the unchecked target and the prophecy encoding for a fixed prophecy assignment, together with a
look-ahead predicate (`GoodFor`) saying that every resolution assumption of a run holds; and
invariance of the prophecy encoding under moving resolution points earlier inside a window where the
borrow's value no longer changes.
-/

namespace Toy.Backward.Sim

open Toy.Backward

/-! ## Reference tables of the target runs -/

theorem tslots_tstep {P : Prog} {k : Nat} {c : Stmt} {t t1 : TState} (hk : P[k]? = some c)
    (htr : ∀ i, (t.slots i).map Prod.fst = refOf P k i) (h : tstep t (trStmt k c) = some t1) :
    ∀ i, (t1.slots i).map Prod.fst = refOf P (k + 1) i := by
  cases c with
  | asMut p =>
    simp only [trStmt, tstep, Option.some.injEq] at h
    subst h
    intro i
    show ((upd t.slots k (some (p, t.heap p))) i).map Prod.fst = refOf P (k + 1) i
    rw [refOf_succ_asMut (regionPtr_of_get hk)]
    by_cases hik : i = k
    · subst hik; rw [upd_same, upd_same]; rfl
    · rw [upd_ne _ _ hik, upd_ne _ _ hik]; exact htr i
  | read x r =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    cases hs : t.slots r with
    | none => simp [trStmt, tstep, hs] at h
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [trStmt, tstep, hs, Option.some.injEq] at h
      subst h
      intro i; rw [refOf_succ_of_ne hrk]; exact htr i
  | write r e =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    cases hs : t.slots r with
    | none => simp [trStmt, tstep, hs] at h
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [trStmt, tstep, hs, Option.some.injEq] at h
      subst h
      intro i
      show (upd t.slots r (some (p, e.eval t.vars)) i).map Prod.fst = refOf P (k + 1) i
      rw [refOf_succ_of_ne hrk]
      by_cases hir : i = r
      · subst hir; rw [upd_same, ← htr i, hs]; rfl
      · rw [upd_ne _ _ hir]; exact htr i
  | rawRead x p =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    simp only [trStmt, tstep, Option.some.injEq] at h
    subst h
    intro i; rw [refOf_succ_of_ne hrk]; exact htr i
  | rawWrite p e =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    simp only [trStmt, tstep, Option.some.injEq] at h
    subst h
    intro i; rw [refOf_succ_of_ne hrk]; exact htr i

theorem trun_backs_inv : ∀ (L : List Nat) (t t1 : TState), trun (L.map TStmt.back) t = some t1 →
    (∀ i ∈ L, (t.slots i).isSome = true) ∧ t1.slots = t.slots
  | [], t, t1, h => by cases Option.some.inj h; exact ⟨fun _ h => (by cases h), rfl⟩
  | i :: L, t, t1, h => by
    rw [List.map_cons, trun_cons] at h
    cases hs : t.slots i with
    | none => simp [tstep, hs] at h
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [tstep, hs, Option.bind] at h
      obtain ⟨h1, h2⟩ := trun_backs_inv L _ t1 h
      refine ⟨fun j hj => ?_, h2⟩
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · simp [hs]
      · exact h1 j hj

section Creation

variable {P : Prog} {π : Placement}

theorem eac_main :
    ∀ (cs : List Stmt) (k : Nat) (t t' : TState),
      k + cs.length = P.length → (∀ j, P[k + j]? = cs[j]?) →
      (∀ i, (t.slots i).map Prod.fst = refOf P k i) →
      (∀ i, isRegion P i = true → k ≤ i → k ≤ π i) →
      trun (translateFrom P π k cs ++ backsAt P π P.length) t = some t' →
      ∀ i, isRegion P i = true → k ≤ π i → i < π i
  | [], k, t, t', hk, _, _, _, _ => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    intro i hr hki
    have := isRegion_lt hr
    omega
  | c :: cs, k, t, t', hk, hP, htr, hfut, ht => by
    have hck : P[k]? = some c := get_head hP
    rw [translateFrom_cons, List.append_assoc, trun_append (backsAt P π k), backsAt_eq] at ht
    cases hb : trun ((backsList P π k).map TStmt.back) t with
    | none => rw [hb] at ht; cases ht
    | some t1 =>
      rw [hb] at ht
      simp only [Option.bind, List.cons_append, trun_cons] at ht
      obtain ⟨hbound, hsl⟩ := trun_backs_inv _ t t1 hb
      have hlt : ∀ i ∈ backsList P π k, i < k := by
        intro i hi
        have h1 := hbound i hi
        cases hs : t.slots i with
        | none => rw [hs] at h1; cases h1
        | some pv => obtain ⟨p, v⟩ := pv; exact (tslot_some htr hs).1
      have htr1 : ∀ i, (t1.slots i).map Prod.fst = refOf P k i := by rw [hsl]; exact htr
      cases hs : tstep t1 (trStmt k c) with
      | none => rw [hs] at ht; cases ht
      | some t2 =>
        rw [hs] at ht
        have IH := eac_main cs (k + 1) t2 t' (by simp at hk; omega) (get_tail hP)
          (tslots_tstep hck htr1 hs)
          (fun i hr hki => by
            have h1 := hfut i hr (by omega)
            rcases Nat.lt_or_ge k (π i) with h2 | h2
            · exact h2
            · have he : π i = k := by omega
              have := hlt i (mem_backsList.mpr ⟨isRegion_lt hr, hr, he⟩)
              omega) ht
        intro i hr hki
        by_cases he : π i = k
        · have := hlt i (mem_backsList.mpr ⟨isRegion_lt hr, hr, he⟩)
          omega
        · exact IH i hr (by omega)

/-- A successful run of the unchecked target ends every region after its creation. -/
theorem endsAfterCreation_of_trun {h : Heap} {t' : TState}
    (ht : trun (translate P π) (TState.init h) = some t') : EndsAfterCreation P π := by
  intro i _ hr
  exact eac_main P 0 (TState.init h) t' (by simp) (fun j => by simp)
    (fun i => by rw [refOf_zero]; rfl) (fun _ _ _ => Nat.zero_le _) ht i hr (Nat.zero_le _)

end Creation

/-! ## The prophecy encoding is stuck exactly when the unchecked target is -/

theorem shape_step (φ : Nat → Int) {t : TState} {u : PState}
    (hsh : ∀ i, (t.slots i).isSome = (u.slots i).isSome) (c : TStmt) :
    (tstep t c = none ↔ pstep φ u c = none) ∧
    (∀ t1 u1, tstep t c = some t1 → pstep φ u c = some u1 →
      ∀ i, (t1.slots i).isSome = (u1.slots i).isSome) := by
  cases c with
  | fwd i p =>
    refine ⟨by simp [tstep, pstep], fun t1 u1 h1 h2 j => ?_⟩
    simp only [tstep, pstep, Option.some.injEq] at h1 h2
    subst h1; subst h2
    show (upd t.slots i _ j).isSome = (upd u.slots i _ j).isSome
    by_cases hji : j = i
    · subst hji; rw [upd_same, upd_same]; rfl
    · rw [upd_ne _ _ hji, upd_ne _ _ hji]; exact hsh j
  | lread x i =>
    have hi := hsh i
    cases ht : t.slots i with
    | none =>
      cases hu : u.slots i with
      | none =>
        exact ⟨by simp [tstep, pstep, ht, hu], fun t1 u1 h1 _ => by simp [tstep, ht] at h1⟩
      | some _ => rw [ht, hu] at hi; cases hi
    | some pv =>
      cases hu : u.slots i with
      | none => rw [ht, hu] at hi; cases hi
      | some qw =>
        obtain ⟨p, v⟩ := pv
        obtain ⟨q, w⟩ := qw
        refine ⟨by simp [tstep, pstep, ht, hu], fun t1 u1 h1 h2 j => ?_⟩
        simp only [tstep, pstep, ht, hu, Option.some.injEq] at h1 h2
        subst h1; subst h2
        exact hsh j
  | lwrite i e =>
    have hi := hsh i
    cases ht : t.slots i with
    | none =>
      cases hu : u.slots i with
      | none =>
        exact ⟨by simp [tstep, pstep, ht, hu], fun t1 u1 h1 _ => by simp [tstep, ht] at h1⟩
      | some _ => rw [ht, hu] at hi; cases hi
    | some pv =>
      cases hu : u.slots i with
      | none => rw [ht, hu] at hi; cases hi
      | some qw =>
        obtain ⟨p, v⟩ := pv
        obtain ⟨q, w⟩ := qw
        refine ⟨by simp [tstep, pstep, ht, hu], fun t1 u1 h1 h2 j => ?_⟩
        simp only [tstep, pstep, ht, hu, Option.some.injEq] at h1 h2
        subst h1; subst h2
        show (upd t.slots i _ j).isSome = (upd u.slots i _ j).isSome
        by_cases hji : j = i
        · subst hji; rw [upd_same, upd_same]; rfl
        · rw [upd_ne _ _ hji, upd_ne _ _ hji]; exact hsh j
  | back i =>
    have hi := hsh i
    cases ht : t.slots i with
    | none =>
      cases hu : u.slots i with
      | none =>
        exact ⟨by simp [tstep, pstep, ht, hu], fun t1 u1 h1 _ => by simp [tstep, ht] at h1⟩
      | some _ => rw [ht, hu] at hi; cases hi
    | some pv =>
      cases hu : u.slots i with
      | none => rw [ht, hu] at hi; cases hi
      | some qw =>
        obtain ⟨p, v⟩ := pv
        obtain ⟨q, w⟩ := qw
        refine ⟨by simp [tstep, pstep, ht, hu], fun t1 u1 h1 h2 j => ?_⟩
        simp only [tstep, pstep, ht, hu, Option.some.injEq] at h1 h2
        subst h1; subst h2
        exact hsh j
  | rawRead x p =>
    refine ⟨by simp [tstep, pstep], fun t1 u1 h1 h2 j => ?_⟩
    simp only [tstep, pstep, Option.some.injEq] at h1 h2
    subst h1; subst h2
    exact hsh j
  | rawWrite p e =>
    refine ⟨by simp [tstep, pstep], fun t1 u1 h1 h2 j => ?_⟩
    simp only [tstep, pstep, Option.some.injEq] at h1 h2
    subst h1; subst h2
    exact hsh j

theorem shape_run (φ : Nat → Int) : ∀ (L : List TStmt) (t : TState) (u : PState),
    (∀ i, (t.slots i).isSome = (u.slots i).isSome) → (trun L t = none ↔ prun φ L u = none)
  | [], _, _, _ => by simp [trun, prun]
  | c :: cs, t, u, hsh => by
    rw [trun_cons, prun_cons]
    obtain ⟨h1, h2⟩ := shape_step φ hsh c
    cases ht : tstep t c with
    | none =>
      have := h1.1 ht
      rw [this]; simp
    | some t1 =>
      cases hu : pstep φ u c with
      | none => have := h1.2 hu; rw [this] at ht; cases ht
      | some u1 =>
        simp only [Option.bind]
        exact shape_run φ cs t1 u1 (h2 t1 u1 ht hu)

theorem pstep_ok_false {φ : Nat → Int} {u u1 : PState} {c : TStmt} (h : pstep φ u c = some u1)
    (hok : u.ok = false) : u1.ok = false := by
  cases c with
  | fwd i p => simp only [pstep, Option.some.injEq] at h; subst h; exact hok
  | lread x i =>
    cases hs : u.slots i with
    | none => simp [pstep, hs] at h
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [pstep, hs, Option.some.injEq] at h; subst h; exact hok
  | lwrite i e =>
    cases hs : u.slots i with
    | none => simp [pstep, hs] at h
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [pstep, hs, Option.some.injEq] at h; subst h; exact hok
  | back i =>
    cases hs : u.slots i with
    | none => simp [pstep, hs] at h
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [pstep, hs, Option.some.injEq] at h; subst h; simp [hok]
  | rawRead x p => simp only [pstep, Option.some.injEq] at h; subst h; exact hok
  | rawWrite p e => simp only [pstep, Option.some.injEq] at h; subst h; exact hok

theorem prun_ok_false (φ : Nat → Int) : ∀ (L : List TStmt) (u u' : PState),
    prun φ L u = some u' → u.ok = false → u'.ok = false
  | [], u, u', h, hok => by cases Option.some.inj h; exact hok
  | c :: cs, u, u', h, hok => by
    rw [prun_cons] at h
    cases hs : pstep φ u c with
    | none => rw [hs] at h; cases h
    | some u1 =>
      rw [hs] at h
      exact prun_ok_false φ cs u1 u' h (pstep_ok_false hs hok)

/-! ## Look-ahead: every resolution assumption of a run holds -/

/-- `GoodFor φ L t`: along the unchecked run of `L` from `t`, every backward call `back i` meets a
slot value equal to `φ i`. -/
def GoodFor (φ : Nat → Int) : List TStmt → TState → Prop
  | [], _ => True
  | c :: cs, t => (∀ i p v, c = .back i → t.slots i = some (p, v) → v = φ i) ∧
      (∀ t1, tstep t c = some t1 → GoodFor φ cs t1)

theorem goodFor_append (φ : Nat → Int) : ∀ (A B : List TStmt) (t : TState),
    GoodFor φ (A ++ B) t ↔ GoodFor φ A t ∧ ∀ t1, trun A t = some t1 → GoodFor φ B t1
  | [], B, t => by
    simp only [List.nil_append, GoodFor, true_and]
    constructor
    · intro h t1 ht1; cases Option.some.inj ht1; exact h
    · intro h; exact h t rfl
  | c :: A, B, t => by
    simp only [List.cons_append, GoodFor]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, fun t1 ht1 => ((goodFor_append φ A B t1).1 (h2 t1 ht1)).1⟩, fun t2 ht2 => ?_⟩
      rw [trun_cons] at ht2
      cases hs : tstep t c with
      | none => rw [hs] at ht2; cases ht2
      | some t1 =>
        rw [hs] at ht2
        exact ((goodFor_append φ A B t1).1 (h2 t1 hs)).2 t2 ht2
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, fun t1 ht1 => (goodFor_append φ A B t1).2 ⟨h2 t1 ht1, fun t2 ht2 => h3 t2 ?_⟩⟩
      rw [trun_cons, ht1]; exact ht2

theorem goodFor_cons_nonback (φ : Nat → Int) {c : TStmt} (hc : ∀ i, c ≠ .back i) (cs : List TStmt)
    (t : TState) : GoodFor φ (c :: cs) t ↔ ∀ t1, tstep t c = some t1 → GoodFor φ cs t1 := by
  simp only [GoodFor]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨fun i _ _ e _ => absurd e (hc i), h⟩

theorem trStmt_ne_back (k : Nat) (c : Stmt) (i : Nat) : trStmt k c ≠ .back i := by
  cases c <;> simp [trStmt]

theorem goodFor_backs (φ : Nat → Int) : ∀ (L : List Nat) (t : TState),
    (∀ i ∈ L, ∀ p v, t.slots i = some (p, v) → v = φ i) → GoodFor φ (L.map TStmt.back) t
  | [], _, _ => trivial
  | i :: L, t, h => by
    refine ⟨fun j p v e hs => ?_, fun t1 ht1 => goodFor_backs φ L t1 (fun j hj p v hs => ?_)⟩
    · cases e; exact h _ (by simp) p v hs
    · have : t1.slots = t.slots := by
        cases hsi : t.slots i with
        | none => simp [tstep, hsi] at ht1
        | some pv =>
          obtain ⟨q, w⟩ := pv
          simp only [tstep, hsi, Option.some.injEq] at ht1
          rw [← ht1]
      rw [this] at hs
      exact h j (by simp [hj]) p v hs

/-! ## Lockstep relation between `trun` and `prun` -/

/-- Relation between an unchecked target state `t` and a prophecy-encoding state `u` at source
point `k`, for the prophecy assignment `φ`; `O i` says that region `i` has not been ended yet. An
open region's cell holds its prophecy; every other cell agrees. -/
structure PRel (P : Prog) (k : Nat) (O : Nat → Prop) (φ : Nat → Int) (t : TState) (u : PState) :
    Prop where
  slots : u.slots = t.slots
  vars : u.vars = t.vars
  tslots : ∀ i, (t.slots i).map Prod.fst = refOf P k i
  hopen : ∀ i p v, t.slots i = some (p, v) → O i → u.heap p = φ i
  hclosed : ∀ p, (∀ i v, t.slots i = some (p, v) → ¬ O i) → u.heap p = t.heap p

theorem PRel.congr {P k O O' φ t u} (hR : PRel P k O φ t u)
    (h : ∀ i, (t.slots i).isSome = true → (O i ↔ O' i)) : PRel P k O' φ t u where
  slots := hR.slots
  vars := hR.vars
  tslots := hR.tslots
  hopen := fun i p v hs hO => hR.hopen i p v hs ((h i (by simp [hs])).2 hO)
  hclosed := fun p hp => hR.hclosed p (fun i v hs hO => hp i v hs ((h i (by simp [hs])).1 hO))

theorem upd_slot_ptr {S : Nat → Option (Ptr × Int)} {r : Nat} {p : Ptr} {v v' : Int}
    (h : S r = some (p, v)) {i : Nat} {q : Ptr} {w : Int}
    (hi : upd S r (some (p, v')) i = some (q, w)) : ∃ w', S i = some (q, w') := by
  by_cases hir : i = r
  · subst hir; rw [upd_same] at hi
    simp only [Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    exact ⟨v, h⟩
  · rw [upd_ne _ _ hir] at hi; exact ⟨w, hi⟩

theorem slot_upd_ptr {S : Nat → Option (Ptr × Int)} {r : Nat} {p : Ptr} {v v' : Int}
    (h : S r = some (p, v)) {i : Nat} {q : Ptr} {w : Int}
    (hi : S i = some (q, w)) : ∃ w', upd S r (some (p, v')) i = some (q, w') := by
  by_cases hir : i = r
  · subst hir; rw [h] at hi
    simp only [Option.some.injEq, Prod.mk.injEq] at hi
    obtain ⟨rfl, rfl⟩ := hi
    exact ⟨v', upd_same _ _ _⟩
  · exact ⟨w, by rw [upd_ne _ _ hir]; exact hi⟩

theorem prop_back {P : Prog} {k : Nat} {O : Nat → Prop} {φ : Nat → Int} {t : TState} {u : PState}
    {i : Nat} {p : Ptr} {v : Int} (hR : PRel P k O φ t u) (hs : t.slots i = some (p, v))
    (hO : O i) (hv : v = φ i) :
    PRel P k (fun j => O j ∧ j ≠ i) φ { t with heap := upd t.heap p v }
      { u with ok := u.ok && decide (v = φ i) } where
  slots := hR.slots
  vars := hR.vars
  tslots := hR.tslots
  hopen := fun j q w hj hO' => hR.hopen j q w hj hO'.1
  hclosed := by
    intro q hq
    show u.heap q = upd t.heap p v q
    by_cases hqp : q = p
    · subst hqp; rw [upd_same, hR.hopen i q v hs hO, hv]
    · rw [upd_ne _ _ hqp]
      apply hR.hclosed q
      intro j w hj hOj
      have hji : j ≠ i := by
        intro e; subst e; rw [hs] at hj
        simp only [Option.some.injEq, Prod.mk.injEq] at hj
        exact hqp hj.1.symm
      exact hq j w hj ⟨hOj, hji⟩

theorem prop_backs {P : Prog} {k : Nat} {φ : Nat → Int} :
    ∀ (L : List Nat) (O : Nat → Prop) (t : TState) (u : PState), L.Nodup →
      (∀ i ∈ L, O i ∧ (t.slots i).isSome = true) → (u.ok = true → PRel P k O φ t u) →
      u.slots = t.slots →
      ∃ t1 u1, trun (L.map TStmt.back) t = some t1 ∧ prun φ (L.map TStmt.back) u = some u1 ∧
        t1.slots = t.slots ∧ u1.slots = u.slots ∧
        (u1.ok = true ↔ u.ok = true ∧ GoodFor φ (L.map TStmt.back) t) ∧
        (u1.ok = true → PRel P k (fun j => O j ∧ j ∉ L) φ t1 u1)
  | [], O, t, u, _, _, hR, _ => ⟨t, u, rfl, rfl, rfl, rfl, by simp [GoodFor],
      fun h => (hR h).congr (fun j _ => by simp)⟩
  | i :: L, O, t, u, hnd, hL, hR, hsl => by
    obtain ⟨hOi, hsi⟩ := hL i (by simp)
    cases hs : t.slots i with
    | none => rw [hs] at hsi; cases hsi
    | some pv =>
      obtain ⟨p, v⟩ := pv
      have hus : u.slots i = some (p, v) := by rw [hsl]; exact hs
      have hnd' := List.nodup_cons.mp hnd
      obtain ⟨t1, u1, ht1, hu1, hts, hus1, hiff, hR1⟩ :=
        prop_backs L (fun j => O j ∧ j ≠ i) { t with heap := upd t.heap p v }
          { u with ok := u.ok && decide (v = φ i) } hnd'.2
          (fun j hj => ⟨⟨(hL j (by simp [hj])).1, fun e => hnd'.1 (e ▸ hj)⟩,
            (hL j (by simp [hj])).2⟩)
          (fun hok => by
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
            exact prop_back (hR hok.1) hs hOi hok.2)
          hsl
      refine ⟨t1, u1, ?_, ?_, hts, hus1, ?_, fun hok => (hR1 hok).congr (fun j _ => ?_)⟩
      · rw [List.map_cons, trun_cons]; simp only [tstep, hs]; exact ht1
      · rw [List.map_cons, prun_cons]; simp only [pstep, hus]; exact hu1
      · rw [hiff]
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.map_cons, GoodFor]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, fun j q w e hj => ?_, fun t2 ht2 => ?_⟩
          · cases e; rw [hs] at hj
            simp only [Option.some.injEq, Prod.mk.injEq] at hj
            obtain ⟨rfl, rfl⟩ := hj; exact h2
          · simp only [tstep, hs, Option.some.injEq] at ht2
            subst ht2; exact h3
        · rintro ⟨h1, h2, h3⟩
          exact ⟨⟨h1, h2 i p v rfl hs⟩, h3 _ (by simp [tstep, hs])⟩
      · simp only [List.mem_cons, not_or]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

section Proph

variable {P : Prog} {π : Placement}

theorem prop_noOpen (ho : EndsByNextOwnerAccess P π) {k : Nat} {c : Stmt} (hk : P[k]? = some c)
    {φ : Nat → Int} {t : TState} {u : PState} (hR : PRel P k (fun j => k < π j) φ t u) {p : Ptr}
    (hp : c.touchesOwner p = true) : ∀ i v, t.slots i = some (p, v) → ¬ k < π i := by
  intro i v hs hlt
  obtain ⟨hik, hreg⟩ := tslot_some hR.tslots hs
  have := ho i (regionPtr_lt hreg) k (List.getElem?_eq_some_iff.mp hk).1
    (ownerAccessAfter_of hreg hik hk hp)
  omega

theorem prop_stmt (hc : EndsAfterCreation P π) (ho : EndsByNextOwnerAccess P π) {k : Nat} {c : Stmt}
    (hk : P[k]? = some c) {φ : Nat → Int} {t t1 : TState} {u : PState}
    (hR : PRel P k (fun j => k < π j) φ t u) (ht : tstep t (trStmt k c) = some t1) :
    ∃ u1, pstep φ u (trStmt k c) = some u1 ∧ u1.ok = u.ok ∧
      PRel P (k + 1) (fun j => k < π j) φ t1 u1 := by
  have hkN : k < P.length := (List.getElem?_eq_some_iff.mp hk).1
  have htr1 := tslots_tstep hk hR.tslots ht
  cases c with
  | asMut p =>
    simp only [trStmt, tstep, Option.some.injEq] at ht
    subst ht
    have hrp : regionPtr P k = some p := regionPtr_of_get hk
    have hπk : k < π k := hc k hkN ((isRegion_iff P k).2 ⟨p, hrp⟩)
    have hno := prop_noOpen ho hk hR (p := p) (by simp [Stmt.touchesOwner])
    have hheap : u.heap p = t.heap p := hR.hclosed p hno
    have htk : t.slots k = none := tslot_none hR.tslots (refOf_self P k)
    refine ⟨{ u with slots := upd u.slots k (some (p, u.heap p)), heap := upd u.heap p (φ k) },
      by simp [trStmt, pstep], rfl, ?_, hR.vars, htr1, ?_, ?_⟩
    · show upd u.slots k (some (p, u.heap p)) = upd t.slots k (some (p, t.heap p))
      rw [hR.slots, hheap]
    · intro i q w hi hO
      change upd t.slots k (some (p, t.heap p)) i = some (q, w) at hi
      show upd u.heap p (φ k) q = φ i
      by_cases hik : i = k
      · subst hik; rw [upd_same] at hi
        simp only [Option.some.injEq, Prod.mk.injEq] at hi
        rw [← hi.1, upd_same]
      · rw [upd_ne _ _ hik] at hi
        by_cases hqp : q = p
        · subst hqp; exact absurd hO (hno i w hi)
        · rw [upd_ne _ _ hqp]; exact hR.hopen i q w hi hO
    · intro q hq
      show upd u.heap p (φ k) q = t.heap q
      by_cases hqp : q = p
      · subst hqp
        exact absurd hπk (hq k (t.heap q) (by show upd t.slots k _ k = _; rw [upd_same]))
      · rw [upd_ne _ _ hqp]
        apply hR.hclosed q
        intro i w hi hO
        have hik : i ≠ k := by intro e; subst e; rw [htk] at hi; cases hi
        exact hq i w (by show upd t.slots k _ i = _; rw [upd_ne _ _ hik]; exact hi) hO
  | read x r =>
    cases hs : t.slots r with
    | none => simp [trStmt, tstep, hs] at ht
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [trStmt, tstep, hs, Option.some.injEq] at ht
      subst ht
      have hus : u.slots r = some (p, v) := by rw [hR.slots]; exact hs
      refine ⟨{ u with vars := upd u.vars x v }, by simp [trStmt, pstep, hus], rfl, hR.slots,
        by simp [hR.vars], htr1, hR.hopen, hR.hclosed⟩
  | write r e =>
    cases hs : t.slots r with
    | none => simp [trStmt, tstep, hs] at ht
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [trStmt, tstep, hs, Option.some.injEq] at ht
      subst ht
      have hus : u.slots r = some (p, v) := by rw [hR.slots]; exact hs
      refine ⟨{ u with slots := upd u.slots r (some (p, e.eval u.vars)) },
        by simp [trStmt, pstep, hus], rfl, ?_, hR.vars, htr1, ?_, ?_⟩
      · show upd u.slots r (some (p, e.eval u.vars)) = upd t.slots r (some (p, e.eval t.vars))
        rw [hR.slots, hR.vars]
      · intro i q w hi hO
        obtain ⟨w', hw'⟩ := upd_slot_ptr hs hi
        exact hR.hopen i q w' hw' hO
      · intro q hq
        apply hR.hclosed q
        intro i w hi hO
        obtain ⟨w', hw'⟩ := slot_upd_ptr (v' := e.eval t.vars) hs hi
        exact hq i w' hw' hO
  | rawRead x p =>
    simp only [trStmt, tstep, Option.some.injEq] at ht
    subst ht
    have hheap : u.heap p = t.heap p :=
      hR.hclosed p (prop_noOpen ho hk hR (p := p) (by simp [Stmt.touchesOwner]))
    refine ⟨{ u with vars := upd u.vars x (u.heap p) }, by simp [trStmt, pstep], rfl, hR.slots,
      by simp [hR.vars, hheap], htr1, hR.hopen, hR.hclosed⟩
  | rawWrite p e =>
    simp only [trStmt, tstep, Option.some.injEq] at ht
    subst ht
    have hno := prop_noOpen ho hk hR (p := p) (by simp [Stmt.touchesOwner])
    refine ⟨{ u with heap := upd u.heap p (e.eval u.vars) }, by simp [trStmt, pstep], rfl, hR.slots,
      hR.vars, htr1, ?_, ?_⟩
    · intro i q w hi hO
      show upd u.heap p (e.eval u.vars) q = φ i
      by_cases hqp : q = p
      · subst hqp; exact absurd hO (hno i w hi)
      · rw [upd_ne _ _ hqp]; exact hR.hopen i q w hi hO
    · intro q hq
      show upd u.heap p (e.eval u.vars) q = upd t.heap p (e.eval t.vars) q
      by_cases hqp : q = p
      · subst hqp; rw [upd_same, upd_same, hR.vars]
      · rw [upd_ne _ _ hqp, upd_ne _ _ hqp]; exact hR.hclosed q hq

theorem prop_main (hc : EndsAfterCreation P π) (ho : EndsByNextOwnerAccess P π)
    (he : EndsByProgramEnd P π) (φ : Nat → Int) :
    ∀ (cs : List Stmt) (k : Nat) (t : TState) (u : PState),
      k + cs.length = P.length → (∀ j, P[k + j]? = cs[j]?) →
      PRel P k (fun j => k ≤ π j) φ t u → u.ok = true →
      ∀ t', trun (translateFrom P π k cs ++ backsAt P π P.length) t = some t' →
        ∃ u', prun φ (translateFrom P π k cs ++ backsAt P π P.length) u = some u' ∧
          (u'.ok = true ↔ GoodFor φ (translateFrom P π k cs ++ backsAt P π P.length) t) ∧
          (u'.ok = true → u'.heap = t'.heap ∧ u'.vars = t'.vars)
  | [], k, t, u, hk, _, hR, hok, t', ht => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    obtain ⟨t1, u1, ht1, hu1, _, _, hiff, hR1⟩ := prop_backs (backsList P π P.length) _ t u
      (backsList_nodup _ _ _)
      (fun i hi => by
        obtain ⟨hiN, hreg, hπ⟩ := mem_backsList.mp hi
        obtain ⟨p, hp⟩ := (isRegion_iff P i).1 hreg
        refine ⟨by show P.length ≤ π i; omega, ?_⟩
        obtain ⟨v, hv⟩ := tslot_of_ref hR.tslots
          (show refOf P P.length i = some p by simp [refOf, hiN, hp])
        simp [hv]) (fun _ => hR) hR.slots
    rw [show translateFrom P π P.length [] = [] from rfl, List.nil_append, backsAt_eq] at ht ⊢
    rw [ht1] at ht
    cases Option.some.inj ht
    refine ⟨u1, hu1, by rw [hiff, hok]; simp, fun h1 => ⟨?_, (hR1 h1).vars⟩⟩
    funext q
    apply (hR1 h1).hclosed q
    rintro i w hi ⟨h2, h3⟩
    obtain ⟨hiN, hreg⟩ := tslot_some (hR1 h1).tslots hi
    have hreg' := (isRegion_iff P i).2 ⟨q, hreg⟩
    exact h3 (mem_backsList.mpr ⟨hiN, hreg', by have := he i hiN hreg'; omega⟩)
  | c :: cs, k, t, u, hk, hP, hR, hok, t', ht => by
    have hck : P[k]? = some c := get_head hP
    obtain ⟨t1, u1, ht1, hu1, hts, hus, hiff, hR1⟩ := prop_backs (backsList P π k) _ t u
      (backsList_nodup _ _ _)
      (fun i hi => by
        obtain ⟨hiN, hreg, hπ⟩ := mem_backsList.mp hi
        obtain ⟨p, hp⟩ := (isRegion_iff P i).1 hreg
        have hik : i < k := by have := hc i hiN hreg; omega
        refine ⟨by show k ≤ π i; omega, ?_⟩
        obtain ⟨v, hv⟩ := tslot_of_ref hR.tslots (show refOf P k i = some p by simp [refOf, hik, hp])
        simp [hv]) (fun _ => hR) hR.slots
    have hsplit : ∀ (A : List TStmt), translateFrom P π k (c :: cs) ++ A =
        (backsList P π k).map TStmt.back ++ (trStmt k c :: (translateFrom P π (k + 1) cs ++ A)) := by
      intro A; rw [translateFrom_cons, List.append_assoc, backsAt_eq, List.cons_append]
    rw [hsplit] at ht ⊢
    rw [trun_append, ht1] at ht
    simp only [Option.bind] at ht
    rw [prun_append, hu1]
    simp only [Option.bind]
    rw [goodFor_append]
    cases hok1 : u1.ok with
    | false =>
      have hsh : ∀ i, (t1.slots i).isSome = (u1.slots i).isSome := by
        intro i; rw [hts, hus, hR.slots]
      cases hp : prun φ (trStmt k c :: (translateFrom P π (k + 1) cs ++ backsAt P π P.length)) u1 with
      | none =>
        have := (shape_run φ _ t1 u1 hsh).2 hp
        rw [this] at ht; cases ht
      | some u' =>
        refine ⟨u', rfl, ?_, fun h => ?_⟩
        · rw [prun_ok_false φ _ u1 u' hp hok1]
          simp only [Bool.false_eq_true, false_iff, not_and]
          intro hg
          have := hiff.2 ⟨hok, hg⟩
          rw [hok1] at this; cases this
        · rw [prun_ok_false φ _ u1 u' hp hok1] at h; cases h
    | true =>
      have hgb : GoodFor φ ((backsList P π k).map TStmt.back) t := (hiff.1 hok1).2
      have hR1' : PRel P k (fun j => k < π j) φ t1 u1 := (hR1 hok1).congr (fun i hi => by
        cases hs : t1.slots i with
        | none => rw [hs] at hi; cases hi
        | some pv =>
          obtain ⟨p, v⟩ := pv
          obtain ⟨hik, hreg⟩ := tslot_some (hR1 hok1).tslots hs
          have hreg' : isRegion P i = true := (isRegion_iff P i).2 ⟨p, hreg⟩
          have hiN := regionPtr_lt hreg
          simp only [mem_backsList, not_and]
          constructor
          · rintro ⟨h1, h2⟩
            have : π i ≠ k := fun e => h2 hiN hreg' e
            omega
          · intro h; exact ⟨by omega, fun _ _ e => by omega⟩)
      rw [trun_cons] at ht
      cases hs : tstep t1 (trStmt k c) with
      | none => rw [hs] at ht; cases ht
      | some t2 =>
        rw [hs] at ht
        obtain ⟨u2, hu2, hok2, hR2⟩ := prop_stmt hc ho hck hR1' hs
        obtain ⟨u', hu', hiff', hobs⟩ := prop_main hc ho he φ cs (k + 1) t2 u2
          (by simp at hk; omega) (get_tail hP) (hR2.congr (fun _ _ => Iff.rfl))
          (by rw [hok2, hok1]) t' ht
        refine ⟨u', by rw [prun_cons, hu2]; exact hu', ?_, hobs⟩
        rw [hiff']
        constructor
        · intro hg
          refine ⟨hgb, fun t3 ht3 => ?_⟩
          rw [ht1] at ht3; cases Option.some.inj ht3
          rw [goodFor_cons_nonback φ (trStmt_ne_back k c)]
          intro t4 ht4
          rw [hs] at ht4; cases Option.some.inj ht4
          exact hg
        · rintro ⟨_, hg⟩
          have := hg t1 ht1
          rw [goodFor_cons_nonback φ (trStmt_ne_back k c)] at this
          exact this t2 hs

/-- Record, for every region scheduled to end immediately before statement `k`, the current value
of its slot (the value its backward call will meet). -/
def recordAt (π : Placement) (k : Nat) (t : TState) (ψ : Nat → Int) : Nat → Int :=
  fun i => if π i = k then (match t.slots i with | some (_, v) => v | none => ψ i) else ψ i

theorem recordAt_spec {π : Placement} {k : Nat} {t : TState} {ψ : Nat → Int} {i : Nat} {p : Ptr}
    {v : Int} (hπ : π i = k) (hs : t.slots i = some (p, v)) : v = recordAt π k t ψ i := by
  simp [recordAt, hπ, hs]

theorem recordAt_ne {π : Placement} {k : Nat} {t : TState} {ψ : Nat → Int} {i : Nat}
    (hπ : π i ≠ k) : recordAt π k t ψ i = ψ i := by
  simp [recordAt, hπ]

theorem goodFor_exists :
    ∀ (cs : List Stmt) (k : Nat) (t : TState) (ψ : Nat → Int), k + cs.length = P.length →
      ∃ φ, GoodFor φ (translateFrom P π k cs ++ backsAt P π P.length) t ∧
        ∀ i, π i < k → φ i = ψ i
  | [], k, t, ψ, hk => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    refine ⟨recordAt π P.length t ψ, ?_, fun i hi => recordAt_ne (by omega)⟩
    rw [show translateFrom P π P.length [] = [] from rfl, List.nil_append, backsAt_eq]
    exact goodFor_backs _ _ t (fun i hi p v hs => recordAt_spec (mem_backsList.mp hi).2.2 hs)
  | c :: cs, k, t, ψ, hk => by
    rw [translateFrom_cons, List.append_assoc, backsAt_eq, List.cons_append]
    have hgb : ∀ φ, (∀ i, π i = k → φ i = recordAt π k t ψ i) →
        GoodFor φ ((backsList P π k).map TStmt.back) t := fun φ hφ =>
      goodFor_backs _ _ t (fun i hi p v hs => by
        rw [hφ i (mem_backsList.mp hi).2.2]
        exact recordAt_spec (mem_backsList.mp hi).2.2 hs)
    cases hb : trun ((backsList P π k).map TStmt.back) t with
    | none =>
      refine ⟨recordAt π k t ψ, (goodFor_append _ _ _ t).2 ⟨hgb _ (fun _ _ => rfl), ?_⟩,
        fun i hi => recordAt_ne (by omega)⟩
      intro t1 ht1; rw [hb] at ht1; cases ht1
    | some t1 =>
      cases hs : tstep t1 (trStmt k c) with
      | none =>
        refine ⟨recordAt π k t ψ, (goodFor_append _ _ _ t).2 ⟨hgb _ (fun _ _ => rfl), ?_⟩,
          fun i hi => recordAt_ne (by omega)⟩
        intro t1' ht1'
        rw [hb] at ht1'; cases Option.some.inj ht1'
        rw [goodFor_cons_nonback _ (trStmt_ne_back k c)]
        intro t2 ht2; rw [hs] at ht2; cases ht2
      | some t2 =>
        obtain ⟨φ, hg, hag⟩ := goodFor_exists cs (k + 1) t2 (recordAt π k t ψ)
          (by simp at hk; omega)
        refine ⟨φ, (goodFor_append _ _ _ t).2 ⟨hgb φ (fun i hi => hag i (by omega)), ?_⟩,
          fun i hi => by rw [hag i (by omega), recordAt_ne (by omega)]⟩
        intro t1' ht1'
        rw [hb] at ht1'; cases Option.some.inj ht1'
        rw [goodFor_cons_nonback _ (trStmt_ne_back k c)]
        intro t2' ht2'; rw [hs] at ht2'; cases Option.some.inj ht2'
        exact hg

/-- `prophecy-agreement`, proved. -/
theorem prophOutcome_iff_effSem (P : Prog) (π : Placement) (h : Heap)
    (ho : EndsByNextOwnerAccess P π) (he : EndsByProgramEnd P π) :
    ∀ o, ProphOutcome P π h o ↔ effSem P π h = some o := by
  intro o
  have hsh : ∀ i, ((TState.init h).slots i).isSome =
      ((⟨h, fun _ => none, fun _ => 0, true⟩ : PState).slots i).isSome := fun _ => rfl
  have hR0 : ∀ φ, PRel P 0 (fun j => 0 ≤ π j) φ (TState.init h)
      ⟨h, fun _ => none, fun _ => 0, true⟩ := fun φ =>
    ⟨rfl, rfl, fun i => by rw [refOf_zero]; rfl, fun _ _ _ hs _ => (by cases hs), fun _ _ => rfl⟩
  unfold ProphOutcome prophSem effSem translate
  constructor
  · rintro ⟨φ, hφ⟩
    cases hp : prun φ (translateFrom P π 0 P ++ backsAt P π P.length)
        ⟨h, fun _ => none, fun _ => 0, true⟩ with
    | none => rw [hp] at hφ; cases hφ
    | some u' =>
      rw [hp] at hφ
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hφ
      obtain ⟨hobs, hok⟩ := hφ
      cases ht : trun (translateFrom P π 0 P ++ backsAt P π P.length) (TState.init h) with
      | none => have := (shape_run φ _ _ _ hsh).1 ht; rw [this] at hp; cases hp
      | some t' =>
        have hc : EndsAfterCreation P π := endsAfterCreation_of_trun (h := h) ht
        obtain ⟨u'', hu'', _, hobs'⟩ := prop_main hc ho he φ P 0 _ _ (by simp) (fun j => by simp)
          (hR0 φ) rfl t' ht
        rw [hp] at hu''; cases Option.some.inj hu''
        obtain ⟨h1, h2⟩ := hobs' hok
        rw [← hobs]
        simp [TState.obs, h1, h2]
  · intro he'
    cases ht : trun (translateFrom P π 0 P ++ backsAt P π P.length) (TState.init h) with
    | none => rw [ht] at he'; cases he'
    | some t' =>
      rw [ht] at he'
      simp only [Option.map_some, Option.some.injEq] at he'
      have hc : EndsAfterCreation P π := endsAfterCreation_of_trun (h := h) ht
      obtain ⟨φ, hg, _⟩ := goodFor_exists (P := P) (π := π) P 0 (TState.init h) (fun _ => 0) (by simp)
      obtain ⟨u', hu', hiff, hobs⟩ := prop_main hc ho he φ P 0 _ _ (by simp) (fun j => by simp)
        (hR0 φ) rfl t' ht
      have hok := hiff.2 hg
      obtain ⟨h1, h2⟩ := hobs hok
      refine ⟨φ, ?_⟩
      rw [hu']
      simp [← he', TState.obs, h1, h2, hok]

end Proph

/-! ## Moving resolution points earlier -/

theorem tslots_pstep {P : Prog} {k : Nat} {c : Stmt} {φ : Nat → Int} {u u1 : PState}
    (hk : P[k]? = some c) (htr : ∀ i, (u.slots i).map Prod.fst = refOf P k i)
    (h : pstep φ u (trStmt k c) = some u1) :
    ∀ i, (u1.slots i).map Prod.fst = refOf P (k + 1) i := by
  cases c with
  | asMut p =>
    simp only [trStmt, pstep, Option.some.injEq] at h
    subst h
    intro i
    show ((upd u.slots k (some (p, u.heap p))) i).map Prod.fst = refOf P (k + 1) i
    rw [refOf_succ_asMut (regionPtr_of_get hk)]
    by_cases hik : i = k
    · subst hik; rw [upd_same, upd_same]; rfl
    · rw [upd_ne _ _ hik, upd_ne _ _ hik]; exact htr i
  | read x r =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    cases hs : u.slots r with
    | none => simp [trStmt, pstep, hs] at h
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [trStmt, pstep, hs, Option.some.injEq] at h
      subst h
      intro i; rw [refOf_succ_of_ne hrk]; exact htr i
  | write r e =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    cases hs : u.slots r with
    | none => simp [trStmt, pstep, hs] at h
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [trStmt, pstep, hs, Option.some.injEq] at h
      subst h
      intro i
      show (upd u.slots r (some (p, e.eval u.vars)) i).map Prod.fst = refOf P (k + 1) i
      rw [refOf_succ_of_ne hrk]
      by_cases hir : i = r
      · subst hir; rw [upd_same, ← htr i, hs]; rfl
      · rw [upd_ne _ _ hir]; exact htr i
  | rawRead x p =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    simp only [trStmt, pstep, Option.some.injEq] at h
    subst h
    intro i; rw [refOf_succ_of_ne hrk]; exact htr i
  | rawWrite p e =>
    have hrk : regionPtr P k = none := regionPtr_of_get_ne hk (by intro p h; cases h)
    simp only [trStmt, pstep, Option.some.injEq] at h
    subst h
    intro i; rw [refOf_succ_of_ne hrk]; exact htr i

theorem pstep_slots_other {P : Prog} {k : Nat} {c : Stmt} {φ : Nat → Int} {u u1 : PState}
    (hk : P[k]? = some c) (h : pstep φ u (trStmt k c) = some u1) :
    ∀ i, i ≠ k → writesAt P k i = false → u1.slots i = u.slots i := by
  intro i hik hw
  cases c with
  | asMut p =>
    simp only [trStmt, pstep, Option.some.injEq] at h
    subst h
    exact upd_ne _ _ hik
  | read x r =>
    cases hs : u.slots r with
    | none => simp [trStmt, pstep, hs] at h
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [trStmt, pstep, hs, Option.some.injEq] at h
      subst h; rfl
  | write r e =>
    cases hs : u.slots r with
    | none => simp [trStmt, pstep, hs] at h
    | some pv =>
      obtain ⟨p, v⟩ := pv
      simp only [trStmt, pstep, hs, Option.some.injEq] at h
      subst h
      have hir : i ≠ r := by
        intro e'; subst e'
        rw [writesAt_of hk (by simp [Stmt.writesRef])] at hw; cases hw
      exact upd_ne _ _ hir
  | rawRead x p =>
    simp only [trStmt, pstep, Option.some.injEq] at h
    subst h; rfl
  | rawWrite p e =>
    simp only [trStmt, pstep, Option.some.injEq] at h
    subst h; rfl

theorem pstep_ok (φ : Nat → Int) {c : TStmt} (hc : ∀ i, c ≠ .back i) (u : PState) (b : Bool) :
    pstep φ { u with ok := b } c = (pstep φ u c).map (fun s => { s with ok := b }) ∧
      ∀ s, pstep φ u c = some s → s.ok = u.ok := by
  cases c with
  | fwd i p =>
    refine ⟨by simp [pstep], fun s h => ?_⟩
    simp only [pstep, Option.some.injEq] at h; subst h; rfl
  | lread x i =>
    cases hs : u.slots i with
    | none => exact ⟨by simp [pstep, hs], fun s h => by simp [pstep, hs] at h⟩
    | some pv =>
      obtain ⟨p, v⟩ := pv
      refine ⟨by simp [pstep, hs], fun s h => ?_⟩
      simp only [pstep, hs, Option.some.injEq] at h; subst h; rfl
  | lwrite i e =>
    cases hs : u.slots i with
    | none => exact ⟨by simp [pstep, hs], fun s h => by simp [pstep, hs] at h⟩
    | some pv =>
      obtain ⟨p, v⟩ := pv
      refine ⟨by simp [pstep, hs], fun s h => ?_⟩
      simp only [pstep, hs, Option.some.injEq] at h; subst h; rfl
  | back i => exact absurd rfl (hc i)
  | rawRead x p =>
    refine ⟨by simp [pstep], fun s h => ?_⟩
    simp only [pstep, Option.some.injEq] at h; subst h; rfl
  | rawWrite p e =>
    refine ⟨by simp [pstep], fun s h => ?_⟩
    simp only [pstep, Option.some.injEq] at h; subst h; rfl

theorem prun_backs (φ : Nat → Int) : ∀ (L : List Nat) (u : PState),
    (∀ i ∈ L, (u.slots i).isSome = true) →
    ∃ u1, prun φ (L.map TStmt.back) u = some u1 ∧ u1 = { u with ok := u1.ok } ∧
      (u1.ok = true ↔ u.ok = true ∧ ∀ i ∈ L, ∀ p v, u.slots i = some (p, v) → v = φ i)
  | [], u, _ => ⟨u, rfl, rfl, by simp⟩
  | i :: L, u, hL => by
    have hsi := hL i (by simp)
    cases hs : u.slots i with
    | none => rw [hs] at hsi; cases hsi
    | some pv =>
      obtain ⟨p, v⟩ := pv
      obtain ⟨u1, hu1, heq, hiff⟩ := prun_backs φ L { u with ok := u.ok && decide (v = φ i) }
        (fun j hj => hL j (by simp [hj]))
      refine ⟨u1, ?_, ?_, ?_⟩
      · rw [List.map_cons, prun_cons]; simp only [pstep, hs]; exact hu1
      · rw [heq]
      · rw [hiff]
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, fun j hj q w hq => ?_⟩
          rcases hj with rfl | hj
          · rw [hs] at hq
            simp only [Option.some.injEq, Prod.mk.injEq] at hq
            obtain ⟨rfl, rfl⟩ := hq; exact h2
          · exact h3 j hj q w hq
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, h2 i (Or.inl rfl) p v hs⟩, fun j hj q w hq => h2 j (Or.inr hj) q w hq⟩

/-- Relation between two runs of the prophecy encoding that differ only in where the resolution
points (backward calls) are placed: the same heap, slots, and variables, and the later run's flag
equals the earlier run's flag conjoined with the checks still pending (`Pend`). -/
structure MRel (P : Prog) (k : Nat) (Pend : Nat → Prop) (φ : Nat → Int) (u u' : PState) : Prop where
  heap : u'.heap = u.heap
  slots : u'.slots = u.slots
  vars : u'.vars = u.vars
  ok : u'.ok = true ↔ (u.ok = true ∧ ∀ i, Pend i → ∀ p v, u.slots i = some (p, v) → v = φ i)
  tslots : ∀ i, (u.slots i).map Prod.fst = refOf P k i

theorem state_eq_with_ok {u u' : PState} (hh : u'.heap = u.heap) (hs : u'.slots = u.slots)
    (hv : u'.vars = u.vars) : u' = { u with ok := u'.ok } := by
  cases u; cases u'
  simp only at hh hs hv
  subst hh; subst hs; subst hv; rfl

theorem bool_eq_of_iff {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

section Move

variable {P : Prog} {π π' : Placement}

theorem move_bound {ρ : Placement} (hρ : EndsAfterCreation P ρ) {k : Nat} {u : PState}
    (htr : ∀ i, (u.slots i).map Prod.fst = refOf P k i) :
    ∀ i ∈ backsList P ρ k, (u.slots i).isSome = true := by
  intro i hi
  obtain ⟨hiN, hreg, hπ⟩ := mem_backsList.mp hi
  obtain ⟨p, hp⟩ := (isRegion_iff P i).1 hreg
  have hik : i < k := by have := hρ i hiN hreg; omega
  have := htr i
  rw [show refOf P k i = some p by simp [refOf, hik, hp]] at this
  cases hs : u.slots i with
  | none => rw [hs] at this; cases this
  | some _ => rfl

theorem move_main (hc : EndsAfterCreation P π) (hc' : EndsAfterCreation P π')
    (hw' : EndsAfterLastWrite P π') (he : EndsByProgramEnd P π) (hle : ∀ i, π' i ≤ π i)
    (φ : Nat → Int) :
    ∀ (cs : List Stmt) (k : Nat) (u u' : PState),
      k + cs.length = P.length → (∀ j, P[k + j]? = cs[j]?) →
      MRel P k (fun i => isRegion P i = true ∧ π' i < k ∧ k ≤ π i) φ u u' →
      (prun φ (translateFrom P π k cs ++ backsAt P π P.length) u).map
          (fun s => ((⟨s.heap, s.vars⟩ : Obs), s.ok)) =
        (prun φ (translateFrom P π' k cs ++ backsAt P π' P.length) u').map
          (fun s => ((⟨s.heap, s.vars⟩ : Obs), s.ok))
  | [], k, u, u', hk, _, hM => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    rw [show translateFrom P π P.length [] = [] from rfl,
      show translateFrom P π' P.length [] = [] from rfl, List.nil_append, List.nil_append,
      backsAt_eq, backsAt_eq]
    obtain ⟨u1, hu1, heq1, hiff1⟩ := prun_backs φ (backsList P π P.length) u
      (move_bound hc hM.tslots)
    obtain ⟨u1', hu1', heq1', hiff1'⟩ := prun_backs φ (backsList P π' P.length) u'
      (by rw [hM.slots]; exact move_bound hc' hM.tslots)
    rw [hu1, hu1']
    have h1h : u1.heap = u.heap := by rw [heq1]
    have h1v : u1.vars = u.vars := by rw [heq1]
    have h1h' : u1'.heap = u'.heap := by rw [heq1']
    have h1v' : u1'.vars = u'.vars := by rw [heq1']
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    refine ⟨by rw [h1h, h1v, h1h', h1v', hM.heap, hM.vars], bool_eq_of_iff ?_⟩
    rw [hiff1, hiff1', hM.ok, hM.slots]
    constructor
    · rintro ⟨hok, hL⟩
      refine ⟨⟨hok, fun i ⟨hr, h1, h2⟩ => hL i (mem_backsList.mpr ⟨isRegion_lt hr, hr, ?_⟩)⟩,
        fun i hi => ?_⟩
      · have := he i (isRegion_lt hr) hr; omega
      · obtain ⟨hiN, hr, h1⟩ := mem_backsList.mp hi
        have := he i hiN hr; have := hle i
        exact hL i (mem_backsList.mpr ⟨hiN, hr, by omega⟩)
    · rintro ⟨⟨hok, hP⟩, hL'⟩
      refine ⟨hok, fun i hi => ?_⟩
      obtain ⟨hiN, hr, h1⟩ := mem_backsList.mp hi
      by_cases h2 : π' i < P.length
      · exact hP i ⟨hr, h2, by omega⟩
      · have := hle i
        exact hL' i (mem_backsList.mpr ⟨hiN, hr, by omega⟩)
  | c :: cs, k, u, u', hk, hP, hM => by
    have hck : P[k]? = some c := get_head hP
    have hkN : k < P.length := (List.getElem?_eq_some_iff.mp hck).1
    have hsplit : ∀ (ρ : Placement), translateFrom P ρ k (c :: cs) ++ backsAt P ρ P.length =
        (backsList P ρ k).map TStmt.back ++
          (trStmt k c :: (translateFrom P ρ (k + 1) cs ++ backsAt P ρ P.length)) := by
      intro ρ; rw [translateFrom_cons, List.append_assoc, backsAt_eq, List.cons_append]
    rw [hsplit π, hsplit π', prun_append, prun_append]
    obtain ⟨u1, hu1, heq1, hiff1⟩ := prun_backs φ (backsList P π k) u (move_bound hc hM.tslots)
    obtain ⟨u1', hu1', heq1', hiff1'⟩ := prun_backs φ (backsList P π' k) u'
      (by rw [hM.slots]; exact move_bound hc' hM.tslots)
    rw [hu1, hu1']
    simp only [Option.bind]
    have h1s : u1.slots = u.slots := by rw [heq1]
    have h1s' : u1'.slots = u'.slots := by rw [heq1']
    have h1h : u1.heap = u.heap := by rw [heq1]
    have h1h' : u1'.heap = u'.heap := by rw [heq1']
    have h1v : u1.vars = u.vars := by rw [heq1]
    have h1v' : u1'.vars = u'.vars := by rw [heq1']
    have hu1'eq : u1' = { u1 with ok := u1'.ok } := state_eq_with_ok
      (by rw [h1h', h1h]; exact hM.heap)
      (by rw [h1s', h1s]; exact hM.slots)
      (by rw [h1v', h1v]; exact hM.vars)
    rw [prun_cons, prun_cons, hu1'eq, (pstep_ok φ (trStmt_ne_back k c) u1 u1'.ok).1]
    cases hs : pstep φ u1 (trStmt k c) with
    | none => rfl
    | some u2 =>
      simp only [Option.map_some, Option.bind]
      have hok2 : u2.ok = u1.ok := (pstep_ok φ (trStmt_ne_back k c) u1 u1'.ok).2 u2 hs
      have htr1 : ∀ i, (u1.slots i).map Prod.fst = refOf P k i := by rw [h1s]; exact hM.tslots
      have hsame : ∀ i, isRegion P i = true → π' i ≤ k → u2.slots i = u1.slots i := by
        intro i hr hi
        apply pstep_slots_other hck hs i
        · intro e; subst e; have := hc' i hkN hr; omega
        · cases hw : writesAt P k i with
          | false => rfl
          | true => have := hw' i (isRegion_lt hr) hr k hkN hw; omega
      apply move_main hc hc' hw' he hle φ cs (k + 1) u2 { u2 with ok := u1'.ok }
        (by simp at hk; omega) (get_tail hP)
      refine ⟨rfl, rfl, rfl, ?_, tslots_pstep hck htr1 hs⟩
      show u1'.ok = true ↔ _
      rw [hiff1', hok2, hiff1, hM.ok, hM.slots]
      constructor
      · rintro ⟨⟨hok, hPd⟩, hL'⟩
        refine ⟨⟨hok, fun i hi => ?_⟩, fun i ⟨hr, h1, h2⟩ p v hsl => ?_⟩
        · obtain ⟨hiN, hr, h1⟩ := mem_backsList.mp hi
          by_cases h2 : π' i < k
          · exact hPd i ⟨hr, h2, by omega⟩
          · have := hle i
            exact hL' i (mem_backsList.mpr ⟨hiN, hr, by omega⟩)
        · rw [hsame i hr (by omega), h1s] at hsl
          by_cases h3 : π' i < k
          · exact hPd i ⟨hr, h3, by omega⟩ p v hsl
          · exact hL' i (mem_backsList.mpr ⟨isRegion_lt hr, hr, by omega⟩) p v hsl
      · rintro ⟨⟨hok, hL⟩, hPd'⟩
        refine ⟨⟨hok, fun i ⟨hr, h1, h2⟩ p v hsl => ?_⟩, fun i hi p v hsl => ?_⟩
        · by_cases h3 : π i = k
          · exact hL i (mem_backsList.mpr ⟨isRegion_lt hr, hr, h3⟩) p v hsl
          · have := hPd' i ⟨hr, by omega, by omega⟩ p v
            rw [hsame i hr (by omega), h1s] at this
            exact this hsl
        · obtain ⟨hiN, hr, h1⟩ := mem_backsList.mp hi
          have := hle i
          by_cases h3 : π i = k
          · exact hL i (mem_backsList.mpr ⟨hiN, hr, h3⟩) p v hsl
          · have := hPd' i ⟨hr, by omega, by omega⟩ p v
            rw [hsame i hr (by omega), h1s] at this
            exact this hsl

theorem prophSem_eq_of_move (hc : EndsAfterCreation P π) (hc' : EndsAfterCreation P π')
    (hw' : EndsAfterLastWrite P π') (he : EndsByProgramEnd P π) (hle : ∀ i, π' i ≤ π i)
    (h : Heap) (φ : Nat → Int) : prophSem P π h φ = prophSem P π' h φ := by
  unfold prophSem translate
  exact move_main hc hc' hw' he hle φ P 0 _ _ (by simp) (fun j => by simp)
    ⟨rfl, rfl, rfl, by simp, fun i => by rw [refOf_zero]; rfl⟩

end Move

/-- `prophecy-sound-wider-window`, proved: clamp the placement to the lazy one, where the prophecy
encoding has the same runs, then use `prophecy-agreement` and `endpoint-window-last-write`. -/
theorem prophOutcome_iff_heapSem (P : Prog) (π : Placement) (h : Heap)
    (had : AliasingDiscipline P) (hc : EndsAfterCreation P π) (hw : EndsAfterLastWrite P π)
    (he : EndsByProgramEnd P π) :
    ∀ o, ProphOutcome P π h o ↔ heapSem P h = some o := by
  intro o
  let π' : Placement := fun i => min (π i) (lazyPlacement P i)
  have hle : ∀ i, π' i ≤ π i := fun i => Nat.min_le_left _ _
  have hc' : EndsAfterCreation P π' := fun i hi hr =>
    Nat.lt_min.mpr ⟨hc i hi hr, lazyPlacement_endsAfterCreation P i hi hr⟩
  have hw' : EndsAfterLastWrite P π' := fun i hi hr j hj hwr =>
    Nat.lt_min.mpr ⟨hw i hi hr j hj hwr,
      lazyPlacement_endsAfterLastUse_of_aliasingDiscipline had i hi hr j hj (usesAt_of_writesAt hwr)⟩
  have ho' : EndsByNextOwnerAccess P π' := fun i hi k hk hown =>
    Nat.le_trans (Nat.min_le_right _ _) (lazyPlacement_endsByNextOwnerAccess P i hi k hk hown)
  have he' : EndsByProgramEnd P π' := fun i hi hr => Nat.le_trans (hle i) (he i hi hr)
  have hmove : ProphOutcome P π h o ↔ ProphOutcome P π' h o := by
    unfold ProphOutcome
    constructor
    · rintro ⟨φ, hφ⟩; exact ⟨φ, by rw [← prophSem_eq_of_move hc hc' hw' he hle]; exact hφ⟩
    · rintro ⟨φ, hφ⟩; exact ⟨φ, by rw [prophSem_eq_of_move hc hc' hw' he hle]; exact hφ⟩
  rw [hmove, prophOutcome_iff_effSem P π' h ho' he' o,
    effSem_eq_heapSem P π' h hc' hw' ho' he' had]

end Toy.Backward.Sim
