import ToyProphecy.Sim.CalleeRun

/-!
# Proof infrastructure: simulation of the main program — definitions

In a main program with no lent access, no frozen access, no use after end and
fresh names, the live borrows with address `x` form one chain (top first) whose
bottom element (the root) borrowed `x` directly (`borrow` or the chosen lender
of `borrowSel`).

Auxiliary definitions and lemmas used only inside proofs of the main statements.
-/

namespace Toy.Prophecy
namespace Sim

open CState

def Live (c : CState) (k : RefVar) : Prop := c.status k = .active ∨ c.status k = .frozen

/-- `k` lends the local `w` directly (a borrow of `w`, or a selection with `w`
among its two candidates). -/
def LendsLoc (c : CState) (k : RefVar) (w : Var) : Prop :=
  c.lender k = some (.loc w) ∨ ∃ y z, c.lender k = some (.sel y z) ∧ (w = y ∨ w = z)

/-- The root `k` of the chain at address `x`. -/
def RootOK (c : CState) (sR : RState) (sB : BState) (sP : PState) (ch : Var → List RefVar)
    (x : Var) (k : RefVar) : Prop :=
  ∃ pk qk, sP.refs k = some pk ∧ sB.refs k = some qk ∧ sP.store x = pk.fin ∧
    ((c.lender k = some (.loc x) ∧ qk.back = fun v => [(.loc x, v)]) ∨
     (∃ (y z : Var) (b : Bool) (y0 z0 : Int), c.lender k = some (.sel y z) ∧
        x = (if b then y else z) ∧ qk.back = selBack b y z y0 z0 ∧
        ((if b then z else y) ≠ x →
          (if b then z0 else y0) = sR.store (if b then z else y) ∧ ch (if b then z else y) = [])))

structure MRel (c : CState) (sR : RState) (sB : BState) (sP : PState) (ch : Var → List RefVar) :
    Prop where
  stuck : c.stuck = false
  viol : c.viol = []
  brR : BRel c.status sR.refs
  brB : BRel c.status sB.refs
  brP : BRel c.status sP.refs
  nodup : ∀ x, (ch x).Nodup
  mem : ∀ k x, k ∈ ch x ↔ (Live c k ∧ sR.refs k = some x)
  head : ∀ x k rest, ch x = k :: rest → c.status k = .active ∧ (∀ p ∈ rest, c.status p = .frozen) ∧
    (∃ q, sB.refs k = some q ∧ q.cur = sR.store x) ∧ (∃ p, sP.refs k = some p ∧ p.cur = sR.store x)
  links : ∀ x, Links c sB sP (ch x)
  root : ∀ x k, (ch x).getLast? = some k → RootOK c sR sB sP ch x k
  free : ∀ x, ch x = [] → sB.store x = sR.store x ∧ sP.store x = sR.store x
  lendsLent : ∀ k w, Live c k → LendsLoc c k w → c.lent w = true
  lendsUniq : ∀ k1 k2 w, Live c k1 → Live c k2 → LendsLoc c k1 w → LendsLoc c k2 w → k1 = k2
  bound : ∀ k, c.status k ≠ .unborn → k ∈ c.bound

theorem MRel.active_head {c sR sB sP ch} (hM : MRel c sR sB sP ch) {k : RefVar}
    (hk : c.status k = .active) : ∃ x rest, sR.refs k = some x ∧ ch x = k :: rest := by
  obtain ⟨x, hx⟩ := bound_of hM.brR (by rw [hk]; simp : c.status k ≠ .unborn)
  have hm := (hM.mem k x).2 ⟨Or.inl hk, hx⟩
  cases h : ch x with
  | nil => rw [h] at hm; simp at hm
  | cons k0 rest =>
    refine ⟨x, rest, hx, ?_⟩
    rw [h] at hm
    rcases List.mem_cons.mp hm with h' | h'
    · rw [h', h]
    · have := (hM.head x k0 rest h).2.1 k h'
      rw [hk] at this; cases this

theorem getLast?_some_of_ne_nil {α : Type} : ∀ {l : List α}, l ≠ [] → ∃ k, l.getLast? = some k
  | [], h => absurd rfl h
  | [a], _ => ⟨a, rfl⟩
  | a :: b :: l, _ => by
      rw [List.getLast?_cons_cons]
      exact getLast?_some_of_ne_nil (by simp)

/-- A nonempty chain at `x` means `x` is lent. -/
theorem MRel.lent_of_ch {c sR sB sP ch} (hM : MRel c sR sB sP ch) {x : Var} (hx : ch x ≠ []) :
    c.lent x = true := by
  obtain ⟨k, hk⟩ := getLast?_some_of_ne_nil hx
  have hkm : k ∈ ch x := List.mem_of_getLast? hk
  have hlive := ((hM.mem k x).1 hkm).1
  obtain ⟨pk, qk, -, -, -, hroot⟩ := hM.root x k hk
  apply hM.lendsLent k x hlive
  rcases hroot with ⟨hl, -⟩ | ⟨y, z, b, -, -, hl, hxb, -⟩
  · exact Or.inl hl
  · refine Or.inr ⟨y, z, hl, ?_⟩
    cases b <;> simp at hxb <;> simp [hxb]

theorem rootOK_congr {c c' : CState} {sR sR' : RState} {sB sB' : BState} {sP sP' : PState}
    {ch ch' : Var → List RefVar} {x : Var} {k : RefVar}
    (h : RootOK c sR sB sP ch x k) (hl : c'.lender k = c.lender k)
    (hb : (sB'.refs k).map BRef.back = (sB.refs k).map BRef.back)
    (hf : (sP'.refs k).map PRef.fin = (sP.refs k).map PRef.fin)
    (hs : sP'.store x = sP.store x)
    (hn : ∀ n, LendsLoc c k n → ch n = [] → n ≠ x → sR'.store n = sR.store n ∧ ch' n = []) :
    RootOK c' sR' sB' sP' ch' x k := by
  obtain ⟨pk, qk, hpk, hqk, hfin, hroot⟩ := h
  obtain ⟨pk', hpk', hpk'f⟩ := map_eq_some_of hf hpk
  obtain ⟨qk', hqk', hqk'b⟩ := map_eq_some_of hb hqk
  refine ⟨pk', qk', hpk', hqk', by rw [hs, hfin, hpk'f], ?_⟩
  rcases hroot with ⟨h1, h2⟩ | ⟨y, z, b, y0, z0, h1, h2, h3, h4⟩
  · exact Or.inl ⟨hl.trans h1, hqk'b.trans h2⟩
  · refine Or.inr ⟨y, z, b, y0, z0, hl.trans h1, h2, hqk'b.trans h3, fun hne => ?_⟩
    obtain ⟨h5, h6⟩ := h4 hne
    have hlends : LendsLoc c k (if b then z else y) :=
      Or.inr ⟨y, z, h1, by cases b <;> simp⟩
    obtain ⟨h7, h8⟩ := hn _ hlends h6 hne
    exact ⟨by rw [h7]; exact h5, h8⟩

theorem mrel_init (σ : Store) :
    MRel CState.init (RState.init σ) (BState.init σ) (PState.init σ) (fun _ => []) where
  stuck := rfl
  viol := rfl
  brR := by intro k; simp [CState.init, RState.init]
  brB := by intro k; simp [CState.init, BState.init]
  brP := by intro k; simp [CState.init, PState.init]
  nodup := by simp
  mem := by intro k x; simp [Live, CState.init]
  head := by intro x k rest h; simp at h
  links := fun _ => trivial
  root := by intro x k h; simp at h
  free := by intro x _; simp [BState.init, RState.init, PState.init]
  lendsLent := by intro k w h; simp [Live, CState.init] at h
  lendsUniq := by intro k1 k2 w h; simp [Live, CState.init] at h
  bound := by intro k h; simp [CState.init] at h

/-! ## Main-program steps under the standard policy -/

theorem stepP_std_op (φ : Nat → Int) (i : Nat) (s : PState) (o : Op) :
    stepP ResPolicy.std φ i s (.op o) = stepOpP true (fun _ => true) φ s o := by
  simp only [stepP, earlyCs, ResPolicy.std, List.filterMap_nil, List.append_nil]
  cases stepOpP true (fun _ => true) φ s o <;> rfl

theorem stepP_std_call (φ : Nat → Int) (i : Nat) (s : PState) (t r : RefVar) (f : Callee) :
    stepP ResPolicy.std φ i s (.call t f r) =
      (s.refs r).bind fun q =>
        (calleeRunP true φ f q.cur (φ s.next) (s.next + 1)).bind fun fr =>
          (fr.refs f.ret).map fun ret =>
            { s with
              refs := fupd (fupd s.refs r (some { q with cur := φ s.next }))
                        t (some { cur := ret.cur, fin := ret.fin, done := false })
              next := fr.next
              cs := s.cs ++ fr.cs } := by
  simp only [stepP, earlyCs, ResPolicy.std, List.filterMap_nil, List.append_nil]
  cases s.refs r with
  | none => rfl
  | some q =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases calleeRunP true φ f q.cur (φ s.next) (s.next + 1) with
    | none => rfl
    | some fr =>
      simp only [Option.bind_some]
      cases fr.refs f.ret <;> rfl

/-! ## Statements: stuck checks and bound names -/

def Stmt.binds : Stmt → Option RefVar
  | .op o => o.binds
  | .call t _ _ => some t

theorem checkStmt_of_stuck {c : CState} (h : c.stuck = true) (st : Stmt) : checkStmt c st = c := by
  cases st with
  | op o => exact checkOp_of_stuck h o
  | call t f r => simp [checkStmt, h]

theorem checkStmts_of_stuck' {c : CState} (h : c.stuck = true) : ∀ P, checkStmts c P = c
  | [] => rfl
  | s :: ss => by simp only [checkStmts, checkStmt_of_stuck h]; exact checkStmts_of_stuck' h ss

theorem checkStmt_call_status_unborn {c : CState} {t r : RefVar} {f : Callee}
    (h : (checkStmt c (.call t f r)).stuck = false) (k : RefVar) :
    (checkStmt c (.call t f r)).status k = .unborn ↔ (c.status k = .unborn ∧ t ≠ k) := by
  have hc : c.stuck = false := by
    cases hc : c.stuck
    · rfl
    · simp [checkStmt, hc] at h
  have hus : (c.useRef r).stuck = false := by
    cases h' : (c.useRef r).stuck
    · rfl
    · simp [checkStmt, hc, h'] at h
  have hr : c.status r ≠ .unborn := by
    intro hr; rw [useRef_unborn hr] at hus; simp [CState.setStuck] at hus
  have hcf : (checkCallee f).stuck = false := by
    cases h' : (checkCallee f).stuck
    · rfl
    · simp [checkStmt, hc, hus, h', CState.setStuck] at h
  simp only [checkStmt, hc, hus, hcf, Bool.false_eq_true, ↓reduceIte]
  simp only [upd_apply, bindRef_status, (useRef_shape c r).status]
  by_cases hkt : k = t
  · subst hkt; simp
  · simp only [hkt, ite_false]
    split
    · simp [Ne.symm hkt]
    · simp only [upd_apply]
      by_cases hkr : k = r
      · subst hkr; simp [hr, Ne.symm hkt]
      · simp [hkr, Ne.symm hkt]

theorem stepR_call_refs {s s' : RState} {t r : RefVar} {f : Callee}
    (h : stepR s (.call t f r) = some s') (k : RefVar) :
    s'.refs k = none ↔ (s.refs k = none ∧ t ≠ k) := by
  simp only [stepR, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨a, ha, s1, -, b, -, rfl⟩ := h
  by_cases hk : k = t
  · subst hk; simp
  · simp [hk, Ne.symm hk]

theorem stepB_call_refs {s s' : BState} {t r : RefVar} {f : Callee}
    (h : stepB s (.call t f r) = some s') (k : RefVar) :
    s'.refs k = none ↔ (s.refs k = none ∧ t ≠ k) := by
  simp only [stepB, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨q, hq, cv, -, rfl⟩ := h
  by_cases hk : k = t
  · subst hk; simp
  · simp [hk, Ne.symm hk]

theorem stepP_call_refs {s s' : PState} {φ : Nat → Int} {i : Nat} {t r : RefVar} {f : Callee}
    (h : stepP ResPolicy.std φ i s (.call t f r) = some s') (k : RefVar) :
    s'.refs k = none ↔ (s.refs k = none ∧ t ≠ k) := by
  rw [stepP_std_call] at h
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨q, hq, fr, -, ret, -, rfl⟩ := h
  by_cases hk : k = t
  · subst hk; simp
  · by_cases hkr : k = r
    · subst hkr; simp [hk, hq, Ne.symm hk]
    · simp [hk, hkr, Ne.symm hk]

theorem runR_none_of_stuck : ∀ {c : CState} {s : RState} {P : Prog},
    BRel c.status s.refs → c.stuck = false → (checkStmts c P).stuck = true → runR s P = none
  | c, s, [], _, hc, h => by simp [checkStmts, hc] at h
  | c, s, st :: P, hb, hc, h => by
      simp only [checkStmts] at h
      simp only [runR]
      by_cases h1 : (checkStmt c st).stuck = true
      · cases st with
        | op o => simp [stepR, stepOpR_none hb (checkOp_stuck hc h1)]
        | call t f r =>
          simp only [stepR, Option.bind_eq_bind]
          cases hr : s.refs r with
          | none => rfl
          | some a =>
            simp only [Option.bind_some]
            have hus : (c.useRef r).stuck = false := by
              rw [useRef_stuck_iff]; simp only [hc, Bool.false_or, decide_eq_false_iff_not]; exact fun h => by rw [(hb r).1 h] at hr; cases hr
            have hcf : (checkCallee f).stuck = true := by
              cases h' : (checkCallee f).stuck
              · simp [checkStmt, hc, hus, h'] at h1
                -- the remaining step is not stuck
                exact absurd h1 (by
                  simp only [bindRef_stuck]; simp)
              · rfl
            cases hs1 : runOpsR false { store := s.store, refs := calleeRefsR a } f.body with
            | none => rfl
            | some s1 =>
              simp only [Option.bind_some, calleeR_stuck hcf s.store a s1 hs1]
              rfl
      · have h1' : (checkStmt c st).stuck = false := by simpa using h1
        cases hst : stepR s st with
        | none => rfl
        | some s' =>
          simp only [Option.bind_some]
          apply runR_none_of_stuck _ h1' h
          intro k
          cases st with
          | op o => exact brel_step hb h1' (stepOpR_refs hst) k
          | call t f r =>
            rw [checkStmt_call_status_unborn h1' k, stepR_call_refs hst k, hb k]

theorem runB_none_of_stuck : ∀ {c : CState} {s : BState} {P : Prog},
    BRel c.status s.refs → c.stuck = false → (checkStmts c P).stuck = true → runB s P = none
  | c, s, [], _, hc, h => by simp [checkStmts, hc] at h
  | c, s, st :: P, hb, hc, h => by
      simp only [checkStmts] at h
      simp only [runB]
      by_cases h1 : (checkStmt c st).stuck = true
      · cases st with
        | op o => simp [stepB, stepOpB_none hb (checkOp_stuck hc h1)]
        | call t f r =>
          simp only [stepB, Option.bind_eq_bind]
          cases hr : s.refs r with
          | none => rfl
          | some q =>
            simp only [Option.bind_some]
            have hus : (c.useRef r).stuck = false := by
              rw [useRef_stuck_iff]; simp only [hc, Bool.false_or, decide_eq_false_iff_not]; exact fun h => by rw [(hb r).1 h] at hr; cases hr
            have hcf : (checkCallee f).stuck = true := by
              cases h' : (checkCallee f).stuck
              · simp [checkStmt, hc, hus, h'] at h1
                exact absurd h1 (by simp only [bindRef_stuck]; simp)
              · rfl
            simp [calleeB_stuck hcf q.cur]
      · have h1' : (checkStmt c st).stuck = false := by simpa using h1
        cases hst : stepB s st with
        | none => rfl
        | some s' =>
          simp only [Option.bind_some]
          apply runB_none_of_stuck _ h1' h
          intro k
          cases st with
          | op o => exact brel_step hb h1' (stepOpB_refs hst) k
          | call t f r =>
            rw [checkStmt_call_status_unborn h1' k, stepB_call_refs hst k, hb k]

theorem runP_none_of_stuck {φ : Nat → Int} : ∀ {c : CState} {s : PState} {P : Prog} {i : Nat},
    BRel c.status s.refs → c.stuck = false → (checkStmts c P).stuck = true →
      runP ResPolicy.std φ i s P = none
  | c, s, [], _, _, hc, h => by simp [checkStmts, hc] at h
  | c, s, st :: P, i, hb, hc, h => by
      simp only [checkStmts] at h
      simp only [runP]
      by_cases h1 : (checkStmt c st).stuck = true
      · cases st with
        | op o => simp [stepP_std_op, stepOpP_none hb _ φ (checkOp_stuck hc h1)]
        | call t f r =>
          rw [stepP_std_call]
          cases hr : s.refs r with
          | none => rfl
          | some q =>
            simp only [Option.bind_some]
            have hus : (c.useRef r).stuck = false := by
              rw [useRef_stuck_iff]; simp only [hc, Bool.false_or, decide_eq_false_iff_not]; exact fun h => by rw [(hb r).1 h] at hr; cases hr
            have hcf : (checkCallee f).stuck = true := by
              cases h' : (checkCallee f).stuck
              · simp [checkStmt, hc, hus, h'] at h1
                exact absurd h1 (by simp only [bindRef_stuck]; simp)
              · rfl
            cases hfr : calleeRunP true φ f q.cur (φ s.next) (s.next + 1) with
            | none => rfl
            | some fr =>
              simp [calleeP_stuck hcf true φ q.cur (φ s.next) (s.next + 1) fr hfr]
      · have h1' : (checkStmt c st).stuck = false := by simpa using h1
        cases hst : stepP ResPolicy.std φ i s st with
        | none => rfl
        | some s' =>
          simp only [Option.bind_some]
          apply runP_none_of_stuck _ h1' h
          intro k
          cases st with
          | op o =>
            rw [stepP_std_op] at hst
            exact brel_step hb h1' (stepOpP_refs hst) k
          | call t f r =>
            rw [checkStmt_call_status_unborn h1' k, stepP_call_refs hst k, hb k]

/-! ## Violations of whole programs -/

theorem checkStmt_viol (c : CState) (st : Stmt) :
    ∃ l, (checkStmt c st).viol = c.viol ++ l ∧ ∀ v ∈ l, v ≠ .unendedAtExit := by
  cases st with
  | op o =>
      obtain ⟨l, hl, hv⟩ := checkOp_viol true c o
      exact ⟨l, hl, fun v h => (hv v h).1⟩
  | call t f r =>
      by_cases hc : c.stuck = true
      · exact ⟨[], by simp [checkStmt, hc], by simp⟩
      have hc' : c.stuck = false := by simpa using hc
      obtain ⟨l1, hl1, hv1⟩ := useRef_viol c r
      simp only [checkStmt, hc', Bool.false_eq_true, ↓reduceIte]
      split
      · exact ⟨l1, hl1, fun v h => by rcases hv1 v h with rfl | rfl <;> simp⟩
      · split
        · exact ⟨l1, by simp [CState.setStuck, hl1], fun v h => by rcases hv1 v h with rfl | rfl <;> simp⟩
        · obtain ⟨l2, hl2, hv2⟩ :=
            bindRef_viol { c.useRef r with viol := (c.useRef r).viol ++ (checkCallee f).viol } t
          refine ⟨l1 ++ (checkCallee f).viol ++ l2, ?_, ?_⟩
          · simp only [hl2]; simp [hl1]
          · intro v h
            rcases List.mem_append.mp h with h | h
            · rcases List.mem_append.mp h with h | h
              · rcases hv1 v h with rfl | rfl <;> simp
              · exact (checkCallee_viol f v h).1
            · rcases hv2 v h with rfl; simp

theorem checkStmts_viol : ∀ (c : CState) (P : Prog),
    ∃ l, (checkStmts c P).viol = c.viol ++ l ∧ ∀ v ∈ l, v ≠ .unendedAtExit
  | c, [] => ⟨[], by simp [checkStmts], by simp⟩
  | c, st :: P => by
      obtain ⟨l1, h1, hv1⟩ := checkStmt_viol c st
      obtain ⟨l2, h2, hv2⟩ := checkStmts_viol (checkStmt c st) P
      refine ⟨l1 ++ l2, by simp [checkStmts, h2, h1], ?_⟩
      intro v h; rcases List.mem_append.mp h with h | h
      · exact hv1 v h
      · exact hv2 v h

theorem viol_nil_of_discipline {P : Prog} (hL : NoLentAccess P) (hF : NoFrozenAccess P)
    (hE : NoUseAfterEnd P) (hB : FreshBindings P) : (checkStmts CState.init P).viol = [] := by
  obtain ⟨l, hl, hv⟩ := checkStmts_viol CState.init P
  have hl' : (checkStmts CState.init P).viol = l := by simpa [CState.init] using hl
  have sub : ∀ v ∈ (checkStmts CState.init P).viol, v ∈ violations P := by
    intro v h
    simp only [violations]
    split
    · exact List.mem_append_left _ h
    · exact h
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro v h
  have hv' := hv v (hl' ▸ h)
  have hm := sub v h
  cases v with
  | lentAccess => exact hL hm
  | frozenAccess => exact hF hm
  | useAfterEnd => exact hE hm
  | rebind => exact hB hm
  | unendedAtExit => exact hv' rfl

theorem checkStmt_not_stuck_of_checkStmts {c : CState} {st : Stmt} {P : Prog}
    (h : (checkStmts (checkStmt c st) P).stuck = false) : (checkStmt c st).stuck = false := by
  cases hc : (checkStmt c st).stuck
  · rfl
  · rw [checkStmts_of_stuck' hc] at h; simp [hc] at h

theorem viol_nil_of_checkStmts {c : CState} {st : Stmt} {P : Prog}
    (h : (checkStmts (checkStmt c st) P).viol = []) : (checkStmt c st).viol = [] := by
  obtain ⟨l, hl, -⟩ := checkStmts_viol (checkStmt c st) P
  rw [hl] at h
  exact (List.append_eq_nil_iff.mp h).1

end Sim
end Toy.Prophecy
