import Toy.PlaceEval.MarkerRevRel

/-!
# Storage-marker erasure, reverse direction: the simulation

The source is a run of `eraseMarkers P x`, the target a run of `P` that never reaches UB (this
is where `UBFree .fresh P` is used). The target's marker steps for `x` are silent and matched by
no source step; every other target step is matched by the same statement or terminator in the
source, which may reach UB instead (a source UB is allowed by refinement). The source's
allocations are placed at the target's addresses shifted by `D`, and `x` at `X0` for the whole
run.
-/

namespace Toy.PlaceEval

/-- Statements whose right-hand sides observe no address and whose constants satisfy `J`. -/
def StmtOK2 (J : Ptr → Prop) : Stmt → Prop
  | .assign _ _ rv => RvOK2 J rv
  | .emit rv => RvOK2 J rv
  | _ => True

/-- Terminators whose constants satisfy `J`. -/
def TermOK2 (J : Ptr → Prop) : Term → Prop
  | .switchInt o _ _ => OpOK2 J o
  | _ => True

/-- Every statement and terminator of `P` satisfies `StmtOK2`/`TermOK2`. -/
def ProgOK2 (J : Ptr → Prop) (P : Prog) : Prop :=
  ∀ b ∈ P.blocks, (∀ s ∈ b.stmts, StmtOK2 J s) ∧ TermOK2 J b.term

theorem ProgOK2.blk {J : Ptr → Prop} {P : Prog} (h : ProgOK2 J P) (l : Label) :
    (∀ s ∈ (P.blk l).stmts, StmtOK2 J s) ∧ TermOK2 J (P.blk l).term := by
  by_cases hl : l < P.blocks.length
  · rw [blk_eq_getElem hl]
    exact h _ (List.getElem_mem hl)
  · have : P.blk l = Block.unreach := by
      simp [Prog.blk, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
    rw [this]
    exact ⟨fun s hs => by simp [Block.unreach] at hs, trivial⟩

section Exec2

variable {P : Prog} {x : Local} {D X0 A : Nat} {g : Nat → Option (Nat × Nat × Nat)}

theorem SRel2.exec_noalloc {σ τ : State} (h : SRel2 P x D X0 A g σ τ) {s : Stmt}
    (hs : NoAllocStmt s) (hok : StmtOK2 (JA A) s) (mS mT : AllocMode) (P1 P2 : Prog)
    {ev ev' : Option Nat} {σ' τ' : State} (h1 : execStmt mS P1 σ s = .ok ev σ')
    (h2 : execStmt mT P2 τ s = .ok ev' τ') :
    ev = ev' ∧ SRel2 P x D X0 A g σ' τ' ∧ σ'.frame = σ.frame := by
  have hJ : ∀ a, JA A ⟨none, a⟩ := fun _ => Or.inl rfl
  have hfr := h.frRel2
  cases s with
  | placeMention p =>
    simp only [execStmt] at h1 h2
    split at h1
    · split at h2
      · cases h1; cases h2; exact ⟨rfl, h, rfl⟩
      · cases h2
    · cases h1
  | assign dst τ0 rv =>
    simp only [execStmt] at h1 h2
    cases e1 : evalPlace σ dst with
    | none => simp only [e1] at h1; cases h1
    | some q =>
      cases e2 : evalPlace τ dst with
      | none => simp only [e2] at h2; cases h2
      | some q' =>
        have hq := evalPlace_transfer2 hJ h.mem hfr dst e1 e2
        cases v1 : rv.eval σ with
        | none => simp only [e1, v1] at h1; cases h1
        | some v =>
          cases v2 : rv.eval τ with
          | none => simp only [e2, v2] at h2; cases h2
          | some w =>
            have hv := rvalue_transfer2 hJ h.mem hfr hok v1 v2
            cases m1 : σ.mem.store q τ0 v with
            | none => simp only [e1, v1, m1] at h1; cases h1
            | some m =>
              cases m2 : τ.mem.store q' τ0 w with
              | none => simp only [e2, v2, m2] at h2; cases h2
              | some n =>
                simp only [e1, v1, m1, StmtResult.ok.injEq] at h1
                simp only [e2, v2, m2, StmtResult.ok.injEq] at h2
                obtain ⟨rfl, rfl⟩ := h1
                obtain ⟨rfl, rfl⟩ := h2
                obtain ⟨hmn, hma, hna⟩ := store_transfer2 h.mem hq hv m1 m2
                exact ⟨rfl, h.with_mem hmn hma hna, rfl⟩
  | emit rv =>
    simp only [execStmt] at h1 h2
    cases v1 : rv.eval σ with
    | none => simp only [v1] at h1; cases h1
    | some v =>
      cases v2 : rv.eval τ with
      | none => simp only [v2] at h2; cases h2
      | some w =>
        have hv := rvalue_transfer2 hJ h.mem hfr hok v1 v2
        simp only [v1] at h1; simp only [v2] at h2
        cases v with
        | ptr _ => cases h1
        | int n =>
          cases w with
          | ptr _ => cases h2
          | int n' =>
            simp only [StmtResult.ok.injEq] at h1 h2
            obtain ⟨rfl, rfl⟩ := h1
            obtain ⟨rfl, rfl⟩ := h2
            simp only [VV2] at hv
            exact ⟨by rw [hv], h, rfl⟩
  | storageLive _ => exact absurd hs id
  | storageDead _ => exact absurd hs id

end Exec2

/-- A reachable configuration of a program that is UB-free under fresh addresses does not step
to UB. -/
theorem step_ne_ub_of_reach {ω : Nat → Nat} {P : Prog} {st0 : State}
    (h0 : P.initState (.fresh ω) = some st0) (hub : UBFree .fresh P) {c : Cfg}
    (hr : Reach (.fresh ω) P (P.entry 0 st0) c) : step (.fresh ω) P c ≠ .ub := by
  intro hs
  obtain ⟨n, t, hn⟩ := hr
  have : run (.fresh ω) P (n + 1) (P.entry 0 st0) = .ub t := by
    rw [run_add_running n 1 _ c t hn, run_succ_ub 0 hs]; simp [Outcome.app]
  exact hub t ⟨ω, st0, h0, n + 1, this⟩

/-- The largest number of statements in a block of `P`. -/
def maxBlk (P : Prog) : Nat := (P.blocks.map fun b => b.stmts.length).foldr max 0

theorem le_foldr_max {l : List Nat} {a : Nat} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h'
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h') (Nat.le_max_right _ _)

theorem blk_length_le (P : Prog) (l : Label) : (P.blk l).stmts.length ≤ maxBlk P := by
  by_cases hl : l < P.blocks.length
  · rw [blk_eq_getElem hl]
    exact le_foldr_max (List.mem_map.2 ⟨_, List.getElem_mem hl, rfl⟩)
  · have : P.blk l = Block.unreach := by
      simp [Prog.blk, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
    rw [this]; simp [Block.unreach]

/-- The configuration relation of the reverse simulation. -/
def CRel2 (P : Prog) (x : Local) (D X0 A : Nat) (ωs : Nat → Nat) (c0 : Cfg) (cs ct : Cfg) :
    Prop :=
  cs.lbl = ct.lbl ∧ cs.rest = eraseStmts x ct.rest ∧ ct.rest <:+ (P.blk ct.lbl).stmts ∧
    Reach (.fresh ωs) P c0 ct ∧ (x < P.locals.length → cs.st.allocOf x ≠ none) ∧
    ∃ g, SRel2 P x D X0 A g cs.st ct.st

section Sim2

variable {P : Prog} {x : Local} {D X0 A : Nat} {ωs : Nat → Nat} {st0 : State}

theorem crel2_entry {σ τ : State} {g : Nat → Option (Nat × Nat × Nat)}
    (h : SRel2 P x D X0 A g σ τ) (hxs : x < P.locals.length → σ.allocOf x ≠ none) (b : Label)
    (hr : Reach (.fresh ωs) P (P.entry 0 st0) (P.entry b τ)) :
    CRel2 P x D X0 A ωs (P.entry 0 st0) ((eraseMarkers P x).entry b σ) (P.entry b τ) :=
  ⟨rfl, by simp [Prog.entry, eraseMarkers_blk], List.suffix_refl _, hr, hxs, g, h⟩

theorem fresh_alloc_pos {P : Prog} (hwf : ∀ y, 0 < (P.layout y).align) (y : Local) (w : Nat) :
    0 < (P.layout y).align * (w + 1) :=
  Nat.mul_pos (hwf y) (Nat.succ_pos _)

theorem crel2_lstep (h0 : P.initState (.fresh ωs) = some st0) (hub : UBFree .fresh P)
    (hAD : A < D) (hXD : X0 + (P.layout x).size ≤ D + 1) (hwf : ∀ y, 0 < (P.layout y).align)
    (hdvd : ∀ y, (P.layout y).align ∣ D) (hok : ProgOK2 (JA A) P) :
    ∀ cs ct, CRel2 P x D X0 A ωs (P.entry 0 st0) cs ct →
      LStepSim .fresh (eraseMarkers P x) (.fresh ωs) P (CRel2 P x D X0 A ωs (P.entry 0 st0))
        (fun c => c.rest.length) cs ct := by
  rintro ⟨l', rs', σ⟩ ⟨l, rt, τ⟩ ⟨hl, hr, hsuf, hreach, hxs, g, h⟩
  simp only at hl hr hsuf hreach hxs h
  subst hl; subst hr
  have hnub := step_ne_ub_of_reach h0 hub hreach
  have hJ : ∀ a, JA A ⟨none, a⟩ := fun _ => Or.inl rfl
  have hreach' : ∀ ev ct', step (.fresh ωs) P ⟨l', rt, τ⟩ = .next ev ct' →
      Reach (.fresh ωs) P (P.entry 0 st0) ct' := by
    intro ev ct' hs
    obtain ⟨n, t, hn⟩ := hreach
    exact ⟨n + 1, _, run_succ_of_running hn hs⟩
  unfold LStepSim
  cases rt with
  | nil =>
    have hterm : ((eraseMarkers P x).blk l').term = (P.blk l').term := by rw [eraseMarkers_blk]
    have htok := (hok.blk l').2
    have hs : ∀ (Q : Prog) (mode : AllocMode) (st : State), step mode Q ⟨l', [], st⟩ =
        match (Q.blk l').term with
        | .goto b => .next none (Q.entry b st)
        | .switchInt o arms ow =>
          match o.evalInt st with
          | some n => .next none (Q.entry (selectTarget arms ow n) st)
          | none => .ub
        | .halt => .halt st
        | .unreachable => .ub := fun _ _ _ => rfl
    have hsT := hs (eraseMarkers P x) (.fresh fun _ => 0) σ
    rw [hterm] at hsT
    have hsP := hs P (.fresh ωs) τ
    simp only [eraseStmts, List.filter_nil, Sem.mode]
    rw [hsP]
    rw [hsP] at hnub hreach'
    cases ht : (P.blk l').term with
    | goto b =>
      rw [ht] at hsT hreach'
      dsimp only at hsT hreach' ⊢
      refine Or.inr ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
      cases hst
      exact Or.inl ⟨fun _ => 0, 0, _, run_one_next hsT,
        crel2_entry h hxs b (hreach' none _ rfl)⟩
    | switchInt o arms ow =>
      rw [ht] at hsT hreach' hnub htok
      dsimp only at hsT hreach' hnub ⊢
      cases hv : o.evalInt τ with
      | none => rw [hv] at hnub; exact absurd rfl hnub
      | some n =>
        rw [hv] at hreach'
        dsimp only at hreach' ⊢
        cases hvS : o.evalInt σ with
        | none =>
          rw [hvS] at hsT
          exact Or.inl ⟨fun _ => 0, 1, run_succ_ub 0 hsT⟩
        | some n' =>
          rw [hvS] at hsT
          have := evalInt_transfer2 hJ h.mem h.frRel2 htok hvS hv
          subst this
          refine Or.inr ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
          cases hst
          exact Or.inl ⟨fun _ => 0, 0, _, run_one_next hsT,
            crel2_entry h hxs _ (hreach' none _ rfl)⟩
    | halt =>
      rw [ht] at hsT
      dsimp only at hsT ⊢
      exact Or.inr ⟨(fun _ _ h => by cases h), fun st hst => ⟨fun _ => 0, 1, σ, run_succ_halt 0 hsT⟩,
        (fun h => by cases h)⟩
    | unreachable =>
      rw [ht] at hnub
      exact absurd rfl hnub
  | cons s rs =>
    have hsuf' : rs <:+ (P.blk l').stmts := List.IsSuffix.trans (List.suffix_cons s rs) hsuf
    have hsok := (hok.blk l').1 s (hsuf.subset List.mem_cons_self)
    cases hm : s.isMarkerOf x with
    | true =>
      rw [eraseStmts_cons_marker rs hm]
      refine Or.inr ⟨fun ev ct' hst => ?_, (fun st hst => ?_), hnub⟩
      · cases s with
        | storageLive y =>
          have hy : y = x := by simpa [Stmt.isMarkerOf] using hm
          subst hy
          cases he : execStmt (.fresh ωs) P τ (.storageLive y) with
          | ok ev0 τ' =>
            rw [step_cons_ok he] at hst
            cases hst
            have he0 := he
            simp only [execStmt] at he
            split at he
            · rename_i τ2 ha
              cases he
              rw [allocate_fresh] at ha
              split at ha
              · rename_i htc
                cases ha
                have h1 := h.deallocate_tgt_x
                have hcT : ∀ (k : Nat) (al : Alloc), (deallocate τ y).mem.allocs[k]? = some al →
                    al.live = true → disjointRanges ((P.layout y).align *
                      (ωs (deallocate τ y).mem.allocs.length + 1)) (P.layout y).size al.base
                      al.size = true := by
                  intro k al hal' hl
                  have := List.all_eq_true.1 htc al (List.mem_of_getElem? hal')
                  simpa [hl] using this
                obtain ⟨g', h2⟩ := h1.alloc_tgt_x hxs
                  (by rw [deallocate_allocOf, ite_pos' rfl]) _ (fresh_alloc_pos hwf _ _) hcT
                exact Or.inr ⟨rfl, by simp, rfl, by simp, hsuf', hreach' _ _ (step_cons_ok he0), hxs, g', h2⟩
              · cases ha
            · cases he
          | ub => rw [step_cons_ub he] at hst; cases hst
          | block => rw [step_cons_block he] at hst; cases hst
        | storageDead y =>
          have hy : y = x := by simpa [Stmt.isMarkerOf] using hm
          subst hy
          have he : execStmt (.fresh ωs) P τ (.storageDead y) = .ok none (deallocate τ y) := rfl
          rw [step_cons_ok he] at hst
          cases hst
          exact Or.inr ⟨rfl, by simp, rfl, by simp, hsuf', hreach' _ _ (step_cons_ok he), hxs, g,
            h.deallocate_tgt_x⟩
        | _ => simp [Stmt.isMarkerOf] at hm
      · cases s with
        | storageLive _ =>
          simp only [step] at hst; split at hst <;> cases hst
        | storageDead _ =>
          simp only [step] at hst; split at hst <;> cases hst
        | _ => simp [Stmt.isMarkerOf] at hm
    | false =>
      rw [eraseStmts_cons_other rs hm]
      cases s with
      | storageLive y =>
        have hy : y ≠ x := by simpa [Stmt.isMarkerOf] using hm
        cases he : execStmt (.fresh ωs) P τ (.storageLive y) with
        | ok ev0 τ' =>
          rw [step_cons_ok he]
          refine Or.inr ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
          cases hst
          have he0 := he
          simp only [execStmt] at he
          split at he
          · rename_i τ2 ha
            cases he
            rw [allocate_fresh] at ha
            split at ha
            · rename_i htc
              cases ha
              have h1 := h.deallocate_both hy
              have hcT : ∀ (k : Nat) (al : Alloc), (deallocate τ y).mem.allocs[k]? = some al →
                  al.live = true → disjointRanges ((P.layout y).align *
                    (ωs (deallocate τ y).mem.allocs.length + 1)) (P.layout y).size al.base
                    al.size = true := by
                intro k al hal' hl
                have := List.all_eq_true.1 htc al (List.mem_of_getElem? hal')
                simpa [hl] using this
              obtain ⟨hcS, h2⟩ := h1.alloc_both hy (P.layout y) _ hAD hXD (fresh_alloc_pos hwf _ _) hcT
              have hlay : (eraseMarkers P x).layout y = P.layout y := rfl
              have hsrc : execStmt (.fresh fun _ => ωs (deallocate τ y).mem.allocs.length +
                  D / (P.layout y).align) (eraseMarkers P x) σ (.storageLive y) =
                  .ok none (allocState (deallocate σ y) y (P.layout y)
                    ((P.layout y).align * (ωs (deallocate τ y).mem.allocs.length + 1) + D)) := by
                have hchk : ((deallocate σ y).mem.allocs.all fun al => !al.live ||
                    disjointRanges ((P.layout y).align * (ωs (deallocate τ y).mem.allocs.length + 1) + D)
                      (P.layout y).size al.base al.size) = true := by
                  rw [List.all_eq_true]
                  intro al hal
                  obtain ⟨j, hj, hjal⟩ := List.getElem_of_mem hal
                  have e : (deallocate σ y).mem.allocs[j]? = some al := by
                    rw [List.getElem?_eq_getElem hj, hjal]
                  cases hl : al.live with
                  | false => rfl
                  | true => simpa using hcS j al e hl
                simp only [execStmt, hlay, allocate_fresh, addr_shift (hdvd y), hchk, ↓reduceIte]
              refine Or.inl ⟨_, 0, _, run_one_next (step_cons_ok hsrc), rfl, rfl, hsuf',
                hreach' _ _ (step_cons_ok he0), ?_, _, h2⟩
              intro hxl
              simp only
              rw [allocState_allocOf, ite_neg' (fun hc => hy hc.1), deallocate_allocOf,
                ite_neg' (Ne.symm hy)]
              exact hxs hxl
            · cases ha
          · cases he
        | ub => rw [step_cons_ub he] at hnub; exact absurd rfl hnub
        | block =>
          rw [step_cons_block he]
          exact Or.inr ⟨(fun _ _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h)⟩
      | storageDead y =>
        have hy : y ≠ x := by simpa [Stmt.isMarkerOf] using hm
        have he : ∀ (mode : AllocMode) (Q : Prog) (st : State),
            execStmt mode Q st (.storageDead y) = .ok none (deallocate st y) := fun _ _ _ => rfl
        rw [step_cons_ok (he _ _ _)]
        refine Or.inr ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
        cases hst
        refine Or.inl ⟨fun _ => 0, 0, _, run_one_next (step_cons_ok (he _ _ _)), rfl, rfl, hsuf',
          hreach' _ _ (step_cons_ok (he _ _ _)), ?_, g, h.deallocate_both hy⟩
        intro hxl
        simp only
        rw [deallocate_allocOf, ite_neg' (Ne.symm hy)]
        exact hxs hxl
      | _ =>
        cases heS : execStmt (.fresh fun _ => 0) (eraseMarkers P x) σ _ with
        | ub => exact Or.inl ⟨fun _ => 0, 1, run_succ_ub 0 (step_cons_ub heS)⟩
        | block => exact absurd heS (execStmt_noalloc_ne_block (by exact trivial))
        | ok evS σ' =>
          cases he : execStmt (.fresh ωs) P τ _ with
          | ok ev0 τ' =>
            rw [step_cons_ok he]
            refine Or.inr ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
            cases hst
            obtain ⟨hev, h2, hfr⟩ := h.exec_noalloc (by exact trivial) hsok _ _ _ _ heS he
            subst hev
            refine Or.inl ⟨fun _ => 0, 0, _, run_one_next (step_cons_ok heS), rfl, rfl, hsuf',
              hreach' _ _ (step_cons_ok he), ?_, g, h2⟩
            intro hxl
            simp only [State.allocOf, hfr]
            exact hxs hxl
          | ub => rw [step_cons_ub he] at hnub; exact absurd rfl hnub
          | block => exact absurd he (execStmt_noalloc_ne_block (by exact trivial))

end Sim2

end Toy.PlaceEval

namespace Toy.PlaceEval

section Entry2

variable {P : Prog} {x : Local} {D X0 A : Nat} {ωs : Nat → Nat}

theorem entry_aux2 (hAD : A < D) (hXD : X0 + (P.layout x).size ≤ D + 1) (hAX : A < X0)
    (hX0 : X0 = (P.layout x).align * (A + 1)) (hwf : ∀ y, 0 < (P.layout y).align)
    (hdvd : ∀ y, (P.layout y).align ∣ D) (hmk : P.hasMarkers x = true) :
    ∀ (xs : List Local) (σ τ τ' : State) (g : Nat → Option (Nat × Nat × Nat)), xs.Nodup →
      SRel2 P x D X0 A g σ τ → (x ∈ xs → σ.allocOf x = none ∧ x < P.locals.length) →
      (x ∉ xs → x < P.locals.length → σ.allocOf x ≠ none) → τ.allocOf x = none →
      allocEntry (.fresh ωs) P xs τ = some τ' →
      ∃ ω0 σ' g', allocEntry (.fresh ω0) (eraseMarkers P x) xs σ = some σ' ∧
        SRel2 P x D X0 A g' σ' τ' ∧ (x < P.locals.length → σ'.allocOf x ≠ none)
  | [], σ, τ, τ', g, _, h, _, hx, _, ht => by
    cases ht
    exact ⟨fun _ => 0, σ, g, rfl, h, hx (by simp)⟩
  | z :: zs, σ, τ, τ', g, hnd, h, hxin, hx, htx, ht => by
    rw [List.nodup_cons] at hnd
    simp only [allocEntry] at ht
    by_cases hzx : z = x
    · have hxz : x = z := hzx.symm
      subst hxz
      rw [ite_pos' hmk] at ht
      obtain ⟨hsx, hxl⟩ := hxin List.mem_cons_self
      obtain ⟨hcS, h1⟩ := h.alloc_src_x hxl hsx htx hAX hXD
      have hxs1 : (allocState σ x (P.layout x) X0).allocOf x ≠ none := by
        rw [allocState_allocOf, ite_pos' ⟨rfl, h.slen ▸ hxl⟩]; simp
      obtain ⟨ω2, σ', g', h2, h3, h4⟩ := entry_aux2 hAD hXD hAX hX0 hwf hdvd hmk zs _ τ τ' g hnd.2 h1
        (fun hm => absurd hm hnd.1) (fun _ _ => hxs1) htx ht
      refine ⟨ocomb (σ.mem.allocs.length + 1) (fun _ => A) ω2, σ', g', ?_, h3, h4⟩
      simp only [allocEntry, eraseMarkers_hasMarkers_self, Bool.false_eq_true, ↓reduceIte]
      have hchk : (σ.mem.allocs.all fun al => !al.live ||
          disjointRanges X0 (P.layout x).size al.base al.size) = true := by
        rw [List.all_eq_true]
        intro al hal
        obtain ⟨j, hj, hjal⟩ := List.getElem_of_mem hal
        have e : σ.mem.allocs[j]? = some al := by rw [List.getElem?_eq_getElem hj, hjal]
        cases hl : al.live with
        | false => rfl
        | true => simpa using hcS j al e hl
      have hlay : (eraseMarkers P x).layout x = P.layout x := rfl
      have hc : allocate (.fresh (ocomb (σ.mem.allocs.length + 1) (fun _ => A) ω2)) σ x (P.layout x) =
          allocate (.fresh fun _ => A) σ x (P.layout x) :=
        allocate_mode_congr (Ss := .fresh) σ x _ (by simp [ocomb])
      rw [hlay, hc]
      simp only [allocate_fresh, ← hX0, hchk, ↓reduceIte, Option.bind_some]
      have hge : ∀ k, (allocState σ x (P.layout x) X0).mem.allocs.length ≤ k →
          ocomb (σ.mem.allocs.length + 1) (fun _ => A) ω2 k = ω2 k := fun k hk => by
        rw [allocState_length] at hk
        simp only [ocomb]; rw [ite_neg' (by omega)]
      exact (allocEntry_local_ge (Ss := .fresh) zs _ hge).trans h2
    · have hxin' : x ∈ zs → σ.allocOf x = none ∧ x < P.locals.length :=
        fun hm => hxin (List.mem_cons_of_mem _ hm)
      have hx' : x ∉ zs → x < P.locals.length → σ.allocOf x ≠ none :=
        fun hm => hx (by simp [Ne.symm hzx, hm])
      by_cases hzm : P.hasMarkers z = true
      · rw [ite_pos' hzm] at ht
        obtain ⟨ω0, σ', g', h1, h2, h3⟩ := entry_aux2 hAD hXD hAX hX0 hwf hdvd hmk zs σ τ τ' g hnd.2
          h hxin' hx' htx ht
        refine ⟨ω0, σ', g', ?_, h2, h3⟩
        simp only [allocEntry, eraseMarkers_hasMarkers_ne P hzx, hzm, ↓reduceIte]
        exact h1
      · have hzm' : P.hasMarkers z = false := by simpa using hzm
        rw [ite_neg' hzm] at ht
        cases ha : allocate (.fresh ωs) τ z (P.layout z) with
        | none => rw [ha] at ht; cases ht
        | some τ1 =>
          rw [ha] at ht
          simp only [Option.bind_some] at ht
          rw [allocate_fresh] at ha
          split at ha
          · rename_i htc
            cases ha
            have hcT : ∀ (k : Nat) (al : Alloc), τ.mem.allocs[k]? = some al →
                al.live = true → disjointRanges ((P.layout z).align *
                  (ωs τ.mem.allocs.length + 1)) (P.layout z).size al.base al.size = true := by
              intro k al hal' hl
              have := List.all_eq_true.1 htc al (List.mem_of_getElem? hal')
              simpa [hl] using this
            obtain ⟨hcS, h1⟩ := h.alloc_both hzx (P.layout z) _ hAD hXD (fresh_alloc_pos hwf _ _) hcT
            obtain ⟨ω2, σ', g', h2, h3, h4⟩ := entry_aux2 hAD hXD hAX hX0 hwf hdvd hmk zs _ _ τ' _
              hnd.2 h1
              (fun hm => by
                obtain ⟨e1, e2⟩ := hxin' hm
                refine ⟨?_, e2⟩
                rw [allocState_allocOf, ite_neg' (fun hc => hzx hc.1)]; exact e1)
              (fun hm hl => by
                rw [allocState_allocOf, ite_neg' (fun hc => hzx hc.1)]; exact hx' hm hl)
              (by rw [allocState_allocOf, ite_neg' (fun hc => hzx hc.1)]; exact htx) ht
            refine ⟨ocomb (σ.mem.allocs.length + 1)
              (fun _ => ωs τ.mem.allocs.length + D / (P.layout z).align) ω2, σ', g', ?_, h3, h4⟩
            have hchk : (σ.mem.allocs.all fun al => !al.live ||
                disjointRanges ((P.layout z).align * (ωs τ.mem.allocs.length + 1) + D)
                  (P.layout z).size al.base al.size) = true := by
              rw [List.all_eq_true]
              intro al hal
              obtain ⟨j, hj, hjal⟩ := List.getElem_of_mem hal
              have e : σ.mem.allocs[j]? = some al := by rw [List.getElem?_eq_getElem hj, hjal]
              cases hl : al.live with
              | false => rfl
              | true => simpa using hcS j al e hl
            have hlay : (eraseMarkers P x).layout z = P.layout z := rfl
            simp only [allocEntry, eraseMarkers_hasMarkers_ne P hzx, hzm', Bool.false_eq_true,
              ↓reduceIte, hlay]
            have hc : allocate (.fresh (ocomb (σ.mem.allocs.length + 1)
                (fun _ => ωs τ.mem.allocs.length + D / (P.layout z).align) ω2)) σ z (P.layout z) =
                allocate (.fresh fun _ => ωs τ.mem.allocs.length + D / (P.layout z).align) σ z
                  (P.layout z) :=
              allocate_mode_congr (Ss := .fresh) σ z _ (by simp [ocomb])
            rw [hc]
            simp only [allocate_fresh, addr_shift (hdvd z), hchk, ↓reduceIte, Option.bind_some]
            have hge : ∀ k, (allocState σ z (P.layout z) ((P.layout z).align *
                (ωs τ.mem.allocs.length + 1) + D)).mem.allocs.length ≤ k →
                ocomb (σ.mem.allocs.length + 1)
                  (fun _ => ωs τ.mem.allocs.length + D / (P.layout z).align) ω2 k = ω2 k :=
              fun k hk => by
                rw [allocState_length] at hk
                simp only [ocomb]; rw [ite_neg' (by omega)]
            exact (allocEntry_local_ge (Ss := .fresh) zs _ hge).trans h2
          · cases ha

end Entry2

/-- **The reverse simulation.** Under the conditions on `D`, `X0` and `A`, for a program that is
UB-free under fresh addresses and whose statements observe no address (`ProgOK2`), every
behaviour of `P` improves a behaviour of `eraseMarkers P x`. -/
theorem eraseMarkers_rev_refinesPP_param (P : Prog) (x : Local) (D X0 A : Nat) (hAD : A < D)
    (hXD : X0 + (P.layout x).size ≤ D + 1) (hAX : A < X0)
    (hX0 : X0 = (P.layout x).align * (A + 1)) (hwf : ∀ y, 0 < (P.layout y).align)
    (hdvd : ∀ y, (P.layout y).align ∣ D) (hok : ProgOK2 (JA A) P) (hub : UBFree .fresh P) :
    RefinesPP .fresh (eraseMarkers P x) P := by
  cases hmk : P.hasMarkers x with
  | false => rw [eraseMarkers_eq_self hmk]; exact refinesPP_refl _ P
  | true =>
    rintro bt ⟨ωs, st0, h0, hbt⟩
    let init : State := ⟨⟨[], []⟩, List.replicate P.locals.length none⟩
    have hao : ∀ y, init.allocOf y = none := fun y => allocOf_replicate _ _ _
    have hinit : SRel2 P x D X0 A (fun _ => none) init init := by
      refine ⟨⟨(fun _ _ _ _ h => by cases h), (fun _ _ _ _ _ _ h => by cases h),
        (fun _ _ _ _ _ _ h => by cases h), (fun _ _ _ _ => by simp [init, Mem.inBounds]; split <;> simp),
        (fun _ _ _ _ _ h => by simp [init] at h), (fun _ _ _ _ _ h => by simp [init] at h),
        (fun _ _ _ _ _ _ _ _ _ h => by cases h)⟩,
        (fun y _ => Or.inl ⟨hao y, hao y⟩), (fun _ => Or.inl (hao x)),
        (fun k h => by rw [hao] at h; cases h), (fun _ _ _ _ _ h => by cases h),
        (fun _ _ h => by simp [init] at h), (fun y k h => by rw [hao] at h; cases h),
        (fun y z k h => by rw [hao] at h; cases h), (fun y k h => by rw [hao] at h; cases h),
        (fun y z k h => by rw [hao] at h; cases h), (by simp [init]), (by simp [init]),
        (fun _ _ h => by simp [init] at h)⟩
    have h0' : allocEntry (.fresh ωs) P (List.range P.locals.length) init = some st0 := h0
    obtain ⟨ω0, st0T, g, h0T, hrel, hxs⟩ := entry_aux2 (ωs := ωs) hAD hXD hAX hX0 hwf hdvd hmk
      (List.range P.locals.length) init init st0 (fun _ => none) List.nodup_range hinit
      (fun hm => ⟨hao x, List.mem_range.1 hm⟩) (fun hm hl => absurd (List.mem_range.2 hl) hm)
      (hao x) h0'
    have hR : CRel2 P x D X0 A ωs (P.entry 0 st0) ((eraseMarkers P x).entry 0 st0T) (P.entry 0 st0) :=
      crel2_entry hrel hxs 0 ⟨0, [], rfl⟩
    have hsim : LIsSim .fresh (eraseMarkers P x) (.fresh ωs) P
        (CRel2 P x D X0 A ωs (P.entry 0 st0)) (fun c => c.rest.length) (maxBlk P) :=
      ⟨fun _ ct hr => Nat.le_trans hr.2.2.1.length_le (blk_length_le P ct.lbl),
        crel2_lstep h0 hub hAD hXD hwf hdvd hok⟩
    obtain ⟨ωT, bs, hbs, himp⟩ := hsim.improves hR bt hbt
    refine ⟨bs, ⟨ocomb st0T.mem.allocs.length ω0 ωT, st0T, ?_, ?_⟩, himp⟩
    · exact allocEntry_local_upto (Ss := .fresh) _ _ _ h0T fun k _ hk => by simp [ocomb, hk]
    · have hge : ∀ k, ((eraseMarkers P x).entry 0 st0T).nAlloc ≤ k →
          ocomb st0T.mem.allocs.length ω0 ωT k = ωT k := fun k hk => by
        simp only [Cfg.nAlloc, Prog.entry] at hk
        simp only [ocomb]; rw [ite_neg' (Nat.not_lt.2 hk)]
      exact (hasBehFrom_local_ge (Ss := .fresh) (P := eraseMarkers P x) hge bs).2 hbs

end Toy.PlaceEval
