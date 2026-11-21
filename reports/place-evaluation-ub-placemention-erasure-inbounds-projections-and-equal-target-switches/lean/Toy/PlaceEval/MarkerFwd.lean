import Toy.PlaceEval.MarkerStep

/-!
# Storage-marker erasure: the forward simulation

The source `P` runs the statements of the target `eraseMarkers P x` interleaved with the
markers of `x`; the source's marker steps are silent and are matched by no target step. The
main result of this file, `eraseMarkers_refinesPP_shift`, gives `RefinesPP S P (eraseMarkers P x)`
under conditions on the shift `D` and the pointers `J` related to themselves.
-/

namespace Toy.PlaceEval

/-! ## A silent source step in front of a lazily matched step -/

theorem lstepSim_of_silent {Ss : Sem} {Ps : Prog} {mt : AllocMode} {Pt : Prog}
    {R : Cfg → Cfg → Prop} {μ : Cfg → Nat} {ω0 : Nat → Nat} {cs cs1 ct : Cfg}
    (h1 : step (Ss.mode ω0) Ps cs = .next none cs1) (h : LStepSim Ss Ps mt Pt R μ cs1 ct) :
    LStepSim Ss Ps mt Pt R μ cs ct := by
  have r1 : run (Ss.mode ω0) Ps 1 cs = .running cs1 [] := run_one_next h1
  rcases h with ⟨ω, k, hk⟩ | ⟨hnext, hhalt, hnub⟩
  · refine Or.inl ⟨ocomb cs1.nAlloc ω0 ω, 1 + k, ?_⟩
    rw [run_ocomb r1 k, hk]; rfl
  refine Or.inr ⟨fun ev ct' hst => ?_, fun st hst => ?_, hnub⟩
  · rcases hnext ev ct' hst with ⟨ω, k, cs', hk, hR⟩ | ⟨rfl, _, hR⟩
    · refine Or.inl ⟨ocomb cs1.nAlloc ω0 ω, k + 1, cs', ?_, hR⟩
      rw [show k + 1 + 1 = 1 + (k + 1) by omega, run_ocomb r1 (k + 1), hk]; rfl
    · exact Or.inl ⟨ω0, 0, cs1, r1, hR⟩
  · obtain ⟨ω, k, st', hk⟩ := hhalt st hst
    refine ⟨ocomb cs1.nAlloc ω0 ω, 1 + k, st', ?_⟩
    rw [run_ocomb r1 k, hk]; rfl

/-! ## Facts about `eraseMarkers` -/

/-- The statements of a block with the markers of `x` removed. -/
def eraseStmts (x : Local) (ss : List Stmt) : List Stmt := ss.filter fun s => !s.isMarkerOf x

theorem eraseMarkers_blk (P : Prog) (x : Local) (l : Label) :
    (eraseMarkers P x).blk l = ⟨eraseStmts x (P.blk l).stmts, (P.blk l).term⟩ := by
  simp only [Prog.blk, eraseMarkers, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases P.blocks[l]? <;> simp [Block.unreach, eraseStmts]

theorem eraseStmts_cons_marker {x : Local} {s : Stmt} (rs : List Stmt) (h : s.isMarkerOf x = true) :
    eraseStmts x (s :: rs) = eraseStmts x rs := by
  simp [eraseStmts, h]

theorem eraseStmts_cons_other {x : Local} {s : Stmt} (rs : List Stmt) (h : s.isMarkerOf x = false) :
    eraseStmts x (s :: rs) = s :: eraseStmts x rs := by
  simp [eraseStmts, h]

theorem eraseMarkers_hasMarkers_self (P : Prog) (x : Local) :
    (eraseMarkers P x).hasMarkers x = false := by
  simp only [Prog.hasMarkers, eraseMarkers, List.any_map, List.any_eq_false]
  intro b _ hb
  simp only [Function.comp, List.any_filter, List.any_eq_true] at hb
  obtain ⟨s, _, hs⟩ := hb
  cases s <;> simp_all [Stmt.isMarkerOf]

theorem eraseMarkers_hasMarkers_ne (P : Prog) {x y : Local} (hy : y ≠ x) :
    (eraseMarkers P x).hasMarkers y = P.hasMarkers y := by
  simp only [Prog.hasMarkers, eraseMarkers, List.any_map]
  congr 1
  funext b
  simp only [Function.comp, List.any_filter]
  congr 1
  funext s
  cases s with
  | storageLive z =>
    simp only [Stmt.isMarkerOf]
    by_cases hz : z = y
    · subst hz; simp [hy]
    · simp [hz]
  | storageDead z =>
    simp only [Stmt.isMarkerOf]
    by_cases hz : z = y
    · subst hz; simp [hy]
    · simp [hz]
  | _ => simp [Stmt.isMarkerOf]

theorem eraseMarkers_eq_self {P : Prog} {x : Local} (h : P.hasMarkers x = false) :
    eraseMarkers P x = P := by
  cases P with
  | mk locals blocks =>
    simp only [eraseMarkers, Prog.mk.injEq, true_and]
    conv => rhs; rw [← List.map_id blocks]
    apply List.map_congr_left
    intro b hb
    simp only [Prog.hasMarkers, List.any_eq_false] at h
    have hb' := h b hb
    simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hb'
    cases b with
    | mk stmts term =>
      simp only [id, Block.mk.injEq, and_true]
      rw [List.filter_eq_self]
      intro s hs
      simp [hb' s hs]

/-! ## Statements that make no allocation -/

/-- A statement other than a storage marker. -/
def NoAllocStmt : Stmt → Prop
  | .storageLive _ => False
  | .storageDead _ => False
  | _ => True

theorem execStmt_noalloc_ne_block {mode : AllocMode} {P : Prog} {σ : State} {s : Stmt}
    (hs : NoAllocStmt s) : execStmt mode P σ s ≠ .block := by
  cases s with
  | placeMention p => simp only [execStmt]; split <;> simp
  | assign dst τ rv =>
    simp only [execStmt]
    split
    · simp
    · split
      · simp
      · split <;> simp
  | emit rv => simp only [execStmt]; split <;> simp
  | storageLive _ => exact absurd hs id
  | storageDead _ => exact absurd hs id

section Exec

variable {P : Prog} {x : Local} {D : Nat} {J : Ptr → Prop} {mt : AllocMode}
  {f : Nat → Option Nat}

theorem XInv.of_eq {τ τ' : State} (h : XInv P x D mt τ) (hf : τ'.frame = τ.frame)
    (ha : τ'.mem.allocs = τ.mem.allocs) : XInv P x D mt τ' := by
  intro hx
  obtain ⟨kx, al, h1, h2, h3⟩ := h hx
  exact ⟨kx, al, by simpa [State.allocOf, hf] using h1, by rw [ha]; exact h2, h3⟩

theorem SRel1.exec_noalloc (hdj : DJOk D J) (hal2 : AlOK D ptrAlign) {σ τ : State}
    (h : SRel1 P x D J mt f σ τ) {s : Stmt} (hs : NoAllocStmt s) (hok : StmtOK D J s)
    (mode mode' : AllocMode) (P1 P2 : Prog) {ev : Option Nat} {σ' : State}
    (he : execStmt mode P1 σ s = .ok ev σ') :
    ∃ τ', execStmt mode' P2 τ s = .ok ev τ' ∧ SRel1 P x D J mt f σ' τ' ∧
      τ'.frame = τ.frame ∧ τ'.mem.allocs = τ.mem.allocs := by
  have hfr := h.frRel
  cases s with
  | placeMention p =>
    simp only [execStmt] at he ⊢
    split at he
    · rename_i hp
      cases he
      cases hq : evalPlace σ p with
      | none => rw [hq] at hp; cases hp
      | some q =>
        obtain ⟨q', hq', _⟩ := evalPlace_transfer hdj h.mem hfr hal2 p hq
        simp only [hq', Option.isSome_some, ↓reduceIte]
        exact ⟨τ, rfl, h, rfl, rfl⟩
    · cases he
  | assign dst τ' rv =>
    obtain ⟨hal, hrv⟩ := hok
    simp only [execStmt] at he ⊢
    cases hq : evalPlace σ dst with
    | none => simp only [hq] at he; cases he
    | some q =>
      obtain ⟨q', hq', hvq⟩ := evalPlace_transfer hdj h.mem hfr hal2 dst hq
      cases hv : rv.eval σ with
      | none => simp only [hq, hv] at he; cases he
      | some v =>
        obtain ⟨v', hv', hvv⟩ := rvalue_transfer hdj h.mem hfr hal2 hrv hv
        cases hm : σ.mem.store q τ' v with
        | none => simp only [hq, hv, hm] at he; cases he
        | some m =>
          simp only [hq, hv, hm, StmtResult.ok.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          obtain ⟨n, hn, hmn, hma, hna⟩ := store_transfer h.mem hvq hvv hal hm
          simp only [hq', hv', hn]
          exact ⟨_, rfl, h.with_mem hmn hma hna, rfl, hna⟩
  | emit rv =>
    simp only [execStmt] at he ⊢
    cases hv : rv.eval σ with
    | none => rw [hv] at he; cases he
    | some v =>
      rw [hv] at he
      obtain ⟨v', hv', hvv⟩ := rvalue_transfer hdj h.mem hfr hal2 hok hv
      rw [hv']
      cases v with
      | ptr _ => cases he
      | int n =>
        cases he
        cases v' with
        | int m => simp only [VV1] at hvv; subst hvv; exact ⟨τ, rfl, h, rfl, rfl⟩
        | ptr _ => simp [VV1] at hvv
  | storageLive _ => exact absurd hs id
  | storageDead _ => exact absurd hs id

end Exec

/-! ## Steps -/

theorem step_cons_ok {mode : AllocMode} {P : Prog} {l : Label} {s : Stmt} {rs : List Stmt}
    {σ σ' : State} {ev : Option Nat} (h : execStmt mode P σ s = .ok ev σ') :
    step mode P ⟨l, s :: rs, σ⟩ = .next ev ⟨l, rs, σ'⟩ := by
  simp [step, h]

theorem step_cons_ub {mode : AllocMode} {P : Prog} {l : Label} {s : Stmt} {rs : List Stmt}
    {σ : State} (h : execStmt mode P σ s = .ub) : step mode P ⟨l, s :: rs, σ⟩ = .ub := by
  simp [step, h]

theorem step_cons_block {mode : AllocMode} {P : Prog} {l : Label} {s : Stmt} {rs : List Stmt}
    {σ : State} (h : execStmt mode P σ s = .block) : step mode P ⟨l, s :: rs, σ⟩ = .block := by
  simp [step, h]

/-- Programs whose statements and terminators satisfy `StmtOK` and `TermOK`. -/
def ProgOK (D : Nat) (J : Ptr → Prop) (P : Prog) : Prop :=
  ∀ b ∈ P.blocks, (∀ s ∈ b.stmts, StmtOK D J s) ∧ TermOK D J b.term

theorem ProgOK.blk {D : Nat} {J : Ptr → Prop} {P : Prog} (h : ProgOK D J P) (l : Label) :
    (∀ s ∈ (P.blk l).stmts, StmtOK D J s) ∧ TermOK D J (P.blk l).term := by
  by_cases hl : l < P.blocks.length
  · rw [blk_eq_getElem hl]
    exact h _ (List.getElem_mem hl)
  · have : P.blk l = Block.unreach := by
      simp [Prog.blk, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
    rw [this]
    exact ⟨fun s hs => by simp [Block.unreach] at hs, trivial⟩

/-- The configuration relation of the forward simulation. -/
def CRel1 (P : Prog) (x : Local) (D : Nat) (J : Ptr → Prop) (mt : AllocMode) (cs ct : Cfg) :
    Prop :=
  cs.lbl = ct.lbl ∧ ct.rest = eraseStmts x cs.rest ∧ (∀ s ∈ cs.rest, s ∈ (P.blk cs.lbl).stmts) ∧
    XInv P x D mt ct.st ∧ ∃ f, SRel1 P x D J mt f cs.st ct.st

section Sim

variable {S : Sem} {P : Prog} {x : Local} {D : Nat} {J : Ptr → Prop} {mt : AllocMode}

theorem crel1_entry {σ τ : State} {f : Nat → Option Nat} (h : SRel1 P x D J mt f σ τ)
    (hx : XInv P x D mt τ) (b : Label) :
    CRel1 P x D J mt (P.entry b σ) ((eraseMarkers P x).entry b τ) := by
  refine ⟨rfl, ?_, fun s hs => hs, hx, f, h⟩
  simp [Prog.entry, eraseMarkers_blk]

theorem crel1_lstep (hdj : DJOk D J) (hal2 : AlOK D ptrAlign) (hmode : ModeRel S mt D P)
    (hok : ProgOK D J P) :
    ∀ (rs : List Stmt) (l : Label) (σ : State) (ct : Cfg), CRel1 P x D J mt ⟨l, rs, σ⟩ ct →
      LStepSim S P mt (eraseMarkers P x) (CRel1 P x D J mt) (fun _ => 0) ⟨l, rs, σ⟩ ct := by
  intro rs
  induction rs with
  | nil =>
    rintro l σ ⟨lt, rt, τ⟩ ⟨hl, hr, _, hx, f, h⟩
    simp only at hl hr
    subst hl
    simp only [eraseStmts, List.filter_nil] at hr
    subst hr
    have hterm : ((eraseMarkers P x).blk l).term = (P.blk l).term := by rw [eraseMarkers_blk]
    have htok := (hok.blk l).2
    have hs : ∀ (Q : Prog) (mode : AllocMode) (st : State), step mode Q ⟨l, [], st⟩ =
        match (Q.blk l).term with
        | .goto b => .next none (Q.entry b st)
        | .switchInt o arms ow =>
          match o.evalInt st with
          | some n => .next none (Q.entry (selectTarget arms ow n) st)
          | none => .ub
        | .halt => .halt st
        | .unreachable => .ub := fun _ _ _ => rfl
    unfold LStepSim
    rw [hs (eraseMarkers P x), hterm]
    have hsP := hs P (S.mode (fun _ => 0)) σ
    cases ht : (P.blk l).term with
    | goto b =>
      rw [ht] at hsP
      dsimp only at hsP ⊢
      refine Or.inr ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
      cases hst
      exact Or.inl ⟨fun _ => 0, 0, _, run_one_next hsP, crel1_entry h hx b⟩
    | switchInt o arms ow =>
      rw [ht] at htok hsP
      dsimp only at hsP ⊢
      cases hv : o.evalInt σ with
      | none =>
        rw [hv] at hsP
        exact Or.inl ⟨fun _ => 0, 1, run_succ_ub 0 hsP⟩
      | some n =>
        rw [hv] at hsP
        have hv' := evalInt_transfer hdj h.mem h.frRel hal2 htok hv
        rw [hv']
        dsimp only
        refine Or.inr ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
        cases hst
        exact Or.inl ⟨fun _ => 0, 0, _, run_one_next hsP, crel1_entry h hx _⟩
    | halt =>
      rw [ht] at hsP
      dsimp only at hsP ⊢
      refine Or.inr ⟨(fun _ _ h => by cases h), fun st hst => ?_, (fun h => by cases h)⟩
      exact ⟨fun _ => 0, 1, σ, run_succ_halt 0 hsP⟩
    | unreachable =>
      rw [ht] at hsP
      dsimp only at hsP
      exact Or.inl ⟨fun _ => 0, 1, run_succ_ub 0 hsP⟩
  | cons s rs ih =>
    rintro l σ ⟨lt, rt, τ⟩ ⟨hl, hr, hsub, hx, f, h⟩
    simp only at hl hr hsub
    subst hl
    have hsub' : ∀ s' ∈ rs, s' ∈ (P.blk l).stmts := fun s' hs' => hsub s' (List.mem_cons_of_mem _ hs')
    have hsok := (hok.blk l).1 s (hsub s (List.mem_cons_self))
    cases hm : s.isMarkerOf x with
    | true =>
      rw [eraseStmts_cons_marker rs hm] at hr
      subst hr
      cases s with
      | storageLive y =>
        have hy : y = x := by simpa [Stmt.isMarkerOf] using hm
        subst hy
        obtain ⟨ω0, σ', f', he, hrel⟩ := h.storageLive_src_x hmode hdj hx
        exact lstepSim_of_silent (step_cons_ok he)
          (ih l σ' _ ⟨rfl, rfl, hsub', hx, f', hrel⟩)
      | storageDead y =>
        have hy : y = x := by simpa [Stmt.isMarkerOf] using hm
        subst hy
        have he : execStmt (S.mode (fun _ => 0)) P σ (.storageDead y) = .ok none (deallocate σ y) := rfl
        exact lstepSim_of_silent (step_cons_ok he)
          (ih l _ _ ⟨rfl, rfl, hsub', hx, f, h.deallocate_src_x⟩)
      | _ => simp [Stmt.isMarkerOf] at hm
    | false =>
      rw [eraseStmts_cons_other rs hm] at hr
      subst hr
      have hTl : (eraseMarkers P x).locals = P.locals := rfl
      cases s with
      | storageLive y =>
        have hy : y ≠ x := by simpa [Stmt.isMarkerOf] using hm
        unfold LStepSim
        cases ht : execStmt mt (eraseMarkers P x) τ (.storageLive y) with
        | ok ev τ' =>
          have hev : ev = none := by
            simp only [execStmt] at ht; split at ht <;> cases ht; rfl
          subst hev
          obtain ⟨ω0, σ', f', he, hrel, hx'⟩ := h.storageLive_both hmode hdj hx hy hTl ht
          rw [step_cons_ok ht]
          refine Or.inr ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
          cases hst
          exact Or.inl ⟨ω0, 0, _, run_one_next (step_cons_ok he), rfl, rfl, hsub', hx', f', hrel⟩
        | ub =>
          simp only [execStmt] at ht; split at ht <;> cases ht
        | block =>
          rw [step_cons_block ht]
          exact Or.inr ⟨(fun _ _ h => by cases h), (fun _ h => by cases h), (fun h => by cases h)⟩
      | storageDead y =>
        have hy : y ≠ x := by simpa [Stmt.isMarkerOf] using hm
        obtain ⟨hrel, hx'⟩ := h.storageDead_both hx hy
        have he : ∀ (mode : AllocMode) (Q : Prog) (st : State),
            execStmt mode Q st (.storageDead y) = .ok none (deallocate st y) := fun _ _ _ => rfl
        unfold LStepSim
        rw [step_cons_ok (he _ _ _)]
        refine Or.inr ⟨fun ev ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
        cases hst
        exact Or.inl ⟨fun _ => 0, 0, _, run_one_next (step_cons_ok (he _ _ _)),
          rfl, rfl, hsub', hx', f, hrel⟩
      | _ =>
        unfold LStepSim
        cases he : execStmt (S.mode (fun _ => 0)) P σ _ with
        | ok ev σ' =>
          obtain ⟨τ', ht, hrel, hf, ha⟩ := h.exec_noalloc hdj hal2 (by exact trivial) hsok _ mt P
            (eraseMarkers P x) he
          rw [step_cons_ok ht]
          refine Or.inr ⟨fun ev' ct' hst => ?_, (fun _ h => by cases h), (fun h => by cases h)⟩
          cases hst
          exact Or.inl ⟨fun _ => 0, 0, _, run_one_next (step_cons_ok he), rfl, rfl, hsub',
            hx.of_eq hf ha, f, hrel⟩
        | ub => exact Or.inl ⟨fun _ => 0, 1, run_succ_ub 0 (step_cons_ub he)⟩
        | block => exact absurd he (execStmt_noalloc_ne_block (by exact trivial))

theorem crel1_lisSim (hdj : DJOk D J) (hal2 : AlOK D ptrAlign) (hmode : ModeRel S mt D P)
    (hok : ProgOK D J P) :
    LIsSim S P mt (eraseMarkers P x) (CRel1 P x D J mt) (fun _ => 0) 0 :=
  ⟨fun _ _ _ => Nat.le_refl _, fun ⟨l, rs, σ⟩ ct h => crel1_lstep hdj hal2 hmode hok rs l σ ct h⟩

end Sim

/-! ## The entry allocations -/

theorem allocEntry_mono {mode : AllocMode} {P : Prog} :
    ∀ (xs : List Local) (σ σ' : State), allocEntry mode P xs σ = some σ' →
      σ.mem.allocs.length ≤ σ'.mem.allocs.length
  | [], σ, σ', h => by cases h; exact Nat.le_refl _
  | z :: zs, σ, σ', h => by
    simp only [allocEntry] at h
    split at h
    · exact allocEntry_mono zs σ σ' h
    · cases ha : allocate mode σ z (P.layout z) with
      | none => rw [ha] at h; cases h
      | some σ1 =>
        rw [ha] at h
        have := allocEntry_mono zs σ1 σ' h
        have := allocate_allocs_length ha
        omega

theorem allocEntry_local_ge {Ss : Sem} {ω ω' : Nat → Nat} {P : Prog} :
    ∀ (xs : List Local) (σ : State), (∀ k, σ.mem.allocs.length ≤ k → ω k = ω' k) →
      allocEntry (Ss.mode ω) P xs σ = allocEntry (Ss.mode ω') P xs σ
  | [], _, _ => rfl
  | z :: zs, σ, h => by
    simp only [allocEntry]
    split
    · exact allocEntry_local_ge zs σ h
    · rw [allocate_mode_congr σ z _ (h _ (Nat.le_refl _))]
      cases ha : allocate (Ss.mode ω') σ z (P.layout z) with
      | none => rfl
      | some σ1 =>
        simp only [Option.bind_some]
        exact allocEntry_local_ge zs σ1 fun k hk => h k (by have := allocate_allocs_length ha; omega)

theorem allocEntry_local_upto {Ss : Sem} {ω ω' : Nat → Nat} {P : Prog} :
    ∀ (xs : List Local) (σ σ' : State), allocEntry (Ss.mode ω) P xs σ = some σ' →
      OAgree ω ω' σ.mem.allocs.length σ'.mem.allocs.length →
      allocEntry (Ss.mode ω') P xs σ = some σ'
  | [], σ, σ', h, _ => h
  | z :: zs, σ, σ', h, ha => by
    simp only [allocEntry] at h ⊢
    split
    · rename_i hz
      rw [ite_pos' hz] at h
      exact allocEntry_local_upto zs σ σ' h ha
    · rename_i hz
      rw [ite_neg' hz] at h
      cases e : allocate (Ss.mode ω) σ z (P.layout z) with
      | none => rw [e] at h; cases h
      | some σ1 =>
        rw [e] at h
        simp only [Option.bind_some] at h
        have h1 := allocate_allocs_length e
        have h2 := allocEntry_mono zs σ1 σ' h
        rw [← allocate_mode_congr σ z _ (ha _ (Nat.le_refl _) (by omega)), e]
        simp only [Option.bind_some]
        exact allocEntry_local_upto zs σ1 σ' h fun k hk1 hk2 => ha k (by omega) hk2

section Entry

variable {P : Prog} {x : Local} {D : Nat} {J : Ptr → Prop} {mt : AllocMode}
  {f : Nat → Option Nat}

/-- The target alone allocates `x < P.locals.length` at entry. -/
theorem SRel1.alloc_tgt_x {σ τ : State} (h : SRel1 P x D J mt f σ τ)
    (hu : ∀ a, σ.mem.get a = .uninit) (hsx : σ.allocOf x = none) (L : Layout) (aT : Nat)
    (hcheck : ∀ ω, mt = .fresh ω → ∀ (k : Nat) (al : Alloc), τ.mem.allocs[k]? = some al →
      al.live = true → disjointRanges aT L.size al.base al.size = true)
    (hpos : D = 0 ∨ 0 < aT) :
    SRel1 P x D J mt f σ (allocState τ x L aT) := by
  refine ⟨⟨?_, ?_, h.mem.junk, ?_⟩, ?_, h.fnone, ?_, ?_, ?_, ?_, ?_, h.slen, ?_, ?_⟩
  · intro k k' al hk hal
    obtain ⟨al', h1, h2⟩ := h.mem.falloc k k' al hk hal
    exact ⟨al', by rw [allocState_getElem?_old (h.frange k k' hk).2]; exact h1, h2⟩
  · intro t; rw [hu]; exact trivial
  · rcases hpos with h0 | hpos'
    · exact Or.inl h0
    · rcases h.mem.tpos with h0 | hp0
      · exact Or.inl h0
      · right
        intro k al hal
        rw [allocState_getElem?] at hal
        split at hal
        · exact hp0 k al hal
        · split at hal
          · cases hal; exact hpos'
          · cases hal
  · intro k k' hk
    rw [allocState_length]
    have := h.frange k k' hk; omega
  · intro z hz
    rw [allocState_allocOf, ite_neg' (fun hc => hz hc.1.symm)]
    exact h.frame z hz
  · intro k hk; rw [hsx] at hk; cases hk
  · intro z j k' al hal hl hj ht
    rw [allocState_allocOf] at ht
    split at ht
    · cases ht; have := (h.frange j _ hj).2; omega
    · exact h.owner z j k' al hal hl hj ht
  · intro z k hk
    rw [allocState_allocOf] at hk
    split at hk
    · cases hk; exact ⟨_, allocState_getElem?_new _ _ _ _, rfl⟩
    · obtain ⟨al, h1, h2⟩ := h.tframe z k hk
      exact ⟨al, by rw [allocState_getElem?_old (getElem?_lt h1)]; exact h1, h2⟩
  · intro z1 z2 k h1 h2
    rw [allocState_allocOf] at h1 h2
    split at h1
    · rename_i hc1
      split at h2
      · rename_i hc2; exact hc1.1.symm.trans hc2.1
      · cases h1
        obtain ⟨al, e, _⟩ := h.tframe z2 _ h2
        have := getElem?_lt e; omega
    · split at h2
      · cases h2
        obtain ⟨al, e, _⟩ := h.tframe z1 _ h1
        have := getElem?_lt e; omega
      · exact h.tinj z1 z2 k h1 h2
  · rw [allocState_frame_length]; exact h.tlen
  · cases mt with
    | slots s => exact True.intro
    | fresh ω =>
      have hd := h.tdisj
      unfold TDisj at hd ⊢
      intro j1 j2 a1 a2 hne h1 h2 l1 l2
      rw [allocState_getElem?] at h1 h2
      split at h1
      · split at h2
        · exact hd j1 j2 a1 a2 hne h1 h2 l1 l2
        · split at h2
          · cases h2
            rw [disjointRanges_comm]
            exact hcheck ω rfl j1 a1 h1 l1
          · cases h2
      · split at h1
        · cases h1
          split at h2
          · exact hcheck ω rfl j2 a2 h2 l2
          · split at h2
            · omega
            · cases h2
        · cases h1

theorem allocState_uninit {σ : State} (hu : ∀ a, σ.mem.get a = .uninit) (z : Local) (L : Layout)
    (a : Nat) : ∀ b, (allocState σ z L a).mem.get b = .uninit := by
  intro b; rw [allocState_get]; split
  · rfl
  · exact hu b

theorem entry_aux {S : Sem} (hdj : DJOk D J) (hmode : ModeRel S mt D P)
    (hmk : P.hasMarkers x = true) :
    ∀ (xs : List Local) (σ τ τ' : State) (f : Nat → Option Nat), xs.Nodup →
      SRel1 P x D J mt f σ τ → (∀ a, σ.mem.get a = .uninit) → σ.allocOf x = none →
      (x ∈ xs → τ.allocOf x = none ∧ x < P.locals.length) → (x ∉ xs → XInv P x D mt τ) →
      allocEntry mt (eraseMarkers P x) xs τ = some τ' →
      ∃ ω0 σ' f', allocEntry (S.mode ω0) P xs σ = some σ' ∧ SRel1 P x D J mt f' σ' τ' ∧
        XInv P x D mt τ'
  | [], σ, τ, τ', f, _, h, _, _, _, hx, ht => by
    cases ht
    exact ⟨fun _ => 0, σ, f, rfl, h, hx (by simp)⟩
  | z :: zs, σ, τ, τ', f, hnd, h, hu, hsx, hxin, hx, ht => by
    rw [List.nodup_cons] at hnd
    simp only [allocEntry] at ht
    by_cases hzx : z = x
    · have hxz : x = z := hzx.symm
      subst hxz
      rw [eraseMarkers_hasMarkers_self, ite_neg' (by simp)] at ht
      obtain ⟨htx, hxl⟩ := hxin (List.mem_cons_self)
      cases ha : allocate mt τ x ((eraseMarkers P x).layout x) with
      | none => rw [ha] at ht; cases ht
      | some τ1 =>
        rw [ha] at ht
        simp only [Option.bind_some] at ht
        have hlay : (eraseMarkers P x).layout x = P.layout x := rfl
        rw [hlay] at ha
        have hxs : x < τ.frame.length := h.tlen ▸ hxl
        -- the target's allocation of `x`
        have key : SRel1 P x D J mt f σ τ1 ∧ XInv P x D mt τ1 := by
          rcases hmode with ⟨s, rfl, rfl, rfl⟩ | ⟨rfl, ⟨ω, rfl⟩, hal⟩
          · rw [allocate_slots] at ha
            cases ha
            refine ⟨h.alloc_tgt_x hu hsx _ _ (fun ω e => by cases e) (Or.inl rfl), fun _ => ?_⟩
            refine ⟨_, _, ?_, allocState_getElem?_new _ _ _ _, rfl, rfl⟩
            rw [allocState_allocOf, ite_pos' ⟨rfl, hxs⟩]
          · rw [allocate_fresh] at ha
            split at ha
            · rename_i htc
              cases ha
              have htc' : ∀ (k : Nat) (al : Alloc), τ.mem.allocs[k]? = some al →
                  al.live = true → disjointRanges ((P.layout x).align *
                    (ω τ.mem.allocs.length + 1)) (P.layout x).size al.base al.size = true := by
                intro k al hal' hl
                have := List.all_eq_true.1 htc al (List.mem_of_getElem? hal')
                simpa [hl] using this
              have hpos : D = 0 ∨ 0 < (P.layout x).align * (ω τ.mem.allocs.length + 1) := by
                rcases (hal x).2 with h0 | h0
                · exact Or.inl h0
                · exact Or.inr (Nat.mul_pos h0 (Nat.succ_pos _))
              refine ⟨h.alloc_tgt_x hu hsx _ _ (fun _ _ => htc') hpos, fun _ => ?_⟩
              refine ⟨_, _, ?_, allocState_getElem?_new _ _ _ _, rfl,
                ⟨ω τ.mem.allocs.length + D / (P.layout x).align, (addr_shift (hal x).1).symm⟩⟩
              rw [allocState_allocOf, ite_pos' ⟨rfl, hxs⟩]
            · cases ha
        obtain ⟨ω0, σ', f', h1, h2, h3⟩ := entry_aux hdj hmode hmk zs σ τ1 τ' f hnd.2 key.1 hu hsx
          (fun hm => absurd hm hnd.1) (fun _ => key.2) ht
        refine ⟨ω0, σ', f', ?_, h2, h3⟩
        simp only [allocEntry, hmk, ↓reduceIte]
        exact h1
    · rw [eraseMarkers_hasMarkers_ne P hzx] at ht
      have hxin' : x ∈ zs → τ.allocOf x = none ∧ x < P.locals.length :=
        fun hm => hxin (List.mem_cons_of_mem _ hm)
      have hx' : x ∉ zs → XInv P x D mt τ := fun hm => hx (by simp [Ne.symm hzx, hm])
      by_cases hzm : P.hasMarkers z = true
      · rw [ite_pos' hzm] at ht
        obtain ⟨ω0, σ', f', h1, h2, h3⟩ := entry_aux hdj hmode hmk zs σ τ τ' f hnd.2 h hu hsx
          hxin' hx' ht
        refine ⟨ω0, σ', f', ?_, h2, h3⟩
        simp only [allocEntry, hzm, ↓reduceIte]
        exact h1
      · rw [ite_neg' hzm] at ht
        cases ha : allocate mt τ z ((eraseMarkers P x).layout z) with
        | none => rw [ha] at ht; cases ht
        | some τ1 =>
          rw [ha] at ht
          simp only [Option.bind_some] at ht
          have hlay : (eraseMarkers P x).layout z = P.layout z := rfl
          rw [hlay] at ha
          obtain ⟨ω1, σ1, f1, hs1, hrel1⟩ := h.alloc_exec hmode hdj hzx ha
          obtain ⟨a1, rfl⟩ := allocate_some hs1
          obtain ⟨b1, rfl⟩ := allocate_some ha
          obtain ⟨ω2, σ', f', h1, h2, h3⟩ := entry_aux hdj hmode hmk zs _ _ τ' f1 hnd.2 hrel1
            (allocState_uninit hu z _ a1)
            (by show (allocState σ z _ a1).allocOf x = none
                rw [allocState_allocOf, ite_neg' (fun hc => hzx hc.1)]; exact hsx)
            (fun hm => by
              obtain ⟨e1, e2⟩ := hxin' hm
              refine ⟨?_, e2⟩
              show (allocState τ z _ b1).allocOf x = none
              rw [allocState_allocOf, ite_neg' (fun hc => hzx hc.1)]; exact e1)
            (fun hm => (hx' hm).allocState hzx _ _) ht
          refine ⟨ocomb (σ.mem.allocs.length + 1) ω1 ω2, σ', f', ?_, h2, h3⟩
          simp only [allocEntry, hzm, Bool.false_eq_true, ↓reduceIte]
          rw [allocate_mode_congr (ω' := ω1) σ z _ (by simp [ocomb]), hs1]
          simp only [Option.bind_some]
          rw [allocEntry_local_ge (ω' := ω2) zs _ fun k hk => by
            simp only [List.length_append, List.length_cons, List.length_nil] at hk
            simp only [ocomb]; rw [ite_neg' (by omega)]]
          exact h1

end Entry

theorem allocOf_replicate (m : Mem) (n y : Nat) :
    (⟨m, List.replicate n none⟩ : State).allocOf y = none := by
  simp only [State.allocOf, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

/-- **The forward simulation.** If the conditions on `D` and `J` hold, the allocation modes
match (`ModeRel`) and every statement and terminator of `P` satisfies `StmtOK`/`TermOK`, then
erasing the markers of `x` refines `P`. -/
theorem eraseMarkers_refinesPP_shift (S : Sem) (P : Prog) (x : Local) (D : Nat)
    (J : Ptr → Prop) (hdj : DJOk D J) (hal2 : AlOK D ptrAlign)
    (hmode : ∀ ωt, ModeRel S (S.mode ωt) D P) (hok : ProgOK D J P) :
    RefinesPP S P (eraseMarkers P x) := by
  cases hmk : P.hasMarkers x with
  | false => rw [eraseMarkers_eq_self hmk]; exact refinesPP_refl S P
  | true =>
    rintro bt ⟨ωt, st0t, h0t, hbt⟩
    let init : State := ⟨⟨[], []⟩, List.replicate P.locals.length none⟩
    have hinit : SRel1 P x D J (S.mode ωt) (fun _ => none) init init := by
      have hao : ∀ y, init.allocOf y = none := fun y => allocOf_replicate _ _ _
      refine ⟨⟨(fun _ _ _ h => by cases h), (fun _ => by simp [init, Mem.get, CR1]),
        (fun _ _ _ _ => by simp [init, Mem.inBounds]; split <;> simp),
        Or.inr (fun _ _ h => by simp [init] at h)⟩,
        (fun _ _ h => by cases h), (fun _ _ _ h => by simp [init] at h),
        (fun y _ => Or.inl ⟨hao y, hao y⟩),
        (fun k h => by rw [hao] at h; cases h), (fun _ _ _ _ h => by simp [init] at h),
        (fun y k h => by rw [hao] at h; cases h), (fun y z k h => by rw [hao] at h; cases h),
        (by simp [init]), (by simp [init]), ?_⟩
      cases h : S.mode ωt with
      | slots s => exact True.intro
      | fresh ω => intro _ _ _ _ _ h1; simp [init] at h1
    have h0t' : allocEntry (S.mode ωt) (eraseMarkers P x) (List.range P.locals.length) init =
        some st0t := h0t
    obtain ⟨ω0, st0s, f, h0s, hrel, hx⟩ := entry_aux hdj (hmode ωt) hmk (List.range P.locals.length)
      init init st0t (fun _ => none) List.nodup_range hinit
      (fun a => by simp [init, Mem.get]) (allocOf_replicate _ _ _)
      (fun hm => ⟨allocOf_replicate _ _ _, List.mem_range.1 hm⟩)
      (fun hm hl => absurd (List.mem_range.2 hl) hm) h0t'
    have hR := crel1_entry hrel hx 0
    obtain ⟨ωs, bs, hbs, himp⟩ := (crel1_lisSim (x := x) hdj hal2 (hmode ωt) hok).improves hR bt hbt
    refine ⟨bs, ⟨ocomb st0s.mem.allocs.length ω0 ωs, st0s, ?_, ?_⟩, himp⟩
    · exact allocEntry_local_upto _ _ _ h0s fun k _ hk => by simp [ocomb, hk]
    · have hge : ∀ k, (P.entry 0 st0s).nAlloc ≤ k → ocomb st0s.mem.allocs.length ω0 ωs k = ωs k :=
        fun k hk => by
          simp only [Cfg.nAlloc, Prog.entry] at hk
          simp only [ocomb]; rw [ite_neg' (Nat.not_lt.2 hk)]
      exact (hasBehFrom_local_ge (Ss := S) (P := P) hge bs).2 hbs

end Toy.PlaceEval

namespace Toy.PlaceEval

/-! ## Refinement without address conditions (no pointer constant with provenance) -/

theorem progOK_of_noProvConst {P : Prog} (hnp : NoProvConst P) :
    ProgOK 0 (fun p => p.prov = none) P := by
  have hop : ∀ o : Operand, o.provFree = true → OpOK 0 (fun p => p.prov = none) o := by
    intro o ho
    cases o with
    | copy p τ => exact fun _ => Nat.dvd_zero _
    | const v =>
      cases v with
      | int _ => trivial
      | ptr q => simpa [Operand.provFree, ConstOK, OpOK] using ho
  have hrv : ∀ rv : Rvalue, rv.provFree = true → RvOK 0 (fun p => p.prov = none) rv := by
    intro rv hr
    cases rv with
    | use o => exact hop o hr
    | rawRef _ => trivial
    | ref _ L => exact fun _ => Nat.dvd_zero _
    | ptrEq a b =>
      simp only [Rvalue.provFree, Bool.and_eq_true] at hr
      exact ⟨rfl, hop a hr.1, hop b hr.2⟩
    | addrOf a => exact ⟨rfl, hop a hr⟩
  intro b hb
  obtain ⟨hs, ht⟩ := hnp b hb
  refine ⟨fun s hsb => ?_, ?_⟩
  · have := hs s hsb
    cases s with
    | assign _ τ rv => exact ⟨fun _ => Nat.dvd_zero _, hrv rv this⟩
    | emit rv => exact hrv rv this
    | _ => trivial
  · cases h : b.term with
    | switchInt o _ _ => rw [h] at ht; exact hop o ht
    | _ => trivial

/-- `eraseMarkers_refinesPP_of_noProvConst`, proved by the forward simulation with no address
shift. -/
theorem eraseMarkers_refinesPP_of_noProvConst_proof (S : Sem) (P : Prog) (x : Local)
    (hnp : NoProvConst P) : RefinesPP S P (eraseMarkers P x) :=
  eraseMarkers_refinesPP_shift S P x 0 (fun p => p.prov = none)
    ⟨fun _ => rfl, fun _ h => Or.inl h⟩ (fun _ => Nat.dvd_zero _)
    (fun ωt => by
      cases S with
      | fresh => exact Or.inr ⟨rfl, ⟨ωt, rfl⟩, fun _ => ⟨Nat.dvd_zero _, Or.inl rfl⟩⟩
      | slots s => exact Or.inl ⟨s, rfl, rfl, rfl⟩)
    (progOK_of_noProvConst hnp)

end Toy.PlaceEval
