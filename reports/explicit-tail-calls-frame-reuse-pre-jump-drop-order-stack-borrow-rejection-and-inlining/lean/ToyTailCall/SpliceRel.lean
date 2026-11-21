import ToyTailCall.SpliceSite

/-!
# Proof support: the simulation relation for call-site splicing

The original stack (top first) is related to the spliced one frame by frame, except that a
frame of `g` entered at the splice site, together with the frame of `ci` below it, corresponds
to one frame of the spliced `ci` (`InlRel`): `ci`'s slots at offset `0`, `g`'s slots at offset
`nC`, then temporaries. Frame identities are renamed by `ρ`.
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false

def Site.renCont (S : Site) : Cont → Cont
  | .store d n => .store (d + S.nC) (S.gStart + S.K * n)
  | .thenReturn => .thenReturn

/-- Well-formedness of a frame of the original run. -/
structure OWF (p : Prog) (F : Frame) : Prop where
  wf : ∃ fn, p.fns[F.fn]? = some fn ∧ F.vals.length = fn.nSlots
  llen : F.live.length = F.vals.length
  ret : F.pendingRet = none

/-- A frame of the original run and its own counterpart in the spliced run. -/
structure PlainRel (S : Site) (ρ : Nat → Nat × Nat) (F F' : Frame) : Prop where
  fid : ρ F.fid = (F'.fid, 0)
  fn : F'.fn = F.fn
  emb : Emb ρ 0 F F'
  owf : OWF S.p F
  wf' : ∃ fn', S.p'.fns[F'.fn]? = some fn' ∧ F'.vals.length = fn'.nSlots
  llen' : F'.live.length = F'.vals.length
  ret' : F'.pendingRet = none
  ext : ∀ fn', S.p'.fns[F.fn]? = some fn' → ∀ s : Nat, F.vals.length ≤ s → F'.isLive s = true →
    fn'.dtor s = .none

/-- A frame `G` of `g` entered at the splice site, the frame `C` of `ci` below it, and the merged
frame `M` of the spliced run. -/
structure InlRel (S : Site) (ρ : Nat → Nat × Nat) (G C M : Frame) : Prop where
  fidG : ρ G.fid = (M.fid, S.nC)
  fidC : ρ C.fid = (M.fid, 0)
  fnG : G.fn = S.g
  fnC : C.fn = S.ci
  fnM : M.fn = S.ci
  embG : Emb ρ S.nC G M
  embC : Emb ρ 0 C M
  owfG : OWF S.p G
  owfC : OWF S.p C
  ret' : M.pendingRet = none
  llen' : M.live.length = M.vals.length
  vlen' : M.vals.length = S.nC + S.nG + S.nT

/-- A frame waiting for a call with an in-range destination. -/
def StoreOK (F : Frame) : Prop := ∃ d n, F.cont = .store d n ∧ d < F.vals.length

/-- Related stacks of waiting (non-top) frames. -/
inductive Below (S : Site) (ρ : Nat → Nat × Nat) : List Frame → List Frame → Prop
  | nil : Below S ρ [] []
  | plain {F F' : Frame} {os ss : List Frame} : PlainRel S ρ F F' → F'.cont = F.cont → StoreOK F →
      Below S ρ os ss → Below S ρ (F :: os) (F' :: ss)
  | inl {G C M : Frame} {os ss : List Frame} : InlRel S ρ G C M → C.cont = .store S.dst S.next →
      StoreOK G → M.cont = S.renCont G.cont → Below S ρ os ss → Below S ρ (G :: C :: os) (M :: ss)

/-- Related whole stacks; `u` is the unwinding flag (positions matter only when not unwinding). -/
inductive Top (S : Site) (ρ : Nat → Nat × Nat) (u : Bool) : List Frame → List Frame → Prop
  | plain {F F' : Frame} {os ss : List Frame} : PlainRel S ρ F F' → (u = false → F'.pc = F.pc) →
      Below S ρ os ss → Top S ρ u (F :: os) (F' :: ss)
  | inl {G C M : Frame} {os ss : List Frame} : InlRel S ρ G C M → C.cont = .store S.dst S.next →
      (u = false → M.pc = S.gStart + S.K * G.pc) → Below S ρ os ss →
      Top S ρ u (G :: C :: os) (M :: ss)

/-- Related running states (original first). -/
structure RelAt (S : Site) (ρ : Nat → Nat × Nat) (a b : State) : Prop where
  top : Top S ρ a.unwinding a.stack b.stack
  uw : b.unwinding = a.unwinding
  ev : b.events = a.events
  freshA : ∀ F ∈ a.stack, F.fid < a.nextFid ∧ ∀ v ∈ F.vals, PtrLt a.nextFid v
  freshB : ∀ F ∈ b.stack, F.fid < b.nextFid
  orderB : b.stack.Pairwise fun x y => y.fid < x.fid

/-- Matched configurations (original first). -/
def Match (S : Site) (ca cb : Conf) : Prop :=
  (∃ a b, ca = .running a ∧ cb = .running b ∧ ∃ ρ, RelAt S ρ a b) ∨
  (∃ ra rb, ca = .halted ra ∧ cb = .halted rb ∧ ra.outcome = rb.outcome ∧ ra.events = rb.events) ∨
  (∃ ra, ca = .halted ra ∧ (ra.outcome = .ub ∨ ra.outcome = .stackOverflow))

theorem match_halted {S : Site} {ra rb : Result} (ho : ra.outcome = rb.outcome)
    (he : ra.events = rb.events) : Match S (.halted ra) (.halted rb) :=
  Or.inr (Or.inl ⟨ra, rb, rfl, rfl, ho, he⟩)

theorem match_ub {S : Site} {cb : Conf} (st : State) : Match S (st.halt .ub) cb :=
  Or.inr (Or.inr ⟨_, rfl, Or.inl rfl⟩)

theorem match_so {S : Site} {cb : Conf} (st : State) : Match S (st.halt .stackOverflow) cb :=
  Or.inr (Or.inr ⟨_, rfl, Or.inr rfl⟩)

theorem match_halt {S : Site} {a b : State} (o : Outcome) (he : b.events = a.events) :
    Match S (a.halt o) (b.halt o) :=
  match_halted rfl he.symm

theorem match_running {S : Site} {ρ : Nat → Nat × Nat} {a b : State} (h : RelAt S ρ a b) :
    Match S (.running a) (.running b) :=
  Or.inl ⟨a, b, rfl, rfl, ρ, h⟩

theorem match_bump {S : Site} {ca cb : Conf} (h : Match S ca cb) :
    Match S (bumpTail ca) (bumpTail cb) := by
  rcases h with ⟨a, b, rfl, rfl, ρ, hr⟩ | ⟨ra, rb, rfl, rfl, ho, he⟩ | ⟨ra, rfl, ho⟩
  · exact Or.inl ⟨_, _, rfl, rfl, ρ, ⟨hr.top, hr.uw, hr.ev, hr.freshA, hr.freshB, hr.orderB⟩⟩
  · exact match_halted ho he
  · exact Or.inr (Or.inr ⟨ra, rfl, ho⟩)

/-! ### Basic facts -/

theorem Below.length_le {S : Site} {ρ : Nat → Nat × Nat} :
    ∀ {os ss : List Frame}, Below S ρ os ss → ss.length ≤ os.length
  | _, _, .nil => Nat.le_refl _
  | _, _, .plain _ _ _ h => by simp only [List.length_cons]; have := h.length_le; omega
  | _, _, .inl _ _ _ _ h => by simp only [List.length_cons]; have := h.length_le; omega

theorem Site.fnS_g (S : Site) : S.fnS S.g S.gf = S.gf := by simp [Site.fnS, S.hgci]

theorem InlRel.lenG {S : Site} {ρ : Nat → Nat × Nat} {G C M : Frame} (h : InlRel S ρ G C M) :
    G.vals.length = S.nG := by
  obtain ⟨fn, hfn, hl⟩ := h.owfG.wf
  rw [h.fnG, S.hg] at hfn
  cases hfn; exact hl

theorem InlRel.lenC {S : Site} {ρ : Nat → Nat × Nat} {G C M : Frame} (h : InlRel S ρ G C M) :
    C.vals.length = S.nC := by
  obtain ⟨fn, hfn, hl⟩ := h.owfC.wf
  rw [h.fnC, S.hc] at hfn
  cases hfn; exact hl

/-! ### Frame lookup -/

def EmbV (ρ : Nat → Nat × Nat) (off : Nat) (X Y : Frame) : Prop :=
  X.vals.length + off ≤ Y.vals.length ∧ ∀ j : Nat, j < X.vals.length → Y.get (j + off) = rv ρ (X.get j)

theorem Emb.toV {ρ : Nat → Nat × Nat} {off : Nat} {X Y : Frame} (h : Emb ρ off X Y) :
    EmbV ρ off X Y := ⟨h.len, h.get⟩

/-- Every frame that a load from the running frame can reach below it has a counterpart. -/
def Look (ρ : Nat → Nat × Nat) (below : List Frame) (M : Frame) (below' : List Frame) : Prop :=
  ∀ fid X, findFrame below fid = some X →
    ∃ Y, findFrame (M :: below') (ρ fid).1 = some Y ∧ EmbV ρ (ρ fid).2 X Y

theorem findFrame_cons_eq {fr : Frame} {stk : List Frame} {fid : Nat} (h : fr.fid = fid) :
    findFrame (fr :: stk) fid = some fr := by
  simp [findFrame, List.find?_cons, h]

theorem below_find {S : Site} {ρ : Nat → Nat × Nat} :
    ∀ {os ss : List Frame}, Below S ρ os ss → ss.Pairwise (fun x y => y.fid < x.fid) →
      ∀ fid X, findFrame os fid = some X →
        ∃ Y, Y ∈ ss ∧ findFrame ss (ρ fid).1 = some Y ∧ EmbV ρ (ρ fid).2 X Y
  | _, _, .nil, _, fid, X, h => by simp [findFrame] at h
  | F :: os, F' :: ss, .plain hP _ _ hB, hpw, fid, X, h => by
    rw [List.pairwise_cons] at hpw
    by_cases hF : F.fid = fid
    · rw [findFrame_cons_eq hF] at h
      cases h
      subst hF
      refine ⟨F', List.mem_cons_self .., findFrame_cons_eq (by rw [hP.fid]), ?_⟩
      rw [hP.fid]; exact hP.emb.toV
    · rw [findFrame_cons_ne hF] at h
      obtain ⟨Y, hY, hf, he⟩ := below_find hB hpw.2 fid X h
      have hYf := (findFrame_some hf).2
      have hne : F'.fid ≠ (ρ fid).1 := by have := hpw.1 Y hY; omega
      exact ⟨Y, List.mem_cons_of_mem _ hY, by rw [findFrame_cons_ne hne]; exact hf, he⟩
  | G :: C :: os, M :: ss, .inl hI _ _ _ hB, hpw, fid, X, h => by
    rw [List.pairwise_cons] at hpw
    by_cases hG : G.fid = fid
    · rw [findFrame_cons_eq hG] at h
      cases h
      subst hG
      refine ⟨M, List.mem_cons_self .., findFrame_cons_eq (by rw [hI.fidG]), ?_⟩
      rw [hI.fidG]; exact hI.embG.toV
    · rw [findFrame_cons_ne hG] at h
      by_cases hC : C.fid = fid
      · rw [findFrame_cons_eq hC] at h
        cases h
        subst hC
        refine ⟨M, List.mem_cons_self .., findFrame_cons_eq (by rw [hI.fidC]), ?_⟩
        rw [hI.fidC]; exact hI.embC.toV
      · rw [findFrame_cons_ne hC] at h
        obtain ⟨Y, hY, hf, he⟩ := below_find hB hpw.2 fid X h
        have hYf := (findFrame_some hf).2
        have hne : M.fid ≠ (ρ fid).1 := by have := hpw.1 Y hY; omega
        exact ⟨Y, List.mem_cons_of_mem _ hY, by rw [findFrame_cons_ne hne]; exact hf, he⟩

theorem look_plain {S : Site} {ρ : Nat → Nat × Nat} {os ss : List Frame} {M : Frame}
    (hB : Below S ρ os ss) (hpw : ss.Pairwise (fun x y => y.fid < x.fid))
    (hlt : ∀ Y ∈ ss, Y.fid < M.fid) : Look ρ os M ss := by
  intro fid X h
  obtain ⟨Y, hY, hf, he⟩ := below_find hB hpw fid X h
  have hYf := (findFrame_some hf).2
  have hne : M.fid ≠ (ρ fid).1 := by have := hlt Y hY; omega
  exact ⟨Y, by rw [findFrame_cons_ne hne]; exact hf, he⟩

theorem look_inl {S : Site} {ρ : Nat → Nat × Nat} {os ss : List Frame} {C M : Frame}
    (hB : Below S ρ os ss) (hpw : ss.Pairwise (fun x y => y.fid < x.fid))
    (hlt : ∀ Y ∈ ss, Y.fid < M.fid) (hC : ρ C.fid = (M.fid, 0)) (hE : EmbV ρ 0 C M) :
    Look ρ (C :: os) M ss := by
  intro fid X h
  by_cases hc : C.fid = fid
  · rw [findFrame_cons_eq hc] at h
    cases h
    subst hc
    exact ⟨M, findFrame_cons_eq (by rw [hC]), by rw [hC]; exact hE⟩
  · rw [findFrame_cons_ne hc] at h
    exact look_plain hB hpw hlt fid X h

theorem look_congr {ρ : Nat → Nat × Nat} {below below' : List Frame} {M M1 : Frame}
    (h : Look ρ below M below') (hf : M1.fid = M.fid) (hv : M1.vals = M.vals) :
    Look ρ below M1 below' := by
  intro fid X hX
  obtain ⟨Y, hY, he⟩ := h fid X hX
  by_cases hm : M.fid = (ρ fid).1
  · rw [findFrame_cons_eq hm] at hY
    cases hY
    refine ⟨M1, findFrame_cons_eq (by rw [hf, hm]), ?_⟩
    obtain ⟨h1, h2⟩ := he
    exact ⟨by rw [hv]; exact h1, fun j hj => by unfold Frame.get; rw [hv]; exact h2 j hj⟩
  · rw [findFrame_cons_ne hm] at hY
    exact ⟨Y, by rw [findFrame_cons_ne (by rw [hf]; exact hm)]; exact hY, he⟩

/-! ### Operand evaluation -/

theorem lt_off {s n off m : Nat} (hs : s < n) (h : n + off ≤ m) : s + off < m := by omega

def killOf (off : Nat) : Operand → Frame → Frame
  | .move s, M => M.kill (s + off)
  | _, M => M

@[simp] theorem killOf_vals (off : Nat) (o : Operand) (M : Frame) : (killOf off o M).vals = M.vals := by
  cases o <;> rfl
@[simp] theorem killOf_fid (off : Nat) (o : Operand) (M : Frame) : (killOf off o M).fid = M.fid := by
  cases o <;> rfl
@[simp] theorem killOf_pendingRet (off : Nat) (o : Operand) (M : Frame) :
    (killOf off o M).pendingRet = M.pendingRet := by cases o <;> rfl
@[simp] theorem killOf_cont (off : Nat) (o : Operand) (M : Frame) : (killOf off o M).cont = M.cont := by
  cases o <;> rfl
@[simp] theorem killOf_fn (off : Nat) (o : Operand) (M : Frame) : (killOf off o M).fn = M.fn := by
  cases o <;> rfl
@[simp] theorem killOf_pc (off : Nat) (o : Operand) (M : Frame) : (killOf off o M).pc = M.pc := by
  cases o <;> rfl
@[simp] theorem killOf_live_length (off : Nat) (o : Operand) (M : Frame) :
    (killOf off o M).live.length = M.live.length := by cases o <;> simp [killOf]

theorem evalOp_sim {ρ : Nat → Nat × Nat} {off : Nat} {below below' : List Frame} {fr M : Frame}
    {o : Operand} {v : Val} {fr1 : Frame} (hE : Emb ρ off fr M) (hfid : ρ fr.fid = (M.fid, off))
    (hL : Look ρ below M below') (h : evalOp below fr o = some (v, fr1)) :
    evalOp below' M (renOp off o) = some (rv ρ v, killOf off o M) ∧ fr1 = killOf 0 o fr := by
  have hlen := hE.len
  cases o with
  | const n =>
    simp only [evalOp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  | copy s =>
    simp only [evalOp] at h
    split at h
    · next hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, rfl⟩
      simp only [renOp, evalOp, lt_off hs hlen, ↓reduceIte, hE.get s hs]
      rfl
    · cases h
  | move s =>
    simp only [evalOp] at h
    split at h
    · next hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, by simp [killOf]⟩
      simp only [renOp, evalOp, lt_off hs hlen, ↓reduceIte, hE.get s hs]
      rfl
    · cases h
  | addrOf s =>
    simp only [evalOp] at h
    split at h
    · next hs =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, rfl⟩
      simp only [renOp, evalOp, lt_off hs hlen, ↓reduceIte, rv, hfid]
      rfl
    · cases h
  | deref s =>
    simp only [evalOp] at h
    cases hget : fr.get s with
    | ptr fid j =>
      rw [hget] at h
      simp only at h
      have hs : s < fr.vals.length := by
        rcases Nat.lt_or_ge s fr.vals.length with hs | hs
        · exact hs
        · rw [get_of_ge fr hs] at hget; cases hget
      have hM : M.get (s + off) = .ptr (ρ fid).1 (j + (ρ fid).2) := by
        rw [hE.get s hs, hget]; rfl
      cases hX : findFrame (fr :: below) fid with
      | none => rw [hX] at h; cases h
      | some X =>
        rw [hX] at h
        simp only at h
        split at h
        · next hj =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨?_, rfl⟩
          simp only [renOp, evalOp, hM]
          by_cases hfr : fr.fid = fid
          · rw [findFrame_cons_eq hfr] at hX
            cases hX
            subst hfr
            rw [hfid]
            simp only [findFrame_cons_eq (rfl : M.fid = M.fid),
              lt_off hj hlen, ↓reduceIte, hE.get j hj]
            rfl
          · rw [findFrame_cons_ne hfr] at hX
            obtain ⟨Y, hY, hYl, hYg⟩ := hL fid X hX
            simp only [hY, lt_off hj hYl, ↓reduceIte, hYg j hj]
            rfl
        · cases h
    | int n => rw [hget] at h; cases h
    | undef => rw [hget] at h; cases h
  | succ s =>
    simp only [evalOp] at h
    cases hget : fr.get s with
    | int n =>
      rw [hget] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hs : s < fr.vals.length := by
        rcases Nat.lt_or_ge s fr.vals.length with hs | hs
        · exact hs
        · rw [get_of_ge fr hs] at hget; cases hget
      refine ⟨?_, rfl⟩
      simp only [renOp, evalOp, hE.get s hs, hget, rv]
      rfl
    | ptr fid j => rw [hget] at h; cases h
    | undef => rw [hget] at h; cases h

theorem evalOp_move_lt {below : List Frame} {fr : Frame} {s : Nat} {v : Val} {fr1 : Frame}
    (h : evalOp below fr (.move s) = some (v, fr1)) : s < fr.vals.length := by
  simp only [evalOp] at h
  split at h
  · assumption
  · cases h

theorem foldl_kill_fields :
    ∀ (ks : List Nat) (fr : Frame),
      (ks.foldl Frame.kill fr).vals = fr.vals ∧ (ks.foldl Frame.kill fr).fid = fr.fid ∧
      (ks.foldl Frame.kill fr).fn = fr.fn ∧ (ks.foldl Frame.kill fr).pc = fr.pc ∧
      (ks.foldl Frame.kill fr).cont = fr.cont ∧
      (ks.foldl Frame.kill fr).pendingRet = fr.pendingRet ∧
      (ks.foldl Frame.kill fr).live.length = fr.live.length
  | [], _ => by simp
  | d :: ks, fr => by
    simp only [List.foldl_cons]
    have := foldl_kill_fields ks (fr.kill d)
    simpa using this

theorem foldl_kill_isLive :
    ∀ (ks : List Nat) (fr : Frame) (s : Nat),
      (ks.foldl Frame.kill fr).isLive s = if s ∈ ks then false else fr.isLive s
  | [], _, _ => by simp
  | d :: ks, fr, s => by
    simp only [List.foldl_cons, foldl_kill_isLive ks (fr.kill d) s, isLive_kill, List.mem_cons]
    by_cases h1 : s ∈ ks
    · simp [h1]
    · by_cases h2 : s = d <;> simp [h1, h2]

theorem foldl_kill_get (ks : List Nat) (fr : Frame) (s : Nat) :
    (ks.foldl Frame.kill fr).get s = fr.get s := by
  unfold Frame.get; rw [(foldl_kill_fields ks fr).1]

theorem Emb.kills {ρ : Nat → Nat × Nat} {off : Nat} :
    ∀ (ks : List Nat) (F M : Frame), Emb ρ off F M →
      Emb ρ off (ks.foldl Frame.kill F) ((ks.map (· + off)).foldl Frame.kill M)
  | [], _, _, h => h
  | d :: ks, F, M, h => by
    simp only [List.foldl_cons, List.map_cons]
    exact Emb.kills ks _ _ (h.kill d)

theorem Emb.kills_out {ρ : Nat → Nat × Nat} {off : Nat} {F : Frame} :
    ∀ (ts : List Nat) (M : Frame), Emb ρ off F M →
      (∀ t ∈ ts, t < off ∨ F.vals.length + off ≤ t) → Emb ρ off F (ts.foldl Frame.kill M)
  | [], _, h, _ => h
  | t :: ts, M, h, ht => by
    simp only [List.foldl_cons]
    exact Emb.kills_out ts _ (h.kill_out (ht t (List.mem_cons_self ..)))
      (fun t' h' => ht t' (List.mem_cons_of_mem _ h'))

theorem evalOps_sim {ρ : Nat → Nat × Nat} {off : Nat} {below below' : List Frame} :
    ∀ (os : List Operand) (fr M : Frame) (vs : List Val) (fr1 : Frame),
      Emb ρ off fr M → ρ fr.fid = (M.fid, off) → Look ρ below M below' →
      evalOps below fr os = some (vs, fr1) →
      ∃ ks : List Nat, (∀ s ∈ ks, s < fr.vals.length) ∧ fr1 = ks.foldl Frame.kill fr ∧
        evalOps below' M (os.map (renOp off)) =
          some (vs.map (rv ρ), (ks.map (· + off)).foldl Frame.kill M)
  | [], fr, M, vs, fr1, _, _, _, h => by
    simp only [evalOps, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl, rfl⟩
  | o :: os, fr, M, vs, fr1, hE, hfid, hL, h => by
    simp only [evalOps] at h
    cases h1 : evalOp below fr o with
    | none => rw [h1] at h; cases h
    | some vf =>
      obtain ⟨v, fr2⟩ := vf
      rw [h1] at h
      simp only at h
      cases h2 : evalOps below fr2 os with
      | none => rw [h2] at h; cases h
      | some vf2 =>
        obtain ⟨vs2, fr3⟩ := vf2
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨e1, e2⟩ := evalOp_sim hE hfid hL h1
        have hE2 : Emb ρ off fr2 (killOf off o M) := by
          rw [e2]; cases o <;> first | exact hE | exact (by simpa [killOf] using hE.kill _)
        have hfid2 : ρ fr2.fid = ((killOf off o M).fid, off) := by
          rw [e2]; simp [hfid]
        obtain ⟨ks, hks, hfr, hev⟩ := evalOps_sim os fr2 (killOf off o M) vs2 fr3 hE2 hfid2
          (look_congr hL (by simp) (by simp)) h2
        have hlen2 : fr2.vals.length = fr.vals.length := by rw [e2]; simp
        cases o with
        | move s =>
          have hs := evalOp_move_lt h1
          refine ⟨s :: ks, ?_, ?_, ?_⟩
          · intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · exact hs
            · rw [← hlen2]; exact hks x hx
          · rw [hfr, e2]; rfl
          · simp only [List.map_cons, evalOps, e1, hev, List.foldl_cons]; rfl
        | _ =>
          refine ⟨ks, fun x hx => by rw [← hlen2]; exact hks x hx, by rw [hfr, e2]; rfl, ?_⟩
          simp only [List.map_cons, evalOps, e1, hev]; rfl

/-! ### Pointer bounds -/

theorem evalOp_ptrLt {N : Nat} {below : List Frame} {fr : Frame} {o : Operand} {v : Val}
    {fr1 : Frame} (hfr : fr.fid < N) (hall : ∀ X ∈ fr :: below, ∀ w ∈ X.vals, PtrLt N w)
    (h : evalOp below fr o = some (v, fr1)) : PtrLt N v := by
  have hfrv := hall fr (List.mem_cons_self ..)
  cases o with
  | const n =>
    simp only [evalOp, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; trivial
  | copy s =>
    simp only [evalOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact ptrLt_get hfrv s
    · cases h
  | move s =>
    simp only [evalOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact ptrLt_get hfrv s
    · cases h
  | addrOf s =>
    simp only [evalOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact hfr
    · cases h
  | deref s =>
    simp only [evalOp] at h
    cases hget : fr.get s with
    | ptr fid j =>
      rw [hget] at h
      simp only at h
      cases hg : findFrame (fr :: below) fid with
      | none => rw [hg] at h; cases h
      | some g =>
        rw [hg] at h
        simp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          exact ptrLt_get (hall g (findFrame_some hg).1) j
        · cases h
    | int n => rw [hget] at h; cases h
    | undef => rw [hget] at h; cases h
  | succ s =>
    simp only [evalOp] at h
    cases hget : fr.get s with
    | int n =>
      rw [hget] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; trivial
    | ptr fid j => rw [hget] at h; cases h
    | undef => rw [hget] at h; cases h

theorem evalOps_ptrLt {N : Nat} {below : List Frame} :
    ∀ (os : List Operand) (fr : Frame) (vs : List Val) (fr1 : Frame), fr.fid < N →
      (∀ X ∈ fr :: below, ∀ w ∈ X.vals, PtrLt N w) → evalOps below fr os = some (vs, fr1) →
      ∀ v ∈ vs, PtrLt N v
  | [], fr, vs, fr1, _, _, h => by
    simp only [evalOps, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; simp
  | o :: os, fr, vs, fr1, hfr, hall, h => by
    simp only [evalOps] at h
    cases h1 : evalOp below fr o with
    | none => rw [h1] at h; cases h
    | some vf =>
      obtain ⟨v, fr2⟩ := vf
      rw [h1] at h
      simp only at h
      cases h2 : evalOps below fr2 os with
      | none => rw [h2] at h; cases h
      | some vf2 =>
        obtain ⟨vs2, fr3⟩ := vf2
        rw [h2] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hf := evalOp_frame h1
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact evalOp_ptrLt hfr hall h1
        · refine evalOps_ptrLt os fr2 vs2 fr3 (by rw [hf.2.1]; exact hfr) ?_ h2 w hw
          intro X hX
          rcases List.mem_cons.mp hX with rfl | hX
          · rw [hf.1]; exact hall fr (List.mem_cons_self ..)
          · exact hall X (List.mem_cons_of_mem _ hX)

/-! ### Changing the renaming on fresh identities -/

def Bounded (N : Nat) (F : Frame) : Prop := F.fid < N ∧ ∀ v ∈ F.vals, PtrLt N v

theorem PlainRel.congr_rho {S : Site} {ρ ρ' : Nat → Nat × Nat} {N : Nat} {F F' : Frame}
    (h : PlainRel S ρ F F') (hρ : ∀ x, x < N → ρ' x = ρ x) (hb : Bounded N F) :
    PlainRel S ρ' F F' :=
  { h with fid := by rw [hρ _ hb.1]; exact h.fid, emb := h.emb.congr_rho hρ hb.2 }

theorem InlRel.congr_rho {S : Site} {ρ ρ' : Nat → Nat × Nat} {N : Nat} {G C M : Frame}
    (h : InlRel S ρ G C M) (hρ : ∀ x, x < N → ρ' x = ρ x) (hG : Bounded N G) (hC : Bounded N C) :
    InlRel S ρ' G C M :=
  { h with fidG := by rw [hρ _ hG.1]; exact h.fidG, fidC := by rw [hρ _ hC.1]; exact h.fidC,
           embG := h.embG.congr_rho hρ hG.2, embC := h.embC.congr_rho hρ hC.2 }

theorem Below.congr_rho {S : Site} {ρ ρ' : Nat → Nat × Nat} {N : Nat}
    (hρ : ∀ x, x < N → ρ' x = ρ x) :
    ∀ {os ss : List Frame}, Below S ρ os ss → (∀ F ∈ os, Bounded N F) → Below S ρ' os ss
  | _, _, .nil, _ => .nil
  | _, _, .plain hP hc hs hB, hb =>
    .plain (hP.congr_rho hρ (hb _ (List.mem_cons_self ..))) hc hs
      (hB.congr_rho hρ fun F hF => hb F (List.mem_cons_of_mem _ hF))
  | _, _, .inl hI hc hs hm hB, hb =>
    .inl (hI.congr_rho hρ (hb _ (List.mem_cons_self ..))
        (hb _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) hc hs hm
      (hB.congr_rho hρ fun F hF => hb F (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hF)))

end Toy.TailCall.SpliceProof
