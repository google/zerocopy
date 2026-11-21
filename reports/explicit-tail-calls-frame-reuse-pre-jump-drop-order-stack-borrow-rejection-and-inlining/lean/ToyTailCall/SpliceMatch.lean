import ToyTailCall.SpliceUpd

/-!
# Proof support: matching pushes, returns and unwinding for call-site splicing
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

section
variable {S : Site} {ρ : Nat → Nat × Nat}

theorem overflows_mono' {D : Option Nat} {m n : Nat} (h : overflows D n = false) (hmn : m ≤ n) :
    overflows D m = false := by
  cases D with
  | none => rfl
  | some d => simp [overflows] at h ⊢; omega

theorem getD_append_replicate {α : Type} (l : List α) (n : Nat) (x : α) (s : Nat) :
    (l ++ List.replicate n x).getD s x = l.getD s x := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases h : s < l.length
  · rw [List.getElem?_append_left h]
  · rw [List.getElem?_append_right (Nat.le_of_not_lt h), List.getElem?_eq_none (Nat.le_of_not_lt h)]
    cases hx : (List.replicate n x)[s - l.length]? with
    | none => rfl
    | some y => simp [List.eq_of_mem_replicate (List.mem_of_getElem? hx)]

theorem getD_map' {α β : Type} (f : α → β) (l : List α) (s : Nat) (d : α) :
    (l.map f).getD s (f d) = f (l.getD s d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[s]? <;> rfl

theorem getD_replicate {α : Type} (n : Nat) (x d : α) (s : Nat) :
    (List.replicate n x).getD s d = if s < n then x else d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

theorem Bounded.mono {N N' : Nat} {F : Frame} (h : Bounded N F) (hN : N ≤ N') : Bounded N' F :=
  ⟨Nat.lt_of_lt_of_le h.1 hN, fun v hv => ptrLt_mono hN (h.2 v hv)⟩

theorem Bounded.congr {N : Nat} {F F1 : Frame} (h : Bounded N F) (hf : F1.fid = F.fid)
    (hv : F1.vals = F.vals) : Bounded N F1 :=
  ⟨by rw [hf]; exact h.1, by rw [hv]; exact h.2⟩

theorem Bounded.write {N : Nat} {F : Frame} (h : Bounded N F) (d : Nat) {v : Val}
    (hv : PtrLt N v) : Bounded N (F.write d v) :=
  ⟨h.1, fun w hw => by
    rcases write_vals F d v w hw with hw | rfl
    · exact h.2 w hw
    · exact hv⟩

theorem pairwise_head {Y Y1 : Frame} {ss : List Frame}
    (h : (Y :: ss).Pairwise (fun x y => y.fid < x.fid)) (hf : Y1.fid = Y.fid) :
    (Y1 :: ss).Pairwise (fun x y => y.fid < x.fid) := by
  rw [List.pairwise_cons] at h ⊢
  exact ⟨fun z hz => by rw [hf]; exact h.1 z hz, h.2⟩

theorem fresh_head {N : Nat} {Y Y1 : Frame} {ss : List Frame} (h : ∀ F ∈ Y :: ss, F.fid < N)
    (hf : Y1.fid = Y.fid) : ∀ F ∈ Y1 :: ss, F.fid < N := by
  intro F hF
  rcases List.mem_cons.mp hF with rfl | hF
  · rw [hf]; exact h Y (List.mem_cons_self ..)
  · exact h F (List.mem_cons_of_mem _ hF)

theorem bounded_head {N : Nat} {F F1 : Frame} {os : List Frame}
    (h : ∀ X ∈ F :: os, Bounded N X) (h1 : Bounded N F1) : ∀ X ∈ F1 :: os, Bounded N X := by
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX
  · exact h1
  · exact h X (List.mem_cons_of_mem _ hX)

theorem below_top {os ss : List Frame} : Below S ρ os ss → os ≠ [] → Top S ρ true os ss
  | .nil, h => absurd rfl h
  | .plain hP _ _ hB, _ => .plain hP (fun h => by cases h) hB
  | .inl hI hc _ _ hB, _ => .inl hI hc (fun h => by cases h) hB

theorem below_nil_iff {os ss : List Frame} (h : Below S ρ os ss) : os = [] ↔ ss = [] := by
  cases h with
  | nil => simp
  | plain => simp
  | inl => simp

theorem relAt_below {a' b' : State} {os ss : List Frame} (hB : Below S ρ os ss) (hne : os ≠ [])
    (hbA : ∀ F ∈ os, Bounded a'.nextFid F) (hbB : ∀ Y ∈ ss, Y.fid < b'.nextFid)
    (hpw : ss.Pairwise (fun x y => y.fid < x.fid)) (ha : a'.stack = os) (hb : b'.stack = ss)
    (hu : a'.unwinding = true) (hu' : b'.unwinding = true) (he : b'.events = a'.events) :
    RelAt S ρ a' b' :=
  ⟨by rw [hu, ha, hb]; exact below_top hB hne, by rw [hu, hu'], he, by rw [ha]; exact hbA,
    by rw [hb]; exact hbB, by rw [hb]; exact hpw⟩

theorem match_unwindBelow {a1 b1 : State} {os ss : List Frame} (hB : Below S ρ os ss)
    (hbA : ∀ F ∈ os, Bounded a1.nextFid F) (hbB : ∀ Y ∈ ss, Y.fid < b1.nextFid)
    (hpw : ss.Pairwise (fun x y => y.fid < x.fid)) (he : b1.events = a1.events) :
    Match S (unwindBelow a1 os) (unwindBelow b1 ss) := by
  cases os with
  | nil =>
    have : ss = [] := (below_nil_iff hB).1 rfl
    subst this
    exact match_halt _ he
  | cons X os' =>
    cases ss with
    | nil => exact absurd ((below_nil_iff hB).2 rfl) (by simp)
    | cons Y ss' =>
      exact match_running (relAt_below hB (by simp) hbA hbB hpw rfl rfl rfl rfl he)

theorem match_unwStep {a b : State} {fn fn' : Fn} {F F' : Frame} {os ss : List Frame}
    (hd : (dropList fn' F' (pendingDrops fn' F') true).2 = (dropList fn F (pendingDrops fn F) true).2)
    (hB : Below S ρ os ss) (hbA : ∀ X ∈ os, Bounded a.nextFid X) (hbB : ∀ Y ∈ ss, Y.fid < b.nextFid)
    (hpw : ss.Pairwise (fun x y => y.fid < x.fid)) (he : b.events = a.events)
    (hu : a.unwinding = true) (hu' : b.unwinding = true) :
    Match S (unwStep a fn F os) (unwStep b fn' F' ss) := by
  simp only [unwStep, hd]
  cases hr : (dropList fn F (pendingDrops fn F) true).2.2 with
  | abort => exact match_halt _ (by simp [he])
  | ok => exact absurd hr (dropList_true_ne_ok _ _ _)
  | unwind =>
    simp only
    cases os with
    | nil =>
      have : ss = [] := (below_nil_iff hB).1 rfl
      subst this
      exact match_halt _ (by simp [he])
    | cons X os' =>
      cases ss with
      | nil => exact absurd ((below_nil_iff hB).2 rfl) (by simp)
      | cons Y ss' =>
        exact match_running (relAt_below hB (by simp) hbA hbB hpw rfl rfl (by simp [hu])
          (by simp [hu']) (by simp [he]))

theorem match_deliver {a1 b1 : State} {os ss : List Frame} {v : Val} (hB : Below S ρ os ss)
    (hbA : ∀ F ∈ os, Bounded a1.nextFid F) (hbB : ∀ Y ∈ ss, Y.fid < b1.nextFid)
    (hpw : ss.Pairwise (fun x y => y.fid < x.fid)) (hv : PtrLt a1.nextFid v)
    (he : b1.events = a1.events) (hu : a1.unwinding = false) (hu' : b1.unwinding = false) :
    Match S (deliver a1 os v) (deliver b1 ss (rv ρ v)) := by
  cases hB with
  | nil => exact match_halted (by simp) (by simp [he])
  | @plain F F' os' ss' hP hc hs hB' =>
    obtain ⟨d, n, hcd, hd⟩ := hs
    have hcd' : F'.cont = .store d n := by rw [hc, hcd]
    simp only [deliver, hcd, hcd']
    refine match_running (ρ := ρ) ⟨?_, by simp [hu, hu'], by simp [he], ?_, ?_, ?_⟩
    · simp only [hu]
      refine .plain ((hP.write hd v).congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (fun _ => rfl) hB'
    · exact bounded_head hbA ((hbA F (List.mem_cons_self ..)).write d hv |>.congr rfl rfl)
    · exact fresh_head hbB rfl
    · exact pairwise_head hpw rfl
  | @inl G C M os' ss' hI hc hs hm hB' =>
    obtain ⟨d, n, hcd, hd⟩ := hs
    have hcd' : M.cont = .store (d + S.nC) (S.gStart + S.K * n) := by rw [hm, hcd]; rfl
    simp only [deliver, hcd, hcd']
    refine match_running (ρ := ρ) ⟨?_, by simp [hu, hu'], by simp [he], ?_, ?_, ?_⟩
    · simp only [hu]
      exact .inl ((hI.writeG hd v).congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
        hc (fun _ => rfl) hB'
    · exact bounded_head hbA ((hbA G (List.mem_cons_self ..)).write d hv |>.congr rfl rfl)
    · exact fresh_head hbB rfl
    · exact pairwise_head hpw rfl

theorem match_push {D : Option Nat} {a1 b1 : State} {os ss : List Frame} {f : FnId}
    {vs : List Val} (hB : Below S ρ os ss) (hbA : ∀ F ∈ os, Bounded a1.nextFid F)
    (hbB : ∀ Y ∈ ss, Y.fid < b1.nextFid) (hpw : ss.Pairwise (fun x y => y.fid < x.fid))
    (hvs : ∀ v ∈ vs, PtrLt a1.nextFid v) (he : b1.events = a1.events)
    (hu : a1.unwinding = false) (hu' : b1.unwinding = false) :
    Match S (push D S.p a1 os f vs) (push D S.p' b1 ss f (vs.map (rv ρ))) := by
  unfold push
  cases hf : S.p.fns[f]? with
  | none => exact match_ub a1
  | some fn =>
    rw [S.p'_fns hf]
    simp only
    by_cases hbad : (vs.length != fn.nParams || fn.nSlots < fn.nParams) = true
    · simp only [hbad, ↓reduceIte]; exact match_ub a1
    · have hok : vs.length = fn.nParams ∧ fn.nParams ≤ fn.nSlots := by
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
          Classical.not_not, Nat.not_lt] at hbad
        exact hbad
      have hge := S.fnS_nSlots_ge hf
      have hnp := S.fnS_nParams hf
      have hbad' : ¬ ((vs.map (rv ρ)).length != (S.fnS f fn).nParams ||
          (S.fnS f fn).nSlots < (S.fnS f fn).nParams) = true := by
        simp only [List.length_map, hnp, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
          not_or, Classical.not_not, Nat.not_lt]
        omega
      simp only [hbad, hbad', Bool.false_eq_true, ↓reduceIte]
      cases hov : overflows D os.length with
      | true => simp only [↓reduceIte]; exact match_so a1
      | false =>
        have hov' : overflows D ss.length = false := overflows_mono' hov hB.length_le
        simp only [hov', Bool.false_eq_true, ↓reduceIte]
        let ρ' : Nat → Nat × Nat := fun x => if x = a1.nextFid then (b1.nextFid, 0) else ρ x
        have hρ' : ∀ x, x < a1.nextFid → ρ' x = ρ x := by
          intro x hx; simp only [ρ', Nat.ne_of_lt hx, ↓reduceIte]
        have hvs' : ∀ v ∈ vs, rv ρ' v = rv ρ v := fun v hv => rv_congr hρ' (hvs v hv)
        refine match_running (ρ := ρ') ⟨?_, by simp [hu, hu'], by simp [he], ?_, ?_, ?_⟩
        · simp only [hu]
          refine .plain ?_ (fun _ => rfl) (hB.congr_rho hρ' hbA)
          refine
            { fid := by simp [ρ']
              fn := rfl
              emb := ⟨by simp; omega, fun s hs => ?_, fun s hs => ?_⟩
              owf := ⟨⟨fn, hf, by simp; omega⟩, by simp; omega, rfl⟩
              wf' := ⟨S.fnS f fn, S.p'_fns hf, by simp; omega⟩
              llen' := by simp; omega
              ret' := rfl
              ext := ?_ }
          · simp only [Frame.get, Nat.add_zero, getD_append_replicate]
            have e : (vs.map (rv ρ)).getD s .undef = rv ρ (vs.getD s .undef) :=
              getD_map' (rv ρ) vs s .undef
            rw [e]
            rcases get_cases ⟨0, f, 0, vs, [], .thenReturn, none⟩ s with hm | hu0
            · simp only [Frame.get] at hm
              rw [hvs' _ hm]
            · simp only [Frame.get] at hu0
              rw [hu0]; rfl
          · simp only [Frame.isLive, Nat.add_zero, getD_append_replicate, hnp]
          · intro fn' _ s hs hl
            simp only [Frame.isLive, getD_append_replicate, getD_replicate, hnp] at hl
            simp only [List.length_append, List.length_replicate] at hs
            split at hl
            · omega
            · cases hl
        · intro F hF
          rcases List.mem_cons.mp hF with rfl | hF
          · refine ⟨by simp, fun v hv => ?_⟩
            simp only [List.mem_append] at hv
            rcases hv with hv | hv
            · exact ptrLt_mono (Nat.le_succ _) (hvs v hv)
            · rw [List.eq_of_mem_replicate hv]; trivial
          · exact (hbA F hF).mono (Nat.le_succ _)
        · intro Y hY
          rcases List.mem_cons.mp hY with rfl | hY
          · simp
          · exact Nat.lt_succ_of_lt (hbB Y hY)
        · rw [List.pairwise_cons]
          exact ⟨fun Y hY => hbB Y hY, hpw⟩

end

end Toy.TailCall.SpliceProof
