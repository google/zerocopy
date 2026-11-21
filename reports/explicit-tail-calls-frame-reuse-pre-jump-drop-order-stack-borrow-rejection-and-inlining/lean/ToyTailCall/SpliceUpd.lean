import ToyTailCall.SpliceRel

/-!
# Proof support: step equations and relation updates for call-site splicing
-/

namespace Toy.TailCall.SpliceProof

open Toy.TailCall
open Toy.TailCall.EscapeProof

set_option linter.unusedSimpArgs false

/-! ### Step equations -/

/-- The instruction-level part of `step` (a copy of its innermost match). -/
def execI (sem : Sem) (D : Option Nat) (p : Prog) (st : State) (fn : Fn) (fr : Frame)
    (rest : List Frame) : Instr → Conf
  | .assign dst op next =>
    match evalOp rest fr op with
    | none => st.halt .ub
    | some (v, fr1) =>
      if dst < fr1.vals.length then
        .running { st with stack := { fr1.write dst v with pc := next } :: rest }
      else st.halt .ub
  | .emit k next =>
    .running { st with stack := { fr with pc := next } :: rest, events := st.events ++ [.out k] }
  | .branchLt s k t e =>
    match fr.get s with
    | .int n => .running { st with stack := { fr with pc := if n < k then t else e } :: rest }
    | _ => st.halt .ub
  | .goto next => .running { st with stack := { fr with pc := next } :: rest }
  | .reset ss next =>
    .running { st with stack := { ss.foldl Frame.clear fr with pc := next } :: rest }
  | .dropSlots ss next =>
    let r := dropList fn fr (ss.filter (fun s => fr.isLive s && fn.dtor s != .none)) false
    let st1 := { st with events := st.events ++ r.2.1 }
    match r.2.2 with
    | .ok => .running { st1 with stack := { r.1 with pc := next } :: rest }
    | .unwind => .running { st1 with stack := r.1 :: rest, unwinding := true }
    | .abort => st1.halt .aborted
  | .call f args dst next =>
    match evalOps rest fr args with
    | none => st.halt .ub
    | some (vs, fr1) =>
      if dst < fr1.vals.length then
        push D p st ({ fr1 with cont := .store dst next } :: rest) f vs
      else st.halt .ub
  | .ret op =>
    match evalOp rest fr op with
    | none => st.halt .ub
    | some (v, fr1) => doReturn st fn fr1 rest v
  | .tailCall f args =>
    match evalOps rest fr args with
    | none => st.halt .ub
    | some (vs, fr1) => doTailCall sem D p st fn fr1 rest f vs
  | .panic => .running { st with unwinding := true }

theorem step_exec {sem : Sem} {D : Option Nat} {p : Prog} {st : State} {fr : Frame}
    {rest : List Frame} {fn : Fn} {i : Instr} (hs : st.stack = fr :: rest)
    (hfn : p.fns[fr.fn]? = some fn) (hu : st.unwinding = false) (hr : fr.pendingRet = none)
    (hc : fn.code[fr.pc]? = some i) : step sem D p st = execI sem D p st fn fr rest i := by
  obtain ⟨stk, nf, ev, md, tc, uw⟩ := st
  obtain ⟨fid, f, pc, vals, live, cont, pr⟩ := fr
  simp only at hs hu hr hfn hc
  subst hs hu hr
  simp only [step, hfn, hc, Bool.false_eq_true, ↓reduceIte]
  cases i <;> rfl

theorem step_code_none {sem : Sem} {D : Option Nat} {p : Prog} {st : State} {fr : Frame}
    {rest : List Frame} {fn : Fn} (hs : st.stack = fr :: rest)
    (hfn : p.fns[fr.fn]? = some fn) (hu : st.unwinding = false) (hr : fr.pendingRet = none)
    (hc : fn.code[fr.pc]? = none) : step sem D p st = st.halt .ub := by
  simp only [step, hs, hfn, hu, hr, hc, Bool.false_eq_true, ↓reduceIte]

theorem step_fn_none {sem : Sem} {D : Option Nat} {p : Prog} {st : State} {fr : Frame}
    {rest : List Frame} (hs : st.stack = fr :: rest) (hfn : p.fns[fr.fn]? = none) :
    step sem D p st = st.halt .ub := by
  simp only [step, hs, hfn]

/-- One unwinding step. -/
def unwStep (st : State) (fn : Fn) (fr : Frame) (rest : List Frame) : Conf :=
  let r := dropList fn fr (pendingDrops fn fr) true
  let st1 := { st with events := st.events ++ r.2.1 }
  match r.2.2 with
  | .abort => st1.halt .aborted
  | _ =>
    match rest with
    | [] => st1.halt .panicked
    | _ => .running { st1 with stack := rest }

theorem step_unw {sem : Sem} {D : Option Nat} {p : Prog} {st : State} {fr : Frame}
    {rest : List Frame} {fn : Fn} (hs : st.stack = fr :: rest)
    (hfn : p.fns[fr.fn]? = some fn) (hu : st.unwinding = true) :
    step sem D p st = unwStep st fn fr rest := by
  obtain ⟨stk, nf, ev, md, tc, uw⟩ := st
  simp only at hs hu
  subst hs hu
  simp only [step, hfn, ↓reduceIte, unwStep]
  rfl

theorem run_succ (sem : Sem) (D : Option Nat) (p : Prog) (n : Nat) (st : State) :
    run sem D p (n + 1) (.running st) = run sem D p n (step sem D p st) := rfl

/-! ### Relation updates: plain frames -/

section
variable {S : Site} {ρ : Nat → Nat × Nat}

theorem PlainRel.congr {F F' F1 F1' : Frame} (h : PlainRel S ρ F F')
    (hv : F1.vals = F.vals) (hl : F1.live = F.live) (hf : F1.fid = F.fid) (hn : F1.fn = F.fn)
    (hr : F1.pendingRet = F.pendingRet) (hv' : F1'.vals = F'.vals) (hl' : F1'.live = F'.live)
    (hf' : F1'.fid = F'.fid) (hn' : F1'.fn = F'.fn) (hr' : F1'.pendingRet = F'.pendingRet) :
    PlainRel S ρ F1 F1' where
  fid := by rw [hf, hf']; exact h.fid
  fn := by rw [hn', hn]; exact h.fn
  emb := h.emb.congr hv hl hv' hl'
  owf := ⟨by rw [hn, hv]; exact h.owf.wf, by rw [hl, hv]; exact h.owf.llen,
    by rw [hr]; exact h.owf.ret⟩
  wf' := by rw [hn', hv']; exact h.wf'
  llen' := by rw [hl', hv']; exact h.llen'
  ret' := by rw [hr']; exact h.ret'
  ext := by
    intro fn' hfn s hs hl1
    unfold Frame.isLive at hl1
    rw [hl'] at hl1
    rw [hn] at hfn
    rw [hv] at hs
    exact h.ext fn' hfn s hs hl1

theorem PlainRel.kill {F F' : Frame} (h : PlainRel S ρ F F') (s : Nat) :
    PlainRel S ρ (F.kill s) (F'.kill s) where
  fid := h.fid
  fn := h.fn
  emb := (h.emb.kill s : Emb ρ 0 (F.kill s) (F'.kill (s + 0)))
  owf := ⟨h.owf.wf, by simpa using h.owf.llen, h.owf.ret⟩
  wf' := h.wf'
  llen' := by simpa using h.llen'
  ret' := h.ret'
  ext := by
    intro fn' hfn t ht hl
    rw [isLive_kill] at hl
    split at hl
    · cases hl
    · exact h.ext fn' hfn t ht hl

theorem PlainRel.kills {F F' : Frame} :
    ∀ (ks : List Nat), PlainRel S ρ F F' → PlainRel S ρ (ks.foldl Frame.kill F) (ks.foldl Frame.kill F')
  | [], h => h
  | s :: ks, h => by simp only [List.foldl_cons]; exact PlainRel.kills ks (h.kill s)

theorem PlainRel.write {F F' : Frame} (h : PlainRel S ρ F F') {d : Nat} (hd : d < F.vals.length)
    (v : Val) : PlainRel S ρ (F.write d v) (F'.write d (rv ρ v)) where
  fid := h.fid
  fn := h.fn
  emb := (h.emb.write v hd h.owf.llen h.llen' : Emb ρ 0 (F.write d v) (F'.write (d + 0) (rv ρ v)))
  owf := ⟨by simpa using h.owf.wf, by simpa using h.owf.llen, h.owf.ret⟩
  wf' := by simpa using h.wf'
  llen' := by simpa using h.llen'
  ret' := h.ret'
  ext := by
    intro fn' hfn t ht hl
    have hd' : d < F'.live.length := by have := h.emb.len; rw [h.llen']; omega
    rw [isLive_write _ _ hd'] at hl
    simp only [write_vals_length] at ht
    have : t ≠ d := by omega
    simp only [this, ↓reduceIte] at hl
    exact h.ext fn' hfn t ht hl

theorem PlainRel.clear {F F' : Frame} (h : PlainRel S ρ F F') (d : Nat) :
    PlainRel S ρ (F.clear d) (F'.clear d) where
  fid := h.fid
  fn := h.fn
  emb := (h.emb.clear d : Emb ρ 0 (F.clear d) (F'.clear (d + 0)))
  owf := ⟨by simpa using h.owf.wf, by simpa using h.owf.llen, h.owf.ret⟩
  wf' := by simpa using h.wf'
  llen' := by simpa using h.llen'
  ret' := h.ret'
  ext := by
    intro fn' hfn t ht hl
    rw [isLive_clear] at hl
    simp only [clear_vals_length] at ht
    split at hl
    · cases hl
    · exact h.ext fn' hfn t ht hl

theorem PlainRel.clears {F F' : Frame} :
    ∀ (ss : List Nat), PlainRel S ρ F F' →
      PlainRel S ρ (ss.foldl Frame.clear F) (ss.foldl Frame.clear F')
  | [], h => h
  | s :: ss, h => by simp only [List.foldl_cons]; exact PlainRel.clears ss (h.clear s)

theorem PlainRel.fnS {F F' : Frame} (h : PlainRel S ρ F F') {fn : Fn}
    (hfn : S.p.fns[F.fn]? = some fn) : S.p'.fns[F'.fn]? = some (S.fnS F.fn fn) := by
  rw [h.fn]; exact S.p'_fns hfn

theorem PlainRel.dtor {F F' : Frame} (h : PlainRel S ρ F F') {fn : Fn}
    (hfn : S.p.fns[F.fn]? = some fn) {s : Nat} (hs : s < F.vals.length) :
    (S.fnS F.fn fn).dtor s = fn.dtor s := by
  obtain ⟨fn0, h0, hl⟩ := h.owf.wf
  rw [hfn] at h0; cases h0
  exact S.fnS_dtor hfn (by omega)

theorem PlainRel.pending {F F' : Frame} (h : PlainRel S ρ F F') {fn : Fn}
    (hfn : S.p.fns[F.fn]? = some fn) : pendingDrops (S.fnS F.fn fn) F' = pendingDrops fn F :=
  pendingDrops_ext h.emb (fun _ hs => h.dtor hfn hs)
    (fun s hs hl => h.ext _ (S.p'_fns hfn) s hs hl)

theorem PlainRel.filter {F F' : Frame} (h : PlainRel S ρ F F') {fn : Fn}
    (hfn : S.p.fns[F.fn]? = some fn) (ss : List Nat) :
    ss.filter (fun s => F'.isLive s && (S.fnS F.fn fn).dtor s != .none) =
      ss.filter (fun s => F.isLive s && fn.dtor s != .none) := by
  apply List.filter_congr
  intro s _
  by_cases hs : (s : Nat) < F.vals.length
  · have := h.emb.live s hs
    simp only [Nat.add_zero] at this
    rw [this, h.dtor hfn hs]
  · have hge : F.vals.length ≤ s := Nat.le_of_not_lt hs
    have hF : F.isLive s = false := isLive_of_ge F (by rw [h.owf.llen]; exact hge)
    rw [hF]
    cases hl : F'.isLive s
    · rfl
    · simp [h.ext _ (S.p'_fns hfn) s hge hl]

theorem PlainRel.dropList {F F' : Frame} (h : PlainRel S ρ F F') {fn : Fn}
    (hfn : S.p.fns[F.fn]? = some fn) (l : List Nat) (hl : ∀ s ∈ l, s < F.vals.length)
    (unw : Bool) :
    (Toy.TailCall.dropList (S.fnS F.fn fn) F' l unw).2 = (Toy.TailCall.dropList fn F l unw).2 ∧
      PlainRel S ρ (Toy.TailCall.dropList fn F l unw).1
        (Toy.TailCall.dropList (S.fnS F.fn fn) F' l unw).1 := by
  have hm : l.map (· + 0) = l := by simp
  obtain ⟨a, b, c⟩ := dropList_sim (off := 0) fn (S.fnS F.fn fn) l F F' unw h.emb hl
    (fun s hs => h.dtor hfn (hl s hs))
  rw [hm] at a b c
  refine ⟨a, ?_⟩
  have s1 := dropList_shape fn F l unw
  have s2 := dropList_shape (S.fnS F.fn fn) F' l unw
  have hv1 := (dropList_frame fn F l unw).1
  have hv2 := (dropList_frame (S.fnS F.fn fn) F' l unw).1
  refine
    { fid := by rw [s1.1, s2.1]; exact h.fid
      fn := by rw [s1.1, s2.1]; exact h.fn
      emb := b
      owf := ⟨by rw [s1.1]; exact h.owf.wf, by rw [s1.2, hv1]; exact h.owf.llen,
        by rw [s1.1]; exact h.owf.ret⟩
      wf' := by rw [s2.1]; exact h.wf'
      llen' := by rw [s2.2, hv2]; exact h.llen'
      ret' := by rw [s2.1]; exact h.ret'
      ext := ?_ }
  intro fn' hfn' t ht hlv
  rw [hv1] at ht
  have hs1 : (Toy.TailCall.dropList fn F l unw).1.fn = F.fn := by rw [s1.1]
  rw [hs1] at hfn'
  rw [c t (Or.inr (by simpa using ht))] at hlv
  exact h.ext fn' hfn' t ht hlv

end

/-! ### Relation updates: merged frames -/

section
variable {S : Site} {ρ : Nat → Nat × Nat}

theorem InlRel.congr {G C M G1 C1 M1 : Frame} (h : InlRel S ρ G C M)
    (hGv : G1.vals = G.vals) (hGl : G1.live = G.live) (hGf : G1.fid = G.fid) (hGn : G1.fn = G.fn)
    (hGr : G1.pendingRet = G.pendingRet)
    (hCv : C1.vals = C.vals) (hCl : C1.live = C.live) (hCf : C1.fid = C.fid) (hCn : C1.fn = C.fn)
    (hCr : C1.pendingRet = C.pendingRet)
    (hMv : M1.vals = M.vals) (hMl : M1.live = M.live) (hMf : M1.fid = M.fid) (hMn : M1.fn = M.fn)
    (hMr : M1.pendingRet = M.pendingRet) : InlRel S ρ G1 C1 M1 where
  fidG := by rw [hGf, hMf]; exact h.fidG
  fidC := by rw [hCf, hMf]; exact h.fidC
  fnG := by rw [hGn]; exact h.fnG
  fnC := by rw [hCn]; exact h.fnC
  fnM := by rw [hMn]; exact h.fnM
  embG := h.embG.congr hGv hGl hMv hMl
  embC := h.embC.congr hCv hCl hMv hMl
  owfG := ⟨by rw [hGn, hGv]; exact h.owfG.wf, by rw [hGl, hGv]; exact h.owfG.llen,
    by rw [hGr]; exact h.owfG.ret⟩
  owfC := ⟨by rw [hCn, hCv]; exact h.owfC.wf, by rw [hCl, hCv]; exact h.owfC.llen,
    by rw [hCr]; exact h.owfC.ret⟩
  ret' := by rw [hMr]; exact h.ret'
  llen' := by rw [hMl, hMv]; exact h.llen'
  vlen' := by rw [hMv]; exact h.vlen'

theorem InlRel.killG {G C M : Frame} (h : InlRel S ρ G C M) {s : Nat} (_hs : s < G.vals.length) :
    InlRel S ρ (G.kill s) C (M.kill (s + S.nC)) :=
  { h with
    embG := h.embG.kill s
    embC := h.embC.kill_out (Or.inr (by rw [h.lenC, h.lenG] at *; omega))
    owfG := ⟨h.owfG.wf, by simpa using h.owfG.llen, h.owfG.ret⟩
    llen' := by simpa using h.llen' }

theorem InlRel.killsG {G C M : Frame} :
    ∀ (ks : List Nat), InlRel S ρ G C M → (∀ s ∈ ks, s < G.vals.length) →
      InlRel S ρ (ks.foldl Frame.kill G) C ((ks.map (· + S.nC)).foldl Frame.kill M)
  | [], h, _ => h
  | s :: ks, h, hks => by
    simp only [List.foldl_cons, List.map_cons]
    exact InlRel.killsG ks (h.killG (hks s (List.mem_cons_self ..)))
      (fun x hx => by simpa using hks x (List.mem_cons_of_mem _ hx))

theorem InlRel.killT {G C M : Frame} (h : InlRel S ρ G C M) {t : Nat} (ht : S.nC + S.nG ≤ t) :
    InlRel S ρ G C (M.kill t) :=
  { h with
    embG := h.embG.kill_out (Or.inr (by rw [h.lenG]; omega))
    embC := h.embC.kill_out (Or.inr (by rw [h.lenC]; omega))
    llen' := by simpa using h.llen' }

theorem InlRel.killsT {G C M : Frame} :
    ∀ (ts : List Nat), InlRel S ρ G C M → (∀ t ∈ ts, S.nC + S.nG ≤ t) →
      InlRel S ρ G C (ts.foldl Frame.kill M)
  | [], h, _ => h
  | t :: ts, h, hts => by
    simp only [List.foldl_cons]
    exact InlRel.killsT ts (h.killT (hts t (List.mem_cons_self ..)))
      (fun x hx => hts x (List.mem_cons_of_mem _ hx))

theorem InlRel.writeG {G C M : Frame} (h : InlRel S ρ G C M) {d : Nat} (hd : d < G.vals.length)
    (v : Val) : InlRel S ρ (G.write d v) C (M.write (d + S.nC) (rv ρ v)) :=
  { h with
    embG := h.embG.write v hd h.owfG.llen h.llen'
    embC := h.embC.write_out _ (Or.inr (by rw [h.lenC]; omega))
      (by rw [h.vlen']; rw [h.lenG] at hd; omega) h.llen'
    owfG := ⟨by simpa using h.owfG.wf, by simpa using h.owfG.llen, h.owfG.ret⟩
    llen' := by simpa using h.llen'
    vlen' := by simpa using h.vlen' }

theorem InlRel.writeT {G C M : Frame} (h : InlRel S ρ G C M) {t : Nat} (ht : S.nC + S.nG ≤ t)
    (htM : t < S.nC + S.nG + S.nT) (w : Val) : InlRel S ρ G C (M.write t w) :=
  { h with
    embG := h.embG.write_out _ (Or.inr (by rw [h.lenG]; omega)) (by rw [h.vlen']; exact htM) h.llen'
    embC := h.embC.write_out _ (Or.inr (by rw [h.lenC]; omega)) (by rw [h.vlen']; exact htM) h.llen'
    llen' := by simpa using h.llen'
    vlen' := by simpa using h.vlen' }

theorem InlRel.clearG {G C M : Frame} (h : InlRel S ρ G C M) (d : Nat) :
    InlRel S ρ (G.clear d) C (M.clear (d + S.nC)) :=
  { h with
    embG := h.embG.clear d
    embC := h.embC.clear_out (Or.inr (by rw [h.lenC]; omega))
    owfG := ⟨by simpa using h.owfG.wf, by simpa using h.owfG.llen, h.owfG.ret⟩
    llen' := by simpa using h.llen'
    vlen' := by simpa using h.vlen' }

theorem InlRel.clearsG {G C M : Frame} :
    ∀ (ss : List Nat), InlRel S ρ G C M →
      InlRel S ρ (ss.foldl Frame.clear G) C ((ss.map (· + S.nC)).foldl Frame.clear M)
  | [], h => h
  | s :: ss, h => by
    simp only [List.foldl_cons, List.map_cons]
    exact InlRel.clearsG ss (h.clearG s)

theorem InlRel.dtorG {G C M : Frame} (h : InlRel S ρ G C M) {s : Nat} (hs : s < G.vals.length) :
    S.c'.dtor (s + S.nC) = S.gf.dtor s :=
  S.c'_dtor_g (by rw [h.lenG] at hs; exact hs)

theorem InlRel.dropListG {G C M : Frame} (h : InlRel S ρ G C M) (l : List Nat)
    (hl : ∀ s ∈ l, s < G.vals.length) (unw : Bool) :
    (Toy.TailCall.dropList S.c' M (l.map (· + S.nC)) unw).2 =
        (Toy.TailCall.dropList S.gf G l unw).2 ∧
      InlRel S ρ (Toy.TailCall.dropList S.gf G l unw).1 C
        (Toy.TailCall.dropList S.c' M (l.map (· + S.nC)) unw).1 := by
  obtain ⟨a, b, c⟩ := dropList_sim (off := S.nC) S.gf S.c' l G M unw h.embG hl
    (fun s hs => h.dtorG (hl s hs))
  refine ⟨a, ?_⟩
  have s1 := dropList_shape S.gf G l unw
  have s2 := dropList_shape S.c' M (l.map (· + S.nC)) unw
  have hv1 := (dropList_frame S.gf G l unw).1
  have hv2 := (dropList_frame S.c' M (l.map (· + S.nC)) unw).1
  have hlenG := h.lenG
  have hlenC := h.lenC
  refine
    { fidG := by rw [s1.1, s2.1]; exact h.fidG
      fidC := by rw [s2.1]; exact h.fidC
      fnG := by rw [s1.1]; exact h.fnG
      fnC := h.fnC
      fnM := by rw [s2.1]; exact h.fnM
      embG := b
      embC := ?_
      owfG := ⟨by rw [s1.1]; exact h.owfG.wf, by rw [s1.2, hv1]; exact h.owfG.llen,
        by rw [s1.1]; exact h.owfG.ret⟩
      owfC := h.owfC
      ret' := by rw [s2.1]; exact h.ret'
      llen' := by rw [s2.2, hv2]; exact h.llen'
      vlen' := by rw [hv2]; exact h.vlen' }
  refine ⟨by rw [hv2]; exact h.embC.len, fun s hs => ?_, fun s hs => ?_⟩
  · unfold Frame.get; rw [hv2]; exact h.embC.get s hs
  · rw [c (s + 0) (Or.inl (by rw [hlenC] at hs; omega))]; exact h.embC.live s hs

/-- After `g`'s slots are finalized, the merged frame is a plain frame of `ci`. -/
theorem plain_of_inl {G C M : Frame} (h : InlRel S ρ G C M)
    (hG : ∀ s, s < S.nG → M.isLive (s + S.nC) = true → S.gf.dtor s = .none) :
    PlainRel S ρ C M where
  fid := h.fidC
  fn := by rw [h.fnM, h.fnC]
  emb := h.embC
  owf := h.owfC
  wf' := ⟨S.c', by rw [h.fnM]; exact S.p'_ci, by rw [h.vlen', S.c'_nSlots]⟩
  llen' := h.llen'
  ret' := h.ret'
  ext := by
    intro fn' hfn s hs hl
    rw [h.fnC, S.p'_ci] at hfn
    cases hfn
    rw [h.lenC] at hs
    by_cases hlo : s < S.nC + S.nG
    · have := S.c'_dtor_g (s := s - S.nC) (by omega)
      rw [show s - S.nC + S.nC = s by omega] at this
      rw [this]
      exact hG (s - S.nC) (by omega) (by rw [show s - S.nC + S.nC = s by omega]; exact hl)
    · exact S.c'_dtor_hi (by omega)

/-- After finalizing the pending slots of `G`, no slot of `g` owns a value with a destructor. -/
theorem dropped_g {G C M : Frame} (h : InlRel S ρ G C M)
    (hna : (Toy.TailCall.dropList S.gf G (pendingDrops S.gf G) false).2.2 ≠ .abort) :
    ∀ s, s < S.nG → (Toy.TailCall.dropList S.gf G (pendingDrops S.gf G) false).1.isLive s = true →
      S.gf.dtor s = .none := by
  intro s hs hl
  obtain ⟨_, hpres, hmem⟩ := dropList_kills_mem S.gf G (pendingDrops S.gf G) false hna
  have hG : G.isLive s = true := by
    cases h0 : G.isLive s
    · rw [hpres s h0] at hl; cases hl
    · rfl
  by_cases hd : S.gf.dtor s = .none
  · exact hd
  · have : s ∈ pendingDrops S.gf G := by
      unfold pendingDrops
      simp only [List.mem_filter, List.mem_reverse, List.mem_range, hG, Bool.true_and,
        bne_iff_ne, ne_eq, hd, not_false_eq_true, decide_true, and_true]
      rw [h.lenG]; exact hs
    rw [hmem s this] at hl; cases hl

/-- The pending drops of a merged frame: `g`'s, renamed, then `ci`'s. -/
theorem pendingDrops_merged {G C M : Frame} (h : InlRel S ρ G C M) :
    pendingDrops S.c' M = (pendingDrops S.gf G).map (· + S.nC) ++ pendingDrops S.c C := by
  have hlenG := h.lenG
  have hlenC := h.lenC
  unfold pendingDrops
  rw [h.vlen', range_reverse_split, List.filter_append, range_reverse_split, List.filter_append]
  have h1 : (((List.range S.nT).map (S.nC + S.nG + ·)).reverse.filter
      fun s => M.isLive s && S.c'.dtor s != .none) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    simp only [List.mem_reverse, List.mem_map, List.mem_range] at hx
    obtain ⟨i, -, rfl⟩ := hx
    simp [S.c'_dtor_hi (s := S.nC + S.nG + i) (by omega)]
  rw [h1, List.nil_append, hlenG, hlenC]
  congr 1
  · rw [← List.map_reverse, List.filter_map]
    rw [show (fun x => S.nC + x) = (· + S.nC) from funext fun x => Nat.add_comm _ _]
    congr 1
    apply List.filter_congr
    intro x hx
    simp only [List.mem_reverse, List.mem_range] at hx
    simp only [Function.comp, h.embG.live x (by rw [hlenG]; exact hx),
      S.c'_dtor_g hx]
  · apply List.filter_congr
    intro x hx
    simp only [List.mem_reverse, List.mem_range] at hx
    have := h.embC.live x (by rw [hlenC]; exact hx)
    simp only [Nat.add_zero] at this
    rw [this, S.c'_dtor_c hx]

/-- The `dropSlots` of a spliced `ret`/`tailCall` block selects `g`'s pending drops. -/
theorem filter_gslots {G C M : Frame} (h : InlRel S ρ G C M) :
    ((List.range S.nG).reverse.map (· + S.nC)).filter
        (fun s => M.isLive s && S.c'.dtor s != .none) =
      (pendingDrops S.gf G).map (· + S.nC) := by
  have hlenG := h.lenG
  unfold pendingDrops
  rw [List.filter_map, hlenG]
  congr 1
  apply List.filter_congr
  intro x hx
  simp only [List.mem_reverse, List.mem_range] at hx
  simp only [Function.comp, h.embG.live x (by rw [hlenG]; exact hx), S.c'_dtor_g hx]

/-- A `dropSlots` of `g`, renamed, selects the renamed slots that `g`'s own `dropSlots` selects. -/
theorem filter_renamed {G C M : Frame} (h : InlRel S ρ G C M) (ss : List Nat) :
    (ss.map (· + S.nC)).filter (fun s => M.isLive s && S.c'.dtor s != .none) =
      (ss.filter fun s => G.isLive s && S.gf.dtor s != .none).map (· + S.nC) := by
  have hlenG := h.lenG
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro x _
  simp only [Function.comp]
  by_cases hx : x < S.nG
  · rw [h.embG.live x (by rw [hlenG]; exact hx), S.c'_dtor_g hx]
  · rw [isLive_of_ge G (by rw [h.owfG.llen, hlenG]; omega), S.c'_dtor_hi (by omega)]
    simp

end

end Toy.TailCall.SpliceProof
