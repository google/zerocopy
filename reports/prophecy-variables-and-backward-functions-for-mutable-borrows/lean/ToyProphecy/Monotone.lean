import ToyProphecy.Programs

/-!
# Simulation lemmas for omitting resolutions at borrow ends

Running the prophecy translation under `ResPolicy.omitAtEnd r` instead of
`ResPolicy.std`, with the same prophecy assignment, takes the same steps, ends in
the same store, and emits a sub-collection of the constraints. These lemmas are
used to prove `prophOutcomeWith_omitAtEnd_of_prophOutcome`.
-/

namespace Toy.Prophecy

open Expr Op Stmt

theorem evalP_congr {L : Bool} {s1 s2 : PState}
    (hst : s2.store = s1.store) (hrefs : s2.refs = s1.refs) :
    ∀ e, evalP L s2 e = evalP L s1 e
  | .lit _ => rfl
  | .var _ => by simp [evalP, hst]
  | .deref _ => by simp [evalP, hrefs]
  | .add a b => by simp [evalP, evalP_congr hst hrefs a, evalP_congr hst hrefs b]

/-- One main-program basic operation under `omitAtEnd r` simulates the same
operation under the standard policy. -/
theorem stepOpP_omitAtEnd_sim (r : RefVar) (φ : Nat → Int) (s1 s2 out1 : PState) (o : Op)
    (hst : s2.store = s1.store) (hrefs : s2.refs = s1.refs) (hnxt : s2.next = s1.next)
    (hcs : ∀ c ∈ s2.cs, c ∈ s1.cs)
    (h : stepOpP true ResPolicy.std.atEnd φ s1 o = some out1) :
    ∃ out2, stepOpP true (ResPolicy.omitAtEnd r).atEnd φ s2 o = some out2 ∧
      out2.store = out1.store ∧ out2.refs = out1.refs ∧ out2.next = out1.next ∧
      (∀ c ∈ out2.cs, c ∈ out1.cs) := by
  have hev := evalP_congr (L := true) hst hrefs
  cases o with
  | assign x e =>
      simp only [stepOpP, ↓reduceIte, Option.map_eq_some_iff] at h ⊢
      obtain ⟨v, hv, rfl⟩ := h
      exact ⟨_, ⟨v, (hev e).symm ▸ hv, rfl⟩, by simp [hst], hrefs, hnxt, hcs⟩
  | borrow q x =>
      simp only [stepOpP, ↓reduceIte, Option.some.injEq] at h ⊢
      subst h
      exact ⟨_, rfl, by simp [hst, hnxt], by simp [hrefs, hst, hnxt], by simp [hnxt], hcs⟩
  | borrowSel q e x y =>
      simp only [stepOpP, ↓reduceIte, Option.map_eq_some_iff] at h ⊢
      obtain ⟨cv, hcv, rfl⟩ := h
      refine ⟨_, ⟨cv, (hev e).symm ▸ hcv, rfl⟩, ?_⟩
      split <;> simp [hst, hrefs, hnxt] <;> exact fun a b hc => hcs (a, b) hc
  | reborrow t q =>
      simp only [stepOpP, Option.map_eq_some_iff] at h ⊢
      obtain ⟨p, hp, rfl⟩ := h
      exact ⟨_, ⟨p, hrefs ▸ hp, rfl⟩, hst, by simp [hrefs, hnxt], by simp [hnxt], hcs⟩
  | write q e =>
      simp only [stepOpP, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h ⊢
      obtain ⟨p, hp, v, hv, rfl⟩ := h
      exact ⟨_, ⟨p, hrefs ▸ hp, v, (hev e).symm ▸ hv, rfl⟩, hst, by simp [hrefs], hnxt, hcs⟩
  | endBorrow q =>
      simp only [stepOpP, ResPolicy.std, ResPolicy.omitAtEnd, Option.map_eq_some_iff] at h ⊢
      obtain ⟨p, hp, rfl⟩ := h
      refine ⟨_, ⟨p, hrefs ▸ hp, rfl⟩, hst, by simp [hrefs], hnxt, ?_⟩
      intro c hc
      by_cases hqr : q = r
      · simp [hqr] at hc ⊢
        exact Or.inl (hcs c hc)
      · simp [hqr] at hc ⊢
        rcases hc with hc | rfl
        · exact Or.inl (hcs c hc)
        · exact Or.inr rfl

/-- A whole main-program run under `omitAtEnd r` simulates the run under the
standard policy: same final store, constraints a sub-collection. -/
theorem runP_omitAtEnd_sim (r : RefVar) (φ : Nat → Int) :
    ∀ (P : Prog) (i : Nat) (s1 s2 out1 : PState),
      s2.store = s1.store → s2.refs = s1.refs → s2.next = s1.next →
      (∀ c ∈ s2.cs, c ∈ s1.cs) →
      runP ResPolicy.std φ i s1 P = some out1 →
      ∃ out2, runP (ResPolicy.omitAtEnd r) φ i s2 P = some out2 ∧
        out2.store = out1.store ∧ (∀ c ∈ out2.cs, c ∈ out1.cs)
  | [], _, s1, s2, out1, hst, _, _, hcs, hrun => by
      simp [runP] at hrun
      subst hrun
      exact ⟨s2, rfl, hst, hcs⟩
  | stmt :: ps, i, s1, s2, out1, hst, hrefs, hnxt, hcs, hrun => by
      simp only [runP, Option.bind_eq_some_iff] at hrun ⊢
      obtain ⟨m1, hstep1, hrest1⟩ := hrun
      cases stmt with
      | op o =>
          have hop1 : stepOpP true ResPolicy.std.atEnd φ s1 o = some m1 := by
            simpa [stepP, earlyCs, ResPolicy.std] using hstep1
          obtain ⟨m2, hop2, hst', hrefs', hnxt', hcs'⟩ :=
            stepOpP_omitAtEnd_sim r φ s1 s2 m1 o hst hrefs hnxt hcs hop1
          have hstep2 : stepP (ResPolicy.omitAtEnd r) φ i s2 (op o) = some m2 := by
            simp only [stepP, earlyCs, ResPolicy.omitAtEnd, ResPolicy.std,
              List.filterMap_nil, List.append_nil, Option.map_eq_some_iff]
            exact ⟨m2, hop2, rfl⟩
          obtain ⟨out2, hrest2, houtst, houtcs⟩ :=
            runP_omitAtEnd_sim r φ ps (i + 1) m1 m2 out1 hst' hrefs' hnxt' hcs' hrest1
          exact ⟨out2, ⟨m2, hstep2, hrest2⟩, houtst, houtcs⟩
      | call t f q =>
          simp only [stepP, earlyCs, ResPolicy.std, List.filterMap_nil, List.append_nil,
            Bind.bind, Pure.pure, Option.bind, Option.map] at hstep1
          cases hq : s1.refs q with
          | none => simp [hq] at hstep1
          | some pq =>
              simp only [hq] at hstep1
              cases hfr : calleeRunP true φ f pq.cur (φ s1.next) (s1.next + 1) with
              | none => simp [hfr] at hstep1
              | some fr =>
                  simp only [hfr] at hstep1
                  cases hret : fr.refs f.ret with
                  | none => simp [hret] at hstep1
                  | some ret =>
                      simp only [hret, Option.some.injEq] at hstep1
                      subst hstep1
                      let m1' : PState :=
                        { s1 with
                          refs := fupd (fupd s1.refs q (some { pq with cur := φ s1.next }))
                            t (some { cur := ret.cur, fin := ret.fin, done := false })
                          next := fr.next
                          cs := s1.cs ++ fr.cs }
                      let m2 : PState :=
                        { s2 with
                          refs := fupd (fupd s2.refs q (some { pq with cur := φ s2.next }))
                            t (some { cur := ret.cur, fin := ret.fin, done := false })
                          next := fr.next
                          cs := s2.cs ++ fr.cs }
                      have hstep2 : stepP (ResPolicy.omitAtEnd r) φ i s2 (call t f q) = some m2 := by
                        simp [stepP, earlyCs, ResPolicy.omitAtEnd, ResPolicy.std, hrefs, hq, hnxt,
                          hfr, hret, m2]
                      have hst' : m2.store = m1'.store := hst
                      have hrefs' : m2.refs = m1'.refs := by simp [m1', m2, hrefs, hnxt]
                      have hnxt' : m2.next = m1'.next := rfl
                      have hcs' : ∀ c ∈ m2.cs, c ∈ m1'.cs := by
                        intro c hc
                        rcases List.mem_append.mp hc with hc | hc
                        · exact List.mem_append.mpr (Or.inl (hcs c hc))
                        · exact List.mem_append.mpr (Or.inr hc)
                      obtain ⟨out2, hrest2, houtst, houtcs⟩ :=
                        runP_omitAtEnd_sim r φ ps (i + 1) m1' m2 out1 hst' hrefs' hnxt' hcs' hrest1
                      exact ⟨out2, ⟨m2, hstep2, hrest2⟩, houtst, houtcs⟩

end Toy.Prophecy
