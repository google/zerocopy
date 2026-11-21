import MonoShim.MoreTightness

/-!
# Closed targets never reach an undefined key

`Res.link k` is the toy's undefined-key outcome. On a closed target no run from a key of the target
returns it. Closedness is not necessary for runs from the roots to avoid it: a call to an undefined
key in unreachable code never runs (`dead_undefined_call_never_links`).
-/

namespace Toy.MonoShim

theorem cleanupDrops_no_link (U : List Key) (c : Call)
    (hc : ∀ k ∈ U, ∀ st k', (c k st).1 ≠ .link k') :
    ∀ (ds : List Ty) (st : St), (∀ t ∈ ds, Key.dropGlue t ∈ U) →
      ∀ k', (cleanupDrops c ds st).1 ≠ .link k' := by
  intro ds
  induction ds with
  | nil => intro st _ k'; simp [cleanupDrops]
  | cons t ds ih =>
    intro st h k'
    have ht := hc _ (h t (by simp)) st k'
    simp only [cleanupDrops]
    rcases hr : c (.dropGlue t) st with ⟨r, st'⟩
    rw [hr] at ht
    cases r with
    | ok => exact ih st' (fun t' ht' => h t' (by simp [ht'])) k'
    | unwind => simp
    | _ => exact ht

theorem aggClone_no_link (U : List Key) (c : Call)
    (hc : ∀ k ∈ U, ∀ st k', (c k st).1 ≠ .link k') :
    ∀ (ts done : List Ty) (st : St),
      (∀ t ∈ ts, cloneKey t ∈ U ∧ Key.dropGlue t ∈ U) →
      (∀ t ∈ done, Key.dropGlue t ∈ U) →
      ∀ k', (aggClone c done ts st).1 ≠ .link k' := by
  intro ts
  induction ts with
  | nil => intro done st _ _ k'; simp [aggClone]
  | cons t ts ih =>
    intro done st h hd k'
    have ht := h t (by simp)
    have hct := hc _ ht.1 st k'
    simp only [aggClone]
    rcases hr : c (cloneKey t) st with ⟨r, st'⟩
    rw [hr] at hct
    cases r with
    | ok =>
      apply ih (t :: done) st' (fun t' ht' => h t' (by simp [ht']))
      intro t' ht'
      simp at ht'
      rcases ht' with rfl | ht'
      · exact ht.2
      · exact hd t' ht'
    | unwind => exact cleanupDrops_no_link U c hc done st' hd k'
    | _ => exact hct

theorem execS_no_link (sig : Sig) (U : List Key) (c : Call)
    (hc : ∀ k ∈ U, ∀ st k', (c k st).1 ≠ .link k') :
    ∀ (s : Stmt) (fr : Frame) (st : St), (∀ k ∈ refs sig s, k ∈ U) → FrameIn U fr →
      (∀ k', (execS sig c s fr st).1 ≠ .link k') ∧ FrameIn U (execS sig c s fr st).2.1 := by
  intro s
  induction s with
  | skip => intro fr st _ hf; exact ⟨by simp [execS], hf⟩
  | emit _ => intro fr st _ hf; exact ⟨by simp [execS], hf⟩
  | panic => intro fr st _ hf; exact ⟨by simp [execS], hf⟩
  | seq a b iha ihb =>
    intro fr st hr hf
    obtain ⟨na, fa⟩ := iha fr st (fun k hk => hr k (by simp [refs, hk])) hf
    simp only [execS]
    rcases h : execS sig c a fr st with ⟨r, fr', st'⟩
    rw [h] at na fa
    cases r with
    | ok => exact ihb fr' st' (fun k hk => hr k (by simp [refs, hk])) fa
    | _ => exact ⟨na, fa⟩
  | call f τs =>
    intro fr st hr hf
    exact ⟨hc _ (hr _ (by simp [refs])) st, hf⟩
  | invoke k =>
    intro fr st hr hf
    exact ⟨hc _ (hr _ (by simp [refs])) st, hf⟩
  | mcall tr m t =>
    intro fr st hr hf
    exact ⟨hc _ (hr _ (by simp [refs])) st, hf⟩
  | drop t =>
    intro fr st hr hf
    exact ⟨hc _ (hr _ (by simp [refs])) st, hf⟩
  | clone t =>
    intro fr st hr hf
    exact ⟨hc _ (hr _ (by simp [refs])) st, hf⟩
  | reify j f τs =>
    intro fr st hr hf
    refine ⟨by simp [execS], ?_⟩
    intro j' v hv
    simp only [execS] at hv
    rcases List.mem_cons.mp hv with h | h
    · cases h; exact hr _ (by simp [refs])
    · exact hf j' v h
  | callPtr j =>
    intro fr st _ hf
    simp only [execS]
    rcases hl : fr.lookup j with _ | v
    · exact ⟨by simp, hf⟩
    · cases v with
      | fn k => exact ⟨hc _ (hf j (.fn k) (lookup_mem fr j _ hl)) st, hf⟩
      | vt _ _ => exact ⟨by simp, hf⟩
  | unsize j t tr =>
    intro fr st hr hf
    refine ⟨by simp [execS], ?_⟩
    intro j' v hv
    simp only [execS] at hv
    rcases List.mem_cons.mp hv with h | h
    · cases h
      refine ⟨?_, hr _ (by simp [refs])⟩
      intro e he
      exact hr _ (by simp only [refs, List.mem_append, List.mem_map]; exact Or.inl ⟨e, he, rfl⟩)
    · exact hf j' v h
  | callDyn j m =>
    intro fr st _ hf
    simp only [execS]
    rcases hl : fr.lookup j with _ | v
    · exact ⟨by simp, hf⟩
    · cases v with
      | fn _ => exact ⟨by simp, hf⟩
      | vt es d =>
        simp only
        rcases hm : es.lookup m with _ | k
        · exact ⟨by simp, hf⟩
        · exact ⟨hc _ ((hf j (.vt es d) (lookup_mem fr j _ hl)).1 (m, k) (lookup_mem es m k hm)) st, hf⟩
  | dropDyn j =>
    intro fr st _ hf
    simp only [execS]
    rcases hl : fr.lookup j with _ | v
    · exact ⟨by simp, hf⟩
    · cases v with
      | fn _ => exact ⟨by simp, hf⟩
      | vt es d => exact ⟨hc _ ((hf j (.vt es d) (lookup_mem fr j _ hl)).2) st, hf⟩
  | onUnwind a b iha ihb =>
    intro fr st hr hf
    obtain ⟨na, fa⟩ := iha fr st (fun k hk => hr k (by simp [refs, hk])) hf
    simp only [execS]
    rcases h : execS sig c a fr st with ⟨r, fr', st'⟩
    rw [h] at na fa
    cases r with
    | unwind =>
      obtain ⟨nb, fb⟩ := ihb fr' st' (fun k hk => hr k (by simp [refs, hk])) fa
      rcases h2 : execS sig c b fr' st' with ⟨r2, fr2, st2⟩
      rw [h2] at nb fb
      simp only [h2]
      cases r2 with
      | ok => exact ⟨by simp, fb⟩
      | unwind => exact ⟨by simp, fb⟩
      | _ => exact ⟨nb, fb⟩
    | _ => exact ⟨na, fa⟩
  | cloneAgg ts =>
    intro fr st hr hf
    have h : ∀ t ∈ ts, cloneKey t ∈ U ∧ Key.dropGlue t ∈ U := by
      intro t ht
      exact ⟨hr _ (by simp only [refs, List.mem_append, List.mem_map]; exact Or.inl ⟨t, ht, rfl⟩),
        hr _ (by simp only [refs, List.mem_append, List.mem_map]; exact Or.inr ⟨t, ht, rfl⟩)⟩
    exact ⟨aggClone_no_link U c hc ts [] st h (by simp), hf⟩
  | guard s ih =>
    intro fr st hr hf
    by_cases h0 : st.ctr = 0
    · exact ⟨by simp [execS, h0], by simp [execS, h0]; exact hf⟩
    · simp only [execS, h0, ite_false]
      exact ih fr _ (fun k hk => hr k (by simpa [refs] using hk)) hf

/-- **Closed targets are link-free.** If the table `tbl` restricted to `T` is closed, then no run
of a key of `T`, at any fuel and initial state, ends in `Res.link`. -/
theorem closed_excludes_link (sig : Sig) (tbl : Key → Option Stmt) (T : List Key)
    (hC : Closed sig tbl T) :
    ∀ (n : Nat), ∀ k ∈ T, ∀ (st : St) (k' : Key), (runKey sig tbl n k st).1 ≠ .link k' := by
  intro n
  induction n with
  | zero => intro k _ st k'; simp [runKey]
  | succ n ih =>
    intro k hk st k'
    obtain ⟨hsome, hrefs⟩ := hC k hk
    rcases hb : tbl k with _ | b
    · rw [hb] at hsome; simp at hsome
    · simp only [runKey, hb]
      exact (execS_no_link sig T (runKey sig tbl n) ih b [] st (hrefs b (by simp [hb]))
        (by intro j v hv; simp at hv)).1 k'

/-- `main` panics before calling the undefined function 5. -/
def PdeadUndef : Program where
  fns := [⟨false, .seq .panic (.call 5 [])⟩]
  methods := []
  impls := []
  dropImpls := []
  cloneImpls := []
  assoc := []

def TdeadUndef : List Key := [.inst 5 [], .inst 0 []]

/-- **Closedness is not necessary for link-freedom.** On `PdeadUndef` with target `TdeadUndef`, the
six hypotheses of the adequacy theorem hold, the target is neither closed nor source-defined, and
yet no run from `main` ends in `Res.link`. -/
theorem dead_undefined_call_never_links :
    RootsIn [.inst 0 []] TdeadUndef ∧
    EdgesIn (edgesM PdeadUndef (stdCfg PdeadUndef)) TdeadUndef ∧
    CoversRefs PdeadUndef.sig (stdCfg PdeadUndef).E ∧
    SynthAgrees PdeadUndef (stdCfg PdeadUndef) TdeadUndef ∧
    CanonicalKeys PdeadUndef TdeadUndef ∧
    CanonicalRefs PdeadUndef (stdCfg PdeadUndef) TdeadUndef ∧
    ¬ Closed PdeadUndef.sig (tableM PdeadUndef (stdCfg PdeadUndef) TdeadUndef) TdeadUndef ∧
    ¬ InstDefined PdeadUndef TdeadUndef ∧
    ∀ r ∈ [.inst 0 []], ∀ (n : Nat) (st : St) (k' : Key),
      (runM PdeadUndef (stdCfg PdeadUndef) TdeadUndef n r st).1 ≠ .link k' := by
  refine ⟨by decide, by decide, stdCfg_covers PdeadUndef, synthStd_agrees PdeadUndef _,
    by decide, by decide, by decide, by decide, ?_⟩
  intro r hr n st k'
  simp at hr; subst hr
  cases n with
  | zero => simp [runM, runKey]
  | succ n => simp [runM, runKey, tableM, TdeadUndef, bodyM, Key.isShim, srcDef0, PdeadUndef,
      Stmt.subst, Stmt.norm, execS]

end Toy.MonoShim
