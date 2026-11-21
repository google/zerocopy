import MonoShim.Ladder

/-!
# Closure and adequacy of the collected target
-/

namespace Toy.MonoShim

/-- Every key stored in a frame slot lies in `U`. -/
def FrameIn (U : List Key) (fr : Frame) : Prop :=
  ∀ j v, (j, v) ∈ fr →
    match v with
    | .fn k => k ∈ U
    | .vt es d => (∀ e ∈ es, e.2 ∈ U) ∧ d ∈ U

theorem lookup_mem {α : Type} : ∀ (l : List (Nat × α)) (j : Nat) (v : α),
    l.lookup j = some v → (j, v) ∈ l := by
  intro l
  induction l with
  | nil => intro j v h; simp [List.lookup] at h
  | cons p l ih =>
    intro j v h
    rcases p with ⟨a, b⟩
    by_cases hj : j = a
    · subst hj; simp [List.lookup] at h; subst h; simp
    · have : (j == a) = false := by simp [hj]
      simp [List.lookup, this] at h
      exact List.mem_cons_of_mem _ (ih j v h)

theorem cleanupDrops_congr (U : List Key) (c1 c2 : Call) (hc : ∀ k ∈ U, ∀ st, c1 k st = c2 k st) :
    ∀ (ds : List Ty) (st : St), (∀ t ∈ ds, Key.dropGlue t ∈ U) →
      cleanupDrops c1 ds st = cleanupDrops c2 ds st := by
  intro ds
  induction ds with
  | nil => intro st _; rfl
  | cons t ds ih =>
    intro st h
    have ht : Key.dropGlue t ∈ U := h t (by simp)
    simp only [cleanupDrops, hc _ ht st]
    rcases c2 (.dropGlue t) st with ⟨r, st'⟩
    cases r <;> simp [ih st' (fun t' ht' => h t' (by simp [ht']))]

theorem aggClone_congr (U : List Key) (c1 c2 : Call) (hc : ∀ k ∈ U, ∀ st, c1 k st = c2 k st) :
    ∀ (ts done : List Ty) (st : St), (∀ t ∈ ts, cloneKey t ∈ U ∧ Key.dropGlue t ∈ U) →
      (∀ t ∈ done, Key.dropGlue t ∈ U) → aggClone c1 done ts st = aggClone c2 done ts st := by
  intro ts
  induction ts with
  | nil => intro done st _ _; rfl
  | cons t ts ih =>
    intro done st h hd
    have ht := h t (by simp)
    simp only [aggClone, hc _ ht.1 st]
    rcases c2 (cloneKey t) st with ⟨r, st'⟩
    cases r with
    | ok =>
      simp only
      apply ih
      · intro t' ht'; exact h t' (by simp [ht'])
      · intro t' ht'
        simp at ht'
        rcases ht' with rfl | ht'
        · exact ht.2
        · exact hd t' ht'
    | unwind => simp only; exact cleanupDrops_congr U c1 c2 hc done st' hd
    | _ => rfl

/-- Congruence of one body execution: oracles that agree on `U` give the same execution of a
statement whose runtime references lie in `U`, from a frame whose slots point into `U`; the
resulting frame again points into `U`. -/
theorem execS_congr (sig : Sig) (U : List Key) (c1 c2 : Call)
    (hc : ∀ k ∈ U, ∀ st, c1 k st = c2 k st) :
    ∀ (s : Stmt) (fr : Frame) (st : St), (∀ k ∈ refs sig s, k ∈ U) → FrameIn U fr →
      execS sig c1 s fr st = execS sig c2 s fr st ∧ FrameIn U (execS sig c1 s fr st).2.1 := by
  intro s
  induction s with
  | skip => intro fr st _ hf; exact ⟨rfl, hf⟩
  | emit e => intro fr st _ hf; exact ⟨rfl, hf⟩
  | panic => intro fr st _ hf; exact ⟨rfl, hf⟩
  | seq a b iha ihb =>
    intro fr st hr hf
    have hra : ∀ k ∈ refs sig a, k ∈ U := fun k hk => hr k (by simp [refs, hk])
    have hrb : ∀ k ∈ refs sig b, k ∈ U := fun k hk => hr k (by simp [refs, hk])
    obtain ⟨ea, fa⟩ := iha fr st hra hf
    simp only [execS, ea]
    rw [ea] at fa
    rcases h : execS sig c2 a fr st with ⟨r, fr', st'⟩
    rw [h] at fa
    cases r with
    | ok => exact ihb fr' st' hrb fa
    | _ => exact ⟨rfl, fa⟩
  | call f τs =>
    intro fr st hr hf
    have hk : Key.inst f τs ∈ U := hr _ (by simp [refs])
    simp [execS, hc _ hk st]; exact hf
  | invoke k =>
    intro fr st hr hf
    have hk : k ∈ U := hr _ (by simp [refs])
    simp [execS, hc _ hk st]; exact hf
  | mcall tr m t =>
    intro fr st hr hf
    have hk : Key.meth tr m t ∈ U := hr _ (by simp [refs])
    simp [execS, hc _ hk st]; exact hf
  | drop t =>
    intro fr st hr hf
    have hk : Key.dropGlue t ∈ U := hr _ (by simp [refs])
    simp [execS, hc _ hk st]; exact hf
  | clone t =>
    intro fr st hr hf
    have hk : cloneKey t ∈ U := hr _ (by simp [refs])
    simp [execS, hc _ hk st]; exact hf
  | reify j f τs =>
    intro fr st hr hf
    refine ⟨rfl, ?_⟩
    intro j' v hv
    simp only [execS] at hv
    rcases List.mem_cons.mp hv with h | h
    · cases h; exact hr _ (by simp [refs])
    · exact hf j' v h
  | callPtr j =>
    intro fr st _ hf
    simp only [execS]
    rcases hl : fr.lookup j with _ | v
    · exact ⟨rfl, hf⟩
    · cases v with
      | fn k =>
        have hk : k ∈ U := hf j (.fn k) (lookup_mem fr j _ hl)
        simp [hc _ hk st]; exact hf
      | vt es d => exact ⟨rfl, hf⟩
  | unsize j t tr =>
    intro fr st hr hf
    refine ⟨rfl, ?_⟩
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
    · exact ⟨rfl, hf⟩
    · cases v with
      | fn k => exact ⟨rfl, hf⟩
      | vt es d =>
        simp only
        rcases hm : es.lookup m with _ | k
        · exact ⟨rfl, hf⟩
        · have hk : k ∈ U := (hf j (.vt es d) (lookup_mem fr j _ hl)).1 (m, k) (lookup_mem es m k hm)
          simp [hc _ hk st]; exact hf
  | dropDyn j =>
    intro fr st _ hf
    simp only [execS]
    rcases hl : fr.lookup j with _ | v
    · exact ⟨rfl, hf⟩
    · cases v with
      | fn k => exact ⟨rfl, hf⟩
      | vt es d =>
        have hk : d ∈ U := (hf j (.vt es d) (lookup_mem fr j _ hl)).2
        simp [hc _ hk st]; exact hf
  | onUnwind a b iha ihb =>
    intro fr st hr hf
    have hra : ∀ k ∈ refs sig a, k ∈ U := fun k hk => hr k (by simp [refs, hk])
    have hrb : ∀ k ∈ refs sig b, k ∈ U := fun k hk => hr k (by simp [refs, hk])
    obtain ⟨ea, fa⟩ := iha fr st hra hf
    simp only [execS, ea]
    rw [ea] at fa
    rcases h : execS sig c2 a fr st with ⟨r, fr', st'⟩
    rw [h] at fa
    cases r with
    | unwind =>
      obtain ⟨eb, fb⟩ := ihb fr' st' hrb fa
      simp only [eb]
      rw [eb] at fb
      rcases h2 : execS sig c2 b fr' st' with ⟨r2, fr2, st2⟩
      rw [h2] at fb
      cases r2 <;> first | exact ⟨rfl, fb⟩ | exact ⟨trivial, fb⟩
    | _ => exact ⟨rfl, fa⟩
  | cloneAgg ts =>
    intro fr st hr hf
    have h : ∀ t ∈ ts, cloneKey t ∈ U ∧ Key.dropGlue t ∈ U := by
      intro t ht
      exact ⟨hr _ (by simp only [refs, List.mem_append, List.mem_map]; exact Or.inl ⟨t, ht, rfl⟩),
        hr _ (by simp only [refs, List.mem_append, List.mem_map]; exact Or.inr ⟨t, ht, rfl⟩)⟩
    have e := aggClone_congr U c1 c2 hc ts [] st h (by simp)
    simp only [execS, e]
    exact ⟨trivial, hf⟩
  | guard s ih =>
    intro fr st hr hf
    have hrs : ∀ k ∈ refs sig s, k ∈ U := fun k hk => hr k (by simpa [refs] using hk)
    by_cases h0 : st.ctr = 0
    · simp [execS, h0]; exact hf
    · simp only [execS, h0, ite_false]
      exact ih fr _ hrs hf

/-- References of an emitted body lie in `T`, given (H1), edge-closure and (H3b). -/
theorem refs_in_of_covering (P : Program) (cfg : MonoCfg) (T : List Key)
    (hE : EdgesIn (edgesM P cfg) T) (h1 : CoversRefs P.sig cfg.E)
    (h3b : CanonicalRefs P cfg T) :
    ∀ k ∈ T, ∀ b, bodyM P cfg k = some b → ∀ k' ∈ refs P.sig b, k' ∈ T := by
  intro k hk b hb k' hk'
  have hn : k'.norm P = k' := h3b k hk b (by simp [hb]) k' hk'
  have hin : k'.norm P ∈ edgesM P cfg k := by
    simp only [edgesM, hb]
    exact List.mem_map.mpr ⟨k', h1 b k' hk', rfl⟩
  have := hE k hk _ hin
  rwa [hn] at this

/-- **Closure.** If `T` is closed under the collector's edges, the edge function covers every
runtime reference (H1), the synthesizer is total on the shim keys of `T` (H2t), referenced keys
are canonical (H3b), and the source defines every non-shim key of `T` (H0), then the table
restricted to `T` is a closed target. -/
theorem closed_of_edgesIn_covering_total_canonicalRefs_instDefined
    (P : Program) (cfg : MonoCfg) (T : List Key)
    (hE : EdgesIn (edgesM P cfg) T) (h1 : CoversRefs P.sig cfg.E) (h2t : SynthTotal cfg T)
    (h3b : CanonicalRefs P cfg T) (h0 : InstDefined P T) :
    Closed P.sig (tableM P cfg T) T := by
  intro k hk
  have hdef : (bodyM P cfg k).isSome := by
    unfold bodyM
    by_cases hs : k.isShim = true
    · simp only [hs, ite_true]; exact h2t k hk hs
    · have hs' : k.isShim = false := by simpa using hs
      simp only [hs', Bool.false_eq_true, ite_false]; exact h0 k hk hs'
  simp only [tableM, hk, ite_true]
  refine ⟨hdef, ?_⟩
  intro b hb k' hk'
  have hb' : bodyM P cfg k = some b := by simpa using hb
  exact refs_in_of_covering P cfg T hE h1 h3b k hk b hb' k' hk'

/-- Under edge-closure, (H1), (H2), (H3a) and (H3b): agreement of `M` and `S` on every key of `T`, at every fuel and state. -/
theorem runM_eq_runS_on_target (P : Program) (cfg : MonoCfg) (T : List Key)
    (hE : EdgesIn (edgesM P cfg) T) (h1 : CoversRefs P.sig cfg.E) (h2 : SynthAgrees P cfg T)
    (h3a : CanonicalKeys P T) (h3b : CanonicalRefs P cfg T) :
    ∀ (n : Nat), ∀ k ∈ T, ∀ st, runM P cfg T n k st = runS P n k st := by
  intro n
  induction n with
  | zero => intro k _ st; rfl
  | succ n ih =>
    intro k hk st
    have hc : ∀ k' ∈ T, ∀ st, runKey P.sig (tableM P cfg T) n k' st = runKey P.sig (srcDef P) n k' st :=
      fun k' hk' st => ih k' hk' st
    have hsrc : srcDef P k = srcDef0 P k := by simp [srcDef, h3a k hk]
    have hrefs := refs_in_of_covering P cfg T hE h1 h3b k hk
    unfold runM runS
    simp only [runKey, tableM, hk, ite_true, hsrc]
    by_cases hs : k.isShim = true
    · have hb : bodyM P cfg k = cfg.synth k := by simp [bodyM, hs]
      have hag := h2 k hk hs
      rw [hb]
      rw [hb] at hrefs
      rcases hsy : cfg.synth k with _ | b <;> rcases hsd : srcDef0 P k with _ | b' <;>
        simp only [hsy, hsd, OptEquiv] at hag
      · rfl
      · have e1 := (execS_congr P.sig T _ _ hc b [] st (hrefs b hsy) (by intro j v h; simp at h)).1
        have e2 := hag (runKey P.sig (srcDef P) n) st
        dsimp only
        rw [e1]
        exact e2
    · have hs' : k.isShim = false := by simpa using hs
      have hb : bodyM P cfg k = srcDef0 P k := by simp [bodyM, hs']
      rw [hb]
      rw [hb] at hrefs
      rcases hsd : srcDef0 P k with _ | b
      · rfl
      · have e1 := (execS_congr P.sig T _ _ hc b [] st (hrefs b hsd) (by intro j v h; simp at h)).1
        dsimp only
        rw [e1]

/-- **Adequacy.** If the roots lie in `T`, `T` is closed under the collector's edges, the edge
function covers every runtime reference (H1), the synthesizer agrees with the source on the shim
keys of `T` (H2), and keys are canonical (H3a, H3b), then the mono semantics restricted to `T`
agrees with the source semantics on every run from every root, at every fuel and initial state. -/
theorem runM_eq_runS_of_rootsIn_edgesIn_covering_agreeing_canonical
    (P : Program) (cfg : MonoCfg) (roots T : List Key)
    (hR : RootsIn roots T) (hE : EdgesIn (edgesM P cfg) T) (h1 : CoversRefs P.sig cfg.E)
    (h2 : SynthAgrees P cfg T) (h3a : CanonicalKeys P T) (h3b : CanonicalRefs P cfg T) :
    ∀ r ∈ roots, ∀ (n : Nat) (st : St), runM P cfg T n r st = runS P n r st :=
  fun r hr n st => runM_eq_runS_on_target P cfg T hE h1 h2 h3a h3b n r (hR r hr) st

end Toy.MonoShim
