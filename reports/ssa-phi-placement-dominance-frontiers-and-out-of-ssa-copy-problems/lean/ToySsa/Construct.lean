import ToySsa.Lang
import ToySsa.Placement

/-!
SSA construction: φ placement at the iterated dominance frontier plus dominator-tree renaming
preserves the values of all variables, both at every block entry and at every block end, on
every walk from the entry; and the construction is in static single-assignment form.
-/
namespace Toy.Ssa

variable {n : Nat}

/-- The CFG has no cycles: every walk from a node back to itself is the null walk. -/
def Acyclic (G : Cfg n) : Prop := ∀ a p, Walk G a a p → p.length = 1

/-- A rank strictly increasing along edges certifies acyclicity. -/
theorem acyclic_of_rank (G : Cfg n) (r : Fin n → Nat)
    (hr : ∀ u v, G.edge u v = true → r u < r v) : Acyclic G := by
  have key : ∀ {a b : Fin n} {p : List (Fin n)}, Walk G a b p → r a + (p.length - 1) ≤ r b := by
    intro a b p hw
    induction hw with
    | single a => simp
    | @cons a' b' c' p' he hw ih =>
      have := hr _ _ he; have := hw.length_pos; simp; omega
  intro a p hw
  have := key hw; have := hw.length_pos; omega

theorem acyclic_diamond : Acyclic diamond :=
  acyclic_of_rank diamond (fun v => if v = 3 then 2 else if v = 0 then 0 else 1) (by decide)

theorem not_acyclic_loop4 : ¬ Acyclic loop4 := by
  intro h
  have := h 1 [1, 2, 1] (walk_of_isWalkB (by decide))
  simp at this

/-- In an acyclic CFG no reachable block has an edge into the entry (it would close a cycle
through the entry). -/
theorem entryNoReachablePreds_of_acyclic {G : Cfg n} (h : Acyclic G) : EntryNoReachablePreds G := by
  intro a ⟨p, hp⟩
  cases he : G.edge a G.entry with
  | false => rfl
  | true =>
    have h1 := h _ _ (hp.append_edge he)
    have h2 := hp.length_pos
    simp only [List.length_append, List.length_singleton] at h1
    omega

/-! ### Lemmas about the construction -/

theorem lastDefAux_or (x : Nat) : ∀ (i : Nat) (l : List (Nat × Exp Nat)) (acc : Option Nat),
    lastDefAux x i l acc = (lastDefAux x i l none).or acc
  | _, [], acc => by simp [lastDefAux]
  | i, xe :: rest, acc => by
    simp only [lastDefAux]
    rw [lastDefAux_or x (i + 1) rest (if xe.1 = x then some i else acc),
      lastDefAux_or x (i + 1) rest (if xe.1 = x then some i else none)]
    by_cases h : xe.1 = x
    · simp only [h, ite_true]
      cases lastDefAux x (i + 1) rest none <;> rfl
    · simp only [h, ite_false]
      cases lastDefAux x (i + 1) rest none <;> rfl

theorem lastDefAux_eq_none (x : Nat) : ∀ (i : Nat) (l : List (Nat × Exp Nat)),
    lastDefAux x i l none = none ↔ x ∉ l.map Prod.fst
  | _, [] => by simp [lastDefAux]
  | i, xe :: rest => by
    simp only [lastDefAux]
    rw [lastDefAux_or x (i + 1) rest, List.map_cons, List.mem_cons, not_or]
    rw [← lastDefAux_eq_none x (i + 1) rest]
    cases lastDefAux x (i + 1) rest none with
    | some j => simp
    | none =>
      by_cases h : xe.1 = x
      · simp [h]
      · simp [h, Ne.symm h]

theorem lastDef_eq_none (x : Nat) (l : List (Nat × Exp Nat)) :
    lastDef x l = none ↔ x ∉ l.map Prod.fst := lastDefAux_eq_none x 0 l

/-- At a definition point of `x` (or a φ for `x`), the live-out name is the block's own output
name. -/
theorem liveOutName_of_def (S : Src n) (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n)
    (x : Nat) (p : Fin n) (h : S.defPts x p ∨ phi x p = true) :
    liveOutName S phi idom x p = outName S x p := by
  unfold liveOutName outName
  rcases hl : lastDef x (S.body p) with _ | i
  · have hx : x ∉ (S.body p).map Prod.fst := (lastDef_eq_none x _).mp hl
    have hc : p = S.cfg.entry ∨ phi x p = true := by
      rcases h with (h | h) | h
      · exact Or.inl h
      · exact absurd h hx
      · exact Or.inr h
    simp only
    unfold topName
    rw [ite_eq_left hc]
  · rfl

/-- Elsewhere the live-out name is the output name of the renaming source. -/
theorem liveOutName_of_not_def (S : Src n) (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n)
    (x : Nat) (p : Fin n) (h : ¬ (S.defPts x p ∨ phi x p = true)) :
    liveOutName S phi idom x p = outName S x (idom x p) := by
  have hx : x ∉ (S.body p).map Prod.fst := fun hx => h (Or.inl (Or.inr hx))
  have hl : lastDef x (S.body p) = none := (lastDef_eq_none x _).mpr hx
  have hc : ¬ (p = S.cfg.entry ∨ phi x p = true) := fun hc => by
    rcases hc with hc | hc
    · exact h (Or.inl (Or.inl hc))
    · exact h (Or.inr hc)
  unfold liveOutName topName
  rw [hl]
  simp only
  rw [ite_eq_right hc]

theorem outName_block (S : Src n) (x : Nat) (d : Fin n) : (outName S x d).2.1 = d := by
  unfold outName
  cases lastDef x (S.body d) <;> rfl

private theorem parCopy_phi_names {c : Fin n} (f : Nat → SName n) (τ : SName n → Nat) :
    ∀ (l : List Nat) (x : Nat), x ∈ l →
      parCopy (l.map (fun y => (((y, c, 0) : SName n), f y))) τ (x, c, 0) = τ (f x)
  | [], _, h => by simp at h
  | y :: rest, x, h => by
    rw [List.map_cons, parCopy_cons]
    by_cases hxy : x = y
    · subst hxy; simp
    · have : ((x, c, 0) : SName n) ≠ (y, c, 0) := by simp [hxy]
      rw [ite_eq_right this]
      exact parCopy_phi_names f τ rest x (by simpa [hxy] using h)

/-- Entering a non-entry block `c`: the φ for `x ∈ vars` at `c` receives the live-out name of
`x` at the predecessor. -/
theorem ssaConstruct_enter_phi (S : Src n) (vars : List Nat) (phi : Nat → Fin n → Bool)
    (idom : Nat → Fin n → Fin n) {p c : Fin n} (hc : c ≠ S.cfg.entry) {x : Nat} (hx : x ∈ vars)
    (hphi : phi x c = true) (τ : SName n → Nat) :
    (ssaConstruct S vars phi idom).enter p c τ (x, c, 0) = τ (liveOutName S phi idom x p) := by
  have hm : (ssaConstruct S vars phi idom).phiMoves p c =
      (vars.filter (fun y => phi y c)).map
        (fun y => (((y, c, 0) : SName n), liveOutName S phi idom y p)) := by
    simp [SsaProg.phiMoves, ssaConstruct, hc, List.map_map, Function.comp_def]
  unfold SsaProg.enter
  rw [hm]
  exact parCopy_phi_names _ τ _ x (List.mem_filter.mpr ⟨hx, hphi⟩)

/-- Entering `c` leaves every name of another block unchanged. -/
theorem ssaConstruct_enter_other (S : Src n) (vars : List Nat) (phi : Nat → Fin n → Bool)
    (idom : Nat → Fin n → Fin n) (p c : Fin n) (τ : SName n → Nat) (nm : SName n)
    (hnm : nm.2.1 ≠ c) : (ssaConstruct S vars phi idom).enter p c τ nm = τ nm := by
  unfold SsaProg.enter
  apply parCopy_of_not_mem
  intro hmem
  simp only [SsaProg.phiMoves, ssaConstruct, List.map_map] at hmem
  split at hmem
  · simp at hmem
  · simp only [List.mem_map, List.mem_filter, Function.comp_def] at hmem
    obtain ⟨y, ⟨a, _, rfl⟩, rfl⟩ := hmem
    exact hnm rfl

/-- The environment after renaming `l` from instruction index `i`: the name of the last
assignment to `x` in `l`, else `env x`. -/
def envAfter (b : Fin n) (env : Nat → SName n) (i : Nat) (l : List (Nat × Exp Nat)) (x : Nat) :
    SName n :=
  match lastDefAux x i l none with
  | some j => (x, b, j + 1)
  | none => env x

theorem renameExp_eval {σs : Nat → Nat} {σt : SName n → Nat} {env : Nat → SName n}
    (h : ∀ y, σs y = σt (env y)) : ∀ e : Exp Nat, (renameExp env e).eval σt = e.eval σs
  | .lit _ => rfl
  | .var y => (h y).symm
  | .add a b => by
    simp only [renameExp, Exp.eval]
    rw [renameExp_eval h a, renameExp_eval h b]

/-- Renaming a block body preserves values: if every variable's value equals that of its
current name, and no current name is overwritten by a later renamed assignment, then after
the body every variable's value equals that of its name in `envAfter`. -/
theorem renameBody_correct (b : Fin n) : ∀ (l : List (Nat × Exp Nat)) (env : Nat → SName n)
    (i : Nat) (σs : Nat → Nat) (σt : SName n → Nat),
    (∀ y, σs y = σt (env y)) → (∀ y z k, i ≤ k → env y ≠ (z, b, k + 1)) →
    ∀ x, execBody (l.map (fun xe => Instr.assign xe.1 xe.2)) σs x =
      execBody (renameBody b env i l) σt (envAfter b env i l x)
  | [], env, i, σs, σt, h, _, x => by
    simp only [List.map_nil, execBody_nil, renameBody, envAfter, lastDefAux]
    exact h x
  | (z, e) :: rest, env, i, σs, σt, h, hfresh, x => by
    have hstep := renameBody_correct b rest (fun y => if y = z then (z, b, i + 1) else env y)
      (i + 1) (upd σs z (e.eval σs)) (upd σt (z, b, i + 1) ((renameExp env e).eval σt)) ?_ ?_ x
    · show execBody (rest.map (fun xe => Instr.assign xe.1 xe.2)) (upd σs z (e.eval σs)) x =
        execBody (renameBody b (fun y => if y = z then (z, b, i + 1) else env y) (i + 1) rest)
          (upd σt (z, b, i + 1) ((renameExp env e).eval σt)) (envAfter b env i ((z, e) :: rest) x)
      rw [hstep]
      congr 1
      unfold envAfter
      simp only [lastDefAux]
      rw [lastDefAux_or x (i + 1) rest (if z = x then some i else none)]
      cases lastDefAux x (i + 1) rest none with
      | some j => rfl
      | none =>
        by_cases hzx : z = x
        · subst hzx; simp
        · have hxz : ¬ x = z := fun h => hzx h.symm
          simp [hzx, hxz]
    · intro y
      by_cases hy : y = z
      · subst hy
        simp only [upd_apply, ite_true]
        exact (renameExp_eval h e).symm
      · simp only [upd_apply, hy, ite_false]
        rw [ite_eq_right (hfresh y z i (Nat.le_refl _))]
        exact h y
    · intro y z' k hk
      by_cases hy : y = z
      · simp only [hy, ite_true]
        intro he
        simp only [Prod.mk.injEq] at he
        omega
      · simp only [hy, ite_false]
        exact hfresh y z' k (by omega)

/-! ### Value preservation -/

/-- **SSA construction preserves values (block entries and block ends).** For a source program
in which no block reachable from the entry has an edge into the entry, whose assigned variables
all lie in `vars`, with a φ placement `phi x` equal to `DF⁺` of the definition points of `x`
(entry included; stated as the two inclusions `hphi_cover` and `hphi_within`) and a renaming
source `idom` that picks, at every reachable non-entry block without a φ for `x`, the nearest
strictly dominating definition point of `x` (φs included): on every walk from the entry, with
last block `b`, (1) on entry to `b` the source value of every variable `x` equals the value of
the SSA name `topName x b` that the constructed program reads for an upward-exposed use of `x`
at `b`, and (2) after `b`'s body the source value of `x` equals the value of the SSA name
`liveOutName x b`. -/
theorem ssaConstruct_preserves_values_of_entryNoReachablePreds (S : Src n) (vars : List Nat)
    (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n)
    (hnp : EntryNoReachablePreds S.cfg)
    (hvars : ∀ b x e, (x, e) ∈ S.body b → x ∈ vars)
    (hphi_cover : ∀ x b, IDF S.cfg (S.defPts x) b → phi x b = true)
    (hphi_within : ∀ x b, phi x b = true → IDF S.cfg (S.defPts x) b)
    (hidom : ∀ x b, Reachable S.cfg b → b ≠ S.cfg.entry → phi x b = false →
      NearestSDomDef S.cfg (fun d => S.defPts x d ∨ phi x d = true) b (idom x b))
    (σ : Nat → Nat) (σ' : SName n → Nat) (hinit : ∀ x, σ' (x, S.cfg.entry, 0) = σ x)
    {b : Fin n} {path : List (Fin n)} (hw : Walk S.cfg S.cfg.entry b path) (x : Nat) :
    S.toProg.atTop σ path x =
        (ssaConstruct S vars phi idom).atTop σ' path (topName S phi idom x b) ∧
      S.toProg.run σ path x =
        (ssaConstruct S vars phi idom).run σ' path (liveOutName S phi idom x b) := by
  -- Names read at the top of a reachable block are never overwritten by its renamed body.
  have hfresh : ∀ c, Reachable S.cfg c → ∀ y z k, 0 ≤ k →
      topName S phi idom y c ≠ (z, c, k + 1) := by
    intro c hc y z k _ he
    unfold topName at he
    split at he
    · simp only [Prod.mk.injEq] at he; omega
    · rename_i hcond
      have hce : c ≠ S.cfg.entry := fun h => hcond (Or.inl h)
      have hph : phi y c = false := by
        cases h : phi y c
        · rfl
        · exact absurd (Or.inr h) hcond
      have hsd := (hidom y c hc hce hph).2.1
      have hb := outName_block S y (idom y c)
      rw [he] at hb
      exact hsd.2 hb.symm
  -- One block body.
  have hbody : ∀ c, Reachable S.cfg c → ∀ (σs : Nat → Nat) (σt : SName n → Nat),
      (∀ y, σs y = σt (topName S phi idom y c)) → ∀ x,
      execBody (S.toProg.body c) σs x =
        execBody ((ssaConstruct S vars phi idom).body c) σt (liveOutName S phi idom x c) := by
    intro c hc σs σt h x
    exact renameBody_correct c (S.body c) _ 0 σs σt h (hfresh c hc) x
  -- One edge.
  have hstep : ∀ p c, Reachable S.cfg p → S.cfg.edge p c = true → ∀ (τ : SName n → Nat) x,
      (ssaConstruct S vars phi idom).enter p c τ (topName S phi idom x c) =
        τ (liveOutName S phi idom x p) := by
    intro p c hp hpc τ x
    have hc : c ≠ S.cfg.entry := by
      intro h
      have := hnp p hp
      rw [← h, hpc] at this
      exact absurd this (by decide)
    by_cases hphc : phi x c = true
    · have hxv : x ∈ vars := by
        apply Classical.byContradiction
        intro hxv
        have hdef : ∀ d, S.defPts x d → d = S.cfg.entry := by
          intro d hd
          rcases hd with hd | hd
          · exact hd
          · obtain ⟨xe, hxe, hx⟩ := List.mem_map.mp hd
            exact absurd (hvars d xe.1 xe.2 hxe) (by rw [hx]; exact hxv)
        exact hc (idf_entry_eq (IDF.mono hdef (hphi_within x c hphc)))
      unfold topName
      rw [ite_eq_left (Or.inr hphc)]
      exact ssaConstruct_enter_phi S vars phi idom hc hxv hphc τ
    · have hphc' : phi x c = false := by
        cases h : phi x c
        · rfl
        · exact absurd h hphc
      have hcr : Reachable S.cfg c := hp.of_edge hpc
      obtain ⟨hdD, hdS, hdN⟩ := hidom x c hcr hc hphc'
      have hsdom : ∀ q, (S.defPts x q ∨ phi x q = true) → Dom S.cfg q p → SDom S.cfg q c := by
        intro q hq hqp
        apply Classical.byContradiction
        intro hns
        have hdf : DF S.cfg q c := ⟨⟨p, hpc, hqp⟩, hns⟩
        have hidf : IDF S.cfg (S.defPts x) c := by
          rcases hq with hq | hq
          · exact IDF.base hq hdf
          · exact IDF.step (hphi_within x q hq) hdf
        exact hphc (hphi_cover x c hidf)
      have hdp : Dom S.cfg (idom x c) p := dom_pred_of_sdom hdS hpc
      have hname : outName S x (idom x c) = liveOutName S phi idom x p := by
        by_cases hpD : S.defPts x p ∨ phi x p = true
        · rw [liveOutName_of_def S phi idom x p hpD]
          have hpd : Dom S.cfg p (idom x c) := hdN p hpD (hsdom p hpD (dom_refl _ _))
          rw [dom_antisymm hpd hdp hp]
        · rw [liveOutName_of_not_def S phi idom x p hpD]
          have hpe : p ≠ S.cfg.entry := fun h => hpD (Or.inl (Or.inl h))
          have hphp : phi x p = false := by
            cases h : phi x p
            · rfl
            · exact absurd (Or.inr h) hpD
          obtain ⟨heD, heS, heN⟩ := hidom x p hp hpe hphp
          have hdsp : SDom S.cfg (idom x c) p := ⟨hdp, fun h => hpD (h ▸ hdD)⟩
          have hde : Dom S.cfg (idom x c) (idom x p) := heN _ hdD hdsp
          have hed : Dom S.cfg (idom x p) (idom x c) := hdN _ heD (hsdom _ heD heS.1)
          rw [dom_antisymm hed hde (Reachable.of_dom heS.1 hp)]
      have htop : topName S phi idom x c = outName S x (idom x c) := by
        unfold topName
        rw [ite_eq_right]
        intro h
        rcases h with h | h
        · exact hc h
        · exact hphc h
      rw [htop, ssaConstruct_enter_other S vars phi idom p c τ _ (by
        rw [outName_block]; exact hdS.2), hname]
  -- Induction along the walk.
  have key := Walk.snoc_induction (G := S.cfg) (a := S.cfg.entry)
    (fun c w => Reachable S.cfg c ∧
      (∀ x, S.toProg.atTop σ w x =
        (ssaConstruct S vars phi idom).atTop σ' w (topName S phi idom x c)) ∧
      (∀ x, S.toProg.run σ w x =
        (ssaConstruct S vars phi idom).run σ' w (liveOutName S phi idom x c)))
    ?_ ?_ hw
  · exact ⟨key.2.1 x, key.2.2 x⟩
  · have hr : Reachable S.cfg S.cfg.entry := ⟨[S.cfg.entry], Walk.single _⟩
    have htop : ∀ x, S.toProg.atTop σ [S.cfg.entry] x =
        (ssaConstruct S vars phi idom).atTop σ' [S.cfg.entry] (topName S phi idom x S.cfg.entry) := by
      intro x
      unfold topName
      rw [ite_eq_left (Or.inl rfl)]
      exact (hinit x).symm
    exact ⟨hr, htop, fun x => hbody _ hr σ σ' htop x⟩
  · intro w p c hwp hpc ⟨hp, _, ihrun⟩
    obtain ⟨l, rfl⟩ : ∃ l, w = l ++ [p] := ⟨_, hwp.eq_dropLast_append⟩
    have hcr : Reachable S.cfg c := hp.of_edge hpc
    have htop : ∀ x, S.toProg.atTop σ (l ++ [p] ++ [c]) x =
        (ssaConstruct S vars phi idom).atTop σ' (l ++ [p] ++ [c]) (topName S phi idom x c) := by
      intro x
      rw [Prog.atTop_append_singleton, SsaProg.atTop_snoc, hstep p c hp hpc, ← ihrun x]
    refine ⟨hcr, htop, fun x => ?_⟩
    rw [Prog.run_append_singleton, SsaProg.run_snoc]
    rw [← Prog.atTop_append_singleton, ← SsaProg.atTop_snoc]
    exact hbody c hcr _ _ htop x

/-- **Acyclic corollary.** On an acyclic CFG (edges into the entry are then possible only from
unreachable blocks) the conclusion of
`ssaConstruct_preserves_values_of_entryNoReachablePreds` holds under its other hypotheses. -/
theorem ssaConstruct_preserves_values_of_acyclic (S : Src n) (vars : List Nat)
    (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n)
    (hacyc : Acyclic S.cfg)
    (hvars : ∀ b x e, (x, e) ∈ S.body b → x ∈ vars)
    (hphi_cover : ∀ x b, IDF S.cfg (S.defPts x) b → phi x b = true)
    (hphi_within : ∀ x b, phi x b = true → IDF S.cfg (S.defPts x) b)
    (hidom : ∀ x b, Reachable S.cfg b → b ≠ S.cfg.entry → phi x b = false →
      NearestSDomDef S.cfg (fun d => S.defPts x d ∨ phi x d = true) b (idom x b))
    (σ : Nat → Nat) (σ' : SName n → Nat) (hinit : ∀ x, σ' (x, S.cfg.entry, 0) = σ x)
    {b : Fin n} {path : List (Fin n)} (hw : Walk S.cfg S.cfg.entry b path) (x : Nat) :
    S.toProg.atTop σ path x =
        (ssaConstruct S vars phi idom).atTop σ' path (topName S phi idom x b) ∧
      S.toProg.run σ path x =
        (ssaConstruct S vars phi idom).run σ' path (liveOutName S phi idom x b) :=
  ssaConstruct_preserves_values_of_entryNoReachablePreds S vars phi idom
    (entryNoReachablePreds_of_acyclic hacyc) hvars hphi_cover hphi_within hidom σ σ' hinit hw x

/-! ### Static single assignment -/

theorem renameBody_dests (b : Fin n) : ∀ (l : List (Nat × Exp Nat)) (env : Nat → SName n) (i : Nat),
    ((renameBody b env i l).flatMap Instr.dests).Nodup ∧
      ∀ v ∈ (renameBody b env i l).flatMap Instr.dests, v.2.1 = b ∧ i + 1 ≤ v.2.2
  | [], _, _ => by simp [renameBody]
  | (z, e) :: rest, env, i => by
    obtain ⟨hnd, hmem⟩ :=
      renameBody_dests b rest (fun y => if y = z then (z, b, i + 1) else env y) (i + 1)
    simp only [renameBody, List.flatMap_cons, Instr.dests, List.singleton_append]
    refine ⟨List.nodup_cons.mpr ⟨fun h => ?_, hnd⟩, fun v hv => ?_⟩
    · have := (hmem _ h).2; simp at this; omega
    · rcases List.mem_cons.mp hv with rfl | hv
      · simp
      · have := hmem v hv; exact ⟨this.1, by omega⟩

private theorem nodup_map_phiName (b : Fin n) :
    ∀ l : List Nat, l.Nodup → (l.map (fun y => ((y, b, 0) : SName n))).Nodup
  | [], _ => by simp
  | y :: rest, h => by
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, nodup_map_phiName b rest h.2⟩
    obtain ⟨y', hy', he⟩ := List.mem_map.mp hm
    simp only [Prod.mk.injEq] at he
    exact h.1 (he.1 ▸ hy')

private theorem nodup_filter_of_nodup {α : Type} (f : α → Bool) {l : List α} (h : l.Nodup) :
    (l.filter f).Nodup :=
  List.filter_sublist.nodup h

/-- Every static definition of block `b` of the constructed program is a name of block `b`; φ
names have index `0` and instruction names index at least `1`. -/
theorem ssaConstruct_defsAt_mem (S : Src n) (vars : List Nat) (phi : Nat → Fin n → Bool)
    (idom : Nat → Fin n → Fin n) (b : Fin n) (v : SName n)
    (hv : v ∈ (ssaConstruct S vars phi idom).defsAt b) :
    v.2.1 = b ∧ (v.2.2 = 0 → b ≠ S.cfg.entry) := by
  unfold SsaProg.defsAt at hv
  rcases List.mem_append.mp hv with hv | hv
  · simp only [ssaConstruct] at hv
    split at hv
    · simp at hv
    · rename_i hbe
      simp only [List.map_map, List.mem_map, Function.comp_def] at hv
      obtain ⟨y, _, rfl⟩ := hv
      exact ⟨rfl, fun _ => hbe⟩
  · have := (renameBody_dests b _ _ 0).2 v hv
    exact ⟨this.1, fun h => by omega⟩

/-- **The construction is in static single-assignment form** when `vars` has no duplicates:
every SSA name has at most one static definition, and no φ or instruction defines an entry name
`(x, entry, 0)` (these hold the initial values). -/
theorem ssaConstruct_singleAssignment_of_nodup (S : Src n) (vars : List Nat)
    (phi : Nat → Fin n → Bool) (idom : Nat → Fin n → Fin n) (hnd : vars.Nodup) :
    (ssaConstruct S vars phi idom).SingleAssignment ∧
      ∀ b x, ((x, S.cfg.entry, 0) : SName n) ∉ (ssaConstruct S vars phi idom).defsAt b := by
  refine ⟨⟨fun b => ?_, fun b b' v hv hv' => ?_⟩, fun b x hx => ?_⟩
  · unfold SsaProg.defsAt
    rw [List.nodup_append]
    obtain ⟨hbnd, hbmem⟩ := renameBody_dests b (S.body b) (fun x => topName S phi idom x b) 0
    refine ⟨?_, hbnd, ?_⟩
    · simp only [ssaConstruct]
      split
      · simp
      · rw [List.map_map]
        exact nodup_map_phiName b _ (nodup_filter_of_nodup _ hnd)
    · intro v₁ h₁ v₂ h₂ he
      subst he
      have h0 : v₁.2.2 = 0 := by
        simp only [ssaConstruct] at h₁
        split at h₁
        · simp at h₁
        · simp only [List.map_map, List.mem_map, Function.comp_def] at h₁
          obtain ⟨y, _, rfl⟩ := h₁
          rfl
      have := (hbmem v₁ h₂).2
      omega
  · exact (ssaConstruct_defsAt_mem S vars phi idom b v hv).1.symm.trans
      (ssaConstruct_defsAt_mem S vars phi idom b' v hv').1
  · have h := ssaConstruct_defsAt_mem S vars phi idom b _ hx
    exact h.2 rfl h.1.symm

/-! ### A witness: the diamond with one assignment -/

/-- Diamond source program: block `1` does `x := x + 1` (`x = 0`); no other assignment. -/
def diamondSrc : Src 4 where
  cfg := diamond
  body b := if b = 1 then [(0, .add (.var 0) (.lit 1))] else []

/-- φ placement for `diamondSrc`: a φ for `x = 0` at the join `3`. -/
def diamondPhi (x : Nat) (b : Fin 4) : Bool := decide (x = 0) && decide (b = 3)

/-- Renaming source for `diamondSrc`: the entry everywhere. -/
def diamondIdom (_ : Nat) (_ : Fin 4) : Fin 4 := 0

theorem diamondSrc_assigns_only_zero : ∀ b : Fin 4, ∀ xe ∈ diamondSrc.body b, xe.1 = 0 := by
  decide

theorem diamondSrc_defPts_ne {x : Nat} (hx : x ≠ 0) {b : Fin 4} (h : diamondSrc.defPts x b) :
    b = diamond.entry := by
  rcases h with h | h
  · exact h
  · obtain ⟨xe, hxe, rfl⟩ := List.mem_map.mp h
    exact absurd (diamondSrc_assigns_only_zero b xe hxe) hx

theorem diamondSrc_defPts_zero {b : Fin 4} (h : diamondSrc.defPts 0 b) :
    (decide (b = 0) || decide (b = 1)) = true := by
  revert h; revert b; unfold Src.defPts; decide

theorem diamondSrc_hvars : ∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0] := by
  intro b x e h
  have := diamondSrc_assigns_only_zero b (x, e) h
  simp_all

theorem diamondSrc_hphi : ∀ x b, diamondPhi x b = true ↔ IDF diamond (diamondSrc.defPts x) b := by
  intro x b
  by_cases hx : x = 0
  · subst hx
    constructor
    · intro h
      have hb : b = 3 := by simpa [diamondPhi] using h
      subst hb
      exact IDF.base (x := 1) (Or.inr (by decide)) df_example
    · intro h
      have h' := IDF.mono (S' := fun w => (decide (w = 0) || decide (w = 1)) = true)
        (fun w hw => diamondSrc_defPts_zero hw) h
      have := idf_subset_of_check (G := diamond) (S := fun w => decide (w = 0) || decide (w = 1))
        (T := fun w => decide (w = 3)) (by decide) h'
      simpa [diamondPhi] using this
  · have hf : diamondPhi x b = false := by simp [diamondPhi, hx]
    rw [hf]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h
      exact absurd (IDF.mono (fun w hw => diamondSrc_defPts_ne hx hw) h)
        (not_idf_entry entryNoPreds_diamond b)

theorem diamondSrc_hidom : ∀ x b, Reachable diamond b → b ≠ diamond.entry →
    diamondPhi x b = false →
    NearestSDomDef diamond (fun d => diamondSrc.defPts x d ∨ diamondPhi x d = true) b
      (diamondIdom x b) := by
  intro x b _ hbe hphi
  refine ⟨Or.inl (Or.inl rfl), ⟨entry_dom diamond b, fun h => hbe h.symm⟩, ?_⟩
  intro d' hd' hsd
  by_cases hx : x = 0
  · subst hx
    have hb3 : b ≠ 3 := by intro h; subst h; simp [diamondPhi] at hphi
    have key : ∀ d' b : Fin 4, b ≠ 0 → b ≠ 3 → d' ≠ 0 → avoidSet diamond d' b = true ∨ d' = b := by
      decide
    by_cases hd0 : d' = 0
    · subst hd0; exact dom_refl _ _
    · exfalso
      rcases key d' b hbe hb3 hd0 with h | h
      · exact not_dom_of_avoidSet h hsd.1
      · exact hsd.2 h
  · have hd0 : d' = 0 := by
      rcases hd' with h | h
      · exact diamondSrc_defPts_ne hx h
      · simp [diamondPhi, hx] at h
    subst hd0; exact dom_refl _ _

theorem diamondSrc_hphi_cover :
    ∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhi x b = true :=
  fun x b h => (diamondSrc_hphi x b).mpr h

theorem diamondSrc_hphi_within :
    ∀ x b, diamondPhi x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b :=
  fun x b h => (diamondSrc_hphi x b).mp h

theorem entryNoReachablePreds_diamond : EntryNoReachablePreds diamond :=
  entryNoReachablePreds_of_entryNoPreds entryNoPreds_diamond

/-- Non-vacuity: all hypotheses of `ssaConstruct_preserves_values_of_entryNoReachablePreds` hold
for the diamond program, with initial SSA store `σ' (x, b, i) = σ x`, on the walk `0 → 1 → 3`. -/
theorem ssaConstruct_hyps_nonvacuous :
    EntryNoReachablePreds diamondSrc.cfg ∧
    (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhi x b = true) ∧
    (∀ x b, diamondPhi x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry → diamondPhi x b = false →
      NearestSDomDef diamondSrc.cfg (fun d => diamondSrc.defPts x d ∨ diamondPhi x d = true) b
        (diamondIdom x b)) ∧
    (∀ x, (fun nm : SName 4 => (fun _ => 0 : Nat → Nat) nm.1) (x, diamondSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk diamondSrc.cfg diamondSrc.cfg.entry 3 [0, 1, 3] :=
  ⟨entryNoReachablePreds_diamond, diamondSrc_hvars, diamondSrc_hphi_cover, diamondSrc_hphi_within,
    diamondSrc_hidom, fun _ => rfl, walk_of_isWalkB (by decide)⟩

/-- Sanity check of both conclusions on the witness: at the top of `3` after `0 → 1 → 3` the
source has `x = 1` and the φ name for `x` at `3` holds `1`; at the end of block `1` on `0 → 1`
the source has `x = 1` and the live-out name of `x` at `1` holds `1`. -/
theorem ssaConstruct_diamond_example :
    diamondSrc.toProg.atTop (fun _ => 0) [0, 1, 3] 0 = 1 ∧
    (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).atTop (fun nm => (fun _ => 0) nm.1)
      [0, 1, 3] (topName diamondSrc diamondPhi diamondIdom 0 3) = 1 ∧
    diamondSrc.toProg.run (fun _ => 0) [0, 1] 0 = 1 ∧
    (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).run (fun nm => (fun _ => 0) nm.1)
      [0, 1] (liveOutName diamondSrc diamondPhi diamondIdom 0 1) = 1 := by
  decide

/-! ### Further witnesses -/

/-- An acyclic CFG `1 → 0 → 2` whose entry `0` has the unreachable predecessor `1`. -/
def acyclicEntryPredCfg : Cfg 3 := Cfg.ofEdges 3 [(1, 0), (0, 2)] 0

/-- Source program on `acyclicEntryPredCfg`: block `0` assigns `x := x + 1` (`x = 0`). -/
def acyclicEntryPredSrc : Src 3 where
  cfg := acyclicEntryPredCfg
  body b := if b = 0 then [(0, .add (.var 0) (.lit 1))] else []

/-- φ placement: `0 ∈ DF(0)` because the unreachable predecessor `1` of the entry is vacuously
dominated by `0`. The construction never emits a φ at the entry. -/
def epPhi (_ : Nat) (b : Fin 3) : Bool := decide (b = 0)

def epIdom (_ : Nat) (_ : Fin 3) : Fin 3 := 0

theorem acyclicEntryPred_props :
    Acyclic acyclicEntryPredCfg ∧ ¬ EntryNoPreds acyclicEntryPredCfg ∧
      EntryNoReachablePreds acyclicEntryPredCfg := by
  have hac : Acyclic acyclicEntryPredCfg :=
    acyclic_of_rank acyclicEntryPredCfg (fun v => if v = 1 then 0 else if v = 0 then 1 else 2)
      (by decide)
  exact ⟨hac, fun h => absurd (h 1) (by decide), entryNoReachablePreds_of_acyclic hac⟩

theorem acyclicEntryPredSrc_hphi :
    ∀ x b, epPhi x b = true ↔ IDF acyclicEntryPredCfg (acyclicEntryPredSrc.defPts x) b := by
  intro x b
  constructor
  · intro hb
    have hb0 : b = 0 := by simpa [epPhi] using hb
    subst hb0
    exact IDF.base (x := 0) (Or.inl rfl) (df_of_check (p := 1) (by decide))
  · intro hidf
    have h' := IDF.mono (S' := fun _ : Fin 3 => true = true) (fun _ _ => rfl) hidf
    have hsub := idf_subset_of_check (G := acyclicEntryPredCfg)
      (S := fun _ => true) (T := fun w => decide (w = 0)) (by decide) h'
    simpa [epPhi] using hsub

theorem acyclicEntryPredSrc_hidom :
    ∀ x b, Reachable acyclicEntryPredCfg b → b ≠ acyclicEntryPredCfg.entry →
      epPhi x b = false →
      NearestSDomDef acyclicEntryPredCfg
        (fun d => acyclicEntryPredSrc.defPts x d ∨ epPhi x d = true) b (epIdom x b) := by
  intro x b hreach hbe _
  have hb1 : b ≠ 1 := by
    intro h; subst h
    obtain ⟨p, hp⟩ := hreach
    have := not_walk_of_closed acyclicEntryPredCfg (fun v => decide (v ≠ 1)) (by decide) hp
      (by decide)
    exact absurd this (by decide)
  have hb2 : b = 2 := by
    have hcases : ∀ b : Fin 3, b = 0 ∨ b = 1 ∨ b = 2 := by decide
    rcases hcases b with rfl | rfl | rfl
    · exact absurd rfl hbe
    · exact absurd rfl hb1
    · rfl
  subst hb2
  refine ⟨Or.inl (Or.inl rfl), ⟨entry_dom acyclicEntryPredCfg 2, by simp [epIdom]⟩, ?_⟩
  intro d' hd' _
  have hd0 : d' = 0 := by
    rcases hd' with (h | h) | h
    · exact h
    · obtain ⟨xe, hxe, _⟩ := List.mem_map.mp h
      have : ∀ d' : Fin 3, 0 < (acyclicEntryPredSrc.body d').length → d' = 0 := by decide
      exact this d' (List.length_pos_of_mem hxe)
    · simpa [epPhi] using h
  subst hd0
  exact dom_refl _ _

/-- Non-vacuity on a CFG with an (unreachable) edge into the entry: all hypotheses hold while
`EntryNoPreds` fails, and both conclusions are checked on the walk `0 → 2`. -/
theorem ssaConstruct_entryPred_nonvacuous :
    ¬ EntryNoPreds acyclicEntryPredSrc.cfg ∧
    EntryNoReachablePreds acyclicEntryPredSrc.cfg ∧
    (∀ b x e, (x, e) ∈ acyclicEntryPredSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF acyclicEntryPredSrc.cfg (acyclicEntryPredSrc.defPts x) b → epPhi x b = true) ∧
    (∀ x b, epPhi x b = true → IDF acyclicEntryPredSrc.cfg (acyclicEntryPredSrc.defPts x) b) ∧
    (∀ x b, Reachable acyclicEntryPredSrc.cfg b → b ≠ acyclicEntryPredSrc.cfg.entry →
      epPhi x b = false →
      NearestSDomDef acyclicEntryPredSrc.cfg
        (fun d => acyclicEntryPredSrc.defPts x d ∨ epPhi x d = true) b (epIdom x b)) ∧
    (∀ x, (fun nm : SName 3 => (fun _ => 0 : Nat → Nat) nm.1)
      (x, acyclicEntryPredSrc.cfg.entry, 0) = (fun _ => 0 : Nat → Nat) x) ∧
    Walk acyclicEntryPredSrc.cfg acyclicEntryPredSrc.cfg.entry 2 [0, 2] ∧
    acyclicEntryPredSrc.toProg.atTop (fun _ => 0) [0, 2] 0 =
      (ssaConstruct acyclicEntryPredSrc [0] epPhi epIdom).atTop
        (fun nm => (fun _ => 0) nm.1) [0, 2] (topName acyclicEntryPredSrc epPhi epIdom 0 2) ∧
    acyclicEntryPredSrc.toProg.run (fun _ => 0) [0, 2] 0 =
      (ssaConstruct acyclicEntryPredSrc [0] epPhi epIdom).run
        (fun nm => (fun _ => 0) nm.1) [0, 2] (liveOutName acyclicEntryPredSrc epPhi epIdom 0 2) :=
  ⟨acyclicEntryPred_props.2.1, acyclicEntryPred_props.2.2, by
    intro b x e h
    have : ∀ b : Fin 3, ∀ xe ∈ acyclicEntryPredSrc.body b, xe.1 = 0 := by decide
    have := this b (x, e) h
    simp_all,
    fun x b h => (acyclicEntryPredSrc_hphi x b).mpr h,
    fun x b h => (acyclicEntryPredSrc_hphi x b).mp h,
    acyclicEntryPredSrc_hidom, fun _ => rfl, walk_of_isWalkB (by decide), by decide, by decide⟩

/-- `loop4` plus an unreachable isolated block `4`: cyclic and not all-reachable. -/
def loopUnreach5 : Cfg 5 := Cfg.ofEdges 5 [(0, 1), (1, 2), (2, 1), (1, 3)] 0

/-- While loop with an unreachable block: the body `2` does `x := x + 1` (`x = 0`). -/
def loopUnreachSrc : Src 5 where
  cfg := loopUnreach5
  body b := if b = 2 then [(0, .add (.var 0) (.lit 1))] else []

def luPhi (x : Nat) (b : Fin 5) : Bool := decide (x = 0) && decide (b = 1)

def luIdom (x : Nat) (b : Fin 5) : Fin 5 := if x = 0 ∧ (b = 2 ∨ b = 3) then 1 else 0

theorem loopUnreachSrc_defPts_ne {x : Nat} (hx : x ≠ 0) {b : Fin 5}
    (h : loopUnreachSrc.defPts x b) : b = loopUnreach5.entry := by
  rcases h with h | h
  · exact h
  · obtain ⟨xe, hxe, rfl⟩ := List.mem_map.mp h
    have : ∀ b : Fin 5, ∀ xe ∈ loopUnreachSrc.body b, xe.1 = 0 := by decide
    exact absurd (this b xe hxe) hx

theorem loopUnreachSrc_defPts_zero {b : Fin 5} (h : loopUnreachSrc.defPts 0 b) :
    (decide (b = 0) || decide (b = 2)) = true := by
  revert h; revert b; unfold Src.defPts; decide

theorem loopUnreachSrc_hphi :
    ∀ x b, luPhi x b = true ↔ IDF loopUnreach5 (loopUnreachSrc.defPts x) b := by
  intro x b
  by_cases hx : x = 0
  · subst hx
    constructor
    · intro h
      have hb : b = 1 := by simpa [luPhi] using h
      subst hb
      exact IDF.base (x := 2) (Or.inr (by decide)) (df_of_check (p := 2) (by decide))
    · intro h
      have h' := IDF.mono (S' := fun w => (decide (w = 0) || decide (w = 2)) = true)
        (fun w hw => loopUnreachSrc_defPts_zero hw) h
      have := idf_subset_of_check (G := loopUnreach5)
        (S := fun w => decide (w = 0) || decide (w = 2)) (T := fun w => decide (w = 1))
        (by decide) h'
      simpa [luPhi] using this
  · have hf : luPhi x b = false := by simp [luPhi, hx]
    rw [hf]
    constructor
    · intro h; exact absurd h (by decide)
    · intro h
      exact absurd (IDF.mono (fun w hw => loopUnreachSrc_defPts_ne hx hw) h)
        (not_idf_entry (by unfold EntryNoPreds; decide) b)

theorem loopUnreachSrc_hidom :
    ∀ x b, Reachable loopUnreach5 b → b ≠ loopUnreach5.entry → luPhi x b = false →
      NearestSDomDef loopUnreach5 (fun d => loopUnreachSrc.defPts x d ∨ luPhi x d = true) b
        (luIdom x b) := by
  intro x b hreach hbe hphi
  have hb4 : b ≠ 4 := by
    intro h; subst h
    obtain ⟨p, hp⟩ := hreach
    have := not_walk_of_closed loopUnreach5 (fun v => decide (v ≠ 4)) (by decide) hp (by decide)
    exact absurd this (by decide)
  by_cases hx : x = 0
  · subst hx
    have hb1 : b ≠ 1 := fun h => by subst h; simp [luPhi] at hphi
    have hb23 : b = 2 ∨ b = 3 := by
      have hcases : ∀ b : Fin 5, b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by decide
      rcases hcases b with rfl | rfl | rfl | rfl | rfl
      · exact absurd rfl hbe
      · exact absurd rfl hb1
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hb4
    rcases hb23 with rfl | rfl
    · refine ⟨Or.inr (by decide), ⟨dom_of_domCheck (by decide), by decide⟩, ?_⟩
      intro d' hd' hsd
      rcases hd' with (h | h) | h
      · subst h; exact entry_dom loopUnreach5 1
      · obtain ⟨xe, hxe, _⟩ := List.mem_map.mp h
        have : ∀ d' : Fin 5, 0 < (loopUnreachSrc.body d').length → d' = 2 := by decide
        have hd2 := this d' (List.length_pos_of_mem hxe)
        subst hd2; exact absurd rfl hsd.2
      · have hd1 : d' = 1 := by simpa [luPhi] using h
        subst hd1; exact dom_refl _ _
    · refine ⟨Or.inr (by decide), ⟨dom_of_domCheck (by decide), by decide⟩, ?_⟩
      intro d' hd' hsd
      rcases hd' with (h | h) | h
      · subst h; exact entry_dom loopUnreach5 1
      · obtain ⟨xe, hxe, _⟩ := List.mem_map.mp h
        have : ∀ d' : Fin 5, 0 < (loopUnreachSrc.body d').length → d' = 2 := by decide
        have hd2 := this d' (List.length_pos_of_mem hxe)
        subst hd2
        exact absurd hsd.1 (not_dom_of_avoidSet (by decide))
      · have hd1 : d' = 1 := by simpa [luPhi] using h
        subst hd1; exact dom_refl _ _
  · have hid0 : luIdom x b = 0 := by simp [luIdom, hx]
    rw [hid0]
    refine ⟨Or.inl (Or.inl rfl), ⟨entry_dom loopUnreach5 b, fun h => hbe h.symm⟩, ?_⟩
    intro d' hd' _
    rcases hd' with h | h
    · rw [loopUnreachSrc_defPts_ne hx h]; exact dom_refl _ _
    · simp [luPhi, hx] at h

/-- Non-vacuity on a cyclic CFG with an unreachable block and a renaming source that picks the
loop-header φ: all hypotheses hold, and both conclusions are checked after two loop trips. -/
theorem ssaConstruct_cyclic_unreach_nonvacuous :
    ¬ Acyclic loopUnreach5 ∧ ¬ AllReachable loopUnreach5 ∧
    EntryNoReachablePreds loopUnreachSrc.cfg ∧
    (∀ b x e, (x, e) ∈ loopUnreachSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF loopUnreachSrc.cfg (loopUnreachSrc.defPts x) b → luPhi x b = true) ∧
    (∀ x b, luPhi x b = true → IDF loopUnreachSrc.cfg (loopUnreachSrc.defPts x) b) ∧
    (∀ x b, Reachable loopUnreachSrc.cfg b → b ≠ loopUnreachSrc.cfg.entry → luPhi x b = false →
      NearestSDomDef loopUnreachSrc.cfg (fun d => loopUnreachSrc.defPts x d ∨ luPhi x d = true) b
        (luIdom x b)) ∧
    (∀ x, (fun nm : SName 5 => (fun _ => 0 : Nat → Nat) nm.1)
      (x, loopUnreachSrc.cfg.entry, 0) = (fun _ => 0 : Nat → Nat) x) ∧
    Walk loopUnreachSrc.cfg loopUnreachSrc.cfg.entry 3 [0, 1, 2, 1, 2, 1, 3] ∧
    loopUnreachSrc.toProg.atTop (fun _ => 0) [0, 1, 2, 1, 2, 1, 3] 0 = 2 ∧
    (ssaConstruct loopUnreachSrc [0] luPhi luIdom).atTop (fun nm => (fun _ => 0) nm.1)
      [0, 1, 2, 1, 2, 1, 3] (topName loopUnreachSrc luPhi luIdom 0 3) = 2 ∧
    loopUnreachSrc.toProg.run (fun _ => 0) [0, 1, 2, 1, 2] 0 = 2 ∧
    (ssaConstruct loopUnreachSrc [0] luPhi luIdom).run (fun nm => (fun _ => 0) nm.1)
      [0, 1, 2, 1, 2] (liveOutName loopUnreachSrc luPhi luIdom 0 2) = 2 := by
  refine ⟨?_, ?_, entryNoReachablePreds_of_entryNoPreds (by unfold EntryNoPreds; decide), ?_,
    fun x b h => (loopUnreachSrc_hphi x b).mpr h, fun x b h => (loopUnreachSrc_hphi x b).mp h,
    loopUnreachSrc_hidom, fun _ => rfl, walk_of_isWalkB (by decide), by decide, by decide,
    by decide, by decide⟩
  · intro h
    have := h 1 [1, 2, 1] (walk_of_isWalkB (by decide))
    simp at this
  · intro h
    obtain ⟨p, hp⟩ := h 4
    have := not_walk_of_closed loopUnreach5 (fun v => decide (v ≠ 4)) (by decide) hp (by decide)
    exact absurd this (by decide)
  · intro b x e h
    have : ∀ b : Fin 5, ∀ xe ∈ loopUnreachSrc.body b, xe.1 = 0 := by decide
    have := this b (x, e) h
    simp_all

/-- Non-vacuity of `ssaConstruct_singleAssignment_of_nodup` (`vars = [0]`) and a negative example:
with the duplicated list `vars = [0, 0]` the diamond construction defines the φ name `(0, 3, 0)`
twice, so it is not in static single-assignment form. -/
theorem ssaConstruct_singleAssignment_needs_nodup :
    [0].Nodup ∧ ¬ [0, 0].Nodup ∧
    ¬ (ssaConstruct diamondSrc [0, 0] diamondPhi diamondIdom).SingleAssignment := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h.1 3
  revert this
  decide

/-! ### Counterexamples for the hypotheses of SSA construction -/

/-- Single entry block with a self-loop doing `x := x + 1`. -/
def entryLoopSrc : Src 1 where
  cfg := entryLoop1
  body _ := [(0, .add (.var 0) (.lit 1))]

/-- `EntryNoReachablePreds` is necessary: with a reachable edge back into the entry, the entry
needs a φ that the construction (which never puts φs at the entry) does not emit; all other
hypotheses hold and the first conclusion fails on `[0, 0]`. -/
theorem ssaConstruct_needs_entryNoReachablePreds :
    ¬ EntryNoReachablePreds entryLoopSrc.cfg ∧
    (∀ b x e, (x, e) ∈ entryLoopSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF entryLoopSrc.cfg (entryLoopSrc.defPts x) b →
      (fun _ _ => true : Nat → Fin 1 → Bool) x b = true) ∧
    (∀ x b, (fun _ _ => true : Nat → Fin 1 → Bool) x b = true →
      IDF entryLoopSrc.cfg (entryLoopSrc.defPts x) b) ∧
    (∀ x b, Reachable entryLoopSrc.cfg b → b ≠ entryLoopSrc.cfg.entry →
      (fun _ _ => true : Nat → Fin 1 → Bool) x b = false →
      NearestSDomDef entryLoopSrc.cfg
        (fun d => entryLoopSrc.defPts x d ∨ (fun _ _ => true : Nat → Fin 1 → Bool) x d = true) b
        ((fun _ _ => 0 : Nat → Fin 1 → Fin 1) x b)) ∧
    (∀ x, (fun nm : SName 1 => (fun _ => 0 : Nat → Nat) nm.1) (x, entryLoopSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk entryLoopSrc.cfg entryLoopSrc.cfg.entry 0 [0, 0] ∧
    ¬ (entryLoopSrc.toProg.atTop (fun _ => 0) [0, 0] 0 =
        (ssaConstruct entryLoopSrc [0] (fun _ _ => true) (fun _ _ => 0)).atTop
          (fun nm => (fun _ => 0) nm.1) [0, 0]
          (topName entryLoopSrc (fun _ _ => true) (fun _ _ => 0) 0 0) ∧
      entryLoopSrc.toProg.run (fun _ => 0) [0, 0] 0 =
        (ssaConstruct entryLoopSrc [0] (fun _ _ => true) (fun _ _ => 0)).run
          (fun nm => (fun _ => 0) nm.1) [0, 0]
          (liveOutName entryLoopSrc (fun _ _ => true) (fun _ _ => 0) 0 0)) := by
  refine ⟨fun h => absurd (h 0 ⟨[0], Walk.single _⟩) (by decide), ?_, ?_, ?_, ?_, fun _ => rfl,
    walk_of_isWalkB (by decide), fun h => absurd h.1 (by decide)⟩
  · intro b x e h
    simp [entryLoopSrc] at h
    simp [h.1]
  · intro _ _ _; rfl
  · intro x b _
    have hb : b = 0 := (by decide : ∀ b : Fin 1, b = 0) b
    subst hb
    exact IDF.base (G := entryLoopSrc.cfg) (S := entryLoopSrc.defPts x) (x := 0) (y := 0)
      (Or.inl rfl) (df_of_check (G := entryLoop1) (p := 0) (by decide))
  · intro x b _ hb
    have h0 : ∀ b : Fin 1, b = 0 := by decide
    exact absurd ((h0 b).trans (h0 _).symm) hb

/-- `Acyclic` is necessary in `ssaConstruct_preserves_values_of_acyclic`: on the entry self-loop
program, which is not acyclic, every other hypothesis of the acyclic corollary holds and its
two-part conclusion fails on `[0, 0]`. -/
theorem ssaConstruct_acyclic_corollary_needs_acyclic :
    ¬ Acyclic entryLoopSrc.cfg ∧
    (∀ b x e, (x, e) ∈ entryLoopSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF entryLoopSrc.cfg (entryLoopSrc.defPts x) b →
      (fun _ _ => true : Nat → Fin 1 → Bool) x b = true) ∧
    (∀ x b, (fun _ _ => true : Nat → Fin 1 → Bool) x b = true →
      IDF entryLoopSrc.cfg (entryLoopSrc.defPts x) b) ∧
    (∀ x b, Reachable entryLoopSrc.cfg b → b ≠ entryLoopSrc.cfg.entry →
      (fun _ _ => true : Nat → Fin 1 → Bool) x b = false →
      NearestSDomDef entryLoopSrc.cfg
        (fun d => entryLoopSrc.defPts x d ∨ (fun _ _ => true : Nat → Fin 1 → Bool) x d = true) b
        ((fun _ _ => 0 : Nat → Fin 1 → Fin 1) x b)) ∧
    (∀ x, (fun nm : SName 1 => (fun _ => 0 : Nat → Nat) nm.1) (x, entryLoopSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk entryLoopSrc.cfg entryLoopSrc.cfg.entry 0 [0, 0] ∧
    ¬ (entryLoopSrc.toProg.atTop (fun _ => 0) [0, 0] 0 =
        (ssaConstruct entryLoopSrc [0] (fun _ _ => true) (fun _ _ => 0)).atTop
          (fun nm => (fun _ => 0) nm.1) [0, 0]
          (topName entryLoopSrc (fun _ _ => true) (fun _ _ => 0) 0 0) ∧
      entryLoopSrc.toProg.run (fun _ => 0) [0, 0] 0 =
        (ssaConstruct entryLoopSrc [0] (fun _ _ => true) (fun _ _ => 0)).run
          (fun nm => (fun _ => 0) nm.1) [0, 0]
          (liveOutName entryLoopSrc (fun _ _ => true) (fun _ _ => 0) 0 0)) := by
  have h := ssaConstruct_needs_entryNoReachablePreds
  exact ⟨fun hac => h.1 (entryNoReachablePreds_of_acyclic hac),
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- φ placement covering `DF⁺` is necessary: the diamond program with no φs and entry renaming
satisfies every other hypothesis (the entry is the nearest strictly dominating definition point
of every non-entry block when no φ exists), yet reads the initial `x` at `3`. -/
theorem ssaConstruct_needs_phi_cover :
    EntryNoReachablePreds diamondSrc.cfg ∧
    (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0]) ∧
    ¬ (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b →
      (fun _ _ => false : Nat → Fin 4 → Bool) x b = true) ∧
    (∀ x b, (fun _ _ => false : Nat → Fin 4 → Bool) x b = true →
      IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry →
      (fun _ _ => false : Nat → Fin 4 → Bool) x b = false →
      NearestSDomDef diamondSrc.cfg
        (fun d => diamondSrc.defPts x d ∨ (fun _ _ => false : Nat → Fin 4 → Bool) x d = true) b
        (diamondIdom x b)) ∧
    (∀ x, (fun nm : SName 4 => (fun _ => 0 : Nat → Nat) nm.1) (x, diamondSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk diamondSrc.cfg diamondSrc.cfg.entry 3 [0, 1, 3] ∧
    ¬ (diamondSrc.toProg.atTop (fun _ => 0) [0, 1, 3] 0 =
        (ssaConstruct diamondSrc [0] (fun _ _ => false) diamondIdom).atTop
          (fun nm => (fun _ => 0) nm.1) [0, 1, 3]
          (topName diamondSrc (fun _ _ => false) diamondIdom 0 3) ∧
      diamondSrc.toProg.run (fun _ => 0) [0, 1, 3] 0 =
        (ssaConstruct diamondSrc [0] (fun _ _ => false) diamondIdom).run
          (fun nm => (fun _ => 0) nm.1) [0, 1, 3]
          (liveOutName diamondSrc (fun _ _ => false) diamondIdom 0 3)) := by
  refine ⟨entryNoReachablePreds_diamond, diamondSrc_hvars, ?_, fun _ _ h => by simp at h,
    ?_, fun _ => rfl, walk_of_isWalkB (by decide), fun h => absurd h.1 (by decide)⟩
  · intro h
    have := h 0 3 (IDF.base (x := 1) (Or.inr (by decide)) df_example)
    exact absurd this (by decide)
  · intro x b _ hbe _
    refine ⟨Or.inl (Or.inl rfl), ⟨entry_dom diamond b, fun h => hbe h.symm⟩, ?_⟩
    intro d' hd' hsd
    have hd'' : diamondSrc.defPts x d' := by
      rcases hd' with h | h
      · exact h
      · simp at h
    by_cases hd0 : d' = 0
    · subst hd0; exact dom_refl _ _
    · exfalso
      have hd1 : d' = 1 := by
        rcases hd'' with h | h
        · exact absurd h hd0
        · obtain ⟨xe, hxe, _⟩ := List.mem_map.mp h
          have : ∀ d' : Fin 4, 0 < (diamondSrc.body d').length → d' = 1 := by decide
          exact this d' (List.length_pos_of_mem hxe)
      subst hd1
      have key : ∀ b : Fin 4, b ≠ 0 → avoidSet diamond 1 b = true ∨ b = 1 := by decide
      rcases key b hbe with h | h
      · exact not_dom_of_avoidSet h hsd.1
      · exact hsd.2 h.symm

/-- Diamond placement plus a spurious φ for the variable `1`, which is outside `vars = [0]`, at
every non-entry block. -/
def diamondPhiSpurious (x : Nat) (b : Fin 4) : Bool :=
  diamondPhi x b || (decide (x = 1) && decide (b ≠ 0))

theorem diamondPhiSpurious_hidom : ∀ x b, Reachable diamond b → b ≠ diamond.entry →
    diamondPhiSpurious x b = false →
    NearestSDomDef diamond (fun d => diamondSrc.defPts x d ∨ diamondPhiSpurious x d = true) b
      (diamondIdom x b) := by
  intro x b hr hbe hf
  have hx1 : x ≠ 1 := by
    intro h; subst h
    have : b ≠ 0 := hbe
    simp [diamondPhiSpurious, this] at hf
  have hdefs : (fun d => diamondSrc.defPts x d ∨ diamondPhiSpurious x d = true) =
      (fun d => diamondSrc.defPts x d ∨ diamondPhi x d = true) := by
    funext d
    simp [diamondPhiSpurious, hx1]
  have hf' : diamondPhi x b = false := by
    simp [diamondPhiSpurious, hx1] at hf
    simpa using hf
  rw [hdefs]
  exact diamondSrc_hidom x b hr hbe hf'

/-- φ placement within `DF⁺` is necessary: a spurious φ for a variable outside `vars` is read by
`topName` but never emitted by the construction, so the SSA program reads an uninitialized name
(here holding `7`); all other hypotheses hold. -/
theorem ssaConstruct_needs_phi_within :
    EntryNoReachablePreds diamondSrc.cfg ∧
    (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhiSpurious x b = true) ∧
    ¬ (∀ x b, diamondPhiSpurious x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry →
      diamondPhiSpurious x b = false →
      NearestSDomDef diamondSrc.cfg
        (fun d => diamondSrc.defPts x d ∨ diamondPhiSpurious x d = true) b (diamondIdom x b)) ∧
    (∀ x, (fun nm : SName 4 => if nm.2.1 = 0 then 0 else 7) (x, diamondSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk diamondSrc.cfg diamondSrc.cfg.entry 3 [0, 1, 3] ∧
    ¬ (diamondSrc.toProg.atTop (fun _ => 0) [0, 1, 3] 1 =
        (ssaConstruct diamondSrc [0] diamondPhiSpurious diamondIdom).atTop
          (fun nm => if nm.2.1 = 0 then 0 else 7) [0, 1, 3]
          (topName diamondSrc diamondPhiSpurious diamondIdom 1 3) ∧
      diamondSrc.toProg.run (fun _ => 0) [0, 1, 3] 1 =
        (ssaConstruct diamondSrc [0] diamondPhiSpurious diamondIdom).run
          (fun nm => if nm.2.1 = 0 then 0 else 7) [0, 1, 3]
          (liveOutName diamondSrc diamondPhiSpurious diamondIdom 1 3)) := by
  refine ⟨entryNoReachablePreds_diamond, diamondSrc_hvars, ?_, ?_, diamondPhiSpurious_hidom,
    fun _ => rfl, walk_of_isWalkB (by decide), fun h => absurd h.1 (by decide)⟩
  · intro x b h
    simp [diamondPhiSpurious, diamondSrc_hphi_cover x b h]
  · intro h
    have h1 := h 1 1 (by decide)
    have := (diamondSrc_hphi 1 1).mpr h1
    exact absurd this (by decide)

/-- Chain source: block `1` does `x := x + 1` (`x = 0`). -/
def chainSrc : Src 3 where
  cfg := chain3
  body b := if b = 1 then [(0, .add (.var 0) (.lit 1))] else []

/-- Dominator-tree renaming is necessary: renaming every use to the entry's value (the correct
choice at `2` is block `1`) satisfies every other hypothesis but reads the initial `x` at `2`. -/
theorem ssaConstruct_needs_nearestSDomDef :
    EntryNoReachablePreds chainSrc.cfg ∧
    (∀ b x e, (x, e) ∈ chainSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF chainSrc.cfg (chainSrc.defPts x) b →
      (fun _ _ => false : Nat → Fin 3 → Bool) x b = true) ∧
    (∀ x b, (fun _ _ => false : Nat → Fin 3 → Bool) x b = true →
      IDF chainSrc.cfg (chainSrc.defPts x) b) ∧
    ¬ (∀ x b, Reachable chainSrc.cfg b → b ≠ chainSrc.cfg.entry →
      (fun _ _ => false : Nat → Fin 3 → Bool) x b = false →
      NearestSDomDef chainSrc.cfg
        (fun d => chainSrc.defPts x d ∨ (fun _ _ => false : Nat → Fin 3 → Bool) x d = true) b
        ((fun _ _ => 0 : Nat → Fin 3 → Fin 3) x b)) ∧
    (∀ x, (fun nm : SName 3 => (fun _ => 0 : Nat → Nat) nm.1) (x, chainSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk chainSrc.cfg chainSrc.cfg.entry 2 [0, 1, 2] ∧
    ¬ (chainSrc.toProg.atTop (fun _ => 0) [0, 1, 2] 0 =
        (ssaConstruct chainSrc [0] (fun _ _ => false) (fun _ _ => 0)).atTop
          (fun nm => (fun _ => 0) nm.1) [0, 1, 2]
          (topName chainSrc (fun _ _ => false) (fun _ _ => 0) 0 2) ∧
      chainSrc.toProg.run (fun _ => 0) [0, 1, 2] 0 =
        (ssaConstruct chainSrc [0] (fun _ _ => false) (fun _ _ => 0)).run
          (fun nm => (fun _ => 0) nm.1) [0, 1, 2]
          (liveOutName chainSrc (fun _ _ => false) (fun _ _ => 0) 0 2)) := by
  have hdef : ∀ x (b : Fin 3), chainSrc.defPts x b → (decide (b = 0) || decide (b = 1)) = true := by
    intro x b h
    rcases h with h | h
    · subst h; decide
    · obtain ⟨xe, hxe, _⟩ := List.mem_map.mp h
      have : ∀ b : Fin 3, 0 < (chainSrc.body b).length →
          (decide (b = 0) || decide (b = 1)) = true := by decide
      exact this b (List.length_pos_of_mem hxe)
  refine ⟨entryNoReachablePreds_of_entryNoPreds (by unfold EntryNoPreds; decide), ?_, ?_,
    fun _ _ h => by simp at h, ?_, fun _ => rfl, walk_of_isWalkB (by decide),
    fun h => absurd h.1 (by decide)⟩
  · intro b x e h
    have : ∀ b : Fin 3, ∀ xe ∈ chainSrc.body b, xe.1 = 0 := by decide
    have := this b (x, e) h
    simp_all
  · intro x b h
    have h' := IDF.mono (S' := fun w => (decide (w = 0) || decide (w = 1)) = true)
      (fun w hw => hdef x w hw) h
    have := idf_subset_of_check (G := chain3) (S := fun w => decide (w = 0) || decide (w = 1))
      (T := fun _ => false) (by decide) h'
    exact absurd this (by decide)
  · intro h
    have h2 := h 0 2 ⟨[0, 1, 2], walk_of_isWalkB (by decide)⟩ (by decide) rfl
    obtain ⟨_, _, hn⟩ := h2
    exact not_dom_of_avoidSet (a := 1) (b := 0) (by decide)
      (hn 1 (Or.inl (Or.inr (by decide))) ⟨dom_of_domCheck (by decide), by decide⟩)

/-- The initial-store hypothesis is necessary: with the SSA entry names initialized to `5`
instead of the source values, the walk `[0]` already disagrees. -/
theorem ssaConstruct_needs_hinit :
    EntryNoReachablePreds diamondSrc.cfg ∧
    (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhi x b = true) ∧
    (∀ x b, diamondPhi x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry → diamondPhi x b = false →
      NearestSDomDef diamondSrc.cfg (fun d => diamondSrc.defPts x d ∨ diamondPhi x d = true) b
        (diamondIdom x b)) ∧
    ¬ (∀ x, (fun _ => 5 : SName 4 → Nat) (x, diamondSrc.cfg.entry, 0) = (fun _ => 0 : Nat → Nat) x) ∧
    Walk diamondSrc.cfg diamondSrc.cfg.entry 0 [0] ∧
    ¬ (diamondSrc.toProg.atTop (fun _ => 0) [0] 0 =
        (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).atTop (fun _ => 5) [0]
          (topName diamondSrc diamondPhi diamondIdom 0 0) ∧
      diamondSrc.toProg.run (fun _ => 0) [0] 0 =
        (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).run (fun _ => 5) [0]
          (liveOutName diamondSrc diamondPhi diamondIdom 0 0)) :=
  ⟨entryNoReachablePreds_diamond, diamondSrc_hvars, diamondSrc_hphi_cover, diamondSrc_hphi_within,
    diamondSrc_hidom, fun h => absurd (h 0) (by decide), walk_of_isWalkB (by decide),
    fun h => absurd h.1 (by decide)⟩

/-- Walks must start at the entry: the null walk at `3` (not a walk from the entry) exposes an
uninitialized φ name. -/
theorem ssaConstruct_needs_walk_from_entry :
    EntryNoReachablePreds diamondSrc.cfg ∧
    (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ [0]) ∧
    (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhi x b = true) ∧
    (∀ x b, diamondPhi x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry → diamondPhi x b = false →
      NearestSDomDef diamondSrc.cfg (fun d => diamondSrc.defPts x d ∨ diamondPhi x d = true) b
        (diamondIdom x b)) ∧
    (∀ x, (fun nm : SName 4 => if nm.2.1 = 0 ∧ nm.2.2 = 0 then 0 else 99)
      (x, diamondSrc.cfg.entry, 0) = (fun _ => 0 : Nat → Nat) x) ∧
    ¬ Walk diamondSrc.cfg diamondSrc.cfg.entry 3 [3] ∧
    ¬ (diamondSrc.toProg.atTop (fun _ => 0) [3] 0 =
        (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).atTop
          (fun nm => if nm.2.1 = 0 ∧ nm.2.2 = 0 then 0 else 99) [3]
          (topName diamondSrc diamondPhi diamondIdom 0 3) ∧
      diamondSrc.toProg.run (fun _ => 0) [3] 0 =
        (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).run
          (fun nm => if nm.2.1 = 0 ∧ nm.2.2 = 0 then 0 else 99) [3]
          (liveOutName diamondSrc diamondPhi diamondIdom 0 3)) :=
  ⟨entryNoReachablePreds_diamond, diamondSrc_hvars, diamondSrc_hphi_cover, diamondSrc_hphi_within,
    diamondSrc_hidom, fun _ => rfl, fun hw => absurd (hw.getElem_zero (by simp)) (by decide),
    fun h => absurd h.1 (by decide)⟩

/-- `vars` must cover the assigned variables: with `vars = []` the φ for `x` at `3` is not
emitted although `topName` reads it. -/
theorem ssaConstruct_needs_hvars :
    EntryNoReachablePreds diamondSrc.cfg ∧
    ¬ (∀ b x e, (x, e) ∈ diamondSrc.body b → x ∈ ([] : List Nat)) ∧
    (∀ x b, IDF diamondSrc.cfg (diamondSrc.defPts x) b → diamondPhi x b = true) ∧
    (∀ x b, diamondPhi x b = true → IDF diamondSrc.cfg (diamondSrc.defPts x) b) ∧
    (∀ x b, Reachable diamondSrc.cfg b → b ≠ diamondSrc.cfg.entry → diamondPhi x b = false →
      NearestSDomDef diamondSrc.cfg (fun d => diamondSrc.defPts x d ∨ diamondPhi x d = true) b
        (diamondIdom x b)) ∧
    (∀ x, (fun nm : SName 4 => (fun _ => 0 : Nat → Nat) nm.1) (x, diamondSrc.cfg.entry, 0) =
      (fun _ => 0 : Nat → Nat) x) ∧
    Walk diamondSrc.cfg diamondSrc.cfg.entry 3 [0, 1, 3] ∧
    ¬ (diamondSrc.toProg.atTop (fun _ => 0) [0, 1, 3] 0 =
        (ssaConstruct diamondSrc [] diamondPhi diamondIdom).atTop (fun nm => (fun _ => 0) nm.1)
          [0, 1, 3] (topName diamondSrc diamondPhi diamondIdom 0 3) ∧
      diamondSrc.toProg.run (fun _ => 0) [0, 1, 3] 0 =
        (ssaConstruct diamondSrc [] diamondPhi diamondIdom).run (fun nm => (fun _ => 0) nm.1)
          [0, 1, 3] (liveOutName diamondSrc diamondPhi diamondIdom 0 3)) := by
  refine ⟨entryNoReachablePreds_diamond, fun h => ?_, diamondSrc_hphi_cover, diamondSrc_hphi_within,
    diamondSrc_hidom, fun _ => rfl, walk_of_isWalkB (by decide), fun h => absurd h.1 (by decide)⟩
  have := h 1 0 (.add (.var 0) (.lit 1)) (by simp [diamondSrc])
  simp at this

/-- While loop source on `loop4`: the body block `2` does `x := x + 1` (`x = 0`). -/
def loopSrc : Src 4 where
  cfg := loop4
  body b := if b = 2 then [(0, .add (.var 0) (.lit 1))] else []

/-- φ for `x` at the header `1` (`DF⁺({0, 2}) = {1}`). -/
def loopPhi (x : Nat) (b : Fin 4) : Bool := decide (x = 0) && decide (b = 1)

/-- Renaming source: the header's φ for uses of `x` in the body and at the exit. -/
def loopIdom (x : Nat) (b : Fin 4) : Fin 4 := if x = 0 ∧ (b = 2 ∨ b = 3) then 1 else 0

/-- Sanity check of the construction on a loop (two trips then exit): the source has `x = 2` at
the exit, and the SSA program's name for `x` there holds `2`; at the end of the second trip
through the body, the live-out name of `x` holds `2`. -/
theorem ssaConstruct_loop_example :
    loopSrc.toProg.atTop (fun _ => 0) [0, 1, 2, 1, 2, 1, 3] 0 = 2 ∧
    (ssaConstruct loopSrc [0] loopPhi loopIdom).atTop (fun nm => (fun _ => 0) nm.1)
      [0, 1, 2, 1, 2, 1, 3] (topName loopSrc loopPhi loopIdom 0 3) = 2 ∧
    loopSrc.toProg.run (fun _ => 0) [0, 1, 2, 1, 2] 0 = 2 ∧
    (ssaConstruct loopSrc [0] loopPhi loopIdom).run (fun nm => (fun _ => 0) nm.1)
      [0, 1, 2, 1, 2] (liveOutName loopSrc loopPhi loopIdom 0 2) = 2 := by
  decide

/-- Non-vacuity of `ssaConstruct_singleAssignment_of_nodup`: the diamond construction with
`vars = [0]`. -/
theorem ssaConstruct_singleAssignment_nonvacuous :
    [0].Nodup ∧ (ssaConstruct diamondSrc [0] diamondPhi diamondIdom).SingleAssignment :=
  ⟨by decide, (ssaConstruct_singleAssignment_of_nodup diamondSrc [0] diamondPhi diamondIdom
    (by decide)).1⟩

end Toy.Ssa
