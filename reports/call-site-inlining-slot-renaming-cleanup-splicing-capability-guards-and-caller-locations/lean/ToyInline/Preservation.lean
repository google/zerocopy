import ToyInline.ScopeLemmas

/-!
# What one inlining step preserves (fully proved)

`LocalsBounded` is preserved by `inlineFn` at a call site; `ScopesWF` preservation is
`scopesWF_inlineFn`. `BlocksBounded` is not preserved when the callee jumps out of range
(`cex_blocksBounded_inlineFn_oob`).
-/

namespace Toy.Inline

theorem foldl_maxSucc_ge (ρ : Nat → Local) :
    ∀ (l : List Nat) (init : Nat),
      init ≤ l.foldl (fun m i => max m (ρ i + 1)) init ∧
        ∀ x ∈ l, ρ x + 1 ≤ l.foldl (fun m i => max m (ρ i + 1)) init
  | [], init => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | a :: as, init => by
    have ih := foldl_maxSucc_ge ρ as (max init (ρ a + 1))
    refine ⟨Nat.le_trans (Nat.le_max_left _ _) ih.1, fun x hx => ?_⟩
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact Nat.le_trans (Nat.le_max_right _ _) ih.1
    · exact ih.2 x hx'

theorem lt_maxSucc (ρ : Nat → Local) (n i : Nat) (hi : i < n) : ρ i < maxSucc ρ n :=
  (foldl_maxSucc_ge ρ (List.range n) 0).2 i (List.mem_range.mpr hi)

theorem Operand.locals_rename (ρ : Nat → Local) (o : Operand) :
    (o.rename ρ).locals = o.locals.map ρ := by
  cases o <;> rfl

theorem Stmt.locals_rename (ρ : Nat → Local) (ns : Nat) (s : Stmt) :
    (s.rename ρ ns).locals = s.locals.map ρ := by
  cases s with
  | assign x rv =>
    cases rv <;> simp [Stmt.rename, Stmt.locals, Rvalue.rename, Rvalue.locals,
      Operand.locals_rename]
  | emit o => simp [Stmt.rename, Stmt.locals, Operand.locals_rename]
  | needCap _ => rfl
  | loc _ _ => rfl

/-- **`LocalsBounded` is preserved by one inlining step.** If block `b` of `F` is `B`, `B` ends
in the call `ci`, and `F` and `G` mention no undeclared locals, then the new body
`inlineFn F b B ci G cfg` (for any configuration) mentions no undeclared local. -/
theorem localsBounded_inlineFn (F : Fn) (b : BlockId) (B : Block) (ci : CallInfo) (G : Fn)
    (cfg : InlineCfg) (hB : nth? F.blocks b = some B) (hterm : B.term = .call ci)
    (hF : LocalsBounded F) (hG : LocalsBounded G) :
    LocalsBounded (inlineFn F b B ci G cfg) := by
  have hBmem : B ∈ F.blocks := nth?_mem F.blocks b B hB
  -- the bound of the new body
  let N := max (max F.nlocals (maxSucc (cfg.rename ci.dest) G.nlocals)) (retTempSucc cfg)
  have hNF : ∀ x, x < F.nlocals → x < N := fun x hx =>
    Nat.lt_of_lt_of_le hx (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _))
  have hNG : ∀ i, i < G.nlocals → cfg.rename ci.dest i < N := fun i hi =>
    Nat.lt_of_lt_of_le (lt_maxSucc _ _ _ hi)
      (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
  have hNt : ∀ t, cfg.ret = .temp t → t < N := fun t ht =>
    Nat.lt_of_lt_of_le (by simp [retTempSucc, ht]) (Nat.le_max_right _ _)
  have hBloc : ∀ x ∈ B.locals, x < F.nlocals := hF B hBmem
  have hdest : ci.dest < F.nlocals := hBloc ci.dest (by
    simp [Block.locals, hterm, Term.locals])
  have hargs : ∀ o ∈ ci.args, ∀ x ∈ o.locals, x < F.nlocals := fun o ho x hx =>
    hBloc x (by
      simp only [Block.locals, hterm, Term.locals, List.mem_append, List.mem_cons,
        List.mem_flatMap]
      exact Or.inr (Or.inr ⟨o, ho, hx⟩))
  intro B' hB' x hx
  show x < N
  simp only [inlineFn, List.mem_append] at hB'
  rcases hB' with (h1 | h2) | h3
  · rcases mem_of_mem_set F.blocks b _ B' h1 with hFmem | rfl
    · exact hNF x (hF B' hFmem x hx)
    · simp only [Block.locals, Term.locals, List.append_nil, List.flatMap_append,
        List.mem_append] at hx
      rcases hx with hx | hx
      · exact hNF x (hBloc x (by simp only [Block.locals, List.mem_append]; exact Or.inl hx))
      · simp only [prologue, List.flatMap_append, List.mem_append, List.mem_flatMap,
          List.mem_map] at hx
        rcases hx with ⟨st, ⟨i, hi, rfl⟩, hxs⟩ | ⟨st, hst, hxs⟩
        · have hi' : i < G.nlocals := List.mem_range.mp (List.mem_of_mem_tail hi)
          simp only [Stmt.locals, Rvalue.locals, List.mem_cons] at hxs
          rcases hxs with rfl | hxs
          · exact hNG i hi'
          · unfold argOr at hxs
            cases hn : nth? ci.args (i - 1) with
            | none => rw [hn] at hxs; simp [Operand.locals] at hxs
            | some o =>
              rw [hn] at hxs
              exact hNF x (hargs o (nth?_mem _ _ _ hn) x hxs)
        · split at hst
          · simp at hst
          · rename_i hn0
            simp only [List.mem_singleton] at hst
            subst hst
            simp only [Stmt.locals, Rvalue.locals, Operand.locals, List.mem_cons,
              List.mem_nil_iff, or_false] at hxs
            subst hxs
            exact hNG 0 (Nat.pos_of_ne_zero hn0)
  · cases ht : ci.target with
    | none => rw [ht] at h2; cases h2
    | some tgt =>
      rw [ht] at h2
      simp only [List.mem_singleton] at h2
      subst h2
      simp only [Block.locals, Term.locals, List.append_nil, List.mem_flatMap] at hx
      rcases hx with ⟨st, hst, hxs⟩
      cases hret : cfg.ret with
      | dest => simp [retStmts, hret] at hst
      | temp t =>
        simp only [retStmts, hret, List.mem_singleton] at hst
        subst hst
        simp only [Stmt.locals, Rvalue.locals, Operand.locals, List.mem_cons,
          List.mem_nil_iff, or_false] at hxs
        rcases hxs with rfl | rfl
        · exact hNF _ hdest
        · exact hNt _ hret
  · simp only [List.mem_map] at h3
    rcases h3 with ⟨BG, hBG, rfl⟩
    have hGloc : ∀ y ∈ BG.locals, y < G.nlocals := hG BG hBG
    simp only [SpliceCtx.block, Block.locals, List.mem_append, List.mem_flatMap,
      List.mem_map] at hx
    rcases hx with ⟨st, ⟨st0, hst0, rfl⟩, hxs⟩ | hxt
    · rw [Stmt.locals_rename] at hxs
      rcases List.mem_map.mp hxs with ⟨y, hy, rfl⟩
      exact hNG y (hGloc y (by
        simp only [Block.locals, List.mem_append, List.mem_flatMap]
        exact Or.inl ⟨st0, hst0, hy⟩))
    · have hGterm : ∀ y ∈ BG.term.locals, y < G.nlocals := fun y hy =>
        hGloc y (by simp only [Block.locals, List.mem_append]; exact Or.inr hy)
      cases hbt : BG.term with
      | goto _ => rw [hbt] at hxt; simp [SpliceCtx.term, Term.locals] at hxt
      | branch o z nz =>
        rw [hbt] at hxt
        simp only [SpliceCtx.term, Term.locals, Operand.locals_rename, List.mem_map] at hxt
        rcases hxt with ⟨y, hy, rfl⟩
        exact hNG y (hGterm y (by rw [hbt]; exact hy))
      | call ci2 =>
        rw [hbt] at hxt
        simp only [SpliceCtx.term, Term.locals, List.mem_cons, List.mem_flatMap,
          List.mem_map] at hxt
        rcases hxt with rfl | ⟨o', ⟨o, ho, rfl⟩, hxo⟩
        · exact hNG _ (hGterm _ (by rw [hbt]; simp [Term.locals]))
        · rw [Operand.locals_rename] at hxo
          rcases List.mem_map.mp hxo with ⟨y, hy, rfl⟩
          exact hNG y (hGterm y (by
            rw [hbt]; simp only [Term.locals, List.mem_cons, List.mem_flatMap]
            exact Or.inr ⟨o, ho, hy⟩))
      | ret =>
        rw [hbt] at hxt; simp only [SpliceCtx.term] at hxt
        split at hxt <;> simp [Term.locals] at hxt
      | resume =>
        rw [hbt] at hxt; simp only [SpliceCtx.term] at hxt
        split at hxt
        · split at hxt <;> simp [Term.locals] at hxt
        · split at hxt <;> simp [Term.locals] at hxt
      | panic _ => rw [hbt] at hxt; simp [SpliceCtx.term, Term.locals] at hxt
      | unreachable => rw [hbt] at hxt; simp [SpliceCtx.term, Term.locals] at hxt
      | abort => rw [hbt] at hxt; simp [SpliceCtx.term, Term.locals] at hxt

end Toy.Inline
