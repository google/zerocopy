import ToyLoanFlow.Analyses

/-!
# Inclusion of the location-insensitive checker in the location-sensitive one

* `lsLoanLive_overwrite_iff_liveLoanLive` / `lsAccepts_overwrite_iff_liveAccepts`: for every
  program and variance mode, the location-sensitive checker with kills at overwrites
  (`LS.Holds`, `KillMode.overwrite`) and the liveness-gated variant without kills
  (`LS.LiveHolds`) judge the same loans live, hence accept the same programs.
* `liveAccepts_of_wellTyped_of_nllAccepts`: every well-typed program accepted by
  `NLL.Accepts vm` is accepted by `LS.Accepts .overwrite vm`, for every variance mode `vm`.
-/

namespace Toy.LoanFlow

variable {n m : Nat}

namespace Incl

theorem killsAt_overwrite_false_of_liveAt {p : Prog n m} {v : Fin m} {q : Fin n}
    (hl : LiveAt p v q) : killsAt .overwrite p q v = false := by
  cases hl with
  | use hu => simp [killsAt, hu]
  | step hd _ _ => simp [killsAt, hd]

theorem liveAt_of_killsAt_overwrite_false {p : Prog n m} {v : Fin m} {q q' : Fin n}
    (hk : killsAt .overwrite p q v = false) (hq : q' ∈ p.succ q) (hl : LiveAt p v q') :
    LiveAt p v q := by
  by_cases hu : v ∈ (p.stmt q).uses
  · exact .use hu
  · have hd : v ∉ (p.stmt q).defs := by
      intro hd
      simp [killsAt, hd, hu] at hk
    exact .step hd hq hl

theorem fst_of_mem_relate {vm : VarMode} {T : List Mutbl} {a b : Fin m} {da db : Nat}
    {o₁ o₂ : Origin m} (h : (o₁, o₂) ∈ relate vm T a da b db) : o₁.1 = a ∨ o₁.1 = b := by
  simp only [relate, List.mem_flatMap, List.mem_range] at h
  obtain ⟨k, _, hk⟩ := h
  split at hk <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  · rcases hk with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact .inl rfl
    · exact .inr rfl
  · obtain ⟨rfl, _⟩ := hk
    exact .inl rfl

/-- The source origin of a generated constraint belongs to a local that the node uses or
overwrites. -/
theorem fst_mem_uses_or_defs_of_mem_gen {vm : VarMode} {p : Prog n m} {q : Fin n}
    {o₁ o₂ : Origin m} (h : (o₁, o₂) ∈ gen vm p q) :
    o₁.1 ∈ (p.stmt q).uses ∨ o₁.1 ∈ (p.stmt q).defs := by
  unfold gen at h
  cases hst : p.stmt q <;> rw [hst] at h
  · simp at h
  · rename_i mu d s
    simp only [List.mem_flatMap, List.mem_range] at h
    obtain ⟨k, _, hk⟩ := h
    split at hk <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    · rcases hk with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact .inl (by simp [Stmt.uses])
      · exact .inr (by simp [Stmt.defs])
    · obtain ⟨rfl, _⟩ := hk
      exact .inl (by simp [Stmt.uses])
  · rename_i d s
    rcases fst_of_mem_relate h with h1 | h1
    · exact .inl (by simp [Stmt.uses, h1])
    · exact .inr (by simp [Stmt.defs, h1])
  · simp at h
  · simp at h
  · rename_i q' s
    rcases fst_of_mem_relate h with h1 | h1
    · exact .inl (by simp [Stmt.uses, h1])
    · exact .inl (by simp [Stmt.uses, h1])
  · simp at h

theorem liveAt_of_mem_gen {vm : VarMode} {p : Prog n m} {q : Fin n} {o₁ o₂ : Origin m}
    (hg : (o₁, o₂) ∈ gen vm p q) (hd : o₁.1 ∉ (p.stmt q).defs) : LiveAt p o₁.1 q := by
  rcases fst_mem_uses_or_defs_of_mem_gen hg with hu | hdef
  · exact .use hu
  · exact absurd hdef hd

theorem subAt_left_live_or_killed {vm : VarMode} {p : Prog n m} {o₁ o₂ : Origin m}
    {q : Fin n} (h : LS.SubAt vm p o₁ o₂ q) :
    LiveAt p o₁.1 q ∨ killsAt .overwrite p q o₁.1 = true := by
  induction h with
  | @base o₁ o₂ q hg =>
    by_cases hu : o₁.1 ∈ (p.stmt q).uses
    · exact .inl (.use hu)
    · rcases fst_mem_uses_or_defs_of_mem_gen hg with hu' | hd
      · exact absurd hu' hu
      · exact .inr (by simp [killsAt, hd, hu])
  | trans _ _ ih₁ _ => exact ih₁
  | persist _ _ hl₁ _ _ => exact .inl hl₁

theorem holds_of_liveHolds {vm : VarMode} {p : Prog n m} {l : Fin n} {o : Origin m}
    {q : Fin n} (h : LS.LiveHolds vm p l o q) : LS.Holds .overwrite vm p l o q := by
  induction h with
  | intro hst => exact .intro hst
  | carry _ hq hl ih => exact .carry ih hq (killsAt_overwrite_false_of_liveAt hl)
  | step _ hq hg hd ih => exact .step ih hq hg hd
  | sub _ hs ih => exact .sub ih hs

theorem liveHolds_of_holds {vm : VarMode} {p : Prog n m} {l : Fin n} {o : Origin m}
    {q : Fin n} (h : LS.Holds .overwrite vm p l o q)
    (hneed : LiveAt p o.1 q ∨ killsAt .overwrite p q o.1 = true ∨
      ∃ q' ∈ p.succ q, LiveAt p o.1 q') :
    LS.LiveHolds vm p l o q := by
  induction h with
  | intro hst => exact .intro hst
  | @carry o q₀ q' _ hq hk ih =>
    have hl : LiveAt p o.1 q' := by
      rcases hneed with hl | hkTrue | ⟨q'', hq'', hl''⟩
      · exact hl
      · rw [hk] at hkTrue; exact Bool.noConfusion hkTrue
      · exact liveAt_of_killsAt_overwrite_false hk hq'' hl''
    exact .carry (ih (.inr (.inr ⟨q', hq, hl⟩))) hq hl
  | @step o₁ o₂ q₀ q' _ hq hg hd ih =>
    exact .step (ih (.inr (.inr ⟨q', hq, liveAt_of_mem_gen hg hd⟩))) hq hg hd
  | @sub o₁ o₂ q₀ _ hs ih =>
    rcases subAt_left_live_or_killed hs with hl₁ | hk₁
    · exact .sub (ih (.inl hl₁)) hs
    · exact .sub (ih (.inr (.inl hk₁))) hs

theorem gen_layer_bounds {vm : VarMode} {p : Prog n m} (hwt : WellTyped p) {b : Fin n}
    {o₁ o₂ : Origin m} (hg : (o₁, o₂) ∈ gen vm p b) :
    o₁.2 < (p.ty o₁.1).length → o₂.2 < (p.ty o₂.1).length := by
  have hst_wt := hwt b
  unfold gen at hg
  cases hst : p.stmt b <;> rw [hst] at hg hst_wt
  · simp at hg
  · rename_i mu d s
    simp only [StmtWellTyped] at hst_wt
    simp only [List.mem_flatMap, List.mem_range] at hg
    obtain ⟨k, hk, hpair⟩ := hg
    have hd_len : (p.ty d).length = (p.ty s).length + 1 := by simp [hst_wt]
    split at hpair <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
    · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega
    · obtain ⟨rfl, rfl⟩ := hpair; simp; omega
  · rename_i d s
    obtain ⟨hds, _⟩ := hst_wt
    simp only [relate, List.mem_flatMap, List.mem_range] at hg
    obtain ⟨k, hk, hpair⟩ := hg
    have hd_len : (p.ty d).length = (p.ty s).length := by simp [hds]
    split at hpair <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
    · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega
    · obtain ⟨rfl, rfl⟩ := hpair; simp; omega
  · simp at hg
  · simp at hg
  · rename_i q' s
    simp only [StmtWellTyped] at hst_wt
    simp only [relate, List.mem_flatMap, List.mem_range] at hg
    obtain ⟨k, hk, hpair⟩ := hg
    have hq_len : (p.ty q').length = (p.ty s).length + 1 := by simp [hst_wt]
    split at hpair <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hpair
    · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega
    · obtain ⟨rfl, rfl⟩ := hpair; simp; omega
  · simp at hg

theorem subAt_bounds_and_outlives {vm : VarMode} {p : Prog n m} (hwt : WellTyped p)
    {o₁ o₂ : Origin m} {q : Fin n} (h : LS.SubAt vm p o₁ o₂ q) :
    (o₁.2 < (p.ty o₁.1).length → o₂.2 < (p.ty o₂.1).length) ∧
      (∀ u : Fin n, NLL.InRegion vm p o₂ u → NLL.InRegion vm p o₁ u) := by
  induction h with
  | @base o₁ o₂ q hg => exact ⟨gen_layer_bounds hwt hg, fun u hu => .outlives hg hu⟩
  | trans _ _ ih₁ ih₂ =>
    exact ⟨fun h1 => ih₂.1 (ih₁.1 h1), fun u hu => ih₁.2 u (ih₂.2 u hu)⟩
  | persist _ _ _ _ ih => exact ih

theorem liveHolds_to_nll {vm : VarMode} {p : Prog n m} (hwt : WellTyped p)
    {l : Fin n} {o : Origin m} {q : Fin n} (h : LS.LiveHolds vm p l o q) :
    ∃ d : Fin m, loanDst p l = some d ∧ o.2 < (p.ty o.1).length ∧
      (∀ u : Fin n, NLL.InRegion vm p o u → NLL.InRegion vm p (d, 0) u) ∧
      (q = l ∨ NLL.InScope vm p l q) := by
  induction h with
  | @intro mu d s hst =>
    have hwt_l := hwt l
    rw [hst] at hwt_l
    simp only [StmtWellTyped] at hwt_l
    refine ⟨d, ?_, ?_, fun _ hu => hu, .inl rfl⟩
    · simp [loanDst, hst]
    · simp [hwt_l]
  | @carry o q₀ q' _ hq hl ih =>
    obtain ⟨d, hd, hlen, hout, hsc⟩ := ih
    have hinR : NLL.InRegion vm p (d, 0) q' := hout q' (.live hl hlen)
    refine ⟨d, hd, hlen, hout, .inr ?_⟩
    rcases hsc with rfl | hsc
    · exact .first hd hq hinR
    · exact .next hd hsc hq hinR
  | @step o₁ o₂ q₀ q' _ hq hg hndef ih =>
    obtain ⟨d, hd, hlen₁, hout₁, hsc⟩ := ih
    have hl₁ : LiveAt p o₁.1 q' := liveAt_of_mem_gen hg hndef
    have hinR : NLL.InRegion vm p (d, 0) q' := hout₁ q' (.live hl₁ hlen₁)
    refine ⟨d, hd, gen_layer_bounds hwt hg hlen₁, fun u hu => hout₁ u (.outlives hg hu), .inr ?_⟩
    rcases hsc with rfl | hsc
    · exact .first hd hq hinR
    · exact .next hd hsc hq hinR
  | @sub o₁ o₂ q₀ _ hsub ih =>
    obtain ⟨d, hd, hlen₁, hout₁, hsc⟩ := ih
    obtain ⟨hb, ho⟩ := subAt_bounds_and_outlives hwt hsub
    exact ⟨d, hd, hb hlen₁, fun u hu => hout₁ u (ho u hu), hsc⟩

end Incl

theorem holds_none_of_holds_overwrite {vm : VarMode} {p : Prog n m} {l : Fin n} {o : Origin m}
    {q : Fin n} (h : LS.Holds .overwrite vm p l o q) : LS.Holds .none vm p l o q := by
  induction h with
  | intro hst => exact .intro hst
  | carry _ hq _ ih => exact .carry ih hq rfl
  | step _ hq hg hd ih => exact .step ih hq hg hd
  | sub _ hs ih => exact .sub ih hs

/-- For every program and variance mode, the location-sensitive checker without kills accepts
a subset of the programs that the checker with kills at overwrites accepts. -/
theorem lsAccepts_of_lsNoKillAccepts (vm : VarMode) (p : Prog n m)
    (h : LS.Accepts .none vm p) : LS.Accepts .overwrite vm p :=
  fun l q hc ⟨o, q₀, hh, hq, hl⟩ => h l q hc ⟨o, q₀, holds_none_of_holds_overwrite hh, hq, hl⟩

/-- For every program and variance mode, a loan is live for the location-sensitive checker with
kills at overwrites iff it is live for the liveness-gated variant without kills. -/
theorem lsLoanLive_overwrite_iff_liveLoanLive (vm : VarMode) (p : Prog n m) (l q : Fin n) :
    LS.LoanLive .overwrite vm p l q ↔ LS.LiveLoanLive vm p l q := by
  constructor
  · rintro ⟨o, q₀, hh, hq, hl⟩
    exact ⟨o, q₀, Incl.liveHolds_of_holds hh (.inr (.inr ⟨q, hq, hl⟩)), hq, hl⟩
  · rintro ⟨o, q₀, hh, hq, hl⟩
    exact ⟨o, q₀, Incl.holds_of_liveHolds hh, hq, hl⟩

/-- For every program and variance mode, the location-sensitive checker with kills at
overwrites accepts exactly the programs that the liveness-gated variant without kills
accepts. -/
theorem lsAccepts_overwrite_iff_liveAccepts (vm : VarMode) (p : Prog n m) :
    LS.Accepts .overwrite vm p ↔ LS.LiveAccepts vm p := by
  simp only [LS.Accepts, LS.LiveAccepts, lsLoanLive_overwrite_iff_liveLoanLive]

/-- Every well-typed program accepted by the location-insensitive checker `NLL.Accepts vm` is
accepted by the liveness-gated location-sensitive variant without kills `LS.LiveAccepts vm`,
for every variance mode `vm`. -/
theorem liveAccepts_of_wellTyped_of_nllAccepts (vm : VarMode) (p : Prog n m)
    (hwt : WellTyped p) (h : NLL.Accepts vm p) : LS.LiveAccepts vm p := by
  intro l q hconf ⟨o, q₀, hh, hq, hl⟩
  obtain ⟨d, hd, hlen, hout, hsc⟩ := Incl.liveHolds_to_nll hwt hh
  have hinR : NLL.InRegion vm p (d, 0) q := hout q (.live hl hlen)
  have hinScope : NLL.InScope vm p l q := by
    rcases hsc with rfl | hsc
    · exact .first hd hq hinR
    · exact .next hd hsc hq hinR
  exact h l q hconf hinScope

end Toy.LoanFlow
