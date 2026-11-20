import ToyDirCC.Dup

/-!
# Tightness of the hypotheses of the hash-consing results

Each theorem states, for one hypothesis, a concrete term for which all other hypotheses
hold and the conclusion fails.
-/

namespace Toy.DirCC.Dup

/-- `frz₀ x₀ + frz₀ x₁`: one tag on two different arguments. -/
def mixedProg : Tm := .add (.frz 0 (.var 0)) (.frz 0 (.var 1))

theorem hashcons_mixedProg :
    hashcons [] mixedProg = ([.var 0, .frz 0 0, .var 1, .frz 0 2, .add 1 3], 4) := by decide

/-- `hcSem_iff_tagSem_of_letFree_wellTagged` needs `WellTagged`: `frz₀ x₀ + frz₀ x₁` is let-free;
its hash-consed table has two `frz` nodes with independent choices and can produce `1`
when both variables are poison, while one choice per tag cannot. -/
theorem hcSem_iff_tagSem_needs_wellTagged :
    LetFree mixedProg = true ∧ ¬ WellTagged mixedProg ∧
    hcSem poisonEnv mixedProg (some 1) ∧ ¬ tagSem poisonEnv mixedProg (some 1) := by
  refine ⟨by decide, by decide, ⟨fun i => if i = 1 then 0 else 1, by decide⟩, ?_⟩
  rintro ⟨σ, hσ⟩
  simp [mixedProg, evalT, poisonEnv, frzT, addV] at hσ
  omega

/-- `let x₀ := 1; x₀`. -/
def letLitProg : Tm := .letE 0 (.lit 1) (.var 0)

/-- `hcSem_iff_tagSem_of_letFree_wellTagged` needs `LetFree` (hash-consing is defined on let-free
terms only; `letE` falls outside its domain). -/
theorem hcSem_iff_tagSem_needs_letFree :
    LetFree letLitProg = false ∧ WellTagged letLitProg ∧
    tagSem poisonEnv letLitProg (some 1) ∧ ¬ hcSem poisonEnv letLitProg (some 1) := by
  refine ⟨by decide, by decide, ⟨fun _ => 0, by decide⟩, ?_⟩
  rintro ⟨c, hc⟩
  have e : hashcons [] letLitProg = ([.lit 0], 0) := by decide
  rw [e] at hc
  simp [evalTbl] at hc

/-- `tagSem_iff_indep_of_uniqueTags` needs `UniqueTags`: `frz₀ x₀ + frz₀ x₀` (two
occurrences, one tag) can produce `1` under independent choices but not under one choice
per tag. -/
theorem tagSem_iff_indep_needs_uniqueTags :
    ¬ UniqueTags dupProg ∧ indep poisonEnv dupProg (some 1) ∧
    ¬ tagSem poisonEnv dupProg (some 1) :=
  ⟨not_uniqueTags_dupProg, indep_dupProg_one, not_tagSem_dupProg_one⟩

/-- `hashcons_inline_sound_of_uniqueTags` needs `UniqueTags`: for the source program
`frz₀ x₀ + frz₀ x₀`, inlining changes nothing, hash-consing merges the two occurrences, and
the merged table cannot produce the outcome `1` that the program can. -/
theorem hashcons_inline_sound_needs_uniqueTags :
    ¬ UniqueTags dupProg ∧ inline dupProg = dupProg ∧
    ¬ hcSem poisonEnv (inline dupProg) (some 1) ∧ indep poisonEnv dupProg (some 1) := by
  have hi : inline dupProg = dupProg := by decide
  refine ⟨not_uniqueTags_dupProg, hi, ?_, indep_dupProg_one⟩
  rw [hi]
  exact not_hcSem_dupProg_one

/-- `let x₀ := 1; (frz₀ x₀ + let x₀ := 2; frz₀ x₀)`: two `frz` occurrences with one tag and
syntactically identical arguments that denote different values because of shadowing. -/
def shadowProg : Tm :=
  .letE 0 (.lit 1) (.add (.frz 0 (.var 0)) (.letE 0 (.lit 2) (.frz 0 (.var 0))))

/-- `wellTagged_inline_of_uniqueTags` needs `UniqueTags`, and `UniqueTags` cannot even be
weakened to `WellTagged`: `shadowProg` is well-tagged but has a repeated tag, and its
inlining `frz₀ 1 + frz₀ 2` is not well-tagged. -/
theorem wellTagged_inline_needs_uniqueTags :
    ¬ UniqueTags shadowProg ∧ WellTagged shadowProg ∧
    inline shadowProg = .add (.frz 0 (.lit 1)) (.frz 0 (.lit 2)) ∧
    ¬ WellTagged (inline shadowProg) := by decide

end Toy.DirCC.Dup
