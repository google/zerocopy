import Toy.Render.Lemmas

/-!
# Main statements (`Toy.Render`)

Positive theorems and characterizations about printing and re-elaboration in the
toy language. Concrete counterexamples, non-vacuity witnesses and positive
controls are in `Toy.Render.Counterexamples` and `Toy.Render.Witnesses`; the
auxiliary lemmas used by the proofs are in `Toy.Render.Lemmas`.
-/

namespace Toy.Render

/-! ## Section law and faithfulness of the default printer -/

/-- **Section law.** For every elaborator configuration of the family, the explicit
printer is a section of elaboration on well-typed terms: re-reading the explicit
text of a well-typed `t` yields exactly `t`. -/
theorem elabWith_ppExplicit_of_wellTyped (cfg : ElabCfg) (S : Sig) (t : Tm)
    (ht : WellTyped S t) : elabWith cfg S (ppExplicit t) = some t := by
  rcases ht with ⟨τ, hty⟩
  simp [elabWith, ppExplicit, ppWith, elabE_ppExplicit cfg S t [] τ none hty (.inl rfl)]

/-- **Default faithfulness, "if" direction.** If `t` passes the structural check
`DefaultRecoverable` (the recursion `defRec` in `Toy.Render.Defs`), the system
elaborator reads the default text of `t` back as `t`. -/
theorem elabSys_ppDefault_of_defaultRecoverable (S : Sig) (t : Tm)
    (h : DefaultRecoverable S t) : elabSys S (ppDefault t) = some t := by
  obtain ⟨σ, -, he⟩ := defRec_sound S t [] none none h
  simp only [elabSys, elabWith, ppDefault, ppWith]
  rw [he]
  rfl

/-- **Default faithfulness, "only if" direction.** If the system elaborator reads
the default text of `t` back as `t`, then `t` passes `DefaultRecoverable`. -/
theorem defaultRecoverable_of_elabSys_ppDefault (S : Sig) (t : Tm)
    (h : elabSys S (ppDefault t) = some t) : DefaultRecoverable S t := by
  simp only [elabSys, elabWith, ppDefault, ppWith, Option.map_eq_some_iff] at h
  obtain ⟨⟨u, σ⟩, he, hu⟩ := h
  simp only at hu
  subst hu
  exact defRec_complete S u [] none none σ (u, σ) rfl rfl he

/-- **Default faithfulness characterization.** For every signature `S` and every
term `t` (well typed or not), the system elaborator reads the default text of `t`
back as `t` if and only if `t` passes `DefaultRecoverable`. -/
theorem elabSys_ppDefault_eq_some_iff_defaultRecoverable (S : Sig) (t : Tm) :
    elabSys S (ppDefault t) = some t ↔ DefaultRecoverable S t :=
  ⟨defaultRecoverable_of_elabSys_ppDefault S t, elabSys_ppDefault_of_defaultRecoverable S t⟩

/-! ## Textual round trips -/

/-- **Textual idempotence is necessary for faithfulness.** For any printer `p` and
reader `cfg`: if `p t` reads back as `t`, then printing the re-read term with `p`
reproduces the text `p t`. -/
theorem textual_round_trip_of_faithful (cfg : ElabCfg) (S : Sig) (p : Tm → Stx) (t : Tm)
    (h : elabWith cfg S (p t) = some t) : (elabWith cfg S (p t)).map p = some (p t) := by
  simp [h]

/-- **Annotation-free text always survives the textual round trip.** If a text `s`
contains no annotation tokens and elaborates (under any configuration) to `t'`,
then the default printing of `t'` is `s` again. -/
theorem ppDefault_elabWith_of_annotationFree (cfg : ElabCfg) (S : Sig) (s : Stx) (t' : Tm)
    (hs : s.annCount = 0) (h : elabWith cfg S s = some t') : ppDefault t' = s := by
  simp only [elabWith, Option.map_eq_some_iff] at h
  rcases h with ⟨⟨u, τ⟩, he, rfl⟩
  exact ppDefault_elabE_of_annotationFree cfg S s none u τ hs he

/-! ## The term round trip as a certificate -/

/-- **The term round trip determines the reading.** If a text `r` reads back as `t`
under the reader `cfg`, then every reading of `r` by `cfg` is `t` and has the same
denotation as `t` in every environment. -/
theorem faithful_reading_unique_and_same_denotation (cfg : ElabCfg) (S : Sig) (r : Stx)
    (t : Tm) (h : Faithful cfg S r t) :
    ∀ t', elabWith cfg S r = some t' → t' = t ∧ ∀ ρ, (Denote S t' ρ ↔ Denote S t ρ) := by
  intro t' h'
  cases h.symm.trans h'
  exact ⟨rfl, fun _ => Iff.rfl⟩

/-! ## The deletion-greedy printer `ppMin` -/

/-- **The deletion-greedy printer is faithful.** For every configuration `cfg` and
every well-typed `t`, the rendering `ppMin cfg S t` reads back as `t` under `cfg`. -/
theorem ppMin_faithful_of_wellTyped (cfg : ElabCfg) (S : Sig) (t : Tm)
    (ht : WellTyped S t) : Faithful cfg S (ppMin cfg S t) t := by
  unfold ppMin
  rw [minMask_eq_foldl]
  apply foldl_greedy_faithful
  rw [ppMask_maskOf_annPos]
  exact elabWith_ppExplicit_of_wellTyped cfg S t ht

/-- **The deletion-greedy printer is locally minimal on well-typed terms.** For every
configuration `cfg`, every well-typed `t` and every annotation position `q` kept by
`minMask cfg S t`: the rendering `ppMin cfg S t` is faithful under `cfg`, and the
rendering that shows the kept positions except `q` is not. -/
theorem ppMin_locally_minimal_of_wellTyped (cfg : ElabCfg) (S : Sig) (t : Tm)
    (ht : WellTyped S t) (q : Path × AnnKind) (hq : q ∈ minMask cfg S t) :
    Faithful cfg S (ppMin cfg S t) t ∧
      ¬ Faithful cfg S (ppMask (maskOf ((minMask cfg S t).erase q)) [] t) t := by
  refine ⟨ppMin_faithful_of_wellTyped cfg S t ht, ?_⟩
  rw [minMask_eq_foldl] at hq ⊢
  have hqL : q ∈ annPos [] t :=
    (foldl_greedy_sublist cfg S t (annPos [] t) (annPos [] t)).subset hq
  exact foldl_greedy_kept cfg S t (annPos [] t) (annPos [] t) [] (annPos_nodup t [])
    (fun _ h => absurd h List.not_mem_nil) q (by simpa using hqL) hq

/-- **The deletion-greedy printer returns the default text when that text is
faithful.** If the default text of `t` is faithful under `cfg`, then
`ppMin cfg S t` is the default text. -/
theorem ppMin_eq_ppDefault_of_faithful_ppDefault (cfg : ElabCfg) (S : Sig) (t : Tm)
    (h : Faithful cfg S (ppDefault t) t) : ppMin cfg S t = ppDefault t := by
  have hall : ∀ M : List (Path × AnnKind), Faithful cfg S (ppMask (maskOf M) [] t) t :=
    fun M => faithful_ppMask_mono_aux cfg S t (fun _ _ => false) (maskOf M)
      (fun _ _ h => absurd h (by simp)) h
  unfold ppMin
  rw [minMask_eq_foldl, foldl_greedy_all cfg S t hall]
  have := foldl_erase_append (annPos [] t) []
  rw [List.append_nil] at this
  rw [this, maskOf_nil]
  rfl

/-! ## Reader-relativity -/

/-- **The configuration family agrees on fully annotated text.** For every
configuration `cfg`, signature `S` and text `s`: if `s` is fully annotated, then
`cfg` reads `s` exactly as the system elaborator does. -/
theorem elabWith_eq_elabSys_of_fullyAnnotated (cfg : ElabCfg) (S : Sig) (s : Stx)
    (hs : s.fullyAnnotated = true) : elabWith cfg S s = elabSys S s := by
  simp [elabSys, elabWith, elabE_eq_cfg0_of_fullyAnnotated cfg S s none hs]

/-- `elabWith_eq_elabSys_of_fullyAnnotated`, packaged with `AgreeOnFull`. -/
theorem elabWith_agreeOnFull (cfg : ElabCfg) : AgreeOnFull elabSys (elabWith cfg) :=
  fun S s hs => elabWith_eq_elabSys_of_fullyAnnotated cfg S s hs

/-- **Explicit text is faithful for every agreeing reader.** If a reader `e'` agrees
with the system elaborator, in every signature, on fully annotated text, it reads the
explicit text of a well-typed `t` as `t`. -/
theorem agreeing_reader_reads_ppExplicit (S : Sig) (t : Tm) (e' : Reader)
    (ht : WellTyped S t) (hag : AgreeOnFull elabSys e') : e' S (ppExplicit t) = some t := by
  rw [hag S (ppExplicit t) (ppExplicit_fullyAnnotated [] t)]
  exact elabWith_ppExplicit_of_wellTyped cfg0 S t ht

/-! ## Monotonicity of correct annotation -/

/-- **Adding correct annotations preserves faithfulness.** For every configuration:
if the rendering of `t` showing the annotations selected by `m` is faithful, so is
the rendering showing the annotations selected by any `m'` that selects at least
the positions `m` selects (the shown annotations are always the ones `t` actually
carries). -/
theorem faithful_ppMask_mono (cfg : ElabCfg) (S : Sig) (t : Tm) (m m' : Mask)
    (hle : ∀ p k, m p k = true → m' p k = true)
    (hf : Faithful cfg S (ppMask m [] t) t) : Faithful cfg S (ppMask m' [] t) t :=
  faithful_ppMask_mono_aux cfg S t m m' hle hf

/-! ## δ-unfolded renderings -/

/-- **Equal δ-normal forms imply equal evaluation.** If two terms have the same
δ-normal form in `S`, they evaluate identically in every environment. -/
theorem eval_eq_of_deltaNF_eq (S : Sig) (t₁ t₂ : Tm) (h : deltaNF S t₁ = deltaNF S t₂) :
    ∀ ρ, eval S ρ t₁ = eval S ρ t₂ := by
  intro ρ
  simp only [eval]
  rw [evalD_eq_unfoldDefs S.defs ρ t₁, evalD_eq_unfoldDefs S.defs ρ t₂]
  exact congrArg (evalD [] ρ) h

/-! ## Coherence of coercion insertion -/

/-- **The deterministic elaborators are instances of the declarative judgment.** If
`elabE cfg S exp s` returns `(t, τ)`, then `t` is a declarative elaboration of `s`
at `τ`, and `t` has type `τ`. -/
theorem elabE_sound (cfg : ElabCfg) (S : Sig) (exp : Option Ty) (s : Stx) (t : Tm) (τ : Ty)
    (h : elabE cfg S exp s = some (t, τ)) : Elabs S s τ t ∧ tyOf S t = some τ :=
  elabE_sound_aux cfg S exp s t τ h

/-- **Coherence when every subtraction is annotated.** For syntax in which every `-`
carries an explicit type argument, any two declarative elaborations at the same type
evaluate identically in every environment. -/
theorem elabs_coherent_of_subAnnotated (S : Sig) (s : Stx) (τ : Ty) (t₁ t₂ : Tm)
    (hs : s.subAnnotated = true) (h₁ : Elabs S s τ t₁) (h₂ : Elabs S s τ t₂) :
    ∀ ρ, eval S ρ t₁ = eval S ρ t₂ := by
  intro ρ
  simp only [eval]
  rw [evalD_eq_evalWith_const S.defs ρ t₁, evalD_eq_evalWith_const S.defs ρ t₂]
  exact (elabs_coh_aux S _ ρ s hs).1 τ t₁ t₂ h₁ h₂

/-- **Coherence without subtraction.** For syntax without `-`, any two declarative
elaborations at the same type evaluate identically in every environment, wherever
their coercions were inserted. -/
theorem elabs_coherent_of_subFree (S : Sig) (s : Stx) (τ : Ty) (t₁ t₂ : Tm)
    (hs : s.subFree = true) (h₁ : Elabs S s τ t₁) (h₂ : Elabs S s τ t₂) :
    ∀ ρ, eval S ρ t₁ = eval S ρ t₂ :=
  elabs_coherent_of_subAnnotated S s τ t₁ t₂ (subAnnotated_of_subFree s hs) h₁ h₂

/-- **Coherence on fully annotated syntax.** For fully annotated syntax (with `-`
allowed), any two declarative elaborations at the same type evaluate identically
in every environment. -/
theorem elabs_coherent_of_fullyAnnotated (S : Sig) (s : Stx) (τ : Ty) (t₁ t₂ : Tm)
    (hs : s.fullyAnnotated = true) (h₁ : Elabs S s τ t₁) (h₂ : Elabs S s τ t₂) :
    ∀ ρ, eval S ρ t₁ = eval S ρ t₂ :=
  elabs_coherent_of_subAnnotated S s τ t₁ t₂ (subAnnotated_of_fullyAnnotated s hs) h₁ h₂

end Toy.Render
