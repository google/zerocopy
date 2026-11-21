import ToyTransfer.Countermodels

/-!
# The transfer matrix

Rows: the seven claim classes. Columns: four map kinds × two directions. Every cell is
either licensed by one of the easy preservation theorems or refuted by a named
countermodel of `ToyTransfer.Countermodels`. The Boolean table `licensedB` is proved to
agree with `Preserves` cell by cell (`licensedB_iff`); the proof of `cell_status` is the
matrix, one arm per cell. For every row except the quantifier-free one, the same table
is also exact for sentences (`licensedB_iff_preservesSent_of_ne_qf`).
-/

namespace Toy.Transfer

/-- Boolean transfer table (a verdict, distinct from the semantic `Preserves`). -/
def licensedB : Cls → MapKind → Dir → Bool
  | .qf, .emb, _ => true
  | .univ, .emb, .bwd => true
  | .exist, .emb, .fwd => true
  | .posExist, _, .fwd => true
  | .pos, .surj, .fwd => true
  | _, _, _ => false

/-! ## Licensed cells -/

theorem preserves_qf_emb (d : Dir) : Preserves .qf .emb d := by
  intro A B h hk n φ hc e
  have hiff := qf_sat_iff_of_embedding_laws h hk.inj hk.presR hk.presP hk.reflR hk.reflP hc e
  cases d
  · exact hiff.1
  · exact hiff.2

theorem preserves_univ_emb_bwd : Preserves .univ .emb .bwd :=
  fun _ _ h hk _ _ hc e =>
    univ_preserved_to_substructure_of_embedding h hk.inj hk.presR hk.presP hk.reflR hk.reflP hc e

theorem preserves_exist_emb_fwd : Preserves .exist .emb .fwd :=
  fun _ _ h hk _ _ hc e =>
    exist_preserved_to_extension_of_embedding h hk.inj hk.presR hk.presP hk.reflR hk.reflP hc e

theorem preserves_posExist_fwd (k : MapKind) : Preserves .posExist k .fwd :=
  fun _ _ h hk _ _ hc e =>
    posExist_preserved_forward_of_hom h hk.toHom.presR hk.toHom.presP hc e

theorem preserves_pos_surj_fwd : Preserves .pos .surj .fwd :=
  fun _ _ h hk _ _ hc e =>
    pos_preserved_forward_of_surjHom h hk.surj hk.presR hk.presP hc e

/-! ## Map facts used by the refutations -/

theorem inclPN_emb : IsEmbedding inclPN := by decide
theorem inclNP_emb : IsEmbedding inclNP := by decide
theorem inclCyc_emb : IsEmbedding inclCyc := by decide
theorem raiseP_surjHom : IsSurjHom raiseP := by decide
theorem addEdge_surjHom : IsSurjHom addEdge := by decide
theorem collapse_strong : IsStrongHom collapse := by decide

/-! ## Refutations, one per countermodel (class and kind supplied per cell) -/

theorem refuteS_by_allP_ext {c : Cls} {k : MapKind} (hc : c.Mem allP) (hk : k.Holds inclPN) :
    ¬ PreservesSent c k .fwd := by
  obtain ⟨-, -, -, -, -, -, -, -, hA, hB⟩ := allP_not_preserved_to_extension
  exact not_preservesSent_fwd inclPN hk allP hc hA hB

theorem refute_by_allP_ext {c : Cls} {k : MapKind} (hc : c.Mem allP) (hk : k.Holds inclPN) :
    ¬ Preserves c k .fwd :=
  fun hp => refuteS_by_allP_ext hc hk hp.toSent

theorem refuteS_by_exP_sub {c : Cls} {k : MapKind} (hc : c.Mem exP) (hk : k.Holds inclNP) :
    ¬ PreservesSent c k .bwd := by
  obtain ⟨-, -, -, -, -, -, -, hB, hA⟩ := exP_not_preserved_to_substructure
  exact not_preservesSent_bwd inclNP hk exP hc hB hA

theorem refute_by_exP_sub {c : Cls} {k : MapKind} (hc : c.Mem exP) (hk : k.Holds inclNP) :
    ¬ Preserves c k .bwd :=
  fun hp => refuteS_by_exP_sub hc hk hp.toSent

theorem refuteS_by_allExR_sub {c : Cls} {k : MapKind} (hc : c.Mem allExR) (hk : k.Holds inclCyc) :
    ¬ PreservesSent c k .bwd := by
  obtain ⟨-, -, -, -, -, hB, hA⟩ := allExR_not_preserved_to_substructure
  exact not_preservesSent_bwd inclCyc hk allExR hc hB hA

theorem refute_by_allExR_sub {c : Cls} {k : MapKind} (hc : c.Mem allExR) (hk : k.Holds inclCyc) :
    ¬ Preserves c k .bwd :=
  fun hp => refuteS_by_allExR_sub hc hk hp.toSent

theorem refuteS_by_exNotP_hom {c : Cls} {k : MapKind} (hc : c.Mem exNotP) (hk : k.Holds raiseP) :
    ¬ PreservesSent c k .fwd := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hA, hB⟩ := exNotP_not_preserved_by_hom
  exact not_preservesSent_fwd raiseP hk exNotP hc hA hB

theorem refute_by_exNotP_hom {c : Cls} {k : MapKind} (hc : c.Mem exNotP) (hk : k.Holds raiseP) :
    ¬ Preserves c k .fwd :=
  fun hp => refuteS_by_exNotP_hom hc hk hp.toSent

theorem refuteS_by_allRImpEq_surj {c : Cls} {k : MapKind} (hc : c.Mem allRImpEq) (hk : k.Holds addEdge) :
    ¬ PreservesSent c k .fwd := by
  obtain ⟨-, -, -, -, -, -, -, -, hA, hB⟩ := allRImpEq_not_preserved_by_surjHom
  exact not_preservesSent_fwd addEdge hk allRImpEq hc hA hB

theorem refute_by_allRImpEq_surj {c : Cls} {k : MapKind} (hc : c.Mem allRImpEq) (hk : k.Holds addEdge) :
    ¬ Preserves c k .fwd :=
  fun hp => refuteS_by_allRImpEq_surj hc hk hp.toSent

theorem refute_by_notP0 {c : Cls} {k : MapKind} (hc : c.Mem notP0) (hk : k.Holds raiseP) :
    ¬ Preserves c k .fwd := by
  obtain ⟨-, -, -, hA, hB⟩ := notP0_not_preserved_by_surjHom
  exact not_preserves_fwd raiseP hk notP0 hc (env1 0) hA hB

theorem refute_by_neq {c : Cls} {k : MapKind} (hc : c.Mem neq01) (hk : k.Holds collapse) :
    ¬ Preserves c k .fwd := by
  obtain ⟨-, -, -, -, hA, hB⟩ := neq_not_preserved_by_strongHom
  exact not_preserves_fwd collapse hk neq01 hc (env2 0 1) hA hB

theorem refuteS_by_exExNeq {c : Cls} {k : MapKind} (hc : c.Mem exExNeq) (hk : k.Holds collapse) :
    ¬ PreservesSent c k .fwd := by
  obtain ⟨-, -, -, -, -, -, hA, hB⟩ := exExNeq_not_preserved_by_strongHom
  exact not_preservesSent_fwd collapse hk exExNeq hc hA hB

theorem refute_by_exExNeq {c : Cls} {k : MapKind} (hc : c.Mem exExNeq) (hk : k.Holds collapse) :
    ¬ Preserves c k .fwd :=
  fun hp => refuteS_by_exExNeq hc hk hp.toSent

theorem refute_by_eq {c : Cls} {k : MapKind} (hc : c.Mem eq01) (hk : k.Holds collapse) :
    ¬ Preserves c k .bwd := by
  obtain ⟨-, -, -, -, -, -, hB, hA⟩ := eq_not_reflected_by_strongHom
  exact not_preserves_bwd collapse hk eq01 hc (env2 0 1) hB hA

theorem refuteS_by_allAllEq {c : Cls} {k : MapKind} (hc : c.Mem allAllEq) (hk : k.Holds collapse) :
    ¬ PreservesSent c k .bwd := by
  obtain ⟨-, -, -, -, -, -, -, hB, hA⟩ := allAllEq_not_reflected_by_strongHom
  exact not_preservesSent_bwd collapse hk allAllEq hc hB hA

theorem refute_by_allAllEq {c : Cls} {k : MapKind} (hc : c.Mem allAllEq) (hk : k.Holds collapse) :
    ¬ Preserves c k .bwd :=
  fun hp => refuteS_by_allAllEq hc hk hp.toSent

theorem refute_by_P0 {c : Cls} {k : MapKind} (hc : c.Mem P0) (hk : k.Holds raiseP) :
    ¬ Preserves c k .bwd := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hB, hA⟩ := P0_not_reflected_by_surjHom
  exact not_preserves_bwd raiseP hk P0 hc (env1 0) hB hA

theorem refuteS_by_exP_surj {c : Cls} {k : MapKind} (hc : c.Mem exP) (hk : k.Holds raiseP) :
    ¬ PreservesSent c k .bwd := by
  obtain ⟨-, -, -, -, -, -, -, hB, hA⟩ := exP_not_reflected_by_surjHom
  exact not_preservesSent_bwd raiseP hk exP hc hB hA

theorem refute_by_exP_surj {c : Cls} {k : MapKind} (hc : c.Mem exP) (hk : k.Holds raiseP) :
    ¬ Preserves c k .bwd :=
  fun hp => refuteS_by_exP_surj hc hk hp.toSent

theorem refuteS_by_allP_surj {c : Cls} {k : MapKind} (hc : c.Mem allP) (hk : k.Holds raiseP) :
    ¬ PreservesSent c k .bwd := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hB, hA⟩ := allP_not_reflected_by_surjHom
  exact not_preservesSent_bwd raiseP hk allP hc hB hA

theorem refute_by_allP_surj {c : Cls} {k : MapKind} (hc : c.Mem allP) (hk : k.Holds raiseP) :
    ¬ Preserves c k .bwd :=
  fun hp => refuteS_by_allP_surj hc hk hp.toSent

/-! ## The matrix -/

/-- **The transfer matrix.** Every cell is decided: either the table says `true` and the
class transfers along every map of that kind in that direction, or the table says
`false` and a named countermodel refutes the transfer. One arm per cell. -/
theorem cell_status : ∀ (c : Cls) (k : MapKind) (d : Dir),
    (licensedB c k d = true ∧ Preserves c k d) ∨ (licensedB c k d = false ∧ ¬ Preserves c k d) :=
  fun c k d => match c, k, d with
  -- quantifier-free
  | .qf, .hom, .fwd => .inr ⟨rfl, refute_by_notP0 (by decide) raiseP_surjHom.toHom⟩
  | .qf, .hom, .bwd => .inr ⟨rfl, refute_by_P0 (by decide) raiseP_surjHom.toHom⟩
  | .qf, .strong, .fwd => .inr ⟨rfl, refute_by_neq (by decide) collapse_strong⟩
  | .qf, .strong, .bwd => .inr ⟨rfl, refute_by_eq (by decide) collapse_strong⟩
  | .qf, .emb, .fwd => .inl ⟨rfl, preserves_qf_emb .fwd⟩
  | .qf, .emb, .bwd => .inl ⟨rfl, preserves_qf_emb .bwd⟩
  | .qf, .surj, .fwd => .inr ⟨rfl, refute_by_notP0 (by decide) raiseP_surjHom⟩
  | .qf, .surj, .bwd => .inr ⟨rfl, refute_by_P0 (by decide) raiseP_surjHom⟩
  -- universal
  | .univ, .hom, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb.toHom⟩
  | .univ, .hom, .bwd => .inr ⟨rfl, refute_by_allAllEq (by decide) collapse_strong.toHom⟩
  | .univ, .strong, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb.toStrongHom⟩
  | .univ, .strong, .bwd => .inr ⟨rfl, refute_by_allAllEq (by decide) collapse_strong⟩
  | .univ, .emb, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb⟩
  | .univ, .emb, .bwd => .inl ⟨rfl, preserves_univ_emb_bwd⟩
  | .univ, .surj, .fwd => .inr ⟨rfl, refute_by_allRImpEq_surj (by decide) addEdge_surjHom⟩
  | .univ, .surj, .bwd => .inr ⟨rfl, refute_by_allP_surj (by decide) raiseP_surjHom⟩
  -- existential
  | .exist, .hom, .fwd => .inr ⟨rfl, refute_by_exNotP_hom (by decide) raiseP_surjHom.toHom⟩
  | .exist, .hom, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb.toHom⟩
  | .exist, .strong, .fwd => .inr ⟨rfl, refute_by_exExNeq (by decide) collapse_strong⟩
  | .exist, .strong, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb.toStrongHom⟩
  | .exist, .emb, .fwd => .inl ⟨rfl, preserves_exist_emb_fwd⟩
  | .exist, .emb, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb⟩
  | .exist, .surj, .fwd => .inr ⟨rfl, refute_by_exNotP_hom (by decide) raiseP_surjHom⟩
  | .exist, .surj, .bwd => .inr ⟨rfl, refute_by_exP_surj (by decide) raiseP_surjHom⟩
  -- ∀∃
  | .ae, .hom, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb.toHom⟩
  | .ae, .hom, .bwd => .inr ⟨rfl, refute_by_allExR_sub (by decide) inclCyc_emb.toHom⟩
  | .ae, .strong, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb.toStrongHom⟩
  | .ae, .strong, .bwd => .inr ⟨rfl, refute_by_allExR_sub (by decide) inclCyc_emb.toStrongHom⟩
  | .ae, .emb, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb⟩
  | .ae, .emb, .bwd => .inr ⟨rfl, refute_by_allExR_sub (by decide) inclCyc_emb⟩
  | .ae, .surj, .fwd => .inr ⟨rfl, refute_by_allRImpEq_surj (by decide) addEdge_surjHom⟩
  | .ae, .surj, .bwd => .inr ⟨rfl, refute_by_allP_surj (by decide) raiseP_surjHom⟩
  -- ∃∀
  | .ea, .hom, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb.toHom⟩
  | .ea, .hom, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb.toHom⟩
  | .ea, .strong, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb.toStrongHom⟩
  | .ea, .strong, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb.toStrongHom⟩
  | .ea, .emb, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb⟩
  | .ea, .emb, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb⟩
  | .ea, .surj, .fwd => .inr ⟨rfl, refute_by_allRImpEq_surj (by decide) addEdge_surjHom⟩
  | .ea, .surj, .bwd => .inr ⟨rfl, refute_by_exP_surj (by decide) raiseP_surjHom⟩
  -- positive
  | .pos, .hom, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb.toHom⟩
  | .pos, .hom, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb.toHom⟩
  | .pos, .strong, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb.toStrongHom⟩
  | .pos, .strong, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb.toStrongHom⟩
  | .pos, .emb, .fwd => .inr ⟨rfl, refute_by_allP_ext (by decide) inclPN_emb⟩
  | .pos, .emb, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb⟩
  | .pos, .surj, .fwd => .inl ⟨rfl, preserves_pos_surj_fwd⟩
  | .pos, .surj, .bwd => .inr ⟨rfl, refute_by_exP_surj (by decide) raiseP_surjHom⟩
  -- positive existential
  | .posExist, .hom, .fwd => .inl ⟨rfl, preserves_posExist_fwd .hom⟩
  | .posExist, .hom, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb.toHom⟩
  | .posExist, .strong, .fwd => .inl ⟨rfl, preserves_posExist_fwd .strong⟩
  | .posExist, .strong, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb.toStrongHom⟩
  | .posExist, .emb, .fwd => .inl ⟨rfl, preserves_posExist_fwd .emb⟩
  | .posExist, .emb, .bwd => .inr ⟨rfl, refute_by_exP_sub (by decide) inclNP_emb⟩
  | .posExist, .surj, .fwd => .inl ⟨rfl, preserves_posExist_fwd .surj⟩
  | .posExist, .surj, .bwd => .inr ⟨rfl, refute_by_exP_surj (by decide) raiseP_surjHom⟩

/-- **Agreement of the Boolean table.** For every claim class `c`, map kind
`k` and direction `d`: `licensedB c k d = true` if and only if class-`c` formulas
transfer along every `k`-map in direction `d`. -/
theorem licensedB_iff (c : Cls) (k : MapKind) (d : Dir) :
    licensedB c k d = true ↔ Preserves c k d := by
  rcases cell_status c k d with ⟨hb, hp⟩ | ⟨hb, hp⟩
  · exact ⟨fun _ => hp, fun _ => hb⟩
  · rw [hb]
    exact ⟨fun h => (nomatch h), fun h => absurd h hp⟩

/-- **The table for sentences.** For every class other than the quantifier-free one,
every map kind and direction: `licensedB c k d = true` if and only if class-`c` sentences
transfer along every `k`-map in direction `d`. (There are no quantifier-free sentences,
`no_qf_sentences`, so for `c = .qf` sentence-level transfer holds vacuously.) -/
theorem licensedB_iff_preservesSent_of_ne_qf (c : Cls) (k : MapKind) (d : Dir) (hc : c ≠ .qf) :
    licensedB c k d = true ↔ PreservesSent c k d := by
  refine ⟨fun hl => ((licensedB_iff c k d).1 hl).toSent, fun hs => ?_⟩
  cases c <;> cases k <;> cases d <;>
    first
    | rfl
    | exact absurd rfl hc
    | exact absurd hs (refuteS_by_allP_ext (by decide) (by decide))
    | exact absurd hs (refuteS_by_exP_sub (by decide) (by decide))
    | exact absurd hs (refuteS_by_allExR_sub (by decide) (by decide))
    | exact absurd hs (refuteS_by_exNotP_hom (by decide) (by decide))
    | exact absurd hs (refuteS_by_allRImpEq_surj (by decide) (by decide))
    | exact absurd hs (refuteS_by_exExNeq (by decide) (by decide))
    | exact absurd hs (refuteS_by_allAllEq (by decide) (by decide))
    | exact absurd hs (refuteS_by_exP_surj (by decide) (by decide))
    | exact absurd hs (refuteS_by_allP_surj (by decide) (by decide))

/-- Sentence-level transfer for the quantifier-free row holds for every map kind and
direction, vacuously. -/
theorem preservesSent_qf (k : MapKind) (d : Dir) : PreservesSent .qf k d :=
  fun _ _ _ _ φ hq => absurd hq (no_qf_sentences φ)

/-- Tightness of `c ≠ .qf` in `licensedB_iff_preservesSent_of_ne_qf`: the quantifier-free
cell for homomorphisms, forward, is unlicensed, yet sentence-level transfer holds there
(vacuously). -/
theorem licensedB_iff_preservesSent_needs_ne_qf :
    licensedB .qf .hom .fwd = false ∧ PreservesSent .qf .hom .fwd :=
  ⟨rfl, preservesSent_qf .hom .fwd⟩

/-! ## Formula-level use of the table (sound, not complete) -/

/-- All seven claim classes. -/
def allCls : List Cls := [.qf, .univ, .exist, .ae, .ea, .pos, .posExist]

/-- Boolean licence for a concrete formula: some class containing it is licensed. -/
def licensedForB {n : Nat} (φ : Fml n) (k : MapKind) (d : Dir) : Bool :=
  allCls.any (fun c => c.test φ && licensedB c k d)

/-- Soundness of the formula-level licence: if `licensedForB φ k d = true`, then `φ`
transfers along every `k`-map in direction `d`, for every environment. -/
theorem transfer_of_licensedForB {n : Nat} (φ : Fml n) (k : MapKind) (d : Dir)
    (hl : licensedForB φ k d = true) :
    ∀ (A B : Str) (h : A.carrier → B.carrier), k.Holds h →
      ∀ e : Fin n → A.carrier, d.Transfer (Sat A φ e) (Sat B φ (h ∘ e)) := by
  intro A B h hk e
  obtain ⟨c, -, hc⟩ := List.any_eq_true.1 hl
  rw [Bool.and_eq_true] at hc
  exact (licensedB_iff c k d).1 hc.2 A B h hk n φ ((c.test_iff φ).1 hc.1) e

/-- `transfer_of_licensedForB` is non-vacuous: `∃x, P x` is licensed forward along
embeddings, and the premise holds at the source of the embedding `inclPN`. -/
theorem transfer_of_licensedForB_nonvacuous :
    licensedForB exP .emb .fwd = true ∧ MapKind.Holds .emb inclPN ∧
    Sat S1P.toStr exP Fin.elim0 := by
  decide

/-- Tightness of the licence hypothesis of `transfer_of_licensedForB`: `∀x, P x` is not
licensed forward along embeddings, and it fails to transfer along the embedding
`inclPN`. -/
theorem transfer_of_licensedForB_needs_licence :
    licensedForB allP .emb .fwd = false ∧ MapKind.Holds .emb inclPN ∧
    Sat S1P.toStr allP Fin.elim0 ∧ ¬ Sat S2PN.toStr allP (inclPN ∘ Fin.elim0) := by
  decide

/-- `∀x, P x ∨ ¬ P x` (valid in every structure). -/
def exclMid : Fml 0 := .all (.or (.pred 0) (.neg (.pred 0)))

/-- The formula-level licence is incomplete: the valid sentence `∀x, P x ∨ ¬ P x` is not
licensed for homomorphisms forward (it is universal with a negation), yet it transfers
along every homomorphism. A `false` verdict is therefore not a refutation for an
individual formula. -/
theorem licensedForB_incomplete :
    licensedForB exclMid .hom .fwd = false ∧
    ∀ (A B : Str) (h : A.carrier → B.carrier), IsHom h →
      Sat A exclMid Fin.elim0 → Sat B exclMid (h ∘ Fin.elim0) :=
  ⟨rfl, fun _ B _ _ _ b => Classical.em (B.P b)⟩

end Toy.Transfer
