import Toy.BoundaryLicensing.Sequent

set_option autoImplicit false

namespace Toy.BoundaryLicensing

/-! ## Pragmatic Exhaustification & Non-Markovian Compression Non-Inheritance -/

/-- Semantic proposition over an epistemic world space `W`. -/
abbrev WorldClaim (W : Type) := W → Prop

/-- Evidence `E` entails claim `C` across all worlds satisfying `E`. -/
def EntailsEv {W : Type} (E C : WorldClaim W) : Prop :=
  ∀ w : W, E w → C w

/-- Evidence `E` refutes/contradicts claim `C` across all worlds satisfying `E`. -/
def ContradictsEv {W : Type} (E C : WorldClaim W) : Prop :=
  ∀ w : W, E w → ¬ C w

/-- Claim `C` is undetermined under `E` when `E` neither entails nor contradicts `C`. -/
def UndeterminedEv {W : Type} (E C : WorldClaim W) : Prop :=
  ¬ EntailsEv E C ∧ ¬ ContradictsEv E C

/-- Exhaustified pragmatic reading of bare `"proved for the model only"` (`M ∧ ¬ S_ext`). -/
def exhaustifiedOnlyReading {W : Type} (M S_ext : WorldClaim W) : WorldClaim W :=
  fun w => M w ∧ ¬ S_ext w

/-- Syntactic scope-disclaimer forms attached to a model theorem `M` regarding an external claim `S_ext`. -/
inductive ScopeDisclaimer where
  | bareOnly
  | unblockedUnshown
  | neitherNor
  deriving DecidableEq, Repr

/-- Meta-epistemic literal truth condition of a `ScopeDisclaimer` relative to `(E, M, S_ext)`. -/
def DisclaimerLitTrue {W : Type} (E M S_ext : WorldClaim W) : ScopeDisclaimer → Prop
  | .bareOnly => EntailsEv E M ∧ ¬ EntailsEv E S_ext
  | .unblockedUnshown => EntailsEv E M ∧ ¬ EntailsEv E S_ext
  | .neitherNor => EntailsEv E M ∧ ¬ EntailsEv E S_ext ∧ ¬ ContradictsEv E S_ext

/-- Object-level world-claim readings licensed by a `ScopeDisclaimer`:
`bareOnly` and `unblockedUnshown` invite refutation of `S_ext`, whereas `neitherNor` cancels the
refutation implicature and licenses only `M`. -/
def disclaimerReadings {W : Type} (M S_ext : WorldClaim W) : ScopeDisclaimer → List (WorldClaim W)
  | .bareOnly => [M, exhaustifiedOnlyReading M S_ext]
  | .unblockedUnshown => [M, fun w => ¬ S_ext w]
  | .neitherNor => [M]

/-- A scope disclaimer `d` is safe under `(E, M, S_ext)` when its meta-epistemic literal assertion holds
and every object-level reading in `disclaimerReadings M S_ext d` is entailed by `E`. -/
def DisclaimerSafe {W : Type} (E M S_ext : WorldClaim W) (d : ScopeDisclaimer) : Prop :=
  DisclaimerLitTrue E M S_ext d ∧ ∀ C ∈ disclaimerReadings M S_ext d, EntailsEv E C

/-- Safety of the explicit `"neither establish nor refute"` disclaimer (`ScopeDisclaimer.neitherNor`). -/
def NeitherNorDisclaimerSafe {W : Type} (E M S_ext : WorldClaim W) : Prop :=
  DisclaimerSafe E M S_ext .neitherNor

/-- Exact characterization of `NeitherNorDisclaimerSafe`: `ScopeDisclaimer.neitherNor` is literally
accurate and generates only `E`-entailed readings iff `E` entails `M` and leaves `S_ext` undetermined. -/
theorem neitherNorDisclaimerSafe_iff {W : Type} (E M S_ext : WorldClaim W) :
    NeitherNorDisclaimerSafe E M S_ext ↔ EntailsEv E M ∧ UndeterminedEv E S_ext := by
  constructor
  · rintro ⟨⟨hM, hne, hnc⟩, _⟩
    exact ⟨hM, hne, hnc⟩
  · rintro ⟨hM, hne, hnc⟩
    refine ⟨⟨hM, hne, hnc⟩, ?_⟩
    intro C hmem
    rcases List.mem_singleton.1 hmem with rfl
    exact hM

/-- Exact characterization of bare `"only"` exhaustification: when `E` establishes `M`,
the exhaustified reading `M ∧ ¬ S_ext` is sound across `E` iff `E` refutes `S_ext`. -/
theorem exhaustifiedOnly_sound_iff_contradictsEv {W : Type} (E M S_ext : WorldClaim W)
    (hM : EntailsEv E M) :
    EntailsEv E (exhaustifiedOnlyReading M S_ext) ↔ ContradictsEv E S_ext := by
  constructor
  · intro hexh w hw
    exact (hexh w hw).2
  · intro hcon w hw
    exact ⟨hM w hw, hcon w hw⟩

/-- Whenever `E` entails `M` and leaves `S_ext` undetermined (as under `BoundaryRel.none`),
`ScopeDisclaimer.bareOnly` and `exhaustifiedOnlyReading` are unsound while `NeitherNorDisclaimerSafe` holds. -/
theorem exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined {W : Type}
    (E M S_ext : WorldClaim W) (hM : EntailsEv E M) (hund : UndeterminedEv E S_ext) :
    ¬ DisclaimerSafe E M S_ext .bareOnly ∧
    ¬ EntailsEv E (exhaustifiedOnlyReading M S_ext) ∧
    NeitherNorDisclaimerSafe E M S_ext := by
  have hnot_exh : ¬ EntailsEv E (exhaustifiedOnlyReading M S_ext) := by
    rw [exhaustifiedOnly_sound_iff_contradictsEv E M S_ext hM]
    exact hund.2
  refine ⟨?_, hnot_exh, (neitherNorDisclaimerSafe_iff E M S_ext).2 ⟨hM, hund⟩⟩
  intro hsafe
  exact hnot_exh (hsafe.2 (exhaustifiedOnlyReading M S_ext)
    (List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)))

/-- Tightness counterexample for `hM : EntailsEv E M` in `exhaustifiedOnly_sound_iff_contradictsEv`:
if `E` refutes `S_ext` while failing `M`, `ContradictsEv E S_ext` holds yet `exhaustifiedOnlyReading` fails. -/
theorem cex_exhaustifiedOnly_without_model_entailed :
    let E : WorldClaim Bool := fun _ => True
    let M : WorldClaim Bool := fun b => b = true
    let S_ext : WorldClaim Bool := fun _ => False
    ContradictsEv E S_ext ∧ ¬ EntailsEv E (exhaustifiedOnlyReading M S_ext) := by
  refine ⟨fun _ _ h => h, ?_⟩
  intro h
  exact Bool.noConfusion (h false trivial).1

/-- Tightness counterexample for `hM : EntailsEv E M` in
`exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`: when `UndeterminedEv E S_ext` holds
without `EntailsEv E M`, `NeitherNorDisclaimerSafe E M S_ext` fails (proving `NeitherNorDisclaimerSafe`
is strictly stronger than `UndeterminedEv`). -/
theorem cex_neitherNor_without_model_entailed :
    let E : WorldClaim Bool := fun _ => True
    let M : WorldClaim Bool := fun b => b = true
    let S_ext : WorldClaim Bool := fun b => b = false
    UndeterminedEv E S_ext ∧ ¬ NeitherNorDisclaimerSafe E M S_ext := by
  intro E M S_ext
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h; exact Bool.noConfusion (h true trivial)
  · intro h; exact h false trivial rfl
  · intro hsafe
    have hM := ((neitherNorDisclaimerSafe_iff E M S_ext).1 hsafe).1
    exact Bool.noConfusion (hM false trivial)

/-- Tightness counterexample for `hund : UndeterminedEv E S_ext` in
`exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`: when `E` refutes `S_ext` and is
satisfiable, `DisclaimerSafe E M S_ext .bareOnly` and `EntailsEv E (exhaustifiedOnlyReading M S_ext)`
both hold while `NeitherNorDisclaimerSafe E M S_ext` fails. -/
theorem cex_exhaustifiedOnly_unsound_without_undetermined :
    let E : WorldClaim Bool := fun b => b = true
    let M : WorldClaim Bool := fun b => b = true
    let S_ext : WorldClaim Bool := fun b => b = false
    EntailsEv E M ∧
    ¬ UndeterminedEv E S_ext ∧
    DisclaimerSafe E M S_ext .bareOnly ∧
    EntailsEv E (exhaustifiedOnlyReading M S_ext) ∧
    ¬ NeitherNorDisclaimerSafe E M S_ext := by
  intro E M S_ext
  have hM : EntailsEv E M := fun _ h => h
  have hcon : ContradictsEv E S_ext := fun b hb hf => by rw [hb] at hf; cases hf
  have hnotEnt : ¬ EntailsEv E S_ext := fun h => Bool.noConfusion (h true rfl)
  have hexh : EntailsEv E (exhaustifiedOnlyReading M S_ext) :=
    (exhaustifiedOnly_sound_iff_contradictsEv E M S_ext hM).2 hcon
  refine ⟨hM, fun h => h.2 hcon, ⟨⟨hM, hnotEnt⟩, ?_⟩, hexh, ?_⟩
  · intro C hmem
    rcases List.mem_cons.1 hmem with rfl | hrest
    · exact hM
    · rcases List.mem_singleton.1 hrest with rfl
      exact hexh
  · intro hnn
    exact ((neitherNorDisclaimerSafe_iff E M S_ext).1 hnn).2.2 hcon

/-! ### Innocent Exclusion & Summary Compression Non-Inheritance of Minimal Blockers -/

/-- Pragmatic strengthening rules on conditional summary cards (`condPerfection` and `scalarExh`). -/
inductive PragRule where
  | condPerfection
  | scalarExh
  deriving DecidableEq, Repr

/-- Conditional summary card `hyp → concl` with no hidden side-channel fields. -/
structure SummaryCard (W : Type) where
  hyp : WorldClaim W
  concl : WorldClaim W

/-- Literal truth condition of a summary card (`hyp w → concl w` evaluated per world). -/
def SummaryCard.lit {W : Type} (card : SummaryCard W) : WorldClaim W :=
  fun w => card.hyp w → card.concl w

/-- Subset `S` of indexed scalar alternatives in `alts` is jointly consistently excludable with `pre`
when some world satisfies `pre` and negates every alternative selected by `S`. -/
def ConsistentExcl {W : Type} (pre : WorldClaim W) (alts : List (WorldClaim W))
    (S : Fin alts.length → Prop) : Prop :=
  ∃ w : W, pre w ∧ ∀ i : Fin alts.length, S i → ¬ alts[i] w

/-- `S` is a maximal consistently excludable subset of `alts` relative to `pre`. -/
def MaximalConsistentExcl {W : Type} (pre : WorldClaim W) (alts : List (WorldClaim W))
    (S : Fin alts.length → Prop) : Prop :=
  ConsistentExcl pre alts S ∧
    ∀ S' : Fin alts.length → Prop, (∀ i, S i → S' i) → ConsistentExcl pre alts S' → ∀ i, S' i → S i

/-- Fox (2007) Innocent Exclusion: alternative `i` is innocently excludable given `pre` and `alts`
when `i` belongs to every maximal consistently excludable subset of `alts`. -/
def InnocentlyExcludable {W : Type} (pre : WorldClaim W) (alts : List (WorldClaim W))
    (i : Fin alts.length) : Prop :=
  ∀ S : Fin alts.length → Prop, MaximalConsistentExcl pre alts S → S i

/-- Innocently exhaustified scalar reading of `pre` against alternative set `alts`. -/
def innocentExh {W : Type} (pre : WorldClaim W) (alts : List (WorldClaim W)) : WorldClaim W :=
  fun w => pre w ∧ ∀ i : Fin alts.length, InnocentlyExcludable pre alts i → ¬ alts[i] w

/-- Pragmatic strengthening generated by rule `r` on `card` relative to scalar alternative set `alts`:
`condPerfection` invites converse `concl → hyp`; `scalarExh` applies `innocentExh card.lit alts`. -/
def SummaryCard.pragReading {W : Type} (alts : List (WorldClaim W)) (card : SummaryCard W) :
    PragRule → WorldClaim W
  | .condPerfection => fun w => card.concl w → card.hyp w
  | .scalarExh => innocentExh card.lit alts

/-- A card with blocker list `B` is implicature-safe under `(E, alts)` when its literal claim and every
unblocked pragmatic reading are entailed by `E`. -/
def ImplicatureSafe {W : Type} (E : WorldClaim W) (alts : List (WorldClaim W))
    (B : List PragRule) (card : SummaryCard W) : Prop :=
  EntailsEv E card.lit ∧ ∀ r : PragRule, r ∉ B → EntailsEv E (card.pragReading alts r)

/-- `B` is a minimal implicature-safe blocker list for `card` under `(E, alts)` when `B` is
duplicate-free, `ImplicatureSafe E alts B card` holds, and removing any `r ∈ B` breaks `ImplicatureSafe`. -/
def MinimalSafeBlockers {W : Type} (E : WorldClaim W) (alts : List (WorldClaim W))
    (B : List PragRule) (card : SummaryCard W) : Prop :=
  B.Nodup ∧ ImplicatureSafe E alts B card ∧
    ∀ r ∈ B, ¬ ImplicatureSafe E alts (B.filter (fun x => x != r)) card

/-- Canonical recomputed blocker list over `[.condPerfection, .scalarExh]` via classical decision. -/
noncomputable def recomputeBlockers {W : Type} (E : WorldClaim W) (alts : List (WorldClaim W))
    (card : SummaryCard W) : List PragRule := by
  letI : DecidablePred (fun r => ¬ EntailsEv E (card.pragReading alts r)) :=
    fun r => Classical.propDecidable _
  exact ([PragRule.condPerfection, PragRule.scalarExh]).filter
    (fun r => decide (¬ EntailsEv E (card.pragReading alts r)))

/-- Full two-conjunct card `H → (G₁ ∧ G₂)` on `W = Bool` with `H = (· = true)`, `G₁ = True`, `G₂ = (· = true)`. -/
def fullConjCard : SummaryCard Bool where
  hyp := fun b => b = true
  concl := fun b => True ∧ b = true

/-- Conclusion-dropped compression `H → G₁` obtained by dropping `G₂` from `fullConjCard`. -/
def compressedG1Card : SummaryCard Bool where
  hyp := fun b => b = true
  concl := fun _ => True

/-- Companion two-conjunct card `H → (H ∧ True)` whose conclusion-drop `H → H` stays implicature-safe. -/
def symmetricConjCard : SummaryCard Bool where
  hyp := fun b => b = true
  concl := fun b => b = true ∧ True

/-- Companion compressed card `H → H` obtained by dropping `True` from `symmetricConjCard`. -/
def symmetricCard : SummaryCard Bool where
  hyp := fun b => b = true
  concl := fun b => b = true

/-- Blocker insufficiency under conclusion-dropping compression: under `E = True` and `alts = []`,
`B = []` is minimal and implicature-safe for `fullConjCard` (`H → True ∧ H`), yet dropping the
second conjunct `G₂` to `compressedG1Card` (`H → True`) breaks `ImplicatureSafe` because
`(G₁ ∧ G₂) → H` strengthens contravariantly to `G₁ → H`. -/
theorem condPerfection_compression_breaks_minimal_safe_blocker :
    let E : WorldClaim Bool := fun _ => True
    MinimalSafeBlockers E [] [] fullConjCard ∧
    EntailsEv fullConjCard.lit compressedG1Card.lit ∧
    EntailsEv E compressedG1Card.lit ∧
    ¬ ImplicatureSafe E [] [] compressedG1Card := by
  intro E
  refine ⟨⟨by decide, ⟨?_, ?_⟩, fun _ h => by cases h⟩, ?_, ?_, ?_⟩
  · intro b _ hb; exact ⟨trivial, hb⟩
  · intro r _ b _
    cases r with
    | condPerfection => intro h; exact h.2
    | scalarExh => exact ⟨fun hb => ⟨trivial, hb⟩, fun i => Fin.elim0 i⟩
  · intro b hfull hb; exact (hfull hb).1
  · intro _ _ _; trivial
  · intro hsafe
    have hperf := hsafe.2 .condPerfection (fun h => by cases h) false trivial trivial
    cases hperf

/-- Scalar alternative `{0, 2}` (`w.1 ≠ 1`) on `Fin 3` for innocent-exclusion compression testing. -/
def fin3Alt02 : WorldClaim (Fin 3) := fun w => w.1 ≠ 1

/-- Scalar alternative `{1, 2}` (`w.1 ≠ 0`) on `Fin 3` for innocent-exclusion compression testing. -/
def fin3Alt12 : WorldClaim (Fin 3) := fun w => w.1 ≠ 0

/-- Dual blocker superfluity (loss of minimality) under genuine conclusion-dropping `(H, G₁ ∧ G₂) ↦ (H, G₁)`
with fixed evidence `E = fin3Alt12` and fixed alternative scale `alts = [fin3Alt02, fin3Alt12]`:
on `preCard = ⟨True, (fin3Alt02 ∨ fin3Alt12) ∧ fin3Alt12⟩`, `fin3Alt02` is innocently excludable and
unentailed by `E` (making `[.scalarExh]` minimal and safe), whereas dropping `G₂ = fin3Alt12` yields
`postCard = ⟨True, fin3Alt02 ∨ fin3Alt12⟩` on which `{fin3Alt02}` and `{fin3Alt12}` clash as distinct
maximal excludable sets so `innocentExh` excludes nothing and `[.scalarExh]` ceases to be minimal. -/
theorem scalarExh_compression_breaks_blocker_minimality :
    let E : WorldClaim (Fin 3) := fin3Alt12
    let alts : List (WorldClaim (Fin 3)) := [fin3Alt02, fin3Alt12]
    let H : WorldClaim (Fin 3) := fun _ => True
    let G₁ : WorldClaim (Fin 3) := fun w => fin3Alt02 w ∨ fin3Alt12 w
    let G₂ : WorldClaim (Fin 3) := fin3Alt12
    let preCard : SummaryCard (Fin 3) := ⟨H, fun w => G₁ w ∧ G₂ w⟩
    let postCard : SummaryCard (Fin 3) := ⟨H, G₁⟩
    MinimalSafeBlockers E alts [.scalarExh] preCard ∧
    EntailsEv preCard.lit postCard.lit ∧
    ImplicatureSafe E alts [] postCard ∧
    ImplicatureSafe E alts [.scalarExh] postCard ∧
    ¬ MinimalSafeBlockers E alts [.scalarExh] postCard := by
  intro E alts H G₁ G₂ preCard postCard
  have hpreLit : EntailsEv E preCard.lit :=
    fun _ hw _ => ⟨Or.inr hw, hw⟩
  have hpostLit : EntailsEv E postCard.lit :=
    fun _ hw _ => Or.inr hw
  -- On `preCard`, every maximal consistent exclusion set contains index `0` (`fin3Alt02`).
  have hexclPre0 : InnocentlyExcludable preCard.lit alts ⟨0, by decide⟩ := by
    intro S ⟨⟨w₀, hpre₀, hS₀⟩, hmax⟩
    have hnotS1 : ¬ S ⟨1, by decide⟩ := by
      intro hs1
      have hn12 : ¬ fin3Alt12 w₀ := hS₀ ⟨1, by decide⟩ hs1
      exact hn12 (hpre₀ trivial).2
    let S' : Fin alts.length → Prop := fun i => i.1 = 0
    have hsub : ∀ i : Fin alts.length, S i → S' i := by
      intro ⟨i, hi⟩ hsi
      by_cases h0 : i = 0
      · exact h0
      · have h1 : i = 1 := by simp [alts] at hi; omega
        subst h1
        exact False.elim (hnotS1 hsi)
    have hcons' : ConsistentExcl preCard.lit alts S' := by
      refine ⟨⟨1, by omega⟩, (fun _ => ⟨Or.inr (by simp [fin3Alt12]), by simp [G₂, fin3Alt12]⟩), ?_⟩
      intro ⟨i, hi⟩ hsi
      dsimp [S'] at hsi
      subst hsi
      simp [alts, fin3Alt02]
    exact hmax S' hsub hcons' ⟨0, by decide⟩ rfl
  -- Consequently, `E` does NOT entail `preCard.pragReading alts .scalarExh` (witness: world `2`).
  have hpreUnsafeEmpty : ¬ ImplicatureSafe E alts [] preCard := by
    intro hsafe
    have hexh2 := hsafe.2 .scalarExh (by simp) ⟨2, by omega⟩ (by simp [E, fin3Alt12])
    have hn02 : ¬ fin3Alt02 ⟨2, by omega⟩ := hexh2.2 ⟨0, by decide⟩ hexclPre0
    exact hn02 (by simp [fin3Alt02])
  -- On `postCard`, neither `0` nor `1` is innocently excludable because `{0}` and `{1}` are both maximal!
  have hmaxPost0 : MaximalConsistentExcl postCard.lit alts (fun i => i.1 = 0) := by
    refine ⟨⟨⟨1, by omega⟩, (fun _ => Or.inr (by simp [fin3Alt12])), ?_⟩, ?_⟩
    · intro ⟨i, hi⟩ hi0; dsimp at hi0; subst hi0; simp [alts, fin3Alt02]
    · intro S' hsub ⟨⟨w, hw⟩, _, hS'⟩ ⟨i, hi⟩ hsi'
      by_cases h0 : i = 0
      · exact h0
      · have h1 : i = 1 := by simp [alts] at hi; omega
        subst h1
        have hn0 : ¬ fin3Alt02 ⟨w, hw⟩ := hS' ⟨0, by decide⟩ (hsub ⟨0, by decide⟩ rfl)
        have hn1 : ¬ fin3Alt12 ⟨w, hw⟩ := hS' ⟨1, by decide⟩ hsi'
        dsimp [alts, fin3Alt02, fin3Alt12] at hn0 hn1
        omega
  have hmaxPost1 : MaximalConsistentExcl postCard.lit alts (fun i => i.1 = 1) := by
    refine ⟨⟨⟨0, by omega⟩, (fun _ => Or.inl (by simp [fin3Alt02])), ?_⟩, ?_⟩
    · intro ⟨i, hi⟩ hi1; dsimp at hi1; subst hi1; simp [alts, fin3Alt12]
    · intro S' hsub ⟨⟨w, hw⟩, _, hS'⟩ ⟨i, hi⟩ hsi'
      by_cases h1 : i = 1
      · exact h1
      · have h0 : i = 0 := by simp [alts] at hi; omega
        subst h0
        have hn0 : ¬ fin3Alt02 ⟨w, hw⟩ := hS' ⟨0, by decide⟩ hsi'
        have hn1 : ¬ fin3Alt12 ⟨w, hw⟩ := hS' ⟨1, by decide⟩ (hsub ⟨1, by decide⟩ rfl)
        dsimp [alts, fin3Alt02, fin3Alt12] at hn0 hn1
        omega
  have hpostSafeEmpty : ImplicatureSafe E alts [] postCard := by
    refine ⟨hpostLit, ?_⟩
    intro r _ w hw
    cases r with
    | condPerfection => exact fun _ => trivial
    | scalarExh =>
      refine ⟨hpostLit w hw, ?_⟩
      intro ⟨i, hi⟩ hie
      by_cases h0 : i = 0
      · subst h0
        have bad : (0 : Nat) = 1 := hie _ hmaxPost1
        omega
      · have h1 : i = 1 := by simp [alts] at hi; omega
        subst h1
        have bad : (1 : Nat) = 0 := hie _ hmaxPost0
        omega
  have hpreSafeScalar : ImplicatureSafe E alts [.scalarExh] preCard := by
    refine ⟨hpreLit, ?_⟩
    intro r hr _ _
    cases r with
    | condPerfection => exact fun _ => trivial
    | scalarExh => exact False.elim (hr (List.mem_singleton.2 rfl))
  have hpostSafeScalar : ImplicatureSafe E alts [.scalarExh] postCard := by
    refine ⟨hpostLit, ?_⟩
    intro r hr _ _
    cases r with
    | condPerfection => exact fun _ => trivial
    | scalarExh => exact False.elim (hr (List.mem_singleton.2 rfl))
  refine ⟨⟨by simp, hpreSafeScalar, ?_⟩, (fun _ h hh => (h hh).1),
    hpostSafeEmpty, hpostSafeScalar, ?_⟩
  · intro r hr hsafe
    rcases List.mem_singleton.1 hr with rfl
    simpa using hpreUnsafeEmpty hsafe
  · intro hmin
    apply hmin.2.2 .scalarExh (List.mem_singleton.2 rfl)
    simpa using hpostSafeEmpty

/-- Non-Markovian impossibility across genuine conclusion-dropping `(H, G₁ ∧ G₂) ↦ (H, G₁)`:
even on `W = Bool` with `E = True`, `alts = []`, and `B = []`, no stateless boolean function
`f : Bool → Bool` computes post-drop `ImplicatureSafe` from pre-drop `ImplicatureSafe` alone. -/
theorem no_stateless_implicature_transfer_for_compression :
    ¬ ∃ f : Bool → Bool,
        ∀ (H G₁ G₂ : WorldClaim Bool) (b₁ b₂ : Bool),
          (b₁ = true ↔ ImplicatureSafe (fun _ => True) [] [] ⟨H, fun w => G₁ w ∧ G₂ w⟩) →
          (b₂ = true ↔ ImplicatureSafe (fun _ => True) [] [] ⟨H, G₁⟩) →
          f b₁ = b₂ := by
  rintro ⟨f, hf⟩
  have h1 := condPerfection_compression_breaks_minimal_safe_blocker
  have hsymFull : ImplicatureSafe (fun _ => True) [] [] symmetricConjCard := by
    refine ⟨fun _ _ hb => ⟨hb, trivial⟩, ?_⟩
    intro r _ b _
    cases r with
    | condPerfection => exact fun h => h.1
    | scalarExh => exact ⟨fun hb => ⟨hb, trivial⟩, fun i => Fin.elim0 i⟩
  have hsymDrop : ImplicatureSafe (fun _ => True) [] [] symmetricCard := by
    refine ⟨fun _ _ hb => hb, ?_⟩
    intro r _ b _
    cases r with
    | condPerfection => exact fun h => h
    | scalarExh => exact ⟨fun hb => hb, fun i => Fin.elim0 i⟩
  have eqFalse : f true = false :=
    hf (fun b => b = true) (fun _ => True) (fun b => b = true) true false
      ⟨fun _ => h1.1.2.1, fun _ => rfl⟩
      ⟨(fun h => by cases h), fun hs => False.elim (h1.2.2.2 hs)⟩
  have eqTrue : f true = true :=
    hf (fun b => b = true) (fun b => b = true) (fun _ => True) true true
      ⟨fun _ => hsymFull, fun _ => rfl⟩
      ⟨fun _ => hsymDrop, fun _ => rfl⟩
  rw [eqTrue] at eqFalse
  cases eqFalse

/-- Positive control & repair for `no_stateless_implicature_transfer_for_compression`:
recomputing `recomputeBlockers E alts card` directly on the compressed card restores both
`ImplicatureSafe` and `MinimalSafeBlockers` whenever `EntailsEv E card.lit`. -/
theorem recomputeBlockers_safe_and_minimal {W : Type} (E : WorldClaim W)
    (alts : List (WorldClaim W)) (card : SummaryCard W)
    (hlit : EntailsEv E card.lit) :
    MinimalSafeBlockers E alts (recomputeBlockers E alts card) card := by
  let p : PragRule → Bool := fun r => by
    letI := Classical.propDecidable (¬ EntailsEv E (card.pragReading alts r))
    exact decide (¬ EntailsEv E (card.pragReading alts r))
  have hrec : recomputeBlockers E alts card = [PragRule.condPerfection, PragRule.scalarExh].filter p := rfl
  rw [hrec]
  have hnodup_base : ([PragRule.condPerfection, PragRule.scalarExh] : List PragRule).Nodup := by decide
  refine ⟨hnodup_base.filter p, ⟨hlit, ?_⟩, ?_⟩
  · intro r hnotmem
    have hall : r ∈ ([PragRule.condPerfection, PragRule.scalarExh] : List PragRule) := by
      cases r <;> decide
    refine Classical.byContradiction fun hnent => ?_
    apply hnotmem
    rw [List.mem_filter]
    refine ⟨hall, ?_⟩
    dsimp [p]
    by_cases h : ¬ EntailsEv E (card.pragReading alts r)
    · simp [h]
    · exact False.elim (h hnent)
  · intro r hmem hsafe
    rw [List.mem_filter] at hmem
    rcases hmem with ⟨_, hp⟩
    have hnent : ¬ EntailsEv E (card.pragReading alts r) := by
      dsimp [p] at hp
      by_cases h : ¬ EntailsEv E (card.pragReading alts r)
      · exact h
      · simp [h] at hp
    have hnot_in_rem :
        r ∉ ([PragRule.condPerfection, PragRule.scalarExh].filter p).filter (fun x => x != r) := by
      intro hin
      rw [List.mem_filter] at hin
      simp at hin
    exact hnent (hsafe.2 r hnot_in_rem)

/-! ### Proved Positive and Negative Examples & Non-Vacuity Witnesses for `Compression.lean` -/

theorem entailsEv_pos : EntailsEv (fun b : Bool => b = true) (fun b => b = true) := fun _ h => h
theorem entailsEv_neg : ¬ EntailsEv (fun _ : Bool => True) (fun b => b = true) := by
  intro h; exact Bool.noConfusion (h false trivial)

theorem contradictsEv_pos : ContradictsEv (fun b : Bool => b = true) (fun _ => False) :=
  fun _ _ hf => hf

theorem contradictsEv_neg : ¬ ContradictsEv (fun _ : Bool => True) (fun b => b = true) := by
  intro h; exact h true trivial rfl

theorem undeterminedEv_pos : UndeterminedEv (fun _ : Bool => True) (fun b => b = true) :=
  ⟨entailsEv_neg, contradictsEv_neg⟩

theorem undeterminedEv_neg : ¬ UndeterminedEv (fun b : Bool => b = true) (fun b => b = true) :=
  fun h => h.1 entailsEv_pos

theorem exhaustifiedOnlyReading_pos :
    exhaustifiedOnlyReading (fun b : Bool => b = true) (fun _ => False) true :=
  ⟨rfl, id⟩

theorem exhaustifiedOnlyReading_neg :
    ¬ exhaustifiedOnlyReading (fun b : Bool => b = true) (fun _ => True) true :=
  fun h => h.2 trivial

theorem disclaimerSafe_pos :
    DisclaimerSafe (fun _ : Bool => True) (fun _ => True) (fun b => b = true) .neitherNor :=
  (neitherNorDisclaimerSafe_iff _ _ _).2 ⟨fun _ h => h, undeterminedEv_pos⟩

theorem disclaimerSafe_neg :
    ¬ DisclaimerSafe (fun _ : Bool => True) (fun _ => True) (fun b => b = true) .bareOnly :=
  (exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined
    (fun _ : Bool => True) (fun _ => True) (fun b => b = true) (fun _ h => h) undeterminedEv_pos).1

theorem neitherNorDisclaimerSafe_pos :
    NeitherNorDisclaimerSafe (fun _ : Bool => True) (fun _ => True) (fun b => b = true) :=
  disclaimerSafe_pos

theorem neitherNorDisclaimerSafe_neg :
    ¬ NeitherNorDisclaimerSafe (fun b : Bool => b = true) (fun _ => True) (fun b => b = true) := by
  rw [neitherNorDisclaimerSafe_iff]
  exact fun h => undeterminedEv_neg h.2

theorem implicatureSafe_pos : ImplicatureSafe (fun _ => True) [] [] fullConjCard :=
  condPerfection_compression_breaks_minimal_safe_blocker.1.2.1

theorem implicatureSafe_neg : ¬ ImplicatureSafe (fun _ => True) [] [] compressedG1Card :=
  condPerfection_compression_breaks_minimal_safe_blocker.2.2.2

theorem minimalSafeBlockers_pos : MinimalSafeBlockers (fun _ => True) [] [] fullConjCard :=
  condPerfection_compression_breaks_minimal_safe_blocker.1

theorem minimalSafeBlockers_neg : ¬ MinimalSafeBlockers (fun _ => True) [] [] compressedG1Card :=
  fun h => implicatureSafe_neg h.2.1

theorem innocentExh_pos :
    innocentExh (fun _ : Bool => True) [(fun b : Bool => b = true)] false := by
  refine ⟨trivial, ?_⟩
  intro ⟨i, hi⟩ _
  have hi0 : i = 0 := by simp at hi; omega
  subst hi0
  intro hf
  cases hf

theorem innocentExh_neg :
    ¬ innocentExh (fun _ : Bool => True) [(fun b : Bool => b = true)] true := by
  intro hexh
  have hie : InnocentlyExcludable (fun _ : Bool => True) [(fun b : Bool => b = true)] ⟨0, by decide⟩ := by
    intro S ⟨_, hmax⟩
    refine hmax (fun _ => True) (fun _ _ => trivial) ⟨false, trivial, ?_⟩ ⟨0, by decide⟩ trivial
    intro ⟨i, hi⟩ _
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    intro hf
    cases hf
  exact hexh.2 ⟨0, by decide⟩ hie rfl

/-- Joint non-vacuity witness for `exhaustifiedOnly_sound_iff_contradictsEv` and
`exhaustifiedOnly_unsound_and_neitherNor_safe_of_undetermined`. -/
theorem nonvacuity_exhaustifiedOnly :
    (EntailsEv (fun b : Bool => b = true) (fun b => b = true) ∧
     ContradictsEv (fun b : Bool => b = true) (fun b => b = false)) ∧
    (EntailsEv (fun _ : Bool => True) (fun _ => True) ∧
     UndeterminedEv (fun _ : Bool => True) (fun b : Bool => b = true) ∧
     NeitherNorDisclaimerSafe (fun _ : Bool => True) (fun _ => True) (fun b : Bool => b = true)) :=
  ⟨⟨entailsEv_pos, fun b hb hf => by rw [hb] at hf; cases hf⟩,
   ⟨fun _ h => h, undeterminedEv_pos, neitherNorDisclaimerSafe_pos⟩⟩

end Toy.BoundaryLicensing
