import ToyWMM.Lemmas
import ToyWMM.Prog
import ToyWMM.Litmus

/-!
# Fence-insertion mappings: soundness

The TSO ordering axiom differs from SC only on `po` write→read pairs (dropped from `ppo`) and
on internal reads-from (`rfi`, store forwarding). A fence between a write and a later read of
the same thread restores the pair through `fenceOrd = [RW] ; po ; [F] ; po ; [RW]`.
-/

namespace Toy.WMM

open Litmus

namespace Exec

variable {n : Nat} (X : Exec n)

theorem eraseFences_scRel_iff {a b : Fin n} :
    X.eraseFences X.scRel a b = true ↔
      X.scRel a b = true ∧ (X.ev a).isAccess = true ∧ (X.ev b).isAccess = true := by
  simp [eraseFences, Rel.restrict, and_assoc]

theorem scRel_cases {a b : Fin n} (h : X.scRel a b = true) :
    X.po a b = true ∨ X.rf a b = true ∨ X.co a b = true ∨ X.fr a b = true := by
  simp only [scRel, Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

end Exec

/-! ## Fencing every write→read pair restores SC -/

/-- **Fence-mapping soundness (execution level).** If `po` is total on each thread, `rf` is
location-respecting, every `po` write→read pair is separated by a fence, and the execution is
TSO-consistent (SC per location and the TSO ordering axiom), then it is SC-consistent once its
fence events are erased. -/
theorem scConsistentErased_of_tso_of_fenceBetweenWR {n : Nat} (X : Exec n)
    (htot : X.PoTotal) (hrf : X.RfSameLoc) (hfence : X.FenceBetweenWR)
    (hloc : X.PerLocSC) (hghb : X.TsoGhbAcyclic) : X.SCConsistentErased := by
  refine Rel.Acyclic.mono ?_ hghb
  intro a b hab
  obtain ⟨h, ha, hb⟩ := (X.eraseFences_scRel_iff).mp hab
  have hpo : X.po a b = true → X.tsoRel a b = true := fun hpo =>
    X.tsoRel_of_po_of_fenced hpo ha hb (hfence a b hpo)
  rcases X.scRel_cases h with h | h | h | h
  · exact hpo h
  · cases hst : X.sameThread a b with
    | true =>
      exact hpo (X.po_of_uniproc_edge hloc htot (X.uniprocRel_of_rf h) (hrf a b h) ha hb hst)
    | false => simp [Exec.tsoRel, Exec.rfe, h, hst]
  · simp [Exec.tsoRel, h]
  · simp [Exec.tsoRel, h]

/-- **Fence-mapping soundness (program level).** For every program `P`, every candidate
execution of `fenceAfterStores P` (an `mfence` inserted immediately after every store) whose
`rf` respects locations and which is TSO-consistent is SC-consistent once its fence events
are erased. -/
theorem scConsistentErased_of_tso_fenceAfterStores (P : Prog) {n : Nat} (X : Exec n)
    (hX : ExecOf (fenceAfterStores P) X) (hrf : X.RfSameLoc) (hloc : X.PerLocSC)
    (hghb : X.TsoGhbAcyclic) : X.SCConsistentErased :=
  scConsistentErased_of_tso_of_fenceBetweenWR X hX.poTotal hrf
    hX.fenceBetweenWR_of_fenceAfterStores hloc hghb

/-! ## Fencing only write→read pairs between shared locations suffices -/

private theorem po_of_uniproc_path {n : Nat} (X : Exec n)
    (hloc : X.PerLocSC) (htot : X.PoTotal) {a b : Fin n}
    (hp : Rel.Path X.uniprocRel a b) (hsl : X.sameLoc a b = true)
    (ha : (X.ev a).isAccess = true) (hb : (X.ev b).isAccess = true)
    (hst : X.sameThread a b = true) : X.po a b = true := by
  have hne : a ≠ b := by
    rintro rfl; exact hloc a hp
  rcases htot a b hne hst with h' | h'
  · exact h'
  · exfalso
    have hba : X.uniprocRel b a = true := by
      simp [Exec.uniprocRel, Exec.poLoc, h', X.sameLoc_symm hsl, ha, hb]
    exact hloc a (Rel.Path.tail hp hba)

/-- **Shared-location fencing soundness (execution level).** Fencing only the `po`
write→read pairs whose write and read are both to locations accessed (excluding
initialisation) by two or more threads still makes every TSO-consistent execution
SC-consistent after fence erasure, provided `po` is a transitive, per-thread, per-thread-total
relation and `rf` and `co` only relate events at the same location. -/
theorem scConsistentErased_of_tso_of_fenceBetweenBothSharedWR {n : Nat} (X : Exec n)
    (hptrans : X.PoTrans) (hpth : X.PoWithinThread) (htot : X.PoTotal)
    (hrfl : X.RfSameLoc) (hcol : X.CoSameLoc)
    (hfence : X.FenceBetweenBothSharedWR) (hloc : X.PerLocSC) (hghb : X.TsoGhbAcyclic) :
    X.SCConsistentErased := by
  let s := X.eraseFences X.scRel
  let isShared (v : Fin n) : Bool := decide (¬ X.LocalLoc (X.ev v).loc)
  -- Helper: any `s` edge changing location must be a `po` edge (hence non-init, same thread).
  have po_of_diff_loc : ∀ a b, s a b = true → (X.ev a).loc ≠ (X.ev b).loc → X.po a b = true := by
    intro a b hab hdiff
    obtain ⟨h, _, _⟩ := X.eraseFences_scRel_iff.mp hab
    rcases X.scRel_cases h with h | h | h | h
    · exact h
    · exact absurd (by simpa [Exec.sameLoc] using hrfl a b h) hdiff
    · exact absurd (by simpa [Exec.sameLoc] using hcol a b h) hdiff
    · obtain ⟨w, hw1, hw2⟩ := X.fr_iff.mp h
      have hsl := X.sameLoc_trans (X.sameLoc_symm (hrfl w a hw1)) (hcol w b hw2)
      exact absurd (by simpa [Exec.sameLoc] using hsl) hdiff
  -- Helper: any `s` edge preserving location is a `uniprocRel` edge.
  have uniproc_of_same_loc : ∀ a b, s a b = true → (X.ev a).loc = (X.ev b).loc →
      X.uniprocRel a b = true := by
    intro a b hab heq
    obtain ⟨h, ha, hb⟩ := X.eraseFences_scRel_iff.mp hab
    rcases X.scRel_cases h with h | h | h | h
    · simp [Exec.uniprocRel, Exec.poLoc, Exec.sameLoc, h, heq, ha, hb]
    · exact X.uniprocRel_of_rf h
    · exact X.uniprocRel_of_co h
    · exact X.uniprocRel_of_fr h
  -- Helper: `po` is irreflexive on memory accesses (from `TsoGhbAcyclic`).
  have hpirr : ∀ a, (X.ev a).isAccess = true → X.po a a = false := by
    intro a hacc
    cases h : X.po a a with
    | false => rfl
    | true =>
      exfalso
      apply hghb a
      apply Rel.Path.single
      have : ((X.ev a).isWrite && (X.ev a).isRead) = false := by
        simp only [Event.isWrite, Event.isRead]; cases (X.ev a).kind <;> rfl
      simp [Exec.tsoRel, Exec.ppo, h, this, hacc]
  -- Helper: given a non-init access `c` at a local location with `Star uniprocRel c x` and
  -- `po x y` (hence `x` is non-init access), we get `Star po c x`, so `po c y`.
  have po_bridge : ∀ {c x y}, (X.ev c).isAccess = true → (X.ev c).isInit = false →
      (X.ev x).isAccess = true → (X.ev c).loc = (X.ev x).loc →
      X.LocalLoc (X.ev c).loc → Rel.Star X.uniprocRel c x → X.po x y = true →
      X.po c y = true := by
    intro c x y hca hci hxa hcloc hlocC hstar hxy
    have hst_xy := hpth x y hxy
    simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true'] at hst_xy
    have hxi : (X.ev x).isInit = false := hst_xy.1.1
    rcases hstar with rfl | hup
    · exact hxy
    · have htid : (X.ev c).tid = (X.ev x).tid := hlocC c x hca hxa hci hxi rfl hcloc.symm
      have hst_cx : X.sameThread c x = true := by simp [Exec.sameThread, hci, hxi, htid]
      have hsl_cx : X.sameLoc c x = true := by simp [Exec.sameLoc, hcloc]
      have hcx : X.po c x = true := po_of_uniproc_path X hloc htot hup hsl_cx hca hxa hst_cx
      exact hptrans c x y hcx hxy
  -- Helper: any edge between shared vertices is a `tsoRel` edge.
  have tso_of_shared : ∀ a b, s a b = true → isShared a = true → isShared b = true →
      X.tsoRel a b = true := by
    intro a b hab hsa hsb
    obtain ⟨h, ha, hb⟩ := X.eraseFences_scRel_iff.mp hab
    have hsha : ¬ X.LocalLoc (X.ev a).loc := by simpa [isShared] using hsa
    have hshb : ¬ X.LocalLoc (X.ev b).loc := by simpa [isShared] using hsb
    have hpo_tso : X.po a b = true → X.tsoRel a b = true := fun hpo =>
      X.tsoRel_of_po_of_fenced hpo ha hb (fun hw hr => hfence a b hpo hw hr hsha hshb)
    rcases X.scRel_cases h with h | h | h | h
    · exact hpo_tso h
    · cases hst : X.sameThread a b with
      | true =>
        exact hpo_tso (X.po_of_uniproc_edge hloc htot (X.uniprocRel_of_rf h) (hrfl a b h) ha hb hst)
      | false => simp [Exec.tsoRel, Exec.rfe, h, hst]
    · simp [Exec.tsoRel, h]
    · simp [Exec.tsoRel, h]
  -- Core path shortening from a shared vertex `u`:
  -- Either `y` is shared and `Path tsoRel u y`, OR `y` is local and there is a shared `z`
  -- (`Star tsoRel u z`) and a non-init access `c` at `loc y` with `po z c` and `Star uniprocRel c y`.
  have shorten : ∀ {u y : Fin n}, isShared u = true → Rel.Path s u y →
      (isShared y = true → Rel.Path X.tsoRel u y) ∧
      (isShared y = false → ∃ z c, isShared z = true ∧ (X.ev z).isAccess = true ∧
        Rel.Star X.tsoRel u z ∧
        (X.ev c).isAccess = true ∧ (X.ev c).isInit = false ∧ (X.ev c).loc = (X.ev y).loc ∧
        X.po z c = true ∧ Rel.Star X.uniprocRel c y) := by
    intro u y hu hp
    induction hp with
    | @single b hub =>
      constructor
      · intro hb; exact Rel.Path.single (tso_of_shared u b hub hu hb)
      · intro hb
        have hdiff : (X.ev u).loc ≠ (X.ev b).loc := by
          intro heq
          have h1 : ¬ X.LocalLoc (X.ev u).loc := by simpa [isShared] using hu
          have h2 : X.LocalLoc (X.ev b).loc := by simpa [isShared] using hb
          rw [heq] at h1; exact h1 h2
        have hpo := po_of_diff_loc u b hub hdiff
        have hst := hpth u b hpo
        simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true'] at hst
        obtain ⟨_, hua, hba⟩ := X.eraseFences_scRel_iff.mp hub
        exact ⟨u, b, hu, hua, Or.inl rfl, hba, hst.1.2, rfl, hpo, Or.inl rfl⟩
    | @tail x b _ hxb ih =>
      cases hx : isShared x with
      | true =>
        have hux := ih.1 hx
        constructor
        · intro hb; exact Rel.Path.tail hux (tso_of_shared x b hxb hx hb)
        · intro hb
          have hdiff : (X.ev x).loc ≠ (X.ev b).loc := by
            intro heq
            have h1 : ¬ X.LocalLoc (X.ev x).loc := by simpa [isShared] using hx
            have h2 : X.LocalLoc (X.ev b).loc := by simpa [isShared] using hb
            rw [heq] at h1; exact h1 h2
          have hpo := po_of_diff_loc x b hxb hdiff
          have hst := hpth x b hpo
          simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true'] at hst
          obtain ⟨_, hxa, hba⟩ := X.eraseFences_scRel_iff.mp hxb
          exact ⟨x, b, hx, hxa, Or.inr hux, hba, hst.1.2, rfl, hpo, Or.inl rfl⟩
      | false =>
        obtain ⟨z, c, hz, hza, huz, hca, hci, hcloc, hzc, hcx⟩ := ih.2 hx
        obtain ⟨_, hxa, hba⟩ := X.eraseFences_scRel_iff.mp hxb
        have hlocX : X.LocalLoc (X.ev x).loc := by simpa [isShared] using hx
        have hlocC : X.LocalLoc (X.ev c).loc := hcloc ▸ hlocX
        by_cases hsame : (X.ev x).loc = (X.ev b).loc
        · have hub : X.uniprocRel x b = true := uniproc_of_same_loc x b hxb hsame
          have hcb : Rel.Star X.uniprocRel c b := Or.inr (Rel.Star.path_of_star_of_edge hcx hub)
          have hsb_false : isShared b = false := by
            simp only [isShared, decide_eq_false_iff_not, Classical.not_not]
            exact hsame ▸ hlocX
          constructor
          · intro hb; rw [hsb_false] at hb; exact absurd hb (by decide)
          · intro _; exact ⟨z, c, hz, hza, huz, hca, hci, hcloc.trans hsame, hzc, hcb⟩
        · have hpo_xb : X.po x b = true := po_of_diff_loc x b hxb hsame
          have hpo_cb : X.po c b = true := po_bridge hca hci hxa hcloc hlocC hcx hpo_xb
          have hpo_zb : X.po z b = true := hptrans z c b hzc hpo_cb
          have hst_xb := hpth x b hpo_xb
          simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true'] at hst_xb
          constructor
          · intro hb
            have hsha : ¬ X.LocalLoc (X.ev z).loc := by simpa [isShared] using hz
            have hshb : ¬ X.LocalLoc (X.ev b).loc := by simpa [isShared] using hb
            have htso_zb : X.tsoRel z b = true :=
              X.tsoRel_of_po_of_fenced hpo_zb hza hba
                (fun hw hr => hfence z b hpo_zb hw hr hsha hshb)
            exact Rel.Star.path_of_star_of_edge huz htso_zb
          · intro _
            exact ⟨z, b, hz, hza, huz, hba, hst_xb.1.2, rfl, hpo_zb, Or.inl rfl⟩
  -- Helper: transitivity of `Rel.Star`.
  have star_trans : ∀ {r : Rel n} {a b c : Fin n}, Rel.Star r a b → Rel.Star r b c → Rel.Star r a c := by
    intro r a b c h1 h2
    rcases h1 with rfl | h1
    · exact h2
    · rcases h2 with rfl | h2
      · exact Or.inr h1
      · exact Or.inr (Rel.Path.trans h1 h2)
  -- Helper: paths starting from a local vertex either reach a shared vertex, stay at one
  -- location (giving a `uniprocRel` path), or cross locations via `po`.
  have local_path : ∀ {x y : Fin n}, isShared x = false → Rel.Path s x y →
      (∃ z, isShared z = true ∧ Rel.Path s x z ∧ Rel.Star s z y) ∨
      (isShared y = false ∧ (X.ev x).loc = (X.ev y).loc ∧ Rel.Path X.uniprocRel x y) ∨
      (∃ w c, isShared y = false ∧
        (X.ev w).isAccess = true ∧ (X.ev w).isInit = false ∧ (X.ev w).loc = (X.ev x).loc ∧
        Rel.Star X.uniprocRel x w ∧
        (X.ev c).isAccess = true ∧ (X.ev c).isInit = false ∧ (X.ev c).loc = (X.ev y).loc ∧
        X.po w c = true ∧ Rel.Star X.uniprocRel c y) := by
    intro x y hx hp
    induction hp with
    | @single b hxb =>
      cases hb : isShared b with
      | true => exact Or.inl ⟨b, hb, Rel.Path.single hxb, Or.inl rfl⟩
      | false =>
        by_cases hsame : (X.ev x).loc = (X.ev b).loc
        · exact Or.inr (Or.inl ⟨rfl, hsame, Rel.Path.single (uniproc_of_same_loc x b hxb hsame)⟩)
        · have hpo := po_of_diff_loc x b hxb hsame
          have hst := hpth x b hpo
          simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true'] at hst
          obtain ⟨_, hxa, hba⟩ := X.eraseFences_scRel_iff.mp hxb
          exact Or.inr (Or.inr ⟨x, b, rfl, hxa, hst.1.1, rfl, Or.inl rfl, hba, hst.1.2, rfl, hpo, Or.inl rfl⟩)
    | @tail b b' hxb hbb' ih =>
      rcases ih with ⟨z, hz, hxz, hzb⟩ | ⟨hb, hloc_xb, hup_xb⟩ |
        ⟨w, c, hb, hwa, hwi, hwloc, hxw, hca, hci, hcloc, hwc, hcb⟩
      · exact Or.inl ⟨z, hz, hxz, Or.inr (Rel.Star.path_of_star_of_edge hzb hbb')⟩
      · cases hb' : isShared b' with
        | true => exact Or.inl ⟨b', hb', Rel.Path.tail hxb hbb', Or.inl rfl⟩
        | false =>
          by_cases hsame : (X.ev b).loc = (X.ev b').loc
          · exact Or.inr (Or.inl ⟨rfl, hloc_xb.trans hsame,
              Rel.Path.tail hup_xb (uniproc_of_same_loc b b' hbb' hsame)⟩)
          · have hpo := po_of_diff_loc b b' hbb' hsame
            have hst := hpth b b' hpo
            simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true'] at hst
            obtain ⟨_, hba, hb'a⟩ := X.eraseFences_scRel_iff.mp hbb'
            exact Or.inr (Or.inr ⟨b, b', rfl, hba, hst.1.1, hloc_xb.symm, Or.inr hup_xb,
              hb'a, hst.1.2, rfl, hpo, Or.inl rfl⟩)
      · cases hb' : isShared b' with
        | true => exact Or.inl ⟨b', hb', Rel.Path.tail hxb hbb', Or.inl rfl⟩
        | false =>
          by_cases hsame : (X.ev b).loc = (X.ev b').loc
          · exact Or.inr (Or.inr ⟨w, c, rfl, hwa, hwi, hwloc, hxw, hca, hci, hcloc.trans hsame,
              hwc, Or.inr (Rel.Star.path_of_star_of_edge hcb (uniproc_of_same_loc b b' hbb' hsame))⟩)
          · have hpo := po_of_diff_loc b b' hbb' hsame
            have hst := hpth b b' hpo
            simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true'] at hst
            obtain ⟨_, hba, hb'a⟩ := X.eraseFences_scRel_iff.mp hbb'
            have hlocB : X.LocalLoc (X.ev b).loc := by simpa [isShared] using hb
            have hlocC : X.LocalLoc (X.ev c).loc := hcloc ▸ hlocB
            have hpo_cb' : X.po c b' = true := po_bridge hca hci hba hcloc hlocC hcb hpo
            have hpo_wb' : X.po w b' = true := hptrans w c b' hwc hpo_cb'
            exact Or.inr (Or.inr ⟨w, b', rfl, hwa, hwi, hwloc, hxw, hb'a, hst.1.2, rfl,
              hpo_wb', Or.inl rfl⟩)
  -- Final assembly: no cycle in `s`.
  intro a ha
  cases hsa : isShared a with
  | true => exact hghb a ((shorten hsa ha).1 hsa)
  | false =>
    rcases local_path hsa ha with ⟨z, hz, haz, hza⟩ | ⟨_, _, hup⟩ |
      ⟨w, c, _, hwa, hwi, hwloc, haw, hca, hci, hcloc, hwc, hca_up⟩
    · have hzz : Rel.Path s z z := by
        rcases hza with rfl | hza
        · rw [hz] at hsa; exact absurd hsa (by decide)
        · exact Rel.Path.trans hza haz
      exact hghb z ((shorten hz hzz).1 hz)
    · exact hloc a hup
    · have hlocA : X.LocalLoc (X.ev a).loc := by simpa [isShared] using hsa
      have hlocC : X.LocalLoc (X.ev c).loc := hcloc ▸ hlocA
      have hcw : Rel.Star X.uniprocRel c w := star_trans hca_up haw
      have hcc : X.po c c = true := po_bridge hca hci hwa (hcloc.trans hwloc.symm) hlocC hcw hwc
      rw [hpirr c hca] at hcc
      exact absurd hcc (by decide)

/-- Corollary in the form with the fencing condition on the write's location only
(`FenceBetweenSharedWR`, which implies `FenceBetweenBothSharedWR`) and `CoKinds`. -/
theorem scConsistentErased_of_tso_of_fenceBetweenSharedWR {n : Nat} (X : Exec n)
    (hptrans : X.PoTrans) (hpth : X.PoWithinThread) (htot : X.PoTotal)
    (hrfl : X.RfSameLoc) (hcok : X.CoKinds)
    (hfence : X.FenceBetweenSharedWR) (hloc : X.PerLocSC) (hghb : X.TsoGhbAcyclic) :
    X.SCConsistentErased :=
  scConsistentErased_of_tso_of_fenceBetweenBothSharedWR X hptrans hpth htot hrfl
    (X.coSameLoc_of_coKinds hcok) (X.fenceBetweenBothSharedWR_of_fenceBetweenSharedWR hfence)
    hloc hghb

/-! ## Fence erasure -/

/-- **Fence erasure.** If `po` is a strict order and `rf`, `co` only relate memory accesses
(writes to reads, writes to writes), then SC-consistency after erasing fence events implies
SC-consistency with the fence events present (fences are inert in the SC relation). -/
theorem scConsistent_of_scConsistentErased {n : Nat} (X : Exec n)
    (hirr : X.PoIrrefl) (htrans : X.PoTrans) (hrfk : X.RfKinds) (hcok : X.CoKinds)
    (h : X.SCConsistentErased) : X.SCConsistent := by
  have hacc_w : ∀ e : Event, e.isWrite = true → e.isAccess = true := by
    intro e he; revert he; simp only [Event.isWrite, Event.isAccess, Event.isFence]
    cases e.kind <;> simp
  have hacc_r : ∀ e : Event, e.isRead = true → e.isAccess = true := by
    intro e he; revert he; simp only [Event.isRead, Event.isAccess, Event.isFence]
    cases e.kind <;> simp
  refine Rel.acyclic_of_acyclic_restrict (p := X.po) (keep := fun a => (X.ev a).isAccess)
    (fun a b hab => by simp [Exec.scRel, hab]) htrans hirr ?_ h
  intro a b hab hfence
  rcases X.scRel_cases hab with h | h | h | h
  · exact h
  · obtain ⟨hw, hr⟩ := hrfk a b h
    rw [hacc_w _ hw, hacc_r _ hr] at hfence; simp at hfence
  · obtain ⟨hw, hw', _⟩ := hcok a b h
    rw [hacc_w _ hw, hacc_w _ hw'] at hfence; simp at hfence
  · obtain ⟨w, hw₁, hw₂⟩ := (X.fr_iff).mp h
    rw [hacc_r _ (hrfk w a hw₁).2, hacc_w _ (hcok w b hw₂).2.1] at hfence; simp at hfence

/-- SC-consistency implies SC-consistency after fence erasure (no hypotheses). -/
theorem scConsistentErased_of_scConsistent {n : Nat} (X : Exec n) (h : X.SCConsistent) :
    X.SCConsistentErased :=
  Rel.Acyclic.mono (fun a b hab => by
    simp only [Exec.eraseFences, Rel.restrict, Bool.and_eq_true] at hab; exact hab.1.1) h

end Toy.WMM
