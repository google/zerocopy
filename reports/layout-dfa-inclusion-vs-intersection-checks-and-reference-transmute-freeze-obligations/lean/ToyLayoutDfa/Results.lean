import ToyLayoutDfa.Lemmas
import ToyLayoutDfa.Refs
import ToyLayoutDfa.RefTools

/-!
# Main results

The universal check, the existential check and size extension: which language relations
`forallCheck` and `existsCheck` decide, and under which hypotheses. The reference
obligation matrix in the toy reference model of `ToyLayoutDfa.Refs`, and the Boolean
reference checker `refCheck` built from `forallCheck`.
-/

namespace Toy.LayoutDfa

open Layout

/-! ## The universal check -/

/-- Soundness of the universal check, for every source automaton (deterministic or not,
with or without dead branches, inhabited or not) and every destination automaton of fixed
size `nB`. -/
theorem forallCheck_sound_fit_of_fixedSize {A B : Layout} {nB : Nat} (hB : B.FixedSize nB) :
    forallCheck A B = true → FitSubset A B nB := by
  intro h s hs
  obtain ⟨k, hk⟩ := forallAux_sound _ _ _ h s hs
  have hlen : (fit k s).length = nB := hB _ hk
  rw [length_fit] at hlen
  subst hlen
  exact hk


/-- Completeness of the universal check for a deterministic destination without non-empty
cycles through its reachable live part (of any word lengths; cycles through unreachable or
dead states allowed) and a `ReachableLive` source, at every destination size `nB`. -/
theorem forallCheck_complete_fit_of_reachableLiveAcyclic_det_live {A B : Layout} {nB : Nat}
    (hno : B.ReachableLiveAcyclic) (hdet : B.Deterministic) (hlive : A.ReachableLive) :
    FitSubset A B nB → forallCheck A B = true := by
  intro hfit
  obtain ⟨s0, hs0⟩ := inhabited_of_reachableLive hlive
  have hle := length_le_edges_of_reachableLiveAcyclic hno (hfit s0 hs0)
  rw [length_fit] at hle
  exact forallAux_complete_fit_of_lt_fuel (by simp only [fuelFor]; omega)
    (reachableDeterministic_of_deterministic hdet) hlive hfit

/-- Completeness of the universal check for a deterministic destination of fixed size `nB`
and a `ReachableLive` source (every reachable source state, the start state included, can
reach the accept state). A corollary of the `ReachableLiveAcyclic` form. -/
theorem forallCheck_complete_fit_of_fixedSize_det_live {A B : Layout} {nB : Nat}
    (hB : B.FixedSize nB) (hdet : B.Deterministic) (hlive : A.ReachableLive) :
    FitSubset A B nB → forallCheck A B = true :=
  forallCheck_complete_fit_of_reachableLiveAcyclic_det_live
    (reachableLiveAcyclic_of_fixedSize hB) hdet hlive

/-- The global-acyclicity form (every state, reachable or not, live or dead), a corollary. -/
theorem forallCheck_complete_fit_of_acyclic_det_live {A B : Layout} {nB : Nat}
    (hacyc : B.Acyclic) (hdet : B.Deterministic) (hlive : A.ReachableLive) :
    FitSubset A B nB → forallCheck A B = true :=
  forallCheck_complete_fit_of_reachableLiveAcyclic_det_live
    (reachableLiveAcyclic_of_acyclic hacyc) hdet hlive

/-- For equal fixed sizes, a deterministic destination and a `ReachableLive` source, the
universal check decides language inclusion. -/
theorem forallCheck_eq_true_iff_subset_of_eq_fixedSize_det_live {A B : Layout} {n : Nat}
    (hA : A.FixedSize n) (hB : B.FixedSize n) (hdet : B.Deterministic)
    (hlive : A.ReachableLive) :
    forallCheck A B = true ↔ Subset A B := by
  constructor
  · intro h s hs
    have := forallCheck_sound_fit_of_fixedSize hB h s hs
    rwa [fit_of_length_eq (hA s hs)] at this
  · intro h
    apply forallCheck_complete_fit_of_fixedSize_det_live hB hdet hlive
    intro s hs
    rw [fit_of_length_eq (hA s hs)]
    exact h s hs

/-! ## The existential check -/

/-- Soundness of the existential check without any destination hypothesis: for a
`ReachableLive` source, acceptance implies that the validity promise is satisfiable at
some destination size. -/
theorem existsCheck_sound_exists_fitMeets_of_live {A B : Layout} (hlive : A.ReachableLive) :
    existsCheck A B = true → ∃ nB, FitMeets A B nB := by
  intro h
  obtain ⟨v, k, hv, hk⟩ := existsAux_sound hlive _ _ _ [] (Path.nil _) h
  exact ⟨k, v, hv, hk⟩

/-- Soundness of the existential check at the destination's fixed size `nB`, for a
`ReachableLive` source (the destination may be nondeterministic); the fixed-size corollary
of `existsCheck_sound_exists_fitMeets_of_live`. -/
theorem existsCheck_sound_fit_of_fixedSize_live {A B : Layout} {nB : Nat}
    (hB : B.FixedSize nB) (hlive : A.ReachableLive) :
    existsCheck A B = true → FitMeets A B nB := by
  intro h
  obtain ⟨k, v, hv, hk⟩ := existsCheck_sound_exists_fitMeets_of_live hlive h
  have hlen : (fit k v).length = nB := hB _ hk
  rw [length_fit] at hlen
  subst hlen
  exact ⟨v, hv, hk⟩

/-- The same completeness statement for a destination without non-empty cycles through its
reachable live part (of any word lengths; cycles through unreachable or dead states
allowed), at every destination size `nB`. -/
theorem existsCheck_eq_false_imp_no_promise_of_reachableLiveAcyclic {A B : Layout} {nB : Nat}
    (hno : B.ReachableLiveAcyclic) :
    existsCheck A B = false → ∀ s, A.Lang s → ¬ B.Lang (fit nB s) := by
  intro hf s hs hbs
  have hle := length_le_edges_of_reachableLiveAcyclic hno hbs
  rw [length_fit] at hle
  have ht : existsCheck A B = true :=
    existsAux_of_accepts_fit hs hbs (by simp only [fuelFor]; omega)
  rw [hf] at ht
  exact Bool.false_ne_true ht

/-- Completeness of the existential check, stated as: when the check rejects, no valid
source string satisfies the validity promise at the destination's fixed size `nB`. For
every source automaton and every destination automaton of fixed size `nB`; a corollary of
the `ReachableLiveAcyclic` form. -/
theorem existsCheck_eq_false_imp_no_promise_of_fixedSize {A B : Layout} {nB : Nat}
    (hB : B.FixedSize nB) :
    existsCheck A B = false → ∀ s, A.Lang s → ¬ B.Lang (fit nB s) :=
  existsCheck_eq_false_imp_no_promise_of_reachableLiveAcyclic (reachableLiveAcyclic_of_fixedSize hB)

/-- The global-acyclicity form (every state, reachable or not, live or dead), a corollary. -/
theorem existsCheck_eq_false_imp_no_promise_of_acyclic {A B : Layout} {nB : Nat}
    (hacyc : B.Acyclic) :
    existsCheck A B = false → ∀ s, A.Lang s → ¬ B.Lang (fit nB s) :=
  existsCheck_eq_false_imp_no_promise_of_reachableLiveAcyclic (reachableLiveAcyclic_of_acyclic hacyc)

/-- For equal fixed sizes and a `ReachableLive` source, the existential check decides
non-empty intersection (the destination may be nondeterministic). -/
theorem existsCheck_eq_true_iff_meets_of_eq_fixedSize_live {A B : Layout} {n : Nat}
    (hA : A.FixedSize n) (hB : B.FixedSize n) (hlive : A.ReachableLive) :
    existsCheck A B = true ↔ Meets A B := by
  constructor
  · intro h
    obtain ⟨s, hs, hbs⟩ := existsCheck_sound_fit_of_fixedSize_live hB hlive h
    exact ⟨s, hs, by rwa [fit_of_length_eq (hA s hs)] at hbs⟩
  · rintro ⟨s, hs, hbs⟩
    cases hc : existsCheck A B with
    | true => rfl
    | false =>
      have hbs' : B.Lang (fit n s) := by rw [fit_of_length_eq (hA s hs)]; exact hbs
      exact absurd hbs' (existsCheck_eq_false_imp_no_promise_of_fixedSize hB hc s hs)

/-! ## Size extension -/

/-- For a source of fixed size `nA` at most the destination's fixed size `nB`, a
deterministic destination and a `ReachableLive` source, the universal check accepts iff the
destination accepts every valid source string followed by exactly `nB - nA` `uninit`
symbols (truncated subtraction; `nA ≤ nB` is assumed). -/
theorem forallCheck_eq_true_iff_uninit_padded_of_fixedSize_le_det_live {A B : Layout}
    {nA nB : Nat} (hA : A.FixedSize nA) (hB : B.FixedSize nB) (hle : nA ≤ nB)
    (hdet : B.Deterministic) (hlive : A.ReachableLive) :
    forallCheck A B = true ↔
      ∀ s, A.Lang s → B.Lang (s ++ List.replicate (nB - nA) Sym.uninit) := by
  have hfit : ∀ s, A.Lang s → fit nB s = s ++ List.replicate (nB - nA) Sym.uninit := by
    intro s hs
    rw [fit_of_length_le (by rw [hA s hs]; exact hle), hA s hs]
  constructor
  · intro h s hs
    rw [← hfit s hs]
    exact forallCheck_sound_fit_of_fixedSize hB h s hs
  · intro h
    apply forallCheck_complete_fit_of_fixedSize_det_live hB hdet hlive
    intro s hs
    rw [hfit s hs]
    exact h s hs

/-! ## The reference obligation matrix -/

/-- `& S → & D`, exactly: for a satisfiable source referent. -/
theorem sharedShared_sound_iff {S D : RefTy} (hS : Satisfiable S) :
    Sound .shared .shared S D ↔
      Includes S D ∧ S.freeze = D.freeze ∧ (D.freeze = false → Includes D S) := by
  refine ⟨fun h => ?_, fun ⟨hinc, hfz, hrev⟩ => sound_shared_shared_of hinc hfz hrev⟩
  rw [sound_iff_soundOneStep] at h
  obtain ⟨m0, hm0⟩ := hS
  have hinc : Includes S D := fun m hm => (h m hm (.read .dst) trivial).1.1
  refine ⟨hinc, ?_, fun hd b hb => (h m0 hm0 (.write .dst b) ⟨Or.inr hd, hb⟩).2⟩
  cases hs : S.freeze <;> cases hd : D.freeze
  · rfl
  · exact absurd (Or.inr ⟨rfl, hd⟩) (h m0 hm0 (.write .src m0) ⟨rfl, hs, hm0⟩).1.1
  · exact absurd (Or.inl ⟨rfl, hs⟩) (h m0 hm0 (.write .dst m0) ⟨Or.inr hd, hinc m0 hm0⟩).1.1
  · rfl

/-- `&mut S → & D`, exactly: for a satisfiable source referent. `S.freeze` does not occur. -/
theorem mutShared_sound_iff {S D : RefTy} (hS : Satisfiable S) :
    Sound .mutable .shared S D ↔ Includes S D ∧ (D.freeze = false → Includes D S) := by
  refine ⟨fun h => ?_, fun ⟨hinc, hrev⟩ => sound_mutable_shared_of hinc hrev⟩
  rw [sound_iff_soundOneStep] at h
  obtain ⟨m0, hm0⟩ := hS
  exact ⟨fun m hm => (h m hm (.read .dst) trivial).1.1,
    fun hd b hb => (h m0 hm0 (.write .dst b) ⟨Or.inr hd, hb⟩).2⟩

/-- `&mut S → &mut D`, exactly: for a satisfiable source referent. No `freeze` flag occurs. -/
theorem mutMut_sound_iff {S D : RefTy} (hS : Satisfiable S) :
    Sound .mutable .mutable S D ↔ Includes S D ∧ Includes D S := by
  refine ⟨fun h => ?_, fun ⟨hinc, hrev⟩ => sound_mutable_mutable_of hinc hrev⟩
  rw [sound_iff_soundOneStep] at h
  obtain ⟨m0, hm0⟩ := hS
  exact ⟨fun m hm => (h m hm (.read .dst) trivial).1.1,
    fun b hb => (h m0 hm0 (.write .dst b) ⟨Or.inl rfl, hb⟩).2⟩

/-- `& S → &mut D` is never sound for a satisfiable source referent. -/
theorem sharedMut_not_sound {S D : RefTy} (hS : Satisfiable S) :
    ¬ Sound .shared .mutable S D := by
  obtain ⟨m0, hm0⟩ := hS
  intro h
  have := h m0 hm0 [.read .src]
    (by
      intro op hop
      simp only [List.mem_singleton] at hop
      subst hop
      rfl)
  exact this.1.2 ⟨rfl, rfl⟩

/-- The obligation matrix is sound in every cell: universally quantified over both modes and
both referent types, with no side hypothesis beyond the antecedent `MatrixOK ms md S D`
(neither `Satisfiable S` nor `D.freeze = true` is assumed). -/
theorem sound_of_matrixOK {ms md : Mode} {S D : RefTy} :
    MatrixOK ms md S D → Sound ms md S D := by
  intro hM
  cases ms <;> cases md
  · obtain ⟨hinc, hd, hs⟩ := hM
    exact sound_shared_shared_of hinc (hs.trans hd.symm)
      (fun h => absurd (hd.symm.trans h) (by decide))
  · exact absurd hM id
  · obtain ⟨hinc, hd⟩ := hM
    exact sound_mutable_shared_of hinc (fun h => absurd (hd.symm.trans h) (by decide))
  · exact sound_mutable_mutable_of hM.1 hM.2

/-- The obligation matrix is exact for a satisfiable source referent, whenever a shared
destination referent is `Freeze`. -/
theorem matrixOK_iff_sound_of_sharedDst_freeze {ms md : Mode} {S D : RefTy}
    (hS : Satisfiable S) (hD : md = .shared → D.freeze = true) :
    MatrixOK ms md S D ↔ Sound ms md S D := by
  refine ⟨sound_of_matrixOK, fun h => ?_⟩
  cases ms <;> cases md
  · obtain ⟨hinc, hfz, _⟩ := (sharedShared_sound_iff hS).mp h
    have hd := hD rfl
    exact ⟨hinc, hd, hfz.trans hd⟩
  · exact sharedMut_not_sound hS h
  · exact ⟨((mutShared_sound_iff hS).mp h).1, hD rfl⟩
  · exact (mutMut_sound_iff hS).mp h

/-- `forallCheck` between layouts of one common fixed size `n` implies language inclusion
(no determinism or liveness assumption). -/
theorem subset_of_forallCheck_of_eq_fixedSize {A B : Layout} {n : Nat}
    (hA : A.FixedSize n) (hB : B.FixedSize n) (h : forallCheck A B = true) : Subset A B := by
  intro s hs
  have := forallCheck_sound_fit_of_fixedSize hB h s hs
  rwa [fit_of_length_eq (hA s hs)] at this

/-- The Boolean reference checker `refCheck` is sound for referent layouts of one common
fixed size `n` (deterministic or not, with or without dead branches), for every mode pair
and every pair of caller-supplied `Freeze` flags. -/
theorem refCheck_sound_of_eq_fixedSize {ms md : Mode} {S D : Layout} {fzS fzD : Bool} {n : Nat}
    (hS : S.FixedSize n) (hD : D.FixedSize n) :
    refCheck ms md S fzS D fzD = true →
      Sound ms md (RefTy.ofLayout S fzS) (RefTy.ofLayout D fzD) := by
  intro h
  apply sound_of_matrixOK
  cases ms <;> cases md
  · simp only [refCheck, Bool.and_eq_true] at h
    obtain ⟨⟨hc, hd⟩, hs⟩ := h
    exact ⟨subset_of_forallCheck_of_eq_fixedSize hS hD hc, hd, hs⟩
  · simp [refCheck] at h
  · simp only [refCheck, Bool.and_eq_true] at h
    obtain ⟨hc, hd⟩ := h
    exact ⟨subset_of_forallCheck_of_eq_fixedSize hS hD hc, hd⟩
  · simp only [refCheck, Bool.and_eq_true] at h
    obtain ⟨hc, hc'⟩ := h
    exact ⟨subset_of_forallCheck_of_eq_fixedSize hS hD hc,
      subset_of_forallCheck_of_eq_fixedSize hD hS hc'⟩

end Toy.LayoutDfa
