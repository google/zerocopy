import ToyLayoutDfa.Counterexamples

/-!
# Counterexamples and non-vacuity witnesses for the existential check and size extension

Conventions as in `ToyLayoutDfa.Counterexamples`.
-/

namespace Toy.LayoutDfa

open Layout

/-! ### Soundness of `existsCheck` -/

/-- Dropping `FixedSize B nB`: the destination `()` makes the check succeed at once
(truncation), but `fit 1 [0] = [0]` is not accepted by `()`. -/
theorem existsCheck_sound_needs_fixedSize_dst :
    b0L.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧ existsCheck b0L unitL = true ∧
      ¬ FitMeets b0L unitL 1 := by
  refine ⟨b0L_live, unitL_not_fixedSize_one, by decide, ?_⟩
  rintro ⟨s, hs, hs'⟩
  exact forall_lang_of_wordsFrom (P := fun s => ¬ unitL.Lang (fit 1 s)) b0L_fixedSize
    (by decide) s hs hs'

/-- Dropping `ReachableLive A`: the source's dead branch (byte 0) matches the destination
`{[0]}`, so the check succeeds when the destination reaches its accept state, although the
source language `{[1]}` and `{[0]}` are disjoint. -/
theorem existsCheck_sound_needs_reachableLive :
    b0L.FixedSize 1 ∧ ¬ deadL.ReachableLive ∧ existsCheck deadL b0L = true ∧
      ¬ FitMeets deadL b0L 1 := by
  refine ⟨b0L_fixedSize, ex_not_reachableLive, by decide, ?_⟩
  rintro ⟨s, hs, hs'⟩
  exact forall_lang_of_wordsFrom (P := fun s => ¬ b0L.Lang (fit 1 s)) deadL_fixedSize
    (by decide) s hs hs'

theorem existsCheck_sound_fit_nonvacuous :
    b0L.FixedSize 1 ∧ boolL.ReachableLive ∧ existsCheck boolL b0L = true :=
  ⟨b0L_fixedSize, boolL_live, by decide⟩

theorem neverL_not_reachableLive : ¬ neverL.ReachableLive := ex_not_reachableLive_uninhabited

theorem neverL_fixedSize (n : Nat) : neverL.FixedSize n :=
  fun w hw => absurd hw (neverL_lang_empty w)

/-- Dropping `ReachableLive A` with an uninhabited source that has no edges at all (so no
dead branch): the destination `()` makes the check succeed at once, but no source word
exists. -/
theorem existsCheck_sound_needs_reachableLive_uninhabited :
    unitL.FixedSize 0 ∧ ¬ neverL.ReachableLive ∧ neverL.edges = [] ∧
      existsCheck neverL unitL = true ∧ ¬ FitMeets neverL unitL 0 :=
  ⟨unitL_fixedSize, neverL_not_reachableLive, rfl, by decide,
    fun ⟨s, hs, _⟩ => neverL_lang_empty s hs⟩

/-! ### Soundness of `existsCheck` at some destination size -/

/-- Dropping `ReachableLive A`: the source's dead branch (byte 0) matches `{[0]}`, and no
destination size makes the promise satisfiable. -/
theorem existsCheck_sound_exists_needs_reachableLive :
    ¬ deadL.ReachableLive ∧ existsCheck deadL b0L = true ∧ ¬ ∃ n, FitMeets deadL b0L n := by
  refine ⟨ex_not_reachableLive, by decide, ?_⟩
  rintro ⟨n, s, hs, hb⟩
  have hs' : s = [Sym.byte 1] :=
    forall_lang_of_wordsFrom (P := fun s => s = [Sym.byte 1]) deadL_fixedSize (by decide) s hs
  subst hs'
  have hb' : fit n [Sym.byte 1] = [Sym.byte 0] :=
    forall_lang_of_wordsFrom (P := fun s => s = [Sym.byte 0]) b0L_fixedSize (by decide) _ hb
  have hl := length_fit n [Sym.byte 1]
  rw [hb'] at hl
  simp at hl
  subst hl
  simp [fit] at hb'

/-- Dropping `ReachableLive A` with the uninhabited, edge-free source `neverL`. -/
theorem existsCheck_sound_exists_needs_reachableLive_uninhabited :
    ¬ neverL.ReachableLive ∧ existsCheck neverL unitL = true ∧
      ¬ ∃ n, FitMeets neverL unitL n :=
  ⟨neverL_not_reachableLive, by decide, fun ⟨_, s, hs, _⟩ => neverL_lang_empty s hs⟩

theorem pairSrcL_live : pairSrcL.ReachableLive :=
  reachableLive_of_liveCert (rank := fun q => if q = 0 then 2 else if q = 2 then 0 else 1)
    (R := [0, 1, 2, 3]) (by decide)

/-- All hypotheses hold, including for a destination without a fixed size (`varDstL`). -/
theorem existsCheck_sound_exists_nonvacuous :
    boolL.ReachableLive ∧ existsCheck boolL b0L = true ∧
      pairSrcL.ReachableLive ∧ existsCheck pairSrcL varDstL = true ∧
      (∀ n, ¬ varDstL.FixedSize n) ∧ FitMeets pairSrcL varDstL 1 :=
  ⟨boolL_live, by decide, pairSrcL_live, by decide, varDstL_not_fixedSize,
    [Sym.byte 0, Sym.byte 0], by decide, by decide⟩

/-! ### Completeness of `existsCheck` (no satisfiable promise is rejected) -/

/-- Dropping `FixedSize B nB`: the cyclic destination `0 0* 1` accepts `[0, 0, 0, 0, 1]`,
which is the word of the source, but the check's step budget (`fuelFor cycL = 4`) is
exhausted and it rejects. -/
theorem existsCheck_noPromise_needs_fixedSize_dst :
    ¬ cycL.FixedSize 5 ∧ existsCheck chainL cycL = false ∧
      chainL.Lang [Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 1] ∧
      cycL.Lang (fit 5 [Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 1]) :=
  ⟨cycL_not_fixedSize_five, by decide, by decide, by decide⟩

theorem existsCheck_noPromise_nonvacuous :
    b1L.FixedSize 1 ∧ existsCheck b0L b1L = false :=
  ⟨b1L_fixedSize, by decide⟩

/-! ### Completeness of `existsCheck` without cycles through the reachable live part -/

/-- Dropping `ReachableLiveAcyclic B`: the destination `0 0* 1` accepts the source word
`[0, 0, 0, 0, 1]`, but the step budget is exhausted and the check rejects. -/
theorem existsCheck_noPromise_needs_reachableLiveAcyclic :
    ¬ cycL.ReachableLiveAcyclic ∧ existsCheck chainL cycL = false ∧
      chainL.Lang [Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 1] ∧
      cycL.Lang (fit 5 [Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 0, Sym.byte 1]) :=
  ⟨cycL_not_reachableLiveAcyclic, by decide, by decide, by decide⟩

/-- All hypotheses hold (the antecedent included), also for a destination without a fixed
size (`varDstL`) and for a destination that is not `Acyclic` (`deadCycReachL`). -/
theorem existsCheck_noPromise_acyclic_nonvacuous :
    (b1L.ReachableLiveAcyclic ∧ existsCheck b0L b1L = false) ∧
      (varDstL.ReachableLiveAcyclic ∧ (∀ n, ¬ varDstL.FixedSize n) ∧
        existsCheck b1L varDstL = false) ∧
      (deadCycReachL.ReachableLiveAcyclic ∧ ¬ deadCycReachL.Acyclic ∧
        existsCheck b1L deadCycReachL = false) :=
  ⟨⟨reachableLiveAcyclic_of_acyclic b1L_acyclic, by decide⟩,
    ⟨reachableLiveAcyclic_of_acyclic varDstL_acyclic, varDstL_not_fixedSize, by decide⟩,
    ⟨reachableLiveAcyclic_of_fixedSize deadCycReachL_fixedSize, deadCycReachL_not_acyclic,
      by decide⟩⟩

/-! ### The equal-size characterization -/

theorem existsCheck_iff_meets_needs_fixedSize_src :
    uL.FixedSize 1 ∧ unitL.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
      ¬ (existsCheck unitL uL = true ↔ Meets unitL uL) := by
  refine ⟨uL_fixedSize, unitL_live, unitL_not_fixedSize_one, fun h => ?_⟩
  obtain ⟨s, hs, hs'⟩ := h.mp (by decide)
  have h0 := unitL_fixedSize s hs
  have h1 := uL_fixedSize s hs'
  omega

theorem existsCheck_iff_meets_needs_fixedSize_dst :
    b0L.FixedSize 1 ∧ b0L.ReachableLive ∧ ¬ unitL.FixedSize 1 ∧
      ¬ (existsCheck b0L unitL = true ↔ Meets b0L unitL) := by
  refine ⟨b0L_fixedSize, b0L_live, unitL_not_fixedSize_one, fun h => ?_⟩
  obtain ⟨s, hs, hs'⟩ := h.mp (by decide)
  have h0 := b0L_fixedSize s hs
  have h1 := unitL_fixedSize s hs'
  omega

/-- Dropping `ReachableLive A` with the uninhabited, edge-free source `neverL`. -/
theorem existsCheck_iff_meets_needs_reachableLive_uninhabited :
    neverL.FixedSize 0 ∧ unitL.FixedSize 0 ∧ ¬ neverL.ReachableLive ∧
      ¬ (existsCheck neverL unitL = true ↔ Meets neverL unitL) :=
  ⟨neverL_fixedSize 0, unitL_fixedSize, neverL_not_reachableLive,
    fun h => let ⟨s, hs, _⟩ := h.mp (by decide); neverL_lang_empty s hs⟩

theorem existsCheck_iff_meets_needs_reachableLive :
    deadL.FixedSize 1 ∧ b0L.FixedSize 1 ∧ ¬ deadL.ReachableLive ∧
      ¬ (existsCheck deadL b0L = true ↔ Meets deadL b0L) := by
  refine ⟨deadL_fixedSize, b0L_fixedSize, ex_not_reachableLive, fun h => ?_⟩
  obtain ⟨s, hs, hs'⟩ := h.mp (by decide)
  exact forall_lang_of_wordsFrom (P := fun s => ¬ b0L.Lang s) deadL_fixedSize
    (by decide) s hs hs'

/-- Both truth values occur under all hypotheses: `boolL`/`b0L` (accepted, meeting) and
`b0L`/`b1L` (rejected, disjoint). -/
theorem existsCheck_iff_meets_nonvacuous :
    (boolL.FixedSize 1 ∧ b0L.FixedSize 1 ∧ boolL.ReachableLive ∧
      existsCheck boolL b0L = true ∧ Meets boolL b0L) ∧
    (b0L.FixedSize 1 ∧ b1L.FixedSize 1 ∧ b0L.ReachableLive ∧
      existsCheck b0L b1L = false ∧ ¬ Meets b0L b1L) :=
  ⟨⟨boolL_fixedSize, b0L_fixedSize, boolL_live, by decide, ex_meets⟩,
    ⟨b0L_fixedSize, b1L_fixedSize, b0L_live, by decide, ex_not_meets⟩⟩

/-! ### Size extension -/

/-- Dropping `FixedSize A nA` (with `nA = 0`): the source `{[0]}` has size 1, not 0; the
check accepts it into `{[0, uninit]}`, but `[0] ++ [uninit, uninit]` is not accepted. -/
theorem extension_iff_needs_fixedSize_src :
    b0uL.FixedSize 2 ∧ 0 ≤ 2 ∧ b0uL.Deterministic ∧ b0L.ReachableLive ∧
      ¬ b0L.FixedSize 0 ∧
      ¬ (forallCheck b0L b0uL = true ↔
        ∀ s, b0L.Lang s → b0uL.Lang (s ++ List.replicate (2 - 0) Sym.uninit)) :=
  ⟨b0uL_fixedSize, by decide, by decide, b0L_live, b0L_not_fixedSize_zero,
    fun h => absurd (h.mp (by decide) [Sym.byte 0] (by decide)) (by decide)⟩

/-- Dropping `FixedSize B nB` (with `nB = 2`): the destination `{[0]}` has size 1, not 2;
the check accepts `{[0]}` into it, but `[0, uninit]` is not accepted. -/
theorem extension_iff_needs_fixedSize_dst :
    b0L.FixedSize 1 ∧ 1 ≤ 2 ∧ b0L.Deterministic ∧ b0L.ReachableLive ∧
      ¬ b0L.FixedSize 2 ∧
      ¬ (forallCheck b0L b0L = true ↔
        ∀ s, b0L.Lang s → b0L.Lang (s ++ List.replicate (2 - 1) Sym.uninit)) :=
  ⟨b0L_fixedSize, by decide, by decide, b0L_live, b0L_not_fixedSize_two,
    fun h => absurd (h.mp (by decide) [Sym.byte 0] (by decide)) (by decide)⟩

/-- Dropping `nA ≤ nB`: a source of size 1 and a destination of size 0. The check accepts
by truncation, while the padded form (with truncated subtraction `0 - 1 = 0`) asks for
`[0] ∈ {[]}`. -/
theorem extension_iff_needs_le :
    b0L.FixedSize 1 ∧ unitL.FixedSize 0 ∧ unitL.Deterministic ∧ b0L.ReachableLive ∧
      ¬ (1 ≤ 0) ∧
      ¬ (forallCheck b0L unitL = true ↔
        ∀ s, b0L.Lang s → unitL.Lang (s ++ List.replicate (0 - 1) Sym.uninit)) :=
  ⟨b0L_fixedSize, unitL_fixedSize, by decide, b0L_live, by decide,
    fun h => absurd (h.mp (by decide) [Sym.byte 0] (by decide)) (by decide)⟩

theorem extension_iff_needs_deterministic :
    ndSrcL.FixedSize 2 ∧ ndDstL.FixedSize 2 ∧ 2 ≤ 2 ∧ ndSrcL.ReachableLive ∧
      ¬ ndDstL.Deterministic ∧
      ¬ (forallCheck ndSrcL ndDstL = true ↔
        ∀ s, ndSrcL.Lang s → ndDstL.Lang (s ++ List.replicate (2 - 2) Sym.uninit)) :=
  ⟨ndSrcL_fixedSize, ndDstL_fixedSize, by decide, ndSrcL_live, by decide,
    fun h => absurd (h.mpr (fun s hs => by simpa using ndSrcL_subset_ndDstL s hs))
      (by decide)⟩

theorem extension_iff_needs_reachableLive :
    deadL.FixedSize 1 ∧ b1L.FixedSize 1 ∧ 1 ≤ 1 ∧ b1L.Deterministic ∧
      ¬ deadL.ReachableLive ∧
      ¬ (forallCheck deadL b1L = true ↔
        ∀ s, deadL.Lang s → b1L.Lang (s ++ List.replicate (1 - 1) Sym.uninit)) :=
  ⟨deadL_fixedSize, b1L_fixedSize, by decide, by decide, ex_not_reachableLive,
    fun h => absurd (h.mpr (fun s hs => by simpa using deadL_subset_b1L s hs)) (by decide)⟩

/-- Both truth values occur under all hypotheses: `bool` into `bool`-then-`uninit`
(accepted; every padded string valid) and `bool` into two `bool` bytes (rejected; the
destination's second position requires an initialised byte, so `[0, uninit]` is
invalid). -/
theorem extension_iff_nonvacuous :
    (boolL.FixedSize 1 ∧ boolUL.FixedSize 2 ∧ 1 ≤ 2 ∧ boolUL.Deterministic ∧
      boolL.ReachableLive ∧ forallCheck boolL boolUL = true ∧
      ∀ s, boolL.Lang s → boolUL.Lang (s ++ List.replicate (2 - 1) Sym.uninit)) ∧
    (boolL.FixedSize 1 ∧ bool2L.FixedSize 2 ∧ 1 ≤ 2 ∧ bool2L.Deterministic ∧
      boolL.ReachableLive ∧ forallCheck boolL bool2L = false ∧
      ¬ bool2L.Lang ([Sym.byte 0] ++ List.replicate (2 - 1) Sym.uninit)) :=
  ⟨⟨boolL_fixedSize, boolUL_fixedSize, by decide, by decide, boolL_live, by decide,
      forall_lang_of_wordsFrom
        (P := fun s => boolUL.Lang (s ++ List.replicate (2 - 1) Sym.uninit))
        boolL_fixedSize (by decide)⟩,
    ⟨boolL_fixedSize, bool2L_fixedSize, by decide, by decide, boolL_live, by decide,
      by decide⟩⟩

/-- Size extension on full-width fixtures: `u8` into `u16` is rejected, because the second byte of
`u16` must be initialised and `fit 2 [0] = [0, uninit]` is not a valid `u16`; `u8` into a
two-byte type whose second byte is padding is accepted, and every padded string is valid
there. -/
theorem u8PadL_lang_byte_uninit (b : Fin 256) : u8PadL.Lang [Sym.byte b, Sym.uninit] := by
  show u8PadL.Path 0 [Sym.byte b, Sym.uninit] 2
  refine Path.cons (q' := 1) (by decide) ?_
    (Path.cons (q' := 2) (by decide) (by decide +kernel) (Path.nil _))
  simp [u8PadL, byteEdges, List.mem_map, List.mem_finRange]

theorem extension_u8_to_u16_rejected_u8_to_u8Pad_accepted :
    u8L.FixedSize 1 ∧ u16L.FixedSize 2 ∧ u8PadL.FixedSize 2 ∧
      forallCheck u8L u16L = false ∧ ¬ u16L.Lang (fit 2 [Sym.byte 0]) ∧
      forallCheck u8L u8PadL = true ∧
      (∀ b : Fin 256, u8PadL.Lang [Sym.byte b, Sym.uninit]) := by
  exact ⟨u8L_fixedSize, u16L_fixedSize, u8PadL_fixedSize, by decide +kernel,
    by decide +kernel, by decide +kernel, u8PadL_lang_byte_uninit⟩

/-- `u8L` accepts exactly the one-byte words of initialised bytes. -/
theorem u8L_lang_iff (s : List Sym) : u8L.Lang s ↔ ∃ b : Fin 256, s = [Sym.byte b] := by
  constructor
  · intro h
    cases s with
    | nil => exact absurd (path_nil_iff.mp h) (by decide)
    | cons a s' =>
      obtain ⟨_, q', he, hp⟩ := path_cons_iff.mp h
      have hab : ∃ b : Fin 256, a = Sym.byte b ∧ q' = 1 := by
        simp only [u8L, byteEdges, List.mem_map] at he
        obtain ⟨b, _, hb⟩ := he
        simp only [Prod.mk.injEq] at hb
        exact ⟨b, hb.2.1.symm, hb.2.2.symm⟩
      obtain ⟨b, rfl, rfl⟩ := hab
      have hs' : s' = [] := (path_from_accept (A := u8L) hp).1
      subst hs'
      exact ⟨b, rfl⟩
  · rintro ⟨b, rfl⟩
    exact byteRef_valid b

theorem u8L_live : u8L.ReachableLive :=
  reachableLive_of_liveCert (rank := fun q => 1 - q) (R := [0, 1]) (by decide +kernel)

theorem u8PadL_deterministic : u8PadL.Deterministic := by
  intro e₁ h₁ e₂ h₂ hs _
  simp only [u8PadL, byteEdges, anyEdges, List.mem_append, List.mem_map] at h₁ h₂
  rcases h₁ with ⟨b, _, rfl⟩ | ⟨b, _, rfl⟩ <;> rcases h₂ with ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ <;>
    simp_all

theorem u16L_deterministic : u16L.Deterministic := by
  intro e₁ h₁ e₂ h₂ hs _
  simp only [u16L, byteEdges, List.mem_append, List.mem_map] at h₁ h₂
  rcases h₁ with ⟨b, _, rfl⟩ | ⟨b, _, rfl⟩ <;> rcases h₂ with ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩ <;>
    simp_all

/-- Both truth values occur under all hypotheses on initialisation-monotone, full-width
fixtures: `u8` into a two-byte type whose second byte is padding (accepted; every padded
string valid) and `u8` into `u16` (rejected; `[0, uninit]` is not a valid `u16`). -/
theorem extension_iff_nonvacuous_fullWidth :
    (u8L.FixedSize 1 ∧ u8PadL.FixedSize 2 ∧ 1 ≤ 2 ∧ u8PadL.Deterministic ∧
      u8L.ReachableLive ∧ forallCheck u8L u8PadL = true ∧
      ∀ s, u8L.Lang s → u8PadL.Lang (s ++ List.replicate (2 - 1) Sym.uninit)) ∧
    (u8L.FixedSize 1 ∧ u16L.FixedSize 2 ∧ 1 ≤ 2 ∧ u16L.Deterministic ∧
      u8L.ReachableLive ∧ forallCheck u8L u16L = false ∧
      ¬ u16L.Lang ([Sym.byte 0] ++ List.replicate (2 - 1) Sym.uninit)) := by
  refine ⟨⟨u8L_fixedSize, u8PadL_fixedSize, by decide, u8PadL_deterministic, u8L_live,
      by decide +kernel, fun s hs => ?_⟩,
    ⟨u8L_fixedSize, u16L_fixedSize, by decide, u16L_deterministic, u8L_live,
      by decide +kernel, by decide +kernel⟩⟩
  obtain ⟨b, rfl⟩ := (u8L_lang_iff s).mp hs
  exact u8PadL_lang_byte_uninit b

end Toy.LayoutDfa
