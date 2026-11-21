import ToyLayoutDfa.RefTools
import ToyLayoutDfa.Lemmas

/-!
# Definition examples

For each core definition: intended positive examples it admits and intended negative
examples it rejects, all fully proved.
-/

namespace Toy.LayoutDfa

open Layout

/-! ### `Accepts` / `Lang` -/

theorem ex_lang_bool : boolL.Lang [Sym.byte 0] ∧ boolL.Lang [Sym.byte 1] ∧
    ¬ boolL.Lang [Sym.byte 2] ∧ ¬ boolL.Lang [Sym.uninit] ∧ ¬ boolL.Lang [] := by
  decide

/-- The accept state is terminal: an edge out of it is never followed. -/
theorem ex_lang_accept_terminal :
    (⟨0, 1, [(0, Sym.byte 0, 1), (1, Sym.byte 0, 1)]⟩ : Layout).Lang [Sym.byte 0] ∧
    ¬ (⟨0, 1, [(0, Sym.byte 0, 1), (1, Sym.byte 0, 1)]⟩ : Layout).Lang
      [Sym.byte 0, Sym.byte 0] := by
  decide

theorem ex_lang_u8 : (∀ b : Fin 256, u8L.Lang [Sym.byte b]) ∧ ¬ u8L.Lang [Sym.uninit] := by
  refine ⟨fun b => byteRef_valid b, by decide +kernel⟩

theorem ex_lang_unit : unitL.Lang [] ∧ ¬ unitL.Lang [Sym.byte 0] := by
  decide

/-! ### `Deterministic` -/

theorem ex_deterministic : boolL.Deterministic ∧ ndSrcL.Deterministic ∧ cycL.Deterministic ∧
    deadL.Deterministic ∧ unitL.Deterministic := by
  decide

theorem ex_not_deterministic : ¬ ndDstL.Deterministic := by
  decide

/-! ### `FixedSize` -/

theorem ex_fixedSize : boolL.FixedSize 1 ∧ unitL.FixedSize 0 ∧ deadL.FixedSize 1 ∧
    ndDstL.FixedSize 2 := by
  refine ⟨fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide) rfl,
    fixedSize_of_rankCert' (rank := fun _ => 0) (by decide) rfl,
    fixedSize_of_rankCert' (rank := fun q => if q = 0 then 1 else 0) (by decide) rfl,
    fixedSize_of_rankCert' (rank := fun q => if q = 0 then 2 else if q = 3 then 0 else 1)
      (by decide) rfl⟩

theorem ex_not_fixedSize : ¬ cycL.FixedSize 2 ∧ ¬ boolL.FixedSize 2 := by
  refine ⟨not_fixedSize_of_lang (w := [Sym.byte 0, Sym.byte 0, Sym.byte 1]) (by decide)
      (by decide),
    not_fixedSize_of_lang (w := [Sym.byte 0]) (by decide) (by decide)⟩

/-! ### `ReachableLive` -/

theorem ex_reachableLive : boolL.ReachableLive ∧ ndDstL.ReachableLive ∧
    unitL.ReachableLive := by
  refine ⟨reachableLive_of_liveCert (rank := fun q => 1 - q) (R := [0, 1]) (by decide),
    reachableLive_of_liveCert (rank := fun q => if q = 0 then 2 else if q = 3 then 0 else 1)
      (R := [0, 1, 2, 3]) (by decide),
    reachableLive_of_liveCert (rank := fun _ => 0) (R := [0]) (by decide)⟩

/-- State 1 of `deadL` is reachable (by byte 0) but accepts no word. -/
theorem deadL_state1_not_live : ∀ v, ¬ deadL.Accepts 1 v := by
  intro v h
  cases v with
  | nil => exact absurd (path_nil_iff.mp h) (by decide)
  | cons a v =>
    obtain ⟨_, q', he, _⟩ := path_cons_iff.mp h
    simp [deadL] at he

theorem ex_not_reachableLive : ¬ deadL.ReachableLive := by
  intro h
  obtain ⟨v, hv⟩ := h [Sym.byte 0] 1 (Path.cons (by decide) (by decide) (Path.nil _))
  exact deadL_state1_not_live v hv

/-- `ReachableLive` includes inhabitation: the uninhabited, edge-free `neverL` (no branch at
all, hence no dead branch) is not `ReachableLive`. -/
theorem neverL_lang_empty (s : List Sym) : ¬ neverL.Lang s := by
  intro h
  cases s with
  | nil => exact absurd (path_nil_iff.mp h) (by decide)
  | cons a w =>
    obtain ⟨_, _, he, _⟩ := path_cons_iff.mp h
    simp [neverL] at he

theorem ex_not_reachableLive_uninhabited : ¬ neverL.ReachableLive := fun h =>
  let ⟨s, hs⟩ := inhabited_of_reachableLive h
  neverL_lang_empty s hs

/-! ### `Acyclic` -/

theorem boolL_acyclic : boolL.Acyclic :=
  acyclic_of_decrCert (rank := fun q => 1 - q) (by decide)
theorem b1L_acyclic : b1L.Acyclic :=
  acyclic_of_decrCert (rank := fun q => 1 - q) (by decide)
theorem ndDstL_acyclic : ndDstL.Acyclic :=
  acyclic_of_decrCert (rank := fun q => if q = 0 then 2 else if q = 3 then 0 else 1) (by decide)
theorem varDstL_acyclic : varDstL.Acyclic :=
  acyclic_of_decrCert (rank := fun q => if q = 0 then 2 else if q = 2 then 0 else 1) (by decide)

/-- The self-loop of `cycL` at state 1 (byte 0) is a non-empty cycle. -/
theorem cycL_not_acyclic : ¬ cycL.Acyclic :=
  fun h => h 1 [Sym.byte 0] (by simp) (Path.cons (by decide) (by decide) (Path.nil _))

theorem ex_acyclic : boolL.Acyclic ∧ varDstL.Acyclic ∧ ¬ cycL.Acyclic :=
  ⟨boolL_acyclic, varDstL_acyclic, cycL_not_acyclic⟩

/-! ### `ReachableLiveAcyclic` -/

/-- State 2 of `deadCycReachL` (reached by byte 1) accepts no word. -/
theorem deadCycReachL_state2_not_live : ∀ v, ¬ deadCycReachL.Accepts 2 v := by
  intro v
  induction v with
  | nil =>
    intro h
    exact absurd (path_nil_iff.mp h) (by decide)
  | cons a w ih =>
    intro h
    obtain ⟨_, q', he, hp⟩ := path_cons_iff.mp h
    simp [deadCycReachL] at he
    obtain ⟨_, rfl⟩ := he
    exact ih hp

theorem deadCycReachL_lang_iff (w : List Sym) : deadCycReachL.Lang w ↔ w = [Sym.byte 0] := by
  constructor
  · intro h
    cases w with
    | nil => exact absurd (path_nil_iff.mp h) (by decide)
    | cons a w' =>
      obtain ⟨_, q1, he, hp⟩ := path_cons_iff.mp h
      simp [deadCycReachL] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hw' : w' = [] := (path_from_accept (A := deadCycReachL) hp).1
        subst hw'
        rfl
      · exact absurd hp (deadCycReachL_state2_not_live w')
  · rintro rfl
    decide

theorem deadCycReachL_fixedSize : deadCycReachL.FixedSize 1 := by
  intro w hw
  rw [(deadCycReachL_lang_iff w).mp hw]
  rfl

/-- The self-loop of `deadCycReachL` at its reachable dead state 2 is a non-empty cycle. -/
theorem deadCycReachL_not_acyclic : ¬ deadCycReachL.Acyclic :=
  fun h => h 2 [Sym.byte 1] (by simp) (Path.cons (by decide) (by decide) (Path.nil _))

/-- The self-loop of `cycL` at state 1 lies in the reachable live part (state 1 is reached by
byte 0 and accepts `[1]`). -/
theorem cycL_not_reachableLiveAcyclic : ¬ cycL.ReachableLiveAcyclic :=
  fun h => h [Sym.byte 0] 1 [Sym.byte 0] [Sym.byte 1] (by simp)
    (Path.cons (by decide) (by decide) (Path.nil _))
    (Path.cons (by decide) (by decide) (Path.nil _))
    (Path.cons (by decide) (by decide) (Path.nil _))

theorem ex_reachableLiveAcyclic :
    varDstL.ReachableLiveAcyclic ∧ deadCycReachL.ReachableLiveAcyclic ∧
      ¬ deadCycReachL.Acyclic ∧ ¬ cycL.ReachableLiveAcyclic :=
  ⟨reachableLiveAcyclic_of_acyclic varDstL_acyclic,
    reachableLiveAcyclic_of_fixedSize deadCycReachL_fixedSize, deadCycReachL_not_acyclic,
    cycL_not_reachableLiveAcyclic⟩

/-! ### `ReachableDeterministic` -/

/-- `b0L` with two extra out-edges of its accept state, both labelled byte 0, to two
different states: not `Deterministic`, but `ReachableDeterministic` (runs never leave the
accept state). -/
def acceptNDL : Layout := ⟨0, 1, [(0, Sym.byte 0, 1), (1, Sym.byte 0, 2), (1, Sym.byte 0, 3)]⟩

theorem acceptNDL_reachableDeterministic : acceptNDL.ReachableDeterministic := by
  intro w q hp hne e₁ he₁ e₂ he₂ hq₁ hq₂ _
  have hq0 : q = 0 := by
    cases w with
    | nil => exact (path_nil_iff.mp hp).symm
    | cons a w' =>
      obtain ⟨_, q1, he, hp1⟩ := path_cons_iff.mp hp
      simp [acceptNDL] at he
      obtain ⟨rfl, rfl⟩ := he
      cases w' with
      | nil => exact absurd (path_nil_iff.mp hp1).symm hne
      | cons _ _ => exact absurd (path_cons_iff.mp hp1).1 (by simp [acceptNDL])
  subst hq0
  simp [acceptNDL] at he₁ he₂
  rcases he₁ with rfl | rfl | rfl <;> simp at hq₁
  rcases he₂ with rfl | rfl | rfl <;> simp at hq₂
  rfl

theorem ndDstL_not_reachableDeterministic : ¬ ndDstL.ReachableDeterministic := by
  intro h
  have := h [] 0 (Path.nil _) (by decide) (0, Sym.byte 0, 1) (by decide) (0, Sym.byte 0, 2)
    (by decide) rfl rfl rfl
  exact absurd this (by decide)

theorem ex_reachableDeterministic :
    boolL.ReachableDeterministic ∧ acceptNDL.ReachableDeterministic ∧
      ¬ acceptNDL.Deterministic ∧ ¬ ndDstL.ReachableDeterministic :=
  ⟨reachableDeterministic_of_deterministic (by decide), acceptNDL_reachableDeterministic,
    by decide, ndDstL_not_reachableDeterministic⟩

/-! ### `fit` -/

theorem ex_fit : fit 2 [Sym.byte 0] = [Sym.byte 0, Sym.uninit] ∧
    fit 1 [Sym.byte 0, Sym.byte 1] = [Sym.byte 0] ∧
    fit 2 [Sym.byte 0, Sym.byte 1] = [Sym.byte 0, Sym.byte 1] ∧
    fit 0 [Sym.byte 0] = [] := by
  decide

/-! ### `forallCheck` and `existsCheck` -/

theorem ex_forallCheck : forallCheck boolL u8L = true ∧ forallCheck u8L u8L = true ∧
    forallCheck u8L u8PadL = true ∧ forallCheck u16L u8L = true := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem ex_not_forallCheck : forallCheck u8L boolL = false ∧ forallCheck u8L u16L = false ∧
    forallCheck boolL b0L = false := by
  refine ⟨by decide +kernel, by decide +kernel, by decide⟩

theorem ex_existsCheck : existsCheck u8L boolL = true ∧ existsCheck boolL b0L = true := by
  refine ⟨by decide +kernel, by decide⟩

theorem ex_not_existsCheck : existsCheck b0L b1L = false ∧ existsCheck u8L u16L = false := by
  refine ⟨by decide, by decide +kernel⟩

/-! ### `Subset`, `Meets`, `FitSubset`, `FitMeets` -/

theorem ex_subset : Subset b0L boolL :=
  forall_lang_of_wordsFrom (n := 1)
    (fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide) rfl) (by decide)

theorem ex_not_subset : ¬ Subset boolL b0L :=
  fun h => absurd (h [Sym.byte 1] (by decide)) (by decide)

theorem ex_meets : Meets boolL b0L := ⟨[Sym.byte 0], by decide, by decide⟩

theorem ex_not_meets : ¬ Meets b0L b1L := by
  rintro ⟨s, hs, hs'⟩
  exact forall_lang_of_wordsFrom (n := 1) (P := fun s => ¬ b1L.Lang s)
    (fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide) rfl) (by decide) s hs hs'

theorem ex_fitSubset : FitSubset b0L b0uL 2 :=
  forall_lang_of_wordsFrom (n := 1) (P := fun s => b0uL.Lang (fit 2 s))
    (fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide) rfl) (by decide)

theorem ex_not_fitSubset : ¬ FitSubset b0L bool2L 2 :=
  fun h => absurd (h [Sym.byte 0] (by decide)) (by decide)

theorem ex_fitMeets : FitMeets boolL b0L 1 := ⟨[Sym.byte 0], by decide, by decide⟩

theorem ex_not_fitMeets : ¬ FitMeets b0L b1L 1 := by
  rintro ⟨s, hs, hs'⟩
  exact forall_lang_of_wordsFrom (n := 1) (P := fun s => ¬ b1L.Lang (fit 1 s))
    (fixedSize_of_rankCert' (rank := fun q => 1 - q) (by decide) rfl) (by decide) s hs hs'

end Toy.LayoutDfa
