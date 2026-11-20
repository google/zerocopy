import ToyGhost.Hoare

/-!
# Result 4: erasability versus noninterference from ghost to real

Treat ghost variables as "high" inputs and real variables as "low" observables.

* `ErasureExact P` is equivalent to the conjunction of termination-sensitive
  ghost-to-real noninterference of `P` (`GhostToRealNI P`) and pointwise agreement
  of `P` with `erase P` (`ErasureAgrees P`). This is a definitional congruence (it
  holds for any program transformation in place of `erase`), and its right-hand
  side still mentions `erase P`. Neither conjunct suffices alone.
* Under R2 the erased program ignores ghost state, so pointwise agreement alone is
  equivalent to exact erasability.
* R1 + R2 (the analogue of a secure-flow typing discipline with ghost = high,
  real = low) give only abort-insensitive noninterference (final real stores of
  normally terminating runs agree); adding R3a and R3b gives the termination- and
  failure-sensitive version.
-/

namespace Toy.Ghost

/-- **4.A** Exact erasability is exactly noninterference plus pointwise agreement.
Definitional: the proof uses neither the semantics nor the definition of `erase`. -/
theorem erasureExact_iff_ghostToRealNI_and_erasureAgrees (P : Stmt) :
    ErasureExact P ↔ GhostToRealNI P ∧ ErasureAgrees P := by
  constructor
  · intro h
    refine ⟨fun σ τ hστ b => ?_, fun σ b => h σ σ rfl b⟩
    exact (h σ τ hστ b).trans (h τ τ rfl b).symm
  · rintro ⟨hNI, hAg⟩ σ τ hστ b
    exact (hNI σ τ hστ b).trans (hAg τ b)

theorem ghostToRealNI_of_erasureExact {P : Stmt} (h : ErasureExact P) : GhostToRealNI P :=
  ((erasureExact_iff_ghostToRealNI_and_erasureAgrees P).1 h).1

/-! ## Facts about the witnesses (fully proved) -/

theorem ghostToRealNI_ceGhostWritesReal : GhostToRealNI ceGhostWritesReal := by
  intro σ τ hστ b
  rw [RBehaves.iff_of_behaves (ceGhostWritesReal_behaves σ),
    RBehaves.iff_of_behaves (ceGhostWritesReal_behaves τ)]
  simp only [Behaviour.real, realPart_update_congr hστ x 1]

/-- The program `x := g`: a real statement reading a ghost variable. -/
def realReadsGhost : Stmt := .assign x (.var g)

theorem erase_realReadsGhost : erase realReadsGhost = realReadsGhost := rfl

theorem erasureAgrees_realReadsGhost : ErasureAgrees realReadsGhost := by
  intro σ b; rw [erase_realReadsGhost]

theorem not_ghostToRealNI_realReadsGhost : ¬ GhostToRealNI realReadsGhost := by
  intro h
  have h1 : Behaves realReadsGhost σ0 (.term (σ0.update x 0)) := ⟨1, rfl⟩
  have h2 : Behaves realReadsGhost σ0g (.term (σ0g.update x 1)) := ⟨1, rfl⟩
  have := (h σ0 σ0g realPart_σ0g.symm _).1 (RBehaves.of_behaves h1)
  rw [RBehaves.iff_of_behaves h2] at this
  have := congrFun (RBehaviour.term.inj this) 0
  simp [realPart, Store.update, x] at this

theorem not_erasureExact_realReadsGhost : ¬ ErasureExact realReadsGhost :=
  fun h => not_ghostToRealNI_realReadsGhost (ghostToRealNI_of_erasureExact h)

/-- **4.B** Noninterference alone does not give exact erasability: `ghost { x := 1 }`
is noninterfering from ghost to real (its real result does not depend on ghost
inputs) but erasure changes its result. -/
theorem ghostToRealNI_not_sufficient_for_erasureExact :
    GhostToRealNI ceGhostWritesReal ∧ ¬ ErasureExact ceGhostWritesReal :=
  ⟨ghostToRealNI_ceGhostWritesReal, erasureExact_needs_ghostWritesGhost.2.2.2⟩

/-- **4.C** Pointwise agreement alone does not give exact erasability: `x := g`
agrees with its erasure (it has no ghost statements) but reads ghost state. -/
theorem erasureAgrees_not_sufficient_for_erasureExact :
    ErasureAgrees realReadsGhost ∧ ¬ ErasureExact realReadsGhost :=
  ⟨erasureAgrees_realReadsGhost, not_erasureExact_realReadsGhost⟩

/-- **4.D** Under R1, R2 and R3a, R3b (per run, from every initial state), `P` is
termination- and failure-sensitively noninterfering from ghost to real. Derived from
the global form of 1.D and 4.A. -/
theorem ghostToRealNI_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P)
    (hT : ∀ σ, GhostNoDivergeFrom P σ) (hF : ∀ σ, GhostNoFailFrom P σ) : GhostToRealNI P :=
  ghostToRealNI_of_erasureExact
    (erasureExact_of_ghostWritesGhost_of_realReadsReal_of_ghostNoDivergeFrom_of_ghostNoFailFrom
      hW hR hT hF)

/-- **4.E** Under R1 and R2 alone, `P` is abort-insensitively noninterfering from ghost
to real: two normally terminating runs from states with the same real part end
with the same real part. Failure and divergence are not compared. Derived from 1.A
and determinism. -/
theorem ghostToRealNI_abortInsensitive_of_ghostWritesGhost_of_realReadsReal
    {P : Stmt} (hW : GhostWritesGhost P) (hR : RealReadsReal P) : GhostToRealNI_AbortInsensitive P := by
  intro σ τ σ' τ' hστ hσ hτ
  obtain ⟨τ1, h1, r1⟩ := refinesUpTo_abortBot_iff.1
    (erase_refinesUpTo_abortBot_of_ghostWritesGhost_of_realReadsReal hW hR hστ) σ' hσ
  obtain ⟨τ2, h2, r2⟩ := refinesUpTo_abortBot_iff.1
    (erase_refinesUpTo_abortBot_of_ghostWritesGhost_of_realReadsReal hW hR rfl) τ' hτ
  cases Behaves.unique h1 h2
  rw [← r1, r2]

/-! ## The termination channel (fully proved) -/

theorem ghostSpinOnG_behaves_σ0 : Behaves ghostSpinOnG σ0 (.term σ0) := ⟨2, rfl⟩

theorem ghostSpinOnG_diverges_σ0g : Diverges ghostSpinOnG σ0g := by
  intro n
  cases n with
  | zero => rfl
  | succ n => exact run_loop_skip_none (by decide) n

theorem ghostWritesGhost_ghostSpinOnG : GhostWritesGhost ghostSpinOnG := trivial
theorem realReadsReal_ghostSpinOnG : RealReadsReal ghostSpinOnG := trivial

theorem ghostBlocksNoFail_ghostSpinOnG : GhostBlocksNoFail ghostSpinOnG :=
  fun _ ⟨_, hn⟩ => run_loop_skip_not_fail hn

/-- **4.F** R1 and R2 do not give termination-sensitive noninterference: the ghost
loop `ghost { while g do skip }` terminates from `σ0` (`g = 0`) and diverges from
`σ0g` (`g = 1`), two states with the same real part; no ghost block of it ever fails,
so only the termination channel is involved. -/
theorem ghostWritesGhost_realReadsReal_not_sufficient_for_ghostToRealNI :
    GhostWritesGhost ghostSpinOnG ∧ RealReadsReal ghostSpinOnG ∧
      realPart σ0 = realPart σ0g ∧ Behaves ghostSpinOnG σ0 (.term σ0) ∧
      Diverges ghostSpinOnG σ0g ∧ (∀ σ, GhostNoFailFrom ghostSpinOnG σ) ∧
      ¬ GhostToRealNI ghostSpinOnG := by
  refine ⟨trivial, trivial, realPart_σ0g.symm, ghostSpinOnG_behaves_σ0, ghostSpinOnG_diverges_σ0g,
    ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ghostSpinOnG, fun h => ?_⟩
  have := (h σ0 σ0g realPart_σ0g.symm _).1 (RBehaves.of_behaves ghostSpinOnG_behaves_σ0)
  rw [RBehaves.iff_of_behaves ghostSpinOnG_diverges_σ0g] at this
  cases this

/-- Positive control for 4.F: the same program is termination-insensitively
noninterfering (proved directly). -/
theorem ghostToRealNI_abortInsensitive_ghostSpinOnG : GhostToRealNI_AbortInsensitive ghostSpinOnG := by
  intro σ τ σ' τ' hστ ⟨n, hn⟩ ⟨m, hm⟩
  cases n with
  | zero => cases hn
  | succ n =>
    cases m with
    | zero => cases hm
    | succ m =>
      rw [run_loop_skip_ok hn, run_loop_skip_ok hm]
      exact hστ

/-! ## Tightness of the hypotheses of 4.D and 4.E (fully proved) -/

/-- `ghost { x := g }`: ghost code copying a ghost value into a real variable. -/
def ceGhostCopiesGhost : Stmt := .ghost (.assign x (.var g))

/-- `ghost { assert g }`: a ghost assertion whose outcome depends on ghost state. -/
def ghostAssertG : Stmt := .ghost (.assert (.var g))

theorem not_ghostToRealNI_ceGhostCopiesGhost : ¬ GhostToRealNI ceGhostCopiesGhost := by
  intro h
  have h1 : Behaves ceGhostCopiesGhost σ0 (.term (σ0.update x 0)) := ⟨2, rfl⟩
  have h2 : Behaves ceGhostCopiesGhost σ0g (.term (σ0g.update x 1)) := ⟨2, rfl⟩
  have := (h σ0 σ0g realPart_σ0g.symm _).1 (RBehaves.of_behaves h1)
  rw [RBehaves.iff_of_behaves h2] at this
  have := congrFun (RBehaviour.term.inj this) 0
  simp [realPart, Store.update, x] at this

theorem not_ghostToRealNI_abortInsensitive_ceGhostCopiesGhost : ¬ GhostToRealNI_AbortInsensitive ceGhostCopiesGhost := by
  intro h
  have := h σ0 σ0g (σ0.update x 0) (σ0g.update x 1) realPart_σ0g.symm ⟨2, rfl⟩ ⟨2, rfl⟩
  have := congrFun this 0
  simp [realPart, Store.update, x] at this

theorem not_ghostToRealNI_ghostAssertG : ¬ GhostToRealNI ghostAssertG := by
  intro h
  have h1 : Behaves ghostAssertG σ0 .fail := ⟨2, rfl⟩
  have h2 : Behaves ghostAssertG σ0g (.term σ0g) := ⟨2, rfl⟩
  have := (h σ0 σ0g realPart_σ0g.symm _).1 (RBehaves.of_behaves h1)
  rw [RBehaves.iff_of_behaves h2] at this
  cases this

theorem ghostToRealNI_needs_ghostWritesGhost :
    RealReadsReal ceGhostCopiesGhost ∧ (∀ σ, GhostNoDivergeFrom ceGhostCopiesGhost σ) ∧
      (∀ σ, GhostNoFailFrom ceGhostCopiesGhost σ) ∧ ¬ GhostToRealNI ceGhostCopiesGhost :=
  ⟨trivial,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := ceGhostCopiesGhost)
      (fun σ => assign_not_diverges _ _ σ),
    ghostNoFailFrom_of_ghostBlocksNoFail (P := ceGhostCopiesGhost) (fun σ => assign_not_fails _ _ σ),
    not_ghostToRealNI_ceGhostCopiesGhost⟩

theorem ghostToRealNI_needs_realReadsReal :
    GhostWritesGhost realReadsGhost ∧ (∀ σ, GhostNoDivergeFrom realReadsGhost σ) ∧
      (∀ σ, GhostNoFailFrom realReadsGhost σ) ∧ ¬ GhostToRealNI realReadsGhost :=
  ⟨trivial, ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := realReadsGhost) trivial,
    ghostNoFailFrom_of_ghostBlocksNoFail (P := realReadsGhost) trivial,
    not_ghostToRealNI_realReadsGhost⟩

theorem ghostToRealNI_needs_ghostNoDivergeFrom :
    GhostWritesGhost ghostSpinOnG ∧ RealReadsReal ghostSpinOnG ∧
      (∀ σ, GhostNoFailFrom ghostSpinOnG σ) ∧ ¬ GhostToRealNI ghostSpinOnG :=
  ⟨trivial, trivial, ghostNoFailFrom_of_ghostBlocksNoFail ghostBlocksNoFail_ghostSpinOnG,
    ghostWritesGhost_realReadsReal_not_sufficient_for_ghostToRealNI.2.2.2.2.2.2⟩

theorem ghostToRealNI_needs_ghostNoFailFrom :
    GhostWritesGhost ghostAssertG ∧ RealReadsReal ghostAssertG ∧
      (∀ σ, GhostNoDivergeFrom ghostAssertG σ) ∧ ¬ GhostToRealNI ghostAssertG :=
  ⟨trivial, trivial,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := ghostAssertG) (fun σ => assert_not_diverges _ σ),
    not_ghostToRealNI_ghostAssertG⟩

theorem ghostToRealNI_abortInsensitive_needs_ghostWritesGhost :
    RealReadsReal ceGhostCopiesGhost ∧ ¬ GhostToRealNI_AbortInsensitive ceGhostCopiesGhost :=
  ⟨trivial, not_ghostToRealNI_abortInsensitive_ceGhostCopiesGhost⟩

theorem ghostToRealNI_abortInsensitive_needs_realReadsReal :
    GhostWritesGhost realReadsGhost ∧ ¬ GhostToRealNI_AbortInsensitive realReadsGhost := by
  refine ⟨trivial, fun h => ?_⟩
  have := h σ0 σ0g (σ0.update x 0) (σ0g.update x 1) realPart_σ0g.symm ⟨1, rfl⟩ ⟨1, rfl⟩
  have := congrFun this 0
  simp [realPart, Store.update, x] at this

/-! ## The failure channel is invisible to abort-insensitive noninterference -/

theorem ghostAssertG_term_eq {σ σ' : Store} (h : Behaves ghostAssertG σ (.term σ')) : σ' = σ := by
  obtain ⟨n, hn⟩ := h
  match n, hn with
  | k + 2, hn =>
    simp only [ghostAssertG, run] at hn
    split at hn
    · cases hn
    · cases hn; rfl

/-- `ghost { assert g }` satisfies R1, R2, R3a everywhere and is abort-insensitively
noninterfering, yet leaks `g` through failure: it is not `GhostToRealNI`. -/
theorem ghostAssertG_abortInsensitive_not_ghostToRealNI :
    GhostWritesGhost ghostAssertG ∧ RealReadsReal ghostAssertG ∧
      (∀ σ, GhostNoDivergeFrom ghostAssertG σ) ∧
      GhostToRealNI_AbortInsensitive ghostAssertG ∧ ¬ GhostToRealNI ghostAssertG :=
  ⟨trivial, trivial,
    ghostNoDivergeFrom_of_ghostBlocksNoDiverge (P := ghostAssertG) (fun σ => assert_not_diverges _ σ),
    fun _ _ _ _ hστ hσ hτ => by rw [ghostAssertG_term_eq hσ, ghostAssertG_term_eq hτ]; exact hστ,
    not_ghostToRealNI_ghostAssertG⟩

/-! ## Under R2, agreement with the erasure is exact erasability -/

/-- **4.G** Under R2, exact erasability is equivalent to pointwise agreement of `P`
with `erase P` from the same full store: the erased program then ignores ghost
state (`erase_rbehaves_congr_of_realReadsReal`). -/
theorem erasureExact_iff_erasureAgrees_of_realReadsReal {P : Stmt} (hR : RealReadsReal P) :
    ErasureExact P ↔ ErasureAgrees P := by
  constructor
  · exact fun h => ((erasureExact_iff_ghostToRealNI_and_erasureAgrees P).1 h).2
  · intro hA σ τ hστ b
    exact (hA σ b).trans (erase_rbehaves_congr_of_realReadsReal hR hστ b)

theorem erasureAgrees_pcGhostWritesGhost : ErasureAgrees pcGhostWritesGhost :=
  ((erasureExact_iff_ghostToRealNI_and_erasureAgrees _).1 pcGhostWritesGhost_erasureExact).2

/-- **Non-vacuity of 4.G** and positive control for 4.C: `ghost { g := 1 }` satisfies
R2 and agrees with its erasure, and it is exactly erasable. -/
theorem pcGhostWritesGhost_realReadsReal_erasureAgrees_erasureExact :
    RealReadsReal pcGhostWritesGhost ∧ ErasureAgrees pcGhostWritesGhost ∧
      ErasureExact pcGhostWritesGhost :=
  ⟨trivial, erasureAgrees_pcGhostWritesGhost, pcGhostWritesGhost_erasureExact⟩

/-- Tightness of R2 in 4.G (canonical form): `x := g` agrees with its erasure, but
is not exactly erasable. -/
theorem erasureExact_iff_erasureAgrees_needs_realReadsReal :
    ErasureAgrees realReadsGhost ∧ ¬ ErasureExact realReadsGhost :=
  erasureAgrees_not_sufficient_for_erasureExact

/-! ## Noninterference without exact erasure under R1 and R2 -/

theorem ghostSpinOnX_behaves_of_x0 {σ : Store} (hx : σ x = 0) :
    Behaves ghostSpinOnX σ (.term σ) := by
  have hx' : σ (.real 0) = 0 := hx
  exact ⟨2, by simp [ghostSpinOnX, run, Expr.eval, x, hx']⟩

theorem ghostSpinOnX_diverges_of_x_ne {σ : Store} (hx : σ x ≠ 0) : Diverges ghostSpinOnX σ := by
  intro n
  cases n with
  | zero => rfl
  | succ n => exact run_loop_skip_none (c := .var x) hx n

/-- `ghost { while x do skip }` satisfies R1 and R2, and its termination depends only
on the real variable `x`, so it is `GhostToRealNI`; yet erasure turns its divergence
from `x = 1` into termination, so it is not exactly erasable. Noninterference from
ghost to real, even together with R1 and R2, does not give exact erasure. -/
theorem ghostSpinOnX_ghostToRealNI_not_erasureExact :
    GhostWritesGhost ghostSpinOnX ∧ RealReadsReal ghostSpinOnX ∧
      GhostToRealNI ghostSpinOnX ∧ ¬ ErasureExact ghostSpinOnX := by
  refine ⟨trivial, trivial, ?_, ?_⟩
  · intro σ τ hστ b
    have hxx : σ x = τ x := congrFun hστ 0
    by_cases hx : σ x = 0
    · rw [RBehaves.iff_of_behaves (ghostSpinOnX_behaves_of_x0 hx),
        RBehaves.iff_of_behaves (ghostSpinOnX_behaves_of_x0 (hxx ▸ hx)), Behaviour.real,
        Behaviour.real, hστ]
    · rw [RBehaves.iff_of_behaves (ghostSpinOnX_diverges_of_x_ne hx),
        RBehaves.iff_of_behaves (ghostSpinOnX_diverges_of_x_ne (hxx ▸ hx))]
  · intro h
    exact not_rbehaves_iff_of_behaves (ghostSpinOnX_diverges_of_x_ne (σ := σ0.update x 1) (by decide))
      (behaves_skip (σ0.update x 1)) (fun e => by cases e) (h _ _ rfl)

end Toy.Ghost
