import ToyBackward.Programs
import ToyBackward.SimProph

/-!
# Results

Main statements, and fully proved counterexamples, non-vacuity witnesses, and positive controls.

Every statement is fully proved. The simulation arguments behind `endpoint-window-last-write`,
`lock-complete`, `lock-success-in-window`, `prophecy-agreement`, and `prophecy-sound-wider-window`
are in `ToyBackward/Simulation.lean`, `ToyBackward/SimLock.lean`, and `ToyBackward/SimProph.lean`;
`endpoint-window`, `sound-lazy`, `sound-eager` (from `endpoint-window-last-write`) and `lock-sound`
(from `lock-complete` and `lock-success-in-window`) are short derivations. `pure-backward-unsound`,
`stateless-unsound`, and `aliasing-iff-placement` are proved directly. Every counterexample is stated in canonical form: a
concrete instance satisfies all the *other* hypotheses of the named result and its conclusion
fails.

Naming: `<result>_tight_<hypothesis>` is the counterexample showing that `<hypothesis>` cannot be
dropped from `<result>`; `<result>_nonvacuous` exhibits an instance of all hypotheses;
`<result>_positive_control` is a nearby setting where an impossibility's conclusion fails.
-/

namespace Toy.Backward

theorem ne_of_map_ne {α β : Type} {f : α → β} {a b : Option α} (h : a.map f ≠ b.map f) : a ≠ b :=
  fun e => h (e ▸ rfl)

theorem not_forall_iff_of_left {α : Type} {A B : α → Prop} (o : α) (ha : A o) (hb : ¬ B o) :
    ¬ ∀ o, A o ↔ B o :=
  fun h => hb ((h o).1 ha)

theorem upd_upd_same {α : Type} (f : Nat → α) (k : Nat) (a b : α) :
    upd (upd f k a) k b = upd f k b := by
  funext q
  simp only [upd]
  split <;> rfl

/-! ## `endpoint-window-last-write` — the unchecked write-back translation on the generalized window -/

/-- **`endpoint-window-last-write` (main, generalized end-point window).** If every region ends
after its creation and after its last *write*, no later than the owner's next access to its cell,
and no later than the program end, and the program obeys the aliasing discipline, then the
effectful-backward translation produces exactly the heap semantics' outcome (both succeed with
the same final heap and variables, or both are stuck). -/
theorem effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastWrite_of_endsByNextOwnerAccess_of_endsByProgramEnd_of_aliasingDiscipline
    (P : Prog) (π : Placement) (h : Heap)
    (hc : EndsAfterCreation P π) (hw : EndsAfterLastWrite P π) (ho : EndsByNextOwnerAccess P π)
    (he : EndsByProgramEnd P π) (had : AliasingDiscipline P) :
    effSem P π h = heapSem P h :=
  Sim.effSem_eq_heapSem P π h hc hw ho he had

/-! ## `endpoint-window` — end-point independence for liveness-respecting placements -/

/-- **`endpoint-window` (end-point independence).** For every placement that ends each region
after its creation and after its last use, no later than the owner's next access, and no later
than the program end, the effectful-backward translation produces exactly the heap semantics'
outcome (both succeed with the same final heap and variables, or both are stuck). The aliasing
discipline is not a hypothesis: it follows, see
`aliasingDiscipline_of_endsAfterLastUse_of_endsByNextOwnerAccess`. -/
theorem effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd
    (P : Prog) (π : Placement) (h : Heap)
    (hc : EndsAfterCreation P π) (hu : EndsAfterLastUse P π) (ho : EndsByNextOwnerAccess P π)
    (he : EndsByProgramEnd P π) :
    effSem P π h = heapSem P h :=
  effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastWrite_of_endsByNextOwnerAccess_of_endsByProgramEnd_of_aliasingDiscipline
    P π h hc (endsAfterLastWrite_of_endsAfterLastUse hu) ho he
    (aliasingDiscipline_of_endsAfterLastUse_of_endsByNextOwnerAccess hu ho)

/-- Convenience corollary of `endpoint-window` (no separate card): any two liveness-respecting
placements give the effectful translation the same outcome, because both give the heap semantics'
outcome. -/
theorem effSem_eq_effSem_of_respectsLiveness (P : Prog) (π₁ π₂ : Placement) (h : Heap)
    (h₁ : RespectsLiveness P π₁) (h₂ : RespectsLiveness P π₂) :
    effSem P π₁ h = effSem P π₂ h := by
  rw [effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd
      P π₁ h h₁.1 h₁.2.1 h₁.2.2.1 h₁.2.2.2,
    effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd
      P π₂ h h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2]

/-! ## `sound-lazy`, `sound-eager` — the two canonical placements -/

/-- **`sound-lazy` (lazy region ends).** For every program obeying the aliasing discipline and
every initial heap, the effectful-backward translation that ends each region at the owner's next
access (or at the program end) produces exactly the heap semantics' outcome (both succeed with
the same final heap and variables, or both are stuck). -/
theorem effSem_lazyPlacement_eq_heapSem_of_aliasingDiscipline (P : Prog) (h : Heap)
    (had : AliasingDiscipline P) :
    effSem P (lazyPlacement P) h = heapSem P h :=
  effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd
    P _ h (lazyPlacement_endsAfterCreation P) (lazyPlacement_endsAfterLastUse_of_aliasingDiscipline had)
    (lazyPlacement_endsByNextOwnerAccess P) (lazyPlacement_endsByProgramEnd P)

/-- **`sound-eager` (eager region ends).** Same, with each region ended immediately after the later
of its creation and its last use (`eagerPlacement`). -/
theorem effSem_eagerPlacement_eq_heapSem_of_aliasingDiscipline (P : Prog) (h : Heap)
    (had : AliasingDiscipline P) :
    effSem P (eagerPlacement P) h = heapSem P h :=
  effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd
    P _ h (eagerPlacement_endsAfterCreation P) (eagerPlacement_endsAfterLastUse P)
    (eagerPlacement_endsByNextOwnerAccess_of_aliasingDiscipline had) (eagerPlacement_endsByProgramEnd P)

/-! ## `lock-complete`, `lock-success-in-window`, `lock-sound` — the borrow-locking translation -/

/-- **`lock-complete` (borrow-locking translation, complete on the window).** For every placement
that ends each region after its creation and after its last use, no later than the owner's next
access, and no later than the program end, the borrow-locking translation produces exactly the
heap semantics' outcome (both succeed with the same final heap and variables, or both are
stuck). -/
theorem lockSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd
    (P : Prog) (π : Placement) (h : Heap)
    (hc : EndsAfterCreation P π) (hu : EndsAfterLastUse P π) (ho : EndsByNextOwnerAccess P π)
    (he : EndsByProgramEnd P π) :
    lockSem P π h = heapSem P h := by
  rw [Sim.lockSem_eq_effSem P π h hc hu ho he]
  exact effSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd
    P π h hc hu ho he

/-- **`lock-success-in-window` (borrow-locking translation succeeds only on the window).** For every
program, placement, and initial heap: if the borrow-locking translation succeeds, the placement is
liveness-respecting (every region ends after its creation and after its last use, no later than
the owner's next access, and no later than the program end). -/
theorem respectsLiveness_of_lockSem_eq_some (P : Prog) (π : Placement) (h : Heap) (o : Obs)
    (hl : lockSem P π h = some o) :
    RespectsLiveness P π :=
  Sim.respectsLiveness_of_lockSem P π h o hl

/-- **`lock-sound` (borrow-locking translation: every placement is sound).** For every program,
every placement of region ends (inside or outside the window), and every initial heap: if the
borrow-locking translation succeeds with observation `o`, the heap semantics succeeds with the same
`o`. A placement can make the translation stuck, never wrong. -/
theorem heapSem_eq_some_of_lockSem_eq_some (P : Prog) (π : Placement) (h : Heap) (o : Obs)
    (hl : lockSem P π h = some o) :
    heapSem P h = some o := by
  obtain ⟨hc, hu, ho, he⟩ := respectsLiveness_of_lockSem_eq_some P π h o hl
  rw [← lockSem_eq_heapSem_of_endsAfterCreation_of_endsAfterLastUse_of_endsByNextOwnerAccess_of_endsByProgramEnd
    P π h hc hu ho he]
  exact hl

/-! ## `pure-backward-unsound` — pure backward functions are unsound -/

/-- **`pure-backward-unsound` (pure backward functions are unsound).** On the program
`reborrowAfterWrite c`, which obeys the aliasing discipline, and any initial heap `h` with
`c ≠ h 0`: the pure-backward translation succeeds with final heap exactly `h` and binds the second
reborrow's read `x1` to the stale `h 0`; the heap semantics succeeds with final heap `h[0 ↦ c]` and
`x1 = c`; so the two outcomes differ both in the final heap and in a local variable. -/
theorem pureBackSem_unsound_on_reborrowAfterWrite (h : Heap) (c : Int) (hc : c ≠ h 0) :
    AliasingDiscipline (reborrowAfterWrite c) ∧
    ∃ o₁ o₂, pureBackSem (reborrowAfterWrite c) h = some o₁ ∧
      heapSem (reborrowAfterWrite c) h = some o₂ ∧
      o₁.heap = h ∧ o₂.heap = upd h 0 c ∧
      o₁.vars 0 = h 0 ∧ o₁.vars 1 = h 0 ∧ o₂.vars 0 = h 0 ∧ o₂.vars 1 = c ∧
      o₁.heap 0 ≠ o₂.heap 0 ∧ o₁.vars 1 ≠ o₂.vars 1 ∧
      pureBackSem (reborrowAfterWrite c) h ≠ heapSem (reborrowAfterWrite c) h := by
  have hne : h 0 ≠ c := fun e => hc e.symm
  have e1 : pureBackSem (reborrowAfterWrite c) h =
      some ⟨h, upd (upd (fun _ => 0) 0 (h 0)) 1 (h 0)⟩ := rfl
  have e2 : heapSem (reborrowAfterWrite c) h =
      some ⟨upd h 0 c, upd (upd (fun _ => 0) 0 (h 0)) 1 (upd h 0 c 0)⟩ := rfl
  have hu0 : upd h 0 c 0 = c := by simp [upd]
  refine ⟨aliasingDiscipline_reborrowAfterWrite c, _, _, e1, e2, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_,
    ?_⟩
  · show upd h 0 c 0 = c
    exact hu0
  · show h 0 ≠ upd h 0 c 0
    rw [hu0]; exact hne
  · show upd (upd (fun _ => 0) 0 (h 0)) 1 (h 0) 1 ≠ upd (upd (fun _ => 0) 0 (h 0)) 1 (upd h 0 c 0) 1
    simp only [upd, ↓reduceIte]
    exact hne
  · rw [e1, e2]
    intro e
    have := congrArg (fun o : Obs => o.vars 1) (Option.some.inj e)
    simp only [upd, ↓reduceIte] at this
    exact hne this

/-- In every stateless model, a successful run of `reborrowAfterWrite c` binds `x0` and `x1` to the
same value, wherever the (failure-only) backward calls are placed. -/
theorem statelessSem_reborrowAfterWrite_vars_eq (F : Ptr → Option Int) (B : Ptr → Int → Bool)
    (π : Placement) (c : Int) (ρ : Env)
    (hρ : statelessSem F B (reborrowAfterWrite c) π = some ρ) : ρ 0 = ρ 1 := by
  unfold statelessSem at hρ
  cases hs : srun F B (translate (reborrowAfterWrite c) π) SState.init with
  | none => rw [hs] at hρ; cases hρ
  | some s' =>
    rw [hs] at hρ
    have hv : s'.vars = ρ := Option.some.inj hρ
    subst hv
    have h2 := srun_filter_not_isBack F B _ _ _ hs
    rw [translate_filter_not_isBack] at h2
    cases hF : F 0 with
    | none =>
      simp [translatePureBack, reborrowAfterWrite, trStmt, srun, sstep, hF] at h2
    | some v =>
      simp [translatePureBack, reborrowAfterWrite, trStmt, srun, sstep, hF, SState.init, upd] at h2
      subst h2
      simp [upd]

/-! ## `stateless-unsound` — every stateless model of `as_mut` is wrong or fails -/

/-- **`stateless-unsound` (every stateless model of `as_mut` is wrong or fails).** For every
forward model `F : Ptr → Option Int`, every backward model `B : Ptr → Int → Bool` (backward calls
may fail but have no other effect), every placement `π` of the backward calls, every initial heap
`h`, and every `c ≠ h 0`: the program `reborrowAfterWrite c` obeys the aliasing discipline; every
successful run of its stateless translation satisfies `x0 = x1` (the two `as_mut` calls on the same
pointer return the same value — the equation that merging duplicate calls relies on); the heap
semantics succeeds with `x0 ≠ x1`; and therefore the stateless translation's outcome on local
variables differs from the heap semantics' (it either fails or computes `x0 = x1`). -/
theorem statelessSem_validates_false_duplicate_call_equation (F : Ptr → Option Int)
    (B : Ptr → Int → Bool) (π : Placement) (h : Heap) (c : Int) (hc : c ≠ h 0) :
    AliasingDiscipline (reborrowAfterWrite c) ∧
    (∀ ρ, statelessSem F B (reborrowAfterWrite c) π = some ρ → ρ 0 = ρ 1) ∧
    (∃ o, heapSem (reborrowAfterWrite c) h = some o ∧ o.vars 0 ≠ o.vars 1) ∧
    statelessSem F B (reborrowAfterWrite c) π ≠ (heapSem (reborrowAfterWrite c) h).map Obs.vars := by
  have hne : h 0 ≠ c := fun e => hc e.symm
  refine ⟨aliasingDiscipline_reborrowAfterWrite c,
    fun ρ hρ => statelessSem_reborrowAfterWrite_vars_eq F B π c ρ hρ, ⟨_, rfl, ?_⟩, ?_⟩
  · show h 0 ≠ c
    exact hne
  · intro heq
    have hheap : (heapSem (reborrowAfterWrite c) h).map Obs.vars =
        some (upd (upd (fun _ => 0) 0 (h 0)) 1 c) := rfl
    rw [hheap] at heq
    have h01 := statelessSem_reborrowAfterWrite_vars_eq F B π c _ heq
    simp only [upd, ↓reduceIte, Nat.zero_ne_add_one] at h01
    exact hne h01

/-! ## `prophecy-agreement` — relation to a prophecy encoding -/

/-- **`prophecy-agreement` (agreement with a prophecy encoding).** If every region ends no later
than the owner's next access to its cell and no later than the program end, then the outcomes of
the prophecy encoding (over all prophecy assignments satisfying every resolution assumption) are
exactly the outcome of the effectful-backward translation: `o` is a prophecy outcome iff the
effectful translation succeeds with `o` (so there is a single outcome, or none if it is stuck). -/
theorem prophOutcome_iff_effSem_of_endsByNextOwnerAccess_of_endsByProgramEnd
    (P : Prog) (π : Placement) (h : Heap)
    (ho : EndsByNextOwnerAccess P π) (he : EndsByProgramEnd P π) :
    ∀ o, ProphOutcome P π h o ↔ effSem P π h = some o :=
  Sim.prophOutcome_iff_effSem P π h ho he

/-- **`prophecy-sound-wider-window` (the prophecy encoding on a wider window).** For a program
obeying the aliasing discipline and a placement ending each region after its creation and after its
last write and no later than the program end (but possibly after the owner's next access), the
prophecy outcomes are exactly the heap semantics' outcome (a single outcome, or none if the heap
semantics is stuck). -/
theorem prophOutcome_iff_heapSem_of_aliasingDiscipline_of_endsAfterCreation_of_endsAfterLastWrite_of_endsByProgramEnd
    (P : Prog) (π : Placement) (h : Heap)
    (had : AliasingDiscipline P) (hc : EndsAfterCreation P π) (hw : EndsAfterLastWrite P π)
    (he : EndsByProgramEnd P π) :
    ∀ o, ProphOutcome P π h o ↔ heapSem P h = some o :=
  Sim.prophOutcome_iff_heapSem P π h had hc hw he

/-! ## Counterexamples (canonical form) -/

section Counterexamples

/-- `sound-lazy` needs `AliasingDiscipline`: a raw write while the reference is in use. -/
theorem effSem_lazyPlacement_eq_heapSem_tight_aliasingDiscipline :
    ¬ AliasingDiscipline rawWriteDuringBorrow ∧
    effSem rawWriteDuringBorrow (lazyPlacement rawWriteDuringBorrow) zeroHeap ≠
      heapSem rawWriteDuringBorrow zeroHeap :=
  ⟨by decide, ne_of_map_ne (f := fun o => o.vars 0) (by decide)⟩

/-- `sound-eager` needs `AliasingDiscipline`: same program, eager ends. -/
theorem effSem_eagerPlacement_eq_heapSem_tight_aliasingDiscipline :
    ¬ AliasingDiscipline rawWriteDuringBorrow ∧
    effSem rawWriteDuringBorrow (eagerPlacement rawWriteDuringBorrow) zeroHeap ≠
      heapSem rawWriteDuringBorrow zeroHeap :=
  ⟨by decide, ne_of_map_ne (f := fun o => o.vars 0) (by decide)⟩

/-- `pure-backward-unsound` needs `c ≠ h 0`: with `c = h 0` the write is invisible, the
pure-backward translation agrees with the heap semantics, and the conclusion fails. -/
theorem pureBackSem_unsound_tight_ne :
    ¬ ((0 : Int) ≠ zeroHeap 0) ∧
    pureBackSem (reborrowAfterWrite 0) zeroHeap = heapSem (reborrowAfterWrite 0) zeroHeap ∧
    ¬ (AliasingDiscipline (reborrowAfterWrite 0) ∧
      ∃ o₁ o₂, pureBackSem (reborrowAfterWrite 0) zeroHeap = some o₁ ∧
        heapSem (reborrowAfterWrite 0) zeroHeap = some o₂ ∧
        o₁.heap = zeroHeap ∧ o₂.heap = upd zeroHeap 0 0 ∧
        o₁.vars 0 = zeroHeap 0 ∧ o₁.vars 1 = zeroHeap 0 ∧ o₂.vars 0 = zeroHeap 0 ∧ o₂.vars 1 = 0 ∧
        o₁.heap 0 ≠ o₂.heap 0 ∧ o₁.vars 1 ≠ o₂.vars 1 ∧
        pureBackSem (reborrowAfterWrite 0) zeroHeap ≠ heapSem (reborrowAfterWrite 0) zeroHeap) := by
  have hupd : upd zeroHeap 0 0 = zeroHeap := by
    funext p; simp only [upd, zeroHeap]; split <;> rfl
  have heq : pureBackSem (reborrowAfterWrite 0) zeroHeap = heapSem (reborrowAfterWrite 0) zeroHeap := by
    have e1 : pureBackSem (reborrowAfterWrite 0) zeroHeap =
        some ⟨zeroHeap, upd (upd (fun _ => 0) 0 0) 1 0⟩ := rfl
    have e2 : heapSem (reborrowAfterWrite 0) zeroHeap =
        some ⟨upd zeroHeap 0 0, upd (upd (fun _ => 0) 0 0) 1 0⟩ := rfl
    rw [e1, e2, hupd]
  refine ⟨by decide, heq, ?_⟩
  rintro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hne⟩
  exact hne heq

/-- `stateless-unsound` needs `c ≠ h 0`: with `c = h 0` the natural stateless model (forward
`some ∘ h`, backward calls always succeed) agrees with the heap semantics on local variables, and
the conclusion fails. -/
theorem statelessSem_validates_false_tight_ne :
    ¬ ((0 : Int) ≠ zeroHeap 0) ∧
    statelessSem (fun p => some (zeroHeap p)) (fun _ _ => true) (reborrowAfterWrite 0)
      (lazyPlacement (reborrowAfterWrite 0)) = (heapSem (reborrowAfterWrite 0) zeroHeap).map Obs.vars ∧
    ¬ (AliasingDiscipline (reborrowAfterWrite 0) ∧
      (∀ ρ, statelessSem (fun p => some (zeroHeap p)) (fun _ _ => true) (reborrowAfterWrite 0)
        (lazyPlacement (reborrowAfterWrite 0)) = some ρ → ρ 0 = ρ 1) ∧
      (∃ o, heapSem (reborrowAfterWrite 0) zeroHeap = some o ∧ o.vars 0 ≠ o.vars 1) ∧
      statelessSem (fun p => some (zeroHeap p)) (fun _ _ => true) (reborrowAfterWrite 0)
        (lazyPlacement (reborrowAfterWrite 0)) ≠ (heapSem (reborrowAfterWrite 0) zeroHeap).map Obs.vars) := by
  have heq : statelessSem (fun p => some (zeroHeap p)) (fun _ _ => true) (reborrowAfterWrite 0)
      (lazyPlacement (reborrowAfterWrite 0)) = (heapSem (reborrowAfterWrite 0) zeroHeap).map Obs.vars := by
    have e1 : statelessSem (fun p => some (zeroHeap p)) (fun _ _ => true) (reborrowAfterWrite 0)
        (lazyPlacement (reborrowAfterWrite 0)) = some (upd (upd (fun _ => 0) 0 0) 1 0) := rfl
    have e2 : (heapSem (reborrowAfterWrite 0) zeroHeap).map Obs.vars =
        some (upd (upd (fun _ => 0) 0 0) 1 0) := rfl
    rw [e1, e2]
  exact ⟨by decide, heq, fun ⟨_, _, _, hne⟩ => hne heq⟩

/-- `endpoint-window` needs `EndsAfterCreation`: an unused region ended before its creation; the
effectful translation is stuck (the backward call has no forward value) while the heap semantics
succeeds. -/
theorem effSem_respecting_tight_endsAfterCreation :
    EndsAfterLastUse unusedRegion (endAt 0) ∧ EndsByNextOwnerAccess unusedRegion (endAt 0) ∧
    EndsByProgramEnd unusedRegion (endAt 0) ∧ ¬ EndsAfterCreation unusedRegion (endAt 0) ∧
    effSem unusedRegion (endAt 0) zeroHeap ≠ heapSem unusedRegion zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, ne_of_map_ne (f := fun o => o.heap 0) (by decide)⟩

/-- `endpoint-window` needs `EndsAfterLastUse`: ending region 0 before its write loses the write. -/
theorem effSem_respecting_tight_endsAfterLastUse :
    EndsAfterCreation (reborrowAfterWrite 5) endBeforeWrite ∧
    EndsByNextOwnerAccess (reborrowAfterWrite 5) endBeforeWrite ∧
    EndsByProgramEnd (reborrowAfterWrite 5) endBeforeWrite ∧
    ¬ EndsAfterLastUse (reborrowAfterWrite 5) endBeforeWrite ∧
    effSem (reborrowAfterWrite 5) endBeforeWrite zeroHeap ≠ heapSem (reborrowAfterWrite 5) zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, ne_of_map_ne (f := fun o => o.vars 1) (by decide)⟩

/-- `endpoint-window` needs `EndsByNextOwnerAccess`: ending region 0 after the second `asMut` makes
that `asMut` read a stale heap model. -/
theorem effSem_respecting_tight_endsByNextOwnerAccess :
    EndsAfterCreation (reborrowAfterWrite 5) endAfterReborrow ∧
    EndsAfterLastUse (reborrowAfterWrite 5) endAfterReborrow ∧
    EndsByProgramEnd (reborrowAfterWrite 5) endAfterReborrow ∧
    ¬ EndsByNextOwnerAccess (reborrowAfterWrite 5) endAfterReborrow ∧
    effSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap ≠
      heapSem (reborrowAfterWrite 5) zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, ne_of_map_ne (f := fun o => o.vars 1) (by decide)⟩

/-- `endpoint-window` needs `EndsByProgramEnd`: a region that never ends never writes back. -/
theorem effSem_respecting_tight_endsByProgramEnd :
    EndsAfterCreation writeOnce (endAt 3) ∧ EndsAfterLastUse writeOnce (endAt 3) ∧
    EndsByNextOwnerAccess writeOnce (endAt 3) ∧ ¬ EndsByProgramEnd writeOnce (endAt 3) ∧
    effSem writeOnce (endAt 3) zeroHeap ≠ heapSem writeOnce zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, ne_of_map_ne (f := fun o => o.heap 0) (by decide)⟩

/-- `endpoint-window-last-write` needs `EndsAfterCreation`. -/
theorem effSem_generalized_tight_endsAfterCreation :
    EndsAfterLastWrite unusedRegion (endAt 0) ∧ EndsByNextOwnerAccess unusedRegion (endAt 0) ∧
    EndsByProgramEnd unusedRegion (endAt 0) ∧ AliasingDiscipline unusedRegion ∧
    ¬ EndsAfterCreation unusedRegion (endAt 0) ∧
    effSem unusedRegion (endAt 0) zeroHeap ≠ heapSem unusedRegion zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    ne_of_map_ne (f := fun o => o.heap 0) (by decide)⟩

/-- `endpoint-window-last-write` needs `EndsAfterLastWrite`. -/
theorem effSem_generalized_tight_endsAfterLastWrite :
    EndsAfterCreation (reborrowAfterWrite 5) endBeforeWrite ∧
    EndsByNextOwnerAccess (reborrowAfterWrite 5) endBeforeWrite ∧
    EndsByProgramEnd (reborrowAfterWrite 5) endBeforeWrite ∧
    AliasingDiscipline (reborrowAfterWrite 5) ∧
    ¬ EndsAfterLastWrite (reborrowAfterWrite 5) endBeforeWrite ∧
    effSem (reborrowAfterWrite 5) endBeforeWrite zeroHeap ≠ heapSem (reborrowAfterWrite 5) zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    ne_of_map_ne (f := fun o => o.vars 1) (by decide)⟩

/-- `endpoint-window-last-write` needs `EndsByNextOwnerAccess`. -/
theorem effSem_generalized_tight_endsByNextOwnerAccess :
    EndsAfterCreation (reborrowAfterWrite 5) endAfterReborrow ∧
    EndsAfterLastWrite (reborrowAfterWrite 5) endAfterReborrow ∧
    EndsByProgramEnd (reborrowAfterWrite 5) endAfterReborrow ∧
    AliasingDiscipline (reborrowAfterWrite 5) ∧
    ¬ EndsByNextOwnerAccess (reborrowAfterWrite 5) endAfterReborrow ∧
    effSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap ≠
      heapSem (reborrowAfterWrite 5) zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    ne_of_map_ne (f := fun o => o.vars 1) (by decide)⟩

/-- `endpoint-window-last-write` needs `EndsByProgramEnd`. -/
theorem effSem_generalized_tight_endsByProgramEnd :
    EndsAfterCreation writeOnce (endAt 3) ∧ EndsAfterLastWrite writeOnce (endAt 3) ∧
    EndsByNextOwnerAccess writeOnce (endAt 3) ∧ AliasingDiscipline writeOnce ∧
    ¬ EndsByProgramEnd writeOnce (endAt 3) ∧
    effSem writeOnce (endAt 3) zeroHeap ≠ heapSem writeOnce zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    ne_of_map_ne (f := fun o => o.heap 0) (by decide)⟩

/-- `endpoint-window-last-write` needs `AliasingDiscipline`: a read through the reference after a
raw write, with the region ended between its last write and the raw write. -/
theorem effSem_generalized_tight_aliasingDiscipline :
    EndsAfterCreation readAfterRawWrite (endAt 2) ∧
    EndsAfterLastWrite readAfterRawWrite (endAt 2) ∧
    EndsByNextOwnerAccess readAfterRawWrite (endAt 2) ∧
    EndsByProgramEnd readAfterRawWrite (endAt 2) ∧
    ¬ AliasingDiscipline readAfterRawWrite ∧
    effSem readAfterRawWrite (endAt 2) zeroHeap ≠ heapSem readAfterRawWrite zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, by decide,
    ne_of_map_ne (f := fun o => o.vars 0) (by decide)⟩

/-- `lock-complete` needs `EndsAfterCreation`: the borrow-locking translation is stuck. -/
theorem lockSem_complete_tight_endsAfterCreation :
    EndsAfterLastUse unusedRegion (endAt 0) ∧ EndsByNextOwnerAccess unusedRegion (endAt 0) ∧
    EndsByProgramEnd unusedRegion (endAt 0) ∧ ¬ EndsAfterCreation unusedRegion (endAt 0) ∧
    lockSem unusedRegion (endAt 0) zeroHeap = none ∧
    lockSem unusedRegion (endAt 0) zeroHeap ≠ heapSem unusedRegion zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, rfl,
    ne_of_map_ne (f := fun o => o.heap 0) (by decide)⟩

/-- `lock-complete` needs `EndsAfterLastUse`: a read after the region's end is stuck in the
borrow-locking translation (it is not stuck in the unchecked one, `effSem_generalized_instance`). -/
theorem lockSem_complete_tight_endsAfterLastUse :
    EndsAfterCreation (writeThenRead 5) (endAt 2) ∧ EndsByNextOwnerAccess (writeThenRead 5) (endAt 2) ∧
    EndsByProgramEnd (writeThenRead 5) (endAt 2) ∧ ¬ EndsAfterLastUse (writeThenRead 5) (endAt 2) ∧
    lockSem (writeThenRead 5) (endAt 2) zeroHeap = none ∧
    lockSem (writeThenRead 5) (endAt 2) zeroHeap ≠ heapSem (writeThenRead 5) zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, rfl,
    ne_of_map_ne (f := fun o => o.heap 0) (by decide)⟩

/-- `lock-complete` needs `EndsByNextOwnerAccess`: the second loan of a still-lent cell is stuck. -/
theorem lockSem_complete_tight_endsByNextOwnerAccess :
    EndsAfterCreation (reborrowAfterWrite 5) endAfterReborrow ∧
    EndsAfterLastUse (reborrowAfterWrite 5) endAfterReborrow ∧
    EndsByProgramEnd (reborrowAfterWrite 5) endAfterReborrow ∧
    ¬ EndsByNextOwnerAccess (reborrowAfterWrite 5) endAfterReborrow ∧
    lockSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap = none ∧
    lockSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap ≠ heapSem (reborrowAfterWrite 5) zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, rfl,
    ne_of_map_ne (f := fun o => o.heap 0) (by decide)⟩

/-- `lock-complete` needs `EndsByProgramEnd`: a cell still lent at the end is stuck. -/
theorem lockSem_complete_tight_endsByProgramEnd :
    EndsAfterCreation writeOnce (endAt 3) ∧ EndsAfterLastUse writeOnce (endAt 3) ∧
    EndsByNextOwnerAccess writeOnce (endAt 3) ∧ ¬ EndsByProgramEnd writeOnce (endAt 3) ∧
    lockSem writeOnce (endAt 3) zeroHeap = none ∧
    lockSem writeOnce (endAt 3) zeroHeap ≠ heapSem writeOnce zeroHeap :=
  ⟨by decide, by decide, by decide, by decide, rfl,
    ne_of_map_ne (f := fun o => o.heap 0) (by decide)⟩

/-- `lock-success-in-window` needs its antecedent `lockSem P π h = some o`: without it the
conclusion would assert that every placement respects liveness, which fails for `endAfterReborrow`
(where the borrow-locking translation is stuck). -/
theorem respectsLiveness_of_lockSem_tight_success :
    lockSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap = none ∧
    ¬ RespectsLiveness (reborrowAfterWrite 5) endAfterReborrow :=
  ⟨rfl, by decide⟩

/-- `lock-sound` needs its antecedent `lockSem P π h = some o`: the outcome `o` produced by the
unchecked translation at the too-late placement `endAfterReborrow` is not the heap semantics'
outcome, and the borrow-locking translation does not produce it (it is stuck there). -/
theorem heapSem_eq_some_of_lockSem_tight_success :
    ∃ o, effSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap = some o ∧
      lockSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap ≠ some o ∧
      heapSem (reborrowAfterWrite 5) zeroHeap ≠ some o := by
  refine ⟨_, rfl, ?_, ne_of_map_ne (f := fun o : Obs => o.vars 1) (by decide)⟩
  have hl : lockSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap = none := rfl
  rw [hl]
  exact (Option.some_ne_none _).symm

/-- `prophecy-agreement` needs `EndsByNextOwnerAccess`: with region 0 ended after the second `asMut`,
the prophecy encoding has an outcome (the correct one) that the effectful translation does not
produce. -/
theorem prophOutcome_iff_effSem_tight_endsByNextOwnerAccess :
    EndsByProgramEnd (reborrowAfterWrite 5) endAfterReborrow ∧
    ¬ EndsByNextOwnerAccess (reborrowAfterWrite 5) endAfterReborrow ∧
    ¬ ∀ o, ProphOutcome (reborrowAfterWrite 5) endAfterReborrow zeroHeap o ↔
      effSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap = some o :=
  ⟨by decide, by decide,
    not_forall_iff_of_left _ ⟨fun _ => 5, rfl⟩ (ne_of_map_ne (f := fun o => o.vars 1) (by decide))⟩

/-- `prophecy-agreement` needs `EndsByProgramEnd`: an unresolved prophecy leaves the owner holding an
arbitrary value. -/
theorem prophOutcome_iff_effSem_tight_endsByProgramEnd :
    EndsByNextOwnerAccess writeOnce (endAt 3) ∧ ¬ EndsByProgramEnd writeOnce (endAt 3) ∧
    ¬ ∀ o, ProphOutcome writeOnce (endAt 3) zeroHeap o ↔ effSem writeOnce (endAt 3) zeroHeap = some o :=
  ⟨by decide, by decide,
    not_forall_iff_of_left _ ⟨fun _ => 9, rfl⟩ (ne_of_map_ne (f := fun o => o.heap 0) (by decide))⟩

/-- `prophecy-sound-wider-window` needs `AliasingDiscipline`. -/
theorem prophOutcome_iff_heapSem_tight_aliasingDiscipline :
    EndsAfterCreation readAfterRawWrite (endAt 4) ∧ EndsAfterLastWrite readAfterRawWrite (endAt 4) ∧
    EndsByProgramEnd readAfterRawWrite (endAt 4) ∧ ¬ AliasingDiscipline readAfterRawWrite ∧
    ¬ ∀ o, ProphOutcome readAfterRawWrite (endAt 4) zeroHeap o ↔
      heapSem readAfterRawWrite zeroHeap = some o :=
  ⟨by decide, by decide, by decide, by decide,
    not_forall_iff_of_left _ ⟨fun _ => 5, rfl⟩ (ne_of_map_ne (f := fun o => o.vars 0) (by decide))⟩

/-- `prophecy-sound-wider-window` needs `EndsAfterCreation`: with an unused region ended before its
creation the prophecy encoding has no outcome, while the heap semantics succeeds. -/
theorem prophOutcome_iff_heapSem_tight_endsAfterCreation :
    AliasingDiscipline unusedRegion ∧ EndsAfterLastWrite unusedRegion (endAt 0) ∧
    EndsByProgramEnd unusedRegion (endAt 0) ∧ ¬ EndsAfterCreation unusedRegion (endAt 0) ∧
    ¬ ∀ o, ProphOutcome unusedRegion (endAt 0) zeroHeap o ↔ heapSem unusedRegion zeroHeap = some o := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro hiff
  have hheap : heapSem unusedRegion zeroHeap = some ⟨zeroHeap, fun _ => 0⟩ := rfl
  obtain ⟨φ, hφ⟩ := (hiff ⟨zeroHeap, fun _ => 0⟩).2 hheap
  cases hφ

/-- `prophecy-sound-wider-window` needs `EndsAfterLastWrite`. -/
theorem prophOutcome_iff_heapSem_tight_endsAfterLastWrite :
    AliasingDiscipline (reborrowAfterWrite 5) ∧ EndsAfterCreation (reborrowAfterWrite 5) endBeforeWrite ∧
    EndsByProgramEnd (reborrowAfterWrite 5) endBeforeWrite ∧
    ¬ EndsAfterLastWrite (reborrowAfterWrite 5) endBeforeWrite ∧
    ¬ ∀ o, ProphOutcome (reborrowAfterWrite 5) endBeforeWrite zeroHeap o ↔
      heapSem (reborrowAfterWrite 5) zeroHeap = some o :=
  ⟨by decide, by decide, by decide, by decide,
    not_forall_iff_of_left _ ⟨fun _ => 0, rfl⟩ (ne_of_map_ne (f := fun o => o.vars 1) (by decide))⟩

/-- `prophecy-sound-wider-window` needs `EndsByProgramEnd`. -/
theorem prophOutcome_iff_heapSem_tight_endsByProgramEnd :
    AliasingDiscipline writeOnce ∧ EndsAfterCreation writeOnce (endAt 3) ∧
    EndsAfterLastWrite writeOnce (endAt 3) ∧ ¬ EndsByProgramEnd writeOnce (endAt 3) ∧
    ¬ ∀ o, ProphOutcome writeOnce (endAt 3) zeroHeap o ↔ heapSem writeOnce zeroHeap = some o :=
  ⟨by decide, by decide, by decide, by decide,
    not_forall_iff_of_left _ ⟨fun _ => 9, rfl⟩ (ne_of_map_ne (f := fun o => o.heap 0) (by decide))⟩

end Counterexamples

/-! ## Non-vacuity witnesses -/

section NonVacuity

/-- `sound-lazy`: a program with two `as_mut` calls on the same pointer obeys the aliasing
discipline, and its lazy placement ends region 0 strictly before the program end. -/
theorem effSem_lazyPlacement_nonvacuous :
    AliasingDiscipline (reborrowAfterWrite 5) ∧ lazyPlacement (reborrowAfterWrite 5) 0 = 3 :=
  ⟨aliasingDiscipline_reborrowAfterWrite 5, by decide⟩

/-- `sound-eager`: a program obeying the aliasing discipline on which the eager and the lazy
placement produce different target programs. -/
theorem effSem_eagerPlacement_nonvacuous :
    AliasingDiscipline writeThenOtherThenRawRead ∧
    translate writeThenOtherThenRawRead (eagerPlacement writeThenOtherThenRawRead) ≠
      translate writeThenOtherThenRawRead (lazyPlacement writeThenOtherThenRawRead) := by
  decide

/-- `pure-backward-unsound`/`stateless-unsound`: the side condition `c ≠ h 0` is satisfiable, and a
natural stateless model (forward model `some ∘ h`, backward calls always succeed) does succeed on
the program, so the universally quantified conclusion of `stateless-unsound` is not vacuous. -/
theorem reborrowAfterWrite_ne_nonvacuous :
    (5 : Int) ≠ zeroHeap 0 ∧
    (statelessSem (fun p => some (zeroHeap p)) (fun _ _ => true) (reborrowAfterWrite 5)
      (lazyPlacement (reborrowAfterWrite 5))).isSome = true := by
  decide

/-- `endpoint-window` and `lock-complete`: the lazy and the eager placement of a program whose
liveness window has two points both satisfy all four hypotheses, and they differ. -/
theorem effSem_respecting_nonvacuous :
    RespectsLiveness writeThenOtherThenRawRead (lazyPlacement writeThenOtherThenRawRead) ∧
    RespectsLiveness writeThenOtherThenRawRead (eagerPlacement writeThenOtherThenRawRead) ∧
    lazyPlacement writeThenOtherThenRawRead 0 ≠ eagerPlacement writeThenOtherThenRawRead 0 := by
  decide

/-- `endpoint-window-last-write`: an instance outside `endpoint-window` (the region ends between its
last write and a later read). -/
theorem effSem_generalized_nonvacuous :
    EndsAfterCreation (writeThenRead 5) (endAt 2) ∧ EndsAfterLastWrite (writeThenRead 5) (endAt 2) ∧
    EndsByNextOwnerAccess (writeThenRead 5) (endAt 2) ∧
    EndsByProgramEnd (writeThenRead 5) (endAt 2) ∧ AliasingDiscipline (writeThenRead 5) ∧
    ¬ EndsAfterLastUse (writeThenRead 5) (endAt 2) := by
  decide

/-- `lock-success-in-window` and `lock-sound`: the borrow-locking translation does succeed on a
program with two loans of one cell. -/
theorem lockSem_success_nonvacuous :
    (lockSem (reborrowAfterWrite 5) (lazyPlacement (reborrowAfterWrite 5)) zeroHeap).isSome = true ∧
    (lockSem writeThenOtherThenRawRead (eagerPlacement writeThenOtherThenRawRead) zeroHeap).isSome =
      true := by
  decide

/-- `prophecy-agreement`: instances where the effectful translation succeeds, including one that
ends a region too early for `endpoint-window` (`prophecy-agreement` does not need
`EndsAfterLastUse`). -/
theorem prophOutcome_iff_effSem_nonvacuous :
    EndsByNextOwnerAccess (reborrowAfterWrite 5) (lazyPlacement (reborrowAfterWrite 5)) ∧
    EndsByProgramEnd (reborrowAfterWrite 5) (lazyPlacement (reborrowAfterWrite 5)) ∧
    (effSem (reborrowAfterWrite 5) (lazyPlacement (reborrowAfterWrite 5)) zeroHeap).isSome = true ∧
    EndsByNextOwnerAccess (reborrowAfterWrite 5) endBeforeWrite ∧
    EndsByProgramEnd (reborrowAfterWrite 5) endBeforeWrite ∧
    (effSem (reborrowAfterWrite 5) endBeforeWrite zeroHeap).isSome = true := by
  decide

/-- `prophecy-sound-wider-window`: an instance outside `endpoint-window` and `prophecy-agreement`
(region 0 ends after the owner's next access). -/
theorem prophOutcome_iff_heapSem_nonvacuous :
    AliasingDiscipline (reborrowAfterWrite 5) ∧ EndsAfterCreation (reborrowAfterWrite 5) endAfterReborrow ∧
    EndsAfterLastWrite (reborrowAfterWrite 5) endAfterReborrow ∧
    EndsByProgramEnd (reborrowAfterWrite 5) endAfterReborrow ∧
    ¬ EndsByNextOwnerAccess (reborrowAfterWrite 5) endAfterReborrow := by
  decide

/-- `aliasing-iff-placement`: both sides of the characterization are exercised, for both named
placements. -/
theorem aliasingDiscipline_iff_nonvacuous :
    (AliasingDiscipline (reborrowAfterWrite 5) ∧
      RespectsLiveness (reborrowAfterWrite 5) (lazyPlacement (reborrowAfterWrite 5)) ∧
      RespectsLiveness (reborrowAfterWrite 5) (eagerPlacement (reborrowAfterWrite 5))) ∧
    (¬ AliasingDiscipline rawWriteDuringBorrow ∧
      ¬ RespectsLiveness rawWriteDuringBorrow (lazyPlacement rawWriteDuringBorrow) ∧
      ¬ RespectsLiveness rawWriteDuringBorrow (eagerPlacement rawWriteDuringBorrow)) := by
  decide

end NonVacuity

/-! ## Positive controls and concrete instances (proved independently of the main statements) -/

section PositiveControls

/-- Positive control for `pure-backward-unsound` and `stateless-unsound`: on the same program, the
effectful translation (lazy ends) agrees with the heap semantics for every initial heap and
every `c`. -/
theorem effSem_reborrowAfterWrite_positive_control (h : Heap) (c : Int) :
    effSem (reborrowAfterWrite c) (lazyPlacement (reborrowAfterWrite c)) h =
      heapSem (reborrowAfterWrite c) h := by
  have e1 : effSem (reborrowAfterWrite c) (lazyPlacement (reborrowAfterWrite c)) h =
      some ⟨upd (upd h 0 c) 0 c, upd (upd (fun _ => 0) 0 (h 0)) 1 c⟩ := rfl
  have e2 : heapSem (reborrowAfterWrite c) h =
      some ⟨upd h 0 c, upd (upd (fun _ => 0) 0 (h 0)) 1 c⟩ := rfl
  rw [e1, e2, upd_upd_same]

/-- Positive control for `pure-backward-unsound` and `stateless-unsound`: the borrow-locking
translation (lazy ends) also agrees with the heap semantics on the same program, for every initial
heap and every `c`. -/
theorem lockSem_reborrowAfterWrite_positive_control (h : Heap) (c : Int) :
    lockSem (reborrowAfterWrite c) (lazyPlacement (reborrowAfterWrite c)) h =
      heapSem (reborrowAfterWrite c) h := by
  have e1 : lockSem (reborrowAfterWrite c) (lazyPlacement (reborrowAfterWrite c)) h =
      some ⟨upd (upd h 0 c) 0 c, upd (upd (fun _ => 0) 0 (h 0)) 1 c⟩ := rfl
  have e2 : heapSem (reborrowAfterWrite c) h =
      some ⟨upd h 0 c, upd (upd (fun _ => 0) 0 (h 0)) 1 c⟩ := rfl
  rw [e1, e2, upd_upd_same]

/-- Positive control for `stateless-unsound`: the effectful translation does not identify the two
`as_mut` calls: the second returns the written value `c`, the first returns `h 0`. -/
theorem effSem_distinguishes_duplicate_calls_positive_control (h : Heap) (c : Int) :
    ∃ o, effSem (reborrowAfterWrite c) (lazyPlacement (reborrowAfterWrite c)) h = some o ∧
      o.vars 0 = h 0 ∧ o.vars 1 = c :=
  ⟨_, rfl, rfl, rfl⟩

/-- Positive control for `stateless-unsound`: with a single `as_mut` (no duplicate call), the
stateless model `F := some ∘ h` with always-succeeding backward calls is exact on local variables. -/
theorem statelessSem_single_reborrow_positive_control (h : Heap) (c : Int) :
    statelessSem (fun p => some (h p)) (fun _ _ => true) (writeThenRead c) (endAt 3) =
      (heapSem (writeThenRead c) h).map Obs.vars := by
  have e1 : statelessSem (fun p => some (h p)) (fun _ _ => true) (writeThenRead c) (endAt 3) =
      some (upd (fun _ => 0) 0 c) := rfl
  have e2 : heapSem (writeThenRead c) h = some ⟨upd h 0 c, upd (fun _ => 0) 0 (upd h 0 c 0)⟩ := rfl
  rw [e1, e2]
  simp [upd]

/-- Concrete instance of `sound-eager` proved directly: on `writeThenOtherThenRawRead` the eager
placement (which differs from the lazy one) gives the heap semantics' outcome, for every heap. -/
theorem effSem_eagerPlacement_instance (h : Heap) :
    effSem writeThenOtherThenRawRead (eagerPlacement writeThenOtherThenRawRead) h =
      heapSem writeThenOtherThenRawRead h :=
  rfl

/-- Concrete instance of `endpoint-window-last-write` outside `endpoint-window`: ending between the
last write and a later read is sound for the unchecked translation. -/
theorem effSem_generalized_instance (h : Heap) (c : Int) :
    effSem (writeThenRead c) (endAt 2) h = heapSem (writeThenRead c) h := by
  have e1 : effSem (writeThenRead c) (endAt 2) h =
      some ⟨upd h 0 c, upd (fun _ => 0) 0 c⟩ := rfl
  have e2 : heapSem (writeThenRead c) h = some ⟨upd h 0 c, upd (fun _ => 0) 0 (upd h 0 c 0)⟩ := rfl
  rw [e1, e2]
  simp [upd]

/-- Outside the window the two write-back translations differ in kind. On each of the three
out-of-window instances used above (region 0 ended before its write; ended after the owner's next
access; a region never ended) the unchecked translation succeeds with an outcome that is **not**
the heap semantics' outcome, while the borrow-locking translation is **stuck**. On the instance
ending a region before its creation both are stuck. -/
theorem outside_window_effSem_wrong_lockSem_stuck :
    (∃ o, effSem (reborrowAfterWrite 5) endBeforeWrite zeroHeap = some o ∧
      heapSem (reborrowAfterWrite 5) zeroHeap ≠ some o) ∧
    lockSem (reborrowAfterWrite 5) endBeforeWrite zeroHeap = none ∧
    (∃ o, effSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap = some o ∧
      heapSem (reborrowAfterWrite 5) zeroHeap ≠ some o) ∧
    lockSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap = none ∧
    (∃ o, effSem writeOnce (endAt 3) zeroHeap = some o ∧ heapSem writeOnce zeroHeap ≠ some o) ∧
    lockSem writeOnce (endAt 3) zeroHeap = none ∧
    effSem unusedRegion (endAt 0) zeroHeap = none ∧ lockSem unusedRegion (endAt 0) zeroHeap = none :=
  ⟨⟨_, rfl, ne_of_map_ne (f := fun o => o.vars 1) (by decide)⟩, rfl,
    ⟨_, rfl, ne_of_map_ne (f := fun o => o.vars 1) (by decide)⟩, rfl,
    ⟨_, rfl, ne_of_map_ne (f := fun o => o.heap 0) (by decide)⟩, rfl, rfl, rfl⟩

/-- Concrete instance contrasting `prophecy-sound-wider-window` with `endpoint-window`: when region
0 ends after the owner's next access, the prophecy outcomes are exactly the heap semantics'
outcome (both directions, proved directly), but the effectful translation goes wrong. -/
theorem prophecy_tolerates_late_end_instance :
    (∀ o, ProphOutcome (reborrowAfterWrite 5) endAfterReborrow zeroHeap o ↔
      heapSem (reborrowAfterWrite 5) zeroHeap = some o) ∧
    effSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap ≠ heapSem (reborrowAfterWrite 5) zeroHeap := by
  refine ⟨fun o => ⟨?_, ?_⟩, ne_of_map_ne (f := fun o => o.vars 1) (by decide)⟩
  · rintro ⟨φ, hφ⟩
    have eval_p : prophSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap φ =
        some (⟨upd (upd zeroHeap 0 (φ 0)) 0 (φ 3), upd (upd (fun _ => 0) 0 0) 1 (φ 0)⟩,
          (true && decide ((5 : Int) = φ 0)) && decide (φ 0 = φ 3)) := rfl
    rw [eval_p] at hφ
    simp only [Option.some.injEq, Prod.mk.injEq, Bool.true_and, Bool.and_eq_true,
      decide_eq_true_eq] at hφ
    rcases hφ with ⟨rfl, h50, h03⟩
    have hφ0 : φ 0 = 5 := h50.symm
    have hφ3 : φ 3 = 5 := h03.symm.trans hφ0
    rw [hφ0, hφ3, upd_upd_same]
    rfl
  · intro hh
    have e2 : heapSem (reborrowAfterWrite 5) zeroHeap =
        some ⟨upd zeroHeap 0 5, upd (upd (fun _ => 0) 0 0) 1 5⟩ := rfl
    rw [e2, Option.some.injEq] at hh
    subst hh
    refine ⟨fun _ => 5, ?_⟩
    have e1 : prophSem (reborrowAfterWrite 5) endAfterReborrow zeroHeap (fun _ => 5) =
        some (⟨upd (upd zeroHeap 0 5) 0 5, upd (upd (fun _ => 0) 0 0) 1 5⟩, true) := rfl
    rw [e1, upd_upd_same]

/-- Outside the aliasing discipline and the window, the prophecy encoding can have **no** outcome
at all while the heap semantics succeeds: the owner reads the prophesied cell, the value written
through the reference depends on that read, and resolution demands `φ 0 + 1 = φ 0`. -/
theorem prophOutcome_empty_ownerReadThenWriteBack :
    ¬ AliasingDiscipline ownerReadThenWriteBack ∧
    ¬ EndsByNextOwnerAccess ownerReadThenWriteBack (endAt 3) ∧
    EndsAfterCreation ownerReadThenWriteBack (endAt 3) ∧
    EndsAfterLastWrite ownerReadThenWriteBack (endAt 3) ∧
    EndsByProgramEnd ownerReadThenWriteBack (endAt 3) ∧
    (heapSem ownerReadThenWriteBack zeroHeap).isSome = true ∧
    ∀ o, ¬ ProphOutcome ownerReadThenWriteBack (endAt 3) zeroHeap o := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  rintro o ⟨φ, hφ⟩
  have e : prophSem ownerReadThenWriteBack (endAt 3) zeroHeap φ =
      some (⟨upd zeroHeap 0 (φ 0), upd (fun _ => 0) 0 (upd zeroHeap 0 (φ 0) 0)⟩,
        true && decide (upd zeroHeap 0 (φ 0) 0 + 1 = φ 0)) := rfl
  rw [e] at hφ
  simp only [Option.some.injEq, Prod.mk.injEq, Bool.true_and, decide_eq_true_eq, upd,
    ↓reduceIte] at hφ
  omega

end PositiveControls

/-! ## Stuckness of the borrow-locking translation is not a diagnosis of the placement -/

/-- The converse of `lock-success-in-window` fails: on the ill-scoped programs `danglingUse` and
`useBeforeCreation`, a liveness-respecting placement still makes the borrow-locking translation
stuck, because the program uses a reference that no earlier `asMut` created. -/
theorem lockSem_none_of_ill_scoped_respectsLiveness :
    (RespectsLiveness danglingUse (endAt 0) ∧ lockSem danglingUse (endAt 0) zeroHeap = none) ∧
    (RespectsLiveness useBeforeCreation (lazyPlacement useBeforeCreation) ∧
      lockSem useBeforeCreation (lazyPlacement useBeforeCreation) zeroHeap = none) :=
  ⟨⟨by decide, rfl⟩, ⟨by decide, rfl⟩⟩

end Toy.Backward
