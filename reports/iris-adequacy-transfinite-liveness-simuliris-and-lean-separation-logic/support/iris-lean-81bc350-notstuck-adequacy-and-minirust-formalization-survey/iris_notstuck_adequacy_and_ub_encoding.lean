/-!
# `iris-lean@81bc350` `NotStuck` Adequacy Interface and Undefined-Behavior Encoding Bridge (Lean 4.34.1)

This standalone Lean 4.34.1 mechanization reproduces the exact operational
definitions of `Language`, `reducible`, `NotStuck`, multi-step thread-pool
execution (`Step`, `NSteps`), and `Adequate` from
`leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`
(`src/Iris/ProgramLogic/Language.lean:21-120` and
`src/Iris/ProgramLogic/Adequacy.lean:174-372`), and machine-checks the
necessary and sufficient conditions for `NotStuck` adequacy to detect
operational undefined behavior (`NoUB`):

1. **Exact Equivalence Under Irreducible Non-Value UB Encoding (`stuck_ub_adequacy_iff_no_ub`):**
   When undefined behavior is encoded as an irreducible non-value configuration
   (`toVal e = none ∧ ¬ reducible L e σ`) and every non-UB configuration is
   either a value (`(toVal e).isSome`) or reducible (`reducible L e σ`),
   `Adequate L .NotStuck e₁ σ₁ (fun _ _ => True)` holds if and only if no
   thread in any finitely reachable thread pool (`NSteps L n ([e₁], σ₁) (t₂, σ₂)`)
   enters a UB state.
2. **Safe Divergence Without Termination Premise (`loop_adequate_notstuck`):**
   A diverging expression `.loop` (`toVal .loop = none`, stepping to `.loop`)
   satisfies `Adequate L .NotStuck .loop σ (fun _ _ => False)` across all
   finite step horizons `n : Nat` without terminating.
3. **Counterexample A — Terminal Value-Encoded Error (`value_error_masks_ub_under_true_post`
   and `value_error_in_forked_thread_masks_ub_under_standard_adequacy`):**
   If UB is encoded as a terminal error value (`toVal (.val .errorVal) = some .errorVal`),
   it satisfies `NotStuck` (`Or.inl rfl`). Under a permissive main-thread
   postcondition `φ = True`, `Adequate` holds; moreover, even when the main-thread
   postcondition `φ` explicitly forbids `.errorVal`, standard `Adequate`
   (`wp_adequacy_gen`, which existentially hides `forkPost`) still accepts a
   program whose forked thread evaluates to `.val .errorVal` while the main
   thread returns `.okVal 0`. Only `StrongAdequate` (`wp_strong_adequacy_gen`)
   with an explicit `forkPost` catches value-encoded errors in forked threads.
4. **Counterexample B — Stutter-Reducible Error (`stutter_error_masks_ub_for_all_postconditions`):**
   If a UB configuration stutters (`primStep .stutterError σ [] .stutterError σ []`),
   it is `reducible` and never reaches a value, satisfying `Adequate L .NotStuck`
   even for the empty postcondition `φ = False`.
5. **Counterexample C — Nondeterministic Error Branch Pruning (`choose_error_unpruned_not_adequate`
   vs. `choose_error_pruned_adequate`):**
   If an expression `.chooseError` can nondeterministically step either to a safe
   value `.val (.okVal 0)` or to `.stuckError`, full `Adequate` rejects it;
   however, if a semantics adapter drops the `.chooseError → .stuckError` branch,
   `Adequate` falsely accepts `.chooseError`.
-/

namespace IrisNotStuckAdequacyProbe

/-! ## Section 1: Exact `iris-lean@81bc350` Operational Language and Adequacy Definitions -/

/-- Stuckness mode (`Iris/ProgramLogic/WeakestPre.lean` / `Adequacy.lean`). -/
inductive Stuckness where
  | NotStuck
  | MaybeStuck
  deriving DecidableEq, Repr

/--
Operational `Language` structure matching `Iris/ProgramLogic/Language.lean:21-40`
in `leanprover-community/iris-lean@81bc35088ba67d465db008f5261a9b341eb6cf6c`.
-/
structure Language where
  Expr : Type
  Val : Type
  State : Type
  Observation : Type
  ofVal : Val → Expr
  toVal : Expr → Option Val
  primStep : Expr → State → List Observation → Expr → State → List Expr → Prop
  to_of_val : ∀ v, toVal (ofVal v) = some v
  of_to_val : ∀ e v, toVal e = some v → ofVal v = e
  val_stuck : ∀ e σ κs e' σ' efs, primStep e σ κs e' σ' efs → toVal e = none

namespace Language

variable (L : Language)

/-- `reducible e σ` (`Iris/ProgramLogic/Language.lean:68-69`). -/
def reducible (e : L.Expr) (σ : L.State) : Prop :=
  ∃ κs e' σ' efs, L.primStep e σ κs e' σ' efs

/-- `irreducible e σ` (`Iris/ProgramLogic/Language.lean:71-72`). -/
def irreducible (e : L.Expr) (σ : L.State) : Prop :=
  ∀ κs e' σ' efs, ¬ L.primStep e σ κs e' σ' efs

/-- `stuck e σ` (`Iris/ProgramLogic/Language.lean:80-81`). -/
def stuck (e : L.Expr) (σ : L.State) : Prop :=
  L.toVal e = none ∧ L.irreducible e σ

/-- `NotStuck s e σ` (`Iris/ProgramLogic/Language.lean:83-86`). -/
def NotStuck (s : Stuckness) (e : L.Expr) (σ : L.State) : Prop :=
  match s with
  | .NotStuck => (L.toVal e).isSome = true ∨ L.reducible e σ
  | .MaybeStuck => True

/--
Single thread-pool step (`Iris/ProgramLogic/Language.lean:96-102`):
selects one thread `e₁` from `t₁ ++ e₁ :: t₂`, steps `(e₁, σ₁)` to `(e₂, σ₂)`
with spawned threads `efs`, yielding `t₁ ++ e₂ :: t₂ ++ efs`.
-/
inductive Step (cfg₁ cfg₂ : List L.Expr × L.State) : Prop where
  | atomic_step {e₁ σ₁ κs e₂ σ₂ efs t₁ t₂} :
      cfg₁ = (t₁ ++ e₁ :: t₂, σ₁) →
      cfg₂ = (t₁ ++ e₂ :: t₂ ++ efs, σ₂) →
      L.primStep e₁ σ₁ κs e₂ σ₂ efs →
      Step cfg₁ cfg₂

/--
`NSteps L n cfg₁ cfg₂` (`Iris/ProgramLogic/Adequacy.lean:236-246`):
`n`-step thread-pool reachability.
-/
def NSteps : Nat → List L.Expr × L.State → List L.Expr × L.State → Prop
  | 0, cfg₁, cfg₂ => cfg₁ = cfg₂
  | n + 1, cfg₁, cfg₃ => ∃ cfg₂, Step L cfg₁ cfg₂ ∧ NSteps n cfg₂ cfg₃

theorem NSteps.refl (cfg : List L.Expr × L.State) : NSteps L 0 cfg cfg := rfl

theorem NSteps.single {cfg₁ cfg₂} (h : Step L cfg₁ cfg₂) : NSteps L 1 cfg₁ cfg₂ :=
  ⟨cfg₂, h, rfl⟩

/--
`adequate s e₁ σ₁ φ` (`Iris/ProgramLogic/Adequacy.lean:236-246`):
- `val_post`: whenever the main thread `e₁` (at index 0 of the pool) reaches
  `L.ofVal v₂` in state `σ₂` after `n` steps, `φ v₂ σ₂` holds.
- `not_stuck`: every thread `e₂` in every `n`-step reachable thread pool `t₂`
  satisfies `L.NotStuck s e₂ σ₂`.
-/
structure Adequate (s : Stuckness) (e₁ : L.Expr) (σ₁ : L.State)
    (φ : L.Val → L.State → Prop) : Prop where
  val_post : ∀ n t₂ σ₂ v₂,
    NSteps L n ([e₁], σ₁) (L.ofVal v₂ :: t₂, σ₂) → φ v₂ σ₂
  not_stuck : ∀ n t₂ σ₂ e₂,
    NSteps L n ([e₁], σ₁) (t₂, σ₂) → e₂ ∈ t₂ → L.NotStuck s e₂ σ₂

/--
Strong adequacy (`wp_strong_adequacy_gen`, `Iris/ProgramLogic/Adequacy.lean:174-232`)
additionally exposes a per-forked-thread value postcondition `forkPost` on all
threads `e₂ ∈ t₂` that reach values, whereas `wp_adequacy_gen` (`302-334`)
existentially quantifies `forkPost` away.
-/
structure StrongAdequate (s : Stuckness) (e₁ : L.Expr) (σ₁ : L.State)
    (φ : L.Val → L.State → Prop) (forkPost : L.Val → L.State → Prop) : Prop
    extends Adequate L s e₁ σ₁ φ where
  fork_val_post : ∀ n t₂ σ₂ e₂ v₂,
    NSteps L n ([e₁], σ₁) (t₂, σ₂) → e₂ ∈ t₂ → L.toVal e₂ = some v₂ → forkPost v₂ σ₂

end Language

/-! ## Section 2: General Equivalence Between `NotStuck` Adequacy and `NoUB` -/

section AdequacyBridge

variable (L : Language) (IsUB : L.Expr → L.State → Prop)

/-- No reachable thread in any finitely reachable configuration satisfies `IsUB`. -/
def NoReachableUB (e₁ : L.Expr) (σ₁ : L.State) : Prop :=
  ∀ n t₂ σ₂ e₂, L.NSteps n ([e₁], σ₁) (t₂, σ₂) → e₂ ∈ t₂ → ¬ IsUB e₂ σ₂

/--
An encoding of undefined behavior is *well-encoded as stuckness* if:
1. Every UB configuration is stuck (`(L.toVal e).isSome = false ∧ ¬ L.reducible e σ`).
2. Every non-UB configuration is either a value or reducible (`L.NotStuck .NotStuck e σ`).
-/
structure WellEncodedUB : Prop where
  ub_not_val : ∀ e σ, IsUB e σ → (L.toVal e).isSome = false
  ub_not_reducible : ∀ e σ, IsUB e σ → ¬ L.reducible e σ
  non_ub_not_stuck : ∀ e σ, ¬ IsUB e σ → L.NotStuck .NotStuck e σ

theorem notStuck_iff_not_ub (hEnc : WellEncodedUB L IsUB) (e : L.Expr) (σ : L.State) :
    L.NotStuck .NotStuck e σ ↔ ¬ IsUB e σ := by
  constructor
  · intro hNS hUB
    cases hNS with
    | inl hVal =>
      have hFalse := hEnc.ub_not_val e σ hUB
      rw [hVal] at hFalse
      contradiction
    | inr hRed =>
      exact hEnc.ub_not_reducible e σ hUB hRed
  · exact hEnc.non_ub_not_stuck e σ

/--
**Main Bridge Theorem:** Under `WellEncodedUB`, `L.Adequate .NotStuck e₁ σ₁ (fun _ _ => True)`
holds if and only if `NoReachableUB L IsUB e₁ σ₁` holds.
-/
theorem stuck_ub_adequacy_iff_no_ub (hEnc : WellEncodedUB L IsUB)
    (e₁ : L.Expr) (σ₁ : L.State) :
    L.Adequate .NotStuck e₁ σ₁ (fun _ _ => True) ↔ NoReachableUB L IsUB e₁ σ₁ := by
  constructor
  · intro hAdeq n t₂ σ₂ e₂ hSteps hMem
    have hNS := hAdeq.not_stuck n t₂ σ₂ e₂ hSteps hMem
    exact (notStuck_iff_not_ub L IsUB hEnc e₂ σ₂).mp hNS
  · intro hNoUB
    refine ⟨?_, ?_⟩
    · intros; trivial
    · intro n t₂ σ₂ e₂ hSteps hMem
      exact (notStuck_iff_not_ub L IsUB hEnc e₂ σ₂).mpr (hNoUB n t₂ σ₂ e₂ hSteps hMem)

end AdequacyBridge

/-! ## Section 3: Concrete Diagnostic Language with Five UB / Divergence Encodings -/

inductive ProbeVal where
  | okVal (n : Nat)
  | errorVal
  deriving DecidableEq, Repr

/--
Expressions for testing the five operational patterns:
- `val v`: terminal value (`okVal n` or `errorVal`)
- `stepOk n`: normal step to `val (okVal n)`
- `loop`: safe non-terminating loop (`loop → loop`)
- `stuckError`: well-encoded UB (`toVal = none`, no outgoing `primStep`)
- `stutterError`: ill-encoded UB that stutters (`stutterError → stutterError`)
- `chooseError`: nondeterministic branch to `val (okVal 0)` OR `stuckError`
- `forkValueError`: spawns a child thread `val errorVal` and steps main thread to `val (okVal 0)`
-/
inductive ProbeExpr where
  | val (v : ProbeVal)
  | stepOk (n : Nat)
  | loop
  | stuckError
  | stutterError
  | chooseError
  | forkValueError
  deriving DecidableEq, Repr

def probeToVal : ProbeExpr → Option ProbeVal
  | .val v => some v
  | _ => none

/-- Full (unpruned) operational step relation. -/
inductive ProbeStepFull :
    ProbeExpr → Unit → List Unit → ProbeExpr → Unit → List ProbeExpr → Prop where
  | step_ok (n : Nat) :
      ProbeStepFull (.stepOk n) () [] (.val (.okVal n)) () []
  | step_loop :
      ProbeStepFull .loop () [] .loop () []
  | step_stutter_error :
      ProbeStepFull .stutterError () [] .stutterError () []
  | step_choose_ok :
      ProbeStepFull .chooseError () [] (.val (.okVal 0)) () []
  | step_choose_err :
      ProbeStepFull .chooseError () [] .stuckError () []
  | step_fork_val_err :
      ProbeStepFull .forkValueError () [] (.val (.okVal 0)) () [.val .errorVal]

/-- Pruned operational step relation that omits `step_choose_err`. -/
inductive ProbeStepPruned :
    ProbeExpr → Unit → List Unit → ProbeExpr → Unit → List ProbeExpr → Prop where
  | step_ok (n : Nat) :
      ProbeStepPruned (.stepOk n) () [] (.val (.okVal n)) () []
  | step_loop :
      ProbeStepPruned .loop () [] .loop () []
  | step_stutter_error :
      ProbeStepPruned .stutterError () [] .stutterError () []
  | step_choose_ok :
      ProbeStepPruned .chooseError () [] (.val (.okVal 0)) () []
  | step_fork_val_err :
      ProbeStepPruned .forkValueError () [] (.val (.okVal 0)) () [.val .errorVal]

abbrev ProbeLangFull : Language where
  Expr := ProbeExpr
  Val := ProbeVal
  State := Unit
  Observation := Unit
  ofVal := ProbeExpr.val
  toVal := probeToVal
  primStep := ProbeStepFull
  to_of_val := by intro v; rfl
  of_to_val := by
    intro e v h
    cases e <;> simp [probeToVal] at h
    subst h; rfl
  val_stuck := by
    intro e σ κs e' σ' efs hStep
    cases hStep <;> rfl

abbrev ProbeLangPruned : Language where
  Expr := ProbeExpr
  Val := ProbeVal
  State := Unit
  Observation := Unit
  ofVal := ProbeExpr.val
  toVal := probeToVal
  primStep := ProbeStepPruned
  to_of_val := by intro v; rfl
  of_to_val := by
    intro e v h
    cases e <;> simp [probeToVal] at h
    subst h; rfl
  val_stuck := by
    intro e σ κs e' σ' efs hStep
    cases hStep <;> rfl

/-! ### 3.1 Immediate `stuckError` Rejection at 0 Steps -/

theorem stuckError_not_notStuck :
    ¬ ProbeLangFull.NotStuck .NotStuck .stuckError () := by
  intro h
  cases h with
  | inl hVal => cases hVal
  | inr hRed =>
    rcases hRed with ⟨_, _, _, _, hStep⟩
    cases hStep

theorem stuckError_not_adequate :
    ¬ ProbeLangFull.Adequate .NotStuck .stuckError () (fun _ _ => True) := by
  intro hAdeq
  have hNS := hAdeq.not_stuck 0 [ProbeExpr.stuckError] () ProbeExpr.stuckError
    rfl (List.Mem.head _)
  exact stuckError_not_notStuck hNS

/-! ### 3.2 Safe Divergence (`loop`) Satisfies `NotStuck` Adequacy Without Termination -/

theorem loop_step_eq {cfg : List ProbeExpr × Unit}
    (h : ProbeLangFull.Step ([.loop], ()) cfg) :
    cfg = ([.loop], ()) := by
  cases h with
  | @atomic_step e₁ σ₁ κs e₂ σ₂ efs t₁ t₂ h₁ h₂ hPrim =>
    injection h₁ with hList _
    cases t₁ with
    | nil =>
      injection hList with hHead hTail
      subst hHead hTail
      cases hPrim
      exact h₂
    | cons _ tl =>
      cases tl <;> injection hList with _ hTail <;> cases hTail

/-- Invariant: every configuration reachable in `n` steps from `([.loop], ())` is `([.loop], ())`. -/
theorem loop_nsteps_invariant :
    ∀ n {cfg : List ProbeExpr × Unit},
      ProbeLangFull.NSteps n ([.loop], ()) cfg → cfg = ([.loop], ())
  | 0, _, h => h.symm
  | n + 1, _, ⟨_, hStep, hRest⟩ => by
    rw [loop_step_eq hStep] at hRest
    exact loop_nsteps_invariant n hRest

/--
`.loop` satisfies `Adequate .NotStuck` even for the unsatisfiable postcondition
`φ := fun _ _ => False`, proving that `NotStuck` adequacy is a partial-correctness
+ progress safety property that does not require termination.
-/
theorem loop_adequate_notstuck :
    ProbeLangFull.Adequate .NotStuck .loop () (fun _ _ => False) := by
  refine ⟨?_, ?_⟩
  · intro n t₂ σ₂ v₂ hSteps
    have hEq := loop_nsteps_invariant n hSteps
    injection hEq with hList _
    cases hList
  · intro n t₂ σ₂ e₂ hSteps hMem
    have hEq := loop_nsteps_invariant n hSteps
    injection hEq with hList _
    subst hList
    cases hMem with
    | head => exact Or.inr ⟨[], .loop, (), [], ProbeStepFull.step_loop⟩
    | tail _ hTail => cases hTail

/-! ### 3.3 Counterexample A: Terminal Value-Encoded Error (`.val .errorVal`) -/

theorem val_no_step (v : ProbeVal) {cfg : List ProbeExpr × Unit}
    (h : ProbeLangFull.Step ([.val v], ()) cfg) : False := by
  cases h with
  | @atomic_step e₁ σ₁ κs e₂ σ₂ efs t₁ t₂ h₁ _ hPrim =>
    injection h₁ with hList _
    cases t₁ with
    | nil =>
      injection hList with hHead _
      subst hHead
      cases hPrim
    | cons _ tl =>
      cases tl <;> injection hList with _ hTail <;> cases hTail

theorem value_error_nsteps_invariant :
    ∀ n {cfg : List ProbeExpr × Unit},
      ProbeLangFull.NSteps n ([.val .errorVal], ()) cfg → cfg = ([.val .errorVal], ())
  | 0, _, h => h.symm
  | _ + 1, _, ⟨_, hStep, _⟩ => False.elim (val_no_step .errorVal hStep)

/--
1. Under a permissive postcondition `φ := fun _ _ => True`, encoding UB as a
   terminal value `.val .errorVal` satisfies `Adequate .NotStuck` because every
   value satisfies `(toVal e).isSome = true`.
-/
theorem value_error_masks_ub_under_true_post :
    ProbeLangFull.Adequate .NotStuck (.val .errorVal) () (fun _ _ => True) := by
  refine ⟨?_, ?_⟩
  · intros; trivial
  · intro n t₂ σ₂ e₂ hSteps hMem
    have hEq := value_error_nsteps_invariant n hSteps
    injection hEq with hList _
    subst hList
    cases hMem with
    | head => exact Or.inl rfl
    | tail _ hTail => cases hTail

theorem forkValueError_step_eq {cfg : List ProbeExpr × Unit}
    (h : ProbeLangFull.Step ([.forkValueError], ()) cfg) :
    cfg = ([.val (.okVal 0), .val .errorVal], ()) := by
  cases h with
  | @atomic_step e₁ σ₁ κs e₂ σ₂ efs t₁ t₂ h₁ h₂ hPrim =>
    injection h₁ with hList _
    cases t₁ with
    | nil =>
      injection hList with hHead hTail
      subst hHead hTail
      cases hPrim
      exact h₂
    | cons _ tl =>
      cases tl <;> injection hList with _ hTail <;> cases hTail

theorem two_vals_no_step (v₁ v₂ : ProbeVal) {cfg : List ProbeExpr × Unit}
    (h : ProbeLangFull.Step ([.val v₁, .val v₂], ()) cfg) : False := by
  cases h with
  | @atomic_step e₁ σ₁ κs e₂ σ₂ efs t₁ t₂ h₁ _ hPrim =>
    injection h₁ with hList _
    cases t₁ with
    | nil =>
      injection hList with hHead _
      subst hHead
      cases hPrim
    | cons _ tl =>
      cases tl with
      | nil =>
        injection hList with _ hTail
        injection hTail with hHead2 _
        subst hHead2
        cases hPrim
      | cons _ tl' =>
        cases tl' <;> injection hList with _ hTail <;> injection hTail with _ hTail2 <;> cases hTail2

/--
Characterization of configurations reachable from `([.forkValueError], ())`:
either the initial 0-step configuration `([.forkValueError], ())` or the 1-step
terminal pool `([.val (.okVal 0), .val .errorVal], ())`.
-/
theorem forkValueError_nsteps_char :
    ∀ n {cfg : List ProbeExpr × Unit},
      ProbeLangFull.NSteps n ([.forkValueError], ()) cfg →
      cfg = ([.forkValueError], ()) ∨
      cfg = ([.val (.okVal 0), .val .errorVal], ())
  | 0, _, h => Or.inl h.symm
  | 1, _, ⟨_, hStep, hEq⟩ => by
    rw [← hEq]
    exact Or.inr (forkValueError_step_eq hStep)
  | _ + 2, _, ⟨_, hStep₁, ⟨_, hStep₂, _⟩⟩ => by
    rw [forkValueError_step_eq hStep₁] at hStep₂
    exact False.elim (two_vals_no_step (.okVal 0) .errorVal hStep₂)

/--
2. Even when the main-thread postcondition `φ` explicitly rejects `.errorVal`
   (`φ v _ := v ≠ .errorVal`), standard `Adequate .NotStuck` (`wp_adequacy_gen`)
   STILL accepts `.forkValueError`, because the main thread at head index 0
   returns `.okVal 0` while the forked thread at index 1 holds `.val .errorVal`
   (which is a value and therefore `NotStuck`)!
-/
theorem value_error_in_forked_thread_masks_ub_under_standard_adequacy :
    ProbeLangFull.Adequate .NotStuck .forkValueError ()
      (fun v _ => v ≠ .errorVal) := by
  refine ⟨?_, ?_⟩
  · intro n t₂ σ₂ v₂ hSteps
    rcases forkValueError_nsteps_char n hSteps with hEq | hEq
    · injection hEq with hList _
      cases hList
    · injection hEq with hList _
      injection hList with hHead _
      injection hHead with hVal
      subst hVal
      intro hContra
      cases hContra
  · intro n t₂ σ₂ e₂ hSteps hMem
    rcases forkValueError_nsteps_char n hSteps with hEq | hEq
    · injection hEq with hList _
      subst hList
      cases hMem with
      | head =>
        exact Or.inr ⟨[], .val (.okVal 0), (), [.val .errorVal], ProbeStepFull.step_fork_val_err⟩
      | tail _ hTail => cases hTail
    · injection hEq with hList _
      subst hList
      cases hMem with
      | head => exact Or.inl rfl
      | tail _ hTail =>
        cases hTail with
        | head => exact Or.inl rfl
        | tail _ hTail2 => cases hTail2

/--
By contrast, `StrongAdequate` (`wp_strong_adequacy_gen`) with `forkPost v _ := v ≠ .errorVal`
rejects `.forkValueError` because the forked thread at index 1 reaches `.val .errorVal`.
-/
theorem strong_adequacy_rejects_value_error_in_forked_thread :
    ¬ ProbeLangFull.StrongAdequate .NotStuck .forkValueError ()
        (fun v _ => v ≠ .errorVal) (fun v _ => v ≠ .errorVal) := by
  intro hStrong
  have hStep : ProbeLangFull.Step ([ProbeExpr.forkValueError], ())
      ([ProbeExpr.val (.okVal 0), ProbeExpr.val .errorVal], ()) :=
    Language.Step.atomic_step (L := ProbeLangFull)
      (t₁ := []) (t₂ := []) rfl rfl ProbeStepFull.step_fork_val_err
  have hMem : ProbeExpr.val .errorVal ∈ [ProbeExpr.val (.okVal 0), ProbeExpr.val .errorVal] :=
    List.Mem.tail _ (List.Mem.head _)
  have hFork := hStrong.fork_val_post 1
    [ProbeExpr.val (.okVal 0), ProbeExpr.val .errorVal] () (ProbeExpr.val .errorVal) .errorVal
    (Language.NSteps.single ProbeLangFull hStep) hMem rfl
  exact hFork rfl

/-! ### 3.4 Counterexample B: Stutter-Reducible Error (`.stutterError`) -/

theorem stutterError_step_eq {cfg : List ProbeExpr × Unit}
    (h : ProbeLangFull.Step ([.stutterError], ()) cfg) :
    cfg = ([.stutterError], ()) := by
  cases h with
  | @atomic_step e₁ σ₁ κs e₂ σ₂ efs t₁ t₂ h₁ h₂ hPrim =>
    injection h₁ with hList _
    cases t₁ with
    | nil =>
      injection hList with hHead hTail
      subst hHead hTail
      cases hPrim
      exact h₂
    | cons _ tl =>
      cases tl <;> injection hList with _ hTail <;> cases hTail

theorem stutterError_nsteps_invariant :
    ∀ n {cfg : List ProbeExpr × Unit},
      ProbeLangFull.NSteps n ([.stutterError], ()) cfg → cfg = ([.stutterError], ())
  | 0, _, h => h.symm
  | n + 1, _, ⟨_, hStep, hRest⟩ => by
    rw [stutterError_step_eq hStep] at hRest
    exact stutterError_nsteps_invariant n hRest

/--
If an error state stutters (`stutterError → stutterError`), it satisfies
`Adequate .NotStuck` for EVERY postcondition `φ` (including `False`), completely
masking undefined behavior.
-/
theorem stutter_error_masks_ub_for_all_postconditions
    (φ : ProbeVal → Unit → Prop) :
    ProbeLangFull.Adequate .NotStuck .stutterError () φ := by
  refine ⟨?_, ?_⟩
  · intro n t₂ σ₂ v₂ hSteps
    have hEq := stutterError_nsteps_invariant n hSteps
    injection hEq with hList _
    cases hList
  · intro n t₂ σ₂ e₂ hSteps hMem
    have hEq := stutterError_nsteps_invariant n hSteps
    injection hEq with hList _
    subst hList
    cases hMem with
    | head => exact Or.inr ⟨[], .stutterError, (), [], ProbeStepFull.step_stutter_error⟩
    | tail _ hTail => cases hTail

/-! ### 3.5 Counterexample C: Nondeterministic Error Branch Pruning (`chooseError`) -/

/--
In the full language `ProbeLangFull`, `.chooseError` can step to `.stuckError`
in 1 step and therefore violates `Adequate .NotStuck`.
-/
theorem choose_error_unpruned_not_adequate :
    ¬ ProbeLangFull.Adequate .NotStuck .chooseError () (fun _ _ => True) := by
  intro hAdeq
  have hStep : ProbeLangFull.Step ([ProbeExpr.chooseError], ()) ([ProbeExpr.stuckError], ()) :=
    Language.Step.atomic_step (L := ProbeLangFull)
      (t₁ := []) (t₂ := []) rfl rfl ProbeStepFull.step_choose_err
  have hNS := hAdeq.not_stuck 1 [ProbeExpr.stuckError] () ProbeExpr.stuckError
    (Language.NSteps.single ProbeLangFull hStep) (List.Mem.head _)
  exact stuckError_not_notStuck hNS

theorem chooseError_pruned_step_eq {cfg : List ProbeExpr × Unit}
    (h : ProbeLangPruned.Step ([.chooseError], ()) cfg) :
    cfg = ([.val (.okVal 0)], ()) := by
  cases h with
  | @atomic_step e₁ σ₁ κs e₂ σ₂ efs t₁ t₂ h₁ h₂ hPrim =>
    injection h₁ with hList _
    cases t₁ with
    | nil =>
      injection hList with hHead hTail
      subst hHead hTail
      cases hPrim
      exact h₂
    | cons _ tl =>
      cases tl <;> injection hList with _ hTail <;> cases hTail

theorem pruned_val_no_step (v : ProbeVal) {cfg : List ProbeExpr × Unit}
    (h : ProbeLangPruned.Step ([.val v], ()) cfg) : False := by
  cases h with
  | @atomic_step e₁ σ₁ κs e₂ σ₂ efs t₁ t₂ h₁ _ hPrim =>
    injection h₁ with hList _
    cases t₁ with
    | nil =>
      injection hList with hHead _
      subst hHead
      cases hPrim
    | cons _ tl =>
      cases tl <;> injection hList with _ hTail <;> cases hTail

theorem chooseError_pruned_nsteps_char :
    ∀ n {cfg : List ProbeExpr × Unit},
      ProbeLangPruned.NSteps n ([.chooseError], ()) cfg →
      cfg = ([.chooseError], ()) ∨ cfg = ([.val (.okVal 0)], ())
  | 0, _, h => Or.inl h.symm
  | 1, _, ⟨_, hStep, hEq⟩ => by
    rw [← hEq]
    exact Or.inr (chooseError_pruned_step_eq hStep)
  | _ + 2, _, ⟨_, hStep₁, ⟨_, hStep₂, _⟩⟩ => by
    rw [chooseError_pruned_step_eq hStep₁] at hStep₂
    exact False.elim (pruned_val_no_step (.okVal 0) hStep₂)

/--
In `ProbeLangPruned` (where the bad nondeterministic branch `step_choose_err`
was omitted), `.chooseError` falsely satisfies `Adequate .NotStuck`! This
demonstrates why total transition preservation (`step_total`) from the ground
semantics into the `Language` instance is required for `Adequate .NotStuck`
to imply `NoUB`.
-/
theorem choose_error_pruned_adequate :
    ProbeLangPruned.Adequate .NotStuck .chooseError () (fun v _ => v = .okVal 0) := by
  refine ⟨?_, ?_⟩
  · intro n t₂ σ₂ v₂ hSteps
    rcases chooseError_pruned_nsteps_char n hSteps with hEq | hEq
    · injection hEq with hList _
      cases hList
    · injection hEq with hList _
      injection hList with hHead _
      injection hHead with hVal
  · intro n t₂ σ₂ e₂ hSteps hMem
    rcases chooseError_pruned_nsteps_char n hSteps with hEq | hEq
    · injection hEq with hList _
      subst hList
      cases hMem with
      | head => exact Or.inr ⟨[], .val (.okVal 0), (), [], ProbeStepPruned.step_choose_ok⟩
      | tail _ hTail => cases hTail
    · injection hEq with hList _
      subst hList
      cases hMem with
      | head => exact Or.inl rfl
      | tail _ hTail => cases hTail

end IrisNotStuckAdequacyProbe
