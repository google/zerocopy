import Toy.Obs.Defs
import Toy.Obs.Machines

/-!
# Definition Adequacy Examples

Fully proved positive and negative examples for every core definition in
`Toy.Obs.Defs`, verifying that each definition admits intended instances and
rejects unintended ones.
-/

namespace Toy.Obs

/-! ## Helper Behavior Formulas for Concrete Machines -/

theorem toggleMachine_beh (b : Bool) (w : List Unit) :
    toggleMachine.beh b w = if w.length % 2 = 0 then b else !b := by
  induction w generalizing b with
  | nil => rfl
  | cons _ w ih =>
    change toggleMachine.beh (!b) w = if (w.length + 1) % 2 = 0 then b else !b
    rw [ih (!b)]
    by_cases h : w.length % 2 = 0
    · have h1 : (w.length + 1) % 2 ≠ 0 := by omega
      simp [h, h1]
    · have h1 : (w.length + 1) % 2 = 0 := by omega
      simp [h, h1]

theorem dualToggleMachine_beh (b : Bool) (w : List Unit) :
    dualToggleMachine.beh b w = toggleMachine.beh (!b) w := by
  induction w generalizing b with
  | nil => rfl
  | cons _ w ih =>
    exact ih (!b)

theorem threeStateToggle_beh_eq_toggle (q : ThreeState) (w : List Unit) :
    threeStateToggle.beh q w =
      toggleMachine.beh (match q with | .s0 => false | .s1 => false | .s2 => true) w := by
  induction w generalizing q with
  | nil =>
    cases q <;> rfl
  | cons _ w ih =>
    cases q
    · exact ih .s2
    · exact ih .s2
    · exact ih .s1

theorem syntacticIndependent_beh (a : Bool) (h : Nat) (w : List Unit) :
    syntacticIndependentMachine.beh (a, h) w = toggleMachine.beh a w := by
  induction w generalizing a h with
  | nil => rfl
  | cons _ w ih => exact ih (!a) (h + 1)

theorem redundantTag_beh (x t h : Bool) (w : List Bool) :
    redundantTagMachine.beh ((x, t), h) w = if w.length % 2 = 0 then x else !x := by
  induction w generalizing x t h with
  | nil => rfl
  | cons i w ih =>
    change redundantTagMachine.beh ((!x, h), i) w = if (w.length + 1) % 2 = 0 then x else !x
    rw [ih (!x) h i]
    by_cases hmod : w.length % 2 = 0
    · have h1 : (w.length + 1) % 2 ≠ 0 := by omega
      simp [hmod, h1]
    · have h1 : (w.length + 1) % 2 = 0 := by omega
      simp [hmod, h1]

theorem eraseHidden_redundantTag_beh (h₀ x t : Bool) (w : List Bool) :
    (eraseHidden redundantTagMachine h₀).beh (x, t) w =
      if w.length % 2 = 0 then x else !x := by
  induction w generalizing x t with
  | nil => rfl
  | cons i w ih =>
    change (eraseHidden redundantTagMachine h₀).beh (!x, h₀) w =
      if (w.length + 1) % 2 = 0 then x else !x
    rw [ih (!x) h₀]
    by_cases hmod : w.length % 2 = 0
    · have h1 : (w.length + 1) % 2 ≠ 0 := by omega
      simp [hmod, h1]
    · have h1 : (w.length + 1) % 2 = 0 := by omega
      simp [hmod, h1]

theorem delayedChannel_run_formula (k : Nat)
    (reg : Fin (k + 2) → Bool) (h : Bool) (w : List Unit) :
    ((delayedChannel k).run (reg, h) w).2 = h ∧
    ∀ j : Fin (k + 2),
      ((delayedChannel k).run (reg, h) w).1 j =
        if hlt : j.val + w.length < k + 2 then reg ⟨j.val + w.length, hlt⟩ else h := by
  induction w generalizing reg with
  | nil =>
    refine ⟨rfl, fun j => ?_⟩
    simp
  | cons _ w ih =>
    let reg' : Fin (k + 2) → Bool :=
      fun j => if hlt : j.val + 1 < k + 2 then reg ⟨j.val + 1, hlt⟩ else h
    have hStep := ih reg'
    refine ⟨hStep.1, fun j => ?_⟩
    change ((delayedChannel k).run (reg', h) w).1 j = _
    rw [hStep.2 j]
    simp only [List.length_cons]
    split
    · dsimp only [reg']
      split <;> split
      · congr 1
      · omega
      · omega
      · rfl
    · split
      · omega
      · rfl

theorem delayedChannel_beh_formula (k : Nat)
    (reg : Fin (k + 2) → Bool) (h : Bool) (w : List Unit) :
    (delayedChannel k).beh (reg, h) w =
      if hlt : w.length < k + 2 then reg ⟨w.length, hlt⟩ else h := by
  change ((delayedChannel k).run (reg, h) w).1 ⟨0, Nat.zero_lt_succ _⟩ = _
  rw [(delayedChannel_run_formula k reg h w).2 ⟨0, Nat.zero_lt_succ _⟩]
  simp only [Nat.zero_add]

theorem eraseHidden_delayedChannel_run_formula (k : Nat) (h₀ : Bool)
    (reg : Fin (k + 2) → Bool) (w : List Unit) :
    ∀ j : Fin (k + 2),
      ((eraseHidden (delayedChannel k) h₀).run reg w) j =
        if hlt : j.val + w.length < k + 2 then reg ⟨j.val + w.length, hlt⟩ else h₀ := by
  induction w generalizing reg with
  | nil =>
    intro j
    simp
  | cons _ w ih =>
    let reg' : Fin (k + 2) → Bool :=
      fun j => if hlt : j.val + 1 < k + 2 then reg ⟨j.val + 1, hlt⟩ else h₀
    intro j
    change ((eraseHidden (delayedChannel k) h₀).run reg' w) j = _
    rw [ih reg' j]
    simp only [List.length_cons]
    split
    · dsimp only [reg']
      split <;> split
      · congr 1
      · omega
      · omega
      · rfl
    · split
      · omega
      · rfl

theorem eraseHidden_delayedChannel_beh_formula (k : Nat) (h₀ : Bool)
    (reg : Fin (k + 2) → Bool) (w : List Unit) :
    (eraseHidden (delayedChannel k) h₀).beh reg w =
      if hlt : w.length < k + 2 then reg ⟨w.length, hlt⟩ else h₀ := by
  change ((eraseHidden (delayedChannel k) h₀).run reg w) ⟨0, Nat.zero_lt_succ _⟩ = _
  rw [eraseHidden_delayedChannel_run_formula k h₀ reg w ⟨0, Nat.zero_lt_succ _⟩]
  simp only [Nat.zero_add]

/-! ## `Moore`, `Moore.run`, `Moore.beh` -/

theorem ex_pos_moore_beh :
    toggleMachine.beh false [] = false ∧
    toggleMachine.beh false [()] = true ∧
    toggleMachine.beh false [(), ()] = false :=
  ⟨rfl, rfl, rfl⟩

theorem ex_neg_moore_beh :
    toggleMachine.beh false ≠ (fun _ => false) := by
  intro h
  have h1 := congrFun h [()]
  contradiction

/-! ## `ObsEq` -/

theorem ex_pos_obsEq :
    ThreeState.s0 ≠ ThreeState.s1 ∧ ObsEq threeStateToggle .s0 .s1 := by
  refine ⟨by decide, ?_⟩
  funext w
  rw [threeStateToggle_beh_eq_toggle .s0 w, threeStateToggle_beh_eq_toggle .s1 w]

theorem ex_neg_obsEq :
    delayedDiffMachine.out .s0 = delayedDiffMachine.out .s1 ∧
    ¬ ObsEq delayedDiffMachine .s0 .s1 := by
  refine ⟨rfl, ?_⟩
  intro h
  have h1 := congrFun h [()]
  contradiction

/-! ## `RelPreservesOut`, `RelStepClosed`, `IsBisim` -/

/-- Nontrivial bisimulation relation on `threeStateToggle` identifying the
distinct states `s0` and `s1` while separating them from `s2`. -/
def threeStateBisimRel (q₁ q₂ : ThreeState) : Prop :=
  (q₁ = .s0 ∨ q₁ = .s1) ∧ (q₂ = .s0 ∨ q₂ = .s1) ∨ (q₁ = .s2 ∧ q₂ = .s2)

theorem ex_pos_relPreservesOut :
    RelPreservesOut delayedDiffMachine
      (fun q₁ q₂ => delayedDiffMachine.out q₁ = delayedDiffMachine.out q₂) :=
  fun _ _ h => h

theorem ex_neg_relPreservesOut :
    ¬ RelPreservesOut toggleMachine (fun _ _ => True) := by
  intro h
  have h01 := h false true trivial
  contradiction

theorem ex_pos_relStepClosed :
    RelStepClosed threeStateToggle threeStateBisimRel := by
  intro q₁ q₂ h _
  cases q₁ <;> cases q₂ <;> simp [threeStateBisimRel, threeStateToggle] at h ⊢

theorem ex_neg_relStepClosed :
    ¬ RelStepClosed delayedDiffMachine
      (fun q₁ q₂ => delayedDiffMachine.out q₁ = delayedDiffMachine.out q₂) := by
  intro h
  have h1 := h .s0 .s1 rfl ()
  contradiction

theorem ex_pos_isBisim :
    IsBisim threeStateToggle threeStateBisimRel ∧ threeStateBisimRel .s0 .s1 := by
  refine ⟨⟨?_, ex_pos_relStepClosed⟩, Or.inl ⟨Or.inl rfl, Or.inr rfl⟩⟩
  intro q₁ q₂ h
  cases q₁ <;> cases q₂ <;> simp [threeStateBisimRel, threeStateToggle] at h ⊢

theorem ex_neg_isBisim_fails_out :
    ¬ IsBisim toggleMachine (fun _ _ => True) :=
  fun h => ex_neg_relPreservesOut h.1

theorem ex_neg_isBisim_fails_step :
    ¬ IsBisim delayedDiffMachine
      (fun q₁ q₂ => delayedDiffMachine.out q₁ = delayedDiffMachine.out q₂) :=
  fun h => ex_neg_relStepClosed h.2

/-! ## `PreservesOut`, `PreservesStep`, `IsHom`, `PreservesInit`, `Surjective`, `IsIso` -/

/-- State projection from `threeStateToggle` to `toggleMachine`. -/
def threeToTwo : ThreeState → Bool
  | .s0 => false
  | .s1 => false
  | .s2 => true

theorem ex_pos_preservesOut :
    PreservesOut threeStateToggle toggleMachine threeToTwo := by
  intro q
  cases q <;> rfl

theorem ex_neg_preservesOut :
    ¬ PreservesOut constFalseMachine constTrueMachine (fun _ => ()) := by
  intro h
  have h0 := h ()
  contradiction

theorem ex_pos_preservesStep :
    PreservesStep threeStateToggle toggleMachine threeToTwo := by
  intro q _
  cases q <;> rfl

theorem ex_neg_preservesStep :
    ¬ PreservesStep toggleMachine (finalMachine Unit Bool) (fun q _ => q) := by
  intro h
  have h1 := congrFun (h false ()) []
  contradiction

theorem ex_pos_isHom :
    IsHom threeStateToggle toggleMachine threeToTwo :=
  ⟨ex_pos_preservesOut, ex_pos_preservesStep⟩

theorem ex_neg_isHom :
    ¬ IsHom toggleMachine (finalMachine Unit Bool) (fun q _ => q) :=
  fun h => ex_neg_preservesStep h.2

theorem ex_pos_preservesInit :
    PreservesInit false true Bool.not := rfl

theorem ex_neg_preservesInit :
    ¬ PreservesInit false true id := by
  intro h
  contradiction

theorem ex_pos_surjective :
    Surjective Bool.not := fun b => ⟨!b, Bool.not_not b⟩

theorem ex_neg_surjective :
    ¬ Surjective (fun _ : Unit => false) := by
  intro h
  rcases h true with ⟨_, hu⟩
  contradiction

theorem ex_pos_isIso :
    IsIso toggleMachine dualToggleMachine Bool.not Bool.not := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, Bool.not_not, Bool.not_not⟩
  · intro q; cases q <;> rfl
  · intro q _; cases q <;> rfl
  · intro q; cases q <;> rfl
  · intro q _; cases q <;> rfl

theorem ex_neg_isIso :
    ¬ IsIso redundantToggleMachine constFalseMachine (fun _ => ()) (fun _ => false) := by
  intro h
  have htrue := h.2.2.1 true
  contradiction

/-! ## `finalMachine` -/

theorem ex_pos_finalMachine :
    let alt : List Unit → Bool := fun w => w.length % 2 == 1
    (finalMachine Unit Bool).out alt = false ∧
    (finalMachine Unit Bool).out ((finalMachine Unit Bool).step alt ()) = true :=
  ⟨rfl, rfl⟩

theorem ex_neg_finalMachine :
    let alt : List Unit → Bool := fun w => w.length % 2 == 1
    (finalMachine Unit Bool).step alt () ≠ alt := by
  intro alt h
  have h0 := congrFun h []
  contradiction

/-! ## `Reachable`, `AllReachable`, `BehInjective` -/

theorem ex_pos_reachable :
    Reachable toggleMachine false true :=
  ⟨[()], rfl⟩

theorem ex_neg_reachable :
    ¬ Reachable idBoolMachine false true := by
  rintro ⟨w, hw⟩
  have hfix : ∀ u : List Unit, idBoolMachine.run false u = false := by
    intro u
    induction u with
    | nil => rfl
    | cons _ u ih => exact ih
  rw [hfix w] at hw
  contradiction

theorem ex_pos_allReachable :
    AllReachable toggleMachine false := by
  intro q
  cases q
  · exact ⟨[], rfl⟩
  · exact ⟨[()], rfl⟩

theorem ex_neg_allReachable :
    ¬ AllReachable idBoolMachine false :=
  fun h => ex_neg_reachable (h true)

theorem ex_pos_behInjective :
    BehInjective toggleMachine := by
  intro q₁ q₂ h
  have h0 := congrFun h []
  exact h0

theorem ex_neg_behInjective :
    ¬ BehInjective redundantToggleMachine := by
  intro h
  have hbeh : redundantToggleMachine.beh false = redundantToggleMachine.beh true := by
    funext w
    have hconst : ∀ b (u : List Unit), redundantToggleMachine.beh b u = false := by
      intro b u
      induction u generalizing b with
      | nil => rfl
      | cons _ u ih => exact ih (!b)
    rw [hconst false w, hconst true w]
  have hft := h false true hbeh
  contradiction

/-! ## `ReachableBeh`, `minimalMachine`, `minimalInit`, `toMinimalQuotient`, `minimalIsoFun` -/

theorem ex_pos_reachableBeh :
    ∃ w : List Unit, toggleMachine.beh (toggleMachine.run false w) = toggleMachine.beh true :=
  ⟨[()], rfl⟩

theorem ex_neg_reachableBeh :
    ¬ ∃ w : List Unit, toggleMachine.beh (toggleMachine.run false w) = (fun _ => false) := by
  rintro ⟨w, hw⟩
  have h0 := congrFun hw []
  have h1 := congrFun hw [()]
  simp only [Moore.beh_nil, Moore.beh_cons, toggleMachine] at h0 h1
  rw [h0] at h1
  contradiction

theorem ex_pos_minimalMachine_step :
    (minimalMachine toggleMachine false).out (minimalInit toggleMachine false) = false ∧
    (minimalMachine toggleMachine false).out
      ((minimalMachine toggleMachine false).step (minimalInit toggleMachine false) ()) = true :=
  ⟨rfl, rfl⟩

theorem ex_neg_minimalMachine_step :
    (minimalMachine toggleMachine false).step (minimalInit toggleMachine false) () ≠
      minimalInit toggleMachine false := by
  intro h
  have h0 := congrFun (congrArg Subtype.val h) []
  contradiction

theorem ex_pos_threeStateToggle_allReachable :
    AllReachable threeStateToggle .s0 := by
  intro q
  cases q
  · exact ⟨[], rfl⟩
  · exact ⟨[(), ()], rfl⟩
  · exact ⟨[()], rfl⟩

theorem ex_pos_toMinimalQuotient :
    let hInit : threeStateToggle.beh .s0 = toggleMachine.beh false := by
      funext w
      exact threeStateToggle_beh_eq_toggle .s0 w
    let φ := toMinimalQuotient toggleMachine false threeStateToggle .s0
      ex_pos_threeStateToggle_allReachable hInit
    φ .s0 = φ .s1 ∧ φ .s0 ≠ φ .s2 := by
  dsimp only
  refine ⟨Subtype.ext ?_, ?_⟩
  · funext w
    change threeStateToggle.beh .s0 w = threeStateToggle.beh .s1 w
    rw [threeStateToggle_beh_eq_toggle .s0 w, threeStateToggle_beh_eq_toggle .s1 w]
  · intro h
    have h0 := congrFun (congrArg Subtype.val h) []
    contradiction

theorem ex_neg_toMinimalQuotient_not_injective :
    let hInit : threeStateToggle.beh .s0 = toggleMachine.beh false := by
      funext w
      exact threeStateToggle_beh_eq_toggle .s0 w
    let φ := toMinimalQuotient toggleMachine false threeStateToggle .s0
      ex_pos_threeStateToggle_allReachable hInit
    ¬ ∀ q₁ q₂, φ q₁ = φ q₂ → q₁ = q₂ := by
  intro hInit φ hInj
  have h01 := hInj .s0 .s1 ex_pos_toMinimalQuotient.1
  contradiction

theorem ex_pos_minimalIsoFun :
    minimalIsoFun toggleMachine false dualToggleMachine true ex_pos_allReachable false = true ∧
    minimalIsoFun toggleMachine false dualToggleMachine true ex_pos_allReachable true = false := by
  have hrun : ∀ (b : Bool) (w : List Unit),
      toggleMachine.run b w = if w.length % 2 = 0 then b else !b := by
    intro b w
    exact toggleMachine_beh b w
  have hdrun : ∀ (b : Bool) (w : List Unit),
      dualToggleMachine.run b w = if w.length % 2 = 0 then b else !b := by
    intro b w
    induction w generalizing b with
    | nil => rfl
    | cons _ w ih =>
      change dualToggleMachine.run (!b) w = if (w.length + 1) % 2 = 0 then b else !b
      rw [ih (!b)]
      by_cases h : w.length % 2 = 0
      · have h1 : (w.length + 1) % 2 ≠ 0 := by omega
        simp [h, h1]
      · have h1 : (w.length + 1) % 2 = 0 := by omega
        simp [h, h1]
  constructor
  · unfold minimalIsoFun
    have hw := Classical.choose_spec (ex_pos_allReachable false)
    rw [hrun] at hw
    rw [hdrun]
    by_cases h : (Classical.choose (ex_pos_allReachable false)).length % 2 = 0
    · simp [h]
    · simp [h] at hw
  · unfold minimalIsoFun
    have hw := Classical.choose_spec (ex_pos_allReachable true)
    rw [hrun] at hw
    rw [hdrun]
    by_cases h : (Classical.choose (ex_pos_allReachable true)).length % 2 = 0
    · simp [h] at hw
    · simp [h]

theorem ex_neg_minimalIsoFun :
    minimalIsoFun toggleMachine false dualToggleMachine true ex_pos_allReachable false ≠ false := by
  rw [ex_pos_minimalIsoFun.1]
  decide

/-! ## Split-State Predicates and `eraseHidden` -/

theorem ex_pos_outIgnoresHidden :
    OutIgnoresHidden syntacticIndependentMachine :=
  fun _ _ _ => rfl

theorem ex_neg_outIgnoresHidden :
    ¬ OutIgnoresHidden leakyOutMachine := by
  intro h
  have h01 := h () false true
  contradiction

theorem ex_pos_stepFstIgnoresHidden :
    StepFstIgnoresHidden syntacticIndependentMachine :=
  fun _ _ _ _ => rfl

theorem ex_neg_stepFstIgnoresHidden :
    ¬ StepFstIgnoresHidden redundantTagMachine := by
  intro h
  have h01 := h (false, false) false true false
  injection h01 with _ htag
  contradiction

theorem ex_pos_obsInjectiveFst :
    ObsInjectiveFst syntacticIndependentMachine := by
  intro a₁ a₂ _ h
  exact congrFun h []

theorem ex_pos_obsInjectiveFst_delayedChannel2 :
    ObsInjectiveFst delayedChannel2 := by
  intro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h hEq
  have hx : x₁ = x₂ := congrFun hEq []
  have hy : y₁ = y₂ := congrFun hEq [()]
  cases hx
  cases hy
  rfl

theorem ex_neg_obsInjectiveFst :
    ¬ ObsInjectiveFst redundantTagMachine := by
  intro hInj
  have hBeh : redundantTagMachine.beh ((false, false), false) =
      redundantTagMachine.beh ((false, true), false) := by
    funext w
    rw [redundantTag_beh false false false w, redundantTag_beh false true false w]
  have hEq := hInj (false, false) (false, true) false hBeh
  injection hEq with _ hft
  contradiction

theorem ex_pos_oneStepOutIgnoresHidden :
    OneStepOutIgnoresHidden delayedChannel2 :=
  fun _ _ _ _ => rfl

theorem ex_neg_oneStepOutIgnoresHidden :
    ¬ OneStepOutIgnoresHidden oneStepLeakMachine := by
  intro h
  have h01 := h false false true ()
  contradiction

theorem ex_pos_boundedBehIgnoresHidden :
    BoundedBehIgnoresHidden delayedChannel2 2 := by
  intro a h₁ h₂ w hlen
  match w with
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ =>
    simp only [List.length_cons] at hlen
    omega

theorem ex_neg_boundedBehIgnoresHidden :
    ¬ BoundedBehIgnoresHidden delayedChannel2 3 := by
  intro h
  have h2 := h (false, false) false true [(), ()] (by decide)
  contradiction

theorem ex_pos_behIgnoresHidden :
    BehIgnoresHidden syntacticIndependentMachine := by
  intro a h₁ h₂
  funext w
  rw [syntacticIndependent_beh a h₁ w, syntacticIndependent_beh a h₂ w]

theorem ex_neg_behIgnoresHidden :
    ¬ BehIgnoresHidden delayedChannel2 := by
  intro h
  have h2 := congrFun (h (false, false) false true) [(), ()]
  contradiction

theorem ex_pos_sameFst :
    SameFst ((), false) ((), true) := rfl

theorem ex_neg_sameFst :
    ¬ SameFst (false, false) (true, false) := by
  intro h
  contradiction

theorem ex_pos_coversHidden :
    CoversHidden (SameFst : (Unit × Bool) → (Unit × Bool) → Prop) :=
  fun _ _ _ => rfl

theorem ex_neg_coversHidden :
    ¬ CoversHidden (Eq : (Unit × Bool) → (Unit × Bool) → Prop) := by
  intro h
  have h01 := h () false true
  injection h01 with _ hft
  contradiction

theorem ex_pos_eraseHidden :
    ∀ a h, (eraseHidden syntacticIndependentMachine 0).beh a =
      syntacticIndependentMachine.beh (a, h) := by
  intro a h
  funext w
  rw [syntacticIndependent_beh a h w]
  induction w generalizing a with
  | nil => rfl
  | cons _ w ih => exact ih (!a)

theorem ex_neg_eraseHidden :
    (eraseHidden delayedChannel2 false).beh (false, false) ≠
      delayedChannel2.beh ((false, false), true) := by
  intro h
  have h2 := congrFun h [(), ()]
  contradiction

end Toy.Obs
