import Toy.IFC.Core
import Toy.IFC.Typing
import Toy.IFC.Hyperproperties

/-!
# Main Theorems, Ablations, and Characterizations

This module states and proves the core soundness theorems (`cmdTyped_implies_tini`,
`tsTyped_implies_tsni`), the accompanying hyperproperty corollary,
typing-rule ablations, and semantic characterization:

- `cmd-typed-implies-tini` (`cmdTyped_implies_tini`): syntax-directed `pc`-label
  security typing (`CmdTyped`) implies termination-insensitive noninterference
  (`TINI`).
- `no-pc-typed-implicit-flow-counterexample`
  (`noPcTyped_accepts_implicit_flow_violating_tini`): dropping control-dependence
  tracking entirely (`NoPcTyped`) accepts `if h then l := 1 else l := 0`,
  violating `TINI`.
- `cmd-typed-termination-channel-counterexample`
  (`cmdTyped_allows_termination_channel`): `CmdTyped` accepts `while h do skip`,
  which terminates on one low-equivalent store and diverges on another,
  violating `TSNI`.
- `cmd-typed-implies-tini-hyperprop` (`cmdTyped_implies_tiniHyperprop`):
  definitional corollary of `cmdTyped_implies_tini` via `tini_iff_tiniHyperprop`,
  relating `CmdTyped` to the 2-safety hyperproperty `tiniHyperprop Γ`.
- `ts-typed-implies-tsni` (`tsTyped_implies_tsni`): the termination-sensitive
  restriction `TsTyped` (requiring both `pc = low` and `exprLevel Γ e = low`
  at every `while` loop) implies termination-sensitive noninterference (`TSNI`).
- `low-guard-while-typed-termination-channel-counterexample`
  (`lowGuardWhileTyped_allows_termination_channel`): restricting only the `while`
  guard to `low` without requiring `pc = low` still admits a termination channel
  (`if h then (while 1 do skip) else skip`).
- `tsni-iff-tini-and-coterminates` (`tsni_iff_tini_and_coterminates`): in this
  deterministic big-step language, `TSNI` is equivalent to `TINI ∧ CoTerminates`.
- `pc-low-while-typed-termination-channel-counterexample`
  (`pcLowWhileTyped_allows_termination_channel`): restricting only `pc = low` at
  `while` without requiring `exprLevel Γ e = low` still admits a termination
  channel (`while h do skip`).
- `while-no-pc-typed-implicit-flow-counterexample`
  (`whileNoPcTyped_accepts_leak_violating_tini`): raising `pc` at `if` while
  dropping `pc` at `while` still leaks via `while h do (l := 1; h := 0)`.

(The hyperproperty theorems `isTwoSafety_implies_subsetClosed`,
`tiniHyperprop_isTwoSafety`, `tiniHyperprop_subsetClosed`,
`tsniHyperprop_termPairs_not_subsetClosed_of_high_var`,
`tsniHyperprop_termPairs_not_twoSafety_of_high_var`,
`tsni_iff_tsniOutHyperprop`, `tsniOutHyperprop_isTwoSafety`, and
`tsniOutHyperprop_subsetClosed` live in `Toy.IFC.Hyperproperties`.)
-/

namespace Toy.IFC

/-- Confinement: a command typed at `pc = high` never changes a `low` variable. -/
theorem cmdTyped_high_preserves_lowEq {Var : Type} [DecidableEq Var] {Γ : Var → Level}
    {c : Cmd Var} {σ σ' : Store Var} (hEval : Eval c σ σ') :
    ∀ {pc : Level}, CmdTyped Γ pc c → pc = .high → LowEq Γ σ σ' := by
  induction hEval with
  | skip => intro _ _ _; exact LowEq.refl _ _
  | assign =>
    intro pc ht hpc
    cases ht with
    | assign _ hle =>
      subst hpc
      exact LowEq.update_high _ (Level.eq_high_of_high_le hle)
  | seq _ _ ih₁ ih₂ =>
    intro pc ht hpc
    cases ht with
    | seq h₁ h₂ => exact (ih₁ h₁ hpc).trans (ih₂ h₂ hpc)
  | iteTrue _ _ ih =>
    intro pc ht hpc
    cases ht with
    | ite h₁ _ => subst hpc; exact ih h₁ rfl
  | iteFalse _ _ ih =>
    intro pc ht hpc
    cases ht with
    | ite _ h₂ => subst hpc; exact ih h₂ rfl
  | whileFalse _ => intro _ _ _; exact LowEq.refl _ _
  | whileTrue _ _ _ ihBody ihLoop =>
    intro pc ht hpc
    have ht' := ht
    cases ht with
    | whileLoop hb => subst hpc; exact (ihBody hb rfl).trans (ihLoop ht' rfl)

/-- **Termination-insensitive noninterference (`cmd-typed-implies-tini`).**
    Any command well typed under the syntax-directed `pc`-label security type
    system `CmdTyped Γ pc c` satisfies termination-insensitive noninterference
    `TINI Γ c`: if two low-equivalent initial stores both lead to terminating
    executions, the resulting final stores are low-equivalent. -/
theorem cmdTyped_implies_tini
    {Var : Type} [DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var}
    (hTyped : CmdTyped Γ pc c) :
    TINI Γ c := by
  intro σ₁ σ₂ σ₁' σ₂' hLow h₁ h₂
  induction h₁ generalizing pc σ₂ σ₂' with
  | skip => cases h₂; exact hLow
  | @assign x e σ =>
    cases h₂
    cases hTyped with
    | assign he _ =>
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        have hel : exprLevel Γ e = .low := Level.eq_low_of_le_low (hy ▸ he)
        simp [Store.update, exprLevel_low_agrees hLow hel]
      · simp [Store.update, hyx, hLow y hy]
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq h₂a h₂b =>
      cases hTyped with
      | seq t₁ t₂ => exact ih₂ t₂ _ _ (ih₁ t₁ _ _ hLow h₂a) h₂b
  | @iteTrue e c₁ c₂ σ σ' hne hc ih =>
    cases hTyped with
    | ite t₁ t₂ =>
      cases hlev : exprLevel Γ e with
      | low =>
        have hagree := exprLevel_low_agrees hLow hlev
        cases h₂ with
        | iteTrue _ h₂' => exact ih t₁ _ _ hLow h₂'
        | iteFalse heq _ => exact absurd (hagree.trans heq) hne
      | high =>
        rw [hlev, Level.join_high_right] at t₁ t₂
        have hHi : CmdTyped Γ .high (.ite e c₁ c₂) := .ite (by simpa using t₁) (by simpa using t₂)
        have p₁ := cmdTyped_high_preserves_lowEq (Eval.iteTrue hne hc) hHi rfl
        have p₂ := cmdTyped_high_preserves_lowEq h₂ hHi rfl
        exact p₁.symm.trans (hLow.trans p₂)
  | @iteFalse e c₁ c₂ σ σ' heq hc ih =>
    cases hTyped with
    | ite t₁ t₂ =>
      cases hlev : exprLevel Γ e with
      | low =>
        have hagree := exprLevel_low_agrees hLow hlev
        cases h₂ with
        | iteTrue hne _ => exact absurd (hagree.symm.trans heq) hne
        | iteFalse _ h₂' => exact ih t₂ _ _ hLow h₂'
      | high =>
        rw [hlev, Level.join_high_right] at t₁ t₂
        have hHi : CmdTyped Γ .high (.ite e c₁ c₂) := .ite (by simpa using t₁) (by simpa using t₂)
        have p₁ := cmdTyped_high_preserves_lowEq (Eval.iteFalse heq hc) hHi rfl
        have p₂ := cmdTyped_high_preserves_lowEq h₂ hHi rfl
        exact p₁.symm.trans (hLow.trans p₂)
  | @whileFalse e c σ heq =>
    cases hTyped with
    | whileLoop tb =>
      cases hlev : exprLevel Γ e with
      | low =>
        have hagree := exprLevel_low_agrees hLow hlev
        cases h₂ with
        | whileFalse _ => exact hLow
        | whileTrue hne _ _ => exact absurd (hagree.symm.trans heq) hne
      | high =>
        rw [hlev, Level.join_high_right] at tb
        have hHi : CmdTyped Γ .high (.whileLoop e c) := .whileLoop (by simpa using tb)
        exact hLow.trans (cmdTyped_high_preserves_lowEq h₂ hHi rfl)
  | @whileTrue e c σ σm σ' hne hb hl ihBody ihLoop =>
    have hT := hTyped
    cases hTyped with
    | whileLoop tb =>
      cases hlev : exprLevel Γ e with
      | low =>
        have hagree := exprLevel_low_agrees hLow hlev
        cases h₂ with
        | whileFalse heq => exact absurd (hagree.trans heq) hne
        | whileTrue _ h₂b h₂l => exact ihLoop hT _ _ (ihBody tb _ _ hLow h₂b) h₂l
      | high =>
        rw [hlev, Level.join_high_right] at tb
        have hHi : CmdTyped Γ .high (.whileLoop e c) := .whileLoop (by simpa using tb)
        have p₁ := cmdTyped_high_preserves_lowEq (Eval.whileTrue hne hb hl) hHi rfl
        have p₂ := cmdTyped_high_preserves_lowEq h₂ hHi rfl
        exact p₁.symm.trans (hLow.trans p₂)

/-- **Control-dependence ablation: dropping `pc` everywhere
    (`no-pc-typed-implicit-flow-counterexample`).**
    For any labeling `Γ` and variables `l`, `h` with `Γ l = low` and `Γ h = high`,
    the explicit-flow-only system `NoPcTyped` (which omits `pc` tracking) accepts
    `implicitFlowProg l h` (`if h then l := 1 else l := 0`), yet that program
    violates `TINI Γ`. Note that `l ≠ h` is derived from `hLow` and `hHigh`
    (`low_ne_high_var`) rather than assumed separately. -/
theorem noPcTyped_accepts_implicit_flow_violating_tini
    {Var : Type} [DecidableEq Var] {Γ : Var → Level} {l h : Var}
    (hLow : Γ l = .low) (hHigh : Γ h = .high) :
    NoPcTyped Γ (implicitFlowProg l h) ∧ ¬ TINI Γ (implicitFlowProg l h) := by
  constructor
  · exact .ite (.assign (by simp [exprLevel, Level.low_le]))
               (.assign (by simp [exprLevel, Level.low_le]))
  · intro hTini
    let σ₁ : Store Var := Store.update zeroStore h 1
    let σ₂ : Store Var := zeroStore
    have hEqLow : LowEq Γ σ₁ σ₂ := (LowEq.update_high (Γ := Γ) (σ := zeroStore) 1 hHigh).symm
    have hEval₁ : Eval (implicitFlowProg l h) σ₁ (Store.update σ₁ l 1) := by
      apply Eval.iteTrue
      · simp [eval, σ₁]
      · exact Eval.assign
    have hEval₂ : Eval (implicitFlowProg l h) σ₂ (Store.update σ₂ l 0) := by
      apply Eval.iteFalse
      · simp [eval, σ₂, zeroStore]
      · exact Eval.assign
    have hOut := hTini σ₁ σ₂ _ _ hEqLow hEval₁ hEval₂
    have hl := hOut l hLow
    simp [Store.update] at hl

/-- **Termination channel in `CmdTyped`
    (`cmd-typed-termination-channel-counterexample`).**
    For any labeling `Γ`, program counter `pc`, and `high` variable `h`
    (`Γ h = high`), the program `termChannelProg h` (`while h do skip`) is
    accepted by `CmdTyped Γ pc`, yet terminates from `zeroStore` and diverges
    from the low-equivalent store `Store.update zeroStore h 1`, refuting
    `TSNI Γ (termChannelProg h)`. Notably, no `low` variable is even required. -/
theorem cmdTyped_allows_termination_channel
    {Var : Type} [DecidableEq Var] {Γ : Var → Level} {pc : Level} {h : Var}
    (hHigh : Γ h = .high) :
    CmdTyped Γ pc (termChannelProg h) ∧
    LowEq Γ zeroStore (Store.update zeroStore h 1) ∧
    Terminates (termChannelProg h) zeroStore ∧
    ¬ Terminates (termChannelProg h) (Store.update zeroStore h 1) ∧
    ¬ TSNI Γ (termChannelProg h) := by
  have hTyped : CmdTyped Γ pc (termChannelProg h) := .whileLoop .skip
  have hLow : LowEq Γ zeroStore (Store.update zeroStore h 1) :=
    LowEq.update_high 1 hHigh
  have hEval₀ : Eval (termChannelProg h) zeroStore zeroStore :=
    Eval.whileFalse (by simp [eval, zeroStore])
  have hTerm₀ : Terminates (termChannelProg h) zeroStore := ⟨zeroStore, hEval₀⟩
  have hNoTerm₁ : ¬ Terminates (termChannelProg h) (Store.update zeroStore h 1) := by
    rintro ⟨σ', hEval₁⟩
    exact while_skip_no_eval hEval₁ (by simp [eval, Store.update])
  have hNotTsni : ¬ TSNI Γ (termChannelProg h) := by
    intro hTsni
    rcases hTsni zeroStore (Store.update zeroStore h 1) zeroStore hLow hEval₀ with ⟨σ₂', hEval₁, _⟩
    exact hNoTerm₁ ⟨σ₂', hEval₁⟩
  exact ⟨hTyped, hLow, hTerm₀, hNoTerm₁, hNotTsni⟩

/-- **Definitional hyperproperty corollary (`cmd-typed-implies-tini-hyperprop`).**
    Any command well typed under `CmdTyped Γ pc c` has terminating I/O behavior
    `ioBehavior c` belonging to `tiniHyperprop Γ`, which is shown in
    `Toy.IFC.Hyperproperties` to be a 2-safety (`tiniHyperprop_isTwoSafety`)
    and therefore subset-closed (`tiniHyperprop_subsetClosed`) hyperproperty.
    Follows directly from `cmdTyped_implies_tini` via `tini_iff_tiniHyperprop`. -/
theorem cmdTyped_implies_tiniHyperprop
    {Var : Type} [DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var}
    (hTyped : CmdTyped Γ pc c) :
    tiniHyperprop Γ (ioBehavior c) :=
  (tini_iff_tiniHyperprop Γ c).mp (cmdTyped_implies_tini hTyped)

/-- Totality: under `TsTyped`, a command typed at `pc = high` terminates from every store. -/
theorem tsTyped_high_total {Var : Type} [DecidableEq Var] {Γ : Var → Level}
    {pc : Level} {c : Cmd Var} (ht : TsTyped Γ pc c) (hpc : pc = .high) :
    ∀ σ, ∃ σ', Eval c σ σ' := by
  induction ht with
  | skip => intro σ; exact ⟨σ, .skip⟩
  | assign => intro σ; exact ⟨_, .assign⟩
  | seq _ _ ih₁ ih₂ =>
    intro σ
    obtain ⟨σm, h₁⟩ := ih₁ hpc σ
    obtain ⟨σ', h₂⟩ := ih₂ hpc σm
    exact ⟨σ', .seq h₁ h₂⟩
  | @ite pc e c₁ c₂ _ _ ih₁ ih₂ =>
    subst hpc
    intro σ
    by_cases he : eval σ e = 0
    · obtain ⟨σ', h⟩ := ih₂ rfl σ
      exact ⟨σ', .iteFalse he h⟩
    · obtain ⟨σ', h⟩ := ih₁ rfl σ
      exact ⟨σ', .iteTrue he h⟩
  | whileLoop hpc' _ _ _ => subst hpc; cases hpc'

/-- **Termination-sensitive noninterference (`ts-typed-implies-tsni`).**
    Any command well typed under the restricted termination-sensitive system
    `TsTyped Γ pc c` (which requires both `pc = low` and `exprLevel Γ e = low`
    at every `while` loop) satisfies termination-sensitive noninterference
    `TSNI Γ c`. -/
theorem tsTyped_implies_tsni
    {Var : Type} [DecidableEq Var] {Γ : Var → Level} {pc : Level} {c : Cmd Var}
    (hTyped : TsTyped Γ pc c) :
    TSNI Γ c := by
  intro σ₁ σ₂ σ₁' hLow h₁
  induction h₁ generalizing pc σ₂ with
  | skip => exact ⟨σ₂, .skip, hLow⟩
  | @assign x e σ =>
    refine ⟨_, .assign, ?_⟩
    cases hTyped with
    | assign he _ =>
      intro y hy
      by_cases hyx : y = x
      · subst hyx
        have hel : exprLevel Γ e = .low := Level.eq_low_of_le_low (hy ▸ he)
        simp [Store.update, exprLevel_low_agrees hLow hel]
      · simp [Store.update, hyx, hLow y hy]
  | seq _ _ ih₁ ih₂ =>
    cases hTyped with
    | seq t₁ t₂ =>
      obtain ⟨σm₂, h₂a, hm⟩ := ih₁ t₁ _ hLow
      obtain ⟨σ₂', h₂b, hf⟩ := ih₂ t₂ _ hm
      exact ⟨σ₂', .seq h₂a h₂b, hf⟩
  | @iteTrue e c₁ c₂ σ σ' hne hc ih =>
    cases hTyped with
    | ite t₁ t₂ =>
      cases hlev : exprLevel Γ e with
      | low =>
        have hagree := exprLevel_low_agrees hLow hlev
        obtain ⟨σ₂', h₂, hf⟩ := ih t₁ _ hLow
        exact ⟨σ₂', .iteTrue (fun h0 => hne (hagree.trans h0)) h₂, hf⟩
      | high =>
        rw [hlev, Level.join_high_right] at t₁ t₂
        have hHi : TsTyped Γ .high (.ite e c₁ c₂) := .ite (by simpa using t₁) (by simpa using t₂)
        obtain ⟨σ₂', h₂⟩ := tsTyped_high_total hHi rfl σ₂
        have p₁ := cmdTyped_high_preserves_lowEq (Eval.iteTrue hne hc)
          (tsTyped_implies_cmdTyped hHi) rfl
        have p₂ := cmdTyped_high_preserves_lowEq h₂ (tsTyped_implies_cmdTyped hHi) rfl
        exact ⟨σ₂', h₂, p₁.symm.trans (hLow.trans p₂)⟩
  | @iteFalse e c₁ c₂ σ σ' heq hc ih =>
    cases hTyped with
    | ite t₁ t₂ =>
      cases hlev : exprLevel Γ e with
      | low =>
        have hagree := exprLevel_low_agrees hLow hlev
        obtain ⟨σ₂', h₂, hf⟩ := ih t₂ _ hLow
        exact ⟨σ₂', .iteFalse (hagree.symm.trans heq) h₂, hf⟩
      | high =>
        rw [hlev, Level.join_high_right] at t₁ t₂
        have hHi : TsTyped Γ .high (.ite e c₁ c₂) := .ite (by simpa using t₁) (by simpa using t₂)
        obtain ⟨σ₂', h₂⟩ := tsTyped_high_total hHi rfl σ₂
        have p₁ := cmdTyped_high_preserves_lowEq (Eval.iteFalse heq hc)
          (tsTyped_implies_cmdTyped hHi) rfl
        have p₂ := cmdTyped_high_preserves_lowEq h₂ (tsTyped_implies_cmdTyped hHi) rfl
        exact ⟨σ₂', h₂, p₁.symm.trans (hLow.trans p₂)⟩
  | @whileFalse e c σ heq =>
    cases hTyped with
    | whileLoop _ hel _ =>
      exact ⟨σ₂, .whileFalse ((exprLevel_low_agrees hLow hel).symm.trans heq), hLow⟩
  | @whileTrue e c σ σm σ' hne hb hl ihBody ihLoop =>
    have hT := hTyped
    cases hTyped with
    | whileLoop _ hel tb =>
      have hagree := exprLevel_low_agrees hLow hel
      obtain ⟨σm₂, h₂b, hm⟩ := ihBody tb _ hLow
      obtain ⟨σ₂', h₂l, hf⟩ := ihLoop hT _ hm
      exact ⟨σ₂', .whileTrue (fun h0 => hne (hagree.trans h0)) h₂b h₂l, hf⟩

/-- **Ablation for `TsTyped`: low loop guards without `pc = low`
    (`low-guard-while-typed-termination-channel-counterexample`).**
    Under `LowGuardWhileTyped`—which requires every `while` guard to have level
    `low` but omits the `pc = low` requirement on `while`—the program
    `highIfLowWhileProg h` (`if h then (while 1 do skip) else skip`) is well typed
    for any `Γ h = high`, yet terminates from `zeroStore` and diverges from
    low-equivalent `Store.update zeroStore h 1`, violating `TSNI Γ`. -/
theorem lowGuardWhileTyped_allows_termination_channel
    {Var : Type} [DecidableEq Var] {Γ : Var → Level} {pc : Level} {h : Var}
    (hHigh : Γ h = .high) :
    LowGuardWhileTyped Γ pc (highIfLowWhileProg h) ∧
    LowEq Γ zeroStore (Store.update zeroStore h 1) ∧
    Terminates (highIfLowWhileProg h) zeroStore ∧
    ¬ Terminates (highIfLowWhileProg h) (Store.update zeroStore h 1) ∧
    ¬ TSNI Γ (highIfLowWhileProg h) := by
  have hTyped : LowGuardWhileTyped Γ pc (highIfLowWhileProg h) :=
    .ite (.whileLoop rfl .skip) .skip
  have hLow : LowEq Γ zeroStore (Store.update zeroStore h 1) :=
    LowEq.update_high 1 hHigh
  have hEval₀ : Eval (highIfLowWhileProg h) zeroStore zeroStore :=
    Eval.iteFalse (by simp [eval, zeroStore]) Eval.skip
  have hTerm₀ : Terminates (highIfLowWhileProg h) zeroStore := ⟨zeroStore, hEval₀⟩
  have hNoTerm₁ : ¬ Terminates (highIfLowWhileProg h) (Store.update zeroStore h 1) := by
    rintro ⟨σ', hEval₁⟩
    cases hEval₁ with
    | iteTrue _ hLoop =>
      exact while_skip_no_eval hLoop (by simp [eval])
    | iteFalse heq _ =>
      simp [eval, Store.update] at heq
  have hNotTsni : ¬ TSNI Γ (highIfLowWhileProg h) := by
    intro hTsni
    rcases hTsni zeroStore (Store.update zeroStore h 1) zeroStore hLow hEval₀ with ⟨σ₂', hEval₁, _⟩
    exact hNoTerm₁ ⟨σ₂', hEval₁⟩
  exact ⟨hTyped, hLow, hTerm₀, hNoTerm₁, hNotTsni⟩

/-- **Characterization of `TSNI` in deterministic big-step semantics
    (`tsni-iff-tini-and-coterminates`).**
    Because `Eval` is deterministic (`eval_deterministic`) and `LowEq` is
    symmetric, termination-sensitive noninterference (`TSNI Γ c`) is logically
    equivalent to termination-insensitive noninterference (`TINI Γ c`) conjoined
    with co-termination on low-equivalent inputs (`CoTerminates Γ c`). -/
theorem tsni_iff_tini_and_coterminates
    {Var : Type} [DecidableEq Var] (Γ : Var → Level) (c : Cmd Var) :
    TSNI Γ c ↔ TINI Γ c ∧ CoTerminates Γ c := by
  constructor
  · intro hTsni
    constructor
    · intro σ₁ σ₂ σ₁' σ₂' hLow h₁ h₂
      rcases hTsni σ₁ σ₂ σ₁' hLow h₁ with ⟨σ₂'', h₂'', hOut⟩
      have hEq := eval_deterministic h₂'' h₂
      subst hEq
      exact hOut
    · intro σ₁ σ₂ hLow
      constructor
      · rintro ⟨σ₁', h₁⟩
        rcases hTsni σ₁ σ₂ σ₁' hLow h₁ with ⟨σ₂', h₂, _⟩
        exact ⟨σ₂', h₂⟩
      · rintro ⟨σ₂', h₂⟩
        rcases hTsni σ₂ σ₁ σ₂' hLow.symm h₂ with ⟨σ₁', h₁, _⟩
        exact ⟨σ₁', h₁⟩
  · rintro ⟨hTini, hCo⟩ σ₁ σ₂ σ₁' hLow h₁
    rcases (hCo σ₁ σ₂ hLow).mp ⟨σ₁', h₁⟩ with ⟨σ₂', h₂⟩
    exact ⟨σ₂', h₂, hTini σ₁ σ₂ σ₁' σ₂' hLow h₁ h₂⟩

/-- **Symmetric ablation for `TsTyped`: `pc = low` at `while` without low loop guards
    (`pc-low-while-typed-termination-channel-counterexample`).**
    Under `PcLowWhileTyped`—which requires `pc = low` at every `while` loop but
    omits `exprLevel Γ e = low`—the program `termChannelProg h` (`while h do skip`)
    is accepted at `pc = low` for any `Γ h = high`, yet terminates from `zeroStore`
    and diverges from low-equivalent `Store.update zeroStore h 1`, violating `TSNI Γ`. -/
theorem pcLowWhileTyped_allows_termination_channel
    {Var : Type} [DecidableEq Var] {Γ : Var → Level} {h : Var}
    (hHigh : Γ h = .high) :
    PcLowWhileTyped Γ .low (termChannelProg h) ∧
    LowEq Γ zeroStore (Store.update zeroStore h 1) ∧
    Terminates (termChannelProg h) zeroStore ∧
    ¬ Terminates (termChannelProg h) (Store.update zeroStore h 1) ∧
    ¬ TSNI Γ (termChannelProg h) := by
  have hBase := cmdTyped_allows_termination_channel (pc := .low) hHigh
  exact ⟨.whileLoop rfl .skip, hBase.2.1, hBase.2.2.1, hBase.2.2.2.1, hBase.2.2.2.2⟩

/-- **Partial `pc`-tracking ablation: dropping `pc` only at `while`
    (`while-no-pc-typed-implicit-flow-counterexample`).**
    Under `WhileNoPcTyped`—which raises `pc` at `if` but leaves `pc` unchanged
    at `while`—the program `whileLeakProg l h` (`while h do (l := 1; h := 0)`)
    is accepted at `pc = low` for any `Γ l = low` and `Γ h = high`, yet
    terminates on both `zeroStore` (yielding `l = 0`) and `Store.update zeroStore h 1`
    (yielding `l = 1`), violating `TINI Γ`. -/
theorem whileNoPcTyped_accepts_leak_violating_tini
    {Var : Type} [DecidableEq Var] {Γ : Var → Level} {l h : Var}
    (hLow : Γ l = .low) (hHigh : Γ h = .high) :
    WhileNoPcTyped Γ .low (whileLeakProg l h) ∧ ¬ TINI Γ (whileLeakProg l h) := by
  constructor
  · exact .whileLoop (.seq
      (.assign (Level.low_le _) (Level.low_le _))
      (.assign (Level.low_le _) (Level.low_le _)))
  · intro hTini
    have hne : l ≠ h := low_ne_high_var hLow hHigh
    let σ₀ : Store Var := zeroStore
    let σ₁ : Store Var := Store.update zeroStore h 1
    let σ₁m : Store Var := Store.update σ₁ l 1
    let σ₁' : Store Var := Store.update σ₁m h 0
    have hEqLow : LowEq Γ σ₀ σ₁ := LowEq.update_high 1 hHigh
    have hEval₀ : Eval (whileLeakProg l h) σ₀ σ₀ :=
      Eval.whileFalse (by simp [eval, σ₀, zeroStore])
    have hEval₁ : Eval (whileLeakProg l h) σ₁ σ₁' := by
      apply Eval.whileTrue (σm := σ₁')
      · simp [eval, σ₁]
      · exact Eval.seq (σm := σ₁m) Eval.assign Eval.assign
      · exact Eval.whileFalse (by simp [eval, σ₁'])
    have hOut := hTini σ₀ σ₁ σ₀ σ₁' hEqLow hEval₀ hEval₁
    have hl := hOut l hLow
    simp [σ₀, σ₁', σ₁m, zeroStore, Store.update, hne] at hl

end Toy.IFC
