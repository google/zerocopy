import Toy.BoundaryLicensing.Basic

set_option autoImplicit false

namespace Toy.BoundaryLicensing

/-! ## Finite-Suite Allowlist, Extensional Lookup, and Anti-Lockout Barriers -/

/-! ### Finite-Suite Allowlist Barrier -/

/-- Extensional soundness of a boolean checker `c` for semantic property `good`. -/
def CheckerSound {α : Type} (good : α → Prop) (c : α → Bool) : Prop :=
  ∀ x : α, c x = true → good x

/-- Pre-fixed finite-suite allowlist restriction accepting `x` iff `x ∈ F` and `c x = true`. -/
def suiteAllowlist {α : Type} [DecidableEq α] (F : List α) (c : α → Bool) (x : α) : Bool :=
  decide (x ∈ F) && c x

/-- A checker law `L` is `SuiteSoundInvariant` on `F` when `L` depends only on `CheckerSound good ·`
truth and input-output behavior restricted to the pre-fixed finite suite `F`. -/
def SuiteSoundInvariant {α : Type} (good : α → Prop) (F : List α)
    (L : (α → Bool) → Prop) : Prop :=
  ∀ c₁ c₂ : α → Bool,
    (CheckerSound good c₁ ↔ CheckerSound good c₂) →
    (∀ x ∈ F, c₁ x = c₂ x) →
    L c₁ → L c₂

theorem checkerSound_suiteAllowlist {α : Type} [DecidableEq α] {good : α → Prop}
    (F : List α) {c : α → Bool} (hsound : CheckerSound good c) :
    CheckerSound good (suiteAllowlist F c) := by
  intro x hx
  simp [suiteAllowlist] at hx
  exact hsound x hx.2

/-- Under `CheckerSound good c`, existence of an accepted artifact outside `F` automatically
witnesses `good p` (`good p` is derivable from `hsound` and `c p = true`). -/
theorem outside_accepted_good_iff {α : Type} (good : α → Prop) (F : List α) (c : α → Bool)
    (hsound : CheckerSound good c) :
    (∃ p : α, p ∉ F ∧ good p ∧ c p = true) ↔ (∃ p : α, p ∉ F ∧ c p = true) := by
  constructor
  · rintro ⟨p, hpnot, _, hcp⟩
    exact ⟨p, hpnot, hcp⟩
  · rintro ⟨p, hpnot, hcp⟩
    exact ⟨p, hpnot, hsound p hcp, hcp⟩

/-- Finite-suite allowlist barrier: every `SuiteSoundInvariant` law satisfied by a sound
checker `c` is also satisfied by `suiteAllowlist F c`, even when `c` accepts an artifact outside `F`
so `suiteAllowlist F c ≠ c`. -/
theorem finite_suite_allowlist_barrier {α : Type} [DecidableEq α]
    (good : α → Prop) (F : List α) (L : (α → Bool) → Prop) (c : α → Bool)
    (hsound : CheckerSound good c)
    (hinv : SuiteSoundInvariant good F L)
    (hlaw : L c)
    (hout : ∃ p : α, p ∉ F ∧ c p = true) :
    L (suiteAllowlist F c) ∧ suiteAllowlist F c ≠ c := by
  have hsound_al : CheckerSound good (suiteAllowlist F c) := checkerSound_suiteAllowlist F hsound
  have heqF : ∀ x ∈ F, c x = suiteAllowlist F c x := by
    intro x hx
    simp [suiteAllowlist, hx]
  refine ⟨hinv c (suiteAllowlist F c) ⟨fun _ => hsound_al, fun _ => hsound⟩ heqF hlaw, ?_⟩
  intro heq
  rcases hout with ⟨p, hpnot, hcp⟩
  have hval := congrFun heq p
  simp [suiteAllowlist, hpnot, hcp] at hval

/-- Positive control for `finite_suite_allowlist_barrier`: a post-freeze probe law inspecting an
artifact `2 ∉ [0]` outside `F` is not `SuiteSoundInvariant` and separates `evenChk` from `suiteAllowlist [0]`. -/
theorem positive_control_postFreeze_probe_separates :
    let good : Nat → Prop := fun n => n % 2 = 0
    let evenChk : Nat → Bool := fun n => n % 2 == 0
    let L : (Nat → Bool) → Prop := fun d => CheckerSound good d ∧ d 2 = true
    CheckerSound good evenChk ∧
    L evenChk ∧
    ¬ L (suiteAllowlist [0] evenChk) := by
  intro good evenChk L
  have hs : CheckerSound good evenChk := by
    intro n hn; simp [evenChk, good] at hn ⊢; exact hn
  refine ⟨hs, ⟨hs, rfl⟩, ?_⟩
  intro hbad
  have h2 := hbad.2
  simp [suiteAllowlist] at h2

/-- Tightness counterexample 1 (`hsound` dropped): `good = (· % 2 = 0)` on `F = [0]`, `c = fun _ => true`
is unsound (`c 1 = true`) while accepting valid outside witness `p = 2` (`2 ∉ [0] ∧ good 2 ∧ c 2 = true`),
and `suiteAllowlist [0] c` becomes sound (`0 % 2 = 0`), falsifying `L = (¬ CheckerSound good ·)`. -/
theorem cex_suite_barrier_without_sound :
    let good : Nat → Prop := fun n => n % 2 = 0
    let L : (Nat → Bool) → Prop := fun d => ¬ CheckerSound good d
    let c : Nat → Bool := fun _ => true
    SuiteSoundInvariant good [0] L ∧
    L c ∧
    (∃ p : Nat, p ∉ ([0] : List Nat) ∧ c p = true) ∧
    (∃ p : Nat, p ∉ ([0] : List Nat) ∧ good p ∧ c p = true) ∧
    ¬ L (suiteAllowlist [0] c) := by
  intro good L c
  refine ⟨?_, ?_, ⟨2, by decide, rfl⟩, ⟨2, by decide, rfl, rfl⟩, ?_⟩
  · intro c₁ c₂ hiff _ h₁ h₂
    exact h₁ (hiff.2 h₂)
  · intro hs
    have h1 : 1 % 2 = 0 := hs 1 rfl
    omega
  · intro hnot
    apply hnot
    intro x hx
    simp [suiteAllowlist, c] at hx
    subst hx
    rfl

/-- Tightness counterexample 2 (`hinv` dropped): when `L` checks `d 2 = true` outside `F = [0]`,
all other hypotheses of `finite_suite_allowlist_barrier` hold and `L (suiteAllowlist [0] c)` fails. -/
theorem cex_suite_barrier_without_invariant :
    let good : Nat → Prop := fun n => n % 2 = 0
    let c : Nat → Bool := fun n => n % 2 == 0
    let L : (Nat → Bool) → Prop := fun d => d 2 = true
    CheckerSound good c ∧
    L c ∧
    (∃ p : Nat, p ∉ ([0] : List Nat) ∧ c p = true) ∧
    ¬ L (suiteAllowlist [0] c) := by
  intro good c L
  refine ⟨fun n hn => by simpa [c, good] using hn, rfl, ⟨2, by decide, rfl⟩, ?_⟩
  simp [L, suiteAllowlist]

/-- Tightness counterexample 3 (`hlaw` dropped): `L = fun _ => False` is `SuiteSoundInvariant`,
all other hypotheses hold, and `L (suiteAllowlist [0] c)` fails. -/
theorem cex_suite_barrier_without_law :
    let good : Nat → Prop := fun n => n % 2 = 0
    let c : Nat → Bool := fun n => n % 2 == 0
    let L : (Nat → Bool) → Prop := fun _ => False
    CheckerSound good c ∧
    SuiteSoundInvariant good [0] L ∧
    (∃ p : Nat, p ∉ ([0] : List Nat) ∧ c p = true) ∧
    ¬ L (suiteAllowlist [0] c) := by
  refine ⟨fun n hn => by simpa using hn, fun _ _ _ _ h => h, ⟨2, by decide, rfl⟩, id⟩

/-- Tightness counterexample 4 (`hout` dropped): when `c` already rejects every input outside `F`,
`suiteAllowlist F c = c`. -/
theorem cex_suite_barrier_without_outside_witness :
    let good : Nat → Prop := fun n => n = 0
    let c : Nat → Bool := fun n => n == 0
    let L : (Nat → Bool) → Prop := fun _ => True
    CheckerSound good c ∧
    SuiteSoundInvariant good [0] L ∧
    L c ∧
    suiteAllowlist [0] c = c := by
  intro good c L
  refine ⟨fun n hn => by simpa [c, good] using hn, fun _ _ _ _ h => h, trivial, ?_⟩
  funext x
  by_cases hx : x = 0
  · subst hx; rfl
  · simp [suiteAllowlist, c, hx]

/-! ### Extensional Lookup-Table Wrapper Barrier -/

/-- Checker paired with explicit internal implementation structure `Code` (distinguishing intensional
representations that share identical input-output behavior `run`). -/
structure ImplChecker (α Code : Type) where
  code : Code
  run : α → Bool

/-- Law `L` over `ImplChecker` is purely extensional when behaviorally identical `run` maps preserve `L`. -/
def ImplExtensionalLaw {α Code : Type} (L : ImplChecker α Code → Prop) : Prop :=
  ∀ c₁ c₂ : ImplChecker α Code, (∀ x : α, c₁.run x = c₂.run x) → L c₁ → L c₂

/-- Finite memoized lookup table `table` agrees with `c` on every stored entry. -/
def TableConsistentWith {α : Type} (table : List (α × Bool)) (c : α → Bool) : Prop :=
  ∀ p ∈ table, p.2 = c p.1

/-- Lookup-table wrapper consulting `table` first and delegating uncached inputs to `fallback`. -/
def lookupWrapper {α : Type} [DecidableEq α] (table : List (α × Bool))
    (fallback : α → Bool) (x : α) : Bool :=
  match table.find? (fun p => p.1 == x) with
  | some (_, b) => b
  | none => fallback x

theorem lookupWrapper_eq_of_consistent {α : Type} [DecidableEq α]
    (table : List (α × Bool)) (c : α → Bool) (hcons : TableConsistentWith table c) (x : α) :
    lookupWrapper table c x = c x := by
  induction table with
  | nil => rfl
  | cons p ps ih =>
    unfold lookupWrapper
    simp only [List.find?_cons]
    by_cases hpx : (p.1 == x) = true
    · simp only [hpx]
      have heq : p.1 = x := by simpa using hpx
      have hv := hcons p List.mem_cons_self
      rw [heq] at hv
      exact hv
    · have hpf : (p.1 == x) = false := Bool.eq_false_iff.2 hpx
      simp only [hpf]
      exact ih (fun q hq => hcons q (List.mem_cons_of_mem p hq))

/-- When `code₁ = code₂`, `⟨code, lookupWrapper table c⟩ = ⟨code, c⟩` by function extensionality,
explaining why distinct `code₁ ≠ code₂` is needed for structural non-equality. -/
theorem lookupWrapper_same_code_eq {α Code : Type} [DecidableEq α]
    (code : Code) (c : α → Bool) (table : List (α × Bool))
    (hcons : TableConsistentWith table c) :
    (⟨code, lookupWrapper table c⟩ : ImplChecker α Code) = ⟨code, c⟩ := by
  congr 1
  funext x
  exact lookupWrapper_eq_of_consistent table c hcons x

/-- Extensional lookup barrier: any purely extensional law `L` satisfied by implementation
`⟨code₁, c⟩` is also satisfied by a distinct lookup-table implementation `⟨code₂, lookupWrapper table c⟩`
whenever `TableConsistentWith table c` holds. -/
theorem extensional_law_admits_lookupWrapper {α Code : Type} [DecidableEq α]
    (L : ImplChecker α Code → Prop) (code₁ code₂ : Code) (c : α → Bool)
    (table : List (α × Bool))
    (hext : ImplExtensionalLaw L)
    (hcons : TableConsistentWith table c)
    (hlaw : L ⟨code₁, c⟩) :
    L ⟨code₂, lookupWrapper table c⟩ ∧ (code₁ ≠ code₂ →
      (⟨code₂, lookupWrapper table c⟩ : ImplChecker α Code) ≠ ⟨code₁, c⟩) := by
  have heq : ∀ x, c x = lookupWrapper table c x :=
    fun x => (lookupWrapper_eq_of_consistent table c hcons x).symm
  refine ⟨hext ⟨code₁, c⟩ ⟨code₂, lookupWrapper table c⟩ heq hlaw, ?_⟩
  intro hne heqStruct
  injection heqStruct with hc _
  exact hne hc.symm

/-- Positive control for `extensional_law_admits_lookupWrapper`: an intensional code-inspecting law
(`chk.code = true`) separates honest compositional code (`true`) from lookup-wrapper code (`false`). -/
theorem positive_control_intensional_code_law_separates :
    let L : ImplChecker Nat Bool → Prop := fun chk => chk.code = true ∧ CheckerSound (· = 0) chk.run
    let c : Nat → Bool := fun n => n == 0
    TableConsistentWith [(0, true)] c ∧
    L ⟨true, c⟩ ∧
    ¬ L ⟨false, lookupWrapper [(0, true)] c⟩ := by
  intro L c
  refine ⟨?_, ⟨rfl, fun n hn => by simpa [c] using hn⟩, fun h => Bool.noConfusion h.1⟩
  intro p hp
  rcases List.mem_singleton.1 hp with rfl
  rfl

/-- Tightness counterexample for `hext` in `extensional_law_admits_lookupWrapper`. -/
theorem cex_lookup_without_extensional :
    let L : ImplChecker Nat Bool → Prop := fun chk => chk.code = true
    let c : Nat → Bool := fun n => n == 0
    TableConsistentWith [(0, true)] c ∧
    L ⟨true, c⟩ ∧
    ¬ L ⟨false, lookupWrapper [(0, true)] c⟩ := by
  refine ⟨?_, rfl, Bool.noConfusion⟩
  intro p hp; rcases List.mem_singleton.1 hp with rfl; rfl

/-- Tightness counterexample for `hcons` in `extensional_law_admits_lookupWrapper`:
an inconsistent lookup entry `(1, true)` breaks extensional soundness. -/
theorem cex_lookup_without_consistent :
    let L : ImplChecker Nat Bool → Prop := fun chk => CheckerSound (· = 0) chk.run
    let c : Nat → Bool := fun n => n == 0
    ImplExtensionalLaw L ∧
    L ⟨true, c⟩ ∧
    ¬ L ⟨false, lookupWrapper [(1, true)] c⟩ := by
  intro L c
  refine ⟨?_, fun n hn => by simpa [c] using hn, ?_⟩
  · intro c₁ c₂ heq h₁ x hx
    rw [← heq x] at hx
    exact h₁ x hx
  · intro hbad
    have h1 := hbad 1 rfl
    omega

/-- Tightness counterexample for `hlaw` in `extensional_law_admits_lookupWrapper`. -/
theorem cex_lookup_without_law :
    let L : ImplChecker Nat Bool → Prop := fun _ => False
    let c : Nat → Bool := fun n => n == 0
    ImplExtensionalLaw L ∧
    TableConsistentWith [(0, true)] c ∧
    ¬ L ⟨false, lookupWrapper [(0, true)] c⟩ := by
  refine ⟨fun _ _ _ h => h, ?_, id⟩
  intro p hp; rcases List.mem_singleton.1 hp with rfl; rfl

/-! ### Exact Anti-Lockout Characterization (`blocking` vs. `warn + adjudicate`) -/

/-- Zero lockout (completeness on valid artifacts): every artifact satisfying `P` is accepted. -/
def ZeroLockout {α : Type} (P : α → Prop) (accept : α → Bool) : Prop :=
  ∀ x : α, P x → accept x = true

/-- Zero false acceptances (soundness): every accepted artifact satisfies `P`. -/
def ZeroFalseAccept {α : Type} (P : α → Prop) (accept : α → Bool) : Prop :=
  ∀ x : α, accept x = true → P x

/-- Gate wiring `Q` directly as a hard `blocking` rejection filter. -/
def blockingGate {α : Type} (Q : α → Bool) (x : α) : Bool :=
  Q x

/-- Gate wiring `Q` as a conservative fast path that routes `Q x = false` warnings to `adj`. -/
def warnAdjudicateGate {α : Type} (Q : α → Bool) (adj : α → Bool) (x : α) : Bool :=
  if Q x then true else adj x

/-- Adjudicator `adj` is exact on warned artifacts (`Q x = false`). -/
def ExactAdjudicatorOnWarnings {α : Type} (P : α → Prop) (Q : α → Bool)
    (adj : α → Bool) : Prop :=
  ∀ x : α, Q x = false → (adj x = true ↔ P x)

/-- Exact Anti-Lockout characterization: a `blocking` check `Q` achieves both
`ZeroLockout` and `ZeroFalseAccept` for `P` iff `Q` is an exact decision procedure for `P`. -/
theorem zeroLockout_and_zeroFalseAccept_iff_exact {α : Type} (P : α → Prop) (Q : α → Bool) :
    (ZeroLockout P (blockingGate Q) ∧ ZeroFalseAccept P (blockingGate Q)) ↔
      ∀ x : α, Q x = true ↔ P x := by
  constructor
  · rintro ⟨hzl, hzfa⟩ x
    exact ⟨hzfa x, hzl x⟩
  · intro hexact
    exact ⟨fun x hp => (hexact x).2 hp, fun x hq => (hexact x).1 hq⟩

/-- Strict proxy lockout: every proxy check `Q` that rejects at least one valid
artifact `x₀` (`P x₀ ∧ Q x₀ = false`) violates `ZeroLockout` when wired as `blockingGate Q`. -/
theorem blockingGate_locks_out_strict_proxy {α : Type} (P : α → Prop) (Q : α → Bool)
    (x₀ : α) (hvalid : P x₀) (hproxy : Q x₀ = false) :
    blockingGate Q x₀ = false ∧ ¬ ZeroLockout P (blockingGate Q) := by
  refine ⟨hproxy, ?_⟩
  intro hzl
  have htrue := hzl x₀ hvalid
  rw [blockingGate, hproxy] at htrue
  cases htrue

/-- `warn + adjudicate` zero-lockout and soundness (positive control for
`blockingGate_locks_out_strict_proxy`): routing `Q x = false` to `adj` satisfying
`ExactAdjudicatorOnWarnings P Q adj` guarantees `ZeroLockout P` unconditionally, and additionally
guarantees `ZeroFalseAccept P` whenever the fast path `Q` is conservative (`ZeroFalseAccept P Q`). -/
theorem warnAdjudicateGate_zeroLockout_and_sound {α : Type} (P : α → Prop)
    (Q adj : α → Bool)
    (hadj : ExactAdjudicatorOnWarnings P Q adj)
    (hfast : ZeroFalseAccept P Q) :
    ZeroLockout P (warnAdjudicateGate Q adj) ∧
    ZeroFalseAccept P (warnAdjudicateGate Q adj) := by
  refine ⟨?_, ?_⟩
  · intro x hp
    unfold warnAdjudicateGate
    cases hq : Q x with
    | true => rfl
    | false => exact (hadj x hq).2 hp
  · intro x hacc
    unfold warnAdjudicateGate at hacc
    cases hq : Q x with
    | true => exact hfast x hq
    | false =>
      rw [hq] at hacc
      exact (hadj x hq).1 hacc

/-- Tightness counterexample for `hadj` in `warnAdjudicateGate_zeroLockout_and_sound`:
if `adj` rejects a warned valid artifact, `ZeroLockout` fails. -/
theorem cex_warnAdjudicate_without_exact_adjudicator :
    let P : Bool → Prop := fun b => b = true
    let Q : Bool → Bool := fun _ => false
    let adj : Bool → Bool := fun _ => false
    ZeroFalseAccept P Q ∧
    ¬ ZeroLockout P (warnAdjudicateGate Q adj) := by
  refine ⟨(fun _ h => by cases h), ?_⟩
  intro hzl
  exact Bool.noConfusion (hzl true rfl)

/-- Tightness counterexample for `hfast` in `warnAdjudicateGate_zeroLockout_and_sound`:
if the fast path `Q` accepts an invalid artifact (`Q false = true`), `warnAdjudicateGate` short-circuits
without invoking `adj` and violates `ZeroFalseAccept`. -/
theorem cex_warnAdjudicate_without_sound_fastPath :
    let P : Bool → Prop := fun b => b = true
    let Q : Bool → Bool := fun _ => true
    let adj : Bool → Bool := fun b => b
    ExactAdjudicatorOnWarnings P Q adj ∧
    ¬ ZeroFalseAccept P (warnAdjudicateGate Q adj) := by
  refine ⟨(fun _ h => by cases h), ?_⟩
  intro hzfa
  exact Bool.noConfusion (hzfa false rfl)

/-- Tightness counterexample for `hvalid` in `blockingGate_locks_out_strict_proxy`. -/
theorem cex_blocking_lockout_without_valid_witness :
    let P : Bool → Prop := fun b => b = true
    let Q : Bool → Bool := fun b => b
    Q false = false ∧ ZeroLockout P (blockingGate Q) :=
  ⟨rfl, fun _ h => h⟩

/-- Tightness counterexample for `hproxy` in `blockingGate_locks_out_strict_proxy`. -/
theorem cex_blocking_lockout_without_proxy_reject :
    let P : Bool → Prop := fun b => b = true
    let Q : Bool → Bool := fun b => b
    P true ∧ ZeroLockout P (blockingGate Q) :=
  ⟨rfl, fun _ h => h⟩

/-! ### Proved Positive and Negative Examples & Non-Vacuity Witnesses for `Barriers.lean` -/

theorem checkerSound_pos : CheckerSound (fun n : Nat => n = 0) (fun n => n == 0) :=
  fun n hn => by simpa using hn

theorem checkerSound_neg : ¬ CheckerSound (fun n : Nat => n = 0) (fun _ => true) := by
  intro h; have := h 1 rfl; omega

theorem suiteAllowlist_pos : suiteAllowlist [0, 2] (fun n => n % 2 == 0) 2 = true := rfl
theorem suiteAllowlist_neg : suiteAllowlist [0, 2] (fun n => n % 2 == 0) 4 = false := rfl

theorem suiteSoundInvariant_pos :
    SuiteSoundInvariant (fun n : Nat => n % 2 = 0) [0] (fun c => c 0 = true) :=
  fun _ _ _ hF hc => by dsimp only at hc ⊢; rw [← hF 0 (List.mem_singleton.2 rfl)]; exact hc

theorem suiteSoundInvariant_neg :
    ¬ SuiteSoundInvariant (fun n : Nat => n % 2 = 0) [0] (fun c => c 2 = true) := by
  intro hinv
  have h := cex_suite_barrier_without_invariant
  have hs1 : CheckerSound (fun n : Nat => n % 2 = 0) (fun n => n % 2 == 0) := h.1
  have hs2 := checkerSound_suiteAllowlist [0] hs1
  have heq : ∀ x ∈ ([0] : List Nat), (x % 2 == 0) = suiteAllowlist [0] (fun n => n % 2 == 0) x := by
    intro x hx; rcases List.mem_singleton.1 hx with rfl; rfl
  exact h.2.2.2 (hinv _ _ ⟨fun _ => hs2, fun _ => hs1⟩ heq rfl)

theorem implExtensionalLaw_pos :
    ImplExtensionalLaw (fun chk : ImplChecker Nat Bool => chk.run 0 = true) :=
  fun _ _ heq h => by dsimp only at h ⊢; rw [← heq 0]; exact h

theorem implExtensionalLaw_neg :
    ¬ ImplExtensionalLaw (fun chk : ImplChecker Nat Bool => chk.code = true) := by
  intro hext
  exact Bool.noConfusion (hext ⟨true, fun _ => true⟩ ⟨false, fun _ => true⟩ (fun _ => rfl) rfl)

theorem tableConsistentWith_pos : TableConsistentWith [(0, true)] (fun n : Nat => n == 0) := by
  intro p hp; rcases List.mem_singleton.1 hp with rfl; rfl

theorem tableConsistentWith_neg : ¬ TableConsistentWith [(1, true)] (fun n : Nat => n == 0) := by
  intro h; have := h (1, true) (List.mem_singleton.2 rfl); simp at this

theorem lookupWrapper_pos : lookupWrapper [(0, true)] (fun _ : Nat => false) 0 = true := rfl
theorem lookupWrapper_neg : lookupWrapper [(0, true)] (fun _ : Nat => false) 1 = false := rfl

theorem zeroLockout_pos : ZeroLockout (fun b : Bool => b = true) (fun b => b) := fun _ h => h
theorem zeroLockout_neg : ¬ ZeroLockout (fun b : Bool => b = true) (fun _ => false) := by
  intro h; exact Bool.noConfusion (h true rfl)

theorem zeroFalseAccept_pos : ZeroFalseAccept (fun b : Bool => b = true) (fun _ => false) :=
  fun _ h => by cases h

theorem zeroFalseAccept_neg : ¬ ZeroFalseAccept (fun b : Bool => b = true) (fun _ => true) := by
  intro h; exact Bool.noConfusion (h false rfl)

theorem blockingGate_pos : blockingGate (fun b : Bool => b) true = true := rfl
theorem blockingGate_neg : blockingGate (fun b : Bool => b) false = false := rfl

theorem warnAdjudicateGate_pos :
    warnAdjudicateGate (fun _ : Bool => false) (fun b => b) true = true := rfl

theorem warnAdjudicateGate_neg :
    warnAdjudicateGate (fun _ : Bool => false) (fun b => b) false = false := rfl

theorem exactAdjudicatorOnWarnings_pos :
    ExactAdjudicatorOnWarnings (fun b : Bool => b = true) (fun _ => false) (fun b => b) :=
  fun _ _ => Iff.rfl

theorem exactAdjudicatorOnWarnings_neg :
    ¬ ExactAdjudicatorOnWarnings (fun b : Bool => b = true) (fun _ => false) (fun _ => false) := by
  intro h; exact Bool.noConfusion ((h true rfl).2 rfl)

/-- Non-vacuity witness for `finite_suite_allowlist_barrier`. -/
theorem nonvacuity_finite_suite_barrier :
    let good : Nat → Prop := fun n => n % 2 = 0
    let c : Nat → Bool := fun n => n % 2 == 0
    let L : (Nat → Bool) → Prop := fun d => CheckerSound good d ∧ d 0 = true
    CheckerSound good c ∧
    SuiteSoundInvariant good [0] L ∧
    L c ∧
    (∃ p : Nat, p ∉ ([0] : List Nat) ∧ c p = true) := by
  intro good c L
  have hs : CheckerSound good c := fun n hn => by simpa [c, good] using hn
  refine ⟨hs, ?_, ⟨hs, rfl⟩, ⟨2, by decide, rfl⟩⟩
  intro c₁ c₂ hiff hF ⟨hs1, hc0⟩
  exact ⟨hiff.1 hs1, by rw [← hF 0 (List.mem_singleton.2 rfl)]; exact hc0⟩

/-- Complete unified non-vacuity witness for `extensional_law_admits_lookupWrapper`,
simultaneously instantiating `ImplExtensionalLaw`, `TableConsistentWith`, `L ⟨code₁, c⟩`,
and distinct representations `code₁ ≠ code₂`. -/
theorem nonvacuity_extensional_lookupWrapper :
    let L : ImplChecker Nat Bool → Prop := fun chk => CheckerSound (· = 0) chk.run ∧ chk.run 0 = true
    let c : Nat → Bool := fun n => n == 0
    let table : List (Nat × Bool) := [(0, true)]
    ImplExtensionalLaw L ∧
    TableConsistentWith table c ∧
    L ⟨true, c⟩ ∧
    (true ≠ false) ∧
    (⟨false, lookupWrapper table c⟩ : ImplChecker Nat Bool) ≠ ⟨true, c⟩ := by
  intro L c table
  have hext : ImplExtensionalLaw L := by
    intro c₁ c₂ heq ⟨hs, h0⟩
    refine ⟨fun x hx => hs x (by rw [heq x]; exact hx), by rw [← heq 0]; exact h0⟩
  have hcons : TableConsistentWith table c := tableConsistentWith_pos
  have hlaw : L ⟨true, c⟩ := ⟨fun n hn => by simpa [c] using hn, rfl⟩
  exact ⟨hext, hcons, hlaw, by decide,
    (extensional_law_admits_lookupWrapper L true false c table hext hcons hlaw).2 (by decide)⟩

/-- Exact-gate non-vacuity witness satisfying both sides of `zeroLockout_and_zeroFalseAccept_iff_exact`. -/
theorem nonvacuity_exact_blockingGate :
    let P : Nat → Prop := fun n => n = 0
    let Q : Nat → Bool := fun n => n == 0
    ZeroLockout P (blockingGate Q) ∧
    ZeroFalseAccept P (blockingGate Q) ∧
    (∀ x : Nat, Q x = true ↔ P x) := by
  intro P Q
  have hexact : ∀ x : Nat, Q x = true ↔ P x := fun x => by simp [Q, P]
  exact ⟨(zeroLockout_and_zeroFalseAccept_iff_exact P Q).2 hexact |>.1,
    (zeroLockout_and_zeroFalseAccept_iff_exact P Q).2 hexact |>.2, hexact⟩

/-- Non-vacuity witness for `blockingGate_locks_out_strict_proxy` and
`warnAdjudicateGate_zeroLockout_and_sound` on a strict proxy `Q` rejecting valid artifact `2`. -/
theorem nonvacuity_warnAdjudicate_strict_proxy :
    let P : Nat → Prop := fun n => n % 2 = 0
    let Q : Nat → Bool := fun n => n == 0
    let adj : Nat → Bool := fun n => n % 2 == 0
    P 2 ∧ Q 2 = false ∧
    ExactAdjudicatorOnWarnings P Q adj ∧
    ZeroFalseAccept P Q := by
  intro P Q adj
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro x _
    simp [adj, P]
  · intro x hx
    have h0 : x = 0 := by simpa [Q] using hx
    subst h0; rfl

end Toy.BoundaryLicensing
