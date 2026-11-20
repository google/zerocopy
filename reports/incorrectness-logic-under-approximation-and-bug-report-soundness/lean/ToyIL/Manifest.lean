import ToyIL.Analyses

/-!
# Manifest errors and context extension

Le, Raad, Villard, Berdine, Dreyer and O'Hearn (OOPSLA 2022, Definition 3.2) call a valid
error triple `[p] C [er : q]` *manifest* when `∀ s. ∃ s'. (s, s') ∈ ⟦C⟧er ∧ s' ∈ q ∗ true`:
the error is reachable from *every* state, whatever the calling context. This toy has no
heap, so `q ∗ true` becomes `q` on the program's own state, and "extension of the state by
a frame" is modelled by product states `σ × τ` (`Cmd.liftFst`).

Two forms of context extension are studied:
* extending the state with an untouched frame component preserves (and, for a nonempty
  frame type, reflects) manifest errors (`manifestError_liftFst`, `manifestError_liftFst_iff`);
* placing the command into a one-hole program context: an error reachable from the state in
  which the context enters the hole is an error of the filled program with the same post
  (`error_in_context_of_err_at_hole`), so erring from every state is exactly the
  context-independent condition (`manifestReach_iff_forall_reaching_contexts`). This is a
  toy analogue of their Theorem 3.4 (a manifest error in a procedure of a complete program is
  either dead code or makes `main` err). The validity half of `ManifestError` is *not*
  preserved by contexts (`manifestError_not_preserved_by_context`).
-/

namespace Toy.IL

variable {σ : Type}

/-- From every initial state, some run of `c` errs in a `Q` state. -/
def ManifestReach (c : Cmd σ) (Q : Assn σ) : Prop := ∀ s, ∃ t, Q t ∧ Exec c s .er t

/-- Manifest error (toy rendering of Le et al. 2022, Definition 3.2): a valid IL error
triple `[P] c [er : Q]` whose post is reached erroneously from every initial state. -/
def ManifestError (P : Assn σ) (c : Cmd σ) (Q : Assn σ) : Prop :=
  IL P c .er Q ∧ ManifestReach c Q

/-- Positive example: `x := 0; error()` errs with `x = 0` from every state. -/
theorem manifestError_pos :
    ManifestError (fun _ : Nat => True) (.seq (.assign (fun _ => 0)) .error) (fun n => n = 0) := by
  refine ⟨?_, ?_⟩
  · rintro t rfl; exact ⟨0, trivial, .seqOk .assign .error⟩
  · intro s; exact ⟨0, rfl, .seqOk .assign .error⟩

/-- Negative example (a *latent* error): `[x = 7] assume (x = 7); error() [er : x = 7]` is
a valid IL triple, so the error is real for callers with `x = 7`, but it is not manifest:
from `x = 0` there is no error. -/
theorem latent_error_not_manifest :
    IL (fun n : Nat => n = 7) (.seq (.assume (fun n => n == 7)) .error) .er (fun n => n = 7) ∧
      ¬ ManifestError (fun n : Nat => n = 7) (.seq (.assume (fun n => n == 7)) .error)
        (fun n => n = 7) := by
  refine ⟨nonvacuity_il_true_positive.1, ?_⟩
  rintro ⟨_, h⟩
  obtain ⟨t, _, ht⟩ := h 0
  simp at ht

/-- `ManifestReach` alone is not a manifest error: `error()` errs from every state, but
`[x = 0] error() [er : True]` is not valid. -/
theorem manifestReach_not_manifestError :
    ManifestReach (.error : Cmd Nat) (fun _ => True) ∧
      ¬ ManifestError (fun n : Nat => n = 0) .error (fun _ => True) := by
  refine ⟨fun s => ⟨s, trivial, .error⟩, ?_⟩
  rintro ⟨h, _⟩
  obtain ⟨s, hs, hst⟩ := h 1 trivial
  simp at hst; omega

/-! ### Frame extension of the state -/

/-- Run `c` on the first component of a product state, leaving the second (the frame)
untouched. -/
def Cmd.liftFst {τ : Type} : Cmd σ → Cmd (σ × τ)
  | .assign f => .assign (fun p => (f p.1, p.2))
  | .assume b => .assume (fun p => b p.1)
  | .error => .error
  | .seq c₁ c₂ => .seq c₁.liftFst c₂.liftFst
  | .choice c₁ c₂ => .choice c₁.liftFst c₂.liftFst
  | .star c => .star c.liftFst

theorem exec_liftFst {τ : Type} {c : Cmd σ} {s t : σ} {e : Exit} (h : Exec c s e t) (r : τ) :
    Exec (c.liftFst (τ := τ)) (s, r) e (t, r) := by
  induction h with
  | assign => exact .assign
  | assume hb => exact .assume hb
  | error => exact .error
  | seqOk _ _ ih₁ ih₂ => exact .seqOk ih₁ ih₂
  | seqEr _ ih => exact .seqEr ih
  | choiceL _ ih => exact .choiceL ih
  | choiceR _ ih => exact .choiceR ih
  | starNil => exact .starNil
  | starOk _ _ ih₁ ih₂ => exact .starOk ih₁ ih₂
  | starEr _ ih => exact .starEr ih

/-- Manifest errors are preserved by extending the state with a frame component: if
`[P] c [er : Q]` is manifest, so is `[P × True] c↑ [er : Q × True]`. -/
theorem manifestError_liftFst {τ : Type} {P Q : Assn σ} {c : Cmd σ}
    (h : ManifestError P c Q) :
    ManifestError (fun p : σ × τ => P p.1) c.liftFst (fun p => Q p.1) := by
  obtain ⟨hil, hreach⟩ := h
  refine ⟨?_, ?_⟩
  · rintro ⟨t, r⟩ ht
    obtain ⟨s, hs, hst⟩ := hil t ht
    exact ⟨(s, r), hs, exec_liftFst hst r⟩
  · rintro ⟨s, r⟩
    obtain ⟨t, ht, hst⟩ := hreach s
    exact ⟨(t, r), ht, exec_liftFst hst r⟩

/-- The validity half of `ManifestError` is needed: with `ManifestReach` alone the lifted
triple is not valid. -/
theorem manifestError_liftFst_il_tight :
    ManifestReach (.error : Cmd Nat) (fun _ => True) ∧
      ¬ IL (fun n : Nat => n = 0) .error .er (fun _ => True) ∧
      ¬ ManifestError (fun p : Nat × Nat => p.1 = 0) (Cmd.error.liftFst) (fun _ => True) := by
  refine ⟨fun s => ⟨s, trivial, .error⟩, ?_, ?_⟩
  · intro h
    obtain ⟨s, hs, hst⟩ := h 1 trivial
    simp at hst; omega
  · rintro ⟨h, _⟩
    obtain ⟨s, hs, hst⟩ := h (1, 0) trivial
    simp [Cmd.liftFst] at hst
    subst hst
    simp at hs

/-- The every-state half of `ManifestError` is needed: a latent error stays latent after
frame extension, so the lifted triple is not a manifest error. -/
theorem manifestError_liftFst_reach_tight :
    IL (fun n : Nat => n = 7) (.seq (.assume (fun n => n == 7)) .error) .er (fun n => n = 7) ∧
      ¬ ManifestReach (.seq (.assume (fun n : Nat => n == 7)) .error) (fun n => n = 7) ∧
      ¬ ManifestError (fun p : Nat × Nat => p.1 = 7)
        ((Cmd.seq (.assume (fun n : Nat => n == 7)) .error).liftFst (τ := Nat))
        (fun p => p.1 = 7) := by
  refine ⟨nonvacuity_il_true_positive.1, ?_, ?_⟩
  · intro h
    obtain ⟨t, _, ht⟩ := h 0
    simp at ht
  · rintro ⟨_, h⟩
    obtain ⟨t, _, ht⟩ := h (0, 0)
    simp [Cmd.liftFst] at ht

/-- Non-vacuity of frame extension, with the frame type instantiated to `Nat`: the
hypothesis holds for `x := 0; error()` with pre `True` and post `x = 0`, and so does the
lifted conclusion. -/
theorem nonvacuity_manifestError_liftFst :
    ManifestError (fun _ : Nat => True) (.seq (.assign (fun _ => 0)) .error) (fun n => n = 0) ∧
      ManifestError (fun _ : Nat × Nat => True)
        ((Cmd.seq (.assign (fun _ : Nat => 0)) .error).liftFst (τ := Nat)) (fun p => p.1 = 0) :=
  ⟨manifestError_pos, manifestError_liftFst manifestError_pos⟩

/-- Exact semantics of `liftFst`: a run of `c.liftFst` from `(s, r)` is a run of `c` from
`s` that leaves the frame component `r` unchanged. -/
theorem exec_liftFst_iff {τ : Type} {c : Cmd σ} {s t : σ} {r r' : τ} {e : Exit} :
    Exec (c.liftFst (τ := τ)) (s, r) e (t, r') ↔ Exec c s e t ∧ r' = r := by
  constructor
  · intro h
    generalize hc : c.liftFst (τ := τ) = cl at h
    generalize hp₁ : (s, r) = p₁ at h
    generalize hp₂ : (t, r') = p₂ at h
    induction h generalizing c s r t r' with
    | assign =>
      cases c <;> simp [Cmd.liftFst] at hc
      subst hc; cases hp₁; cases hp₂; exact ⟨.assign, rfl⟩
    | assume hb =>
      cases c <;> simp [Cmd.liftFst] at hc
      subst hc; cases hp₁; cases hp₂; exact ⟨.assume hb, rfl⟩
    | error =>
      cases c <;> simp [Cmd.liftFst] at hc
      cases hp₁; cases hp₂; exact ⟨.error, rfl⟩
    | @seqOk _ _ _ m _ _ _ _ ih₁ ih₂ =>
      cases c <;> simp [Cmd.liftFst] at hc
      obtain ⟨hc₁, hc₂⟩ := hc
      rcases m with ⟨ms, mr⟩
      obtain ⟨hm₁, rfl⟩ := ih₁ hc₁ hp₁ rfl
      obtain ⟨hm₂, rfl⟩ := ih₂ hc₂ rfl hp₂
      exact ⟨.seqOk hm₁ hm₂, rfl⟩
    | seqEr _ ih =>
      cases c <;> simp [Cmd.liftFst] at hc
      obtain ⟨hc₁, _⟩ := hc
      obtain ⟨h₁, rfl⟩ := ih hc₁ hp₁ hp₂
      exact ⟨.seqEr h₁, rfl⟩
    | choiceL _ ih =>
      cases c <;> simp [Cmd.liftFst] at hc
      obtain ⟨hc₁, _⟩ := hc
      obtain ⟨h₁, rfl⟩ := ih hc₁ hp₁ hp₂
      exact ⟨.choiceL h₁, rfl⟩
    | choiceR _ ih =>
      cases c <;> simp [Cmd.liftFst] at hc
      obtain ⟨_, hc₂⟩ := hc
      obtain ⟨h₂, rfl⟩ := ih hc₂ hp₁ hp₂
      exact ⟨.choiceR h₂, rfl⟩
    | starNil =>
      cases c <;> simp [Cmd.liftFst] at hc
      cases hp₁; cases hp₂; exact ⟨.starNil, rfl⟩
    | @starOk _ _ m _ _ _ _ ih₁ ih₂ =>
      cases c <;> simp [Cmd.liftFst] at hc
      rcases m with ⟨ms, mr⟩
      obtain ⟨h₁, rfl⟩ := ih₁ hc hp₁ rfl
      obtain ⟨h₂, rfl⟩ := ih₂ (c := .star _) (congrArg Cmd.star hc) rfl hp₂
      exact ⟨.starOk h₁ h₂, rfl⟩
    | starEr _ ih =>
      cases c <;> simp [Cmd.liftFst] at hc
      obtain ⟨h₁, rfl⟩ := ih hc hp₁ hp₂
      exact ⟨.starEr h₁, rfl⟩
  · rintro ⟨h, rfl⟩
    exact exec_liftFst h _

/-- For a nonempty frame type, frame extension both preserves and reflects manifest
errors. -/
theorem manifestError_liftFst_iff {τ : Type} (r₀ : τ) {P Q : Assn σ} {c : Cmd σ} :
    ManifestError (fun p : σ × τ => P p.1) (c.liftFst (τ := τ)) (fun p => Q p.1) ↔
      ManifestError P c Q := by
  constructor
  · rintro ⟨hil, hreach⟩
    refine ⟨?_, ?_⟩
    · intro t ht
      obtain ⟨⟨s, r⟩, hs, hst⟩ := hil (t, r₀) ht
      exact ⟨s, hs, (exec_liftFst_iff.1 hst).1⟩
    · intro s
      obtain ⟨⟨t, r⟩, ht, hst⟩ := hreach (s, r₀)
      exact ⟨t, ht, (exec_liftFst_iff.1 hst).1⟩
  · exact manifestError_liftFst

/-- The frame element `r₀ : τ` is needed for reflection: over the empty frame type the
lifted triple is vacuously a manifest error even when the original is not. -/
theorem manifestError_liftFst_iff_frame_tight :
    ¬ (ManifestError (fun _ : Nat × Empty => True) (Cmd.skip.liftFst (τ := Empty)) (fun _ => True) ↔
      ManifestError (fun _ : Nat => True) Cmd.skip (fun _ => True)) := by
  intro h
  obtain ⟨_, hr⟩ := h.1 ⟨fun p => p.2.elim, fun p => p.2.elim⟩
  obtain ⟨_, _, hex⟩ := hr 0
  simp at hex

/-- Non-vacuity of the reflection theorem: both sides hold for `x := 0; error()` with frame
type `Nat`. -/
theorem nonvacuity_manifestError_liftFst_iff :
    ManifestError (fun _ : Nat × Nat => True)
        ((Cmd.seq (.assign (fun _ : Nat => 0)) .error).liftFst (τ := Nat)) (fun p => p.1 = 0) ∧
      ManifestError (fun _ : Nat => True) (.seq (.assign (fun _ => 0)) .error) (fun n => n = 0) :=
  ⟨nonvacuity_manifestError_liftFst.2, manifestError_pos⟩

/-- A manifest error need not have pre `True`: `[x = 99] x := 0; error() [er : x = 0]` is a
manifest error. -/
theorem manifestError_pre_need_not_be_true :
    ManifestError (fun n : Nat => n = 99) (.seq (.assign (fun _ => 0)) .error) (fun n => n = 0) :=
  ⟨fun _ ht => ht ▸ ⟨99, rfl, .seqOk .assign .error⟩, manifestError_pos.2⟩

/-! ### Program contexts -/

/-- Program contexts with one hole. -/
inductive Ctx (σ : Type) where
  | hole
  | seqL (K : Ctx σ) (c₂ : Cmd σ)
  | seqR (c₁ : Cmd σ) (K : Ctx σ)
  | choiceL (K : Ctx σ) (c₂ : Cmd σ)
  | choiceR (c₁ : Cmd σ) (K : Ctx σ)
  | star (K : Ctx σ)

/-- Plug a command into the hole. -/
def Ctx.fill : Ctx σ → Cmd σ → Cmd σ
  | .hole, c => c
  | .seqL K c₂, c => .seq (K.fill c) c₂
  | .seqR c₁ K, c => .seq c₁ (K.fill c)
  | .choiceL K c₂, c => .choice (K.fill c) c₂
  | .choiceR c₁ K, c => .choice c₁ (K.fill c)
  | .star K, c => .star (K.fill c)

/-- `Reaches c K s u`: running `K[c]` from `s` can arrive at the hole in state `u`
(i.e. the hole is not dead code from `s`). Only loop contexts depend on `c`, because
earlier iterations run the filled body. -/
inductive Reaches (c : Cmd σ) : Ctx σ → σ → σ → Prop where
  | hole {s : σ} : Reaches c .hole s s
  | seqL {K : Ctx σ} {c₂ : Cmd σ} {s u : σ} : Reaches c K s u → Reaches c (.seqL K c₂) s u
  | seqR {c₁ : Cmd σ} {K : Ctx σ} {s m u : σ} :
      Exec c₁ s .ok m → Reaches c K m u → Reaches c (.seqR c₁ K) s u
  | choiceL {K : Ctx σ} {c₂ : Cmd σ} {s u : σ} : Reaches c K s u → Reaches c (.choiceL K c₂) s u
  | choiceR {c₁ : Cmd σ} {K : Ctx σ} {s u : σ} : Reaches c K s u → Reaches c (.choiceR c₁ K) s u
  | star {K : Ctx σ} {s m u : σ} :
      Exec (.star (K.fill c)) s .ok m → Reaches c K m u → Reaches c (.star K) s u

/-- Positive example: `x := x + 1; [·]; skip` reaches its hole from `0` in state `1`. -/
theorem reaches_pos :
    Reaches (.error : Cmd Nat) (.seqR (.assign Nat.succ) (.seqL .hole Cmd.skip)) 0 1 :=
  .seqR .assign (.seqL .hole)

/-- Negative example: behind `assume false` the hole is dead code. -/
theorem reaches_neg (c : Cmd Nat) (s u : Nat) :
    ¬ Reaches c (.seqR (.assume (fun _ => false)) .hole) s u := by
  intro h
  cases h with
  | seqR h₁ _ => simp at h₁

/-- If running `K[c]` from `s` can arrive at the hole in state `u`, and `c` can err from `u`
into `Q`, then `K[c]` can err from `s` into `Q`: an error short-circuits the rest of the
program, so the error state is unchanged. -/
theorem error_in_context_of_err_at_hole {c : Cmd σ} {Q : Assn σ} {K : Ctx σ} {s u : σ}
    (hu : ∃ t, Q t ∧ Exec c u .er t) (hr : Reaches c K s u) :
    ∃ t, Q t ∧ Exec (K.fill c) s .er t := by
  induction hr with
  | hole => exact hu
  | seqL _ ih => obtain ⟨t, ht, h⟩ := ih hu; exact ⟨t, ht, .seqEr h⟩
  | seqR h₁ _ ih => obtain ⟨t, ht, h⟩ := ih hu; exact ⟨t, ht, .seqOk h₁ h⟩
  | choiceL _ ih => obtain ⟨t, ht, h⟩ := ih hu; exact ⟨t, ht, .choiceL h⟩
  | choiceR _ ih => obtain ⟨t, ht, h⟩ := ih hu; exact ⟨t, ht, .choiceR h⟩
  | star h₁ _ ih => obtain ⟨t, ht, h⟩ := ih hu; exact ⟨t, ht, exec_star_snoc h₁ h⟩

/-- A command that can err into `Q` from every state can err into `Q` inside every
context, from every state from which the context reaches the hole. -/
theorem error_in_context_of_manifestReach {c : Cmd σ} {Q : Assn σ} {K : Ctx σ} {s u : σ}
    (hm : ManifestReach c Q) (hr : Reaches c K s u) : ∃ t, Q t ∧ Exec (K.fill c) s .er t :=
  error_in_context_of_err_at_hole (hm u) hr

/-- Exact characterization: `c` can err into `Q` from every state iff, for every one-hole
context `K` and all states `s u` with `Reaches c K s u`, `K[c]` can err into `Q` from `s`.
(`←`: take the empty context.) -/
theorem manifestReach_iff_forall_reaching_contexts {c : Cmd σ} {Q : Assn σ} :
    ManifestReach c Q ↔
      ∀ (K : Ctx σ) (s u : σ), Reaches c K s u → ∃ t, Q t ∧ Exec (K.fill c) s .er t :=
  ⟨fun hm _ _ _ hr => error_in_context_of_manifestReach hm hr, fun h s => h .hole s s .hole⟩

/-- Corollary: if the context reaches its hole from every initial state, the filled program
again errs into `Q` from every initial state. -/
theorem manifestReach_fill_of_reaches_from_every_state {c : Cmd σ} {Q : Assn σ} {K : Ctx σ}
    (hm : ManifestReach c Q) (hr : ∀ s, ∃ u, Reaches c K s u) : ManifestReach (K.fill c) Q := by
  intro s
  obtain ⟨u, hu⟩ := hr s
  exact error_in_context_of_manifestReach hm hu

/-- Hypothesis `hu` of `error_in_context_of_err_at_hole` is needed: `assume (x = 7); error()`
has no erroneous run from `0`, the context `x := 0; [·]` reaches its hole from `5` in state
`0`, and the filled program has no erroneous run from `5`. (The context avoids the error
although every state satisfies the valid pre `True` of `[True] c [er : x = 7]`.) -/
theorem error_in_context_err_at_hole_tight :
    let c : Cmd Nat := .seq (.assume (fun n => n == 7)) .error
    let K : Ctx Nat := .seqR (.assign (fun _ => 0)) .hole
    (¬ ∃ t, (fun n : Nat => n = 7) t ∧ Exec c 0 .er t) ∧ Reaches c K 5 0 ∧
      ¬ ∃ t, (fun n : Nat => n = 7) t ∧ Exec (K.fill c) 5 .er t := by
  refine ⟨?_, .seqR .assign .hole, ?_⟩
  · rintro ⟨t, _, ht⟩
    simp at ht
  · rintro ⟨t, _, ht⟩
    simp [Ctx.fill] at ht

/-- Hypothesis `hr` of `error_in_context_of_err_at_hole` is needed: `error()` errs from `0`,
but behind `assume false` the hole is dead code and the filled program has no error. -/
theorem error_in_context_reaches_tight :
    let K : Ctx Nat := .seqR (.assume (fun _ => false)) .hole
    (∃ t, (fun _ : Nat => True) t ∧ Exec (.error : Cmd Nat) 0 .er t) ∧
      ¬ Reaches (.error : Cmd Nat) K 0 0 ∧
      ¬ ∃ t, (fun _ : Nat => True) t ∧ Exec (K.fill .error) 0 .er t := by
  refine ⟨⟨0, trivial, .error⟩, reaches_neg _ 0 0, ?_⟩
  rintro ⟨t, _, ht⟩
  simp [Ctx.fill] at ht

/-- Non-vacuity of `error_in_context_of_err_at_hole` and of the characterization: for
`c = x := 0; error()` (which errs into `x = 0` from every state) inside
`x := x + 1; (skip + [·])⋆`, the context reaches its hole from `0` in state `1` after one
complete loop iteration, and the filled program errs into `x = 0` from `0`. -/
theorem nonvacuity_error_in_context :
    let c : Cmd Nat := .seq (.assign (fun _ => 0)) .error
    let K : Ctx Nat := .seqR (.assign Nat.succ) (.star (.choiceR Cmd.skip .hole))
    (∃ t, (fun n : Nat => n = 0) t ∧ Exec c 1 .er t) ∧ ManifestReach c (fun n => n = 0) ∧
      Reaches c K 0 1 ∧ ∃ t, (fun n : Nat => n = 0) t ∧ Exec (K.fill c) 0 .er t := by
  have hr : Reaches (.seq (.assign (fun _ => 0)) .error : Cmd Nat)
      (.seqR (.assign Nat.succ) (.star (.choiceR Cmd.skip .hole))) 0 1 :=
    .seqR .assign (.star (.starOk (.choiceL (.assume rfl)) .starNil) (.choiceR .hole))
  exact ⟨manifestError_pos.2 1, manifestError_pos.2, hr,
    error_in_context_of_err_at_hole (manifestError_pos.2 1) hr⟩

/-- Hypothesis `hm` of `manifestReach_fill_of_reaches_from_every_state` is needed: the
context `x := 0; [·]` reaches its hole from every state, but the latent error of
`assume (x = 7); error()` is then never triggered. -/
theorem manifestReach_fill_manifest_tight :
    let c : Cmd Nat := .seq (.assume (fun n => n == 7)) .error
    let K : Ctx Nat := .seqR (.assign (fun _ => 0)) .hole
    ¬ ManifestReach c (fun n => n = 7) ∧ (∀ s, ∃ u, Reaches c K s u) ∧
      ¬ ManifestReach (K.fill c) (fun n => n = 7) := by
  refine ⟨?_, fun _ => ⟨0, .seqR .assign .hole⟩, ?_⟩
  · intro h
    obtain ⟨t, _, ht⟩ := h 0
    simp at ht
  · intro h
    obtain ⟨t, _, ht⟩ := h 5
    simp [Ctx.fill] at ht

/-- Hypothesis `hr` of `manifestReach_fill_of_reaches_from_every_state` is needed (reaching
the hole from *some* state is not enough): `assume (x = 0); [·]` reaches its hole from `0`
only, and `assume (x = 0); error()` does not err from `1`. -/
theorem manifestReach_fill_every_state_tight :
    let K : Ctx Nat := .seqR (.assume (fun n => n == 0)) .hole
    ManifestReach (.error : Cmd Nat) (fun _ => True) ∧
      (∃ s u, Reaches (.error : Cmd Nat) K s u) ∧
      ¬ (∀ s, ∃ u, Reaches (.error : Cmd Nat) K s u) ∧
      ¬ ManifestReach (K.fill .error) (fun _ => True) := by
  refine ⟨fun s => ⟨s, trivial, .error⟩, ⟨0, 0, .seqR (.assume rfl) .hole⟩, ?_, ?_⟩
  · intro h
    obtain ⟨u, hu⟩ := h 1
    cases hu with
    | seqR h₁ _ => simp at h₁
  · intro h
    obtain ⟨t, _, ht⟩ := h 1
    simp [Ctx.fill] at ht

/-- Non-vacuity of `manifestReach_fill_of_reaches_from_every_state`. -/
theorem nonvacuity_manifestReach_fill :
    let c : Cmd Nat := .seq (.assign (fun _ => 0)) .error
    let K : Ctx Nat := .seqR (.assign Nat.succ) (.star (.choiceR Cmd.skip .hole))
    ManifestReach c (fun n => n = 0) ∧ (∀ s, ∃ u, Reaches c K s u) ∧
      ManifestReach (K.fill c) (fun n => n = 0) := by
  have hr : ∀ s, ∃ u, Reaches (.seq (.assign (fun _ => 0)) .error : Cmd Nat)
      (.seqR (.assign Nat.succ) (.star (.choiceR Cmd.skip .hole))) s u :=
    fun s => ⟨s + 1, .seqR .assign (.star .starNil (.choiceR .hole))⟩
  exact ⟨manifestError_pos.2, hr, manifestReach_fill_of_reaches_from_every_state
    manifestError_pos.2 hr⟩

/-- `ManifestError` itself (with its validity half) is not preserved by contexts, even by
contexts that reach the hole from every state: here `ManifestError P c Q` holds, but after
`x := 2` the post state `0` of `Q` is unreachable, so `K[c]` is a manifest error for no
pre. -/
theorem manifestError_not_preserved_by_context :
    let c : Cmd Nat := .choice (.seq (.assume (fun n => n == 0)) .error)
                               (.seq (.assign (fun _ => 1)) .error)
    let P : Assn Nat := fun n => n = 0
    let Q : Assn Nat := fun n => n = 0 ∨ n = 1
    let K : Ctx Nat := .seqR (.assign (fun _ => 2)) .hole
    ManifestError P c Q ∧ (∀ s, ∃ u, Reaches c K s u) ∧
      (∀ P' : Assn Nat, ¬ ManifestError P' (K.fill c) Q) := by
  refine ⟨⟨?_, ?_⟩, fun _ => ⟨2, .seqR .assign .hole⟩, ?_⟩
  · rintro t (rfl | rfl)
    · exact ⟨0, rfl, .choiceL (.seqOk (.assume rfl) .error)⟩
    · exact ⟨0, rfl, .choiceR (.seqOk .assign .error)⟩
  · intro s
    exact ⟨1, Or.inr rfl, .choiceR (.seqOk .assign .error)⟩
  · intro P' ⟨hil, _⟩
    obtain ⟨s, _, hst⟩ := hil 0 (Or.inl rfl)
    simp [Ctx.fill] at hst

/-- A latent error is triggered by a context that enters the hole in a triggering state:
`assume (x = 7); error()` errs from no state other than `7`, but `x := 7; [·]` makes it err
from `5`. -/
theorem latent_error_triggered_by_context :
    let c : Cmd Nat := .seq (.assume (fun n => n == 7)) .error
    let K : Ctx Nat := .seqR (.assign (fun _ => 7)) .hole
    ¬ ManifestReach c (fun n => n = 7) ∧ Reaches c K 5 7 ∧
      ∃ t, (fun n : Nat => n = 7) t ∧ Exec (K.fill c) 5 .er t := by
  refine ⟨?_, .seqR .assign .hole, ?_⟩
  · intro h
    obtain ⟨t, _, ht⟩ := h 0
    simp at ht
  · exact error_in_context_of_err_at_hole ⟨7, rfl, .seqOk (.assume rfl) .error⟩
      (.seqR .assign .hole)

end Toy.IL
