import Toy.Progress.Slicing

/-!
# Mixing progress semantics across an inlined call

A *function* is a body together with a per-function progress attribute; compiling it
sets the progress flag of every loop in its body to the attribute (`Fn.code`). A call
site `pre ;; call g ;; post` in a caller with attribute `cm` is given its meaning by
`CallSite.linked`: the callee's loops keep the callee's attribute. Two inlining
strategies are compared against it:

* `inlineUnmarked` — the inlined body is governed by the caller's attribute, as if the
  attribute were a property of the merged function only;
* `inlineDroppingAttr` — the merged function keeps the attribute only if both functions
  had it.
-/

namespace Toy.Progress

/-- A function: a body and a per-function progress attribute. -/
structure Fn where
  body : Cmd
  mustProgress : Bool

/-- The compiled code of a function: every loop carries the function's attribute. -/
def Fn.code (f : Fn) : Cmd := f.body.markAll f.mustProgress

/-- A call site `pre ;; call g ;; post` inside a caller with attribute `mustProgress`. -/
structure CallSite where
  pre : Cmd
  post : Cmd
  mustProgress : Bool

/-- The meaning of the call site before inlining: the callee's code runs with the
callee's own attribute. -/
def CallSite.linked (cs : CallSite) (g : Fn) : Cmd :=
  .seq (cs.pre.markAll cs.mustProgress) (.seq g.code (cs.post.markAll cs.mustProgress))

/-- Inlining in which the caller's attribute governs every loop of the merged body,
including the callee's. -/
def CallSite.inlineUnmarked (cs : CallSite) (g : Fn) : Cmd :=
  (Cmd.seq cs.pre (.seq g.body cs.post)).markAll cs.mustProgress

/-- Inlining in which the merged function keeps the attribute only if both the caller
and the callee had it. -/
def CallSite.inlineDroppingAttr (cs : CallSite) (g : Fn) : Cmd :=
  (Cmd.seq cs.pre (.seq g.body cs.post)).markAll (cs.mustProgress && g.mustProgress)

/-- The hazard: a call site `skip ;; call g ;; emit 1` in a forward-progress caller. -/
def hazardSite : CallSite := { pre := .skip, post := .emit (.num 1), mustProgress := true }

/-- A divergence-observable callee whose body is `while 1 do skip`. -/
def spinFn : Fn := { body := spin false, mustProgress := false }

/-! ### Examples -/

/-- Positive example: the linked hazard program keeps the callee's loop unflagged. -/
theorem linked_hazard :
    hazardSite.linked spinFn = .seq .skip (.seq (spin false) (.emit (.num 1))) := by decide

/-- Positive example: unmarked inlining flags the callee's loop. -/
theorem inlineUnmarked_hazard :
    hazardSite.inlineUnmarked spinFn = .seq .skip (.seq (spin true) (.emit (.num 1))) := by
  decide

/-- Negative example: attribute-dropping inlining does not flag the callee's loop. -/
theorem inlineDroppingAttr_hazard :
    hazardSite.inlineDroppingAttr spinFn ≠ .seq .skip (.seq (spin true) (.emit (.num 1))) := by
  decide

/-- Positive example: when both functions have the attribute, attribute-dropping inlining
coincides with the linked program. -/
theorem inlineDroppingAttr_eq_linked_of_both (pre post body : Cmd) :
    ({ pre, post, mustProgress := true } : CallSite).inlineDroppingAttr
        { body, mustProgress := true } =
      ({ pre, post, mustProgress := true } : CallSite).linked { body, mustProgress := true } :=
  rfl

theorem progressViolation_seq_spin_true (k : Cmd) (s : State) :
    ProgressViolation (.seq .skip (.seq (spin true) k)) s :=
  ⟨1, .num 1, .skip, rfl, silentlyIterates_spin s⟩

theorem not_progressViolation_seq_spin_false (k : Cmd) (s : State) :
    ¬ ProgressViolation (.seq .skip (.seq (spin false) k)) s := by
  rintro ⟨n, b, body, hh, hsd⟩
  cases n with
  | zero => simp [run_zero, Cmd.head] at hh
  | succ n =>
    rw [run_succ_of_step (c' := .seq (spin false) k) (s' := s) (o := []) n rfl] at hh hsd
    exact not_progressViolation_spinSeq_false k s ⟨n, b, body, hh, hsd⟩

theorem obsBeh_seq_skip_spinSeq (k : Cmd) (s : State) (b : Beh) :
    ObsBeh (.seq .skip (.seq (spin false) k)) s b ↔ b = .div [] :=
  obsBeh_of_silent (silent_of_step (c := .seq .skip (.seq (spin false) k))
    (c' := .seq (spin false) k) (s := s) (s' := s) rfl (spinSeq_silent false k s)) b

/-! ## Flags do not affect execution -/

theorem markAll_eq_skip_iff (m : Bool) (c : Cmd) : c.markAll m = .skip ↔ c = .skip := by
  cases c <;> simp [Cmd.markAll]

theorem step_markAll (m : Bool) (c : Cmd) (s : State) :
    step (c.markAll m) s = (step c s).map (fun r => (r.1.markAll m, r.2.1, r.2.2)) := by
  induction c with
  | skip | assign _ _ | emit _ => rfl
  | ite b c₁ c₂ _ _ =>
    simp only [Cmd.markAll, step, Option.map]
    split <;> rfl
  | loop mp b body _ =>
    simp [Cmd.markAll, step]
  | seq c₁ c₂ ih₁ _ =>
    simp only [Cmd.markAll, step, ih₁]
    cases step c₁ s <;> simp [Option.map, Cmd.markAll]

theorem run_markAll (m : Bool) (n : Nat) (c : Cmd) (s : State) :
    run n (c.markAll m) s = ((run n c s).1.markAll m, (run n c s).2.1, (run n c s).2.2) := by
  induction n generalizing c s with
  | zero => rfl
  | succ n ih =>
    simp only [run, step_markAll]
    cases step c s with
    | none => rfl
    | some r =>
      obtain ⟨c1, s1, o⟩ := r
      simp [Option.map, ih]

theorem termsWith_markAll (m : Bool) {c : Cmd} {s s' : State} {t : List Val} :
    TermsWith (c.markAll m) s t s' ↔ TermsWith c s t s' := by
  constructor
  · rintro ⟨n, hn⟩
    rw [run_markAll] at hn
    simp only [Prod.mk.injEq, markAll_eq_skip_iff] at hn
    exact ⟨n, Prod.ext hn.1 (Prod.ext hn.2.1 hn.2.2)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [run_markAll, hn]; rfl⟩

/-- The divergence-observable semantics ignores loop flags. -/
theorem obsBeh_markAll (m : Bool) (c : Cmd) (s : State) (b : Beh) :
    ObsBeh (c.markAll m) s b ↔ ObsBeh c s b := by
  cases b with
  | term t => simp only [ObsBeh, termsWith_markAll]
  | div t =>
    simp only [ObsBeh, Diverges, traceAt, run_markAll, ne_eq, markAll_eq_skip_iff]
  | react f =>
    simp only [ObsBeh, traceAt, run_markAll]

theorem head_markAll (m : Bool) (c : Cmd) : (c.markAll m).head = c.head.markAll m := by
  induction c with
  | seq c₁ _ ih => exact ih
  | _ => rfl

theorem not_progressViolation_markAll_false (c : Cmd) (s : State) :
    ¬ ProgressViolation (c.markAll false) s := by
  rintro ⟨n, b, body, hh, -⟩
  rw [run_markAll, head_markAll] at hh
  cases h : (run n c s).1.head <;> rw [h] at hh <;> simp [Cmd.markAll] at hh

theorem markAll_idem (m₁ m₂ : Bool) (c : Cmd) : (c.markAll m₁).markAll m₂ = c.markAll m₂ := by
  induction c <;> simp [Cmd.markAll, *]

/-- A progress violation is a silent divergence, so every per-loop behaviour is a
forward-progress behaviour. -/
theorem fpBeh_of_mixedBeh {c : Cmd} {s : State} {b : Beh} (h : MixedBeh c s b) : FPBeh c s b :=
  h.elim (fun h => Or.inl (silentlyDiverges_of_progressViolation h)) Or.inr

/-! ## Result: the per-loop semantics restricts to the two global semantics -/

/-- **Flagging every loop gives the forward-progress semantics**: the per-loop semantics
of `c.markAll true` coincides with the thread-level forward-progress semantics of `c`. -/
theorem mixedBeh_markAll_true_iff_fpBeh (c : Cmd) (s : State) (b : Beh) :
    MixedBeh (c.markAll true) s b ↔ FPBeh c s b := by
  have hsd : SilentlyDiverges (c.markAll true) s ↔ SilentlyDiverges c s := by
    simp only [SilentlyDiverges, obsBeh_markAll]
  unfold MixedBeh FPBeh
  rw [obsBeh_markAll]
  constructor
  · rintro (h | h)
    · exact Or.inl (hsd.1 (silentlyDiverges_of_progressViolation h))
    · exact Or.inr h
  · rintro (h | h)
    · left
      obtain ⟨n, mp, b', body, hh, hsi⟩ := exists_head_silentlyIterates c s h
      refine ⟨n, b', body.markAll true, ?_, ?_⟩
      · rw [run_markAll, head_markAll, hh]; rfl
      · rw [run_markAll]
        obtain ⟨σ, o, h0, hit, hN⟩ := hsi
        exact ⟨σ, o, h0, fun i => ⟨(hit i).1, (termsWith_markAll true).2 (hit i).2⟩, hN⟩
    · exact Or.inr h

/-- **Flagging no loop gives the divergence-observable semantics.** -/
theorem mixedBeh_markAll_false_iff_obsBeh (c : Cmd) (s : State) (b : Beh) :
    MixedBeh (c.markAll false) s b ↔ ObsBeh c s b := by
  unfold MixedBeh
  rw [obsBeh_markAll]
  exact ⟨fun h => h.resolve_left (not_progressViolation_markAll_false c s), Or.inr⟩

/-- **The per-loop semantics restricts to both global semantics**: flagging every loop
gives the forward-progress semantics and flagging none gives the divergence-observable
semantics. -/
theorem mixedBeh_markAll_restricts (c : Cmd) (s : State) (b : Beh) :
    (MixedBeh (c.markAll true) s b ↔ FPBeh c s b) ∧
    (MixedBeh (c.markAll false) s b ↔ ObsBeh c s b) :=
  ⟨mixedBeh_markAll_true_iff_fpBeh c s b, mixedBeh_markAll_false_iff_obsBeh c s b⟩

/-- Non-vacuity for both restriction results: on `skip ;; while 1 do skip ;; emit 1`,
flagging every loop makes `term [42]` a behaviour (undefined behaviour), as does the
forward-progress semantics; flagging none leaves exactly `div []`, as does the
divergence-observable semantics. -/
theorem mixedBeh_markAll_nonvacuous (s : State) :
    (MixedBeh ((Cmd.seq .skip (.seq (spin false) (.emit (.num 1)))).markAll true) s
        (.term [42]) ∧
      FPBeh (.seq .skip (.seq (spin false) (.emit (.num 1)))) s (.term [42])) ∧
    (¬ MixedBeh ((Cmd.seq .skip (.seq (spin true) (.emit (.num 1)))).markAll false) s
        (.term [42]) ∧
      ¬ ObsBeh (.seq .skip (.seq (spin true) (.emit (.num 1)))) s (.term [42])) := by
  refine ⟨⟨Or.inl (progressViolation_seq_spin_true _ s), Or.inl ?_⟩, ?_, ?_⟩
  · exact ⟨[], (obsBeh_seq_skip_spinSeq _ s _).2 rfl⟩
  · rintro (h | h)
    · exact not_progressViolation_seq_spin_false _ s h
    · have := (obsBeh_seq_skip_spinSeq (.emit (.num 1)) s _).1 h; cases this
  · intro h
    have := (obsBeh_of_silent (silent_of_step (c := .seq .skip (.seq (spin true) (.emit (.num 1))))
      (c' := .seq (spin true) (.emit (.num 1))) (s := s) (s' := s) rfl
      (spinSeq_silent true _ s)) _).1 h
    cases this

/-! ## Result: unmarked inlining turns a defined program into undefined behaviour -/

/-- **Inlining a divergence-observable callee containing `while 1 do skip` into a
forward-progress caller without keeping the callee's loop unflagged is a
miscompilation**: the linked program `skip ;; call g ;; emit 1` is defined from every state
(it silently diverges), the unmarked inlining has a progress violation from every
state, so it is not a refinement; deleting the now-flagged loop afterwards refines the
inlined program but not the original. -/
theorem inlineUnmarked_divergenceObservableCallee_not_refines :
    (∀ s, ¬ ProgressViolation (hazardSite.linked spinFn) s ∧
          ProgressViolation (hazardSite.inlineUnmarked spinFn) s) ∧
    ¬ Refines MixedBeh (hazardSite.linked spinFn) (hazardSite.inlineUnmarked spinFn) ∧
    Refines MixedBeh (hazardSite.inlineUnmarked spinFn) (.seq .skip (.seq .skip (.emit (.num 1)))) ∧
    ¬ Refines MixedBeh (hazardSite.linked spinFn) (.seq .skip (.seq .skip (.emit (.num 1)))) := by
  rw [linked_hazard, inlineUnmarked_hazard]
  have hT : TermsWith (.seq .skip (.seq .skip (.emit (.num 1)))) (fun _ => 0) [1] (fun _ => 0) :=
    termsWith_seq (termsWith_skip _) (termsWith_seq (termsWith_skip _) (termsWith_emit _ _))
  have hNot : ¬ MixedBeh (.seq .skip (.seq (spin false) (.emit (.num 1)))) (fun _ => 0)
      (.term [1]) := by
    rintro (h | h)
    · exact not_progressViolation_seq_spin_false _ _ h
    · have := (obsBeh_seq_skip_spinSeq _ _ _).1 h; cases this
  refine ⟨fun s => ⟨not_progressViolation_seq_spin_false _ s,
    progressViolation_seq_spin_true _ s⟩, ?_, ?_, ?_⟩
  · intro h
    exact hNot (h _ _ (Or.inl (progressViolation_seq_spin_true _ _)))
  · exact fun s _ _ => Or.inl (progressViolation_seq_spin_true _ s)
  · intro h
    exact hNot (h _ _ (Or.inr ((obsBeh_of_termsWith hT _).2 rfl)))

/-- Positive control: attribute-dropping inlining of the same call is defined from every
state and refines the linked program. -/
theorem inlineDroppingAttr_hazard_defined :
    (∀ s, ¬ ProgressViolation (hazardSite.inlineDroppingAttr spinFn) s) ∧
    Refines MixedBeh (hazardSite.linked spinFn) (hazardSite.inlineDroppingAttr spinFn) := by
  have he : hazardSite.inlineDroppingAttr spinFn = hazardSite.linked spinFn := by decide
  rw [he, linked_hazard]
  exact ⟨fun s => not_progressViolation_seq_spin_false _ s, refines_refl _ _⟩

/-! ## Result: attribute-dropping inlining is sound -/

theorem linked_markAll_false (cs : CallSite) (g : Fn) :
    (cs.linked g).markAll false = cs.inlineDroppingAttr g ∨
      cs.inlineDroppingAttr g = cs.linked g := by
  rcases cs with ⟨pre, post, cm⟩
  rcases g with ⟨body, gm⟩
  cases cm <;> cases gm <;>
    simp [CallSite.linked, CallSite.inlineDroppingAttr, Fn.code, Cmd.markAll, markAll_idem]

/-- **Inlining that drops the progress attribute unless both functions have it is always
a refinement** of the linked program, for every top-level call site and callee. -/
theorem inlineDroppingAttr_refines_linked (cs : CallSite) (g : Fn) :
    Refines MixedBeh (cs.linked g) (cs.inlineDroppingAttr g) := by
  rcases linked_markAll_false cs g with hfalse | heq
  · intro s b hb
    rw [← hfalse, mixedBeh_markAll_false_iff_obsBeh] at hb
    exact Or.inr hb
  · rw [heq]; exact refines_refl _ _

/-- A forward-progress caller whose own code before the call is `while 1 do skip`. -/
def callerLoopSite : CallSite := { pre := spin false, post := .emit (.num 1), mustProgress := true }

/-- Non-vacuity in a case where attribute-dropping inlining changes loop flags: the caller's
own loop is flagged in the linked program (a progress violation from every state) and
unflagged after inlining (no progress violation), and the refinement holds. -/
theorem inlineDroppingAttr_callerLoop_nonvacuous :
    callerLoopSite.inlineDroppingAttr spinFn ≠ callerLoopSite.linked spinFn ∧
    (∀ s, ProgressViolation (callerLoopSite.linked spinFn) s) ∧
    (∀ s, ¬ ProgressViolation (callerLoopSite.inlineDroppingAttr spinFn) s) ∧
    Refines MixedBeh (callerLoopSite.linked spinFn) (callerLoopSite.inlineDroppingAttr spinFn) := by
  refine ⟨by decide, fun s => ⟨0, .num 1, .skip, rfl, silentlyIterates_spin s⟩,
    fun s => not_progressViolation_markAll_false _ s, inlineDroppingAttr_refines_linked _ _⟩

end Toy.Progress
