import ToyUnwindCap.Chain

/-!
# Mixed-backend results (call-chain model)
-/

namespace Toy.UnwindCap

/-! ## Normal returns -/

/-- **Normal returns across mixed backends.** Let `A` be a lawful ABI (`A.Lawful`). If the
innermost callee's backend `b0` and the backend of every frame in `frs` conform to `A`, then the
compiled result of the chain equals its specified result: `compRet b0 frs v = specRet frs v`
for every value `v`. -/
theorem compRet_eq_specRet_of_conforms (A : AbiCodec) (hA : A.Lawful) (b0 : AbiCodec)
    (frs : List RetFrame) (v : Nat) (h0 : Conforms b0 A)
    (hfrs : ∀ fr ∈ frs, Conforms fr.backend A) : compRet b0 frs v = specRet frs v := by
  induction frs generalizing b0 v with
  | nil => rfl
  | cons fr rest ih =>
    have hfr := hfrs fr List.mem_cons_self
    simp only [compRet, specRet]
    rw [hfr.2, h0.1, hA]
    exact ih fr.backend (fr.k v) hfr (fun f hf => hfrs f (List.mem_cons_of_mem _ hf))

/-! ## Unwinding: auxiliary lemmas -/

/-- Every event of an unwind started at position `i` is tagged with a position `≥ i`, and so
is every catching frame. -/
theorem unwindWith_frame_ge (actOf : UFrame → Action) :
    ∀ (c : List UFrame) (i : Nat), (∀ e ∈ (unwindWith actOf i c).1, i ≤ e.frame) ∧
      (∀ k, (unwindWith actOf i c).2 = .caught k → i ≤ k) := by
  intro c
  induction c with
  | nil => intro i; simp [unwindWith]
  | cons fr rest ih =>
    intro i
    have ih' := ih (i + 1)
    simp only [unwindWith]
    split
    · exact ⟨fun e he => Nat.le_of_succ_le (ih'.1 e he),
        fun k hk => Nat.le_of_succ_le (ih'.2 k hk)⟩
    · refine ⟨fun e he => ?_, fun k hk => Nat.le_of_succ_le (ih'.2 k hk)⟩
      rcases List.mem_append.1 he with he | he
      · obtain ⟨x, _, rfl⟩ := List.mem_map.1 he
        exact Nat.le_refl _
      · exact Nat.le_of_succ_le (ih'.1 e he)
    · refine ⟨fun e he => ?_, fun k hk => ?_⟩
      · simp only [List.mem_singleton] at he; subst he; exact Nat.le_refl _
      · simp only [UOut.caught.injEq] at hk; subst hk; exact Nat.le_refl _
    · exact ⟨fun e he => by simp at he, fun k hk => by simp at hk⟩

theorem sameShape_refl : ∀ c : List UFrame, SameShape c c
  | [] => trivial
  | _ :: rest => ⟨rfl, fun _ => rfl, sameShape_refl rest⟩

/-- Let no frame of `c` reached by the specified unwind be a `pads = none` frame with a terminate
pad (`NoReachedNoneTerminate c`). Then the compiled and specified unwinds agree from position `i`
exactly when `ObligationsFull c`. -/
theorem unwindWith_effAct_eq_iff (c : List UFrame) (hterm : NoReachedNoneTerminate c) (i : Nat) :
    unwindWith UFrame.effAct i c = unwindWith UFrame.act i c ↔ ObligationsFull c := by
  induction c generalizing i with
  | nil => simp [unwindWith, ObligationsFull]
  | cons fr rest ih =>
    obtain ⟨hfr, hrest⟩ := hterm
    obtain ⟨pd, a⟩ := fr
    cases pd with
    | full =>
      cases a with
      | none =>
        simp only [unwindWith, UFrame.effAct, ObligationsFull, Action.obligation, Action.Stops]
        simpa using ih (hrest rfl) (i + 1)
      | cleanup ds =>
        simp only [unwindWith, UFrame.effAct, ObligationsFull, Action.Stops]
        rw [Prod.ext_iff]
        simp only [List.append_cancel_left_eq]
        rw [← Prod.ext_iff, ih (hrest rfl) (i + 1)]
        simp
      | catchPad => simp [unwindWith, UFrame.effAct, ObligationsFull, Action.Stops]
      | terminate => simp [unwindWith, UFrame.effAct, ObligationsFull, Action.Stops]
    | none =>
      cases a with
      | none =>
        simp only [unwindWith, UFrame.effAct, ObligationsFull, Action.obligation, Action.Stops]
        simpa using ih (hrest rfl) (i + 1)
      | cleanup ds =>
        cases ds with
        | nil =>
          simp only [unwindWith, UFrame.effAct, ObligationsFull, Action.obligation, Action.Stops,
            List.map_nil, List.nil_append]
          simpa using ih (hrest rfl) (i + 1)
        | cons x xs =>
          simp only [ObligationsFull, Action.obligation, List.isEmpty_cons, Bool.not_false,
            forall_const]
          refine ⟨fun heq => ?_, fun h => absurd h.1 (by simp)⟩
          have hb := (unwindWith_frame_ge UFrame.effAct rest (i + 1)).1 (UEvent.drop i x)
          have h1 : (unwindWith UFrame.effAct i (⟨.none, .cleanup (x :: xs)⟩ :: rest)).1 =
              (unwindWith UFrame.act i (⟨.none, .cleanup (x :: xs)⟩ :: rest)).1 := by rw [heq]
          simp only [unwindWith, UFrame.effAct, List.map_cons, List.cons_append] at h1
          rw [h1] at hb
          exact absurd (hb List.mem_cons_self) (by simp [UEvent.frame])
      | catchPad =>
        simp only [ObligationsFull, Action.obligation, forall_const]
        refine ⟨fun heq => ?_, fun h => absurd h.1 (by simp)⟩
        have hb := (unwindWith_frame_ge UFrame.effAct rest (i + 1)).2 i
        have h2 : (unwindWith UFrame.effAct i (⟨.none, .catchPad⟩ :: rest)).2 =
            (unwindWith UFrame.act i (⟨.none, .catchPad⟩ :: rest)).2 := by rw [heq]
        simp only [unwindWith, UFrame.effAct] at h2
        exact absurd (hb h2) (by omega)
      | terminate => exact absurd rfl (hfr rfl)

/-- If `ObligationsFull c`, the compiled and specified unwinds agree from every position `i`
(no further hypothesis). -/
theorem unwindWith_effAct_eq_of_obligationsFull :
    ∀ (c : List UFrame) (i : Nat), ObligationsFull c →
      unwindWith UFrame.effAct i c = unwindWith UFrame.act i c
  | [], _, _ => rfl
  | ⟨pd, a⟩ :: rest, i, ⟨hobl, hrest⟩ => by
    cases pd with
    | full =>
      cases a with
      | none =>
        simpa [unwindWith, UFrame.effAct] using
          unwindWith_effAct_eq_of_obligationsFull rest (i + 1) (hrest rfl)
      | cleanup ds =>
        simp only [unwindWith, UFrame.effAct]
        rw [unwindWith_effAct_eq_of_obligationsFull rest (i + 1) (hrest rfl)]
      | catchPad => rfl
      | terminate => rfl
    | none =>
      cases a with
      | none =>
        simpa [unwindWith, UFrame.effAct] using
          unwindWith_effAct_eq_of_obligationsFull rest (i + 1) (hrest rfl)
      | cleanup ds =>
        cases ds with
        | nil =>
          simpa [unwindWith, UFrame.effAct] using
            unwindWith_effAct_eq_of_obligationsFull rest (i + 1) (hrest rfl)
        | cons x xs => exact absurd (hobl rfl) (by simp)
      | catchPad => exact absurd (hobl rfl) (by simp)
      | terminate => exact absurd (hobl rfl) (by simp)

/-- Robust agreement from position `i` (for every chain of the same shape) holds exactly for
`Shielded` chains. -/
theorem robust_at_iff_shielded (c : List UFrame) (i : Nat) :
    (∀ c', SameShape c c' → unwindWith UFrame.effAct i c' = unwindWith UFrame.act i c') ↔
      Shielded c := by
  induction c generalizing i with
  | nil =>
    constructor
    · intro _; trivial
    · intro _ c' hs
      cases c' with
      | nil => rfl
      | cons _ _ => exact absurd hs (by simp [SameShape])
  | cons fr rest ih =>
    obtain ⟨pd, a⟩ := fr
    constructor
    · intro h
      cases pd with
      | none =>
        exfalso
        have h1 := h (⟨.none, .catchPad⟩ :: rest)
          ⟨rfl, ⟨(by intro hx; cases hx), sameShape_refl rest⟩⟩
        have h2 := congrArg Prod.snd h1
        simp only [unwindWith, UFrame.effAct] at h2
        have hb := (unwindWith_frame_ge UFrame.effAct rest (i + 1)).2 i h2
        omega
      | full =>
        refine ⟨rfl, ?_⟩
        cases hst : a.Stops
        · right
          apply (ih (i + 1)).1
          intro c'' hs''
          have h1 := h (⟨.full, a⟩ :: c'') ⟨rfl, ⟨fun _ => rfl, hs''⟩⟩
          cases a with
          | none => simpa [unwindWith, UFrame.effAct] using h1
          | cleanup ds =>
            simp only [unwindWith, UFrame.effAct] at h1
            rw [Prod.ext_iff] at h1
            simp only [List.append_cancel_left_eq] at h1
            exact Prod.ext h1.1 h1.2
          | catchPad => simp [Action.Stops] at hst
          | terminate => simp [Action.Stops] at hst
        · exact Or.inl rfl
    · intro hsh c' hs
      obtain ⟨hpd, hrest⟩ := hsh
      simp only at hpd
      subst hpd
      cases c' with
      | nil => exact absurd hs (by simp [SameShape])
      | cons b bs =>
        obtain ⟨hbp, hba, hss⟩ := hs
        have hb : b = ⟨.full, a⟩ := by
          obtain ⟨bp, ba⟩ := b
          simp only at hbp hba
          subst hbp
          rw [hba (by simp)]
        subst hb
        rcases hrest with hst | hsr
        · cases a with
          | catchPad => rfl
          | terminate => rfl
          | none => simp [Action.Stops] at hst
          | cleanup _ => simp [Action.Stops] at hst
        · have ihr := (ih (i + 1)).2 hsr bs hss
          cases a with
          | none => simpa [unwindWith, UFrame.effAct] using ihr
          | cleanup ds => simp only [unwindWith, UFrame.effAct]; rw [ihr]
          | catchPad => rfl
          | terminate => rfl

/-! ## Unwinding: main results -/

/-- **Drops and catches behave as specified iff every reached frame with an obligation has
landing pads.** For every chain `c` in which no frame reached by the specified unwind is a
`pads = none` frame with a terminate pad (`NoReachedNoneTerminate c`):
`compUnwind c = specUnwind c` iff `ObligationsFull c`, i.e. every frame that the specified
unwind reaches (up to and including the first frame whose action stops it) and that has a
non-empty cleanup pad, a catch pad or a terminate pad was compiled with `pads = full`. -/
theorem compUnwind_eq_specUnwind_iff_obligationsFull_of_noReachedNoneTerminate (c : List UFrame)
    (hterm : NoReachedNoneTerminate c) :
    compUnwind c = specUnwind c ↔ ObligationsFull c :=
  unwindWith_effAct_eq_iff c hterm 0

/-- **Sufficiency without side condition.** For every chain `c` with `ObligationsFull c`, the
compiled and specified unwinds agree. -/
theorem compUnwind_eq_specUnwind_of_obligationsFull (c : List UFrame) (h : ObligationsFull c) :
    compUnwind c = specUnwind c :=
  unwindWith_effAct_eq_of_obligationsFull c 0 h

/-- **Robust agreement iff shielded.** For every chain `c`: the compiled and specified unwinds
agree on every chain `c'` with `SameShape c c'` (same backends frame by frame, same actions at
every `pads = full` frame, any actions at `pads = none` frames) iff `Shielded c`, i.e. scanning
from the innermost frame, every frame is compiled with `pads = full` up to and including the first
frame whose action stops the unwind (`catchPad` or `terminate`), or up to the end of the chain if
no frame stops it. -/
theorem robust_iff_shielded (c : List UFrame) :
    (∀ c', SameShape c c' → compUnwind c' = specUnwind c') ↔ Shielded c :=
  robust_at_iff_shielded c 0

/-- `TerminateShielded` implies `Shielded`. -/
theorem shielded_of_terminateShielded : ∀ c : List UFrame, TerminateShielded c → Shielded c
  | [], _ => trivial
  | fr :: rest, ⟨hp, h⟩ => ⟨hp, by
      rcases h with h | h
      · left; rw [h]; rfl
      · right; exact shielded_of_terminateShielded rest h⟩

/-- **Abort shielding suffices** (a corollary of `robust_iff_shielded`). For every chain `c` with
`TerminateShielded c` (scanning from the innermost frame, every frame is compiled with
`pads = full` up to and including the first frame with a terminate pad, or up to the end of the
chain if there is none), the compiled and specified unwinds agree on every chain `c'` with
`SameShape c c'`. -/
theorem robust_of_terminateShielded (c : List UFrame) (h : TerminateShielded c) :
    ∀ c', SameShape c c' → compUnwind c' = specUnwind c' :=
  (robust_iff_shielded c).2 (shielded_of_terminateShielded c h)

end Toy.UnwindCap
