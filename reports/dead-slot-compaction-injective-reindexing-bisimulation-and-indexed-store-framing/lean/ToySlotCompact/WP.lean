import ToySlotCompact.Bisim

/-!
# Weakest preconditions and verification-condition transport
-/

namespace Toy.SlotCompact

variable {N M : Nat}

/-- Fuel-bounded execution: `exec p n s = some sf` iff `p` halts from `s` within `n` steps in
state `sf` (the state at the `halt` instruction). Debug events are ignored; the emitted output
values are a function of `sf` (`outs.map sf.st` for the `halt outs` at `sf.pc`). -/
def exec (p : Prog N) : Nat → State N → Option (State N)
  | 0, _ => none
  | n + 1, s =>
    match step p s with
    | .running s' _ => exec p n s'
    | .halted s' _ => some s'
    | .stuck => none

/-- `pc` is the position of a `halt` instruction of `p`. -/
def IsHalt (p : Prog N) (pc : Nat) : Prop := ∃ outs, p[pc]? = some (Instr.halt outs)

/-- Total-correctness weakest precondition: from `s`, `p` halts and the halting state satisfies
`Q`. Postconditions may depend on the halting program point and the final store. -/
def wp (p : Prog N) (Q : State N → Prop) (s : State N) : Prop :=
  ∃ n sf, exec p n s = some sf ∧ Q sf

theorem exec_isHalt {p : Prog N} : ∀ {n : Nat} {s sf : State N}, exec p n s = some sf →
    IsHalt p sf.pc := by
  intro n
  induction n with
  | zero => intro s sf h; simp [exec] at h
  | succ n ih =>
    intro s sf h
    simp only [exec] at h
    cases hs : step p s with
    | running s' e => rw [hs] at h; exact ih h
    | stuck => rw [hs] at h; simp at h
    | halted s' o =>
      rw [hs] at h
      simp only [Option.some.injEq] at h
      subst h
      unfold step at hs
      cases hp : p[s.pc]? with
      | none => rw [hp] at hs; simp at hs
      | some ins =>
        rw [hp] at hs
        cases ins <;> simp [stepInstr] at hs
        case halt outs => obtain ⟨rfl, -⟩ := hs; exact ⟨outs, hp⟩

/-- Option matching under a relation. -/
def OptRel {N M : Nat} (R : State N → State M → Prop) : Option (State N) → Option (State M) → Prop
  | none, none => True
  | some a, some b => R a b
  | _, _ => False

theorem exec_optRel_of_silentBisim {p : Prog N} {q : Prog M} {R : State N → State M → Prop}
    (h : SilentBisim p q R) : ∀ (n : Nat) (s : State N) (s' : State M), R s s' →
      OptRel R (exec p n s) (exec q n s') := by
  intro n
  induction n with
  | zero => intro s s' _; trivial
  | succ n ih =>
    intro s s' hs
    have h1 := h s s' hs
    simp only [exec]
    revert h1
    cases step p s <;> cases step q s' <;> simp [ResRelS, OptRel]
    case running.running a _ b _ => exact ih a b

/-- Weakest preconditions are transported along any silent lockstep bisimulation, for
postconditions that agree on related halting states. -/
theorem wp_iff_of_silentBisim {p : Prog N} {q : Prog M} {R : State N → State M → Prop}
    (h : SilentBisim p q R) {Q : State N → Prop} {Q' : State M → Prop}
    (hQ : ∀ s s', IsHalt p s.pc → R s s' → (Q s ↔ Q' s')) {s : State N} {s' : State M}
    (hs : R s s') : wp p Q s ↔ wp q Q' s' := by
  have hrel := fun n => exec_optRel_of_silentBisim h n s s' hs
  constructor
  · rintro ⟨n, sf, hex, hq⟩
    have := hrel n
    rw [hex] at this
    cases hq' : exec q n s' with
    | none => rw [hq'] at this; exact this.elim
    | some sf' =>
      rw [hq'] at this
      exact ⟨n, sf', hq', (hQ sf sf' (exec_isHalt hex) this).mp hq⟩
  · rintro ⟨n, sf', hex, hq⟩
    have := hrel n
    rw [hex] at this
    cases hp : exec p n s with
    | none => rw [hp] at this; exact this.elim
    | some sf =>
      rw [hp] at this
      exact ⟨n, sf, hp, (hQ sf sf' (exec_isHalt hp) this).mpr hq⟩

/-- If some postcondition pair agreeing on related halting states has different weakest
preconditions at related states, the relation is not a silent (hence not a lockstep)
bisimulation. Used to derive bisimulation failures from concrete executions. -/
theorem not_lockstepBisim_of_wp_ne {p : Prog N} {q : Prog M} {R : State N → State M → Prop}
    {Q : State N → Prop} {Q' : State M → Prop}
    (hQ : ∀ s s', IsHalt p s.pc → R s s' → (Q s ↔ Q' s')) {s : State N} {s' : State M}
    (hs : R s s') (hne : ¬ (wp p Q s ↔ wp q Q' s')) : ¬ LockstepBisim p q R :=
  fun hb => hne (wp_iff_of_silentBisim (silentBisim_of_lockstepBisim hb) hQ hs)

/-! ## Transport for compaction -/

/-- `Q` (original) and `Q'` (compacted) agree on every pair of `CompactRel`-related halting
states. -/
def PostCorr (p : Prog N) (L : Ann N) (π : Compaction p L M) (Q : State N → Prop)
    (Q' : State M → Prop) : Prop :=
  ∀ s s', IsHalt p s.pc → CompactRel p L π s s' → (Q s ↔ Q' s')

/-- **WP transport.** Under the liveness certificate and the no-clobber conditions (in
particular for injective `π`), the weakest precondition of the compacted program for `Q'` and
of the original program for `Q` agree on `CompactRel`-related states, whenever `Q` and `Q'`
agree on related halting states. Debug reads are irrelevant here. -/
theorem wp_transport_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hA : NoAssignClobber p L π)
    (hM : NoMarkerClobber p L π) {Q : State N → Prop} {Q' : State M → Prop}
    (hQ : PostCorr p L π Q Q') :
    ∀ s s', CompactRel p L π s s' → (wp p Q s ↔ wp (compact p L π) Q' s') :=
  fun _ _ hs => wp_iff_of_silentBisim (compact_silentBisim_of_noClobber p L π hR hT hA hM) hQ hs

/-- `Q` mentions only live slots: at every halting point, `Q` depends only on the slots the mask
declares live there. -/
def DependsOnlyOnLive (p : Prog N) (L : Ann N) (Q : State N → Prop) : Prop :=
  ∀ s t : State N, IsHalt p s.pc → s.pc = t.pc → (∀ i, L s.pc i = true → s.st i = t.st i) →
    (Q s ↔ Q t)

/-- The transported postcondition: evaluate `Q` on the pulled-back store. -/
def pullPost {p : Prog N} {L : Ann N} (π : Compaction p L M) (Q : State N → Prop) :
    State M → Prop :=
  fun s' => Q ⟨s'.pc, pullStore π s'.st⟩

theorem isHalt_lt {p : Prog N} {pc : Nat} (h : IsHalt p pc) : ∃ ins, p[pc]? = some ins := by
  obtain ⟨outs, h⟩ := h
  exact ⟨_, h⟩

/-- A postcondition mentioning only live slots corresponds to its transport `pullPost π Q`. -/
theorem postCorr_pullPost {p : Prog N} {L : Ann N} (π : Compaction p L M) {Q : State N → Prop}
    (hQ : DependsOnlyOnLive p L Q) : PostCorr p L π Q (pullPost π Q) := by
  intro s s' hh ⟨hpc, hst⟩
  obtain ⟨ins, hins⟩ := isHalt_lt hh
  apply hQ s ⟨s'.pc, pullStore π s'.st⟩ hh hpc.symm
  intro i hl
  have hk := kept_of_getElem? hins hl
  simp only [pullStore_kept π s'.st hk]
  exact (hst i hk hl).symm

/-- **Exact class of transportable postconditions.** If `π` is injective on the slots live at
each halting point, a postcondition `Q` has some compacted counterpart `Q'` agreeing with it on
related halting states iff `Q` mentions only live slots. -/
theorem exists_postCorr_iff_dependsOnlyOnLive (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hinj : ∀ pc, IsHalt p pc → InjOnLiveAt p L π pc) (Q : State N → Prop) :
    (∃ Q' : State M → Prop, PostCorr p L π Q Q') ↔ DependsOnlyOnLive p L Q := by
  constructor
  · rintro ⟨Q', hQ'⟩ s t hh hpc hag
    let s' : State M := ⟨s.pc, pushStore π s.pc s.st⟩
    have hs : CompactRel p L π s s' := compactRel_pushStore (hinj s.pc hh) s.st
    have ht : CompactRel p L π t s' := by
      refine ⟨hpc, fun i hk hl => ?_⟩
      rw [← hpc] at hl
      rw [← hag i hl]
      exact hs.2 i hk hl
    have hh' : IsHalt p t.pc := hpc ▸ hh
    exact (hQ' s s' hh hs).trans (hQ' t s' hh' ht).symm
  · intro hQ
    exact ⟨pullPost π Q, postCorr_pullPost π hQ⟩

/-- `Pre` mentions only slots that are kept and live at entry. -/
def DependsOnlyOnEntryLive (p : Prog N) (L : Ann N) (Pre : Store N → Prop) : Prop :=
  ∀ σ τ : Store N, (∀ i, L 0 i = true → Kept p L i = true → σ i = τ i) → (Pre σ ↔ Pre τ)

/-- **Verification-condition transport, original to compacted.** Under the liveness
certificate and the no-clobber conditions, if "`Pre` implies `wp p Q`" holds at entry for the
original program and `Q` mentions only live slots, then the transported condition holds for the
compacted program, with transported precondition `Pre ∘ pullStore π` and transported
postcondition `pullPost π Q`. No injectivity at entry and no restriction on `Pre` is needed. -/
theorem vc_forward_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hA : NoAssignClobber p L π)
    (hM : NoMarkerClobber p L π) (Pre : Store N → Prop) (Q : State N → Prop)
    (hQ : DependsOnlyOnLive p L Q) :
    (∀ σ, Pre σ → wp p Q ⟨0, σ⟩) →
      (∀ σ', Pre (pullStore π σ') → wp (compact p L π) (pullPost π Q) ⟨0, σ'⟩) := by
  have htr := wp_transport_of_noClobber p L π hR hT hA hM (postCorr_pullPost π hQ)
  intro h σ' hpre
  exact (htr _ _ (compactRel_pullStore π σ' 0)).mp (h _ hpre)

/-- **Verification-condition transport, compacted to original.** Under the liveness certificate,
the no-clobber conditions, and injectivity of `π` on the slots live at entry, if the transported
condition holds for the compacted program, then "`Pre` implies `wp p Q`" holds at entry for the
original program, provided `Pre` mentions only kept entry-live slots and `Q` mentions only live
slots. -/
theorem vc_backward_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hA : NoAssignClobber p L π)
    (hM : NoMarkerClobber p L π) (hinj0 : InjOnLiveAt p L π 0) (Pre : Store N → Prop)
    (Q : State N → Prop) (hPre : DependsOnlyOnEntryLive p L Pre) (hQ : DependsOnlyOnLive p L Q) :
    (∀ σ', Pre (pullStore π σ') → wp (compact p L π) (pullPost π Q) ⟨0, σ'⟩) →
      (∀ σ, Pre σ → wp p Q ⟨0, σ⟩) := by
  have htr := wp_transport_of_noClobber p L π hR hT hA hM (postCorr_pullPost π hQ)
  intro h σ hpre
  have hrel := compactRel_pushStore hinj0 σ
  have hpre' : Pre (pullStore π (pushStore π 0 σ)) := by
    refine (hPre _ σ (fun i hl hk => ?_)).mpr hpre
    rw [pullStore_kept π _ hk]
    exact pushStore_live hinj0 σ hk hl
  exact (htr _ _ hrel).mpr (h _ hpre')

/-- Both directions together (convenience corollary). -/
theorem vc_transfer_of_noClobber (p : Prog N) (L : Ann N) (π : Compaction p L M)
    (hR : ReadsLive p L) (hT : TransferClosed p L) (hA : NoAssignClobber p L π)
    (hM : NoMarkerClobber p L π) (hinj0 : InjOnLiveAt p L π 0) (Pre : Store N → Prop)
    (Q : State N → Prop) (hPre : DependsOnlyOnEntryLive p L Pre) (hQ : DependsOnlyOnLive p L Q) :
    (∀ σ, Pre σ → wp p Q ⟨0, σ⟩) ↔
      (∀ σ', Pre (pullStore π σ') → wp (compact p L π) (pullPost π Q) ⟨0, σ'⟩) :=
  ⟨vc_forward_of_noClobber p L π hR hT hA hM Pre Q hQ,
    vc_backward_of_noClobber p L π hR hT hA hM hinj0 Pre Q hPre hQ⟩

end Toy.SlotCompact
