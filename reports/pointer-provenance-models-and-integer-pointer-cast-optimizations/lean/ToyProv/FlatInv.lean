import ToyProv.Exec

/-!
# The flat-model invariant

In `flat`, no reachable register or memory byte carries provenance (`FlatSt`): allocation, `int2ptr`
and pointer decoding all produce provenance-less pointers. Consequences: address-equal pointers are
identical values in `flat` (`substAddrEq_sound_flat`), and a side condition that requires a
provenance (such as `provIsCandC`) holds in no reachable `flat` state.
-/

namespace Toy.Prov

def FlatByte : AByte → Prop
  | .uninit => True
  | .intFrag _ _ => True
  | .ptrFrag p _ => p.prov = none

def FlatVal : Val → Prop
  | .int _ => True
  | .ptr p => p.prov = none

def FlatSt (s : St) : Prop :=
  (∀ r v, s.regs r = some v → FlatVal v) ∧ (∀ a, FlatByte (s.mem a))

theorem flatSt_init : FlatSt init := ⟨fun _ _ h => by simp [init] at h, fun _ => trivial⟩

theorem flatByte_writeBytes (mem : Addr → AByte) (a : Addr) (bs : List AByte)
    (hmem : ∀ x, FlatByte (mem x)) (hbs : ∀ b ∈ bs, FlatByte b) :
    ∀ x, FlatByte (writeBytes mem a bs x) := by
  induction bs generalizing mem a with
  | nil => exact hmem
  | cons b bs ih =>
    intro x
    apply ih
    · intro y
      split
      · exact hbs b (by simp)
      · exact hmem y
    · intro b' hb'
      exact hbs b' (by simp [hb'])

theorem flatByte_readBytes (mem : Addr → AByte) (a n : Nat)
    (hmem : ∀ x, FlatByte (mem x)) : ∀ b ∈ readBytes mem a n, FlatByte b := by
  induction n generalizing a with
  | zero => intro b hb; simp [readBytes] at hb
  | succ n ih =>
    intro b hb
    simp only [readBytes, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hmem a
    · exact ih (a + 1) b hb

theorem flatSt_setReg {s : St} (hs : FlatSt s) (r : Reg) {v : Val} (hv : FlatVal v) :
    FlatSt (s.setReg r v) := by
  refine ⟨fun x w hw => ?_, hs.2⟩
  simp only [St.setReg] at hw
  split at hw
  · cases hw; exact hv
  · exact hs.1 x w hw

theorem flatByte_decodePtr {b₀ b₁ : AByte} {q : Ptr}
    (hb₀ : FlatByte b₀) (hb₁ : FlatByte b₁) (h : decodePtr b₀ b₁ = some (.inl q)) :
    FlatVal (.ptr q) := by
  cases b₀ with
  | uninit => cases b₁ <;> simp [decodePtr] at h
  | intFrag n₀ i₀ =>
    cases b₁ with
    | uninit => simp [decodePtr] at h
    | ptrFrag _ _ => simp [decodePtr] at h
    | intFrag n₁ i₁ =>
      rw [decodePtr_intFrag_eq] at h
      split at h <;> simp at h
  | ptrFrag p₀ i₀ =>
    cases b₁ with
    | uninit => simp [decodePtr] at h
    | intFrag _ _ => simp [decodePtr] at h
    | ptrFrag p₁ i₁ =>
      rcases i₀ with _ | _ | i₀ <;> rcases i₁ with _ | _ | i₁ <;>
        simp [decodePtr] at h
      obtain ⟨_, rfl⟩ := h
      have h0 : p₀.prov = none := hb₀
      have h1 : p₁.prov = none := hb₁
      simp [FlatVal, mergeProv, h0, h1]

theorem step_flat_preserves {s s' : St} {i : Instr} (hs : FlatSt s)
    (hstep : some s' ∈ step .flat s i) : FlatSt s' := by
  cases i with
  | alloc d n =>
    by_cases hn : n = 0
    · simp [step, hn] at hstep
    · simp only [step, hn, ↓reduceIte, List.mem_singleton, Option.some.injEq] at hstep
      subst hstep
      exact ⟨(flatSt_setReg hs d (show FlatVal (.ptr ⟨none, s.top⟩) from rfl)).1, hs.2⟩
  | free p =>
    simp only [step] at hstep
    cases hr : s.regs p with
    | none => simp [hr] at hstep
    | some v =>
      cases v with
      | int _ => simp [hr] at hstep
      | ptr x =>
        simp only [hr] at hstep
        cases hft : freeTarget .flat s x <;> simp [hft] at hstep
        subst hstep; exact hs
  | load d ty p =>
    simp only [step] at hstep
    cases hr : s.regs p with
    | none => simp [hr] at hstep
    | some v =>
      cases v with
      | int _ => simp [hr] at hstep
      | ptr x =>
        simp only [hr] at hstep
        by_cases hacc : canAccess .flat s x 2 = true
        · simp only [hacc, ↓reduceIte] at hstep
          cases ty with
          | int =>
            simp only at hstep
            cases hdec : decodeInt (s.mem x.addr) (s.mem (x.addr + 1)) with
            | none => simp [hdec] at hstep
            | some np =>
              simp only [hdec, List.mem_singleton, Option.some.injEq] at hstep
              subst hstep
              exact ⟨(flatSt_setReg hs d (show FlatVal (.int np.1) from trivial)).1, hs.2⟩
          | ptr =>
            simp only at hstep
            cases hdec : decodePtr (s.mem x.addr) (s.mem (x.addr + 1)) with
            | none => simp [hdec] at hstep
            | some res =>
              simp only [hdec] at hstep
              cases res with
              | inl q =>
                simp only [List.mem_singleton, Option.some.injEq] at hstep
                subst hstep
                exact flatSt_setReg hs d (flatByte_decodePtr (hs.2 x.addr) (hs.2 (x.addr + 1)) hdec)
              | inr n =>
                simp only [castToPtr, List.mem_singleton, Option.some.injEq] at hstep
                subst hstep
                exact flatSt_setReg hs d (show FlatVal (.ptr ⟨none, n⟩) from rfl)
        · simp [hacc] at hstep
  | store p r =>
    simp only [step] at hstep
    cases hp : s.regs p with
    | none => simp [hp] at hstep
    | some vp =>
      cases vp with
      | int _ => simp [hp] at hstep
      | ptr x =>
        cases hr : s.regs r with
        | none => simp [hp, hr] at hstep
        | some vr =>
          simp only [hp, hr] at hstep
          by_cases hacc : canAccess .flat s x 2 = true
          · simp only [hacc, ↓reduceIte, List.mem_singleton, Option.some.injEq] at hstep
            subst hstep
            refine ⟨hs.1, flatByte_writeBytes _ _ _ hs.2 ?_⟩
            have hfv := hs.1 r vr hr
            cases vr with
            | int _ => intro b hb; simp [encodeVal] at hb; rcases hb with rfl | rfl <;> trivial
            | ptr q => intro b hb; simp [encodeVal] at hb; rcases hb with rfl | rfl <;> exact hfv
          · simp [hacc] at hstep
  | memcpy d r n =>
    simp only [step] at hstep
    cases hd : s.regs d with
    | none => simp [hd] at hstep
    | some vd =>
      cases vd with
      | int _ => simp [hd] at hstep
      | ptr x =>
        cases hr : s.regs r with
        | none => simp [hd, hr] at hstep
        | some vr =>
          cases vr with
          | int _ => simp [hd, hr] at hstep
          | ptr y =>
            simp only [hd, hr] at hstep
            by_cases hacc : (canAccess .flat s x n && canAccess .flat s y n) = true
            · simp only [hacc, ↓reduceIte, List.mem_singleton, Option.some.injEq] at hstep
              subst hstep
              exact ⟨hs.1, flatByte_writeBytes _ _ _ hs.2 (flatByte_readBytes _ _ _ hs.2)⟩
            · simp [hacc] at hstep
  | ptr2int d p =>
    simp only [step] at hstep
    cases hp : s.regs p with
    | none => simp [hp] at hstep
    | some v =>
      cases v with
      | int _ => simp [hp] at hstep
      | ptr x =>
        simp only [hp, List.mem_singleton, Option.some.injEq] at hstep
        subst hstep
        exact ⟨(flatSt_setReg hs d (show FlatVal (.int x.addr) from trivial)).1, hs.2⟩
  | int2ptr d i =>
    simp only [step] at hstep
    cases hi : s.regs i with
    | none => simp [hi] at hstep
    | some v =>
      cases v with
      | ptr _ => simp [hi] at hstep
      | int a =>
        simp only [hi, castToPtr, List.mem_singleton, Option.some.injEq] at hstep
        subst hstep
        exact flatSt_setReg hs d (show FlatVal (.ptr ⟨none, a⟩) from rfl)
  | ptrEq d p q =>
    simp only [step] at hstep
    cases hp : s.regs p with
    | none => simp [hp] at hstep
    | some vp =>
      cases vp with
      | int _ => simp [hp] at hstep
      | ptr x =>
        cases hq : s.regs q with
        | none => simp [hp, hq] at hstep
        | some vq =>
          cases vq with
          | int _ => simp [hp, hq] at hstep
          | ptr y =>
            simp only [hp, hq, List.mem_singleton, Option.some.injEq] at hstep
            subst hstep
            exact flatSt_setReg hs d (show FlatVal (.int _) from trivial)
  | intEq d i j =>
    simp only [step] at hstep
    cases hi : s.regs i with
    | none => simp [hi] at hstep
    | some vi =>
      cases vi with
      | ptr _ => simp [hi] at hstep
      | int a =>
        cases hj : s.regs j with
        | none => simp [hi, hj] at hstep
        | some vj =>
          cases vj with
          | ptr _ => simp [hi, hj] at hstep
          | int b =>
            simp only [hi, hj, List.mem_singleton, Option.some.injEq] at hstep
            subst hstep
            exact flatSt_setReg hs d (show FlatVal (.int _) from trivial)
  | offset d p k =>
    simp only [step] at hstep
    cases hp : s.regs p with
    | none => simp [hp] at hstep
    | some vp =>
      cases vp with
      | int _ => simp [hp] at hstep
      | ptr x =>
        simp only [hp] at hstep
        cases hoa : offsetAddr x.addr k with
        | none => simp [hoa] at hstep
        | some a =>
          simp only [hoa, List.mem_singleton, Option.some.injEq] at hstep
          subst hstep
          have hfx : x.prov = none := by simpa [FlatVal] using hs.1 p (.ptr x) hp
          exact flatSt_setReg hs d hfx
  | const d n =>
    simp only [step, List.mem_singleton, Option.some.injEq] at hstep
    subst hstep
    exact flatSt_setReg hs d (show FlatVal (.int n) from trivial)
  | copy d r =>
    simp only [step] at hstep
    cases hr : s.regs r with
    | none => simp [hr] at hstep
    | some v =>
      simp only [hr, List.mem_singleton, Option.some.injEq] at hstep
      subst hstep
      exact flatSt_setReg hs d (hs.1 r v hr)
  | obs r =>
    simp only [step] at hstep
    cases hr : s.regs r with
    | none => simp [hr] at hstep
    | some v =>
      cases v with
      | int n =>
        simp only [hr, List.mem_singleton, Option.some.injEq] at hstep
        subst hstep; exact hs
      | ptr x =>
        simp only [hr, List.mem_singleton, Option.some.injEq] at hstep
        subst hstep; exact hs

theorem execOk_flat_preserves {P : Prog} {s s' : St} (hs : FlatSt s)
    (h : s' ∈ execOk .flat P s) : FlatSt s' := by
  induction P generalizing s with
  | nil => simp [execOk_nil] at h; subst h; exact hs
  | cons i P ih =>
    rw [execOk_cons, List.mem_flatMap] at h
    rcases h with ⟨s₁, hs₁, hs'⟩
    rw [List.mem_filterMap] at hs₁
    rcases hs₁ with ⟨o, ho, ho_eq⟩
    cases o with
    | none => simp at ho_eq
    | some s₁' =>
      simp only [id_eq, Option.some.injEq] at ho_eq
      subst ho_eq
      exact ih (step_flat_preserves hs ho) hs'

theorem after_flat_flatSt (P : Prog) : ∀ s ∈ after .flat P, FlatSt s :=
  fun _ hs => execOk_flat_preserves flatSt_init hs

/-- Table: `SubstAddrEq` is sound in `flat` (address-equal pointers are identical values there,
by the invariant `FlatSt`). -/
theorem substAddrEq_sound_flat : Sound .flat SubstAddrEq := by
  rintro src tgt ⟨pre, i, post, q, p, rfl, rfl, hc⟩
  apply refines_of_beh_eq
  apply beh_replace_of_step_eq
  intro s hs
  apply step_substUse
  have hflat := after_flat_flatSt pre s hs
  have had := hc s hs
  simp only [addrEqC] at had
  cases hp : s.regs p with
  | none => simp [hp] at had
  | some vp =>
    cases vp with
    | int _ => simp [hp] at had
    | ptr xp =>
      cases hq : s.regs q with
      | none => simp [hp, hq] at had
      | some vq =>
        cases vq with
        | int _ => simp [hp, hq] at had
        | ptr xq =>
          simp only [hp, hq, beq_iff_eq] at had
          have hpx : xp.prov = none := hflat.1 p (.ptr xp) hp
          have hqx : xq.prov = none := hflat.1 q (.ptr xq) hq
          cases xp; cases xq; simp_all

end Toy.Prov
