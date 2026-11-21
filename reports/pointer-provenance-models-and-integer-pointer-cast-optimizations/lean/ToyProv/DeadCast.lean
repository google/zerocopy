import ToyProv.Exec

/-!
# Dead `ptr2int` elimination in the deterministic models

`AgreeExcept d s₁ s₂`: two states that agree except on register `d` and on the exposed set. In
`flat` and `strict` no instruction reads the exposed set, so running a program that does not read
`d` from two such states gives the same outputs (`execOk_agreeExcept`). Hence removing an unused
`ptr2int` is sound in both models (`dropUnusedPtr2int_sound_det`).
-/

namespace Toy.Prov

def AgreeExcept (d : Reg) (s₁ s₂ : St) : Prop :=
  s₁.blocks = s₂.blocks ∧
  s₁.mem = s₂.mem ∧
  s₁.top = s₂.top ∧
  s₁.out = s₂.out ∧
  (∀ r, r ≠ d → s₁.regs r = s₂.regs r)

theorem agreeExcept_setReg {d : Reg} {s₁ s₂ : St} (h : AgreeExcept d s₁ s₂)
    (dst : Reg) (v : Val) : AgreeExcept d (s₁.setReg dst v) (s₂.setReg dst v) := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun r hr => ?_⟩
  simp only [St.setReg]
  split
  · rfl
  · exact h.2.2.2.2 r hr

theorem agreeExcept_expose {d : Reg} {s₁ s₂ : St} (h : AgreeExcept d s₁ s₂)
    (ps₁ ps₂ : List AllocId) : AgreeExcept d (s₁.expose ps₁) (s₂.expose ps₂) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem canAccess_of_blocks_eq {m : Model} {s₁ s₂ : St} (h : s₁.blocks = s₂.blocks)
    (x : Ptr) (n : Nat) : canAccess m s₁ x n = canAccess m s₂ x n := by
  cases m <;> simp [canAccess, h]

theorem freeTarget_of_blocks_eq {m : Model} {s₁ s₂ : St} (h : s₁.blocks = s₂.blocks)
    (x : Ptr) : freeTarget m s₁ x = freeTarget m s₂ x := by
  cases m <;> simp [freeTarget, h]

theorem step_agreeExcept {m : Model} (hm : m = .flat ∨ m = .strict) {d : Reg}
    {s₁ s₂ : St} {i : Instr} (h : AgreeExcept d s₁ s₂) (hi : i.reads d = false) :
    ((step m s₁ i).filterMap id = [] ∧ (step m s₂ i).filterMap id = []) ∨
    (∃ s₁' s₂', (step m s₁ i).filterMap id = [s₁'] ∧ (step m s₂ i).filterMap id = [s₂'] ∧
      AgreeExcept d s₁' s₂') := by
  have hcast : ∀ dst a,
      ∃ s₁' s₂', (castToPtr m s₁ dst a).filterMap id = [s₁'] ∧
        (castToPtr m s₂ dst a).filterMap id = [s₂'] ∧ AgreeExcept d s₁' s₂' := by
    intro dst a
    rcases hm with rfl | rfl <;>
      exact ⟨s₁.setReg dst (.ptr ⟨none, a⟩), s₂.setReg dst (.ptr ⟨none, a⟩),
        rfl, rfl, agreeExcept_setReg h dst _⟩
  cases i with
  | alloc dst n =>
    by_cases hn : n = 0
    · left; simp [step, hn]
    · right
      rcases hm with rfl | rfl
      · refine ⟨{ (s₁.setReg dst (.ptr ⟨none, s₁.top⟩)) with
                    blocks := s₁.blocks ++ [⟨s₁.top, n, true⟩], top := s₁.top + n },
          { (s₂.setReg dst (.ptr ⟨none, s₁.top⟩)) with
              blocks := s₂.blocks ++ [⟨s₁.top, n, true⟩], top := s₁.top + n },
          by simp [step, hn], by simp [step, hn, h.2.2.1], ?_⟩
        have hsr := agreeExcept_setReg h dst (.ptr ⟨none, s₁.top⟩)
        exact ⟨by simp [h.1], hsr.2.1, rfl, hsr.2.2.2.1, hsr.2.2.2.2⟩
      · refine ⟨{ (s₁.setReg dst (.ptr ⟨some s₁.blocks.length, s₁.top⟩)) with
                    blocks := s₁.blocks ++ [⟨s₁.top, n, true⟩], top := s₁.top + n },
          { (s₂.setReg dst (.ptr ⟨some s₁.blocks.length, s₁.top⟩)) with
              blocks := s₂.blocks ++ [⟨s₁.top, n, true⟩], top := s₁.top + n },
          by simp [step, hn], by simp [step, hn, h.1, h.2.2.1], ?_⟩
        have hsr := agreeExcept_setReg h dst (.ptr ⟨some s₁.blocks.length, s₁.top⟩)
        exact ⟨by simp [h.1], hsr.2.1, rfl, hsr.2.2.2.1, hsr.2.2.2.2⟩
  | free p =>
    have hp : p ≠ d := by simpa [Instr.reads] using hi
    have hreg : s₁.regs p = s₂.regs p := h.2.2.2.2 p hp
    cases hpv : s₁.regs p with
    | none => left; simp [step, hpv, ← hreg]
    | some v =>
      cases v with
      | int _ => left; simp [step, hpv, ← hreg]
      | ptr x =>
        have hft_eq : freeTarget m s₁ x = freeTarget m s₂ x := freeTarget_of_blocks_eq h.1 x
        cases hft : freeTarget m s₂ x with
        | none => left; simp [step, hpv, ← hreg, hft_eq, hft]
        | some id =>
          right
          refine ⟨{ s₁ with blocks := killBlock s₁.blocks id },
            { s₂ with blocks := killBlock s₂.blocks id },
            by simp [step, hpv, hft_eq, hft],
            by simp [step, ← hreg, hpv, hft],
            ⟨by simp [h.1], h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩
  | load dst ty p =>
    have hp : p ≠ d := by simpa [Instr.reads] using hi
    have hreg : s₁.regs p = s₂.regs p := h.2.2.2.2 p hp
    cases hpv : s₁.regs p with
    | none => left; simp [step, hpv, ← hreg]
    | some v =>
      cases v with
      | int _ => left; simp [step, hpv, ← hreg]
      | ptr x =>
        by_cases hacc : canAccess m s₁ x 2 = true
        · have hacc2 : canAccess m s₂ x 2 = true := by rwa [← canAccess_of_blocks_eq h.1]
          cases ty with
          | int =>
            cases hdec : decodeInt (s₁.mem x.addr) (s₁.mem (x.addr + 1)) with
            | none => left; simp [step, hpv, ← hreg, hacc, hacc2, ← h.2.1, hdec]
            | some np =>
              right
              refine ⟨(s₁.setReg dst (.int np.1)).expose np.2,
                (s₂.setReg dst (.int np.1)).expose np.2,
                by simp [step, hpv, hacc, hdec],
                by simp [step, ← hreg, hpv, hacc2, ← h.2.1, hdec],
                agreeExcept_expose (agreeExcept_setReg h dst _) _ _⟩
          | ptr =>
            cases hdec : decodePtr (s₁.mem x.addr) (s₁.mem (x.addr + 1)) with
            | none => left; simp [step, hpv, ← hreg, hacc, hacc2, ← h.2.1, hdec]
            | some res =>
              cases res with
              | inl q =>
                right
                refine ⟨s₁.setReg dst (.ptr q), s₂.setReg dst (.ptr q),
                  by simp [step, hpv, hacc, hdec],
                  by simp [step, ← hreg, hpv, hacc2, ← h.2.1, hdec],
                  agreeExcept_setReg h dst _⟩
              | inr n =>
                right
                obtain ⟨s₁', s₂', hs₁', hs₂', ha⟩ := hcast dst n
                exact ⟨s₁', s₂', by simpa [step, hpv, hacc, hdec] using hs₁',
                  by simpa [step, ← hreg, hpv, hacc2, ← h.2.1, hdec] using hs₂', ha⟩
        · left; simp [step, hpv, ← hreg, hacc, ← canAccess_of_blocks_eq h.1]
  | store p r =>
    simp only [Instr.reads, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
    have hregp := h.2.2.2.2 p hi.1
    have hregr := h.2.2.2.2 r hi.2
    cases hpv : s₁.regs p with
    | none => left; simp [step, hpv, ← hregp]
    | some vp =>
      cases vp with
      | int _ => left; simp [step, hpv, ← hregp]
      | ptr x =>
        cases hrv : s₁.regs r with
        | none => left; simp [step, hpv, ← hregp, hrv, ← hregr]
        | some vr =>
          by_cases hacc : canAccess m s₁ x 2 = true
          · have hacc2 : canAccess m s₂ x 2 = true := by rwa [← canAccess_of_blocks_eq h.1]
            right
            refine ⟨{ s₁ with mem := writeBytes s₁.mem x.addr (encodeVal vr) },
              { s₂ with mem := writeBytes s₂.mem x.addr (encodeVal vr) },
              by simp [step, hpv, hrv, hacc],
              by simp [step, ← hregp, hpv, ← hregr, hrv, hacc2],
              ⟨h.1, by simp [h.2.1], h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩
          · left; simp [step, hpv, ← hregp, hrv, ← hregr, hacc, ← canAccess_of_blocks_eq h.1]
  | memcpy dst r n =>
    simp only [Instr.reads, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
    have hregd := h.2.2.2.2 dst hi.1
    have hregr := h.2.2.2.2 r hi.2
    cases hdv : s₁.regs dst with
    | none => left; simp [step, hdv, ← hregd]
    | some vd =>
      cases vd with
      | int _ => left; simp [step, hdv, ← hregd]
      | ptr x =>
        cases hrv : s₁.regs r with
        | none => left; simp [step, hdv, ← hregd, hrv, ← hregr]
        | some vr =>
          cases vr with
          | int _ => left; simp [step, hdv, ← hregd, hrv, ← hregr]
          | ptr y =>
            by_cases hacc : (canAccess m s₁ x n && canAccess m s₁ y n) = true
            · have hacc2 : (canAccess m s₂ x n && canAccess m s₂ y n) = true := by
                simpa [canAccess_of_blocks_eq h.1] using hacc
              right
              refine ⟨{ s₁ with mem := writeBytes s₁.mem x.addr (readBytes s₁.mem y.addr n) },
                { s₂ with mem := writeBytes s₂.mem x.addr (readBytes s₂.mem y.addr n) },
                by simp [step, hdv, hrv, hacc],
                by simp [step, ← hregd, hdv, ← hregr, hrv, hacc2],
                ⟨h.1, by simp [h.2.1], h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩
            · have hacc2 : (canAccess m s₂ x n && canAccess m s₂ y n) = false := by
                rw [← canAccess_of_blocks_eq h.1, ← canAccess_of_blocks_eq h.1]
                cases h' : (canAccess m s₁ x n && canAccess m s₁ y n) <;> simp_all
              left
              simp [step, hdv, ← hregd, hrv, ← hregr, hacc, hacc2]
  | ptr2int dst p =>
    have hp : p ≠ d := by simpa [Instr.reads] using hi
    have hreg := h.2.2.2.2 p hp
    cases hpv : s₁.regs p with
    | none => left; simp [step, hpv, ← hreg]
    | some v =>
      cases v with
      | int _ => left; simp [step, hpv, ← hreg]
      | ptr x =>
        right
        refine ⟨(s₁.setReg dst (.int x.addr)).expose x.prov.toList,
          (s₂.setReg dst (.int x.addr)).expose x.prov.toList,
          by simp [step, hpv], by simp [step, ← hreg, hpv],
          agreeExcept_expose (agreeExcept_setReg h dst _) _ _⟩
  | int2ptr dst r =>
    have hr : r ≠ d := by simpa [Instr.reads] using hi
    have hreg := h.2.2.2.2 r hr
    cases hrv : s₁.regs r with
    | none => left; simp [step, hrv, ← hreg]
    | some v =>
      cases v with
      | ptr _ => left; simp [step, hrv, ← hreg]
      | int a =>
        right
        obtain ⟨s₁', s₂', hs₁', hs₂', ha⟩ := hcast dst a
        exact ⟨s₁', s₂', by simpa [step, hrv] using hs₁',
          by simpa [step, ← hreg, hrv] using hs₂', ha⟩
  | ptrEq dst p q =>
    simp only [Instr.reads, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
    have hregp := h.2.2.2.2 p hi.1
    have hregq := h.2.2.2.2 q hi.2
    cases hpv : s₁.regs p with
    | none => left; simp [step, hpv, ← hregp]
    | some vp =>
      cases vp with
      | int _ => left; simp [step, hpv, ← hregp]
      | ptr x =>
        cases hqv : s₁.regs q with
        | none => left; simp [step, hpv, ← hregp, hqv, ← hregq]
        | some vq =>
          cases vq with
          | int _ => left; simp [step, hpv, ← hregp, hqv, ← hregq]
          | ptr y =>
            right
            refine ⟨s₁.setReg dst (.int (if x.addr = y.addr then 1 else 0)),
              s₂.setReg dst (.int (if x.addr = y.addr then 1 else 0)),
              by simp [step, hpv, hqv], by simp [step, ← hregp, hpv, ← hregq, hqv],
              agreeExcept_setReg h dst _⟩
  | intEq dst i j =>
    simp only [Instr.reads, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hi
    have hregi := h.2.2.2.2 i hi.1
    have hregj := h.2.2.2.2 j hi.2
    cases hiv : s₁.regs i with
    | none => left; simp [step, hiv, ← hregi]
    | some vi =>
      cases vi with
      | ptr _ => left; simp [step, hiv, ← hregi]
      | int a =>
        cases hjv : s₁.regs j with
        | none => left; simp [step, hiv, ← hregi, hjv, ← hregj]
        | some vj =>
          cases vj with
          | ptr _ => left; simp [step, hiv, ← hregi, hjv, ← hregj]
          | int b =>
            right
            refine ⟨s₁.setReg dst (.int (if a = b then 1 else 0)),
              s₂.setReg dst (.int (if a = b then 1 else 0)),
              by simp [step, hiv, hjv], by simp [step, ← hregi, hiv, ← hregj, hjv],
              agreeExcept_setReg h dst _⟩
  | offset dst p k =>
    have hp : p ≠ d := by simpa [Instr.reads] using hi
    have hreg := h.2.2.2.2 p hp
    cases hpv : s₁.regs p with
    | none => left; simp [step, hpv, ← hreg]
    | some vp =>
      cases vp with
      | int _ => left; simp [step, hpv, ← hreg]
      | ptr x =>
        cases hoa : offsetAddr x.addr k with
        | none => left; simp [step, hpv, ← hreg, hoa]
        | some a =>
          right
          refine ⟨s₁.setReg dst (.ptr ⟨x.prov, a⟩), s₂.setReg dst (.ptr ⟨x.prov, a⟩),
            by simp [step, hpv, hoa], by simp [step, ← hreg, hpv, hoa],
            agreeExcept_setReg h dst _⟩
  | const dst n =>
    right
    refine ⟨s₁.setReg dst (.int n), s₂.setReg dst (.int n), rfl, rfl, agreeExcept_setReg h dst _⟩
  | copy dst r =>
    have hr : r ≠ d := by simpa [Instr.reads] using hi
    have hreg := h.2.2.2.2 r hr
    cases hrv : s₁.regs r with
    | none => left; simp [step, hrv, ← hreg]
    | some v =>
      right
      refine ⟨s₁.setReg dst v, s₂.setReg dst v, by simp [step, hrv], by simp [step, ← hreg, hrv],
        agreeExcept_setReg h dst _⟩
  | obs r =>
    have hr : r ≠ d := by simpa [Instr.reads] using hi
    have hreg := h.2.2.2.2 r hr
    cases hrv : s₁.regs r with
    | none => left; simp [step, hrv, ← hreg]
    | some v =>
      cases v with
      | int n =>
        right
        refine ⟨{ s₁ with out := s₁.out ++ [n] }, { s₂ with out := s₂.out ++ [n] },
          by simp [step, hrv], by simp [step, ← hreg, hrv],
          ⟨h.1, h.2.1, h.2.2.1, by simp [h.2.2.2.1], h.2.2.2.2⟩⟩
      | ptr x =>
        right
        refine ⟨{ s₁ with out := s₁.out ++ [x.addr] }, { s₂ with out := s₂.out ++ [x.addr] },
          by simp [step, hrv], by simp [step, ← hreg, hrv],
          ⟨h.1, h.2.1, h.2.2.1, by simp [h.2.2.2.1], h.2.2.2.2⟩⟩

theorem execOk_agreeExcept {m : Model} (hm : m = .flat ∨ m = .strict) {d : Reg}
    {post : Prog} {s₁ s₂ : St} (h : AgreeExcept d s₁ s₂)
    (hpost : ∀ i ∈ post, i.reads d = false) :
    (execOk m post s₁).map St.out = (execOk m post s₂).map St.out := by
  induction post generalizing s₁ s₂ with
  | nil => simp [execOk_nil, h.2.2.2.1]
  | cons i post ih =>
    rw [execOk_cons, execOk_cons]
    rcases step_agreeExcept hm h (hpost i (by simp)) with ⟨he₁, he₂⟩ | ⟨s₁', s₂', hs₁', hs₂', ha'⟩
    · simp [he₁, he₂]
    · rw [hs₁', hs₂']
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact ih ha' (fun j hj => hpost j (by simp [hj]))

theorem dropUnusedPtr2int_sound_det {m : Model} (hm : m = .flat ∨ m = .strict) :
    Sound m DropUnusedPtr2int := by
  rintro src tgt ⟨pre, post, d, p, rfl, rfl, hpost, hp⟩
  apply refines_of_after_map_out_eq
  rw [after_eq_execOk, after_eq_execOk, execOk_append, execOk_append]
  simp only [List.map_flatMap]
  apply flatMap_congr_mem
  intro s hs
  have hps := hp s hs
  simp only [isPtrC] at hps
  cases hsp : s.regs p with
  | none => simp [hsp] at hps
  | some vp =>
    cases vp with
    | int _ => simp [hsp] at hps
    | ptr x =>
      rw [execOk_cons]
      have hstep : (step m s (.ptr2int d p)).filterMap id =
          [((s.setReg d (.int x.addr)).expose x.prov.toList)] := by
        simp [step, hsp]
      rw [hstep, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      have ha : AgreeExcept d ((s.setReg d (.int x.addr)).expose x.prov.toList) s :=
        ⟨rfl, rfl, rfl, rfl, fun r hr => by simp [St.expose, St.setReg, hr]⟩
      exact (execOk_agreeExcept hm ha hpost).symm

end Toy.Prov
