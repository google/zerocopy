import ToyProv.Disjoint

/-!
# Monotone simulation: more provenance never adds UB

`StLE s t`: same blocks, top and output; registers related pointwise (equal integers; pointers with
equal addresses and `t`'s provenance at least `s`'s); memory related bytewise by `AByteLE`;
`s.exposed ⊆ t.exposed`. Every defined step of `s` in `strict` or `exposed` is matched by a defined
step of `t` in the same or a more permissive model (`step_mono`); the proof uses the monotonicity
of byte decoding (`decodeInt_mono`, `decodePtr_mono`). This gives R6a, the strict cast fold and R2b.
-/

namespace Toy.Prov

def ValLE : Val → Val → Prop
  | .int n, .int n' => n = n'
  | .ptr p, .ptr q => PtrLE p q
  | _, _ => False

def OptValLE : Option Val → Option Val → Prop
  | none, none => True
  | some v, some w => ValLE v w
  | _, _ => False

def StLE (s t : St) : Prop :=
  s.blocks = t.blocks ∧
  s.top = t.top ∧
  s.out = t.out ∧
  (∀ r, OptValLE (s.regs r) (t.regs r)) ∧
  (∀ a, AByteLE (s.mem a) (t.mem a)) ∧
  (∀ id ∈ s.exposed, id ∈ t.exposed)

theorem valLE_refl (v : Val) : ValLE v v := by
  cases v <;> simp [ValLE, PtrLE, ProvLE.refl]

theorem optValLE_refl (ov : Option Val) : OptValLE ov ov := by
  cases ov with
  | none => trivial
  | some v => exact valLE_refl v

theorem stLE_refl (s : St) : StLE s s :=
  ⟨rfl, rfl, rfl, fun _ => optValLE_refl _, fun _ => AByteLE.refl _, fun _ h => h⟩

theorem stLE_setReg {s t : St} (h : StLE s t) (r : Reg) {v w : Val} (hvw : ValLE v w) :
    StLE (s.setReg r v) (t.setReg r w) := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun x => ?_, h.2.2.2.2.1, h.2.2.2.2.2⟩
  simp only [St.setReg]
  split
  · exact hvw
  · exact h.2.2.2.1 x

theorem stLE_expose {s t : St} (h : StLE s t) {ps₁ ps₂ : List AllocId}
    (hps : ∀ id ∈ ps₁, id ∈ ps₂) : StLE (s.expose ps₁) (t.expose ps₂) := by
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun id hid => ?_⟩
  simp only [St.expose, List.mem_append] at hid ⊢
  rcases hid with hid | hid
  · exact Or.inl (h.2.2.2.2.2 id hid)
  · exact Or.inr (hps id hid)

def BytesLE : List AByte → List AByte → Prop
  | [], [] => True
  | b :: bs, c :: cs => AByteLE b c ∧ BytesLE bs cs
  | _, _ => False

theorem encodeVal_le {v w : Val} (h : ValLE v w) :
    BytesLE (encodeVal v) (encodeVal w) := by
  cases v <;> cases w <;> simp [ValLE] at h
  · subst h; exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, trivial⟩
  · exact ⟨⟨h, rfl⟩, ⟨h, rfl⟩, trivial⟩

theorem writeBytes_le {mem₁ mem₂ : Addr → AByte} (hmem : ∀ a, AByteLE (mem₁ a) (mem₂ a))
    (addr : Addr) {bs₁ bs₂ : List AByte} (hbs : BytesLE bs₁ bs₂) :
    ∀ a, AByteLE (writeBytes mem₁ addr bs₁ a) (writeBytes mem₂ addr bs₂ a) := by
  induction bs₁ generalizing bs₂ mem₁ mem₂ addr with
  | nil =>
    cases bs₂ with
    | nil => exact hmem
    | cons _ _ => exact False.elim hbs
  | cons b bs₁ ih =>
    cases bs₂ with
    | nil => exact False.elim hbs
    | cons c bs₂ =>
      obtain ⟨h0, hrest⟩ := hbs
      exact ih (fun a => by split; exact h0; exact hmem a) (addr + 1) hrest

theorem readBytes_le {mem₁ mem₂ : Addr → AByte} (hmem : ∀ a, AByteLE (mem₁ a) (mem₂ a))
    (addr n : Nat) : BytesLE (readBytes mem₁ addr n) (readBytes mem₂ addr n) := by
  induction n generalizing addr with
  | zero => trivial
  | succ n ih => exact ⟨hmem addr, ih (addr + 1)⟩

theorem canAccess_mono {m₁ m₂ : Model} (hm₁ : m₁ ≠ .flat) (hm₂ : m₂ ≠ .flat)
    {s t : St} (hblk : s.blocks = t.blocks) {x y : Ptr} (hxy : PtrLE x y) (n : Nat)
    (hacc : canAccess m₁ s x n = true) : canAccess m₂ t y n = true := by
  have hx : canAccess .strict s x n = true := by
    cases m₁ <;> simp_all [canAccess]
  have hy : canAccess .strict t y n = true := by
    simp only [canAccess] at hx ⊢
    cases hxp : x.prov with
    | none => simp [hxp] at hx
    | some id =>
      rcases hxy.2 with hnone | heq
      · simp [hxp] at hnone
      · rw [← heq, hxp, ← hblk]
        simpa [hxp, hxy.1] using hx
  cases m₂ <;> simp_all [canAccess]

theorem freeTarget_mono {m₁ m₂ : Model} (hm₁ : m₁ ≠ .flat) (hm₂ : m₂ ≠ .flat)
    {s t : St} (hblk : s.blocks = t.blocks) {x y : Ptr} (hxy : PtrLE x y) {id : AllocId}
    (hft : freeTarget m₁ s x = some id) : freeTarget m₂ t y = some id := by
  have hx : freeTarget .strict s x = some id := by
    cases m₁ <;> simp_all [freeTarget]
  have hy : freeTarget .strict t y = some id := by
    simp only [freeTarget] at hx ⊢
    cases hxp : x.prov with
    | none => simp [hxp] at hx
    | some id' =>
      rcases hxy.2 with hnone | heq
      · simp [hxp] at hnone
      · rw [← heq, hxp, ← hblk]
        simpa [hxp, hxy.1] using hx
  cases m₂ <;> simp_all [freeTarget]

theorem candidates_subset_of_stLE {s t : St} (h : StLE s t) (a : Addr) :
    ∀ id ∈ candidates s a, id ∈ candidates t a := by
  intro id hid
  simp only [candidates, List.mem_filter, List.mem_range, Bool.and_eq_true, List.contains_iff_mem] at hid ⊢
  refine ⟨by rw [← h.1]; exact hid.1, h.2.2.2.2.2 id hid.2.1, ?_⟩
  rw [← h.1]; exact hid.2.2

theorem castToPtr_mono {m₁ m₂ : Model} (hm₁₂ : m₁ = .exposed → m₂ = .exposed)
    {s t s' : St} (h : StLE s t) (d : Reg) (a : Addr)
    (hs' : some s' ∈ castToPtr m₁ s d a) :
    ∃ t', some t' ∈ castToPtr m₂ t d a ∧ StLE s' t' := by
  cases m₁ with
  | flat | strict =>
    simp only [castToPtr, List.mem_singleton, Option.some.injEq] at hs'
    subst hs'
    cases m₂ with
    | flat | strict =>
      exact ⟨t.setReg d (.ptr ⟨none, a⟩), by simp [castToPtr], stLE_setReg h d ⟨rfl, Or.inl rfl⟩⟩
    | exposed =>
      cases hcand : candidates t a with
      | nil =>
        exact ⟨t.setReg d (.ptr ⟨none, a⟩), by simp [castToPtr, hcand], stLE_setReg h d ⟨rfl, Or.inl rfl⟩⟩
      | cons c cs =>
        exact ⟨t.setReg d (.ptr ⟨some c, a⟩), by simp [castToPtr, hcand], stLE_setReg h d ⟨rfl, Or.inl rfl⟩⟩
  | exposed =>
    have hm₂ : m₂ = .exposed := hm₁₂ rfl
    subst hm₂
    simp only [castToPtr] at hs'
    cases hcand_s : candidates s a with
    | nil =>
      rw [hcand_s] at hs'
      simp only [List.mem_singleton, Option.some.injEq] at hs'
      subst hs'
      cases hcand_t : candidates t a with
      | nil =>
        exact ⟨t.setReg d (.ptr ⟨none, a⟩), by simp [castToPtr, hcand_t], stLE_setReg h d ⟨rfl, Or.inl rfl⟩⟩
      | cons c cs =>
        exact ⟨t.setReg d (.ptr ⟨some c, a⟩), by simp [castToPtr, hcand_t], stLE_setReg h d ⟨rfl, Or.inl rfl⟩⟩
    | cons c cs =>
      rw [hcand_s] at hs'
      simp only [List.mem_map, Option.some.injEq] at hs'
      obtain ⟨id, hid, rfl⟩ := hs'
      have hid_s : id ∈ candidates s a := by rw [hcand_s]; exact hid
      have hid_t : id ∈ candidates t a := candidates_subset_of_stLE h a id hid_s
      refine ⟨t.setReg d (.ptr ⟨some id, a⟩), ?_, stLE_setReg h d ⟨rfl, ProvLE.refl _⟩⟩
      simp only [castToPtr]
      cases hcand_t : candidates t a with
      | nil => rw [hcand_t] at hid_t; simp at hid_t
      | cons c' cs' =>
        simp only [List.mem_map, Option.some.injEq]
        exact ⟨id, by rw [← hcand_t]; exact hid_t, rfl⟩

theorem step_mono {m₁ m₂ : Model} (hm₁ : m₁ ≠ .flat) (hm₂ : m₂ ≠ .flat)
    (hm₁₂ : m₁ = .exposed → m₂ = .exposed) {s t s' : St} {i : Instr}
    (h : StLE s t) (hs' : some s' ∈ step m₁ s i) :
    ∃ t', some t' ∈ step m₂ t i ∧ StLE s' t' := by
  cases i with
  | alloc d n =>
    by_cases hn : n = 0
    · simp [step, hn] at hs'
    · simp only [step, hn, ↓reduceIte, List.mem_singleton, Option.some.injEq] at hs'
      subst hs'
      cases m₁ with
      | flat => exact absurd rfl hm₁
      | strict | exposed =>
        cases m₂ with
        | flat => exact absurd rfl hm₂
        | strict | exposed =>
          have hsreg := (stLE_setReg h d (v := .ptr ⟨some s.blocks.length, s.top⟩)
            (w := .ptr ⟨some t.blocks.length, t.top⟩) ⟨h.2.1, by rw [h.1]; exact ProvLE.refl _⟩).2.2.2.1
          exact ⟨{ (t.setReg d (.ptr ⟨some t.blocks.length, t.top⟩)) with
                      blocks := t.blocks ++ [⟨t.top, n, true⟩], top := t.top + n },
            by simp [step, hn], by simp [h.1, h.2.1], by simp [h.2.1], h.2.2.1, hsreg,
            h.2.2.2.2.1, h.2.2.2.2.2⟩
  | free p =>
    simp only [step] at hs'
    cases hr : s.regs p with
    | none => simp [hr] at hs'
    | some v =>
      have htr := h.2.2.2.1 p
      rw [hr] at htr
      cases htr_eq : t.regs p with
      | none => simp [htr_eq, OptValLE] at htr
      | some w =>
        rw [htr_eq] at htr
        cases v <;> cases w <;> simp [OptValLE, ValLE] at htr
        · simp [hr] at hs'
        · rename_i x y
          simp only [hr] at hs'
          cases hft : freeTarget m₁ s x with
          | none => simp [hft] at hs'
          | some id =>
            simp only [hft, List.mem_singleton, Option.some.injEq] at hs'
            subst hs'
            have hft' := freeTarget_mono hm₁ hm₂ h.1 htr hft
            refine ⟨{ t with blocks := killBlock t.blocks id }, ?_, ?_⟩
            · simp [step, htr_eq, hft']
            · exact ⟨by simp [h.1], h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
  | load d ty p =>
    simp only [step] at hs'
    cases hr : s.regs p with
    | none => simp [hr] at hs'
    | some v =>
      have htr := h.2.2.2.1 p
      rw [hr] at htr
      cases htr_eq : t.regs p with
      | none => simp [htr_eq, OptValLE] at htr
      | some w =>
        rw [htr_eq] at htr
        cases v <;> cases w <;> simp [OptValLE, ValLE] at htr
        · simp [hr] at hs'
        · rename_i x y
          simp only [hr] at hs'
          by_cases hacc : canAccess m₁ s x 2 = true
          · simp only [hacc, ↓reduceIte] at hs'
            have hacc' := canAccess_mono hm₁ hm₂ h.1 htr 2 hacc
            have hb₀ := h.2.2.2.2.1 x.addr
            have hb₁ := h.2.2.2.2.1 (x.addr + 1)
            cases ty with
            | int =>
              simp only at hs'
              cases hdec : decodeInt (s.mem x.addr) (s.mem (x.addr + 1)) with
              | none => simp [hdec] at hs'
              | some np =>
                simp only [hdec, List.mem_singleton, Option.some.injEq] at hs'
                subst hs'
                obtain ⟨ps', hdec', hps'⟩ := decodeInt_mono hb₀ hb₁ hdec
                refine ⟨(t.setReg d (.int np.1)).expose ps', ?_,
                  stLE_expose (stLE_setReg h d (show ValLE (.int np.1) (.int np.1) from rfl)) hps'⟩
                simp [step, htr_eq, hacc', ← htr.1, hdec']
            | ptr =>
              simp only at hs'
              cases hdec : decodePtr (s.mem x.addr) (s.mem (x.addr + 1)) with
              | none => simp [hdec] at hs'
              | some res =>
                simp only [hdec] at hs'
                cases res with
                | inl q =>
                  simp only [List.mem_singleton, Option.some.injEq] at hs'
                  subst hs'
                  obtain ⟨q', hdec', hq'⟩ := (decodePtr_mono hb₀ hb₁).2 q hdec
                  exact ⟨t.setReg d (.ptr q'), by simp [step, htr_eq, hacc', ← htr.1, hdec'],
                    stLE_setReg h d hq'⟩
                | inr n =>
                  have hdec' := (decodePtr_mono hb₀ hb₁).1 n hdec
                  obtain ⟨t', ht'_mem, ht'_le⟩ := castToPtr_mono hm₁₂ h d n hs'
                  exact ⟨t', by simp [step, htr_eq, hacc', ← htr.1, hdec', ht'_mem], ht'_le⟩
          · simp [hacc] at hs'
  | store p r =>
    simp only [step] at hs'
    cases hp : s.regs p with
    | none => simp [hp] at hs'
    | some vp =>
      have htp := h.2.2.2.1 p
      rw [hp] at htp
      cases htp_eq : t.regs p with
      | none => simp [htp_eq, OptValLE] at htp
      | some wp =>
        rw [htp_eq] at htp
        cases vp <;> cases wp <;> simp [OptValLE, ValLE] at htp
        · simp [hp] at hs'
        · rename_i x y
          cases hr : s.regs r with
          | none => simp [hp, hr] at hs'
          | some vr =>
            have htr := h.2.2.2.1 r
            rw [hr] at htr
            cases htr_eq : t.regs r with
            | none => simp [htr_eq, OptValLE] at htr
            | some wr =>
              rw [htr_eq] at htr
              simp only [OptValLE] at htr
              simp only [hp, hr] at hs'
              by_cases hacc : canAccess m₁ s x 2 = true
              · simp only [hacc, ↓reduceIte, List.mem_singleton, Option.some.injEq] at hs'
                subst hs'
                have hacc' := canAccess_mono hm₁ hm₂ h.1 htp 2 hacc
                refine ⟨{ t with mem := writeBytes t.mem y.addr (encodeVal wr) }, ?_,
                  h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, h.2.2.2.2.2⟩
                · simp [step, htp_eq, htr_eq, hacc']
                · rw [← htp.1]; exact writeBytes_le h.2.2.2.2.1 x.addr (encodeVal_le htr)
              · simp [hacc] at hs'
  | memcpy d r n =>
    simp only [step] at hs'
    cases hd : s.regs d with
    | none => simp [hd] at hs'
    | some vd =>
      have htd := h.2.2.2.1 d
      rw [hd] at htd
      cases htd_eq : t.regs d with
      | none => simp [htd_eq, OptValLE] at htd
      | some wd =>
        rw [htd_eq] at htd
        cases vd <;> cases wd <;> simp [OptValLE, ValLE] at htd
        · simp [hd] at hs'
        · rename_i x xd
          cases hr : s.regs r with
          | none => simp [hd, hr] at hs'
          | some vr =>
            have htr := h.2.2.2.1 r
            rw [hr] at htr
            cases htr_eq : t.regs r with
            | none => simp [htr_eq, OptValLE] at htr
            | some wr =>
              rw [htr_eq] at htr
              cases vr <;> cases wr <;> simp [OptValLE, ValLE] at htr
              · simp [hd, hr] at hs'
              · rename_i y yr
                simp only [hd, hr] at hs'
                by_cases hacc : (canAccess m₁ s x n && canAccess m₁ s y n) = true
                · simp only [hacc, ↓reduceIte, List.mem_singleton, Option.some.injEq] at hs'
                  subst hs'
                  simp only [Bool.and_eq_true] at hacc
                  have haccx' := canAccess_mono hm₁ hm₂ h.1 htd n hacc.1
                  have haccy' := canAccess_mono hm₁ hm₂ h.1 htr n hacc.2
                  refine ⟨{ t with mem := writeBytes t.mem xd.addr (readBytes t.mem yr.addr n) }, ?_,
                    h.1, h.2.1, h.2.2.1, h.2.2.2.1, ?_, h.2.2.2.2.2⟩
                  · simp [step, htd_eq, htr_eq, haccx', haccy']
                  · rw [← htd.1, ← htr.1]
                    exact writeBytes_le h.2.2.2.2.1 x.addr (readBytes_le h.2.2.2.2.1 y.addr n)
                · simp [hacc] at hs'
  | ptr2int d p =>
    simp only [step] at hs'
    cases hp : s.regs p with
    | none => simp [hp] at hs'
    | some v =>
      have htp := h.2.2.2.1 p
      rw [hp] at htp
      cases htp_eq : t.regs p with
      | none => simp [htp_eq, OptValLE] at htp
      | some w =>
        rw [htp_eq] at htp
        cases v <;> cases w <;> simp [OptValLE, ValLE] at htp
        · simp [hp] at hs'
        · rename_i x y
          simp only [hp, List.mem_singleton, Option.some.injEq] at hs'
          subst hs'
          have hps : ∀ id ∈ x.prov.toList, id ∈ y.prov.toList := by
            rcases htp.2 with hnone | heq
            · simp [hnone]
            · simp [heq]
          refine ⟨(t.setReg d (.int y.addr)).expose y.prov.toList, ?_, ?_⟩
          · simp [step, htp_eq]
          · exact stLE_expose (stLE_setReg h d (show ValLE (.int x.addr) (.int y.addr) from htp.1)) hps
  | int2ptr d i =>
    simp only [step] at hs'
    cases hi : s.regs i with
    | none => simp [hi] at hs'
    | some v =>
      have hti := h.2.2.2.1 i
      rw [hi] at hti
      cases hti_eq : t.regs i with
      | none => simp [hti_eq, OptValLE] at hti
      | some w =>
        rw [hti_eq] at hti
        cases v <;> cases w <;> simp [OptValLE, ValLE] at hti
        · rename_i a b
          subst hti
          simp only [hi] at hs'
          obtain ⟨t', ht'_mem, ht'_le⟩ := castToPtr_mono hm₁₂ h d a hs'
          exact ⟨t', by simp [step, hti_eq, ht'_mem], ht'_le⟩
        · simp [hi] at hs'
  | ptrEq d p q =>
    simp only [step] at hs'
    cases hp : s.regs p with
    | none => simp [hp] at hs'
    | some vp =>
      have htp := h.2.2.2.1 p
      rw [hp] at htp
      cases htp_eq : t.regs p with
      | none => simp [htp_eq, OptValLE] at htp
      | some wp =>
        rw [htp_eq] at htp
        cases vp <;> cases wp <;> simp [OptValLE, ValLE] at htp
        · simp [hp] at hs'
        · rename_i x x'
          cases hq : s.regs q with
          | none => simp [hp, hq] at hs'
          | some vq =>
            have htq := h.2.2.2.1 q
            rw [hq] at htq
            cases htq_eq : t.regs q with
            | none => simp [htq_eq, OptValLE] at htq
            | some wq =>
              rw [htq_eq] at htq
              cases vq <;> cases wq <;> simp [OptValLE, ValLE] at htq
              · simp [hp, hq] at hs'
              · rename_i y y'
                simp only [hp, hq, List.mem_singleton, Option.some.injEq] at hs'
                subst hs'
                refine ⟨t.setReg d (.int (if x'.addr = y'.addr then 1 else 0)), ?_, ?_⟩
                · simp [step, htp_eq, htq_eq]
                · rw [← htp.1, ← htq.1]; exact stLE_setReg h d rfl
  | intEq d i j =>
    simp only [step] at hs'
    cases hi : s.regs i with
    | none => simp [hi] at hs'
    | some vi =>
      have hti := h.2.2.2.1 i
      rw [hi] at hti
      cases hti_eq : t.regs i with
      | none => simp [hti_eq, OptValLE] at hti
      | some wi =>
        rw [hti_eq] at hti
        cases vi <;> cases wi <;> simp [OptValLE, ValLE] at hti
        · rename_i a a'
          subst hti
          cases hj : s.regs j with
          | none => simp [hi, hj] at hs'
          | some vj =>
            have htj := h.2.2.2.1 j
            rw [hj] at htj
            cases htj_eq : t.regs j with
            | none => simp [htj_eq, OptValLE] at htj
            | some wj =>
              rw [htj_eq] at htj
              cases vj <;> cases wj <;> simp [OptValLE, ValLE] at htj
              · rename_i b b'
                subst htj
                simp only [hi, hj, List.mem_singleton, Option.some.injEq] at hs'
                subst hs'
                exact ⟨t.setReg d (.int (if a = b then 1 else 0)), by simp [step, hti_eq, htj_eq],
                  stLE_setReg h d rfl⟩
              · simp [hi, hj] at hs'
        · simp [hi] at hs'
  | offset d p k =>
    simp only [step] at hs'
    cases hp : s.regs p with
    | none => simp [hp] at hs'
    | some vp =>
      have htp := h.2.2.2.1 p
      rw [hp] at htp
      cases htp_eq : t.regs p with
      | none => simp [htp_eq, OptValLE] at htp
      | some wp =>
        rw [htp_eq] at htp
        cases vp <;> cases wp <;> simp [OptValLE, ValLE] at htp
        · simp [hp] at hs'
        · rename_i x y
          simp only [hp] at hs'
          cases hoa : offsetAddr x.addr k with
          | none => simp [hoa] at hs'
          | some a =>
            simp only [hoa, List.mem_singleton, Option.some.injEq] at hs'
            subst hs'
            refine ⟨t.setReg d (.ptr ⟨y.prov, a⟩), ?_, stLE_setReg h d ⟨rfl, htp.2⟩⟩
            simp [step, htp_eq, ← htp.1, hoa]
  | const d n =>
    simp only [step, List.mem_singleton, Option.some.injEq] at hs'
    subst hs'
    exact ⟨t.setReg d (.int n), by simp [step], stLE_setReg h d rfl⟩
  | copy d r =>
    simp only [step] at hs'
    cases hr : s.regs r with
    | none => simp [hr] at hs'
    | some v =>
      have htr := h.2.2.2.1 r
      rw [hr] at htr
      cases htr_eq : t.regs r with
      | none => simp [htr_eq, OptValLE] at htr
      | some w =>
        rw [htr_eq] at htr
        simp only [OptValLE] at htr
        simp only [hr, List.mem_singleton, Option.some.injEq] at hs'
        subst hs'
        exact ⟨t.setReg d w, by simp [step, htr_eq], stLE_setReg h d htr⟩
  | obs r =>
    simp only [step] at hs'
    cases hr : s.regs r with
    | none => simp [hr] at hs'
    | some v =>
      have htr := h.2.2.2.1 r
      rw [hr] at htr
      cases htr_eq : t.regs r with
      | none => simp [htr_eq, OptValLE] at htr
      | some w =>
        rw [htr_eq] at htr
        cases v <;> cases w <;> simp [OptValLE, ValLE] at htr
        · rename_i a a'
          subst htr
          simp only [hr, List.mem_singleton, Option.some.injEq] at hs'
          subst hs'
          exact ⟨{ t with out := t.out ++ [a] }, by simp [step, htr_eq],
            h.1, h.2.1, by simp [h.2.2.1], h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
        · rename_i x y
          simp only [hr, List.mem_singleton, Option.some.injEq] at hs'
          subst hs'
          exact ⟨{ t with out := t.out ++ [y.addr] }, by simp [step, htr_eq],
            h.1, h.2.1, by simp [h.2.2.1, htr.1], h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem execOk_mono {m₁ m₂ : Model} (hm₁ : m₁ ≠ .flat) (hm₂ : m₂ ≠ .flat)
    (hm₁₂ : m₁ = .exposed → m₂ = .exposed) {P : Prog} {s t s' : St}
    (h : StLE s t) (hs' : s' ∈ execOk m₁ P s) :
    ∃ t' ∈ execOk m₂ P t, StLE s' t' := by
  induction P generalizing s t with
  | nil => simp [execOk_nil] at hs'; subst hs'; exact ⟨t, by simp [execOk_nil], h⟩
  | cons i P ih =>
    rw [execOk_cons, List.mem_flatMap] at hs'
    rcases hs' with ⟨s₁, hs₁, hs_end⟩
    rw [List.mem_filterMap] at hs₁
    rcases hs₁ with ⟨o, ho, ho_eq⟩
    cases o with
    | none => simp at ho_eq
    | some s₁' =>
      simp only [id_eq, Option.some.injEq] at ho_eq
      subst ho_eq
      obtain ⟨t₁, ht₁, hle₁⟩ := step_mono hm₁ hm₂ hm₁₂ h ho
      obtain ⟨t', ht', hle'⟩ := ih hle₁ hs_end
      refine ⟨t', ?_, hle'⟩
      rw [execOk_cons, List.mem_flatMap]
      refine ⟨t₁, ?_, ht'⟩
      rw [List.mem_filterMap]
      exact ⟨some t₁, ht₁, rfl⟩

end Toy.Prov
