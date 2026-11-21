import ToyProv.Disjoint

/-!
# Erasing provenance: the flat model simulates the exposed model

`EraseRel s f`: `f` is `s` with every provenance (in registers and in memory) erased, with the same
blocks, top and output. Every defined exposed step of `s` is matched by the unique flat step of
`f` (`step_eraseRel`). This gives R6b (`flat_semRefines_exposed`) and R6c
(`exposed_beh_elements_equal`: all UB-free exposed runs end with the same output, because they all
erase to the one flat run).
-/

namespace Toy.Prov

def erasePtr (p : Ptr) : Ptr := ⟨none, p.addr⟩

def eraseVal : Val → Val
  | .int n => .int n
  | .ptr p => .ptr (erasePtr p)

def eraseByte : AByte → AByte
  | .uninit => .uninit
  | .intFrag n i => .intFrag n i
  | .ptrFrag p i => .ptrFrag (erasePtr p) i

def EraseRel (s f : St) : Prop :=
  DisjointBlocks s ∧
  f.blocks = s.blocks ∧
  f.top = s.top ∧
  f.out = s.out ∧
  (∀ r, f.regs r = (s.regs r).map eraseVal) ∧
  (∀ a, f.mem a = eraseByte (s.mem a))

theorem eraseRel_init : EraseRel init init :=
  ⟨disjointBlocks_init, rfl, rfl, rfl, fun _ => by simp [init], fun _ => by simp [init, eraseByte]⟩

theorem eraseRel_setReg {s f : St} (h : EraseRel s f) (r : Reg) (v : Val) :
    EraseRel (s.setReg r v) (f.setReg r (eraseVal v)) := by
  refine ⟨⟨h.1.1, h.1.2⟩, h.2.1, h.2.2.1, h.2.2.2.1, fun x => ?_, h.2.2.2.2.2⟩
  simp only [St.setReg]
  split
  · rfl
  · exact h.2.2.2.2.1 x

theorem writeBytes_map (g : AByte → AByte) (mem : Addr → AByte) (a : Addr) (bs : List AByte) :
    writeBytes (fun x => g (mem x)) a (bs.map g) = fun x => g (writeBytes mem a bs x) := by
  induction bs generalizing mem a with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, writeBytes]
    have hfun : (fun x => if x = a then g b else g (mem x)) = (fun x => g (if x = a then b else mem x)) := by
      funext x; split <;> rfl
    rw [hfun, ih]

theorem readBytes_map (g : AByte → AByte) (mem : Addr → AByte) (a n : Nat) :
    readBytes (fun x => g (mem x)) a n = (readBytes mem a n).map g := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [readBytes, ih]

theorem encodeVal_eraseVal (v : Val) : encodeVal (eraseVal v) = (encodeVal v).map eraseByte := by
  cases v <;> rfl

theorem findLiveBase_unique (bs : List Block) (a : Addr) (id k : Nat) (b₀ : Block)
    (h₀ : bs[id]? = some b₀) (hlive : b₀.live = true) (hbase : b₀.base = a)
    (hneq : ∀ j bj, j ≠ id → bs[j]? = some bj → bj.base ≠ a) :
    findLiveBase a bs k = some (k + id) := by
  induction bs generalizing id k with
  | nil => simp at h₀
  | cons b bs ih =>
    cases id with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h₀
      subst h₀
      simp [findLiveBase, hlive, hbase]
    | succ id =>
      have hbne : b.base ≠ a := hneq 0 b (by omega) rfl
      have hcond : (b.live && b.base == a) = false := by
        cases b.live <;> simp [hbne]
      simp only [findLiveBase, hcond, Bool.false_eq_true, ↓reduceIte]
      rw [ih id (k + 1) h₀ (fun j bj hj hbj => hneq (j + 1) bj (by omega) hbj)]
      congr 1; omega

theorem canAccess_flat_of_exposed {s f : St} (hf : f.blocks = s.blocks) {x : Ptr} {n : Nat}
    (h : canAccess .exposed s x n = true) : canAccess .flat f (erasePtr x) n = true := by
  simp only [canAccess, lookup_eq_getElem?] at h ⊢
  cases hxp : x.prov with
  | none => simp [hxp] at h
  | some id =>
    simp only [hxp] at h
    cases hb : s.blocks[id]? with
    | none => simp [hb] at h
    | some b =>
      simp only [hb] at h
      rw [hf, List.any_eq_true]
      exact ⟨b, List.mem_of_getElem? hb, h⟩

theorem decodeInt_erase (b₀ b₁ : AByte) {n : Nat} {ps : List AllocId}
    (h : decodeInt b₀ b₁ = some (n, ps)) :
    decodeInt (eraseByte b₀) (eraseByte b₁) = some (n, []) := by
  cases b₀ with
  | uninit => cases b₁ <;> simp [decodeInt] at h
  | intFrag n₀ i₀ =>
    cases b₁ with
    | uninit => simp [decodeInt] at h
    | ptrFrag _ _ => simp [decodeInt] at h
    | intFrag n₁ i₁ =>
      rw [decodeInt_intFrag_eq] at h
      split at h <;> simp_all [eraseByte, decodeInt_intFrag_eq]
  | ptrFrag p₀ i₀ =>
    cases b₁ with
    | uninit => simp [decodeInt] at h
    | intFrag _ _ => simp [decodeInt] at h
    | ptrFrag p₁ i₁ =>
      rw [decodeInt_ptrFrag_eq] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases hc with ⟨rfl, rfl, haddr⟩
        simp_all [eraseByte, erasePtr, decodeInt_ptrFrag_eq, provsOf]
      · simp at h

theorem decodePtr_erase (b₀ b₁ : AByte) :
    (∀ q, decodePtr b₀ b₁ = some (.inl q) →
      decodePtr (eraseByte b₀) (eraseByte b₁) = some (.inl (erasePtr q))) ∧
    (∀ n, decodePtr b₀ b₁ = some (.inr n) →
      decodePtr (eraseByte b₀) (eraseByte b₁) = some (.inr n)) := by
  constructor
  · intro q h
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
        rw [decodePtr_ptrFrag_eq] at h
        split at h
        · rename_i hc
          rcases hc with ⟨rfl, rfl, haddr⟩
          simp only [Option.some.injEq, Sum.inl.injEq] at h
          subst h
          simp [eraseByte, erasePtr, decodePtr_ptrFrag_eq, haddr, mergeProv]
        · simp at h
  · intro n h
    cases b₀ with
    | uninit => cases b₁ <;> simp [decodePtr] at h
    | ptrFrag p₀ i₀ =>
      cases b₁ with
      | uninit => simp [decodePtr] at h
      | intFrag _ _ => simp [decodePtr] at h
      | ptrFrag p₁ i₁ =>
        rw [decodePtr_ptrFrag_eq] at h
        split at h <;> simp at h
    | intFrag n₀ i₀ =>
      cases b₁ with
      | uninit => simp [decodePtr] at h
      | ptrFrag _ _ => simp [decodePtr] at h
      | intFrag n₁ i₁ =>
        rw [decodePtr_intFrag_eq] at h
        split at h <;> simp_all [eraseByte, decodePtr_intFrag_eq]

theorem step_eraseRel {s f s' : St} {i : Instr} (h : EraseRel s f)
    (hs' : some s' ∈ step .exposed s i) :
    ∃ f', some f' ∈ step .flat f i ∧ EraseRel s' f' := by
  have hd' : DisjointBlocks s' := step_preserves_disjointBlocks h.1 hs'
  cases i with
  | alloc d n =>
    by_cases hn : n = 0
    · simp [step, hn] at hs'
    · simp only [step, hn, ↓reduceIte, List.mem_singleton, Option.some.injEq] at hs'
      subst hs'
      refine ⟨{ (f.setReg d (.ptr ⟨none, f.top⟩)) with
                  blocks := f.blocks ++ [⟨f.top, n, true⟩], top := f.top + n },
        by simp [step, hn], hd', by simp [h.2.1, h.2.2.1], by simp [h.2.2.1], h.2.2.2.1,
        fun r => ?_, h.2.2.2.2.2⟩
      simp only [St.setReg, h.2.2.1]
      split
      · rfl
      · exact h.2.2.2.2.1 r
  | free p =>
    simp only [step] at hs'
    cases hr : s.regs p with
    | none => simp [hr] at hs'
    | some v =>
      cases v with
      | int _ => simp [hr] at hs'
      | ptr x =>
        simp only [hr] at hs'
        cases hft : freeTarget .exposed s x with
        | none => simp [hft] at hs'
        | some bid =>
          simp only [hft, List.mem_singleton, Option.some.injEq] at hs'
          subst hs'
          simp only [freeTarget, lookup_eq_getElem?] at hft
          cases hxp : x.prov with
          | none => simp [hxp] at hft
          | some bid' =>
            simp only [hxp] at hft
            cases hb : s.blocks[bid']? with
            | none => simp [hb] at hft
            | some b =>
              simp only [hb] at hft
              split at hft <;> try (simp at hft; done)
              simp only [Option.some.injEq] at hft
              rcases hft with rfl
              rename_i hcond
              simp only [Bool.and_eq_true, beq_iff_eq] at hcond
              have hflb : findLiveBase x.addr f.blocks 0 = some bid' := by
                rw [h.2.1]
                simpa using findLiveBase_unique s.blocks x.addr bid' 0 b hb hcond.1 hcond.2
                  (fun j bj hj hbj => by
                    rcases Nat.lt_trichotomy j bid' with hlt | heq | hgt
                    · have ⟨h1a, _⟩ := h.1.1 j bj hbj
                      have h2 := h.1.2 j bid' bj b hlt hbj hb
                      dsimp only [Addr] at *; omega
                    · exact absurd heq hj
                    · have ⟨h1a, _⟩ := h.1.1 bid' b hb
                      have h2 := h.1.2 bid' j b bj hgt hb hbj
                      dsimp only [Addr] at *; omega)
              have hfr : f.regs p = some (.ptr (erasePtr x)) := by simp [h.2.2.2.2.1 p, hr, eraseVal]
              refine ⟨{ f with blocks := killBlock f.blocks bid' }, ?_, hd', by simp [h.2.1], h.2.2.1,
                h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩
              simp [step, hfr, freeTarget, erasePtr, hflb]
  | load d ty p =>
    simp only [step] at hs'
    cases hr : s.regs p with
    | none => simp [hr] at hs'
    | some v =>
      cases v with
      | int _ => simp [hr] at hs'
      | ptr x =>
        simp only [hr] at hs'
        by_cases hacc : canAccess .exposed s x 2 = true
        · simp only [hacc, ↓reduceIte] at hs'
          have hfr : f.regs p = some (.ptr (erasePtr x)) := by simp [h.2.2.2.2.1 p, hr, eraseVal]
          have hfacc : canAccess .flat f (erasePtr x) 2 = true := canAccess_flat_of_exposed h.2.1 hacc
          cases ty with
          | int =>
            simp only at hs'
            cases hdec : decodeInt (s.mem x.addr) (s.mem (x.addr + 1)) with
            | none => simp [hdec] at hs'
            | some np =>
              simp only [hdec, List.mem_singleton, Option.some.injEq] at hs'
              subst hs'
              have hdec' : decodeInt (f.mem (erasePtr x).addr) (f.mem ((erasePtr x).addr + 1)) =
                  some (np.1, []) := by
                simpa [erasePtr, h.2.2.2.2.2] using decodeInt_erase _ _ hdec
              refine ⟨(f.setReg d (.int np.1)).expose [], ?_, hd', h.2.1, h.2.2.1, h.2.2.2.1,
                fun r => ?_, h.2.2.2.2.2⟩
              · simp [step, hfr, hfacc, hdec']
              · simp only [St.expose, St.setReg]; split <;> simp [eraseVal, h.2.2.2.2.1 r]
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
                have hdec' := (decodePtr_erase (s.mem x.addr) (s.mem (x.addr + 1))).1 q hdec
                refine ⟨f.setReg d (.ptr (erasePtr q)), ?_, ?_⟩
                · rw [step]; simp only [hfr, hfacc, ↓reduceIte]
                  rw [show (erasePtr x).addr = x.addr from rfl,
                    h.2.2.2.2.2 x.addr, h.2.2.2.2.2 (x.addr + 1), hdec']
                  simp
                · exact ⟨hd', (eraseRel_setReg h d (.ptr q)).2⟩
              | inr n =>
                have hdec' := (decodePtr_erase (s.mem x.addr) (s.mem (x.addr + 1))).2 n hdec
                simp only [castToPtr] at hs'
                have hres : ∃ prov, s' = s.setReg d (.ptr ⟨prov, n⟩) := by
                  cases hcand : candidates s n with
                  | nil => simp [hcand] at hs'; exact ⟨none, hs'⟩
                  | cons c cs =>
                    rw [hcand] at hs'
                    simp only [List.mem_map, Option.some.injEq] at hs'
                    obtain ⟨bid, -, heq⟩ := hs'; exact ⟨some bid, heq.symm⟩
                obtain ⟨prov, rfl⟩ := hres
                refine ⟨f.setReg d (.ptr ⟨none, n⟩), ?_, ?_⟩
                · rw [step]; simp only [hfr, hfacc, ↓reduceIte]
                  rw [show (erasePtr x).addr = x.addr from rfl,
                    h.2.2.2.2.2 x.addr, h.2.2.2.2.2 (x.addr + 1), hdec']
                  simp [castToPtr]
                · exact ⟨hd', (eraseRel_setReg h d (.ptr ⟨prov, n⟩)).2⟩
        · simp [hacc] at hs'
  | store p r =>
    simp only [step] at hs'
    cases hp : s.regs p with
    | none => simp [hp] at hs'
    | some vp =>
      cases vp with
      | int _ => simp [hp] at hs'
      | ptr x =>
        cases hr : s.regs r with
        | none => simp [hp, hr] at hs'
        | some vr =>
          simp only [hp, hr] at hs'
          by_cases hacc : canAccess .exposed s x 2 = true
          · simp only [hacc, ↓reduceIte, List.mem_singleton, Option.some.injEq] at hs'
            subst hs'
            have hfp : f.regs p = some (.ptr (erasePtr x)) := by simp [h.2.2.2.2.1 p, hp, eraseVal]
            have hfr : f.regs r = some (eraseVal vr) := by simp [h.2.2.2.2.1 r, hr]
            have hfacc : canAccess .flat f (erasePtr x) 2 = true := canAccess_flat_of_exposed h.2.1 hacc
            refine ⟨{ f with mem := writeBytes f.mem (erasePtr x).addr (encodeVal (eraseVal vr)) },
              ?_, hd', h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun a => ?_⟩
            · simp [step, hfp, hfr, hfacc]
            · have hm : f.mem = fun z => eraseByte (s.mem z) := funext h.2.2.2.2.2
              rw [hm, encodeVal_eraseVal, writeBytes_map]
              rfl
          · simp [hacc] at hs'
  | memcpy d r n =>
    simp only [step] at hs'
    cases hd_reg : s.regs d with
    | none => simp [hd_reg] at hs'
    | some vd =>
      cases vd with
      | int _ => simp [hd_reg] at hs'
      | ptr x =>
        cases hr_reg : s.regs r with
        | none => simp [hd_reg, hr_reg] at hs'
        | some vr =>
          cases vr with
          | int _ => simp [hd_reg, hr_reg] at hs'
          | ptr y =>
            simp only [hd_reg, hr_reg] at hs'
            by_cases hacc : (canAccess .exposed s x n && canAccess .exposed s y n) = true
            · simp only [hacc, ↓reduceIte, List.mem_singleton, Option.some.injEq] at hs'
              subst hs'
              simp only [Bool.and_eq_true] at hacc
              have hfd : f.regs d = some (.ptr (erasePtr x)) := by simp [h.2.2.2.2.1 d, hd_reg, eraseVal]
              have hfr : f.regs r = some (.ptr (erasePtr y)) := by simp [h.2.2.2.2.1 r, hr_reg, eraseVal]
              have hfacc : (canAccess .flat f (erasePtr x) n && canAccess .flat f (erasePtr y) n) = true := by
                simp [canAccess_flat_of_exposed h.2.1 hacc.1, canAccess_flat_of_exposed h.2.1 hacc.2]
              refine ⟨{ f with mem := writeBytes f.mem (erasePtr x).addr (readBytes f.mem (erasePtr y).addr n) },
                ?_, hd', h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun a => ?_⟩
              · simp [step, hfd, hfr, hfacc]
              · have hm : f.mem = fun z => eraseByte (s.mem z) := funext h.2.2.2.2.2
                rw [hm, erasePtr, readBytes_map, writeBytes_map]
                rfl
            · simp [hacc] at hs'
  | ptr2int d p =>
    simp only [step] at hs'
    cases hp : s.regs p with
    | none => simp [hp] at hs'
    | some v =>
      cases v with
      | int _ => simp [hp] at hs'
      | ptr x =>
        simp only [hp, List.mem_singleton, Option.some.injEq] at hs'
        subst hs'
        have hfp : f.regs p = some (.ptr (erasePtr x)) := by simp [h.2.2.2.2.1 p, hp, eraseVal]
        refine ⟨(f.setReg d (.int x.addr)).expose [], ?_, hd', h.2.1, h.2.2.1, h.2.2.2.1,
          fun r => ?_, h.2.2.2.2.2⟩
        · simp [step, hfp, erasePtr]
        · simp only [St.expose, St.setReg]; split <;> simp [eraseVal, h.2.2.2.2.1 r]
  | int2ptr d i =>
    simp only [step] at hs'
    cases hi : s.regs i with
    | none => simp [hi] at hs'
    | some v =>
      cases v with
      | ptr _ => simp [hi] at hs'
      | int a =>
        simp only [hi, castToPtr] at hs'
        have hres : ∃ prov, s' = s.setReg d (.ptr ⟨prov, a⟩) := by
          cases hcand : candidates s a with
          | nil => simp [hcand] at hs'; exact ⟨none, hs'⟩
          | cons c cs =>
            rw [hcand] at hs'
            simp only [List.mem_map, Option.some.injEq] at hs'
            obtain ⟨bid, -, heq⟩ := hs'; exact ⟨some bid, heq.symm⟩
        obtain ⟨prov, rfl⟩ := hres
        have hfi : f.regs i = some (.int a) := by simp [h.2.2.2.2.1 i, hi, eraseVal]
        refine ⟨f.setReg d (.ptr ⟨none, a⟩), ?_, hd', (eraseRel_setReg h d (.ptr ⟨prov, a⟩)).2⟩
        simp [step, hfi, castToPtr]
  | ptrEq d p q =>
    simp only [step] at hs'
    cases hp : s.regs p with
    | none => simp [hp] at hs'
    | some vp =>
      cases vp with
      | int _ => simp [hp] at hs'
      | ptr x =>
        cases hq : s.regs q with
        | none => simp [hp, hq] at hs'
        | some vq =>
          cases vq with
          | int _ => simp [hp, hq] at hs'
          | ptr y =>
            simp only [hp, hq, List.mem_singleton, Option.some.injEq] at hs'
            subst hs'
            have hfp : f.regs p = some (.ptr (erasePtr x)) := by simp [h.2.2.2.2.1 p, hp, eraseVal]
            have hfq : f.regs q = some (.ptr (erasePtr y)) := by simp [h.2.2.2.2.1 q, hq, eraseVal]
            refine ⟨f.setReg d (.int (if x.addr = y.addr then 1 else 0)), ?_,
              hd', (eraseRel_setReg h d _).2⟩
            simp [step, hfp, hfq, erasePtr]
  | intEq d i j =>
    simp only [step] at hs'
    cases hi : s.regs i with
    | none => simp [hi] at hs'
    | some vi =>
      cases vi with
      | ptr _ => simp [hi] at hs'
      | int a =>
        cases hj : s.regs j with
        | none => simp [hi, hj] at hs'
        | some vj =>
          cases vj with
          | ptr _ => simp [hi, hj] at hs'
          | int b =>
            simp only [hi, hj, List.mem_singleton, Option.some.injEq] at hs'
            subst hs'
            have hfi : f.regs i = some (.int a) := by simp [h.2.2.2.2.1 i, hi, eraseVal]
            have hfj : f.regs j = some (.int b) := by simp [h.2.2.2.2.1 j, hj, eraseVal]
            refine ⟨f.setReg d (.int (if a = b then 1 else 0)), ?_, hd', (eraseRel_setReg h d _).2⟩
            simp [step, hfi, hfj]
  | offset d p k =>
    simp only [step] at hs'
    cases hp : s.regs p with
    | none => simp [hp] at hs'
    | some vp =>
      cases vp with
      | int _ => simp [hp] at hs'
      | ptr x =>
        simp only [hp] at hs'
        cases hoa : offsetAddr x.addr k with
        | none => simp [hoa] at hs'
        | some a =>
          simp only [hoa, List.mem_singleton, Option.some.injEq] at hs'
          subst hs'
          have hfp : f.regs p = some (.ptr (erasePtr x)) := by simp [h.2.2.2.2.1 p, hp, eraseVal]
          refine ⟨f.setReg d (.ptr ⟨none, a⟩), ?_, hd', (eraseRel_setReg h d (.ptr ⟨x.prov, a⟩)).2⟩
          simp [step, hfp, erasePtr, hoa]
  | const d n =>
    simp only [step, List.mem_singleton, Option.some.injEq] at hs'
    subst hs'
    exact ⟨f.setReg d (.int n), by simp [step], hd', (eraseRel_setReg h d (.int n)).2⟩
  | copy d r =>
    simp only [step] at hs'
    cases hr : s.regs r with
    | none => simp [hr] at hs'
    | some v =>
      simp only [hr, List.mem_singleton, Option.some.injEq] at hs'
      subst hs'
      have hfr : f.regs r = some (eraseVal v) := by simp [h.2.2.2.2.1 r, hr]
      exact ⟨f.setReg d (eraseVal v), by simp [step, hfr], hd', (eraseRel_setReg h d v).2⟩
  | obs r =>
    simp only [step] at hs'
    cases hr : s.regs r with
    | none => simp [hr] at hs'
    | some v =>
      cases v with
      | int n =>
        simp only [hr, List.mem_singleton, Option.some.injEq] at hs'
        subst hs'
        have hfr : f.regs r = some (.int n) := by simp [h.2.2.2.2.1 r, hr, eraseVal]
        exact ⟨{ f with out := f.out ++ [n] }, by simp [step, hfr],
          hd', h.2.1, h.2.2.1, by simp [h.2.2.2.1], h.2.2.2.2.1, h.2.2.2.2.2⟩
      | ptr x =>
        simp only [hr, List.mem_singleton, Option.some.injEq] at hs'
        subst hs'
        have hfr : f.regs r = some (.ptr (erasePtr x)) := by simp [h.2.2.2.2.1 r, hr, eraseVal]
        exact ⟨{ f with out := f.out ++ [x.addr] }, by simp [step, hfr, erasePtr],
          hd', h.2.1, h.2.2.1, by simp [h.2.2.2.1], h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem execOk_eraseRel {P : Prog} {s f s' : St} (h : EraseRel s f) (hs' : s' ∈ execOk .exposed P s) :
    ∃ f' ∈ execOk .flat P f, EraseRel s' f' := by
  induction P generalizing s f with
  | nil => simp [execOk_nil] at hs'; subst hs'; exact ⟨f, by simp [execOk_nil], h⟩
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
      obtain ⟨f₁, hf₁, hrel₁⟩ := step_eraseRel h ho
      obtain ⟨f', hf', hrel'⟩ := ih hrel₁ hs_end
      refine ⟨f', ?_, hrel'⟩
      rw [execOk_cons, List.mem_flatMap]
      refine ⟨f₁, ?_, hf'⟩
      rw [List.mem_filterMap]
      exact ⟨some f₁, hf₁, rfl⟩

theorem after_eraseRel (P : Prog) {s : St} (hs : s ∈ after .exposed P) :
    ∃ f ∈ after .flat P, EraseRel s f :=
  execOk_eraseRel eraseRel_init hs

/-- **R6c.** In the exposed model, angelic resolution never yields two different defined
behaviours: all elements of `beh .exposed P` are equal (the list may repeat one outcome, see
`exposed_beh_may_repeat`). -/
theorem exposed_beh_elements_equal (P : Prog) :
    ∀ o₁ ∈ beh .exposed P, ∀ o₂ ∈ beh .exposed P, o₁ = o₂ := by
  intro o₁ ho₁ o₂ ho₂
  rw [beh_eq_of_after] at ho₁ ho₂
  cases ha : after .exposed P with
  | nil => simp [ha] at ho₁ ho₂; rw [ho₁, ho₂]
  | cons s rest =>
    simp only [ha, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.mem_map] at ho₁ ho₂
    rcases ho₁ with ⟨s₁, hs₁, rfl⟩
    rcases ho₂ with ⟨s₂, hs₂, rfl⟩
    obtain ⟨f₁, hf₁, hrel₁⟩ := after_eraseRel P (by rw [ha]; exact hs₁)
    obtain ⟨f₂, hf₂, hrel₂⟩ := after_eraseRel P (by rw [ha]; exact hs₂)
    have heq := execOk_det_eq (Or.inl rfl) hf₁ hf₂
    subst heq
    rw [← hrel₁.2.2.2.1, ← hrel₂.2.2.2.1]

end Toy.Prov
