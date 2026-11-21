import Toy.WrapNiche.Op

/-!
# Proof lemmas (fully proved)

Arithmetic facts about `offset` and `wrapAdd`, a membership count for wrapping intervals,
byte-level frame lemmas for `writeBytes` and `readBytes`, the little-endian round trip of the
niche field, and composition facts for `run`. They are used in the proofs of the main results
and are not results of this package.
-/

namespace Toy.WrapNiche

open Imported

/-! ## Wrapping arithmetic -/

/-- `offset s x` by cases (no floor modulo). -/
theorem offset_eq {M : Nat} (s x : Fin M) :
    offset s x = if s.val ≤ x.val then x.val - s.val else x.val + M - s.val := by
  unfold offset
  have hs := s.isLt
  have hx := x.isLt
  split
  · have : x.val + (M - s.val) = (x.val - s.val) + M := by omega
    rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_of_lt (by omega)]; omega

theorem offset_lt {M : Nat} (s x : Fin M) : offset s x < M :=
  Nat.mod_lt _ (pos_of_fin s)

theorem offset_wrapAdd_of_lt {M : Nat} (ns : Fin M) {r : Nat} (hr : r < M) :
    offset ns (wrapAdd ns r) = r := by
  unfold offset wrapAdd
  have hns := ns.isLt
  have h1 : ((ns.val + r) % M + (M - ns.val)) % M = ((ns.val + r) + (M - ns.val)) % M := by
    rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [h1]
  have h2 : ns.val + r + (M - ns.val) = r + M := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hr]

theorem offset_wrapAdd {M : Nat} (ns : Fin M) (r : Nat) :
    offset ns (wrapAdd ns r) = r % M := by
  have hM := pos_of_fin ns
  have h : wrapAdd ns r = wrapAdd ns (r % M) := by
    apply Fin.ext; unfold wrapAdd; simp [Nat.add_mod]
  rw [h, offset_wrapAdd_of_lt ns (Nat.mod_lt r hM)]

theorem wrapAdd_offset {M : Nat} (s x : Fin M) :
    wrapAdd s (offset s x) = x := by
  apply Fin.ext
  change (s.val + (x.val + (M - s.val)) % M) % M = x.val
  have hs := s.isLt
  have hx := x.isLt
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have h2 : s.val + (x.val + (M - s.val)) = x.val + M := by omega
  rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt hx]

theorem wrapAdd_add {M : Nat} (s : Fin M) (a b : Nat) :
    wrapAdd (wrapAdd s a) b = wrapAdd s (a + b) := by
  apply Fin.ext
  change ((s.val + a) % M + b) % M = (s.val + (a + b)) % M
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_assoc]

theorem offset_shift {M : Nat} (o s x : Fin M) :
    offset s x = (offset o x + (M - offset o s)) % M := by
  have hM := pos_of_fin o
  have hs := offset_lt o s
  have hx := offset_lt o x
  let d := (offset o x + (M - offset o s)) % M
  have hxs : wrapAdd s d = x := by
    have h1 : s = wrapAdd o (offset o s) := (wrapAdd_offset o s).symm
    have h2 : (o.val + offset o x) % M = x.val := congrArg Fin.val (wrapAdd_offset o x)
    apply Fin.ext
    rw [h1, wrapAdd_add]
    change (o.val + (offset o s + d)) % M = x.val
    dsimp only [d]
    rw [Nat.add_mod o.val, Nat.add_mod (offset o s), Nat.mod_mod, ← Nat.add_mod (offset o s),
        ← Nat.add_mod o.val]
    have h3 : o.val + (offset o s + (offset o x + (M - offset o s))) =
        (o.val + offset o x) + M := by omega
    rw [h3, Nat.add_mod_right, h2]
  have hlt : d < M := Nat.mod_lt _ hM
  have hret := offset_wrapAdd_of_lt s hlt
  rw [hxs] at hret
  exact hret

theorem offset_wrapSub_one {M : Nat} (s : Fin M) (hM : 2 ≤ M) :
    offset s (wrapSub s 1) = M - 1 := by
  have h1 : 1 % M = 1 := Nat.mod_eq_of_lt (by omega)
  have h2 : wrapSub s 1 = wrapAdd s (M - 1) := by
    apply Fin.ext
    change (s.val + (M - 1 % M)) % M = (s.val + (M - 1)) % M
    rw [h1]
  rw [h2, offset_wrapAdd_of_lt s (by omega)]

/-! ## Counting the members of a wrapping interval -/

theorem list_count_offset {M : Nat} (s : Fin M) (k : Nat) (hk : k < M) :
    ((List.finRange M).filter (fun x => decide (offset s x ≤ k))).length = k + 1 := by
  let f : Fin (k + 1) → Fin M := fun r => wrapAdd s r.val
  let l1 := (List.finRange (k + 1)).map f
  let l2 := (List.finRange M).filter (fun x => decide (offset s x ≤ k))
  have hnd1 : l1.Nodup :=
    Counting.nodup_map_of_injOn (fun a _ b _ hab => by
      have ha := offset_wrapAdd_of_lt s (Nat.lt_of_lt_of_le a.isLt (Nat.succ_le_of_lt hk))
      have hb := offset_wrapAdd_of_lt s (Nat.lt_of_lt_of_le b.isLt (Nat.succ_le_of_lt hk))
      rw [show f a = wrapAdd s a.val from rfl, show f b = wrapAdd s b.val from rfl] at hab
      rw [hab] at ha
      exact Fin.ext (ha.symm.trans hb)) (List.nodup_finRange _)
  have hnd2 : l2.Nodup := List.Pairwise.filter _ (List.nodup_finRange _)
  have hsub12 : ∀ x ∈ l1, x ∈ l2 := by
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨r, _, rfl⟩ := hx
    simp only [l2, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    rw [show f r = wrapAdd s r.val from rfl, offset_wrapAdd_of_lt s (by omega)]
    omega
  have hsub21 : ∀ x ∈ l2, x ∈ l1 := by
    intro x hx
    simp only [l2, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hx
    rw [List.mem_map]
    exact ⟨⟨offset s x, by omega⟩, List.mem_finRange _, wrapAdd_offset s x⟩
  have h1 := Counting.nodup_length_le_of_subset hnd1 hsub12
  have h2 := Counting.nodup_length_le_of_subset hnd2 hsub21
  simp only [l1, List.length_map, List.length_finRange] at h1 h2
  show l2.length = k + 1
  omega

/-! ## The checked decoder of the general enum -/

/-- `genLayout` decodes canonically for every enum shape, encoding and validity set. -/
theorem genLayout_canonical {n : Nat} (E : EnumSpec) (A : AffineNiche (256 ^ n))
    (V : Validity n) : Canonical (genLayout E A V) := by
  intro p y hp
  simp only [genLayout] at hp
  split at hp
  · split at hp
    · cases hp; simp only [genLayout, AffineNiche.tagOf, Nat.add_sub_cancel_left, wrapAdd_offset]
    · cases hp
  · split at hp
    · cases hp; rfl
    · cases hp

/-! ## Bytes -/

theorem writeBytes_length (p : Bytes) (off : Nat) (bs : List (Fin 256)) :
    (writeBytes p off bs).length = p.length := by
  simp [writeBytes]

theorem writeBytes_getD (p : Bytes) (off : Nat) (bs : List (Fin 256)) (i : Nat) :
    (writeBytes p off bs).getD i none =
      if i < p.length then
        if off ≤ i ∧ i < off + bs.length then some (bs.getD (i - off) 0) else p.getD i none
      else none := by
  unfold writeBytes
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < p.length
  · have hi' : i < ((List.range p.length).map fun i =>
        if off ≤ i ∧ i < off + bs.length then some (bs.getD (i - off) 0) else p.getD i none).length := by
      simp [hi]
    rw [List.getElem?_eq_getElem hi', Option.getD_some, List.getElem_map, List.getElem_range]
    simp only [hi, ↓reduceIte]
  · have hge : ((List.range p.length).map fun i =>
        if off ≤ i ∧ i < off + bs.length then some (bs.getD (i - off) 0) else p.getD i none).length ≤ i := by
      simp; omega
    rw [List.getElem?_eq_none hge]; simp [hi]

theorem mapM_id_map_some {α : Type} (l : List α) : (l.map some).mapM id = some l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.mapM_cons, ih]

theorem readBytes_writeBytes_self (p : Bytes) (off : Nat) (bs : List (Fin 256))
    (hfit : off + bs.length ≤ p.length) :
    readBytes (writeBytes p off bs) off bs.length = some bs := by
  unfold readBytes
  have hmap : ((List.range bs.length).map fun j => (writeBytes p off bs).getD (off + j) none) =
      bs.map some := by
    apply List.ext_getElem
    · simp
    · intro j hj1 hj2
      simp only [List.getElem_map, List.getElem_range]
      rw [writeBytes_getD]
      have hj : j < bs.length := by simp at hj2; exact hj2
      have h1 : off + j < p.length := by omega
      have h2 : off ≤ off + j ∧ off + j < off + bs.length := by omega
      simp only [h1, h2, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  rw [hmap, mapM_id_map_some]

theorem readBytes_writeBytes_disjoint (p : Bytes) (off1 len1 off2 : Nat)
    (bs2 : List (Fin 256)) (hdis : off2 + bs2.length ≤ off1 ∨ off1 + len1 ≤ off2) :
    readBytes (writeBytes p off2 bs2) off1 len1 = readBytes p off1 len1 := by
  unfold readBytes
  congr 1
  apply List.ext_getElem
  · simp
  · intro j hj1 hj2
    simp only [List.getElem_map, List.getElem_range]
    rw [writeBytes_getD]
    have hj : j < len1 := by simp at hj1; exact hj1
    have hnot : ¬ (off2 ≤ off1 + j ∧ off1 + j < off2 + bs2.length) := by omega
    simp only [hnot, ↓reduceIte]
    by_cases hlt : off1 + j < p.length
    · simp [hlt]
    · simp only [hlt, ↓reduceIte, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega)]; rfl

theorem writeBytes_comm (p : Bytes) (off1 : Nat) (bs1 : List (Fin 256))
    (off2 : Nat) (bs2 : List (Fin 256))
    (hdis : off1 + bs1.length ≤ off2 ∨ off2 + bs2.length ≤ off1) :
    writeBytes (writeBytes p off1 bs1) off2 bs2 = writeBytes (writeBytes p off2 bs2) off1 bs1 := by
  apply List.ext_getElem
  · simp [writeBytes_length]
  · intro i hi1 hi2
    have hi : i < p.length := by simp [writeBytes_length] at hi1; exact hi1
    have hget : ∀ (q : Bytes) (hq : i < q.length), q[i]'hq = q.getD i none := by
      intro q hq; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    rw [hget _ hi1, hget _ hi2]
    rw [writeBytes_getD, writeBytes_getD, writeBytes_getD, writeBytes_getD]
    simp only [writeBytes_length, hi, ↓reduceIte]
    by_cases h1 : off1 ≤ i ∧ i < off1 + bs1.length <;>
    by_cases h2 : off2 ≤ i ∧ i < off2 + bs2.length
    · omega
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h1, h2]

theorem leBytes_length (w x : Nat) : (leBytes w x).length = w := by
  simp [leBytes]

theorem range_succ_eq_cons (w : Nat) :
    List.range (w + 1) = 0 :: (List.range w).map (· + 1) := by
  induction w with
  | zero => rfl
  | succ w ih =>
    conv => lhs; rw [List.range_succ, ih]
    conv => rhs; rw [List.range_succ, List.map_append, List.map_singleton]
    rfl

theorem leVal_leBytes (w x : Nat) : leVal (leBytes w x) = x % 256 ^ w := by
  induction w generalizing x with
  | zero => simp [leBytes, leVal, Nat.mod_one]
  | succ w ih =>
    have hstep : leBytes (w + 1) x = ⟨x % 256, Nat.mod_lt _ (by decide)⟩ :: leBytes w (x / 256) := by
      unfold leBytes
      rw [range_succ_eq_cons, List.map_cons, List.map_map]
      congr 1
      · simp
      · apply List.map_congr_left
        intro j _
        apply Fin.ext
        change x / 256 ^ (j + 1) % 256 = (x / 256) / 256 ^ j % 256
        rw [div_div_256]
    rw [hstep]
    change x % 256 + 256 * leVal (leBytes w (x / 256)) = x % 256 ^ (w + 1)
    rw [ih (x / 256)]
    have h1 : x = x % 256 + 256 * (x / 256) := (Nat.mod_add_div x 256).symm
    have h2 : x / 256 = (x / 256) % 256 ^ w + 256 ^ w * (x / 256 / 256 ^ w) :=
      (Nat.mod_add_div (x / 256) (256 ^ w)).symm
    have hlt : x % 256 + 256 * (x / 256 % 256 ^ w) < 256 ^ (w + 1) := by
      have ha : x % 256 < 256 := Nat.mod_lt _ (by decide)
      have hb : x / 256 % 256 ^ w < 256 ^ w := Nat.mod_lt _ (pat_card_pos w)
      rw [Nat.pow_succ]; omega
    have hmul : x = (x % 256 + 256 * (x / 256 % 256 ^ w)) + 256 ^ (w + 1) * (x / 256 / 256 ^ w) := by
      have h256 : 256 * (256 ^ w * (x / 256 / 256 ^ w)) = 256 ^ (w + 1) * (x / 256 / 256 ^ w) := by
        rw [Nat.pow_succ, Nat.mul_comm (256 ^ w) 256, Nat.mul_assoc]
      calc x = x % 256 + 256 * (x / 256) := h1
        _ = x % 256 + 256 * ((x / 256) % 256 ^ w + 256 ^ w * (x / 256 / 256 ^ w)) := by rw [← h2]
        _ = x % 256 + 256 * ((x / 256) % 256 ^ w) + 256 * (256 ^ w * (x / 256 / 256 ^ w)) := by
            rw [Nat.mul_add, Nat.add_assoc]
        _ = (x % 256 + 256 * (x / 256 % 256 ^ w)) + 256 ^ (w + 1) * (x / 256 / 256 ^ w) := by
            rw [h256]
    conv => rhs; rw [hmul, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

theorem readNiche_writeNiche (L : OpLayout) (p : Bytes) (x : Pat L.nw)
    (hfit : L.no + L.nw ≤ p.length) :
    L.readNiche (L.writeNiche p x) = some x := by
  unfold OpLayout.readNiche OpLayout.writeNiche
  have hlen : (leBytes L.nw x.val).length = L.nw := leBytes_length L.nw x.val
  have hrb := readBytes_writeBytes_self p L.no (leBytes L.nw x.val) (by rw [hlen]; exact hfit)
  rw [hlen] at hrb
  rw [hrb]
  simp only [Option.map_some, Option.some.injEq]
  apply Fin.ext
  change leVal (leBytes L.nw x.val) % 256 ^ L.nw = x.val
  rw [leVal_leBytes, Nat.mod_mod, Nat.mod_eq_of_lt x.isLt]

theorem writeNiche_length (L : OpLayout) (p : Bytes) (x : Pat L.nw) :
    (L.writeNiche p x).length = p.length :=
  writeBytes_length _ _ _

/-- `SetDiscriminant` keeps the length of the place. -/
theorem setDisc_length {sem : Sem} {L : OpLayout} {v : Nat} {p q : Bytes}
    (h : setDisc sem L v p = some q) : q.length = p.length := by
  unfold setDisc at h
  split at h
  · cases sem with
    | operational => split at h <;> simp_all
    | erased => simp_all
  · split at h
    · split at h
      · cases h; exact writeNiche_length _ _ _
      · cases h
    · cases h

/-- A write that does not overlap the niche field commutes with `setDisc` at the level of the
byte helper `writeBytes`. -/
theorem setDisc_writeBytes_comm_of_disjointFromNiche (sem : Sem) (L : OpLayout) (v off : Nat)
    (bs : List (Fin 256)) (hdis : L.DisjointFromNiche off bs.length) (p : Bytes) :
    (setDisc sem L v p).map (fun q => writeBytes q off bs) =
      setDisc sem L v (writeBytes p off bs) := by
  have hrb : L.readNiche (writeBytes p off bs) = L.readNiche p := by
    unfold OpLayout.readNiche
    rw [readBytes_writeBytes_disjoint p L.no L.nw off bs hdis]
  have hrd : L.readDisc (writeBytes p off bs) = L.readDisc p := by
    unfold OpLayout.readDisc; rw [hrb]
  unfold setDisc
  by_cases hvu : v = L.E.u
  · simp only [hvu, ↓reduceIte]
    cases sem with
    | erased => rfl
    | operational => rw [hrd]; split <;> simp
  · simp only [hvu, ↓reduceIte]
    by_cases henc : L.Encodable v
    · simp only [henc, ↓reduceIte, writeBytes_length]
      by_cases hfit : L.no + L.nw ≤ p.length
      · simp only [hfit, ↓reduceIte, Option.map_some, Option.some.injEq]
        unfold OpLayout.writeNiche
        have hdis' : L.no + (leBytes L.nw (L.A.tagOf (v - L.A.first)).val).length ≤ off ∨
            off + bs.length ≤ L.no := by
          rw [leBytes_length]; exact hdis.symm
        exact writeBytes_comm p L.no _ off bs hdis'
      · simp [hfit]
    · simp [henc]

/-! ## Runs -/

theorem run_append (sem : Sem) (L : OpLayout) (p1 p2 : List Op) (s : Bytes × List Nat) :
    run sem L (p1 ++ p2) s = (run sem L p1 s).bind (run sem L p2) := by
  induction p1 generalizing s with
  | nil => rfl
  | cons o os ih =>
    simp only [List.cons_append, run]
    cases stepOp sem L o s with
    | none => rfl
    | some s' => exact ih s'

theorem run_writesOf (sem : Sem) (L : OpLayout) (ws : List (Nat × List (Fin 256)))
    (p : Bytes) (out : List Nat)
    (hin : ∀ w ∈ ws, w.1 + w.2.length ≤ p.length)
    (hpw : ws.Pairwise (fun a b => a.1 + a.2.length ≤ b.1 ∨ b.1 + b.2.length ≤ a.1)) :
    ∃ q, run sem L (writesOf ws) (p, out) = some (q, out) ∧ q.length = p.length ∧
      ∀ w ∈ ws, readBytes q w.1 w.2.length = some w.2 := by
  induction ws generalizing p with
  | nil => exact ⟨p, rfl, rfl, fun _ h => by cases h⟩
  | cons w0 ws ih =>
    rw [List.pairwise_cons] at hpw
    have hw0 : w0.1 + w0.2.length ≤ p.length := hin w0 (List.mem_cons_self ..)
    let p1 := writeBytes p w0.1 w0.2
    have hp1len : p1.length = p.length := writeBytes_length p w0.1 w0.2
    have hin' : ∀ w ∈ ws, w.1 + w.2.length ≤ p1.length := fun w hw => by
      rw [hp1len]; exact hin w (List.mem_cons_of_mem w0 hw)
    obtain ⟨q, hrun, hqlen, hreads⟩ := ih p1 hin' hpw.2
    have hw0_pres : ∀ (l : List (Nat × List (Fin 256))) (r : Bytes) (q' : Bytes),
        (∀ w ∈ l, w0.1 + w0.2.length ≤ w.1 ∨ w.1 + w.2.length ≤ w0.1) →
        run sem L (writesOf l) (r, out) = some (q', out) →
        readBytes q' w0.1 w0.2.length = readBytes r w0.1 w0.2.length := by
      intro l
      induction l with
      | nil => intro r q' _ h; cases h; rfl
      | cons a t iht =>
        intro r q' hdisl h
        simp only [writesOf, List.map_cons, run, stepOp] at h
        split at h
        · simp only [Option.bind_some] at h
          rw [iht _ _ (fun w hw => hdisl w (List.mem_cons_of_mem a hw)) h]
          exact readBytes_writeBytes_disjoint r w0.1 w0.2.length a.1 a.2
            ((hdisl a (List.mem_cons_self ..)).symm)
        · simp at h
    refine ⟨q, ?_, by rw [hqlen, hp1len], ?_⟩
    · simp only [writesOf, List.map_cons, run, stepOp, hw0, ↓reduceIte, Option.bind_some]
      exact hrun
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hmem
      · rw [hw0_pres ws p1 q hpw.1 hrun]
        exact readBytes_writeBytes_self p w.1 w.2 hw0
      · exact hreads w hmem

end Toy.WrapNiche
