import PanicSafety.Retain

/-!
# Results on the retain-like operations

* Raw moves with `len` updated at the end are safe under `abort` and unsafe under
  `unwind`; when the run unwinds, the unwound state satisfies `Inv` if and only if the
  abstract retain removed no element up to and including the panic (a removed element whose
  destructor panics counts as removed).
* Leak amplification is panic-safe under `unwind`; after a panic `len = 0` and every value
  of the entry container that was not removed is leaked.
* A back-shift guard updated before each destructor is panic-safe and leak-free under
  `unwind` for every destructor table. The same guard updated after each destructor is
  panic-safe under `unwind` when no destructor panics
  (`guardRetainLate_panicSafe_unwind_of_noPanickingDtors`), and is not panic-safe for the
  destructor table `dtPanicsOn0` (`guardRetainLate_dtorPanic_counterexample`).

All statements assume an entry state satisfying `Inv` unless stated otherwise. The back-shift
guard of this file performs memory moves and a `len` update; it runs no destructor.
-/

namespace Toy.PanicSafety

/-! ## Exact specifications -/

/-- Normal-return clause of the exact specifications: the abstract run finished, the
container holds exactly the kept values in order, exactly the removed values were added to
the drop log, and `Inv` holds. Buffer cells at index `len` and beyond are unspecified. -/
def RetainReturns (o : AbsOut) (m m' : Mem) : Prop :=
  o.ending = .finished ∧ toks m'.elems = o.kept ∧ m'.dropped = o.rejected ++ m.dropped ∧ Inv m'

instance (o : AbsOut) (m m' : Mem) : Decidable (RetainReturns o m m') := by
  unfold RetainReturns; infer_instance

/-- Every value of the entry container is, after the run, either in the drop log or held
by the container's first `len` cells. -/
def LeakFree (m m' : Mem) : Prop := ∀ t ∈ toks m.elems, t ∈ m'.dropped ∨ t ∈ toks m'.elems

instance (m m' : Mem) : Decidable (LeakFree m m') := by unfold LeakFree; infer_instance

/-- Exact behaviour of `rawRetain` under `abort`: it returns exactly when the abstract
retain finishes, with the abstract result; otherwise (a callback or destructor panicked) it
aborts. It never reaches UB. -/
def RawAbortExact (cb : Callback) (dt : DtorTable) (m : Mem) : Prop :=
  match run .abort cb dt rawRetain m with
  | .ret m' => RetainReturns (specRetain cb dt (toks m.elems)) m m'
  | .abort => (specRetain cb dt (toks m.elems)).ending ≠ .finished
  | _ => False

instance (cb : Callback) (dt : DtorTable) (m : Mem) : Decidable (RawAbortExact cb dt m) := by
  unfold RawAbortExact; split <;> infer_instance

/-- Exact behaviour of `leakRetain` under `unwind`: it returns exactly when the abstract
retain finishes, with the abstract result; otherwise it unwinds to a state with `len = 0`,
drop log extended by exactly the removed values, unchanged buffer length and counters
(buffer contents unspecified). It never aborts and never reaches UB. -/
def LeakUnwindExact (cb : Callback) (dt : DtorTable) (m : Mem) : Prop :=
  match run .unwind cb dt leakRetain m with
  | .ret m' => RetainReturns (specRetain cb dt (toks m.elems)) m m'
  | .unwound m' =>
    (specRetain cb dt (toks m.elems)).ending ≠ .finished ∧ m'.len = 0 ∧
    m'.dropped = (specRetain cb dt (toks m.elems)).rejected ++ m.dropped ∧
    m'.buf.length = m.buf.length ∧ m'.ctrA = m.ctrA ∧ m'.ctrB = m.ctrB
  | _ => False

instance (cb : Callback) (dt : DtorTable) (m : Mem) : Decidable (LeakUnwindExact cb dt m) := by
  unfold LeakUnwindExact; split <;> infer_instance

/-- Exact behaviour of `guardRetain` under `unwind`: it returns exactly when the abstract
retain finishes, with the abstract result; otherwise it unwinds to a container holding
exactly the kept values followed by the unprocessed values, with exactly the removed values
added to the drop log, satisfying `Inv`. It never aborts and never reaches UB. -/
def GuardUnwindExact (cb : Callback) (dt : DtorTable) (m : Mem) : Prop :=
  match run .unwind cb dt guardRetain m with
  | .ret m' => RetainReturns (specRetain cb dt (toks m.elems)) m m'
  | .unwound m' =>
    (specRetain cb dt (toks m.elems)).ending ≠ .finished ∧
    toks m'.elems = (specRetain cb dt (toks m.elems)).kept ++ (specRetain cb dt (toks m.elems)).rest ∧
    m'.dropped = (specRetain cb dt (toks m.elems)).rejected ++ m.dropped ∧ Inv m'
  | _ => False

instance (cb : Callback) (dt : DtorTable) (m : Mem) : Decidable (GuardUnwindExact cb dt m) := by
  unfold GuardUnwindExact; split <;> infer_instance

/-! ## Proof infrastructure -/

/-! ### Raw and leak-amplified loops -/

/-- A list of initialized cells is the `some`-image of its tokens. -/
theorem raw_map_some_toks (cs : List Cell) (h : ∀ c ∈ cs, c ≠ none) :
    (toks cs).map some = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | none => exact absurd rfl (h none List.mem_cons_self)
    | some t =>
      rw [toks_cons_some, List.map_cons, ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]

/-- The tokens of a `some`-image list are the list itself. -/
theorem raw_toks_map_some (l : List Tok) : toks (l.map some) = l := by
  induction l with
  | nil => rfl
  | cons t l ih => rw [List.map_cons, toks_cons_some, ih]

/-- Unique ownership of a `some`-image list: no duplicates and disjoint from the drop log. -/
theorem raw_ownsUniquely_map_some (d l : List Tok) :
    OwnsUniquely d (l.map some) ↔ l.Nodup ∧ ∀ t ∈ l, t ∉ d := by
  simp only [OwnsUniquely, raw_toks_map_some]
  constructor
  · rintro ⟨-, h2, h3⟩; exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    refine ⟨fun c hc => ?_, h2, h3⟩
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hc
    simp

/-- Moving the next element to the kept list permutes the accumulated lists. -/
theorem raw_perm_keep (kept rej ys : List Tok) (y : Tok) :
    ((kept ++ [y]) ++ rej ++ ys).Perm (kept ++ rej ++ y :: ys) := by
  simp only [List.append_assoc, List.singleton_append]
  exact List.Perm.append_left kept List.perm_middle.symm

/-- Moving the next element to the rejected list permutes the accumulated lists. -/
theorem raw_perm_rej (kept rej ys : List Tok) (y : Tok) :
    (kept ++ (y :: rej) ++ ys).Perm (kept ++ rej ++ y :: ys) := by
  simp only [List.append_assoc, List.cons_append]
  exact List.Perm.append_left kept List.perm_middle.symm

/-- Reading the cell just after a prefix. -/
theorem raw_getElem?_len (A B : List Cell) (c : Cell) : (A ++ c :: B)[A.length]? = some c := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Writing the cell just after a prefix. -/
theorem raw_set_len (A B : List Cell) (c d : Cell) :
    (A ++ c :: B).set A.length d = A ++ d :: B := by
  rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
  rfl

/-- Length of a loop-state buffer `kept ++ mid ++ ys ++ tail`. -/
theorem raw_buf_length (kept mid ys : List Tok) (tail : List Cell) :
    (kept.map some ++ (mid ++ ys).map some ++ tail).length =
      kept.length + mid.length + ys.length + tail.length := by
  simp only [List.length_append, List.length_map]
  omega

/-- The next unprocessed cell of a loop-state buffer holds the next unprocessed value. -/
theorem raw_buf_getElem? (kept mid ys : List Tok) (y : Tok) (tail : List Cell) :
    (kept.map some ++ (mid ++ y :: ys).map some ++ tail)[kept.length + mid.length]? =
      some (some y) := by
  have h : kept.map some ++ (mid ++ y :: ys).map some ++ tail =
      (kept.map some ++ mid.map some) ++ some y :: (ys.map some ++ tail) := by
    simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append]
  have hl : kept.length + mid.length = (kept.map some ++ mid.map some).length := by
    simp only [List.length_append, List.length_map]
  rw [h, hl, raw_getElem?_len]

/-- `getD` form of `raw_buf_getElem?`. -/
theorem raw_buf_getD (kept mid ys : List Tok) (y : Tok) (tail : List Cell) :
    (kept.map some ++ (mid ++ y :: ys).map some ++ tail).getD (kept.length + mid.length) none =
      some y := by
  rw [List.getD_eq_getElem?_getD, raw_buf_getElem?]
  rfl

/-- The raw move of a kept value over the first stale cell. -/
theorem raw_buf_set (kept mid ys : List Tok) (m1 y : Tok) (tail : List Cell) :
    (kept.map some ++ ((m1 :: mid) ++ y :: ys).map some ++ tail).set kept.length (some y) =
      (kept ++ [y]).map some ++ ((mid ++ [y]) ++ ys).map some ++ tail := by
  have h : kept.map some ++ ((m1 :: mid) ++ y :: ys).map some ++ tail =
      kept.map some ++ some m1 :: (mid.map some ++ some y :: (ys.map some ++ tail)) := by
    simp only [List.map_append, List.map_cons, List.append_assoc, List.cons_append]
  have hl : kept.length = (kept.map some).length := by simp only [List.length_map]
  rw [h, hl, raw_set_len]
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append]

/-- The loop-state buffer re-read with the next value moved to the kept list (no stale cells). -/
theorem raw_buf_keep0 (kept ys : List Tok) (y : Tok) (tail : List Cell) :
    kept.map some ++ ([] ++ y :: ys).map some ++ tail =
      (kept ++ [y]).map some ++ ([] ++ ys).map some ++ tail := by
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc, List.cons_append,
    List.nil_append]

/-- The loop-state buffer re-read with the next value turned into a stale cell. -/
theorem raw_buf_rej (kept mid ys : List Tok) (y : Tok) (tail : List Cell) :
    kept.map some ++ (mid ++ y :: ys).map some ++ tail =
      kept.map some ++ ((mid ++ [y]) ++ ys).map some ++ tail := by
  simp only [List.append_assoc, List.singleton_append]

/-- Raw loop invariant: buffer `kept ++ mid ++ ys ++ tail` (`mid` stale), run follows `absRetain`. -/
theorem raw_loop (mode : Mode) (cb : Callback) (dt : DtorTable) (n L cA cB : Nat)
    (tail : List Cell) (d0 : List Tok) :
    ∀ (ys kept mid rej : List Tok) (r i del : Nat) (m : Mem) (o : AbsOut),
    r = ys.length → i = kept.length + mid.length → del = rej.length →
    mid.length = rej.length →
    (∀ t ∈ mid, t ∈ kept ∨ t ∈ rej) →
    (kept ++ rej ++ ys).Nodup →
    (∀ t ∈ kept ++ rej ++ ys, t ∉ d0) →
    n = kept.length + mid.length + ys.length →
    m = ⟨kept.map some ++ (mid ++ ys).map some ++ tail, L, rej ++ d0, cA, cB⟩ →
    absRetain cb dt ys i kept rej = o →
    ∃ mid' : List Tok, mid'.length = o.rejected.length ∧
      (∀ t ∈ mid', t ∈ o.kept ∨ t ∈ o.rejected) ∧
      (o.kept ++ o.rejected ++ o.rest).Nodup ∧
      (∀ t ∈ o.kept ++ o.rejected ++ o.rest, t ∉ d0) ∧
      n = o.kept.length + mid'.length + o.rest.length ∧
      (exec mode cb dt (rawLoop n r i del) i [] m).1 =
        (if o.ending = .finished then
          .ret ⟨o.kept.map some ++ (mid' ++ o.rest).map some ++ tail, o.kept.length,
            o.rejected ++ d0, cA, cB⟩
        else panicFrom mode dt []
          ⟨o.kept.map some ++ (mid' ++ o.rest).map some ++ tail, L, o.rejected ++ d0, cA, cB⟩) := by
  intro ys
  induction ys with
  | nil =>
    intro kept mid rej r i del m o hr hi hdel hml hmid hnd hd0 hn hm ho
    subst hr hm hdel
    simp only [absRetain] at ho
    subst ho
    refine ⟨mid, hml, hmid, hnd, hd0, hn, ?_⟩
    have hk : n - rej.length = kept.length := by
      simp only [List.length_nil] at hn; omega
    simp only [List.length_nil, rawLoop, exec, List.isEmpty_nil, ite_true, hk]
  | cons y ys ih =>
    intro kept mid rej r i del m o hr hi hdel hml hmid hnd hd0 hn hm ho
    subst hr hm hi hdel
    simp only [List.length_cons, rawLoop, exec]
    simp only [absRetain] at ho
    cases hcb : cb (kept.length + mid.length) with
    | panic =>
      simp only [hcb] at ho ⊢
      subst ho
      refine ⟨mid, hml, hmid, hnd, hd0, hn, ?_⟩
      show _ = if Ending.callbackPanic = Ending.finished then _ else _
      rw [ite_eq_right (by decide)]
    | ret b =>
      cases b with
      | true =>
        simp only [hcb, ite_true] at ho ⊢
        by_cases hdel0 : 0 < rej.length
        · rw [ite_eq_left hdel0]
          obtain ⟨m1, mid1, rfl⟩ : ∃ m1 mid1, mid = m1 :: mid1 := by
            cases mid with
            | nil => simp only [List.length_nil] at hml; omega
            | cons a b => exact ⟨a, b, rfl⟩
          have hlt : kept.length + (m1 :: mid1).length <
              (kept.map some ++ ((m1 :: mid1) ++ y :: ys).map some ++ tail).length := by
            rw [raw_buf_length]; simp only [List.length_cons]; omega
          have hk : kept.length + (m1 :: mid1).length - rej.length = kept.length := by
            simp only [List.length_cons] at hml ⊢; omega
          simp only [exec, hk]
          rw [ite_eq_left ⟨hlt, by omega⟩, raw_buf_getD, raw_buf_set]
          refine ih (kept ++ [y]) (mid1 ++ [y]) rej _ _ _ _ o rfl ?_ rfl ?_ ?_ ?_ ?_ ?_ rfl ho
          · simp only [List.length_append, List.length_cons, List.length_nil]; omega
          · simp only [List.length_append, List.length_cons, List.length_nil] at hml ⊢; omega
          · intro t ht
            rcases List.mem_append.mp ht with ht | ht
            · rcases hmid t (List.mem_cons_of_mem _ ht) with h | h
              · exact Or.inl (List.mem_append_left _ h)
              · exact Or.inr h
            · rw [List.mem_singleton] at ht
              exact Or.inl (List.mem_append_right _ (List.mem_singleton.mpr ht))
          · exact (raw_perm_keep kept rej ys y).nodup_iff.mpr hnd
          · exact fun t ht => hd0 t ((raw_perm_keep kept rej ys y).mem_iff.mp ht)
          · simp only [List.length_append, List.length_cons, List.length_nil] at hn ⊢; omega
        · rw [ite_eq_right hdel0]
          have hmid0 : mid = [] := List.eq_nil_of_length_eq_zero (by omega)
          subst hmid0
          rw [raw_buf_keep0]
          refine ih (kept ++ [y]) [] rej _ _ _ _ o rfl ?_ rfl hml ?_ ?_ ?_ ?_ rfl ho
          · simp only [List.length_append, List.length_cons, List.length_nil]
          · intro t ht; exact absurd ht List.not_mem_nil
          · exact (raw_perm_keep kept rej ys y).nodup_iff.mpr hnd
          · exact fun t ht => hd0 t ((raw_perm_keep kept rej ys y).mem_iff.mp ht)
          · simp only [List.length_append, List.length_cons, List.length_nil] at hn ⊢; omega
      | false =>
        simp only [hcb, Bool.false_eq_true, ite_false] at ho ⊢
        have hy : y ∉ rej ++ d0 := by
          rw [List.mem_append]
          rintro (h | h)
          · exact (List.nodup_append.mp hnd).2.2 y (List.mem_append_right _ h) y
              List.mem_cons_self rfl
          · exact hd0 y (List.mem_append_right _ List.mem_cons_self) h
        simp only [exec, raw_buf_getElem?, ite_eq_right hy]
        have hmid' : ∀ t ∈ mid ++ [y], t ∈ kept ∨ t ∈ y :: rej := by
          intro t ht
          rcases List.mem_append.mp ht with ht | ht
          · rcases hmid t ht with h | h
            · exact Or.inl h
            · exact Or.inr (List.mem_cons_of_mem _ h)
          · rw [List.mem_singleton] at ht
            exact Or.inr (ht ▸ List.mem_cons_self)
        have hnd' := (raw_perm_rej kept rej ys y).nodup_iff.mpr hnd
        have hd0' := fun t ht => hd0 t ((raw_perm_rej kept rej ys y).mem_iff.mp ht)
        have hn' : n = kept.length + (mid ++ [y]).length + ys.length := by
          simp only [List.length_append, List.length_cons, List.length_nil] at hn ⊢; omega
        cases hdt : dt y with
        | true =>
          simp only [hdt, ite_true] at ho ⊢
          subst ho
          have hl' : (mid ++ [y]).length = (y :: rej).length := by
            simp only [List.length_append, List.length_cons, List.length_nil]; omega
          refine ⟨mid ++ [y], hl', hmid', hnd', hd0', hn', ?_⟩
          show _ = if Ending.dtorPanic = Ending.finished then _ else _
          rw [ite_eq_right (by decide), raw_buf_rej]
          rfl
        | false =>
          simp only [hdt, Bool.false_eq_true, ite_false] at ho ⊢
          rw [raw_buf_rej]
          refine ih kept (mid ++ [y]) (y :: rej) _ _ _ _ o rfl ?_ ?_ ?_ hmid' hnd' hd0' hn' rfl ho
          · simp only [List.length_append, List.length_cons, List.length_nil]; omega
          · simp only [List.length_cons]
          · simp only [List.length_append, List.length_cons, List.length_nil]; omega

/-- Under `Inv`, the buffer is the owned values then the tail; they are distinct and undropped. -/
theorem raw_setup (m : Mem) (hm : Inv m) :
    m.buf = (toks m.elems).map some ++ m.buf.drop m.len ∧ (toks m.elems).length = m.len ∧
    (toks m.elems).Nodup ∧ ∀ t ∈ toks m.elems, t ∉ m.dropped := by
  obtain ⟨hlen, hinit, hnd, hd⟩ := hm
  have h1 := raw_map_some_toks m.elems hinit
  refine ⟨?_, ?_, hnd, hd⟩
  · rw [h1]
    exact (List.take_append_drop _ _).symm
  · have h2 := congrArg List.length h1
    rw [List.length_map] at h2
    rw [h2]
    simp only [Mem.elems, List.length_take]
    omega

/-- The raw loop from the start under `Inv`, with `len` set to `L` (`m.len` raw, `0` leak). -/
theorem raw_run (mode : Mode) (cb : Callback) (dt : DtorTable) (m : Mem) (hm : Inv m) (L : Nat)
    (o : AbsOut) (ho : specRetain cb dt (toks m.elems) = o) :
    ∃ mid' : List Tok, mid'.length = o.rejected.length ∧
      (∀ t ∈ mid', t ∈ o.kept ∨ t ∈ o.rejected) ∧
      (o.kept ++ o.rejected ++ o.rest).Nodup ∧
      (∀ t ∈ o.kept ++ o.rejected ++ o.rest, t ∉ m.dropped) ∧
      m.len = o.kept.length + mid'.length + o.rest.length ∧
      (exec mode cb dt (rawLoop m.len m.len 0 0) 0 [] { m with len := L }).1 =
        (if o.ending = .finished then
          .ret ⟨o.kept.map some ++ (mid' ++ o.rest).map some ++ m.buf.drop m.len, o.kept.length,
            o.rejected ++ m.dropped, m.ctrA, m.ctrB⟩
        else panicFrom mode dt []
          ⟨o.kept.map some ++ (mid' ++ o.rest).map some ++ m.buf.drop m.len, L,
            o.rejected ++ m.dropped, m.ctrA, m.ctrB⟩) := by
  obtain ⟨hbuf, hlen, hnd, hd⟩ := raw_setup m hm
  refine raw_loop mode cb dt m.len L m.ctrA m.ctrB (m.buf.drop m.len) m.dropped
    (toks m.elems) [] [] [] m.len 0 0 { m with len := L } o hlen.symm rfl rfl rfl ?_ ?_ ?_ ?_ ?_ ho
  · intro t ht; exact absurd ht List.not_mem_nil
  · simpa only [List.nil_append] using hnd
  · simpa only [List.nil_append] using hd
  · simp only [List.length_nil, Nat.zero_add, hlen]
  · simp only [List.map_nil, List.nil_append]
    rw [← hbuf]

/-- The normal-return state of the raw loop satisfies the normal-return clause. -/
theorem raw_returns (o : AbsOut) (m : Mem) (mid' : List Tok) (tail : List Cell) (cA cB : Nat)
    (hf : o.ending = .finished) (hnd : (o.kept ++ o.rejected ++ o.rest).Nodup)
    (hd0 : ∀ t ∈ o.kept ++ o.rejected ++ o.rest, t ∉ m.dropped) :
    RetainReturns o m ⟨o.kept.map some ++ (mid' ++ o.rest).map some ++ tail, o.kept.length,
      o.rejected ++ m.dropped, cA, cB⟩ := by
  have helems : (⟨o.kept.map some ++ (mid' ++ o.rest).map some ++ tail, o.kept.length,
      o.rejected ++ m.dropped, cA, cB⟩ : Mem).elems = o.kept.map some := by
    show List.take o.kept.length _ = _
    rw [List.append_assoc]
    exact List.take_left' (List.length_map _)
  have hkr := (List.nodup_append.mp (List.nodup_append.mp hnd).1)
  refine ⟨hf, ?_, rfl, ?_, ?_⟩
  · rw [helems, raw_toks_map_some]
  · show o.kept.length ≤ (o.kept.map some ++ (mid' ++ o.rest).map some ++ tail).length
    rw [raw_buf_length]; omega
  · rw [helems, raw_ownsUniquely_map_some]
    refine ⟨hkr.1, fun t ht h => ?_⟩
    rcases List.mem_append.mp h with h | h
    · exact hkr.2.2 t ht t h rfl
    · exact hd0 t (List.mem_append_left _ (List.mem_append_left _ ht)) h

/-- `Inv` of an unwound raw-loop state holds exactly when nothing was removed. -/
theorem raw_unwound_inv_iff (kept mid rej rest d0 : List Tok) (tail : List Cell) (len cA cB : Nat)
    (hml : mid.length = rej.length) (hmid : ∀ t ∈ mid, t ∈ kept ∨ t ∈ rej)
    (hnd : (kept ++ rej ++ rest).Nodup) (hd0 : ∀ t ∈ kept ++ rej ++ rest, t ∉ d0)
    (hn : len = kept.length + mid.length + rest.length) :
    Inv ⟨kept.map some ++ (mid ++ rest).map some ++ tail, len, rej ++ d0, cA, cB⟩ ↔ rej = [] := by
  have hb : kept.map some ++ (mid ++ rest).map some ++ tail =
      (kept ++ mid ++ rest).map some ++ tail := by
    simp only [List.map_append, List.append_assoc]
  have helems : (⟨kept.map some ++ (mid ++ rest).map some ++ tail, len, rej ++ d0, cA, cB⟩ :
      Mem).elems = (kept ++ mid ++ rest).map some := by
    show List.take len _ = _
    rw [hb]
    exact List.take_left' (by simp only [List.length_map, List.length_append, hn])
  unfold Inv
  rw [helems, raw_ownsUniquely_map_some]
  constructor
  · rintro ⟨-, hnd2, hd2⟩
    cases mid with
    | nil => exact List.eq_nil_of_length_eq_zero (by simp only [List.length_nil] at hml; omega)
    | cons t mid1 =>
      exfalso
      rcases hmid t List.mem_cons_self with h | h
      · have h2 := List.nodup_append.mp (List.nodup_append.mp hnd2).1
        exact h2.2.2 t h t List.mem_cons_self rfl
      · exact hd2 t (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))
          (List.mem_append_left _ h)
  · rintro rfl
    have hmid0 : mid = [] := List.eq_nil_of_length_eq_zero (by simpa using hml)
    subst hmid0
    refine ⟨?_, hnd, fun t ht => ?_⟩
    · show len ≤ (kept.map some ++ ([] ++ rest).map some ++ tail).length
      rw [raw_buf_length]; omega
    · rw [List.nil_append]; exact hd0 t ht

/-! ### Back-shift guard loop -/

/-- `toks` of a list of initialized cells is the underlying token list. -/
theorem grd_toks_map_some (L : List Tok) : toks (L.map some) = L := by
  induction L with
  | nil => rfl
  | cons x L ih => rw [List.map_cons, toks_cons_some, ih]

/-- Initialized cells holding distinct values outside the drop log are uniquely owned. -/
theorem grd_ownsUniquely_map_some (dr L : List Tok) (hnd : L.Nodup) (hdr : ∀ t ∈ L, t ∉ dr) :
    OwnsUniquely dr (L.map some) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hc
    simp
  · rw [grd_toks_map_some]; exact hnd
  · rw [grd_toks_map_some]; exact hdr

/-- If all cells are initialized, mapping `some` over their tokens gives them back. -/
theorem grd_map_toks (cs : List Cell) (h : ∀ c ∈ cs, c ≠ none) : (toks cs).map some = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases c with
    | none => exact absurd rfl (h none List.mem_cons_self)
    | some t =>
      rw [toks_cons_some, List.map_cons, ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]

/-- A pointwise description of a buffer prefix as initialized cells determines the prefix. -/
theorem grd_take_eq_map_some (b : List Cell) (L : List Tok)
    (h : ∀ i (hi : i < L.length), b[i]? = some (some L[i])) : b.take L.length = L.map some := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, List.getElem?_map]
  by_cases hi : i < L.length
  · simp only [hi, ↓reduceIte, h i hi, List.getElem?_eq_getElem hi, Option.map_some]
  · simp only [hi, ↓reduceIte, List.getElem?_eq_none (Nat.le_of_not_lt hi), Option.map_none]

/-- A state whose first `len` cells hold the distinct, undropped tokens `L` satisfies `Inv`,
and its element tokens are `L`. -/
theorem grd_post (m' : Mem) (L : List Tok) (hlen : m'.len = L.length)
    (hle : L.length ≤ m'.buf.length)
    (hcells : ∀ i (hi : i < L.length), m'.buf[i]? = some (some L[i]))
    (hnd : L.Nodup) (hdr : ∀ t ∈ L, t ∉ m'.dropped) : toks m'.elems = L ∧ Inv m' := by
  have he : m'.elems = L.map some := by
    rw [Mem.elems, hlen]; exact grd_take_eq_map_some _ _ hcells
  refine ⟨by rw [he, grd_toks_map_some], ?_⟩
  unfold Inv
  refine ⟨by omega, ?_⟩
  rw [he]; exact grd_ownsUniquely_map_some _ _ hnd hdr

/-- `copyRange` preserves the buffer length. -/
theorem grd_copyRange_length (c : Nat) (b : List Cell) (s d : Nat) :
    (copyRange c b s d).length = b.length := by
  induction c generalizing b s d with
  | zero => rfl
  | succ c ih => rw [copyRange, ih, List.length_set]

/-- `copyRange` leaves cells below the destination unchanged. -/
theorem grd_copyRange_getElem?_lt (c : Nat) (b : List Cell) (s d i : Nat) (hi : i < d) :
    (copyRange c b s d)[i]? = b[i]? := by
  induction c generalizing b s d with
  | zero => rfl
  | succ c ih =>
    rw [copyRange, ih _ _ _ (by omega), List.getElem?_set_ne (by omega)]

/-- Front-to-back `copyRange` with `dst ≤ src` moves cell `src + k` to cell `dst + k`. -/
theorem grd_copyRange_getElem?_shift (c : Nat) (b : List Cell) (s d k : Nat) (hds : d ≤ s)
    (hsc : s + c ≤ b.length) (hk : k < c) :
    (copyRange c b s d)[d + k]? = b[s + k]? := by
  induction c generalizing b s d k with
  | zero => omega
  | succ c ih =>
    rw [copyRange]
    cases k with
    | zero =>
      rw [grd_copyRange_getElem?_lt _ _ _ _ _ (by omega), Nat.add_zero, Nat.add_zero,
        List.getElem?_set_self (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by omega)]
      rfl
    | succ k =>
      have h1 : d + (k + 1) = (d + 1) + k := by omega
      have h2 : s + (k + 1) = (s + 1) + k := by omega
      rw [h1, ih _ _ _ _ (by omega) (by rw [List.length_set]; omega) (by omega), ← h2,
        List.getElem?_set_ne (by omega)]

/-- After the back-shift fix-up moves `ys` from `s` down to just after `kept`, the
container holds exactly `kept ++ ys`, and satisfies `Inv` when these are distinct and
undropped. -/
theorem grd_unwound_post (b : List Cell) (kept ys : List Tok) (s : Nat) (m' : Mem)
    (hbuf : m'.buf = copyRange ys.length b s kept.length)
    (hlen : m'.len = kept.length + ys.length)
    (hks : kept.length ≤ s) (hsb : s + ys.length ≤ b.length)
    (hk : ∀ i (hi : i < kept.length), b[i]? = some (some kept[i]))
    (hy : ∀ i (hi : i < ys.length), b[s + i]? = some (some ys[i]))
    (hnd : (kept ++ ys).Nodup) (hdr : ∀ t ∈ kept ++ ys, t ∉ m'.dropped) :
    toks m'.elems = kept ++ ys ∧ Inv m' := by
  apply grd_post m' (kept ++ ys) (by rw [hlen, List.length_append])
    (by rw [hbuf, grd_copyRange_length, List.length_append]; omega) _ hnd hdr
  intro i hi
  rw [List.length_append] at hi
  rw [hbuf]
  by_cases hik : i < kept.length
  · rw [grd_copyRange_getElem?_lt _ _ _ _ _ hik, hk i hik, List.getElem_append_left hik]
  · obtain ⟨k, rfl⟩ : ∃ k, i = kept.length + k := ⟨i - kept.length, by omega⟩
    rw [grd_copyRange_getElem?_shift _ _ _ _ _ hks hsb (by omega), hy k (by omega),
      List.getElem_append_right (by omega)]
    simp

/-- Loop invariant of `guardLoop` under `unwind`: at index `p` with `kept` kept and `rej`
removed (`d = rej.length`), the run agrees with the abstract retain on the remaining `ys`. -/
theorem grd_loop (cb : Callback) (dt : DtorTable) (n : Nat) (d0 : List Tok) :
    ∀ (ys kept rej : List Tok) (p d : Nat) (m : Mem),
      p = kept.length + rej.length → d = rej.length → p + ys.length = n →
      n ≤ m.buf.length →
      (∀ i (hi : i < kept.length), m.buf[i]? = some (some kept[i])) →
      (∀ i (hi : i < ys.length), m.buf[p + i]? = some (some ys[i])) →
      m.dropped = rej ++ d0 → (kept ++ ys).Nodup → (∀ t ∈ kept ++ ys, t ∉ m.dropped) →
      match (exec .unwind cb dt (guardLoop n ys.length p d) p [.guard (backshift p d n)] m).1 with
      | .ret m' =>
        (absRetain cb dt ys p kept rej).ending = .finished ∧
        toks m'.elems = (absRetain cb dt ys p kept rej).kept ∧
        m'.dropped = (absRetain cb dt ys p kept rej).rejected ++ d0 ∧ Inv m'
      | .unwound m' =>
        (absRetain cb dt ys p kept rej).ending ≠ .finished ∧
        toks m'.elems =
          (absRetain cb dt ys p kept rej).kept ++ (absRetain cb dt ys p kept rej).rest ∧
        m'.dropped = (absRetain cb dt ys p kept rej).rejected ++ d0 ∧ Inv m'
      | _ => False := by
  intro ys
  induction ys with
  | nil =>
    intro kept rej p d m hp hd hn hB hk hy hdr hnd hdis
    simp only [List.length_nil, guardLoop, exec, backshift, absRetain, List.isEmpty_nil,
      ↓reduceIte]
    simp only [List.length_nil, Nat.add_zero] at hn
    simp only [List.append_nil] at hnd hdis
    have hle : kept.length ≤ m.buf.length := by omega
    have hpost := grd_post ⟨m.buf, kept.length, m.dropped, m.ctrA, m.ctrB⟩ kept rfl hle hk hnd hdis
    rw [show n - p = 0 by omega, show n - d = kept.length by omega]
    exact ⟨trivial, hpost.1, hdr, hpost.2⟩
  | cons x ys ih =>
    intro kept rej p d m hp hd hn hB hk hy hdr hnd hdis
    have hx : m.buf[p]? = some (some x) := by
      have h := hy 0 (by simp)
      rwa [Nat.add_zero, List.getElem_cons_zero] at h
    have hy' : ∀ i (hi : i < ys.length), m.buf[p + 1 + i]? = some (some ys[i]) := by
      intro i hi
      have h := hy (i + 1) (by simp only [List.length_cons]; omega)
      rw [show p + (i + 1) = p + 1 + i by omega, List.getElem_cons_succ] at h
      exact h
    have hperm : (kept ++ x :: ys).Perm (x :: (kept ++ ys)) := List.perm_middle
    have hnd2 := hperm.nodup_iff.mp hnd
    rw [List.nodup_cons] at hnd2
    obtain ⟨hxn, hnd'⟩ := hnd2
    have hxd : x ∉ m.dropped := hdis x (hperm.mem_iff.mpr List.mem_cons_self)
    have hdis' : ∀ t ∈ kept ++ ys, t ∉ x :: m.dropped := by
      intro t ht
      rw [List.mem_cons, not_or]
      exact ⟨fun h => hxn (h ▸ ht), hdis t (hperm.mem_iff.mpr (List.mem_cons_of_mem _ ht))⟩
    have hnd3 : (kept ++ [x] ++ ys).Nodup := by
      rw [List.append_assoc, List.singleton_append]; exact hnd
    have hdis3 : ∀ t ∈ kept ++ [x] ++ ys, t ∉ m.dropped := by
      rw [List.append_assoc, List.singleton_append]; exact hdis
    simp only [List.length_cons] at hn
    rw [List.length_cons, guardLoop]
    cases hcb : cb p with
    | panic =>
      simp only [exec, hcb, panicFrom, unwindEntries, backshift, absRetain]
      rw [show n - p = (x :: ys).length by simp only [List.length_cons]; omega,
        show p - d = kept.length by omega,
        show n - d = kept.length + (x :: ys).length by simp only [List.length_cons]; omega]
      have H := grd_unwound_post m.buf kept (x :: ys) p
        { buf := copyRange (x :: ys).length m.buf p kept.length,
          len := kept.length + (x :: ys).length, dropped := m.dropped, ctrA := m.ctrA,
          ctrB := m.ctrB } rfl rfl (by omega) (by simp only [List.length_cons]; omega) hk hy
        hnd hdis
      exact ⟨by decide, H.1, hdr, H.2⟩
    | ret b =>
      cases b with
      | true =>
        by_cases hd0 : 0 < d
        · have hc1 : p < m.buf.length := by omega
          have hc2 : p - d < m.buf.length := by omega
          simp only [exec, hcb, absRetain, hd0, hc1, hc2, and_self, ↓reduceIte]
          have hpd : p - d = kept.length := by omega
          have hgd : m.buf.getD p none = some x := by
            rw [List.getD_eq_getElem?_getD, hx]; rfl
          rw [hpd, hgd]
          refine ih (kept ++ [x]) rej (p + 1) d _
            (by simp only [List.length_append, List.length_singleton]; omega) hd (by omega)
            (by simp only [List.length_set]; omega) ?_ ?_ hdr hnd3 hdis3
          · intro i hi
            simp only [List.length_append, List.length_singleton] at hi
            show (m.buf.set kept.length (some x))[i]? = _
            by_cases hik : i < kept.length
            · rw [List.getElem?_set_ne (by omega), hk i hik, List.getElem_append_left hik]
            · have hi' : i = kept.length := by omega
              subst hi'
              rw [List.getElem?_set_self (by omega)]
              simp
          · intro i hi
            show (m.buf.set kept.length (some x))[p + 1 + i]? = _
            rw [List.getElem?_set_ne (by omega)]
            exact hy' i hi
        · simp only [exec, hcb, absRetain, hd0, ↓reduceIte]
          refine ih (kept ++ [x]) rej (p + 1) d m
            (by simp only [List.length_append, List.length_singleton]; omega) hd (by omega)
            hB ?_ hy' hdr hnd3 hdis3
          intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          by_cases hik : i < kept.length
          · rw [hk i hik, List.getElem_append_left hik]
          · have hi' : i = kept.length := by omega
            subst hi'
            have hxk : m.buf[kept.length]? = some (some x) := by
              rw [show kept.length = p by omega]; exact hx
            rw [hxk]
            simp
      | false =>
        cases hdt : dt x with
        | true =>
          simp only [exec, hcb, absRetain, hdt, hx, hxd, panicFrom, unwindEntries, backshift,
            ↓reduceIte, Bool.false_eq_true]
          rw [show n - (p + 1) = ys.length by omega, show p + 1 - (d + 1) = kept.length by omega,
            show n - (d + 1) = kept.length + ys.length by omega]
          have H := grd_unwound_post m.buf kept ys (p + 1)
            { buf := copyRange ys.length m.buf (p + 1) kept.length,
              len := kept.length + ys.length, dropped := x :: m.dropped, ctrA := m.ctrA,
              ctrB := m.ctrB } rfl rfl (by omega) (by omega) hk hy' hnd' hdis'
          exact ⟨by decide, H.1, by rw [hdr]; rfl, H.2⟩
        | false =>
          simp only [exec, hcb, absRetain, hdt, hx, hxd, ↓reduceIte, Bool.false_eq_true]
          exact ih kept (x :: rej) (p + 1) (d + 1) _ (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega) (by omega) hB hk hy'
            (by show x :: m.dropped = _; rw [hdr]; rfl) hnd' hdis'

/-- `absRetain` loses no element: every element of the input, or already kept or removed,
ends in `kept`, `rejected` or `rest`. -/
theorem grd_absRetain_mem (cb : Callback) (dt : DtorTable) :
    ∀ (xs : List Tok) (j : Nat) (kept rej : List Tok) (t : Tok), t ∈ xs ∨ t ∈ kept ∨ t ∈ rej →
      t ∈ (absRetain cb dt xs j kept rej).kept ∨ t ∈ (absRetain cb dt xs j kept rej).rejected ∨
        t ∈ (absRetain cb dt xs j kept rej).rest := by
  intro xs
  induction xs with
  | nil =>
    intro j kept rej t h
    simp only [absRetain]
    rcases h with h | h | h
    · exact absurd h List.not_mem_nil
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  | cons x xs ih =>
    intro j kept rej t h
    cases hcb : cb j with
    | panic =>
      simp only [absRetain, hcb]
      rcases h with h | h | h
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    | ret b =>
      cases b with
      | true =>
        simp only [absRetain, hcb]
        apply ih
        rcases h with h | h | h
        · rcases List.mem_cons.mp h with rfl | h
          · exact Or.inr (Or.inl (List.mem_append_right _ List.mem_cons_self))
          · exact Or.inl h
        · exact Or.inr (Or.inl (List.mem_append_left _ h))
        · exact Or.inr (Or.inr h)
      | false =>
        cases hdt : dt x with
        | true =>
          simp only [absRetain, hcb, hdt, ↓reduceIte]
          rcases h with h | h | h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr (Or.inl List.mem_cons_self)
            · exact Or.inr (Or.inr h)
          · exact Or.inl h
          · exact Or.inr (Or.inl (List.mem_cons_of_mem _ h))
        | false =>
          simp only [absRetain, hcb, hdt, ↓reduceIte, Bool.false_eq_true]
          apply ih
          rcases h with h | h | h
          · rcases List.mem_cons.mp h with rfl | h
            · exact Or.inr (Or.inr List.mem_cons_self)
            · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (List.mem_cons_of_mem _ h))

/-! ## Raw moves -/

/-- Under `abort`, raw-move retain is exactly the abstract retain, for every callback and
destructor table and every entry state satisfying `Inv`. -/
theorem rawRetain_abort_exact (cb : Callback) (dt : DtorTable) (m : Mem) (hm : Inv m) :
    RawAbortExact cb dt m := by
  obtain ⟨mid', -, -, hnd, hd0, -, hex⟩ := raw_run .abort cb dt m hm m.len _ rfl
  have hrun : run .abort cb dt rawRetain m =
      (exec .abort cb dt (rawLoop m.len m.len 0 0) 0 [] { m with len := m.len }).1 := rfl
  unfold RawAbortExact
  rw [hrun, hex]
  by_cases hf : (specRetain cb dt (toks m.elems)).ending = .finished
  · rw [ite_eq_left hf]
    exact raw_returns _ m mid' _ _ _ hf hnd hd0
  · rw [ite_eq_right hf]
    exact hf

/-- Raw-move retain is panic-safe under `abort`. -/
theorem rawRetain_panicSafe_abort : PanicSafe .abort rawRetain := by
  intro cb dt m hm
  have h := rawRetain_abort_exact cb dt m hm
  unfold RawAbortExact at h
  revert h
  cases run .abort cb dt rawRetain m <;> simp [ResOk, RetainReturns]
  all_goals intros; assumption

/-- Under `unwind`, for every entry state satisfying `Inv`: whenever raw-move retain unwinds,
the unwound container satisfies `Inv` if and only if the abstract retain removed no element
up to and including the panic (its `rejected` list is empty; a removed element whose
destructor panics counts as removed). -/
theorem rawRetain_unwound_inv_iff_rejected_nil (cb : Callback) (dt : DtorTable) (m m' : Mem)
    (hm : Inv m) (h : run .unwind cb dt rawRetain m = .unwound m') :
    Inv m' ↔ (specRetain cb dt (toks m.elems)).rejected = [] := by
  obtain ⟨mid', hml, hmid, hnd, hd0, hn, hex⟩ := raw_run .unwind cb dt m hm m.len _ rfl
  have hrun : run .unwind cb dt rawRetain m =
      (exec .unwind cb dt (rawLoop m.len m.len 0 0) 0 [] { m with len := m.len }).1 := rfl
  rw [hrun, hex] at h
  by_cases hf : (specRetain cb dt (toks m.elems)).ending = .finished
  · rw [ite_eq_left hf] at h
    exact absurd h (fun h' => Res.noConfusion h')
  · rw [ite_eq_right hf] at h
    have hm' := (Res.unwound.inj h : _ = m')
    subst hm'
    exact raw_unwound_inv_iff _ _ _ _ _ _ _ _ _ hml hmid hnd hd0 hn

/-- Entry state of the double-drop counterexample. -/
def ceMem2 : Mem := ⟨[some 0, some 1], 2, [], 0, 0⟩

/-- Decidable form of `rawRetain_unwound_inv_iff_rejected_nil` for one run (used by its
bounded check). -/
def RawUnwoundIff (cb : Callback) (dt : DtorTable) (m : Mem) : Prop :=
  match run .unwind cb dt rawRetain m with
  | .unwound m' => (Inv m' ↔ (specRetain cb dt (toks m.elems)).rejected = [])
  | _ => True

instance (cb : Callback) (dt : DtorTable) (m : Mem) : Decidable (RawUnwoundIff cb dt m) := by
  unfold RawUnwoundIff; split <;> infer_instance

/-- Bounded check of `rawRetain_unwound_inv_iff_rejected_nil` (same family as
`rawRetain_abort_exact_upTo3`). -/
theorem rawRetain_unwound_inv_iff_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      RawUnwoundIff (tableOf bs) (dtOf ds) m := by
  decide

/-- Remove element `0`, then panic on element `1`. -/
def ceCbRemoveThenPanic : Callback := tableOf [.ret false, .panic]

/-- Counterexample: under `unwind`, raw-move retain on `[0, 1]` with a callback that removes
element `0` and then panics unwinds to a container whose `len` still covers the dropped
value `0`; the owner's drop of the container then reaches UB (value `0` is dropped twice).
Under `abort` the same run aborts. -/
theorem rawRetain_unwind_doubleDrop :
    Inv ceMem2 ∧
    run .unwind ceCbRemoveThenPanic noPanicDtors rawRetain ceMem2 =
      .unwound ⟨[some 0, some 1], 2, [0], 0, 0⟩ ∧
    ¬ Inv ⟨[some 0, some 1], 2, [0], 0, 0⟩ ∧
    harness .unwind ceCbRemoveThenPanic noPanicDtors rawRetain ceMem2 = .ub ∧
    run .abort ceCbRemoveThenPanic noPanicDtors rawRetain ceMem2 = .abort := by
  decide

/-- Entry state with three elements. -/
def ceMem3 : Mem := ⟨[some 0, some 1, some 2], 3, [], 0, 0⟩

/-- The other direction of `rawRetain_unwound_inv_iff_rejected_nil` is exercised: keeping
element `0` and panicking on element `1` removes nothing, and the unwound state satisfies
`Inv`. -/
theorem rawRetain_unwind_noRemoval_example :
    run .unwind (tableOf [.ret true, .panic]) noPanicDtors rawRetain ceMem2 = .unwound ceMem2 ∧
    Inv ceMem2 ∧
    (specRetain (tableOf [.ret true, .panic]) noPanicDtors (toks ceMem2.elems)).rejected = [] := by
  decide

/-- Remove element `0`, keep element `1`, panic on element `2`. -/
def ceCbRemoveKeepPanic : Callback := tableOf [.ret false, .ret true, .panic]

/-- Counterexample with a moved-out slot: after removing `0` and moving `1` down, a panic
leaves two cells holding value `1` within `len`; the owner's drop reaches UB. -/
theorem rawRetain_unwind_duplicate :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors rawRetain ceMem3 =
      .unwound ⟨[some 1, some 1, some 2], 3, [0], 0, 0⟩ ∧
    harness .unwind ceCbRemoveKeepPanic noPanicDtors rawRetain ceMem3 = .ub := by
  decide

/-- Bounded check of `rawRetain_abort_exact`: sizes `0..3`, the entry states `testMems n`,
all callback tables determined by the first `n` invocations, all destructor tables
determined by tokens `0..n-1`. -/
theorem rawRetain_abort_exact_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      RawAbortExact (tableOf bs) (dtOf ds) m := by
  decide

/-! ## Leak amplification -/

/-- Under `unwind`, leak-amplified retain behaves exactly as `LeakUnwindExact` says, for
every callback and destructor table and every entry state satisfying `Inv`. -/
theorem leakRetain_unwind_exact (cb : Callback) (dt : DtorTable) (m : Mem) (hm : Inv m) :
    LeakUnwindExact cb dt m := by
  obtain ⟨mid', -, -, hnd, hd0, hn, hex⟩ := raw_run .unwind cb dt m hm 0 _ rfl
  have hrun : run .unwind cb dt leakRetain m =
      (exec .unwind cb dt (rawLoop m.len m.len 0 0) 0 [] { m with len := 0 }).1 := rfl
  have hlen := hm.1
  unfold LeakUnwindExact
  rw [hrun, hex]
  by_cases hf : (specRetain cb dt (toks m.elems)).ending = .finished
  · rw [ite_eq_left hf]
    exact raw_returns _ m mid' _ _ _ hf hnd hd0
  · rw [ite_eq_right hf]
    refine ⟨hf, rfl, rfl, ?_, rfl, rfl⟩
    show (_ ++ _ ++ m.buf.drop m.len).length = m.buf.length
    rw [raw_buf_length, List.length_drop]
    omega

/-- Leak-amplified retain is panic-safe under `unwind`. -/
theorem leakRetain_panicSafe_unwind : PanicSafe .unwind leakRetain := by
  intro cb dt m hm
  have h := leakRetain_unwind_exact cb dt m hm
  unfold LeakUnwindExact at h
  revert h
  cases run .unwind cb dt leakRetain m with
  | ret m' => simp only [ResOk, RetainReturns]; exact fun h => h.2.2.2
  | unwound m' =>
    simp only [ResOk]
    rintro ⟨_, h0, -⟩
    simp [Inv, Mem.elems, h0, OwnsUniquely, toks]
  | abort => simp
  | ub => simp

/-- For every entry state satisfying `Inv`: after an unwind, leak-amplified retain leaves a
container whose first `len` cells hold no value, and a value of the entry container is in
the drop log if and only if the abstract retain removed it. Hence every value of the entry
container that was not removed is leaked (neither in the drop log nor held by the
container). -/
theorem leakRetain_unwound_leaks (cb : Callback) (dt : DtorTable) (m m' : Mem) (hm : Inv m)
    (h : run .unwind cb dt leakRetain m = .unwound m') :
    toks m'.elems = [] ∧
    ∀ t ∈ toks m.elems, (t ∈ m'.dropped ↔ t ∈ (specRetain cb dt (toks m.elems)).rejected) := by
  have hx := leakRetain_unwind_exact cb dt m hm
  unfold LeakUnwindExact at hx
  rw [h] at hx
  obtain ⟨_, h0, hd, -⟩ := hx
  refine ⟨by simp [Mem.elems, h0, toks], fun t ht => ?_⟩
  have hnd : t ∉ m.dropped := hm.2.2.2 t ht
  rw [hd, List.mem_append]
  constructor
  · rintro (h | h)
    · exact h
    · exact absurd h hnd
  · exact Or.inl

/-- Non-vacuity and leak witness: on `[0, 1, 2]`, removing `0`, keeping `1` and panicking on
`2` unwinds with `len = 0`; values `1` and `2` are leaked. -/
theorem leakRetain_unwind_example :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors leakRetain ceMem3 =
      .unwound ⟨[some 1, some 1, some 2], 0, [0], 0, 0⟩ ∧
    ¬ LeakFree ceMem3 ⟨[some 1, some 1, some 2], 0, [0], 0, 0⟩ := by
  decide

/-- Bounded check of `leakRetain_unwind_exact` (same family as `rawRetain_abort_exact_upTo3`). -/
theorem leakRetain_unwind_exact_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      LeakUnwindExact (tableOf bs) (dtOf ds) m := by
  decide

/-! ## Drop guards -/

/-- Under `unwind`, back-shift-guard retain (guard fields updated before each destructor)
behaves exactly as `GuardUnwindExact` says, for every callback table, every destructor
table (panicking destructors included), and every entry state satisfying `Inv`. -/
theorem guardRetain_unwind_exact (cb : Callback) (dt : DtorTable) (m : Mem) (hm : Inv m) :
    GuardUnwindExact cb dt m := by
  obtain ⟨hlen, hinit, hnd, hdis⟩ := hm
  have hmap := grd_map_toks m.elems hinit
  have hxs_len : (toks m.elems).length = m.len := by
    have h : ((toks m.elems).map some).length = (m.buf.take m.len).length :=
      congrArg List.length hmap
    rw [List.length_map, List.length_take] at h
    omega
  have hcells : ∀ i (hi : i < (toks m.elems).length),
      m.buf[0 + i]? = some (some (toks m.elems)[i]) := by
    intro i hi
    have h1 : ((toks m.elems).map some)[i]? = some (some (toks m.elems)[i]) := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi]; rfl
    have hi' : i < m.len := by omega
    have h2 : m.elems[i]? = m.buf[i]? := by
      show (m.buf.take m.len)[i]? = _
      rw [List.getElem?_take]
      simp only [hi', ↓reduceIte]
    rw [hmap, h2] at h1
    rw [Nat.zero_add]; exact h1
  have H := grd_loop cb dt m.len m.dropped (toks m.elems) [] [] 0 0 m rfl rfl
    (by rw [Nat.zero_add]; exact hxs_len) hlen (fun i hi => absurd hi (Nat.not_lt_zero _))
    hcells rfl hnd hdis
  rw [hxs_len] at H
  unfold GuardUnwindExact run guardRetain
  simp only [exec]
  generalize (exec .unwind cb dt (guardLoop m.len m.len 0 0) 0
    [.guard (backshift 0 0 m.len)] m).1 = R at H ⊢
  cases R with
  | ret m' => exact H
  | unwound m' => exact H
  | abort => exact H
  | ub => exact H

/-- Back-shift-guard retain is panic-safe under `unwind`. -/
theorem guardRetain_panicSafe_unwind : PanicSafe .unwind guardRetain := by
  intro cb dt m hm
  have h := guardRetain_unwind_exact cb dt m hm
  unfold GuardUnwindExact at h
  revert h
  cases run .unwind cb dt guardRetain m <;> simp [ResOk, RetainReturns]
  all_goals intros; assumption

/-- Bounded check of `guardRetain_unwind_exact` (same family as `rawRetain_abort_exact_upTo3`). -/
theorem guardRetain_unwind_exact_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      GuardUnwindExact (tableOf bs) (dtOf ds) m := by
  decide

/-- Back-shift-guard retain is leak-free on unwind: for every entry state satisfying `Inv`,
whenever the run unwinds, every value of the entry container is in the drop log or held by
the first `len` cells of the unwound container. -/
theorem guardRetain_unwound_leakFree (cb : Callback) (dt : DtorTable) (m m' : Mem)
    (hm : Inv m) (h : run .unwind cb dt guardRetain m = .unwound m') : LeakFree m m' := by
  have H := guardRetain_unwind_exact cb dt m hm
  unfold GuardUnwindExact at H
  rw [h] at H
  obtain ⟨-, hk, hd, -⟩ := H
  intro t ht
  rcases grd_absRetain_mem cb dt (toks m.elems) 0 [] [] t (Or.inl ht) with h1 | h1 | h1
  · right; rw [hk]; exact List.mem_append_left _ h1
  · left; rw [hd]; exact List.mem_append_left _ h1
  · right; rw [hk]; exact List.mem_append_right _ h1

/-- Decidable form of `guardRetain_unwound_leakFree` for one run (used by its bounded check). -/
def GuardUnwoundLeakFree (cb : Callback) (dt : DtorTable) (m : Mem) : Prop :=
  match run .unwind cb dt guardRetain m with
  | .unwound m' => LeakFree m m'
  | _ => True

instance (cb : Callback) (dt : DtorTable) (m : Mem) :
    Decidable (GuardUnwoundLeakFree cb dt m) := by
  unfold GuardUnwoundLeakFree; split <;> infer_instance

/-- Bounded check of `guardRetain_unwound_leakFree` (same family as
`rawRetain_abort_exact_upTo3`). -/
theorem guardRetain_unwound_leakFree_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n, ∀ ds ∈ allBools n,
      GuardUnwoundLeakFree (tableOf bs) (dtOf ds) m := by
  decide

/-- All buffers of at most two cells over `none`, `some 0`, `some 1`. -/
def smallBufs : List (List Cell) :=
  let cs : List Cell := [none, some 0, some 1]
  [[]] ++ cs.map (fun a => [a]) ++ cs.flatMap (fun a => cs.map fun b => [a, b])

/-- Entry states for checks without an entry invariant: every buffer of `smallBufs`, every
`len ≤ 3`, drop log `[]` or `[0]`. Most of these states violate `Inv`. -/
def smallMems : List Mem :=
  smallBufs.flatMap fun b => [0, 1, 2, 3].flatMap fun l => [[], [0]].map fun d => ⟨b, l, d, 0, 0⟩

set_option maxRecDepth 100000 in
/-- Bounded check of the statement of `guardRetain_unwound_leakFree` without its hypothesis
`Inv m`, on entry states that need not satisfy `Inv`: every state of `smallMems`, callback
tables determined by the first `3` invocations, destructor tables determined by tokens
`0, 1`. -/
theorem guardRetain_unwound_leakFree_noInv_bounded :
    ∀ m ∈ smallMems, ∀ bs ∈ allBehs 3, ∀ ds ∈ allBools 2,
      GuardUnwoundLeakFree (tableOf bs) (dtOf ds) m := by
  decide

/-- Non-vacuity witness for the guard results: the run of `rawRetain_unwind_duplicate`,
under the guard, unwinds to `[1, 2]` with `0` dropped. -/
theorem guardRetain_unwind_example :
    Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors guardRetain ceMem3 =
      .unwound ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    Inv ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    LeakFree ceMem3 ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ := by
  decide

/-- Entry state with one element. -/
def ceMem1 : Mem := ⟨[some 0], 1, [], 0, 0⟩

/-- Remove element `0`. -/
def ceCbRemove : Callback := tableOf [.ret false]

/-- The destructor of value `0` panics. -/
def dtPanicsOn0 : DtorTable := dtOf [true]

/-- With a destructor that panics, the guard updated before the destructor still unwinds to
a state satisfying `Inv` (`len = 0`, value `0` dropped once). -/
theorem guardRetain_dtorPanic_example :
    Inv ceMem1 ∧
    run .unwind ceCbRemove dtPanicsOn0 guardRetain ceMem1 = .unwound ⟨[some 0], 0, [0], 0, 0⟩ ∧
    Inv ⟨[some 0], 0, [0], 0, 0⟩ := by
  decide

/-- With non-panicking destructors, the late-update guard loop and the early-update guard loop have the same outcome. -/
theorem guardLoopLate_eq_guardLoop_of_noPanickingDtors (cb : Callback) (dt : DtorTable)
    (hdt : NoPanickingDtors dt) (n : Nat) :
    ∀ (r p d j : Nat) (es : List Entry) (m : Mem),
      (exec .unwind cb dt (guardLoopLate n r p d) j es m).1 =
      (exec .unwind cb dt (guardLoop n r p d) j es m).1
  | 0, _, _, _, _, _ => rfl
  | r + 1, p, d, j, es, m => by
      simp only [guardLoopLate, guardLoop, exec]
      cases hcb : cb j with
      | panic => rfl
      | ret b =>
        cases b with
        | true =>
          simp only [ite_true]
          split
          · simp only [exec]
            split
            · cases es with
              | nil => rfl
              | cons e es' =>
                cases e with
                | value _ => rfl
                | guard _ => exact guardLoopLate_eq_guardLoop_of_noPanickingDtors cb dt hdt n r (p + 1) d (j + 1) _ _
            · rfl
          · cases es with
            | nil => rfl
            | cons e es' =>
              cases e with
              | value _ => rfl
              | guard _ => exact guardLoopLate_eq_guardLoop_of_noPanickingDtors cb dt hdt n r (p + 1) d (j + 1) _ _
        | false =>
          simp only [Bool.false_eq_true, ite_false]
          cases es with
          | nil =>
            simp only [exec]
            cases hb : m.buf[p]? with
            | none => rfl
            | some c =>
              cases c with
              | none => rfl
              | some t =>
                by_cases ht : t ∈ m.dropped
                · simp [ht]
                · simp [ht, hdt t]
          | cons e es' =>
            cases e with
            | value _ =>
              simp only [exec]
              cases hb : m.buf[p]? with
              | none => rfl
              | some c =>
                cases c with
                | none => rfl
                | some t =>
                  by_cases ht : t ∈ m.dropped
                  · simp [ht]
                  · simp [ht, hdt t]
            | guard g =>
              simp only [exec]
              cases hb : m.buf[p]? with
              | none => rfl
              | some c =>
                cases c with
                | none => rfl
                | some t =>
                  by_cases ht : t ∈ m.dropped
                  · simp [ht]
                  · simp only [ht, ite_false, hdt t, Bool.false_eq_true]
                    exact guardLoopLate_eq_guardLoop_of_noPanickingDtors cb dt hdt n r (p + 1) (d + 1) (j + 1) _ _

/-- Back-shift-guard retain with the guard fields updated after each destructor is
panic-safe under `unwind` for every callback table, every destructor table in which no
destructor panics, and every entry state satisfying `Inv`. -/
theorem guardRetainLate_panicSafe_unwind_of_noPanickingDtors :
    PanicSafeAssumingNoDtorPanic .unwind guardRetainLate := by
  intro cb dt m hdt hm
  have heq : run .unwind cb dt guardRetainLate m = run .unwind cb dt guardRetain m := by
    unfold run guardRetainLate guardRetain
    simp only [exec]
    exact guardLoopLate_eq_guardLoop_of_noPanickingDtors cb dt hdt m.len m.len 0 0 0 _ m
  rw [heq]
  exact guardRetain_panicSafe_unwind cb dt m hm

/-- Counterexample (tightness of `NoPanickingDtors` for `guardRetainLate`, on a one-element
container): removing value `0` whose destructor panics leaves the guard's fields stale
(`processed = 0`, `deleted = 0`), so the guard leaves the dropped cell inside `len = 1`
instead of excluding it; the unwound state violates `Inv`, and the owner's drop reaches UB
(value `0` dropped twice). -/
theorem guardRetainLate_dtorPanic_counterexample :
    Inv ceMem1 ∧ ¬ NoPanickingDtors dtPanicsOn0 ∧
    run .unwind ceCbRemove dtPanicsOn0 guardRetainLate ceMem1 =
      .unwound ⟨[some 0], 1, [0], 0, 0⟩ ∧
    ¬ Inv ⟨[some 0], 1, [0], 0, 0⟩ ∧
    harness .unwind ceCbRemove dtPanicsOn0 guardRetainLate ceMem1 = .ub := by
  refine ⟨by decide, fun h => absurd (h 0) (by decide), by decide, by decide, by decide⟩

/-- Bounded check of `guardRetainLate_panicSafe_unwind_of_noPanickingDtors`: sizes `0..3`, entry
states `testMems n`, callback tables determined by the first `n` invocations, and the
non-panicking destructor table. -/
theorem guardRetainLate_panicSafe_upTo3 :
    ∀ n ∈ [0, 1, 2, 3], ∀ m ∈ testMems n, ∀ bs ∈ allBehs n,
      ResOk (run .unwind (tableOf bs) noPanicDtors guardRetainLate m) := by
  decide

/-- Non-vacuity witness for `guardRetainLate_panicSafe_unwind_of_noPanickingDtors`: the
non-panicking table satisfies the hypothesis, and a callback panic after a removal unwinds
to a state satisfying `Inv`. -/
theorem guardRetainLate_noPanic_example :
    NoPanickingDtors noPanicDtors ∧ Inv ceMem3 ∧
    run .unwind ceCbRemoveKeepPanic noPanicDtors guardRetainLate ceMem3 =
      .unwound ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ ∧
    Inv ⟨[some 1, some 2, some 2], 2, [0], 0, 0⟩ := by
  refine ⟨fun _ => rfl, by decide, by decide, by decide⟩

/-! ## Tightness of the entry invariant -/

/-- An entry state violating `Inv` (value `0` held twice). -/
def dupMem : Mem := ⟨[some 0, some 0], 2, [], 0, 0⟩

/-- Counterexample (the entry `Inv` cannot be dropped from `rawRetain_abort_exact`). -/
theorem rawRetain_abort_exact_needs_inv :
    ¬ Inv dupMem ∧ ¬ RawAbortExact (tableOf []) noPanicDtors dupMem := by decide

/-- Counterexample (the entry `Inv` cannot be dropped from `leakRetain_unwind_exact`). -/
theorem leakRetain_unwind_exact_needs_inv :
    ¬ Inv dupMem ∧ ¬ LeakUnwindExact (tableOf []) noPanicDtors dupMem := by decide

/-- Counterexample (the entry `Inv` cannot be dropped from `guardRetain_unwind_exact`). -/
theorem guardRetain_unwind_exact_needs_inv :
    ¬ Inv dupMem ∧ ¬ GuardUnwindExact (tableOf []) noPanicDtors dupMem := by decide

/-- Counterexample (the entry `Inv` cannot be dropped from
`rawRetain_unwound_inv_iff_rejected_nil`): from `dupMem`, a panic before any removal unwinds
to `dupMem` itself, and the biconditional fails (nothing was removed, yet the unwound state
violates `Inv`). -/
theorem rawRetain_unwound_iff_needs_inv :
    ¬ Inv dupMem ∧
    run .unwind (tableOf [.panic]) noPanicDtors rawRetain dupMem = .unwound dupMem ∧
    ¬ (Inv dupMem ↔
      (specRetain (tableOf [.panic]) noPanicDtors (toks dupMem.elems)).rejected = []) := by
  decide

/-- Counterexample (the entry `Inv` cannot be dropped from `leakRetain_unwound_leaks`): on a
one-element container whose value is already in the drop log, a panic before any removal
unwinds, and the value is in the drop log although it was not removed. -/
theorem leakRetain_unwound_leaks_needs_inv :
    ¬ Inv ⟨[some 0], 1, [0], 0, 0⟩ ∧
    run .unwind (tableOf [.panic]) noPanicDtors leakRetain ⟨[some 0], 1, [0], 0, 0⟩ =
      .unwound ⟨[some 0], 0, [0], 0, 0⟩ ∧
    ¬ (toks (Mem.elems ⟨[some 0], 0, [0], 0, 0⟩) = [] ∧
      ∀ t ∈ toks (Mem.elems ⟨[some 0], 1, [0], 0, 0⟩),
        (t ∈ (⟨[some 0], 0, [0], 0, 0⟩ : Mem).dropped ↔
          t ∈ (specRetain (tableOf [.panic]) noPanicDtors
            (toks (Mem.elems ⟨[some 0], 1, [0], 0, 0⟩))).rejected)) := by
  decide

/-- Counterexample (the entry `Inv` cannot be dropped from
`guardRetainLate_panicSafe_unwind_of_noPanickingDtors`): with non-panicking destructors and a
callback that keeps everything, the run from `dupMem` returns a state violating `Inv`. -/
theorem guardRetainLate_needs_inv :
    ¬ Inv dupMem ∧ NoPanickingDtors noPanicDtors ∧
    ¬ ResOk (run .unwind (tableOf []) noPanicDtors guardRetainLate dupMem) :=
  ⟨by decide, fun _ => rfl, by decide⟩

end Toy.PanicSafety
