import Toy.Sep.Commands

/-!
# Non-local commands and tightness of the locality hypotheses (all proved)

* `allocAt` (allocate at a fixed address, faulting if it is taken) has the frame
  property but violates safety monotonicity; the triple `{emp} allocAt 0 1 {0 ↦ 1}`
  holds but its framed version with frame `0 ↦ 2` fails (it faults). The variant
  `allocAtBlock` that blocks instead of faulting is local.
* `isAllocTest 1 0` (record in cell `0` whether cell `1` is allocated) is
  safety-monotone but violates the frame property; `{0 ↦ 0} isAllocTest 1 0 {0 ↦ 0}`
  holds but its framed version with frame `1 ↦ 7` fails (cell `0` becomes `1`).
* `allocLeast` (deterministic least-free-address allocation) is safety-monotone
  but violates the frame property; `{emp} allocLeast 1 {0 ↦ 1}` holds but its
  framed version with frame `0 ↦ 2` fails (the new cell lands at address `1`).
* Predictable allocation is not local: a command that, from some base heap, is
  safe, always allocates a fixed free address, and still runs when a frame
  occupies that address, violates the frame property. Corollaries: every total
  deterministic single-cell writer `detAlloc f v`, and deterministic
  pointer-recording allocation `detAllocInto f r v` with a fresh address choice.
  Each hypothesis is shown necessary.
* A heap command that is safe on `emp` but can fault somewhere is not
  safety-monotone (e.g. an allocator that faults when memory is exhausted).
* The fault-avoiding reading of triples is necessary: with `WeakTriple` the frame
  rule fails even for the local command `assertAlloc 0`.
* Frames must range over a rich enough class: if only the frame `emp` is
  allowed, every command satisfies the (restricted) frame rule.
-/

namespace Toy.Sep

open SepStruct

variable {V : Type}

/-! ## `skip` and `assertAlloc` are local (helper facts) -/

theorem skip_safetyMono {S : Type _} [SepStruct S] : SafetyMono (skip : Cmd S) :=
  fun _ _ _ _ => safe_skip _

theorem skip_frameProp {S : Type _} [SepStruct S] : FrameProp (skip : Cmd S) := by
  intro h h' h'' hd _ hr
  refine ⟨h, rfl, hd, ?_⟩
  injection hr

theorem assertAlloc_safetyMono (k : Nat) : SafetyMono (assertAlloc (V := V) k) := by
  intro h h' _ hs
  rw [safe_assertAlloc_iff] at hs ⊢
  simp only [Heap.union_eq, Heap.join_val]
  cases e : h.val k with
  | none => exact absurd e hs
  | some w => simp

theorem assertAlloc_frameProp (k : Nat) : FrameProp (assertAlloc (V := V) k) := by
  intro h h' h'' hd hs hr
  rcases hr with ⟨_, hf⟩ | ⟨_, he⟩
  · cases hf
  · injection he with he
    exact ⟨h, Or.inr ⟨(safe_assertAlloc_iff k h).1 hs, rfl⟩, hd, he⟩

/-! ## `allocAt`: frame property holds, safety monotonicity fails -/

theorem allocAt_frameProp (k : Nat) (v : V) : FrameProp (allocAt k v) := by
  intro h h' h'' hd hs hrun
  rw [safe_allocAt_iff] at hs
  rcases hrun with ⟨_, hf⟩ | ⟨hk, he⟩
  · cases hf
  · simp only [Heap.union_eq, Heap.join_val, hs, Option.none_or] at hk
    injection he with he
    refine ⟨h.set k (some v), Or.inr ⟨hs, rfl⟩, ?_, ?_⟩
    · intro j
      by_cases hj : j = k
      · subst hj; exact Or.inr hk
      · simp only [Heap.set_val, hj, ite_false]; exact hd j
    · rw [he]
      exact (Heap.set_join hk _).symm

theorem allocAt_not_safetyMono (k : Nat) (v : V) : ¬ SafetyMono (allocAt k v) := by
  intro hsm
  have h1 : Safe (allocAt k v) (Heap.emp : Heap V) := (safe_allocAt_iff k v _).2 rfl
  have hd : disj (Heap.emp : Heap V) (Heap.pt k v) := fun _ => Or.inl rfl
  have h2 := hsm _ _ hd h1
  rw [safe_allocAt_iff] at h2
  simp at h2

/-- **Tightness of safety monotonicity** (canonical form): `allocAt 0 1` has the
frame property and satisfies `{emp} allocAt 0 1 {0 ↦ 1}`, but the framed triple
`{emp * (0 ↦ 2)} allocAt 0 1 {(0 ↦ 1) * (0 ↦ 2)}` fails. -/
theorem allocAt_frameProp_and_framed_triple_fails :
    FrameProp (allocAt 0 (1 : Nat)) ∧
    Triple (sing Heap.emp) (allocAt 0 (1 : Nat)) (sing (Heap.pt 0 1)) ∧
    ¬ Triple (sep (sing Heap.emp) (sing (Heap.pt 0 2))) (allocAt 0 (1 : Nat))
        (sep (sing (Heap.pt 0 1)) (sing (Heap.pt 0 2))) := by
  refine ⟨allocAt_frameProp 0 1, ?_, ?_⟩
  · intro h hh
    have hh : h = Heap.emp := hh
    subst hh
    refine ⟨(safe_allocAt_iff 0 1 _).2 rfl, ?_⟩
    intro h' hr
    rcases hr with ⟨hne, _⟩ | ⟨_, he⟩
    · exact absurd rfl hne
    · injection he with he
  · intro ht
    have hpre : sep (sing Heap.emp) (sing (Heap.pt 0 2)) (union Heap.emp (Heap.pt 0 2)) :=
      ⟨Heap.emp, Heap.pt 0 2, fun _ => Or.inl rfl, rfl, rfl, rfl⟩
    have hs := (ht _ hpre).1
    rw [safe_allocAt_iff] at hs
    simp at hs

/-! ## `isAllocTest`: safety monotonicity holds, frame property fails -/

theorem isAllocTest_safetyMono (k r : Nat) : SafetyMono (isAllocTest k r) := by
  intro h h' _ hs
  rw [safe_isAllocTest_iff] at hs ⊢
  simp only [Heap.union_eq, Heap.join_val]
  cases e : h.val r with
  | none => exact absurd e hs
  | some w => simp

theorem isAllocTest_not_frameProp {k r : Nat} (hkr : k ≠ r) :
    ¬ FrameProp (isAllocTest k r) := by
  intro hfp
  have hd : disj (Heap.pt r 0 : Heap Nat) (Heap.pt k 7) := by
    intro j
    simp only [Heap.pt_val]
    by_cases hj : j = r
    · subst hj; simp [Ne.symm hkr]
    · simp [hj]
  have hs : Safe (isAllocTest k r) (Heap.pt r 0) :=
    (safe_isAllocTest_iff _ _ _).2 (by simp)
  have hrun : isAllocTest k r (union (Heap.pt r 0) (Heap.pt k 7))
      (.ok ((union (Heap.pt r 0) (Heap.pt k 7)).set r (some 1))) :=
    Or.inr (Or.inl ⟨by simp, by simp [hkr], rfl⟩)
  obtain ⟨h₀, hrun0, _, heq⟩ := hfp _ _ _ hd hs hrun
  rcases hrun0 with ⟨_, hf⟩ | ⟨_, hk, _⟩ | ⟨_, _, he⟩
  · cases hf
  · simp [hkr] at hk
  · injection he with he
    subst he
    have := congrArg (fun h : Heap Nat => h.val r) heq
    simp at this

/-- The side condition `k ≠ r` of `isAllocTest_not_frameProp` cannot be dropped:
when the tested cell is the result cell, the test always answers "allocated" (it
behaves like `[r] := 1`) and has the frame property. -/
theorem isAllocTest_self_frameProp (r : Nat) : FrameProp (isAllocTest r r) := by
  intro h h' h'' hd hs hrun
  rw [safe_isAllocTest_iff] at hs
  have h'r := Heap.right_none_of_disj hd hs
  have hx : (union h h').val r = h.val r := Heap.union_val_of_ne_none hs
  rcases hrun with ⟨hn, _⟩ | ⟨_, _, he⟩ | ⟨_, hn, _⟩
  · exact absurd (hx ▸ hn) hs
  · injection he with he
    refine ⟨h.set r (some 1), Or.inr (Or.inl ⟨hs, hs, rfl⟩), fun j => ?_, ?_⟩
    · by_cases hj : j = r
      · subst hj; exact Or.inr h'r
      · simp only [Heap.set_val, hj, ite_false]; exact hd j
    · rw [he]; exact (Heap.set_join h'r _).symm
  · exact absurd (hx ▸ hn) hs

/-- **Tightness of the frame property, via the allocation test** (canonical
form): `isAllocTest 1 0` is safety-monotone and satisfies
`{0 ↦ 0} isAllocTest 1 0 {0 ↦ 0}`, but the framed triple
`{(0 ↦ 0) * (1 ↦ 7)} isAllocTest 1 0 {(0 ↦ 0) * (1 ↦ 7)}` fails. -/
theorem isAllocTest_safetyMono_and_framed_triple_fails :
    SafetyMono (isAllocTest 1 0) ∧
    Triple (sing (Heap.pt 0 0)) (isAllocTest 1 0) (sing (Heap.pt 0 0)) ∧
    ¬ Triple (sep (sing (Heap.pt 0 0)) (sing (Heap.pt 1 7))) (isAllocTest 1 0)
        (sep (sing (Heap.pt 0 0)) (sing (Heap.pt 1 7))) := by
  refine ⟨isAllocTest_safetyMono 1 0, ?_, ?_⟩
  · intro h hh
    have hh : h = Heap.pt 0 0 := hh
    subst hh
    refine ⟨(safe_isAllocTest_iff _ _ _).2 (by simp), ?_⟩
    intro h' hr
    rcases hr with ⟨_, hf⟩ | ⟨_, hk, _⟩ | ⟨_, _, he⟩
    · cases hf
    · simp at hk
    · injection he with he
      subst he
      apply Heap.ext
      intro j
      by_cases hj : j = 0 <;> simp [hj]
  · intro ht
    have hd : disj (Heap.pt 0 0 : Heap Nat) (Heap.pt 1 7) := by
      intro j; by_cases hj : j = 0 <;> simp [hj]
    have hpre : sep (sing (Heap.pt 0 0)) (sing (Heap.pt 1 7))
        (union (Heap.pt 0 0 : Heap Nat) (Heap.pt 1 7)) :=
      ⟨_, _, hd, rfl, rfl, rfl⟩
    have hrun : isAllocTest 1 0 (union (Heap.pt 0 0 : Heap Nat) (Heap.pt 1 7))
        (.ok ((union (Heap.pt 0 0 : Heap Nat) (Heap.pt 1 7)).set 0 (some 1))) :=
      Or.inr (Or.inl ⟨by simp, by simp, rfl⟩)
    obtain ⟨q, r', _, heq, hq, hr'⟩ := (ht _ hpre).2 _ hrun
    have hq : q = Heap.pt 0 0 := hq
    have hr' : r' = Heap.pt 1 7 := hr'
    subst hq
    subst hr'
    have := congrArg (fun x : Heap Nat => x.val 0) heq
    simp at this

/-! ## `allocLeast`: safety monotonicity holds, frame property fails -/

theorem allocLeast_safetyMono (v : V) : SafetyMono (allocLeast v) :=
  fun _ _ _ _ => safe_allocLeast v _

theorem allocLeast_not_frameProp (v : V) : ¬ FrameProp (allocLeast v) := by
  intro hfp
  have hd : disj (Heap.emp : Heap V) (Heap.pt 0 v) := fun _ => Or.inl rfl
  have hrun : allocLeast v (union (Heap.emp : Heap V) (Heap.pt 0 v))
      (.ok ((union (Heap.emp : Heap V) (Heap.pt 0 v)).set 1 (some v))) := by
    refine ⟨1, by simp, ?_, rfl⟩
    intro j hj
    have : j = 0 := by omega
    subst this
    simp
  obtain ⟨h₀, ⟨k, _, hlt, he⟩, hd0, _⟩ := hfp _ _ _ hd (safe_allocLeast v _) hrun
  have hk0 : k = 0 := by
    cases k with
    | zero => rfl
    | succ k => exact absurd rfl (hlt 0 (by omega))
  subst hk0
  injection he with he
  subst he
  rcases hd0 0 with h1 | h1 <;> simp at h1

/-- **Tightness of the frame property, via deterministic allocation** (canonical
form): `allocLeast 1` is safety-monotone and satisfies `{emp} allocLeast 1 {0 ↦ 1}`,
but the framed triple `{emp * (0 ↦ 2)} allocLeast 1 {(0 ↦ 1) * (0 ↦ 2)}` fails. -/
theorem allocLeast_safetyMono_and_framed_triple_fails :
    SafetyMono (allocLeast (1 : Nat)) ∧
    Triple (sing Heap.emp) (allocLeast (1 : Nat)) (sing (Heap.pt 0 1)) ∧
    ¬ Triple (sep (sing Heap.emp) (sing (Heap.pt 0 2))) (allocLeast (1 : Nat))
        (sep (sing (Heap.pt 0 1)) (sing (Heap.pt 0 2))) := by
  refine ⟨allocLeast_safetyMono 1, ?_, ?_⟩
  · intro h hh
    have hh : h = Heap.emp := hh
    subst hh
    refine ⟨safe_allocLeast 1 _, ?_⟩
    rintro h' ⟨k, _, hlt, he⟩
    have hk0 : k = 0 := by
      cases k with
      | zero => rfl
      | succ k => exact absurd rfl (hlt 0 (by omega))
    subst hk0
    injection he with he
  · intro ht
    have hpre : sep (sing Heap.emp) (sing (Heap.pt 0 2))
        (union (Heap.emp : Heap Nat) (Heap.pt 0 2)) :=
      ⟨_, _, fun _ => Or.inl rfl, rfl, rfl, rfl⟩
    have hrun : allocLeast 1 (union (Heap.emp : Heap Nat) (Heap.pt 0 2))
        (.ok ((union (Heap.emp : Heap Nat) (Heap.pt 0 2)).set 1 (some 1))) := by
      refine ⟨1, by simp, ?_, rfl⟩
      intro j hj
      have : j = 0 := by omega
      subst this
      simp
    obtain ⟨q, r', hd, _, hq, hr'⟩ := (ht _ hpre).2 _ hrun
    have hq : q = Heap.pt 0 1 := hq
    have hr' : r' = Heap.pt 0 2 := hr'
    subst hq
    subst hr'
    rcases hd 0 with h1 | h1 <;> simp at h1

/-- `allocLeast 1` is not local (canonical counterexample for the frame-rule
hypothesis of the converse results: with that hypothesis dropped, the conclusion
fails). -/
theorem allocLeast_not_safetyMono_and_frameProp :
    ¬ (SafetyMono (allocLeast (1 : Nat)) ∧ FrameProp (allocLeast (1 : Nat))) :=
  fun h => allocLeast_not_frameProp 1 h.2

/-- **Tightness of the triple premise** (canonical form): `skip` is local, yet
`{P * R} skip {Q * R}` fails for `P = R = true`, `Q = false` (because the premise
`{P} skip {Q}` fails). -/
theorem skip_local_and_framed_triple_fails :
    SafetyMono (skip : Cmd (Heap Nat)) ∧ FrameProp (skip : Cmd (Heap Nat)) ∧
    ¬ Triple (sep (fun _ => True) (fun _ => True)) (skip : Cmd (Heap Nat))
        (sep (fun _ => False) (fun _ => True)) := by
  refine ⟨skip_safetyMono, skip_frameProp, ?_⟩
  intro ht
  obtain ⟨_, hpost⟩ := ht (union Heap.emp Heap.emp)
    ⟨Heap.emp, Heap.emp, fun _ => Or.inl rfl, rfl, trivial, trivial⟩
  obtain ⟨_, _, _, _, hf, _⟩ := hpost _ rfl
  exact hf

/-! ## Predictable allocation violates the frame property -/

/-- From the base heap `hb`, every normal outcome of `c` has address `a`
allocated: from `hb`, `c` always allocates (or keeps) a cell at the fixed address
`a`. Deterministic allocators satisfy this at every heap from which they run. -/
def AlwaysAllocatesAt (c : Cmd (Heap V)) (hb : Heap V) (a : Nat) : Prop :=
  ∀ h₀, c hb (.ok h₀) → h₀.val a ≠ none

/-- `c` has at least one normal run from `hb` extended by the one-cell heap
`a ↦ w`: `c` can still terminate normally when a frame occupies address `a`. -/
def RunsWhenOccupied (c : Cmd (Heap V)) (hb : Heap V) (a : Nat) (w : V) : Prop :=
  ∃ h'', c (union hb (Heap.pt a w)) (.ok h'')

theorem disj_pt_of_none {hb : Heap V} {a : Nat} (hfree : hb.val a = none) (w : V) :
    disj hb (Heap.pt a w) := by
  intro k
  by_cases hk : k = a
  · subst hk; exact Or.inl hfree
  · exact Or.inr (by simp [hk])

/-- **Impossibility: predictable allocation is not local.** Suppose that from some
base heap `hb` the command `c` is safe, every normal outcome allocates the fixed
address `a`, `a` is free in `hb`, and `c` still has a normal run when a frame
occupies `a`. Then `c` violates the frame property. (The frame property would
explain that run by a run from `hb` whose result avoids the frame's cell `a`.) -/
theorem not_frameProp_of_alwaysAllocatesAt_of_runsWhenOccupied
    {c : Cmd (Heap V)} {hb : Heap V} {a : Nat} {w : V}
    (hs : Safe c hb) (hfree : hb.val a = none)
    (hpred : AlwaysAllocatesAt c hb a) (hrun : RunsWhenOccupied c hb a w) :
    ¬ FrameProp c := by
  intro hfp
  obtain ⟨h'', hr⟩ := hrun
  obtain ⟨h₀, hr0, hd0, _⟩ := hfp hb (Heap.pt a w) h'' (disj_pt_of_none hfree w) hs hr
  rcases hd0 a with e | e
  · exact hpred h₀ hr0 e
  · simp at e

/-- **Corollary: no total deterministic single-cell writer is local.** For *every*
address-choice function `f` (fresh or not) and every value `v` (so `V` is
inhabited), the command that from each heap `h` terminates normally in exactly
`h[f h ↦ v]` violates the frame property. (Base heap `emp`, address `f emp`.) -/
theorem detAlloc_not_frameProp (f : Heap V → Nat) (v : V) : ¬ FrameProp (detAlloc f v) :=
  not_frameProp_of_alwaysAllocatesAt_of_runsWhenOccupied (hb := Heap.emp)
    (a := f Heap.emp) (w := v) (safe_detAlloc f v _) rfl
    (fun h₀ hr => by injection hr with hr; subst hr; simp) ⟨_, rfl⟩

/-- **Corollary: deterministic pointer-recording allocation with a fresh address
choice is not local.** If `f h` is fresh in `h` whenever cell `r` is allocated,
then `[r] := det_cons(v)` violates the frame property. (Base heap `r ↦ 0`.) -/
theorem detAllocInto_not_frameProp_of_fresh {f : Heap Nat → Nat} {r : Nat} (v : Nat)
    (hfresh : ∀ h : Heap Nat, h.val r ≠ none → h.val (f h) = none) :
    ¬ FrameProp (detAllocInto f r v) := by
  have hb : (Heap.pt r 0 : Heap Nat).val r ≠ none := by simp
  have hfree := hfresh _ hb
  have hne : f (Heap.pt r 0) ≠ r := by
    intro e; rw [e] at hfree; exact hb hfree
  refine not_frameProp_of_alwaysAllocatesAt_of_runsWhenOccupied (hb := Heap.pt r 0)
    (a := f (Heap.pt r 0)) (w := v) ((safe_detAllocInto_iff _ _ _ _).2 hb) hfree ?_ ?_
  · rintro h₀ (⟨hn, _⟩ | ⟨_, he⟩)
    · exact absurd hn hb
    · injection he with he; subst he; simp [hne]
  · exact ⟨_, Or.inr ⟨by rw [Heap.union_val_of_ne_none hb]; exact hb, rfl⟩⟩

/-- Freshness matters for pointer-recording allocation: with the non-fresh choice
`f _ = r`, `[r] := det_cons(v)` degenerates to the mutation `[r] := r` and has the
frame property. -/
theorem detAllocInto_self_frameProp (r v : Nat) :
    FrameProp (detAllocInto (fun _ => r) r v) := by
  intro h h' h'' hd hs hrun
  rw [safe_detAllocInto_iff] at hs
  have h'r := Heap.right_none_of_disj hd hs
  have hx : (union h h').val r = h.val r := Heap.union_val_of_ne_none hs
  rcases hrun with ⟨hn, _⟩ | ⟨_, he⟩
  · exact absurd (hx ▸ hn) hs
  · injection he with he
    refine ⟨(h.set r (some v)).set r (some r), Or.inr ⟨hs, rfl⟩, fun j => ?_, ?_⟩
    · by_cases hj : j = r
      · subst hj; exact Or.inr h'r
      · simp only [Heap.set_val, hj, ite_false]; exact hd j
    · rw [he]; apply Heap.ext; intro j
      by_cases hj : j = r
      · subst hj; simp
      · simp [hj]

/-- **Positive control (determinism dropped)**: allocation at a
nondeterministically chosen fresh address has the frame property. -/
theorem alloc_frameProp (v : V) : FrameProp (alloc v) := by
  intro h h' h'' hd _ hr
  obtain ⟨k, hk, he⟩ := hr
  injection he with he
  simp only [Heap.union_eq, Heap.join_val] at hk
  have hk1 : h.val k = none := by cases e : h.val k <;> simp_all
  have hk2 : h'.val k = none := by rw [hk1] at hk; simpa using hk
  refine ⟨h.set k (some v), ⟨k, hk1, rfl⟩, fun j => ?_, ?_⟩
  · by_cases hj : j = k
    · subst hj; exact Or.inr hk2
    · simp only [Heap.set_val, hj, ite_false]; exact hd j
  · rw [he]; exact (Heap.set_join hk2 _).symm

/-- **Positive control (running when the address is occupied dropped)**: a
deterministic allocator that only runs from the empty heap has the frame
property. -/
theorem detAllocOnEmp_frameProp (v : V) : FrameProp (detAllocOnEmp v) := by
  intro h h' h'' hd _ ⟨he, ho⟩
  have hboth : ∀ k, h.val k = none ∧ h'.val k = none := by
    intro k
    have := congrArg (fun x : Heap V => x.val k) he
    simp only [Heap.union_eq, Heap.join_val, Heap.emp_val] at this
    cases e1 : h.val k <;> cases e2 : h'.val k <;> simp_all
  have hh : h = Heap.emp := Heap.ext fun k => (hboth k).1
  have hh' : h' = Heap.emp := Heap.ext fun k => (hboth k).2
  subst hh; subst hh'
  injection ho with ho
  exact ⟨Heap.pt 0 v, ⟨rfl, rfl⟩, fun _ => Or.inr rfl, by rw [ho]; exact (Heap.join_emp _).symm⟩

/-! ### Tightness of each hypothesis of the impossibility (canonical form) -/

/-- A command that may fault from every heap, and otherwise sets address `0`. -/
def faultOrSet0 (v : V) : Cmd (Heap V) := fun h o => o = .fault ∨ o = .ok (h.set 0 (some v))

/-- **Tightness of `Safe c hb`**: `faultOrSet0 1` is unsafe at `emp`, but every
other hypothesis holds (base `emp`, address `0`, frame value `1`) and it has the
frame property (vacuously, since it is safe nowhere). -/
theorem faultOrSet0_not_safe_and_frameProp :
    ¬ Safe (faultOrSet0 (1 : Nat)) Heap.emp ∧ (Heap.emp : Heap Nat).val 0 = none ∧
    AlwaysAllocatesAt (faultOrSet0 (1 : Nat)) Heap.emp 0 ∧
    RunsWhenOccupied (faultOrSet0 (1 : Nat)) Heap.emp 0 1 ∧
    FrameProp (faultOrSet0 (1 : Nat)) := by
  refine ⟨fun hs => hs (Or.inl rfl), rfl, ?_, ⟨_, Or.inr rfl⟩, ?_⟩
  · rintro h₀ (hf | he)
    · cases hf
    · injection he with he; subst he; simp
  · intro _ _ _ _ hs _
    exact absurd (Or.inl rfl) hs

/-- **Tightness of `hb.val a = none`**: `skip` from the base heap `0 ↦ 1` is safe,
always "allocates" address `0` (it is already allocated), runs when a frame also
claims address `0`, and has the frame property. -/
theorem skip_occupied_base_and_frameProp :
    Safe (skip : Cmd (Heap Nat)) (Heap.pt 0 1) ∧ (Heap.pt 0 1 : Heap Nat).val 0 ≠ none ∧
    AlwaysAllocatesAt (skip : Cmd (Heap Nat)) (Heap.pt 0 1) 0 ∧
    RunsWhenOccupied (skip : Cmd (Heap Nat)) (Heap.pt 0 1) 0 2 ∧
    FrameProp (skip : Cmd (Heap Nat)) := by
  refine ⟨safe_skip _, by simp, ?_, ⟨_, rfl⟩, skip_frameProp⟩
  intro h₀ hr
  injection hr with hr
  subst hr
  simp

/-- **Tightness of `AlwaysAllocatesAt`** (positive control): nondeterministic
allocation `alloc 1` from `emp` is safe, `0` is free, it runs when a frame
occupies `0`, and it has the frame property; it may allocate address `1`
instead of `0`. -/
theorem alloc_not_alwaysAllocatesAt_and_frameProp :
    Safe (alloc (1 : Nat)) Heap.emp ∧ (Heap.emp : Heap Nat).val 0 = none ∧
    ¬ AlwaysAllocatesAt (alloc (1 : Nat)) Heap.emp 0 ∧
    RunsWhenOccupied (alloc (1 : Nat)) Heap.emp 0 1 ∧
    FrameProp (alloc (1 : Nat)) := by
  refine ⟨safe_alloc _ _, rfl, ?_, ⟨_, ⟨1, by simp, rfl⟩⟩, alloc_frameProp 1⟩
  intro hp
  exact hp _ ⟨1, rfl, rfl⟩ (by simp)

/-- **Tightness of `RunsWhenOccupied`** (positive control): `detAllocOnEmp 1` is
safe at `emp`, always allocates address `0` from `emp`, and has the frame
property; it has no run from the one-cell heap `0 ↦ 1`. -/
theorem detAllocOnEmp_not_runsWhenOccupied_and_frameProp :
    Safe (detAllocOnEmp (1 : Nat)) Heap.emp ∧ (Heap.emp : Heap Nat).val 0 = none ∧
    AlwaysAllocatesAt (detAllocOnEmp (1 : Nat)) Heap.emp 0 ∧
    ¬ RunsWhenOccupied (detAllocOnEmp (1 : Nat)) Heap.emp 0 1 ∧
    FrameProp (detAllocOnEmp (1 : Nat)) := by
  refine ⟨safe_detAllocOnEmp _ _, rfl, ?_, ?_, detAllocOnEmp_frameProp 1⟩
  · rintro h₀ ⟨_, he⟩
    injection he with he; subst he; simp
  · rintro ⟨_, he, _⟩
    have := congrArg (fun x : Heap Nat => x.val 0) he
    simp at this

/-- Non-vacuity of the impossibility: all four hypotheses hold for the
deterministic writer `detAlloc (fun _ => 0) 1` (base `emp`, address `0`). -/
theorem not_frameProp_of_alwaysAllocatesAt_nonvacuous :
    Safe (detAlloc (fun _ => 0) (1 : Nat)) Heap.emp ∧ (Heap.emp : Heap Nat).val 0 = none ∧
    AlwaysAllocatesAt (detAlloc (fun _ => 0) (1 : Nat)) Heap.emp 0 ∧
    RunsWhenOccupied (detAlloc (fun _ => 0) (1 : Nat)) Heap.emp 0 1 :=
  ⟨safe_detAlloc _ _ _, rfl, fun h₀ hr => by injection hr with hr; subst hr; simp, ⟨_, rfl⟩⟩

/-! ## Faulting on a larger heap breaks safety monotonicity -/

/-- If a heap command is safe on `emp` but can fault from some heap `h`, it is
not safety-monotone. In particular an allocator that faults when memory is
exhausted is not safety-monotone, whether or not its address choice is
deterministic. -/
theorem not_safetyMono_of_safe_emp_of_faults {c : Cmd (Heap V)} {h : Heap V}
    (hs : Safe c Heap.emp) (hf : c h .fault) : ¬ SafetyMono c := by
  intro hsm
  have := hsm Heap.emp h (fun _ => Or.inl rfl) hs
  rw [Heap.union_eq, Heap.emp_join] at this
  exact this hf

/-! ## Blocking instead of faulting at a fixed address is local -/

/-- Allocation at a fixed address that *blocks* when the address is taken is
safety-monotone and has the frame property: in this partial-correctness model
blocking is indistinguishable from divergence. -/
theorem allocAtBlock_safetyMono_and_frameProp (k : Nat) (v : V) :
    SafetyMono (allocAtBlock k v) ∧ FrameProp (allocAtBlock k v) := by
  refine ⟨fun _ _ _ _ => safe_allocAtBlock k v _, ?_⟩
  intro h h' h'' hd _ ⟨hu, ho⟩
  injection ho with ho
  simp only [Heap.union_eq, Heap.join_val] at hu
  have hh : h.val k = none := by cases e : h.val k <;> simp_all
  have hh' : h'.val k = none := by rw [hh] at hu; simpa using hu
  refine ⟨h.set k (some v), ⟨hh, rfl⟩, fun j => ?_, ?_⟩
  · by_cases hj : j = k
    · subst hj; exact Or.inr hh'
    · simp only [Heap.set_val, hj, ite_false]; exact hd j
  · rw [ho]; exact (Heap.set_join hh' _).symm

/-- `allocAtBlock 0 1` is local, but it has no outcome at all from `0 ↦ 2`
(it blocks): it is the blocking counterpart of the non-local `allocAt 0 1`. -/
theorem allocAtBlock_local_and_blocks_when_taken :
    Local (allocAtBlock 0 (1 : Nat)) ∧ ¬ ∃ o, allocAtBlock 0 (1 : Nat) (Heap.pt 0 2) o := by
  refine ⟨allocAtBlock_safetyMono_and_frameProp 0 1, ?_⟩
  rintro ⟨_, h0, _⟩
  simp at h0

/-! ## Fault avoidance is necessary -/

/-- **The frame rule needs fault-avoiding triples**: `assertAlloc 0` is local and
the non-fault-avoiding triple `{emp} assertAlloc 0 {false}` holds (every run from
`emp` faults), but the framed non-fault-avoiding triple
`{emp * (0 ↦ 1)} assertAlloc 0 {false * (0 ↦ 1)}` fails. -/
theorem assertAlloc_local_and_framed_weakTriple_fails :
    SafetyMono (assertAlloc (V := Nat) 0) ∧ FrameProp (assertAlloc (V := Nat) 0) ∧
    WeakTriple (sing Heap.emp) (assertAlloc (V := Nat) 0) (fun _ => False) ∧
    ¬ WeakTriple (sep (sing Heap.emp) (sing (Heap.pt 0 1))) (assertAlloc (V := Nat) 0)
        (sep (fun _ => False) (sing (Heap.pt 0 1))) := by
  refine ⟨assertAlloc_safetyMono 0, assertAlloc_frameProp 0, ?_, ?_⟩
  · intro h hh h' hr
    have hh : h = Heap.emp := hh
    subst hh
    rcases hr with ⟨_, hf⟩ | ⟨hne, _⟩
    · cases hf
    · exact hne rfl
  · intro ht
    have hpre : sep (sing Heap.emp) (sing (Heap.pt 0 1))
        (union (Heap.emp : Heap Nat) (Heap.pt 0 1)) :=
      ⟨_, _, fun _ => Or.inl rfl, rfl, rfl, rfl⟩
    have hrun : assertAlloc (V := Nat) 0 (union Heap.emp (Heap.pt 0 1))
        (.ok (union Heap.emp (Heap.pt 0 1))) :=
      Or.inr ⟨by simp, rfl⟩
    obtain ⟨_, _, _, _, hf, _⟩ := ht _ hpre _ hrun
    exact hf

/-! ## A degenerate frame class does not force locality -/

/-- In the heap model, *every* command satisfies the frame rule when the only
allowed frame is `emp`. -/
theorem frame_rule_with_emp_frame_trivial (c : Cmd (Heap V)) (P Q : Assn (Heap V))
    (ht : Triple P c Q) : Triple (sep P (sing Heap.emp)) c (sep Q (sing Heap.emp)) := by
  intro h ⟨f, e, _, he, hP, hE⟩
  have hE : e = Heap.emp := hE
  subst hE
  have hhf : h = f := by rw [he]; exact Heap.join_emp f
  subst hhf
  obtain ⟨hs, hpost⟩ := ht h hP
  exact ⟨hs, fun h' hr => ⟨h', Heap.emp, fun _ => Or.inr rfl, (Heap.join_emp h').symm,
    hpost h' hr, rfl⟩⟩

/-- **Restricting frames to `emp` admits non-local commands**: `allocLeast 1`
satisfies the frame rule for the frame `emp` (for all `P`, `Q`) but is not local.
Shows that the converse results need frames ranging over at least the singleton
assertions. -/
theorem allocLeast_frame_rule_for_emp_frame_and_not_local :
    (∀ P Q : Assn (Heap Nat), Triple P (allocLeast 1) Q →
        Triple (sep P (sing Heap.emp)) (allocLeast 1) (sep Q (sing Heap.emp))) ∧
    ¬ (SafetyMono (allocLeast (1 : Nat)) ∧ FrameProp (allocLeast (1 : Nat))) :=
  ⟨fun P Q => frame_rule_with_emp_frame_trivial _ P Q,
    allocLeast_not_safetyMono_and_frameProp⟩

end Toy.Sep
