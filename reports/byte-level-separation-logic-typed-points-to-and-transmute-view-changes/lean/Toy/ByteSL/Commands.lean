import Toy.ByteSL.Struct
import Toy.ByteSL.Shared

/-!
# Result group 5: a byte-level command language and the frame rule

Commands are relations on byte heaps (`Cmd (BHeap D)`), faulting when they touch memory without
the required permission. Reads need any permission (`full` or `ro`); writes need `full`.

Local commands:

* `bstore a b` — byte store `[a] := b`;
* `bcopy src dst` — byte copy `[dst] := [src]`, copying the abstract byte (`uninit` included);
* `tstore r a v` — typed store: writes `r.encode v` at `a`;
* `tcopy r src dst` — typed copy: typed load at `src` (decode; faults if the bytes do not decode),
  then typed store of the loaded value at `dst` (padding of the destination becomes whatever the
  encoder writes);
* `tload r a` — the heap footprint of a typed load into a variable outside the heap: faults unless
  the bytes at `a` are allocated and decode; leaves the heap unchanged and returns nothing.

Commands that read or write outside their permission:

* `bcopyLoose src dst` — a byte copy that reads an unallocated source cell as `uninit`;
* `tcopyLoose r src dst` — a typed copy that reads unallocated source cells as `uninit`;
* `bstoreShared a b` — a byte store permitted with read-only permission.

Results:

* `frameRuleSound_iff_safetyMono_and_frameProp` (R5a): in every separation structure (no algebraic
  law assumed; in particular on the byte heap with read-only sharing), the frame rule holds for a
  command exactly when it is safety-monotone and has the frame property.
* `byte_commands_local`, `typed_commands_local` (R5b): `bstore`, `bcopy` (no representation
  involved) and `tstore`, `tcopy`, `tload` (for every representation, no law needed) are local; and
  (`readBytes_frame_stable`) the bytes a read sees — hence the value a typed load decodes — are the
  same in every disjoint extension of the heap.
* `tcopyLoose_local_of_decodeMono` (R5c): the loose typed copy (unallocated source cells read as
  `uninit` instead of faulting) is local when the representation satisfies `DecodeMono`; for a
  representation violating it, it is not (`tcopyLoose_not_local_exactUnitRep`).
* `bcopyLoose_safetyMono_and_not_frameProp` (R5d, counterexample): the loose byte copy is
  safety-monotone but violates the frame property, and the frame rule fails for it.
* `bstoreShared_safetyMono_and_not_frameProp` (R5e, counterexample): a store through a read-only
  cell violates the frame property, and the frame rule fails for it.
* `byteHeap_isSepAlgebra_and_not_rightCancel` (R5f, counterexample): for every byte payload type,
  the byte heap with read-only sharing is a partial commutative monoid with unit but is not
  cancellative.

Commands have no variable store: a typed load's result is observable only by writing its
encoding back into the heap (`tcopy`) or not at all (`tload`).
-/

namespace Toy.ByteSL

open SepStruct

/-! ## Reading and writing cells -/

section Access

variable {D : Type}

/-- The bytes of the `n` cells `a, …, a + n - 1` if all are allocated (with any permission);
`none` otherwise. -/
def readBytes (h : BHeap D) (a n : Nat) : Option (Bytes D n) :=
  if hall : ∀ i, i < n → (h.val (a + i)).isSome = true then
    some (Vector.ofFn fun i => ((h.val (a + i.val)).get (hall i.val i.isLt)).byte)
  else none

/-- The bytes of the `n` cells at `a`, reading an unallocated cell as `uninit` (never fails). -/
def readLoose (h : BHeap D) (a n : Nat) : Bytes D n :=
  Vector.ofFn fun i => match h.val (a + i.val) with
    | some c => c.byte
    | none => .uninit

/-- All `n` cells at `a` are allocated with full permission. -/
def OwnsFull (h : BHeap D) (a n : Nat) : Prop :=
  ∀ i, i < n → ∃ b, h.val (a + i) = some ⟨.full, b⟩

/-- Overwrite the `n` cells at `a` with full permission and the bytes `x`. -/
def writeBytes {n : Nat} (h : BHeap D) (a : Nat) (x : Bytes D n) : BHeap D :=
  ⟨fun k => if hk : a ≤ k ∧ k < a + n then some ⟨.full, x[k - a]'(by omega)⟩ else h.val k, by
    obtain ⟨m, hm⟩ := h.finite
    refine ⟨max m (a + n), fun k hk => ?_⟩
    simp only [show ¬ (a ≤ k ∧ k < a + n) by omega, dite_false]
    exact hm k (by omega)⟩

theorem writeBytes_val_of_not {n : Nat} (h : BHeap D) (a : Nat) (x : Bytes D n) {k : Nat}
    (hk : ¬ (a ≤ k ∧ k < a + n)) : (writeBytes h a x).val k = h.val k := by
  show (if hk : a ≤ k ∧ k < a + n then _ else h.val k) = h.val k
  simp only [hk, dite_false]

end Access

/-! ## Commands -/

section Commands

variable {D V : Type} {n : Nat}

/-- Byte store `[a] := b`: faults unless cell `a` is held with full permission. -/
def bstore (a : Nat) (b : AByte D) : Cmd (BHeap D) := fun h o =>
  (¬ OwnsFull h a 1 ∧ o = .fault) ∨ (OwnsFull h a 1 ∧ o = .ok (writeBytes h a #v[b]))

/-- Byte copy `[dst] := [src]` of one abstract byte (`uninit` is copied as `uninit`): faults
unless `src` is allocated (any permission) and `dst` is held with full permission. -/
def bcopy (src dst : Nat) : Cmd (BHeap D) := fun h o =>
  ((readBytes h src 1 = none ∨ ¬ OwnsFull h dst 1) ∧ o = .fault) ∨
  (∃ x, readBytes h src 1 = some x ∧ OwnsFull h dst 1 ∧ o = .ok (writeBytes h dst x))

/-- Typed store of `v` at representation `r`: writes `r.encode v` at `a`; faults unless all `n`
cells are held with full permission. -/
def tstore (r : Rep (Bytes D n) V) (a : Nat) (v : V) : Cmd (BHeap D) := fun h o =>
  (¬ OwnsFull h a n ∧ o = .fault) ∨ (OwnsFull h a n ∧ o = .ok (writeBytes h a (r.encode v)))

/-- Typed copy at representation `r`: decode the `n` bytes at `src` (faulting if any is
unallocated or they do not decode) and store the encoding of the decoded value at `dst`
(faulting unless all `n` destination cells are held with full permission). -/
def tcopy (r : Rep (Bytes D n) V) (src dst : Nat) : Cmd (BHeap D) := fun h o =>
  ((¬ (∃ x v, readBytes h src n = some x ∧ r.decode x = some v) ∨ ¬ OwnsFull h dst n) ∧
      o = .fault) ∨
  (∃ x v, readBytes h src n = some x ∧ r.decode x = some v ∧ OwnsFull h dst n ∧
      o = .ok (writeBytes h dst (r.encode v)))

/-- Typed load at representation `r` into a variable outside the heap (the heap footprint of
`let x = *a;`): faults unless the `n` bytes at `a` are allocated (any permission) and decode;
otherwise leaves the heap unchanged. The decoded value is not returned (there is no variable store);
`readBytes_frame_stable` states that a frame does not change the bytes read. -/
def tload (r : Rep (Bytes D n) V) (a : Nat) : Cmd (BHeap D) := fun h o =>
  (¬ (∃ x v, readBytes h a n = some x ∧ r.decode x = some v) ∧ o = .fault) ∨
  ((∃ x v, readBytes h a n = some x ∧ r.decode x = some v) ∧ o = .ok h)

/-- A byte copy that reads an *unallocated* source cell as `uninit` instead of faulting (it
reads memory it does not own); faults unless `dst` is held with full permission. -/
def bcopyLoose (src dst : Nat) : Cmd (BHeap D) := fun h o =>
  (¬ OwnsFull h dst 1 ∧ o = .fault) ∨
  (OwnsFull h dst 1 ∧ o = .ok (writeBytes h dst (readLoose h src 1)))

/-- A typed copy that reads unallocated source cells as `uninit` instead of faulting (it may read
bytes it does not own, e.g. padding it was not given); faults if the bytes so read do not decode
or `dst` is not held with full permission. -/
def tcopyLoose (r : Rep (Bytes D n) V) (src dst : Nat) : Cmd (BHeap D) := fun h o =>
  ((¬ (∃ v, r.decode (readLoose h src n) = some v) ∨ ¬ OwnsFull h dst n) ∧ o = .fault) ∨
  (∃ v, r.decode (readLoose h src n) = some v ∧ OwnsFull h dst n ∧
      o = .ok (writeBytes h dst (r.encode v)))

/-- A byte store permitted with *read-only* permission (a write through a shared view): faults
only if cell `a` is unallocated; keeps the cell's permission. -/
def bstoreShared (a : Nat) (b : AByte D) : Cmd (BHeap D) := fun h o =>
  (h.val a = none ∧ o = .fault) ∨ (∃ c, h.val a = some c ∧ o = .ok (h.set a (some ⟨c.perm, b⟩)))

end Commands

/-! ## Proof helpers for R5b and R5c -/

/-- Reading allocated cells in a left-biased union returns the left heap's bytes. -/
theorem readBytes_union_of_some {D : Type} {h h' : BHeap D} {a n : Nat} {x : Bytes D n}
    (hr : readBytes h a n = some x) : readBytes (union h h') a n = some x := by
  unfold readBytes at hr ⊢
  split at hr
  · rename_i hall
    injection hr with hr
    subst hr
    have hall' : ∀ i, i < n → ((union h h').val (a + i)).isSome = true := by
      intro i hi
      have ec := option_eq_some_get (hall i hi)
      rw [BHeap.union_eq, Heap.join_val, ec]
      rfl
    rw [dite_eq_left_of_eq_true (eq_true hall')]
    congr 1
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    have ec := option_eq_some_get (hall i hi)
    have eu : (union h h').val (a + i) = some ((h.val (a + i)).get (hall i hi)) := by
      rw [BHeap.union_eq, Heap.join_val]
      exact congrArg (·.or (h'.val (a + i))) ec
    rw [option_get_eq_of_eq (hall' i hi) eu]
  · cases hr

theorem ownsFull_none_of_disj {D : Type} {h h' : BHeap D} {a n : Nat}
    (hd : disj h h') (hown : OwnsFull h a n) {i : Nat} (hi : i < n) : h'.val (a + i) = none := by
  obtain ⟨b, hb⟩ := hown i hi
  cases e : h'.val (a + i) with
  | none => rfl
  | some c =>
    have hro := (hd (a + i) _ _ hb e).1
    cases hro

theorem ownsFull_union {D : Type} {h h' : BHeap D} {a n : Nat}
    (hown : OwnsFull h a n) : OwnsFull (union h h') a n := by
  intro i hi
  obtain ⟨b, hb⟩ := hown i hi
  exact ⟨b, by simp [hb]⟩

/-- Writing cells held with full permission commutes with adding a disjoint frame. -/
theorem writeBytes_union_of_disj {D : Type} {n : Nat} {h h' : BHeap D} {a : Nat} (x : Bytes D n)
    (hd : disj h h') (hown : OwnsFull h a n) :
    disj (writeBytes h a x) h' ∧ writeBytes (union h h') a x = union (writeBytes h a x) h' := by
  constructor
  · intro k c₁ c₂ e1 e2
    by_cases hk : a ≤ k ∧ k < a + n
    · have hk_eq : k = a + (k - a) := by omega
      rw [hk_eq, ownsFull_none_of_disj hd hown (by omega)] at e2
      cases e2
    · rw [writeBytes_val_of_not h a x hk] at e1
      exact hd k c₁ c₂ e1 e2
  · apply Heap.ext
    intro k
    by_cases hk : a ≤ k ∧ k < a + n
    · simp [writeBytes, hk]
    · simp [writeBytes_val_of_not _ a x hk]

/-- Adding a frame can only make the loosely read bytes more defined. -/
theorem readLoose_le_union {D : Type} (h h' : BHeap D) (a n : Nat) :
    readLoose h a n ⊑ readLoose (union h h') a n := by
  intro i hi
  simp only [readLoose, Vector.getElem_ofFn, BHeap.union_eq, Heap.join_val]
  cases h.val (a + i) with
  | none => exact AByte.uninit_le _
  | some c => exact AByte.le_refl _

/-! ## R5a, R5b, R5c (statements) -/

/-- **R5a.** In every separation structure `S` (no algebraic law assumed — in particular on the
byte heap with read-only sharing, which is not cancellative), for every command `c`: the frame
rule is sound for `c` (for all assertions `P Q R`, `{P} c {Q}` implies `{P * R} c {Q * R}`) iff `c`
is safety-monotone and has the frame property. -/
theorem frameRuleSound_iff_safetyMono_and_frameProp {S : Type _} [SepStruct S] (c : Cmd S) :
    FrameRuleSound c ↔ SafetyMono c ∧ FrameProp c := by
  constructor
  · intro hFR
    refine ⟨fun h h' hd hs => ?_, fun h h' h'' hd hs hr => ?_⟩
    · exact (hFR (· = h) (c h ∘ .ok) (· = h') (fun _ e => by subst e; exact ⟨hs, fun _ => id⟩)
        (union h h') ⟨h, h', hd, rfl, rfl, rfl⟩).1
    · obtain ⟨h₀, h₂, hd₀, heq, hq, rfl⟩ :=
        (hFR (· = h) (c h ∘ .ok) (· = h') (fun _ e => by subst e; exact ⟨hs, fun _ => id⟩)
          (union h h') ⟨h, h', hd, rfl, rfl, rfl⟩).2 h'' hr
      exact ⟨h₀, hq, hd₀, heq⟩
  · rintro ⟨hSM, hFP⟩ P Q R hT _ ⟨h₁, h₂, hd, rfl, hP, hR⟩
    obtain ⟨hs, hQ⟩ := hT h₁ hP
    refine ⟨hSM h₁ h₂ hd hs, fun h'' hr => ?_⟩
    obtain ⟨h₀, hr₀, hd₀, rfl⟩ := hFP h₁ h₂ h'' hd hs hr
    exact ⟨h₀, h₂, hd₀, rfl, hQ h₀ hr₀, hR⟩

/-- **R5b, byte commands.** For every byte payload type, every byte store `bstore a b` (faults
unless cell `a` is held with full permission) and every byte copy `bcopy src dst` (faults unless
`src` is allocated with any permission and `dst` is held with full permission) is
safety-monotone and has the frame property on the byte heap with read-only sharing. -/
theorem byte_commands_local {D : Type} :
    (∀ (a : Nat) (b : AByte D), Local (bstore (D := D) a b)) ∧
      (∀ (src dst : Nat), Local (bcopy (D := D) src dst)) := by
  refine ⟨fun a b => ?_, fun src dst => ?_⟩
  · refine ⟨fun h h' _ hs hf => ?_, fun h h' h'' hd hs hr => ?_⟩
    · have hown : OwnsFull h a 1 := Classical.byContradiction fun hn => hs (Or.inl ⟨hn, rfl⟩)
      rcases hf with ⟨hn, _⟩ | ⟨_, ho⟩
      · exact hn (ownsFull_union hown)
      · cases ho
    · have hown : OwnsFull h a 1 := Classical.byContradiction fun hn => hs (Or.inl ⟨hn, rfl⟩)
      rcases hr with ⟨_, ho⟩ | ⟨_, ho⟩
      · cases ho
      · cases ho
        obtain ⟨hd0, heq⟩ := writeBytes_union_of_disj #v[b] hd hown
        exact ⟨_, Or.inr ⟨hown, rfl⟩, hd0, heq⟩
  · refine ⟨fun h h' _ hs hf => ?_, fun h h' h'' hd hs hr => ?_⟩
    · have hok : (∃ x, readBytes h src 1 = some x) ∧ OwnsFull h dst 1 := by
        refine ⟨?_, Classical.byContradiction fun hn => hs (Or.inl ⟨Or.inr hn, rfl⟩)⟩
        cases e : readBytes h src 1 with
        | none => exact absurd (Or.inl ⟨Or.inl e, rfl⟩) hs
        | some x => exact ⟨x, rfl⟩
      rcases hf with ⟨hfl | hfl, _⟩ | ⟨_, _, _, ho⟩
      · obtain ⟨x, hx⟩ := hok.1
        rw [readBytes_union_of_some hx] at hfl
        cases hfl
      · exact hfl (ownsFull_union hok.2)
      · cases ho
    · have hown : OwnsFull h dst 1 :=
        Classical.byContradiction fun hn => hs (Or.inl ⟨Or.inr hn, rfl⟩)
      have ⟨x, hx⟩ : ∃ x, readBytes h src 1 = some x := by
        cases e : readBytes h src 1 with
        | none => exact absurd (Or.inl ⟨Or.inl e, rfl⟩) hs
        | some x => exact ⟨x, rfl⟩
      rcases hr with ⟨_, ho⟩ | ⟨x', hx', _, ho⟩
      · cases ho
      · cases ho
        rw [readBytes_union_of_some hx] at hx'
        injection hx' with hx'
        subst hx'
        obtain ⟨hd0, heq⟩ := writeBytes_union_of_disj x hd hown
        exact ⟨_, Or.inr ⟨x, hx, hown, rfl⟩, hd0, heq⟩

/-- **R5b, typed commands.** For every representation `r` (no laws assumed), every typed store
`tstore r a v` (faults unless all `n` cells are held with full permission), typed copy
`tcopy r src dst` (faults unless the source cells are allocated with any permission and decode,
and the destination cells are held with full permission) and typed load `tload r a` (faults
unless the cells are allocated with any permission and decode; leaves the heap unchanged and
returns nothing) is safety-monotone and has the frame property on the byte heap with read-only
sharing. -/
theorem typed_commands_local {D V : Type} {n : Nat} (r : Rep (Bytes D n) V) :
    (∀ (a : Nat) (v : V), Local (tstore r a v)) ∧
      (∀ (src dst : Nat), Local (tcopy r src dst)) ∧
      (∀ (a : Nat), Local (tload r a)) := by
  refine ⟨fun a v => ?_, fun src dst => ?_, fun a => ?_⟩
  · refine ⟨fun h h' _ hs hf => ?_, fun h h' h'' hd hs hr => ?_⟩
    · have hown : OwnsFull h a n := Classical.byContradiction fun hn => hs (Or.inl ⟨hn, rfl⟩)
      rcases hf with ⟨hn, _⟩ | ⟨_, ho⟩
      · exact hn (ownsFull_union hown)
      · cases ho
    · have hown : OwnsFull h a n := Classical.byContradiction fun hn => hs (Or.inl ⟨hn, rfl⟩)
      rcases hr with ⟨_, ho⟩ | ⟨_, ho⟩
      · cases ho
      · cases ho
        obtain ⟨hd0, heq⟩ := writeBytes_union_of_disj (r.encode v) hd hown
        exact ⟨_, Or.inr ⟨hown, rfl⟩, hd0, heq⟩
  · refine ⟨fun h h' _ hs hf => ?_, fun h h' h'' hd hs hr => ?_⟩
    · have hdec : ∃ x w, readBytes h src n = some x ∧ r.decode x = some w :=
        Classical.byContradiction fun hn => hs (Or.inl ⟨Or.inl hn, rfl⟩)
      have hown : OwnsFull h dst n :=
        Classical.byContradiction fun hn => hs (Or.inl ⟨Or.inr hn, rfl⟩)
      rcases hf with ⟨hfl | hfl, _⟩ | ⟨_, _, _, _, _, ho⟩
      · obtain ⟨x, w, hx, hw⟩ := hdec
        exact hfl ⟨x, w, readBytes_union_of_some hx, hw⟩
      · exact hfl (ownsFull_union hown)
      · cases ho
    · have hdec : ∃ x w, readBytes h src n = some x ∧ r.decode x = some w :=
        Classical.byContradiction fun hn => hs (Or.inl ⟨Or.inl hn, rfl⟩)
      have hown : OwnsFull h dst n :=
        Classical.byContradiction fun hn => hs (Or.inl ⟨Or.inr hn, rfl⟩)
      rcases hr with ⟨_, ho⟩ | ⟨x', w', hx', hw', _, ho⟩
      · cases ho
      · cases ho
        obtain ⟨x, w, hx, hw⟩ := hdec
        rw [readBytes_union_of_some hx] at hx'
        injection hx' with hx'
        subst hx'
        rw [hw] at hw'
        injection hw' with hw'
        subst hw'
        obtain ⟨hd0, heq⟩ := writeBytes_union_of_disj (r.encode w) hd hown
        exact ⟨_, Or.inr ⟨x, w, hx, hw, hown, rfl⟩, hd0, heq⟩
  · refine ⟨fun h h' _ hs hf => ?_, fun h h' h'' hd hs hr => ?_⟩
    · have hdec : ∃ x w, readBytes h a n = some x ∧ r.decode x = some w :=
        Classical.byContradiction fun hn => hs (Or.inl ⟨hn, rfl⟩)
      rcases hf with ⟨hfl, _⟩ | ⟨_, ho⟩
      · obtain ⟨x, w, hx, hw⟩ := hdec
        exact hfl ⟨x, w, readBytes_union_of_some hx, hw⟩
      · cases ho
    · have hdec : ∃ x w, readBytes h a n = some x ∧ r.decode x = some w :=
        Classical.byContradiction fun hn => hs (Or.inl ⟨hn, rfl⟩)
      rcases hr with ⟨_, ho⟩ | ⟨_, ho⟩
      · cases ho
      · cases ho
        exact ⟨h, Or.inr ⟨hdec, rfl⟩, hd, rfl⟩

/-- **R5c.** For every representation `r` satisfying `DecodeMono` and all addresses `src`, `dst`:
the loose typed copy `tcopyLoose r src dst` — which reads each unallocated source cell as `uninit`
instead of faulting, faults if the bytes so read do not decode or the destination is not held with
full permission, and otherwise writes the encoding of the decoded value at `dst` — is
safety-monotone and has the frame property. (A frame can only make the bytes read more defined;
a monotone decoder then returns the same value.) -/
theorem tcopyLoose_local_of_decodeMono {D V : Type} {n : Nat} (r : Rep (Bytes D n) V)
    (hM : r.DecodeMono) (src dst : Nat) : Local (tcopyLoose r src dst) := by
  refine ⟨fun h h' _ hs hf => ?_, fun h h' h'' hd hs hr => ?_⟩
  · have hdec : ∃ w, r.decode (readLoose h src n) = some w :=
      Classical.byContradiction fun hn => hs (Or.inl ⟨Or.inl hn, rfl⟩)
    have hown : OwnsFull h dst n :=
      Classical.byContradiction fun hn => hs (Or.inl ⟨Or.inr hn, rfl⟩)
    rcases hf with ⟨hfl | hfl, _⟩ | ⟨_, _, _, ho⟩
    · obtain ⟨w, hw⟩ := hdec
      exact hfl ⟨w, OptLe.some_le_iff.mp (hw ▸ hM _ _ (readLoose_le_union h h' src n))⟩
    · exact hfl (ownsFull_union hown)
    · cases ho
  · have hdec : ∃ w, r.decode (readLoose h src n) = some w :=
      Classical.byContradiction fun hn => hs (Or.inl ⟨Or.inl hn, rfl⟩)
    have hown : OwnsFull h dst n :=
      Classical.byContradiction fun hn => hs (Or.inl ⟨Or.inr hn, rfl⟩)
    rcases hr with ⟨_, ho⟩ | ⟨w', hw', _, ho⟩
    · cases ho
    · cases ho
      obtain ⟨w, hw⟩ := hdec
      have hw_u : r.decode (readLoose (union h h') src n) = some w :=
        OptLe.some_le_iff.mp (hw ▸ hM _ _ (readLoose_le_union h h' src n))
      rw [hw_u] at hw'
      injection hw' with hw'
      subst hw'
      obtain ⟨hd0, heq⟩ := writeBytes_union_of_disj (r.encode w) hd hown
      exact ⟨_, Or.inr ⟨w, hw, hown, rfl⟩, hd0, heq⟩

/-! ## Concrete heaps used below -/

/-- The cell at address `1` held fully, `uninit`. -/
abbrev hDst : BHeap Byte := Heap.block .full 1 (#v[.uninit] : Bytes Byte 1)

/-- The cell at address `0` held fully, initialized to `5`. -/
abbrev hSrc5 : BHeap Byte := Heap.block .full 0 (#v[.init 5] : Bytes Byte 1)

theorem hDst_hSrc5_disj : disj hDst hSrc5 := by
  apply disj_of_forall_none
  intro k
  rcases k with _ | _ | k
  · left; decide
  · right; decide
  · left; exact Heap.block_val_of_ge _ _ _ (by omega)

theorem ownsFull_hDst : OwnsFull hDst 1 1 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  exact ⟨.uninit, by decide⟩

theorem ownsFull_join_hDst : OwnsFull (union hDst hSrc5) 1 1 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  exact ⟨.uninit, by decide⟩

/-! ## R5c tightness: the loose typed copy with a non-monotone decoder -/

/-- The loose typed copy at `exactUnitRep` is not safety-monotone. -/
theorem tcopyLoose_exactUnitRep_not_safetyMono : ¬ SafetyMono (tcopyLoose exactUnitRep 0 1) := by
  intro hsm
  have hsafe : Safe (tcopyLoose exactUnitRep 0 1) hDst := by
    rintro (⟨hf, _⟩ | ⟨_, _, _, ho⟩)
    · rcases hf with hf | hf
      · exact hf ⟨(), by decide⟩
      · exact hf ownsFull_hDst
    · cases ho
  apply hsm hDst hSrc5 hDst_hSrc5_disj hsafe
  refine Or.inl ⟨Or.inl ?_, rfl⟩
  rintro ⟨v, hv⟩
  cases v
  exact absurd hv (by decide)

/-- Tightness of `hM` in R5c: for `exactUnitRep` (only `[uninit]` decodes; violates
`DecodeMono`), the loose typed copy from `0` to `1` is safe in `hDst` (the unowned source reads
as `[uninit]`) but faults in `hDst ∘ hSrc5` (the source now reads as `[init 5]`), so it is not
safety-monotone. -/
theorem tcopyLoose_not_local_exactUnitRep :
    ¬ exactUnitRep.DecodeMono ∧ ¬ Local (tcopyLoose exactUnitRep 0 1) :=
  ⟨exactUnitRep_not_decodeMono, fun h => tcopyLoose_exactUnitRep_not_safetyMono h.1⟩

/-! ## R5d: the loose byte copy -/

/-- The loose byte copy cannot fault once the destination is owned with full permission, and this
is preserved by disjoint extension. -/
theorem bcopyLoose_safetyMono (src dst : Nat) : SafetyMono (bcopyLoose (D := Byte) src dst) := by
  intro h h' hd hs
  rintro (⟨hf, _⟩ | ⟨_, ho⟩)
  · apply hf
    intro i hi
    have hown : OwnsFull h dst 1 := by
      refine Classical.byContradiction fun hno => hs (Or.inl ⟨hno, rfl⟩)
    obtain ⟨b, hb⟩ := hown i hi
    exact ⟨b, by simp [hb]⟩
  · cases ho

/-- **R5d (counterexample).** The byte copy that reads an unallocated source cell as `uninit`
(`bcopyLoose 0 1`) is safety-monotone, but violates the frame property: in `hDst` it writes
`uninit` to cell `1`, while in `hDst ∘ hSrc5` it writes `init 5` there. The frame rule fails for
it: `{1 ↦ uninit} bcopyLoose 0 1 {cell 1 holds uninit}` holds, but its framing with `{0 ↦ 5}`
does not. -/
theorem bcopyLoose_safetyMono_and_not_frameProp :
    SafetyMono (bcopyLoose (D := Byte) 0 1) ∧ ¬ FrameProp (bcopyLoose (D := Byte) 0 1) ∧
      Triple (ptsB .full 1 (#v[.uninit] : Bytes Byte 1)) (bcopyLoose (D := Byte) 0 1)
        (fun h => h.val 1 = some ⟨.full, .uninit⟩) ∧
      ¬ Triple (sep (ptsB .full 1 (#v[.uninit] : Bytes Byte 1))
            (ptsB .full 0 (#v[.init 5] : Bytes Byte 1)))
          (bcopyLoose (D := Byte) 0 1)
          (sep (fun h => h.val 1 = some ⟨.full, .uninit⟩)
            (ptsB .full 0 (#v[.init 5] : Bytes Byte 1))) ∧
      ¬ FrameRuleSound (bcopyLoose (D := Byte) 0 1) := by
  have hsafe : Safe (bcopyLoose (D := Byte) 0 1) hDst := by
    rintro (⟨hf, _⟩ | ⟨_, ho⟩)
    · exact hf ownsFull_hDst
    · cases ho
  -- The unframed run writes `uninit`; the framed run writes `init 5`.
  have hrun₀ : ∀ h₀, bcopyLoose (D := Byte) 0 1 hDst (.ok h₀) → h₀.val 1 = some ⟨.full, .uninit⟩ := by
    rintro h₀ (⟨_, ho⟩ | ⟨_, ho⟩)
    · cases ho
    · cases ho; decide
  have hrun : bcopyLoose (D := Byte) 0 1 (union hDst hSrc5)
      (.ok (writeBytes (union hDst hSrc5) 1 (readLoose (union hDst hSrc5) 0 1))) :=
    Or.inr ⟨ownsFull_join_hDst, rfl⟩
  have hval : (writeBytes (union hDst hSrc5) 1 (readLoose (union hDst hSrc5) 0 1)).val 1 =
      some ⟨.full, .init 5⟩ := by decide
  have ht : Triple (ptsB .full 1 (#v[.uninit] : Bytes Byte 1)) (bcopyLoose (D := Byte) 0 1)
      (fun h => h.val 1 = some ⟨.full, .uninit⟩) := by
    intro h hP
    have hP' : h = hDst := hP
    subst hP'
    exact ⟨hsafe, hrun₀⟩
  have hnf : ¬ Triple (sep (ptsB .full 1 (#v[.uninit] : Bytes Byte 1))
        (ptsB .full 0 (#v[.init 5] : Bytes Byte 1)))
      (bcopyLoose (D := Byte) 0 1)
      (sep (fun h => h.val 1 = some ⟨.full, .uninit⟩)
        (ptsB .full 0 (#v[.init 5] : Bytes Byte 1))) := by
    intro hframed
    obtain ⟨_, hpost⟩ := hframed (union hDst hSrc5)
      ⟨hDst, hSrc5, hDst_hSrc5_disj, rfl, rfl, rfl⟩
    obtain ⟨h₁, h₂, _, he, hq, hr⟩ := hpost _ hrun
    have hr' : h₂ = hSrc5 := hr
    subst hr'
    have e := congrArg (fun h : BHeap Byte => h.val 1) he
    change _ = (h₁.val 1).or (hSrc5.val 1) at e
    rw [hval, hq] at e
    exact absurd e (by decide)
  refine ⟨bcopyLoose_safetyMono 0 1, fun H => ?_, ht, hnf, fun H => hnf (H _ _ _ ht)⟩
  obtain ⟨h₀, hr, _, he⟩ := H hDst hSrc5 _ hDst_hSrc5_disj hsafe hrun
  have e := congrArg (fun h : BHeap Byte => h.val 1) he
  change _ = (h₀.val 1).or (hSrc5.val 1) at e
  rw [hval, hrun₀ h₀ hr] at e
  exact absurd e (by decide)

/-! ## R5e: writing through a read-only cell -/

/-- The read-only cell at `0` holding `init 1`. -/
abbrev hRO1 : BHeap Byte := Heap.block .ro 0 (#v[.init 1] : Bytes Byte 1)

/-- A store through a read-only cell cannot fault once the cell is allocated, and this is preserved
by disjoint extension. -/
theorem bstoreShared_safetyMono (a : Nat) (b : AByte Byte) :
    SafetyMono (bstoreShared (D := Byte) a b) := by
  intro h h' _ hs
  rintro (⟨hf, _⟩ | ⟨_, _, ho⟩)
  · cases e : h.val a with
    | none => exact hs (Or.inl ⟨e, rfl⟩)
    | some c =>
      simp only [BHeap.union_eq, Heap.join_val, e] at hf
      cases hf
  · cases ho

/-- The read-only block `0 ↦ 2`, the result of storing `2` through the read-only cell `hRO1`. -/
abbrev hRO2 : BHeap Byte := Heap.block .ro 0 (#v[.init 2] : Bytes Byte 1)

theorem hRO1_set_eq_hRO2 : hRO1.set 0 (some ⟨.ro, .init 2⟩) = hRO2 := by
  apply Heap.ext
  intro k
  rcases k with _ | k
  · decide
  · simp only [Heap.set_val, Nat.add_one_ne_zero, ↓reduceIte]
    rw [Heap.block_val_of_ge _ _ _ (by omega), Heap.block_val_of_ge _ _ _ (by omega)]

/-- **R5e (counterexample).** A byte store permitted with read-only permission
(`bstoreShared 0 (init 2)`) is safety-monotone but violates the frame property: `hRO1` (the
read-only cell `0 ↦ 1`) is disjoint from itself, yet every run of the store from `hRO1` ends in a
heap (the cell `0 ↦ 2`) that is no longer disjoint from the frame `hRO1`. The frame rule fails for
it: `{0 ↦ro 1} bstoreShared 0 (init 2) {0 ↦ro 2}` holds, but its framing with `{0 ↦ro 1}` does
not. -/
theorem bstoreShared_safetyMono_and_not_frameProp :
    SafetyMono (bstoreShared (D := Byte) 0 (.init 2)) ∧
      ¬ FrameProp (bstoreShared (D := Byte) 0 (.init 2)) ∧
      disj hRO1 hRO1 ∧
      (∀ h₀, bstoreShared (D := Byte) 0 (.init 2) hRO1 (.ok h₀) → ¬ disj h₀ hRO1) ∧
      Triple (ptsB .ro 0 (#v[.init 1] : Bytes Byte 1)) (bstoreShared (D := Byte) 0 (.init 2))
        (ptsB .ro 0 (#v[.init 2] : Bytes Byte 1)) ∧
      ¬ Triple (sep (ptsB .ro 0 (#v[.init 1] : Bytes Byte 1)) (ptsB .ro 0 (#v[.init 1] : Bytes Byte 1)))
          (bstoreShared (D := Byte) 0 (.init 2))
          (sep (ptsB .ro 0 (#v[.init 2] : Bytes Byte 1)) (ptsB .ro 0 (#v[.init 1] : Bytes Byte 1))) ∧
      ¬ FrameRuleSound (bstoreShared (D := Byte) 0 (.init 2)) := by
  have hsafe : Safe (bstoreShared (D := Byte) 0 (.init 2)) hRO1 := by
    rintro (⟨hf, _⟩ | ⟨_, _, ho⟩)
    · exact absurd hf (by decide)
    · cases ho
  have hv0 : hRO1.val 0 = some ⟨.ro, .init 1⟩ := by decide
  have hruns : ∀ h₀, bstoreShared (D := Byte) 0 (.init 2) hRO1 (.ok h₀) → h₀ = hRO2 := by
    rintro h₀ (⟨_, ho⟩ | ⟨c, hc, ho⟩)
    · cases ho
    · cases ho
      rw [hv0] at hc
      injection hc with hc
      subst hc
      exact hRO1_set_eq_hRO2
  have hnd : ¬ disj hRO2 hRO1 := fun hd =>
    absurd (hd 0 ⟨.ro, .init 2⟩ ⟨.ro, .init 1⟩ (by decide) hv0).2 (by decide)
  have hnot : ∀ h₀, bstoreShared (D := Byte) 0 (.init 2) hRO1 (.ok h₀) → ¬ disj h₀ hRO1 :=
    fun h₀ hr => (hruns h₀ hr) ▸ hnd
  have hrun : bstoreShared (D := Byte) 0 (.init 2) (union hRO1 hRO1)
      (.ok ((union hRO1 hRO1).set 0 (some ⟨.ro, .init 2⟩))) :=
    Or.inr ⟨⟨.ro, .init 1⟩, by decide, rfl⟩
  have ht : Triple (ptsB .ro 0 (#v[.init 1] : Bytes Byte 1)) (bstoreShared (D := Byte) 0 (.init 2))
      (ptsB .ro 0 (#v[.init 2] : Bytes Byte 1)) := by
    intro h hP
    have hP' : h = hRO1 := hP
    subst hP'
    exact ⟨hsafe, fun h₀ hr => hruns h₀ hr⟩
  have hnf : ¬ Triple (sep (ptsB .ro 0 (#v[.init 1] : Bytes Byte 1)) (ptsB .ro 0 (#v[.init 1] : Bytes Byte 1)))
      (bstoreShared (D := Byte) 0 (.init 2))
      (sep (ptsB .ro 0 (#v[.init 2] : Bytes Byte 1)) (ptsB .ro 0 (#v[.init 1] : Bytes Byte 1))) := by
    intro hframed
    obtain ⟨_, hpost⟩ := hframed (union hRO1 hRO1) ⟨hRO1, hRO1, disj_block_ro_self 0 _, rfl, rfl, rfl⟩
    obtain ⟨h₁, h₂, hd, -, hq, hr⟩ := hpost _ hrun
    have hq' : h₁ = hRO2 := hq
    have hr' : h₂ = hRO1 := hr
    subst hq' hr'
    exact hnd hd
  refine ⟨bstoreShared_safetyMono 0 _, fun H => ?_, disj_block_ro_self 0 _, hnot, ht, hnf,
    fun H => hnf (H _ _ _ ht)⟩
  obtain ⟨h₀, hr, hd, _⟩ := H hRO1 hRO1 _ (disj_block_ro_self 0 _) hsafe hrun
  exact hnot h₀ hr hd

/-! ## R5f: the byte heap with read-only sharing is not cancellative -/

/-- The byte heap with read-only sharing is a partial commutative monoid with unit `emp`. -/
theorem byteHeap_isSepAlgebra (D : Type) : IsSepAlgebra (BHeap D) Heap.emp := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b hab k c₁ c₂ e1 e2
    obtain ⟨hro, heq⟩ := hab k c₂ c₁ e2 e1
    subst heq
    exact ⟨hro, rfl⟩
  · intro a b hab
    apply Heap.ext
    intro k
    simp only [BHeap.union_eq, Heap.join_val]
    cases ea : a.val k with
    | none => cases b.val k <;> rfl
    | some c₁ =>
      cases eb : b.val k with
      | none => rfl
      | some c₂ =>
        obtain ⟨_, heq⟩ := hab k c₁ c₂ ea eb
        subst heq
        rfl
  · intro a b c hab habc
    refine ⟨?_, ?_, ?_⟩
    · intro k c₂ c₃ eb ec
      cases ea : a.val k with
      | none =>
        exact habc k c₂ c₃ (by simp [ea, eb]) ec
      | some c₁ =>
        obtain ⟨_, h12⟩ := hab k c₁ c₂ ea eb
        subst h12
        exact habc k c₁ c₃ (by simp [ea]) ec
    · intro k c₁ c' ea ebc
      cases eb : b.val k with
      | some c₂ =>
        simp only [BHeap.union_eq, Heap.join_val, eb, Option.some_or, Option.some.injEq] at ebc
        rw [← ebc]
        exact hab k c₁ c₂ ea eb
      | none =>
        simp only [BHeap.union_eq, Heap.join_val, eb, Option.none_or] at ebc
        exact habc k c₁ c' (by simp [ea]) ebc
    · apply Heap.ext
      intro k
      simp only [BHeap.union_eq, Heap.join_val]
      cases a.val k <;> cases b.val k <;> cases c.val k <;> rfl
  · intro a
    refine ⟨fun k c₁ _ e1 _ => (by cases e1), ?_⟩
    apply Heap.ext
    intro k
    rfl

/-- The read-only cell `0 ↦ uninit`, over any byte payload type. -/
abbrev roUninitCell (D : Type) : BHeap D := Heap.block .ro 0 (#v[.uninit] : Bytes D 1)

/-- **R5f (counterexample).** For every byte payload type `D`, the byte heap with read-only sharing
is a partial commutative monoid with unit `emp`, but it is not right-cancellative: the read-only
cell `0 ↦ uninit` is disjoint from itself and from `emp`, and combined with itself it gives the
same heap as `emp` combined with it, although the cell is not `emp`. -/
theorem byteHeap_isSepAlgebra_and_not_rightCancel (D : Type) :
    IsSepAlgebra (BHeap D) Heap.emp ∧ ¬ RightCancel (BHeap D) ∧
      disj (roUninitCell D) (roUninitCell D) ∧ disj (Heap.emp : BHeap D) (roUninitCell D) ∧
      union (roUninitCell D) (roUninitCell D) = union (Heap.emp : BHeap D) (roUninitCell D) ∧
      roUninitCell D ≠ Heap.emp := by
  have hsa := byteHeap_isSepAlgebra D
  have hd : disj (roUninitCell D) (roUninitCell D) := disj_block_ro_self 0 _
  have he : disj (Heap.emp : BHeap D) (roUninitCell D) := (hsa.unit (roUninitCell D)).1
  have heq : union (roUninitCell D) (roUninitCell D) = union (Heap.emp : BHeap D) (roUninitCell D) :=
    (Heap.join_self _).trans (hsa.unit (roUninitCell D)).2.symm
  have hne : roUninitCell D ≠ Heap.emp := fun h => by
    have e := congrArg (fun h : BHeap D => h.val 0) h
    have e0 : (roUninitCell D).val 0 = some ⟨.ro, .uninit⟩ :=
      Heap.block_val_add .ro 0 (#v[.uninit] : Bytes D 1) (i := 0) (by decide)
    simp only [e0, Heap.emp_val] at e
    cases e
  exact ⟨hsa, fun H => hne (H _ _ _ hd he heq), hd, he, heq, hne⟩

/-! ## R5b supplement: reads see the same bytes in every disjoint extension -/

/-- **R5b, value stability.** If the cells `a, …, a + n - 1` are allocated in `h` and hold the
bytes `x`, then in every disjoint extension of `h` — with the frame on either side — they still
hold exactly `x`. So the value a typed load (or the source read of a typed copy) decodes is the
same with and without the frame. -/
theorem readBytes_frame_stable {D : Type} {h h' : BHeap D} (hd : disj h h') {a n : Nat}
    {x : Bytes D n} (hr : readBytes h a n = some x) :
    readBytes (union h h') a n = some x ∧ readBytes (union h' h) a n = some x := by
  refine ⟨readBytes_union_of_some hr, ?_⟩
  rw [← (byteHeap_isSepAlgebra D).comm h h' hd]
  exact readBytes_union_of_some hr

/-! ## R5c supplement: the loose typed copy reads cells the frame owns -/

/-- A heap owning the source data byte `0 ↦ 5` and the destination cells `2, 3`, but not the source
padding byte at address `1`. -/
abbrev hLoose : BHeap Byte :=
  union (Heap.block .full 0 (#v[.init 5] : Bytes Byte 1))
    (Heap.block .full 2 (#v[.uninit, .uninit] : Bytes Byte 2))

/-- A frame holding the address `1` with **full** permission. -/
abbrev hFrame1 : BHeap Byte := Heap.block .full 1 (#v[.init 9] : Bytes Byte 1)

/-- What R5c's locality does and does not mean: the loose typed copy at `u8PadRep` from `0` to
`2` runs in `hLoose ∘ hFrame1`, where the frame holds the source padding byte `1` with full
(exclusive) permission; the copy reads that byte (`readLoose` returns `[init 5, init 9]`) and
succeeds. In the model this is harmless (the monotone decoder ignores the byte), but an operational
semantics in which reading memory exclusively owned by someone else is undefined behavior or a
data race does not license this footprint. -/
theorem tcopyLoose_reads_frame_owned_full_cell :
    disj hLoose hFrame1 ∧ hFrame1.val 1 = some ⟨.full, .init 9⟩ ∧
      readLoose (union hLoose hFrame1) 0 2 = #v[.init 5, .init 9] ∧
      tcopyLoose u8PadRep 0 2 (union hLoose hFrame1)
        (.ok (writeBytes (union hLoose hFrame1) 2 (u8PadRep.encode 5))) := by
  refine ⟨?_, by decide, by decide, Or.inr ⟨5, by decide, ?_, rfl⟩⟩
  · apply disj_of_forall_none
    intro k
    rcases k with _ | _ | _ | _ | k
    · right; decide
    · left; decide
    · right; decide
    · right; decide
    · left
      simp only [BHeap.union_eq, Heap.join_val]
      rw [Heap.block_val_of_ge _ _ _ (by omega), Heap.block_val_of_ge _ _ _ (by omega)]
      rfl
  · intro i hi
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
    · exact ⟨.uninit, by decide⟩
    · exact ⟨.uninit, by decide⟩

/-! ## Non-vacuity -/

/-- Non-vacuity for R5a: a nontrivial triple for the byte store holds (`{0 ↦ uninit} [0] := 1
{0 ↦ 1}`), so `FrameRuleSound` has non-vacuous premises. -/
theorem byteHeap_frameRule_nonvacuous :
    Triple (ptsB .full 0 (#v[.uninit] : Bytes Byte 1)) (bstore (D := Byte) 0 (.init 1))
      (ptsB .full 0 (#v[.init 1] : Bytes Byte 1)) := by
  intro h hP
  have hP' : h = Heap.block .full 0 #v[.uninit] := hP
  subst hP'
  have hown : OwnsFull (Heap.block .full 0 (#v[.uninit] : Bytes Byte 1)) 0 1 := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    exact ⟨.uninit, by decide⟩
  refine ⟨?_, ?_⟩
  · rintro (⟨hf, _⟩ | ⟨_, ho⟩)
    · exact hf hown
    · cases ho
  · rintro h' (⟨_, ho⟩ | ⟨_, ho⟩)
    · cases ho
    · cases ho
      show _ = _
      apply Heap.ext
      intro k
      rcases k with _ | k
      · decide
      · rw [writeBytes_val_of_not _ _ _ (by omega), Heap.block_val_of_ge _ _ _ (by omega),
          Heap.block_val_of_ge _ _ _ (by omega)]

/-- Non-vacuity for R5b: each command has a normal outcome from some heap (the typed commands at
the `u8` representation). -/
theorem byte_and_typed_commands_nonvacuous :
    bstore (D := Byte) 1 (.init 7) hDst (.ok (writeBytes hDst 1 #v[.init 7])) ∧
      bcopy (D := Byte) 0 1 (union hDst hSrc5)
        (.ok (writeBytes (union hDst hSrc5) 1 #v[.init 5])) ∧
      tstore u8Rep 1 (7 : Byte) hDst (.ok (writeBytes hDst 1 #v[.init 7])) ∧
      tcopy u8Rep 0 1 (union hDst hSrc5)
        (.ok (writeBytes (union hDst hSrc5) 1 (u8Rep.encode 5))) ∧
      tload u8Rep 0 hSrc5 (.ok hSrc5) := by
  refine ⟨Or.inr ⟨ownsFull_hDst, rfl⟩, Or.inr ⟨#v[.init 5], by decide, ownsFull_join_hDst, rfl⟩,
    Or.inr ⟨ownsFull_hDst, rfl⟩,
    Or.inr ⟨#v[.init 5], 5, by decide, rfl, ownsFull_join_hDst, rfl⟩,
    Or.inr ⟨⟨#v[.init 5], 5, by decide, rfl⟩, rfl⟩⟩

/-- Non-vacuity for R5c: `u8PadRep` satisfies `DecodeMono`, and the loose typed copy runs from a
heap that owns the source data byte but not the source padding byte. -/
theorem tcopyLoose_local_nonvacuous :
    u8PadRep.DecodeMono ∧
      tcopyLoose u8PadRep 0 2
        (union (Heap.block .full 0 (#v[.init 5] : Bytes Byte 1))
          (Heap.block .full 2 (#v[.uninit, .uninit] : Bytes Byte 2)))
        (.ok (writeBytes (union (Heap.block .full 0 (#v[.init 5] : Bytes Byte 1))
          (Heap.block .full 2 (#v[.uninit, .uninit] : Bytes Byte 2))) 2 (u8PadRep.encode 5))) := by
  refine ⟨u8PadRep_decodeMono, Or.inr ⟨5, by decide, ?_, rfl⟩⟩
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · exact ⟨.uninit, by decide⟩
  · exact ⟨.uninit, by decide⟩

/-! ## Hypotheses of `readBytes_frame_stable` -/

/-- Tightness of `hd : disj h h'` in `readBytes_frame_stable`: `h` holds `0 ↦ 1` and `h'` holds
`0 ↦ 2`, both with full permission, so they are not disjoint; `readBytes h 0 1 = some [init 1]`
holds, but the conclusion fails. Its left-framed conjunct still holds, because `union` is
left-biased on overlapping cells; the right-framed conjunct `readBytes (union h' h) 0 1` returns
`h'`'s byte. -/
theorem readBytes_frame_stable_tight_hd :
    let h : BHeap Byte := Heap.block .full 0 (#v[.init 1] : Bytes Byte 1)
    let h' : BHeap Byte := Heap.block .full 0 (#v[.init 2] : Bytes Byte 1)
    readBytes h 0 1 = some #v[.init 1] ∧
      ¬ disj h h' ∧
      readBytes (union h h') 0 1 = some #v[.init 1] ∧
      ¬ (readBytes (union h h') 0 1 = some #v[.init 1] ∧
          readBytes (union h' h) 0 1 = some #v[.init 1]) := by
  intro h h'
  refine ⟨by decide, ?_, by decide, ?_⟩
  · intro hd
    exact absurd (hd 0 ⟨.full, .init 1⟩ ⟨.full, .init 2⟩ (by decide) (by decide)).1 (by decide)
  · rintro ⟨_, hr2⟩
    exact absurd hr2 (by decide)

/-- Tightness of `hr : readBytes h a n = some x` in `readBytes_frame_stable`: the empty heap is
disjoint from itself, but cell `0` is unallocated, so it reads as `none` rather than
`some [init 1]`, and the conclusion fails. -/
theorem readBytes_frame_stable_tight_hr :
    disj (Heap.emp : BHeap Byte) Heap.emp ∧
      readBytes (Heap.emp : BHeap Byte) 0 1 ≠ some (#v[.init 1] : Bytes Byte 1) ∧
      ¬ (readBytes (union (Heap.emp : BHeap Byte) Heap.emp) 0 1 = some #v[.init 1] ∧
          readBytes (union (Heap.emp : BHeap Byte) Heap.emp) 0 1 = some #v[.init 1]) :=
  ⟨(byteHeap_isSepAlgebra Byte).unit Heap.emp |>.1, by decide, fun ⟨h1, _⟩ => absurd h1 (by decide)⟩

/-- Non-vacuity of `readBytes_frame_stable` with an overlapping read-only frame: the heap
`hDst ∘ hRO1` (cell `1` fully owned and `uninit`, cell `0` read-only holding `1`) and the frame
`hRO1` share the read-only cell `0` and are disjoint; the read of cell `0` returns `[init 1]` with
the frame on either side, and the typed copy and typed load at `u8Rep` from address `0` run in the
framed heap. -/
theorem readBytes_frame_stable_shared_ro_nonvacuous :
    let hBase : BHeap Byte := union hDst hRO1
    disj hBase hRO1 ∧
      readBytes hBase 0 1 = some #v[.init 1] ∧
      readBytes (union hBase hRO1) 0 1 = some #v[.init 1] ∧
      readBytes (union hRO1 hBase) 0 1 = some #v[.init 1] ∧
      tcopy u8Rep 0 1 (union hBase hRO1)
        (.ok (writeBytes (union hBase hRO1) 1 (u8Rep.encode 1))) ∧
      tload u8Rep 0 (union hBase hRO1) (.ok (union hBase hRO1)) := by
  intro hBase
  have hdisj : disj hBase hRO1 := by
    intro k c₁ c₂ e1 e2
    rcases k with _ | _ | k
    · have hc1 : c₁ = ⟨.ro, .init 1⟩ := by
        have : hBase.val 0 = some ⟨.ro, .init 1⟩ := by decide
        rw [this] at e1; injection e1 with e1; exact e1.symm
      have hc2 : c₂ = ⟨.ro, .init 1⟩ := by
        have : hRO1.val 0 = some ⟨.ro, .init 1⟩ := by decide
        rw [this] at e2; injection e2 with e2; exact e2.symm
      subst hc1 hc2; exact ⟨rfl, rfl⟩
    · have : hRO1.val 1 = none := by decide
      rw [this] at e2; cases e2
    · have : hRO1.val (k + 2) = none := Heap.block_val_of_ge _ _ _ (by omega)
      rw [this] at e2; cases e2
  have hrd : readBytes hBase 0 1 = some #v[.init 1] := by decide
  have ⟨hr1, hr2⟩ := readBytes_frame_stable hdisj hrd
  have hown : OwnsFull (union hBase hRO1) 1 1 := fun i hi => by
    have : i = 0 := by omega
    subst this
    exact ⟨.uninit, by decide⟩
  exact ⟨hdisj, hrd, hr1, hr2,
    Or.inr ⟨#v[.init 1], 1, hr1, rfl, hown, rfl⟩,
    Or.inr ⟨⟨#v[.init 1], 1, hr1, rfl⟩, rfl⟩⟩

end Toy.ByteSL
