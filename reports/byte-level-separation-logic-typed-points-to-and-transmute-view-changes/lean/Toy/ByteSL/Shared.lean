import Toy.ByteSL.PointsTo

/-!
# Result group 4: shared (read-only) typed views of the same bytes

With read-only permission, cells combine idempotently, so two typed views of the same `n` bytes
can be separated from each other: `a ↦dec[rA, ro] v ∗ a ↦dec[rB, ro] w`. With full permission
on either side they cannot.

Results (all fully proved):

* R4a, three statements: `sep_ro_ptsDec_iff_block_decodes` — a heap satisfies the separating
  conjunction of two read-only decode-based typed views at the same address exactly when it is the
  read-only block of some byte vector that decodes to `v` under `rA` and to `w` under `rB`;
  `sep_ro_ptsDec_satisfiable_iff_common_bytes` — hence the conjunction is satisfiable exactly when
  some byte vector decodes to both; `sep_ro_ptsEnc_satisfiable_iff_encode_eq` — for encode-based
  views, satisfiable exactly when the two encodings are the same byte vector (a separate statement,
  not a consequence of the decode-based one).
* `not_sep_ptsDec_of_full_of_pos_size` (R4b, impossibility): for a nonzero size, if either view
  holds full permission, no heap satisfies the separating conjunction of the two views.
-/

namespace Toy.ByteSL

open SepStruct

/-! ## Helper lemmas -/

theorem Heap.blockOn_perm_of_val_eq_some {D : Type} {n : Nat} {p : Perm} {a : Nat}
    {x : Bytes D n} {keep : Nat → Bool} {k : Nat} {c : Cell D}
    (e : (Heap.blockOn p a x keep).val k = some c) : c.perm = p := by
  rw [Heap.blockOn_val] at e
  split at e
  · split at e
    · cases e; rfl
    · cases e
  · cases e

theorem Heap.block_perm_of_val_eq_some {D : Type} {n : Nat} {p : Perm} {a : Nat}
    {x : Bytes D n} {k : Nat} {c : Cell D}
    (e : (Heap.block p a x).val k = some c) : c.perm = p :=
  Heap.blockOn_perm_of_val_eq_some e

/-- A read-only block is disjoint from itself. -/
theorem disj_block_ro_self {D : Type} {n : Nat} (a : Nat) (x : Bytes D n) :
    disj (Heap.block .ro a x) (Heap.block .ro a x) := by
  intro k c₁ c₂ e1 e2
  rw [e1] at e2
  cases e2
  exact ⟨Heap.block_perm_of_val_eq_some e1, rfl⟩

/-- Union is idempotent. -/
theorem Heap.join_self {C : Type} (h : Heap C) : h.join h = h := by
  apply Heap.ext
  intro k
  simp only [Heap.join_val]
  cases h.val k <;> rfl

/-- Two disjoint read-only blocks at the same address hold the same bytes. -/
theorem eq_of_disj_block_ro {D : Type} {n : Nat} {a : Nat} {x y : Bytes D n}
    (hd : disj (Heap.block .ro a x) (Heap.block .ro a y)) : x = y := by
  apply Vector.ext
  intro i hi
  have := (hd (a + i) _ _ (Heap.block_val_add .ro a x hi) (Heap.block_val_add .ro a y hi)).2
  injection this

/-! ## R4a: read-only views coexist iff a common byte vector decodes under both -/

/-- **R4a.** For representations `rA`, `rB` of equal size `n`, address `a`, values `v`, `w` and
heap `h`: `h` satisfies the separating conjunction of the read-only decode-based typed points-to
of `v` at `rA` and of `w` at `rB`, both at `a`, iff `h` is the read-only block at `a` of some byte
vector `x` with `rA.decode x = some v` and `rB.decode x = some w`. -/
theorem sep_ro_ptsDec_iff_block_decodes {D A B : Type} {n : Nat}
    (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B) (a : Nat) (v : A) (w : B) (h : BHeap D) :
    sep (ptsDec .ro rA a v) (ptsDec .ro rB a w) h ↔
      ∃ x : Bytes D n, h = Heap.block .ro a x ∧ rA.decode x = some v ∧ rB.decode x = some w := by
  constructor
  · rintro ⟨h₁, h₂, hd, he, ⟨x, hx, hdA⟩, ⟨y, hy, hdB⟩⟩
    have hx' : h₁ = Heap.block .ro a x := hx
    have hy' : h₂ = Heap.block .ro a y := hy
    subst hx' hy'
    have hxy := eq_of_disj_block_ro hd
    subst hxy
    exact ⟨x, he.trans (Heap.join_self _), hdA, hdB⟩
  · rintro ⟨x, rfl, hdA, hdB⟩
    exact ⟨Heap.block .ro a x, Heap.block .ro a x, disj_block_ro_self a x,
      (Heap.join_self _).symm, ⟨x, rfl, hdA⟩, ⟨x, rfl, hdB⟩⟩

/-- Corollary of R4a: the separating conjunction of two read-only decode-based typed views at the
same address is satisfiable iff some byte vector decodes to `v` under `rA` and to `w` under
`rB`. -/
theorem sep_ro_ptsDec_satisfiable_iff_common_bytes {D A B : Type} {n : Nat}
    (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B) (a : Nat) (v : A) (w : B) :
    (∃ h : BHeap D, sep (ptsDec .ro rA a v) (ptsDec .ro rB a w) h) ↔
      ∃ x : Bytes D n, rA.decode x = some v ∧ rB.decode x = some w := by
  constructor
  · rintro ⟨h, hs⟩
    obtain ⟨x, _, hA, hB⟩ := (sep_ro_ptsDec_iff_block_decodes rA rB a v w h).mp hs
    exact ⟨x, hA, hB⟩
  · rintro ⟨x, hA, hB⟩
    exact ⟨_, (sep_ro_ptsDec_iff_block_decodes rA rB a v w _).mpr ⟨x, rfl, hA, hB⟩⟩

/-- Encode-based analogue of R4a: two read-only encode-based typed views at the same address can
be separated from each other iff the two encodings are the same byte vector. -/
theorem sep_ro_ptsEnc_satisfiable_iff_encode_eq {D A B : Type} {n : Nat}
    (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B) (a : Nat) (v : A) (w : B) :
    (∃ h : BHeap D, sep (ptsEnc .ro rA a v) (ptsEnc .ro rB a w) h) ↔ rA.encode v = rB.encode w := by
  constructor
  · rintro ⟨h, h₁, h₂, hd, _, hA, hB⟩
    have hA' : h₁ = Heap.block .ro a (rA.encode v) := hA
    have hB' : h₂ = Heap.block .ro a (rB.encode w) := hB
    subst hA' hB'
    exact eq_of_disj_block_ro hd
  · intro he
    refine ⟨Heap.block .ro a (rA.encode v), Heap.block .ro a (rA.encode v),
      Heap.block .ro a (rA.encode v), disj_block_ro_self a _, (Heap.join_self _).symm, rfl, ?_⟩
    show Heap.block .ro a (rA.encode v) = Heap.block .ro a (rB.encode w)
    rw [he]

/-- Non-vacuity for R4a: the byte `1` is read-only-viewed both as the `u8` value `1` and as the
`bool` value `true`; and no read-only `bool` view coexists with the `u8` view of `2`. -/
theorem sep_ro_ptsDec_nonvacuous :
    sep (ptsDec .ro u8Rep 0 (1 : Byte)) (ptsDec .ro boolRep 0 true)
        (Heap.block .ro 0 #v[.init 1]) ∧
      ∀ b : Bool, ¬ ∃ h : BHeap Byte, sep (ptsDec .ro u8Rep 0 (2 : Byte)) (ptsDec .ro boolRep 0 b) h := by
  refine ⟨(sep_ro_ptsDec_iff_block_decodes _ _ _ _ _ _).mpr ⟨_, rfl, rfl, rfl⟩, fun b hb => ?_⟩
  obtain ⟨x, hA, hB⟩ := (sep_ro_ptsDec_satisfiable_iff_common_bytes _ _ _ _ _).mp hb
  have hle := u8Rep_encodeLeast x 2 hA
  have hx0 : x[0] = .init 2 := (AByte.init_le_iff).mp (hle 0 (by decide))
  rw [boolRep, byteRep_decode, hx0] at hB
  revert hB
  cases b <;> decide

/-! ## R4b: full permission excludes any second view -/

/-- **R4b (impossibility).** For representations `rA`, `rB` of equal nonzero size `n`, if at least
one of the permissions `p`, `q` is `full`, then no heap satisfies the separating conjunction of the
decode-based typed points-to of `v` at `rA` with permission `p` and of `w` at `rB` with permission
`q`, both at the same address `a`. -/
theorem not_sep_ptsDec_of_full_of_pos_size {D A B : Type} {n : Nat} (hn : 0 < n)
    (rA : Rep (Bytes D n) A) (rB : Rep (Bytes D n) B) (p q : Perm) (hpq : p = .full ∨ q = .full)
    (a : Nat) (v : A) (w : B) (h : BHeap D) :
    ¬ sep (ptsDec p rA a v) (ptsDec q rB a w) h := by
  rintro ⟨h₁, h₂, hd, -, ⟨x, hx, -⟩, ⟨y, hy, -⟩⟩
  have hx' : h₁ = Heap.block p a x := hx
  have hy' : h₂ = Heap.block q a y := hy
  subst hx' hy'
  obtain ⟨hro, heq⟩ := hd (a + 0) _ _ (Heap.block_val_add p a x hn) (Heap.block_val_add q a y hn)
  have hp : p = .ro := hro
  have hqp : p = q := by injection heq
  subst hp
  rcases hpq with h1 | h1
  · cases h1
  · rw [← hqp] at h1; cases h1

/-- Positive control for R4b: with read-only permission on both sides the conclusion fails — the
two views of the byte `1` (at `u8Rep` and at `boolRep`) coexist. -/
theorem not_sep_ptsDec_positive_control :
    ∃ h : BHeap Byte, sep (ptsDec .ro u8Rep 0 (1 : Byte)) (ptsDec .ro boolRep 0 true) h :=
  ⟨_, sep_ro_ptsDec_nonvacuous.1⟩

/-- A zero-size representation of `Unit`. -/
def zeroUnitRep : Rep (Bytes Byte 0) Unit := ⟨fun _ => #v[], fun _ => some ()⟩

/-- Tightness of `hn` in R4b (canonical form): at size `0` (`¬ 0 < 0`), with `p = q = full` (so
`hpq` holds), two full-permission views coexist (in the empty block). -/
theorem not_sep_ptsDec_tight_hn :
    ¬ (0 < 0) ∧ (Perm.full = .full ∨ Perm.full = .full) ∧
      ∃ h : BHeap Byte, sep (ptsDec .full zeroUnitRep 0 ()) (ptsDec .full zeroUnitRep 0 ()) h := by
  refine ⟨by decide, Or.inl rfl, Heap.block .full 0 #v[], Heap.block .full 0 #v[],
    Heap.block .full 0 #v[], ?_, (Heap.join_self _).symm, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  intro k c₁ c₂ e1 _
  rw [Heap.block_val_of_ge _ _ _ (by omega)] at e1
  cases e1

/-- Tightness of `hpq` in R4b (canonical form): at size `1` (`0 < 1` holds) with both permissions
read-only (`hpq` fails), the two views of the byte `1` at `u8Rep` and at `boolRep` coexist. -/
theorem not_sep_ptsDec_tight_hpq :
    0 < 1 ∧ ¬ (Perm.ro = .full ∨ Perm.ro = .full) ∧
      ∃ h : BHeap Byte, sep (ptsDec .ro u8Rep 0 (1 : Byte)) (ptsDec .ro boolRep 0 true) h := by
  refine ⟨by decide, fun h => ?_, not_sep_ptsDec_positive_control⟩
  rcases h with h | h <;> cases h

/-- Non-vacuity for R4b: its hypotheses hold for `u8Rep`, `boolRep` at size 1 with `p = full`,
and the full-permission view alone is satisfiable. -/
theorem not_sep_ptsDec_nonvacuous :
    0 < 1 ∧ (Perm.full = .full ∨ Perm.ro = .full) ∧
      ptsDec .full u8Rep 0 (1 : Byte) (Heap.block .full 0 #v[.init 1]) ∧
      ptsDec .ro boolRep 0 true (Heap.block .ro 0 #v[.init 1]) :=
  ⟨by decide, Or.inl rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

end Toy.ByteSL
