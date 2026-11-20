import Toy.ByteSL.ReprExamples
import Toy.ByteSL.SepBasic

/-!
# The byte heap with a two-point permission per byte

Heaps are *finite* partial maps from addresses (`Nat`) to cells. A cell holds an abstract byte
(`AByte D`: `uninit` or `init d`, the vocabulary of the published package
`byte-representation-galois-laws-and-transmute-composition`) together with a permission:

* `Perm.full` — exclusive ownership (read and write);
* `Perm.ro` — read-only ownership, freely duplicable.

Disjointness is cell-wise: at every address at most one side has a cell, *or* both sides have the
**same** cell with permission `ro`. Union takes each cell from the left if it is allocated there,
otherwise from the right. So read-only cells combine idempotently (`ro` + `ro` = `ro`, with
agreement on the byte), and a `full` cell is incompatible with any other cell at the same address.
This is the two-point permission algebra "full | read-only" (read-only combines idempotently with
itself; full combines with nothing), the algebra `{R, RW}` of Calcagno, O'Hearn and Yang (LICS
2007); there are no fractions, so read-only ownership can never be recombined into full ownership.
No order on permissions is used anywhere.
-/

namespace Toy.ByteSL

open SepStruct

/-! ## Finite partial maps -/

/-- A finite heap: a partial map `Nat → Option C` with finitely many allocated addresses. -/
structure Heap (C : Type) where
  /-- The contents of each address (`none` = unallocated). -/
  val : Nat → Option C
  /-- Only finitely many addresses are allocated. -/
  finite : ∃ n, ∀ k, n ≤ k → val k = none

namespace Heap

variable {C : Type}

theorem ext {h₁ h₂ : Heap C} (hv : ∀ k, h₁.val k = h₂.val k) : h₁ = h₂ := by
  cases h₁; cases h₂
  have : _ := funext hv
  subst this
  rfl

/-- The empty heap. -/
def emp : Heap C := ⟨fun _ => none, ⟨0, fun _ _ => rfl⟩⟩

/-- Overwrite address `k` with `o` (`some c` allocates/updates, `none` frees). -/
def set (h : Heap C) (k : Nat) (o : Option C) : Heap C :=
  ⟨fun j => if j = k then o else h.val j, by
    obtain ⟨n, hn⟩ := h.finite
    refine ⟨max n (k + 1), fun j hj => ?_⟩
    have hjk : j ≠ k := by omega
    have hjn : n ≤ j := by omega
    simp [hjk, hn j hjn]⟩

/-- Heap union: each cell is taken from `h₁` if allocated there, else from `h₂`. -/
def join (h₁ h₂ : Heap C) : Heap C :=
  ⟨fun k => (h₁.val k).or (h₂.val k), by
    obtain ⟨n₁, hn₁⟩ := h₁.finite
    obtain ⟨n₂, hn₂⟩ := h₂.finite
    refine ⟨max n₁ n₂, fun k hk => ?_⟩
    have e1 := hn₁ k (by omega)
    have e2 := hn₂ k (by omega)
    simp [e1, e2]⟩

@[simp] theorem emp_val (k : Nat) : (emp : Heap C).val k = none := rfl

@[simp] theorem set_val (h : Heap C) (k : Nat) (o : Option C) (j : Nat) :
    (h.set k o).val j = if j = k then o else h.val j := rfl

@[simp] theorem join_val (h₁ h₂ : Heap C) (k : Nat) :
    (h₁.join h₂).val k = (h₁.val k).or (h₂.val k) := rfl

end Heap

/-! ## Permissions and cells -/

/-- The two-point permission algebra: `full` (exclusive, read and write) and `ro` (read-only,
duplicable). Two `ro` cells at one address combine (if they hold the same byte); `full` combines
with nothing. -/
inductive Perm where
  /-- Exclusive ownership: the byte may be read and written. -/
  | full : Perm
  /-- Read-only ownership: the byte may be read; the cell may be shared. -/
  | ro : Perm
  deriving DecidableEq

/-- A heap cell: a permission and an abstract byte. -/
structure Cell (D : Type) where
  /-- The permission held on this byte. -/
  perm : Perm
  /-- The abstract byte stored (possibly `uninit`). -/
  byte : AByte D
  deriving DecidableEq

/-- Byte heaps: finite partial maps from addresses to cells. -/
abbrev BHeap (D : Type) := Heap (Cell D)

/-- Disjointness of byte heaps: wherever both heaps have a cell, the two cells are equal and
read-only. -/
def BHeap.Disj {D : Type} (h₁ h₂ : BHeap D) : Prop :=
  ∀ k c₁ c₂, h₁.val k = some c₁ → h₂.val k = some c₂ → c₁.perm = .ro ∧ c₁ = c₂

instance (D : Type) : SepStruct (BHeap D) where
  disj := BHeap.Disj
  union := Heap.join

namespace BHeap

variable {D : Type}

@[simp] theorem disj_iff (h₁ h₂ : BHeap D) :
    disj h₁ h₂ ↔ ∀ k c₁ c₂, h₁.val k = some c₁ → h₂.val k = some c₂ → c₁.perm = .ro ∧ c₁ = c₂ :=
  Iff.rfl

@[simp] theorem union_eq (h₁ h₂ : BHeap D) : union h₁ h₂ = h₁.join h₂ := rfl

end BHeap

/-! ## Contiguous blocks of cells -/

/-- `blockOn p a x keep`: the heap whose allocated addresses are exactly `a + i` for `i < n` with
`keep i = true`; cell `a + i` holds permission `p` and byte `x[i]`. -/
def Heap.blockOn {D : Type} {n : Nat} (p : Perm) (a : Nat) (x : Bytes D n) (keep : Nat → Bool) :
    BHeap D where
  val k :=
    if hk : a ≤ k ∧ k < a + n then
      (if keep (k - a) then some ⟨p, x[k - a]'(by omega)⟩ else none)
    else none
  finite := ⟨a + n, fun k hk => by simp only [show ¬ (a ≤ k ∧ k < a + n) by omega, dite_false]⟩

/-- `block p a x`: exactly the `n` cells `a, …, a + n - 1`, with permission `p` and bytes `x`. -/
def Heap.block {D : Type} {n : Nat} (p : Perm) (a : Nat) (x : Bytes D n) : BHeap D :=
  Heap.blockOn p a x (fun _ => true)

namespace Heap

variable {D : Type} {n : Nat}

theorem blockOn_val (p : Perm) (a : Nat) (x : Bytes D n) (keep : Nat → Bool) (k : Nat) :
    (blockOn p a x keep).val k =
      if hk : a ≤ k ∧ k < a + n then
        (if keep (k - a) then some ⟨p, x[k - a]'(by omega)⟩ else none)
      else none := rfl

theorem blockOn_val_of_lt (p : Perm) (a : Nat) (x : Bytes D n) (keep : Nat → Bool) {k : Nat}
    (hk : k < a) : (blockOn p a x keep).val k = none := by
  rw [blockOn_val]; simp only [show ¬ (a ≤ k ∧ k < a + n) by omega, dite_false]

theorem blockOn_val_of_ge (p : Perm) (a : Nat) (x : Bytes D n) (keep : Nat → Bool) {k : Nat}
    (hk : a + n ≤ k) : (blockOn p a x keep).val k = none := by
  rw [blockOn_val]; simp only [show ¬ (a ≤ k ∧ k < a + n) by omega, dite_false]

theorem blockOn_val_add (p : Perm) (a : Nat) (x : Bytes D n) (keep : Nat → Bool) {i : Nat}
    (hi : i < n) :
    (blockOn p a x keep).val (a + i) = if keep i then some ⟨p, x[i]⟩ else none := by
  rw [blockOn_val]
  simp only [show a ≤ a + i ∧ a + i < a + n by omega, Nat.add_sub_cancel_left]
  rfl

theorem block_val_add (p : Perm) (a : Nat) (x : Bytes D n) {i : Nat} (hi : i < n) :
    (block p a x).val (a + i) = some ⟨p, x[i]⟩ := by
  unfold block
  rw [blockOn_val_add p a x _ hi]
  rfl

theorem block_val_of_lt (p : Perm) (a : Nat) (x : Bytes D n) {k : Nat} (hk : k < a) :
    (block p a x).val k = none := blockOn_val_of_lt p a x _ hk

theorem block_val_of_ge (p : Perm) (a : Nat) (x : Bytes D n) {k : Nat} (hk : a + n ≤ k) :
    (block p a x).val k = none := blockOn_val_of_ge p a x _ hk

/-- A block determines its bytes. -/
theorem block_inj {p : Perm} {a : Nat} {x y : Bytes D n} (h : block p a x = block p a y) :
    x = y := by
  apply Vector.ext
  intro i hi
  have e := congrArg (fun h : BHeap D => h.val (a + i)) h
  simp only [block_val_add p a _ hi] at e
  injection e with e
  injection e

/-- A nonempty block determines its permission. -/
theorem block_perm_inj {p q : Perm} {a : Nat} {x y : Bytes D n} (hn : 0 < n)
    (h : block p a x = block q a y) : p = q := by
  have e := congrArg (fun h : BHeap D => h.val (a + 0)) h
  simp only [block_val_add p a _ hn, block_val_add q a _ hn] at e
  injection e with e
  injection e

end Heap

/-! ## Byte points-to and the definedness order on heaps -/

/-- **Byte points-to** `a ↦ᵦ[p] x`: the heap is exactly the `n` cells `a, …, a + n - 1`, each with
permission `p`, holding the abstract bytes `x` (an exact footprint, as for the standard points-to
of separation logic). -/
def ptsB {D : Type} {n : Nat} (p : Perm) (a : Nat) (x : Bytes D n) : Assn (BHeap D) :=
  fun h => h = Heap.block p a x

/-- The **byte-definedness order** lifted to heaps: `HeapByteLe h h'` iff `h` and `h'` have the
same allocated addresses, the same permission at each, and each byte of `h'` is at least as
defined as the byte of `h` (`uninit` may have become initialized; initialized bytes are
unchanged). This is *not* the heap-extension (sub-heap) order of separation logic: the domain is
fixed. -/
def HeapByteLe {D : Type} (h h' : BHeap D) : Prop :=
  ∀ k, (h.val k = none ↔ h'.val k = none) ∧
    ∀ c c', h.val k = some c → h'.val k = some c' → c.perm = c'.perm ∧ c.byte ⊑ c'.byte

/-- **Byte-definedness upward closure** of an assertion: the heaps obtained from a heap satisfying
`P` by initializing zero or more of its `uninit` bytes (same addresses, same permissions, same
initialized bytes). Not to be confused with the upward closure under heap extension (`P * True`)
of intuitionistic separation logic, which adds cells; this closure never adds or removes cells. -/
def byteUpClose {D : Type} (P : Assn (BHeap D)) : Assn (BHeap D) :=
  fun h => ∃ h₀, P h₀ ∧ HeapByteLe h₀ h

/-- Two blocks at the same address with the same permission are related by `HeapByteLe` when their
bytes are related by the pointwise definedness order. -/
theorem heapByteLe_block_of_le {D : Type} {n : Nat} (p : Perm) (a : Nat) {x y : Bytes D n}
    (hxy : x ⊑ y) : HeapByteLe (Heap.block p a x) (Heap.block p a y) := by
  intro k
  by_cases hk : a ≤ k ∧ k < a + n
  · obtain ⟨i, rfl⟩ : ∃ i, k = a + i := ⟨k - a, by omega⟩
    have hi : i < n := by omega
    rw [Heap.block_val_add p a x hi, Heap.block_val_add p a y hi]
    refine ⟨⟨fun h => (nomatch h), fun h => (nomatch h)⟩, ?_⟩
    intro c c' hc hc'
    cases hc; cases hc'
    exact ⟨rfl, hxy i hi⟩
  · have e1 : (Heap.block p a x).val k = none := by
      unfold Heap.block; rw [Heap.blockOn_val]; simp only [hk, dite_false]
    have e2 : (Heap.block p a y).val k = none := by
      unfold Heap.block; rw [Heap.blockOn_val]; simp only [hk, dite_false]
    rw [e1, e2]
    exact ⟨Iff.rfl, fun c c' hc _ => by cases hc⟩

end Toy.ByteSL
