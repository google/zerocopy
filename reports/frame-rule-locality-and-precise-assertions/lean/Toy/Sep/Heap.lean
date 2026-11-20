import Toy.Sep.Basic

/-!
# The heap model

Heaps are *finite* partial maps from addresses (`Nat`) to values (`V`),
represented as `Nat → Option V` together with a proof that only finitely many
addresses are allocated. Two heaps are disjoint when no address is allocated in
both; their union takes each cell from whichever side has it. This is the
standard heap model of separation logic (without a separate variable store:
commands that would write a program variable are modelled either by their heap
footprint alone or by writing to a designated heap cell).
-/

namespace Toy.Sep

open SepStruct

/-- A finite heap: a partial map `Nat → Option V` with finitely many allocated
addresses. -/
structure Heap (V : Type) where
  /-- The contents of each address (`none` = unallocated). -/
  val : Nat → Option V
  /-- Only finitely many addresses are allocated. -/
  finite : ∃ n, ∀ k, n ≤ k → val k = none

namespace Heap

variable {V : Type}

theorem ext {h₁ h₂ : Heap V} (hv : ∀ k, h₁.val k = h₂.val k) : h₁ = h₂ := by
  cases h₁; cases h₂
  have : _ := funext hv
  subst this
  rfl

/-- The empty heap. -/
def emp : Heap V := ⟨fun _ => none, ⟨0, fun _ _ => rfl⟩⟩

/-- Overwrite address `k` with `o` (`some v` allocates/updates, `none` frees). -/
def set (h : Heap V) (k : Nat) (o : Option V) : Heap V :=
  ⟨fun j => if j = k then o else h.val j, by
    obtain ⟨n, hn⟩ := h.finite
    refine ⟨max n (k + 1), fun j hj => ?_⟩
    have hjk : j ≠ k := by omega
    have hjn : n ≤ j := by omega
    simp [hjk, hn j hjn]⟩

/-- The singleton heap `k ↦ v`. -/
def pt (k : Nat) (v : V) : Heap V := emp.set k (some v)

/-- Heap disjointness: no address is allocated in both heaps. -/
def Disj (h₁ h₂ : Heap V) : Prop := ∀ k, h₁.val k = none ∨ h₂.val k = none

/-- Heap union: each cell is taken from `h₁` if allocated there, else from `h₂`.
Meaningful (and commutative) only on disjoint heaps. -/
def join (h₁ h₂ : Heap V) : Heap V :=
  ⟨fun k => (h₁.val k).or (h₂.val k), by
    obtain ⟨n₁, hn₁⟩ := h₁.finite
    obtain ⟨n₂, hn₂⟩ := h₂.finite
    refine ⟨max n₁ n₂, fun k hk => ?_⟩
    have e1 := hn₁ k (by omega)
    have e2 := hn₂ k (by omega)
    simp [e1, e2]⟩

@[simp] theorem emp_val (k : Nat) : (emp : Heap V).val k = none := rfl

@[simp] theorem set_val (h : Heap V) (k : Nat) (o : Option V) (j : Nat) :
    (h.set k o).val j = if j = k then o else h.val j := rfl

@[simp] theorem join_val (h₁ h₂ : Heap V) (k : Nat) :
    (h₁.join h₂).val k = (h₁.val k).or (h₂.val k) := rfl

@[simp] theorem pt_val (k : Nat) (v : V) (j : Nat) :
    (pt k v).val j = if j = k then some v else none := by
  simp [pt]

end Heap

instance (V : Type) : SepStruct (Heap V) where
  disj := Heap.Disj
  union := Heap.join

namespace Heap

variable {V : Type}

@[simp] theorem disj_iff (h₁ h₂ : Heap V) :
    disj h₁ h₂ ↔ ∀ k, h₁.val k = none ∨ h₂.val k = none := Iff.rfl

@[simp] theorem union_eq (h₁ h₂ : Heap V) : union h₁ h₂ = h₁.join h₂ := rfl

theorem join_comm {h₁ h₂ : Heap V} (hd : Heap.Disj h₁ h₂) : h₁.join h₂ = h₂.join h₁ := by
  apply ext; intro k
  rcases hd k with h | h <;> cases e1 : h₁.val k <;> cases e2 : h₂.val k <;> simp_all

theorem join_emp (h : Heap V) : h.join emp = h := by
  apply ext; intro k; simp

theorem emp_join (h : Heap V) : emp.join h = h := by
  apply ext; intro k; simp

/-- Updating a cell that is unallocated in the frame commutes with adding the frame. -/
theorem set_join {h h' : Heap V} {k : Nat} (hk : h'.val k = none) (o : Option V) :
    (h.set k o).join h' = (h.join h').set k o := by
  apply ext; intro j
  by_cases hj : j = k
  · subst hj; simp [hk]
  · simp [hj]

/-- A cell allocated on the left of a disjoint pair is unallocated on the right. -/
theorem right_none_of_disj {h h' : Heap V} (hd : disj h h') {k : Nat}
    (hk : h.val k ≠ none) : h'.val k = none := by
  rcases hd k with e | e
  · exact absurd e hk
  · exact e

/-- A cell allocated on the left keeps its contents in the union. -/
theorem union_val_of_ne_none {h h' : Heap V} {k : Nat} (hk : h.val k ≠ none) :
    (union h h').val k = h.val k := by
  cases e : h.val k with
  | none => exact absurd e hk
  | some w => simp [e]

end Heap

/-! ## The heap model is a cancellative separation algebra -/

theorem heap_disjSymm (V : Type) : DisjSymm (Heap V) := by
  intro a b h k
  rcases h k with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem heap_unionComm (V : Type) : UnionComm (Heap V) := by
  intro a b h
  exact Heap.join_comm h

theorem heap_unionAssoc (V : Type) : UnionAssoc (Heap V) := by
  intro a b c hab habc
  simp only [Heap.disj_iff, Heap.union_eq, Heap.join_val] at hab habc ⊢
  refine ⟨fun k => ?_, fun k => ?_, Heap.ext fun k => ?_⟩
  · have h1 := hab k; have h2 := habc k
    cases ea : a.val k <;> cases eb : b.val k <;> cases ec : c.val k <;> simp_all
  · have h1 := hab k; have h2 := habc k
    cases ea : a.val k <;> cases eb : b.val k <;> cases ec : c.val k <;> simp_all
  · simp only [Heap.join_val]
    cases ea : a.val k <;> cases eb : b.val k <;> cases ec : c.val k <;> simp

theorem heap_unitLaw (V : Type) : UnitLaw (Heap.emp : Heap V) := by
  intro a
  exact ⟨fun k => Or.inl rfl, Heap.emp_join a⟩

theorem heap_isSepAlgebra (V : Type) : IsSepAlgebra (Heap V) Heap.emp :=
  ⟨heap_disjSymm V, heap_unionComm V, heap_unionAssoc V, heap_unitLaw V⟩

theorem heap_rightCancel (V : Type) : RightCancel (Heap V) := by
  intro a b c hac hbc he
  apply Heap.ext; intro k
  have hk := congrArg (fun h : Heap V => h.val k) he
  simp only [Heap.union_eq, Heap.join_val] at hk
  rcases hac k with h1 | h1 <;> rcases hbc k with h2 | h2
  · simp_all
  · cases ea : a.val k <;> simp_all
  · cases eb : b.val k <;> simp_all
  · cases ea : a.val k <;> cases eb : b.val k <;> simp_all

theorem heap_leftCancel (V : Type) : LeftCancel (Heap V) := by
  intro a b c hca hcb he
  apply Heap.ext; intro k
  have hk := congrArg (fun h : Heap V => h.val k) he
  simp only [Heap.union_eq, Heap.join_val] at hk
  rcases hca k with h1 | h1 <;> rcases hcb k with h2 | h2
  · simp_all
  · cases ea : a.val k <;> simp_all
  · cases eb : b.val k <;> simp_all
  · cases ec : c.val k <;> simp_all

theorem heap_unionAssocRev (V : Type) : UnionAssocRev (Heap V) :=
  unionAssocRev_of_disjSymm_of_unionComm_of_unionAssoc
    (heap_disjSymm V) (heap_unionComm V) (heap_unionAssoc V)

theorem heap_rightUnitLaw (V : Type) : RightUnitLaw (Heap.emp : Heap V) :=
  fun a => ⟨fun _ => Or.inr rfl, Heap.join_emp a⟩

/-! ## Subheaps -/

namespace Heap

variable {V : Type}

/-- `r` is a *subheap* of `h`: every cell allocated in `r` is allocated in `h`
with the same contents. -/
def Sub (r h : Heap V) : Prop := ∀ k, r.val k ≠ none → h.val k = r.val k

/-- In the heap model, "`r` is the right part of some disjoint decomposition of
`h`" is exactly "`r` is a subheap of `h`". -/
theorem exists_frame_iff_sub (r h : Heap V) :
    (∃ f, disj f r ∧ h = union f r) ↔ Sub r h := by
  constructor
  · rintro ⟨f, hd, rfl⟩ k hk
    have hf : f.val k = none := by
      rcases hd k with e | e
      · exact e
      · exact absurd e hk
    simp [hf]
  · intro hs
    refine ⟨⟨fun k => if r.val k = none then h.val k else none, ?_⟩, ?_, ?_⟩
    · obtain ⟨n, hn⟩ := h.finite
      exact ⟨n, fun k hk => by simp [hn k hk]⟩
    · intro k
      by_cases e : r.val k = none
      · exact Or.inr e
      · exact Or.inl (by simp [e])
    · apply ext; intro k
      by_cases e : r.val k = none
      · simp [e]
      · have := hs k e
        cases er : r.val k with
        | none => exact absurd er e
        | some w => simp [er, this]

end Heap

end Toy.Sep
