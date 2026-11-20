/-!
# A toy borrow-stack model for one memory location

This file defines a deliberately small borrow-tracking model in the style of
Stacked Borrows (Jung, Dang, Kang, Dreyer; POPL 2020). It is a *toy*: one memory
location holding a natural number, a stack of tagged permission items, protectors
as a per-item flag, and a counter for fresh tags. It is not Stacked Borrows.

Deviations from the rules of the Stacked Borrows paper (its Fig. 3 and Fig. 4):
* a read access *removes* the `unique` items above the granting item; the paper's
  rule `read-2` replaces them by `Disabled`;
* a write access removes *every* item above the granting item; the paper's rule
  `write-1` keeps the adjacent group of `SharedRW` items directly above a `SharedRW`
  granting item;
* a new `sharedRW` item is inserted directly above the granting item; the paper's
  `GrantTag` inserts it above the adjacent group of `SharedRW` items when the granting
  item is itself `SharedRW` (the two rules agree when the granting item is `unique`);
* protectors are a boolean flag that stays active for the whole run; the paper uses
  call IDs that become inactive when the call returns;
* raw pointers are represented only as tagged `sharedRW` items (the paper uses the
  untagged `⊥`; the later Miri implementation of Stacked Borrows tags raw pointers);
* there is a single location, no allocation or deallocation, no `Box`, no two-phase
  borrows, and no retag kinds other than an explicit reborrow.

Convention: the head of the list is the **top** of the stack.
-/

namespace Toy.Alias

/-- Pointer tags. Tags are natural numbers; fresh tags are drawn from `Mem.next`. -/
abbrev Tag := Nat

/-- Permission carried by a borrow-stack item. Toy versions of the Stacked Borrows
permissions: `unique` (a mutable reference, `&mut T`), `sharedRW` (shared
read-write: a shared reference to interior-mutable data, or a raw pointer), and
`sharedRO` (shared read-only: a shared reference `&T` without interior mutability). -/
inductive Perm where
  | unique
  | sharedRW
  | sharedRO
  deriving DecidableEq, Repr

/-- The two kinds of memory access. -/
inductive AccessKind where
  | read
  | write
  deriving DecidableEq, Repr

/-- `p.grants k`: an item with permission `p` may serve as the granting item for an
access of kind `k`. Every permission grants reads; only `unique` and `sharedRW`
grant writes. -/
def Perm.grants : Perm → AccessKind → Bool
  | _, .read => true
  | .unique, .write => true
  | .sharedRW, .write => true
  | .sharedRO, .write => false

/-- Positive example: a mutable reference grants writes. -/
theorem Perm.grants_unique_write : Perm.unique.grants .write = true := rfl

/-- Negative example: a read-only shared reference does not grant writes. -/
theorem Perm.not_grants_sharedRO_write : Perm.sharedRO.grants .write = false := rfl

/-- A borrow-stack item: a permission, the tag it is issued to, and whether it is
protected. Removing a protected item from the stack is undefined behavior. -/
structure Item where
  perm : Perm
  tag : Tag
  prot : Bool
  deriving DecidableEq, Repr

/-- Machine state for the single location: the stored value, the borrow stack (head =
top), and the next fresh tag. -/
structure Mem where
  val : Nat
  stack : List Item
  next : Tag
  deriving DecidableEq, Repr

/-- `findGranting k t s` locates the **topmost** item of `s` whose tag is `t` and whose
permission grants `k`. It returns `(above, granting, below)` with
`s = above ++ granting :: below`, or `none` if no item qualifies. -/
def findGranting (k : AccessKind) (t : Tag) : List Item → Option (List Item × Item × List Item)
  | [] => none
  | i :: rest =>
    if i.tag = t ∧ i.perm.grants k = true then some ([], i, rest)
    else
      match findGranting k t rest with
      | some (a, g, b) => some (i :: a, g, b)
      | none => none

/-- Positive example: a write through tag `0` is granted by the `unique` item below a
`sharedRO` item. -/
theorem findGranting_example_pos :
    findGranting .write 0 [⟨.sharedRO, 1, false⟩, ⟨.unique, 0, false⟩] =
      some ([⟨.sharedRO, 1, false⟩], ⟨.unique, 0, false⟩, []) := by decide

/-- Negative example: a write through a tag whose only item is `sharedRO` finds no
granting item. -/
theorem findGranting_example_neg :
    findGranting .write 1 [⟨.sharedRO, 1, false⟩, ⟨.unique, 0, false⟩] = none := by decide

/-- `invalidatedBy k i`: whether an item `i` lying *above* the granting item is removed
by an access of kind `k`. Reads remove the `unique` items above the granting item;
writes remove every item above it. -/
def invalidatedBy : AccessKind → Item → Bool
  | .read, i => decide (i.perm = .unique)
  | .write, _ => true

/-- Positive example: a read removes a `unique` item above the granting item. -/
theorem invalidatedBy_read_unique : invalidatedBy .read ⟨.unique, 1, false⟩ = true := rfl

/-- Negative example: a read does not remove a `sharedRW` item above the granting item. -/
theorem invalidatedBy_read_sharedRW : invalidatedBy .read ⟨.sharedRW, 1, false⟩ = false := rfl

/-- The effect of an access of kind `k` through tag `t` on a borrow stack. UB (`none`)
if there is no granting item, or if a protected item would be removed. Otherwise the
items above the granting item that the access invalidates are removed. -/
def accessStack (k : AccessKind) (t : Tag) (s : List Item) : Option (List Item) :=
  match findGranting k t s with
  | none => none
  | some (above, g, below) =>
    if above.any (fun i => invalidatedBy k i && i.prot) then none
    else some (above.filter (fun i => !invalidatedBy k i) ++ g :: below)

/-- Positive example: a read through a parent removes its `unique` child (Stacked
Borrows' "a parent read invalidates a mutable child"). -/
theorem accessStack_parent_read_pops_child :
    accessStack .read 0 [⟨.unique, 1, false⟩, ⟨.unique, 0, false⟩] =
      some [⟨.unique, 0, false⟩] := by decide

/-- Negative example: the same read is UB when the child item is protected. -/
theorem accessStack_parent_read_protected_child_ub :
    accessStack .read 0 [⟨.unique, 1, true⟩, ⟨.unique, 0, false⟩] = none := by decide

/-- Negative example: a write through a tag that is no longer in the stack is UB. -/
theorem accessStack_write_popped_ub :
    accessStack .write 1 [⟨.unique, 0, false⟩] = none := by decide

/-- A read through tag `t`: returns the stored value and the updated state, or `none`
(UB). -/
def read (t : Tag) (m : Mem) : Option (Nat × Mem) :=
  (accessStack .read t m.stack).map fun s => (m.val, { m with stack := s })

/-- A write of `v` through tag `t`: returns the updated state, or `none` (UB). -/
def write (t : Tag) (v : Nat) (m : Mem) : Option Mem :=
  (accessStack .write t m.stack).map fun s => { m with val := v, stack := s }

/-- Positive example: reading through the top item returns the value. -/
theorem read_example_pos :
    read 0 ⟨7, [⟨.unique, 0, false⟩], 1⟩ = some (7, ⟨7, [⟨.unique, 0, false⟩], 1⟩) := by decide

/-- Negative example: a write through a `sharedRO` tag is UB. -/
theorem write_example_neg :
    write 1 9 ⟨7, [⟨.sharedRO, 1, false⟩, ⟨.unique, 0, false⟩], 2⟩ = none := by decide

/-- Negative example: a read through a tag that has no item in the stack is UB. -/
theorem read_example_neg :
    read 1 ⟨7, [⟨.unique, 0, false⟩], 1⟩ = none := by decide

/-- Positive example: a write through a parent removes the child above it and stores the
value. -/
theorem write_example_pos :
    write 0 9 ⟨7, [⟨.sharedRO, 1, false⟩, ⟨.unique, 0, false⟩], 2⟩ =
      some ⟨9, [⟨.unique, 0, false⟩], 2⟩ := by decide

/-- `insertAboveGranting k t new s` inserts `new` directly above the topmost item that
grants `k` to `t`, without performing an access. This is the Stacked Borrows rule for new
`SharedRW` items when the granting item is `unique`; when the granting item is itself
`SharedRW`, Stacked Borrows' `GrantTag` instead inserts the new item above the adjacent
group of `SharedRW` items (one of the deviations listed at the top of this file). `none`
if there is no granting item. -/
def insertAboveGranting (k : AccessKind) (t : Tag) (new : Item) (s : List Item) :
    Option (List Item) :=
  (findGranting k t s).map fun (above, g, below) => above ++ new :: g :: below

/-- Positive example: a new `sharedRW` item is placed directly above its parent, below
an unrelated `sharedRO` item. -/
theorem insertAboveGranting_example_pos :
    insertAboveGranting .write 0 ⟨.sharedRW, 2, false⟩
        [⟨.sharedRO, 1, false⟩, ⟨.unique, 0, false⟩] =
      some [⟨.sharedRO, 1, false⟩, ⟨.sharedRW, 2, false⟩, ⟨.unique, 0, false⟩] := by decide

/-- Negative example: no insertion when the parent does not grant writes. -/
theorem insertAboveGranting_example_neg :
    insertAboveGranting .write 1 ⟨.sharedRW, 2, false⟩
        [⟨.sharedRO, 1, false⟩, ⟨.unique, 0, false⟩] = none := by decide

/-- Reborrow ("retag") from parent tag `parent`, creating the fresh tag `m.next` with
permission `p` and protector flag `prot`. This follows the Stacked Borrows reborrow rule up
to the deviations listed at the top of this file: a `sharedRW` item is inserted directly
above the parent's write-granting item with no access (Stacked Borrows agrees when that
granting item is `unique`; when it is `SharedRW`, Stacked Borrows inserts above the
adjacent group of `SharedRW` items); a `unique` item is pushed on top after a write access
through the parent; a `sharedRO` item is pushed on top after a read access through the
parent. Returns the new tag (always `m.next`) and the updated state, or `none` (UB). -/
def retag (parent : Tag) (p : Perm) (prot : Bool) (m : Mem) : Option (Tag × Mem) :=
  let new : Item := ⟨p, m.next, prot⟩
  let s? : Option (List Item) :=
    match p with
    | .sharedRW => insertAboveGranting .write parent new m.stack
    | .unique => (accessStack .write parent m.stack).map (new :: ·)
    | .sharedRO => (accessStack .read parent m.stack).map (new :: ·)
  s?.map fun s => (m.next, { m with stack := s, next := m.next + 1 })

/-- Positive example: a mutable reborrow of the root pushes a fresh `unique` item. -/
theorem retag_example_pos :
    retag 0 .unique true ⟨0, [⟨.unique, 0, false⟩], 1⟩ =
      some (1, ⟨0, [⟨.unique, 1, true⟩, ⟨.unique, 0, false⟩], 2⟩) := by decide

/-- Negative example: a mutable reborrow from a read-only shared reference is UB. -/
theorem retag_example_neg :
    retag 1 .unique false ⟨0, [⟨.sharedRO, 1, false⟩, ⟨.unique, 0, false⟩], 2⟩ = none := by
  decide

/-- The tag created by a successful retag is always `m.next`. -/
theorem retag_tag {parent : Tag} {p : Perm} {prot : Bool} {m : Mem} {x : Tag} {m' : Mem}
    (h : retag parent p prot m = some (x, m')) : x = m.next := by
  unfold retag at h
  cases p <;> simp only [Option.map] at h <;> split at h <;> simp_all

/-- `NextFresh m`: the next tag to be issued does not already occur in the stack, so the
reborrow about to be performed creates a tag that no existing item carries. This is a
well-formedness fact about the tag counter, not an aliasing condition: it follows from
`TagsBelowNext m`, which holds initially and is preserved by every operation
(`tagsBelowNext_initMem`, `tagsBelowNext_read`, `tagsBelowNext_write`,
`tagsBelowNext_retag`, and `tagsBelowNext_runCallee`). -/
def NextFresh (m : Mem) : Prop := ∀ i ∈ m.stack, i.tag ≠ m.next

instance (m : Mem) : Decidable (NextFresh m) := by
  unfold NextFresh; infer_instance

/-- `TagsBelowNext m`: every tag in the stack is strictly below the next fresh tag (the
usual invariant of a fresh-tag counter). It holds for `initMem` and is preserved by
`read`, `write`, `retag` (below) and by unknown code (`tagsBelowNext_runCallee`). -/
def TagsBelowNext (m : Mem) : Prop := ∀ i ∈ m.stack, i.tag < m.next

instance (m : Mem) : Decidable (TagsBelowNext m) := by
  unfold TagsBelowNext; infer_instance

/-- `TagsBelowNext` implies `NextFresh`. -/
theorem nextFresh_of_tagsBelowNext {m : Mem} (h : TagsBelowNext m) : NextFresh m :=
  fun i hi heq => Nat.lt_irrefl _ (heq ▸ h i hi)

/-- Negative example: `NextFresh` does not imply `TagsBelowNext` (a stack may contain a tag
above `next` without containing `next` itself). -/
theorem nextFresh_not_tagsBelowNext :
    NextFresh ⟨0, [⟨.unique, 5, false⟩], 1⟩ ∧ ¬ TagsBelowNext ⟨0, [⟨.unique, 5, false⟩], 1⟩ := by
  decide

/-- The canonical initial state: value `0`, a single unprotected `unique` root item with
tag `0`, next tag `1`. -/
def initMem : Mem := ⟨0, [⟨.unique, 0, false⟩], 1⟩

/-- Positive example: the initial state satisfies `TagsBelowNext`. -/
theorem tagsBelowNext_initMem : TagsBelowNext initMem := by decide

/-- Negative example: a stack containing the tag that the counter will issue next. -/
theorem not_tagsBelowNext_example :
    ¬ TagsBelowNext ⟨0, [⟨.unique, 0, false⟩, ⟨.unique, 1, false⟩], 1⟩ := by decide

/-- Positive example: the initial state satisfies `NextFresh`. -/
theorem nextFresh_initMem : NextFresh initMem := by decide

/-- Negative example: a state whose stack already contains the next tag. -/
theorem not_nextFresh_example : ¬ NextFresh ⟨0, [⟨.unique, 0, false⟩, ⟨.unique, 1, false⟩], 1⟩ := by
  decide

/-! ## Basic facts: the granting search and preservation of `TagsBelowNext` -/

/-- Skipping a non-granting item at the top of the stack. -/
theorem findGranting_cons_skip {k : AccessKind} {t : Tag} {i : Item} {rest : List Item}
    (h : ¬ (i.tag = t ∧ i.perm.grants k = true)) :
    findGranting k t (i :: rest) =
      (findGranting k t rest).map fun (a, g, b) => (i :: a, g, b) := by
  conv => lhs; unfold findGranting
  simp only [h, ite_false]
  cases findGranting k t rest with
  | none => rfl
  | some res => rcases res with ⟨_, _, _⟩; rfl

/-- Specification of `findGranting`: the split, the granting item, and that no item above
it grants the access. -/
theorem findGranting_spec {k : AccessKind} {t : Tag} {s ab bl : List Item} {g : Item}
    (h : findGranting k t s = some (ab, g, bl)) :
    s = ab ++ g :: bl ∧ g.tag = t ∧ g.perm.grants k = true ∧
      ∀ i ∈ ab, ¬ (i.tag = t ∧ i.perm.grants k = true) := by
  induction s generalizing ab with
  | nil => simp [findGranting] at h
  | cons i rest ih =>
    unfold findGranting at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, hc.1, hc.2, fun _ hm => by cases hm⟩
    · rename_i hc
      cases hfg : findGranting k t rest with
      | none => simp [hfg] at h
      | some res =>
        rcases res with ⟨a', g', b'⟩
        simp only [hfg, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        obtain ⟨hs, hgt, hgg, hall⟩ := ih hfg
        refine ⟨by simp [hs], hgt, hgg, ?_⟩
        intro j hj
        cases hj with
        | head => exact hc
        | tail _ hm => exact hall j hm

/-- An access only removes items: every item of the new stack was in the old one. -/
theorem accessStack_sublist_prop {k : AccessKind} {t : Tag} {s s' : List Item}
    {P : Item → Prop} (h : ∀ i ∈ s, P i) (ha : accessStack k t s = some s') :
    ∀ i ∈ s', P i := by
  unfold accessStack at ha
  cases hfg : findGranting k t s with
  | none => simp [hfg] at ha
  | some res =>
    rcases res with ⟨ab, g, bl⟩
    obtain ⟨hs, _, _, _⟩ := findGranting_spec hfg
    simp only [hfg] at ha
    split at ha
    · cases ha
    · simp only [Option.some.injEq] at ha
      subst ha
      intro i hi
      apply h i
      rw [hs]
      simp only [List.mem_append, List.mem_filter, List.mem_cons] at hi ⊢
      rcases hi with ⟨hab, _⟩ | rfl | hbl
      · exact Or.inl hab
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr hbl)

/-- Reads preserve `TagsBelowNext`. -/
theorem tagsBelowNext_read {t : Tag} {m m' : Mem} {v : Nat}
    (h : TagsBelowNext m) (hr : read t m = some (v, m')) : TagsBelowNext m' := by
  unfold read at hr
  cases ha : accessStack .read t m.stack with
  | none => simp [ha] at hr
  | some s' =>
    simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨_, rfl⟩ := hr
    exact accessStack_sublist_prop h ha

/-- Writes preserve `TagsBelowNext`. -/
theorem tagsBelowNext_write {t : Tag} {v : Nat} {m m' : Mem}
    (h : TagsBelowNext m) (hw : write t v m = some m') : TagsBelowNext m' := by
  unfold write at hw
  cases ha : accessStack .write t m.stack with
  | none => simp [ha] at hw
  | some s' =>
    simp only [ha, Option.map_some, Option.some.injEq] at hw
    subst hw
    exact accessStack_sublist_prop h ha

/-- Reborrows preserve `TagsBelowNext`. -/
theorem tagsBelowNext_retag {parent : Tag} {p : Perm} {prot : Bool} {m m' : Mem} {x : Tag}
    (h : TagsBelowNext m) (hr : retag parent p prot m = some (x, m')) : TagsBelowNext m' := by
  unfold retag at hr
  cases p with
  | sharedRW =>
    simp only at hr
    unfold insertAboveGranting at hr
    cases hfg : findGranting .write parent m.stack with
    | none => simp [hfg] at hr
    | some res =>
      rcases res with ⟨ab, g, bl⟩
      obtain ⟨hs, _, _, _⟩ := findGranting_spec hfg
      simp only [hfg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨_, rfl⟩ := hr
      intro i hi
      simp only [List.mem_append, List.mem_cons] at hi
      rcases hi with hab | rfl | rfl | hbl
      · exact Nat.lt_succ_of_lt (h i (by rw [hs]; exact List.mem_append_left _ hab))
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt
          (h i (by rw [hs]; exact List.mem_append_right _ (List.mem_cons_self ..)))
      · exact Nat.lt_succ_of_lt
          (h i (by rw [hs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hbl)))
  | unique =>
    simp only at hr
    cases ha : accessStack .write parent m.stack with
    | none => simp [ha] at hr
    | some s' =>
      simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨_, rfl⟩ := hr
      intro i hi
      cases hi with
      | head => exact Nat.lt_succ_self _
      | tail _ hm => exact Nat.lt_succ_of_lt (accessStack_sublist_prop h ha i hm)
  | sharedRO =>
    simp only at hr
    cases ha : accessStack .read parent m.stack with
    | none => simp [ha] at hr
    | some s' =>
      simp only [ha, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨_, rfl⟩ := hr
      intro i hi
      cases hi with
      | head => exact Nat.lt_succ_self _
      | tail _ hm => exact Nat.lt_succ_of_lt (accessStack_sublist_prop h ha i hm)

end Toy.Alias
