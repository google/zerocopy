/-
  NonDivergingIntrinsicsAndUnreachableProp.lean

  Standalone Lean v4.34.1 mechanization (no imports beyond the prelude) of

  * the operational meaning of the two MIR non-diverging intrinsic statements,
    `StatementKind::Intrinsic(NonDivergingIntrinsic::Assume(op))` and
    `StatementKind::Intrinsic(NonDivergingIntrinsic::CopyNonOverlapping { src, dst, count })`,
    as implemented by the rustc interpreter (`eval_nondiverging_intrinsic`,
    `copy_intrinsic`, `mem_copy_repeatedly`);
  * the switch-pruning step of `UnreachablePropagation`
    (`remove_successors_from_switch`), which replaces `SwitchInt` arms that lead
    to unreachable blocks by `assume` statements; and
  * the arm-redirection step of `UnreachableEnumBranching`.

  Main results
  ------------
  * `pruneSwitch_exact` / `pruneSwitch_ub_iff`: for a `SwitchInt` with at least
    one valued arm and pairwise distinct arm values, the pruned block has
    undefined behaviour exactly when the original terminator does (jumping into
    a block flagged unreachable counts as undefined behaviour), and otherwise
    both continue at the same block in states that agree on every local below
    the first fresh temporary.
  * `doomed_reaches_ub`: every block in the inductive closure used by the pass
    (ends in `unreachable`, in a `goto` to such a block, or in a `SwitchInt`
    whose every successor is such a block) reaches undefined behaviour from every
    state, which justifies the collapse used in `pruneSwitch_exact`.
  * `assume_as_switch_gadget`: a well-typed `assume(op)` is equivalent to
    `switchInt(op) -> [0: unreachable block, otherwise: next]`.
  * `enumBranching_sound`: redirecting arms of uninhabited variants preserves the
    successor for every discriminant of an inhabited variant.
  * `execCopy_isSome_iff` and corollaries: alignment of both pointers is required
    even for a zero-length copy; a zero-length copy needs nothing else (null and
    dangling pointers are accepted); a non-empty copy additionally needs both
    ranges mapped and disjoint, and then copies slot by slot.
  * Sharpness counterexamples `ce1` .. `ce5`.

  Every proof is by structural recursion, case analysis and rewriting.
-/

namespace NonDivergingIntrinsics

/-! ## Section 1: values, states, operands -/

abbrev Local := Nat
abbrev Block := Nat

/-- Runtime values. Pointers carry only an address (no provenance). -/
inductive Val where
  | int (n : Nat)
  | bool (b : Bool)
  | ptr (addr : Nat)

/-- The bit pattern a `SwitchInt` or an integer comparison observes. -/
noncomputable def Val.bits : Val → Option Nat
  | .int n => some n
  | .bool true => some 1
  | .bool false => some 0
  | .ptr _ => none

/-- `locals l = none` models an uninitialized local; `mem a = none` models an
address that is not inside any live allocation. -/
structure State where
  locals : Local → Option Val
  mem : Nat → Option Nat

noncomputable def State.setLocal (σ : State) (l : Local) (v : Val) : State :=
  { σ with locals := fun x => if x = l then some v else σ.locals x }

inductive Operand where
  | copy (l : Local)
  | move (l : Local)
  | const (v : Val)

/-- `Operand::to_copy`: a `Move` becomes a `Copy`, everything else is unchanged. -/
noncomputable def Operand.toCopy : Operand → Operand
  | .move l => .copy l
  | .copy l => .copy l
  | .const v => .const v

/-- The operand reads no local at or above `tmp`. -/
noncomputable def Operand.readsBelow (tmp : Local) : Operand → Prop
  | .copy l => l < tmp
  | .move l => l < tmp
  | .const _ => True

/-- Operand evaluation. As in the rustc interpreter, a `Move` operand reads the
local without de-initializing it. -/
noncomputable def evalOperand (σ : State) : Operand → Option Val
  | .copy l => σ.locals l
  | .move l => σ.locals l
  | .const v => some v

noncomputable def discrBits (σ : State) (op : Operand) : Option Nat :=
  match evalOperand σ op with
  | some v => v.bits
  | none => none

inductive CmpOp where
  | eq
  | ne

noncomputable def cmpBits : CmpOp → Nat → Nat → Bool
  | .eq, m, n => decide (m = n)
  | .ne, m, n => !decide (m = n)

inductive Rvalue where
  | use (op : Operand)
  | cmp (c : CmpOp) (lhs rhs : Operand)

noncomputable def evalRvalue (σ : State) : Rvalue → Option Val
  | .use op => evalOperand σ op
  | .cmp c a b =>
    match discrBits σ a, discrBits σ b with
    | some m, some n => some (.bool (cmpBits c m n))
    | _, _ => none

/-! ## Section 2: `copy_nonoverlapping` on a flat slot memory -/

/-- Pointee layout: element size, required alignment, and the largest total
size the interpreter accepts (`compute_size_in_bytes`). -/
structure Layout where
  elemSize : Nat
  align : Nat
  sizeBound : Nat

/-- All `n` slots starting at `a` lie inside live allocations. -/
noncomputable def rangeMapped (m : Nat → Option Nat) (a : Nat) : Nat → Bool
  | 0 => true
  | n + 1 => (m a).isSome && rangeMapped m (a + 1) n

noncomputable def disjointRanges (src dst size : Nat) : Bool :=
  decide (src + size ≤ dst) || decide (dst + size ≤ src)

/-- Memory after copying `size` slots from `src` to `dst`. -/
noncomputable def copySlots (m : Nat → Option Nat) (src dst size : Nat) : Nat → Option Nat :=
  fun a => if dst ≤ a ∧ a < dst + size then m (src + (a - dst)) else m a

/-- `copy_intrinsic` followed by `mem_copy`, in interpreter order: total size,
alignment of `src`, alignment of `dst`, then (only for a non-empty copy) both
ranges dereferenceable and the two ranges disjoint. `none` is undefined
behaviour. -/
noncomputable def execCopy (lay : Layout) (σ : State) (src dst count : Nat) : Option State :=
  if lay.sizeBound < count * lay.elemSize then none
  else if src % lay.align ≠ 0 then none
  else if dst % lay.align ≠ 0 then none
  else if count * lay.elemSize = 0 then some σ
  else if rangeMapped σ.mem src (count * lay.elemSize) = false then none
  else if rangeMapped σ.mem dst (count * lay.elemSize) = false then none
  else if disjointRanges src dst (count * lay.elemSize) = false then none
  else some { σ with mem := copySlots σ.mem src dst (count * lay.elemSize) }

/-- Exact characterization of when the copy is defined. -/
theorem execCopy_isSome_iff (lay : Layout) (σ : State) (src dst count : Nat) :
    (execCopy lay σ src dst count).isSome = true ↔
      (¬ lay.sizeBound < count * lay.elemSize ∧ src % lay.align = 0 ∧
        dst % lay.align = 0 ∧
        (count * lay.elemSize = 0 ∨
          (rangeMapped σ.mem src (count * lay.elemSize) = true ∧
            rangeMapped σ.mem dst (count * lay.elemSize) = true ∧
            disjointRanges src dst (count * lay.elemSize) = true))) := by
  unfold execCopy
  by_cases h1 : lay.sizeBound < count * lay.elemSize
  · simp [h1]
  · by_cases h2 : src % lay.align = 0
    · by_cases h3 : dst % lay.align = 0
      · by_cases h4 : count * lay.elemSize = 0
        · simp [h2, h3, h4]
        · cases h5 : rangeMapped σ.mem src (count * lay.elemSize) <;>
            cases h6 : rangeMapped σ.mem dst (count * lay.elemSize) <;>
            cases h7 : disjointRanges src dst (count * lay.elemSize) <;>
            simp [h1, h2, h3, h4]
      · simp [h1, h2, h3]
    · simp [h1, h2]

/-- A zero-length copy between aligned pointers is defined and changes nothing,
whatever the pointers point to (dangling, one-past-the-end, or null). -/
theorem copy_zero_count_aligned_ok (lay : Layout) (σ : State) (src dst : Nat)
    (hs : src % lay.align = 0) (hd : dst % lay.align = 0) :
    execCopy lay σ src dst 0 = some σ := by
  simp [execCopy, hs, hd]

/-- The null address is aligned for every alignment, so a zero-length copy from
and to null is defined. -/
theorem copy_zero_count_null_ok (lay : Layout) (σ : State) :
    execCopy lay σ 0 0 0 = some σ :=
  copy_zero_count_aligned_ok lay σ 0 0 (Nat.zero_mod _) (Nat.zero_mod _)

/-- A misaligned source is undefined behaviour even when nothing is copied. -/
theorem copy_zero_count_misaligned_src_ub (lay : Layout) (σ : State) (src dst : Nat)
    (hs : src % lay.align ≠ 0) : execCopy lay σ src dst 0 = none := by
  simp [execCopy, hs]

/-- A misaligned destination is undefined behaviour even when nothing is copied. -/
theorem copy_zero_count_misaligned_dst_ub (lay : Layout) (σ : State) (src dst : Nat)
    (hd : dst % lay.align ≠ 0) : execCopy lay σ src dst 0 = none := by
  by_cases hs : src % lay.align = 0 <;> simp [execCopy, hs, hd]

/-- Zero-length copies are defined exactly when both pointers are aligned. -/
theorem copy_zero_count_ok_iff_aligned (lay : Layout) (σ : State) (src dst : Nat) :
    (execCopy lay σ src dst 0).isSome = true ↔
      (src % lay.align = 0 ∧ dst % lay.align = 0) := by
  rw [execCopy_isSome_iff]
  simp

/-- A non-empty range whose first slot is unmapped is not dereferenceable. -/
theorem rangeMapped_first_unmapped (m : Nat → Option Nat) (a n : Nat)
    (h : m a = none) : rangeMapped m a (n + 1) = false := by
  simp [rangeMapped, h]

/-- A non-empty copy from a pointer whose first slot is unmapped (in particular
from null, when address `0` is unmapped) is undefined behaviour. -/
theorem copy_nonempty_unmapped_src_ub (lay : Layout) (σ : State) (src dst count : Nat)
    (hpos : count * lay.elemSize ≠ 0) (h : σ.mem src = none) :
    execCopy lay σ src dst count = none := by
  cases hsz : count * lay.elemSize with
  | zero => exact absurd hsz hpos
  | succ k =>
    have hr : rangeMapped σ.mem src (k + 1) = false := rangeMapped_first_unmapped _ _ _ h
    unfold execCopy
    rw [hsz]
    by_cases h1 : lay.sizeBound < k + 1
    · simp [h1]
    · by_cases h2 : src % lay.align = 0
      · by_cases h3 : dst % lay.align = 0
        · simp [h1, h2, h3, hr]
        · simp [h1, h2, h3]
      · simp [h1, h2]

/-- Overlapping ranges are undefined behaviour for a non-empty copy. -/
theorem copy_overlap_ub (lay : Layout) (σ : State) (src dst count : Nat)
    (hpos : count * lay.elemSize ≠ 0)
    (hov : disjointRanges src dst (count * lay.elemSize) = false) :
    execCopy lay σ src dst count = none := by
  have h := execCopy_isSome_iff lay σ src dst count
  cases hx : execCopy lay σ src dst count with
  | none => rfl
  | some σ' =>
    rw [hx] at h
    have h' := h.mp rfl
    cases h'.2.2.2 with
    | inl h0 => exact absurd h0 hpos
    | inr h3 => rw [hov] at h3; exact absurd h3.2.2 (by decide)

/-- A defined non-empty copy writes slot `src + i` to slot `dst + i`, leaves every
slot outside the destination range and every local unchanged. -/
theorem copy_ok_slotwise (lay : Layout) (σ σ' : State) (src dst count : Nat)
    (hpos : count * lay.elemSize ≠ 0)
    (h : execCopy lay σ src dst count = some σ') :
    (∀ i, i < count * lay.elemSize → σ'.mem (dst + i) = σ.mem (src + i)) ∧
    (∀ a, ¬ (dst ≤ a ∧ a < dst + count * lay.elemSize) → σ'.mem a = σ.mem a) ∧
    σ'.locals = σ.locals := by
  unfold execCopy at h
  by_cases h1 : lay.sizeBound < count * lay.elemSize
  · simp [h1] at h
  · by_cases h2 : src % lay.align = 0
    · by_cases h3 : dst % lay.align = 0
      · cases h5 : rangeMapped σ.mem src (count * lay.elemSize) <;>
          cases h6 : rangeMapped σ.mem dst (count * lay.elemSize) <;>
          cases h7 : disjointRanges src dst (count * lay.elemSize) <;>
          simp [h1, h2, h3, hpos, h5, h6, h7] at h
        subst h
        refine ⟨?_, ?_, rfl⟩
        · intro i hi
          show copySlots σ.mem src dst (count * lay.elemSize) (dst + i) = σ.mem (src + i)
          unfold copySlots
          rw [ite_eq_left ⟨Nat.le_add_right dst i, Nat.add_lt_add_left hi dst⟩,
            Nat.add_sub_cancel_left]
        · intro a ha
          show copySlots σ.mem src dst (count * lay.elemSize) a = σ.mem a
          unfold copySlots
          rw [ite_eq_right ha]
      · simp [h1, h2, h3] at h
    · simp [h1, h2] at h

/-! ## Section 3: statements, terminators and block execution -/

inductive Statement where
  | assign (dst : Local) (rv : Rvalue)
  | assume (op : Operand)
  | copyNonOverlapping (src dst count : Operand) (lay : Layout)
  | nop

inductive Terminator where
  | goto (target : Block)
  | switchInt (discr : Operand) (targets : List (Nat × Block)) (otherwise : Block)
  | unreachable
  | ret

/-- Result of running one basic block. `ub` is undefined behaviour. -/
inductive Outcome where
  | ub
  | jump (b : Block) (σ : State)
  | done (σ : State)

noncomputable def Outcome.isUb : Outcome → Bool
  | .ub => true
  | .jump _ _ => false
  | .done _ => false

/-- `NonDivergingIntrinsic::Assume`: the operand must evaluate to `true`;
`false` (and anything that is not a boolean) is undefined behaviour. -/
noncomputable def execAssume (σ : State) (op : Operand) : Option State :=
  match evalOperand σ op with
  | some (.bool true) => some σ
  | _ => none

noncomputable def execStmt (σ : State) : Statement → Option State
  | .assign dst rv =>
    match evalRvalue σ rv with
    | some v => some (σ.setLocal dst v)
    | none => none
  | .assume op => execAssume σ op
  | .copyNonOverlapping src dst count lay =>
    match evalOperand σ src, evalOperand σ dst, evalOperand σ count with
    | some (.ptr s), some (.ptr d), some (.int n) => execCopy lay σ s d n
    | _, _, _ => none
  | .nop => some σ

noncomputable def execStmts (σ : State) : List Statement → Option State
  | [] => some σ
  | s :: rest =>
    match execStmt σ s with
    | some σ' => execStmts σ' rest
    | none => none

/-- `SwitchTargets::target_for_value`: first arm whose value matches, else
`otherwise`. -/
noncomputable def lookup (targets : List (Nat × Block)) (otherwise : Block) (d : Nat) : Block :=
  match targets with
  | [] => otherwise
  | (v, b) :: rest => if d = v then b else lookup rest otherwise d

noncomputable def execTerm (σ : State) : Terminator → Outcome
  | .goto b => .jump b σ
  | .switchInt discr targets otherwise =>
    match discrBits σ discr with
    | some d => .jump (lookup targets otherwise d) σ
    | none => .ub
  | .unreachable => .ub
  | .ret => .done σ

noncomputable def execBlock (σ : State) (stmts : List Statement) (term : Terminator) : Outcome :=
  match execStmts σ stmts with
  | some σ' => execTerm σ' term
  | none => .ub

theorem execStmts_append (σ : State) (a b : List Statement) :
    execStmts σ (a ++ b) =
      match execStmts σ a with
      | some σ' => execStmts σ' b
      | none => none := by
  induction a generalizing σ with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.cons_append, execStmts]
    cases execStmt σ s with
    | none => rfl
    | some σ₁ => exact ih σ₁

/-- A block that ends in `unreachable` is undefined behaviour whatever its
statements do, so the pass may empty such blocks. -/
theorem unreachable_block_ub (σ : State) (stmts : List Statement) :
    execBlock σ stmts .unreachable = .ub := by
  unfold execBlock
  cases execStmts σ stmts <;> rfl

theorem unreachable_block_statements_irrelevant (σ : State) (stmts : List Statement) :
    execBlock σ stmts .unreachable = execBlock σ [] .unreachable := by
  rw [unreachable_block_ub, unreachable_block_ub]

/-! ## Section 4: lookup lemmas -/

theorem lookup_eq_otherwise_or_mem (ts : List (Nat × Block)) (o : Block) (d : Nat) :
    lookup ts o d = o ∨ (d, lookup ts o d) ∈ ts := by
  induction ts with
  | nil => exact Or.inl rfl
  | cons p rest ih =>
    obtain ⟨v, b⟩ := p
    by_cases h : d = v
    · refine Or.inr ?_
      simp [lookup, h]
    · cases ih with
      | inl h' =>
        refine Or.inl ?_
        simp [lookup, h, h']
      | inr h' =>
        refine Or.inr ?_
        simp only [lookup, h, ite_false]
        exact List.mem_cons_of_mem _ h'

theorem lookup_of_not_mem (ts : List (Nat × Block)) (o : Block) (d : Nat)
    (h : d ∉ ts.map Prod.fst) : lookup ts o d = o := by
  induction ts with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, b⟩ := p
    have hv : d ≠ v := fun e => h (by simp [e])
    have hr : d ∉ rest.map Prod.fst := fun m => h (by simp [m])
    simp [lookup, hv, ih hr]

theorem lookup_filter_of_not_mem (q : Nat × Block → Bool) (ts : List (Nat × Block))
    (o : Block) (d : Nat) (h : d ∉ ts.map Prod.fst) : lookup (ts.filter q) o d = o := by
  induction ts with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, b⟩ := p
    have hv : d ≠ v := fun e => h (by simp [e])
    have hr : d ∉ rest.map Prod.fst := fun m => h (by simp [m])
    rw [List.filter_cons]
    by_cases hq : q (v, b) = true
    · simp [hq, lookup, hv, ih hr]
    · simp [hq, ih hr]

theorem lookup_of_mem_nodup (ts : List (Nat × Block)) (o : Block) (d : Nat) (b : Block)
    (hn : (ts.map Prod.fst).Nodup) (hm : (d, b) ∈ ts) : lookup ts o d = b := by
  induction ts with
  | nil => exact absurd hm List.not_mem_nil
  | cons p rest ih =>
    obtain ⟨v, t⟩ := p
    have hn' : v ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
      simpa [List.nodup_cons] using hn
    cases List.mem_cons.mp hm with
    | inl e =>
      have hv : d = v := congrArg Prod.fst e
      have ht : b = t := congrArg Prod.snd e
      simp [lookup, hv, ht]
    | inr hmem =>
      have hd : d ∈ rest.map Prod.fst := List.mem_map.mpr ⟨(d, b), hmem, rfl⟩
      have hv : d ≠ v := fun e => hn'.1 (e ▸ hd)
      simp [lookup, hv, ih hn'.2 hmem]

/-- Dropping arms that lead to flagged blocks does not change where a value goes
when its original successor is not flagged. -/
theorem lookup_filter_reachable (U : Block → Bool) (ts : List (Nat × Block)) (o : Block)
    (d : Nat) (h : U (lookup ts o d) = false) :
    lookup (ts.filter (fun p => !U p.2)) o d = lookup ts o d := by
  induction ts with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, b⟩ := p
    rw [List.filter_cons]
    by_cases hv : d = v
    · have hb : U b = false := by simpa [lookup, hv] using h
      simp [lookup, hv, hb]
    · have h' : U (lookup rest o d) = false := by simpa [lookup, hv] using h
      by_cases hb : U b = true
      · simp [lookup, hv, hb, ih h']
      · simp [lookup, hv, hb, ih h']

/-- With pairwise distinct arm values, a value whose original successor is
flagged falls through to `otherwise` once flagged arms are dropped. -/
theorem lookup_filter_unreachable (U : Block → Bool) (ts : List (Nat × Block)) (o : Block)
    (d : Nat) (hn : (ts.map Prod.fst).Nodup) (h : U (lookup ts o d) = true) :
    lookup (ts.filter (fun p => !U p.2)) o d = o := by
  induction ts with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, b⟩ := p
    have hn' : v ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by
      simpa [List.nodup_cons] using hn
    rw [List.filter_cons]
    by_cases hv : d = v
    · have hb : U b = true := by simpa [lookup, hv] using h
      have hnot : d ∉ rest.map Prod.fst := hv ▸ hn'.1
      simp [hb, lookup_filter_of_not_mem _ rest o d hnot]
    · have h' : U (lookup rest o d) = true := by simpa [lookup, hv] using h
      have hl := ih hn'.2 h'
      by_cases hb : U b = true
      · simp [hb, hl]
      · simp [hb, lookup, hv, hl]

/-- If no arm survives the filter, every arm leads to a flagged block. -/
theorem filter_reach_nil (U : Block → Bool) (ts : List (Nat × Block))
    (h : ts.filter (fun p => !U p.2) = []) : ∀ p, p ∈ ts → U p.2 = true := by
  induction ts with
  | nil =>
    intro p hp
    exact absurd hp List.not_mem_nil
  | cons q rest ih =>
    intro p hp
    rw [List.filter_cons] at h
    cases hq : U q.2 with
    | true =>
      rw [hq] at h
      have h' : rest.filter (fun p => !U p.2) = [] := h
      cases List.mem_cons.mp hp with
      | inl e =>
        rw [e]
        exact hq
      | inr hm => exact ih h' p hm
    | false =>
      rw [hq] at h
      have h' : q :: rest.filter (fun p => !U p.2) = [] := h
      cases h'

/-! ## Section 5: blocks that always reach undefined behaviour -/

structure BlockData where
  stmts : List Statement
  term : Terminator

abbrev Body := Block → BlockData

/-- Big-step execution of a control-flow graph to a final outcome. -/
inductive Reaches (body : Body) : Block → State → Outcome → Prop where
  | ub {b : Block} {σ : State} :
      execBlock σ (body b).stmts (body b).term = .ub → Reaches body b σ .ub
  | done {b : Block} {σ σ' : State} :
      execBlock σ (body b).stmts (body b).term = .done σ' → Reaches body b σ (.done σ')
  | step {b b' : Block} {σ σ' : State} {o : Outcome} :
      execBlock σ (body b).stmts (body b).term = .jump b' σ' →
      Reaches body b' σ' o → Reaches body b σ o

/-- The closure `UnreachablePropagation` computes in post-order: a block is
flagged when it ends in `unreachable`, in a `goto` to a flagged block, or in a
`SwitchInt` all of whose successors are flagged. -/
inductive Doomed (body : Body) : Block → Prop where
  | unreachable {b : Block} : (body b).term = .unreachable → Doomed body b
  | goto {b t : Block} : (body b).term = .goto t → Doomed body t → Doomed body b
  | switch {b : Block} {discr : Operand} {ts : List (Nat × Block)} {o : Block} :
      (body b).term = .switchInt discr ts o →
      (∀ p, p ∈ ts → Doomed body p.2) → Doomed body o → Doomed body b

/-- Every flagged block reaches undefined behaviour from every state. -/
theorem doomed_reaches_ub {body : Body} {b : Block} (h : Doomed body b) :
    ∀ σ, Reaches body b σ .ub := by
  induction h with
  | unreachable hterm =>
    intro σ
    refine Reaches.ub ?_
    rw [hterm]
    exact unreachable_block_ub σ _
  | @goto b t hterm _ ih =>
    intro σ
    cases hs : execStmts σ (body b).stmts with
    | none =>
      refine Reaches.ub ?_
      unfold execBlock
      rw [hs]
    | some σ' =>
      refine Reaches.step (b' := t) (σ' := σ') ?_ (ih σ')
      unfold execBlock
      rw [hs, hterm]
      rfl
  | @switch b discr ts o hterm _ _ ihts iho =>
    intro σ
    cases hs : execStmts σ (body b).stmts with
    | none =>
      refine Reaches.ub ?_
      unfold execBlock
      rw [hs]
    | some σ' =>
      cases hd : discrBits σ' discr with
      | none =>
        refine Reaches.ub ?_
        unfold execBlock
        rw [hs, hterm]
        simp [execTerm, hd]
      | some d =>
        have hstep : execBlock σ (body b).stmts (body b).term =
            .jump (lookup ts o d) σ' := by
          unfold execBlock
          rw [hs, hterm]
          simp [execTerm, hd]
        cases lookup_eq_otherwise_or_mem ts o d with
        | inl ho =>
          rw [ho] at hstep
          exact Reaches.step hstep (iho σ')
        | inr hm => exact Reaches.step hstep (ihts _ hm σ')

/-- Execution is deterministic. -/
theorem reaches_functional {body : Body} {b : Block} {σ : State} {o₁ o₂ : Outcome}
    (h₁ : Reaches body b σ o₁) (h₂ : Reaches body b σ o₂) : o₁ = o₂ := by
  induction h₁ generalizing o₂ with
  | ub e₁ =>
    cases h₂ with
    | ub _ => rfl
    | done e₂ => rw [e₁] at e₂; cases e₂
    | step e₂ _ => rw [e₁] at e₂; cases e₂
  | done e₁ =>
    cases h₂ with
    | ub e₂ => rw [e₁] at e₂; cases e₂
    | done e₂ => rw [e₁] at e₂; cases e₂; rfl
    | step e₂ _ => rw [e₁] at e₂; cases e₂
  | step e₁ _ ih =>
    cases h₂ with
    | ub e₂ => rw [e₁] at e₂; cases e₂
    | done e₂ => rw [e₁] at e₂; cases e₂
    | step e₂ r₂ => rw [e₁] at e₂; cases e₂; exact ih r₂

/-- A flagged block never returns normally. -/
theorem doomed_never_done {body : Body} {b : Block} (h : Doomed body b) (σ σ' : State) :
    ¬ Reaches body b σ (.done σ') := by
  intro hdone
  have := reaches_functional (doomed_reaches_ub h σ) hdone
  cases this

/-! ## Section 6: `UnreachablePropagation` switch pruning -/

/-- The two statements `add_assumption` appends:
`tmp = <Eq|Ne>(copy discr, const v); assume(move tmp)`. The constant stands for
`Const::from_scalar(.., Scalar::from_uint(v, discr_size), discr_ty)`: a constant
of the discriminant's own type whose bit pattern is `v`. -/
noncomputable def assumeCmp (c : CmpOp) (discr : Operand) (v : Nat) (tmp : Local) : List Statement :=
  [.assign tmp (.cmp c discr.toCopy (.const (.int v))), .assume (.move tmp)]

/-- One `Ne` assumption per removed arm, each with its own fresh temporary. -/
noncomputable def neAssumes (discr : Operand) : List (Nat × Block) → Local → List Statement
  | [], _ => []
  | (v, _) :: rest, tmp => assumeCmp .ne discr v tmp ++ neAssumes discr rest (tmp + 1)

/-- Case split of `remove_successors_from_switch` on `(num_targets,
otherwise_unreachable)`, where `num_targets = reach.length + 1`. -/
noncomputable def pruneCore (discr : Operand) (otherwise : Block) (tmp : Local) :
    Bool → List (Nat × Block) → List (Nat × Block) → List Statement × Terminator
  | true, [], _ => ([], .unreachable)
  | true, [(v, t)], _ => (assumeCmp .eq discr v tmp, .goto t)
  | true, a :: b :: rest, _ => ([], .switchInt discr (a :: b :: rest) otherwise)
  | false, [], removed => (neAssumes discr removed tmp, .goto otherwise)
  | false, a :: rest, removed =>
    (neAssumes discr removed tmp, .switchInt discr (a :: rest) otherwise)

/-- `remove_successors_from_switch`: `U` is `is_unreachable_block`. The result is
the list of statements appended to the block and its new terminator. When no
arm is removed the result is the original terminator with no new statement,
which is the pass's "nothing has changed" exit. -/
noncomputable def pruneSwitch (U : Block → Bool) (discr : Operand) (targets : List (Nat × Block))
    (otherwise : Block) (tmp : Local) : List Statement × Terminator :=
  pruneCore discr otherwise tmp (U otherwise)
    (targets.filter (fun p => !U p.2)) (targets.filter (fun p => U p.2))

/-- Entering a flagged block is undefined behaviour (see `doomed_reaches_ub`). -/
noncomputable def collapse (U : Block → Bool) : Outcome → Outcome
  | .jump b σ => if U b = true then .ub else .jump b σ
  | .ub => .ub
  | .done σ => .done σ

/-- The two states agree on memory and on every local below `tmp`. -/
noncomputable def AgreeBelow (tmp : Local) (σ σ' : State) : Prop :=
  (∀ l, l < tmp → σ'.locals l = σ.locals l) ∧ σ'.mem = σ.mem

noncomputable def OutcomeEquiv (tmp : Local) : Outcome → Outcome → Prop
  | .ub, .ub => True
  | .jump b σ, .jump b' σ' => b = b' ∧ AgreeBelow tmp σ σ'
  | .done σ, .done σ' => AgreeBelow tmp σ σ'
  | _, _ => False

theorem agreeBelow_refl (tmp : Local) (σ : State) : AgreeBelow tmp σ σ :=
  ⟨fun _ _ => rfl, rfl⟩

theorem agreeBelow_setLocal (tmp : Local) (σ : State) (x : Val) :
    AgreeBelow tmp σ (σ.setLocal tmp x) := by
  refine ⟨?_, rfl⟩
  intro l hl
  have hne : l ≠ tmp := Nat.ne_of_lt hl
  simp [State.setLocal, hne]

theorem agreeBelow_step (tmp : Local) (σ σ' : State) (x : Val)
    (h : AgreeBelow (tmp + 1) (σ.setLocal tmp x) σ') : AgreeBelow tmp σ σ' := by
  refine ⟨?_, ?_⟩
  · intro l hl
    have hne : l ≠ tmp := Nat.ne_of_lt hl
    rw [h.1 l (Nat.lt_succ_of_lt hl)]
    simp [State.setLocal, hne]
  · rw [h.2]
    rfl

theorem discrBits_toCopy (σ : State) (op : Operand) :
    discrBits σ op.toCopy = discrBits σ op := by
  cases op <;> rfl

theorem discrBits_const_int (σ : State) (v : Nat) :
    discrBits σ (.const (.int v)) = some v := rfl

theorem discrBits_setLocal (σ : State) (op : Operand) (tmp : Local) (x : Val)
    (h : op.readsBelow tmp) : discrBits (σ.setLocal tmp x) op = discrBits σ op := by
  cases op with
  | copy l =>
    have hne : l ≠ tmp := Nat.ne_of_lt h
    simp [discrBits, evalOperand, State.setLocal, hne]
  | move l =>
    have hne : l ≠ tmp := Nat.ne_of_lt h
    simp [discrBits, evalOperand, State.setLocal, hne]
  | const v => rfl

theorem readsBelow_succ (op : Operand) (tmp : Local) (h : op.readsBelow tmp) :
    op.readsBelow (tmp + 1) := by
  cases op with
  | copy l => exact Nat.lt_succ_of_lt h
  | move l => exact Nat.lt_succ_of_lt h
  | const v => exact True.intro

theorem exec_assumeCmp (σ : State) (c : CmpOp) (discr : Operand) (v d : Nat) (tmp : Local)
    (hd : discrBits σ discr = some d) :
    execStmts σ (assumeCmp c discr v tmp) =
      if cmpBits c d v = true then some (σ.setLocal tmp (.bool true)) else none := by
  have hr : evalRvalue σ (.cmp c discr.toCopy (.const (.int v))) =
      some (.bool (cmpBits c d v)) := by
    simp only [evalRvalue, discrBits_toCopy, hd, discrBits_const_int]
  cases hc : cmpBits c d v <;>
    simp [assumeCmp, execStmts, execStmt, hr, hc, execAssume, evalOperand, State.setLocal]

theorem exec_assumeCmp_none (σ : State) (c : CmpOp) (discr : Operand) (v : Nat) (tmp : Local)
    (hd : discrBits σ discr = none) : execStmts σ (assumeCmp c discr v tmp) = none := by
  have hr : evalRvalue σ (.cmp c discr.toCopy (.const (.int v))) = none := by
    simp only [evalRvalue, discrBits_toCopy, hd]
  simp [assumeCmp, execStmts, execStmt, hr]

/-- Running the `Ne` assumptions: undefined behaviour exactly when the
discriminant equals a removed value; otherwise only fresh temporaries change. -/
theorem exec_neAssumes (discr : Operand) (d : Nat) :
    ∀ (removed : List (Nat × Block)) (tmp : Local) (σ : State),
      discr.readsBelow tmp → discrBits σ discr = some d →
      (d ∈ removed.map Prod.fst → execStmts σ (neAssumes discr removed tmp) = none) ∧
      (d ∉ removed.map Prod.fst →
        ∃ σ', execStmts σ (neAssumes discr removed tmp) = some σ' ∧
          AgreeBelow tmp σ σ' ∧ discrBits σ' discr = some d) := by
  intro removed
  induction removed with
  | nil =>
    intro tmp σ _ hd
    exact ⟨fun h => absurd h List.not_mem_nil, fun _ => ⟨σ, rfl, agreeBelow_refl tmp σ, hd⟩⟩
  | cons p rest ih =>
    intro tmp σ hfresh hd
    obtain ⟨v, b⟩ := p
    have hexec : execStmts σ (neAssumes discr ((v, b) :: rest) tmp) =
        match execStmts σ (assumeCmp .ne discr v tmp) with
        | some σ' => execStmts σ' (neAssumes discr rest (tmp + 1))
        | none => none := execStmts_append σ _ _
    rw [exec_assumeCmp σ .ne discr v d tmp hd] at hexec
    by_cases hdv : d = v
    · have hc : cmpBits .ne d v = false := by simp [cmpBits, hdv]
      rw [hc] at hexec
      refine ⟨fun _ => ?_, fun hnot => ?_⟩
      · rw [hexec]
        rfl
      · exact absurd (by simp [hdv]) hnot
    · have hc : cmpBits .ne d v = true := by simp [cmpBits, hdv]
      rw [hc] at hexec
      have hexec' : execStmts σ (neAssumes discr ((v, b) :: rest) tmp) =
          execStmts (σ.setLocal tmp (.bool true)) (neAssumes discr rest (tmp + 1)) := by
        rw [hexec]
        rfl
      have hd' : discrBits (σ.setLocal tmp (.bool true)) discr = some d := by
        rw [discrBits_setLocal σ discr tmp _ hfresh]
        exact hd
      have hih := ih (tmp + 1) (σ.setLocal tmp (.bool true)) (readsBelow_succ discr tmp hfresh) hd'
      refine ⟨fun hmem => ?_, fun hnot => ?_⟩
      · have hm : d ∈ rest.map Prod.fst := by
          simpa [hdv] using hmem
        rw [hexec']
        exact hih.1 hm
      · have hm : d ∉ rest.map Prod.fst := fun m => hnot (by simp [m])
        obtain ⟨σ', he, hag, hd''⟩ := hih.2 hm
        exact ⟨σ', by rw [hexec']; exact he, agreeBelow_step tmp σ σ' _ hag, hd''⟩

theorem exec_neAssumes_none (discr : Operand) (v : Nat) (b : Block)
    (rest : List (Nat × Block)) (tmp : Local) (σ : State)
    (hd : discrBits σ discr = none) :
    execStmts σ (neAssumes discr ((v, b) :: rest) tmp) = none := by
  have hexec : execStmts σ (neAssumes discr ((v, b) :: rest) tmp) =
      match execStmts σ (assumeCmp .ne discr v tmp) with
      | some σ' => execStmts σ' (neAssumes discr rest (tmp + 1))
      | none => none := execStmts_append σ _ _
  rw [exec_assumeCmp_none σ .ne discr v tmp hd] at hexec
  exact hexec

/-- The block produced by the pass: original statements are untouched, so only
the appended statements and the new terminator are run here. -/
noncomputable def prunedOutcome (U : Block → Bool) (σ : State) (discr : Operand)
    (targets : List (Nat × Block)) (otherwise : Block) (tmp : Local) : Outcome :=
  execBlock σ (pruneSwitch U discr targets otherwise tmp).1
    (pruneSwitch U discr targets otherwise tmp).2

theorem mem_removed_iff (U : Block → Bool) (ts : List (Nat × Block)) (d : Nat) :
    d ∈ (ts.filter (fun p => U p.2)).map Prod.fst ↔ ∃ b, (d, b) ∈ ts ∧ U b = true := by
  constructor
  · intro h
    obtain ⟨⟨v, b⟩, hm, hv⟩ := List.mem_map.mp h
    have hm' := List.mem_filter.mp hm
    exact ⟨b, by simpa [← hv] using hm'.1, hm'.2⟩
  · intro ⟨b, hm, hb⟩
    exact List.mem_map.mpr ⟨(d, b), List.mem_filter.mpr ⟨hm, hb⟩, rfl⟩

theorem collapse_switch (U : Block → Bool) (σ : State) (discr : Operand)
    (ts : List (Nat × Block)) (o : Block) :
    collapse U (execTerm σ (.switchInt discr ts o)) =
      match discrBits σ discr with
      | some d => if U (lookup ts o d) = true then .ub else .jump (lookup ts o d) σ
      | none => .ub := by
  cases h : discrBits σ discr with
  | none => simp [execTerm, h, collapse]
  | some d => simp [execTerm, h, collapse]

theorem collapse_switch_none (U : Block → Bool) (σ : State) (discr : Operand)
    (ts : List (Nat × Block)) (o : Block) (h : discrBits σ discr = none) :
    collapse U (execTerm σ (.switchInt discr ts o)) = .ub := by
  rw [collapse_switch, h]

theorem collapse_jump_flagged (U : Block → Bool) (b : Block) (σ : State)
    (h : U b = true) : collapse U (.jump b σ) = .ub := by
  simp [collapse, h]

theorem collapse_jump_unflagged (U : Block → Bool) (b : Block) (σ : State)
    (h : U b = false) : collapse U (.jump b σ) = .jump b σ := by
  simp [collapse, h]

theorem collapse_switch_flagged (U : Block → Bool) (σ : State) (discr : Operand)
    (ts : List (Nat × Block)) (o : Block) (d : Nat) (h : discrBits σ discr = some d)
    (hu : U (lookup ts o d) = true) :
    collapse U (execTerm σ (.switchInt discr ts o)) = .ub := by
  rw [collapse_switch, h]
  simp [hu]

theorem collapse_switch_unflagged (U : Block → Bool) (σ : State) (discr : Operand)
    (ts : List (Nat × Block)) (o : Block) (d : Nat) (h : discrBits σ discr = some d)
    (hu : U (lookup ts o d) = false) :
    collapse U (execTerm σ (.switchInt discr ts o)) = .jump (lookup ts o d) σ := by
  rw [collapse_switch, h]
  simp [hu]

theorem outcomeEquiv_ub (tmp : Local) : OutcomeEquiv tmp .ub .ub := True.intro

theorem outcomeEquiv_jump (tmp : Local) (b : Block) (σ σ' : State)
    (h : AgreeBelow tmp σ σ') : OutcomeEquiv tmp (.jump b σ) (.jump b σ') :=
  And.intro rfl h

/-- **Exactness of the switch pruning.** For a `SwitchInt` with at least one
valued arm and pairwise distinct arm values, whose discriminant operand does not
read the fresh temporaries, the original terminator and the pruned block either
both have undefined behaviour (entering a flagged block counts as undefined
behaviour), or both continue at the same block in states that agree on memory
and on every local below the first fresh temporary. -/
theorem pruneSwitch_exact (U : Block → Bool) (discr : Operand)
    (targets : List (Nat × Block)) (otherwise : Block) (tmp : Local) (σ : State)
    (hfresh : discr.readsBelow tmp)
    (hnodup : (targets.map Prod.fst).Nodup)
    (hne : targets ≠ []) :
    OutcomeEquiv tmp
      (collapse U (execTerm σ (.switchInt discr targets otherwise)))
      (collapse U (prunedOutcome U σ discr targets otherwise tmp)) := by
  cases hU : U otherwise with
  | true =>
    cases hreach : targets.filter (fun p => !U p.2) with
    | nil =>
      -- every successor is flagged: the block becomes `unreachable`
      have hp : pruneSwitch U discr targets otherwise tmp = ([], .unreachable) := by
        unfold pruneSwitch
        rw [hU, hreach]
        rfl
      have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) = .ub := by
        unfold prunedOutcome
        rw [hp]
        rfl
      rw [hT]
      cases hd : discrBits σ discr with
      | none =>
        rw [collapse_switch_none U σ discr targets otherwise hd]
        exact outcomeEquiv_ub tmp
      | some d =>
        have hall : U (lookup targets otherwise d) = true := by
          cases lookup_eq_otherwise_or_mem targets otherwise d with
          | inl h => rw [h]; exact hU
          | inr h =>
            exact filter_reach_nil U targets hreach _ h
        rw [collapse_switch_flagged U σ discr targets otherwise d hd hall]
        exact outcomeEquiv_ub tmp
    | cons x xs =>
      cases xs with
      | nil =>
        -- one surviving arm, flagged `otherwise`: `assume(discr == v); goto t`
        obtain ⟨v, t⟩ := x
        have hp : pruneSwitch U discr targets otherwise tmp =
            (assumeCmp .eq discr v tmp, .goto t) := by
          unfold pruneSwitch
          rw [hU, hreach]
          rfl
        have hmem : (v, t) ∈ targets ∧ U t = false := by
          have h1 : (v, t) ∈ targets.filter (fun p => !U p.2) := by
            rw [hreach]
            exact List.mem_cons_self
          have h2 := List.mem_filter.mp h1
          exact ⟨h2.1, by simpa using h2.2⟩
        cases hd : discrBits σ discr with
        | none =>
          have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) = .ub := by
            unfold prunedOutcome
            rw [hp]
            show collapse U (execBlock σ (assumeCmp .eq discr v tmp) (.goto t)) = .ub
            unfold execBlock
            rw [exec_assumeCmp_none σ .eq discr v tmp hd]
            rfl
          rw [hT, collapse_switch_none U σ discr targets otherwise hd]
          exact outcomeEquiv_ub tmp
        | some d =>
          have hexec := exec_assumeCmp σ .eq discr v d tmp hd
          by_cases hdv : d = v
          · have hc : cmpBits .eq d v = true := by simp [cmpBits, hdv]
            have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) =
                .jump t (σ.setLocal tmp (.bool true)) := by
              unfold prunedOutcome
              rw [hp]
              show collapse U (execBlock σ (assumeCmp .eq discr v tmp) (.goto t)) = _
              unfold execBlock
              rw [hexec, hc]
              exact collapse_jump_unflagged U t _ hmem.2
            have hl : lookup targets otherwise d = t :=
              lookup_of_mem_nodup targets otherwise d t hnodup (hdv ▸ hmem.1)
            have hu : U (lookup targets otherwise d) = false := by rw [hl]; exact hmem.2
            rw [hT, collapse_switch_unflagged U σ discr targets otherwise d hd hu, hl]
            exact outcomeEquiv_jump tmp t σ _ (agreeBelow_setLocal tmp σ _)
          · have hc : cmpBits .eq d v = false := by simp [cmpBits, hdv]
            have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) = .ub := by
              unfold prunedOutcome
              rw [hp]
              show collapse U (execBlock σ (assumeCmp .eq discr v tmp) (.goto t)) = _
              unfold execBlock
              rw [hexec, hc]
              rfl
            have hall : U (lookup targets otherwise d) = true := by
              cases hb : U (lookup targets otherwise d) with
              | true => rfl
              | false =>
                have h1 := lookup_filter_reachable U targets otherwise d hb
                rw [hreach] at h1
                have h2 : lookup [(v, t)] otherwise d = otherwise := by simp [lookup, hdv]
                rw [h2] at h1
                rw [← h1, hU] at hb
                cases hb
            rw [hT, collapse_switch_flagged U σ discr targets otherwise d hd hall]
            exact outcomeEquiv_ub tmp
      | cons y ys =>
        -- at least two surviving arms, flagged `otherwise`: smaller `SwitchInt`, no `assume`
        have hp : pruneSwitch U discr targets otherwise tmp =
            ([], .switchInt discr (x :: y :: ys) otherwise) := by
          unfold pruneSwitch
          rw [hU, hreach]
          rfl
        have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) =
            collapse U (execTerm σ
              (.switchInt discr (targets.filter (fun p => !U p.2)) otherwise)) := by
          unfold prunedOutcome
          rw [hp, hreach]
          rfl
        rw [hT]
        cases hd : discrBits σ discr with
        | none =>
          rw [collapse_switch_none U σ discr targets otherwise hd,
            collapse_switch_none U σ discr _ otherwise hd]
          exact outcomeEquiv_ub tmp
        | some d =>
          cases hb : U (lookup targets otherwise d) with
          | false =>
            have hlk := lookup_filter_reachable U targets otherwise d hb
            have hb' : U (lookup (targets.filter (fun p => !U p.2)) otherwise d) = false := by
              rw [hlk]
              exact hb
            rw [collapse_switch_unflagged U σ discr targets otherwise d hd hb,
              collapse_switch_unflagged U σ discr _ otherwise d hd hb', hlk]
            exact outcomeEquiv_jump tmp _ σ σ (agreeBelow_refl tmp σ)
          | true =>
            have hlk := lookup_filter_unreachable U targets otherwise d hnodup hb
            have hb' : U (lookup (targets.filter (fun p => !U p.2)) otherwise d) = true := by
              rw [hlk]
              exact hU
            rw [collapse_switch_flagged U σ discr targets otherwise d hd hb,
              collapse_switch_flagged U σ discr _ otherwise d hd hb']
            exact outcomeEquiv_ub tmp
  | false =>
    cases hreach : targets.filter (fun p => !U p.2) with
    | nil =>
      -- every valued arm is flagged, `otherwise` is not: `Ne` assumptions, then `goto otherwise`
      have hp : pruneSwitch U discr targets otherwise tmp =
          (neAssumes discr (targets.filter (fun p => U p.2)) tmp, .goto otherwise) := by
        unfold pruneSwitch
        rw [hU, hreach]
        rfl
      cases hd : discrBits σ discr with
      | none =>
        have hrem : ∃ v b rest, targets.filter (fun p => U p.2) = (v, b) :: rest := by
          cases targets with
          | nil => exact absurd rfl hne
          | cons p tl =>
            obtain ⟨v, b⟩ := p
            have hflag : U b = true := by
              exact filter_reach_nil U _ hreach (v, b) List.mem_cons_self
            exact ⟨v, b, tl.filter (fun p => U p.2), by simp [hflag]⟩
        obtain ⟨v, b, rest, hrem⟩ := hrem
        have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) = .ub := by
          unfold prunedOutcome
          rw [hp, hrem]
          show collapse U
            (execBlock σ (neAssumes discr ((v, b) :: rest) tmp) (.goto otherwise)) = .ub
          unfold execBlock
          rw [exec_neAssumes_none discr v b rest tmp σ hd]
          rfl
        rw [hT, collapse_switch_none U σ discr targets otherwise hd]
        exact outcomeEquiv_ub tmp
      | some d =>
        obtain ⟨hin, hout⟩ :=
          exec_neAssumes discr d (targets.filter (fun p => U p.2)) tmp σ hfresh hd
        by_cases hmem : d ∈ (targets.filter (fun p => U p.2)).map Prod.fst
        · obtain ⟨b, hb1, hb2⟩ := (mem_removed_iff U targets d).mp hmem
          have hl := lookup_of_mem_nodup targets otherwise d b hnodup hb1
          have hu : U (lookup targets otherwise d) = true := by rw [hl]; exact hb2
          have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) = .ub := by
            unfold prunedOutcome
            rw [hp]
            show collapse U (execBlock σ
              (neAssumes discr (targets.filter (fun p => U p.2)) tmp) (.goto otherwise)) = .ub
            unfold execBlock
            rw [hin hmem]
            rfl
          rw [hT, collapse_switch_flagged U σ discr targets otherwise d hd hu]
          exact outcomeEquiv_ub tmp
        · obtain ⟨σ', he, hag, _⟩ := hout hmem
          have hl : lookup targets otherwise d = otherwise := by
            cases lookup_eq_otherwise_or_mem targets otherwise d with
            | inl h => exact h
            | inr h =>
              have hu : U (lookup targets otherwise d) = true := by
                exact filter_reach_nil U targets hreach _ h
              exact absurd ((mem_removed_iff U targets d).mpr ⟨_, h, hu⟩) hmem
          have hu : U (lookup targets otherwise d) = false := by rw [hl]; exact hU
          have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) =
              .jump otherwise σ' := by
            unfold prunedOutcome
            rw [hp]
            show collapse U (execBlock σ
              (neAssumes discr (targets.filter (fun p => U p.2)) tmp) (.goto otherwise)) = _
            unfold execBlock
            rw [he]
            exact collapse_jump_unflagged U otherwise σ' hU
          rw [hT, collapse_switch_unflagged U σ discr targets otherwise d hd hu, hl]
          exact outcomeEquiv_jump tmp otherwise σ σ' hag
    | cons x xs =>
      -- some arm survives, `otherwise` is not flagged: `Ne` assumptions, smaller `SwitchInt`
      have hp : pruneSwitch U discr targets otherwise tmp =
          (neAssumes discr (targets.filter (fun p => U p.2)) tmp,
            .switchInt discr (x :: xs) otherwise) := by
        unfold pruneSwitch
        rw [hU, hreach]
        rfl
      cases hd : discrBits σ discr with
      | none =>
        have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) = .ub := by
          unfold prunedOutcome
          rw [hp]
          show collapse U (execBlock σ
            (neAssumes discr (targets.filter (fun p => U p.2)) tmp)
            (.switchInt discr (x :: xs) otherwise)) = .ub
          cases hrem : targets.filter (fun p => U p.2) with
          | nil =>
            show collapse U (execTerm σ (.switchInt discr (x :: xs) otherwise)) = .ub
            exact collapse_switch_none U σ discr _ otherwise hd
          | cons p rest =>
            obtain ⟨v, b⟩ := p
            unfold execBlock
            rw [exec_neAssumes_none discr v b rest tmp σ hd]
            rfl
        rw [hT, collapse_switch_none U σ discr targets otherwise hd]
        exact outcomeEquiv_ub tmp
      | some d =>
        obtain ⟨hin, hout⟩ :=
          exec_neAssumes discr d (targets.filter (fun p => U p.2)) tmp σ hfresh hd
        by_cases hmem : d ∈ (targets.filter (fun p => U p.2)).map Prod.fst
        · obtain ⟨b, hb1, hb2⟩ := (mem_removed_iff U targets d).mp hmem
          have hl := lookup_of_mem_nodup targets otherwise d b hnodup hb1
          have hu : U (lookup targets otherwise d) = true := by rw [hl]; exact hb2
          have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) = .ub := by
            unfold prunedOutcome
            rw [hp]
            show collapse U (execBlock σ
              (neAssumes discr (targets.filter (fun p => U p.2)) tmp)
              (.switchInt discr (x :: xs) otherwise)) = .ub
            unfold execBlock
            rw [hin hmem]
            rfl
          rw [hT, collapse_switch_flagged U σ discr targets otherwise d hd hu]
          exact outcomeEquiv_ub tmp
        · obtain ⟨σ', he, hag, hd'⟩ := hout hmem
          have hb : U (lookup targets otherwise d) = false := by
            cases hb : U (lookup targets otherwise d) with
            | false => rfl
            | true =>
              cases lookup_eq_otherwise_or_mem targets otherwise d with
              | inl h =>
                rw [h, hU] at hb
                cases hb
              | inr h => exact absurd ((mem_removed_iff U targets d).mpr ⟨_, h, hb⟩) hmem
          have hlk : lookup (x :: xs) otherwise d = lookup targets otherwise d := by
            rw [← hreach]
            exact lookup_filter_reachable U targets otherwise d hb
          have hb' : U (lookup (x :: xs) otherwise d) = false := by
            rw [hlk]
            exact hb
          have hT : collapse U (prunedOutcome U σ discr targets otherwise tmp) =
              .jump (lookup targets otherwise d) σ' := by
            unfold prunedOutcome
            rw [hp]
            show collapse U (execBlock σ
              (neAssumes discr (targets.filter (fun p => U p.2)) tmp)
              (.switchInt discr (x :: xs) otherwise)) = _
            unfold execBlock
            rw [he]
            show collapse U (execTerm σ' (.switchInt discr (x :: xs) otherwise)) = _
            rw [collapse_switch_unflagged U σ' discr _ otherwise d hd' hb', hlk]
          rw [hT, collapse_switch_unflagged U σ discr targets otherwise d hd hb]
          exact outcomeEquiv_jump tmp _ σ σ' hag

theorem outcomeEquiv_isUb {tmp : Local} {o₁ o₂ : Outcome} (h : OutcomeEquiv tmp o₁ o₂) :
    o₁.isUb = o₂.isUb := by
  cases o₁ with
  | ub =>
    cases o₂ with
    | ub => rfl
    | jump b σ => exact False.elim h
    | done σ => exact False.elim h
  | jump b σ =>
    cases o₂ with
    | ub => exact False.elim h
    | jump b' σ' => rfl
    | done σ' => exact False.elim h
  | done σ =>
    cases o₂ with
    | ub => exact False.elim h
    | jump b' σ' => exact False.elim h
    | done σ' => rfl

/-- **Bidirectional statement.** The original terminator has undefined behaviour
if and only if the pruned block does. -/
theorem pruneSwitch_ub_iff (U : Block → Bool) (discr : Operand)
    (targets : List (Nat × Block)) (otherwise : Block) (tmp : Local) (σ : State)
    (hfresh : discr.readsBelow tmp)
    (hnodup : (targets.map Prod.fst).Nodup)
    (hne : targets ≠ []) :
    (collapse U (execTerm σ (.switchInt discr targets otherwise))).isUb = true ↔
      (collapse U (prunedOutcome U σ discr targets otherwise tmp)).isUb = true := by
  rw [outcomeEquiv_isUb (pruneSwitch_exact U discr targets otherwise tmp σ hfresh hnodup hne)]

/-! ### `assume` in terms of `SwitchInt` and `unreachable` -/

theorem assume_ok_iff (σ : State) (op : Operand) :
    (execStmt σ (.assume op)).isSome = true ↔ evalOperand σ op = some (.bool true) := by
  show (execAssume σ op).isSome = true ↔ _
  unfold execAssume
  cases h : evalOperand σ op with
  | none => simp
  | some v =>
    cases v with
    | int n => simp
    | ptr a => simp
    | bool b => cases b <;> simp

theorem assume_true_ok (σ : State) (op : Operand)
    (h : evalOperand σ op = some (.bool true)) : execStmt σ (.assume op) = some σ := by
  show execAssume σ op = some σ
  unfold execAssume
  rw [h]

theorem assume_false_ub (σ : State) (op : Operand)
    (h : evalOperand σ op = some (.bool false)) : execStmt σ (.assume op) = none := by
  show execAssume σ op = none
  unfold execAssume
  rw [h]

/-- A well-typed `assume(op)` (the MIR validator requires a `bool` operand) is
exactly `switchInt(op) -> [0: u, otherwise: next]` with `u` a flagged block. -/
theorem assume_as_switch_gadget (U : Block → Bool) (σ : State) (op : Operand)
    (u next : Block) (hu : U u = true) (hnext : U next = false)
    (hty : ∀ v, evalOperand σ op = some v → ∃ b, v = .bool b) :
    collapse U (execTerm σ (.switchInt op [(0, u)] next)) =
      match execAssume σ op with
      | some σ' => .jump next σ'
      | none => .ub := by
  rw [collapse_switch]
  cases he : evalOperand σ op with
  | none => simp [discrBits, execAssume, he]
  | some v =>
    obtain ⟨b, hb⟩ := hty v he
    subst hb
    cases b with
    | true => simp [discrBits, execAssume, he, Val.bits, lookup, hnext]
    | false => simp [discrBits, execAssume, he, Val.bits, lookup, hu]

/-! ## Section 7: `UnreachableEnumBranching` -/

/-- Removes the first occurrence of `v` (the list stands for the set
`allowed_variants`; `remove` on a set and on a duplicate-free list agree). -/
noncomputable def eraseVal (v : Nat) : List Nat → List Nat
  | [] => []
  | a :: rest => if a = v then rest else a :: eraseVal v rest

theorem mem_eraseVal_of_ne (v d : Nat) (hne : d ≠ v) :
    ∀ l : List Nat, d ∈ l → d ∈ eraseVal v l := by
  intro l
  induction l with
  | nil => intro h; exact absurd h List.not_mem_nil
  | cons a rest ih =>
    intro h
    by_cases hav : a = v
    · have hd : d ∈ rest := by
        cases List.mem_cons.mp h with
        | inl e => exact absurd (e.trans hav) hne
        | inr hm => exact hm
      simpa [eraseVal, hav] using hd
    · cases List.mem_cons.mp h with
      | inl e => simp [eraseVal, hav, e]
      | inr hm =>
        have := ih hm
        simp [eraseVal, hav, this]

theorem mem_of_mem_eraseVal (v d : Nat) :
    ∀ l : List Nat, d ∈ eraseVal v l → d ∈ l := by
  intro l
  induction l with
  | nil => intro h; exact h
  | cons a rest ih =>
    intro h
    by_cases hav : a = v
    · have hd : d ∈ rest := by simpa [eraseVal, hav] using h
      exact List.mem_cons_of_mem _ hd
    · have h' : d = a ∨ d ∈ eraseVal v rest := by simpa [eraseVal, hav] using h
      cases h' with
      | inl e => rw [e]; exact List.mem_cons_self
      | inr hm => exact List.mem_cons_of_mem _ (ih hm)

/-- The loop over explicit arms: an arm whose value is not (or is no longer) in
the set of discriminants of inhabited variants is redirected to the unreachable
block `u`; a matching discriminant is removed from the set. Returns the new
arms and the inhabited discriminants that no arm covers. -/
noncomputable def markArms (u : Block) : List Nat → List (Nat × Block) → List (Nat × Block) × List Nat
  | allowed, [] => ([], allowed)
  | allowed, (v, t) :: rest =>
    if v ∈ allowed then
      ((v, t) :: (markArms u (eraseVal v allowed) rest).1,
        (markArms u (eraseVal v allowed) rest).2)
    else
      ((v, u) :: (markArms u allowed rest).1, (markArms u allowed rest).2)

/-- `replace_otherwise_to_unreachable`: when at most one inhabited discriminant
is uncovered and `otherwise` is not already an empty unreachable block, the
uncovered discriminant (if any) gets an explicit arm to the old `otherwise` and
`otherwise` becomes the unreachable block. -/
noncomputable def enumCore (otherwise u : Block) (arms : List (Nat × Block)) :
    List Nat → Bool → List (Nat × Block) × Block
  | [], false => (arms, u)
  | [w], false => (arms ++ [(w, otherwise)], u)
  | [], true => (arms, otherwise)
  | [_], true => (arms, otherwise)
  | _ :: _ :: _, _ => (arms, otherwise)

noncomputable def enumBranching (allowed : List Nat) (targets : List (Nat × Block))
    (otherwise u : Block) (otherwiseAlreadyUnreachable : Bool) :
    List (Nat × Block) × Block :=
  enumCore otherwise u (markArms u allowed targets).1 (markArms u allowed targets).2
    otherwiseAlreadyUnreachable

theorem markArms_vals (u : Block) (ts : List (Nat × Block)) :
    ∀ allowed, (markArms u allowed ts).1.map Prod.fst = ts.map Prod.fst := by
  induction ts with
  | nil => intro allowed; rfl
  | cons p rest ih =>
    intro allowed
    obtain ⟨v, t⟩ := p
    by_cases hv : v ∈ allowed
    · simp [markArms, hv, ih]
    · simp [markArms, hv, ih]

theorem markArms_lookup_allowed (u : Block) (ts : List (Nat × Block)) (d : Nat)
    (o o' : Block) :
    ∀ allowed, d ∈ allowed → d ∈ ts.map Prod.fst →
      lookup (markArms u allowed ts).1 o' d = lookup ts o d := by
  induction ts with
  | nil => intro allowed _ hm; exact absurd hm List.not_mem_nil
  | cons p rest ih =>
    intro allowed hd hm
    obtain ⟨v, t⟩ := p
    by_cases hdv : d = v
    · subst hdv
      simp [markArms, hd, lookup]
    · have hm' : d ∈ rest.map Prod.fst := by simpa [hdv] using hm
      by_cases hv : v ∈ allowed
      · have hd' : d ∈ eraseVal v allowed := mem_eraseVal_of_ne v d hdv allowed hd
        simp [markArms, hv, lookup, hdv, ih (eraseVal v allowed) hd' hm']
      · simp [markArms, hv, lookup, hdv, ih allowed hd hm']

theorem markArms_uncovered (u : Block) (ts : List (Nat × Block)) (d : Nat) :
    ∀ allowed, d ∈ allowed → d ∉ ts.map Prod.fst → d ∈ (markArms u allowed ts).2 := by
  induction ts with
  | nil => intro allowed hd _; exact hd
  | cons p rest ih =>
    intro allowed hd hm
    obtain ⟨v, t⟩ := p
    have hdv : d ≠ v := fun e => hm (by simp [e])
    have hm' : d ∉ rest.map Prod.fst := fun m => hm (by simp [m])
    by_cases hv : v ∈ allowed
    · simp only [markArms, hv, ite_true]
      exact ih (eraseVal v allowed) (mem_eraseVal_of_ne v d hdv allowed hd) hm'
    · simp only [markArms, hv, ite_false]
      exact ih allowed hd hm'

theorem markArms_forged (u : Block) (ts : List (Nat × Block)) (d : Nat) (o' : Block) :
    ∀ allowed, d ∉ allowed → d ∈ ts.map Prod.fst →
      lookup (markArms u allowed ts).1 o' d = u := by
  induction ts with
  | nil => intro allowed _ hm; exact absurd hm List.not_mem_nil
  | cons p rest ih =>
    intro allowed hd hm
    obtain ⟨v, t⟩ := p
    by_cases hdv : d = v
    · subst hdv
      simp [markArms, hd, lookup]
    · have hm' : d ∈ rest.map Prod.fst := by simpa [hdv] using hm
      by_cases hv : v ∈ allowed
      · have hd' : d ∉ eraseVal v allowed := fun m => hd (mem_of_mem_eraseVal v d allowed m)
        simp [markArms, hv, lookup, hdv, ih (eraseVal v allowed) hd' hm']
      · simp [markArms, hv, lookup, hdv, ih allowed hd hm']

theorem lookup_append_of_mem (l1 l2 : List (Nat × Block)) (o o' : Block) (d : Nat)
    (h : d ∈ l1.map Prod.fst) : lookup (l1 ++ l2) o d = lookup l1 o' d := by
  induction l1 with
  | nil => exact absurd h List.not_mem_nil
  | cons p rest ih =>
    obtain ⟨v, t⟩ := p
    by_cases hdv : d = v
    · simp [lookup, hdv]
    · have h' : d ∈ rest.map Prod.fst := by simpa [hdv] using h
      simp [lookup, hdv, ih h']

theorem lookup_append_of_not_mem (l1 l2 : List (Nat × Block)) (o : Block) (d : Nat)
    (h : d ∉ l1.map Prod.fst) : lookup (l1 ++ l2) o d = lookup l2 o d := by
  induction l1 with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨v, t⟩ := p
    have hdv : d ≠ v := fun e => h (by simp [e])
    have h' : d ∉ rest.map Prod.fst := fun m => h (by simp [m])
    simp [lookup, hdv, ih h']

/-- **Soundness under inhabited-variant typing.** If the discriminant is the
discriminant of an inhabited variant, the rewritten `SwitchInt` has the same
successor as the original one. -/
theorem enumBranching_sound (allowed : List Nat) (targets : List (Nat × Block))
    (otherwise u : Block) (flag : Bool) (d : Nat) (hd : d ∈ allowed) :
    lookup (enumBranching allowed targets otherwise u flag).1
        (enumBranching allowed targets otherwise u flag).2 d =
      lookup targets otherwise d := by
  unfold enumBranching
  by_cases hm : d ∈ targets.map Prod.fst
  · have key : ∀ o', lookup (markArms u allowed targets).1 o' d = lookup targets otherwise d :=
      fun o' => markArms_lookup_allowed u targets d otherwise o' allowed hd hm
    have hm1 : d ∈ (markArms u allowed targets).1.map Prod.fst := by
      rw [markArms_vals]
      exact hm
    cases (markArms u allowed targets).2 with
    | nil => cases flag <;> exact key _
    | cons w ws =>
      cases ws with
      | nil =>
        cases flag with
        | false =>
          show lookup ((markArms u allowed targets).1 ++ [(w, otherwise)]) u d = _
          rw [lookup_append_of_mem _ _ u u d hm1]
          exact key u
        | true => exact key otherwise
      | cons w2 ws2 => cases flag <;> exact key otherwise
  · have hunc := markArms_uncovered u targets d allowed hd hm
    have hm1 : d ∉ (markArms u allowed targets).1.map Prod.fst := by
      rw [markArms_vals]
      exact hm
    have horig : lookup targets otherwise d = otherwise :=
      lookup_of_not_mem targets otherwise d hm
    have hnew : lookup (markArms u allowed targets).1 otherwise d = otherwise :=
      lookup_of_not_mem _ otherwise d hm1
    cases hrem : (markArms u allowed targets).2 with
    | nil =>
      rw [hrem] at hunc
      exact absurd hunc List.not_mem_nil
    | cons w ws =>
      cases ws with
      | nil =>
        rw [hrem] at hunc
        have hdw : d = w := by simpa using hunc
        cases flag with
        | false =>
          show lookup ((markArms u allowed targets).1 ++ [(w, otherwise)]) u d = _
          rw [lookup_append_of_not_mem _ _ u d hm1, horig]
          simp [lookup, hdw]
        | true =>
          show lookup (markArms u allowed targets).1 otherwise d = _
          rw [hnew, horig]
      | cons w2 ws2 =>
        cases flag <;>
          (show lookup (markArms u allowed targets).1 otherwise d = _; rw [hnew, horig])

/-- A discriminant outside the inhabited set that has an explicit arm is sent
to the unreachable block: the typing hypothesis of `enumBranching_sound` cannot
be dropped. -/
theorem enumBranching_forged_hits_unreachable (allowed : List Nat)
    (targets : List (Nat × Block)) (otherwise u : Block) (flag : Bool) (d : Nat)
    (hd : d ∉ allowed) (hm : d ∈ targets.map Prod.fst) :
    lookup (enumBranching allowed targets otherwise u flag).1
        (enumBranching allowed targets otherwise u flag).2 d = u := by
  unfold enumBranching
  have key : ∀ o', lookup (markArms u allowed targets).1 o' d = u :=
    fun o' => markArms_forged u targets d o' allowed hd hm
  have hm1 : d ∈ (markArms u allowed targets).1.map Prod.fst := by
    rw [markArms_vals]
    exact hm
  cases (markArms u allowed targets).2 with
  | nil => cases flag <;> exact key _
  | cons w ws =>
    cases ws with
    | nil =>
      cases flag with
      | false =>
        show lookup ((markArms u allowed targets).1 ++ [(w, otherwise)]) u d = _
        rw [lookup_append_of_mem _ _ u u d hm1]
        exact key u
      | true => exact key otherwise
    | cons w2 ws2 => cases flag <;> exact key otherwise

/-! ## Section 8: golden specimens and sharpness counterexamples -/

/-- Flags exactly the listed blocks. -/
noncomputable def flagged (bs : List Block) : Block → Bool := fun b => decide (b ∈ bs)

/-- Local `l` holds `v`; every other local is uninitialized; no memory is mapped. -/
noncomputable def stateWith (l : Local) (v : Val) : State :=
  { locals := fun x => if x = l then some v else none, mem := fun _ => none }

noncomputable def emptyState : State := { locals := fun _ => none, mem := fun _ => none }

/-- Slots `16 .. 47` are mapped and hold their own address. -/
noncomputable def mappedState : State :=
  { locals := fun _ => none, mem := fun a => if 16 ≤ a ∧ a < 48 then some a else none }

noncomputable def u64Layout : Layout := { elemSize := 8, align := 8, sizeBound := 4096 }

/-! ### Golden specimens: `pruneSwitch` reproduces what rustc emitted

Each right-hand side transcribes the block that `UnreachablePropagation` produced
for the specimen of the same name (rustc 1.98.0-nightly, commit `14210df0e`);
`_n` is local `n`, `bbN` is block `N`, and a constant is its bit pattern. -/

/-- `switchInt(copy _1) -> [5: bb2, otherwise: bb1]`, `bb1` unreachable, becomes
`_3 = Eq(copy _1, const 5_u8); assume(move _3); goto -> bb2`. -/
theorem golden_one_arm_otherwise_unreachable :
    pruneSwitch (flagged [1]) (.copy 1) [(5, 2)] 1 3 =
      ([.assign 3 (.cmp .eq (.copy 1) (.const (.int 5))), .assume (.move 3)], .goto 2) := rfl

/-- `switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1]`, `bb3` unreachable,
becomes `_3 = Ne(copy _1, const 0_u8); assume(move _3);
switchInt(copy _1) -> [1: bb2, otherwise: bb1]`. -/
theorem golden_removed_arm_otherwise_reachable :
    pruneSwitch (flagged [3]) (.copy 1) [(0, 3), (1, 2)] 1 3 =
      ([.assign 3 (.cmp .ne (.copy 1) (.const (.int 0))), .assume (.move 3)],
        .switchInt (.copy 1) [(1, 2)] 1) := rfl

/-- `switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1]`, `bb2` and `bb3`
unreachable, becomes `_4 = Ne(copy _1, const 0_u8); assume(move _4);
_5 = Ne(copy _1, const 1_u8); assume(move _5); goto -> bb1`. -/
theorem golden_all_arms_unreachable_otherwise_reachable :
    pruneSwitch (flagged [2, 3]) (.copy 1) [(0, 3), (1, 2)] 1 4 =
      ([.assign 4 (.cmp .ne (.copy 1) (.const (.int 0))), .assume (.move 4),
        .assign 5 (.cmp .ne (.copy 1) (.const (.int 1))), .assume (.move 5)], .goto 1) := rfl

/-- `switchInt(copy _1) -> [0: bb2, otherwise: bb1]`, both unreachable, becomes
`unreachable`. -/
theorem golden_everything_unreachable :
    pruneSwitch (flagged [1, 2]) (.copy 1) [(0, 2)] 1 3 = ([], .unreachable) := rfl

/-- `switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1]`, only `bb1`
unreachable: nothing changes and no `assume` is emitted. -/
theorem golden_two_arms_otherwise_unreachable :
    pruneSwitch (flagged [1]) (.copy 1) [(0, 3), (1, 2)] 1 3 =
      ([], .switchInt (.copy 1) [(0, 3), (1, 2)] 1) := rfl

/-- `switchInt(move _2) -> [0: bb2, otherwise: bb1]` on a `bool`, `bb2`
unreachable, becomes `_4 = Ne(copy _2, const false); assume(move _4); goto -> bb1`. -/
theorem golden_bool_discriminant :
    pruneSwitch (flagged [2]) (.move 2) [(0, 2)] 1 4 =
      ([.assign 4 (.cmp .ne (.copy 2) (.const (.int 0))), .assume (.move 4)], .goto 1) := rfl

/-- `switchInt(move _2) -> [0: bb3, 1: bb1, otherwise: bb1]` (a match on
`Result<u32, Infallible>` after `UnreachableEnumBranching`), `bb1` unreachable,
becomes `_4 = Eq(copy _2, const 0_isize); assume(move _4); goto -> bb3`. -/
theorem golden_result_infallible :
    pruneSwitch (flagged [1]) (.move 2) [(0, 3), (1, 1)] 1 4 =
      ([.assign 4 (.cmp .eq (.copy 2) (.const (.int 0))), .assume (.move 4)], .goto 3) := rfl

/-- `switchInt(move _2) -> [0: bb4, 1: bb1, 2: bb2, otherwise: bb1]`, `bb1`
unreachable, becomes `switchInt(move _2) -> [0: bb4, 2: bb2, otherwise: bb1]`
with no `assume`. -/
theorem golden_uninhabited_middle_variant :
    pruneSwitch (flagged [1]) (.move 2) [(0, 4), (1, 1), (2, 2)] 1 3 =
      ([], .switchInt (.move 2) [(0, 4), (2, 2)] 1) := rfl

/-- `UnreachableEnumBranching` on `enum E3 { A, B(Infallible), C }`:
`[0: bb4, 1: bb3, 2: bb2, otherwise: bb1]` becomes
`[0: bb4, 1: bb1, 2: bb2, otherwise: bb1]` (`bb1` is the unreachable block). -/
theorem golden_enum_uninhabited_middle_variant :
    enumBranching [0, 2] [(0, 4), (1, 3), (2, 2)] 1 1 true =
      ([(0, 4), (1, 1), (2, 2)], 1) := rfl

/-- `UnreachableEnumBranching` on a three-variant enum matched with a wildcard:
`[0: bb3, 1: bb2, otherwise: bb1]` becomes
`[0: bb3, 1: bb2, 2: bb1, otherwise: bb5]` (`bb5` is a new unreachable block). -/
theorem golden_enum_otherwise_is_last_variant :
    enumBranching [0, 1, 2] [(0, 3), (1, 2)] 1 5 false =
      ([(0, 3), (1, 2), (2, 1)], 5) := rfl

/-! ### Sharpness counterexamples -/

/-- Dropping an unreachable arm *without* recording the `assume` turns undefined
behaviour into defined behaviour: checking the pruned body would no longer
establish that the original body is free of undefined behaviour. With the
`assume` that rustc emits, the undefined behaviour is still there. -/
theorem ce1_switch_prune_without_assume_loses_ub_reverse_unsound :
    -- original `switchInt(copy _1) -> [0: bb3, 1: bb2, otherwise: bb1]`, `_1 = 0`,
    -- `bb3` unreachable: undefined behaviour
    (collapse (flagged [3])
      (execTerm (stateWith 1 (.int 0)) (.switchInt (.copy 1) [(0, 3), (1, 2)] 1))).isUb = true ∧
    -- arm removed, no `assume`: the same input now takes `otherwise`
    (collapse (flagged [3])
      (execBlock (stateWith 1 (.int 0)) [] (.switchInt (.copy 1) [(1, 2)] 1))).isUb = false ∧
    -- arm removed with the `assume` (what the pass emits): undefined behaviour
    (collapse (flagged [3])
      (prunedOutcome (flagged [3]) (stateWith 1 (.int 0)) (.copy 1) [(0, 3), (1, 2)] 1 3)).isUb
        = true :=
  ⟨rfl, rfl, rfl⟩

/-- A zero-length `copy_nonoverlapping` is undefined behaviour when either
pointer is misaligned, and is defined for null and for dangling aligned
pointers; a non-empty copy from null or between overlapping ranges is undefined
behaviour; a non-empty copy between disjoint mapped ranges copies. -/
theorem ce2_copy_nonoverlapping_zero_count_misaligned_ub_but_null_ok :
    (execCopy u64Layout emptyState 17 16 0).isSome = false ∧
    (execCopy u64Layout emptyState 16 17 0).isSome = false ∧
    (execCopy u64Layout emptyState 0 0 0).isSome = true ∧
    (execCopy u64Layout emptyState 8 4096 0).isSome = true ∧
    (execCopy u64Layout mappedState 0 16 1).isSome = false ∧
    (execCopy u64Layout mappedState 16 16 1).isSome = false ∧
    (execCopy u64Layout mappedState 16 20 1).isSome = false ∧
    (execCopy u64Layout mappedState 16 24 1).map (fun s => s.mem 24) = some (some 16) ∧
    (execCopy u64Layout mappedState 16 24 1).map (fun s => s.mem 31) = some (some 23) ∧
    (execCopy u64Layout mappedState 16 24 1).map (fun s => s.mem 32) = some (some 32) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The same facts at statement level, with operands read from locals. -/
theorem ce2_statement_level :
    (execStmt (stateWith 1 (.bool false)) (.assume (.copy 1))).isSome = false ∧
    (execStmt (stateWith 1 (.bool true)) (.assume (.copy 1))).isSome = true ∧
    (execStmt emptyState (.assume (.copy 1))).isSome = false ∧
    (execStmt emptyState
      (.copyNonOverlapping (.const (.ptr 0)) (.const (.ptr 0)) (.const (.int 0)) u64Layout)).isSome
        = true ∧
    (execStmt emptyState
      (.copyNonOverlapping (.const (.ptr 17)) (.const (.ptr 16)) (.const (.int 0)) u64Layout)).isSome
        = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

noncomputable def ce3Targets : List (Nat × Block) := [(0, 4), (1, 3), (2, 2)]

/-- `UnreachableEnumBranching` output for an enum whose variants `0` and `2` are
inhabited and whose variant `1` is not; block `9` is the unreachable block. -/
noncomputable def ce3New : List (Nat × Block) × Block := enumBranching [0, 2] ce3Targets 7 9 false

/-- A forged discriminant (the uninhabited variant `1`, or the out-of-range
value `5`) runs ordinary code in the original body but enters the unreachable
block after `UnreachableEnumBranching`; inhabited discriminants are unaffected. -/
theorem ce3_forged_uninhabited_enum_discriminant_hits_unreachable_ub :
    ce3New = ([(0, 4), (1, 9), (2, 2)], 9) ∧
    lookup ce3New.1 ce3New.2 0 = lookup ce3Targets 7 0 ∧
    lookup ce3New.1 ce3New.2 2 = lookup ce3Targets 7 2 ∧
    (collapse (flagged [9])
      (execTerm (stateWith 1 (.int 1)) (.switchInt (.copy 1) ce3Targets 7))).isUb = false ∧
    (collapse (flagged [9])
      (execTerm (stateWith 1 (.int 1)) (.switchInt (.copy 1) ce3New.1 ce3New.2))).isUb = true ∧
    (collapse (flagged [9])
      (execTerm (stateWith 1 (.int 5)) (.switchInt (.copy 1) ce3Targets 7))).isUb = false ∧
    (collapse (flagged [9])
      (execTerm (stateWith 1 (.int 5)) (.switchInt (.copy 1) ce3New.1 ce3New.2))).isUb = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A `SwitchInt` with no valued arm is replaced by a `goto` with no `assume`,
so the read of the discriminant disappears: with an uninitialized discriminant
the original is undefined behaviour and the result is not. The hypothesis
`targets ≠ []` of `pruneSwitch_exact` cannot be dropped. -/
theorem ce4_zero_arm_switch_drops_discriminant_read :
    (collapse (flagged []) (execTerm emptyState (.switchInt (.copy 1) [] 1))).isUb = true ∧
    pruneSwitch (flagged []) (.copy 1) [] 1 2 = ([], .goto 1) ∧
    (collapse (flagged []) (prunedOutcome (flagged []) emptyState (.copy 1) [] 1 2)).isUb = false :=
  ⟨rfl, rfl, rfl⟩

/-- With a repeated arm value the pruning is not exact: the first arm for `5`
enters a flagged block, yet the pruned block assumes `_1 == 5` and continues.
The distinct-values hypothesis of `pruneSwitch_exact` (enforced by the MIR
validator) cannot be dropped. -/
theorem ce5_duplicate_switch_values_break_exactness :
    (collapse (flagged [3])
      (execTerm (stateWith 1 (.int 5)) (.switchInt (.copy 1) [(5, 3), (5, 2)] 3))).isUb = true ∧
    (collapse (flagged [3])
      (prunedOutcome (flagged [3]) (stateWith 1 (.int 5)) (.copy 1) [(5, 3), (5, 2)] 3 4)).isUb
        = false :=
  ⟨rfl, rfl⟩

end NonDivergingIntrinsics

#print axioms NonDivergingIntrinsics.pruneSwitch_exact
#print axioms NonDivergingIntrinsics.pruneSwitch_ub_iff
#print axioms NonDivergingIntrinsics.doomed_reaches_ub
#print axioms NonDivergingIntrinsics.doomed_never_done
#print axioms NonDivergingIntrinsics.assume_as_switch_gadget
#print axioms NonDivergingIntrinsics.assume_ok_iff
#print axioms NonDivergingIntrinsics.enumBranching_sound
#print axioms NonDivergingIntrinsics.enumBranching_forged_hits_unreachable
#print axioms NonDivergingIntrinsics.execCopy_isSome_iff
#print axioms NonDivergingIntrinsics.copy_zero_count_ok_iff_aligned
#print axioms NonDivergingIntrinsics.copy_zero_count_null_ok
#print axioms NonDivergingIntrinsics.copy_nonempty_unmapped_src_ub
#print axioms NonDivergingIntrinsics.copy_overlap_ub
#print axioms NonDivergingIntrinsics.copy_ok_slotwise
#print axioms NonDivergingIntrinsics.golden_one_arm_otherwise_unreachable
#print axioms NonDivergingIntrinsics.golden_all_arms_unreachable_otherwise_reachable
#print axioms NonDivergingIntrinsics.golden_enum_otherwise_is_last_variant
#print axioms NonDivergingIntrinsics.ce1_switch_prune_without_assume_loses_ub_reverse_unsound
#print axioms NonDivergingIntrinsics.ce2_copy_nonoverlapping_zero_count_misaligned_ub_but_null_ok
#print axioms NonDivergingIntrinsics.ce2_statement_level
#print axioms NonDivergingIntrinsics.ce3_forged_uninhabited_enum_discriminant_hits_unreachable_ub
#print axioms NonDivergingIntrinsics.ce4_zero_arm_switch_drops_discriminant_read
#print axioms NonDivergingIntrinsics.ce5_duplicate_switch_values_break_exactness
