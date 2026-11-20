import ToyWMM.Exec

/-!
# Straight-line programs, their candidate executions, and the fence-insertion mapping

A program is a list of threads; a thread is a list of instructions (`store`, `load`,
`mfence`) with constant locations and stored values, no registers, no control flow, and no
dependencies. The events of a program are laid out canonically: one initialisation write per
location `0, …, numLocs - 1`, followed by the instructions of thread `0`, thread `1`, … in
program order. A candidate execution of `P` (`ExecOf P X`) has exactly these events (reads may
return any value) and `po` = "same thread, earlier in the layout"; `rf` and `co` are free and
are constrained by `Exec.Wf`.
-/

namespace Toy.WMM

/-- Instructions of the toy source/target language. -/
inductive Instr where
  /-- Store the constant `val` to location `loc`. -/
  | store (loc val : Nat)
  /-- Load from location `loc` (the value is chosen by the execution). -/
  | load (loc : Nat)
  /-- Full fence (x86 `MFENCE`). -/
  | mfence
  deriving DecidableEq, Repr

/-- A program: a list of threads, each a list of instructions. Thread `t` has thread id `t`. -/
abbrev Prog := List (List Instr)

namespace Instr

/-- Location of an instruction (`0` for fences). -/
def loc : Instr → Nat
  | store l _ => l
  | load l => l
  | mfence => 0

/-- The event of an instruction in thread `t` (reads carry the placeholder value `0`). -/
def toEvent (t : Nat) : Instr → Event
  | store l v => ⟨.write, t, l, v⟩
  | load l => ⟨.read, t, l, 0⟩
  | mfence => ⟨.fence, t, 0, 0⟩

end Instr

/-- Events of threads `t, t+1, …` in program order. -/
def threadEvents : Nat → Prog → List Event
  | _, [] => []
  | t, th :: rest => th.map (Instr.toEvent t) ++ threadEvents (t + 1) rest

/-- One more than the largest location mentioned by the program. -/
def Prog.numLocs (P : Prog) : Nat := (P.flatten.map Instr.loc).foldr max 0 + 1

/-- Canonical event layout: initialisation writes for locations `0, …, numLocs - 1`, then the
threads' events. -/
def layout (P : Prog) : List Event :=
  (List.range P.numLocs).map Event.initW ++ threadEvents 0 P

/-- `X` is a candidate execution of program `P`: same events as `layout P` (except for the
values returned by reads) and `po` is "same thread and earlier". -/
structure ExecOf (P : Prog) {n : Nat} (X : Exec n) : Prop where
  length : n = (layout P).length
  kind : ∀ i : Fin n, (X.ev i).kind = ((layout P).getD i.val default).kind
  tid : ∀ i : Fin n, (X.ev i).tid = ((layout P).getD i.val default).tid
  loc : ∀ i : Fin n, (X.ev i).loc = ((layout P).getD i.val default).loc
  val : ∀ i : Fin n, (X.ev i).isRead = false →
    (X.ev i).val = ((layout P).getD i.val default).val
  po : ∀ a b : Fin n, X.po a b = (X.sameThread a b && decide (a.val < b.val))

/-! ## The fence-insertion mapping -/

/-- Insert an `mfence` immediately after every store of a thread. -/
def fenceThread : List Instr → List Instr
  | [] => []
  | .store l v :: rest => .store l v :: .mfence :: fenceThread rest
  | .load l :: rest => .load l :: fenceThread rest
  | .mfence :: rest => .mfence :: fenceThread rest

/-- **The mapping**: insert an `mfence` immediately after every store, in every thread. -/
def fenceAfterStores (P : Prog) : Prog := P.map fenceThread

/-! ## Executions of programs are well-formed in their `po` -/

namespace ExecOf

variable {P : Prog} {n : Nat} {X : Exec n}

theorem poIrrefl (hX : ExecOf P X) : X.PoIrrefl := by
  intro a; rw [hX.po]; simp

theorem poTrans (hX : ExecOf P X) : X.PoTrans := by
  intro a b c hab hbc
  rw [hX.po] at hab hbc ⊢
  simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    decide_eq_true_eq] at hab hbc ⊢
  refine ⟨⟨⟨hab.1.1.1, hbc.1.1.2⟩, hab.1.2.trans hbc.1.2⟩, Nat.lt_trans hab.2 hbc.2⟩

theorem poWithinThread (hX : ExecOf P X) : X.PoWithinThread := by
  intro a b hab
  rw [hX.po] at hab
  simp only [Bool.and_eq_true] at hab
  exact hab.1

theorem poTotal (hX : ExecOf P X) : X.PoTotal := by
  intro a b hab hst
  rw [hX.po, hX.po]
  have hst' : X.sameThread b a = true := by
    simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hst ⊢
    exact ⟨⟨hst.1.2, hst.1.1⟩, hst.2.symm⟩
  rw [hst, hst']
  simp only [Bool.true_and, decide_eq_true_eq]
  have : a.val ≠ b.val := fun h => hab (Fin.ext h)
  omega

end ExecOf

/-! ## Executions of `fenceAfterStores P` fence every write→read pair -/

/-- In the event list `l`, every (non-initialisation) write is immediately followed by a fence
of the same thread. -/
def StoreThenFence (l : List Event) : Prop :=
  ∀ i e, l[i]? = some e → e.kind = .write →
    ∃ f, l[i + 1]? = some f ∧ f.kind = .fence ∧ f.tid = e.tid

theorem StoreThenFence.append {l₁ l₂ : List Event} (h₁ : StoreThenFence l₁)
    (h₂ : StoreThenFence l₂) : StoreThenFence (l₁ ++ l₂) := by
  intro i e he hk
  by_cases hil : i < l₁.length
  · rw [List.getElem?_append_left hil] at he
    obtain ⟨f, hf, hfk, hft⟩ := h₁ i e he hk
    have hi1 : i + 1 < l₁.length := by
      rcases List.getElem?_eq_some_iff.mp hf with ⟨h, _⟩; exact h
    exact ⟨f, by rw [List.getElem?_append_left hi1]; exact hf, hfk, hft⟩
  · have hle : l₁.length ≤ i := by omega
    rw [List.getElem?_append_right hle] at he
    obtain ⟨f, hf, hfk, hft⟩ := h₂ _ e he hk
    refine ⟨f, ?_, hfk, hft⟩
    rw [List.getElem?_append_right (by omega)]
    have : i + 1 - l₁.length = i - l₁.length + 1 := by omega
    rw [this]; exact hf

theorem storeThenFence_fenceThread (t : Nat) (th : List Instr) :
    StoreThenFence ((fenceThread th).map (Instr.toEvent t)) := by
  induction th with
  | nil => intro i e he; simp [fenceThread] at he
  | cons ins rest ih =>
    cases ins with
    | store l v =>
      intro i e he hk
      match i with
      | 0 =>
        simp only [fenceThread, List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at he
        subst he
        exact ⟨Instr.toEvent t .mfence, by simp [fenceThread], rfl, rfl⟩
      | 1 =>
        simp only [fenceThread, List.map_cons, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at he
        subst he; simp [Instr.toEvent] at hk
      | k + 2 =>
        simp only [fenceThread, List.map_cons, List.getElem?_cons_succ] at he
        obtain ⟨f, hf, hfk, hft⟩ := ih k e he hk
        exact ⟨f, by simp only [fenceThread, List.map_cons, List.getElem?_cons_succ]; exact hf,
          hfk, hft⟩
    | load l =>
      intro i e he hk
      match i with
      | 0 =>
        simp only [fenceThread, List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at he
        subst he; simp [Instr.toEvent] at hk
      | k + 1 =>
        simp only [fenceThread, List.map_cons, List.getElem?_cons_succ] at he
        obtain ⟨f, hf, hfk, hft⟩ := ih k e he hk
        exact ⟨f, by simp only [fenceThread, List.map_cons, List.getElem?_cons_succ]; exact hf,
          hfk, hft⟩
    | mfence =>
      intro i e he hk
      match i with
      | 0 =>
        simp only [fenceThread, List.map_cons, List.getElem?_cons_zero, Option.some.injEq] at he
        subst he; simp [Instr.toEvent] at hk
      | k + 1 =>
        simp only [fenceThread, List.map_cons, List.getElem?_cons_succ] at he
        obtain ⟨f, hf, hfk, hft⟩ := ih k e he hk
        exact ⟨f, by simp only [fenceThread, List.map_cons, List.getElem?_cons_succ]; exact hf,
          hfk, hft⟩

theorem storeThenFence_threadEvents (t : Nat) (P : Prog) :
    StoreThenFence (threadEvents t (fenceAfterStores P)) := by
  induction P generalizing t with
  | nil => intro i e he; simp [threadEvents, fenceAfterStores] at he
  | cons th rest ih =>
    exact StoreThenFence.append (storeThenFence_fenceThread t th) (ih (t + 1))

theorem storeThenFence_layout (P : Prog) : StoreThenFence (layout (fenceAfterStores P)) := by
  refine StoreThenFence.append ?_ (storeThenFence_threadEvents 0 P)
  intro i e he hk
  simp only [List.getElem?_map, Option.map_eq_some_iff] at he
  obtain ⟨_, _, rfl⟩ := he
  simp [Event.initW] at hk

theorem ExecOf.getD_eq {P : Prog} {n : Nat} {X : Exec n} (hX : ExecOf P X) (i : Fin n) :
    (layout P)[i.val]? = some ((layout P).getD i.val default) := by
  have hi : i.val < (layout P).length := hX.length ▸ i.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

/-- Every candidate execution of `fenceAfterStores P` has a fence between every `po`-ordered
write→read pair. -/
theorem ExecOf.fenceBetweenWR_of_fenceAfterStores {P : Prog} {n : Nat} {X : Exec n}
    (hX : ExecOf (fenceAfterStores P) X) : X.FenceBetweenWR := by
  intro a b hab hwa hrb
  have hpo := hab
  rw [hX.po] at hpo
  simp only [Exec.sameThread, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
    decide_eq_true_eq] at hpo
  obtain ⟨⟨⟨hai, hbi⟩, htab⟩, hlt⟩ := hpo
  have hka : (X.ev a).kind = .write := by
    revert hwa hai; simp only [Event.isWrite, Event.isInit]
    cases (X.ev a).kind <;> simp
  rw [hX.kind a] at hka
  obtain ⟨f, hf, hfk, hft⟩ := storeThenFence_layout P a.val _ (hX.getD_eq a) hka
  have ha1 : a.val + 1 < n := by
    rcases List.getElem?_eq_some_iff.mp hf with ⟨h, _⟩; have hl := hX.length; omega
  let fi : Fin n := ⟨a.val + 1, ha1⟩
  have hfeq : (layout (fenceAfterStores P)).getD fi.val default = f := by
    rw [List.getD_eq_getElem?_getD]; simp only [fi, hf, Option.getD_some]
  have hfiK : (X.ev fi).kind = .fence := by rw [hX.kind, hfeq, hfk]
  have hfiT : (X.ev fi).tid = (X.ev a).tid := by rw [hX.tid, hX.tid, hfeq, hft]
  have hfiI : (X.ev fi).isInit = false := by simp [Event.isInit, hfiK]
  have hne : fi.val ≠ b.val := by
    intro h
    have : fi = b := Fin.ext h
    rw [← this] at hrb
    simp [Event.isRead, hfiK] at hrb
  have haA : (X.ev a).isAccess = true := by
    revert hwa; simp only [Event.isWrite, Event.isAccess, Event.isFence]
    cases (X.ev a).kind <;> simp
  have hbA : (X.ev b).isAccess = true := by
    revert hrb; simp only [Event.isRead, Event.isAccess, Event.isFence]
    cases (X.ev b).kind <;> simp
  simp only [Exec.fenceOrd, haA, hbA, Bool.true_and, decide_eq_true_eq]
  refine ⟨fi, ?_, by simp [Event.isFence, hfiK], ?_⟩
  · rw [hX.po]
    simp [Exec.sameThread, hai, hfiI, hfiT, fi]
  · rw [hX.po]
    simp only [Exec.sameThread, hfiI, hbi, hfiT, htab, Bool.not_false, beq_self_eq_true,
      Bool.and_self, Bool.true_and, decide_eq_true_eq]
    simp only [fi] at hne ⊢
    omega

end Toy.WMM
