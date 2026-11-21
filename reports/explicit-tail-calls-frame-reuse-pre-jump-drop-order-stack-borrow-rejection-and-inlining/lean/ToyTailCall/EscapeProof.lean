import ToyTailCall.Machine
import ToyTailCall.Borrow
import ToyTailCall.Lemmas

/-!
# Proof support: soundness of the static escape check

The proof has two parts.

1. `taint fn` is a fixpoint of `taintStep fn` (`taint_fix`): the step only adds tainted slots,
   a list of `nSlots` flags can gain a flag at most `nSlots` times, and `taint` iterates the step
   `nSlots + 1` times. Consequently every `assign` and `call` of `fn` respects the taint: a
   destination slot written from a tainted operand (or by a call with a tainted argument) is
   tainted.
2. An invariant `Inv` of every running state of the unbounded `preJump` run of an accepted
   program: frame identities strictly decrease down the stack and are below `nextFid`, no value
   points into a frame at or above `nextFid`, no frame holds a pointer into a frame above it,
   untainted slots of a frame hold no pointer into that frame, and no frame holds a pointer into a
   frame below it that waits with continuation `thenReturn` or waits for a call whose
   destination slot is untainted. At a `tailCall`, every argument is untainted, so (by the
   invariant) none of its values points into the current frame.
-/

namespace Toy.TailCall.EscapeProof

open Toy.TailCall

set_option linter.unusedSimpArgs false

/-! ### The taint fixpoint -/

/-- Number of set flags among the first `k` entries. -/
def cnt (T : List Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => cnt T k + if T.getD k false then 1 else 0

theorem cnt_le_self (T : List Bool) : ∀ k, cnt T k ≤ k
  | 0 => Nat.le_refl 0
  | k + 1 => by
    have := cnt_le_self T k
    simp only [cnt]
    split <;> omega

theorem cnt_mono {T T' : List Bool} (h : ∀ d, T.getD d false = true → T'.getD d false = true) :
    ∀ k, cnt T k ≤ cnt T' k
  | 0 => Nat.le_refl 0
  | k + 1 => by
    have ih := cnt_mono h k
    simp only [cnt]
    cases h1 : T.getD k false <;> cases h2 : T'.getD k false
    · simp; omega
    · simp; omega
    · have := h k h1; rw [h2] at this; cases this
    · simp; omega

theorem cnt_strict {T T' : List Bool} (h : ∀ d, T.getD d false = true → T'.getD d false = true)
    {d : Nat} (hd1 : T.getD d false = false) (hd2 : T'.getD d false = true) :
    ∀ k, d < k → cnt T k < cnt T' k
  | 0, hk => absurd hk (Nat.not_lt_zero _)
  | k + 1, hk => by
    simp only [cnt]
    by_cases hdk : d = k
    · subst hdk
      have := cnt_mono h d
      rw [hd1, hd2]
      simp
      omega
    · have ih := cnt_strict h hd1 hd2 k (by omega)
      cases h1 : T.getD k false <;> cases h2 : T'.getD k false
      · simp; omega
      · simp; omega
      · have := h k h1; rw [h2] at this; cases this
      · simp; omega

theorem getD_ge {α : Type} {l : List α} {d : Nat} {x : α} (h : l.length ≤ d) : l.getD d x = x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem taintStep_length (fn : Fn) (T : List Bool) : (taintStep fn T).length = fn.nSlots := by
  simp [taintStep]

theorem taintStep_getD (fn : Fn) (T : List Bool) {d : Nat} (hd : d < fn.nSlots) :
    (taintStep fn T).getD d false = (T.getD d false || fn.code.any fun i =>
      match i with
      | .assign d' op _ => d' == d && opTainted T op
      | .call _ args d' _ => d' == d && args.any (opTainted T)
      | _ => false) := by
  simp [taintStep, List.getD_eq_getElem?_getD, hd]
  rfl

/-- The `k`-th iterate of `taintStep` from "nothing tainted". -/
def S (fn : Fn) (k : Nat) : List Bool := Nat.repeat (taintStep fn) k (List.replicate fn.nSlots false)

theorem S_succ (fn : Fn) (k : Nat) : S fn (k + 1) = taintStep fn (S fn k) := rfl

theorem S_length (fn : Fn) : ∀ k, (S fn k).length = fn.nSlots
  | 0 => by simp [S, Nat.repeat]
  | k + 1 => by rw [S_succ, taintStep_length]

theorem S_infl (fn : Fn) (k : Nat) :
    ∀ d, (S fn k).getD d false = true → (S fn (k + 1)).getD d false = true := by
  intro d h
  rcases Nat.lt_or_ge d fn.nSlots with hd | hd
  · rw [S_succ, taintStep_getD fn _ hd, h]
    rfl
  · rw [getD_ge (by rw [S_length]; exact hd)] at h
    cases h

theorem ext_getD {l1 l2 : List Bool} (hl : l1.length = l2.length)
    (h : ∀ d, l1.getD d false = l2.getD d false) : l1 = l2 := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
    using this

theorem S_chain (fn : Fn) :
    ∀ k, (∃ j, j ≤ k ∧ S fn (j + 1) = S fn j) ∨ k ≤ cnt (S fn k) fn.nSlots
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
    rcases S_chain fn k with ⟨j, hj, he⟩ | hc
    · exact Or.inl ⟨j, by omega, he⟩
    · by_cases he : S fn (k + 1) = S fn k
      · exact Or.inl ⟨k, by omega, he⟩
      · right
        have hne : ¬ ∀ d, (S fn (k + 1)).getD d false = (S fn k).getD d false :=
          fun hall => he (ext_getD (by rw [S_length, S_length]) hall)
        rw [Classical.not_forall] at hne
        obtain ⟨d, hd⟩ := hne
        have h1 : (S fn k).getD d false = false := by
          cases h0 : (S fn k).getD d false
          · rfl
          · exact absurd ((S_infl fn k d h0).trans h0.symm) hd
        have h2 : (S fn (k + 1)).getD d false = true := by
          cases h0 : (S fn (k + 1)).getD d false
          · rw [h0, h1] at hd; exact absurd rfl hd
          · rfl
        have hdn : d < fn.nSlots := by
          rcases Nat.lt_or_ge d fn.nSlots with hdn | hdn
          · exact hdn
          · rw [getD_ge (by rw [S_length]; exact hdn)] at h2; cases h2
        have := cnt_strict (S_infl fn k) h1 h2 fn.nSlots hdn
        omega

theorem S_stable (fn : Fn) (j : Nat) (he : S fn (j + 1) = S fn j) : ∀ m, S fn (j + m) = S fn j
  | 0 => rfl
  | m + 1 => by
    rw [← Nat.add_assoc, S_succ, S_stable fn j he m, ← S_succ, he]

/-- `taint fn` is a fixpoint of `taintStep fn`. -/
theorem taint_fix (fn : Fn) : taintStep fn (taint fn) = taint fn := by
  have h : taint fn = S fn (fn.nSlots + 1) := rfl
  rcases S_chain fn (fn.nSlots + 1) with ⟨j, hj, he⟩ | hc
  · have h1 := S_stable fn j he (fn.nSlots + 1 - j)
    have h2 := S_stable fn j he (fn.nSlots + 1 - j + 1)
    rw [show j + (fn.nSlots + 1 - j) = fn.nSlots + 1 by omega] at h1
    rw [show j + (fn.nSlots + 1 - j + 1) = fn.nSlots + 1 + 1 by omega, S_succ] at h2
    rw [h, h2, h1]
  · have := cnt_le_self (S fn (fn.nSlots + 1)) fn.nSlots
    omega

theorem taint_assign {fn : Fn} {d : Slot} {op : Operand} {nx : Nat}
    (hi : Instr.assign d op nx ∈ fn.code) (hd : d < fn.nSlots)
    (ht : opTainted (taint fn) op = true) : (taint fn).getD d false = true := by
  rw [← taint_fix fn, taintStep_getD fn _ hd]
  simp only [Bool.or_eq_true, List.any_eq_true]
  right
  exact ⟨_, hi, by simp [ht]⟩

theorem taint_call {fn : Fn} {g : FnId} {args : List Operand} {d : Slot} {nx : Nat}
    (hi : Instr.call g args d nx ∈ fn.code) (hd : d < fn.nSlots)
    (ht : args.any (opTainted (taint fn)) = true) : (taint fn).getD d false = true := by
  rw [← taint_fix fn, taintStep_getD fn _ hd]
  simp only [Bool.or_eq_true, List.any_eq_true]
  right
  exact ⟨_, hi, by simp [ht]⟩

/-! ### Values and frames -/

/-- No value held by frame `f` (its slots and its pending return value) points into frame `X`. -/
def NoPtr (X : Nat) (f : Frame) : Prop :=
  (∀ v ∈ f.vals, v.pointsInto X = false) ∧ ∀ v, f.pendingRet = some v → v.pointsInto X = false

/-- Frame `b` (below the running frame) waits for a value that cannot point into it: it waits
with continuation `thenReturn` (it was finalized by a tail call), or it waits for a call whose
destination slot is untainted. -/
def Guard (p : Prog) (b : Frame) : Prop :=
  b.cont = .thenReturn ∨
    ∃ dst next fn, b.cont = .store dst next ∧ p.fns[b.fn]? = some fn ∧
      (taint fn).getD dst false = false

/-- Untainted slots of `f` hold no pointer into `f`. -/
def Untainted (p : Prog) (f : Frame) : Prop :=
  ∀ fn, p.fns[f.fn]? = some fn → ∀ s, (taint fn).getD s false = false →
    (f.get s).pointsInto f.fid = false

/-- `f` runs an existing function and has one value per slot of it. -/
def WF (p : Prog) (f : Frame) : Prop := ∃ fn, p.fns[f.fn]? = some fn ∧ f.vals.length = fn.nSlots

/-- The invariant of the running states of the unbounded `preJump` run of an accepted program
(stack listed top first). -/
structure Inv (p : Prog) (st : State) : Prop where
  wf : ∀ f ∈ st.stack, WF p f
  fresh : ∀ f ∈ st.stack, f.fid < st.nextFid ∧ ∀ X, st.nextFid ≤ X → NoPtr X f
  order : st.stack.Pairwise fun a b => b.fid < a.fid
  down : st.stack.Pairwise fun a b => NoPtr a.fid b
  untainted : ∀ f ∈ st.stack, Untainted p f
  guard : st.stack.Pairwise fun a b => Guard p b → NoPtr b.fid a

/-- A value that may be stored in the running frame, which sits on the frames `rest`. -/
def SafeVal (p : Prog) (n : Nat) (rest : List Frame) (v : Val) : Prop :=
  (∀ X, n ≤ X → v.pointsInto X = false) ∧ ∀ b ∈ rest, Guard p b → v.pointsInto b.fid = false

theorem get_cases (f : Frame) (s : Slot) : f.get s ∈ f.vals ∨ f.get s = .undef := by
  unfold Frame.get
  rw [List.getD_eq_getElem?_getD]
  cases h : f.vals[s]? with
  | none => right; rfl
  | some v => left; exact List.mem_of_getElem? h

theorem get_noPtr {f : Frame} {X : Nat} (h : ∀ v ∈ f.vals, v.pointsInto X = false) (s : Slot) :
    (f.get s).pointsInto X = false := by
  rcases get_cases f s with hm | he
  · exact h _ hm
  · rw [he]; rfl

theorem findFrame_some {stk : List Frame} {fid : Nat} {g : Frame}
    (h : findFrame stk fid = some g) : g ∈ stk ∧ g.fid = fid := by
  unfold findFrame at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem findFrame_cons_ne {fr : Frame} {stk : List Frame} {fid : Nat} (h : fr.fid ≠ fid) :
    findFrame (fr :: stk) fid = findFrame stk fid := by
  simp [findFrame, List.find?_cons, h]

/-- Evaluating an operand changes the frame's drop flags at most. -/
theorem evalOp_frame {below : List Frame} {fr : Frame} {o : Operand} {v : Val} {fr' : Frame}
    (h : evalOp below fr o = some (v, fr')) :
    fr'.vals = fr.vals ∧ fr'.fid = fr.fid ∧ fr'.fn = fr.fn ∧ fr'.pc = fr.pc ∧
      fr'.cont = fr.cont ∧ fr'.pendingRet = fr.pendingRet := by
  unfold evalOp at h
  repeat' split at h
  all_goals first
    | (simp at h; done)
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; simp [Frame.kill])

theorem evalOps_frame {below : List Frame} {fr : Frame} {os : List Operand} {vs : List Val}
    {fr' : Frame} (h : evalOps below fr os = some (vs, fr')) :
    fr'.vals = fr.vals ∧ fr'.fid = fr.fid ∧ fr'.fn = fr.fn ∧ fr'.pc = fr.pc ∧
      fr'.cont = fr.cont ∧ fr'.pendingRet = fr.pendingRet := by
  induction os generalizing fr vs with
  | nil => simp [evalOps] at h; obtain ⟨-, rfl⟩ := h; simp
  | cons o os ih =>
    simp only [evalOps] at h
    split at h
    · simp at h
    · rename_i v fr1 h1
      split at h
      · simp at h
      · rename_i vs' fr2 h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        have a := evalOp_frame h1
        have b := ih h2
        exact ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1,
          b.2.2.2.1.trans a.2.2.2.1, b.2.2.2.2.1.trans a.2.2.2.2.1, b.2.2.2.2.2.trans a.2.2.2.2.2⟩

/-- A value computed in the running frame points into `X` only if some frame other than `X`
holds such a pointer, or the running frame is `X` and the operand takes an address. -/
theorem evalOp_noPtr {below : List Frame} {fr : Frame} {o : Operand} {v : Val} {fr' : Frame}
    {X : Nat} (hfr : fr.fid ≠ X)
    (hall : ∀ g ∈ fr :: below, g.fid ≠ X → ∀ w ∈ g.vals, w.pointsInto X = false)
    (h : evalOp below fr o = some (v, fr')) : v.pointsInto X = false := by
  have hfrv := hall fr (List.mem_cons_self ..) hfr
  cases o with
  | const n =>
    simp only [evalOp, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | copy s =>
    simp only [evalOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact get_noPtr hfrv s
    · cases h
  | move s =>
    simp only [evalOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact get_noPtr hfrv s
    · cases h
  | addrOf s =>
    simp only [evalOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; simp [Val.pointsInto, hfr]
    · cases h
  | deref s =>
    simp only [evalOp] at h
    cases hget : fr.get s with
    | ptr fid j =>
      rw [hget] at h
      simp only at h
      cases hg : findFrame (fr :: below) fid with
      | none => rw [hg] at h; cases h
      | some g =>
        rw [hg] at h
        simp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          have ⟨hmem, hgfid⟩ := findFrame_some hg
          have hfid : fid ≠ X := by
            have := get_noPtr hfrv s
            rw [hget] at this
            simpa [Val.pointsInto] using this
          exact get_noPtr (hall g hmem (by rw [hgfid]; exact hfid)) j
        · cases h
    | int n => rw [hget] at h; cases h
    | undef => rw [hget] at h; cases h
  | succ s =>
    simp only [evalOp] at h
    cases hget : fr.get s with
    | int n =>
      rw [hget] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; rfl
    | ptr fid j => rw [hget] at h; cases h
    | undef => rw [hget] at h; cases h

theorem evalOps_noPtr {below : List Frame} {fr : Frame} {os : List Operand} {vs : List Val}
    {fr' : Frame} {X : Nat} (hfr : fr.fid ≠ X)
    (hall : ∀ g ∈ fr :: below, g.fid ≠ X → ∀ w ∈ g.vals, w.pointsInto X = false)
    (h : evalOps below fr os = some (vs, fr')) : ∀ v ∈ vs, v.pointsInto X = false := by
  induction os generalizing fr vs fr' with
  | nil => simp [evalOps] at h; obtain ⟨rfl, -⟩ := h; simp
  | cons o os ih =>
    simp only [evalOps] at h
    split at h
    · simp at h
    · rename_i v fr1 h1
      split at h
      · simp at h
      · rename_i vs' fr2 h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have hf := evalOp_frame h1
        have hall1 : ∀ g ∈ fr1 :: below, g.fid ≠ X → ∀ w ∈ g.vals, w.pointsInto X = false := by
          intro g hg
          rcases List.mem_cons.mp hg with rfl | hg
          · rw [hf.1, hf.2.1]; exact hall fr (List.mem_cons_self ..)
          · exact hall g (List.mem_cons_of_mem _ hg)
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact evalOp_noPtr hfr hall h1
        · exact ih (by rw [hf.2.1]; exact hfr) hall1 h2 w hw

/-- An untainted operand evaluated in the running frame never yields a pointer into it. -/
theorem evalOp_untainted {below : List Frame} {fr : Frame} {o : Operand} {v : Val} {fr' : Frame}
    {T : List Bool} (hT : ∀ s, T.getD s false = false → (fr.get s).pointsInto fr.fid = false)
    (hbelow : ∀ g ∈ below, ∀ w ∈ g.vals, w.pointsInto fr.fid = false)
    (ho : opTainted T o = false) (h : evalOp below fr o = some (v, fr')) :
    v.pointsInto fr.fid = false := by
  cases o with
  | const n =>
    simp only [evalOp, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | copy s =>
    simp only [evalOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact hT s ho
    · cases h
  | move s =>
    simp only [evalOp] at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; exact hT s ho
    · cases h
  | addrOf s => simp [opTainted] at ho
  | deref s =>
    have hs := hT s ho
    simp only [evalOp] at h
    cases hget : fr.get s with
    | ptr fid j =>
      rw [hget] at h hs
      simp only at h
      have hne : fr.fid ≠ fid := by
        intro he; simp [Val.pointsInto, he] at hs
      rw [findFrame_cons_ne hne] at h
      cases hg : findFrame below fid with
      | none => rw [hg] at h; cases h
      | some g =>
        rw [hg] at h
        simp only at h
        split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.1]
          exact get_noPtr (hbelow g (findFrame_some hg).1) j
        · cases h
    | int n => rw [hget] at h; cases h
    | undef => rw [hget] at h; cases h
  | succ s =>
    simp only [evalOp] at h
    cases hget : fr.get s with
    | int n =>
      rw [hget] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1]; rfl
    | ptr fid j => rw [hget] at h; cases h
    | undef => rw [hget] at h; cases h

theorem evalOps_untainted {below : List Frame} {fr : Frame} {os : List Operand} {vs : List Val}
    {fr' : Frame} {T : List Bool}
    (hT : ∀ s, T.getD s false = false → (fr.get s).pointsInto fr.fid = false)
    (hbelow : ∀ g ∈ below, ∀ w ∈ g.vals, w.pointsInto fr.fid = false)
    (hos : os.any (opTainted T) = false) (h : evalOps below fr os = some (vs, fr')) :
    ∀ v ∈ vs, v.pointsInto fr.fid = false := by
  induction os generalizing fr vs fr' with
  | nil => simp [evalOps] at h; obtain ⟨rfl, -⟩ := h; simp
  | cons o os ih =>
    simp only [List.any_cons, Bool.or_eq_false_iff] at hos
    simp only [evalOps] at h
    split at h
    · simp at h
    · rename_i v fr1 h1
      split at h
      · simp at h
      · rename_i vs' fr2 h2
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        have hf := evalOp_frame h1
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact evalOp_untainted hT hbelow hos.1 h1
        · have := ih (fr := fr1) (by intro s hs; unfold Frame.get; rw [hf.1, hf.2.1]; exact hT s hs)
            (by rw [hf.2.1]; exact hbelow) hos.2 h2 w hw
          rw [hf.2.1] at this; exact this

/-! ### Frame updates -/

theorem write_vals (f : Frame) (d : Slot) (v w : Val) (h : w ∈ (f.write d v).vals) :
    w ∈ f.vals ∨ w = v :=
  List.mem_or_eq_of_mem_set h

theorem write_get (f : Frame) (d : Slot) (v : Val) (s : Slot) :
    (f.write d v).get s = f.get s ∨ (s = d ∧ (f.write d v).get s = v) := by
  unfold Frame.write Frame.get
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hds : d = s
  · subst hds
    by_cases hl : d < f.vals.length
    · right; simp [hl]
    · left; simp [hl, List.getElem?_eq_none (Nat.le_of_not_lt hl)]
  · left; simp [hds]

theorem clear_vals (f : Frame) (d : Slot) (w : Val) (h : w ∈ (f.clear d).vals) :
    w ∈ f.vals ∨ w = .undef :=
  List.mem_or_eq_of_mem_set h

theorem clear_get (f : Frame) (d : Slot) (s : Slot) :
    (f.clear d).get s = f.get s ∨ (f.clear d).get s = .undef := by
  have := write_get f d .undef s
  unfold Frame.write at this
  unfold Frame.clear
  rcases this with h | ⟨-, h⟩
  · left; exact h
  · right; exact h

theorem foldl_clear_frame (ss : List Slot) (fr : Frame) :
    (ss.foldl Frame.clear fr).fid = fr.fid ∧ (ss.foldl Frame.clear fr).fn = fr.fn ∧
      (ss.foldl Frame.clear fr).vals.length = fr.vals.length ∧
      (ss.foldl Frame.clear fr).pendingRet = fr.pendingRet ∧
      (∀ w ∈ (ss.foldl Frame.clear fr).vals, w ∈ fr.vals ∨ w = .undef) ∧
      (∀ s, (ss.foldl Frame.clear fr).get s = fr.get s ∨
        (ss.foldl Frame.clear fr).get s = .undef) := by
  induction ss generalizing fr with
  | nil => exact ⟨rfl, rfl, rfl, rfl, fun w hw => Or.inl hw, fun s => Or.inl rfl⟩
  | cons d ss ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ih (fr.clear d)
    refine ⟨by rw [h1]; rfl, by rw [h2]; rfl, by rw [h3]; simp [Frame.clear], by rw [h4]; rfl,
      fun w hw => ?_, fun s => ?_⟩
    · rcases h5 w hw with hw | hw
      · exact clear_vals fr d w hw
      · exact Or.inr hw
    · rcases h6 s with hs | hs
      · rw [hs]; exact clear_get fr d s
      · exact Or.inr hs

theorem dropList_frame (fn : Fn) (fr : Frame) (ss : List Slot) (unw : Bool) :
    (dropList fn fr ss unw).1.vals = fr.vals ∧ (dropList fn fr ss unw).1.fid = fr.fid ∧
      (dropList fn fr ss unw).1.fn = fr.fn ∧
      (dropList fn fr ss unw).1.pendingRet = fr.pendingRet := by
  induction ss generalizing fr unw with
  | nil => simp [dropList]
  | cons s ss ih =>
    simp only [dropList]
    split
    · split
      · simp [Frame.kill]
      · have := ih (fr.kill s) true; simpa [Frame.kill] using this
    · have := ih (fr.kill s) unw; simpa [Frame.kill] using this

/-! ### Preservation of the invariant -/

theorem pairwise_split {R : Frame → Frame → Prop} {l1 l2 : List Frame} {b : Frame}
    (h : (l1 ++ b :: l2).Pairwise R) : (∀ a ∈ l1, R a b) ∧ (∀ c ∈ l2, R b c) := by
  rw [List.pairwise_append, List.pairwise_cons] at h
  exact ⟨fun a ha => h.2.2 a ha b (List.mem_cons_self ..), h.2.1.1⟩

theorem inv_congr {p : Prog} {st st' : State} (hinv : Inv p st) (hs : st'.stack = st.stack)
    (hn : st'.nextFid = st.nextFid) : Inv p st' := by
  obtain ⟨a, b, c, d, e, f⟩ := hinv
  exact ⟨by rw [hs]; exact a, by rw [hs, hn]; exact b, by rw [hs]; exact c, by rw [hs]; exact d,
    by rw [hs]; exact e, by rw [hs]; exact f⟩

theorem inv_pop {p : Prog} {st st' : State} {fr : Frame} {rest : List Frame} (hinv : Inv p st)
    (hs : st.stack = fr :: rest) (hs' : st'.stack = rest) (hn : st'.nextFid = st.nextFid) :
    Inv p st' := by
  have hsub : ∀ f ∈ st'.stack, f ∈ st.stack := by
    intro f hf; rw [hs'] at hf; rw [hs]; exact List.mem_cons_of_mem _ hf
  have o := hinv.order; have d := hinv.down; have g := hinv.guard
  rw [hs, List.pairwise_cons] at o d g
  exact ⟨fun f hf => hinv.wf f (hsub f hf), fun f hf => by rw [hn]; exact hinv.fresh f (hsub f hf),
    by rw [hs']; exact o.2, by rw [hs']; exact d.2, fun f hf => hinv.untainted f (hsub f hf),
    by rw [hs']; exact g.2⟩

theorem inv_top {p : Prog} {st st' : State} {fr fr' : Frame} {rest : List Frame}
    (hinv : Inv p st) (hs : st.stack = fr :: rest) (hs' : st'.stack = fr' :: rest)
    (hn : st'.nextFid = st.nextFid) (hfid : fr'.fid = fr.fid) (hfn : fr'.fn = fr.fn)
    (hlen : fr'.vals.length = fr.vals.length)
    (hvals : ∀ v ∈ fr'.vals, v ∈ fr.vals ∨ SafeVal p st.nextFid rest v)
    (hret : ∀ v, fr'.pendingRet = some v → fr.pendingRet = some v ∨ SafeVal p st.nextFid rest v)
    (hunt : Untainted p fr') : Inv p st' := by
  have o := hinv.order; have d := hinv.down; have g := hinv.guard
  rw [hs, List.pairwise_cons] at o d g
  have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
  have hrest : ∀ f ∈ rest, f ∈ st.stack := by
    intro f hf; rw [hs]; exact List.mem_cons_of_mem _ hf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f hf; rw [hs'] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · obtain ⟨fn, hfn', hl⟩ := hinv.wf fr hfr
      exact ⟨fn, by rw [hfn]; exact hfn', by rw [hlen]; exact hl⟩
    · exact hinv.wf f (hrest f hf)
  · intro f hf; rw [hs'] at hf; rw [hn]
    rcases List.mem_cons.mp hf with rfl | hf
    · obtain ⟨h1, h2⟩ := hinv.fresh fr hfr
      refine ⟨by rw [hfid]; exact h1, fun X hX => ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
      · rcases hvals v hv with hv | hv
        · exact (h2 X hX).1 v hv
        · exact hv.1 X hX
      · rcases hret v hv with hv | hv
        · exact (h2 X hX).2 v hv
        · exact hv.1 X hX
    · exact hinv.fresh f (hrest f hf)
  · rw [hs', List.pairwise_cons]; exact ⟨fun b hb => by rw [hfid]; exact o.1 b hb, o.2⟩
  · rw [hs', List.pairwise_cons]; exact ⟨fun b hb => by rw [hfid]; exact d.1 b hb, d.2⟩
  · intro f hf; rw [hs'] at hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hunt
    · exact hinv.untainted f (hrest f hf)
  · rw [hs', List.pairwise_cons]
    refine ⟨fun b hb hgb => ⟨fun v hv => ?_, fun v hv => ?_⟩, g.2⟩
    · rcases hvals v hv with hv | hv
      · exact (g.1 b hb hgb).1 v hv
      · exact hv.2 b hb hgb
    · rcases hret v hv with hv | hv
      · exact (g.1 b hb hgb).2 v hv
      · exact hv.2 b hb hgb

theorem untainted_congr {p : Prog} {f f' : Frame} (h : Untainted p f) (hv : f'.vals = f.vals)
    (hfid : f'.fid = f.fid) (hfn : f'.fn = f.fn) : Untainted p f' := by
  intro fn hfn' s hs
  have := h fn (by rw [← hfn]; exact hfn') s hs
  unfold Frame.get at this ⊢
  rw [hv, hfid]; exact this

/-- The running frame changes only in its drop flags, `pc` or continuation. -/
theorem inv_top_same {p : Prog} {st st' : State} {fr fr' : Frame} {rest : List Frame}
    (hinv : Inv p st) (hs : st.stack = fr :: rest) (hs' : st'.stack = fr' :: rest)
    (hn : st'.nextFid = st.nextFid) (hv : fr'.vals = fr.vals) (hfid : fr'.fid = fr.fid)
    (hfn : fr'.fn = fr.fn) (hret : fr'.pendingRet = fr.pendingRet) : Inv p st' := by
  have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
  exact inv_top hinv hs hs' hn hfid hfn (by rw [hv]) (fun v h => Or.inl (by rw [← hv]; exact h))
    (fun v h => Or.inl (by rw [← hret]; exact h)) (untainted_congr (hinv.untainted fr hfr) hv hfid hfn)

theorem hall_fresh {p : Prog} {st : State} {fr : Frame} {rest : List Frame} (hinv : Inv p st)
    (hs : st.stack = fr :: rest) {X : Nat} (hX : st.nextFid ≤ X) :
    fr.fid ≠ X ∧ ∀ g ∈ fr :: rest, g.fid ≠ X → ∀ w ∈ g.vals, w.pointsInto X = false := by
  have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
  refine ⟨by have := (hinv.fresh fr hfr).1; omega, fun g hg _ => ?_⟩
  rw [← hs] at hg
  exact ((hinv.fresh g hg).2 X hX).1

theorem hall_guard {p : Prog} {st : State} {fr : Frame} {rest : List Frame} (hinv : Inv p st)
    (hs : st.stack = fr :: rest) {b : Frame} (hb : b ∈ rest) (hgb : Guard p b) :
    fr.fid ≠ b.fid ∧ ∀ g ∈ fr :: rest, g.fid ≠ b.fid → ∀ w ∈ g.vals, w.pointsInto b.fid = false := by
  obtain ⟨l1, l2, hl⟩ := List.append_of_mem hb
  have hst : st.stack = (fr :: l1) ++ b :: l2 := by rw [hs, hl]; rfl
  have o := hinv.order; have d := hinv.down; have g := hinv.guard
  rw [hst] at o d g
  have ho := pairwise_split o; have hd := pairwise_split d; have hg := pairwise_split g
  refine ⟨by have := ho.1 fr (List.mem_cons_self ..); omega, fun x hx hne => ?_⟩
  have hx' : x ∈ (fr :: l1) ++ b :: l2 := by rw [← hst, hs]; exact hx
  rcases List.mem_append.mp hx' with hx1 | hx2
  · exact (hg.1 x hx1 hgb).1
  · rcases List.mem_cons.mp hx2 with rfl | hx2
    · exact absurd rfl hne
    · exact (hd.2 x hx2).1

theorem safe_eval {p : Prog} {st : State} {fr : Frame} {rest : List Frame} (hinv : Inv p st)
    (hs : st.stack = fr :: rest) {o : Operand} {v : Val} {fr1 : Frame}
    (h : evalOp rest fr o = some (v, fr1)) : SafeVal p st.nextFid rest v :=
  ⟨fun _ hX => evalOp_noPtr (hall_fresh hinv hs hX).1 (hall_fresh hinv hs hX).2 h,
    fun _ hb hgb => evalOp_noPtr (hall_guard hinv hs hb hgb).1 (hall_guard hinv hs hb hgb).2 h⟩

theorem safe_evals {p : Prog} {st : State} {fr : Frame} {rest : List Frame} (hinv : Inv p st)
    (hs : st.stack = fr :: rest) {os : List Operand} {vs : List Val} {fr1 : Frame}
    (h : evalOps rest fr os = some (vs, fr1)) : ∀ v ∈ vs, SafeVal p st.nextFid rest v :=
  fun v hv =>
    ⟨fun _ hX => evalOps_noPtr (hall_fresh hinv hs hX).1 (hall_fresh hinv hs hX).2 h v hv,
      fun _ hb hgb => evalOps_noPtr (hall_guard hinv hs hb hgb).1 (hall_guard hinv hs hb hgb).2 h v hv⟩

theorem safe_ret {p : Prog} {st : State} {fr : Frame} {rest : List Frame} (hinv : Inv p st)
    (hs : st.stack = fr :: rest) {v : Val} (h : fr.pendingRet = some v) :
    SafeVal p st.nextFid rest v := by
  have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
  have g := hinv.guard
  rw [hs, List.pairwise_cons] at g
  exact ⟨fun X hX => ((hinv.fresh fr hfr).2 X hX).2 v h, fun b hb hgb => (g.1 b hb hgb).2 v h⟩

theorem inv_push {p : Prog} {st st1 st' : State} {fr c : Frame} {rest : List Frame} {f : FnId}
    {vs : List Val} (hinv : Inv p st) (hs : st.stack = fr :: rest) (hn : st1.nextFid = st.nextFid)
    (hfid : c.fid = fr.fid) (hfn : c.fn = fr.fn) (hvals : c.vals = fr.vals)
    (hret : c.pendingRet = fr.pendingRet)
    (hsafe : ∀ v ∈ vs, SafeVal p st.nextFid rest v)
    (hg : Guard p c → ∀ v ∈ vs, v.pointsInto c.fid = false)
    (h : push none p st1 (c :: rest) f vs = .running st') : Inv p st' := by
  obtain ⟨stk1, n1, ev1, md1, tc1, uw1⟩ := st1
  simp only at hn
  subst hn
  unfold push at h
  cases hf : p.fns[f]? with
  | none => rw [hf] at h; simp [State.halt] at h
  | some fn =>
    rw [hf] at h
    simp only at h
    split at h
    · simp [State.halt] at h
    · rename_i hok
      simp only [overflows, Bool.false_eq_true, ↓reduceIte, Conf.running.injEq] at h
      subst h
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
        Classical.not_not, Nat.not_lt] at hok
      obtain ⟨hlenp, hle⟩ := hok
      have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
      have hrest : ∀ x ∈ rest, x ∈ st.stack := by
        intro x hx; rw [hs]; exact List.mem_cons_of_mem _ hx
      have o := hinv.order; have d := hinv.down; have g := hinv.guard
      rw [hs, List.pairwise_cons] at o d g
      have hcfresh := hinv.fresh fr hfr
      have hnew : ∀ w ∈ vs ++ List.replicate (fn.nSlots - fn.nParams) Val.undef,
          w ∈ vs ∨ w = .undef := by
        intro w hw
        rcases List.mem_append.mp hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (List.eq_of_mem_replicate hw)
      have hnoc : ∀ X, NoPtr X fr → NoPtr X c := fun X ⟨h1, h2⟩ =>
        ⟨by rw [hvals]; exact h1, by rw [hret]; exact h2⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · exact ⟨fn, hf, by simp [hlenp]; omega⟩
        · obtain ⟨fn', h1, h2⟩ := hinv.wf fr hfr
          exact ⟨fn', by rw [hfn]; exact h1, by rw [hvals]; exact h2⟩
        · exact hinv.wf x (hrest x hx)
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · refine ⟨by simp, fun X hX => ⟨fun w hw => ?_, fun w hw => by simp at hw⟩⟩
          rcases hnew w hw with hw | rfl
          · exact (hsafe w hw).1 X (by omega)
          · rfl
        · refine ⟨by rw [hfid]; omega, fun X hX => hnoc X (hcfresh.2 X (by omega))⟩
        · have := hinv.fresh x (hrest x hx)
          exact ⟨by omega, fun X hX => this.2 X (by omega)⟩
      · simp only [List.pairwise_cons, List.mem_cons]
        refine ⟨?_, ⟨fun b hb => by rw [hfid]; exact o.1 b hb, o.2⟩⟩
        intro b hb
        rcases hb with rfl | hb
        · rw [hfid]; exact hcfresh.1
        · exact (hinv.fresh b (hrest b hb)).1
      · simp only [List.pairwise_cons, List.mem_cons]
        refine ⟨?_, ⟨fun b hb => by rw [hfid]; exact d.1 b hb, d.2⟩⟩
        intro b hb
        rcases hb with rfl | hb
        · exact hnoc _ (hcfresh.2 _ (Nat.le_refl _))
        · exact (hinv.fresh b (hrest b hb)).2 _ (Nat.le_refl _)
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | hx
        · intro fn' _ s _
          refine get_noPtr (fun w hw => ?_) s
          rcases hnew w hw with hm | rfl
          · exact (hsafe _ hm).1 _ (Nat.le_refl _)
          · rfl
        · exact untainted_congr (hinv.untainted fr hfr) hvals hfid hfn
        · exact hinv.untainted x (hrest x hx)
      · simp only [List.pairwise_cons, List.mem_cons]
        refine ⟨?_, ⟨fun b hb hgb => hnoc _ (g.1 b hb hgb), g.2⟩⟩
        intro b hb hgb
        refine ⟨fun w hw => ?_, fun w hw => by simp at hw⟩
        rcases hnew w hw with hw | rfl
        · rcases hb with rfl | hb
          · exact hg hgb w hw
          · exact (hsafe w hw).2 b hb hgb
        · rfl

theorem inv_deliver {p : Prog} {st st1 st' : State} {fr : Frame} {rest : List Frame} {v : Val}
    (hinv : Inv p st) (hs : st.stack = fr :: rest) (hn : st1.nextFid = st.nextFid)
    (hv : SafeVal p st.nextFid rest v) (h : deliver st1 rest v = .running st') : Inv p st' := by
  have hpop : Inv p { st with stack := rest } := inv_pop hinv hs rfl rfl
  cases rest with
  | nil => simp [deliver, State.halt] at h
  | cons g rest' =>
    have hgm : g ∈ { st with stack := g :: rest' }.stack := List.mem_cons_self ..
    have hv' : SafeVal p st.nextFid rest' v :=
      ⟨hv.1, fun b hb hgb => hv.2 b (List.mem_cons_of_mem _ hb) hgb⟩
    simp only [deliver] at h
    split at h
    · rename_i dst next hc
      simp only [Conf.running.injEq] at h
      subst h
      refine inv_top hpop rfl rfl hn rfl rfl (by simp [Frame.write])
        (fun w hw => ?_) (fun w hw => Or.inl hw) ?_
      · rcases write_vals g dst v w hw with hw | rfl
        · exact Or.inl hw
        · exact Or.inr hv'
      · intro fn hfn s hs
        have hget : ({ g.write dst v with pc := next } : Frame).get s = (g.write dst v).get s := rfl
        rw [hget]
        rcases write_get g dst v s with he | ⟨rfl, he⟩
        · rw [he]; exact hpop.untainted g hgm fn hfn s hs
        · rw [he]
          exact hv.2 g (List.mem_cons_self ..) (Or.inr ⟨s, next, fn, hc, hfn, hs⟩)
    · rename_i hc
      simp only [Conf.running.injEq] at h
      subst h
      refine inv_top hpop rfl rfl hn rfl rfl rfl (fun w hw => Or.inl hw) ?_
        (untainted_congr (hpop.untainted g hgm) rfl rfl rfl)
      intro w hw
      simp only [Option.some.injEq] at hw
      subst hw
      exact Or.inr hv'

theorem inv_doReturn {p : Prog} {st st' : State} {fr fr1 : Frame} {rest : List Frame} {fn : Fn}
    {v : Val} (hinv : Inv p st) (hs : st.stack = fr :: rest) (hv : SafeVal p st.nextFid rest v)
    (h : doReturn st fn fr1 rest v = .running st') : Inv p st' := by
  dsimp only [doReturn] at h
  split at h
  · exact inv_deliver hinv hs (by rfl) hv h
  · unfold unwindBelow at h
    split at h
    · simp [State.halt] at h
    · simp only [Conf.running.injEq] at h
      subst h
      exact inv_pop hinv hs rfl rfl
  · simp [State.halt] at h

theorem bumpTail_running {c : Conf} {st' : State} (h : bumpTail c = .running st') :
    ∃ st'', c = .running st'' ∧ st'.stack = st''.stack ∧ st'.nextFid = st''.nextFid := by
  cases c with
  | running s =>
    simp only [bumpTail, Conf.running.injEq] at h
    subst h
    exact ⟨s, rfl, rfl, rfl⟩
  | halted r => simp [bumpTail] at h

/-- One step of the unbounded `preJump` machine preserves the invariant. -/
theorem inv_step {p : Prog} (hacc : EscapeCheckAccepts p = true) {st st' : State}
    (hinv : Inv p st) (h : step .preJump none p st = .running st') : Inv p st' := by
  cases hs : st.stack with
  | nil => simp [step, hs, State.halt] at h
  | cons fr rest =>
    have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
    cases hfn : p.fns[fr.fn]? with
    | none => simp [step, hs, hfn, State.halt] at h
    | some fn =>
    have hlen : fr.vals.length = fn.nSlots := by
      obtain ⟨fn0, hfn0, hl⟩ := hinv.wf fr hfr
      rw [hfn] at hfn0
      cases hfn0
      exact hl
    have hunt := hinv.untainted fr hfr fn hfn
    have hbelow : ∀ g ∈ rest, ∀ w ∈ g.vals, w.pointsInto fr.fid = false := by
      have d := hinv.down
      rw [hs, List.pairwise_cons] at d
      exact fun g hg => (d.1 g hg).1
    have hacc_fn : EscapeCheckFn fn = true := by
      simp only [EscapeCheckAccepts, List.all_eq_true] at hacc
      exact hacc fn (List.mem_of_getElem? hfn)
    have hfnEq : ∀ fn', p.fns[fr.fn]? = some fn' → fn' = fn := by
      intro fn' h1; rw [hfn] at h1; exact (Option.some.inj h1).symm
    simp only [step, hs, hfn] at h
    by_cases hu : st.unwinding = true
    · simp only [hu, ↓reduceIte] at h
      try dsimp only at h
      split at h
      · simp [State.halt] at h
      · split at h
        · simp [State.halt] at h
        · simp only [Conf.running.injEq] at h
          subst h
          exact inv_pop hinv hs rfl rfl
    · simp only [hu, Bool.false_eq_true, ↓reduceIte] at h
      cases hret : fr.pendingRet with
      | some v =>
        rw [hret] at h
        simp only at h
        exact inv_doReturn hinv hs (safe_ret hinv hs hret) h
      | none =>
        rw [hret] at h
        simp only at h
        cases hcode : fn.code[fr.pc]? with
        | none => rw [hcode] at h; simp [State.halt] at h
        | some i =>
          rw [hcode] at h
          simp only at h
          have hmem : i ∈ fn.code := List.mem_of_getElem? hcode
          cases i with
          | assign dst op next =>
            simp only at h
            cases hev : evalOp rest fr op with
            | none => rw [hev] at h; simp [State.halt] at h
            | some vf =>
              obtain ⟨v, fr1⟩ := vf
              rw [hev] at h
              simp only at h
              have hf := evalOp_frame hev
              split at h
              · rename_i hdst
                simp only [Conf.running.injEq] at h
                subst h
                refine inv_top hinv hs rfl rfl (by simp [Frame.write, hf.2.1])
                  (by simp [Frame.write, hf.2.2.1]) (by simp [Frame.write, hf.1])
                  (fun w hw => ?_) (fun w hw => ?_) ?_
                · rcases write_vals fr1 dst v w hw with hw | rfl
                  · left; rw [← hf.1]; exact hw
                  · right; exact safe_eval hinv hs hev
                · left; rw [← hf.2.2.2.2.2]; exact hw
                · intro fn' hfn' s hs'
                  have e3 : fn' = fn := hfnEq fn' (by rw [← hf.2.2.1]; exact hfn')
                  rw [e3] at hs'
                  show ((fr1.write dst v).get s).pointsInto fr1.fid = false
                  rw [hf.2.1]
                  rcases write_get fr1 dst v s with he | ⟨rfl, he⟩
                  · rw [he]; unfold Frame.get; rw [hf.1]; exact hunt s hs'
                  · rw [he]
                    have hop : opTainted (taint fn) op = false := by
                      cases hot : opTainted (taint fn) op
                      · rfl
                      · have := taint_assign hmem (by rw [← hlen, ← hf.1]; exact hdst) hot
                        rw [hs'] at this
                        cases this
                    exact evalOp_untainted hunt hbelow hop hev
              · simp [State.halt] at h
          | emit k next =>
            simp only [Conf.running.injEq] at h
            subst h
            exact inv_top_same hinv hs rfl rfl rfl rfl rfl (by simp [hret])
          | branchLt s0 k t e =>
            simp only at h
            cases hget : fr.get s0 with
            | int n =>
              rw [hget] at h
              simp only [Conf.running.injEq] at h
              subst h
              exact inv_top_same hinv hs rfl rfl rfl rfl rfl (by simp [hret])
            | ptr a b => rw [hget] at h; simp [State.halt] at h
            | undef => rw [hget] at h; simp [State.halt] at h
          | goto next =>
            simp only [Conf.running.injEq] at h
            subst h
            exact inv_top_same hinv hs rfl rfl rfl rfl rfl (by simp [hret])
          | reset ss next =>
            simp only [Conf.running.injEq] at h
            subst h
            obtain ⟨h1, h2, h3, h4, h5, h6⟩ := foldl_clear_frame ss fr
            refine inv_top hinv hs rfl rfl h1 h2 h3 (fun w hw => ?_)
              (fun w hw => Or.inl (by rw [← h4]; exact hw)) ?_
            · rcases h5 w hw with hw | rfl
              · exact Or.inl hw
              · exact Or.inr ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
            · intro fn' hfn' s hs'
              have e3 : fn' = fn := hfnEq fn' (by rw [← h2]; exact hfn')
              rw [e3] at hs'
              show ((ss.foldl Frame.clear fr).get s).pointsInto (ss.foldl Frame.clear fr).fid = false
              rw [h1]
              rcases h6 s with he | he
              · rw [he]; exact hunt s hs'
              · rw [he]; rfl
          | dropSlots ss next =>
            dsimp only at h
            obtain ⟨d1, d2, d3, d4⟩ :=
              dropList_frame fn fr (ss.filter (fun s => fr.isLive s && fn.dtor s != .none)) false
            split at h
            · simp only [Conf.running.injEq] at h
              subst h
              exact inv_top_same hinv hs rfl rfl d1 d2 d3 d4
            · simp only [Conf.running.injEq] at h
              subst h
              exact inv_top_same hinv hs rfl rfl d1 d2 d3 d4
            · simp [State.halt] at h
          | call g args dst next =>
            simp only at h
            cases hev : evalOps rest fr args with
            | none => rw [hev] at h; simp [State.halt] at h
            | some vf =>
              obtain ⟨vs, fr1⟩ := vf
              rw [hev] at h
              simp only at h
              have hf := evalOps_frame hev
              split at h
              · rename_i hdst
                refine inv_push (c := { fr1 with cont := .store dst next }) hinv hs (by rfl)
                  hf.2.1 hf.2.2.1 hf.1 hf.2.2.2.2.2 (safe_evals hinv hs hev) ?_ h
                rintro (hc | ⟨dst', next', fn', hc, hfn', hT⟩)
                · simp at hc
                · simp only [Cont.store.injEq] at hc
                  have e3 : fn' = fn := hfnEq fn' (by rw [← hf.2.2.1]; exact hfn')
                  rw [e3, ← hc.1] at hT
                  have hargs : args.any (opTainted (taint fn)) = false := by
                    cases ha : args.any (opTainted (taint fn))
                    · rfl
                    · have := taint_call hmem (by rw [← hlen, ← hf.1]; exact hdst) ha
                      rw [hT] at this
                      cases this
                  intro w hw
                  have := evalOps_untainted hunt hbelow hargs hev w hw
                  show w.pointsInto fr1.fid = false
                  rw [hf.2.1]; exact this
              · simp [State.halt] at h
          | ret op =>
            simp only at h
            cases hev : evalOp rest fr op with
            | none => rw [hev] at h; simp [State.halt] at h
            | some vf =>
              obtain ⟨v, fr1⟩ := vf
              rw [hev] at h
              simp only at h
              exact inv_doReturn hinv hs (safe_eval hinv hs hev) h
          | tailCall g args =>
            simp only at h
            cases hev : evalOps rest fr args with
            | none => rw [hev] at h; simp [State.halt] at h
            | some vf =>
              obtain ⟨vs, fr1⟩ := vf
              rw [hev] at h
              simp only at h
              have hf := evalOps_frame hev
              have hargs : args.any (opTainted (taint fn)) = false := by
                simp only [EscapeCheckFn, List.all_eq_true] at hacc_fn
                have := hacc_fn _ hmem
                cases ha : args.any (opTainted (taint fn))
                · rfl
                · simp [ha] at this
              dsimp only [doTailCall] at h
              obtain ⟨d1, d2, d3, d4⟩ := dropList_frame fn fr1 (pendingDrops fn fr1) false
              split at h
              · obtain ⟨st'', hp, hs1, hn1⟩ := bumpTail_running h
                refine inv_congr ?_ hs1 hn1
                refine inv_push
                  (c := { (dropList fn fr1 (pendingDrops fn fr1) false).1 with cont := .thenReturn })
                  hinv hs (by rfl) (d2.trans hf.2.1) (d3.trans hf.2.2.1) (d1.trans hf.1)
                  (d4.trans hf.2.2.2.2.2) (safe_evals hinv hs hev) ?_ hp
                intro _ w hw
                have := evalOps_untainted hunt hbelow hargs hev w hw
                show w.pointsInto (dropList fn fr1 (pendingDrops fn fr1) false).1.fid = false
                rw [d2, hf.2.1]; exact this
              · unfold unwindBelow at h
                split at h
                · simp [State.halt] at h
                · simp only [Conf.running.injEq] at h
                  subst h
                  exact inv_pop hinv hs rfl rfl
              · simp [State.halt] at h
          | panic =>
            simp only [Conf.running.injEq] at h
            subst h
            exact inv_congr hinv hs.symm rfl

/-- The initial state satisfies the invariant. -/
theorem inv_start (p : Prog) (st : State) (h : start none p = .running st) : Inv p st := by
  unfold start push at h
  cases hf : p.fns[0]? with
  | none => rw [hf] at h; simp [State.halt] at h
  | some fn =>
    rw [hf] at h
    simp only at h
    split at h
    · simp [State.halt] at h
    · rename_i hok
      simp only [overflows, Bool.false_eq_true, ↓reduceIte, Conf.running.injEq] at h
      subst h
      simp only [List.length_nil, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, not_or,
        Classical.not_not, Nat.not_lt] at hok
      obtain ⟨h0, hle⟩ := hok
      have hv : ∀ w ∈ ([] : List Val) ++ List.replicate (fn.nSlots - fn.nParams) Val.undef,
          w = .undef := by
        intro w hw
        rw [List.nil_append] at hw
        exact List.eq_of_mem_replicate hw
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try dsimp only
      · intro f hf'
        rw [List.mem_singleton] at hf'
        subst hf'
        exact ⟨fn, hf, by simp; omega⟩
      · intro f hf'
        rw [List.mem_singleton] at hf'
        subst hf'
        refine ⟨by simp [State.empty], fun X _ => ⟨fun w hw => by rw [hv w hw]; rfl,
          fun w hw => by simp at hw⟩⟩
      · exact List.pairwise_singleton _ _
      · exact List.pairwise_singleton _ _
      · intro f hf'
        rw [List.mem_singleton] at hf'
        subst hf'
        intro fn' _ s _
        exact get_noPtr (fun w hw => by rw [hv w hw]; rfl) s
      · exact List.pairwise_singleton _ _

theorem inv_run (p : Prog) (hacc : EscapeCheckAccepts p = true) :
    ∀ (n : Nat) (c : Conf) (st : State), (∀ s, c = .running s → Inv p s) →
      run .preJump none p n c = .running st → Inv p st
  | 0, c, st, hc, h => hc st h
  | n + 1, .halted r, st, _, h => by rw [run_halted] at h; cases h
  | n + 1, .running s, st, hc, h =>
    inv_run p hacc n _ st (fun s' hs' => inv_step hacc (hc s rfl) hs') h

/-- Soundness of the escape check. -/
theorem noStackBorrow (p : Prog) (hacc : EscapeCheckAccepts p = true) : NoStackBorrow p := by
  intro n st hrun
  have hinv := inv_run p hacc n (start none p) st (fun s hs => inv_start p s hs) hrun
  unfold tailCallBorrowsFrame
  cases hs : st.stack with
  | nil => rfl
  | cons fr rest =>
    simp only
    split
    · rfl
    · cases hfn : p.fns[fr.fn]? with
      | none => rfl
      | some fn =>
        simp only
        split
        · rename_i g args hcode
          split
          · rename_i vs fr1 hev
            have hfr : fr ∈ st.stack := by rw [hs]; exact List.mem_cons_self ..
            have hunt := hinv.untainted fr hfr fn hfn
            have hbelow : ∀ g ∈ rest, ∀ w ∈ g.vals, w.pointsInto fr.fid = false := by
              have d := hinv.down
              rw [hs, List.pairwise_cons] at d
              exact fun g hg => (d.1 g hg).1
            have hacc_fn : EscapeCheckFn fn = true := by
              simp only [EscapeCheckAccepts, List.all_eq_true] at hacc
              exact hacc fn (List.mem_of_getElem? hfn)
            have hargs : args.any (opTainted (taint fn)) = false := by
              simp only [EscapeCheckFn, List.all_eq_true] at hacc_fn
              have := hacc_fn _ (List.mem_of_getElem? hcode)
              cases ha : args.any (opTainted (taint fn))
              · rfl
              · simp [ha] at this
            have hno := evalOps_untainted hunt hbelow hargs hev
            cases hany : vs.any (Val.pointsInto fr.fid)
            · rfl
            · obtain ⟨w, hw, hw'⟩ := List.any_eq_true.mp hany
              rw [hno w hw] at hw'
              cases hw'
          · rfl
        · rfl

end Toy.TailCall.EscapeProof
