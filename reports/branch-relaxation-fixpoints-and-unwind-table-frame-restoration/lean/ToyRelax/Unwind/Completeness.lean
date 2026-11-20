import ToyRelax.Unwind.Results

/-!
# Result 7b: checker completeness

The abstract interpretation is exact for this straight-line language: a single
well-chosen entry state (registers hold pairwise distinct values above every
constant the body writes, memory holds a small value) separates every
abstract distinction the checker makes.
-/

namespace Toy.Unwind

/-- A bound strictly above every constant written by `setReg` in `os`, and at
least 1. -/
def constBound : List Op → Int
  | [] => 1
  | .setReg _ v :: os => max (v + 1) (constBound os)
  | _ :: os => constBound os

theorem one_le_constBound : ∀ os : List Op, 1 ≤ constBound os
  | [] => by simp [constBound]
  | o :: os => by
    have := one_le_constBound os
    cases o <;> simp only [constBound] <;> omega

theorem lt_constBound_of_mem : ∀ (os : List Op) (r : Nat) (v : Int),
    Op.setReg r v ∈ os → v < constBound os
  | [], _, _, h => by cases h
  | o :: os, r, v, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h
      simp only [constBound]
      omega
    · have := lt_constBound_of_mem os r v h
      cases o <;> simp only [constBound] <;> omega

/-- `x` is the concrete value denoted by abstract value `v` relative to the
offset `M`: entry values of register `q` are `M + q`, unknown values are below
`M`. -/
def Denotes (M : Int) : AVal → Int → Prop
  | .entry q => fun x => x = M + q
  | .unknown => fun x => x < M

/-- Exact description of a concrete state reached from an entry state with
`sp = 0`. -/
def Precise (M : Int) (A : AState) (s : MState) : Prop :=
  s.sp = 0 - A.d ∧ (∀ r, Denotes M (A.regs r) (s.regs r)) ∧
  (∀ k, Denotes M (A.slot k) (s.mem (0 - k)))

/-- The separating entry state. -/
def sepState (M : Int) : MState := ⟨0, fun r => M + r, fun _ => 0⟩

theorem precise_init {M : Int} (hM : 1 ≤ M) : Precise M AState.init (sepState M) := by
  refine ⟨by simp [AState.init, sepState], ?_, ?_⟩
  · intro r
    simp [AState.init, sepState, Denotes]
  · intro k
    simp only [AState.init, sepState, Denotes]
    omega

theorem precise_execOp {M : Int} {A : AState} {s : MState} (o : Op)
    (hc : ∀ r v, o = .setReg r v → v < M) (h : Precise M A s) :
    Precise M (absOp o A) (execOp o s) := by
  obtain ⟨hsp, hregs, hslot⟩ := h
  cases o with
  | push r =>
    refine ⟨by simp only [execOp, absOp]; omega, hregs, ?_⟩
    intro k
    simp only [absOp, execOp, upd]
    by_cases hk : k = A.d + 1
    · rw [ite_eq_left hk, ite_eq_left (by omega)]
      exact hregs r
    · rw [ite_eq_right hk, ite_eq_right (by omega)]
      exact hslot k
  | subSp n => exact ⟨by simp only [execOp, absOp]; omega, hregs, hslot⟩
  | saveAt r off =>
    refine ⟨by simp only [execOp, absOp]; omega, hregs, ?_⟩
    intro k
    simp only [absOp, execOp, upd]
    by_cases hk : k = A.d - off
    · rw [ite_eq_left hk, ite_eq_left (by omega)]
      exact hregs r
    · rw [ite_eq_right hk, ite_eq_right (by omega)]
      exact hslot k
  | pop r =>
    refine ⟨by simp only [execOp, absOp]; omega, ?_, hslot⟩
    intro r'
    simp only [absOp, execOp, upd]
    by_cases hr : r' = r
    · rw [ite_eq_left hr, ite_eq_left hr, hsp]
      exact hslot A.d
    · rw [ite_eq_right hr, ite_eq_right hr]
      exact hregs r'
  | addSp n => exact ⟨by simp only [execOp, absOp]; omega, hregs, hslot⟩
  | setReg r v =>
    refine ⟨hsp, ?_, hslot⟩
    intro r'
    simp only [absOp, execOp, upd]
    by_cases hr : r' = r
    · rw [ite_eq_left hr, ite_eq_left hr]
      exact hc r v rfl
    · rw [ite_eq_right hr, ite_eq_right hr]
      exact hregs r'

theorem precise_run {M : Int} : ∀ (os : List Op) (A : AState) (s : MState),
    (∀ r v, Op.setReg r v ∈ os → v < M) → Precise M A s →
    Precise M (absRun os A) (run os s)
  | [], _, _, _, h => h
  | o :: os, _, _, hc, h =>
    precise_run os _ _ (fun r v hm => hc r v (List.mem_cons_of_mem _ hm))
      (precise_execOp o (fun r v ho => hc r v (ho ▸ List.mem_cons_self)) h)

/-- **Result 7b (checker completeness).**  Every table that is correct in the
sense of `TableCorrect` is accepted by the checker. -/
theorem checkTable_complete {body : List Op} {cs : List Nat} {tbl : Table}
    (h : TableCorrect body cs tbl) : checkTable body cs tbl = true := by
  unfold checkTable
  rw [List.all_eq_true]
  intro i hi
  have hi' : i ≤ body.length := by
    rw [List.mem_range] at hi
    omega
  let M := constBound body
  have hM : 1 ≤ M := one_le_constBound body
  have hc : ∀ r v, Op.setReg r v ∈ body.take i → v < M :=
    fun r v hm => lt_constBound_of_mem body r v (List.mem_of_mem_take hm)
  obtain ⟨hcfa, hrec⟩ := h (sepState M) i hi'
  have hp := precise_run (body.take i) _ _ hc (precise_init hM)
  generalize hA : absRun (List.take i body) AState.init = A at hp ⊢
  generalize hs : run (List.take i body) (sepState M) = s at hp hcfa hrec
  obtain ⟨hsp, hregs, hslot⟩ := hp
  simp only [sepState] at hcfa
  have hcfa' : (tbl i).cfa = A.d := by omega
  unfold checkRow
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨hcfa', ?_⟩
  intro r hr
  have hrr := hrec r hr
  simp only [sepState] at hrr
  unfold recoverReg at hrr
  cases hrule : (tbl i).rule r with
  | savedAt off =>
    rw [hrule] at hrr
    simp only [Option.some.injEq] at hrr
    have hd := hslot off
    rw [show s.sp + (tbl i).cfa - off = 0 - off by omega] at hrr
    simp only [ruleOk, beq_iff_eq]
    cases hv : A.slot off with
    | entry q =>
      rw [hv] at hd
      simp only [Denotes] at hd
      have : (q : Int) = r := by omega
      rw [show q = r by omega]
    | unknown =>
      rw [hv] at hd
      simp only [Denotes] at hd
      omega
  | sameValue =>
    rw [hrule] at hrr
    simp only [Option.some.injEq] at hrr
    have hd := hregs r
    simp only [ruleOk, beq_iff_eq]
    cases hv : A.regs r with
    | entry q =>
      rw [hv] at hd
      simp only [Denotes] at hd
      rw [show q = r by omega]
    | unknown =>
      rw [hv] at hd
      simp only [Denotes] at hd
      omega
  | undefined =>
    rw [hrule] at hrr
    cases hrr

/-- Checker characterization (Results 7a and 7b combined): the checker accepts
exactly the correct tables. -/
theorem checkTable_iff_tableCorrect {body : List Op} {cs : List Nat} {tbl : Table} :
    checkTable body cs tbl = true ↔ TableCorrect body cs tbl :=
  ⟨checkTable_sound, checkTable_complete⟩

end Toy.Unwind
