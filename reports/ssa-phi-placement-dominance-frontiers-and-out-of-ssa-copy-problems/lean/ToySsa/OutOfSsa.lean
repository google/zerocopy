import ToySsa.Lang
import ToySsa.Decide

/-!
Out-of-SSA translation by naive copy insertion: the exact correctness condition
(parallel copies; every predecessor of a φ-block has a single successor), the critical-edge
corollary, and the swap and lost-copy miscompilations.
-/
namespace Toy.Ssa

variable {n : Nat}

/-! ## General correctness of naive copy insertion -/

theorem mem_succs {G : Cfg n} {p c : Fin n} : c ∈ succs G p ↔ G.edge p c = true := by
  simp [succs, List.mem_filter, List.mem_finRange]

theorem succs_nodup (G : Cfg n) (p : Fin n) : (succs G p).Nodup :=
  List.filter_sublist.nodup (List.nodup_finRange n)

private theorem eq_singleton_of_nodup {α : Type} {l : List α} {b : α} (hnd : l.Nodup)
    (hb : b ∈ l) (hall : ∀ c ∈ l, c = b) : l = [b] := by
  cases l with
  | nil => simp at hb
  | cons c rest =>
    have hc := hall c List.mem_cons_self
    subst hc
    cases rest with
    | nil => rfl
    | cons d rest' =>
      have hd := hall d (by simp)
      subst hd
      simp at hnd

private theorem length_pos_of_ne_nil' {α : Type} {l : List α} (h : l ≠ []) : 0 < l.length := by
  cases l with
  | nil => exact absurd rfl h
  | cons _ _ => simp

/-- Copies for φ-free successors are identities. -/
theorem execBody_flatMap_parallel_nil {V : Type} [DecidableEq V] (P : SsaProg V n) (p : Fin n) :
    ∀ (l : List (Fin n)) (τ : V → Nat), (∀ c ∈ l, P.phis c = []) →
      execBody (l.flatMap fun c => copyInstrs .parallel (P.phiMoves p c)) τ = τ := by
  intro l
  induction l with
  | nil => intro τ _; rfl
  | cons c rest ih =>
    intro τ h
    rw [List.flatMap_cons, execBody_append]
    have hc : P.phis c = [] := h c List.mem_cons_self
    have : execBody (copyInstrs .parallel (P.phiMoves p c)) τ = τ := by
      show parCopy (P.phiMoves p c) τ = τ
      simp [SsaProg.phiMoves, hc, parCopy_nil]
    rw [this]
    exact ih τ (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))

/-- Under `PhiPredsSingleSucc`, the parallel copies appended to `p` act, whichever successor `b`
is taken next, exactly as the φs of `b` on the edge `p → b`. -/
theorem execBody_outCopies_parallel_eq_enter {V : Type} [DecidableEq V] (P : SsaProg V n)
    (h : PhiPredsSingleSucc P) {p b : Fin n} (hpb : P.cfg.edge p b = true) (τ : V → Nat) :
    execBody (outCopies .parallel P p) τ = P.enter p b τ := by
  by_cases hb : 0 < (P.phis b).length
  · have hs : succs P.cfg p = [b] :=
      eq_singleton_of_nodup (succs_nodup _ _) (mem_succs.mpr hpb)
        (fun c hc => h p b hb hpb c (mem_succs.mp hc))
    simp only [outCopies, hs, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rfl
  · have hnil : P.phis b = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hall : ∀ c ∈ succs P.cfg p, P.phis c = [] := by
      intro c hc
      apply Classical.byContradiction
      intro hne
      have hcb := h p c (length_pos_of_ne_nil' hne) (mem_succs.mp hc) b hpb
      subst hcb
      exact hne hnil
    rw [outCopies, execBody_flatMap_parallel_nil P p _ τ hall]
    simp [SsaProg.enter, SsaProg.phiMoves, hnil, parCopy_nil]

/-- **Exact relation at block ends.** Under `PhiPredsSingleSucc` with parallel copies, along every
walk the naive translation's store at the end of the last block `b` is the SSA program's store
there followed by the copies appended to `b`. -/
theorem naiveOutOfSsa_parallel_run_eq_outCopies {V : Type} [DecidableEq V] (P : SsaProg V n)
    (h : PhiPredsSingleSucc P) {a b : Fin n} {path : List (Fin n)} (hw : Walk P.cfg a b path)
    (σ : V → Nat) :
    (naiveOutOfSsa .parallel P).run σ path = execBody (outCopies .parallel P b) (P.run σ path) := by
  refine Walk.snoc_induction (G := P.cfg) (a := a)
    (fun c w => (naiveOutOfSsa .parallel P).run σ w =
      execBody (outCopies .parallel P c) (P.run σ w)) ?_ ?_ hw
  · show execBody ((naiveOutOfSsa .parallel P).body a) σ = _
    rw [naiveOutOfSsa_body, execBody_append]
    rfl
  · intro w p c hwp hpc ih
    obtain ⟨l, rfl⟩ : ∃ l, w = l ++ [p] := ⟨_, hwp.eq_dropLast_append⟩
    rw [Prog.run_append_singleton, ih, naiveOutOfSsa_body, execBody_append,
      execBody_outCopies_parallel_eq_enter P h hpc, List.append_assoc]
    show _ = execBody (outCopies .parallel P c) (P.run σ (l ++ [p, c]))
    rw [SsaProg.run_append_pair]

/-- **Naive out-of-SSA with parallel copies is exact when every predecessor of a φ-block has a
single successor.** Along every walk: (a) on entry to the last block `b` (after its φs in the SSA
program), the translated program's store equals the SSA program's store on all variables; and
(b) at the end of `b` the stores are also equal provided no successor of `b` carries φs (for
example, an exit block with no successors). -/
theorem naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc {V : Type} [DecidableEq V]
    (P : SsaProg V n) (h : PhiPredsSingleSucc P) {a b : Fin n} {path : List (Fin n)}
    (hw : Walk P.cfg a b path) (σ : V → Nat) :
    (naiveOutOfSsa .parallel P).atTop σ path = P.atTop σ path ∧
      ((∀ c, P.cfg.edge b c = true → P.phis c = []) →
        (naiveOutOfSsa .parallel P).run σ path = P.run σ path) := by
  constructor
  · rcases hw.single_or_snoc with ⟨rfl, rfl⟩ | ⟨w, p, rfl, hwp, hpb⟩
    · rfl
    · obtain ⟨l, rfl⟩ : ∃ l, w = l ++ [p] := ⟨_, hwp.eq_dropLast_append⟩
      rw [Prog.atTop_append_singleton, naiveOutOfSsa_parallel_run_eq_outCopies P h hwp,
        execBody_outCopies_parallel_eq_enter P h hpb, List.append_assoc]
      exact (P.atTop_append_pair σ l p b).symm
  · intro hexit
    rw [naiveOutOfSsa_parallel_run_eq_outCopies P h hw, outCopies,
      execBody_flatMap_parallel_nil P b _ _ (fun c hc => hexit c (mem_succs.mp hc))]

/-- No critical edges and φs only at join blocks imply that every predecessor of a φ-block has a
single successor. -/
theorem phiPredsSingleSucc_of_noCriticalEdges {V : Type} (P : SsaProg V n)
    (hce : NoCriticalEdges P.cfg) (hj : PhisOnlyAtJoins P) : PhiPredsSingleSucc P := by
  intro p b hb hpb c hpc
  obtain ⟨a₁, a₂, hne, h₁, h₂⟩ := hj b hb
  rcases hce p b hpb with hs | hp
  · exact hs c hpc
  · exact absurd ((hp a₁ h₁).trans (hp a₂ h₂).symm) hne

/-- **Critical-edge form**: with no critical edges, φs only at join blocks, and parallel copies,
naive out-of-SSA translation is exact on every walk on entry to the last block, and at its end
when no successor of the last block carries φs. Derived from the two previous results. -/
theorem naiveOutOfSsa_parallel_eq_of_noCriticalEdges_of_phisOnlyAtJoins {V : Type} [DecidableEq V]
    (P : SsaProg V n) (hce : NoCriticalEdges P.cfg) (hj : PhisOnlyAtJoins P)
    {a b : Fin n} {path : List (Fin n)} (hw : Walk P.cfg a b path) (σ : V → Nat) :
    (naiveOutOfSsa .parallel P).atTop σ path = P.atTop σ path ∧
      ((∀ c, P.cfg.edge b c = true → P.phis c = []) →
        (naiveOutOfSsa .parallel P).run σ path = P.run σ path) :=
  naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc P
    (phiPredsSingleSucc_of_noCriticalEdges P hce hj) hw σ

/-! ## Sequential copies -/

instance SeqSafe.instDecidable {V : Type} [DecidableEq V] : (ms : List (V × V)) → Decidable (SeqSafe ms)
  | [] => isTrue trivial
  | m :: rest =>
    haveI := SeqSafe.instDecidable rest
    inferInstanceAs (Decidable (m.1 ∉ rest.map Prod.fst ∧ m.1 ∉ rest.map Prod.snd ∧ SeqSafe rest))

/-- **Sequential copies realize a parallel copy when no destination is overwritten or read
later**: if no destination of a move is the destination or source of a later move (`SeqSafe`),
the assignments `d₁ := s₁; …; dₖ := sₖ` in list order have the effect of the parallel copy. -/
theorem execBody_sequential_eq_parCopy {V : Type} [DecidableEq V] :
    ∀ (ms : List (V × V)), SeqSafe ms → ∀ σ : V → Nat,
      execBody (copyInstrs .sequential ms) σ = parCopy ms σ
  | [], _, σ => (parCopy_nil σ).symm
  | (d, s) :: rest, ⟨hd1, hd2, hrest⟩, σ => by
    show execBody (copyInstrs .sequential rest) (upd σ d (σ s)) = _
    rw [execBody_sequential_eq_parCopy rest hrest]
    funext y
    unfold parCopy
    simp only [List.find?_cons]
    by_cases hyd : d = y
    · subst hyd
      have : rest.find? (fun m => decide (m.1 = d)) = none := by
        rw [List.find?_eq_none]
        intro m hm
        simp only [decide_eq_true_eq]
        intro h; exact hd1 (List.mem_map.mpr ⟨m, hm, h⟩)
      simp [this, upd]
    · have hdy : decide (d = y) = false := decide_eq_false hyd
      simp only [hdy]
      cases hf : rest.find? (fun m => decide (m.1 = y)) with
      | none => simp [upd, Ne.symm hyd]
      | some m =>
        have hm := List.mem_of_find?_eq_some hf
        have : m.2 ≠ d := fun h => hd2 (List.mem_map.mpr ⟨m, hm, h⟩)
        simp [upd, this]

theorem execBody_outCopies_sequential_eq_parallel {V : Type} [DecidableEq V] (P : SsaProg V n)
    (hs : ∀ p b, SeqSafe (P.phiMoves p b)) (p : Fin n) (τ : V → Nat) :
    execBody (outCopies .sequential P p) τ = execBody (outCopies .parallel P p) τ := by
  unfold outCopies
  generalize succs P.cfg p = l
  induction l generalizing τ with
  | nil => rfl
  | cons c rest ih =>
    rw [List.flatMap_cons, List.flatMap_cons, execBody_append, execBody_append,
      execBody_sequential_eq_parCopy _ (hs p c)]
    exact ih _

/-- With `SeqSafe` φ-moves for every pair of blocks `(p, b)`, CFG edge or not, the sequential and
parallel naive translations have the same store after every sequence of blocks (walk or not). -/
theorem naiveOutOfSsa_sequential_run_eq_parallel {V : Type} [DecidableEq V] (P : SsaProg V n)
    (hs : ∀ p b, SeqSafe (P.phiMoves p b)) (σ : V → Nat) (path : List (Fin n)) :
    (naiveOutOfSsa .sequential P).run σ path = (naiveOutOfSsa .parallel P).run σ path := by
  induction path generalizing σ with
  | nil => rfl
  | cons b bs ih =>
    show (naiveOutOfSsa .sequential P).run (execBody ((naiveOutOfSsa .sequential P).body b) σ) bs =
      (naiveOutOfSsa .parallel P).run (execBody ((naiveOutOfSsa .parallel P).body b) σ) bs
    rw [naiveOutOfSsa_body, naiveOutOfSsa_body, execBody_append, execBody_append,
      execBody_outCopies_sequential_eq_parallel P hs]
    exact ih _

/-- **Naive out-of-SSA with sequential copies is exact under `PhiPredsSingleSucc` when the φ-moves
for every pair of blocks `(p, b)`, CFG edge or not, are `SeqSafe`** (no φ destination of `b` is the
destination or `p`-operand of a later φ of `b`); same two conclusions as the parallel theorem. -/
theorem naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe {V : Type} [DecidableEq V]
    (P : SsaProg V n) (h : PhiPredsSingleSucc P) (hs : ∀ p b, SeqSafe (P.phiMoves p b))
    {a b : Fin n} {path : List (Fin n)} (hw : Walk P.cfg a b path) (σ : V → Nat) :
    (naiveOutOfSsa .sequential P).atTop σ path = P.atTop σ path ∧
      ((∀ c, P.cfg.edge b c = true → P.phis c = []) →
        (naiveOutOfSsa .sequential P).run σ path = P.run σ path) := by
  have hpar := naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc P h hw σ
  refine ⟨?_, fun hexit => ?_⟩
  · rw [← hpar.1]
    exact naiveOutOfSsa_sequential_run_eq_parallel P hs σ _
  · rw [← hpar.2 hexit]
    exact naiveOutOfSsa_sequential_run_eq_parallel P hs σ _

/-- `SeqSafe` is tight in `execBody_sequential_eq_parCopy`: the swap move list
`[(0, 1), (1, 0)]` is not `SeqSafe`, and executing it one move at a time differs from the parallel
copy (at variable `1`, starting from the identity store). -/
theorem execBody_sequential_needs_seqSafe :
    ¬ SeqSafe ([(0, 1), (1, 0)] : List (Nat × Nat)) ∧
    ¬ (∀ σ : Nat → Nat, execBody (copyInstrs .sequential ([(0, 1), (1, 0)] : List (Nat × Nat))) σ =
        parCopy [(0, 1), (1, 0)] σ) := by
  refine ⟨fun h => h.2.1 (by simp), fun h => ?_⟩
  have := congrFun (h (fun x => x)) 1
  simp [execBody, copyInstrs, Instr.exec, upd, parCopy, Exp.eval] at this

/-- Non-vacuity of `execBody_sequential_eq_parCopy` on a move list where order matters: in
`[(2, 1), (1, 0)]` the second move overwrites the source of the first, and the list is
`SeqSafe`. -/
theorem execBody_sequential_hyps_nonvacuous : SeqSafe ([(2, 1), (1, 0)] : List (Nat × Nat)) := by
  simp [SeqSafe]

/-! ## The swap problem -/

/-- Variables of the swap example: `a₁ = 0`, `b₁ = 1`, `a₂ = 2`, `b₂ = 3`, temporary `t = 4`. -/
def swapCfg : Cfg 4 := Cfg.ofEdges 4 [(0, 1), (1, 2), (2, 1), (1, 3)] 0

/-- Swap loop in SSA form (back edge split by the latch block `2`, so no edge is critical):
`a₁ := 1; b₁ := 2` in block `0`; header `1` has `a₂ = φ(a₁, b₂)`, `b₂ = φ(b₁, a₂)`
(operands for predecessors `0` and `2`); exit `3`. φ order `[a₂, b₂]`. -/
def swapSsaAB : SsaProg Nat 4 where
  cfg := swapCfg
  phis b := if b = 1 then
      [(2, fun p => if p = 0 then 0 else 3), (3, fun p => if p = 0 then 1 else 2)] else []
  body b := if b = 0 then [.assign 0 (.lit 1), .assign 1 (.lit 2)] else []

/-- The same SSA program with φ order `[b₂, a₂]`. -/
def swapSsaBA : SsaProg Nat 4 where
  cfg := swapCfg
  phis b := if b = 1 then
      [(3, fun p => if p = 0 then 1 else 2), (2, fun p => if p = 0 then 0 else 3)] else []
  body b := if b = 0 then [.assign 0 (.lit 1), .assign 1 (.lit 2)] else []

/-- Out-of-SSA program for the swap loop that sequentializes the back-edge copies through the
temporary `t = 4`: `t := a₂; a₂ := b₂; b₂ := t` at the end of the latch. -/
def swapTempProg : Prog Nat 4 where
  cfg := swapCfg
  body b :=
    if b = 0 then [.assign 0 (.lit 1), .assign 1 (.lit 2), .assign 2 (.var 0), .assign 3 (.var 1)]
    else if b = 2 then [.assign 4 (.var 2), .assign 2 (.var 3), .assign 3 (.var 4)]
    else []

/-- One trip around the swap loop. -/
def swapWalk : List (Fin 4) := [0, 1, 2, 1]

theorem swapWalk_walk : Walk swapCfg 0 1 swapWalk := walk_of_isWalkB (by decide)

/-- **Swap problem**: after one back-edge traversal from `a₁ = 1, b₁ = 2`, the SSA program has
`(a₂, b₂) = (2, 1)`; sequential copies in order `a₂ := b₂; b₂ := a₂` give `(2, 2)`, and in order
`b₂ := a₂; a₂ := b₂` give `(1, 1)`. Both φ orders denote the same SSA program. -/
theorem swap_sequential_either_order_wrong :
    (swapSsaAB.atTop (fun _ => 0) swapWalk 2, swapSsaAB.atTop (fun _ => 0) swapWalk 3) = (2, 1) ∧
    (swapSsaBA.atTop (fun _ => 0) swapWalk 2, swapSsaBA.atTop (fun _ => 0) swapWalk 3) = (2, 1) ∧
    ((naiveOutOfSsa .sequential swapSsaAB).atTop (fun _ => 0) swapWalk 2,
      (naiveOutOfSsa .sequential swapSsaAB).atTop (fun _ => 0) swapWalk 3) = (2, 2) ∧
    ((naiveOutOfSsa .sequential swapSsaBA).atTop (fun _ => 0) swapWalk 2,
      (naiveOutOfSsa .sequential swapSsaBA).atTop (fun _ => 0) swapWalk 3) = (1, 1) := by
  decide

theorem phiPredsSingleSucc_swapSsaAB : PhiPredsSingleSucc swapSsaAB := by
  unfold PhiPredsSingleSucc; decide

theorem noCriticalEdges_swapCfg : NoCriticalEdges swapCfg := by
  unfold NoCriticalEdges; decide

theorem phisOnlyAtJoins_swapSsaAB : PhisOnlyAtJoins swapSsaAB := by
  intro b hb
  have : b = 1 := by revert b; decide
  subst this
  exact ⟨0, 2, by decide, by decide, by decide⟩

/-- Positive control for the swap problem: the naive translation of the swap loop with parallel
copies agrees with the SSA program on entry to the last block of every walk (an instance of
`naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc`). -/
theorem swap_parallel_correct {a b : Fin 4} {path : List (Fin 4)} (hw : Walk swapCfg a b path)
    (σ : Nat → Nat) :
    (naiveOutOfSsa .parallel swapSsaAB).atTop σ path = swapSsaAB.atTop σ path :=
  (naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc swapSsaAB phiPredsSingleSucc_swapSsaAB hw σ).1

/-- Stores that agree on every variable other than the temporary `t = 4`. -/
def AgreeOffTemp (σ₁ σ₂ : Nat → Nat) : Prop := ∀ x, x ≠ 4 → σ₁ x = σ₂ x

private theorem swap_naive_body0 : (naiveOutOfSsa .parallel swapSsaAB).body 0 =
    [.assign 0 (.lit 1), .assign 1 (.lit 2), .pcopy [(2, 0), (3, 1)]] := rfl
private theorem swap_naive_body1 : (naiveOutOfSsa .parallel swapSsaAB).body 1 =
    [.pcopy [], .pcopy []] := rfl
private theorem swap_naive_body2 : (naiveOutOfSsa .parallel swapSsaAB).body 2 =
    [.pcopy [(2, 3), (3, 2)]] := rfl
private theorem swap_naive_body3 : (naiveOutOfSsa .parallel swapSsaAB).body 3 = [] := rfl

/-- Each block of `swapTempProg` acts like the corresponding block of the naive parallel
translation, off the temporary. -/
theorem swapTemp_block_agree (b : Fin 4) {σ₁ σ₂ : Nat → Nat} (h : AgreeOffTemp σ₁ σ₂) :
    AgreeOffTemp (execBody (swapTempProg.body b) σ₁)
      (execBody ((naiveOutOfSsa .parallel swapSsaAB).body b) σ₂) := by
  have hb : b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 := by revert b; decide
  intro x hx
  have hx' := h x hx
  rcases hb with rfl | rfl | rfl | rfl
  · rw [swap_naive_body0]
    simp [swapTempProg, execBody, Instr.exec, upd_apply, Exp.eval, parCopy_cons, parCopy_nil]
    by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> by_cases h2 : x = 2 <;>
      by_cases h3 : x = 3 <;> simp_all <;> omega
  · rw [swap_naive_body1]
    simp [swapTempProg, execBody, Instr.exec, parCopy_nil]
    exact hx'
  · rw [swap_naive_body2]
    simp [swapTempProg, execBody, Instr.exec, upd_apply, Exp.eval, parCopy_cons, parCopy_nil]
    have e2 := h 2 (by decide)
    have e3 := h 3 (by decide)
    by_cases h2 : x = 2 <;> by_cases h3 : x = 3 <;> simp_all <;> omega
  · rw [swap_naive_body3]
    exact hx'

theorem swapTemp_run_agree (path : List (Fin 4)) :
    ∀ {σ₁ σ₂ : Nat → Nat}, AgreeOffTemp σ₁ σ₂ →
      AgreeOffTemp (swapTempProg.run σ₁ path) ((naiveOutOfSsa .parallel swapSsaAB).run σ₂ path) := by
  induction path with
  | nil => intro σ₁ σ₂ h; exact h
  | cons b bs ih => intro σ₁ σ₂ h; exact ih (swapTemp_block_agree b h)

/-- **A temporary also fixes the swap problem**: the sequence `t := a₂; a₂ := b₂; b₂ := t` agrees
with the SSA program on every variable other than `t`, on every walk. -/
theorem swap_temp_sequence_correct {a b : Fin 4} {path : List (Fin 4)}
    (hw : Walk swapCfg a b path) (σ : Nat → Nat) (x : Nat) (hx : x ≠ 4) :
    swapTempProg.atTop σ path x = swapSsaAB.atTop σ path x := by
  rw [← (naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc swapSsaAB phiPredsSingleSucc_swapSsaAB
    hw σ).1]
  exact swapTemp_run_agree path.dropLast (fun _ _ => rfl) x hx

/-- Sanity check of the temporary sequence on one loop trip. -/
theorem swap_temp_one_trip :
    (swapTempProg.atTop (fun _ => 0) swapWalk 2, swapTempProg.atTop (fun _ => 0) swapWalk 3) =
      (2, 1) := by
  decide

/-! ## When sequential copies are exact, and when they are not -/

/-- The chain `0 → 1 → 2`. -/
def dupCfg : Cfg 3 := Cfg.ofEdges 3 [(0, 1), (1, 2)] 0

/-- A φ-block with two φs for the same destination `2` on the chain `0 → 1 → 2`: `x₀ := 10;
x₁ := 20` in block `0`, then `2 = φ(0)` and `2 = φ(1)` at block `1`. No φ destination is a φ
operand. -/
def dupPhiSsa : SsaProg Nat 3 where
  cfg := dupCfg
  phis b := if b = 1 then [(2, fun _ => 0), (2, fun _ => 1)] else []
  body b := if b = 0 then [.assign 0 (.lit 10), .assign 1 (.lit 20)] else []

/-- **Distinct φ destinations are needed for sequential copies**: on `dupPhiSsa` every predecessor
of a φ-block has a single successor, no edge is critical, and no φ destination is a φ operand,
yet the sequential translation gives `2 ↦ 20` (last write wins) where the SSA program's parallel
φs give `2 ↦ 10` (first entry wins). -/
theorem dupPhi_sequential_wrong :
    PhiPredsSingleSucc dupPhiSsa ∧ NoCriticalEdges dupCfg ∧
    (∀ (p : Fin 3), ∀ φ ∈ dupPhiSsa.phis 1, φ.2 p ≠ 2) ∧
    ¬ SeqSafe (dupPhiSsa.phiMoves 0 1) ∧ Walk dupCfg 0 1 [0, 1] ∧
    (naiveOutOfSsa .sequential dupPhiSsa).atTop (fun _ => 0) [0, 1] 2 = 20 ∧
    dupPhiSsa.atTop (fun _ => 0) [0, 1] 2 = 10 := by
  refine ⟨by unfold PhiPredsSingleSucc; decide, by unfold NoCriticalEdges; decide, ?_, by decide,
    walk_of_isWalkB (by decide), by decide, by decide⟩
  intro p φ hφ
  simp [dupPhiSsa] at hφ
  rcases hφ with rfl | rfl <;> simp

/-- Header φs `a₂ = φ(a₁, c₁)`, `b₂ = φ(b₁, a₂)` on the swap CFG, in φ order `[a₂, b₂]`
(`a₁ = 0`, `b₁ = 1`, `c₁ = 2`, `a₂ = 3`, `b₂ = 4`; `a₁ := 1; b₁ := 2; c₁ := 5` in block `0`). The
second φ reads the first φ's destination on the back edge, without a cycle. -/
def chainPhiAB : SsaProg Nat 4 where
  cfg := swapCfg
  phis b := if b = 1 then
      [(3, fun p => if p = 0 then 0 else 2), (4, fun p => if p = 0 then 1 else 3)] else []
  body b := if b = 0 then [.assign 0 (.lit 1), .assign 1 (.lit 2), .assign 2 (.lit 5)] else []

/-- The same φs in order `[b₂, a₂]`. -/
def chainPhiBA : SsaProg Nat 4 where
  cfg := swapCfg
  phis b := if b = 1 then
      [(4, fun p => if p = 0 then 1 else 3), (3, fun p => if p = 0 then 0 else 2)] else []
  body b := if b = 0 then [.assign 0 (.lit 1), .assign 1 (.lit 2), .assign 2 (.lit 5)] else []

/-- **φ order matters without a cycle**: after one back-edge traversal the SSA program has
`(a₂, b₂) = (5, 1)`; sequential copies in order `[a₂, b₂]` give `(5, 5)`. The order `[b₂, a₂]` is
`SeqSafe` for every pair of blocks, so its sequential translation is exact on every walk
(`chainPhiBA_sequential_exact`). -/
theorem chainPhi_order_matters :
    PhiPredsSingleSucc chainPhiAB ∧ ¬ SeqSafe (chainPhiAB.phiMoves 2 1) ∧
    (chainPhiAB.atTop (fun _ => 0) swapWalk 3, chainPhiAB.atTop (fun _ => 0) swapWalk 4) = (5, 1) ∧
    ((naiveOutOfSsa .sequential chainPhiAB).atTop (fun _ => 0) swapWalk 3,
      (naiveOutOfSsa .sequential chainPhiAB).atTop (fun _ => 0) swapWalk 4) = (5, 5) ∧
    (∀ p b, SeqSafe (chainPhiBA.phiMoves p b)) := by
  refine ⟨by unfold PhiPredsSingleSucc; decide, by decide, by decide, by decide, by decide⟩

theorem chainPhiBA_sequential_exact {a b : Fin 4} {path : List (Fin 4)}
    (hw : Walk swapCfg a b path) (σ : Nat → Nat) :
    (naiveOutOfSsa .sequential chainPhiBA).atTop σ path = chainPhiBA.atTop σ path :=
  (naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe chainPhiBA
    (by unfold PhiPredsSingleSucc; decide) chainPhi_order_matters.2.2.2.2 hw σ).1

/-- **A copy cycle with an outgoing tree copy needs no temporary**: the parallel copy
`(a₂, b₂, c₂) := (b₂, a₂, a₂)` (`a₂ = 0`, `b₂ = 1`, `c₂ = 2`) is realized by the three plain
assignments `c₂ := a₂; a₂ := b₂; b₂ := c₂`. -/
theorem windmill_sequential_no_temp (σ : Nat → Nat) :
    execBody [.assign 2 (.var 0), .assign 0 (.var 1), .assign 1 (.var 2)] σ =
      parCopy [(0, 1), (1, 0), (2, 0)] σ := by
  funext y
  simp only [execBody, List.foldl, Instr.exec, upd_apply, Exp.eval, parCopy_cons, parCopy_nil]
  by_cases h0 : y = 0 <;> by_cases h1 : y = 1 <;> by_cases h2 : y = 2 <;> simp_all <;> omega

/-! ## The lost-copy problem -/

/-- Variables: `x₁ = 0`, `x₂ = 1`, `x₃ = 2`. CFG: `0 → 1`, `1 → 1` (critical back edge),
`1 → 2`. -/
def lostCfg : Cfg 3 := Cfg.ofEdges 3 [(0, 1), (1, 1), (1, 2)] 0

/-- Briggs et al.'s lost-copy loop after copy folding: `x₁ := 1`; header
`x₂ = φ(x₁, x₃)`, `x₃ := x₂ + 1`, loop or exit; the exit reads `x₂`. -/
def lostSsa : SsaProg Nat 3 where
  cfg := lostCfg
  phis b := if b = 1 then [(1, fun p => if p = 0 then 0 else 2)] else []
  body b := if b = 0 then [.assign 0 (.lit 1)]
    else if b = 1 then [.assign 2 (.add (.var 1) (.lit 1))] else []

/-- The source loop before SSA construction and copy folding (`x = 0`, `y = 1`):
`x := 1`; loop `{ y := x; x := x + 1 }`; return `y`. -/
def lostSource : Prog Nat 3 where
  cfg := lostCfg
  body b := if b = 0 then [.assign 0 (.lit 1)]
    else if b = 1 then [.assign 1 (.var 0), .assign 0 (.add (.var 0) (.lit 1))] else []

/-- Two loop iterations, then exit. -/
def lostWalk : List (Fin 3) := [0, 1, 1, 2]

theorem lostWalk_walk : Walk lostCfg 0 2 lostWalk := walk_of_isWalkB (by decide)

/-- **Lost-copy problem**: on two iterations the source returns `y = 2` and the SSA program has
`x₂ = 2` at the exit, but the naive translation (even with parallel copies) has `x₂ = 3`: the
back-edge copy `x₂ := x₃` at the end of block `1` also runs on the exit path. -/
theorem lostCopy_naive_miscompiles :
    lostSource.atTop (fun _ => 0) lostWalk 1 = 2 ∧
    lostSsa.atTop (fun _ => 0) lostWalk 1 = 2 ∧
    (naiveOutOfSsa .parallel lostSsa).atTop (fun _ => 0) lostWalk 1 = 3 ∧
    (naiveOutOfSsa .sequential lostSsa).atTop (fun _ => 0) lostWalk 1 = 3 := by
  decide

theorem not_noCriticalEdges_lostCfg : ¬ NoCriticalEdges lostCfg := by
  unfold NoCriticalEdges; decide

theorem phisOnlyAtJoins_lostSsa : PhisOnlyAtJoins lostSsa := by
  intro b hb
  have : b = 1 := by revert b; decide
  subst this
  exact ⟨0, 1, by decide, by decide, by decide⟩

theorem not_phiPredsSingleSucc_lostSsa : ¬ PhiPredsSingleSucc lostSsa := by
  unfold PhiPredsSingleSucc; decide

/-- CFG after splitting the critical edge `1 → 1` with a new block `3`:
`0 → 1`, `1 → 3`, `3 → 1`, `1 → 2`. -/
def lostSplitCfg : Cfg 4 := Cfg.ofEdges 4 [(0, 1), (1, 3), (3, 1), (1, 2)] 0

/-- The lost-copy SSA program on the split CFG: the φ operand from the new block `3` is `x₃`. -/
def lostSplitSsa : SsaProg Nat 4 where
  cfg := lostSplitCfg
  phis b := if b = 1 then [(1, fun p => if p = 0 then 0 else 2)] else []
  body b := if b = 0 then [.assign 0 (.lit 1)]
    else if b = 1 then [.assign 2 (.add (.var 1) (.lit 1))] else []

/-- `k` back-edge traversals then exit, on the original CFG: block `1` runs `k + 1` times. -/
def lostLoopWalk (k : Nat) : List (Fin 3) := [0, 1] ++ List.replicate k 1 ++ [2]

/-- The corresponding walk on the split CFG (each back edge goes through block `3`). -/
def lostSplitWalk (k : Nat) : List (Fin 4) := [0, 1] ++ (List.replicate k [3, 1]).flatten ++ [2]

private theorem replicate_cons_eq_append {α : Type} (k : Nat) (x : α) :
    x :: List.replicate k x = List.replicate k x ++ [x] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change x :: x :: List.replicate k x = (x :: List.replicate k x) ++ [x]
    rw [List.cons_append, ← ih]

private theorem replicate_flatten_succ {α : Type} (k : Nat) (xs : List α) :
    (List.replicate (k + 1) xs).flatten = (List.replicate k xs).flatten ++ xs := by
  induction k with
  | zero => simp
  | succ k ih =>
    change xs ++ (List.replicate (k + 1) xs).flatten = (xs ++ (List.replicate k xs).flatten) ++ xs
    rw [ih, List.append_assoc]

private theorem lostLoopPrefix_succ (k : Nat) :
    ([0, 1] ++ List.replicate (k + 1) 1 : List (Fin 3)) = ([0, 1] ++ List.replicate k 1) ++ [1] := by
  rw [List.append_assoc, ← replicate_cons_eq_append]; rfl

private theorem lostSplitPrefix_succ (k : Nat) :
    ([0, 1] ++ (List.replicate (k + 1) [3, 1]).flatten : List (Fin 4)) =
      ([0, 1] ++ (List.replicate k [3, 1]).flatten) ++ [3, 1] := by
  rw [replicate_flatten_succ, List.append_assoc]

private theorem lostLoopPrefix_last (k : Nat) :
    ∃ l, ([0, 1] ++ List.replicate k 1 : List (Fin 3)) = l ++ [1] := by
  cases k with
  | zero => exact ⟨[0], rfl⟩
  | succ k => exact ⟨_, lostLoopPrefix_succ k⟩

private theorem lostSplitPrefix_last (k : Nat) :
    ∃ l, ([0, 1] ++ (List.replicate k [3, 1]).flatten : List (Fin 4)) = l ++ [1] := by
  cases k with
  | zero => exact ⟨[0], rfl⟩
  | succ k =>
    exact ⟨[0, 1] ++ (List.replicate k [3, 1]).flatten ++ [3], by
      rw [lostSplitPrefix_succ]; simp [List.append_assoc]⟩

theorem lostLoopPrefix_walk (k : Nat) : Walk lostCfg 0 1 ([0, 1] ++ List.replicate k 1) := by
  induction k with
  | zero => exact walk_of_isWalkB (by decide)
  | succ k ih => rw [lostLoopPrefix_succ]; exact ih.append_edge (by decide)

/-- Every `lostLoopWalk k` is a walk of `lostCfg` from `0` to `2`. -/
theorem lostLoopWalk_walk (k : Nat) : Walk lostCfg 0 2 (lostLoopWalk k) :=
  (lostLoopPrefix_walk k).append_edge (by decide)

theorem lostSplitPrefix_walk (k : Nat) :
    Walk lostSplitCfg 0 1 ([0, 1] ++ (List.replicate k [3, 1]).flatten) := by
  induction k with
  | zero => exact walk_of_isWalkB (by decide)
  | succ k ih =>
    rw [lostSplitPrefix_succ]
    have h1 := ih.append_edge (c := 3) (by decide)
    have h2 := h1.append_edge (c := 1) (by decide)
    simpa [List.append_assoc] using h2

/-- Every `lostSplitWalk k` is a walk of `lostSplitCfg` from `0` to `2`. -/
theorem lostSplitWalk_walk (k : Nat) : Walk lostSplitCfg 0 2 (lostSplitWalk k) :=
  (lostSplitPrefix_walk k).append_edge (by decide)

private theorem lost_runs_agree (k : Nat) (σ : Nat → Nat) :
    lostSplitSsa.run σ ([0, 1] ++ (List.replicate k [3, 1]).flatten) =
      lostSsa.run σ ([0, 1] ++ List.replicate k 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lostSplitPrefix_succ, lostLoopPrefix_succ, SsaProg.run_append_pair]
    obtain ⟨l, hl⟩ := lostSplitPrefix_last k
    obtain ⟨l', hl'⟩ := lostLoopPrefix_last k
    have h3 : lostSplitSsa.run σ (([0, 1] ++ (List.replicate k [3, 1]).flatten) ++ [3]) =
        lostSplitSsa.run σ ([0, 1] ++ (List.replicate k [3, 1]).flatten) := by
      rw [hl, SsaProg.run_snoc]
      simp [lostSplitSsa, SsaProg.enter, SsaProg.phiMoves, parCopy_nil, execBody]
    rw [h3, hl', SsaProg.run_snoc, ← hl', ← ih]
    rfl

/-- **Splitting the critical edge fixes the lost copy**: for every number `k` of back-edge
traversals (so the loop body runs `k + 1 ≥ 1` times), the naive (parallel-copy) translation of
the split program reaches the exit with the same store as the SSA program on the original CFG. -/
theorem lostCopy_split_fixes (k : Nat) (σ : Nat → Nat) :
    (naiveOutOfSsa .parallel lostSplitSsa).atTop σ (lostSplitWalk k) =
      lostSsa.atTop σ (lostLoopWalk k) := by
  rw [(naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc lostSplitSsa
    (by unfold PhiPredsSingleSucc; decide) (lostSplitWalk_walk k) σ).1]
  obtain ⟨l, hl⟩ := lostSplitPrefix_last k
  obtain ⟨l', hl'⟩ := lostLoopPrefix_last k
  unfold lostSplitWalk lostLoopWalk
  rw [hl, hl', SsaProg.atTop_snoc, SsaProg.atTop_snoc, ← hl, ← hl', lost_runs_agree]
  simp [lostSplitSsa, lostSsa, SsaProg.enter, SsaProg.phiMoves, parCopy_nil]

/-- Sanity check of the split translation on two iterations: the exit sees `x₂ = 2`. -/
theorem lostCopy_split_two_iterations :
    (naiveOutOfSsa .parallel lostSplitSsa).atTop (fun _ => 0) (lostSplitWalk 1) 1 = 2 ∧
    lostSsa.atTop (fun _ => 0) (lostLoopWalk 1) 1 = 2 := by
  decide

theorem noCriticalEdges_lostSplitCfg : NoCriticalEdges lostSplitCfg := by
  unfold NoCriticalEdges; decide

theorem phiPredsSingleSucc_lostSplitSsa : PhiPredsSingleSucc lostSplitSsa := by
  unfold PhiPredsSingleSucc; decide

/-! ## Counterexamples for the hypotheses of the general theorem -/

/-- `PhiPredsSingleSucc` is necessary (lost copy): parallel mode, a genuine walk, and the stores
differ on entry to the exit block, so the conclusion fails. -/
theorem naiveOutOfSsa_needs_phiPredsSingleSucc :
    ¬ PhiPredsSingleSucc lostSsa ∧ Walk lostCfg 0 2 lostWalk ∧
    ¬ ((naiveOutOfSsa .parallel lostSsa).atTop (fun _ => 0) lostWalk =
          lostSsa.atTop (fun _ => 0) lostWalk ∧
        ((∀ c, lostCfg.edge 2 c = true → lostSsa.phis c = []) →
          (naiveOutOfSsa .parallel lostSsa).run (fun _ => 0) lostWalk =
            lostSsa.run (fun _ => 0) lostWalk)) := by
  refine ⟨not_phiPredsSingleSucc_lostSsa, lostWalk_walk, fun h => ?_⟩
  have := congrFun h.1 1
  exact absurd this (by decide)

/-- Parallel copies are necessary (swap): `PhiPredsSingleSucc` holds and the walk is genuine, but
the sequential translation's store differs on entry to the last block. -/
theorem naiveOutOfSsa_needs_parallel :
    PhiPredsSingleSucc swapSsaAB ∧ Walk swapCfg 0 1 swapWalk ∧
    ¬ ((naiveOutOfSsa .sequential swapSsaAB).atTop (fun _ => 0) swapWalk =
          swapSsaAB.atTop (fun _ => 0) swapWalk ∧
        ((∀ c, swapCfg.edge 1 c = true → swapSsaAB.phis c = []) →
          (naiveOutOfSsa .sequential swapSsaAB).run (fun _ => 0) swapWalk =
            swapSsaAB.run (fun _ => 0) swapWalk)) := by
  refine ⟨phiPredsSingleSucc_swapSsaAB, swapWalk_walk, fun h => ?_⟩
  have := congrFun h.1 3
  exact absurd this (by decide)

/-- The walk hypothesis is necessary: on the non-walk `[0, 3]` the copies emitted at the end of
block `0` for its real successor `1` are visible at the top of `3`. -/
theorem naiveOutOfSsa_needs_walk :
    PhiPredsSingleSucc swapSsaAB ∧ NoCriticalEdges swapCfg ∧ PhisOnlyAtJoins swapSsaAB ∧
    (∀ a b, ¬ Walk swapCfg a b [0, 3]) ∧
    ¬ ((naiveOutOfSsa .parallel swapSsaAB).atTop (fun _ => 0) [0, 3] =
          swapSsaAB.atTop (fun _ => 0) [0, 3] ∧
        ((∀ c, swapCfg.edge 3 c = true → swapSsaAB.phis c = []) →
          (naiveOutOfSsa .parallel swapSsaAB).run (fun _ => 0) [0, 3] =
            swapSsaAB.run (fun _ => 0) [0, 3])) := by
  refine ⟨phiPredsSingleSucc_swapSsaAB, noCriticalEdges_swapCfg, phisOnlyAtJoins_swapSsaAB, ?_,
    fun h => ?_⟩
  · intro a b hw
    cases hw with
    | cons he hw' =>
      have := hw'.getElem_zero (by simp)
      simp at this
      subst this
      exact absurd he (by decide)
  · have := congrFun h.1 2
    exact absurd this (by decide)

/-- The lost-copy loop without an exit block: `0 → 1`, `1 → 1`, and the procedure returns `x₂`
at the end of block `1`, the return not being modeled as an edge. -/
def lostNoExitCfg : Cfg 2 := Cfg.ofEdges 2 [(0, 1), (1, 1)] 0

def lostNoExitSsa : SsaProg Nat 2 where
  cfg := lostNoExitCfg
  phis b := if b = 1 then [(1, fun p => if p = 0 then 0 else 2)] else []
  body b := if b = 0 then [.assign 0 (.lit 1)] else [.assign 2 (.add (.var 1) (.lit 1))]

/-- **The exit hypothesis of the block-end conclusion is necessary, and returns must be modeled as
edges to an exit block.** Without an exit block, every predecessor of the φ-block has a single
successor and no edge is critical, the block-entry stores agree, but at the end of block `1`
(where the unmodeled return reads `x₂`) the naive translation has `x₂ = 3` while the SSA program
has `x₂ = 2`: block `1` has the φ-carrying successor `1`. -/
theorem naiveOutOfSsa_run_needs_exit :
    PhiPredsSingleSucc lostNoExitSsa ∧ NoCriticalEdges lostNoExitCfg ∧
    PhisOnlyAtJoins lostNoExitSsa ∧ Walk lostNoExitCfg 0 1 [0, 1, 1] ∧
    ¬ (∀ c, lostNoExitCfg.edge 1 c = true → lostNoExitSsa.phis c = []) ∧
    (naiveOutOfSsa .parallel lostNoExitSsa).atTop (fun _ => 0) [0, 1, 1] =
      lostNoExitSsa.atTop (fun _ => 0) [0, 1, 1] ∧
    (naiveOutOfSsa .parallel lostNoExitSsa).run (fun _ => 0) [0, 1, 1] 1 = 3 ∧
    lostNoExitSsa.run (fun _ => 0) [0, 1, 1] 1 = 2 := by
  have hpp : PhiPredsSingleSucc lostNoExitSsa := by unfold PhiPredsSingleSucc; decide
  have hw : Walk lostNoExitCfg 0 1 [0, 1, 1] := walk_of_isWalkB (by decide)
  refine ⟨hpp, by unfold NoCriticalEdges; decide, ?_, hw, ?_,
    (naiveOutOfSsa_parallel_eq_of_phiPredsSingleSucc lostNoExitSsa hpp hw _).1, by decide,
    by decide⟩
  · intro b hb
    have : b = 1 := by revert b; decide
    subst this
    exact ⟨0, 1, by decide, by decide, by decide⟩
  · intro h
    exact absurd (h 1 (by decide)) (by decide)

/-- Branch `0 → 1`, `0 → 2` with a φ at the single-predecessor block `1`: `x := 5` in block `0`
(`x = 0`), `a = φ(x)` at `1` (`a = 1`). -/
def branchPhiCfg : Cfg 3 := Cfg.ofEdges 3 [(0, 1), (0, 2)] 0

def branchPhiSsa : SsaProg Nat 3 where
  cfg := branchPhiCfg
  phis b := if b = 1 then [(1, fun _ => 0)] else []
  body b := if b = 0 then [.assign 0 (.lit 5)] else []

/-- `PhisOnlyAtJoins` is necessary for the critical-edge form: no critical edges, parallel
copies, a genuine walk `0 → 2`, but the copy for the φ at `1` runs on the way to `2`. -/
theorem naiveOutOfSsa_noCriticalEdges_needs_phisOnlyAtJoins :
    NoCriticalEdges branchPhiCfg ∧ ¬ PhisOnlyAtJoins branchPhiSsa ∧
    Walk branchPhiCfg 0 2 [0, 2] ∧
    ¬ ((naiveOutOfSsa .parallel branchPhiSsa).atTop (fun _ => 0) [0, 2] =
          branchPhiSsa.atTop (fun _ => 0) [0, 2] ∧
        ((∀ c, branchPhiCfg.edge 2 c = true → branchPhiSsa.phis c = []) →
          (naiveOutOfSsa .parallel branchPhiSsa).run (fun _ => 0) [0, 2] =
            branchPhiSsa.run (fun _ => 0) [0, 2])) := by
  refine ⟨by unfold NoCriticalEdges; decide, ?_, walk_of_isWalkB (by decide), fun h => ?_⟩
  · intro h
    obtain ⟨a, c, hne, ha, hc⟩ := h 1 (by decide)
    revert a c; decide
  · have := congrFun h.1 1
    exact absurd this (by decide)

/-- `NoCriticalEdges` is necessary for the critical-edge form (lost copy). -/
theorem naiveOutOfSsa_noCriticalEdges_needs_noCriticalEdges :
    ¬ NoCriticalEdges lostCfg ∧ PhisOnlyAtJoins lostSsa ∧ Walk lostCfg 0 2 lostWalk ∧
    ¬ ((naiveOutOfSsa .parallel lostSsa).atTop (fun _ => 0) lostWalk =
          lostSsa.atTop (fun _ => 0) lostWalk ∧
        ((∀ c, lostCfg.edge 2 c = true → lostSsa.phis c = []) →
          (naiveOutOfSsa .parallel lostSsa).run (fun _ => 0) lostWalk =
            lostSsa.run (fun _ => 0) lostWalk)) :=
  ⟨not_noCriticalEdges_lostCfg, phisOnlyAtJoins_lostSsa, lostWalk_walk,
    naiveOutOfSsa_needs_phiPredsSingleSucc.2.2⟩

/-- Parallel copies are necessary for the critical-edge form (swap). -/
theorem naiveOutOfSsa_noCriticalEdges_needs_parallel :
    NoCriticalEdges swapCfg ∧ PhisOnlyAtJoins swapSsaAB ∧ Walk swapCfg 0 1 swapWalk ∧
    ¬ ((naiveOutOfSsa .sequential swapSsaAB).atTop (fun _ => 0) swapWalk =
          swapSsaAB.atTop (fun _ => 0) swapWalk ∧
        ((∀ c, swapCfg.edge 1 c = true → swapSsaAB.phis c = []) →
          (naiveOutOfSsa .sequential swapSsaAB).run (fun _ => 0) swapWalk =
            swapSsaAB.run (fun _ => 0) swapWalk)) :=
  ⟨noCriticalEdges_swapCfg, phisOnlyAtJoins_swapSsaAB, swapWalk_walk,
    naiveOutOfSsa_needs_parallel.2.2⟩

/-- Non-vacuity of the general theorem and its critical-edge form: the swap loop, on a walk that
ends at the exit block `3` (no successors, so the block-end conclusion's hypothesis holds too). -/
theorem naiveOutOfSsa_hyps_nonvacuous :
    PhiPredsSingleSucc swapSsaAB ∧ NoCriticalEdges swapCfg ∧ PhisOnlyAtJoins swapSsaAB ∧
    Walk swapCfg 0 3 [0, 1, 2, 1, 3] ∧ (∀ c, swapCfg.edge 3 c = true → swapSsaAB.phis c = []) :=
  ⟨phiPredsSingleSucc_swapSsaAB, noCriticalEdges_swapCfg, phisOnlyAtJoins_swapSsaAB,
    walk_of_isWalkB (by decide), by decide⟩

/-- Non-vacuity of `naiveOutOfSsa_sequential_eq_of_phiPredsSingleSucc_of_seqSafe`: the header φs
in order `[b₂, a₂]` on the swap CFG, on a walk through the back edge to the exit. -/
theorem naiveOutOfSsa_sequential_hyps_nonvacuous :
    PhiPredsSingleSucc chainPhiBA ∧ (∀ p b, SeqSafe (chainPhiBA.phiMoves p b)) ∧
    Walk swapCfg 0 3 [0, 1, 2, 1, 3] ∧ (∀ c, swapCfg.edge 3 c = true → chainPhiBA.phis c = []) :=
  ⟨by unfold PhiPredsSingleSucc; decide, chainPhi_order_matters.2.2.2.2,
    walk_of_isWalkB (by decide), by decide⟩

/-- Non-vacuity of `swap_temp_sequence_correct`: one loop trip, observed variable `a₂ = 2 ≠ 4`. -/
theorem swap_temp_hyps_nonvacuous : Walk swapCfg 0 1 swapWalk ∧ (2 : Nat) ≠ 4 :=
  ⟨swapWalk_walk, by decide⟩

/-- `x ≠ t` is necessary for `swap_temp_sequence_correct`: after one trip the temporary holds the
old `a₂` (`1`), while the SSA program never writes `t`. -/
theorem swap_temp_needs_ne_temp :
    Walk swapCfg 0 1 swapWalk ∧ ¬ ((4 : Nat) ≠ 4) ∧
    swapTempProg.atTop (fun _ => 0) swapWalk 4 ≠ swapSsaAB.atTop (fun _ => 0) swapWalk 4 :=
  ⟨swapWalk_walk, fun h => h rfl, by decide⟩

/-- The walk hypothesis is necessary for `swap_temp_sequence_correct`: on the non-walk `[0, 3]`
the entry copies are visible at `3`. -/
theorem swap_temp_needs_walk :
    (∀ a b, ¬ Walk swapCfg a b [0, 3]) ∧ (2 : Nat) ≠ 4 ∧
    swapTempProg.atTop (fun _ => 0) [0, 3] 2 ≠ swapSsaAB.atTop (fun _ => 0) [0, 3] 2 :=
  ⟨naiveOutOfSsa_needs_walk.2.2.2.1, by decide, by decide⟩

/-- Tightness of `PhiPredsSingleSucc` in the sequential theorem: the lost-copy loop has a single
φ, so its moves are `SeqSafe` for all pairs of blocks, yet the sequential translation fails at the exit. -/
theorem naiveOutOfSsa_sequential_needs_phiPredsSingleSucc :
    ¬ PhiPredsSingleSucc lostSsa ∧ (∀ p b, SeqSafe (lostSsa.phiMoves p b)) ∧
    Walk lostCfg 0 2 lostWalk ∧
    ¬ ((naiveOutOfSsa .sequential lostSsa).atTop (fun _ => 0) lostWalk =
          lostSsa.atTop (fun _ => 0) lostWalk ∧
        ((∀ c, lostCfg.edge 2 c = true → lostSsa.phis c = []) →
          (naiveOutOfSsa .sequential lostSsa).run (fun _ => 0) lostWalk =
            lostSsa.run (fun _ => 0) lostWalk)) := by
  refine ⟨not_phiPredsSingleSucc_lostSsa, by decide, lostWalk_walk, fun h => ?_⟩
  have := congrFun h.1 1
  exact absurd this (by decide)

/-- `SeqSafe` is necessary for the sequential theorem: the header φs in order `[a₂, b₂]`. -/
theorem naiveOutOfSsa_sequential_needs_seqSafe :
    PhiPredsSingleSucc chainPhiAB ∧ ¬ (∀ p b, SeqSafe (chainPhiAB.phiMoves p b)) ∧
    Walk swapCfg 0 1 swapWalk ∧
    ¬ ((naiveOutOfSsa .sequential chainPhiAB).atTop (fun _ => 0) swapWalk =
          chainPhiAB.atTop (fun _ => 0) swapWalk ∧
        ((∀ c, swapCfg.edge 1 c = true → chainPhiAB.phis c = []) →
          (naiveOutOfSsa .sequential chainPhiAB).run (fun _ => 0) swapWalk =
            chainPhiAB.run (fun _ => 0) swapWalk)) := by
  refine ⟨chainPhi_order_matters.1, fun h => chainPhi_order_matters.2.1 (h 2 1), swapWalk_walk,
    fun h => ?_⟩
  have := congrFun h.1 4
  exact absurd this (by decide)

/-- The walk hypothesis is necessary for the sequential theorem: on the non-walk `[0, 3]` the
copies at the end of block `0` are visible at the top of `3`. -/
theorem naiveOutOfSsa_sequential_needs_walk :
    PhiPredsSingleSucc chainPhiBA ∧ (∀ p b, SeqSafe (chainPhiBA.phiMoves p b)) ∧
    (∀ a b, ¬ Walk swapCfg a b [0, 3]) ∧
    ¬ ((naiveOutOfSsa .sequential chainPhiBA).atTop (fun _ => 0) [0, 3] =
          chainPhiBA.atTop (fun _ => 0) [0, 3] ∧
        ((∀ c, swapCfg.edge 3 c = true → chainPhiBA.phis c = []) →
          (naiveOutOfSsa .sequential chainPhiBA).run (fun _ => 0) [0, 3] =
            chainPhiBA.run (fun _ => 0) [0, 3])) := by
  refine ⟨naiveOutOfSsa_sequential_hyps_nonvacuous.1, chainPhi_order_matters.2.2.2.2,
    naiveOutOfSsa_needs_walk.2.2.2.1, fun h => ?_⟩
  have := congrFun h.1 3
  exact absurd this (by decide)

/-- The exit hypothesis of the block-end conclusion is necessary for the sequential theorem too
(single φ, so `SeqSafe`): without an exit block the stores differ at the end of block `1`. -/
theorem naiveOutOfSsa_sequential_run_needs_exit :
    PhiPredsSingleSucc lostNoExitSsa ∧ (∀ p b, SeqSafe (lostNoExitSsa.phiMoves p b)) ∧
    Walk lostNoExitCfg 0 1 [0, 1, 1] ∧
    ¬ (∀ c, lostNoExitCfg.edge 1 c = true → lostNoExitSsa.phis c = []) ∧
    (naiveOutOfSsa .sequential lostNoExitSsa).run (fun _ => 0) [0, 1, 1] 1 = 3 ∧
    lostNoExitSsa.run (fun _ => 0) [0, 1, 1] 1 = 2 :=
  ⟨naiveOutOfSsa_run_needs_exit.1, by decide, naiveOutOfSsa_run_needs_exit.2.2.2.1,
    naiveOutOfSsa_run_needs_exit.2.2.2.2.1, by decide, by decide⟩

end Toy.Ssa
