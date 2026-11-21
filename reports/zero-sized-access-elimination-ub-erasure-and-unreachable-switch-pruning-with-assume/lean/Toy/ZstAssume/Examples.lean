import Toy.ZstAssume.RunLemmas

/-!
# Definition examples

For each core definition, fully proved intended positive and negative examples.
-/

namespace Toy.ZstAssume

/-- A state whose locals are given by a list (`0` beyond its end) and in which every
byte is dereferenceable. -/
def mkState (xs : List Int) : State := ⟨fun i => xs.getD i 0, fun _ => true⟩

/-- A state with the given locals in which no byte is dereferenceable. -/
def mkStateNoMem (xs : List Int) : State := ⟨fun i => xs.getD i 0, fun _ => false⟩

/-! ### Basic syntax and state -/

theorem state_set_updates : ((mkState [1, 2]).set 0 5).locals 0 = 5 := by decide
/-- `State.set` leaves the other locals unchanged. -/
theorem state_set_frames : ((mkState [1, 2]).set 0 5).locals 1 = 2 := by decide
theorem expr_eval_add : Expr.eval (mkState [3]) (.add (.var 0) (.const 2)) = 5 := by decide
/-- Expression arithmetic is unbounded: no 64-bit wrapping. -/
theorem expr_eval_no_wrap :
    Expr.eval (mkState []) (.add (.const 18446744073709551615) (.const 1)) ≠ 0 := by decide
theorem cond_eval_pos : Cond.eval (mkState [5]) (.eq 0 5) = true := by decide
theorem cond_eval_neg : Cond.eval (mkState [5]) (.ne 0 5) = false := by decide
theorem bytesDeref_pos : bytesDeref (fun p => decide (p < 10)) 8 2 = true := by decide
/-- One non-dereferenceable byte in the range (address `10`) makes the range fail. -/
theorem bytesDeref_neg : bytesDeref (fun p => decide (p < 10)) 9 2 = false := by decide
theorem accessTy_read : (Stmt.read (.var 0) ⟨0, 4⟩).accessTy? = some ⟨0, 4⟩ := by decide
theorem accessTy_emit : (Stmt.emit (.const 0)).accessTy? = none := by decide

/-! ### `aligned`, `ZContract.holds`, `accessOK` -/

theorem aligned_pos : aligned 4 8 = true := by decide
theorem aligned_neg : aligned 4 6 = false := by decide
/-- Degenerate edge `align = 0`: exactly the address `0` is aligned. -/
theorem aligned_zero_align_zero_addr : aligned 0 0 = true := by decide
theorem aligned_zero_align_nonzero_addr : aligned 0 4 = false := by decide
/-- Degenerate edge `align = 0`, in general: exactly the address `0` is aligned. -/
theorem aligned_zero_iff (p : Int) : aligned 0 p = true ↔ p = 0 := by
  simp [aligned]
/-- Every address is aligned for alignment `1`, including negative ones. -/
theorem aligned_one (p : Int) : aligned 1 p = true := by simp [aligned]

theorem holds_anyPtr_null_misaligned : ZContract.anyPtr.holds 4 0 = true ∧
    ZContract.anyPtr.holds 4 1 = true := by decide
theorem holds_aligned_rejects_misaligned : ZContract.aligned.holds 4 1 = false := by decide
theorem holds_aligned_admits_null : ZContract.aligned.holds 4 0 = true := by decide
theorem holds_nonnullAligned_rejects_null : ZContract.nonnullAligned.holds 1 0 = false := by
  decide
theorem holds_nonnullAligned_admits : ZContract.nonnullAligned.holds 4 8 = true := by decide

/-- A one-byte access needs its byte to be dereferenceable, whatever the zero-size
contract. -/
theorem accessOK_nonzero_needs_deref (K : ZContract) :
    accessOK K (fun _ => false) 1 8 1 = false ∧ accessOK K (fun _ => true) 1 8 1 = true := by
  cases K <;> decide
/-- A zero-byte access ignores dereferenceability: `accessOK` reduces to `pre₀`. -/
theorem accessOK_zero_ignores_deref :
    accessOK .aligned (fun _ => false) 4 8 0 = true ∧
      accessOK .aligned (fun _ => true) 4 9 0 = false := by decide
/-- A nonzero access through null is UB even under the most permissive zero-size
contract. -/
theorem accessOK_nonzero_null (K : ZContract) : accessOK K (fun _ => true) 1 0 1 = false := by
  cases K <;> decide

/-! ### `IsZeroSizeAccess`, `Stmt.zeroPre`, `Stmt.pre` -/

theorem isZeroSize_read_zst : IsZeroSizeAccess (.read (.var 0) ⟨0, 4⟩) := by decide
theorem isZeroSize_copy_zero_count : IsZeroSizeAccess (.copy (.var 0) (.var 1) ⟨4, 4⟩ 0) := by
  decide
theorem isZeroSize_copy_zst : IsZeroSizeAccess (.copy (.var 0) (.var 1) ⟨0, 2⟩ 3) := by decide
theorem not_isZeroSize_read_byte : ¬ IsZeroSizeAccess (.read (.var 0) ⟨1, 1⟩) := by decide
theorem not_isZeroSize_copy_one : ¬ IsZeroSizeAccess (.copy (.var 0) (.var 1) ⟨4, 4⟩ 1) := by
  decide
theorem not_isZeroSize_emit : ¬ IsZeroSizeAccess (.emit (.const 0)) := by decide
theorem not_isZeroSize_assume : ¬ IsZeroSizeAccess (.assume (.eq 0 0)) := by decide

/-- For a zero-size access, the statement's UB precondition is exactly `zeroPre`. -/
theorem pre_eq_zeroPre_of_isZeroSize (K : ZContract) (st : State) (s : Stmt)
    (hz : IsZeroSizeAccess s) : s.pre K st = s.zeroPre K st := by
  cases s with
  | read p τ =>
    simp only [IsZeroSizeAccess] at hz
    simp [Stmt.pre, Stmt.zeroPre, accessOK, hz]
  | write p τ =>
    simp only [IsZeroSizeAccess] at hz
    simp [Stmt.pre, Stmt.zeroPre, accessOK, hz]
  | copy src dst τ n =>
    simp only [IsZeroSizeAccess] at hz
    simp [Stmt.pre, Stmt.zeroPre, accessOK, hz]
  | _ => simp [IsZeroSizeAccess] at hz

theorem zeroPre_read_misaligned :
    (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned (mkState [1]) = false := by decide
theorem zeroPre_read_aligned :
    (Stmt.read (.var 0) ⟨0, 4⟩).zeroPre .aligned (mkState [8]) = true := by decide
theorem zeroPre_copy_checks_src :
    (Stmt.copy (.var 0) (.var 1) ⟨4, 4⟩ 0).zeroPre .aligned (mkState [1, 8]) = false := by
  decide

/-- With alignment `1` and a contract that permits null, `zeroPre` always holds. -/
theorem zeroPre_of_align_one {K : ZContract} (hK : K ≠ .nonnullAligned) (s : Stmt)
    (st : State) (ha : ∀ τ, s.accessTy? = some τ → τ.align = 1) : s.zeroPre K st = true := by
  cases K with
  | nonnullAligned => exact absurd rfl hK
  | anyPtr => cases s <;> simp [Stmt.zeroPre, ZContract.holds]
  | aligned =>
    cases s with
    | read p τ =>
      have := ha τ rfl
      simp [Stmt.zeroPre, ZContract.holds, this, aligned]
    | write p τ =>
      have := ha τ rfl
      simp [Stmt.zeroPre, ZContract.holds, this, aligned]
    | copy src dst τ n =>
      have := ha τ rfl
      simp [Stmt.zeroPre, ZContract.holds, this, aligned]
    | _ => simp [Stmt.zeroPre]

/-! ### `selectTarget` -/

/-- The first matching arm wins. -/
theorem selectTarget_first_match : selectTarget [(5, 1), (5, 2)] 0 5 = 1 := by decide
/-- No matching arm: the `otherwise` label. -/
theorem selectTarget_otherwise : selectTarget [(5, 1)] 0 6 = 0 := by decide

/-! ### `run` and `HasBeh` -/

/-- `emit 7; halt`. -/
def pEmit7 : Prog := [⟨[.emit (.const 7)], .halt⟩]
/-- `unreachable`. -/
def pUnreach : Prog := [Block.unreach]
/-- `halt`. -/
def pHalt : Prog := [⟨[], .halt⟩]
/-- A silent self-loop. -/
def pSpin : Prog := [⟨[], .goto 0⟩]
/-- A loop emitting `1` forever. -/
def pReact : Prog := [⟨[.emit (.const 1)], .goto 0⟩]

theorem step_emit7 (K : ZContract) (σ : State) :
    step K pEmit7 (pEmit7.init σ) = .next (some 7) ⟨0, [], σ⟩ := rfl
/-- Stepping at an `unreachable` terminator is UB. -/
theorem step_unreach (K : ZContract) (σ : State) : step K pUnreach (pUnreach.init σ) = .ub := rfl
theorem at_terminator (σ : State) : (pEmit7.at 0 1 σ).rest = [] := rfl
theorem at_entry (σ : State) : (pEmit7.at 0 0 σ).rest = [.emit (.const 7)] := rfl
theorem prefixOf_example : prefixOf (fun n => (n : Int)) 3 = [0, 1, 2] := by decide

theorem hasBeh_emit7 (K : ZContract) (σ : State) : HasBeh K pEmit7 σ (.term [7]) :=
  ⟨2, σ, rfl⟩

theorem not_hasBeh_emit7_wrong (K : ZContract) (σ : State) (t : List Int) :
    ¬ HasBeh K pEmit7 σ (.wrong t) := by
  intro h
  have := (hasBehFrom_iff_of_run_done (b := .wrong t)
    (show run K pEmit7 2 (pEmit7.init σ) = .done [7] σ from rfl)).1 h
  cases this

theorem hasBeh_unreach (K : ZContract) (σ : State) : HasBeh K pUnreach σ (.wrong []) :=
  ⟨1, rfl⟩

theorem run_spin (K : ZContract) (σ : State) :
    ∀ n, run K pSpin n (pSpin.init σ) = .running (pSpin.init σ) [] := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run_succ_next (o := none) (c' := pSpin.init σ) n rfl, ih]
    rfl

theorem hasBeh_spin (K : ZContract) (σ : State) (b : Beh) :
    HasBeh K pSpin σ b ↔ b = .div [] :=
  hasBehFrom_iff_of_silent (fun n => ⟨_, run_spin K σ n⟩) b

theorem run_react (K : ZContract) (σ : State) :
    ∀ k, run K pReact (2 * k) (pReact.init σ) = .running (pReact.init σ) (List.replicate k 1) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [h2, run_succ_next (o := some 1) (c' := ⟨0, [], σ⟩) _ rfl,
      run_succ_next (o := none) (c' := pReact.init σ) _ rfl, ih]
    simp [Outcome.cons, List.replicate_succ]

theorem run_react_running_aux (K : ZContract) (σ : State) :
    ∀ n, (∃ c t, run K pReact n (pReact.init σ) = .running c t) ∧
      (∃ c t, run K pReact n ⟨0, [], σ⟩ = .running c t)
  | 0 => ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩
  | n + 1 => by
    obtain ⟨⟨c₁, t₁, h₁⟩, ⟨c₂, t₂, h₂⟩⟩ := run_react_running_aux K σ n
    refine ⟨⟨c₂, [1] ++ t₂, ?_⟩, ⟨c₁, t₁, ?_⟩⟩
    · rw [run_succ_next (o := some 1) (c' := ⟨0, [], σ⟩) _ rfl, h₂]
      rfl
    · rw [run_succ_next (o := none) (c' := pReact.init σ) _ rfl, h₁]
      rfl

theorem run_react_running (K : ZContract) (σ : State) (n : Nat) :
    (run K pReact n (pReact.init σ)).isRunning = true := by
  obtain ⟨c, t, h⟩ := (run_react_running_aux K σ n).1
  rw [h]
  rfl

theorem hasBeh_react (K : ZContract) (σ : State) : HasBeh K pReact σ (.react fun _ => 1) := by
  refine ⟨run_react_running K σ, fun k => ⟨2 * k, ?_⟩⟩
  rw [run_react]
  simp [Outcome.trace, prefixOf, List.map_const']

/-! ### `ImprovesPP`, `ImprovesWT`, `RefinesPP`, `RefinesWT` -/

theorem improvesPP_pos : ImprovesPP (.term [1, 2]) (.wrong [1]) :=
  Or.inr ⟨[1], rfl, ⟨[2], rfl⟩⟩
theorem improvesPP_neg : ¬ ImprovesPP (.term [2]) (.wrong [1]) := by
  rintro (h | ⟨t, ht, hp⟩)
  · cases h
  · cases ht
    simp [Beh.HasPrefix] at hp
theorem improvesWT_pos : ImprovesWT (.term [2]) (.wrong [1]) := Or.inr ⟨[1], rfl⟩
theorem improvesWT_neg : ¬ ImprovesWT (.term [1]) (.term [2]) := by
  rintro (h | ⟨t, ht⟩)
  · cases h
  · cases ht

/-- UB is the top element: any target refines an always-UB source. -/
theorem refinesPP_of_src_unreach (K : ZContract) (P : Prog) : RefinesPP K pUnreach P :=
  fun σ bt _ => ⟨.wrong [], hasBeh_unreach K σ, Or.inr ⟨[], rfl, hasPrefix_nil bt⟩⟩

/-- Introducing UB where the source is defined is not a refinement under either
discipline. -/
theorem not_refinesWT_halt_unreach (K : ZContract) : ¬ RefinesWT K pHalt pUnreach := by
  intro h
  obtain ⟨bs, hbs, himp⟩ := h (mkState []) _ (hasBeh_unreach K (mkState []))
  have := (hasBehFrom_iff_of_run_done (b := bs)
    (show run K pHalt 1 (pHalt.init (mkState [])) = .done [] (mkState []) from rfl)).1 hbs
  subst this
  rcases himp with h' | ⟨t, ht⟩
  · cases h'
  · cases ht

theorem not_refinesPP_halt_unreach (K : ZContract) : ¬ RefinesPP K pHalt pUnreach :=
  fun h => not_refinesWT_halt_unreach K (refinesWT_of_refinesPP h)

/-- Whole-trace refinement is strictly weaker: losing an event before UB is allowed. -/
def pEmitUnreach : Prog := [⟨[.emit (.const 7)], .unreachable⟩]

theorem refinesWT_emitUnreach_unreach (K : ZContract) : RefinesWT K pEmitUnreach pUnreach := by
  intro σ bt hbt
  have := (hasBehFrom_iff_of_run_ub
    (show run K pUnreach 1 (pUnreach.init σ) = .ub [] from rfl) bt).1 hbt
  subst this
  exact ⟨.wrong [7], ⟨2, rfl⟩, Or.inr ⟨[7], rfl⟩⟩

theorem not_refinesPP_emitUnreach_unreach (K : ZContract) :
    ¬ RefinesPP K pEmitUnreach pUnreach := by
  intro h
  obtain ⟨bs, hbs, himp⟩ := h (mkState []) _ (hasBeh_unreach K (mkState []))
  have := (hasBehFrom_iff_of_run_ub (b := bs)
    (show run K pEmitUnreach 2 (pEmitUnreach.init (mkState [])) = .ub [7] from rfl)).1 hbs
  subst this
  rcases himp with h' | ⟨t, ht, hp⟩
  · cases h'
  · cases ht
    simp [Beh.HasPrefix] at hp

/-! ### `ReachableAt` -/

def pTwoHalts : Prog := [⟨[], .halt⟩, ⟨[], .halt⟩]

theorem reachableAt_entry (K : ZContract) (P : Prog) (σ : State) : ReachableAt K P 0 0 σ :=
  ⟨σ, 0, [], rfl⟩

/-- Block `1` of `pTwoHalts` is never reached. -/
theorem not_reachableAt_dead_block (K : ZContract) (st : State) :
    ¬ ReachableAt K pTwoHalts 1 0 st := by
  rintro ⟨σ, n, t, h⟩
  cases n with
  | zero => cases h
  | succ n =>
    rw [run_succ_halt (s := σ) n rfl] at h
    cases h

/-! ### `UBFree` -/

theorem ubFree_halt (K : ZContract) : UBFree K pHalt := by
  intro σ t h
  have := (hasBehFrom_iff_of_run_done (b := .wrong t)
    (show run K pHalt 1 (pHalt.init σ) = .done [] σ from rfl)).1 h
  cases this

theorem not_ubFree_unreach (K : ZContract) : ¬ UBFree K pUnreach :=
  fun h => h (mkState []) [] (hasBeh_unreach K (mkState []))

/-! ### `wpFrom` / `wp`: the two VC equations, proved as lemmas -/

theorem cons_none (r : Outcome) : r.cons none = r := by
  cases r <;> simp [Outcome.cons]

/-- `wp Unreachable Q = False`. -/
theorem wpFrom_unreachable {K : ZContract} {P : Prog} {l : Label} {st : State}
    (Q : List Int → State → Prop) (hl : (P.blk l).term = .unreachable) :
    ¬ wpFrom K P Q ⟨l, [], st⟩ := by
  rintro ⟨n, t, s, h, _⟩
  cases n with
  | zero => cases h
  | succ n =>
    have hs : step K P ⟨l, [], st⟩ = .ub := by simp [step, hl]
    rw [run_succ_ub n hs] at h
    cases h

/-- `wp (assume c) Q = c ∧ wp Q`. -/
theorem wpFrom_assume {K : ZContract} {P : Prog} {l : Label} {st : State} {rest : List Stmt}
    (Q : List Int → State → Prop) (c : Cond) :
    wpFrom K P Q ⟨l, .assume c :: rest, st⟩ ↔ c.eval st = true ∧ wpFrom K P Q ⟨l, rest, st⟩ := by
  constructor
  · rintro ⟨n, t, s, h, hq⟩
    cases n with
    | zero => cases h
    | succ n =>
      by_cases hc : c.eval st = true
      · have hs : step K P ⟨l, .assume c :: rest, st⟩ = .next none ⟨l, rest, st⟩ := by
          simp [step, execStmt, Stmt.pre, hc]
        rw [run_succ_next n hs, cons_none] at h
        exact ⟨hc, n, t, s, h, hq⟩
      · have hs : step K P ⟨l, .assume c :: rest, st⟩ = .ub := by
          simp [step, execStmt, Stmt.pre, hc]
        rw [run_succ_ub n hs] at h
        cases h
  · rintro ⟨hc, n, t, s, h, hq⟩
    have hs : step K P ⟨l, .assume c :: rest, st⟩ = .next none ⟨l, rest, st⟩ := by
      simp [step, execStmt, Stmt.pre, hc]
    exact ⟨n + 1, t, s, by rw [run_succ_next n hs, cons_none, h], hq⟩

theorem wp_halt_true (K : ZContract) (σ : State) : wp K pHalt (fun _ _ => True) σ :=
  ⟨1, [], σ, rfl, trivial⟩

theorem not_wp_unreach (K : ZContract) (Q : List Int → State → Prop) (σ : State) :
    ¬ wp K pUnreach Q σ :=
  wpFrom_unreachable Q rfl

/-! ### Transformations -/

theorem deleteStmt_example :
    deleteStmt [⟨[.read (.var 0) ⟨0, 4⟩, .emit (.const 1)], .halt⟩] 0 0 =
      [⟨[.emit (.const 1)], .halt⟩] := by decide
/-- Deleting at an out-of-range position changes nothing. -/
theorem deleteStmt_out_of_range : deleteStmt pEmit7 0 5 = pEmit7 := by decide

/-- Inserting at a position past the end appends before the terminator. -/
theorem insertStmt_past_end :
    insertStmt pEmit7 0 5 (.read (.var 0) ⟨0, 4⟩) =
      [⟨[.emit (.const 7), .read (.var 0) ⟨0, 4⟩], .halt⟩] := by decide

theorem insertStmt_example :
    insertStmt pEmit7 0 1 (.read (.var 0) ⟨0, 4⟩) =
      [⟨[.emit (.const 7), .read (.var 0) ⟨0, 4⟩], .halt⟩] := by decide

theorem dropArms_example : dropArms [(5, 1), (6, 2), (5, 3)] 5 = [(6, 2)] := by decide
/-- Arms with other values are kept. -/
theorem dropArms_keeps : dropArms [(6, 2)] 5 = [(6, 2)] := by decide

theorem pruneArm_example :
    pruneArm [⟨[], .switch 0 [(5, 1), (6, 2)] 3⟩] 0 5 = [⟨[], .switch 0 [(6, 2)] 3⟩] := by
  decide
/-- On a block that does not end in a switch, pruning is the identity. -/
theorem pruneArm_non_switch : pruneArm pEmit7 0 5 = pEmit7 := by decide

theorem pruneArmAssume_example :
    pruneArmAssume [⟨[], .switch 0 [(5, 1), (6, 2)] 3⟩] 0 5 =
      [⟨[.assume (.ne 0 5)], .switch 0 [(6, 2)] 3⟩] := by decide
theorem pruneArmAssume_non_switch : pruneArmAssume pEmit7 0 5 = pEmit7 := by decide

theorem pruneOtherwiseAssume_example :
    pruneOtherwiseAssume [⟨[], .switch 0 [(5, 1)] 2⟩] 0 =
      [⟨[.assume (.eq 0 5)], .goto 1⟩] := by decide
/-- With two arms the shape does not apply and nothing changes. -/
theorem pruneOtherwiseAssume_two_arms :
    pruneOtherwiseAssume [⟨[], .switch 0 [(5, 1), (6, 1)] 2⟩] 0 =
      [⟨[], .switch 0 [(5, 1), (6, 1)] 2⟩] := by decide

theorem replaceUnreachable_example : replaceUnreachable pEmit7 0 = pUnreach := by decide
/-- An out-of-range label is left unchanged (it already denotes `Block.unreach`). -/
theorem replaceUnreachable_out_of_range : replaceUnreachable pEmit7 3 = pEmit7 := by decide

/-- `setTerm` at an out-of-range label changes nothing. -/
theorem setTerm_out_of_range : setTerm pEmit7 3 (.goto 0) = pEmit7 := by decide

theorem foldToGoto_example :
    foldToGoto [⟨[], .switch 0 [(5, 1)] 2⟩] 0 2 = [⟨[], .goto 2⟩] := by decide

theorem isUnreachableBlock_out_of_range : IsUnreachableBlock pHalt 7 := by decide
theorem isUnreachableBlock_unreach : IsUnreachableBlock pUnreach 0 := by decide
theorem not_isUnreachableBlock_halt : ¬ IsUnreachableBlock pHalt 0 := by decide
/-- A block that emits before `unreachable` is not an unreachable block. -/
theorem not_isUnreachableBlock_emit_unreach : ¬ IsUnreachableBlock pEmitUnreach 0 := by decide

/-! ### Further definition examples -/

/-- `Ty` records the size and the alignment of a layout. -/
theorem ty_fields : (⟨0, 4⟩ : Ty).size = 0 ∧ (⟨0, 4⟩ : Ty).align = 4 := ⟨rfl, rfl⟩
/-- Two layouts with the same size and different alignments are different. -/
theorem ty_align_distinguishes : (⟨0, 4⟩ : Ty) ≠ ⟨0, 1⟩ := by decide

/-- `mkState` gives the listed locals and makes every byte dereferenceable. -/
theorem state_locals_example : (mkState [3, 4]).locals 1 = 4 ∧ (mkState []).deref 0 = true :=
  ⟨rfl, rfl⟩
/-- `mkStateNoMem` makes no byte dereferenceable. -/
theorem state_noMem_example : (mkStateNoMem [3, 4]).deref 0 = false := rfl

/-- `Stmt.pre` of a zero-size read at alignment `4` under `aligned`, aligned pointer. -/
theorem pre_read_aligned : (Stmt.read (.var 0) ⟨0, 4⟩).pre .aligned (mkState [8]) = true := by
  decide
/-- `Stmt.pre` of the same read through a misaligned pointer. -/
theorem pre_read_misaligned :
    (Stmt.read (.var 0) ⟨0, 4⟩).pre .aligned (mkState [1]) = false := by decide

/-- `execStmt` continues past a true `assume`. -/
theorem execStmt_assume_pass (K : ZContract) :
    (execStmt K (.assume (.eq 0 5)) (mkState [5])).isSome = true := rfl
/-- `execStmt` reports UB (`none`) for a false `assume`. -/
theorem execStmt_assume_fail (K : ZContract) :
    execStmt K (.assume (.eq 0 5)) (mkState [4]) = none := rfl

/-- `Outcome.trace` of a terminated outcome. -/
theorem outcome_trace_done : (Outcome.done [7] (mkState [])).trace = [7] := rfl
/-- `Outcome.trace` of a UB outcome is its own trace. -/
theorem outcome_trace_ub_ne : (Outcome.ub [1]).trace ≠ [7] := by decide
/-- `Outcome.isRunning` holds of a running outcome. -/
theorem outcome_isRunning_running (c : Cfg) : (Outcome.running c [1]).isRunning = true := rfl
/-- `Outcome.isRunning` fails for a UB outcome. -/
theorem outcome_isRunning_ub : (Outcome.ub [1]).isRunning = false := rfl
/-- `Outcome.cons (some v)` prepends `v`. -/
theorem outcome_cons_some : ((Outcome.ub [2]).cons (some 1)).trace = [1, 2] := rfl

/-- `prefixOf f k` has exactly `k` elements. -/
theorem prefixOf_neg : prefixOf (fun n => (n : Int)) 3 ≠ [0, 1] := by decide

/-- `GoesWrongFrom`: `unreachable` goes wrong with empty trace. -/
theorem goesWrongFrom_unreach (K : ZContract) (σ : State) :
    GoesWrongFrom K pUnreach (pUnreach.init σ) [] := ⟨1, rfl⟩
/-- `GoesWrongFrom`: `halt` never goes wrong. -/
theorem not_goesWrongFrom_halt (K : ZContract) (σ : State) (t : List Int) :
    ¬ GoesWrongFrom K pHalt (pHalt.init σ) t := by
  rintro ⟨n, hn⟩
  have := (hasBehFrom_iff_of_run_done (b := .wrong t)
    (show run K pHalt 1 (pHalt.init σ) = .done [] σ from rfl)).1 ⟨n, hn⟩
  cases this

/-- `EquivWT` holds between `emit 7; unreachable` and `unreachable` (both always reach
UB), although `EquivPP` does not (`not_equivPP_emitUnreach_unreach`). -/
theorem equivWT_emitUnreach_unreach (K : ZContract) : EquivWT K pEmitUnreach pUnreach :=
  ⟨refinesWT_emitUnreach_unreach K, refinesWT_of_refinesPP (refinesPP_of_src_unreach K _)⟩
theorem not_equivPP_emitUnreach_unreach (K : ZContract) : ¬ EquivPP K pEmitUnreach pUnreach :=
  fun h => not_refinesPP_emitUnreach_unreach K h.1
/-- `EquivWT` fails between `halt` and `unreachable`. -/
theorem not_equivWT_halt_unreach (K : ZContract) : ¬ EquivWT K pHalt pUnreach :=
  fun h => not_refinesWT_halt_unreach K h.1

/-- `copyProg` with count `0` terminates on aligned pointers under `aligned`. -/
theorem copyProg_aligned_term :
    HasBeh .aligned (copyProg 0 1 ⟨4, 4⟩ 0) (mkState [8, 8]) (.term []) := ⟨2, _, rfl⟩
/-- `copyProg` with count `0` reaches UB on a misaligned source under `aligned`. -/
theorem copyProg_misaligned_wrong :
    HasBeh .aligned (copyProg 0 1 ⟨4, 4⟩ 0) (mkState [1, 8]) (.wrong []) := ⟨1, rfl⟩
/-- `copyLoopProg` with count `0` checks no pointer and terminates. -/
theorem copyLoopProg_zero_term :
    HasBeh .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 0) (mkState [1, 8]) (.term []) := ⟨4, _, rfl⟩
/-- `copyLoopProg` with count `1` performs a 4-byte access and reaches UB on a
misaligned source. -/
theorem copyLoopProg_one_misaligned_wrong :
    HasBeh .aligned (copyLoopProg 0 1 2 ⟨4, 4⟩ 1) (mkState [1, 8]) (.wrong []) := ⟨4, rfl⟩

end Toy.ZstAssume
