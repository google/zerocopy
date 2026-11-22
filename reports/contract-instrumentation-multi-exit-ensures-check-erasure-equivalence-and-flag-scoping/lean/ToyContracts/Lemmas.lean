import ToyContracts.Programs

/-!
# Auxiliary lemmas (fully proved)
-/

namespace Toy.Contracts

/-! ## Halting observations -/

/-- Halting observations of a run that is `fuelOut` below fuel `k` and constant (and final) from
fuel `k` on: exactly that constant. -/
theorem halts_iff_of_run_const {c : Contract} {p : Fn} {x : Nat} (k : Nat) (o₀ : Obs)
    (hk : ∀ m, run c p x (m + k) = o₀) (hlt : ∀ n, n < k → (run c p x n).outcome = .fuelOut)
    (hfin : o₀.outcome ≠ .fuelOut) (o : Obs) : Halts c p x o ↔ o = o₀ := by
  constructor
  · rintro ⟨hne, n, hn⟩
    by_cases h : n < k
    · exact absurd (hn ▸ hlt n h) hne
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.le_of_not_lt h)
      rw [← hn, hk]
  · rintro rfl
    exact ⟨hfin, k, by simpa using hk 0⟩

/-- Fuel-exact identity implies identity of halting observations. -/
theorem haltsEqAt_of_runEqAt {c : Contract} {p q : Fn} {x : Nat} (h : RunEqAt c p q x) :
    HaltsEqAt c p q x := by
  intro o
  constructor
  · rintro ⟨hne, n, hn⟩; exact ⟨hne, n, (h n) ▸ hn⟩
  · rintro ⟨hne, n, hn⟩; exact ⟨hne, n, (h n).symm ▸ hn⟩

/-- A target with no halting observation at `x` UB-refines every source at `x`
(`UBRefinesAt` compares halting runs of the target only). -/
theorem ubRefinesAt_of_forall_not_halts {c : Contract} {tgt : Fn} {x : Nat}
    (h : ∀ o, ¬ Halts c tgt x o) (src : Fn) : UBRefinesAt c tgt src x :=
  fun o ho => absurd ho (h o)

/-! ## Statement lists -/

theorem execStmts_append (c : Contract) (x : Nat) (ss₁ ss₂ : List Stmt) (σ : Store)
    (ev : List Nat) :
    execStmts c x (ss₁ ++ ss₂) σ ev =
      match execStmts c x ss₁ σ ev with
      | .stop ev' o => .stop ev' o
      | .cont σ' ev' => execStmts c x ss₂ σ' ev' := by
  induction ss₁ generalizing σ ev with
  | nil => rfl
  | cons s ss ih =>
    cases s with
    | assign i rv => exact ih _ _
    | emit o => exact ih _ _
    | checkReq => simp only [List.cons_append, execStmts]; split; exact ih _ _; rfl
    | checkEns o => simp only [List.cons_append, execStmts]; split; exact ih _ _; rfl
    | assumeReq => simp only [List.cons_append, execStmts]; split; exact ih _ _; rfl

theorem execStmts_stop_outcome {c : Contract} {x : Nat} {ss : List Stmt} {σ : Store}
    {ev ev' : List Nat} {o : Outcome} (h : execStmts c x ss σ ev = .stop ev' o) :
    (∃ k, o = .checkFail k) ∨ o = .ub := by
  induction ss generalizing σ ev with
  | nil => cases h
  | cons s ss ih =>
    cases s with
    | assign i rv => exact ih h
    | emit op => exact ih h
    | checkReq =>
      simp only [execStmts] at h; split at h
      · exact ih h
      · cases h; exact .inl ⟨.pre, rfl⟩
    | checkEns op =>
      simp only [execStmts] at h; split at h
      · exact ih h
      · cases h; exact .inl ⟨.post, rfl⟩
    | assumeReq =>
      simp only [execStmts] at h; split at h
      · exact ih h
      · cases h; exact .inr rfl

theorem wrapObs_of_execStmts_stop {c : Contract} {x : Nat} {ss : List Stmt} {σ : Store}
    {ev ev' : List Nat} {o : Outcome} (h : execStmts c x ss σ ev = .stop ev' o) :
    wrapObs c x ⟨ev', o⟩ = ⟨ev', o⟩ := by
  rcases execStmts_stop_outcome h with ⟨k, rfl⟩ | rfl <;> rfl

theorem execStmts_no_stop_of_all {c : Contract} {x : Nat} {ss : List Stmt}
    (hnc : ss.all (fun s => !s.isContract) = true) (σ : Store) (ev : List Nat) :
    ∃ σ' ev', execStmts c x ss σ ev = .cont σ' ev' := by
  induction ss generalizing σ ev with
  | nil => exact ⟨σ, ev, rfl⟩
  | cons s ss ih =>
    simp only [List.all_cons, Bool.and_eq_true, Bool.not_eq_true'] at hnc
    cases s with
    | assign i rv => exact ih hnc.2 _ _
    | emit op => exact ih hnc.2 _ _
    | checkReq | checkEns _ | assumeReq => cases hnc.1

/-! ## Runs of functions without contract statements -/

theorem runFrom_no_checkFail_of_blocks {c : Contract} {f : Fn}
    (hb : f.blocks.all (fun blk => blk.stmts.all (fun s => !s.isContract)) = true)
    (x n b : Nat) (σ : Store) (ev : List Nat) (k : CheckKind) :
    (runFrom c f x n b σ ev).outcome ≠ .checkFail k := by
  induction n generalizing b σ ev with
  | zero => nofun
  | succ n ih =>
    simp only [runFrom]
    cases hblk : f.blocks[b]? with
    | none => nofun
    | some blk =>
      dsimp only
      have hst : blk.stmts.all (fun s => !s.isContract) = true := by
        simpa using List.all_eq_true.mp hb blk (List.mem_of_getElem? hblk)
      obtain ⟨σ', ev', hex⟩ := execStmts_no_stop_of_all (c := c) (x := x) hst σ ev
      rw [hex]; dsimp only
      cases blk.term with
      | goto b' => exact ih b' σ' ev'
      | branch o b₁ b₀ => exact ih _ σ' ev'
      | tryQ o e b' => dsimp only; split; nofun; exact ih b' σ' ev'
      | ret _ _ => nofun
      | panic => nofun

/-- A function without contract statements never ends with a failed check. -/
theorem run_no_checkFail_of_noChecks {c : Contract} {f : Fn} (hnc : NoChecks f)
    (x n : Nat) (k : CheckKind) : (run c f x n).outcome ≠ .checkFail k := by
  obtain ⟨hp, hb⟩ := hnc
  obtain ⟨σ, ev, hex⟩ := execStmts_no_stop_of_all (c := c) (x := x) hp (fun _ => 0) []
  simp only [run, hex]
  exact runFrom_no_checkFail_of_blocks hb x n f.entry σ ev k

/-! ## Instrumentation -/

theorem runFrom_instr_allExits_eq_wrapObs (c : Contract) (g : Fn) (hg : Lowered g)
    (x n b : Nat) (σ : Store) (ev : List Nat) :
    runFrom c (instr .allExits g) x n b σ ev = wrapObs c x (runFrom c g x n b σ ev) := by
  induction n generalizing b σ ev with
  | zero => rfl
  | succ n ih =>
    simp only [runFrom, instr, List.getElem?_map]
    cases hblk : g.blocks[b]? with
    | none => rfl
    | some blk =>
      have hnotry : (!blk.term.isTryQ) = true := by
        simpa using List.all_eq_true.mp hg blk (List.mem_of_getElem? hblk)
      simp only [Option.map_some]
      cases ht : blk.term with
      | goto b' =>
        simp only [instrBlock, ht]
        cases hex : execStmts c x blk.stmts σ ev with
        | stop ev' o => exact (wrapObs_of_execStmts_stop hex).symm
        | cont σ' ev' => exact ih b' σ' ev'
      | branch o b₁ b₀ =>
        simp only [instrBlock, ht]
        cases hex : execStmts c x blk.stmts σ ev with
        | stop ev' o => exact (wrapObs_of_execStmts_stop hex).symm
        | cont σ' ev' => exact ih _ σ' ev'
      | tryQ o e b' => rw [ht] at hnotry; cases hnotry
      | panic =>
        simp only [instrBlock, ht]
        cases hex : execStmts c x blk.stmts σ ev with
        | stop ev' o => exact (wrapObs_of_execStmts_stop hex).symm
        | cont σ' ev' => rfl
      | ret k o =>
        simp only [instrBlock, ht, Placement.selects, ↓reduceIte, execStmts_append]
        cases hex : execStmts c x blk.stmts σ ev with
        | stop ev' o' => exact (wrapObs_of_execStmts_stop hex).symm
        | cont σ' ev' =>
          simp only [execStmts, wrapObs]
          cases c.ens x (evalOp x σ' o) <;> rfl

/-- If every normal return reachable from block `b` satisfies `Ens`, instrumentation with any
placement (inserted checks at arbitrary `ret` edges, `?` exits unchecked) does not change the run
from `b`. -/
theorem runFrom_instr_eq_of_ens (c : Contract) (p : Placement) (g : Fn) (x n b : Nat)
    (σ : Store) (ev : List Nat)
    (hens : ∀ m tr r, runFrom c g x m b σ ev = ⟨tr, .ret r⟩ → c.ens x r = true) :
    runFrom c (instr p g) x n b σ ev = runFrom c g x n b σ ev := by
  induction n generalizing b σ ev with
  | zero => rfl
  | succ n ih =>
    simp only [runFrom, instr, List.getElem?_map]
    cases hblk : g.blocks[b]? with
    | none => rfl
    | some blk =>
      simp only [Option.map_some]
      cases ht : blk.term with
      | goto b' =>
        simp only [instrBlock, ht]
        cases hex : execStmts c x blk.stmts σ ev with
        | stop ev' o => rfl
        | cont σ' ev' =>
          exact ih b' σ' ev' fun m tr r hm =>
            hens (m + 1) tr r (by simp [runFrom, hblk, hex, ht, hm])
      | branch o b₁ b₀ =>
        simp only [instrBlock, ht]
        cases hex : execStmts c x blk.stmts σ ev with
        | stop ev' o => rfl
        | cont σ' ev' =>
          exact ih _ σ' ev' fun m tr r hm =>
            hens (m + 1) tr r (by simp [runFrom, hblk, hex, ht, hm])
      | tryQ o e b' =>
        simp only [instrBlock, ht]
        cases hex : execStmts c x blk.stmts σ ev with
        | stop ev' o => rfl
        | cont σ' ev' =>
          dsimp only; split
          · rfl
          · next hne =>
            exact ih b' σ' ev' fun m tr r hm =>
              hens (m + 1) tr r (by simp [runFrom, hblk, hex, ht, hne, hm])
      | panic =>
        simp only [instrBlock, ht]
      | ret k o =>
        simp only [instrBlock, ht]
        cases hp : p.selects k
        · simp [ht]
        · simp only [↓reduceIte, execStmts_append]
          cases hex : execStmts c x blk.stmts σ ev with
          | stop ev' o' => rfl
          | cont σ' ev' =>
            have hr : c.ens x (evalOp x σ' o) = true :=
              hens 1 ev' (evalOp x σ' o) (by simp [runFrom, hblk, hex, ht])
            simp [execStmts, hr]

/-- On an input with `Req x` at which every normal return of `g` satisfies `Ens`, instrumentation
with any placement does not change the run, at every fuel (no `Lowered` or `NoChecks` needed). -/
theorem run_instr_eq_of_req_of_ensOnReturnsAt (c : Contract) (p : Placement) (g : Fn) (x : Nat)
    (hreq : c.req x = true) (hens : EnsOnReturnsAt c g x) (n : Nat) :
    run c (instr p g) x n = run c g x n := by
  simp only [run, instr, execStmts, hreq, ↓reduceIte]
  cases hex : execStmts c x g.prologue (fun _ => 0) [] with
  | stop ev o => rfl
  | cont σ ev =>
    exact runFrom_instr_eq_of_ens c p g x n g.entry σ ev fun m tr r hm =>
      hens tr r ⟨nofun, m, by simp [run, hex, hm]⟩

/-- Off `Req`, every instrumentation stops at its first prologue statement with a `requires`
failure and no events, at every fuel. -/
theorem run_instr_of_req_false (c : Contract) (p : Placement) (g : Fn) (x : Nat)
    (h : c.req x = false) (n : Nat) : run c (instr p g) x n = ⟨[], .checkFail .pre⟩ := by
  simp [run, instr, execStmts, h]

/-- On an input with `Req x` at which every normal return of `g` satisfies `Ens`, the contract
wrapper leaves the run of `g` unchanged, at every fuel. -/
theorem instrObs_run_eq_of_req_of_ensOnReturnsAt (c : Contract) (g : Fn) (x : Nat)
    (hreq : c.req x = true) (hens : EnsOnReturnsAt c g x) (n : Nat) :
    instrObs c x (run c g x n) = run c g x n := by
  simp only [instrObs, hreq, ↓reduceIte]
  cases hrun : run c g x n with
  | mk tr out =>
    cases out with
    | ret r => simp [wrapObs, hens tr r ⟨nofun, n, hrun⟩]
    | _ => rfl

/-- If the contract wrapper of a run of `g` is a normal return of `r`, then `Req x`, `Ens x r`,
and the run of `g` itself is that return. -/
theorem instrObs_eq_ret {c : Contract} {x : Nat} {o : Obs} {tr : List Nat} {r : Nat}
    (h : instrObs c x o = ⟨tr, .ret r⟩) : c.req x = true ∧ c.ens x r = true ∧ o = ⟨tr, .ret r⟩ := by
  unfold instrObs at h
  cases hreq : c.req x <;> rw [hreq] at h
  · cases h
  · simp only [↓reduceIte] at h
    obtain ⟨ev, out⟩ := o
    cases out with
    | ret r' =>
      simp only [wrapObs] at h
      cases hens : c.ens x r' <;> rw [hens] at h
      · cases h
      · cases h; exact ⟨rfl, hens, rfl⟩
    | _ => simp only [wrapObs] at h; cases h

/-! ## Determinism -/

theorem runFrom_mono {c : Contract} {f : Fn} {x n m b : Nat} {σ : Store} {ev : List Nat}
    (hfin : (runFrom c f x n b σ ev).outcome ≠ .fuelOut) (hle : n ≤ m) :
    runFrom c f x m b σ ev = runFrom c f x n b σ ev := by
  induction n generalizing m b σ ev with
  | zero => exact absurd rfl hfin
  | succ n ih =>
    cases m with
    | zero => omega
    | succ m =>
      simp only [runFrom] at hfin ⊢
      cases hblk : f.blocks[b]? with
      | none => rfl
      | some blk =>
        rw [hblk] at hfin; dsimp only at hfin ⊢
        cases hex : execStmts c x blk.stmts σ ev with
        | stop ev' o => rfl
        | cont σ' ev' =>
          rw [hex] at hfin; dsimp only at hfin ⊢
          cases ht : blk.term with
          | goto b' => rw [ht] at hfin; exact ih hfin (Nat.le_of_succ_le_succ hle)
          | branch o b₁ b₀ => rw [ht] at hfin; exact ih hfin (Nat.le_of_succ_le_succ hle)
          | tryQ o e b' =>
            rw [ht] at hfin; dsimp only at hfin ⊢
            by_cases heq : evalOp x σ' o = 0
            · simp [heq]
            · simp only [heq, ↓reduceIte] at hfin ⊢
              exact ih hfin (Nat.le_of_succ_le_succ hle)
          | ret _ _ => rfl
          | panic => rfl

/-- Fuel monotonicity: once a run has ended (not `fuelOut`), more fuel gives the same observation. -/
theorem run_mono {c : Contract} {f : Fn} {x n m : Nat}
    (hfin : (run c f x n).outcome ≠ .fuelOut) (hle : n ≤ m) :
    run c f x m = run c f x n := by
  simp only [run] at hfin ⊢
  cases hex : execStmts c x f.prologue (fun _ => 0) [] with
  | stop ev o => rfl
  | cont σ ev => rw [hex] at hfin; exact runFrom_mono hfin hle

/-- Determinism: a function has at most one halting observation on each input. -/
theorem halts_unique {c : Contract} {f : Fn} {x : Nat} {o₁ o₂ : Obs}
    (h₁ : Halts c f x o₁) (h₂ : Halts c f x o₂) : o₁ = o₂ := by
  obtain ⟨hf₁, n₁, hn₁⟩ := h₁
  obtain ⟨hf₂, n₂, hn₂⟩ := h₂
  by_cases hle : n₁ ≤ n₂
  · rw [← hn₂, run_mono (hn₁ ▸ hf₁) hle, hn₁]
  · rw [← hn₁, run_mono (hn₂ ▸ hf₂) (Nat.le_of_not_le hle), hn₂]

/-! ## Lowering -/

theorem lowered_lower (f : Fn) : Lowered (lower f) := by
  unfold Lowered lower
  rw [List.all_append, Bool.and_eq_true, List.all_map]
  refine ⟨List.all_eq_true.mpr fun blk hblk => ?_, List.all_eq_true.mpr fun blk _ => ?_⟩
  · rw [List.mem_iff_getElem] at hblk
    obtain ⟨i, hi, rfl⟩ := hblk
    have _hi' : i < f.blocks.length := by simpa using hi
    simp only [List.getElem_mapIdx]
    cases f.blocks[i].term <;> rfl
  · dsimp only [Function.comp_apply, errBlock]
    cases blk.term <;> rfl

theorem lower_blocks_lt (f : Fn) {b : Nat} (hb : b < f.blocks.length) :
    (lower f).blocks[b]? =
      (f.blocks[b]?).map (fun blk => { blk with term := lowerTerm f.blocks.length b blk.term }) := by
  simp only [lower]
  rw [List.getElem?_append_left (by simp [hb]), List.getElem?_mapIdx]

theorem lower_blocks_add (f : Fn) (b : Nat) :
    (lower f).blocks[f.blocks.length + b]? = (f.blocks[b]?).map errBlock := by
  simp only [lower]
  rw [List.getElem?_append_right (by simp)]
  simp [List.getElem?_map]

theorem runFrom_succ (c : Contract) (f : Fn) (x n b : Nat) (σ : Store) (ev : List Nat) :
    runFrom c f x (n + 1) b σ ev =
      match f.blocks[b]? with
      | none => ⟨ev, .stuck⟩
      | some blk =>
        match execStmts c x blk.stmts σ ev with
        | .stop ev' o => ⟨ev', o⟩
        | .cont σ' ev' =>
          match blk.term with
          | .goto b' => runFrom c f x n b' σ' ev'
          | .branch o b₁ b₀ => runFrom c f x n (if evalOp x σ' o = 0 then b₀ else b₁) σ' ev'
          | .tryQ o e b' =>
              if evalOp x σ' o = 0 then ⟨ev', .ret (evalOp x σ' e)⟩ else runFrom c f x n b' σ' ev'
          | .ret _ o => ⟨ev', .ret (evalOp x σ' o)⟩
          | .panic => ⟨ev', .panic⟩ := rfl

/-- A halting run of `f` from an in-range block at fuel `n` is reproduced by `lower f` at fuel
`n + 1` (one extra block execution for a final `?` error exit). -/
theorem runFrom_lower_of_fin {c : Contract} {f : Fn}
    (htgt : f.blocks.all (fun blk => blk.term.targets.all (· < f.blocks.length)) = true)
    (x n : Nat) {b : Nat} (hb : b < f.blocks.length) (σ : Store) (ev : List Nat)
    (hfin : (runFrom c f x n b σ ev).outcome ≠ .fuelOut) :
    runFrom c (lower f) x (n + 1) b σ ev = runFrom c f x n b σ ev := by
  induction n generalizing b σ ev with
  | zero => exact absurd rfl hfin
  | succ n ih =>
    rw [runFrom_succ c (lower f) x (n + 1) b σ ev, runFrom_succ c f x n b σ ev]
    rw [runFrom_succ c f x n b σ ev] at hfin
    cases hblk : f.blocks[b]? with
    | none => exact absurd hblk (by simp [hb])
    | some blk =>
      have hbt : blk.term.targets.all (· < f.blocks.length) = true := by
        simpa using List.all_eq_true.mp htgt blk (List.mem_of_getElem? hblk)
      rw [lower_blocks_lt f hb, hblk]; rw [hblk] at hfin
      dsimp only [Option.map_some] at hfin ⊢
      cases hex : execStmts c x blk.stmts σ ev with
      | stop ev' o => rfl
      | cont σ' ev' =>
        rw [hex] at hfin; dsimp only at hfin ⊢
        cases ht : blk.term with
        | goto b' =>
          rw [ht] at hbt hfin
          simp only [Term.targets, List.all_cons, List.all_nil, Bool.and_true,
            decide_eq_true_eq] at hbt
          exact ih hbt _ _ hfin
        | branch o b₁ b₀ =>
          rw [ht] at hbt hfin
          simp only [Term.targets, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
            decide_eq_true_eq] at hbt
          dsimp only [lowerTerm] at hfin ⊢
          by_cases heq : evalOp x σ' o = 0
          · simp only [heq, ↓reduceIte] at hfin ⊢; exact ih hbt.2 _ _ hfin
          · simp only [heq, ↓reduceIte] at hfin ⊢; exact ih hbt.1 _ _ hfin
        | tryQ o e b' =>
          rw [ht] at hbt hfin
          simp only [Term.targets, List.all_cons, List.all_nil, Bool.and_true,
            decide_eq_true_eq] at hbt
          dsimp only [lowerTerm] at hfin ⊢
          by_cases heq : evalOp x σ' o = 0
          · simp only [heq, ↓reduceIte]
            rw [runFrom_succ, lower_blocks_add f b, hblk]
            dsimp only [Option.map_some, errBlock]; rw [ht]; rfl
          · simp only [heq, ↓reduceIte] at hfin ⊢; exact ih hbt _ _ hfin
        | ret _ _ => rfl
        | panic => rfl

/-- A halting run of `lower f` from an in-range block at fuel `n` is already a halting run of `f`
at fuel `n`. -/
theorem runFrom_of_lower_fin {c : Contract} {f : Fn}
    (htgt : f.blocks.all (fun blk => blk.term.targets.all (· < f.blocks.length)) = true)
    (x n : Nat) {b : Nat} (hb : b < f.blocks.length) (σ : Store) (ev : List Nat)
    (hfin : (runFrom c (lower f) x n b σ ev).outcome ≠ .fuelOut) :
    runFrom c f x n b σ ev = runFrom c (lower f) x n b σ ev := by
  induction n generalizing b σ ev with
  | zero => exact absurd rfl hfin
  | succ n ih =>
    rw [runFrom_succ c f x n b σ ev, runFrom_succ c (lower f) x n b σ ev]
    rw [runFrom_succ c (lower f) x n b σ ev] at hfin
    cases hblk : f.blocks[b]? with
    | none => exact absurd hblk (by simp [hb])
    | some blk =>
      have hbt : blk.term.targets.all (· < f.blocks.length) = true := by
        simpa using List.all_eq_true.mp htgt blk (List.mem_of_getElem? hblk)
      rw [lower_blocks_lt f hb, hblk]; rw [lower_blocks_lt f hb, hblk] at hfin
      dsimp only [Option.map_some] at hfin ⊢
      cases hex : execStmts c x blk.stmts σ ev with
      | stop ev' o => rfl
      | cont σ' ev' =>
        rw [hex] at hfin; dsimp only at hfin ⊢
        cases ht : blk.term with
        | goto b' =>
          rw [ht] at hbt hfin
          simp only [Term.targets, List.all_cons, List.all_nil, Bool.and_true,
            decide_eq_true_eq] at hbt
          exact ih hbt _ _ hfin
        | branch o b₁ b₀ =>
          rw [ht] at hbt hfin
          simp only [Term.targets, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
            decide_eq_true_eq] at hbt
          dsimp only [lowerTerm] at hfin ⊢
          by_cases heq : evalOp x σ' o = 0
          · simp only [heq, ↓reduceIte] at hfin ⊢; exact ih hbt.2 _ _ hfin
          · simp only [heq, ↓reduceIte] at hfin ⊢; exact ih hbt.1 _ _ hfin
        | tryQ o e b' =>
          rw [ht] at hbt hfin
          simp only [Term.targets, List.all_cons, List.all_nil, Bool.and_true,
            decide_eq_true_eq] at hbt
          dsimp only [lowerTerm] at hfin ⊢
          by_cases heq : evalOp x σ' o = 0
          · simp only [heq, ↓reduceIte] at hfin ⊢
            cases n with
            | zero => exact absurd rfl hfin
            | succ m =>
              rw [runFrom_succ, lower_blocks_add f b, hblk]
              dsimp only [Option.map_some, errBlock]; rw [ht]; rfl
          · simp only [heq, ↓reduceIte] at hfin ⊢; exact ih hbt _ _ hfin
        | ret _ _ => rfl
        | panic => rfl

/-! ## Erasure -/

theorem filter_not_isContract_of_all {ss : List Stmt}
    (h : ss.all (fun s => !s.isContract) = true) :
    ss.filter (fun s => !s.isContract) = ss :=
  List.filter_eq_self.mpr (fun s hs => List.all_eq_true.mp h s hs)

theorem filter_checkReq_cons (ss : List Stmt) :
    (.checkReq :: ss).filter (fun s => !s.isContract) = ss.filter (fun s => !s.isContract) := rfl

theorem filter_checkEns_singleton (o : Operand) :
    ([Stmt.checkEns o]).filter (fun s => !s.isContract) = [] := rfl

theorem erase_instrBlock_eq {blk : Block} (p : Placement)
    (h : blk.stmts.all (fun s => !s.isContract) = true) :
    { (instrBlock p blk) with
        stmts := (instrBlock p blk).stmts.filter (fun s => !s.isContract) } = blk := by
  cases blk with
  | mk stmts term =>
    cases term with
    | ret k o =>
      dsimp only [instrBlock]
      cases p.selects k
      · change Block.mk (stmts.filter (fun s => !s.isContract)) (.ret k o) = _
        rw [filter_not_isContract_of_all h]
      · change Block.mk ((stmts ++ [Stmt.checkEns o]).filter (fun s => !s.isContract))
          (.ret k o) = _
        rw [List.filter_append, filter_checkEns_singleton, List.append_nil,
          filter_not_isContract_of_all h]
    | _ =>
      dsimp only [instrBlock]
      rw [filter_not_isContract_of_all h]

theorem map_erase_instrBlock {blks : List Block} (p : Placement)
    (hb : blks.all (fun blk => blk.stmts.all (fun s => !s.isContract)) = true) :
    (blks.map (instrBlock p)).map
        (fun blk => { blk with stmts := blk.stmts.filter (fun s => !s.isContract) }) = blks := by
  induction blks with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hb
    simp only [List.map_cons, erase_instrBlock_eq p hb.1, ih hb.2]

/-- The erasure of any function contains no contract statement. -/
theorem noChecks_erase (p : Fn) : NoChecks (erase p) := by
  unfold NoChecks erase
  refine ⟨List.all_eq_true.mpr fun s hs => ?_, List.all_eq_true.mpr fun blk hblk => ?_⟩
  · exact (List.mem_filter.mp hs).2
  · obtain ⟨blk₀, _, rfl⟩ := List.mem_map.mp hblk
    exact List.all_eq_true.mpr fun s hs => (List.mem_filter.mp hs).2

/-- Runs from a block depend on the blocks of the function and not on its prologue or entry. -/
theorem runFrom_congr_blocks (c : Contract) (f₁ f₂ : Fn) (hb : f₁.blocks = f₂.blocks)
    (x n b : Nat) (σ : Store) (ev : List Nat) :
    runFrom c f₁ x n b σ ev = runFrom c f₂ x n b σ ev := by
  induction n generalizing b σ ev with
  | zero => rfl
  | succ n ih =>
    simp only [runFrom, hb]
    cases f₂.blocks[b]? with
    | none => rfl
    | some blk =>
      dsimp only
      cases execStmts c x blk.stmts σ ev with
      | stop ev' o => rfl
      | cont σ' ev' =>
        dsimp only
        cases blk.term with
        | goto b' => exact ih b' σ' ev'
        | branch o b₁ b₀ => exact ih _ σ' ev'
        | tryQ o e b' => dsimp only; split; rfl; exact ih b' σ' ev'
        | ret _ _ => rfl
        | panic => rfl

/-! ## Concrete runs -/

/-- A run of the emitting loop `gLoop` never ends: at fuel `n` it has emitted `n` ones. -/
theorem runFrom_gLoop (x : Nat) : ∀ n σ ev,
    runFrom c1 gLoop x n 0 σ ev = ⟨ev ++ List.replicate n 1, .fuelOut⟩ := by
  intro n
  induction n with
  | zero => intro σ ev; simp [runFrom]
  | succ n ih =>
    intro σ ev
    have h : runFrom c1 gLoop x (n + 1) 0 σ ev = runFrom c1 gLoop x n 0 σ (ev ++ [1]) := rfl
    rw [h, ih]
    simp [List.replicate_succ]

/-- Under resolution at the definition, the governing crate is the crate holding the check. -/
theorem governingCrate_atDefinition (s : Site) (cs : CallSite) :
    governingCrate s .atDefinition cs = holder s cs := by
  cases s <;> rfl

/-- Compile-time evaluation that evaluates checks runs the function itself. -/
theorem ctfeRun_evalChecks_eq (c : Contract) (p : Fn) (x n : Nat) :
    ctfeRun .evalChecks c p x n = run c p x n := rfl

end Toy.Contracts
