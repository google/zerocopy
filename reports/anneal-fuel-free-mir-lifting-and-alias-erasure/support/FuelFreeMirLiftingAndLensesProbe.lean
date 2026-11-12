-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

/-!
# Self-Contained Mechanized Probe: Fuel-Free MIR Lifting and Alias Erasure

Standalone Lean 4 (`v4.34.1`) mechanization accompanying
`reports/anneal-fuel-free-mir-lifting-and-alias-erasure/REPORT.md`.
Requires only Lean 4 `Init` (zero external Lake dependencies, zero `sorry`,
standard axioms only).

Mechanizes six core architectural results across twenty-two exported theorems:
1. **Kleene Fuel Monotonicity & Fuel-Free Convergence (`FuelOrder`,
   `WpConverges`, `evalFuel_mono`, `StepsTo.bind_wp`)**: existential step
   synthesis over a `prelude`-compatible fueled small-step interpreter
   (`evalFuel`), keeping `WellFounded.fix` and `Classical.choice` out of TCB.
2. **Tier 1 Syntactic Purity & Alias Erasure (`PureState`, `MachineState`,
   `MirFrameSim`, `checkPureProg_rejects_deref`, `stepPure_simulates`,
   `wpConverges_of_pureExec`)**: proving once and for all that syntactic
   absence of pointer dereferences and address-taking rvalues erases `Memory`.
3. **Opaque-Body `LiftBlock` & Flat Environment Normalization (`LiftBlock`,
   `twoDiamondCfg`, `liftBlock_diamond_shared`, `forcePureEnv`,
   `set_eq_of_forcePureEnv`, `chained_sets_collapse_rfl`)**: sharing join-block
   `LiftBlock` theorems across sequential `if`-diamonds over an opaque `post`
   and collapsing sequential `List.set` chains to a flat list literal by `rfl`.
4. **Fuel-Free Bounded Range Loops & Target-Block Stepping (`forRangeUp`,
   `forRangeUp_induction`, `wpConverges_forRangeUp`, `runToTarget`,
   `stepsTo_of_runToTarget_reached`, `wpConverges_of_runToTarget_halted`,
   `runToTarget_mono_bound`, `runCfgToBlock`,
   `stepsTo_of_runCfgToBlock_reached`, `wpConverges_of_runCfgToBlock_halted`,
   `no_uniform_fuel_countUp`, `countUp_wpConverges_all_n`)**: proving target
   block stepping without overshooting, impossibility of uniform constant fuel
   on symbolic `[0, n)` loops, and zero-numeral convergence for all `n`.
5. **Tier 2 Separation-Logic Lenses (`MutLens`, `DisjointLenses`,
   `subplaceFieldLens_disjoint`, `liftLens_twoBorrowAdd_sound`)**: erasing
   pointer/borrow aliasing for whole-slot and sibling-field (`&mut`) mutations.
6. **Scalars, Callee Stack Suffixes, Transmute Layouts, & Field-0 Subplaces
   (`signExtendMod_nonneg_id`, `pushBaseStack_step_comm`,
   `instantiated_transmute_roundtrip`,
   `subplaceWrite_sibling_preserves_field0`)**: modular sign extension,
   stack-suffix frame invariance, monomorphic layout and function-pointer
   provenance across `transmute`, and sibling-field write framing at offset `0`.
-/

namespace FuelFreeMirLiftingProbe

/-! ## 1. Kleene Fuel Order and Fuel-Free Weakest Precondition -/

/-- Outcome of a bounded-fuel operational interpreter. -/
inductive FuelResult (α : Type) where
  | outOfFuel : FuelResult α
  | halted (v : α) : FuelResult α
  | faulted : FuelResult α
  deriving DecidableEq, Repr

/-- Flat Kleene information order: `outOfFuel` is bottom; `halted v` and
`faulted` are maximal terminal outcomes. -/
def FuelOrder {α : Type} : FuelResult α → FuelResult α → Prop
  | .outOfFuel, _ => True
  | .halted v₁, .halted v₂ => v₁ = v₂
  | .faulted, .faulted => True
  | _, _ => False

theorem FuelOrder.refl {α : Type} (r : FuelResult α) : FuelOrder r r := by
  cases r <;> trivial

theorem FuelOrder.trans {α : Type} {r₁ r₂ r₃ : FuelResult α}
    (h₁₂ : FuelOrder r₁ r₂) (h₂₃ : FuelOrder r₂ r₃) : FuelOrder r₁ r₃ := by
  cases r₁ <;> cases r₂ <;> cases r₃ <;> simp_all [FuelOrder]

theorem FuelOrder.halted_stable {α : Type} {v : α} {r : FuelResult α}
    (h : FuelOrder (.halted v) r) : r = .halted v := by
  cases r <;> simp_all [FuelOrder]

/-- Deterministic small-step transition relation outcome. -/
inductive Step (σ α : Type) where
  | cont (next : σ) : Step σ α
  | done (ret : α) : Step σ α
  | fault : Step σ α

/-- Fueled TCB-style evaluator using structural recursion on `fuel : Nat`. -/
def evalFuel {σ α : Type} (step : σ → Step σ α) : Nat → σ → FuelResult α
  | 0, _ => .outOfFuel
  | k + 1, s =>
    match step s with
    | .cont s' => evalFuel step k s'
    | .done v => .halted v
    | .fault => .faulted

/-- Adding fuel preserves every terminal outcome (`FuelOrder` monotonicity). -/
theorem evalFuel_mono {σ α : Type} (step : σ → Step σ α) :
    ∀ {k₁ k₂ : Nat} (s : σ), k₁ ≤ k₂ →
      FuelOrder (evalFuel step k₁ s) (evalFuel step k₂ s)
  | 0, _, _, _ => trivial
  | k₁ + 1, 0, _, hle => absurd hle (Nat.not_lt_of_ge (Nat.zero_le _))
  | k₁ + 1, k₂ + 1, s, hle => by
    unfold evalFuel
    cases step s with
    | cont s' => exact evalFuel_mono step s' (Nat.le_of_succ_le_succ hle)
    | done v => rfl
    | fault => trivial

/-- Fuel-free total convergence predicate: there exists some finite budget `k`
under which `evalFuel` halts at a value satisfying `post`. -/
def WpConverges {σ α : Type}
    (step : σ → Step σ α) (s : σ) (post : α → Prop) : Prop :=
  ∃ k v, evalFuel step k s = .halted v ∧ post v

/-- Terminal-step rule: a state whose transition immediately returns `.done v`
satisfies `WpConverges` without exposing any numeric step literal to callers. -/
theorem WpConverges.of_done {σ α : Type}
    {step : σ → Step σ α} {s : σ} {v : α} {post : α → Prop}
    (hd : step s = .done v) (hp : post v) :
    WpConverges step s post :=
  ⟨1, v, by simp [evalFuel, hd], hp⟩

/-- Multi-step segment convergence from `s` to an intermediate state satisfying
`mid` without halting early. -/
inductive StepsTo {σ α : Type}
    (step : σ → Step σ α) : σ → (σ → Prop) → Prop where
  | refl {s : σ} {mid : σ → Prop} (h : mid s) : StepsTo step s mid
  | step {s s' : σ} {mid : σ → Prop}
      (hstep : step s = .cont s')
      (hrest : StepsTo step s' mid) :
      StepsTo step s mid

/-- Sequential bind rule: fuel budgets are synthesized existentially across
segments (`1 + k`), so user proofs never mention fuel numerals. -/
theorem StepsTo.bind_wp {σ α : Type} {step : σ → Step σ α} {s : σ}
    {mid : σ → Prop} {post : α → Prop}
    (hseg : StepsTo step s mid)
    (hcont : ∀ s₁, mid s₁ → WpConverges step s₁ post) :
    WpConverges step s post := by
  induction hseg with
  | refl hm => exact hcont _ hm
  | @step s₀ s' _ hs _ ih =>
    obtain ⟨k, v, heval, hpost⟩ := ih hcont
    refine ⟨k + 1, v, ?_, hpost⟩
    simp [evalFuel, hs, heval]

/-! ## 2. Tier 1 Syntactic Purity and Alias Erasure -/

/-- Representative multi-field memory state standing in for Anneal's 12-field
`Memory` record (`nextAllocId`, `globals`, `borrows`, `nextTag`, `callees`,
`traitImpls`, `callStack`, `activeCallee`, `activeProtectors`, `nextProtector`,
`callerLocals`, and `fnPtrs`). -/
structure Memory where
  borrows : List (Nat × Nat)
  callerSlots : List Nat
  nextTag : Nat
  deriving DecidableEq, Repr

/-- Local slot state in an activation frame. -/
inductive SlotState where
  | uninit : SlotState
  | val (n : Nat) : SlotState
  deriving DecidableEq, Repr

/-- Full stateful machine configuration (`frame` + `Memory`). -/
structure MachineState where
  pc : Nat
  locals : List SlotState
  memory : Memory
  deriving DecidableEq, Repr

/-- Alias-erased local configuration (`pc` + `env`, with `Memory` erased). -/
structure PureState where
  pc : Nat
  env : List SlotState
  deriving DecidableEq, Repr

/-- Frame simulation relating `ps : PureState` to `ms : MachineState` at an
arbitrary caller memory `mem₀`. -/
def MirFrameSim (mem₀ : Memory) (ps : PureState) (ms : MachineState) : Prop :=
  ms.pc = ps.pc ∧ ms.locals = ps.env ∧ ms.memory = mem₀

/-- Minimal MIR statement model mixing pure local arithmetic and memory-touching
pointer dereferences. -/
inductive ToyStmt where
  | assignConst (dst : Nat) (c : Nat) : ToyStmt
  | assignAdd (dst lhs rhs : Nat) : ToyStmt
  | derefRead (dst ptrSlot : Nat) : ToyStmt
  | derefWrite (ptrSlot src : Nat) : ToyStmt
  | ret (slot : Nat) : ToyStmt

/-- Computable syntactic purity predicate rejecting pointer dereferences. -/
def checkPureStmt : ToyStmt → Bool
  | .assignConst _ _ => true
  | .assignAdd _ _ _ => true
  | .derefRead _ _ => false
  | .derefWrite _ _ => false
  | .ret _ => true

def checkPureProg (prog : List ToyStmt) : Bool :=
  prog.all checkPureStmt

/-- Negative purity canary: dereference reads and writes are syntactically
rejected before any operational step is attempted. -/
theorem checkPureProg_rejects_deref :
    checkPureProg [.derefRead 0 1, .ret 0] = false ∧
      checkPureProg [.derefWrite 0 1, .ret 0] = false :=
  ⟨rfl, rfl⟩

def readSlot? (env : List SlotState) (idx : Nat) : Option Nat :=
  match env[idx]? with
  | some (.val n) => some n
  | _ => none

def stepMachine (prog : List ToyStmt) (ms : MachineState) :
    Step MachineState (Nat × Memory) :=
  match prog[ms.pc]? with
  | none => .fault
  | some (.assignConst dst c) =>
    if dst < ms.locals.length then
      .cont { ms with pc := ms.pc + 1, locals := ms.locals.set dst (.val c) }
    else .fault
  | some (.assignAdd dst lhs rhs) =>
    match readSlot? ms.locals lhs, readSlot? ms.locals rhs with
    | some a, some b =>
      if dst < ms.locals.length then
        let locals' := ms.locals.set dst (.val (a + b))
        .cont { ms with pc := ms.pc + 1, locals := locals' }
      else .fault
    | _, _ => .fault
  | some (.derefRead dst ptrSlot) =>
    match readSlot? ms.locals ptrSlot with
    | some addr =>
      match ms.memory.callerSlots[addr]? with
      | some v =>
        if dst < ms.locals.length then
          let locals' := ms.locals.set dst (.val v)
          .cont { ms with pc := ms.pc + 1, locals := locals' }
        else .fault
      | none => .fault
    | none => .fault
  | some (.derefWrite ptrSlot src) =>
    match readSlot? ms.locals ptrSlot, readSlot? ms.locals src with
    | some addr, some v =>
      if addr < ms.memory.callerSlots.length then
        let slots' := ms.memory.callerSlots.set addr v
        let mem' := { ms.memory with callerSlots := slots' }
        .cont { ms with pc := ms.pc + 1, memory := mem' }
      else .fault
    | _, _ => .fault
  | some (.ret slot) =>
    match readSlot? ms.locals slot with
    | some v => .done (v, ms.memory)
    | none => .fault

def stepPure (prog : List ToyStmt) (ps : PureState) : Step PureState Nat :=
  match prog[ps.pc]? with
  | none => .fault
  | some (.assignConst dst c) =>
    if dst < ps.env.length then
      .cont { pc := ps.pc + 1, env := ps.env.set dst (.val c) }
    else .fault
  | some (.assignAdd dst lhs rhs) =>
    match readSlot? ps.env lhs, readSlot? ps.env rhs with
    | some a, some b =>
      if dst < ps.env.length then
        .cont { pc := ps.pc + 1, env := ps.env.set dst (.val (a + b)) }
      else .fault
    | _, _ => .fault
  | some (.derefRead _ _) => .fault
  | some (.derefWrite _ _) => .fault
  | some (.ret slot) =>
    match readSlot? ps.env slot with
    | some v => .done v
    | none => .fault

/-- Single-step lockstep simulation for syntactically pure statements. -/
theorem stepPure_simulates
    {prog : List ToyStmt} (hpure : checkPureProg prog = true)
    {mem₀ : Memory} {ps : PureState} {ms : MachineState}
    (hsim : MirFrameSim mem₀ ps ms) :
    match stepPure prog ps with
    | .cont ps' =>
      ∃ ms', stepMachine prog ms = .cont ms' ∧ MirFrameSim mem₀ ps' ms'
    | .done v => stepMachine prog ms = .done (v, mem₀)
    | .fault => stepMachine prog ms = .fault := by
  rcases hsim with ⟨hpc, hloc, hmem⟩
  rcases ms with ⟨mpc, mlocals, mmem⟩
  dsimp at hpc hloc hmem
  subst hpc hloc hmem
  dsimp only [stepPure, stepMachine]
  cases hlookup : prog[ps.pc]? with
  | none => rfl
  | some stmt =>
    have hstmt : checkPureStmt stmt = true := by
      unfold checkPureProg at hpure
      exact List.all_eq_true.mp hpure stmt (List.mem_of_getElem? hlookup)
    cases stmt with
    | assignConst dst c =>
      by_cases hlt : dst < ps.env.length
      · simp [hlt, MirFrameSim]
      · simp [hlt]
    | assignAdd dst lhs rhs =>
      cases h1 : readSlot? ps.env lhs <;> cases h2 : readSlot? ps.env rhs
      · simp [h1, h2]
      · simp [h1, h2]
      · simp [h1, h2]
      · by_cases hlt : dst < ps.env.length <;> simp [h1, h2, hlt, MirFrameSim]
    | derefRead _ _ => contradiction
    | derefWrite _ _ => contradiction
    | ret slot =>
      cases hret : readSlot? ps.env slot <;> simp [hret]

/-- Once-and-for-all Tier 1 alias-erasure theorem: pure convergence lifts to
full stateful convergence for arbitrary `mem₀ : Memory` with `mem' = mem₀`. -/
theorem evalFuel_of_pureExec
    {prog : List ToyStmt} (hpure : checkPureProg prog = true) :
    ∀ (k : Nat) {mem₀ : Memory} {ps : PureState} {ms : MachineState} {v : Nat},
      MirFrameSim mem₀ ps ms →
      evalFuel (stepPure prog) k ps = .halted v →
      evalFuel (stepMachine prog) k ms = .halted (v, mem₀)
  | 0, _, _, _, _, _, heval => nomatch heval
  | k + 1, mem₀, ps, ms, v, hsim, heval => by
    have hstep := stepPure_simulates hpure hsim
    unfold evalFuel at heval ⊢
    cases hs : stepPure prog ps with
    | cont ps' =>
      rw [hs] at hstep heval
      rcases hstep with ⟨ms', hms', hsim'⟩
      rw [hms']
      exact evalFuel_of_pureExec hpure k hsim' heval
    | done ret =>
      rw [hs] at hstep heval
      rw [hstep]
      injection heval with hret
      subst hret
      rfl
    | fault =>
      rw [hs] at heval
      nomatch heval

theorem wpConverges_of_pureExec
    {prog : List ToyStmt} (hpure : checkPureProg prog = true)
    (mem₀ : Memory) (ps : PureState) (ms : MachineState)
    (hsim : MirFrameSim mem₀ ps ms)
    {post : Nat → Prop}
    (hwp : WpConverges (stepPure prog) ps post) :
    WpConverges (stepMachine prog) ms (fun (v, m) => m = mem₀ ∧ post v) := by
  rcases hwp with ⟨k, v, heval, hpost⟩
  exact ⟨k, (v, mem₀), evalFuel_of_pureExec hpure k hsim heval, ⟨rfl, hpost⟩⟩

/-! ## 3. Opaque-Body `LiftBlock` and Flat Environment Normalization -/

/-- Minimal block-structured pure CFG modeling `MirLiftCore.LiftBlock` over
sequential `if`-diamonds with shared join blocks. -/
inductive ToyBlock where
  | setConstAndGoto (dst c bbNext : Nat) : ToyBlock
  | addConstAndGoto (dst src c bbNext : Nat) : ToyBlock
  | branchSlotZero (condSlot bbZero bbNonZero : Nat) : ToyBlock
  | retAdd (lhs rhs : Nat) : ToyBlock

structure CfgState where
  bb : Nat
  env : List SlotState
  deriving DecidableEq, Repr

def stepCfg (cfg : List ToyBlock) (s : CfgState) : Step CfgState Nat :=
  match cfg[s.bb]? with
  | none => .fault
  | some (.setConstAndGoto dst c bbNext) =>
    if dst < s.env.length then
      .cont { bb := bbNext, env := s.env.set dst (.val c) }
    else .fault
  | some (.addConstAndGoto dst src c bbNext) =>
    match readSlot? s.env src with
    | some v =>
      if dst < s.env.length then
        .cont { bb := bbNext, env := s.env.set dst (.val (v + c)) }
      else .fault
    | none => .fault
  | some (.branchSlotZero condSlot bbZero bbNonZero) =>
    match readSlot? s.env condSlot with
    | some 0 => .cont { s with bb := bbZero }
    | some (_ + 1) => .cont { s with bb := bbNonZero }
    | none => .fault
  | some (.retAdd lhs rhs) =>
    match readSlot? s.env lhs, readSlot? s.env rhs with
    | some a, some b => .done (a + b)
    | _, _ => .fault

/-- Block-level lifting judgment parametric in an opaque postcondition
`post : Nat → Prop` (`MirLiftCore.LiftBlock` + `lift_PureMirConverges`). -/
def LiftBlock (cfg : List ToyBlock) (bbIdx : Nat)
    (env : List SlotState) (post : Nat → Prop) : Prop :=
  WpConverges (stepCfg cfg) { bb := bbIdx, env := env } post

theorem LiftBlock.of_cont {cfg : List ToyBlock} {bbIdx bbNext : Nat}
    {env env' : List SlotState} {post : Nat → Prop}
    (hstep : stepCfg cfg { bb := bbIdx, env := env } =
      .cont { bb := bbNext, env := env' })
    (hnext : LiftBlock cfg bbNext env' post) :
    LiftBlock cfg bbIdx env post :=
  StepsTo.bind_wp (StepsTo.step hstep (StepsTo.refl rfl))
    (fun _ h_eq => h_eq ▸ hnext)

def twoDiamondCfg : List ToyBlock :=
  [ .branchSlotZero 0 1 2
  , .setConstAndGoto 2 10 3
  , .setConstAndGoto 2 20 3
  , .branchSlotZero 1 4 5
  , .addConstAndGoto 2 2 1 6
  , .addConstAndGoto 2 2 2 6
  , .retAdd 2 3 ]

/-- Two-diamond sequential sharing via opaque-`post` `LiftBlock`: `hjoin6`
(`bb 6`) and `hjoin3` (`bb 3`, splitting on `y` once) are parameterized over
dead condition slots so `cases x` at `bb 0` reuses `hjoin3` across both `x`
arms without reverting or duplicating the second diamond ($2 + 2$ vs. $2^2$). -/
theorem liftBlock_diamond_shared (x y z : Nat) (post : Nat → Prop)
    (hpost :
      post (((if x = 0 then 10 else 20) + (if y = 0 then 1 else 2)) + z)) :
    LiftBlock twoDiamondCfg 0 [.val x, .val y, .uninit, .val z] post := by
  have hjoin6 : ∀ (s0 s1 u : Nat), post (u + z) →
      LiftBlock twoDiamondCfg 6 [.val s0, .val s1, .val u, .val z] post :=
    fun _ _ _ hu => WpConverges.of_done rfl hu
  have hjoin3 : ∀ (s0 w : Nat),
      post ((w + (if y = 0 then 1 else 2)) + z) →
      LiftBlock twoDiamondCfg 3 [.val s0, .val y, .val w, .val z] post := by
    intro s0 w hw
    cases y with
    | zero =>
      dsimp at hw
      exact LiftBlock.of_cont rfl
        (LiftBlock.of_cont rfl (hjoin6 s0 0 (w + 1) hw))
    | succ m =>
      dsimp at hw
      exact LiftBlock.of_cont rfl
        (LiftBlock.of_cont rfl (hjoin6 s0 (m + 1) (w + 2) hw))
  cases x with
  | zero =>
    dsimp at hpost
    exact LiftBlock.of_cont rfl (LiftBlock.of_cont rfl (hjoin3 0 10 hpost))
  | succ n =>
    dsimp at hpost
    exact LiftBlock.of_cont rfl
      (LiftBlock.of_cont rfl (hjoin3 (n + 1) 20 hpost))

/-- Rebuilds a slot list Spine-eagerly so Lean's WHNF reduces nested `List.set`
updates to a single flat list literal rather than an unreduced update tower. -/
def forcePureEnv (env : List SlotState) : List SlotState :=
  env.map id

theorem set_eq_of_forcePureEnv
    {env : List SlotState} {idx : Nat} {slot : SlotState}
    {flat : List SlotState}
    (h : forcePureEnv (env.set idx slot) = flat) :
    env.set idx slot = flat := by
  simpa [forcePureEnv] using h

/-- Concrete demonstration: 4 chained slot updates collapse to a flat literal
by `rfl`. -/
theorem chained_sets_collapse_rfl (x y : Nat) :
    ((((([SlotState.uninit, .val x, .val y, .uninit].set 0 (.val (x + y))).set
          3 (.val 1)).set 1 .uninit).set 2 .uninit)) =
      [.val (x + y), .uninit, .uninit, .val 1] :=
  set_eq_of_forcePureEnv rfl

/-! ## 4. Fuel-Free Bounded Range Loops (`forRangeUp`) -/

/-- Structural range fold over `[lo, hi)` indexed by `rem = hi - i`. -/
def forRangeUpAux {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) :
    (i rem : Nat) → lo ≤ i → i + rem = hi → α → α
  | _, 0, _, _, acc => acc
  | i, rem + 1, hlo, hsum, acc =>
    have hlt : i < hi := by omega
    forRangeUpAux lo hi step (i + 1) rem (by omega) (by omega)
      (step i hlo hlt acc)

def forRangeUp {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) : α :=
  if h : lo ≤ hi then
    forRangeUpAux lo hi step lo (hi - lo) (Nat.le_refl lo) (by omega) init
  else
    init

theorem forRangeUp_eq_init_of_ge {α : Type} {lo hi : Nat} (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α) (hge : hi ≤ lo) :
    forRangeUp lo hi init step = init := by
  unfold forRangeUp
  split
  · next hle =>
    have hzero : hi - lo = 0 := by omega
    simp [hzero, forRangeUpAux]
  · rfl

theorem forRangeUpAux_induction {α : Type} (lo hi : Nat)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → Prop) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (acc : α),
      inv i acc →
      (∀ j (hjlo : lo ≤ j) (hjlt : j < hi) a,
        inv j a → inv (j + 1) (step j hjlo hjlt a)) →
      inv hi (forRangeUpAux lo hi step i rem hlo hsum acc)
  | i, 0, _, hsum, acc, hinv, _ => by
    have : i = hi := by omega
    subst this
    exact hinv
  | i, rem + 1, hlo, hsum, acc, hinv, hstep =>
    forRangeUpAux_induction lo hi step inv (i + 1) rem (by omega) (by omega)
      (step i hlo (by omega) acc)
      (hstep i hlo (by omega) acc hinv)
      hstep

theorem forRangeUp_induction {α : Type} (lo hi : Nat) (init : α)
    (step : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → Prop)
    (hle : lo ≤ hi)
    (hinit : inv lo init)
    (hstep : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a,
      inv i a → inv (i + 1) (step i hlo hlt a)) :
    inv hi (forRangeUp lo hi init step) := by
  simp only [forRangeUp, hle, ↓reduceDIte]
  exact forRangeUpAux_induction lo hi step inv lo (hi - lo)
    (Nat.le_refl lo) (by omega) init hinit hstep

/-- Fuel-free operational loop rule: if each iteration `[i, i + 1)` steps from
an `inv i a` machine state to an `inv (i + 1) (f i ... a)` state and the exit
branch converges from `inv hi result`, then the entire loop converges without
mentioning any step count or fuel numeral. -/
theorem wpConverges_forRangeUpAux {σ out α : Type}
    (stepOp : σ → Step σ out)
    (lo hi : Nat)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop)
    (post : out → Prop) :
    ∀ (i rem : Nat) (hlo : lo ≤ i) (hsum : i + rem = hi) (a : α) (s : σ),
      inv i a s →
      (∀ j (hjlo : lo ≤ j) (hjlt : j < hi) acc s₀,
        inv j acc s₀ → StepsTo stepOp s₀ (inv (j + 1) (f j hjlo hjlt acc))) →
      (∀ s_exit,
        inv hi (forRangeUpAux lo hi f i rem hlo hsum a) s_exit →
          WpConverges stepOp s_exit post) →
      WpConverges stepOp s post
  | i, 0, hlo, hsum, a, s, hinv, _, hexit => by
    have hi_eq : i = hi := by omega
    subst hi_eq
    exact hexit s hinv
  | i, rem + 1, hlo, hsum, a, s, hinv, hiter, hexit => by
    have hlt : i < hi := by omega
    exact StepsTo.bind_wp (hiter i hlo hlt a s hinv) (fun s₁ hinv₁ =>
      wpConverges_forRangeUpAux stepOp lo hi f inv post
        (i + 1) rem (by omega) (by omega) (f i hlo hlt a) s₁ hinv₁ hiter hexit)

theorem wpConverges_forRangeUp {σ out α : Type}
    (stepOp : σ → Step σ out)
    (lo hi : Nat) (init : α)
    (f : (i : Nat) → lo ≤ i → i < hi → α → α)
    (inv : Nat → α → σ → Prop)
    (s₀ : σ) (post : out → Prop)
    (hle : lo ≤ hi)
    (hinit : inv lo init s₀)
    (hiter : ∀ i (hlo : lo ≤ i) (hlt : i < hi) a s,
      inv i a s → StepsTo stepOp s (inv (i + 1) (f i hlo hlt a)))
    (hexit : ∀ s_exit,
      inv hi (forRangeUp lo hi init f) s_exit →
        WpConverges stepOp s_exit post) :
    WpConverges stepOp s₀ post := by
  simp only [forRangeUp, hle, ↓reduceDIte] at hexit
  exact wpConverges_forRangeUpAux stepOp lo hi f inv post
    lo (hi - lo) (Nat.le_refl lo) (by omega) init s₀ hinit hiter hexit

/-- Outcome of a block-targeted segment stepper (`runCfgToBlock`). -/
inductive TargetOutcome (σ α : Type) where
  | reached (s : σ) : TargetOutcome σ α
  | halted (v : α) : TargetOutcome σ α
  | faulted : TargetOutcome σ α
  | exhausted : TargetOutcome σ α
  deriving DecidableEq, Repr

/-- Zero-or-more-step auxiliary loop (`runCfgUntilAux`): stops immediately when
`atTarget s` holds or when `.done` / `.fault` is reached. -/
def runUntilTarget {σ α : Type}
    (step : σ → Step σ α) (atTarget : σ → Bool) :
    Nat → σ → TargetOutcome σ α
  | 0, s =>
    if atTarget s then .reached s else .exhausted
  | bound + 1, s =>
    if atTarget s then
      .reached s
    else
      match step s with
      | .cont s' => runUntilTarget step atTarget bound s'
      | .done v => .halted v
      | .fault => .faulted

/-- Block-targeted stepper modeling `runCfgToBlock`: takes one mandatory step
from `s` (so stepping from a loop header `atTarget s = true` advances across the
loop body rather than halting in zero steps) and then runs `runUntilTarget` up
to structural ceiling `bound`, halting immediately at the next `atTarget` entry
or terminal `.done` / `.fault` without overshooting. -/
def runToTarget {σ α : Type}
    (step : σ → Step σ α) (atTarget : σ → Bool)
    (bound : Nat) (s : σ) : TargetOutcome σ α :=
  match step s with
  | .cont s' => runUntilTarget step atTarget bound s'
  | .done v => .halted v
  | .fault => .faulted

theorem stepsTo_of_runUntilTarget_reached {σ α : Type}
    (step : σ → Step σ α) (atTarget : σ → Bool) {mid : σ → Prop} :
    ∀ (bound : Nat) (s s_hit : σ),
      runUntilTarget step atTarget bound s = .reached s_hit →
      (atTarget s_hit = true → mid s_hit) →
      StepsTo step s mid
  | 0, s, s_hit, hrun, hmid => by
    dsimp [runUntilTarget] at hrun
    split at hrun
    · next ht =>
      injection hrun with hs
      subst hs
      exact StepsTo.refl (hmid ht)
    · nomatch hrun
  | bound + 1, s, s_hit, hrun, hmid => by
    dsimp [runUntilTarget] at hrun
    split at hrun
    · next ht =>
      injection hrun with hs
      subst hs
      exact StepsTo.refl (hmid ht)
    · cases hs : step s with
      | cont s' =>
        rw [hs] at hrun
        exact StepsTo.step hs
          (stepsTo_of_runUntilTarget_reached
            step atTarget bound s' s_hit hrun hmid)
      | done _ =>
        rw [hs] at hrun
        nomatch hrun
      | fault =>
        rw [hs] at hrun
        nomatch hrun

/-- Soundness of block-targeted segment stepping
(`mirStepsConverges_of_runCfgToBlock`): reaching `s_hit` under any internal
ceiling `bound` yields `StepsTo` with zero exposed step numerals, even when
starting at `atTarget s = true`. -/
theorem stepsTo_of_runToTarget_reached {σ α : Type}
    (step : σ → Step σ α) (atTarget : σ → Bool) {mid : σ → Prop}
    (bound : Nat) (s s_hit : σ)
    (hrun : runToTarget step atTarget bound s = .reached s_hit)
    (hmid : atTarget s_hit = true → mid s_hit) :
    StepsTo step s mid := by
  dsimp [runToTarget] at hrun
  cases hs : step s with
  | cont s' =>
    rw [hs] at hrun
    exact StepsTo.step hs
      (stepsTo_of_runUntilTarget_reached step atTarget bound s' s_hit hrun hmid)
  | done _ =>
    rw [hs] at hrun
    nomatch hrun
  | fault =>
    rw [hs] at hrun
    nomatch hrun

theorem wpConverges_of_runUntilTarget_halted {σ α : Type}
    (step : σ → Step σ α) (atTarget : σ → Bool)
    {post : α → Prop} :
    ∀ (bound : Nat) (s : σ) (v : α),
      runUntilTarget step atTarget bound s = .halted v →
      post v →
      WpConverges step s post
  | 0, s, _, hrun, _ => by
    dsimp [runUntilTarget] at hrun
    split at hrun <;> nomatch hrun
  | bound + 1, s, v, hrun, hpost => by
    dsimp [runUntilTarget] at hrun
    split at hrun
    · nomatch hrun
    · cases hs : step s with
      | cont s' =>
        rw [hs] at hrun
        exact StepsTo.bind_wp (StepsTo.step hs (StepsTo.refl rfl))
          (fun _ h_eq => h_eq ▸
            wpConverges_of_runUntilTarget_halted
              step atTarget bound s' v hrun hpost)
      | done v₀ =>
        rw [hs] at hrun
        injection hrun with hv
        subst hv
        exact WpConverges.of_done hs hpost
      | fault =>
        rw [hs] at hrun
        nomatch hrun

/-- Soundness of block-targeted terminal stepping
(`mirWpConverges_of_runCfgToBlock`): halting with `.halted v` before
re-entering `atTarget` yields `WpConverges` with zero exposed fuel numerals. -/
theorem wpConverges_of_runToTarget_halted {σ α : Type}
    (step : σ → Step σ α) (atTarget : σ → Bool)
    {post : α → Prop} (bound : Nat) (s : σ) (v : α)
    (hrun : runToTarget step atTarget bound s = .halted v)
    (hpost : post v) :
    WpConverges step s post := by
  dsimp [runToTarget] at hrun
  cases hs : step s with
  | cont s' =>
    rw [hs] at hrun
    exact StepsTo.bind_wp (StepsTo.step hs (StepsTo.refl rfl))
      (fun _ h_eq => h_eq ▸
        wpConverges_of_runUntilTarget_halted
          step atTarget bound s' v hrun hpost)
  | done v₀ =>
    rw [hs] at hrun
    injection hrun with hv
    subst hv
    exact WpConverges.of_done hs hpost
  | fault =>
    rw [hs] at hrun
    nomatch hrun

theorem runUntilTarget_mono_bound {σ α : Type}
    (step : σ → Step σ α) (atTarget : σ → Bool) :
    ∀ {b₁ b₂ : Nat} (s : σ),
      runUntilTarget step atTarget b₁ s ≠ .exhausted →
      b₁ ≤ b₂ →
      runUntilTarget step atTarget b₂ s = runUntilTarget step atTarget b₁ s
  | 0, b₂, s, hne, _ => by
    cases b₂ with
    | zero => rfl
    | succ b₂' =>
      dsimp [runUntilTarget] at hne ⊢
      split at hne <;> simp_all
  | _ + 1, 0, _, _, hle => absurd hle (Nat.not_lt_of_ge (Nat.zero_le _))
  | b₁ + 1, b₂ + 1, s, hne, hle => by
    dsimp [runUntilTarget] at hne ⊢
    split
    · rfl
    · next hnt =>
      simp [hnt] at hne
      cases hs : step s with
      | cont s' =>
        rw [hs] at hne
        exact runUntilTarget_mono_bound step atTarget s' hne
          (Nat.le_of_succ_le_succ hle)
      | done _ => rfl
      | fault => rfl

/-- Early-halting stability: once `runToTarget` hits the next `atTarget` entry,
`.halted`, or `.faulted` within ceiling `b₁`, any larger ceiling `b₂ ≥ b₁`
returns the exact same outcome without overshooting the target block. -/
theorem runToTarget_mono_bound {σ α : Type}
    (step : σ → Step σ α) (atTarget : σ → Bool)
    {b₁ b₂ : Nat} (s : σ)
    (hne : runToTarget step atTarget b₁ s ≠ .exhausted)
    (hle : b₁ ≤ b₂) :
    runToTarget step atTarget b₂ s = runToTarget step atTarget b₁ s := by
  dsimp [runToTarget] at hne ⊢
  cases hs : step s with
  | cont s' =>
    rw [hs] at hne
    exact runUntilTarget_mono_bound step atTarget s' hne hle
  | done _ => rfl
  | fault => rfl

/-- Block-count-parameterized segment evaluator matching
`MirLiftCore.runCfgToBlock`: derives its internal recursion ceiling
`Nat.add numBlocks 256` from the CFG block count `numBlocks` so caller proofs
contain zero numeric step bounds. -/
def runCfgToBlock {σ α : Type}
    (numBlocks : Nat) (step : σ → Step σ α) (atTarget : σ → Bool)
    (s : σ) : TargetOutcome σ α :=
  runToTarget step atTarget (Nat.add numBlocks 256) s

/-- Block-count-derived segment soundness
(`mirStepsConverges_of_runCfgToBlock`): exposes zero numeric step bounds at
user proof call sites. -/
theorem stepsTo_of_runCfgToBlock_reached {σ α : Type}
    (numBlocks : Nat) (step : σ → Step σ α) (atTarget : σ → Bool)
    {mid : σ → Prop} (s s_hit : σ)
    (hrun : runCfgToBlock numBlocks step atTarget s = .reached s_hit)
    (hmid : atTarget s_hit = true → mid s_hit) :
    StepsTo step s mid :=
  stepsTo_of_runToTarget_reached step atTarget (Nat.add numBlocks 256)
    s s_hit hrun hmid

/-- Block-count-derived terminal soundness
(`mirWpConverges_of_runCfgToBlock`): exposes zero numeric step bounds at user
proof call sites. -/
theorem wpConverges_of_runCfgToBlock_halted {σ α : Type}
    (numBlocks : Nat) (step : σ → Step σ α) (atTarget : σ → Bool)
    {post : α → Prop} (s : σ) (v : α)
    (hrun : runCfgToBlock numBlocks step atTarget s = .halted v)
    (hpost : post v) :
    WpConverges step s post :=
  wpConverges_of_runToTarget_halted step atTarget (Nat.add numBlocks 256)
    s v hrun hpost

/-- Concrete symbolic `[0, limit)` loop state demonstrating why fixed-numeral
fuel budgets fail on parametric bounds whereas `wpConverges_forRangeUp` +
`runCfgToBlock` discharges all `n : Nat` with zero step numerals. -/
structure LoopState where
  i : Nat
  limit : Nat
  deriving DecidableEq, Repr

/-- Single-block CFG skeleton for `stepCountUp`, supplying `numBlocks` to
`runCfgToBlock` without exposing numeric step budgets. -/
def countUpBlocks : List Unit := [()]

def stepCountUp (s : LoopState) : Step LoopState Nat :=
  if s.i < s.limit then
    .cont { s with i := s.i + 1 }
  else
    .done s.i

theorem evalFuel_stepCountUp_outOfFuel :
    ∀ (k i limit : Nat), i + k ≤ limit →
      evalFuel stepCountUp k { i := i, limit := limit } = .outOfFuel
  | 0, _, _, _ => rfl
  | k + 1, i, limit, hle => by
    have hlt : i < limit := by omega
    simp only [evalFuel, stepCountUp, hlt, ↓reduceIte]
    exact evalFuel_stepCountUp_outOfFuel k (i + 1) limit (by omega)

/-- Impossibility of uniform constant fuel: no fixed constant `K : Nat` can
halt `stepCountUp` across every symbolic bound `n : Nat`. -/
theorem no_uniform_fuel_countUp :
    ¬ ∃ (K : Nat), ∀ (n : Nat),
      ∃ v, evalFuel stepCountUp K { i := 0, limit := n } = .halted v := by
  rintro ⟨K, hK⟩
  obtain ⟨v, hv⟩ := hK K
  have hout := evalFuel_stepCountUp_outOfFuel K 0 K (by omega)
  rw [hout] at hv
  nomatch hv

/-- Fuel-free discharge of the same symbolic loop for all `n : Nat` by composing
`wpConverges_forRangeUp` with `stepsTo_of_runCfgToBlock_reached` (re-entering
the single-block loop header `atHdr := fun _ => true` after one body step) and
`wpConverges_of_runCfgToBlock_halted` on loop exit, with zero step numerals. -/
theorem countUp_wpConverges_all_n (n : Nat) :
    WpConverges stepCountUp { i := 0, limit := n } (fun v => v = n) := by
  let atHdr : LoopState → Bool := fun _ => true
  have hid : forRangeUp 0 n 0 (fun _ _ _ acc => acc + 1) = n :=
    forRangeUp_induction 0 n 0 (fun _ _ _ acc => acc + 1)
      (fun i acc => acc = i) (Nat.zero_le n) rfl
      (fun _ _ _ _ hacc => congrArg (· + 1) hacc)
  refine wpConverges_forRangeUp stepCountUp 0 n 0
    (fun _ _ _ acc => acc + 1)
    (fun i acc s => s = { i := i, limit := n } ∧ acc = i)
    { i := 0, limit := n } (fun v => v = n)
    (Nat.zero_le n) ⟨rfl, rfl⟩ ?_ ?_
  · intro i _ hlt a s ⟨hs, ha⟩
    subst hs
    subst a
    refine stepsTo_of_runCfgToBlock_reached countUpBlocks.length
      stepCountUp atHdr { i := i, limit := n } { i := i + 1, limit := n }
      ?_ (fun _ => ⟨rfl, rfl⟩)
    simp only [runCfgToBlock, runToTarget, stepCountUp, hlt, ↓reduceIte]; rfl
  · intro s_exit ⟨hs, ha⟩
    rw [hid] at ha
    subst hs
    have hnlt : ¬ (n < n) := Nat.lt_irrefl n
    exact wpConverges_of_runCfgToBlock_halted countUpBlocks.length
      stepCountUp atHdr { i := n, limit := n } n
      (by simp only [runCfgToBlock, runToTarget, stepCountUp, hnlt, ↓reduceIte])
      rfl

/-! ## 5. Tier 2 Separation-Logic Lenses (`MutLens` & Subplace Disjointness) -/

/-- Well-behaved total lens focusing an outer state `S` onto an inner view `A`,
satisfying the three classical Put-Get, Put-Put, and Get-Put lens laws. -/
structure MutLens (S A : Type) where
  get : S → A
  put : S → A → S
  put_get : ∀ s v, get (put s v) = v
  put_put : ∀ s v₁ v₂, put (put s v₁) v₂ = put s v₂
  get_put : ∀ s, put s (get s) = s

/-- Composition of two `MutLens` witnesses (used to focus from `Memory` to a
caller struct slot and then to a subplace field `&mut s.field`). -/
def MutLens.comp {S B A : Type} (outer : MutLens S B) (inner : MutLens B A) :
    MutLens S A where
  get s := inner.get (outer.get s)
  put s a := outer.put s (inner.put (outer.get s) a)
  put_get s a := by rw [outer.put_get, inner.put_get]
  put_put s a₁ a₂ := by rw [outer.put_get, inner.put_put, outer.put_put]
  get_put s := by rw [inner.get_put, outer.get_put]

/-- Two lenses on `S` have disjoint footprints when writing through one leaves
reads through the other invariant and their writes commute. -/
structure DisjointLenses {S A B : Type}
    (l₁ : MutLens S A) (l₂ : MutLens S B) : Prop where
  get₁_put₂ : ∀ s b, l₁.get (l₂.put s b) = l₁.get s
  get₂_put₁ : ∀ s a, l₂.get (l₁.put s a) = l₂.get s
  put_comm : ∀ s a b, l₁.put (l₂.put s b) a = l₂.put (l₁.put s a) b

/-- Sibling struct-field lenses on `α × β` (`&mut p.1` and `&mut p.2`). -/
def fstLens {α β : Type} : MutLens (α × β) α where
  get p := p.1
  put p a := (a, p.2)
  put_get _ _ := rfl
  put_put _ _ _ := rfl
  get_put := fun ⟨_, _⟩ => rfl

def sndLens {α β : Type} : MutLens (α × β) β where
  get p := p.2
  put p b := (p.1, b)
  put_get _ _ := rfl
  put_put _ _ := fun _ => rfl
  get_put := fun ⟨_, _⟩ => rfl

/-- Sibling field reborrows (`&mut s.1` and `&mut s.2`) on the same underlying
caller allocation are provably footprint-disjoint when lifted through any valid
allocation lens `allocLens : MutLens S (α × β)`. -/
theorem subplaceFieldLens_disjoint {S α β : Type}
    (allocLens : MutLens S (α × β)) :
    DisjointLenses (allocLens.comp fstLens) (allocLens.comp sndLens) where
  get₁_put₂ s b := by simp [MutLens.comp, fstLens, sndLens, allocLens.put_get]
  get₂_put₁ s a := by simp [MutLens.comp, fstLens, sndLens, allocLens.put_get]
  put_comm s a b := by
    simp [MutLens.comp, fstLens, sndLens, allocLens.put_get, allocLens.put_put]

/-- Soundness of erasing a two-borrow `&mut` swap/update into pure value pairs
`(a, b) ↦ (a + b, b)` without global alias case splits. -/
theorem liftLens_twoBorrowAdd_sound {S : Type}
    (l₁ l₂ : MutLens S Nat)
    (hdisj : DisjointLenses l₁ l₂)
    (s₀ : S) (a b : Nat)
    (ha : l₁.get s₀ = a) (hb : l₂.get s₀ = b) :
    let s₁ := l₁.put s₀ (l₁.get s₀ + l₂.get s₀)
    l₁.get s₁ = a + b ∧ l₂.get s₁ = b := by
  refine ⟨?_, ?_⟩
  · rw [l₁.put_get, ha, hb]
  · rw [hdisj.get₂_put₁, hb]

/-! ## 6. Scalars, Callee Stack Suffixes, Transmute Layouts, and Subplaces -/

/-- Closed-form two's-complement sign extension from `srcBits` to `dstBits`
over modular `Nat` words, avoiding bit-by-bit `BitVec` extraction loops. -/
def signExtendMod (srcBits dstBits x : Nat) : Nat :=
  let mSrc := 2 ^ srcBits
  let mDst := 2 ^ dstBits
  let v := x % mSrc
  if 2 * v < mSrc then v % mDst else (v + (mDst - mSrc)) % mDst

/-- Non-negative values (`2 * (x % 2^srcBits) < 2^srcBits`) round-trip through
`signExtendMod` into any wider target width without bit-blasting. -/
theorem signExtendMod_nonneg_id (srcBits dstBits x : Nat)
    (hpos : 0 < 2 ^ srcBits)
    (hle : 2 ^ srcBits ≤ 2 ^ dstBits)
    (hnonneg : 2 * (x % 2 ^ srcBits) < 2 ^ srcBits) :
    signExtendMod srcBits dstBits x = x % 2 ^ srcBits := by
  unfold signExtendMod
  simp only [hnonneg, ↓reduceIte]
  have hlt : x % 2 ^ srcBits < 2 ^ dstBits :=
    Nat.lt_of_lt_of_le (Nat.mod_lt x hpos) hle
  exact Nat.mod_eq_of_lt hlt

/-- Splices a caller `baseStack` below the active callee stack frames. -/
def pushBaseStack {Frame : Type}
    (baseStack calleeStack : List Frame) : List Frame :=
  calleeStack ++ baseStack

/-- Stack-suffix frame invariance: any local/callee transition operating on the
active top frame `f :: rest` commutes definitionally with splicing an arbitrary
caller `baseStack` underneath (`ActiveRootMemory` stack-suffix law). -/
theorem pushBaseStack_step_comm {Frame : Type}
    (stepTop : Frame → Frame) (f : Frame) (rest baseStack : List Frame) :
    pushBaseStack baseStack (stepTop f :: rest) =
      stepTop f :: pushBaseStack baseStack rest :=
  rfl

/-- Simplified MIR value for layout-indexed `CastKind.transmute`: either a
scalar bit-vector of `sizeBytes` or a thin pointer carrying provenance. -/
inductive TransmuteVal where
  | bits (val : Nat) (sizeBytes : Nat)
  | fnThinPtr (allocId : Nat) (fnId : Nat)
  deriving DecidableEq, Repr

/-- Transmuting through a layout entry with `layoutBytes`: an uninstantiated
generic placeholder (`layoutBytes = 0`, as on polymorphic `Wrapper<T>` prior to
`instantiateForBody`) truncates scalar payloads via `% 2^(8 * layoutBytes)`,
whereas instantiated monomorphic layouts preserve both scalar bits and thin
function-pointer provenance across `fnPtrToPtr` / `transmute`. -/
def evalTransmuteCast (layoutBytes : Nat) : TransmuteVal → TransmuteVal
  | .bits val _ => .bits (val % (2 ^ (8 * layoutBytes))) layoutBytes
  | .fnThinPtr allocId fnId =>
    if layoutBytes = 8 then .fnThinPtr allocId fnId else .bits 0 layoutBytes

theorem instantiated_transmute_roundtrip (val allocId fnId : Nat)
    (hlt : val < 2 ^ 64) :
    evalTransmuteCast 0 (.bits val 8) = .bits 0 0 ∧
    evalTransmuteCast 8 (.bits val 8) = .bits val 8 ∧
    evalTransmuteCast 8 (.fnThinPtr allocId fnId) =
      .fnThinPtr allocId fnId := by
  refine ⟨?_, ?_, rfl⟩
  · simp [evalTransmuteCast, Nat.mod_one]
  · simp [evalTransmuteCast, Nat.mod_eq_of_lt hlt]

/-- Aggregate heap slot storing a struct's fields alongside its root Tree
Borrows tag and per-field subplace child tags (`TreeFieldExclusiveBorrow`). -/
structure AggregateSlot (α : Type) where
  field0 : α
  field1 : α
  rootTag : Nat
  field0Tag : Nat
  field1Tag : Nat
  deriving DecidableEq, Repr

/-- Resolving `(allocId, 0)` through `SubplaceLocalSepProp` inspects `field0`
(and `field0Tag`) rather than the whole `AggregateSlot`, so mutating sibling
subplace `field1` via `writeSubplaceField1` preserves `field0`, `rootTag`, and
`field0Tag` without requiring root offset `(allocId, 0)` to be unallocated. -/
def writeSubplaceField1 {α : Type}
    (s : AggregateSlot α) (v₁ : α) (newTag₁ : Nat) : AggregateSlot α :=
  { s with field1 := v₁, field1Tag := newTag₁ }

theorem subplaceWrite_sibling_preserves_field0 {α : Type}
    (s : AggregateSlot α) (v₁ : α) (newTag₁ : Nat) :
    (writeSubplaceField1 s v₁ newTag₁).field0 = s.field0 ∧
    (writeSubplaceField1 s v₁ newTag₁).rootTag = s.rootTag ∧
    (writeSubplaceField1 s v₁ newTag₁).field0Tag = s.field0Tag :=
  ⟨rfl, rfl, rfl⟩

end FuelFreeMirLiftingProbe

